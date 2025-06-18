use crate::block::QueueInfo;
use crate::protocol::{VirtioBlkError, VirtioBlkReqHeader, VirtioBlkRequest, VirtioBlkResult};
use alloc::vec::Vec;
use axaddrspace::GuestPhysAddr;
use core::mem::size_of;
use log::{debug, warn};

// VirtIO 描述符标志
const VIRTQ_DESC_F_NEXT: u16 = 1;
const VIRTQ_DESC_F_WRITE: u16 = 2;

// VirtIO 描述符结构
#[repr(C)]
#[derive(Debug, Clone, Copy)]
struct VirtqDesc {
    addr: u64,  // 缓冲区的客户机物理地址
    len: u32,   // 缓冲区长度
    flags: u16, // 描述符标志
    next: u16,  // 如果有next标志，则指向下一个描述符
}

pub struct DescriptorChainParser;

impl DescriptorChainParser {
    /// 解析描述符链并构建 VirtIO 块请求
    pub fn parse_descriptor_chain(
        desc_index: u16,
        queue: &QueueInfo,
        offset: usize,
    ) -> VirtioBlkResult<VirtioBlkRequest> {
        debug!("解析描述符链，起始索引: {}", desc_index);

        if !queue.ready() {
            return Err(VirtioBlkError::QueueNotReady);
        }

        let mut descriptors = Vec::new();
        let mut current_desc_index = desc_index;
        let mut has_next = true;

        // 遍历描述符链
        while has_next {
            let desc = Self::read_descriptor(current_desc_index, queue, offset)?;

            debug!(
                "描述符 {}: addr=0x{:x}, len={}, flags=0x{:x}",
                current_desc_index, desc.addr, desc.len, desc.flags
            );

            descriptors.push(desc);

            if desc.flags & VIRTQ_DESC_F_NEXT != 0 {
                current_desc_index = desc.next;
                if current_desc_index as usize >= queue.size() as usize {
                    warn!("描述符索引超出范围: {}", current_desc_index);
                    return Err(VirtioBlkError::InvalidDescriptorChain);
                }
            } else {
                has_next = false;
            }
        }

        if descriptors.len() < 3 {
            warn!(
                "描述符链太短，期望至少3个描述符，实际: {}",
                descriptors.len()
            );
            return Err(VirtioBlkError::InvalidDescriptorChain);
        }

        // 第一个描述符应该是请求头
        let header_desc = &descriptors[0];
        if header_desc.flags & VIRTQ_DESC_F_WRITE != 0 {
            warn!("请求头描述符不应该是可写的");
            return Err(VirtioBlkError::InvalidDescriptorChain);
        }

        if header_desc.len < size_of::<VirtioBlkReqHeader>() as u32 {
            warn!("请求头描述符太小");
            return Err(VirtioBlkError::InvalidDescriptorChain);
        }

        // 读取请求头
        let header = Self::read_request_header(header_desc.addr, offset)?;
        let header_type = header.type_;
        let header_sector = header.sector;
        debug!("请求头: type={}, sector={}", header_type, header_sector);

        // 最后一个描述符应该是状态字节
        let status_desc = descriptors.last().unwrap();
        if status_desc.flags & VIRTQ_DESC_F_WRITE == 0 {
            warn!("状态描述符应该是可写的");
            return Err(VirtioBlkError::InvalidDescriptorChain);
        }

        if status_desc.len < 1 {
            warn!("状态描述符太小");
            return Err(VirtioBlkError::InvalidDescriptorChain);
        }

        let status_addr = GuestPhysAddr::from_usize((status_desc.addr + offset as u64) as usize);

        // 创建请求
        let mut request = VirtioBlkRequest::new(header, status_addr);

        // 中间的描述符是数据缓冲区
        for desc in &descriptors[1..descriptors.len() - 1] {
            let data_addr = GuestPhysAddr::from_usize((desc.addr + offset as u64) as usize);
            request.add_data_buffer(data_addr, desc.len as usize);
        }

        debug!(
            "成功解析请求: 类型={}, 数据缓冲区数量={}",
            header_type,
            request.data_buffers.len()
        );

        Ok(request)
    }

    fn read_descriptor(
        desc_index: u16,
        queue: &QueueInfo,
        offset: usize,
    ) -> VirtioBlkResult<VirtqDesc> {
        let desc_table_addr = queue.desc_table_addr + offset as u64;
        let desc_addr = desc_table_addr + (desc_index as u64 * size_of::<VirtqDesc>() as u64);

        debug!("读取描述符 {} 从地址 0x{:x}", desc_index, desc_addr);

        // 安全地逐字节读取描述符以避免对齐问题
        unsafe {
            let desc_ptr = desc_addr as *const u8;
            let mut desc_bytes = [0u8; 16]; // VirtqDesc 的大小是 16 字节

            for i in 0..16 {
                desc_bytes[i] = core::ptr::read_volatile(desc_ptr.add(i));
            }

            // 手动解析字段（小端序）
            let addr = u64::from_le_bytes([
                desc_bytes[0],
                desc_bytes[1],
                desc_bytes[2],
                desc_bytes[3],
                desc_bytes[4],
                desc_bytes[5],
                desc_bytes[6],
                desc_bytes[7],
            ]);
            let len =
                u32::from_le_bytes([desc_bytes[8], desc_bytes[9], desc_bytes[10], desc_bytes[11]]);
            let flags = u16::from_le_bytes([desc_bytes[12], desc_bytes[13]]);
            let next = u16::from_le_bytes([desc_bytes[14], desc_bytes[15]]);

            Ok(VirtqDesc {
                addr,
                len,
                flags,
                next,
            })
        }
    }

    fn read_request_header(addr: u64, offset: usize) -> VirtioBlkResult<VirtioBlkReqHeader> {
        let header_addr = addr + offset as u64;

        debug!("读取请求头从地址 0x{:x}", header_addr);

        // 由于VirtioBlkReqHeader使用了packed repr，需要字节级读取以避免对齐问题
        unsafe {
            let header_ptr = header_addr as *const u8;
            let mut header_bytes = [0u8; 16]; // VirtioBlkReqHeader 的大小是 16 字节

            for i in 0..16 {
                header_bytes[i] = core::ptr::read_volatile(header_ptr.add(i));
            }

            // 手动解析字段（小端序）
            let type_ = u32::from_le_bytes([
                header_bytes[0],
                header_bytes[1],
                header_bytes[2],
                header_bytes[3],
            ]);
            let ioprio = u32::from_le_bytes([
                header_bytes[4],
                header_bytes[5],
                header_bytes[6],
                header_bytes[7],
            ]);
            let sector = u64::from_le_bytes([
                header_bytes[8],
                header_bytes[9],
                header_bytes[10],
                header_bytes[11],
                header_bytes[12],
                header_bytes[13],
                header_bytes[14],
                header_bytes[15],
            ]);

            Ok(VirtioBlkReqHeader {
                type_,
                ioprio,
                sector,
            })
        }
    }
}
