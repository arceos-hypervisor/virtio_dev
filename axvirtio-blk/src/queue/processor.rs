use crate::backend::BlockBackend;
use crate::protocol::{
    SECTOR_SIZE, VirtioBlkError, VirtioBlkRequest, VirtioBlkResult, VirtioBlkStatus,
};
use crate::protocol::{VIRTIO_BLK_T_FLUSH, VIRTIO_BLK_T_IN, VIRTIO_BLK_T_OUT};
use alloc::vec::Vec;
use log::{debug, warn};

pub struct RequestProcessor;

impl RequestProcessor {
    /// 执行 VirtIO 块请求
    pub fn execute_request(
        request: &VirtioBlkRequest,
        backend: &dyn BlockBackend,
        offset: usize,
    ) -> VirtioBlkStatus {
        let request_type = request.header.type_;
        let request_sector = request.header.sector;
        debug!(
            "执行请求: type={}, sector={}, 数据长度={}",
            request_type,
            request_sector,
            request.total_data_len()
        );

        let result = match request_type {
            VIRTIO_BLK_T_IN => Self::handle_read_request(request, backend, offset),
            VIRTIO_BLK_T_OUT => Self::handle_write_request(request, backend, offset),
            VIRTIO_BLK_T_FLUSH => Self::handle_flush_request(backend),
            _ => {
                warn!("不支持的请求类型: {}", request_type);
                Err(VirtioBlkError::UnsupportedRequestType)
            }
        };

        match result {
            Ok(_) => {
                debug!("请求执行成功");
                VirtioBlkStatus::Ok
            }
            Err(err) => {
                warn!("请求执行失败: {:?}", err);
                err.to_status()
            }
        }
    }

    fn handle_read_request(
        request: &VirtioBlkRequest,
        backend: &dyn BlockBackend,
        _offset: usize,
    ) -> VirtioBlkResult<()> {
        let sector = request.header.sector;
        let total_len = request.total_data_len();

        debug!("处理读请求: sector={}, len={}", sector, total_len);

        // 验证扇区边界
        if total_len % SECTOR_SIZE as usize != 0 {
            warn!("读取长度不是扇区大小的倍数: {}", total_len);
        }

        // 读取数据到临时缓冲区
        let mut buffer = vec![0u8; total_len];
        let bytes_read = backend.read(sector, &mut buffer)?;

        debug!("从后端读取了 {} 字节", bytes_read);

        // 将数据写入客户机内存的数据缓冲区
        let mut buffer_offset = 0;
        for (guest_addr, len) in &request.data_buffers {
            let end_offset = buffer_offset + len;
            if end_offset > buffer.len() {
                warn!("数据缓冲区超出读取数据范围");
                return Err(VirtioBlkError::BufferTooSmall);
            }

            let dest_addr = guest_addr.as_usize() as *mut u8;

            // 使用现有的地址转换方式写入客户机内存
            unsafe {
                core::ptr::copy_nonoverlapping(
                    buffer[buffer_offset..end_offset].as_ptr(),
                    dest_addr,
                    *len,
                );
            }

            buffer_offset = end_offset;
            debug!(
                "写入 {} 字节到客户机地址 0x{:x}",
                len,
                guest_addr.as_usize()
            );
        }

        Ok(())
    }

    fn handle_write_request(
        request: &VirtioBlkRequest,
        backend: &dyn BlockBackend,
        _offset: usize,
    ) -> VirtioBlkResult<()> {
        if backend.is_read_only() {
            warn!("尝试写入只读设备");
            return Err(VirtioBlkError::BackendError);
        }

        let sector = request.header.sector;
        let total_len = request.total_data_len();

        debug!("处理写请求: sector={}, len={}", sector, total_len);

        // 验证扇区边界
        if total_len % SECTOR_SIZE as usize != 0 {
            warn!("写入长度不是扇区大小的倍数: {}", total_len);
        }

        // 从客户机内存读取数据到临时缓冲区
        let mut buffer = vec![0u8; total_len];
        let mut buffer_offset = 0;

        for (guest_addr, len) in &request.data_buffers {
            let end_offset = buffer_offset + len;
            if end_offset > buffer.len() {
                warn!("数据缓冲区超出写入数据范围");
                return Err(VirtioBlkError::BufferTooSmall);
            }

            let src_addr = guest_addr.as_usize() as *const u8;

            // 使用现有的地址转换方式从客户机内存读取
            unsafe {
                core::ptr::copy_nonoverlapping(
                    src_addr,
                    buffer[buffer_offset..end_offset].as_mut_ptr(),
                    *len,
                );
            }

            buffer_offset = end_offset;
            debug!(
                "从客户机地址 0x{:x} 读取 {} 字节",
                guest_addr.as_usize(),
                len
            );
        }

        // 写入数据到后端
        let bytes_written = backend.write(sector, &buffer)?;
        debug!("写入 {} 字节到后端", bytes_written);

        Ok(())
    }

    fn handle_flush_request(backend: &dyn BlockBackend) -> VirtioBlkResult<()> {
        debug!("处理刷新请求");
        backend.flush()?;
        debug!("刷新完成");
        Ok(())
    }

    /// 写入状态字节到客户机内存
    pub fn write_status(status_addr: &axaddrspace::GuestPhysAddr, status: VirtioBlkStatus) {
        debug!(
            "写入状态 {:?} 到地址 0x{:x}",
            status,
            status_addr.as_usize()
        );

        // 使用现有的地址转换方式写入状态
        unsafe {
            let status_ptr = status_addr.as_usize() as *mut u8;
            core::ptr::write_volatile(status_ptr, status.as_u8());
        }
    }
}
