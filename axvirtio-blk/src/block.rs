use alloc::boxed::Box;
use alloc::sync::Arc;
use axaddrspace::{GuestPhysAddr, HostVirtAddr};
use axerrno::AxResult;
use core::sync::atomic::{AtomicU8, Ordering};
use log::{debug, info, warn};
use memory_addr::MemoryAddr;
use spin::Mutex;
use virtio_bindings::bindings::virtio_ring::VRING_USED_F_NO_NOTIFY;
use virtio_bindings::virtio_mmio::{
    VIRTIO_MMIO_CONFIG_GENERATION, VIRTIO_MMIO_DEVICE_FEATURES, VIRTIO_MMIO_DEVICE_FEATURES_SEL,
    VIRTIO_MMIO_DEVICE_ID, VIRTIO_MMIO_DRIVER_FEATURES, VIRTIO_MMIO_DRIVER_FEATURES_SEL,
    VIRTIO_MMIO_INTERRUPT_ACK, VIRTIO_MMIO_INTERRUPT_STATUS, VIRTIO_MMIO_MAGIC_VALUE,
    VIRTIO_MMIO_QUEUE_AVAIL_HIGH, VIRTIO_MMIO_QUEUE_AVAIL_LOW, VIRTIO_MMIO_QUEUE_DESC_HIGH,
    VIRTIO_MMIO_QUEUE_DESC_LOW, VIRTIO_MMIO_QUEUE_NOTIFY, VIRTIO_MMIO_QUEUE_NUM,
    VIRTIO_MMIO_QUEUE_NUM_MAX, VIRTIO_MMIO_QUEUE_READY, VIRTIO_MMIO_QUEUE_SEL,
    VIRTIO_MMIO_QUEUE_USED_HIGH, VIRTIO_MMIO_QUEUE_USED_LOW, VIRTIO_MMIO_STATUS,
    VIRTIO_MMIO_VENDOR_ID, VIRTIO_MMIO_VERSION,
};

// 导入新模块
use crate::backend::{BlockBackend, MemoryBackend};
use crate::protocol::{VIRTIO_BLK_F_FLUSH, VIRTIO_F_RING_EVENT_IDX};
use crate::queue::{DescriptorChainParser, RequestProcessor};

// 定义virtio设备状态常量
mod status {
    /// 设备初始状态
    pub const RESET: u8 = 0;
    /// 驱动程序已找到设备
    pub const ACKNOWLEDGE: u8 = 1;
    /// 驱动程序知道如何驱动设备
    pub const DRIVER: u8 = 2;
    /// 驱动程序设置了特性
    pub const FEATURES_OK: u8 = 8;
    /// 驱动程序准备好了
    pub const DRIVER_OK: u8 = 4;
    /// 设备需要重置
    pub const FAILED: u8 = 128;
}

// 定义virtio特性常量

// 定义virtio中断类型常量
const VIRTIO_MMIO_INT_VRING: u8 = 0x01; // 队列中断
const VIRTIO_MMIO_INT_CONFIG: u8 = 0x02; // 配置空间变化中断

// 定义队列相关常量
const MAX_QUEUE_NUM: usize = 1; // virtio-blk设备只有一个队列
const DEFAULT_QUEUE_SIZE: u16 = 0x400; // 默认队列大小

// 辅助函数，用于更新当前选择的队列的字段
fn update_queue_field<F>(device: &Block, f: F)
where
    F: FnOnce(&mut QueueInfo),
{
    // 允许在 ACKNOWLEDGE|DRIVER 状态或更高状态下配置队列
    let current_status = device.device_status();
    if current_status >= (status::ACKNOWLEDGE | status::DRIVER) 
        && (current_status & status::FAILED) == 0 {
        if let Some(mut queue) = device.selected_queue() {
            f(&mut queue);
            // 将更新后的队列信息保存回设备
            if device.update_selected_queue(queue) {
                debug!("队列已更新: {:?}", queue);
            } else {
                warn!("无法更新队列");
            }
        } else {
            warn!("更新无效的virtio队列");
        }
    } else {
        warn!("在无效状态下更新virtio队列: 0x{:x}", current_status);
    }
}

// 设备常量定义
const MMIO_MAGIC_VALUE: u32 = 0x7472_6976; // "virt" in ASCII (little endian)
const MMIO_VERSION: u32 = 2; // 当前virtio标准版本
const VENDOR_ID: u32 = 0; // 供应商ID
const BLOCK_DEVICE_ID: u32 = 2; // virtio-blk设备ID

// 内部状态结构体
struct Inner {
    // 设备标识符
    _id: u32,
    size: usize,
    offset: usize, // 偏移量，通常用于内存映射

    // virtio设备状态
    device_status: u8,

    // 特性选择与特性值
    device_features_sel: u32,
    driver_features_sel: u32,
    device_features: u64, // 设备支持的特性
    driver_features: u64, // 驱动确认的特性

    // 队列相关
    queue_select: u16,                  // 当前选择的队列
    queues: [QueueInfo; MAX_QUEUE_NUM], // 所有队列的信息

    // 存储后端
    backend: Box<dyn BlockBackend>,
}

pub struct Block {
    inner: Mutex<Inner>,

    // 中断状态 - 保持在外部，因为它是AtomicU8，已经是线程安全的
    interrupt_status: Arc<AtomicU8>,
}

impl Block {
    /// 创建一个新的Block实例
    pub fn new(id: u32, size: usize, offset: usize) -> Self {
        // 初始化队列信息
        let queues = [QueueInfo::new(DEFAULT_QUEUE_SIZE); MAX_QUEUE_NUM];

        // 创建内存存储后端
        let backend = Box::new(MemoryBackend::new(size as u64, false));

        // 初始化设备特性
        let mut device_features = 0u64;
        device_features |= 1 << VIRTIO_F_RING_EVENT_IDX;
        device_features |= 1 << VIRTIO_BLK_F_FLUSH;
        // 可以根据需要添加更多特性

        info!("vm offset: {:#x}", offset);

        Block {
            inner: Mutex::new(Inner {
                _id: id,
                size,
                offset,
                device_status: 0,
                device_features_sel: 0,
                driver_features_sel: 0,
                device_features,
                driver_features: 0,
                queue_select: 0,
                queues,
                backend,
            }),
            interrupt_status: Arc::new(AtomicU8::new(0)),
        }
    }

    /// 获取设备类型ID
    pub fn device_type(&self) -> u32 {
        BLOCK_DEVICE_ID
    }

    /// 获取设备特性
    pub fn device_features(&self) -> u64 {
        self.inner.lock().device_features
    }

    /// 获取当前设备特性选择页
    pub fn device_features_select(&self) -> u32 {
        self.inner.lock().device_features_sel
    }

    /// 设置设备特性选择页
    pub fn set_device_features_select(&self, value: u32) {
        self.inner.lock().device_features_sel = value;
    }

    /// 获取驱动特性选择页
    pub fn driver_features_select(&self) -> u32 {
        self.inner.lock().driver_features_sel
    }

    /// 设置驱动特性选择页
    pub fn set_driver_features_select(&self, value: u32) {
        self.inner.lock().driver_features_sel = value;
    }

    /// 获取驱动确认的特性
    pub fn driver_features(&self) -> u64 {
        self.inner.lock().driver_features
    }

    /// 设置驱动确认的特性
    pub fn set_driver_features(&self, page: u32, value: u32) {
        let mut inner = self.inner.lock();
        match page {
            0 => inner.driver_features = (inner.driver_features & !0xffffffff) | (value as u64),
            1 => {
                inner.driver_features =
                    (inner.driver_features & 0xffffffff) | ((value as u64) << 32)
            }
            _ => warn!("Invalid driver features page: {}", page),
        }
    }

    /// 获取设备状态
    pub fn device_status(&self) -> u8 {
        self.inner.lock().device_status
    }

    /// 确认设备状态
    pub fn ack_device_status(&self, status: u8) {
        use status::*;
        
        // 使用原子操作来避免竞态条件
        let mut inner = self.inner.lock();
        let current_status = inner.device_status;
        debug!("Acking device status: current=0x{:x}, new=0x{:x}", current_status, status);

        // 匹配状态变化
        let new_status = match status {
            // 设备重置请求
            0 => {
                debug!("Device reset requested");
                RESET
            }
            // 驱动程序发现设备
            ACKNOWLEDGE => {
                if current_status == RESET {
                    debug!("Driver acknowledged device");
                    ACKNOWLEDGE
                } else {
                    warn!("Invalid state transition: 0x{:x} -> ACKNOWLEDGE", current_status);
                    current_status
                }
            }
            // 驱动程序知道如何驱动设备 (可以直接从RESET跳转到ACKNOWLEDGE|DRIVER)
            s if s == (ACKNOWLEDGE | DRIVER) => {
                if current_status == RESET || current_status == ACKNOWLEDGE {
                    debug!("Driver knows how to drive device");
                    s
                } else {
                    warn!("Invalid state transition: 0x{:x} -> DRIVER", current_status);
                    current_status
                }
            }
            // 驱动程序设置了特性
            s if s == (ACKNOWLEDGE | DRIVER | FEATURES_OK) => {
                if current_status == (ACKNOWLEDGE | DRIVER) {
                    debug!("Driver features OK");

                    // 如果驱动程序确认了VIRTIO_F_RING_EVENT_IDX特性，设置队列的event_idx标志
                    if inner.driver_features & (1 << VIRTIO_F_RING_EVENT_IDX) != 0 {
                        let queue_select = inner.queue_select as usize;
                        if queue_select < MAX_QUEUE_NUM {
                            inner.queues[queue_select].set_event_idx(true);
                            debug!("Event index enabled for queue");
                        }
                    }

                    s
                } else {
                    warn!("Invalid state transition: 0x{:x} -> FEATURES_OK", current_status);
                    current_status
                }
            }
            // 驱动程序准备好了
            s if s == (ACKNOWLEDGE | DRIVER | FEATURES_OK | DRIVER_OK) => {
                if current_status == (ACKNOWLEDGE | DRIVER | FEATURES_OK) {
                    debug!("Driver is ready");
                    s
                } else {
                    warn!("Invalid state transition: 0x{:x} -> DRIVER_OK", current_status);
                    current_status
                }
            }
            // 设备失败
            s if (s & FAILED) != 0 => {
                debug!("Device failed");
                current_status | FAILED
            }
            // 其他无效状态转换
            _ => {
                warn!(
                    "Invalid virtio driver status transition: 0x{:x} -> 0x{:x}",
                    current_status, status
                );
                current_status
            }
        };

        inner.device_status = new_status;
        debug!("Device status updated to: 0x{:x}", new_status);
    }

    /// 设置队列选择
    pub fn set_queue_select(&self, queue: u16) {
        self.inner.lock().queue_select = queue;
    }

    /// 获取中断状态
    pub fn interrupt_status(&self) -> &AtomicU8 {
        &self.interrupt_status
    }

    /// 检查设备状态
    pub fn check_device_status(&self, set: u8, clear: u8) -> bool {
        let status = self.inner.lock().device_status;
        status & set == set && status & clear == 0
    }

    /// 获取配置生成号
    pub fn config_generation(&self) -> u32 {
        0 // 简单实现，返回固定值
    }

    /// 读取配置空间
    pub fn read_config(&self, offset: usize, data: &mut [u8]) {
        // 简单实现，对于块设备，配置空间通常包含容量信息
        let inner = self.inner.lock();
        let capacity = inner.size as u64;
        if offset < 8 && !data.is_empty() {
            let range = offset..(offset + data.len()).min(8);
            if let Some(slice) = capacity.to_le_bytes().get(range.clone()) {
                data[..range.len()].copy_from_slice(slice);
            }
        }
    }

    /// 写入配置空间
    pub fn write_config(&self, _offset: usize, _data: &[u8]) {
        // 对于大多数配置，块设备不支持写入
        warn!("Writing to virtio-blk config space is not supported");
    }

    /// 通知配置空间变化
    ///
    /// 当设备的配置空间发生变化时（例如磁盘大小变化），
    /// 应调用此方法触发配置变化中断
    pub fn notify_config_changed(&self) {
        debug!("配置空间变化，触发中断");
        // 设置VIRTIO_MMIO_INT_CONFIG位，表示配置空间变化
        self.interrupt_status
            .fetch_or(VIRTIO_MMIO_INT_CONFIG, Ordering::SeqCst);
    }

    /// 队列通知
    ///
    /// 当驱动程序写入VIRTIO_MMIO_QUEUE_NOTIFY寄存器时，会调用此方法
    /// 参数val表示队列索引，指示哪个队列有新的请求
    pub fn queue_notify(&self, val: u32) {
        debug!("Queue notify: {}", val);

        // 检查队列索引是否有效
        if val != 0 {
            warn!("收到无效队列索引的通知: {}", val);
            return;
        }

        // 获取队列信息
        if let Some(queue) = self.selected_queue() {
            // 检查队列是否已准备好
            if !queue.ready() {
                warn!("队列未准备好，忽略通知");
                return;
            }

            // 处理队列中的请求
            self.process_queue(&queue);
        } else {
            warn!("无法获取队列信息，忽略通知");
        }

        // 设置中断状态位，表示队列操作完成
        self.interrupt_status
            .fetch_or(VIRTIO_MMIO_INT_VRING, Ordering::SeqCst);
    }

    /// 处理队列中的请求
    ///
    /// 从可用环中获取请求，处理它，然后更新已用环
    ///
    /// # 参数
    /// * `queue` - 队列信息
    fn process_queue(&self, queue: &QueueInfo) {
        debug!("处理队列中的请求");

        if !queue.ready() {
            warn!("队列未准备好，无法处理请求");
            return;
        }

        let inner = self.inner.lock();
        let offset = inner.offset;

        // 转换客户机物理地址到主机虚拟地址
        let avail_ring_addr = GuestPhysAddr::from_usize(queue.avail_ring_addr as usize);
        let avail_vaddr = HostVirtAddr::from_usize(avail_ring_addr.as_usize() + offset);

        // 读取可用环的idx字段
        let avail_idx = unsafe {
            let idx_ptr = (avail_vaddr.as_usize() + 2) as *const u16;
            core::ptr::read_volatile(idx_ptr)
        };

        // 获取下一个要处理的可用描述符索引
        let next_avail = queue.next_avail();

        // 检查是否有新的请求
        if next_avail == avail_idx {
            debug!("没有新的请求需要处理");
            return;
        }

        debug!(
            "处理请求: next_avail={}, avail_idx={}",
            next_avail, avail_idx
        );

        // 计算可用环中的元素位置
        // avail ring结构: flags(u16) + idx(u16) + ring[queue_size]
        // 每个ring元素: desc_index(u16)
        let elem_offset = 4 + (next_avail as usize % queue.size() as usize) * 2;
        let elem_addr = avail_vaddr.checked_add(elem_offset).unwrap();

        // 读取描述符索引
        let desc_index = unsafe {
            let desc_idx_ptr = elem_addr.as_usize() as *const u16;
            core::ptr::read_volatile(desc_idx_ptr)
        };

        debug!("处理描述符链: head_idx={}", desc_index);

        // 使用新的描述符解析和请求处理逻辑
        match DescriptorChainParser::parse_descriptor_chain(desc_index, queue, offset) {
            Ok(request) => {
                let request_type = request.header.type_;
                debug!("成功解析请求: 类型={}", request_type);

                // 执行请求
                let status =
                    RequestProcessor::execute_request(&request, inner.backend.as_ref(), offset);

                // 写入状态到客户机内存
                RequestProcessor::write_status(&request.status_addr, status);

                // 计算写入的总字节数
                let bytes_written = if request.is_read() {
                    request.total_data_len() as u32
                } else {
                    0 // 写请求不返回数据长度
                };

                // 释放锁以避免死锁
                drop(inner);

                // 更新used ring
                self.update_used_ring(queue, desc_index, bytes_written);

                // 更新next_avail
                let new_next_avail = (next_avail + 1) % queue.size();
                debug!("更新next_avail: {} -> {}", next_avail, new_next_avail);

                // 创建更新后的队列信息
                let mut updated_queue = queue.clone();
                updated_queue.set_next_avail(new_next_avail);

                // 将更新后的队列信息保存回设备
                if self.update_selected_queue(updated_queue) {
                    debug!("队列状态已更新");
                } else {
                    warn!("无法更新队列状态");
                }
            }
            Err(err) => {
                warn!("解析描述符链失败: {:?}", err);

                // 释放锁
                drop(inner);

                // 即使解析失败，也要更新used ring以避免驱动程序挂起
                self.update_used_ring(queue, desc_index, 0);

                // 更新next_avail
                let new_next_avail = (next_avail + 1) % queue.size();
                let mut updated_queue = queue.clone();
                updated_queue.set_next_avail(new_next_avail);
                self.update_selected_queue(updated_queue);
            }
        }
    }

    /// 更新used ring，通知驱动程序请求已完成
    ///
    /// # 参数
    /// * `queue` - 队列信息
    /// * `desc_index` - 描述符链的头索引
    /// * `len` - 写入的总字节数
    fn update_used_ring(&self, queue: &QueueInfo, desc_index: u16, len: u32) {
        debug!("更新used ring: desc_index={}, len={}", desc_index, len);

        if !queue.ready() {
            warn!("队列未准备好，无法更新used ring");
            return;
        }

        let inner = self.inner.lock();
        let offset = inner.offset;

        // 转换客户机物理地址到主机虚拟地址
        let used_ring_gaddr = GuestPhysAddr::from_usize(queue.used_ring_addr as usize);
        let used_ring_vaddr = HostVirtAddr::from_usize(used_ring_gaddr.as_usize() + offset);
        let next_used = queue.next_used();

        // 计算used ring元素的地址
        // used ring结构: flags(u16) + idx(u16) + ring[queue_size]
        // 每个ring元素: id(u32) + len(u32)
        let elem_offset = 4 + (next_used as usize % queue.size() as usize) * 8;
        let elem_addr = used_ring_vaddr.checked_add(elem_offset).unwrap();

        // 写入描述符索引和长度到客户机内存
        unsafe {
            // 写入id (u32)
            let id_ptr = elem_addr.as_usize() as *mut u32;
            core::ptr::write_volatile(id_ptr, desc_index as u32);

            // 写入len (u32)
            let len_ptr = (elem_addr.as_usize() + 4) as *mut u32;
            core::ptr::write_volatile(len_ptr, len);
        }

        // 更新used ring的idx字段 (内存屏障确保写入顺序)
        let new_idx = next_used.wrapping_add(1);
        unsafe {
            let idx_ptr = (used_ring_vaddr.as_usize() + 2) as *mut u16;
            debug!("更新used ring idx: {:?} -> {}", used_ring_vaddr, new_idx);
            core::ptr::write_volatile(idx_ptr, new_idx);
            debug!(
                "更新后的used ring idx: {:?}",
                core::ptr::read_volatile(idx_ptr)
            );
        }

        debug!(
            "已更新used ring: desc_index={}, len={}, next_used={} -> {}",
            desc_index, len, next_used, new_idx
        );

        // 释放锁
        drop(inner);

        // 更新队列的next_used字段
        let mut updated_queue = queue.clone();
        updated_queue.set_next_used(new_idx);

        // 将更新后的队列信息保存回设备
        if self.update_selected_queue(updated_queue) {
            debug!("队列的next_used已更新");
        } else {
            warn!("无法更新队列的next_used");
        }

        // 检查是否需要抑制中断 (VRING_USED_F_NO_NOTIFY)
        let suppress_interrupt = unsafe {
            let flags_ptr = used_ring_vaddr.as_usize() as *const u16;
            core::ptr::read_volatile(flags_ptr) & (VRING_USED_F_NO_NOTIFY as u16) != 0
        };

        if !suppress_interrupt {
            // 触发中断
            self.interrupt_status
                .fetch_or(VIRTIO_MMIO_INT_VRING, Ordering::SeqCst);
            debug!("触发中断通知驱动程序");
        } else {
            debug!("抑制中断通知");
        }
    }

    /// 获取选定的队列
    pub fn selected_queue(&self) -> Option<QueueInfo> {
        let inner = self.inner.lock();
        let queue_select = inner.queue_select as usize;

        if queue_select < MAX_QUEUE_NUM {
            // 返回选定队列的拷贝
            Some(inner.queues[queue_select])
        } else {
            warn!("选择的队列索引超出范围: {}", queue_select);
            None
        }
    }

    /// 获取选定队列的可变引用（实际上返回的是拷贝）
    pub fn selected_queue_mut(&self) -> Option<QueueInfo> {
        self.selected_queue()
    }

    /// 更新选定队列的信息
    fn update_selected_queue(&self, queue: QueueInfo) -> bool {
        let mut inner = self.inner.lock();
        let queue_select = inner.queue_select as usize;

        if queue_select < MAX_QUEUE_NUM {
            inner.queues[queue_select] = queue;
            true
        } else {
            warn!("尝试更新无效队列: {}", queue_select);
            false
        }
    }

    /// 模拟 MMIO 读取操作
    pub fn mmio_read(&self, addr: GuestPhysAddr, width: usize) -> AxResult<usize> {
        if width != 4 && addr.as_usize() < 0x100 {
            // 配置寄存器必须是4字节访问
            return Ok(0);
        }

        let offset = addr.as_usize() & 0x1ff;
        let mut data = [0u8; 8]; // 足够大以容纳所有类型
        let slice = &mut data[..width];

        // 映射到virtio-mmio对应的函数
        match offset {
            o @ 0..=0xff => {
                // 寄存器读取
                let v = match o as u32 {
                    VIRTIO_MMIO_MAGIC_VALUE => MMIO_MAGIC_VALUE,
                    VIRTIO_MMIO_VERSION => MMIO_VERSION,
                    VIRTIO_MMIO_DEVICE_ID => self.device_type(),
                    VIRTIO_MMIO_VENDOR_ID => VENDOR_ID,
                    VIRTIO_MMIO_DEVICE_FEATURES => match self.device_features_select() {
                        0 => self.device_features() as u32,
                        1 => (self.device_features() >> 32) as u32,
                        _ => 0,
                    },
                    VIRTIO_MMIO_QUEUE_NUM_MAX => {
                        self.selected_queue().map(|q| q.max_size()).unwrap_or(0) as u32
                    }
                    VIRTIO_MMIO_QUEUE_READY => {
                        self.selected_queue().map(|q| q.ready()).unwrap_or(false) as u32
                    }
                    VIRTIO_MMIO_INTERRUPT_STATUS => {
                        debug!(
                            "读取中断状态: {}",
                            self.interrupt_status().load(Ordering::SeqCst)
                        );
                        self.interrupt_status().load(Ordering::SeqCst) as u32
                    }
                    VIRTIO_MMIO_STATUS => self.device_status() as u32,
                    VIRTIO_MMIO_CONFIG_GENERATION => self.config_generation() as u32,
                    _ => {
                        warn!("未知的virtio mmio寄存器读取: 0x{:x}", offset);
                        return Ok(0);
                    }
                };

                // 将u32值转换为适当的返回值
                match width {
                    4 => Ok(v as usize),
                    _ => Ok(0), // 其他宽度应该已经被过滤
                }
            }

            // 配置空间读取
            o @ 0x100..=0xfff => {
                self.read_config(o - 0x100, slice);
                match width {
                    1 => Ok(slice[0] as usize),
                    2 => Ok(u16::from_le_bytes([slice[0], slice[1]]) as usize),
                    4 => Ok(u32::from_le_bytes([slice[0], slice[1], slice[2], slice[3]]) as usize),
                    8 => Ok(u64::from_le_bytes([
                        slice[0], slice[1], slice[2], slice[3], slice[4], slice[5], slice[6],
                        slice[7],
                    ]) as usize),
                    _ => Ok(0),
                }
            }

            _ => Ok(0),
        }
    }

    /// 模拟 MMIO 写入操作
    pub fn mmio_write(&self, addr: GuestPhysAddr, width: usize, val: usize) -> AxResult<()> {
        if width != 4 && addr.as_usize() < 0x100 {
            // 配置寄存器必须是4字节访问
            return Ok(());
        }

        let offset = addr.as_usize() & 0x1ff;
        let mut data = [0u8; 8];

        // 根据宽度准备数据
        match width {
            1 => data[0] = val as u8,
            2 => data[..2].copy_from_slice(&(val as u16).to_le_bytes()),
            4 => data[..4].copy_from_slice(&(val as u32).to_le_bytes()),
            8 => data[..8].copy_from_slice(&(val as u64).to_le_bytes()),
            _ => return Ok(()), // 其他宽度不支持
        }

        // 映射到virtio-mmio对应的函数
        match offset {
            o @ 0..=0xff => {
                // 寄存器写入
                match o as u32 {
                    VIRTIO_MMIO_DEVICE_FEATURES_SEL => {
                        self.set_device_features_select(val as u32);
                    }
                    VIRTIO_MMIO_DEVICE_FEATURES => {
                        // DEVICE_FEATURES 寄存器是只读的，驱动程序不应该写入
                        warn!("驱动程序尝试写入只读的DEVICE_FEATURES寄存器");
                    }
                    VIRTIO_MMIO_DRIVER_FEATURES_SEL => {
                        self.set_driver_features_select(val as u32);
                    }
                    VIRTIO_MMIO_DRIVER_FEATURES => {
                        // 允许在 ACKNOWLEDGE|DRIVER 状态或更高状态下设置特性
                        let current_status = self.device_status();
                        if current_status >= (status::ACKNOWLEDGE | status::DRIVER) 
                            && (current_status & status::FAILED) == 0 {
                            self.set_driver_features(self.driver_features_select(), val as u32);
                        } else {
                            warn!(
                                "ack virtio features in invalid state 0x{:x}",
                                current_status
                            );
                        }
                    }
                    VIRTIO_MMIO_QUEUE_SEL => {
                        self.set_queue_select(val as u16);
                    }
                    VIRTIO_MMIO_QUEUE_NUM => {
                        update_queue_field(self, |q| q.set_size(val as u16));
                    }
                    VIRTIO_MMIO_QUEUE_READY => {
                        update_queue_field(self, |q| q.set_ready(val == 1));
                    }
                    VIRTIO_MMIO_QUEUE_NOTIFY => {
                        // 检查设备状态是否为DRIVER_OK，只有在设备准备好的状态下才处理通知
                        if self.check_device_status(status::DRIVER_OK, status::FAILED) {
                            // 获取当前选择的队列
                            let queue_idx = val as u32;

                            // 处理队列通知
                            self.queue_notify(queue_idx);

                            // 在实际实现中，这里应该:
                            // 1. 检查队列是否已准备好
                            // 2. 从描述符表中获取请求
                            // 3. 处理IO请求
                            // 4. 更新used ring
                            // 5. 如果需要，触发中断

                            // 记录通知事件
                            debug!("处理队列 {} 的通知", queue_idx);
                        } else {
                            warn!("在无效状态下收到队列通知: 0x{:x}", self.device_status());
                        }
                    }
                    VIRTIO_MMIO_INTERRUPT_ACK => {
                        if self.check_device_status(status::DRIVER_OK, 0) {
                            self.interrupt_status()
                                .fetch_and(!(val as u8), Ordering::SeqCst);
                        }
                    }
                    VIRTIO_MMIO_STATUS => {
                        self.ack_device_status(val as u8);
                    }
                    VIRTIO_MMIO_QUEUE_DESC_LOW => {
                        update_queue_field(self, |q| {
                            q.set_desc_table_address(Some(val as u32), None)
                        });
                    }
                    VIRTIO_MMIO_QUEUE_DESC_HIGH => {
                        update_queue_field(self, |q| {
                            q.set_desc_table_address(None, Some(val as u32))
                        });
                    }
                    VIRTIO_MMIO_QUEUE_AVAIL_LOW => {
                        update_queue_field(self, |q| {
                            q.set_avail_ring_address(Some(val as u32), None)
                        });
                    }
                    VIRTIO_MMIO_QUEUE_AVAIL_HIGH => {
                        update_queue_field(self, |q| {
                            q.set_avail_ring_address(None, Some(val as u32))
                        });
                    }
                    VIRTIO_MMIO_QUEUE_USED_LOW => {
                        update_queue_field(self, |q| {
                            q.set_used_ring_address(Some(val as u32), None)
                        });
                    }
                    VIRTIO_MMIO_QUEUE_USED_HIGH => {
                        update_queue_field(self, |q| {
                            q.set_used_ring_address(None, Some(val as u32))
                        });
                    }
                    _ => warn!("未知的virtio mmio寄存器写入: 0x{:x}", offset),
                }
            }

            // 配置空间写入
            offset @ 0x100..=0xfff => {
                if self.check_device_status(status::DRIVER, status::FAILED) {
                    self.write_config(offset - 0x100, &data[..width]);
                } else {
                    warn!("can not write to device config data area before driver is ready");
                }
            }

            _ => warn!("未知的virtio mmio寄存器写入: 0x{:x}", offset),
        }

        // 记录关键寄存器的写入
        match offset as u32 {
            VIRTIO_MMIO_QUEUE_NOTIFY => {
                // 已在处理函数中记录详细日志，这里不再重复
            }
            VIRTIO_MMIO_STATUS => {
                debug!("Status register set to: 0x{:x}", val);
            }
            VIRTIO_MMIO_DRIVER_FEATURES => {
                debug!(
                    "Driver features set to: 0x{:x} (page: {})",
                    val,
                    self.driver_features_select()
                );
            }
            VIRTIO_MMIO_QUEUE_READY => {
                debug!("Queue ready set to: {}", val);
            }
            _ => {}
        }

        Ok(())
    }
}

// 简化的队列信息结构，用于返回队列状态
#[derive(Clone, Copy, Debug)]
pub struct QueueInfo {
    pub max_size: u16,
    pub size: u16,
    pub ready: bool,
    pub desc_table_addr: u64,
    pub avail_ring_addr: u64,
    pub used_ring_addr: u64,
    pub event_idx: bool,
    pub next_avail: u16, // 下一个要处理的可用描述符索引
    pub next_used: u16,  // 下一个要写入的已用描述符索引
}

impl QueueInfo {
    /// 创建一个新的队列信息
    pub fn new(max_size: u16) -> Self {
        Self {
            max_size,
            size: 0,
            ready: false,
            desc_table_addr: 0,
            avail_ring_addr: 0,
            used_ring_addr: 0,
            event_idx: false,
            next_avail: 0,
            next_used: 0,
        }
    }

    /// 获取队列最大大小
    pub fn max_size(&self) -> u16 {
        self.max_size
    }

    /// 获取队列当前大小
    pub fn size(&self) -> u16 {
        self.size
    }

    /// 设置队列大小
    pub fn set_size(&mut self, size: u16) {
        if size <= self.max_size {
            self.size = size;
        }
    }

    /// 获取队列就绪状态
    pub fn ready(&self) -> bool {
        self.ready
    }

    /// 设置队列就绪状态
    pub fn set_ready(&mut self, ready: bool) {
        self.ready = ready;
    }

    /// 设置描述符表地址
    pub fn set_desc_table_address(&mut self, low: Option<u32>, high: Option<u32>) {
        if let Some(low_addr) = low {
            self.desc_table_addr = (self.desc_table_addr & !0xffffffff) | (low_addr as u64);
        }
        if let Some(high_addr) = high {
            self.desc_table_addr = (self.desc_table_addr & 0xffffffff) | ((high_addr as u64) << 32);
        }
    }

    /// 设置可用环地址
    pub fn set_avail_ring_address(&mut self, low: Option<u32>, high: Option<u32>) {
        if let Some(low_addr) = low {
            self.avail_ring_addr = (self.avail_ring_addr & !0xffffffff) | (low_addr as u64);
        }
        if let Some(high_addr) = high {
            self.avail_ring_addr = (self.avail_ring_addr & 0xffffffff) | ((high_addr as u64) << 32);
        }
    }

    /// 设置已用环地址
    pub fn set_used_ring_address(&mut self, low: Option<u32>, high: Option<u32>) {
        if let Some(low_addr) = low {
            self.used_ring_addr = (self.used_ring_addr & !0xffffffff) | (low_addr as u64);
        }
        if let Some(high_addr) = high {
            self.used_ring_addr = (self.used_ring_addr & 0xffffffff) | ((high_addr as u64) << 32);
        }
    }

    /// 设置事件索引标志
    pub fn set_event_idx(&mut self, enabled: bool) {
        self.event_idx = enabled;
    }

    /// 获取下一个要处理的可用描述符索引
    pub fn next_avail(&self) -> u16 {
        self.next_avail
    }

    /// 设置下一个要处理的可用描述符索引
    pub fn set_next_avail(&mut self, next_avail: u16) {
        self.next_avail = next_avail;
    }

    /// 获取下一个要写入的已用描述符索引
    pub fn next_used(&self) -> u16 {
        self.next_used
    }

    /// 设置下一个要写入的已用描述符索引
    pub fn set_next_used(&mut self, next_used: u16) {
        self.next_used = next_used;
    }
}
