use alloc::sync::Arc;
use axaddrspace::GuestPhysAddr;
use axerrno::AxResult;
use core::sync::atomic::{AtomicU8, Ordering};
use log::{debug, warn};
use spin::Mutex;
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
const VIRTIO_F_RING_EVENT_IDX: u32 = 29;

// 辅助函数，用于更新当前选择的队列的字段
fn update_queue_field<F>(device: &Block, f: F)
where
    F: FnOnce(&mut QueueInfo),
{
    if device.check_device_status(status::FEATURES_OK, status::DRIVER_OK | status::FAILED) {
        if let Some(mut queue) = device.selected_queue() {
            f(&mut queue);
            // 在实际实现中，这里应该将更新后的队列信息保存回设备
            debug!("Queue updated: {:?}", queue);
        } else {
            warn!("update invalid virtio queue");
        }
    } else {
        warn!(
            "update virtio queue in invalid state 0x{:x}",
            device.device_status()
        );
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

    // virtio设备状态
    device_status: u8,

    // 特性选择与特性值
    device_features_sel: u32,
    driver_features_sel: u32,
    device_features: u64, // 设备支持的特性
    driver_features: u64, // 驱动确认的特性

    // 队列相关
    queue_select: u16, // 当前选择的队列
}

pub struct Block {
    inner: Mutex<Inner>,

    // 中断状态 - 保持在外部，因为它是AtomicU8，已经是线程安全的
    interrupt_status: Arc<AtomicU8>,
}

impl Block {
    /// 创建一个新的Block实例
    pub fn new(id: u32, size: usize) -> Self {
        Block {
            inner: Mutex::new(Inner {
                _id: id,
                size,
                device_status: 0,
                device_features_sel: 0,
                driver_features_sel: 0,
                device_features: 0, // 初始不支持任何特性
                driver_features: 0,
                queue_select: 0,
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
                inner.driver_features = (inner.driver_features & 0xffffffff) | ((value as u64) << 32)
            }
            _ => warn!("Invalid driver features page: {}", page),
        }
    }

    /// 获取设备状态
    pub fn device_status(&self) -> u8 {
        self.inner.lock().device_status
    }

    /// 设置设备状态值
    fn set_device_status(&self, status: u8) {
        let mut inner = self.inner.lock();
        inner.device_status = status;
        debug!("Device status set to: {:#x}", status);
    }

    /// 确认设备状态
    pub fn ack_device_status(&self, status: u8) {
        use status::*;
        let current_status = self.device_status();
        debug!("Acking device status: {:#x}", !current_status & status);

        // 匹配状态变化
        match (current_status, status) {
            // 设备重置请求
            (_, 0) => {
                debug!("Device reset requested");
                self.set_device_status(RESET);
            }
            // 驱动程序发现设备
            (RESET, ACKNOWLEDGE | 0x3 ) => {
                debug!("Driver acknowledged device");
                self.set_device_status(status);
            }
            // 驱动程序知道如何驱动设备
            (ACKNOWLEDGE, ACKNOWLEDGE | DRIVER ) => {
                debug!("Driver knows how to drive device");
                self.set_device_status(status);
            }
            // 驱动程序设置了特性
            // (ACKNOWLEDGE | DRIVER, ACKNOWLEDGE | DRIVER | FEATURES_OK) => {
            (0x3, 0xb ) => {
                debug!("Driver features OK");

                // 如果驱动程序确认了VIRTIO_F_RING_EVENT_IDX特性，设置队列的event_idx标志
                if self.driver_features() & (1 << VIRTIO_F_RING_EVENT_IDX) != 0 {
                    if let Some(mut queue) = self.selected_queue() {
                        queue.set_event_idx(true);
                        debug!("Event index enabled for queue");
                    }
                }

                self.set_device_status(status);
            }
            // 驱动程序准备好了
            // (ACKNOWLEDGE | DRIVER | FEATURES_OK, ACKNOWLEDGE | DRIVER | FEATURES_OK | DRIVER_OK) => {
            (0xb, 0xf) => {
                debug!("Driver is ready");
                self.set_device_status(status);
            }
            // 设备失败
            (_, s) if (s & FAILED) != 0 => {
                debug!("Device failed");
                self.set_device_status(current_status | FAILED);
            }
            // 其他无效状态转换
            _ => {
                warn!(
                    "Invalid virtio driver status transition: 0x{:x} -> 0x{:x}",
                    current_status,
                    status
                );
            }
        }
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

    /// 队列通知
    pub fn queue_notify(&self, val: u32) {
        debug!("Queue notify: {}", val);
        // 在实际实现中，这里应当处理IO请求
        // 作为模拟实现，我们只记录这个通知
        self.interrupt_status.fetch_or(1, Ordering::SeqCst);
    }

    /// 获取选定的队列
    pub fn selected_queue(&self) -> Option<QueueInfo> {
        // 简化实现，只返回一个固定的队列信息
        let inner = self.inner.lock();
        if inner.queue_select == 0 {
            Some(QueueInfo::new(0x400))
        } else {
            None
        }
    }

    /// 获取选定队列的可变引用
    pub fn selected_queue_mut(&self) -> Option<QueueInfo> {
        self.selected_queue()
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
                        let mut inner = self.inner.lock();
                        if self.device_features_select() == 0 {
                            inner.device_features = (inner.device_features & !0xffffffff) | (val as u64);
                        } else if self.device_features_select() == 1 {
                            inner.device_features =
                                (inner.device_features & 0xffffffff) | ((val as u64) << 32);
                        }
                    }
                    VIRTIO_MMIO_DRIVER_FEATURES_SEL => {
                        self.set_driver_features_select(val as u32);
                    }
                    VIRTIO_MMIO_DRIVER_FEATURES => {
                        if self.check_device_status(status::DRIVER, status::FEATURES_OK | status::FAILED) {
                            self.set_driver_features(self.driver_features_select(), val as u32);
                        } else {
                            warn!("ack virtio features in invalid state 0x{:x}", self.device_status());
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
                        self.queue_notify(val as u32);
                    }
                    VIRTIO_MMIO_INTERRUPT_ACK => {
                        if self.check_device_status(status::DRIVER_OK, 0) {
                            self.interrupt_status().fetch_and(!(val as u8), Ordering::SeqCst);
                        }
                    }
                    VIRTIO_MMIO_STATUS => {
                        self.ack_device_status(val as u8);
                    }
                    VIRTIO_MMIO_QUEUE_DESC_LOW => {
                        update_queue_field(self, |q| q.set_desc_table_address(Some(val as u32), None));
                    }
                    VIRTIO_MMIO_QUEUE_DESC_HIGH => {
                        update_queue_field(self, |q| q.set_desc_table_address(None, Some(val as u32)));
                    }
                    VIRTIO_MMIO_QUEUE_AVAIL_LOW => {
                        update_queue_field(self, |q| q.set_avail_ring_address(Some(val as u32), None));
                    }
                    VIRTIO_MMIO_QUEUE_AVAIL_HIGH => {
                        update_queue_field(self, |q| q.set_avail_ring_address(None, Some(val as u32)));
                    }
                    VIRTIO_MMIO_QUEUE_USED_LOW => {
                        update_queue_field(self, |q| q.set_used_ring_address(Some(val as u32), None));
                    }
                    VIRTIO_MMIO_QUEUE_USED_HIGH => {
                        update_queue_field(self, |q| q.set_used_ring_address(None, Some(val as u32)));
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
                debug!("Queue notify: {}", val);
            }
            VIRTIO_MMIO_STATUS => {
                debug!("Status register set to: 0x{:x}", val);
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
}
