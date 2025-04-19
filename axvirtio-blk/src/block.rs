use alloc::sync::Arc;
use axaddrspace::GuestPhysAddr;
use axerrno::AxResult;
use core::sync::atomic::{AtomicU8, Ordering};
use log::{debug, warn};
use virtio_bindings::virtio_mmio::{
    VIRTIO_MMIO_DEVICE_FEATURES, VIRTIO_MMIO_DEVICE_ID, VIRTIO_MMIO_INTERRUPT_STATUS,
    VIRTIO_MMIO_MAGIC_VALUE, VIRTIO_MMIO_QUEUE_NOTIFY, VIRTIO_MMIO_QUEUE_NUM_MAX,
    VIRTIO_MMIO_QUEUE_READY, VIRTIO_MMIO_STATUS, VIRTIO_MMIO_VENDOR_ID, VIRTIO_MMIO_VERSION,
};

// 设备常量定义
const MMIO_MAGIC_VALUE: u32 = 0x7472_6976; // "virt" in ASCII (little endian)
const MMIO_VERSION: u32 = 2; // 当前virtio标准版本
const VENDOR_ID: u32 = 0; // 供应商ID
const BLOCK_DEVICE_ID: u32 = 2; // virtio-blk设备ID

pub struct Block {
    pub id: u32,
    pub size: usize,

    // virtio设备状态
    device_status: u8,

    // 特性选择与特性值
    device_features_sel: u32,
    driver_features_sel: u32,
    device_features: u64, // 设备支持的特性
    driver_features: u64, // 驱动确认的特性

    // 队列相关
    queue_select: u16, // 当前选择的队列

    // 中断状态
    interrupt_status: Arc<AtomicU8>,
}

impl Block {
    /// 创建一个新的Block实例
    pub fn new(id: u32, size: usize) -> Self {
        Block {
            id,
            size,
            device_status: 0,
            device_features_sel: 0,
            driver_features_sel: 0,
            device_features: 0, // 初始不支持任何特性
            driver_features: 0,
            queue_select: 0,
            interrupt_status: Arc::new(AtomicU8::new(0)),
        }
    }

    /// 获取设备类型ID
    pub fn device_type(&self) -> u32 {
        BLOCK_DEVICE_ID
    }

    /// 获取设备特性
    pub fn device_features(&self) -> u64 {
        self.device_features
    }

    /// 获取当前设备特性选择页
    pub fn device_features_select(&self) -> u32 {
        self.device_features_sel
    }

    /// 设置设备特性选择页
    pub fn set_device_features_select(&mut self, value: u32) {
        self.device_features_sel = value;
    }

    /// 获取驱动特性选择页
    pub fn driver_features_select(&self) -> u32 {
        self.driver_features_sel
    }

    /// 设置驱动特性选择页
    pub fn set_driver_features_select(&mut self, value: u32) {
        self.driver_features_sel = value;
    }

    /// 设置驱动确认的特性
    pub fn set_driver_features(&mut self, page: u32, value: u32) {
        match page {
            0 => self.driver_features = (self.driver_features & !0xffffffff) | (value as u64),
            1 => {
                self.driver_features = (self.driver_features & 0xffffffff) | ((value as u64) << 32)
            }
            _ => warn!("Invalid driver features page: {}", page),
        }
    }

    /// 获取设备状态
    pub fn device_status(&self) -> u8 {
        self.device_status
    }

    /// 确认设备状态
    pub fn ack_device_status(&mut self, status: u8) {
        self.device_status = status;
        debug!("Device status set to: {:#x}", status);
    }

    /// 设置队列选择
    pub fn set_queue_select(&mut self, queue: u16) {
        self.queue_select = queue;
    }

    /// 获取中断状态
    pub fn interrupt_status(&self) -> &AtomicU8 {
        &self.interrupt_status
    }

    /// 检查设备状态
    pub fn check_device_status(&self, set: u8, clear: u8) -> bool {
        let status = self.device_status;
        status & set == set && status & clear == 0
    }

    /// 获取配置生成号
    pub fn config_generation(&self) -> u32 {
        0 // 简单实现，返回固定值
    }

    /// 读取配置空间
    pub fn read_config(&self, offset: usize, data: &mut [u8]) {
        // 简单实现，对于块设备，配置空间通常包含容量信息
        let capacity = self.size as u64;
        if offset < 8 && !data.is_empty() {
            let range = offset..(offset + data.len()).min(8);
            if let Some(slice) = capacity.to_le_bytes().get(range.clone()) {
                data[..range.len()].copy_from_slice(slice);
            }
        }
    }

    /// 写入配置空间
    pub fn write_config(&mut self, _offset: usize, _data: &[u8]) {
        // 对于大多数配置，块设备不支持写入
        warn!("Writing to virtio-blk config space is not supported");
    }

    /// 队列通知
    pub fn queue_notify(&mut self, val: u32) {
        debug!("Queue notify: {}", val);
        // 在实际实现中，这里应当处理IO请求
        // 作为模拟实现，我们只记录这个通知
        self.interrupt_status.fetch_or(1, Ordering::SeqCst);
    }

    /// 获取选定的队列
    pub fn selected_queue(&self) -> Option<QueueInfo> {
        // 简化实现，只返回一个固定的队列信息
        if self.queue_select == 0 {
            Some(QueueInfo {
                max_size: 256,
                ready: true,
            })
        } else {
            None
        }
    }

    /// 获取选定队列的可变引用
    pub fn selected_queue_mut(&mut self) -> Option<QueueInfo> {
        self.selected_queue()
    }

    /// 模拟 MMIO 读取操作
    pub fn mmio_read(&self, addr: GuestPhysAddr, width: usize) -> AxResult<usize> {
        if width != 4 && addr.as_usize() < 0x100 {
            // 配置寄存器必须是4字节访问
            return Ok(0);
        }

        let offset = addr.as_usize() & 0xfff;
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
                        self.selected_queue().map(|q| q.max_size).unwrap_or(0) as u32
                    }
                    VIRTIO_MMIO_QUEUE_READY => {
                        self.selected_queue().map(|q| q.ready).unwrap_or(false) as u32
                    }
                    VIRTIO_MMIO_INTERRUPT_STATUS => {
                        self.interrupt_status().load(Ordering::SeqCst) as u32
                    }
                    VIRTIO_MMIO_STATUS => self.device_status() as u32,
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

        let offset = addr.as_usize() & 0xfff;
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
                    VIRTIO_MMIO_DEVICE_FEATURES => {
                        // if self.device_features_select() == 0 {
                        //     self.device_features = (self.device_features & !0xffffffff) | (val as u64);
                        // } else {
                        //     self.device_features =
                        //         (self.device_features & 0xffffffff) | ((val as u64) << 32);
                        // }
                    }
                    VIRTIO_MMIO_QUEUE_NOTIFY => {
                        todo!();
                        // self.queue_notify(val as u32);
                    }
                    VIRTIO_MMIO_STATUS => {
                        todo!();
                        // self.ack_device_status(val as u8);
                    }
                    _ => warn!("未知的virtio mmio寄存器写入: 0x{:x}", offset),
                }
            }

            // 配置空间写入
            o @ 0x100..=0xfff => {
                todo!();
                // self.write_config(o - 0x100, &data[..width]);
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
#[derive(Clone, Copy)]
pub struct QueueInfo {
    pub max_size: u16,
    pub ready: bool,
}
