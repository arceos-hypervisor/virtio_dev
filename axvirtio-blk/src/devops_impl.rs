use axaddrspace::device::DeviceAddrRange;
use axdevice_base::BaseDeviceOps;
use axdevice_base::EmuDeviceType;

use axaddrspace::{GuestPhysAddr,GuestPhysAddrRange};
use axerrno::AxResult;
use log::debug;
use memory_addr::AddrRange;
use virtio_device::VirtioDevice;
use virtio_device::VirtioMmioDevice;

use crate::block::Block;

impl BaseDeviceOps for Block {
    fn emu_type(&self) -> EmuDeviceType {
        EmuDeviceType::EmuDeviceTVirtioBlk
    }

    fn address_range(&self) -> GuestPhysAddrRange {
        GuestPhysAddrRange::from_start_size(0x0a00_0000.into(), 0x4000)
    }

    fn handle_read(&self, addr: <GuestPhysAddrRange as DeviceAddrRange>::Addr, width: usize) -> AxResult<usize> {
        // unsafe { Ok(core::ptr::read_volatile(addr.as_usize() as *const usize)) }
        // 调用 Block 的 mmio_read 方法
        if addr.as_usize() < 0xa003e00 {
            // 配置寄存器必须是4字节访问
            debug!("MMIO read error: address out of range {:x}", addr.as_usize());
            return Ok(0);
        }
        //  unsafe { Ok(core::ptr::read_volatile(addr.as_usize() as *const usize)) }
        let data0 = unsafe { core::ptr::read_volatile(addr.as_usize() as *const usize) };
        let data1 = self.mmio_read(addr, width).unwrap();
        debug!("MMIO read {:x}: {:x} {:x}",addr,  data0, data1);
        // panic!("data error")
        self.mmio_read(addr, width)
    }

    fn handle_write(&self, addr: <GuestPhysAddrRange as DeviceAddrRange>::Addr, width: usize, val: usize) {
        debug!("MMIO write 0x{:x}: 0x{:x}", addr, val);
        // 调用 Block 的 mmio_write 方法
        if let Err(e) = self.mmio_write(addr, width, val) {
            debug!("MMIO write error: {:?}", e);
        }
    }
}
