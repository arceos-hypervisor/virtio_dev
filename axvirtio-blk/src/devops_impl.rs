use axaddrspace::device::DeviceAddrRange;
use axdevice_base::BaseDeviceOps;
use axdevice_base::EmuDeviceType;

use axaddrspace::{GuestPhysAddr,GuestPhysAddrRange};
use axerrno::AxResult;
use log::debug;
use memory_addr::AddrRange;

use crate::block::Block;

impl BaseDeviceOps for Block {
    fn emu_type(&self) -> EmuDeviceType {
        EmuDeviceType::EmuDeviceTVirtioBlk
    }

    fn address_range(&self) -> GuestPhysAddrRange {
        GuestPhysAddrRange::from_start_size(0x0a00_3e00.into(), 0x200)
    }

    fn handle_read(&self, addr: <GuestPhysAddrRange as DeviceAddrRange>::Addr, width: usize) -> AxResult<usize> {
        // 调用 Block 的 mmio_read 方法
        self.mmio_read(addr, width)
    }

    fn handle_write(&self, addr: <GuestPhysAddrRange as DeviceAddrRange>::Addr, width: usize, val: usize) {
        // 调用 Block 的 mmio_write 方法
        if let Err(e) = self.mmio_write(addr, width, val) {
            debug!("MMIO write error: {:?}", e);
        }
    }
}
