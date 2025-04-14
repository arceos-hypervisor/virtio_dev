use axdevice_base::BaseDeviceOps;
use axdevice_base::EmuDeviceType;

use axaddrspace::GuestPhysAddr;
use axerrno::AxResult;
use log::debug;
use memory_addr::AddrRange;

use crate::block::Block;

impl BaseDeviceOps for Block {
    fn emu_type(&self) -> EmuDeviceType {
        EmuDeviceType::EmuDeviceTVirtioBlk
    }

    fn address_range(&self) -> AddrRange<GuestPhysAddr> {
        AddrRange::new(0x800_0000.into(), (0x800_0000 + 0x10000).into())
    }

    fn handle_read(&self, addr: GuestPhysAddr, width: usize) -> AxResult<usize> {
        // 调用 Block 的 mmio_read 方法
        self.mmio_read(addr, width)
    }

    fn handle_write(&self, addr: GuestPhysAddr, width: usize, val: usize) {
        // 调用 Block 的 mmio_write 方法
        if let Err(e) = self.mmio_write(addr, width, val) {
            debug!("MMIO write error: {:?}", e);
        }
    }
}
