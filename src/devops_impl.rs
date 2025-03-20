use axdevice_base::BaseDeviceOps;
use axdevice_base::EmuDeviceType;

use axaddrspace::GuestPhysAddr;
use axerrno::AxResult;
use memory_addr::AddrRange;

use crate::virtio_device::VirtioDevice;

impl BaseDeviceOps for VirtioDevice {
    fn emu_type(&self) -> EmuDeviceType {
        EmuDeviceType::EmuDeviceTVirtioBlk
    }

    fn address_range(&self) -> AddrRange<GuestPhysAddr> {
        AddrRange::new(self.base_gpa.into(), (self.base_gpa + self.length).into())
    }

    fn handle_read(&self, addr: GuestPhysAddr, _width: usize) -> AxResult<usize> {
        unsafe { Ok(core::ptr::read_volatile(addr.as_usize() as *const usize)) }
    }

    fn handle_write(&self, addr: GuestPhysAddr, _width: usize, val: usize) {
        unsafe {
            core::ptr::write_volatile(addr.as_usize() as *mut usize, val);
        }
    }
}
