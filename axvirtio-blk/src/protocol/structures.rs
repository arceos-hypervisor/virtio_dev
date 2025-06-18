use alloc::vec::Vec;
use axaddrspace::GuestPhysAddr;

/// VirtIO Block Request Header
#[repr(C, packed)]
#[derive(Debug, Clone, Copy)]
pub struct VirtioBlkReqHeader {
    pub type_: u32,
    pub ioprio: u32,
    pub sector: u64,
}

impl VirtioBlkReqHeader {
    pub fn new() -> Self {
        Self {
            type_: 0,
            ioprio: 0,
            sector: 0,
        }
    }

    pub fn from_bytes(data: &[u8]) -> Option<Self> {
        if data.len() >= core::mem::size_of::<Self>() {
            Some(unsafe { core::ptr::read_unaligned(data.as_ptr() as *const Self) })
        } else {
            None
        }
    }
}

/// VirtIO Block Request Status
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum VirtioBlkStatus {
    Ok = 0,
    IoError = 1,
    Unsupported = 2,
}

impl VirtioBlkStatus {
    pub fn as_u8(self) -> u8 {
        self as u8
    }
}

/// Parsed VirtIO Block Request
#[derive(Debug)]
pub struct VirtioBlkRequest {
    pub header: VirtioBlkReqHeader,
    pub data_buffers: Vec<(GuestPhysAddr, usize)>,
    pub status_addr: GuestPhysAddr,
}

impl VirtioBlkRequest {
    pub fn new(header: VirtioBlkReqHeader, status_addr: GuestPhysAddr) -> Self {
        Self {
            header,
            data_buffers: Vec::new(),
            status_addr,
        }
    }

    pub fn add_data_buffer(&mut self, addr: GuestPhysAddr, len: usize) {
        self.data_buffers.push((addr, len));
    }

    pub fn is_read(&self) -> bool {
        self.header.type_ == crate::protocol::VIRTIO_BLK_T_IN
    }

    pub fn is_write(&self) -> bool {
        self.header.type_ == crate::protocol::VIRTIO_BLK_T_OUT
    }

    pub fn is_flush(&self) -> bool {
        self.header.type_ == crate::protocol::VIRTIO_BLK_T_FLUSH
    }

    pub fn sector(&self) -> u64 {
        self.header.sector
    }

    pub fn total_data_len(&self) -> usize {
        self.data_buffers.iter().map(|(_, len)| *len).sum()
    }
}
