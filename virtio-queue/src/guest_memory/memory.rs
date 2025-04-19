use axaddrspace::GuestPhysAddr;

pub trait GuestPhysAddrTrait {
    fn mask(&self, mask: usize) -> usize;
    fn check_sub(&self, other: &GuestPhysAddr) -> Option<GuestPhysAddr>;
}

impl GuestPhysAddrTrait for GuestPhysAddr {
    fn mask(&self, mask: usize) -> usize {
        self.as_usize() & mask
    }

    fn check_sub(&self, other: &GuestPhysAddr) -> Option<GuestPhysAddr> {
        self.as_usize()
            .checked_sub(other.as_usize())
            .map(GuestPhysAddr::from_usize)
    }
}
