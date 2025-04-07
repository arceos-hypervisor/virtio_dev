// Copyright 2022 Unikie
// SPDX-License-Identifier: BSD-3-Clause OR Apache-2.0

include!(concat!(env!("OUT_DIR"), "/virtio_net.rs"));

use core::fmt::*;
use core::mem::transmute;

impl Debug for virtio_net_hdr_v1 {
    fn fmt(&self, f: &mut Formatter) -> Result {
        // SAFETY: As of Linux v6.0, all union fields have compatible types.
        // This means that it is safe to convert any variant into any other,
        // as they all have the same size, alignment, and permitted values.
        // https://doc.rust-lang.org/reference/items/unions.html#reading-and-writing-union-fields
        let csum = unsafe { self.__bindgen_anon_1.csum };

        // We forgo determining the correct name of the fields in the
        // union due to the complexity that would involve.
        f.debug_struct("virtio_net_hdr_v1")
            .field("flags", &self.flags)
            .field("gso_type", &self.gso_type)
            .field("hdr_len", &self.hdr_len)
            .field("gso_size", &self.gso_size)
            .field("csum_start", &csum.start)
            .field("csum_offset", &csum.offset)
            .field("num_buffers", &self.num_buffers)
            .finish()
    }
}

impl PartialEq<Self> for virtio_net_hdr_v1 {
    fn eq<'a>(&'a self, other: &'a Self) -> bool {
        // SAFETY: The values will be valid byte arrays, and the lifetimes match the
        // original types.
        unsafe {
            let ptr1 = transmute::<&'a Self, &'a [u8; size_of::<Self>()]>(&self);
            let ptr2 = transmute::<&'a Self, &'a [u8; size_of::<Self>()]>(&other);
            ptr1 == ptr2
        }
    }
}
