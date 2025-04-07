//! Descriptor types for virtio queue.

use vm_memory::{ByteValued, Le16, Le32, Le64};

pub mod packed;
pub mod split;

/// a virtio descriptor
#[deprecated = "Descriptor has been deprecated. Please use RawDescriptor"]
pub type Descriptor = RawDescriptor;

/// A virtio descriptor's layout constraints with C representation.
/// This is a unified representation of the memory layout order
/// for packed descriptors and split descriptors.
/// This type corresponds to struct virtq_desc, see:
/// https://docs.oasis-open.org/virtio/virtio/v1.3/csd01/virtio-v1.3-csd01.html#x1-720008
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub struct RawDescriptor(Le64, Le32, Le16, Le16);

// SAFETY: This is safe because `Descriptor` contains only wrappers over POD types and
// all accesses through safe `vm-memory` API will validate any garbage that could be
// included in there.
unsafe impl ByteValued for RawDescriptor {}

impl From<split::Descriptor> for RawDescriptor {
    fn from(desc: split::Descriptor) -> Self {
        RawDescriptor(
            Le64::from(desc.addr().0),
            Le32::from(desc.len()),
            Le16::from(desc.flags()),
            Le16::from(desc.next()),
        )
    }
}

impl From<packed::Descriptor> for RawDescriptor {
    fn from(desc: packed::Descriptor) -> Self {
        RawDescriptor(
            Le64::from(desc.addr().0),
            Le32::from(desc.len()),
            Le16::from(desc.id()),
            Le16::from(desc.flags()),
        )
    }
}

impl From<RawDescriptor> for split::Descriptor {
    fn from(desc: RawDescriptor) -> split::Descriptor {
        split::Descriptor::new(desc.0.into(), desc.1.into(), desc.2.into(), desc.3.into())
    }
}

impl From<RawDescriptor> for packed::Descriptor {
    fn from(desc: RawDescriptor) -> packed::Descriptor {
        packed::Descriptor::new(desc.0.into(), desc.1.into(), desc.2.into(), desc.3.into())
    }
}
