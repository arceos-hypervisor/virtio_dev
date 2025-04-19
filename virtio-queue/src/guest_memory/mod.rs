pub mod atomic_integer;
pub mod bitmap;
pub mod bytes;
pub mod endian;
mod guest_memory;
pub mod memory;
mod memory_io;
pub mod volatile_memory;

use core::fmt::Display;

pub use guest_memory::{GuestMemory, GuestMemoryRegion};

/// `VolatileMemory` related errors.
#[allow(missing_docs)]
#[derive(Debug)]
pub enum MemoryError {
    /// `addr` is out of bounds of the volatile memory slice.
    OutOfBounds { addr: usize },
    /// Taking a slice at `base` with `offset` would overflow `usize`.
    Overflow { base: usize, offset: usize },
    /// Taking a slice whose size overflows `usize`.
    TooBig { nelements: usize, size: usize },
    /// Trying to obtain a misaligned reference.
    Misaligned { addr: usize, alignment: usize },
    /// Writing to memory failed
    IOError,
    /// Incomplete read or write
    PartialBuffer { expected: usize, completed: usize },
}

impl Display for MemoryError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            MemoryError::OutOfBounds { addr } => write!(f, "Out of bounds access at {:#x}", addr),
            MemoryError::Overflow { base, offset } => {
                write!(f, "Overflow at base {:#x} with offset {}", base, offset)
            }
            MemoryError::TooBig { nelements, size } => write!(
                f,
                "Too big slice requested: {} elements of size {}",
                nelements, size
            ),
            MemoryError::Misaligned { addr, alignment } => write!(
                f,
                "Misaligned access at {:#x} with alignment {}",
                addr, alignment
            ),
            MemoryError::IOError => write!(f, "I/O error"),
            MemoryError::PartialBuffer {
                expected,
                completed,
            } => write!(
                f,
                "Partial buffer: expected {}, completed {}",
                expected, completed
            ),
        }
    }
}
