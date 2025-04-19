use core::error::Error;

use alloc::vec::Vec;

use super::{
    bitmap::BitmapSlice,
    volatile_memory::{
        copy_slice_impl::{copy_from_volatile_slice, copy_to_volatile_slice},
        VolatileSlice,
    },
};

pub trait Read {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, ()>;
}

pub trait Write {
    fn write(&mut self, buf: &[u8]) -> Result<usize, ()>;
}

pub trait ReadVolatile {
    /// Tries to read some bytes into the given [`VolatileSlice`] buffer, returning how many bytes
    /// were read.
    ///
    /// The behavior of implementations should be identical to [`Read::read`](std::io::Read::read)
    fn read_volatile<B: BitmapSlice>(
        &mut self,
        buf: &mut VolatileSlice<B>,
    ) -> Result<usize, super::MemoryError>;

    /// Tries to fill the given [`VolatileSlice`] buffer by reading from `self` returning an error
    /// if insufficient bytes could be read.
    ///
    /// The default implementation is identical to that of [`Read::read_exact`](std::io::Read::read_exact)
    fn read_exact_volatile<B: BitmapSlice>(
        &mut self,
        buf: &mut VolatileSlice<B>,
    ) -> Result<(), super::MemoryError> {
        // Implementation based on https://github.com/rust-lang/rust/blob/7e7483d26e3cec7a44ef00cf7ae6c9c8c918bec6/library/std/src/io/mod.rs#L465

        let mut partial_buf = buf.offset(0)?;

        while !partial_buf.is_empty() {
            match self.read_volatile(&mut partial_buf) {
                Ok(0) => return Err(super::MemoryError::IOError),
                Ok(bytes_read) => partial_buf = partial_buf.offset(bytes_read)?,
                Err(err) => return Err(super::MemoryError::IOError),
            }
        }

        Ok(())
    }
}

/// A version of the standard library's [`Write`](std::io::Write) trait that operates on volatile
/// memory instead of slices.
///
/// This trait is needed as rust slices (`&[u8]` and `&mut [u8]`) cannot be used when operating on
/// guest memory [1].
///
/// [1]: https://github.com/rust-vmm/vm-memory/pull/217
pub trait WriteVolatile {
    /// Tries to write some bytes from the given [`VolatileSlice`] buffer, returning how many bytes
    /// were written.
    ///
    /// The behavior of implementations should be identical to [`Write::write`](std::io::Write::write)
    fn write_volatile<B: BitmapSlice>(
        &mut self,
        buf: &VolatileSlice<B>,
    ) -> Result<usize, super::MemoryError>;

    /// Tries write the entire content of the given [`VolatileSlice`] buffer to `self` returning an
    /// error if not all bytes could be written.
    ///
    /// The default implementation is identical to that of [`Write::write_all`](std::io::Write::write_all)
    fn write_all_volatile<B: BitmapSlice>(
        &mut self,
        buf: &VolatileSlice<B>,
    ) -> Result<(), super::MemoryError> {
        // Based on https://github.com/rust-lang/rust/blob/7e7483d26e3cec7a44ef00cf7ae6c9c8c918bec6/library/std/src/io/mod.rs#L1570

        let mut partial_buf = buf.offset(0)?;

        while !partial_buf.is_empty() {
            match self.write_volatile(&partial_buf) {
                Ok(0) => return Err(super::MemoryError::IOError),
                Ok(bytes_written) => partial_buf = partial_buf.offset(bytes_written)?,
                Err(err) => return Err(super::MemoryError::IOError),
            }
        }

        Ok(())
    }
}

macro_rules! impl_read_write_volatile_for_raw_fd {
    ($raw_fd_ty:ty) => {
        impl ReadVolatile for $raw_fd_ty {
            fn read_volatile<B: BitmapSlice>(
                &mut self,
                buf: &mut VolatileSlice<B>,
            ) -> Result<usize, super::Error> {
                read_volatile_raw_fd(self, buf)
            }
        }

        impl WriteVolatile for $raw_fd_ty {
            fn write_volatile<B: BitmapSlice>(
                &mut self,
                buf: &VolatileSlice<B>,
            ) -> Result<usize, super::Error> {
                write_volatile_raw_fd(self, buf)
            }
        }
    };
}

impl WriteVolatile for &mut [u8] {
    fn write_volatile<B: BitmapSlice>(
        &mut self,
        buf: &VolatileSlice<B>,
    ) -> Result<usize, super::MemoryError> {
        let total = buf.len().min(self.len());
        let src = buf
            .subslice(0, total)
            .expect("subslice failed, buf: {:?}, total: {}");

        // SAFETY:
        // We check above that `src` is contiguously allocated memory of length `total <= self.len())`.
        // Furthermore, both src and dst of the call to
        // copy_from_volatile_slice are valid for reads and writes respectively of length `total`
        // since total is the minimum of lengths of the memory areas pointed to. The areas do not
        // overlap, since `dst` is inside guest memory, and buf is a slice (no slices to guest
        // memory are possible without violating rust's aliasing rules).
        let written = unsafe { copy_from_volatile_slice(self.as_mut_ptr(), &src, total) };

        // Advance the slice, just like the stdlib: https://doc.rust-lang.org/src/std/io/impls.rs.html#335
        *self = core::mem::take(self).split_at_mut(written).1;

        Ok(written)
    }

    fn write_all_volatile<B: BitmapSlice>(
        &mut self,
        buf: &VolatileSlice<B>,
    ) -> Result<(), super::MemoryError> {
        // Based on https://github.com/rust-lang/rust/blob/f7b831ac8a897273f78b9f47165cf8e54066ce4b/library/std/src/io/impls.rs#L376-L382
        if self
            .write_volatile(buf)
            .map_err(|_| super::MemoryError::IOError)?
            == buf.len()
        {
            Ok(())
        } else {
            Err(super::MemoryError::IOError)
        }
    }
}

impl ReadVolatile for &[u8] {
    fn read_volatile<B: BitmapSlice>(
        &mut self,
        buf: &mut VolatileSlice<B>,
    ) -> Result<usize, super::MemoryError> {
        let total = buf.len().min(self.len());
        let dst = buf.subslice(0, total)?;

        // SAFETY:
        // We check above that `dst` is contiguously allocated memory of length `total <= self.len())`.
        // Furthermore, both src and dst of the call to copy_to_volatile_slice are valid for reads
        // and writes respectively of length `total` since total is the minimum of lengths of the
        // memory areas pointed to. The areas do not overlap, since `dst` is inside guest memory,
        // and buf is a slice (no slices to guest memory are possible without violating rust's aliasing rules).
        let read = unsafe { copy_to_volatile_slice(&dst, self.as_ptr(), total) };

        // Advance the slice, just like the stdlib: https://doc.rust-lang.org/src/std/io/impls.rs.html#232-310
        *self = self.split_at(read).1;

        Ok(read)
    }

    fn read_exact_volatile<B: BitmapSlice>(
        &mut self,
        buf: &mut VolatileSlice<B>,
    ) -> Result<(), super::MemoryError> {
        // Based on https://github.com/rust-lang/rust/blob/f7b831ac8a897273f78b9f47165cf8e54066ce4b/library/std/src/io/impls.rs#L282-L302
        if buf.len() > self.len() {
            return Err(super::MemoryError::IOError);
        }

        self.read_volatile(buf).map(|_| ())
    }
}
