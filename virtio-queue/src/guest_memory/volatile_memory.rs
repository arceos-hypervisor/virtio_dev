// Portions Copyright 2019 Red Hat, Inc.
//
// Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the THIRT-PARTY file.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! Types for volatile access to memory.
//!
//! Two of the core rules for safe rust is no data races and no aliased mutable references.
//! `VolatileRef` and `VolatileSlice`, along with types that produce those which implement
//! `VolatileMemory`, allow us to sidestep that rule by wrapping pointers that absolutely have to be
//! accessed volatile. Some systems really do need to operate on shared memory and can't have the
//! compiler reordering or eliding access because it has no visibility into what other systems are
//! doing with that hunk of memory.
//!
//! For the purposes of maintaining safety, volatile memory has some rules of its own:
//! 1. No references or slices to volatile memory (`&` or `&mut`).
//! 2. Access should always been done with a volatile read or write.
//!    The First rule is because having references of any kind to memory considered volatile would
//!    violate pointer aliasing. The second is because unvolatile accesses are inherently undefined if
//!    done concurrently without synchronization. With volatile access we know that the compiler has
//!    not reordered or elided the access.

extern crate alloc;

use core::cmp::min;
use core::marker::PhantomData;
use core::mem::{align_of, size_of};
use core::ptr::{copy, read_volatile, write_volatile};
// use core::ptr::{read_volatile, write_volatile};
use core::result;
use core::sync::atomic::Ordering;

use super::atomic_integer::AtomicInteger;
use super::bitmap::{Bitmap, BitmapSlice, BS};
use super::bytes::{AtomicAccess, ByteValued, Bytes};
use super::memory_io::{ReadVolatile, WriteVolatile};
// Import ReadVolatile trait directly to make it available for &[u8]

use super::MemoryError;
// use crate::{AtomicAccess, ByteValued, Bytes};

type MmapInfo = core::marker::PhantomData<()>;

use copy_slice_impl::{copy_from_volatile_slice, copy_to_volatile_slice};

/// Result of volatile memory operations.
pub type Result<T> = result::Result<T, MemoryError>;

/// Convenience function for computing `base + offset`.
///
/// # Errors
///
/// Returns [`Err(Error::Overflow)`](enum.Error.html#variant.Overflow) in case `base + offset`
/// exceeds `usize::MAX`.
///
/// # Examples
///
/// ```
/// # use vm_memory::volatile_memory::compute_offset;
/// #
/// assert_eq!(108, compute_offset(100, 8).unwrap());
/// assert!(compute_offset(std::usize::MAX, 6).is_err());
/// ```
pub fn compute_offset(base: usize, offset: usize) -> Result<usize> {
    match base.checked_add(offset) {
        None => Err(MemoryError::Overflow { base, offset }),
        Some(m) => Ok(m),
    }
}

/// Types that support raw volatile access to their data.
pub trait VolatileMemory {
    /// Type used for dirty memory tracking.
    type B: Bitmap;

    /// Gets the size of this slice.
    fn len(&self) -> usize;

    /// Check whether the region is empty.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a [`VolatileSlice`](struct.VolatileSlice.html) of `count` bytes starting at
    /// `offset`.
    ///
    /// Note that the property `get_slice(offset, count).len() == count` MUST NOT be
    /// relied on for the correctness of unsafe code. This is a safe function inside of a
    /// safe trait, and implementors are under no obligation to follow its documentation.
    fn get_slice(&self, offset: usize, count: usize) -> Result<VolatileSlice<BS<Self::B>>>;

    /// Gets a slice of memory for the entire region that supports volatile access.
    fn as_volatile_slice(&self) -> VolatileSlice<BS<Self::B>> {
        self.get_slice(0, self.len()).unwrap()
    }

    /// Gets a `VolatileRef` at `offset`.
    fn get_ref<T: ByteValued>(&self, offset: usize) -> Result<VolatileRef<T, BS<Self::B>>> {
        let slice = self.get_slice(offset, size_of::<T>())?;

        assert_eq!(
            slice.len(),
            size_of::<T>(),
            "VolatileMemory::get_slice(offset, count) returned slice of length != count."
        );

        // SAFETY: This is safe because the invariants of the constructors of VolatileSlice ensure that
        // slice.addr is valid memory of size slice.len(). The assert above ensures that
        // the length of the slice is exactly enough to hold one `T`. Lastly, the lifetime of the
        // returned VolatileRef match that of the VolatileSlice returned by get_slice and thus the
        // lifetime one `self`.
        unsafe {
            Ok(VolatileRef::with_bitmap(
                slice.addr,
                slice.bitmap,
                slice.mmap,
            ))
        }
    }

    /// Returns a [`VolatileArrayRef`](struct.VolatileArrayRef.html) of `n` elements starting at
    /// `offset`.
    fn get_array_ref<T: ByteValued>(
        &self,
        offset: usize,
        n: usize,
    ) -> Result<VolatileArrayRef<T, BS<Self::B>>> {
        // Use isize to avoid problems with ptr::offset and ptr::add down the line.
        let nbytes = isize::try_from(n)
            .ok()
            .and_then(|n| n.checked_mul(size_of::<T>() as isize))
            .ok_or(MemoryError::TooBig {
                nelements: n,
                size: size_of::<T>(),
            })?;
        let slice = self.get_slice(offset, nbytes as usize)?;

        assert_eq!(
            slice.len(),
            nbytes as usize,
            "VolatileMemory::get_slice(offset, count) returned slice of length != count."
        );

        // SAFETY: This is safe because the invariants of the constructors of VolatileSlice ensure that
        // slice.addr is valid memory of size slice.len(). The assert above ensures that
        // the length of the slice is exactly enough to hold `n` instances of `T`. Lastly, the lifetime of the
        // returned VolatileArrayRef match that of the VolatileSlice returned by get_slice and thus the
        // lifetime one `self`.
        unsafe {
            Ok(VolatileArrayRef::with_bitmap(
                slice.addr,
                n,
                slice.bitmap,
                slice.mmap,
            ))
        }
    }

    /// Returns a reference to an instance of `T` at `offset`.
    ///
    /// # Safety
    /// To use this safely, the caller must guarantee that there are no other
    /// users of the given chunk of memory for the lifetime of the result.
    ///
    /// # Errors
    ///
    /// If the resulting pointer is not aligned, this method will return an
    /// [`Error`](enum.Error.html).
    unsafe fn aligned_as_ref<T: ByteValued>(&self, offset: usize) -> Result<&T> {
        let slice = self.get_slice(offset, size_of::<T>())?;
        slice.check_alignment(align_of::<T>())?;

        assert_eq!(
            slice.len(),
            size_of::<T>(),
            "VolatileMemory::get_slice(offset, count) returned slice of length != count."
        );

        // SAFETY: This is safe because the invariants of the constructors of VolatileSlice ensure that
        // slice.addr is valid memory of size slice.len(). The assert above ensures that
        // the length of the slice is exactly enough to hold one `T`.
        // Dereferencing the pointer is safe because we check the alignment above, and the invariants
        // of this function ensure that no aliasing pointers exist. Lastly, the lifetime of the
        // returned VolatileArrayRef match that of the VolatileSlice returned by get_slice and thus the
        // lifetime one `self`.
        unsafe { Ok(&*(slice.addr as *const T)) }
    }

    /// Returns a mutable reference to an instance of `T` at `offset`. Mutable accesses performed
    /// using the resulting reference are not automatically accounted for by the dirty bitmap
    /// tracking functionality.
    ///
    /// # Safety
    ///
    /// To use this safely, the caller must guarantee that there are no other
    /// users of the given chunk of memory for the lifetime of the result.
    ///
    /// # Errors
    ///
    /// If the resulting pointer is not aligned, this method will return an
    /// [`Error`](enum.Error.html).
    unsafe fn aligned_as_mut<T: ByteValued>(&self, offset: usize) -> Result<&mut T> {
        let slice = self.get_slice(offset, size_of::<T>())?;
        slice.check_alignment(align_of::<T>())?;

        assert_eq!(
            slice.len(),
            size_of::<T>(),
            "VolatileMemory::get_slice(offset, count) returned slice of length != count."
        );

        // SAFETY: This is safe because the invariants of the constructors of VolatileSlice ensure that
        // slice.addr is valid memory of size slice.len(). The assert above ensures that
        // the length of the slice is exactly enough to hold one `T`.
        // Dereferencing the pointer is safe because we check the alignment above, and the invariants
        // of this function ensure that no aliasing pointers exist. Lastly, the lifetime of the
        // returned VolatileArrayRef match that of the VolatileSlice returned by get_slice and thus the
        // lifetime one `self`.

        unsafe { Ok(&mut *(slice.addr as *mut T)) }
    }

    /// Returns a reference to an instance of `T` at `offset`. Mutable accesses performed
    /// using the resulting reference are not automatically accounted for by the dirty bitmap
    /// tracking functionality.
    ///
    /// # Errors
    ///
    /// If the resulting pointer is not aligned, this method will return an
    /// [`Error`](enum.Error.html).
    fn get_atomic_ref<T: AtomicInteger>(&self, offset: usize) -> Result<&T> {
        let slice = self.get_slice(offset, size_of::<T>())?;
        slice.check_alignment(align_of::<T>())?;

        assert_eq!(
            slice.len(),
            size_of::<T>(),
            "VolatileMemory::get_slice(offset, count) returned slice of length != count."
        );

        // SAFETY: This is safe because the invariants of the constructors of VolatileSlice ensure that
        // slice.addr is valid memory of size slice.len(). The assert above ensures that
        // the length of the slice is exactly enough to hold one `T`.
        // Dereferencing the pointer is safe because we check the alignment above. Lastly, the lifetime of the
        // returned VolatileArrayRef match that of the VolatileSlice returned by get_slice and thus the
        // lifetime one `self`.
        unsafe { Ok(&*(slice.addr as *const T)) }
    }

    /// Returns the sum of `base` and `offset` if the resulting address is valid.
    fn compute_end_offset(&self, base: usize, offset: usize) -> Result<usize> {
        let mem_end = compute_offset(base, offset)?;
        if mem_end > self.len() {
            return Err(MemoryError::OutOfBounds { addr: mem_end });
        }
        Ok(mem_end)
    }
}

impl<'a> From<&'a mut [u8]> for VolatileSlice<'a, ()> {
    fn from(value: &'a mut [u8]) -> Self {
        // SAFETY: Since we construct the VolatileSlice from a rust slice, we know that
        // the memory at addr `value as *mut u8` is valid for reads and writes (because mutable
        // reference) of len `value.len()`. Since the `VolatileSlice` inherits the lifetime `'a`,
        // it is not possible to access/mutate `value` while the VolatileSlice is alive.
        //
        // Note that it is possible for multiple aliasing sub slices of this `VolatileSlice`s to
        // be created through `VolatileSlice::subslice`. This is OK, as pointers are allowed to
        // alias, and it is impossible to get rust-style references from a `VolatileSlice`.
        unsafe { VolatileSlice::new(value.as_mut_ptr(), value.len()) }
    }
}

#[repr(C, packed)]
struct Packed<T>(T);

/// A guard to perform mapping and protect unmapping of the memory.
#[derive(Debug)]
pub struct PtrGuard {
    addr: *mut u8,
    len: usize,
}

#[allow(clippy::len_without_is_empty)]
impl PtrGuard {
    #[allow(unused_variables)]
    fn new(mmap: Option<&MmapInfo>, addr: *mut u8, len: usize) -> Self {
        Self { addr, len }
    }

    fn read(mmap: Option<&MmapInfo>, addr: *mut u8, len: usize) -> Self {
        Self::new(mmap, addr, len)
    }

    /// Returns a non-mutable pointer to the beginning of the slice.
    pub fn as_ptr(&self) -> *const u8 {
        self.addr
    }

    /// Gets the length of the mapped region.
    pub fn len(&self) -> usize {
        self.len
    }
}

/// A mutable guard to perform mapping and protect unmapping of the memory.
#[derive(Debug)]
pub struct PtrGuardMut(PtrGuard);

#[allow(clippy::len_without_is_empty)]
impl PtrGuardMut {
    fn write(mmap: Option<&MmapInfo>, addr: *mut u8, len: usize) -> Self {
        Self(PtrGuard::new(mmap, addr, len))
    }

    /// Returns a mutable pointer to the beginning of the slice. Mutable accesses performed
    /// using the resulting pointer are not automatically accounted for by the dirty bitmap
    /// tracking functionality.
    pub fn as_ptr(&self) -> *mut u8 {
        self.0.addr
    }

    /// Gets the length of the mapped region.
    pub fn len(&self) -> usize {
        self.0.len
    }
}

/// A slice of raw memory that supports volatile access.
#[derive(Clone, Copy, Debug)]
pub struct VolatileSlice<'a, B = ()> {
    addr: *mut u8,
    size: usize,
    bitmap: B,
    mmap: Option<&'a MmapInfo>,
}

impl<'a> VolatileSlice<'a, ()> {
    /// Creates a slice of raw memory that must support volatile access.
    ///
    /// # Safety
    ///
    /// To use this safely, the caller must guarantee that the memory at `addr` is `size` bytes long
    /// and is available for the duration of the lifetime of the new `VolatileSlice`. The caller
    /// must also guarantee that all other users of the given chunk of memory are using volatile
    /// accesses.
    pub unsafe fn new(addr: *mut u8, size: usize) -> VolatileSlice<'a> {
        Self::with_bitmap(addr, size, (), None)
    }
}

impl<'a, B: BitmapSlice> VolatileSlice<'a, B> {
    /// Creates a slice of raw memory that must support volatile access, and uses the provided
    /// `bitmap` object for dirty page tracking.
    ///
    /// # Safety
    ///
    /// To use this safely, the caller must guarantee that the memory at `addr` is `size` bytes long
    /// and is available for the duration of the lifetime of the new `VolatileSlice`. The caller
    /// must also guarantee that all other users of the given chunk of memory are using volatile
    /// accesses.
    pub unsafe fn with_bitmap(
        addr: *mut u8,
        size: usize,
        bitmap: B,
        mmap: Option<&'a MmapInfo>,
    ) -> VolatileSlice<'a, B> {
        VolatileSlice {
            addr,
            size,
            bitmap,
            mmap,
        }
    }

    /// Returns a guard for the pointer to the underlying memory.
    pub fn ptr_guard(&self) -> PtrGuard {
        PtrGuard::read(self.mmap, self.addr, self.len())
    }

    /// Returns a mutable guard for the pointer to the underlying memory.
    pub fn ptr_guard_mut(&self) -> PtrGuardMut {
        PtrGuardMut::write(self.mmap, self.addr, self.len())
    }

    /// Gets the size of this slice.
    pub fn len(&self) -> usize {
        self.size
    }

    /// Checks if the slice is empty.
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// Borrows the inner `BitmapSlice`.
    pub fn bitmap(&self) -> &B {
        &self.bitmap
    }

    /// Divides one slice into two at an index.
    ///
    /// # Example
    ///
    /// ```
    /// # use vm_memory::{VolatileMemory, VolatileSlice};
    /// #
    /// # // Create a buffer
    /// # let mut mem = [0u8; 32];
    /// #
    /// # // Get a `VolatileSlice` from the buffer
    /// let vslice = VolatileSlice::from(&mut mem[..]);
    ///
    /// let (start, end) = vslice.split_at(8).expect("Could not split VolatileSlice");
    /// assert_eq!(8, start.len());
    /// assert_eq!(24, end.len());
    /// ```
    pub fn split_at(&self, mid: usize) -> Result<(Self, Self)> {
        let end = self.offset(mid)?;
        let start =
            // SAFETY: safe because self.offset() already checked the bounds
            unsafe { VolatileSlice::with_bitmap(self.addr, mid, self.bitmap.clone(), self.mmap) };

        Ok((start, end))
    }

    /// Returns a subslice of this [`VolatileSlice`](struct.VolatileSlice.html) starting at
    /// `offset` with `count` length.
    ///
    /// The returned subslice is a copy of this slice with the address increased by `offset` bytes
    /// and the size set to `count` bytes.
    pub fn subslice(&self, offset: usize, count: usize) -> Result<Self> {
        let _ = self.compute_end_offset(offset, count)?;

        // SAFETY: This is safe because the pointer is range-checked by compute_end_offset, and
        // the lifetime is the same as the original slice.
        unsafe {
            Ok(VolatileSlice::with_bitmap(
                self.addr.add(offset),
                count,
                self.bitmap.slice_at(offset),
                self.mmap,
            ))
        }
    }

    /// Returns a subslice of this [`VolatileSlice`](struct.VolatileSlice.html) starting at
    /// `offset`.
    ///
    /// The returned subslice is a copy of this slice with the address increased by `count` bytes
    /// and the size reduced by `count` bytes.
    pub fn offset(&self, count: usize) -> Result<VolatileSlice<'a, B>> {
        let new_addr = (self.addr as usize)
            .checked_add(count)
            .ok_or(MemoryError::Overflow {
                base: self.addr as usize,
                offset: count,
            })?;
        let new_size = self
            .size
            .checked_sub(count)
            .ok_or(MemoryError::OutOfBounds { addr: new_addr })?;
        // SAFETY: Safe because the memory has the same lifetime and points to a subset of the
        // memory of the original slice.
        unsafe {
            Ok(VolatileSlice::with_bitmap(
                self.addr.add(count),
                new_size,
                self.bitmap.slice_at(count),
                self.mmap,
            ))
        }
    }

    /// Copies as many elements of type `T` as possible from this slice to `buf`.
    ///
    /// Copies `self.len()` or `buf.len()` times the size of `T` bytes, whichever is smaller,
    /// to `buf`. The copy happens from smallest to largest address in `T` sized chunks
    /// using volatile reads.
    ///
    /// # Examples
    ///
    /// ```
    /// # use vm_memory::{VolatileMemory, VolatileSlice};
    /// #
    /// let mut mem = [0u8; 32];
    /// let vslice = VolatileSlice::from(&mut mem[..]);
    /// let mut buf = [5u8; 16];
    /// let res = vslice.copy_to(&mut buf[..]);
    ///
    /// assert_eq!(16, res);
    /// for &v in &buf[..] {
    ///     assert_eq!(v, 0);
    /// }
    /// ```
    pub fn copy_to<T>(&self, buf: &mut [T]) -> usize
    where
        T: ByteValued,
    {
        // A fast path for u8/i8
        if size_of::<T>() == 1 {
            let total = buf.len().min(self.len());

            // SAFETY:
            // - dst is valid for writes of at least `total`, since total <= buf.len()
            // - src is valid for reads of at least `total` as total <= self.len()
            // - The regions are non-overlapping as `src` points to guest memory and `buf` is
            //   a slice and thus has to live outside of guest memory (there can be more slices to
            //   guest memory without violating rust's aliasing rules)
            // - size is always a multiple of alignment, so treating *mut T as *mut u8 is fine
            unsafe { copy_from_volatile_slice(buf.as_mut_ptr() as *mut u8, self, total) }
        } else {
            let count = self.size / size_of::<T>();
            let source = self.get_array_ref::<T>(0, count).unwrap();
            source.copy_to(buf)
        }
    }

    /// Copies as many bytes as possible from this slice to the provided `slice`.
    ///
    /// The copies happen in an undefined order.
    ///
    /// # Examples
    ///
    /// ```
    /// # use vm_memory::{VolatileMemory, VolatileSlice};
    /// #
    /// # // Create a buffer
    /// # let mut mem = [0u8; 32];
    /// #
    /// # // Get a `VolatileSlice` from the buffer
    /// # let vslice = VolatileSlice::from(&mut mem[..]);
    /// #
    /// vslice.copy_to_volatile_slice(
    ///     vslice
    ///         .get_slice(16, 16)
    ///         .expect("Could not get VolatileSlice"),
    /// );
    /// ```
    pub fn copy_to_volatile_slice<S: BitmapSlice>(&self, slice: VolatileSlice<S>) {
        // SAFETY: Safe because the pointers are range-checked when the slices
        // are created, and they never escape the VolatileSlices.
        // FIXME: ... however, is it really okay to mix non-volatile
        // operations such as copy with read_volatile and write_volatile?
        unsafe {
            let count = min(self.size, slice.size);
            copy(self.addr, slice.addr, count);
            slice.bitmap.mark_dirty(0, count);
        }
    }

    /// Copies as many elements of type `T` as possible from `buf` to this slice.
    ///
    /// The copy happens from smallest to largest address in `T` sized chunks using volatile writes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use vm_memory::{VolatileMemory, VolatileSlice};
    /// #
    /// let mut mem = [0u8; 32];
    /// let vslice = VolatileSlice::from(&mut mem[..]);
    ///
    /// let buf = [5u8; 64];
    /// vslice.copy_from(&buf[..]);
    ///
    /// for i in 0..4 {
    ///     let val = vslice
    ///         .get_ref::<u32>(i * 4)
    ///         .expect("Could not get value")
    ///         .load();
    ///     assert_eq!(val, 0x05050505);
    /// }
    /// ```
    pub fn copy_from<T>(&self, buf: &[T])
    where
        T: ByteValued,
    {
        // A fast path for u8/i8
        if size_of::<T>() == 1 {
            let total = buf.len().min(self.len());
            // SAFETY:
            // - dst is valid for writes of at least `total`, since total <= self.len()
            // - src is valid for reads of at least `total` as total <= buf.len()
            // - The regions are non-overlapping as `dst` points to guest memory and `buf` is
            //   a slice and thus has to live outside of guest memory (there can be more slices to
            //   guest memory without violating rust's aliasing rules)
            // - size is always a multiple of alignment, so treating *mut T as *mut u8 is fine
            unsafe { copy_to_volatile_slice(self, buf.as_ptr() as *const u8, total) };
        } else {
            let count = self.size / size_of::<T>();
            // It's ok to use unwrap here because `count` was computed based on the current
            // length of `self`.
            let dest = self.get_array_ref::<T>(0, count).unwrap();

            // No need to explicitly call `mark_dirty` after this call because
            // `VolatileArrayRef::copy_from` already takes care of that.
            dest.copy_from(buf);
        };
    }

    /// Checks if the current slice is aligned at `alignment` bytes.
    fn check_alignment(&self, alignment: usize) -> Result<()> {
        // Check that the desired alignment is a power of two.
        debug_assert!((alignment & (alignment - 1)) == 0);
        if ((self.addr as usize) & (alignment - 1)) != 0 {
            return Err(MemoryError::Misaligned {
                addr: self.addr as usize,
                alignment,
            });
        }
        Ok(())
    }
}

impl<B: BitmapSlice> Bytes<usize> for VolatileSlice<'_, B> {
    type E = MemoryError;

    /// # Examples
    /// * Write a slice of size 5 at offset 1020 of a 1024-byte `VolatileSlice`.
    ///
    /// ```
    /// # use vm_memory::{Bytes, VolatileMemory, VolatileSlice};
    /// #
    /// let mut mem = [0u8; 1024];
    /// let vslice = VolatileSlice::from(&mut mem[..]);
    /// let res = vslice.write(&[1, 2, 3, 4, 5], 1020);
    ///
    /// assert!(res.is_ok());
    /// assert_eq!(res.unwrap(), 4);
    /// ```
    fn write(&self, mut buf: &[u8], addr: usize) -> Result<usize> {
        if buf.is_empty() {
            return Ok(0);
        }

        if addr >= self.size {
            return Err(MemoryError::OutOfBounds { addr });
        }

        // NOTE: the duality of read <-> write here is correct. This is because we translate a call
        // "volatile_slice.write(buf)" (e.g. "write to volatile_slice from buf") into
        // "buf.read_volatile(volatile_slice)" (e.g. read from buf into volatile_slice)
        buf.read_volatile(&mut self.offset(addr)?)
    }

    /// # Examples
    /// * Read a slice of size 16 at offset 1010 of a 1024-byte `VolatileSlice`.
    ///
    /// ```
    /// # use vm_memory::{Bytes, VolatileMemory, VolatileSlice};
    /// #
    /// let mut mem = [0u8; 1024];
    /// let vslice = VolatileSlice::from(&mut mem[..]);
    /// let buf = &mut [0u8; 16];
    /// let res = vslice.read(buf, 1010);
    ///
    /// assert!(res.is_ok());
    /// assert_eq!(res.unwrap(), 14);
    /// ```
    fn read(&self, mut buf: &mut [u8], addr: usize) -> Result<usize> {
        if buf.is_empty() {
            return Ok(0);
        }

        if addr >= self.size {
            return Err(MemoryError::OutOfBounds { addr });
        }

        // NOTE: The duality of read <-> write here is correct. This is because we translate a call
        // volatile_slice.read(buf) (e.g. read from volatile_slice into buf) into
        // "buf.write_volatile(volatile_slice)" (e.g. write into buf from volatile_slice)
        // Both express data transfer from volatile_slice to buf.
        buf.write_volatile(&self.offset(addr)?)
    }

    /// # Examples
    /// * Write a slice at offset 256.
    ///
    /// ```
    /// # use vm_memory::{Bytes, VolatileMemory, VolatileSlice};
    /// #
    /// # // Create a buffer
    /// # let mut mem = [0u8; 1024];
    /// #
    /// # // Get a `VolatileSlice` from the buffer
    /// # let vslice = VolatileSlice::from(&mut mem[..]);
    /// #
    /// let res = vslice.write_slice(&[1, 2, 3, 4, 5], 256);
    ///
    /// assert!(res.is_ok());
    /// assert_eq!(res.unwrap(), ());
    /// ```
    fn write_slice(&self, buf: &[u8], addr: usize) -> Result<()> {
        // `mark_dirty` called within `self.write`.
        let len = self.write(buf, addr)?;
        if len != buf.len() {
            return Err(MemoryError::PartialBuffer {
                expected: buf.len(),
                completed: len,
            });
        }
        Ok(())
    }

    /// # Examples
    /// * Read a slice of size 16 at offset 256.
    ///
    /// ```
    /// # use vm_memory::{Bytes, VolatileMemory, VolatileSlice};
    /// #
    /// # // Create a buffer
    /// # let mut mem = [0u8; 1024];
    /// #
    /// # // Get a `VolatileSlice` from the buffer
    /// # let vslice = VolatileSlice::from(&mut mem[..]);
    /// #
    /// let buf = &mut [0u8; 16];
    /// let res = vslice.read_slice(buf, 256);
    ///
    /// assert!(res.is_ok());
    /// ```
    fn read_slice(&self, buf: &mut [u8], addr: usize) -> Result<()> {
        let len = self.read(buf, addr)?;
        if len != buf.len() {
            return Err(MemoryError::PartialBuffer {
                expected: buf.len(),
                completed: len,
            });
        }
        Ok(())
    }

    fn read_volatile_from<F>(&self, addr: usize, src: &mut F, count: usize) -> Result<usize>
    where
        F: ReadVolatile,
    {
        let slice = self.offset(addr)?;
        /* Unwrap safe here because (0, min(len, count)) is definitely a valid subslice */
        let mut slice = slice.subslice(0, slice.len().min(count)).unwrap();
        src.read_volatile(&mut slice)
    }

    fn read_exact_volatile_from<F>(&self, addr: usize, src: &mut F, count: usize) -> Result<()>
    where
        F: ReadVolatile,
    {
        src.read_exact_volatile(&mut self.get_slice(addr, count)?)
    }

    fn write_volatile_to<F>(&self, addr: usize, dst: &mut F, count: usize) -> Result<usize>
    where
        F: WriteVolatile,
    {
        let slice = self.offset(addr)?;
        /* Unwrap safe here because (0, min(len, count)) is definitely a valid subslice */
        let slice = slice.subslice(0, slice.len().min(count)).unwrap();
        dst.write_volatile(&slice)
    }

    fn write_all_volatile_to<F>(&self, addr: usize, dst: &mut F, count: usize) -> Result<()>
    where
        F: WriteVolatile,
    {
        dst.write_all_volatile(&self.get_slice(addr, count)?)
    }

    fn store<T: AtomicAccess>(&self, val: T, addr: usize, order: Ordering) -> Result<()> {
        self.get_atomic_ref::<T::A>(addr).map(|r| {
            r.store(val.into(), order);
            self.bitmap.mark_dirty(addr, size_of::<T>())
        })
    }

    fn load<T: AtomicAccess>(&self, addr: usize, order: Ordering) -> Result<T> {
        self.get_atomic_ref::<T::A>(addr)
            .map(|r| r.load(order).into())
    }
}

impl<B: BitmapSlice> VolatileMemory for VolatileSlice<'_, B> {
    type B = B;

    fn len(&self) -> usize {
        self.size
    }

    fn get_slice(&self, offset: usize, count: usize) -> Result<VolatileSlice<B>> {
        self.subslice(offset, count)
    }
}

/// A memory location that supports volatile access to an instance of `T`.
///
/// # Examples
///
/// ```
/// # use vm_memory::VolatileRef;
/// #
/// let mut v = 5u32;
/// let v_ref = unsafe { VolatileRef::new(&mut v as *mut u32 as *mut u8) };
///
/// assert_eq!(v, 5);
/// assert_eq!(v_ref.load(), 5);
/// v_ref.store(500);
/// assert_eq!(v, 500);
/// ```
#[derive(Clone, Copy, Debug)]
pub struct VolatileRef<'a, T, B = ()> {
    addr: *mut Packed<T>,
    bitmap: B,
    mmap: Option<&'a MmapInfo>,
}

impl<'a, T> VolatileRef<'a, T, ()>
where
    T: ByteValued,
{
    /// Creates a [`VolatileRef`](struct.VolatileRef.html) to an instance of `T`.
    ///
    /// # Safety
    ///
    /// To use this safely, the caller must guarantee that the memory at `addr` is big enough for a
    /// `T` and is available for the duration of the lifetime of the new `VolatileRef`. The caller
    /// must also guarantee that all other users of the given chunk of memory are using volatile
    /// accesses.
    pub unsafe fn new(addr: *mut u8) -> Self {
        Self::with_bitmap(addr, (), None)
    }
}

#[allow(clippy::len_without_is_empty)]
impl<'a, T, B> VolatileRef<'a, T, B>
where
    T: ByteValued,
    B: BitmapSlice,
{
    /// Creates a [`VolatileRef`](struct.VolatileRef.html) to an instance of `T`, using the
    /// provided `bitmap` object for dirty page tracking.
    ///
    /// # Safety
    ///
    /// To use this safely, the caller must guarantee that the memory at `addr` is big enough for a
    /// `T` and is available for the duration of the lifetime of the new `VolatileRef`. The caller
    /// must also guarantee that all other users of the given chunk of memory are using volatile
    /// accesses.
    pub unsafe fn with_bitmap(addr: *mut u8, bitmap: B, mmap: Option<&'a MmapInfo>) -> Self {
        VolatileRef {
            addr: addr as *mut Packed<T>,
            bitmap,
            mmap,
        }
    }

    /// Returns a pointer to the underlying memory. Mutable accesses performed
    /// using the resulting pointer are not automatically accounted for by the dirty bitmap
    /// tracking functionality.
    #[deprecated(
        since = "0.12.1",
        note = "Use `.ptr_guard()` or `.ptr_guard_mut()` instead"
    )]
    #[cfg(not(all(feature = "xen", unix)))]
    pub fn as_ptr(&self) -> *mut u8 {
        self.addr as *mut u8
    }

    /// Returns a guard for the pointer to the underlying memory.
    pub fn ptr_guard(&self) -> PtrGuard {
        PtrGuard::read(self.mmap, self.addr as *mut u8, self.len())
    }

    /// Returns a mutable guard for the pointer to the underlying memory.
    pub fn ptr_guard_mut(&self) -> PtrGuardMut {
        PtrGuardMut::write(self.mmap, self.addr as *mut u8, self.len())
    }

    /// Gets the size of the referenced type `T`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::mem::size_of;
    /// # use vm_memory::VolatileRef;
    /// #
    /// let v_ref = unsafe { VolatileRef::<u32>::new(0 as *mut _) };
    /// assert_eq!(v_ref.len(), size_of::<u32>() as usize);
    /// ```
    pub fn len(&self) -> usize {
        size_of::<T>()
    }

    /// Borrows the inner `BitmapSlice`.
    pub fn bitmap(&self) -> &B {
        &self.bitmap
    }

    /// Does a volatile write of the value `v` to the address of this ref.
    #[inline(always)]
    pub fn store(&self, v: T) {
        let guard = self.ptr_guard_mut();

        // SAFETY: Safe because we checked the address and size when creating this VolatileRef.
        unsafe { write_volatile(guard.as_ptr() as *mut Packed<T>, Packed::<T>(v)) };
        self.bitmap.mark_dirty(0, self.len())
    }

    /// Does a volatile read of the value at the address of this ref.
    #[inline(always)]
    pub fn load(&self) -> T {
        let guard = self.ptr_guard();

        // SAFETY: Safe because we checked the address and size when creating this VolatileRef.
        // For the purposes of demonstrating why read_volatile is necessary, try replacing the code
        // in this function with the commented code below and running `cargo test --release`.
        // unsafe { *(self.addr as *const T) }
        unsafe { read_volatile(guard.as_ptr() as *const Packed<T>).0 }
    }

    /// Converts this to a [`VolatileSlice`](struct.VolatileSlice.html) with the same size and
    /// address.
    pub fn to_slice(&self) -> VolatileSlice<'a, B> {
        // SAFETY: Safe because we checked the address and size when creating this VolatileRef.
        unsafe {
            VolatileSlice::with_bitmap(
                self.addr as *mut u8,
                size_of::<T>(),
                self.bitmap.clone(),
                self.mmap,
            )
        }
    }
}

/// A memory location that supports volatile access to an array of elements of type `T`.
///
/// # Examples
///
/// ```
/// # use vm_memory::VolatileArrayRef;
/// #
/// let mut v = [5u32; 1];
/// let v_ref = unsafe { VolatileArrayRef::new(&mut v[0] as *mut u32 as *mut u8, v.len()) };
///
/// assert_eq!(v[0], 5);
/// assert_eq!(v_ref.load(0), 5);
/// v_ref.store(0, 500);
/// assert_eq!(v[0], 500);
/// ```
#[derive(Clone, Copy, Debug)]
pub struct VolatileArrayRef<'a, T, B = ()> {
    addr: *mut u8,
    nelem: usize,
    bitmap: B,
    phantom: PhantomData<&'a T>,
    mmap: Option<&'a MmapInfo>,
}

impl<'a, T> VolatileArrayRef<'a, T>
where
    T: ByteValued,
{
    /// Creates a [`VolatileArrayRef`](struct.VolatileArrayRef.html) to an array of elements of
    /// type `T`.
    ///
    /// # Safety
    ///
    /// To use this safely, the caller must guarantee that the memory at `addr` is big enough for
    /// `nelem` values of type `T` and is available for the duration of the lifetime of the new
    /// `VolatileRef`. The caller must also guarantee that all other users of the given chunk of
    /// memory are using volatile accesses.
    pub unsafe fn new(addr: *mut u8, nelem: usize) -> Self {
        Self::with_bitmap(addr, nelem, (), None)
    }
}

impl<'a, T, B> VolatileArrayRef<'a, T, B>
where
    T: ByteValued,
    B: BitmapSlice,
{
    /// Creates a [`VolatileArrayRef`](struct.VolatileArrayRef.html) to an array of elements of
    /// type `T`, using the provided `bitmap` object for dirty page tracking.
    ///
    /// # Safety
    ///
    /// To use this safely, the caller must guarantee that the memory at `addr` is big enough for
    /// `nelem` values of type `T` and is available for the duration of the lifetime of the new
    /// `VolatileRef`. The caller must also guarantee that all other users of the given chunk of
    /// memory are using volatile accesses.
    pub unsafe fn with_bitmap(
        addr: *mut u8,
        nelem: usize,
        bitmap: B,
        mmap: Option<&'a MmapInfo>,
    ) -> Self {
        VolatileArrayRef {
            addr,
            nelem,
            bitmap,
            phantom: PhantomData,
            mmap,
        }
    }

    /// Returns `true` if this array is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use vm_memory::VolatileArrayRef;
    /// #
    /// let v_array = unsafe { VolatileArrayRef::<u32>::new(0 as *mut _, 0) };
    /// assert!(v_array.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.nelem == 0
    }

    /// Returns the number of elements in the array.
    ///
    /// # Examples
    ///
    /// ```
    /// # use vm_memory::VolatileArrayRef;
    /// #
    /// # let v_array = unsafe { VolatileArrayRef::<u32>::new(0 as *mut _, 1) };
    /// assert_eq!(v_array.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.nelem
    }

    /// Returns the size of `T`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::mem::size_of;
    /// # use vm_memory::VolatileArrayRef;
    /// #
    /// let v_ref = unsafe { VolatileArrayRef::<u32>::new(0 as *mut _, 0) };
    /// assert_eq!(v_ref.element_size(), size_of::<u32>() as usize);
    /// ```
    pub fn element_size(&self) -> usize {
        size_of::<T>()
    }

    /// Returns a pointer to the underlying memory. Mutable accesses performed
    /// using the resulting pointer are not automatically accounted for by the dirty bitmap
    /// tracking functionality.
    #[deprecated(
        since = "0.12.1",
        note = "Use `.ptr_guard()` or `.ptr_guard_mut()` instead"
    )]
    #[cfg(not(all(feature = "xen", unix)))]
    pub fn as_ptr(&self) -> *mut u8 {
        self.addr
    }

    /// Returns a guard for the pointer to the underlying memory.
    pub fn ptr_guard(&self) -> PtrGuard {
        PtrGuard::read(self.mmap, self.addr, self.len())
    }

    /// Returns a mutable guard for the pointer to the underlying memory.
    pub fn ptr_guard_mut(&self) -> PtrGuardMut {
        PtrGuardMut::write(self.mmap, self.addr, self.len())
    }

    /// Borrows the inner `BitmapSlice`.
    pub fn bitmap(&self) -> &B {
        &self.bitmap
    }

    /// Converts this to a `VolatileSlice` with the same size and address.
    pub fn to_slice(&self) -> VolatileSlice<'a, B> {
        // SAFETY: Safe as long as the caller validated addr when creating this object.
        unsafe {
            VolatileSlice::with_bitmap(
                self.addr,
                self.nelem * self.element_size(),
                self.bitmap.clone(),
                self.mmap,
            )
        }
    }

    /// Does a volatile read of the element at `index`.
    ///
    /// # Panics
    ///
    /// Panics if `index` is less than the number of elements of the array to which `&self` points.
    pub fn ref_at(&self, index: usize) -> VolatileRef<'a, T, B> {
        assert!(index < self.nelem);
        // SAFETY: Safe because the memory has the same lifetime and points to a subset of the
        // memory of the VolatileArrayRef.
        unsafe {
            // byteofs must fit in an isize as it was checked in get_array_ref.
            let byteofs = (self.element_size() * index) as isize;
            let ptr = self.addr.offset(byteofs);
            VolatileRef::with_bitmap(ptr, self.bitmap.slice_at(byteofs as usize), self.mmap)
        }
    }

    /// Does a volatile read of the element at `index`.
    pub fn load(&self, index: usize) -> T {
        self.ref_at(index).load()
    }

    /// Does a volatile write of the element at `index`.
    pub fn store(&self, index: usize, value: T) {
        // The `VolatileRef::store` call below implements the required dirty bitmap tracking logic,
        // so no need to do that in this method as well.
        self.ref_at(index).store(value)
    }

    /// Copies as many elements of type `T` as possible from this array to `buf`.
    ///
    /// Copies `self.len()` or `buf.len()` times the size of `T` bytes, whichever is smaller,
    /// to `buf`. The copy happens from smallest to largest address in `T` sized chunks
    /// using volatile reads.
    ///
    /// # Examples
    ///
    /// ```
    /// # use vm_memory::VolatileArrayRef;
    /// #
    /// let mut v = [0u8; 32];
    /// let v_ref = unsafe { VolatileArrayRef::new(v.as_mut_ptr(), v.len()) };
    ///
    /// let mut buf = [5u8; 16];
    /// v_ref.copy_to(&mut buf[..]);
    /// for &v in &buf[..] {
    ///     assert_eq!(v, 0);
    /// }
    /// ```
    pub fn copy_to(&self, buf: &mut [T]) -> usize {
        // A fast path for u8/i8
        if size_of::<T>() == 1 {
            let source = self.to_slice();
            let total = buf.len().min(source.len());

            // SAFETY:
            // - dst is valid for writes of at least `total`, since total <= buf.len()
            // - src is valid for reads of at least `total` as total <= source.len()
            // - The regions are non-overlapping as `src` points to guest memory and `buf` is
            //   a slice and thus has to live outside of guest memory (there can be more slices to
            //   guest memory without violating rust's aliasing rules)
            // - size is always a multiple of alignment, so treating *mut T as *mut u8 is fine
            return unsafe {
                copy_from_volatile_slice(buf.as_mut_ptr() as *mut u8, &source, total)
            };
        }

        let guard = self.ptr_guard();
        let mut ptr = guard.as_ptr() as *const Packed<T>;
        let start = ptr;

        for v in buf.iter_mut().take(self.len()) {
            // SAFETY: read_volatile is safe because the pointers are range-checked when
            // the slices are created, and they never escape the VolatileSlices.
            // ptr::add is safe because get_array_ref() validated that
            // size_of::<T>() * self.len() fits in an isize.
            unsafe {
                *v = read_volatile(ptr).0;
                ptr = ptr.add(1);
            }
        }

        // SAFETY: It is guaranteed that start and ptr point to the regions of the same slice.
        unsafe { ptr.offset_from(start) as usize }
    }

    /// Copies as many bytes as possible from this slice to the provided `slice`.
    ///
    /// The copies happen in an undefined order.
    ///
    /// # Examples
    ///
    /// ```
    /// # use vm_memory::VolatileArrayRef;
    /// #
    /// let mut v = [0u8; 32];
    /// let v_ref = unsafe { VolatileArrayRef::<u8>::new(v.as_mut_ptr(), v.len()) };
    /// let mut buf = [5u8; 16];
    /// let v_ref2 = unsafe { VolatileArrayRef::<u8>::new(buf.as_mut_ptr(), buf.len()) };
    ///
    /// v_ref.copy_to_volatile_slice(v_ref2.to_slice());
    /// for &v in &buf[..] {
    ///     assert_eq!(v, 0);
    /// }
    /// ```
    pub fn copy_to_volatile_slice<S: BitmapSlice>(&self, slice: VolatileSlice<S>) {
        // SAFETY: Safe because the pointers are range-checked when the slices
        // are created, and they never escape the VolatileSlices.
        // FIXME: ... however, is it really okay to mix non-volatile
        // operations such as copy with read_volatile and write_volatile?
        unsafe {
            let count = min(self.len() * self.element_size(), slice.size);
            copy(self.addr, slice.addr, count);
            slice.bitmap.mark_dirty(0, count);
        }
    }

    /// Copies as many elements of type `T` as possible from `buf` to this slice.
    ///
    /// Copies `self.len()` or `buf.len()` times the size of `T` bytes, whichever is smaller,
    /// to this slice's memory. The copy happens from smallest to largest address in
    /// `T` sized chunks using volatile writes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use vm_memory::VolatileArrayRef;
    /// #
    /// let mut v = [0u8; 32];
    /// let v_ref = unsafe { VolatileArrayRef::<u8>::new(v.as_mut_ptr(), v.len()) };
    ///
    /// let buf = [5u8; 64];
    /// v_ref.copy_from(&buf[..]);
    /// for &val in &v[..] {
    ///     assert_eq!(5u8, val);
    /// }
    /// ```
    pub fn copy_from(&self, buf: &[T]) {
        // A fast path for u8/i8
        if size_of::<T>() == 1 {
            let destination = self.to_slice();
            let total = buf.len().min(destination.len());

            // absurd formatting brought to you by clippy
            // SAFETY:
            // - dst is valid for writes of at least `total`, since total <= destination.len()
            // - src is valid for reads of at least `total` as total <= buf.len()
            // - The regions are non-overlapping as `dst` points to guest memory and `buf` is
            //   a slice and thus has to live outside of guest memory (there can be more slices to
            //   guest memory without violating rust's aliasing rules)
            // - size is always a multiple of alignment, so treating *const T as *const u8 is fine
            unsafe { copy_to_volatile_slice(&destination, buf.as_ptr() as *const u8, total) };
        } else {
            let guard = self.ptr_guard_mut();
            let start = guard.as_ptr();
            let mut ptr = start as *mut Packed<T>;

            for &v in buf.iter().take(self.len()) {
                // SAFETY: write_volatile is safe because the pointers are range-checked when
                // the slices are created, and they never escape the VolatileSlices.
                // ptr::add is safe because get_array_ref() validated that
                // size_of::<T>() * self.len() fits in an isize.
                unsafe {
                    write_volatile(ptr, Packed::<T>(v));
                    ptr = ptr.add(1);
                }
            }

            self.bitmap.mark_dirty(0, ptr as usize - start as usize);
        }
    }
}

impl<'a, B: BitmapSlice> From<VolatileSlice<'a, B>> for VolatileArrayRef<'a, u8, B> {
    fn from(slice: VolatileSlice<'a, B>) -> Self {
        // SAFETY: Safe because the result has the same lifetime and points to the same
        // memory as the incoming VolatileSlice.
        unsafe { VolatileArrayRef::with_bitmap(slice.addr, slice.len(), slice.bitmap, slice.mmap) }
    }
}

// Return the largest value that `addr` is aligned to. Forcing this function to return 1 will
// cause test_non_atomic_access to fail.
fn alignment(addr: usize) -> usize {
    // Rust is silly and does not let me write addr & -addr.
    addr & (!addr + 1)
}

pub(crate) mod copy_slice_impl {
    use super::*;

    // SAFETY: Has the same safety requirements as `read_volatile` + `write_volatile`, namely:
    // - `src_addr` and `dst_addr` must be valid for reads/writes.
    // - `src_addr` and `dst_addr` must be properly aligned with respect to `align`.
    // - `src_addr` must point to a properly initialized value, which is true here because
    //   we're only using integer primitives.
    unsafe fn copy_single(align: usize, src_addr: *const u8, dst_addr: *mut u8) {
        match align {
            8 => write_volatile(dst_addr as *mut u64, read_volatile(src_addr as *const u64)),
            4 => write_volatile(dst_addr as *mut u32, read_volatile(src_addr as *const u32)),
            2 => write_volatile(dst_addr as *mut u16, read_volatile(src_addr as *const u16)),
            1 => write_volatile(dst_addr, read_volatile(src_addr)),
            _ => unreachable!(),
        }
    }

    /// Copies `total` bytes from `src` to `dst` using a loop of volatile reads and writes
    ///
    /// SAFETY: `src` and `dst` must be point to a contiguously allocated memory region of at least
    /// length `total`. The regions must not overlap
    unsafe fn copy_slice_volatile(mut dst: *mut u8, mut src: *const u8, total: usize) -> usize {
        let mut left = total;

        let align = min(alignment(src as usize), alignment(dst as usize));

        let mut copy_aligned_slice = |min_align| {
            if align < min_align {
                return;
            }

            while left >= min_align {
                // SAFETY: Safe because we check alignment beforehand, the memory areas are valid
                // for reads/writes, and the source always contains a valid value.
                unsafe { copy_single(min_align, src, dst) };

                left -= min_align;

                if left == 0 {
                    break;
                }

                // SAFETY: We only explain the invariants for `src`, the argument for `dst` is
                // analogous.
                // - `src` and `src + min_align` are within (or one byte past) the same allocated object
                //   This is given by the invariant on this function ensuring that [src, src + total)
                //   are part of the same allocated object, and the condition on the while loop
                //   ensures that we do not go outside this object
                // - The computed offset in bytes cannot overflow isize, because `min_align` is at
                //   most 8 when the closure is called (see below)
                // - The sum `src as usize + min_align` can only wrap around if src as usize + min_align - 1 == usize::MAX,
                //   however in this case, left == 0, and we'll have exited the loop above.
                unsafe {
                    src = src.add(min_align);
                    dst = dst.add(min_align);
                }
            }
        };

        if size_of::<usize>() > 4 {
            copy_aligned_slice(8);
        }
        copy_aligned_slice(4);
        copy_aligned_slice(2);
        copy_aligned_slice(1);

        total
    }

    /// Copies `total` bytes from `src` to `dst`
    ///
    /// SAFETY: `src` and `dst` must be point to a contiguously allocated memory region of at least
    /// length `total`. The regions must not overlap
    unsafe fn copy_slice(dst: *mut u8, src: *const u8, total: usize) -> usize {
        if total <= size_of::<usize>() {
            // SAFETY: Invariants of copy_slice_volatile are the same as invariants of copy_slice
            unsafe {
                copy_slice_volatile(dst, src, total);
            };
        } else {
            // SAFETY:
            // - Both src and dst are allocated for reads/writes of length `total` by function
            //   invariant
            // - src and dst are properly aligned, as any alignment is valid for u8
            // - The regions are not overlapping by function invariant
            unsafe {
                core::ptr::copy_nonoverlapping(src, dst, total);
            }
        }

        total
    }

    /// Copies `total` bytes from `slice` to `dst`
    ///
    /// SAFETY: `slice` and `dst` must be point to a contiguously allocated memory region of at
    /// least length `total`. The regions must not overlap.
    pub(crate) unsafe fn copy_from_volatile_slice<B: BitmapSlice>(
        dst: *mut u8,
        slice: &VolatileSlice<'_, B>,
        total: usize,
    ) -> usize {
        let guard = slice.ptr_guard();

        // SAFETY: guaranteed by function invariants.
        copy_slice(dst, guard.as_ptr(), total)
    }

    /// Copies `total` bytes from 'src' to `slice`
    ///
    /// SAFETY: `slice` and `src` must be point to a contiguously allocated memory region of at
    /// least length `total`. The regions must not overlap.
    pub(crate) unsafe fn copy_to_volatile_slice<B: BitmapSlice>(
        slice: &VolatileSlice<'_, B>,
        src: *const u8,
        total: usize,
    ) -> usize {
        let guard = slice.ptr_guard_mut();

        // SAFETY: guaranteed by function invariants.
        let count = copy_slice(guard.as_ptr(), src, total);
        slice.bitmap.mark_dirty(0, count);
        count
    }
}
