// Portions Copyright 2019 Red Hat, Inc.
//
// Portions Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! Define the `ByteValued` trait to mark that it is safe to instantiate the struct with random
//! data.

use super::memory_io::{Read, ReadVolatile, Write, WriteVolatile};
use core::mem::{size_of, MaybeUninit};
use core::result::Result;
use core::slice::{from_raw_parts, from_raw_parts_mut};
use core::sync::atomic::Ordering;

use super::atomic_integer::AtomicInteger;
// use crate::volatile_memory::VolatileSlice;

/// Types for which it is safe to initialize from raw data.
///
/// # Safety
///
/// A type `T` is `ByteValued` if and only if it can be initialized by reading its contents from a
/// byte array.  This is generally true for all plain-old-data structs.  It is notably not true for
/// any type that includes a reference. It is generally also not safe for non-packed structs, as
/// compiler-inserted padding is considered uninitialized memory, and thus reads/writing it will
/// cause undefined behavior.
///
/// Implementing this trait guarantees that it is safe to instantiate the struct with random data.
pub unsafe trait ByteValued: Copy + Send + Sync {
    /// Converts a slice of raw data into a reference of `Self`.
    ///
    /// The value of `data` is not copied. Instead a reference is made from the given slice. The
    /// value of `Self` will depend on the representation of the type in memory, and may change in
    /// an unstable fashion.
    ///
    /// This will return `None` if the length of data does not match the size of `Self`, or if the
    /// data is not aligned for the type of `Self`.
    fn from_slice(data: &[u8]) -> Option<&Self> {
        // Early out to avoid an unneeded `align_to` call.
        if data.len() != size_of::<Self>() {
            return None;
        }

        // SAFETY: Safe because the ByteValued trait asserts any data is valid for this type, and
        // we ensured the size of the pointer's buffer is the correct size. The `align_to` method
        // ensures that we don't have any unaligned references. This aliases a pointer, but because
        // the pointer is from a const slice reference, there are no mutable aliases. Finally, the
        // reference returned can not outlive data because they have equal implicit lifetime
        // constraints.
        match unsafe { data.align_to::<Self>() } {
            ([], [mid], []) => Some(mid),
            _ => None,
        }
    }

    /// Converts a mutable slice of raw data into a mutable reference of `Self`.
    ///
    /// Because `Self` is made from a reference to the mutable slice, mutations to the returned
    /// reference are immediately reflected in `data`. The value of the returned `Self` will depend
    /// on the representation of the type in memory, and may change in an unstable fashion.
    ///
    /// This will return `None` if the length of data does not match the size of `Self`, or if the
    /// data is not aligned for the type of `Self`.
    fn from_mut_slice(data: &mut [u8]) -> Option<&mut Self> {
        // Early out to avoid an unneeded `align_to_mut` call.
        if data.len() != size_of::<Self>() {
            return None;
        }

        // SAFETY: Safe because the ByteValued trait asserts any data is valid for this type, and
        // we ensured the size of the pointer's buffer is the correct size. The `align_to` method
        // ensures that we don't have any unaligned references. This aliases a pointer, but because
        // the pointer is from a mut slice reference, we borrow the passed in mutable reference.
        // Finally, the reference returned can not outlive data because they have equal implicit
        // lifetime constraints.
        match unsafe { data.align_to_mut::<Self>() } {
            ([], [mid], []) => Some(mid),
            _ => None,
        }
    }

    /// Converts a reference to `self` into a slice of bytes.
    ///
    /// The value of `self` is not copied. Instead, the slice is made from a reference to `self`.
    /// The value of bytes in the returned slice will depend on the representation of the type in
    /// memory, and may change in an unstable fashion.
    fn as_slice(&self) -> &[u8] {
        // SAFETY: Safe because the entire size of self is accessible as bytes because the trait
        // guarantees it. The lifetime of the returned slice is the same as the passed reference,
        // so that no dangling pointers will result from this pointer alias.
        unsafe { from_raw_parts(self as *const Self as *const u8, size_of::<Self>()) }
    }

    /// Converts a mutable reference to `self` into a mutable slice of bytes.
    ///
    /// Because the slice is made from a reference to `self`, mutations to the returned slice are
    /// immediately reflected in `self`. The value of bytes in the returned slice will depend on
    /// the representation of the type in memory, and may change in an unstable fashion.
    fn as_mut_slice(&mut self) -> &mut [u8] {
        // SAFETY: Safe because the entire size of self is accessible as bytes because the trait
        // guarantees it. The trait also guarantees that any combination of bytes is valid for this
        // type, so modifying them in the form of a byte slice is valid. The lifetime of the
        // returned slice is the same as the passed reference, so that no dangling pointers will
        // result from this pointer alias. Although this does alias a mutable pointer, we do so by
        // exclusively borrowing the given mutable reference.
        unsafe { from_raw_parts_mut(self as *mut Self as *mut u8, size_of::<Self>()) }
    }
}

macro_rules! byte_valued_array {
    ($T:ty, $($N:expr)+) => {
        $(
            // SAFETY: All intrinsic types and arrays of intrinsic types are ByteValued.
            // They are just numbers.
            unsafe impl ByteValued for [$T; $N] {}
        )+
    }
}

macro_rules! byte_valued_type {
    ($T:ty) => {
        // SAFETY: Safe as long T is POD.
        // We are using this macro to generated the implementation for integer types below.
        unsafe impl ByteValued for $T {}
        byte_valued_array! {
            $T,
            0  1  2  3  4  5  6  7  8  9
            10 11 12 13 14 15 16 17 18 19
            20 21 22 23 24 25 26 27 28 29
            30 31 32
        }
    };
}

byte_valued_type!(u8);
byte_valued_type!(u16);
byte_valued_type!(u32);
byte_valued_type!(u64);
byte_valued_type!(u128);
byte_valued_type!(usize);
byte_valued_type!(i8);
byte_valued_type!(i16);
byte_valued_type!(i32);
byte_valued_type!(i64);
byte_valued_type!(i128);
byte_valued_type!(isize);

/// A trait used to identify types which can be accessed atomically by proxy.
pub trait AtomicAccess:
    ByteValued
    // Could not find a more succinct way of stating that `Self` can be converted
    // into `Self::A::V`, and the other way around.
    + From<<<Self as AtomicAccess>::A as AtomicInteger>::V>
    + Into<<<Self as AtomicAccess>::A as AtomicInteger>::V>
{
    /// The `AtomicInteger` that atomic operations on `Self` are based on.
    type A: AtomicInteger;
}

macro_rules! impl_atomic_access {
    ($T:ty, $A:path) => {
        impl AtomicAccess for $T {
            type A = $A;
        }
    };
}

impl_atomic_access!(i8, core::sync::atomic::AtomicI8);
impl_atomic_access!(i16, core::sync::atomic::AtomicI16);
impl_atomic_access!(i32, core::sync::atomic::AtomicI32);
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "powerpc64",
    target_arch = "s390x",
    target_arch = "riscv64"
))]
impl_atomic_access!(i64, core::sync::atomic::AtomicI64);

impl_atomic_access!(u8, core::sync::atomic::AtomicU8);
impl_atomic_access!(u16, core::sync::atomic::AtomicU16);
impl_atomic_access!(u32, core::sync::atomic::AtomicU32);
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "powerpc64",
    target_arch = "s390x",
    target_arch = "riscv64"
))]
impl_atomic_access!(u64, core::sync::atomic::AtomicU64);

impl_atomic_access!(isize, core::sync::atomic::AtomicIsize);
impl_atomic_access!(usize, core::sync::atomic::AtomicUsize);

/// A container to host a range of bytes and access its content.
///
/// Candidates which may implement this trait include:
/// - anonymous memory areas
/// - mmapped memory areas
/// - data files
/// - a proxy to access memory on remote
pub trait Bytes<A> {
    /// Associated error codes
    type E;

    /// Writes a slice into the container at `addr`.
    ///
    /// Returns the number of bytes written. The number of bytes written can
    /// be less than the length of the slice if there isn't enough room in the
    /// container.
    ///
    /// If the given slice is empty (e.g. has length 0), always returns `Ok(0)`, even if `addr`
    /// is otherwise out of bounds. However, if the container is empty, it will
    /// return an error (unless the slice is also empty, in which case the above takes precedence).
    ///
    /// ```rust
    /// # use vm_memory::{Bytes, VolatileMemoryError, VolatileSlice};
    /// let mut arr = [1, 2, 3, 4, 5];
    /// let slice = VolatileSlice::from(arr.as_mut_slice());
    ///
    /// assert_eq!(slice.write(&[1, 2, 3], 0).unwrap(), 3);
    /// assert_eq!(slice.write(&[1, 2, 3], 3).unwrap(), 2);
    /// assert!(matches!(
    ///     slice.write(&[1, 2, 3], 5).unwrap_err(),
    ///     VolatileMemoryError::OutOfBounds { addr: 5 }
    /// ));
    /// assert_eq!(slice.write(&[], 5).unwrap(), 0);
    /// ```
    fn write(&self, buf: &[u8], addr: A) -> Result<usize, Self::E>;

    /// Reads data from the container at `addr` into a slice.
    ///
    /// Returns the number of bytes read. The number of bytes read can be less than the length
    /// of the slice if there isn't enough data within the container.
    ///
    /// If the given slice is empty (e.g. has length 0), always returns `Ok(0)`, even if `addr`
    /// is otherwise out of bounds. However, if the container is empty, it will
    /// return an error (unless the slice is also empty, in which case the above takes precedence).
    fn read(&self, buf: &mut [u8], addr: A) -> Result<usize, Self::E>;

    /// Writes the entire content of a slice into the container at `addr`.
    ///
    /// If the given slice is empty (e.g. has length 0), always returns `Ok(0)`, even if `addr`
    /// is otherwise out of bounds.
    ///
    /// # Errors
    ///
    /// Returns an error if there isn't enough space within the container to write the entire slice.
    /// Part of the data may have been copied nevertheless.
    fn write_slice(&self, buf: &[u8], addr: A) -> Result<(), Self::E>;

    /// Reads data from the container at `addr` to fill an entire slice.
    ///
    /// If the given slice is empty (e.g. has length 0), always returns `Ok(0)`, even if `addr`
    /// is otherwise out of bounds.
    ///
    /// # Errors
    ///
    /// Returns an error if there isn't enough data within the container to fill the entire slice.
    /// Part of the data may have been copied nevertheless.
    fn read_slice(&self, buf: &mut [u8], addr: A) -> Result<(), Self::E>;

    /// Writes an object into the container at `addr`.
    ///
    /// # Errors
    ///
    /// Returns an error if the object doesn't fit inside the container.
    fn write_obj<T: ByteValued>(&self, val: T, addr: A) -> Result<(), Self::E> {
        self.write_slice(val.as_slice(), addr)
    }

    /// Reads an object from the container at `addr`.
    ///
    /// Reading from a volatile area isn't strictly safe as it could change mid-read.
    /// However, as long as the type T is plain old data and can handle random initialization,
    /// everything will be OK.
    ///
    /// # Errors
    ///
    /// Returns an error if there's not enough data inside the container.
    fn read_obj<T: ByteValued>(&self, addr: A) -> Result<T, Self::E> {
        // SAFETY: ByteValued objects must be assignable from a arbitrary byte
        // sequence and are mandated to be packed.
        // Hence, zeroed memory is a fine initialization.
        let mut result: T = unsafe { MaybeUninit::<T>::zeroed().assume_init() };
        self.read_slice(result.as_mut_slice(), addr).map(|_| result)
    }

    /// Reads up to `count` bytes from `src` and writes them into the container at `addr`.
    /// Unlike `VolatileRead::read_volatile`, this function retries on `EINTR` being returned from
    /// the underlying I/O `read` operation.
    ///
    /// Returns the number of bytes written into the container.
    ///
    /// # Arguments
    /// * `addr` - Begin writing at this address.
    /// * `src` - Copy from `src` into the container.
    /// * `count` - Copy `count` bytes from `src` into the container.
    ///
    /// # Examples
    ///
    /// * Read bytes from /dev/urandom (uses the `backend-mmap` feature)
    ///
    /// ```
    /// # #[cfg(all(feature = "backend-mmap", feature = "rawfd"))]
    /// # {
    /// # use vm_memory::{Address, GuestMemory, Bytes, GuestAddress, GuestMemoryMmap};
    /// # use std::fs::File;
    /// # use std::path::Path;
    /// #
    /// # let start_addr = GuestAddress(0x1000);
    /// # let gm = GuestMemoryMmap::<()>::from_ranges(&vec![(start_addr, 0x400)])
    /// #    .expect("Could not create guest memory");
    /// # let addr = GuestAddress(0x1010);
    /// # let mut file = if cfg!(target_family = "unix") {
    /// let mut file = File::open(Path::new("/dev/urandom")).expect("Could not open /dev/urandom");
    /// #   file
    /// # } else {
    /// #   File::open(Path::new("c:\\Windows\\system32\\ntoskrnl.exe"))
    /// #       .expect("Could not open c:\\Windows\\system32\\ntoskrnl.exe")
    /// # };
    ///
    /// gm.read_volatile_from(addr, &mut file, 128)
    ///     .expect("Could not read from /dev/urandom into guest memory");
    ///
    /// let read_addr = addr.checked_add(8).expect("Could not compute read address");
    /// let rand_val: u32 = gm
    ///     .read_obj(read_addr)
    ///     .expect("Could not read u32 val from /dev/urandom");
    /// # }
    /// ```
    fn read_volatile_from<F>(&self, addr: A, src: &mut F, count: usize) -> Result<usize, Self::E>
    where
        F: ReadVolatile;

    /// Reads exactly `count` bytes from an object and writes them into the container at `addr`.
    ///
    /// # Errors
    ///
    /// Returns an error if `count` bytes couldn't have been copied from `src` to the container.
    /// Part of the data may have been copied nevertheless.
    ///
    /// # Arguments
    /// * `addr` - Begin writing at this address.
    /// * `src` - Copy from `src` into the container.
    /// * `count` - Copy exactly `count` bytes from `src` into the container.
    fn read_exact_volatile_from<F>(
        &self,
        addr: A,
        src: &mut F,
        count: usize,
    ) -> Result<(), Self::E>
    where
        F: ReadVolatile;

    /// Reads up to `count` bytes from the container at `addr` and writes them into `dst`.
    /// Unlike `VolatileWrite::write_volatile`, this function retries on `EINTR` being returned by
    /// the underlying I/O `write` operation.
    ///
    /// Returns the number of bytes written into the object.
    ///
    /// # Arguments
    /// * `addr` - Begin reading from this address.
    /// * `dst` - Copy from the container to `dst`.
    /// * `count` - Copy `count` bytes from the container to `dst`.
    fn write_volatile_to<F>(&self, addr: A, dst: &mut F, count: usize) -> Result<usize, Self::E>
    where
        F: WriteVolatile;

    /// Reads exactly `count` bytes from the container at `addr` and writes them into an object.
    ///
    /// # Errors
    ///
    /// Returns an error if `count` bytes couldn't have been copied from the container to `dst`.
    /// Part of the data may have been copied nevertheless.
    ///
    /// # Arguments
    /// * `addr` - Begin reading from this address.
    /// * `dst` - Copy from the container to `dst`.
    /// * `count` - Copy exactly `count` bytes from the container to `dst`.
    fn write_all_volatile_to<F>(&self, addr: A, dst: &mut F, count: usize) -> Result<(), Self::E>
    where
        F: WriteVolatile;

    /// Atomically store a value at the specified address.
    fn store<T: AtomicAccess>(&self, val: T, addr: A, order: Ordering) -> Result<(), Self::E>;

    /// Atomically load a value from the specified address.
    fn load<T: AtomicAccess>(&self, addr: A, order: Ordering) -> Result<T, Self::E>;
}
