// Portions Copyright 2019 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// Copyright (C) 2024 Red Hat, Inc. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

use alloc::collections::VecDeque;
use alloc::vec::Vec;
use alloc::vec;
// use std::io::{self, Read, Write};
// use alloc::fmt::{Read, Write};
use core::mem::{size_of, MaybeUninit};
use core::ops::Deref;
use core::ptr::copy_nonoverlapping;
use core::{cmp, result};

use crate::{DescriptorChain, Error};
use vm_memory::bitmap::{BitmapSlice, WithBitmapSlice};
use vm_memory::{
    Address, ByteValued, GuestMemory, GuestMemoryRegion, MemoryRegionAddress, VolatileSlice,
};

pub type Result<T> = result::Result<T, Error>;

#[derive(Clone)]
struct DescriptorChainConsumer<'a, B> {
    buffers: VecDeque<VolatileSlice<'a, B>>,
    bytes_consumed: usize,
}

impl<'a, B: BitmapSlice> DescriptorChainConsumer<'a, B> {
    fn available_bytes(&self) -> usize {
        // This is guaranteed not to overflow because the total length of the chain
        // is checked during all creations of `DescriptorChainConsumer` (see
        // `Reader::new()` and `Writer::new()`).
        self.buffers
            .iter()
            .fold(0usize, |count, vs| count + vs.len())
    }

    fn bytes_consumed(&self) -> usize {
        self.bytes_consumed
    }

    /// Consumes at most `count` bytes from the `DescriptorChain`. Callers must provide a function
    /// that takes a `&[VolatileSlice]` and returns the total number of bytes consumed. This
    /// function guarantees that the combined length of all the slices in the `&[VolatileSlice]` is
    /// less than or equal to `count`.
    ///
    /// # Errors
    ///
    /// If the provided function returns any error then no bytes are consumed from the buffer and
    /// the error is returned to the caller.
    fn consume<F>(&mut self, count: usize, f: F) -> Result<usize>
    where
        F: FnOnce(&[&VolatileSlice<B>]) -> Result<usize>,
    {
        let mut buflen = 0;
        let mut bufs = Vec::with_capacity(self.buffers.len());
        for vs in &self.buffers {
            if buflen >= count {
                break;
            }

            bufs.push(vs);

            let rem = count - buflen;
            if rem < vs.len() {
                buflen += rem;
            } else {
                buflen += vs.len();
            }
        }

        if bufs.is_empty() {
            return Ok(0);
        }

        let bytes_consumed = f(&bufs)?;

        // This can happen if a driver tricks a device into reading/writing more data than
        // fits in a `usize`.
        let total_bytes_consumed =
            self.bytes_consumed
                .checked_add(bytes_consumed)
                .ok_or_else(|| {
                    Error::DescriptorChainOverflow
                })?;

        let mut rem = bytes_consumed;
        while let Some(vs) = self.buffers.pop_front() {
            if rem < vs.len() {
                // Split the slice and push the remainder back into the buffer list. Safe because we
                // know that `rem` is not out of bounds due to the check and we checked the bounds
                // on `vs` when we added it to the buffer list.
                self.buffers.push_front(vs.offset(rem).unwrap());
                break;
            }

            // No need for checked math because we know that `vs.size() <= rem`.
            rem -= vs.len();
        }

        self.bytes_consumed = total_bytes_consumed;

        Ok(bytes_consumed)
    }

    fn split_at(&mut self, offset: usize) -> Result<DescriptorChainConsumer<'a, B>> {
        let mut rem = offset;
        let pos = self.buffers.iter().position(|vs| {
            if rem < vs.len() {
                true
            } else {
                rem -= vs.len();
                false
            }
        });

        if let Some(at) = pos {
            let mut other = self.buffers.split_off(at);

            if rem > 0 {
                // There must be at least one element in `other` because we checked
                // its `size` value in the call to `position` above.
                let front = other.pop_front().expect("empty VecDeque after split");
                self.buffers
                    .push_back(front.subslice(0, rem).map_err(Error::VolatileMemoryError)?);
                other.push_front(front.offset(rem).map_err(Error::VolatileMemoryError)?);
            }

            Ok(DescriptorChainConsumer {
                buffers: other,
                bytes_consumed: 0,
            })
        } else if rem == 0 {
            Ok(DescriptorChainConsumer {
                buffers: VecDeque::new(),
                bytes_consumed: 0,
            })
        } else {
            Err(Error::SplitOutOfBounds(offset))
        }
    }
}

/// Provides high-level interface over the sequence of memory regions
/// defined by readable descriptors in the descriptor chain.
///
/// Note that virtio spec requires driver to place any device-writable
/// descriptors after any device-readable descriptors (2.6.4.2 in Virtio Spec v1.1).
/// Reader will skip iterating over descriptor chain when first writable
/// descriptor is encountered.
#[derive(Clone)]
pub struct Reader<'a, B = ()> {
    buffer: DescriptorChainConsumer<'a, B>,
}

impl<'a, B: BitmapSlice> Reader<'a, B> {
    /// Construct a new Reader wrapper over `desc_chain`.
    pub fn new<M, T>(mem: &'a M, desc_chain: DescriptorChain<T>) -> Result<Reader<'a, B>>
    where
        M: GuestMemory,
        <<M as GuestMemory>::R as GuestMemoryRegion>::B: WithBitmapSlice<'a, S = B>,
        T: Deref,
        T::Target: GuestMemory + Sized,
    {
        let mut total_len: usize = 0;
        let buffers = desc_chain
            .readable()
            .map(|desc| {
                // Verify that summing the descriptor sizes does not overflow.
                // This can happen if a driver tricks a device into reading more data than
                // fits in a `usize`.
                total_len = total_len
                    .checked_add(desc.len() as usize)
                    .ok_or(Error::DescriptorChainOverflow)?;

                let region = mem
                    .find_region(desc.addr())
                    .ok_or(Error::FindMemoryRegion)?;
                let offset = desc
                    .addr()
                    .checked_sub(region.start_addr().raw_value())
                    .unwrap();
                region
                    .get_slice(MemoryRegionAddress(offset.raw_value()), desc.len() as usize)
                    .map_err(Error::GuestMemoryError)
            })
            .collect::<Result<VecDeque<VolatileSlice<'a, B>>>>()?;
        Ok(Reader {
            buffer: DescriptorChainConsumer {
                buffers,
                bytes_consumed: 0,
            },
        })
    }

    /// Reads an object from the descriptor chain buffer.
    pub fn read_obj<T: ByteValued>(&mut self) -> Result<T> {
        let mut obj = MaybeUninit::<T>::uninit();

        // SAFETY: `MaybeUninit` guarantees that the pointer is valid for
        // `size_of::<T>()` bytes.
        let buf = unsafe {
            ::core::slice::from_raw_parts_mut(obj.as_mut_ptr() as *mut u8, size_of::<T>())
        };

        // self.read_exact(buf)?;
        todo!();

        // SAFETY: any type that implements `ByteValued` can be considered initialized
        // even if it is filled with random data.
        Ok(unsafe { obj.assume_init() })
    }

    /// Returns number of bytes available for reading.  May return an error if the combined
    /// lengths of all the buffers in the DescriptorChain would cause an integer overflow.
    pub fn available_bytes(&self) -> usize {
        self.buffer.available_bytes()
    }

    /// Returns number of bytes already read from the descriptor chain buffer.
    pub fn bytes_read(&self) -> usize {
        self.buffer.bytes_consumed()
    }

    /// Splits this `Reader` into two at the given offset in the `DescriptorChain` buffer.
    /// After the split, `self` will be able to read up to `offset` bytes while the returned
    /// `Reader` can read up to `available_bytes() - offset` bytes.  Returns an error if
    /// `offset > self.available_bytes()`.
    pub fn split_at(&mut self, offset: usize) -> Result<Reader<'a, B>> {
        self.buffer.split_at(offset).map(|buffer| Reader { buffer })
    }
}

impl<B: BitmapSlice> Reader<'_, B> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        self.buffer.consume(buf.len(), |bufs| {
            let mut rem = buf;
            let mut total = 0;
            for vs in bufs {
                let copy_len = cmp::min(rem.len(), vs.len());

                // SAFETY: Safe because we verify that we do not read outside
                // of the slice's bound. The slice guard will only get dropped
                // after the function returns. This will keep the pointer valid
                // while reads are happening.
                unsafe {
                    copy_nonoverlapping(vs.ptr_guard().as_ptr(), rem.as_mut_ptr(), copy_len);
                }
                rem = &mut rem[copy_len..];
                total += copy_len;
            }
            Ok(total)
        })
    }
}

/// Provides high-level interface over the sequence of memory regions
/// defined by writable descriptors in the descriptor chain.
///
/// Note that virtio spec requires driver to place any device-writable
/// descriptors after any device-readable descriptors (2.6.4.2 in Virtio Spec v1.1).
/// Writer will start iterating the descriptors from the first writable one and will
/// assume that all following descriptors are writable.
#[derive(Clone)]
pub struct Writer<'a, B = ()> {
    buffer: DescriptorChainConsumer<'a, B>,
}

impl<'a, B: BitmapSlice> Writer<'a, B> {
    /// Construct a new Writer wrapper over `desc_chain`.
    pub fn new<M, T>(mem: &'a M, desc_chain: DescriptorChain<T>) -> Result<Writer<'a, B>>
    where
        M: GuestMemory,
        <<M as GuestMemory>::R as GuestMemoryRegion>::B: WithBitmapSlice<'a, S = B>,
        T: Deref,
        T::Target: GuestMemory + Sized,
    {
        let mut total_len: usize = 0;
        let buffers = desc_chain
            .writable()
            .map(|desc| {
                // Verify that summing the descriptor sizes does not overflow.
                // This can happen if a driver tricks a device into writing more data than
                // fits in a `usize`.
                total_len = total_len
                    .checked_add(desc.len() as usize)
                    .ok_or(Error::DescriptorChainOverflow)?;

                let region = mem
                    .find_region(desc.addr())
                    .ok_or(Error::FindMemoryRegion)?;
                let offset = desc
                    .addr()
                    .checked_sub(region.start_addr().raw_value())
                    .unwrap();
                region
                    .get_slice(MemoryRegionAddress(offset.raw_value()), desc.len() as usize)
                    .map_err(Error::GuestMemoryError)
            })
            .collect::<Result<VecDeque<VolatileSlice<'a, B>>>>()?;

        Ok(Writer {
            buffer: DescriptorChainConsumer {
                buffers,
                bytes_consumed: 0,
            },
        })
    }

    /// Writes an object to the descriptor chain buffer.
    pub fn write_obj<T: ByteValued>(&mut self, val: T) -> Result<()> {
        // self.write_all(val.as_slice())
        todo!()
    }

    /// Returns number of bytes available for writing.  May return an error if the combined
    /// lengths of all the buffers in the DescriptorChain would cause an overflow.
    pub fn available_bytes(&self) -> usize {
        self.buffer.available_bytes()
    }

    /// Returns number of bytes already written to the descriptor chain buffer.
    pub fn bytes_written(&self) -> usize {
        self.buffer.bytes_consumed()
    }

    /// Splits this `Writer` into two at the given offset in the `DescriptorChain` buffer.
    /// After the split, `self` will be able to write up to `offset` bytes while the returned
    /// `Writer` can write up to `available_bytes() - offset` bytes.  Returns an error if
    /// `offset > self.available_bytes()`.
    pub fn split_at(&mut self, offset: usize) -> Result<Writer<'a, B>> {
        self.buffer.split_at(offset).map(|buffer| Writer { buffer })
    }
}

impl<B: BitmapSlice> Writer<'_, B> {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        self.buffer.consume(buf.len(), |bufs| {
            let mut rem = buf;
            let mut total = 0;
            for vs in bufs {
                let copy_len = cmp::min(rem.len(), vs.len());

                // SAFETY: Safe because we ensure that we do not write over the
                // slice's bounds. The slice guard will only get dropped after
                // the function returns. This will keep the pointer valid while
                // writes are happening.
                unsafe {
                    copy_nonoverlapping(rem.as_ptr(), vs.ptr_guard_mut().as_ptr(), copy_len);
                }
                vs.bitmap().mark_dirty(0, copy_len);
                rem = &rem[copy_len..];
                total += copy_len;
            }
            Ok(total)
        })
    }

    fn flush(&mut self) -> Result<()> {
        // Nothing to flush since the writes go straight into the buffer.
        Ok(())
    }
}
