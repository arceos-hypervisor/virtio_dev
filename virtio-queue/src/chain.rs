// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Copyright © 2019 Intel Corporation
//
// Copyright (C) 2020-2021 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

use core::fmt::{self, Debug};
use core::mem::size_of;
use core::ops::Deref;

use crate::guest_memory::bitmap::{BitmapSlice, WithBitmapSlice};
// use vm_memory::bitmap::{BitmapSlice, WithBitmapSlice};
// use vm_memory::{Address, Bytes, GuestPhysAddr, GuestMemory, GuestMemoryRegion};
use crate::GuestMemory;
use crate::guest_memory::bytes::Bytes;
use crate::{desc::split::Descriptor, Error, Reader, Writer};
use axaddrspace::GuestPhysAddr;
use memory_addr::MemoryAddr;
use virtio_bindings::bindings::virtio_ring::VRING_DESC_ALIGN_SIZE;
use crate::guest_memory::GuestMemoryRegion;
/// A virtio descriptor chain.
#[derive(Clone, Debug)]
pub struct DescriptorChain<M> {
    mem: M,
    desc_table: GuestPhysAddr,
    queue_size: u16,
    head_index: u16,
    next_index: u16,
    ttl: u16,
    yielded_bytes: u32,
    is_indirect: bool,
}

impl<M> DescriptorChain<M>
where
    M: Deref,
    M::Target: GuestMemory,
{
    fn with_ttl(
        mem: M,
        desc_table: GuestPhysAddr,
        queue_size: u16,
        ttl: u16,
        head_index: u16,
    ) -> Self {
        DescriptorChain {
            mem,
            desc_table,
            queue_size,
            head_index,
            next_index: head_index,
            ttl,
            is_indirect: false,
            yielded_bytes: 0,
        }
    }

    /// Create a new `DescriptorChain` instance.
    ///
    /// # Arguments
    /// * `mem` - the `GuestMemory` object that can be used to access the buffers pointed to by the
    ///           descriptor chain.
    /// * `desc_table` - the address of the descriptor table.
    /// * `queue_size` - the size of the queue, which is also the maximum size of a descriptor
    ///                  chain.
    /// * `head_index` - the descriptor index of the chain head.
    pub(crate) fn new(mem: M, desc_table: GuestPhysAddr, queue_size: u16, head_index: u16) -> Self {
        Self::with_ttl(mem, desc_table, queue_size, queue_size, head_index)
    }

    /// Get the descriptor index of the chain head.
    pub fn head_index(&self) -> u16 {
        self.head_index
    }

    /// Return a `GuestMemory` object that can be used to access the buffers pointed to by the
    /// descriptor chain.
    pub fn memory(&self) -> &M::Target {
        self.mem.deref()
    }

    /// Return an iterator that only yields the readable descriptors in the chain.
    pub fn readable(self) -> DescriptorChainRwIter<M> {
        DescriptorChainRwIter {
            chain: self,
            writable: false,
        }
    }

    /// Return a new instance of Writer
    pub fn writer<'a, B: BitmapSlice>(self, mem: &'a M::Target) -> Result<Writer<'a, B>, Error>
    where
        M::Target: Sized,
        <<M::Target as GuestMemory>::R as GuestMemoryRegion>::B: WithBitmapSlice<'a, S = B>,
    {
        Writer::new(mem, self).map_err(|_| Error::InvalidChain)
    }

    /// Return a new instance of Reader
    pub fn reader<'a, B: BitmapSlice>(self, mem: &'a M::Target) -> Result<Reader<'a, B>, Error>
    where
        M::Target: Sized,
        <<M::Target as GuestMemory>::R as GuestMemoryRegion>::B: WithBitmapSlice<'a, S = B>,
    {
        Reader::new(mem, self).map_err(|_| Error::InvalidChain)
    }

    /// Return an iterator that only yields the writable descriptors in the chain.
    pub fn writable(self) -> DescriptorChainRwIter<M> {
        DescriptorChainRwIter {
            chain: self,
            writable: true,
        }
    }

    // Alters the internal state of the `DescriptorChain` to switch iterating over an
    // indirect descriptor table defined by `desc`.
    fn switch_to_indirect_table(&mut self, desc: Descriptor) -> Result<(), Error> {
        // Check the VIRTQ_DESC_F_INDIRECT flag (i.e., is_indirect) is not set inside
        // an indirect descriptor.
        // (see VIRTIO Spec, Section 2.6.5.3.1 Driver Requirements: Indirect Descriptors)
        if self.is_indirect {
            return Err(Error::InvalidIndirectDescriptor);
        }

        // Alignment requirements for vring elements start from virtio 1.0,
        // but this is not necessary for address of indirect descriptor.
        if desc.len() & (VRING_DESC_ALIGN_SIZE - 1) != 0 {
            return Err(Error::InvalidIndirectDescriptorTable);
        }

        // It is safe to do a plain division since we checked above that desc.len() is a multiple of
        // VRING_DESC_ALIGN_SIZE, and VRING_DESC_ALIGN_SIZE is != 0.
        let table_len = desc.len() / VRING_DESC_ALIGN_SIZE;
        if table_len > u32::from(u16::MAX) {
            return Err(Error::InvalidIndirectDescriptorTable);
        }

        self.desc_table = desc.addr();
        // try_from cannot fail as we've checked table_len above
        self.queue_size = u16::try_from(table_len).expect("invalid table_len");
        self.next_index = 0;
        self.ttl = self.queue_size;
        self.is_indirect = true;

        Ok(())
    }
}

impl<M> Iterator for DescriptorChain<M>
where
    M: Deref,
    M::Target: GuestMemory,
{
    type Item = Descriptor;

    /// Return the next descriptor in this descriptor chain, if there is one.
    ///
    /// Note that this is distinct from the next descriptor chain returned by
    /// [`AvailIter`](struct.AvailIter.html), which is the head of the next
    /// _available_ descriptor chain.
    fn next(&mut self) -> Option<Self::Item> {
        
        if self.ttl == 0 || self.next_index >= self.queue_size {
            return None;
        }

        let desc_addr = self
            .desc_table
            // The multiplication can not overflow an u64 since we are multiplying an u16 with a
            // small number.
            .checked_add(self.next_index as usize * size_of::<Descriptor>() as usize)?;
        
        // The guest device driver should not touch the descriptor once submitted, so it's safe
        // to use read_obj() here.
        todo!();
        // let desc = self.mem.read_obj::<Descriptor>(desc_addr).ok()?;

        // if desc.refers_to_indirect_table() {
        //     self.switch_to_indirect_table(desc).ok()?;
        //     return self.next();
        // }

        // // constructing a chain that is longer than 2^32 bytes is illegal,
        // // let's terminate the iteration if something violated this.
        // // (VIRTIO v1.2, 2.7.5.2: "Drivers MUST NOT add a descriptor chain
        // // longer than 2^32 bytes in total;")
        // match self.yielded_bytes.checked_add(desc.len()) {
        //     Some(yielded_bytes) => self.yielded_bytes = yielded_bytes,
        //     None => return None,
        // };

        // if desc.has_next() {
        //     self.next_index = desc.next();
        //     // It's ok to decrement `self.ttl` here because we check at the start of the method
        //     // that it's greater than 0.
        //     self.ttl -= 1;
        // } else {
        //     self.ttl = 0;
        // }

        // Some(desc)
    }
}

/// An iterator for readable or writable descriptors.
#[derive(Clone)]
pub struct DescriptorChainRwIter<M> {
    chain: DescriptorChain<M>,
    writable: bool,
}

impl<M> Iterator for DescriptorChainRwIter<M>
where
    M: Deref,
    M::Target: GuestMemory,
{
    type Item = Descriptor;

    /// Return the next readable/writeable descriptor (depending on the `writable` value) in this
    /// descriptor chain, if there is one.
    ///
    /// Note that this is distinct from the next descriptor chain returned by
    /// [`AvailIter`](struct.AvailIter.html), which is the head of the next
    /// _available_ descriptor chain.
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.chain.next() {
                Some(v) => {
                    if v.is_write_only() == self.writable {
                        return Some(v);
                    }
                }
                None => return None,
            }
        }
    }
}

// We can't derive Debug, because rustc doesn't generate the `M::T: Debug` constraint
impl<M> Debug for DescriptorChainRwIter<M>
where
    M: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DescriptorChainRwIter")
            .field("chain", &self.chain)
            .field("writable", &self.writable)
            .finish()
    }
}
