// Copyright 2018 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

use core::sync::atomic::Ordering;

use log::warn;

use crate::{status, VirtioDevice, WithDriverSelect};
use virtio_bindings::virtio_mmio::{
    VIRTIO_MMIO_CONFIG_GENERATION, VIRTIO_MMIO_DEVICE_FEATURES, VIRTIO_MMIO_DEVICE_FEATURES_SEL,
    VIRTIO_MMIO_DEVICE_ID, VIRTIO_MMIO_DRIVER_FEATURES, VIRTIO_MMIO_DRIVER_FEATURES_SEL,
    VIRTIO_MMIO_INTERRUPT_ACK, VIRTIO_MMIO_INTERRUPT_STATUS, VIRTIO_MMIO_MAGIC_VALUE,
    VIRTIO_MMIO_QUEUE_AVAIL_HIGH, VIRTIO_MMIO_QUEUE_AVAIL_LOW, VIRTIO_MMIO_QUEUE_DESC_HIGH,
    VIRTIO_MMIO_QUEUE_DESC_LOW, VIRTIO_MMIO_QUEUE_NOTIFY, VIRTIO_MMIO_QUEUE_NUM,
    VIRTIO_MMIO_QUEUE_NUM_MAX, VIRTIO_MMIO_QUEUE_READY, VIRTIO_MMIO_QUEUE_SEL,
    VIRTIO_MMIO_QUEUE_USED_HIGH, VIRTIO_MMIO_QUEUE_USED_LOW, VIRTIO_MMIO_STATUS,
    VIRTIO_MMIO_VENDOR_ID, VIRTIO_MMIO_VERSION,
};
use virtio_queue::QueueT;

pub const VIRTIO_MMIO_CONFIG: u64 = virtio_bindings::virtio_mmio::VIRTIO_MMIO_CONFIG as u64;

// Required by the Virtio MMIO device register layout at offset 0 from base. Turns out this
// is actually the ASCII sequence for "virt" (in little endian ordering).
const MMIO_MAGIC_VALUE: u32 = 0x7472_6976;

// Current version specified by the Virtio standard (legacy devices used 1 here).
const MMIO_VERSION: u32 = 2;

// TODO: Crosvm was using 0 here a while ago, and Firecracker started doing that as well. Should
// we leave it like that, or should we use the VENDOR_ID value for PCI Virtio devices? It looks
// like the standard doesn't say anything regarding an actual VENDOR_ID value for MMIO devices.
const VENDOR_ID: u32 = 0;

// Helper function that runs the provided closure to mutate the currently selected queue of
// a `VirtioDevice`, provided the status check is successful.
// TODO: This function and its uses will likely have to be updated when we start offering
// packed virtqueue support as well.
fn update_queue_field<D, F, Q>(device: &mut D, f: F)
where
    D: WithDriverSelect + ?Sized + VirtioDevice<Q = Q>,
    Q: QueueT,
    F: FnOnce(&mut Q),
{
    if device.check_device_status(status::FEATURES_OK, status::DRIVER_OK | status::FAILED) {
        if let Some(queue) = device.selected_queue_mut() {
            f(queue);
        } else {
            warn!("update invalid virtio queue");
        }
    } else {
        warn!(
            "update virtio queue in invalid state 0x{:x}",
            device.device_status()
        );
    }
}

/// A common interface for Virtio devices that use the MMIO transport, which also provides a
/// default implementation of read and write operations from/to the device registers and
/// configuration space.
// Adding the `M` generic parameter that's also required by `VirtioDevice` for the time being.
pub trait VirtioMmioDevice: WithDriverSelect {
    /// Callback invoked when the driver writes a value to the Queue Notify configuration register.
    ///
    /// This is the simplest mechanism the driver can use to notify a virtio MMIO device. The
    /// meaning of the value is interpreted as specified by the standard. Many VMMs use something
    /// like the KVM `ioeventfd` mechanism, which eliminates the need to implement this method.
    // TODO: Move this to the `VirtioDevice` interface if it uniformly applies to all transports.
    fn queue_notify(&mut self, _val: u32) {
        // Do nothing by default.
    }

    /// Handle a driver read operation from the MMIO space of the device.
    fn read(&self, offset: u64, data: &mut [u8]) {
        match offset {
            // The standard specifies that accesses to configuration registers are 32-bit wide.
            0x00..=0xff if data.len() == 4 => {
                // This is safe since offset ranges from 0x00..=0xff, i.e. < u32::max.
                let v = match offset as u32 {
                    VIRTIO_MMIO_MAGIC_VALUE => MMIO_MAGIC_VALUE,
                    VIRTIO_MMIO_VERSION => MMIO_VERSION,
                    VIRTIO_MMIO_DEVICE_ID => self.device_type(),
                    VIRTIO_MMIO_VENDOR_ID => VENDOR_ID,
                    VIRTIO_MMIO_DEVICE_FEATURES => match self.device_features_select() {
                        0 => self.device_features() as u32,
                        1 => (self.device_features() >> 32) as u32,
                        // No device features defined beyond the first two pages.
                        _ => 0,
                    },
                    VIRTIO_MMIO_QUEUE_NUM_MAX => self
                        .selected_queue()
                        .map(QueueT::max_size)
                        .unwrap_or(0)
                        .into(),
                    VIRTIO_MMIO_QUEUE_READY => self
                        .selected_queue()
                        .map(|q| q.ready())
                        .unwrap_or(false)
                        .into(),
                    VIRTIO_MMIO_INTERRUPT_STATUS => {
                        self.interrupt_status().load(Ordering::SeqCst).into()
                    }
                    VIRTIO_MMIO_STATUS => self.device_status().into(),
                    VIRTIO_MMIO_CONFIG_GENERATION => self.config_generation().into(),
                    _ => {
                        warn!("unknown virtio mmio register read: 0x{:x}", offset);
                        return;
                    }
                };
                // This cannot panic, because we checked that `data.len() == 4`.
                data.copy_from_slice(v.to_le_bytes().as_ref());
            }

            // TODO: The standard specifies that configuration space size is device specific, so
            // we might want to express that via the trait instead of hard coding the current
            // arbitrary ceiling.
            // It's ok to use `as` here because `offset` always fits into an `usize` in this case.
            VIRTIO_MMIO_CONFIG..=0xfff => self.read_config(offset as usize - 0x100, data),
            _ => {
                warn!(
                    "invalid virtio mmio read: 0x{:x}:0x{:x}",
                    offset,
                    data.len()
                );
            }
        };
    }

    /// Handle a driver write operation to the MMIO space of the device.
    fn write(&mut self, offset: u64, data: &[u8]) {
        match offset {
            // The standard specifies that accesses to configuration registers are 32-bit wide.
            0x00..=0xff if data.len() == 4 => {
                // The `try_into` below attempts to convert `data` to a `[u8; 4]`, which
                // always succeeds because we previously checked that `data.len() == 4`.
                let v = u32::from_le_bytes(data.try_into().unwrap());

                // This is safe since offset ranges from 0x00..=0xff, i.e. < u32::max.
                match offset as u32 {
                    VIRTIO_MMIO_DEVICE_FEATURES_SEL => self.set_device_features_select(v),
                    VIRTIO_MMIO_DRIVER_FEATURES => {
                        if self.check_device_status(
                            status::DRIVER,
                            status::FEATURES_OK | status::FAILED,
                        ) {
                            self.set_driver_features(self.driver_features_select(), v);
                        } else {
                            warn!(
                                "ack virtio features in invalid state 0x{:x}",
                                self.device_status()
                            );
                        }
                    }
                    VIRTIO_MMIO_DRIVER_FEATURES_SEL => self.set_driver_features_select(v),

                    // TODO: add warnings or signal some sort of event (depending on how we end up
                    // implementing logging and metrics) for values that do not actually fit the
                    // data type specified by the virtio standard (we simply use `as` conversion
                    // for now).
                    VIRTIO_MMIO_QUEUE_SEL => self.set_queue_select(v as u16),
                    VIRTIO_MMIO_QUEUE_NUM => update_queue_field(self, |q| q.set_size(v as u16)),
                    VIRTIO_MMIO_QUEUE_READY => update_queue_field(self, |q| q.set_ready(v == 1)),
                    VIRTIO_MMIO_QUEUE_NOTIFY => self.queue_notify(v),
                    VIRTIO_MMIO_INTERRUPT_ACK => {
                        if self.check_device_status(status::DRIVER_OK, 0) {
                            self.interrupt_status()
                                .fetch_and(!(v as u8), Ordering::SeqCst);
                        }
                    }
                    VIRTIO_MMIO_STATUS => self.ack_device_status(v as u8),
                    VIRTIO_MMIO_QUEUE_DESC_LOW => {
                        update_queue_field(self, |q| q.set_desc_table_address(Some(v), None))
                    }
                    VIRTIO_MMIO_QUEUE_DESC_HIGH => {
                        update_queue_field(self, |q| q.set_desc_table_address(None, Some(v)))
                    }
                    VIRTIO_MMIO_QUEUE_AVAIL_LOW => {
                        update_queue_field(self, |q| q.set_avail_ring_address(Some(v), None))
                    }
                    VIRTIO_MMIO_QUEUE_AVAIL_HIGH => {
                        update_queue_field(self, |q| q.set_avail_ring_address(None, Some(v)))
                    }
                    VIRTIO_MMIO_QUEUE_USED_LOW => {
                        update_queue_field(self, |q| q.set_used_ring_address(Some(v), None))
                    }
                    VIRTIO_MMIO_QUEUE_USED_HIGH => {
                        update_queue_field(self, |q| q.set_used_ring_address(None, Some(v)))
                    }
                    _ => {
                        warn!("unknown virtio mmio register write: 0x{:x}", offset);
                    }
                }
            }
            // TODO: The standard specifies that configuration space size is device specific, so
            // we might want to express that via the trait instead of hard coding the current
            // arbitrary ceiling (same as for `read`).
            VIRTIO_MMIO_CONFIG..=0xfff => {
                if self.check_device_status(status::DRIVER, status::FAILED) {
                    // It's ok to use `as` here because `offset` always fits into an `usize`.
                    self.write_config(offset as usize - 0x100, data)
                } else {
                    warn!("can not write to device config data area before driver is ready");
                }
            }
            _ => {
                warn!(
                    "invalid virtio mmio write: 0x{:x}:0x{:x}",
                    offset,
                    data.len()
                );
            }
        }
    }
}
