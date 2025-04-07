// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

// We're only providing virtio over MMIO devices for now, but we aim to add PCI support as well.

use alloc::vec::Vec;
use core::convert::TryFrom;
use core::ops::DerefMut;
use core::sync::atomic::{AtomicU8, Ordering};
use spin::{Mutex, MutexGuard};
// use core::sync::{Arc, Mutex};

use alloc::sync::Arc;
use event_manager::{
    Error as EvmgrError, EventManager, MutEventSubscriber, RemoteEndpoint, Result as EvmgrResult,
    SubscriberId,
};
use kvm_ioctls::{IoEventAddress, VmFd};
use linux_loader::cmdline::Cmdline;
use virtio_device::VirtioConfig;
use vm_device::DeviceMmio;
use vm_device::bus::{self, MmioAddress, MmioRange};
use vm_device::device_manager::MmioManager;
use vm_memory::{GuestAddress, GuestAddressSpace};
use vmm_sys_util::errno;
use vmm_sys_util::eventfd::{EFD_NONBLOCK, EventFd};

// TODO: Move virtio-related defines from the local modules to the `vm-virtio` crate upstream.

// TODO: Add MMIO-specific module when we add support for something like PCI as well.

// Device-independent virtio features.
pub(crate) mod features {
    pub const VIRTIO_F_RING_EVENT_IDX: u64 = 29;
    pub const VIRTIO_F_VERSION_1: u64 = 32;
    pub const VIRTIO_F_IN_ORDER: u64 = 35;
}

// This bit is set on the device interrupt status when notifying the driver about used
// queue events.
// TODO: There seem to be similar semantics when the PCI transport is used with MSI-X cap
// disabled. Let's figure out at some point if having MMIO as part of the name is necessary.
const VIRTIO_MMIO_INT_VRING: u8 = 0x01;

// The driver will write to the register at this offset in the MMIO region to notify the device
// about available queue events.
const VIRTIO_MMIO_QUEUE_NOTIFY_OFFSET: u64 = 0x50;

// TODO: Make configurable for each device maybe?
const QUEUE_MAX_SIZE: u16 = 256;

// Common errors encountered during device creation, configuration, and operation.
#[derive(Debug)]
pub enum Error {
    AlreadyActivated,
    BadFeatures(u64),
    Bus(bus::Error),
    Cmdline(linux_loader::cmdline::Error),
    Endpoint(EvmgrError),
    // EventFd(Error),
    Overflow,
    QueuesNotValid,
    RegisterIoevent(errno::Error),
    RegisterIrqfd(errno::Error),
}

type Result<T> = core::result::Result<T, Error>;
pub type Subscriber = Arc<Mutex<dyn MutEventSubscriber + Send>>;

#[derive(Copy, Clone)]
pub struct MmioConfig {
    pub range: MmioRange,
    // The interrupt assigned to the device.
    pub gsi: u32,
}

impl MmioConfig {
    pub fn new(base: u64, size: u64, gsi: u32) -> Result<Self> {
        MmioRange::new(MmioAddress(base), size)
            .map(|range| MmioConfig { range, gsi })
            .map_err(Error::Bus)
    }

    pub fn next(&self) -> Result<Self> {
        let range = self.range;
        let next_start = range
            .base()
            .0
            .checked_add(range.size())
            .ok_or(Error::Overflow)?;
        Self::new(next_start, range.size(), self.gsi + 1)
    }
}

// Represents the environment the devices in this crate current expect in order to be created
// and registered with the appropriate buses/handlers/etc. We're always passing a mmio_cfg object
// for now, and we'll re-evaluate the mechanism for exposing environment (i.e. maybe we'll do it
// through an object that implements a number of traits the devices are aware of).
pub struct Env<'a, M, B> {
    // The objects used for guest memory accesses and other operations.
    pub mem: M,
    // Used by the devices to register ioevents and irqfds.
    pub vm_fd: Arc<VmFd>,
    // Mutable handle to the event manager the device is supposed to register with. There could be
    // more if we decide to use more than just one thread for device model emulation.
    pub event_mgr: &'a mut EventManager<Arc<Mutex<dyn MutEventSubscriber + Send>>>,
    // This stands for something that implements `MmioManager`, and can be passed as a reference
    // or smart pointer (such as a `Mutex` guard).
    pub mmio_mgr: B,
    // The virtio MMIO device parameters (MMIO range and interrupt to be used).
    pub mmio_cfg: MmioConfig,
    // We pass a mutable reference to the kernel cmdline `String` so the device can add any
    // required arguments (i.e. for virtio over MMIO discovery). This means we need to create
    // the devices before loading he kernel cmdline into memory, but that's not a significant
    // limitation.
    pub kernel_cmdline: &'a mut Cmdline,
}

impl<'a, M, B> Env<'a, M, B>
where
    // We're using this (more convoluted) bound so we can pass both references and smart
    // pointers such as mutex guards here.
    B: DerefMut,
    B::Target: MmioManager<D = Arc<dyn DeviceMmio + Send + Sync>>,
{
    // Registers an MMIO device with the inner bus and kernel cmdline.
    pub fn register_mmio_device(
        &mut self,
        device: Arc<dyn DeviceMmio + Send + Sync>,
    ) -> Result<()> {
        self.mmio_mgr
            .register_mmio(self.mmio_cfg.range, device)
            .map_err(Error::Bus)?;

        self.kernel_cmdline
            .add_virtio_mmio_device(
                self.mmio_cfg.range.size(),
                GuestAddress(self.mmio_cfg.range.base().0),
                self.mmio_cfg.gsi,
                None,
            )
            .map_err(Error::Cmdline)?;

        Ok(())
    }

    // Appends a string to the inner kernel cmdline.
    pub fn insert_cmdline_str<T: AsRef<str>>(&mut self, t: T) -> Result<()> {
        self.kernel_cmdline
            .insert_str(t.as_ref())
            .map_err(Error::Cmdline)
    }
}

// Holds configuration objects which are common to all current devices.
pub struct CommonConfig<M: GuestAddressSpace> {
    pub virtio: VirtioConfig<M>,
    pub mmio: MmioConfig,
    pub endpoint: RemoteEndpoint<Subscriber>,
    pub vm_fd: Arc<VmFd>,
    pub irqfd: Arc<EventFd>,
}

impl<M: GuestAddressSpace> CommonConfig<M> {
    pub fn new<B>(virtio_cfg: VirtioConfig<M>, env: &Env<M, B>) -> Result<Self> {
        let irqfd = Arc::new(EventFd::new(EFD_NONBLOCK).map_err(Error::EventFd)?);

        env.vm_fd
            .register_irqfd(&irqfd, env.mmio_cfg.gsi)
            .map_err(Error::RegisterIrqfd)?;

        Ok(CommonConfig {
            virtio: virtio_cfg,
            mmio: env.mmio_cfg,
            endpoint: env.event_mgr.remote_endpoint(),
            vm_fd: env.vm_fd.clone(),
            irqfd,
        })
    }

    // Perform common initial steps for device activation based on the configuration, and return
    // a `Vec` that contains `EventFd`s registered as ioeventfds, which are used to convey queue
    // notifications coming from the driver.
    pub fn prepare_activate(&self) -> Result<Vec<EventFd>> {
        if !self.virtio.queues_valid() {
            return Err(Error::QueuesNotValid);
        }

        if self.virtio.device_activated {
            return Err(Error::AlreadyActivated);
        }

        // We do not support legacy drivers.
        if self.virtio.driver_features & (1 << features::VIRTIO_F_VERSION_1) == 0 {
            return Err(Error::BadFeatures(self.virtio.driver_features));
        }

        let mut ioevents = Vec::new();

        // Right now, we operate under the assumption all queues are marked ready by the device
        // (which is true until we start supporting devices that can optionally make use of
        // additional queues on top of the defaults).
        for i in 0..self.virtio.queues.len() {
            let fd = EventFd::new(EFD_NONBLOCK).map_err(Error::QueuesNotValid)?;

            // Register the queue event fd.
            self.vm_fd
                .register_ioevent(
                    &fd,
                    &IoEventAddress::Mmio(
                        self.mmio.range.base().0 + VIRTIO_MMIO_QUEUE_NOTIFY_OFFSET,
                    ),
                    // The maximum number of queues should fit within an `u16` according to the
                    // standard, so the conversion below is always expected to succeed.
                    u32::try_from(i).unwrap(),
                )
                .map_err(Error::RegisterIoevent)?;

            ioevents.push(fd);
        }

        Ok(ioevents)
    }

    // Perform the final steps of device activation based on the inner configuration and the
    // provided subscriber that's going to handle the device queues. We'll extend this when
    // we start support devices that make use of multiple handlers (i.e. for multiple queues).
    pub fn finalize_activate(&mut self, handler: Subscriber) -> Result<()> {
        // Register the queue handler with the `EventManager`. We could record the `sub_id`
        // (and/or keep a handler clone) for further interaction (i.e. to remove the subscriber at
        // a later time, retrieve state, etc).
        let _sub_id = self
            .endpoint
            .call_blocking(move |mgr| -> EvmgrResult<SubscriberId> {
                Ok(mgr.add_subscriber(handler))
            })
            .map_err(Error::Endpoint)?;

        self.virtio.device_activated = true;

        Ok(())
    }
}

/// Simple trait to model the operation of signalling the driver about used events
/// for the specified queue.
// TODO: Does this need renaming to be relevant for packed queues as well?
pub trait SignalUsedQueue {
    // TODO: Should this return an error? This failing is not really recoverable at the interface
    // level so the expectation is the implementation handles that transparently somehow.
    fn signal_used_queue(&self, index: u16);
}

/// Uses a single irqfd as the basis of signalling any queue (useful for the MMIO transport,
/// where a single interrupt is shared for everything).
pub struct SingleFdSignalQueue {
    pub irqfd: Arc<EventFd>,
    pub interrupt_status: Arc<AtomicU8>,
}

impl SignalUsedQueue for SingleFdSignalQueue {
    fn signal_used_queue(&self, _index: u16) {
        self.interrupt_status
            .fetch_or(VIRTIO_MMIO_INT_VRING, Ordering::SeqCst);
        self.irqfd
            .write(1)
            .expect("Failed write to eventfd when signalling queue");
    }
}
