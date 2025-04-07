// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

// use core::fs::File;
// use core::io::{self, Seek, SeekFrom};
// use core::path::{Path, PathBuf};

use virtio_blk::stdio_executor;

use crate::device;
use crate::virtio::features::{VIRTIO_F_IN_ORDER, VIRTIO_F_RING_EVENT_IDX, VIRTIO_F_VERSION_1};

pub use device::Block;

// TODO: Move relevant defines to vm-virtio crate.

// Block device ID as defined by the standard.
pub const BLOCK_DEVICE_ID: u32 = 2;

// Block device read-only feature.
pub const VIRTIO_BLK_F_RO: u64 = 5;
// Block device FLUSH feature.
pub const VIRTIO_BLK_F_FLUSH: u64 = 9;

// The sector size is 512 bytes (1 << 9).
const SECTOR_SHIFT: u8 = 9;

#[derive(Debug)]
pub enum Error {
    Backend(stdio_executor::Error),
    Virtio(crate::virtio::Error),
    // OpenFile(Error),
    // Seek(Error),
}

pub type Result<T> = core::result::Result<T, Error>;

// TODO: Add a helper abstraction to rust-vmm for building the device configuration space.
// The one we build below for the block device contains the minimally required `capacity` member,
// but other fields can be present as well depending on the negotiated features.
fn build_config_space<P: AsRef<Path>>(path: P) -> Result<Vec<u8>> {
    // TODO: right now, the file size is computed by the StdioBackend as well. Maybe we should
    // create the backend as early as possible, and get the size information from there.
    let file_size = File::open(path)
        .map_err(Error::OpenFile)?
        .seek(SeekFrom::End(0))
        .map_err(Error::Seek)?;
    // If the file size is actually not a multiple of sector size, then data at the very end
    // will be ignored.
    let num_sectors = file_size >> SECTOR_SHIFT;
    // This has to be in little endian btw.
    Ok(num_sectors.to_le_bytes().to_vec())
}

// Arguments required when building a block device.
pub struct BlockArgs {
    pub file_path: PathBuf,
    pub read_only: bool,
    pub root_device: bool,
    pub advertise_flush: bool,
}

impl BlockArgs {
    // Generate device features based on the configuration options.
    pub fn device_features(&self) -> u64 {
        // The queue handling logic for the device uses the buffers in order, so we enable the
        // corresponding feature as well.
        let mut features =
            1 << VIRTIO_F_VERSION_1 | 1 << VIRTIO_F_IN_ORDER | 1 << VIRTIO_F_RING_EVENT_IDX;

        if self.read_only {
            features |= 1 << VIRTIO_BLK_F_RO;
        }

        if self.advertise_flush {
            features |= 1 << VIRTIO_BLK_F_FLUSH;
        }

        features
    }

    // Generate additional info that needs to be appended to the kernel command line based
    // on the current arg configuration.
    pub fn cmdline_config_substring(&self) -> String {
        let mut s = String::new();
        if self.root_device {
            s.push_str("root=/dev/vda");

            if self.read_only {
                s.push_str(" ro");
            } else {
                s.push_str(" rw");
            }
        }
        s
    }
}
