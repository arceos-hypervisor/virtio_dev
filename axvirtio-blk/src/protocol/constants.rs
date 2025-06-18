// General VirtIO Feature Bits
pub const VIRTIO_F_RING_EVENT_IDX: u64 = 29;

// VirtIO Block Device Feature Bits
pub const VIRTIO_BLK_F_SIZE_MAX: u64 = 1;
pub const VIRTIO_BLK_F_SEG_MAX: u64 = 2;
pub const VIRTIO_BLK_F_GEOMETRY: u64 = 4;
pub const VIRTIO_BLK_F_RO: u64 = 5;
pub const VIRTIO_BLK_F_BLK_SIZE: u64 = 6;
pub const VIRTIO_BLK_F_FLUSH: u64 = 9;
pub const VIRTIO_BLK_F_TOPOLOGY: u64 = 10;
pub const VIRTIO_BLK_F_CONFIG_WCE: u64 = 11;
pub const VIRTIO_BLK_F_MQ: u64 = 12;
pub const VIRTIO_BLK_F_DISCARD: u64 = 13;
pub const VIRTIO_BLK_F_WRITE_ZEROES: u64 = 14;

// Request Types
pub const VIRTIO_BLK_T_IN: u32 = 0;
pub const VIRTIO_BLK_T_OUT: u32 = 1;
pub const VIRTIO_BLK_T_FLUSH: u32 = 4;
pub const VIRTIO_BLK_T_GET_ID: u32 = 8;
pub const VIRTIO_BLK_T_DISCARD: u32 = 11;
pub const VIRTIO_BLK_T_WRITE_ZEROES: u32 = 13;

// Status Values
pub const VIRTIO_BLK_S_OK: u8 = 0;
pub const VIRTIO_BLK_S_IOERR: u8 = 1;
pub const VIRTIO_BLK_S_UNSUPP: u8 = 2;

// Device constants
pub const VIRTIO_BLK_ID_BYTES: usize = 20;
pub const SECTOR_SIZE: u64 = 512;
pub const SECTOR_SHIFT: u8 = 9;
