use crate::backend::BlockBackend;
use crate::protocol::{SECTOR_SIZE, VirtioBlkError, VirtioBlkResult};
use alloc::vec::Vec;
use spin::Mutex;

/// Memory-based block device backend
pub struct MemoryBackend {
    data: Mutex<Vec<u8>>,
    capacity: u64,
    read_only: bool,
}

impl MemoryBackend {
    /// Create a new memory backend with specified capacity
    pub fn new(capacity: u64, read_only: bool) -> Self {
        let data = vec![0u8; capacity as usize];
        Self {
            data: Mutex::new(data),
            capacity,
            read_only,
        }
    }

    /// Create a new memory backend with initial data
    pub fn with_data(data: Vec<u8>, read_only: bool) -> Self {
        let capacity = data.len() as u64;
        Self {
            data: Mutex::new(data),
            capacity,
            read_only,
        }
    }

    fn validate_access(&self, sector: u64, len: usize) -> VirtioBlkResult<()> {
        let start_byte = sector * SECTOR_SIZE;
        let end_byte = start_byte + len as u64;

        if end_byte > self.capacity {
            return Err(VirtioBlkError::InvalidSector);
        }

        Ok(())
    }
}

impl BlockBackend for MemoryBackend {
    fn capacity(&self) -> u64 {
        self.capacity
    }

    fn read(&self, sector: u64, buffer: &mut [u8]) -> VirtioBlkResult<usize> {
        self.validate_access(sector, buffer.len())?;

        let start_byte = (sector * SECTOR_SIZE) as usize;
        let end_byte = start_byte + buffer.len();

        let data = self.data.lock();
        if end_byte > data.len() {
            return Err(VirtioBlkError::InvalidSector);
        }

        buffer.copy_from_slice(&data[start_byte..end_byte]);
        Ok(buffer.len())
    }

    fn write(&self, sector: u64, buffer: &[u8]) -> VirtioBlkResult<usize> {
        if self.read_only {
            return Err(VirtioBlkError::BackendError);
        }

        self.validate_access(sector, buffer.len())?;

        let start_byte = (sector * SECTOR_SIZE) as usize;
        let end_byte = start_byte + buffer.len();

        let mut data = self.data.lock();
        if end_byte > data.len() {
            return Err(VirtioBlkError::InvalidSector);
        }

        data[start_byte..end_byte].copy_from_slice(buffer);
        Ok(buffer.len())
    }

    fn flush(&self) -> VirtioBlkResult<()> {
        // For memory backend, flush is a no-op
        Ok(())
    }

    fn is_read_only(&self) -> bool {
        self.read_only
    }
}
