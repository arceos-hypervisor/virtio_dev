use crate::protocol::{VirtioBlkError, VirtioBlkResult};

/// Block Device Backend Trait
pub trait BlockBackend: Send + Sync {
    /// Get the total capacity in bytes
    fn capacity(&self) -> u64;

    /// Read data from the backend
    ///
    /// # Arguments
    /// * `sector` - Starting sector number
    /// * `buffer` - Buffer to read data into
    ///
    /// # Returns
    /// Number of bytes read or error
    fn read(&self, sector: u64, buffer: &mut [u8]) -> VirtioBlkResult<usize>;

    /// Write data to the backend
    ///
    /// # Arguments
    /// * `sector` - Starting sector number  
    /// * `buffer` - Buffer containing data to write
    ///
    /// # Returns
    /// Number of bytes written or error
    fn write(&self, sector: u64, buffer: &[u8]) -> VirtioBlkResult<usize>;

    /// Flush any pending writes
    fn flush(&self) -> VirtioBlkResult<()>;

    /// Check if the backend is read-only
    fn is_read_only(&self) -> bool;

    /// Get sector size in bytes (typically 512)
    fn sector_size(&self) -> u64 {
        512
    }

    /// Get number of sectors
    fn num_sectors(&self) -> u64 {
        self.capacity() / self.sector_size()
    }
}
