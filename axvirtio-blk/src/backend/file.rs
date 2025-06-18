use crate::backend::BlockBackend;
use crate::protocol::{SECTOR_SIZE, VirtioBlkError, VirtioBlkResult};
use alloc::string::String;
use alloc::sync::Arc;
use axfs::{self, fops::OpenOptions};
use spin::Mutex;

/// File-based block device backend
pub struct FileBackend {
    file: Arc<Mutex<axfs::fops::File>>,
    capacity: u64,
    read_only: bool,
    file_path: String,
}

impl FileBackend {
    /// Create a new file backend with specified capacity
    ///
    /// # Arguments
    /// * `path` - Path to the file to use as storage
    /// * `capacity` - Device capacity in bytes
    /// * `read_only` - Whether the backend is read-only
    ///
    /// # Returns
    /// New FileBackend instance or error
    pub fn new(path: &str, capacity: u64, read_only: bool) -> VirtioBlkResult<Self> {
        let mut opts = OpenOptions::new();
        opts.read(true);

        if !read_only {
            opts.write(true);
            opts.create(true);
        }

        let file = axfs::fops::File::open(path, &opts).map_err(Self::map_axfs_error)?;

        // If creating a new file, truncate to desired capacity
        if !read_only {
            file.truncate(capacity).map_err(Self::map_axfs_error)?;
        }

        Ok(Self {
            file: Arc::new(Mutex::new(file)),
            capacity,
            read_only,
            file_path: String::from(path),
        })
    }

    /// Open an existing file as backend
    ///
    /// # Arguments  
    /// * `path` - Path to existing file
    /// * `read_only` - Whether to open in read-only mode
    ///
    /// # Returns
    /// New FileBackend instance or error
    pub fn open_existing(path: &str, read_only: bool) -> VirtioBlkResult<Self> {
        let mut opts = OpenOptions::new();
        opts.read(true);

        if !read_only {
            opts.write(true);
        }

        let file = axfs::fops::File::open(path, &opts).map_err(Self::map_axfs_error)?;

        // Get file size as capacity
        let attr = file.get_attr().map_err(Self::map_axfs_error)?;
        let capacity = attr.size();

        Ok(Self {
            file: Arc::new(Mutex::new(file)),
            capacity,
            read_only,
            file_path: String::from(path),
        })
    }

    /// Map axfs errors to VirtIO block errors
    fn map_axfs_error(err: axerrno::AxError) -> VirtioBlkError {
        use axerrno::AxError;
        match err {
            AxError::NotFound => VirtioBlkError::BackendError,
            AxError::PermissionDenied => VirtioBlkError::BackendError,
            AxError::InvalidInput => VirtioBlkError::InvalidSector,
            AxError::UnexpectedEof => VirtioBlkError::InvalidSector,
            _ => VirtioBlkError::BackendError,
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

impl BlockBackend for FileBackend {
    fn capacity(&self) -> u64 {
        self.capacity
    }

    fn read(&self, sector: u64, buffer: &mut [u8]) -> VirtioBlkResult<usize> {
        self.validate_access(sector, buffer.len())?;

        let offset = sector * SECTOR_SIZE;
        let mut file = self.file.lock();

        let bytes_read = file.read_at(offset, buffer).map_err(Self::map_axfs_error)?;

        Ok(bytes_read)
    }

    fn write(&self, sector: u64, buffer: &[u8]) -> VirtioBlkResult<usize> {
        if self.read_only {
            return Err(VirtioBlkError::BackendError);
        }

        self.validate_access(sector, buffer.len())?;

        let offset = sector * SECTOR_SIZE;
        let mut file = self.file.lock();

        let bytes_written = file
            .write_at(offset, buffer)
            .map_err(Self::map_axfs_error)?;

        Ok(bytes_written)
    }

    fn flush(&self) -> VirtioBlkResult<()> {
        let file = self.file.lock();
        file.flush().map_err(Self::map_axfs_error)?;
        Ok(())
    }

    fn is_read_only(&self) -> bool {
        self.read_only
    }
}
