use crate::protocol::VirtioBlkStatus;

/// VirtIO Block Device Errors
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum VirtioBlkError {
    /// Invalid descriptor chain
    InvalidDescriptorChain,
    /// Unsupported request type
    UnsupportedRequestType,
    /// Invalid sector address
    InvalidSector,
    /// Buffer too small
    BufferTooSmall,
    /// Address translation failed
    AddressTranslationFailed,
    /// Backend operation failed
    BackendError,
    /// Invalid request header
    InvalidRequestHeader,
    /// Queue not ready
    QueueNotReady,
}

impl VirtioBlkError {
    /// Convert error to VirtIO block status code
    pub fn to_status(self) -> VirtioBlkStatus {
        match self {
            VirtioBlkError::UnsupportedRequestType => VirtioBlkStatus::Unsupported,
            VirtioBlkError::InvalidSector
            | VirtioBlkError::BufferTooSmall
            | VirtioBlkError::AddressTranslationFailed
            | VirtioBlkError::BackendError
            | VirtioBlkError::InvalidRequestHeader
            | VirtioBlkError::QueueNotReady => VirtioBlkStatus::IoError,
            VirtioBlkError::InvalidDescriptorChain => VirtioBlkStatus::IoError,
        }
    }
}

pub type VirtioBlkResult<T> = Result<T, VirtioBlkError>;
