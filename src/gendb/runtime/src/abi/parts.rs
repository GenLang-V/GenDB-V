//! Stored parts as query-call inputs: the part-file mappings of one stored parts directory and their ABI part
//! descriptors, owned together.

use super::error::AbiError;
use super::records::PartDescriptor;
use gendb_storage::io::{MappedPartFiles, PartAccess};
use std::path::Path;

/// The read-only mappings of a stored parts directory and one [`PartDescriptor`] per part. The descriptors point
/// into the mappings, so both live exactly as long as this owner; a caller that passes the descriptors to a library
/// must keep the owner alive until its process exits (the shim hands verified code `&'static` slices).
pub struct MappedParts {
    files: MappedPartFiles,
    descriptors: Vec<PartDescriptor>,
}

impl MappedParts {
    /// Map a directory written by `gendb_storage::io::PartFilesWriter`, with the kernel advice `access` (the saved v3
    /// route uses the default: no advice).
    pub fn open(directory: &Path, access: &PartAccess) -> Result<Self, AbiError> {
        let files = MappedPartFiles::open(directory, access)?;
        let descriptors = files
            .parts()
            .map(|part| PartDescriptor { elem: part.elem.code(), reserved: 0, len: part.len, data: part.data })
            .collect();
        Ok(Self { files, descriptors })
    }

    pub fn files(&self) -> &MappedPartFiles {
        &self.files
    }

    pub fn descriptors(&self) -> &[PartDescriptor] {
        &self.descriptors
    }
}
