//! Basic storage I/O of source columns: normalization of projected Arrow tables into canonical native columns,
//! metadata-only projection, read-only memory, and persisted archives whose column files later executions map
//! instead of decoding. [`PartFilesWriter`] and [`MappedPartFiles`] store and map the typed parts that representation
//! builders produce.
//!
//! Trusted: this module's normalization and file/mapping code, the Arrow IPC codec, the filesystem and the OS
//! mapping calls. No value is hashed or rescanned to identify columns; archives carry assigned lifecycle versions and
//! are checked by lifecycle, declared schema/types and file extents.
//!
//! Only canonical encodings are carried: each declared column is delivered in its canonical native form (see
//! [`NativeColumn`]). The earlier version's non-canonical encodings (decimal coefficient views, registered native storage) and its
//! region-built prepared assets belong to the native path and stay in that version.

mod archive;
mod column;
mod column_files;
mod error;
mod ipc;
mod parts;
mod read_only;
mod source_columns;
#[cfg(test)]
mod tests;

pub use archive::fresh_lifecycle_version;
pub use column::{
    ColumnBinding, NATIVE_TYPE_BOOL, NATIVE_TYPE_CARDINALITY, NATIVE_TYPE_I32, NATIVE_TYPE_I64, NATIVE_TYPE_I128,
    NATIVE_TYPE_U32, NATIVE_TYPE_U64, NATIVE_TYPE_UTF8, NativeColumn,
};
pub use column_files::{ArchiveExtension, CapturedBuffer, CapturedColumn};
pub use error::{Result, STORAGE_RESERVE_REFUSAL, StorageIoError};
pub use ipc::{ArchiveTableLayout, IpcSegment, read_ipc_segments};
pub(crate) use ipc::decode_mapped_ipc;
pub use parts::{
    ByteOrder, MappedPart, MappedPartFiles, PartAccess, PartElem, PartFilesWriter, PartPlacement, PartsFormat, PartsManifest, RESERVE_CHECK_BYTES,
    ReadAdvice, STORAGE_MARGIN_BYTES, free_bytes_at,
};
pub use read_only::ReadOnlyBuffer;
pub use source_columns::{ProjectedTable, SourceColumns};
