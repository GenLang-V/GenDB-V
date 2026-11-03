//! Artifacts: GenDB's library of immutable records. Trusted component (the TCB relies on its record formats,
//! identities and append-only publication).
//!
//! * [`canonical_json`]: the one canonical JSON encoding and SHA-256 content identity ([`ContentId`]);
//! * [`object_store`]: typed records and raw blobs in `objects/`, published atomically, read with digest checks;
//! * [`append_only`]: append-only record streams whose heads name current publications; [`record_index`] holds
//!   their derived index files;
//! * [`asset_directory`]: immutable stored asset directories inside the library (`assets/<name>/`), named by
//!   library-relative paths;
//! * [`column`]: declared source columns as recorded;
//! * [`verus`]: records of Verus-checked query packages (builds, representations and assets, statement keys,
//!   claims, admission and serving lookup).
//!
//! Formats are byte-compatible with the saved libraries of the earlier GenDB version; saved ABI v1/v2 and native records are
//! read only by that version (not part of this repository).
#![forbid(unsafe_code)]

pub mod append_only;
pub mod asset_directory;
pub mod canonical_json;
pub mod column;
pub mod content_id;
pub mod object_store;
pub mod record_index;
pub mod verus;

pub use asset_directory::{ASSETS_DIRECTORY, AssetNameLock};
pub use append_only::{APPEND_RECORD_KIND, AppendOnlyError, AppendRecord, append_record, lookup_record_head};
pub use canonical_json::{CanonError, canonical_envelope, content_id};
pub use column::{ColType, ColumnSpec};
pub use content_id::{ContentId, ContentIdParseError};
pub use object_store::{ObjectStore, StoreError, VerifiedObject, blob_id};
pub use record_index::{RecordIndex, rebuild_indexes};
