//! The C records of ABI v3 and v4, exactly as the framework shims declare them (`runtime/verus/gendb_shim.rs` for v3,
//! `runtime/verus/shim_v4/records.rs` for v4; same names and field order), and the layout records that a library must
//! report before any call.
//!
//! ABI v4 has two crate kinds. A storage crate exports [`STORAGE_BUILD_SYMBOL`] with the v3 build signature (columns
//! in, parts to the part sink). A query crate exports [`STORAGE_QUERY_SYMBOL`]: its inputs are the storage uses of
//! the query ([`StorageUseDescriptor`], one part list per use in the query's declared use order) and the statement
//! arguments; its record extends the v3 call record with each use's request counters. Both export
//! [`LAYOUT_V4_SYMBOL`] ([`expected_layout_v4`]).

use gendb_storage::io::NativeColumn;
use std::ffi::c_void;

pub const ABI_VERSION: u64 = 3;
pub const LAYOUT_SYMBOL: &str = "gendb_verus_abi_layout_v3";
pub const QUERY_SYMBOL: &str = "gendb_verus_query_v3";
pub const BUILD_SYMBOL: &str = "gendb_verus_build_v3";

pub const ABI_V4_VERSION: u64 = 4;
pub const LAYOUT_V4_SYMBOL: &str = "gendb_verus_abi_layout_v4";
pub const STORAGE_BUILD_SYMBOL: &str = "gendb_verus_storage_build_v4";
pub const STORAGE_QUERY_SYMBOL: &str = "gendb_verus_query_v4";
/// The build entry of a storage crate built from admitted storages: the parts of its sources in (as the query entry's
/// storage uses, no argument), its parts out to the part sink.
pub const STORAGE_DERIVED_BUILD_SYMBOL: &str = "gendb_verus_storage_build_derived_v4";

/// Largest worker count of one call. The shim refuses other counts (`AbiRefused`), the verified entry checks the
/// same bound (`gendb_entry::parallel::MAX_WORKERS`), and the layout record carries it.
pub const MAX_WORKERS: usize = 64;

/// One stored part: `len` elements of the element type with ABI code `elem` (`gendb_storage::io::PartElem::code`).
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct PartDescriptor {
    pub elem: u32,
    pub reserved: u32,
    pub len: u64,
    pub data: *const u8,
}

/// One statement argument: `kind` 1 = integer (`int`), 2 = numeric coefficient (`num_lo | num_hi << 64`, two's
/// complement i128), 3 = date (`y`, `m`, `d`), 4 = text (v4 query crates only: `num_hi` bytes at address `num_lo`, which
/// the caller keeps unchanged until the process exits). Unused fields are zero.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ArgumentDescriptor {
    pub kind: u32,
    pub reserved: u32,
    pub int: i64,
    pub num_lo: u64,
    pub num_hi: u64,
    pub y: i32,
    pub m: i32,
    pub d: i32,
    pub reserved2: i32,
}

pub(super) const ARGUMENT_INT: u32 = 1;
pub(super) const ARGUMENT_NUM: u32 = 2;
pub(super) const ARGUMENT_DATE: u32 = 3;
pub(super) const ARGUMENT_TEXT: u32 = 4;

/// Inputs of one call: columns (build), parts and arguments (query), and the worker count.
#[repr(C)]
pub(super) struct CallInputs {
    pub columns: *const NativeColumn,
    pub column_count: u64,
    pub parts: *const PartDescriptor,
    pub part_count: u64,
    pub arguments: *const ArgumentDescriptor,
    pub argument_count: u64,
    pub workers: u64,
}

impl CallInputs {
    /// Borrows the three arrays: the record is valid only while they are.
    pub fn new(
        columns: &[NativeColumn],
        parts: &[PartDescriptor],
        arguments: &[ArgumentDescriptor],
        workers: usize,
    ) -> Self {
        Self {
            columns: columns.as_ptr(),
            column_count: columns.len() as u64,
            parts: parts.as_ptr(),
            part_count: parts.len() as u64,
            arguments: arguments.as_ptr(),
            argument_count: arguments.len() as u64,
            workers: workers as u64,
        }
    }
}

/// `put(ctx, part index, element code, element count, data)`; non-zero refuses the part.
pub(super) type PutPartFn = unsafe extern "C" fn(*mut c_void, u64, u32, u64, *const u8) -> i32;

/// Host sink of the builder's parts, called once per part in part order.
#[repr(C)]
pub(super) struct PartSink {
    pub ctx: *mut c_void,
    pub put: Option<PutPartFn>,
}

/// `put(ctx, data, byte count)`; non-zero refuses the wire.
pub(super) type PutResultWireFn = unsafe extern "C" fn(*mut c_void, *const u8, u64) -> i32;

/// Host sink of the result wire, called at most once per query call with the complete bytes.
#[repr(C)]
pub(super) struct ResultWireSink {
    pub ctx: *mut c_void,
    pub put: Option<PutResultWireFn>,
}

/// Call record, written by the shim. `sql_error`: the exact SQL error code (1..=8) when `status` is 6, else 0.
/// `ranges` points at `2 * range_capacity` host words; the shim writes at most `range_capacity` `(lo, hi)` pairs and
/// reports the full count in `range_count`.
#[repr(C)]
#[derive(Debug)]
pub(super) struct CallRecord {
    pub status: u32,
    pub sql_error: u32,
    pub parts_delivered: u64,
    pub result_bytes: u64,
    pub spawned: u64,
    pub joined: u64,
    pub range_count: u64,
    pub range_capacity: u64,
    pub ranges: *mut u64,
}

/// One storage use of a v4 query call: `part_count` part descriptors at `parts`, in stored part order.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct StorageUseDescriptor {
    pub part_count: u64,
    pub parts: *const PartDescriptor,
}

/// Inputs of one v4 query call: the storage uses in the query's declared use order, the arguments and the worker count.
#[repr(C)]
pub(super) struct StorageQueryInputs {
    pub uses: *const StorageUseDescriptor,
    pub use_count: u64,
    pub arguments: *const ArgumentDescriptor,
    pub argument_count: u64,
    pub workers: u64,
}

impl StorageQueryInputs {
    /// Borrows both arrays: the record is valid only while they are.
    pub fn new(uses: &[StorageUseDescriptor], arguments: &[ArgumentDescriptor], workers: usize) -> Self {
        Self {
            uses: uses.as_ptr(),
            use_count: uses.len() as u64,
            arguments: arguments.as_ptr(),
            argument_count: arguments.len() as u64,
            workers: workers as u64,
        }
    }
}

/// Counter words per storage use in [`StorageQueryRecord::request_counts`]: requests, elements, bytes.
pub const REQUEST_COUNT_WORDS: usize = 3;

/// Call record of a v4 query call: the v3 call record, then the storage-use counters. `request_counts` points at
/// `REQUEST_COUNT_WORDS * use_count` host words; the shim writes the counters of the handle of use `i` at words
/// `3i..3i+3` and sets `counts_reported` to the number of handles it reported.
#[repr(C)]
#[derive(Debug)]
pub(super) struct StorageQueryRecord {
    pub call: CallRecord,
    pub use_count: u64,
    pub counts_reported: u64,
    pub request_counts: *mut u64,
}

pub(super) type QueryEntryFn = unsafe extern "C" fn(*const CallInputs, *const ResultWireSink, *mut CallRecord) -> i32;
pub(super) type BuildEntryFn = unsafe extern "C" fn(*const CallInputs, *const PartSink, *mut CallRecord) -> i32;
pub(super) type DerivedBuildEntryFn = unsafe extern "C" fn(*const StorageQueryInputs, *const PartSink, *mut CallRecord) -> i32;
pub(super) type StorageQueryEntryFn =
    unsafe extern "C" fn(*const StorageQueryInputs, *const ResultWireSink, *mut StorageQueryRecord) -> i32;
/// `layout(out, n)` writes up to `n` layout entries and returns how many exist.
pub(super) type LayoutFn = unsafe extern "C" fn(*mut u64, u64) -> u64;

/// The layout record a library must report through [`LAYOUT_SYMBOL`]: ABI version, the sizes of the seven records
/// (column, part, argument, inputs, part sink, result wire sink, call record), the alignment of i128 and
/// [`MAX_WORKERS`].
pub fn expected_layout() -> [u64; 10] {
    [
        ABI_VERSION,
        std::mem::size_of::<NativeColumn>() as u64,
        std::mem::size_of::<PartDescriptor>() as u64,
        std::mem::size_of::<ArgumentDescriptor>() as u64,
        std::mem::size_of::<CallInputs>() as u64,
        std::mem::size_of::<PartSink>() as u64,
        std::mem::size_of::<ResultWireSink>() as u64,
        std::mem::size_of::<CallRecord>() as u64,
        std::mem::align_of::<i128>() as u64,
        MAX_WORKERS as u64,
    ]
}

/// The v4 layout record: ABI version 4, the sizes of the ten records (column, part, argument, v3 inputs, storage use,
/// v4 query inputs, part sink, result wire sink, call record, v4 query record), the alignment of i128 and
/// [`MAX_WORKERS`].
pub fn expected_layout_v4() -> [u64; 13] {
    [
        ABI_V4_VERSION,
        std::mem::size_of::<NativeColumn>() as u64,
        std::mem::size_of::<PartDescriptor>() as u64,
        std::mem::size_of::<ArgumentDescriptor>() as u64,
        std::mem::size_of::<CallInputs>() as u64,
        std::mem::size_of::<StorageUseDescriptor>() as u64,
        std::mem::size_of::<StorageQueryInputs>() as u64,
        std::mem::size_of::<PartSink>() as u64,
        std::mem::size_of::<ResultWireSink>() as u64,
        std::mem::size_of::<CallRecord>() as u64,
        std::mem::size_of::<StorageQueryRecord>() as u64,
        std::mem::align_of::<i128>() as u64,
        MAX_WORKERS as u64,
    ]
}
