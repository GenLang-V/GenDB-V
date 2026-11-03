// FRAMEWORK FILE: trusted C ABI shim of the GenDB Verus ABI v4 (gendb-runtime, `runtime/verus/shim_v4/`).
//
// Copied unchanged into every storage crate and every query crate of the fixed entry v4 as `crate::gendb_shim`,
// outside `verus!{}`: this part (records, codes and conversions, shared) followed by the entry part of the crate kind
// (`storage_build.rs` or `query.rs`). NOT VERIFIED; it is a listed trusted component. It only (1) checks and converts
// host descriptors into `crate::gendb_abi` values (columns, parts, statement arguments), (2) calls the verified
// entry of its crate (`crate::gendb_entry::abi_build_storage` or `crate::gendb_entry::abi_query`) and (3) writes the
// call record, the builder's parts, the result wire and the storage request counters. It contains no query logic, no
// parameter check (the verified entry decides the parameter domain and answers `ParamRefused`) and no way to create a
// stored-parts handle (the entry opens them).
//
// The record layouts and codes below mirror the host side (`gendb_runtime::abi`); the host refuses a library whose
// layout record differs, and a host test compares the codes with this text.
//
// Result wire: `GSQLRS1` (magic, status byte): 0 = rows (value encoding identical to the SQLSpec reference
// evaluator's shim, `sqlspec/interpreter/host/shim.rs`), 1 = SQL error followed by one code byte, 2 = capacity. The
// SQL error code is also written to `CallRecord::sql_error`.
// `&'static` slices are honest only because the host keeps every input, part, argument and this library mapped until
// the process that called it exits, and the verified code joins every worker it spawned before returning. A panic
// reaching this shim aborts the process, so no return can happen while a worker may still borrow host memory.
// Parts are read as host-order elements; the host maps only parts whose byte order is the host's.
#![allow(dead_code)]

use crate::gendb_abi::{AbiStatus, DispatchEvidence};
use std::ffi::c_void;

const ABI_VERSION: u64 = 4;
const MAX_WORKERS: u64 = 64;

const STATUS_OK: u32 = 0;
const STATUS_INVALID_INPUT: u32 = 1;
const STATUS_MALFORMED: u32 = 2;
const STATUS_WORKER_FAILED: u32 = 3;
const STATUS_REFUSED: u32 = 4;
const STATUS_CAPACITY: u32 = 5;
const STATUS_SQL_ERROR: u32 = 6;
const STATUS_PARAM_REFUSED: u32 = 7;
const STATUS_ABI_REFUSED: u32 = 16;
const STATUS_SINK_FAILED: u32 = 17;

// Column type tags accepted by a storage build (canonical NOT NULL columns); every other tag refuses the call.
const NATIVE_TYPE_I32: i32 = 1;
const NATIVE_TYPE_I64: i32 = 2;
const NATIVE_TYPE_I128: i32 = 3;
const NATIVE_TYPE_UTF8: i32 = 4;

// Part element codes.
const PART_I8: u32 = 1;
const PART_I16: u32 = 2;
const PART_I32: u32 = 3;
const PART_I64: u32 = 4;
const PART_I128: u32 = 5;
const PART_U8: u32 = 6;
const PART_U16: u32 = 7;
const PART_U32: u32 = 8;
const PART_U64: u32 = 9;

// Statement argument kinds.
const ARGUMENT_INT: u32 = 1;
const ARGUMENT_NUM: u32 = 2;
const ARGUMENT_DATE: u32 = 3;

/// Counter words per storage use in `StorageQueryRecord::request_counts`: requests, elements, bytes.
const REQUEST_COUNT_WORDS: usize = 3;

/// One normalized source column (the storage column descriptor, 48 bytes).
#[repr(C)]
pub struct NativeColumn {
    type_tag: i32,
    nullable: i32,
    len: i64,
    values: *const u8,
    offsets: *const i64,
    bytes: *const u8,
    validity: *const u8,
}

/// One stored part: `len` elements of type `elem` (a `PART_*` code) at `data`.
#[repr(C)]
pub struct PartDescriptor {
    elem: u32,
    reserved: u32,
    len: u64,
    data: *const u8,
}

/// One statement argument: `kind` 1 = integer (`int`), 2 = numeric coefficient (`num_lo` | `num_hi` << 64,
/// two's complement i128), 3 = date (`y`, `m`, `d`). Unused fields are ignored.
#[repr(C)]
pub struct ArgumentDescriptor {
    kind: u32,
    reserved: u32,
    int: i64,
    num_lo: u64,
    num_hi: u64,
    y: i32,
    m: i32,
    d: i32,
    reserved2: i32,
}

/// Inputs of a storage build: the delivered columns and the worker count (parts and arguments unused).
#[repr(C)]
pub struct CallInputs {
    columns: *const NativeColumn,
    column_count: u64,
    parts: *const PartDescriptor,
    part_count: u64,
    arguments: *const ArgumentDescriptor,
    argument_count: u64,
    workers: u64,
}

/// One storage use of a query call: `part_count` part descriptors at `parts`.
#[repr(C)]
pub struct StorageUseDescriptor {
    part_count: u64,
    parts: *const PartDescriptor,
}

/// Inputs of a query call: the storage uses in the query's declared use order, the arguments and the worker count.
#[repr(C)]
pub struct StorageQueryInputs {
    uses: *const StorageUseDescriptor,
    use_count: u64,
    arguments: *const ArgumentDescriptor,
    argument_count: u64,
    workers: u64,
}

/// Host sink of the builder's parts: called once per part, in part order.
#[repr(C)]
pub struct PartSink {
    ctx: *mut c_void,
    put: Option<unsafe extern "C" fn(*mut c_void, u64, u32, u64, *const u8) -> i32>,
}

/// Host sink of the result wire: called at most once per call with the complete bytes.
#[repr(C)]
pub struct ResultWireSink {
    ctx: *mut c_void,
    put: Option<unsafe extern "C" fn(*mut c_void, *const u8, u64) -> i32>,
}

/// Call record. `sql_error`: the SQL error code (1..=8) when `status` is 6, else 0.
#[repr(C)]
pub struct CallRecord {
    status: u32,
    sql_error: u32,
    parts_delivered: u64,
    result_bytes: u64,
    spawned: u64,
    joined: u64,
    range_count: u64,
    range_capacity: u64,
    ranges: *mut u64,
}

/// Call record of a query call: the call record, then the counters of every storage-use handle the entry reported
/// (`request_counts`: `REQUEST_COUNT_WORDS * use_count` host words; use `i` at words `3i..3i+3`).
#[repr(C)]
pub struct StorageQueryRecord {
    call: CallRecord,
    use_count: u64,
    counts_reported: u64,
    request_counts: *mut u64,
}

/// `len` host elements of `T` at `data`, or `None` if the pointer is null or misaligned or the extent overflows.
unsafe fn host_slice<T>(data: *const u8, len: u64) -> Option<&'static [T]> {
    let len = usize::try_from(len).ok()?;
    if len == 0 {
        return Some(&[]);
    }
    if data.is_null() || (data as usize) % std::mem::align_of::<T>() != 0 {
        return None;
    }
    if len.checked_mul(std::mem::size_of::<T>())? > isize::MAX as usize {
        return None;
    }
    Some(unsafe { std::slice::from_raw_parts(data.cast::<T>(), len) })
}

/// The `len` host records at `data` (descriptor arrays, valid for the call only).
unsafe fn host_records<'a, T>(data: *const T, len: u64) -> Option<&'a [T]> {
    let len = usize::try_from(len).ok()?;
    if len == 0 {
        return Some(&[]);
    }
    if data.is_null() {
        return None;
    }
    Some(unsafe { std::slice::from_raw_parts(data, len) })
}

/// The requested worker count, if it is in 1..=MAX_WORKERS.
fn requested_workers(workers: u64) -> Option<usize> {
    if (1..=MAX_WORKERS).contains(&workers) { Some(workers as usize) } else { None }
}

fn status_code(status: &AbiStatus) -> u32 {
    match status {
        AbiStatus::Ok => STATUS_OK,
        AbiStatus::InvalidInput => STATUS_INVALID_INPUT,
        AbiStatus::Malformed => STATUS_MALFORMED,
        AbiStatus::WorkerFailed => STATUS_WORKER_FAILED,
        AbiStatus::Refused => STATUS_REFUSED,
        AbiStatus::Capacity => STATUS_CAPACITY,
        AbiStatus::SqlError(_) => STATUS_SQL_ERROR,
        AbiStatus::ParamRefused => STATUS_PARAM_REFUSED,
    }
}

unsafe fn write_dispatch(out: &mut CallRecord, dispatch: &DispatchEvidence) {
    out.spawned = dispatch.spawned;
    out.joined = dispatch.joined;
    out.range_count = dispatch.ranges.len() as u64;
    if !out.ranges.is_null() {
        for (i, (lo, hi)) in dispatch.ranges.iter().take(out.range_capacity as usize).enumerate() {
            unsafe {
                *out.ranges.add(2 * i) = *lo;
                *out.ranges.add(2 * i + 1) = *hi;
            }
        }
    }
}

/// Start every call as `AbiRefused` with nothing delivered; the range buffer and its capacity are the host's.
fn reset_call_record(out: &mut CallRecord) {
    out.status = STATUS_ABI_REFUSED;
    out.sql_error = 0;
    out.parts_delivered = 0;
    out.result_bytes = 0;
    out.spawned = 0;
    out.joined = 0;
    out.range_count = 0;
}

fn abort_on_panic<R>(f: impl FnOnce() -> R) -> R {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
        Ok(r) => r,
        Err(_) => std::process::abort(),
    }
}

/// Writes `[abi version, sizes and alignments of the ABI records]` so the host can refuse a library compiled with a
/// different layout. Returns the number of available entries.
#[no_mangle]
pub unsafe extern "C" fn gendb_verus_abi_layout_v4(out: *mut u64, n: u64) -> u64 {
    let layout = [
        ABI_VERSION,
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
        MAX_WORKERS,
    ];
    if !out.is_null() {
        for (i, v) in layout.iter().take(n as usize).enumerate() {
            unsafe { *out.add(i) = *v };
        }
    }
    layout.len() as u64
}

/// The parts of one storage use (a query's storage use, or a source of a storage built from admitted storages), as
/// host-order slices. An unknown element code refuses the call.
unsafe fn storage_use_parts(u: &StorageUseDescriptor) -> Option<Vec<crate::gendb_abi::Part>> {
    use crate::gendb_abi::Part;
    let mut out = Vec::new();
    for p in unsafe { host_records(u.parts, u.part_count)? } {
        out.push(match p.elem {
            PART_I8 => Part::I8(unsafe { host_slice(p.data, p.len)? }),
            PART_I16 => Part::I16(unsafe { host_slice(p.data, p.len)? }),
            PART_I32 => Part::I32(unsafe { host_slice(p.data, p.len)? }),
            PART_I64 => Part::I64(unsafe { host_slice(p.data, p.len)? }),
            PART_I128 => Part::I128(unsafe { host_slice(p.data, p.len)? }),
            PART_U8 => Part::U8(unsafe { host_slice(p.data, p.len)? }),
            PART_U16 => Part::U16(unsafe { host_slice(p.data, p.len)? }),
            PART_U32 => Part::U32(unsafe { host_slice(p.data, p.len)? }),
            PART_U64 => Part::U64(unsafe { host_slice(p.data, p.len)? }),
            _ => return None,
        });
    }
    Some(out)
}

/// Element code, element count and data of one builder part (storage builds hand them to the host sink).
fn owned_part_raw(part: &crate::gendb_abi::OwnedPart) -> (u32, usize, *const u8) {
    use crate::gendb_abi::OwnedPart;
    match part {
        OwnedPart::I8(v) => (PART_I8, v.len(), v.as_ptr().cast::<u8>()),
        OwnedPart::I16(v) => (PART_I16, v.len(), v.as_ptr().cast::<u8>()),
        OwnedPart::I32(v) => (PART_I32, v.len(), v.as_ptr().cast::<u8>()),
        OwnedPart::I64(v) => (PART_I64, v.len(), v.as_ptr().cast::<u8>()),
        OwnedPart::I128(v) => (PART_I128, v.len(), v.as_ptr().cast::<u8>()),
        OwnedPart::U8(v) => (PART_U8, v.len(), v.as_ptr().cast::<u8>()),
        OwnedPart::U16(v) => (PART_U16, v.len(), v.as_ptr().cast::<u8>()),
        OwnedPart::U32(v) => (PART_U32, v.len(), v.as_ptr().cast::<u8>()),
        OwnedPart::U64(v) => (PART_U64, v.len(), v.as_ptr().cast::<u8>()),
    }
}
// ---- Storage crate entry, nullable source columns (`runtime/verus/shim_v4/storage_build_nullable.rs`) ----
//
// The storage build shim of a storage crate whose declaration has a nullable column, used instead of
// `storage_build.rs` (which stays the shim of every declaration of NOT NULL columns, byte for byte). It differs only in
// `input_columns`: a nullable column descriptor delivers its values column, then its validity (one byte per row, 1
// valid, 0 NULL, from the descriptor's validity buffer) as a `Column::Utf8` with no offsets. `gendb_abi.rs` has no
// byte-column variant, and adding one would change the dependency closure of every admitted storage; a text column
// always has at least one offset, so the verified binder (`gendb_entry/binder.rs`) tells the two apart.

use crate::gendb_abi::Column;

/// Utf8: `len + 1` absolute offsets; the byte extent is `offsets[len]` (canonical capture). Monotonicity and ranges
/// are decided by the verified binder, not here.
unsafe fn utf8_column(c: &NativeColumn) -> Option<Column> {
    let rows = u64::try_from(c.len).ok()?;
    let offsets: &'static [i64] = unsafe { host_slice(c.offsets.cast::<u8>(), rows.checked_add(1)?)? };
    let extent = u64::try_from(*offsets.last()?).ok()?;
    let bytes: &'static [u8] = unsafe { host_slice(c.bytes, extent)? };
    Some(Column::Utf8 { offsets, bytes })
}

/// The validity of a nullable column of `len` rows: its bytes as a `Column::Utf8` with no offsets.
unsafe fn validity_column(c: &NativeColumn) -> Option<Column> {
    let validity: &'static [u8] = unsafe { host_slice(c.validity, c.len as u64)? };
    Some(Column::Utf8 { offsets: &[], bytes: validity })
}

/// Build input columns: each column's values, and after a nullable column its validity. An unsupported type tag
/// refuses the call.
unsafe fn input_columns(inputs: &CallInputs) -> Option<Vec<Column>> {
    let mut out = Vec::new();
    for c in unsafe { host_records(inputs.columns, inputs.column_count)? } {
        if c.len < 0 {
            return None;
        }
        out.push(match c.type_tag {
            NATIVE_TYPE_I32 => Column::I32(unsafe { host_slice(c.values, c.len as u64)? }),
            NATIVE_TYPE_I64 => Column::I64(unsafe { host_slice(c.values, c.len as u64)? }),
            NATIVE_TYPE_I128 => Column::I128(unsafe { host_slice(c.values, c.len as u64)? }),
            NATIVE_TYPE_UTF8 => unsafe { utf8_column(c)? },
            _ => return None,
        });
        if c.nullable != 0 {
            out.push(unsafe { validity_column(c)? });
        }
    }
    Some(out)
}

/// Storage build entry. Statement arguments are not read: a storage asset is built once for every statement and
/// binding that reads it. On `Ok` every part is handed to the host sink from the builder's own buffer (the host writes
/// it to its file during the call); other statuses deliver nothing.
#[no_mangle]
pub unsafe extern "C" fn gendb_verus_storage_build_v4(
    inputs: *const CallInputs,
    sink: *const PartSink,
    out: *mut CallRecord,
) -> i32 {
    abort_on_panic(|| {
        let Some(out) = (unsafe { out.as_mut() }) else { return -1 };
        reset_call_record(out);
        let (Some(inputs), Some(sink)) = (unsafe { inputs.as_ref() }, unsafe { sink.as_ref() }) else { return 0 };
        let (Some(put), Some(workers), Some(columns)) =
            (sink.put, requested_workers(inputs.workers), unsafe { input_columns(inputs) })
        else {
            return 0;
        };
        let r = crate::gendb_entry::abi_build_storage(&columns, workers);
        unsafe { write_dispatch(out, &r.dispatch) };
        out.status = status_code(&r.status);
        if out.status != STATUS_OK {
            return 0;
        }
        for (i, part) in r.parts.iter().enumerate() {
            let (elem, len, data) = owned_part_raw(part);
            if unsafe { put(sink.ctx, i as u64, elem, len as u64, data) } != 0 {
                out.status = STATUS_SINK_FAILED;
                return 0;
            }
            out.parts_delivered += 1;
        }
        0
    })
}
