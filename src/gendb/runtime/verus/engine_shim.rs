// ---- Engine crate entry (`runtime/verus/engine_shim.rs`) ----
//
// The trusted C glue of engine crates (`gendb_runtime::abi::GENDB_ENGINE_SHIM_SOURCE`: the shared v4 records of
// `shim_v4/records.rs`, then this part). NOT VERIFIED; a listed trusted component (`shim_engine`). It only (1) checks
// and converts host descriptors into `crate::gendb_abi` values (the parts of every storage use) and the AST bytes into a
// `&'static [u8]`, (2) calls the verified `crate::gendb_entry::abi_engine_query` / `abi_engine_echo` and (3) writes
// the call record, the result wire (the query shim's GSQLRS1 encoding, unchanged: no new status) and the storage
// request counters. It contains no query logic and no AST decoding (the verified entry decodes the bytes and answers
// `Malformed` / `ParamRefused` itself).
//
// The AST bytes, like stored parts, are honest as `&'static` only because the host keeps them unchanged until the
// calling process exits. A panic reaching this shim aborts the process.

use crate::exec::value::EVal;
use crate::gendb_abi::Part;
use crate::gendb_entry::stored::RequestCounts;
use crate::gendb_entry::results::{ResultColumn, ResultColumns};
use crate::spec::value::SqlError;

/// Version of the engine symbols and of `EngineQueryInputs` (reported by `gendb_verus_engine_layout_v1`).
const ENGINE_ABI_VERSION: u64 = 1;

/// GSQLRS1 result wire: magic, status byte, then rows (0), one SQL error code byte (1) or nothing (2, capacity).
const RESULT_MAGIC: &[u8; 8] = b"GSQLRS1\0";
const WIRE_ROWS: u8 = 0;
const WIRE_SQL_ERROR: u8 = 1;
const WIRE_CAPACITY: u8 = 2;

/// Inputs of an engine call: the storage uses in the engine's declared use order, the AST bytes (`ast_len` bytes at
/// `ast`, kept unchanged by the host until the process exits) and the worker count.
#[repr(C)]
pub struct EngineQueryInputs {
    uses: *const StorageUseDescriptor,
    use_count: u64,
    ast: *const u8,
    ast_len: u64,
    workers: u64,
}

/// Writes `[engine ABI version, sizes of EngineQueryInputs, StorageUseDescriptor, ResultWireSink, StorageQueryRecord]`
/// so the host can refuse an engine library compiled with another layout. Returns the number of available entries.
#[no_mangle]
pub unsafe extern "C" fn gendb_verus_engine_layout_v1(out: *mut u64, n: u64) -> u64 {
    let layout = [
        ENGINE_ABI_VERSION,
        std::mem::size_of::<EngineQueryInputs>() as u64,
        std::mem::size_of::<StorageUseDescriptor>() as u64,
        std::mem::size_of::<ResultWireSink>() as u64,
        std::mem::size_of::<StorageQueryRecord>() as u64,
    ];
    if !out.is_null() {
        for (i, v) in layout.iter().take(n as usize).enumerate() {
            unsafe { *out.add(i) = *v };
        }
    }
    layout.len() as u64
}

/// The part list of every storage use, in use order. The count must be the engine's declared use count
/// (`gendb_entry::stores::STORAGE_USES`, the entry's precondition) and the record must have room for every use's
/// counters; otherwise the call is refused before any verified code runs.
unsafe fn engine_uses(inputs: &EngineQueryInputs, out: &StorageQueryRecord) -> Option<Vec<Vec<Part>>> {
    let uses = unsafe { host_records(inputs.uses, inputs.use_count)? };
    if uses.len() != crate::gendb_entry::stores::STORAGE_USES
        || out.use_count != inputs.use_count
        || (!uses.is_empty() && out.request_counts.is_null())
    {
        return None;
    }
    let mut out = Vec::new();
    for u in uses {
        out.push(unsafe { storage_use_parts(u)? });
    }
    Some(out)
}

// ---- The query shim's result encoding, byte for byte (`shim_v4/query.rs`, from `write_request_counts` to
// `encode_columns`; a host test compares the two texts).

/// Write the counters of every reported handle at its use position; `counts_reported` counts the handles written.
unsafe fn write_request_counts(out: &mut StorageQueryRecord, requests: &[RequestCounts]) {
    for counts in requests {
        if counts.use_index >= out.use_count {
            continue;
        }
        let at = counts.use_index as usize * REQUEST_COUNT_WORDS;
        unsafe {
            *out.request_counts.add(at) = counts.requests;
            *out.request_counts.add(at + 1) = counts.elements;
            *out.request_counts.add(at + 2) = counts.bytes;
        }
        out.counts_reported += 1;
    }
}

/// SQL error code (identical to the SQLSpec reference evaluator shim's `error_code`).
fn error_code(e: &SqlError) -> u8 {
    match e {
        SqlError::NumericValueOutOfRange => 1,
        SqlError::DatetimeFieldOverflow => 2,
        SqlError::TypeError => 3,
        SqlError::DivisionByZero => 4,
        SqlError::CardinalityViolation => 5,
        SqlError::SubstringError => 6,
        SqlError::InvalidEscapeSequence => 7,
        SqlError::InvalidEscapeCharacter => 8,
    }
}

/// `EVal` -> GSQLRS1 value bytes (identical to the SQLSpec reference evaluator shim's `encode_value`).
fn encode_value(out: &mut Vec<u8>, v: &EVal) {
    match v {
        EVal::Null => out.push(0),
        EVal::Bool(b) => out.extend([1, *b as u8]),
        EVal::Int(x) => {
            out.push(2);
            out.extend(x.to_le_bytes());
        }
        EVal::Num { coeff, scale } => {
            out.push(3);
            out.extend(coeff.to_le_bytes());
            out.extend(scale.to_le_bytes());
        }
        EVal::Date(d) => {
            out.push(4);
            out.extend(d.to_le_bytes());
        }
        EVal::Ts(t) => {
            out.push(5);
            out.extend(t.to_le_bytes());
        }
        EVal::Text(b) => {
            out.push(6);
            out.extend((b.len() as u64).to_le_bytes());
            out.extend(b);
        }
    }
}

fn encode_rows(rows: &[Vec<EVal>]) -> Vec<u8> {
    let mut out = RESULT_MAGIC.to_vec();
    out.push(WIRE_ROWS);
    out.extend((rows.len() as u64).to_le_bytes());
    for row in rows {
        out.extend((row.len() as u64).to_le_bytes());
        for v in row {
            encode_value(&mut out, v);
        }
    }
    out
}

/// Bytes one value of column `c` at row `i` takes in the GSQLRS1 wire (`encode_value`).
fn column_value_bytes(c: &ResultColumn, i: usize) -> usize {
    match c {
        ResultColumn::Int(_) => 9,
        ResultColumn::Num { .. } => 21,
        ResultColumn::Date(_) => 5,
        ResultColumn::Text { offsets, .. } => 9 + (offsets[i + 1] - offsets[i]),
        ResultColumn::Values(v) => match &v[i] {
            EVal::Null => 1,
            EVal::Bool(_) => 2,
            EVal::Int(_) | EVal::Ts(_) => 9,
            EVal::Num { .. } => 21,
            EVal::Date(_) => 5,
            EVal::Text(b) => 9 + b.len(),
        },
    }
}

/// Append value `i` of column `c` in the GSQLRS1 value encoding (identical to `encode_value` of the same `EVal`).
fn encode_column_value(out: &mut Vec<u8>, c: &ResultColumn, i: usize) {
    match c {
        ResultColumn::Int(v) => {
            out.push(2);
            out.extend(v[i].to_le_bytes());
        }
        ResultColumn::Num { coeffs, scale } => {
            out.push(3);
            out.extend(coeffs[i].to_le_bytes());
            out.extend(scale.to_le_bytes());
        }
        ResultColumn::Date(v) => {
            out.push(4);
            out.extend(v[i].to_le_bytes());
        }
        ResultColumn::Text { offsets, bytes } => {
            let value = &bytes[offsets[i]..offsets[i + 1]];
            out.push(6);
            out.extend((value.len() as u64).to_le_bytes());
            out.extend(value);
        }
        ResultColumn::Values(v) => encode_value(out, &v[i]),
    }
}

/// A columnar answer as the same GSQLRS1 rows wire as `encode_rows` (row by row). The verified entry guarantees
/// `columns_wf` for a delivered columnar answer (every column has `rows` values; text offsets monotone and inside the
/// bytes), so the indexing below is in bounds; the exact size is computed first so the wire is allocated once.
fn encode_columns(answer: &ResultColumns) -> Vec<u8> {
    let (rows, columns) = (answer.rows, &answer.columns);
    let mut size = RESULT_MAGIC.len() + 1 + 8 + 8 * rows;
    for c in columns.iter() {
        for i in 0..rows {
            size += column_value_bytes(c, i);
        }
    }
    let mut out = Vec::with_capacity(size);
    out.extend_from_slice(RESULT_MAGIC);
    out.push(WIRE_ROWS);
    out.extend((rows as u64).to_le_bytes());
    for i in 0..rows {
        out.extend((columns.len() as u64).to_le_bytes());
        for c in columns.iter() {
            encode_column_value(&mut out, c, i);
        }
    }
    out
}

// ---- End of the query shim's result encoding.

/// Engine entry. `Ok` delivers the GSQLRS1 rows wire, `SqlError` the error wire (and `sql_error`), `Capacity` the
/// capacity wire; other statuses (`Refused`, `Malformed`, `ParamRefused`, `WorkerFailed`) deliver nothing. The request
/// counters of every storage use are written for every status the entry returns.
#[no_mangle]
pub unsafe extern "C" fn gendb_verus_engine_query_v1(
    inputs: *const EngineQueryInputs,
    sink: *const ResultWireSink,
    out: *mut StorageQueryRecord,
) -> i32 {
    abort_on_panic(|| {
        let Some(out) = (unsafe { out.as_mut() }) else { return -1 };
        reset_call_record(&mut out.call);
        out.counts_reported = 0;
        let (Some(inputs), Some(sink)) = (unsafe { inputs.as_ref() }, unsafe { sink.as_ref() }) else { return 0 };
        let (Some(put), Some(workers), Some(uses), Some(ast)) = (
            sink.put,
            requested_workers(inputs.workers),
            unsafe { engine_uses(inputs, out) },
            unsafe { host_slice::<u8>(inputs.ast, inputs.ast_len) },
        ) else {
            return 0;
        };
        let answered = crate::gendb_entry::abi_engine_query(uses, ast, workers);
        unsafe { write_request_counts(out, &answered.requests) };
        let r = &answered.result;
        unsafe { write_dispatch(&mut out.call, &r.dispatch) };
        out.call.status = status_code(&r.status);
        let mut wire = RESULT_MAGIC.to_vec();
        match &r.status {
            AbiStatus::Ok => {
                wire = match &answered.columns {
                    Some(columns) => encode_columns(columns),
                    None => encode_rows(&r.rows),
                }
            }
            AbiStatus::SqlError(e) => {
                out.call.sql_error = error_code(e) as u32;
                wire.push(WIRE_SQL_ERROR);
                wire.push(error_code(e));
            }
            AbiStatus::Capacity => wire.push(WIRE_CAPACITY),
            _ => return 0,
        }
        if unsafe { put(sink.ctx, wire.as_ptr(), wire.len() as u64) } != 0 {
            out.call.status = STATUS_SINK_FAILED;
            return 0;
        }
        out.call.result_bytes = wire.len() as u64;
        0
    })
}

/// Echo entry: the verified echo text of the statement the AST bytes decode to (`(Malformed)` for none) is handed to
/// `sink` once. Returns 0 when the sink received it, -1 for a null sink or AST bytes that are not a valid host extent,
/// -2 when the sink refused the text. Reads no stored data.
#[no_mangle]
pub unsafe extern "C" fn gendb_verus_engine_echo_v1(ast: *const u8, ast_len: u64, sink: *const ResultWireSink) -> i32 {
    abort_on_panic(|| {
        let Some(sink) = (unsafe { sink.as_ref() }) else { return -1 };
        let (Some(put), Some(ast)) = (sink.put, unsafe { host_slice::<u8>(ast, ast_len) }) else { return -1 };
        let text = crate::gendb_entry::abi_engine_echo(ast);
        if unsafe { put(sink.ctx, text.as_ptr(), text.len() as u64) } != 0 { -2 } else { 0 }
    })
}
