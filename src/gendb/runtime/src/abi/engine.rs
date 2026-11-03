//! Host side of engine libraries (fixed engine entry `gendb-verus-engine-entry-v1`): load a compiled engine crate, call
//! it with the parts of its storage uses and one statement's AST bytes, and ask it for the verified echo of AST bytes.
//!
//! An engine library exports the v4 layout record (`gendb_verus_abi_layout_v4`, the shared v4 records) and its own
//! layout record ([`ENGINE_LAYOUT_SYMBOL`], [`expected_engine_layout`]), the call entry [`ENGINE_QUERY_SYMBOL`] and the
//! echo entry [`ENGINE_ECHO_SYMBOL`]. Results use the unchanged v4 query record and GSQLRS1 wire (no new status):
//! `Malformed` (bytes that decode to no statement) and `ParamRefused` (a statement that is not supported) deliver no
//! wire, like the other refusals.
//!
//! The Verus sources of engine crates that live in the runtime: [`ENGINE_CODEC_SOURCE`] (`crate::gendb_ast_codec`) and
//! the trusted shim [`GENDB_ENGINE_SHIM_SOURCE`] (`crate::gendb_shim`: the shared v4 records, then
//! `runtime/verus/engine_shim.rs`).
//!
//! TRUSTED (not verified), like the rest of this module: the loader, the record mirrors and the shim. The AST bytes and
//! every part are handed to verified code as `&'static` slices, honest only in a short-lived child process that keeps
//! them until it exits (`gendb worker`).

use super::call::{decoded_call, measure_call, new_call_record, range_buffer, WireCollector};
use super::error::AbiError;
use super::loader::LoadedLibrary;
use super::outcome::CallOutcome;
use super::records::{
    expected_layout_v4, PartDescriptor, ResultWireSink, StorageQueryRecord, StorageUseDescriptor, LAYOUT_V4_SYMBOL, REQUEST_COUNT_WORDS,
};
use super::storage_library::reported_request_counts;
use std::ffi::c_void;
use std::path::Path;

/// `crate::gendb_ast_codec` of every engine crate: the fixed meaning of AST bytes (`decode_spec`), the verified decoder
/// and the verified echo renderer.
pub const ENGINE_CODEC_SOURCE: &str = include_str!("../../verus/engine_codec.rs");

/// `crate::gendb_shim` of every engine crate: the shared v4 records, then the engine entries
/// (`gendb_verus_engine_query_v1` -> `crate::gendb_entry::abi_engine_query`, `gendb_verus_engine_echo_v1` ->
/// `crate::gendb_entry::abi_engine_echo`).
pub const GENDB_ENGINE_SHIM_SOURCE: &str = concat!(include_str!("../../verus/shim_v4/records.rs"), include_str!("../../verus/engine_shim.rs"));

/// Version of the engine symbols and of [`EngineQueryInputs`].
pub const ENGINE_ABI_VERSION: u64 = 1;
pub const ENGINE_LAYOUT_SYMBOL: &str = "gendb_verus_engine_layout_v1";
pub const ENGINE_QUERY_SYMBOL: &str = "gendb_verus_engine_query_v1";
pub const ENGINE_ECHO_SYMBOL: &str = "gendb_verus_engine_echo_v1";

/// Trusted items of the engine ABI boundary, `(id, statement)`, for the TCB list of engine packages (with the v4 items
/// of the shared records and the worker).
pub const TRUSTED_ITEMS_ENGINE: [(&str, &str); 2] = [
    (
        "shim_engine",
        "runtime/verus/{shim_v4/records.rs, engine_shim.rs}: descriptors -> &'static slices (one part list per storage use, in \
         declared use order; use count equal to the crate's STORAGE_USES), the AST bytes -> a &'static [u8] (kept by the host \
         until the process exits), catch_unwind -> abort, worker-count check, GSQLRS1 rows/error/capacity encoding (the query \
         shim's text), the call record's error code, every use's request counters and the echo text to the host sink",
    ),
    (
        "host_abi_engine",
        "gendb_runtime::abi::engine: dlopen, v4 and engine layout-record checks, storage-use descriptors and the AST extent, status \
         decoding, status/error/wire agreement, request counters read back per storage use (all or none), echo bytes collected once",
    ),
];

/// Inputs of one engine call (mirrors `EngineQueryInputs` of `runtime/verus/engine_shim.rs`).
#[repr(C)]
pub(super) struct EngineQueryInputs {
    pub uses: *const StorageUseDescriptor,
    pub use_count: u64,
    pub ast: *const u8,
    pub ast_len: u64,
    pub workers: u64,
}

type EngineQueryEntryFn = unsafe extern "C" fn(*const EngineQueryInputs, *const ResultWireSink, *mut StorageQueryRecord) -> i32;
type EngineEchoFn = unsafe extern "C" fn(*const u8, u64, *const ResultWireSink) -> i32;

/// The engine layout record a library must report through [`ENGINE_LAYOUT_SYMBOL`]: engine ABI version, then the sizes
/// of the engine inputs, storage-use descriptor, result wire sink and v4 query record.
pub fn expected_engine_layout() -> [u64; 5] {
    [
        ENGINE_ABI_VERSION,
        std::mem::size_of::<EngineQueryInputs>() as u64,
        std::mem::size_of::<StorageUseDescriptor>() as u64,
        std::mem::size_of::<ResultWireSink>() as u64,
        std::mem::size_of::<StorageQueryRecord>() as u64,
    ]
}

/// A loaded engine library (never unloaded, see `LoadedLibrary`).
pub struct EngineLibrary {
    library: LoadedLibrary,
    query: EngineQueryEntryFn,
    echo: EngineEchoFn,
}

impl EngineLibrary {
    /// `dlopen` an engine library: the v4 layout record, the engine layout record, then both engine entries.
    ///
    /// # Safety
    /// As `LoadedLibrary::open`: only a framework Verus build of a frozen engine crate, only in an offline child process.
    pub unsafe fn load(path: &Path) -> Result<Self, AbiError> {
        let library = unsafe { LoadedLibrary::open(path, LAYOUT_V4_SYMBOL, &expected_layout_v4())? };
        // SAFETY: the engine layout symbol has the `LayoutFn` signature (engine_shim.rs).
        let layout: super::records::LayoutFn = unsafe { std::mem::transmute(library.symbol(ENGINE_LAYOUT_SYMBOL)?) };
        let expected = expected_engine_layout();
        let mut actual = vec![0u64; expected.len()];
        let available = unsafe { layout(actual.as_mut_ptr(), actual.len() as u64) };
        if available != expected.len() as u64 || actual != expected {
            return Err(AbiError::LayoutMismatch { actual, expected: expected.to_vec() });
        }
        // SAFETY: the entries have the signatures engine_shim.rs declares for them.
        let query = unsafe { std::mem::transmute::<*mut c_void, EngineQueryEntryFn>(library.symbol(ENGINE_QUERY_SYMBOL)?) };
        let echo = unsafe { std::mem::transmute::<*mut c_void, EngineEchoFn>(library.symbol(ENGINE_ECHO_SYMBOL)?) };
        Ok(Self { library, query, echo })
    }

    pub fn path(&self) -> &Path {
        &self.library.path
    }

    /// Run the engine over `uses` (the mapped part list of each storage use, in the engine's declared use order) for
    /// the statement `ast` (encoded by `gendb_frontend::engine_encode`). Status, error code and wire must agree; the
    /// outcome carries the request counters of every handle the entry reported.
    ///
    /// # Safety
    /// Every part descriptor and the AST bytes must stay mapped and unchanged until this process exits (the shim hands
    /// them to verified code as `&'static` slices; the worker child retains them for its lifetime).
    pub unsafe fn call(&self, uses: &[&[PartDescriptor]], ast: &[u8], workers: usize, range_capacity: usize) -> Result<CallOutcome, AbiError> {
        let use_records: Vec<StorageUseDescriptor> =
            uses.iter().map(|parts| StorageUseDescriptor { part_count: parts.len() as u64, parts: parts.as_ptr() }).collect();
        let inputs = EngineQueryInputs {
            uses: use_records.as_ptr(),
            use_count: use_records.len() as u64,
            ast: ast.as_ptr(),
            ast_len: ast.len() as u64,
            workers: workers as u64,
        };
        let mut collector = WireCollector::new();
        let sink = collector.record();
        let mut ranges = range_buffer(range_capacity)?;
        let words = uses.len().checked_mul(REQUEST_COUNT_WORDS).ok_or(AbiError::RangeCapacityOverflow)?;
        let mut counts = vec![0u64; words];
        let mut record = StorageQueryRecord {
            call: new_call_record(&mut ranges),
            use_count: uses.len() as u64,
            counts_reported: 0,
            request_counts: counts.as_mut_ptr(),
        };
        // SAFETY: inputs, sink, collector, record and its buffers outlive the call; the caller guarantees parts and AST.
        let (code, usage) = measure_call(|| unsafe { (self.query)(&inputs, &sink, &mut record) });
        let mut outcome = decoded_call(code, &record.call, &ranges, usage)?;
        collector.finish(&mut outcome, &record.call)?;
        outcome.storage_requests = reported_request_counts(&record, &counts)?;
        Ok(outcome)
    }

    /// The verified echo text of `ast`: the evaluator's echo grammar for the statement the bytes decode to, or
    /// `(Malformed)`. Reads no stored data.
    ///
    /// # Safety
    /// The AST bytes must stay mapped and unchanged until this process exits.
    pub unsafe fn echo(&self, ast: &[u8]) -> Result<Vec<u8>, AbiError> {
        let mut text: Option<Vec<u8>> = None;
        let sink = ResultWireSink { ctx: (&mut text as *mut Option<Vec<u8>>).cast(), put: Some(put_echo) };
        // SAFETY: `sink` and `text` outlive the call; the caller guarantees the AST bytes.
        let code = unsafe { (self.echo)(ast.as_ptr(), ast.len() as u64, &sink) };
        match (code, text) {
            (0, Some(text)) => Ok(text),
            (0, None) => Err(AbiError::WireDelivery("the engine echo returned without delivering its text")),
            (code, _) => Err(AbiError::EntryFailed(code)),
        }
    }
}

unsafe extern "C" fn put_echo(ctx: *mut c_void, data: *const u8, len: u64) -> i32 {
    // SAFETY: `ctx` is the `Option<Vec<u8>>` owned by `EngineLibrary::echo` for the duration of the call.
    let text = unsafe { &mut *ctx.cast::<Option<Vec<u8>>>() };
    let Ok(len) = usize::try_from(len) else { return 1 };
    if text.is_some() || (len > 0 && data.is_null()) {
        return 1;
    }
    // SAFETY: the shim passes a live buffer of `len` bytes for the duration of this call.
    *text = Some(if len == 0 { vec![] } else { unsafe { std::slice::from_raw_parts(data, len) }.to_vec() });
    0
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The engine shim's result encoding is the query shim's text, byte for byte (no new status, one wire).
    #[test]
    fn engine_shim_encodes_results_as_the_query_shim() {
        let query = include_str!("../../verus/shim_v4/query.rs");
        let engine = include_str!("../../verus/engine_shim.rs");
        let block = |text: &'static str| -> &'static str {
            let start = text.find("/// Write the counters of every reported handle").expect("encoding start");
            let columns = start + text[start..].find("fn encode_columns").expect("encode_columns");
            let end = columns + text[columns..].find("\n}\n").expect("end of encode_columns") + 3;
            &text[start..end]
        };
        assert_eq!(block(engine), block(query));
        for (code, name) in [(0, "STATUS_OK"), (2, "STATUS_MALFORMED"), (7, "STATUS_PARAM_REFUSED")] {
            assert!(include_str!("../../verus/shim_v4/records.rs").contains(&format!("const {name}: u32 = {code};")));
        }
    }

    #[test]
    fn engine_layout_names_the_engine_records() {
        let layout = expected_engine_layout();
        assert_eq!(layout[0], ENGINE_ABI_VERSION);
        assert_eq!(layout[1], 40, "EngineQueryInputs: two pointers and three u64 on a 64-bit host");
        assert!(GENDB_ENGINE_SHIM_SOURCE.contains("pub unsafe extern \"C\" fn gendb_verus_abi_layout_v4"));
        for symbol in [ENGINE_LAYOUT_SYMBOL, ENGINE_QUERY_SYMBOL, ENGINE_ECHO_SYMBOL] {
            assert!(GENDB_ENGINE_SHIM_SOURCE.contains(&format!("pub unsafe extern \"C\" fn {symbol}(")), "{symbol}");
        }
    }
}
