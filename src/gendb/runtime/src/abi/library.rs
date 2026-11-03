//! A loaded ABI v3 library (the saved v3 route and the current candidate crates) and calls of its build and query
//! entries.

use super::arguments::StatementArgument;
use super::call::{WireCollector, call_build_entry, decoded_call, measure_call, new_call_record, range_buffer};
use super::error::AbiError;
use super::loader::LoadedLibrary;
use super::outcome::CallOutcome;
use super::records::{
    ArgumentDescriptor, BUILD_SYMBOL, BuildEntryFn, CallInputs, LAYOUT_SYMBOL, PartDescriptor, QUERY_SYMBOL,
    QueryEntryFn, expected_layout,
};
use gendb_storage::io::{NativeColumn, PartFilesWriter, PartsManifest};
use std::path::Path;

/// A loaded v3 library with both entries. Never unloaded (see [`LoadedLibrary`]).
pub struct VerusLibrary {
    library: LoadedLibrary,
    query: QueryEntryFn,
    build: BuildEntryFn,
}

impl VerusLibrary {
    /// `dlopen`, then refuse a library whose ABI version or record layout differs from this host (a saved v1 or v2
    /// library lacks the v3 layout symbol and is refused).
    ///
    /// # Safety
    /// As [`LoadedLibrary::open`]: only a framework Verus build of a frozen crate, only in an offline child process.
    pub unsafe fn load(path: &Path) -> Result<Self, AbiError> {
        let library = unsafe { LoadedLibrary::open(path, LAYOUT_SYMBOL, &expected_layout())? };
        // SAFETY: each symbol is a framework shim entry of the matching C signature (records.rs mirrors the shim).
        let (query, build) = unsafe {
            (
                std::mem::transmute::<*mut std::ffi::c_void, QueryEntryFn>(library.symbol(QUERY_SYMBOL)?),
                std::mem::transmute::<*mut std::ffi::c_void, BuildEntryFn>(library.symbol(BUILD_SYMBOL)?),
            )
        };
        Ok(Self { library, query, build })
    }

    pub fn path(&self) -> &Path {
        &self.library.path
    }

    /// Run the query entry over stored parts with `arguments` (one per free parameter, slot order). The status, error
    /// code and wire must agree ([`super::check_query_wire`]).
    ///
    /// # Safety
    /// Every part descriptor must point at memory that stays mapped and unchanged until this process exits.
    pub unsafe fn call_query(
        &self,
        parts: &[PartDescriptor],
        arguments: &[StatementArgument],
        workers: usize,
        range_capacity: usize,
    ) -> Result<CallOutcome, AbiError> {
        let argument_records: Vec<ArgumentDescriptor> = arguments.iter().map(|a| a.descriptor()).collect();
        let inputs = CallInputs::new(&[], parts, &argument_records, workers);
        let mut collector = WireCollector::new();
        let sink = collector.record();
        let mut ranges = range_buffer(range_capacity)?;
        let mut record = new_call_record(&mut ranges);
        // SAFETY: `inputs`, `sink`, the collector and the record outlive the call; the caller guarantees the parts.
        let (code, usage) = measure_call(|| unsafe { (self.query)(&inputs, &sink, &mut record) });
        let mut outcome = decoded_call(code, &record, &ranges, usage)?;
        collector.finish(&mut outcome, &record)?;
        Ok(outcome)
    }

    /// Run the representation builder over normalized source columns; its parts are written by `parts` as delivered
    /// and committed only on `Ok` ([`call_build_entry`]). The builder reads no statement argument: one stored asset
    /// serves every binding.
    ///
    /// # Safety
    /// Every column descriptor must point at memory that stays mapped and unchanged until this process exits.
    pub unsafe fn call_build(
        &self,
        columns: &[NativeColumn],
        workers: usize,
        range_capacity: usize,
        parts: PartFilesWriter,
    ) -> Result<(CallOutcome, Option<PartsManifest>), AbiError> {
        // SAFETY: `build` is this library's framework build entry; the caller guarantees the columns.
        unsafe { call_build_entry(self.build, columns, workers, range_capacity, parts) }
    }
}
