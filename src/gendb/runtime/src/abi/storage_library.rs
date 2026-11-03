//! Loaded ABI v4 libraries: a storage crate's build entry and a query crate's storage-use query entry.
//!
//! A storage build runs once per storage asset over the declared source columns of its storage and writes the parts
//! its builder returns ([`StorageBuildLibrary`]). A query call reads only the parts of its storage uses, one mapped
//! part list per use in the query's declared use order, and reports each use's verified request counters
//! ([`StorageQueryLibrary`]). The two kinds are separate compiled artifacts: each exports only its own entry.

use super::arguments::StatementArgument;
use super::call::{WireCollector, call_build_entry, call_derived_build_entry, decoded_call, measure_call, new_call_record, range_buffer};
use super::error::AbiError;
use super::loader::LoadedLibrary;
use super::outcome::{CallOutcome, StorageRequestCounts};
use super::records::{
    ArgumentDescriptor, BuildEntryFn, DerivedBuildEntryFn, LAYOUT_V4_SYMBOL, PartDescriptor, REQUEST_COUNT_WORDS, STORAGE_BUILD_SYMBOL,
    STORAGE_DERIVED_BUILD_SYMBOL, STORAGE_QUERY_SYMBOL, StorageQueryEntryFn, StorageQueryInputs, StorageQueryRecord, StorageUseDescriptor,
    expected_layout_v4,
};
use gendb_storage::io::{NativeColumn, PartFilesWriter, PartsManifest};
use std::path::Path;

/// A loaded v4 storage library (never unloaded, see [`LoadedLibrary`]).
pub struct StorageBuildLibrary {
    library: LoadedLibrary,
    build: BuildEntryFn,
}

impl StorageBuildLibrary {
    /// `dlopen` a storage library: v4 layout record, then its build entry.
    ///
    /// # Safety
    /// As [`LoadedLibrary::open`]: only a framework Verus build of a frozen crate, only in an offline child process.
    pub unsafe fn load(path: &Path) -> Result<Self, AbiError> {
        let library = unsafe { LoadedLibrary::open(path, LAYOUT_V4_SYMBOL, &expected_layout_v4())? };
        // SAFETY: the storage build entry has the v3 build signature (records.rs mirrors the shim).
        let build = unsafe { std::mem::transmute::<*mut std::ffi::c_void, BuildEntryFn>(library.symbol(STORAGE_BUILD_SYMBOL)?) };
        Ok(Self { library, build })
    }

    pub fn path(&self) -> &Path {
        &self.library.path
    }

    /// Run the storage builder once over the storage's declared source columns; its parts are written by `parts` as
    /// delivered and committed only on `Ok`.
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
        // SAFETY: `build` is this library's framework storage build entry; the caller guarantees the columns.
        unsafe { call_build_entry(self.build, columns, workers, range_capacity, parts) }
    }
}

/// A loaded v4 derived storage library (a storage built from admitted storages; never unloaded).
pub struct DerivedStorageBuildLibrary {
    library: LoadedLibrary,
    build: DerivedBuildEntryFn,
}

impl DerivedStorageBuildLibrary {
    /// `dlopen` a derived storage library: v4 layout record, then its derived build entry.
    ///
    /// # Safety
    /// As [`LoadedLibrary::open`]: only a framework Verus build of a frozen crate, only in an offline child process.
    pub unsafe fn load(path: &Path) -> Result<Self, AbiError> {
        let library = unsafe { LoadedLibrary::open(path, LAYOUT_V4_SYMBOL, &expected_layout_v4())? };
        // SAFETY: the derived build entry has the `DerivedBuildEntryFn` signature (records.rs mirrors the shim).
        let build =
            unsafe { std::mem::transmute::<*mut std::ffi::c_void, DerivedBuildEntryFn>(library.symbol(STORAGE_DERIVED_BUILD_SYMBOL)?) };
        Ok(Self { library, build })
    }

    pub fn path(&self) -> &Path {
        &self.library.path
    }

    /// Run the derived builder once over the mapped parts of its sources (`uses`, the builder's use order); its parts
    /// are written by `parts` after any parts already linked there, committed only on `Ok`.
    ///
    /// # Safety
    /// Every part descriptor must point at memory that stays mapped and unchanged until this process exits.
    pub unsafe fn call_build(
        &self,
        uses: &[&[PartDescriptor]],
        workers: usize,
        range_capacity: usize,
        parts: PartFilesWriter,
    ) -> Result<(CallOutcome, Option<PartsManifest>), AbiError> {
        // SAFETY: `build` is this library's framework derived build entry; the caller guarantees the parts.
        unsafe { call_derived_build_entry(self.build, uses, workers, range_capacity, parts) }
    }
}

/// A loaded v4 query library (never unloaded, see [`LoadedLibrary`]).
pub struct StorageQueryLibrary {
    library: LoadedLibrary,
    query: StorageQueryEntryFn,
}

impl StorageQueryLibrary {
    /// `dlopen` a v4 query library: v4 layout record, then its query entry.
    ///
    /// # Safety
    /// As [`LoadedLibrary::open`]: only a framework Verus build of a frozen crate, only in an offline child process.
    pub unsafe fn load(path: &Path) -> Result<Self, AbiError> {
        let library = unsafe { LoadedLibrary::open(path, LAYOUT_V4_SYMBOL, &expected_layout_v4())? };
        // SAFETY: the query entry has the `StorageQueryEntryFn` signature (records.rs mirrors the shim).
        let query =
            unsafe { std::mem::transmute::<*mut std::ffi::c_void, StorageQueryEntryFn>(library.symbol(STORAGE_QUERY_SYMBOL)?) };
        Ok(Self { library, query })
    }

    pub fn path(&self) -> &Path {
        &self.library.path
    }

    /// Run the query entry over `uses` (the mapped part list of each storage use, in the query's declared use order)
    /// with `arguments` (one per free parameter, slot order). Status, error code and wire must agree; the outcome
    /// carries the request counters of every handle the entry reported.
    ///
    /// # Safety
    /// Every part descriptor must point at memory that stays mapped and unchanged until this process exits, and so must
    /// the bytes of every text argument (the shim hands them to verified code as `&'static [u8]`; the worker child
    /// retains its arguments for its lifetime).
    pub unsafe fn call_query(
        &self,
        uses: &[&[PartDescriptor]],
        arguments: &[StatementArgument],
        workers: usize,
        range_capacity: usize,
    ) -> Result<CallOutcome, AbiError> {
        let use_records: Vec<StorageUseDescriptor> =
            uses.iter().map(|parts| StorageUseDescriptor { part_count: parts.len() as u64, parts: parts.as_ptr() }).collect();
        let argument_records: Vec<ArgumentDescriptor> = arguments.iter().map(|a| a.descriptor()).collect();
        let inputs = StorageQueryInputs::new(&use_records, &argument_records, workers);
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
        // SAFETY: inputs, sink, collector, record and its buffers outlive the call; the caller guarantees the parts.
        let (code, usage) = measure_call(|| unsafe { (self.query)(&inputs, &sink, &mut record) });
        let mut outcome = decoded_call(code, &record.call, &ranges, usage)?;
        collector.finish(&mut outcome, &record.call)?;
        outcome.storage_requests = reported_request_counts(&record, &counts)?;
        Ok(outcome)
    }
}

/// The counters of the handles the shim reported: none, or exactly one per storage use (the shim writes every
/// handle's counters at its use position; a partial report is a delivery error).
pub(super) fn reported_request_counts(record: &StorageQueryRecord, counts: &[u64]) -> Result<Vec<StorageRequestCounts>, AbiError> {
    if record.counts_reported == 0 {
        return Ok(vec![]);
    }
    if record.counts_reported != record.use_count {
        return Err(AbiError::WireDelivery("storage request counters reported for only some storage uses"));
    }
    Ok(counts
        .chunks_exact(REQUEST_COUNT_WORDS)
        .enumerate()
        .map(|(use_index, words)| StorageRequestCounts {
            use_index: use_index as u64,
            requests: words[0],
            elements: words[1],
            bytes: words[2],
        })
        .collect())
}
