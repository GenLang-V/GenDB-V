//! One entry call, shared by every ABI version and crate kind: the call record and its dispatch range buffer, the
//! descriptive wall/CPU measurement, the decoding of status and dispatch, the result wire collector of query calls and
//! the build call with its direct-to-file part sink.

use super::error::AbiError;
use super::outcome::{CallOutcome, CallStatus, CallUsage, DispatchEvidence, check_query_wire};
use super::part_sink::PartFileSink;
use super::records::{BuildEntryFn, CallInputs, CallRecord, DerivedBuildEntryFn, PartDescriptor, ResultWireSink, StorageQueryInputs, StorageUseDescriptor};
use gendb_storage::io::{NativeColumn, PartFilesWriter, PartsManifest};
use std::ffi::c_void;

/// The dispatch range buffer of one call: `2 * range_capacity` words.
pub(super) fn range_buffer(range_capacity: usize) -> Result<Vec<u64>, AbiError> {
    Ok(vec![0u64; range_capacity.checked_mul(2).ok_or(AbiError::RangeCapacityOverflow)?])
}

/// A fresh call record (status `u32::MAX` until the shim writes one) pointing at `ranges`.
pub(super) fn new_call_record(ranges: &mut [u64]) -> CallRecord {
    CallRecord {
        status: u32::MAX,
        sql_error: 0,
        parts_delivered: 0,
        result_bytes: 0,
        spawned: 0,
        joined: 0,
        range_count: 0,
        range_capacity: (ranges.len() / 2) as u64,
        ranges: ranges.as_mut_ptr(),
    }
}

/// The outcome of a call the entry answered with `code` and `record` (no wire yet): a non-zero code is
/// [`AbiError::EntryFailed`] (the entry had no call record to write).
pub(super) fn decoded_call(code: i32, record: &CallRecord, ranges: &[u64], usage: CallUsage) -> Result<CallOutcome, AbiError> {
    if code != 0 {
        return Err(AbiError::EntryFailed(code));
    }
    Ok(CallOutcome {
        status: CallStatus::from_code(record.status)?,
        sql_error: None,
        result_wire: None,
        parts_delivered: record.parts_delivered,
        dispatch: reported_dispatch(record, ranges),
        usage,
        storage_requests: vec![],
    })
}

/// The dispatch the call record reports; at most `range_capacity` ranges were written.
fn reported_dispatch(record: &CallRecord, ranges: &[u64]) -> DispatchEvidence {
    let written = usize::try_from(record.range_count).unwrap_or(usize::MAX).min(ranges.len() / 2);
    DispatchEvidence {
        spawned: record.spawned,
        joined: record.joined,
        ranges: ranges.chunks_exact(2).take(written).map(|pair| (pair[0], pair[1])).collect(),
        ranges_reported: record.range_count,
    }
}

/// Run `entry` and measure its wall time and CPU usage (descriptive only).
pub(super) fn measure_call(entry: impl FnOnce() -> i32) -> (i32, CallUsage) {
    let start = std::time::Instant::now();
    let before = CpuTimes::now();
    let code = entry();
    let after = CpuTimes::now();
    let usage = CallUsage {
        wall_ns: start.elapsed().as_nanos() as u64,
        process_user_ns: after.process_user_ns.saturating_sub(before.process_user_ns),
        process_system_ns: after.process_system_ns.saturating_sub(before.process_system_ns),
        caller_cpu_ns: after.caller_ns.saturating_sub(before.caller_ns),
    };
    (code, usage)
}

/// Process user/system CPU and the calling thread's CPU (user + system), in nanoseconds.
struct CpuTimes {
    process_user_ns: u64,
    process_system_ns: u64,
    caller_ns: u64,
}

impl CpuTimes {
    fn now() -> Self {
        let ns = |t: libc::timeval| t.tv_sec as u64 * 1_000_000_000 + t.tv_usec as u64 * 1_000;
        // SAFETY: getrusage fills the zero-initialized structs it is given.
        let (process, thread) = unsafe {
            let mut process: libc::rusage = std::mem::zeroed();
            let mut thread: libc::rusage = std::mem::zeroed();
            libc::getrusage(libc::RUSAGE_SELF, &mut process);
            libc::getrusage(libc::RUSAGE_THREAD, &mut thread);
            (process, thread)
        };
        Self {
            process_user_ns: ns(process.ru_utime),
            process_system_ns: ns(process.ru_stime),
            caller_ns: ns(thread.ru_utime) + ns(thread.ru_stime),
        }
    }
}

/// Run a build entry (v3 `gendb_verus_build_v3` or v4 `gendb_verus_storage_build_v4`, same signature) over normalized
/// source columns. Each part it returns is written by `parts` straight from the builder's buffer as it is delivered;
/// the manifest is written (the directory committed) only when the build returned `Ok`.
///
/// # Safety
/// `build` must be a framework build entry, and every column descriptor must point at memory that stays mapped and
/// unchanged until this process exits.
pub(super) unsafe fn call_build_entry(
    build: BuildEntryFn,
    columns: &[NativeColumn],
    workers: usize,
    range_capacity: usize,
    parts: PartFilesWriter,
) -> Result<(CallOutcome, Option<PartsManifest>), AbiError> {
    let inputs = CallInputs::new(columns, &[], &[], workers);
    let mut sink = PartFileSink::new(parts);
    let sink_record = sink.record();
    let mut ranges = range_buffer(range_capacity)?;
    let mut record = new_call_record(&mut ranges);
    // SAFETY: `inputs`, `sink_record`, the sink and the record outlive the call; the caller guarantees the columns.
    let (code, usage) = measure_call(|| unsafe { build(&inputs, &sink_record, &mut record) });
    let outcome = decoded_call(code, &record, &ranges, usage)?;
    let (parts, delivery_error) = sink.into_parts();
    if let Some(error) = delivery_error {
        return Err(error);
    }
    if outcome.parts_delivered != parts.part_count() as u64 || record.result_bytes != 0 || record.sql_error != 0 {
        return Err(AbiError::PartDelivery("builder part count differs from delivered parts, or a build returned a result wire"));
    }
    if matches!(outcome.status, CallStatus::SqlError | CallStatus::ParamRefused | CallStatus::Capacity) {
        return Err(AbiError::BuildStatus(outcome.status));
    }
    let manifest = match outcome.status {
        CallStatus::Ok => Some(parts.finish()?),
        _ => None,
    };
    Ok((outcome, manifest))
}

/// Run a derived storage build entry (`gendb_verus_storage_build_derived_v4`) over the parts of its sources (`uses`, in
/// the builder's use order). Parts are written by `parts` as delivered, after any parts the caller linked first; the
/// manifest is written only when the build returned `Ok`.
///
/// # Safety
/// `build` must be a framework derived build entry, and every part descriptor must point at memory that stays mapped
/// and unchanged until this process exits.
pub(super) unsafe fn call_derived_build_entry(
    build: DerivedBuildEntryFn,
    uses: &[&[PartDescriptor]],
    workers: usize,
    range_capacity: usize,
    parts: PartFilesWriter,
) -> Result<(CallOutcome, Option<PartsManifest>), AbiError> {
    let use_records: Vec<StorageUseDescriptor> = uses.iter().map(|p| StorageUseDescriptor { part_count: p.len() as u64, parts: p.as_ptr() }).collect();
    let inputs = StorageQueryInputs::new(&use_records, &[], workers);
    let linked = parts.part_count() as u64;
    let mut sink = PartFileSink::new(parts);
    let sink_record = sink.record();
    let mut ranges = range_buffer(range_capacity)?;
    let mut record = new_call_record(&mut ranges);
    // SAFETY: `inputs`, `sink_record`, the sink and the record outlive the call; the caller guarantees the parts.
    let (code, usage) = measure_call(|| unsafe { build(&inputs, &sink_record, &mut record) });
    let outcome = decoded_call(code, &record, &ranges, usage)?;
    let (parts, delivery_error) = sink.into_parts();
    if let Some(error) = delivery_error {
        return Err(error);
    }
    if linked + outcome.parts_delivered != parts.part_count() as u64 || record.result_bytes != 0 || record.sql_error != 0 {
        return Err(AbiError::PartDelivery("derived builder part count differs from delivered parts, or a build returned a result wire"));
    }
    if matches!(outcome.status, CallStatus::SqlError | CallStatus::ParamRefused | CallStatus::Capacity) {
        return Err(AbiError::BuildStatus(outcome.status));
    }
    let manifest = match outcome.status {
        CallStatus::Ok => Some(parts.finish()?),
        _ => None,
    };
    Ok((outcome, manifest))
}

/// Receives the result wire during one query call.
pub(super) struct WireCollector {
    wire: Option<Vec<u8>>,
    error: Option<AbiError>,
}

impl WireCollector {
    pub fn new() -> Self {
        Self { wire: None, error: None }
    }

    /// The C sink record pointing at `self`; valid while `self` is neither moved nor dropped.
    pub fn record(&mut self) -> ResultWireSink {
        ResultWireSink { ctx: (self as *mut Self).cast(), put: Some(put_result_wire) }
    }

    /// Attach the delivered wire to `outcome` after checking that its length is the record's and that status, SQL
    /// error code and wire agree ([`check_query_wire`]).
    pub fn finish(self, outcome: &mut CallOutcome, record: &CallRecord) -> Result<(), AbiError> {
        if let Some(error) = self.error {
            return Err(error);
        }
        if self.wire.as_ref().map_or(0, |w| w.len() as u64) != record.result_bytes {
            return Err(AbiError::WireMismatch {
                status: outcome.status,
                reason: "result wire length differs from the call record".into(),
            });
        }
        outcome.sql_error = check_query_wire(outcome.status, record.sql_error, self.wire.as_deref())?;
        outcome.result_wire = self.wire;
        Ok(())
    }

    fn accept(&mut self, data: *const u8, len: u64) -> Result<(), AbiError> {
        if self.wire.is_some() {
            return Err(AbiError::WireDelivery("result wire delivered twice"));
        }
        let len = usize::try_from(len).map_err(|_| AbiError::WireDelivery("result wire extent overflow"))?;
        if len > 0 && data.is_null() {
            return Err(AbiError::WireDelivery("result wire data is null"));
        }
        // SAFETY: the shim passes a live buffer of `len` bytes for the duration of this call.
        self.wire = Some(if len == 0 { vec![] } else { unsafe { std::slice::from_raw_parts(data, len) }.to_vec() });
        Ok(())
    }
}

unsafe extern "C" fn put_result_wire(ctx: *mut c_void, data: *const u8, len: u64) -> i32 {
    // SAFETY: `ctx` is the `WireCollector` owned by the query call for the duration of the call.
    let collector = unsafe { &mut *ctx.cast::<WireCollector>() };
    match collector.accept(data, len) {
        Ok(()) => 0,
        Err(error) => {
            collector.error = Some(error);
            1
        }
    }
}
