//! Profile feedback of an engine version: where each template's time goes, for the
//! author's next round. Profiles are diagnostics: never gating, never timing evidence, never on the serving path.
//!
//! One profile job per template ([`profile_statement`]): one fresh worker child running the template's official
//! statement at one worker count, 1 warm and 1 measured call (`PROFILE_REPETITIONS`), with the run's per-call limits
//! (an unfinished template is profiled up to the limit, which shows where the time goes before the stop) and the
//! child's sampler armed (`gendb_runtime::worker::SamplingRequest`, [`PROFILE_SAMPLE_INTERVAL_US`] of process CPU time
//! between samples). No answer is compared, so the child stores each answer under the framework's stored-answer bound
//! (`AnswerBound::STORED`: an answer over 100 rows or 1 MiB of row text is kept as its row count, digest and first
//! rows). [`profile_version`] runs every template at the worker count with its largest gap
//! (`super::score::ScaleScore::largest_gap_workers`), each child under the caller's lease, after the timing, so timed
//! calls are never perturbed.
//!
//! Recorded per call: wall time, process and calling-thread CPU, the watchdog's sampled peak of anonymous memory,
//! process read bytes and the dispatch counts. Recorded for the last call that ran (the measured call, or the call the
//! watchdog stopped): the sampled hot functions by **self samples**. The child records instruction pointers only (the
//! engine libraries have their `.symtab` symbols but no frame pointers: `opt-level` builds omit them and the Verus build
//! passes no `-C force-frame-pointers`), so there is no inclusive time. Each sampled address is placed in the function
//! of the object's symbol table (read with the `object` crate) that contains it; Rust names are demangled
//! ([`demangle`]: the v0 scheme the Verus toolchain uses, and the legacy one) and the engine crate's own prefix
//! (`gendb_engine::`) is dropped, so engine functions read as module paths (`agent::…`, `exec::relational::…`). Samples
//! in the worker executable itself (the host), in an object without a readable symbol table, or at an address no
//! symbol covers (a stripped library's internal functions) are grouped per object. Output: `PROFILE.md` and
//! `profile/<statement>-w<workers>.json` ([`write_profile`]).

mod demangle;

use super::score::ScaleScore;
use super::timing::EngineStatement;
use gendb_runtime::abi::CallStatus;
use gendb_runtime::worker::{AnswerBound, CallLimits, CallObservation, CallSamples, SamplingRequest, StorageUseInput, Unfinished, UnfinishedReason, WorkerRequest};
use gendb_storage::io::PartAccess;
use gendb_verification::admission::AdmissionError;
use gendb_verification::admission::execution::{CandidateRunner, PROFILE_REPETITIONS, RANGE_CAPACITY};
use gendb_verification::obligations::ENGINE_CRATE_NAME;
use object::{Object, ObjectSymbol, SymbolKind};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

pub use demangle::demangle;

/// Process CPU time between samples, microseconds (a framework constant of profile jobs).
pub const PROFILE_SAMPLE_INTERVAL_US: u32 = 1000;
/// The report and the per-statement records, relative to the directory [`write_profile`] writes into.
pub const PROFILE_FILE: &str = "PROFILE.md";
pub const PROFILE_DIRECTORY: &str = "profile";
/// Functions listed per statement in `PROFILE.md` (all of them are in the JSON record).
const LISTED_FUNCTIONS: usize = 15;

/// What the profile method can and cannot show, recorded with every profile.
pub const PROFILE_METHOD: &str = "self samples only: a SIGPROF timer over process CPU time records the interrupted instruction pointer of a \
busy thread (no stack walk: the engine library has no frame pointers), placed in the containing function of the object's symbol table; \
samples are descriptive and the sampling perturbs the call slightly, so profile times are never timing evidence";

/// The compiled engine version a profile runs, and the limits of its calls.
pub struct ProfileSubject<'a> {
    pub runner: &'a CandidateRunner,
    /// The compiled engine library.
    pub library: &'a Path,
    /// Its storage uses' parts directories, in use order.
    pub uses: &'a [StorageUseInput],
    pub access: PartAccess,
    pub limits: CallLimits,
}

/// One call of a profile job.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProfiledCall {
    pub repetition: u32,
    pub status: CallStatus,
    pub wall_ns: u64,
    /// User plus system CPU of the whole process during the call, and of the calling thread alone.
    pub process_cpu_ns: u64,
    pub caller_cpu_ns: u64,
    pub peak_anon_bytes: Option<u64>,
    pub read_bytes: Option<u64>,
    pub threads_spawned: u64,
    pub threads_joined: u64,
}

/// The call the watchdog stopped (or the child failure).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProfileStop {
    pub reason: UnfinishedReason,
    pub repetition: Option<u32>,
    pub elapsed_ns: Option<u64>,
    pub peak_anon_bytes: Option<u64>,
}

/// One function's self samples in the profiled call.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionSamples {
    pub function: String,
    /// The object's file name (`libgendb_engine.so`, `libc.so.6`, ...).
    pub object: String,
    pub self_samples: u64,
    /// Share of the call's samples, in permille (floored).
    pub self_permille: u64,
}

/// The profile of one statement at one worker count.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StatementProfile {
    /// The statement's name (template or variant id), its template and binding.
    pub statement: String,
    pub template: String,
    pub binding: String,
    pub workers: usize,
    pub calls: Vec<ProfiledCall>,
    pub stopped: Option<ProfileStop>,
    /// The repetition whose samples are shown (the last call that ran), with its sample counts.
    pub sampled_call: Option<u32>,
    pub interval_us: u32,
    pub samples_taken: u64,
    pub samples_dropped: u64,
    pub samples_unmapped: u64,
    /// Every sampled function, most samples first.
    pub functions: Vec<FunctionSamples>,
    pub method: String,
    pub evidence: PathBuf,
}

/// Profile `statement` at `workers` workers in one fresh child under `work` (see the module notes). An answer is not
/// compared (a profile is a diagnostic), so it is stored bounded; a refused child is the runner's error.
pub fn profile_statement(subject: &ProfileSubject<'_>, statement: &EngineStatement, workers: usize, work: &Path) -> Result<StatementProfile, AdmissionError> {
    let request = WorkerRequest::for_engine_query(subject.library, subject.uses.to_vec(), subject.access, std::slice::from_ref(&statement.ast), vec![workers as u32], PROFILE_REPETITIONS, RANGE_CAPACITY)
        .with_call_limits(subject.limits)
        .with_sampling(SamplingRequest { interval_us: PROFILE_SAMPLE_INTERVAL_US })
        .with_answer_bound(AnswerBound::STORED);
    let result = subject.runner.run(work, &request, None)?;
    let stopped = result.unfinished.as_ref().map(|u| {
        let call = u.stopped();
        ProfileStop { reason: u.reason(), repetition: call.map(|c| c.repetition), elapsed_ns: call.map(|c| c.elapsed_ns), peak_anon_bytes: call.and_then(|c| c.peak_anon_bytes) }
    });
    let (sampled_call, samples) = match result.unfinished.as_ref().and_then(Unfinished::stopped) {
        Some(call) => (Some(call.repetition), call.samples.clone()),
        None => result.observations.last().map_or((None, None), |o| (Some(o.repetition), o.samples.clone())),
    };
    let samples = samples.unwrap_or_default();
    Ok(StatementProfile {
        statement: statement.name().to_string(),
        template: statement.template.clone(),
        binding: statement.binding.clone(),
        workers,
        calls: result.observations.iter().map(profiled_call).collect(),
        stopped,
        sampled_call,
        interval_us: PROFILE_SAMPLE_INTERVAL_US,
        samples_taken: samples.taken,
        samples_dropped: samples.dropped,
        samples_unmapped: samples.unmapped,
        functions: self_samples(subject.library, &subject.runner.worker, &samples),
        method: PROFILE_METHOD.to_string(),
        evidence: work.to_path_buf(),
    })
}

/// Profile every statement of `statements` (the official statements) at the worker count of its largest gap in
/// `score`, each child under one `lease()` and under `work/<statement>/w<workers>`.
pub fn profile_version<Lease>(
    subject: &ProfileSubject<'_>,
    score: &ScaleScore,
    statements: &[EngineStatement],
    work: &Path,
    lease: impl Fn() -> Result<Lease, String>,
) -> Result<Vec<StatementProfile>, AdmissionError> {
    let mut profiles = Vec::with_capacity(statements.len());
    for statement in statements {
        let workers = score
            .largest_gap_workers(&statement.template)
            .ok_or_else(|| AdmissionError::tool(format!("the score has no cell of {}", statement.template)))?;
        let _lease = lease().map_err(AdmissionError::tool)?;
        profiles.push(profile_statement(subject, statement, workers, &work.join(statement.name()).join(format!("w{workers}")))?);
    }
    Ok(profiles)
}

fn profiled_call(o: &CallObservation) -> ProfiledCall {
    let usage = &o.outcome.usage;
    ProfiledCall {
        repetition: o.repetition,
        status: o.outcome.status,
        wall_ns: usage.wall_ns,
        process_cpu_ns: usage.process_user_ns.saturating_add(usage.process_system_ns),
        caller_cpu_ns: usage.caller_cpu_ns,
        peak_anon_bytes: o.peak_anon_bytes,
        read_bytes: o.process_io.map(|io| io.read_bytes),
        threads_spawned: o.outcome.dispatch.spawned,
        threads_joined: o.outcome.dispatch.joined,
    }
}

/// The self samples of every function in `samples`, most first: each object's addresses placed in its symbol table
/// (the engine library's names without the engine crate prefix); the worker executable `worker`, an object without a
/// readable symbol table, and an object's addresses no symbol covers each form one group per object.
pub fn self_samples(library: &Path, worker: &Path, samples: &CallSamples) -> Vec<FunctionSamples> {
    let same_file = |a: &Path, b: &Path| a == b || matches!((a.canonicalize(), b.canonicalize()), (Ok(x), Ok(y)) if x == y);
    let mut counts: BTreeMap<(String, String), u64> = BTreeMap::new();
    for object in &samples.objects {
        let path = Path::new(&object.path);
        let label = path.file_name().map_or_else(|| object.path.clone(), |n| n.to_string_lossy().into_owned());
        let table = (!same_file(path, worker)).then(|| SymbolTable::read(path).ok()).flatten();
        let engine = same_file(path, library);
        for &(address, count) in &object.addresses {
            let function = match table.as_ref().and_then(|t| t.function_at(address)) {
                Some(name) if engine => demangle(name).replace(&format!("{ENGINE_CRATE_NAME}::"), ""),
                Some(name) => demangle(name),
                None if table.is_some() => format!("[{label}: no symbol]"),
                None => format!("[{label}]"),
            };
            *counts.entry((function, label.clone())).or_default() += count;
        }
    }
    let total = samples.taken.max(1);
    let mut functions: Vec<FunctionSamples> = counts
        .into_iter()
        .map(|((function, object), self_samples)| FunctionSamples { function, object, self_samples, self_permille: self_samples * 1000 / total })
        .collect();
    functions.sort_by(|a, b| b.self_samples.cmp(&a.self_samples).then_with(|| a.function.cmp(&b.function)));
    functions
}

/// The function symbols of one ELF file: `(start, end, name)` in address order. A symbol without a size ends where the
/// next one starts.
struct SymbolTable {
    functions: Vec<(u64, u64, String)>,
}

impl SymbolTable {
    fn read(path: &Path) -> Result<Self, String> {
        // Read on demand (the symbol and string tables only), not the whole file.
        let data = object::ReadCache::new(std::fs::File::open(path).map_err(|e| format!("{}: {e}", path.display()))?);
        let file = object::File::parse(&data).map_err(|e| format!("{}: {e}", path.display()))?;
        let mut symbols: Vec<(u64, u64, String)> = file
            .symbols()
            .chain(file.dynamic_symbols())
            .filter(|s| s.kind() == SymbolKind::Text && s.address() != 0)
            .filter_map(|s| Some((s.address(), s.size(), s.name().ok()?.to_string())))
            .collect();
        symbols.sort_by(|a, b| a.0.cmp(&b.0).then(b.1.cmp(&a.1)));
        symbols.dedup_by_key(|s| s.0);
        let starts: Vec<u64> = symbols.iter().map(|s| s.0).collect();
        let functions = symbols
            .into_iter()
            .enumerate()
            .map(|(i, (start, size, name))| {
                let end = if size > 0 { start + size } else { starts.get(i + 1).copied().unwrap_or(start + 1) };
                (start, end, name)
            })
            .collect();
        Ok(Self { functions })
    }

    /// The function containing `address`.
    fn function_at(&self, address: u64) -> Option<&str> {
        let i = self.functions.partition_point(|f| f.0 <= address).checked_sub(1)?;
        let (start, end, name) = &self.functions[i];
        (*start..*end).contains(&address).then_some(name.as_str())
    }
}

/// `PROFILE.md` for `profiles` under the heading `title` (the version's name).
pub fn render_profile_md(title: &str, profiles: &[StatementProfile]) -> String {
    let mut md = format!("# Profile of {title}\n\nMethod: {PROFILE_METHOD}.\n\n");
    for p in profiles {
        let _ = writeln!(md, "## {} at {} workers (binding {})\n", p.statement, p.workers, p.binding);
        match &p.stopped {
            Some(stop) => {
                let _ = writeln!(
                    md,
                    "Did not finish: {} in call {} after {} (peak anonymous memory {}).\n",
                    reason_text(stop.reason),
                    stop.repetition.map_or_else(|| "unknown".to_string(), |r| r.to_string()),
                    stop.elapsed_ns.map_or_else(|| "an unknown time".to_string(), duration),
                    stop.peak_anon_bytes.map_or_else(|| "unknown".to_string(), bytes),
                );
            }
            None => md.push_str("Finished every call.\n\n"),
        }
        if !p.calls.is_empty() {
            md.push_str("| call | status | wall | process CPU | calling-thread CPU | peak anonymous memory | read bytes | threads spawned |\n|---|---|---|---|---|---|---|---|\n");
            for c in &p.calls {
                let _ = writeln!(
                    md,
                    "| {}{} | {:?} | {} | {} | {} | {} | {} | {} |",
                    c.repetition,
                    if c.repetition == 0 { " (warm)" } else { "" },
                    c.status,
                    duration(c.wall_ns),
                    duration(c.process_cpu_ns),
                    duration(c.caller_cpu_ns),
                    c.peak_anon_bytes.map_or_else(|| "-".to_string(), bytes),
                    c.read_bytes.map_or_else(|| "-".to_string(), bytes),
                    c.threads_spawned,
                );
            }
            md.push('\n');
        }
        let Some(call) = p.sampled_call else {
            md.push_str("No call ran, so nothing was sampled.\n\n");
            continue;
        };
        let _ = writeln!(
            md,
            "Hot functions of call {call} by self samples ({} samples; timer interval {} us of process CPU, checked by the kernel at its tick, so samples can be further apart; {} dropped, {} outside any object):\n",
            p.samples_taken, p.interval_us, p.samples_dropped, p.samples_unmapped
        );
        md.push_str("| function | object | self samples | share |\n|---|---|---|---|\n");
        for f in p.functions.iter().take(LISTED_FUNCTIONS) {
            let _ = writeln!(md, "| `{}` | {} | {} | {}.{}% |", f.function, f.object, f.self_samples, f.self_permille / 10, f.self_permille % 10);
        }
        let rest: Vec<&FunctionSamples> = p.functions.iter().skip(LISTED_FUNCTIONS).collect();
        if !rest.is_empty() {
            let samples: u64 = rest.iter().map(|f| f.self_samples).sum();
            let permille = samples * 1000 / p.samples_taken.max(1);
            let _ = writeln!(md, "| {} other functions | | {samples} | {}.{}% |", rest.len(), permille / 10, permille % 10);
        }
        md.push('\n');
    }
    md
}

/// Write `PROFILE.md` (headed `# Profile of <title>`: pass the subject only, such as `v003 at sf1`) and one
/// `profile/<statement>-w<workers>.json` per profile under `dir`.
pub fn write_profile(dir: &Path, title: &str, profiles: &[StatementProfile]) -> std::io::Result<()> {
    let records = dir.join(PROFILE_DIRECTORY);
    std::fs::create_dir_all(&records)?;
    for p in profiles {
        let json = serde_json::to_vec_pretty(p).map_err(std::io::Error::other)?;
        std::fs::write(records.join(format!("{}-w{}.json", p.statement, p.workers)), json)?;
    }
    std::fs::write(dir.join(PROFILE_FILE), render_profile_md(title, profiles))
}

fn reason_text(reason: UnfinishedReason) -> &'static str {
    match reason {
        UnfinishedReason::OverTimeLimit => "stopped at the call time limit",
        UnfinishedReason::OverMemoryLimit => "stopped at the anonymous-memory limit",
        UnfinishedReason::ChildFailure => "the child process failed",
    }
}

/// Nanoseconds as milliseconds (below 10 s) or seconds, three decimals.
fn duration(ns: u64) -> String {
    match ns < 10_000_000_000 {
        true => format!("{}.{:03} ms", ns / 1_000_000, ns / 1000 % 1000),
        false => format!("{}.{:03} s", ns / 1_000_000_000, ns / 1_000_000 % 1000),
    }
}

/// Bytes in MiB with one decimal.
fn bytes(b: u64) -> String {
    format!("{}.{} MiB", b >> 20, (b & ((1 << 20) - 1)) * 10 >> 20)
}

#[cfg(test)]
mod tests {
    use super::*;
    use gendb_runtime::worker::SampledObject;

    /// The symbols of this test executable: a sampled address inside a known function is placed there; the worker
    /// executable is one group; an unreadable object is one group.
    #[test]
    fn addresses_are_placed_in_their_functions() {
        let exe = std::env::current_exe().unwrap();
        let table = SymbolTable::read(&exe).unwrap();
        let (start, _, name) = table.functions.iter().find(|f| demangle(&f.2).ends_with("engine::profile::render_profile_md")).expect("render_profile_md is a function of this executable").clone();
        assert_eq!(table.function_at(start).map(demangle), Some(demangle(&name)));
        let samples = CallSamples {
            interval_us: 1000,
            taken: 10,
            dropped: 0,
            unmapped: 0,
            objects: vec![
                SampledObject { path: exe.to_string_lossy().into_owned(), addresses: vec![(start, 6)] },
                SampledObject { path: "/nonexistent/libother.so".into(), addresses: vec![(16, 4)] },
            ],
        };
        let functions = self_samples(Path::new("/nonexistent/engine.so"), Path::new("/nonexistent/gendb"), &samples);
        assert_eq!(functions[0].self_samples, 6);
        assert!(functions[0].function.ends_with("engine::profile::render_profile_md"), "{functions:?}");
        assert_eq!(functions[0].self_permille, 600);
        assert_eq!((functions[1].function.as_str(), functions[1].object.as_str(), functions[1].self_samples), ("[libother.so]", "libother.so", 4));
        let as_worker = self_samples(Path::new("/nonexistent/engine.so"), &exe, &samples);
        assert!(as_worker[0].function.starts_with('['), "the worker executable is one group: {as_worker:?}");
        let as_engine = self_samples(&exe, Path::new("/nonexistent/gendb"), &samples);
        assert!(as_engine[0].function.contains("engine::profile::render_profile_md"), "{as_engine:?}");
        assert!(!as_engine[0].function.contains(&format!("{ENGINE_CRATE_NAME}::")));
    }

    #[test]
    fn profile_markdown_lists_calls_and_functions() {
        let profile = StatementProfile {
            statement: "Q01".into(),
            template: "Q01".into(),
            binding: "v0".into(),
            workers: 32,
            calls: vec![ProfiledCall { repetition: 0, status: CallStatus::Ok, wall_ns: 1_500_000, process_cpu_ns: 3_000_000, caller_cpu_ns: 1_000_000, peak_anon_bytes: Some(3 << 20), read_bytes: Some(0), threads_spawned: 32, threads_joined: 32 }],
            stopped: Some(ProfileStop { reason: UnfinishedReason::OverTimeLimit, repetition: Some(1), elapsed_ns: Some(60_000_000_000), peak_anon_bytes: Some(5 << 30) }),
            sampled_call: Some(1),
            interval_us: 1000,
            samples_taken: 200,
            samples_dropped: 0,
            samples_unmapped: 0,
            functions: vec![FunctionSamples { function: "exec::relational::ops::product_rows_exec".into(), object: "libgendb_engine.so".into(), self_samples: 150, self_permille: 750 }],
            method: PROFILE_METHOD.into(),
            evidence: PathBuf::from("work"),
        };
        let md = render_profile_md("v000", &[profile]);
        assert!(md.contains("## Q01 at 32 workers (binding v0)"), "{md}");
        assert!(md.contains("Did not finish: stopped at the call time limit in call 1 after 60.000 s (peak anonymous memory 5120.0 MiB)"), "{md}");
        assert!(md.contains("| 0 (warm) | Ok | 1.500 ms | 3.000 ms | 1.000 ms | 3.0 MiB | 0.0 MiB | 32 |"), "{md}");
        assert!(md.contains("| `exec::relational::ops::product_rows_exec` | libgendb_engine.so | 150 | 75.0% |"), "{md}");
    }
}
