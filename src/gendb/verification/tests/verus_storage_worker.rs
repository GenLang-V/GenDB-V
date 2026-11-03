//! The ABI v4 runtime path end to end on the tiny storage fixture of `verus_storage_entry.rs` (`fixtures/verus_storage`,
//! read unchanged): the storage crate and the query crate are assembled by `obligations::{storage_crate_files,
//! query_crate_files}`, given their trusted shims by `with_trusted_shim` (`gendb_runtime::abi::GENDB_STORAGE_SHIM_SOURCE`
//! and `GENDB_QUERY_SHIM_V4_SOURCE`), verified and compiled by the pinned Verus (`--no-cheating`, whole crate), and
//! then run through the real worker child:
//! - a `StorageBuild` job over six inline sensor rows writes the five format-2 parts (zone map + columns);
//! - a `StorageQuery` job over that storage use answers `SELECT id, reading FROM sensor WHERE day < $1` exactly, and
//!   its verified request counters show the selective reader: the block minima plus one block's three column
//!   extents, fewer bytes than stored; the process I/O of the call is recorded;
//! - controls: an argument outside the declared date domain is `ParamRefused` by the verified entry; a use list whose
//!   length differs from the query's declared use count is refused by the shim before any verified code
//!   (`AbiRefused`); a parts directory missing a part file is refused by the host before the call.
//!
//! Needs the pinned frontend Python, the pinned Verus (`GENDB_VERUS_HOME`, default `<repository>/toolchains`) and the
//! `gendb` executable as the worker (`GENDB_WORKER`); run with `--ignored`.
use gendb_frontend::ast::{AstDocument, Translation};
use gendb_frontend::columns::{analyze, source_declaration};
use gendb_frontend::params::{declare, instantiate, Instance, ParamRequest};
use gendb_frontend::parser::SqlParser;
use gendb_runtime::abi::{CallStatus, StatementArgument, GENDB_QUERY_SHIM_V4_SOURCE, GENDB_STORAGE_SHIM_SOURCE};
use gendb_runtime::worker::{
    spawn, InlineColumn, InlineElem, StorageUseInput, WorkerError, WorkerInput, WorkerRequest, WorkerResult,
};
use gendb_storage::io::{PartAccess, ReadAdvice};
use gendb_verification::obligations::{
    query_crate_files, storage_crate_files, with_trusted_shim, DeclaredSource, StorageName, StorageUse, CANDIDATE_CRATE_NAME,
    STORAGE_CRATE_NAME,
};
use gendb_verification::verus::{
    freeze_framework_crate, run_verus, CodegenOptions, FrameworkSource, VerusMode, VerusOptions, VerusOutcome, VerusToolchain,
};
use serde_json::json;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

const INTERFACE: &str = include_str!("fixtures/verus_storage/interface.rs");
const BUILDER: &str = include_str!("fixtures/verus_storage/builder.rs");
const AGENT: &str = include_str!("fixtures/verus_storage/agent.rs");
const TIMEOUT_SECONDS: u64 = 600;
const RANGE_CAPACITY: u64 = 64;

fn fixtures() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

fn source(path: &str, text: &str) -> FrameworkSource {
    FrameworkSource { path: path.into(), text: text.into() }
}

fn translated() -> (AstDocument, Vec<ParamRequest>) {
    let dir = fixtures().join("verus_storage");
    let requests: Vec<ParamRequest> = serde_json::from_str(&std::fs::read_to_string(dir.join("params.json")).unwrap()).unwrap();
    let placeholders: Vec<_> = requests.iter().map(|r| r.placeholder()).collect();
    let parser = SqlParser::from_environment().unwrap();
    let (_, t) = parser.translate(&fixtures().join("verus_params/schema.sql"), &dir.join("query.sql"), "postgres", &placeholders).unwrap();
    let Translation::Ok(doc) = t else { panic!("fixture SQL refused: {t:?}") };
    (doc, requests)
}

/// The fixture's storage crate and query crate, each with its trusted shim (the files a host library is built from).
fn crates_with_shims() -> (Vec<FrameworkSource>, Vec<FrameworkSource>) {
    let (doc, requests) = translated();
    let inst: Instance = instantiate(&doc, &declare(&doc, &requests).unwrap()).unwrap();
    let name = StorageName::new("sensor_days").unwrap();
    // sensor is table 1: id, reading, day (ordinals 0, 2, 3).
    let declaration = DeclaredSource::for_storage(&doc.tables, &BTreeMap::from([(1, BTreeSet::from([0, 2, 3]))])).unwrap();
    let interface = vec![source("stores/sensor_days/interface/mod.rs", INTERFACE)];
    let mut storage = storage_crate_files(&doc.tables, &name, &declaration, false).unwrap();
    storage.extend(interface.iter().cloned());
    storage.push(source("builder/mod.rs", BUILDER));
    let delivered = source_declaration(&inst.doc, &analyze(&inst.doc).unwrap()).unwrap();
    let uses = [StorageUse { name: &name, declaration: &declaration, interface: &interface }];
    let mut query = query_crate_files(&inst, &delivered, &uses, "verus_storage fixture").unwrap();
    query.push(source("agent/mod.rs", AGENT));
    (with_trusted_shim(storage, GENDB_STORAGE_SHIM_SOURCE), with_trusted_shim(query, GENDB_QUERY_SHIM_V4_SOURCE))
}

/// Verify (whole crate, `--no-cheating`) and compile `files`; the compiled library and the verification summary.
fn compiled_library(toolchain: &VerusToolchain, work: &Path, crate_name: &str, files: &[FrameworkSource]) -> (PathBuf, serde_json::Value) {
    let author = |p: &str| p.starts_with("builder/") || p.starts_with("agent/") || p.contains("/interface/");
    let unscanned: Vec<&str> = files.iter().filter(|f| !author(&f.path)).map(|f| f.path.as_str()).collect();
    let frozen = freeze_framework_crate(files, &unscanned, &work.join("frozen")).unwrap_or_else(|e| panic!("{crate_name}: {e:?}"));
    let options =
        VerusOptions { crate_name: crate_name.into(), codegen: CodegenOptions { opt_level: 1, target_cpu: None }, num_threads: Some(8) };
    let run = run_verus(toolchain, &frozen, &options, VerusMode::VerifyAndCompile, &work.join("verus-build")).unwrap();
    assert_eq!(run.outcome, VerusOutcome::Compiled, "{crate_name}: {}", run.rendered_errors());
    let summary = run.verification.clone().unwrap();
    assert!(summary.is_verifying_entire_crate && summary.errors == 0, "{summary:?}");
    (run.artifact.expect("a compiled library"), serde_json::to_value(summary).unwrap())
}

fn date(y: i32, m: i32, d: i32) -> Vec<StatementArgument> {
    vec![StatementArgument::Date { y, m, d }]
}

#[test]
#[ignore = "runs the pinned Verus toolchain, frontend and the gendb worker; set GENDB_WORKER; -- --ignored"]
fn storage_build_and_query_run_through_the_worker() {
    let worker = PathBuf::from(std::env::var_os("GENDB_WORKER").expect("GENDB_WORKER: the gendb executable"));
    let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let work = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("verus-storage-worker-{}-{nanos}", std::process::id()));
    let toolchain = VerusToolchain::from_env().unwrap();
    let (storage_files, query_files) = crates_with_shims();
    let (storage_library, storage_verification) = compiled_library(&toolchain, &work.join("storage"), STORAGE_CRATE_NAME, &storage_files);
    let (query_library, query_verification) = compiled_library(&toolchain, &work.join("query"), CANDIDATE_CRATE_NAME, &query_files);

    // Six sensor rows (id, reading numeric(10,2) coefficient, day Date32): blocks of two rows start on 2000-01-01
    // (10957), 2001-06-25 (11498) and 2002-11-09 (12000).
    let column = |elem, values: &[i64]| InlineColumn { elem, values: values.iter().map(i64::to_string).collect(), validity: None };
    let input = WorkerInput::Inline {
        columns: vec![
            column(InlineElem::I32, &[1, 2, 3, 4, 5, 6]),
            column(InlineElem::I128, &[1234, -5, 700, 1, 2, 3]),
            column(InlineElem::I32, &[10957, 10958, 11498, 11499, 12000, 12001]),
        ],
    };
    let parts = work.join("asset");
    let build = WorkerRequest::for_storage_build(&storage_library, input, &parts, 1, RANGE_CAPACITY);
    let built = spawn(&worker, &work.join("build"), &build, TIMEOUT_SECONDS).unwrap();
    assert_eq!(built.observations[0].outcome.status, CallStatus::Ok);
    let manifest = built.parts.clone().expect("committed parts");
    // Zone map (3 + 3 i32), id (6 i32), reading (6 i128), day (6 i32).
    assert_eq!((manifest.format_version, manifest.storage_bytes), (2, 12 + 12 + 24 + 96 + 24));

    let uses = vec![StorageUseInput { name: "sensor_days".into(), parts_directory: parts.clone() }];
    let access = PartAccess { read_advice: ReadAdvice::Random, drop_cached_pages: false };
    // $1 = 2000-01-03: only the first block can hold a qualifying row; the second binding is outside the declared
    // domain 2000-01-01..=2030-12-31.
    let request = WorkerRequest::for_storage_query(
        &query_library,
        uses.clone(),
        access,
        vec![date(2000, 1, 3), date(1999, 12, 31)],
        vec![1, 2],
        1,
        RANGE_CAPACITY,
    );
    let queried = spawn(&worker, &work.join("query"), &request, TIMEOUT_SECONDS).unwrap();
    assert_eq!(queried.storage_uses.len(), 1);
    assert_eq!(queried.storage_uses[0].storage_bytes, manifest.storage_bytes);
    let mut report = vec![];
    for observation in &queried.observations {
        let outcome = &observation.outcome;
        match observation.binding {
            Some(0) => {
                assert_eq!(outcome.status, CallStatus::Ok);
                let mut rows = observation.rows.clone().unwrap();
                rows.sort_by_key(|row| row[0].as_i64());
                assert_eq!(rows, [vec![json!(1), json!("12.34")], vec![json!(2), json!("-0.05")]]);
                let counts = &outcome.storage_requests;
                assert_eq!(counts.len(), 1);
                // One request for the three block minima, then id, reading and day of block 0 (two rows each).
                assert_eq!((counts[0].use_index, counts[0].requests, counts[0].elements), (0, 4, 3 + 2 + 2 + 2));
                assert_eq!(counts[0].bytes, 3 * 4 + 2 * 4 + 2 * 16 + 2 * 4);
                assert!(counts[0].bytes < manifest.storage_bytes, "the selective reader requests less than stored");
                assert!(observation.process_io.is_some(), "process I/O recorded");
            }
            _ => assert_eq!((outcome.status, outcome.result_wire.is_none()), (CallStatus::ParamRefused, true)),
        }
        report.push(json!({"binding": observation.binding, "workers": observation.workers, "status": outcome.status,
            "rows": observation.rows, "requests": outcome.storage_requests, "process_io": observation.process_io}));
    }

    // Controls. A use list of another length than the query's declared use count: refused by the shim.
    let no_uses = WorkerRequest::for_storage_query(&query_library, vec![], access, vec![date(2000, 1, 3)], vec![1], 1, RANGE_CAPACITY);
    let refused = spawn(&worker, &work.join("no-uses"), &no_uses, TIMEOUT_SECONDS).unwrap();
    let outcome = &refused.observations[0].outcome;
    assert_eq!((outcome.status, outcome.storage_requests.is_empty()), (CallStatus::AbiRefused, true));
    // A parts directory without its part files: refused by the host mapping, before any call.
    let incomplete = work.join("incomplete-asset");
    std::fs::create_dir_all(&incomplete).unwrap();
    std::fs::copy(parts.join("parts.json"), incomplete.join("parts.json")).unwrap();
    let missing_part = WorkerRequest::for_storage_query(
        &query_library,
        vec![StorageUseInput { name: "sensor_days".into(), parts_directory: incomplete }],
        access,
        vec![date(2000, 1, 3)],
        vec![1],
        1,
        RANGE_CAPACITY,
    );
    match spawn(&worker, &work.join("missing-part"), &missing_part, TIMEOUT_SECONDS) {
        Err(WorkerError::ChildFailed(failure)) => assert!(failure.stderr.contains("part-0000.bin"), "{}", failure.stderr),
        other => panic!("a missing part file must be refused: {:?}", other.map(|r: WorkerResult| r.observations.len())),
    }
    let evidence = json!({"storage_library": storage_library, "storage_verification": storage_verification,
        "query_library": query_library, "query_verification": query_verification, "parts": manifest,
        "build": built.observations[0], "calls": report, "no_uses": outcome.status, "work": work});
    std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", work.join("evidence.json").display());
}
