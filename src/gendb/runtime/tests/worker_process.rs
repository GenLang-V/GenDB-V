//! The worker child process through its real entry: this test executable doubles as the worker
//! (`<this test> worker REQUEST RESULT`, exactly the `gendb worker` contract, `worker::worker_main`).
//!
//! Always run: refusals the worker makes before opening anything (another build's identity, including the form of the earlier GenDB version;
//! saved ABI v1/v2 requests; a request breaking the rules; a usage error).
//!
//! Saved replay (tiny inputs and saved SF1 records; set `GENDB_RUNTIME_SAVED_CHECK=<config.json>`; saved files are only
//! read, every write goes to the config's `scratch`):
//! - `tiny_cases`: a saved tiny build request (inline columns) and its query request, copied with this build's
//!   identity and a fresh parts directory, run through the worker: build outcome, parts manifest and part bytes, and
//!   every query observation (without usage) equal the saved ones; then controls: worker counts 0 and 65
//!   (`AbiRefused`), optional refused bindings (outside the domain, wrong argument kind or count: `ParamRefused`,
//!   decided by the verified entry), and a first value outside `numeric(15, 2)`
//!   (`InvalidInput`, no parts);
//! - `tables_input`: the same case's values written as a prepared archive table (declared fields at their original
//!   ordinals) and delivered through `WorkerInput::Tables`: the built parts equal the saved ones byte for byte;
//! - `saved_calls`: a copied saved query call (the saved request with this build's identity): the observations
//!   (without usage) equal the saved result's;
//! - `serving`: a statement translated from its saved SQL, schema and parameter declaration, served from a copy of
//!   its saved library through `serve::serve` over the saved prepared capture at every saved binding and worker
//!   count: each record (without wall time) equals the saved serving record, host refusals equal the saved refusal
//!   texts and run no worker, another free domain has no package, and serving writes no object.
//!
//! Config: `{"scratch", "report", "tiny_cases": [{"name", "library", "case", "refused_bindings"?}],
//!   "tables_input": {"library", "case", "table", "fields": [[ordinal, ColumnSpec]...]}?,
//!   "saved_calls": [{"name", "request", "result"}], "serving": [{"name", "library", "prepared_root", "dataset",
//!   "preflight", "cases": [{"arguments", "workers", "expected"?, "refused"?}], "other_domain": [ParamRequest]?}]}`.

use gendb_artifacts::ObjectStore;
use gendb_artifacts::{ColType, ColumnSpec};
use gendb_frontend::ast::Translation;
use gendb_frontend::params::{Instance, ParamRequest, declare, instantiate};
use gendb_frontend::parser::SqlParser;
use gendb_runtime::abi::{CallStatus, StatementArgument};
use gendb_runtime::identity::WorkerBuildIdentity;
use gendb_runtime::serve::{ServeError, WorkerExecutor, serve};
use gendb_storage::io::PartAccess;
use gendb_storage::versions::CurrentCapture;
use gendb_runtime::worker::{
    ChildFailure, InlineColumn, InlineElem, TableColumns, WORKER_SUBCOMMAND, WorkerError, WorkerInput, WorkerJob,
    WorkerRequest, WorkerResult, spawn, worker_main,
};
use gendb_storage::import::{DatasetSpec, PreparedSource};
use gendb_storage::io::{ProjectedTable, SourceColumns};
use serde_json::{Value, json};
use std::ffi::OsString;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

const TIMEOUT_SECONDS: u64 = 600;
const RANGE_CAPACITY: u64 = 64;

fn main() -> ExitCode {
    let arguments: Vec<OsString> = std::env::args_os().collect();
    if arguments.get(1).is_some_and(|word| word == WORKER_SUBCOMMAND) {
        return worker_main(&arguments[2..]);
    }
    let mut failed = 0;
    failed += check("refusals_before_opening", refusals_before_opening);
    match std::env::var_os("GENDB_RUNTIME_SAVED_CHECK") {
        Some(config) => failed += check("saved_replay", || saved_replay(Path::new(&config))),
        None => println!("saved_replay: skipped (set GENDB_RUNTIME_SAVED_CHECK)"),
    }
    if failed == 0 { ExitCode::SUCCESS } else { ExitCode::FAILURE }
}

fn check(name: &str, body: impl FnOnce()) -> usize {
    match catch_unwind(AssertUnwindSafe(body)) {
        Ok(()) => {
            println!("{name}: ok");
            0
        }
        Err(_) => {
            println!("{name}: FAILED");
            1
        }
    }
}

fn worker() -> PathBuf {
    std::env::current_exe().unwrap()
}

fn scratch(name: &str) -> PathBuf {
    let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let path = std::env::temp_dir().join(format!("gendb-runtime-{name}-{}-{nanos}", std::process::id()));
    std::fs::create_dir_all(&path).unwrap();
    path
}

fn read_json(path: &Path) -> Value {
    serde_json::from_slice(&std::fs::read(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))).unwrap()
}

/// Run a raw request file through the worker executable: (exit code, stderr, result file written).
fn run_raw(work: &Path, request: &Value) -> (Option<i32>, String, bool) {
    std::fs::create_dir_all(work).unwrap();
    let (request_path, result_path) = (work.join("request.json"), work.join("result.json"));
    std::fs::write(&request_path, serde_json::to_vec(request).unwrap()).unwrap();
    let output = std::process::Command::new(worker())
        .arg(WORKER_SUBCOMMAND)
        .arg(&request_path)
        .arg(&result_path)
        .output()
        .unwrap();
    (output.status.code(), String::from_utf8_lossy(&output.stderr).into_owned(), result_path.exists())
}

// ---------------------------------------------------------------------------------------------------------------
// Refusals before anything is opened (no library exists at the requested path).

fn refusals_before_opening() {
    let work = scratch("refusals");
    let missing = work.join("no-library.so");
    let query = WorkerRequest::for_query(&missing, None, vec![vec![]], vec![1], 1, RANGE_CAPACITY);
    let refused = |name: &str, request: Value, expected: &str| {
        let (code, stderr, result) = run_raw(&work.join(name), &request);
        assert_eq!((code, result), (Some(1), false), "{name}: {stderr}");
        assert!(stderr.contains(expected), "{name}: {stderr}");
        assert!(!stderr.contains("dlopen"), "{name}: refused before the library: {stderr}");
    };
    let mut stale = serde_json::to_value(&query).unwrap();
    stale["build"] = json!({"runtime": "gendb-runtime/0.1.0+sha256:stale"});
    refused("stale", stale, "worker build differs");
    let mut legacy = serde_json::to_value(&query).unwrap();
    legacy["build"] =
        json!({"registry": "r", "gate": "g", "runtime": WorkerBuildIdentity::current().runtime, "compiler": "c"});
    refused("legacy-build", legacy, "worker build differs");
    let mut v2 = serde_json::to_value(&query).unwrap();
    v2["abi"] = json!("v2");
    refused("abi-v2", v2, "earlier GenDB version");
    let mut v1 = serde_json::to_value(&query).unwrap();
    v1.as_object_mut().unwrap().remove("abi");
    refused("abi-v1", v1, "earlier GenDB version");
    let two_counts = WorkerRequest {
        workers: vec![1, 2],
        ..WorkerRequest::for_build(&missing, WorkerInput::None, &work.join("parts"), 1, RANGE_CAPACITY)
    };
    refused("build-shape", serde_json::to_value(&two_counts).unwrap(), "runs once at one worker count");
    // The parent side reports the same refusal as a child failure with its exit status and stderr.
    match spawn(&worker(), &work.join("spawned"), &two_counts, TIMEOUT_SECONDS) {
        Err(WorkerError::ChildFailed(ChildFailure { exit_code: Some(1), stderr, .. })) => {
            assert!(stderr.contains("runs once"))
        }
        other => panic!("{other:?}"),
    }
    // Usage error.
    let output = std::process::Command::new(worker()).arg(WORKER_SUBCOMMAND).arg("only-one").output().unwrap();
    assert_eq!(output.status.code(), Some(2));
}

// ---------------------------------------------------------------------------------------------------------------
// Saved replay.

fn saved_replay(config_path: &Path) {
    let config = read_json(config_path);
    let scratch = PathBuf::from(config["scratch"].as_str().unwrap()).join(format!("run-{}", std::process::id()));
    let mut report = json!({"worker_build": WorkerBuildIdentity::current(), "scratch": scratch});
    for case in config["tiny_cases"].as_array().into_iter().flatten() {
        let name = case["name"].as_str().unwrap();
        report["tiny_cases"][name] = replay_tiny_case(case, &scratch.join("tiny").join(name));
    }
    if let Some(tables) = config.get("tables_input") {
        report["tables_input"] = replay_tables_input(tables, &scratch.join("tables-input"));
    }
    for call in config["saved_calls"].as_array().into_iter().flatten() {
        let name = call["name"].as_str().unwrap();
        report["saved_calls"][name] = replay_saved_call(call, &scratch.join("calls").join(name));
    }
    for statement in config["serving"].as_array().into_iter().flatten() {
        let name = statement["name"].as_str().unwrap();
        report["serving"][name] = replay_serving(statement, &scratch.join("serving").join(name));
    }
    std::fs::write(config["report"].as_str().unwrap(), serde_json::to_vec_pretty(&report).unwrap()).unwrap();
}

/// A saved request with this build's identity (the only change besides the named directory rewrites).
fn with_current_build(mut request: Value) -> Value {
    request["build"] = serde_json::to_value(WorkerBuildIdentity::current()).unwrap();
    request
}

fn without_usage(outcome: &Value) -> Value {
    let mut outcome = outcome.clone();
    outcome.as_object_mut().unwrap().remove("usage");
    outcome
}

/// Observations of a run without descriptive usage, for comparison with a saved run.
fn comparable(result: &Value) -> Vec<Value> {
    result["observations"]
        .as_array()
        .unwrap()
        .iter()
        .map(|observation| {
            let mut observation = observation.clone();
            observation["outcome"] = without_usage(&observation["outcome"]);
            observation
        })
        .collect()
}

fn run(work: &Path, request: &Value) -> WorkerResult {
    let request: WorkerRequest = serde_json::from_value(request.clone()).unwrap();
    spawn(&worker(), work, &request, TIMEOUT_SECONDS).unwrap_or_else(|e| panic!("{}: {e}", work.display()))
}

fn assert_parts_equal(stored: &Path, saved: &Path) {
    let manifest = read_json(&saved.join("parts.json"));
    assert_eq!(read_json(&stored.join("parts.json")), manifest);
    for index in 0..manifest["parts"].as_array().unwrap().len() {
        let file = format!("part-{index:04}.bin");
        assert_eq!(std::fs::read(stored.join(&file)).unwrap(), std::fs::read(saved.join(&file)).unwrap(), "{file}");
    }
}

fn replay_tiny_case(case: &Value, work: &Path) -> Value {
    let library = case["library"].as_str().unwrap();
    let saved = Path::new(case["case"].as_str().unwrap());
    let parts = work.join("parts");

    let mut build = with_current_build(read_json(&saved.join("build/verus-run.request.json")));
    build["library"] = json!(library);
    build["job"]["build"]["output_directory"] = json!(parts);
    let built = serde_json::to_value(run(&work.join("build"), &build)).unwrap();
    let saved_build = read_json(&saved.join("build/verus-run.result.json"));
    assert_eq!(comparable(&built), comparable(&saved_build), "build {}", saved.display());
    assert_eq!(built["parts"], saved_build["parts"]);
    assert_parts_equal(&parts, &saved.join("parts"));

    let mut query = with_current_build(read_json(&saved.join("query/verus-run.request.json")));
    query["library"] = json!(library);
    query["job"]["query"]["parts_directory"] = json!(parts);
    let queried = serde_json::to_value(run(&work.join("query"), &query)).unwrap();
    let saved_query = read_json(&saved.join("query/verus-run.result.json"));
    assert_eq!(comparable(&queried), comparable(&saved_query), "query {}", saved.display());
    assert_eq!(queried["bindings"], saved_query["bindings"], "arguments echoed");

    let first_binding: Vec<StatementArgument> = serde_json::from_value(query["bindings"][0].clone()).unwrap();
    let controls = |bindings: Vec<Vec<StatementArgument>>, workers: Vec<u32>| {
        WorkerRequest::for_query(Path::new(library), Some(&parts), bindings, workers, 1, RANGE_CAPACITY)
    };
    let statuses = |result: &WorkerResult| -> Vec<(CallStatus, bool)> {
        result.observations.iter().map(|o| (o.outcome.status, o.outcome.result_wire.is_none())).collect()
    };
    let bad_workers =
        spawn(&worker(), &work.join("workers-0-65"), &controls(vec![first_binding], vec![0, 65]), TIMEOUT_SECONDS)
            .unwrap();
    assert_eq!(statuses(&bad_workers), [(CallStatus::AbiRefused, true); 2]);
    let mut report = json!({"build": built["observations"][0]["outcome"]["status"], "parts": built["parts"],
        "query_calls": queried["observations"].as_array().unwrap().len(), "workers_0_65": "abi_refused"});
    if let Some(bindings) = case.get("refused_bindings") {
        let bindings: Vec<Vec<StatementArgument>> = serde_json::from_value(bindings.clone()).unwrap();
        let count = bindings.len();
        let refused =
            spawn(&worker(), &work.join("refused-bindings"), &controls(bindings, vec![1]), TIMEOUT_SECONDS).unwrap();
        assert_eq!(statuses(&refused), vec![(CallStatus::ParamRefused, true); count]);
        report["refused_bindings"] = json!(format!("{count} x param_refused"));
    }
    let mut out_of_domain = build.clone();
    out_of_domain["input"]["inline"]["columns"][0]["values"][0] = json!("100000000000000000000");
    out_of_domain["job"]["build"]["output_directory"] = json!(work.join("never"));
    let invalid = run(&work.join("invalid-build"), &out_of_domain);
    assert_eq!((invalid.observations[0].outcome.status, invalid.parts.is_none()), (CallStatus::InvalidInput, true));
    assert!(!work.join("never").exists());
    report["value_outside_numeric_15_2"] = json!("invalid_input");
    report
}

/// The tiny case's inline values as one declared table of a prepared archive, delivered as `Tables` input.
fn replay_tables_input(config: &Value, work: &Path) -> Value {
    use arrow::array::{ArrayRef, Date32Array, Decimal128Array, Int32Array, Int64Array, StringArray};
    use arrow::datatypes::{Field, Schema};
    use arrow::record_batch::RecordBatch;
    use std::sync::Arc;

    let saved = Path::new(config["case"].as_str().unwrap());
    let build = read_json(&saved.join("build/verus-run.request.json"));
    let inline: Vec<InlineColumn> = serde_json::from_value(build["input"]["inline"]["columns"].clone()).unwrap();
    let fields: Vec<(usize, ColumnSpec)> = serde_json::from_value(config["fields"].clone()).unwrap();
    assert_eq!(inline.len(), fields.len());
    let arrays: Vec<ArrayRef> = inline
        .iter()
        .zip(&fields)
        .map(|(column, (_, spec))| -> ArrayRef {
            let integers = || column.values.iter().map(|v| v.parse::<i128>().unwrap());
            match (column.elem, &spec.ty) {
                (InlineElem::I128, ColType::Decimal { p, s }) => Arc::new(
                    Decimal128Array::from(integers().collect::<Vec<_>>()).with_precision_and_scale(*p, *s).unwrap(),
                ),
                (InlineElem::I32, ColType::Date32) => {
                    Arc::new(Date32Array::from(integers().map(|v| v as i32).collect::<Vec<_>>()))
                }
                (InlineElem::I32, ColType::I32) => {
                    Arc::new(Int32Array::from(integers().map(|v| v as i32).collect::<Vec<_>>()))
                }
                (InlineElem::I64, ColType::I64) => {
                    Arc::new(Int64Array::from(integers().map(|v| v as i64).collect::<Vec<_>>()))
                }
                (InlineElem::Utf8, ColType::Utf8) => Arc::new(StringArray::from(column.values.clone())),
                other => panic!("inline column {other:?}"),
            }
        })
        .collect();
    let schema = Arc::new(Schema::new(
        fields
            .iter()
            .zip(&arrays)
            .map(|((_, spec), array)| Field::new(&spec.name, array.data_type().clone(), false))
            .collect::<Vec<_>>(),
    ));
    let table_name = config["table"].as_str().unwrap();
    let table = ProjectedTable {
        table: table_name.into(),
        original_indices: fields.iter().map(|(ordinal, _)| *ordinal).collect(),
        fields: fields.iter().map(|(_, spec)| spec.clone()).collect(),
        row_count: arrays[0].len(),
        batches: vec![RecordBatch::try_new(schema, arrays).unwrap()],
    };
    std::fs::create_dir_all(work).unwrap();
    let archive = work.join("archive");
    let captured = SourceColumns::from_projected(vec![table]).unwrap();
    captured.write_archive(&archive).unwrap();
    captured.write_and_map_column_files(&archive).unwrap();
    let input = WorkerInput::Tables {
        path: archive,
        tables: vec![TableColumns {
            table: table_name.into(),
            ordinals: fields.iter().map(|(ordinal, _)| *ordinal).collect(),
        }],
    };
    let workers = build["workers"][0].as_u64().unwrap() as u32;
    let parts = work.join("parts");
    let request = WorkerRequest::for_build(
        Path::new(config["library"].as_str().unwrap()),
        input,
        &parts,
        workers,
        RANGE_CAPACITY,
    );
    let result = spawn(&worker(), &work.join("build"), &request, TIMEOUT_SECONDS).unwrap();
    assert_eq!(result.observations[0].outcome.status, CallStatus::Ok);
    assert_parts_equal(&parts, &saved.join("parts"));
    json!({"column_rows": result.column_rows, "parts": result.parts, "equal_to_inline_build": true})
}

fn replay_saved_call(call: &Value, work: &Path) -> Value {
    let request = with_current_build(read_json(Path::new(call["request"].as_str().unwrap())));
    assert!(matches!(serde_json::from_value::<WorkerRequest>(request.clone()).unwrap().job, WorkerJob::Query { .. }));
    let result = serde_json::to_value(run(work, &request)).unwrap();
    let saved = read_json(Path::new(call["result"].as_str().unwrap()));
    assert_eq!(comparable(&result), comparable(&saved));
    json!({"observations": comparable(&result)})
}

/// The statement instance of saved preflight files: SQL, schema and parameter declaration, translated again.
fn saved_instance(preflight: &Path, requests: &[ParamRequest]) -> Instance {
    let placeholders: Vec<_> = requests.iter().map(ParamRequest::placeholder).collect();
    let parser = SqlParser::from_environment().unwrap();
    let (_, translation) = parser
        .translate(&preflight.join("schema.sql"), &preflight.join("query.sql"), "postgres", &placeholders)
        .unwrap();
    let Translation::Ok(document) = translation else { panic!("saved SQL refused: {translation:?}") };
    instantiate(&document, &declare(&document, requests).unwrap()).unwrap()
}

fn replay_serving(config: &Value, work: &Path) -> Value {
    let preflight = Path::new(config["preflight"].as_str().unwrap());
    let requests: Vec<ParamRequest> = serde_json::from_value(read_json(&preflight.join("parameters.json"))).unwrap();
    let instance = saved_instance(preflight, &requests);
    let dataset: DatasetSpec = serde_json::from_value(config["dataset"].clone()).unwrap();
    let source = PreparedSource::open(Path::new(config["prepared_root"].as_str().unwrap()), &dataset).unwrap();
    let current = CurrentCapture::of(&source).unwrap();
    let library = Path::new(config["library"].as_str().unwrap());
    let store = ObjectStore::open_existing(library).unwrap();
    let objects = || std::fs::read_dir(library.join("objects")).unwrap().count();
    let objects_before = objects();
    let executor = WorkerExecutor::new(&worker(), work, TIMEOUT_SECONDS, RANGE_CAPACITY, 1);
    let mut served = vec![];
    for case in config["cases"].as_array().unwrap() {
        let arguments: Vec<String> = serde_json::from_value(case["arguments"].clone()).unwrap();
        let workers = case["workers"].as_u64().unwrap() as u32;
        let calls_before = std::fs::read_dir(work).map_or(0, |d| d.count());
        match serve(&store, &instance, &arguments, &current, PartAccess::default(), &executor, workers) {
            Ok(answer) => {
                let mut record = answer.record().unwrap();
                record.as_object_mut().unwrap().remove("wall_ns");
                let expected = &case["expected"];
                assert_eq!(&record, expected, "{arguments:?} at {workers} workers");
                served.push(json!({"arguments": arguments, "workers": workers, "answer": record["answer"]}));
            }
            Err(error @ ServeError::Arguments(_)) => {
                assert_eq!(Some(error.to_string().as_str()), case["refused"].as_str(), "{arguments:?}");
                assert_eq!(
                    std::fs::read_dir(work).map_or(0, |d| d.count()),
                    calls_before,
                    "a host refusal runs no worker"
                );
                served.push(json!({"arguments": arguments, "workers": workers, "host_refused": error.to_string()}));
            }
            Err(error) => panic!("{arguments:?} at {workers} workers: {error}"),
        }
    }
    let mut report = json!({"served": served, "statement_free_parameters": instance.free.len()});
    if let Some(other) = config.get("other_domain") {
        let other: Vec<ParamRequest> = serde_json::from_value(other.clone()).unwrap();
        let other_instance = saved_instance(preflight, &other);
        let arguments: Vec<String> = serde_json::from_value(config["cases"][0]["arguments"].clone()).unwrap();
        match serve(&store, &other_instance, &arguments, &current, PartAccess::default(), &executor, 1) {
            Err(ServeError::NoPackage) => report["other_domain"] = json!("no admitted package"),
            other => panic!("another free domain must be another statement: {:?}", other.err()),
        }
    }
    assert_eq!(objects(), objects_before, "serving writes no object");
    report
}
