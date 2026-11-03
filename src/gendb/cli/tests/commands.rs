//! The `gendb` binary through its real command line: help and usage exit codes, `gendb sql translate` with the pinned
//! parser, a format 1 workload request of the earlier GenDB version refused by `gendb synthesize` before anything is written or any author is
//! inspected, `gendb author-tools mcp` failing on stderr only, `gendb exclude-storage` recording an exclusion a later
//! request honors, and `gendb worker` both refusing a saved request of the earlier GenDB version and
//! (with saved inputs) running a build and a query job as the child of `gendb_runtime::worker::spawn`.
//!
//! Scratch goes under Cargo's per-target temporary directory. The worker round trip runs only when
//! `GENDB_CLI_SAVED_WORKER_CASE` names a JSON file `{"library": <compiled candidate .so>, "case": <saved tiny case
//! directory with build/ and query/ verus-run request and result files>}`; saved files are only read.

use gendb_runtime::identity::WorkerBuildIdentity;
use gendb_runtime::worker::{WorkerRequest, spawn};
use serde_json::{Value, json};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const GENDB: &str = env!("CARGO_BIN_EXE_gendb");

fn gendb(arguments: &[&str]) -> Output {
    Command::new(GENDB).args(arguments).output().expect("gendb starts")
}

/// A fresh scratch directory for one test.
fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join("gendb-cli").join(name);
    if dir.exists() {
        std::fs::remove_dir_all(&dir).unwrap();
    }
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

#[test]
fn help_and_usage_exit_codes() {
    let help = gendb(&["--help"]);
    assert_eq!(help.status.code(), Some(0));
    let text = String::from_utf8(help.stdout).unwrap();
    for command in ["synthesize", "preflight", "serve", "sql", "worker", "author-tools", "exclude-storage", "import"] {
        assert!(text.contains(command), "{command} in {text}");
    }
    assert_eq!(gendb(&[]).status.code(), Some(2));
    assert_eq!(gendb(&["no-such-command"]).status.code(), Some(2));
    assert_eq!(gendb(&["sql", "--help"]).status.code(), Some(0));
    assert_eq!(gendb(&["sql"]).status.code(), Some(2));
    assert_eq!(gendb(&["sql", "translate", "--no-such-flag", "x"]).status.code(), Some(2));
    assert_eq!(gendb(&["sql", "check-library", "--out", "a", "--out", "b"]).status.code(), Some(2));
    assert_eq!(gendb(&["sql", "run", "--build", "b", "--fixture", "f"]).status.code(), Some(2), "--out is required");
    assert_eq!(gendb(&["worker"]).status.code(), Some(2));
    for route in ["synthesize", "preflight", "serve"] {
        assert_eq!(gendb(&[route, "request.json"]).status.code(), Some(2), "{route} needs REQUEST and RUN_DIR");
    }
    assert_eq!(gendb(&["author-tools", "check", "context", "evidence"]).status.code(), Some(2));
    assert_eq!(gendb(&["import", "request.json", "published"]).status.code(), Some(2), "import needs REQUEST, PUBLISHED_DIR and RUN_DIR");
}

/// The public exclusion route appends one library record per package; a later `physical_only` request over the same
/// library, with no request-level list, finds the package ineligible.
#[test]
fn exclude_storage_appends_once_and_later_physical_only_requests_refuse_the_package() {
    use gendb_artifacts::ObjectStore;
    use gendb_artifacts::verus::VERUS_STORAGE_PACKAGE_KIND;
    use gendb_synthesis::storage::policy::StoredDataPolicy;
    let library = scratch("exclude-storage").join("library");
    let package = ObjectStore::open(&library).unwrap().put(1, VERUS_STORAGE_PACKAGE_KIND, &json!({"name":"orders_by_customer"})).unwrap();
    let (lib, id) = (library.to_str().unwrap(), package.to_hex());
    let first = gendb(&["exclude-storage", lib, "physical_only", &id, "review: stores another table's row ranges"]);
    assert_eq!(first.status.code(), Some(0), "{}", String::from_utf8_lossy(&first.stderr));
    let first: Value = serde_json::from_slice(&first.stdout).unwrap();
    assert_eq!((first["recorded_now"].as_bool(), first["record"]["storage"].as_str()), (Some(true), Some("orders_by_customer")));
    let again: Value = serde_json::from_slice(&gendb(&["exclude-storage", lib, "physical_only", &id, "a second review"]).stdout).unwrap();
    assert_eq!((again["recorded_now"].as_bool(), &again["exclusion"]), (Some(false), &first["exclusion"]));
    assert_eq!(gendb(&["exclude-storage", lib, "unrestricted", &id, "reviewed"]).status.code(), Some(3), "only physical_only has exclusions");
    assert_eq!(gendb(&["exclude-storage", lib, "physical_only", "not-an-id", "reviewed"]).status.code(), Some(2));
    assert_eq!(gendb(&["exclude-storage", lib]).status.code(), Some(2));

    let later_request: StoredDataPolicy = serde_json::from_value(json!({"kind":"physical_only"})).unwrap();
    let store = ObjectStore::open_existing(&library).unwrap();
    let reason = later_request.ineligible(&store, package, "orders_by_customer").unwrap().unwrap();
    assert!(reason.starts_with("storage_policy_excluded") && reason.contains("another table's row ranges"), "{reason}");
    assert_eq!(StoredDataPolicy::Unrestricted.ineligible(&store, package, "orders_by_customer").unwrap(), None);
}

#[test]
fn synthesize_refuses_a_format_1_request_before_any_work() {
    let dir = scratch("format-one");
    std::fs::write(dir.join("request.json"), r#"{"format_version": 1, "authoring": "verus_rust", "queries": []}"#)
        .unwrap();
    let run = dir.join("run");
    let refused = gendb(&["synthesize", dir.join("request.json").to_str().unwrap(), run.to_str().unwrap()]);
    assert_eq!(refused.status.code(), Some(3));
    let stderr = String::from_utf8_lossy(&refused.stderr);
    assert!(stderr.contains("earlier GenDB version") && stderr.contains("authoring"), "{stderr}");
    assert!(refused.stdout.is_empty() && !run.exists(), "nothing is printed or written");
}

#[test]
fn author_tools_failure_keeps_stdout_for_the_protocol() {
    let dir = scratch("author-tools");
    let failed = gendb(&[
        "author-tools",
        "mcp",
        dir.join("absent.json").to_str().unwrap(),
        dir.join("evidence").to_str().unwrap(),
    ]);
    assert_eq!(failed.status.code(), Some(3));
    assert!(failed.stdout.is_empty(), "stdout carries only MCP messages");
    assert!(!String::from_utf8_lossy(&failed.stderr).is_empty());
}

#[test]
fn sql_translate_writes_the_ast_once() {
    let dir = scratch("translate");
    std::fs::write(dir.join("schema.sql"), "CREATE TABLE t (k integer PRIMARY KEY, v numeric(6,2));\n").unwrap();
    std::fs::write(dir.join("query.sql"), "SELECT sum(v) AS s FROM t WHERE k > 1").unwrap();
    let out = dir.join("out");
    let arguments = ["sql", "translate", "--schema", "schema.sql", "--sql", "query.sql", "--out", "out"];
    let translated = Command::new(GENDB).current_dir(&dir).args(arguments).output().unwrap();
    assert_eq!(translated.status.code(), Some(0), "{}", String::from_utf8_lossy(&translated.stderr));
    let record: Value = serde_json::from_slice(&translated.stdout).unwrap();
    assert_eq!(record["kind"], "gendb-sql-translate");
    assert_eq!(record["status"], "ok");
    assert_eq!(record["output"]["names"], json!(["s"]));
    assert_eq!(record["ast"], json!(out.join("ast.json")), "paths are absolute");
    assert!(out.join("ast.json").is_file() && out.join("translate.json").is_file());
    let again = Command::new(GENDB).current_dir(&dir).args(arguments).output().unwrap();
    assert_eq!(again.status.code(), Some(3), "records are written once");
}

#[test]
fn worker_refuses_a_saved_legacy_request() {
    let dir = scratch("worker-refusal");
    std::fs::write(dir.join("request.json"), r#"{"abi": "v2"}"#).unwrap();
    let result = dir.join("result.json");
    let refused = gendb(&["worker", dir.join("request.json").to_str().unwrap(), result.to_str().unwrap()]);
    assert_eq!(refused.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&refused.stderr).contains("earlier GenDB version"), "{}", String::from_utf8_lossy(&refused.stderr));
    assert!(!result.exists(), "a refusal writes no result");
}

#[test]
fn worker_runs_saved_tiny_case() {
    let Some(config) = std::env::var_os("GENDB_CLI_SAVED_WORKER_CASE") else {
        eprintln!("worker_runs_saved_tiny_case: GENDB_CLI_SAVED_WORKER_CASE not set; not run");
        return;
    };
    let config = read_json(Path::new(&config));
    let library = config["library"].as_str().unwrap();
    let saved = Path::new(config["case"].as_str().unwrap());
    let dir = scratch("worker-round-trip");
    let parts = dir.join("parts");

    let mut build = with_this_build(read_json(&saved.join("build/verus-run.request.json")));
    build["library"] = json!(library);
    build["job"]["build"]["output_directory"] = json!(parts);
    let built = run_worker(&dir.join("build"), build);
    assert_eq!(observations(&built), observations(&read_json(&saved.join("build/verus-run.result.json"))));
    assert_eq!(built["observations"][0]["outcome"]["status"], "ok");

    let mut query = with_this_build(read_json(&saved.join("query/verus-run.request.json")));
    query["library"] = json!(library);
    query["job"]["query"]["parts_directory"] = json!(parts);
    let queried = run_worker(&dir.join("query"), query);
    assert_eq!(observations(&queried), observations(&read_json(&saved.join("query/verus-run.result.json"))));
}

fn read_json(path: &Path) -> Value {
    serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap()
}

/// A saved request made current: the build identity of this build, which the `gendb` binary shares.
fn with_this_build(mut request: Value) -> Value {
    request["build"] = serde_json::to_value(WorkerBuildIdentity::current()).unwrap();
    request
}

/// Run `request` in a `gendb worker` child through the runtime's parent side.
fn run_worker(work: &Path, request: Value) -> Value {
    let request: WorkerRequest = serde_json::from_value(request).unwrap();
    let result = spawn(Path::new(GENDB), work, &request, 600).unwrap();
    serde_json::to_value(result).unwrap()
}

/// The observations without their descriptive usage (timings), for comparison with a saved run.
fn observations(result: &Value) -> Vec<Value> {
    let mut observations = result["observations"].as_array().unwrap().clone();
    for observation in &mut observations {
        observation["outcome"].as_object_mut().unwrap().remove("usage");
    }
    observations
}
