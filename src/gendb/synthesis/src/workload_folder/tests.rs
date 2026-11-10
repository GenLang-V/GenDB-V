//! Unit tests of the workload-folder reader and request writer: schema and header round trips, both key forms, each
//! refusal, the golden requests (the published runs' requests, trimmed to 2 or 3 queries per workload, paths as
//! placeholders: `tests/fixtures/workload_folder/expected`), the input files and a 4-row Parquet footer check.

use super::data::{self, DataSize};
use super::requests::{self, Baselines, FlatStorages, RunContext, ScaleInputs};
use super::schema;
use super::settings::{DecimalText, Mode, Settings, StartFrom, Storage};
use super::{FolderError, WorkloadFolder, queries};
use crate::controller::request::{EngineEmphasis, MemberRole, WorkloadRequest};
use crate::query::host_locks::HostLocks;
use gendb_frontend::params::BindingRequest;
use gendb_verification::admission::dataset_ddl;
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/workload_folder")
}

/// A fresh scratch directory (unique per call: tests run in parallel).
fn scratch(name: &str) -> PathBuf {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("gendb-workload-folder-{name}-{}-{n}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// The fixture folder `name` with its `gendb.toml` and `overlay` on top.
fn folder(name: &str, overlay: Settings) -> WorkloadFolder {
    let root = fixtures().join(name);
    WorkloadFolder::read(&root, Settings::read(&root, None).unwrap().overlay(overlay)).unwrap()
}

fn ctx() -> RunContext {
    let locks = HostLocks { activity_lock: "/l/activity.lock".into(), build_lock: "/l/build.lock".into(), race_lock: "/l/race.lock".into() };
    RunContext { work: "/w".into(), host_locks: locks, author_executable: "claude".into() }
}

/// One placeholder source file per table.
fn locations(folder: &WorkloadFolder) -> BTreeMap<String, Vec<PathBuf>> {
    folder.schema.tables.iter().map(|t| (t.name.clone(), vec![PathBuf::from(format!("/d/{}.parquet", t.name))])).collect()
}

/// The fixture baselines `name`, copied to scratch with an (empty) answer file of every engine at every visible
/// binding of `folder` at `scale`.
fn baselines(name: &str, folder: &WorkloadFolder, scale: &str) -> Baselines {
    let dir = scratch(&format!("baselines-{name}-{scale}"));
    for file in std::fs::read_dir(fixtures().join("baselines").join(name)).unwrap() {
        let file = file.unwrap().path();
        std::fs::copy(&file, dir.join(file.file_name().unwrap())).unwrap();
    }
    let read = Baselines::read(&dir).unwrap();
    let visible = folder.visible_bindings(scale).unwrap();
    for (query, list) in visible["queries"].as_object().unwrap() {
        for binding in list.as_array().unwrap() {
            for engine in &read.engines {
                let file = read.answer_file(engine, query, binding["binding_id"].as_str().unwrap());
                std::fs::create_dir_all(file.parent().unwrap()).unwrap();
                std::fs::write(&file, r#"{"run":{"result":[]}}"#).unwrap();
            }
        }
    }
    read
}

fn scale(name: &str, folder: &WorkloadFolder, bytes: u64, capture: bool, baselines: Option<Baselines>) -> ScaleInputs {
    let data_size = DataSize { original_data_bytes: bytes, measure: "manifest_original_data_bytes", source: format!("/d/{name}/MANIFEST.json").into() };
    ScaleInputs { name: name.into(), locations: locations(folder), capture: capture.then(|| format!("/c/{name}").into()), data_size, baselines }
}

/// The golden comparison's normalization (as the fixture writer applies it to the published requests): path fields
/// and absolute paths `<path>`, barriers `<locks>`, descriptions and reviews `<text>`, the targets file at the start of
/// a provenance `<targets>`, and `{"free": {}}` for a free parameter without bounds.
fn normalize(value: &Value, key: &str) -> Value {
    const PATH_KEYS: [&str; 14] =
        ["author_executable", "library", "prepared_workload", "output_home", "path", "source_library", "original_data_record", "templates", "variants", "bindings", "targets", "request", "source", "run"];
    match value {
        _ if key == "barriers" => json!("<locks>"),
        Value::Object(map) => Value::Object(map.iter().filter(|(_, v)| !(key == "free" && v.is_null())).map(|(k, v)| (k.clone(), normalize(v, k))).collect()),
        Value::Array(items) => Value::Array(items.iter().map(|v| normalize(v, key)).collect()),
        Value::String(text) if key == "provenance" => json!(match text.split_once(' ') {
            Some((_, rest)) => format!("<targets> {rest}"),
            None => text.clone(),
        }),
        Value::String(_) if key == "description" || key == "review" => json!("<text>"),
        Value::String(text) if text.starts_with('/') || PATH_KEYS.contains(&key) => json!("<path>"),
        other => other.clone(),
    }
}

/// `generated` equals the expected request `file` up to the normalization; the first differing path is named.
fn assert_golden(generated: &WorkloadRequest, file: &str) {
    let expected: Value = serde_json::from_str(&std::fs::read_to_string(fixtures().join("expected").join(file)).unwrap()).unwrap();
    let generated = normalize(&serde_json::to_value(generated).unwrap(), "");
    if generated != expected {
        fn first_difference(a: &Value, b: &Value, at: String) -> String {
            match (a, b) {
                (Value::Object(x), Value::Object(y)) => {
                    for k in x.keys().chain(y.keys()) {
                        match (x.get(k), y.get(k)) {
                            (Some(p), Some(q)) if p != q => return first_difference(p, q, format!("{at}/{k}")),
                            (None, _) | (_, None) => return format!("{at}/{k}: only in {}", if x.contains_key(k) { "generated" } else { "expected" }),
                            _ => {}
                        }
                    }
                    at
                }
                (Value::Array(x), Value::Array(y)) if x.len() == y.len() => {
                    x.iter().zip(y).enumerate().find(|(_, (p, q))| p != q).map(|(i, (p, q))| first_difference(p, q, format!("{at}[{i}]"))).unwrap_or(at)
                }
                _ => format!("{at}: generated {a} expected {b}"),
            }
        }
        panic!("{file}: {}", first_difference(&generated, &expected, String::new()));
    }
}

fn settings() -> Settings {
    Settings::default()
}

// ---------------------------------------------------------------- schema.sql -----------------------------------------

/// The canonical schema reads and is written back unchanged by the DDL GenDB writes from a request; the same schema
/// with its keys inside CREATE TABLE reads into the same tables and the same ordered declaration list.
#[test]
fn schema_round_trip_and_both_key_forms() {
    let canonical = std::fs::read_to_string(fixtures().join("tpc-h/schema.sql")).unwrap();
    let parsed = schema::parse(&canonical).unwrap();
    assert_eq!(parsed.tables.len(), 8);
    assert_eq!(parsed.constraints.as_ref().unwrap().declarations.len(), 15);
    let (ddl, omitted) = dataset_ddl(&parsed.dataset(&BTreeMap::new()), parsed.constraints.as_ref());
    assert!(omitted.is_empty());
    assert_eq!(ddl, canonical, "the canonical form is the DDL GenDB writes");
    let inline = schema::parse(&std::fs::read_to_string(fixtures().join("tpc-h-inline-schema.sql")).unwrap()).unwrap();
    assert_eq!(inline, parsed, "keys inside CREATE TABLE normalize to the canonical list");

    let check = schema::parse("CREATE TABLE readings (\n    value bigint NOT NULL CONSTRAINT value_nonnegative CHECK (value >= 0)\n);\n").unwrap();
    let canonical = schema::parse(&std::fs::read_to_string(fixtures().join("readings-count/schema.sql")).unwrap()).unwrap();
    assert_eq!(check, canonical, "a named column CHECK");
}

/// Both key forms give the same request (the whole templates request of the TPC-H folder).
#[test]
fn both_key_forms_give_the_same_request() {
    let copy = scratch("inline-folder");
    let source = fixtures().join("tpc-h");
    std::fs::create_dir_all(copy.join("queries")).unwrap();
    for file in ["gendb.toml", "bindings.json", "queries/Q01.sql", "queries/Q06.sql", "queries/Q11.sql"] {
        std::fs::copy(source.join(file), copy.join(file)).unwrap();
    }
    std::fs::copy(fixtures().join("tpc-h-inline-schema.sql"), copy.join("schema.sql")).unwrap();
    let overlay = Settings { scale: Some("sf100".into()), ..settings() };
    let canonical = folder("tpc-h", overlay.clone());
    let inline = WorkloadFolder::read(&copy, Settings::read(&copy, None).unwrap().overlay(overlay)).unwrap();
    let request = |f: &WorkloadFolder| {
        let mut s = scale("sf100", f, 114_641_618_862, true, None);
        s.locations = locations(&canonical);
        serde_json::to_value(requests::templates_request(f, &ctx(), &s).unwrap()).unwrap()
    };
    assert_eq!(request(&inline), request(&canonical));
}

/// Each schema refusal, by name.
#[test]
fn schema_refusals() {
    let refused = |text: &str| schema::parse(text).unwrap_err();
    let cases: [(&str, &str, &str); 11] = [
        ("CREATE TABLE t (a varchar(10));", "schema_unsupported_type", "write text"),
        ("CREATE TABLE t (a char(1) NOT NULL);", "schema_unsupported_type", "write text"),
        ("CREATE TABLE t (a numeric);", "schema_unsupported_type", "numeric(p,s)"),
        ("CREATE TABLE t (a double precision);", "schema_unsupported_type", "is not supported"),
        ("CREATE TABLE t (a integer DEFAULT 0);", "schema_unsupported", "DEFAULT"),
        ("CREATE TABLE t (a integer CHECK (a > 0));", "schema_unnamed_check", "CONSTRAINT <name> CHECK"),
        ("CREATE TABLE t (a integer, CHECK (a > 0));", "schema_unnamed_check", "CONSTRAINT <name> CHECK"),
        ("CREATE TABLE t (a integer);\nALTER TABLE t ADD PRIMARY KEY (a);\nCREATE TABLE u (b integer);", "schema_syntax", "comes after an ALTER TABLE"),
        ("CREATE TABLE t (a integer);\nALTER TABLE u ADD PRIMARY KEY (a);", "schema_syntax", "no CREATE TABLE u"),
        ("CREATE TABLE t (a integer);\nCREATE INDEX i ON t (a);", "schema_syntax", "CREATE TABLE statements and ALTER TABLE"),
        ("CREATE TABLE \"T\" (a integer);", "schema_syntax", "unquoted identifier"),
    ];
    for (text, reason, words) in cases {
        let error = refused(text);
        assert_eq!(error.reason, reason, "{text}: {error}");
        assert!(error.detail.contains(words), "{text}: {error}");
    }
}

// ---------------------------------------------------------------- query files ----------------------------------------

/// Header lines become typed parameters (free with optional bounds, or fixed); the SQL is the rest of the file.
#[test]
fn query_header_round_trip_and_refusals() {
    let text = "-- $1 day date min 1994-01-01 max 1998-12-31\n-- $2 discount numeric(15,2)\n-- $3 nation text = GERMANY\n-- note\nSELECT 1;\n";
    let query = queries::parse("Q9", Path::new("Q9.sql"), text).unwrap();
    assert_eq!(query.sql, "-- note\nSELECT 1;\n");
    let shapes: Vec<(u32, &str, &str, BindingRequest)> = query.parameters.iter().map(|p| (p.index, p.name.as_deref().unwrap(), p.sql_type.as_str(), p.binding.clone())).collect();
    assert_eq!(shapes, [
        (1, "day", "date", BindingRequest::Free { min: Some("1994-01-01".into()), max: Some("1998-12-31".into()) }),
        (2, "discount", "numeric(15,2)", BindingRequest::Free { min: None, max: None }),
        (3, "nation", "text", BindingRequest::Fixed("GERMANY".into())),
    ]);
    assert!(query.is_template());
    let concrete = queries::parse("Q1", Path::new("Q1.sql"), "SELECT 1;\n").unwrap();
    assert!(concrete.parameters.is_empty() && !concrete.is_template());
    for bad in ["-- $x k bigint\nSELECT $1;", "-- $1 k\nSELECT $1;", "-- $1 k bigint max 3 min 1\nSELECT $1;", "-- $1 k bigint\n-- $1 j bigint\nSELECT $1;"] {
        assert_eq!(queries::parse("Q", Path::new("Q.sql"), bad).unwrap_err().reason, "query_header", "{bad}");
    }
    let mut stems = vec!["Q10", "Q2", "Q1", "Q24", "sf100", "sf1", "sf10"];
    stems.sort_by(|a, b| queries::natural_order(a, b));
    assert_eq!(stems, ["Q1", "Q2", "Q10", "Q24", "sf1", "sf10", "sf100"]);
}

/// The `queries` setting selects and orders the files; a listed name without a file is refused.
#[test]
fn query_selection() {
    let selected = folder("tpc-h", Settings { queries: Some(vec!["Q11".into(), "Q01".into()]), ..settings() });
    assert_eq!(selected.queries.iter().map(|q| q.name.as_str()).collect::<Vec<_>>(), ["Q11", "Q01"]);
    let root = fixtures().join("tpc-h");
    let error = WorkloadFolder::read(&root, Settings { queries: Some(vec!["Q99".into()]), ..settings() }).unwrap_err();
    assert_eq!(error.reason, "query_missing");
}

// ---------------------------------------------------------------- settings and bindings ------------------------------

#[test]
fn settings_overlay_paths_and_refusals() {
    let dir = scratch("settings");
    std::fs::write(dir.join("gendb.toml"), "mode = \"engine\"\nbudget_usd = 438\ntimed_calls = 5\nreuse = [\"libs/a\"]\nstart_from = \"runs/r:v001\"\n[[members]]\nfolder = \"../m\"\nrole = \"check\"\n").unwrap();
    std::fs::write(dir.join("other.toml"), "budget_usd = \"12.5\"\nthreads = [1, 8]\n").unwrap();
    let read = Settings::read(&dir, Some(&dir.join("other.toml"))).unwrap();
    assert_eq!((read.mode(), read.budget_usd.as_ref().map(DecimalText::text)), (Mode::Engine, Some("12.5".into())));
    assert_eq!(read.threads(), [1, 8]);
    assert_eq!(read.reuse, Some(vec![dir.join("libs/a")]));
    assert_eq!(read.start(), Some(StartFrom::Version { run: dir.join("runs/r"), version: "v001".into() }));
    let member = &read.members.as_ref().unwrap()[0];
    assert_eq!((member.folder.clone(), member.role), (dir.join("../m"), MemberRole::Check));
    assert_eq!(StartFrom::parse("/exports/engine"), StartFrom::Folder("/exports/engine".into()));
    let cli = Settings { storage: Some(Storage::Plain), ..settings() };
    assert_eq!(read.clone().overlay(cli).storage(), Storage::Plain);
    assert_eq!(read.name_or(Path::new("/x/TPC-H")), "tpc_h");
    let shared = Settings::default().with_shared_from(&read);
    assert_eq!((shared.threads(), shared.budget_usd.is_some(), shared.timed_calls), (vec![1, 8], true, Some(5)));

    std::fs::write(dir.join("bad.toml"), "speed_up = 5\n").unwrap();
    assert_eq!(Settings::parse_file(&dir.join("bad.toml")).unwrap_err().reason, "settings_invalid");
}

/// Bindings: the folder's file per scale wins, a concrete statement without an entry gets `v0`, and a wrong count of
/// arguments is refused.
#[test]
fn visible_bindings() {
    let engine = folder("tpc-h-engine", settings());
    assert_eq!(engine.visible_bindings("sf1").unwrap()["queries"]["Q01"].as_array().unwrap().len(), 1);
    assert_eq!(engine.visible_bindings("sf100").unwrap()["queries"]["Q01"].as_array().unwrap().len(), 3);
    let sec = folder("sec-edgar", settings());
    let visible = sec.visible_bindings("sf3").unwrap();
    assert_eq!(visible["kind"], "visible");
    assert_eq!(visible["queries"]["Q1"][0]["arguments"], json!([]));

    let copy = scratch("bad-bindings");
    std::fs::create_dir_all(copy.join("queries")).unwrap();
    std::fs::copy(fixtures().join("readings-count/schema.sql"), copy.join("schema.sql")).unwrap();
    std::fs::copy(fixtures().join("readings-count/queries/readings-count.sql"), copy.join("queries/readings-count.sql")).unwrap();
    std::fs::write(copy.join("queries/count.sql"), "SELECT COUNT(*) AS n FROM readings;\n").unwrap();
    std::fs::write(copy.join("bindings.json"), r#"{"queries": {"readings-count": [{"binding_id": "v0", "arguments": ["4", "5"]}]}}"#).unwrap();
    let wrong = WorkloadFolder::read(&copy, settings()).unwrap();
    assert_eq!(wrong.visible_bindings("tiny").unwrap_err().reason, "bindings_invalid");
    std::fs::remove_file(copy.join("bindings.json")).unwrap();
    let unbound = WorkloadFolder::read(&copy, settings()).unwrap();
    assert_eq!(unbound.visible_bindings("tiny").unwrap()["queries"], json!({"count": [{"binding_id": "v0", "arguments": []}]}), "a concrete statement's one binding");
    let error = requests::templates_request(&unbound, &ctx(), &scale("tiny", &unbound, 100, false, None)).unwrap_err();
    assert_eq!(error.reason, "bindings_missing", "goal fast needs a template's bindings");
}

// ---------------------------------------------------------------- golden requests: templates mode --------------------

/// TPC-H, agent-designed storage: the generated request is the queries phase request (without the storage session)
/// and, with `stop_before_queries` and one query at a time, the storage phase request of the published run.
#[test]
fn golden_tpch_designed() {
    let tpch = folder("tpc-h", Settings { scale: Some("sf100".into()), parallel_queries: Some(6), parallel_preparations: Some(8), ..settings() });
    let inputs = scale("sf100", &tpch, 114_641_618_862, true, Some(baselines("tpch-sf100", &tpch, "sf100")));
    let request = requests::templates_request(&tpch, &ctx(), &inputs).unwrap();
    request.validate().unwrap();
    let mut queries_phase = request.clone();
    queries_phase.workload_storage = None;
    assert_golden(&queries_phase, "tpch-q-all.json");
    let mut storage_phase = request;
    storage_phase.workload_storage.as_mut().unwrap().stop_before_queries = true;
    storage_phase.max_concurrent_queries = 1;
    assert_golden(&storage_phase, "tpch-w1.json");
}

#[test]
fn golden_tpch_plain() {
    let tpch = folder("tpc-h", Settings { storage: Some(Storage::Plain), parallel_queries: Some(3), parallel_preparations: Some(8), scale: Some("sf100".into()), ..settings() });
    let inputs = scale("sf100", &tpch, 114_641_618_862, true, Some(baselines("tpch-sf100", &tpch, "sf100")));
    let request = requests::templates_request(&tpch, &ctx(), &inputs).unwrap();
    request.validate().unwrap();
    assert_golden(&request, "tpch-flat-q-all.json");
}

/// SEC-EDGAR (a concrete statement among templates; the storage budget from `storage_budget_bytes`), both storages.
#[test]
fn golden_sec_templates() {
    for (storage, file) in [(Storage::Designed, "sec.json"), (Storage::Plain, "sec-flat.json")] {
        let sec = folder("sec-edgar", Settings { storage: Some(storage), scale: Some("sf3".into()), parallel_queries: Some(6), parallel_preparations: Some(8), ..settings() });
        let locations = locations(&sec);
        let budget = sec.settings.storage_budget_bytes.map(|b| (b, sec.root.as_path()));
        let data_size = data::data_size(&sec.data_dir("sf3"), &sec.schema.dataset(&locations), budget).unwrap();
        assert_eq!((data_size.original_data_bytes, data_size.measure), (5_439_582_957, "setting_storage_budget_bytes"));
        let inputs = ScaleInputs { name: "sf3".into(), locations, capture: Some("/c/sf3".into()), data_size, baselines: Some(baselines("sec-sf3", &sec, "sf3")) };
        let request = requests::templates_request(&sec, &ctx(), &inputs).unwrap();
        request.validate().unwrap();
        assert_golden(&request, file);
    }
}

/// readings-count: goal correct over the plain storage, no other engine; the request of the example's own writer.
#[test]
fn golden_readings_count() {
    // the published run used one query session at a time (the default is 5)
    let readings = folder("readings-count", Settings { parallel_queries: Some(1), ..settings() });
    let request = requests::templates_request(&readings, &ctx(), &scale("tiny", &readings, 100, false, None)).unwrap();
    request.validate().unwrap();
    assert_golden(&request, "readings-count.json");
}

// ---------------------------------------------------------------- golden requests: engine mode -----------------------

/// A flat-storage record holding the eligible packages of the expected request `file`.
fn flat_record(file: &str, name: &str) -> FlatStorages {
    let expected: Value = serde_json::from_str(&std::fs::read_to_string(fixtures().join("expected").join(file)).unwrap()).unwrap();
    let tables: Vec<Value> = expected["storage_policy"]["eligible_storages"].as_array().unwrap().iter().map(|e| json!({"package": e["package"]})).collect();
    let record = scratch(&format!("flat-{name}")).join("flat-storage.json");
    std::fs::write(&record, json!({"tables": tables}).to_string()).unwrap();
    FlatStorages::read(&record).unwrap()
}

fn engine_overlay(budget: &str) -> Settings {
    Settings { budget_usd: Some(DecimalText::Text(budget.into())), parallel_preparations: Some(8), memory_limit_bytes: Some(154_618_822_656), ..settings() }
}

/// anyschema: a check member (its own library, no output home, answers only) and its flat preparation request.
#[test]
fn golden_anyschema_member_and_flat_preparation() {
    let anyschema = folder("anyschema", engine_overlay("438"));
    let tiny = scale("tiny", &anyschema, 39_507, true, Some(baselines("anyschema-tiny", &anyschema, "tiny")));
    let flat = flat_record("anyschema-member.json", "anyschema");
    let member = requests::engine_request(&anyschema, &ctx(), std::slice::from_ref(&tiny), &flat, Some("anyschema"), vec![]).unwrap();
    member.validate_member(MemberRole::Check).unwrap();
    assert_golden(&member, "anyschema-member.json");
    let preparation = requests::flat_preparation_request(&anyschema, &ctx(), &ScaleInputs { capture: None, ..tiny }, &ctx().paths(Some("anyschema")).library).unwrap();
    preparation.validate().unwrap();
    assert_golden(&preparation, "anyschema-flat.json");
}

/// TPC-H engine over the ladder sf1, sf100 (the primary of the published engine run, whose request adds the output
/// home); an engine without an answer at some cell is not required.
#[test]
fn golden_tpch_engine() {
    let overlay = Settings { reuse: Some(vec!["/r/templates-library".into()]), ..engine_overlay("438") };
    let tpch = folder("tpc-h-engine", overlay);
    let sf1 = scale("sf1", &tpch, 1_100_693_130, true, Some(baselines("tpch-sf1", &tpch, "sf1")));
    let sf100_baselines = baselines("tpch-sf100", &tpch, "sf100");
    let sf100 = scale("sf100", &tpch, 114_641_618_862, true, Some(sf100_baselines.clone()));
    let flat = flat_record("tpch-engine.json", "tpch");
    let mut request = requests::engine_request(&tpch, &ctx(), &[sf1.clone(), sf100], &flat, None, vec![]).unwrap();
    request.validate().unwrap();
    assert_eq!(request.output_home, Some("/w/output".into()));
    request.output_home = None;
    assert_golden(&request, "tpch-engine.json");

    let umbra = sf100_baselines.engines.iter().find(|e| e.name == "umbra").unwrap();
    std::fs::remove_file(sf100_baselines.answer_file(umbra, "Q06", "v1")).unwrap();
    let sf100 = scale("sf100", &tpch, 114_641_618_862, true, Some(sf100_baselines));
    let request = requests::engine_request(&tpch, &ctx(), &[sf1, sf100], &flat, None, vec![]).unwrap();
    let gendb_verification::admission::ValidationPolicy::FormalProofs { required_engines, .. } = &request.validation else { panic!() };
    assert_eq!(required_engines, &["duckdb"]);
    assert_eq!(request.engine.as_ref().unwrap().scales[1].saved_answers.len(), 17);
}

/// SEC-EDGAR engine (one scale, three reuse libraries, the emphasis).
#[test]
fn golden_sec_engine() {
    let reuse = ["/r/a", "/r/b", "/r/c"].map(PathBuf::from).to_vec();
    let overlay = Settings { mode: Some(Mode::Engine), scales: Some(vec!["sf3".into()]), emphasis: Some(EngineEmphasis::CoOptimization), reuse: Some(reuse), ..engine_overlay("1000") };
    let sec = folder("sec-edgar", overlay);
    let sf3 = scale("sf3", &sec, 5_439_582_957, true, Some(baselines("sec-sf3", &sec, "sf3")));
    let mut request = requests::engine_request(&sec, &ctx(), &[sf3], &flat_record("sec-engine.json", "sec"), None, vec![]).unwrap();
    request.validate().unwrap();
    request.output_home = None;
    assert_golden(&request, "sec-engine.json");
}

/// Members, `one_engine` and an exported-engine start become `engine.workloads`; `RUN:VERSION` alone a continued run.
#[test]
fn engine_workloads_and_seeds() {
    let ctx = ctx();
    let make = |overlay: Settings, members| {
        let anyschema = folder("anyschema", Settings { ..engine_overlay("10") }.overlay(overlay));
        let tiny = scale("tiny", &anyschema, 39_507, true, Some(baselines("anyschema-tiny", &anyschema, "tiny")));
        requests::engine_request(&anyschema, &ctx, &[tiny], &flat_record("anyschema-member.json", "seeds"), None, members).unwrap().engine.unwrap()
    };
    let continued = make(Settings { start_from: Some("/runs/g:v003".into()), ..settings() }, vec![]);
    assert_eq!((continued.seed_version.as_ref().map(|s| s.version.as_str()), continued.workloads.is_some()), (Some("v003"), false));
    let timed = make(Settings { timed_calls: Some(5), ..settings() }, vec![]);
    assert_eq!((timed.timed_calls(), continued.timed_calls), (5, None), "`timed_calls` maps to engine.timed_calls; unset, the request's default (3)");
    let member = requests::member_entry(&ctx, "sec", MemberRole::Counted, None);
    let several = make(Settings { one_engine: Some(true), start_from: Some("/exports/e".into()), ..settings() }, vec![member]);
    let workloads = several.workloads.unwrap();
    assert_eq!((workloads.name.as_str(), workloads.require_one_engine, workloads.members[0].request.clone()), ("anyschema", true, PathBuf::from("/w/requests/members/sec.json")));
    assert!(several.seed_version.is_none());
    let refused = folder("anyschema", Settings { budget_usd: None, ..engine_overlay("1") });
    let tiny = scale("tiny", &refused, 1, true, None);
    let error = requests::engine_request(&refused, &ctx, &[tiny], &flat_record("anyschema-member.json", "nobudget"), None, vec![]).unwrap_err();
    assert!(error.detail.contains("budget_usd"), "{error}");
}

// ---------------------------------------------------------------- input files ------------------------------------------

/// The inputs an engine run reads: templates.json naming each statement's SQL without its header, bindings per scale
/// with `v0` for a concrete statement, the data size and an empty variants manifest.
#[test]
fn input_files() {
    let sec = folder("sec-edgar", Settings { mode: Some(Mode::Engine), ..settings() });
    let paths = ctx().paths(None);
    let paths = requests::WorkloadPaths { inputs: scratch("inputs"), ..paths };
    let sf3 = scale("sf3", &sec, 5, true, None);
    requests::write_inputs(&sec, &paths, std::slice::from_ref(&sf3)).unwrap();
    let index: Value = serde_json::from_str(&std::fs::read_to_string(paths.templates()).unwrap()).unwrap();
    for query in &sec.queries {
        let entry = &index["templates"][&query.name];
        assert_eq!(std::fs::read_to_string(paths.inputs.join(entry["sql"].as_str().unwrap())).unwrap(), query.sql);
        assert_eq!(entry["parameters"], serde_json::to_value(&query.parameters).unwrap());
        assert!(!query.sql.starts_with("-- $"));
    }
    let bindings: Value = serde_json::from_str(&std::fs::read_to_string(paths.bindings("sf3")).unwrap()).unwrap();
    assert_eq!((&bindings["queries"]["Q1"][0]["binding_id"], &bindings["queries"]["Q1"][0]["arguments"]), (&json!("v0"), &json!([])));
    let size: Value = serde_json::from_str(&std::fs::read_to_string(paths.data_size("sf3")).unwrap()).unwrap();
    assert_eq!(size["original_data_bytes"], 5);
    assert_eq!(std::fs::read_to_string(paths.empty_variants()).unwrap().trim(), "{\n  \"variants\": []\n}");
}

// ---------------------------------------------------------------- data -------------------------------------------------

/// A 4-row Parquet file: its footer is checked against schema.sql (every difference listed with its fix), a table may
/// be a directory of parts, and the data size comes from the manifest or the footers.
#[test]
fn parquet_footer_check() {
    use arrow::array::{ArrayRef, Decimal128Array, Int64Array, LargeStringArray, StringArray};
    use arrow::datatypes::{DataType, Field, Schema as ArrowSchema};
    use arrow::record_batch::RecordBatch;
    use std::sync::Arc;
    let write = |path: &Path, fields: Vec<Field>, columns: Vec<ArrayRef>| {
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        let batch = RecordBatch::try_new(Arc::new(ArrowSchema::new(fields)), columns).unwrap();
        let mut writer = parquet::arrow::ArrowWriter::try_new(std::fs::File::create(path).unwrap(), batch.schema(), None).unwrap();
        writer.write(&batch).unwrap();
        writer.close().unwrap();
    };
    let ids: ArrayRef = Arc::new(Int64Array::from(vec![1, 2, 3, 4]));
    let amounts: ArrayRef = Arc::new(Decimal128Array::from(vec![100, 250, 0, 999]).with_precision_and_scale(15, 2).unwrap());
    let root = scratch("parquet");
    std::fs::create_dir_all(root.join("queries")).unwrap();
    std::fs::write(root.join("schema.sql"), "CREATE TABLE t (\n    id bigint NOT NULL,\n    name text NOT NULL,\n    amount numeric(15,2)\n);\n").unwrap();
    std::fs::write(root.join("queries/Q1.sql"), "SELECT COUNT(*) FROM t;\n").unwrap();
    let wrong = root.join("data/bad/t.parquet");
    write(
        &wrong,
        vec![Field::new("id", DataType::Int64, false), Field::new("name", DataType::LargeUtf8, true), Field::new("amount", DataType::Decimal128(15, 2), false)],
        vec![ids.clone(), Arc::new(LargeStringArray::from(vec!["a", "b", "c", "d"])), amounts.clone()],
    );
    let good_fields = || vec![Field::new("id", DataType::Int64, false), Field::new("name", DataType::Utf8, false), Field::new("amount", DataType::Decimal128(15, 2), true)];
    let names: ArrayRef = Arc::new(StringArray::from(vec!["a", "b", "c", "d"]));
    write(&root.join("data/good/t/part-1.parquet"), good_fields(), vec![ids.clone(), names.clone(), amounts.clone()]);
    write(&root.join("data/good/t/part-0.parquet"), good_fields(), vec![ids, names, amounts]);
    let folder = WorkloadFolder::read(&root, Settings::default()).unwrap();
    assert_eq!(folder.data_scales(), ["bad", "good"]);
    let error = folder.check_data("bad").unwrap_err();
    assert_eq!(error.reason, "data_schema");
    let lines: Vec<&str> = error.detail.lines().collect();
    assert_eq!(lines.len(), 3, "{error}");
    assert!(lines[0].contains("t.name is LargeUtf8") && lines[0].contains("pa.string()"), "{}", lines[0]);
    assert!(lines[1].contains("t.name is nullable in the file but NOT NULL in schema.sql"), "{}", lines[1]);
    assert!(lines[2].contains("t.amount is NOT NULL in the file but nullable in schema.sql"), "{}", lines[2]);
    folder.check_data("good").unwrap();
    let parts = &folder.locations("good").unwrap()["t"];
    assert_eq!(parts.iter().map(|p| p.file_name().unwrap().to_str().unwrap()).collect::<Vec<_>>(), ["part-0.parquet", "part-1.parquet"]);
    let footers = folder.data_size("good").unwrap();
    assert!(footers.original_data_bytes > 0 && footers.measure == "parquet_uncompressed_bytes", "{footers:?}");
    std::fs::write(root.join("data/good/MANIFEST.json"), r#"{"rows": {"t": 4}}"#).unwrap();
    assert_eq!(folder.data_size("good").unwrap(), footers, "a manifest without original_data_bytes: the footers' size");
    std::fs::write(root.join("data/good/MANIFEST.json"), r#"{"original_data_bytes": 39507}"#).unwrap();
    assert_eq!(folder.data_size("good").unwrap().original_data_bytes, 39_507);
    std::fs::write(root.join("data/good/MANIFEST.json"), r#"{"original_data_bytes": 0}"#).unwrap();
    assert_eq!(folder.data_size("good").unwrap_err().reason, "data_size", "a stated size must be positive");
    assert_eq!(folder.check_data("none").unwrap_err().reason, "data_missing");
    let both = WorkloadFolder::read(&root, Settings { scale: None, ..Settings::default() }).unwrap();
    assert_eq!(both.run_scales().unwrap_err().reason, "scale_invalid", "two scales and no scale setting");
}

// ---------------------------------------------------------------- frontend translation -------------------------------

/// Every query translates against the DDL GenDB writes; an undeclared parameter is refused by the frontend, by name.
#[test]
fn frontend_translation_of_every_query() {
    let parser = gendb_frontend::parser::SqlParser::from_environment().unwrap();
    let readings = folder("readings-count", settings());
    readings.check_queries(&parser, &scratch("translate-ok")).unwrap();
    let tpch = folder("tpc-h", settings());
    tpch.check_queries(&parser, &scratch("translate-tpch")).unwrap();

    let copy = scratch("translate-refused");
    std::fs::create_dir_all(copy.join("queries")).unwrap();
    std::fs::copy(fixtures().join("readings-count/schema.sql"), copy.join("schema.sql")).unwrap();
    std::fs::write(copy.join("queries/Q1.sql"), "-- $1 k bigint\nSELECT COUNT(*) AS n FROM readings WHERE value > $1 AND value < $2;\n").unwrap();
    let error: FolderError = WorkloadFolder::read(&copy, settings()).unwrap().check_queries(&parser, &copy.join("scratch")).unwrap_err();
    assert_eq!(error.reason, "frontend_refusal");
    assert!(error.detail.starts_with("Q1 ("), "{error}");
}
