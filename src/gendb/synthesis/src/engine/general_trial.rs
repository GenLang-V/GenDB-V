//! The $0 fixture trial of the general line . FRAMEWORK TEST ONLY: a
//! scripted author (no provider, no LLM, a stub cost of one dollar per call) runs the whole general loop through the
//! public controller (`engine::branches::run_general_engine`, `gendb engine prepare`, `gendb prepare-flat-storage`) on
//! two tiny generated TPC-H captures, with a call limit of 1 s. Nothing here is a timing experiment: the cells take
//! milliseconds and only their order matters.
//!
//! Fixture (built once, cached under `<trial>/fixture`): the PostgreSQL-checked tiny case of Q12 (every table,
//! FK-closed) grown deterministically per scale ([`trial_tables`]: `part` grows most and no training template reads it,
//! so materializing every table dominates each call of version 0 and its slowed copies); the 8 generated flat storages
//! of scale `s1` in one library (`gendb prepare-flat-storage`); templates Q01, Q06 and Q12 (Q12 holds the text
//! constants `'1-URGENT'` and `'2-HIGH'`) with their frozen variants, visible bindings `v0` and `v1`, synthetic
//! baselines, and saved answers computed by the verified SQLSpec reference evaluator on each scale's database.
//!
//! Two runs, each a test (run with `-- --ignored`; `TMPDIR` a scratch directory, `GENDB_WORKER` the `gendb`
//! executable of this build, `GENDB_TRIAL_DIR` the trial folder, `GENDB_BUILD_LOCK` the build lock; the pinned
//! Verus and frontend):
//! - [`version_zero_admission_resumes_without_a_second_admission`] (run P): `gendb engine prepare` generates, admits,
//!   times and profiles version 0. Its first launch (a child process of this test binary) is killed by SIGKILL at the
//!   crash point just before the library admission (the intent is written, nothing admitted); the second just after the
//!   admission (before `admitted.json`); the third is the real `gendb engine prepare`, which adopts the admission. The
//!   library then holds exactly one engine version.
//! - [`general_line_trial`] (run L): the loop with two branches and two ladder entries (`s1`, and `s2`, the last scale,
//!   where the run stays). Every launch is a child process; the plan of every scripted
//!   session is [`plan`]. Its root `v000` is a labeled fixture, version 0 materializing every table eight times
//!   (`branches::RootSource::fixture`), because a submission is accepted only when it beats its parent and an accepted
//!   merge must beat the main-line head (the best version so far): the trial needs room above its root, and the copies
//!   (materializing 1, 2, 3 or 5 times) are chosen so that the main line is decided both ways: by the adopted
//!   acceptance race when the parent is the main-line head, and by a main-line race when it is not. The launches:
//!   1. the move to `s2` (every cell of `v000` finished at `s1`; the `s2` assets were prepared into the run library with
//!      `gendb prepare-flat-storage`); b1's first session submits the copy materializing three times with its direction
//!      (accepted, `v001`; its parent `v000` is the main-line head, so its acceptance race decides the main line: `v001`
//!      becomes the head with that timing adopted, and nothing is timed again); SIGKILL just after its admission;
//!   2. relaunch: the admission is adopted (no second admission); the session continues the provider session; its next
//!      call is stopped by SIGTERM after the scripted transport wrote its durable receipt;
//!   3. relaunch: the receipt is recovered; the submission (a `static` item) is refused at freeze; its transcript holds a
//!      compaction, so the session ends. b2 starts at once, since b1 has an evaluated submission: its first submission
//!      has no direction (refused: `branch_direction_required`), its second states one (the copy materializing five
//!      times: accepted over the root, `v002`; its parent is not the main-line head and its recorded score is not better
//!      than `v001`'s, so it is not the main-line head and a merge is due) and asks for a fresh session.
//!      The run pauses after both first sessions (`pause_after_session`);
//!   4. relaunch with the cadence switched to every session (not part of the run's identity): b1's second session is a
//!      fresh session (a template constant, refused, with a compaction); b2's merge session submits the copy
//!      materializing twice, which beats the main-line head; SIGKILL just before its admission (the intent is written);
//!   5. relaunch: the merge is admitted from its intent (`v003`, the main-line head); b1's third session is a refusal
//!      with a compaction;
//!   6. relaunch: b1's fourth session, seeded from its head `v001` (the copy materializing three times), submits in turn
//!      version 0's code (accepted; its parent is not the main-line head and its recorded score beats the merge's, so a
//!      main-line race times it against the merge, and it becomes the head), the copy materializing twice (rejected: an
//!      attempt), a template constant (refused at freeze) and a schema name (refused at freeze, `schema_name`). b2's
//!      third session submits two storages built from the flat storage of one table and extending it ([`TrialStorage`]),
//!      each with the copy materializing three times: `marked`
//!      (an empty added part: a storage change whose serving storage stays at the plain storage's size, within s2's
//!      original data size, set just above it; accepted over b2's head) and the `zoned` fixture (a zone part: the serving
//!      storage grows above s2's original data size; refused at the storage step, `storage_budget_exceeded`, before
//!      any timing). The versions reading only the plain storage are allowed as is. The stub costs reach the budget and the run stops (`budget_limit`).
//!
//!   Then the records are checked against each other (library versions and selections, tree, findings, folders, the
//!   main-line decisions, the output home) and the rendered prompts of a first, a continued and a fresh call are copied
//!   for review.
//! - [`trial_storage_fixtures_verify`]: the two storage fixtures alone (scan and whole-crate Verus), a fast check.
//! - [`stops`]: a kill just after a submission's storage is registered, before the engine's admission (run S), and the
//!   user's SIGTERM during a Verus run and during an author call through the real `gendb` (run T).
//! - [`live_stop`] (run R, PAID: real Claude Code calls, at most the request's small budget): the user's SIGTERM during
//!   a live call of the real author CLI, its recovery and the resumed provider session.
//!
//! Every launch installs the user's stop (`gendb_runtime::process_stop`), as `gendb engine synthesize|prepare` does.

mod live_stop;
mod stops;

use super::acceptance::{CRASH_AFTER_ADMISSION, CRASH_BEFORE_ADMISSION};
use super::branches::{GeneralRunOptions, LADDER_FILE, RootSource, prepare_general_run, run_general_engine, seed_root_version};
use super::replay_fixture::{TPCH_DATASET, repository, saved_value, tpch_constraints, training_entries, worker, write_parquet};
use super::rounds::{GENERAL_LINE_PROMPT, PAUSED, engine_directory, prepare_engine_scale};
use super::sessions::{SESSION_FILE, SessionKind, SessionRecord, branch_sessions};
use super::tree::{self, NodeKind, VersionTree};
use crate::controller::author::{AuthorCall, AuthorTransport, CandidateSubmission, Capability};
use crate::controller::ledger::{Call, Receipt, Tokens, UsageScope};
use crate::controller::limits::Money;
use crate::controller::records::{self, read_json, write_json_atomic};
use crate::controller::request::WorkloadRequest;
use crate::controller::workload_run::flat_preparation::prepare_flat_storage;
use crate::controller::workload_run::lifecycle::{Route, record_request, record_route};
use crate::file_lock::FileLock;
use crate::storage::engine_library::seed_engine_library;
use gendb_artifacts::verus::{engine_lineage, engine_selections, engine_versions};
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_frontend::ast::{TableDef, Translation, decode};
use gendb_frontend::engine_encode::encode_binding;
use gendb_frontend::params::{Instance, ParamRequest};
use gendb_frontend::parser::SqlParser;
use gendb_sqlspec::codec::{HostTables, HostValue, RunOutcome};
use gendb_sqlspec::evaluator::{EvaluatorLibrary, echo_text};
use gendb_sqlspec::fixtures::{Fixture, fixtures_dir};
use gendb_storage::import::DatasetSpec;
use gendb_verification::admission::dataset_ddl;
use gendb_verification::obligations::{AssemblyError, StorageUse, flat_storage, interpreter_engine};
use gendb_verification::reference::{BuildOptions, BuildStatus, build_evaluator};
use gendb_verification::verus::{FrameworkSource, VerusToolchain};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

// ------------------------------------------------------------------------------------------------ the fixture

/// Bump when the generated data or the fixture's files change: the cache under `<trial>/fixture-<identity>` is reused
/// only for the same identity (the reference evaluators, which depend only on the bound statements, are cached under
/// `<trial>/evaluators` for every identity).
const FIXTURE_IDENTITY: &str = "v2";
/// The training templates of the trial.
const TEMPLATES: [&str; 3] = ["Q01", "Q06", "Q12"];
/// The visible bindings of every template (`v0` is the timing binding).
const BINDINGS: [&str; 2] = ["v0", "v1"];
/// The configured worker counts (official cells).
const WORKERS: [usize; 2] = [1, 2];
/// The tiny database every scale grows from.
const BASE_CASE: &str = "pg_reference/tpch_all22_cases/q12.json";
/// Rows added per scale unit: `part` (read by no training template), `orders`, and lines per new order.
const PART_ROWS: usize = 6000;
const ORDER_ROWS: usize = 8;
const LINES_PER_ORDER: usize = 10;
/// The trial's call limit in seconds (the design's test limit) and memory limit (a framework safety limit for tiny data).
const CALL_LIMIT_SECONDS: u64 = 1;
const MEMORY_LIMIT_BYTES: u64 = 16 << 30;
/// The stub cost of every scripted call, and run L's budget: exactly the calls of [`plan`] (13 calls).
const CALL_COST: &str = "1";
const RUN_L_BUDGET: &str = "13";

/// The trial folder (`GENDB_TRIAL_DIR`, default `<TMPDIR>/general-trial`).
fn trial_dir() -> PathBuf {
    std::env::var_os("GENDB_TRIAL_DIR").map(PathBuf::from).unwrap_or_else(|| PathBuf::from(std::env::var_os("TMPDIR").expect("TMPDIR")).join("general-trial"))
}

/// Run `f` holding the build lock (`GENDB_BUILD_LOCK`), as every Verus run of the fixture must.
fn with_build_lock<T>(f: impl FnOnce() -> T) -> T {
    let path = PathBuf::from(std::env::var_os("GENDB_BUILD_LOCK").expect("GENDB_BUILD_LOCK: the build lock"));
    let file = fs::OpenOptions::new().create(true).truncate(false).write(true).open(&path).unwrap();
    let _lock = FileLock::acquire(file, libc::LOCK_EX).unwrap();
    f()
}

/// The prepared fixture of both scales.
struct TrialFixture {
    dir: PathBuf,
    dataset: DatasetSpec,
    /// The flat library of scale `s1` (8 generated flat storages; no engine version).
    flat_library: PathBuf,
    /// The flat storage packages `(name, package)` in table order.
    flat: Vec<(String, ContentId)>,
    /// Per scale: its data files (`table -> parquet`), its saved answers and its flat bytes (`s1` only, known now).
    scales: Vec<FixtureScale>,
    /// The flat storage preparation's capture of `s1`.
    s1_capture: PathBuf,
    s1_flat_bytes: u64,
    templates: PathBuf,
    variants: PathBuf,
    bindings: PathBuf,
}

struct FixtureScale {
    name: &'static str,
    locations: serde_json::Map<String, Value>,
    targets: PathBuf,
    saved_answers: Vec<Value>,
}

/// One table's column position.
fn column(schema: &[TableDef], table: &str, name: &str) -> (usize, usize) {
    let t = schema.iter().position(|d| d.name == table).unwrap_or_else(|| panic!("table {table}"));
    let c = schema[t].columns.iter().position(|c| c.name == name).unwrap_or_else(|| panic!("column {table}.{name}"));
    (t, c)
}

fn text(value: &str) -> HostValue {
    HostValue::Text(value.as_bytes().to_vec())
}

fn decimal(coeff: i128) -> HostValue {
    HostValue::Num { coeff, scale: 2 }
}

/// The trial database at scale `units` (1 or 2): [`BASE_CASE`] grown deterministically. `part` gains
/// `PART_ROWS * units` rows; `orders` gains `ORDER_ROWS * units` orders of the case's customer, each with
/// `LINES_PER_ORDER` lines of the case's part and supplier (so every key and foreign key stays valid), with varied
/// quantities, prices, discounts, flags, dates, priorities and ship modes.
fn trial_tables(schema: &[TableDef], base: &HostTables, units: usize) -> HostTables {
    let mut tables = base.clone();
    let set = |row: &mut Vec<HostValue>, table: &str, name: &str, value: HostValue| row[column(schema, table, name).1] = value;
    let date = |row: &Vec<HostValue>, table: &str, name: &str| match row[column(schema, table, name).1] {
        HostValue::Date(d) => d,
        ref other => panic!("{table}.{name}: {other:?}"),
    };
    let (part, _) = column(schema, "part", "p_partkey");
    for k in 0..PART_ROWS * units {
        let mut row = tables[part][0].clone();
        set(&mut row, "part", "p_partkey", HostValue::Int(10_000 + k as i64));
        set(&mut row, "part", "p_name", text(&format!("trial part {k} goldenrod lavender spring chocolate")));
        set(&mut row, "part", "p_mfgr", text(&format!("Manufacturer#{}", k % 5 + 1)));
        set(&mut row, "part", "p_brand", text(&format!("Brand#{}{}", k % 5 + 1, k % 4 + 1)));
        set(&mut row, "part", "p_type", text(["STANDARD POLISHED TIN", "SMALL PLATED COPPER", "PROMO BURNISHED NICKEL"][k % 3]));
        set(&mut row, "part", "p_size", HostValue::Int((k % 50 + 1) as i64));
        set(&mut row, "part", "p_container", text(["SM CASE", "MED BOX", "LG PACK", "JUMBO PKG"][k % 4]));
        set(&mut row, "part", "p_retailprice", decimal(90_000 + k as i128));
        set(&mut row, "part", "p_comment", text("trial fixture row, read by no training template"));
        tables[part].push(row);
    }
    let (orders, _) = column(schema, "orders", "o_orderkey");
    let (lineitem, _) = column(schema, "lineitem", "l_orderkey");
    let order_base = tables[orders][0].clone();
    let line_base = tables[lineitem][0].clone();
    let first_order_date = date(&order_base, "orders", "o_orderdate");
    let flags = [("A", "F"), ("N", "O"), ("R", "F"), ("N", "F")];
    let modes = ["MAIL", "SHIP", "AIR", "TRUCK", "REG AIR"];
    let priorities = ["1-URGENT", "2-HIGH", "3-MEDIUM", "4-NOT SPECIFIED", "5-LOW"];
    for j in 0..ORDER_ROWS * units {
        let key = 10_000 + j as i64;
        let order_date = first_order_date + ((j * 53) % 1700) as i32 - 600;
        let mut order = order_base.clone();
        set(&mut order, "orders", "o_orderkey", HostValue::Int(key));
        set(&mut order, "orders", "o_orderstatus", text(if j % 2 == 0 { "O" } else { "F" }));
        set(&mut order, "orders", "o_totalprice", decimal(500_000 + 37 * j as i128));
        set(&mut order, "orders", "o_orderdate", HostValue::Date(order_date));
        set(&mut order, "orders", "o_orderpriority", text(priorities[j % priorities.len()]));
        tables[orders].push(order);
        for i in 1..=LINES_PER_ORDER {
            let mut line = line_base.clone();
            let quantity = ((j * 7 + i * 3) % 50 + 1) as i128;
            let ship = order_date + ((i * 5) % 90) as i32 + 1;
            let (flag, status) = flags[(j + i) % flags.len()];
            set(&mut line, "lineitem", "l_orderkey", HostValue::Int(key));
            set(&mut line, "lineitem", "l_linenumber", HostValue::Int(i as i64));
            set(&mut line, "lineitem", "l_quantity", decimal(quantity * 100));
            set(&mut line, "lineitem", "l_extendedprice", decimal(quantity * 100_000 + (j * 13 + i) as i128));
            set(&mut line, "lineitem", "l_discount", decimal(((j + i) % 11) as i128));
            set(&mut line, "lineitem", "l_tax", decimal(((j * 3 + i) % 9) as i128));
            set(&mut line, "lineitem", "l_returnflag", text(flag));
            set(&mut line, "lineitem", "l_linestatus", text(status));
            set(&mut line, "lineitem", "l_shipdate", HostValue::Date(ship));
            set(&mut line, "lineitem", "l_commitdate", HostValue::Date(order_date + 30 + (j % 40) as i32));
            set(&mut line, "lineitem", "l_receiptdate", HostValue::Date(ship + 1 + ((j + i) % 25) as i32));
            set(&mut line, "lineitem", "l_shipmode", text(modes[(j + i) % modes.len()]));
            set(&mut line, "lineitem", "l_comment", text("trial fixture line"));
            tables[lineitem].push(line);
        }
    }
    tables
}

/// The training set's `templates.json`, the variants manifest of the training templates and the visible bindings `v0`
/// and `v1` (`output/tpch-sf100/bindings/visible.json`), written under `dir`.
fn training_files(dir: &Path) -> (PathBuf, PathBuf, PathBuf) {
    let repo = repository();
    let entries = training_entries(&TEMPLATES);
    let index: serde_json::Map<String, Value> = entries.iter().cloned().collect();
    let templates = dir.join("templates.json");
    fs::write(&templates, serde_json::to_vec_pretty(&json!({"templates":index})).unwrap()).unwrap();
    let manifest: Value = serde_json::from_str(&fs::read_to_string(repo.join("src/gendb/fixtures/tpch/engine-variants/manifest.json")).unwrap()).unwrap();
    let variants: Vec<Value> = manifest["variants"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|v| TEMPLATES.contains(&v["template"].as_str().unwrap()))
        .map(|v| {
            let mut v = v.clone();
            v["file"] = json!(repo.join("src/gendb/fixtures/tpch/engine-variants").join(v["file"].as_str().unwrap()));
            v
        })
        .collect();
    let manifest_file = dir.join("variants.json");
    fs::write(&manifest_file, serde_json::to_vec_pretty(&json!({"variants":variants})).unwrap()).unwrap();
    let visible: Value = serde_json::from_str(&fs::read_to_string(repo.join("output/tpch-sf100/bindings/visible.json")).unwrap()).unwrap();
    let queries: serde_json::Map<String, Value> = TEMPLATES
        .iter()
        .map(|t| {
            let kept: Vec<Value> = visible["queries"][*t].as_array().unwrap().iter().filter(|b| BINDINGS.contains(&b["binding_id"].as_str().unwrap())).cloned().collect();
            (t.to_string(), Value::Array(kept))
        })
        .collect();
    let bindings = dir.join("bindings.json");
    fs::write(&bindings, serde_json::to_vec_pretty(&json!({"kind":"trial fixture: v0 and v1 of output/tpch-sf100/bindings/visible.json","queries":queries})).unwrap()).unwrap();
    (templates, manifest_file, bindings)
}

/// Synthetic baselines of every template at every visible binding and worker count (`targets.json`): DuckDB 2 ms,
/// Umbra 1 ms. Only their ratios enter the score; nothing compares the trial with real engines.
fn synthetic_targets(path: &Path) {
    let cell = json!({"duckdb_ms":2.0,"umbra_ms":1.0,"target_ms":1.0,"agreement":"exact-order"});
    let workers: serde_json::Map<String, Value> = ["1", "2", "64"].iter().map(|w| (w.to_string(), cell.clone())).collect();
    let bindings: serde_json::Map<String, Value> = BINDINGS.iter().map(|b| (b.to_string(), Value::Object(workers.clone()))).collect();
    let targets: serde_json::Map<String, Value> = TEMPLATES.iter().map(|t| (t.to_string(), Value::Object(bindings.clone()))).collect();
    fs::write(path, serde_json::to_vec_pretty(&Value::Object(targets)).unwrap()).unwrap();
}

/// A `fixed_flat` request over `dataset` (the flat storage preparation's request) with library `library`.
fn flat_request(dataset: &DatasetSpec, library: &Path, path: &Path) -> PathBuf {
    let request = json!({"format_version":2,"dataset":dataset,"queries":[{"name":"schema","sql":"SELECT r_regionkey FROM region",
            "limits":{"max_iterations":1,"max_cost_usd":"1","spend_policy":"estimated_usd","max_retries_per_iteration":1,"author_timeout_seconds":60}}],
        "hardware":{"threads":WORKERS},"max_concurrent_queries":1,"author_executable":"fixture","library":library,"barriers":barriers(),
        "storage_policy":{"kind":"fixed_flat"},"integrity_constraints":tpch_constraints(),
        "validation":{"kind":"formal_proofs","numeric_relative_tolerance":"1e-9","required_engines":[],"saved_answers":[]}});
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, serde_json::to_vec_pretty(&request).unwrap()).unwrap();
    path.to_path_buf()
}

/// The host's shared locks (one timing at a time on this host; every Verus run under the build lock): the activity and
/// race locks beside the build lock.
fn barriers() -> Value {
    let build = PathBuf::from(std::env::var_os("GENDB_BUILD_LOCK").expect("GENDB_BUILD_LOCK"));
    json!({"activity_lock":build.with_file_name("activity.lock"),"build_lock":build,"race_lock":build.with_file_name("race.lock")})
}

impl TrialFixture {
    /// Build the fixture under `<trial>/fixture-<identity>` once; later calls reuse it (`fixture.json` marks it complete).
    fn prepare() -> TrialFixture {
        let dir = trial_dir().join(format!("fixture-{FIXTURE_IDENTITY}"));
        fs::create_dir_all(&dir).unwrap();
        let mut dataset: DatasetSpec = serde_json::from_str(TPCH_DATASET).unwrap();
        let parser = SqlParser::from_environment().unwrap();
        let (ddl_text, omitted) = dataset_ddl(&dataset, Some(&tpch_constraints()));
        assert!(omitted.is_empty(), "{omitted:?}");
        let ddl = dir.join("schema.sql");
        fs::write(&ddl, ddl_text).unwrap();
        let probe = dir.join("probe.sql");
        fs::write(&probe, "SELECT r_regionkey FROM region").unwrap();
        let (_, translation) = parser.translate(&ddl, &probe, "postgres", &[]).unwrap();
        let Translation::Ok(doc) = translation else { panic!("schema probe refused: {translation:?}") };
        let schema = doc.tables.clone();
        let base = Fixture::load(&fixtures_dir().join(BASE_CASE)).unwrap().database_for(&doc).unwrap();
        let (templates, variants, bindings) = training_files(&dir);
        let mut scales = vec![];
        let mut databases = vec![];
        for (units, name) in [(1, "s1"), (2, "s2")] {
            let tables = trial_tables(&schema, &base, units);
            let data = dir.join("data").join(name);
            fs::create_dir_all(&data).unwrap();
            let mut locations = serde_json::Map::new();
            for (spec, rows) in dataset.tables.iter().zip(&tables) {
                let file = data.join(format!("{}.parquet", spec.name));
                if !file.is_file() {
                    write_parquet(&file, &spec.fields, rows);
                }
                locations.insert(spec.name.clone(), json!([file]));
            }
            let targets = dir.join(format!("targets-{name}.json"));
            synthetic_targets(&targets);
            scales.push(FixtureScale { name, locations, targets, saved_answers: vec![] });
            databases.push(tables);
        }
        for table in &mut dataset.tables {
            table.locations = vec![PathBuf::from(scales[0].locations[&table.name][0].as_str().unwrap())];
        }
        // The saved answers of every template at every visible binding, per scale: one reference evaluator per bound
        // statement (cached by its echo), run on each scale's database.
        let toolchain = VerusToolchain::from_env().unwrap();
        let entries = training_entries(&TEMPLATES);
        let visible: Value = read_json(&bindings).unwrap();
        for (name, entry) in &entries {
            let parameters: Vec<ParamRequest> = serde_json::from_value(entry["parameters"].clone()).unwrap();
            let placeholders: Vec<_> = parameters.iter().map(ParamRequest::placeholder).collect();
            let (_, translation) = parser.translate(&ddl, Path::new(entry["sql"].as_str().unwrap()), "postgres", &placeholders).unwrap();
            let Translation::Ok(template) = translation else { panic!("{name}: refused: {translation:?}") };
            for binding in visible["queries"][name].as_array().unwrap() {
                let id = binding["binding_id"].as_str().unwrap();
                let arguments: Vec<String> = binding["arguments"].as_array().unwrap().iter().map(|a| a.as_str().unwrap().to_string()).collect();
                let bound = encode_binding(&template, &arguments).unwrap().document;
                let echo = echo_text(&bound);
                let key: String = Sha256::digest(echo.as_bytes()).iter().take(8).map(|b| format!("{b:02x}")).collect();
                let evaluator = trial_dir().join("evaluators").join(format!("{name}-{id}-{key}"));
                let built = evaluator.join("built.json");
                if !built.is_file() {
                    let build = with_build_lock(|| build_evaluator(&toolchain, &bound, &evaluator.join("ast.json"), &evaluator.join("build"), &BuildOptions::default()).unwrap());
                    assert_eq!(build.status, BuildStatus::Ok, "{name} {id}: reference build {}", build.record);
                    write_json_atomic(&built, &json!({"library":build.library,"echo":echo})).unwrap();
                }
                let library = PathBuf::from(read_json::<Value>(&built).unwrap()["library"].as_str().unwrap());
                for (scale, tables) in scales.iter_mut().zip(&databases) {
                    let file = dir.join("answers").join(scale.name).join(format!("{name}-{id}.json"));
                    if !file.is_file() {
                        let outcome = EvaluatorLibrary::load(&library).unwrap().run(tables).unwrap();
                        let RunOutcome::Rows(rows) = outcome else { panic!("{name} {id} at {}: the reference answered {outcome:?}", scale.name) };
                        let rows: Vec<Value> = rows.iter().map(|row| Value::Array(row.iter().map(saved_value).collect())).collect();
                        fs::create_dir_all(file.parent().unwrap()).unwrap();
                        write_json_atomic(&file, &json!({"echo":echo,"rows":rows,"engine":"verified SQLSpec reference evaluator","database":format!("{BASE_CASE} grown, scale {}", scale.name)})).unwrap();
                    }
                    scale.saved_answers.push(json!({"query":name,"binding":id,"engine":"reference",
                        "description":format!("the verified SQLSpec reference evaluator on the trial database of scale {}", scale.name),"path":file,"rows_pointer":"/rows"}));
                }
            }
        }
        // The flat storages of `s1` in the fixture's flat library (verified once; later runs seed their libraries from it).
        let flat_library = dir.join("flat-library");
        let flat_run = dir.join("flat-s1");
        let record: Value = if flat_run.join("flat-storage.json").is_file() {
            read_json(&flat_run.join("flat-storage.json")).unwrap()
        } else {
            prepare_flat_storage(&flat_request(&dataset, &flat_library, &dir.join("flat-s1-request.json")), &flat_run).unwrap()
        };
        let mut flat: Vec<(String, ContentId)> =
            record["tables"].as_array().unwrap().iter().map(|t| (t["storage"].as_str().unwrap().to_string(), serde_json::from_value(t["package"].clone()).unwrap())).collect();
        let order: Vec<String> = dataset.tables.iter().map(|t| format!("flat_{}", t.name)).collect();
        flat.sort_by_key(|(name, _)| order.iter().position(|o| o == name));
        let s1_flat_bytes = record["storage_bytes"].as_u64().unwrap();
        write_json_atomic(&dir.join("fixture.json"), &json!({"identity":FIXTURE_IDENTITY,"flat":flat,"s1_flat_bytes":s1_flat_bytes,"templates":TEMPLATES,
            "rows":databases.iter().map(|d| d.iter().map(Vec::len).collect::<Vec<_>>()).collect::<Vec<_>>()})).unwrap();
        TrialFixture { s1_capture: flat_run.join("data"), dir, dataset, flat_library, flat, scales, s1_flat_bytes, templates, variants, bindings }
    }

    fn packages(&self) -> Vec<ContentId> {
        self.flat.iter().map(|(_, p)| *p).collect()
    }

    /// Seed a run's engine library from the fixture's flat library (hard links; no engine version).
    fn seed_library(&self, library: &Path) {
        seed_engine_library(&self.flat_library, library, &self.packages(), true).unwrap();
    }

    /// The general-line request of runs P and L: `library`, the ladder `s1`, `s2` (the last scale) with the original data
    /// sizes `original` (the budget for changed storage), two
    /// branches, the cadence `cadence`, the stub budget `budget`, the trial's call and memory limits.
    #[allow(clippy::too_many_arguments)]
    fn request(&self, path: &Path, library: &Path, home: &Path, s2_capture: &Path, original: [u64; 2], budget: &str, cadence: &str) -> PathBuf {
        let ladder = [
            TrialScale { name: "s1", data: 0, capture: &self.s1_capture, original_data_bytes: original[0] },
            TrialScale { name: "s2", data: 1, capture: s2_capture, original_data_bytes: original[1] },
        ];
        self.request_with(path, library, home, &ladder, &RunShape { branches: 2, budget, cadence, author_executable: Path::new("fixture") })
    }

    /// The general-line request of a run with the ladder `ladder` and `shape`.
    fn request_with(&self, path: &Path, library: &Path, home: &Path, ladder: &[TrialScale<'_>], shape: &RunShape<'_>) -> PathBuf {
        let RunShape { branches, budget, cadence, author_executable } = *shape;
        let sizes: Vec<u64> = ladder.iter().map(|s| s.original_data_bytes).collect();
        let original = path.with_file_name("original-data-size.json");
        write_json_atomic(&original, &json!({"meaning":"trial fixture: each scale's original_data_bytes as the trial sets it (the budget for changed storage; plain storage only is allowed as is)","original_data_bytes":sizes})).unwrap();
        let scale = |s: &TrialScale<'_>| {
            let data = &self.scales[s.data];
            json!({"name":s.name,"locations":data.locations,"prepared_workload":s.capture,"bindings":self.bindings,"targets":data.targets,
                "saved_answers":data.saved_answers,"original_data_bytes":s.original_data_bytes,"original_data_record":original})
        };
        let eligible: Vec<Value> = self.flat.iter().map(|(_, p)| json!({"package":p,"review":"trial fixture: generated flat storage, every column once (gendb prepare-flat-storage)"})).collect();
        let request = json!({"format_version":2,"dataset":self.dataset,"queries":[],"hardware":{"threads":WORKERS},"max_concurrent_queries":1,"max_concurrent_preparations":4,
            "author_executable":author_executable,"library":library,"barriers":barriers(),"output_home":home,
            "storage_policy":{"kind":"physical_only","eligible_storages":eligible},"integrity_constraints":tpch_constraints(),
            "validation":{"kind":"formal_proofs","numeric_relative_tolerance":"1e-9","required_engines":[]},
            "engine":{"line":"general","templates":self.templates,"timing_binding":"v0","variants":self.variants,
                "storage_seed":{"source_library":self.flat_library,"packages":self.packages()},
                "limits":{"max_iterations":"unset","max_cost_usd":budget,"spend_policy":"estimated_usd","max_retries_per_iteration":1,"author_timeout_seconds":3600},
                "scales":ladder.iter().map(scale).collect::<Vec<_>>(),
                "branches":branches,"pause_after_session":cadence,"call_limit_seconds":CALL_LIMIT_SECONDS,"anon_memory_limit_bytes":MEMORY_LIMIT_BYTES}});
        fs::write(path, serde_json::to_vec_pretty(&request).unwrap()).unwrap();
        WorkloadRequest::read(path).unwrap().validate().unwrap();
        path.to_path_buf()
    }
}

/// One scale of a trial request's ladder: its name, the fixture data it uses (`0`: `s1`'s, `1`: `s2`'s), its prepared
/// capture and its original data size (the budget for changed storage).
struct TrialScale<'a> {
    name: &'static str,
    data: usize,
    capture: &'a Path,
    original_data_bytes: u64,
}

/// The rest of a trial request: branches, the stub budget, the review cadence and the author executable (`fixture` for
/// the scripted authors, never started).
#[derive(Clone, Copy)]
struct RunShape<'a> {
    branches: u32,
    budget: &'a str,
    cadence: &'a str,
    author_executable: &'a Path,
}

/// Switch a request file's review cadence (not part of the run's identity).
fn set_cadence(path: &Path, cadence: &str) {
    let mut request: Value = read_json(path).unwrap();
    request["engine"]["pause_after_session"] = json!(cadence);
    fs::write(path, serde_json::to_vec_pretty(&request).unwrap()).unwrap();
}

// ------------------------------------------------------------------------------------------------ engine sources

/// Version 0's `agent/mod.rs` (one text for every schema): generated for a two-table unit schema.
fn version_zero_text() -> String {
    let doc = r#"{"format": "gendb-sql-ast-v1", "status": "ok", "frontend": {"identity": "unit"}, "sql": "SELECT c FROM t",
        "schema": {"tables": [
            {"name": "t", "columns": [{"name": "c", "type": {"kind": "int4"}, "nullable": false}], "constraints": [{"kind": "key", "name": null, "primary": true, "columns": [0], "nulls_distinct": true, "deferrable": false, "initially_deferred": false}]},
            {"name": "u", "columns": [{"name": "e", "type": {"kind": "int8"}, "nullable": false}]}]},
        "output": {"names": ["c"], "columns": [{"type": {"kind": "int4"}, "nullable": false, "dscale": null}], "pg_types": ["int4"]},
        "root": 3, "nodes": [
          {"id": 0, "tag": "Table", "table": 0, "columns": [{"type": {"kind": "int4"}, "nullable": false, "dscale": null}]},
          {"id": 1, "tag": "Col", "index": 0, "type": {"type": {"kind": "int4"}, "nullable": false, "dscale": null}},
          {"id": 2, "tag": "Project", "exprs": [1], "input": 0, "columns": [{"type": {"kind": "int4"}, "nullable": false, "dscale": null}]},
          {"id": 3, "tag": "OrderedQuery", "body": 2, "keys": [], "limit": null, "offset": 0}]}"#;
    let Translation::Ok(doc) = decode(doc).unwrap() else { panic!("unit schema refused") };
    let schema = Instance::concrete(&doc).unwrap().doc.tables;
    let flats: Vec<_> = (0..schema.len()).map(|t| flat_storage(&schema, t).unwrap()).collect();
    let interfaces: Vec<Vec<FrameworkSource>> = flats.iter().map(|f| f.files.iter().filter(|x| x.path.starts_with(&f.name.interface_prefix())).cloned().collect()).collect();
    let uses: Vec<StorageUse<'_>> = flats.iter().zip(&interfaces).map(|(f, i)| StorageUse { name: &f.name, declaration: &f.declaration, interface: i }).collect();
    interpreter_engine(&schema, &uses).unwrap().remove(0).text
}

/// The line of version 0 that materializes the database.
const MATERIALIZE: &str = "    let edb = materialize_database(stores, Ghost(db));\n";

/// TRIAL FIXTURE: version 0 materializing every table `times` times (`times` 1 is version 0's code). The copies are
/// kept live through `either` (one of two equal databases), so the compiler cannot drop them; the proof is version 0's.
fn slowed(times: u32) -> String {
    let v0 = version_zero_text();
    assert_eq!(v0.matches(MATERIALIZE).count(), 1, "version 0 materializes the database once");
    if times == 1 {
        return v0;
    }
    let mut lines = String::from("    let mut edb = materialize_database(stores, Ghost(db));\n");
    for _ in 1..times {
        lines.push_str("    edb = either(edb, materialize_database(stores, Ghost(db)));\n");
    }
    let either = "/// TRIAL FIXTURE: one of two equal databases (both materializations stay live, so the compiler cannot drop one).\n\
                  fn either(a: EDatabase, b: EDatabase) -> (r: EDatabase)\n    ensures\n        r@ == a@ || r@ == b@,\n{\n    if a.tables.len() <= b.tables.len() { a } else { b }\n}\n\n\
                  /// The engine:";
    v0.replacen(MATERIALIZE, &lines, 1)
        .replacen("/// The engine:", either, 1)
        .replacen("use crate::exec::relational::schema::{lemma_db_wf_ts_ok, view_rows};", "use crate::exec::relational::schema::{lemma_db_wf_ts_ok, view_rows, EDatabase};", 1)
        .replacen("//! Version 0 of the general engine", &format!("//! TRIAL FIXTURE: version 0 materializing every table {times} times. Version 0 of the general engine"), 1)
}

/// The root of runs L, S and R: version 0 materializing every table eight times.
fn slowed_root(schema: &[TableDef], uses: &[StorageUse<'_>]) -> Result<Vec<FrameworkSource>, AssemblyError> {
    let mut files = interpreter_engine(schema, uses)?;
    files[0].text = slowed(8);
    Ok(files)
}

const SLOWED_ROOT_GENERATOR: &str = "trial-fixture-slowed-version-0-x8";
const SLOWED_ROOT_NOTES: &str = "TRIAL FIXTURE root: version 0 materializing every table eight times (engine::general_trial), so the trial's submissions have room to beat their parents";
const SLOWED_ROOT_NOTEBOOK: &str = "# Notes\n\n## Direction\n\nTrial fixture root: version 0 materializing every table eight times.\n\n## Design\n\nVersion 0 (the verified interpreter over the flat storage) with seven extra materializations.\n\n## Tried\n\nNothing.\n\n## Ideas\n\nMaterialize once.\n\n## Proof notes\n\nVersion 0's proof; the extra copies equal the bound database.\n";

// ------------------------------------------------------------------------------------------------ the scripted author

/// What one scripted call writes and submits.
#[derive(Clone, Copy, Debug)]
enum Code {
    /// Version 0 materializing every table this many times (1: version 0's code).
    Slowed(u32),
    /// A helper module with a text constant of template Q12 (refused at freeze: `template_constant`).
    TemplateConstant,
    /// A helper module naming a column of the schema (refused at freeze: `schema_name`).
    SchemaName,
    /// A helper module with a `static` item (refused at freeze: `static_item`).
    StaticItem,
    /// Version 0 materializing every table this many times, reading the flat storages plus a storage built from the flat
    /// storage of one table (a workspace storage, submitted with the engine).
    WithStorage(u32, TrialStorage),
}

/// The trial's storages built from an admitted flat storage (`built_from` it, `extends` it: its parts are kept unchanged
/// and linked), each adding one part after them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TrialStorage {
    /// The fixture `zoned`: a zone part holding the smallest key (8 bytes): the serving storage grows.
    Zoned,
    /// A part that is always empty: the serving storage does not grow.
    Marked,
}

impl TrialStorage {
    fn name(self) -> &'static str {
        match self {
            TrialStorage::Zoned => "zoned",
            TrialStorage::Marked => "marked",
        }
    }

    /// The interface (`stores/<name>/interface/mod.rs`) and builder (`builder/mod.rs`) texts.
    fn texts(self) -> (String, String) {
        let fixtures = repository().join("src/gendb/verification/tests/fixtures/general_storage");
        match self {
            TrialStorage::Zoned => (fs::read_to_string(fixtures.join("zoned_interface.rs")).unwrap(), fs::read_to_string(fixtures.join("zoned_builder.rs")).unwrap()),
            TrialStorage::Marked => (MARKED_INTERFACE.into(), MARKED_BUILDER.into()),
        }
    }

    /// The part it adds, as its manifest declares it.
    fn part(self) -> (&'static str, &'static str) {
        match self {
            TrialStorage::Zoned => ("ZONE I64: the smallest key of the table", "the smallest key: skip metadata over the table's own rows"),
            TrialStorage::Marked => ("MARK I64: an empty skip part (trial fixture)", "trial fixture: an empty skip part, it stores no value"),
        }
    }
}

/// TRIAL FIXTURE: the interface of storage `marked` (built from the flat storage of one table, keeping its parts and
/// adding one empty part, so it stores no new byte). Written over its declaration and GenDB's plain-columns vocabulary,
/// like the fixture `zoned` (`verification/tests/fixtures/general_storage`); it names no table or column.
const MARKED_INTERFACE: &str = r#"//! TRIAL FIXTURE (general engine line trial; framework test only, not an author output): the interface of storage
//! `marked`. It keeps the parts of the flat storage of one table unchanged (`extends`), states them with the
//! plain-columns vocabulary (`plain`, GenDB's `gendb-plain-columns-v1` text copied unchanged) by the declared column
//! types and a part layout given as data, and adds one empty part, so it stores no new byte. It names no table or column.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::Row;

pub mod plain;

verus! {

/// The parts kept from the flat storage (the declared columns: one key part, then two text columns of two parts).
pub const KEPT_PARTS: usize = 5;

/// The empty part, after the kept parts.
pub const MARK: usize = 5;

/// The part of each declared column among the kept parts (data: the declared column types, in order).
pub open spec fn layout() -> Seq<int> {
    seq![0int, 1int, 3int]
}

/// The parts represent `rels`, the one stored relation: the kept parts hold it plainly; the last part is empty.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& rels.len() == 1
    &&& parts.len() == KEPT_PARTS + 1
    &&& plain::plain_columns(parts, rels[0], super::declaration::stored_columns_t0(), layout())
    &&& parts[MARK as int] is I64
    &&& parts[MARK as int]->I64_0.len() == 0
}

/// Lossless: the kept parts determine the relation.
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires
        represents(parts, a),
        represents(parts, b),
    ensures
        a == b,
{
    plain::lemma_plain_columns_determine(parts, a[0], b[0], super::declaration::stored_columns_t0(), layout());
    assert(a =~= b);
}

} // verus!
"#;

/// TRIAL FIXTURE: the builder of storage `marked`: the flat parts kept, one empty part added; the kept parts restated
/// with `lemma_flat_plain` (by table id; no table or column name), as the `zoned` fixture builder does.
const MARKED_BUILDER: &str = r#"//! TRIAL FIXTURE (general engine line trial; framework test only, not an author output): the builder of storage
//! `marked`, built from the flat storage of its table and extending it: the flat parts are kept unchanged, and the
//! builder adds one empty part. It restates the kept parts with `lemma_flat_plain` (by table id; no table or column name).
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::gendb_entry::layout::{owned_parts_view, PartView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::sources::Stores;
use crate::gendb_entry::storage::{represents, stored_relations};
use crate::link::source::proj_columns;
use crate::schema::schema_spec;
use crate::sources_flat::{flat_layout, flat_part_count, flat_parts, lemma_flat_plain, lemma_flat_table_unique};
use crate::spec::value::Database;
use crate::stores::marked::declaration::{lemma_declared_schema, stored_cols_t0, stored_columns_t0, stored_table_t0};
use crate::stores::marked::interface::{layout, MARK};

verus! {

/// The table the storage keeps, by id (the storage's declaration states the same).
pub const TABLE: usize = 7;

/// What the declaration states: table `TABLE` and all of its columns in order, so its column types are the schema's
/// and its part layout is the flat storage's.
proof fn lemma_declared()
    ensures
        stored_table_t0() == TABLE as nat,
        stored_columns_t0() == schema_spec()[TABLE as int].columns,
        stored_cols_t0().len() == 3,
        forall|k: int| 0 <= k < 3 ==> #[trigger] stored_cols_t0()[k] == k,
        layout() == flat_layout(TABLE as int),
{
    lemma_declared_schema();
    let cols = stored_cols_t0();
    assert(cols =~= seq![0nat, 1nat, 2nat]);
    assert forall|k: int| 0 <= k < 3 implies #[trigger] cols[k] == k by {
        if k == 0 {} else if k == 1 {} else {}
    }
    assert(proj_columns(schema_spec()[TABLE as int], cols) =~= schema_spec()[TABLE as int].columns);
    assert forall|k: int| 0 <= k < 3 implies #[trigger] layout()[k] == flat_layout(TABLE as int)[k] by {
        if k == 0 {} else if k == 1 {} else {}
    }
    assert(layout() =~= flat_layout(TABLE as int));
}

/// Keep the flat parts, add the empty part (the derived storage entry's builder).
pub fn build(stores: &mut Stores, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        sources_ready(old(stores)@),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(p) ==> forall|db: Database| #[trigger] sources_bound(old(stores)@, db)
            ==> represents(storage_parts(old(stores)@, owned_parts_view(p@)), stored_relations(db)),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ghost sv = stores@;
    let ghost db = choose|db: Database| sources_bound(sv, db);
    let ghost flat = flat_parts(sv, TABLE as int);
    proof {
        lemma_declared();
        lemma_flat_plain(sv, db, TABLE as int);
    }
    let mark: Vec<i64> = Vec::new();
    let parts: Vec<OwnedPart> = vec![OwnedPart::I64(mark)];
    proof {
        let all = storage_parts(sv, owned_parts_view(parts@));
        assert(all =~= flat + seq![PartView::I64(Seq::<i64>::empty())]);
        assert(flat.len() == flat_part_count(TABLE as int));
        assert forall|other: Database| #[trigger] sources_bound(sv, other) implies represents(all, stored_relations(other)) by {
            lemma_flat_table_unique(sv, db, other, TABLE as int);
            let rows = other.tables[TABLE as int];
            let cols = stored_columns_t0();
            crate::stores::marked::interface::plain::lemma_proj_identity(rows, stored_cols_t0(), 3);
            assert(stored_relations(other)[0] == rows);
            assert forall|k: int| 0 <= k < cols.len() implies #[trigger] crate::stores::marked::interface::plain::plain_column(all, layout()[k], cols[k].ty, rows, k) by {
                let p = layout()[k];
                assert(crate::sources_flat::plain::plain_column(flat, flat_layout(TABLE as int)[k], schema_spec()[TABLE as int].columns[k].ty, rows, k));
                assert(all[p] == flat[p]);
                if p + 1 < flat.len() {
                    assert(all[p + 1] == flat[p + 1]);
                }
            }
            assert(all[MARK as int] == PartView::I64(Seq::<i64>::empty()));
        }
    }
    Ok(parts)
}

} // verus!
"#;

#[derive(Clone, Copy, Debug)]
struct Step {
    code: Code,
    direction: Option<&'static str>,
    next_session: Option<&'static str>,
    /// The call's transcript reports one completed automatic compaction.
    compaction: bool,
    /// After writing its durable receipt, the transport stops this process with SIGTERM (the user's stop).
    sigterm: bool,
}

const fn step(code: Code) -> Step {
    Step { code, direction: None, next_session: None, compaction: false, sigterm: false }
}

const B1_DIRECTION: &str = "b1 (trial): fewer materializations of the database per call; differs from b2 by removing work instead of reordering it";
const B2_DIRECTION: &str = "b2 (trial): a different number of materializations; differs from b1 to give the main line gains to merge";

/// Which run's script the scripted authors follow (the work order's `script`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Script {
    /// Run L ([`general_line_trial`]).
    LineTrial,
    /// Run S ([`stops::storage_registration_resumes_once`]).
    StorageRegistration,
}

impl Script {
    fn of_order(order: &Value) -> Script {
        match order["script"].as_str() {
            None | Some("L") => Script::LineTrial,
            Some("S") => Script::StorageRegistration,
            Some(other) => panic!("unknown trial script {other}"),
        }
    }
}

/// The scripted sessions of `script`: the steps of session `number` of `branch`, one per call (module documentation).
fn plan(script: Script, branch: &str, number: u32) -> Vec<Step> {
    match script {
        Script::LineTrial => line_trial_plan(branch, number),
        // Run S: b1's first submission reads the storage `marked` (no growth) with the copy materializing twice; the next
        // call has no step (an error receipt), which uses the budget.
        Script::StorageRegistration => match (branch, number) {
            ("b1", 1) => vec![Step { direction: Some(B1_DIRECTION), ..step(Code::WithStorage(2, TrialStorage::Marked)) }],
            _ => vec![],
        },
    }
}

/// Run L's scripted sessions (module documentation).
fn line_trial_plan(branch: &str, number: u32) -> Vec<Step> {
    match (branch, number) {
        ("b1", 1) => vec![Step { direction: Some(B1_DIRECTION), ..step(Code::Slowed(3)) }, Step { compaction: true, sigterm: true, ..step(Code::StaticItem) }],
        ("b1", 2) => vec![Step { compaction: true, ..step(Code::TemplateConstant) }],
        ("b1", 3) => vec![Step { compaction: true, ..step(Code::StaticItem) }],
        ("b1", 4) => vec![step(Code::Slowed(1)), step(Code::Slowed(2)), step(Code::TemplateConstant), Step { compaction: true, ..step(Code::SchemaName) }],
        ("b2", 1) => vec![step(Code::Slowed(5)), Step { direction: Some(B2_DIRECTION), next_session: Some("fresh"), ..step(Code::Slowed(5)) }],
        ("b2", 2) => vec![step(Code::Slowed(2))],
        ("b2", 3) => vec![step(Code::WithStorage(3, TrialStorage::Marked)), Step { compaction: true, ..step(Code::WithStorage(3, TrialStorage::Zoned)) }],
        _ => vec![],
    }
}

/// The scripted transport of one session (`authors(label, ..)`): its call `n` acts as step `n - 1` of [`plan`] (the
/// call id is the session ledger's, so a relaunch continues the script), saves its prompt and what it saw, writes a
/// `stream-json`-like transcript (`stdout.jsonl`) and a durable receipt before answering, so an interrupted call's
/// receipt is recovered as Claude Code's would be from its transcript.
struct TrialAuthor {
    label: String,
    engine_dir: PathBuf,
    script: Script,
}

const RECEIPT_FILE: &str = "scripted-receipt.json";

impl TrialAuthor {
    fn session(&self) -> SessionRecord {
        let (branch, number) = self.label.split_once("-session-").unwrap();
        read_json(&super::sessions::session_directory(&self.engine_dir, branch, number.parse().unwrap()).join(SESSION_FILE)).unwrap()
    }

    /// Write the step's code into the workspace: `agent/` holds `mod.rs` and at most one helper module; the manifest
    /// declares them, with the step's general-line fields and its own notes (so no two steps are the same submission).
    fn act(&self, workspace: &Path, step: &Step, label: &str) {
        let agent = workspace.join("engine/src/agent");
        for entry in fs::read_dir(&agent).unwrap().flatten() {
            if entry.file_name() != "mod.rs" {
                fs::remove_file(entry.path()).unwrap();
            }
        }
        let mut modules = vec![json!({"file":"mod.rs","role":"entry","items":["engine"]})];
        let helper = |name: &str, body: &str| -> Value {
            fs::write(agent.join(name), format!("//! TRIAL FIXTURE helper module.\nuse vstd::prelude::*;\n\nverus! {{\n\n{body}\n\n}} // verus!\n")).unwrap();
            json!({"file":name,"role":"helper","items":[]})
        };
        let mut storage = None;
        match step.code {
            Code::Slowed(times) => fs::write(agent.join("mod.rs"), slowed(times)).unwrap(),
            Code::TemplateConstant => modules.push(helper("priority.rs", "pub const HIGH_PRIORITY: &str = \"1-URGENT\";")),
            Code::SchemaName => modules.push(helper("columns.rs", "pub const L_SHIPDATE_POSITION: usize = 10;")),
            Code::StaticItem => modules.push(helper("calls.rs", "pub static CALLS: u64 = 0;")),
            Code::WithStorage(times, kind) => {
                fs::write(agent.join("mod.rs"), slowed(times)).unwrap();
                storage = Some(kind);
            }
        }
        let path = workspace.join(super::submission::MANIFEST_FILE);
        let mut manifest: Value = read_json(&path).unwrap();
        manifest["modules"] = json!(modules);
        // The flat storages always; a workspace storage only with its step.
        let mut uses: Vec<Value> = manifest["storage_uses"].as_array().unwrap().iter().filter(|u| u["admitted"].is_string()).cloned().collect();
        if let Some(kind) = storage {
            let region = uses.iter().find(|u| u["name"] == "flat_region").expect("the flat storage of region")["admitted"].clone();
            uses.push(json!({"name":kind.name(),"workspace":write_storage(workspace, kind, &region)}));
        }
        manifest["storage_uses"] = json!(uses);
        manifest["notes"] = json!(format!("trial step {label}: {:?}", step.code));
        let fields = manifest.as_object_mut().unwrap();
        for (key, value) in [("direction", step.direction), ("next_session", step.next_session)] {
            match value {
                Some(v) => fields.insert(key.into(), json!(v)),
                None => fields.remove(key),
            };
        }
        fields.insert("findings".into(), json!([format!("trial step {label}: {:?}", step.code)]));
        fs::write(&path, serde_json::to_vec_pretty(&manifest).unwrap()).unwrap();
    }
}

/// Write the workspace storage `kind` (`new-storages/<name>/`: its manifest, interface with the plain-columns vocabulary,
/// and builder), built from and extending the flat storage of region (admitted package `region`). Returns its manifest
/// path relative to the workspace. The manifest names the table and its columns (the scans read code, not manifests).
fn write_storage(workspace: &Path, kind: TrialStorage, region: &Value) -> String {
    let name = kind.name();
    let dir = workspace.join("new-storages").join(name);
    if dir.exists() {
        fs::remove_dir_all(&dir).unwrap();
    }
    let src = dir.join("crate/src");
    let (interface, builder) = kind.texts();
    fs::create_dir_all(src.join(format!("stores/{name}/interface"))).unwrap();
    fs::create_dir_all(src.join("builder")).unwrap();
    fs::write(src.join(format!("stores/{name}/interface/mod.rs")), interface).unwrap();
    fs::write(src.join(format!("stores/{name}/interface/plain.rs")), gendb_verification::obligations::PLAIN_COLUMNS).unwrap();
    fs::write(src.join("builder/mod.rs"), builder).unwrap();
    let (label, why) = kind.part();
    let manifest = json!({"format_version":1,"name":name,"crate_dir":"crate",
        "tables":[{"table":"region","columns":["r_regionkey","r_name","r_comment"]}],
        "parts":[label],
        "layout":{"summary":"the flat storage's parts kept unchanged and linked (extends), then one part","units":"rows; keys as stored","choice":"trial fixture"},
        "data_policy":[{"part":0,"table":"region","kind":"own_skip_metadata","columns":["r_regionkey"],"why":why}],
        "built_from":{"sources":[{"name":"flat_region","admitted":region}],"extends":"flat_region"}});
    fs::write(dir.join("verus-storage.json"), serde_json::to_vec_pretty(&manifest).unwrap()).unwrap();
    format!("new-storages/{name}/verus-storage.json")
}

impl AuthorTransport for TrialAuthor {
    fn capability(&self) -> Capability {
        Capability {
            transport: "scripted-trial".into(),
            executable: "none".into(),
            version: "1".into(),
            model: "none (scripted trial author; no provider)".into(),
            effort: "none".into(),
            persistent_sessions: true,
            hard_usd_cap: false,
            cost_semantics: format!("trial stub: {CALL_COST} dollar per call, per invocation"),
        }
    }

    fn usage_scope(&self) -> Option<UsageScope> {
        Some(UsageScope::Invocation)
    }

    fn provider_session_exists(&self, call_dir: &Path) -> bool {
        call_dir.join("stdout.jsonl").is_file()
    }

    fn recover_receipt(&self, call: &Call, _session_id: &str, call_dir: &Path, _workspace: &Path) -> Result<Option<Receipt>, String> {
        let path = call_dir.join(RECEIPT_FILE);
        if !path.is_file() {
            return Ok(None);
        }
        let receipt: Receipt = read_json(&path).map_err(|e| e.to_string())?;
        Ok((receipt.call_id == call.id).then_some(receipt))
    }

    fn invoke(&mut self, request: &AuthorCall) -> Receipt {
        fs::create_dir_all(request.call_dir).unwrap();
        fs::write(request.call_dir.join(crate::controller::layout::PROMPT_FILE), request.prompt).unwrap();
        let session = self.session();
        let index = request.call.id as usize - 1;
        let steps = plan(self.script, &session.branch, session.number);
        let workspace = request.workspace;
        let listing = |dir: &Path| -> Vec<String> {
            let mut names: Vec<String> = fs::read_dir(dir).into_iter().flatten().flatten().map(|e| e.file_name().to_string_lossy().into_owned()).collect();
            names.sort();
            names
        };
        let observation = json!({"label":self.label,"call":request.call.id,"resume":request.resume,"provider_session":request.session_id,"kind":session.kind,
            "seed":session.seed,"merge_from":session.merge_from,"scale":session.scale,"notes":fs::read_to_string(workspace.join("NOTES.md")).ok(),
            "versions":listing(&workspace.join(crate::prompts::engine_contract::VERSIONS_DIRECTORY)),"merge":listing(&workspace.join("merge")),
            "step":steps.get(index).map(|s| format!("{s:?}"))});
        write_json_atomic(&request.call_dir.join("trial-observation.json"), &observation).unwrap();
        let label = format!("{}-{}", self.label, request.call.id);
        let Some(step) = steps.get(index).copied() else {
            return Receipt { call_id: request.call.id, session_id: request.session_id.into(), ended_unix_ms: records::now_unix_ms(), elapsed_ms: 1,
                reported_cost_usd: Some(Money::parse(CALL_COST).unwrap()), billed_cost_usd: None, tokens: Some(Tokens::default()),
                outcome: format!("error: {label} has no scripted step"), raw_result: Some(json!({"scripted":true})), output: None, usage_scope: Some(UsageScope::Invocation) };
        };
        self.act(workspace, &step, &label);
        let usage = |tokens: u64| json!({"type":"assistant","parent_tool_use_id":null,"message":{"usage":{"input_tokens":10,"cache_read_input_tokens":tokens,"cache_creation_input_tokens":100,"output_tokens":20}}}).to_string();
        let mut transcript = vec![json!({"type":"system","subtype":"init","session_id":request.session_id}).to_string(), usage(20_000 * request.call.id)];
        if step.compaction {
            transcript.push(json!({"type":"system","subtype":"compact_boundary","compact_metadata":{"trigger":"auto","pre_tokens":900_000,"post_tokens":12_000}}).to_string());
            transcript.push(usage(12_000));
        }
        transcript.push(json!({"type":"result","subtype":"success","session_id":request.session_id,"total_cost_usd":CALL_COST,"scripted":true}).to_string());
        fs::write(request.call_dir.join("stdout.jsonl"), transcript.join("\n") + "\n").unwrap();
        let submission = CandidateSubmission { candidate_manifest: super::submission::MANIFEST_FILE.into(), rationale: format!("trial step {label}: {:?}", step.code),
            data_access_analysis: "every table read from its flat storage".into() };
        let receipt = Receipt {
            call_id: request.call.id,
            session_id: request.session_id.into(),
            ended_unix_ms: records::now_unix_ms(),
            elapsed_ms: 1,
            reported_cost_usd: Some(Money::parse(CALL_COST).unwrap()),
            billed_cost_usd: None,
            tokens: Some(Tokens::default()),
            outcome: "success".into(),
            raw_result: Some(json!({"session_id":request.session_id,"scripted":true,"step":format!("{step:?}")})),
            output: Some(json!(submission)),
            usage_scope: Some(UsageScope::Invocation),
        };
        write_json_atomic(&request.call_dir.join(RECEIPT_FILE), &receipt).unwrap();
        if step.sigterm {
            eprintln!("trial: {label} stops this process with SIGTERM after writing its receipt");
            // SAFETY: kill(2) on this process with a valid signal number; SIGTERM's default action ends the process.
            unsafe {
                libc::kill(libc::getpid(), libc::SIGTERM);
            }
            std::thread::sleep(std::time::Duration::from_secs(600));
        }
        receipt
    }
}

/// The trial's storage fixtures alone (no run): each is assembled as a storage crate built from the flat storage of
/// region and extending it (the derived storage generation), passes the general line's storage scan, and verifies whole
/// with `--no-cheating` (`run_verus`). A fast check of the fixtures before the trial submits them.
#[test]
#[ignore = "runs the pinned frontend and Verus on two storage crates; TMPDIR, GENDB_BUILD_LOCK, GENDB_TRIAL_DIR; -- --ignored"]
fn trial_storage_fixtures_verify() {
    use gendb_verification::obligations::{DeclaredSource, Derivation, StorageName, derived_storage_crate_files, plain_columns_interface_file, with_trusted_shim};
    use gendb_verification::verus::engine_rules::{EngineLine, EngineRuleSet, TemplateConstants};
    use gendb_verification::verus::{CodegenOptions, VerusMode, VerusOptions, VerusOutcome, freeze_framework_crate, run_verus};
    let dir = run_folder("storage-fixtures");
    let parser = SqlParser::from_environment().unwrap();
    let dataset: DatasetSpec = serde_json::from_str(TPCH_DATASET).unwrap();
    let (ddl_text, _) = dataset_ddl(&dataset, Some(&tpch_constraints()));
    fs::write(dir.join("schema.sql"), ddl_text).unwrap();
    fs::write(dir.join("probe.sql"), "SELECT r_regionkey FROM region").unwrap();
    let Translation::Ok(doc) = parser.translate(&dir.join("schema.sql"), &dir.join("probe.sql"), "postgres", &[]).unwrap().1 else { panic!("schema probe refused") };
    let schema = doc.tables;
    let region = schema.iter().position(|t| t.name == "region").unwrap();
    assert_eq!(region, 7, "the fixtures' table id");
    let flat = flat_storage(&schema, region).unwrap();
    let interface: Vec<FrameworkSource> = flat.files.iter().filter(|f| f.path.starts_with(&flat.name.interface_prefix())).cloned().collect();
    let sources = [StorageUse { name: &flat.name, declaration: &flat.declaration, interface: &interface }];
    let rules = EngineRuleSet::for_line(EngineLine::General, TemplateConstants::default(), &schema);
    let toolchain = VerusToolchain::from_env().unwrap();
    let mut records = vec![];
    for kind in [TrialStorage::Marked, TrialStorage::Zoned] {
        let name = StorageName::new(kind.name()).unwrap();
        let declaration = DeclaredSource::for_storage(&schema, &std::collections::BTreeMap::from([(region, BTreeSet::from([0usize, 1, 2]))])).unwrap();
        let mut files = derived_storage_crate_files(&schema, &name, &declaration, Derivation { sources: &sources, extends: Some(0) }, false).unwrap();
        let (own_interface, builder) = kind.texts();
        let own = [FrameworkSource { path: format!("{}mod.rs", name.interface_prefix()), text: own_interface }, plain_columns_interface_file(&name),
            FrameworkSource { path: "builder/mod.rs".into(), text: builder }];
        let findings: Vec<_> = own.iter().flat_map(|f| rules.scan_storage_source(&f.path, &f.text)).collect();
        assert_eq!(findings, vec![], "{name}: the general line's storage scan");
        files.extend(own);
        let files = with_trusted_shim(files, gendb_runtime::abi::GENDB_STORAGE_DERIVED_SHIM_SOURCE);
        let unscanned: Vec<&str> = files.iter().filter(|f| gendb_registry::author_definition(&f.path).is_none()).map(|f| f.path.as_str()).collect();
        let frozen = freeze_framework_crate(&files, &unscanned, &dir.join(kind.name()).join("frozen")).unwrap();
        let options = VerusOptions { crate_name: gendb_verification::obligations::STORAGE_CRATE_NAME.into(), codegen: CodegenOptions { opt_level: 1, target_cpu: None }, num_threads: Some(16) };
        let run = with_build_lock(|| run_verus(&toolchain, &frozen, &options, VerusMode::Verify, &dir.join(kind.name()).join("verus")).unwrap());
        assert!(matches!(run.outcome, VerusOutcome::Verified), "{name}: {} {}", run.detail, run.rendered_errors());
        records.push(json!({"storage":kind.name(),"verification":run.verification,"wall_ns":run.wall_ns}));
    }
    write_json_atomic(&dir.join("evidence.json"), &json!({"storages":records})).unwrap();
    eprintln!("storage fixtures: {}", dir.display());
}

// ------------------------------------------------------------------------------------------------ launches

/// One launch of the controller in a child process of this test binary ([`trial_child`]) or of the `gendb` executable.
#[derive(Debug)]
struct Launch {
    name: String,
    code: Option<i32>,
    signal: Option<i32>,
    log: PathBuf,
}

/// Run this test binary's [`trial_child`] with `child` (its JSON work order) and the crash point `crash`, to completion.
fn launch_child(name: &str, dir: &Path, child: &Value, crash: Option<&str>) -> Launch {
    let log = dir.join(format!("launch-{name}.log"));
    let mut command = child_command(name, dir, child);
    match crash {
        Some(point) => command.env("GENDB_TEST_CRASH_AT", point),
        None => command.env_remove("GENDB_TEST_CRASH_AT"),
    };
    run_logged(name, command, log)
}

/// This test binary running [`trial_child`] with the work order `child` (written as `<dir>/launch-<name>.json`).
fn child_command(name: &str, dir: &Path, child: &Value) -> Command {
    let order = dir.join(format!("launch-{name}.json"));
    write_json_atomic(&order, child).unwrap();
    let mut command = Command::new(std::env::current_exe().unwrap());
    command.args(["--exact", "engine::general_trial::trial_child", "--ignored", "--nocapture", "--test-threads", "1"]).env("GENDB_TRIAL_CHILD", &order);
    command
}

/// Run the `gendb` executable with `arguments`.
fn launch_cli(name: &str, dir: &Path, arguments: &[&std::ffi::OsStr]) -> Launch {
    let mut command = Command::new(worker());
    command.args(arguments).env_remove("GENDB_TEST_CRASH_AT");
    run_logged(name, command, dir.join(format!("launch-{name}.log")))
}

fn run_logged(name: &str, mut command: Command, log: PathBuf) -> Launch {
    use std::os::unix::process::ExitStatusExt;
    let out = fs::File::create(&log).unwrap();
    let started = records::now_unix_ms();
    let status = command.stdout(out.try_clone().unwrap()).stderr(out).status().unwrap();
    let launch = Launch { name: name.into(), code: status.code(), signal: status.signal(), log };
    eprintln!("launch {name}: code {:?} signal {:?} in {} ms ({})", launch.code, launch.signal, records::now_unix_ms() - started, launch.log.display());
    launch
}

/// The child side of a launch (`GENDB_TRIAL_CHILD` names its work order): `prepare` (run P's version 0),
/// `synthesize` (run L's loop with the scripted authors) or `live` (run R's loop with the real Claude Code author and
/// the framework-check prompt, [`live_stop`]). Not a test of its own: it does nothing without a work order.
#[test]
#[ignore = "the child process of the general-line trial; run by the trial's tests"]
fn trial_child() {
    let Some(order) = std::env::var_os("GENDB_TRIAL_CHILD") else { return };
    let order: Value = read_json(Path::new(&order)).unwrap();
    let request = WorkloadRequest::read(Path::new(order["request"].as_str().unwrap())).unwrap();
    let run = PathBuf::from(order["run"].as_str().unwrap());
    // As `gendb engine synthesize|prepare` does, before the async runtime's threads start: SIGTERM stops this launch's
    // children and ends it with SIGTERM (`gendb_runtime::process_stop`).
    gendb_runtime::process_stop::install(&run).unwrap();
    let script = Script::of_order(&order);
    let runtime = tokio::runtime::Runtime::new().unwrap();
    let summary = match order["mode"].as_str().unwrap() {
        "prepare" => runtime.block_on(prepare_general_run(&request, &run, &worker())),
        "synthesize" => {
            records::create_dir(&run).unwrap();
            let engine_dir = engine_directory(&run.canonicalize().unwrap());
            let authors = |label: &str, _: &Path| -> Result<TrialAuthor, String> { Ok(TrialAuthor { label: label.into(), engine_dir: engine_dir.clone(), script }) };
            let options = GeneralRunOptions { prompt: GENERAL_LINE_PROMPT, render_only: false };
            runtime.block_on(run_general_engine(&request, &run, authors, &worker(), options))
        }
        "live" => runtime.block_on(live_stop::run_live(&request, &run)),
        other => panic!("unknown mode {other}"),
    };
    gendb_runtime::process_stop::park_if_stopping();
    println!("{}", serde_json::to_string_pretty(&summary.unwrap()).unwrap());
}

/// The run's latest published summary.
fn latest_summary(run: &Path) -> Value {
    let pointer: Value = read_json(&run.join("summary-latest.json")).unwrap();
    read_json(&run.join(pointer["record"].as_str().unwrap())).unwrap()
}

/// A fresh run folder of this trial (`<trial>/<stamp>-<name>`), named in `<trial>/LATEST-<name>`.
fn run_folder(name: &str) -> PathBuf {
    let dir = trial_dir().join(format!("{}-{name}", records::now_unix_ms()));
    fs::create_dir_all(&dir).unwrap();
    fs::write(trial_dir().join(format!("LATEST-{name}")), format!("{}\n", dir.display())).unwrap();
    dir
}

// ------------------------------------------------------------------------------------------------ run P

#[test]
#[ignore = "runs the pinned frontend, Verus and the gendb worker on tiny data; TMPDIR, GENDB_WORKER, GENDB_BUILD_LOCK, GENDB_TRIAL_DIR; -- --ignored"]
fn version_zero_admission_resumes_without_a_second_admission() {
    let fixture = TrialFixture::prepare();
    let dir = run_folder("P");
    let library = dir.join("library");
    fixture.seed_library(&library);
    let original = [fixture.s1_flat_bytes * 4, fixture.s1_flat_bytes * 8];
    let request = fixture.request(&dir.join("request.json"), &library, &dir.join("home"), &fixture.s1_capture, original, "1", "never");
    let run = dir.join("run");
    let order = json!({"mode":"prepare","request":request,"run":run});
    // 1. Killed just before the library admission: the intent is written, nothing is admitted.
    let first = launch_child("1-crash-before-admission", &dir, &order, Some(CRASH_BEFORE_ADMISSION));
    assert_eq!(first.signal, Some(libc::SIGKILL), "{first:?}");
    let engine_dir = engine_directory(&run.canonicalize().unwrap());
    let seed = engine_dir.join("seed-v0");
    let store = ObjectStore::open_existing(&library).unwrap();
    assert!(seed.join(super::acceptance::ADMITTING_FILE).is_file() && !seed.join("admitted.json").is_file());
    assert_eq!(engine_versions(&store).unwrap().len(), 0, "nothing admitted before the crash");
    // 2. Resumed from the intent (no second Verus run or timing) and killed just after the admission.
    let second = launch_child("2-crash-after-admission", &dir, &order, Some(CRASH_AFTER_ADMISSION));
    assert_eq!(second.signal, Some(libc::SIGKILL), "{second:?}");
    assert_eq!(engine_versions(&store).unwrap().len(), 1, "admitted once from the intent");
    assert!(!seed.join("admitted.json").is_file(), "killed before the admission was recorded");
    // 3. The real `gendb engine prepare`: it adopts the admission, profiles version 0 and writes its records.
    let third = launch_cli("3-gendb-engine-prepare", &dir, &["engine".as_ref(), "prepare".as_ref(), request.as_os_str(), run.as_os_str()]);
    assert_eq!(third.code, Some(0), "{third:?}");
    let versions = engine_versions(&store).unwrap();
    assert_eq!(versions.len(), 1, "exactly one engine version: no second admission");
    let admitted: Value = read_json(&seed.join("admitted.json")).unwrap();
    assert_eq!(admitted["admission"]["library_version"], 1);
    assert!(admitted["admission"]["recovered"]["how"].as_str().unwrap().starts_with("adopted"), "{}", admitted["admission"]);
    assert_eq!(admitted["admission"]["admission"], json!(versions[0].admission_id));
    let frozen: Vec<String> = fs::read_dir(&seed).unwrap().flatten().map(|e| e.file_name().to_string_lossy().into_owned()).filter(|n| n.starts_with("frozen-")).collect();
    assert_eq!(frozen, ["frozen-0"], "one freeze: the resumed launches admitted the recorded intent");
    let tree = VersionTree::read(&engine_dir).unwrap();
    assert_eq!((tree.versions().count(), tree.main_line_head()), (1, Some(tree::ROOT_VERSION)));
    let v0 = engine_dir.join("versions").join(tree::ROOT_VERSION);
    for file in ["version.json", "node.json", "README.md", "code/agent/mod.rs", "manifest.json", "seed-manifest.json", "NOTES.md", "admission.json", "official-matrix.json", "score.json", "PROFILE.md"] {
        assert!(v0.join(file).is_file(), "v000 lacks {file}");
    }
    let version: Value = read_json(&v0.join("version.json")).unwrap();
    assert_eq!(version["origin"]["generator"], gendb_verification::obligations::INTERPRETER_ENGINE_GENERATOR);
    assert_eq!(version["profile"]["status"], "profiled", "{}", version["profile"]);
    assert_eq!(version["node"]["score"]["score"]["finished"].as_u64(), Some((TEMPLATES.len() * WORKERS.len()) as u64), "version 0 finishes every cell at s1");
    assert!(dir.join("home/engine/README.md").is_file() && dir.join("home/engine/TREE.md").is_file(), "the output home");
    let prepare: Value = read_json(&engine_dir.join("prepare.json")).unwrap();
    let evidence = json!({"fixture":fixture.dir,"run":run,"library":library,"launches":[format!("{first:?}"),format!("{second:?}"),format!("{third:?}")],"prepare":prepare,"admitted":admitted,
        "library_versions":versions.iter().map(|v| json!({"version":v.version,"admission":v.admission_id,"package":v.package_id})).collect::<Vec<_>>()});
    write_json_atomic(&dir.join("evidence.json"), &evidence).unwrap();
    eprintln!("run P: {}", dir.display());
}

// ------------------------------------------------------------------------------------------------ run L

#[test]
#[ignore = "runs the pinned frontend, Verus and the gendb worker on tiny data; TMPDIR, GENDB_WORKER, GENDB_BUILD_LOCK, GENDB_TRIAL_DIR; -- --ignored"]
fn general_line_trial() {
    let fixture = TrialFixture::prepare();
    let dir = run_folder("L");
    let library = dir.join("library");
    fixture.seed_library(&library);
    // Scale s2's flat assets into the run library, as a real move needs (the packages are current: no Verus run).
    let mut s2_dataset = fixture.dataset.clone();
    for table in &mut s2_dataset.tables {
        table.locations = vec![PathBuf::from(fixture.scales[1].locations[&table.name][0].as_str().unwrap())];
    }
    let s2_request = flat_request(&s2_dataset, &library, &dir.join("flat-s2-request.json"));
    let flat_s2 = dir.join("flat-s2");
    let prepared = launch_cli("0-gendb-prepare-flat-storage-s2", &dir, &["prepare-flat-storage".as_ref(), s2_request.as_os_str(), flat_s2.as_os_str()]);
    assert_eq!(prepared.code, Some(0), "{prepared:?}");
    let s2_record: Value = read_json(&flat_s2.join("flat-storage.json")).unwrap();
    assert!(s2_record["tables"].as_array().unwrap().iter().all(|t| t["created"].is_null()), "the s1 packages are current: no new flat package at s2");
    let s2_flat_bytes = s2_record["storage_bytes"].as_u64().unwrap();
    // s2's original data size sits between `marked` (a storage change at the plain storage's size) and `zoned` (8
    // bytes more): the first is accepted, the second refused. s1's is below the plain storage (version 0 is allowed as is).
    let original = [fixture.s1_flat_bytes / 2, s2_flat_bytes + 4];
    let request_path = fixture.request(&dir.join("request.json"), &library, &dir.join("home"), &flat_s2.join("data"), original, RUN_L_BUDGET, "first_session_of_each_branch");
    let request = WorkloadRequest::read(&request_path).unwrap();
    let run = dir.join("run");

    seed_slowed_root(&request, &run, &dir);
    let engine_dir = engine_directory(&run.canonicalize().unwrap());
    let store = ObjectStore::open_existing(&library).unwrap();
    let order = json!({"mode":"synthesize","request":request_path,"run":run});
    let mut launches = vec![];

    // 1. The move to s2, then b1's first submission, killed just after its admission.
    launches.push(launch_child("1-b1-admission-killed", &dir, &order, Some(CRASH_AFTER_ADMISSION)));
    assert_eq!(launches[0].signal, Some(libc::SIGKILL), "{:?}", launches[0]);
    let ladder: Value = read_json(&engine_dir.join(LADDER_FILE)).unwrap();
    assert_eq!((ladder["current"].as_u64(), ladder["moves"][0]["to"].as_str()), (Some(1), Some("s2")), "moved to s2 once v000 finished every cell at s1: {ladder}");
    assert_eq!(engine_versions(&store).unwrap().len(), 2, "v000 and b1's submission");
    // 2. Relaunch: the admission is adopted; the next call is stopped by SIGTERM.
    launches.push(launch_child("2-b1-call-stopped-by-sigterm", &dir, &order, None));
    assert_eq!(launches[1].signal, Some(libc::SIGTERM), "{:?}", launches[1]);
    assert_eq!(engine_versions(&store).unwrap().len(), 2, "no second admission after the relaunch");
    // 3. Relaunch: the receipt is recovered, the submission refused at freeze, the session ends (compaction). b2 starts
    //    at once (b1 has an evaluated submission): its first submission has no direction (refused), its second states
    //    one (accepted, not the main-line head: a merge is due) and asks for a fresh session. The run pauses after both
    //    first sessions.
    launches.push(launch_child("3-b1-ends-b2-first-session-pause", &dir, &order, None));
    assert_eq!(launches[2].code, Some(0), "{:?}", launches[2]);
    let paused = latest_summary(&run);
    assert_eq!(paused["status"], PAUSED, "{paused}");
    assert_eq!(engine_versions(&store).unwrap().len(), 3, "v000, b1's and b2's versions");
    // 4. The cadence switched to every session (not part of the run's identity): b1's fresh second session, and b2's
    //    merge session, killed just before its admission (its intent is written).
    set_cadence(&request_path, "every_session");
    launches.push(launch_child("4-b1-fresh-merge-killed-before-admission", &dir, &order, Some(CRASH_BEFORE_ADMISSION)));
    assert_eq!(launches[3].signal, Some(libc::SIGKILL), "{:?}", launches[3]);
    assert_eq!(engine_versions(&store).unwrap().len(), 3, "killed before the merge's admission");
    // 5. Relaunch: the merge is admitted from its intent and becomes the main-line head; b1's third session runs; the
    //    run pauses.
    launches.push(launch_child("5-merge-admitted-from-intent", &dir, &order, None));
    assert_eq!((launches[4].code, latest_summary(&run)["status"].as_str()), (Some(0), Some(PAUSED)), "{:?}", launches[4]);
    assert_eq!(engine_versions(&store).unwrap().len(), 4);
    // 6. b1's fourth session (the four submissions in turn) and b2's third; the budget stops the run.
    launches.push(launch_child("6-b1-in-turn-budget-stop", &dir, &order, None));
    assert_eq!(launches[5].code, Some(0), "{:?}", launches[5]);
    let summary = latest_summary(&run);
    assert_eq!((summary["status"].as_str(), summary["reason"].as_str()), (Some("stopped"), Some("budget_limit")), "{summary}");

    let checks = check_run_l(&dir, &run, &engine_dir, &store);
    let evidence = json!({"fixture":fixture.dir,"run":run,"library":library,"request":request_path,"original_data_bytes":original,"s2_flat_bytes":s2_flat_bytes,"s1_flat_bytes":fixture.s1_flat_bytes,
        "launches":launches.iter().map(|l| json!({"name":l.name,"code":l.code,"signal":l.signal,"log":l.log})).collect::<Vec<_>>(),"summary":summary,"checks":checks});
    write_json_atomic(&dir.join("evidence.json"), &evidence).unwrap();
    eprintln!("run L: {}", dir.display());
}

/// The root of runs L, S and R, seeded in this process: version 0 materializing every table eight times (a labeled
/// fixture), so the scripted submissions have room to beat their parent. Its record is `<dir>/root.json`.
fn seed_slowed_root(request: &WorkloadRequest, run: &Path, dir: &Path) {
    records::create_dir(run).unwrap();
    let root = run.canonicalize().unwrap();
    record_route(&root, Route::Engine).unwrap();
    record_request(&root, &serde_json::to_value(request).unwrap()).unwrap();
    let parser = SqlParser::from_environment().unwrap();
    let runtime = tokio::runtime::Runtime::new().unwrap();
    let prepared = runtime.block_on(prepare_engine_scale(request, 0, &root, &parser, &worker())).unwrap();
    let source = RootSource::fixture(SLOWED_ROOT_GENERATOR, slowed_root, SLOWED_ROOT_NOTES, SLOWED_ROOT_NOTEBOOK, "TRIAL FIXTURE: version 0 materializing every table eight times.");
    let seeded = seed_root_version(request, &prepared, &engine_directory(&root), &source).unwrap();
    assert_eq!(seeded["origin"]["generator"], SLOWED_ROOT_GENERATOR, "{seeded}");
    write_json_atomic(&dir.join("root.json"), &seeded).unwrap();
}

/// Run L's main-line decisions (`main-line.json` beside each accepted branch submission, `main-line.jsonl`, `TREE.md`,
/// the library's selections): `v001`'s parent `v000` was the main-line head, so its acceptance race decided (adopted,
/// no second timing); b1's version 0 code `b1_v0` (parent `v001`, while the merge `v003` was the head) was timed against
/// the head in a main-line race; b2's versions (parents `v000` and `v002`, never the head) took nothing from their
/// acceptance races. The adopted decision's record is the same as the raced one's but for its adoption note. Returns
/// the decisions.
fn check_main_line_decisions(engine_dir: &Path, store: &ObjectStore, tree: &VersionTree, session_dir: &dyn Fn(&str, u32) -> PathBuf, b1_v0: &str) -> Value {
    let frozen = |b: &str, n: u32, iteration: u32| crate::controller::layout::RunLayout::new(&session_dir(b, n)).iteration(iteration).join("frozen");
    let decided = |frozen: &Path| -> Value { read_json(&frozen.join("main-line.json")).unwrap() };
    let evaluations = |frozen: &Path| -> Vec<PathBuf> {
        fs::read_dir(frozen).unwrap().flatten().filter(|e| e.file_name().to_string_lossy().starts_with("evaluation")).map(|e| e.path()).collect()
    };
    // v001: the acceptance race adopted; no evaluation of it ran a main-line timing.
    let v001_frozen = frozen("b1", 1, 1);
    let v001 = decided(&v001_frozen);
    let admitted: Value = read_json(&v001_frozen.join("admitted.json")).unwrap();
    let acceptance_race = admitted["record"]["race"].as_str().unwrap();
    assert_eq!((v001["changed"].as_bool(), v001["head"].as_str(), v001["previous"].as_str()), (Some(true), Some("v001"), Some("v000")), "{v001}");
    assert_eq!((v001["adopted"]["from"].as_str(), v001["adopted"]["race"].as_str(), v001["race"].as_str()), (Some(tree::ADOPTED_ACCEPTANCE_RACE), Some(acceptance_race), Some(acceptance_race)), "{v001}");
    assert!(evaluations(&v001_frozen).iter().all(|e| !e.join("main-line").exists()), "v001 was not timed again for the main line");
    // b1_v0: a main-line race against the merge v003.
    let raced = decided(&frozen("b1", 4, 1));
    assert_eq!((raced["changed"].as_bool(), raced["head"].as_str(), raced["previous"].as_str()), (Some(true), Some(b1_v0), Some("v003")), "{raced}");
    assert!(raced["adopted"].is_null() && raced["race"].as_str().unwrap().ends_with("main-line/race.json") && Path::new(raced["race"].as_str().unwrap()).is_file(), "{raced}");
    // The same decision record but for the adoption note.
    let fields = |d: &Value| -> Vec<String> { d.as_object().unwrap().keys().filter(|k| *k != "adopted").cloned().collect() };
    assert_eq!((fields(&v001), &v001["reason"]), (fields(&raced), &raced["reason"]));
    // b2's versions: their parents were never the main-line head.
    let unadopted: Vec<Value> = [frozen("b2", 1, 2), frozen("b2", 3, 1)].iter().map(|f| decided(f)).collect();
    assert!(unadopted.iter().all(|d| d["adopted"].is_null() && d["changed"] == false), "{unadopted:?}");
    // main-line.jsonl, TREE.md and the library's selections say the same.
    let changes: Vec<(Option<&str>, Option<&str>)> = tree.main_line.iter().map(|c| (c.adopted.as_deref(), c.race.as_deref().and_then(Path::to_str))).collect();
    assert_eq!(changes[1], (Some(tree::ADOPTED_ACCEPTANCE_RACE), Some(acceptance_race)), "{changes:?}");
    assert_eq!(changes[3], (None, raced["race"].as_str()), "{changes:?}");
    let markdown = fs::read_to_string(engine_dir.join("TREE.md")).unwrap();
    assert!(markdown.contains("- v001 (race, at s2, after v000; timing adopted from its acceptance race)\n"), "{markdown}");
    assert!(markdown.contains(&format!("- {b1_v0} (race, at s2, after v003)\n")), "{markdown}");
    let reasons: Vec<String> = engine_selections(store).unwrap().into_iter().map(|(_, s)| s.reason).collect();
    assert_eq!((reasons[1].as_str(), reasons[3].clone()), ("race, timing adopted from its acceptance race (v001)", format!("race ({b1_v0})")), "{reasons:?}");
    json!({"v001":v001,b1_v0:raced,"b2":unadopted,"selection_reasons":reasons})
}

/// The records of run L agree with each other and with the plan (module documentation); returns what was checked.
fn check_run_l(dir: &Path, run: &Path, engine_dir: &Path, store: &ObjectStore) -> Value {
    let tree = VersionTree::read(engine_dir).unwrap();
    let ids: Vec<&str> = tree.versions().map(|n| n.id.as_str()).collect();
    assert_eq!(ids, ["v000", "v001", "v002", "v003", "v004", "v005"], "the versions in library order");
    // The library: one admission per version, in order, no gap; lineage and parents agree with the tree.
    let versions = engine_versions(store).unwrap();
    assert_eq!(versions.len(), ids.len(), "one library version per tree version (no double admission)");
    for (node, version) in tree.versions().zip(&versions) {
        assert_eq!(tree::version_number(&node.id).unwrap() + 1, version.version, "{}", node.id);
        let lineage = engine_lineage(store, version).unwrap().unwrap();
        assert_eq!(lineage.kind, match node.kind { NodeKind::FrameworkGenerated => "framework_generated", NodeKind::Branch => "branch", NodeKind::Merge => "merge", NodeKind::StageSeed | NodeKind::WorkloadSeed => "framework_generated" }, "{}", node.id);
        let parents: Vec<ContentId> = node.parents.iter().map(|p| versions[tree::version_number(p).unwrap() as usize].package_id).collect();
        assert_eq!(lineage.parents, parents, "{}: lineage parents", node.id);
    }
    let node = |id: &str| tree.node(id).unwrap_or_else(|| panic!("{id}"));
    assert_eq!((node("v001").branch.as_str(), node("v001").parents.clone()), ("b1", vec!["v000".to_string()]));
    assert_eq!((node("v002").branch.as_str(), node("v002").parents.clone()), ("b2", vec!["v000".to_string()]));
    assert_eq!((node("v003").kind, node("v003").parents.clone()), (NodeKind::Merge, vec!["v001".to_string(), "v002".to_string()]), "the merge took b2's head into the main line");
    // The last two versions came from concurrent sessions, in either order: b1's version 0 code over its head v001 (the
    // slowed copy), and b2's copy with the storage that does not grow, over its head v002.
    let last = |branch: &str| tree.versions().filter(|n| n.branch == branch).last().unwrap().clone();
    let (b1_v0, b2_marked) = (last("b1"), last("b2"));
    assert_eq!(b1_v0.parents, ["v001"], "b1's fourth session was seeded from the slowed copy");
    assert_eq!(b2_marked.parents, ["v002"]);
    assert!(["v004", "v005"].contains(&b1_v0.id.as_str()) && ["v004", "v005"].contains(&b2_marked.id.as_str()));
    assert!(node("v002").direction.as_deref() == Some(B2_DIRECTION) && node("v001").direction.as_deref() == Some(B1_DIRECTION));
    // The attempts and why.
    let reasons: Vec<(String, String)> = tree.attempts().map(|n| (n.id.clone(), n.reason.clone().unwrap_or_default())).collect();
    let has = |id: &str, text: &str| reasons.iter().any(|(i, r)| i == id && r.contains(text));
    assert!(has("b1-a001", "static_item"), "{reasons:?}");
    assert!(has("b1-a002", "template_constant"), "{reasons:?}");
    assert!(has("b2-a001", "branch_direction_required"), "{reasons:?}");
    assert!(has("b1-a003", "static_item"), "{reasons:?}");
    assert!(has("b1-a004", &format!("not better than its parent {}", b1_v0.id)), "the slowed copy is rejected against b1's new head: {reasons:?}");
    assert!(has("b2-a002", "storage_budget_exceeded") && has("b2-a002", "exceed the original data size at s2"), "the growing storage is refused: {reasons:?}");
    assert!(has("b1-a005", "template_constant") && has("b1-a006", "schema_name"), "{reasons:?}");
    assert_eq!(reasons.len(), 8, "{reasons:?}");
    // The main line: the library's selections and main-line.jsonl agree; the accepted merge was the head.
    let selections = engine_selections(store).unwrap();
    assert_eq!(selections.len(), tree.main_line.len());
    for ((_, selection), change) in selections.iter().zip(&tree.main_line) {
        assert_eq!(selection.package, versions[tree::version_number(&change.version).unwrap() as usize].package_id, "{}", change.version);
    }
    let heads: Vec<(&str, &str)> = tree.main_line.iter().map(|c| (c.version.as_str(), c.reason.as_str())).collect();
    assert_eq!(heads, [("v000", "version_0"), ("v001", "race"), ("v003", "merge"), (b1_v0.id.as_str(), "race")], "{heads:?}");
    // Sessions: their kinds, how each ended, and the recovery records.
    let ended = |branch: &str| -> Vec<(u32, SessionKind, String)> {
        branch_sessions(engine_dir, branch).unwrap().into_iter().map(|s| (s.record.number, s.record.kind, s.reason().unwrap_or("open").to_string())).collect()
    };
    let b1 = ended("b1");
    let b2 = ended("b2");
    assert_eq!(b1.iter().map(|(n, k, _)| (*n, *k)).collect::<Vec<_>>(), [(1, SessionKind::Branch), (2, SessionKind::Branch), (3, SessionKind::Branch), (4, SessionKind::Branch)], "{b1:?}");
    assert_eq!(b2.iter().map(|(n, k, _)| (*n, *k)).collect::<Vec<_>>(), [(1, SessionKind::Branch), (2, SessionKind::Merge), (3, SessionKind::Branch)], "{b2:?}");
    assert!(b1[..3].iter().all(|(_, _, r)| r == "fresh_session") && b2[0].2 == "fresh_session", "{b1:?} {b2:?}");
    assert_eq!(b2[1].2, "first_eligible_candidate", "an accepted merge ends its session: {b2:?}");
    let session_dir = |b: &str, n: u32| super::sessions::session_directory(engine_dir, b, n);
    let call_dir = |b: &str, n: u32, call: u64| crate::controller::layout::RunLayout::new(&session_dir(b, n)).call(call);
    let interruption = fs::read_dir(call_dir("b1", 1, 2)).unwrap().flatten().any(|e| e.file_name().to_string_lossy().starts_with("interruption-"));
    assert!(interruption, "the SIGTERM'd call was found dispatched and its receipt recovered");
    let observation = |b: &str, n: u32, call: u64| -> Value { read_json(&call_dir(b, n, call).join("trial-observation.json")).unwrap() };
    assert_eq!(observation("b1", 1, 2)["resume"], true, "b1's second call continued the provider session");
    assert_eq!(observation("b1", 2, 1)["resume"], false, "a fresh session after the compaction");
    assert_eq!(observation("b2", 1, 2)["resume"], true);
    assert_eq!((observation("b2", 2, 1)["kind"].as_str(), observation("b2", 2, 1)["merge_from"].as_str()), (Some("merge"), Some("v002")));
    assert!(observation("b2", 2, 1)["merge"].as_array().unwrap().iter().any(|f| f == "README.md"), "the merge inputs are in the workspace");
    assert_eq!(observation("b1", 4, 1)["seed"], "v001", "b1's fourth session starts from its head, the slowed copy");
    // Admission records: b1's first admission adopted after the SIGKILL, b2's admitted from its intent.
    let admitted = |b: &str, n: u32, iteration: u32| -> Value {
        read_json(&crate::controller::layout::RunLayout::new(&session_dir(b, n)).iteration(iteration).join("frozen").join("admitted.json")).unwrap()
    };
    assert!(admitted("b1", 1, 1)["record"]["admission"]["recovered"]["how"].as_str().unwrap().starts_with("adopted"), "b1's admission was adopted");
    assert!(admitted("b2", 2, 1)["record"]["admission"]["recovered"].is_null(), "the merge was admitted from its intent after the crash (not adopted)");
    let merge_frozen = crate::controller::layout::RunLayout::new(&session_dir("b2", 2)).iteration(1).join("frozen");
    assert!(merge_frozen.join(super::acceptance::ADMITTING_FILE).is_file());
    let main_line = check_main_line_decisions(engine_dir, store, &tree, &session_dir, &b1_v0.id);
    // Every version and attempt folder is complete; the findings log has one entry per evaluated submission.
    for n in tree.versions().filter(|n| n.id != tree::ROOT_VERSION) {
        let d = n.directory(engine_dir);
        for file in ["version.json", "node.json", "README.md", "code/agent/mod.rs", "manifest.json", "seed-manifest.json", "NOTES.md", "admission.json", "race.json", "receipts.json",
            "variant-answers.json"] {
            assert!(d.join(file).is_file(), "{} lacks {file}", n.id);
        }
        assert!(!d.join("PROFILE.md").exists(), "{}: the development evaluation profiles nothing after an admission", n.id);
        assert!(d.join("cells").join(format!("{}.json", n.scale)).is_file(), "{} lacks its cells", n.id);
        let version: Value = read_json(&d.join("version.json")).unwrap();
        let (serving, budget) = (version["storage"]["serving_bytes"].as_u64().unwrap(), version["storage"]["budget_bytes"].as_u64().unwrap());
        let decision = version["storage"]["decision"].as_str().unwrap();
        assert!(decision.starts_with("plain storage only at s2") || (serving <= budget && decision.starts_with("changed storage within the original data size at s2")),
            "{}: {serving} serving bytes, budget {budget}: {decision}", n.id);
    }
    for n in tree.attempts() {
        for file in ["attempt.json", "node.json", "receipts.json"] {
            assert!(n.directory(engine_dir).join(file).is_file(), "{} lacks {file}", n.id);
        }
    }
    let findings = tree::read_lines(&engine_dir.join(tree::FINDINGS_FILE)).unwrap();
    let logged: BTreeSet<&str> = findings.iter().filter_map(|f| f["node"].as_str()).collect();
    let evaluated: BTreeSet<&str> = tree.nodes.iter().filter(|n| n.id != tree::ROOT_VERSION).map(|n| n.id.as_str()).collect();
    assert_eq!((findings.len(), &logged), (evaluated.len(), &evaluated), "one finding per evaluated submission");
    // Every accepted version's finding states its measured effect, also when its admission was resumed (b1's adopted
    // `v001`, the merge admitted from its intent).
    let without_effect: Vec<&str> = findings.iter().filter(|f| f["accepted"] == true && f["effect"].is_null()).filter_map(|f| f["node"].as_str()).collect();
    assert_eq!(without_effect, Vec::<&str>::new(), "accepted versions whose finding has no effect");
    let findings_markdown = fs::read_to_string(engine_dir.join(tree::FINDINGS_MARKDOWN)).unwrap();
    for n in tree.versions().filter(|n| n.id != tree::ROOT_VERSION) {
        let entry = findings_markdown.split("\n## ").find(|e| e.starts_with(&format!("{} ", n.id))).unwrap_or_else(|| panic!("FINDINGS.md lacks {}", n.id));
        assert!(entry.contains("- Effect: "), "FINDINGS.md: {} has no Effect line:\n{entry}", n.id);
    }
    let markdown = fs::read_to_string(engine_dir.join("TREE.md")).unwrap();
    assert!(tree.nodes.iter().all(|n| markdown.contains(&format!("| {} |", n.id))), "TREE.md lists every node");
    // The output home mirrors the records.
    let home = dir.join("home/engine");
    for file in ["README.md", "TREE.md", "FINDINGS.md", "tree.json"] {
        assert!(home.join(file).is_file(), "the output home lacks {file}");
    }
    for n in &tree.nodes {
        assert!(home.join(if n.accepted { "versions" } else { "attempts" }).join(&n.id).is_dir(), "the output home lacks {}", n.id);
    }
    // The ladder stays at s2, the last scale.
    let summary = latest_summary(run);
    assert!(summary["scale"]["last_check"]["decision"].as_str().unwrap().contains("the last scale"), "{}", summary["scale"]);
    // The storages built from the flat storage: the one that does not grow was admitted with b2's version (registered in
    // the library, read by it); the growing one was refused at the storage step, before any timing.
    let marked: Value = read_json(&b2_marked.directory(engine_dir).join("version.json")).unwrap();
    let uses: Vec<&str> = marked["storage"]["uses"].as_array().unwrap().iter().filter_map(|u| u["name"].as_str()).collect();
    assert!(uses.contains(&"marked") && uses.contains(&"flat_region"), "{uses:?}");
    let growth = tree.node("b2-a002").unwrap().clone();
    assert!(growth.score.is_none(), "refused before the interleaved timing");
    let growth_attempt: Value = read_json(&growth.directory(engine_dir).join("attempt.json")).unwrap();
    // The rendered prompts for review.
    let prompts = dir.join("prompts");
    fs::create_dir_all(&prompts).unwrap();
    for (name, b, n, call) in [("1-first-call-b1-session-1", "b1", 1, 1), ("2-continued-call-b1-session-1", "b1", 1, 2), ("3-fresh-session-b1-session-2", "b1", 2, 1),
        ("4-first-call-b2-session-1", "b2", 1, 1), ("5-merge-session-b2-session-2", "b2", 2, 1), ("6-b1-session-4-seeded-from-the-slowed-copy", "b1", 4, 1)]
    {
        fs::copy(call_dir(b, n, call).join(crate::controller::layout::PROMPT_FILE), prompts.join(format!("{name}.md"))).unwrap();
    }
    let read = |name: &str| fs::read_to_string(prompts.join(format!("{name}.md"))).unwrap();
    assert!(read("1-first-call-b1-session-1").contains("# Goal") && read("1-first-call-b1-session-1").contains("# HANDOFF: YOUR BRANCH SO FAR"));
    assert!(read("2-continued-call-b1-session-1").starts_with("# EVALUATION OF YOUR SUBMISSION") && !read("2-continued-call-b1-session-1").contains("# Goal"));
    assert!(read("3-fresh-session-b1-session-2").contains("# Goal") && read("3-fresh-session-b1-session-2").contains("# HANDOFF: YOUR BRANCH SO FAR"));
    json!({"versions":ids,"attempts":reasons,"main_line":heads,"main_line_decisions":main_line,"sessions":{"b1":b1.iter().map(|(n, k, r)| json!([n, k, r])).collect::<Vec<_>>(),"b2":b2.iter().map(|(n, k, r)| json!([n, k, r])).collect::<Vec<_>>()},
        "findings":findings.len(),"no_growth_storage":{"version":b2_marked.id,"uses":uses,"decision":marked["storage"]["decision"]},
        "growth_storage":{"attempt":growth.id,"reason":growth.reason,"evaluation":growth_attempt["evaluation"]},"prompts":prompts})
}
