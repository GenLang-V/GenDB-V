//! An engine library end to end at tiny scale: admission, serving of ad hoc
//! SQL with an echo, and the engine's three refusals.
//!
//! - **Storages**: the eight generated flat TPC-H storages (`obligations::flat_storage`, the SF100 dataset's column
//!   types), each verified and compiled whole with the pinned Verus, published and admitted with `physical_only`
//!   revision 2 standing; each asset built by the storage's stored library over one tiny database (the PostgreSQL-checked
//!   case `tpch_all22_cases/q06.json`) for a fixture capture.
//! - **Engine**: a TEST FIXTURE engine (`GENDB_FIXTURE_ENGINE`, not part of this repository: materialize every table,
//!   then the verified interpreter), frozen with a fresh generation of the engine crate over the admitted storages and
//!   verified and compiled whole. Framework test only; it says nothing about engine speed.
//! - **Qualification**: Q01 and Q06 at their visible bindings v0..v2, one call each at 64 workers, compared under
//!   `formal_proofs` with saved answers computed by the verified SQLSpec evaluator of each bound statement on the same
//!   database; the variants of Q01 and Q06 whose bytes differ from their template's run at 64 workers, 1 warm + 1 hot,
//!   through the timing harness's variant matrix.
//! - **Admission** under the library budget lock (`engine_library::admit_engine_version`), then **serving**
//!   (`engine::serving::serve_statement`): an ad hoc parameterized SQL statement (its answer equal to the verified
//!   evaluator's), then `Refused` (worker counts 0 and 65), `Malformed` (undecodable bytes) and `ParamRefused` (a
//!   decodable statement that is not well typed).
//!
//! Needs the pinned Verus and frontend, and `GENDB_WORKER` (a `gendb` executable of this build). Work goes under
//! `GENDB_ENGINE_TEST_WORK` (default `TMPDIR`); verified storage and engine builds are cached there by exact
//! sources. With `GENDB_BUILD_LOCK`, every Verus run holds that lock.

use gendb_artifacts::{ContentId, ObjectStore};
use gendb_frontend::ast::{AstDocument, TableDef, Translation};
use gendb_frontend::columns::declared_columns;
use gendb_frontend::params::ParamRequest;
use gendb_frontend::parser::SqlParser;
use gendb_runtime::abi::GENDB_STORAGE_SHIM_SOURCE;
use gendb_runtime::answer::rows_json;
use gendb_runtime::worker::{StorageUseInput, WorkerInput};
use gendb_sqlspec::codec::{HostTables, HostValue, RunOutcome};
use gendb_sqlspec::evaluator::EvaluatorLibrary;
use gendb_sqlspec::fixtures::{Fixture, fixtures_dir};
use gendb_storage::import::DatasetSpec;
use gendb_storage::io::PartAccess;
use gendb_storage::versions::{CapturedTable, CurrentCapture};
use gendb_synthesis::engine::serving::{EngineServeStatement, EngineServing, serve_statement};
use gendb_synthesis::engine::timing::{CellRequest, EngineCellRunner, EngineStatement, MatrixKind, VariantOf, run_matrix};
use gendb_synthesis::query::source_items::requires_ensures;
use gendb_synthesis::storage::engine_library::{admit_engine_version, engine_assets};
use gendb_synthesis::storage::library_lock::{BUDGET_LOCK, LibraryLock};
use gendb_synthesis::storage::policy::StoredDataPolicy;
use gendb_synthesis::storage::registration::register_storage;
use gendb_verification::admission::bindings::BenchmarkBinding;
use gendb_verification::admission::engine::{
    ENGINE_QUALIFICATION_KIND, EngineCandidate, EngineRunner, EngineSchema, TemplateCheck, VariantCheck, distinct_variants, engine_framework_files,
    qualify_templates,
};
use gendb_verification::admission::execution::CandidateRunner;
use gendb_verification::admission::qualification::CandidateModule;
use gendb_verification::admission::storage::{StorageCandidate, StorageSchema, build_storage_asset, publish_storage, run_constraints_digest};
use gendb_verification::admission::validation::{SavedAnswerSource, ValidationPolicy};
use gendb_verification::admission::{AdmissionError, IntegrityConstraints, cases::inline_columns, dataset_ddl};
use gendb_verification::obligations::{ENGINE_CRATE_NAME, FlatStorage, STORAGE_CRATE_NAME, flat_storage, storage_crate_files, with_trusted_shim};
use gendb_verification::reference::{BuildOptions, BuildStatus, build_evaluator};
use gendb_verification::verus::engine_rules::TemplateConstants;
use gendb_verification::verus::{AuthorRoot, CodegenOptions, FrameworkSource, VerusMode, VerusOptions, VerusOutcome, VerusToolchain, freeze_author_crate, run_verus};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

/// The SF100 dataset's tables and column types (the completed SF100 runs' request): integers bigint, decimals
/// numeric(15,2), text and date; all NOT NULL. Parquet locations are not needed: nothing is imported.
const TPCH_DATASET: &str = r#"{"tables": [
  {"name": "lineitem", "format": "Parquet", "locations": [], "fields": [
    {"name": "l_orderkey", "ty": "I64", "nullable": false}, {"name": "l_partkey", "ty": "I64", "nullable": false},
    {"name": "l_suppkey", "ty": "I64", "nullable": false}, {"name": "l_linenumber", "ty": "I64", "nullable": false},
    {"name": "l_quantity", "ty": {"Decimal": {"p": 15, "s": 2}}, "nullable": false},
    {"name": "l_extendedprice", "ty": {"Decimal": {"p": 15, "s": 2}}, "nullable": false},
    {"name": "l_discount", "ty": {"Decimal": {"p": 15, "s": 2}}, "nullable": false},
    {"name": "l_tax", "ty": {"Decimal": {"p": 15, "s": 2}}, "nullable": false},
    {"name": "l_returnflag", "ty": "Utf8", "nullable": false}, {"name": "l_linestatus", "ty": "Utf8", "nullable": false},
    {"name": "l_shipdate", "ty": "Date32", "nullable": false}, {"name": "l_commitdate", "ty": "Date32", "nullable": false},
    {"name": "l_receiptdate", "ty": "Date32", "nullable": false}, {"name": "l_shipinstruct", "ty": "Utf8", "nullable": false},
    {"name": "l_shipmode", "ty": "Utf8", "nullable": false}, {"name": "l_comment", "ty": "Utf8", "nullable": false}]},
  {"name": "orders", "format": "Parquet", "locations": [], "fields": [
    {"name": "o_orderkey", "ty": "I64", "nullable": false}, {"name": "o_custkey", "ty": "I64", "nullable": false},
    {"name": "o_orderstatus", "ty": "Utf8", "nullable": false}, {"name": "o_totalprice", "ty": {"Decimal": {"p": 15, "s": 2}}, "nullable": false},
    {"name": "o_orderdate", "ty": "Date32", "nullable": false}, {"name": "o_orderpriority", "ty": "Utf8", "nullable": false},
    {"name": "o_clerk", "ty": "Utf8", "nullable": false}, {"name": "o_shippriority", "ty": "I64", "nullable": false},
    {"name": "o_comment", "ty": "Utf8", "nullable": false}]},
  {"name": "customer", "format": "Parquet", "locations": [], "fields": [
    {"name": "c_custkey", "ty": "I64", "nullable": false}, {"name": "c_name", "ty": "Utf8", "nullable": false},
    {"name": "c_address", "ty": "Utf8", "nullable": false}, {"name": "c_nationkey", "ty": "I64", "nullable": false},
    {"name": "c_phone", "ty": "Utf8", "nullable": false}, {"name": "c_acctbal", "ty": {"Decimal": {"p": 15, "s": 2}}, "nullable": false},
    {"name": "c_mktsegment", "ty": "Utf8", "nullable": false}, {"name": "c_comment", "ty": "Utf8", "nullable": false}]},
  {"name": "part", "format": "Parquet", "locations": [], "fields": [
    {"name": "p_partkey", "ty": "I64", "nullable": false}, {"name": "p_name", "ty": "Utf8", "nullable": false},
    {"name": "p_mfgr", "ty": "Utf8", "nullable": false}, {"name": "p_brand", "ty": "Utf8", "nullable": false},
    {"name": "p_type", "ty": "Utf8", "nullable": false}, {"name": "p_size", "ty": "I64", "nullable": false},
    {"name": "p_container", "ty": "Utf8", "nullable": false}, {"name": "p_retailprice", "ty": {"Decimal": {"p": 15, "s": 2}}, "nullable": false},
    {"name": "p_comment", "ty": "Utf8", "nullable": false}]},
  {"name": "partsupp", "format": "Parquet", "locations": [], "fields": [
    {"name": "ps_partkey", "ty": "I64", "nullable": false}, {"name": "ps_suppkey", "ty": "I64", "nullable": false},
    {"name": "ps_availqty", "ty": "I64", "nullable": false}, {"name": "ps_supplycost", "ty": {"Decimal": {"p": 15, "s": 2}}, "nullable": false},
    {"name": "ps_comment", "ty": "Utf8", "nullable": false}]},
  {"name": "supplier", "format": "Parquet", "locations": [], "fields": [
    {"name": "s_suppkey", "ty": "I64", "nullable": false}, {"name": "s_name", "ty": "Utf8", "nullable": false},
    {"name": "s_address", "ty": "Utf8", "nullable": false}, {"name": "s_nationkey", "ty": "I64", "nullable": false},
    {"name": "s_phone", "ty": "Utf8", "nullable": false}, {"name": "s_acctbal", "ty": {"Decimal": {"p": 15, "s": 2}}, "nullable": false},
    {"name": "s_comment", "ty": "Utf8", "nullable": false}]},
  {"name": "nation", "format": "Parquet", "locations": [], "fields": [
    {"name": "n_nationkey", "ty": "I64", "nullable": false}, {"name": "n_name", "ty": "Utf8", "nullable": false},
    {"name": "n_regionkey", "ty": "I64", "nullable": false}, {"name": "n_comment", "ty": "Utf8", "nullable": false}]},
  {"name": "region", "format": "Parquet", "locations": [], "fields": [
    {"name": "r_regionkey", "ty": "I64", "nullable": false}, {"name": "r_name", "ty": "Utf8", "nullable": false},
    {"name": "r_comment", "ty": "Utf8", "nullable": false}]}
]}"#;

/// The templates qualified here, and the generation identity of the engine crate.
const TEMPLATES: [&str; 2] = ["Q01", "Q06"];
const GENERATION_IDENTITY: &str = "schema engine";
const ALLOWANCE: Option<u64> = Some(1 << 40);

fn repository() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).ancestors().nth(3).expect("<repository>/src/gendb/synthesis").to_path_buf()
}

/// Run `f` holding the build lock `GENDB_BUILD_LOCK` exclusively, when that variable names a lock file.
fn with_build_lock<T>(f: impl FnOnce() -> T) -> T {
    let Some(path) = std::env::var_os("GENDB_BUILD_LOCK") else { return f() };
    let file = std::fs::OpenOptions::new().create(true).append(true).open(&path).unwrap();
    use std::os::fd::AsRawFd;
    // SAFETY: flock on a file descriptor this function owns; released when `file` is dropped (closed).
    assert_eq!(unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX) }, 0, "flock {}", PathBuf::from(&path).display());
    let result = f();
    drop(file);
    result
}

fn base_dir() -> PathBuf {
    std::env::var_os("GENDB_ENGINE_TEST_WORK").or_else(|| std::env::var_os("TMPDIR")).map(PathBuf::from).expect("GENDB_ENGINE_TEST_WORK or TMPDIR")
}

/// Every file of a frozen crate (path and text) as one JSON text: the cache key of its verified build.
fn sources_json(root: &Path) -> String {
    fn walk(dir: &Path, prefix: &str, out: &mut BTreeMap<String, String>) {
        for entry in std::fs::read_dir(dir).unwrap() {
            let entry = entry.unwrap();
            let name = format!("{prefix}{}", entry.file_name().to_string_lossy());
            if entry.file_type().unwrap().is_dir() {
                walk(&entry.path(), &format!("{name}/"), out);
            } else {
                out.insert(name, std::fs::read_to_string(entry.path()).unwrap());
            }
        }
    }
    let mut out = BTreeMap::new();
    walk(&root.join("src"), "", &mut out);
    serde_json::to_string(&out).unwrap()
}

/// The frozen crate of `framework` with the author roots `roots`, verified and compiled whole: `(frozen root, run
/// record)`. Reused from `<cache>/<name>-*` when an earlier run froze byte-equal sources (the fresh freeze is then
/// removed).
fn verified_crate(toolchain: &VerusToolchain, framework: &[FrameworkSource], roots: &[AuthorRoot<'_>], crate_name: &str, cache: &Path, name: &str) -> (PathBuf, Value) {
    let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = cache.join(format!("{name}-{nanos}"));
    let frozen = freeze_author_crate(framework, roots, &dir.join("frozen")).unwrap_or_else(|e| panic!("{name}: {e}"));
    let key = sources_json(&frozen.root);
    for entry in std::fs::read_dir(cache).unwrap() {
        let earlier = entry.unwrap().path();
        let matches = earlier.file_name().unwrap().to_string_lossy().starts_with(&format!("{name}-")) && earlier != dir;
        if matches && std::fs::read_to_string(earlier.join("sources.json")).ok().as_deref() == Some(key.as_str()) {
            let run: Value = serde_json::from_str(&std::fs::read_to_string(earlier.join("run.json")).unwrap()).unwrap();
            if Path::new(run["artifact"].as_str().unwrap_or_default()).is_file() {
                remove_read_only(&dir);
                return (earlier.join("frozen"), run);
            }
        }
    }
    let options = VerusOptions { crate_name: crate_name.into(), codegen: CodegenOptions { opt_level: 1, target_cpu: None }, num_threads: Some(16) };
    let run = with_build_lock(|| run_verus(toolchain, &frozen, &options, VerusMode::VerifyAndCompile, &dir.join("verus")).unwrap());
    assert_eq!(run.outcome, VerusOutcome::Compiled, "{name}: {} {}", run.detail, run.rendered_errors());
    let record = run.record();
    std::fs::write(dir.join("run.json"), serde_json::to_vec_pretty(&record).unwrap()).unwrap();
    std::fs::write(dir.join("sources.json"), key).unwrap();
    (frozen.root, record)
}

/// Remove a directory tree frozen read-only (directories made writable first; file modes untouched).
fn remove_read_only(root: &Path) {
    use std::os::unix::fs::PermissionsExt;
    fn open_up(dir: &Path) {
        std::fs::set_permissions(dir, std::fs::Permissions::from_mode(0o755)).unwrap();
        for entry in std::fs::read_dir(dir).unwrap() {
            let entry = entry.unwrap();
            if entry.file_type().unwrap().is_dir() {
                open_up(&entry.path());
            }
        }
    }
    open_up(root);
    std::fs::remove_dir_all(root).unwrap();
}

/// Write `files` under `root` (paths relative to `src/` of the crate they belong to).
fn write_files(root: &Path, files: &[FrameworkSource]) {
    for f in files {
        let path = root.join(&f.path);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, &f.text).unwrap();
    }
}

/// The verified SQLSpec evaluator's rows of `doc` on `tables`.
fn evaluator_rows(toolchain: &VerusToolchain, doc: &AstDocument, dir: &Path, tables: &HostTables) -> Vec<Vec<HostValue>> {
    let build = with_build_lock(|| build_evaluator(toolchain, doc, &dir.join("ast.json"), &dir.join("build"), &BuildOptions::default()).unwrap());
    assert_eq!(build.status, BuildStatus::Ok, "reference build {}", build.record);
    match EvaluatorLibrary::load(build.library.as_ref().unwrap()).unwrap().run(tables).unwrap() {
        RunOutcome::Rows(rows) => rows,
        other => panic!("the reference answered {other:?}"),
    }
}

/// Rows in the saved-answer format (integers as numbers, numerics `{"dec"}`, dates `{"date"}`, text as strings).
fn saved_rows(rows: &[Vec<HostValue>]) -> Value {
    let pg = rows_json(rows).unwrap();
    json!(rows.iter().zip(pg).map(|(row, texts)| row.iter().zip(texts).map(|(value, text)| match value {
        HostValue::Num { .. } => json!({"dec": text}),
        HostValue::Date(_) => json!({"date": text}),
        _ => text,
    }).collect::<Vec<_>>()).collect::<Vec<_>>())
}

struct Template {
    name: String,
    sql: String,
    parameters: Vec<ParamRequest>,
    bindings: Vec<BenchmarkBinding>,
}

fn template(name: &str) -> Template {
    let dir = repository().join("src/gendb/fixtures/tpch/templates");
    let index: Value = serde_json::from_str(&std::fs::read_to_string(dir.join("templates.json")).unwrap()).unwrap();
    let visible: Value = serde_json::from_str(&std::fs::read_to_string(repository().join("output/tpch-sf100/bindings/visible.json")).unwrap()).unwrap();
    let entry = &index["templates"][name];
    let bindings = visible["queries"][name]
        .as_array()
        .unwrap()
        .iter()
        .map(|b| BenchmarkBinding { name: b["binding_id"].as_str().unwrap().into(), arguments: b["arguments"].as_array().unwrap().iter().map(|a| a.as_str().unwrap().into()).collect() })
        .collect();
    Template { name: name.into(), sql: std::fs::read_to_string(dir.join(entry["sql"].as_str().unwrap())).unwrap(), parameters: serde_json::from_value(entry["parameters"].clone()).unwrap(), bindings }
}

/// The variant cells of the timing harness, each run through `EngineRunner::cell` (B4 wires the same way).
struct VariantCells<'a> {
    engine: &'a EngineRunner<'a>,
    checks: BTreeMap<String, &'a TemplateCheck>,
}

impl EngineCellRunner for VariantCells<'_> {
    fn run_cell(&self, cell: CellRequest<'_>, work: &Path) -> Result<Value, AdmissionError> {
        let check = self.checks[cell.statement.name()];
        self.engine.cell(check, &cell.statement.binding, &cell.statement.ast, cell.workers, cell.calls, work, None)
    }
}

#[test]
#[ignore = "runs the pinned Verus (8 storages, the engine, 7 reference evaluators), the frontend and the gendb worker; set GENDB_WORKER; -- --ignored. Admission refuses the fixture engine since the whole-statement evaluator rule applies to engines (it calls exec_ordered): needs an admissible fixture engine"]
fn engine_admission_serving_and_refusals_at_tiny_scale() {
    let worker = PathBuf::from(std::env::var_os("GENDB_WORKER").expect("GENDB_WORKER: the gendb executable"));
    let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let work = base_dir().join(format!("engine-tiny-{}-{nanos}", std::process::id()));
    let cache = base_dir().join("engine-tiny-cache");
    std::fs::create_dir_all(&work).unwrap();
    std::fs::create_dir_all(&cache).unwrap();
    let toolchain = VerusToolchain::from_env().unwrap();
    let parser = SqlParser::from_environment().unwrap();
    let runner = CandidateRunner { worker: worker.clone() };
    let mut evidence = json!({"work": work});

    // The dataset, its declared constraints and the schema they translate to.
    let dataset: DatasetSpec = serde_json::from_str(TPCH_DATASET).unwrap();
    let constraints: IntegrityConstraints =
        serde_json::from_str(&std::fs::read_to_string(repository().join("src/gendb/fixtures/tpch/integrity-constraints.json")).unwrap()).unwrap();
    let (ddl, omitted) = dataset_ddl(&dataset, Some(&constraints));
    assert!(omitted.is_empty());
    std::fs::write(work.join("schema.sql"), &ddl).unwrap();
    std::fs::write(work.join("probe.sql"), "SELECT r_regionkey FROM region").unwrap();
    let Translation::Ok(probe) = parser.translate(&work.join("schema.sql"), &work.join("probe.sql"), "postgres", &[]).unwrap().1 else { panic!("schema probe refused") };
    let schema: Vec<TableDef> = probe.tables.clone();
    let frontend = probe.frontend.clone();
    let store = ObjectStore::open(work.join("library")).unwrap();
    let policy = StoredDataPolicy::PhysicalOnly { eligible_storages: vec![] };

    // The tiny database and its fixture capture.
    let case = Fixture::load(&fixtures_dir().join("pg_reference/tpch_all22_cases/q06.json")).unwrap();
    let database = case.database_for(&probe).unwrap();
    let capture = CurrentCapture {
        tables: schema
            .iter()
            .enumerate()
            .map(|(t, def)| CapturedTable { table: def.name.clone(), source_version: "tiny-v1".into(), row_order: "tiny-r1".into(), rows: database[t].len() as u64, ordinals: (0..def.columns.len()).collect() })
            .collect(),
    };

    // 1. The eight flat storages: verified, published, built over the tiny database, admitted under physical_only.
    let declared = run_constraints_digest(&schema).unwrap();
    let clause_text = |text: &str, name: &str| requires_ensures(text, name);
    let flats: Vec<FlatStorage> = (0..schema.len()).map(|t| flat_storage(&schema, t).unwrap()).collect();
    let mut uses = vec![];
    for flat in &flats {
        let name = flat.name.as_str();
        let framework = with_trusted_shim(storage_crate_files(&schema, &flat.name, &flat.declaration, false).unwrap(), GENDB_STORAGE_SHIM_SOURCE);
        let sources = work.join("storage-sources").join(name);
        write_files(&sources, &flat.files);
        let interface = format!("stores/{name}/interface");
        let roots = [AuthorRoot { crate_directory: &interface, source: &sources.join(&interface) }, AuthorRoot { crate_directory: "builder", source: &sources.join("builder") }];
        let (frozen, run) = verified_crate(&toolchain, &framework, &roots, STORAGE_CRATE_NAME, &cache, name);
        let schema_view = StorageSchema { tables: &schema, ddl: &ddl, frontend: &frontend };
        let candidate = StorageCandidate { name: &flat.name, declaration: &flat.declaration, uses_declared_constraints: false, derivation: None, frozen_root: &frozen, verus_run: &run, readers: vec![], flat: false };
        let published = publish_storage(&store, schema_view, &candidate, &clause_text).unwrap();
        let table_id = flat.declaration.tables[0].table_id;
        let selection = BTreeMap::from([(table_id, (0..schema[table_id].columns.len()).collect::<BTreeSet<usize>>())]);
        let input = WorkerInput::Inline { columns: inline_columns(&declared_columns(&schema, &selection).unwrap(), &database).unwrap() };
        let asset = build_storage_asset(&store, &runner, published.package, &capture, declared, input, 1, &work.join("asset-builds").join(name)).unwrap();
        let data_policy: Vec<Value> = flat.parts.iter().enumerate().map(|(i, p)| json!({"part":i,"table":flat.table,"kind":"base_payload","columns":[p.column],"why":"the flat copy of the column"})).collect();
        let description = json!({"storage_policy":"physical_only","storage_policy_revision":2,"data_policy":data_policy,"registered_by":"engine_tiny test"});
        register_storage(&store, name, published.package, asset.id, &[asset.asset.evidence], &description).unwrap();
        uses.push(gendb_artifacts::verus::VerusStorageUseV1 { name: name.into(), package: published.package });
    }
    let (inputs, assets): (Vec<StorageUseInput>, Vec<ContentId>) = engine_assets(&store, &uses, &capture).unwrap();
    evidence["storages"] = json!(uses);

    // 2. The fixture engine: frozen with a fresh generation over the admitted storages, verified and compiled whole.
    let framework = engine_framework_files(&store, &schema, &uses, GENERATION_IDENTITY).unwrap();
    let agent = work.join("engine-sources/agent");
    std::fs::create_dir_all(&agent).unwrap();
    std::fs::copy(std::env::var_os("GENDB_FIXTURE_ENGINE").expect("GENDB_FIXTURE_ENGINE: the fixture engine's agent/mod.rs"), agent.join("mod.rs")).unwrap();
    let (frozen, run) = verified_crate(&toolchain, &framework, &[AuthorRoot { crate_directory: "agent", source: &agent }], ENGINE_CRATE_NAME, &cache, "engine");
    let library = PathBuf::from(run["artifact"].as_str().unwrap());
    evidence["engine_verification"] = run["verification"].clone();

    // 3. Saved answers of the verified evaluator, then qualification of Q01 and Q06 at v0..v2.
    let templates: Vec<Template> = TEMPLATES.iter().map(|t| template(t)).collect();
    let mut saved = vec![];
    for t in &templates {
        let unbound = TemplateCheck::prepare(&parser, &dataset, Some(&constraints), &ValidationPolicy::default(), &t.name, &t.name, &t.sql, &t.parameters, &t.bindings, &work.join("statements").join(format!("{}-reference", t.name))).unwrap();
        for b in &t.bindings {
            let dir = work.join("reference").join(format!("{}-{}", t.name, b.name));
            let rows = evaluator_rows(&toolchain, &unbound.ast(&b.name).unwrap().document, &dir, &database);
            std::fs::write(dir.join("answer.json"), serde_json::to_vec(&saved_rows(&rows)).unwrap()).unwrap();
            saved.push(SavedAnswerSource { query: t.name.clone(), binding: b.name.clone(), engine: "verified_evaluator".into(), description: "SQLSpec reference evaluator on the tiny database".into(), path: dir.join("answer.json"), rows_pointer: String::new() });
        }
    }
    let validation = ValidationPolicy::FormalProofs { numeric_relative_tolerance: "0".into(), required_engines: vec!["verified_evaluator".into()], saved_answers: saved };
    let checks: Vec<TemplateCheck> = templates
        .iter()
        .map(|t| TemplateCheck::prepare(&parser, &dataset, Some(&constraints), &validation, &t.name, &t.name, &t.sql, &t.parameters, &t.bindings, &work.join("statements").join(&t.name)).unwrap())
        .collect();
    let engine = EngineRunner { runner: &runner, library: &library, uses: &inputs, access: PartAccess::default(), limits: None, answer_bound: None };
    let qualification = qualify_templates(&engine, &checks, &work.join("qualification")).unwrap();
    assert_eq!((qualification["status"].as_str(), qualification["cells_compared"].as_u64()), (Some("saved_answers_agree"), Some(6)), "{qualification:#}");

    // 4. The variants of Q01 and Q06: those with bytes of their own run at 64 workers, 1 warm + 1 hot.
    let manifest: Value = serde_json::from_str(&std::fs::read_to_string(repository().join("src/gendb/fixtures/tpch/engine-variants/manifest.json")).unwrap()).unwrap();
    let variants: Vec<VariantCheck> = manifest["variants"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|v| TEMPLATES.contains(&v["template"].as_str().unwrap()))
        .map(|v| {
            let t = templates.iter().find(|t| t.name == v["template"]).unwrap();
            let sql = std::fs::read_to_string(repository().join("src/gendb/fixtures/tpch/engine-variants").join(v["file"].as_str().unwrap())).unwrap();
            let id = v["id"].as_str().unwrap();
            let check = TemplateCheck::prepare(&parser, &dataset, Some(&constraints), &validation, id, &t.name, &sql, &t.parameters, &t.bindings, &work.join("statements").join(id)).unwrap();
            VariantCheck { id: id.into(), kind: v["kind"].as_str().unwrap().into(), template: t.name.clone(), check }
        })
        .collect();
    let (distinct, same_ast) = distinct_variants(&checks, &variants, "v0").unwrap();
    let statements: Vec<EngineStatement> = distinct
        .iter()
        .map(|(v, ast)| EngineStatement { template: v.template.clone(), variant: Some(VariantOf { id: v.id.clone(), kind: v.kind.clone() }), binding: "v0".into(), ast: ast.bytes.clone() })
        .collect();
    let cells = VariantCells { engine: &engine, checks: variants.iter().map(|v| (v.id.clone(), &v.check)).collect() };
    let matrix = run_matrix(&cells, MatrixKind::Variants, &statements, &[64], &work.join("variants"), || Ok::<_, String>(())).unwrap();
    assert!(matrix.unchecked_cells().is_empty(), "every variant returns its template's saved answers");
    let variant_record = json!({"run":statements.iter().map(|s| s.name()).collect::<Vec<_>>(),"same_ast":same_ast,"matrix":matrix});

    // 5. Admission under the library's budget lock: the storage policy of the uses, then every record.
    let constants = TemplateConstants::from_templates_json(&repository().join("src/gendb/fixtures/tpch/templates/templates.json")).unwrap();
    let lock = LibraryLock::acquire(&store, BUDGET_LOCK).unwrap();
    let candidate = EngineCandidate {
        frozen_root: &frozen,
        verus_run: &run,
        uses: uses.clone(),
        generation_identity: GENERATION_IDENTITY,
        constants: &constants,
        modules: vec![CandidateModule { file: "mod.rs".into(), role: "entry".into(), items: vec![] }],
        evidence: vec![(ENGINE_QUALIFICATION_KIND, qualification.clone()), ("gendb.verus.engine-variants.v1", variant_record.clone())],
        assets: assets.clone(),
    };
    let schema_view = EngineSchema { tables: &schema, ddl: &ddl, frontend: &frontend };
    let admitted = admit_engine_version(&lock, &store, &capture, &policy, ALLOWANCE, schema_view, candidate).unwrap();
    drop(lock);
    assert_eq!(admitted.version, 1);
    evidence["admission"] = admitted.record();

    // 6. Serving from the library: ad hoc SQL with a parameter, then the three refusals.
    let resolved = gendb_artifacts::verus::resolve_engine(&store, None).unwrap().unwrap();
    assert!(resolved.selected && resolved.version.package_id == admitted.package);
    let serving = EngineServing { store: &store, engine: &resolved, capture: &capture, policy: &policy, parser: &parser, access: PartAccess::default(), worker: &worker, work: &work.join("serving") };
    let ad_hoc_sql = "SELECT l_returnflag, l_linestatus, count(*) AS n, sum(l_quantity) AS q FROM lineitem WHERE l_shipdate <= $1 GROUP BY l_returnflag, l_linestatus ORDER BY l_returnflag, l_linestatus";
    let parameters: Vec<ParamRequest> = serde_json::from_value(json!([{"index":1,"type":"date","binding":{"free":{}}}])).unwrap();
    let ad_hoc = EngineServeStatement { sql: Some(ad_hoc_sql.into()), parameters: parameters.clone(), arguments: vec!["1998-09-02".into()], ast_hex: None };
    let served = serve_statement(&serving, &ad_hoc, &[1, 4], 0).unwrap();
    let reference = {
        let check = TemplateCheck::prepare(&parser, &dataset, Some(&constraints), &ValidationPolicy::default(), "ad_hoc", "ad_hoc", ad_hoc_sql, &parameters,
            &[BenchmarkBinding { name: "v0".into(), arguments: vec!["1998-09-02".into()] }], &work.join("statements/ad_hoc")).unwrap();
        rows_json(&evaluator_rows(&toolchain, &check.ast("v0").unwrap().document, &work.join("reference/ad_hoc"), &database)).unwrap()
    };
    for cell in &served {
        assert_eq!((cell["status"].as_str(), cell["echo"]["verdict"].as_str(), cell["answer"]["status"].as_str()), (Some("executed"), Some("equal"), Some("ok")), "{cell:#}");
        assert_eq!(cell["ast"]["sha256"].as_str().map(str::len), Some(64));
        assert_eq!(cell["answer"]["rows"], json!(reference), "the engine's rows equal the verified evaluator's");
    }
    let refused = serve_statement(&serving, &ad_hoc, &[0, 65], 1).unwrap();
    assert!(refused.iter().all(|c| c["answer"]["status"] == "refused" && c["echo"]["verdict"] == "not_run"), "{refused:#?}");
    let malformed = serve_statement(&serving, &EngineServeStatement { sql: None, parameters: vec![], arguments: vec![], ast_hex: Some("4753514c4153543109".into()) }, &[1], 2).unwrap();
    assert_eq!((malformed[0]["answer"]["status"].as_str(), malformed[0]["echo"]["engine"].as_str(), malformed[0]["echo"]["verdict"].as_str()), (Some("malformed"), Some("(Malformed)"), Some("no_host_document")), "{malformed:#?}");
    let mut table_99 = b"GSQLAST1".to_vec();
    table_99.push(0);
    table_99.extend(99u32.to_le_bytes());
    table_99.extend(0u32.to_le_bytes());
    table_99.push(0);
    table_99.extend(0u64.to_le_bytes());
    let hex: String = table_99.iter().map(|b| format!("{b:02x}")).collect();
    let unsupported = serve_statement(&serving, &EngineServeStatement { sql: None, parameters: vec![], arguments: vec![], ast_hex: Some(hex) }, &[1], 3).unwrap();
    assert_eq!((unsupported[0]["answer"]["status"].as_str(), unsupported[0]["echo"]["engine"].as_str()), (Some("param_refused"), Some("(OrderedQuery (Table 99) [] none 0)")), "{unsupported:#?}");
    evidence["serving"] = json!({"ad_hoc":served,"refused":refused,"malformed":malformed,"param_refused":unsupported,"reference_rows":reference});
    evidence["qualification"] = qualification;
    evidence["variants"] = variant_record;
    std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", work.join("evidence.json").display());
}
