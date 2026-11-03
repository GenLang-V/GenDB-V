//! Engine crates (fixed engine entry `gendb-verus-engine-entry-v1`) end to end on tiny data, with version 0 of the
//! general engine.
//!
//! Version 0 (`obligations::interpreter_engine`, identity `gendb-interpreter-engine-v0`) is framework code generated in
//! source: its `agent/mod.rs`, the same text for every schema, reads every table through the crate's generated flat
//! access module (`obligations::flat_tables`, `crate::flat_tables`) over the flat storage of every table
//! (`obligations::flat_storage`) and answers with SQLSpec's verified interpreter (`exec_ordered`). It is the cheapest
//! complete engine and infeasible at scale; here it checks the framework (the entry, the AST codec, the crate assembly,
//! the flat access, the shim, the host ABI and the worker's engine job) and is itself checked.
//!
//! Every test needs the pinned Verus (`GENDB_VERUS_HOME`, default `<repository>/toolchains`) and the pinned frontend
//! Python, and runs with `--ignored`. Work directories go under `GENDB_ENGINE_TEST_WORK` (default: the Cargo target's
//! tmp directory). A compiled engine is reused from `<work>/engine-cache/<name>` when its frozen sources are byte-equal
//! (each check of the proof otherwise runs Verus again). With `GENDB_BUILD_LOCK` set to a lock file, every Verus run
//! takes it exclusively (`flock`), so the tests share the machine with other builders one Verus writer at a time.
//!
//! 1. [`version_0_verifies_whole_and_the_negative_fixture_fails`]: version 0 over the eight flat TPC-H storages (the
//!    SF100 dataset's column types, the 15 TPC-H integrity constraints declared), with the embedded engine toolkit
//!    (`engine_link/**`) and the flat access module, verifies and compiles whole with `--no-cheating`, 0 errors; the
//!    negative fixture (version 0 whose engine answers empty rows without computing them) fails verification. Its
//!    `agent/mod.rs` passes the general line's engine rules over the TPC-H template constants and schema names, and the
//!    schema-engine line refuses it by the whole-statement evaluator rule only.
//! 2. [`version_0_verifies_for_a_second_schema`]: version 0 generated for a second, unrelated schema (3 tables with
//!    integer, bigint, numeric, date, text, varchar and char columns; one foreign key) verifies whole, 0 errors; and a
//!    storage crate built from that schema's flat storage of one table, which carries `sources_flat.rs` and reads it,
//!    verifies whole, 0 errors.
//! 3. [`engine_calls_round_trip_and_answer_as_the_reference`] (also needs the `gendb` executable as the worker,
//!    `GENDB_WORKER`): every TPC-H template (`src/gendb/fixtures/tpch/templates`) at its visible bindings v0, v1 and v2
//!    (`output/tpch-sf100/bindings/visible.json`) is substituted and encoded (`gendb_frontend::engine_encode`); a worker
//!    child's engine job echoes each AST, and the echo equals the host's rendering of the bound document
//!    (`gendb_sqlspec::evaluator::echo_text`). Then, on each template's own tiny FK-closed database
//!    (`sqlspec/tests/fixtures/pg_reference/tpch_all22_cases/qNN.json`, written as flat assets), version 0's answer at
//!    v0 equals the verified reference evaluator's (`reference::build_evaluator` of the bound document, run on the same
//!    database).
//! 4. Three coverage statements (constructors the templates do not use:
//!    SELECT DISTINCT, negation, NULL and boolean literals, IS NULL, LEFT JOIN, EXISTS, NOT IN, COUNT(DISTINCT), date to
//!    timestamp with an interval, integer division, SUBSTRING, EXTRACT(MONTH/DAY), ORDER BY DESC NULLS LAST with LIMIT and
//!    OFFSET) round-trip the same way, undecodable bytes are answered `Malformed` (echo `(Malformed)`) and a decodable
//!    statement that is not well typed (`SELECT * FROM` table 99) `ParamRefused`
//!    ([`engine_coverage_statements_and_refusals`]; no reference build). Its evidence records which codec constructors
//!    and operator values the encoded statements (the 66 template instances and the coverage statements) exercised.
//! 5. [`limited_cells_are_recorded_unfinished_on_the_general_line`] (also `GENDB_WORKER`): admission cells
//!    (`admission::engine::EngineRunner::cell`) and qualification of version 0 over Q01's tiny database with lineitem
//!    grown to [`GROWN_LINEITEM_ROWS`] rows. Without limits (the schema-engine line) a fast statement's cell is as before;
//!    with a 1 s call limit the three-way self-product of lineitem is recorded `unfinished` (`over_time_limit`, no call
//!    finished, the echo checked) instead of refused, the fast statement still finishes, and qualification records the
//!    stopped binding, runs the binding after it in a fresh child, and skips the template named as unfinished at the
//!    timing binding.
//! 6. [`paused_schema_engine_crates_assemble_unchanged`] (frontend only; reads a paused run, never writes it): every
//!    frozen engine crate of a paused schema-engine run's round 1 is assembled again, byte for byte.
//! 7. [`nullable_columns_round_trip_from_the_capture_through_version_0`] (also `GENDB_WORKER`): nullable source columns
//!    end to end. A schema with a nullable column of every type (`fixtures/verus_flat/nullable_schema.sql`) is captured
//!    from Arrow columns with NULLs (`SourceColumns`, its column files with a validity file per nullable column); the
//!    flat assets are those capture files, linked part by part as `prepare-flat-storage` places them (values, offsets,
//!    bytes, validity); version 0 over the nullable flat storages (the flat access module with validity readers) verifies
//!    and compiles whole, and its answers to a statement that outputs every cell of every table and to one that
//!    aggregates and filters on NULLs equal the verified reference evaluator's on the same database. A storage crate
//!    built from the flat storage of the nullable table `line` (carrying `sources_flat.rs` with the nullable readers)
//!    verifies whole too.
//! 8. [`one_engine_source_verifies_over_two_schemas`] (stage runs): one shared tiny agent
//!    ([`SHARED_STAGE_AGENT`]) and a small workload module per schema, in the engine crates of two schemas assembled with
//!    the uniform flat access (`FlatAccess::Uniform`): the NOT NULL second schema and the nullable schema of test 7, each
//!    over the flat storage of every table. The agent reads every column of every table its workload module selects
//!    through `crate::flat_tables`, choosing the nullable reader by `schema_exec()`'s nullability linked with
//!    `lemma_nullable_column`, and answers as version 0. Both crates verify whole, 0 errors, and pass the stage rules
//!    over both schemas' names. A third crate whose storages are not generated flat storages (each flat storage's
//!    interface with one comment line added) carries the uniform module without a flat table; that module verifies
//!    (module-scoped run: its agent is a stub, so this run is no crate evidence).
//! 9. [`stage_goal_templates_encode_and_echo`] (also `GENDB_WORKER`; paths from `GENDB_STAGE_ENCODE_*`): a goal workload's templates at `v0` (SEC-EDGAR's six, Q1 without parameters) are prepared as the engine's
//!    checks prepare them, encoded, and echoed by version 0 over the workload's flat storages exactly as the host
//!    renders them.
//! 10. [`one_family_and_default_module_verify_over_two_schemas`] (runs of several workloads): one toy
//!    storage family (a plain-copy builder and interface, generic by table id over `crate::sources_flat`,
//!    `crate::schema_exec` and `crate::whole_schema`) and one shared toy engine with the default workload module
//!    (opening the family store by table and column id) over two NOT NULL schemas of two and three tables with every
//!    stored type class: each schema's family instance (built from the flat storage of every table) and its engine crate
//!    (reading only the instance) verify whole, 0 errors, with the same author files, which pass the member rule set
//!    over both schemas.
//! 11. [`one_family_builder_reads_nullable_columns_in_every_schema`]: one toy family builder text that
//!    reads the flat sources with the nullable items (`lemma_nullable_column`, `nullable_column_slice`, `column_slice`
//!    for the columns that are not nullable) compiles in the family's instance over a NOT NULL schema and over the
//!    nullable schema of test 7; `sources_flat` and the reader verify, 0 errors (module-scoped: the builder root is a
//!    stub, so this run is no crate evidence).
//! 12. [`recorded_tpch_family_instance_verifies_with_this_generation`] (reads `GENDB_RECORDED_FAMILY_INSTANCE`
//!    only): a family instance a run recorded over the TPC-H schema, assembled again by this generation (only
//!    `sources_flat.rs` may differ from the recorded framework files), verifies whole with its recorded author files.
use gendb_frontend::ast::{AstDocument, TableDef, Translation};
use gendb_frontend::engine_encode::{encode_binding, EngineAst};
use gendb_frontend::params::ParamRequest;
use gendb_frontend::parser::SqlParser;
use gendb_runtime::abi::{CallStatus, GENDB_ENGINE_SHIM_SOURCE, GENDB_STORAGE_DERIVED_SHIM_SOURCE};
use gendb_runtime::answer::QueryAnswer;
use gendb_runtime::worker::{spawn, CallLimits, StorageUseInput, UnfinishedReason, WorkerRequest, WorkerResult};
use gendb_sqlspec::codec::{HostTables, HostValue, RunOutcome};
use gendb_sqlspec::evaluator::{echo_text, EvaluatorLibrary};
use gendb_sqlspec::fixtures::{fixtures_dir, Fixture};
use gendb_storage::import::DatasetSpec;
use gendb_storage::io::{PartAccess, PartElem, PartFilesWriter, PartsFormat};
use gendb_verification::admission::bindings::BenchmarkBinding;
use gendb_verification::admission::engine::{qualify_finished_templates, EngineRunner, SkippedTemplate, TemplateCheck};
use gendb_verification::admission::execution::CandidateRunner;
use gendb_verification::admission::validation::ValidationPolicy;
use gendb_verification::admission::{dataset_ddl, IntegrityConstraints};
use gendb_verification::obligations::{
    check_storage_composition, derived_storage_crate_files, engine_crate_files, engine_crate_files_with, flat_storage, interpreter_engine,
    plain_columns_interface_file, whole_schema_declaration, with_trusted_shim, DeclaredSource, Derivation, FlatAccess, FlatAccessSite, FlatBuffer,
    FlatStorage, StorageName, StorageUse, ENGINE_CRATE_NAME, STORAGE_CRATE_NAME, STORAGE_SCHEMA_EXEC_PATH, WHOLE_SCHEMA_PATH,
};
use gendb_verification::reference::{build_evaluator, BuildOptions, BuildStatus};
use gendb_verification::verus::engine_rules::{scan_plan_source, EngineLine, EngineRuleSet, StageWorkload, TemplateConstants};
use gendb_verification::verus::{
    freeze_framework_crate, run_verus, verify_modules, CodegenOptions, FrameworkSource, FrozenCrate, VerusMode, VerusOptions, VerusOutcome,
    VerusToolchain,
};
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

/// The SF100 dataset's tables and column types (the request of the
/// published TPC-H SF100 runs): every integer column bigint, every decimal numeric(15,2), text and date; all NOT NULL.
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

const TEMPLATE_COUNT: usize = 22;
const RANGE_CAPACITY: u64 = 64;

fn repository() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).ancestors().nth(3).expect("<repository>/src/gendb/verification").to_path_buf()
}

/// A fresh work directory `<work>/<name>-<pid>-<nanos>`.
fn work_dir(name: &str) -> PathBuf {
    let base = std::env::var_os("GENDB_ENGINE_TEST_WORK").map(PathBuf::from).unwrap_or_else(|| PathBuf::from(env!("CARGO_TARGET_TMPDIR")));
    let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = base.join(format!("engine-{name}-{}-{nanos}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
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

/// The cache of compiled engine libraries (`<work>/engine-cache`), shared by runs.
fn cache_dir() -> PathBuf {
    let base = std::env::var_os("GENDB_ENGINE_TEST_WORK").map(PathBuf::from).unwrap_or_else(|| PathBuf::from(env!("CARGO_TARGET_TMPDIR")));
    base.join("engine-cache")
}

/// The TPC-H dataset DDL of the SF100 runs with the 15 declared integrity constraints, written to `work/tpch.sql`.
fn tpch_ddl(work: &Path) -> PathBuf {
    let dataset: DatasetSpec = serde_json::from_str(TPCH_DATASET).unwrap();
    let constraints: IntegrityConstraints =
        serde_json::from_str(&std::fs::read_to_string(repository().join("src/gendb/fixtures/tpch/integrity-constraints.json")).unwrap()).unwrap();
    let (ddl, omitted) = dataset_ddl(&dataset, Some(&constraints));
    assert!(omitted.is_empty(), "{omitted:?}");
    let path = work.join("tpch.sql");
    std::fs::write(&path, ddl).unwrap();
    path
}

/// One template: its name (`Q01`), SQL file and parameter declarations.
struct Template {
    name: String,
    sql: PathBuf,
    params: Vec<ParamRequest>,
}

fn templates() -> Vec<Template> {
    let dir = repository().join("src/gendb/fixtures/tpch/templates");
    let index: Value = serde_json::from_str(&std::fs::read_to_string(dir.join("templates.json")).unwrap()).unwrap();
    let list: Vec<Template> = index["templates"]
        .as_object()
        .unwrap()
        .iter()
        .map(|(name, t)| Template {
            name: name.clone(),
            sql: dir.join(t["sql"].as_str().unwrap()),
            params: serde_json::from_value(t["parameters"].clone()).unwrap(),
        })
        .collect();
    assert_eq!(list.len(), TEMPLATE_COUNT);
    list
}

/// The visible bindings of `template`: `(binding id, argument texts in slot order)`, v0..v2.
fn visible_bindings(visible: &Value, template: &str) -> Vec<(String, Vec<String>)> {
    visible["queries"][template]
        .as_array()
        .unwrap()
        .iter()
        .map(|b| (b["binding_id"].as_str().unwrap().to_string(), b["arguments"].as_array().unwrap().iter().map(|a| a.as_str().unwrap().to_string()).collect()))
        .collect()
}

/// The template's typed AST document (parameters still `Param` nodes, after the parser's constant check).
fn translate(parser: &SqlParser, ddl: &Path, t: &Template) -> AstDocument {
    let placeholders: Vec<_> = t.params.iter().map(ParamRequest::placeholder).collect();
    let (_, translation) = parser.translate(ddl, &t.sql, "postgres", &placeholders).unwrap();
    let Translation::Ok(doc) = translation else { panic!("{}: refused: {translation:?}", t.name) };
    doc
}

// --------------------------------------------------------------------------------------------------- version 0

/// The flat storage of every table of `schema`, in table id order.
fn flat_storages(schema: &[TableDef]) -> Vec<FlatStorage> {
    (0..schema.len()).map(|t| flat_storage(schema, t).unwrap()).collect()
}

/// The interface files of every flat storage (`stores/<name>/interface/**`), in the same order.
fn flat_interfaces(flats: &[FlatStorage]) -> Vec<Vec<FrameworkSource>> {
    flats.iter().map(|f| f.files.iter().filter(|x| x.path.starts_with(&f.name.interface_prefix())).cloned().collect()).collect()
}

fn flat_uses<'a>(flats: &'a [FlatStorage], interfaces: &'a [Vec<FrameworkSource>]) -> Vec<StorageUse<'a>> {
    flats.iter().zip(interfaces).map(|(f, i)| StorageUse { name: &f.name, declaration: &f.declaration, interface: i }).collect()
}

/// Version 0's `agent/mod.rs` for `schema` over the flat storage of every table.
fn version_0(schema: &[TableDef], flats: &[FlatStorage]) -> String {
    let interfaces = flat_interfaces(flats);
    let agent = interpreter_engine(schema, &flat_uses(flats, &interfaces)).unwrap();
    assert_eq!(agent.len(), 1);
    agent[0].text.clone()
}

/// Every file of the engine crate over the flat storage of every table (with the trusted shim) whose author module is
/// `agent`.
fn engine_crate(schema: &[TableDef], flats: &[FlatStorage], agent: &str) -> Vec<FrameworkSource> {
    let interfaces = flat_interfaces(flats);
    let mut files = engine_crate_files(schema, &flat_uses(flats, &interfaces), "version 0 of the general engine").unwrap();
    assert!(files.iter().any(|f| f.path == FlatAccessSite::Engine.path()), "the flat access module is assembled");
    files.push(FrameworkSource { path: "agent/mod.rs".into(), text: agent.into() });
    with_trusted_shim(files, GENDB_ENGINE_SHIM_SOURCE)
}

/// TEST FIXTURE ONLY: version 0 whose engine answers empty rows for every statement and database, without computing
/// them and without proof (must fail verification at the entry's obligation).
fn negative_agent(v0: &str) -> String {
    let start = v0.find("    let edb = materialize_database(").expect("version 0 materializes the database");
    let end = v0.rfind("    r\n}").expect("version 0 returns r");
    format!("{}    Ok(Answer::Rows(Vec::new()))\n}}{}", &v0[..start], &v0[end + "    r\n}".len()..])
}

/// The compiled library of a frozen engine crate: reused from the cache when an earlier run compiled byte-equal
/// sources, else one whole-crate verify and compile (the cache entry is written then). Returns the library and
/// whether it was verified here.
fn compiled_engine(toolchain: &VerusToolchain, files: &[FrameworkSource], work: &Path) -> (PathBuf, Value) {
    compiled_engine_in(toolchain, files, work, "version-0-engine")
}

/// [`compiled_engine`] with the cache entry `<work>/engine-cache/<cache>`.
fn compiled_engine_in(toolchain: &VerusToolchain, files: &[FrameworkSource], work: &Path, cache: &str) -> (PathBuf, Value) {
    let unscanned: Vec<&str> = files.iter().filter(|f| gendb_registry::author_definition(&f.path).is_none()).map(|f| f.path.as_str()).collect();
    let frozen = freeze_framework_crate(files, &unscanned, &work.join("frozen")).unwrap_or_else(|e| panic!("{e:?}"));
    let cache = cache_dir().join(cache);
    if let (Ok(cached), Ok(record)) = (std::fs::read_to_string(cache.join("sources.json")), std::fs::read_to_string(cache.join("run.json"))) {
        let record: Value = serde_json::from_str(&record).unwrap();
        let library = PathBuf::from(record["library"].as_str().unwrap_or_default());
        if cached == sources_json(&frozen) && library.is_file() {
            return (library, json!({"reused_from": cache, "verification": record["verification"]}));
        }
    }
    let run = with_build_lock(|| run_verus(toolchain, &frozen, &options(), VerusMode::VerifyAndCompile, &work.join("verus")).unwrap());
    assert_eq!(run.outcome, VerusOutcome::Compiled, "version 0: {}", run.rendered_errors());
    let library = run.artifact.clone().unwrap();
    let _ = std::fs::remove_dir_all(&cache);
    std::fs::create_dir_all(&cache).unwrap();
    let kept = cache.join("libgendb_engine.so");
    std::fs::copy(&library, &kept).unwrap();
    std::fs::write(cache.join("sources.json"), sources_json(&frozen)).unwrap();
    let record = json!({"library": kept, "verification": run.verification, "wall_ns": run.wall_ns, "frozen": frozen.root});
    std::fs::write(cache.join("run.json"), serde_json::to_vec_pretty(&record).unwrap()).unwrap();
    (kept, json!({"verified_here": true, "verification": run.verification, "wall_ns": run.wall_ns}))
}

/// Every file of a frozen crate (path and text), as one JSON text: the cache key.
fn sources_json(frozen: &FrozenCrate) -> String {
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
    walk(&frozen.root.join("src"), "", &mut out);
    serde_json::to_string(&out).unwrap()
}

fn options() -> VerusOptions {
    VerusOptions { crate_name: ENGINE_CRATE_NAME.into(), codegen: CodegenOptions { opt_level: 1, target_cpu: None }, num_threads: Some(16) }
}

/// The TPC-H schema (the SF100 dataset DDL with the declared constraints), from a trivial statement over it.
fn tpch_schema(parser: &SqlParser, work: &Path) -> (PathBuf, Vec<TableDef>) {
    let ddl = tpch_ddl(work);
    let sql = work.join("schema-probe.sql");
    std::fs::write(&sql, "SELECT r_regionkey FROM region").unwrap();
    let (_, translation) = parser.translate(&ddl, &sql, "postgres", &[]).unwrap();
    let Translation::Ok(doc) = translation else { panic!("schema probe refused: {translation:?}") };
    (ddl, doc.tables)
}

/// Verify (no library) the frozen crate `files` named `crate_name` under `work`, holding the build lock.
fn verify_only(toolchain: &VerusToolchain, files: &[FrameworkSource], crate_name: &str, work: &Path) -> gendb_verification::verus::VerusRun {
    let unscanned: Vec<&str> = files.iter().filter(|f| gendb_registry::author_definition(&f.path).is_none()).map(|f| f.path.as_str()).collect();
    let frozen = freeze_framework_crate(files, &unscanned, &work.join("frozen")).unwrap_or_else(|e| panic!("{e:?}"));
    let options = VerusOptions { crate_name: crate_name.into(), ..options() };
    with_build_lock(|| run_verus(toolchain, &frozen, &options, VerusMode::Verify, &work.join("verus")).unwrap())
}

#[test]
#[ignore = "runs the pinned Verus on version 0 over TPC-H and on its negative fixture; -- --ignored"]
fn version_0_verifies_whole_and_the_negative_fixture_fails() {
    let work = work_dir("verify");
    let toolchain = VerusToolchain::from_env().unwrap();
    let parser = SqlParser::from_environment().unwrap();
    let (_, schema) = tpch_schema(&parser, &work);
    let flats = flat_storages(&schema);
    let agent = version_0(&schema, &flats);
    std::fs::write(work.join("version-0-agent.rs"), &agent).unwrap();

    // The general line's rules pass over the TPC-H template constants and every TPC-H table and column name; the
    // schema-engine line refuses version 0 by the whole-statement evaluator rule only.
    let constants = TemplateConstants::from_templates_json(&repository().join("src/gendb/fixtures/tpch/templates/templates.json")).unwrap();
    let general = EngineRuleSet::for_line(EngineLine::General, constants.clone(), &schema);
    assert_eq!(general.scan_agent_source("agent/mod.rs", &agent), vec![], "version 0 under the general line's rules");
    let reports = general.schema_name_reports("agent/mod.rs", &agent);
    let schema_engine = EngineRuleSet::for_line(EngineLine::SchemaEngine, constants, &schema);
    let refused: BTreeSet<&str> = schema_engine.scan_agent_source("agent/mod.rs", &agent).iter().map(|f| f.rule).collect();
    assert_eq!(refused, BTreeSet::from(["whole_statement_evaluator"]));

    let (library, origin) = compiled_engine(&toolchain, &engine_crate(&schema, &flats, &agent), &work.join("positive"));
    eprintln!("version 0: {} ({origin})", library.display());

    let negative = negative_agent(&agent);
    std::fs::write(work.join("version-0-negative-agent.rs"), &negative).unwrap();
    let run = verify_only(&toolchain, &engine_crate(&schema, &flats, &negative), ENGINE_CRATE_NAME, &work.join("negative"));
    assert_eq!(run.outcome, VerusOutcome::ProofFailure, "the negative fixture must fail verification: {}", run.detail);
    let failed = run.rendered_errors();
    assert!(failed.contains("postcondition not satisfied"), "{failed}");
    let evidence = json!({"positive": {"library": library, "origin": origin},
        "general_line": {"rule_set": general.record(), "findings": 0, "reported_table_mentions": reports.len()},
        "schema_engine_line": {"refused_by": refused},
        "negative": {"outcome": run.outcome, "verification": run.verification, "detail": run.detail, "errors": failed}});
    std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", work.join("evidence.json").display());
}

/// A second, unrelated schema: integer, bigint, numeric, date, text, varchar and char columns, two primary keys and one
/// foreign key.
const SECOND_SCHEMA_DDL: &str = "CREATE TABLE account (\n    a_id integer NOT NULL,\n    a_name varchar(20) NOT NULL,\n    a_opened date NOT NULL,\n    a_limit numeric(12,2) NOT NULL\n);\n\
CREATE TABLE ledger (\n    g_id bigint NOT NULL,\n    g_account integer NOT NULL,\n    g_amount numeric(12,2) NOT NULL,\n    g_day date NOT NULL,\n    g_note text NOT NULL\n);\n\
CREATE TABLE tag (\n    t_code char(3) NOT NULL,\n    t_weight numeric(5,1) NOT NULL\n);\n\
ALTER TABLE account ADD PRIMARY KEY (a_id);\nALTER TABLE ledger ADD PRIMARY KEY (g_id);\nALTER TABLE ledger ADD FOREIGN KEY (g_account) REFERENCES account (a_id);\n";

/// TEST FIXTURE ONLY: the interface of storage `ledger_kept`, which keeps the parts of the flat storage of `ledger`
/// unchanged: its relation is that storage's.
const KEPT_INTERFACE: &str = r#"//! TEST FIXTURE: the parts of the flat storage of `ledger`, kept unchanged.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::Row;

verus! {

/// The parts represent `rels` exactly as the flat storage's parts do.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    crate::stores::flat_ledger::interface::represents(parts, rels)
}

/// Lossless, as the flat storage.
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires
        represents(parts, a),
        represents(parts, b),
    ensures
        a == b,
{
    crate::stores::flat_ledger::interface::lemma_represents_determines(parts, a, b);
}

} // verus!
"#;

/// TEST FIXTURE ONLY: the builder of `ledger_kept`: it adds no part (the extended source's parts come first and are all
/// it stores) and reads the source's row count through the generated `crate::sources_flat`.
const KEPT_BUILDER: &str = r#"//! TEST FIXTURE: keeps the flat storage's parts; reads its row count through `crate::sources_flat`.
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::gendb_entry::layout::owned_parts_view;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::sources::Stores;
use crate::gendb_entry::storage::{represents, stored_relations};
use crate::spec::value::Database;

verus! {

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
    let rows = crate::sources_flat::table_rows(stores, 1, Ghost(db));
    assert(rows == db.tables[1].len());
    let parts: Vec<OwnedPart> = Vec::new();
    proof {
        assert forall|other: Database| #[trigger] sources_bound(sv, other)
            implies represents(storage_parts(sv, owned_parts_view(parts@)), stored_relations(other)) by {
            assert(storage_parts(sv, owned_parts_view(parts@)) =~= sv.flat_ledger);
            assert(stored_relations(other) =~= crate::stores::flat_ledger::declaration::stored_relations(other));
        }
    }
    Ok(parts)
}

} // verus!
"#;

#[test]
#[ignore = "runs the pinned Verus on version 0 for a second schema and on a storage crate built from its flat storage; -- --ignored"]
fn version_0_verifies_for_a_second_schema() {
    let work = work_dir("second-schema");
    let toolchain = VerusToolchain::from_env().unwrap();
    let parser = SqlParser::from_environment().unwrap();
    let ddl = work.join("second.sql");
    std::fs::write(&ddl, SECOND_SCHEMA_DDL).unwrap();
    let probe = work.join("probe.sql");
    std::fs::write(&probe, "SELECT a_id FROM account").unwrap();
    let (_, translation) = parser.translate(&ddl, &probe, "postgres", &[]).unwrap();
    let Translation::Ok(doc) = translation else { panic!("second schema refused: {translation:?}") };
    let schema = doc.tables;
    assert_eq!(schema.iter().map(|t| t.name.as_str()).collect::<Vec<_>>(), ["account", "ledger", "tag"]);
    let flats = flat_storages(&schema);
    let agent = version_0(&schema, &flats);
    let general = EngineRuleSet::for_line(EngineLine::General, TemplateConstants::default(), &schema);
    assert_eq!(general.scan_agent_source("agent/mod.rs", &agent), vec![], "version 0 names nothing of the second schema");
    let engine = verify_only(&toolchain, &engine_crate(&schema, &flats, &agent), ENGINE_CRATE_NAME, &work.join("engine"));
    assert_eq!(engine.outcome, VerusOutcome::Verified, "version 0 over the second schema: {}", engine.rendered_errors());

    // A storage crate built from the flat storage of `ledger` (extending it, adding no part), which carries
    // `sources_flat.rs` and calls it.
    let interfaces = flat_interfaces(&flats);
    let uses = flat_uses(&flats, &interfaces);
    let kept = StorageName::new("ledger_kept").unwrap();
    let source = [uses[1]];
    let mut files =
        derived_storage_crate_files(&schema, &kept, &flats[1].declaration, Derivation { sources: &source, extends: Some(0) }, false).unwrap();
    assert!(files.iter().any(|f| f.path == FlatAccessSite::DerivedSources.path()));
    files.push(FrameworkSource { path: format!("{}mod.rs", kept.interface_prefix()), text: KEPT_INTERFACE.into() });
    files.push(FrameworkSource { path: "builder/mod.rs".into(), text: KEPT_BUILDER.into() });
    let derived = verify_only(&toolchain, &with_trusted_shim(files, GENDB_STORAGE_DERIVED_SHIM_SOURCE), STORAGE_CRATE_NAME, &work.join("derived"));
    assert_eq!(derived.outcome, VerusOutcome::Verified, "storage crate over a flat source: {}", derived.rendered_errors());
    let evidence = json!({"schema": schema.iter().map(|t| json!({"table": t.name, "columns": t.columns.iter().map(|c| &c.name).collect::<Vec<_>>()})).collect::<Vec<_>>(),
        "version_0": {"outcome": engine.outcome, "verification": engine.verification, "wall_ns": engine.wall_ns},
        "derived_storage_with_sources_flat": {"outcome": derived.outcome, "verification": derived.verification, "wall_ns": derived.wall_ns}});
    std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", work.join("evidence.json").display());
}

// ------------------------------------------------------------------------------- stage runs: one source, two schemas

/// TEST FIXTURE ONLY: the shared engine source of [`one_engine_source_verifies_over_two_schemas`]. It reads every column
/// of every table its workload module selects through the uniform flat access (the nullable reader exactly for a
/// column `schema_exec()` declares nullable, linked by `lemma_nullable_column`), then answers as version 0 does (every
/// table is flat-stored in both crates). It names no table or column of either schema.
const SHARED_STAGE_AGENT: &str = r#"//! TEST FIXTURE ONLY: one engine source for the crates of two schemas (stage runs).
use vstd::prelude::*;
use crate::gendb_entry::{answer_meets, bound_db, outcome_ok, stores_ready, supported, Answer};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::schema_exec::schema_exec;
use crate::exec::ast::{view_ordered, EOrderedQuery};
use crate::exec::relational::schema::{lemma_db_wf_ts_ok, view_rows, view_schema, ETableSchema};
use crate::exec::relational::entry::exec_ordered;
use crate::bridge::order::lemma_denote_top_ok;
use crate::flat_tables::{
    column_slice, flat_bound, flat_table, lemma_flat_database_unique, lemma_nullable_column, materialize_database, nullable_column, nullable_column_slice,
    table_rows,
};
use crate::schema::schema_spec;
use crate::spec::value::Database;

pub mod workload;

verus! {

/// Rows `0..n` of every column of flat-stored table `t`, each read with the reader its declared nullability calls for.
fn read_every_column(stores: &mut Stores, schema: &Vec<ETableSchema>, t: usize, Ghost(db): Ghost<Database>)
    requires
        flat_bound(old(stores)@, db),
        flat_table(t as int),
        view_schema(schema@) == schema_spec(),
        t < schema@.len(),
    ensures
        final(stores)@ == old(stores)@,
{
    let n = table_rows(stores, t, Ghost(db));
    let width = schema[t].columns.len();
    proof {
        assert(view_schema(schema@)[t as int].columns == schema@[t as int].columns@);
    }
    let mut c: usize = 0;
    while c < width
        invariant
            stores@ == old(stores)@,
            flat_bound(stores@, db),
            flat_table(t as int),
            view_schema(schema@) == schema_spec(),
            t < schema@.len(),
            width == schema@[t as int].columns@.len(),
            schema_spec()[t as int].columns == schema@[t as int].columns@,
            n == db.tables[t as int].len(),
            c <= width,
        decreases width - c,
    {
        if n > 0 {
            proof {
                lemma_nullable_column(t as int, c as int);
            }
            if schema[t].columns[c].nullable {
                let (_values, _validity) = nullable_column_slice(stores, t, c, 0, n, Ghost(db));
            } else {
                let _values = column_slice(stores, t, c, 0, n, Ghost(db));
            }
        }
        c += 1;
    }
}

/// The engine: every table the workload module selects read column by column, then the verified interpreter's answer
/// over the materialized database.
pub fn engine(stores: &mut Stores, q: &EOrderedQuery, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        supported(view_ordered(*q)),
        1 <= workers <= MAX_WORKERS,
    ensures
        answer_meets(old(stores)@, view_ordered(*q), r),
{
    let ghost sv = stores@;
    let ghost db = choose|db: Database| bound_db(sv, db);
    let schema = schema_exec();
    let mut t: usize = 0;
    while t < schema.len()
        invariant
            stores@ == sv,
            bound_db(sv, db),
            view_schema(schema@) == schema_spec(),
        decreases schema.len() - t,
    {
        if crate::agent::workload::reads_table(t) {
            read_every_column(stores, &schema, t, Ghost(db));
        }
        t += 1;
    }
    let edb = materialize_database(stores, Ghost(db));
    proof {
        lemma_db_wf_ts_ok(db);
        lemma_denote_top_ok(db, view_ordered(*q));
    }
    let r: Result<Answer, QueryError> = match exec_ordered(&edb, q) {
        Ok(Ok(rows)) => {
            proof {
                assert(crate::link::query::view_rows(rows@) =~= view_rows(rows@));
            }
            Ok(Answer::Rows(rows))
        },
        Ok(Err(e)) => Ok(Answer::SqlError(e)),
        Err(_) => Ok(Answer::Capacity),
    };
    proof {
        assert forall|other: Database| #[trigger] bound_db(sv, other) implies outcome_ok(other, view_ordered(*q), r) by {
            lemma_flat_database_unique(sv, db, other);
        }
    }
    r
}

} // verus!
"#;

/// TEST FIXTURE ONLY: the workload module of the NOT NULL schema's crate: the shared engine reads every flat-stored
/// table.
const PLAIN_WORKLOAD_MODULE: &str = r#"//! TEST FIXTURE ONLY: a workload module (the NOT NULL schema).
use vstd::prelude::*;
use crate::flat_tables::{flat_table, is_flat_table};

verus! {

/// Whether the shared engine reads table `t`: every flat-stored table.
pub fn reads_table(t: usize) -> (r: bool)
    ensures
        r ==> flat_table(t as int),
{
    is_flat_table(t)
}

} // verus!
"#;

/// TEST FIXTURE ONLY: the workload module of the nullable schema's crate: the shared engine reads the flat-stored tables
/// among the schema's.
const NULLABLE_WORKLOAD_MODULE: &str = r#"//! TEST FIXTURE ONLY: a workload module (the nullable schema).
use vstd::prelude::*;
use crate::flat_tables::{flat_table, is_flat_table, TABLE_COUNT};

verus! {

/// Whether the shared engine reads table `t`: a table id of the schema whose table is flat-stored.
pub fn reads_table(t: usize) -> (r: bool)
    ensures
        r ==> flat_table(t as int),
{
    t < TABLE_COUNT && is_flat_table(t)
}

} // verus!
"#;

/// TEST FIXTURE ONLY: an agent that type-checks and is not verified (the module-scoped run checks `flat_tables` only).
const STUB_AGENT: &str = r#"//! TEST FIXTURE ONLY: not verified (module-scoped run of the flat access module).
use vstd::prelude::*;
use crate::gendb_entry::{answer_meets, stores_ready, supported, Answer};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::stores::Stores;
use crate::exec::ast::{view_ordered, EOrderedQuery};

verus! {

pub fn engine(stores: &mut Stores, q: &EOrderedQuery, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        supported(view_ordered(*q)),
        1 <= workers <= MAX_WORKERS,
    ensures
        answer_meets(old(stores)@, view_ordered(*q), r),
{
    vstd::pervasive::unreached()
}

} // verus!
"#;

/// The schema of `ddl` (its tables with the declared constraints), from the trivial statement `probe` over it.
fn schema_of(parser: &SqlParser, ddl: &Path, probe: &str, work: &Path) -> Vec<TableDef> {
    let sql = work.join(format!("probe-{}.sql", ddl.file_stem().unwrap().to_string_lossy()));
    std::fs::write(&sql, probe).unwrap();
    let (_, translation) = parser.translate(ddl, &sql, "postgres", &[]).unwrap();
    let Translation::Ok(doc) = translation else { panic!("{}: refused: {translation:?}", ddl.display()) };
    doc.tables
}

/// The files of a stage run's crate over `schema` reading `uses` (uniform flat access, trusted shim) with the shared
/// `agent` and the workload module `workload` (none for the stub agent).
fn stage_crate(schema: &[TableDef], uses: &[StorageUse<'_>], agent: &str, workload: Option<&str>) -> Vec<FrameworkSource> {
    let mut files = engine_crate_files_with(schema, uses, "a stage run's crate", FlatAccess::Uniform).unwrap();
    files.push(FrameworkSource { path: "agent/mod.rs".into(), text: agent.into() });
    if let Some(module) = workload {
        files.push(FrameworkSource { path: "agent/workload/mod.rs".into(), text: module.into() });
    }
    with_trusted_shim(files, GENDB_ENGINE_SHIM_SOURCE)
}

#[test]
#[ignore = "runs the pinned Verus on the engine crates of two schemas sharing one agent, and on a crate without flat storages; -- --ignored"]
fn one_engine_source_verifies_over_two_schemas() {
    let work = work_dir("stage-two-schemas");
    let toolchain = VerusToolchain::from_env().unwrap();
    let parser = SqlParser::from_environment().unwrap();
    let plain_ddl = work.join("plain.sql");
    std::fs::write(&plain_ddl, SECOND_SCHEMA_DDL).unwrap();
    let plain = schema_of(&parser, &plain_ddl, "SELECT a_id FROM account", &work);
    let nullable_ddl = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/verus_flat/nullable_schema.sql");
    let nullable = schema_of(&parser, &nullable_ddl, "SELECT id FROM filing", &work);
    assert!(plain.iter().all(|t| t.columns.iter().all(|c| !c.nullable)) && nullable.iter().any(|t| t.columns.iter().any(|c| c.nullable)));

    // The shared source and both workload modules pass the stage rules over both schemas' names.
    let constants = TemplateConstants::default();
    let rules = EngineRuleSet::for_stage(&[
        StageWorkload { name: "plain", schema: &plain, constants: &constants },
        StageWorkload { name: "nullable", schema: &nullable, constants: &constants },
    ]);
    for (path, text) in [("agent/mod.rs", SHARED_STAGE_AGENT), ("agent/workload/mod.rs", PLAIN_WORKLOAD_MODULE), ("agent/workload/mod.rs", NULLABLE_WORKLOAD_MODULE)] {
        assert_eq!(rules.scan_agent_source(path, text), vec![], "{path} under the stage rules");
    }

    let mut evidence = vec![];
    for (name, schema, module) in [("plain", &plain, PLAIN_WORKLOAD_MODULE), ("nullable", &nullable, NULLABLE_WORKLOAD_MODULE)] {
        let flats = flat_storages(schema);
        let interfaces = flat_interfaces(&flats);
        let files = stage_crate(schema, &flat_uses(&flats, &interfaces), SHARED_STAGE_AGENT, Some(module));
        let access = &files.iter().find(|f| f.path == FlatAccessSite::Engine.path()).unwrap().text;
        let degenerate = access.contains("pub open spec fn nullable_column(t: int, c: int) -> bool {\n    false\n}");
        assert_eq!(degenerate, name == "plain", "{name}: the nullable items are degenerate exactly without a nullable column");
        let run = verify_only(&toolchain, &files, ENGINE_CRATE_NAME, &work.join(name));
        assert_eq!(run.outcome, VerusOutcome::Verified, "{name}: {}", run.rendered_errors());
        let verification = run.verification.clone().unwrap();
        assert!(verification.errors == 0 && verification.is_verifying_entire_crate, "{name}: {verification:?}");
        eprintln!("{name}: verified whole, {} verified, 0 errors, {:.1} s", verification.verified, run.wall_ns as f64 / 1e9);
        evidence.push(json!({"schema": name, "outcome": run.outcome, "verification": run.verification, "wall_ns": run.wall_ns}));
    }

    // No generated flat storage: the uniform module verifies (module-scoped; the stub agent is not verified).
    let flats = flat_storages(&plain);
    let impostors: Vec<Vec<FrameworkSource>> = flat_interfaces(&flats)
        .into_iter()
        .map(|files| files.into_iter().map(|f| FrameworkSource { text: format!("// TEST FIXTURE: not the flat storage generator's text.\n{}", f.text), ..f }).collect())
        .collect();
    let uses = flat_uses(&flats, &impostors);
    let files = stage_crate(&plain, &uses, STUB_AGENT, None);
    let access = &files.iter().find(|f| f.path == FlatAccessSite::Engine.path()).unwrap().text;
    assert!(access.contains("pub open spec fn flat_table(t: int) -> bool {\n    false\n}"), "{access}");
    let unscanned: Vec<&str> = files.iter().filter(|f| gendb_registry::author_definition(&f.path).is_none()).map(|f| f.path.as_str()).collect();
    let frozen = freeze_framework_crate(&files, &unscanned, &work.join("no-flat/frozen")).unwrap_or_else(|e| panic!("{e:?}"));
    let scoped = with_build_lock(|| verify_modules(&toolchain, &frozen, &options(), &["flat_tables".to_string()], &work.join("no-flat/verus")).unwrap());
    let summary = scoped.verification.clone().unwrap();
    assert!(scoped.outcome == VerusOutcome::Verified && summary.errors == 0 && summary.verified > 0, "no flat table: {} {}", scoped.detail, scoped.rendered_errors());
    eprintln!("no flat storage: flat_tables verified (module-scoped), {} verified, 0 errors", summary.verified);
    evidence.push(json!({"schema": "plain without flat storages", "scope": "flat_tables only", "outcome": scoped.outcome, "verification": scoped.verification, "wall_ns": scoped.wall_ns}));
    let evidence = json!({"crates": evidence, "rule_set": rules.record()});
    std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", work.join("evidence.json").display());
}

// ------------------------------------------------------- runs of several workloads: one storage family, two schemas

/// Two tiny NOT NULL schemas of different table counts for the toy family, with every stored type
/// class: integer, bigint, numeric, date, text, varchar and char.
const FAMILY_SCHEMA_A: &str = "CREATE TABLE alpha_item (\n    ai_key bigint NOT NULL,\n    ai_qty integer NOT NULL,\n    ai_day date NOT NULL\n);\n\
CREATE TABLE alpha_note (\n    an_item bigint NOT NULL,\n    an_amount numeric(12,2) NOT NULL,\n    an_body text NOT NULL\n);\n\
ALTER TABLE alpha_item ADD PRIMARY KEY (ai_key);\n";
const FAMILY_SCHEMA_B: &str = "CREATE TABLE beta_one (\n    bo_key integer NOT NULL,\n    bo_label varchar(12) NOT NULL\n);\n\
CREATE TABLE beta_two (\n    bt_key bigint NOT NULL,\n    bt_owner integer NOT NULL,\n    bt_price numeric(10,2) NOT NULL\n);\n\
CREATE TABLE beta_three (\n    bh_code char(3) NOT NULL,\n    bh_since date NOT NULL\n);\n\
ALTER TABLE beta_one ADD PRIMARY KEY (bo_key);\n";

/// The toy family's name: the instance's storage name in every schema's crates.
const TOY_FAMILY: &str = "copyfam";

/// TEST FIXTURE ONLY: the interface of the toy storage family `copyfam`.
const TOY_FAMILY_INTERFACE: &str = r#"//! TEST FIXTURE ONLY: the interface of the toy storage family `copyfam`: every column of every
//! table of the schema held plainly (the plain-columns vocabulary, `plain`), table after table and column after column,
//! by table and column id. The same text in every instance.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::schema::schema_spec;
use crate::spec::types::Column;
use crate::spec::value::Row;

pub mod plain;

verus! {

/// The parts the first `k` columns of `cols` take.
pub open spec fn columns_width(cols: Seq<Column>, k: int) -> int
    decreases k,
{
    if k <= 0 { 0 } else { columns_width(cols, k - 1) + plain::plain_width(cols[k - 1].ty) }
}

/// The first part of table `t`: the parts of every table before it.
pub open spec fn table_start(t: int) -> int
    decreases t,
{
    if t <= 0 { 0 } else { table_start(t - 1) + columns_width(schema_spec()[t - 1].columns, schema_spec()[t - 1].columns.len() as int) }
}

/// The part of column `c` of table `t`.
pub open spec fn column_part(t: int, c: int) -> int {
    table_start(t) + columns_width(schema_spec()[t].columns, c)
}

/// The part of every column of table `t`, in column order.
pub open spec fn table_layout(t: int) -> Seq<int> {
    Seq::new(schema_spec()[t].columns.len(), |c: int| column_part(t, c))
}

/// The parts hold `rels` plainly: one relation per table of the schema, each column from its part.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& rels.len() == schema_spec().len()
    &&& forall|t: int| 0 <= t < rels.len() ==> #[trigger] plain::plain_columns(parts, rels[t], schema_spec()[t].columns, table_layout(t))
}

/// Lossless: the parts determine the relations.
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires
        represents(parts, a),
        represents(parts, b),
    ensures
        a == b,
{
    assert forall|t: int| 0 <= t < a.len() implies #[trigger] a[t] == b[t] by {
        assert(plain::plain_columns(parts, a[t], schema_spec()[t].columns, table_layout(t)));
        assert(plain::plain_columns(parts, b[t], schema_spec()[t].columns, table_layout(t)));
        plain::lemma_plain_columns_determine(parts, a[t], b[t], schema_spec()[t].columns, table_layout(t));
    }
    assert(a =~= b);
}

} // verus!
"#;

/// TEST FIXTURE ONLY: the builder of the toy storage family `copyfam`.
const TOY_FAMILY_BUILDER: &str = r#"//! TEST FIXTURE ONLY: the builder of the toy storage family `copyfam`: every column of every table
//! copied from the flat sources (`crate::sources_flat`, by table and column id) into its plain parts, text offsets
//! rebased to 0. The column types come from `crate::schema_exec`, the schema's shape and the store's relations from
//! `crate::whole_schema`. The same text in every instance; `plan` is the composed plan (this toy reads none of it).
use vstd::prelude::*;
use vstd::slice::slice_to_vec;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::gendb_entry::layout::{owned_part_view, owned_parts_view, PartView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::storage::{represents, stored_relations};
use crate::exec::relational::schema::view_schema;
use crate::link::query::{text_at, text_wf};
use crate::schema::schema_spec;
use crate::schema_exec::schema_exec;
use crate::sources_flat::{column_slice, flat_bound, flat_table, lemma_flat_table_unique, slice_value, table_rows, ColumnSlice};
use crate::spec::typing::row_in_table;
use crate::spec::types::SqlType;
use crate::spec::value::{Database, Row, Val};
use crate::stores::copyfam::interface::{column_part, columns_width, table_layout, table_start};
use crate::stores::copyfam::interface::plain::{is_text, plain_column, plain_columns, plain_text, plain_width};
use crate::whole_schema::{lemma_copyfam, lemma_schema_shape, stored_type};

pub mod plan;

verus! {

/// The toy plan: a workload's plan is a literal of it (`plan::plan()`).
pub struct Plan {
    pub sorted: Vec<usize>,
}

/// Append `part` to `parts`: the view grows by the part's view.
fn push_part(parts: &mut Vec<OwnedPart>, part: OwnedPart)
    ensures
        owned_parts_view(final(parts)@) == owned_parts_view(old(parts)@).push(owned_part_view(part)),
{
    let ghost before = parts@;
    let ghost view = owned_part_view(part);
    parts.push(part);
    proof {
        assert(owned_parts_view(parts@) =~= owned_parts_view(before).push(view));
    }
}

/// A column held plainly stays held when parts are appended.
proof fn lemma_plain_column_kept(a: Seq<PartView>, b: Seq<PartView>, p: int, ty: SqlType, rows: Seq<Row>, c: int)
    requires
        plain_column(a, p, ty, rows, c),
        a.len() <= b.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] b[i] == a[i],
    ensures
        plain_column(b, p, ty, rows, c),
{
    assert(b[p] == a[p]);
    if is_text(ty) {
        assert(b[p + 1] == a[p + 1]);
        assert(plain_text(b, p) == plain_text(a, p));
    }
}

/// The offsets `o` minus their first: the offsets of the same rows from 0.
fn rebased(o: &[i64]) -> (r: Vec<i64>)
    requires
        o@.len() >= 1,
        0 <= o@[0],
        forall|x: int, y: int| 0 <= x <= y < o@.len() ==> o@[x] <= o@[y],
    ensures
        r@.len() == o@.len(),
        forall|k: int| 0 <= k < o@.len() ==> #[trigger] r@[k] == o@[k] - o@[0],
{
    let first = o[0];
    let mut r: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < o.len()
        invariant
            k <= o@.len(),
            o@.len() >= 1,
            first == o@[0],
            0 <= o@[0],
            forall|x: int, y: int| 0 <= x <= y < o@.len() ==> o@[x] <= o@[y],
            r@.len() == k,
            forall|x: int| 0 <= x < k ==> #[trigger] r@[x] == o@[x] - o@[0],
        decreases o@.len() - k,
    {
        assert(o@[0] <= o@[k as int]);
        r.push(o[k] - first);
        k += 1;
    }
    r
}

/// A text column copied as its rebased offsets `r` and its bytes `b` (from offsets `o`) is held plainly at `p`.
proof fn lemma_text_copied(parts: Seq<PartView>, p: int, ty: SqlType, rows: Seq<Row>, c: int, o: Seq<i64>, r: Seq<i64>, b: Seq<u8>)
    requires
        is_text(ty),
        0 <= p,
        p + 2 <= parts.len(),
        parts[p] == PartView::I64(r),
        parts[p + 1] == PartView::U8(b),
        o.len() == rows.len() + 1,
        0 <= o[0],
        forall|x: int, y: int| 0 <= x <= y < o.len() ==> o[x] <= o[y],
        b.len() == o[o.len() - 1] - o[0],
        r.len() == o.len(),
        forall|k: int| 0 <= k < o.len() ==> #[trigger] r[k] == o[k] - o[0],
        forall|j: int| 0 <= j < rows.len() ==> #[trigger] rows[j][c] == Val::Text(b.subrange(o[j] - o[0], o[j + 1] - o[0])),
    ensures
        plain_column(parts, p, ty, rows, c),
{
    let n = rows.len() as int;
    let tv = plain_text(parts, p);
    assert(tv.offsets == r && tv.bytes == b);
    assert forall|i: int| 0 <= i < n implies 0 <= #[trigger] tv.offsets[i] <= tv.offsets[i + 1] <= tv.bytes.len() by {
        assert(o[0] <= o[i] && o[i] <= o[i + 1] && o[i + 1] <= o[n]);
        assert(r[i] == o[i] - o[0] && r[i + 1] == o[i + 1] - o[0]);
    }
    assert(text_wf(tv, n));
    assert forall|i: int| 0 <= i < n implies #[trigger] rows[i][c] == Val::Text(text_at(tv, i)) by {
        assert(r[i] == o[i] - o[0] && r[i + 1] == o[i + 1] - o[0]);
        assert(rows[i][c] == Val::Text(b.subrange(o[i] - o[0], o[i + 1] - o[0])));
    }
}

/// Column `c` (type `ty`) of flat-stored table `t` (`n` rows) appended to `parts` as its plain parts.
fn push_column(stores: &mut Stores, t: usize, c: usize, n: usize, ty: SqlType, parts: &mut Vec<OwnedPart>, Ghost(db): Ghost<Database>)
    requires
        flat_bound(old(stores)@, db),
        flat_table(t as int),
        c < schema_spec()[t as int].columns.len(),
        ty == schema_spec()[t as int].columns[c as int].ty,
        stored_type(ty),
        n == db.tables[t as int].len(),
    ensures
        final(stores)@ == old(stores)@,
        owned_parts_view(final(parts)@).len() == owned_parts_view(old(parts)@).len() + plain_width(ty),
        forall|i: int| 0 <= i < owned_parts_view(old(parts)@).len() ==> #[trigger] owned_parts_view(final(parts)@)[i] == owned_parts_view(old(parts)@)[i],
        plain_column(owned_parts_view(final(parts)@), owned_parts_view(old(parts)@).len() as int, ty, db.tables[t as int], c as int),
{
    let ghost p = owned_parts_view(parts@).len() as int;
    let ghost rows = db.tables[t as int];
    if n == 0 {
        match ty {
            SqlType::Int4 => push_part(parts, OwnedPart::I32(Vec::new())),
            SqlType::Date => push_part(parts, OwnedPart::I32(Vec::new())),
            SqlType::Int8 => push_part(parts, OwnedPart::I64(Vec::new())),
            SqlType::Numeric { .. } => push_part(parts, OwnedPart::I128(Vec::new())),
            _ => {
                let mut offsets: Vec<i64> = Vec::new();
                offsets.push(0);
                push_part(parts, OwnedPart::I64(offsets));
                push_part(parts, OwnedPart::U8(Vec::new()));
                proof {
                    assert(plain_text(owned_parts_view(parts@), p).offsets.len() == 1);
                }
            },
        }
        return;
    }
    let s = column_slice(stores, t, c, 0, n, Ghost(db));
    proof {
        assert forall|j: int| 0 <= j < n implies #[trigger] rows[j][c as int] == slice_value(s, j) by {
            assert(db.tables[t as int][0 + j][c as int] == slice_value(s, j));
        }
    }
    match s {
        ColumnSlice::Int32(v) => push_part(parts, OwnedPart::I32(slice_to_vec(v))),
        ColumnSlice::Date(v) => push_part(parts, OwnedPart::I32(slice_to_vec(v))),
        ColumnSlice::Int64(v) => push_part(parts, OwnedPart::I64(slice_to_vec(v))),
        ColumnSlice::Numeric(v, _) => push_part(parts, OwnedPart::I128(slice_to_vec(v))),
        ColumnSlice::Text(o, b) => {
            let offsets = rebased(o);
            let ghost r = offsets@;
            push_part(parts, OwnedPart::I64(offsets));
            push_part(parts, OwnedPart::U8(slice_to_vec(b)));
            proof {
                lemma_text_copied(owned_parts_view(parts@), p, ty, rows, c as int, o@, r, b@);
            }
        },
    }
}

/// Every column of table `t` held plainly at its part: the table is held plainly.
proof fn lemma_table_held(parts: Seq<PartView>, db: Database, t: int)
    requires
        db.schema == schema_spec(),
        crate::spec::typing::db_wf(db),
        0 <= t < db.tables.len(),
        schema_spec()[t].columns.len() >= 1,
        forall|k: int| 0 <= k < schema_spec()[t].columns.len() ==> #[trigger] plain_column(parts, column_part(t, k), schema_spec()[t].columns[k].ty, db.tables[t], k),
    ensures
        plain_columns(parts, db.tables[t], schema_spec()[t].columns, table_layout(t)),
{
    let rows = db.tables[t];
    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] rows[i].len() == schema_spec()[t].columns.len() by {
        assert(row_in_table(rows[i], db.schema[t]));
    }
    assert forall|k: int| 0 <= k < schema_spec()[t].columns.len() implies #[trigger] plain_column(parts, table_layout(t)[k], schema_spec()[t].columns[k].ty, rows, k) by {
        assert(table_layout(t)[k] == column_part(t, k));
    }
}

/// Two databases bound to the flat sources have the same tables.
proof fn lemma_same_tables(sv: StoresView, a: Database, b: Database)
    requires
        flat_bound(sv, a),
        flat_bound(sv, b),
    ensures
        a.tables == b.tables,
{
    lemma_schema_shape();
    assert forall|t: int| 0 <= t < a.tables.len() implies #[trigger] a.tables[t] == b.tables[t] by {
        lemma_flat_table_unique(sv, a, b, t);
    }
    assert(a.tables =~= b.tables);
}

/// Copy every column of every table from the flat sources into its plain parts (the derived storage entry's builder).
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
    proof {
        lemma_schema_shape();
    }
    let schema = schema_exec();
    let mut parts: Vec<OwnedPart> = Vec::new();
    let mut t: usize = 0;
    while t < schema.len()
        invariant
            stores@ == sv,
            sources_bound(sv, db),
            view_schema(schema@) == schema_spec(),
            t <= schema@.len(),
            owned_parts_view(parts@).len() == table_start(t as int),
            forall|t2: int, k: int| 0 <= t2 < t && 0 <= k < schema_spec()[t2].columns.len() ==>
                #[trigger] plain_column(owned_parts_view(parts@), column_part(t2, k), schema_spec()[t2].columns[k].ty, db.tables[t2], k),
        decreases schema.len() - t,
    {
        proof {
            lemma_schema_shape();
            assert(schema@.len() == schema_spec().len());
            assert(flat_table(t as int));
            assert(view_schema(schema@)[t as int].columns == schema@[t as int].columns@);
        }
        let n = table_rows(stores, t, Ghost(db));
        let width = schema[t].columns.len();
        let mut c: usize = 0;
        while c < width
            invariant
                stores@ == sv,
                sources_bound(sv, db),
                view_schema(schema@) == schema_spec(),
                t < schema@.len(),
                schema@.len() == schema_spec().len(),
                flat_table(t as int),
                width == schema_spec()[t as int].columns.len(),
                schema_spec()[t as int].columns == schema@[t as int].columns@,
                n == db.tables[t as int].len(),
                c <= width,
                owned_parts_view(parts@).len() == column_part(t as int, c as int),
                forall|t2: int, k: int| 0 <= t2 < t && 0 <= k < schema_spec()[t2].columns.len() ==>
                    #[trigger] plain_column(owned_parts_view(parts@), column_part(t2, k), schema_spec()[t2].columns[k].ty, db.tables[t2], k),
                forall|k: int| 0 <= k < c ==>
                    #[trigger] plain_column(owned_parts_view(parts@), column_part(t as int, k), schema_spec()[t as int].columns[k].ty, db.tables[t as int], k),
            decreases width - c,
        {
            let ty = schema[t].columns[c].ty;
            let ghost before = owned_parts_view(parts@);
            proof {
                lemma_schema_shape();
            }
            push_column(stores, t, c, n, ty, &mut parts, Ghost(db));
            proof {
                let after = owned_parts_view(parts@);
                assert forall|t2: int, k: int| 0 <= t2 < t && 0 <= k < schema_spec()[t2].columns.len() implies
                    #[trigger] plain_column(after, column_part(t2, k), schema_spec()[t2].columns[k].ty, db.tables[t2], k) by {
                    lemma_plain_column_kept(before, after, column_part(t2, k), schema_spec()[t2].columns[k].ty, db.tables[t2], k);
                }
                assert forall|k: int| 0 <= k < c + 1 implies
                    #[trigger] plain_column(after, column_part(t as int, k), schema_spec()[t as int].columns[k].ty, db.tables[t as int], k) by {
                    if k < c {
                        lemma_plain_column_kept(before, after, column_part(t as int, k), schema_spec()[t as int].columns[k].ty, db.tables[t as int], k);
                    }
                }
                assert(column_part(t as int, c as int + 1) == column_part(t as int, c as int) + plain_width(ty));
            }
            c += 1;
        }
        proof {
            assert(table_start(t as int + 1) == column_part(t as int, width as int));
        }
        t += 1;
    }
    proof {
        let view = owned_parts_view(parts@);
        assert(storage_parts(sv, view) =~= view);
        assert forall|other: Database| #[trigger] sources_bound(sv, other) implies represents(storage_parts(sv, view), stored_relations(other)) by {
            lemma_copyfam(other);
            lemma_copyfam(db);
            lemma_same_tables(sv, db, other);
            assert forall|t2: int| 0 <= t2 < other.tables.len() implies
                #[trigger] plain_columns(view, other.tables[t2], schema_spec()[t2].columns, table_layout(t2)) by {
                lemma_table_held(view, db, t2);
            }
        }
    }
    Ok(parts)
}

} // verus!
"#;

/// TEST FIXTURE ONLY: the toy family's default plan (`default_plan.rs`, composed as `builder/plan.rs`).
const TOY_FAMILY_PLAN: &str = r#"//! TEST FIXTURE ONLY: the default plan of the toy storage family `copyfam`: nothing sorted.
use super::Plan;
use vstd::prelude::*;

verus! {

/// The plan of a workload without one of its own.
pub fn plan() -> Plan {
    Plan { sorted: vec![] }
}

} // verus!
"#;

/// TEST FIXTURE ONLY: the shared default workload module of the toy family run.
const TOY_DEFAULT_MODULE: &str = r#"//! TEST FIXTURE ONLY: the default workload module of the toy family run: the family store
//! `crate::stores::copyfam` opened as the engine's database, by table and column id, for any schema.
use vstd::prelude::*;
use vstd::slice::slice_to_vec;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::schema_exec::schema_exec;
use crate::exec::relational::schema::{view_rows, view_schema, EDatabase, ETableSchema};
use crate::exec::value::{view_row, ERow, EVal};
use crate::schema::schema_spec;
use crate::spec::datetime::date_valid;
use crate::spec::types::{Column, SqlType};
use crate::spec::typing::{row_in_table, value_in_column};
use crate::spec::value::Database;
use crate::stores::copyfam::declaration::stored_relations;
use crate::stores::copyfam::interface::{column_part, lemma_represents_determines, represents, table_layout, table_start};
use crate::stores::copyfam::interface::plain::{
    is_text, plain_column, plain_columns, plain_slice_len, plain_slice_wf, plain_value, plain_width, read_plain, PlainSlice,
};
use crate::whole_schema::{lemma_copyfam, lemma_schema_shape, stored_type};

verus! {

/// Two databases bound to the stores are equal: the family store is lossless and holds every table.
pub proof fn lemma_database_unique(sv: StoresView, a: Database, b: Database)
    requires
        bound_db(sv, a),
        bound_db(sv, b),
    ensures
        a == b,
{
    lemma_represents_determines(sv.copyfam, stored_relations(a), stored_relations(b));
    lemma_copyfam(a);
    lemma_copyfam(b);
    assert(a.tables =~= b.tables);
}

/// Whether a column of type `ty` is held as text (`plain::is_text`), executable.
fn is_text_type(ty: SqlType) -> (r: bool)
    ensures
        r == is_text(ty),
{
    match ty {
        SqlType::Text => true,
        SqlType::Varchar { .. } => true,
        SqlType::Bpchar { .. } => true,
        _ => false,
    }
}

/// The interpreter value of the one row of `s`, a slice of column `col` whose value lies in it.
fn cell_value(s: PlainSlice, Ghost(col): Ghost<Column>) -> (v: EVal)
    requires
        plain_slice_wf(s),
        plain_slice_len(s) == 1,
        value_in_column(plain_value(s, 0), col),
    ensures
        v@ == plain_value(s, 0),
{
    match s {
        PlainSlice::Int32(x) => EVal::Int(x[0] as i64),
        PlainSlice::Date(x) => {
            assert(date_valid(x@[0] as int - 10957));
            EVal::Date(x[0] - 10957)
        },
        PlainSlice::Int64(x) => EVal::Int(x[0]),
        PlainSlice::Numeric(x, scale) => EVal::Num { coeff: x[0], scale },
        PlainSlice::Text(o, b) => {
            proof {
                assert(b@.subrange(o@[0] - o@[0], o@[1] - o@[0]) =~= b@);
            }
            EVal::Text(slice_to_vec(b))
        },
    }
}

/// The first part of table `t + 1` (`start` is table `t`'s), from the column types.
fn table_end(schema: &Vec<ETableSchema>, t: usize, start: usize, count: usize, Ghost(sv): Ghost<StoresView>, Ghost(db): Ghost<Database>) -> (next: usize)
    requires
        represents(sv.copyfam, db.tables),
        count == sv.copyfam.len(),
        view_schema(schema@) == schema_spec(),
        t < schema@.len(),
        start as int == table_start(t as int),
    ensures
        next as int == table_start(t as int + 1),
{
    proof {
        assert(view_schema(schema@)[t as int].columns == schema@[t as int].columns@);
        assert(plain_columns(sv.copyfam, db.tables[t as int], schema_spec()[t as int].columns, table_layout(t as int)));
    }
    let width = schema[t].columns.len();
    let mut q = start;
    let mut c: usize = 0;
    while c < width
        invariant
            represents(sv.copyfam, db.tables),
            count == sv.copyfam.len(),
            view_schema(schema@) == schema_spec(),
            t < schema@.len(),
            width == schema_spec()[t as int].columns.len(),
            schema_spec()[t as int].columns == schema@[t as int].columns@,
            plain_columns(sv.copyfam, db.tables[t as int], schema_spec()[t as int].columns, table_layout(t as int)),
            c <= width,
            q as int == column_part(t as int, c as int),
        decreases width - c,
    {
        let ty = schema[t].columns[c].ty;
        proof {
            assert(plain_column(sv.copyfam, table_layout(t as int)[c as int], ty, db.tables[t as int], c as int));
            assert(table_layout(t as int)[c as int] == column_part(t as int, c as int));
            assert(column_part(t as int, c as int + 1) == column_part(t as int, c as int) + plain_width(ty));
        }
        q = if is_text_type(ty) { q + 2 } else { q + 1 };
        c += 1;
    }
    q
}

/// Every row of table `t` of the database bound to the stores, read from the family store (table `t`'s first part is
/// `start`).
fn read_table(stores: &mut Stores, schema: &Vec<ETableSchema>, t: usize, start: usize, count: usize, Ghost(db): Ghost<Database>) -> (rows: Vec<ERow>)
    requires
        bound_db(old(stores)@, db),
        represents(old(stores)@.copyfam, db.tables),
        count == old(stores)@.copyfam.len(),
        view_schema(schema@) == schema_spec(),
        t < schema@.len(),
        start as int == table_start(t as int),
    ensures
        final(stores)@ == old(stores)@,
        view_rows(rows@) == db.tables[t as int],
{
    let ghost sv = stores@;
    let ghost table = db.tables[t as int];
    let ghost cols = schema_spec()[t as int].columns;
    proof {
        lemma_schema_shape();
        assert(view_schema(schema@)[t as int].columns == schema@[t as int].columns@);
        assert(plain_columns(sv.copyfam, table, cols, table_layout(t as int)));
        assert(plain_column(sv.copyfam, table_layout(t as int)[0], cols[0].ty, table, 0));
        assert(table_layout(t as int)[0] == column_part(t as int, 0));
    }
    let width = schema[t].columns.len();
    let first = schema[t].columns[0].ty;
    let len = stores.copyfam.part_len(start);
    let n = if is_text_type(first) { len - 1 } else { len };
    proof {
        assert(stored_type(first));
        assert(n == table.len());
    }
    let mut out: Vec<ERow> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            stores@ == sv,
            bound_db(sv, db),
            count == sv.copyfam.len(),
            view_schema(schema@) == schema_spec(),
            t < schema@.len(),
            table == db.tables[t as int],
            cols == schema_spec()[t as int].columns,
            cols == schema@[t as int].columns@,
            width == cols.len(),
            plain_columns(sv.copyfam, table, cols, table_layout(t as int)),
            start as int == table_start(t as int),
            n == table.len(),
            i <= n,
            view_rows(out@) == table.take(i as int),
        decreases n - i,
    {
        proof {
            assert(row_in_table(table[i as int], db.schema[t as int]));
        }
        let mut row: ERow = Vec::new();
        let mut p: usize = start;
        let mut c: usize = 0;
        while c < width
            invariant
                stores@ == sv,
                count == sv.copyfam.len(),
                t < schema@.len(),
                view_rows(out@) == table.take(i as int),
                table == db.tables[t as int],
                cols == schema@[t as int].columns@,
                width == cols.len(),
                plain_columns(sv.copyfam, table, cols, table_layout(t as int)),
                row_in_table(table[i as int], db.schema[t as int]),
                db.schema == schema_spec(),
                cols == schema_spec()[t as int].columns,
                i < n,
                n == table.len(),
                c <= width,
                p as int == column_part(t as int, c as int),
                row@.len() == c,
                forall|k: int| 0 <= k < c ==> #[trigger] row@[k]@ == table[i as int][k],
            decreases width - c,
        {
            let ty = schema[t].columns[c].ty;
            proof {
                assert(plain_column(sv.copyfam, table_layout(t as int)[c as int], cols[c as int].ty, table, c as int));
                assert(table_layout(t as int)[c as int] == column_part(t as int, c as int));
                assert(value_in_column(table[i as int][c as int], cols[c as int]));
            }
            let s = read_plain(&mut stores.copyfam, p, ty, i, i + 1, Ghost(table), Ghost(c as int));
            proof {
                assert(table[i as int + 0][c as int] == plain_value(s, 0));
            }
            let v = cell_value(s, Ghost(cols[c as int]));
            row.push(v);
            proof {
                assert(column_part(t as int, c as int + 1) == column_part(t as int, c as int) + plain_width(ty));
            }
            p = if is_text_type(ty) { p + 2 } else { p + 1 };
            c += 1;
        }
        proof {
            assert(view_row(row@) =~= table[i as int]);
        }
        let ghost before = out@;
        let ghost value = view_row(row@);
        out.push(row);
        proof {
            assert(view_rows(out@) =~= view_rows(before).push(value));
            assert(table.take(i as int + 1) =~= table.take(i as int).push(table[i as int]));
            assert(view_rows(out@) =~= table.take(i as int + 1));
        }
        i += 1;
    }
    proof {
        assert(table.take(n as int) =~= table);
    }
    out
}

/// The database bound to the stores, read from the family store: `edb@ == db`.
pub fn open_database(stores: &mut Stores, Ghost(db): Ghost<Database>) -> (edb: EDatabase)
    requires
        bound_db(old(stores)@, db),
    ensures
        final(stores)@ == old(stores)@,
        edb@ == db,
{
    let ghost sv = stores@;
    proof {
        lemma_copyfam(db);
        lemma_schema_shape();
    }
    let schema = schema_exec();
    let count = stores.copyfam.part_count();
    let mut tables: Vec<Vec<ERow>> = Vec::new();
    let mut start: usize = 0;
    let mut t: usize = 0;
    while t < schema.len()
        invariant
            stores@ == sv,
            bound_db(sv, db),
            represents(sv.copyfam, db.tables),
            count == sv.copyfam.len(),
            view_schema(schema@) == schema_spec(),
            schema@.len() == schema_spec().len(),
            t <= schema@.len(),
            start as int == table_start(t as int),
            tables@.len() == t,
            forall|k: int| 0 <= k < t ==> #[trigger] view_rows(tables@[k]@) == db.tables[k],
        decreases schema.len() - t,
    {
        let rows = read_table(stores, &schema, t, start, count, Ghost(db));
        let next = table_end(&schema, t, start, count, Ghost(sv), Ghost(db));
        tables.push(rows);
        start = next;
        t += 1;
    }
    let edb = EDatabase { schema, tables };
    proof {
        assert(edb@.tables =~= db.tables);
        assert(edb@ == db);
    }
    edb
}

} // verus!
"#;

/// TEST FIXTURE ONLY: the shared engine of the toy family run.
const TOY_FAMILY_ENGINE: &str = r#"//! TEST FIXTURE ONLY: the shared engine of the toy family run: the database opened by the default
//! workload module (`crate::agent::workload`), then the verified interpreter's answer. It names no table or column.
use vstd::prelude::*;
use crate::gendb_entry::{answer_meets, bound_db, outcome_ok, stores_ready, supported, Answer};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::stores::Stores;
use crate::exec::ast::{view_ordered, EOrderedQuery};
use crate::exec::relational::schema::{lemma_db_wf_ts_ok, view_rows};
use crate::exec::relational::entry::exec_ordered;
use crate::bridge::order::lemma_denote_top_ok;
use crate::spec::value::Database;

pub mod workload;

verus! {

/// The engine: the database opened by the default module, then the verified interpreter's answer.
pub fn engine(stores: &mut Stores, q: &EOrderedQuery, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        supported(view_ordered(*q)),
        1 <= workers <= MAX_WORKERS,
    ensures
        answer_meets(old(stores)@, view_ordered(*q), r),
{
    let ghost sv = stores@;
    let ghost db = choose|db: Database| bound_db(sv, db);
    let edb = crate::agent::workload::open_database(stores, Ghost(db));
    proof {
        lemma_db_wf_ts_ok(db);
        lemma_denote_top_ok(db, view_ordered(*q));
    }
    let r: Result<Answer, QueryError> = match exec_ordered(&edb, q) {
        Ok(Ok(rows)) => {
            proof {
                assert(crate::link::query::view_rows(rows@) =~= view_rows(rows@));
            }
            Ok(Answer::Rows(rows))
        },
        Ok(Err(e)) => Ok(Answer::SqlError(e)),
        Err(_) => Ok(Answer::Capacity),
    };
    proof {
        assert forall|other: Database| #[trigger] bound_db(sv, other) implies outcome_ok(other, view_ordered(*q), r) by {
            crate::agent::workload::lemma_database_unique(sv, db, other);
        }
    }
    r
}

} // verus!
"#;

/// The storage crate of the toy family's instance over `schema` (built from the flat storage of every table: `flats`
/// with their interfaces) and the engine crate that reads it with the shared engine and the default module, each with
/// its trusted shim; and the instance's whole-schema declaration.
fn toy_family_crates(schema: &[TableDef], flats: &[FlatStorage], interfaces: &[Vec<FrameworkSource>]) -> (Vec<FrameworkSource>, Vec<FrameworkSource>, DeclaredSource) {
    let name = StorageName::new(TOY_FAMILY).unwrap();
    let every: BTreeMap<usize, BTreeSet<usize>> = schema.iter().enumerate().map(|(t, table)| (t, (0..table.columns.len()).collect())).collect();
    let whole = DeclaredSource::for_storage(schema, &every).unwrap();
    assert!(whole_schema_declaration(schema, &whole));
    let sources = flat_uses(flats, interfaces);
    let interface = vec![
        FrameworkSource { path: format!("{}mod.rs", name.interface_prefix()), text: TOY_FAMILY_INTERFACE.into() },
        plain_columns_interface_file(&name),
    ];
    let mut storage = derived_storage_crate_files(schema, &name, &whole, Derivation { sources: &sources, extends: None }, false).unwrap();
    storage.extend(interface.iter().cloned());
    storage.push(FrameworkSource { path: "builder/mod.rs".into(), text: TOY_FAMILY_BUILDER.into() });
    storage.push(FrameworkSource { path: "builder/plan.rs".into(), text: TOY_FAMILY_PLAN.into() });
    let uses = [StorageUse { name: &name, declaration: &whole, interface: &interface }];
    let mut engine = engine_crate_files_with(schema, &uses, "the toy family run's crate", FlatAccess::Uniform).unwrap();
    engine.push(FrameworkSource { path: "agent/mod.rs".into(), text: TOY_FAMILY_ENGINE.into() });
    engine.push(FrameworkSource { path: "agent/workload/mod.rs".into(), text: TOY_DEFAULT_MODULE.into() });
    (with_trusted_shim(storage, GENDB_STORAGE_DERIVED_SHIM_SOURCE), with_trusted_shim(engine, GENDB_ENGINE_SHIM_SOURCE), whole)
}

/// Runs of several workloads: one toy storage family (a plain-copy builder and
/// interface, generic by table id, reading `crate::schema_exec` and `crate::whole_schema`) and one shared toy engine
/// with the default workload module, over two NOT NULL schemas of two and three tables. For each schema the family's
/// instance (a storage crate built from the flat storage of every table, storing every column of every table) and the
/// engine crate that reads only that instance verify whole, 0 errors; the author files are the same bytes in both
/// schemas, pass the member rule set over both schemas (agent, default module, storage files and the plan rule), and the
/// instance composes with the engine crate.
#[test]
#[ignore = "runs the pinned Verus on the toy family's storage crates and engine crates of two schemas; -- --ignored"]
fn one_family_and_default_module_verify_over_two_schemas() {
    let work = work_dir("family-two-schemas");
    let toolchain = VerusToolchain::from_env().unwrap();
    let parser = SqlParser::from_environment().unwrap();
    let schema_a_ddl = work.join("alpha.sql");
    std::fs::write(&schema_a_ddl, FAMILY_SCHEMA_A).unwrap();
    let schema_b_ddl = work.join("beta.sql");
    std::fs::write(&schema_b_ddl, FAMILY_SCHEMA_B).unwrap();
    let alpha = schema_of(&parser, &schema_a_ddl, "SELECT ai_key FROM alpha_item", &work);
    let beta = schema_of(&parser, &schema_b_ddl, "SELECT bo_key FROM beta_one", &work);
    assert_eq!((alpha.len(), beta.len()), (2, 3));

    // The author files pass the member rule set over both schemas.
    let constants = TemplateConstants::default();
    let rules = EngineRuleSet::for_members(&[
        StageWorkload { name: "alpha", schema: &alpha, constants: &constants },
        StageWorkload { name: "beta", schema: &beta, constants: &constants },
    ]);
    for (path, text) in [("agent/mod.rs", TOY_FAMILY_ENGINE), ("agent/workload/mod.rs", TOY_DEFAULT_MODULE)] {
        assert_eq!(rules.scan_agent_source(path, text), vec![], "{path} under the member rules");
    }
    for (path, text) in [("stores/copyfam/interface/mod.rs", TOY_FAMILY_INTERFACE), ("builder/mod.rs", TOY_FAMILY_BUILDER), ("builder/plan.rs", TOY_FAMILY_PLAN)] {
        assert_eq!(rules.scan_storage_source(path, text), vec![], "{path} under the member rules' storage scan");
    }
    assert_eq!(scan_plan_source("default_plan.rs", TOY_FAMILY_PLAN), vec![], "the plan is data");

    let mut evidence = vec![];
    for (name, schema) in [("alpha", &alpha), ("beta", &beta)] {
        let flats = flat_storages(schema);
        let interfaces = flat_interfaces(&flats);
        let (storage, engine, _) = toy_family_crates(schema, &flats, &interfaces);
        assert!(storage.iter().any(|f| f.path == WHOLE_SCHEMA_PATH) && storage.iter().any(|f| f.path == STORAGE_SCHEMA_EXEC_PATH));
        assert!(engine.iter().any(|f| f.path == WHOLE_SCHEMA_PATH));
        check_storage_composition(&storage, &engine, &StorageName::new(TOY_FAMILY).unwrap()).unwrap_or_else(|e| panic!("{name}: composition: {e}"));
        for (kind, files, crate_name) in [("storage", &storage, STORAGE_CRATE_NAME), ("engine", &engine, ENGINE_CRATE_NAME)] {
            let run = verify_only(&toolchain, files, crate_name, &work.join(format!("{name}-{kind}")));
            assert_eq!(run.outcome, VerusOutcome::Verified, "{name} {kind}: {}", run.rendered_errors());
            let verification = run.verification.clone().unwrap();
            assert!(verification.errors == 0 && verification.is_verifying_entire_crate, "{name} {kind}: {verification:?}");
            eprintln!("{name} {kind}: verified whole, {} verified, 0 errors", verification.verified);
            evidence.push(json!({"schema": name, "crate": kind, "outcome": run.outcome, "verification": run.verification, "wall_ns": run.wall_ns}));
        }
    }
    let evidence = json!({"crates": evidence, "rule_set": rules.record(), "family": TOY_FAMILY,
        "author_files": "the same interface, builder, plan, default module and engine text in both schemas' crates"});
    std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", work.join("evidence.json").display());
}

// ------------------------------------------------ one family builder text over the nullable items, every schema

/// TEST FIXTURE ONLY: the root of a toy family builder whose column reader (`read`) is under test.
const TOY_READER_ROOT: &str = r#"//! TEST FIXTURE ONLY: the root of a toy family builder whose column reader (`read`) is under test:
//! `build` is a stub, type-checked and not verified (the run verifies `sources_flat` and `builder::read` only).
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::gendb_entry::layout::owned_parts_view;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::sources::Stores;
use crate::gendb_entry::storage::{represents, stored_relations};
use crate::spec::value::Database;

pub mod plan;
pub mod read;

verus! {

/// The toy plan (`plan::plan()`).
pub struct Plan {
    pub sorted: Vec<usize>,
}

/// A stub: the module-scoped run does not verify it.
pub fn build(stores: &mut Stores, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        sources_ready(old(stores)@),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(p) ==> forall|db: Database| #[trigger] sources_bound(old(stores)@, db)
            ==> represents(storage_parts(old(stores)@, owned_parts_view(p@)), stored_relations(db)),
        r matches Err(e) ==> e is WorkerFailed,
{
    vstd::pervasive::unreached()
}

} // verus!
"#;

/// TEST FIXTURE ONLY: a family builder's column reader over the nullable items, the same text in every instance.
const TOY_NULLABLE_READER: &str = r#"//! TEST FIXTURE ONLY: the column reader of a toy family builder, the same text in every workload's
//! instance: column `c` of table `t` read from the flat sources (`crate::sources_flat`, by table and column id) with the
//! reader its declared nullability calls for (`crate::schema_exec`'s nullability, linked with `lemma_nullable_column`),
//! as a family builder does. Over a schema without nullable columns `nullable_column` is false and the nullable branch
//! is never taken; the text compiles and verifies there all the same.
use vstd::prelude::*;
use crate::gendb_entry::sources::Stores;
use crate::exec::relational::schema::{view_schema, ETableSchema};
use crate::schema::schema_spec;
use crate::schema_exec::schema_exec;
use crate::sources_flat::{
    column_slice, flat_bound, flat_table, is_flat_table, lemma_nullable_column, nullable_column_slice, slice_value, table_rows, ColumnSlice,
};
use crate::spec::types::Column;
use crate::spec::value::{Database, Val};

verus! {

/// Row `j` of a column read as the values `s` with the validity `valid` (`None`: a column that is not nullable).
pub open spec fn read_value(s: ColumnSlice, valid: Option<&'static [u8]>, j: int) -> Val {
    match valid {
        Some(v) => if v@[j] == 0 { Val::Null } else { slice_value(s, j) },
        None => slice_value(s, j),
    }
}

/// Rows `0..n` (at least one) of column `c` of flat-stored table `t`, declared `col`: row `j` of the column is
/// `read_value(r.0, r.1, j)`, with a validity exactly when the column is nullable.
pub fn read_column(stores: &mut Stores, t: usize, c: usize, n: usize, col: Column, Ghost(db): Ghost<Database>) -> (r: (ColumnSlice, Option<&'static [u8]>))
    requires
        flat_bound(old(stores)@, db),
        flat_table(t as int),
        c < schema_spec()[t as int].columns.len(),
        col == schema_spec()[t as int].columns[c as int],
        n == db.tables[t as int].len(),
        n >= 1,
    ensures
        final(stores)@ == old(stores)@,
        (r.1 matches Some(_)) == col.nullable,
        forall|j: int| 0 <= j < n ==> #[trigger] db.tables[t as int][j][c as int] == read_value(r.0, r.1, j),
{
    proof {
        lemma_nullable_column(t as int, c as int);
    }
    if col.nullable {
        let (s, v) = nullable_column_slice(stores, t, c, 0, n, Ghost(db));
        proof {
            assert forall|j: int| 0 <= j < n implies #[trigger] db.tables[t as int][j][c as int] == read_value(s, Some(v), j) by {
                assert(db.tables[t as int][0 + j][c as int] == if v@[j] == 0 { Val::Null } else { slice_value(s, j) });
            }
        }
        (s, Some(v))
    } else {
        let s = column_slice(stores, t, c, 0, n, Ghost(db));
        proof {
            assert forall|j: int| 0 <= j < n implies #[trigger] db.tables[t as int][j][c as int] == read_value(s, None, j) by {
                assert(db.tables[t as int][0 + j][c as int] == slice_value(s, j));
            }
        }
        (s, None)
    }
}

/// Every column of flat-stored table `t` read once with `read_column` (nothing for an empty table), each declared
/// as `schema_exec()` states.
fn read_table(stores: &mut Stores, schema: &Vec<ETableSchema>, t: usize, Ghost(db): Ghost<Database>)
    requires
        flat_bound(old(stores)@, db),
        flat_table(t as int),
        view_schema(schema@) == schema_spec(),
        t < schema@.len(),
    ensures
        final(stores)@ == old(stores)@,
{
    let n = table_rows(stores, t, Ghost(db));
    let width = schema[t].columns.len();
    proof {
        assert(view_schema(schema@)[t as int].columns == schema@[t as int].columns@);
    }
    let mut c: usize = 0;
    while c < width
        invariant
            stores@ == old(stores)@,
            flat_bound(stores@, db),
            flat_table(t as int),
            t < schema@.len(),
            width == schema@[t as int].columns@.len(),
            schema_spec()[t as int].columns == schema@[t as int].columns@,
            n == db.tables[t as int].len(),
            c <= width,
        decreases width - c,
    {
        if n > 0 {
            let col = schema[t].columns[c];
            let _ = read_column(stores, t, c, n, col, Ghost(db));
        }
        c += 1;
    }
}

/// Every column of every flat-stored table of the schema, by table and column id.
pub fn read_every_column(stores: &mut Stores, Ghost(db): Ghost<Database>)
    requires
        flat_bound(old(stores)@, db),
    ensures
        final(stores)@ == old(stores)@,
{
    let schema = schema_exec();
    let mut t: usize = 0;
    while t < schema.len()
        invariant
            stores@ == old(stores)@,
            flat_bound(stores@, db),
            view_schema(schema@) == schema_spec(),
        decreases schema.len() - t,
    {
        if is_flat_table(t) {
            read_table(stores, &schema, t, Ghost(db));
        }
        t += 1;
    }
}

} // verus!
"#;

/// The storage crate of the toy family's instance over `schema` (built from the flat storage of every table) with the
/// builder under test: the stub root, the column reader and the toy plan, with its trusted shim.
fn toy_reader_crate(schema: &[TableDef], flats: &[FlatStorage], interfaces: &[Vec<FrameworkSource>]) -> Vec<FrameworkSource> {
    let name = StorageName::new(TOY_FAMILY).unwrap();
    let every: BTreeMap<usize, BTreeSet<usize>> = schema.iter().enumerate().map(|(t, table)| (t, (0..table.columns.len()).collect())).collect();
    let whole = DeclaredSource::for_storage(schema, &every).unwrap();
    assert!(whole_schema_declaration(schema, &whole));
    let sources = flat_uses(flats, interfaces);
    let mut storage = derived_storage_crate_files(schema, &name, &whole, Derivation { sources: &sources, extends: None }, false).unwrap();
    storage.extend([
        FrameworkSource { path: format!("{}mod.rs", name.interface_prefix()), text: TOY_FAMILY_INTERFACE.into() },
        plain_columns_interface_file(&name),
        FrameworkSource { path: "builder/mod.rs".into(), text: TOY_READER_ROOT.into() },
        FrameworkSource { path: "builder/read.rs".into(), text: TOY_NULLABLE_READER.into() },
        FrameworkSource { path: "builder/plan.rs".into(), text: TOY_FAMILY_PLAN.into() },
    ]);
    with_trusted_shim(storage, GENDB_STORAGE_DERIVED_SHIM_SOURCE)
}

/// One family builder text that reads the flat sources with the nullable items (`lemma_nullable_column`,
/// `nullable_column_slice`, `column_slice` for `!nullable_column(t, c)`, the nullability from `crate::schema_exec`)
/// compiles and verifies in the family's instance over a NOT NULL schema (`nullable_column` false: the items are the
/// uniform ones) and over a schema with nullable columns of every stored type. Module-scoped: `sources_flat` and the
/// builder's reader `builder::read` are verified, 0 errors; the rest of each crate is type-checked (the builder root is
/// a stub), so this run is no crate evidence. The reader text passes the member rule set's storage scan over both
/// schemas.
#[test]
#[ignore = "runs the pinned Verus (module-scoped) on the toy family's instances over a NOT NULL and a nullable schema; -- --ignored"]
fn one_family_builder_reads_nullable_columns_in_every_schema() {
    let work = work_dir("family-nullable-reader");
    let toolchain = VerusToolchain::from_env().unwrap();
    let parser = SqlParser::from_environment().unwrap();
    let alpha_ddl = work.join("alpha.sql");
    std::fs::write(&alpha_ddl, FAMILY_SCHEMA_A).unwrap();
    let alpha = schema_of(&parser, &alpha_ddl, "SELECT ai_key FROM alpha_item", &work);
    let nullable_ddl = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/verus_flat/nullable_schema.sql");
    let nullable = schema_of(&parser, &nullable_ddl, "SELECT id FROM filing", &work);
    assert!(alpha.iter().all(|t| t.columns.iter().all(|c| !c.nullable)) && nullable.iter().any(|t| t.columns.iter().any(|c| c.nullable)));

    let constants = TemplateConstants::default();
    let rules = EngineRuleSet::for_members(&[
        StageWorkload { name: "alpha", schema: &alpha, constants: &constants },
        StageWorkload { name: "nullable", schema: &nullable, constants: &constants },
    ]);
    for (path, text) in [("builder/mod.rs", TOY_READER_ROOT), ("builder/read.rs", TOY_NULLABLE_READER)] {
        assert_eq!(rules.scan_storage_source(path, text), vec![], "{path} under the member rules' storage scan");
    }

    let mut evidence = vec![];
    for (name, schema) in [("alpha", &alpha), ("nullable", &nullable)] {
        let flats = flat_storages(schema);
        let interfaces = flat_interfaces(&flats);
        let files = toy_reader_crate(schema, &flats, &interfaces);
        let access = &files.iter().find(|f| f.path == FlatAccessSite::DerivedSources.path()).unwrap().text;
        let degenerate = access.contains("pub open spec fn nullable_column(t: int, c: int) -> bool {\n    false\n}");
        assert_eq!(degenerate, name == "alpha", "{name}: the nullable items are degenerate exactly without a nullable column");
        let unscanned: Vec<&str> = files.iter().filter(|f| gendb_registry::author_definition(&f.path).is_none()).map(|f| f.path.as_str()).collect();
        let frozen = freeze_framework_crate(&files, &unscanned, &work.join(name).join("frozen")).unwrap_or_else(|e| panic!("{name}: {e:?}"));
        let options = VerusOptions { crate_name: STORAGE_CRATE_NAME.into(), ..options() };
        let modules = ["sources_flat".to_string(), "builder::read".to_string()];
        let run = with_build_lock(|| verify_modules(&toolchain, &frozen, &options, &modules, &work.join(name).join("verus")).unwrap());
        let summary = run.verification.clone().unwrap();
        assert!(run.outcome == VerusOutcome::Verified && summary.errors == 0 && summary.verified > 0, "{name}: {} {}", run.detail, run.rendered_errors());
        eprintln!("{name}: sources_flat and builder::read verified (module-scoped), {} verified, 0 errors, {:.1} s", summary.verified, run.wall_ns as f64 / 1e9);
        evidence.push(json!({"schema": name, "scope": modules, "outcome": run.outcome, "verification": run.verification, "wall_ns": run.wall_ns}));
    }
    let evidence = json!({"crates": evidence, "rule_set": rules.record(), "family": TOY_FAMILY,
        "author_files": "the same builder root, reader, plan and interface text in both schemas' instances"});
    std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", work.join("evidence.json").display());
}

/// A family instance a run recorded over the TPC-H schema (`GENDB_RECORDED_FAMILY_INSTANCE`: a frozen
/// storage directory `<frozen>/storages/<family>` with its `storage.json` and `crate/src/**`), assembled again by this
/// generation from the TPC-H schema of [`tpch_schema`] and the generated flat storages, in the recorded source order:
/// the framework files are the recorded set, every one but `sources_flat.rs` the recorded text byte for byte, and the
/// crate with the recorded author files verifies whole, 0 errors. Reads the directory only.
#[test]
#[ignore = "runs the pinned Verus on a recorded TPC-H family instance (GENDB_RECORDED_FAMILY_INSTANCE); -- --ignored"]
fn recorded_tpch_family_instance_verifies_with_this_generation() {
    let dir = PathBuf::from(std::env::var_os("GENDB_RECORDED_FAMILY_INSTANCE").expect("GENDB_RECORDED_FAMILY_INSTANCE: a frozen family instance"));
    let work = work_dir("recorded-family-instance");
    let toolchain = VerusToolchain::from_env().unwrap();
    let parser = SqlParser::from_environment().unwrap();
    let (_, schema) = tpch_schema(&parser, &work);
    let record: Value = serde_json::from_str(&std::fs::read_to_string(dir.join("storage.json")).unwrap()).unwrap();
    let name = StorageName::new(record["manifest"]["name"].as_str().unwrap()).unwrap();
    let declaration: DeclaredSource = serde_json::from_value(record["declaration"].clone()).unwrap();
    assert!(whole_schema_declaration(&schema, &declaration), "{name}: a whole-schema storage (a family's instance)");
    let flats = flat_storages(&schema);
    let interfaces = flat_interfaces(&flats);
    let order: Vec<usize> = record["derivation"]["sources"]
        .as_array()
        .unwrap()
        .iter()
        .map(|s| flats.iter().position(|f| f.name.as_str() == s["name"].as_str().unwrap()).unwrap_or_else(|| panic!("{s}: not a flat storage")))
        .collect();
    let sources: Vec<StorageUse<'_>> = order.iter().map(|&k| StorageUse { name: &flats[k].name, declaration: &flats[k].declaration, interface: &interfaces[k] }).collect();
    let extends = record["derivation"]["extends"].as_u64().map(|k| k as usize);
    let framework = with_trusted_shim(
        derived_storage_crate_files(&schema, &name, &declaration, Derivation { sources: &sources, extends }, false).unwrap(),
        GENDB_STORAGE_DERIVED_SHIM_SOURCE,
    );
    let src = dir.join("crate/src");
    let recorded = |path: &str| std::fs::read_to_string(src.join(path)).unwrap_or_else(|e| panic!("{path}: {e}"));
    let listed: BTreeSet<&str> = record["framework_files"].as_array().unwrap().iter().map(|p| p.as_str().unwrap()).collect();
    assert_eq!(framework.iter().map(|f| f.path.as_str()).collect::<BTreeSet<_>>(), listed, "the recorded framework files");
    let changed: Vec<String> = framework.iter().filter(|f| recorded(&f.path) != f.text).map(|f| f.path.clone()).collect();
    eprintln!("{name}: framework files this generation changes: {changed:?}");
    assert!(changed.iter().all(|p| *p == FlatAccessSite::DerivedSources.path()), "only sources_flat.rs may change: {changed:?}");
    let mut files = framework;
    for path in record["author_files"].as_array().unwrap() {
        let path = path.as_str().unwrap();
        files.push(FrameworkSource { path: path.into(), text: recorded(path) });
    }
    let run = verify_only(&toolchain, &files, STORAGE_CRATE_NAME, &work);
    assert_eq!(run.outcome, VerusOutcome::Verified, "{name}: {}", run.rendered_errors());
    let verification = run.verification.clone().unwrap();
    assert!(verification.errors == 0 && verification.is_verifying_entire_crate, "{name}: {verification:?}");
    eprintln!("{name}: verified whole, {} verified, 0 errors, {:.1} s", verification.verified, run.wall_ns as f64 / 1e9);
    let evidence = json!({"instance": dir, "changed": changed, "outcome": run.outcome, "verification": run.verification, "wall_ns": run.wall_ns});
    std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", work.join("evidence.json").display());
}

// ----------------------------------------------------------------------------------- calls through worker children

/// Write the flat assets of `tables` (rows per table, table id order) under `dir`: one parts directory per table, in
/// the flat storage's part order. Returns the storage uses in the engine crate's use order.
fn flat_assets(flats: &[FlatStorage], tables: &HostTables, dir: &Path) -> Vec<StorageUseInput> {
    flats
        .iter()
        .map(|flat| {
            let table_id = flat.declaration.tables[0].table_id;
            let rows = &tables[table_id];
            let parts_directory = dir.join(flat.name.as_str());
            let mut writer = PartFilesWriter::new(&parts_directory, PartsFormat::LittleEndian).unwrap();
            for part in &flat.parts {
                let k = flat.declaration.tables[0].columns.iter().position(|c| c.ordinal == part.ordinal).unwrap();
                let column: Vec<&HostValue> = rows.iter().map(|r| &r[k]).collect();
                let (elem, len, bytes) = part_bytes(part.buffer, &column, &flat.table, &part.column);
                writer.write_part(elem, len, &bytes).unwrap();
            }
            writer.finish().unwrap();
            StorageUseInput { name: flat.name.to_string(), parts_directory }
        })
        .collect()
}

/// The element type, element count and host-order bytes of one flat part of `column`.
fn part_bytes(buffer: FlatBuffer, column: &[&HostValue], table: &str, name: &str) -> (PartElem, usize, Vec<u8>) {
    let refuse = |v: &HostValue| -> ! { panic!("{table}.{name}: value {v:?} has no flat representation") };
    let mut bytes = vec![];
    match buffer {
        FlatBuffer::Values => {
            let elem = match column.first() {
                Some(HostValue::Num { .. }) => PartElem::I128,
                Some(HostValue::Date(_)) => PartElem::I32,
                _ => PartElem::I64,
            };
            for v in column {
                match (elem, v) {
                    (PartElem::I64, HostValue::Int(x)) => bytes.extend(x.to_le_bytes()),
                    (PartElem::I128, HostValue::Num { coeff, .. }) => bytes.extend(coeff.to_le_bytes()),
                    (PartElem::I32, HostValue::Date(d)) => bytes.extend((d + 10957).to_le_bytes()),
                    _ => refuse(v),
                }
            }
            (elem, column.len(), bytes)
        }
        FlatBuffer::Offsets => {
            let mut end = 0i64;
            bytes.extend(end.to_le_bytes());
            for v in column {
                let HostValue::Text(t) = v else { refuse(v) };
                end += t.len() as i64;
                bytes.extend(end.to_le_bytes());
            }
            (PartElem::I64, column.len() + 1, bytes)
        }
        FlatBuffer::Bytes => {
            for v in column {
                let HostValue::Text(t) = v else { refuse(v) };
                bytes.extend(t);
            }
            (PartElem::U8, bytes.len(), bytes)
        }
        // The TPC-H fixtures have no nullable column.
        FlatBuffer::Validity => panic!("{table}.{name}: a validity part (the TPC-H schema has no nullable column)"),
    }
}

/// Statements over the TPC-H schema (no parameters) that use the constructors the 22 templates do not.
const COVERAGE_SQL: [&str; 3] = [
    "SELECT DISTINCT -l_quantity AS nq, l_orderkey / 2 AS half, l_linenumber * 3 - 1 AS x, true AS t FROM lineitem \
     WHERE NOT (l_comment IS NULL) OR l_shipdate >= DATE '1995-01-01' OR l_shipdate < DATE '1990-01-01' \
     ORDER BY nq DESC NULLS LAST, half LIMIT 5 OFFSET 2",
    "SELECT SUBSTRING(c_phone FROM 1 FOR 2) AS cc, SUBSTRING(c_name FROM 3) AS rest, EXTRACT(MONTH FROM o_orderdate) AS m, \
     EXTRACT(DAY FROM o_orderdate) AS d, AVG(o_shippriority) AS a, SUM(o_custkey) AS s, MIN(c_name) AS mn, MAX(c_name) AS mx, \
     COUNT(o_comment) AS cnt, COUNT(DISTINCT o_clerk) AS dc \
     FROM customer LEFT JOIN orders ON c_custkey = o_custkey AND o_comment NOT LIKE '%x%' \
     GROUP BY SUBSTRING(c_phone FROM 1 FOR 2), SUBSTRING(c_name FROM 3), EXTRACT(MONTH FROM o_orderdate), EXTRACT(DAY FROM o_orderdate) \
     HAVING COUNT(*) <> 0",
    "SELECT o_orderkey, CAST(o_orderdate AS timestamp) + INTERVAL '1' DAY AS ts, CASE WHEN o_totalprice > 10.5 THEN NULL ELSE o_totalprice END AS p \
     FROM orders WHERE EXISTS (SELECT 1 FROM lineitem WHERE l_orderkey = o_orderkey) \
     AND o_custkey NOT IN (SELECT c_custkey FROM customer WHERE c_acctbal <= -1.25) AND o_orderstatus <> 'é' ORDER BY o_orderkey DESC",
];

/// `SELECT * FROM` table 99 as AST bytes: decodable (`Table(99)`, no key, no limit, offset 0), not well typed.
fn table_99_ast() -> Vec<u8> {
    let mut ast = b"GSQLAST1".to_vec();
    ast.push(0);
    ast.extend(99u32.to_le_bytes());
    ast.extend(0u32.to_le_bytes());
    ast.push(0);
    ast.extend(0u64.to_le_bytes());
    ast
}

/// The node tags and operator values (`field:value`) of a document: what its encoding exercises.
fn constructors(doc: &AstDocument, into: &mut BTreeSet<String>) {
    for node in &doc.nodes {
        into.insert(node.tag.clone());
        let kind = &gendb_frontend::ast::schema().kinds[&node.tag];
        for ((name, _), value) in kind.fields.iter().zip(&node.fields) {
            match value {
                gendb_frontend::ast::FieldValue::Enum(e) => {
                    into.insert(format!("{name}:{e}"));
                }
                gendb_frontend::ast::FieldValue::ScalarTy(t) => {
                    into.insert(format!("{name}:{}", t.kind));
                }
                gendb_frontend::ast::FieldValue::OptNat(Some(_)) => {
                    into.insert(format!("{name}:some"));
                }
                gendb_frontend::ast::FieldValue::Bool(true) => {
                    into.insert(format!("{name}:true"));
                }
                _ => {}
            }
        }
    }
}

/// The answer rows of an `Ok` call (decoded from its result wire).
fn answer_rows(result: &WorkerResult, call: usize) -> Result<Vec<Vec<HostValue>>, String> {
    let outcome = &result.observations[call].outcome;
    match QueryAnswer::of(outcome) {
        Ok(QueryAnswer::Rows(rows)) => Ok(rows),
        other => Err(format!("status {:?}: {other:?}", outcome.status)),
    }
}

#[test]
#[ignore = "runs the pinned Verus, the frontend, reference evaluators and the gendb worker; set GENDB_WORKER; -- --ignored"]
fn engine_calls_round_trip_and_answer_as_the_reference() {
    let worker = PathBuf::from(std::env::var_os("GENDB_WORKER").expect("GENDB_WORKER: the gendb executable"));
    let work = work_dir("calls");
    let toolchain = VerusToolchain::from_env().unwrap();
    let parser = SqlParser::from_environment().unwrap();
    let (ddl, schema) = tpch_schema(&parser, &work);
    let flats = flat_storages(&schema);
    let (library, origin) = compiled_engine(&toolchain, &engine_crate(&schema, &flats, &version_0(&schema, &flats)), &work.join("engine"));
    let visible: Value = serde_json::from_str(&std::fs::read_to_string(repository().join("output/tpch-sf100/bindings/visible.json")).unwrap()).unwrap();

    let mut records = vec![];
    for t in templates() {
        let template_doc = translate(&parser, &ddl, &t);
        assert_eq!(template_doc.tables, schema, "{}: one schema for every template", t.name);
        let bindings = visible_bindings(&visible, &t.name);
        assert_eq!(bindings.iter().map(|(id, _)| id.as_str()).collect::<Vec<_>>(), ["v0", "v1", "v2"], "{}", t.name);
        let encoded: Vec<EngineAst> =
            bindings.iter().map(|(id, args)| encode_binding(&template_doc, args).unwrap_or_else(|e| panic!("{} {id}: {e}", t.name))).collect();
        for (i, a) in encoded.iter().enumerate() {
            assert_eq!(encode_binding(&template_doc, &bindings[i].1).unwrap().bytes, a.bytes, "{}: deterministic encoding", t.name);
        }

        // The template's own tiny database, as flat assets.
        let case = fixtures_dir().join(format!("pg_reference/tpch_all22_cases/{}.json", t.name.to_lowercase()));
        let tables = Fixture::load(&case).unwrap().database_for(&template_doc).unwrap();
        let dir = work.join(&t.name);
        let uses = flat_assets(&flats, &tables, &dir.join("assets"));

        // One engine job: the echo of every binding's AST, then one call per binding.
        let asts: Vec<Vec<u8>> = encoded.iter().map(|a| a.bytes.clone()).collect();
        let request = WorkerRequest::for_engine_query(&library, uses, PartAccess::default(), &asts, vec![1], 1, RANGE_CAPACITY);
        let result = spawn(&worker, &dir.join("worker"), &request, 3600).unwrap_or_else(|e| panic!("{}: {e}", t.name));
        assert_eq!(result.echoes.len(), 3, "{}", t.name);
        for (i, a) in encoded.iter().enumerate() {
            assert_eq!(result.echoes[i], echo_text(&a.document), "{} {}: the engine's echo differs from the bound document", t.name, bindings[i].0);
            assert_eq!(result.observations[i].binding, Some(i));
        }

        // The reference: the verified evaluator of the bound v0 document on the same database.
        let reference_dir = dir.join("reference");
        let build = with_build_lock(|| {
            build_evaluator(&toolchain, &encoded[0].document, &reference_dir.join("ast.json"), &reference_dir.join("build"), &BuildOptions::default())
                .unwrap()
        });
        assert_eq!(build.status, BuildStatus::Ok, "{}: reference build {}", t.name, build.record);
        let reference = EvaluatorLibrary::load(build.library.as_ref().unwrap()).unwrap().run(&tables).unwrap();
        let RunOutcome::Rows(expected) = reference else { panic!("{}: the reference answered {reference:?}", t.name) };
        let engine_rows = answer_rows(&result, 0).unwrap_or_else(|e| panic!("{} v0: {e}", t.name));
        assert_eq!(engine_rows, expected, "{} v0: the engine's rows differ from the reference evaluator's", t.name);
        let statuses: Vec<CallStatus> = result.observations.iter().map(|o| o.outcome.status).collect();
        records.push(json!({"template": t.name, "ast_bytes": asts.iter().map(Vec::len).collect::<Vec<_>>(), "echo_equal": [true, true, true],
            "statuses": statuses, "v0_rows": expected.len(), "reference_verification": build.record["run"]["verification"], "case": case}));
        eprintln!("{}: echo v0-v2 equal, v0 rows {} equal to the reference", t.name, expected.len());
    }
    let evidence = json!({"engine_library": library, "engine_origin": origin, "templates": records});
    std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", work.join("evidence.json").display());
}

#[test]
#[ignore = "runs the frontend and the gendb worker over version 0 (pinned Verus once if not cached); set GENDB_WORKER; -- --ignored"]
fn engine_coverage_statements_and_refusals() {
    let worker = PathBuf::from(std::env::var_os("GENDB_WORKER").expect("GENDB_WORKER: the gendb executable"));
    let work = work_dir("coverage");
    let toolchain = VerusToolchain::from_env().unwrap();
    let parser = SqlParser::from_environment().unwrap();
    let (ddl, schema) = tpch_schema(&parser, &work);
    let flats = flat_storages(&schema);
    let (library, origin) = compiled_engine(&toolchain, &engine_crate(&schema, &flats, &version_0(&schema, &flats)), &work.join("engine"));
    let visible: Value = serde_json::from_str(&std::fs::read_to_string(repository().join("output/tpch-sf100/bindings/visible.json")).unwrap()).unwrap();

    // What the 66 template instances exercise (encoding only).
    let mut exercised = BTreeSet::new();
    for t in templates() {
        let doc = translate(&parser, &ddl, &t);
        for (id, args) in visible_bindings(&visible, &t.name) {
            constructors(&encode_binding(&doc, &args).unwrap_or_else(|e| panic!("{} {id}: {e}", t.name)).document, &mut exercised);
        }
    }
    let from_templates = exercised.clone();

    // The coverage statements and the two refusals, in one engine job over Q01's tiny database.
    let mut coverage = vec![];
    for (i, sql) in COVERAGE_SQL.iter().enumerate() {
        let path = work.join(format!("coverage-{i}.sql"));
        std::fs::write(&path, sql).unwrap();
        let (_, translation) = parser.translate(&ddl, &path, "postgres", &[]).unwrap();
        let Translation::Ok(doc) = translation else { panic!("coverage statement {i} refused: {translation:?}") };
        let ast = encode_binding(&doc, &[]).unwrap();
        constructors(&ast.document, &mut exercised);
        coverage.push(ast);
    }
    let mut asts: Vec<Vec<u8>> = coverage.iter().map(|a| a.bytes.clone()).collect();
    asts.extend([b"GSQLAST1\x09".to_vec(), table_99_ast()]);
    let q01 = templates().into_iter().next().unwrap();
    let tables = Fixture::load(&fixtures_dir().join("pg_reference/tpch_all22_cases/q01.json")).unwrap().database_for(&translate(&parser, &ddl, &q01)).unwrap();
    let uses = flat_assets(&flats, &tables, &work.join("assets"));
    let request = WorkerRequest::for_engine_query(&library, uses, PartAccess::default(), &asts, vec![1, 2], 1, RANGE_CAPACITY);
    let result = spawn(&worker, &work.join("worker"), &request, 3600).unwrap();
    let n = coverage.len();
    for (i, a) in coverage.iter().enumerate() {
        assert_eq!(result.echoes[i], echo_text(&a.document), "coverage statement {i}: echo");
        for call in result.observations.iter().filter(|o| o.binding == Some(i)) {
            assert_eq!(call.outcome.status, CallStatus::Ok, "coverage statement {i}: {:?}", call.outcome);
        }
    }
    assert_eq!(result.echoes[n], "(Malformed)");
    assert_eq!(result.echoes[n + 1], "(OrderedQuery (Table 99) [] none 0)");
    for call in &result.observations {
        match call.binding {
            Some(b) if b == n => assert_eq!(call.outcome.status, CallStatus::Malformed),
            Some(b) if b == n + 1 => assert_eq!(call.outcome.status, CallStatus::ParamRefused),
            _ => {}
        }
        assert!(call.outcome.result_wire.is_some() == (call.outcome.status == CallStatus::Ok), "{:?}", call.outcome);
    }
    let codec: BTreeSet<String> = gendb_frontend::ast::schema()
        .kinds
        .iter()
        .filter(|(name, k)| k.sort != "ordered" && k.sort != "order_key" && *name != "Param")
        .map(|(name, _)| name.clone())
        .collect();
    let not_exercised: Vec<&String> = codec.iter().filter(|c| !exercised.contains(*c)).collect();
    let evidence = json!({"engine_library": library, "engine_origin": origin,
        "coverage_statements": {"echo_equal": true, "statuses": result.observations.iter().map(|o| (o.binding, o.workers, o.outcome.status)).collect::<Vec<_>>()},
        "refusals": {"undecodable": ["(Malformed)", "Malformed"], "table_99": ["(OrderedQuery (Table 99) [] none 0)", "ParamRefused"]},
        "exercised_by_templates": from_templates, "exercised_with_coverage_statements": exercised,
        "codec_constructors_not_exercised": not_exercised});
    std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("not exercised: {not_exercised:?}; evidence: {}", work.join("evidence.json").display());
}

// ------------------------------------------------------------------------------------- per-call limits in admission

/// Rows of the grown lineitem table of [`limited_cells_are_recorded_unfinished_on_the_general_line`]: the three-way
/// self-product has this many cubed rows, which version 0 materializes (seconds of CPU and gigabytes).
const GROWN_LINEITEM_ROWS: usize = 200;

/// Grow lineitem (table `t`) to `rows` rows with copies of its first row under new line numbers (the primary key
/// `(l_orderkey, l_linenumber)` stays unique; every foreign key of a copy is the first row's).
fn grow_lineitem(schema: &[TableDef], tables: &mut HostTables, rows: usize) {
    let t = schema.iter().position(|d| d.name == "lineitem").unwrap();
    let line = schema[t].columns.iter().position(|c| c.name == "l_linenumber").unwrap();
    let first = tables[t][0].clone();
    for k in 0..rows.saturating_sub(tables[t].len()) {
        let mut row = first.clone();
        row[line] = HostValue::Int(1000 + k as i64);
        tables[t].push(row);
    }
}

#[test]
#[ignore = "runs the frontend and the gendb worker over version 0 (pinned Verus once if not cached); set GENDB_WORKER; -- --ignored"]
fn limited_cells_are_recorded_unfinished_on_the_general_line() {
    let worker = PathBuf::from(std::env::var_os("GENDB_WORKER").expect("GENDB_WORKER: an executable of this build serving `worker`"));
    let work = work_dir("limits");
    let toolchain = VerusToolchain::from_env().unwrap();
    let parser = SqlParser::from_environment().unwrap();
    let (ddl, schema) = tpch_schema(&parser, &work);
    let flats = flat_storages(&schema);
    let (library, origin) = compiled_engine(&toolchain, &engine_crate(&schema, &flats, &version_0(&schema, &flats)), &work.join("engine"));

    // Q01's tiny database with lineitem grown, as flat assets.
    let probe = work.join("probe.sql");
    std::fs::write(&probe, "SELECT r_regionkey FROM region").unwrap();
    let Translation::Ok(probe) = parser.translate(&ddl, &probe, "postgres", &[]).unwrap().1 else { panic!("schema probe refused") };
    let mut tables = Fixture::load(&fixtures_dir().join("pg_reference/tpch_all22_cases/q01.json")).unwrap().database_for(&probe).unwrap();
    grow_lineitem(&schema, &mut tables, GROWN_LINEITEM_ROWS);
    let uses = flat_assets(&flats, &tables, &work.join("assets"));

    // Three statements with one integer parameter (no saved answers: status only). The slow one evaluates the
    // three-way self-product of lineitem as a scalar subquery once per region row kept by `r_regionkey >= $1`: at `v0`
    // ($1 = 0) it runs, at `v1` ($1 = 1000, no row kept) it never does.
    let dataset: DatasetSpec = serde_json::from_str(TPCH_DATASET).unwrap();
    let constraints: IntegrityConstraints =
        serde_json::from_str(&std::fs::read_to_string(repository().join("src/gendb/fixtures/tpch/integrity-constraints.json")).unwrap()).unwrap();
    let parameters: Vec<ParamRequest> = serde_json::from_value(json!([{"index": 1, "name": "least", "type": "integer", "binding": {"free": {}}}])).unwrap();
    let binding = |name: &str, least: &str| BenchmarkBinding { name: name.into(), arguments: vec![least.into()] };
    let check = |name: &str, sql: &str, bindings: &[BenchmarkBinding]| {
        TemplateCheck::prepare(&parser, &dataset, Some(&constraints), &ValidationPolicy::default(), name, name, sql, &parameters, bindings, &work.join("statements").join(name))
            .unwrap_or_else(|e| panic!("{name}: {e}"))
    };
    let fast = check("fast", "SELECT count(*) AS n FROM region WHERE r_regionkey >= $1", &[binding("v0", "0")]);
    let self_product = check(
        "self_product",
        "SELECT r_regionkey, (SELECT count(*) FROM lineitem a, lineitem b, lineitem c) AS n FROM region WHERE r_regionkey >= $1",
        &[binding("v0", "0"), binding("v1", "1000")],
    );
    let pair_product = check("pair_product", "SELECT count(*) AS n FROM lineitem a, lineitem b WHERE a.l_linenumber >= $1", &[binding("v0", "0")]);
    let runner = CandidateRunner { worker };
    let schema_engine = EngineRunner { runner: &runner, library: &library, uses: &uses, access: PartAccess::default(), limits: None, answer_bound: None };
    let limits = CallLimits { call_limit_ns: 1_000_000_000, ..CallLimits::GENERAL_ENGINE };
    let general = EngineRunner { runner: &runner, library: &library, uses: &uses, access: PartAccess::default(), limits: Some(limits), answer_bound: None };

    // Schema-engine line: no limits, the record has no `unfinished`.
    let fast_ast = fast.ast("v0").unwrap().bytes;
    let unlimited = schema_engine.cell(&fast, "v0", &fast_ast, 1, 2, &work.join("cells/schema-engine-fast"), None).unwrap();
    assert!(unlimited.get("unfinished").is_none() && unlimited["calls"] == 2 && unlimited["echo"]["verdict"] == "equal", "{unlimited:#}");

    // General line: the fast statement finishes; the self-product is recorded unfinished at the time limit, not refused.
    let limited_fast = general.cell(&fast, "v0", &fast_ast, 1, 2, &work.join("cells/general-fast"), None).unwrap();
    assert!(limited_fast.get("unfinished").is_none() && limited_fast["calls"] == 2, "{limited_fast:#}");
    let product_ast = self_product.ast("v0").unwrap().bytes;
    let started = std::time::Instant::now();
    let stopped = general.cell(&self_product, "v0", &product_ast, 1, 2, &work.join("cells/general-self-product"), None).unwrap();
    let wall = started.elapsed();
    assert_eq!((stopped["status"].as_str(), stopped["calls"].as_u64(), stopped["median_hot_wall_ns"].is_null()), (Some("unfinished"), Some(0), true), "{stopped:#}");
    assert_eq!(stopped["unfinished"]["reason"], "over_time_limit", "{stopped:#}");
    assert_eq!((stopped["unfinished"]["statement"].as_u64(), stopped["unfinished"]["repetition"].as_u64()), (Some(0), Some(0)));
    assert_eq!(stopped["echo"]["verdict"], "equal");
    assert!(wall < std::time::Duration::from_secs(4), "stopped within the limit plus 3 s: {wall:?}");

    // Qualification on the general line: the slow statement's `v0` recorded unfinished and its `v1` run in a fresh
    // child and compared, the fast statement compared, the template named unfinished at the timing binding skipped.
    let skipped = [SkippedTemplate { template: "pair_product".into(), workers: 1, reason: UnfinishedReason::OverTimeLimit }];
    let checks = [fast, self_product, pair_product];
    let qualification = qualify_finished_templates(&general, &checks, &skipped, &work.join("qualification")).unwrap();
    assert_eq!(qualification["status"], "saved_answers_agree_where_finished", "{qualification:#}");
    assert_eq!((qualification["cells_unfinished"].as_u64(), qualification["cells_without_saved_answers"].as_u64()), (Some(1), Some(2)));
    assert_eq!(qualification["skipped"][0]["template"], "pair_product");
    let names: Vec<&str> = qualification["templates"].as_array().unwrap().iter().map(|t| t["template"].as_str().unwrap()).collect();
    assert_eq!(names, ["fast", "self_product"]);
    let slow = &qualification["templates"][1]["bindings"];
    assert_eq!((slow[0]["binding"].as_str(), slow[0]["cell"]["status"].as_str(), slow[0]["cell"]["unfinished"]["reason"].as_str()), (Some("v0"), Some("unfinished"), Some("over_time_limit")), "{slow:#}");
    assert_eq!((slow[1]["binding"].as_str(), slow[1]["cell"]["status"].as_str(), slow[1]["echo"]["verdict"].as_str()), (Some("v1"), Some("status_only"), Some("equal")), "{slow:#}");
    assert!(work.join("qualification/self_product-from-v1").is_dir(), "the binding after the stop ran in a fresh child");
    assert!(!work.join("qualification/pair_product").exists(), "a skipped template runs no child");

    // Schema-engine line qualification: the record has none of the limits' keys.
    let unlimited_qualification = qualify_finished_templates(&schema_engine, &checks[..1], &[], &work.join("qualification-schema-engine")).unwrap();
    for key in ["limits", "cells_unfinished", "skipped", "unfinished_rule"] {
        assert!(unlimited_qualification.get(key).is_none(), "{key}: {unlimited_qualification:#}");
    }
    let evidence = json!({"engine_library": library, "engine_origin": origin, "limits": limits, "load_average": std::fs::read_to_string("/proc/loadavg").unwrap_or_default().trim(),
        "schema_engine_cell": unlimited, "general_fast_cell": limited_fast, "general_stopped_cell": stopped, "stopped_cell_wall_ns": wall.as_nanos() as u64,
        "general_qualification": qualification, "schema_engine_qualification": unlimited_qualification});
    std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", work.join("evidence.json").display());
}

// --------------------------------------------------------------------------- a paused schema-engine run, unchanged

/// A paused schema-engine run's round-1 engine crates assemble byte for byte as frozen (read only): for every frozen
/// local job of `GENDB_PAUSED_ENGINE_JOBS` (`<run>/engine/rounds/round-0001/calls/0001/local-jobs/*/frozen`), the
/// framework files of `engine_crate_files` over the TPC-H schema and the job's storage uses (`candidate.json`: name and
/// declaration; the interface files of the frozen crate), with the trusted engine shim and the run's generation
/// identity `schema engine`, are exactly the job's framework files (`candidate.json`'s list) with the frozen texts.
#[test]
#[ignore = "reads a paused schema-engine run's frozen crates (read only; GENDB_PAUSED_ENGINE_JOBS, not part of this repository) and runs the frontend; -- --ignored"]
fn paused_schema_engine_crates_assemble_unchanged() {
    let jobs = PathBuf::from(std::env::var_os("GENDB_PAUSED_ENGINE_JOBS").expect("GENDB_PAUSED_ENGINE_JOBS: the run's round-1 local-jobs directory"));
    let work = work_dir("paused");
    let parser = SqlParser::from_environment().unwrap();
    let (_, schema) = tpch_schema(&parser, &work);
    let mut checked = vec![];
    let mut entries: Vec<PathBuf> = std::fs::read_dir(&jobs).unwrap().map(|e| e.unwrap().path().join("frozen")).filter(|p| p.join("candidate.json").is_file()).collect();
    entries.sort();
    assert!(!entries.is_empty(), "no frozen job under {}", jobs.display());
    for frozen in entries {
        let candidate: Value = serde_json::from_str(&std::fs::read_to_string(frozen.join("candidate.json")).unwrap()).unwrap();
        let src = frozen.join("crate/src");
        let names: Vec<StorageName> = candidate["storage_uses"].as_array().unwrap().iter().map(|u| StorageName::new(u["name"].as_str().unwrap()).unwrap()).collect();
        let declarations: Vec<DeclaredSource> = candidate["storage_uses"].as_array().unwrap().iter().map(|u| serde_json::from_value(u["declaration"].clone()).unwrap()).collect();
        let interfaces: Vec<Vec<FrameworkSource>> = names
            .iter()
            .map(|n| {
                let root = src.join(n.interface_prefix());
                let mut files = vec![];
                let mut stack = vec![root.clone()];
                while let Some(dir) = stack.pop() {
                    for entry in std::fs::read_dir(&dir).unwrap() {
                        let path = entry.unwrap().path();
                        if path.is_dir() {
                            stack.push(path);
                        } else {
                            let relative = path.strip_prefix(&src).unwrap().to_string_lossy().to_string();
                            files.push(FrameworkSource { path: relative, text: std::fs::read_to_string(&path).unwrap() });
                        }
                    }
                }
                files
            })
            .collect();
        let uses: Vec<StorageUse<'_>> = names.iter().zip(&declarations).zip(&interfaces).map(|((name, declaration), interface)| StorageUse { name, declaration, interface }).collect();
        let generated = with_trusted_shim(engine_crate_files(&schema, &uses, "schema engine").unwrap(), GENDB_ENGINE_SHIM_SOURCE);
        let listed: BTreeSet<String> = candidate["framework_files"].as_array().unwrap().iter().map(|p| p.as_str().unwrap().to_string()).collect();
        let produced: BTreeSet<String> = generated.iter().map(|f| f.path.clone()).collect();
        assert_eq!(produced, listed, "{}: the framework file list", frozen.display());
        let differing: Vec<&str> = generated.iter().filter(|f| std::fs::read_to_string(src.join(&f.path)).unwrap() != f.text).map(|f| f.path.as_str()).collect();
        assert_eq!(differing, Vec::<&str>::new(), "{}: framework files that differ from the frozen crate", frozen.display());
        assert!(!produced.iter().any(|p| p.starts_with("flat_tables")), "no flat access in the schema-engine crates");
        checked.push(json!({"job": frozen.parent().unwrap().file_name().unwrap().to_string_lossy(), "uses": names.iter().map(|n| n.as_str()).collect::<Vec<_>>(), "framework_files": produced.len()}));
    }
    eprintln!("{} frozen crates assemble unchanged: {checked:?}", checked.len());
    std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&json!({"jobs": checked})).unwrap()).unwrap();
}

// ------------------------------------------------------------------------------------------------ nullable columns

/// One captured table of the nullable round trip: its Arrow columns (with NULLs) and the same rows as host values.
struct NullableTable {
    projected: gendb_storage::io::ProjectedTable,
    rows: Vec<Vec<HostValue>>,
}

/// The nullable fixture's tables (`filing`, `line`, `unit`, in table id order) as Arrow columns and host rows: every
/// nullable column has a NULL row and non-NULL rows, text includes multi-byte and empty values.
fn nullable_tables() -> Vec<NullableTable> {
    use arrow::array::{ArrayRef, Date32Array, Decimal128Array, Int32Array, Int64Array, StringArray};
    use arrow::datatypes::{Field, Schema};
    use arrow::record_batch::RecordBatch;
    use gendb_artifacts::{ColType, ColumnSpec};
    use std::sync::Arc;
    let table = |name: &str, fields: Vec<(&str, ColType, bool)>, arrays: Vec<ArrayRef>, rows: Vec<Vec<HostValue>>| {
        let specs: Vec<ColumnSpec> = fields.iter().map(|(n, ty, nullable)| ColumnSpec { name: n.to_string(), ty: *ty, nullable: *nullable }).collect();
        let arrow_fields: Vec<Field> = specs.iter().zip(&arrays).map(|(f, a)| Field::new(&f.name, a.data_type().clone(), f.nullable)).collect();
        let batch = RecordBatch::try_new(Arc::new(Schema::new(arrow_fields)), arrays).unwrap();
        let row_count = batch.num_rows();
        let projected = gendb_storage::io::ProjectedTable { table: name.into(), original_indices: (0..specs.len()).collect(), fields: specs, batches: vec![batch], row_count };
        NullableTable { projected, rows }
    };
    let text = |t: &str| HostValue::Text(t.as_bytes().to_vec());
    let null = || HostValue::Null;
    // Date32 days since 1970-01-01; host dates are days since 2000-01-01.
    let (day_a, day_b) = (19023, 10956);
    let filing = table(
        "filing",
        vec![("id", ColType::I32, false), ("fy", ColType::I32, true), ("big", ColType::I64, true), ("amount", ColType::Decimal { p: 28, s: 4 }, true),
            ("filed", ColType::Date32, true), ("label", ColType::Utf8, true), ("code", ColType::Utf8, true), ("kind", ColType::Utf8, true), ("name", ColType::Utf8, false)],
        vec![
            Arc::new(Int32Array::from(vec![1, 2, 3])),
            Arc::new(Int32Array::from(vec![Some(2022), None, Some(-7)])),
            Arc::new(Int64Array::from(vec![Some(9_000_000_000), None, None])),
            Arc::new(Decimal128Array::from(vec![Some(125_000), None, Some(-1)]).with_precision_and_scale(28, 4).unwrap()),
            Arc::new(Date32Array::from(vec![Some(day_a), None, Some(day_b)])),
            Arc::new(StringArray::from(vec![Some("λ label"), None, Some("")])),
            Arc::new(StringArray::from(vec![Some("ab"), None, None])),
            Arc::new(StringArray::from(vec![Some("x"), None, Some("y")])),
            Arc::new(StringArray::from(vec!["first", "second", "third"])),
        ],
        vec![
            vec![HostValue::Int(1), HostValue::Int(2022), HostValue::Int(9_000_000_000), HostValue::Num { coeff: 125_000, scale: 4 }, HostValue::Date(day_a - 10957),
                text("λ label"), text("ab"), text("x"), text("first")],
            vec![HostValue::Int(2), null(), null(), null(), null(), null(), null(), null(), text("second")],
            vec![HostValue::Int(3), HostValue::Int(-7), null(), HostValue::Num { coeff: -1, scale: 4 }, HostValue::Date(day_b - 10957), text(""), null(), text("y"), text("third")],
        ],
    );
    let line = table(
        "line",
        vec![("filing", ColType::I32, false), ("stmt", ColType::Utf8, true), ("n", ColType::I64, false)],
        vec![Arc::new(Int32Array::from(vec![1, 1, 3])), Arc::new(StringArray::from(vec![Some("IS"), None, Some("")])), Arc::new(Int64Array::from(vec![10, 11, 12]))],
        vec![vec![HostValue::Int(1), text("IS"), HostValue::Int(10)], vec![HostValue::Int(1), null(), HostValue::Int(11)], vec![HostValue::Int(3), text(""), HostValue::Int(12)]],
    );
    let unit = table(
        "unit",
        vec![("code", ColType::Utf8, false), ("scale", ColType::I32, false)],
        vec![Arc::new(StringArray::from(vec!["USD", "pure"])), Arc::new(Int32Array::from(vec![2, 0]))],
        vec![vec![text("USD"), HostValue::Int(2)], vec![text("pure"), HostValue::Int(0)]],
    );
    vec![filing, line, unit]
}

/// The flat assets of `flats` from the capture archive `archive`: part `i` of each flat storage is the captured column
/// file of generated part `i` (values, text offsets and bytes, validity), linked as `prepare-flat-storage` places it.
fn flat_assets_from_capture(flats: &[FlatStorage], archive: &Path, dir: &Path) -> Vec<StorageUseInput> {
    let captured = gendb_storage::io::SourceColumns::captured_columns(archive).unwrap();
    flats
        .iter()
        .map(|flat| {
            let parts_directory = dir.join(flat.name.as_str());
            let mut writer = PartFilesWriter::new(&parts_directory, PartsFormat::LittleEndian).unwrap();
            for part in &flat.parts {
                let column = captured.iter().find(|c| c.table == flat.table && c.ordinal == part.ordinal).unwrap();
                let (buffer, elem, len) = match part.buffer {
                    FlatBuffer::Values => (&column.values, flat_part_elem(part.elem), column.rows),
                    FlatBuffer::Offsets => (&column.offsets, PartElem::I64, column.rows + 1),
                    FlatBuffer::Bytes => (&column.bytes, PartElem::U8, column.bytes.as_ref().unwrap().bytes as usize),
                    FlatBuffer::Validity => (&column.validity, PartElem::U8, column.rows),
                };
                let file = buffer.as_ref().unwrap_or_else(|| panic!("{}.{}: no {:?} file", flat.table, part.column, part.buffer));
                writer.add_file_part(elem, len, &file.path).unwrap();
            }
            writer.finish().unwrap();
            StorageUseInput { name: flat.name.to_string(), parts_directory }
        })
        .collect()
}

fn flat_part_elem(elem: gendb_verification::obligations::FlatElem) -> PartElem {
    use gendb_verification::obligations::FlatElem;
    match elem {
        FlatElem::I32 => PartElem::I32,
        FlatElem::I64 => PartElem::I64,
        FlatElem::I128 => PartElem::I128,
        FlatElem::U8 => PartElem::U8,
    }
}

/// Statements of the nullable round trip: every cell of every table, and aggregates and filters over NULLs.
const NULLABLE_SQL: [&str; 2] = [
    "SELECT * FROM filing, line, unit",
    "SELECT COUNT(fy) AS c, COUNT(*) AS n, SUM(amount) AS s, MIN(label) AS m, MAX(filed) AS f, COUNT(stmt) AS k \
     FROM filing LEFT JOIN line ON id = filing WHERE code IS NULL OR kind IS NOT NULL OR stmt IS NULL",
];

#[test]
#[ignore = "runs the pinned Verus, the frontend, reference evaluators and the gendb worker; set GENDB_WORKER; -- --ignored"]
fn nullable_columns_round_trip_from_the_capture_through_version_0() {
    let worker = PathBuf::from(std::env::var_os("GENDB_WORKER").expect("GENDB_WORKER: the gendb executable"));
    let work = work_dir("nullable");
    let toolchain = VerusToolchain::from_env().unwrap();
    let parser = SqlParser::from_environment().unwrap();
    let ddl = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/verus_flat/nullable_schema.sql");
    let translate_sql = |name: &str, sql: &str| -> AstDocument {
        let file = work.join(format!("{name}.sql"));
        std::fs::write(&file, sql).unwrap();
        let (_, translation) = parser.translate(&ddl, &file, "postgres", &[]).unwrap();
        let Translation::Ok(doc) = translation else { panic!("{name}: refused: {translation:?}") };
        doc
    };
    let schema = translate_sql("probe", "SELECT id FROM filing").tables;
    assert_eq!(schema.iter().map(|t| t.name.as_str()).collect::<Vec<_>>(), ["filing", "line", "unit"]);
    let flats = flat_storages(&schema);
    let (library, origin) = compiled_engine_in(&toolchain, &engine_crate(&schema, &flats, &version_0(&schema, &flats)), &work.join("engine"), "version-0-nullable-engine");

    // A storage crate built from the flat storage of `line` (keeping its parts), with `sources_flat.rs` over it.
    let interfaces = flat_interfaces(&flats);
    let uses_of_flats = flat_uses(&flats, &interfaces);
    let kept = StorageName::new("line_kept").unwrap();
    let mut files =
        derived_storage_crate_files(&schema, &kept, &flats[1].declaration, Derivation { sources: &uses_of_flats[1..2], extends: Some(0) }, false).unwrap();
    let sources_flat = files.iter().find(|f| f.path == FlatAccessSite::DerivedSources.path()).unwrap();
    assert!(sources_flat.text.contains("pub fn nullable_column_slice(") && sources_flat.text.contains("pub open spec fn nullable_column(t: int, c: int) -> bool {\n    (t == 1 && (c == 1))\n}"));
    files.push(FrameworkSource { path: format!("{}mod.rs", kept.interface_prefix()), text: KEPT_INTERFACE.replace("flat_ledger", "flat_line").replace("`ledger`", "`line`") });
    files.push(FrameworkSource { path: "builder/mod.rs".into(), text: KEPT_BUILDER.replace("flat_ledger", "flat_line") });
    let derived = verify_only(&toolchain, &with_trusted_shim(files, GENDB_STORAGE_DERIVED_SHIM_SOURCE), STORAGE_CRATE_NAME, &work.join("derived"));
    assert_eq!(derived.outcome, VerusOutcome::Verified, "storage crate over a nullable flat source: {}", derived.rendered_errors());

    // The capture: Arrow columns with NULLs -> canonical columns -> column files (a validity file per nullable column).
    let tables = nullable_tables();
    let archive = work.join("capture");
    let columns = gendb_storage::io::SourceColumns::from_projected(tables.iter().map(|t| t.projected.clone()).collect()).unwrap();
    columns.write_archive(&archive).unwrap();
    columns.write_and_map_column_files(&archive).unwrap();
    let uses = flat_assets_from_capture(&flats, &archive, &work.join("assets"));
    let database: HostTables = tables.iter().map(|t| t.rows.clone()).collect();

    let mut records = vec![];
    for (i, sql) in NULLABLE_SQL.iter().enumerate() {
        let doc = translate_sql(&format!("q{i}"), sql);
        let encoded = encode_binding(&doc, &[]).unwrap();
        let dir = work.join(format!("q{i}"));
        let request = WorkerRequest::for_engine_query(&library, uses.clone(), PartAccess::default(), &[encoded.bytes.clone()], vec![1], 1, RANGE_CAPACITY);
        let result = spawn(&worker, &dir.join("worker"), &request, 3600).unwrap_or_else(|e| panic!("q{i}: {e}"));
        assert_eq!(result.echoes[0], echo_text(&encoded.document), "q{i}: echo");
        let build = with_build_lock(|| {
            build_evaluator(&toolchain, &encoded.document, &dir.join("reference/ast.json"), &dir.join("reference/build"), &BuildOptions::default()).unwrap()
        });
        assert_eq!(build.status, BuildStatus::Ok, "q{i}: reference build {}", build.record);
        let reference = EvaluatorLibrary::load(build.library.as_ref().unwrap()).unwrap().run(&database).unwrap();
        let RunOutcome::Rows(expected) = reference else { panic!("q{i}: the reference answered {reference:?}") };
        let rows = answer_rows(&result, 0).unwrap_or_else(|e| panic!("q{i}: {e}"));
        assert_eq!(rows, expected, "q{i}: the engine's rows differ from the reference evaluator's");
        let nulls = rows.iter().flatten().filter(|v| **v == HostValue::Null).count();
        if i == 0 {
            let expected_nulls: usize = database[0].iter().flatten().filter(|v| **v == HostValue::Null).count() * 3 * 2
                + database[1].iter().flatten().filter(|v| **v == HostValue::Null).count() * 3 * 2;
            assert_eq!((rows.len(), nulls), (18, expected_nulls), "every cell, NULLs included");
        }
        records.push(json!({"sql": sql, "rows": rows.len(), "nulls": nulls, "reference_verification": build.record["run"]["verification"]}));
        eprintln!("q{i}: {} rows ({nulls} NULL values) equal to the reference", rows.len());
    }
    let evidence = json!({"engine_library": library, "engine_origin": origin, "capture": archive, "statements": records,
        "derived_storage_with_sources_flat": {"outcome": derived.outcome, "verification": derived.verification, "wall_ns": derived.wall_ns}});
    std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", work.join("evidence.json").display());
}

/// Empty flat assets of `flats` under `dir` (every table with no row): one parts directory per flat storage, in its
/// part order (a text column's offsets part holds one 0). Returns the storage uses in order.
fn empty_flat_assets(flats: &[FlatStorage], dir: &Path) -> Vec<StorageUseInput> {
    flats
        .iter()
        .map(|flat| {
            let parts_directory = dir.join(flat.name.as_str());
            let mut writer = PartFilesWriter::new(&parts_directory, PartsFormat::LittleEndian).unwrap();
            for part in &flat.parts {
                match part.buffer {
                    FlatBuffer::Offsets => writer.write_part(PartElem::I64, 1, &0i64.to_le_bytes()).unwrap(),
                    FlatBuffer::Values => writer.write_part(flat_part_elem(part.elem), 0, &[]).unwrap(),
                    FlatBuffer::Bytes | FlatBuffer::Validity => writer.write_part(PartElem::U8, 0, &[]).unwrap(),
                }
            }
            writer.finish().unwrap();
            StorageUseInput { name: flat.name.to_string(), parts_directory }
        })
        .collect()
}

/// Stage runs: a goal workload's templates at the timing binding `v0`, prepared as the engine's
/// checks prepare them (`TemplateCheck::prepare`; a template without free parameters as a concrete statement, named by
/// its one visible binding), are encoded (`engine_encode`), and version 0 over the workload's flat storages (compiled
/// once, then cached) decodes each AST in a worker child over empty flat assets and echoes exactly the host's rendering
/// of the bound document. Paths from the environment: `GENDB_STAGE_ENCODE_REQUEST` (a request file with the workload's
/// `dataset` and `integrity_constraints`, read only), `GENDB_STAGE_ENCODE_TEMPLATES` (its `templates.json`) and
/// `GENDB_STAGE_ENCODE_BINDINGS` (its `visible.json`).
#[test]
#[ignore = "runs the frontend, the pinned Verus (once, cached) and the gendb worker on the templates named by GENDB_STAGE_ENCODE_*; set GENDB_WORKER; -- --ignored"]
fn stage_goal_templates_encode_and_echo() {
    let env = |name: &str| PathBuf::from(std::env::var_os(name).unwrap_or_else(|| panic!("{name}")));
    let worker = env("GENDB_WORKER");
    let work = work_dir("stage-encode");
    let toolchain = VerusToolchain::from_env().unwrap();
    let parser = SqlParser::from_environment().unwrap();
    let request: Value = serde_json::from_slice(&std::fs::read(env("GENDB_STAGE_ENCODE_REQUEST")).unwrap()).unwrap();
    let dataset: DatasetSpec = serde_json::from_value(request["dataset"].clone()).unwrap();
    let constraints: IntegrityConstraints = serde_json::from_value(request["integrity_constraints"].clone()).unwrap();
    let templates_file = env("GENDB_STAGE_ENCODE_TEMPLATES");
    let index: Value = serde_json::from_slice(&std::fs::read(&templates_file).unwrap()).unwrap();
    let visible: Value = serde_json::from_slice(&std::fs::read(env("GENDB_STAGE_ENCODE_BINDINGS")).unwrap()).unwrap();
    let validation: ValidationPolicy = serde_json::from_value(json!({"kind":"formal_proofs","numeric_relative_tolerance":"0"})).unwrap();

    let mut checks = vec![];
    for (name, template) in index["templates"].as_object().unwrap() {
        let sql = std::fs::read_to_string(templates_file.parent().unwrap().join(template["sql"].as_str().unwrap())).unwrap();
        let parameters: Vec<ParamRequest> = serde_json::from_value(template["parameters"].clone()).unwrap();
        let bindings: Vec<BenchmarkBinding> = visible_bindings(&visible, name).into_iter().map(|(name, arguments)| BenchmarkBinding { name, arguments }).collect();
        let concrete = parameters.is_empty();
        let prepared_at: &[BenchmarkBinding] = if concrete { &[] } else { &bindings };
        let mut check = TemplateCheck::prepare(&parser, &dataset, Some(&constraints), &validation, name, name, &sql, &parameters, prepared_at, &work.join("statements").join(name))
            .unwrap_or_else(|e| panic!("{name}: {e}"));
        check.bindings = bindings;
        let named = check.statement_binding("v0");
        assert_eq!(named, if concrete { "statement" } else { "v0" }, "{name}: the statement's binding of v0");
        checks.push((name.clone(), concrete, check));
    }
    let schema = checks[0].2.preflight.statement.instance.doc.tables.clone();
    let flats = flat_storages(&schema);
    let (library, origin) = compiled_engine_in(&toolchain, &engine_crate(&schema, &flats, &version_0(&schema, &flats)), &work.join("engine"), "version-0-stage-goal-engine");
    let asts: Vec<EngineAst> = checks.iter().map(|(name, _, check)| check.ast("v0").unwrap_or_else(|e| panic!("{name} at v0: {e}"))).collect();
    let uses = empty_flat_assets(&flats, &work.join("assets"));
    let bytes: Vec<Vec<u8>> = asts.iter().map(|a| a.bytes.clone()).collect();
    let job = WorkerRequest::for_engine_query(&library, uses, PartAccess::default(), &bytes, vec![1], 1, RANGE_CAPACITY);
    let result = spawn(&worker, &work.join("worker"), &job, 3600).unwrap();
    let mut records = vec![];
    for (i, ((name, concrete, _), ast)) in checks.iter().zip(&asts).enumerate() {
        assert_eq!(result.echoes[i], echo_text(&ast.document), "{name}: the engine's echo of the decoded AST differs from the host's rendering");
        let status = result.observations.iter().find(|o| o.binding == Some(i)).map(|o| o.outcome.status);
        records.push(json!({"template": name, "concrete": concrete, "ast_bytes": ast.bytes.len(), "echo_equal": true, "status_on_empty_tables": status}));
        eprintln!("{name}: {} AST bytes, echo equal{}", ast.bytes.len(), if *concrete { " (concrete statement, binding v0 = statement)" } else { "" });
    }
    let evidence = json!({"engine_library": library, "engine_origin": origin, "templates": records});
    std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", work.join("evidence.json").display());
}
