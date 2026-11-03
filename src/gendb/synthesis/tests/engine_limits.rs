//! The per-call limits and the profile sampler of engine jobs on version 0 of the general engine, through real worker children over tiny TPC-H data.
//!
//! - **Engine**: version 0 (`obligations::interpreter_engine`: every table materialized from its flat storage, then the
//!   verified interpreter), assembled over the eight generated flat TPC-H storages (the SF100 dataset's column types,
//!   the 15 declared constraints) and verified and compiled whole with `--no-cheating` here (cached under the work
//!   directory by exact sources), unless `GENDB_ENGINE_LIBRARY` names an already compiled engine over the same eight
//!   storages in table order.
//! - **Data**: Q01's tiny FK-closed database (`tpch_all22_cases/q01.json`) with lineitem grown to [`LINEITEM_ROWS`]
//!   rows by copies of its first row under new line numbers (the primary key and every foreign key still hold), written
//!   as flat assets.
//! - **Statements**: a fast one (`count(*)` over region) and the self-product `lineitem x lineitem x lineitem`, which the
//!   interpreter materializes ([`LINEITEM_ROWS`] cubed rows: seconds of CPU and gigabytes if run to the end).
//!
//! [`limits_stop_calls_and_keep_earlier_observations`]: one engine job, the fast statement twice then
//! the self-product, with a 1 s call limit: the result is `unfinished(over_time_limit)` naming the self-product's first
//! call, stopped within the limit plus 3 s, with the fast statement's two observations kept; the same job with a
//! 256 MiB memory limit (and a 30 s call limit) is `unfinished(over_memory_limit)`.
//! [`profile_of_v0_names_interpreter_functions`]: profile jobs (`engine::profile`) of the self-product
//! stopped at a 2 s limit and of the finishing two-way product: symbolized functions of the interpreter
//! (`exec::relational::...`) with sample counts.
//!
//! Needs the pinned Verus (unless `GENDB_ENGINE_LIBRARY`) and frontend, and `GENDB_WORKER`: an executable of this build
//! that serves `<exe> worker REQUEST RESULT` (`gendb`, or the runtime's `worker_process` test executable). Work goes
//! under `GENDB_ENGINE_TEST_WORK` (default `TMPDIR`); with `GENDB_BUILD_LOCK`, the Verus run holds that lock.
//! Framework tests only: they say nothing about engine speed.

use gendb_frontend::ast::{TableDef, Translation};
use gendb_frontend::engine_encode::encode_binding;
use gendb_frontend::parser::SqlParser;
use gendb_runtime::abi::GENDB_ENGINE_SHIM_SOURCE;
use gendb_runtime::worker::{CallLimits, StorageUseInput, Unfinished, UnfinishedReason, WorkerRequest, spawn};
use gendb_sqlspec::codec::{HostTables, HostValue};
use gendb_sqlspec::fixtures::{Fixture, fixtures_dir};
use gendb_storage::import::DatasetSpec;
use gendb_storage::io::{PartAccess, PartElem, PartFilesWriter, PartsFormat};
use gendb_synthesis::engine::profile::{ProfileSubject, profile_statement, render_profile_md};
use gendb_synthesis::engine::timing::EngineStatement;
use gendb_verification::admission::execution::CandidateRunner;
use gendb_verification::admission::{IntegrityConstraints, dataset_ddl};
use gendb_verification::obligations::{
    FlatBuffer, FlatElem, FlatStorage, StorageUse, engine_crate_files, flat_storage, interpreter_engine, with_trusted_shim, ENGINE_CRATE_NAME,
};
use gendb_verification::verus::{CodegenOptions, FrameworkSource, VerusMode, VerusOptions, VerusOutcome, VerusToolchain, freeze_framework_crate, run_verus};
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

/// Rows of the grown lineitem table: the three-way self-product has `LINEITEM_ROWS`^3 rows.
const LINEITEM_ROWS: usize = 200;
const RANGE_CAPACITY: u64 = 64;
const FAST_SQL: &str = "SELECT count(*) AS n FROM region";
const SELF_PRODUCT_SQL: &str = "SELECT count(*) AS n FROM lineitem a, lineitem b, lineitem c";
const PAIR_PRODUCT_SQL: &str = "SELECT count(*) AS n FROM lineitem a, lineitem b";

/// The SF100 dataset's tables and column types (the completed SF100 runs' request), all NOT NULL.
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

fn repository() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).ancestors().nth(3).expect("<repository>/src/gendb/synthesis").to_path_buf()
}

fn base_dir() -> PathBuf {
    std::env::var_os("GENDB_ENGINE_TEST_WORK").or_else(|| std::env::var_os("TMPDIR")).map(PathBuf::from).expect("GENDB_ENGINE_TEST_WORK or TMPDIR")
}

fn fresh_dir(name: &str) -> PathBuf {
    let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = base_dir().join(format!("engine-limits-{name}-{}-{nanos}", std::process::id()));
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

/// Everything both tests run over.
struct Setup {
    work: PathBuf,
    worker: PathBuf,
    library: PathBuf,
    library_origin: Value,
    uses: Vec<StorageUseInput>,
    fast: Vec<u8>,
    self_product: Vec<u8>,
    pair_product: Vec<u8>,
}

fn setup(name: &str) -> Setup {
    let worker = PathBuf::from(std::env::var_os("GENDB_WORKER").expect("GENDB_WORKER: an executable of this build serving `worker`"));
    let work = fresh_dir(name);
    let parser = SqlParser::from_environment().unwrap();

    // The schema (the SF100 dataset DDL with the declared constraints).
    let dataset: DatasetSpec = serde_json::from_str(TPCH_DATASET).unwrap();
    let constraints: IntegrityConstraints =
        serde_json::from_str(&std::fs::read_to_string(repository().join("src/gendb/fixtures/tpch/integrity-constraints.json")).unwrap()).unwrap();
    let (ddl, omitted) = dataset_ddl(&dataset, Some(&constraints));
    assert!(omitted.is_empty(), "{omitted:?}");
    let ddl_path = work.join("tpch.sql");
    std::fs::write(&ddl_path, ddl).unwrap();
    let encode = |label: &str, sql: &str| {
        let path = work.join(format!("{label}.sql"));
        std::fs::write(&path, sql).unwrap();
        let (_, translation) = parser.translate(&ddl_path, &path, "postgres", &[]).unwrap();
        let Translation::Ok(doc) = translation else { panic!("{label}: refused: {translation:?}") };
        (doc.tables.clone(), encode_binding(&doc, &[]).unwrap().bytes)
    };
    let (schema, fast) = encode("fast", FAST_SQL);
    let (_, self_product) = encode("self-product", SELF_PRODUCT_SQL);
    let (_, pair_product) = encode("pair-product", PAIR_PRODUCT_SQL);
    let flats: Vec<FlatStorage> = (0..schema.len()).map(|t| flat_storage(&schema, t).unwrap()).collect();

    // The engine: version 0 over the eight flat storages (or the given compiled engine).
    let (library, library_origin) = match std::env::var_os("GENDB_ENGINE_LIBRARY") {
        Some(path) => (PathBuf::from(&path), json!({"given": path.to_string_lossy()})),
        None => version_zero(&schema, &flats),
    };

    // The tiny database: Q01's, lineitem grown to LINEITEM_ROWS rows; written as flat assets.
    let case = Fixture::load(&fixtures_dir().join("pg_reference/tpch_all22_cases/q01.json")).unwrap();
    let probe_path = work.join("probe.sql");
    std::fs::write(&probe_path, "SELECT r_regionkey FROM region").unwrap();
    let Translation::Ok(probe) = parser.translate(&ddl_path, &probe_path, "postgres", &[]).unwrap().1 else { panic!("schema probe refused") };
    let mut tables = case.database_for(&probe).unwrap();
    grow_lineitem(&schema, &mut tables, LINEITEM_ROWS);
    let uses = flat_assets(&flats, &tables, &work.join("assets"));
    Setup { work, worker, library, library_origin, uses, fast, self_product, pair_product }
}

/// Version 0 compiled: assembled with a fresh generation of the engine crate, verified and compiled whole
/// (`--no-cheating`), reused from `<base>/engine-limits-cache` when an earlier run compiled byte-equal sources.
fn version_zero(schema: &[TableDef], flats: &[FlatStorage]) -> (PathBuf, Value) {
    let interfaces: Vec<Vec<FrameworkSource>> =
        flats.iter().map(|f| f.files.iter().filter(|x| x.path.starts_with(&f.name.interface_prefix())).cloned().collect()).collect();
    let uses: Vec<StorageUse<'_>> =
        flats.iter().zip(&interfaces).map(|(f, interface)| StorageUse { name: &f.name, declaration: &f.declaration, interface }).collect();
    let mut files = engine_crate_files(schema, &uses, "general engine v0 (G2 limits test)").unwrap();
    files.extend(interpreter_engine(schema, &uses).unwrap());
    let files = with_trusted_shim(files, GENDB_ENGINE_SHIM_SOURCE);
    let key = serde_json::to_string(&files.iter().map(|f| (&f.path, &f.text)).collect::<BTreeMap<_, _>>()).unwrap();
    let cache = base_dir().join("engine-limits-cache");
    if std::fs::read_to_string(cache.join("sources.json")).ok().as_deref() == Some(key.as_str()) {
        let record: Value = serde_json::from_str(&std::fs::read_to_string(cache.join("run.json")).unwrap()).unwrap();
        let library = cache.join(format!("lib{ENGINE_CRATE_NAME}.so"));
        if library.is_file() {
            return (library, json!({"reused_from": cache, "verification": record["verification"]}));
        }
    }
    let dir = fresh_dir("v0-build");
    let unscanned: Vec<&str> = files.iter().filter(|f| gendb_registry::author_definition(&f.path).is_none()).map(|f| f.path.as_str()).collect();
    let frozen = freeze_framework_crate(&files, &unscanned, &dir.join("frozen")).unwrap();
    let toolchain = VerusToolchain::from_env().unwrap();
    let options = VerusOptions { crate_name: ENGINE_CRATE_NAME.into(), codegen: CodegenOptions { opt_level: 1, target_cpu: None }, num_threads: Some(16) };
    let run = with_build_lock(|| run_verus(&toolchain, &frozen, &options, VerusMode::VerifyAndCompile, &dir.join("verus")).unwrap());
    assert_eq!(run.outcome, VerusOutcome::Compiled, "version 0: {} {}", run.detail, run.rendered_errors());
    let _ = std::fs::remove_dir_all(&cache);
    std::fs::create_dir_all(&cache).unwrap();
    let library = cache.join(format!("lib{ENGINE_CRATE_NAME}.so"));
    std::fs::copy(run.artifact.as_ref().unwrap(), &library).unwrap();
    std::fs::write(cache.join("sources.json"), key).unwrap();
    let record = json!({"verification": run.verification, "wall_ns": run.wall_ns, "frozen": frozen.root});
    std::fs::write(cache.join("run.json"), serde_json::to_vec_pretty(&record).unwrap()).unwrap();
    (library, json!({"verified_here": true, "verification": run.verification, "wall_ns": run.wall_ns}))
}

/// Grow lineitem to `rows` rows with copies of its first row under new line numbers (the primary key
/// (l_orderkey, l_linenumber) stays unique; every foreign key of the copies is the first row's).
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

/// Write the flat assets of `tables` under `dir` (one parts directory per table, in the flat storage's part order);
/// the storage uses in the engine crate's use order.
fn flat_assets(flats: &[FlatStorage], tables: &HostTables, dir: &Path) -> Vec<StorageUseInput> {
    flats
        .iter()
        .map(|flat| {
            let table_id = flat.declaration.tables[0].table_id;
            let parts_directory = dir.join(flat.name.as_str());
            let mut writer = PartFilesWriter::new(&parts_directory, PartsFormat::LittleEndian).unwrap();
            for part in &flat.parts {
                let k = flat.declaration.tables[0].columns.iter().position(|c| c.ordinal == part.ordinal).unwrap();
                let column: Vec<&HostValue> = tables[table_id].iter().map(|r| &r[k]).collect();
                let (elem, len, bytes) = part_bytes(part.buffer, part.elem, &column);
                writer.write_part(elem, len, &bytes).unwrap();
            }
            writer.finish().unwrap();
            StorageUseInput { name: flat.name.to_string(), parts_directory }
        })
        .collect()
}

/// The element type, element count and little-endian bytes of one flat part of `column`.
fn part_bytes(buffer: FlatBuffer, elem: FlatElem, column: &[&HostValue]) -> (PartElem, usize, Vec<u8>) {
    let mut bytes = vec![];
    match (buffer, elem) {
        (FlatBuffer::Values, FlatElem::I64) => column.iter().for_each(|v| match v {
            HostValue::Int(x) => bytes.extend(x.to_le_bytes()),
            other => panic!("{other:?} in an i64 part"),
        }),
        (FlatBuffer::Values, FlatElem::I128) => column.iter().for_each(|v| match v {
            HostValue::Num { coeff, .. } => bytes.extend(coeff.to_le_bytes()),
            other => panic!("{other:?} in an i128 part"),
        }),
        (FlatBuffer::Values, FlatElem::I32) => column.iter().for_each(|v| match v {
            HostValue::Date(d) => bytes.extend((d + 10957).to_le_bytes()),
            other => panic!("{other:?} in an i32 part"),
        }),
        (FlatBuffer::Offsets, _) => {
            let mut end = 0i64;
            bytes.extend(end.to_le_bytes());
            for v in column {
                let HostValue::Text(t) = v else { panic!("{v:?} in a text column") };
                end += t.len() as i64;
                bytes.extend(end.to_le_bytes());
            }
            return (PartElem::I64, column.len() + 1, bytes);
        }
        (FlatBuffer::Bytes, _) => {
            for v in column {
                let HostValue::Text(t) = v else { panic!("{v:?} in a text column") };
                bytes.extend(t);
            }
            return (PartElem::U8, bytes.len(), bytes);
        }
        other => panic!("no flat part {other:?}"),
    }
    let elem = match elem {
        FlatElem::I32 => PartElem::I32,
        FlatElem::I64 => PartElem::I64,
        FlatElem::I128 => PartElem::I128,
        FlatElem::U8 => PartElem::U8,
    };
    (elem, column.len(), bytes)
}

fn load_average() -> String {
    std::fs::read_to_string("/proc/loadavg").unwrap_or_default().trim().to_string()
}

#[test]
#[ignore = "runs the pinned Verus (v0, once, cached) and frontend and a worker of this build; set GENDB_WORKER; -- --ignored"]
fn limits_stop_calls_and_keep_earlier_observations() {
    let s = setup("limits");
    let job = |limits: CallLimits| {
        WorkerRequest::for_engine_query(&s.library, s.uses.clone(), PartAccess::default(), &[s.fast.clone(), s.self_product.clone()], vec![1], 2, RANGE_CAPACITY)
            .with_call_limits(limits)
    };

    // The time limit: 1 s per call (memory limit 16 GiB as a host safety bound).
    let time_limit = CallLimits { call_limit_ns: 1_000_000_000, anon_memory_limit_bytes: 16 << 30 };
    let load_before = load_average();
    let started = Instant::now();
    let result = spawn(&s.worker, &s.work.join("time-limit"), &job(time_limit), 600).unwrap();
    let child_wall = started.elapsed();
    let Some(Unfinished::OverTimeLimit(stopped)) = &result.unfinished else { panic!("expected over_time_limit: {:?}", result.unfinished) };
    assert_eq!((stopped.statement, stopped.workers, stopped.repetition), (1, 1, 0), "the self-product's first call");
    assert!(stopped.elapsed_ns >= time_limit.call_limit_ns && stopped.elapsed_ns <= time_limit.call_limit_ns + 3_000_000_000, "{stopped:?}");
    assert_eq!(result.observations.len(), 2, "the fast statement's two calls are kept");
    assert!(result.observations.iter().all(|o| o.binding == Some(0) && o.rows.is_some()), "{:?}", result.observations);
    let earlier_ns: u64 = result.observations.iter().map(|o| o.outcome.usage.wall_ns).sum();
    assert_eq!(result.echoes.len(), 2, "the echoes of both statements are kept");
    assert!(child_wall <= Duration::from_nanos(time_limit.call_limit_ns + 3_000_000_000 + earlier_ns) + Duration::from_secs(2),
        "the child ended within the limit plus 3 s (plus the earlier calls and the child's start): {child_wall:?}");

    // The memory limit: 256 MiB of anonymous memory (call limit 30 s).
    let memory_limit = CallLimits { call_limit_ns: 30_000_000_000, anon_memory_limit_bytes: 256 << 20 };
    let started = Instant::now();
    let memory = spawn(&s.worker, &s.work.join("memory-limit"), &job(memory_limit), 600).unwrap();
    let memory_wall = started.elapsed();
    let Some(Unfinished::OverMemoryLimit(over)) = &memory.unfinished else { panic!("expected over_memory_limit: {:?}", memory.unfinished) };
    assert_eq!((over.statement, over.repetition, over.limit), (1, 0, memory_limit.anon_memory_limit_bytes));
    assert!(over.anon_bytes.is_some_and(|b| b > memory_limit.anon_memory_limit_bytes), "{over:?}");
    assert_eq!(memory.observations.len(), 2);
    assert_eq!(memory.unfinished.as_ref().map(Unfinished::reason), Some(UnfinishedReason::OverMemoryLimit));

    let evidence = json!({"engine": s.library, "engine_origin": s.library_origin, "lineitem_rows": LINEITEM_ROWS,
        "load_average_before": load_before, "load_average_after": load_average(),
        "time_limit": {"limits": time_limit, "unfinished": result.unfinished, "kept_observations": result.observations.len(),
            "child_wall_ns": child_wall.as_nanos() as u64, "earlier_calls_wall_ns": earlier_ns, "evidence": s.work.join("time-limit")},
        "memory_limit": {"limits": memory_limit, "unfinished": memory.unfinished, "kept_observations": memory.observations.len(),
            "child_wall_ns": memory_wall.as_nanos() as u64, "evidence": s.work.join("memory-limit")}});
    std::fs::write(s.work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", s.work.join("evidence.json").display());
}

#[test]
#[ignore = "runs the pinned Verus (v0, once, cached) and frontend and a worker of this build; set GENDB_WORKER; -- --ignored"]
fn profile_of_v0_names_interpreter_functions() {
    let s = setup("profile");
    let runner = CandidateRunner { worker: s.worker.clone() };
    let statement = |template: &str, ast: &[u8]| EngineStatement { template: template.into(), variant: None, binding: "adhoc".into(), ast: ast.to_vec() };
    let subject = |call_limit_ns| ProfileSubject {
        runner: &runner,
        library: &s.library,
        uses: &s.uses,
        access: PartAccess::default(),
        limits: CallLimits { call_limit_ns, anon_memory_limit_bytes: 16 << 30 },
    };
    let load_before = load_average();

    // The self-product, stopped at a 2 s limit: profiled up to the stop.
    let stopped = profile_statement(&subject(2_000_000_000), &statement("self_product", &s.self_product), 1, &s.work.join("self-product")).unwrap();
    let stop = stopped.stopped.as_ref().expect("the self-product does not finish in 2 s");
    assert_eq!((stop.reason, stop.repetition), (UnfinishedReason::OverTimeLimit, Some(0)));
    assert_eq!(stopped.sampled_call, Some(0));
    assert!(stopped.samples_taken > 50, "{} samples", stopped.samples_taken);
    let interpreter: u64 = stopped.functions.iter().filter(|f| f.function.contains("exec::relational::")).map(|f| f.self_samples).sum();
    assert!(interpreter > 0, "the interpreter's functions are named: {:?}", &stopped.functions[..stopped.functions.len().min(20)]);
    assert!(stopped.functions.iter().all(|f| !f.function.contains(&format!("{ENGINE_CRATE_NAME}::"))), "engine names are module paths");
    assert!(stopped.functions.iter().any(|f| f.object == format!("lib{ENGINE_CRATE_NAME}.so") && f.self_samples > 0));

    // The two-way product finishes: warm and measured calls, the measured call's samples.
    let finished = profile_statement(&subject(60_000_000_000), &statement("pair_product", &s.pair_product), 1, &s.work.join("pair-product")).unwrap();
    assert!(finished.stopped.is_none(), "{:?}", finished.stopped);
    assert_eq!((finished.calls.len(), finished.sampled_call), (2, Some(1)));
    assert!(finished.calls.iter().all(|c| c.peak_anon_bytes.is_some()), "the watchdog's sampled peak is recorded");

    let md = render_profile_md("version 0 (G2 profile test)", &[stopped.clone(), finished.clone()]);
    std::fs::write(s.work.join("PROFILE.md"), &md).unwrap();
    let evidence = json!({"engine": s.library, "engine_origin": s.library_origin, "lineitem_rows": LINEITEM_ROWS,
        "load_average_before": load_before, "load_average_after": load_average(),
        "self_product": stopped, "pair_product": finished, "interpreter_self_samples": interpreter});
    std::fs::write(s.work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("{md}\nevidence: {}", s.work.join("evidence.json").display());
}
