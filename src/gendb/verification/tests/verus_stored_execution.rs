//! The v4 evaluation helpers (`admission::stored_execution`) and the statement check of the preflight through real
//! worker children, on the tiny storage fixture (`fixtures/verus_storage`: interface, builder and query read unchanged):
//! 1. a tiny Parquet dataset (`sensor`, `site`) is prepared like any workload capture; two statements are prepared and
//!    preflighted for real (the v4 statement check crate verified by Verus, one verified evaluator per admission
//!    binding, labelled tiny cases, the DataFusion reference): the fixture query `SELECT id, reading FROM sensor WHERE
//!    day < $1` and `SELECT id FROM sensor WHERE day < $1`, which does not deliver the stored `reading`;
//! 2. the storage crate (roots `stores/sensor_days/interface`, `builder`) and the query crate (root `agent`, interface
//!    copy scanned as author text) are frozen by `verus::freeze_author_crate`. Their compiled libraries are reused from
//!    an earlier run when the frozen sources are byte-equal to it (`GENDB_S4B_REUSE=<dir with storage/ and query/>`,
//!    for example S3's integrated check); otherwise each crate is verified and compiled once;
//! 3. the stored asset over the prepared capture is built once by the storage library; then `check_stored_prepared_data`
//!    (exact, request counters below the stored bytes), `check_stored_parameter_refusals`, `check_stored_tiny_cases`
//!    (every case, and a one-case selection) and `check_storage_tiny_builds` (the second statement's cases fill the
//!    stored `reading` with its synthetic default) run in worker children;
//! 4. control: a use whose stored bytes differ from the mapped asset is refused.
//!
//! Needs the pinned frontend Python, the pinned Verus (`GENDB_VERUS_HOME`, default `<repository>/toolchains`) and the
//! `gendb` executable as the worker (`GENDB_WORKER`); run with `--ignored`.
use arrow::array::{ArrayRef, Date32Array, Decimal128Array, Int32Array, StringArray};
use arrow::datatypes::{DataType, Field, Schema};
use arrow::record_batch::RecordBatch;
use gendb_artifacts::{ColType, ColumnSpec};
use gendb_frontend::parser::SqlParser;
use gendb_frontend::params::ParamRequest;
use gendb_runtime::abi::{GENDB_QUERY_SHIM_V4_SOURCE, GENDB_STORAGE_SHIM_SOURCE};
use gendb_runtime::worker::{TableColumns, WorkerInput, WorkerRequest};
use gendb_storage::import::{prepare_source, ColumnDemand, DataFormat, DatasetSpec, PreparationRequest, SqlReference, TableSpec};
use gendb_storage::io::{PartAccess, ReadAdvice};
use gendb_verification::admission::execution::{CandidateRunner, RANGE_CAPACITY};
use gendb_verification::admission::stored_execution::{
    check_storage_tiny_builds, check_stored_parameter_refusals, check_stored_prepared_data, check_stored_tiny_cases, StorageUseRun, TinyBuilder,
    TinyCaseSelection,
};
use gendb_verification::admission::{prepare_statement, preflight, prepared_references, QueryPreflight, StatementInputs};
use gendb_verification::obligations::{
    query_crate_files, storage_crate_files, with_trusted_shim, DeclaredSource, StorageName, StorageUse, CANDIDATE_CRATE_NAME,
    QUERY_ENTRY_IDENTITY, STORAGE_CRATE_NAME,
};
use gendb_verification::verus::{
    freeze_author_crate, run_verus, AuthorRoot, CodegenOptions, FrameworkSource, FrozenCrate, VerusMode, VerusOptions, VerusOutcome,
    VerusToolchain,
};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::sync::Arc;

const INTERFACE: &str = include_str!("fixtures/verus_storage/interface.rs");
const BUILDER: &str = include_str!("fixtures/verus_storage/builder.rs");
const AGENT: &str = include_str!("fixtures/verus_storage/agent.rs");
const WORKER_COUNTS: [usize; 2] = [1, 2];

fn fixtures() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

fn column(name: &str, ty: ColType, nullable: bool) -> ColumnSpec {
    ColumnSpec { name: name.into(), ty, nullable }
}

/// The fixture dataset (the schema of `verus_storage_library.rs`) over two tiny Parquet files written to `dir`: six
/// sensor rows in blocks of two days (2000-01-01/02, 2001-06-25/26, 2002-11-09/10) and two sites.
fn dataset(dir: &Path) -> DatasetSpec {
    std::fs::create_dir_all(dir).unwrap();
    let write = |path: &Path, fields: Vec<Field>, columns: Vec<ArrayRef>| {
        let batch = RecordBatch::try_new(Arc::new(Schema::new(fields)), columns).unwrap();
        let mut writer = datafusion::parquet::arrow::ArrowWriter::try_new(std::fs::File::create(path).unwrap(), batch.schema(), None).unwrap();
        writer.write(&batch).unwrap();
        writer.close().unwrap();
    };
    let (sensor, site) = (dir.join("sensor.parquet"), dir.join("site.parquet"));
    write(
        &sensor,
        vec![
            Field::new("id", DataType::Int32, false),
            Field::new("site", DataType::Int32, false),
            Field::new("reading", DataType::Decimal128(10, 2), false),
            Field::new("day", DataType::Date32, false),
            Field::new("tag", DataType::Utf8, false),
            Field::new("note", DataType::Utf8, true),
        ],
        vec![
            Arc::new(Int32Array::from(vec![1, 2, 3, 4, 5, 6])),
            Arc::new(Int32Array::from(vec![1, 1, 2, 2, 1, 2])),
            Arc::new(Decimal128Array::from(vec![1234, -5, 700, 1, 2, 3]).with_precision_and_scale(10, 2).unwrap()),
            Arc::new(Date32Array::from(vec![10957, 10958, 11498, 11499, 12000, 12001])),
            Arc::new(StringArray::from(vec!["a", "b", "c", "d", "e", "f"])),
            Arc::new(StringArray::from(vec![Some("n"), None, None, None, None, None])),
        ],
    );
    write(
        &site,
        vec![Field::new("code", DataType::Utf8, false), Field::new("region", DataType::Int32, false)],
        vec![Arc::new(StringArray::from(vec!["x", "y"])), Arc::new(Int32Array::from(vec![7, 8]))],
    );
    let table = |name: &str, fields, location: &Path| TableSpec { name: name.into(), fields, locations: vec![location.to_owned()], format: DataFormat::Parquet };
    DatasetSpec {
        tables: vec![
            table("site", vec![column("code", ColType::Utf8, false), column("region", ColType::I32, false)], &site),
            table("sensor", vec![
                column("id", ColType::I32, false),
                column("site", ColType::I32, false),
                column("reading", ColType::Decimal { p: 10, s: 2 }, false),
                column("day", ColType::Date32, false),
                column("tag", ColType::Utf8, false),
                column("note", ColType::Utf8, true),
            ], &sensor),
        ],
    }
}

fn source(path: &str, text: &str) -> FrameworkSource {
    FrameworkSource { path: path.into(), text: text.into() }
}

/// A workspace author directory holding one `mod.rs`.
fn author_root(dir: &Path, text: &str) -> PathBuf {
    std::fs::create_dir_all(dir).unwrap();
    std::fs::write(dir.join("mod.rs"), text).unwrap();
    dir.to_owned()
}

/// Every file under `<root>/src`, relative to it.
fn source_tree(root: &Path) -> BTreeMap<String, Vec<u8>> {
    fn walk(dir: &Path, prefix: &str, out: &mut BTreeMap<String, Vec<u8>>) {
        for entry in std::fs::read_dir(dir).unwrap() {
            let entry = entry.unwrap();
            let name = format!("{prefix}{}", entry.file_name().to_string_lossy());
            if entry.file_type().unwrap().is_dir() {
                walk(&entry.path(), &format!("{name}/"), out);
            } else {
                out.insert(name, std::fs::read(entry.path()).unwrap());
            }
        }
    }
    let mut out = BTreeMap::new();
    walk(&root.join("src"), "", &mut out);
    out
}

/// The compiled library of `frozen`: reused from `<reuse>/<name>` when that run compiled byte-equal sources, else one
/// whole-crate verify+compile in `work`. Returns the library and how it was obtained.
fn compiled_library(toolchain: &VerusToolchain, frozen: &FrozenCrate, name: &str, crate_name: &str, reuse: Option<&Path>, work: &Path) -> (PathBuf, Value) {
    if let Some(reuse) = reuse {
        let run: Value = serde_json::from_slice(&std::fs::read(reuse.join(name).join("run.json")).unwrap()).unwrap();
        let equal = source_tree(&reuse.join(name).join("frozen")) == source_tree(&frozen.root);
        if equal && run["outcome"] == "compiled" {
            let library = PathBuf::from(run["artifact"].as_str().unwrap());
            assert!(library.is_file(), "{}", library.display());
            return (library, json!({"reused_from": reuse.join(name), "verification": run["verification"]}));
        }
        eprintln!("{name}: sources differ from {} (or not compiled); verifying again", reuse.display());
    }
    let options = VerusOptions { crate_name: crate_name.into(), codegen: CodegenOptions { opt_level: 1, target_cpu: None }, num_threads: Some(8) };
    let run = run_verus(toolchain, frozen, &options, VerusMode::VerifyAndCompile, &work.join(format!("{name}-verus-build"))).unwrap();
    assert_eq!(run.outcome, VerusOutcome::Compiled, "{name}: {}", run.rendered_errors());
    (run.artifact.clone().unwrap(), json!({"verified_here": true, "verification": run.verification}))
}

#[test]
#[ignore = "runs the pinned Verus toolchain, frontend, DataFusion and the gendb worker; set GENDB_WORKER; -- --ignored"]
fn stored_execution_checks_run_through_worker_children() {
    let worker = PathBuf::from(std::env::var_os("GENDB_WORKER").expect("GENDB_WORKER: the gendb executable"));
    let reuse = std::env::var_os("GENDB_S4B_REUSE").map(PathBuf::from);
    let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let work = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("verus-stored-execution-{}-{nanos}", std::process::id()));
    let toolchain = VerusToolchain::from_env().unwrap();
    let parser = SqlParser::from_environment().unwrap();
    let runtime = tokio::runtime::Runtime::new().unwrap();
    let dataset = dataset(&work.join("data"));

    // 1. Two statements, one prepared capture, real preflights.
    let requests: Vec<ParamRequest> = serde_json::from_str(&std::fs::read_to_string(fixtures().join("verus_storage/params.json")).unwrap()).unwrap();
    let fixture_sql = std::fs::read_to_string(fixtures().join("verus_storage/query.sql")).unwrap();
    let sqls = [fixture_sql.as_str(), "SELECT id\nFROM sensor\nWHERE day < $1;\n"];
    let statements: Vec<_> = sqls
        .iter()
        .enumerate()
        .map(|(i, sql)| prepare_statement(&parser, &dataset, None, sql, &requests, &[], &[], &work.join(format!("query-{i}/verus-preflight"))).unwrap_or_else(|r| panic!("{}", r.error)))
        .collect();
    let mut demand = ColumnDemand::default();
    for statement in &statements {
        demand.add_declaration(&dataset, &statement.source).unwrap();
    }
    let request = PreparationRequest { dataset: &dataset, demand: &demand, base: None, registry: &work.join("registry"), root: &work.join("prepared") };
    let (prepared, _) = prepare_source(&request).unwrap();
    let prepared = Arc::new(prepared);
    let reference = SqlReference::new(prepared.clone()).unwrap();
    let mut preflights: Vec<(QueryPreflight, StatementInputs)> = vec![];
    for (i, statement) in statements.into_iter().enumerate() {
        let inputs = StatementInputs::project(&statement, prepared.clone(), &work.join(format!("query-{i}"))).unwrap();
        let checked = runtime.block_on(preflight(statement, &inputs, &reference, &parser, &WORKER_COUNTS, Default::default())).unwrap_or_else(|r| panic!("preflight {i}: {} {}", r.error, r.detail));
        assert_eq!(checked.framework_check["outcome"], "verified", "{}", checked.framework_check);
        assert_eq!(checked.framework_check["entry_identity"], QUERY_ENTRY_IDENTITY);
        preflights.push((checked, inputs));
    }
    let (query, query_inputs) = &preflights[0];
    let statement = &query.statement;
    let references = runtime.block_on(prepared_references(query, &reference));

    // 2. Both crates frozen with their author roots; compiled libraries.
    let doc = &statement.instance.doc;
    let name = StorageName::new("sensor_days").unwrap();
    let declaration = DeclaredSource::for_storage(&doc.tables, &BTreeMap::from([(1, BTreeSet::from([0, 2, 3]))])).unwrap();
    let storage_files = with_trusted_shim(storage_crate_files(&doc.tables, &name, &declaration, false).unwrap(), GENDB_STORAGE_SHIM_SOURCE);
    let workspace = work.join("workspace");
    let (interface_dir, builder_dir, agent_dir) =
        (author_root(&workspace.join("interface"), INTERFACE), author_root(&workspace.join("builder"), BUILDER), author_root(&workspace.join("agent"), AGENT));
    let storage_roots = [
        AuthorRoot { crate_directory: "stores/sensor_days/interface", source: &interface_dir },
        AuthorRoot { crate_directory: "builder", source: &builder_dir },
    ];
    let storage_frozen = freeze_author_crate(&storage_files, &storage_roots, &work.join("storage/frozen")).unwrap();
    assert_eq!(storage_frozen.author_files, ["builder/mod.rs", "stores/sensor_days/interface/mod.rs"]);
    let interface = vec![source("stores/sensor_days/interface/mod.rs", INTERFACE)];
    let uses = [StorageUse { name: &name, declaration: &declaration, interface: &interface }];
    let query_files = with_trusted_shim(query_crate_files(&statement.instance, &statement.source, &uses, &statement.identity()).unwrap(), GENDB_QUERY_SHIM_V4_SOURCE);
    let query_frozen = freeze_author_crate(&query_files, &[AuthorRoot { crate_directory: "agent", source: &agent_dir }], &work.join("query/frozen")).unwrap();
    let (storage_library, storage_origin) = compiled_library(&toolchain, &storage_frozen, "storage", STORAGE_CRATE_NAME, reuse.as_deref(), &work);
    let (query_library, query_origin) = compiled_library(&toolchain, &query_frozen, "query", CANDIDATE_CRATE_NAME, reuse.as_deref(), &work);

    // 3. The stored asset over the prepared capture (built once), then the four checks.
    let runner = CandidateRunner { worker };
    let prepared_parts = work.join("asset/parts");
    let input = WorkerInput::Tables { path: query_inputs.archive.clone(), tables: vec![TableColumns { table: "sensor".into(), ordinals: vec![0, 2, 3] }] };
    let built = runner.run(&work.join("asset/build"), &WorkerRequest::for_storage_build(&storage_library, input, &prepared_parts, 1, RANGE_CAPACITY), None).unwrap();
    let stored_bytes = built.parts.as_ref().expect("the asset build returned parts").storage_bytes;
    let builder = TinyBuilder::Columns { library: storage_library.clone() };
    let run = |stored_bytes| StorageUseRun { name: &name, declaration: &declaration, builder: &builder, prepared_parts: &prepared_parts, stored_bytes, assumes_declared_constraints: false };
    let uses = [run(stored_bytes)];
    let access = PartAccess { read_advice: ReadAdvice::Random, drop_cached_pages: false };
    let all_bindings: Vec<usize> = (0..statement.bindings.len()).collect();
    let prepared_data =
        check_stored_prepared_data(&runner, query, &references, &query_library, &uses, access, &work.join("checks/prepared"), &all_bindings, &WORKER_COUNTS, 2, None)
            .unwrap();
    assert_eq!(prepared_data["status"], "exact", "{prepared_data}");
    for cell in prepared_data["cells"].as_array().unwrap() {
        let requests = &cell["storage_requests"][0];
        assert_eq!((requests["name"].as_str(), requests["stored_bytes"].as_u64()), (Some("sensor_days"), Some(stored_bytes)), "{cell}");
        assert!(requests["bytes"].as_u64().unwrap() <= stored_bytes, "{cell}");
        assert!(cell["process_io"]["read_bytes_per_call"].as_array().unwrap().len() == 2, "{cell}");
    }
    let refusals = check_stored_parameter_refusals(&runner, query, &query_library, &uses, &work.join("checks/refusals")).unwrap();
    assert_eq!(refusals["status"], "refused_as_declared", "{refusals}");
    let every = TinyCaseSelection::every(query, &WORKER_COUNTS);
    let cases = check_stored_tiny_cases(&runner, query, &query_library, &uses, &work.join("checks/cases"), &every).unwrap();
    assert_eq!((cases["status"].as_str(), cases["cases"].as_array().unwrap().len()), (Some("allowed"), query.cases.len()));
    assert!(cases["exact_comparisons"].as_u64().unwrap() > 0, "{cases}");
    for case in cases["cases"].as_array().unwrap() {
        let tiny_bytes = &case["storages"][0]["parts"]["storage_bytes"];
        for verdict in case["verdicts"].as_array().unwrap().iter().filter(|v| v["storage_requests"].is_array()) {
            for requests in verdict["storage_requests"].as_array().unwrap() {
                assert_eq!(&requests["stored_bytes"], tiny_bytes, "a tiny verdict reports its tiny asset's bytes: {case}");
            }
        }
    }
    let one = TinyCaseSelection { cases: vec![query.cases.len() - 1], bindings: vec![0], workers: vec![2] };
    let one_case = check_stored_tiny_cases(&runner, query, &query_library, &uses, &work.join("checks/one-case"), &one).unwrap();
    let one_case_records = one_case["cases"].as_array().unwrap();
    assert_eq!((one_case_records.len(), one_case_records[0]["verdicts"].as_array().unwrap().len()), (1, 1), "{one_case}");
    let statement_refs: Vec<&QueryPreflight> = preflights.iter().map(|(p, _)| p).collect();
    let builds = check_storage_tiny_builds(&runner, &storage_library, &declaration, false, &statement_refs, &work.join("checks/storage-builds"), 1).unwrap();
    let records = builds["builds"].as_array().unwrap();
    assert_eq!(records.len(), preflights.iter().map(|(p, _)| p.cases.len()).sum::<usize>(), "{builds}");
    let synthetic = |key: &str| records.iter().filter(|b| b["statement_key"] == key).all(|b| b["input"]["synthetic_columns"] == json!(["sensor.reading"]));
    assert!(synthetic(&preflights[1].0.statement.key_v4_id), "the second statement does not deliver reading: {builds}");
    assert!(records.iter().filter(|b| b["statement_key"] == statement.key_v4_id).all(|b| b["input"]["synthetic_columns"] == json!([])));

    // 4. Control: the mapped asset must be the resolved asset.
    let wrong = [run(stored_bytes + 1)];
    let refused = check_stored_prepared_data(&runner, query, &references, &query_library, &wrong, access, &work.join("checks/wrong-asset"), &[0], &[1], 1, None).unwrap_err();
    assert!(refused.message.contains("not the resolved assets") && refused.class.name() == "tool_failure", "{refused}");

    let evidence = json!({"work": work, "statement_check": query.framework_check, "second_statement_check": preflights[1].0.framework_check["outcome"],
        "storage_library": storage_library, "storage_origin": storage_origin, "query_library": query_library, "query_origin": query_origin,
        "asset": built.parts, "prepared_data": prepared_data, "parameter_refusals": refusals,
        "tiny_cases": {"cases": cases["cases"].as_array().unwrap().len(), "exact_comparisons": cases["exact_comparisons"], "status_only": cases["status_only_observations"], "first": cases["cases"][0]},
        "one_case_selection": one_case["selection"], "storage_tiny_builds": {"builds": records.len(), "statements": builds["statements"], "first_synthetic": records.iter().find(|b| b["input"]["synthetic_columns"] != json!([]))},
        "wrong_asset_refusal": refused.to_string()});
    std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", work.join("evidence.json").display());
}
