//! The derived-storage route of the general engine line, end to end on tiny TPC-H data.
//!
//! On the general line every storage file and engine file must pass the schema-name rule (no table or column name).
//! A storage built from a flat storage reads it through the generated `crate::sources_flat` (by table and column id);
//! to keep the flat parts (`extends`) it restates them with the plain-columns vocabulary (`obligations::plain_columns`,
//! copied unchanged into its interface), which `crate::sources_flat::lemma_flat_plain` proves of the flat parts.
//!
//! [`general_line_storages_build_admit_and_serve_an_engine`] (pinned Verus and frontend, and `GENDB_WORKER`, an
//! executable of this build that serves `<exe> worker REQUEST RESULT`):
//! 1. the eight flat TPC-H storages are verified, published, built over each template's tiny database and admitted
//!    through the normal storage path (`admission::storage`);
//! 2. two storages built from flat storages, each chosen by table id and column ordinal and naming no table or column:
//!    `recoded` (fixture `general_storage/recoded_*`: one numeric column re-encoded as 64-bit coefficients, its own part;
//!    the copy route) and `zoned` (`general_storage/zoned_*`: the flat parts of one table kept, `extends`, restated with
//!    the plain-columns vocabulary, plus a zone part). Each passes the general line's storage scan
//!    (`EngineRuleSet::scan_storage_source` over the TPC-H names and template constants), verifies whole with
//!    `--no-cheating`, is published, built in a worker child from the flat assets of every capture, and admitted;
//! 3. an engine that reads both (`general_storage/engine_agent.rs`: version 0 with one column of each table replaced by
//!    the values read from the derived storages) passes the general line's agent scan, is assembled by the normal
//!    generation from the library (`admission::engine::engine_framework_files`) and verifies whole; on each template's
//!    tiny database (`tpch_all22_cases/qNN.json`) its worker-child answer at binding v0 equals the verified reference
//!    evaluator's;
//! 4. controls: the same builder naming its flat source (`crate::stores::flat_<table>`), and an interface naming a
//!    column, are refused by the general line's storage scan.
//!
//! Work goes under `GENDB_ENGINE_TEST_WORK` (default the Cargo target's tmp directory); verified builds are cached there
//! by exact sources. With `GENDB_BUILD_LOCK`, every Verus run holds that lock.
use gendb_artifacts::verus::VerusStorageUseV1;
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_frontend::ast::{AstDocument, TableDef, Translation};
use gendb_frontend::columns::declared_columns;
use gendb_frontend::engine_encode::encode_binding;
use gendb_frontend::params::ParamRequest;
use gendb_frontend::parser::SqlParser;
use gendb_runtime::abi::GENDB_STORAGE_SHIM_SOURCE;
use gendb_runtime::answer::QueryAnswer;
use gendb_runtime::worker::{spawn, StorageUseInput, WorkerInput, WorkerRequest};
use gendb_sqlspec::codec::{HostTables, RunOutcome};
use gendb_sqlspec::evaluator::EvaluatorLibrary;
use gendb_sqlspec::fixtures::{fixtures_dir, Fixture};
use gendb_storage::import::DatasetSpec;
use gendb_storage::io::PartAccess;
use gendb_storage::versions::{CapturedTable, CurrentCapture};
use gendb_verification::admission::cases::inline_columns;
use gendb_verification::admission::engine::engine_framework_files;
use gendb_verification::admission::execution::CandidateRunner;
use gendb_verification::admission::storage::{
    admit_storage, build_storage_asset, candidate_framework_files, derived_storage_input, publish_storage, run_constraints_digest, CandidateDerivation,
    StorageCandidate, StorageSchema,
};
use gendb_verification::admission::{dataset_ddl, IntegrityConstraints};
use gendb_verification::obligations::{
    flat_storage, plain_columns_interface_file, storage_crate_files, with_trusted_shim, DeclaredSource, FlatStorage, StorageName, ENGINE_CRATE_NAME,
    STORAGE_CRATE_NAME,
};
use gendb_verification::reference::{build_evaluator, BuildOptions, BuildStatus};
use gendb_verification::verus::engine_rules::{EngineLine, EngineRuleSet, TemplateConstants};
use gendb_verification::verus::{freeze_framework_crate, run_verus, CodegenOptions, FrameworkSource, VerusMode, VerusOptions, VerusOutcome, VerusToolchain};
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

const RECODED_INTERFACE: &str = include_str!("fixtures/general_storage/recoded_interface.rs");
const RECODED_BUILDER: &str = include_str!("fixtures/general_storage/recoded_builder.rs");
const ZONED_INTERFACE: &str = include_str!("fixtures/general_storage/zoned_interface.rs");
const ZONED_BUILDER: &str = include_str!("fixtures/general_storage/zoned_builder.rs");
const ENGINE_AGENT: &str = include_str!("fixtures/general_storage/engine_agent.rs");
const RANGE_CAPACITY: u64 = 64;

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
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).ancestors().nth(3).expect("<repository>/src/gendb/verification").to_path_buf()
}

fn base_dir() -> PathBuf {
    std::env::var_os("GENDB_ENGINE_TEST_WORK").map(PathBuf::from).unwrap_or_else(|| PathBuf::from(env!("CARGO_TARGET_TMPDIR")))
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

fn source(path: &str, text: &str) -> FrameworkSource {
    FrameworkSource { path: path.into(), text: text.into() }
}

/// The frozen crate of `files` (author files scanned at freezing), verified and compiled whole: `(frozen root, run
/// record)`. Reused from `<cache>/<name>` when an earlier run froze byte-equal sources.
fn verified_crate(toolchain: &VerusToolchain, files: &[FrameworkSource], crate_name: &str, cache: &Path, name: &str) -> (PathBuf, Value) {
    let key = serde_json::to_string(&files.iter().map(|f| (&f.path, &f.text)).collect::<BTreeMap<_, _>>()).unwrap();
    let dir = cache.join(name);
    if std::fs::read_to_string(dir.join("sources.json")).ok().as_deref() == Some(key.as_str()) {
        let run: Value = serde_json::from_str(&std::fs::read_to_string(dir.join("run.json")).unwrap()).unwrap();
        if Path::new(run["artifact"].as_str().unwrap_or_default()).is_file() {
            return (dir.join("frozen"), run);
        }
    }
    if dir.exists() {
        make_writable(&dir);
        std::fs::remove_dir_all(&dir).unwrap();
    }
    let unscanned: Vec<&str> = files.iter().filter(|f| gendb_registry::author_definition(&f.path).is_none()).map(|f| f.path.as_str()).collect();
    let frozen = freeze_framework_crate(files, &unscanned, &dir.join("frozen")).unwrap_or_else(|e| panic!("{name}: {e:?}"));
    let options = VerusOptions { crate_name: crate_name.into(), codegen: CodegenOptions { opt_level: 1, target_cpu: None }, num_threads: Some(16) };
    let run = with_build_lock(|| run_verus(toolchain, &frozen, &options, VerusMode::VerifyAndCompile, &dir.join("verus")).unwrap());
    assert_eq!(run.outcome, VerusOutcome::Compiled, "{name}: {} {}", run.detail, run.rendered_errors());
    let record = run.record();
    std::fs::write(dir.join("run.json"), serde_json::to_vec_pretty(&record).unwrap()).unwrap();
    std::fs::write(dir.join("sources.json"), key).unwrap();
    (frozen.root, record)
}

/// Make a frozen (read-only) tree writable so it can be removed.
fn make_writable(root: &Path) {
    use std::os::unix::fs::PermissionsExt;
    for entry in std::fs::read_dir(root).unwrap() {
        let path = entry.unwrap().path();
        let mode = if path.is_dir() { 0o755 } else { 0o644 };
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(mode)).unwrap();
        if path.is_dir() {
            make_writable(&path);
        }
    }
    std::fs::set_permissions(root, std::fs::Permissions::from_mode(0o755)).unwrap();
}

/// One template: its name (`Q01`), statement document, v0 arguments.
struct Template {
    name: String,
    doc: AstDocument,
    v0: Vec<String>,
}

fn templates(parser: &SqlParser, ddl: &Path) -> Vec<Template> {
    let dir = repository().join("src/gendb/fixtures/tpch/templates");
    let index: Value = serde_json::from_str(&std::fs::read_to_string(dir.join("templates.json")).unwrap()).unwrap();
    let visible: Value = serde_json::from_str(&std::fs::read_to_string(repository().join("output/tpch-sf100/bindings/visible.json")).unwrap()).unwrap();
    index["templates"]
        .as_object()
        .unwrap()
        .iter()
        .map(|(name, t)| {
            let params: Vec<ParamRequest> = serde_json::from_value(t["parameters"].clone()).unwrap();
            let placeholders: Vec<_> = params.iter().map(ParamRequest::placeholder).collect();
            let (_, translation) = parser.translate(ddl, &dir.join(t["sql"].as_str().unwrap()), "postgres", &placeholders).unwrap();
            let Translation::Ok(doc) = translation else { panic!("{name}: refused: {translation:?}") };
            let v0 = visible["queries"][name].as_array().unwrap()[0]["arguments"].as_array().unwrap().iter().map(|a| a.as_str().unwrap().to_string()).collect();
            Template { name: name.clone(), doc, v0 }
        })
        .collect()
}

/// The fixture capture of a tiny database (every table, one row-order identity per database).
fn capture(schema: &[TableDef], database: &HostTables, identity: &str) -> CurrentCapture {
    CurrentCapture {
        tables: schema
            .iter()
            .enumerate()
            .map(|(t, def)| CapturedTable {
                table: def.name.clone(),
                source_version: "tiny-v1".into(),
                row_order: identity.into(),
                rows: database[t].len() as u64,
                ordinals: (0..def.columns.len()).collect(),
            })
            .collect(),
    }
}

/// The verified SQLSpec evaluator's rows of `doc` on `tables`.
fn evaluator_rows(toolchain: &VerusToolchain, doc: &AstDocument, dir: &Path, tables: &HostTables) -> Vec<Vec<gendb_sqlspec::codec::HostValue>> {
    let build = with_build_lock(|| build_evaluator(toolchain, doc, &dir.join("ast.json"), &dir.join("build"), &BuildOptions::default()).unwrap());
    assert_eq!(build.status, BuildStatus::Ok, "reference build {}", build.record);
    match EvaluatorLibrary::load(build.library.as_ref().unwrap()).unwrap().run(tables).unwrap() {
        RunOutcome::Rows(rows) => rows,
        other => panic!("the reference answered {other:?}"),
    }
}

/// The own author files of a storage build (`stores/<name>/interface/**`, `builder/**`).
fn own_files<'a>(files: &'a [FrameworkSource], name: &StorageName) -> Vec<&'a FrameworkSource> {
    files.iter().filter(|f| f.path.starts_with(&name.interface_prefix()) || f.path.starts_with("builder/")).collect()
}

#[test]
#[ignore = "runs the pinned Verus (8 flat storages, 2 derived storages, the engine, 22 reference evaluators), the frontend and the gendb worker; set GENDB_WORKER; -- --ignored"]
fn general_line_storages_build_admit_and_serve_an_engine() {
    let worker = PathBuf::from(std::env::var_os("GENDB_WORKER").expect("GENDB_WORKER: an executable of this build serving `worker`"));
    let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let work = base_dir().join(format!("general-storage-{}-{nanos}", std::process::id()));
    let cache = base_dir().join("general-storage-cache");
    std::fs::create_dir_all(&work).unwrap();
    std::fs::create_dir_all(&cache).unwrap();
    let toolchain = VerusToolchain::from_env().unwrap();
    let parser = SqlParser::from_environment().unwrap();
    let runner = CandidateRunner { worker: worker.clone() };
    let mut evidence = json!({"work": work});

    // The dataset, its declared constraints, the schema and the general line's rule set over it.
    let dataset: DatasetSpec = serde_json::from_str(TPCH_DATASET).unwrap();
    let constraints: IntegrityConstraints =
        serde_json::from_str(&std::fs::read_to_string(repository().join("src/gendb/fixtures/tpch/integrity-constraints.json")).unwrap()).unwrap();
    let (ddl, omitted) = dataset_ddl(&dataset, Some(&constraints));
    assert!(omitted.is_empty());
    let ddl_path = work.join("schema.sql");
    std::fs::write(&ddl_path, &ddl).unwrap();
    std::fs::write(work.join("probe.sql"), "SELECT r_regionkey FROM region").unwrap();
    let Translation::Ok(probe) = parser.translate(&ddl_path, &work.join("probe.sql"), "postgres", &[]).unwrap().1 else { panic!("schema probe refused") };
    let schema: Vec<TableDef> = probe.tables.clone();
    let frontend = probe.frontend.clone();
    let schema_view = StorageSchema { tables: &schema, ddl: &ddl, frontend: &frontend };
    let constants = TemplateConstants::from_templates_json(&repository().join("src/gendb/fixtures/tpch/templates/templates.json")).unwrap();
    let general = EngineRuleSet::for_line(EngineLine::General, constants, &schema);
    let declared = run_constraints_digest(&schema).unwrap();
    let store = ObjectStore::open(work.join("library")).unwrap();
    let no_clauses = |_: &str, _: &str| Some((vec![], vec![]));

    // The tiny databases (one per template) and their captures.
    let templates = templates(&parser, &ddl_path);
    let databases: Vec<(String, HostTables, CurrentCapture)> = templates
        .iter()
        .map(|t| {
            let case = fixtures_dir().join(format!("pg_reference/tpch_all22_cases/{}.json", t.name.to_lowercase()));
            let database = Fixture::load(&case).unwrap().database_for(&t.doc).unwrap();
            let capture = capture(&schema, &database, &format!("tiny-{}", t.name.to_lowercase()));
            (t.name.clone(), database, capture)
        })
        .collect();

    // 1. The eight flat storages: verified, published, built over every tiny database, admitted.
    let flats: Vec<FlatStorage> = (0..schema.len()).map(|t| flat_storage(&schema, t).unwrap()).collect();
    let mut flat_packages: Vec<ContentId> = vec![];
    let mut assets: BTreeMap<(String, String), PathBuf> = BTreeMap::new();
    for flat in &flats {
        let mut files = storage_crate_files(&schema, &flat.name, &flat.declaration, false).unwrap();
        files.extend(flat.files.iter().cloned());
        let (frozen, run) = verified_crate(&toolchain, &with_trusted_shim(files, GENDB_STORAGE_SHIM_SOURCE), STORAGE_CRATE_NAME, &cache, flat.name.as_str());
        let candidate = StorageCandidate { name: &flat.name, declaration: &flat.declaration, uses_declared_constraints: false, derivation: None, frozen_root: &frozen, verus_run: &run, readers: vec![], flat: false };
        let published = publish_storage(&store, schema_view, &candidate, &no_clauses).unwrap();
        let table_id = flat.declaration.tables[0].table_id;
        let selection = BTreeMap::from([(table_id, (0..schema[table_id].columns.len()).collect::<BTreeSet<usize>>())]);
        let mut first_evidence = None;
        for (name, database, capture) in &databases {
            let input = WorkerInput::Inline { columns: inline_columns(&declared_columns(&schema, &selection).unwrap(), database).unwrap() };
            let asset = build_storage_asset(&store, &runner, published.package, capture, declared, input, 1, &work.join("asset-builds").join(format!("{}-{name}", flat.name))).unwrap();
            first_evidence.get_or_insert(asset.asset.evidence);
            assets.insert((flat.name.to_string(), name.clone()), asset.directory.clone());
        }
        admit_storage(&store, published.package, vec![first_evidence.unwrap()]).unwrap();
        flat_packages.push(published.package);
    }

    // 2. The two storages built from flat storages: scanned, verified, published, built from the flat assets, admitted.
    let lineitem = schema.iter().position(|t| t.name == "lineitem").unwrap();
    let region = schema.iter().position(|t| t.name == "region").unwrap();
    assert_eq!((lineitem, region), (0, 7), "the fixtures' table ids");
    let derived = [
        ("recoded", lineitem, BTreeSet::from([5usize]), None, vec![source("stores/recoded/interface/mod.rs", RECODED_INTERFACE)], RECODED_BUILDER),
        ("zoned", region, BTreeSet::from([0usize, 1, 2]), Some(0usize), vec![source("stores/zoned/interface/mod.rs", ZONED_INTERFACE)], ZONED_BUILDER),
    ];
    let mut derived_packages: Vec<(StorageName, ContentId)> = vec![];
    let mut derived_records = vec![];
    for (name, table, columns, extends, interface, builder) in derived {
        let name = StorageName::new(name).unwrap();
        let declaration = DeclaredSource::for_storage(&schema, &BTreeMap::from([(table, columns)])).unwrap();
        let derivation = CandidateDerivation { sources: vec![CandidateDerivation::source(&store, flats[table].name.as_str(), flat_packages[table]).unwrap()], extends };
        let mut files = candidate_framework_files(&schema, &name, &declaration, false, Some(&derivation)).unwrap();
        files.extend(interface);
        if name.as_str() == "zoned" {
            files.push(plain_columns_interface_file(&name));
        }
        files.push(source("builder/mod.rs", builder));
        let own: Vec<&FrameworkSource> = own_files(&files, &name);
        let findings: Vec<_> = own.iter().flat_map(|f| general.scan_storage_source(&f.path, &f.text)).collect();
        assert_eq!(findings, vec![], "{name}: the general line's storage scan");
        assert!(files.iter().any(|f| f.path == "sources_flat.rs") && files.iter().any(|f| f.path == "sources_flat/plain.rs"), "{name}: the flat access");
        let (frozen, run) = verified_crate(&toolchain, &files, STORAGE_CRATE_NAME, &cache, name.as_str());
        let candidate = StorageCandidate { name: &name, declaration: &declaration, uses_declared_constraints: false, derivation: Some(&derivation), frozen_root: &frozen, verus_run: &run, readers: vec![], flat: false };
        let published = publish_storage(&store, schema_view, &candidate, &no_clauses).unwrap();
        let mut first_evidence = None;
        for (template, _, capture) in &databases {
            let input = derived_storage_input(&store, &published.record, capture).unwrap();
            let asset = build_storage_asset(&store, &runner, published.package, capture, declared, input, 1, &work.join("asset-builds").join(format!("{name}-{template}"))).unwrap();
            first_evidence.get_or_insert(asset.asset.evidence);
            assets.insert((name.to_string(), template.clone()), asset.directory.clone());
        }
        let admission = admit_storage(&store, published.package, vec![first_evidence.unwrap()]).unwrap();
        derived_records.push(json!({"storage": name.as_str(), "package": published.package, "admission": admission, "verification": run["verification"],
            "extends": extends, "files_scanned": own.iter().map(|f| &f.path).collect::<Vec<_>>()}));
        derived_packages.push((name, published.package));
    }
    evidence["derived_storages"] = json!(derived_records);

    // 3. The engine that reads both: scanned, assembled from the library, verified; one call per template.
    assert_eq!(general.scan_agent_source("agent/mod.rs", ENGINE_AGENT), vec![], "the engine's agent under the general line's rules");
    let mut uses: Vec<VerusStorageUseV1> = flats.iter().zip(&flat_packages).map(|(f, p)| VerusStorageUseV1 { name: f.name.to_string(), package: *p }).collect();
    uses.extend(derived_packages.iter().map(|(n, p)| VerusStorageUseV1 { name: n.to_string(), package: *p }));
    let mut engine_files = engine_framework_files(&store, &schema, &uses, "the general storage route test").unwrap();
    engine_files.push(source("agent/mod.rs", ENGINE_AGENT));
    let (_, engine_run) = verified_crate(&toolchain, &engine_files, ENGINE_CRATE_NAME, &cache, "engine");
    let library = PathBuf::from(engine_run["artifact"].as_str().unwrap());
    evidence["engine_verification"] = engine_run["verification"].clone();
    let mut answers = vec![];
    for (t, (name, database, _)) in templates.iter().zip(&databases) {
        let ast = encode_binding(&t.doc, &t.v0).unwrap_or_else(|e| panic!("{name}: {e}"));
        let inputs: Vec<StorageUseInput> = uses.iter().map(|u| StorageUseInput { name: u.name.clone(), parts_directory: assets[&(u.name.clone(), name.clone())].clone() }).collect();
        let dir = work.join("calls").join(name);
        let request = WorkerRequest::for_engine_query(&library, inputs, PartAccess::default(), std::slice::from_ref(&ast.bytes), vec![1], 1, RANGE_CAPACITY);
        let result = spawn(&worker, &dir.join("worker"), &request, 3600).unwrap_or_else(|e| panic!("{name}: {e}"));
        let rows = match QueryAnswer::of(&result.observations[0].outcome) {
            Ok(QueryAnswer::Rows(rows)) => rows,
            other => panic!("{name}: {other:?}"),
        };
        let expected = evaluator_rows(&toolchain, &ast.document, &dir.join("reference"), database);
        assert_eq!(rows, expected, "{name}: the engine's rows differ from the reference evaluator's");
        eprintln!("{name}: {} rows equal to the reference", rows.len());
        answers.push(json!({"template": name, "rows": rows.len(), "equal_to_reference": true}));
    }
    evidence["answers"] = json!(answers);

    // 4. Controls: naming the flat source, or a column, is refused by the general line's storage scan.
    let naming_source = ZONED_BUILDER.replacen("verus! {", "verus! {\npub open spec fn kept() -> bool { crate::stores::flat_region::declaration::stored_table_t0() == 7 }\n", 1);
    let refused: Vec<_> = general.scan_storage_source("builder/mod.rs", &naming_source).into_iter().map(|f| f.rule).collect();
    assert!(refused.contains(&"schema_name"), "{refused:?}");
    let naming_column = RECODED_INTERFACE.replacen("pub open spec fn scale()", "pub open spec fn l_extendedprice_scale() -> nat { 2 }\n\npub open spec fn scale()", 1);
    let refused: Vec<_> = general.scan_storage_source("stores/recoded/interface/mod.rs", &naming_column).into_iter().map(|f| f.rule).collect();
    assert!(refused.contains(&"schema_name"), "{refused:?}");
    evidence["controls"] = json!({"builder_naming_its_flat_source": "refused (schema_name)", "interface_naming_a_column": "refused (schema_name)"});
    std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", work.join("evidence.json").display());
}
