//! The stored-data library path end to end on the tiny storage fixture (`fixtures/verus_storage`: interface, builder
//! and query read unchanged), through the admission and serving APIs:
//! 1. the statement is prepared like any request (`admission::prepare_statement` over a declared dataset: schema
//!    `sensor`/`site`, the storage stores sensor's id, reading and day), and the storage crate and query crate are
//!    assembled by `obligations::{storage_crate_files, query_crate_files}` with their shims, frozen and checked by ONE
//!    pinned Verus `--no-cheating` verify+compile each (run records persisted; `GENDB_S3_REUSE=<work>` reuses them);
//! 2. `admission::storage::publish_storage` publishes the storage build and package; `build_storage_asset` builds the
//!    asset once with the STORED library object into the library, and a second call reuses it (no build);
//!    `admit_storage` admits the package;
//! 3. `admission::qualification_v4::qualify_v4` admits the query package (fresh translation, fresh generation with the
//!    interface from the stored closure, configuration, closure and composition checks);
//! 4. the run directory is moved away and the library itself is moved: `runtime::serve::serve` still answers exactly
//!    from the library-relative asset, with the verified request counters below the stored bytes;
//! 2b. a storage built from the admitted one (derived entry, `extends`) is checked, published and built from the
//!    source's asset alone: its parts are the source's part files as hard links;
//! 5. controls: a stale capture (another row-order identity) is refused `NoStorageAsset`; an altered interface copy in
//!    a query build is refused at admission; a storage build whose builder implements a framework type is refused at
//!    publication by the central author-source scan over its stored sources; a new column capture of the same table
//!    (same row-order identity) resolves the same asset.
//!
//! Needs the pinned frontend Python, the pinned Verus (`GENDB_VERUS_HOME`, default `<repository>/toolchains`) and the
//! `gendb` executable as the worker (`GENDB_WORKER`); run with `--ignored`.
use gendb_artifacts::verus::VerusStorageUseV1;
use gendb_artifacts::{ColType, ColumnSpec, ObjectStore};
use gendb_frontend::parser::SqlParser;
use gendb_frontend::params::ParamRequest;
use gendb_runtime::abi::{GENDB_QUERY_SHIM_V4_SOURCE, GENDB_STORAGE_SHIM_SOURCE};
use gendb_runtime::answer::QueryAnswer;
use gendb_runtime::serve::{ServeError, ServingRoute, WorkerExecutor, serve};
use gendb_runtime::worker::{InlineColumn, InlineElem, WorkerInput};
use gendb_storage::import::{DataFormat, DatasetSpec, TableSpec};
use gendb_storage::io::{PartAccess, ReadAdvice};
use gendb_storage::versions::{CapturedTable, CurrentCapture};
use gendb_verification::admission::execution::CandidateRunner;
use gendb_verification::admission::qualification_v4::{QueryV4Candidate, QueryV4Context, qualify_v4};
use gendb_verification::admission::storage::{
    CandidateDerivation, StorageCandidate, StorageSchema, admit_storage, build_storage_asset, candidate_framework_files, derived_storage_input, publish_storage,
};
use gendb_verification::admission::prepare_statement;
use gendb_verification::obligations::{
    query_crate_files, storage_crate_files, with_trusted_shim, DeclaredSource, StorageName, StorageUse, CANDIDATE_CRATE_NAME,
    STORAGE_CRATE_NAME,
};
use gendb_verification::verus::{
    freeze_framework_crate, run_verus, CodegenOptions, FrameworkSource, VerusMode, VerusOptions, VerusOutcome, VerusToolchain,
};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

const INTERFACE: &str = include_str!("fixtures/verus_storage/interface.rs");
const BUILDER: &str = include_str!("fixtures/verus_storage/builder.rs");
const AGENT: &str = include_str!("fixtures/verus_storage/agent.rs");
const DERIVED_BUILDER: &str = include_str!("fixtures/verus_storage/derived_builder.rs");
const TIMEOUT_SECONDS: u64 = 600;

fn fixtures() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

fn column(name: &str, ty: ColType, nullable: bool) -> ColumnSpec {
    ColumnSpec { name: name.into(), ty, nullable }
}

/// The fixture schema as a declared dataset (text columns as `text`: the dataset DDL has no char/varchar).
fn dataset() -> DatasetSpec {
    let table = |name: &str, fields| TableSpec { name: name.into(), fields, locations: vec![], format: DataFormat::Parquet };
    DatasetSpec {
        tables: vec![
            table("site", vec![column("code", ColType::Utf8, false), column("region", ColType::I32, false)]),
            table("sensor", vec![
                column("id", ColType::I32, false),
                column("site", ColType::I32, false),
                column("reading", ColType::Decimal { p: 10, s: 2 }, false),
                column("day", ColType::Date32, false),
                column("tag", ColType::Utf8, false),
                column("note", ColType::Utf8, true),
            ]),
        ],
    }
}

fn source(path: &str, text: &str) -> FrameworkSource {
    FrameworkSource { path: path.into(), text: text.into() }
}

/// Freeze `files` (author files scanned) and verify+compile once, or reuse `<work>/<name>` from an earlier run. Returns
/// the frozen root and the persisted run record.
fn checked_crate(toolchain: &VerusToolchain, work: &Path, name: &str, crate_name: &str, files: &[FrameworkSource]) -> (PathBuf, Value) {
    let dir = work.join(name);
    let record = dir.join("run.json");
    if !record.is_file() {
        let author = |p: &str| p.starts_with("builder/") || p.starts_with("agent/") || p.contains("/interface/");
        let unscanned: Vec<&str> = files.iter().filter(|f| !author(&f.path)).map(|f| f.path.as_str()).collect();
        let frozen = freeze_framework_crate(files, &unscanned, &dir.join("frozen")).unwrap_or_else(|e| panic!("{name}: {e:?}"));
        let options = VerusOptions { crate_name: crate_name.into(), codegen: CodegenOptions { opt_level: 1, target_cpu: None }, num_threads: Some(8) };
        let run = run_verus(toolchain, &frozen, &options, VerusMode::VerifyAndCompile, &dir.join("verus-build")).unwrap();
        assert_eq!(run.outcome, VerusOutcome::Compiled, "{name}: {}", run.rendered_errors());
        std::fs::write(&record, serde_json::to_vec_pretty(&run.record()).unwrap()).unwrap();
    }
    (dir.join("frozen"), serde_json::from_slice(&std::fs::read(&record).unwrap()).unwrap())
}

fn capture(row_order: &str, ordinals: Vec<usize>) -> CurrentCapture {
    CurrentCapture {
        tables: vec![CapturedTable { table: "sensor".into(), source_version: "fixture-v1".into(), row_order: row_order.into(), rows: 6, ordinals }],
    }
}

#[test]
#[ignore = "runs the pinned Verus toolchain, frontend and the gendb worker; set GENDB_WORKER; -- --ignored"]
fn storage_library_admits_reuses_and_serves_from_the_library() {
    let worker = PathBuf::from(std::env::var_os("GENDB_WORKER").expect("GENDB_WORKER: the gendb executable"));
    let work = match std::env::var_os("GENDB_S3_REUSE") {
        Some(reuse) => PathBuf::from(reuse),
        None => {
            let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
            Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("verus-storage-library-{}-{nanos}", std::process::id()))
        }
    };
    let attempt = work.join(format!("attempt-{}", std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
    let (run, library) = (attempt.join("run"), attempt.join("library"));
    std::fs::create_dir_all(&run).unwrap();
    let toolchain = VerusToolchain::from_env().unwrap();
    let parser = SqlParser::from_environment().unwrap();
    let dataset = dataset();

    // 1. The statement and both crates.
    let requests: Vec<ParamRequest> =
        serde_json::from_str(&std::fs::read_to_string(fixtures().join("verus_storage/params.json")).unwrap()).unwrap();
    let sql = std::fs::read_to_string(fixtures().join("verus_storage/query.sql")).unwrap();
    let statement = prepare_statement(&parser, &dataset, None, &sql, &requests, &[], &[], &run.join("statement")).unwrap_or_else(|r| panic!("{}", r.error));
    let doc = &statement.instance.doc;
    let name = StorageName::new("sensor_days").unwrap();
    let declaration = DeclaredSource::for_storage(&doc.tables, &BTreeMap::from([(1, BTreeSet::from([0, 2, 3]))])).unwrap();
    let interface = vec![source("stores/sensor_days/interface/mod.rs", INTERFACE)];
    let mut storage_files = storage_crate_files(&doc.tables, &name, &declaration, false).unwrap();
    storage_files.extend(interface.iter().cloned());
    storage_files.push(source("builder/mod.rs", BUILDER));
    let uses = [StorageUse { name: &name, declaration: &declaration, interface: &interface }];
    let mut query_files = query_crate_files(&statement.instance, &statement.source, &uses, &statement.identity()).unwrap();
    query_files.push(source("agent/mod.rs", AGENT));
    let (storage_root, storage_run) =
        checked_crate(&toolchain, &work, "storage", STORAGE_CRATE_NAME, &with_trusted_shim(storage_files, GENDB_STORAGE_SHIM_SOURCE));
    let (query_root, query_run) =
        checked_crate(&toolchain, &work, "query", CANDIDATE_CRATE_NAME, &with_trusted_shim(query_files, GENDB_QUERY_SHIM_V4_SOURCE));

    // 2. Storage package, one asset build by the stored library, reuse, admission.
    let store = ObjectStore::open(&library).unwrap();
    let no_clauses = |_: &str, _: &str| Some((vec![], vec![]));
    let frontend = doc.frontend.clone();
    let schema = StorageSchema { tables: &doc.tables, ddl: &statement.schema_ddl, frontend: &frontend };
    let candidate = StorageCandidate { name: &name, declaration: &declaration, uses_declared_constraints: false, derivation: None, frozen_root: &storage_root, verus_run: &storage_run, readers: vec![], flat: false };
    // Control: records of a storage build whose builder implements a framework type are refused by the central
    // author-source scan at publication, even though no freeze scanned this copy.
    let unscanned = attempt.join("unscanned-storage");
    copy_tree(&storage_root, &unscanned);
    let builder = unscanned.join("src/builder/mod.rs");
    let text = std::fs::read_to_string(&builder).unwrap().replacen("verus! {", "verus! {\nimpl crate::gendb_entry::stored::StoredParts {}\n", 1);
    std::fs::write(&builder, text).unwrap();
    let unscanned_candidate = StorageCandidate { frozen_root: &unscanned, ..candidate };
    let scan_refusal = publish_storage(&store, schema, &unscanned_candidate, &no_clauses).unwrap_err();
    assert!(scan_refusal.to_string().contains("impl_ownership"), "{scan_refusal}");
    let candidate = StorageCandidate { frozen_root: &storage_root, ..unscanned_candidate };
    let published = publish_storage(&store, schema, &candidate, &no_clauses).unwrap();
    let runner = CandidateRunner { worker: worker.clone() };
    let column = |elem, values: &[i64]| InlineColumn { elem, values: values.iter().map(i64::to_string).collect(), validity: None };
    let input = WorkerInput::Inline {
        columns: vec![
            column(InlineElem::I32, &[1, 2, 3, 4, 5, 6]),
            column(InlineElem::I128, &[1234, -5, 700, 1, 2, 3]),
            column(InlineElem::I32, &[10957, 10958, 11498, 11499, 12000, 12001]),
        ],
    };
    let current = capture("fixture-read-1", vec![0, 2, 3]);
    let asset = build_storage_asset(&store, &runner, published.package, &current, None, input.clone(), 1, &run.join("asset-build-1")).unwrap();
    assert!(asset.built && asset.directory.starts_with(&library), "{:?}", asset.directory);
    assert_eq!(asset.asset.directory, format!("assets/{}", asset.asset.key.identity().unwrap().to_hex()));
    let again = build_storage_asset(&store, &runner, published.package, &current, None, input, 1, &run.join("asset-build-2")).unwrap();
    assert!(!again.built && again.id == asset.id && !run.join("asset-build-2").exists(), "the second call reuses the asset: no build");
    let storage_admission = admit_storage(&store, published.package, vec![asset.asset.evidence]).unwrap();

    // 2b. A storage built from the admitted one (derived entry), extending it: its asset holds the source's part files
    // as hard links and builds no part of its own.
    let copy_name = StorageName::new("sensor_copy").unwrap();
    let derivation = CandidateDerivation { sources: vec![CandidateDerivation::source(&store, "sensor_days", published.package).unwrap()], extends: Some(0) };
    let mut derived_files = candidate_framework_files(&doc.tables, &copy_name, &declaration, false, Some(&derivation)).unwrap();
    derived_files.push(source("stores/sensor_copy/interface/mod.rs", INTERFACE));
    derived_files.push(source("builder/mod.rs", DERIVED_BUILDER));
    let (derived_root, derived_run) = checked_crate(&toolchain, &work, "derived", STORAGE_CRATE_NAME, &derived_files);
    let derived_candidate = StorageCandidate {
        name: &copy_name,
        declaration: &declaration,
        uses_declared_constraints: false,
        derivation: Some(&derivation),
        frozen_root: &derived_root,
        verus_run: &derived_run,
        readers: vec![],
        flat: false,
    };
    let derived = publish_storage(&store, schema, &derived_candidate, &no_clauses).unwrap();
    assert_eq!(derived.record.derived_from.as_ref().map(|d| d.sources[0].package), Some(published.package));
    let derived_input = derived_storage_input(&store, &derived.record, &current).unwrap();
    let derived_asset = build_storage_asset(&store, &runner, derived.package, &current, None, derived_input, 1, &run.join("derived-build")).unwrap();
    assert_eq!(derived_asset.asset.parts, asset.asset.parts, "every part inherited, none added");
    {
        use std::os::unix::fs::MetadataExt;
        let inode = |dir: &Path| std::fs::metadata(dir.join("part-0004.bin")).unwrap().ino();
        assert_eq!(inode(&derived_asset.directory), inode(&asset.directory), "inherited parts are the source's files");
    }

    // 3. Query package over the admitted storage.
    let evaluation = json!({"fixture": "verus_storage_library", "assets": [asset.id]});
    let context = QueryV4Context { library: &library, statement: &statement, dataset: &dataset, parser: &parser, clause_text: &no_clauses };
    let storage_uses = vec![VerusStorageUseV1 { name: "sensor_days".into(), package: published.package }];
    let candidate = |frozen_root| QueryV4Candidate {
        frozen_root,
        verus_run: &query_run,
        storage_uses: storage_uses.clone(),
        modules: vec![],
        evaluation: &evaluation,
        assets: vec![asset.id],
    };
    // Control: a query build whose copy of the interface was altered is refused (framework generation / closure).
    let altered = attempt.join("altered-query");
    copy_tree(&query_root, &altered);
    let copy = altered.join("src/stores/sensor_days/interface/mod.rs");
    let text = std::fs::read_to_string(&copy).unwrap().replace("pub const BLOCK: usize = 2;", "pub const BLOCK: usize = 3;");
    std::fs::write(&copy, text).unwrap();
    let refused = qualify_v4(&context, candidate(&altered)).unwrap_err();
    assert!(refused.to_string().contains("stores/sensor_days/interface/mod.rs"), "{refused}");
    let qualification = qualify_v4(&context, candidate(&query_root)).unwrap();

    // 4. Move the run directory and the library: serving uses only the library.
    std::fs::rename(&run, attempt.join("run-moved")).unwrap();
    let moved_library = attempt.join("library-moved");
    std::fs::rename(&library, &moved_library).unwrap();
    let store = ObjectStore::open_existing(&moved_library).unwrap();
    let executor = WorkerExecutor::new(&worker, &attempt.join("serving"), TIMEOUT_SECONDS, 64, 1);
    let access = PartAccess { read_advice: ReadAdvice::Random, drop_cached_pages: false };
    let arguments = vec!["2000-01-03".to_string()];
    let served = serve(&store, &statement.instance, &arguments, &current, access, &executor, 1).unwrap();
    assert_eq!(served.route, ServingRoute::StoredDataV4);
    let QueryAnswer::Rows(rows) = &served.answer else { panic!("rows expected: {:?}", served.answer) };
    assert_eq!(rows.len(), 2);
    let record = served.record().unwrap();
    let mut texts: Vec<Value> = record["answer"]["rows"].as_array().unwrap().clone();
    texts.sort_by_key(|row| row[0].to_string());
    assert_eq!(texts, vec![json!([1, "12.34"]), json!([2, "-0.05"])], "{record}");
    let requests = &served.outcome.storage_requests;
    assert_eq!(requests.len(), 1);
    assert!(requests[0].bytes < asset.asset.storage_bytes, "selective reads: {requests:?} of {} stored bytes", asset.asset.storage_bytes);
    assert_eq!(served.storages[0].asset, asset.id);

    // 5. Controls on the moved library.
    match serve(&store, &statement.instance, &arguments, &capture("fixture-read-2", vec![0, 2, 3]), access, &executor, 1) {
        Err(ServeError::NoStorageAsset { storage }) => assert_eq!(storage, "sensor_days"),
        other => panic!("a stale capture must be refused: {:?}", other.err()),
    }
    let widened = capture("fixture-read-1", vec![0, 1, 2, 3, 4]);
    let served_widened = serve(&store, &statement.instance, &arguments, &widened, access, &executor, 1).unwrap();
    assert_eq!(served_widened.storages[0].asset, asset.id, "added columns of the same read keep the asset");

    let evidence = json!({"library": moved_library, "storage_package": published.package, "storage_build": published.build,
        "storage_admission": storage_admission, "asset": asset.id, "asset_directory": asset.asset.directory,
        "stored_bytes": asset.asset.storage_bytes, "asset_build_reused_on_second_call": !again.built,
        "qualification": qualification.record(), "served": record, "stale_capture": "no_storage_asset",
        "altered_interface_refusal": refused.to_string(), "unscanned_builder_refusal": scan_refusal.to_string(), "widened_capture_asset": served_widened.storages[0].asset,
        "storage_run": storage_run.get("verification"), "query_run": query_run.get("verification")});
    std::fs::write(attempt.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", attempt.join("evidence.json").display());
}

/// Copy a frozen crate directory (files become writable copies).
fn copy_tree(from: &Path, to: &Path) {
    std::fs::create_dir_all(to).unwrap();
    for entry in std::fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let target = to.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            copy_tree(&entry.path(), &target);
        } else {
            std::fs::write(&target, std::fs::read(entry.path()).unwrap()).unwrap();
        }
    }
}
