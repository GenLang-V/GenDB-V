//! The storage entry and the query entry v4 end to end at the proof boundary, on a tiny non-TPC-H fixture
//! (`fixtures/verus_storage`, over the schema of `fixtures/verus_params`):
//! - storage `sensor_days` stores sensor's id, reading and day (not site, tag, note) in canonical row order with a
//!   zone map of `day` per block of two rows, and a reader that marks the blocks that may hold a day below a bound;
//! - the query `SELECT id, reading FROM sensor WHERE day < $1` (`$1 date` free) reads the block minima first and then
//!   only the data extents of marked blocks.
//!
//! SQL + parameter request -> frontend AST -> `DeclaredSource::for_storage` / `columns::source_declaration` ->
//! `obligations::{storage_crate_files, query_crate_files}` (the one assembly of each kind) + the fixture's interface,
//! builder and query (hand-written framework test inputs, not author outputs) -> the dependency closure the query crate
//! must share with the storage crate -> ONE pinned Verus `--no-cheating` verify+compile of each whole crate. Negative
//! variants (verify only): an unsound zone-map reader and a wrong zone map (storage crate), a forged `StoredParts` and a
//! counter reset (query crate). An altered interface copy is refused by the closure comparison.
//!
//!
//! Declared integrity constraints (query entry v5): the same query crate over the fixture schema with
//! `ALTER TABLE ... ADD` declarations, its agent extended by a lemma that uses the declared PRIMARY KEY of sensor
//! (`fixtures/verus_storage/declared_key.rs`), verifies as a whole crate; removing that key from the declarations
//! (another one kept) or deleting the entry's constraint conjunct makes it fail.
//!
//! Constrained storage builders (storage entry v2): the same storage opting in (`uses_declared_constraints`) under
//! those declarations, its builder extended by a lemma that derives distinct delivered ids from the entry's
//! precondition `source_witnessed` (`fixtures/verus_storage/witnessed_key.rs`) and requiring it, verifies and compiles
//! as a whole crate; deleting `source_witnessed` from the entry's precondition makes it fail. The constrained query crate
//! (entry v5) composes with the unconstrained storage and with the constrained one by the unchanged closure rule: both
//! storages have the same closure, so the query crate is the same text either way.
//!
//! The generation tests need the pinned frontend Python only. The Verus tests also need the pinned Verus
//! (`GENDB_VERUS_HOME`, default `<repository>/toolchains`); run them with `--ignored`.
use gendb_frontend::ast::{AstDocument, Translation};
use gendb_frontend::columns::{analyze, source_declaration};
use gendb_frontend::params::{declare, instantiate, Instance, ParamRequest};
use gendb_frontend::parser::SqlParser;
use gendb_runtime::abi::GENDB_STORAGE_SHIM_SOURCE;
use gendb_verification::obligations::{
    check_storage_composition, compare_storage_closure, derived_storage_crate_files, query_crate_files, query_entry, storage_closure, storage_crate_files,
    with_trusted_shim, Derivation,
    AssemblyError, ClosureMismatch, CompositionError, DeclaredSource, StorageName, StorageUse, CANDIDATE_CRATE_NAME, QUERY_ENTRY_V5,
    QUERY_ENTRY_V5_SOURCE, STORAGE_CRATE_NAME, STORAGE_ENTRY_SOURCE, STORAGE_ENTRY_V2_SOURCE,
};
use gendb_verification::verus::{
    freeze_framework_crate, rule, run_verus, CodegenOptions, FrameworkSource, FreezeError, FrozenCrate, VerusMode, VerusOptions,
    VerusOutcome, VerusToolchain,
};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

const INTERFACE: &str = include_str!("fixtures/verus_storage/interface.rs");
const BUILDER: &str = include_str!("fixtures/verus_storage/builder.rs");
const AGENT: &str = include_str!("fixtures/verus_storage/agent.rs");
const DECLARED_KEY: &str = include_str!("fixtures/verus_storage/declared_key.rs");
const WITNESSED_KEY: &str = include_str!("fixtures/verus_storage/witnessed_key.rs");
const DERIVED_BUILDER: &str = include_str!("fixtures/verus_storage/derived_builder.rs");

fn fixtures() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

fn scratch(name: &str) -> PathBuf {
    let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let d = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("verus-storage-entry-{name}-{}-{nanos}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn source(path: &str, text: &str) -> FrameworkSource {
    FrameworkSource { path: path.into(), text: text.into() }
}

/// The fixture statement, translated against the shared fixture schema.
fn translated() -> (AstDocument, Vec<ParamRequest>) {
    translated_over(&fixtures().join("verus_params/schema.sql"))
}

/// The fixture statement, translated against the DDL file `schema`.
fn translated_over(schema: &Path) -> (AstDocument, Vec<ParamRequest>) {
    let dir = fixtures().join("verus_storage");
    let requests: Vec<ParamRequest> = serde_json::from_str(&std::fs::read_to_string(dir.join("params.json")).unwrap()).unwrap();
    let placeholders: Vec<_> = requests.iter().map(|r| r.placeholder()).collect();
    let parser = SqlParser::from_environment().unwrap();
    let (_, t) = parser.translate(schema, &dir.join("query.sql"), "postgres", &placeholders).unwrap();
    let Translation::Ok(doc) = t else { panic!("fixture SQL refused: {t:?}") };
    (doc, requests)
}

/// Both crates of the fixture: every file (framework and fixture author files), relative to `src/`.
struct Fixture {
    name: StorageName,
    storage: Vec<FrameworkSource>,
    query: Vec<FrameworkSource>,
}

fn fixture_with(interface: &str, builder: &str, agent: &str) -> Fixture {
    fixture_from(translated(), interface, builder, agent, false)
}

/// Both crates over the translated fixture; the storage crate opts in to the declared constraints when
/// `uses_declared_constraints` (storage entry v2).
fn fixture_from(
    (doc, requests): (AstDocument, Vec<ParamRequest>),
    interface: &str,
    builder: &str,
    agent: &str,
    uses_declared_constraints: bool,
) -> Fixture {
    let inst: Instance = instantiate(&doc, &declare(&doc, &requests).unwrap()).unwrap();
    let name = StorageName::new("sensor_days").unwrap();
    // sensor is table 1: id, reading, day (ordinals 0, 2, 3).
    let selection = BTreeMap::from([(1, BTreeSet::from([0, 2, 3]))]);
    let declaration = DeclaredSource::for_storage(&doc.tables, &selection).unwrap();
    let interface_files = vec![source("stores/sensor_days/interface/mod.rs", interface)];
    let mut storage = storage_crate_files(&doc.tables, &name, &declaration, uses_declared_constraints).unwrap();
    storage.extend(interface_files.iter().cloned());
    storage.push(source("builder/mod.rs", builder));
    let delivered = source_declaration(&inst.doc, &analyze(&inst.doc).unwrap()).unwrap();
    let uses = [StorageUse { name: &name, declaration: &declaration, interface: &interface_files }];
    let mut query = query_crate_files(&inst, &delivered, &uses, "verus_storage fixture").unwrap();
    query.push(source("agent/mod.rs", agent));
    Fixture { name, storage, query }
}

fn fixture() -> Fixture {
    fixture_with(INTERFACE, BUILDER, AGENT)
}

fn text<'a>(files: &'a [FrameworkSource], path: &str) -> &'a str {
    &files.iter().find(|f| f.path == path).unwrap_or_else(|| panic!("{path} missing")).text
}

/// Generation only (no Verus). The storage declaration stores sensor's columns 0, 2 and 3; the query crate imports the
/// schema from `schema.rs`, carries the storage's declaration and interface, shares the storage crate's closure byte
/// for byte and its author files pass the author-source rules (`check_storage_composition`); an altered interface
/// copy and a missing schema are refused.
#[test]
fn storage_fixture_sources_generate_and_share_the_closure() {
    let f = fixture();
    let declaration = text(&f.storage, "stores/sensor_days/declaration.rs");
    assert!(declaration.contains("pub open spec fn stored_table_t0() -> nat {\n    1\n}"), "{declaration}");
    assert!(declaration.contains("pub open spec fn stored_cols_t0() -> Seq<nat> {\n    seq![0nat, 2, 3]\n}"));
    assert!(declaration.contains("seq![proj_all(db.tables[stored_table_t0() as int], stored_cols_t0())]"));
    let query = text(&f.query, "query.rs");
    assert!(query.contains("use crate::schema::schema_spec;") && !query.contains("fn schema_spec"), "{query}");
    let stores = text(&f.query, "gendb_entry/stores.rs");
    assert!(stores.contains("pub sensor_days: StoredParts,"), "{stores}");
    assert!(stores.contains(
        "&&& crate::stores::sensor_days::interface::represents(sv.sensor_days, crate::stores::sensor_days::declaration::stored_relations(db))"
    ));
    for (path, kind) in [("builder/mod.rs", &f.storage), ("gendb_source.rs", &f.storage), ("agent/mod.rs", &f.query), ("gendb_params.rs", &f.query)] {
        text(kind, path);
    }
    assert_eq!(check_storage_composition(&f.storage, &f.query, &f.name), Ok(()));
    let mut altered = f.query.clone();
    let copy = altered.iter_mut().find(|s| s.path == "stores/sensor_days/interface/mod.rs").unwrap();
    copy.text = copy.text.replace("pub const BLOCK: usize = 2;", "pub const BLOCK: usize = 3;");
    assert_eq!(
        compare_storage_closure(&f.storage, &altered, &f.name),
        Err(ClosureMismatch::Different { path: "stores/sensor_days/interface/mod.rs".into() })
    );
    let missing: Vec<FrameworkSource> = f.query.iter().filter(|s| s.path != "schema.rs").cloned().collect();
    assert_eq!(compare_storage_closure(&f.storage, &missing, &f.name), Err(ClosureMismatch::Missing { path: "schema.rs".into() }));
}

fn options(name: &str) -> VerusOptions {
    VerusOptions { crate_name: name.into(), codegen: CodegenOptions { opt_level: 1, target_cpu: None }, num_threads: Some(8) }
}

/// Freeze `files`: framework files unscanned (the fork/join file names vstd threads), author files (the registry's
/// author definitions: `builder/**`, `stores/*/interface/**`, `agent/**`) scanned by the refusal list.
fn try_freeze(work: &Path, name: &str, files: &[FrameworkSource]) -> Result<FrozenCrate, FreezeError> {
    let unscanned: Vec<&str> =
        files.iter().filter(|f| gendb_registry::author_definition(&f.path).is_none()).map(|f| f.path.as_str()).collect();
    freeze_framework_crate(files, &unscanned, &work.join(name).join("frozen"))
}

fn freeze(work: &Path, name: &str, files: &[FrameworkSource]) -> FrozenCrate {
    try_freeze(work, name, files).unwrap_or_else(|e| panic!("{name}: {e:?}"))
}

/// Freeze only (no Verus). The fixture's author files pass the author-source rules in both crate kinds. An interface
/// whose meaning depends on the crate (`module_path!`) and a query module that adds a method to the framework's
/// `StoredParts` are refused when frozen, with the rule and file named, and the composition rule refuses the latter.
#[test]
fn fixture_author_sources_are_scanned_at_freeze() {
    let work = scratch("source-rules");
    let f = fixture();
    freeze(&work, "storage", &f.storage);
    freeze(&work, "query", &f.query);
    let named = variant(INTERFACE, "pub const BLOCK: usize = 2;", "pub const BLOCK: usize = 2;\n\npub open spec fn crate_named() -> bool { module_path!()@.len() == 0 }");
    let peek = variant(AGENT, "verus! {", "verus! {\n\nimpl crate::gendb_entry::stored::StoredParts { pub open spec fn peek(&self) -> bool { true } }");
    for (name, files, file, refused_by) in [
        ("interface-module-path", fixture_with(&named, BUILDER, AGENT).storage, "stores/sensor_days/interface/mod.rs", rule::MACRO),
        ("agent-foreign-impl", fixture_with(INTERFACE, BUILDER, &peek).query, "agent/mod.rs", rule::IMPL_OWNERSHIP),
    ] {
        match try_freeze(&work, name, &files) {
            Err(FreezeError::Refused { findings }) => {
                assert!(findings.iter().any(|x| x.rule == refused_by && x.file == file), "{name}: {findings:?}")
            }
            other => panic!("{name}: expected a refusal, got {other:?}"),
        }
    }
    let composed = fixture_with(INTERFACE, BUILDER, &peek);
    let refused = check_storage_composition(&composed.storage, &composed.query, &composed.name);
    assert!(matches!(&refused, Err(CompositionError::SourceRules(x)) if x.iter().all(|x| x.rule == rule::IMPL_OWNERSHIP)), "{refused:?}");
}

/// Replace exactly one occurrence of `from` in `text` (the variant must differ from the fixture).
fn variant(text: &str, from: &str, to: &str) -> String {
    assert_eq!(text.matches(from).count(), 1, "variant anchor {from:?} must occur once");
    text.replacen(from, to, 1)
}

#[test]
#[ignore = "runs the pinned Verus toolchain and frontend; cargo test -p gendb-verification --test verus_storage_entry -- --ignored"]
fn verified_storage_and_query_entries_check_and_refuse_bypasses() {
    let work = scratch("entries");
    let toolchain = VerusToolchain::from_env().unwrap();
    let f = fixture();
    let mut evidence = serde_json::Map::new();

    // One whole-crate --no-cheating Verus run per crate, which also compiles the library a host would run.
    for (name, crate_name, files) in [("storage", STORAGE_CRATE_NAME, &f.storage), ("query", CANDIDATE_CRATE_NAME, &f.query)] {
        let frozen = freeze(&work, name, files);
        let run = run_verus(&toolchain, &frozen, &options(crate_name), VerusMode::VerifyAndCompile, &work.join(name).join("verus-build")).unwrap();
        assert_eq!(run.outcome, VerusOutcome::Compiled, "{name}: {}", run.rendered_errors());
        let summary = run.verification.clone().unwrap();
        assert!(summary.is_verifying_entire_crate && summary.errors == 0, "{summary:?}");
        evidence.insert(name.into(), serde_json::json!({"verification": summary, "wall_ns": run.wall_ns, "library": run.artifact}));
    }

    // Negative variants: each must be rejected (proof failure or compile error) at the fixed boundary.
    let negatives = [
        ("unsound-reader", fixture_with(&variant(&variant(INTERFACE, NEG_READER.0, NEG_READER.1), NEG_READER_INVARIANT.0, NEG_READER_INVARIANT.1), BUILDER, AGENT).storage),
        ("wrong-zone-map", fixture_with(INTERFACE, &variant(BUILDER, NEG_ZONES.0, NEG_ZONES.1), AGENT).storage),
        ("forged-handle", fixture_with(INTERFACE, BUILDER, &variant(AGENT, NEG_FORGED.0, NEG_FORGED.1)).query),
        ("counter-reset", fixture_with(INTERFACE, BUILDER, &variant(AGENT, NEG_RESET.0, NEG_RESET.1)).query),
    ];
    let mut rejected = vec![];
    for (name, files) in &negatives {
        let frozen = freeze(&work, name, files);
        let run = run_verus(&toolchain, &frozen, &options(&name.replace('-', "_")), VerusMode::Verify, &work.join(name).join("verus")).unwrap();
        assert!(run.outcome != VerusOutcome::Verified && run.outcome != VerusOutcome::Compiled, "{name} must be rejected");
        rejected.push(serde_json::json!({"variant": name, "outcome": run.outcome, "errors": run.rendered_errors()}));
    }
    evidence.insert("negatives".into(), serde_json::Value::Array(rejected));
    std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", work.join("evidence.json").display());
}

/// The fixture under declared integrity constraints: the fixture DDL followed by `declarations` (one `ALTER TABLE ...
/// ADD ...;` line each, as `dataset_ddl` writes them), written to `work`; the storage is the unconstrained one; the
/// agent is the fixture's with the declared-key lemma appended.
fn declared_fixture(work: &Path, name: &str, declarations: &[&str]) -> Fixture {
    fixture_from(translated_over(&declared_schema(work, name, declarations)), INTERFACE, BUILDER, &format!("{AGENT}{DECLARED_KEY}"), false)
}

/// The fixture DDL followed by `declarations`, written to `<work>/<name>-schema.sql`.
fn declared_schema(work: &Path, name: &str, declarations: &[&str]) -> PathBuf {
    let mut ddl = std::fs::read_to_string(fixtures().join("verus_params/schema.sql")).unwrap();
    for declaration in declarations {
        ddl.push_str(declaration);
        ddl.push('\n');
    }
    let schema = work.join(format!("{name}-schema.sql"));
    std::fs::write(&schema, ddl).unwrap();
    schema
}

/// The fixture under `declarations` with the storage opting in (storage entry v2): its builder requires
/// `source_witnessed` and uses the witnessed-key lemma; the query is the plain fixture agent (entry v5).
fn witnessed_fixture(work: &Path, name: &str, declarations: &[&str]) -> Fixture {
    let builder = format!("{}{WITNESSED_KEY}", variant(&variant(BUILDER, WITNESSED_REQUIRES.0, WITNESSED_REQUIRES.1), WITNESSED_USE.0, WITNESSED_USE.1));
    fixture_from(translated_over(&declared_schema(work, name, declarations)), INTERFACE, &builder, AGENT, true)
}

/// The builder variant of the storage entry v2: it requires the entry's precondition and uses the lemma.
const WITNESSED_REQUIRES: (&str, &str) =
    ("    requires source_wf(src@), in_domain(tables(src@)),\n", "    requires source_wf(src@), in_domain(tables(src@)), source_witnessed(src@),\n");
const WITNESSED_USE: (&str, &str) = (
    "        assert(tables(v)[0] == t);\n",
    "        assert(tables(v)[0] == t);\n        if t.len() >= 2 {\n            lemma_delivered_ids_distinct(v, 0, 1);\n            assert(ids(pv)[0] != ids(pv)[1]);\n        }\n",
);
/// The storage entry v2's precondition of `abi_build_storage`.
const WITNESSED_PRECONDITION: &str = "    requires column_source(columns@) is Some ==> source_witnessed(delivered_source(columns@)),\n";

/// Generation only (no Verus). Under the declarations the opted-in storage crate carries the storage entry v2 and the
/// query crate's `gendb_constraints.rs`; its closure is the unconstrained storage's, byte for byte, so the constrained
/// query crate is the same text over either storage and composes with both by the unchanged rule. Opting in without
/// declarations is refused by name, and an interface that names the declared-constraints module is refused.
#[test]
fn constrained_storage_generates_entry_v2_and_shares_the_closure() {
    let work = scratch("entry-v2-generation");
    let plain = declared_fixture(&work, "plain", &[SITE_KEY, SENSOR_KEY]);
    let witnessed = witnessed_fixture(&work, "witnessed", &[SITE_KEY, SENSOR_KEY]);
    assert_eq!(text(&plain.storage, "gendb_entry.rs"), STORAGE_ENTRY_SOURCE);
    assert!(!plain.storage.iter().any(|f| f.path == "gendb_constraints.rs"), "an unconstrained storage carries no module");
    assert_eq!(text(&witnessed.storage, "gendb_entry.rs"), STORAGE_ENTRY_V2_SOURCE);
    assert_eq!(text(&witnessed.storage, "gendb_constraints.rs"), text(&witnessed.query, "gendb_constraints.rs"));
    assert!(text(&witnessed.storage, "lib.rs").contains("pub mod schema;\npub mod gendb_constraints;\npub mod stores;\n"));
    assert_eq!(storage_closure(&plain.storage, &plain.name), storage_closure(&witnessed.storage, &witnessed.name), "the same closure");
    let framework = |files: &[FrameworkSource]| -> Vec<(String, String)> {
        files.iter().filter(|f| f.path != "agent/mod.rs").map(|f| (f.path.clone(), f.text.clone())).collect()
    };
    let (plain_query, witnessed_query) = (framework(&plain.query), framework(&witnessed.query));
    assert_eq!(plain_query, witnessed_query, "the constrained query crate is the same over either storage");
    for storage in [&plain.storage, &witnessed.storage] {
        assert_eq!(check_storage_composition(storage, &witnessed.query, &witnessed.name), Ok(()));
    }
    // Opting in without declarations: named refusal before any build.
    let (doc, _) = translated();
    let declaration = DeclaredSource::for_storage(&doc.tables, &BTreeMap::from([(1, BTreeSet::from([0, 2, 3]))])).unwrap();
    let refused = storage_crate_files(&doc.tables, &witnessed.name, &declaration, true).unwrap_err();
    assert!(matches!(&refused, AssemblyError::Constraints(m) if m.starts_with("declared_constraints_unavailable: storage sensor_days")), "{refused}");
    assert_eq!(refused.failure_class(), "refusal");
    // An interface naming the module is refused at composition (the central author-source scan) and at freeze.
    let naming = variant(INTERFACE, "pub const BLOCK: usize = 2;", "pub const BLOCK: usize = 2;\n\npub open spec fn declared() -> Schema { crate::gendb_constraints::declared_schema() }");
    let named = fixture_from(translated_over(&work.join("witnessed-schema.sql")), &naming, BUILDER, AGENT, true);
    let refused = check_storage_composition(&named.storage, &named.query, &named.name).unwrap_err();
    assert!(matches!(&refused, CompositionError::SourceRules(x) if x.iter().all(|x| x.rule == rule::INTERFACE_NAMES_DECLARED_CONSTRAINTS)), "{refused:?}");
    match try_freeze(&work, "interface-names-module", &named.storage) {
        Err(FreezeError::Refused { findings }) => assert!(findings.iter().any(|x| x.rule == rule::INTERFACE_NAMES_DECLARED_CONSTRAINTS)),
        other => panic!("expected a refusal, got {other:?}"),
    }
}

#[test]
#[ignore = "runs the pinned Verus toolchain and frontend; cargo test -p gendb-verification --test verus_storage_entry -- --ignored"]
fn storage_entry_v2_uses_the_declared_key_and_needs_it() {
    let work = scratch("entry-v2");
    let toolchain = VerusToolchain::from_env().unwrap();
    let f = witnessed_fixture(&work, "witnessed", &[SITE_KEY, SENSOR_KEY]);
    assert_eq!(text(&f.storage, "gendb_entry.rs"), STORAGE_ENTRY_V2_SOURCE);
    let mut evidence = serde_json::Map::new();
    // Positive: the whole storage crate with the trusted shim, as publication builds it.
    let storage = with_trusted_shim(f.storage.clone(), GENDB_STORAGE_SHIM_SOURCE);
    let frozen = freeze(&work, "storage-v2", &storage);
    let run = run_verus(&toolchain, &frozen, &options(STORAGE_CRATE_NAME), VerusMode::VerifyAndCompile, &work.join("storage-v2").join("verus")).unwrap();
    assert_eq!(run.outcome, VerusOutcome::Compiled, "storage v2: {}", run.rendered_errors());
    let summary = run.verification.clone().unwrap();
    assert!(summary.is_verifying_entire_crate && summary.errors == 0, "{summary:?}");
    evidence.insert("positive".into(), serde_json::json!({"verification": summary, "wall_ns": run.wall_ns, "library": run.artifact}));

    // Negative: the entry's precondition deleted from the positive crate; the builder's requirement is then unmet at the
    // entry's call.
    let mut without_precondition = f.storage.clone();
    let entry = without_precondition.iter_mut().find(|s| s.path == "gendb_entry.rs").unwrap();
    assert_eq!(entry.text.matches(WITNESSED_PRECONDITION).count(), 1);
    entry.text = entry.text.replace(WITNESSED_PRECONDITION, "");
    let name = "without-source-witnessed";
    let frozen = freeze(&work, name, &without_precondition);
    let run = run_verus(&toolchain, &frozen, &options(&name.replace('-', "_")), VerusMode::Verify, &work.join(name).join("verus")).unwrap();
    let errors = run.rendered_errors();
    assert!(run.outcome != VerusOutcome::Verified && run.outcome != VerusOutcome::Compiled, "{name} must be rejected");
    assert!(errors.contains("gendb_entry.rs") && errors.contains("precondition not satisfied"), "{name}: rejected elsewhere: {errors}");
    evidence.insert("negatives".into(), serde_json::json!([{"variant": name, "outcome": run.outcome, "errors": errors}]));
    std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", work.join("evidence.json").display());
}

/// The declared PRIMARY KEY of sensor and one more declaration (a key of site).
const SENSOR_KEY: &str = "ALTER TABLE sensor ADD PRIMARY KEY (id);";
const SITE_KEY: &str = "ALTER TABLE site ADD PRIMARY KEY (region);";
/// The entry v5's constraint conjunct of `bound_db`.
const CONSTRAINT_CONJUNCT: &str = "    &&& constraints_hold(declared_db(db))\n";

#[test]
#[ignore = "runs the pinned Verus toolchain and frontend; cargo test -p gendb-verification --test verus_storage_entry -- --ignored"]
fn query_entry_v5_uses_the_declared_key_and_needs_it() {
    let work = scratch("entry-v5");
    let toolchain = VerusToolchain::from_env().unwrap();
    let f = declared_fixture(&work, "declared", &[SITE_KEY, SENSOR_KEY]);
    // Generation: entry v5 with the generated module; the unconstrained storage composes by the unchanged rule.
    assert_eq!(text(&f.query, "gendb_entry.rs"), QUERY_ENTRY_V5_SOURCE);
    let module = text(&f.query, "gendb_constraints.rs");
    assert!(module.contains("Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }"), "{module}");
    assert_eq!(compare_storage_closure(&f.storage, &f.query, &f.name), Ok(()));
    assert_eq!(check_storage_composition(&f.storage, &f.query, &f.name), Ok(()));
    assert_eq!(text(&f.storage, "schema.rs"), text(&fixture().storage, "schema.rs"), "the column schema is unchanged");

    let mut evidence = serde_json::Map::new();
    let frozen = freeze(&work, "query-v5", &f.query);
    let run = run_verus(&toolchain, &frozen, &options(CANDIDATE_CRATE_NAME), VerusMode::Verify, &work.join("query-v5").join("verus")).unwrap();
    assert_eq!(run.outcome, VerusOutcome::Verified, "query v5: {}", run.rendered_errors());
    let summary = run.verification.clone().unwrap();
    assert!(summary.is_verifying_entire_crate && summary.errors == 0, "{summary:?}");
    evidence.insert("positive".into(), serde_json::json!({"verification": summary, "wall_ns": run.wall_ns}));

    // Negatives: the sensor key removed from the declarations (the site key kept: still entry v5), and the entry's
    // constraint conjunct deleted from the positive crate.
    let without_key = declared_fixture(&work, "without-key", &[SITE_KEY]);
    let (doc, requests) = translated_over(&work.join("without-key-schema.sql"));
    let inst = instantiate(&doc, &declare(&doc, &requests).unwrap()).unwrap();
    assert_eq!(query_entry(&inst), QUERY_ENTRY_V5);
    let mut without_conjunct = f.query.clone();
    let entry = without_conjunct.iter_mut().find(|s| s.path == "gendb_entry.rs").unwrap();
    assert_eq!(entry.text.matches(CONSTRAINT_CONJUNCT).count(), 1);
    entry.text = entry.text.replace(CONSTRAINT_CONJUNCT, "");
    let mut rejected = vec![];
    // Each fails at the declared-key lemma: the declared schema has no sensor key, or the bridge lemma's
    // `constraints_hold` precondition is not available.
    let cases = [
        ("without-declared-key", &without_key.query, "declared_schema()[1].constraints.len() == 1"),
        ("without-entry-conjunct", &without_conjunct, "lemma_primary_key_identifies(d, 1, 0"),
    ];
    for (name, files, failing) in cases {
        let frozen = freeze(&work, name, files);
        let run = run_verus(&toolchain, &frozen, &options(&name.replace('-', "_")), VerusMode::Verify, &work.join(name).join("verus")).unwrap();
        let errors = run.rendered_errors();
        assert!(run.outcome != VerusOutcome::Verified && run.outcome != VerusOutcome::Compiled, "{name} must be rejected");
        assert!(errors.contains("agent/mod.rs") && errors.contains(failing), "{name}: rejected elsewhere: {errors}");
        rejected.push(serde_json::json!({"variant": name, "outcome": run.outcome, "errors": errors}));
    }
    evidence.insert("negatives".into(), serde_json::Value::Array(rejected));
    std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", work.join("evidence.json").display());
}

// Negative variants: (anchor, replacement). Each anchor occurs exactly once in its fixture file.
/// The reader skips a block whose minimum equals `bound - 1` (it holds a qualifying row); its loop invariant says what
/// it computes, so the refusal is the completeness postcondition.
const NEG_READER: (&str, &str) = ("marked.push((mins[b] as i64) < bound);", "marked.push((mins[b] as i64) + 1 < bound);");
const NEG_READER_INVARIANT: (&str, &str) =
    ("#[trigger] marked@[k] == ((mins@[k] as int) < bound),", "#[trigger] marked@[k] == ((mins@[k] as int) + 1 < bound),");
/// The builder records each block's first day as its maximum.
const NEG_ZONES: (&str, &str) = ("        maxs.push(hi);", "        maxs.push(lo);");
/// The query builds its own handle over parts of its choice (the constructor is framework only).
const NEG_FORGED: (&str, &str) =
    ("    let ghost sv = stores@;", "    let _forged = crate::gendb_entry::stored::StoredParts::new(Vec::new(), 0);\n    let ghost sv = stores@;");
/// The query resets the request counters of its handle (the fields are private).
const NEG_RESET: (&str, &str) = ("    let ghost sv = stores@;", "    stores.sensor_days.requests = 0;\n    let ghost sv = stores@;");

/// The derived storage entry (a storage built from admitted storages): storage `sensor_copy` extends `sensor_days`,
/// inheriting all of its parts and adding none, with `sensor_days`'s interface text. Its crate carries the source's
/// closure byte for byte (`check_storage_composition` against the source storage crate), and one pinned Verus
/// `--no-cheating` verify+compile of the whole crate succeeds; a builder that claims a part it does not return fails.
#[test]
#[ignore = "runs the pinned Verus toolchain and frontend; cargo test -p gendb-verification --test verus_storage_entry -- --ignored derived"]
fn derived_storage_entry_verifies_an_extension() {
    let work = scratch("derived-entry");
    let toolchain = VerusToolchain::from_env().unwrap();
    let base = fixture();
    let (doc, _) = translated();
    let declaration = DeclaredSource::for_storage(&doc.tables, &BTreeMap::from([(1, BTreeSet::from([0, 2, 3]))])).unwrap();
    let source_interface = vec![source("stores/sensor_days/interface/mod.rs", INTERFACE)];
    let uses = [StorageUse { name: &base.name, declaration: &declaration, interface: &source_interface }];
    let copy = StorageName::new("sensor_copy").unwrap();
    let assemble = |builder: &str| {
        let mut files = derived_storage_crate_files(&doc.tables, &copy, &declaration, Derivation { sources: &uses, extends: Some(0) }, false).unwrap();
        files.push(source("stores/sensor_copy/interface/mod.rs", INTERFACE));
        files.push(source("builder/mod.rs", builder));
        with_trusted_shim(files, gendb_runtime::abi::GENDB_STORAGE_DERIVED_SHIM_SOURCE)
    };
    let derived = assemble(DERIVED_BUILDER);
    check_storage_composition(&base.storage, &derived, &base.name).unwrap();
    assert!(text(&derived, "gendb_entry/derivation.rs").contains("    sv.sensor_days\n"));
    assert!(derived_storage_crate_files(&doc.tables, &base.name, &declaration, Derivation { sources: &uses, extends: None }, false).is_err(), "own name");

    let frozen = freeze(&work, "derived", &derived);
    let run = run_verus(&toolchain, &frozen, &options(STORAGE_CRATE_NAME), VerusMode::VerifyAndCompile, &work.join("derived/verus-build")).unwrap();
    assert_eq!(run.outcome, VerusOutcome::Compiled, "{}", run.rendered_errors());

    let lying = assemble(&variant(DERIVED_BUILDER, "let parts: Vec<OwnedPart> = Vec::new();", "let mut parts: Vec<OwnedPart> = Vec::new();\n    parts.push(OwnedPart::U8(Vec::new()));"));
    let frozen = freeze(&work, "derived-lying", &lying);
    let run = run_verus(&toolchain, &frozen, &options(STORAGE_CRATE_NAME), VerusMode::Verify, &work.join("derived-lying/verus")).unwrap();
    assert!(run.outcome != VerusOutcome::Verified && run.outcome != VerusOutcome::Compiled, "an extra part breaks the claimed representation");
}
