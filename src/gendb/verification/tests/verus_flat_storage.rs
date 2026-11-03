//! The generated flat storages (`storage_policy` `fixed_flat`, `obligations::flat_storage`).
//!
//! Generation (no Verus): the flat storage of the TPC-H `lineitem` table (bigint, numeric(15,2), text and date
//! columns: every flat element kind) has one part per column and two per text column, in column order, is generated
//! identically from its declaration, and its author files pass the source rules; a nullable column has one more part,
//! its validity. The TPC-H schema's flat storage crates, engine crate and a derived crate assemble byte for byte as
//! before nullable columns were supported.
//!
//! Proof (`--ignored`, pinned Verus): that storage crate, assembled by the one storage-crate assembly with the
//! generated interface and builder, verifies and compiles whole with `--no-cheating` against the fixed storage entry v1.
//! It is the representative check of the generator; preparation checks every table's crate once, the same way. The
//! flat storage of a table with a nullable column of every type (`verus_flat/nullable_schema.sql`, its crate with the
//! nullable source module, binder and shim) verifies and compiles whole too.
use gendb_frontend::ast::{AstDocument, Translation};
use gendb_frontend::parser::SqlParser;
use gendb_verification::obligations::{flat_storage, flat_storage_of, FlatBuffer, FlatElem, STORAGE_CRATE_NAME};
use gendb_verification::verus::{
    freeze_framework_crate, run_verus, CodegenOptions, FrameworkSource, FrozenCrate, VerusMode, VerusOptions, VerusOutcome, VerusToolchain,
};
use std::path::{Path, PathBuf};

fn fixtures() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

fn scratch(name: &str) -> PathBuf {
    let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let d = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("verus-flat-{name}-{}-{nanos}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

/// The schema of `ddl` (a trivial statement over it, translated by the pinned frontend).
fn schema(ddl: &Path, sql: &str) -> AstDocument {
    let work = scratch("schema");
    let query = work.join("query.sql");
    std::fs::write(&query, sql).unwrap();
    let parser = SqlParser::from_environment().unwrap();
    let (_, t) = parser.translate(ddl, &query, "postgres", &[]).unwrap();
    let Translation::Ok(doc) = t else { panic!("fixture SQL refused: {t:?}") };
    doc
}

fn lineitem() -> AstDocument {
    schema(&fixtures().join("verus_flat/schema.sql"), "SELECT l_orderkey FROM lineitem")
}

/// The schema with a nullable column of every type (table 0 `filing`), a nullable text column (`line`) and a table of
/// NOT NULL columns (`unit`).
fn nullable_schema() -> AstDocument {
    schema(&fixtures().join("verus_flat/nullable_schema.sql"), "SELECT id FROM filing")
}

/// Every file of the flat storage crate of table `table` of `doc`, with its trusted shim (the nullable one when the
/// table has a nullable column).
fn crate_files(doc: &AstDocument, table: usize) -> Vec<FrameworkSource> {
    let flat = flat_storage(&doc.tables, table).unwrap();
    let mut files = gendb_verification::admission::storage::candidate_framework_files(&doc.tables, &flat.name, &flat.declaration, false, None).unwrap();
    files.extend(flat.files);
    files
}

/// Freeze with the author files (`builder/**`, `stores/*/interface/**`) scanned by the source rules.
fn freeze(work: &Path, files: &[FrameworkSource]) -> FrozenCrate {
    let unscanned: Vec<&str> = files.iter().filter(|f| gendb_registry::author_definition(&f.path).is_none()).map(|f| f.path.as_str()).collect();
    freeze_framework_crate(files, &unscanned, &work.join("frozen")).unwrap_or_else(|e| panic!("{e:?}"))
}

#[test]
fn flat_storage_generates_one_plain_part_per_column_and_a_validity_part_per_nullable_column() {
    let doc = lineitem();
    let flat = flat_storage(&doc.tables, 0).unwrap();
    assert_eq!(flat.name.as_str(), "flat_lineitem");
    assert_eq!(flat.parts.len(), 16 + 5, "one part per column, two per text column");
    let shipdate = flat.parts.iter().position(|p| p.constant == "L_SHIPDATE").unwrap();
    assert_eq!((flat.parts[shipdate].ordinal, flat.parts[shipdate].elem), (10, FlatElem::I32));
    let quantity = flat.parts.iter().find(|p| p.column == "l_quantity").unwrap();
    assert_eq!((quantity.elem, quantity.buffer), (FlatElem::I128, FlatBuffer::Values));
    let comment: Vec<_> = flat.parts.iter().filter(|p| p.column == "l_comment").map(|p| (p.constant.as_str(), p.elem)).collect();
    assert_eq!(comment, [("L_COMMENT_OFFSETS", FlatElem::I64), ("L_COMMENT_BYTES", FlatElem::U8)]);
    assert!(flat.parts.windows(2).all(|w| w[0].ordinal <= w[1].ordinal), "column order");
    let again = flat_storage_of(&flat.declaration).unwrap();
    let texts = |files: &[FrameworkSource]| files.iter().map(|f| (f.path.clone(), f.text.clone())).collect::<Vec<_>>();
    assert_eq!(texts(&again.files), texts(&flat.files), "deterministic from the declaration");
    freeze(&scratch("rules"), &crate_files(&doc, 0));

    let sensor = schema(&fixtures().join("verus_params/schema.sql"), "SELECT id FROM sensor");
    let with_note = flat_storage(&sensor.tables, 1).unwrap();
    let parts: Vec<_> = with_note.parts.iter().map(|p| (p.constant.as_str(), p.buffer, p.elem)).collect();
    assert_eq!(parts[parts.len() - 3..], [("NOTE_OFFSETS", FlatBuffer::Offsets, FlatElem::I64), ("NOTE_BYTES", FlatBuffer::Bytes, FlatElem::U8), ("NOTE_VALIDITY", FlatBuffer::Validity, FlatElem::U8)]);
    assert_eq!(parts.len(), 1 + 1 + 1 + 1 + 2 + 3, "sensor: four fixed-width columns, varchar(8), nullable text with its validity");
    let interface = &with_note.files[0].text;
    for item in ["pub fn read_note_validity(", "pub open spec fn note_value(parts: Seq<PartView>, i: int) -> Val {\n    if u8s(parts[NOTE_VALIDITY as int])[i] == 0 { Val::Null } else {",
        "rels[0][i as int][5] is Null || rels[0][i as int][5] == Val::Text(r@)"] {
        assert!(interface.contains(item), "{item}\n{interface}");
    }
    assert!(!flat.files[0].text.contains("Null") && !flat.files[0].text.contains("VALIDITY"), "a NOT NULL table states no validity");
    freeze(&scratch("nullable-rules"), &crate_files(&sensor, 1));
    assert_eq!(flat_storage(&sensor.tables, 0).unwrap().parts.len(), 3, "site: char(3) offsets and bytes, integer");
}

#[test]
#[ignore = "runs the pinned Verus toolchain and frontend; cargo test -p gendb-verification --test verus_flat_storage -- --ignored"]
fn flat_lineitem_storage_crate_verifies_and_compiles_whole() {
    let work = scratch("verify");
    let toolchain = VerusToolchain::from_env().unwrap();
    let frozen = freeze(&work, &crate_files(&lineitem(), 0));
    let options = VerusOptions { crate_name: STORAGE_CRATE_NAME.into(), codegen: CodegenOptions { opt_level: 1, target_cpu: None }, num_threads: Some(8) };
    let run = run_verus(&toolchain, &frozen, &options, VerusMode::VerifyAndCompile, &work.join("verus-build")).unwrap();
    assert_eq!(run.outcome, VerusOutcome::Compiled, "{}", run.rendered_errors());
    let summary = run.verification.clone().unwrap();
    assert!(summary.is_verifying_entire_crate && summary.errors == 0, "{summary:?}");
    let evidence = serde_json::json!({"verification": summary, "wall_ns": run.wall_ns, "library": run.artifact, "frozen": frozen.root});
    std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", work.join("evidence.json").display());
}

/// SHA-256 of files in order (each path, a zero byte, the text's length and the text).
fn files_digest(files: &[FrameworkSource]) -> String {
    use sha2::{Digest, Sha256};
    let mut hash = Sha256::new();
    for f in files {
        hash.update(f.path.as_bytes());
        hash.update([0u8]);
        hash.update((f.text.len() as u64).to_le_bytes());
        hash.update(f.text.as_bytes());
    }
    hash.finalize().iter().map(|b| format!("{b:02x}")).collect()
}

/// The TPC-H runs' schema (every column NOT NULL, the declared keys): every generated flat storage crate (framework files
/// with the storage shim, interface and builder), the engine crate over all of them with version 0, and a storage crate
/// built from a flat source (`sources_flat`) assemble byte for byte as before nullable source columns were supported
/// (digests recorded by running this test on the unchanged generators). So every admitted TPC-H flat package,
/// asset and engine version stays current.
#[test]
fn tpch_flat_crates_assemble_as_before_nullable_columns() {
    use gendb_verification::admission::storage::candidate_framework_files;
    use gendb_verification::obligations::{derived_storage_crate_files, engine_crate_files, interpreter_engine, Derivation, StorageName, StorageUse};
    let doc = schema(&fixtures().join("verus_flat/tpch_constrained.sql"), "SELECT r_regionkey FROM region");
    let tables = &doc.tables;
    let flats: Vec<_> = (0..tables.len()).map(|t| flat_storage(tables, t).unwrap()).collect();
    let interfaces: Vec<Vec<FrameworkSource>> =
        flats.iter().map(|f| f.files.iter().filter(|x| x.path.starts_with(&f.name.interface_prefix())).cloned().collect()).collect();
    let uses: Vec<StorageUse<'_>> =
        flats.iter().zip(&interfaces).map(|(f, i)| StorageUse { name: &f.name, declaration: &f.declaration, interface: i }).collect();
    let mut digests = vec![];
    for flat in &flats {
        let mut files = candidate_framework_files(tables, &flat.name, &flat.declaration, false, None).unwrap();
        files.extend(flat.files.iter().cloned());
        digests.push((flat.name.to_string(), files_digest(&files)));
    }
    let mut engine = engine_crate_files(tables, &uses, "tpch").unwrap();
    engine.extend(interpreter_engine(tables, &uses).unwrap());
    digests.push(("engine".into(), files_digest(&engine)));
    let copy = StorageName::new("lineitem_copy").unwrap();
    let derived = derived_storage_crate_files(tables, &copy, &flats[0].declaration, Derivation { sources: &uses[..1], extends: Some(0) }, true).unwrap();
    digests.push(("derived".into(), files_digest(&derived)));
    let rendered: Vec<String> = digests.iter().map(|(name, digest)| format!("{name} {digest}")).collect();
    eprintln!("{}", rendered.join("\n"));
    assert_eq!(rendered.join("\n"), TPCH_FLAT_CRATE_DIGESTS.trim());
}

/// `<crate> <files digest>` per TPC-H flat storage, the engine crate and the derived storage crate (see the test above).
const TPCH_FLAT_CRATE_DIGESTS: &str = "
flat_lineitem cc292a04404b9b9dd09cc4957b26fabaae7c0459977636abda9117bd4172026c
flat_orders 41e0a4db85a5b231d8f8a20d5042673de91615e24eea9a98da840963add9fc4b
flat_customer edd460c869dbce652cecd891e7ff88f10e951103f56792013e704c0928c2a358
flat_part 3f1f7e4e142323f8038d0d2ef3f9410ba510fb345edca5483b3c1a31773e8a7c
flat_partsupp 2bb74f70f771cdec878fcac5927dc5b9de9e66ef33b570bf5d7066bb5b62cc36
flat_supplier d4ed7dc496b3de7d6f214ed291e63906dad025a8ffc2a745afa8684a388149b2
flat_nation 5675f81d9e6cfe6ee7487551fe4e6820acb4d91718b5ba68c28020b8bd72b0d1
flat_region a3d6c79018102b321a8eabb07869ecd48f95233200c5bffbd2566f07940fbbe7
engine 6511970e6eb9c9163a8765fce5a7d63ef267022f8f55ee0e5149591b2eb3ab8d
derived 3dc7e16349285e07936af6f15f1b8548a2ec74d768fc3989ff0d43d47110c3ad
";

/// The flat storage crate of `filing` (a nullable integer, bigint, numeric, date, text, varchar and char column, and NOT
/// NULL integer and text columns) verifies and compiles whole with `--no-cheating`: its source module with validity
/// fields and exact nullable domain decisions, its binder of validity columns, its declaration, and the generated
/// interface (validity parts, `Val::Null` rows, validity readers) and builder. Its shim is the nullable one.
#[test]
#[ignore = "runs the pinned Verus toolchain and frontend; cargo test -p gendb-verification --test verus_flat_storage -- --ignored"]
fn nullable_flat_storage_crate_verifies_and_compiles_whole() {
    let work = scratch("verify-nullable");
    let toolchain = VerusToolchain::from_env().unwrap();
    let files = crate_files(&nullable_schema(), 0);
    let shim = files.iter().find(|f| f.path == "gendb_shim.rs").unwrap();
    assert_eq!(shim.text, gendb_runtime::abi::GENDB_STORAGE_NULLABLE_SHIM_SOURCE);
    let frozen = freeze(&work, &files);
    let options = VerusOptions { crate_name: STORAGE_CRATE_NAME.into(), codegen: CodegenOptions { opt_level: 1, target_cpu: None }, num_threads: Some(8) };
    let run = run_verus(&toolchain, &frozen, &options, VerusMode::VerifyAndCompile, &work.join("verus-build")).unwrap();
    assert_eq!(run.outcome, VerusOutcome::Compiled, "{}", run.rendered_errors());
    let summary = run.verification.clone().unwrap();
    assert!(summary.is_verifying_entire_crate && summary.errors == 0, "{summary:?}");
    let evidence = serde_json::json!({"verification": summary, "wall_ns": run.wall_ns, "library": run.artifact, "frozen": frozen.root});
    std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", work.join("evidence.json").display());
}

/// The compiled nullable flat storage `flat_filing` builds through the worker child from inline columns with validity
/// (the tiny-case path: worker inline columns -> nullable shim -> verified binder, exact domain decision -> builder):
/// every value and validity buffer is a part, byte for byte, and a NUL byte under a NULL text row is accepted (the
/// domain is decided for valid rows only), while the same byte in a valid row is `InvalidInput`.
#[test]
#[ignore = "runs the pinned Verus, the frontend and the gendb worker; set GENDB_WORKER; -- --ignored"]
fn nullable_flat_storage_builds_through_the_worker() {
    use gendb_runtime::abi::CallStatus;
    use gendb_runtime::worker::{spawn, InlineColumn, InlineElem, WorkerInput, WorkerRequest};
    let worker = PathBuf::from(std::env::var_os("GENDB_WORKER").expect("GENDB_WORKER: the gendb executable"));
    let work = scratch("nullable-build");
    let toolchain = VerusToolchain::from_env().unwrap();
    let doc = nullable_schema();
    let flat = flat_storage(&doc.tables, 0).unwrap();
    let frozen = freeze(&work, &crate_files(&doc, 0));
    let options = VerusOptions { crate_name: STORAGE_CRATE_NAME.into(), codegen: CodegenOptions { opt_level: 1, target_cpu: None }, num_threads: Some(8) };
    let run = run_verus(&toolchain, &frozen, &options, VerusMode::VerifyAndCompile, &work.join("verus-build")).unwrap();
    assert_eq!(run.outcome, VerusOutcome::Compiled, "{}", run.rendered_errors());
    let library = run.artifact.clone().unwrap();

    let column = |elem, values: &[&str], validity: Option<&[u8]>| InlineColumn {
        elem,
        values: values.iter().map(|v| v.to_string()).collect(),
        validity: validity.map(<[u8]>::to_vec),
    };
    // A NUL byte under the NULL row of `label` (its value bytes mean nothing).
    let input = |label_validity: &[u8]| WorkerInput::Inline {
        columns: vec![
            column(InlineElem::I32, &["1", "2", "3"], None),
            column(InlineElem::I32, &["2022", "0", "-7"], Some(&[1, 0, 1])),
            column(InlineElem::I64, &["9000000000", "0", "0"], Some(&[1, 0, 0])),
            column(InlineElem::I128, &["125000", "0", "-1"], Some(&[1, 0, 1])),
            column(InlineElem::I32, &["19023", "0", "10956"], Some(&[1, 0, 1])),
            column(InlineElem::Utf8, &["λ label", "\u{0}junk", ""], Some(label_validity)),
            column(InlineElem::Utf8, &["ab", "", ""], Some(&[1, 0, 0])),
            column(InlineElem::Utf8, &["x", "", "y"], Some(&[1, 0, 1])),
            column(InlineElem::Utf8, &["first", "second", "third"], None),
        ],
    };
    let parts = work.join("asset");
    let build = WorkerRequest::for_storage_build(&library, input(&[1, 0, 1]), &parts, 1, 64);
    let built = spawn(&worker, &work.join("build"), &build, 600).unwrap();
    assert_eq!(built.observations[0].outcome.status, CallStatus::Ok, "{:?}", built.observations[0]);
    let manifest = built.parts.clone().expect("committed parts");
    assert_eq!(manifest.parts.len(), flat.parts.len());
    let part = |constant: &str| {
        let index = flat.parts.iter().position(|p| p.constant == constant).unwrap();
        std::fs::read(parts.join(format!("part-{index:04}.bin"))).unwrap()
    };
    for (constant, validity) in [("FY_VALIDITY", [1u8, 0, 1]), ("BIG_VALIDITY", [1, 0, 0]), ("LABEL_VALIDITY", [1, 0, 1]), ("CODE_VALIDITY", [1, 0, 0])] {
        assert_eq!(part(constant), validity, "{constant}");
    }
    assert_eq!(part("FY"), [2022i32, 0, -7].iter().flat_map(|x| x.to_le_bytes()).collect::<Vec<u8>>());
    assert_eq!(part("LABEL_BYTES"), "λ label\u{0}junk".as_bytes());

    // The same NUL byte in a valid row is outside text's domain: the verified decision answers InvalidInput.
    let refused = WorkerRequest::for_storage_build(&library, input(&[1, 1, 1]), &work.join("refused-asset"), 1, 64);
    let refused = spawn(&worker, &work.join("refused"), &refused, 600).unwrap();
    assert_eq!(refused.observations[0].outcome.status, CallStatus::InvalidInput);
    let evidence = serde_json::json!({"verification": run.verification, "parts": manifest.parts.len(), "storage_bytes": manifest.storage_bytes});
    std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&evidence).unwrap()).unwrap();
    eprintln!("evidence: {}", work.join("evidence.json").display());
}

/// The mapped-capture path a workload storage takes on its first build (no Verus): each admitted flat storage of a
/// prepared library (`GENDB_NULLABLE_LIBRARY`, from `gendb prepare-flat-storage` over a schema with nullable columns)
/// builds through the worker child from the prepared capture (`GENDB_NULLABLE_CAPTURE`: `WorkerInput::Tables`, the
/// mapped column files with their validity, the nullable shim, the verified binder and domain decision, the builder),
/// and every part it returns equals the capture's column file the flat asset links for that part, byte for byte (so
/// every `<COLUMN>_VALIDITY` part is the capture's validity file).
#[test]
#[ignore = "builds compiled flat storages of a prepared library through the gendb worker; set GENDB_WORKER, GENDB_NULLABLE_LIBRARY, GENDB_NULLABLE_CAPTURE; -- --ignored"]
fn nullable_flat_storages_build_from_the_mapped_capture() {
    use gendb_artifacts::verus as records;
    use gendb_artifacts::ObjectStore;
    use gendb_runtime::abi::CallStatus;
    use gendb_runtime::worker::{spawn, TableColumns, WorkerInput, WorkerRequest};
    use gendb_storage::io::SourceColumns;
    use gendb_verification::obligations::DeclaredSource;
    let path = |name: &str| PathBuf::from(std::env::var_os(name).unwrap_or_else(|| panic!("{name}")));
    let (worker, library, archive) = (path("GENDB_WORKER"), path("GENDB_NULLABLE_LIBRARY"), path("GENDB_NULLABLE_CAPTURE"));
    let work = scratch("mapped-capture-build");
    let store = ObjectStore::open(&library).unwrap();
    let captured = SourceColumns::captured_columns(&archive).unwrap();
    let mut checked = vec![];
    for (_, package) in records::current_storages(&store).unwrap() {
        let declaration: DeclaredSource = serde_json::from_value(package.declaration.clone()).unwrap();
        let flat = flat_storage_of(&declaration).unwrap();
        let build = records::storage_build(&store, &package).unwrap();
        let compiled = records::library_path(&store, &build).unwrap();
        let ordinals = declaration.tables[0].columns.iter().map(|c| c.ordinal).collect();
        let input = WorkerInput::Tables { path: archive.clone(), tables: vec![TableColumns { table: flat.table.clone(), ordinals }] };
        let parts = work.join(flat.name.as_str());
        let request = WorkerRequest::for_storage_build(&compiled, input, &parts, 1, 64);
        let built = spawn(&worker, &work.join(format!("{}-child", flat.name)), &request, 600).unwrap();
        assert_eq!(built.observations[0].outcome.status, CallStatus::Ok, "{}: {:?}", flat.name, built.observations[0]);
        assert_eq!(built.parts.as_ref().expect("committed parts").parts.len(), flat.parts.len(), "{}", flat.name);
        for (index, part) in flat.parts.iter().enumerate() {
            let column = captured.iter().find(|c| c.table == flat.table && c.ordinal == part.ordinal).unwrap();
            let file = match part.buffer {
                FlatBuffer::Values => &column.values,
                FlatBuffer::Offsets => &column.offsets,
                FlatBuffer::Bytes => &column.bytes,
                FlatBuffer::Validity => &column.validity,
            };
            let expected = std::fs::read(&file.as_ref().unwrap().path).unwrap();
            let actual = std::fs::read(parts.join(format!("part-{index:04}.bin"))).unwrap();
            assert!(actual == expected, "{} part {index} {}: differs from the capture's file", flat.name, part.constant);
        }
        let validity = flat.parts.iter().filter(|p| p.buffer == FlatBuffer::Validity).count();
        checked.push(serde_json::json!({"storage": flat.name.as_str(), "parts": flat.parts.len(), "validity_parts": validity}));
        eprintln!("{}: {} parts ({validity} validity) equal to the capture's files", flat.name, flat.parts.len());
    }
    assert!(checked.iter().any(|c| c["validity_parts"].as_u64() > Some(0)), "some storage has a nullable column");
    std::fs::write(work.join("evidence.json"), serde_json::to_vec_pretty(&serde_json::json!({"library": library, "capture": archive, "storages": checked})).unwrap()).unwrap();
    eprintln!("evidence: {}", work.join("evidence.json").display());
}

/// Write the generated flat storage files of every table of the DDL `GENDB_RENDER_FLAT_DDL` under
/// `GENDB_RENDER_FLAT_DIR/<storage>/` for review (generation only: no Verus, no data).
#[test]
#[ignore = "renders the flat storages of a DDL for review: GENDB_RENDER_FLAT_DDL, GENDB_RENDER_FLAT_DIR; -- --ignored"]
fn render_flat_storages_for_review() {
    let ddl = PathBuf::from(std::env::var("GENDB_RENDER_FLAT_DDL").expect("GENDB_RENDER_FLAT_DDL"));
    let out = PathBuf::from(std::env::var("GENDB_RENDER_FLAT_DIR").expect("GENDB_RENDER_FLAT_DIR"));
    let doc = schema(&ddl, "SELECT r_regionkey FROM region");
    for table_id in 0..doc.tables.len() {
        let flat = flat_storage(&doc.tables, table_id).unwrap();
        for file in &flat.files {
            let path = out.join(flat.name.as_str()).join(&file.path);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(&path, &file.text).unwrap();
        }
    }
}
