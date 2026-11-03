//! Record rules of storage packages, stored assets in the library and query packages over stored data (entry v4, and
//! entry v5 under declared integrity constraints), on fixture build records (no Verus run: the build output is a
//! fixture JSON reporting a complete verification).

mod common;

use gendb_artifacts::verus::*;
use gendb_artifacts::{ContentId, ObjectStore};
use std::collections::{BTreeMap, BTreeSet};
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::path::{Path, PathBuf};

const COMPLETE: &str = "{\"verification-results\":{\"success\":true,\"verified\":12,\"errors\":0,\"is-verifying-entire-crate\":true,\"encountered-error\":false,\"encountered-vir-error\":false}}";
const STORAGE_ENTRY: &str = "// FRAMEWORK FILE: the fixed storage entry (identity `gendb-verus-storage-entry-v1`)\npub proof fn theorem_storage_built() {}\npub proof fn theorem_storage_build_total() {}\n";
const STORAGE_ENTRY_V2: &str = "// FRAMEWORK FILE: the fixed storage entry v2 (identity `gendb-verus-storage-entry-v2`)\npub proof fn theorem_storage_built() {}\npub proof fn theorem_storage_build_total() {}\n";
const QUERY_ENTRY: &str = "// FRAMEWORK FILE: the fixed query entry v4 (identity `gendb-verus-entry-v4`)\npub proof fn theorem_end_to_end() {}\npub proof fn corollary_inside_capacity() {}\n";
const QUERY_ENTRY_V5: &str = "// FRAMEWORK FILE: the fixed query entry v5 (identity `gendb-verus-entry-v5`)\npub proof fn theorem_end_to_end() {}\npub proof fn corollary_inside_capacity() {}\n";
const QUERY_RS: &str = "//! SELECT x FROM t WHERE x < $1\nuse crate::schema::schema_spec;\nMEANING x < ps[0]\n";

/// The shared closure files of storage `s` (library, schema, declaration, interface) and their fixture texts.
fn shared(interface: &str, schema: &str) -> Vec<(String, String)> {
    [
        ("spec/value.rs", "SPEC"),
        ("gendb_abi.rs", "ABI4"),
        ("gendb_entry/stored.rs", "STORED"),
        ("schema.rs", schema),
        ("stores/s/mod.rs", "pub mod declaration;\npub mod interface;\n"),
        ("stores/s/declaration.rs", "DECLARATION t: 0, 2"),
        ("stores/s/interface/mod.rs", interface),
    ]
    .into_iter()
    .map(|(p, t)| (p.to_string(), t.to_string()))
    .collect()
}

struct Crate {
    root: PathBuf,
    /// `(path, text, owner)`.
    files: Vec<(String, String, VerusSourceOwnerV1)>,
}

impl Crate {
    fn write(dir: &Path, files: Vec<(String, String, VerusSourceOwnerV1)>) -> Crate {
        for (path, text, _) in &files {
            let file = dir.join("src").join(path);
            std::fs::create_dir_all(file.parent().unwrap()).unwrap();
            std::fs::write(file, text).unwrap();
        }
        std::fs::write(dir.join("lib.so"), b"\x7fELF-fixture").unwrap();
        Crate { root: dir.to_owned(), files }
    }

    fn framework(&self) -> Vec<(&str, &str)> {
        self.files.iter().filter(|f| f.2 == VerusSourceOwnerV1::Framework).map(|f| (f.0.as_str(), f.1.as_str())).collect()
    }

    fn publish(&self, store: &ObjectStore, provider: &str, argv_extra: &[&str], tcb: ContentId) -> ContentId {
        let mut argv: Vec<String> = ["lib.rs", "--edition=2021", "--no-cheating", "--output-json", "--compile", "-o", "/x/lib.so"].map(String::from).to_vec();
        argv.extend(argv_extra.iter().map(|a| a.to_string()));
        publish_build(store, VerusBuildInput {
            purpose: VerusBuildPurposeV1::Candidate,
            provider_identity: provider.into(),
            argv,
            environment: BTreeMap::from([("VSTD_KIND".into(), "Imported".into()), ("TMPDIR".into(), self.root.display().to_string())]),
            exit_code: Some(0),
            stdout: COMPLETE,
            frozen_directory: &self.root,
            sources: self.files.iter().map(|f| (f.0.clone(), f.2)).collect(),
            library_path: &self.root.join("lib.so"),
            wall_ns: 1,
            tcb,
        })
        .unwrap()
    }
}

fn framework(files: Vec<(String, String)>) -> Vec<(String, String, VerusSourceOwnerV1)> {
    files.into_iter().map(|(p, t)| (p, t, VerusSourceOwnerV1::Framework)).collect()
}

fn storage_crate(dir: &Path, interface: &str) -> Crate {
    storage_crate_with(dir, interface, STORAGE_ENTRY, None)
}

/// A storage crate with the entry text `entry` and, when `constraints` is given, a framework `gendb_constraints.rs`.
fn storage_crate_with(dir: &Path, interface: &str, entry: &str, constraints: Option<&str>) -> Crate {
    let mut files = framework(shared(interface, "SCHEMA"));
    files.extend(framework(vec![("lib.rs".into(), "STORAGE ROOT".into()), ("gendb_entry.rs".into(), entry.into())]));
    files.extend(framework(constraints.map(|text| ("gendb_constraints.rs".to_string(), text.to_string())).into_iter().collect()));
    // The interface is the author's in the storage crate; the builder too.
    for f in files.iter_mut().filter(|f| f.0.starts_with("stores/s/interface/")) {
        f.2 = VerusSourceOwnerV1::Agent;
    }
    files.push(("builder/mod.rs".into(), "BUILDER".into(), VerusSourceOwnerV1::Agent));
    Crate::write(dir, files)
}

fn query_crate(dir: &Path, shared_files: Vec<(String, String)>) -> Crate {
    query_crate_with(dir, shared_files, QUERY_ENTRY, None)
}

/// A query crate with the entry text `entry` and, when `constraints` is given, a framework `gendb_constraints.rs`.
fn query_crate_with(dir: &Path, shared_files: Vec<(String, String)>, entry: &str, constraints: Option<&str>) -> Crate {
    let mut files = framework(shared_files);
    files.extend(framework(vec![
        ("lib.rs".into(), "QUERY ROOT".into()),
        ("gendb_entry.rs".into(), entry.into()),
        ("query.rs".into(), QUERY_RS.into()),
    ]));
    files.extend(framework(constraints.map(|text| ("gendb_constraints.rs".to_string(), text.to_string())).into_iter().collect()));
    files.push(("agent/mod.rs".into(), "AGENT".into(), VerusSourceOwnerV1::Agent));
    Crate::write(dir, files)
}

fn storage_package(store: &ObjectStore, build: ContentId, tcb: ContentId) -> VerusStoragePackageV1 {
    let build_record: VerusBuildV1 = store.read(build).unwrap().decode().unwrap();
    let closure = build_record
        .sources
        .iter()
        .filter(|s| !s.path.starts_with("builder/") && !["lib.rs", "gendb_entry.rs", "gendb_constraints.rs"].contains(&s.path.as_str()))
        .map(|s| VerusClosureFileV1 { path: s.path.clone(), blob: s.blob, bytes: s.bytes })
        .collect();
    VerusStoragePackageV1 {
        name: "s".into(),
        build,
        entry_identity: VERUS_STORAGE_ENTRY_V1_IDENTITY.into(),
        assumed_constraints: None,
        tables: vec![VerusStoredTableV1 { table: "t".into(), table_id: 0, ordinals: vec![0, 2] }],
        declaration: serde_json::json!({"tables": []}),
        schema_ddl: store.put_blob(b"CREATE TABLE t (x integer NOT NULL, y integer NOT NULL, z integer NOT NULL);").unwrap(),
        frontend: serde_json::json!({"identity": "fixture"}),
        closure,
        configuration: build_record.check_configuration().unwrap(),
        readers: vec![],
        theorems: vec!["gendb_entry::theorem_storage_built".into(), "gendb_entry::theorem_storage_build_total".into()],
        workers: (1, 64),
        tcb,
        derived_from: None,
    }
}

fn staged_parts(store: &ObjectStore, lock: &StorageAssetLock) -> PathBuf {
    let staged = store.fresh_asset_staging_directory(lock.asset_name()).unwrap();
    std::fs::create_dir(&staged).unwrap();
    std::fs::write(staged.join("part-0000.bin"), [0u8; 12]).unwrap();
    std::fs::write(staged.join("parts.json"), br#"{"format_version":2,"byte_order":"little","parts":[["i32",3]],"storage_bytes":12}"#).unwrap();
    staged
}

fn built() -> BuiltParts {
    BuiltParts { format_version: 2, byte_order: "little".into(), parts: vec![("i32".into(), 3)], storage_bytes: 12 }
}

fn key(package: ContentId, source_version: &str, row_order: &str) -> VerusStorageAssetKeyV1 {
    VerusStorageAssetKeyV1 {
        storage_package: package,
        tables: vec![VerusStorageAssetTableV1 { table: "t".into(), source_version: source_version.into(), row_order: row_order.into(), rows: 3 }],
    }
}

/// A storage package is published only when it is its build's (framework files, author roots, closure,
/// configuration); it is admitted once per version; its asset is placed in the library under a relative path, once
/// per key, and is found only for the same source version and row order.
#[test]
fn storage_packages_and_library_assets() {
    let dir = common::scratch_dir("storage-records");
    let store = ObjectStore::open(dir.join("library")).unwrap();
    let tcb = store.put(1, VERUS_TCB_KIND, &VerusTcbV1 { items: vec![], refusal_rules: serde_json::json!([]) }).unwrap();
    let storage = storage_crate(&dir.join("storage"), "INTERFACE v1");
    let build = storage.publish(&store, "pinned", &[], tcb);
    let package = storage_package(&store, build, tcb);
    let refusal = |p: &VerusStoragePackageV1, framework: &[(&str, &str)]| publish_storage_package(&store, p, framework).unwrap_err().to_string();

    let mut stale = storage.framework();
    stale[0].1 = "OTHER SPEC";
    assert!(refusal(&package, &stale).contains("differs from the framework generation"));
    let mut foreign = package.clone();
    foreign.closure.push(VerusClosureFileV1 { path: "builder/mod.rs".into(), ..foreign.closure[0].clone() });
    assert!(refusal(&foreign, &storage.framework()).contains("not a stored, shared file"));
    let mut no_interface = package.clone();
    no_interface.closure.retain(|f| !f.path.contains("/interface/"));
    assert!(refusal(&no_interface, &storage.framework()).contains("lacks stores/s/interface/mod.rs"));
    let mut other_configuration = package.clone();
    other_configuration.configuration.provider_identity = "another toolchain".into();
    assert!(refusal(&other_configuration, &storage.framework()).contains("configuration"));
    let with_cfg = storage.publish(&store, "pinned", &["--cfg", "x"], tcb);
    let cfg_build: VerusBuildV1 = store.read(with_cfg).unwrap().decode().unwrap();
    assert!(cfg_build.check_configuration().unwrap_err().to_string().contains("unsupported option --cfg"));

    let package_id = publish_storage_package(&store, &package, &storage.framework()).unwrap();
    let evidence = store.put(1, "fixture-storage-checks", &true).unwrap();
    assert!(admit_storage_package(&store, &VerusStorageAdmissionV1 { package: package_id, gate_identity: "g".into(), evidence: vec![] }).is_err());
    assert!(resolve_admitted_storage(&store, package_id).is_err(), "published is not admitted");
    let admission = VerusStorageAdmissionV1 { package: package_id, gate_identity: "g".into(), evidence: vec![evidence] };
    admit_storage_package(&store, &admission).unwrap();
    assert!(admit_storage_package(&store, &admission).is_err(), "admitted once");
    assert_eq!(resolve_admitted_storage(&store, package_id).unwrap().name, "s");
    assert_eq!(current_storages(&store).unwrap().into_iter().map(|(id, _)| id).collect::<Vec<_>>(), vec![package_id]);

    let wrong_table = VerusStorageAssetKeyV1 { tables: vec![VerusStorageAssetTableV1 { table: "u".into(), ..key(package_id, "v1", "r1").tables[0].clone() }], ..key(package_id, "v1", "r1") };
    let wrong_lock = lock_storage_asset(&store, wrong_table).unwrap();
    assert!(publish_storage_asset(&store, &wrong_lock, &staged_parts(&store, &wrong_lock), built(), 1, evidence).unwrap_err().to_string().contains("stored tables"));
    let lock = lock_storage_asset(&store, key(package_id, "v1", "r1")).unwrap();
    assert!(locked_storage_asset(&store, &lock).unwrap().is_none());
    let (asset_id, asset) = publish_storage_asset(&store, &lock, &staged_parts(&store, &lock), built(), 1, evidence).unwrap();
    assert_eq!(asset.directory, format!("assets/{}", key(package_id, "v1", "r1").identity().unwrap().to_hex()));
    let directory = storage_asset_directory(&store, &asset).unwrap();
    assert!(directory.starts_with(store.root()) && directory.join("part-0000.bin").is_file());
    assert!(publish_storage_asset(&store, &lock, &staged_parts(&store, &lock), built(), 1, evidence).is_err(), "one asset per key");
    drop(lock);
    assert_eq!(resolve_storage_asset(&store, &key(package_id, "v1", "r1")).unwrap().unwrap().0, asset_id);
    assert!(resolve_storage_asset(&store, &key(package_id, "v2", "r1")).unwrap().is_none(), "a changed source is stale");
    assert!(resolve_storage_asset(&store, &key(package_id, "v1", "r2")).unwrap().is_none(), "another read of the source is stale");

    // The library stands alone: moved as a whole, its asset is found at the same relative path.
    let moved = dir.join("moved-library");
    std::fs::rename(store.root(), &moved).unwrap();
    let moved = ObjectStore::open_existing(&moved).unwrap();
    let (_, found) = resolve_storage_asset(&moved, &key(package_id, "v1", "r1")).unwrap().unwrap();
    assert!(storage_asset_directory(&moved, &found).unwrap().join("parts.json").is_file());
}

/// A query package over stored data is admitted only with admitted storages whose closure it carries byte for byte,
/// with the same check configuration, and whose composition rule passes; it is then found by its key v2.
#[test]
fn query_packages_compose_only_with_their_storages_closure() {
    let dir = common::scratch_dir("query-v4-records");
    let store = ObjectStore::open(dir.join("library")).unwrap();
    let tcb = store.put(1, VERUS_TCB_KIND, &VerusTcbV1 { items: vec![], refusal_rules: serde_json::json!([]) }).unwrap();
    let storage = storage_crate(&dir.join("storage"), "INTERFACE v1");
    let storage_build_id = storage.publish(&store, "pinned", &[], tcb);
    let package = storage_package(&store, storage_build_id, tcb);
    let storage_id = publish_storage_package(&store, &package, &storage.framework()).unwrap();
    let evidence = store.put(1, "fixture-evidence", &true).unwrap();

    let key = VerusStatementKeyV2 {
        frontend_identity: "fixture".into(),
        schema: "SCHEMA".into(),
        statement: statement_meaning(QUERY_RS),
        free: vec![VerusFreeParamV1 { index: 1, slot: 0, sql_type: "integer".into(), min: Some("1".into()), max: Some("9".into()) }],
        output: vec![("x".into(), "int4".into())],
        constraints: None,
    };
    let statement = publish_statement_key_v2(&store, &key).unwrap();
    let parameters = vec![VerusParamDeclV1 { index: 1, sql_type: "integer".into(), binding: VerusParamBindingV1::Free { min: Some("1".into()), max: Some("9".into()) } }];
    let uses = vec![VerusStorageUseV1 { name: "s".into(), package: storage_id }];
    let theorems = vec!["gendb_entry::theorem_end_to_end".to_string()];
    let admit = |crate_: &Crate, provider: &str, composition: CompositionRule<'_>| -> Result<ContentId, String> {
        let build = crate_.publish(&store, provider, &[], tcb);
        let claim = publish_claim_v2(&store, VerusSqlClaimV2Input {
            statement, build, theorems: theorems.clone(), sql: "SELECT x FROM t WHERE x < $1".into(),
            frontend: serde_json::json!({"identity": "fixture"}), schema_ddl: "DDL", parameters: parameters.clone(),
            demand: serde_json::json!({}), storage_uses: uses.clone(),
        })
        .map_err(|e| e.to_string())?;
        let package = store
            .put(1, VERUS_QUERY_PACKAGE_V3_KIND, &VerusQueryPackageV3 {
                statement, claim, entry_identity: VERUS_ENTRY_V4_IDENTITY.into(), build, storage_uses: uses.clone(),
                implementations: vec![], abi_version: 4, workers: (1, 64), tcb,
            })
            .unwrap();
        let admission = VerusPackageAdmissionV2 { package, gate_identity: "g".into(), qualification_evidence: vec![evidence], assets: vec![] };
        admit_package_v4(&store, &admission, &crate_.framework(), composition).map_err(|e| e.to_string())
    };
    let accept: CompositionRule<'_> = &|_| Ok(());
    let good = query_crate(&dir.join("query-good"), shared("INTERFACE v1", "SCHEMA"));

    // A storage that is published but not admitted cannot be used.
    assert!(admit(&good, "pinned", accept).unwrap_err().contains("not admitted"));
    admit_storage_package(&store, &VerusStorageAdmissionV1 { package: storage_id, gate_identity: "g".into(), evidence: vec![evidence] }).unwrap();

    let changed_interface = query_crate(&dir.join("query-interface"), shared("INTERFACE v2", "SCHEMA"));
    assert!(admit(&changed_interface, "pinned", accept).unwrap_err().contains("stores/s/interface/mod.rs of storage s is missing from the query build or differs"));
    let mut changed_dependency = shared("INTERFACE v1", "SCHEMA");
    changed_dependency[0].1 = "SPEC CHANGED".into();
    let changed_dependency = query_crate(&dir.join("query-dependency"), changed_dependency);
    assert!(admit(&changed_dependency, "pinned", accept).unwrap_err().contains("spec/value.rs of storage s"));
    assert!(admit(&good, "another toolchain", accept).unwrap_err().contains("another toolchain or configuration"));
    let refuse: CompositionRule<'_> = &|c| Err(format!("fixture rule refuses {}", c.name));
    assert!(admit(&good, "pinned", refuse).unwrap_err().contains("fixture rule refuses s"));
    assert!(resolve_package_v4(&store, statement).unwrap().is_none());

    let admitted = admit(&good, "pinned", accept).unwrap();
    let resolved = resolve_package_v4(&store, statement).unwrap().unwrap();
    assert_eq!((resolved.admission_id, resolved.storages[0].name.as_str()), (admitted, "s"));
    let v1_key = VerusStatementKeyV1 { frontend_identity: key.frontend_identity.clone(), meaning: key.statement.clone(), free: key.free.clone(), output: key.output.clone() };
    assert_ne!(v1_key.identity().unwrap(), statement, "keys v1 and v2 never share a stream");
    assert!(resolve_package_v3(&store, v1_key.identity().unwrap()).unwrap().is_none());
}

/// A key that declares integrity constraints is proved with entry v5 and a build carrying the key's
/// `gendb_constraints.rs`; a key without declarations with entry v4 and no such file. Every other combination (the
/// assumption dropped, or added, or another declaration list) is refused at the claim or at admission, and the
/// admitted constrained package is found only by its own key.
#[test]
fn declared_constraints_fix_the_entry_and_module_of_a_package() {
    let dir = common::scratch_dir("query-v5-records");
    let store = ObjectStore::open(dir.join("library")).unwrap();
    let tcb = store.put(1, VERUS_TCB_KIND, &VerusTcbV1 { items: vec![], refusal_rules: serde_json::json!([]) }).unwrap();
    let storage = storage_crate(&dir.join("storage"), "INTERFACE v1");
    let storage_build_id = storage.publish(&store, "pinned", &[], tcb);
    let storage_id = publish_storage_package(&store, &storage_package(&store, storage_build_id, tcb), &storage.framework()).unwrap();
    let evidence = store.put(1, "fixture-evidence", &true).unwrap();
    admit_storage_package(&store, &VerusStorageAdmissionV1 { package: storage_id, gate_identity: "g".into(), evidence: vec![evidence] }).unwrap();

    let plain_key = VerusStatementKeyV2 {
        frontend_identity: "fixture".into(),
        schema: "SCHEMA".into(),
        statement: statement_meaning(QUERY_RS),
        free: vec![],
        output: vec![("x".into(), "int4".into())],
        constraints: None,
    };
    let declared_key = VerusStatementKeyV2 { constraints: Some("CONSTRAINTS t: PRIMARY KEY (x)".into()), ..plain_key.clone() };
    assert_eq!((query_entry_identity(&plain_key), query_entry_identity(&declared_key)), (VERUS_ENTRY_V4_IDENTITY, VERUS_ENTRY_V5_IDENTITY));
    let plain = publish_statement_key_v2(&store, &plain_key).unwrap();
    let declared = publish_statement_key_v2(&store, &declared_key).unwrap();
    let uses = vec![VerusStorageUseV1 { name: "s".into(), package: storage_id }];
    // Publish the claim and a package naming `package_entry`, then admit it against `expected` framework files.
    let admit = |crate_: &Crate, statement: ContentId, package_entry: &str, expected: &[(&str, &str)]| -> Result<ContentId, String> {
        let build = crate_.publish(&store, "pinned", &[], tcb);
        let claim = publish_claim_v2(&store, VerusSqlClaimV2Input {
            statement, build, theorems: vec!["gendb_entry::theorem_end_to_end".into()], sql: "SELECT x FROM t".into(),
            frontend: serde_json::json!({"identity": "fixture"}), schema_ddl: "DDL", parameters: vec![],
            demand: serde_json::json!({}), storage_uses: uses.clone(),
        })
        .map_err(|e| e.to_string())?;
        let package = store
            .put(1, VERUS_QUERY_PACKAGE_V3_KIND, &VerusQueryPackageV3 {
                statement, claim, entry_identity: package_entry.into(), build, storage_uses: uses.clone(),
                implementations: vec![], abi_version: 4, workers: (1, 64), tcb,
            })
            .unwrap();
        let admission = VerusPackageAdmissionV2 { package, gate_identity: "g".into(), qualification_evidence: vec![evidence], assets: vec![] };
        admit_package_v4(&store, &admission, expected, &|_| Ok(())).map_err(|e| e.to_string())
    };
    let crate_of = |name: &str, entry: &str, constraints: Option<&str>| query_crate_with(&dir.join(name), shared("INTERFACE v1", "SCHEMA"), entry, constraints);
    let module = declared_key.constraints.as_deref();
    let v5 = crate_of("v5", QUERY_ENTRY_V5, module);
    let refused = |crate_: &Crate, statement, entry| admit(crate_, statement, entry, &crate_.framework()).unwrap_err();

    // The assumption dropped: entry v4 for a constrained key (with or without the module), or the module missing.
    assert!(refused(&crate_of("v4-module", QUERY_ENTRY, module), declared, VERUS_ENTRY_V4_IDENTITY).contains("not the fixed entry gendb-verus-entry-v5"));
    assert!(refused(&crate_of("v5-no-module", QUERY_ENTRY_V5, None), declared, VERUS_ENTRY_V5_IDENTITY).starts_with("declared_constraints_missing"));
    // The assumption added: entry v5 or the module for an unconstrained key.
    assert!(refused(&crate_of("v5-plain", QUERY_ENTRY_V5, None), plain, VERUS_ENTRY_V5_IDENTITY).contains("not the fixed entry gendb-verus-entry-v4"));
    assert!(refused(&crate_of("v4-extra-module", QUERY_ENTRY, module), plain, VERUS_ENTRY_V4_IDENTITY).starts_with("declared_constraints_unexpected"));
    // Another declaration list than the key's.
    assert!(refused(&crate_of("v5-other", QUERY_ENTRY_V5, Some("CONSTRAINTS t: UNIQUE (x)")), declared, VERUS_ENTRY_V5_IDENTITY).contains("not the statement key's declared constraints"));
    // At admission: a package naming entry v4 for the constrained key, and a fresh generation without the module.
    assert!(refused(&v5, declared, VERUS_ENTRY_V4_IDENTITY).contains("not the admitted format of its statement key"));
    let without_module: Vec<(&str, &str)> = v5.framework().into_iter().filter(|(path, _)| *path != "gendb_constraints.rs").collect();
    assert!(admit(&v5, declared, VERUS_ENTRY_V5_IDENTITY, &without_module).unwrap_err().starts_with("declared_constraints_missing"));
    assert!(resolve_package_v4(&store, declared).unwrap().is_none());

    let admitted = admit(&v5, declared, VERUS_ENTRY_V5_IDENTITY, &v5.framework()).unwrap();
    let resolved = resolve_package_v4(&store, declared).unwrap().unwrap();
    assert_eq!((resolved.admission_id, resolved.package.entry_identity.as_str()), (admitted, VERUS_ENTRY_V5_IDENTITY));
    assert_eq!(resolved.claim.entry_identity, VERUS_ENTRY_V5_IDENTITY);
    assert!(resolve_package_v4(&store, plain).unwrap().is_none(), "the constrained package is on its own key's stream only");
    let plain_admitted = admit(&crate_of("v4", QUERY_ENTRY, None), plain, VERUS_ENTRY_V4_IDENTITY, &crate_of("v4-fresh", QUERY_ENTRY, None).framework()).unwrap();
    assert_eq!(resolve_package_v4(&store, plain).unwrap().unwrap().admission_id, plain_admitted);
    assert_eq!(resolve_package_v4(&store, declared).unwrap().unwrap().admission_id, admitted, "each key keeps its own package");
}

/// A storage package assumes declared constraints exactly when its build is of the storage entry v2 and carries the
/// recorded `gendb_constraints.rs`; every mismatch is refused at publication. Admitted, it is composed only by a query
/// key with exactly that declaration set (`storage_assumes_declared_constraints` for a key without declarations or with
/// another list), and its package record without the field keeps the unconstrained identity.
#[test]
fn constraint_dependent_storages_record_and_compose_only_with_their_set() {
    const MODULE: &str = "CONSTRAINTS t: PRIMARY KEY (x)";
    const OTHER: &str = "CONSTRAINTS t: UNIQUE (x)";
    let dir = common::scratch_dir("storage-v2-records");
    let store = ObjectStore::open(dir.join("library")).unwrap();
    let tcb = store.put(1, VERUS_TCB_KIND, &VerusTcbV1 { items: vec![], refusal_rules: serde_json::json!([]) }).unwrap();
    let digest = declared_constraints_digest(MODULE);
    assert_eq!(digest, store.put_blob(MODULE.as_bytes()).unwrap(), "the digest is the module's blob identity");
    let publish = |name: &str, entry: &str, module: Option<&str>, assumed: Option<ContentId>, identity: &str| -> Result<ContentId, String> {
        let crate_ = storage_crate_with(&dir.join(name), "INTERFACE v1", entry, module);
        let build = crate_.publish(&store, "pinned", &[], tcb);
        let package = VerusStoragePackageV1 { assumed_constraints: assumed, entry_identity: identity.into(), ..storage_package(&store, build, tcb) };
        publish_storage_package(&store, &package, &crate_.framework()).map_err(|e| e.to_string())
    };
    let (v1, v2) = (VERUS_STORAGE_ENTRY_V1_IDENTITY, VERUS_STORAGE_ENTRY_V2_IDENTITY);
    // The assumption recorded without its entry or module, or the module/entry without the record: refused.
    assert!(publish("v1-assumed", STORAGE_ENTRY, None, Some(digest), v2).unwrap_err().contains("not the fixed entry gendb-verus-storage-entry-v2"));
    assert!(publish("v2-unrecorded", STORAGE_ENTRY_V2, Some(MODULE), None, v1).unwrap_err().contains("not the fixed entry gendb-verus-storage-entry-v1"));
    assert!(publish("v2-no-module", STORAGE_ENTRY_V2, None, Some(digest), v2).unwrap_err().starts_with("declared_constraints_missing"));
    assert!(publish("v1-extra-module", STORAGE_ENTRY, Some(MODULE), None, v1).unwrap_err().starts_with("declared_constraints_unexpected"));
    assert!(publish("v2-other-module", STORAGE_ENTRY_V2, Some(OTHER), Some(digest), v2).unwrap_err().contains("not the package's assumed constraints"));
    assert!(publish("v2-named-v1", STORAGE_ENTRY_V2, Some(MODULE), Some(digest), v1).unwrap_err().contains("names another TCB or entry"));
    let storage_id = publish("v2", STORAGE_ENTRY_V2, Some(MODULE), Some(digest), v2).unwrap();
    let plain_id = publish("v1", STORAGE_ENTRY, None, None, v1).unwrap();
    let evidence = store.put(1, "fixture-evidence", &true).unwrap();
    for id in [storage_id, plain_id] {
        admit_storage_package(&store, &VerusStorageAdmissionV1 { package: id, gate_identity: "g".into(), evidence: vec![evidence] }).unwrap();
    }
    let storage = resolve_admitted_storage(&store, storage_id).unwrap();
    assert_eq!((storage.assumed_constraints, storage.storage_entry_identity()), (Some(digest), v2));
    let plain_record = serde_json::to_value(resolve_admitted_storage(&store, plain_id).unwrap()).unwrap();
    assert!(plain_record.get("assumed_constraints").is_none(), "an unconstrained package record is unchanged");
    // The exact-set rule itself: none and other sets refused, the same set accepted; v1 storages everywhere.
    assert!(storage.check_declared_constraints(None).unwrap_err().to_string().starts_with("storage_assumes_declared_constraints: storage s assumes"));
    assert!(storage.check_declared_constraints(Some(declared_constraints_digest(OTHER))).is_err());
    storage.check_declared_constraints(Some(digest)).unwrap();

    // Query admission: the storage composes only with a key declaring exactly its set.
    let key = |constraints: Option<&str>| VerusStatementKeyV2 {
        frontend_identity: "fixture".into(),
        schema: "SCHEMA".into(),
        statement: statement_meaning(QUERY_RS),
        free: vec![],
        output: vec![("x".into(), "int4".into())],
        constraints: constraints.map(String::from),
    };
    let uses = vec![VerusStorageUseV1 { name: "s".into(), package: storage_id }];
    let admit = |name: &str, constraints: Option<&str>, entry: &str, identity: &str| -> Result<ContentId, String> {
        let statement = publish_statement_key_v2(&store, &key(constraints)).unwrap();
        let crate_ = query_crate_with(&dir.join(name), shared("INTERFACE v1", "SCHEMA"), entry, constraints);
        let build = crate_.publish(&store, "pinned", &[], tcb);
        let claim = publish_claim_v2(&store, VerusSqlClaimV2Input {
            statement, build, theorems: vec!["gendb_entry::theorem_end_to_end".into()], sql: "SELECT x FROM t".into(),
            frontend: serde_json::json!({"identity": "fixture"}), schema_ddl: "DDL", parameters: vec![],
            demand: serde_json::json!({}), storage_uses: uses.clone(),
        })
        .map_err(|e| e.to_string())?;
        let package = store
            .put(1, VERUS_QUERY_PACKAGE_V3_KIND, &VerusQueryPackageV3 {
                statement, claim, entry_identity: identity.into(), build, storage_uses: uses.clone(),
                implementations: vec![], abi_version: 4, workers: (1, 64), tcb,
            })
            .unwrap();
        let admission = VerusPackageAdmissionV2 { package, gate_identity: "g".into(), qualification_evidence: vec![evidence], assets: vec![] };
        admit_package_v4(&store, &admission, &crate_.framework(), &|_| Ok(())).map_err(|e| e.to_string())
    };
    let refused = admit("q-v4", None, QUERY_ENTRY, VERUS_ENTRY_V4_IDENTITY).unwrap_err();
    assert!(refused.starts_with("storage_assumes_declared_constraints: storage s assumes") && refused.ends_with("this run declares none"), "{refused}");
    let refused = admit("q-v5-other", Some(OTHER), QUERY_ENTRY_V5, VERUS_ENTRY_V5_IDENTITY).unwrap_err();
    assert!(refused.starts_with("storage_assumes_declared_constraints") && refused.contains("other constraints"), "{refused}");
    admit("q-v5", Some(MODULE), QUERY_ENTRY_V5, VERUS_ENTRY_V5_IDENTITY).unwrap();
}

/// One builder per key across concurrent callers (threads holding separate lock descriptions, as processes do): four
/// callers of one key build once and all get that asset, while another key is built without waiting. Retry after an
/// interrupted publication: a placed directory with its stored but unappended record is completed without a build; a
/// placed directory without a record is refused and left as it is.
#[test]
fn one_builder_per_key_and_precise_retry() {
    let dir = common::scratch_dir("storage-asset-locks");
    let store = ObjectStore::open(dir.join("library")).unwrap();
    let tcb = store.put(1, VERUS_TCB_KIND, &VerusTcbV1 { items: vec![], refusal_rules: serde_json::json!([]) }).unwrap();
    let storage = storage_crate(&dir.join("storage"), "INTERFACE v1");
    let build = storage.publish(&store, "pinned", &[], tcb);
    let package_id = publish_storage_package(&store, &storage_package(&store, build, tcb), &storage.framework()).unwrap();
    let evidence = store.put(1, "fixture-build-evidence", &true).unwrap();
    let builds = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));

    // The build_storage_asset protocol with a fixture build: lock, look up under the lock, build only if absent, publish.
    let asset_of = {
        let (store, builds) = (store.clone(), builds.clone());
        move |row_order: &str| -> ContentId {
            let lock = lock_storage_asset(&store, key(package_id, "v1", row_order)).unwrap();
            if let Some((id, _)) = locked_storage_asset(&store, &lock).unwrap() {
                return id;
            }
            builds.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            let staged = staged_parts(&store, &lock);
            std::thread::sleep(std::time::Duration::from_millis(200));
            publish_storage_asset(&store, &lock, &staged, built(), 1, evidence).unwrap().0
        }
    };
    let callers: Vec<_> = (0..4)
        .map(|_| {
            let asset_of = asset_of.clone();
            std::thread::spawn(move || asset_of("shared"))
        })
        .collect();
    let ids: BTreeSet<ContentId> = callers.into_iter().map(|c| c.join().unwrap()).collect();
    assert_eq!((ids.len(), builds.load(std::sync::atomic::Ordering::SeqCst)), (1, 1), "one build, one asset for every caller");

    // A held key does not block another key.
    let held = lock_storage_asset(&store, key(package_id, "v1", "held")).unwrap();
    let (done, finished) = std::sync::mpsc::channel();
    let other = asset_of.clone();
    std::thread::spawn(move || done.send(other("other")).unwrap());
    assert!(finished.recv_timeout(std::time::Duration::from_secs(20)).is_ok(), "another key proceeds while one is held");
    drop(held);

    // Interrupted after the record was stored, before it was appended: completed on retry, no build.
    let interrupted = lock_storage_asset(&store, key(package_id, "v1", "interrupted")).unwrap();
    let name = key(package_id, "v1", "interrupted").identity().unwrap();
    let directory = store.place_asset_directory(&staged_parts(&store, &interrupted), name).unwrap();
    let record = VerusStorageAssetV1 {
        key: key(package_id, "v1", "interrupted"), directory, parts_format: 2, byte_order: "little".into(),
        parts: vec![("i32".into(), 3)], storage_bytes: 12, build_wall_ns: 1, evidence,
    };
    let stored = store.put(1, VERUS_STORAGE_ASSET_KIND, &record).unwrap();
    assert!(resolve_storage_asset(&store, &key(package_id, "v1", "interrupted")).unwrap().is_none());
    assert_eq!(locked_storage_asset(&store, &interrupted).unwrap().map(|(id, _)| id), Some(stored));
    assert_eq!(resolve_storage_asset(&store, &key(package_id, "v1", "interrupted")).unwrap().map(|(id, _)| id), Some(stored));
    drop(interrupted);

    // Interrupted between the rename and the record: refused, the directory is not overwritten.
    let orphan = lock_storage_asset(&store, key(package_id, "v1", "orphan")).unwrap();
    let name = key(package_id, "v1", "orphan").identity().unwrap();
    let placed = store.asset_directory(&store.place_asset_directory(&staged_parts(&store, &orphan), name).unwrap()).unwrap();
    let refusal = locked_storage_asset(&store, &orphan).unwrap_err().to_string();
    assert!(refusal.contains("unrecorded_asset_directory"), "{refusal}");
    assert!(publish_storage_asset(&store, &orphan, &staged_parts(&store, &orphan), built(), 1, evidence).is_err());
    assert!(placed.join("parts.json").is_file(), "the placed directory is left as it is");
    assert_eq!(builds.load(std::sync::atomic::Ordering::SeqCst), 2, "only the shared and the other key were built");
}

/// The release of a published asset (the general engine line): its directory goes and its key's stream ends with a
/// release record naming the asset, its bytes and why, so the key has no asset; a second release does nothing. A
/// rebuild publishes after the release, and an interrupted publication after a release completes with its own
/// (unappended) record, never an earlier, released one. A release interrupted after its directory was moved leaves the
/// record without a directory and a staged leftover that the key's next lookup removes.
#[test]
fn a_release_ends_the_keys_stream_and_a_rebuild_publishes_after_it() {
    let dir = common::scratch_dir("storage-asset-release");
    let store = ObjectStore::open(dir.join("library")).unwrap();
    let tcb = store.put(1, VERUS_TCB_KIND, &VerusTcbV1 { items: vec![], refusal_rules: serde_json::json!([]) }).unwrap();
    let storage = storage_crate(&dir.join("storage"), "INTERFACE v1");
    let build = storage.publish(&store, "pinned", &[], tcb);
    let package_id = publish_storage_package(&store, &storage_package(&store, build, tcb), &storage.framework()).unwrap();
    let evidence = store.put(1, "fixture-build-evidence", &true).unwrap();
    let lock = lock_storage_asset(&store, key(package_id, "v1", "released")).unwrap();
    let (first, record) = publish_storage_asset(&store, &lock, &staged_parts(&store, &lock), built(), 1, evidence).unwrap();
    let placed = storage_asset_directory(&store, &record).unwrap();

    let released = release_storage_asset(&store, &lock, first, "superseded (fixture)", 7).unwrap().expect("released");
    assert_eq!((released.record.asset, released.record.storage_bytes, released.record.released_unix_ms), (first, 12, 7));
    assert_eq!((released.file_bytes, released.freed_bytes), (12 + 81, 12 + 81), "the part and parts.json, no other link");
    assert!(!placed.exists() && resolve_storage_asset(&store, lock.key()).unwrap().is_none());
    let (release_id, release) = released_storage_asset(&store, lock.key()).unwrap().unwrap();
    assert_eq!((release_id, release.reason.as_str()), (released.release, "superseded (fixture)"));
    assert!(release_storage_asset(&store, &lock, first, "again", 8).unwrap().is_none(), "nothing left to release");
    assert!(locked_storage_asset(&store, &lock).unwrap().is_none(), "the key needs a build");

    // A rebuild publishes after the release record.
    let (second, _) = publish_storage_asset(&store, &lock, &staged_parts(&store, &lock), built(), 2, evidence).unwrap();
    assert_ne!(second, first);
    assert_eq!(resolve_storage_asset(&store, lock.key()).unwrap().map(|(id, _)| id), Some(second));
    assert!(released_storage_asset(&store, lock.key()).unwrap().is_none());

    // Released again, then a publication interrupted after its record was stored: its own record completes it.
    release_storage_asset(&store, &lock, second, "superseded (fixture)", 9).unwrap().expect("released");
    let name = lock.key().identity().unwrap();
    let directory = store.place_asset_directory(&staged_parts(&store, &lock), name).unwrap();
    let third = VerusStorageAssetV1 { key: lock.key().clone(), directory, parts_format: 2, byte_order: "little".into(), parts: vec![("i32".into(), 3)], storage_bytes: 12, build_wall_ns: 3, evidence };
    let stored = store.put(1, VERUS_STORAGE_ASSET_KIND, &third).unwrap();
    assert_eq!(locked_storage_asset(&store, &lock).unwrap().map(|(id, _)| id), Some(stored), "not the released first or second record");

    // A release interrupted after its directory was moved away: the record stays without a directory.
    let staged = store.retire_asset_directory(lock.asset_name()).unwrap().expect("a placed directory");
    assert!(resolve_storage_asset(&store, lock.key()).unwrap().is_some() && !store.asset_directory_exists(name) && staged.is_dir());
    assert!(store.remove_stale_asset_staging(lock.asset_name()).unwrap() > 0 && !staged.exists(), "the leftover is a stale staged build of the key");
}

/// A trial build outside the library is published with exactly the record computed at its build: the rename places
/// the very directory (same files, sealed), the published id is the precomputed one, recovery finds nothing to
/// complete, and a record of another key, an incomplete trial or a trial inside the library are refused.
#[test]
fn trial_assets_publish_their_precomputed_record_by_rename() {
    let dir = common::scratch_dir("storage-trial-assets");
    let store = ObjectStore::open(dir.join("library")).unwrap();
    let tcb = store.put(1, VERUS_TCB_KIND, &VerusTcbV1 { items: vec![], refusal_rules: serde_json::json!([]) }).unwrap();
    let storage = storage_crate(&dir.join("storage"), "INTERFACE v1");
    let build = storage.publish(&store, "pinned", &[], tcb);
    let package_id = publish_storage_package(&store, &storage_package(&store, build, tcb), &storage.framework()).unwrap();
    let evidence = store.put(1, "fixture-build-evidence", &true).unwrap();
    let trial = |name: &str, complete: bool| {
        let path = dir.join("session/trial-assets").join(name);
        std::fs::create_dir_all(&path).unwrap();
        std::fs::write(path.join("part-0000.bin"), [0u8; 12]).unwrap();
        if complete {
            std::fs::write(path.join("parts.json"), br#"{"format_version":2,"byte_order":"little","parts":[["i32",3]],"storage_bytes":12}"#).unwrap();
        }
        path
    };
    let record = storage_asset_record(key(package_id, "v1", "trial"), built(), 5, evidence).unwrap();
    let expected = storage_asset_id(&record).unwrap();
    let lock = lock_storage_asset(&store, key(package_id, "v1", "trial")).unwrap();
    let other = storage_asset_record(key(package_id, "v1", "other"), built(), 5, evidence).unwrap();
    assert!(publish_trial_storage_asset(&store, &lock, &trial("a", true), other).unwrap_err().to_string().contains("another key"));
    assert!(publish_trial_storage_asset(&store, &lock, &trial("b", false), record.clone()).unwrap_err().to_string().contains("incomplete"));
    let inside = store.root().join("inside");
    std::fs::create_dir_all(&inside).unwrap();
    std::fs::write(inside.join("parts.json"), b"{}").unwrap();
    assert!(publish_trial_storage_asset(&store, &lock, &inside, record.clone()).unwrap_err().to_string().contains("outside this library"));
    assert!(locked_storage_asset(&store, &lock).unwrap().is_none(), "no record is stored before placement");

    let sealed = trial("c", true);
    std::fs::set_permissions(&sealed, std::fs::Permissions::from_mode(0o555)).unwrap();
    let inode = std::fs::metadata(sealed.join("part-0000.bin")).unwrap().ino();
    let (id, published) = publish_trial_storage_asset(&store, &lock, &sealed, record.clone()).unwrap();
    assert_eq!((id, &published), (expected, &record), "the published asset is the precomputed record");
    let placed = storage_asset_directory(&store, &published).unwrap();
    assert!(!sealed.exists() && std::fs::metadata(placed.join("part-0000.bin")).unwrap().ino() == inode, "renamed, not copied");
    assert_eq!(std::fs::metadata(&placed).unwrap().permissions().mode() & 0o777, 0o555);
    assert_eq!(locked_storage_asset(&store, &lock).unwrap().map(|(id, _)| id), Some(expected));
    drop(lock);
    assert_eq!(resolve_storage_asset(&store, &key(package_id, "v1", "trial")).unwrap().map(|(id, _)| id), Some(expected));
}

/// Author discovery lists every admitted version of a name, newest first, the head marked current; the head-only
/// listing keeps its meaning.
#[test]
fn every_admitted_version_is_discoverable() {
    let dir = common::scratch_dir("storage-versions");
    let store = ObjectStore::open(dir.join("library")).unwrap();
    let tcb = store.put(1, VERUS_TCB_KIND, &VerusTcbV1 { items: vec![], refusal_rules: serde_json::json!([]) }).unwrap();
    let evidence = store.put(1, "fixture-evidence", &true).unwrap();
    let mut packages = vec![];
    for version in ["v1", "v2"] {
        let storage = storage_crate(&dir.join(version), &format!("INTERFACE {version}"));
        let build = storage.publish(&store, "pinned", &[], tcb);
        let id = publish_storage_package(&store, &storage_package(&store, build, tcb), &storage.framework()).unwrap();
        admit_storage_package(&store, &VerusStorageAdmissionV1 { package: id, gate_identity: "g".into(), evidence: vec![evidence] }).unwrap();
        packages.push(id);
    }
    let listed: Vec<(ContentId, bool)> = admitted_storages(&store).unwrap().into_iter().map(|a| (a.package_id, a.current)).collect();
    assert_eq!(listed, vec![(packages[1], true), (packages[0], false)], "both versions of `s`, newest first");
    let heads: Vec<ContentId> = current_storages(&store).unwrap().into_iter().map(|(id, _)| id).collect();
    assert_eq!(heads, vec![packages[1]]);
    assert_eq!(resolve_admitted_storage(&store, packages[0]).unwrap().name, "s", "the older version stays usable by id");
}
