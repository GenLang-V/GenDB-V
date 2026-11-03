//! Admission rules of Verus build, representation, asset and v3 package records.

mod common;

use gendb_artifacts::verus::*;
use gendb_artifacts::{ColType, ColumnSpec, ContentId, ObjectStore};
use std::collections::BTreeMap;
use std::path::Path;

const COMPLETE: &str = "{\"verification-results\":{\"success\":true,\"verified\":12,\"errors\":0,\"is-verifying-entire-crate\":true,\"encountered-error\":false,\"encountered-vir-error\":false}}";

fn tcb(store: &ObjectStore) -> ContentId {
    store.put(1, VERUS_TCB_KIND, &VerusTcbV1 { items: vec![], refusal_rules: serde_json::json!([]) }).unwrap()
}

fn publish(
    store: &ObjectStore,
    frozen: &Path,
    purpose: VerusBuildPurposeV1,
    stdout: &str,
    sources: Vec<(String, VerusSourceOwnerV1)>,
    tcb: ContentId,
) -> ContentId {
    publish_build(store, VerusBuildInput {
        purpose,
        provider_identity: "{\"verus\":\"pinned\"}".into(),
        argv: ["lib.rs", "--no-cheating", "--output-json", "--compile"].map(String::from).to_vec(),
        environment: BTreeMap::new(),
        exit_code: Some(0),
        stdout,
        frozen_directory: frozen,
        sources,
        library_path: &frozen.join("libq.so"),
        wall_ns: 1,
        tcb,
    })
    .unwrap()
}

fn column(name: &str, ty: ColType) -> ColumnSpec {
    ColumnSpec { name: name.into(), ty, nullable: false }
}

#[test]
fn builds_need_real_verus_evidence_and_assets_cover_every_source_table() {
    let dir = common::scratch_dir("verus-build");
    let frozen = dir.join("frozen");
    std::fs::create_dir_all(frozen.join("src/agent")).unwrap();
    std::fs::write(frozen.join("src/gendb_contract.rs"), "CONTRACT").unwrap();
    std::fs::write(frozen.join("src/agent/mod.rs"), "AGENT").unwrap();
    std::fs::write(frozen.join("libq.so"), b"\x7fELF-fixture").unwrap();
    let store = ObjectStore::open(dir.join("library")).unwrap();
    let tcb = tcb(&store);
    let sources = || vec![("gendb_contract.rs".into(), VerusSourceOwnerV1::Framework), ("agent/mod.rs".into(), VerusSourceOwnerV1::Agent)];
    let partial = COMPLETE.replace("\"is-verifying-entire-crate\":true", "\"is-verifying-entire-crate\":false");
    let failed = "{\"verification-results\":{\"success\":false,\"verified\":11,\"errors\":1}}";
    let good = publish(&store, &frozen, VerusBuildPurposeV1::Candidate, COMPLETE, sources(), tcb);
    let fixture = publish(&store, &frozen, VerusBuildPurposeV1::AbiFixtureUnproved, COMPLETE, sources(), tcb);
    let broken = publish(&store, &frozen, VerusBuildPurposeV1::Candidate, failed, sources(), tcb);
    let partial = publish(&store, &frozen, VerusBuildPurposeV1::Candidate, &partial, sources(), tcb);
    assert!(check_build_evidence(&store, good).is_ok());
    assert!(check_build_evidence(&store, fixture).unwrap_err().to_string().contains("fixture"));
    assert!(check_build_evidence(&store, broken).unwrap_err().to_string().contains("successful"));
    assert!(check_build_evidence(&store, partial).unwrap_err().to_string().contains("entire crate"));

    let amount = column("a", ColType::Decimal { p: 15, s: 2 });
    let text = column("k", ColType::Utf8);
    let tables = vec![
        VerusSourceTableV2 { table: "t".into(), fields: vec![(1, text), (4, amount.clone())] },
        VerusSourceTableV2 { table: "u".into(), fields: vec![(0, amount)] },
    ];
    let representation = |build, sources: Vec<VerusSourceTableV2>| VerusRepresentationV2 {
        build, name: "narrow".into(), sources, parts: vec!["i64".into()], decode_item: "agent::decode".into(), builder_item: "agent::build".into(),
    };
    let repeated = vec![tables[0].clone(), tables[0].clone()];
    assert!(publish_representation_v2(&store, &representation(good, repeated)).unwrap_err().to_string().contains("repeated"));
    assert!(publish_representation_v2(&store, &representation(good, vec![])).is_err());
    let repr = publish_representation_v2(&store, &representation(good, tables.clone())).unwrap();
    let fixture_repr = publish_representation_v2(&store, &representation(fixture, tables)).unwrap();
    let versions = |t_version: &'static str| move |table: &str| -> Result<(String, usize), String> {
        match table {
            "t" => Ok((t_version.to_string(), 3)),
            "u" => Ok(("u1".to_string(), 7)),
            _ => Err(format!("{table} absent")),
        }
    };
    let decoded = |id: ContentId| -> VerusRepresentationV2 { store.read(id).unwrap().decode().unwrap() };
    let key = |id, version: &'static str| VerusAssetKeyV2::current(id, &decoded(id), &versions(version)).unwrap();
    assert_eq!(key(repr, "v1").sources.iter().map(|s| (s.table.as_str(), s.rows)).collect::<Vec<_>>(), [("t", 3), ("u", 7)]);
    let only_t = |t: &str| if t == "t" { Ok(("v1".to_string(), 3)) } else { Err("u absent".to_string()) };
    assert!(VerusAssetKeyV2::current(repr, &decoded(repr), &only_t).is_err(), "every source table must be covered");
    let evidence = store.put(1, "verus-build-observation-fixture", &true).unwrap();
    assert!(publish_asset_v2(&store, key(fixture_repr, "v1"), dir.join("a0"), 1, 8, evidence).is_err());
    let mut partial_key = key(repr, "v1");
    partial_key.sources.pop();
    assert!(publish_asset_v2(&store, partial_key, dir.join("a0"), 1, 8, evidence).unwrap_err().to_string().contains("source tables"));
    let asset = publish_asset_v2(&store, key(repr, "v1"), dir.join("a1"), 1, 24, evidence).unwrap();
    assert!(publish_asset_v2(&store, key(repr, "v1"), dir.join("a2"), 1, 24, evidence).is_err(), "one asset per key");
    assert_eq!(resolve_asset_v2(&store, &key(repr, "v1")).unwrap().unwrap().0, asset);
    assert!(resolve_asset_v2(&store, &key(repr, "v2")).unwrap().is_none(), "a changed version of one table is not applicable");
}

/// The statement key, the claim and the admission agree on one build; a key of another meaning (a different fixed
/// value) or another free domain never resolves to it; the claim needs the entry's theorems and the key's free
/// parameters; admission needs the fresh generation's query.rs to be the key's meaning.
#[test]
fn v3_package_is_found_only_by_its_statement_key() {
    let dir = common::scratch_dir("verus-v3");
    let frozen = dir.join("frozen");
    std::fs::create_dir_all(frozen.join("src/agent")).unwrap();
    std::fs::create_dir_all(frozen.join("src/gendb_entry")).unwrap();
    let query = "//! Generated by the gendb-sql emitter\n//!     SELECT x FROM t WHERE x < $1;\nuse vstd::prelude::*;\nMEANING x < ps[0]\n";
    let entry = "// FRAMEWORK FILE: the fixed entry v3 (identity `gendb-verus-entry-v3`)\npub proof fn theorem_end_to_end(db: Database) {}\npub proof fn theorem_build_total() {}\n";
    let framework: Vec<(&str, &str)> = vec![
        ("query.rs", query), ("gendb_source.rs", "SOURCE"), ("gendb_params.rs", "PARAMS"), ("gendb_entry.rs", entry),
        ("gendb_entry/binder.rs", "BINDER"), ("gendb_abi.rs", "ABI3"), ("gendb_shim.rs", "SHIM3"),
    ];
    for (path, text) in &framework {
        std::fs::write(frozen.join("src").join(path), text).unwrap();
    }
    std::fs::write(frozen.join("src/agent/mod.rs"), "AGENT").unwrap();
    std::fs::write(frozen.join("libq.so"), b"\x7fELF-fixture").unwrap();
    let store = ObjectStore::open(dir.join("library")).unwrap();
    let tcb = tcb(&store);
    let mut sources: Vec<(String, VerusSourceOwnerV1)> = framework.iter().map(|(p, _)| (p.to_string(), VerusSourceOwnerV1::Framework)).collect();
    sources.push(("agent/mod.rs".into(), VerusSourceOwnerV1::Agent));
    let build = publish(&store, &frozen, VerusBuildPurposeV1::Candidate, COMPLETE, sources, tcb);

    let free = |max: &str| vec![VerusFreeParamV1 { index: 1, slot: 0, sql_type: "integer".into(), min: Some("1".into()), max: Some(max.into()) }];
    let key = |meaning: &str, max: &str| VerusStatementKeyV1 {
        frontend_identity: "gendb-sql-frontend-v4".into(), meaning: meaning.into(), free: free(max), output: vec![("x".into(), "integer".into())],
    };
    assert_eq!(statement_meaning(query), "use vstd::prelude::*;\nMEANING x < ps[0]\n");
    let statement = publish_statement_key(&store, &key(&statement_meaning(query), "100")).unwrap();
    let other_domain = key(&statement_meaning(query), "50").identity().unwrap();
    let other_meaning = publish_statement_key(&store, &key("use vstd::prelude::*;\nMEANING x < 7\n", "100")).unwrap();
    assert!(statement != other_domain && statement != other_meaning);
    let declaration = |max: &str| vec![
        VerusParamDeclV1 { index: 1, sql_type: "integer".into(), binding: VerusParamBindingV1::Free { min: Some("1".into()), max: Some(max.into()) } },
        VerusParamDeclV1 { index: 2, sql_type: "date".into(), binding: VerusParamBindingV1::Fixed { value: "2020-06-30".into() } },
    ];
    let claim_input = |statement, theorems: &[&str], parameters| VerusSqlClaimInput {
        statement, build, theorems: theorems.iter().map(|t| t.to_string()).collect(), sql: "SELECT x FROM t WHERE x < $1".into(),
        frontend: serde_json::json!({"identity": "gendb-sql-frontend-v4"}), schema_ddl: "CREATE TABLE t (x integer NOT NULL);", parameters,
        source: serde_json::json!({"tables": []}),
    };
    let theorems = ["gendb_entry::theorem_end_to_end", "gendb_entry::theorem_build_total"];
    let refusal = |input| publish_claim(&store, input).unwrap_err().to_string();
    assert!(refusal(claim_input(other_meaning, &theorems, declaration("100"))).contains("meaning"));
    assert!(refusal(claim_input(statement, &["gendb_entry::theorem_build_total"], declaration("100"))).contains("theorem_end_to_end"));
    assert!(refusal(claim_input(statement, &["gendb_entry::theorem_end_to_end", "gendb_entry::corollary_missing"], declaration("100"))).contains("does not define"));
    assert!(refusal(claim_input(statement, &theorems, declaration("50"))).contains("free parameters"));
    let claim = publish_claim(&store, claim_input(statement, &theorems, declaration("100"))).unwrap();
    let claim_of_other_statement = store
        .put(1, VERUS_SQL_CLAIM_KIND, &VerusSqlClaimV1 { statement: other_meaning, ..store.read(claim).unwrap().decode().unwrap() })
        .unwrap();

    let repr = publish_representation_v2(&store, &VerusRepresentationV2 {
        build, name: "copy".into(), sources: vec![VerusSourceTableV2 { table: "t".into(), fields: vec![(0, column("x", ColType::I32))] }],
        parts: vec!["i32".into()], decode_item: "agent::decode".into(), builder_item: "agent::build".into(),
    })
    .unwrap();
    let evidence = store.put(1, "verus-build-observation-fixture", &true).unwrap();
    let asset_key = VerusAssetKeyV2::current(repr, &store.read(repr).unwrap().decode().unwrap(), &|_: &str| Ok(("v1".into(), 3))).unwrap();
    let asset = publish_asset_v2(&store, asset_key, dir.join("asset"), 1, 12, evidence).unwrap();
    let package = |claim, abi_version| {
        store
            .put(1, VERUS_QUERY_PACKAGE_V2_KIND, &VerusQueryPackageV2 {
                statement, claim, entry_identity: VERUS_ENTRY_V3_IDENTITY.into(), build, representation: repr, implementations: vec![],
                abi_version, workers: (1, 64), tcb,
            })
            .unwrap()
    };
    let admission = |package| VerusPackageAdmissionV1 { package, gate_identity: "gate".into(), qualification_evidence: vec![evidence], assets: vec![asset] };
    let refusal = |admission: &VerusPackageAdmissionV1, framework: &[(&str, &str)]| admit_package_v3(&store, admission, framework).unwrap_err().to_string();
    assert!(refusal(&admission(package(claim, 2)), &framework).contains("ABI v2"));
    assert!(refusal(&admission(package(claim_of_other_statement, 3)), &framework).contains("claim"));
    let p = package(claim, 3);
    let mut stale = framework.clone();
    stale[0].1 = "//! other SQL\nuse vstd::prelude::*;\nMEANING x < 7\n";
    assert!(refusal(&admission(p), &stale).contains("meaning"));
    assert!(refusal(&admission(p), &framework[1..]).contains("query.rs"));
    let mut weakened = framework.clone();
    weakened[3].1 = "pub proof fn theorem_end_to_end() {} // weakened";
    assert!(refusal(&admission(p), &weakened).contains("differs"));
    assert!(refusal(&VerusPackageAdmissionV1 { qualification_evidence: vec![], ..admission(p) }, &framework).contains("evidence"));
    assert!(resolve_package_v3(&store, statement).unwrap().is_none());
    let admitted = admit_package_v3(&store, &admission(p), &framework).unwrap();
    let resolved = resolve_package_v3(&store, statement).unwrap().unwrap();
    assert_eq!((resolved.admission_id, resolved.package.claim, resolved.key.free.clone()), (admitted, claim, free("100")));
    assert!(resolve_package_v3(&store, other_domain).unwrap().is_none(), "another free domain is another statement");
    assert!(resolve_package_v3(&store, other_meaning).unwrap().is_none(), "another fixed value is another statement");
}
