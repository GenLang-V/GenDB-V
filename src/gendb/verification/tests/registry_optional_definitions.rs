//! The registry's optional definitions (`gendb_registry::Presence::Optional`) against the crates the generators
//! assemble (no Verus, no I/O). The always-present definitions of every crate kind are checked by
//! `obligations::tests::registry_matches_the_assembled_crates`; this file checks the crates whose storages call for
//! generated files:
//! - an engine crate over generated flat storages carries `flat_tables.rs` and `flat_tables/plain.rs`
//!   (`flat_tables`, `flat_tables_plain`);
//! - a storage crate built from admitted storages carries `gendb_entry/sources.rs` (`derived_sources`) and
//!   `gendb_entry/derivation.rs` (`derived_derivation`), plus `sources_flat.rs` and `sources_flat/plain.rs`
//!   (`sources_flat`, `sources_flat_plain`) when a source is a generated flat storage, and has no source binding of
//!   source columns (`storage_source`, `storage_column_binder`);
//! - a storage whose author copies the plain-columns vocabulary into its interface carries
//!   `stores/<name>/interface/plain.rs` (`plain_columns`), the same text as the generated copies;
//! - crates without such storages carry none of them.

use gendb_frontend::ast::{decode, Translation};
use gendb_frontend::params::Instance;
use gendb_registry::{definitions_for, optional_definitions_for, ConstraintMode, CrateKind, Presence, DEFINITIONS};
use gendb_verification::obligations::{
    derived_storage_crate_files, engine_crate_files, flat_storage, interpreter_engine, plain_columns_interface_file, storage_crate_files, DeclaredSource,
    Derivation, FlatStorage, StorageName, StorageUse, PLAIN_COLUMNS,
};
use gendb_verification::verus::FrameworkSource;
use std::collections::{BTreeMap, BTreeSet};

/// `SELECT c FROM t` over `t(c integer, d date)` (table 0) and `u(e bigint)` (table 1), both NOT NULL; with `constrained`
/// the dataset declares `PRIMARY KEY (c)` on `t` (engine crates exist only under declared constraints). The same
/// statement as the obligations unit tests' small statement.
fn small_statement(constrained: bool) -> Instance {
    let constraints = if constrained {
        r#""constraints": [{"kind": "key", "name": null, "primary": true, "columns": [0], "nulls_distinct": true, "deferrable": false, "initially_deferred": false}]"#
    } else {
        r#""constraints": []"#
    };
    let doc = r#"{"format": "gendb-sql-ast-v1", "status": "ok", "frontend": {"identity": "unit"}, "sql": "SELECT c FROM t",
        "schema": {"tables": [
            {"name": "t", "columns": [{"name": "c", "type": {"kind": "int4"}, "nullable": false}, {"name": "d", "type": {"kind": "date"}, "nullable": false}], CONSTRAINTS},
            {"name": "u", "columns": [{"name": "e", "type": {"kind": "int8"}, "nullable": false}]}]},
        "output": {"names": ["c"], "columns": [{"type": {"kind": "int4"}, "nullable": false, "dscale": null}], "pg_types": ["int4"]},
        "root": 3, "nodes": [
          {"id": 0, "tag": "Table", "table": 0, "columns": [{"type": {"kind": "int4"}, "nullable": false, "dscale": null}, {"type": {"kind": "date"}, "nullable": false, "dscale": null}]},
          {"id": 1, "tag": "Col", "index": 0, "type": {"type": {"kind": "int4"}, "nullable": false, "dscale": null}},
          {"id": 2, "tag": "Project", "exprs": [1], "input": 0, "columns": [{"type": {"kind": "int4"}, "nullable": false, "dscale": null}]},
          {"id": 3, "tag": "OrderedQuery", "body": 2, "keys": [], "limit": null, "offset": 0}]}"#;
    let Translation::Ok(doc) = decode(&doc.replace("CONSTRAINTS", constraints)).unwrap() else { panic!("refused") };
    Instance::concrete(&doc).unwrap()
}

/// The interface files of a flat storage (`stores/<name>/interface/**`).
fn flat_interface(flat: &FlatStorage) -> Vec<FrameworkSource> {
    flat.files.iter().filter(|f| f.path.starts_with(&flat.name.interface_prefix())).cloned().collect()
}

fn file(path: &str, text: &str) -> FrameworkSource {
    FrameworkSource { path: path.into(), text: text.into() }
}

/// Check one assembled crate of `kind` in `mode` whose storages are named `storages`: every file belongs to an
/// always-present or optional definition of the kind (for one of the names); every always-present definition is in
/// the crate except those named in `absent`; exactly the optional definitions named in `present` are in it.
fn check(what: &str, kind: CrateKind, mode: ConstraintMode, files: &[FrameworkSource], storages: &[&str], absent: &[&str], present: &[&str]) {
    let carried = |name: &str| {
        let d = DEFINITIONS.iter().find(|d| d.name == name).unwrap();
        files.iter().any(|f| storages.iter().any(|s| d.covers(&f.path, s)))
    };
    for f in files {
        let covering = definitions_for(kind, mode).chain(optional_definitions_for(kind, mode)).find(|d| storages.iter().any(|s| d.covers(&f.path, s)));
        assert!(covering.is_some(), "{what}: {} is in no definition of {kind:?} {mode:?}", f.path);
    }
    for d in definitions_for(kind, mode) {
        assert_eq!(carried(d.name), !absent.contains(&d.name), "{what}: always-present definition {}", d.name);
    }
    for d in optional_definitions_for(kind, mode) {
        assert_eq!(carried(d.name), present.contains(&d.name), "{what}: optional definition {}", d.name);
    }
}

#[test]
fn optional_definitions_describe_the_crates_that_carry_them() {
    // Engine crates (declared constraints): over the flat storage of every table, and over one plain storage.
    let inst = small_statement(true);
    let schema = &inst.doc.tables;
    let flats: Vec<FlatStorage> = (0..schema.len()).map(|t| flat_storage(schema, t).unwrap()).collect();
    let interfaces: Vec<Vec<FrameworkSource>> = flats.iter().map(flat_interface).collect();
    let uses: Vec<StorageUse<'_>> = flats.iter().zip(&interfaces).map(|(f, i)| StorageUse { name: &f.name, declaration: &f.declaration, interface: i }).collect();
    let mut flat_engine = engine_crate_files(schema, &uses, "unit").unwrap();
    flat_engine.extend(interpreter_engine(schema, &uses).unwrap());
    let names: Vec<&str> = flats.iter().map(|f| f.name.as_str()).collect();
    check("engine over flat storages", CrateKind::Engine, ConstraintMode::Declared, &flat_engine, &names, &[], &["flat_tables", "flat_tables_plain"]);
    let t_all = StorageName::new("t_all").unwrap();
    let declaration = DeclaredSource::for_storage(schema, &BTreeMap::from([(0, BTreeSet::from([0, 1]))])).unwrap();
    let interface = vec![file("stores/t_all/interface/mod.rs", "// interface")];
    let plain = [StorageUse { name: &t_all, declaration: &declaration, interface: &interface }];
    let mut engine = engine_crate_files(schema, &plain, "unit").unwrap();
    engine.push(file("agent/mod.rs", "// agent"));
    check("engine over a plain storage", CrateKind::Engine, ConstraintMode::Declared, &engine, &["t_all"], &[], &[]);

    // Storage crates (no declared constraints): built from a flat storage, built from a plain storage, and from source
    // columns.
    let inst = small_statement(false);
    let schema = &inst.doc.tables;
    let flat = flat_storage(schema, 0).unwrap();
    let flat_files = flat_interface(&flat);
    let flat_source = [StorageUse { name: &flat.name, declaration: &flat.declaration, interface: &flat_files }];
    let copy = StorageName::new("t_copy").unwrap();
    let author = [file("stores/t_copy/interface/mod.rs", "// interface"), file("builder/mod.rs", "// builder")];
    let derived_absent = ["storage_source", "storage_column_binder"];
    let mut over_flat = derived_storage_crate_files(schema, &copy, &flat.declaration, Derivation { sources: &flat_source, extends: Some(0) }, false).unwrap();
    over_flat.extend(author.iter().cloned());
    check("derived over a flat storage", CrateKind::Storage, ConstraintMode::Unconstrained, &over_flat, &[flat.name.as_str(), "t_copy"], &derived_absent,
        &["sources_flat", "sources_flat_plain", "derived_sources", "derived_derivation"]);
    // The author copies the plain-columns vocabulary into the interface: the same text as the generated copies.
    let mut with_plain = over_flat.clone();
    with_plain.push(plain_columns_interface_file(&copy));
    check("derived over a flat storage, interface with plain.rs", CrateKind::Storage, ConstraintMode::Unconstrained, &with_plain, &[flat.name.as_str(), "t_copy"],
        &derived_absent, &["sources_flat", "sources_flat_plain", "plain_columns", "derived_sources", "derived_derivation"]);
    for path in ["sources_flat/plain.rs", "stores/t_copy/interface/plain.rs"] {
        assert_eq!(with_plain.iter().find(|f| f.path == path).unwrap().text, PLAIN_COLUMNS, "{path}");
    }
    assert_eq!(flat_engine.iter().find(|f| f.path == "flat_tables/plain.rs").unwrap().text, PLAIN_COLUMNS);
    let declaration = DeclaredSource::for_storage(schema, &BTreeMap::from([(0, BTreeSet::from([0, 1]))])).unwrap();
    let plain = [StorageUse { name: &t_all, declaration: &declaration, interface: &interface }];
    let mut over_plain = derived_storage_crate_files(schema, &copy, &declaration, Derivation { sources: &plain, extends: None }, false).unwrap();
    over_plain.extend(author.iter().cloned());
    check("derived over a plain storage", CrateKind::Storage, ConstraintMode::Unconstrained, &over_plain, &["t_all", "t_copy"], &derived_absent,
        &["derived_sources", "derived_derivation"]);
    let mut from_columns = storage_crate_files(schema, &t_all, &declaration, false).unwrap();
    from_columns.extend([file("stores/t_all/interface/mod.rs", "// interface"), file("builder/mod.rs", "// builder")]);
    check("storage from source columns", CrateKind::Storage, ConstraintMode::Unconstrained, &from_columns, &["t_all"], &[], &[]);

    // The presence serializes with its kind (the contract renders it).
    assert_eq!(serde_json::to_value(Presence::Optional(CrateKind::Engine)).unwrap(), serde_json::json!({"optional":"engine"}));
}
