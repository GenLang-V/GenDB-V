//! The evaluator crate's generated files on real statements (Python parser, no Verus): the constraint fixture schema
//! (keys, composite and cross-type foreign keys, CHECKs with integer division and CASE) through the parser, the
//! decoder, the translator's `schema_spec` and the evaluator's executable schema module: every constraint is emitted
//! (none dropped), CHECK arenas as chains, and every case of the constraint fixture emits deterministically. With
//! `GENDB_SQL_EMIT_DIR` set, the modules are written there for a pinned-Verus check.

use gendb_frontend::ast::{AstDocument, Translation};
use gendb_frontend::parser::SqlParser;
use gendb_frontend::translator::{emit_query_module, EmitOptions};
use gendb_sqlspec::evaluator::{crate_files, echo_text, schema_module};
use gendb_sqlspec::fixtures::{fixtures_dir, CaseQuery, Fixture};
use std::path::{Path, PathBuf};

/// A fresh scratch directory for one translation (inputs of the parser are files).
fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("sqlspec-evaluator-crate-{}-{name}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn translate(parser: &SqlParser, ddl: &str, sql: &str, name: &str) -> AstDocument {
    let dir = scratch(name);
    let (schema, query) = (dir.join("schema.sql"), dir.join("query.sql"));
    std::fs::write(&schema, ddl).unwrap();
    std::fs::write(&query, sql).unwrap();
    let (_, translation) = parser.translate(&schema, &query, "postgres", &[]).unwrap();
    std::fs::remove_dir_all(&dir).unwrap();
    match translation {
        Translation::Ok(doc) => doc,
        Translation::Refused(r) => panic!("{name} refused: {r:?}"),
    }
}

/// Emit twice (deterministic) and optionally write the modules for the Verus check.
fn emit_checked(name: &str, doc: &AstDocument) {
    let module = emit_query_module(doc, &EmitOptions::default()).unwrap();
    let schema = schema_module(doc).unwrap();
    assert_eq!(module, emit_query_module(doc, &EmitOptions::default()).unwrap());
    assert_eq!(schema, schema_module(doc).unwrap());
    if let Some(dir) = std::env::var_os("GENDB_SQL_EMIT_DIR") {
        std::fs::write(Path::new(&dir).join(format!("{name}.rs")), &module).unwrap();
        std::fs::write(Path::new(&dir).join(format!("{name}_schema.rs")), &schema).unwrap();
    }
}

#[test]
fn constraint_schema_emits() {
    let parser = SqlParser::from_environment().unwrap();
    let ddl = std::fs::read_to_string(fixtures_dir().join("constraints/cov_c_schema.sql")).unwrap();
    let doc = translate(&parser, &ddl, "SELECT f.id, p.v FROM fkf f JOIN pk2 p ON f.y = p.b AND f.x = p.a", "join");
    let declared: usize = doc.tables.iter().map(|t| t.constraints.len()).sum();
    let module = emit_query_module(&doc, &EmitOptions::default()).unwrap();
    let schema = schema_module(&doc).unwrap();
    assert_eq!(module.matches("Constraint::").count(), declared);
    assert_eq!(schema.matches("EConstraint::").count(), declared);
    assert_eq!(module.matches("Constraint::Check(").count(), 4);
    emit_checked("cov_c", &doc);

    // The whole evaluator crate: library modules, generated files, entry and shim, echo of the translated AST.
    let files = crate_files(&doc).unwrap();
    let paths: Vec<&str> = files.iter().map(|f| f.path.as_str()).collect();
    for needed in ["lib.rs", "query.rs", "query_schema.rs", "abi.rs", "shim.rs", "spec/mod.rs", "exec/relational/entry.rs", "bridge/mod.rs"] {
        assert!(paths.contains(&needed), "{needed}");
    }
    assert!(!paths.iter().any(|p| p.starts_with("link") || p.starts_with("pins")));
    assert!(echo_text(&doc).starts_with("(OrderedQuery "));

    let fixture = Fixture::load(&fixtures_dir().join("pg_reference/cov_c.json")).unwrap();
    for case in &fixture.cases {
        let CaseQuery::Sql(sql) = &case.query else { panic!("{}: labelled query", case.name) };
        emit_checked(&format!("cov_c_{}", case.name), &translate(&parser, &fixture.ddl, sql, &case.name));
    }
}
