//! Parser, decoder and translator on real statements (Python parser, no Verus): the TPC-H schema's constraints decode,
//! and TPC-H Q6/Q3/Q4 and one query composing the other core constructors translate deterministically. With
//! `GENDB_SQL_EMIT_DIR` set, the modules are written there for one pinned-Verus check over the SQLSpec library.
//!
//! The constraint-fixture emission check (`cov_c`) needs the evaluator's executable schema module and the PostgreSQL
//! reference fixtures, so it lives with the SQLSpec host.

use gendb_frontend::ast::{self, AstDocument, ConstraintDef, Translation};
use gendb_frontend::parser::SqlParser;
use gendb_frontend::translator::{emit_query_module, EmitOptions};
use serde_json::Value;
use std::path::{Path, PathBuf};

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..")
}

fn tpch(label: &str) -> (String, Translation) {
    SqlParser::from_environment()
        .unwrap()
        .translate_labelled(&repo().join("src/gendb/fixtures/tpch-spec/schema.sql"), &repo().join("src/gendb/fixtures/tpch-spec/queries.sql"), label, "postgres")
        .unwrap()
}

/// Translate twice (deterministic) and optionally write the module for the Verus check.
fn emit_checked(name: &str, doc: &AstDocument) {
    let module = emit_query_module(doc, &EmitOptions::default()).unwrap();
    assert_eq!(module, emit_query_module(doc, &EmitOptions::default()).unwrap());
    if let Some(dir) = std::env::var_os("GENDB_SQL_EMIT_DIR") {
        std::fs::write(Path::new(&dir).join(format!("{name}.rs")), &module).unwrap();
    }
}

/// Constraints of the TPC-H schema decode (lineitem: FK to orders, composite PK, composite FK to partsupp); a CHECK
/// arena decodes as a `pred`; malformed constraints are rejected; a pre-v3 table without the `constraints` key decodes
/// with none.
#[test]
fn decoder_reads_constraints() {
    let (text, doc) = tpch("Q6");
    let Translation::Ok(doc) = doc else { panic!("Q6 refused") };
    let lineitem = &doc.tables[7].constraints;
    assert!(matches!(&lineitem[0], ConstraintDef::ForeignKey { columns, table: 6, ref_columns, match_full: false, .. } if columns == &[0] && ref_columns == &[0]));
    assert!(matches!(&lineitem[1], ConstraintDef::Key { primary: true, columns, nulls_distinct: true, .. } if columns == &[0, 3]));
    assert!(matches!(&lineitem[2], ConstraintDef::ForeignKey { columns, table: 4, ref_columns, .. } if columns == &[1, 2] && ref_columns == &[0, 1]));
    let v: Value = serde_json::from_str(&text).unwrap();
    let corrupt = |f: &dyn Fn(&mut Value)| {
        let mut w = v.clone();
        f(&mut w);
        ast::decode(&w.to_string()).unwrap_err().0
    };
    let e = corrupt(&|w| w["schema"]["tables"][7]["constraints"][1]["columns"] = serde_json::json!([0, 16]));
    assert!(e.contains("outside the table"), "{e}");
    let e = corrupt(&|w| w["schema"]["tables"][7]["constraints"][2]["table"] = serde_json::json!(8));
    assert!(e.contains("table id"), "{e}");
    let e = corrupt(&|w| w["schema"]["tables"][7]["constraints"][2]["ref_columns"] = serde_json::json!([0, 9]));
    assert!(e.contains("referenced column outside"), "{e}");
    let e = corrupt(&|w| w["schema"]["tables"][7]["constraints"][0]["on_delete"] = serde_json::json!("cascade_all"));
    assert!(e.contains("on_delete"), "{e}");
    let e = corrupt(&|w| w["schema"]["tables"][7]["constraints"][0]["match"] = serde_json::json!("partial"));
    assert!(e.contains("keys"), "{e}");
    let e = corrupt(&|w| w["schema"]["tables"][7]["constraints"][1]["kind"] = serde_json::json!("exclude"));
    assert!(e.contains("kind"), "{e}");
    // A CHECK whose root is an expression, not a pred.
    let e = corrupt(&|w| {
        w["schema"]["tables"][7]["constraints"][0] = serde_json::json!({"kind": "check", "name": null, "root": 0,
            "nodes": [{"id": 0, "tag": "Col", "index": 0, "type": {"type": {"kind": "int4"}, "nullable": false, "dscale": null}}]});
    });
    assert!(e.contains("must be a pred"), "{e}");
    // A well-formed CHECK decodes; a pre-v3 table without `constraints` decodes with none.
    let mut w = v.clone();
    w["schema"]["tables"][0]["constraints"] = serde_json::json!([{"kind": "check", "name": "c", "root": 1, "nodes": [
        {"id": 0, "tag": "Col", "index": 0, "type": {"type": {"kind": "int4"}, "nullable": false, "dscale": null}},
        {"id": 1, "tag": "IsNull", "e": 0}]}]);
    w["schema"]["tables"][1].as_object_mut().unwrap().remove("constraints");
    let Translation::Ok(d) = ast::decode(&w.to_string()).unwrap() else { panic!() };
    assert!(matches!(&d.tables[0].constraints[0], ConstraintDef::Check { root: 1, nodes, .. } if nodes.len() == 2));
    assert!(d.tables[1].constraints.is_empty());
}

/// TPC-H Q6, Q3 and Q4 (standard texts) through the parser, the decoder and the translator.
#[test]
fn tpch_core_queries_emit() {
    for label in ["Q6", "Q3", "Q4"] {
        let (_, doc) = tpch(label);
        let Translation::Ok(doc) = doc else { panic!("{label} refused: {doc:?}") };
        emit_checked(&label.to_lowercase(), &doc);
    }
}

/// One query composing the other core constructors (derived table, LEFT JOIN, HAVING, IN list, IS NOT NULL, unary minus,
/// int4 -> int8 casts, SUM(int8) -> numeric, NULLS FIRST) over nullable tables.
#[test]
fn composed_core_query_emits() {
    let dir = std::env::temp_dir().join(format!("gendb-frontend-emit-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let (schema, sql) = (dir.join("schema.sql"), dir.join("query.sql"));
    std::fs::write(&schema, "CREATE TABLE r (k integer, v numeric(10,2), tag text);\nCREATE TABLE s (k integer, w integer);").unwrap();
    std::fs::write(
        &sql,
        "SELECT d.k, COUNT(*) AS n, SUM(d.w8) AS total, SUM(r.v) AS v \
         FROM (SELECT s.k, s.w + 5000000000 AS w8 FROM s WHERE s.w IS NOT NULL OR s.k IN (1, 4)) AS d \
         LEFT JOIN r ON r.k = d.k AND NOT r.tag = 'x' \
         WHERE -d.k < 0 GROUP BY d.k HAVING COUNT(r.v) >= 0 ORDER BY 1 NULLS FIRST",
    )
    .unwrap();
    let (_, doc) = SqlParser::from_environment().unwrap().translate(&schema, &sql, "postgres", &[]).unwrap();
    std::fs::remove_dir_all(&dir).unwrap();
    let Translation::Ok(doc) = doc else { panic!("refused: {doc:?}") };
    emit_checked("composed", &doc);
}
