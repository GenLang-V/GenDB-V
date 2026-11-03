//! Boundary check on the saved accepted statements of an earlier run (Q6, the Q6 template and
//! Q4), without the Python parser or Verus: each saved parser document decodes, its saved parameter
//! requests bind through `declare` / `instantiate`, the candidate translation is byte-equal to the `query.rs` of the
//! admitted crate, and the column demand yields the saved source declaration and free parameters. The saved Q6
//! document also serves as the base of the decoder's structural-corruption checks.
//!
//! The saved run records are not part of this repository: without them these tests fail.

use gendb_frontend::ast::{self, AstDocument, Translation};
use gendb_frontend::columns;
use gendb_frontend::params::{self, Instance, ParamRequest};
use gendb_frontend::translator::{emit_instance_module, EmitOptions};
use serde_json::Value;
use std::path::PathBuf;

fn saved(statement: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../output/verified-agent-proofs").join(statement)
}

fn read(path: PathBuf) -> String {
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

fn saved_document(statement: &str) -> (String, AstDocument) {
    let text = read(saved(statement).join("query/ast.json"));
    let Translation::Ok(doc) = ast::decode(&text).unwrap() else { panic!("{statement}: saved document is a refusal") };
    (text, doc)
}

fn saved_instance(statement: &str) -> Instance {
    let (_, doc) = saved_document(statement);
    let requests: Vec<ParamRequest> = serde_json::from_str(&read(saved(statement).join("query/parameters.json"))).unwrap();
    params::instantiate(&doc, &params::declare(&doc, &requests).unwrap()).unwrap()
}

#[test]
fn saved_statements_translate_to_their_admitted_query_modules() {
    for statement in ["q6", "q6-template", "q4"] {
        let inst = saved_instance(statement);
        let emitted = emit_instance_module(&inst, &EmitOptions::candidate()).unwrap();
        let admitted = read(saved(statement).join("code/crate/src/query.rs"));
        assert!(emitted == admitted, "{statement}: the translation differs from the admitted crate's query.rs");

        let record: Value = serde_json::from_str(&read(saved(statement).join("query/statement.json"))).unwrap();
        let demand = columns::analyze(&inst.doc).unwrap();
        let declaration = columns::source_declaration(&inst.doc, &demand).unwrap();
        assert_eq!(serde_json::to_value(&declaration).unwrap(), record["source_declaration"], "{statement}: source declaration");
        let free: Vec<Value> = inst
            .free
            .iter()
            .map(|f| {
                let (min, max) = f.bounds().expect("saved statements have ordered parameters");
                serde_json::json!({"index": f.index, "slot": f.slot, "type": f.ty.sql_name(), "min": f.ty.text(min), "max": f.ty.text(max)})
            })
            .collect();
        assert_eq!(Value::Array(free), record["free_parameters"], "{statement}: free parameters");
    }
}

/// Structural corruptions of the saved Q6 document are rejected, each with its named rule.
#[test]
fn decoder_rejects_malformed_arenas() {
    let (text, _) = saved_document("q6");
    let v: Value = serde_json::from_str(&text).unwrap();
    let corrupt = |f: &dyn Fn(&mut Value)| {
        let mut w = v.clone();
        f(&mut w);
        ast::decode(&w.to_string()).unwrap_err().0
    };
    // A child that is shared by two parents (the arena must be a tree).
    let e = corrupt(&|w| w["nodes"][13]["a"] = w["nodes"][7]["a"].clone());
    assert!(e.contains("already has a parent"), "{e}");
    // A forward reference.
    let e = corrupt(&|w| w["nodes"][2]["a"] = serde_json::json!(5));
    assert!(e.contains("earlier node id"), "{e}");
    // An int4 literal out of range, and an impossible date.
    let e = corrupt(&|w| w["nodes"][32]["v"] = serde_json::json!("2147483648"));
    assert!(e.contains("outside its kind"), "{e}");
    let e = corrupt(&|w| w["nodes"][5]["d"] = serde_json::json!("32"));
    assert!(e.contains("calendar date"), "{e}");
    // An unknown field (no silently ignored input).
    let e = corrupt(&|w| w["nodes"][4]["extra"] = serde_json::json!(1));
    assert!(e.contains("keys"), "{e}");
}
