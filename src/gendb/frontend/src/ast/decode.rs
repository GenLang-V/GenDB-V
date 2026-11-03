//! Decoding and validation of a parser document (either status).
//!
//! Every structural rule is checked, without recursion (so any depth decodes): known tags, exactly the schema's keys,
//! value kinds and machine ranges, children are earlier nodes of the right sort with exactly one parent, the root is
//! the last node and an `OrderedQuery`, literals are valid (the Verus `type_lit` conditions), table ids exist in the
//! schema, declared parameters match their `Param` nodes, and the output metadata matches the root's arity. Typing
//! beyond literals is checked by the verified checker of the semantics library, not here.

mod arena;
mod tables;
mod types;

use super::document::{Annotation, AstDocument, Node, Output, Refusal, Translation};
use super::schema::schema;
use super::{err, AstError};
use crate::params::{DocParam, ParamType};
use serde_json::{Map, Value};

/// Decode a parser document (either status).
pub fn decode(text: &str) -> Result<Translation, AstError> {
    let v: Value = serde_json::from_str(text).map_err(|e| AstError(format!("not JSON: {e}")))?;
    let top = v.as_object().ok_or_else(|| AstError("document must be an object".into()))?;
    if top.get("format").and_then(Value::as_str) != Some(schema().format.as_str()) {
        return err(format!("format is not {}", schema().format));
    }
    match top.get("status").and_then(Value::as_str) {
        Some("ok") => decode_statement(top).map(Translation::Ok),
        Some("refused") => decode_refusal(top).map(Translation::Refused),
        _ => err("status must be ok or refused"),
    }
}

fn decode_refusal(top: &Map<String, Value>) -> Result<Refusal, AstError> {
    expect_keys(top, &["format", "status", "frontend", "sql", "refusal"], "document")?;
    let r = object(top, "refusal")?;
    expect_keys(r, &["reason", "meaning", "detail", "path", "sql"], "refusal")?;
    Ok(Refusal { reason: string(r, "reason")?, detail: string(r, "detail")?, path: string(r, "path")?, sql: string(r, "sql")? })
}

fn decode_statement(top: &Map<String, Value>) -> Result<AstDocument, AstError> {
    let mut keys = vec!["format", "status", "frontend", "sql", "schema", "output", "root", "nodes"];
    if top.contains_key("params") {
        keys.push("params");
    }
    expect_keys(top, &keys, "document")?;
    let tables = tables::decode_tables(object(top, "schema")?)?;
    let params = match top.get("params") {
        Some(p) => decode_params(p)?,
        None => Vec::new(),
    };
    let raw_nodes = top.get("nodes").and_then(Value::as_array).ok_or_else(|| AstError("nodes must be a list".into()))?;
    let nodes = arena::decode_arena(raw_nodes, tables.len())?;
    check_params(&nodes, &params)?;
    let root = arena_root(&nodes, &top["root"])?;
    let sch = schema();
    if sch.kinds[&nodes[root].tag].sort != sch.root_sort {
        return err(format!("root must be a {}", sch.root_sort));
    }
    let output = decode_output(object(top, "output")?)?;
    let body = nodes[root].child("body").ok_or_else(|| AstError("root has no body".into()))?;
    match &nodes[body].annotation {
        Some(Annotation::Columns(cols)) if cols.len() == output.names.len() && cols == &output.columns => {}
        _ => return err("output metadata disagrees with the root body's columns"),
    }
    Ok(AstDocument { frontend: top["frontend"].clone(), sql: string(top, "sql")?, tables, output, params, nodes, root })
}

/// The root of a post-order arena: it must be the last node.
pub(super) fn arena_root(nodes: &[Node], raw_root: &Value) -> Result<usize, AstError> {
    let root = raw_root.as_u64().ok_or_else(|| AstError("root must be a node id".into()))?;
    if nodes.is_empty() || root != (nodes.len() - 1) as u64 {
        return err("root must be the last node");
    }
    Ok(root as usize)
}

/// The `params` section: `[{index, type}]`, indices >= 1 strictly ascending, parameter types only.
fn decode_params(v: &Value) -> Result<Vec<DocParam>, AstError> {
    let list = v.as_array().ok_or_else(|| AstError("params must be a list".into()))?;
    let mut out: Vec<DocParam> = Vec::new();
    for p in list {
        let o = p.as_object().ok_or_else(|| AstError("param: not an object".into()))?;
        expect_keys(o, &["index", "type"], "param")?;
        let index = o["index"].as_u64().filter(|&i| i >= 1 && i <= u32::MAX as u64).ok_or_else(|| AstError("param.index".into()))? as u32;
        if out.last().is_some_and(|q| q.index >= index) {
            return err("params must have strictly ascending indices");
        }
        let ty = ParamType::from_pg(&types::decode_pg_type(&o["type"])?).ok_or_else(|| AstError(format!("${index}: not a parameter type")))?;
        out.push(DocParam { index, ty });
    }
    Ok(out)
}

/// Every `Param` node is a declared parameter under a `Lit` of the declared type; every declared parameter occurs.
pub(super) fn check_params(nodes: &[Node], params: &[DocParam]) -> Result<(), AstError> {
    let mut occurs = vec![false; params.len()];
    for (i, n) in nodes.iter().enumerate() {
        let Some(literal) = (n.tag == "Lit").then(|| n.child("lit")).flatten() else { continue };
        let Some(index) = nodes[literal].param_index() else { continue };
        let k = params.iter().position(|p| p.index == index).ok_or_else(|| AstError(format!("node {literal}: ${index} is not declared")))?;
        occurs[k] = true;
        if n.annotation != Some(Annotation::Type(params[k].ty.coltype())) {
            return err(format!("node {i}: the type of ${index} differs from its declaration"));
        }
    }
    if let Some(k) = occurs.iter().position(|o| !o) {
        return err(format!("${} is declared but does not occur", params[k].index));
    }
    Ok(())
}

fn decode_output(o: &Map<String, Value>) -> Result<Output, AstError> {
    expect_keys(o, &["names", "columns", "pg_types"], "output")?;
    let strings = |k: &str| -> Result<Vec<String>, AstError> {
        o[k].as_array()
            .ok_or_else(|| AstError(format!("output.{k}")))?
            .iter()
            .map(|x| x.as_str().map(str::to_owned).ok_or_else(|| AstError(format!("output.{k}"))))
            .collect()
    };
    let columns = o["columns"].as_array().ok_or_else(|| AstError("output.columns".into()))?.iter().map(types::decode_coltype).collect::<Result<Vec<_>, _>>()?;
    let (names, pg_types) = (strings("names")?, strings("pg_types")?);
    if names.len() != columns.len() || pg_types.len() != columns.len() {
        return err("output lists differ in length");
    }
    Ok(Output { names, columns, pg_types })
}

// JSON access with the decoder's error messages.

fn object<'a>(o: &'a Map<String, Value>, k: &str) -> Result<&'a Map<String, Value>, AstError> {
    o.get(k).and_then(Value::as_object).ok_or_else(|| AstError(format!("{k} must be an object")))
}

fn string(o: &Map<String, Value>, k: &str) -> Result<String, AstError> {
    o.get(k).and_then(Value::as_str).map(str::to_owned).ok_or_else(|| AstError(format!("{k} must be a string")))
}

/// `o` has exactly the keys `keys` (no silently ignored input).
fn expect_keys(o: &Map<String, Value>, keys: &[&str], what: &str) -> Result<(), AstError> {
    let mut have: Vec<&str> = o.keys().map(String::as_str).collect();
    let mut want = keys.to_vec();
    have.sort_unstable();
    want.sort_unstable();
    if have != want {
        return err(format!("{what}: keys {have:?}, expected {want:?}"));
    }
    Ok(())
}
