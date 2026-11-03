//! The post-order node arena: each node is decoded against its kind in the encoding schema, its children are claimed
//! (earlier ids, right sort, exactly one parent), its annotation is decoded, and its literal validity is checked.

use super::super::document::{Annotation, FieldValue, Node};
use super::super::literals::{canonical_int, check_literal_and_table};
use super::super::schema::{schema, AstSchema, ChildMode, FieldKind};
use super::super::{err, AstError};
use super::expect_keys;
use super::types::{decode_coltype, decode_scalar_ty};
use serde_json::{Map, Value};

/// Decode the arena `raw` of a document or CHECK constraint whose schema has `table_count` tables. Every node except
/// the last must have exactly one parent.
pub(in crate::ast) fn decode_arena(raw: &[Value], table_count: usize) -> Result<Vec<Node>, AstError> {
    let mut arena = ArenaDecoder { schema: schema(), table_count, nodes: Vec::with_capacity(raw.len()), has_parent: vec![false; raw.len()] };
    for (id, v) in raw.iter().enumerate() {
        let node = arena.decode_node(id, v)?;
        arena.nodes.push(node);
    }
    if let Some(orphan) = arena.has_parent.iter().take(raw.len().saturating_sub(1)).position(|p| !p) {
        return err(format!("node {orphan} has no parent"));
    }
    Ok(arena.nodes)
}

struct ArenaDecoder<'s> {
    schema: &'s AstSchema,
    table_count: usize,
    /// The nodes decoded so far (ids `0..nodes.len()`).
    nodes: Vec<Node>,
    has_parent: Vec<bool>,
}

impl ArenaDecoder<'_> {
    fn decode_node(&mut self, id: usize, v: &Value) -> Result<Node, AstError> {
        let o = v.as_object().ok_or_else(|| AstError(format!("node {id}: not an object")))?;
        if o.get("id").and_then(Value::as_u64) != Some(id as u64) {
            return err(format!("node {id}: id must equal its position"));
        }
        let tag = o.get("tag").and_then(Value::as_str).ok_or_else(|| AstError(format!("node {id}: tag")))?;
        let schema = self.schema;
        let kind = schema.kinds.get(tag).ok_or_else(|| AstError(format!("node {id}: unknown tag {tag}")))?;
        let annotation_key = match schema.annotations.get(&kind.sort).map(String::as_str) {
            Some("coltype") => Some("type"),
            Some("coltypes") => Some("columns"),
            _ => None,
        };
        let mut keys: Vec<&str> = vec!["id", "tag"];
        keys.extend(kind.fields.iter().map(|(n, _)| n.as_str()));
        keys.extend(annotation_key);
        expect_keys(o, &keys, &format!("node {id} ({tag})"))?;
        let mut fields = Vec::with_capacity(kind.fields.len());
        for (name, field_kind) in &kind.fields {
            let at = format!("node {id} ({tag}).{name}");
            fields.push(self.decode_field(id, &at, field_kind, &o[name.as_str()])?);
        }
        let annotation = match annotation_key {
            Some(key) => Some(decode_annotation(id, key, o)?),
            None => None,
        };
        let node = Node { tag: tag.to_owned(), fields, annotation };
        check_literal_and_table(&node, self.table_count).map_err(|e| AstError(format!("node {id}: {}", e.0)))?;
        Ok(node)
    }

    /// Field value `x` of node `id` (`at` names the field in errors).
    fn decode_field(&mut self, id: usize, at: &str, kind: &FieldKind, x: &Value) -> Result<FieldValue, AstError> {
        Ok(match kind {
            FieldKind::Child(ChildMode::Seq, sort) => {
                let list = x.as_array().ok_or_else(|| AstError(format!("{at}: expected a list")))?;
                FieldValue::Children(list.iter().map(|r| self.claim_child(id, at, r, sort)).collect::<Result<_, _>>()?)
            }
            FieldKind::Child(_, sort) => FieldValue::Child(self.claim_child(id, at, x, sort)?),
            FieldKind::Int(_) => FieldValue::Int(canonical_int(x).ok_or_else(|| AstError(format!("{at}: canonical decimal string")))?),
            FieldKind::Nat(_) => FieldValue::Nat(x.as_u64().ok_or_else(|| AstError(format!("{at}: non-negative integer")))?),
            FieldKind::OptNat(_) => FieldValue::OptNat(if x.is_null() {
                None
            } else {
                Some(x.as_u64().ok_or_else(|| AstError(format!("{at}: null or non-negative integer")))?)
            }),
            FieldKind::Fixed(m) => FieldValue::Fixed(x.as_i64().filter(|n| m.fits(&n.to_string())).ok_or_else(|| AstError(format!("{at}: integer outside {m:?}")))?),
            FieldKind::Bool => FieldValue::Bool(x.as_bool().ok_or_else(|| AstError(format!("{at}: bool")))?),
            FieldKind::Bytes => FieldValue::Bytes(x.as_str().filter(|s| !s.contains('\0')).ok_or_else(|| AstError(format!("{at}: text without NUL")))?.to_owned()),
            FieldKind::ScalarTy => FieldValue::ScalarTy(decode_scalar_ty(x).ok_or_else(|| AstError(format!("{at}: scalar type")))?),
            FieldKind::Enum(e) => {
                let value = x.as_str().filter(|s| self.schema.enums[e].iter().any(|v| v == s)).ok_or_else(|| AstError(format!("{at}: not a {e}")))?;
                FieldValue::Enum(value.to_owned())
            }
        })
    }

    /// Claim `r` as a child of node `id`: an earlier node of sort `sort` without a parent yet.
    fn claim_child(&mut self, id: usize, at: &str, r: &Value, sort: &str) -> Result<usize, AstError> {
        let c = r.as_u64().filter(|&c| (c as usize) < id).ok_or_else(|| AstError(format!("{at}: child must be an earlier node id")))? as usize;
        if self.has_parent[c] {
            return err(format!("{at}: node {c} already has a parent"));
        }
        if self.schema.kinds[&self.nodes[c].tag].sort != sort {
            return err(format!("{at}: node {c} is not a {sort}"));
        }
        self.has_parent[c] = true;
        Ok(c)
    }
}

/// The parser's annotation under `key` (`type` of an expression, `columns` of a query).
fn decode_annotation(id: usize, key: &str, o: &Map<String, Value>) -> Result<Annotation, AstError> {
    if key == "type" {
        return Ok(Annotation::Type(decode_coltype(&o["type"]).map_err(|e| AstError(format!("node {id} type: {}", e.0)))?));
    }
    let cols = o["columns"].as_array().ok_or_else(|| AstError(format!("node {id}: columns must be a list")))?;
    let columns = cols.iter().map(decode_coltype).collect::<Result<_, _>>().map_err(|e| AstError(format!("node {id} columns: {}", e.0)))?;
    Ok(Annotation::Columns(columns))
}
