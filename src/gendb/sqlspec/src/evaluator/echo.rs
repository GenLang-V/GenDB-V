//! Echo text: the canonical s-expression of a statement AST that the evaluator shim renders from the compiled
//! executable AST (`abi_echo`, proved equal to `query_spec`). The host renders the translated AST document the same
//! way; equal texts show that the compiled crate evaluates exactly the translated AST (translation validation of
//! the emitter). The grammar is trusted and mirrored by `sqlspec/interpreter/host/shim.rs`.

use gendb_frontend::ast::{schema, AstDocument, FieldKind, FieldValue};
use std::fmt::Write as _;

/// `(Tag field ...)` per node in schema field order; children inline, lists `[a b]`, `none` / `(some n)`, scalar
/// types `(Numeric s)`, bytes `0x<hex>`. Bottom-up over the post-order arena, no recursion.
pub fn echo_text(doc: &AstDocument) -> String {
    let ast_schema = schema();
    let mut texts: Vec<String> = Vec::with_capacity(doc.nodes.len());
    for node in &doc.nodes {
        let kind = &ast_schema.kinds[&node.tag];
        let mut o = format!("({}", node.tag);
        for ((_, field_kind), value) in kind.fields.iter().zip(&node.fields) {
            o.push(' ');
            match (field_kind, value) {
                (_, FieldValue::Child(c)) => o.push_str(&std::mem::take(&mut texts[*c])),
                (_, FieldValue::Children(cs)) => {
                    let parts: Vec<String> = cs.iter().map(|c| std::mem::take(&mut texts[*c])).collect();
                    let _ = write!(o, "[{}]", parts.join(" "));
                }
                (_, FieldValue::Int(v)) => o.push_str(v),
                (_, FieldValue::Nat(v)) => {
                    let _ = write!(o, "{v}");
                }
                (_, FieldValue::Fixed(v)) => {
                    let _ = write!(o, "{v}");
                }
                (_, FieldValue::OptNat(None)) => o.push_str("none"),
                (_, FieldValue::OptNat(Some(v))) => {
                    let _ = write!(o, "(some {v})");
                }
                (_, FieldValue::Bool(b)) => {
                    let _ = write!(o, "{b}");
                }
                (FieldKind::Bytes, FieldValue::Bytes(s)) => {
                    o.push_str("0x");
                    for b in s.as_bytes() {
                        let _ = write!(o, "{b:02x}");
                    }
                }
                (_, FieldValue::ScalarTy(t)) => match t.scale {
                    Some(s) => {
                        let _ = write!(o, "({} {s})", t.kind);
                    }
                    None => {
                        let _ = write!(o, "({})", t.kind);
                    }
                },
                (_, FieldValue::Enum(e)) => o.push_str(e),
                (k, v) => unreachable!("decoded field {v:?} does not match kind {k:?}"),
            }
        }
        o.push(')');
        texts.push(o);
    }
    std::mem::take(&mut texts[doc.root])
}
