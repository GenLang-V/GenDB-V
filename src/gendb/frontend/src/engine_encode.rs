//! The host encoder of engine calls: a translated statement document and one binding become the AST bytes an engine
//! call reads (format `gendb-engine-ast-v1`, decoded by the engine crates' verified `gendb_ast_codec::decode_query`,
//! whose meaning is the fixed `decode_spec`; byte format documented in `runtime/verus/engine_codec.rs`).
//!
//! Two steps, in the order the design fixes:
//! 1. [`bind_document`]: the binding's values are substituted into the typed AST as literals (`params::declare` with
//!    every parameter fixed, then `params::instantiate`), AFTER the parser's constant-expression check (`SqlParser`
//!    applies it to every parser document, while parameters are still `Param` nodes). A parameter expression such as
//!    `$1 + INTERVAL '1' YEAR` therefore keeps SQLSpec's row-by-row meaning, exactly as in the per-template route.
//! 2. [`encode_document`]: the bound document (no parameter left) is written deterministically: the magic `GSQLAST1`,
//!    then the root `OrderedQuery` in prefix order. Each node is its tag byte ([`tag`], the position of its kind in
//!    its sort's constructor list, the codec's table) followed by its fields in the AST schema's field order
//!    (`frontend/ast/ast_schema.json`), each in the representation of its field kind. Records (`OrderedQuery`,
//!    `OrderKey`) have no tag.
//!
//! The same document is rendered by `gendb_sqlspec::evaluator::echo_text`; an engine library's verified echo of the
//! bytes must equal that text (translation validation of this encoder, per statement).
//!
//! Trust: this module is the trusted host item `host_ast_encoding`; nothing here is proved. It refuses (never guesses)
//! a document it cannot encode exactly: a parameter left unbound, a value outside its field's byte width, an unknown
//! tag or enum value, or a node of the wrong sort.

use crate::ast::{schema, AstDocument, ChildMode, FieldKind, FieldValue, Machine, Node};
use crate::params::{declare, instantiate, BindingRequest, ParamError, ParamRefusal, ParamRequest};
use std::fmt;

/// The byte format this module writes.
pub const ENGINE_AST_FORMAT: &str = "gendb-engine-ast-v1";

/// The 8 bytes every encoded AST starts with.
pub const AST_MAGIC: &[u8; 8] = b"GSQLAST1";

/// Why a document and binding could not be encoded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EncodeError {
    /// The binding is not a value list of the declared parameters (`params` refusal).
    Binding(ParamError),
    /// A parameter is still unbound in the document to encode.
    Unbound(String),
    /// A value does not fit its field's byte representation (for example a column position above `u32::MAX`).
    Range(String),
    /// The document is not a well-formed `gendb-sql-ast-v1` tree (wrong sort, unknown tag or enum value).
    Shape(String),
}

impl fmt::Display for EncodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Binding(e) => write!(f, "engine_ast_binding: {e}"),
            Self::Unbound(m) => write!(f, "engine_ast_unbound_parameter: {m}"),
            Self::Range(m) => write!(f, "engine_ast_value_range: {m}"),
            Self::Shape(m) => write!(f, "engine_ast_shape: {m}"),
        }
    }
}

impl std::error::Error for EncodeError {}

/// An encoded engine statement: the bound document (what the bytes mean; the host renders its echo text from it) and
/// the bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EngineAst {
    pub document: AstDocument,
    pub bytes: Vec<u8>,
}

/// `doc` with every declared parameter bound to its value in `arguments` (one argument text per declared parameter,
/// ascending `$index`; exact values as `params::ParamType::parse` reads them) and substituted as a literal node.
pub fn bind_document(doc: &AstDocument, arguments: &[String]) -> Result<AstDocument, EncodeError> {
    if arguments.len() != doc.params.len() {
        let detail = format!("{} arguments for {} declared parameters", arguments.len(), doc.params.len());
        return Err(EncodeError::Binding(ParamError { reason: ParamRefusal::ArgumentCount, detail }));
    }
    let requests: Vec<ParamRequest> = doc
        .params
        .iter()
        .zip(arguments)
        .map(|(p, a)| ParamRequest { index: p.index, name: None, sql_type: p.ty.sql_name(), binding: BindingRequest::Fixed(a.clone()) })
        .collect();
    let decls = declare(doc, &requests).map_err(EncodeError::Binding)?;
    let instance = instantiate(doc, &decls).map_err(EncodeError::Binding)?;
    if !instance.free.is_empty() || !instance.doc.params.is_empty() {
        return Err(EncodeError::Unbound("a parameter stayed free after substitution".into()));
    }
    Ok(instance.doc)
}

/// The engine call's AST for `doc` at `arguments`: [`bind_document`], then [`encode_document`].
pub fn encode_binding(doc: &AstDocument, arguments: &[String]) -> Result<EngineAst, EncodeError> {
    let document = bind_document(doc, arguments)?;
    let bytes = encode_document(&document)?;
    Ok(EngineAst { document, bytes })
}

/// The AST bytes of a document without parameters (format `gendb-engine-ast-v1`).
pub fn encode_document(doc: &AstDocument) -> Result<Vec<u8>, EncodeError> {
    if let Some(p) = doc.params.first() {
        return Err(EncodeError::Unbound(format!("${} is declared and not bound", p.index)));
    }
    let mut out = AST_MAGIC.to_vec();
    Encoder { doc, out: &mut out }.node(doc.root, "ordered")?;
    Ok(out)
}

/// The tag byte of node kind `kind` of sort `sort`: its position in the sort's constructor list (the codec's table).
/// `None` for a record sort (no tag), and for a kind that is not a constructor of the sort (`Param` included).
pub fn tag(sort: &str, kind: &str) -> Option<u8> {
    let constructors: &[&str] = match sort {
        "query" => &["Table", "Filter", "Project", "Product", "LeftJoin", "Aggregate", "GroupBy", "Distinct"],
        "expr" => &["Col", "Lit", "Neg", "Arith", "Cast", "AddInterval", "Call", "If", "Subquery"],
        "pred" => &["Cmp", "And", "Or", "Not", "IsNull", "OfBool", "Exists", "AnyCmp"],
        "agg" => &["CountStar", "Count", "Sum", "Min", "Max", "Avg", "DistinctAgg"],
        "literal" => &["Null", "Bool", "Int", "Num", "Date", "Text"],
        _ => return None,
    };
    constructors.iter().position(|c| *c == kind).map(|p| p as u8)
}

/// The tag byte of a scalar type kind (`ScalarTy`), the codec's table.
fn scalar_ty_tag(kind: &str) -> Option<u8> {
    ["Bool", "Int4", "Int8", "Numeric", "Date", "Timestamp", "Text"].iter().position(|k| *k == kind).map(|p| p as u8)
}

/// Sorts written without a tag byte (records).
const RECORD_SORTS: [&str; 2] = ["ordered", "order_key"];

struct Encoder<'a> {
    doc: &'a AstDocument,
    out: &'a mut Vec<u8>,
}

impl Encoder<'_> {
    /// Node `id`, which must be of sort `sort`: its tag (unless a record), then its fields in schema order.
    fn node(&mut self, id: usize, sort: &str) -> Result<(), EncodeError> {
        let node: &Node = self.doc.nodes.get(id).ok_or_else(|| EncodeError::Shape(format!("node {id} is outside the document")))?;
        if node.param_index().is_some() {
            return Err(EncodeError::Unbound(format!("node {id} is a parameter")));
        }
        let kind = schema().kinds.get(&node.tag).ok_or_else(|| EncodeError::Shape(format!("unknown node kind {}", node.tag)))?;
        if kind.sort != sort {
            return Err(EncodeError::Shape(format!("node {id} ({}) is a {}, expected a {sort}", node.tag, kind.sort)));
        }
        if !RECORD_SORTS.contains(&sort) {
            let t = tag(sort, &node.tag).ok_or_else(|| EncodeError::Shape(format!("{} is not a {sort} constructor of the codec", node.tag)))?;
            self.out.push(t);
        }
        if node.fields.len() != kind.fields.len() {
            return Err(EncodeError::Shape(format!("node {id} ({}) has {} fields, its kind {}", node.tag, node.fields.len(), kind.fields.len())));
        }
        for ((name, field_kind), value) in kind.fields.iter().zip(&node.fields) {
            self.field(&node.tag, name, field_kind, value)?;
        }
        Ok(())
    }

    fn field(&mut self, tag: &str, name: &str, kind: &FieldKind, value: &FieldValue) -> Result<(), EncodeError> {
        let at = || format!("{tag}.{name}");
        match (kind, value) {
            (FieldKind::Child(ChildMode::Ref | ChildMode::Box, sort), FieldValue::Child(c)) => self.node(*c, sort),
            (FieldKind::Child(ChildMode::Seq, sort), FieldValue::Children(cs)) => {
                self.u32(cs.len() as u64, &at())?;
                cs.iter().try_for_each(|c| self.node(*c, sort))
            }
            (FieldKind::Int(machine), FieldValue::Int(text)) => self.signed(*machine, text, &at()),
            (FieldKind::Fixed(machine), FieldValue::Fixed(v)) => self.signed(*machine, &v.to_string(), &at()),
            (FieldKind::Nat(Machine::U64), FieldValue::Nat(v)) => {
                self.out.extend(v.to_le_bytes());
                Ok(())
            }
            (FieldKind::Nat(Machine::U32 | Machine::Usize), FieldValue::Nat(v)) => self.u32(*v, &at()),
            (FieldKind::OptNat(Machine::U64), FieldValue::OptNat(v)) => {
                match v {
                    None => self.out.push(0),
                    Some(n) => {
                        self.out.push(1);
                        self.out.extend(n.to_le_bytes());
                    }
                }
                Ok(())
            }
            (FieldKind::Bool, FieldValue::Bool(b)) => {
                self.out.push(u8::from(*b));
                Ok(())
            }
            (FieldKind::Bytes, FieldValue::Bytes(text)) => {
                self.u32(text.len() as u64, &at())?;
                self.out.extend(text.as_bytes());
                Ok(())
            }
            (FieldKind::ScalarTy, FieldValue::ScalarTy(t)) => {
                let t_tag = scalar_ty_tag(&t.kind).ok_or_else(|| EncodeError::Shape(format!("{}: unknown scalar type {}", at(), t.kind)))?;
                self.out.push(t_tag);
                match (t.kind.as_str(), t.scale) {
                    ("Numeric", Some(scale)) => self.u32(scale, &at()),
                    ("Numeric", None) => Err(EncodeError::Shape(format!("{}: Numeric without a scale", at()))),
                    (_, None) => Ok(()),
                    (_, Some(_)) => Err(EncodeError::Shape(format!("{}: {} takes no scale", at(), t.kind))),
                }
            }
            (FieldKind::Enum(e), FieldValue::Enum(v)) => {
                let values = schema().enums.get(e).ok_or_else(|| EncodeError::Shape(format!("{}: unknown enum {e}", at())))?;
                let position = values.iter().position(|x| x == v).ok_or_else(|| EncodeError::Shape(format!("{}: {v} is not a {e}", at())))?;
                self.out.push(position as u8);
                Ok(())
            }
            (kind, value) => Err(EncodeError::Shape(format!("{}: value {value:?} does not match field kind {kind:?}", at()))),
        }
    }

    /// A count or position as u32 (little-endian).
    fn u32(&mut self, v: u64, at: &str) -> Result<(), EncodeError> {
        let v = u32::try_from(v).map_err(|_| EncodeError::Range(format!("{at}: {v} exceeds u32")))?;
        self.out.extend(v.to_le_bytes());
        Ok(())
    }

    /// A signed integer of `machine`'s width (two's complement, little-endian) from its decimal text.
    fn signed(&mut self, machine: Machine, text: &str, at: &str) -> Result<(), EncodeError> {
        let range = |_| EncodeError::Range(format!("{at}: {text} does not fit {machine:?}"));
        match machine {
            Machine::I32 => self.out.extend(text.parse::<i32>().map_err(range)?.to_le_bytes()),
            Machine::I64 => self.out.extend(text.parse::<i64>().map_err(range)?.to_le_bytes()),
            Machine::I128 => self.out.extend(text.parse::<i128>().map_err(range)?.to_le_bytes()),
            other => return Err(EncodeError::Shape(format!("{at}: signed field of machine type {other:?}"))),
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The tag tables follow the AST schema: every kind of an encoded sort has a tag, and nothing else does.
    #[test]
    fn tags_cover_exactly_the_schema_constructors() {
        let s = schema();
        for (name, kind) in &s.kinds {
            let tagged = tag(&kind.sort, name);
            match (kind.sort.as_str(), name.as_str()) {
                ("ordered" | "order_key", _) | ("literal", "Param") => assert_eq!(tagged, None, "{name}"),
                _ => assert!(tagged.is_some(), "{name} of sort {} has no tag", kind.sort),
            }
        }
        for sort in ["query", "expr", "pred", "agg", "literal"] {
            let kinds = s.kinds.iter().filter(|(n, k)| k.sort == sort && *n != "Param").count();
            let tags: Vec<u8> = s.kinds.iter().filter_map(|(n, k)| (k.sort == sort).then(|| tag(sort, n)).flatten()).collect();
            assert_eq!(tags.len(), kinds, "{sort}");
            let mut sorted = tags.clone();
            sorted.sort_unstable();
            assert_eq!(sorted, (0..kinds as u8).collect::<Vec<_>>(), "{sort}: tags are 0..n");
        }
        for (k, i) in [("Bool", 0), ("Int4", 1), ("Int8", 2), ("Numeric", 3), ("Date", 4), ("Timestamp", 5), ("Text", 6)] {
            assert_eq!(scalar_ty_tag(k), Some(i));
        }
        assert_eq!(s.scalar_types.len(), 7, "the codec's scalar type table covers the schema's");
    }
}
