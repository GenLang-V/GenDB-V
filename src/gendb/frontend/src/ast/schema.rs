//! The AST encoding schema (`frontend/ast/ast_schema.json`), parsed once. It names the Verus sort types, view functions,
//! variant forms and field kinds that the decoder checks against and the translator renders generically.

use super::{err, AstError};
use serde_json::{Map, Value};
use std::collections::BTreeMap;
use std::sync::OnceLock;

/// The shared encoding schema, embedded at compile time. The Python parser reads the same file at run time.
pub const SCHEMA_JSON: &str = include_str!("../../ast/ast_schema.json");

/// Machine representation of an integer field in the exec AST (and, for `I32`/`I64` fields, also in spec).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Machine {
    I32,
    I64,
    I128,
    U32,
    U64,
    Usize,
}

impl Machine {
    fn parse(s: &str) -> Option<Machine> {
        Some(match s {
            "i32" => Machine::I32,
            "i64" => Machine::I64,
            "i128" => Machine::I128,
            "u32" => Machine::U32,
            "u64" => Machine::U64,
            "usize" => Machine::Usize,
            _ => return None,
        })
    }

    /// Whether the decimal integer `v` is representable.
    pub fn fits(self, v: &str) -> bool {
        match self {
            Machine::I32 => v.parse::<i32>().is_ok(),
            Machine::I64 => v.parse::<i64>().is_ok(),
            Machine::I128 => v.parse::<i128>().is_ok(),
            Machine::U32 => v.parse::<u32>().is_ok(),
            Machine::U64 => v.parse::<u64>().is_ok(),
            Machine::Usize => v.parse::<usize>().is_ok(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChildMode {
    /// Inline child (`a: Expr`).
    Ref,
    /// Boxed child (`arg: Box<Expr>`).
    Box,
    /// Child list (spec `Seq`, exec `Vec`).
    Seq,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FieldKind {
    /// A child node of the named sort.
    Child(ChildMode, String),
    /// Spec `int` (JSON decimal string), exec machine type.
    Int(Machine),
    /// Spec `nat` (JSON integer), exec machine type.
    Nat(Machine),
    /// Spec `Option<nat>` (JSON integer or null), exec `Option<machine>`.
    OptNat(Machine),
    /// Machine integer in both spec and exec (JSON integer).
    Fixed(Machine),
    Bool,
    /// UTF-8 text without NUL (spec `Seq<u8>`, exec `Vec<u8>`).
    Bytes,
    ScalarTy,
    /// One of the values of the named schema enum.
    Enum(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Form {
    Tuple,
    Struct,
    Unit,
    Record,
    /// Not a Verus constructor: a typed statement parameter (`Param`), rendered as its value (`crate::params`).
    Param,
}

/// One node kind (tag): its sort, variant form and fields in Verus declaration order.
#[derive(Debug, Clone)]
pub struct KindSpec {
    pub sort: String,
    pub form: Form,
    pub fields: Vec<(String, FieldKind)>,
}

/// One sort: its spec and exec type names and the Verus functions relating them.
#[derive(Debug, Clone)]
pub struct SortSpec {
    pub spec: String,
    pub exec: String,
    pub view: String,
    /// View of a child list of this sort (`seq:` fields), when the sort occurs in lists.
    pub list_view: Option<String>,
    /// Typing-equivalence relation of the sort and the lemma building it for a child list (SQLSpec `bridge::params`).
    pub teq: Option<String>,
    pub teq_intro: Option<String>,
}

#[derive(Debug, Clone)]
pub struct AstSchema {
    pub format: String,
    pub verus_interface: String,
    pub root_sort: String,
    pub sorts: BTreeMap<String, SortSpec>,
    pub kinds: BTreeMap<String, KindSpec>,
    pub enums: BTreeMap<String, Vec<String>>,
    /// Scalar type kind -> its parameter names (`Numeric` -> `["scale"]`).
    pub scalar_types: BTreeMap<String, Vec<String>>,
    /// Sort -> annotation kind (`coltype` on expressions, `coltypes` on queries).
    pub annotations: BTreeMap<String, String>,
}

/// The parsed shared schema. The file is part of the source; a malformed file is a build defect (the unit test
/// `embedded_schema_parses` checks it).
pub fn schema() -> &'static AstSchema {
    static SCHEMA: OnceLock<AstSchema> = OnceLock::new();
    SCHEMA.get_or_init(|| parse_schema(SCHEMA_JSON).expect("embedded ast_schema.json is malformed"))
}

fn parse_schema(text: &str) -> Result<AstSchema, AstError> {
    let top: Value = serde_json::from_str(text).map_err(|e| AstError(format!("schema: {e}")))?;
    let section = |k: &str| top.get(k).and_then(Value::as_object).ok_or_else(|| AstError(format!("schema.{k}")));
    let text_of = |k: &str| top.get(k).and_then(Value::as_str).map(str::to_owned).ok_or_else(|| AstError(format!("schema.{k}")));
    let sorts = parse_sorts(section("sorts")?)?;
    let enums = parse_string_lists(section("enums")?)?;
    let scalar_types = parse_string_lists(section("scalar_types")?)?;
    let mut annotations = BTreeMap::new();
    for (sort, kind) in section("annotations")? {
        annotations.insert(sort.clone(), kind.as_str().ok_or_else(|| AstError("schema.annotations".into()))?.to_owned());
    }
    let kinds = parse_kinds(section("kinds")?, &sorts, &enums)?;
    Ok(AstSchema {
        format: text_of("format")?,
        verus_interface: text_of("verus_interface")?,
        root_sort: text_of("root_sort")?,
        sorts,
        kinds,
        enums,
        scalar_types,
        annotations,
    })
}

fn parse_sorts(section: &Map<String, Value>) -> Result<BTreeMap<String, SortSpec>, AstError> {
    let mut sorts = BTreeMap::new();
    for (name, spec) in section {
        let required = |k: &str| spec.get(k).and_then(Value::as_str).map(str::to_owned).ok_or_else(|| AstError(format!("sort {name}.{k}")));
        let optional = |k: &str| spec.get(k).and_then(Value::as_str).map(str::to_owned);
        sorts.insert(
            name.clone(),
            SortSpec {
                spec: required("spec")?,
                exec: required("exec")?,
                view: required("view")?,
                list_view: optional("list_view"),
                teq: optional("teq"),
                teq_intro: optional("teq_intro"),
            },
        );
    }
    Ok(sorts)
}

fn parse_kinds(
    section: &Map<String, Value>,
    sorts: &BTreeMap<String, SortSpec>,
    enums: &BTreeMap<String, Vec<String>>,
) -> Result<BTreeMap<String, KindSpec>, AstError> {
    let mut kinds = BTreeMap::new();
    for (tag, spec) in section {
        let sort = spec.get("sort").and_then(Value::as_str).ok_or_else(|| AstError(format!("kind {tag}.sort")))?;
        if !sorts.contains_key(sort) {
            return err(format!("kind {tag}: unknown sort {sort}"));
        }
        let form = match spec.get("form").and_then(Value::as_str) {
            Some("tuple") => Form::Tuple,
            Some("struct") => Form::Struct,
            Some("unit") => Form::Unit,
            Some("record") => Form::Record,
            Some("param") => Form::Param,
            _ => return err(format!("kind {tag}: bad form")),
        };
        let mut fields = Vec::new();
        for entry in spec.get("fields").and_then(Value::as_array).ok_or_else(|| AstError(format!("kind {tag}.fields")))? {
            let pair = strings(entry)?;
            if pair.len() != 2 {
                return err(format!("kind {tag}: field entries are [name, kind]"));
            }
            fields.push((pair[0].clone(), parse_field_kind(&pair[1], sorts, enums)?));
        }
        kinds.insert(tag.clone(), KindSpec { sort: sort.to_owned(), form, fields });
    }
    Ok(kinds)
}

/// A field kind: `ref:<sort>`, `box:<sort>`, `seq:<sort>`, `int:<machine>`, `nat:<machine>`, `opt_nat:<machine>`, `i32`,
/// `i64`, `bool`, `bytes`, `scalar_ty` or `enum:<E>`.
fn parse_field_kind(k: &str, sorts: &BTreeMap<String, SortSpec>, enums: &BTreeMap<String, Vec<String>>) -> Result<FieldKind, AstError> {
    let (head, arg) = k.split_once(':').unwrap_or((k, ""));
    let machine = || Machine::parse(arg).ok_or_else(|| AstError(format!("field kind {k}: bad machine type")));
    Ok(match head {
        "ref" | "box" | "seq" => {
            if !sorts.contains_key(arg) {
                return err(format!("field kind {k}: unknown sort"));
            }
            let mode = match head {
                "ref" => ChildMode::Ref,
                "box" => ChildMode::Box,
                _ => ChildMode::Seq,
            };
            FieldKind::Child(mode, arg.to_owned())
        }
        "int" => FieldKind::Int(machine()?),
        "nat" => FieldKind::Nat(machine()?),
        "opt_nat" => FieldKind::OptNat(machine()?),
        "i32" => FieldKind::Fixed(Machine::I32),
        "i64" => FieldKind::Fixed(Machine::I64),
        "bool" => FieldKind::Bool,
        "bytes" => FieldKind::Bytes,
        "scalar_ty" => FieldKind::ScalarTy,
        "enum" if enums.contains_key(arg) => FieldKind::Enum(arg.to_owned()),
        _ => return err(format!("unknown field kind {k}")),
    })
}

fn parse_string_lists(section: &Map<String, Value>) -> Result<BTreeMap<String, Vec<String>>, AstError> {
    section.iter().map(|(name, list)| Ok((name.clone(), strings(list)?))).collect()
}

fn strings(v: &Value) -> Result<Vec<String>, AstError> {
    v.as_array()
        .ok_or_else(|| AstError("schema: expected a list".into()))?
        .iter()
        .map(|e| e.as_str().map(str::to_owned).ok_or_else(|| AstError("schema: expected strings".into())))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn embedded_schema_parses() {
        let s = schema();
        assert_eq!(s.format, "gendb-sql-ast-v1");
        assert_eq!(s.kinds["OrderedQuery"].sort, s.root_sort);
    }
}
