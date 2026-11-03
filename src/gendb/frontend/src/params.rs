//! Typed statement parameters `$n`: declared types, exact values, domains and the substitution of fixed parameters.
//! One path for a concrete statement (no parameter), a template (every parameter free) and a partial specialization
//! (some fixed).
//!
//! - The parser types every placeholder from its declaration (`ParamRequest::placeholder`, parser
//!   `features/params.py`): a `Param { index }` literal node under a `Lit` annotated like a constant of that type, and
//!   the document's `params` section (`AstDocument::params`).
//! - A request binds each declared parameter to a fixed value or leaves it free: `declare`. A free integer, numeric or
//!   date parameter has an inclusive domain `[min, max]` (the type's range where a bound is omitted); a free `text`
//!   parameter has every text value (no bounds: text order depends on the collation).
//! - `instantiate` replaces each fixed `Param` node by the literal node of its value (a leaf by a leaf: node ids and the
//!   tree are unchanged) and keeps the free ones. With every parameter fixed the result is the AST of the same SQL
//!   with those literals written in place (checked for TPC-H Q6 by the `params_columns` test).
//! - The translator (`translator::emit_instance_module`) renders free parameter `slot` (rank in ascending index
//!   order) as `ps[slot]` of `query_spec_at(ps)`, and the declared types and domains as `param_typed(ps)` /
//!   `param_domain(ps)`.
//!
//! Values are exact: an integer is decimal digits with an optional sign; a `numeric(p, s)` has at most `s` fractional
//! digits (padded to exactly `s`: the value of PostgreSQL's `CAST(v AS numeric(p, s))` for such inputs, never rounded,
//! no exponent) and a coefficient of at most `p` digits; a date is `YYYY-MM-DD` with year 0001..9999; a `text` value is
//! any string without a NUL byte (PostgreSQL text cannot hold one), taken as is (its UTF-8 bytes). Anything else is the
//! named refusal `invalid_parameter_value`. Parameters are never NULL. The same parser converts host arguments
//! (`parse_arguments`).

use crate::ast::{valid_ymd, AstDocument, ColType, FieldValue, Node, PgType};
use serde::{Deserialize, Serialize};
use std::fmt;

/// Parameter types: `integer`, `bigint`, `numeric(p, s)` with `p <= 38` (an `i128` coefficient), `date`, `text`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ParamType {
    Int4,
    Int8,
    Numeric { precision: u32, scale: u32 },
    Date,
    Text,
}

/// Largest numeric precision of a parameter (the ABI carries an `i128` coefficient).
pub const NUMERIC_PARAM_MAX_PRECISION: u32 = 38;

/// A value of a parameter type. `Num` is the coefficient at the declared scale; `Text` holds no NUL. The derived order
/// compares values of one ordered type (integers, coefficients, dates as `(y, m, d)`); it is never used for text.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ParamValue {
    Int(i64),
    Num(i128),
    Date { y: i32, m: u32, d: u32 },
    Text(String),
}

/// Why a parameter declaration, value or argument list was refused. Serialized (and displayed) as the recorded reason
/// string, e.g. `invalid_parameter_value`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ParamRefusal {
    /// The bindings or requests do not name exactly the declared parameters (or with other types).
    ParameterDeclarationMismatch,
    /// A text is not an exact value of the parameter type.
    InvalidParameterValue,
    /// A free domain with `min > max`, or a bound on a `text` parameter.
    InvalidParameterDomain,
    /// Host arguments whose count differs from the free parameters.
    ArgumentCount,
}

impl ParamRefusal {
    pub fn as_str(self) -> &'static str {
        match self {
            ParamRefusal::ParameterDeclarationMismatch => "parameter_declaration_mismatch",
            ParamRefusal::InvalidParameterValue => "invalid_parameter_value",
            ParamRefusal::InvalidParameterDomain => "invalid_parameter_domain",
            ParamRefusal::ArgumentCount => "argument_count",
        }
    }
}

impl fmt::Display for ParamRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ParamError {
    pub reason: ParamRefusal,
    pub detail: String,
}

impl ParamError {
    /// The same refusal with its detail prefixed by the parameter `$index`.
    fn at_parameter(self, index: u32) -> ParamError {
        ParamError { reason: self.reason, detail: format!("${index}: {}", self.detail) }
    }
}

impl fmt::Display for ParamError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.reason, self.detail)
    }
}

impl std::error::Error for ParamError {}

fn refuse<T>(reason: ParamRefusal, detail: impl Into<String>) -> Result<T, ParamError> {
    Err(ParamError { reason, detail: detail.into() })
}

impl ParamType {
    /// The parameter type of a declared SQL type, or `None` outside the five parameter types.
    pub fn from_pg(t: &PgType) -> Option<ParamType> {
        Some(match t {
            PgType::Int4 => ParamType::Int4,
            PgType::Int8 => ParamType::Int8,
            PgType::Numeric { typmod: Some((p, s)) } if *p <= NUMERIC_PARAM_MAX_PRECISION as u64 => ParamType::Numeric { precision: *p as u32, scale: *s as u32 },
            PgType::Date => ParamType::Date,
            PgType::Text => ParamType::Text,
            _ => return None,
        })
    }

    pub fn sql_name(&self) -> String {
        match self {
            ParamType::Int4 => "integer".into(),
            ParamType::Int8 => "bigint".into(),
            ParamType::Numeric { precision, scale } => format!("numeric({precision},{scale})"),
            ParamType::Date => "date".into(),
            ParamType::Text => "text".into(),
        }
    }

    /// Static type of the `Lit` over a placeholder of this type: a non-NULL constant of the type (a numeric constant of
    /// scale `s`, as a parameter's typmod is not part of its PostgreSQL type).
    pub fn coltype(&self) -> ColType {
        let (ty, dscale) = match self {
            ParamType::Int4 => (PgType::Int4, None),
            ParamType::Int8 => (PgType::Int8, None),
            ParamType::Numeric { scale, .. } => (PgType::Numeric { typmod: None }, Some(*scale as u64)),
            ParamType::Date => (PgType::Date, None),
            ParamType::Text => (PgType::Text, None),
        };
        ColType { ty, nullable: false, dscale, dscale_exact: true }
    }

    /// Verus `ScalarTy` of the literals of this type (`spec::typing::type_lit`).
    pub fn verus_scalar_ty(&self) -> String {
        match self {
            ParamType::Int4 => "ScalarTy::Int4".into(),
            ParamType::Int8 => "ScalarTy::Int8".into(),
            ParamType::Numeric { scale, .. } => format!("ScalarTy::Numeric {{ scale: {scale} }}"),
            ParamType::Date => "ScalarTy::Date".into(),
            ParamType::Text => "ScalarTy::Text".into(),
        }
    }

    /// Smallest and largest value of an ordered type; `None` for `text`, whose order depends on the collation.
    pub fn range(&self) -> Option<(ParamValue, ParamValue)> {
        Some(match self {
            ParamType::Int4 => (ParamValue::Int(i32::MIN as i64), ParamValue::Int(i32::MAX as i64)),
            ParamType::Int8 => (ParamValue::Int(i64::MIN), ParamValue::Int(i64::MAX)),
            ParamType::Numeric { precision, .. } => {
                let largest = 10i128.pow(*precision) - 1;
                (ParamValue::Num(-largest), ParamValue::Num(largest))
            }
            ParamType::Date => (ParamValue::Date { y: 1, m: 1, d: 1 }, ParamValue::Date { y: 9999, m: 12, d: 31 }),
            ParamType::Text => return None,
        })
    }

    /// Every value of the type: its range, or every text.
    pub fn full_domain(&self) -> ParamDomain {
        match self.range() {
            Some((min, max)) => ParamDomain::Range { min, max },
            None => ParamDomain::AllText,
        }
    }

    /// The exact value of `text` (module doc), within the type's range.
    pub fn parse(&self, text: &str) -> Result<ParamValue, ParamError> {
        let parsed = match self {
            ParamType::Int4 | ParamType::Int8 => parse_integer(text),
            ParamType::Numeric { scale, .. } => parse_numeric(text, *scale),
            ParamType::Date => parse_date(text),
            ParamType::Text => parse_text(text),
        };
        let value = parsed.and_then(|v| if self.full_domain().contains(&v) { Ok(v) } else { Err("outside the type's range".into()) });
        value.or_else(|why| refuse(ParamRefusal::InvalidParameterValue, format!("{text:?} as {}: {why}", self.sql_name())))
    }

    /// The literal node of `v` (a value of this type): the AST node of the same constant written in the SQL.
    pub fn literal_node(&self, v: &ParamValue) -> Node {
        let (tag, fields) = match (self, v) {
            (ParamType::Int4 | ParamType::Int8, ParamValue::Int(x)) => {
                let kind = if *self == ParamType::Int4 { "Int4" } else { "Int8" };
                ("Int", vec![FieldValue::Int(x.to_string()), FieldValue::Enum(kind.into())])
            }
            (ParamType::Numeric { scale, .. }, ParamValue::Num(c)) => ("Num", vec![FieldValue::Int(c.to_string()), FieldValue::Nat(*scale as u64)]),
            (ParamType::Date, ParamValue::Date { y, m, d }) => ("Date", vec![FieldValue::Int(y.to_string()), FieldValue::Int(m.to_string()), FieldValue::Int(d.to_string())]),
            (ParamType::Text, ParamValue::Text(s)) => ("Text", vec![FieldValue::Bytes(s.clone())]),
            _ => unreachable!("value {v:?} is not of type {self:?}"),
        };
        Node { tag: tag.into(), fields, annotation: None }
    }

    /// Canonical text of `v` (accepted by `parse`).
    pub fn text(&self, v: &ParamValue) -> String {
        match (self, v) {
            (ParamType::Numeric { scale, .. }, ParamValue::Num(c)) => {
                let s = *scale as usize;
                let digits = format!("{:0>width$}", c.unsigned_abs(), width = s + 1);
                let (int, frac) = digits.split_at(digits.len() - s);
                format!("{}{int}{}{frac}", if *c < 0 { "-" } else { "" }, if s > 0 { "." } else { "" })
            }
            (_, ParamValue::Int(x)) => x.to_string(),
            (_, ParamValue::Date { y, m, d }) => format!("{y:04}-{m:02}-{d:02}"),
            (ParamType::Text, ParamValue::Text(s)) => s.clone(),
            _ => unreachable!("value {v:?} is not of type {self:?}"),
        }
    }
}

// Exact text parsers; an `Err` names why the text is not a value (the caller adds the refusal reason).

fn parse_integer(text: &str) -> Result<ParamValue, String> {
    let digits = text.strip_prefix(['+', '-']).unwrap_or(text);
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return Err("expected decimal digits with an optional sign".into());
    }
    text.parse::<i64>().map(ParamValue::Int).map_err(|_| "outside the type's range".into())
}

/// Plain decimal notation with at most `scale` fractional digits, as the coefficient at `scale` (never rounded).
fn parse_numeric(text: &str, scale: u32) -> Result<ParamValue, String> {
    let (negative, body) = match text.strip_prefix('-') {
        Some(b) => (true, b),
        None => (false, text.strip_prefix('+').unwrap_or(text)),
    };
    let (int, frac) = body.split_once('.').unwrap_or((body, ""));
    if int.len() + frac.len() == 0 || !int.bytes().chain(frac.bytes()).all(|b| b.is_ascii_digit()) {
        return Err("expected plain decimal notation".into());
    }
    if frac.len() > scale as usize {
        return Err(format!("more than {scale} fractional digits (values are not rounded)"));
    }
    let padded = format!("{int}{frac}{}", "0".repeat(scale as usize - frac.len()));
    let digits = padded.trim_start_matches('0');
    if digits.len() > NUMERIC_PARAM_MAX_PRECISION as usize {
        return Err("outside the type's range".into());
    }
    let coeff: i128 = if digits.is_empty() { 0 } else { digits.parse().expect("at most 38 decimal digits") };
    Ok(ParamValue::Num(if negative { -coeff } else { coeff }))
}

fn parse_date(text: &str) -> Result<ParamValue, String> {
    let b = text.as_bytes();
    let digits = |r: std::ops::Range<usize>| b[r].iter().all(u8::is_ascii_digit);
    if b.len() != 10 || b[4] != b'-' || b[7] != b'-' || !digits(0..4) || !digits(5..7) || !digits(8..10) {
        return Err("expected YYYY-MM-DD".into());
    }
    let (y, m, d): (i32, u32, u32) = (text[0..4].parse().unwrap(), text[5..7].parse().unwrap(), text[8..10].parse().unwrap());
    if y < 1 || !valid_ymd(y as i64, m as i64, d as i64) {
        return Err("not a calendar date".into());
    }
    Ok(ParamValue::Date { y, m, d })
}

/// Any string without a NUL byte (the Rust string is UTF-8; its bytes are the value).
fn parse_text(text: &str) -> Result<ParamValue, String> {
    if text.contains('\0') {
        return Err("text contains a NUL byte".into());
    }
    Ok(ParamValue::Text(text.to_string()))
}

/// One parameter of a request: `$index` of SQL type `sql_type` (e.g. `"numeric(3,2)"`), fixed or free.
///
/// JSON: `{"index": 2, "type": "numeric(3,2)", "binding": {"fixed": "0.06"}}` or
/// `{"index": 1, "type": "date", "binding": {"free": {"min": "1992-01-01", "max": "1998-12-31"}}}` (`{"free": {}}` for
/// the type's range; the only free form of a `text` parameter). Optional `"name"`: a readable name of the parameter
/// (for TPC-H the specification's substitution-parameter name, e.g. `"delta"`), used to bind named argument maps
/// ([`arguments_by_name`]) and in reports; it is not part of the statement's meaning or of any key.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ParamRequest {
    pub index: u32,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    #[serde(rename = "type")]
    pub sql_type: String,
    pub binding: BindingRequest,
}

/// The argument texts of the free parameters of `params` in slot order (ascending `$index`), taken from the named
/// binding `named` (parameter name -> argument text). Every free parameter must have a name with a value, and every
/// name in `named` must be a free parameter's; otherwise the first problem is returned.
pub fn arguments_by_name(params: &[ParamRequest], named: &std::collections::BTreeMap<String, String>) -> Result<Vec<String>, String> {
    let mut free: Vec<&ParamRequest> = params.iter().filter(|p| matches!(p.binding, BindingRequest::Free { .. })).collect();
    free.sort_by_key(|p| p.index);
    let mut texts = Vec::with_capacity(free.len());
    for p in &free {
        let name = p.name.as_deref().ok_or_else(|| format!("free parameter ${} has no name", p.index))?;
        texts.push(named.get(name).cloned().ok_or_else(|| format!("no value for parameter {name} (${})", p.index))?);
    }
    if let Some(extra) = named.keys().find(|k| !free.iter().any(|p| p.name.as_deref() == Some(k.as_str()))) {
        return Err(format!("{extra} is not a free parameter of the statement"));
    }
    Ok(texts)
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", deny_unknown_fields)]
pub enum BindingRequest {
    Fixed(String),
    Free {
        #[serde(default)]
        min: Option<String>,
        #[serde(default)]
        max: Option<String>,
    },
}

/// A placeholder declaration as the parser reads it (`--params`): `{"index": n, "type": "<SQL type>"}`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Placeholder {
    pub index: u32,
    #[serde(rename = "type")]
    pub sql_type: String,
}

impl ParamRequest {
    pub fn placeholder(&self) -> Placeholder {
        Placeholder { index: self.index, sql_type: self.sql_type.clone() }
    }
}

/// A declared parameter of a translated statement (`AstDocument::params`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct DocParam {
    pub index: u32,
    pub ty: ParamType,
}

/// The declared domain of a free parameter.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ParamDomain {
    /// Every value of an ordered type (integer, numeric, date) in the inclusive `[min, max]`.
    Range { min: ParamValue, max: ParamValue },
    /// Every text value: any byte string without NUL (the emitted `text_ok`); the host sends UTF-8 strings.
    AllText,
}

impl ParamDomain {
    /// `v` (a value of the parameter's type) lies in the domain.
    pub fn contains(&self, v: &ParamValue) -> bool {
        match (self, v) {
            (ParamDomain::Range { min, max }, _) => min <= v && v <= max,
            (ParamDomain::AllText, ParamValue::Text(s)) => !s.contains('\0'),
            (ParamDomain::AllText, _) => false,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Binding {
    Fixed(ParamValue),
    Free { domain: ParamDomain },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ParamDecl {
    pub index: u32,
    pub ty: ParamType,
    pub binding: Binding,
}

/// Bind the declared parameters of `doc` (types from the document, i.e. from the parser) as `requests` say. Every
/// declared parameter needs exactly one request and vice versa.
pub fn declare(doc: &AstDocument, requests: &[ParamRequest]) -> Result<Vec<ParamDecl>, ParamError> {
    let mut requested: Vec<u32> = requests.iter().map(|r| r.index).collect();
    requested.sort_unstable();
    let declared: Vec<u32> = doc.params.iter().map(|p| p.index).collect();
    if requested != declared {
        return refuse(ParamRefusal::ParameterDeclarationMismatch, format!("requests for {requested:?}, statement declares {declared:?}"));
    }
    doc.params
        .iter()
        .map(|p| {
            let request = requests.iter().find(|r| r.index == p.index).expect("same index sets");
            let binding = bind(p.ty, &request.binding).map_err(|e| e.at_parameter(p.index))?;
            Ok(ParamDecl { index: p.index, ty: p.ty, binding })
        })
        .collect()
}

/// The binding of a parameter of type `ty`: its fixed value, or its free domain (omitted bounds are the type's range;
/// a `text` parameter takes no bound).
fn bind(ty: ParamType, request: &BindingRequest) -> Result<Binding, ParamError> {
    let (min, max) = match request {
        BindingRequest::Fixed(v) => return Ok(Binding::Fixed(ty.parse(v)?)),
        BindingRequest::Free { min, max } => (min, max),
    };
    let Some((lo, hi)) = ty.range() else {
        if min.is_some() || max.is_some() {
            return refuse(ParamRefusal::InvalidParameterDomain, format!("{} takes no min/max: its order depends on the collation (the domain is every text value)", ty.sql_name()));
        }
        return Ok(Binding::Free { domain: ParamDomain::AllText });
    };
    let min = min.as_deref().map(|t| ty.parse(t)).transpose()?.unwrap_or(lo);
    let max = max.as_deref().map(|t| ty.parse(t)).transpose()?.unwrap_or(hi);
    if min > max {
        return refuse(ParamRefusal::InvalidParameterDomain, format!("min {} > max {}", ty.text(&min), ty.text(&max)));
    }
    Ok(Binding::Free { domain: ParamDomain::Range { min, max } })
}

/// A free parameter of an instance: `ps[slot]` of `query_spec_at(ps)`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct FreeParam {
    pub index: u32,
    pub slot: usize,
    pub ty: ParamType,
    pub domain: ParamDomain,
}

impl FreeParam {
    /// The value lies in the declared domain (the host-side reading of the emitted `param_domain`).
    pub fn admits(&self, v: &ParamValue) -> bool {
        self.domain.contains(v)
    }

    /// The inclusive bounds of an ordered domain (`None` for text).
    pub fn bounds(&self) -> Option<(&ParamValue, &ParamValue)> {
        match &self.domain {
            ParamDomain::Range { min, max } => Some((min, max)),
            ParamDomain::AllText => None,
        }
    }

    /// The domain as recorded and reported: `[min, max]` in canonical texts, or the text domain.
    pub fn domain_text(&self) -> String {
        match self.bounds() {
            Some((min, max)) => format!("[{}, {}]", self.ty.text(min), self.ty.text(max)),
            None => "every text value without a NUL byte".into(),
        }
    }
}

/// A statement with its fixed parameters substituted: `doc` has no fixed `Param` node, `doc.params` lists the free
/// ones, `free[slot]` describes `ps[slot]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Instance {
    pub doc: AstDocument,
    pub free: Vec<FreeParam>,
}

impl Instance {
    /// A statement without parameters.
    pub fn concrete(doc: &AstDocument) -> Result<Instance, ParamError> {
        if let Some(p) = doc.params.first() {
            return refuse(ParamRefusal::ParameterDeclarationMismatch, format!("${} is declared but not bound (use params::instantiate)", p.index));
        }
        Ok(Instance { doc: doc.clone(), free: Vec::new() })
    }
}

/// Substitute the fixed parameters of `decls` (from `declare` for `doc`).
pub fn instantiate(doc: &AstDocument, decls: &[ParamDecl]) -> Result<Instance, ParamError> {
    let declared: Vec<(u32, ParamType)> = doc.params.iter().map(|p| (p.index, p.ty)).collect();
    let given: Vec<(u32, ParamType)> = decls.iter().map(|d| (d.index, d.ty)).collect();
    if declared != given {
        return refuse(ParamRefusal::ParameterDeclarationMismatch, format!("bindings for {given:?}, statement declares {declared:?}"));
    }
    let mut out = doc.clone();
    for node in out.nodes.iter_mut() {
        let Some(index) = node.param_index() else { continue };
        let decl = decls.iter().find(|d| d.index == index).expect("declared parameter");
        if let Binding::Fixed(v) = &decl.binding {
            *node = decl.ty.literal_node(v);
        }
    }
    let mut free = Vec::new();
    for d in decls {
        if let Binding::Free { domain } = &d.binding {
            free.push(FreeParam { index: d.index, slot: free.len(), ty: d.ty, domain: domain.clone() });
        }
    }
    out.params = free.iter().map(|f| DocParam { index: f.index, ty: f.ty }).collect();
    Ok(Instance { doc: out, free })
}

/// Host arguments for the free parameters (one text per slot), converted exactly. Domain membership is not checked
/// here: the verified entry refuses out-of-domain values (`param_domain`).
pub fn parse_arguments(free: &[FreeParam], args: &[String]) -> Result<Vec<ParamValue>, ParamError> {
    if args.len() != free.len() {
        return refuse(ParamRefusal::ArgumentCount, format!("{} arguments for {} free parameters", args.len(), free.len()));
    }
    free.iter().zip(args).map(|(f, a)| f.ty.parse(a).map_err(|e| e.at_parameter(f.index))).collect()
}
