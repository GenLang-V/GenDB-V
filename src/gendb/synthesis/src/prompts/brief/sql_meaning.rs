//! How the author sees the statement's meaning: the annotated AST (one line per node: constructor, fields, static
//! type, environment layout), the capacity conditions and SQL errors of the constructors that occur, and the ABI
//! encoding of each delivered source column. Generic per constructor and type; the crate's definitions are the
//! authority, these texts only point to them.

use gendb_frontend::ast::{Annotation, AstDocument, FieldValue, PgType, schema};
use gendb_frontend::columns::{ColumnDemand, NodeLayout, Slot, SourceType, slot_name};
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::fmt::Write as _;

/// The SQL name of a declared column type, as the schema DDL writes it.
pub fn sql_type_name(ty: &PgType) -> String {
    let sized = |name: &str, n: &Option<u64>| n.map_or(name.to_string(), |n| format!("{name}({n})"));
    match ty {
        PgType::Bool => "boolean".into(),
        PgType::Int4 => "integer".into(),
        PgType::Int8 => "bigint".into(),
        PgType::Numeric { typmod: Some((p, s)) } => format!("numeric({p},{s})"),
        PgType::Numeric { typmod: None } => "numeric".into(),
        PgType::Date => "date".into(),
        PgType::Timestamp => "timestamp".into(),
        PgType::Text => "text".into(),
        PgType::Varchar { max_chars } => sized("varchar", max_chars),
        PgType::Bpchar { n } => sized("char", n),
    }
}

/// The ABI element, value mapping and declared domain of one delivered column of SQL type `sql`.
pub fn source_encoding(ty: SourceType, sql: &str) -> Value {
    match ty {
        SourceType::Decimal { p, s } => json!({"sql":sql,"abi_element":"i128 (Column::I128)","value":format!("coefficient c at scale {s}: Val::Num {{ coeff: c, scale: {s} }} = c * 10^-{s}"),"declared_domain":format!("|c| < 10^{p}")}),
        SourceType::Date32 => json!({"sql":sql,"abi_element":"i32 (Column::I32)","value":"days d since 1970-01-01: Val::Date(d - 10957) (VERUS_SQL days since 2000-01-01; gendb_source::date32_val)","declared_domain":"PostgreSQL date range (spec date_valid)"}),
        SourceType::Int32 => json!({"sql":sql,"abi_element":"i32 (Column::I32)","value":"Val::Int(x)","declared_domain":"int4"}),
        SourceType::Int64 => json!({"sql":sql,"abi_element":"i64 (Column::I64)","value":"Val::Int(x)","declared_domain":"int8"}),
        SourceType::Utf8 => json!({"sql":sql,"abi_element":"Utf8: offsets &[i64] (rows + 1, nondecreasing; may start > 0) + bytes &[u8] (Column::Utf8 -> link::query::TextCol / TextView)",
            "value":"Val::Text(bytes[offsets[i]..offsets[i+1]]) (link::query::text_at)","equality_and_order":"text equality = byte equality; ORDER BY on text = byte order (C collation)",
            "declared_domain":"NUL-free; varchar(n): at most n characters; char(n): canonical (no trailing space). Decided for the delivered bytes by the entry's verified source_in_domain before build"}),
    }
}

/// Scalar fields of a node as `name=value` texts.
fn scalar_text(name: &str, value: &FieldValue) -> Option<String> {
    Some(match value {
        FieldValue::Child(_) | FieldValue::Children(_) => return None,
        FieldValue::Int(s) => format!("{name}={s}"),
        FieldValue::Nat(x) => format!("{name}={x}"),
        FieldValue::Fixed(x) => format!("{name}={x}"),
        FieldValue::OptNat(x) => format!("{name}={x:?}"),
        FieldValue::Bool(b) => format!("{name}={b}"),
        FieldValue::Bytes(b) => format!("{name}={b:?}"),
        FieldValue::Enum(e) => format!("{name}={e}"),
        FieldValue::ScalarTy(t) => format!("{name}={}{}", t.kind, t.scale.map(|s| format!("({s})")).unwrap_or_default()),
    })
}

/// The annotated AST as indented text (depth first from the root) and the table of environments it names.
pub fn annotated_tree(doc: &AstDocument, demand: &ColumnDemand) -> (String, Value) {
    let kinds = &schema().kinds;
    let mut environments: Vec<Vec<Slot>> = vec![];
    let mut environment_id = |env: &Vec<Slot>| -> usize {
        environments.iter().position(|e| e == env).unwrap_or_else(|| {
            environments.push(env.clone());
            environments.len() - 1
        })
    };
    let mut out = String::new();
    let mut stack = vec![(doc.root, 0usize, "root".to_string())];
    while let Some((id, depth, role)) = stack.pop() {
        let node = &doc.nodes[id];
        let mut scalars = vec![];
        let mut children: Vec<(usize, String)> = vec![];
        for ((name, _), value) in kinds[&node.tag].fields.iter().zip(&node.fields) {
            match value {
                FieldValue::Child(c) => children.push((*c, name.clone())),
                FieldValue::Children(cs) => children.extend(cs.iter().enumerate().map(|(i, c)| (*c, format!("{name}[{i}]")))),
                other => scalars.extend(scalar_text(name, other)),
            }
        }
        if let ("Table", Some(FieldValue::Nat(t))) = (node.tag.as_str(), node.field("table")) {
            scalars.push(format!("= {}", doc.tables[*t as usize].name));
        }
        let ty = match &node.annotation {
            Some(Annotation::Type(t)) => format!(
                "  : {:?}{}{}",
                t.ty,
                if t.nullable { " NULL" } else { "" },
                t.dscale.map(|s| format!(" scale {s}{}", if t.dscale_exact { "" } else { " (display scale value-dependent)" })).unwrap_or_default()
            ),
            Some(Annotation::Columns(cs)) => format!("  : row of {} columns", cs.len()),
            None => String::new(),
        };
        let layout = match &demand.layout[id] {
            NodeLayout::Env { env } => format!("  env=E{}", environment_id(env)),
            NodeLayout::Query { ctx_len, output } => {
                format!("  ctx_len={ctx_len} output=[{}]", output.iter().map(|s| slot_name(doc, *s)).collect::<Vec<_>>().join(", "))
            }
            NodeLayout::None => String::new(),
        };
        let param = node.param_index().map(|i| format!("  (free parameter ${i})")).unwrap_or_default();
        let _ = writeln!(out, "{}{role}: n{id} {} {}{ty}{layout}{param}", "  ".repeat(depth), node.tag, scalars.join(" "));
        for (child, name) in children.into_iter().rev() {
            stack.push((child, depth + 1, name));
        }
    }
    let table: Value = json!(environments.iter().enumerate().map(|(i, e)| json!({"env":format!("E{i}"),
        "positions":e.iter().enumerate().map(|(p, s)| format!("{p}: {}", slot_name(doc, *s))).collect::<Vec<_>>()})).collect::<Vec<_>>());
    (out, table)
}

/// Per constructor: where its capacity conditions are defined and which SQL errors it can raise (with the defining
/// spec function).
const CONSTRUCTOR_CONDITIONS: &[(&str, &str, &str)] = &[
    ("Arith::Numeric", "exec::domain::fits_expr: operands, alignment to a common scale and the result fit i128", "22003 numeric_value_out_of_range beyond PostgreSQL's numeric format range (spec::numeric::num_result)"),
    ("Arith::Int4", "exec::domain::fits_expr", "22003 when the result leaves int4 (spec::int::int_result)"),
    ("Arith::Int8", "exec::domain::fits_expr", "22003 when the result leaves int8 (spec::int::int_result)"),
    ("Neg::Numeric", "exec::domain::fits_expr", "22003 beyond the numeric format range (spec::numeric::num_result)"),
    ("Neg::Int4", "exec::domain::fits_expr", "22003 when -x leaves int4 (spec::int::int_result)"),
    ("Neg::Int8", "exec::domain::fits_expr", "22003 when -x leaves int8 (spec::int::int_result)"),
    ("Sum::Numeric", "exec::relational::domain::sum_mass_fits: per group, the sum of absolute argument values at the result scale is at most i128::MAX (order independent: every partition and merge order fits)", "see spec::relation::agg_value (numeric format range)"),
    ("Sum::Int4", "exec::relational::domain::sum_mass_fits", "see spec::relation::agg_value"),
    ("Sum::Int8", "exec::relational::domain::sum_mass_fits", "see spec::relation::agg_value"),
    ("Avg::Numeric", "sum_mass_fits and the division (exec::aggs::avg::fits_avg_value)", "22003 when the numeric sum leaves the format range (spec::aggs::avg::avg_value)"),
    ("Count", "exec::relational::domain::fits_query (Aggregate/GroupBy arms)", "22003 when a count exceeds int8 (spec::relation::agg_value, spec::int::int_result; link::capacity lemma_count_value)"),
    ("CountStar", "exec::relational::domain::fits_query (Aggregate/GroupBy arms)", "22003 when a count exceeds int8 (as Count)"),
    ("Call::DivNumeric", "exec::domain::fits_fn", "22012 division_by_zero (spec::fns::div)"),
    ("Call::DivInt4", "exec::domain::fits_fn", "22012 division_by_zero, then 22003 via int_result (spec::fns::div)"),
    ("Call::DivInt8", "exec::domain::fits_fn", "22012 division_by_zero, then 22003 via int_result (spec::fns::div)"),
    ("Call::Substring2", "exec::domain::fits_fn", "22011 substring_error (spec::fns::substring)"),
    ("Call::Substring3", "exec::domain::fits_fn", "22011 substring_error (spec::fns::substring)"),
    ("Call::Like", "exec::domain::fits_fn", "22025 invalid_escape_sequence (spec::fns::like)"),
    ("Cast", "exec::domain::fits_expr", "DateToTimestamp: 22008 datetime_field_overflow outside the timestamp range (spec::datetime::ts_result)"),
    ("AddInterval", "exec::domain::fits_expr", "22008 datetime_field_overflow outside the timestamp range (spec::datetime::ts_result)"),
    ("Subquery", "exec::relational::domain::fits_query of the subquery", "21000 cardinality_violation when a scalar subquery has more than one row (spec::eval)"),
    ("Exists", "fits_query of the subquery for every outer row (strict, canonical order)", "the subquery's condition errors propagate (link::exists)"),
    ("LeftJoin", "exec::relational::domain::fits_query (padding width)", "the ON condition's errors propagate"),
    ("Filter", "every condition evaluation of every input row, in row order until the first error", "the first failing condition's error in the canonical row order (link::capacity lemma_filter_err)"),
    ("GroupBy", "keys and aggregate arguments of every row; per-group aggregate conditions", "the first error in the canonical order (link::capacity lemma_group_by_err)"),
    ("Aggregate", "aggregate arguments of every row; aggregate conditions", "the first error in the canonical order (link::capacity lemma_aggregate_err)"),
];

/// Capacity-domain conditions and SQL errors of the constructors that occur in the statement.
pub fn domain_notes(doc: &AstDocument) -> Value {
    let mut present: BTreeMap<String, usize> = BTreeMap::new();
    for node in &doc.nodes {
        let key = match (node.tag.as_str(), node.field("f"), node.field("kind")) {
            ("Call", Some(FieldValue::Enum(f)), _) => format!("Call::{f}"),
            (tag @ ("Arith" | "Sum" | "Avg" | "Neg"), _, Some(FieldValue::Enum(k))) => format!("{tag}::{k}"),
            (tag, _, _) => tag.to_string(),
        };
        *present.entry(key).or_default() += 1;
    }
    let conditions: Vec<Value> = CONSTRUCTOR_CONDITIONS
        .iter()
        .filter(|(k, _, _)| present.contains_key(*k))
        .map(|(k, c, e)| json!({"constructor":k,"count":present[*k],"capacity_condition":c,"sql_errors":e}))
        .collect();
    json!({"constructors_in_statement":present,"conditions":conditions,"authority":"the named spec/exec functions in your crate define both columns exactly; this table only points to them",
        "order":"fits_query follows the canonical evaluation of spec::eval: children left to right, rows in order, AND/OR evaluated strictly, stopping at the first SQL error. An implementation that computes more than the canonical evaluation (e.g. evaluates a branch after an operand already failed) must handle its own extra overflows without answering Capacity"})
}
