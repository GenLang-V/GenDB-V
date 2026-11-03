//! `schema_spec()`: the schema a statement was resolved against, as the semantics library's `Schema`, with its declared
//! constraints; and `declared_schema()`: the declared constraints over a column schema's `schema_spec()`. The helpers
//! here are shared with the evaluator's executable schema module (SQLSpec host), which must render the same constraint
//! and CHECK-chain names.

use super::constructors::spec_chain;
use super::{comment_text, EmitError};
use crate::ast::{ConstraintDef, PgType, TableDef};
use std::fmt::Write;

/// `schema_spec()` of the schema `tables` (a document's `tables`).
pub(super) fn emit_schema_spec(out: &mut String, tables: &[TableDef]) -> Result<(), EmitError> {
    writeln!(out, "/// The schema the query was resolved against (table id = position), with its declared constraints").unwrap();
    writeln!(out, "/// (`spec::constraints`; CHECK predicates are let-chains `c<table>_<k>_n<i>`).").unwrap();
    writeln!(out, "pub open spec fn schema_spec() -> Schema {{").unwrap();
    emit_check_chains(out, tables)?;
    writeln!(out, "    seq![").unwrap();
    for (t, table) in tables.iter().enumerate() {
        writeln!(out, "        // {}", comment_text(&table.name)).unwrap();
        writeln!(out, "        TableSchema {{ columns: seq![").unwrap();
        for c in &table.columns {
            writeln!(out, "            Column {{ ty: {}, nullable: {} }}, // {}", sql_type(&c.ty), c.nullable, comment_text(&c.name)).unwrap();
        }
        writeln!(out, "        ], constraints: seq![").unwrap();
        for (k, c) in table.constraints.iter().enumerate() {
            writeln!(out, "            {},", spec_constraint(c, &check_prefix(t, k, "n"))).unwrap();
        }
        writeln!(out, "        ] }},").unwrap();
    }
    writeln!(out, "    ]\n}}\n").unwrap();
    Ok(())
}

/// `declared_schema()`: the tables and columns of `schema_spec()` (referenced, never repeated) with the declared
/// constraints of `tables`, table id = position.
pub(super) fn emit_declared_schema(out: &mut String, tables: &[TableDef]) -> Result<(), EmitError> {
    writeln!(out, "/// The column schema `schema_spec()` with the declared integrity constraints (`spec::constraints`; CHECK").unwrap();
    writeln!(out, "/// predicates are let-chains `c<table>_<k>_n<i>`): the same tables and columns, each table's constraints in").unwrap();
    writeln!(out, "/// declaration order.").unwrap();
    writeln!(out, "pub open spec fn declared_schema() -> Schema {{").unwrap();
    emit_check_chains(out, tables)?;
    writeln!(out, "    seq![").unwrap();
    for (t, table) in tables.iter().enumerate() {
        writeln!(out, "        // {}", comment_text(&table.name)).unwrap();
        writeln!(out, "        TableSchema {{ columns: schema_spec()[{t}].columns, constraints: seq![").unwrap();
        for (k, c) in table.constraints.iter().enumerate() {
            writeln!(out, "            {},", spec_constraint(c, &check_prefix(t, k, "n"))).unwrap();
        }
        writeln!(out, "        ] }},").unwrap();
    }
    writeln!(out, "    ]\n}}\n").unwrap();
    Ok(())
}

/// The spec let-chain of every CHECK of `tables`, in table and declaration order.
fn emit_check_chains(out: &mut String, tables: &[TableDef]) -> Result<(), EmitError> {
    for (t, table) in tables.iter().enumerate() {
        for (k, c) in table.constraints.iter().enumerate() {
            if let ConstraintDef::Check { nodes, .. } = c {
                spec_chain(out, nodes, &check_prefix(t, k, "n"))?;
            }
        }
    }
    Ok(())
}

/// Name prefix of the let-chain of CHECK `k` of table `t` (`n`: spec chain, `g`/`e`: exec chain).
pub fn check_prefix(t: usize, k: usize, side: &str) -> String {
    format!("c{t}_{k}_{side}")
}

/// `seq![a nat, ...]` of column positions (never empty after decoding).
pub fn nat_seq(cols: &[u64]) -> String {
    format!("seq![{}]", cols.iter().map(|c| format!("{c}nat")).collect::<Vec<_>>().join(", "))
}

/// The spec `Constraint` of `c`; a CHECK names the root of its chain with `prefix`.
pub fn spec_constraint(c: &ConstraintDef, prefix: &str) -> String {
    match c {
        ConstraintDef::Key { primary, columns, nulls_distinct, .. } => {
            format!("Constraint::Key {{ cols: {}, primary: {primary}, nulls_distinct: {nulls_distinct} }}", nat_seq(columns))
        }
        ConstraintDef::ForeignKey { columns, table, ref_columns, match_full, .. } => {
            format!("Constraint::ForeignKey {{ cols: {}, table: {table}, ref_cols: {}, match_full: {match_full} }}", nat_seq(columns), nat_seq(ref_columns))
        }
        ConstraintDef::Check { root, .. } => format!("Constraint::Check({prefix}{root})"),
    }
}

/// Verus `SqlType` of a stored column (decoding guarantees the type modifiers are present).
pub fn sql_type(t: &PgType) -> String {
    match t {
        PgType::Bool => "SqlType::Bool".into(),
        PgType::Int4 => "SqlType::Int4".into(),
        PgType::Int8 => "SqlType::Int8".into(),
        PgType::Numeric { typmod: Some((p, s)) } => format!("SqlType::Numeric {{ precision: {p}, scale: {s} }}"),
        PgType::Date => "SqlType::Date".into(),
        PgType::Timestamp => "SqlType::Timestamp".into(),
        PgType::Text => "SqlType::Text".into(),
        PgType::Varchar { max_chars: Some(n) } => format!("SqlType::Varchar {{ max_chars: {n} }}"),
        PgType::Bpchar { n: Some(n) } => format!("SqlType::Bpchar {{ len: {n} }}"),
        other => unreachable!("schema column without type modifier: {other:?}"),
    }
}
