//! The `schema` section: tables, their stored columns and declared constraints. Structure only (kinds, keys, positions
//! in range, a `pred` arena per CHECK); well-formedness (keys referenced by foreign keys, type pairs, CHECK typing) is
//! decided by the verified `constraints_wf`.

use super::super::document::{ColumnDef, ConstraintDef, ConstraintTiming, PgType, TableDef, REFERENTIAL_ACTIONS};
use super::super::schema::schema;
use super::super::{err, AstError};
use super::arena::decode_arena;
use super::types::decode_pg_type;
use super::{arena_root, check_params, expect_keys, string};
use serde_json::{Map, Value};

pub(super) fn decode_tables(s: &Map<String, Value>) -> Result<Vec<TableDef>, AstError> {
    expect_keys(s, &["tables"], "schema")?;
    let raw_tables = s["tables"].as_array().ok_or_else(|| AstError("schema.tables".into()))?;
    let table_count = raw_tables.len();
    let mut tables = Vec::with_capacity(table_count);
    for t in raw_tables {
        tables.push(decode_table(t, table_count)?);
    }
    check_referenced_columns(&tables)?;
    Ok(tables)
}

fn decode_table(t: &Value, table_count: usize) -> Result<TableDef, AstError> {
    let t = t.as_object().ok_or_else(|| AstError("table".into()))?;
    // Documents of parsers before v3 have no `constraints` key: their schema declared none.
    if t.contains_key("constraints") {
        expect_keys(t, &["name", "columns", "constraints"], "table")?;
    } else {
        expect_keys(t, &["name", "columns"], "table")?;
    }
    let mut columns = Vec::new();
    for c in t["columns"].as_array().ok_or_else(|| AstError("table.columns".into()))? {
        columns.push(decode_column(c)?);
    }
    let mut constraints = Vec::new();
    if let Some(cs) = t.get("constraints") {
        for c in cs.as_array().ok_or_else(|| AstError("table.constraints".into()))? {
            let constraint = decode_constraint(c, columns.len() as u64, table_count)
                .map_err(|e| AstError(format!("table {}: constraint: {}", string(t, "name").unwrap_or_default(), e.0)))?;
            constraints.push(constraint);
        }
    }
    Ok(TableDef { name: string(t, "name")?, columns, constraints })
}

fn decode_column(c: &Value) -> Result<ColumnDef, AstError> {
    let c = c.as_object().ok_or_else(|| AstError("column".into()))?;
    expect_keys(c, &["name", "type", "nullable"], "column")?;
    let ty = decode_pg_type(&c["type"])?;
    // Stored columns carry full type modifiers (Verus `SqlType`).
    if matches!(ty, PgType::Numeric { typmod: None } | PgType::Varchar { max_chars: None } | PgType::Bpchar { n: None }) {
        return err("schema column types need their type modifier");
    }
    Ok(ColumnDef { name: string(c, "name")?, ty, nullable: c["nullable"].as_bool().ok_or_else(|| AstError("column.nullable".into()))? })
}

/// Foreign-key column positions are checked against the referenced table once all tables are known.
fn check_referenced_columns(tables: &[TableDef]) -> Result<(), AstError> {
    for t in tables {
        for c in &t.constraints {
            if let ConstraintDef::ForeignKey { table, ref_columns, .. } = c {
                let referenced = &tables[*table as usize];
                if ref_columns.iter().any(|&r| r >= referenced.columns.len() as u64) {
                    return err(format!("table {}: referenced column outside table {}", t.name, referenced.name));
                }
            }
        }
    }
    Ok(())
}

/// One constraint of a table with `ncols` columns.
fn decode_constraint(v: &Value, ncols: u64, table_count: usize) -> Result<ConstraintDef, AstError> {
    let c = v.as_object().ok_or_else(|| AstError("not an object".into()))?;
    let name = match c.get("name") {
        Some(Value::Null) => None,
        Some(Value::String(n)) => Some(n.clone()),
        _ => return err("name must be null or a string"),
    };
    let flag = |k: &str| c.get(k).and_then(Value::as_bool).ok_or_else(|| AstError(format!("{k} must be a bool")));
    // A non-empty list of column positions, below `bound` when the table is known here.
    let positions = |k: &str, bound: Option<u64>| -> Result<Vec<u64>, AstError> {
        let list = c.get(k).and_then(Value::as_array).ok_or_else(|| AstError(format!("{k} must be a list")))?;
        let out: Vec<u64> = list.iter().map(|x| x.as_u64().ok_or_else(|| AstError(format!("{k}: column positions")))).collect::<Result<_, _>>()?;
        if out.is_empty() {
            return err(format!("{k} is empty"));
        }
        if bound.is_some_and(|n| out.iter().any(|&p| p >= n)) {
            return err(format!("{k}: column position outside the table"));
        }
        Ok(out)
    };
    let timing = || -> Result<ConstraintTiming, AstError> { Ok(ConstraintTiming { deferrable: flag("deferrable")?, initially_deferred: flag("initially_deferred")? }) };
    match c.get("kind").and_then(Value::as_str) {
        Some("key") => {
            expect_keys(c, &["kind", "name", "primary", "columns", "nulls_distinct", "deferrable", "initially_deferred"], "key")?;
            Ok(ConstraintDef::Key { name, primary: flag("primary")?, columns: positions("columns", Some(ncols))?, nulls_distinct: flag("nulls_distinct")?, timing: timing()? })
        }
        Some("foreign_key") => {
            expect_keys(c, &["kind", "name", "columns", "table", "ref_columns", "match_full", "on_delete", "on_update", "deferrable", "initially_deferred"], "foreign_key")?;
            let table = c["table"].as_u64().filter(|&t| (t as usize) < table_count).ok_or_else(|| AstError("table must be a table id of the schema".into()))?;
            let action = |k: &str| -> Result<String, AstError> {
                c.get(k)
                    .and_then(Value::as_str)
                    .filter(|a| REFERENTIAL_ACTIONS.contains(a))
                    .map(str::to_owned)
                    .ok_or_else(|| AstError(format!("{k} must be one of {REFERENTIAL_ACTIONS:?}")))
            };
            Ok(ConstraintDef::ForeignKey {
                name,
                columns: positions("columns", Some(ncols))?,
                table,
                ref_columns: positions("ref_columns", None)?,
                match_full: flag("match_full")?,
                on_delete: action("on_delete")?,
                on_update: action("on_update")?,
                timing: timing()?,
            })
        }
        Some("check") => {
            expect_keys(c, &["kind", "name", "root", "nodes"], "check")?;
            let raw_nodes = c["nodes"].as_array().ok_or_else(|| AstError("nodes must be a list".into()))?;
            let nodes = decode_arena(raw_nodes, table_count)?;
            // A CHECK has no statement parameters.
            check_params(&nodes, &[])?;
            let root = arena_root(&nodes, &c["root"])?;
            if schema().kinds[&nodes[root].tag].sort != "pred" {
                return err("the CHECK root must be a pred");
            }
            Ok(ConstraintDef::Check { name, nodes, root })
        }
        _ => err("kind must be key, foreign_key or check"),
    }
}
