//! The complete database of one tiny case: every schema table (table id = position) with every column. It is the one
//! value the verified evaluator labels and every input of the case is projected from, row by row: the candidate's
//! inline columns ([`super::inline_columns`]) and every storage's tiny input ([`super::storage_case_input`]).
//!
//! Without declared integrity constraints it is the database the cases have always had: each delivered table with its
//! delivered columns, every other column at a default of its type (NULL when nullable), every other table empty.
//!
//! With declared constraints those defaults violate most keys and foreign keys, and generated rows can repeat a key
//! (rows varied while their key's equality class stays equal) or reference a missing parent. A small deterministic
//! heuristic completes and repairs them, so such cases stay valid instead of being dropped. The complete database is
//! the one value both the verified evaluator's labels and every input are taken from, so a repair changes what a case
//! tests, never the soundness of its comparison.
//! - Keys: in each row, the key's undecided cells get a value distinct per row (only the key columns that are not
//!   foreign-key columns of the table, when there are such).
//! - Repeated keys: a row whose fully decided key repeats an earlier row's gets a fresh value, unused in that column, in
//!   one key column (a column that is not a foreign-key column of the table when there is one, else the last).
//! - Foreign keys: the undecided referencing cells of a row take the referenced values of the first parent row that
//!   agrees with its decided cells. When no parent row agrees, a parent row is added (defaults, the referenced columns
//!   set to the row's values), also to a table the statement delivers (its other cells are completed like any other);
//!   its own keys and foreign keys are completed in the next round. At most one round per table plus one: a cycle that
//!   keeps adding rows stops there.
//! - CHECK: per column a CHECK reads that has undecided cells, the first candidate value (the default, the CHECK's
//!   literals and their neighbours, small values of the type) that a host pre-test of the table's CHECKs accepts in
//!   every such row; otherwise the default stays.
//!
//! This is not a constraint solver: cyclic, composite, overlapping or CHECK-coupled declarations can leave the database
//! outside the constraints. The pre-test is only a heuristic too. The verified evaluator decides `constraints_hold` on
//! every complete database it labels; a case it does not certify is never run ([`super::certification`]).

use super::constants::{Constants, collect_constants, small_values, text_fits, values_near};
use super::storage_input::source_type;
use super::{CaseTables, DAYS_1970_TO_2000, default_value, host_value};
use crate::obligations::DeclaredType;
use gendb_frontend::ast::{ConstraintDef, FieldValue, Node, PgType, TableDef};
use gendb_frontend::columns::SourceDeclaration;
use gendb_sqlspec::codec::{HostTables, HostValue};
use gendb_sqlspec::pg_text::parse_date;
use std::cmp::Ordering;

/// The complete database of the case `tables` (rows of the `declaration`'s delivered tables) over the dataset
/// `schema` (module documentation).
pub fn complete_database(schema: &[TableDef], declaration: &SourceDeclaration, tables: &CaseTables) -> HostTables {
    let mut completion = Completion::of_delivered(schema, declaration, tables);
    if schema.iter().any(|t| !t.constraints.is_empty()) {
        for _ in 0..=schema.len() {
            let keys = completion.distinguish_keys();
            let repeated = completion.rekey_repeated_keys();
            let parents = completion.reference_parents();
            if !keys && !repeated && !parents {
                break;
            }
        }
        completion.satisfy_checks();
    }
    completion.tables
}

/// A database being completed, with which cells are decided.
struct Completion<'a> {
    schema: &'a [TableDef],
    tables: HostTables,
    /// `decided[t][row][column]`: delivered, or set by an earlier step.
    decided: Vec<Vec<Vec<bool>>>,
}

impl<'a> Completion<'a> {
    /// The delivered rows with defaults elsewhere: delivered cells are decided.
    fn of_delivered(schema: &'a [TableDef], declaration: &SourceDeclaration, tables: &CaseTables) -> Self {
        let mut completion = Completion { schema, tables: vec![], decided: vec![] };
        for (table_id, def) in schema.iter().enumerate() {
            let delivered = declaration.tables.iter().position(|t| t.table_id == table_id);
            let (mut rows, mut decided) = (vec![], vec![]);
            for row in delivered.map_or(&[][..], |j| &tables[j]) {
                let j = delivered.expect("rows come from a delivered table");
                let mut values = default_row(def);
                let mut known = vec![false; def.columns.len()];
                for (k, column) in declaration.tables[j].columns.iter().enumerate() {
                    values[column.ordinal] = host_value(column.ty, &row[k]);
                    known[column.ordinal] = true;
                }
                rows.push(values);
                decided.push(known);
            }
            completion.tables.push(rows);
            completion.decided.push(decided);
        }
        completion
    }

    /// Set an undecided cell and mark it decided.
    fn decide(&mut self, t: usize, row: usize, column: usize, value: HostValue) {
        self.tables[t][row][column] = value;
        self.decided[t][row][column] = true;
    }

    /// Give the undecided key cells of every row a value distinct per row; whether any cell changed.
    fn distinguish_keys(&mut self) -> bool {
        let schema = self.schema;
        let mut changed = false;
        for (t, def) in schema.iter().enumerate() {
            let foreign = foreign_key_columns(def);
            for constraint in &def.constraints {
                let ConstraintDef::Key { columns, .. } = constraint else { continue };
                for row in 0..self.tables[t].len() {
                    let undecided: Vec<usize> = columns.iter().map(|c| *c as usize).filter(|c| !self.decided[t][row][*c]).collect();
                    let own: Vec<usize> = undecided.iter().copied().filter(|c| !foreign.contains(c)).collect();
                    for c in if own.is_empty() { undecided } else { own } {
                        if let Some(value) = distinct_value(&def.columns[c].ty, row) {
                            self.decide(t, row, c, value);
                            changed = true;
                        }
                    }
                }
            }
        }
        changed
    }

    /// Give a row whose fully decided key repeats an earlier row's key a fresh value in one key column; whether any
    /// cell changed. A key with a NULL never repeats (`nulls_distinct`) and is left as it is.
    fn rekey_repeated_keys(&mut self) -> bool {
        let schema = self.schema;
        let mut changed = false;
        for (t, def) in schema.iter().enumerate() {
            let foreign = foreign_key_columns(def);
            for constraint in &def.constraints {
                let ConstraintDef::Key { columns, .. } = constraint else { continue };
                let columns: Vec<usize> = columns.iter().map(|c| *c as usize).collect();
                let Some(&changeable) = columns.iter().rev().find(|c| !foreign.contains(c)).or(columns.last()) else { continue };
                let mut seen: Vec<Vec<HostValue>> = vec![];
                for row in 0..self.tables[t].len() {
                    if !columns.iter().all(|c| self.decided[t][row][*c]) {
                        continue;
                    }
                    let key: Vec<HostValue> = columns.iter().map(|c| self.tables[t][row][*c].clone()).collect();
                    if key.contains(&HostValue::Null) {
                        continue;
                    }
                    if seen.contains(&key) {
                        let used: Vec<&HostValue> = self.tables[t].iter().map(|r| &r[changeable]).collect();
                        if let Some(value) = fresh_value(&def.columns[changeable].ty, &used) {
                            self.decide(t, row, changeable, value);
                            changed = true;
                            seen.push(columns.iter().map(|c| self.tables[t][row][*c].clone()).collect());
                        }
                    } else {
                        seen.push(key);
                    }
                }
            }
        }
        changed
    }

    /// Give every row whose foreign key is not yet satisfied a parent: an agreeing parent row's referenced values, or an
    /// added parent row; whether anything changed.
    fn reference_parents(&mut self) -> bool {
        let schema = self.schema;
        let mut changed = false;
        for (t, def) in schema.iter().enumerate() {
            for constraint in &def.constraints {
                let ConstraintDef::ForeignKey { columns, table, ref_columns, match_full, .. } = constraint else { continue };
                let (columns, ref_columns): (Vec<usize>, Vec<usize>) =
                    (columns.iter().map(|c| *c as usize).collect(), ref_columns.iter().map(|c| *c as usize).collect());
                let parent = *table as usize;
                for row in 0..self.tables[t].len() {
                    let key: Vec<HostValue> = columns.iter().map(|c| self.tables[t][row][*c].clone()).collect();
                    let nulls = key.iter().filter(|v| **v == HostValue::Null).count();
                    // SQL: a key with a NULL references nothing (MATCH FULL: only when every column is NULL).
                    if nulls == key.len() || (nulls > 0 && !match_full) {
                        continue;
                    }
                    let agrees = |parent_row: &Vec<HostValue>| {
                        columns.iter().zip(&ref_columns).all(|(c, r)| !self.decided[t][row][*c] || parent_row[*r] == self.tables[t][row][*c])
                    };
                    let found = self.tables[parent].iter().position(agrees);
                    let undecided: Vec<usize> = (0..columns.len()).filter(|i| !self.decided[t][row][columns[*i]]).collect();
                    match found {
                        Some(p) => {
                            for i in undecided {
                                let value = self.tables[parent][p][ref_columns[i]].clone();
                                self.decide(t, row, columns[i], value);
                                changed = true;
                            }
                        }
                        None => {
                            let mut added = default_row(&schema[parent]);
                            let mut known = vec![false; added.len()];
                            for (c, r) in columns.iter().zip(&ref_columns) {
                                added[*r] = self.tables[t][row][*c].clone();
                                known[*r] = true;
                            }
                            for i in undecided {
                                self.decided[t][row][columns[i]] = true;
                            }
                            self.tables[parent].push(added);
                            self.decided[parent].push(known);
                            changed = true;
                        }
                    }
                }
            }
        }
        changed
    }

    /// Per table and CHECK-read column with undecided cells: the first candidate value the table's CHECKs accept (host
    /// pre-test) in every row with an undecided cell there; otherwise the default stays.
    fn satisfy_checks(&mut self) {
        let schema = self.schema;
        for (t, def) in schema.iter().enumerate() {
            let checks: Vec<(&[Node], usize)> = def
                .constraints
                .iter()
                .filter_map(|c| match c {
                    ConstraintDef::Check { nodes, root, .. } => Some((nodes.as_slice(), *root)),
                    _ => None,
                })
                .collect();
            if checks.is_empty() {
                continue;
            }
            let mut read: Vec<usize> = checks.iter().flat_map(|(nodes, _)| nodes.iter().filter(|n| n.tag == "Col").filter_map(column_index)).collect();
            read.sort_unstable();
            read.dedup();
            let mut constants = Constants::default();
            for (nodes, root) in &checks {
                collect_constants(nodes, *root, &mut constants);
            }
            for c in read {
                let rows: Vec<usize> = (0..self.tables[t].len()).filter(|r| !self.decided[t][*r][c]).collect();
                if rows.is_empty() {
                    continue;
                }
                let accepted = check_candidates(&def.columns[c].ty, &constants).into_iter().find(|value| {
                    rows.iter().all(|r| {
                        let mut row = self.tables[t][*r].clone();
                        row[c] = value.clone();
                        checks.iter().all(|(nodes, root)| pretest(nodes, *root, &row) == Some(true))
                    })
                });
                if let Some(value) = accepted {
                    for r in rows {
                        self.decide(t, r, c, value.clone());
                    }
                }
            }
        }
    }
}

/// The columns of `def` that some foreign key of it references from.
fn foreign_key_columns(def: &TableDef) -> Vec<usize> {
    def.constraints
        .iter()
        .flat_map(|c| match c {
            ConstraintDef::ForeignKey { columns, .. } => columns.iter().map(|c| *c as usize).collect(),
            _ => vec![],
        })
        .collect()
}

/// A value of `ty` not in `used` (a column's current values): the smallest non-negative number (date, timestamp) or
/// decimal text that is unused and fits the type (generated keys may sit at a type's extremes, so "largest + 1" could
/// overflow); `None` when the domain has none left (a full `char(1)`, a boolean).
fn fresh_value(ty: &PgType, used: &[&HostValue]) -> Option<HostValue> {
    let candidate = |n: usize| -> Option<HostValue> {
        match ty {
            PgType::Bool => (n < 2).then_some(HostValue::Bool(n == 1)),
            PgType::Int4 => i32::try_from(n).ok().map(|i| HostValue::Int(i as i64)),
            PgType::Int8 => i64::try_from(n).ok().map(HostValue::Int),
            PgType::Numeric { typmod } => {
                let scale = typmod.map_or(0, |(_, s)| s as u32);
                let coeff = (n as i128).checked_mul(10i128.checked_pow(scale)?)?;
                let fits = typmod.is_none_or(|(p, _)| u32::try_from(p).ok().and_then(|p| 10i128.checked_pow(p)).is_none_or(|bound| coeff < bound));
                fits.then_some(HostValue::Num { coeff, scale })
            }
            PgType::Date => i32::try_from(n).ok().map(HostValue::Date),
            PgType::Timestamp => i64::try_from(n).ok().map(HostValue::Ts),
            PgType::Text | PgType::Varchar { .. } | PgType::Bpchar { .. } => {
                let text = n.to_string();
                text_fits(ty, &text).then(|| HostValue::Text(text.into_bytes()))
            }
        }
    };
    (0..=used.len()).filter_map(candidate).find(|value| !used.contains(&value))
}

/// A row of `def` with every column at its default (NULL when nullable).
fn default_row(def: &TableDef) -> Vec<HostValue> {
    def.columns.iter().map(|c| if c.nullable { HostValue::Null } else { default_value(&c.ty) }).collect()
}

/// The `row`-th value of a key column, distinct per row; `None` when the column's domain has no such value (a `char(1)`
/// key has ten, a `numeric(1, 0)` key nine, a boolean two), so the cell keeps its default.
fn distinct_value(ty: &PgType, row: usize) -> Option<HostValue> {
    let n = row as i64 + 1;
    match ty {
        PgType::Bool => (row < 2).then_some(HostValue::Bool(row == 1)),
        PgType::Int4 => i32::try_from(n).ok().map(|i| HostValue::Int(i as i64)),
        PgType::Int8 => Some(HostValue::Int(n)),
        PgType::Numeric { typmod } => {
            let fits = typmod.is_none_or(|(p, _)| u32::try_from(p).ok().and_then(|p| 10i128.checked_pow(p)).is_none_or(|bound| (n as i128) < bound));
            fits.then_some(HostValue::Num { coeff: n as i128, scale: typmod.map_or(0, |(_, s)| s as u32) })
        }
        PgType::Date => Some(HostValue::Date(n as i32)),
        PgType::Timestamp => Some(HostValue::Ts(n)),
        PgType::Text | PgType::Varchar { .. } | PgType::Bpchar { .. } => {
            let text = n.to_string();
            text_fits(ty, &text).then(|| HostValue::Text(text.into_bytes()))
        }
    }
}

/// Candidate values of a CHECK-read column, the default first: the CHECK's literals and their neighbours, then small
/// values of the type (in its ABI unit, converted); text: the CHECK's text literals.
fn check_candidates(ty: &PgType, constants: &Constants) -> Vec<HostValue> {
    let mut out = vec![default_value(ty)];
    match (ty, DeclaredType::of(ty).map(source_type)) {
        (PgType::Bool, _) => out.push(HostValue::Bool(true)),
        (_, Some(source)) => {
            let near = values_near(source, constants);
            let small = if matches!(ty, PgType::Text | PgType::Varchar { .. } | PgType::Bpchar { .. }) { vec![] } else { small_values(source) };
            for x in near.into_iter().chain(small) {
                out.extend(host_number(ty, x));
            }
            if matches!(source, gendb_frontend::columns::SourceType::Utf8) {
                out.extend(constants.texts.iter().filter(|t| text_fits(ty, t)).map(|t| HostValue::Text(t.clone().into_bytes())));
            }
        }
        _ => {}
    }
    out.dedup();
    out
}

/// A number in the ABI unit of `ty` as the evaluator's value.
fn host_number(ty: &PgType, x: i128) -> Option<HostValue> {
    match ty {
        PgType::Int4 => i32::try_from(x).ok().map(|i| HostValue::Int(i as i64)),
        PgType::Int8 => i64::try_from(x).ok().map(HostValue::Int),
        PgType::Numeric { typmod: Some((_, s)) } => Some(HostValue::Num { coeff: x, scale: *s as u32 }),
        PgType::Date => i32::try_from(x - DAYS_1970_TO_2000 as i128).ok().map(HostValue::Date),
        _ => None,
    }
}

fn column_index(node: &Node) -> Option<usize> {
    match node.field("index") {
        Some(FieldValue::Nat(i)) => Some(*i as usize),
        _ => None,
    }
}

/// Host pre-test of one CHECK on a row: `Some(true)` when the predicate is not False (SQL's CHECK rule; Unknown passes),
/// `Some(false)` when it is False, `None` when the pre-test cannot evaluate it. Only a heuristic: the verified evaluator
/// decides.
fn pretest(nodes: &[Node], root: usize, row: &[HostValue]) -> Option<bool> {
    predicate(nodes, root, row).map(|truth| truth != Some(false))
}

/// Kleene truth of a predicate node (`None` inside: Unknown); outer `None`: not evaluable here.
fn predicate(nodes: &[Node], id: usize, row: &[HostValue]) -> Option<Option<bool>> {
    let node = &nodes[id];
    let child = |name: &str| node.child(name);
    match node.tag.as_str() {
        "And" | "Or" => {
            let (a, b) = (predicate(nodes, child("a")?, row)?, predicate(nodes, child("b")?, row)?);
            let and = node.tag == "And";
            Some(match (a, b) {
                (Some(x), Some(y)) => Some(if and { x && y } else { x || y }),
                (Some(x), None) | (None, Some(x)) if x != and => Some(x),
                _ => None,
            })
        }
        "Not" => predicate(nodes, child("p")?, row).map(|t| t.map(|x| !x)),
        "IsNull" => Some(Some(expression(nodes, child("e")?, row)? == HostValue::Null)),
        "OfBool" => match expression(nodes, child("e")?, row)? {
            HostValue::Bool(b) => Some(Some(b)),
            HostValue::Null => Some(None),
            _ => None,
        },
        "Cmp" => {
            let (a, b) = (expression(nodes, child("a")?, row)?, expression(nodes, child("b")?, row)?);
            if a == HostValue::Null || b == HostValue::Null {
                return Some(None);
            }
            let order = compare(&a, &b)?;
            let op = match node.field("op") {
                Some(FieldValue::Enum(op)) => op.as_str(),
                _ => return None,
            };
            Some(Some(match op {
                "Eq" => order == Ordering::Equal,
                "Ne" => order != Ordering::Equal,
                "Lt" => order == Ordering::Less,
                "Le" => order != Ordering::Greater,
                "Gt" => order == Ordering::Greater,
                "Ge" => order != Ordering::Less,
                _ => return None,
            }))
        }
        _ => None,
    }
}

/// The value of an expression node (`Col`, `Lit`, widening `Cast`); `None` outside the pre-test.
fn expression(nodes: &[Node], id: usize, row: &[HostValue]) -> Option<HostValue> {
    let node = &nodes[id];
    match node.tag.as_str() {
        "Col" => row.get(column_index(node)?).cloned(),
        "Lit" => literal(&nodes[node.child("lit")?]),
        "Cast" => {
            let value = expression(nodes, node.child("arg")?, row)?;
            match (node.field("cast"), value) {
                (_, HostValue::Null) => Some(HostValue::Null),
                (Some(FieldValue::Enum(c)), HostValue::Int(i)) if c == "Int4ToInt8" => Some(HostValue::Int(i)),
                (Some(FieldValue::Enum(c)), HostValue::Int(i)) if c == "IntToNumeric" => Some(HostValue::Num { coeff: i as i128, scale: 0 }),
                _ => None,
            }
        }
        _ => None,
    }
}

fn literal(node: &Node) -> Option<HostValue> {
    let int = |name: &str| match node.field(name) {
        Some(FieldValue::Int(s)) => s.parse::<i128>().ok(),
        Some(FieldValue::Nat(n)) => Some(*n as i128),
        _ => None,
    };
    match node.tag.as_str() {
        "Null" => Some(HostValue::Null),
        "Bool" => match node.field("value") {
            Some(FieldValue::Bool(b)) => Some(HostValue::Bool(*b)),
            _ => None,
        },
        "Int" => i64::try_from(int("v")?).ok().map(HostValue::Int),
        "Num" => Some(HostValue::Num { coeff: int("coeff")?, scale: u32::try_from(int("scale")?).ok()? }),
        "Date" => parse_date(&format!("{:04}-{:02}-{:02}", int("y")?, int("m")?, int("d")?)).and_then(|d| i32::try_from(d).ok()).map(HostValue::Date),
        "Text" => match node.field("bytes") {
            Some(FieldValue::Bytes(t)) => Some(HostValue::Text(t.clone().into_bytes())),
            _ => None,
        },
        _ => None,
    }
}

/// SQL order of two non-NULL values of comparable types (numbers by value across scales, text by bytes).
fn compare(a: &HostValue, b: &HostValue) -> Option<Ordering> {
    let number = |v: &HostValue| match v {
        HostValue::Int(i) => Some((*i as i128, 0u32)),
        HostValue::Num { coeff, scale } => Some((*coeff, *scale)),
        _ => None,
    };
    match (a, b) {
        (HostValue::Bool(x), HostValue::Bool(y)) => Some(x.cmp(y)),
        (HostValue::Date(x), HostValue::Date(y)) => Some(x.cmp(y)),
        (HostValue::Ts(x), HostValue::Ts(y)) => Some(x.cmp(y)),
        (HostValue::Text(x), HostValue::Text(y)) => Some(x.cmp(y)),
        _ => {
            let ((x, sx), (y, sy)) = (number(a)?, number(b)?);
            let scale = sx.max(sy);
            let at = |c: i128, s: u32| 10i128.checked_pow(scale - s).and_then(|m| c.checked_mul(m));
            Some(at(x, sx)?.cmp(&at(y, sy)?))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::admission::cases::CaseValue;
    use gendb_frontend::ast::{ColumnDef, ConstraintTiming};
    use gendb_frontend::columns::{SourceColumn, SourceTable, SourceType};

    const TIMING: ConstraintTiming = ConstraintTiming { deferrable: false, initially_deferred: false };

    fn key(columns: &[u64]) -> ConstraintDef {
        ConstraintDef::Key { name: None, primary: true, columns: columns.to_vec(), nulls_distinct: true, timing: TIMING }
    }

    fn foreign(columns: &[u64], table: u64, ref_columns: &[u64]) -> ConstraintDef {
        ConstraintDef::ForeignKey {
            name: None,
            columns: columns.to_vec(),
            table,
            ref_columns: ref_columns.to_vec(),
            match_full: false,
            on_delete: "no_action".into(),
            on_update: "no_action".into(),
            timing: TIMING,
        }
    }

    fn int_table(name: &str, columns: &[&str], constraints: Vec<ConstraintDef>) -> TableDef {
        TableDef { name: name.into(), columns: columns.iter().map(|c| ColumnDef { name: c.to_string(), ty: PgType::Int8, nullable: false }).collect(), constraints }
    }

    /// Delivered: `table_id`'s columns `ordinals` (all int8).
    fn delivered(tables: &[(usize, &str, &[usize])]) -> SourceDeclaration {
        SourceDeclaration {
            tables: tables
                .iter()
                .enumerate()
                .map(|(index, (table_id, name, ordinals))| SourceTable {
                    index,
                    table_id: *table_id,
                    name: name.to_string(),
                    columns: ordinals.iter().map(|o| SourceColumn { ordinal: *o, name: format!("c{o}"), ty: SourceType::Int64, row_count_only: false, nullable: false }).collect(),
                })
                .collect(),
        }
    }

    fn rows(values: &[&[i128]]) -> Vec<Vec<CaseValue>> {
        values.iter().map(|r| r.iter().map(|v| CaseValue::Num(*v)).collect()).collect()
    }

    fn int(i: i64) -> HostValue {
        HostValue::Int(i)
    }

    /// The case's delivered cells, read back from the complete database (table by table, row by row).
    fn delivered_cells(database: &HostTables, declaration: &SourceDeclaration) -> Vec<Vec<Vec<HostValue>>> {
        declaration.tables.iter().map(|t| database[t.table_id].iter().map(|row| t.columns.iter().map(|c| row[c.ordinal].clone()).collect()).collect()).collect()
    }

    /// Without constraints the complete database is the delivered rows with defaults and empty other tables.
    #[test]
    fn without_constraints_it_is_the_default_filled_database() {
        let schema = [int_table("p", &["k", "v"], vec![]), int_table("c", &["a", "b", "x"], vec![])];
        let declaration = delivered(&[(1, "c", &[2])]);
        let database = complete_database(&schema, &declaration, &vec![rows(&[&[5], &[5]])]);
        assert_eq!(database, vec![vec![], vec![vec![int(0), int(0), int(5)], vec![int(0), int(0), int(5)]]]);
    }

    /// A two-table PK/FK case: the child's key gets distinct values, its reference one added parent (the parent is not
    /// delivered), delivered values and delivered row counts unchanged.
    #[test]
    fn a_primary_and_foreign_key_case_completes_without_touching_delivered_rows() {
        let schema = [
            int_table("p", &["k", "v"], vec![key(&[0])]),
            int_table("c", &["a", "b", "x"], vec![key(&[0, 1]), foreign(&[0], 0, &[0])]),
        ];
        let declaration = delivered(&[(1, "c", &[2])]);
        let tables = vec![rows(&[&[5], &[5], &[7]])];
        let database = complete_database(&schema, &declaration, &tables);
        assert_eq!(delivered_cells(&database, &declaration), vec![vec![vec![int(5)], vec![int(5)], vec![int(7)]]]);
        // Key (a, b): b (not a foreign-key column) distinct per row; a references the one added parent row k = 0.
        assert_eq!(database[1], vec![vec![int(0), int(1), int(5)], vec![int(0), int(2), int(5)], vec![int(0), int(3), int(7)]]);
        assert_eq!(database[0], vec![vec![int(0), int(0)]]);
    }

    /// A reference into a delivered parent takes an agreeing parent row's key; no row is added to the parent.
    #[test]
    fn a_reference_into_a_delivered_parent_uses_its_rows() {
        let schema = [int_table("p", &["k", "v"], vec![key(&[0])]), int_table("c", &["a", "x"], vec![foreign(&[0], 0, &[0])])];
        let declaration = delivered(&[(0, "p", &[0, 1]), (1, "c", &[1])]);
        let tables = vec![rows(&[&[3, 30], &[4, 40]]), rows(&[&[9]])];
        let database = complete_database(&schema, &declaration, &tables);
        assert_eq!(database[0].len(), 2);
        assert_eq!(database[1], vec![vec![int(3), int(9)]]);
    }

    /// A delivered reference with no parent row in a delivered parent gets an added parent row (delivered values
    /// unchanged); a repeated delivered key gets a fresh value.
    #[test]
    fn a_missing_parent_is_added_and_a_repeated_key_rekeyed() {
        let schema = [int_table("p", &["k", "v"], vec![key(&[0])]), int_table("c", &["a"], vec![foreign(&[0], 0, &[0])])];
        let declaration = delivered(&[(0, "p", &[0, 1]), (1, "c", &[0])]);
        let tables = vec![rows(&[&[1, 10], &[1, 11]]), rows(&[&[5]])];
        let database = complete_database(&schema, &declaration, &tables);
        assert_eq!(database[0], vec![vec![int(1), int(10)], vec![int(0), int(11)], vec![int(5), int(0)]]);
        assert_eq!(database[1], vec![vec![int(5)]]);
        // Keys at the type's maximum: the fresh key is the smallest unused value, not an overflowing maximum + 1.
        let tables = vec![rows(&[&[i64::MAX as i128, 1], &[i64::MAX as i128, 2]]), rows(&[])];
        let database = complete_database(&schema, &declaration, &tables);
        assert_eq!(database[0], vec![vec![int(i64::MAX), int(1)], vec![int(0), int(2)]]);
    }

    /// A self-referencing key cycle (t.k references t.p, both keys) keeps adding rows; the completion stops after its
    /// bounded rounds instead of looping, and the result is left for the evaluator to judge.
    #[test]
    fn a_cyclic_declaration_stops_after_its_rounds() {
        let schema = [int_table("t", &["k", "p"], vec![key(&[0]), ConstraintDef::Key { name: None, primary: false, columns: vec![1], nulls_distinct: true, timing: TIMING }, foreign(&[0], 0, &[1])]),
            int_table("u", &["x"], vec![foreign(&[0], 0, &[0])])];
        let declaration = delivered(&[(1, "u", &[0])]);
        let database = complete_database(&schema, &declaration, &vec![rows(&[&[7]])]);
        // Every round adds one row whose key needs another: bounded by the round count (tables + 1).
        assert!(database[0].len() <= schema.len() + 2, "{database:?}");
        let referenced: Vec<&HostValue> = database[0].iter().map(|r| &r[1]).collect();
        assert!(database[0].iter().any(|r| !referenced.contains(&&r[0])), "the last row's reference is unmet: {database:?}");
    }

    /// An undelivered CHECK-read column takes the first candidate the pre-test accepts; delivered cells are untouched.
    #[test]
    fn an_undelivered_check_column_takes_an_accepted_value() {
        use crate::admission::integrity_constraints::{ConstraintDeclaration, IntegrityConstraints, USER_DECLARED};
        use gendb_artifacts::{ColType, ColumnSpec};
        use gendb_storage::import::{DataFormat, DatasetSpec, TableSpec};
        let column = |name: &str, ty| ColumnSpec { name: name.into(), ty, nullable: false };
        let dataset = DatasetSpec {
            tables: vec![TableSpec {
                name: "t".into(),
                fields: vec![column("a", ColType::I64), column("q", ColType::I32), column("d", ColType::Date32)],
                locations: vec!["t.parquet".into()],
                format: DataFormat::Parquet,
            }],
        };
        let declared = IntegrityConstraints {
            trust: USER_DECLARED.into(),
            declarations: vec![ConstraintDeclaration { table: "t".into(), sql: "CONSTRAINT q_range CHECK (q > 0 AND q <= 50 AND d >= DATE '1992-01-01')".into() }],
        };
        let scratch = std::env::temp_dir().join(format!("gendb-complete-case-{}", std::process::id()));
        let parser = gendb_frontend::parser::SqlParser::from_environment().unwrap();
        let statement = crate::admission::prepare_statement(&parser, &dataset, Some(&declared), "SELECT a FROM t", &[], &[], &[], &scratch).unwrap_or_else(|r| panic!("{}", r.error));
        let schema = &statement.instance.doc.tables;
        let declaration = delivered(&[(0, "t", &[0])]);
        let database = complete_database(schema, &declaration, &vec![rows(&[&[1], &[2]])]);
        let ConstraintDef::Check { nodes, root, .. } = &schema[0].constraints[0] else { panic!("a CHECK") };
        for (i, row) in database[0].iter().enumerate() {
            assert_eq!(row[0], int(i as i64 + 1));
            assert_eq!(pretest(nodes, *root, row), Some(true), "{row:?}");
        }
        // The defaults fail it: the completion changed them.
        assert_eq!(pretest(nodes, *root, &[int(1), int(0), HostValue::Date(0)]), Some(false));
        std::fs::remove_dir_all(&scratch).ok();
    }
}
