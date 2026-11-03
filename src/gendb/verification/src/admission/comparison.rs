//! Result comparison: a candidate's rows are accepted exactly when they are an output the SQL allows
//! (`spec::order::ordered_ok`): the value AND display scale of every column, the ORDER BY key sequence, and within
//! every tie class a sub-multiset of the exact result. The exact result is the full ordered body (ORDER BY applied,
//! OFFSET and LIMIT not applied), so ties at the OFFSET/LIMIT boundary are accepted in any allowed choice.
//!
//! Test infrastructure, not a proof.

use gendb_frontend::ast::{AstDocument, FieldValue};
use gendb_sqlspec::codec::HostValue;
use gendb_sqlspec::pg_text::value_json;
use serde::Serialize;
use serde_json::{Value, json};
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

/// ORDER BY keys `(output column, descending, nulls first)`, OFFSET and LIMIT of a statement.
#[derive(Clone, Debug, Serialize)]
pub struct Window {
    pub keys: Vec<(usize, bool, bool)>,
    pub offset: u64,
    pub limit: Option<u64>,
}

impl Window {
    /// The window of the statement's root `OrderedQuery`.
    pub fn of(doc: &AstDocument) -> Window {
        let root = &doc.nodes[doc.root];
        let nat = |f: Option<&FieldValue>| match f {
            Some(FieldValue::Nat(x)) => Some(*x),
            _ => None,
        };
        let flag = |f: Option<&FieldValue>| matches!(f, Some(FieldValue::Bool(true)));
        let keys = root
            .children("keys")
            .unwrap_or_default()
            .iter()
            .map(|k| {
                let key = &doc.nodes[*k];
                (nat(key.field("col")).unwrap_or(0) as usize, flag(key.field("desc")), flag(key.field("nulls_first")))
            })
            .collect();
        let limit = match root.field("limit") {
            Some(FieldValue::OptNat(l)) => *l,
            _ => None,
        };
        Window { keys, offset: nat(root.field("offset")).unwrap_or(0), limit }
    }

    /// The ORDER BY key values of a row (numerics by value, so `1.0` ties with `1.00`).
    fn tie_class(&self, row: &[HostValue]) -> Vec<HostValue> {
        self.keys.iter().map(|(c, _, _)| row.get(*c).map(order_value).unwrap_or(HostValue::Null)).collect()
    }

    /// Sort a reference body by the ORDER BY keys (stable; ties keep their order, which the tie-aware comparison does
    /// not depend on).
    pub fn sort_body(&self, rows: &mut [Vec<HostValue>]) {
        rows.sort_by(|a, b| self.row_order(a, b));
    }

    /// The ORDER BY order of two rows (direction and NULL placement per key; numerics by value).
    pub fn row_order(&self, a: &[HostValue], b: &[HostValue]) -> Ordering {
        for (col, desc, nulls_first) in &self.keys {
            let (x, y) = (&a[*col], &b[*col]);
            let order = match (x == &HostValue::Null, y == &HostValue::Null) {
                (true, true) => Ordering::Equal,
                (true, false) => if *nulls_first { Ordering::Less } else { Ordering::Greater },
                (false, true) => if *nulls_first { Ordering::Greater } else { Ordering::Less },
                (false, false) => if *desc { compare_values(y, x) } else { compare_values(x, y) },
            };
            if order != Ordering::Equal {
                return order;
            }
        }
        Ordering::Equal
    }

    /// `rows` are in ORDER BY order: every key names an output column of every row, and no row sorts before its
    /// predecessor. `Err` names the first violation.
    pub fn check_ordered(&self, rows: &[Vec<HostValue>]) -> Result<(), String> {
        if let Some(row) = rows.iter().position(|r| self.keys.iter().any(|(c, _, _)| *c >= r.len())) {
            return Err(format!("row {row} has {} columns; an ORDER BY key names a column beyond them", rows[row].len()));
        }
        match rows.windows(2).position(|pair| self.row_order(&pair[0], &pair[1]) == Ordering::Greater) {
            Some(i) => Err(format!("row {} sorts before row {i} under ORDER BY", i + 1)),
            None => Ok(()),
        }
    }

    /// `Ok(rule)` iff `actual` is an allowed output given `full`, the exact full ordered body: `actual` has the
    /// window's length and the window's ORDER BY key sequence, and within every tie class its rows are a sub-multiset
    /// of `full`'s rows of that class. `Err` explains the first difference.
    pub fn allowed_output(&self, full: &[Vec<HostValue>], actual: &[Vec<HostValue>]) -> Result<&'static str, String> {
        let offset = (self.offset as usize).min(full.len());
        let end = self.limit.map_or(full.len(), |l| offset.saturating_add(l as usize).min(full.len()));
        let window = &full[offset..end];
        if actual.len() != window.len() {
            return Err(format!(
                "{} rows, the allowed outputs have {} (OFFSET {} LIMIT {:?} of {} ordered rows)",
                actual.len(),
                window.len(),
                self.offset,
                self.limit,
                full.len()
            ));
        }
        if actual.iter().map(|r| self.tie_class(r)).ne(window.iter().map(|r| self.tie_class(r))) {
            return Err("the ORDER BY key sequence differs from the allowed outputs'".into());
        }
        // Every row of `actual` must be taken from `full`'s rows of its own tie class, each at most as often as it
        // occurs there.
        let classes: BTreeSet<String> = actual.iter().map(|r| format!("{:?}", self.tie_class(r))).collect();
        let mut pool: BTreeMap<String, usize> = BTreeMap::new();
        for r in full {
            let class = format!("{:?}", self.tie_class(r));
            if classes.contains(&class) {
                *pool.entry(format!("{class}|{r:?}")).or_default() += 1;
            }
        }
        for r in actual {
            match pool.get_mut(&format!("{:?}|{r:?}", self.tie_class(r))) {
                Some(n) if *n > 0 => *n -= 1,
                _ => {
                    return Err(format!(
                        "row {} is not a row of its ORDER BY tie class in the exact result",
                        json!(rows_text(std::slice::from_ref(r)))
                    ));
                }
            }
        }
        Ok(match (self.keys.is_empty(), self.limit.is_some() || self.offset > 0) {
            (true, false) => "multiset equal (no ORDER BY)",
            (true, true) => "allowed: the window's length, a sub-multiset of the exact rows (no ORDER BY)",
            (false, false) => "allowed: ORDER BY key sequence equal, each tie class equal as a multiset",
            (false, true) => "allowed: OFFSET/LIMIT window, ORDER BY key sequence equal, each tie class a sub-multiset of the exact class",
        })
    }
}

/// A value as an ORDER BY key: numerics by value (trailing zeros of the coefficient removed), everything else as is.
fn order_value(v: &HostValue) -> HostValue {
    match v {
        HostValue::Num { coeff, scale } => {
            let (mut c, mut s) = (*coeff, *scale);
            while s > 0 && c % 10 == 0 {
                c /= 10;
                s -= 1;
            }
            HostValue::Num { coeff: c, scale: s }
        }
        other => other.clone(),
    }
}

/// Exact comparison of two values of one column: numerics by value (a rescaling that overflows `i128` is larger in
/// magnitude than any value that does not), text by bytes.
fn compare_values(a: &HostValue, b: &HostValue) -> Ordering {
    let at_scale = |c: i128, s: u32, t: u32| if c == 0 { Some(0) } else { 10i128.checked_pow(t - s).and_then(|m| c.checked_mul(m)) };
    match (a, b) {
        (HostValue::Int(x), HostValue::Int(y)) => x.cmp(y),
        (HostValue::Date(x), HostValue::Date(y)) => x.cmp(y),
        (HostValue::Ts(x), HostValue::Ts(y)) => x.cmp(y),
        (HostValue::Bool(x), HostValue::Bool(y)) => x.cmp(y),
        (HostValue::Text(x), HostValue::Text(y)) => x.cmp(y),
        (HostValue::Num { coeff: c1, scale: s1 }, HostValue::Num { coeff: c2, scale: s2 }) => {
            let t = (*s1).max(*s2);
            match (at_scale(*c1, *s1, t), at_scale(*c2, *s2, t)) {
                (Some(x), Some(y)) => x.cmp(&y),
                (None, _) => if *c1 > 0 { Ordering::Greater } else { Ordering::Less },
                (_, None) => if *c2 > 0 { Ordering::Less } else { Ordering::Greater },
            }
        }
        _ => Ordering::Equal,
    }
}

/// Rows as PostgreSQL output text for records and messages (a non-UTF-8 text is shown as null here; answers
/// themselves are compared exactly).
pub fn rows_text(rows: &[Vec<HostValue>]) -> Vec<Vec<Value>> {
    rows.iter().map(|r| r.iter().map(|x| value_json(x).unwrap_or(Value::Null)).collect()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn row(k: &str, coeff: i128, scale: u32) -> Vec<HostValue> {
        vec![HostValue::Text(k.as_bytes().to_vec()), HostValue::Num { coeff, scale }]
    }

    fn window(keys: &[(usize, bool)], offset: u64, limit: Option<u64>) -> Window {
        Window { keys: keys.iter().map(|(c, d)| (*c, *d, *d)).collect(), offset, limit }
    }

    /// ORDER BY s DESC LIMIT 2 over a full body whose rows 2..4 tie on s: exactly the windows `ordered_ok` allows.
    #[test]
    fn comparison_accepts_exactly_the_allowed_windows() {
        let full = vec![row("a", 900, 2), row("b", 500, 2), row("c", 500, 2), row("d", 500, 2), row("e", 100, 2)];
        let w = window(&[(1, true)], 0, Some(2));
        assert!(w.allowed_output(&full, &[row("a", 900, 2), row("b", 500, 2)]).is_ok());
        assert!(w.allowed_output(&full, &[row("a", 900, 2), row("d", 500, 2)]).is_ok(), "any tied row at the LIMIT boundary");
        assert!(w.allowed_output(&full, &[row("b", 500, 2), row("a", 900, 2)]).is_err(), "order of distinct keys");
        assert!(w.allowed_output(&full, &[row("a", 900, 2)]).is_err(), "window length");
        assert!(w.allowed_output(&full, &[row("a", 900, 2), row("z", 500, 2)]).is_err(), "not a row of the tie class");
        assert!(w.allowed_output(&full, &[row("a", 900, 2), row("b", 5, 0)]).is_err(), "scale is part of the value");
        let w = window(&[(1, true)], 1, Some(2));
        assert!(w.allowed_output(&full, &[row("d", 500, 2), row("b", 500, 2)]).is_ok());
        assert!(w.allowed_output(&full, &[row("b", 500, 2), row("b", 500, 2)]).is_err(), "multiplicity");
        let permuted = vec![row("a", 900, 2), row("c", 500, 2), row("d", 500, 2), row("b", 500, 2), row("e", 100, 2)];
        assert!(window(&[(1, true)], 0, None).allowed_output(&full, &permuted).is_ok());
        let full = vec![row("x", 500, 2), row("y", 50, 1)];
        assert!(window(&[(1, false)], 0, None).allowed_output(&full, &[row("y", 50, 1), row("x", 500, 2)]).is_ok());
        assert!(window(&[], 0, Some(1)).allowed_output(&full, &[row("y", 50, 1)]).is_ok());
        assert!(window(&[], 5, None).allowed_output(&full, &[]).is_ok());
    }

    /// A reference body is sorted by the statement's keys with numerics by value and explicit NULL placement.
    #[test]
    fn reference_bodies_sort_by_value_and_null_placement() {
        let mut rows = vec![vec![HostValue::Num { coeff: 5, scale: 0 }], vec![HostValue::Null], vec![HostValue::Num { coeff: 450, scale: 2 }]];
        Window { keys: vec![(0, false, false)], offset: 0, limit: None }.sort_body(&mut rows);
        assert_eq!(rows, vec![vec![HostValue::Num { coeff: 450, scale: 2 }], vec![HostValue::Num { coeff: 5, scale: 0 }], vec![HostValue::Null]]);
        Window { keys: vec![(0, true, true)], offset: 0, limit: None }.sort_body(&mut rows);
        assert_eq!(rows[0], vec![HostValue::Null]);
    }
}
