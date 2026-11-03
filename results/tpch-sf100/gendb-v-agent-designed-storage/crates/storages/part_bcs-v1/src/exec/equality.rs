//! Executable SQL value equality (`spec::equality`): IS NOT DISTINCT FROM on values and rows, and the DISTINCT
//! representatives of a row or value list (first occurrence of each class, in order). Exact (it uses
//! `compare_exec`, which never leaves the executable domain), so none of these functions can return `Capacity`.
//! Rows are `exec::relational::schema::view_rows` / `rows_ts_ok` and are copied with
//! `exec::relational::rows::clone_row`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::equality::*;
use crate::exec::value::*;
use crate::exec::scalar::*;
use crate::exec::relational::schema::*;
use crate::exec::relational::rows::*;

verus! {

/// `spec::equality::val_not_distinct`: `a IS NOT DISTINCT FROM b` (two NULLs are not distinct).
pub fn val_not_distinct_exec(a: &EVal, b: &EVal) -> (r: bool)
    ensures r == val_not_distinct(a@, b@),
{
    match (a, b) {
        (EVal::Null, EVal::Null) => true,
        (EVal::Null, _) | (_, EVal::Null) => false,
        _ => match compare_exec(a, b) {
            Some(c) => c == 0,
            None => false,
        },
    }
}

/// `spec::equality::row_not_distinct`: same width and every column pair not distinct.
pub fn row_not_distinct_exec(r: &ERow, s: &ERow) -> (b: bool)
    ensures b == row_not_distinct(view_row(r@), view_row(s@)),
{
    let ghost gr = view_row(r@);
    let ghost gs = view_row(s@);
    if r.len() != s.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < r.len()
        invariant
            i <= r.len(), r.len() == s.len(), gr == view_row(r@), gs == view_row(s@),
            forall|j: int| 0 <= j < i ==> val_not_distinct(#[trigger] gr[j], gs[j]),
        decreases r.len() - i,
    {
        if !val_not_distinct_exec(&r[i], &s[i]) {
            assert(!val_not_distinct(gr[i as int], gs[i as int]));
            return false;
        }
        i = i + 1;
    }
    true
}

/// `spec::equality::has_not_distinct`.
fn has_not_distinct_exec(d: &Vec<ERow>, k: &ERow) -> (b: bool)
    ensures b == has_not_distinct(view_rows(d@), view_row(k@)),
{
    let ghost gd = view_rows(d@);
    let ghost gk = view_row(k@);
    let mut i: usize = 0;
    while i < d.len()
        invariant
            i <= d.len(), gd == view_rows(d@), gk == view_row(k@),
            has_not_distinct(gd.take(i as int), gk) == false,
        decreases d.len() - i,
    {
        let ghost t = gd.take(i as int + 1);
        proof {
            assert(t.drop_last() =~= gd.take(i as int));
            assert(t.last() == view_row(d@[i as int]@));
        }
        if row_not_distinct_exec(&d[i], k) {
            proof { lemma_has_not_distinct_extends(gd, gk, i as int + 1); }
            return true;
        }
        i = i + 1;
    }
    proof { assert(gd.take(d.len() as int) =~= gd); }
    false
}

/// A prefix with a not-distinct row makes the whole sequence have one.
proof fn lemma_has_not_distinct_extends(rows: Seq<Row>, r: Row, n: int)
    requires 0 <= n <= rows.len(), has_not_distinct(rows.take(n), r),
    ensures has_not_distinct(rows, r),
    decreases rows.len(),
{
    if n == rows.len() {
        assert(rows.take(n) =~= rows);
    } else {
        let d = rows.drop_last();
        assert(d.take(n) =~= rows.take(n));
        lemma_has_not_distinct_extends(d, r, n);
    }
}

/// `spec::equality::distinct_rows` (first occurrence of each class, in order).
pub fn distinct_rows_exec(rows: &Vec<ERow>) -> (out: Vec<ERow>)
    requires rows_ts_ok(view_rows(rows@)),
    ensures
        view_rows(out@) == distinct_rows(view_rows(rows@)),
        rows_ts_ok(view_rows(out@)),
{
    let ghost g = view_rows(rows@);
    let mut out: Vec<ERow> = Vec::new();
    let mut i: usize = 0;
    while i < rows.len()
        invariant
            i <= rows.len(), g == view_rows(rows@), rows_ts_ok(g),
            view_rows(out@) == distinct_rows(g.take(i as int)),
            rows_ts_ok(view_rows(out@)),
        decreases rows.len() - i,
    {
        let ghost prev = view_rows(out@);
        proof {
            let t = g.take(i as int + 1);
            assert(t.drop_last() =~= g.take(i as int));
            assert(t.last() == g[i as int]);
            assert(g[i as int] == view_row(rows@[i as int]@));
        }
        if !has_not_distinct_exec(&out, &rows[i]) {
            let r = clone_row(&rows[i]);
            out.push(r);
            proof { assert(view_rows(out@) =~= prev.push(g[i as int])); }
        }
        i = i + 1;
    }
    proof { assert(g.take(rows.len() as int) =~= g); }
    out
}

/// `spec::equality::has_val_not_distinct`.
fn has_val_not_distinct_exec(d: &Vec<EVal>, v: &EVal) -> (b: bool)
    ensures b == has_val_not_distinct(view_row(d@), v@),
{
    let ghost gd = view_row(d@);
    let mut i: usize = 0;
    while i < d.len()
        invariant
            i <= d.len(), gd == view_row(d@),
            has_val_not_distinct(gd.take(i as int), v@) == false,
        decreases d.len() - i,
    {
        let ghost t = gd.take(i as int + 1);
        proof {
            assert(t.drop_last() =~= gd.take(i as int));
            assert(t.last() == d@[i as int]@);
        }
        if val_not_distinct_exec(&d[i], v) {
            proof { lemma_has_val_not_distinct_extends(gd, v@, i as int + 1); }
            return true;
        }
        i = i + 1;
    }
    proof { assert(gd.take(d.len() as int) =~= gd); }
    false
}

/// A prefix with a not-distinct value makes the whole sequence have one.
proof fn lemma_has_val_not_distinct_extends(vs: Seq<Val>, v: Val, n: int)
    requires 0 <= n <= vs.len(), has_val_not_distinct(vs.take(n), v),
    ensures has_val_not_distinct(vs, v),
    decreases vs.len(),
{
    if n == vs.len() {
        assert(vs.take(n) =~= vs);
    } else {
        let d = vs.drop_last();
        assert(d.take(n) =~= vs.take(n));
        lemma_has_val_not_distinct_extends(d, v, n);
    }
}

/// `spec::equality::distinct_vals` (the non-NULL values, first occurrence of each class, in order).
pub fn distinct_vals_exec(vs: &Vec<EVal>) -> (out: Vec<EVal>)
    ensures view_row(out@) == distinct_vals(view_row(vs@)),
{
    let ghost g = view_row(vs@);
    let mut out: Vec<EVal> = Vec::new();
    let mut i: usize = 0;
    while i < vs.len()
        invariant
            i <= vs.len(), g == view_row(vs@),
            view_row(out@) == distinct_vals(g.take(i as int)),
        decreases vs.len() - i,
    {
        let ghost prev = view_row(out@);
        proof {
            let t = g.take(i as int + 1);
            assert(t.drop_last() =~= g.take(i as int));
            assert(t.last() == g[i as int]);
            assert(g[i as int] == vs@[i as int]@);
        }
        if !matches!(vs[i], EVal::Null) && !has_val_not_distinct_exec(&out, &vs[i]) {
            let v = clone_val(&vs[i]);
            out.push(v);
            proof { assert(view_row(out@) =~= prev.push(g[i as int])); }
        }
        i = i + 1;
    }
    proof { assert(g.take(vs.len() as int) =~= g); }
    out
}

} // verus!
