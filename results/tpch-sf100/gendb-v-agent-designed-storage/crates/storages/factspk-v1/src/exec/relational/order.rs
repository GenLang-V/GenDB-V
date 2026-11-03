//! `ORDER BY` / `LIMIT` / `OFFSET` over materialized rows: key comparison (`keys_cmp_exec`), the stable insertion
//! sort of `spec::order::sort_rows` (`sort_rows_exec`) and OFFSET/LIMIT slicing (`slice_rows_exec`), with the facts
//! that sorting and slicing keep the timestamp representation invariant. Sorting never leaves the executable
//! domain. Query implementations may use these helpers; the top-level statement evaluator that applies them to the
//! canonical body rows is `exec::relational::entry::exec_ordered`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::exec::value::*;
use crate::exec::ast::*;
use crate::exec::scalar::*;
use crate::exec::domain::*;
use crate::exec::relational::schema::*;
use crate::exec::relational::rows::*;
use crate::bridge::order::*;

verus! {

pub open spec fn view_keys(keys: Seq<EOrderKey>) -> Seq<OrderKey> {
    view_order_keys(keys)
}

/// `spec::order::key_cmp`: a missing column compares as NULL; NULLs are first or last per `nulls_first`; other
/// values compare by `compare` (incomparable values tie), reversed for `desc`.
fn key_cmp_exec(k: &EOrderKey, r1: &ERow, r2: &ERow) -> (c: i8)
    ensures c as int == key_cmp(view_order_key(*k), view_row(r1@), view_row(r2@)),
{
    let ghost gk = view_order_key(*k);
    let ghost g1 = view_row(r1@);
    let ghost g2 = view_row(r2@);
    // The key column's value, `None` when it is NULL or past the end of the row.
    let a = if k.col < r1.len() && !matches!(r1[k.col], EVal::Null) { Some(&r1[k.col]) } else { None };
    let b = if k.col < r2.len() && !matches!(r2[k.col], EVal::Null) { Some(&r2[k.col]) } else { None };
    proof {
        if k.col < r1.len() { assert(g1[k.col as int] == r1@[k.col as int]@); }
        if k.col < r2.len() { assert(g2[k.col as int] == r2@[k.col as int]@); }
    }
    match (a, b) {
        (None, None) => 0,
        (None, Some(_)) => if k.nulls_first { -1 } else { 1 },
        (Some(_), None) => if k.nulls_first { 1 } else { -1 },
        (Some(a), Some(b)) => {
            let c: i8 = match compare_exec(a, b) {
                Some(c) => {
                    proof { lemma_compare_range(a@, b@); }
                    c
                },
                None => 0,
            };
            if k.desc { -c } else { c }
        },
    }
}

/// `spec::order::keys_cmp` (lexicographic over the keys).
pub fn keys_cmp_exec(keys: &Vec<EOrderKey>, r1: &ERow, r2: &ERow) -> (c: i8)
    ensures c as int == keys_cmp(view_keys(keys@), view_row(r1@), view_row(r2@)),
{
    let ghost gk = view_keys(keys@);
    let ghost g1 = view_row(r1@);
    let ghost g2 = view_row(r2@);
    let mut i: usize = 0;
    proof { assert(gk.subrange(0, gk.len() as int) =~= gk); }
    while i < keys.len()
        invariant
            i <= keys.len(), gk == view_keys(keys@), g1 == view_row(r1@), g2 == view_row(r2@),
            keys_cmp(gk, g1, g2) == keys_cmp(gk.subrange(i as int, gk.len() as int), g1, g2),
        decreases keys.len() - i,
    {
        let ghost rest = gk.subrange(i as int, gk.len() as int);
        proof {
            assert(rest[0] == view_order_key(keys@[i as int]));
            assert(rest.drop_first() =~= gk.subrange(i as int + 1, gk.len() as int));
        }
        let c = key_cmp_exec(&keys[i], r1, r2);
        if c != 0 {
            return c;
        }
        i = i + 1;
    }
    0
}

/// `spec::order::sort_rows` (stable insertion sort).
pub fn sort_rows_exec(keys: &Vec<EOrderKey>, rows: Vec<ERow>) -> (out: Vec<ERow>)
    ensures view_rows(out@) == sort_rows(view_keys(keys@), view_rows(rows@)),
{
    let ghost gk = view_keys(keys@);
    let ghost g = view_rows(rows@);
    let mut out: Vec<ERow> = Vec::new();
    let mut i: usize = 0;
    proof { assert(g.take(0) =~= Seq::<Row>::empty()); }
    while i < rows.len()
        invariant
            i <= rows.len(), gk == view_keys(keys@), g == view_rows(rows@),
            view_rows(out@) == sort_rows(gk, g.take(i as int)),
        decreases rows.len() - i,
    {
        proof {
            let t = g.take(i as int + 1);
            assert(t.drop_last() =~= g.take(i as int));
            assert(t.last() == g[i as int]);
            assert(g[i as int] == view_row(rows@[i as int]@));
        }
        let r = clone_row(&rows[i]);
        insert_sorted_exec(keys, &mut out, r);
        i = i + 1;
    }
    proof { assert(g.take(rows.len() as int) =~= g); }
    out
}

/// `spec::order::insert_sorted`: inserts `r` into sorted `s` after every row that is not greater (stable).
fn insert_sorted_exec(keys: &Vec<EOrderKey>, s: &mut Vec<ERow>, r: ERow)
    ensures view_rows(final(s)@) == insert_sorted(view_keys(keys@), view_rows(old(s)@), view_row(r@)),
{
    let ghost gk = view_keys(keys@);
    let ghost g = view_rows(s@);
    let ghost gr = view_row(r@);
    let mut pos = s.len();
    while pos > 0 && keys_cmp_exec(keys, &s[pos - 1], &r) > 0
        invariant
            pos <= s.len(), gk == view_keys(keys@), g == view_rows(s@), gr == view_row(r@),
            forall|k: int| pos <= k < g.len() ==> keys_cmp(gk, #[trigger] g[k], gr) > 0,
        decreases pos,
    {
        proof { assert(g[pos - 1] == view_row(s@[pos - 1]@)); }
        pos = pos - 1;
    }
    proof {
        if pos > 0 { assert(g[pos - 1] == view_row(s@[pos - 1]@)); }
        lemma_insert_sorted_at(gk, g, gr, pos as int);
    }
    s.insert(pos, r);
    proof {
        assert(view_rows(s@) =~= g.take(pos as int) + seq![gr] + g.skip(pos as int));
    }
}

/// `insert_sorted` places `r` at `pos` when `pos` is right after the last row that is not greater than `r`.
proof fn lemma_insert_sorted_at(keys: Seq<OrderKey>, s: Seq<Row>, r: Row, pos: int)
    requires
        0 <= pos <= s.len(),
        forall|k: int| pos <= k < s.len() ==> keys_cmp(keys, #[trigger] s[k], r) > 0,
        pos == 0 || keys_cmp(keys, s[pos - 1], r) <= 0,
    ensures
        insert_sorted(keys, s, r) == s.take(pos) + seq![r] + s.skip(pos),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s.take(pos) + seq![r] + s.skip(pos) =~= seq![r]);
    } else if pos == s.len() {
        assert(s.take(pos) + seq![r] + s.skip(pos) =~= s.push(r));
    } else {
        let d = s.drop_last();
        assert(keys_cmp(keys, s[s.len() - 1], r) > 0);
        assert forall|k: int| pos <= k < d.len() implies keys_cmp(keys, #[trigger] d[k], r) > 0 by {
            assert(d[k] == s[k]);
        }
        if pos > 0 { assert(d[pos - 1] == s[pos - 1]); }
        lemma_insert_sorted_at(keys, d, r, pos);
        assert((d.take(pos) + seq![r] + d.skip(pos)).push(s.last()) =~= s.take(pos) + seq![r] + s.skip(pos));
    }
}

/// OFFSET then LIMIT (`spec::order::slice_rows`).
pub fn slice_rows_exec(s: &Vec<ERow>, offset: u64, limit: Option<u64>) -> (out: Vec<ERow>)
    ensures
        view_rows(out@) == slice_rows(view_rows(s@), offset as nat, match limit { Some(n) => Some(n as nat), None => None }),
{
    let ghost g = view_rows(s@);
    let len = s.len();
    let lo: usize = if (offset as u128) <= (len as u128) { offset as usize } else { len };
    let hi: usize = match limit {
        Some(n) => if (lo as u128) + (n as u128) <= (len as u128) { lo + n as usize } else { len },
        None => len,
    };
    let mut out: Vec<ERow> = Vec::new();
    let mut i = lo;
    while i < hi
        invariant
            lo <= i <= hi, hi <= len, len == s.len(), g == view_rows(s@),
            view_rows(out@) == g.subrange(lo as int, i as int),
        decreases hi - i,
    {
        let ghost prev = view_rows(out@);
        let r = clone_row(&s[i]);
        out.push(r);
        proof {
            assert(view_rows(out@) =~= prev.push(g[i as int]));
            assert(g.subrange(lo as int, i as int + 1) =~= g.subrange(lo as int, i as int).push(g[i as int]));
        }
        i = i + 1;
    }
    out
}

// ------------------------------------------------------------------ the timestamp invariant is kept

pub proof fn lemma_insert_sorted_ts_ok(keys: Seq<OrderKey>, s: Seq<Row>, r: Row)
    requires rows_ts_ok(s), row_ts_ok(r),
    ensures rows_ts_ok(insert_sorted(keys, s, r)),
    decreases s.len(),
{
    if s.len() > 0 && keys_cmp(keys, s.last(), r) > 0 {
        let d = s.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies row_ts_ok(#[trigger] d[i]) by { assert(d[i] == s[i]); }
        lemma_insert_sorted_ts_ok(keys, d, r);
        assert(row_ts_ok(s[s.len() - 1]));
    }
}

pub proof fn lemma_sort_rows_ts_ok(keys: Seq<OrderKey>, s: Seq<Row>)
    requires rows_ts_ok(s),
    ensures rows_ts_ok(sort_rows(keys, s)),
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies row_ts_ok(#[trigger] d[i]) by { assert(d[i] == s[i]); }
        lemma_sort_rows_ts_ok(keys, d);
        assert(row_ts_ok(s[s.len() - 1]));
        lemma_insert_sorted_ts_ok(keys, sort_rows(keys, d), s.last());
    }
}

pub proof fn lemma_slice_ts_ok(s: Seq<Row>, offset: nat, limit: Option<nat>)
    requires rows_ts_ok(s),
    ensures rows_ts_ok(slice_rows(s, offset, limit)),
{
    let out = slice_rows(s, offset, limit);
    let lo = if offset <= s.len() { offset as int } else { s.len() as int };
    assert forall|i: int| 0 <= i < out.len() implies row_ts_ok(#[trigger] out[i]) by {
        assert(out[i] == s[lo + i]);
    }
}

} // verus!
