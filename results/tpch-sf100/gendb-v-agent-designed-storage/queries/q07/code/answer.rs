//! The normal form's accumulators from the scan's group sums: for every key `k`, `gcount`, `gsum` and `gabs` of
//! `g7` over `shipping` are the sums of the scan's per-group count, sum and mass over the groups whose key row is
//! `k` (`lemma_group_sums`). The sum over `shipping` reduces to lineitem (`body::lemma_ship_sum`), lineitem's
//! table rows are the stored lines in another order (the row map is a bijection), and each stored line's term is
//! the model's (`line::lemma_line`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::numeric::abs;
use crate::link::join::*;
use crate::link::query::*;
use crate::stores::facts::interface::common::colfmt::{stored_rows, lemma_stored_rows_multiset, is_perm};
use super::sqlq::*;
use super::reduce::*;
use super::body::*;
use super::model::*;
use super::bind::*;
use super::line::*;

verus! {

/// Sum of the line terms of the stored lines `[0, k)`.
pub open spec fn jsum(c: Cols, x: Ctx, ps: Seq<Literal>, phi: spec_fn(Row) -> int, k: int) -> int
    decreases k,
{
    if k <= 0 { 0 } else { jsum(c, x, ps, phi, k - 1) + line_term(c, x, ps, phi, k - 1) }
}

/// The stored lines in storage order, as table rows.
pub open spec fn srows(db: Database, lm: Seq<int>) -> Seq<Row> {
    stored_rows(t_li(db), lm)
}

proof fn lemma_prefix_sum(db: Database, c: Cols, x: Ctx, ps: Seq<Literal>, phi: spec_fn(Row) -> int, lm: Seq<int>,
    om: Seq<int>, k: int)
    requires chain_ok(db, c, x, ps, lm, om), 0 <= k <= c.n_l,
    ensures sum_of(srows(db, lm).take(k), h1(db, ps, phi)) == jsum(c, x, ps, phi, k),
    decreases k,
{
    let s = srows(db, lm);
    if k > 0 {
        lemma_prefix_sum(db, c, x, ps, phi, lm, om, k - 1);
        assert(s.take(k).drop_last() =~= s.take(k - 1));
        assert(s.take(k).last() == s[k - 1]);
        assert(s[k - 1] == t_li(db)[lm[k - 1]]);
        lemma_line(db, c, x, ps, phi, lm, om, k - 1);
    } else {
        assert(s.take(0) =~= Seq::<Row>::empty());
    }
}

/// The sum of the reduction's term over lineitem is the sum of the stored lines' terms.
pub proof fn lemma_table_sum(db: Database, c: Cols, x: Ctx, ps: Seq<Literal>, phi: spec_fn(Row) -> int, lm: Seq<int>,
    om: Seq<int>)
    requires chain_ok(db, c, x, ps, lm, om),
    ensures sum_of(t_li(db), h1(db, ps, phi)) == jsum(c, x, ps, phi, c.n_l as int),
{
    let s = srows(db, lm);
    assert(is_perm(lm, t_li(db).len() as int));
    lemma_stored_rows_multiset(t_li(db), lm);
    lemma_sum_of_perm(s, t_li(db), h1(db, ps, phi));
    lemma_prefix_sum(db, c, x, ps, phi, lm, om, c.n_l as int);
    assert(s.take(c.n_l as int) =~= s);
}

// ------------------------------------------------------------------------------------------------ per key

/// A line's group is one of the four, or none.
pub proof fn lemma_grp_range(c: Cols, x: Ctx, j: int)
    ensures -1 <= l_grp(c, x, j) <= 3,
{
}

/// Count, sum and mass of the groups whose key row is `k`.
pub open spec fn kcnt(c: Cols, x: Ctx, ps: Seq<Literal>, k: Row, b: int) -> int {
    (if krow(ps, 0) == k { rcnt(c, x, 0, 0, b) } else { 0 }) + (if krow(ps, 1) == k { rcnt(c, x, 1, 0, b) } else { 0 })
        + (if krow(ps, 2) == k { rcnt(c, x, 2, 0, b) } else { 0 }) + (if krow(ps, 3) == k { rcnt(c, x, 3, 0, b) } else { 0 })
}

pub open spec fn ksum(c: Cols, x: Ctx, ps: Seq<Literal>, k: Row, b: int) -> int {
    (if krow(ps, 0) == k { rsum(c, x, 0, 0, b) } else { 0 }) + (if krow(ps, 1) == k { rsum(c, x, 1, 0, b) } else { 0 })
        + (if krow(ps, 2) == k { rsum(c, x, 2, 0, b) } else { 0 }) + (if krow(ps, 3) == k { rsum(c, x, 3, 0, b) } else { 0 })
}

pub open spec fn kmass(c: Cols, x: Ctx, ps: Seq<Literal>, k: Row, b: int) -> int {
    (if krow(ps, 0) == k { rmass(c, x, 0, 0, b) } else { 0 }) + (if krow(ps, 1) == k { rmass(c, x, 1, 0, b) } else { 0 })
        + (if krow(ps, 2) == k { rmass(c, x, 2, 0, b) } else { 0 }) + (if krow(ps, 3) == k { rmass(c, x, 3, 0, b) } else { 0 })
}

/// The key of a line's SELECT list is its group's key row.
proof fn lemma_lrow_key(ps: Seq<Literal>, gi: int, v: int)
    ensures
        (g7().key)(lrow7(ps, gi, v)) == krow(ps, gi),
        (g7().arg)(0, lrow7(ps, gi, v)) == v,
        (g7().qual)(lrow7(ps, gi, v)),
{
    let r = lrow7(ps, gi, v);
    assert(seq![r[0], r[1], r[2]] =~= krow(ps, gi));
}

proof fn lemma_kcnt(c: Cols, x: Ctx, ps: Seq<Literal>, k: Row, b: int)
    requires b >= 0,
    ensures
        jsum(c, x, ps, count_term(g7(), k), b) == kcnt(c, x, ps, k, b),
        jsum(c, x, ps, sum_term(g7(), k, 0), b) == ksum(c, x, ps, k, b),
        jsum(c, x, ps, abs_term(g7(), k, 0), b) == kmass(c, x, ps, k, b),
    decreases b,
{
    if b > 0 {
        lemma_kcnt(c, x, ps, k, b - 1);
        lemma_grp_range(c, x, b - 1);
        let gl = l_grp(c, x, b - 1);
        let v = l_vol(c, b - 1);
        lemma_r_step(c, x, 0, 0, b - 1);
        lemma_r_step(c, x, 1, 0, b - 1);
        lemma_r_step(c, x, 2, 0, b - 1);
        lemma_r_step(c, x, 3, 0, b - 1);
        if gl >= 0 {
            lemma_lrow_key(ps, gl, v);
            assert(abs(v) == iabs(v));
        }
    }
}

/// The normal form's accumulators over `shipping` are the scan's group sums.
pub proof fn lemma_group_sums(db: Database, c: Cols, x: Ctx, ps: Seq<Literal>, lm: Seq<int>, om: Seq<int>, k: Row)
    requires chain_ok(db, c, x, ps, lm, om),
    ensures
        gcount(g7(), ship(db, ps), k) == kcnt(c, x, ps, k, c.n_l as int),
        gsum(g7(), ship(db, ps), k, 0) == ksum(c, x, ps, k, c.n_l as int),
        gabs(g7(), ship(db, ps), k, 0) == kmass(c, x, ps, k, c.n_l as int),
{
    let sh = ship(db, ps);
    lemma_acc_sum_of(g7(), sh, k, 0);
    lemma_ship_sum(db, ps, count_term(g7(), k));
    lemma_ship_sum(db, ps, sum_term(g7(), k, 0));
    lemma_ship_sum(db, ps, abs_term(g7(), k, 0));
    lemma_table_sum(db, c, x, ps, count_term(g7(), k), lm, om);
    lemma_table_sum(db, c, x, ps, sum_term(g7(), k, 0), lm, om);
    lemma_table_sum(db, c, x, ps, abs_term(g7(), k, 0), lm, om);
    lemma_kcnt(c, x, ps, k, c.n_l as int);
}

} // verus!
