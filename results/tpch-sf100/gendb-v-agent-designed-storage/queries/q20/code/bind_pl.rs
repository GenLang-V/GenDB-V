//! Storages `part_nameidx` and `li_pkdate` at the level of their parts.
//! - part: `pp_ok` (shape, name order, bigint keys) and `pa_bound` (the part rows' `p_partkey`, `p_name`);
//! - lineitem: `lp_ok` (shape, row map, index, value bounds); the stored rows as 4-value rows `wrows`
//!   (`[l_partkey, l_suppkey, l_quantity, l_shipdate]` of stored row `s`); `sl_lsum`/`sl_lcnt`, the SUM and COUNT of
//!   the statement's lineitem subquery over them; `lemma_bind_lp`: they are `nf::lsum`/`nf::lcnt` of every database
//!   the parts represent (the row map is a bijection, so the stored rows are a permutation of the relation);
//!   `lemma_pos_sum`: the same sums over the index positions (`irow` is a bijection too).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::datetime::date_valid;
use crate::gendb_entry::layout::PartView;
use crate::link::query::{proj, proj_all};
use crate::link::source::lemma_proj_all_index;
use crate::link::join::*;
use crate::link::expr::{ival, tval};
use crate::stores::part_nameidx::interface as pi;
use crate::stores::part_nameidx::declaration as pd;
use crate::stores::li_pkdate::interface as li;
use crate::stores::li_pkdate::declaration as ld;
use crate::stores::suppliers::interface::common::colfmt as cf;
use super::typed::*;
use super::nf::*;
use super::bind_sp::i64r;

verus! {

// ------------------------------------------------------------------------------------------------ part

pub open spec fn pp_ok(pp: Seq<PartView>) -> bool {
    &&& pi::pa_shape(pp, pi::n_rows(pp))
    &&& pi::perm_ok(pp, pi::n_rows(pp))
    &&& forall|r: int| 0 <= r < pi::n_rows(pp) ==> i64r(#[trigger] pi::pkey_at(pp, r))
}

/// The part rows of `db` hold the parts' values.
pub open spec fn pa_bound(pp: Seq<PartView>, db: Database) -> bool {
    &&& pt(db).len() == pi::n_rows(pp)
    &&& forall|r: int| 0 <= r < pt(db).len() ==> #[trigger] pt(db)[r][0] == Val::Int(pi::pkey_at(pp, r))
        && pt(db)[r][1] == Val::Text(pi::name_at(pp, r))
}

pub proof fn lemma_bind_pp(pp: Seq<PartView>, db: Database)
    requires pi::represents(pp, pd::stored_relations(db)), tables_ok(db),
    ensures pp_ok(pp), pa_bound(pp, db),
{
    let rel = pd::stored_relations(db)[0];
    let cols = pd::stored_cols_t0();
    assert(rel == proj_all(pt(db), cols));
    lemma_proj_all_index(pt(db), cols);
    assert forall|r: int| 0 <= r < pt(db).len() implies #[trigger] pt(db)[r][0] == Val::Int(pi::pkey_at(pp, r))
        && pt(db)[r][1] == Val::Text(pi::name_at(pp, r)) by {
        assert(rel[r] == pi::pa_row(pi::pkey_at(pp, r), pi::name_at(pp, r)));
        assert(rel[r][0] == pt(db)[r][cols[0] as int]);
        assert(rel[r][1] == pt(db)[r][cols[1] as int]);
    }
    assert forall|r: int| 0 <= r < pi::n_rows(pp) implies i64r(#[trigger] pi::pkey_at(pp, r)) by {
        assert(prow_ok(pt(db)[r]));
        assert(pt(db)[r][0] == Val::Int(pi::pkey_at(pp, r)));
    }
}

// ------------------------------------------------------------------------------------------------ lineitem

/// Values of stored row `s` within the declared domain.
pub open spec fn lrow_vals_ok(lp: Seq<PartView>, s: int) -> bool {
    &&& i64r(li::key_at(lp, s))
    &&& i64r(li::supp_at(lp, s))
    &&& -p15() < li::qty_at(lp, s) < p15()
    &&& date_valid(li::date_at(lp, s))
}

pub open spec fn lp_ok(lp: Seq<PartView>) -> bool {
    &&& li::li_shape(lp, li::n_rows(lp))
    &&& li::row_map_ok(lp, li::n_rows(lp))
    &&& li::idx_ok(lp, li::n_rows(lp))
    &&& forall|s: int| 0 <= s < li::n_rows(lp) ==> #[trigger] lrow_vals_ok(lp, s)
}

/// Stored row `s` as `[l_partkey, l_suppkey, l_quantity, l_shipdate]`.
pub open spec fn wrow(lp: Seq<PartView>, s: int) -> Row {
    li::li_row(li::key_at(lp, s), li::supp_at(lp, s), li::qty_at(lp, s), li::date_at(lp, s))
}

/// The stored rows.
pub open spec fn wrows(lp: Seq<PartView>) -> Seq<Row> {
    Seq::new(li::n_rows(lp) as nat, |s: int| wrow(lp, s))
}

/// A 4-value row of part `k`, supplier `su`, shipped in `[d0, d1)`.
pub open spec fn wsel(k: int, su: int, d0: int, d1: int, r: Row) -> bool {
    r[0] == Val::Int(k) && r[1] == Val::Int(su) && d0 <= ival(r[3]) && ival(r[3]) < d1
}

pub open spec fn lq4(k: int, su: int, d0: int, d1: int) -> spec_fn(Row) -> int {
    |r: Row| if wsel(k, su, d0, d1, r) { ival(r[2]) } else { 0int }
}

pub open spec fn lc4(k: int, su: int, d0: int, d1: int) -> spec_fn(Row) -> int {
    |r: Row| if wsel(k, su, d0, d1, r) { 1int } else { 0int }
}

/// SUM(l_quantity) coefficient of the stored rows of part `k`, supplier `su` in the window.
pub open spec fn sl_lsum(lp: Seq<PartView>, k: int, su: int, d0: int, d1: int) -> int {
    sum_of(wrows(lp), lq4(k, su, d0, d1))
}

/// Their number.
pub open spec fn sl_lcnt(lp: Seq<PartView>, k: int, su: int, d0: int, d1: int) -> int {
    sum_of(wrows(lp), lc4(k, su, d0, d1))
}

/// The lineitem rows of `db` and the parts' sums.
pub open spec fn li_bound(lp: Seq<PartView>, db: Database) -> bool {
    &&& lt(db).len() == li::n_rows(lp)
    &&& forall|k: int, su: int, d0: int, d1: int| #[trigger] lsum(db, k, su, d0, d1) == sl_lsum(lp, k, su, d0, d1)
        && lcnt(db, k, su, d0, d1) == sl_lcnt(lp, k, su, d0, d1)
}

/// The row map as a sequence.
pub open spec fn mseq(lp: Seq<PartView>) -> Seq<int> {
    Seq::new(li::n_rows(lp) as nat, |s: int| li::map_at(lp, s))
}

/// The stored rows are a permutation of the projected relation.
proof fn lemma_wrows_perm(lp: Seq<PartView>, rel: Seq<Row>)
    requires
        li::represents(lp, seq![rel]),
    ensures
        wrows(lp).to_multiset() == rel.to_multiset(),
{
    let n = li::n_rows(lp);
    let m = mseq(lp);
    assert(rel.len() == n);
    assert(seq![rel][0] == rel);
    assert forall|i: int| 0 <= i < n implies #[trigger] cf::covered(m, i) by {
        assert(li::mapped(lp, n, i));
        let s = choose|s: int| 0 <= s < n && #[trigger] li::map_at(lp, s) == i;
        assert(m[s] == i);
    }
    assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b implies #[trigger] m[a] != #[trigger] m[b] by {
        assert(li::map_at(lp, a) != li::map_at(lp, b));
    }
    assert(cf::is_perm(m, n));
    cf::lemma_stored_rows_multiset(rel, m);
    let sr = cf::stored_rows(rel, m);
    assert forall|s: int| 0 <= s < n implies #[trigger] sr[s] == wrows(lp)[s] by {
        assert(rel[li::map_at(lp, s)] == wrow(lp, s));
    }
    assert(sr =~= wrows(lp));
}

/// The lineitem SUM and COUNT over `db` are the parts' sums.
proof fn lemma_li_sums(lp: Seq<PartView>, db: Database, k: int, su: int, d0: int, d1: int)
    requires li::represents(lp, ld::stored_relations(db)), tables_ok(db),
    ensures
        lsum(db, k, su, d0, d1) == sl_lsum(lp, k, su, d0, d1),
        lcnt(db, k, su, d0, d1) == sl_lcnt(lp, k, su, d0, d1),
{
    let l = lt(db);
    let cols = ld::stored_cols_t0();
    let rel = proj_all(l, cols);
    assert(ld::stored_relations(db) == seq![rel]);
    lemma_proj_all_index(l, cols);
    lemma_wrows_perm(lp, rel);
    let pm = |r: Row| proj(r, cols);
    assert(rel =~= l.map_values(pm));
    lemma_sum_of_map(l, pm, lq4(k, su, d0, d1));
    lemma_sum_of_map(l, pm, lc4(k, su, d0, d1));
    assert forall|i: int| 0 <= i < l.len() implies
        (|r: Row| lq4(k, su, d0, d1)(pm(r)))(#[trigger] l[i]) == lq_term(k, su, d0, d1)(l[i])
        && (|r: Row| lc4(k, su, d0, d1)(pm(r)))(l[i]) == lc_term(k, su, d0, d1)(l[i]) by {
        let p = pm(l[i]);
        assert(p[0] == l[i][1] && p[1] == l[i][2] && p[2] == l[i][4] && p[3] == l[i][10]);
    }
    lemma_sum_of_ext(l, |r: Row| lq4(k, su, d0, d1)(pm(r)), lq_term(k, su, d0, d1));
    lemma_sum_of_ext(l, |r: Row| lc4(k, su, d0, d1)(pm(r)), lc_term(k, su, d0, d1));
    lemma_sum_of_perm(wrows(lp), rel, lq4(k, su, d0, d1));
    lemma_sum_of_perm(wrows(lp), rel, lc4(k, su, d0, d1));
}

pub proof fn lemma_bind_lp(lp: Seq<PartView>, db: Database)
    requires li::represents(lp, ld::stored_relations(db)), tables_ok(db),
    ensures lp_ok(lp), li_bound(lp, db),
{
    let l = lt(db);
    let n = li::n_rows(lp);
    let cols = ld::stored_cols_t0();
    let rel = proj_all(l, cols);
    assert(ld::stored_relations(db)[0] == rel);
    lemma_proj_all_index(l, cols);
    assert forall|s: int| 0 <= s < n implies #[trigger] lrow_vals_ok(lp, s) by {
        let r = li::map_at(lp, s);
        assert(0 <= r < n);
        assert(rel[r] == wrow(lp, s));
        assert(lrow_ok(l[r]));
        assert(rel[r][0] == l[r][1] && rel[r][1] == l[r][2] && rel[r][2] == l[r][4] && rel[r][3] == l[r][10]);
    }
    assert forall|k: int, su: int, d0: int, d1: int| #[trigger] lsum(db, k, su, d0, d1) == sl_lsum(lp, k, su, d0, d1)
        && lcnt(db, k, su, d0, d1) == sl_lcnt(lp, k, su, d0, d1) by {
        lemma_li_sums(lp, db, k, su, d0, d1);
    }
}

/// The index positions' stored rows as a sequence.
pub open spec fn iseq(lp: Seq<PartView>) -> Seq<int> {
    Seq::new(li::n_rows(lp) as nat, |p: int| li::irow(lp, p))
}

/// Row at index position `p`.
pub open spec fn prows(lp: Seq<PartView>) -> Seq<Row> {
    Seq::new(li::n_rows(lp) as nat, |p: int| wrow(lp, li::irow(lp, p)))
}

/// Sums over the stored rows are sums over the index positions.
pub proof fn lemma_pos_sum(lp: Seq<PartView>, f: spec_fn(Row) -> int)
    requires lp_ok(lp), li::has_idx(lp),
    ensures sum_of(wrows(lp), f) == sum_of(prows(lp), f),
{
    let n = li::n_rows(lp);
    let m = iseq(lp);
    assert forall|i: int| 0 <= i < n implies #[trigger] cf::covered(m, i) by {
        assert(li::indexed(lp, n, i));
        let p = choose|p: int| 0 <= p < n && #[trigger] li::irow(lp, p) == i;
        assert(m[p] == i);
    }
    assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b implies #[trigger] m[a] != #[trigger] m[b] by {
        assert(li::irow(lp, a) != li::irow(lp, b));
    }
    assert forall|p: int| 0 <= p < n implies 0 <= #[trigger] m[p] < n by {
        assert(0 <= li::irow(lp, p) < n);
    }
    assert(cf::is_perm(m, n));
    cf::lemma_stored_rows_multiset(wrows(lp), m);
    let sr = cf::stored_rows(wrows(lp), m);
    assert forall|p: int| 0 <= p < n implies #[trigger] sr[p] == prows(lp)[p] by {
        assert(0 <= li::irow(lp, p) < n);
    }
    assert(sr =~= prows(lp));
    lemma_sum_of_perm(prows(lp), wrows(lp), f);
}

} // verus!
