//! The rows of the index storages `li_pkship` (lineitem, composite index on l_partkey and ship key) and `part_bcs`
//! (part, composite index on brand, container and size) in index order, and their link to the statement's sums.
//!
//! - `lrows(lp)`: the lineitem rows `[l_partkey, l_quantity, l_extendedprice, l_discount, l_shipinstruct,
//!   l_shipmode]` at the index positions of li_pkship (`lrow(lp, q)` is the row of stored row `irow(q)`);
//! - `prows(pp)`: the part rows `[p_partkey, p_brand, p_size, p_container]` at the index positions of part_bcs.
//! Both indexes are bijections over a row map that is itself a bijection, so these are permutations of the
//! database's rows projected on the statement's columns (`lemma_ix_link`), the same multisets as the incumbent's
//! `model::li_rows` / `model::pa_rows`. Hence the statement's accumulators `terms::tot` over facts and custpart are
//! the sums `ix_tot` over the index orders (`lemma_ix_tot`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::link::expr::{ival, tval};
use crate::link::join::{sum_of, lemma_sum_of_perm};
use crate::link::query::{proj, proj_all};
use crate::link::source::lemma_proj_all_index;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stores::{StoresView, stored_ok};
use crate::stores::facts::interface::common::colfmt::{is_perm, stored_rows, lemma_stored_rows_multiset, covered};
use crate::stores::li_pkship::interface as lsi;
use crate::stores::li_pkship::declaration as lsd;
use crate::stores::part_bcs::interface as pbi;
use crate::stores::part_bcs::declaration as pbd;
use super::model::{p15, abs_lt, li_rows, pa_rows, n_pa};
use super::terms::*;
use super::bind::{lemma_rows_typed, rows_typed, lrow_typed, prow_typed, lcols, pcols, num2, int8v, textv, lemma_li_link,
    lemma_pa_link};

verus! {

// ------------------------------------------------------------------------------------------------ rows in index order

/// Number of lineitem rows of li_pkship.
pub open spec fn n_l(lp: Seq<PartView>) -> int {
    lsi::n_rows(lp)
}

/// Number of part rows of part_bcs.
pub open spec fn n_p(pp: Seq<PartView>) -> int {
    pbi::n_rows(pp)
}

/// The lineitem row at index position `q`.
pub open spec fn lrow(lp: Seq<PartView>, q: int) -> Row {
    lsi::row_at(lp, lsi::irow(lp, q))
}

/// The lineitem rows in index order.
pub open spec fn lrows(lp: Seq<PartView>) -> Seq<Row> {
    Seq::new(n_l(lp) as nat, |q: int| lrow(lp, q))
}

/// The part row at index position `p`.
pub open spec fn prow_val(pp: Seq<PartView>, p: int) -> Row {
    pbi::row_at(pp, pbi::prow(pp, p))
}

/// The part rows in index order.
pub open spec fn prows(pp: Seq<PartView>) -> Seq<Row> {
    Seq::new(n_p(pp) as nat, |p: int| prow_val(pp, p))
}

/// Per part row `z`: accumulator `k` over every lineitem row (in index order).
pub open spec fn pin_l(lp: Seq<PartView>, ps: Seq<Literal>, k: int) -> spec_fn(Row) -> int {
    |z: Row| sum_of(lrows(lp), jt(ps, k, z))
}

/// Accumulator `k` over the part index positions `p0 .. p1`.
pub open spec fn rsum(lp: Seq<PartView>, pp: Seq<PartView>, ps: Seq<Literal>, k: int, p0: int, p1: int) -> int {
    sum_of(prows(pp).subrange(p0, p1), pin_l(lp, ps, k))
}

// ------------------------------------------------------------------------------------------------ stored values

/// The values of stored lineitem row `s` lie in their columns' ranges.
pub open spec fn l_vals_ok(lp: Seq<PartView>, s: int) -> bool {
    &&& i64::MIN <= lsi::key_at(lp, s) <= i64::MAX
    &&& abs_lt(lsi::qty_at(lp, s), p15())
    &&& abs_lt(lsi::price_at(lp, s), p15())
    &&& abs_lt(lsi::disc_at(lp, s), p15())
}

/// The values of part row `r` lie in their columns' ranges.
pub open spec fn p_vals_ok(pp: Seq<PartView>, r: int) -> bool {
    &&& i64::MIN <= pbi::pkey_at(pp, r) <= i64::MAX
    &&& i64::MIN <= pbi::size_at(pp, r) <= i64::MAX
}

/// What the index plan uses about li_pkship's parts.
pub open spec fn lp_ok(lp: Seq<PartView>) -> bool {
    let n = n_l(lp);
    &&& lsi::li_shape(lp, n)
    &&& lsi::idx_ok(lp, n)
    &&& forall|s: int| 0 <= s < n ==> #[trigger] lsi::dict_idx_ok(lp, s)
    &&& forall|s: int| 0 <= s < n ==> #[trigger] l_vals_ok(lp, s)
}

/// What the index plan uses about part_bcs's parts.
pub open spec fn pp_ok(pp: Seq<PartView>) -> bool {
    let n = n_p(pp);
    &&& pbi::pa_shape(pp, n)
    &&& pbi::idx_ok(pp, n)
    &&& forall|r: int| 0 <= r < n ==> #[trigger] pbi::dict_idx_ok(pp, r)
    &&& forall|r: int| 0 <= r < n ==> #[trigger] p_vals_ok(pp, r)
}

// ------------------------------------------------------------------------------------------------ links

/// li_pkship of a bound database: its facts, and (with the index) its rows in index order are a permutation of the
/// lineitem rows projected on `lcols()`.
pub proof fn lemma_l_link(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        lp_ok(sv.li_pkship),
        n_l(sv.li_pkship) == db.tables[0].len(),
        lsi::has_idx(sv.li_pkship) ==> lrows(sv.li_pkship).to_multiset() == proj_all(db.tables[0], lcols()).to_multiset(),
{
    let lp = sv.li_pkship;
    let rels = lsd::stored_relations(db);
    assert(stored_ok(sv, db));
    assert(lsi::represents(lp, rels));
    lemma_rows_typed(db);
    lsd::lemma_stored_relations(db);
    let t0 = db.tables[0];
    let rel = rels[0];
    assert(lsd::stored_cols_t0() =~= lcols());
    lemma_proj_all_index(t0, lcols());
    let n = rel.len() as int;
    assert(n == t0.len());
    assert forall|s: int| 0 <= s < n implies #[trigger] l_vals_ok(lp, s) by {
        let r = lsi::map_at(lp, s);
        assert(0 <= r < n);
        assert(rel[r] == lsi::row_at(lp, s));
        assert(lrow_typed(t0[r]));
        assert(rel[r][0] == t0[r][1]);
        assert(rel[r][1] == t0[r][4]);
        assert(rel[r][2] == t0[r][5]);
        assert(rel[r][3] == t0[r][6]);
        assert(int8v(t0[r][1]) && num2(t0[r][4]) && num2(t0[r][5]) && num2(t0[r][6]));
    }
    assert(forall|s: int| 0 <= s < n ==> #[trigger] lsi::dict_idx_ok(lp, s));
    if lsi::has_idx(lp) {
        let rmap = Seq::new(n as nat, |q: int| lsi::map_at(lp, lsi::irow(lp, q)));
        assert forall|q: int| 0 <= q < n implies 0 <= #[trigger] rmap[q] < n by {
            assert(0 <= lsi::irow(lp, q) < n);
        }
        assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b implies #[trigger] rmap[a] != #[trigger] rmap[b] by {
            assert(lsi::irow(lp, a) != lsi::irow(lp, b));
            assert(0 <= lsi::irow(lp, a) < n && 0 <= lsi::irow(lp, b) < n);
        }
        assert forall|i: int| 0 <= i < n implies #[trigger] covered(rmap, i) by {
            assert(lsi::mapped(lp, n, i));
            let s = choose|s: int| 0 <= s < n && #[trigger] lsi::map_at(lp, s) == i;
            assert(lsi::indexed(lp, n, s));
            let q = choose|q: int| 0 <= q < n && #[trigger] lsi::irow(lp, q) == s;
            assert(rmap[q] == i);
        }
        assert(is_perm(rmap, n));
        assert forall|q: int| 0 <= q < n implies #[trigger] lrows(lp)[q] == stored_rows(rel, rmap)[q] by {
            assert(0 <= lsi::irow(lp, q) < n);
            assert(rel[lsi::map_at(lp, lsi::irow(lp, q))] == lsi::row_at(lp, lsi::irow(lp, q)));
        }
        assert(lrows(lp) =~= stored_rows(rel, rmap));
        lemma_stored_rows_multiset(rel, rmap);
    }
}

/// part_bcs of a bound database: its facts, and (with the index) its rows in index order are a permutation of the
/// part rows projected on `pcols()`.
pub proof fn lemma_p_link(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        pp_ok(sv.part_bcs),
        n_p(sv.part_bcs) == db.tables[3].len(),
        pbi::has_idx(sv.part_bcs) ==> prows(sv.part_bcs).to_multiset() == proj_all(db.tables[3], pcols()).to_multiset(),
{
    let pp = sv.part_bcs;
    let rels = pbd::stored_relations(db);
    assert(stored_ok(sv, db));
    assert(pbi::represents(pp, rels));
    lemma_rows_typed(db);
    pbd::lemma_stored_relations(db);
    let t3 = db.tables[3];
    let rel = rels[0];
    assert(pbd::stored_cols_t0() =~= pcols());
    lemma_proj_all_index(t3, pcols());
    let n = rel.len() as int;
    assert(n == t3.len());
    assert forall|r: int| 0 <= r < n implies #[trigger] p_vals_ok(pp, r) by {
        assert(rel[r] == pbi::row_at(pp, r));
        assert(prow_typed(t3[r]));
        assert(rel[r][0] == t3[r][0]);
        assert(rel[r][2] == t3[r][5]);
        assert(int8v(t3[r][0]) && int8v(t3[r][5]));
    }
    assert(forall|r: int| 0 <= r < n ==> #[trigger] pbi::dict_idx_ok(pp, r));
    if pbi::has_idx(pp) {
        let pmap = Seq::new(n as nat, |p: int| pbi::prow(pp, p));
        assert forall|i: int| 0 <= i < n implies #[trigger] covered(pmap, i) by {
            assert(pbi::listed(pp, n, i));
            let p = choose|p: int| 0 <= p < n && #[trigger] pbi::prow(pp, p) == i;
            assert(pmap[p] == i);
        }
        assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b implies #[trigger] pmap[a] != #[trigger] pmap[b] by {
            assert(pbi::prow(pp, a) != pbi::prow(pp, b));
        }
        assert(is_perm(pmap, n));
        assert forall|p: int| 0 <= p < n implies #[trigger] prows(pp)[p] == stored_rows(rel, pmap)[p] by {
            assert(0 <= pbi::prow(pp, p) < n);
            assert(rel[pbi::prow(pp, p)] == pbi::row_at(pp, pbi::prow(pp, p)));
        }
        assert(prows(pp) =~= stored_rows(rel, pmap));
        lemma_stored_rows_multiset(rel, pmap);
    }
}

/// With both indexes present, the statement's accumulator `k` over facts and custpart is the sum over the part
/// index positions of the per-part sums over the lineitem index positions.
pub proof fn lemma_ix_tot(sv: StoresView, db: Database, ps: Seq<Literal>, k: int)
    requires
        bound_db(sv, db),
        lsi::has_idx(sv.li_pkship),
        pbi::has_idx(sv.part_bcs),
    ensures
        n_p(sv.part_bcs) == n_pa(sv.custpart),
        tot(sv.facts, sv.custpart, ps, k, 0, n_pa(sv.custpart)) == rsum(sv.li_pkship, sv.part_bcs, ps, k, 0, n_p(sv.part_bcs)),
{
    let (fp, cp, lp, pp) = (sv.facts, sv.custpart, sv.li_pkship, sv.part_bcs);
    lemma_li_link(sv, db);
    lemma_pa_link(sv, db);
    lemma_l_link(sv, db);
    lemma_p_link(sv, db);
    assert(lrows(lp).to_multiset() == li_rows(fp).to_multiset());
    assert forall|z: Row| #[trigger] pin(fp, ps, k)(z) == pin_l(lp, ps, k)(z) by {
        lemma_sum_of_perm(li_rows(fp), lrows(lp), jt(ps, k, z));
    }
    assert(pin(fp, ps, k) =~= pin_l(lp, ps, k));
    let n = n_pa(cp);
    assert(pa_rows(cp).len() == n);
    assert(pa_rows(cp).subrange(0, n) =~= pa_rows(cp));
    assert(prows(pp).subrange(0, n_p(pp)) =~= prows(pp));
    lemma_sum_of_perm(pa_rows(cp), prows(pp), pin_l(lp, ps, k));
}

} // verus!
