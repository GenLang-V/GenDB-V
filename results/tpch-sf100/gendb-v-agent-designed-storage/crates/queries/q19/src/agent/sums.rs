//! Per part row, the accumulators over the stored lineitem rows in key index order.
//!
//! The key index lists every stored row once (kind 2: a bijection; kinds 0 and 1: the identity), so a sum over the
//! rows in index order is the sum over the stored rows (`lemma_irows_sum`, hence `pin == kin` over all positions,
//! `lemma_pin_kin`). The term of one index position is the contribution of its stored row's values to the part's
//! arm (`lemma_pos_term`); positions whose key differs from the part's contribute nothing.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::link::expr::{ival, tval};
use crate::link::join::{sum_of, lemma_sum_of_perm, lemma_sum_of_zero};
use crate::gendb_entry::layout::PartView;
use crate::stores::facts::interface::common::colfmt::*;
use crate::stores::facts::interface::common::keyidx::{fidx, idx_map};
use super::model::*;
use super::terms::*;
use super::decode::*;

verus! {

/// The stored rows in key index order have the same sums as in stored order.
pub proof fn lemma_irows_sum(fp: Seq<PartView>, f: spec_fn(Row) -> int)
    requires li_shape(fp),
    ensures sum_of(irows(fp), f) == sum_of(li_rows(fp), f),
{
    let n = n_li(fp);
    let rows = li_rows(fp);
    if kx_kind(fp) == 2 {
        let m = idx_map(kx_c(fp), kx_b(fp), li_bs(fp), n);
        assert(is_perm(m, n));
        assert forall|p: int| 0 <= p < n implies #[trigger] irows(fp)[p] == stored_rows(rows, m)[p] by {
            lemma_ikey(fp, p);
            assert(m[p] == fidx(kx_c(fp), kx_b(fp), li_bs(fp), p));
        }
        assert(irows(fp) =~= stored_rows(rows, m));
        lemma_stored_rows_multiset(rows, m);
        lemma_sum_of_perm(irows(fp), rows, f);
    } else {
        assert forall|p: int| 0 <= p < n implies #[trigger] irows(fp)[p] == rows[p] by {
            lemma_ikey(fp, p);
        }
        assert(irows(fp) =~= rows);
    }
}

/// Per part row: the accumulator over every stored lineitem row is the one over every index position.
pub proof fn lemma_pin_kin(fp: Seq<PartView>, ps: Seq<Literal>, k: int, z: Row)
    requires li_shape(fp),
    ensures pin(fp, ps, k)(z) == kin(fp, ps, k, z, 0, n_li(fp)),
{
    lemma_irows_sum(fp, jt(ps, k, z));
    assert(irows(fp).subrange(0, n_li(fp)) =~= irows(fp));
}

/// The term of index position `p` for part row `z`: the contribution of its stored row `s`, qualifying when the
/// part has an arm, the keys are equal and the arm's lineitem side holds.
pub proof fn lemma_pos_term(fp: Seq<PartView>, ps: Seq<Literal>, k: int, z: Row, p: int)
    requires li_shape(fp), 0 <= p < n_li(fp), z.len() == 4,
    ensures ({
        let s = irow_at(fp, p);
        let a = zarm(ps, z);
        &&& jt(ps, k, z)(irows(fp)[p]) == contrib(k,
                a < 3 && ival(z[0]) == ikey_at(fp, p)
                    && li_arm(ps, a, qty_at(fp, s), sdict(fp, sidx_at(fp, s)), mdict(fp, midx_at(fp, s))),
                price_at(fp, s) * (100 - disc_at(fp, s)))
        &&& 0 <= s < n_li(fp)
    }),
{
    let s = irow_at(fp, p);
    lemma_ikey(fp, p);
    let y = li_row(fp, s);
    assert(irows(fp)[p] == y);
    lemma_wq_arm(ps, y, z);
    lemma_joined(y, z);
}

/// A part row without an arm keeps no lineitem row.
pub proof fn lemma_pin_none(fp: Seq<PartView>, ps: Seq<Literal>, k: int, z: Row)
    requires z.len() == 4, zarm(ps, z) == 3,
    ensures pin(fp, ps, k)(z) == 0,
{
    let rows = li_rows(fp);
    assert forall|i: int| 0 <= i < rows.len() implies jt(ps, k, z)(#[trigger] rows[i]) == 0 by {
        lemma_wq_arm(ps, rows[i], z);
    }
    lemma_sum_of_zero(rows, jt(ps, k, z));
}

/// The terms of every position are bounded like the contributions; the mass terms are nonnegative.
pub proof fn lemma_kin_bounds(fp: Seq<PartView>, ps: Seq<Literal>, z: Row, a: int, b: int)
    requires 0 <= a <= b <= n_li(fp),
    ensures
        -kin(fp, ps, 2, z, a, b) <= kin(fp, ps, 1, z, a, b) <= kin(fp, ps, 2, z, a, b),
        kin(fp, ps, 0, z, a, b) >= 0,
        kin(fp, ps, 0, z, a, b) == 0 ==> kin(fp, ps, 2, z, a, b) == 0,
{
    let rows = irows(fp);
    assert forall|i: int| a <= i < b implies
        -jt(ps, 2, z)(#[trigger] rows[i]) <= jt(ps, 1, z)(rows[i]) <= jt(ps, 2, z)(rows[i])
        && 0 <= jt(ps, 0, z)(rows[i])
        && (jt(ps, 0, z)(rows[i]) == 0 ==> jt(ps, 2, z)(rows[i]) == 0) by {
        lemma_term_bounds(ps, rows[i] + z);
    }
    lemma_sum_within(rows, jt(ps, 1, z), jt(ps, 2, z), jt(ps, 0, z), a, b);
}

/// Mass terms are nonnegative, so a subrange's mass is at most the whole range's.
pub proof fn lemma_kin_mass_le(fp: Seq<PartView>, ps: Seq<Literal>, z: Row, a: int, b: int, c: int, d: int)
    requires 0 <= a <= b <= c <= d <= n_li(fp),
    ensures 0 <= kin(fp, ps, 2, z, b, c) <= kin(fp, ps, 2, z, a, d),
{
    let rows = irows(fp);
    assert forall|i: int| a <= i < d implies jt(ps, 2, z)(#[trigger] rows[i]) >= 0 by {
        lemma_term_bounds(ps, rows[i] + z);
    }
    lemma_sum_sub_le(rows, jt(ps, 2, z), a, b, c, d);
}

/// Per part row: `|pin sum| <= pin mass`, count and mass nonnegative.
pub proof fn lemma_pin_bounds(fp: Seq<PartView>, ps: Seq<Literal>, z: Row)
    ensures
        -pin(fp, ps, 2)(z) <= pin(fp, ps, 1)(z) <= pin(fp, ps, 2)(z),
        pin(fp, ps, 0)(z) >= 0,
        pin(fp, ps, 2)(z) >= 0,
        pin(fp, ps, 0)(z) == 0 ==> pin(fp, ps, 2)(z) == 0,
{
    let rows = li_rows(fp);
    assert forall|i: int| 0 <= i < rows.len() implies
        -jt(ps, 2, z)(#[trigger] rows[i]) <= jt(ps, 1, z)(rows[i]) <= jt(ps, 2, z)(rows[i])
        && 0 <= jt(ps, 0, z)(rows[i])
        && (jt(ps, 0, z)(rows[i]) == 0 ==> jt(ps, 2, z)(rows[i]) == 0) by {
        lemma_term_bounds(ps, rows[i] + z);
    }
    lemma_sum_within(rows, jt(ps, 1, z), jt(ps, 2, z), jt(ps, 0, z), 0, rows.len() as int);
    assert(rows.subrange(0, rows.len() as int) =~= rows);
}

/// Over a range of part rows: `|tot sum| <= tot mass`, count and mass nonnegative, mass 0 without a count.
pub proof fn lemma_tot_bounds(fp: Seq<PartView>, cp: Seq<PartView>, ps: Seq<Literal>, a: int, b: int)
    requires 0 <= a <= b <= n_pa(cp),
    ensures
        -tot(fp, cp, ps, 2, a, b) <= tot(fp, cp, ps, 1, a, b) <= tot(fp, cp, ps, 2, a, b),
        tot(fp, cp, ps, 0, a, b) >= 0,
        tot(fp, cp, ps, 0, a, b) == 0 ==> tot(fp, cp, ps, 2, a, b) == 0,
{
    let rows = pa_rows(cp);
    assert forall|i: int| a <= i < b implies
        -pin(fp, ps, 2)(#[trigger] rows[i]) <= pin(fp, ps, 1)(rows[i]) <= pin(fp, ps, 2)(rows[i])
        && 0 <= pin(fp, ps, 0)(rows[i])
        && (pin(fp, ps, 0)(rows[i]) == 0 ==> pin(fp, ps, 2)(rows[i]) == 0) by {
        lemma_pin_bounds(fp, ps, rows[i]);
    }
    lemma_sum_within(rows, pin(fp, ps, 1), pin(fp, ps, 2), pin(fp, ps, 0), a, b);
}

/// Mass over part rows: a subrange's mass is at most the whole range's.
pub proof fn lemma_tot_mass_le(fp: Seq<PartView>, cp: Seq<PartView>, ps: Seq<Literal>, a: int, b: int, c: int, d: int)
    requires 0 <= a <= b <= c <= d <= n_pa(cp),
    ensures 0 <= tot(fp, cp, ps, 2, b, c) <= tot(fp, cp, ps, 2, a, d),
{
    let rows = pa_rows(cp);
    assert forall|i: int| a <= i < d implies pin(fp, ps, 2)(#[trigger] rows[i]) >= 0 by {
        lemma_pin_bounds(fp, ps, rows[i]);
    }
    lemma_sum_sub_le(rows, pin(fp, ps, 2), a, b, c, d);
}

} // verus!
