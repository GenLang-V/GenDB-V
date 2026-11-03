//! The statement's accumulators as sums over the stored rows.
//!
//! A joined row `z = a ++ b` has six columns: a lineitem row `a = [l_partkey, l_extendedprice, l_discount,
//! l_shipdate]` (`model::li_row`) and a part row `b = [p_partkey, p_type]` (`model::pa_row`). It qualifies when the
//! keys are equal and the shipdate lies in `[lo, hi)` (`zq`); its value is `l_extendedprice * (1 - l_discount)`
//! as a coefficient of scale 4 (`zv`), and it is a promotion when p_type is `LIKE 'PROMO%'` (`zp`).
//!
//! Every accumulator is a per-row term (`term(k, ..)`, `k` in `0..6`: count, promotion count, promotion sum, sum,
//! absolute mass, promotion absolute mass) summed over the joined rows. Over the stored rows this is, per lineitem
//! row, a sum over the part rows (`inner`), then a sum over a range of lineitem rows (`tot`). With dense part keys
//! (`model::dense`) the inner sum is the one part row `p_partkey - 1` (`lemma_inner_dense`, `rowval`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::spec::fns::like::like_value;
use crate::link::expr::{ival, tval};
use crate::link::join::{sum_of, lemma_sum_of_append, lemma_sum_of_remove, lemma_sum_of_zero};
use crate::gendb_entry::layout::PartView;
use super::model::*;

verus! {

// ------------------------------------------------------------------------------------------------ terms

/// The bytes of the pattern `'PROMO%'`.
pub open spec fn promo_pat() -> Seq<u8> {
    seq![80u8, 82u8, 79u8, 77u8, 79u8, 37u8]
}

/// `s LIKE 'PROMO%'` (escape `\`) is true.
pub open spec fn promo_text(s: Seq<u8>) -> bool {
    like_value(Val::Text(s), Val::Text(promo_pat()), Val::Text(seq![92u8])) == Ok::<Val, SqlError>(Val::Bool(true))
}

/// The join and date condition of a joined row.
pub open spec fn zq(lo: int, hi: int, z: Row) -> bool {
    ival(z[0]) == ival(z[4]) && lo <= ival(z[3]) && ival(z[3]) < hi
}

/// `l_extendedprice * (1 - l_discount)`: a coefficient of scale 4.
pub open spec fn zv(z: Row) -> int {
    ival(z[1]) * (100 - ival(z[2]))
}

/// p_type is a promotion type.
pub open spec fn zp(z: Row) -> bool {
    promo_text(tval(z[5]))
}

/// Accumulator kinds.
pub open spec fn K_CNT() -> int { 0 }
pub open spec fn K_PCNT() -> int { 1 }
pub open spec fn K_PSUM() -> int { 2 }
pub open spec fn K_SUM() -> int { 3 }
pub open spec fn K_MASS() -> int { 4 }
pub open spec fn K_PMASS() -> int { 5 }

/// The per-row term of accumulator `k` (`contrib` of the joined row).
pub open spec fn term(k: int, lo: int, hi: int) -> spec_fn(Row) -> int {
    |z: Row| contrib(k, zq(lo, hi, z), zp(z), zv(z))
}

/// Per lineitem row `a`: the terms of `a ++ b` summed over the stored part rows `b`.
pub open spec fn inner(cp: Seq<PartView>, k: int, lo: int, hi: int) -> spec_fn(Row) -> int {
    |a: Row| sum_of(pa_rows(cp), |b: Row| term(k, lo, hi)(a + b))
}

/// Accumulator `k` over the stored lineitem rows `r0 .. r1` joined with every stored part row.
pub open spec fn tot(fp: Seq<PartView>, cp: Seq<PartView>, k: int, lo: int, hi: int, r0: int, r1: int) -> int {
    sum_of(li_rows(fp).subrange(r0, r1), inner(cp, k, lo, hi))
}

// ------------------------------------------------------------------------------------------------ sums over ranges

/// One more row of a range.
pub proof fn lemma_sum_step(rows: Seq<Row>, f: spec_fn(Row) -> int, r0: int, i: int)
    requires 0 <= r0 <= i < rows.len(),
    ensures sum_of(rows.subrange(r0, i + 1), f) == sum_of(rows.subrange(r0, i), f) + f(rows[i]),
{
    let s = rows.subrange(r0, i + 1);
    assert(s.drop_last() =~= rows.subrange(r0, i));
    assert(s.last() == rows[i]);
}

/// The empty range sums to 0.
pub proof fn lemma_sum_empty(rows: Seq<Row>, f: spec_fn(Row) -> int, r0: int)
    requires 0 <= r0 <= rows.len(),
    ensures sum_of(rows.subrange(r0, r0), f) == 0,
{
    assert(rows.subrange(r0, r0).len() == 0);
}

/// A range splits at any point.
pub proof fn lemma_sum_split(rows: Seq<Row>, f: spec_fn(Row) -> int, a: int, b: int, c: int)
    requires 0 <= a <= b <= c <= rows.len(),
    ensures sum_of(rows.subrange(a, c), f) == sum_of(rows.subrange(a, b), f) + sum_of(rows.subrange(b, c), f),
{
    assert(rows.subrange(a, c) =~= rows.subrange(a, b) + rows.subrange(b, c));
    lemma_sum_of_append(rows.subrange(a, b), rows.subrange(b, c), f);
}

/// `tot` steps by one lineitem row.
pub proof fn lemma_tot_step(fp: Seq<PartView>, cp: Seq<PartView>, k: int, lo: int, hi: int, r0: int, i: int)
    requires 0 <= r0 <= i < n_li(fp),
    ensures tot(fp, cp, k, lo, hi, r0, i + 1) == tot(fp, cp, k, lo, hi, r0, i) + inner(cp, k, lo, hi)(li_rows(fp)[i]),
{
    lemma_sum_step(li_rows(fp), inner(cp, k, lo, hi), r0, i);
}

/// `tot` over an empty range.
pub proof fn lemma_tot_empty(fp: Seq<PartView>, cp: Seq<PartView>, k: int, lo: int, hi: int, r0: int)
    requires 0 <= r0 <= n_li(fp),
    ensures tot(fp, cp, k, lo, hi, r0, r0) == 0,
{
    lemma_sum_empty(li_rows(fp), inner(cp, k, lo, hi), r0);
}

/// `tot` splits at any point.
pub proof fn lemma_tot_split(fp: Seq<PartView>, cp: Seq<PartView>, k: int, lo: int, hi: int, a: int, b: int, c: int)
    requires 0 <= a <= b <= c <= n_li(fp),
    ensures tot(fp, cp, k, lo, hi, a, c) == tot(fp, cp, k, lo, hi, a, b) + tot(fp, cp, k, lo, hi, b, c),
{
    lemma_sum_split(li_rows(fp), inner(cp, k, lo, hi), a, b, c);
}

// ------------------------------------------------------------------------------------------------ one lineitem row

/// Contributions of the six accumulators are bounded by the count's and the mass's: `0 <= count, promotion count
/// <= 1`, every sum within the mass, the promotion mass within the mass.
pub proof fn lemma_contrib_bounds(q: bool, pr: bool, v: int)
    ensures
        0 <= contrib(1, q, pr, v) <= contrib(0, q, pr, v) <= 1,
        0 <= contrib(5, q, pr, v) <= contrib(4, q, pr, v),
        -contrib(4, q, pr, v) <= contrib(2, q, pr, v) <= contrib(4, q, pr, v),
        -contrib(4, q, pr, v) <= contrib(3, q, pr, v) <= contrib(4, q, pr, v),
{
}

/// The joined row of lineitem row `a` and part row `b`.
pub proof fn lemma_joined(a: Row, b: Row)
    requires a.len() == 4, b.len() == 2,
    ensures
        (a + b).len() == 6,
        (a + b)[0] == a[0], (a + b)[1] == a[1], (a + b)[2] == a[2], (a + b)[3] == a[3],
        (a + b)[4] == b[0], (a + b)[5] == b[1],
{
}

/// The contribution to accumulator `k` of one joined pair: none unless it qualifies (`q`); `pr` is the promotion
/// test and `v` the value.
pub open spec fn contrib(k: int, q: bool, pr: bool, v: int) -> int {
    if !q {
        0
    } else if k == 0 {
        1
    } else if k == 1 {
        if pr { 1 } else { 0 }
    } else if k == 2 {
        if pr { v } else { 0 }
    } else if k == 3 {
        v
    } else if k == 4 {
        abs(v)
    } else {
        if pr { abs(v) } else { 0 }
    }
}

/// Accumulator `k` of stored lineitem row `i` under dense part keys: the contribution of its one matching part row
/// `l_partkey - 1`.
pub open spec fn rowval(fp: Seq<PartView>, cp: Seq<PartView>, k: int, lo: int, hi: int, i: int) -> int {
    let key = lpk_at(fp, i);
    let s = ship_at(fp, i);
    contrib(k, lo <= s && s < hi && 1 <= key && key <= n_pa(cp), promo_text(ptype_at(cp, key - 1)),
        price_at(fp, i) * (100 - disc_at(fp, i)))
}

/// The part row at stored position `j`.
pub proof fn lemma_pa_row(cp: Seq<PartView>, j: int)
    requires 0 <= j < n_pa(cp),
    ensures
        pa_rows(cp)[j] == pa_row(pkey_at(cp, j), ptype_at(cp, j)),
        pa_rows(cp)[j].len() == 2,
        ival(pa_rows(cp)[j][0]) == pkey_at(cp, j),
        tval(pa_rows(cp)[j][1]) == ptype_at(cp, j),
{
}

/// The lineitem row at stored position `i`.
pub proof fn lemma_li_row(fp: Seq<PartView>, i: int)
    requires 0 <= i < n_li(fp),
    ensures
        li_rows(fp)[i] == li_row(lpk_at(fp, i), price_at(fp, i), disc_at(fp, i), ship_at(fp, i)),
        li_rows(fp)[i].len() == 4,
        ival(li_rows(fp)[i][0]) == lpk_at(fp, i),
        ival(li_rows(fp)[i][1]) == price_at(fp, i),
        ival(li_rows(fp)[i][2]) == disc_at(fp, i),
        ival(li_rows(fp)[i][3]) == ship_at(fp, i),
{
}

/// Under dense part keys, the inner sum of stored lineitem row `i` is `rowval`.
pub proof fn lemma_inner_dense(fp: Seq<PartView>, cp: Seq<PartView>, k: int, lo: int, hi: int, i: int)
    requires
        dense(cp),
        0 <= i < n_li(fp),
    ensures
        inner(cp, k, lo, hi)(li_rows(fp)[i]) == rowval(fp, cp, k, lo, hi, i),
{
    let a = li_rows(fp)[i];
    let bs = pa_rows(cp);
    let f = |b: Row| term(k, lo, hi)(a + b);
    let key = lpk_at(fp, i);
    let np = n_pa(cp);
    lemma_li_row(fp, i);
    assert(inner(cp, k, lo, hi)(a) == sum_of(bs, f));
    if 1 <= key && key <= np {
        let m = key - 1;
        lemma_pa_row(cp, m);
        lemma_sum_of_remove(bs, m, f);
        let rest = bs.remove(m);
        assert forall|x: int| 0 <= x < rest.len() implies f(#[trigger] rest[x]) == 0 by {
            let j = if x < m { x } else { x + 1 };
            assert(rest[x] == bs[j]);
            lemma_pa_row(cp, j);
            lemma_joined(a, bs[j]);
            assert(pkey_at(cp, j) == j + 1);
            assert(!zq(lo, hi, a + bs[j]));
        }
        lemma_sum_of_zero(rest, f);
        lemma_joined(a, bs[m]);
        assert(pkey_at(cp, m) == key);
        let z = a + bs[m];
        assert(ival(z[0]) == key && ival(z[4]) == key);
        assert(tval(z[5]) == ptype_at(cp, m));
        assert(ival(z[1]) == price_at(fp, i) && ival(z[2]) == disc_at(fp, i) && ival(z[3]) == ship_at(fp, i));
    } else {
        assert forall|x: int| 0 <= x < bs.len() implies f(#[trigger] bs[x]) == 0 by {
            lemma_pa_row(cp, x);
            lemma_joined(a, bs[x]);
            assert(pkey_at(cp, x) == x + 1);
            assert(!zq(lo, hi, a + bs[x]));
        }
        lemma_sum_of_zero(bs, f);
    }
}

/// A lineitem row outside the shipdate window joins with no part row.
pub proof fn lemma_inner_out(cp: Seq<PartView>, k: int, lo: int, hi: int, a: Row)
    requires
        a.len() == 4,
        !(lo <= ival(a[3]) && ival(a[3]) < hi),
    ensures
        inner(cp, k, lo, hi)(a) == 0,
{
    let bs = pa_rows(cp);
    let f = |b: Row| term(k, lo, hi)(a + b);
    assert forall|x: int| 0 <= x < bs.len() implies f(#[trigger] bs[x]) == 0 by {
        lemma_pa_row(cp, x);
        lemma_joined(a, bs[x]);
        assert(!zq(lo, hi, a + bs[x]));
    }
    lemma_sum_of_zero(bs, f);
}

/// Stored lineitem rows `a .. b` outside the shipdate window contribute nothing.
pub proof fn lemma_tot_zero(fp: Seq<PartView>, cp: Seq<PartView>, k: int, lo: int, hi: int, a: int, b: int)
    requires
        0 <= a <= b <= n_li(fp),
        forall|i: int| a <= i < b ==> !(lo <= #[trigger] ship_at(fp, i) && ship_at(fp, i) < hi),
    ensures
        tot(fp, cp, k, lo, hi, a, b) == 0,
    decreases b - a,
{
    if b > a {
        lemma_tot_zero(fp, cp, k, lo, hi, a, b - 1);
        lemma_tot_step(fp, cp, k, lo, hi, a, b - 1);
        lemma_li_row(fp, b - 1);
        assert(!(lo <= ship_at(fp, b - 1) && ship_at(fp, b - 1) < hi));
        lemma_inner_out(cp, k, lo, hi, li_rows(fp)[b - 1]);
    } else {
        lemma_tot_empty(fp, cp, k, lo, hi, a);
    }
}

/// Under dense part keys, `tot` steps by `rowval` (accumulators 0..5).
pub proof fn lemma_tot_dense_step(fp: Seq<PartView>, cp: Seq<PartView>, lo: int, hi: int, r0: int, i: int)
    requires
        dense(cp),
        0 <= r0 <= i < n_li(fp),
    ensures
        tot(fp, cp, 0, lo, hi, r0, i + 1) == tot(fp, cp, 0, lo, hi, r0, i) + rowval(fp, cp, 0, lo, hi, i),
        tot(fp, cp, 1, lo, hi, r0, i + 1) == tot(fp, cp, 1, lo, hi, r0, i) + rowval(fp, cp, 1, lo, hi, i),
        tot(fp, cp, 2, lo, hi, r0, i + 1) == tot(fp, cp, 2, lo, hi, r0, i) + rowval(fp, cp, 2, lo, hi, i),
        tot(fp, cp, 3, lo, hi, r0, i + 1) == tot(fp, cp, 3, lo, hi, r0, i) + rowval(fp, cp, 3, lo, hi, i),
        tot(fp, cp, 4, lo, hi, r0, i + 1) == tot(fp, cp, 4, lo, hi, r0, i) + rowval(fp, cp, 4, lo, hi, i),
{
    lemma_tot_step(fp, cp, 0, lo, hi, r0, i);
    lemma_tot_step(fp, cp, 1, lo, hi, r0, i);
    lemma_tot_step(fp, cp, 2, lo, hi, r0, i);
    lemma_tot_step(fp, cp, 3, lo, hi, r0, i);
    lemma_tot_step(fp, cp, 4, lo, hi, r0, i);
    lemma_inner_dense(fp, cp, 0, lo, hi, i);
    lemma_inner_dense(fp, cp, 1, lo, hi, i);
    lemma_inner_dense(fp, cp, 2, lo, hi, i);
    lemma_inner_dense(fp, cp, 3, lo, hi, i);
    lemma_inner_dense(fp, cp, 4, lo, hi, i);
}

} // verus!
