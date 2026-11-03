//! Per-group accumulators of Q1 and their meaning in the normal form (`acc_ok`): over a row sequence `rs` and a
//! group key `k`, the count and the exact SUM coefficients of quantity, price and discount (these cannot overflow:
//! `|sum| <= count * 10^15`, kept as a linear bound), and the SUMs of the two products (disc_price, charge) in one
//! of two modes:
//! - `small`: every row of the group had both products inside 64 bits, so each product's absolute mass (`gabs`) is
//!   at most `count * 2^63 < 2^127`: the sums are exact and no mass needs tracking (the fast path);
//! - exact: the sum together with the exact absolute mass, or the fact that the mass already exceeds `i128::MAX`
//!   (`over_*`, sticky: the SUM/AVG capacity condition of that group fails).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::link::query::*;
use crate::link::expr::i128_max;
use crate::agent::normal::*;

verus! {

/// Accumulators of one group.
#[derive(Clone, Copy)]
pub struct Acc {
    /// A row of the group (its key is the group's key).
    pub rep: usize,
    /// Number of rows.
    pub cnt: u64,
    /// SUM coefficients (scale 2) of quantity, extendedprice and discount.
    pub sum_qty: i128,
    pub sum_price: i128,
    pub sum_disc: i128,
    /// Mode of the product sums: bounded masses (`true`) or exact masses (`false`).
    pub small: bool,
    /// SUM coefficient (scale 4) of price * (1 - discount); exact mode: its absolute mass, and whether the mass
    /// exceeds i128.
    pub sum_dp: i128,
    pub mass_dp: i128,
    pub over_dp: bool,
    /// SUM coefficient (scale 6) of the charge; exact mode: its absolute mass, and whether it exceeds i128.
    pub sum_ch: i128,
    pub mass_ch: i128,
    pub over_ch: bool,
}

/// `|x| <= cnt * 10^15`.
pub open spec fn within(x: i128, cnt: u64) -> bool {
    -(cnt as int) * coeff_bound() <= x as int <= (cnt as int) * coeff_bound()
}

/// `2^63`: the bound of a product inside 64 bits.
pub open spec fn p63() -> int {
    0x8000_0000_0000_0000
}

/// The mass bound of `cnt` products inside 64 bits: `cnt * 2^63`.
pub open spec fn small_bound(cnt: u64) -> int {
    cnt as int * p63()
}

/// A product inside 64 bits.
pub open spec fn fits_i64(v: int) -> bool {
    -p63() <= v < p63()
}

/// One exact-mode product accumulator: the exact sum and mass, or a mass beyond `i128::MAX`.
pub open spec fn prod_ok(over: bool, sum: i128, mass: i128, gsum_v: int, gabs_v: int) -> bool {
    if over {
        gabs_v > i128_max()
    } else {
        mass as int == gabs_v && sum as int == gsum_v
    }
}

/// One small-mode product accumulator: the exact sum, and a mass of at most `cnt * 2^63`.
pub open spec fn small_ok(sum: i128, cnt: u64, gsum_v: int, gabs_v: int) -> bool {
    sum as int == gsum_v && gabs_v <= small_bound(cnt)
}

/// The accumulators of group `k` over rows `rs`.
pub open spec fn acc_ok(pd: int, rs: Seq<Row>, k: Row, a: Acc) -> bool {
    let g = q1_spec(pd);
    &&& a.cnt as int == gcount(g, rs, k)
    &&& a.sum_qty as int == gsum(g, rs, k, 0)
    &&& a.sum_price as int == gsum(g, rs, k, 1)
    &&& a.sum_disc as int == gsum(g, rs, k, 6)
    &&& within(a.sum_qty, a.cnt) && within(a.sum_price, a.cnt) && within(a.sum_disc, a.cnt)
    &&& if a.small {
        &&& !a.over_dp && !a.over_ch
        &&& small_ok(a.sum_dp, a.cnt, gsum(g, rs, k, 2), gabs(g, rs, k, 2))
        &&& small_ok(a.sum_ch, a.cnt, gsum(g, rs, k, 3), gabs(g, rs, k, 3))
    } else {
        &&& prod_ok(a.over_dp, a.sum_dp, a.mass_dp, gsum(g, rs, k, 2), gabs(g, rs, k, 2))
        &&& prod_ok(a.over_ch, a.sum_ch, a.mass_ch, gsum(g, rs, k, 3), gabs(g, rs, k, 3))
    }
}

/// Zero accumulators with representative row `rep`, in mode `small`.
pub open spec fn acc_zero(rep: usize, small: bool) -> Acc {
    Acc {
        rep,
        cnt: 0,
        sum_qty: 0,
        sum_price: 0,
        sum_disc: 0,
        small,
        sum_dp: 0,
        mass_dp: 0,
        over_dp: false,
        sum_ch: 0,
        mass_ch: 0,
        over_ch: false,
    }
}

pub fn new_acc(rep: usize, small: bool) -> (a: Acc)
    ensures a == acc_zero(rep, small),
    no_unwind
{
    Acc {
        rep,
        cnt: 0,
        sum_qty: 0,
        sum_price: 0,
        sum_disc: 0,
        small,
        sum_dp: 0,
        mass_dp: 0,
        over_dp: false,
        sum_ch: 0,
        mass_ch: 0,
        over_ch: false,
    }
}

/// Zero accumulators are the accumulators of every key over no rows.
pub proof fn lemma_acc_empty(pd: int, k: Row, rep: usize, small: bool)
    ensures acc_ok(pd, Seq::empty(), k, acc_zero(rep, small)),
{
}

/// A row that does not belong to group `k` leaves its accumulators unchanged.
pub proof fn lemma_acc_miss(pd: int, rs: Seq<Row>, x: Row, k: Row, a: Acc)
    requires acc_ok(pd, rs, k, a), !hit(q1_spec(pd), x, k),
    ensures acc_ok(pd, rs.push(x), k, a),
{
    let g = q1_spec(pd);
    lemma_push(g, rs, x, k, 0);
    lemma_push(g, rs, x, k, 1);
    lemma_push(g, rs, x, k, 2);
    lemma_push(g, rs, x, k, 3);
    lemma_push(g, rs, x, k, 6);
}

/// The exact-mode product accumulator after one more value `v` (sticky overflow of the mass).
pub open spec fn prod_step_ok(over0: bool, sum0: i128, mass0: i128, over: bool, sum: i128, mass: i128, v: int) -> bool {
    &&& over == (over0 || mass0 as int + abs(v) > i128_max())
    &&& !over ==> mass as int == mass0 as int + abs(v) && sum as int == sum0 as int + v
}

/// Accumulator `b` is `a` plus one row with coefficients (q, e, d) and products (dp, ch).
pub open spec fn acc_step(a: Acc, b: Acc, q: int, e: int, d: int, dp: int, ch: int) -> bool {
    &&& b.rep == a.rep
    &&& b.small == a.small
    &&& b.cnt as int == a.cnt as int + 1
    &&& b.sum_qty as int == a.sum_qty as int + q
    &&& b.sum_price as int == a.sum_price as int + e
    &&& b.sum_disc as int == a.sum_disc as int + d
    &&& within(b.sum_qty, b.cnt) && within(b.sum_price, b.cnt) && within(b.sum_disc, b.cnt)
    &&& if a.small {
        &&& fits_i64(dp) && fits_i64(ch)
        &&& !b.over_dp && !b.over_ch
        &&& b.sum_dp as int == a.sum_dp as int + dp
        &&& b.sum_ch as int == a.sum_ch as int + ch
    } else {
        &&& prod_step_ok(a.over_dp, a.sum_dp, a.mass_dp, b.over_dp, b.sum_dp, b.mass_dp, dp)
        &&& prod_step_ok(a.over_ch, a.sum_ch, a.mass_ch, b.over_ch, b.sum_ch, b.mass_ch, ch)
    }
}

/// A row of group `k` adds its contribution.
pub proof fn lemma_acc_hit(pd: int, rs: Seq<Row>, x: Row, k: Row, a: Acc, b: Acc)
    requires
        acc_ok(pd, rs, k, a),
        hit(q1_spec(pd), x, k),
        acc_step(a, b, q1_arg(0, x), q1_arg(1, x), q1_arg(6, x), q1_arg(2, x), q1_arg(3, x)),
    ensures acc_ok(pd, rs.push(x), k, b),
{
    let g = q1_spec(pd);
    lemma_push(g, rs, x, k, 0);
    lemma_push(g, rs, x, k, 1);
    lemma_push(g, rs, x, k, 2);
    lemma_push(g, rs, x, k, 3);
    lemma_push(g, rs, x, k, 6);
    lemma_abs_bound(g, rs, k, 2);
    lemma_abs_bound(g, rs, k, 3);
    if a.small {
        assert(small_bound(b.cnt) == small_bound(a.cnt) + p63());
    }
}

/// Product accumulator invariant used by `add_row_at`: not overflowed means a nonnegative mass bounding the sum.
pub open spec fn prod_inv(over: bool, sum: i128, mass: i128) -> bool {
    !over ==> 0 <= mass && -(mass as int) <= sum as int <= mass as int
}

/// The machine invariant of an accumulator (what keeps its additions inside `i128`).
pub open spec fn acc_inv(a: Acc) -> bool {
    &&& within(a.sum_qty, a.cnt) && within(a.sum_price, a.cnt) && within(a.sum_disc, a.cnt)
    &&& if a.small {
        &&& !a.over_dp && !a.over_ch
        &&& -small_bound(a.cnt) <= a.sum_dp as int <= small_bound(a.cnt)
        &&& -small_bound(a.cnt) <= a.sum_ch as int <= small_bound(a.cnt)
    } else {
        &&& prod_inv(a.over_dp, a.sum_dp, a.mass_dp)
        &&& prod_inv(a.over_ch, a.sum_ch, a.mass_ch)
    }
}

/// `acc_ok` implies the machine invariant (a sum is bounded by its mass).
pub proof fn lemma_acc_inv(pd: int, rs: Seq<Row>, k: Row, a: Acc)
    requires acc_ok(pd, rs, k, a),
    ensures acc_inv(a),
{
    let g = q1_spec(pd);
    lemma_abs_bound(g, rs, k, 2);
    lemma_abs_bound(g, rs, k, 3);
}

/// `small_bound` of a count below `u64::MAX`, one step up, stays inside `i128`.
pub proof fn lemma_small_bound_step(cnt: u64)
    requires cnt < u64::MAX,
    ensures
        small_bound(cnt) + p63() == small_bound((cnt + 1) as u64),
        small_bound((cnt + 1) as u64) <= i128_max(),
{
    assert(small_bound((cnt + 1) as u64) == (cnt + 1) * p63());
    assert((cnt + 1) * p63() <= 0xffff_ffff_ffff_ffff * p63()) by (nonlinear_arith)
        requires cnt + 1 <= 0xffff_ffff_ffff_ffff;
}

/// Adds one row to slot `s` in place. A small-mode slot takes only rows whose products fit 64 bits.
#[inline(always)]
pub fn add_row_at(slots: &mut Vec<Acc>, s: usize, q: i64, e: i64, d: i64, dp: i128, ch: i128)
    requires
        s < old(slots)@.len(),
        acc_inv(old(slots)@[s as int]),
        old(slots)@[s as int].cnt < u64::MAX,
        coeff_ok_int(q as int), coeff_ok_int(e as int), coeff_ok_int(d as int),
        old(slots)@[s as int].small ==> fits_i64(dp as int) && fits_i64(ch as int),
        dp != i128::MIN,
    ensures
        final(slots)@.len() == old(slots)@.len(),
        final(slots)@ == old(slots)@.update(s as int, final(slots)@[s as int]),
        acc_step(old(slots)@[s as int], final(slots)@[s as int], q as int, e as int, d as int, dp as int, ch as int),
        acc_inv(final(slots)@[s as int]),
    no_unwind
{
    let ghost a = slots@[s as int];
    slots[s].cnt = slots[s].cnt + 1;
    slots[s].sum_qty = slots[s].sum_qty + q as i128;
    slots[s].sum_price = slots[s].sum_price + e as i128;
    slots[s].sum_disc = slots[s].sum_disc + d as i128;
    if slots[s].small {
        proof {
            lemma_small_bound_step(a.cnt);
        }
        slots[s].sum_dp = slots[s].sum_dp + dp;
        slots[s].sum_ch = slots[s].sum_ch + ch;
    } else {
        if !slots[s].over_dp {
            let m = if dp < 0 { -dp } else { dp };
            match slots[s].mass_dp.checked_add(m) {
                Some(v) => {
                    slots[s].mass_dp = v;
                    slots[s].sum_dp = slots[s].sum_dp + dp;
                },
                None => {
                    slots[s].over_dp = true;
                },
            }
        }
        if !slots[s].over_ch {
            if ch == i128::MIN {
                // |ch| = 2^127 alone exceeds i128::MAX.
                slots[s].over_ch = true;
            } else {
                let m = if ch < 0 { -ch } else { ch };
                match slots[s].mass_ch.checked_add(m) {
                    Some(v) => {
                        slots[s].mass_ch = v;
                        slots[s].sum_ch = slots[s].sum_ch + ch;
                    },
                    None => {
                        slots[s].over_ch = true;
                    },
                }
            }
        }
    }
    proof {
        assert(slots@ =~= old(slots)@.update(s as int, slots@[s as int]));
    }
}

/// A numeric(15,2) coefficient (as an integer).
pub open spec fn coeff_ok_int(x: int) -> bool {
    -coeff_bound() < x < coeff_bound()
}

} // verus!
