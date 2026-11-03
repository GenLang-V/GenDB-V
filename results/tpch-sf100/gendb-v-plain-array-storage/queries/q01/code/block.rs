//! The fast scan of a row range in small mode (`scan_fast`): rows are added to per-slot 64-bit deltas (`Delta`)
//! instead of the 128-bit slot accumulators, and the deltas are added into the slots (`flush`) every `BLOCK` rows.
//!
//! A qualifying row takes the fast path when its returnflag and linestatus are one byte each, its key already has a
//! slot (found through the one-byte key index) and its coefficients are tiny (`tiny`: quantity and price in
//! `[0, 2^31)`, discount and tax in `[0, 128)`); then a block of at most `BLOCK = 2^14` rows keeps every delta inside
//! 64 bits (`delta_bound`). The first row that does not take the fast path ends the scan: the caller hands it to
//! the general scan (`scan::scan_range`) and resumes.
//!
//! Invariant inside a block: the slots with their deltas added (`view_table`) form the group table of the rows
//! scanned so far (`scan::table_ok`); at a block boundary every delta is zero, so the slots alone form it.
use vstd::prelude::*;
use crate::link::query::*;
use crate::agent::normal::*;
use crate::agent::columns::*;
use crate::agent::accum::*;
use crate::agent::scan::*;

verus! {

/// Rows per block: `2^14`.
pub const BLOCK: usize = 16384;

/// Exclusive bound of a tiny quantity or price coefficient: `2^31`.
pub open spec fn qmax() -> int {
    0x8000_0000
}

/// Bound of a tiny row's `|disc_price|` coefficient (`< 2^31 * 128 <= 2^38`).
pub open spec fn dpmax() -> int {
    0x40_0000_0000
}

/// Bound of a tiny row's `|charge|` coefficient (`< 2^38 * 228 <= 2^46`).
pub open spec fn chmax() -> int {
    0x4000_0000_0000
}

/// The 64-bit deltas of one slot since the last flush: count and SUM coefficients.
#[derive(Clone, Copy)]
pub struct Delta {
    pub cnt: i64,
    pub qty: i64,
    pub price: i64,
    pub disc: i64,
    pub dp: i64,
    pub ch: i64,
}

pub open spec fn delta_zero() -> Delta {
    Delta { cnt: 0, qty: 0, price: 0, disc: 0, dp: 0, ch: 0 }
}

pub fn new_delta() -> (d: Delta)
    ensures d == delta_zero(),
    no_unwind
{
    Delta { cnt: 0, qty: 0, price: 0, disc: 0, dp: 0, ch: 0 }
}

/// The accumulators of a slot with its delta added fit their types.
pub open spec fn fits(a: Acc, d: Delta) -> bool {
    &&& 0 <= d.cnt
    &&& a.cnt + d.cnt <= u64::MAX
    &&& i128::MIN <= a.sum_qty + d.qty <= i128::MAX
    &&& i128::MIN <= a.sum_price + d.price <= i128::MAX
    &&& i128::MIN <= a.sum_disc + d.disc <= i128::MAX
    &&& i128::MIN <= a.sum_dp + d.dp <= i128::MAX
    &&& i128::MIN <= a.sum_ch + d.ch <= i128::MAX
}

/// Slot accumulators `a` with the delta `d` added (exact under `fits`).
pub open spec fn eff(a: Acc, d: Delta) -> Acc {
    Acc {
        rep: a.rep,
        cnt: (a.cnt + d.cnt) as u64,
        sum_qty: (a.sum_qty + d.qty) as i128,
        sum_price: (a.sum_price + d.price) as i128,
        sum_disc: (a.sum_disc + d.disc) as i128,
        small: a.small,
        sum_dp: (a.sum_dp + d.dp) as i128,
        mass_dp: a.mass_dp,
        over_dp: a.over_dp,
        sum_ch: (a.sum_ch + d.ch) as i128,
        mass_ch: a.mass_ch,
        over_ch: a.over_ch,
    }
}

/// The table the slots and their deltas stand for: slot `s < ng` with its delta added.
pub open spec fn view_table(slots: Seq<Acc>, blk: Seq<Delta>, ng: int) -> Seq<Acc> {
    Seq::new(slots.len(), |s: int| if s < ng { eff(slots[s], blk[s]) } else { slots[s] })
}

/// The deltas after `k` tiny rows.
pub open spec fn delta_bound(d: Delta, k: int) -> bool {
    &&& 0 <= d.cnt <= k
    &&& 0 <= d.qty <= k * qmax()
    &&& 0 <= d.price <= k * qmax()
    &&& 0 <= d.disc <= k * 128
    &&& -k * dpmax() <= d.dp <= k * dpmax()
    &&& -k * chmax() <= d.ch <= k * chmax()
}

/// The coefficients of a tiny row.
pub open spec fn tiny(q: int, e: int, d: int, dp: int, ch: int) -> bool {
    &&& 0 <= q < qmax()
    &&& 0 <= e < qmax()
    &&& 0 <= d < 128
    &&& -dpmax() <= dp <= dpmax()
    &&& -chmax() <= ch <= chmax()
}

/// Every delta is zero.
pub open spec fn blk_zero(blk: Seq<Delta>) -> bool {
    forall|s: int| 0 <= s < blk.len() ==> #[trigger] blk[s] == delta_zero()
}

/// With zero deltas the view is the slots.
pub proof fn lemma_view_zero(slots: Seq<Acc>, blk: Seq<Delta>, ng: int)
    requires blk_zero(blk), 0 <= ng <= slots.len(), ng <= blk.len(),
    ensures
        view_table(slots, blk, ng) == slots,
        forall|s: int| 0 <= s < ng ==> fits(slots[s], #[trigger] blk[s]) && delta_bound(blk[s], 0),
{
    assert forall|s: int| 0 <= s < ng implies fits(slots[s], #[trigger] blk[s]) && delta_bound(blk[s], 0) by {
        assert(blk[s] == delta_zero());
    }
    assert forall|s: int| 0 <= s < slots.len() implies #[trigger] view_table(slots, blk, ng)[s] == slots[s] by {
        if s < ng {
            assert(blk[s] == delta_zero());
            let a = slots[s];
            assert(eff(a, blk[s]) =~= a);
        }
    }
    assert(view_table(slots, blk, ng) =~= slots);
}

/// The index only reads the representatives, which the view keeps.
pub proof fn lemma_idx_same_reps(c: Cols, s1: Seq<Acc>, s2: Seq<Acc>, ng: int, idx: Seq<usize>)
    requires
        idx_ok(c, s1, ng, idx),
        s1.len() == s2.len(),
        0 <= ng <= s1.len(),
        forall|t: int| 0 <= t < ng ==> (#[trigger] s2[t]).rep == s1[t].rep,
    ensures idx_ok(c, s2, ng, idx),
{
    assert forall|code: int| 0 <= code < IDX_LEN && #[trigger] idx[code] != 0 implies
        idx[code] - 1 < ng && short_key(c, s2[idx[code] - 1].rep as int) && row_code(c, s2[idx[code] - 1].rep as int) == code by {
        assert(s2[idx[code] - 1].rep == s1[idx[code] - 1].rep);
    }
    assert forall|s: int| 0 <= s < ng && short_key(c, (#[trigger] s2[s]).rep as int) implies
        idx[row_code(c, s2[s].rep as int)] == s + 1 by {
        assert(s2[s].rep == s1[s].rep);
    }
}

/// The view keeps the representatives and the modes of the slots.
pub proof fn lemma_view_reps(slots: Seq<Acc>, blk: Seq<Delta>, ng: int)
    requires 0 <= ng <= slots.len(),
    ensures
        view_table(slots, blk, ng).len() == slots.len(),
        forall|t: int| 0 <= t < slots.len() ==> (#[trigger] view_table(slots, blk, ng)[t]).rep == slots[t].rep
            && view_table(slots, blk, ng)[t].small == slots[t].small,
{
}

/// Adding one tiny row of slot `s` to its delta is one `acc_step` of the view, and keeps the view's table.
pub proof fn lemma_fast_step(
    pd: int,
    c: Cols,
    lo: int,
    i: int,
    slots: Seq<Acc>,
    blk: Seq<Delta>,
    ng: int,
    s: int,
    d2: Delta,
    k: int,
)
    requires
        0 <= lo <= i < c.n,
        0 <= k,
        table_ok(pd, c, lo, i, view_table(slots, blk, ng), ng),
        mode_ok(slots, ng, true),
        0 <= s < ng <= slots.len(),
        ng <= blk.len(),
        fits(slots[s], blk[s]),
        delta_bound(blk[s], k),
        q1_qual(pd, crow(c, i)),
        slot_key(c, slots[s]) == key_of(c, i),
        tiny(q1_arg(0, crow(c, i)), q1_arg(1, crow(c, i)), q1_arg(6, crow(c, i)), q1_arg(2, crow(c, i)), q1_arg(3, crow(c, i))),
        d2.cnt == blk[s].cnt + 1,
        d2.qty == blk[s].qty + q1_arg(0, crow(c, i)),
        d2.price == blk[s].price + q1_arg(1, crow(c, i)),
        d2.disc == blk[s].disc + q1_arg(6, crow(c, i)),
        d2.dp == blk[s].dp + q1_arg(2, crow(c, i)),
        d2.ch == blk[s].ch + q1_arg(3, crow(c, i)),
    ensures
        fits(slots[s], d2),
        delta_bound(d2, k + 1),
        table_ok(pd, c, lo, i + 1, view_table(slots, blk.update(s, d2), ng), ng),
{
    let v = view_table(slots, blk, ng);
    let x = crow(c, i);
    let a = v[s];
    let b = eff(slots[s], d2);
    lemma_table_slot(pd, c, lo, i, v, ng, s);
    lemma_acc_inv(pd, range_rows(c, lo, i), slot_key(c, a), a);
    assert(a == eff(slots[s], blk[s]));
    assert(slots[s].small);
    // The view's accumulators are the exact sums (no cast wraps under `fits`).
    assert(a.cnt as int == slots[s].cnt + blk[s].cnt);
    assert(a.sum_qty as int == slots[s].sum_qty + blk[s].qty);
    assert(a.sum_price as int == slots[s].sum_price + blk[s].price);
    assert(a.sum_disc as int == slots[s].sum_disc + blk[s].disc);
    assert(a.sum_dp as int == slots[s].sum_dp + blk[s].dp);
    assert(a.sum_ch as int == slots[s].sum_ch + blk[s].ch);
    assert(a.cnt < u64::MAX);
    lemma_small_bound_step(a.cnt);
    let q = q1_arg(0, x);
    let e = q1_arg(1, x);
    let d = q1_arg(6, x);
    // One more row keeps every linear bound of `acc_inv` inside the types.
    assert(within(a.sum_qty, a.cnt) && within(a.sum_price, a.cnt) && within(a.sum_disc, a.cnt));
    assert(-small_bound(a.cnt) <= a.sum_dp as int <= small_bound(a.cnt));
    assert(-small_bound(a.cnt) <= a.sum_ch as int <= small_bound(a.cnt));
    assert(small_bound((a.cnt + 1) as u64) == small_bound(a.cnt) + p63());
    assert(fits(slots[s], d2));
    assert(b.cnt as int == a.cnt + 1);
    assert(b.sum_qty as int == a.sum_qty + q);
    assert(b.sum_price as int == a.sum_price + e);
    assert(b.sum_disc as int == a.sum_disc + d);
    assert(b.sum_dp as int == a.sum_dp + q1_arg(2, x));
    assert(b.sum_ch as int == a.sum_ch + q1_arg(3, x));
    assert(within(b.sum_qty, b.cnt) && within(b.sum_price, b.cnt) && within(b.sum_disc, b.cnt));
    assert(acc_step(a, b, q, e, d, q1_arg(2, x), q1_arg(3, x)));
    assert(slot_key(c, a) == key_of(c, i));
    lemma_table_hit(pd, c, lo, i, v, ng, s, b, ng, true);
    assert(v.update(s, b) =~= view_table(slots, blk.update(s, d2), ng));
}

/// Row `lo + j` (qualifying) takes the fast path: its key is one byte each with slot `s`, and its coefficients are
/// tiny. Returns `Some((s, q, e, d, dp, ch))`, or `None` when the row needs the general scan.
#[inline(always)]
fn fast_row(
    c: &Cols,
    sp: &Span,
    lo: usize,
    hi: usize,
    j: usize,
    a0: i64,
    a1: i64,
    b0: i64,
    b1: i64,
    slots: &Vec<Acc>,
    ng: usize,
    idx: &Vec<usize>,
) -> (r: Option<(usize, i64, i64, i64, i64, i64)>)
    requires
        cols_wf(*c),
        lo <= hi <= c.n,
        j < hi - lo,
        span_ok(*c, lo as int, hi as int, *sp),
        a0 == sp.rf_offsets@[j as int], a1 == sp.rf_offsets@[j + 1],
        b0 == sp.ls_offsets@[j as int], b1 == sp.ls_offsets@[j + 1],
        ng <= slots@.len(),
        idx_ok(*c, slots@, ng as int, idx@),
    ensures
        r matches Some(v) ==> {
            let x = crow(*c, lo + j);
            &&& v.0 < ng
            &&& slot_key(*c, slots@[v.0 as int]) == key_of(*c, lo + j)
            &&& v.1 as int == q1_arg(0, x) && v.2 as int == q1_arg(1, x) && v.3 as int == q1_arg(6, x)
            &&& v.4 as int == q1_arg(2, x) && v.5 as int == q1_arg(3, x)
            &&& tiny(v.1 as int, v.2 as int, v.3 as int, v.4 as int, v.5 as int)
        },
    no_unwind
{
    let ghost i = lo + j;
    let code = match short_code(c, sp, lo, hi, j, a0, a1, b0, b1) {
        Some(code) => code,
        None => return None,
    };
    let s = idx[code];
    if s == 0 {
        return None;
    }
    proof {
        lemma_crow(*c, i);
        lemma_row_args(*c, i);
        lemma_short_keys(*c, slots@[s - 1].rep as int, i);
        assert(sp.qty@[j as int] == c.qty@[i] && sp.price@[j as int] == c.price@[i]);
        assert(sp.disc@[j as int] == c.disc@[i] && sp.tax@[j as int] == c.tax@[i]);
        assert(coeff_ok(c.qty@[i]) && coeff_ok(c.price@[i]) && coeff_ok(c.disc@[i]) && coeff_ok(c.tax@[i]));
    }
    let q = c64(sp.qty[j]);
    let e = c64(sp.price[j]);
    let d = c64(sp.disc[j]);
    let t = c64(sp.tax[j]);
    if q < 0 || q >= 0x8000_0000 || e < 0 || e >= 0x8000_0000 || d < 0 || d >= 128 || t < 0 || t >= 128 {
        return None;
    }
    let m = 100 - d;
    let w = 100 + t;
    proof {
        assert(-27 <= m <= 100 && 100 <= w < 228);
        assert(-dpmax() <= e * m <= dpmax()) by (nonlinear_arith)
            requires 0 <= e < 0x8000_0000, -27 <= m <= 100;
        assert(-chmax() <= (e * m) * w <= chmax()) by (nonlinear_arith)
            requires -dpmax() <= e * m <= dpmax(), 100 <= w < 228;
    }
    let dp = e * m;
    let ch = dp * w;
    Some(((s - 1) as usize, q, e, d, dp, ch))
}

/// Accumulates rows `[lo + j0, lo + bend)` into the deltas, stopping at the first qualifying row that does not take
/// the fast path. Returns the first row offset not scanned and whether the scan stopped early.
fn block_rows(
    c: &Cols,
    sp: &Span,
    lo: usize,
    hi: usize,
    j0: usize,
    bend: usize,
    limit: i32,
    Ghost(pd): Ghost<int>,
    slots: &Vec<Acc>,
    ng: usize,
    idx: &Vec<usize>,
    blk: &mut Vec<Delta>,
) -> (r: (usize, bool))
    requires
        cols_wf(*c),
        lo <= hi <= c.n,
        j0 < bend <= hi - lo,
        bend - j0 <= BLOCK,
        span_ok(*c, lo as int, hi as int, *sp),
        sp.rf_offsets@.len() == hi - lo + 1 && sp.ls_offsets@.len() == hi - lo + 1,
        limit as int == pd + 10957,
        ng <= slots@.len(),
        ng <= old(blk)@.len(),
        table_ok(pd, *c, lo as int, lo + j0, slots@, ng as int),
        idx_ok(*c, slots@, ng as int, idx@),
        mode_ok(slots@, ng as int, true),
        blk_zero(old(blk)@),
    ensures
        j0 <= r.0 <= bend,
        !r.1 ==> r.0 == bend,
        final(blk)@.len() == old(blk)@.len(),
        table_ok(pd, *c, lo as int, lo + r.0, view_table(slots@, final(blk)@, ng as int), ng as int),
        forall|s: int| 0 <= s < ng ==> fits(slots@[s], #[trigger] final(blk)@[s]),
        forall|s: int| ng <= s < final(blk)@.len() ==> #[trigger] final(blk)@[s] == delta_zero(),
    no_unwind
{
    hide(table_ok);
    hide(idx_ok);
    hide(mode_ok);
    let ghost blen = blk@.len();
    proof {
        lemma_view_zero(slots@, blk@, ng as int);
    }
    let mut j = j0;
    // Row j's start offsets, carried from the previous row's end offsets.
    let mut a0 = sp.rf_offsets[j];
    let mut b0 = sp.ls_offsets[j];
    while j < bend
        invariant
            cols_wf(*c),
            lo <= hi <= c.n,
            j0 <= j <= bend <= hi - lo,
            bend - j0 <= BLOCK,
            span_ok(*c, lo as int, hi as int, *sp),
            sp.rf_offsets@.len() == hi - lo + 1 && sp.ls_offsets@.len() == hi - lo + 1,
            a0 == sp.rf_offsets@[j as int],
            b0 == sp.ls_offsets@[j as int],
            limit as int == pd + 10957,
            ng <= slots@.len(),
            ng <= blen,
            blk@.len() == blen,
            blen == old(blk)@.len(),
            table_ok(pd, *c, lo as int, lo + j, view_table(slots@, blk@, ng as int), ng as int),
            idx_ok(*c, slots@, ng as int, idx@),
            mode_ok(slots@, ng as int, true),
            forall|s: int| 0 <= s < ng ==> fits(slots@[s], #[trigger] blk@[s]) && delta_bound(blk@[s], j - j0),
            forall|s: int| ng <= s < blen ==> #[trigger] blk@[s] == delta_zero(),
        decreases bend - j,
    {
        proof {
            lemma_crow(*c, lo + j);
            assert(sp.ship@[j as int] == c.ship@[lo + j]);
        }
        let a1 = sp.rf_offsets[j + 1];
        let b1 = sp.ls_offsets[j + 1];
        if sp.ship[j] > limit {
            proof {
                lemma_table_skip(pd, *c, lo as int, lo + j, view_table(slots@, blk@, ng as int), ng as int);
                assert forall|s: int| 0 <= s < ng implies fits(slots@[s], #[trigger] blk@[s]) && delta_bound(blk@[s], j + 1 - j0) by {
                    assert(delta_bound(blk@[s], j - j0));
                }
            }
        } else {
            proof {
                assert(q1_qual(pd, crow(*c, lo + j)));
            }
            match fast_row(c, sp, lo, hi, j, a0, a1, b0, b1, slots, ng, idx) {
                None => {
                    return (j, true);
                },
                Some((s, q, e, d, dp, ch)) => {
                    let old_d = blk[s];
                    proof {
                        assert(fits(slots@[s as int], old_d) && delta_bound(old_d, j - j0));
                        assert(j - j0 < BLOCK);
                    }
                    let d2 = Delta {
                        cnt: old_d.cnt + 1,
                        qty: old_d.qty + q,
                        price: old_d.price + e,
                        disc: old_d.disc + d,
                        dp: old_d.dp + dp,
                        ch: old_d.ch + ch,
                    };
                    let ghost blk0 = blk@;
                    proof {
                        reveal(mode_ok);
                        lemma_fast_step(pd, *c, lo as int, lo + j, slots@, blk0, ng as int, s as int, d2, j - j0);
                    }
                    blk[s] = d2;
                    proof {
                        assert(blk@ == blk0.update(s as int, d2));
                        assert forall|t: int| 0 <= t < ng implies fits(slots@[t], #[trigger] blk@[t]) && delta_bound(blk@[t], j + 1 - j0) by {
                            if t != s {
                                assert(blk@[t] == blk0[t]);
                                assert(delta_bound(blk0[t], j - j0));
                            }
                        }
                        assert forall|t: int| ng <= t < blen implies #[trigger] blk@[t] == delta_zero() by {
                            assert(blk@[t] == blk0[t]);
                        }
                    }
                },
            }
        }
        a0 = a1;
        b0 = b1;
        j = j + 1;
    }
    (bend, false)
}

/// Adds every delta into its slot and zeroes the deltas: the slots become the view.
fn flush(slots: &mut Vec<Acc>, blk: &mut Vec<Delta>, ng: usize)
    requires
        ng <= old(slots)@.len(),
        ng <= old(blk)@.len(),
        forall|s: int| 0 <= s < ng ==> fits(old(slots)@[s], #[trigger] old(blk)@[s]),
        forall|s: int| ng <= s < old(blk)@.len() ==> #[trigger] old(blk)@[s] == delta_zero(),
    ensures
        final(slots)@ == view_table(old(slots)@, old(blk)@, ng as int),
        final(blk)@.len() == old(blk)@.len(),
        blk_zero(final(blk)@),
    no_unwind
{
    let ghost s0 = slots@;
    let ghost k0 = blk@;
    let mut s: usize = 0;
    while s < ng
        invariant
            s <= ng,
            ng <= s0.len(),
            ng <= k0.len(),
            slots@.len() == s0.len(),
            blk@.len() == k0.len(),
            forall|t: int| 0 <= t < ng ==> fits(s0[t], #[trigger] k0[t]),
            forall|t: int| 0 <= t < s0.len() ==> #[trigger] slots@[t] == if t < s { eff(s0[t], k0[t]) } else { s0[t] },
            forall|t: int| 0 <= t < k0.len() ==> #[trigger] blk@[t] == if t < s || t >= ng { delta_zero() } else { k0[t] },
            forall|t: int| ng <= t < k0.len() ==> #[trigger] k0[t] == delta_zero(),
        decreases ng - s,
    {
        let d = blk[s];
        let a = slots[s];
        proof {
            assert(d == k0[s as int] && a == s0[s as int]);
            assert(fits(a, d));
        }
        let b = Acc {
            rep: a.rep,
            cnt: a.cnt + d.cnt as u64,
            sum_qty: a.sum_qty + d.qty as i128,
            sum_price: a.sum_price + d.price as i128,
            sum_disc: a.sum_disc + d.disc as i128,
            small: a.small,
            sum_dp: a.sum_dp + d.dp as i128,
            mass_dp: a.mass_dp,
            over_dp: a.over_dp,
            sum_ch: a.sum_ch + d.ch as i128,
            mass_ch: a.mass_ch,
            over_ch: a.over_ch,
        };
        proof {
            assert(b == eff(a, d));
        }
        slots[s] = b;
        blk[s] = new_delta();
        s = s + 1;
    }
    proof {
        assert(slots@ =~= view_table(s0, k0, ng as int));
    }
}

/// A table uses at most its slots.
pub proof fn lemma_table_ng(pd: int, c: Cols, lo: int, i: int, slots: Seq<Acc>, ng: int)
    requires table_ok(pd, c, lo, i, slots, ng),
    ensures 0 <= ng <= slots.len(),
{
}

/// After a flush the slots are the view: they keep the index and the small mode.
pub proof fn lemma_after_flush(c: Cols, s0: Seq<Acc>, k0: Seq<Delta>, s1: Seq<Acc>, ng: int, idx: Seq<usize>)
    requires
        s1 == view_table(s0, k0, ng),
        0 <= ng <= s0.len(),
        idx_ok(c, s0, ng, idx),
        mode_ok(s0, ng, true),
    ensures
        idx_ok(c, s1, ng, idx),
        mode_ok(s1, ng, true),
        s1.len() == s0.len(),
{
    lemma_view_reps(s0, k0, ng);
    lemma_idx_same_reps(c, s0, s1, ng, idx);
    assert forall|t: int| 0 <= t < ng implies (#[trigger] s1[t]).small == true by {
        assert(s0[t].small);
    }
}

/// Scans rows `[start, hi)` of the range that began at `lo` with the fast path, in blocks of `BLOCK` rows. Returns
/// the first row not scanned: `hi`, or a qualifying row that needs the general scan.
pub fn scan_fast(
    c: &Cols,
    lo: usize,
    start: usize,
    hi: usize,
    limit: i32,
    Ghost(pd): Ghost<int>,
    slots: &mut Vec<Acc>,
    ng: usize,
    idx: &Vec<usize>,
    blk: &mut Vec<Delta>,
) -> (at: usize)
    requires
        cols_wf(*c),
        lo <= start <= hi <= c.n,
        limit as int == pd + 10957,
        ng <= old(slots)@.len(),
        ng <= old(blk)@.len(),
        table_ok(pd, *c, lo as int, start as int, old(slots)@, ng as int),
        idx_ok(*c, old(slots)@, ng as int, idx@),
        mode_ok(old(slots)@, ng as int, true),
        blk_zero(old(blk)@),
    ensures
        start <= at <= hi,
        final(slots)@.len() == old(slots)@.len(),
        final(blk)@.len() == old(blk)@.len(),
        table_ok(pd, *c, lo as int, at as int, final(slots)@, ng as int),
        idx_ok(*c, final(slots)@, ng as int, idx@),
        mode_ok(final(slots)@, ng as int, true),
        blk_zero(final(blk)@),
    no_unwind
{
    hide(table_ok);
    hide(idx_ok);
    hide(mode_ok);
    hide(view_table);
    let sp = span_of(c, lo, hi);
    let len = hi - lo;
    let mut j = start - lo;
    proof {
        assert(sp.rf_offsets@.len() == len + 1 && sp.ls_offsets@.len() == len + 1);
    }
    while j < len
        invariant
            cols_wf(*c),
            lo <= start <= hi <= c.n,
            len == hi - lo,
            start - lo <= j <= len,
            span_ok(*c, lo as int, hi as int, sp),
            sp.rf_offsets@.len() == len + 1 && sp.ls_offsets@.len() == len + 1,
            limit as int == pd + 10957,
            ng <= slots@.len(),
            ng <= blk@.len(),
            slots@.len() == old(slots)@.len(),
            blk@.len() == old(blk)@.len(),
            table_ok(pd, *c, lo as int, lo + j, slots@, ng as int),
            idx_ok(*c, slots@, ng as int, idx@),
            mode_ok(slots@, ng as int, true),
            blk_zero(blk@),
        decreases len - j,
    {
        let bend = if len - j > BLOCK { j + BLOCK } else { len };
        let (j2, stopped) = block_rows(c, &sp, lo, hi, j, bend, limit, Ghost(pd), slots, ng, idx, blk);
        let ghost s0 = slots@;
        let ghost k0 = blk@;
        flush(slots, blk, ng);
        proof {
            lemma_after_flush(*c, s0, k0, slots@, ng as int, idx@);
        }
        j = j2;
        if stopped {
            return lo + j;
        }
    }
    hi
}

/// Scans rows `[lo, hi)` in small mode: the fast path, with each row it does not take handed to the general scan
/// (one row at a time), until the range ends or the general scan stops (`Full`, `RowOverflow`, `NeedExact`).
pub fn scan_mixed(
    c: &Cols,
    lo: usize,
    hi: usize,
    limit: i32,
    Ghost(pd): Ghost<int>,
    slots: &mut Vec<Acc>,
    ng: &mut usize,
    idx: &mut Vec<usize>,
    blk: &mut Vec<Delta>,
) -> (r: (Stop, usize))
    requires
        cols_wf(*c),
        lo <= hi <= c.n,
        limit as int == pd + 10957,
        *old(ng) == 0,
        old(slots)@.len() <= old(blk)@.len(),
        table_ok(pd, *c, lo as int, lo as int, old(slots)@, 0),
        idx_ok(*c, old(slots)@, 0, old(idx)@),
        blk_zero(old(blk)@),
    ensures
        final(slots)@.len() == old(slots)@.len(),
        lo <= r.1 <= hi,
        table_ok(pd, *c, lo as int, r.1 as int, final(slots)@, *final(ng) as int),
        idx_ok(*c, final(slots)@, *final(ng) as int, final(idx)@),
        mode_ok(final(slots)@, *final(ng) as int, true),
        r.0 == Stop::NeedExact ==> r.1 < hi,
        r.0 == Stop::Done ==> r.1 == hi,
        r.0 == Stop::Full ==> r.1 < hi && *final(ng) == final(slots)@.len(),
        r.0 == Stop::RowOverflow ==> r.1 < hi && q1_qual(pd, crow(*c, r.1 as int))
            && !crate::link::expr::fits_i128(charge(crow(*c, r.1 as int))),
    no_unwind
{
    hide(table_ok);
    hide(idx_ok);
    hide(mode_ok);
    proof {
        assert(mode_ok(slots@, 0, true)) by {
            reveal(mode_ok);
        }
    }
    let mut pos = lo;
    while pos < hi
        invariant
            cols_wf(*c),
            lo <= pos <= hi <= c.n,
            limit as int == pd + 10957,
            slots@.len() == old(slots)@.len(),
            slots@.len() <= blk@.len(),
            *ng <= slots@.len(),
            table_ok(pd, *c, lo as int, pos as int, slots@, *ng as int),
            idx_ok(*c, slots@, *ng as int, idx@),
            mode_ok(slots@, *ng as int, true),
            blk_zero(blk@),
        decreases hi - pos,
    {
        let p2 = scan_fast(c, lo, pos, hi, limit, Ghost(pd), slots, *ng, idx, blk);
        if p2 == hi {
            return (Stop::Done, hi);
        }
        let (st, a) = scan_range(c, lo, p2, p2 + 1, limit, Ghost(pd), true, slots, ng, idx);
        proof {
            lemma_table_ng(pd, *c, lo as int, a as int, slots@, *ng as int);
        }
        match st {
            Stop::Done => {
                pos = a;
            },
            _ => {
                return (st, a);
            },
        }
    }
    (Stop::Done, hi)
}

} // verus!
