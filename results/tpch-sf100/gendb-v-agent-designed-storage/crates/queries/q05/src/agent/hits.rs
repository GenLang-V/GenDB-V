//! Deferred accumulation for the live-order kernel. Phase 1 of a batch writes the stored lineitem rows that take
//! part in a group into a hit list without branching (`hb[x]` the row, `hg[x]` its group), and `drain` later adds
//! the listed rows to the accumulators in one branch-free pass, so the cache misses of their price and discount
//! overlap.
//!
//! Invariant (`hits_ok`): the listed rows strictly increase inside `[lo, hi)`, each takes part in exactly its group
//! (`hit_in`), and every other row of `[lo, hi)` takes part in none (`quiet`). Draining such a list moves the
//! accumulators from rows `[ja, lo)` to rows `[ja, hi)`.
use vstd::prelude::*;
use crate::agent::q5spec::*;
use crate::agent::chain::*;
use crate::agent::common::forview::*;
use crate::agent::common::sums::*;
use crate::agent::kernel::*;

verus! {

/// Stored lineitem row `j` takes part in no group.
pub open spec fn quiet(t: ScanCtx, j: int) -> bool {
    forall|gi: int| 0 <= gi < t.gnames@.len() ==>
        #[trigger] line_mult(t.rs@, t.prm@, gkey(t.gnames@, gi), t.lrows@[j]) == 0
}

/// Stored lineitem row `j` takes part once in group `g` and in no other group.
pub open spec fn hit_in(t: ScanCtx, j: int, g: int) -> bool {
    &&& 0 <= g < t.gnames@.len()
    &&& forall|gi: int| 0 <= gi < t.gnames@.len() ==>
        #[trigger] line_mult(t.rs@, t.prm@, gkey(t.gnames@, gi), t.lrows@[j]) == if gi == g { 1int } else { 0int }
}

/// Where the quiet rows before list entry `x` begin: `lo` for the first entry, else after the previous entry.
pub open spec fn hgap(hb: Seq<usize>, lo: int, x: int) -> int {
    if x == 0 { lo } else { hb[x - 1] as int + 1 }
}

/// The first `h` entries of `hb`/`hg` list exactly the rows of `[lo, hi)` that take part in a group.
pub open spec fn hits_ok(t: ScanCtx, hb: Seq<usize>, hg: Seq<usize>, h: int, lo: int, hi: int) -> bool {
    &&& 0 <= h <= hb.len() && h <= hg.len()
    &&& 0 <= lo <= hi <= t.n_l
    &&& lo <= hgap(hb, lo, h) <= hi
    &&& forall|x: int| 0 <= x < h ==> hgap(hb, lo, x) <= #[trigger] hb[x] < hi
    &&& forall|x: int| 0 <= x < h ==> hit_in(t, #[trigger] hb[x] as int, hg[x] as int)
    &&& forall|x: int, y: int| 0 <= x < h && hgap(hb, lo, x) <= y < #[trigger] hb[x] ==> #[trigger] quiet(t, y)
    &&& forall|y: int| hgap(hb, lo, h) <= y < hi ==> #[trigger] quiet(t, y)
}

/// The empty list over an empty range.
pub proof fn lemma_hits_empty(t: ScanCtx, hb: Seq<usize>, hg: Seq<usize>, lo: int)
    requires 0 <= lo <= t.n_l,
    ensures hits_ok(t, hb, hg, 0, lo, lo),
{
}

/// Quiet rows `[hi, hi2)` extend the list's range.
pub proof fn lemma_hits_extend(t: ScanCtx, hb: Seq<usize>, hg: Seq<usize>, h: int, lo: int, hi: int, hi2: int)
    requires
        hits_ok(t, hb, hg, h, lo, hi), hi <= hi2 <= t.n_l,
        forall|y: int| hi <= y < hi2 ==> #[trigger] quiet(t, y),
    ensures hits_ok(t, hb, hg, h, lo, hi2),
{
    assert forall|y: int| hgap(hb, lo, h) <= y < hi2 implies #[trigger] quiet(t, y) by {
        if y < hi {
            assert(hgap(hb, lo, h) <= y < hi);
        }
    }
}

/// One step of phase 1: row `j` is written at entry `h`; the list grows when the row is a hit.
pub proof fn lemma_hits_push(t: ScanCtx, hb0: Seq<usize>, hg0: Seq<usize>, hb1: Seq<usize>, hg1: Seq<usize>,
    h: int, lo: int, j: int, g: usize, hit: bool)
    requires
        hits_ok(t, hb0, hg0, h, lo, j), j < t.n_l, h < hb0.len(), h < hg0.len(),
        hb1 == hb0.update(h, j as usize), hg1 == hg0.update(h, g),
        hit ==> hit_in(t, j, g as int),
        !hit ==> quiet(t, j),
    ensures
        hits_ok(t, hb1, hg1, if hit { h + 1 } else { h }, lo, j + 1),
{
    assert forall|x: int| 0 <= x <= h implies #[trigger] hgap(hb1, lo, x) == hgap(hb0, lo, x) by {
        if x > 0 {
            assert(hb1[x - 1] == hb0[x - 1]);
        }
    }
    let h2 = if hit { h + 1 } else { h };
    assert(hb1[h] as int == j);
    assert forall|x: int| 0 <= x < h2 implies hgap(hb1, lo, x) <= #[trigger] hb1[x] < j + 1 by {
        if x < h {
            assert(hb1[x] == hb0[x]);
        } else {
            assert(hgap(hb0, lo, h) <= j);
        }
    }
    assert forall|x: int| 0 <= x < h2 implies hit_in(t, #[trigger] hb1[x] as int, hg1[x] as int) by {
        if x < h {
            assert(hb1[x] == hb0[x] && hg1[x] == hg0[x]);
        } else {
            assert(hg1[h] == g);
        }
    }
    assert forall|x: int, y: int| 0 <= x < h2 && hgap(hb1, lo, x) <= y < #[trigger] hb1[x]
        implies #[trigger] quiet(t, y) by {
        if x < h {
            assert(hb1[x] == hb0[x]);
            assert(hgap(hb0, lo, x) <= y < hb0[x]);
        } else {
            assert(hgap(hb0, lo, h) <= y < j);
        }
    }
    if hit {
        assert(hgap(hb1, lo, h + 1) == j + 1);
    } else {
        assert forall|y: int| hgap(hb1, lo, h) <= y < j + 1 implies #[trigger] quiet(t, y) by {
            if y < j {
                assert(hgap(hb0, lo, h) <= y < j);
            }
        }
    }
}

/// Quiet rows `[x, y)` leave every accumulator as it is.
pub proof fn lemma_quiet_lines(t: ScanCtx, ja: int, x: int, y: int,
    cnt: Seq<usize>, sum: Seq<i128>, abs: Seq<u128>, ovf: Seq<bool>)
    requires
        t.wf(), 0 <= ja <= x <= y <= t.n_l,
        forall|j: int| x <= j < y ==> #[trigger] quiet(t, j),
        cnt.len() == t.gnames@.len() && sum.len() == t.gnames@.len() && abs.len() == t.gnames@.len() && ovf.len() == t.gnames@.len(),
        forall|gi: int| 0 <= gi < t.gnames@.len() ==> #[trigger] t.acc_ok(gi, ja, x, cnt[gi], sum[gi], abs[gi], ovf[gi]),
    ensures
        forall|gi: int| 0 <= gi < t.gnames@.len() ==> #[trigger] t.acc_ok(gi, ja, y, cnt[gi], sum[gi], abs[gi], ovf[gi]),
{
    assert forall|gi: int| 0 <= gi < t.gnames@.len() implies #[trigger] t.acc_ok(gi, ja, y, cnt[gi], sum[gi], abs[gi], ovf[gi]) by {
        assert(t.acc_ok(gi, ja, x, cnt[gi], sum[gi], abs[gi], ovf[gi]));
        assert forall|m: int| #[trigger] t.lsum(gi, m, ja, y) == t.lsum(gi, m, ja, x) by {
            let f = contrib_fn(t.rs@, t.prm@, gkey(t.gnames@, gi), m);
            assert forall|j: int| x <= j < y implies f(#[trigger] t.lrows@[j]) == 0 by {
                assert(quiet(t, j));
                assert(line_mult(t.rs@, t.prm@, gkey(t.gnames@, gi), t.lrows@[j]) == 0);
            }
            lemma_sum_range_zero(t.lrows@, f, x, y);
            lemma_sum_range_split(t.lrows@, f, ja, x, y);
        }
        assert(t.lsum(gi, 0, ja, y) == t.lsum(gi, 0, ja, x));
        assert(t.lsum(gi, 1, ja, y) == t.lsum(gi, 1, ja, x));
        assert(t.lsum(gi, 2, ja, y) == t.lsum(gi, 2, ja, x));
    }
}

/// `x / d.bs` by a shift (the block size is a power of two).
#[inline(always)]
pub fn shr_div(d: Div, x: usize) -> (r: usize)
    requires d.ok(), d.p2,
    ensures r == x / d.bs,
    no_unwind
{
    let xx = x as u64;
    let ss = d.sh as u64;
    proof {
        vstd::bits::lemma_u64_shr_is_div(xx, ss);
    }
    let r = xx >> ss;
    proof {
        vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(x as int, 1, d.bs as int);
        assert(x as int / 1 == x as int);
    }
    r as usize
}

/// Add hit row `j` of group `g` (price code value `ep`, discount `dc`) to the accumulators.
#[inline(always)]
pub fn acc_val(Ghost(t): Ghost<ScanCtx>, cnt: &mut Vec<usize>, sum: &mut Vec<i128>, abs: &mut Vec<u128>, ovf: &mut Vec<bool>,
    Ghost(ja): Ghost<int>, j: usize, g: usize, ep: i64, dc: i64)
    requires
        t.wf(), 0 <= ja <= j < t.n_l,
        old(cnt)@.len() == t.gnames@.len() && old(sum)@.len() == t.gnames@.len()
            && old(abs)@.len() == t.gnames@.len() && old(ovf)@.len() == t.gnames@.len(),
        forall|gi: int| 0 <= gi < t.gnames@.len() ==>
            #[trigger] t.acc_ok(gi, ja, j as int, old(cnt)@[gi], old(sum)@[gi], old(abs)@[gi], old(ovf)@[gi]),
        hit_in(t, j as int, g as int),
        ep == fv32(t.le_c@, t.le_b@, t.ldiv.bs as int, j as int),
        dc == fv8(t.ld_c@, t.ld_b@, t.ldiv.bs as int, j as int),
    ensures
        final(cnt)@.len() == t.gnames@.len() && final(sum)@.len() == t.gnames@.len()
            && final(abs)@.len() == t.gnames@.len() && final(ovf)@.len() == t.gnames@.len(),
        forall|gi: int| 0 <= gi < t.gnames@.len() ==>
            #[trigger] t.acc_ok(gi, ja, j as int + 1, final(cnt)@[gi], final(sum)@[gi], final(abs)@[gi], final(ovf)@[gi]),
    no_unwind
{
    let ghost rs = t.rs@;
    let ghost prm = t.prm@;
    let ghost gn = t.gnames@;
    let ghost ng = gn.len();
    let ghost l = t.lrows@[j as int];
    let ghost oc = cnt@;
    let ghost osu = sum@;
    let ghost oa = abs@;
    let ghost oo = ovf@;
    proof {
        lemma_weights(&t, j as int, ep as int, dc as int);
    }
    let (v, a) = revenue(ep, dc);
    proof {
        assert(t.acc_ok(g as int, ja, j as int, oc[g as int], osu[g as int], oa[g as int], oo[g as int]));
    }
    if !ovf[g] {
        if abs[g] <= (i128::MAX as u128) - a {
            abs[g] = abs[g] + a;
            sum[g] = sum[g] + v;
            cnt[g] = cnt[g] + 1;
        } else {
            ovf[g] = true;
        }
    }
    proof {
        assert forall|gi: int| 0 <= gi < ng implies
            #[trigger] t.acc_ok(gi, ja, j as int + 1, cnt@[gi], sum@[gi], abs@[gi], ovf@[gi]) by {
            let dm = if gi == g { 1int } else { 0int };
            assert(line_mult(rs, prm, gkey(gn, gi), l) == dm);
            lemma_acc_step(&t, gi, ja, j as int, dm);
            assert(t.lsum(gi, 0, ja, j as int + 1) == t.lsum(gi, 0, ja, j as int) + dm * wsel(0, l));
            assert(t.lsum(gi, 1, ja, j as int + 1) == t.lsum(gi, 1, ja, j as int) + dm * wsel(1, l));
            assert(t.lsum(gi, 2, ja, j as int + 1) == t.lsum(gi, 2, ja, j as int) + dm * wsel(2, l));
            assert(t.acc_ok(gi, ja, j as int, oc[gi], osu[gi], oa[gi], oo[gi]));
        }
    }
}

/// Add the listed hit rows to the accumulators: from rows `[ja, lo)` to rows `[ja, hi)`.
#[inline(never)]
pub fn drain(Ghost(t): Ghost<ScanCtx>, le_c: &[u32], le_b: &[i64], ld_c: &[u8], ld_b: &[i64], ldiv: Div,
    hb: &Vec<usize>, hg: &Vec<usize>, h: usize, Ghost(ja): Ghost<int>, Ghost(lo): Ghost<int>, Ghost(hi): Ghost<int>,
    cnt: &mut Vec<usize>, sum: &mut Vec<i128>, abs: &mut Vec<u128>, ovf: &mut Vec<bool>)
    requires
        t.wf(), le_c == t.le_c, le_b == t.le_b, ld_c == t.ld_c, ld_b == t.ld_b, ldiv == t.ldiv, ldiv.p2,
        hits_ok(t, hb@, hg@, h as int, lo, hi), 0 <= ja <= lo,
        old(cnt)@.len() == t.gnames@.len() && old(sum)@.len() == t.gnames@.len()
            && old(abs)@.len() == t.gnames@.len() && old(ovf)@.len() == t.gnames@.len(),
        forall|gi: int| 0 <= gi < t.gnames@.len() ==>
            #[trigger] t.acc_ok(gi, ja, lo, old(cnt)@[gi], old(sum)@[gi], old(abs)@[gi], old(ovf)@[gi]),
    ensures
        final(cnt)@.len() == t.gnames@.len() && final(sum)@.len() == t.gnames@.len()
            && final(abs)@.len() == t.gnames@.len() && final(ovf)@.len() == t.gnames@.len(),
        forall|gi: int| 0 <= gi < t.gnames@.len() ==>
            #[trigger] t.acc_ok(gi, ja, hi, final(cnt)@[gi], final(sum)@[gi], final(abs)@[gi], final(ovf)@[gi]),
    no_unwind
{
    let ghost bs = ldiv.bs as int;
    let mut i: usize = 0;
    while i < h
        invariant
            t.wf(), le_c == t.le_c, le_b == t.le_b, ld_c == t.ld_c, ld_b == t.ld_b, ldiv == t.ldiv, ldiv.p2,
            bs == ldiv.bs as int,
            hits_ok(t, hb@, hg@, h as int, lo, hi), 0 <= ja <= lo, i <= h,
            lo <= hgap(hb@, lo, i as int) <= hi,
            cnt@.len() == t.gnames@.len() && sum@.len() == t.gnames@.len()
                && abs@.len() == t.gnames@.len() && ovf@.len() == t.gnames@.len(),
            forall|gi: int| 0 <= gi < t.gnames@.len() ==>
                #[trigger] t.acc_ok(gi, ja, hgap(hb@, lo, i as int), cnt@[gi], sum@[gi], abs@[gi], ovf@[gi]),
        decreases h - i,
    {
        let j = hb[i];
        let g = hg[i];
        proof {
            let x = hgap(hb@, lo, i as int);
            assert(x <= hb@[i as int] < hi);
            assert forall|y: int| x <= y < j implies #[trigger] quiet(t, y) by {
                assert(hgap(hb@, lo, i as int) <= y < hb@[i as int]);
            }
            lemma_quiet_lines(t, ja, x, j as int, cnt@, sum@, abs@, ovf@);
            assert(hit_in(t, hb@[i as int] as int, hg@[i as int] as int));
            lemma_block_index(j as int, bs, le_b@.len() as int);
            lemma_block_index(j as int, bs, ld_b@.len() as int);
            assert(i64::MIN <= fv32(t.le_c@, t.le_b@, bs, j as int) <= i64::MAX);
            assert(i64::MIN <= fv8(t.ld_c@, t.ld_b@, bs, j as int) <= i64::MAX);
        }
        let blk = shr_div(ldiv, j);
        let ep = le_c[j] as i64 + le_b[blk];
        let dc = ld_c[j] as i64 + ld_b[blk];
        acc_val(Ghost(t), cnt, sum, abs, ovf, Ghost(ja), j, g, ep, dc);
        proof {
            assert(hgap(hb@, lo, i as int + 1) == j as int + 1);
        }
        i = i + 1;
    }
    proof {
        let x = hgap(hb@, lo, h as int);
        if h > 0 {
            assert(hb@[h - 1] < hi);
        }
        lemma_quiet_lines(t, ja, x, hi, cnt@, sum@, abs@, ovf@);
    }
}

} // verus!
