//! The scan model over positions of a row order `p` (the country-code order of storage `cust_phoneidx`): what
//! the fast path computes per range of positions, and how it equals the row-order accumulators of `model`.
//! - kernel accumulators (no group test; a run of the order has one group): `tpc`/`tps` count and sum the
//!   positive balances; `pband` lists the balances of at least `bl` of the rows without orders; `pcgt`/`psgt`
//!   count and sum the balances above a threshold of the rows without orders, which are those of `pband` above it
//!   when the threshold is at least `bl` (`lemma_band`);
//!   `cnt_gt`/`sum_gt` count and sum the elements of a list above a threshold;
//! - position versions of the model's accumulators: `pcnta`/`psuma` (pass A), `pcntb`/`psumb` (pass B);
//! - `lemma_run_a`/`lemma_run_b`: over positions whose rows all have group `g`, the position accumulators are the
//!   kernel accumulators (`g` listed) or zero (`g == NG`);
//! - `lemma_reindex_*`: over a bijection of `[0, n)`, the position accumulators over `[0, n)` are the row-order
//!   accumulators over `[0, n)` (`common::perm::lemma_sum_perm`).
use vstd::prelude::*;
use crate::spec::value::*;
use super::model::*;
use super::common::perm::*;
use crate::spec::numeric::abs;

verus! {

// ------------------------------------------------------------------------------------------------ kernel model

/// The balance of the row at position `j`.
pub open spec fn pa(v: Cv, p: Seq<u32>, j: int) -> int {
    racct(v, p[j] as int)
}

/// Positions of `[lo, hi)` with a positive balance.
pub open spec fn tpc(v: Cv, p: Seq<u32>, lo: int, hi: int) -> nat
    decreases hi - lo,
{
    if hi <= lo { 0 } else { tpc(v, p, lo, hi - 1) + if pa(v, p, hi - 1) > 0 { 1nat } else { 0nat } }
}

/// Sum of their balances.
pub open spec fn tps(v: Cv, p: Seq<u32>, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { tps(v, p, lo, hi - 1) + if pa(v, p, hi - 1) > 0 { pa(v, p, hi - 1) } else { 0 } }
}

/// The balances of at least `bl` of the positions of `[lo, hi)` whose row has no orders, in position order (the
/// candidates the kernel lists: below `bl` none can be above an average of at least `bl`).
pub open spec fn pband(v: Cv, p: Seq<u32>, lo: int, hi: int, bl: int) -> Seq<int>
    decreases hi - lo,
{
    if hi <= lo {
        Seq::empty()
    } else if rnoord(v, p[hi - 1] as int) && pa(v, p, hi - 1) >= bl {
        pband(v, p, lo, hi - 1, bl).push(pa(v, p, hi - 1))
    } else {
        pband(v, p, lo, hi - 1, bl)
    }
}

/// Positions of `[lo, hi)` whose row has no orders and a balance above `thr`.
pub open spec fn pcgt(v: Cv, p: Seq<u32>, lo: int, hi: int, thr: int) -> nat
    decreases hi - lo,
{
    if hi <= lo { 0 } else { pcgt(v, p, lo, hi - 1, thr) + if rnoord(v, p[hi - 1] as int) && pa(v, p, hi - 1) > thr { 1nat } else { 0nat } }
}

/// Sum of their balances.
pub open spec fn psgt(v: Cv, p: Seq<u32>, lo: int, hi: int, thr: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { psgt(v, p, lo, hi - 1, thr) + if rnoord(v, p[hi - 1] as int) && pa(v, p, hi - 1) > thr { pa(v, p, hi - 1) } else { 0 } }
}

/// Elements of `s` above `thr`.
pub open spec fn cnt_gt(s: Seq<int>, thr: int) -> nat
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { cnt_gt(s.drop_last(), thr) + if s.last() > thr { 1nat } else { 0nat } }
}

/// Sum of the elements of `s` above `thr`.
pub open spec fn sum_gt(s: Seq<int>, thr: int) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { sum_gt(s.drop_last(), thr) + if s.last() > thr { s.last() } else { 0 } }
}

/// The kernel accumulators split at `mid`.
pub proof fn lemma_t_split(v: Cv, p: Seq<u32>, lo: int, mid: int, hi: int, bl: int)
    requires lo <= mid <= hi,
    ensures
        tpc(v, p, lo, hi) == tpc(v, p, lo, mid) + tpc(v, p, mid, hi),
        tps(v, p, lo, hi) == tps(v, p, lo, mid) + tps(v, p, mid, hi),
        pband(v, p, lo, hi, bl) == pband(v, p, lo, mid, bl) + pband(v, p, mid, hi, bl),
    decreases hi - mid,
{
    if hi > mid {
        lemma_t_split(v, p, lo, mid, hi - 1, bl);
        let (a, b) = (pband(v, p, lo, mid, bl), pband(v, p, mid, hi - 1, bl));
        if rnoord(v, p[hi - 1] as int) && pa(v, p, hi - 1) >= bl {
            assert((a + b).push(pa(v, p, hi - 1)) =~= a + b.push(pa(v, p, hi - 1)));
        }
    } else {
        assert(pband(v, p, lo, hi, bl) =~= pband(v, p, lo, mid, bl) + Seq::<int>::empty());
    }
}

/// The candidates above `thr` split at `mid`.
pub proof fn lemma_gt_split(v: Cv, p: Seq<u32>, lo: int, mid: int, hi: int, thr: int)
    requires lo <= mid <= hi,
    ensures
        pcgt(v, p, lo, hi, thr) == pcgt(v, p, lo, mid, thr) + pcgt(v, p, mid, hi, thr),
        psgt(v, p, lo, hi, thr) == psgt(v, p, lo, mid, thr) + psgt(v, p, mid, hi, thr),
    decreases hi - mid,
{
    if hi > mid {
        lemma_gt_split(v, p, lo, mid, hi - 1, thr);
    }
}

/// With a threshold of at least `bl`, the candidates above it are the listed balances above it.
pub proof fn lemma_band(v: Cv, p: Seq<u32>, lo: int, hi: int, bl: int, thr: int)
    requires bl <= thr,
    ensures
        pcgt(v, p, lo, hi, thr) == cnt_gt(pband(v, p, lo, hi, bl), thr),
        psgt(v, p, lo, hi, thr) == sum_gt(pband(v, p, lo, hi, bl), thr),
    decreases hi - lo,
{
    if hi > lo {
        lemma_band(v, p, lo, hi - 1, bl, thr);
        if rnoord(v, p[hi - 1] as int) && pa(v, p, hi - 1) >= bl {
            lemma_gt_push(pband(v, p, lo, hi - 1, bl), pa(v, p, hi - 1), thr);
        }
    }
}

/// One more element: `cnt_gt`/`sum_gt` of `s.push(x)`.
pub proof fn lemma_gt_push(s: Seq<int>, x: int, thr: int)
    ensures
        cnt_gt(s.push(x), thr) == cnt_gt(s, thr) + if x > thr { 1nat } else { 0nat },
        sum_gt(s.push(x), thr) == sum_gt(s, thr) + if x > thr { x } else { 0 },
{
    assert(s.push(x).drop_last() =~= s);
}

/// `cnt_gt`/`sum_gt` add over a concatenation.
pub proof fn lemma_gt_concat(a: Seq<int>, b: Seq<int>, thr: int)
    ensures
        cnt_gt(a + b, thr) == cnt_gt(a, thr) + cnt_gt(b, thr),
        sum_gt(a + b, thr) == sum_gt(a, thr) + sum_gt(b, thr),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        lemma_gt_concat(a, b.drop_last(), thr);
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
    }
}

/// The prefix `s[0 .. q + 1]` adds element `q`.
pub proof fn lemma_gt_prefix(s: Seq<int>, q: int, thr: int)
    requires 0 <= q < s.len(),
    ensures
        cnt_gt(s.subrange(0, q + 1), thr) == cnt_gt(s.subrange(0, q), thr) + if s[q] > thr { 1nat } else { 0nat },
        sum_gt(s.subrange(0, q + 1), thr) == sum_gt(s.subrange(0, q), thr) + if s[q] > thr { s[q] } else { 0 },
{
    assert(s.subrange(0, q + 1) =~= s.subrange(0, q).push(s[q]));
    lemma_gt_push(s.subrange(0, q), s[q], thr);
}

/// Bounds of `cnt_gt`/`sum_gt` over elements below `acct_bound()` in magnitude.
pub proof fn lemma_gt_bound(s: Seq<int>, thr: int)
    requires forall|q: int| 0 <= q < s.len() ==> -acct_bound() < #[trigger] s[q] < acct_bound(),
    ensures
        cnt_gt(s, thr) <= s.len(),
        abs(sum_gt(s, thr)) <= cnt_gt(s, thr) * acct_bound(),
    decreases s.len(),
{
    if s.len() > 0 {
        let t = s.drop_last();
        assert forall|q: int| 0 <= q < t.len() implies -acct_bound() < #[trigger] t[q] < acct_bound() by {
            assert(t[q] == s[q]);
        }
        lemma_gt_bound(t, thr);
        assert(-acct_bound() < s[s.len() - 1] < acct_bound());
    }
}

/// The rows at positions `[lo, hi)` are rows of the views.
pub open spec fn rows_in(v: Cv, p: Seq<u32>, lo: int, hi: int) -> bool {
    &&& 0 <= lo
    &&& hi <= p.len()
    &&& forall|j: int| lo <= j < hi ==> #[trigger] p[j] < v.n
}

/// Bounds of the kernel accumulators.
pub proof fn lemma_t_bound(v: Cv, p: Seq<u32>, lo: int, hi: int, bl: int)
    requires cv_ok(v), rows_in(v, p, lo, hi), lo <= hi,
    ensures
        tpc(v, p, lo, hi) <= hi - lo,
        abs(tps(v, p, lo, hi)) <= tpc(v, p, lo, hi) * acct_bound(),
        pband(v, p, lo, hi, bl).len() <= hi - lo,
        forall|q: int| 0 <= q < pband(v, p, lo, hi, bl).len() ==>
            -acct_bound() < #[trigger] pband(v, p, lo, hi, bl)[q] < acct_bound(),
    decreases hi - lo,
{
    if hi > lo {
        lemma_t_bound(v, p, lo, hi - 1, bl);
        assert(p[hi - 1] < v.n);
        assert(-acct_bound() < racct(v, p[hi - 1] as int) < acct_bound());
    }
}

/// Bounds of the candidates above a threshold.
pub proof fn lemma_gt_pbound(v: Cv, p: Seq<u32>, lo: int, hi: int, thr: int)
    requires cv_ok(v), rows_in(v, p, lo, hi), lo <= hi,
    ensures
        pcgt(v, p, lo, hi, thr) <= hi - lo,
        abs(psgt(v, p, lo, hi, thr)) <= pcgt(v, p, lo, hi, thr) * acct_bound(),
    decreases hi - lo,
{
    if hi > lo {
        lemma_gt_pbound(v, p, lo, hi - 1, thr);
        assert(p[hi - 1] < v.n);
        assert(-acct_bound() < racct(v, p[hi - 1] as int) < acct_bound());
    }
}

// ------------------------------------------------------------------------------------------------ position model

/// Positions of `[lo, hi)` whose row enters the subquery.
pub open spec fn pcnta(v: Cv, p: Seq<u32>, lo: int, hi: int) -> nat
    decreases hi - lo,
{
    if hi <= lo { 0 } else { pcnta(v, p, lo, hi - 1) + if qa(v, p[hi - 1] as int) { 1nat } else { 0nat } }
}

/// Sum of their balances.
pub open spec fn psuma(v: Cv, p: Seq<u32>, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { psuma(v, p, lo, hi - 1) + if qa(v, p[hi - 1] as int) { pa(v, p, hi - 1) } else { 0 } }
}

/// Row at position `j` is a result row of group `k`.
pub open spec fn qbk(v: Cv, avg: Val, k: int, p: Seq<u32>, j: int) -> bool {
    qb(v, avg, p[j] as int) && rgid(v, p[j] as int) == k
}

/// Positions of `[lo, hi)` whose row is a result row of group `k`.
pub open spec fn pcntb(v: Cv, avg: Val, k: int, p: Seq<u32>, lo: int, hi: int) -> nat
    decreases hi - lo,
{
    if hi <= lo { 0 } else { pcntb(v, avg, k, p, lo, hi - 1) + if qbk(v, avg, k, p, hi - 1) { 1nat } else { 0nat } }
}

/// Sum of their balances.
pub open spec fn psumb(v: Cv, avg: Val, k: int, p: Seq<u32>, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { psumb(v, avg, k, p, lo, hi - 1) + if qbk(v, avg, k, p, hi - 1) { pa(v, p, hi - 1) } else { 0 } }
}

/// The position accumulators split at `mid`.
pub proof fn lemma_p_split(v: Cv, avg: Val, k: int, p: Seq<u32>, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures
        pcnta(v, p, lo, hi) == pcnta(v, p, lo, mid) + pcnta(v, p, mid, hi),
        psuma(v, p, lo, hi) == psuma(v, p, lo, mid) + psuma(v, p, mid, hi),
        pcntb(v, avg, k, p, lo, hi) == pcntb(v, avg, k, p, lo, mid) + pcntb(v, avg, k, p, mid, hi),
        psumb(v, avg, k, p, lo, hi) == psumb(v, avg, k, p, lo, mid) + psumb(v, avg, k, p, mid, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_p_split(v, avg, k, p, lo, mid, hi - 1);
    }
}

/// Bounds of the pass A position accumulators.
pub proof fn lemma_pa_bound(v: Cv, p: Seq<u32>, lo: int, hi: int)
    requires cv_ok(v), rows_in(v, p, lo, hi), lo <= hi,
    ensures
        pcnta(v, p, lo, hi) <= hi - lo,
        abs(psuma(v, p, lo, hi)) <= pcnta(v, p, lo, hi) * acct_bound(),
    decreases hi - lo,
{
    if hi > lo {
        lemma_pa_bound(v, p, lo, hi - 1);
        assert(p[hi - 1] < v.n);
        assert(-acct_bound() < racct(v, p[hi - 1] as int) < acct_bound());
    }
}

/// Bounds of the pass B position accumulators.
pub proof fn lemma_pb_bound(v: Cv, avg: Val, k: int, p: Seq<u32>, lo: int, hi: int)
    requires cv_ok(v), rows_in(v, p, lo, hi), lo <= hi,
    ensures
        pcntb(v, avg, k, p, lo, hi) <= hi - lo,
        abs(psumb(v, avg, k, p, lo, hi)) <= pcntb(v, avg, k, p, lo, hi) * acct_bound(),
    decreases hi - lo,
{
    if hi > lo {
        lemma_pb_bound(v, avg, k, p, lo, hi - 1);
        assert(p[hi - 1] < v.n);
        assert(-acct_bound() < racct(v, p[hi - 1] as int) < acct_bound());
    }
}

/// Every row at positions `[lo, hi)` has group `g`.
pub open spec fn one_group(v: Cv, p: Seq<u32>, lo: int, hi: int, g: int) -> bool {
    forall|j: int| lo <= j < hi ==> #[trigger] rgid(v, p[j] as int) == g
}

/// Pass A over positions of one group: the kernel accumulators (a listed group) or zero.
pub proof fn lemma_run_a(v: Cv, p: Seq<u32>, lo: int, hi: int, g: int)
    requires one_group(v, p, lo, hi, g),
    ensures
        pcnta(v, p, lo, hi) == if g < 7 { tpc(v, p, lo, hi) } else { 0 },
        psuma(v, p, lo, hi) == if g < 7 { tps(v, p, lo, hi) } else { 0 },
    decreases hi - lo,
{
    if hi > lo {
        lemma_run_a(v, p, lo, hi - 1, g);
        assert(rgid(v, p[hi - 1] as int) == g);
    }
}

/// `thr` is the coefficient threshold of `a > avg` on the balances.
pub open spec fn thr_of(thr: int, avg: Val) -> bool {
    forall|a: int| -acct_bound() < a < acct_bound() ==> #[trigger] gt_avg(a, avg) == (a > thr)
}

/// Pass B over positions of one group: the candidates above the threshold (group `k == g`, listed) or zero.
pub proof fn lemma_run_b(v: Cv, avg: Val, thr: int, k: int, p: Seq<u32>, lo: int, hi: int, g: int)
    requires
        cv_ok(v),
        rows_in(v, p, lo, hi),
        one_group(v, p, lo, hi, g),
        thr_of(thr, avg),
    ensures
        pcntb(v, avg, k, p, lo, hi) == if g < 7 && k == g { pcgt(v, p, lo, hi, thr) } else { 0 },
        psumb(v, avg, k, p, lo, hi) == if g < 7 && k == g { psgt(v, p, lo, hi, thr) } else { 0 },
    decreases hi - lo,
{
    if hi > lo {
        lemma_run_b(v, avg, thr, k, p, lo, hi - 1, g);
        let r = p[hi - 1] as int;
        assert(rgid(v, r) == g);
        assert(r < v.n);
        assert(-acct_bound() < racct(v, r) < acct_bound());
        assert(gt_avg(racct(v, r), avg) == (racct(v, r) > thr));
    }
}

// ------------------------------------------------------------------------------------------------ reindexing

/// The order `p` as a row map.
pub open spec fn pmap(p: Seq<u32>) -> Seq<int> {
    Seq::new(p.len(), |j: int| p[j] as int)
}

pub open spec fn fa_cnt(v: Cv) -> spec_fn(int) -> int {
    |i: int| if qa(v, i) { 1int } else { 0int }
}

pub open spec fn fa_sum(v: Cv) -> spec_fn(int) -> int {
    |i: int| if qa(v, i) { racct(v, i) } else { 0int }
}

pub open spec fn fb_cnt(v: Cv, avg: Val, k: int) -> spec_fn(int) -> int {
    |i: int| if qb(v, avg, i) && rgid(v, i) == k { 1int } else { 0int }
}

pub open spec fn fb_sum(v: Cv, avg: Val, k: int) -> spec_fn(int) -> int {
    |i: int| if qb(v, avg, i) && rgid(v, i) == k { racct(v, i) } else { 0int }
}

proof fn lemma_rows_a(v: Cv, m: int)
    requires m >= 0,
    ensures cnta(v, 0, m) == sum_range(fa_cnt(v), m), suma(v, 0, m) == sum_range(fa_sum(v), m),
    decreases m,
{
    if m > 0 {
        lemma_rows_a(v, m - 1);
    }
}

proof fn lemma_pos_a(v: Cv, p: Seq<u32>, m: int)
    requires 0 <= m <= p.len(),
    ensures pcnta(v, p, 0, m) == sum_over(pmap(p), fa_cnt(v), m), psuma(v, p, 0, m) == sum_over(pmap(p), fa_sum(v), m),
    decreases m,
{
    if m > 0 {
        lemma_pos_a(v, p, m - 1);
        assert(pmap(p)[m - 1] == p[m - 1] as int);
    }
}

proof fn lemma_rows_b(v: Cv, avg: Val, k: int, m: int)
    requires m >= 0,
    ensures cntb(v, avg, k, 0, m) == sum_range(fb_cnt(v, avg, k), m), sumb(v, avg, k, 0, m) == sum_range(fb_sum(v, avg, k), m),
    decreases m,
{
    if m > 0 {
        lemma_rows_b(v, avg, k, m - 1);
    }
}

proof fn lemma_pos_b(v: Cv, avg: Val, k: int, p: Seq<u32>, m: int)
    requires 0 <= m <= p.len(),
    ensures
        pcntb(v, avg, k, p, 0, m) == sum_over(pmap(p), fb_cnt(v, avg, k), m),
        psumb(v, avg, k, p, 0, m) == sum_over(pmap(p), fb_sum(v, avg, k), m),
    decreases m,
{
    if m > 0 {
        lemma_pos_b(v, avg, k, p, m - 1);
        assert(pmap(p)[m - 1] == p[m - 1] as int);
    }
}

/// Pass A over a bijection: the position accumulators are the row accumulators.
pub proof fn lemma_reindex_a(v: Cv, p: Seq<u32>, n: int)
    requires is_bij(pmap(p), n), p.len() == n,
    ensures pcnta(v, p, 0, n) == cnta(v, 0, n), psuma(v, p, 0, n) == suma(v, 0, n),
{
    lemma_rows_a(v, n);
    lemma_pos_a(v, p, n);
    lemma_sum_perm(pmap(p), n, fa_cnt(v));
    lemma_sum_perm(pmap(p), n, fa_sum(v));
}

/// Pass B over a bijection: the position accumulators are the row accumulators.
pub proof fn lemma_reindex_b(v: Cv, avg: Val, k: int, p: Seq<u32>, n: int)
    requires is_bij(pmap(p), n), p.len() == n,
    ensures pcntb(v, avg, k, p, 0, n) == cntb(v, avg, k, 0, n), psumb(v, avg, k, p, 0, n) == sumb(v, avg, k, 0, n),
{
    lemma_rows_b(v, avg, k, n);
    lemma_pos_b(v, avg, k, p, n);
    lemma_sum_perm(pmap(p), n, fb_cnt(v, avg, k));
    lemma_sum_perm(pmap(p), n, fb_sum(v, avg, k));
}

} // verus!
