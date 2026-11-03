//! Round-robin block assignment of the fast scan: with `s` tasks, task `k` sums blocks `k, k + s, k + 2s, ...`
//! (round `r` of task `k` is block `k + r * s`), so every task reads all regions of the table. Each task runs the
//! same number of rounds `q`, with `q * s >= nb` (blocks past the end are empty, `lemma_bsum_past`).
//!
//! - `bsum(g)`: the model sum of block `g` (its rows `block_start(g) .. block_start(g + 1)`);
//! - `ssum(k, s, q)`: task `k`'s sum over its first `q` rounds;
//! - `rsum(K, s, q)`: the sums of tasks `0 .. K` added up;
//! - `lemma_rsum_all`: all `s` tasks together are the rows `0 .. block_start(q * s)` (round by round, each round being
//!   `s` adjacent blocks: `lemma_round`, `lemma_rsum_step`);
//! - bounds that keep every partial table inside `i128` / `u64` (`lemma_ssum_bound`, `lemma_rsum_bound`,
//!   `lemma_rsum_count`, `lemma_ssum_count_mono`).
//! A task may visit its rounds in any rotation (`fast::FastTask::run` starts at round `k * q / s`, so concurrent tasks
//! read different regions of the table): its sum is still `ssum(k, s, q)`.
//! Every lemma is stated per table entry `i` and value kind `w`.
use vstd::prelude::*;
use super::model::*;
use super::fast::{block_start, tval};

verus! {

/// The sum of block `g` (value kind `w`, table entry `i`).
pub open spec fn bsum(m: Model, p: int, i: int, w: int, g: int) -> int {
    isum(m, p, i, w, block_start(m, g), block_start(m, g + 1))
}

/// Task `k`'s sum over its first `q` rounds (blocks `k + r * s`, `r < q`).
pub open spec fn ssum(m: Model, p: int, i: int, w: int, k: int, s: int, q: int) -> int
    decreases q,
{
    if q <= 0 { 0 } else { ssum(m, p, i, w, k, s, q - 1) + bsum(m, p, i, w, k + (q - 1) * s) }
}

/// The sums of tasks `0 .. kk` over `q` rounds.
pub open spec fn rsum(m: Model, p: int, i: int, w: int, kk: int, s: int, q: int) -> int
    decreases kk,
{
    if kk <= 0 { 0 } else { rsum(m, p, i, w, kk - 1, s, q) + ssum(m, p, i, w, kk - 1, s, q) }
}

/// Round `r`'s first `kk` blocks (`r * s .. r * s + kk`).
pub open spec fn round_sum(m: Model, p: int, i: int, w: int, kk: int, s: int, r: int) -> int
    decreases kk,
{
    if kk <= 0 { 0 } else { round_sum(m, p, i, w, kk - 1, s, r) + bsum(m, p, i, w, r * s + kk - 1) }
}

/// Block starts grow with the block.
pub proof fn lemma_bs_mono(m: Model, a: int, b: int)
    requires model_wf(m), 0 <= a <= b,
    ensures 0 <= block_start(m, a) <= block_start(m, b) <= m.n,
{
    assert(a * m.bsize <= b * m.bsize) by (nonlinear_arith) requires 0 <= a <= b, m.bsize >= 1;
    assert(0 <= a * m.bsize) by (nonlinear_arith) requires 0 <= a, m.bsize >= 1;
}

/// A block at or past `nb` is empty.
pub proof fn lemma_bsum_past(m: Model, p: int, i: int, w: int, g: int)
    requires model_wf(m), g >= m.nb,
    ensures bsum(m, p, i, w, g) == 0, block_start(m, g) == m.n,
{
    assert(g * m.bsize >= m.nb * m.bsize) by (nonlinear_arith) requires g >= m.nb, m.bsize >= 1;
    assert((g + 1) * m.bsize >= m.nb * m.bsize) by (nonlinear_arith) requires g >= m.nb, m.bsize >= 1;
    lemma_isum_empty(m, p, i, w, m.n);
}

/// One block's sum is bounded by its rows: at most `bsize` of them.
pub proof fn lemma_bsum_bound(m: Model, p: int, i: int, w: int, g: int)
    requires
        model_wf(m), g >= 0, 0 <= w <= 5,
        forall|j: int| 0 <= j < m.n ==> #[trigger] block_ok(m, blk(m, j)),
    ensures
        -(m.bsize * vbound(w)) <= bsum(m, p, i, w, g) <= m.bsize * vbound(w),
        w == 5 ==> 0 <= bsum(m, p, i, w, g) <= m.bsize,
{
    let (lo, hi) = (block_start(m, g), block_start(m, g + 1));
    lemma_bs_mono(m, g, g + 1);
    assert(hi - lo <= m.bsize) by {
        assert((g + 1) * m.bsize == g * m.bsize + m.bsize) by (nonlinear_arith);
    }
    lemma_isum_bound(m, p, i, w, lo, hi);
    assert(vbound(w) >= 1);
    assert((hi - lo) * vbound(w) <= m.bsize * vbound(w)) by (nonlinear_arith)
        requires 0 <= hi - lo <= m.bsize, vbound(w) >= 1;
}

/// A task's sum over `q` rounds is bounded by `q` blocks.
pub proof fn lemma_ssum_bound(m: Model, p: int, i: int, w: int, k: int, s: int, q: int)
    requires
        model_wf(m), 0 <= k, 1 <= s, 0 <= q, 0 <= w <= 5,
        forall|j: int| 0 <= j < m.n ==> #[trigger] block_ok(m, blk(m, j)),
    ensures
        -(q * m.bsize * vbound(w)) <= ssum(m, p, i, w, k, s, q) <= q * m.bsize * vbound(w),
        w == 5 ==> 0 <= ssum(m, p, i, w, k, s, q) <= q * m.bsize,
    decreases q,
{
    if q > 0 {
        lemma_ssum_bound(m, p, i, w, k, s, q - 1);
        assert(k + (q - 1) * s >= 0) by (nonlinear_arith) requires 0 <= k, 1 <= s, 1 <= q;
        lemma_bsum_bound(m, p, i, w, k + (q - 1) * s);
        assert(q * m.bsize * vbound(w) == (q - 1) * m.bsize * vbound(w) + m.bsize * vbound(w)) by (nonlinear_arith);
        assert(q * m.bsize == (q - 1) * m.bsize + m.bsize) by (nonlinear_arith);
    }
}

/// A task's count over its first `a` rounds is at most its count over its first `b` rounds (`a <= b`).
pub proof fn lemma_ssum_count_mono(m: Model, p: int, i: int, k: int, s: int, a: int, b: int)
    requires
        model_wf(m), 0 <= k, 1 <= s, 0 <= a <= b,
        forall|j: int| 0 <= j < m.n ==> #[trigger] block_ok(m, blk(m, j)),
    ensures ssum(m, p, i, 5, k, s, a) <= ssum(m, p, i, 5, k, s, b),
    decreases b - a,
{
    if a < b {
        lemma_ssum_count_mono(m, p, i, k, s, a, b - 1);
        assert(k + (b - 1) * s >= 0) by (nonlinear_arith) requires 0 <= k, 1 <= s, 1 <= b;
        lemma_bsum_bound(m, p, i, 5, k + (b - 1) * s);
    }
}

/// `kk` tasks' sums together are bounded by `kk` times one task's bound; counts are non-negative and grow with `kk`.
pub proof fn lemma_rsum_bound(m: Model, p: int, i: int, w: int, kk: int, s: int, q: int)
    requires
        model_wf(m), 0 <= kk, 1 <= s, 0 <= q, 0 <= w <= 5,
        forall|j: int| 0 <= j < m.n ==> #[trigger] block_ok(m, blk(m, j)),
    ensures
        -(kk * (q * m.bsize * vbound(w))) <= rsum(m, p, i, w, kk, s, q) <= kk * (q * m.bsize * vbound(w)),
        w == 5 ==> 0 <= rsum(m, p, i, w, kk, s, q),
    decreases kk,
{
    if kk > 0 {
        lemma_rsum_bound(m, p, i, w, kk - 1, s, q);
        lemma_ssum_bound(m, p, i, w, kk - 1, s, q);
        let b = q * m.bsize * vbound(w);
        assert(kk * b == (kk - 1) * b + b) by (nonlinear_arith);
    }
}

/// Counts of tasks `0 .. kk` are at most those of tasks `0 .. kk2` (`kk <= kk2`).
pub proof fn lemma_rsum_count_mono(m: Model, p: int, i: int, kk: int, kk2: int, s: int, q: int)
    requires
        model_wf(m), 0 <= kk <= kk2, 1 <= s, 0 <= q,
        forall|j: int| 0 <= j < m.n ==> #[trigger] block_ok(m, blk(m, j)),
    ensures rsum(m, p, i, 5, kk, s, q) <= rsum(m, p, i, 5, kk2, s, q),
    decreases kk2 - kk,
{
    if kk < kk2 {
        lemma_rsum_count_mono(m, p, i, kk, kk2 - 1, s, q);
        lemma_ssum_bound(m, p, i, 5, kk2 - 1, s, q);
    }
}

/// The first `kk` blocks of round `r` are its rows `block_start(r * s) .. block_start(r * s + kk)`.
pub proof fn lemma_round(m: Model, p: int, i: int, w: int, kk: int, s: int, r: int)
    requires model_wf(m), 0 <= kk, 1 <= s, 0 <= r,
    ensures round_sum(m, p, i, w, kk, s, r) == isum(m, p, i, w, block_start(m, r * s), block_start(m, r * s + kk)),
    decreases kk,
{
    assert(r * s >= 0) by (nonlinear_arith) requires 0 <= r, 1 <= s;
    if kk == 0 {
        lemma_isum_empty(m, p, i, w, block_start(m, r * s));
    } else {
        lemma_round(m, p, i, w, kk - 1, s, r);
        lemma_bs_mono(m, r * s, r * s + kk - 1);
        lemma_bs_mono(m, r * s + kk - 1, r * s + kk);
        lemma_isum_split(m, p, i, w, block_start(m, r * s), block_start(m, r * s + kk - 1), block_start(m, r * s + kk));
    }
}

/// One more round adds round `q`'s first `kk` blocks to the sums of tasks `0 .. kk`.
pub proof fn lemma_rsum_step(m: Model, p: int, i: int, w: int, kk: int, s: int, q: int)
    requires 0 <= kk, 0 <= q,
    ensures rsum(m, p, i, w, kk, s, q + 1) == rsum(m, p, i, w, kk, s, q) + round_sum(m, p, i, w, kk, s, q),
    decreases kk,
{
    if kk > 0 {
        lemma_rsum_step(m, p, i, w, kk - 1, s, q);
        assert(kk - 1 + q * s == q * s + kk - 1);
    }
}

/// All `s` tasks over `q` rounds are the rows `0 .. block_start(q * s)`.
pub proof fn lemma_rsum_all(m: Model, p: int, i: int, w: int, s: int, q: int)
    requires model_wf(m), 1 <= s, 0 <= q,
    ensures rsum(m, p, i, w, s, s, q) == isum(m, p, i, w, 0, block_start(m, q * s)),
    decreases q,
{
    if q == 0 {
        lemma_rsum_zero(m, p, i, w, s, s);
        lemma_isum_empty(m, p, i, w, 0);
    } else {
        lemma_rsum_all(m, p, i, w, s, q - 1);
        lemma_rsum_step(m, p, i, w, s, s, q - 1);
        lemma_round(m, p, i, w, s, s, q - 1);
        assert((q - 1) * s + s == q * s) by (nonlinear_arith);
        assert((q - 1) * s >= 0) by (nonlinear_arith) requires q >= 1, s >= 1;
        lemma_bs_mono(m, 0, (q - 1) * s);
        lemma_bs_mono(m, (q - 1) * s, q * s);
        lemma_isum_split(m, p, i, w, 0, block_start(m, (q - 1) * s), block_start(m, q * s));
    }
}

/// No round: every task's sum is zero.
pub proof fn lemma_rsum_zero(m: Model, p: int, i: int, w: int, kk: int, s: int)
    requires 0 <= kk,
    ensures rsum(m, p, i, w, kk, s, 0) == 0,
    decreases kk,
{
    if kk > 0 {
        lemma_rsum_zero(m, p, i, w, kk - 1, s);
    }
}

/// Enough rounds cover every block: `q * s >= nb` gives all rows.
pub proof fn lemma_rsum_total(m: Model, p: int, i: int, w: int, s: int, q: int)
    requires model_wf(m), 1 <= s, 0 <= q, q * s >= m.nb,
    ensures rsum(m, p, i, w, s, s, q) == isum(m, p, i, w, 0, m.n),
{
    lemma_rsum_all(m, p, i, w, s, q);
    assert(q * s * m.bsize >= m.nb * m.bsize) by (nonlinear_arith) requires q * s >= m.nb, m.bsize >= 1;
}

} // verus!
