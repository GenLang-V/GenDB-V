//! The lineitem scan of a call: one `scan::ScanTask` per worker (at most `MAX_TASKS`) over consecutive row ranges
//! (`split_at`), run by `fork_join` (one worker: the whole range on the calling thread, no spawn), and the merge of
//! the per-range counts in range order (`merge`).
use vstd::prelude::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{fork_join, Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::agent::common::selection::*;
use crate::agent::scan::*;

verus! {

/// Start of part `k` when `n` items are split into `w` parts: `k * (n / w) + min(k, n % w)`.
pub open spec fn split_at(n: int, w: int, k: int) -> int {
    k * (n / w) + if k < n % w { k } else { n % w }
}

/// The part boundaries are non-decreasing and end at `n`.
pub proof fn lemma_split(n: int, w: int, k: int)
    requires 0 <= n, 1 <= w, 0 <= k < w,
    ensures
        split_at(n, w, k + 1) == split_at(n, w, k) + n / w + if k < n % w { 1int } else { 0int },
        0 <= split_at(n, w, k) <= split_at(n, w, k + 1) <= n,
        split_at(n, w, 0) == 0,
        split_at(n, w, w) == n,
{
    let (q, r) = (n / w, n % w);
    assert(n == w * q + r && 0 <= r < w && 0 <= q) by (nonlinear_arith) requires q == n / w, r == n % w, 0 <= n, 1 <= w;
    assert((k + 1) * q == k * q + q) by (nonlinear_arith);
    assert(w * q == q * w) by (nonlinear_arith);
    assert(0 <= k * q) by (nonlinear_arith) requires 0 <= k, 0 <= q;
    assert((k + 1) * q <= w * q) by (nonlinear_arith) requires k + 1 <= w, 0 <= q;
    assert(0 * q == 0);
}

/// The counts of `[0, nl)` start empty.
pub proof fn lemma_acc_empty(sv: StoresView, q: Probe)
    ensures acc_ok(Counts { n0: 0, h0: 0, n1: 0, h1: 0 }, sv, q, 0, 0),
{
}

/// Adds the counts `b` of `[mid, hi)` to the counts `a` of `[0, mid)`: the counts of `[0, hi)`.
fn merge(a: &mut Counts, b: &Counts, Ghost(sv): Ghost<StoresView>, Ghost(q): Ghost<Probe>, Ghost(mid): Ghost<int>, Ghost(hi): Ghost<int>)
    requires
        0 <= mid <= hi <= usize::MAX,
        acc_ok(*old(a), sv, q, 0, mid),
        acc_ok(*b, sv, q, mid, hi),
    ensures acc_ok(*final(a), sv, q, 0, hi),
{
    proof {
        assert forall|i: int| 0 <= #[trigger] t_n(sv, q, 0)(i) <= 1 by {}
        assert forall|i: int| 0 <= #[trigger] t_h(sv, q, 0)(i) <= 1 by {}
        assert forall|i: int| 0 <= #[trigger] t_n(sv, q, 1)(i) <= 1 by {}
        assert forall|i: int| 0 <= #[trigger] t_h(sv, q, 1)(i) <= 1 by {}
        lemma_rs_bound(sv, q, 0, hi, t_n(sv, q, 0));
        lemma_rs_bound(sv, q, 0, hi, t_h(sv, q, 0));
        lemma_rs_bound(sv, q, 0, hi, t_n(sv, q, 1));
        lemma_rs_bound(sv, q, 0, hi, t_h(sv, q, 1));
        lemma_range_sum_split(guard(p_qual(sv, q), t_n(sv, q, 0)), 0, mid, hi);
        lemma_range_sum_split(guard(p_qual(sv, q), t_h(sv, q, 0)), 0, mid, hi);
        lemma_range_sum_split(guard(p_qual(sv, q), t_n(sv, q, 1)), 0, mid, hi);
        lemma_range_sum_split(guard(p_qual(sv, q), t_h(sv, q, 1)), 0, mid, hi);
    }
    a.n0 = a.n0 + b.n0;
    a.h0 = a.h0 + b.h0;
    a.n1 = a.n1 + b.n1;
    a.h1 = a.h1 + b.h1;
}

/// Most tasks of one scan. The scan is memory-bound: more threads only compete for bandwidth (measured on the real
/// data: 32 tasks ~130 ms at 64 workers, 48 tasks ~160 ms, 64 tasks ~150 ms).
pub const MAX_TASKS: usize = 32;

/// The counts of all lineitem rows, with at most `workers` threads (at most `MAX_TASKS` tasks).
pub fn count_all(c: Cols, q: Probe, workers: usize, dispatch: &mut Dispatch, Ghost(sv): Ghost<StoresView>)
    -> (r: Result<Counts, WorkerFailure>)
    requires cols_ok(c, sv), probe_ok(q), 1 <= workers <= MAX_WORKERS,
    ensures r matches Ok(acc) ==> acc_ok(acc, sv, q, 0, c.nl as int),
{
    let n = c.nl;
    if workers == 1 {
        return Ok(scan_range(&c, &q, 0, n, new_bufs(), Ghost(sv)));
    }
    let nt = if workers > MAX_TASKS { MAX_TASKS } else { workers };
    let mut tasks: Vec<ScanTask> = Vec::new();
    let mut k: usize = 0;
    while k < nt
        invariant
            cols_ok(c, sv), probe_ok(q), n == c.nl,
            1 <= nt <= MAX_TASKS, k <= nt, tasks@.len() == k,
            forall|t: int| 0 <= t < k ==> (#[trigger] tasks@[t]).pre() && tasks@[t].sv@ == sv && tasks@[t].q == q
                && tasks@[t].lo == split_at(n as int, nt as int, t) && tasks@[t].hi == split_at(n as int, nt as int, t + 1),
        decreases nt - k,
    {
        proof { lemma_split(n as int, nt as int, k as int); }
        let lo = k * (n / nt) + if k < n % nt { k } else { n % nt };
        let hi = lo + n / nt + if k < n % nt { 1usize } else { 0usize };
        tasks.push(ScanTask { c, q, lo, hi, bf: new_bufs(), sv: Ghost(sv) });
        k = k + 1;
    }
    let ghost tasks0 = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => { return Err(e); },
    };
    let ghost outs0 = outs@;
    proof {
        assert forall|u: int| 0 <= u < nt implies acc_ok(#[trigger] outs0[u], sv, q,
            split_at(n as int, nt as int, u), split_at(n as int, nt as int, u + 1)) by {
            assert(tasks0[u].post(outs0[u]));
        }
    }
    let mut total = Counts { n0: 0, h0: 0, n1: 0, h1: 0 };
    proof {
        lemma_acc_empty(sv, q);
        lemma_split(n as int, nt as int, 0);
    }
    let mut t: usize = 0;
    while t < nt
        invariant
            cols_ok(c, sv), n == c.nl,
            1 <= nt, t <= nt, outs@ == outs0, outs0.len() == nt,
            forall|u: int| 0 <= u < nt ==> acc_ok(#[trigger] outs0[u], sv, q,
                split_at(n as int, nt as int, u), split_at(n as int, nt as int, u + 1)),
            acc_ok(total, sv, q, 0, split_at(n as int, nt as int, t as int)),
        decreases nt - t,
    {
        proof { lemma_split(n as int, nt as int, t as int); }
        let o = outs[t];
        merge(&mut total, &o, Ghost(sv), Ghost(q), Ghost(split_at(n as int, nt as int, t as int)),
            Ghost(split_at(n as int, nt as int, t + 1)));
        t = t + 1;
    }
    proof {
        lemma_split(n as int, nt as int, (nt - 1) as int);
    }
    Ok(total)
}

} // verus!
