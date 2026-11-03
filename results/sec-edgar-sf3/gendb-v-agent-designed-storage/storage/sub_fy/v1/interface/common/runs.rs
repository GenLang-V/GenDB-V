//! Runs and directories over row positions: a run-start list partitions `0..n` into nonempty runs; runs keyed by
//! strictly increasing pairs; a group directory (first run of every key value); per-run value bounds; and the
//! sparse form of a nullable column (its non-NULL rows, increasing).
use vstd::prelude::*;

verus! {

/// Strict lexicographic order of pairs.
pub open spec fn pair_lt(a0: u64, a1: u64, b0: u64, b1: u64) -> bool {
    a0 < b0 || (a0 == b0 && a1 < b1)
}

/// Pairs `(first[p], second[p])` strictly increase lexicographically.
pub open spec fn pairs_increasing(first: Seq<u64>, second: Seq<u64>) -> bool {
    &&& first.len() == second.len()
    &&& forall|p: int, q: int| 0 <= p < q < first.len() ==> pair_lt(#[trigger] first[p], second[p], #[trigger] first[q], second[q])
}

/// `start` (`runs + 1` entries, strictly increasing from 0 to `n`) cuts `0..n` into `runs` nonempty runs: run `r`
/// is `[start[r], start[r + 1])`.
pub open spec fn runs_partition_ok(start: Seq<u64>, runs: int, n: int) -> bool {
    &&& runs >= 0
    &&& start.len() == runs + 1
    &&& start[0] == 0
    &&& start[runs] == n
    &&& forall|a: int, b: int| 0 <= a < b <= runs ==> #[trigger] start[a] < #[trigger] start[b]
}

/// Row position `i` is in run `r`.
pub open spec fn in_run(start: Seq<u64>, r: int, i: int) -> bool {
    start[r] <= i < start[r + 1]
}

/// The run holding row position `i`.
pub open spec fn run_of(start: Seq<u64>, runs: int, i: int) -> int {
    choose|r: int| 0 <= r < runs && #[trigger] in_run(start, r, i)
}

/// Every row position `i < n` is in exactly one run, `run_of(start, runs, i)`.
pub proof fn lemma_run_of(start: Seq<u64>, runs: int, n: int, i: int)
    requires runs_partition_ok(start, runs, n), 0 <= i < n,
    ensures
        0 <= run_of(start, runs, i) < runs,
        in_run(start, run_of(start, runs, i), i),
        start[run_of(start, runs, i)] <= i < start[run_of(start, runs, i) + 1],
        forall|r: int| 0 <= r < runs && #[trigger] in_run(start, r, i) ==> r == run_of(start, runs, i),
{
    assert(runs > 0) by {
        if runs == 0 {
            assert(start[0] == start[runs]);
        }
    }
    lemma_run_exists(start, runs, n, i, runs);
    let r0 = run_of(start, runs, i);
    assert forall|r: int| 0 <= r < runs && #[trigger] in_run(start, r, i) implies r == r0 by {
        if r < r0 {
            assert(start[r + 1] <= start[r0]);
        } else if r > r0 {
            assert(start[r0 + 1] <= start[r]);
        }
    }
}

proof fn lemma_run_exists(start: Seq<u64>, runs: int, n: int, i: int, hi: int)
    requires runs_partition_ok(start, runs, n), 0 <= i < n, 0 < hi <= runs, i < start[hi],
    ensures exists|r: int| 0 <= r < runs && #[trigger] in_run(start, r, i),
    decreases hi,
{
    if start[hi - 1] <= i {
        assert(0 <= hi - 1 < runs && in_run(start, hi - 1, i));
    } else {
        if hi - 1 == 0 {
            assert(start[0] == 0);
        }
        lemma_run_exists(start, runs, n, i, hi - 1);
    }
}

/// `g[u]` is the first run whose key `k0` is at least `u` (`u <= count`): runs before it have keys below `u`, runs
/// from it on have keys of at least `u`. With nondecreasing keys, the runs of key `u` are `[g[u], g[u + 1])`.
pub open spec fn group_starts_ok(g: Seq<u64>, k0: Seq<u64>, count: int) -> bool {
    &&& g.len() == count + 1
    &&& forall|u: int| 0 <= u <= count ==> #[trigger] g[u] <= k0.len()
    &&& forall|u: int, r: int| 0 <= u <= count && 0 <= r < k0.len() ==> (r < #[trigger] g[u] <==> #[trigger] k0[r] < u)
}

/// Every value of run `r` lies in `[mins[r], maxs[r]]` (per-run skip bounds).
pub open spec fn run_bounds_ok(vals: Seq<i32>, start: Seq<u64>, mins: Seq<i32>, maxs: Seq<i32>) -> bool {
    &&& mins.len() == start.len() - 1
    &&& maxs.len() == start.len() - 1
    &&& forall|r: int, i: int| 0 <= r < mins.len() && start[r] <= i < start[r + 1]
        ==> #[trigger] mins[r] <= #[trigger] vals[i] && vals[i] <= maxs[r]
}

/// Sorted row positions (strictly increasing, below `n`): the non-NULL rows of a sparse column.
pub open spec fn sparse_rows_ok(rows: Seq<u64>, n: int) -> bool {
    &&& forall|a: int, b: int| 0 <= a < b < rows.len() ==> #[trigger] rows[a] < #[trigger] rows[b]
    &&& forall|k: int| 0 <= k < rows.len() ==> #[trigger] rows[k] < n
}

/// Row `j` is listed.
pub open spec fn sparse_has(rows: Seq<u64>, j: int) -> bool {
    exists|k: int| 0 <= k < rows.len() && rows[k] == j
}

/// The position of row `j` in the list (meaningful when listed).
pub open spec fn sparse_index(rows: Seq<u64>, j: int) -> int {
    choose|k: int| 0 <= k < rows.len() && rows[k] == j
}

/// In strictly increasing rows, the listed position of `rows[k]` is `k`.
pub proof fn lemma_sparse_index(rows: Seq<u64>, n: int, k: int)
    requires sparse_rows_ok(rows, n), 0 <= k < rows.len(),
    ensures sparse_has(rows, rows[k] as int), sparse_index(rows, rows[k] as int) == k,
{
    let j = rows[k] as int;
    assert(sparse_has(rows, j));
    let k2 = sparse_index(rows, j);
    if k2 < k {
        assert(rows[k2] < rows[k]);
    } else if k2 > k {
        assert(rows[k] < rows[k2]);
    }
}

} // verus!
