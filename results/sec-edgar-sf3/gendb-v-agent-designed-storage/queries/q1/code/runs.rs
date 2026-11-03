//! Accumulators over runs of a run-length-encoded layout, as plain sequences: `st` (`runs + 1` run starts,
//! strictly increasing), `sg` (the group code of every run) and `l` (one `i32` value per row). Over the runs
//! `[lo, hi)`: the rows of group `g` (`run_rows`), the runs of group `g` (`run_count`) and the exact value sum of
//! the rows of group `g` (`run_vals`). Each is defined by recursion on `hi`, is additive over adjacent run ranges
//! and is bounded by the rows it covers, so per-chunk partial results merge exactly in machine integers.
use vstd::prelude::*;

verus! {

/// Exact sum of `l[a..b)`.
pub open spec fn line_total(l: Seq<i32>, a: int, b: int) -> int
    decreases b - a,
{
    if b <= a { 0 } else { line_total(l, a, b - 1) + l[b - 1] as int }
}

/// Rows of the runs of group `g` among the runs `[lo, hi)`.
pub open spec fn run_rows(st: Seq<u64>, sg: Seq<u64>, g: int, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { run_rows(st, sg, g, lo, hi - 1) + if sg[hi - 1] == g { st[hi] - st[hi - 1] } else { 0 } }
}

/// Number of runs of group `g` among the runs `[lo, hi)`.
pub open spec fn run_count(sg: Seq<u64>, g: int, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { run_count(sg, g, lo, hi - 1) + if sg[hi - 1] == g { 1int } else { 0 } }
}

/// Exact value sum of the rows of the runs of group `g` among the runs `[lo, hi)`.
pub open spec fn run_vals(st: Seq<u64>, sg: Seq<u64>, l: Seq<i32>, g: int, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo {
        0
    } else {
        run_vals(st, sg, l, g, lo, hi - 1)
            + if sg[hi - 1] == g { line_total(l, st[hi - 1] as int, st[hi] as int) } else { 0 }
    }
}

/// A group with rows has a run.
pub proof fn lemma_rows_pos(st: Seq<u64>, sg: Seq<u64>, g: int, lo: int, hi: int)
    requires run_rows(st, sg, g, lo, hi) > 0,
    ensures exists|s: int| lo <= s < hi && sg[s] == g,
    decreases hi - lo,
{
    if hi > lo {
        if sg[hi - 1] != g {
            lemma_rows_pos(st, sg, g, lo, hi - 1);
        }
    }
}

/// Run starts strictly increase over `[0, runs]`.
pub open spec fn starts_ok(st: Seq<u64>, runs: int) -> bool {
    &&& st.len() == runs + 1
    &&& forall|a: int, b: int| 0 <= a < b <= runs ==> #[trigger] st[a] < #[trigger] st[b]
}

/// `|line_total(l, a, b)| <= 2^31 (b - a)`.
pub proof fn lemma_line_total_bound(l: Seq<i32>, a: int, b: int)
    requires a <= b,
    ensures -0x8000_0000 * (b - a) <= line_total(l, a, b) <= 0x8000_0000 * (b - a),
    decreases b - a,
{
    if b > a {
        lemma_line_total_bound(l, a, b - 1);
    }
}

/// `line_total` is additive over adjacent ranges.
pub proof fn lemma_line_total_split(l: Seq<i32>, a: int, m: int, b: int)
    requires a <= m <= b,
    ensures line_total(l, a, m) + line_total(l, m, b) == line_total(l, a, b),
    decreases b - m,
{
    if b > m {
        lemma_line_total_split(l, a, m, b - 1);
    }
}

/// The three accumulators are additive over adjacent run ranges.
pub proof fn lemma_runs_split(st: Seq<u64>, sg: Seq<u64>, l: Seq<i32>, g: int, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures
        run_rows(st, sg, g, lo, mid) + run_rows(st, sg, g, mid, hi) == run_rows(st, sg, g, lo, hi),
        run_count(sg, g, lo, mid) + run_count(sg, g, mid, hi) == run_count(sg, g, lo, hi),
        run_vals(st, sg, l, g, lo, mid) + run_vals(st, sg, l, g, mid, hi) == run_vals(st, sg, l, g, lo, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_runs_split(st, sg, l, g, lo, mid, hi - 1);
    }
}

/// Bounds: the rows and values of runs `[lo, hi)` lie within their row span `st[hi] - st[lo]`.
pub proof fn lemma_runs_bound(st: Seq<u64>, sg: Seq<u64>, l: Seq<i32>, runs: int, g: int, lo: int, hi: int)
    requires starts_ok(st, runs), 0 <= lo <= hi <= runs,
    ensures
        0 <= run_rows(st, sg, g, lo, hi) <= st[hi] - st[lo],
        0 <= run_count(sg, g, lo, hi) <= hi - lo,
        -0x8000_0000 * (st[hi] - st[lo]) <= run_vals(st, sg, l, g, lo, hi) <= 0x8000_0000 * (st[hi] - st[lo]),
    decreases hi - lo,
{
    if hi > lo {
        lemma_runs_bound(st, sg, l, runs, g, lo, hi - 1);
        if hi - 1 > lo {
            assert(st[lo] < st[hi - 1]);
        }
        assert(st[hi - 1] < st[hi]);
        lemma_line_total_bound(l, st[hi - 1] as int, st[hi] as int);
        assert(-0x8000_0000 * (st[hi - 1] - st[lo]) + -0x8000_0000 * (st[hi] - st[hi - 1])
            == -0x8000_0000 * (st[hi] - st[lo]));
        assert(0x8000_0000 * (st[hi - 1] - st[lo]) + 0x8000_0000 * (st[hi] - st[hi - 1])
            == 0x8000_0000 * (st[hi] - st[lo]));
    }
}

} // verus!
