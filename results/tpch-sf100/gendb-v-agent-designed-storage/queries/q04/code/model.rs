//! Raw column model of the Q4 scan over storage `facts`: the decoded orders and lineitem columns a scan task reads
//! (frame-of-reference codes plus per-group bases, uniform groups of `bs_o` / `bs_l` rows), the counts the scan
//! computes (`count_raw`), and the co-clustering facts it relies on:
//! - `keys_distinct`: o_orderkey is distinct over the stored orders rows (the declared primary key);
//! - `lines_clustered`: along the stored lineitem rows, the stored position of each line's order (`rpos`, the first
//!   stored orders row with that key, or `n_o`) never decreases.
//! Under both, the lines of stored order `p` are exactly the stored lineitem rows `j` with `rpos(lkey(j)) == p`, one
//! contiguous run, so a cursor walking both tables in step finds every order's lines (`merge_inv`, `lemma_merge_step`).
//!
//! Run lengths (storage `li_ordruns`): `rl[r]` is the length of the `r`-th maximal run of equal l_orderkey along the
//! stored lineitem rows, starting at `rstart(r)` (`runs_model`). When there are exactly as many runs as stored orders
//! rows and the last line's order exists, the runs pair up with the orders rows one to one (`lemma_runs_aligned`:
//! run `r` belongs to stored orders row `r`), so the lines of order `p` are the rows of run `p` (`lemma_run_lines`,
//! `lemma_run_late`), found without reading l_orderkey.
use vstd::prelude::*;
use crate::stores::facts::interface::common::keyidx::{fkey, keyidx_ok};
use crate::stores::li_ordruns::interface::{run_start, lemma_run_start_mono, lemma_run_start_next};

verus! {

/// Column slices of one scan (whole parts, requested on the calling thread).
pub struct Cols {
    pub ok_codes: &'static [u32],
    pub ok_bases: &'static [i64],
    pub od_codes: &'static [u16],
    pub od_bases: &'static [i64],
    pub op_codes: &'static [u8],
    pub op_bases: &'static [u64],
    pub oi_codes: &'static [u32],
    pub oi_bases: &'static [u64],
    pub oi_kind: u64,
    /// Stored orders rows and their group size.
    pub n_o: usize,
    pub bs_o: usize,
    pub lk_codes: &'static [u32],
    pub lk_bases: &'static [i64],
    pub lc_codes: &'static [u16],
    pub lc_bases: &'static [i64],
    pub lr_codes: &'static [u16],
    pub lr_bases: &'static [i64],
    /// Stored lineitem rows and their group size.
    pub n_l: usize,
    pub bs_l: usize,
    /// Run lengths of l_orderkey along the stored lineitem rows (storage li_ordruns; may be empty).
    pub rl: &'static [u8],
}

impl Copy for Cols {}

impl Clone for Cols {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

/// o_orderkey of stored orders row `p`.
pub open spec fn okey(c: Cols, p: int) -> int {
    fkey(c.ok_codes@, c.ok_bases@, c.bs_o as int, p)
}

/// o_orderdate (days since 2000-01-01) of stored orders row `p`.
pub open spec fn odate(c: Cols, p: int) -> int {
    c.od_bases@[p / c.bs_o as int] + c.od_codes@[p]
}

/// Dictionary index of o_orderpriority of stored orders row `p`.
pub open spec fn oprio(c: Cols, p: int) -> int {
    c.op_bases@[p / c.bs_o as int] + c.op_codes@[p]
}

/// l_orderkey of stored lineitem row `j`.
pub open spec fn lkey(c: Cols, j: int) -> int {
    c.lk_bases@[j / c.bs_l as int] + c.lk_codes@[j]
}

/// l_commitdate of stored lineitem row `j`.
pub open spec fn lcmt(c: Cols, j: int) -> int {
    c.lc_bases@[j / c.bs_l as int] + c.lc_codes@[j]
}

/// l_receiptdate of stored lineitem row `j`.
pub open spec fn lrcp(c: Cols, j: int) -> int {
    c.lr_bases@[j / c.bs_l as int] + c.lr_codes@[j]
}

pub open spec fn in_i64(x: int) -> bool {
    i64::MIN <= x <= i64::MAX
}

/// Shapes of the slices, decoded values in `i64`, priority indices below `k` (the dictionary size).
pub open spec fn cols_ok(c: Cols, k: int) -> bool {
    &&& c.bs_o >= 1
    &&& c.bs_l >= 1
    &&& c.ok_codes@.len() == c.n_o
    &&& c.od_codes@.len() == c.n_o
    &&& c.op_codes@.len() == c.n_o
    &&& c.od_bases@.len() == c.ok_bases@.len()
    &&& c.op_bases@.len() == c.ok_bases@.len()
    &&& c.ok_bases@.len() * c.bs_o >= c.n_o
    &&& c.lk_codes@.len() == c.n_l
    &&& c.lc_codes@.len() == c.n_l
    &&& c.lr_codes@.len() == c.n_l
    &&& c.lc_bases@.len() == c.lk_bases@.len()
    &&& c.lr_bases@.len() == c.lk_bases@.len()
    &&& c.lk_bases@.len() * c.bs_l >= c.n_l
    &&& keyidx_ok(c.ok_codes@, c.ok_bases@, c.oi_codes@, c.oi_bases@, c.bs_o as int, c.oi_kind, c.n_o as int)
    &&& forall|p: int| 0 <= p < c.n_o ==> in_i64(#[trigger] okey(c, p))
    &&& forall|p: int| 0 <= p < c.n_o ==> in_i64(#[trigger] odate(c, p))
    &&& forall|p: int| 0 <= p < c.n_o ==> 0 <= #[trigger] oprio(c, p) < k
    &&& forall|j: int| 0 <= j < c.n_l ==> in_i64(#[trigger] lkey(c, j))
    &&& forall|j: int| 0 <= j < c.n_l ==> in_i64(#[trigger] lcmt(c, j))
    &&& forall|j: int| 0 <= j < c.n_l ==> in_i64(#[trigger] lrcp(c, j))
}

/// o_orderkey is distinct over the stored orders rows.
pub open spec fn keys_distinct(c: Cols) -> bool {
    forall|a: int, b: int| 0 <= a < c.n_o && 0 <= b < c.n_o && a != b ==> #[trigger] okey(c, a) != #[trigger] okey(c, b)
}

/// The first stored orders row at or after `i` with key `k`, or `n_o`.
pub open spec fn rpos_from(c: Cols, k: int, i: int) -> int
    decreases c.n_o - i,
{
    if i < 0 || i >= c.n_o {
        c.n_o as int
    } else if okey(c, i) == k {
        i
    } else {
        rpos_from(c, k, i + 1)
    }
}

/// The stored orders row of key `k` (the first one), or `n_o` when none has it.
pub open spec fn rpos(c: Cols, k: int) -> int {
    rpos_from(c, k, 0)
}

/// Stored lineitem row `j`'s order comes no later than row `j + 1`'s.
pub open spec fn lstep(c: Cols, j: int) -> bool {
    rpos(c, lkey(c, j)) <= rpos(c, lkey(c, j + 1))
}

/// The stored lineitem rows follow the stored orders order.
pub open spec fn lines_clustered(c: Cols) -> bool {
    forall|j: int| 0 <= j < c.n_l - 1 ==> #[trigger] lstep(c, j)
}

/// Stored lineitem row `j` is a line of order key `k` with `l_commitdate < l_receiptdate`.
pub open spec fn lmatch(c: Cols, j: int, k: int) -> bool {
    lkey(c, j) == k && lcmt(c, j) < lrcp(c, j)
}

/// Some stored lineitem row matches order key `k` (the EXISTS subquery).
pub open spec fn has_line_raw(c: Cols, k: int) -> bool {
    exists|j: int| 0 <= j < c.n_l && #[trigger] lmatch(c, j, k)
}

/// Stored orders row `p` qualifies: its date lies in `[lo, hi]` and it has a matching line.
pub open spec fn qual_raw(c: Cols, lo: int, hi: int, p: int) -> bool {
    lo <= odate(c, p) <= hi && has_line_raw(c, okey(c, p))
}

/// Number of qualifying stored orders rows in `[q0, q1)` with priority index `d`.
pub open spec fn count_raw(c: Cols, lo: int, hi: int, d: int, q0: int, q1: int) -> int
    decreases q1 - q0,
{
    if q1 <= q0 {
        0
    } else {
        count_raw(c, lo, hi, d, q0, q1 - 1) + if qual_raw(c, lo, hi, q1 - 1) && oprio(c, q1 - 1) == d { 1int } else { 0 }
    }
}

/// The merge cursor `cur` is the first stored lineitem row whose order is at or after stored orders row `p`.
pub open spec fn merge_inv(c: Cols, p: int, cur: int) -> bool {
    &&& 0 <= cur <= c.n_l
    &&& cur < c.n_l ==> rpos(c, lkey(c, cur)) >= p
    &&& cur > 0 ==> rpos(c, lkey(c, cur - 1)) < p
}

// ------------------------------------------------------------------------------------------------ rpos

proof fn lemma_rpos_from_bound(c: Cols, k: int, i: int)
    requires 0 <= i,
    ensures
        0 <= rpos_from(c, k, i) <= c.n_o,
        rpos_from(c, k, i) < c.n_o ==> okey(c, rpos_from(c, k, i)) == k,
    decreases c.n_o - i,
{
    if i < c.n_o && okey(c, i) != k {
        lemma_rpos_from_bound(c, k, i + 1);
    }
}

proof fn lemma_rpos_from_at(c: Cols, k: int, i: int, p: int)
    requires
        0 <= i <= p <= c.n_o,
        p < c.n_o ==> okey(c, p) == k,
        forall|q: int| i <= q < p ==> #[trigger] okey(c, q) != k,
    ensures rpos_from(c, k, i) == p,
    decreases p - i,
{
    if i < p {
        lemma_rpos_from_at(c, k, i + 1, p);
    }
}

/// `rpos` lies in `[0, n_o]`, and below `n_o` it finds a row with key `k`.
pub proof fn lemma_rpos_bound(c: Cols, k: int)
    ensures
        0 <= rpos(c, k) <= c.n_o,
        rpos(c, k) < c.n_o ==> okey(c, rpos(c, k)) == k,
{
    lemma_rpos_from_bound(c, k, 0);
}

/// Under distinct keys, the stored row holding key `k` is `rpos(k)`.
pub proof fn lemma_rpos_of(c: Cols, p: int)
    requires keys_distinct(c), 0 <= p < c.n_o,
    ensures rpos(c, okey(c, p)) == p,
{
    assert forall|q: int| 0 <= q < p implies #[trigger] okey(c, q) != okey(c, p) by {}
    lemma_rpos_from_at(c, okey(c, p), 0, p);
}

/// No stored orders row has key `k`: `rpos(k) == n_o`.
pub proof fn lemma_rpos_none(c: Cols, k: int)
    requires forall|q: int| 0 <= q < c.n_o ==> #[trigger] okey(c, q) != k,
    ensures rpos(c, k) == c.n_o,
{
    lemma_rpos_from_at(c, k, 0, c.n_o as int);
}

/// `rpos` of lineitem rows is nondecreasing between any two rows.
pub proof fn lemma_lines_le(c: Cols, a: int, b: int)
    requires lines_clustered(c), 0 <= a <= b < c.n_l,
    ensures rpos(c, lkey(c, a)) <= rpos(c, lkey(c, b)),
    decreases b - a,
{
    if a < b {
        lemma_lines_le(c, a, b - 1);
        assert(lstep(c, b - 1));
    }
}

/// One merge step: when the cursor stood at the first line of order `p` or later (`merge_inv(p, c0)`) and advanced
/// over lines with key `okey(p)` up to `cur` (the first row with another key, or the end), then the lines of `p` are
/// exactly `[c0, cur)` and the cursor stands right for order `p + 1`.
pub proof fn lemma_merge_step(c: Cols, p: int, c0: int, cur: int)
    requires
        keys_distinct(c),
        lines_clustered(c),
        0 <= p < c.n_o,
        merge_inv(c, p, c0),
        c0 <= cur <= c.n_l,
        forall|j: int| c0 <= j < cur ==> #[trigger] lkey(c, j) == okey(c, p),
        cur < c.n_l ==> lkey(c, cur) != okey(c, p),
    ensures
        merge_inv(c, p + 1, cur),
        forall|j: int| 0 <= j < c.n_l && #[trigger] lkey(c, j) == okey(c, p) ==> c0 <= j < cur,
{
    let k = okey(c, p);
    lemma_rpos_of(c, p);
    if cur < c.n_l {
        // rpos(lkey(cur)) >= p (from c0 by monotony), and != p since its key differs from okey(p).
        if c0 < c.n_l {
            lemma_lines_le(c, c0, cur);
        }
        lemma_rpos_bound(c, lkey(c, cur));
        assert(rpos(c, lkey(c, cur)) > p);
    }
    if cur > c0 {
        assert(lkey(c, cur - 1) == k);
    }
    assert forall|j: int| 0 <= j < c.n_l && #[trigger] lkey(c, j) == okey(c, p) implies c0 <= j < cur by {
        assert(rpos(c, lkey(c, j)) == p);
        if j < c0 {
            lemma_lines_le(c, j, c0 - 1);
        } else if j >= cur {
            lemma_lines_le(c, cur, j);
        }
    }
}

/// The merge cursor of order `p` is unique.
pub proof fn lemma_merge_unique(c: Cols, p: int, a: int, b: int)
    requires lines_clustered(c), merge_inv(c, p, a), merge_inv(c, p, b),
    ensures a == b,
{
    if a < b {
        lemma_lines_le(c, a, b - 1);
    } else if b < a {
        lemma_lines_le(c, b, a - 1);
    }
}

// ------------------------------------------------------------------------------------------------ runs

/// First stored lineitem row of run `r`.
pub open spec fn rstart(c: Cols, r: int) -> int {
    run_start(c.rl@, r)
}

/// Row `i` of run `r` has the l_orderkey of the run's first row.
pub open spec fn lsame(c: Cols, r: int, i: int) -> bool {
    lkey(c, rstart(c, r) + i) == lkey(c, rstart(c, r))
}

/// Run `r` starts with another l_orderkey than the row before it.
pub open spec fn lsplit(c: Cols, r: int) -> bool {
    lkey(c, rstart(c, r)) != lkey(c, rstart(c, r) - 1)
}

/// The run lengths are the maximal runs of l_orderkey, one per stored orders row (`n_o` runs).
pub open spec fn runs_model(c: Cols) -> bool {
    &&& c.rl@.len() == c.n_o
    &&& c.n_o > 0
    &&& run_start(c.rl@, c.n_o as int) == c.n_l
    &&& forall|r: int| 0 <= r < c.n_o ==> #[trigger] c.rl@[r] >= 1
    &&& forall|r: int, i: int| 0 <= r < c.n_o && 0 <= i < c.rl@[r] ==> #[trigger] lsame(c, r, i)
    &&& forall|r: int| 0 < r < c.n_o ==> #[trigger] lsplit(c, r)
}

/// Run `r` holds the lines of stored orders row `r`.
pub open spec fn runs_aligned(c: Cols) -> bool {
    forall|r: int| 0 <= r < c.n_o ==> #[trigger] lkey(c, rstart(c, r)) == okey(c, r)
}

/// Stored lineitem row `j` has `l_commitdate < l_receiptdate`.
pub open spec fn late(c: Cols, j: int) -> bool {
    lcmt(c, j) < lrcp(c, j)
}

/// Some row of run `p` is late.
pub open spec fn run_late(c: Cols, p: int) -> bool {
    exists|j: int| rstart(c, p) <= j < rstart(c, p + 1) && #[trigger] late(c, j)
}

/// Runs start inside the table: `rstart(r) + (n_o - r) <= n_l`, and run `r` ends at `rstart(r + 1)`.
pub proof fn lemma_rstart_bounds(c: Cols, r: int)
    requires runs_model(c), 0 <= r <= c.n_o,
    ensures
        0 <= rstart(c, r),
        rstart(c, r) + (c.n_o - r) <= c.n_l,
        r < c.n_o ==> rstart(c, r + 1) == rstart(c, r) + c.rl@[r],
{
    lemma_run_start_mono(c.rl@, r, c.n_o as int);
    lemma_run_start_mono(c.rl@, 0, r);
    if r < c.n_o {
        lemma_run_start_next(c.rl@, r);
    }
}

/// Run starts are nondecreasing.
pub proof fn lemma_rstart_le(c: Cols, a: int, b: int)
    requires runs_model(c), 0 <= a <= b <= c.n_o,
    ensures rstart(c, a) <= rstart(c, b),
{
    lemma_run_start_mono(c.rl@, a, b);
}

/// The order position of run `r`'s key.
pub open spec fn fpos(c: Cols, r: int) -> int {
    rpos(c, lkey(c, rstart(c, r)))
}

/// `fpos` is nondecreasing (the lines follow the orders).
proof fn lemma_fpos_le(c: Cols, a: int, b: int)
    requires runs_model(c), lines_clustered(c), 0 <= a <= b < c.n_o,
    ensures fpos(c, a) <= fpos(c, b),
{
    lemma_rstart_le(c, a, b);
    lemma_rstart_bounds(c, a);
    lemma_rstart_bounds(c, b);
    lemma_lines_le(c, rstart(c, a), rstart(c, b));
}

/// The last run holds the last line, so its order position is that line's.
proof fn lemma_fpos_last(c: Cols)
    requires runs_model(c),
    ensures fpos(c, c.n_o - 1) == rpos(c, lkey(c, c.n_l - 1)),
{
    let r = c.n_o - 1;
    lemma_rstart_bounds(c, r);
    assert(rstart(c, r + 1) == c.n_l);
    assert(lsame(c, r, c.rl@[r] - 1));
}

/// Consecutive runs belong to different orders, when the later one's order exists.
proof fn lemma_fpos_lt(c: Cols, r: int)
    requires
        runs_model(c),
        lines_clustered(c),
        0 <= r < c.n_o - 1,
        fpos(c, r + 1) < c.n_o,
    ensures
        fpos(c, r) < fpos(c, r + 1),
{
    let e = rstart(c, r + 1);
    lemma_rstart_bounds(c, r);
    lemma_rstart_bounds(c, r + 1);
    assert(lsame(c, r, c.rl@[r] - 1));
    assert(lkey(c, e - 1) == lkey(c, rstart(c, r)));
    lemma_lines_le(c, e - 1, e);
    assert(lsplit(c, r + 1));
    if fpos(c, r) == fpos(c, r + 1) {
        lemma_rpos_bound(c, lkey(c, rstart(c, r)));
        lemma_rpos_bound(c, lkey(c, e));
    }
}

/// `fpos(r) >= r` (strictly increasing from 0).
proof fn lemma_fpos_ge(c: Cols, r: int)
    requires
        runs_model(c),
        lines_clustered(c),
        0 <= r < c.n_o,
        fpos(c, c.n_o - 1) < c.n_o,
    ensures
        fpos(c, r) >= r,
    decreases r,
{
    lemma_rpos_bound(c, lkey(c, rstart(c, r)));
    if r > 0 {
        lemma_fpos_ge(c, r - 1);
        lemma_fpos_le(c, r, c.n_o - 1);
        lemma_fpos_lt(c, r - 1);
    }
}

/// `fpos(r) <= r` (strictly increasing up to `n_o - 1`).
proof fn lemma_fpos_le_r(c: Cols, r: int)
    requires
        runs_model(c),
        lines_clustered(c),
        0 <= r < c.n_o,
        fpos(c, c.n_o - 1) < c.n_o,
    ensures
        fpos(c, r) <= r,
    decreases c.n_o - r,
{
    if r < c.n_o - 1 {
        lemma_fpos_le_r(c, r + 1);
        lemma_fpos_le(c, r + 1, c.n_o - 1);
        lemma_fpos_lt(c, r);
    }
}

/// With one run per stored orders row and the last line's order present, run `r` belongs to stored orders row `r`.
pub proof fn lemma_runs_aligned(c: Cols)
    requires
        runs_model(c),
        lines_clustered(c),
        rpos(c, lkey(c, c.n_l - 1)) < c.n_o,
    ensures
        runs_aligned(c),
{
    lemma_fpos_last(c);
    assert forall|r: int| 0 <= r < c.n_o implies #[trigger] lkey(c, rstart(c, r)) == okey(c, r) by {
        lemma_fpos_ge(c, r);
        lemma_fpos_le_r(c, r);
        lemma_rpos_bound(c, lkey(c, rstart(c, r)));
    }
}

/// The lines of stored order `p` are exactly the rows of run `p`.
pub proof fn lemma_run_lines(c: Cols, p: int)
    requires
        keys_distinct(c),
        lines_clustered(c),
        runs_model(c),
        runs_aligned(c),
        0 <= p < c.n_o,
    ensures
        merge_inv(c, p, rstart(c, p)),
        forall|j: int| 0 <= j < c.n_l ==> (#[trigger] lkey(c, j) == okey(c, p) <==> rstart(c, p) <= j < rstart(c, p + 1)),
{
    let s = rstart(c, p);
    let e = rstart(c, p + 1);
    lemma_rstart_bounds(c, p);
    lemma_rstart_bounds(c, p + 1);
    lemma_rpos_of(c, p);
    assert(lkey(c, s) == okey(c, p));
    if s > 0 {
        assert(p > 0);
        lemma_rstart_bounds(c, p - 1);
        assert(lsame(c, p - 1, c.rl@[p - 1] - 1));
        assert(lkey(c, s - 1) == okey(c, p - 1));
        lemma_rpos_of(c, p - 1);
    }
    assert(merge_inv(c, p, s));
    assert forall|j: int| s <= j < e implies #[trigger] lkey(c, j) == okey(c, p) by {
        assert(lsame(c, p, j - s));
    }
    if e < c.n_l {
        assert(p + 1 < c.n_o) by {
            if p + 1 == c.n_o {
                assert(e == c.n_l);
            }
        }
        assert(lkey(c, e) == okey(c, p + 1));
    }
    lemma_merge_step(c, p, s, e);
}

/// EXISTS over the lines of stored order `p` is a late row in run `p`.
pub proof fn lemma_run_late(c: Cols, p: int)
    requires
        keys_distinct(c),
        lines_clustered(c),
        runs_model(c),
        runs_aligned(c),
        0 <= p < c.n_o,
    ensures
        has_line_raw(c, okey(c, p)) == run_late(c, p),
{
    lemma_run_lines(c, p);
    lemma_rstart_bounds(c, p);
    lemma_rstart_bounds(c, p + 1);
    if has_line_raw(c, okey(c, p)) {
        let w = choose|j: int| 0 <= j < c.n_l && #[trigger] lmatch(c, j, okey(c, p));
        assert(late(c, w));
    }
    if run_late(c, p) {
        let w = choose|j: int| rstart(c, p) <= j < rstart(c, p + 1) && #[trigger] late(c, j);
        assert(lkey(c, w) == okey(c, p));
        assert(lmatch(c, w, okey(c, p)));
    }
}

// ------------------------------------------------------------------------------------------------ counts

/// One more row at the end of a count range.
pub proof fn lemma_count_step(c: Cols, lo: int, hi: int, d: int, q0: int, q1: int)
    requires q0 <= q1,
    ensures count_raw(c, lo, hi, d, q0, q1 + 1)
        == count_raw(c, lo, hi, d, q0, q1) + if qual_raw(c, lo, hi, q1) && oprio(c, q1) == d { 1int } else { 0 },
{
}

/// A count over `[q0, q1)` lies in `[0, q1 - q0]`.
pub proof fn lemma_count_bound(c: Cols, lo: int, hi: int, d: int, q0: int, q1: int)
    requires q0 <= q1,
    ensures 0 <= count_raw(c, lo, hi, d, q0, q1) <= q1 - q0,
    decreases q1 - q0,
{
    if q0 < q1 {
        lemma_count_bound(c, lo, hi, d, q0, q1 - 1);
    }
}

/// Adjacent ranges add.
pub proof fn lemma_count_split(c: Cols, lo: int, hi: int, d: int, q0: int, q1: int, q2: int)
    requires q0 <= q1 <= q2,
    ensures count_raw(c, lo, hi, d, q0, q2) == count_raw(c, lo, hi, d, q0, q1) + count_raw(c, lo, hi, d, q1, q2),
    decreases q2 - q1,
{
    if q1 < q2 {
        lemma_count_split(c, lo, hi, d, q0, q1, q2 - 1);
    }
}

/// Rows that never qualify add nothing.
pub proof fn lemma_count_none(c: Cols, lo: int, hi: int, d: int, q0: int, q1: int)
    requires forall|p: int| q0 <= p < q1 ==> !#[trigger] qual_raw(c, lo, hi, p),
    ensures count_raw(c, lo, hi, d, q0, q1) == 0,
    decreases q1 - q0,
{
    if q0 < q1 {
        lemma_count_none(c, lo, hi, d, q0, q1 - 1);
    }
}

// ------------------------------------------------------------------------------------------------ groups

/// Row `j` of group `g` (rows `g * bs .. g * bs + bs`) has `j / bs == g`.
pub proof fn lemma_div_group(j: int, bs: int, g: int)
    requires bs >= 1, g * bs <= j < g * bs + bs,
    ensures j / bs == g,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(j, bs, g, j - g * bs);
}

/// The next group starts one group size later: `(g + 1) * bs == g * bs + bs`.
pub proof fn lemma_next_group(g: int, bs: int)
    ensures (g + 1) * bs == g * bs + bs,
{
    assert((g + 1) * bs == g * bs + bs) by (nonlinear_arith);
}

/// A group index is at most the row index past its group: `g + 1 <= (g + 1) * bs`.
pub proof fn lemma_group_le(g: int, bs: int)
    requires g >= 0, bs >= 1,
    ensures g + 1 <= (g + 1) * bs,
{
    assert(g + 1 <= (g + 1) * bs) by (nonlinear_arith) requires g >= 0, bs >= 1;
}

/// The group of row `j` and the rows left in it: `j / bs * bs <= j`, `j + (bs - j % bs) == (j / bs + 1) * bs`.
pub proof fn lemma_group_of_row(j: int, bs: int)
    requires j >= 0, bs >= 1,
    ensures
        (j / bs) * bs <= j,
        0 <= j / bs,
        1 <= bs - j % bs <= bs,
        j + (bs - j % bs) == (j / bs) * bs + bs,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, bs);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(j, bs);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(j, bs);
    assert(bs * (j / bs) == (j / bs) * bs) by (nonlinear_arith);
}

/// `j < len * bs` puts `j / bs` below `len`.
pub proof fn lemma_div_below(j: int, bs: int, len: int)
    requires bs >= 1, 0 <= j < len * bs,
    ensures 0 <= j / bs < len,
{
    crate::stores::facts::interface::common::read::lemma_div_lt(j, bs, len);
}

} // verus!
