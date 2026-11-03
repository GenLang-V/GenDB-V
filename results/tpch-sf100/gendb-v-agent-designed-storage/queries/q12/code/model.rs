//! Raw column model of the Q12 scan over storage `facts`: the decoded orders and lineitem columns a scan task reads
//! (frame-of-reference codes plus per-group bases, uniform groups of `bs_o` / `bs_l` rows), the scan's window
//! (`Win`: receipt-date days, the selected l_shipmode dictionary entries and the high o_orderpriority entries),
//! the per-line contribution it counts (`lval`, `cnt`), and the co-clustering facts it relies on:
//! - `keys_distinct`: o_orderkey is distinct over the stored orders rows (the declared primary key);
//! - `lines_clustered`: along the stored lineitem rows, the stored position of each line's order (`rpos`, the first
//!   stored orders row with that key, or `n_o`) never decreases.
//! Under both, a cursor that only moves forward over the stored orders rows finds the order of every qualifying
//! line in turn (`lemma_rpos_walk`).
use vstd::prelude::*;
use crate::stores::facts::interface::common::keyidx::{fkey, keyidx_ok};

verus! {

/// Column slices of one scan (whole parts, requested on the calling thread).
pub struct Cols {
    pub ok_codes: &'static [u32],
    pub ok_bases: &'static [i64],
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
    pub ls_codes: &'static [u16],
    pub ls_bases: &'static [i64],
    pub ls_zmax: &'static [i64],
    pub lc_codes: &'static [u16],
    pub lc_bases: &'static [i64],
    pub lc_zmax: &'static [i64],
    pub lr_codes: &'static [u16],
    pub lr_bases: &'static [i64],
    pub lr_zmax: &'static [i64],
    pub lm_codes: &'static [u8],
    pub lm_bases: &'static [u64],
    /// Stored lineitem rows and their group size.
    pub n_l: usize,
    pub bs_l: usize,
}

impl Copy for Cols {}

impl Clone for Cols {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

/// The scan's parameters: the receipt-date window `[lo, hi]` (days since 2000-01-01), the l_shipmode dictionary
/// entries equal to `$1` and `$2` (`u64::MAX` when none is), and the o_orderpriority entries `'1-URGENT'` and
/// `'2-HIGH'` (`u64::MAX` when absent).
pub struct Win {
    pub lo: i64,
    pub hi: i64,
    pub s0: u64,
    pub s1: u64,
    pub u0: u64,
    pub u1: u64,
}

impl Copy for Win {}

impl Clone for Win {
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

/// Dictionary index of o_orderpriority of stored orders row `p`.
pub open spec fn oprio(c: Cols, p: int) -> int {
    c.op_bases@[p / c.bs_o as int] + c.op_codes@[p]
}

/// l_orderkey of stored lineitem row `j`.
pub open spec fn lkey(c: Cols, j: int) -> int {
    c.lk_bases@[j / c.bs_l as int] + c.lk_codes@[j]
}

/// l_shipdate of stored lineitem row `j`.
pub open spec fn lship(c: Cols, j: int) -> int {
    c.ls_bases@[j / c.bs_l as int] + c.ls_codes@[j]
}

/// l_commitdate of stored lineitem row `j`.
pub open spec fn lcmt(c: Cols, j: int) -> int {
    c.lc_bases@[j / c.bs_l as int] + c.lc_codes@[j]
}

/// l_receiptdate of stored lineitem row `j`.
pub open spec fn lrcp(c: Cols, j: int) -> int {
    c.lr_bases@[j / c.bs_l as int] + c.lr_codes@[j]
}

/// Dictionary index of l_shipmode of stored lineitem row `j`.
pub open spec fn lmode(c: Cols, j: int) -> int {
    c.lm_bases@[j / c.bs_l as int] + c.lm_codes@[j]
}

pub open spec fn in_i64(x: int) -> bool {
    i64::MIN <= x <= i64::MAX
}

/// Shapes of the slices, decoded values in `i64`, dictionary indices below `kp` (o_orderpriority) and `km`
/// (l_shipmode), receipt dates below their group's zone maximum.
pub open spec fn cols_ok(c: Cols, kp: int, km: int) -> bool {
    &&& c.bs_o >= 1
    &&& c.bs_l >= 1
    &&& c.ok_codes@.len() == c.n_o
    &&& c.op_codes@.len() == c.n_o
    &&& c.op_bases@.len() == c.ok_bases@.len()
    &&& c.ok_bases@.len() * c.bs_o >= c.n_o
    &&& c.lk_codes@.len() == c.n_l
    &&& c.ls_codes@.len() == c.n_l
    &&& c.lc_codes@.len() == c.n_l
    &&& c.lr_codes@.len() == c.n_l
    &&& c.lm_codes@.len() == c.n_l
    &&& c.ls_bases@.len() == c.lk_bases@.len()
    &&& c.lc_bases@.len() == c.lk_bases@.len()
    &&& c.lr_bases@.len() == c.lk_bases@.len()
    &&& c.lr_zmax@.len() == c.lk_bases@.len()
    &&& c.lc_zmax@.len() == c.lk_bases@.len()
    &&& c.ls_zmax@.len() == c.lk_bases@.len()
    &&& c.lm_bases@.len() == c.lk_bases@.len()
    &&& c.lk_bases@.len() * c.bs_l >= c.n_l
    &&& km < u64::MAX
    &&& kp < u64::MAX
    &&& keyidx_ok(c.ok_codes@, c.ok_bases@, c.oi_codes@, c.oi_bases@, c.bs_o as int, c.oi_kind, c.n_o as int)
    &&& forall|p: int| 0 <= p < c.n_o ==> in_i64(#[trigger] okey(c, p))
    &&& forall|p: int| 0 <= p < c.n_o ==> 0 <= #[trigger] oprio(c, p) < kp
    &&& forall|j: int| 0 <= j < c.n_l ==> in_i64(#[trigger] lkey(c, j))
    &&& forall|j: int| 0 <= j < c.n_l ==> in_i64(#[trigger] lship(c, j))
    &&& forall|j: int| 0 <= j < c.n_l ==> in_i64(#[trigger] lcmt(c, j))
    &&& forall|j: int| 0 <= j < c.n_l ==> in_i64(#[trigger] lrcp(c, j))
    &&& forall|j: int| 0 <= j < c.n_l ==> 0 <= #[trigger] lmode(c, j) < km
    &&& forall|j: int| 0 <= j < c.n_l ==> #[trigger] lrcp(c, j) <= c.lr_zmax@[j / c.bs_l as int]
    &&& forall|j: int| 0 <= j < c.n_l ==> #[trigger] lcmt(c, j) <= c.lc_zmax@[j / c.bs_l as int]
    &&& forall|j: int| 0 <= j < c.n_l ==> #[trigger] lship(c, j) <= c.ls_zmax@[j / c.bs_l as int]
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

// ------------------------------------------------------------------------------------------------ the counts

/// Stored lineitem row `j` passes the lineitem conditions: receipt date in `[lo, hi]`, `l_commitdate <
/// l_receiptdate`, `l_shipdate < l_commitdate`, ship mode one of the selected entries.
pub open spec fn lqual(c: Cols, w: Win, j: int) -> bool {
    &&& w.lo <= lrcp(c, j) <= w.hi
    &&& lcmt(c, j) < lrcp(c, j)
    &&& lship(c, j) < lcmt(c, j)
    &&& (lmode(c, j) == w.s0 || lmode(c, j) == w.s1)
}

/// Priority entry `e` is high (`'1-URGENT'` or `'2-HIGH'`).
pub open spec fn phigh(w: Win, e: int) -> bool {
    e == w.u0 || e == w.u1
}

/// Aggregate `a` (0: high, 1: low) takes an order of priority entry `e`.
pub open spec fn agg_takes(w: Win, a: int, e: int) -> bool {
    if a == 0 { phigh(w, e) } else { !phigh(w, e) }
}

/// Contribution of stored lineitem row `j` to aggregate `a` of ship-mode entry `d`: 1 when the line qualifies,
/// has mode `d`, its order exists and the order's priority is taken by `a`.
pub open spec fn lval(c: Cols, w: Win, a: int, d: int, j: int) -> int {
    let p = rpos(c, lkey(c, j));
    if lqual(c, w, j) && lmode(c, j) == d && p < c.n_o && agg_takes(w, a, oprio(c, p)) { 1int } else { 0int }
}

/// Sum of `lval` over stored lineitem rows `[j0, j1)`.
pub open spec fn cnt(c: Cols, w: Win, a: int, d: int, j0: int, j1: int) -> int
    decreases j1 - j0,
{
    if j1 <= j0 {
        0
    } else {
        cnt(c, w, a, d, j0, j1 - 1) + lval(c, w, a, d, j1 - 1)
    }
}

/// One more row at the end of a count range.
pub proof fn lemma_cnt_step(c: Cols, w: Win, a: int, d: int, j0: int, j1: int)
    requires j0 <= j1,
    ensures cnt(c, w, a, d, j0, j1 + 1) == cnt(c, w, a, d, j0, j1) + lval(c, w, a, d, j1),
{
}

/// A count over `[j0, j1)` lies in `[0, j1 - j0]`.
pub proof fn lemma_cnt_bound(c: Cols, w: Win, a: int, d: int, j0: int, j1: int)
    requires j0 <= j1,
    ensures 0 <= cnt(c, w, a, d, j0, j1) <= j1 - j0,
    decreases j1 - j0,
{
    if j0 < j1 {
        lemma_cnt_bound(c, w, a, d, j0, j1 - 1);
    }
}

/// Adjacent ranges add.
pub proof fn lemma_cnt_split(c: Cols, w: Win, a: int, d: int, j0: int, j1: int, j2: int)
    requires j0 <= j1 <= j2,
    ensures cnt(c, w, a, d, j0, j2) == cnt(c, w, a, d, j0, j1) + cnt(c, w, a, d, j1, j2),
    decreases j2 - j1,
{
    if j1 < j2 {
        lemma_cnt_split(c, w, a, d, j0, j1, j2 - 1);
    }
}

/// Rows that never qualify add nothing.
pub proof fn lemma_cnt_none(c: Cols, w: Win, a: int, d: int, j0: int, j1: int)
    requires forall|j: int| j0 <= j < j1 ==> !#[trigger] lqual(c, w, j),
    ensures cnt(c, w, a, d, j0, j1) == 0,
    decreases j1 - j0,
{
    if j0 < j1 {
        lemma_cnt_none(c, w, a, d, j0, j1 - 1);
    }
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

proof fn lemma_rpos_from_first(c: Cols, k: int, i: int, q: int)
    requires 0 <= i <= q < c.n_o, okey(c, q) == k,
    ensures rpos_from(c, k, i) <= q,
    decreases q - i,
{
    if i < q && okey(c, i) != k {
        lemma_rpos_from_first(c, k, i + 1, q);
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

/// No row before `rpos(k)` has key `k`.
pub proof fn lemma_rpos_first(c: Cols, k: int, q: int)
    requires 0 <= q < c.n_o, okey(c, q) == k,
    ensures rpos(c, k) <= q,
{
    lemma_rpos_from_first(c, k, 0, q);
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

/// A forward walk from `p0 <= rpos(k)` over rows without key `k` stays at or before `rpos(k)`: one step.
pub proof fn lemma_rpos_walk(c: Cols, k: int, p: int)
    requires 0 <= p < c.n_o, p <= rpos(c, k), okey(c, p) != k,
    ensures p + 1 <= rpos(c, k),
{
    lemma_rpos_bound(c, k);
}

/// The walk ends at `rpos(k)`: either at a row with key `k` (distinct keys) or past the last row.
pub proof fn lemma_rpos_walk_end(c: Cols, k: int, p: int)
    requires
        keys_distinct(c),
        0 <= p <= c.n_o,
        p <= rpos(c, k),
        p < c.n_o ==> okey(c, p) == k,
    ensures rpos(c, k) == p,
{
    lemma_rpos_bound(c, k);
    if p < c.n_o {
        lemma_rpos_of(c, p);
    }
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
