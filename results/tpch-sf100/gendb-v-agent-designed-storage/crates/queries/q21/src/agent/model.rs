//! Raw column model of the Q21 scan over storage `facts`: the decoded orders and lineitem columns a scan task reads
//! (frame-of-reference codes plus per-group bases, uniform groups of `bs_o` / `bs_l` rows) and the per-line counts
//! the scan computes (`cnt`).
//!
//! A stored lineitem row `j` counts for supplier key `s` (`lhit`) when it is late (`l_commitdate < l_receiptdate`),
//! another line of its order has another supplier (`ex2`, the EXISTS), no late line of its order has another supplier
//! (`ex3`, the NOT EXISTS), its order is stored with o_orderstatus dictionary index `f` (`ofound`), and its
//! l_suppkey is `s`. Order and supplier facts the scan relies on:
//! - `keys_distinct`: o_orderkey is distinct over the stored orders rows (the declared primary key);
//! - `lines_clustered`: along the stored lineitem rows, the stored position of each line's order (`rpos`, the first
//!   stored orders row with that key, or `n_o`) never decreases.
//! Under both, the lines of stored order `p` are exactly the stored lineitem rows `j` with `rpos(lkey(j)) == p`, one
//! contiguous run, so a cursor walking both tables in step finds every order's lines (`merge_inv`, `lemma_merge_step`).
use vstd::prelude::*;
use crate::stores::facts::interface::common::keyidx::{fkey, keyidx_ok};

verus! {

/// Column slices of one scan (whole parts, requested on the calling thread).
pub struct Cols {
    pub ok_codes: &'static [u32],
    pub ok_bases: &'static [i64],
    pub os_codes: &'static [u8],
    pub os_bases: &'static [u64],
    pub oi_codes: &'static [u32],
    pub oi_bases: &'static [u64],
    pub oi_kind: u64,
    /// Stored orders rows and their group size.
    pub n_o: usize,
    pub bs_o: usize,
    pub lk_codes: &'static [u32],
    pub lk_bases: &'static [i64],
    pub ls_codes: &'static [u32],
    pub ls_bases: &'static [i64],
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

/// Dictionary index of o_orderstatus of stored orders row `p`.
pub open spec fn ostat(c: Cols, p: int) -> int {
    c.os_bases@[p / c.bs_o as int] + c.os_codes@[p]
}

/// l_orderkey of stored lineitem row `j`.
pub open spec fn lkey(c: Cols, j: int) -> int {
    c.lk_bases@[j / c.bs_l as int] + c.lk_codes@[j]
}

/// l_suppkey of stored lineitem row `j`.
pub open spec fn lsupp(c: Cols, j: int) -> int {
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

pub open spec fn in_i64(x: int) -> bool {
    i64::MIN <= x <= i64::MAX
}

/// Shapes of the slices, decoded values in `i64`, status indices below `k` (the dictionary size).
pub open spec fn cols_ok(c: Cols, k: int) -> bool {
    &&& 0 <= k <= u64::MAX
    &&& c.bs_o >= 1
    &&& c.bs_l >= 1
    &&& c.ok_codes@.len() == c.n_o
    &&& c.os_codes@.len() == c.n_o
    &&& c.os_bases@.len() == c.ok_bases@.len()
    &&& c.ok_bases@.len() * c.bs_o >= c.n_o
    &&& c.lk_codes@.len() == c.n_l
    &&& c.ls_codes@.len() == c.n_l
    &&& c.lc_codes@.len() == c.n_l
    &&& c.lr_codes@.len() == c.n_l
    &&& c.ls_bases@.len() == c.lk_bases@.len()
    &&& c.lc_bases@.len() == c.lk_bases@.len()
    &&& c.lr_bases@.len() == c.lk_bases@.len()
    &&& c.lk_bases@.len() * c.bs_l >= c.n_l
    &&& keyidx_ok(c.ok_codes@, c.ok_bases@, c.oi_codes@, c.oi_bases@, c.bs_o as int, c.oi_kind, c.n_o as int)
    &&& forall|p: int| 0 <= p < c.n_o ==> in_i64(#[trigger] okey(c, p))
    &&& forall|p: int| 0 <= p < c.n_o ==> 0 <= #[trigger] ostat(c, p) < k
    &&& forall|j: int| 0 <= j < c.n_l ==> in_i64(#[trigger] lkey(c, j))
    &&& forall|j: int| 0 <= j < c.n_l ==> in_i64(#[trigger] lsupp(c, j))
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

// ------------------------------------------------------------------------------------------------ the line condition

/// Stored lineitem row `j` is late: `l_commitdate < l_receiptdate`.
pub open spec fn late(c: Cols, j: int) -> bool {
    lcmt(c, j) < lrcp(c, j)
}

/// Stored lineitem row `i` is a line of row `j`'s order with another supplier.
pub open spec fn other(c: Cols, i: int, j: int) -> bool {
    lkey(c, i) == lkey(c, j) && lsupp(c, i) != lsupp(c, j)
}

/// EXISTS: some line of row `j`'s order has another supplier.
pub open spec fn ex2(c: Cols, j: int) -> bool {
    exists|i: int| 0 <= i < c.n_l && #[trigger] other(c, i, j)
}

/// The NOT EXISTS subquery's rows: some late line of row `j`'s order has another supplier.
pub open spec fn ex3(c: Cols, j: int) -> bool {
    exists|i: int| 0 <= i < c.n_l && #[trigger] other(c, i, j) && late(c, i)
}

/// Row `j`'s order is stored, with o_orderstatus dictionary index `f`.
pub open spec fn ofound(c: Cols, f: int, j: int) -> bool {
    rpos(c, lkey(c, j)) < c.n_o && ostat(c, rpos(c, lkey(c, j))) == f
}

/// Row `j` counts (for its own supplier).
pub open spec fn lineq(c: Cols, f: int, j: int) -> bool {
    late(c, j) && ex2(c, j) && !ex3(c, j) && ofound(c, f, j)
}

/// Row `j` counts for supplier key `s`.
pub open spec fn lhit(c: Cols, f: int, s: int, j: int) -> bool {
    lineq(c, f, j) && lsupp(c, j) == s
}

/// Number of counting stored lineitem rows in `[l0, l1)` with supplier key `s`.
pub open spec fn cnt(c: Cols, f: int, s: int, l0: int, l1: int) -> int
    decreases l1 - l0,
{
    if l1 <= l0 {
        0
    } else {
        cnt(c, f, s, l0, l1 - 1) + if lhit(c, f, s, l1 - 1) { 1int } else { 0 }
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

/// Two cursors right for the same orders row are equal.
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

/// The cursor of orders row 0 is lineitem row 0.
pub proof fn lemma_merge_zero(c: Cols, cur: int)
    requires merge_inv(c, 0, cur),
    ensures cur == 0,
{
    if cur > 0 {
        lemma_rpos_bound(c, lkey(c, cur - 1));
    }
}

/// Lines at or after the cursor of the end of orders have no stored order: they never count.
pub proof fn lemma_merge_end(c: Cols, f: int, s: int, cur: int)
    requires lines_clustered(c), merge_inv(c, c.n_o as int, cur),
    ensures cnt(c, f, s, cur, c.n_l as int) == 0,
{
    assert forall|j: int| cur <= j < c.n_l implies !#[trigger] lhit(c, f, s, j) by {
        lemma_lines_le(c, cur, j);
        lemma_rpos_bound(c, lkey(c, j));
    }
    lemma_cnt_none(c, f, s, cur, c.n_l as int);
}

// ------------------------------------------------------------------------------------------------ counts

/// One more row at the end of a count range.
pub proof fn lemma_cnt_step(c: Cols, f: int, s: int, l0: int, l1: int)
    requires l0 <= l1,
    ensures cnt(c, f, s, l0, l1 + 1) == cnt(c, f, s, l0, l1) + if lhit(c, f, s, l1) { 1int } else { 0 },
{
}

/// A count over `[l0, l1)` lies in `[0, l1 - l0]`.
pub proof fn lemma_cnt_bound(c: Cols, f: int, s: int, l0: int, l1: int)
    requires l0 <= l1,
    ensures 0 <= cnt(c, f, s, l0, l1) <= l1 - l0,
    decreases l1 - l0,
{
    if l0 < l1 {
        lemma_cnt_bound(c, f, s, l0, l1 - 1);
    }
}

/// Adjacent ranges add.
pub proof fn lemma_cnt_split(c: Cols, f: int, s: int, l0: int, l1: int, l2: int)
    requires l0 <= l1 <= l2,
    ensures cnt(c, f, s, l0, l2) == cnt(c, f, s, l0, l1) + cnt(c, f, s, l1, l2),
    decreases l2 - l1,
{
    if l1 < l2 {
        lemma_cnt_split(c, f, s, l0, l1, l2 - 1);
    }
}

/// Rows that never count add nothing.
pub proof fn lemma_cnt_none(c: Cols, f: int, s: int, l0: int, l1: int)
    requires forall|j: int| l0 <= j < l1 ==> !#[trigger] lhit(c, f, s, j),
    ensures cnt(c, f, s, l0, l1) == 0,
    decreases l1 - l0,
{
    if l0 < l1 {
        lemma_cnt_none(c, f, s, l0, l1 - 1);
    }
}

/// Number of late rows in `[l0, l1)`.
pub open spec fn nlate(c: Cols, l0: int, l1: int) -> int
    decreases l1 - l0,
{
    if l1 <= l0 {
        0
    } else {
        nlate(c, l0, l1 - 1) + if late(c, l1 - 1) { 1int } else { 0 }
    }
}

/// When the rows of `[l0, l1)` count exactly when they are late and the condition `b` holds, and every late one has
/// supplier key `w`, the count for supplier key `s` is the late rows when `b && s == w`, else 0.
pub proof fn lemma_cnt_run(c: Cols, f: int, s: int, l0: int, l1: int, b: bool, w: int)
    requires
        l0 <= l1,
        forall|j: int| l0 <= j < l1 ==> #[trigger] lineq(c, f, j) == (late(c, j) && b),
        forall|j: int| l0 <= j < l1 && #[trigger] late(c, j) ==> lsupp(c, j) == w,
    ensures cnt(c, f, s, l0, l1) == if b && s == w { nlate(c, l0, l1) } else { 0 },
    decreases l1 - l0,
{
    if l0 < l1 {
        lemma_cnt_run(c, f, s, l0, l1 - 1, b, w);
        assert(lineq(c, f, l1 - 1) == (late(c, l1 - 1) && b));
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


/// No stored orders row from `e` on has status index `f`.
pub open spec fn no_f_from(c: Cols, f: int, e: int) -> bool {
    forall|p: int| e <= p < c.n_o ==> #[trigger] ostat(c, p) != f
}

/// Lines at or after the cursor of orders row `e` never count when no orders row from `e` on has status `f`.
pub proof fn lemma_merge_tail(c: Cols, f: int, s: int, e: int, cur: int)
    requires lines_clustered(c), merge_inv(c, e, cur), no_f_from(c, f, e),
    ensures cnt(c, f, s, cur, c.n_l as int) == 0,
{
    assert forall|j: int| cur <= j < c.n_l implies !#[trigger] lhit(c, f, s, j) by {
        lemma_lines_le(c, cur, j);
        lemma_rpos_bound(c, lkey(c, j));
    }
    lemma_cnt_none(c, f, s, cur, c.n_l as int);
}


/// Lines between the cursors of orders rows `e` and `q` have their order in `[e, q)` (or none); when no row there has
/// status index `f`, they never count.
pub proof fn lemma_merge_gap(c: Cols, f: int, s: int, e: int, q: int, a: int, b: int)
    requires
        lines_clustered(c),
        e <= q,
        merge_inv(c, e, a),
        merge_inv(c, q, b),
        forall|p: int| e <= p < q ==> #[trigger] ostat(c, p) != f,
    ensures
        a <= b,
        cnt(c, f, s, a, b) == 0,
{
    if b < a {
        lemma_lines_le(c, b, a - 1);
    }
    assert forall|j: int| a <= j < b implies !#[trigger] lhit(c, f, s, j) by {
        lemma_lines_le(c, a, j);
        lemma_lines_le(c, j, b - 1);
        lemma_rpos_bound(c, lkey(c, j));
    }
    lemma_cnt_none(c, f, s, a, b);
}

} // verus!
