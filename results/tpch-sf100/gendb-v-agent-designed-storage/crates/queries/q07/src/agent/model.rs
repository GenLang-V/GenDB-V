//! Raw column model of the Q7 scan: the decoded columns a scan task reads (frame-of-reference codes plus per-group
//! bases; uniform groups of `bs_*` rows, so row `j`'s group is `j / bs`), the nation classes of the two names, and
//! the per-line result the scan accumulates.
//!
//! - the nations with a class are listed (`Ctx`): class bit 1 (value 1) when the nation's name is `$1`, bit 2
//!   (value 2) when it is `$2` (`nat_cls`; unlisted keys have class 0);
//! - supplier, customer, orders rows are found by key (`srow`, `crow`, `orow`: the row holding the key, unique
//!   by the primary keys `keys_ok`); a line's supplier class `l_scls`, its order's customer class `l_ccls`;
//! - a line is in group `l_grp` in 0..4: pair 0 is (supplier nation `$1`, customer nation `$2`), pair 1 the
//!   reverse (only when `$1 != $2`); the year is 1995 (0) or 1996 (1); -1 when the line does not qualify;
//! - `rcnt` / `rsum` / `rmass`: count, sum of `l_vol` and sum of `|l_vol|` of the lines of a group over a range.
use vstd::prelude::*;
use crate::stores::facts::interface::common::keyidx::{fkey, keyidx_ok};
use super::dates::*;

verus! {

/// Column slices of one scan (whole parts, requested on the calling thread) and their sizes.
pub struct Cols {
    pub ls_codes: &'static [u16],
    pub ls_bases: &'static [i64],
    pub ls_zmax: &'static [i64],
    pub lsk_codes: &'static [u32],
    pub lsk_bases: &'static [i64],
    pub lln_codes: &'static [u8],
    pub lln_bases: &'static [i64],
    pub lok_codes: &'static [u32],
    pub lok_bases: &'static [i64],
    pub lp_codes: &'static [u32],
    pub lp_bases: &'static [i64],
    pub ld_codes: &'static [u8],
    pub ld_bases: &'static [i64],
    pub n_l: usize,
    pub bs_l: usize,
    pub ok_codes: &'static [u32],
    pub ok_bases: &'static [i64],
    pub oi_codes: &'static [u32],
    pub oi_bases: &'static [u64],
    pub oi_kind: u64,
    pub oc_codes: &'static [u32],
    pub oc_bases: &'static [i64],
    pub n_o: usize,
    pub bs_o: usize,
    pub sk_codes: &'static [u32],
    pub sk_bases: &'static [i64],
    pub sn_codes: &'static [u8],
    pub sn_bases: &'static [i64],
    pub s_kind: u64,
    pub n_s: usize,
    pub bs_s: usize,
    pub ck_codes: &'static [u32],
    pub ck_bases: &'static [i64],
    pub cn_codes: &'static [u8],
    pub cn_bases: &'static [i64],
    pub c_kind: u64,
    pub n_c: usize,
    pub bs_c: usize,
    /// An empty index column (supplier and customer keys have no index column).
    pub no_codes: &'static [u32],
    pub no_bases: &'static [u64],
    /// Run starts of l_orderkey along the stored lines (storage `li_okruns`; `runs_ok`), and their count.
    pub l_st: &'static [u32],
    pub n_st: usize,
}

impl Copy for Cols {}

impl Clone for Cols {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

// ------------------------------------------------------------------------------------------------ decoded values

/// Value of row `j` of a FOR column (`bases[j / bs] + codes[j]`).
pub open spec fn fv(bases: Seq<i64>, code: int, bs: int, j: int) -> int {
    bases[j / bs] + code
}

pub open spec fn lship(c: Cols, j: int) -> int { fv(c.ls_bases@, c.ls_codes@[j] as int, c.bs_l as int, j) }
pub open spec fn lsupp(c: Cols, j: int) -> int { fv(c.lsk_bases@, c.lsk_codes@[j] as int, c.bs_l as int, j) }
pub open spec fn lkey(c: Cols, j: int) -> int { fv(c.lok_bases@, c.lok_codes@[j] as int, c.bs_l as int, j) }
pub open spec fn lprice(c: Cols, j: int) -> int { fv(c.lp_bases@, c.lp_codes@[j] as int, c.bs_l as int, j) }
pub open spec fn ldisc(c: Cols, j: int) -> int { fv(c.ld_bases@, c.ld_codes@[j] as int, c.bs_l as int, j) }
pub open spec fn okey(c: Cols, p: int) -> int { fkey(c.ok_codes@, c.ok_bases@, c.bs_o as int, p) }
pub open spec fn ocust(c: Cols, p: int) -> int { fv(c.oc_bases@, c.oc_codes@[p] as int, c.bs_o as int, p) }
pub open spec fn skey(c: Cols, r: int) -> int { fkey(c.sk_codes@, c.sk_bases@, c.bs_s as int, r) }
pub open spec fn snat(c: Cols, r: int) -> int { fv(c.sn_bases@, c.sn_codes@[r] as int, c.bs_s as int, r) }
pub open spec fn ckey(c: Cols, r: int) -> int { fkey(c.ck_codes@, c.ck_bases@, c.bs_c as int, r) }
pub open spec fn cnat(c: Cols, r: int) -> int { fv(c.cn_bases@, c.cn_codes@[r] as int, c.bs_c as int, r) }

pub open spec fn in_i64(x: int) -> bool {
    i64::MIN <= x <= i64::MAX
}

/// `|x| < 10^15` (a numeric(15, 2) coefficient).
pub open spec fn small15(x: int) -> bool {
    -1_000_000_000_000_000 < x < 1_000_000_000_000_000
}

/// Lineitem slices: shapes, decoded values in their declared ranges, and the shipdate zone maxima.
pub open spec fn li_ok(c: Cols) -> bool {
    &&& c.bs_l >= 1
    &&& c.ls_codes@.len() == c.n_l && c.lsk_codes@.len() == c.n_l && c.lln_codes@.len() == c.n_l
    &&& c.lok_codes@.len() == c.n_l && c.lp_codes@.len() == c.n_l && c.ld_codes@.len() == c.n_l
    &&& c.ls_bases@.len() * c.bs_l >= c.n_l
    &&& c.ls_zmax@.len() == c.ls_bases@.len()
    &&& c.lsk_bases@.len() == c.ls_bases@.len() && c.lln_bases@.len() == c.ls_bases@.len()
    &&& c.lok_bases@.len() == c.ls_bases@.len() && c.lp_bases@.len() == c.ls_bases@.len()
    &&& c.ld_bases@.len() == c.ls_bases@.len()
    &&& forall|j: int| 0 <= j < c.n_l ==> in_i64(#[trigger] lship(c, j)) && lship(c, j) <= c.ls_zmax@[j / c.bs_l as int]
    &&& forall|j: int| 0 <= j < c.n_l ==> in_i64(#[trigger] lsupp(c, j))
    &&& forall|j: int| 0 <= j < c.n_l ==> in_i64(#[trigger] lkey(c, j))
    &&& forall|j: int| 0 <= j < c.n_l ==> small15(#[trigger] lprice(c, j))
    &&& forall|j: int| 0 <= j < c.n_l ==> small15(#[trigger] ldisc(c, j))
}

/// Orders slices: the key index over o_orderkey, o_custkey codes, decoded values in range.
pub open spec fn ord_ok(c: Cols) -> bool {
    &&& c.bs_o >= 1
    &&& c.oc_codes@.len() == c.n_o
    &&& c.oc_bases@.len() == c.ok_bases@.len()
    &&& keyidx_ok(c.ok_codes@, c.ok_bases@, c.oi_codes@, c.oi_bases@, c.bs_o as int, c.oi_kind, c.n_o as int)
    &&& forall|p: int| 0 <= p < c.n_o ==> in_i64(#[trigger] okey(c, p))
    &&& forall|p: int| 0 <= p < c.n_o ==> in_i64(#[trigger] ocust(c, p))
}

/// Supplier slices: keys (no index column; stored rows sorted by key when kind 1) and nation keys.
pub open spec fn sup_ok(c: Cols) -> bool {
    &&& c.bs_s >= 1
    &&& c.s_kind <= 1
    &&& keyidx_ok(c.sk_codes@, c.sk_bases@, c.no_codes@, c.no_bases@, c.bs_s as int, c.s_kind, c.n_s as int)
    &&& c.sn_codes@.len() == c.n_s && c.sn_bases@.len() == c.sk_bases@.len()
    &&& forall|r: int| 0 <= r < c.n_s ==> in_i64(#[trigger] skey(c, r))
    &&& forall|r: int| 0 <= r < c.n_s ==> in_i64(#[trigger] snat(c, r))
}

/// Customer slices: keys and nation keys.
pub open spec fn cus_ok(c: Cols) -> bool {
    &&& c.bs_c >= 1
    &&& c.c_kind <= 1
    &&& keyidx_ok(c.ck_codes@, c.ck_bases@, c.no_codes@, c.no_bases@, c.bs_c as int, c.c_kind, c.n_c as int)
    &&& c.cn_codes@.len() == c.n_c && c.cn_bases@.len() == c.ck_bases@.len()
    &&& forall|r: int| 0 <= r < c.n_c ==> in_i64(#[trigger] ckey(c, r))
    &&& forall|r: int| 0 <= r < c.n_c ==> in_i64(#[trigger] cnat(c, r))
}

/// Shapes of the slices, and decoded values in their declared ranges.
pub open spec fn cols_ok(c: Cols) -> bool {
    &&& li_ok(c)
    &&& ord_ok(c)
    &&& sup_ok(c)
    &&& cus_ok(c)
}

/// The keys of orders, supplier and customer rows are distinct (their primary keys).
pub open spec fn keys_ok(c: Cols) -> bool {
    &&& forall|a: int, b: int| 0 <= a < c.n_o && 0 <= b < c.n_o && #[trigger] okey(c, a) == #[trigger] okey(c, b) ==> a == b
    &&& forall|a: int, b: int| 0 <= a < c.n_s && 0 <= b < c.n_s && #[trigger] skey(c, a) == #[trigger] skey(c, b) ==> a == b
    &&& forall|a: int, b: int| 0 <= a < c.n_c && 0 <= b < c.n_c && #[trigger] ckey(c, a) == #[trigger] ckey(c, b) ==> a == b
}

// ------------------------------------------------------------------------------------------------ classes

/// The query constants of a scan: the nations with a class (keys `nk`, classes `nc`) and whether `$1 == $2`.
pub struct Ctx {
    pub nk: Seq<i64>,
    pub nc: Seq<u8>,
    pub same: bool,
}

/// The class of the last of the first `n` listed nations with key `v`, 0 when none.
pub open spec fn cls_in(nk: Seq<i64>, nc: Seq<u8>, v: int, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else if nk[n - 1] as int == v { nc[n - 1] as int } else { cls_in(nk, nc, v, n - 1) }
}

/// Class of nation key `v`: its listed class, 0 when it is not listed.
pub open spec fn nat_cls(x: Ctx, v: int) -> int {
    cls_in(x.nk, x.nc, v, x.nk.len() as int)
}

/// The supplier row with key `k` (meaningful when one exists).
pub open spec fn srow(c: Cols, k: int) -> int {
    choose|r: int| 0 <= r < c.n_s && #[trigger] skey(c, r) == k
}

pub open spec fn has_s(c: Cols, k: int) -> bool {
    exists|r: int| 0 <= r < c.n_s && #[trigger] skey(c, r) == k
}

pub open spec fn crow(c: Cols, k: int) -> int {
    choose|r: int| 0 <= r < c.n_c && #[trigger] ckey(c, r) == k
}

pub open spec fn has_c(c: Cols, k: int) -> bool {
    exists|r: int| 0 <= r < c.n_c && #[trigger] ckey(c, r) == k
}

pub open spec fn orow(c: Cols, k: int) -> int {
    choose|p: int| 0 <= p < c.n_o && #[trigger] okey(c, p) == k
}

pub open spec fn has_o(c: Cols, k: int) -> bool {
    exists|p: int| 0 <= p < c.n_o && #[trigger] okey(c, p) == k
}

/// The stored orders row of an order key: the row holding it, `n_o` without one.
#[verifier::opaque]
pub open spec fn opos(c: Cols, k: int) -> int {
    if has_o(c, k) { orow(c, k) } else { c.n_o as int }
}

/// Co-clustering: along the stored lines, the stored orders rows of their order keys never decrease.
#[verifier::opaque]
pub open spec fn clus_ok(c: Cols) -> bool {
    forall|j: int| 0 <= j < c.n_l - 1 ==> #[trigger] opos(c, lkey(c, j)) <= opos(c, lkey(c, j + 1))
}

/// Co-clustering between any two lines.
pub proof fn lemma_clus_mono(c: Cols, a: int, b: int)
    requires clus_ok(c), 0 <= a <= b < c.n_l,
    ensures opos(c, lkey(c, a)) <= opos(c, lkey(c, b)),
    decreases b - a,
{
    if a < b {
        lemma_clus_mono(c, a, b - 1);
        reveal(clus_ok);
        assert(opos(c, lkey(c, b - 1)) <= opos(c, lkey(c, (b - 1) + 1)));
    }
}

/// A key held by orders row `q` has `opos` `q`.
pub proof fn lemma_opos_at(c: Cols, k: int, q: int)
    requires keys_ok(c), 0 <= q < c.n_o, okey(c, q) == k,
    ensures has_o(c, k), opos(c, k) == q,
{
    reveal(opos);
    assert(has_o(c, k));
    let w = orow(c, k);
    assert(0 <= w < c.n_o && okey(c, w) == k);
}

/// A key not held by orders row `q` (`q` a row) does not have `opos` `q`; `opos` is at most `n_o`.
pub proof fn lemma_opos_ne(c: Cols, k: int, q: int)
    requires 0 <= q < c.n_o, okey(c, q) != k,
    ensures opos(c, k) != q, 0 <= opos(c, k) <= c.n_o,
{
    reveal(opos);
    if has_o(c, k) {
        let w = orow(c, k);
        assert(0 <= w < c.n_o && okey(c, w) == k);
    }
}

/// `opos` below `n_o` is the key's orders row.
pub proof fn lemma_opos_row(c: Cols, k: int)
    requires opos(c, k) < c.n_o,
    ensures has_o(c, k), orow(c, k) == opos(c, k), 0 <= opos(c, k), okey(c, opos(c, k)) == k,
{
    reveal(opos);
    if has_o(c, k) {
        let w = orow(c, k);
        assert(0 <= w < c.n_o && okey(c, w) == k);
    }
}

/// Run `k` of the l_orderkey run starts: lines `[st[k], st[k + 1])`, nonempty and inside the table, share one
/// order key, and the line right after the run has another key.
pub open spec fn run_ok(c: Cols, k: int) -> bool {
    let a = c.l_st@[k] as int;
    let b = c.l_st@[k + 1] as int;
    &&& a < b <= c.n_l
    &&& forall|s: int| a <= s < b ==> #[trigger] lkey(c, s) == lkey(c, a)
    &&& b < c.n_l ==> lkey(c, b) != lkey(c, b - 1)
}

/// The run starts (storage `li_okruns`' contract over the model): the first is line 0, every run is correct.
pub open spec fn runs_ok(c: Cols) -> bool {
    &&& c.n_st == c.l_st@.len()
    &&& c.l_st@.len() >= 1
    &&& c.l_st@[0] == 0
    &&& forall|k: int| 0 <= k < c.l_st@.len() - 1 ==> #[trigger] run_ok(c, k)
}

/// Supplier class of a supplier key: the class of its nation, 0 without a supplier.
pub open spec fn s_cls(c: Cols, x: Ctx, k: int) -> int {
    if has_s(c, k) { nat_cls(x, snat(c, srow(c, k))) } else { 0 }
}

/// Customer class of a customer key.
pub open spec fn c_cls(c: Cols, x: Ctx, k: int) -> int {
    if has_c(c, k) { nat_cls(x, cnat(c, crow(c, k))) } else { 0 }
}

/// Customer class of an order key (through the order's customer), 0 without an order.
pub open spec fn o_cls(c: Cols, x: Ctx, k: int) -> int {
    if has_o(c, k) { c_cls(c, x, ocust(c, orow(c, k))) } else { 0 }
}

/// Bit 1 (`$1`) and bit 2 (`$2`) of a class in 0..4.
pub open spec fn is1(cl: int) -> bool { cl % 2 == 1 }
pub open spec fn is2(cl: int) -> bool { cl >= 2 }

/// The pair of a line from its supplier and customer classes: 0 for ($1, $2), 1 for ($2, $1), -1 for none.
pub open spec fn pair_of(x: Ctx, sc: int, cc: int) -> int {
    if is1(sc) && is2(cc) { 0 } else if !x.same && is2(sc) && is1(cc) { 1 } else { -1 }
}

/// Year slot of a day of the window: 0 for 1995, 1 for 1996.
pub open spec fn yslot(d: int) -> int {
    if d < day_1996() { 0 } else { 1 }
}

/// The group of line `j` (0..4), or -1 when it does not qualify.
pub open spec fn l_grp(c: Cols, x: Ctx, j: int) -> int {
    let d = lship(c, j);
    if win_lo() <= d <= win_hi() {
        let pr = pair_of(x, s_cls(c, x, lsupp(c, j)), o_cls(c, x, lkey(c, j)));
        if pr >= 0 { 2 * pr + yslot(d) } else { -1 }
    } else {
        -1
    }
}

/// The scale-4 coefficient of `l_extendedprice * (1 - l_discount)` of line `j`.
pub open spec fn l_vol(c: Cols, j: int) -> int {
    lprice(c, j) * (100 - ldisc(c, j))
}

pub open spec fn iabs(v: int) -> int {
    if v < 0 { -v } else { v }
}

// ------------------------------------------------------------------------------------------------ range sums

/// Number of lines of `[a, b)` in group `gi`.
pub open spec fn rcnt(c: Cols, x: Ctx, gi: int, a: int, b: int) -> int
    decreases b - a,
{
    if b <= a { 0 } else { rcnt(c, x, gi, a, b - 1) + if l_grp(c, x, b - 1) == gi { 1int } else { 0 } }
}

/// Sum of `l_vol` over the lines of `[a, b)` in group `gi`.
pub open spec fn rsum(c: Cols, x: Ctx, gi: int, a: int, b: int) -> int
    decreases b - a,
{
    if b <= a { 0 } else { rsum(c, x, gi, a, b - 1) + if l_grp(c, x, b - 1) == gi { l_vol(c, b - 1) } else { 0 } }
}

/// Sum of `|l_vol|` over the lines of `[a, b)` in group `gi`.
pub open spec fn rmass(c: Cols, x: Ctx, gi: int, a: int, b: int) -> int
    decreases b - a,
{
    if b <= a { 0 } else { rmass(c, x, gi, a, b - 1) + if l_grp(c, x, b - 1) == gi { iabs(l_vol(c, b - 1)) } else { 0 } }
}

/// One more line at the end of a range.
pub proof fn lemma_r_step(c: Cols, x: Ctx, gi: int, a: int, b: int)
    requires a <= b,
    ensures
        rcnt(c, x, gi, a, b + 1) == rcnt(c, x, gi, a, b) + if l_grp(c, x, b) == gi { 1int } else { 0 },
        rsum(c, x, gi, a, b + 1) == rsum(c, x, gi, a, b) + if l_grp(c, x, b) == gi { l_vol(c, b) } else { 0 },
        rmass(c, x, gi, a, b + 1) == rmass(c, x, gi, a, b) + if l_grp(c, x, b) == gi { iabs(l_vol(c, b)) } else { 0 },
{
}

/// Adjacent ranges add.
pub proof fn lemma_r_split(c: Cols, x: Ctx, gi: int, a: int, m: int, b: int)
    requires a <= m <= b,
    ensures
        rcnt(c, x, gi, a, b) == rcnt(c, x, gi, a, m) + rcnt(c, x, gi, m, b),
        rsum(c, x, gi, a, b) == rsum(c, x, gi, a, m) + rsum(c, x, gi, m, b),
        rmass(c, x, gi, a, b) == rmass(c, x, gi, a, m) + rmass(c, x, gi, m, b),
    decreases b - m,
{
    if m < b {
        lemma_r_split(c, x, gi, a, m, b - 1);
    }
}

/// Lines outside every group add nothing.
pub proof fn lemma_r_none(c: Cols, x: Ctx, gi: int, a: int, b: int)
    requires forall|j: int| a <= j < b ==> #[trigger] l_grp(c, x, j) == -1, 0 <= gi,
    ensures rcnt(c, x, gi, a, b) == 0, rsum(c, x, gi, a, b) == 0, rmass(c, x, gi, a, b) == 0,
    decreases b - a,
{
    if a < b {
        lemma_r_none(c, x, gi, a, b - 1);
    }
}

/// Counts are bounded by the range, masses are nonnegative and bound the sums.
pub proof fn lemma_r_bounds(c: Cols, x: Ctx, gi: int, a: int, b: int)
    requires a <= b,
    ensures
        0 <= rcnt(c, x, gi, a, b) <= b - a,
        0 <= rmass(c, x, gi, a, b),
        -rmass(c, x, gi, a, b) <= rsum(c, x, gi, a, b) <= rmass(c, x, gi, a, b),
    decreases b - a,
{
    if a < b {
        lemma_r_bounds(c, x, gi, a, b - 1);
    }
}

/// Masses grow with the range.
pub proof fn lemma_r_mono(c: Cols, x: Ctx, gi: int, a: int, m: int, b: int)
    requires a <= m <= b,
    ensures rmass(c, x, gi, a, m) <= rmass(c, x, gi, a, b),
{
    lemma_r_split(c, x, gi, a, m, b);
    lemma_r_bounds(c, x, gi, m, b);
}

} // verus!
