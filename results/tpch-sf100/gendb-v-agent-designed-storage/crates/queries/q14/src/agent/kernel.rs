//! The fast scan: lineitem row groups against dense part keys.
//!
//! Per lineitem group `g` (stored rows `gs[g] .. gs[g + 1]`): the shipdate zone map (group base as minimum, `zmax`
//! as maximum) skips a group outside the window. Otherwise the group is scanned in chunks of `CHUNK` rows, each in
//! blocks of 64 rows: (A) every row of the block is read densely and without branches (`dense_block`, vectorized):
//! the window test on the shipdate code, the part row `l_partkey - 1` (part keys are dense, `model::dense`) and
//! `l_extendedprice * (100 - l_discount)`; the joined rows (inside the window, with a part) give the count, sum and
//! mass and a 64-bit mask; (B) the mask's set bits, lowest first (`low_bit_index`), list each joined row's part row
//! and value (`compact_block`); (C) per chunk, the promotion bit of each listed part row is gathered from the bitmap
//! (independent loads) and added to the promotion count and sum without branches (`promo_sums`).
//!
//! Proof: count, sum and mass step per row (`dacc_ok`); the promotion accumulators of the rows are those of the
//! listed rows (`promo_listed`, `lsum` over a ghost list), since a row that does not join adds nothing.
//!
//! A group is scanned in `i64` when its bases are small (`group_fast_ok`: every value below `2^42`, at most 65536
//! rows); the range totals are `i128`. A range with a group outside that condition reports `false` and the caller
//! runs the general path instead.
use vstd::prelude::*;
use crate::spec::numeric::abs;
use crate::gendb_entry::layout::PartView;
use crate::stores::facts::interface::*;
use crate::stores::facts::interface::common::colfmt::*;
use crate::stores::custpart::interface::common::colfmt as cpc;
use crate::stores::custpart::interface::common::read as cpr;
use super::model::*;
use super::terms::*;
use super::bitmap::{bits_ok, bit, bit_in, lemma_shift_div, lemma_bit_01, lemma_bit_or, lemma_bit_zero};

verus! {

/// The shipdate window `[lo, hi)` in days since 2000-01-01.
#[derive(Clone, Copy)]
pub struct Win {
    pub lo: i64,
    pub hi: i64,
}

/// Accumulators 0..4 of a range of stored lineitem rows: count, promotion count, promotion sum, sum, mass.
#[derive(Clone, Copy)]
pub struct Acc {
    pub cnt: i128,
    pub pcnt: i128,
    pub psum: i128,
    pub sum: i128,
    pub mass: i128,
}

/// The accumulators of stored lineitem rows `r0 .. r1`.
pub open spec fn acc_ok(a: Acc, fp: Seq<PartView>, cp: Seq<PartView>, w: Win, r0: int, r1: int) -> bool {
    &&& a.cnt == tot(fp, cp, 0, w.lo as int, w.hi as int, r0, r1)
    &&& a.pcnt == tot(fp, cp, 1, w.lo as int, w.hi as int, r0, r1)
    &&& a.psum == tot(fp, cp, 2, w.lo as int, w.hi as int, r0, r1)
    &&& a.sum == tot(fp, cp, 3, w.lo as int, w.hi as int, r0, r1)
    &&& a.mass == tot(fp, cp, 4, w.lo as int, w.hi as int, r0, r1)
}

/// `2^42`: the bound of one row's value in the fast path.
pub open spec fn v_max() -> int {
    0x400_0000_0000
}

/// The accumulators of `rows` rows of the fast path are small.
pub open spec fn acc_small(a: Acc, rows: int) -> bool {
    &&& 0 <= a.cnt <= rows
    &&& 0 <= a.pcnt <= rows
    &&& 0 <= a.mass <= rows * v_max()
    &&& -a.mass <= a.psum <= a.mass
    &&& -a.mass <= a.sum <= a.mass
}

/// The promotion flag of every p_type dictionary entry.
pub open spec fn promo_ok(promo: Seq<bool>, cp: Seq<PartView>) -> bool {
    &&& promo.len() == n_td(cp)
    &&& forall|e: int| 0 <= e < n_td(cp) ==> #[trigger] promo[e] == promo_text(tdict(cp, e))
}

/// Dense part keys in uniform groups of 65536 rows.
pub open spec fn look_ok(p: PaCols, cp: Seq<PartView>) -> bool {
    &&& pa_cols_ok(p, cp)
    &&& dense(cp)
    &&& p.bsize == 65536
}

/// The fast condition of lineitem group `g`.
pub open spec fn group_fast_ok(c: LiCols, g: int) -> bool {
    &&& 0 <= c.price_base@[g] <= 0x1_0000_0000
    &&& 0 <= c.disc_base@[g] <= 0x100
    &&& -0x100_0000_0000 <= c.pk_base@[g] <= 0x100_0000_0000
    &&& c.gs@[g + 1] - c.gs@[g] <= 65536
}

/// `x` clamped into `[0, hi]`.
pub open spec fn clampi(x: int, hi: int) -> int {
    if x < 0 { 0 } else if x > hi { hi } else { x }
}

/// `x` clamped into `[0, 65536]`, as a shipdate code threshold.
#[inline]
pub fn clamp_code(x: i128) -> (r: u32)
    ensures r as int == clampi(x as int, 65536),
    no_unwind
{
    if x < 0 { 0 } else if x > 65536 { 65536 } else { x as u32 }
}

/// The values of stored lineitem row `j` of group `g` from the group's bases and the row's codes.
pub proof fn lemma_li_vals(c: LiCols, fp: Seq<PartView>, g: int, j: int)
    requires
        li_cols_ok(c, fp),
        0 <= g < c.ng,
        c.gs@[g] <= j < c.gs@[g + 1],
    ensures
        0 <= j < c.n,
        ship_at(fp, j) == c.ship_base@[g] + c.ship@[j],
        lpk_at(fp, j) == c.pk_base@[g] + c.pk@[j],
        price_at(fp, j) == c.price_base@[g] + c.price@[j],
        disc_at(fp, j) == c.disc_base@[g] + c.disc@[j],
        c.ship_base@[g] + c.ship@[j] <= c.ship_zmax@[g],
{
    let gs = li_gs(fp);
    let n = n_li(fp);
    assert(in_group(gs, g, j));
    lemma_groups_bounds(gs, n, g + 1);
    lemma_for_at(gs, n, fp[LI_SHIPDATE_BASE as int], fp[LI_SHIPDATE_CODES as int], g, j);
    lemma_for_at(gs, n, fp[LI_PARTKEY_BASE as int], fp[LI_PARTKEY_CODES as int], g, j);
    lemma_for_at(gs, n, fp[LI_EXTENDEDPRICE_BASE as int], fp[LI_EXTENDEDPRICE_CODES as int], g, j);
    lemma_for_at(gs, n, fp[LI_DISCOUNT_BASE as int], fp[LI_DISCOUNT_CODES as int], g, j);
}

/// The part lookup at stored part row `r`: its p_type dictionary index from its group's base and its code.
pub proof fn lemma_part_lookup(p: PaCols, cp: Seq<PartView>, r: int)
    requires
        look_ok(p, cp),
        0 <= r < p.n,
    ensures
        r / 65536 < p.ty_base@.len(),
        r < p.ty@.len(),
        tidx_at(cp, r) == p.ty_base@[r / 65536] + p.ty@[r],
        0 <= tidx_at(cp, r) < n_td(cp),
        pkey_at(cp, r) == r + 1,
{
    let gp = cp[pp(crate::stores::custpart::interface::PA_GROUPS)];
    let n = n_pa(cp);
    cpc::lemma_uniform_groups(gp, n, 65536);
    cpc::lemma_nblocks(n, 65536);
    cpr::lemma_div_lt(r, 65536, cpc::nblocks_of(n, 65536));
    cpr::lemma_for_row(gp, n, 65536, cp[pp(crate::stores::custpart::interface::PA_TYPE_BASE)],
        cp[pp(crate::stores::custpart::interface::PA_TYPE_CODES)], r);
}

// ------------------------------------------------------------------------------------------------ the chunk scan

/// Stored lineitem row `i` ships inside the window.
pub open spec fn inw(fp: Seq<PartView>, w: Win, i: int) -> bool {
    w.lo <= ship_at(fp, i) && ship_at(fp, i) < w.hi
}

/// Stored lineitem row `i` ships inside the window and its key has a part row (dense keys: row `l_partkey - 1`):
/// it joins, and counts in every accumulator.
pub open spec fn joined(fp: Seq<PartView>, cp: Seq<PartView>, w: Win, i: int) -> bool {
    inw(fp, w, i) && 1 <= lpk_at(fp, i) && lpk_at(fp, i) <= n_pa(cp)
}

/// `l_extendedprice * (100 - l_discount)` of stored lineitem row `i` (a coefficient at scale 4).
pub open spec fn val_at(fp: Seq<PartView>, i: int) -> int {
    price_at(fp, i) * (100 - disc_at(fp, i))
}

/// The bitmap word holding part row `r`.
pub open spec fn word_of(bits: Seq<Vec<u64>>, s: int, r: int) -> u64 {
    bits[(r / 64) / crate::agent::bitmap::p2(s)]@[(r / 64) % crate::agent::bitmap::p2(s)]
}

/// The window test of a shipdate code against the clamped thresholds, as one unsigned comparison.
pub proof fn lemma_window_code(lo: int, hi: int, base: int, cs: u32, s_lo: u32, s_hi: u32, width: u32)
    requires
        cs < 65536,
        s_lo as int == clampi(lo - base, 65536),
        s_hi as int == clampi(hi - base, 65536),
        width == if s_hi >= s_lo { (s_hi - s_lo) as u32 } else { 0u32 },
    ensures
        (cs.wrapping_sub(s_lo) < width) == (lo <= base + cs && base + cs < hi),
{
    assert(cs.wrapping_sub(s_lo) == if cs >= s_lo { (cs - s_lo) as u32 } else { (cs as int - s_lo as int + 0x1_0000_0000) as u32 });
}

/// The bit of part row `ru` in its word, by shifts.
pub proof fn lemma_bit_shift(wv: u64, ru: u64)
    ensures (((wv >> (ru & 63u64)) & 1u64) == 1u64) == bit(wv, ru as int % 64),
        ((wv >> (ru & 63u64)) & 1u64) <= 1u64,
{
    lemma_shift_div(ru);
    assert((ru & 63u64) as int == ru as int % 64);
    lemma_bit_01(wv, ru & 63u64);
}

/// Flipping bit `t` changes that bit only.
pub proof fn lemma_bit_flip(x: u64, t: u64, c: u64)
    requires t < 64, c < 64,
    ensures bit(x ^ (1u64 << t), c as int) == if c == t { !bit(x, c as int) } else { bit(x, c as int) },
{
    assert((((x ^ (1u64 << t)) >> c) & 1u64 == 1u64) == if c == t { !((x >> c) & 1u64 == 1u64) } else { (x >> c) & 1u64 == 1u64 }) by (bit_vector)
        requires t < 64, c < 64;
}

/// The position (0..63) of the single set bit of `low`, from its binary digits: each digit is whether the bit lies
/// in the mask of the positions with that digit set.
pub open spec fn bit_pos(low: u64) -> u64 {
    add(add(add(add(add(
        if low & 0xffff_ffff_0000_0000u64 != 0 { 32u64 } else { 0u64 },
        if low & 0xffff_0000_ffff_0000u64 != 0 { 16u64 } else { 0u64 }),
        if low & 0xff00_ff00_ff00_ff00u64 != 0 { 8u64 } else { 0u64 }),
        if low & 0xf0f0_f0f0_f0f0_f0f0u64 != 0 { 4u64 } else { 0u64 }),
        if low & 0xcccc_cccc_cccc_ccccu64 != 0 { 2u64 } else { 0u64 }),
        if low & 0xaaaa_aaaa_aaaa_aaaau64 != 0 { 1u64 } else { 0u64 })
}

/// `x & !(x - 1)` keeps exactly the lowest set bit `t` of `x`, and `bit_pos` finds `t`.
pub proof fn lemma_low_bit(x: u64, t: u64)
    requires
        x != 0,
        t < 64,
        (x >> t) & 1u64 == 1u64,
        x << sub(64, t) == 0,
    ensures
        x & !sub(x, 1) == 1u64 << t,
        bit_pos(1u64 << t) == t,
{
    assert(x & !sub(x, 1) == 1u64 << t) by (bit_vector)
        requires x != 0, t < 64, (x >> t) & 1u64 == 1u64, x << sub(64, t) == 0;
    assert(bit_pos(1u64 << t) == t) by (bit_vector)
        requires t < 64;
}

/// The position of the lowest set bit of `x != 0` (`trailing_zeros`, which is not `no_unwind` in the pinned vstd),
/// without branches.
pub fn low_bit_index(x: u64) -> (r: (u64, u64))
    requires x != 0,
    ensures
        r.0 == vstd::std_specs::bits::u64_trailing_zeros(x),
        r.0 < 64,
        r.1 == 1u64 << r.0,
    no_unwind
{
    let low = x & !(x - 1);
    let t = (if low & 0xffff_ffff_0000_0000u64 != 0 { 32u64 } else { 0u64 })
        + (if low & 0xffff_0000_ffff_0000u64 != 0 { 16u64 } else { 0u64 })
        + (if low & 0xff00_ff00_ff00_ff00u64 != 0 { 8u64 } else { 0u64 })
        + (if low & 0xf0f0_f0f0_f0f0_f0f0u64 != 0 { 4u64 } else { 0u64 })
        + (if low & 0xcccc_cccc_cccc_ccccu64 != 0 { 2u64 } else { 0u64 })
        + (if low & 0xaaaa_aaaa_aaaa_aaaau64 != 0 { 1u64 } else { 0u64 });
    proof {
        let tz = vstd::std_specs::bits::u64_trailing_zeros(x) as u64;
        vstd::std_specs::bits::axiom_u64_trailing_zeros(x);
        lemma_low_bit(x, tz);
        assert(low == 1u64 << tz);
        assert(t == bit_pos(low));
    }
    (t, low)
}

/// Rows per chunk of the scan (the size of a task's listing buffers).
pub const CHUNK: usize = 2048;

// ------------------------------------------------------------------------------------------------ count, sum, mass

/// The count, sum and mass of rows `r0 .. r1` in `i64`, with the bounds of the fast path.
pub open spec fn dacc_ok(fp: Seq<PartView>, cp: Seq<PartView>, w: Win, r0: int, r1: int, cnt: int, sum: int, mass: int) -> bool {
    &&& cnt == tot(fp, cp, 0, w.lo as int, w.hi as int, r0, r1)
    &&& sum == tot(fp, cp, 3, w.lo as int, w.hi as int, r0, r1)
    &&& mass == tot(fp, cp, 4, w.lo as int, w.hi as int, r0, r1)
    &&& 0 <= cnt <= r1 - r0
    &&& 0 <= mass <= (r1 - r0) * v_max()
    &&& -mass <= sum <= mass
}

/// The empty range.
pub proof fn lemma_dacc_empty(fp: Seq<PartView>, cp: Seq<PartView>, w: Win, r0: int)
    requires 0 <= r0 <= n_li(fp),
    ensures dacc_ok(fp, cp, w, r0, r0, 0, 0, 0),
{
    lemma_tot_empty(fp, cp, 0, w.lo as int, w.hi as int, r0);
    lemma_tot_empty(fp, cp, 3, w.lo as int, w.hi as int, r0);
    lemma_tot_empty(fp, cp, 4, w.lo as int, w.hi as int, r0);
}

/// One row more: count, sum and mass step by the row's terms (nothing unless it joins).
pub proof fn lemma_dacc_step(fp: Seq<PartView>, cp: Seq<PartView>, w: Win, r0: int, j: int, cnt: int, sum: int, mass: int)
    requires
        dense(cp),
        0 <= r0 <= j < n_li(fp),
        -v_max() < val_at(fp, j) < v_max(),
        dacc_ok(fp, cp, w, r0, j, cnt, sum, mass),
    ensures
        dacc_ok(fp, cp, w, r0, j + 1,
            cnt + if joined(fp, cp, w, j) { 1int } else { 0int },
            sum + if joined(fp, cp, w, j) { val_at(fp, j) } else { 0int },
            mass + if joined(fp, cp, w, j) { abs(val_at(fp, j)) } else { 0int }),
{
    let (lo, hi) = (w.lo as int, w.hi as int);
    lemma_tot_dense_step(fp, cp, lo, hi, r0, j);
    let q = joined(fp, cp, w, j);
    let v = val_at(fp, j);
    let pr = promo_text(ptype_at(cp, lpk_at(fp, j) - 1));
    assert(rowval(fp, cp, 0, lo, hi, j) == contrib(0, q, pr, v));
    assert(rowval(fp, cp, 3, lo, hi, j) == contrib(3, q, pr, v));
    assert(rowval(fp, cp, 4, lo, hi, j) == contrib(4, q, pr, v));
    lemma_contrib_bounds(q, pr, v);
    assert((j + 1 - r0) * v_max() == (j - r0) * v_max() + v_max()) by (nonlinear_arith);
}

/// Adjacent ranges join.
pub proof fn lemma_dacc_join(fp: Seq<PartView>, cp: Seq<PartView>, w: Win, r0: int, r1: int, r2: int,
    cnt: int, sum: int, mass: int, c1: int, s1: int, m1: int)
    requires
        0 <= r0 <= r1 <= r2 <= n_li(fp),
        dacc_ok(fp, cp, w, r0, r1, cnt, sum, mass),
        dacc_ok(fp, cp, w, r1, r2, c1, s1, m1),
    ensures
        dacc_ok(fp, cp, w, r0, r2, cnt + c1, sum + s1, mass + m1),
{
    let (lo, hi) = (w.lo as int, w.hi as int);
    lemma_tot_split(fp, cp, 0, lo, hi, r0, r1, r2);
    lemma_tot_split(fp, cp, 3, lo, hi, r0, r1, r2);
    lemma_tot_split(fp, cp, 4, lo, hi, r0, r1, r2);
    assert((r1 - r0) * v_max() + (r2 - r1) * v_max() == (r2 - r0) * v_max()) by (nonlinear_arith);
}

/// The promotion sum of a range lies within its mass.
pub proof fn lemma_psum_mass(fp: Seq<PartView>, cp: Seq<PartView>, lo: int, hi: int, a: int, b: int)
    requires
        dense(cp),
        0 <= a <= b <= n_li(fp),
    ensures
        -tot(fp, cp, 4, lo, hi, a, b) <= tot(fp, cp, 2, lo, hi, a, b) <= tot(fp, cp, 4, lo, hi, a, b),
    decreases b - a,
{
    if a == b {
        lemma_tot_empty(fp, cp, 2, lo, hi, a);
        lemma_tot_empty(fp, cp, 4, lo, hi, a);
    } else {
        lemma_psum_mass(fp, cp, lo, hi, a, b - 1);
        lemma_tot_dense_step(fp, cp, lo, hi, a, b - 1);
        let i = b - 1;
        let key = lpk_at(fp, i);
        let s = ship_at(fp, i);
        lemma_contrib_bounds(lo <= s && s < hi && 1 <= key && key <= n_pa(cp), promo_text(ptype_at(cp, key - 1)),
            price_at(fp, i) * (100 - disc_at(fp, i)));
    }
}

// ------------------------------------------------------------------------------------------------ the listing

/// Promotion accumulator `k` (1: count, 2: sum) over the listed rows `js`.
pub open spec fn lsum(fp: Seq<PartView>, cp: Seq<PartView>, w: Win, k: int, js: Seq<int>) -> int
    decreases js.len(),
{
    if js.len() == 0 {
        0
    } else {
        lsum(fp, cp, w, k, js.drop_last()) + rowval(fp, cp, k, w.lo as int, w.hi as int, js.last())
    }
}

/// A listed entry: joined row `j` with its part row `ru` and value `v`.
pub open spec fn listed_row(fp: Seq<PartView>, cp: Seq<PartView>, w: Win, j: int, ru: u64, v: i64) -> bool {
    &&& 0 <= j < n_li(fp)
    &&& joined(fp, cp, w, j)
    &&& ru as int == lpk_at(fp, j) - 1
    &&& v as int == val_at(fp, j)
    &&& -v_max() < v < v_max()
}

/// `js` lists `m` joined rows; entry `x` has part row `rb[x]` and value `vb[x]`.
pub open spec fn list_ok(fp: Seq<PartView>, cp: Seq<PartView>, w: Win, js: Seq<int>, rb: Seq<u64>, vb: Seq<i64>, m: int) -> bool {
    &&& js.len() == m
    &&& m <= rb.len()
    &&& m <= vb.len()
    &&& forall|x: int| 0 <= x < m ==> #[trigger] listed_row(fp, cp, w, js[x], rb[x], vb[x])
}

/// The promotion accumulators of rows `r0 .. r1` are those of the listed rows.
pub open spec fn promo_listed(fp: Seq<PartView>, cp: Seq<PartView>, w: Win, r0: int, r1: int, js: Seq<int>) -> bool {
    &&& tot(fp, cp, 1, w.lo as int, w.hi as int, r0, r1) == lsum(fp, cp, w, 1, js)
    &&& tot(fp, cp, 2, w.lo as int, w.hi as int, r0, r1) == lsum(fp, cp, w, 2, js)
}

/// Nothing listed before the first row.
pub proof fn lemma_promo_empty(fp: Seq<PartView>, cp: Seq<PartView>, w: Win, r0: int)
    requires 0 <= r0 <= n_li(fp),
    ensures promo_listed(fp, cp, w, r0, r0, Seq::empty()),
{
    lemma_tot_empty(fp, cp, 1, w.lo as int, w.hi as int, r0);
    lemma_tot_empty(fp, cp, 2, w.lo as int, w.hi as int, r0);
}

/// Rows `x .. y` that do not join add nothing to the promotion accumulators.
pub proof fn lemma_promo_skip(fp: Seq<PartView>, cp: Seq<PartView>, w: Win, r0: int, x: int, y: int, js: Seq<int>)
    requires
        dense(cp),
        0 <= r0 <= x <= y <= n_li(fp),
        forall|i: int| x <= i < y ==> !#[trigger] joined(fp, cp, w, i),
        promo_listed(fp, cp, w, r0, x, js),
    ensures
        promo_listed(fp, cp, w, r0, y, js),
    decreases y - x,
{
    if x < y {
        let (lo, hi) = (w.lo as int, w.hi as int);
        lemma_tot_dense_step(fp, cp, lo, hi, r0, x);
        assert(!joined(fp, cp, w, x));
        assert(rowval(fp, cp, 1, lo, hi, x) == 0);
        assert(rowval(fp, cp, 2, lo, hi, x) == 0);
        lemma_promo_skip(fp, cp, w, r0, x + 1, y, js);
    }
}

/// Row `j` listed: both sides step by its terms.
pub proof fn lemma_promo_list(fp: Seq<PartView>, cp: Seq<PartView>, w: Win, r0: int, j: int, js: Seq<int>)
    requires
        dense(cp),
        0 <= r0 <= j < n_li(fp),
        promo_listed(fp, cp, w, r0, j, js),
    ensures
        promo_listed(fp, cp, w, r0, j + 1, js.push(j)),
{
    lemma_tot_dense_step(fp, cp, w.lo as int, w.hi as int, r0, j);
    assert(js.push(j).drop_last() =~= js);
}

// ------------------------------------------------------------------------------------------------ one block

/// The common facts of the rows `j0 .. j0 + nb` of lineitem group `g` and the group's scan constants.
pub open spec fn block_ok(c: LiCols, fp: Seq<PartView>, cp: Seq<PartView>, g: int, j0: int, nb: int,
    kb1: i64, pb: i64, db: i64) -> bool
{
    &&& li_cols_ok(c, fp)
    &&& dense(cp)
    &&& 0 <= g < c.ng
    &&& group_fast_ok(c, g)
    &&& c.gs@[g] <= j0
    &&& j0 + nb <= c.gs@[g + 1]
    &&& c.gs@[g + 1] <= c.n
    &&& 0 <= nb <= 64
    &&& kb1 == c.pk_base@[g] - 1
    &&& pb == c.price_base@[g]
    &&& db == c.disc_base@[g]
}

/// The values of row `j` of a fast group: the key is `kb1 + 1 + code`, the value fits `2^42`.
pub proof fn lemma_fast_row(c: LiCols, fp: Seq<PartView>, g: int, j: int, kb1: i64, pb: i64, db: i64)
    requires
        li_cols_ok(c, fp),
        0 <= g < c.ng,
        group_fast_ok(c, g),
        c.gs@[g] <= j < c.gs@[g + 1],
        kb1 == c.pk_base@[g] - 1,
        pb == c.price_base@[g],
        db == c.disc_base@[g],
    ensures
        0 <= j < c.n,
        lpk_at(fp, j) == kb1 + 1 + c.pk@[j],
        val_at(fp, j) == (pb + c.price@[j]) * (100 - (db + c.disc@[j])),
        -v_max() < val_at(fp, j) < v_max(),
{
    lemma_li_vals(c, fp, g, j);
    assert(0 <= c.price@[j] < 0x1_0000_0000);
    assert(0 <= c.disc@[j] < 0x100);
    assert(-0x400_0000_0000 < (pb + c.price@[j]) * (100 - (db + c.disc@[j])) < 0x400_0000_0000) by (nonlinear_arith)
        requires 0 <= pb <= 0x1_0000_0000, 0 <= c.price@[j] < 0x1_0000_0000,
            0 <= db <= 0x100, 0 <= c.disc@[j] < 0x100;
}

/// Rows `j0 .. j0 + nb` (`nb <= 64`) of a fast group read densely, without branches: the mask of the joined rows
/// (bit `b` for row `j0 + b`) and their count, sum and mass.
pub fn dense_block(c: &LiCols, g: usize, j0: usize, nb: usize, w: Win, sb: i64, s_lo: u32, s_hi: u32, width: u32,
    kb1: i64, np: u64, pb: i64, db: i64, Ghost(fp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>)
    -> (r: (u64, i64, i64, i64))
    requires
        block_ok(*c, fp, cp, g as int, j0 as int, nb as int, kb1, pb, db),
        sb == c.ship_base@[g as int],
        s_lo as int == clampi(w.lo - sb, 65536),
        s_hi as int == clampi(w.hi - sb, 65536),
        width == if s_hi >= s_lo { (s_hi - s_lo) as u32 } else { 0u32 },
        np as int == n_pa(cp),
    ensures
        forall|bb: int| 0 <= bb < 64 ==> #[trigger] bit(r.0, bb) == (bb < nb && joined(fp, cp, w, j0 + bb)),
        dacc_ok(fp, cp, w, j0 as int, j0 + nb, r.1 as int, r.2 as int, r.3 as int),
    no_unwind
{
    hide(groups_wf);
    hide(zone_max_ok);
    let mut mask: u64 = 0;
    let mut cnt: i64 = 0;
    let mut sum: i64 = 0;
    let mut mass: i64 = 0;
    let mut b: usize = 0;
    proof {
        lemma_dacc_empty(fp, cp, w, j0 as int);
        assert forall|cc: int| 0 <= cc < 64 implies !#[trigger] bit(0u64, cc) by {
            lemma_bit_zero(cc as u64);
        }
    }
    while b < nb
        invariant
            block_ok(*c, fp, cp, g as int, j0 as int, nb as int, kb1, pb, db),
            sb == c.ship_base@[g as int],
            s_lo as int == clampi(w.lo - sb, 65536),
            s_hi as int == clampi(w.hi - sb, 65536),
            width == if s_hi >= s_lo { (s_hi - s_lo) as u32 } else { 0u32 },
            np as int == n_pa(cp),
            b <= nb,
            forall|bb: int| 0 <= bb < 64 ==> #[trigger] bit(mask, bb) == (bb < b && joined(fp, cp, w, j0 + bb)),
            dacc_ok(fp, cp, w, j0 as int, j0 + b, cnt as int, sum as int, mass as int),
        decreases nb - b,
    {
        let j = j0 + b;
        proof {
            lemma_fast_row(*c, fp, g as int, j as int, kb1, pb, db);
            lemma_li_vals(*c, fp, g as int, j as int);
        }
        let cs = c.ship[j] as u32;
        let f = cs.wrapping_sub(s_lo) < width;
        let r = kb1 + c.pk[j] as i64;
        let q = 0 <= r && (r as u64) < np;
        let v: i64 = (pb + c.price[j] as i64) * (100 - (db + c.disc[j] as i64));
        let fq = f && q;
        let fb: u64 = if fq { 1 } else { 0 };
        proof {
            lemma_window_code(w.lo as int, w.hi as int, sb as int, cs, s_lo, s_hi, width);
            assert(f == inw(fp, w, j as int));
            assert(fq == joined(fp, cp, w, j as int));
            assert forall|cc: int| 0 <= cc < 64 implies #[trigger] bit(mask | (fb << (b as u64)), cc)
                == if cc == b { bit(mask, cc) || fb == 1 } else { bit(mask, cc) } by {
                lemma_bit_or(mask, fb, b as u64, cc as u64);
            }
            lemma_dacc_step(fp, cp, w, j0 as int, j as int, cnt as int, sum as int, mass as int);
            assert((j + 1 - j0) * v_max() <= 64 * v_max()) by (nonlinear_arith)
                requires j + 1 - j0 <= 64;
        }
        mask = mask | (fb << (b as u64));
        let av: i64 = if v < 0 { -v } else { v };
        cnt = cnt + if fq { 1i64 } else { 0i64 };
        sum = sum + if fq { v } else { 0i64 };
        mass = mass + if fq { av } else { 0i64 };
        b = b + 1;
    }
    (mask, cnt, sum, mass)
}

/// The joined rows of a block in increasing order (lowest set bit of the mask first): each one's part row and
/// value appended to the listing at `m`.
pub fn compact_block(c: &LiCols, g: usize, a: usize, j0: usize, nb: usize, mask: u64, kb1: i64, pb: i64, db: i64,
    rbuf: &mut Vec<u64>, vbuf: &mut Vec<i64>, m: usize,
    Ghost(fp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>, Ghost(w): Ghost<Win>, Ghost(js): Ghost<Seq<int>>)
    -> (r: (usize, Ghost<Seq<int>>))
    requires
        block_ok(*c, fp, cp, g as int, j0 as int, nb as int, kb1, pb, db),
        forall|bb: int| 0 <= bb < 64 ==> #[trigger] bit(mask, bb) == (bb < nb && joined(fp, cp, w, j0 + bb)),
        old(rbuf)@.len() == CHUNK,
        old(vbuf)@.len() == CHUNK,
        a <= j0,
        m <= j0 - a,
        j0 + nb - a <= CHUNK,
        list_ok(fp, cp, w, js, old(rbuf)@, old(vbuf)@, m as int),
        promo_listed(fp, cp, w, a as int, j0 as int, js),
    ensures
        final(rbuf)@.len() == CHUNK,
        final(vbuf)@.len() == CHUNK,
        r.0 <= j0 + nb - a,
        list_ok(fp, cp, w, r.1@, final(rbuf)@, final(vbuf)@, r.0 as int),
        promo_listed(fp, cp, w, a as int, j0 + nb, r.1@),
    no_unwind
{
    hide(groups_wf);
    hide(zone_max_ok);
    let mut mk = mask;
    let mut mm = m;
    let ghost mut lj = js;
    // Rows `j0 .. j0 + pp` are handled; the mask holds the joined rows from `pp` on.
    let ghost mut pp: int = 0;
    while mk != 0
        invariant
            block_ok(*c, fp, cp, g as int, j0 as int, nb as int, kb1, pb, db),
            a <= j0,
            j0 + nb - a <= CHUNK,
            0 <= pp <= nb,
            forall|bb: int| 0 <= bb < 64 ==> #[trigger] bit(mk, bb) == (pp <= bb < nb && joined(fp, cp, w, j0 + bb)),
            mm <= j0 + pp - a,
            rbuf@.len() == CHUNK,
            vbuf@.len() == CHUNK,
            list_ok(fp, cp, w, lj, rbuf@, vbuf@, mm as int),
            promo_listed(fp, cp, w, a as int, j0 + pp, lj),
        decreases nb - pp,
    {
        let (tz, low) = low_bit_index(mk);
        proof {
            vstd::std_specs::bits::axiom_u64_trailing_zeros(mk);
            assert(tz < 64);
            assert(bit(mk, tz as int));
            assert forall|i: int| j0 + pp <= i < j0 + tz implies !#[trigger] joined(fp, cp, w, i) by {
                let bb = i - j0;
                assert(!bit(mk, bb));
            }
        }
        let t = tz as usize;
        let j = j0 + t;
        proof {
            lemma_fast_row(*c, fp, g as int, j as int, kb1, pb, db);
            lemma_li_vals(*c, fp, g as int, j as int);
            lemma_groups_bounds(li_gs(fp), n_li(fp), g as int + 1);
        }
        let r = kb1 + c.pk[j] as i64;
        let v: i64 = (pb + c.price[j] as i64) * (100 - (db + c.disc[j] as i64));
        let ghost (ob, ov) = (rbuf@, vbuf@);
        crate::gendb_entry::work::put(rbuf, mm, r as u64);
        crate::gendb_entry::work::put(vbuf, mm, v);
        proof {
            lemma_promo_skip(fp, cp, w, a as int, j0 + pp, j as int, lj);
            lemma_promo_list(fp, cp, w, a as int, j as int, lj);
            let nl = lj.push(j as int);
            assert(listed_row(fp, cp, w, j as int, r as u64, v));
            assert forall|x: int| 0 <= x < mm + 1 implies #[trigger] listed_row(fp, cp, w, nl[x], rbuf@[x], vbuf@[x]) by {
                if x < mm {
                    assert(nl[x] == lj[x] && rbuf@[x] == ob[x] && vbuf@[x] == ov[x]);
                }
            }
            assert forall|cc: int| 0 <= cc < 64 implies #[trigger] bit(mk ^ (1u64 << tz), cc)
                == (tz + 1 <= cc < nb && joined(fp, cp, w, j0 + cc)) by {
                lemma_bit_flip(mk, tz, cc as u64);
            }
            lj = nl;
            pp = tz + 1;
        }
        mk = mk ^ low;
        mm = mm + 1;
    }
    proof {
        assert forall|i: int| j0 + pp <= i < j0 + nb implies !#[trigger] joined(fp, cp, w, i) by {
            let bb = i - j0;
            lemma_bit_zero(bb as u64);
            assert(!bit(mk, bb));
        }
        lemma_groups_bounds(li_gs(fp), n_li(fp), g as int + 1);
        lemma_promo_skip(fp, cp, w, a as int, j0 + pp, j0 + nb, lj);
    }
    (mm, Ghost(lj))
}

/// The promotion count and sum of the listed rows: the bit of each listed part row in the bitmap (independent
/// loads, so their cache misses overlap), added without branches.
pub fn promo_sums(p: &PaCols, bits: &Vec<Vec<u64>>, s: u64, rbuf: &Vec<u64>, vbuf: &Vec<i64>, m: usize,
    Ghost(fp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>, Ghost(w): Ghost<Win>, Ghost(js): Ghost<Seq<int>>)
    -> (r: (i64, i64))
    requires
        look_ok(*p, cp),
        bits_ok(bits@, s as int, cp),
        m <= CHUNK,
        list_ok(fp, cp, w, js, rbuf@, vbuf@, m as int),
    ensures
        r.0 == lsum(fp, cp, w, 1, js),
        r.1 == lsum(fp, cp, w, 2, js),
        0 <= r.0 <= m,
    no_unwind
{
    hide(pa_shape);
    proof {
        vstd::bits::lemma_u64_pow2_no_overflow(s as nat);
        vstd::bits::lemma_u64_shl_is_mul(1u64, s);
    }
    let mask: u64 = (1u64 << s) - 1;
    proof {
        assert(mask as nat == vstd::bits::low_bits_mask(s as nat));
    }
    let mut pcnt: i64 = 0;
    let mut psum: i64 = 0;
    let mut t: usize = 0;
    while t < m
        invariant
            look_ok(*p, cp),
            bits_ok(bits@, s as int, cp),
            m <= CHUNK,
            list_ok(fp, cp, w, js, rbuf@, vbuf@, m as int),
            mask as nat == vstd::bits::low_bits_mask(s as nat),
            t <= m,
            pcnt == lsum(fp, cp, w, 1, js.take(t as int)),
            psum == lsum(fp, cp, w, 2, js.take(t as int)),
            0 <= pcnt <= t,
            -(t * v_max()) <= psum <= t * v_max(),
        decreases m - t,
    {
        let ru = rbuf[t];
        let v = vbuf[t];
        let ghost j = js[t as int];
        proof {
            assert(listed_row(fp, cp, w, j, ru, v));
            assert(ru < p.n);
        }
        let x = ru >> 6u64;
        proof {
            vstd::bits::lemma_u64_pow2_no_overflow(s as nat);
            lemma_shift_div(ru);
            vstd::bits::lemma_u64_shr_is_div(x, s);
            vstd::bits::lemma_u64_low_bits_mask_is_mod(x, s as nat);
            let r = ru as int;
            assert(bit_in(bits@, s as int, r) == promo_text(ptype_at(cp, r)));
            assert(x as int == r / 64);
            assert((x >> s) as int == (r / 64) / crate::agent::bitmap::p2(s as int));
            assert(mask == (vstd::bits::low_bits_mask(s as nat) as u64));
            assert(x & mask == x % (vstd::arithmetic::power2::pow2(s as nat) as u64));
            assert((x & mask) as int == (r / 64) % crate::agent::bitmap::p2(s as int));
        }
        let bi = (x >> s) as usize;
        let inner = &bits[bi];
        let oi = (x & mask) as usize;
        let nil = inner.len();
        proof {
            assert(oi < nil);
        }
        let wv = inner[oi];
        proof {
            lemma_bit_shift(wv, ru);
            assert(wv == word_of(bits@, s as int, ru as int));
        }
        let bitv: u64 = (wv >> (ru & 63u64)) & 1u64;
        let pi = bitv as i64;
        proof {
            assert(pi == 0 || pi == 1);
            assert(-v_max() < v * pi < v_max() && v * pi == if pi == 1 { v as int } else { 0int }) by (nonlinear_arith)
                requires pi == 0 || pi == 1, -v_max() < v < v_max();
        }
        let pv: i64 = v * pi;
        proof {
            let (lo, hi) = (w.lo as int, w.hi as int);
            let pr = promo_text(ptype_at(cp, lpk_at(fp, j) - 1));
            assert(pr == (bitv == 1u64));
            assert(rowval(fp, cp, 1, lo, hi, j) == if pr { 1int } else { 0int });
            assert(rowval(fp, cp, 2, lo, hi, j) == if pr { v as int } else { 0int });
            assert(js.take(t + 1).drop_last() =~= js.take(t as int));
            assert(js.take(t + 1).last() == j);
            assert((t + 1) * v_max() == t * v_max() + v_max()) by (nonlinear_arith);
        }
        pcnt = pcnt + pi;
        psum = psum + pv;
        t = t + 1;
    }
    proof {
        assert(js.take(m as int) =~= js);
    }
    (pcnt, psum)
}

/// Rows `a .. b` of lineitem group `g` of the fast scan, per block of 64 rows: every row read densely without
/// branches (`dense_block`: the count, sum and mass of the joined rows and their mask), then the joined rows' part
/// rows and values listed from the mask (`compact_block`); finally the listed rows' promotion count and sum
/// (`promo_sums`).
pub fn scan_chunk(c: &LiCols, p: &PaCols, bits: &Vec<Vec<u64>>, s: u64, rbuf: &mut Vec<u64>, vbuf: &mut Vec<i64>,
    g: usize, a: usize, b: usize, w: Win, Ghost(fp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>) -> (r: Acc)
    requires
        li_cols_ok(*c, fp),
        look_ok(*p, cp),
        bits_ok(bits@, s as int, cp),
        old(rbuf)@.len() == CHUNK,
        old(vbuf)@.len() == CHUNK,
        g < c.ng,
        group_fast_ok(*c, g as int),
        c.gs@[g as int] <= a <= b <= c.gs@[g + 1],
        b - a <= CHUNK,
    ensures
        final(rbuf)@.len() == CHUNK,
        final(vbuf)@.len() == CHUNK,
        acc_ok(r, fp, cp, w, a as int, b as int),
        acc_small(r, b - a),
    no_unwind
{
    hide(groups_wf);
    hide(zone_max_ok);
    hide(pa_shape);
    let ghost (lo, hi) = (w.lo as int, w.hi as int);
    proof {
        lemma_groups_bounds(li_gs(fp), n_li(fp), g + 1);
    }
    let len = b - a;
    let sb = c.ship_base[g];
    let s_lo = clamp_code(w.lo as i128 - sb as i128);
    let s_hi = clamp_code(w.hi as i128 - sb as i128);
    let width: u32 = if s_hi >= s_lo { s_hi - s_lo } else { 0 };
    let kb1 = c.pk_base[g] - 1;
    let np = p.n as u64;
    let pb = c.price_base[g];
    let db = c.disc_base[g];
    let mut cnt: i64 = 0;
    let mut sum: i64 = 0;
    let mut mass: i64 = 0;
    let mut m: usize = 0;
    let ghost mut js: Seq<int> = Seq::empty();
    let mut k0: usize = 0;
    proof {
        lemma_dacc_empty(fp, cp, w, a as int);
        lemma_promo_empty(fp, cp, w, a as int);
    }
    while k0 < len
        invariant
            li_cols_ok(*c, fp),
            look_ok(*p, cp),
            g < c.ng,
            group_fast_ok(*c, g as int),
            c.gs@[g as int] <= a, a + len == b, b <= c.gs@[g + 1], c.gs@[g + 1] <= c.n,
            len <= CHUNK,
            k0 <= len,
            m <= k0,
            sb == c.ship_base@[g as int],
            s_lo as int == clampi(w.lo - sb, 65536),
            s_hi as int == clampi(w.hi - sb, 65536),
            width == if s_hi >= s_lo { (s_hi - s_lo) as u32 } else { 0u32 },
            kb1 == c.pk_base@[g as int] - 1,
            np as int == n_pa(cp),
            pb == c.price_base@[g as int],
            db == c.disc_base@[g as int],
            rbuf@.len() == CHUNK,
            vbuf@.len() == CHUNK,
            dacc_ok(fp, cp, w, a as int, a + k0, cnt as int, sum as int, mass as int),
            list_ok(fp, cp, w, js, rbuf@, vbuf@, m as int),
            promo_listed(fp, cp, w, a as int, a + k0, js),
        decreases len - k0,
    {
        let nb = if len - k0 >= 64 { 64 } else { len - k0 };
        let j0 = a + k0;
        let (mask, c1, s1, m1) = dense_block(c, g, j0, nb, w, sb, s_lo, s_hi, width, kb1, np, pb, db,
            Ghost(fp), Ghost(cp));
        let (m2, Ghost(js2)) = compact_block(c, g, a, j0, nb, mask, kb1, pb, db, rbuf, vbuf, m,
            Ghost(fp), Ghost(cp), Ghost(w), Ghost(js));
        proof {
            lemma_dacc_join(fp, cp, w, a as int, j0 as int, j0 + nb, cnt as int, sum as int, mass as int,
                c1 as int, s1 as int, m1 as int);
            assert((j0 + nb - a) * v_max() <= CHUNK * v_max()) by (nonlinear_arith)
                requires j0 + nb - a <= CHUNK;
        }
        cnt = cnt + c1;
        sum = sum + s1;
        mass = mass + m1;
        m = m2;
        proof {
            js = js2;
        }
        k0 = k0 + nb;
    }
    let (pcnt, psum) = promo_sums(p, bits, s, rbuf, vbuf, m, Ghost(fp), Ghost(cp), Ghost(w), Ghost(js));
    proof {
        lemma_psum_mass(fp, cp, lo, hi, a as int, b as int);
    }
    Acc { cnt: cnt as i128, pcnt: pcnt as i128, psum: psum as i128, sum: sum as i128, mass: mass as i128 }
}

/// Group `g` lies outside the window by its zone map: every row's shipdate is in `[base, zmax]`.
pub open spec fn group_skipped(c: LiCols, w: Win, g: int) -> bool {
    c.ship_base@[g] >= w.hi || c.ship_zmax@[g] < w.lo
}

/// A skipped group contributes nothing.
pub proof fn lemma_group_skipped(c: LiCols, fp: Seq<PartView>, cp: Seq<PartView>, w: Win, g: int)
    requires
        li_cols_ok(c, fp),
        0 <= g < c.ng,
        group_skipped(c, w, g),
    ensures
        forall|k: int| 0 <= k < 6 ==> #[trigger] tot(fp, cp, k, w.lo as int, w.hi as int, c.gs@[g] as int, c.gs@[g + 1] as int) == 0,
{
    lemma_groups_bounds(li_gs(fp), n_li(fp), g + 1);
    lemma_groups_mono(li_gs(fp), n_li(fp), g, g + 1);
    assert forall|i: int| c.gs@[g] <= i < c.gs@[g + 1] implies !(w.lo <= #[trigger] ship_at(fp, i) && ship_at(fp, i) < w.hi) by {
        lemma_li_vals(c, fp, g, i);
    }
    assert forall|k: int| 0 <= k < 6 implies #[trigger] tot(fp, cp, k, w.lo as int, w.hi as int, c.gs@[g] as int, c.gs@[g + 1] as int) == 0 by {
        lemma_tot_zero(fp, cp, k, w.lo as int, w.hi as int, c.gs@[g] as int, c.gs@[g + 1] as int);
    }
}

/// `2^64 * 2^42`: a bound of the mass of any range of the fast path.
pub open spec fn range_mass_max() -> int {
    0x1_0000_0000_0000_0000 * v_max()
}

/// The fast scan of lineitem groups `g_lo .. g_hi`: `Some` totals, or `None` when a group is outside the fast
/// condition.
pub fn scan_range(c: &LiCols, p: &PaCols, bits: &Vec<Vec<u64>>, s: u64, rbuf: &mut Vec<u64>, vbuf: &mut Vec<i64>, g_lo: usize, g_hi: usize, w: Win,
    Ghost(fp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>) -> (r: Option<Acc>)
    requires
        li_cols_ok(*c, fp),
        look_ok(*p, cp),
        bits_ok(bits@, s as int, cp),
        old(rbuf)@.len() == CHUNK,
        old(vbuf)@.len() == CHUNK,
        g_lo <= g_hi <= c.ng,
    ensures
        r matches Some(a) ==> acc_ok(a, fp, cp, w, c.gs@[g_lo as int] as int, c.gs@[g_hi as int] as int)
            && acc_small(a, c.gs@[g_hi as int] - c.gs@[g_lo as int]),
    no_unwind
{
    let ghost (lo, hi) = (w.lo as int, w.hi as int);
    let ghost r0 = c.gs@[g_lo as int] as int;
    proof {
        lemma_groups_bounds(li_gs(fp), n_li(fp), g_lo as int);
        lemma_tot_empty(fp, cp, 0, lo, hi, r0);
        lemma_tot_empty(fp, cp, 1, lo, hi, r0);
        lemma_tot_empty(fp, cp, 2, lo, hi, r0);
        lemma_tot_empty(fp, cp, 3, lo, hi, r0);
        lemma_tot_empty(fp, cp, 4, lo, hi, r0);
    }
    let mut acc = Acc { cnt: 0, pcnt: 0, psum: 0, sum: 0, mass: 0 };
    let mut g = g_lo;
    while g < g_hi
        invariant
            li_cols_ok(*c, fp),
            look_ok(*p, cp),
            bits_ok(bits@, s as int, cp),
            g_lo <= g <= g_hi <= c.ng,
            rbuf@.len() == CHUNK,
            vbuf@.len() == CHUNK,
            r0 == c.gs@[g_lo as int],
            lo == w.lo, hi == w.hi,
            0 <= r0 <= c.gs@[g as int] <= c.n,
            acc_ok(acc, fp, cp, w, r0, c.gs@[g as int] as int),
            acc_small(acc, c.gs@[g as int] - r0),
        decreases g_hi - g,
    {
        let ghost r1 = c.gs@[g as int] as int;
        proof {
            lemma_groups_bounds(li_gs(fp), n_li(fp), g + 1);
            lemma_groups_mono(li_gs(fp), n_li(fp), g as int, g + 1);
        }
        let ghost r2 = c.gs@[g + 1] as int;
        if c.ship_base[g] >= w.hi || c.ship_zmax[g] < w.lo {
            proof {
                lemma_group_skipped(*c, fp, cp, w, g as int);
                assert(tot(fp, cp, 0, lo, hi, r1, r2) == 0);
                assert(tot(fp, cp, 1, lo, hi, r1, r2) == 0);
                assert(tot(fp, cp, 2, lo, hi, r1, r2) == 0);
                assert(tot(fp, cp, 3, lo, hi, r1, r2) == 0);
                assert(tot(fp, cp, 4, lo, hi, r1, r2) == 0);
                lemma_tot_split(fp, cp, 0, lo, hi, r0, r1, r2);
                lemma_tot_split(fp, cp, 1, lo, hi, r0, r1, r2);
                lemma_tot_split(fp, cp, 2, lo, hi, r0, r1, r2);
                lemma_tot_split(fp, cp, 3, lo, hi, r0, r1, r2);
                lemma_tot_split(fp, cp, 4, lo, hi, r0, r1, r2);
                assert((r1 - r0) * v_max() <= (r2 - r0) * v_max()) by (nonlinear_arith) requires r1 <= r2;
            }
        } else {
            let pbg = c.price_base[g];
            let dbg = c.disc_base[g];
            let kbg = c.pk_base[g];
            let len = c.gs[g + 1] - c.gs[g];
            if !(0 <= pbg && pbg <= 0x1_0000_0000 && 0 <= dbg && dbg <= 0x100
                && -0x100_0000_0000 <= kbg && kbg <= 0x100_0000_0000 && len <= 65536) {
                return None;
            }
            let start = c.gs[g] as usize;
            let end = c.gs[g + 1] as usize;
            let mut ga = Acc { cnt: 0, pcnt: 0, psum: 0, sum: 0, mass: 0 };
            let mut a = start;
            proof {
                lemma_tot_empty(fp, cp, 0, lo, hi, r1);
                lemma_tot_empty(fp, cp, 1, lo, hi, r1);
                lemma_tot_empty(fp, cp, 2, lo, hi, r1);
                lemma_tot_empty(fp, cp, 3, lo, hi, r1);
                lemma_tot_empty(fp, cp, 4, lo, hi, r1);
            }
            while a < end
                invariant
                    li_cols_ok(*c, fp),
                    look_ok(*p, cp),
                    bits_ok(bits@, s as int, cp),
                    rbuf@.len() == CHUNK,
                    vbuf@.len() == CHUNK,
                    g < c.ng,
                    group_fast_ok(*c, g as int),
                    start == c.gs@[g as int], end == c.gs@[g + 1], end <= c.n,
                    start == r1,
                    start <= a <= end,
                    end - start <= 65536,
                    lo == w.lo, hi == w.hi,
                    acc_ok(ga, fp, cp, w, start as int, a as int),
                    acc_small(ga, a - start),
                decreases end - a,
            {
                let bb = if end - a > CHUNK { a + CHUNK } else { end };
                let ca = scan_chunk(c, p, bits, s, rbuf, vbuf, g, a, bb, w, Ghost(fp), Ghost(cp));
                proof {
                    lemma_tot_split(fp, cp, 0, lo, hi, start as int, a as int, bb as int);
                    lemma_tot_split(fp, cp, 1, lo, hi, start as int, a as int, bb as int);
                    lemma_tot_split(fp, cp, 2, lo, hi, start as int, a as int, bb as int);
                    lemma_tot_split(fp, cp, 3, lo, hi, start as int, a as int, bb as int);
                    lemma_tot_split(fp, cp, 4, lo, hi, start as int, a as int, bb as int);
                    assert((a - start) * v_max() + (bb - a) * v_max() == (bb - start) * v_max()) by (nonlinear_arith);
                    assert((bb - start) * v_max() <= 65536 * v_max()) by (nonlinear_arith)
                        requires bb - start <= 65536;
                }
                ga = Acc {
                    cnt: ga.cnt + ca.cnt,
                    pcnt: ga.pcnt + ca.pcnt,
                    psum: ga.psum + ca.psum,
                    sum: ga.sum + ca.sum,
                    mass: ga.mass + ca.mass,
                };
                a = bb;
            }
            proof {
                lemma_tot_split(fp, cp, 0, lo, hi, r0, r1, r2);
                lemma_tot_split(fp, cp, 1, lo, hi, r0, r1, r2);
                lemma_tot_split(fp, cp, 2, lo, hi, r0, r1, r2);
                lemma_tot_split(fp, cp, 3, lo, hi, r0, r1, r2);
                lemma_tot_split(fp, cp, 4, lo, hi, r0, r1, r2);
                assert((r1 - r0) * v_max() + (r2 - r1) * v_max() == (r2 - r0) * v_max()) by (nonlinear_arith);
                assert((r2 - r0) * v_max() <= range_mass_max()) by (nonlinear_arith)
                    requires 0 <= r2 - r0 <= 0x1_0000_0000_0000_0000;
            }
            acc = Acc {
                cnt: acc.cnt + ga.cnt,
                pcnt: acc.pcnt + ga.pcnt,
                psum: acc.psum + ga.psum,
                sum: acc.sum + ga.sum,
                mass: acc.mass + ga.mass,
            };
        }
        g = g + 1;
    }
    Some(acc)
}

} // verus!
