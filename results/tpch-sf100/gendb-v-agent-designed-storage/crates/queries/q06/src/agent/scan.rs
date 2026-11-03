//! Scan of the stored lineitem row groups of storage `facts` against the normal form (`norm::qspec`).
//!
//! Layout read: per row group `g` (stored rows `gs[g] .. gs[g + 1]`), frame-of-reference columns: a row's value is
//! the group's I64 base plus its unsigned code (U16 l_shipdate days, U8 l_discount, U16 l_quantity and U32
//! l_extendedprice coefficients), and an I64 zone maximum of l_shipdate per group.
//!
//! Per group: the zone map skips a group whose shipdate range misses `[lo, hi)`; otherwise the condition is
//! evaluated on the codes against per-group code thresholds (`clampi`) and the products are summed in `u64`
//! (`group_fast`, or `group_noship` when the whole group is inside the date range) when the bases are small
//! and non-negative, else exactly in `i128` with an absolute-mass check (`group_general`).
//!
//! Every function returns the accumulators of `link::query` over its stored rows: `gsum` (exact sum of the
//! products at scale 4), `gabs` (their absolute mass) and `gcount`, or reports that the absolute mass exceeds
//! `i128` (the statement's capacity domain).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::link::query::*;
use crate::link::expr::{ival, i128_max};
use crate::gendb_entry::layout::PartView;
use crate::stores::facts::interface::*;
use crate::stores::facts::interface::common::colfmt::*;
use super::norm::*;
use super::bits::*;
use super::common::bitwords::bit64;

verus! {

/// The exact bounds of the condition (see `norm::bounds_ok`): shipdate days `[lo, hi)`, discount coefficients
/// `[dlo, dhi]`, quantity coefficients below `qhi`.
#[derive(Clone, Copy)]
pub struct Bnd {
    pub lo: i64,
    pub hi: i64,
    pub dlo: i64,
    pub dhi: i64,
    pub qhi: i64,
}

/// The normal form of the bounds.
pub open spec fn qs(b: Bnd) -> QuerySpec {
    qspec(b.lo as int, b.hi as int, b.dlo as int, b.dhi as int, b.qhi as int)
}

/// `x` clamped into `[0, hi]`.
pub open spec fn clampi(x: int, hi: int) -> int {
    if x < 0 { 0 } else if x > hi { hi } else { x }
}

/// The partial result of a range of stored rows: `(sum, abs, count, ok)`; `ok` means the three accumulators,
/// otherwise the absolute mass exceeds `i128`.
pub open spec fn partial_ok(r: (i128, i128, u64, bool), g: QuerySpec, rows: Seq<Row>) -> bool {
    if r.3 {
        &&& r.0 == gsum(g, rows, ek(), 0)
        &&& r.1 == gabs(g, rows, ek(), 0)
        &&& r.2 == gcount(g, rows, ek())
    } else {
        gabs(g, rows, ek(), 0) > i128_max()
    }
}

/// `x` clamped into `[0, hi]`, as a code threshold.
#[inline]
pub fn clamp_code(x: i128, hi: u32) -> (r: u32)
    ensures r as int == clampi(x as int, hi as int),
    no_unwind
{
    if x < 0 { 0 } else if x > hi as i128 { hi } else { x as u32 }
}

// ------------------------------------------------------------------------------------------- accumulator facts

/// Rows without a hit contribute nothing.
pub proof fn lemma_no_hits(g: QuerySpec, rows: Seq<Row>, lo: int, hi: int)
    requires
        0 <= lo <= hi <= rows.len(),
        forall|j: int| lo <= j < hi ==> !#[trigger] hit(g, rows[j], ek()),
    ensures
        gsum(g, rows.subrange(lo, hi), ek(), 0) == 0,
        gabs(g, rows.subrange(lo, hi), ek(), 0) == 0,
        gcount(g, rows.subrange(lo, hi), ek()) == 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_no_hits(g, rows, lo, hi - 1);
        lemma_range_step(g, rows, lo, hi - 1, ek(), 0);
    } else {
        lemma_empty(g, rows, lo, ek(), 0);
    }
}

/// The count is at most the number of rows.
pub proof fn lemma_gcount_le(g: QuerySpec, rows: Seq<Row>, k: Row)
    ensures gcount(g, rows, k) <= rows.len(),
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_gcount_le(g, rows.drop_last(), k);
    }
}

/// A sub-range's absolute mass bounds the mass of a range around it from below.
pub proof fn lemma_abs_mono(g: QuerySpec, rows: Seq<Row>, a: int, b: int, c: int, d: int)
    requires 0 <= a <= b <= c <= d <= rows.len(),
    ensures gabs(g, rows.subrange(b, c), ek(), 0) <= gabs(g, rows.subrange(a, d), ek(), 0),
{
    lemma_split(g, rows, a, b, d, ek(), 0);
    lemma_split(g, rows, b, c, d, ek(), 0);
    lemma_abs_bound(g, rows.subrange(a, b), ek(), 0);
    lemma_abs_bound(g, rows.subrange(c, d), ek(), 0);
}

/// One row's hit under the normal form is its condition.
pub proof fn lemma_hit(b: Bnd, x: Row)
    ensures hit(qs(b), x, ek()) == row_qual(b.lo as int, b.hi as int, b.dlo as int, b.dhi as int, b.qhi as int, x),
        (qs(b).arg)(0, x) == ival(x[1]) * ival(x[2]),
{
}

/// The condition on a decoded row is the condition on its codes against the clamped code thresholds.
pub proof fn lemma_code_qual(b: Bnd, bq: int, bp: int, bd: int, bs: int, cq: int, cp: int, cd: int, cs: int)
    requires
        0 <= cs < 65536, 0 <= cd < 256, 0 <= cq < 65536,
    ensures
        row_qual(b.lo as int, b.hi as int, b.dlo as int, b.dhi as int, b.qhi as int, li_row(bq + cq, bp + cp, bd + cd, bs + cs)) == (
            clampi(b.lo - bs, 65536) <= cs && cs < clampi(b.hi - bs, 65536)
            && clampi(b.dlo - bd, 256) <= cd && cd < clampi(b.dhi - bd + 1, 256)
            && cq < clampi(b.qhi - bq, 65536)),
{
    let x = li_row(bq + cq, bp + cp, bd + cd, bs + cs);
    assert(ival(x[0]) == bq + cq && ival(x[1]) == bp + cp && ival(x[2]) == bd + cd && ival(x[3]) == bs + cs);
}

/// Inside the date range, the condition on a decoded row is the condition on its discount and quantity codes.
pub proof fn lemma_code_qual_noship(b: Bnd, bq: int, bp: int, bd: int, s: int, cq: int, cp: int, cd: int)
    requires
        0 <= cd < 256, 0 <= cq < 65536,
        b.lo <= s < b.hi,
    ensures
        row_qual(b.lo as int, b.hi as int, b.dlo as int, b.dhi as int, b.qhi as int, li_row(bq + cq, bp + cp, bd + cd, s)) == (
            clampi(b.dlo - bd, 256) <= cd && cd < clampi(b.dhi - bd + 1, 256)
            && cq < clampi(b.qhi - bq, 65536)),
{
    let x = li_row(bq + cq, bp + cp, bd + cd, s);
    assert(ival(x[0]) == bq + cq && ival(x[1]) == bp + cp && ival(x[2]) == bd + cd && ival(x[3]) == s);
}

/// A product of a price below `2^33` and a discount below `2^9` is below `2^42`.
pub proof fn lemma_small_product(x: int, y: int)
    requires 0 <= x < 0x2_0000_0000, 0 <= y < 0x200,
    ensures 0 <= x * y < 0x400_0000_0000,
{
    assert(0 <= x * y) by (nonlinear_arith) requires 0 <= x, 0 <= y;
    assert(x * y <= x * 0x1ff) by (nonlinear_arith) requires 0 <= x, y <= 0x1ff;
}

// ------------------------------------------------------------------------------------------- group kernels

/// The decoded rows of a group: row `j` is `[bq + qty[j], bp + price[j], bd + disc[j], bs + ship[j]]`.
pub open spec fn group_rows_ok(xs: Seq<Row>, ship: Seq<u16>, disc: Seq<u8>, qty: Seq<u16>, price: Seq<u32>,
    start: int, end: int, bq: int, bp: int, bd: int, bs: int) -> bool
{
    &&& 0 <= start <= end
    &&& end <= xs.len() && end <= ship.len() && end <= disc.len() && end <= qty.len() && end <= price.len()
    &&& forall|j: int| start <= j < end ==> #[trigger] xs[j] == li_row(bq + qty[j], bp + price[j], bd + disc[j], bs + ship[j])
}

/// Sum over one group with small non-negative bases, checking the shipdate codes (vectorizable: one pass of
/// branch-free code arithmetic). Returns `(sum, count)`; the sum is also the absolute mass (every product is
/// non-negative).
#[inline]
pub fn group_fast(ship: &[u16], disc: &[u8], qty: &[u16], price: &[u32], start: usize, len: usize,
    s_lo: u32, s_hi: u32, d_lo: u32, d_hi: u32, q_hi: u32, bp: u64, bd: u64,
    Ghost(xs): Ghost<Seq<Row>>, Ghost(b): Ghost<Bnd>, Ghost(bq): Ghost<int>, Ghost(bs): Ghost<int>) -> (r: (u64, u64))
    requires
        start + len <= usize::MAX,
        group_rows_ok(xs, ship@, disc@, qty@, price@, start as int, start + len, bq, bp as int, bd as int, bs),
        len <= 65536,
        bp <= 0x1_0000_0000,
        bd <= 0x100,
        s_lo as int == clampi(b.lo - bs, 65536),
        s_hi as int == clampi(b.hi - bs, 65536),
        d_lo as int == clampi(b.dlo - bd, 256),
        d_hi as int == clampi(b.dhi - bd + 1, 256),
        q_hi as int == clampi(b.qhi - bq, 65536),
    ensures
        r.0 == gsum(qs(b), xs.subrange(start as int, start + len), ek(), 0),
        r.0 == gabs(qs(b), xs.subrange(start as int, start + len), ek(), 0),
        r.1 == gcount(qs(b), xs.subrange(start as int, start + len), ek()),
        r.1 <= len,
    no_unwind
{
    let ghost g = qs(b);
    let (_, s1) = ship.split_at(start);
    let (s, _) = s1.split_at(len);
    let (_, d1) = disc.split_at(start);
    let (d, _) = d1.split_at(len);
    let (_, q1) = qty.split_at(start);
    let (q, _) = q1.split_at(len);
    let (_, p1) = price.split_at(start);
    let (p, _) = p1.split_at(len);
    proof {
        assert(s@ =~= ship@.subrange(start as int, start + len));
        assert(d@ =~= disc@.subrange(start as int, start + len));
        assert(q@ =~= qty@.subrange(start as int, start + len));
        assert(p@ =~= price@.subrange(start as int, start + len));
        lemma_empty(g, xs, start as int, ek(), 0);
    }
    let mut acc: u64 = 0;
    let mut cnt: u64 = 0;
    let mut k: usize = 0;
    while k < len
        invariant
            k <= len,
            len <= 65536,
            bp <= 0x1_0000_0000,
            bd <= 0x100,
            s@ == ship@.subrange(start as int, start + len),
            d@ == disc@.subrange(start as int, start + len),
            q@ == qty@.subrange(start as int, start + len),
            p@ == price@.subrange(start as int, start + len),
            group_rows_ok(xs, ship@, disc@, qty@, price@, start as int, start + len, bq, bp as int, bd as int, bs),
            s_lo as int == clampi(b.lo - bs, 65536),
            s_hi as int == clampi(b.hi - bs, 65536),
            d_lo as int == clampi(b.dlo - bd, 256),
            d_hi as int == clampi(b.dhi - bd + 1, 256),
            q_hi as int == clampi(b.qhi - bq, 65536),
            g == qs(b),
            acc == gsum(g, xs.subrange(start as int, start + k), ek(), 0),
            acc == gabs(g, xs.subrange(start as int, start + k), ek(), 0),
            cnt == gcount(g, xs.subrange(start as int, start + k), ek()),
            acc <= k * 0x400_0000_0000,
            cnt <= k,
        decreases len - k,
    {
        let cs = s[k] as u32;
        let cd = d[k] as u32;
        let cq = q[k] as u32;
        let pv = p[k] as u64;
        let m = s_lo <= cs && cs < s_hi && d_lo <= cd && cd < d_hi && cq < q_hi;
        proof {
            lemma_small_product(bp + pv, bd + cd);
        }
        let v = (bp + pv) * (bd + cd as u64);
        proof {
            let j = start + k;
            assert(xs[j] == li_row(bq + q@[k as int], bp + p@[k as int], bd + d@[k as int], bs + s@[k as int]));
            lemma_code_qual(b, bq, bp as int, bd as int, bs, cq as int, pv as int, cd as int, cs as int);
            lemma_hit(b, xs[j]);
            assert(ival(xs[j][1]) * ival(xs[j][2]) == v);
            lemma_range_step(g, xs, start as int, j, ek(), 0);
            assert(xs.subrange(start as int, j + 1) == xs.subrange(start as int, start + (k + 1)));
        }
        acc = acc + if m { v } else { 0 };
        cnt = cnt + if m { 1 } else { 0 };
        k = k + 1;
    }
    (acc, cnt)
}

/// Sum over one group with small non-negative bases whose every shipdate is inside the range (the shipdate
/// codes are not read). Returns `(sum, count)`; the sum is also the absolute mass.
#[inline]
pub fn group_noship(disc: &[u8], qty: &[u16], price: &[u32], start: usize, len: usize,
    d_lo: u32, d_hi: u32, q_hi: u32, bp: u64, bd: u64,
    Ghost(xs): Ghost<Seq<Row>>, Ghost(b): Ghost<Bnd>, Ghost(bq): Ghost<int>, Ghost(bs): Ghost<int>, Ghost(ship): Ghost<Seq<u16>>) -> (r: (u64, u64))
    requires
        start + len <= usize::MAX,
        group_rows_ok(xs, ship, disc@, qty@, price@, start as int, start + len, bq, bp as int, bd as int, bs),
        forall|j: int| start <= j < start + len ==> b.lo <= bs + #[trigger] ship[j] < b.hi,
        len <= 65536,
        bp <= 0x1_0000_0000,
        bd <= 0x100,
        d_lo as int == clampi(b.dlo - bd, 256),
        d_hi as int == clampi(b.dhi - bd + 1, 256),
        q_hi as int == clampi(b.qhi - bq, 65536),
    ensures
        r.0 == gsum(qs(b), xs.subrange(start as int, start + len), ek(), 0),
        r.0 == gabs(qs(b), xs.subrange(start as int, start + len), ek(), 0),
        r.1 == gcount(qs(b), xs.subrange(start as int, start + len), ek()),
        r.1 <= len,
    no_unwind
{
    let ghost g = qs(b);
    let (_, d1) = disc.split_at(start);
    let (d, _) = d1.split_at(len);
    let (_, q1) = qty.split_at(start);
    let (q, _) = q1.split_at(len);
    let (_, p1) = price.split_at(start);
    let (p, _) = p1.split_at(len);
    proof {
        assert(d@ =~= disc@.subrange(start as int, start + len));
        assert(q@ =~= qty@.subrange(start as int, start + len));
        assert(p@ =~= price@.subrange(start as int, start + len));
        lemma_empty(g, xs, start as int, ek(), 0);
    }
    let mut acc: u64 = 0;
    let mut cnt: u64 = 0;
    let mut k: usize = 0;
    while k < len
        invariant
            k <= len,
            len <= 65536,
            bp <= 0x1_0000_0000,
            bd <= 0x100,
            d@ == disc@.subrange(start as int, start + len),
            q@ == qty@.subrange(start as int, start + len),
            p@ == price@.subrange(start as int, start + len),
            group_rows_ok(xs, ship, disc@, qty@, price@, start as int, start + len, bq, bp as int, bd as int, bs),
            forall|j: int| start <= j < start + len ==> b.lo <= bs + #[trigger] ship[j] < b.hi,
            d_lo as int == clampi(b.dlo - bd, 256),
            d_hi as int == clampi(b.dhi - bd + 1, 256),
            q_hi as int == clampi(b.qhi - bq, 65536),
            g == qs(b),
            acc == gsum(g, xs.subrange(start as int, start + k), ek(), 0),
            acc == gabs(g, xs.subrange(start as int, start + k), ek(), 0),
            cnt == gcount(g, xs.subrange(start as int, start + k), ek()),
            acc <= k * 0x400_0000_0000,
            cnt <= k,
        decreases len - k,
    {
        let cd = d[k] as u32;
        let cq = q[k] as u32;
        let pv = p[k] as u64;
        let m = d_lo <= cd && cd < d_hi && cq < q_hi;
        proof {
            lemma_small_product(bp + pv, bd + cd);
        }
        let v = (bp + pv) * (bd + cd as u64);
        proof {
            let j = start + k;
            assert(xs[j] == li_row(bq + q@[k as int], bp + p@[k as int], bd + d@[k as int], bs + ship[j]));
            assert(b.lo <= bs + ship[j] < b.hi);
            lemma_code_qual_noship(b, bq, bp as int, bd as int, bs + ship[j], cq as int, pv as int, cd as int);
            lemma_hit(b, xs[j]);
            assert(ival(xs[j][1]) * ival(xs[j][2]) == v);
            lemma_range_step(g, xs, start as int, j, ek(), 0);
            assert(xs.subrange(start as int, j + 1) == xs.subrange(start as int, start + (k + 1)));
        }
        acc = acc + if m { v } else { 0 };
        cnt = cnt + if m { 1 } else { 0 };
        k = k + 1;
    }
    (acc, cnt)
}

/// `|price| < 10^15` and `|discount| < 10^15` on the rows of a group (numeric(15, 2)).
pub open spec fn group_vals_ok(xs: Seq<Row>, start: int, end: int) -> bool {
    forall|j: int| start <= j < end ==> abs(ival(#[trigger] xs[j][1])) < p15() && abs(ival(xs[j][2])) < p15()
}

/// Exact sum over one group with any bases (`i128`; the absolute mass is checked against `i128`).
pub fn group_general(ship: &[u16], disc: &[u8], qty: &[u16], price: &[u32], start: usize, end: usize,
    bs: i64, bd: i64, bq: i64, bp: i64, b: Bnd, Ghost(xs): Ghost<Seq<Row>>) -> (r: (i128, i128, u64, bool))
    requires
        group_rows_ok(xs, ship@, disc@, qty@, price@, start as int, end as int, bq as int, bp as int, bd as int, bs as int),
        group_vals_ok(xs, start as int, end as int),
    ensures
        partial_ok(r, qs(b), xs.subrange(start as int, end as int)),
        r.3 ==> r.2 <= end - start,
    no_unwind
{
    let ghost g = qs(b);
    let mut sum: i128 = 0;
    let mut mass: i128 = 0;
    let mut cnt: u64 = 0;
    let mut j: usize = start;
    proof {
        lemma_empty(g, xs, start as int, ek(), 0);
    }
    while j < end
        invariant
            start <= j <= end,
            group_rows_ok(xs, ship@, disc@, qty@, price@, start as int, end as int, bq as int, bp as int, bd as int, bs as int),
            group_vals_ok(xs, start as int, end as int),
            g == qs(b),
            sum == gsum(g, xs.subrange(start as int, j as int), ek(), 0),
            mass == gabs(g, xs.subrange(start as int, j as int), ek(), 0),
            cnt == gcount(g, xs.subrange(start as int, j as int), ek()),
            cnt <= j - start,
        decreases end - j,
    {
        let s = bs as i128 + ship[j] as i128;
        let d = bd as i128 + disc[j] as i128;
        let q = bq as i128 + qty[j] as i128;
        let p = bp as i128 + price[j] as i128;
        let m = b.lo as i128 <= s && s < b.hi as i128 && b.dlo as i128 <= d && d <= b.dhi as i128 && q < b.qhi as i128;
        proof {
            assert(xs[j as int] == li_row(bq + qty@[j as int], bp + price@[j as int], bd + disc@[j as int], bs + ship@[j as int]));
            let x = xs[j as int];
            assert(ival(x[0]) == q && ival(x[1]) == p && ival(x[2]) == d && ival(x[3]) == s);
            lemma_hit(b, x);
            lemma_range_step(g, xs, start as int, j as int, ek(), 0);
            lemma_abs_bound(g, xs.subrange(start as int, j as int), ek(), 0);
        }
        if m {
            proof {
                assert(abs(p as int) < p15() && abs(d as int) < p15());
                assert(abs(p as int * d as int) < p15() * p15()) by (nonlinear_arith)
                    requires abs(p as int) < p15(), abs(d as int) < p15(), p15() > 0;
            }
            let v = p * d;
            let a = if v < 0 { -v } else { v };
            if mass > i128::MAX - a {
                proof {
                    lemma_abs_mono(g, xs, start as int, start as int, j + 1, end as int);
                }
                return (sum, mass, cnt, false);
            }
            sum = sum + v;
            mass = mass + a;
            cnt = cnt + 1;
        }
        j = j + 1;
    }
    (sum, mass, cnt, true)
}

// ------------------------------------------------------------------------------------------- the group scan

/// The extents the scan reads, with their lengths (slice lengths are not available in worker bodies).
#[derive(Clone, Copy)]
pub struct Cols {
    pub gs: &'static [u64],
    pub ship: &'static [u16],
    pub disc: &'static [u8],
    pub qty: &'static [u16],
    pub price: &'static [u32],
    pub ship_base: &'static [i64],
    pub ship_zmax: &'static [i64],
    pub disc_base: &'static [i64],
    pub qty_base: &'static [i64],
    pub price_base: &'static [i64],
    /// Number of row groups.
    pub ng: usize,
    /// Number of stored rows.
    pub n: usize,
}

/// The extents are the whole parts of a storage of the expected shape.
pub open spec fn cols_ok(c: Cols, parts: Seq<PartView>) -> bool {
    &&& shape_ok(parts)
    &&& c.gs@ == gsv(parts)
    &&& c.ng + 1 == c.gs@.len()
    &&& c.n == n_rows(parts)
    &&& parts[LI_SHIPDATE_CODES as int] == PartView::U16(c.ship@)
    &&& parts[LI_DISCOUNT_CODES as int] == PartView::U8(c.disc@)
    &&& parts[LI_QUANTITY_CODES as int] == PartView::U16(c.qty@)
    &&& parts[LI_EXTENDEDPRICE_CODES as int] == PartView::U32(c.price@)
    &&& parts[LI_SHIPDATE_BASE as int] == PartView::I64(c.ship_base@)
    &&& parts[LI_SHIPDATE_ZMAX as int] == PartView::I64(c.ship_zmax@)
    &&& parts[LI_DISCOUNT_BASE as int] == PartView::I64(c.disc_base@)
    &&& parts[LI_QUANTITY_BASE as int] == PartView::I64(c.qty_base@)
    &&& parts[LI_EXTENDEDPRICE_BASE as int] == PartView::I64(c.price_base@)
}

/// The rows of group `g` decoded from the extents, their value bounds and their shipdate zone.
pub proof fn lemma_group(c: Cols, parts: Seq<PartView>, g: int)
    requires cols_ok(c, parts), 0 <= g < c.ng,
    ensures ({
        let xs = xs_parts(parts);
        let (start, end) = (c.gs@[g] as int, c.gs@[g + 1] as int);
        &&& 0 <= start < end <= xs.len()
        &&& group_rows_ok(xs, c.ship@, c.disc@, c.qty@, c.price@, start, end,
                c.qty_base@[g] as int, c.price_base@[g] as int, c.disc_base@[g] as int, c.ship_base@[g] as int)
        &&& group_vals_ok(xs, start, end)
        &&& forall|j: int| start <= j < end ==> c.ship_base@[g] + #[trigger] c.ship@[j] <= c.ship_zmax@[g]
    }),
{
    let xs = xs_parts(parts);
    let gs = gsv(parts);
    let n = n_rows(parts);
    lemma_groups_bounds(gs, n, g);
    lemma_groups_bounds(gs, n, g + 1);
    assert(gs[g] < gs[g + 1]);
    assert forall|j: int| gs[g] <= j < gs[g + 1] implies #[trigger] xs[j] == li_row(c.qty_base@[g] + c.qty@[j],
        c.price_base@[g] + c.price@[j], c.disc_base@[g] + c.disc@[j], c.ship_base@[g] + c.ship@[j]) by {
        assert(in_group(gs, g, j));
        lemma_group_of_unique(gs, n, g, j);
    }
    assert forall|j: int| gs[g] <= j < gs[g + 1] implies abs(ival(#[trigger] xs[j][1])) < p15() && abs(ival(xs[j][2])) < p15() by {
        assert(abs(price_at(parts, j)) < p15());
        assert(abs(disc_at(parts, j)) < p15());
    }
    assert forall|j: int| gs[g] <= j < gs[g + 1] implies c.ship_base@[g] + #[trigger] c.ship@[j] <= c.ship_zmax@[g] by {
        assert(in_group(gs, g, j));
    }
}

/// A group whose rows fill whole words: its word range lies inside the selected bitmaps, and each of its rows
/// satisfies `row_bits_ok` (the bitmap bits are the row's discount and quantity conditions; price decoding).
pub proof fn lemma_group_bits(c: Cols, bt: Bits, b: Bnd, gi: int, parts: Seq<PartView>, bp: int)
    requires
        cols_ok(c, parts),
        bits_rows_ok(bt, b, parts),
        bt.on,
        0 <= gi < c.ng,
        c.gs@[gi] % 64 == 0,
        (c.gs@[gi + 1] - c.gs@[gi]) % 64 == 0,
        bp == c.price_base@[gi],
    ensures ({
        let start = c.gs@[gi] as int;
        let end = c.gs@[gi + 1] as int;
        let w0 = start / 64;
        let nwg = (end - start) / 64;
        &&& 64 * w0 == start && 64 * (w0 + nwg) == end
        &&& end <= c.n
        &&& bt.oa + w0 + nwg <= bt.dbits@.len() && bt.ob + w0 + nwg <= bt.dbits@.len()
        &&& bt.oc + w0 + nwg <= bt.dbits@.len() && bt.oq + w0 + nwg <= bt.qbits@.len()
        &&& w0 + nwg <= bt.nw
        &&& (gi + 1) * bt.ns <= bt.skeys@.len()
        &&& end <= c.price@.len() && end <= xs_parts(parts).len()
        &&& forall|j: int| start <= j < end ==> #[trigger] row_bits_ok(bt, b, xs_parts(parts), c.price@, bp, j)
    }),
{
    let xs = xs_parts(parts);
    let gs = gsv(parts);
    let nr = n_rows(parts);
    lemma_groups_bounds(gs, nr, gi);
    lemma_groups_bounds(gs, nr, gi + 1);
    lemma_group(c, parts, gi);
    let start = c.gs@[gi] as int;
    let end = c.gs@[gi + 1] as int;
    let w0 = start / 64;
    let nwg = (end - start) / 64;
    assert(64 * (w0 + nwg) == end);
    assert(w0 + nwg <= bt.nw) by (nonlinear_arith) requires 64 * (w0 + nwg) == end, end <= nr, nr <= bt.nw * 64;
    let ng = gs.len() - 1;
    assert((gi + 1) * bt.ns <= ng * bt.ns) by (nonlinear_arith) requires gi + 1 <= ng, bt.ns >= 0;
    assert forall|j: int| start <= j < end implies #[trigger] row_bits_ok(bt, b, xs, c.price@, bp, j) by {
        assert(xs[j] == li_row(qty_at(parts, j), price_at(parts, j), disc_at(parts, j), ship_at(parts, j)));
        assert(xs[j] == li_row(c.qty_base@[gi] + c.qty@[j], bp + c.price@[j], c.disc_base@[gi] + c.disc@[j],
            c.ship_base@[gi] + c.ship@[j]));
        assert(wbit(bt.dbits@, bt.oa as int, j) == (disc_at(parts, j) == b.dlo));
    }
}

/// `t * nw + nw <= ns * nw` for a key `t < ns`.
pub proof fn lemma_ship_offset(t: int, nw: int, ns: int)
    requires 0 <= t < ns, 0 <= nw,
    ensures 0 <= t * nw, t * nw + nw <= ns * nw,
{
    assert(0 <= t * nw) by (nonlinear_arith) requires 0 <= t, 0 <= nw;
    assert(t * nw + nw <= ns * nw) by (nonlinear_arith) requires t + 1 <= ns, 0 <= nw;
}

/// The shipdate condition of row `j` of group `gi` from the selected shipdate bitmaps or the zone map.
pub proof fn lemma_row_ship(c: Cols, bt: Bits, b: Bnd, gi: int, parts: Seq<PartView>, j: int,
    need_lo: bool, tl: int, need_hi: bool, th: int)
    requires
        cols_ok(c, parts),
        bits_rows_ok(bt, b, parts),
        bt.on,
        0 <= gi < c.ng,
        c.gs@[gi] <= j < c.gs@[gi + 1],
        need_lo == (c.ship_base@[gi] < b.lo),
        need_hi == (c.ship_zmax@[gi] >= b.hi),
        need_lo ==> 0 <= tl < bt.ns && bt.skeys@[gi * bt.ns + tl] == b.lo,
        need_hi ==> 0 <= th < bt.ns && bt.skeys@[gi * bt.ns + th] == b.hi,
    ensures
        row_ship_ok(bt, b, xs_parts(parts), need_lo, if need_lo { tl * bt.nw } else { th * bt.nw },
            need_hi, if need_hi { th * bt.nw } else if need_lo { tl * bt.nw } else { th * bt.nw }, j),
{
    let xs = xs_parts(parts);
    let gs = gsv(parts);
    let nr = n_rows(parts);
    lemma_groups_bounds(gs, nr, gi);
    lemma_groups_bounds(gs, nr, gi + 1);
    lemma_group(c, parts, gi);
    assert(in_group(gs, gi, j));
    lemma_group_of_unique(gs, nr, gi, j);
    assert(xs[j] == li_row(qty_at(parts, j), price_at(parts, j), disc_at(parts, j), ship_at(parts, j)));
    assert(xs[j] == li_row(c.qty_base@[gi] + c.qty@[j], c.price_base@[gi] + c.price@[j],
        c.disc_base@[gi] + c.disc@[j], c.ship_base@[gi] + c.ship@[j]));
    assert(c.ship_base@[gi] + c.ship@[j] <= c.ship_zmax@[gi]);
    if need_lo {
        assert(wbit(bt.sbits@, tl * bt.nw, j) == (ship_at(parts, j) < bt.skeys@[gi * bt.ns + tl]));
    }
    if need_hi {
        assert(wbit(bt.sbits@, th * bt.nw, j) == (ship_at(parts, j) < bt.skeys@[gi * bt.ns + th]));
    }
}

/// Words `off .. off + len` of a bitmap part.
#[inline(always)]
pub fn sub_words(v: &'static [u64], off: usize, len: usize) -> (r: &'static [u64])
    requires off + len <= v@.len(),
    ensures r@ == v@.subrange(off as int, off + len),
    no_unwind
{
    let (_, t) = v.split_at(off);
    let (r, _) = t.split_at(len);
    proof {
        assert(r@ =~= v@.subrange(off as int, off + len));
    }
    r
}

/// The bitmap words of a plan state, for each of its rows, the row's discount, quantity and shipdate conditions
/// and its price code (`gw_bit_ok`), from what the selected bitmaps state about facts' stored rows.
pub proof fn lemma_plan_bits(c: Cols, bt: Bits, b: Bnd, gi: int, parts: Seq<PartView>, gw: Gw, tl: int, th: int)
    requires
        cols_ok(c, parts),
        bits_rows_ok(bt, b, parts),
        bt.on,
        0 <= gi < c.ng,
        c.gs@[gi] % 64 == 0,
        (c.gs@[gi + 1] - c.gs@[gi]) % 64 == 0,
        gw.bp == c.price_base@[gi],
        64 * gw.w0 == c.gs@[gi],
        64 * (gw.w0 + gw.nwg) == c.gs@[gi + 1],
        gw.a@ == bt.dbits@.subrange(bt.oa + gw.w0, bt.oa + gw.w0 + gw.nwg),
        gw.b@ == bt.dbits@.subrange(bt.ob + gw.w0, bt.ob + gw.w0 + gw.nwg),
        gw.c@ == bt.dbits@.subrange(bt.oc + gw.w0, bt.oc + gw.w0 + gw.nwg),
        gw.q@ == bt.qbits@.subrange(bt.oq + gw.w0, bt.oq + gw.w0 + gw.nwg),
        gw.need_lo == (c.ship_base@[gi] < b.lo),
        gw.need_hi == (c.ship_zmax@[gi] >= b.hi),
        gw.need_lo ==> 0 <= tl < bt.ns && bt.skeys@[gi * bt.ns + tl] == b.lo
            && gw.l@ == bt.sbits@.subrange(tl * bt.nw + gw.w0, tl * bt.nw + gw.w0 + gw.nwg),
        gw.need_hi ==> 0 <= th < bt.ns && bt.skeys@[gi * bt.ns + th] == b.hi
            && gw.h@ == bt.sbits@.subrange(th * bt.nw + gw.w0, th * bt.nw + gw.w0 + gw.nwg),
    ensures
        forall|k: int, i: int| 0 <= k < gw.nwg && 0 <= i < 64 ==> #[trigger] gw_bit_ok(gw, b, xs_parts(parts), c.price@, k, i),
{
    let xs = xs_parts(parts);
    lemma_group_bits(c, bt, b, gi, parts, gw.bp as int);
    if gw.need_lo { lemma_ship_offset(tl, bt.nw as int, bt.ns as int); }
    if gw.need_hi { lemma_ship_offset(th, bt.nw as int, bt.ns as int); }
    assert forall|k: int, i: int| 0 <= k < gw.nwg && 0 <= i < 64 implies #[trigger] gw_bit_ok(gw, b, xs, c.price@, k, i) by {
        let w = gw.w0 + k;
        let j = 64 * w + i;
        assert(c.gs@[gi] <= j < c.gs@[gi + 1]);
        assert(row_bits_ok(bt, b, xs, c.price@, gw.bp as int, j));
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(j, 64, w, i);
        assert(j / 64 == w && j % 64 == i);
        lemma_row_ship(c, bt, b, gi, parts, j, gw.need_lo, tl, gw.need_hi, th);
        assert(gw.a@[k] == bt.dbits@[bt.oa + w]);
        assert(gw.b@[k] == bt.dbits@[bt.ob + w]);
        assert(gw.c@[k] == bt.dbits@[bt.oc + w]);
        assert(gw.q@[k] == bt.qbits@[bt.oq + w]);
        assert(wbit(bt.dbits@, bt.oa as int, j) == bit64(bt.dbits@[bt.oa + w], i));
        assert(wbit(bt.dbits@, bt.ob as int, j) == bit64(bt.dbits@[bt.ob + w], i));
        assert(wbit(bt.dbits@, bt.oc as int, j) == bit64(bt.dbits@[bt.oc + w], i));
        assert(wbit(bt.qbits@, bt.oq as int, j) == bit64(bt.qbits@[bt.oq + w], i));
        if gw.need_lo {
            assert(gw.l@[k] == bt.sbits@[tl * bt.nw + w]);
            assert(wbit(bt.sbits@, tl * bt.nw, j) == bit64(bt.sbits@[tl * bt.nw + w], i));
        }
        if gw.need_hi {
            assert(gw.h@[k] == bt.sbits@[th * bt.nw + w]);
            assert(wbit(bt.sbits@, th * bt.nw, j) == bit64(bt.sbits@[th * bt.nw + w], i));
        }
    }
}

/// The bitmap plan of group `gi`: when the bitmaps serve the binding, the zone map does not skip the group, its
/// rows fill whole 64-row words, its price base is small and non-negative and the shipdate keys it needs exist.
pub fn group_plan(c: Cols, bt: Bits, gi: usize, b: Bnd, Ghost(parts): Ghost<Seq<PartView>>) -> (r: Option<Gw>)
    requires
        cols_ok(c, parts),
        bits_rows_ok(bt, b, parts),
        gi < c.ng,
    ensures
        r matches Some(gw) ==> {
            &&& gw_ok(gw, bt.dlo, b, xs_parts(parts), c.price@)
            &&& 64 * gw.w0 == c.gs@[gi as int]
            &&& 64 * (gw.w0 + gw.nwg) == c.gs@[gi + 1]
        },
    no_unwind
{
    proof {
        lemma_groups_bounds(gsv(parts), n_rows(parts), gi as int);
        lemma_groups_bounds(gsv(parts), n_rows(parts), gi + 1);
        lemma_group(c, parts, gi as int);
    }
    let start = c.gs[gi] as usize;
    let end = c.gs[gi + 1] as usize;
    let sb = c.ship_base[gi];
    let sz = c.ship_zmax[gi];
    let bp = c.price_base[gi];
    let len = end - start;
    if !(bt.on && sb < b.hi && sz >= b.lo && start % 64 == 0 && len % 64 == 0 && len <= 65536 && 0 <= bp
        && bp <= 0x1_0000_0000) {
        return None;
    }
    let w0 = start / 64;
    let nwg = len / 64;
    proof {
        lemma_group_bits(c, bt, b, gi as int, parts, bp as int);
    }
    let need_lo = sb < b.lo;
    let need_hi = sz >= b.hi;
    let tl = if need_lo { find_ship_key(bt, gi, b.lo) } else { Some(0) };
    let th = if need_hi { find_ship_key(bt, gi, b.hi) } else { Some(0) };
    let (tl, th) = match (tl, th) {
        (Some(x), Some(y)) => (x, y),
        _ => { return None; }
    };
    let a = sub_words(bt.dbits, bt.oa + w0, nwg);
    let bb = sub_words(bt.dbits, bt.ob + w0, nwg);
    let cc = sub_words(bt.dbits, bt.oc + w0, nwg);
    let q = sub_words(bt.qbits, bt.oq + w0, nwg);
    proof {
        if need_lo { lemma_ship_offset(tl as int, bt.nw as int, bt.ns as int); }
        if need_hi { lemma_ship_offset(th as int, bt.nw as int, bt.ns as int); }
    }
    let l = if need_lo { sub_words(bt.sbits, tl * bt.nw + w0, nwg) } else { q };
    let h = if need_hi { sub_words(bt.sbits, th * bt.nw + w0, nwg) } else { q };
    let ml: u64 = if need_lo { !0u64 } else { 0u64 };
    let xh: u64 = if need_hi { 0u64 } else { !0u64 };
    let gw = Gw { a, b: bb, c: cc, q, l, h, w0, nwg, bp: bp as u64, ml, xh, need_lo, need_hi };
    proof {
        lemma_plan_bits(c, bt, b, gi as int, parts, gw, tl as int, th as int);
    }
    Some(gw)
}

/// Groups `gi` and `gi + 1` scanned together through their bitmap plans (`bits::gw_pair`), when both have one:
/// `(sum, count)` of their rows; the sum is also the absolute mass.
#[inline(always)]
pub fn pair_step(c: Cols, bt: Bits, gi: usize, b: Bnd, fast: bool, Ghost(parts): Ghost<Seq<PartView>>) -> (r: Option<(u64, u64)>)
    requires
        cols_ok(c, parts),
        bits_rows_ok(bt, b, parts),
        gi + 1 < c.ng,
    ensures
        r matches Some(p) ==> {
            let rows = xs_parts(parts).subrange(c.gs@[gi as int] as int, c.gs@[gi + 2] as int);
            &&& p.0 == gsum(qs(b), rows, ek(), 0)
            &&& p.0 == gabs(qs(b), rows, ek(), 0)
            &&& p.1 == gcount(qs(b), rows, ek())
            &&& p.0 <= 0x800_0000_0000_0000
            &&& p.1 <= c.gs@[gi + 2] - c.gs@[gi as int]
        },
    no_unwind when !fast
{
    let ghost xs = xs_parts(parts);
    let p1 = group_plan(c, bt, gi, b, Ghost(parts));
    let g1 = match p1 {
        Some(g1) => g1,
        None => { return None; }
    };
    let p2 = group_plan(c, bt, gi + 1, b, Ghost(parts));
    let g2 = match p2 {
        Some(g2) => g2,
        None => { return None; }
    };
    let (s1, k1, s2, k2) = gw_pair(g1, g2, c.price, bt.dlo, fast, Ghost(xs), Ghost(b));
    proof {
        let gs = c.gs@;
        assert(gw_rows(g1, xs, 0, g1.nwg as int) == xs.subrange(gs[gi as int] as int, gs[gi + 1] as int));
        assert(gw_rows(g2, xs, 0, g2.nwg as int) == xs.subrange(gs[gi + 1] as int, gs[gi + 2] as int));
        lemma_split(qs(b), xs, gs[gi as int] as int, gs[gi + 1] as int, gs[gi + 2] as int, ek(), 0);
    }
    Some((s1 + s2, k1 + k2))
}

/// The partial result of the stored rows of group `gi`.
pub fn group_partial(c: Cols, bt: Bits, gi: usize, b: Bnd, Ghost(parts): Ghost<Seq<PartView>>) -> (r: (i128, i128, u64, bool))
    requires
        cols_ok(c, parts),
        bits_rows_ok(bt, b, parts),
        gi < c.ng,
    ensures
        partial_ok(r, qs(b), xs_parts(parts).subrange(c.gs@[gi as int] as int, c.gs@[gi + 1] as int)),
        r.3 ==> r.2 <= c.gs@[gi + 1] - c.gs@[gi as int],
        r.3 ==> 0 <= r.1,
    no_unwind
{
    let ghost g = qs(b);
    let ghost xs = xs_parts(parts);
    proof {
        lemma_groups_bounds(gsv(parts), n_rows(parts), gi as int);
        lemma_groups_bounds(gsv(parts), n_rows(parts), gi + 1);
        lemma_group(c, parts, gi as int);
    }
    let start = c.gs[gi] as usize;
    let end = c.gs[gi + 1] as usize;
    let sb = c.ship_base[gi];
    let sz = c.ship_zmax[gi];
    let ghost bq = c.qty_base@[gi as int] as int;
    let ghost bs = sb as int;
    if !(sb < b.hi && sz >= b.lo) {
        // zone map: every shipdate of the group is outside [lo, hi)
        proof {
            assert forall|j: int| start <= j < end implies !#[trigger] hit(g, xs[j], ek()) by {
                lemma_hit(b, xs[j]);
                assert(ival(xs[j][3]) == sb + c.ship@[j]);
            }
            lemma_no_hits(g, xs, start as int, end as int);
        }
        return (0, 0, 0, true);
    }
    let bd = c.disc_base[gi];
    let bqe = c.qty_base[gi];
    let bp = c.price_base[gi];
    let len = end - start;
    match group_plan(c, bt, gi, b, Ghost(parts)) {
        Some(gw) => {
            let (s_g, c_g) = gw_run(gw, c.price, bt.dlo, 0, gw.nwg, false, Ghost(xs), Ghost(b));
            proof {
                assert(gw_rows(gw, xs, 0, gw.nwg as int) == xs.subrange(start as int, end as int));
            }
            return (s_g as i128, s_g as i128, c_g, true);
        }
        None => {}
    }
    if 0 <= bp && bp <= 0x1_0000_0000 && 0 <= bd && bd <= 0x100 && len <= 65536 {
        let dl = clamp_code(b.dlo as i128 - bd as i128, 256);
        let dh = clamp_code(b.dhi as i128 - bd as i128 + 1, 256);
        let qh = clamp_code(b.qhi as i128 - bqe as i128, 65536);
        let (s_g, c_g) = if sb >= b.lo && sz < b.hi {
            group_noship(c.disc, c.qty, c.price, start, len, dl, dh, qh, bp as u64, bd as u64,
                Ghost(xs), Ghost(b), Ghost(bq), Ghost(bs), Ghost(c.ship@))
        } else {
            let sl = clamp_code(b.lo as i128 - sb as i128, 65536);
            let sh = clamp_code(b.hi as i128 - sb as i128, 65536);
            group_fast(c.ship, c.disc, c.qty, c.price, start, len, sl, sh, dl, dh, qh, bp as u64, bd as u64,
                Ghost(xs), Ghost(b), Ghost(bq), Ghost(bs))
        };
        (s_g as i128, s_g as i128, c_g, true)
    } else {
        let r = group_general(c.ship, c.disc, c.qty, c.price, start, end, sb, bd, bqe, bp, b, Ghost(xs));
        proof {
            lemma_abs_bound(g, xs.subrange(start as int, end as int), ek(), 0);
        }
        r
    }
}

/// The partial result of the stored rows of groups `g_lo .. g_hi`. `fast`: the bit-index instruction that may
/// unwind is allowed (the calling thread; workers pass `false`). Inlined into both callers, so `fast` is a
/// constant in each copy.
#[inline(always)]
pub fn scan_groups(c: Cols, bt: Bits, g_lo: usize, g_hi: usize, b: Bnd, fast: bool, Ghost(parts): Ghost<Seq<PartView>>)
    -> (r: (i128, i128, u64, bool))
    requires
        cols_ok(c, parts),
        bits_rows_ok(bt, b, parts),
        g_lo <= g_hi <= c.ng,
    ensures
        partial_ok(r, qs(b), xs_parts(parts).subrange(c.gs@[g_lo as int] as int, c.gs@[g_hi as int] as int)),
        r.3 ==> r.2 <= c.gs@[g_hi as int] - c.gs@[g_lo as int],
    no_unwind when !fast
{
    let ghost g = qs(b);
    let ghost xs = xs_parts(parts);
    let ghost gs = gsv(parts);
    let ghost nr = n_rows(parts);
    let ghost r0 = gs[g_lo as int] as int;
    let ghost r1 = gs[g_hi as int] as int;
    proof {
        lemma_groups_bounds(gs, nr, g_lo as int);
        lemma_groups_bounds(gs, nr, g_hi as int);
        if g_lo < g_hi {
            lemma_groups_mono(gs, nr, g_lo as int, g_hi as int);
        }
        lemma_empty(g, xs, r0, ek(), 0);
    }
    let mut sum: i128 = 0;
    let mut mass: i128 = 0;
    let mut cnt: u64 = 0;
    let mut gi: usize = g_lo;
    while gi < g_hi
        invariant
            cols_ok(c, parts),
            bits_rows_ok(bt, b, parts),
            g_lo <= gi <= g_hi <= c.ng,
            g == qs(b),
            xs == xs_parts(parts),
            gs == gsv(parts),
            nr == n_rows(parts),
            gs == c.gs@,
            r0 == gs[g_lo as int],
            r1 == gs[g_hi as int],
            r0 <= gs[gi as int] <= r1 <= xs.len(),
            sum == gsum(g, xs.subrange(r0, gs[gi as int] as int), ek(), 0),
            mass == gabs(g, xs.subrange(r0, gs[gi as int] as int), ek(), 0),
            cnt == gcount(g, xs.subrange(r0, gs[gi as int] as int), ek()),
            cnt <= gs[gi as int] - r0,
        decreases g_hi - gi,
    {
        let ghost start = gs[gi as int] as int;
        let step = if gi + 1 < g_hi { pair_step(c, bt, gi, b, fast, Ghost(parts)) } else { None };
        match step {
            Some((s2, k2)) => {
                // groups gi and gi + 1 together
                let ghost end2 = gs[gi + 2] as int;
                proof {
                    lemma_groups_bounds(gs, nr, gi + 2);
                    lemma_groups_mono(gs, nr, gi as int, gi + 2);
                    if gi + 2 < g_hi {
                        lemma_groups_mono(gs, nr, gi + 2, g_hi as int);
                    }
                    lemma_split(g, xs, r0, start, end2, ek(), 0);
                    lemma_abs_bound(g, xs.subrange(r0, start), ek(), 0);
                }
                if mass > i128::MAX - s2 as i128 {
                    proof {
                        lemma_abs_mono(g, xs, r0, r0, end2, r1);
                    }
                    return (sum, mass, cnt, false);
                }
                sum = sum + s2 as i128;
                mass = mass + s2 as i128;
                cnt = cnt + k2;
                gi = gi + 2;
            }
            None => {
                let ghost end = gs[gi + 1] as int;
                let (s_g, a_g, c_g, ok) = group_partial(c, bt, gi, b, Ghost(parts));
                proof {
                    lemma_groups_bounds(gs, nr, gi + 1);
                    if gi + 1 < g_hi {
                        lemma_groups_mono(gs, nr, gi + 1, g_hi as int);
                    }
                    lemma_split(g, xs, r0, start, end, ek(), 0);
                    lemma_abs_bound(g, xs.subrange(r0, start), ek(), 0);
                }
                if !ok {
                    proof {
                        lemma_abs_mono(g, xs, r0, start, end, r1);
                    }
                    return (sum, mass, cnt, false);
                }
                if mass > i128::MAX - a_g {
                    proof {
                        lemma_abs_mono(g, xs, r0, r0, end, r1);
                    }
                    return (sum, mass, cnt, false);
                }
                proof {
                    lemma_abs_bound(g, xs.subrange(r0, end), ek(), 0);
                }
                sum = sum + s_g;
                mass = mass + a_g;
                cnt = cnt + c_g;
                gi = gi + 1;
            }
        }
    }
    (sum, mass, cnt, true)
}

} // verus!
