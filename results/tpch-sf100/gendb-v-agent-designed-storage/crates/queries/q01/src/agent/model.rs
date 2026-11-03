//! Integer model of the stored lineitem columns Q1 reads (storage `facts`): the code and base sequences of the
//! frame-of-reference columns, the decoded value of every stored row, its group index and the spec sums the
//! kernels compute (`isum`), by stored row range.
//!
//! Stored row `j` lies in block `j / bsize`; its value of a FOR column is `base[j / bsize] + code[j]`. The group
//! index of a row is `rfi * nls + lsi` (dictionary indices of l_returnflag and l_linestatus; `lsi < nls`).
//! Value kinds `w`: 0 quantity, 1 extended price, 2 price * (100 - discount), 3 price * (100 - discount) *
//! (100 + tax), 4 discount (coefficients at scales 2, 2, 4, 6, 2), 5 the count (1 per row).
use vstd::prelude::*;
use super::common::csum::*;

verus! {

pub struct Model {
    pub qty: Seq<u16>,
    pub qty_b: Seq<i64>,
    pub price: Seq<u32>,
    pub price_b: Seq<i64>,
    pub disc: Seq<u8>,
    pub disc_b: Seq<i64>,
    pub tax: Seq<u8>,
    pub tax_b: Seq<i64>,
    pub rf: Seq<u8>,
    pub rf_b: Seq<u64>,
    pub ls: Seq<u8>,
    pub ls_b: Seq<u64>,
    pub ship: Seq<u16>,
    pub ship_b: Seq<i64>,
    pub ship_z: Seq<i64>,
    /// Stored rows.
    pub n: int,
    /// Rows per block.
    pub bsize: int,
    /// Blocks.
    pub nb: int,
    /// Dictionary sizes of l_returnflag and l_linestatus.
    pub nrf: int,
    pub nls: int,
}

pub open spec fn blk(m: Model, j: int) -> int {
    j / m.bsize
}

pub open spec fn qv(m: Model, j: int) -> int {
    m.qty_b[blk(m, j)] + m.qty[j]
}

pub open spec fn pv(m: Model, j: int) -> int {
    m.price_b[blk(m, j)] + m.price[j]
}

pub open spec fn dv(m: Model, j: int) -> int {
    m.disc_b[blk(m, j)] + m.disc[j]
}

pub open spec fn tv(m: Model, j: int) -> int {
    m.tax_b[blk(m, j)] + m.tax[j]
}

pub open spec fn shv(m: Model, j: int) -> int {
    m.ship_b[blk(m, j)] + m.ship[j]
}

pub open spec fn rfi(m: Model, j: int) -> int {
    m.rf_b[blk(m, j)] + m.rf[j]
}

pub open spec fn lsi(m: Model, j: int) -> int {
    m.ls_b[blk(m, j)] + m.ls[j]
}

/// The group index of row `j`.
pub open spec fn gidx(m: Model, j: int) -> int {
    rfi(m, j) * m.nls + lsi(m, j)
}

/// Value kind `w` of row `j`.
pub open spec fn mval(m: Model, w: int, j: int) -> int {
    if w == 0 {
        qv(m, j)
    } else if w == 1 {
        pv(m, j)
    } else if w == 2 {
        pv(m, j) * (100 - dv(m, j))
    } else if w == 3 {
        pv(m, j) * (100 - dv(m, j)) * (100 + tv(m, j))
    } else if w == 4 {
        dv(m, j)
    } else {
        1
    }
}

/// Row `j` passes `l_shipdate <= p` and lies in group `t`.
pub open spec fn msel(m: Model, p: int, t: int, j: int) -> bool {
    shv(m, j) <= p && gidx(m, j) == t
}

/// Sum of value kind `w` over the rows `lo .. hi` of group `t` that pass the date bound.
pub open spec fn isum(m: Model, p: int, t: int, w: int, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { isum(m, p, t, w, lo, hi - 1) + if msel(m, p, t, hi - 1) { mval(m, w, hi - 1) } else { 0 } }
}

/// The shape of the model: every code sequence holds `n` rows, every base and zone sequence `nb` blocks of
/// `bsize` rows, zone maxima bound the shipdates, dictionary indices lie in their dictionaries.
pub open spec fn model_wf(m: Model) -> bool {
    &&& m.n >= 0 && m.bsize >= 1 && m.nb >= 0
    &&& m.nb * m.bsize >= m.n
    &&& m.qty.len() == m.n && m.price.len() == m.n && m.disc.len() == m.n && m.tax.len() == m.n
    &&& m.rf.len() == m.n && m.ls.len() == m.n && m.ship.len() == m.n
    &&& m.qty_b.len() == m.nb && m.price_b.len() == m.nb && m.disc_b.len() == m.nb && m.tax_b.len() == m.nb
    &&& m.rf_b.len() == m.nb && m.ls_b.len() == m.nb && m.ship_b.len() == m.nb && m.ship_z.len() == m.nb
    &&& m.nrf >= 0 && m.nls >= 1
    &&& forall|j: int| 0 <= j < m.n ==> #[trigger] shv(m, j) <= m.ship_z[blk(m, j)]
    &&& forall|j: int| 0 <= j < m.n ==> 0 <= #[trigger] rfi(m, j) < m.nrf
    &&& forall|j: int| 0 <= j < m.n ==> 0 <= #[trigger] lsi(m, j) < m.nls
}

/// The fast path's bounds on the bases of block `g` (they make every row value small).
pub open spec fn block_ok(m: Model, g: int) -> bool {
    &&& -0x1_0000_0000 <= m.qty_b[g] <= 0x1_0000_0000
    &&& -0x1_0000_0000 <= m.price_b[g] <= 0x1_0000_0000
    &&& 0 <= m.disc_b[g] <= 100
    &&& 0 <= m.tax_b[g] <= 100
    &&& -0x100_0000_0000 <= m.ship_b[g] <= 0x100_0000_0000
    &&& m.rf_b[g] <= 0x1_0000_0000
    &&& m.ls_b[g] <= 0x1_0000_0000
}

/// The bound on value kind `w` of a row of a block with `block_ok`.
pub open spec fn vbound(w: int) -> int {
    if w == 0 || w == 1 {
        0x2_0000_0000
    } else if w == 2 {
        0x200_0000_0000
    } else if w == 3 {
        0x4_0000_0000_0000
    } else if w == 4 {
        512
    } else {
        1
    }
}

/// Row `j` lies in block `blk(m, j)`, a block of the model.
pub proof fn lemma_blk(m: Model, j: int)
    requires model_wf(m), 0 <= j < m.n,
    ensures 0 <= blk(m, j) < m.nb, blk(m, j) * m.bsize <= j < (blk(m, j) + 1) * m.bsize,
{
    let b = m.bsize;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, b);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(j, b);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(j, b);
    assert(b * (j / b) == (j / b) * b) by (nonlinear_arith);
    assert((j / b + 1) * b == (j / b) * b + b) by (nonlinear_arith);
    if j / b >= m.nb {
        assert((j / b) * b >= m.nb * b) by (nonlinear_arith) requires j / b >= m.nb, b >= 1;
    }
}

/// The rows of block `g`: `blk` of every row in `g * bsize .. (g + 1) * bsize` is `g`.
pub proof fn lemma_blk_of(m: Model, g: int, j: int)
    requires m.bsize >= 1, g >= 0, g * m.bsize <= j < (g + 1) * m.bsize,
    ensures blk(m, j) == g,
{
    let b = m.bsize;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, b);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(j, b);
    assert(b * (j / b) == (j / b) * b) by (nonlinear_arith);
    let q = j / b;
    if q < g {
        assert(q * b + b <= g * b) by (nonlinear_arith) requires q + 1 <= g, b >= 1;
    } else if q > g {
        assert(q * b >= (g + 1) * b) by (nonlinear_arith) requires q >= g + 1, b >= 1;
    }
}

/// The value kinds of a row of a block with `block_ok` are within `vbound`.
pub proof fn lemma_row_bounds(m: Model, j: int, w: int)
    requires model_wf(m), 0 <= j < m.n, block_ok(m, blk(m, j)), 0 <= w <= 5,
    ensures -vbound(w) <= mval(m, w, j) <= vbound(w),
{
    lemma_blk(m, j);
    let (p, d, t) = (pv(m, j), dv(m, j), tv(m, j));
    assert(-0x2_0000_0000 <= p <= 0x2_0000_0000);
    assert(0 <= d <= 355 && 0 <= t <= 355);
    let x = 100 - d;
    let y = 100 + t;
    assert(-255 <= x <= 100 && 100 <= y <= 455);
    assert(-0x200_0000_0000 <= p * x <= 0x200_0000_0000) by (nonlinear_arith)
        requires -0x2_0000_0000 <= p <= 0x2_0000_0000, -255 <= x <= 100;
    assert(-0x4_0000_0000_0000 <= p * x * y <= 0x4_0000_0000_0000) by (nonlinear_arith)
        requires -0x200_0000_0000 <= p * x <= 0x200_0000_0000, 100 <= y <= 455;
}

/// One more row at the end of the range.
pub proof fn lemma_isum_step(m: Model, p: int, t: int, w: int, lo: int, hi: int)
    requires lo <= hi,
    ensures isum(m, p, t, w, lo, hi + 1) == isum(m, p, t, w, lo, hi) + if msel(m, p, t, hi) { mval(m, w, hi) } else { 0 },
{
}

/// The empty range.
pub proof fn lemma_isum_empty(m: Model, p: int, t: int, w: int, lo: int)
    ensures isum(m, p, t, w, lo, lo) == 0,
{
}

/// Adjacent ranges add.
pub proof fn lemma_isum_split(m: Model, p: int, t: int, w: int, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures isum(m, p, t, w, lo, hi) == isum(m, p, t, w, lo, mid) + isum(m, p, t, w, mid, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_isum_split(m, p, t, w, lo, mid, hi - 1);
    }
}

/// A chunk of rows `c0 .. c0 + len` summed by a selection and value over chunk positions that agree with the
/// model row by row.
pub proof fn lemma_isum_csum(m: Model, p: int, t: int, w: int, c0: int, len: int, sel: spec_fn(int) -> bool,
    val: spec_fn(int) -> int)
    requires
        len >= 0,
        forall|i: int| 0 <= i < len ==> #[trigger] sel(i) == msel(m, p, t, c0 + i),
        forall|i: int| 0 <= i < len && sel(i) ==> #[trigger] val(i) == mval(m, w, c0 + i),
    ensures isum(m, p, t, w, c0, c0 + len) == csum(sel, val, len),
    decreases len,
{
    if len > 0 {
        lemma_isum_csum(m, p, t, w, c0, len - 1, sel, val);
        assert(sel(len - 1) == msel(m, p, t, c0 + (len - 1)));
    }
}

/// A range without a selected row sums to 0.
pub proof fn lemma_isum_none(m: Model, p: int, t: int, w: int, lo: int, hi: int)
    requires forall|j: int| lo <= j < hi ==> !#[trigger] msel(m, p, t, j),
    ensures isum(m, p, t, w, lo, hi) == 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_isum_none(m, p, t, w, lo, hi - 1);
        assert(!msel(m, p, t, hi - 1));
    }
}

/// Bounds of a sum over rows of blocks with `block_ok`.
pub proof fn lemma_isum_bound(m: Model, p: int, t: int, w: int, lo: int, hi: int)
    requires
        model_wf(m), 0 <= lo <= hi <= m.n, 0 <= w <= 5,
        forall|j: int| lo <= j < hi ==> #[trigger] block_ok(m, blk(m, j)),
    ensures
        -((hi - lo) * vbound(w)) <= isum(m, p, t, w, lo, hi) <= (hi - lo) * vbound(w),
        w == 5 ==> 0 <= isum(m, p, t, w, lo, hi) <= hi - lo,
    decreases hi - lo,
{
    if hi > lo {
        lemma_isum_bound(m, p, t, w, lo, hi - 1);
        assert(block_ok(m, blk(m, hi - 1)));
        lemma_row_bounds(m, hi - 1, w);
        assert((hi - lo) * vbound(w) == (hi - 1 - lo) * vbound(w) + vbound(w)) by (nonlinear_arith);
    }
}

/// Rows of blocks `a .. b` lie in blocks `a .. b`.
pub proof fn lemma_blk_range(m: Model, j: int, a: int, b: int)
    requires m.bsize >= 1, 0 <= a, a * m.bsize <= j < b * m.bsize,
    ensures a <= blk(m, j) < b,
{
    let bs = m.bsize;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, bs);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(j, bs);
    assert(bs * (j / bs) == (j / bs) * bs) by (nonlinear_arith);
    let q = j / bs;
    if q < a {
        assert(q * bs + bs <= a * bs) by (nonlinear_arith) requires q + 1 <= a, bs >= 1;
    }
    if q >= b {
        assert(q * bs >= b * bs) by (nonlinear_arith) requires q >= b, bs >= 1;
    }
}

/// Blocks before the last start before row `n`.
pub proof fn lemma_block_starts(m: Model, g: int)
    requires model_wf(m), m.nb * m.bsize < m.n + m.bsize, 0 <= g < m.nb,
    ensures g * m.bsize < m.n, (g + 1) * m.bsize <= m.n + m.bsize - 1 + m.bsize,
{
    assert(g * m.bsize <= (m.nb - 1) * m.bsize) by (nonlinear_arith) requires g <= m.nb - 1, m.bsize >= 1;
    assert((m.nb - 1) * m.bsize == m.nb * m.bsize - m.bsize) by (nonlinear_arith);
    assert((g + 1) * m.bsize == g * m.bsize + m.bsize) by (nonlinear_arith);
}

// ------------------------------------------------------------------------------------------------ sums by key

/// Row `j` passes the date bound and holds the dictionary indices `(a, b)`.
pub open spec fn ksel(m: Model, p: int, a: int, b: int, j: int) -> bool {
    shv(m, j) <= p && rfi(m, j) == a && lsi(m, j) == b
}

/// Sum of value kind `w` over the rows `lo .. hi` of key `(a, b)` that pass the date bound.
pub open spec fn ksum(m: Model, p: int, a: int, b: int, w: int, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { ksum(m, p, a, b, w, lo, hi - 1) + if ksel(m, p, a, b, hi - 1) { mval(m, w, hi - 1) } else { 0 } }
}

pub open spec fn abs_int(x: int) -> int {
    if x >= 0 { x } else { -x }
}

/// Absolute mass of value kind `w` over the same rows.
pub open spec fn kabs(m: Model, p: int, a: int, b: int, w: int, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { kabs(m, p, a, b, w, lo, hi - 1) + if ksel(m, p, a, b, hi - 1) { abs_int(mval(m, w, hi - 1)) } else { 0 } }
}

/// With `lsi < nls`, the group-index sums are the key sums.
pub proof fn lemma_isum_ksum(m: Model, p: int, a: int, b: int, w: int, lo: int, hi: int)
    requires model_wf(m), 0 <= lo <= hi <= m.n, 0 <= b < m.nls,
    ensures isum(m, p, a * m.nls + b, w, lo, hi) == ksum(m, p, a, b, w, lo, hi),
    decreases hi - lo,
{
    if hi > lo {
        lemma_isum_ksum(m, p, a, b, w, lo, hi - 1);
        let j = hi - 1;
        assert(0 <= lsi(m, j) < m.nls);
        let (x1, y1, n) = (rfi(m, j), lsi(m, j), m.nls);
        if x1 * n + y1 == a * n + b && !(x1 == a && y1 == b) {
            if x1 < a {
                assert(x1 * n + n <= a * n) by (nonlinear_arith) requires x1 < a, n >= 1;
            } else if x1 > a {
                assert(a * n + n <= x1 * n) by (nonlinear_arith) requires a < x1, n >= 1;
            }
        }
    }
}

/// A key's sums by range: one more row, adjacent ranges.
pub proof fn lemma_ksum_split(m: Model, p: int, a: int, b: int, w: int, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures
        ksum(m, p, a, b, w, lo, hi) == ksum(m, p, a, b, w, lo, mid) + ksum(m, p, a, b, w, mid, hi),
        kabs(m, p, a, b, w, lo, hi) == kabs(m, p, a, b, w, lo, mid) + kabs(m, p, a, b, w, mid, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_ksum_split(m, p, a, b, w, lo, mid, hi - 1);
    }
}

/// The count is the number of selected rows and bounds every absolute mass by `count * vmax` when every
/// selected row's value is within `vmax`; the mass bounds the sum.
pub proof fn lemma_kabs_bounds(m: Model, p: int, a: int, b: int, w: int, lo: int, hi: int)
    ensures
        kabs(m, p, a, b, w, lo, hi) >= 0,
        -kabs(m, p, a, b, w, lo, hi) <= ksum(m, p, a, b, w, lo, hi) <= kabs(m, p, a, b, w, lo, hi),
        hi >= lo ==> 0 <= ksum(m, p, a, b, 5, lo, hi) <= hi - lo,
    decreases hi - lo,
{
    if hi > lo {
        lemma_kabs_bounds(m, p, a, b, w, lo, hi - 1);
    }
}

/// Under the fast path's bounds the mass of a key is at most `(hi - lo) * vbound(w)`.
pub proof fn lemma_kabs_fast(m: Model, p: int, a: int, b: int, w: int, lo: int, hi: int)
    requires
        model_wf(m), 0 <= lo <= hi <= m.n, 0 <= w <= 5,
        forall|j: int| lo <= j < hi ==> #[trigger] block_ok(m, blk(m, j)),
    ensures kabs(m, p, a, b, w, lo, hi) <= (hi - lo) * vbound(w),
    decreases hi - lo,
{
    if hi > lo {
        lemma_kabs_fast(m, p, a, b, w, lo, hi - 1);
        assert(block_ok(m, blk(m, hi - 1)));
        lemma_row_bounds(m, hi - 1, w);
        assert((hi - lo) * vbound(w) == (hi - 1 - lo) * vbound(w) + vbound(w)) by (nonlinear_arith);
    }
}

} // verus!
