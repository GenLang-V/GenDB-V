//! Exec building blocks of Q10 over the model's parts (`Cols`: the column slices, block sizes and the bound
//! parameters): block arithmetic, the customer row of a key (`cust_find`: by position when the keys are dense,
//! else the key index), the nation row of a key (`nat_find`), and the sums of one order's returned lineitems
//! (`fast_sums`: the contiguous run of the order at the lineitem cursor, using the co-clustering; `scan_sums`: a
//! scan of every lineitem row, the general path). Sums are exact in `i128`, with the absolute sum in `u128`; an
//! order whose absolute mass leaves `i128` is flagged (`ovf`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::{abs, pow10};
use crate::link::expr::i128_max;
use crate::stores::facts::interface::common::keyidx as fk;
use crate::stores::custpart::interface::common::keyidx as ck;
use super::common::isum::*;
use super::model::*;
use super::qspec::*;

verus! {

// ------------------------------------------------------------------------------------------------ columns

/// The column slices of the model and the bound parameters (`rf`: the l_returnflag dictionary entry of `'R'`, or
/// an index no row has; `[lo, hi]`: the date window). Slice lengths are fields because slice `len` may unwind in
/// worker bodies.
#[derive(Clone, Copy)]
pub struct Cols {
    pub l_key_c: &'static [u32],
    pub l_key_b: &'static [i64],
    pub l_price_c: &'static [u32],
    pub l_price_b: &'static [i64],
    pub l_disc_c: &'static [u8],
    pub l_disc_b: &'static [i64],
    pub l_rf_c: &'static [u8],
    pub l_rf_b: &'static [u64],
    pub l_bs: u64,
    pub l_n: usize,
    pub l_nb: usize,
    pub o_key_c: &'static [u32],
    pub o_key_b: &'static [i64],
    pub o_cust_c: &'static [u32],
    pub o_cust_b: &'static [i64],
    pub o_date_c: &'static [u16],
    pub o_date_b: &'static [i64],
    pub o_date_z: &'static [i64],
    pub o_ic: &'static [u32],
    pub o_ib: &'static [u64],
    pub o_kind: u64,
    pub o_bs: u64,
    pub o_bsz: usize,
    pub idx_ok: bool,
    pub o_n: usize,
    pub o_nb: usize,
    pub c_key_c: &'static [u32],
    pub c_key_b: &'static [i64],
    pub c_nat_c: &'static [u8],
    pub c_nat_b: &'static [i64],
    pub c_bs: u64,
    pub c_bsz: usize,
    pub c_bsz_ok: bool,
    pub c_n: usize,
    pub c_nb: usize,
    pub c_kind: u64,
    pub c_dense: bool,
    pub e32: &'static [u32],
    pub e64: &'static [u64],
    pub n_key_c: &'static [u8],
    pub n_key_b: &'static [i64],
    pub n_bs: u64,
    pub n_n: usize,
    pub rf: u64,
    pub lo: i64,
    pub hi: i64,
    pub cluster: u64,
}

/// The slices are the model's parts; `rf` decides `l_returnflag = 'R'` on every lineitem row; `c_dense`: customer
/// row `c` has key `c + 1`.
pub open spec fn cols_ok(c: Cols, m: M, p: QP) -> bool {
    &&& c.l_key_c@ == m.l_key_c && c.l_key_b@ == m.l_key_b
    &&& c.l_price_c@ == m.l_price_c && c.l_price_b@ == m.l_price_b
    &&& c.l_disc_c@ == m.l_disc_c && c.l_disc_b@ == m.l_disc_b
    &&& c.l_rf_c@ == m.l_rf_c && c.l_rf_b@ == m.l_rf_b
    &&& c.l_bs as int == m.l_bs && c.l_n == m.l_n && c.l_nb == m.l_nb
    &&& c.o_key_c@ == m.o_key_c && c.o_key_b@ == m.o_key_b
    &&& c.o_cust_c@ == m.o_cust_c && c.o_cust_b@ == m.o_cust_b
    &&& c.o_date_c@ == m.o_date_c && c.o_date_b@ == m.o_date_b && c.o_date_z@ == m.o_date_z
    &&& c.o_ic@ == m.o_ic && c.o_ib@ == m.o_ib && c.o_kind == m.o_kind
    &&& c.o_bs as int == m.o_bs && c.o_n == m.o_n && c.o_nb == m.o_nb
    &&& c.idx_ok ==> c.o_bsz as int == m.o_bs
    &&& c.c_key_c@ == m.c_key_c && c.c_key_b@ == m.c_key_b
    &&& c.c_nat_c@ == m.c_nat_c && c.c_nat_b@ == m.c_nat_b
    &&& c.c_bs as int == m.c_bs && c.c_n == m.c_n && c.c_nb == m.c_nb
    &&& c.c_bsz_ok ==> c.c_bsz as int == m.c_bs
    &&& c.c_kind == m.c_kind
    &&& c.e32@ == Seq::<u32>::empty() && c.e64@ == Seq::<u64>::empty()
    &&& c.n_key_c@ == m.n_key_c && c.n_key_b@ == m.n_key_b
    &&& c.n_bs as int == m.n_bs && c.n_n == m.n_n
    &&& forall|j: int| 0 <= j < m.l_n ==> (#[trigger] lflag(m, j) == r_text()) == (lrf(m, j) == c.rf as int)
    &&& c.lo == p.lo && c.hi == p.hi
    &&& c.cluster == m.cluster
    &&& c.c_dense ==> forall|i: int| 0 <= i < m.c_n ==> #[trigger] ckey(m, i) == i + 1
}

/// `j / bs` is `g` for a row of block `g`.
pub proof fn lemma_div_in(j: int, bs: int, g: int)
    requires bs >= 1, g * bs <= j < (g + 1) * bs,
    ensures j / bs == g,
{
    assert((g + 1) * bs == g * bs + bs) by (nonlinear_arith);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_div(j, bs, g, j - g * bs);
}

/// A row index below `n` has its block below the group count.
pub proof fn lemma_block_bound(j: int, bs: int, n: int, nb: int)
    requires bs >= 1, 0 <= j < n, nb * bs >= n,
    ensures 0 <= j / bs < nb,
{
    crate::stores::facts::interface::common::read::lemma_div_lt(j, bs, nb);
}

// ------------------------------------------------------------------------------------------------ lookups

/// The customer row of key `k`: under the primary key the only one (`cpos`).
#[inline(always)]
pub fn cust_find(c: &Cols, k: i64, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: Option<usize>)
    requires cols_ok(*c, m, p), model_ok(m),
    ensures
        r matches Some(i) ==> i < m.c_n && ckey(m, i as int) == k as int && cpos(m, k as int) == i as int,
        r is None ==> forall|i: int| 0 <= i < m.c_n ==> #[trigger] ckey(m, i) != k as int,
        r is None ==> cpos(m, k as int) == m.c_n,
    no_unwind
{
    if c.c_dense {
        if k >= 1 && (k as u64) <= (c.c_n as u64) {
            let i = (k - 1) as usize;
            proof {
                assert(ckey(m, i as int) == k as int);
                crate::agent::facts::lemma_cpos(m, k as int);
            }
            Some(i)
        } else {
            proof {
                assert forall|i: int| 0 <= i < m.c_n implies #[trigger] ckey(m, i) != k as int by {
                    assert(ckey(m, i) == i + 1);
                }
                crate::agent::facts::lemma_cpos(m, k as int);
            }
            None
        }
    } else if c.c_bsz_ok {
        let r = ck::key_find(c.c_key_c, c.c_key_b, c.e32, c.e64, c.c_bsz, c.c_kind, c.c_n, k as i128);
        proof {
            crate::agent::facts::lemma_cpos(m, k as int);
            match r {
                Some(i) => {
                    assert(ck::fkey(m.c_key_c, m.c_key_b, m.c_bs, i as int) == ckey(m, i as int));
                },
                None => {
                    assert forall|i: int| 0 <= i < m.c_n implies #[trigger] ckey(m, i) != k as int by {
                        assert(ck::fkey(m.c_key_c, m.c_key_b, m.c_bs, i) == ckey(m, i));
                    }
                },
            }
        }
        r
    } else {
        // a block wider than the address space: scan the rows
        let mut i: usize = 0;
        while i < c.c_n
            invariant
                cols_ok(*c, m, p), model_ok(m),
                i <= m.c_n,
                forall|t: int| 0 <= t < i ==> #[trigger] ckey(m, t) != k as int,
            decreases m.c_n - i,
        {
            proof {
                lemma_block_bound(i as int, m.c_bs, m.c_n, m.c_nb);
                assert(in_i64(ckey(m, i as int)));
            }
            if c.c_key_b[((i as u64) / c.c_bs) as usize] + c.c_key_c[i] as i64 == k {
                proof { crate::agent::facts::lemma_cpos(m, k as int); }
                return Some(i);
            }
            i = i + 1;
        }
        proof { crate::agent::facts::lemma_cpos(m, k as int); }
        None
    }
}

/// `c_nationkey` of customer row `i`.
#[inline(always)]
pub fn cnat_at(c: &Cols, i: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (k: i64)
    requires cols_ok(*c, m, p), model_ok(m), i < m.c_n,
    ensures k as int == cnat(m, i as int),
    no_unwind
{
    proof {
        lemma_block_bound(i as int, m.c_bs, m.c_n, m.c_nb);
        assert(in_i64(ckey(m, i as int)));
        assert(in_i64(cnat(m, i as int)));
    }
    c.c_nat_b[((i as u64) / c.c_bs) as usize] + c.c_nat_c[i] as i64
}

/// The nation row of key `k` (a scan of the nation rows): under the primary key the only one (`npos`).
#[inline(always)]
pub fn nat_find(c: &Cols, k: i64, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: Option<usize>)
    requires cols_ok(*c, m, p), model_ok(m),
    ensures
        r matches Some(n) ==> n < m.n_n && npos(m, k as int) == n as int,
        r is None ==> npos(m, k as int) == m.n_n,
    no_unwind
{
    let mut n: usize = 0;
    while n < c.n_n
        invariant
            cols_ok(*c, m, p), model_ok(m),
            n <= m.n_n,
            forall|t: int| 0 <= t < n ==> #[trigger] nkey(m, t) != k as int,
        decreases m.n_n - n,
    {
        proof {
            lemma_block_bound(n as int, m.n_bs, m.n_n, m.n_nb);
            assert(in_i64(nkey(m, n as int)));
        }
        let g = ((n as u64) / c.n_bs) as usize;
        if c.n_key_b[g] + c.n_key_c[n] as i64 == k {
            proof { crate::agent::facts::lemma_npos(m, k as int); }
            return Some(n);
        }
        n = n + 1;
    }
    proof { crate::agent::facts::lemma_npos(m, k as int); }
    None
}

/// Customer row `i`'s nation exists.
#[inline(always)]
pub fn nat_ok_at(c: &Cols, i: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: Option<usize>)
    requires cols_ok(*c, m, p), model_ok(m), i < m.c_n,
    ensures
        r matches Some(n) ==> nat_ok(m, i as int) && n == npos(m, cnat(m, i as int)),
        r is None ==> !nat_ok(m, i as int),
    no_unwind
{
    let k = cnat_at(c, i, Ghost(m), Ghost(p));
    nat_find(c, k, Ghost(m), Ghost(p))
}

// ------------------------------------------------------------------------------------------------ lineitem runs

/// `l` is the first lineitem row whose order position is at least `o` (the order positions never decrease).
pub open spec fn lb_ok(m: M, o: int, l: int) -> bool {
    &&& 0 <= l <= m.l_n
    &&& forall|t: int| 0 <= t < l ==> #[trigger] lpos(m, t) < o
    &&& forall|t: int| l <= t < m.l_n ==> #[trigger] lpos(m, t) >= o
}

/// With the cluster flag, the order position is nondecreasing.
pub proof fn lemma_lpos_mono(m: M, a: int, b: int)
    requires model_ok(m), m.cluster == 1, 0 <= a <= b < m.l_n,
    ensures lpos(m, a) <= lpos(m, b),
    decreases b - a,
{
    if a < b {
        lemma_lpos_mono(m, a, b - 1);
        assert(lpos(m, b - 1) <= lpos(m, (b - 1) + 1));
    }
}

/// The order at `q` is the one position with its key, so a lineitem row of that key has position `q`.
pub proof fn lemma_lpos_key(m: M, q: int, t: int)
    requires model_ok(m), 0 <= q < m.o_n,
    ensures (lkey(m, t) == okey(m, q)) == (lpos(m, t) == q),
{
    crate::agent::facts::lemma_opos(m, okey(m, q));
    crate::agent::facts::lemma_opos(m, lkey(m, t));
    if lkey(m, t) == okey(m, q) {
        assert(opos(m, okey(m, q)) == q) by {
            if opos(m, okey(m, q)) != q {
                assert(okey(m, q) != okey(m, q));
            }
        }
    }
}

/// A lineitem block cursor: `lg` is the block of the row `j` (or `j` starts block `lg + 1`).
pub open spec fn lcur_ok(m: M, j: int, lg: int, lge: int) -> bool {
    &&& m.l_bs >= 1
    &&& lg * m.l_bs <= j <= lge
    &&& lge == (lg + 1) * m.l_bs
    &&& j <= m.l_n
    &&& lge <= m.l_n + m.l_bs
}

/// Bounds of the SUM argument: at most 31 digits.
proof fn lemma_arg_bound(pr: int, ds: int)
    requires -pow10(15) < pr < pow10(15), -pow10(15) < ds < pow10(15),
    ensures abs(pr * (100 - ds)) < pow10(31), pow10(31) == 10000000000000000000000000000000,
        pow10(15) == 1000000000000000,
{
    assert(pow10(15) == 1000000000000000) by (compute);
    assert(pow10(31) == 10000000000000000000000000000000) by (compute);
    let x = abs(pr);
    let y = abs(100 - ds);
    assert(abs(pr * (100 - ds)) == x * y) by (nonlinear_arith) requires x == abs(pr), y == abs(100 - ds);
    assert(x * y < 10000000000000000000000000000000) by (nonlinear_arith)
        requires 0 <= x < 1000000000000000, 0 <= y < 1000000000000100;
}

/// The SUM argument coefficient of lineitem row `j` (block `g`).
#[inline(always)]
pub fn row_arg(c: &Cols, j: usize, g: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (a: i128)
    requires cols_ok(*c, m, p), model_ok(m), j < m.l_n, g as int == j as int / m.l_bs,
    ensures a as int == larg(m, j as int), abs(a as int) < 10000000000000000000000000000000,
    no_unwind
{
    proof {
        lemma_block_bound(j as int, m.l_bs, m.l_n, m.l_nb);
        assert(in_i64(lkey(m, j as int)));
        lemma_arg_bound(lprice(m, j as int), ldisc(m, j as int));
    }
    let price = c.l_price_b[g] + c.l_price_c[j] as i64;
    let disc = c.l_disc_b[g] + c.l_disc_c[j] as i64;
    (price as i128) * (100 - disc as i128)
}

/// The returned-flag test code of block `g`: row `j` of the block is returned exactly when its code equals it
/// (256: no row of the block).
#[inline(always)]
fn rf_target(c: &Cols, g: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (t: u16)
    requires cols_ok(*c, m, p), model_ok(m), g < m.l_nb,
    ensures
        forall|j: int| 0 <= j < m.l_n && j / m.l_bs == g ==> (#[trigger] lflag(m, j) == r_text()) == (m.l_rf_c[j] as int == t as int),
    no_unwind
{
    let b = c.l_rf_b[g];
    let t: u16 = if b <= c.rf && c.rf - b <= 255 { (c.rf - b) as u16 } else { 256 };
    proof {
        assert forall|j: int| 0 <= j < m.l_n && j / m.l_bs == g implies (#[trigger] lflag(m, j) == r_text()) == (m.l_rf_c[j] as int == t as int) by {
            assert(lrf(m, j) == b as int + m.l_rf_c[j] as int);
        }
    }
    t
}

/// Partial sums of one order over lineitem rows `[j0, j)`.
pub open spec fn dsum(f: spec_fn(int) -> int, j0: int, j: int) -> int {
    isum(j, f) - isum(j0, f)
}

/// One accumulation step of an order's revenue: the count always; the sum and the absolute sum while the absolute
/// sum stays inside `i128` (beyond it the order's mass is outside the capacity condition).
pub open spec fn acc_ok(m: M, q: int, j0: int, j: int, cnt: u64, sum: i128, ab: u128, ovf: bool) -> bool {
    &&& cnt as int == dsum(lcnt_f(m, q), j0, j)
    &&& cnt as int <= j - j0
    &&& !ovf ==> sum as int == dsum(lsum_f(m, q), j0, j) && ab as int == dsum(labs_f(m, q), j0, j)
        && ab as int <= i128_max() && -(ab as int) <= sum as int <= ab as int
    &&& ovf ==> dsum(labs_f(m, q), j0, j) > i128_max()
}

/// The terms of an order's sums at one row.
proof fn lemma_terms_at(m: M, q: int, j: int)
    ensures
        lcnt_f(m, q)(j) == if lhit(m, q, j) { 1int } else { 0int },
        lsum_f(m, q)(j) == if lhit(m, q, j) { larg(m, j) } else { 0int },
        labs_f(m, q)(j) == if lhit(m, q, j) { abs(larg(m, j)) } else { 0int },
        labs_f(m, q)(j) >= 0,
{
}

/// Accumulate row `j` (a hit with argument `a`, or not a hit) into an order's sums.
#[inline(always)]
pub fn acc_row(cnt: u64, sum: i128, ab: u128, ovf: bool, hitj: bool, a: i128, Ghost(m): Ghost<M>,
    Ghost(q): Ghost<int>, Ghost(j0): Ghost<int>, Ghost(j): Ghost<int>) -> (r: (u64, i128, u128, bool))
    requires
        acc_ok(m, q, j0, j, cnt, sum, ab, ovf),
        0 <= j0 <= j,
        j < u64::MAX,
        hitj == lhit(m, q, j),
        hitj ==> a as int == larg(m, j) && abs(a as int) < 10000000000000000000000000000000,
    ensures
        acc_ok(m, q, j0, j + 1, r.0, r.1, r.2, r.3),
    no_unwind
{
    proof {
        lemma_terms_at(m, q, j);
        lemma_isum_step(j, lcnt_f(m, q));
        lemma_isum_step(j, lsum_f(m, q));
        lemma_isum_step(j, labs_f(m, q));
    }
    if !hitj {
        return (cnt, sum, ab, ovf);
    }
    let cnt1 = cnt + 1;
    if ovf {
        return (cnt1, sum, ab, ovf);
    }
    let aa: u128 = if a < 0 { (0 - a) as u128 } else { a as u128 };
    assert(aa as int == abs(larg(m, j)));
    let na = ab + aa;
    if na > 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffffu128 {
        (cnt1, sum, ab, true)
    } else {
        (cnt1, sum + a, na, false)
    }
}

/// The sums of one order: count, revenue and absolute revenue of its returned lineitems (`ovf`: the absolute
/// revenue leaves `i128`).
pub open spec fn sums_ok(m: M, q: int, cnt: u64, sum: i128, ab: u128, ovf: bool) -> bool {
    &&& cnt as int == lcnt(m, q)
    &&& !ovf ==> sum as int == lsum(m, q) && ab as int == labs(m, q) && ab as int <= i128_max()
        && -(ab as int) <= sum as int <= ab as int
    &&& ovf ==> labs(m, q) > i128_max()
}

/// Lineitem block `g` allows the `i64` row arithmetic: price base in `[0, 2^31]` and discount base in
/// `[-1024, 1024]`, so every row's price is below `2^33`, `|100 - discount|` below `2^11` and the argument below
/// `2^44` in absolute value.
pub open spec fn fast_block(m: M, g: int) -> bool {
    &&& 0 <= m.l_price_b[g] <= 0x8000_0000
    &&& -1024 <= m.l_disc_b[g] <= 1024
}

/// Bound of the absolute revenue of an order below which the next fast segment starts.
pub const AB_FAST: u128 = 0x0100_0000_0000_0000_0000_0000_0000_0000;

/// The SUM argument of lineitem row `j` of a fast block `g` (price base `pb`, discount base `db`), in `i64`.
#[inline(always)]
pub fn row_arg64(c: &Cols, j: usize, pb: i64, db: i64, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(g): Ghost<int>) -> (a: i64)
    requires
        cols_ok(*c, m, p), model_ok(m), j < m.l_n, g == j as int / m.l_bs, 0 <= g < m.l_nb,
        fast_block(m, g), pb == m.l_price_b[g], db == m.l_disc_b[g],
    ensures a as int == larg(m, j as int), -0x1000_0000_0000 < a < 0x1000_0000_0000,
    no_unwind
{
    let price = pb + c.l_price_c[j] as i64;
    let f = 100 - (db + c.l_disc_c[j] as i64);
    proof {
        assert(0 <= price < 0x2_0000_0000);
        assert(-2048 < f < 2048);
        assert(-0x1000_0000_0000 < price * f < 0x1000_0000_0000) by (nonlinear_arith)
            requires 0 <= price < 0x2_0000_0000, -2048 < f < 2048;
    }
    price * f
}

/// The returned-flag target code, the fast-arithmetic flag and the price and discount bases of block `g`.
#[inline(always)]
pub fn block_info(c: &Cols, g: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: (u16, bool, i64, i64))
    requires cols_ok(*c, m, p), model_ok(m), g < m.l_nb,
    ensures
        forall|j: int| 0 <= j < m.l_n && j / m.l_bs == g ==> (#[trigger] lflag(m, j) == r_text()) == (m.l_rf_c[j] as int == r.0 as int),
        r.1 ==> fast_block(m, g as int) && r.2 == m.l_price_b[g as int] && r.3 == m.l_disc_b[g as int],
    no_unwind
{
    let t = rf_target(c, g, Ghost(m), Ghost(p));
    let pb = c.l_price_b[g];
    let db = c.l_disc_b[g];
    let fb = 0 <= pb && pb <= 0x8000_0000 && -1024 <= db && db <= 1024;
    (t, fb, pb, db)
}

/// Bound of a segment's absolute revenue below which `seg_sum` adds one more row inside `i64`.
pub const SEG_AB: u64 = 0x4000_0000_0000_0000;

/// The sums of one order over the rows `[j0, j)` of one segment, in `i64`.
pub open spec fn seg_ok(m: M, q: int, j0: int, j: int, n: u64, s: i64, a: u64) -> bool {
    &&& n as int == dsum(lcnt_f(m, q), j0, j)
    &&& s as int == dsum(lsum_f(m, q), j0, j)
    &&& a as int == dsum(labs_f(m, q), j0, j)
    &&& n as int <= j - j0
    &&& -(a as int) <= s as int <= a as int
    &&& a <= SEG_AB + 0x1000_0000_0000
}

/// One row of a segment.
proof fn lemma_seg_step(m: M, q: int, j0: int, j: int, n: u64, s: i64, a: u64, hitj: bool, t: int, tm: int)
    requires
        seg_ok(m, q, j0, j, n, s, a),
        0 <= j0 <= j,
        j < u64::MAX,
        a <= SEG_AB,
        hitj == lhit(m, q, j),
        t == larg(m, j),
        -0x1000_0000_0000 < t < 0x1000_0000_0000,
        tm == if hitj { t } else { 0 },
    ensures
        seg_ok(m, q, j0, j + 1, (n + if hitj { 1u64 } else { 0u64 }) as u64, (s + tm) as i64, (a + abs(tm)) as u64),
{
    lemma_terms_at(m, q, j);
    lemma_isum_step(j, lcnt_f(m, q));
    lemma_isum_step(j, lsum_f(m, q));
    lemma_isum_step(j, labs_f(m, q));
}

/// The returned rows of the order with key `okv` among the rows `[j0, end)` of one fast block `g` (key base `kb`,
/// returned-flag target `tgt`, price and discount bases `pb`, `db`): it stops at the first row of another key, at
/// `end`, or when the absolute revenue reaches `SEG_AB`. Branch-free `i64` arithmetic per row.
#[inline(always)]
fn seg_sum(c: &Cols, okv: i64, kb: i64, tgt: u16, pb: i64, db: i64, j0: usize, end: usize,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(q): Ghost<int>, Ghost(g): Ghost<int>) -> (r: (usize, u64, i64, u64, bool))
    requires
        cols_ok(*c, m, p), model_ok(m),
        0 <= q < m.o_n, okv == okey(m, q),
        0 <= g < m.l_nb,
        g * m.l_bs <= j0 <= end <= (g + 1) * m.l_bs,
        end <= m.l_n,
        fast_block(m, g), kb == m.l_key_b[g], pb == m.l_price_b[g], db == m.l_disc_b[g],
        forall|t: int| 0 <= t < m.l_n && t / m.l_bs == g ==> (#[trigger] lflag(m, t) == r_text()) == (m.l_rf_c[t] as int == tgt as int),
    ensures ({
        let (j, n, s, a, stop) = r;
        &&& j0 <= j <= end
        &&& forall|t: int| j0 <= t < j ==> #[trigger] lkey(m, t) == okey(m, q)
        &&& stop ==> j < end && lkey(m, j as int) != okey(m, q)
        &&& seg_ok(m, q, j0 as int, j as int, n, s, a)
        &&& j0 < end ==> j > j0 || stop
    }),
    no_unwind
{
    let mut j = j0;
    let mut n: u64 = 0;
    let mut s: i64 = 0;
    let mut a: u64 = 0;
    let mut stop = false;
    while j < end && !stop && a <= SEG_AB
        invariant
            cols_ok(*c, m, p), model_ok(m),
            0 <= q < m.o_n, okv == okey(m, q),
            0 <= g < m.l_nb,
            g * m.l_bs <= j0 <= j <= end <= (g + 1) * m.l_bs,
            end <= m.l_n,
            fast_block(m, g), kb == m.l_key_b[g], pb == m.l_price_b[g], db == m.l_disc_b[g],
            forall|t: int| 0 <= t < m.l_n && t / m.l_bs == g ==> (#[trigger] lflag(m, t) == r_text()) == (m.l_rf_c[t] as int == tgt as int),
            forall|t: int| j0 <= t < j ==> #[trigger] lkey(m, t) == okey(m, q),
            stop ==> j < end && lkey(m, j as int) != okey(m, q),
            seg_ok(m, q, j0 as int, j as int, n, s, a),
        decreases end - j + if stop { 0int } else { 1int },
    {
        proof {
            lemma_div_in(j as int, m.l_bs, g);
            assert(in_i64(lkey(m, j as int)));
        }
        if kb + c.l_key_c[j] as i64 != okv {
            stop = true;
        } else {
            let hitj = c.l_rf_c[j] as u16 == tgt;
            let t = row_arg64(c, j, pb, db, Ghost(m), Ghost(p), Ghost(g));
            let tm: i64 = if hitj { t } else { 0 };
            let ta: u64 = if tm < 0 { (0 - tm) as u64 } else { tm as u64 };
            proof {
                lemma_seg_step(m, q, j0 as int, j as int, n, s, a, hitj, t as int, tm as int);
            }
            n = n + if hitj { 1u64 } else { 0u64 };
            s = s + tm;
            a = a + ta;
            j = j + 1;
        }
    }
    proof {
        if j == j0 {
            assert(a as int == dsum(labs_f(m, q), j0 as int, j0 as int));
        }
    }
    (j, n, s, a, stop)
}

/// Sums over consecutive row ranges add up.
proof fn lemma_acc_seg(m: M, q: int, j0: int, j1: int, j2: int, cnt: u64, sum: i128, ab: u128, n: u64, s: i64, a: u64)
    requires
        acc_ok(m, q, j0, j1, cnt, sum, ab, false),
        seg_ok(m, q, j1, j2, n, s, a),
        ab <= AB_FAST,
        0 <= j0 <= j1 <= j2,
        j2 <= u64::MAX,
    ensures
        acc_ok(m, q, j0, j2, (cnt + n) as u64, (sum + s) as i128, (ab + a) as u128, false),
{
    lemma_dsum_join3(lcnt_f(m, q), j0, j1, j2);
    lemma_dsum_join3(lsum_f(m, q), j0, j1, j2);
    lemma_dsum_join3(labs_f(m, q), j0, j1, j2);
}

/// Range sums over consecutive ranges add up.
proof fn lemma_dsum_join3(f: spec_fn(int) -> int, a: int, b: int, c: int)
    ensures dsum(f, a, b) + dsum(f, b, c) == dsum(f, a, c),
{
}

/// The lineitem run of the order at `q` (key `okv`) from the cursor `j0`: count, revenue and absolute revenue of its
/// returned rows, and the cursor after the run (the first row of the next order). Rows of fast blocks
/// (`fast_block`) use branch-free `i64` arithmetic while the absolute revenue stays below `AB_FAST`; other rows
/// use the exact `i128` step with its overflow check.
#[inline(always)]
pub fn fast_sums(c: &Cols, okv: i64, j0: usize, l_hi: usize, lg0: usize, lge0: u64,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(q): Ghost<int>) -> (r: (u64, i128, u128, bool, usize, usize, u64))
    requires
        cols_ok(*c, m, p), model_ok(m), m.cluster == 1,
        0 <= q < m.o_n, okv == okey(m, q),
        lb_ok(m, q, j0 as int),
        j0 <= l_hi <= m.l_n,
        forall|t: int| l_hi <= t < m.l_n ==> #[trigger] lpos(m, t) > q,
        lcur_ok(m, j0 as int, lg0 as int, lge0 as int),
    ensures ({
        let (cnt, sum, ab, ovf, j1, lg1, lge1) = r;
        &&& j0 <= j1 <= l_hi
        &&& lb_ok(m, q + 1, j1 as int)
        &&& lcur_ok(m, j1 as int, lg1 as int, lge1 as int)
        &&& sums_ok(m, q, cnt, sum, ab, ovf)
    }),
    no_unwind
{
    let mut j = j0;
    let mut lg = lg0;
    let mut lge = lge0;
    let mut cnt: u64 = 0;
    let mut sum: i128 = 0;
    let mut ab: u128 = 0;
    let mut ovf = false;
    let mut stop = false;
    let mut tgt: u16 = 256;
    let mut fb = false;
    let mut pb: i64 = 0;
    let mut db: i64 = 0;
    if j < c.l_n && (j as u64) < lge {
        proof {
            lemma_div_in(j as int, m.l_bs, lg as int);
            lemma_block_bound(j as int, m.l_bs, m.l_n, m.l_nb);
        }
        let bi = block_info(c, lg, Ghost(m), Ghost(p));
        tgt = bi.0;
        fb = bi.1;
        pb = bi.2;
        db = bi.3;
    }
    while j < l_hi && !stop
        invariant
            cols_ok(*c, m, p), model_ok(m), m.cluster == 1,
            0 <= q < m.o_n, okv == okey(m, q),
            lb_ok(m, q, j0 as int),
            j0 <= j <= l_hi <= m.l_n,
            lcur_ok(m, j as int, lg as int, lge as int),
            (j as u64) < lge && j < m.l_n ==> forall|t: int| 0 <= t < m.l_n && t / m.l_bs == lg ==>
                (#[trigger] lflag(m, t) == r_text()) == (m.l_rf_c[t] as int == tgt as int),
            (j as u64) < lge && j < m.l_n && fb ==> fast_block(m, lg as int) && pb == m.l_price_b[lg as int]
                && db == m.l_disc_b[lg as int],
            forall|t: int| j0 <= t < j ==> #[trigger] lkey(m, t) == okey(m, q),
            stop ==> j < l_hi && lkey(m, j as int) != okey(m, q),
            acc_ok(m, q, j0 as int, j as int, cnt, sum, ab, ovf),
        decreases l_hi - j + if stop { 0int } else { 1int },
    {
        if j as u64 == lge {
            proof {
                assert((lg + 2) * m.l_bs == (lg + 1) * m.l_bs + m.l_bs) by (nonlinear_arith);
                // the next block holds row j < l_n, so it is a block of the table
                lemma_div_in(j as int, m.l_bs, lg as int + 1);
                lemma_block_bound(j as int, m.l_bs, m.l_n, m.l_nb);
            }
            lg = lg + 1;
            lge = lge + c.l_bs;
            let bi = block_info(c, lg, Ghost(m), Ghost(p));
            tgt = bi.0;
            fb = bi.1;
            pb = bi.2;
            db = bi.3;
        }
        assert(lg * m.l_bs <= j < lge && lge == (lg + 1) * m.l_bs);
        proof {
            lemma_div_in(j as int, m.l_bs, lg as int);
            lemma_block_bound(j as int, m.l_bs, m.l_n, m.l_nb);
            assert(in_i64(lkey(m, j as int)));
        }
        if fb && !ovf && ab <= AB_FAST {
            // the rest of the order's run inside this block
            let end: usize = if lge < l_hi as u64 { lge as usize } else { l_hi };
            let kb = c.l_key_b[lg];
            let r = seg_sum(c, okv, kb, tgt, pb, db, j, end, Ghost(m), Ghost(p), Ghost(q), Ghost(lg as int));
            proof {
                lemma_acc_seg(m, q, j0 as int, j as int, r.0 as int, cnt, sum, ab, r.1, r.2, r.3);
            }
            cnt = cnt + r.1;
            sum = sum + r.2 as i128;
            ab = ab + r.3 as u128;
            j = r.0;
            stop = r.4;
        } else {
            let lk = c.l_key_b[lg] + c.l_key_c[j] as i64;
            if lk != okv {
                stop = true;
            } else {
                let hitj = c.l_rf_c[j] as u16 == tgt;
                let a: i128 = if hitj { row_arg(c, j, lg, Ghost(m), Ghost(p)) } else { 0 };
                let r = acc_row(cnt, sum, ab, ovf, hitj, a, Ghost(m), Ghost(q), Ghost(j0 as int), Ghost(j as int));
                cnt = r.0;
                sum = r.1;
                ab = r.2;
                ovf = r.3;
                j = j + 1;
            }
        }
    }
    proof {
        // the order's rows are exactly [j0, j)
        assert forall|t: int| 0 <= t < m.l_n && (t < j0 || t >= j) implies lkey(m, t) != okey(m, q) by {
            lemma_lpos_key(m, q, t);
            if t >= j {
                if j < l_hi {
                    lemma_lpos_key(m, q, j as int);
                    lemma_lpos_mono(m, j as int, t);
                }
            }
        }
        lemma_run_totals(m, q, j0 as int, j as int);
        assert forall|t: int| 0 <= t < j implies #[trigger] lpos(m, t) < q + 1 by {
            if t >= j0 {
                lemma_lpos_key(m, q, t);
            }
        }
        assert forall|t: int| j <= t < m.l_n implies #[trigger] lpos(m, t) >= q + 1 by {
            if j < l_hi {
                lemma_lpos_key(m, q, j as int);
                lemma_lpos_mono(m, j as int, t);
            }
        }
    }
    (cnt, sum, ab, ovf, j, lg, lge)
}

/// When an order's rows are exactly `[j0, j)`, its partial sums there are its totals.
pub proof fn lemma_run_totals(m: M, q: int, j0: int, j: int)
    requires
        0 <= j0 <= j <= m.l_n,
        forall|t: int| 0 <= t < m.l_n && (t < j0 || t >= j) ==> lkey(m, t) != okey(m, q),
    ensures
        dsum(lcnt_f(m, q), j0, j) == lcnt(m, q),
        dsum(lsum_f(m, q), j0, j) == lsum(m, q),
        dsum(labs_f(m, q), j0, j) == labs(m, q),
{
    assert forall|t: int| 0 <= t < j0 implies #[trigger] lcnt_f(m, q)(t) == 0 && lsum_f(m, q)(t) == 0 && labs_f(m, q)(t) == 0 by {}
    assert forall|t: int| j <= t < m.l_n implies #[trigger] lcnt_f(m, q)(t) == 0 && lsum_f(m, q)(t) == 0 && labs_f(m, q)(t) == 0 by {}
    lemma_isum_prefix_zero(j0, lcnt_f(m, q));
    lemma_isum_prefix_zero(j0, lsum_f(m, q));
    lemma_isum_prefix_zero(j0, labs_f(m, q));
    lemma_isum_suffix_zero(j, m.l_n, lcnt_f(m, q));
    lemma_isum_suffix_zero(j, m.l_n, lsum_f(m, q));
    lemma_isum_suffix_zero(j, m.l_n, labs_f(m, q));
}

/// The general path: an order's sums by a scan of every lineitem row.
pub fn scan_sums(c: &Cols, okv: i64, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(q): Ghost<int>) -> (r: (u64, i128, u128, bool))
    requires
        cols_ok(*c, m, p), model_ok(m),
        0 <= q < m.o_n, okv == okey(m, q),
    ensures sums_ok(m, q, r.0, r.1, r.2, r.3),
    no_unwind
{
    let mut j: usize = 0;
    let mut cnt: u64 = 0;
    let mut sum: i128 = 0;
    let mut ab: u128 = 0;
    let mut ovf = false;
    while j < c.l_n
        invariant
            cols_ok(*c, m, p), model_ok(m),
            0 <= q < m.o_n, okv == okey(m, q),
            j <= m.l_n,
            acc_ok(m, q, 0, j as int, cnt, sum, ab, ovf),
        decreases m.l_n - j,
    {
        let g = ((j as u64) / c.l_bs) as usize;
        proof {
            lemma_block_bound(j as int, m.l_bs, m.l_n, m.l_nb);
            assert(in_i64(lkey(m, j as int)));
        }
        let lk = c.l_key_b[g] + c.l_key_c[j] as i64;
        let rb = c.l_rf_b[g];
        let hitj = lk == okv && rb <= c.rf && c.rf - rb == c.l_rf_c[j] as u64;
        let a: i128 = if hitj { row_arg(c, j, g, Ghost(m), Ghost(p)) } else { 0 };
        let r = acc_row(cnt, sum, ab, ovf, hitj, a, Ghost(m), Ghost(q), Ghost(0), Ghost(j as int));
        cnt = r.0;
        sum = r.1;
        ab = r.2;
        ovf = r.3;
        j = j + 1;
    }
    proof {
        assert(dsum(lcnt_f(m, q), 0, m.l_n) == lcnt(m, q));
        assert(dsum(lsum_f(m, q), 0, m.l_n) == lsum(m, q));
        assert(dsum(labs_f(m, q), 0, m.l_n) == labs(m, q));
    }
    (cnt, sum, ab, ovf)
}

/// Decoded orders values of position `q` (block `og`): key, customer key, date.
#[inline(always)]
pub fn order_at(c: &Cols, q: usize, og: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: (i64, i64, i64))
    requires cols_ok(*c, m, p), model_ok(m), q < m.o_n, og as int == q as int / m.o_bs,
    ensures r.0 as int == okey(m, q as int), r.1 as int == ocust(m, q as int), r.2 as int == odate(m, q as int),
    no_unwind
{
    proof {
        lemma_block_bound(q as int, m.o_bs, m.o_n, m.o_nb);
        assert(in_i64(okey(m, q as int)));
    }
    (c.o_key_b[og] + c.o_key_c[q] as i64, c.o_cust_b[og] + c.o_cust_c[q] as i64, c.o_date_b[og] + c.o_date_c[q] as i64)
}

} // verus!
