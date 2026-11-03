//! The fast Q1 scan: worker task `k` of `s` sums blocks `k, k + s, k + 2s, ...` (`stride`), starting at round
//! `k * q / s` and wrapping around, into a dense table of the groups
//! (`t = nrf * nls` entries, entry `rfi * nls + lsi`): per entry the count (u64) and five exact sums (i128) of
//! quantity, price, price * (100 - discount), that times (100 + tax), and discount (coefficients).
//!
//! It runs only on blocks whose bases pass `model::block_ok` (checked by the caller), so every row value is small
//! (`model::vbound`) and a chunk of at most `CHUNK` rows sums in `i64` without overflow. Per block: skipped when
//! its shipdate base exceeds the bound (no row qualifies); otherwise chunk by chunk, with the shipdate test left
//! out when the block's zone maximum is within the bound. Per chunk the (rf, ls) code pairs present lie in the
//! bounding box of the codes (`chunk_box`: from the chunk's pair mask of storage `li_pairmask` when it names one pair
//! or two pairs differing in one code, else `code_range` over the codes):
//! - one pair: no key test (`kern::chunk_all2`, code-domain sums; `chunk_date` with the shipdate test);
//! - two codes of one column in a full block (the box's low and high codes, `next_code` shows no code between):
//!   one pass (`kern::chunk_split2`), e.g. TPC-H's early region with l_returnflag in {A, R};
//! - three or four present entries in a full block (`present_entries`): one four-way masked pass (`try_multi`),
//!   e.g. the region where l_linestatus changes;
//! - otherwise one masked pass per two present table entries (`chunk_two`, `chunk_pair`).
//! Every pass is branch-free (masked sums) so it vectorizes.
use vstd::prelude::*;
use crate::gendb_entry::parallel::WorkerTask;
use super::common::csum::*;
use super::model::*;
use super::kern::{chunk_all2, chunk_split2};
use super::stride::*;
use super::pairmask::{marked, decode_mask};
use crate::stores::li_pairmask::interface as LP;

verus! {

pub const NSUMS: usize = 5;
/// Rows per chunk: `CHUNK * vbound(w) < 2^63` for every value kind.
pub const CHUNK: usize = 2048;
/// Largest dense group table of the fast path.
pub const MAXT: usize = 64;

// ------------------------------------------------------------------------------------------------ chunk passes

/// Sums of one selection over one chunk: count and the five value kinds (decoded with the chunk's block bases).
pub struct ChunkSums {
    pub cnt: i64,
    pub q: i64,
    pub p: i64,
    pub dp: i64,
    pub ch: i64,
    pub d: i64,
}

pub open spec fn cqc(qs: Seq<u16>) -> spec_fn(int) -> int {
    |i: int| qs[i] as int
}

pub open spec fn cdc(ds: Seq<u8>) -> spec_fn(int) -> int {
    |i: int| ds[i] as int
}

pub open spec fn cq(qs: Seq<u16>, bq: int) -> spec_fn(int) -> int {
    |i: int| bq + qs[i]
}

pub open spec fn cp(ps: Seq<u32>, bp: int) -> spec_fn(int) -> int {
    |i: int| bp + ps[i]
}

pub open spec fn cd(ds: Seq<u8>, bd: int) -> spec_fn(int) -> int {
    |i: int| bd + ds[i]
}

pub open spec fn cdp(ps: Seq<u32>, ds: Seq<u8>, bp: int, bd: int) -> spec_fn(int) -> int {
    |i: int| (bp + ps[i]) * (100 - (bd + ds[i]))
}

pub open spec fn cch(ps: Seq<u32>, ds: Seq<u8>, ts: Seq<u8>, bp: int, bd: int, bt: int) -> spec_fn(int) -> int {
    |i: int| (bp + ps[i]) * (100 - (bd + ds[i])) * (100 + (bt + ts[i]))
}

/// The bases of the chunk's block within the fast path's bounds.
pub open spec fn bases_ok(bq: i64, bp: i64, bd: i64, bt: i64) -> bool {
    &&& -0x1_0000_0000 <= bq <= 0x1_0000_0000
    &&& -0x1_0000_0000 <= bp <= 0x1_0000_0000
    &&& 0 <= bd <= 100
    &&& 0 <= bt <= 100
}

/// The sums `r` are those of selection `sel` over the chunk's `m` positions.
pub open spec fn sums_ok(r: ChunkSums, sel: spec_fn(int) -> bool, qs: Seq<u16>, ps: Seq<u32>, ds: Seq<u8>, ts: Seq<u8>,
    bq: i64, bp: i64, bd: i64, bt: i64, m: int) -> bool
{
    &&& r.cnt == csum(sel, one(), m)
    &&& r.q == csum(sel, cq(qs, bq as int), m)
    &&& r.p == csum(sel, cp(ps, bp as int), m)
    &&& r.dp == csum(sel, cdp(ps, ds, bp as int, bd as int), m)
    &&& r.ch == csum(sel, cch(ps, ds, ts, bp as int, bd as int, bt as int), m)
    &&& r.d == csum(sel, cd(ds, bd as int), m)
}

/// `1` or `0`.
#[inline]
fn b2i(b: bool) -> (r: i64)
    ensures r == if b { 1i64 } else { 0i64 },
    no_unwind
{
    if b { 1 } else { 0 }
}

/// `x` when `s == 1`, `0` when `s == 0` (a bit mask, no branch).
#[inline]
fn masked(x: i64, s: i64) -> (r: i64)
    requires s == 0 || s == 1,
    ensures r == if s == 1 { x } else { 0 },
    no_unwind
{
    let mk: i64 = 0i64 - s;
    let r = x & mk;
    proof {
        if s == 1 {
            assert(mk == -1i64);
            assert((x & -1i64) == x) by (bit_vector);
        } else {
            assert(mk == 0i64);
            assert((x & 0i64) == 0i64) by (bit_vector);
        }
    }
    r
}

/// Price, price * (100 - discount) and that times (100 + tax) of one row (`k1 = 100 - bd`, `k2 = 100 + bt`).
#[inline]
fn row_vals(pc: u32, dc: u8, tc: u8, bp: i64, k1: i64, k2: i64) -> (r: (i64, i64, i64))
    requires -0x1_0000_0000 <= bp <= 0x1_0000_0000, 0 <= k1 <= 100, 100 <= k2 <= 200,
    ensures
        r.0 == bp + pc,
        r.1 == r.0 * (k1 - dc),
        r.2 == r.1 * (k2 + tc),
        -0x2_0000_0000 <= r.0 <= 0x2_0000_0000,
        -0x200_0000_0000 <= r.1 <= 0x200_0000_0000,
        -0x4_0000_0000_0000 <= r.2 <= 0x4_0000_0000_0000,
    no_unwind
{
    let pr = bp + pc as i64;
    let x = k1 - dc as i64;
    let y = k2 + tc as i64;
    assert(-0x200_0000_0000 <= pr * x <= 0x200_0000_0000) by (nonlinear_arith)
        requires -0x2_0000_0000 <= pr <= 0x2_0000_0000, -255 <= x <= 100;
    let dp = pr * x;
    assert(-0x4_0000_0000_0000 <= dp * y <= 0x4_0000_0000_0000) by (nonlinear_arith)
        requires -0x200_0000_0000 <= dp <= 0x200_0000_0000, 100 <= y <= 455;
    let ch = dp * y;
    (pr, dp, ch)
}

/// The decoded sums from the code-domain sums of quantity and discount.
proof fn lemma_finish_sums(sel: spec_fn(int) -> bool, qs: Seq<u16>, ds: Seq<u8>, bq: int, bd: int, m: int)
    ensures
        csum(sel, cq(qs, bq), m) == bq * csum(sel, one(), m) + csum(sel, cqc(qs), m),
        csum(sel, cd(ds, bd), m) == bd * csum(sel, one(), m) + csum(sel, cdc(ds), m),
{
    lemma_csum_affine(sel, cqc(qs), cq(qs, bq), bq, m);
    lemma_csum_affine(sel, cdc(ds), cd(ds, bd), bd, m);
}

/// The loop state of a chunk pass over positions `0 .. j` for selection `sel`.
pub open spec fn acc_ok(sel: spec_fn(int) -> bool, qs: Seq<u16>, ps: Seq<u32>, ds: Seq<u8>, ts: Seq<u8>,
    bp: i64, bd: i64, bt: i64, j: int, c: i64, q: i64, p: i64, dp: i64, ch: i64, d: i64) -> bool
{
    &&& c == csum(sel, one(), j) && 0 <= c <= j
    &&& q == csum(sel, cqc(qs), j) && 0 <= q <= j * 0xffff
    &&& p == csum(sel, cp(ps, bp as int), j) && -(j * 0x2_0000_0000) <= p <= j * 0x2_0000_0000
    &&& dp == csum(sel, cdp(ps, ds, bp as int, bd as int), j) && -(j * 0x200_0000_0000) <= dp <= j * 0x200_0000_0000
    &&& ch == csum(sel, cch(ps, ds, ts, bp as int, bd as int, bt as int), j)
        && -(j * 0x4_0000_0000_0000) <= ch <= j * 0x4_0000_0000_0000
    &&& d == csum(sel, cdc(ds), j) && 0 <= d <= j * 255
}

/// One loop step of a chunk pass: position `j` with selection bit `s` and its row values.
proof fn lemma_acc_step(sel: spec_fn(int) -> bool, qs: Seq<u16>, ps: Seq<u32>, ds: Seq<u8>, ts: Seq<u8>,
    bp: i64, bd: i64, bt: i64, j: int, c: i64, q: i64, p: i64, dp: i64, ch: i64, d: i64,
    s: int, pr: int, dpv: int, chv: int)
    requires
        0 <= j < 2048, j < qs.len(), j < ps.len(), j < ds.len(), j < ts.len(),
        acc_ok(sel, qs, ps, ds, ts, bp, bd, bt, j, c, q, p, dp, ch, d),
        s == if sel(j) { 1int } else { 0int },
        pr == bp + ps[j],
        dpv == pr * ((100 - bd) - ds[j]),
        chv == dpv * ((100 + bt) + ts[j]),
        -0x2_0000_0000 <= pr <= 0x2_0000_0000,
        -0x200_0000_0000 <= dpv <= 0x200_0000_0000,
        -0x4_0000_0000_0000 <= chv <= 0x4_0000_0000_0000,
    ensures ({
        let (c2, q2, p2) = (c + s, q + if s == 1 { qs[j] as int } else { 0 }, p + if s == 1 { pr } else { 0 });
        let (dp2, ch2, d2) = (dp + if s == 1 { dpv } else { 0 }, ch + if s == 1 { chv } else { 0 },
            d + if s == 1 { ds[j] as int } else { 0 });
        &&& i64::MIN <= c2 <= i64::MAX && i64::MIN <= q2 <= i64::MAX && i64::MIN <= p2 <= i64::MAX
        &&& i64::MIN <= dp2 <= i64::MAX && i64::MIN <= ch2 <= i64::MAX && i64::MIN <= d2 <= i64::MAX
        &&& acc_ok(sel, qs, ps, ds, ts, bp, bd, bt, j + 1, c2 as i64, q2 as i64, p2 as i64,
            dp2 as i64, ch2 as i64, d2 as i64)
    }),
{
    lemma_csum_step(sel, one(), j);
    lemma_csum_step(sel, cqc(qs), j);
    lemma_csum_step(sel, cp(ps, bp as int), j);
    lemma_csum_step(sel, cdp(ps, ds, bp as int, bd as int), j);
    lemma_csum_step(sel, cch(ps, ds, ts, bp as int, bd as int, bt as int), j);
    lemma_csum_step(sel, cdc(ds), j);
    assert(cdp(ps, ds, bp as int, bd as int)(j) == dpv);
    assert(cch(ps, ds, ts, bp as int, bd as int, bt as int)(j) == chv);
}

/// The decoded chunk sums from a finished pass (code-domain quantity and discount, plus base times count).
#[inline]
fn finish(c: i64, q: i64, p: i64, dp: i64, ch: i64, d: i64, bq: i64, bp: i64, bd: i64, bt: i64,
    Ghost(sel): Ghost<spec_fn(int) -> bool>, Ghost(qs): Ghost<Seq<u16>>, Ghost(ps): Ghost<Seq<u32>>,
    Ghost(ds): Ghost<Seq<u8>>, Ghost(ts): Ghost<Seq<u8>>, Ghost(m): Ghost<int>) -> (r: ChunkSums)
    requires 0 <= m <= 2048, bases_ok(bq, bp, bd, bt), acc_ok(sel, qs, ps, ds, ts, bp, bd, bt, m, c, q, p, dp, ch, d),
    ensures sums_ok(r, sel, qs, ps, ds, ts, bq, bp, bd, bt, m),
    no_unwind
{
    proof {
        lemma_finish_sums(sel, qs, ds, bq as int, bd as int, m);
        assert(-0x1_0000_0000 * 2048 <= bq * c <= 0x1_0000_0000 * 2048) by (nonlinear_arith)
            requires -0x1_0000_0000 <= bq <= 0x1_0000_0000, 0 <= c <= 2048;
        assert(0 <= bd * c <= 100 * 2048) by (nonlinear_arith) requires 0 <= bd <= 100, 0 <= c <= 2048;
    }
    ChunkSums { cnt: c, q: q + bq * c, p, dp, ch, d: d + bd * c }
}

/// Bounds of a selection's decoded sums (each a sum over its selected positions; `s1` is unused).
pub proof fn lemma_csum_bounds_split(s1: spec_fn(int) -> bool, s2: spec_fn(int) -> bool, qs: Seq<u16>, ps: Seq<u32>,
    ds: Seq<u8>, ts: Seq<u8>, bp: i64, bd: i64, bt: i64, m: int)
    requires 0 <= m <= 2048, m <= qs.len(), m <= ps.len(), m <= ds.len(), m <= ts.len(), bases_ok(0, bp, bd, bt),
    ensures
        0 <= csum(s2, cqc(qs), m) <= m * 0xffff,
        -(m * 0x2_0000_0000) <= csum(s2, cp(ps, bp as int), m) <= m * 0x2_0000_0000,
        -(m * 0x200_0000_0000) <= csum(s2, cdp(ps, ds, bp as int, bd as int), m) <= m * 0x200_0000_0000,
        -(m * 0x4_0000_0000_0000) <= csum(s2, cch(ps, ds, ts, bp as int, bd as int, bt as int), m) <= m * 0x4_0000_0000_0000,
        0 <= csum(s2, cdc(ds), m) <= m * 255,
    decreases m,
{
    if m > 0 {
        lemma_csum_bounds_split(s1, s2, qs, ps, ds, ts, bp, bd, bt, m - 1);
        let j = m - 1;
        let pr = bp + ps[j];
        let x = (100 - bd) - ds[j];
        let y = (100 + bt) + ts[j];
        assert(-0x200_0000_0000 <= pr * x <= 0x200_0000_0000) by (nonlinear_arith)
            requires -0x2_0000_0000 <= pr <= 0x2_0000_0000, -255 <= x <= 100;
        assert(-0x4_0000_0000_0000 <= (pr * x) * y <= 0x4_0000_0000_0000) by (nonlinear_arith)
            requires -0x200_0000_0000 <= pr * x <= 0x200_0000_0000, 100 <= y <= 455;
        assert(cdp(ps, ds, bp as int, bd as int)(j) == pr * x);
        assert(cch(ps, ds, ts, bp as int, bd as int, bt as int)(j) == (pr * x) * y);
    }
}

/// Positions whose shipdate code is at most `thr` (a chunk whose rows all hold one pair).
pub open spec fn sel_date(ss: Seq<u16>, thr: int) -> spec_fn(int) -> bool {
    |i: int| ss[i] <= thr
}

fn chunk_date(qs: &[u16], ps: &[u32], ds: &[u8], ts: &[u8], ss: &[u16], m: usize, bq: i64, bp: i64, bd: i64, bt: i64,
    thr: i64) -> (r: ChunkSums)
    requires
        m <= CHUNK, m <= qs@.len(), m <= ps@.len(), m <= ds@.len(), m <= ts@.len(), m <= ss@.len(),
        bases_ok(bq, bp, bd, bt),
    ensures sums_ok(r, sel_date(ss@, thr as int), qs@, ps@, ds@, ts@, bq, bp, bd, bt, m as int),
    no_unwind
{
    let ghost sel = sel_date(ss@, thr as int);
    let k1 = 100 - bd;
    let k2 = 100 + bt;
    let (mut c, mut q, mut p, mut dp, mut ch, mut d) = (0i64, 0i64, 0i64, 0i64, 0i64, 0i64);
    let mut j: usize = 0;
    while j < m
        invariant
            j <= m, m <= CHUNK, m <= qs@.len(), m <= ps@.len(), m <= ds@.len(), m <= ts@.len(), m <= ss@.len(),
            bases_ok(bq, bp, bd, bt), k1 == 100 - bd, k2 == 100 + bt,
            sel == sel_date(ss@, thr as int),
            acc_ok(sel, qs@, ps@, ds@, ts@, bp, bd, bt, j as int, c, q, p, dp, ch, d),
        decreases m - j,
    {
        let s = b2i((ss[j] as i64) <= thr);
        let (pr, dpv, chv) = row_vals(ps[j], ds[j], ts[j], bp, k1, k2);
        proof {
            lemma_acc_step(sel, qs@, ps@, ds@, ts@, bp, bd, bt, j as int, c, q, p, dp, ch, d, s as int, pr as int, dpv as int, chv as int);
        }
        c = c + s;
        q = q + masked(qs[j] as i64, s);
        p = p + masked(pr, s);
        dp = dp + masked(dpv, s);
        ch = ch + masked(chv, s);
        d = d + masked(ds[j] as i64, s);
        j = j + 1;
    }
    finish(c, q, p, dp, ch, d, bq, bp, bd, bt, Ghost(sel), Ghost(qs@), Ghost(ps@), Ghost(ds@), Ghost(ts@), Ghost(m as int))
}

/// Positions whose code `xs[i]` is `x` (and its complement).
pub open spec fn sel_eq(xs: Seq<u8>, x: int) -> spec_fn(int) -> bool {
    |i: int| xs[i] == x
}

pub open spec fn sel_ne(xs: Seq<u8>, x: int) -> spec_fn(int) -> bool {
    |i: int| xs[i] != x
}

pub struct ChunkSums2 {
    pub a: ChunkSums,
    pub b: ChunkSums,
}

/// Positions holding the code pair `(r, l)` whose shipdate code is at most `thr`.
pub open spec fn sel_pair(rs: Seq<u8>, ls: Seq<u8>, ss: Seq<u16>, r: int, l: int, thr: int) -> spec_fn(int) -> bool {
    |i: int| rs[i] == r && ls[i] == l && ss[i] <= thr
}

fn chunk_pair(qs: &[u16], ps: &[u32], ds: &[u8], ts: &[u8], rs: &[u8], ls: &[u8], ss: &[u16], m: usize,
    bq: i64, bp: i64, bd: i64, bt: i64, r1: u8, l1: u8, thr: i64) -> (r: ChunkSums)
    requires
        m <= CHUNK, m <= qs@.len(), m <= ps@.len(), m <= ds@.len(), m <= ts@.len(),
        m <= rs@.len(), m <= ls@.len(), m <= ss@.len(),
        bases_ok(bq, bp, bd, bt),
    ensures sums_ok(r, sel_pair(rs@, ls@, ss@, r1 as int, l1 as int, thr as int), qs@, ps@, ds@, ts@, bq, bp, bd, bt, m as int),
    no_unwind
{
    let ghost sel = sel_pair(rs@, ls@, ss@, r1 as int, l1 as int, thr as int);
    let k1 = 100 - bd;
    let k2 = 100 + bt;
    let (mut c, mut q, mut p, mut dp, mut ch, mut d) = (0i64, 0i64, 0i64, 0i64, 0i64, 0i64);
    let mut j: usize = 0;
    while j < m
        invariant
            j <= m, m <= CHUNK, m <= qs@.len(), m <= ps@.len(), m <= ds@.len(), m <= ts@.len(),
            m <= rs@.len(), m <= ls@.len(), m <= ss@.len(),
            bases_ok(bq, bp, bd, bt), k1 == 100 - bd, k2 == 100 + bt,
            sel == sel_pair(rs@, ls@, ss@, r1 as int, l1 as int, thr as int),
            acc_ok(sel, qs@, ps@, ds@, ts@, bp, bd, bt, j as int, c, q, p, dp, ch, d),
        decreases m - j,
    {
        let s = b2i(rs[j] == r1 && ls[j] == l1 && (ss[j] as i64) <= thr);
        let (pr, dpv, chv) = row_vals(ps[j], ds[j], ts[j], bp, k1, k2);
        proof {
            lemma_acc_step(sel, qs@, ps@, ds@, ts@, bp, bd, bt, j as int, c, q, p, dp, ch, d, s as int, pr as int, dpv as int, chv as int);
        }
        c = c + s;
        q = q + masked(qs[j] as i64, s);
        p = p + masked(pr, s);
        dp = dp + masked(dpv, s);
        ch = ch + masked(chv, s);
        d = d + masked(ds[j] as i64, s);
        j = j + 1;
    }
    finish(c, q, p, dp, ch, d, bq, bp, bd, bt, Ghost(sel), Ghost(qs@), Ghost(ps@), Ghost(ds@), Ghost(ts@), Ghost(m as int))
}

/// Two pairs in one masked pass.
fn chunk_two(qs: &[u16], ps: &[u32], ds: &[u8], ts: &[u8], rs: &[u8], ls: &[u8], ss: &[u16], m: usize,
    bq: i64, bp: i64, bd: i64, bt: i64, r1: u8, l1: u8, r2: u8, l2: u8, thr: i64) -> (r: ChunkSums2)
    requires
        m <= CHUNK, m <= qs@.len(), m <= ps@.len(), m <= ds@.len(), m <= ts@.len(),
        m <= rs@.len(), m <= ls@.len(), m <= ss@.len(),
        bases_ok(bq, bp, bd, bt),
    ensures
        sums_ok(r.a, sel_pair(rs@, ls@, ss@, r1 as int, l1 as int, thr as int), qs@, ps@, ds@, ts@, bq, bp, bd, bt, m as int),
        sums_ok(r.b, sel_pair(rs@, ls@, ss@, r2 as int, l2 as int, thr as int), qs@, ps@, ds@, ts@, bq, bp, bd, bt, m as int),
    no_unwind
{
    let ghost s1 = sel_pair(rs@, ls@, ss@, r1 as int, l1 as int, thr as int);
    let ghost s2 = sel_pair(rs@, ls@, ss@, r2 as int, l2 as int, thr as int);
    let k1 = 100 - bd;
    let k2 = 100 + bt;
    let (mut c1, mut q1, mut p1, mut dp1, mut ch1, mut d1) = (0i64, 0i64, 0i64, 0i64, 0i64, 0i64);
    let (mut c2, mut q2, mut p2, mut dp2, mut ch2, mut d2) = (0i64, 0i64, 0i64, 0i64, 0i64, 0i64);
    let mut j: usize = 0;
    while j < m
        invariant
            j <= m, m <= CHUNK, m <= qs@.len(), m <= ps@.len(), m <= ds@.len(), m <= ts@.len(),
            m <= rs@.len(), m <= ls@.len(), m <= ss@.len(),
            bases_ok(bq, bp, bd, bt), k1 == 100 - bd, k2 == 100 + bt,
            s1 == sel_pair(rs@, ls@, ss@, r1 as int, l1 as int, thr as int),
            s2 == sel_pair(rs@, ls@, ss@, r2 as int, l2 as int, thr as int),
            acc_ok(s1, qs@, ps@, ds@, ts@, bp, bd, bt, j as int, c1, q1, p1, dp1, ch1, d1),
            acc_ok(s2, qs@, ps@, ds@, ts@, bp, bd, bt, j as int, c2, q2, p2, dp2, ch2, d2),
        decreases m - j,
    {
        let dq = (ss[j] as i64) <= thr;
        let a = b2i(rs[j] == r1 && ls[j] == l1 && dq);
        let b = b2i(rs[j] == r2 && ls[j] == l2 && dq);
        let (pr, dpv, chv) = row_vals(ps[j], ds[j], ts[j], bp, k1, k2);
        proof {
            lemma_acc_step(s1, qs@, ps@, ds@, ts@, bp, bd, bt, j as int, c1, q1, p1, dp1, ch1, d1, a as int, pr as int, dpv as int, chv as int);
            lemma_acc_step(s2, qs@, ps@, ds@, ts@, bp, bd, bt, j as int, c2, q2, p2, dp2, ch2, d2, b as int, pr as int, dpv as int, chv as int);
        }
        let cqv = qs[j] as i64;
        let cdv = ds[j] as i64;
        c1 = c1 + a;
        q1 = q1 + masked(cqv, a);
        p1 = p1 + masked(pr, a);
        dp1 = dp1 + masked(dpv, a);
        ch1 = ch1 + masked(chv, a);
        d1 = d1 + masked(cdv, a);
        c2 = c2 + b;
        q2 = q2 + masked(cqv, b);
        p2 = p2 + masked(pr, b);
        dp2 = dp2 + masked(dpv, b);
        ch2 = ch2 + masked(chv, b);
        d2 = d2 + masked(cdv, b);
        j = j + 1;
    }
    let ra = finish(c1, q1, p1, dp1, ch1, d1, bq, bp, bd, bt, Ghost(s1), Ghost(qs@), Ghost(ps@), Ghost(ds@), Ghost(ts@), Ghost(m as int));
    let rb = finish(c2, q2, p2, dp2, ch2, d2, bq, bp, bd, bt, Ghost(s2), Ghost(qs@), Ghost(ps@), Ghost(ds@), Ghost(ts@), Ghost(m as int));
    ChunkSums2 { a: ra, b: rb }
}

pub struct ChunkSums4 {
    pub a: ChunkSums,
    pub b: ChunkSums,
    pub c: ChunkSums,
    pub d: ChunkSums,
}

/// Four pairs in one masked pass.
fn chunk_four(qs: &[u16], ps: &[u32], ds: &[u8], ts: &[u8], rs: &[u8], ls: &[u8], ss: &[u16], m: usize,
    bq: i64, bp: i64, bd: i64, bt: i64, r1: u8, l1: u8, r2: u8, l2: u8, r3: u8, l3: u8, r4: u8, l4: u8, thr: i64)
    -> (r: ChunkSums4)
    requires
        m <= CHUNK, m <= qs@.len(), m <= ps@.len(), m <= ds@.len(), m <= ts@.len(),
        m <= rs@.len(), m <= ls@.len(), m <= ss@.len(),
        bases_ok(bq, bp, bd, bt),
    ensures
        sums_ok(r.a, sel_pair(rs@, ls@, ss@, r1 as int, l1 as int, thr as int), qs@, ps@, ds@, ts@, bq, bp, bd, bt, m as int),
        sums_ok(r.b, sel_pair(rs@, ls@, ss@, r2 as int, l2 as int, thr as int), qs@, ps@, ds@, ts@, bq, bp, bd, bt, m as int),
        sums_ok(r.c, sel_pair(rs@, ls@, ss@, r3 as int, l3 as int, thr as int), qs@, ps@, ds@, ts@, bq, bp, bd, bt, m as int),
        sums_ok(r.d, sel_pair(rs@, ls@, ss@, r4 as int, l4 as int, thr as int), qs@, ps@, ds@, ts@, bq, bp, bd, bt, m as int),
    no_unwind
{
    let ghost s1 = sel_pair(rs@, ls@, ss@, r1 as int, l1 as int, thr as int);
    let ghost s2 = sel_pair(rs@, ls@, ss@, r2 as int, l2 as int, thr as int);
    let ghost s3 = sel_pair(rs@, ls@, ss@, r3 as int, l3 as int, thr as int);
    let ghost s4 = sel_pair(rs@, ls@, ss@, r4 as int, l4 as int, thr as int);
    let k1 = 100 - bd;
    let k2 = 100 + bt;
    let (mut c1, mut q1, mut p1, mut dp1, mut ch1, mut d1) = (0i64, 0i64, 0i64, 0i64, 0i64, 0i64);
    let (mut c2, mut q2, mut p2, mut dp2, mut ch2, mut d2) = (0i64, 0i64, 0i64, 0i64, 0i64, 0i64);
    let (mut c3, mut q3, mut p3, mut dp3, mut ch3, mut d3) = (0i64, 0i64, 0i64, 0i64, 0i64, 0i64);
    let (mut c4, mut q4, mut p4, mut dp4, mut ch4, mut d4) = (0i64, 0i64, 0i64, 0i64, 0i64, 0i64);
    let mut j: usize = 0;
    while j < m
        invariant
            j <= m, m <= CHUNK, m <= qs@.len(), m <= ps@.len(), m <= ds@.len(), m <= ts@.len(),
            m <= rs@.len(), m <= ls@.len(), m <= ss@.len(),
            bases_ok(bq, bp, bd, bt), k1 == 100 - bd, k2 == 100 + bt,
            s1 == sel_pair(rs@, ls@, ss@, r1 as int, l1 as int, thr as int),
            s2 == sel_pair(rs@, ls@, ss@, r2 as int, l2 as int, thr as int),
            s3 == sel_pair(rs@, ls@, ss@, r3 as int, l3 as int, thr as int),
            s4 == sel_pair(rs@, ls@, ss@, r4 as int, l4 as int, thr as int),
            acc_ok(s1, qs@, ps@, ds@, ts@, bp, bd, bt, j as int, c1, q1, p1, dp1, ch1, d1),
            acc_ok(s2, qs@, ps@, ds@, ts@, bp, bd, bt, j as int, c2, q2, p2, dp2, ch2, d2),
            acc_ok(s3, qs@, ps@, ds@, ts@, bp, bd, bt, j as int, c3, q3, p3, dp3, ch3, d3),
            acc_ok(s4, qs@, ps@, ds@, ts@, bp, bd, bt, j as int, c4, q4, p4, dp4, ch4, d4),
        decreases m - j,
    {
        let dq = (ss[j] as i64) <= thr;
        let x = rs[j];
        let y = ls[j];
        let a = b2i(x == r1 && y == l1 && dq);
        let b = b2i(x == r2 && y == l2 && dq);
        let c = b2i(x == r3 && y == l3 && dq);
        let e = b2i(x == r4 && y == l4 && dq);
        let (pr, dpv, chv) = row_vals(ps[j], ds[j], ts[j], bp, k1, k2);
        proof {
            lemma_acc_step(s1, qs@, ps@, ds@, ts@, bp, bd, bt, j as int, c1, q1, p1, dp1, ch1, d1, a as int, pr as int, dpv as int, chv as int);
            lemma_acc_step(s2, qs@, ps@, ds@, ts@, bp, bd, bt, j as int, c2, q2, p2, dp2, ch2, d2, b as int, pr as int, dpv as int, chv as int);
            lemma_acc_step(s3, qs@, ps@, ds@, ts@, bp, bd, bt, j as int, c3, q3, p3, dp3, ch3, d3, c as int, pr as int, dpv as int, chv as int);
            lemma_acc_step(s4, qs@, ps@, ds@, ts@, bp, bd, bt, j as int, c4, q4, p4, dp4, ch4, d4, e as int, pr as int, dpv as int, chv as int);
        }
        let cqv = qs[j] as i64;
        let cdv = ds[j] as i64;
        c1 = c1 + a;
        q1 = q1 + masked(cqv, a);
        p1 = p1 + masked(pr, a);
        dp1 = dp1 + masked(dpv, a);
        ch1 = ch1 + masked(chv, a);
        d1 = d1 + masked(cdv, a);
        c2 = c2 + b;
        q2 = q2 + masked(cqv, b);
        p2 = p2 + masked(pr, b);
        dp2 = dp2 + masked(dpv, b);
        ch2 = ch2 + masked(chv, b);
        d2 = d2 + masked(cdv, b);
        c3 = c3 + c;
        q3 = q3 + masked(cqv, c);
        p3 = p3 + masked(pr, c);
        dp3 = dp3 + masked(dpv, c);
        ch3 = ch3 + masked(chv, c);
        d3 = d3 + masked(cdv, c);
        c4 = c4 + e;
        q4 = q4 + masked(cqv, e);
        p4 = p4 + masked(pr, e);
        dp4 = dp4 + masked(dpv, e);
        ch4 = ch4 + masked(chv, e);
        d4 = d4 + masked(cdv, e);
        j = j + 1;
    }
    let ra = finish(c1, q1, p1, dp1, ch1, d1, bq, bp, bd, bt, Ghost(s1), Ghost(qs@), Ghost(ps@), Ghost(ds@), Ghost(ts@), Ghost(m as int));
    let rb = finish(c2, q2, p2, dp2, ch2, d2, bq, bp, bd, bt, Ghost(s2), Ghost(qs@), Ghost(ps@), Ghost(ds@), Ghost(ts@), Ghost(m as int));
    let rc = finish(c3, q3, p3, dp3, ch3, d3, bq, bp, bd, bt, Ghost(s3), Ghost(qs@), Ghost(ps@), Ghost(ds@), Ghost(ts@), Ghost(m as int));
    let rd = finish(c4, q4, p4, dp4, ch4, d4, bq, bp, bd, bt, Ghost(s4), Ghost(qs@), Ghost(ps@), Ghost(ds@), Ghost(ts@), Ghost(m as int));
    ChunkSums4 { a: ra, b: rb, c: rc, d: rd }
}

/// Some position of the chunk holds the code pair `(r, l)` (a branch-free count, so it vectorizes).
fn has_pair(rs: &[u8], ls: &[u8], m: usize, r: u8, l: u8) -> (b: bool)
    requires m <= CHUNK, m <= rs@.len(), m <= ls@.len(),
    ensures b == exists|ii: int| 0 <= ii < m && rs@[ii] == r && ls@[ii] == l,
    no_unwind
{
    let mut c: i64 = 0;
    let mut j: usize = 0;
    while j < m
        invariant
            j <= m, m <= CHUNK, m <= rs@.len(), m <= ls@.len(), 0 <= c <= j,
            (c > 0) == exists|ii: int| 0 <= ii < j && rs@[ii] == r && ls@[ii] == l,
        decreases m - j,
    {
        let s = b2i(rs[j] == r && ls[j] == l);
        proof {
            if s == 1 {
                assert(rs@[j as int] == r && ls@[j as int] == l);
            }
            if c > 0 {
                let w = choose|ii: int| 0 <= ii < j && rs@[ii] == r && ls@[ii] == l;
                assert(0 <= w < j + 1);
            }
            if c + s > 0 && c == 0 {
                assert(s == 1);
            }
            if c + s == 0 {
                assert forall|ii: int| 0 <= ii < j + 1 implies !(rs@[ii] == r && ls@[ii] == l) by {
                    if ii < j {
                        assert(!(exists|k: int| 0 <= k < j && rs@[k] == r && ls@[k] == l));
                    }
                }
            }
        }
        c = c + s;
        j = j + 1;
    }
    c > 0
}

/// Min and max of the codes of a non-empty chunk (both attained). Branch-free, so it vectorizes.
fn code_range(xs: &[u8], m: usize) -> (r: (u8, u8))
    requires 0 < m <= xs@.len(),
    ensures
        r.0 <= r.1,
        forall|i: int| 0 <= i < m ==> r.0 <= #[trigger] xs@[i] <= r.1,
        exists|i: int| 0 <= i < m && xs@[i] == r.0,
        exists|i: int| 0 <= i < m && xs@[i] == r.1,
    no_unwind
{
    let mut lo: u8 = xs[0];
    let mut hi: u8 = xs[0];
    let mut j: usize = 1;
    while j < m
        invariant
            1 <= j <= m, m <= xs@.len(), lo <= hi,
            forall|i: int| 0 <= i < j ==> lo <= #[trigger] xs@[i] <= hi,
            exists|i: int| 0 <= i < j && xs@[i] == lo,
            exists|i: int| 0 <= i < j && xs@[i] == hi,
        decreases m - j,
    {
        let x = xs[j];
        proof {
            let wl = choose|i: int| 0 <= i < j && xs@[i] == lo;
            let wh = choose|i: int| 0 <= i < j && xs@[i] == hi;
            assert(0 <= wl < j + 1 && 0 <= wh < j + 1);
            assert(xs@[j as int] == x);
        }
        lo = if x < lo { x } else { lo };
        hi = if x > hi { x } else { hi };
        j = j + 1;
    }
    (lo, hi)
}

/// The smallest code of a chunk other than `lo` (`255` when every code is `lo`). Branch-free, so it vectorizes.
fn next_code(xs: &[u8], m: usize, lo: u8) -> (r: u8)
    requires m <= xs@.len(),
    ensures forall|i: int| 0 <= i < m && #[trigger] xs@[i] != lo ==> r <= xs@[i],
    no_unwind
{
    let mut nx: u8 = 255;
    let mut j: usize = 0;
    while j < m
        invariant
            j <= m, m <= xs@.len(),
            forall|i: int| 0 <= i < j && #[trigger] xs@[i] != lo ==> nx <= xs@[i],
        decreases m - j,
    {
        let x = xs[j];
        let y = if x == lo { 255u8 } else { x };
        nx = if y < nx { y } else { nx };
        j = j + 1;
    }
    nx
}

/// The code box `r0 ..= r1`, `l0 ..= l1` of a non-empty chunk's rf and ls codes, and `two`: every row's codes are
/// at the box's corners and the box is a line (two pairs at most, told apart by one column). From the chunk's
/// pair mask when it is known (`has`) and decodes (no code read), else from the codes (`two` only when `full`).
fn chunk_box(rs: &[u8], lss: &[u8], len: usize, full: bool, mk: u64, has: bool) -> (r: (u8, u8, u8, u8, bool))
    requires
        0 < len <= rs@.len(), len <= lss@.len(),
        has ==> forall|i: int| 0 <= i < len ==> #[trigger] marked(mk, rs@[i], lss@[i]),
    ensures
        r.0 <= r.1 && r.2 <= r.3,
        forall|i: int| 0 <= i < len ==> r.0 <= #[trigger] rs@[i] <= r.1,
        forall|i: int| 0 <= i < len ==> r.2 <= #[trigger] lss@[i] <= r.3,
        r.4 ==> r.0 == r.1 || r.2 == r.3,
        r.4 ==> forall|i: int| 0 <= i < len ==> (#[trigger] rs@[i] == r.0 || rs@[i] == r.1),
        r.4 ==> forall|i: int| 0 <= i < len ==> (#[trigger] lss@[i] == r.2 || lss@[i] == r.3),
    no_unwind
{
    if has {
        let (ok, r0, r1, l0, l1) = decode_mask(mk);
        if ok {
            proof {
                assert forall|i: int| 0 <= i < len implies (#[trigger] rs@[i] == r0 || rs@[i] == r1) by {
                    assert(marked(mk, rs@[i], lss@[i]));
                }
                assert forall|i: int| 0 <= i < len implies (#[trigger] lss@[i] == l0 || lss@[i] == l1) by {
                    assert(marked(mk, rs@[i], lss@[i]));
                }
            }
            return (r0, r1, l0, l1, true);
        }
    }
    let (r0, r1) = code_range(rs, len);
    let (l0, l1) = code_range(lss, len);
    let two = full && ((r0 < r1 && l0 == l1 && (r1 - r0 == 1 || next_code(rs, len, r0) == r1))
        || (r0 == r1 && l0 < l1 && (l1 - l0 == 1 || next_code(lss, len, l0) == l1)));
    proof {
        if two {
            assert forall|i: int| 0 <= i < len implies (#[trigger] rs@[i] == r0 || rs@[i] == r1) by {
                assert(r0 <= rs@[i] <= r1);
            }
            assert forall|i: int| 0 <= i < len implies (#[trigger] lss@[i] == l0 || lss@[i] == l1) by {
                assert(l0 <= lss@[i] <= l1);
            }
        }
    }
    (r0, r1, l0, l1, two)
}

// ------------------------------------------------------------------------------------------------ the group table

/// The value of kind `w` of a table: the count (`w == 5`) or sum `w` of entry `i`.
pub open spec fn tval(cnt: Seq<u64>, sum: Seq<i128>, i: int, w: int) -> int {
    if w == 5 { cnt[i] as int } else { sum[i * 5 + w] as int }
}

/// Field `w` of chunk sums (5: the count).
pub open spec fn ws(cs: ChunkSums, w: int) -> int {
    if w == 0 { cs.q as int } else if w == 1 { cs.p as int } else if w == 2 { cs.dp as int }
    else if w == 3 { cs.ch as int } else if w == 4 { cs.d as int } else { cs.cnt as int }
}

/// A table of `t` entries holding, per entry and kind, the model sums over the rows `lo .. hi`.
pub open spec fn tbl_ok(cnt: Seq<u64>, sum: Seq<i128>, m: Model, p: int, lo: int, hi: int, t: int) -> bool {
    &&& cnt.len() == t && sum.len() == 5 * t
    &&& forall|i: int, w: int| 0 <= i < t && 0 <= w <= 5 ==> #[trigger] tval(cnt, sum, i, w) == isum(m, p, i, w, lo, hi)
}

/// Add chunk sums to entry `i`.
fn add_out(out_cnt: &mut Vec<u64>, out_sum: &mut Vec<i128>, i: usize, cs: &ChunkSums)
    requires
        i < old(out_cnt)@.len(), old(out_sum)@.len() == 5 * old(out_cnt)@.len(),
        forall|w: int| 0 <= w <= 5 ==> -0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff
            <= #[trigger] tval(old(out_cnt)@, old(out_sum)@, i as int, w) + ws(*cs, w) <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff,
        0 <= cs.cnt, old(out_cnt)@[i as int] + cs.cnt <= u64::MAX,
    ensures
        final(out_cnt)@.len() == old(out_cnt)@.len(), final(out_sum)@.len() == old(out_sum)@.len(),
        forall|k: int, w: int| 0 <= k < final(out_cnt)@.len() && 0 <= w <= 5 ==> #[trigger] tval(final(out_cnt)@, final(out_sum)@, k, w)
            == tval(old(out_cnt)@, old(out_sum)@, k, w) + if k == i { ws(*cs, w) } else { 0 },
    no_unwind
{
    let ns = out_sum.len();
    let ghost nc = old(out_cnt)@.len() as int;
    assert(i * 5 + 4 < ns) by (nonlinear_arith) requires i < nc, ns == 5 * nc;
    let b = i * NSUMS;
    assert(tval(old(out_cnt)@, old(out_sum)@, i as int, 0) + ws(*cs, 0) == old(out_sum)@[b as int] + cs.q);
    assert(tval(old(out_cnt)@, old(out_sum)@, i as int, 1) + ws(*cs, 1) == old(out_sum)@[b + 1] + cs.p);
    assert(tval(old(out_cnt)@, old(out_sum)@, i as int, 2) + ws(*cs, 2) == old(out_sum)@[b + 2] + cs.dp);
    assert(tval(old(out_cnt)@, old(out_sum)@, i as int, 3) + ws(*cs, 3) == old(out_sum)@[b + 3] + cs.ch);
    assert(tval(old(out_cnt)@, old(out_sum)@, i as int, 4) + ws(*cs, 4) == old(out_sum)@[b + 4] + cs.d);
    out_cnt[i] = out_cnt[i] + cs.cnt as u64;
    out_sum[b] = out_sum[b] + cs.q as i128;
    out_sum[b + 1] = out_sum[b + 1] + cs.p as i128;
    out_sum[b + 2] = out_sum[b + 2] + cs.dp as i128;
    out_sum[b + 3] = out_sum[b + 3] + cs.ch as i128;
    out_sum[b + 4] = out_sum[b + 4] + cs.d as i128;
    assert forall|k: int, w: int| 0 <= k < out_cnt@.len() && 0 <= w <= 5 implies #[trigger] tval(out_cnt@, out_sum@, k, w)
        == tval(old(out_cnt)@, old(out_sum)@, k, w) + if k == i { ws(*cs, w) } else { 0 } by {
        if w < 5 {
            if k != i {
                assert(k * 5 + w != b && k * 5 + w != b + 1 && k * 5 + w != b + 2 && k * 5 + w != b + 3 && k * 5 + w != b + 4)
                    by (nonlinear_arith) requires k != i, 0 <= w < 5, b == i * 5;
            }
        }
    }
}

/// Two group indices `x * n + y` with `y < n` are equal exactly when both parts are.
pub proof fn lemma_index_unique(x1: int, y1: int, x2: int, y2: int, n: int)
    requires n >= 1, 0 <= y1 < n, 0 <= y2 < n,
    ensures (x1 * n + y1 == x2 * n + y2) <==> (x1 == x2 && y1 == y2),
{
    if x1 * n + y1 == x2 * n + y2 && x1 != x2 {
        if x1 < x2 {
            assert(x1 * n + n <= x2 * n) by (nonlinear_arith) requires x1 < x2, n >= 1;
        } else {
            assert(x2 * n + n <= x1 * n) by (nonlinear_arith) requires x2 < x1, n >= 1;
        }
    }
}

/// The part of a group index `x * n + y` (`0 <= y < n`): `x` and `y` are its quotient and remainder by `n`.
pub proof fn lemma_index_parts(x: int, y: int, n: int)
    requires n >= 1, 0 <= y < n,
    ensures (x * n + y) / n == x, (x * n + y) % n == y,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x * n + y, n, x, y);
}

/// The model rows of one chunk: rows `c0 .. c0 + len` of block `g`, read through the chunk's slices.
pub open spec fn chunk_rows(m: Model, g: int, c0: int, len: int, qs: Seq<u16>, ps: Seq<u32>, ds: Seq<u8>, ts: Seq<u8>,
    rs: Seq<u8>, ls: Seq<u8>, ss: Seq<u16>, bq: i64, bp: i64, bd: i64, bt: i64, brf: int, bls: int) -> bool
{
    &&& model_wf(m) && 0 <= g < m.nb && len >= 0 && c0 >= 0 && c0 + len <= m.n
    &&& g * m.bsize <= c0 && c0 + len <= (g + 1) * m.bsize
    &&& qs.len() == len && ps.len() == len && ds.len() == len && ts.len() == len
    &&& rs.len() == len && ls.len() == len && ss.len() == len
    &&& qs == m.qty.subrange(c0, c0 + len) && ps == m.price.subrange(c0, c0 + len)
    &&& ds == m.disc.subrange(c0, c0 + len) && ts == m.tax.subrange(c0, c0 + len)
    &&& rs == m.rf.subrange(c0, c0 + len) && ls == m.ls.subrange(c0, c0 + len) && ss == m.ship.subrange(c0, c0 + len)
    &&& bq == m.qty_b[g] && bp == m.price_b[g] && bd == m.disc_b[g] && bt == m.tax_b[g]
    &&& brf == m.rf_b[g] && bls == m.ls_b[g]
}

/// Row by row, the chunk's decoded values and group index are the model's.
pub proof fn lemma_chunk_row(m: Model, g: int, c0: int, len: int, qs: Seq<u16>, ps: Seq<u32>, ds: Seq<u8>, ts: Seq<u8>,
    rs: Seq<u8>, ls: Seq<u8>, ss: Seq<u16>, bq: i64, bp: i64, bd: i64, bt: i64, brf: int, bls: int, i: int)
    requires chunk_rows(m, g, c0, len, qs, ps, ds, ts, rs, ls, ss, bq, bp, bd, bt, brf, bls), 0 <= i < len,
    ensures
        blk(m, c0 + i) == g,
        cq(qs, bq as int)(i) == mval(m, 0, c0 + i),
        cp(ps, bp as int)(i) == mval(m, 1, c0 + i),
        cdp(ps, ds, bp as int, bd as int)(i) == mval(m, 2, c0 + i),
        cch(ps, ds, ts, bp as int, bd as int, bt as int)(i) == mval(m, 3, c0 + i),
        cd(ds, bd as int)(i) == mval(m, 4, c0 + i),
        one()(i) == mval(m, 5, c0 + i),
        gidx(m, c0 + i) == (brf + rs[i]) * m.nls + (bls + ls[i]),
        0 <= bls + ls[i] < m.nls,
        0 <= brf + rs[i] < m.nrf,
        shv(m, c0 + i) == m.ship_b[g] + ss[i],
{
    lemma_blk_of(m, g, c0 + i);
    assert(qs[i] == m.qty[c0 + i] && ps[i] == m.price[c0 + i] && ds[i] == m.disc[c0 + i] && ts[i] == m.tax[c0 + i]);
    assert(rs[i] == m.rf[c0 + i] && ls[i] == m.ls[c0 + i] && ss[i] == m.ship[c0 + i]);
    assert(0 <= rfi(m, c0 + i) < m.nrf && 0 <= lsi(m, c0 + i) < m.nls);
}

/// Sums of a selection over a chunk that agrees with the model's selection of entry `tt` row by row are the model
/// sums of `tt` over the chunk's rows.
pub proof fn lemma_sums_isum(r: ChunkSums, sel: spec_fn(int) -> bool, m: Model, p: int, tt: int, g: int, c0: int, len: int,
    qs: Seq<u16>, ps: Seq<u32>, ds: Seq<u8>, ts: Seq<u8>, rs: Seq<u8>, ls: Seq<u8>, ss: Seq<u16>,
    bq: i64, bp: i64, bd: i64, bt: i64, brf: int, bls: int)
    requires
        chunk_rows(m, g, c0, len, qs, ps, ds, ts, rs, ls, ss, bq, bp, bd, bt, brf, bls),
        sums_ok(r, sel, qs, ps, ds, ts, bq, bp, bd, bt, len),
        forall|i: int| 0 <= i < len ==> #[trigger] sel(i) == msel(m, p, tt, c0 + i),
    ensures forall|w: int| 0 <= w <= 5 ==> #[trigger] ws(r, w) == isum(m, p, tt, w, c0, c0 + len),
{
    assert forall|i: int| 0 <= i < len implies #[trigger] cq(qs, bq as int)(i) == mval(m, 0, c0 + i) by {
        lemma_chunk_row(m, g, c0, len, qs, ps, ds, ts, rs, ls, ss, bq, bp, bd, bt, brf, bls, i);
    }
    assert forall|i: int| 0 <= i < len implies #[trigger] cp(ps, bp as int)(i) == mval(m, 1, c0 + i) by {
        lemma_chunk_row(m, g, c0, len, qs, ps, ds, ts, rs, ls, ss, bq, bp, bd, bt, brf, bls, i);
    }
    assert forall|i: int| 0 <= i < len implies #[trigger] cdp(ps, ds, bp as int, bd as int)(i) == mval(m, 2, c0 + i) by {
        lemma_chunk_row(m, g, c0, len, qs, ps, ds, ts, rs, ls, ss, bq, bp, bd, bt, brf, bls, i);
    }
    assert forall|i: int| 0 <= i < len implies #[trigger] cch(ps, ds, ts, bp as int, bd as int, bt as int)(i) == mval(m, 3, c0 + i) by {
        lemma_chunk_row(m, g, c0, len, qs, ps, ds, ts, rs, ls, ss, bq, bp, bd, bt, brf, bls, i);
    }
    assert forall|i: int| 0 <= i < len implies #[trigger] cd(ds, bd as int)(i) == mval(m, 4, c0 + i) by {
        lemma_chunk_row(m, g, c0, len, qs, ps, ds, ts, rs, ls, ss, bq, bp, bd, bt, brf, bls, i);
    }
    assert forall|i: int| 0 <= i < len implies #[trigger] one()(i) == mval(m, 5, c0 + i) by {
        lemma_chunk_row(m, g, c0, len, qs, ps, ds, ts, rs, ls, ss, bq, bp, bd, bt, brf, bls, i);
    }
    lemma_isum_csum(m, p, tt, 0, c0, len, sel, cq(qs, bq as int));
    lemma_isum_csum(m, p, tt, 1, c0, len, sel, cp(ps, bp as int));
    lemma_isum_csum(m, p, tt, 2, c0, len, sel, cdp(ps, ds, bp as int, bd as int));
    lemma_isum_csum(m, p, tt, 3, c0, len, sel, cch(ps, ds, ts, bp as int, bd as int, bt as int));
    lemma_isum_csum(m, p, tt, 4, c0, len, sel, cd(ds, bd as int));
    lemma_isum_csum(m, p, tt, 5, c0, len, sel, one());
}

/// The rows of the task's blocks satisfy the fast path's bounds.
pub open spec fn rows_ok(m: Model, lo: int, hi: int) -> bool {
    forall|j: int| lo <= j < hi ==> #[trigger] block_ok(m, blk(m, j))
}

/// Overflow freedom of adding a chunk's sums (rows `c0 .. c1`) to a table of the rows `lo .. c0`.
pub proof fn lemma_add_fits(m: Model, p: int, i: int, lo: int, c0: int, c1: int)
    requires model_wf(m), 0 <= lo <= c0 <= c1 <= m.n, rows_ok(m, lo, c1), m.n <= u64::MAX,
    ensures
        forall|w: int| 0 <= w <= 5 ==> -0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff
            <= #[trigger] (isum(m, p, i, w, lo, c0) + isum(m, p, i, w, c0, c1)) <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff,
        0 <= isum(m, p, i, 5, lo, c0) + isum(m, p, i, 5, c0, c1) <= u64::MAX,
        forall|w: int| 0 <= w <= 5 ==> #[trigger] isum(m, p, i, w, lo, c1) == isum(m, p, i, w, lo, c0) + isum(m, p, i, w, c0, c1),
{
    assert forall|w: int| 0 <= w <= 5 implies #[trigger] isum(m, p, i, w, lo, c1) == isum(m, p, i, w, lo, c0) + isum(m, p, i, w, c0, c1) by {
        lemma_isum_split(m, p, i, w, lo, c0, c1);
    }
    assert forall|w: int| 0 <= w <= 5 implies -0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff
        <= #[trigger] (isum(m, p, i, w, lo, c0) + isum(m, p, i, w, c0, c1)) <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff by {
        lemma_isum_split(m, p, i, w, lo, c0, c1);
        lemma_isum_bound(m, p, i, w, lo, c1);
        assert(vbound(w) <= 0x4_0000_0000_0000);
        assert((c1 - lo) * vbound(w) <= 0x1_0000_0000_0000_0000 * 0x4_0000_0000_0000) by (nonlinear_arith)
            requires 0 <= c1 - lo <= 0x1_0000_0000_0000_0000, 0 <= vbound(w) <= 0x4_0000_0000_0000;
    }
    lemma_isum_split(m, p, i, 5, lo, c0, c1);
    lemma_isum_bound(m, p, i, 5, lo, c1);
}


// ------------------------------------------------------------------------------------------------ one chunk

/// The column slices of the stored lineitem parts the scan reads (zero-copy extents of whole parts).
#[derive(Clone, Copy)]
pub struct Cols {
    pub qty: &'static [u16],
    pub qty_b: &'static [i64],
    pub price: &'static [u32],
    pub price_b: &'static [i64],
    pub disc: &'static [u8],
    pub disc_b: &'static [i64],
    pub tax: &'static [u8],
    pub tax_b: &'static [i64],
    pub rf: &'static [u8],
    pub rf_b: &'static [u64],
    pub ls: &'static [u8],
    pub ls_b: &'static [u64],
    pub ship: &'static [u16],
    pub ship_b: &'static [i64],
    pub ship_z: &'static [i64],
    /// The pair masks of storage li_pairmask (one per `CHUNK` stored rows; empty: unknown) and their count.
    pub mk: &'static [u64],
    pub nmk: usize,
}

/// The masks' count, and every stored row's code pair marked in the mask of its `CHUNK`-row chunk.
pub open spec fn masks_hold(c: Cols) -> bool {
    &&& c.nmk == c.mk@.len()
    &&& c.nmk > 0 ==> LP::masks_ok(c.rf@, c.ls@, c.mk@)
}

/// The model the slices denote.
pub open spec fn cols_model(c: Cols, n: int, bsize: int, nrf: int, nls: int) -> Model {
    Model {
        qty: c.qty@, qty_b: c.qty_b@, price: c.price@, price_b: c.price_b@, disc: c.disc@, disc_b: c.disc_b@,
        tax: c.tax@, tax_b: c.tax_b@, rf: c.rf@, rf_b: c.rf_b@, ls: c.ls@, ls_b: c.ls_b@,
        ship: c.ship@, ship_b: c.ship_b@, ship_z: c.ship_z@,
        n, bsize, nb: c.qty_b@.len() as int, nrf, nls,
    }
}

/// Elements `lo .. hi` of a slice.
fn sub<T>(s: &'static [T], lo: usize, hi: usize) -> (r: &'static [T])
    requires lo <= hi <= s@.len(),
    ensures r@ == s@.subrange(lo as int, hi as int),
    no_unwind
{
    let (_, tail) = s.split_at(lo);
    let (mid, _) = tail.split_at(hi - lo);
    proof {
        assert(mid@ =~= s@.subrange(lo as int, hi as int));
    }
    mid
}

/// Entries other than the chunk's targets get nothing from the chunk's rows.
proof fn lemma_untouched(m: Model, p: int, k: int, c0: int, c1: int)
    requires forall|j: int| c0 <= j < c1 ==> #[trigger] gidx(m, j) != k,
    ensures forall|w: int| 0 <= w <= 5 ==> #[trigger] isum(m, p, k, w, c0, c1) == 0,
{
    assert forall|w: int| 0 <= w <= 5 implies #[trigger] isum(m, p, k, w, c0, c1) == 0 by {
        lemma_isum_none(m, p, k, w, c0, c1);
    }
}

/// The table over rows `lo .. c0` plus the chunk's sums for entries below `k` (or exactly the entries `tgt`).
pub open spec fn tbl_part(cnt: Seq<u64>, sum: Seq<i128>, m: Model, p: int, lo: int, c0: int, c1: int, t: int,
    done: spec_fn(int) -> bool) -> bool
{
    &&& cnt.len() == t && sum.len() == 5 * t
    &&& forall|i: int, w: int| 0 <= i < t && 0 <= w <= 5 ==> #[trigger] tval(cnt, sum, i, w)
            == isum(m, p, i, w, lo, c0) + if done(i) { isum(m, p, i, w, c0, c1) } else { 0 }
}

/// Add the chunk sums of entry `tt` (the model sums of its rows) to a partial table.
fn add_entry(out_cnt: &mut Vec<u64>, out_sum: &mut Vec<i128>, tt: usize, cs: &ChunkSums, Ghost(m): Ghost<Model>,
    Ghost(p): Ghost<int>, Ghost(lo): Ghost<int>, Ghost(c0): Ghost<int>, Ghost(c1): Ghost<int>, Ghost(t): Ghost<int>,
    Ghost(done): Ghost<spec_fn(int) -> bool>)
    requires
        model_wf(m), m.n <= u64::MAX, 0 <= lo <= c0 <= c1 <= m.n, rows_ok(m, lo, c1),
        0 <= tt < t, !done(tt as int),
        tbl_part(old(out_cnt)@, old(out_sum)@, m, p, lo, c0, c1, t, done),
        forall|w: int| 0 <= w <= 5 ==> #[trigger] ws(*cs, w) == isum(m, p, tt as int, w, c0, c1),
    ensures
        tbl_part(final(out_cnt)@, final(out_sum)@, m, p, lo, c0, c1, t, |i: int| done(i) || i == tt),
    no_unwind
{
    proof {
        lemma_add_fits(m, p, tt as int, lo, c0, c1);
        assert(tval(old(out_cnt)@, old(out_sum)@, tt as int, 5) == old(out_cnt)@[tt as int] as int);
        assert(ws(*cs, 5) == cs.cnt);
        assert forall|w: int| 0 <= w <= 5 implies -0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff
            <= #[trigger] tval(old(out_cnt)@, old(out_sum)@, tt as int, w) + ws(*cs, w) <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff by {
            assert(tval(old(out_cnt)@, old(out_sum)@, tt as int, w) == isum(m, p, tt as int, w, lo, c0));
        }
        lemma_isum_bound(m, p, tt as int, 5, c0, c1);
    }
    add_out(out_cnt, out_sum, tt, cs);
}

/// Table entry `i` is the group of a code pair inside the box `r0 ..= r1` x `l0 ..= l1` of the block with bases
/// `brf`, `bls`.
pub open spec fn in_box_spec(i: int, nls: int, brf: int, bls: int, r0: int, r1: int, l0: int, l1: int) -> bool {
    &&& brf + r0 <= i / nls <= brf + r1
    &&& bls + l0 <= i % nls <= bls + l1
}

fn in_box(i: usize, nls: usize, brf: u64, bls: u64, r0: u8, r1: u8, l0: u8, l1: u8) -> (b: bool)
    requires nls >= 1,
    ensures b == in_box_spec(i as int, nls as int, brf as int, bls as int, r0 as int, r1 as int, l0 as int, l1 as int),
    no_unwind
{
    let a = (i / nls) as u64;
    let b = (i % nls) as u64;
    a >= brf && b >= bls && a - brf >= r0 as u64 && a - brf <= r1 as u64 && b - bls >= l0 as u64 && b - bls <= l1 as u64
}

/// The code pair of a table entry inside the box.
fn box_codes(i: usize, nls: usize, brf: u64, bls: u64) -> (r: (u8, u8))
    requires nls >= 1, brf <= i / nls <= brf + 255, bls <= i % nls <= bls + 255,
    ensures r.0 == i / nls - brf, r.1 == i % nls - bls,
    no_unwind
{
    (((i / nls) as u64 - brf) as u8, ((i % nls) as u64 - bls) as u8)
}

/// The masked selection of the code pair of entry `i` is the model's selection of entry `i`.
proof fn lemma_entry_sel(m: Model, p: int, g: int, c0: int, len: int, qs: Seq<u16>, ps: Seq<u32>, ds: Seq<u8>, ts: Seq<u8>,
    rs: Seq<u8>, ls: Seq<u8>, ss: Seq<u16>, bq: i64, bp: i64, bd: i64, bt: i64, brf: int, bls: int, i: int, ra: int, la: int,
    thr: int)
    requires
        chunk_rows(m, g, c0, len, qs, ps, ds, ts, rs, ls, ss, bq, bp, bd, bt, brf, bls),
        i >= 0, ra == i / m.nls - brf, la == i % m.nls - bls,
        forall|ii: int| 0 <= ii < len ==> (#[trigger] shv(m, c0 + ii) <= p) == (ss[ii] <= thr),
    ensures forall|ii: int| 0 <= ii < len ==> #[trigger] sel_pair(rs, ls, ss, ra, la, thr)(ii) == msel(m, p, i, c0 + ii),
{
    let nls = m.nls;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, nls);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(i, nls);
    assert(nls * (i / nls) == (i / nls) * nls) by (nonlinear_arith);
    assert forall|ii: int| 0 <= ii < len implies #[trigger] sel_pair(rs, ls, ss, ra, la, thr)(ii) == msel(m, p, i, c0 + ii) by {
        lemma_chunk_row(m, g, c0, len, qs, ps, ds, ts, rs, ls, ss, bq, bp, bd, bt, brf, bls, ii);
        lemma_index_unique(brf + rs[ii], bls + ls[ii], i / nls, i % nls, nls);
    }
}

/// An entry outside the box gets nothing from the chunk's rows (their code pairs lie in the box).
proof fn lemma_entry_empty(m: Model, p: int, g: int, c0: int, len: int, qs: Seq<u16>, ps: Seq<u32>, ds: Seq<u8>, ts: Seq<u8>,
    rs: Seq<u8>, ls: Seq<u8>, ss: Seq<u16>, bq: i64, bp: i64, bd: i64, bt: i64, brf: int, bls: int, i: int,
    r0: int, r1: int, l0: int, l1: int)
    requires
        chunk_rows(m, g, c0, len, qs, ps, ds, ts, rs, ls, ss, bq, bp, bd, bt, brf, bls),
        i >= 0, !in_box_spec(i, m.nls, brf, bls, r0, r1, l0, l1),
        forall|ii: int| 0 <= ii < len ==> r0 <= #[trigger] rs[ii] <= r1,
        forall|ii: int| 0 <= ii < len ==> l0 <= #[trigger] ls[ii] <= l1,
    ensures forall|w: int| 0 <= w <= 5 ==> #[trigger] isum(m, p, i, w, c0, c0 + len) == 0,
{
    let nls = m.nls;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, nls);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(i, nls);
    assert(nls * (i / nls) == (i / nls) * nls) by (nonlinear_arith);
    assert forall|j: int| c0 <= j < c0 + len implies #[trigger] gidx(m, j) != i by {
        let ii = j - c0;
        lemma_chunk_row(m, g, c0, len, qs, ps, ds, ts, rs, ls, ss, bq, bp, bd, bt, brf, bls, ii);
        assert(r0 <= rs[ii] <= r1 && l0 <= ls[ii] <= l1);
        lemma_index_unique(brf + rs[ii], bls + ls[ii], i / nls, i % nls, nls);
    }
    lemma_untouched(m, p, i, c0, c0 + len);
}

/// An entry whose code pair no row of the chunk holds gets nothing from the chunk's rows.
proof fn lemma_entry_absent(m: Model, p: int, g: int, c0: int, len: int, qs: Seq<u16>, ps: Seq<u32>, ds: Seq<u8>, ts: Seq<u8>,
    rs: Seq<u8>, ls: Seq<u8>, ss: Seq<u16>, bq: i64, bp: i64, bd: i64, bt: i64, brf: int, bls: int, i: int, ra: int, la: int)
    requires
        chunk_rows(m, g, c0, len, qs, ps, ds, ts, rs, ls, ss, bq, bp, bd, bt, brf, bls),
        i >= 0, ra == i / m.nls - brf, la == i % m.nls - bls,
        !(exists|ii: int| 0 <= ii < len && rs[ii] == ra && ls[ii] == la),
    ensures forall|w: int| 0 <= w <= 5 ==> #[trigger] isum(m, p, i, w, c0, c0 + len) == 0,
{
    let nls = m.nls;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, nls);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(i, nls);
    assert(nls * (i / nls) == (i / nls) * nls) by (nonlinear_arith);
    assert forall|j: int| c0 <= j < c0 + len implies #[trigger] gidx(m, j) != i by {
        let ii = j - c0;
        lemma_chunk_row(m, g, c0, len, qs, ps, ds, ts, rs, ls, ss, bq, bp, bd, bt, brf, bls, ii);
        lemma_index_unique(brf + rs[ii], bls + ls[ii], i / nls, i % nls, nls);
        assert(!(rs[ii] == ra && ls[ii] == la));
    }
    lemma_untouched(m, p, i, c0, c0 + len);
}

/// Some row of the chunk holds the code pair `(ra, la)`.
pub open spec fn holds(rs: Seq<u8>, ls: Seq<u8>, len: int, ra: int, la: int) -> bool {
    exists|ii: int| 0 <= ii < len && rs[ii] == ra && ls[ii] == la
}

/// Entry `k` is one of the first `np` slots `e0, e1, e2, e3`.
pub open spec fn in_slots(k: int, np: int, e0: int, e1: int, e2: int, e3: int) -> bool {
    (np > 0 && k == e0) || (np > 1 && k == e1) || (np > 2 && k == e2) || (np > 3 && k == e3)
}

/// The table entries inside the chunk's code box that some row holds, in increasing order, when there are at most
/// four of them (`np <= 4` slots); `np == 5` when there are more.
fn present_entries(rs: &[u8], lss: &[u8], len: usize, t: usize, nls: usize, brf: u64, bls: u64,
    r0: u8, r1: u8, l0: u8, l1: u8) -> (r: (usize, usize, usize, usize, usize))
    requires len <= CHUNK, len <= rs@.len(), len <= lss@.len(), nls >= 1, t <= MAXT,
    ensures
        r.0 <= 5,
        r.0 <= 4 ==> forall|k: int| 0 <= k < t
            && #[trigger] in_box_spec(k, nls as int, brf as int, bls as int, r0 as int, r1 as int, l0 as int, l1 as int)
            && !in_slots(k, r.0 as int, r.1 as int, r.2 as int, r.3 as int, r.4 as int)
            ==> !holds(rs@, lss@, len as int, k / (nls as int) - brf, k % (nls as int) - bls),
        r.0 > 0 ==> r.1 < t && in_box_spec(r.1 as int, nls as int, brf as int, bls as int, r0 as int, r1 as int, l0 as int, l1 as int),
        r.0 > 1 ==> r.1 < r.2 < t && in_box_spec(r.2 as int, nls as int, brf as int, bls as int, r0 as int, r1 as int, l0 as int, l1 as int),
        r.0 > 2 ==> r.2 < r.3 < t && in_box_spec(r.3 as int, nls as int, brf as int, bls as int, r0 as int, r1 as int, l0 as int, l1 as int),
        r.0 > 3 ==> r.3 < r.4 < t && in_box_spec(r.4 as int, nls as int, brf as int, bls as int, r0 as int, r1 as int, l0 as int, l1 as int),
    no_unwind
{
    let mut np: usize = 0;
    let (mut e0, mut e1, mut e2, mut e3) = (0usize, 0usize, 0usize, 0usize);
    let mut i: usize = 0;
    while i < t
        invariant
            len <= CHUNK, len <= rs@.len(), len <= lss@.len(), nls >= 1, t <= MAXT, i <= t, np <= 4,
            forall|k: int| 0 <= k < i
                && #[trigger] in_box_spec(k, nls as int, brf as int, bls as int, r0 as int, r1 as int, l0 as int, l1 as int)
                && !in_slots(k, np as int, e0 as int, e1 as int, e2 as int, e3 as int)
                ==> !holds(rs@, lss@, len as int, k / (nls as int) - brf, k % (nls as int) - bls),
            np > 0 ==> e0 < i && in_box_spec(e0 as int, nls as int, brf as int, bls as int, r0 as int, r1 as int, l0 as int, l1 as int),
            np > 1 ==> e0 < e1 < i && in_box_spec(e1 as int, nls as int, brf as int, bls as int, r0 as int, r1 as int, l0 as int, l1 as int),
            np > 2 ==> e1 < e2 < i && in_box_spec(e2 as int, nls as int, brf as int, bls as int, r0 as int, r1 as int, l0 as int, l1 as int),
            np > 3 ==> e2 < e3 < i && in_box_spec(e3 as int, nls as int, brf as int, bls as int, r0 as int, r1 as int, l0 as int, l1 as int),
        decreases t - i,
    {
        if in_box(i, nls, brf, bls, r0, r1, l0, l1) {
            let (ra, la) = box_codes(i, nls, brf, bls);
            if has_pair(rs, lss, len, ra, la) {
                if np == 4 {
                    return (5, e0, e1, e2, e3);
                }
                if np == 0 {
                    e0 = i;
                } else if np == 1 {
                    e1 = i;
                } else if np == 2 {
                    e2 = i;
                } else {
                    e3 = i;
                }
                np = np + 1;
            }
        }
        i = i + 1;
    }
    (np, e0, e1, e2, e3)
}

/// A full chunk (every row passes the date bound) whose box holds three or four present entries: one masked
/// pass adds them all (a fourth slot repeats the third). Returns false, leaving the table unchanged, otherwise.
fn try_multi(out_cnt: &mut Vec<u64>, out_sum: &mut Vec<i128>, qs: &[u16], ps: &[u32], ds: &[u8], ts: &[u8],
    rs: &[u8], lss: &[u8], ss: &[u16], g: usize, c0: usize, len: usize, bq: i64, bp: i64, bd: i64, bt: i64,
    brf: u64, bls: u64, r0: u8, r1: u8, l0: u8, l1: u8, nls: usize, t: usize,
    Ghost(m): Ghost<Model>, Ghost(p): Ghost<int>, Ghost(rlo): Ghost<int>) -> (done: bool)
    requires
        chunk_rows(m, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt, brf as int, bls as int),
        model_wf(m), m.n <= u64::MAX, 0 <= rlo <= c0, rows_ok(m, rlo, c0 + len),
        len <= CHUNK, nls == m.nls, t == m.nrf * m.nls, t <= MAXT, bases_ok(bq, bp, bd, bt),
        forall|ii: int| 0 <= ii < len ==> r0 <= #[trigger] rs@[ii] <= r1,
        forall|ii: int| 0 <= ii < len ==> l0 <= #[trigger] lss@[ii] <= l1,
        forall|j: int| c0 <= j < c0 + len ==> #[trigger] shv(m, j) <= p,
        tbl_ok(old(out_cnt)@, old(out_sum)@, m, p, rlo, c0 as int, t as int),
    ensures
        done ==> tbl_ok(final(out_cnt)@, final(out_sum)@, m, p, rlo, c0 + len, t as int),
        !done ==> final(out_cnt)@ == old(out_cnt)@ && final(out_sum)@ == old(out_sum)@,
    no_unwind
{
    let (np, e0, e1, e2, e3) = present_entries(rs, lss, len, t, nls, brf, bls, r0, r1, l0, l1);
    if np != 3 && np != 4 {
        return false;
    }
    let ghost c1 = c0 + len;
    let thr2: i64 = 0x10000;
    let e3x = if np == 4 { e3 } else { e2 };
    let (ra0, la0) = box_codes(e0, nls, brf, bls);
    let (ra1, la1) = box_codes(e1, nls, brf, bls);
    let (ra2, la2) = box_codes(e2, nls, brf, bls);
    let (ra3, la3) = box_codes(e3x, nls, brf, bls);
    let cs = chunk_four(qs, ps, ds, ts, rs, lss, ss, len, bq, bp, bd, bt, ra0, la0, ra1, la1, ra2, la2, ra3, la3, thr2);
    let ghost none = |i: int| false;
    proof {
        assert forall|ii: int| 0 <= ii < len implies (#[trigger] shv(m, c0 + ii) <= p) == (ss@[ii] <= thr2) by {
            assert(shv(m, c0 + ii) <= p);
        }
        lemma_entry_sel(m, p, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt,
            brf as int, bls as int, e0 as int, ra0 as int, la0 as int, thr2 as int);
        lemma_entry_sel(m, p, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt,
            brf as int, bls as int, e1 as int, ra1 as int, la1 as int, thr2 as int);
        lemma_entry_sel(m, p, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt,
            brf as int, bls as int, e2 as int, ra2 as int, la2 as int, thr2 as int);
        lemma_entry_sel(m, p, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt,
            brf as int, bls as int, e3x as int, ra3 as int, la3 as int, thr2 as int);
        lemma_sums_isum(cs.a, sel_pair(rs@, lss@, ss@, ra0 as int, la0 as int, thr2 as int), m, p, e0 as int, g as int, c0 as int,
            len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt, brf as int, bls as int);
        lemma_sums_isum(cs.b, sel_pair(rs@, lss@, ss@, ra1 as int, la1 as int, thr2 as int), m, p, e1 as int, g as int, c0 as int,
            len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt, brf as int, bls as int);
        lemma_sums_isum(cs.c, sel_pair(rs@, lss@, ss@, ra2 as int, la2 as int, thr2 as int), m, p, e2 as int, g as int, c0 as int,
            len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt, brf as int, bls as int);
        lemma_sums_isum(cs.d, sel_pair(rs@, lss@, ss@, ra3 as int, la3 as int, thr2 as int), m, p, e3x as int, g as int, c0 as int,
            len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt, brf as int, bls as int);
        assert forall|i: int, w: int| 0 <= i < t && 0 <= w <= 5 implies #[trigger] tval(out_cnt@, out_sum@, i, w)
            == isum(m, p, i, w, rlo, c0 as int) + if none(i) { isum(m, p, i, w, c0 as int, c1) } else { 0 } by {}
    }
    add_entry(out_cnt, out_sum, e0, &cs.a, Ghost(m), Ghost(p), Ghost(rlo), Ghost(c0 as int), Ghost(c1), Ghost(t as int), Ghost(none));
    let ghost d1 = |k: int| none(k) || k == e0;
    add_entry(out_cnt, out_sum, e1, &cs.b, Ghost(m), Ghost(p), Ghost(rlo), Ghost(c0 as int), Ghost(c1), Ghost(t as int), Ghost(d1));
    let ghost d2 = |k: int| d1(k) || k == e1;
    add_entry(out_cnt, out_sum, e2, &cs.c, Ghost(m), Ghost(p), Ghost(rlo), Ghost(c0 as int), Ghost(c1), Ghost(t as int), Ghost(d2));
    let ghost d3 = |k: int| d2(k) || k == e2;
    if np == 4 {
        add_entry(out_cnt, out_sum, e3, &cs.d, Ghost(m), Ghost(p), Ghost(rlo), Ghost(c0 as int), Ghost(c1), Ghost(t as int), Ghost(d3));
    }
    proof {
        assert forall|k: int, w: int| 0 <= k < t && 0 <= w <= 5 implies #[trigger] tval(out_cnt@, out_sum@, k, w)
            == isum(m, p, k, w, rlo, c1) by {
            lemma_isum_split(m, p, k, w, rlo, c0 as int, c1);
            if !in_slots(k, np as int, e0 as int, e1 as int, e2 as int, e3 as int) {
                if in_box_spec(k, nls as int, brf as int, bls as int, r0 as int, r1 as int, l0 as int, l1 as int) {
                    assert(!holds(rs@, lss@, len as int, k / (nls as int) - brf, k % (nls as int) - bls));
                    lemma_entry_absent(m, p, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt,
                        brf as int, bls as int, k, k / (nls as int) - brf, k % (nls as int) - bls);
                } else {
                    lemma_entry_empty(m, p, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt,
                        brf as int, bls as int, k, r0 as int, r1 as int, l0 as int, l1 as int);
                }
            }
        }
    }
    true
}

/// One chunk (rows `c0 .. c1` of block `g`): every table entry gains the model sums of the chunk's rows.
fn do_chunk(out_cnt: &mut Vec<u64>, out_sum: &mut Vec<i128>, cols: &Cols, g: usize, c0: usize, c1: usize,
    full: bool, thr: i64, nls: usize, t: usize, mk: u64, has: bool,
    Ghost(m): Ghost<Model>, Ghost(p): Ghost<int>, Ghost(rlo): Ghost<int>)
    requires
        has ==> forall|j: int| c0 <= j < c1 ==> #[trigger] marked(mk, m.rf[j], m.ls[j]),
        model_wf(m), m.n <= u64::MAX, m == cols_model(*cols, m.n, m.bsize, m.nrf, m.nls),
        0 <= g < m.nb, g * m.bsize <= c0 < c1, c1 <= (g + 1) * m.bsize, c1 <= m.n, c1 - c0 <= CHUNK,
        0 <= rlo <= c0, rows_ok(m, rlo, c1 as int),
        nls == m.nls, t == m.nrf * m.nls, t <= MAXT,
        forall|j: int| c0 <= j < c1 ==> (#[trigger] shv(m, j) <= p) == (full || m.ship[j] <= thr),
        tbl_ok(old(out_cnt)@, old(out_sum)@, m, p, rlo, c0 as int, t as int),
    ensures
        tbl_ok(final(out_cnt)@, final(out_sum)@, m, p, rlo, c1 as int, t as int),
    no_unwind
{
    let len = c1 - c0;
    let qs = sub(cols.qty, c0, c1);
    let ps = sub(cols.price, c0, c1);
    let ds = sub(cols.disc, c0, c1);
    let ts = sub(cols.tax, c0, c1);
    let rs = sub(cols.rf, c0, c1);
    let lss = sub(cols.ls, c0, c1);
    let ss = sub(cols.ship, c0, c1);
    let bq = cols.qty_b[g];
    let bp = cols.price_b[g];
    let bd = cols.disc_b[g];
    let bt = cols.tax_b[g];
    let brf = cols.rf_b[g];
    let bls = cols.ls_b[g];
    let ghost (ci0, ci1) = (c0 as int, c1 as int);
    proof {
        assert(rows_ok(m, rlo, c1 as int));
        lemma_blk_of(m, g as int, c0 as int);
        assert(block_ok(m, blk(m, c0 as int)));
        assert(chunk_rows(m, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt,
            brf as int, bls as int));
    }
    proof {
        if has {
            assert forall|i: int| 0 <= i < len implies #[trigger] marked(mk, rs@[i], lss@[i]) by {
                assert(marked(mk, m.rf[c0 + i], m.ls[c0 + i]));
            }
        }
    }
    let (r0, r1, l0, l1, two) = chunk_box(rs, lss, len, full, mk, has);
    // the box's high corner is a table entry
    let corner_ok: bool = if brf < 64 && bls < 64 && nls <= MAXT {
        let a1 = brf as usize + r1 as usize;
        let b1 = bls as usize + l1 as usize;
        assert(a1 * nls <= 319 * 64) by (nonlinear_arith) requires a1 <= 319, nls <= 64;
        a1 * nls + b1 < t && b1 < nls
    } else {
        false
    };
    let ghost none = |i: int| false;
    proof {
        assert forall|i: int, w: int| 0 <= i < t && 0 <= w <= 5 implies #[trigger] tval(out_cnt@, out_sum@, i, w)
            == isum(m, p, i, w, rlo, c0 as int) + if none(i) { isum(m, p, i, w, c0 as int, c1 as int) } else { 0 } by {}
    }
    if r0 == r1 && l0 == l1 {
        // one pair: every row of the chunk lies in entry tt
        let ghost (a, b) = (brf + r0, bls + l0);
        proof {
            lemma_chunk_row(m, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt, brf as int, bls as int, 0);
            assert(a < m.nrf && b < m.nls);
            assert(a * nls + b < t) by (nonlinear_arith) requires 0 <= a < m.nrf, 0 <= b < nls, t == m.nrf * nls;
            assert(a * nls <= a * nls + b);
            assert(m.nrf <= t) by (nonlinear_arith) requires t == m.nrf * nls, nls >= 1, m.nrf >= 0;
            assert(brf < 64 && bls < 64);
        }
        let tt = (brf as usize + r0 as usize) * nls + (bls as usize + l0 as usize);
        proof {
            assert forall|j: int| c0 <= j < c1 implies #[trigger] gidx(m, j) == tt by {
                lemma_chunk_row(m, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt, brf as int, bls as int, j - c0);
            }
        }
        let cs = if full {
            let r = chunk_all2(qs, ps, ds, ts, len, bq, bp, bd, bt);
            proof {
                assert forall|i: int| 0 <= i < len implies #[trigger] sel_all()(i) == msel(m, p, tt as int, c0 + i) by {
                    assert(gidx(m, c0 + i) == tt);
                    assert(shv(m, c0 + i) <= p);
                }
                lemma_sums_isum(r, sel_all(), m, p, tt as int, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt, brf as int, bls as int);
            }
            r
        } else {
            let r = chunk_date(qs, ps, ds, ts, ss, len, bq, bp, bd, bt, thr);
            proof {
                assert forall|i: int| 0 <= i < len implies #[trigger] sel_date(ss@, thr as int)(i) == msel(m, p, tt as int, c0 + i) by {
                    assert(gidx(m, c0 + i) == tt);
                    assert(ss@[i] == m.ship[c0 + i]);
                    assert((shv(m, c0 + i) <= p) == (m.ship[c0 + i] <= thr));
                }
                lemma_sums_isum(r, sel_date(ss@, thr as int), m, p, tt as int, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt, brf as int, bls as int);
            }
            r
        };
        add_entry(out_cnt, out_sum, tt, &cs, Ghost(m), Ghost(p), Ghost(rlo), Ghost(c0 as int), Ghost(c1 as int), Ghost(t as int), Ghost(none));
        proof {
            assert forall|k: int, w: int| 0 <= k < t && 0 <= w <= 5 implies #[trigger] tval(out_cnt@, out_sum@, k, w)
                == isum(m, p, k, w, rlo, c1 as int) by {
                lemma_isum_split(m, p, k, w, rlo, c0 as int, c1 as int);
                if k != tt {
                    lemma_untouched(m, p, k, c0 as int, c1 as int);
                }
            }
        }
    } else if full && two && (r0 < r1 || l0 < l1) && corner_ok {
        // two pairs in a full block, told apart by rf (one ls) or by ls (one rf): every code is the box's low or
        // high code
        let by_rf = r0 < r1;
        let xs = if by_rf { rs } else { lss };
        let x1 = if by_rf { r0 } else { l0 };
        let ghost (a0, a1, b0, b1) = (brf + r0, brf + r1, bls + l0, bls + l1);
        proof {
            // the box's corners are table entries: the high corner by the run-time test, the low one below it
            assert(a1 * nls + b1 < t);
            assert(0 <= a0 <= a1 && 0 <= b0 <= b1 < nls);
            assert(a0 * nls <= a1 * nls) by (nonlinear_arith) requires 0 <= a0 <= a1, nls >= 0;
            assert(a0 * nls + b0 < t);
            assert(a0 * nls <= a0 * nls + b0 && a1 * nls <= a1 * nls + b1);
            lemma_index_unique(a0, b0, a1, b1, nls as int);
        }
        let tt1 = (brf as usize + r0 as usize) * nls + (bls as usize + l0 as usize);
        let tt2 = (brf as usize + r1 as usize) * nls + (bls as usize + l1 as usize);
        assert(tt1 != tt2);
        let cs = chunk_split2(qs, ps, ds, ts, xs, len, bq, bp, bd, bt, x1);
        proof {
            assert forall|i: int| 0 <= i < len implies #[trigger] sel_eq(xs@, x1 as int)(i) == msel(m, p, tt1 as int, c0 + i) by {
                lemma_chunk_row(m, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt, brf as int, bls as int, i);
                assert(shv(m, c0 + i) <= p);
                lemma_index_unique(brf + rs@[i], bls + lss@[i], brf + r0, bls + l0, nls as int);
            }
            assert forall|i: int| 0 <= i < len implies #[trigger] sel_ne(xs@, x1 as int)(i) == msel(m, p, tt2 as int, c0 + i) by {
                lemma_chunk_row(m, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt, brf as int, bls as int, i);
                assert(shv(m, c0 + i) <= p);
                lemma_index_unique(brf + rs@[i], bls + lss@[i], brf + r1, bls + l1, nls as int);
            }
            lemma_sums_isum(cs.a, sel_eq(xs@, x1 as int), m, p, tt1 as int, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt, brf as int, bls as int);
            lemma_sums_isum(cs.b, sel_ne(xs@, x1 as int), m, p, tt2 as int, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt, brf as int, bls as int);
        }
        add_entry(out_cnt, out_sum, tt1, &cs.a, Ghost(m), Ghost(p), Ghost(rlo), Ghost(c0 as int), Ghost(c1 as int), Ghost(t as int), Ghost(none));
        let ghost d1 = |i: int| none(i) || i == tt1;
        add_entry(out_cnt, out_sum, tt2, &cs.b, Ghost(m), Ghost(p), Ghost(rlo), Ghost(c0 as int), Ghost(c1 as int), Ghost(t as int), Ghost(d1));
        proof {
            assert forall|k: int, w: int| 0 <= k < t && 0 <= w <= 5 implies #[trigger] tval(out_cnt@, out_sum@, k, w)
                == isum(m, p, k, w, rlo, c1 as int) by {
                lemma_isum_split(m, p, k, w, rlo, c0 as int, c1 as int);
                if k != tt1 && k != tt2 {
                    assert forall|j: int| c0 <= j < c1 implies #[trigger] gidx(m, j) != k by {
                        let i = j - c0;
                        lemma_chunk_row(m, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt, brf as int, bls as int, i);
                        lemma_index_unique(brf + rs@[i], bls + lss@[i], brf + r0, bls + l0, nls as int);
                        lemma_index_unique(brf + rs@[i], bls + lss@[i], brf + r1, bls + l1, nls as int);
                    }
                    lemma_untouched(m, p, k, c0 as int, c1 as int);
                }
            }
        }
    } else {
        let thr2: i64 = if full { 0x10000 } else { thr };
        proof {
            if full {
                assert forall|j: int| c0 <= j < c0 + len implies #[trigger] shv(m, j) <= p by {}
            }
        }
        let multi = if full {
            try_multi(out_cnt, out_sum, qs, ps, ds, ts, rs, lss, ss, g, c0, len, bq, bp, bd, bt, brf, bls,
                r0, r1, l0, l1, nls, t, Ghost(m), Ghost(p), Ghost(rlo))
        } else {
            false
        };
        if multi {
            // three or four entries added in one pass
        } else {
            // the table entries inside the chunk's code box that some row holds, two per masked pass
            let mut pend: usize = t;
            let mut i: usize = 0;
            while i < t
                invariant
                    chunk_rows(m, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt, brf as int, bls as int),
                    model_wf(m), m.n <= u64::MAX, 0 <= rlo <= c0, c1 <= m.n, rows_ok(m, rlo, c1 as int),
                    len == c1 - c0, len <= CHUNK, nls == m.nls, t == m.nrf * m.nls, t <= MAXT, i <= t,
                    qs@.len() == len, ps@.len() == len, ds@.len() == len, ts@.len() == len, rs@.len() == len,
                    lss@.len() == len, ss@.len() == len, bases_ok(bq, bp, bd, bt),
                    forall|ii: int| 0 <= ii < len ==> r0 <= #[trigger] rs@[ii] <= r1,
                    forall|ii: int| 0 <= ii < len ==> l0 <= #[trigger] lss@[ii] <= l1,
                    forall|ii: int| 0 <= ii < len ==> (#[trigger] shv(m, c0 + ii) <= p) == (ss@[ii] <= thr2),
                    pend == t || (pend < i && in_box_spec(pend as int, nls as int, brf as int, bls as int, r0 as int, r1 as int, l0 as int, l1 as int)),
                    tbl_part(out_cnt@, out_sum@, m, p, rlo, c0 as int, c1 as int, t as int, |k: int| k < i && k != pend),
                decreases t - i,
            {
                let ghost pend0 = pend;
                if in_box(i, nls, brf, bls, r0, r1, l0, l1) {
                    let (ra, la) = box_codes(i, nls, brf, bls);
                    if has_pair(rs, lss, len, ra, la) {
                        if pend < t {
                            let (rb, lb) = box_codes(pend, nls, brf, bls);
                            let cs = chunk_two(qs, ps, ds, ts, rs, lss, ss, len, bq, bp, bd, bt, rb, lb, ra, la, thr2);
                            proof {
                                lemma_entry_sel(m, p, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt,
                                    brf as int, bls as int, pend as int, rb as int, lb as int, thr2 as int);
                                lemma_entry_sel(m, p, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt,
                                    brf as int, bls as int, i as int, ra as int, la as int, thr2 as int);
                                lemma_sums_isum(cs.a, sel_pair(rs@, lss@, ss@, rb as int, lb as int, thr2 as int), m, p, pend as int, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt, brf as int, bls as int);
                                lemma_sums_isum(cs.b, sel_pair(rs@, lss@, ss@, ra as int, la as int, thr2 as int), m, p, i as int, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt, brf as int, bls as int);
                            }
                            let ghost dk = |k: int| k < i && k != pend0;
                            add_entry(out_cnt, out_sum, pend, &cs.a, Ghost(m), Ghost(p), Ghost(rlo), Ghost(c0 as int), Ghost(c1 as int), Ghost(t as int), Ghost(dk));
                            let ghost dk1 = |k: int| dk(k) || k == pend0;
                            add_entry(out_cnt, out_sum, i, &cs.b, Ghost(m), Ghost(p), Ghost(rlo), Ghost(c0 as int), Ghost(c1 as int), Ghost(t as int), Ghost(dk1));
                            pend = t;
                        } else {
                            pend = i;
                        }
                    } else {
                        proof {
                            lemma_entry_absent(m, p, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt,
                                brf as int, bls as int, i as int, ra as int, la as int);
                        }
                    }
                } else {
                    proof {
                        lemma_entry_empty(m, p, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt,
                            brf as int, bls as int, i as int, r0 as int, r1 as int, l0 as int, l1 as int);
                    }
                }
                proof {
                    assert forall|k: int, w: int| 0 <= k < t && 0 <= w <= 5 implies #[trigger] tval(out_cnt@, out_sum@, k, w)
                        == isum(m, p, k, w, rlo, c0 as int) + if k < i + 1 && k != pend { isum(m, p, k, w, c0 as int, c1 as int) } else { 0 } by {
                        if k == i && k != pend {
                            // `i` was added now, or holds no row of the chunk
                        }
                    }
                }
                i = i + 1;
            }
            if pend < t {
                let (rb, lb) = box_codes(pend, nls, brf, bls);
                let cs = chunk_pair(qs, ps, ds, ts, rs, lss, ss, len, bq, bp, bd, bt, rb, lb, thr2);
                proof {
                    lemma_entry_sel(m, p, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt,
                        brf as int, bls as int, pend as int, rb as int, lb as int, thr2 as int);
                    lemma_sums_isum(cs, sel_pair(rs@, lss@, ss@, rb as int, lb as int, thr2 as int), m, p, pend as int, g as int, c0 as int, len as int, qs@, ps@, ds@, ts@, rs@, lss@, ss@, bq, bp, bd, bt, brf as int, bls as int);
                }
                let ghost dk = |k: int| k < t && k != pend;
                add_entry(out_cnt, out_sum, pend, &cs, Ghost(m), Ghost(p), Ghost(rlo), Ghost(c0 as int), Ghost(c1 as int), Ghost(t as int), Ghost(dk));
            }
            proof {
                assert forall|k: int, w: int| 0 <= k < t && 0 <= w <= 5 implies #[trigger] tval(out_cnt@, out_sum@, k, w)
                    == isum(m, p, k, w, rlo, c1 as int) by {
                    lemma_isum_split(m, p, k, w, rlo, c0 as int, c1 as int);
                }
            }
        }
    }
}


// ------------------------------------------------------------------------------------------------ the worker task

/// Block `g` (rows `lo .. hi`) added into a table of no rows (`lo .. lo`): the block's table. Blocks whose shipdate
/// base exceeds the bound hold no qualifying row and are skipped; otherwise chunk by chunk, with the shipdate test
/// left out when the block's zone maximum is within the bound.
fn scan_block(out_cnt: &mut Vec<u64>, out_sum: &mut Vec<i128>, cols: &Cols, g: usize, lo: usize, hi: usize, p: i64,
    nls: usize, t: usize, Ghost(m): Ghost<Model>)
    requires
        model_wf(m), m.n <= u64::MAX, m == cols_model(*cols, m.n, m.bsize, m.nrf, m.nls), masks_hold(*cols),
        0 <= g < m.nb, lo == g * m.bsize, lo <= hi, hi <= m.n, hi <= lo + m.bsize,
        nls == m.nls, t == m.nrf * m.nls, t <= MAXT, block_ok(m, g as int), -0x8000_0000 <= p <= 0x7fff_ffff,
        forall|j: int| lo <= j < hi ==> #[trigger] block_ok(m, blk(m, j)),
        forall|j: int| lo <= j < hi ==> #[trigger] blk(m, j) == g,
        tbl_ok(old(out_cnt)@, old(out_sum)@, m, p as int, lo as int, lo as int, t as int),
    ensures
        tbl_ok(final(out_cnt)@, final(out_sum)@, m, p as int, lo as int, hi as int, t as int),
    no_unwind
{
    let sb = cols.ship_b[g];
    if sb > p {
        // no row of the block passes the date bound: its shipdates are at least the base
        proof {
            assert forall|i: int, w: int| 0 <= i < t && 0 <= w <= 5 implies #[trigger] tval(out_cnt@, out_sum@, i, w)
                == isum(m, p as int, i, w, lo as int, hi as int) by {
                assert forall|j: int| lo <= j < hi implies !#[trigger] msel(m, p as int, i, j) by {
                    assert(blk(m, j) == g);
                }
                lemma_isum_none(m, p as int, i, w, lo as int, hi as int);
                lemma_isum_split(m, p as int, i, w, lo as int, lo as int, hi as int);
            }
        }
    } else {
        let full = cols.ship_z[g] <= p;
        let thr = p - sb;
        let mut c0 = lo;
        while c0 < hi
            invariant
                model_wf(m), m.n <= u64::MAX, m == cols_model(*cols, m.n, m.bsize, m.nrf, m.nls), masks_hold(*cols),
                0 <= g < m.nb, lo == g * m.bsize, lo <= c0 <= hi, hi <= m.n, hi <= lo + m.bsize,
                nls == m.nls, t == m.nrf * m.nls, t <= MAXT, block_ok(m, g as int),
                forall|j: int| lo <= j < hi ==> #[trigger] block_ok(m, blk(m, j)),
                forall|j: int| lo <= j < hi ==> #[trigger] blk(m, j) == g,
                sb == m.ship_b[g as int], thr == p - sb, full == (m.ship_z[g as int] <= p),
                tbl_ok(out_cnt@, out_sum@, m, p as int, lo as int, c0 as int, t as int),
            decreases hi - c0,
        {
            let c1 = if CHUNK < hi - c0 { c0 + CHUNK } else { hi };
            // the chunk's pair mask, when the chunk is one mask's rows
            let ci = c0 / CHUNK;
            let has = c0 % CHUNK == 0 && ci < cols.nmk;
            let mk: u64 = if has { cols.mk[ci] } else { 0 };
            proof {
                if has {
                    lemma_mask_rows(*cols, m, c0 as int, c1 as int, ci as int);
                }
            }
            proof {
                assert(c1 <= (g + 1) * m.bsize) by (nonlinear_arith) requires c1 <= hi, hi <= lo + m.bsize, lo == g * m.bsize;
                assert forall|j: int| c0 <= j < c1 implies (#[trigger] shv(m, j) <= p) == (full || m.ship[j] <= thr) by {
                    assert(blk(m, j) == g);
                }
                assert forall|j: int| lo <= j < c1 implies #[trigger] block_ok(m, blk(m, j)) by {}
            }
            do_chunk(out_cnt, out_sum, cols, g, c0, c1, full, thr, nls, t, mk, has, Ghost(m), Ghost(p as int), Ghost(lo as int));
            c0 = c1;
        }
    }
}

/// A zeroed table of `t` entries (worker side).
fn zero_table(cnt: &mut Vec<u64>, sum: &mut Vec<i128>, t: usize)
    requires old(cnt)@.len() == t, old(sum)@.len() == 5 * t, t <= MAXT,
    ensures
        final(cnt)@.len() == t, final(sum)@.len() == 5 * t,
        forall|i: int| 0 <= i < t ==> #[trigger] final(cnt)@[i] == 0,
        forall|i: int| 0 <= i < 5 * t ==> #[trigger] final(sum)@[i] == 0,
    no_unwind
{
    let mut i: usize = 0;
    while i < t
        invariant
            cnt@.len() == t, sum@.len() == 5 * t, t <= MAXT, i <= t,
            forall|i2: int| 0 <= i2 < i ==> #[trigger] cnt@[i2] == 0,
        decreases t - i,
    {
        cnt[i] = 0;
        i = i + 1;
    }
    let mut j: usize = 0;
    while j < 5 * t
        invariant
            cnt@.len() == t, sum@.len() == 5 * t, t <= MAXT, j <= 5 * t,
            forall|i2: int| 0 <= i2 < t ==> #[trigger] cnt@[i2] == 0,
            forall|i2: int| 0 <= i2 < j ==> #[trigger] sum@[i2] == 0,
        decreases 5 * t - j,
    {
        sum[j] = 0;
        j = j + 1;
    }
}

/// Table `b` added into table `a`, entry by entry (worker side).
fn add_into(a_cnt: &mut Vec<u64>, a_sum: &mut Vec<i128>, b_cnt: &Vec<u64>, b_sum: &Vec<i128>, t: usize)
    requires
        old(a_cnt)@.len() == t, old(a_sum)@.len() == 5 * t, b_cnt@.len() == t, b_sum@.len() == 5 * t, t <= MAXT,
        forall|i: int, w: int| 0 <= i < t && 0 <= w < 5 ==> -0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff
            <= #[trigger] tval(old(a_cnt)@, old(a_sum)@, i, w) + tval(b_cnt@, b_sum@, i, w) <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff,
        forall|i: int| 0 <= i < t ==> #[trigger] old(a_cnt)@[i] + b_cnt@[i] <= u64::MAX,
    ensures
        final(a_cnt)@.len() == t, final(a_sum)@.len() == 5 * t,
        forall|i: int, w: int| 0 <= i < t && 0 <= w <= 5 ==> #[trigger] tval(final(a_cnt)@, final(a_sum)@, i, w)
            == tval(old(a_cnt)@, old(a_sum)@, i, w) + tval(b_cnt@, b_sum@, i, w),
    no_unwind
{
    let mut i: usize = 0;
    while i < t
        invariant
            a_cnt@.len() == t, a_sum@.len() == 5 * t, b_cnt@.len() == t, b_sum@.len() == 5 * t, t <= MAXT, i <= t,
            forall|i2: int, w: int| 0 <= i2 < t && 0 <= w < 5 ==> -0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff
                <= #[trigger] tval(old(a_cnt)@, old(a_sum)@, i2, w) + tval(b_cnt@, b_sum@, i2, w) <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff,
            forall|i2: int| 0 <= i2 < t ==> #[trigger] old(a_cnt)@[i2] + b_cnt@[i2] <= u64::MAX,
            forall|i2: int, w: int| 0 <= i2 < t && 0 <= w <= 5 ==> #[trigger] tval(a_cnt@, a_sum@, i2, w)
                == tval(old(a_cnt)@, old(a_sum)@, i2, w) + if i2 < i { tval(b_cnt@, b_sum@, i2, w) } else { 0 },
        decreases t - i,
    {
        let ghost (oc, os) = (a_cnt@, a_sum@);
        let b = i * NSUMS;
        proof {
            assert(i * 5 + 4 < 5 * t) by (nonlinear_arith) requires i < t;
            assert(tval(oc, os, i as int, 5) == tval(old(a_cnt)@, old(a_sum)@, i as int, 5));
            assert forall|w: int| 0 <= w < 5 implies -0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff
                <= #[trigger] (os[b + w] + b_sum@[b + w]) <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff by {
                assert(tval(oc, os, i as int, w) == tval(old(a_cnt)@, old(a_sum)@, i as int, w));
                assert(tval(b_cnt@, b_sum@, i as int, w) == b_sum@[b + w]);
            }
            assert(-0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff <= os[b + 0] + b_sum@[b + 0] <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff);
            assert(-0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff <= os[b + 1] + b_sum@[b + 1] <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff);
            assert(-0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff <= os[b + 2] + b_sum@[b + 2] <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff);
            assert(-0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff <= os[b + 3] + b_sum@[b + 3] <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff);
            assert(-0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff <= os[b + 4] + b_sum@[b + 4] <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff);
            assert(b + 0 == b);
            assert(oc[i as int] == old(a_cnt)@[i as int]);
        }
        a_cnt[i] = a_cnt[i] + b_cnt[i];
        a_sum[b] = a_sum[b] + b_sum[b];
        a_sum[b + 1] = a_sum[b + 1] + b_sum[b + 1];
        a_sum[b + 2] = a_sum[b + 2] + b_sum[b + 2];
        a_sum[b + 3] = a_sum[b + 3] + b_sum[b + 3];
        a_sum[b + 4] = a_sum[b + 4] + b_sum[b + 4];
        proof {
            assert forall|i2: int, w: int| 0 <= i2 < t && 0 <= w <= 5 implies #[trigger] tval(a_cnt@, a_sum@, i2, w)
                == tval(old(a_cnt)@, old(a_sum)@, i2, w) + if i2 < i + 1 { tval(b_cnt@, b_sum@, i2, w) } else { 0 } by {
                assert(tval(oc, os, i2, w) == tval(old(a_cnt)@, old(a_sum)@, i2, w) + if i2 < i { tval(b_cnt@, b_sum@, i2, w) } else { 0 });
                if w < 5 && i2 != i {
                    assert(i2 * 5 + w != b && i2 * 5 + w != b + 1 && i2 * 5 + w != b + 2 && i2 * 5 + w != b + 3 && i2 * 5 + w != b + 4)
                        by (nonlinear_arith) requires i2 != i, 0 <= w < 5, b == i * 5;
                }
            }
        }
        i = i + 1;
    }
}

/// One worker: task `k` of `s` sums blocks `k + r * s` over rounds `r < q` (blocks at or past `ng` are empty), each
/// block into the scratch table `blk_*`, then added into its own table `out_*` (zeroed on entry).
pub struct FastTask {
    pub cols: Cols,
    pub n: usize,
    pub bsize: usize,
    pub nrf: usize,
    pub nls: usize,
    pub t: usize,
    pub k: usize,
    pub s: usize,
    pub q: usize,
    pub ng: usize,
    pub p: i64,
    pub out_cnt: Vec<u64>,
    pub out_sum: Vec<i128>,
    pub blk_cnt: Vec<u64>,
    pub blk_sum: Vec<i128>,
}

pub struct FastOut {
    pub cnt: Vec<u64>,
    pub sum: Vec<i128>,
}

/// The first stored row of block `g` (clipped to `n`).
pub open spec fn block_start(m: Model, g: int) -> int {
    if g * m.bsize < m.n { g * m.bsize } else { m.n }
}

/// The task's input facts: the model of its slices, its rounds, the fast path's bounds on every block, a zeroed
/// table, a scratch table of the same shape and the date bound in the date range.
pub open spec fn task_pre(c: Cols, n: int, bsize: int, nrf: int, nls: int, t: int, k: int, s: int, q: int, ng: int,
    p: int, cnt: Seq<u64>, sum: Seq<i128>, bcnt: Seq<u64>, bsum: Seq<i128>) -> bool
{
    let m = cols_model(c, n, bsize, nrf, nls);
    &&& model_wf(m) && n <= u64::MAX && m.nb * bsize < n + bsize && n + bsize <= usize::MAX
    &&& ng == m.nb && m.nb * 64 <= usize::MAX
    &&& 0 <= k < s <= 64 && 0 <= q <= m.nb && q * s <= m.nb + s
    &&& forall|g: int| 0 <= g < m.nb ==> #[trigger] block_ok(m, g)
    &&& t == nrf * nls && t <= MAXT
    &&& cnt.len() == t && sum.len() == 5 * t && bcnt.len() == t && bsum.len() == 5 * t
    &&& forall|i: int| 0 <= i < t ==> #[trigger] cnt[i] == 0
    &&& forall|i: int| 0 <= i < 5 * t ==> #[trigger] sum[i] == 0
    &&& -0x8000_0000 <= p <= 0x7fff_ffff
    &&& masks_hold(c)
}

/// The rows `c0 .. c1` of chunk `ci` (`c0 == ci * CHUNK`, at most `CHUNK` rows) are marked in its mask.
proof fn lemma_mask_rows(c: Cols, m: Model, c0: int, c1: int, ci: int)
    requires
        masks_hold(c), m.rf == c.rf@, m.ls == c.ls@, m.rf.len() == m.n, 0 <= c0 < c1 <= m.n, c1 - c0 <= CHUNK,
        ci == c0 / (CHUNK as int), c0 % (CHUNK as int) == 0, ci < c.nmk,
    ensures forall|j: int| c0 <= j < c1 ==> #[trigger] marked(c.mk@[ci], m.rf[j], m.ls[j]),
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(c0, CHUNK as int);
    assert forall|j: int| c0 <= j < c1 implies #[trigger] marked(c.mk@[ci], m.rf[j], m.ls[j]) by {
        assert(LP::row_marked(c.rf@, c.ls@, c.mk@, j));
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(j, CHUNK as int, ci, j - ci * (CHUNK as int));
    }
}

/// One block's step of a task's prefix sum: `r + 1` rounds are `r` rounds and block `k + r * s`; every prefix of
/// at most `q` rounds is within `q` blocks (`|value| <= 2^114`, count `<= q * bsize <= u64::MAX`).
proof fn lemma_prefix_facts(m: Model, p: int, i: int, k: int, s: int, r: int, q: int)
    requires
        model_wf(m), 0 <= k < s <= 64, 0 <= r <= q <= m.nb, m.nb * m.bsize < m.n + m.bsize,
        m.n + m.bsize <= usize::MAX,
        forall|j: int| 0 <= j < m.n ==> #[trigger] block_ok(m, blk(m, j)),
    ensures
        forall|w: int| 0 <= w < 5 ==> -0x4_0000_0000_0000_0000_0000_0000_0000 <= #[trigger] ssum(m, p, i, w, k, s, r)
            <= 0x4_0000_0000_0000_0000_0000_0000_0000,
        0 <= ssum(m, p, i, 5, k, s, r) <= u64::MAX,
        forall|w: int| 0 <= w <= 5 ==> #[trigger] ssum(m, p, i, w, k, s, r + 1) == ssum(m, p, i, w, k, s, r) + bsum(m, p, i, w, k + r * s),
{
    assert(r * m.bsize <= m.nb * m.bsize) by (nonlinear_arith) requires r <= m.nb, m.bsize >= 1;
    assert(0 <= r * m.bsize) by (nonlinear_arith) requires 0 <= r, m.bsize >= 1;
    assert forall|w: int| 0 <= w <= 5 implies #[trigger] ssum(m, p, i, w, k, s, r + 1) == ssum(m, p, i, w, k, s, r) + bsum(m, p, i, w, k + r * s) by {
        assert((r + 1 - 1) * s == r * s);
    }
    assert forall|w: int| 0 <= w < 5 implies -0x4_0000_0000_0000_0000_0000_0000_0000 <= #[trigger] ssum(m, p, i, w, k, s, r)
        <= 0x4_0000_0000_0000_0000_0000_0000_0000 by {
        lemma_ssum_bound(m, p, i, w, k, s, r);
        assert(vbound(w) <= 0x4_0000_0000_0000);
        assert(r * m.bsize * vbound(w) <= 0x1_0000_0000_0000_0000 * 0x4_0000_0000_0000) by (nonlinear_arith)
            requires 0 <= r * m.bsize <= 0x1_0000_0000_0000_0000, 0 <= vbound(w) <= 0x4_0000_0000_0000;
    }
    lemma_ssum_bound(m, p, i, 5, k, s, r);
}

/// The first pass of a rotated task (rounds `r0 .. q`): after round `r` the table holds `ssum(r + 1) - ssum(r0)`,
/// within `i128` and, for the count, within `u64`.
proof fn lemma_rot_first(m: Model, p: int, i: int, k: int, s: int, r0: int, r: int, q: int)
    requires
        model_wf(m), 0 <= k < s <= 64, 0 <= r0 <= r < q <= m.nb, m.nb * m.bsize < m.n + m.bsize,
        m.n + m.bsize <= usize::MAX,
        forall|j: int| 0 <= j < m.n ==> #[trigger] block_ok(m, blk(m, j)),
    ensures
        forall|w: int| 0 <= w < 5 ==> -0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff
            <= #[trigger] ((ssum(m, p, i, w, k, s, r) - ssum(m, p, i, w, k, s, r0)) + bsum(m, p, i, w, k + r * s))
            <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff,
        0 <= (ssum(m, p, i, 5, k, s, r) - ssum(m, p, i, 5, k, s, r0)) + bsum(m, p, i, 5, k + r * s) <= u64::MAX,
        forall|w: int| 0 <= w <= 5 ==> #[trigger] ssum(m, p, i, w, k, s, r + 1) == ssum(m, p, i, w, k, s, r) + bsum(m, p, i, w, k + r * s),
{
    lemma_prefix_facts(m, p, i, k, s, r, q);
    lemma_prefix_facts(m, p, i, k, s, r + 1, q);
    lemma_prefix_facts(m, p, i, k, s, r0, q);
    lemma_ssum_count_mono(m, p, i, k, s, r0, r + 1);
    assert forall|w: int| 0 <= w < 5 implies -0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff
        <= #[trigger] ((ssum(m, p, i, w, k, s, r) - ssum(m, p, i, w, k, s, r0)) + bsum(m, p, i, w, k + r * s))
        <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff by {
        assert(ssum(m, p, i, w, k, s, r + 1) == ssum(m, p, i, w, k, s, r) + bsum(m, p, i, w, k + r * s));
        assert(-0x4_0000_0000_0000_0000_0000_0000_0000 <= ssum(m, p, i, w, k, s, r + 1) <= 0x4_0000_0000_0000_0000_0000_0000_0000);
        assert(-0x4_0000_0000_0000_0000_0000_0000_0000 <= ssum(m, p, i, w, k, s, r0) <= 0x4_0000_0000_0000_0000_0000_0000_0000);
    }
}

/// The second pass of a rotated task (rounds `0 .. r0`, after `r0 .. q`): after round `r` the table holds
/// `ssum(q) - ssum(r0) + ssum(r + 1)`, within `i128` and, for the count, within `u64`.
proof fn lemma_rot_second(m: Model, p: int, i: int, k: int, s: int, r0: int, r: int, q: int)
    requires
        model_wf(m), 0 <= k < s <= 64, 0 <= r < r0 <= q <= m.nb, m.nb * m.bsize < m.n + m.bsize,
        m.n + m.bsize <= usize::MAX,
        forall|j: int| 0 <= j < m.n ==> #[trigger] block_ok(m, blk(m, j)),
    ensures
        forall|w: int| 0 <= w < 5 ==> -0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff
            <= #[trigger] ((ssum(m, p, i, w, k, s, q) - ssum(m, p, i, w, k, s, r0) + ssum(m, p, i, w, k, s, r))
                + bsum(m, p, i, w, k + r * s))
            <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff,
        0 <= (ssum(m, p, i, 5, k, s, q) - ssum(m, p, i, 5, k, s, r0) + ssum(m, p, i, 5, k, s, r)) + bsum(m, p, i, 5, k + r * s)
            <= u64::MAX,
        forall|w: int| 0 <= w <= 5 ==> #[trigger] ssum(m, p, i, w, k, s, r + 1) == ssum(m, p, i, w, k, s, r) + bsum(m, p, i, w, k + r * s),
{
    lemma_prefix_facts(m, p, i, k, s, r, q);
    lemma_prefix_facts(m, p, i, k, s, r + 1, q);
    lemma_prefix_facts(m, p, i, k, s, r0, q);
    lemma_prefix_facts(m, p, i, k, s, q, q);
    // counts: ssum(r + 1) <= ssum(r0) <= ssum(q)
    lemma_ssum_count_mono(m, p, i, k, s, r + 1, r0);
    lemma_ssum_count_mono(m, p, i, k, s, r0, q);
    assert forall|w: int| 0 <= w < 5 implies -0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff
        <= #[trigger] ((ssum(m, p, i, w, k, s, q) - ssum(m, p, i, w, k, s, r0) + ssum(m, p, i, w, k, s, r))
            + bsum(m, p, i, w, k + r * s))
        <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff by {
        assert(ssum(m, p, i, w, k, s, r + 1) == ssum(m, p, i, w, k, s, r) + bsum(m, p, i, w, k + r * s));
        assert(-0x4_0000_0000_0000_0000_0000_0000_0000 <= ssum(m, p, i, w, k, s, r + 1) <= 0x4_0000_0000_0000_0000_0000_0000_0000);
        assert(-0x4_0000_0000_0000_0000_0000_0000_0000 <= ssum(m, p, i, w, k, s, r0) <= 0x4_0000_0000_0000_0000_0000_0000_0000);
        assert(-0x4_0000_0000_0000_0000_0000_0000_0000 <= ssum(m, p, i, w, k, s, q) <= 0x4_0000_0000_0000_0000_0000_0000_0000);
    }
}

/// The facts a task's rounds need, as `run` receives them.
pub open spec fn rounds_pre(c: Cols, n: int, bsize: int, nrf: int, nls: int, t: int, k: int, s: int, q: int, ng: int,
    p: int) -> bool
{
    let m = cols_model(c, n, bsize, nrf, nls);
    &&& model_wf(m) && n <= u64::MAX && m.nb * bsize < n + bsize && n + bsize <= usize::MAX
    &&& ng == m.nb && m.nb * 64 <= usize::MAX
    &&& 0 <= k < s <= 64 && 0 <= q <= m.nb && q * s <= m.nb + s
    &&& forall|g: int| 0 <= g < m.nb ==> #[trigger] block_ok(m, g)
    &&& forall|j: int| 0 <= j < m.n ==> #[trigger] block_ok(m, blk(m, j))
    &&& t == nrf * nls && t <= MAXT
    &&& -0x8000_0000 <= p <= 0x7fff_ffff
    &&& masks_hold(c)
}

/// Round `r` of task `k` (block `k + r * s`, empty at or past `ng`) added into the task's table `acc_*`, through
/// the scratch table `bc`, `bsm`.
fn add_round(acc_cnt: &mut Vec<u64>, acc_sum: &mut Vec<i128>, bc: &mut Vec<u64>, bsm: &mut Vec<i128>, cols: &Cols,
    n: usize, bsize: usize, nrf: usize, nls: usize, t: usize, k: usize, s: usize, q: usize, ng: usize, p: i64, r: usize,
    Ghost(m): Ghost<Model>)
    requires
        rounds_pre(*cols, n as int, bsize as int, nrf as int, nls as int, t as int, k as int, s as int, q as int,
            ng as int, p as int),
        m == cols_model(*cols, n as int, bsize as int, nrf as int, nls as int),
        r < q,
        old(acc_cnt)@.len() == t, old(acc_sum)@.len() == 5 * t, old(bc)@.len() == t, old(bsm)@.len() == 5 * t,
        forall|i: int, w: int| 0 <= i < t && 0 <= w < 5 ==> -0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff
            <= #[trigger] tval(old(acc_cnt)@, old(acc_sum)@, i, w) + bsum(m, p as int, i, w, k + r * s)
            <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff,
        forall|i: int| 0 <= i < t ==> 0 <= #[trigger] tval(old(acc_cnt)@, old(acc_sum)@, i, 5)
            + bsum(m, p as int, i, 5, k + r * s) <= u64::MAX,
    ensures
        final(acc_cnt)@.len() == t, final(acc_sum)@.len() == 5 * t, final(bc)@.len() == t, final(bsm)@.len() == 5 * t,
        forall|i: int, w: int| 0 <= i < t && 0 <= w <= 5 ==> #[trigger] tval(final(acc_cnt)@, final(acc_sum)@, i, w)
            == tval(old(acc_cnt)@, old(acc_sum)@, i, w) + bsum(m, p as int, i, w, k + r * s),
    no_unwind
{
    proof {
        assert(r * s <= q * s) by (nonlinear_arith) requires r <= q, s >= 0;
        assert(r * s >= 0) by (nonlinear_arith) requires r >= 0, s >= 0;
    }
    let g = k + r * s;
    if g < ng {
        proof {
            assert(g * bsize < m.nb * bsize) by (nonlinear_arith) requires g < m.nb, bsize >= 1;
            assert(g * bsize + bsize <= m.nb * bsize) by (nonlinear_arith) requires g < m.nb, bsize >= 1;
            assert(g * bsize >= 0) by (nonlinear_arith) requires g >= 0, bsize >= 1;
        }
        let lo = g * bsize;
        let hi = if bsize < n - lo { lo + bsize } else { n };
        proof {
            assert(lo == block_start(m, g as int));
            assert(hi == block_start(m, g as int + 1)) by {
                assert((g + 1) * bsize == lo + bsize) by (nonlinear_arith) requires lo == g * bsize;
            }
            assert forall|j: int| lo <= j < hi implies #[trigger] blk(m, j) == g by {
                assert(hi <= (g + 1) * bsize) by (nonlinear_arith) requires hi <= lo + bsize, lo == g * bsize;
                lemma_blk_of(m, g as int, j);
            }
        }
        zero_table(bc, bsm, t);
        proof {
            assert forall|i: int, w: int| 0 <= i < t && 0 <= w <= 5 implies #[trigger] tval(bc@, bsm@, i, w)
                == isum(m, p as int, i, w, lo as int, lo as int) by {
                if w < 5 {
                    assert(0 <= i * 5 + w < 5 * t) by (nonlinear_arith) requires 0 <= i < t, 0 <= w < 5;
                }
            }
        }
        scan_block(bc, bsm, cols, g, lo, hi, p, nls, t, Ghost(m));
        proof {
            assert forall|i: int, w: int| 0 <= i < t && 0 <= w <= 5 implies #[trigger] tval(bc@, bsm@, i, w)
                == bsum(m, p as int, i, w, g as int) by {}
            assert forall|i: int, w: int| 0 <= i < t && 0 <= w < 5 implies -0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff
                <= #[trigger] tval(acc_cnt@, acc_sum@, i, w) + tval(bc@, bsm@, i, w) <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff by {
                assert(tval(bc@, bsm@, i, w) == bsum(m, p as int, i, w, g as int));
            }
            assert forall|i: int| 0 <= i < t implies #[trigger] acc_cnt@[i] + bc@[i] <= u64::MAX by {
                assert(tval(acc_cnt@, acc_sum@, i, 5) == acc_cnt@[i]);
                assert(tval(bc@, bsm@, i, 5) == bc@[i]);
                assert(tval(bc@, bsm@, i, 5) == bsum(m, p as int, i, 5, g as int));
            }
        }
        add_into(acc_cnt, acc_sum, bc, bsm, t);
    } else {
        proof {
            assert forall|i: int, w: int| 0 <= i < t && 0 <= w <= 5 implies #[trigger] tval(acc_cnt@, acc_sum@, i, w)
                == tval(old(acc_cnt)@, old(acc_sum)@, i, w) + bsum(m, p as int, i, w, k + r * s) by {
                lemma_bsum_past(m, p as int, i, w, g as int);
            }
        }
    }
}

impl WorkerTask for FastTask {
    type Output = FastOut;

    open spec fn pre(&self) -> bool {
        task_pre(self.cols, self.n as int, self.bsize as int, self.nrf as int, self.nls as int, self.t as int,
            self.k as int, self.s as int, self.q as int, self.ng as int, self.p as int, self.out_cnt@, self.out_sum@,
            self.blk_cnt@, self.blk_sum@)
    }

    open spec fn post(&self, out: FastOut) -> bool {
        let m = cols_model(self.cols, self.n as int, self.bsize as int, self.nrf as int, self.nls as int);
        &&& out.cnt@.len() == self.t && out.sum@.len() == 5 * self.t
        &&& forall|i: int, w: int| 0 <= i < self.t && 0 <= w <= 5 ==> #[trigger] tval(out.cnt@, out.sum@, i, w)
            == ssum(m, self.p as int, i, w, self.k as int, self.s as int, self.q as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.k as u64, self.ng as u64)
    }

    fn run(self) -> (out: FastOut) {
        let FastTask { cols, n, bsize, nrf, nls, t, k, s, q, ng, p, out_cnt, out_sum, blk_cnt, blk_sum } = self;
        let ghost m = cols_model(cols, n as int, bsize as int, nrf as int, nls as int);
        let ghost pp = p as int;
        let mut acc_cnt = out_cnt;
        let mut acc_sum = out_sum;
        let mut bc = blk_cnt;
        let mut bsm = blk_sum;
        proof {
            assert forall|j: int| 0 <= j < m.n implies #[trigger] block_ok(m, blk(m, j)) by {
                lemma_blk(m, j);
            }
            assert forall|i: int, w: int| 0 <= i < t && 0 <= w <= 5 implies #[trigger] tval(acc_cnt@, acc_sum@, i, w) == 0 by {
                if w < 5 {
                    assert(0 <= i * 5 + w < 5 * t) by (nonlinear_arith) requires 0 <= i < t, 0 <= w < 5;
                }
            }
            assert(k * q <= 64 * m.nb) by (nonlinear_arith) requires 0 <= k < 64, 0 <= q <= m.nb;
        }
        // The first round `r0 = k * q / s`: concurrent tasks start in different regions of the table.
        let r0: usize = k * q / s;
        proof {
            assert(k * q <= q * s) by (nonlinear_arith) requires 0 <= k < s, q >= 0;
            vstd::arithmetic::div_mod::lemma_div_is_ordered((k * q) as int, (q * s) as int, s as int);
            vstd::arithmetic::div_mod::lemma_div_by_multiple(q as int, s as int);
            assert(r0 <= q);
        }
        // Pass 1, rounds `r0 .. q`: the table holds `ssum(r) - ssum(r0)`.
        let mut r: usize = r0;
        while r < q
            invariant
                rounds_pre(cols, n as int, bsize as int, nrf as int, nls as int, t as int, k as int, s as int,
                    q as int, ng as int, pp),
                m == cols_model(cols, n as int, bsize as int, nrf as int, nls as int), pp == p as int,
                r0 <= r <= q,
                acc_cnt@.len() == t, acc_sum@.len() == 5 * t, bc@.len() == t, bsm@.len() == 5 * t,
                forall|i: int, w: int| 0 <= i < t && 0 <= w <= 5 ==> #[trigger] tval(acc_cnt@, acc_sum@, i, w)
                    == ssum(m, pp, i, w, k as int, s as int, r as int) - ssum(m, pp, i, w, k as int, s as int, r0 as int),
            decreases q - r,
        {
            let ghost (oc, os) = (acc_cnt@, acc_sum@);
            proof {
                assert forall|i: int, w: int| 0 <= i < t && 0 <= w < 5 implies -0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff
                    <= #[trigger] tval(oc, os, i, w) + bsum(m, pp, i, w, k + r * s) <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff by {
                    lemma_rot_first(m, pp, i, k as int, s as int, r0 as int, r as int, q as int);
                    let x = (ssum(m, pp, i, w, k as int, s as int, r as int) - ssum(m, pp, i, w, k as int, s as int, r0 as int))
                        + bsum(m, pp, i, w, k + r * s);
                    assert(-0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff <= x <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff);
                }
                assert forall|i: int| 0 <= i < t implies 0 <= #[trigger] tval(oc, os, i, 5) + bsum(m, pp, i, 5, k + r * s) <= u64::MAX by {
                    lemma_rot_first(m, pp, i, k as int, s as int, r0 as int, r as int, q as int);
                }
            }
            add_round(&mut acc_cnt, &mut acc_sum, &mut bc, &mut bsm, &cols, n, bsize, nrf, nls, t, k, s, q, ng, p, r, Ghost(m));
            proof {
                assert forall|i: int, w: int| 0 <= i < t && 0 <= w <= 5 implies #[trigger] tval(acc_cnt@, acc_sum@, i, w)
                    == ssum(m, pp, i, w, k as int, s as int, r + 1) - ssum(m, pp, i, w, k as int, s as int, r0 as int) by {
                    lemma_rot_first(m, pp, i, k as int, s as int, r0 as int, r as int, q as int);
                    assert(tval(oc, os, i, w) == ssum(m, pp, i, w, k as int, s as int, r as int) - ssum(m, pp, i, w, k as int, s as int, r0 as int));
                    assert(ssum(m, pp, i, w, k as int, s as int, r + 1) == ssum(m, pp, i, w, k as int, s as int, r as int) + bsum(m, pp, i, w, k + r * s));
                }
            }
            r = r + 1;
        }
        // Pass 2, rounds `0 .. r0`: the table holds `ssum(q) - ssum(r0) + ssum(r)`.
        let mut r: usize = 0;
        proof {
            assert forall|i: int, w: int| 0 <= i < t && 0 <= w <= 5 implies #[trigger] tval(acc_cnt@, acc_sum@, i, w)
                == ssum(m, pp, i, w, k as int, s as int, q as int) - ssum(m, pp, i, w, k as int, s as int, r0 as int)
                    + ssum(m, pp, i, w, k as int, s as int, 0) by {}
        }
        while r < r0
            invariant
                rounds_pre(cols, n as int, bsize as int, nrf as int, nls as int, t as int, k as int, s as int,
                    q as int, ng as int, pp),
                m == cols_model(cols, n as int, bsize as int, nrf as int, nls as int), pp == p as int,
                r <= r0 <= q,
                acc_cnt@.len() == t, acc_sum@.len() == 5 * t, bc@.len() == t, bsm@.len() == 5 * t,
                forall|i: int, w: int| 0 <= i < t && 0 <= w <= 5 ==> #[trigger] tval(acc_cnt@, acc_sum@, i, w)
                    == ssum(m, pp, i, w, k as int, s as int, q as int) - ssum(m, pp, i, w, k as int, s as int, r0 as int)
                        + ssum(m, pp, i, w, k as int, s as int, r as int),
            decreases r0 - r,
        {
            let ghost (oc, os) = (acc_cnt@, acc_sum@);
            proof {
                assert forall|i: int, w: int| 0 <= i < t && 0 <= w < 5 implies -0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff
                    <= #[trigger] tval(oc, os, i, w) + bsum(m, pp, i, w, k + r * s) <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff by {
                    lemma_rot_second(m, pp, i, k as int, s as int, r0 as int, r as int, q as int);
                    let x = (ssum(m, pp, i, w, k as int, s as int, q as int) - ssum(m, pp, i, w, k as int, s as int, r0 as int)
                        + ssum(m, pp, i, w, k as int, s as int, r as int)) + bsum(m, pp, i, w, k + r * s);
                    assert(-0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff <= x <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff);
                }
                assert forall|i: int| 0 <= i < t implies 0 <= #[trigger] tval(oc, os, i, 5) + bsum(m, pp, i, 5, k + r * s) <= u64::MAX by {
                    lemma_rot_second(m, pp, i, k as int, s as int, r0 as int, r as int, q as int);
                }
            }
            add_round(&mut acc_cnt, &mut acc_sum, &mut bc, &mut bsm, &cols, n, bsize, nrf, nls, t, k, s, q, ng, p, r, Ghost(m));
            proof {
                assert forall|i: int, w: int| 0 <= i < t && 0 <= w <= 5 implies #[trigger] tval(acc_cnt@, acc_sum@, i, w)
                    == ssum(m, pp, i, w, k as int, s as int, q as int) - ssum(m, pp, i, w, k as int, s as int, r0 as int)
                        + ssum(m, pp, i, w, k as int, s as int, r + 1) by {
                    lemma_rot_second(m, pp, i, k as int, s as int, r0 as int, r as int, q as int);
                    assert(ssum(m, pp, i, w, k as int, s as int, r + 1) == ssum(m, pp, i, w, k as int, s as int, r as int) + bsum(m, pp, i, w, k + r * s));
                }
            }
            r = r + 1;
        }
        FastOut { cnt: acc_cnt, sum: acc_sum }
    }
}

} // verus!
