//! Code-domain chunk passes for the two hot chunk kinds: every row of the chunk in one pair (`chunk_all2`) and two
//! pairs told apart by one code column in a full block (`chunk_split2`).
//!
//! A pass sums only the stored codes and their small products, with 32 x 32 -> 64-bit multiplies (no 64-bit
//! multiply per row): per selection the count and the sums of `q`, `p`, `p*d`, `p*t`, `p*(d*t)`, `d`, `t` and `d*t`,
//! where `q, p, d, t` are the chunk's quantity, price, discount and tax codes. The block bases enter once per chunk
//! (`finish2`): with `P = bp + p`, `k1 = 100 - bd`, `k2 = 100 + bt`,
//!   `P * (k1 - d)            = bp*k1 - bp*d + k1*p - p*d`,
//!   `P * (k1 - d) * (k2 + t) = bp*k1*k2 + bp*k1*t - bp*k2*d - bp*(d*t) + k1*k2*p + k1*(p*t) - k2*(p*d) - p*(d*t)`,
//! so the decoded sums are those `fast::sums_ok` states (`lemma_cdp_sum`, `lemma_cch_sum`). With at most `CHUNK`
//! rows every code sum fits in `u64` (the largest, `p*(d*t)`, below `2048 * 2^32 * 65025 < 2^59`).
use vstd::prelude::*;
use super::common::csum::*;
use super::fast::*;

verus! {

// ------------------------------------------------------------------------------------------------ code-domain values

pub open spec fn cpc(ps: Seq<u32>) -> spec_fn(int) -> int {
    |i: int| ps[i] as int
}

pub open spec fn cpd(ps: Seq<u32>, ds: Seq<u8>) -> spec_fn(int) -> int {
    |i: int| ps[i] * ds[i]
}

pub open spec fn cpt(ps: Seq<u32>, ts: Seq<u8>) -> spec_fn(int) -> int {
    |i: int| ps[i] * ts[i]
}

pub open spec fn cpdt(ps: Seq<u32>, ds: Seq<u8>, ts: Seq<u8>) -> spec_fn(int) -> int {
    |i: int| ps[i] * (ds[i] * ts[i])
}

pub open spec fn ctc(ts: Seq<u8>) -> spec_fn(int) -> int {
    |i: int| ts[i] as int
}

pub open spec fn cdt(ds: Seq<u8>, ts: Seq<u8>) -> spec_fn(int) -> int {
    |i: int| ds[i] * ts[i]
}

/// The code-domain loop state of a pass over positions `0 .. j` for selection `sel`.
pub open spec fn acc2_ok(sel: spec_fn(int) -> bool, qs: Seq<u16>, ps: Seq<u32>, ds: Seq<u8>, ts: Seq<u8>, j: int,
    c: u64, q: u64, s1: u64, s2: u64, s3: u64, s4: u64, d: u64, t: u64, dt: u64) -> bool
{
    &&& c == csum(sel, one(), j) && c <= j
    &&& q == csum(sel, cqc(qs), j) && q <= j * 0xffff
    &&& s1 == csum(sel, cpc(ps), j) && s1 <= j * 0xffff_ffff
    &&& s2 == csum(sel, cpd(ps, ds), j) && s2 <= j * (0xffff_ffff * 255)
    &&& s3 == csum(sel, cpt(ps, ts), j) && s3 <= j * (0xffff_ffff * 255)
    &&& s4 == csum(sel, cpdt(ps, ds, ts), j) && s4 <= j * (0xffff_ffff * 65025)
    &&& d == csum(sel, cdc(ds), j) && d <= j * 255
    &&& t == csum(sel, ctc(ts), j) && t <= j * 255
    &&& dt == csum(sel, cdt(ds, ts), j) && dt <= j * 65025
}

/// The code products of one row, each within its bound.
pub open spec fn row_codes_ok(ps: Seq<u32>, ds: Seq<u8>, ts: Seq<u8>, j: int, pd: int, pt: int, pdt: int, dt: int) -> bool {
    &&& pd == ps[j] * ds[j] && pd <= 0xffff_ffff * 255
    &&& pt == ps[j] * ts[j] && pt <= 0xffff_ffff * 255
    &&& dt == ds[j] * ts[j] && dt <= 65025
    &&& pdt == ps[j] * (ds[j] * ts[j]) && pdt <= 0xffff_ffff * 65025
}

/// The code products of row `j` (32 x 32 -> 64-bit multiplies).
#[inline]
fn row_codes(pc: u32, dc: u8, tc: u8) -> (r: (u64, u64, u64, u64))
    ensures
        r.0 == pc * dc, r.1 == pc * tc, r.3 == dc * tc, r.2 == pc * (dc * tc),
        r.0 <= 0xffff_ffff * 255, r.1 <= 0xffff_ffff * 255, r.3 <= 65025, r.2 <= 0xffff_ffff * 65025,
    no_unwind
{
    let p = pc as u64;
    let d = dc as u64;
    let t = tc as u64;
    assert(d * t <= 65025) by (nonlinear_arith) requires d <= 255, t <= 255;
    let dt = d * t;
    assert(p * d <= 0xffff_ffff * 255) by (nonlinear_arith) requires p <= 0xffff_ffff, d <= 255;
    assert(p * t <= 0xffff_ffff * 255) by (nonlinear_arith) requires p <= 0xffff_ffff, t <= 255;
    assert(p * dt <= 0xffff_ffff * 65025) by (nonlinear_arith) requires p <= 0xffff_ffff, dt <= 65025;
    (p * d, p * t, p * dt, dt)
}

/// `x` when `b`, else 0 (a select, no branch).
#[inline]
fn pick(x: u64, b: bool) -> (r: u64)
    ensures r == if b { x } else { 0 },
    no_unwind
{
    if b { x } else { 0 }
}

/// One loop step of a code-domain pass: position `j` with selection bit `b`.
proof fn lemma_acc2_step(sel: spec_fn(int) -> bool, qs: Seq<u16>, ps: Seq<u32>, ds: Seq<u8>, ts: Seq<u8>, j: int,
    c: u64, q: u64, s1: u64, s2: u64, s3: u64, s4: u64, d: u64, t: u64, dt: u64, b: bool,
    pd: int, pt: int, pdt: int, dtv: int)
    requires
        0 <= j < 2048, j < qs.len(), j < ps.len(), j < ds.len(), j < ts.len(),
        acc2_ok(sel, qs, ps, ds, ts, j, c, q, s1, s2, s3, s4, d, t, dt),
        b == sel(j),
        row_codes_ok(ps, ds, ts, j, pd, pt, pdt, dtv),
    ensures ({
        let k = if b { 1int } else { 0int };
        let (c2, q2, p2) = (c + k, q + if b { qs[j] as int } else { 0 }, s1 + if b { ps[j] as int } else { 0 });
        let (pd2, pt2, pdt2) = (s2 + if b { pd } else { 0 }, s3 + if b { pt } else { 0 }, s4 + if b { pdt } else { 0 });
        let (d2, t2, dt2) = (d + if b { ds[j] as int } else { 0 }, t + if b { ts[j] as int } else { 0 },
            dt + if b { dtv } else { 0 });
        &&& c2 <= u64::MAX && q2 <= u64::MAX && p2 <= u64::MAX && pd2 <= u64::MAX && pt2 <= u64::MAX
        &&& pdt2 <= u64::MAX && d2 <= u64::MAX && t2 <= u64::MAX && dt2 <= u64::MAX
        &&& acc2_ok(sel, qs, ps, ds, ts, j + 1, c2 as u64, q2 as u64, p2 as u64, pd2 as u64, pt2 as u64,
            pdt2 as u64, d2 as u64, t2 as u64, dt2 as u64)
    }),
{
    lemma_csum_step(sel, one(), j);
    lemma_csum_step(sel, cqc(qs), j);
    lemma_csum_step(sel, cpc(ps), j);
    lemma_csum_step(sel, cpd(ps, ds), j);
    lemma_csum_step(sel, cpt(ps, ts), j);
    lemma_csum_step(sel, cpdt(ps, ds, ts), j);
    lemma_csum_step(sel, cdc(ds), j);
    lemma_csum_step(sel, ctc(ts), j);
    lemma_csum_step(sel, cdt(ds, ts), j);
    assert(cpd(ps, ds)(j) == pd && cpt(ps, ts)(j) == pt && cpdt(ps, ds, ts)(j) == pdt && cdt(ds, ts)(j) == dtv);
    assert((j + 1) * (0xffff_ffff * 65025) == j * (0xffff_ffff * 65025) + 0xffff_ffff * 65025) by (nonlinear_arith);
    assert((j + 1) * (0xffff_ffff * 255) == j * (0xffff_ffff * 255) + 0xffff_ffff * 255) by (nonlinear_arith);
    assert((j + 1) * 0xffff_ffff == j * 0xffff_ffff + 0xffff_ffff) by (nonlinear_arith);
    assert((j + 1) * 0xffff == j * 0xffff + 0xffff) by (nonlinear_arith);
    assert((j + 1) * 65025 == j * 65025 + 65025) by (nonlinear_arith);
    assert((j + 1) * 255 == j * 255 + 255) by (nonlinear_arith);
    assert(j * (0xffff_ffff * 65025) + 0xffff_ffff * 65025 <= 2048 * (0xffff_ffff * 65025)) by (nonlinear_arith)
        requires j < 2048;
}

// ------------------------------------------------------------------------------------------------ decoding

/// Discounted price sums from code sums: `(bp + p) * (k1 - d) = bp*k1 - bp*d + k1*p - p*d` summed.
proof fn lemma_cdp_sum(sel: spec_fn(int) -> bool, ps: Seq<u32>, ds: Seq<u8>, bp: int, bd: int, m: int)
    requires m >= 0,
    ensures ({
        let k1 = 100 - bd;
        csum(sel, cdp(ps, ds, bp, bd), m) == bp * k1 * csum(sel, one(), m) - bp * csum(sel, cdc(ds), m)
            + k1 * csum(sel, cpc(ps), m) - csum(sel, cpd(ps, ds), m)
    }),
    decreases m,
{
    if m > 0 {
        let j = m - 1;
        let k1 = 100 - bd;
        lemma_cdp_sum(sel, ps, ds, bp, bd, j);
        lemma_csum_step(sel, cdp(ps, ds, bp, bd), j);
        lemma_csum_step(sel, one(), j);
        lemma_csum_step(sel, cdc(ds), j);
        lemma_csum_step(sel, cpc(ps), j);
        lemma_csum_step(sel, cpd(ps, ds), j);
        let (g0, c0, d0, p0, pd0) = (csum(sel, cdp(ps, ds, bp, bd), j), csum(sel, one(), j), csum(sel, cdc(ds), j),
            csum(sel, cpc(ps), j), csum(sel, cpd(ps, ds), j));
        if sel(j) {
            let (p, d) = (ps[j] as int, ds[j] as int);
            assert(cdp(ps, ds, bp, bd)(j) == (bp + p) * (k1 - d));
            assert((bp + p) * (k1 - d) == bp * k1 - bp * d + k1 * p - p * d) by (nonlinear_arith);
            assert(g0 + (bp * k1 - bp * d + k1 * p - p * d) == bp * k1 * (c0 + 1) - bp * (d0 + d) + k1 * (p0 + p)
                - (pd0 + p * d)) by (nonlinear_arith)
                requires g0 == bp * k1 * c0 - bp * d0 + k1 * p0 - pd0;
        }
    }
}

/// `(x1 - x2 + x3 - x4) * y` distributed.
proof fn lemma_dist4(x1: int, x2: int, x3: int, x4: int, y: int)
    ensures (x1 - x2 + x3 - x4) * y == x1 * y - x2 * y + x3 * y - x4 * y,
{
    assert((x1 - x2 + x3 - x4) * y == x1 * y - x2 * y + x3 * y - x4 * y) by (nonlinear_arith);
}

/// `(bp + p) * (k1 - d) * (k2 + t)` expanded, one distribution step at a time.
proof fn lemma_expand3(bp: int, p: int, k1: int, d: int, k2: int, t: int)
    ensures (bp + p) * (k1 - d) * (k2 + t) == bp * k1 * k2 + bp * k1 * t - bp * k2 * d - bp * (d * t)
        + k1 * k2 * p + k1 * (p * t) - k2 * (p * d) - p * (d * t),
{
    let (x1, x2, x3, x4) = (bp * k1, bp * d, k1 * p, p * d);
    let a = x1 - x2 + x3 - x4;
    assert((bp + p) * (k1 - d) == a) by (nonlinear_arith) requires a == bp * k1 - bp * d + k1 * p - p * d;
    assert(a * (k2 + t) == a * k2 + a * t) by (nonlinear_arith);
    lemma_dist4(x1, x2, x3, x4, k2);
    lemma_dist4(x1, x2, x3, x4, t);
    assert(x2 * k2 == bp * k2 * d) by (nonlinear_arith) requires x2 == bp * d;
    assert(x3 * k2 == k1 * k2 * p) by (nonlinear_arith) requires x3 == k1 * p;
    assert(x4 * k2 == k2 * (p * d)) by (nonlinear_arith) requires x4 == p * d;
    assert(x1 * t == bp * k1 * t) by (nonlinear_arith) requires x1 == bp * k1;
    assert(x2 * t == bp * (d * t)) by (nonlinear_arith) requires x2 == bp * d;
    assert(x3 * t == k1 * (p * t)) by (nonlinear_arith) requires x3 == k1 * p;
    assert(x4 * t == p * (d * t)) by (nonlinear_arith) requires x4 == p * d;
}

/// Charge sums from code sums: `(bp + p) * (k1 - d) * (k2 + t)` expanded into eight code-sum terms.
proof fn lemma_cch_sum(sel: spec_fn(int) -> bool, ps: Seq<u32>, ds: Seq<u8>, ts: Seq<u8>, bp: int, bd: int, bt: int, m: int)
    requires m >= 0,
    ensures ({
        let (k1, k2) = (100 - bd, 100 + bt);
        csum(sel, cch(ps, ds, ts, bp, bd, bt), m) == bp * k1 * k2 * csum(sel, one(), m) + bp * k1 * csum(sel, ctc(ts), m)
            - bp * k2 * csum(sel, cdc(ds), m) - bp * csum(sel, cdt(ds, ts), m) + k1 * k2 * csum(sel, cpc(ps), m)
            + k1 * csum(sel, cpt(ps, ts), m) - k2 * csum(sel, cpd(ps, ds), m) - csum(sel, cpdt(ps, ds, ts), m)
    }),
    decreases m,
{
    if m > 0 {
        let j = m - 1;
        let (k1, k2) = (100 - bd, 100 + bt);
        lemma_cch_sum(sel, ps, ds, ts, bp, bd, bt, j);
        lemma_csum_step(sel, cch(ps, ds, ts, bp, bd, bt), j);
        lemma_csum_step(sel, one(), j);
        lemma_csum_step(sel, ctc(ts), j);
        lemma_csum_step(sel, cdc(ds), j);
        lemma_csum_step(sel, cdt(ds, ts), j);
        lemma_csum_step(sel, cpc(ps), j);
        lemma_csum_step(sel, cpt(ps, ts), j);
        lemma_csum_step(sel, cpd(ps, ds), j);
        lemma_csum_step(sel, cpdt(ps, ds, ts), j);
        let g0 = csum(sel, cch(ps, ds, ts, bp, bd, bt), j);
        let (c0, t0, d0, dt0) = (csum(sel, one(), j), csum(sel, ctc(ts), j), csum(sel, cdc(ds), j), csum(sel, cdt(ds, ts), j));
        let (p0, pt0, pd0, pdt0) = (csum(sel, cpc(ps), j), csum(sel, cpt(ps, ts), j), csum(sel, cpd(ps, ds), j),
            csum(sel, cpdt(ps, ds, ts), j));
        if sel(j) {
            let (p, d, t) = (ps[j] as int, ds[j] as int, ts[j] as int);
            assert(cch(ps, ds, ts, bp, bd, bt)(j) == (bp + p) * (k1 - d) * (k2 + t));
            lemma_expand3(bp, p, k1, d, k2, t);
            assert(g0 + (bp * k1 * k2 + bp * k1 * t - bp * k2 * d - bp * (d * t) + k1 * k2 * p + k1 * (p * t) - k2 * (p * d)
                - p * (d * t)) == bp * k1 * k2 * (c0 + 1) + bp * k1 * (t0 + t) - bp * k2 * (d0 + d) - bp * (dt0 + d * t)
                + k1 * k2 * (p0 + p) + k1 * (pt0 + p * t) - k2 * (pd0 + p * d) - (pdt0 + p * (d * t))) by (nonlinear_arith)
                requires g0 == bp * k1 * k2 * c0 + bp * k1 * t0 - bp * k2 * d0 - bp * dt0 + k1 * k2 * p0 + k1 * pt0
                    - k2 * pd0 - pdt0;
        }
    }
}

/// The decoded chunk sums of a finished code-domain pass (`fast::sums_ok`).
fn finish2(c: u64, q: u64, s1: u64, s2: u64, s3: u64, s4: u64, d: u64, t: u64, dt: u64, bq: i64, bp: i64, bd: i64,
    bt: i64, Ghost(sel): Ghost<spec_fn(int) -> bool>, Ghost(qs): Ghost<Seq<u16>>, Ghost(ps): Ghost<Seq<u32>>,
    Ghost(ds): Ghost<Seq<u8>>, Ghost(ts): Ghost<Seq<u8>>, Ghost(m): Ghost<int>) -> (r: ChunkSums)
    requires
        0 <= m <= 2048, m <= qs.len(), m <= ps.len(), m <= ds.len(), m <= ts.len(), bases_ok(bq, bp, bd, bt),
        acc2_ok(sel, qs, ps, ds, ts, m, c, q, s1, s2, s3, s4, d, t, dt),
    ensures sums_ok(r, sel, qs, ps, ds, ts, bq, bp, bd, bt, m),
    no_unwind
{
    proof {
        assert(m * (0xffff_ffff * 65025) <= 2048 * (0xffff_ffff * 65025)) by (nonlinear_arith) requires m <= 2048;
        assert(m * (0xffff_ffff * 255) <= 2048 * (0xffff_ffff * 255)) by (nonlinear_arith) requires m <= 2048;
        assert(m * 0xffff_ffff <= 2048 * 0xffff_ffff) by (nonlinear_arith) requires m <= 2048;
        assert(m * 0xffff <= 2048 * 0xffff) by (nonlinear_arith) requires m <= 2048;
        assert(m * 65025 <= 2048 * 65025) by (nonlinear_arith) requires m <= 2048;
        assert(m * 255 <= 2048 * 255) by (nonlinear_arith) requires m <= 2048;
    }
    let (ci, qi, p1, pd, pt, pdt) = (c as i128, q as i128, s1 as i128, s2 as i128, s3 as i128, s4 as i128);
    let (di, ti, dti) = (d as i128, t as i128, dt as i128);
    let (b, k1, k2) = (bp as i128, (100 - bd) as i128, (100 + bt) as i128);
    proof {
        assert(-0x1_0000_0000 * 100 <= b * k1 <= 0x1_0000_0000 * 100) by (nonlinear_arith)
            requires -0x1_0000_0000 <= b <= 0x1_0000_0000, 0 <= k1 <= 100;
        assert(-0x1_0000_0000 * 200 <= b * k2 <= 0x1_0000_0000 * 200) by (nonlinear_arith)
            requires -0x1_0000_0000 <= b <= 0x1_0000_0000, 100 <= k2 <= 200;
        assert(0 <= k1 * k2 <= 20000) by (nonlinear_arith) requires 0 <= k1 <= 100, 100 <= k2 <= 200;
        assert(-0x1_0000_0000 * 20000 <= b * k1 * k2 <= 0x1_0000_0000 * 20000) by (nonlinear_arith)
            requires -0x1_0000_0000 * 100 <= b * k1 <= 0x1_0000_0000 * 100, 100 <= k2 <= 200;
        assert(-0x1_0000_0000 * 20000 * 2048 <= b * k1 * k2 * ci <= 0x1_0000_0000 * 20000 * 2048) by (nonlinear_arith)
            requires -0x1_0000_0000 * 20000 <= b * k1 * k2 <= 0x1_0000_0000 * 20000, 0 <= ci <= 2048;
        assert(-0x1_0000_0000 * 100 * 2048 <= b * k1 * ci <= 0x1_0000_0000 * 100 * 2048) by (nonlinear_arith)
            requires -0x1_0000_0000 * 100 <= b * k1 <= 0x1_0000_0000 * 100, 0 <= ci <= 2048;
        assert(-0x1_0000_0000 * 100 * 2048 * 255 <= b * k1 * ti <= 0x1_0000_0000 * 100 * 2048 * 255) by (nonlinear_arith)
            requires -0x1_0000_0000 * 100 <= b * k1 <= 0x1_0000_0000 * 100, 0 <= ti <= 2048 * 255;
        assert(-0x1_0000_0000 * 200 * 2048 * 255 <= b * k2 * di <= 0x1_0000_0000 * 200 * 2048 * 255) by (nonlinear_arith)
            requires -0x1_0000_0000 * 200 <= b * k2 <= 0x1_0000_0000 * 200, 0 <= di <= 2048 * 255;
        assert(-0x1_0000_0000 * 2048 * 255 <= b * di <= 0x1_0000_0000 * 2048 * 255) by (nonlinear_arith)
            requires -0x1_0000_0000 <= b <= 0x1_0000_0000, 0 <= di <= 2048 * 255;
        assert(-0x1_0000_0000 * 2048 * 65025 <= b * dti <= 0x1_0000_0000 * 2048 * 65025) by (nonlinear_arith)
            requires -0x1_0000_0000 <= b <= 0x1_0000_0000, 0 <= dti <= 2048 * 65025;
        assert(-0x1_0000_0000 * 2048 <= b * ci <= 0x1_0000_0000 * 2048) by (nonlinear_arith)
            requires -0x1_0000_0000 <= b <= 0x1_0000_0000, 0 <= ci <= 2048;
        assert(0 <= k1 * k2 * p1 <= 20000 * (2048 * 0xffff_ffff)) by (nonlinear_arith)
            requires 0 <= k1 * k2 <= 20000, 0 <= p1 <= 2048 * 0xffff_ffff;
        assert(0 <= k1 * p1 <= 100 * (2048 * 0xffff_ffff)) by (nonlinear_arith)
            requires 0 <= k1 <= 100, 0 <= p1 <= 2048 * 0xffff_ffff;
        assert(0 <= k1 * pt <= 100 * (2048 * (0xffff_ffff * 255))) by (nonlinear_arith)
            requires 0 <= k1 <= 100, 0 <= pt <= 2048 * (0xffff_ffff * 255);
        assert(0 <= k2 * pd <= 200 * (2048 * (0xffff_ffff * 255))) by (nonlinear_arith)
            requires 100 <= k2 <= 200, 0 <= pd <= 2048 * (0xffff_ffff * 255);
        assert(0 <= bd * ci <= 100 * 2048) by (nonlinear_arith) requires 0 <= bd <= 100, 0 <= ci <= 2048;
        assert(-0x1_0000_0000 * 2048 <= bq * ci <= 0x1_0000_0000 * 2048) by (nonlinear_arith)
            requires -0x1_0000_0000 <= bq <= 0x1_0000_0000, 0 <= ci <= 2048;
    }
    let pv = b * ci + p1;
    let dpv = b * k1 * ci - b * di + k1 * p1 - pd;
    let chv = b * k1 * k2 * ci + b * k1 * ti - b * k2 * di - b * dti + k1 * k2 * p1 + k1 * pt - k2 * pd - pdt;
    proof {
        lemma_csum_affine(sel, cpc(ps), cp(ps, bp as int), bp as int, m);
        lemma_cdp_sum(sel, ps, ds, bp as int, bd as int, m);
        lemma_cch_sum(sel, ps, ds, ts, bp as int, bd as int, bt as int, m);
        lemma_csum_affine(sel, cqc(qs), cq(qs, bq as int), bq as int, m);
        lemma_csum_affine(sel, cdc(ds), cd(ds, bd as int), bd as int, m);
        lemma_count_bounds(sel, m);
        lemma_csum_bounds_split(sel, sel, qs, ps, ds, ts, bp, bd, bt, m);
        assert(pv == csum(sel, cp(ps, bp as int), m));
        assert(dpv == csum(sel, cdp(ps, ds, bp as int, bd as int), m));
        assert(chv == csum(sel, cch(ps, ds, ts, bp as int, bd as int, bt as int), m));
    }
    ChunkSums { cnt: c as i64, q: (qi + bq as i128 * ci) as i64, p: pv as i64, dp: dpv as i64, ch: chv as i64,
        d: (di + bd as i128 * ci) as i64 }
}

// ------------------------------------------------------------------------------------------------ the passes

/// Every position of a chunk whose rows all hold one pair and pass the date bound.
pub fn chunk_all2(qs: &[u16], ps: &[u32], ds: &[u8], ts: &[u8], m: usize, bq: i64, bp: i64, bd: i64, bt: i64) -> (r: ChunkSums)
    requires
        m <= CHUNK, m <= qs@.len(), m <= ps@.len(), m <= ds@.len(), m <= ts@.len(),
        bases_ok(bq, bp, bd, bt),
    ensures sums_ok(r, sel_all(), qs@, ps@, ds@, ts@, bq, bp, bd, bt, m as int),
    no_unwind
{
    let ghost sel = sel_all();
    let (mut c, mut q, mut s1, mut s2, mut s3, mut s4, mut d, mut t, mut dt) = (0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
    let mut j: usize = 0;
    while j < m
        invariant
            j <= m, m <= CHUNK, m <= qs@.len(), m <= ps@.len(), m <= ds@.len(), m <= ts@.len(),
            sel == sel_all(),
            acc2_ok(sel, qs@, ps@, ds@, ts@, j as int, c, q, s1, s2, s3, s4, d, t, dt),
        decreases m - j,
    {
        let (pd, pt, pdt, dtv) = row_codes(ps[j], ds[j], ts[j]);
        proof {
            lemma_acc2_step(sel, qs@, ps@, ds@, ts@, j as int, c, q, s1, s2, s3, s4, d, t, dt, true,
                pd as int, pt as int, pdt as int, dtv as int);
        }
        c = c + 1;
        q = q + qs[j] as u64;
        s1 = s1 + ps[j] as u64;
        s2 = s2 + pd;
        s3 = s3 + pt;
        s4 = s4 + pdt;
        d = d + ds[j] as u64;
        t = t + ts[j] as u64;
        dt = dt + dtv;
        j = j + 1;
    }
    finish2(c, q, s1, s2, s3, s4, d, t, dt, bq, bp, bd, bt, Ghost(sel), Ghost(qs@), Ghost(ps@), Ghost(ds@), Ghost(ts@),
        Ghost(m as int))
}

/// One pass over a full chunk holding two pairs told apart by the code column `xs`: `xs[i] == x1` and the rest
/// (the second pair's code sums are the chunk's totals minus the first pair's).
pub fn chunk_split2(qs: &[u16], ps: &[u32], ds: &[u8], ts: &[u8], xs: &[u8], m: usize, bq: i64, bp: i64, bd: i64,
    bt: i64, x1: u8) -> (r: ChunkSums2)
    requires
        m <= CHUNK, m <= qs@.len(), m <= ps@.len(), m <= ds@.len(), m <= ts@.len(), m <= xs@.len(),
        bases_ok(bq, bp, bd, bt),
    ensures
        sums_ok(r.a, sel_eq(xs@, x1 as int), qs@, ps@, ds@, ts@, bq, bp, bd, bt, m as int),
        sums_ok(r.b, sel_ne(xs@, x1 as int), qs@, ps@, ds@, ts@, bq, bp, bd, bt, m as int),
    no_unwind
{
    let ghost s1 = sel_eq(xs@, x1 as int);
    let ghost sa = sel_all();
    let (mut c1, mut q1, mut p1, mut pd1, mut pt1, mut pdt1, mut d1, mut t1, mut dt1) =
        (0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
    let (mut ca, mut qa, mut pa, mut pda, mut pta, mut pdta, mut da, mut ta, mut dta) =
        (0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
    let mut j: usize = 0;
    while j < m
        invariant
            j <= m, m <= CHUNK, m <= qs@.len(), m <= ps@.len(), m <= ds@.len(), m <= ts@.len(), m <= xs@.len(),
            s1 == sel_eq(xs@, x1 as int), sa == sel_all(),
            acc2_ok(s1, qs@, ps@, ds@, ts@, j as int, c1, q1, p1, pd1, pt1, pdt1, d1, t1, dt1),
            acc2_ok(sa, qs@, ps@, ds@, ts@, j as int, ca, qa, pa, pda, pta, pdta, da, ta, dta),
        decreases m - j,
    {
        let a = xs[j] == x1;
        let (pd, pt, pdt, dtv) = row_codes(ps[j], ds[j], ts[j]);
        proof {
            lemma_acc2_step(s1, qs@, ps@, ds@, ts@, j as int, c1, q1, p1, pd1, pt1, pdt1, d1, t1, dt1, a,
                pd as int, pt as int, pdt as int, dtv as int);
            lemma_acc2_step(sa, qs@, ps@, ds@, ts@, j as int, ca, qa, pa, pda, pta, pdta, da, ta, dta, true,
                pd as int, pt as int, pdt as int, dtv as int);
        }
        let qv = qs[j] as u64;
        let pv = ps[j] as u64;
        let dv = ds[j] as u64;
        let tv = ts[j] as u64;
        c1 = c1 + pick(1, a);
        q1 = q1 + pick(qv, a);
        p1 = p1 + pick(pv, a);
        pd1 = pd1 + pick(pd, a);
        pt1 = pt1 + pick(pt, a);
        pdt1 = pdt1 + pick(pdt, a);
        d1 = d1 + pick(dv, a);
        t1 = t1 + pick(tv, a);
        dt1 = dt1 + pick(dtv, a);
        ca = ca + 1;
        qa = qa + qv;
        pa = pa + pv;
        pda = pda + pd;
        pta = pta + pt;
        pdta = pdta + pdt;
        da = da + dv;
        ta = ta + tv;
        dta = dta + dtv;
        j = j + 1;
    }
    let ghost s2 = sel_ne(xs@, x1 as int);
    proof {
        assert forall|i: int| 0 <= i < m implies #[trigger] s2(i) == !s1(i) by {}
        lemma_split_acc2(s1, s2, qs@, ps@, ds@, ts@, m as int, c1, q1, p1, pd1, pt1, pdt1, d1, t1, dt1,
            ca, qa, pa, pda, pta, pdta, da, ta, dta);
    }
    let ra = finish2(c1, q1, p1, pd1, pt1, pdt1, d1, t1, dt1, bq, bp, bd, bt, Ghost(s1), Ghost(qs@), Ghost(ps@),
        Ghost(ds@), Ghost(ts@), Ghost(m as int));
    let rb = finish2(ca - c1, qa - q1, pa - p1, pda - pd1, pta - pt1, pdta - pdt1, da - d1, ta - t1, dta - dt1,
        bq, bp, bd, bt, Ghost(s2), Ghost(qs@), Ghost(ps@), Ghost(ds@), Ghost(ts@), Ghost(m as int));
    ChunkSums2 { a: ra, b: rb }
}

/// The code-domain state of the complement selection: the totals minus the first selection's (each a sum of
/// non-negative terms over fewer positions, so within the same bounds).
proof fn lemma_split_acc2(s1: spec_fn(int) -> bool, s2: spec_fn(int) -> bool, qs: Seq<u16>, ps: Seq<u32>, ds: Seq<u8>,
    ts: Seq<u8>, m: int, c1: u64, q1: u64, p1: u64, pd1: u64, pt1: u64, pdt1: u64, d1: u64, t1: u64, dt1: u64,
    ca: u64, qa: u64, pa: u64, pda: u64, pta: u64, pdta: u64, da: u64, ta: u64, dta: u64)
    requires
        0 <= m <= 2048, m <= qs.len(), m <= ps.len(), m <= ds.len(), m <= ts.len(),
        forall|i: int| 0 <= i < m ==> #[trigger] s2(i) == !s1(i),
        acc2_ok(s1, qs, ps, ds, ts, m, c1, q1, p1, pd1, pt1, pdt1, d1, t1, dt1),
        acc2_ok(sel_all(), qs, ps, ds, ts, m, ca, qa, pa, pda, pta, pdta, da, ta, dta),
    ensures
        c1 <= ca && q1 <= qa && p1 <= pa && pd1 <= pda && pt1 <= pta && pdt1 <= pdta && d1 <= da && t1 <= ta && dt1 <= dta,
        acc2_ok(s2, qs, ps, ds, ts, m, (ca - c1) as u64, (qa - q1) as u64, (pa - p1) as u64, (pda - pd1) as u64,
            (pta - pt1) as u64, (pdta - pdt1) as u64, (da - d1) as u64, (ta - t1) as u64, (dta - dt1) as u64),
{
    lemma_csum_complement(s1, s2, one(), m);
    lemma_csum_complement(s1, s2, cqc(qs), m);
    lemma_csum_complement(s1, s2, cpc(ps), m);
    lemma_csum_complement(s1, s2, cpd(ps, ds), m);
    lemma_csum_complement(s1, s2, cpt(ps, ts), m);
    lemma_csum_complement(s1, s2, cpdt(ps, ds, ts), m);
    lemma_csum_complement(s1, s2, cdc(ds), m);
    lemma_csum_complement(s1, s2, ctc(ts), m);
    lemma_csum_complement(s1, s2, cdt(ds, ts), m);
    lemma_code_bounds(s2, qs, ps, ds, ts, m);
}

/// Bounds of any selection's code sums (each a sum of non-negative terms within its row bound).
proof fn lemma_code_bounds(sel: spec_fn(int) -> bool, qs: Seq<u16>, ps: Seq<u32>, ds: Seq<u8>, ts: Seq<u8>, m: int)
    requires 0 <= m, m <= qs.len(), m <= ps.len(), m <= ds.len(), m <= ts.len(),
    ensures
        0 <= csum(sel, one(), m) <= m,
        0 <= csum(sel, cqc(qs), m) <= m * 0xffff,
        0 <= csum(sel, cpc(ps), m) <= m * 0xffff_ffff,
        0 <= csum(sel, cpd(ps, ds), m) <= m * (0xffff_ffff * 255),
        0 <= csum(sel, cpt(ps, ts), m) <= m * (0xffff_ffff * 255),
        0 <= csum(sel, cpdt(ps, ds, ts), m) <= m * (0xffff_ffff * 65025),
        0 <= csum(sel, cdc(ds), m) <= m * 255,
        0 <= csum(sel, ctc(ts), m) <= m * 255,
        0 <= csum(sel, cdt(ds, ts), m) <= m * 65025,
    decreases m,
{
    if m > 0 {
        let j = m - 1;
        lemma_code_bounds(sel, qs, ps, ds, ts, j);
        let (p, d, t) = (ps[j] as int, ds[j] as int, ts[j] as int);
        assert(0 <= p * d <= 0xffff_ffff * 255) by (nonlinear_arith) requires 0 <= p <= 0xffff_ffff, 0 <= d <= 255;
        assert(0 <= p * t <= 0xffff_ffff * 255) by (nonlinear_arith) requires 0 <= p <= 0xffff_ffff, 0 <= t <= 255;
        assert(0 <= d * t <= 65025) by (nonlinear_arith) requires 0 <= d <= 255, 0 <= t <= 255;
        assert(0 <= p * (d * t) <= 0xffff_ffff * 65025) by (nonlinear_arith) requires 0 <= p <= 0xffff_ffff, 0 <= d * t <= 65025;
        assert(cpd(ps, ds)(j) == p * d && cpt(ps, ts)(j) == p * t && cdt(ds, ts)(j) == d * t && cpdt(ps, ds, ts)(j) == p * (d * t));
        lemma_csum_step(sel, one(), j);
        lemma_csum_step(sel, cqc(qs), j);
        lemma_csum_step(sel, cpc(ps), j);
        lemma_csum_step(sel, cpd(ps, ds), j);
        lemma_csum_step(sel, cpt(ps, ts), j);
        lemma_csum_step(sel, cpdt(ps, ds, ts), j);
        lemma_csum_step(sel, cdc(ds), j);
        lemma_csum_step(sel, ctc(ts), j);
        lemma_csum_step(sel, cdt(ds, ts), j);
        assert(m * (0xffff_ffff * 65025) == j * (0xffff_ffff * 65025) + 0xffff_ffff * 65025) by (nonlinear_arith) requires m == j + 1;
        assert(m * (0xffff_ffff * 255) == j * (0xffff_ffff * 255) + 0xffff_ffff * 255) by (nonlinear_arith) requires m == j + 1;
        assert(m * 0xffff_ffff == j * 0xffff_ffff + 0xffff_ffff) by (nonlinear_arith) requires m == j + 1;
        assert(m * 0xffff == j * 0xffff + 0xffff) by (nonlinear_arith) requires m == j + 1;
        assert(m * 65025 == j * 65025 + 65025) by (nonlinear_arith) requires m == j + 1;
        assert(m * 255 == j * 255 + 255) by (nonlinear_arith) requires m == j + 1;
    }
}

} // verus!
