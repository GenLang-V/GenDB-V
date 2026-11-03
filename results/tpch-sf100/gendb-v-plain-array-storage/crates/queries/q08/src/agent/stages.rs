//! The lineitem scan of a row range, block by block (`BLOCK` rows per worker task, `SBLK` rows on the serial path), in
//! stages over candidate lists:
//!
//! 1. the coarse filter (`stage1`): one L2-resident bit per lineitem row's part-key group; rows whose bit is clear
//!    cannot match; the candidates are recorded as `u32` offsets inside the block (`olist_ok`, `ocovers`): one
//!    4-byte store per row, the cheapest form of the scan's only per-row write;
//! 2. the exact part bit (`stage1b`) of the remaining rows (their keys re-read from the block, still in L1/L2), into
//!    absolute rows; when the matching parts are not positional, a linear search over the part table replaces both
//!    (`stage1_slow`, never taken on dbgen data);
//! 3. the order (`stage2`): its row by key, and its date inside the window;
//! 4. customer, nations, region, supplier and the totals (`stage3`, `acc::acc_step`).
//!
//! Every stage's output list is strictly increasing, inside the block, and contains every qualifying row of the
//! block (`list_ok`, `covers`); rows left out contribute nothing, so the totals of the listed rows are the
//! block's (`acc::lemma_acc_gap`). Every helper is `no_unwind` (worker bodies cannot unwind).
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::WorkerTask;
use crate::link::query::text_at;
use crate::agent::tables::*;
use crate::agent::line::*;
use crate::agent::cols::*;
use crate::agent::lookup::*;
use crate::agent::partpass::*;
use crate::agent::acc::*;
use crate::agent::common::bits::{bit, word_bit};
use crate::agent::common::text::{text_eq_at, tview};

verus! {

/// Rows per block of a worker task (its candidate buffers hold `BLOCK` entries each).
pub const BLOCK: usize = 4096;

/// Rows per block of the serial scan: larger blocks interleave the random lookups of stages 1b to 3 less often
/// with the stream of stage 1, while a block's keys (128 KiB) stay in L2 for stage 1b (one task, so its buffers are
/// allocated once).
pub const SBLK: usize = 16384;

/// The block sizes the scan supports (powers of two, so a candidate slot is masked into its buffer; below 2^32, so a
/// row's offset in its block is a `u32`).
pub open spec fn blk_ok(n: usize) -> bool { n == 4096 || n == 16384 }

// ------------------------------------------------------------------------------------------------ candidate lists

/// The first `n` entries of `s` are strictly increasing offsets of rows of `b..e` from `b`.
pub open spec fn olist_ok(s: Seq<u32>, n: int, b: int, e: int) -> bool {
    &&& 0 <= n <= s.len()
    &&& forall|x: int, y: int| 0 <= x < y < n ==> s[x] < s[y]
    &&& forall|x: int| 0 <= x < n ==> b + #[trigger] s[x] < e
}

/// Every qualifying row of `b..e` is `b` plus one of the first `n` offsets.
pub open spec fn ocovers(sv: StoresView, ps: Seq<Literal>, s: Seq<u32>, n: int, b: int, e: int) -> bool {
    forall|r: int| b <= r < e && #[trigger] line_q(sv, ps, r) ==> exists|x: int| 0 <= x < n && b + s[x] == r
}

/// The first `n` entries of `s` are strictly increasing rows of `b..e`.
pub open spec fn list_ok(s: Seq<usize>, n: int, b: int, e: int) -> bool {
    &&& 0 <= n <= s.len()
    &&& forall|x: int, y: int| 0 <= x < y < n ==> s[x] < s[y]
    &&& forall|x: int| 0 <= x < n ==> b <= #[trigger] s[x] < e
}

/// Every qualifying row of `b..e` is among the first `n` entries.
pub open spec fn covers(sv: StoresView, ps: Seq<Literal>, s: Seq<usize>, n: int, b: int, e: int) -> bool {
    forall|r: int| b <= r < e && #[trigger] line_q(sv, ps, r) ==> exists|x: int| 0 <= x < n && s[x] == r
}

/// Every listed row's part matches.
pub open spec fn all_part(sv: StoresView, ps: Seq<Literal>, s: Seq<usize>, n: int) -> bool {
    forall|x: int| 0 <= x < n ==> part_q(sv, ps, #[trigger] s[x] as int)
}

/// Every listed row's order row is in `ords`, with the row's key and a date inside the window.
pub open spec fn ords_ok(sv: StoresView, s: Seq<usize>, ords: Seq<usize>, n: int) -> bool {
    &&& n <= ords.len()
    &&& forall|x: int| 0 <= x < n ==> (#[trigger] ords[x]) < n_o(sv) && o_key(sv)[ords[x] as int] == l_okey(sv)[s[x] as int]
            && date_in(o_date(sv)[ords[x] as int])
}

// ------------------------------------------------------------------------------------------------ the part test

/// The part row a positional part key `k` names (`k - 1`), or `u64::MAX` for keys below 1.
pub open spec fn pidx(k: i64) -> u64 { if k >= 1 { (k - 1) as u64 } else { u64::MAX } }

/// With positional matches, a lineitem row's part matches exactly when the type bit of row `l_partkey - 1` is set
/// (`u` is `l_partkey - 1` as a wrapping `u64`), and then that row is the part.
proof fn lemma_part_bit(sv: StoresView, ps: Seq<Literal>, d: Dir, l: int, u: u64)
    requires
        dir_ok(d, sv, ps), d.pos, 0 <= l < n_l(sv), l_pkey(sv).len() == n_l(sv),
        u == pidx(l_pkey(sv)[l]),
    ensures
        part_q(sv, ps, l) <==> ((u as int) < n_p(sv) && word_bit(d.pbits@, u as int)),
        (u as int) < n_p(sv) && word_bit(d.pbits@, u as int) ==> part_hit(sv, ps, u as int, l),
{
    let k = l_pkey(sv)[l];
    let typ = typ_of(ps);
    if (u as int) < n_p(sv) && word_bit(d.pbits@, u as int) {
        assert(p_type(sv, u as int) == typ);
        assert(p_key(sv)[u as int] as int == u + 1);
        assert(u as int == k - 1);
        assert(part_hit(sv, ps, u as int, l));
    }
    if part_q(sv, ps, l) {
        let p = choose|p: int| 0 <= p < n_p(sv) && #[trigger] part_hit(sv, ps, p, l);
        assert(p_key(sv)[p] as int == p + 1);
        assert(u as int == p);
    }
}

/// A word's bit test as `0` or `1`.
pub proof fn lemma_bit01(x: u64, s: u64)
    ensures (x >> s) & 1 <= 1, ((x >> s) & 1 == 1) == bit(x, s),
{
    assert((x >> s) & 1 <= 1) by (bit_vector);
}

/// A clear coarse bit of the key's group excludes the row.
proof fn lemma_coarse_miss(sv: StoresView, ps: Seq<Literal>, d: Dir, l: int)
    requires
        dir_ok(d, sv, ps), d.pos, 0 <= l < n_l(sv), l_pkey(sv).len() == n_l(sv),
        l_pkey(sv)[l] >= 1 ==> !word_bit((*d.coarse)@, khash(l_pkey(sv)[l] as int)),
    ensures !line_q(sv, ps, l),
{
    if line_q(sv, ps, l) {
        lemma_q_part(sv, ps, l);
        let p = choose|p: int| 0 <= p < n_p(sv) && #[trigger] part_hit(sv, ps, p, l);
        assert(p_type(sv, p) == typ_of(ps));
        assert(p_key(sv)[p] as int == p + 1);
        assert(word_bit(d.pbits@, p));
    }
}

/// The candidate slot `n & (cap - 1)` is `n` below `cap`.
proof fn lemma_slot(n: usize, cap: usize)
    requires n < cap, blk_ok(cap),
    ensures n & sub(cap, 1) == n,
{
    if cap == 4096 {
        assert(n < 4096 ==> n & 4095usize == n) by (bit_vector);
    } else {
        assert(n < 16384 ==> n & 16383usize == n) by (bit_vector);
    }
}

// ------------------------------------------------------------------------------------------------ stages

/// Stage 1: the coarse filter over the rows `b..e` (offsets into `out`).
#[inline(never)]
pub fn stage1<const N: usize>(c: &Cols, d: &Dir, b: usize, e: usize, out: &mut [u32; N],
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (n: usize)
    requires scan_ok(*c, *d, sv, ps), d.pos, b <= e <= c.nl, e - b <= N, blk_ok(N),
    ensures
        olist_ok(final(out)@, n as int, b as int, e as int),
        ocovers(sv, ps, final(out)@, n as int, b as int, e as int),
    no_unwind
{
    let len = e - b;
    let coarse: &[u64; CW] = &d.coarse;
    let (_, tail) = c.l_pk.split_at(b);
    let (blk, _) = tail.split_at(len);
    let mut n: usize = 0;
    let mut j: usize = 0;
    while j < len
        invariant
            scan_ok(*c, *d, sv, ps), d.pos, b <= e <= c.nl, len == e - b, len <= N, blk_ok(N),
            coarse@ == (*d.coarse)@,
            blk@ == l_pkey(sv).subrange(b as int, e as int),
            out@.len() == N, n <= j <= len,
            olist_ok(out@, n as int, b as int, (b + j) as int),
            ocovers(sv, ps, out@, n as int, b as int, (b + j) as int),
        decreases len - j,
    {
        let k = blk[j];
        let x = k as u64;
        proof { lemma_key_group(x); }
        let g = (x >> 3) & GMASK;
        let w = coarse[(g >> 6) as usize];
        proof { lemma_bit01(w, g & 63); }
        let f = ((w >> (g & 63)) & 1) as usize;
        let ghost out0 = out@;
        proof { lemma_slot(n, N); }
        out[n & (N - 1)] = j as u32;
        proof {
            let r = (b + j) as int;
            assert(k == l_pkey(sv)[r]);
            assert((j as u32) as int == j);
            if f == 0 {
                if k >= 1 {
                    assert(x as int == k as int);
                    assert(!word_bit((*d.coarse)@, khash(k as int)));
                }
                lemma_coarse_miss(sv, ps, *d, r);
            }
            assert forall|y: int| 0 <= y < n implies out@[y] == out0[y] by {}
            assert forall|rr: int| b <= rr < b + j + 1 && #[trigger] line_q(sv, ps, rr)
                implies exists|y: int| 0 <= y < n + f && b + out@[y] == rr by {
                if rr < b + j {
                    let y = choose|y: int| 0 <= y < n && b + out0[y] == rr;
                    assert(out@[y] == out0[y]);
                } else {
                    assert(b + out@[n as int] == rr);
                }
            }
        }
        n = n + f;
        j = j + 1;
    }
    n
}

/// Stage 1 over two blocks of equal length at once (`b..m` into `oa`, `m..e` into `ob`): two independent streams of
/// `l_partkey`, which keeps more memory requests in flight on one core.
#[inline(never)]
pub fn stage1x2<const N: usize>(c: &Cols, d: &Dir, b: usize, m: usize, e: usize, oa: &mut [u32; N],
    ob: &mut [u32; N], Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: (usize, usize))
    requires scan_ok(*c, *d, sv, ps), d.pos, b <= m <= e <= c.nl, m - b <= N, e - m == m - b, blk_ok(N),
    ensures
        olist_ok(final(oa)@, r.0 as int, b as int, m as int),
        ocovers(sv, ps, final(oa)@, r.0 as int, b as int, m as int),
        olist_ok(final(ob)@, r.1 as int, m as int, e as int),
        ocovers(sv, ps, final(ob)@, r.1 as int, m as int, e as int),
    no_unwind
{
    let len = m - b;
    let coarse: &[u64; CW] = &d.coarse;
    let (_, tail) = c.l_pk.split_at(b);
    let (blka, rest) = tail.split_at(len);
    let (blkb, _) = rest.split_at(len);
    let mut na: usize = 0;
    let mut nb: usize = 0;
    let mut j: usize = 0;
    while j < len
        invariant
            scan_ok(*c, *d, sv, ps), d.pos, b <= m <= e <= c.nl, len == m - b, e - m == len, len <= N, blk_ok(N),
            coarse@ == (*d.coarse)@,
            blka@ == l_pkey(sv).subrange(b as int, m as int),
            blkb@ == l_pkey(sv).subrange(m as int, e as int),
            oa@.len() == N, ob@.len() == N, na <= j <= len, nb <= j,
            olist_ok(oa@, na as int, b as int, (b + j) as int),
            ocovers(sv, ps, oa@, na as int, b as int, (b + j) as int),
            olist_ok(ob@, nb as int, m as int, (m + j) as int),
            ocovers(sv, ps, ob@, nb as int, m as int, (m + j) as int),
        decreases len - j,
    {
        let kva = blka[j];
        let kvb = blkb[j];
        let xa = kva as u64;
        let xb = kvb as u64;
        proof { lemma_key_group(xa); lemma_key_group(xb); }
        let ga = (xa >> 3) & GMASK;
        let gb = (xb >> 3) & GMASK;
        let wa = coarse[(ga >> 6) as usize];
        let wb = coarse[(gb >> 6) as usize];
        proof { lemma_bit01(wa, ga & 63); lemma_bit01(wb, gb & 63); }
        let fa = ((wa >> (ga & 63)) & 1) as usize;
        let fb = ((wb >> (gb & 63)) & 1) as usize;
        let ghost oa0 = oa@;
        let ghost ob0 = ob@;
        proof { lemma_slot(na, N); lemma_slot(nb, N); }
        oa[na & (N - 1)] = j as u32;
        ob[nb & (N - 1)] = j as u32;
        proof {
            let ra = (b + j) as int;
            let rb = (m + j) as int;
            assert(kva == l_pkey(sv)[ra] && kvb == l_pkey(sv)[rb]);
            assert((j as u32) as int == j);
            if fa == 0 {
                if kva >= 1 {
                    assert(xa as int == kva as int);
                    assert(!word_bit((*d.coarse)@, khash(kva as int)));
                }
                lemma_coarse_miss(sv, ps, *d, ra);
            }
            if fb == 0 {
                if kvb >= 1 {
                    assert(xb as int == kvb as int);
                    assert(!word_bit((*d.coarse)@, khash(kvb as int)));
                }
                lemma_coarse_miss(sv, ps, *d, rb);
            }
            assert forall|y: int| 0 <= y < na implies oa@[y] == oa0[y] by {}
            assert forall|y: int| 0 <= y < nb implies ob@[y] == ob0[y] by {}
            assert forall|rr: int| b <= rr < b + j + 1 && #[trigger] line_q(sv, ps, rr)
                implies exists|y: int| 0 <= y < na + fa && b + oa@[y] == rr by {
                if rr < b + j {
                    let y = choose|y: int| 0 <= y < na && b + oa0[y] == rr;
                    assert(oa@[y] == oa0[y]);
                } else {
                    assert(b + oa@[na as int] == rr);
                }
            }
            assert forall|rr: int| m <= rr < m + j + 1 && #[trigger] line_q(sv, ps, rr)
                implies exists|y: int| 0 <= y < nb + fb && m + ob@[y] == rr by {
                if rr < m + j {
                    let y = choose|y: int| 0 <= y < nb && m + ob0[y] == rr;
                    assert(ob@[y] == ob0[y]);
                } else {
                    assert(m + ob@[nb as int] == rr);
                }
            }
        }
        na = na + fa;
        nb = nb + fb;
        j = j + 1;
    }
    (na, nb)
}

/// Stages 1b to 3 of one block whose stage-1 offsets are `l1` (`n1` entries); `bx`, `by`, `bz` are scratch.
fn finish_block<const N: usize>(c: &Cols, d: &Dir, l1: &[u32; N], n1: usize, b: usize, e: usize,
    bx: &mut [usize; N], by: &mut [usize; N], bz: &mut [usize; N], acc0: Acc, Ghost(sv): Ghost<StoresView>,
    Ghost(ps): Ghost<Seq<Literal>>, Ghost(lo): Ghost<int>) -> (acc: Acc)
    requires
        scan_ok(*c, *d, sv, ps), d.pos, 0 <= lo <= b, b <= e <= c.nl, acc_ok(acc0, sv, ps, lo, b as int),
        olist_ok(l1@, n1 as int, b as int, e as int), ocovers(sv, ps, l1@, n1 as int, b as int, e as int),
    ensures acc_ok(acc, sv, ps, lo, e as int),
    no_unwind
{
    let n2 = stage1b(c, d, l1, n1, b, e, bx, Ghost(sv), Ghost(ps));
    let m = stage2(c, bx, n2, b, e, by, bz, Ghost(sv), Ghost(ps));
    stage3(c, d, by, bz, m, b, e, acc0, Ghost(sv), Ghost(ps), Ghost(lo))
}

/// Stage 1b: the exact part bit of the rows `b + inp[t]` (absolute rows into `out`).
pub fn stage1b<const N: usize>(c: &Cols, d: &Dir, inp: &[u32; N], n1: usize, b: usize, e: usize,
    out: &mut [usize; N], Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (n: usize)
    requires
        scan_ok(*c, *d, sv, ps), d.pos, b <= e <= c.nl,
        olist_ok(inp@, n1 as int, b as int, e as int), ocovers(sv, ps, inp@, n1 as int, b as int, e as int),
    ensures
        list_ok(final(out)@, n as int, b as int, e as int),
        covers(sv, ps, final(out)@, n as int, b as int, e as int),
        all_part(sv, ps, final(out)@, n as int),
    no_unwind
{
    let np = c.np as u64;
    let mut n: usize = 0;
    let mut t: usize = 0;
    while t < n1
        invariant
            scan_ok(*c, *d, sv, ps), d.pos, b <= e <= c.nl, np == c.np,
            olist_ok(inp@, n1 as int, b as int, e as int), ocovers(sv, ps, inp@, n1 as int, b as int, e as int),
            n1 <= N, out@.len() == N, n <= t <= n1,
            list_ok(out@, n as int, b as int, e as int),
            forall|x: int| 0 <= x < n ==> exists|y: int| 0 <= y < t && #[trigger] out@[x] == b + inp@[y],
            forall|r: int| b <= r < e && #[trigger] line_q(sv, ps, r) ==>
                (exists|x: int| 0 <= x < n && out@[x] == r) || (exists|y: int| t <= y < n1 && b + inp@[y] == r),
            all_part(sv, ps, out@, n as int),
        decreases n1 - t,
    {
        let i = b + inp[t] as usize;
        let k = c.l_pk[i];
        assert(k == l_pkey(sv)[i as int]);
        let u: u64 = if k >= 1 { (k - 1) as u64 } else { u64::MAX };
        let f: usize = if u < np {
            proof {
                assert((u >> 6) == u / 64 && (u & 63) == u % 64 && (u & 63) < 64) by (bit_vector);
                assert((u as int) / 64 < d.pbits@.len());
            }
            let w = d.pbits[(u >> 6) as usize];
            proof {
                assert(word_bit(d.pbits@, u as int) == bit(w, u & 63));
                lemma_bit01(w, u & 63);
            }
            ((w >> (u & 63)) & 1) as usize
        } else {
            0
        };
        proof {
            lemma_part_bit(sv, ps, *d, i as int, u);
        }
        let ghost out0 = out@;
        out[n] = i;
        proof {
            assert forall|x: int| 0 <= x < n implies out@[x] == out0[x] by {}
            if f == 1 {
                assert forall|x: int| 0 <= x < n implies out@[x] < i by {
                    let y = choose|y: int| 0 <= y < t && #[trigger] out0[x] == b + inp@[y];
                    assert(inp@[y] < inp@[t as int]);
                }
                assert(part_q(sv, ps, i as int)) by {
                    assert(part_hit(sv, ps, u as int, i as int));
                }
            } else {
                assert(!part_q(sv, ps, i as int));
                if line_q(sv, ps, i as int) { lemma_q_part(sv, ps, i as int); }
            }
            assert forall|x: int| 0 <= x < n + f implies exists|y: int| 0 <= y < t + 1 && #[trigger] out@[x] == b + inp@[y] by {
                if x < n {
                    let y = choose|y: int| 0 <= y < t && #[trigger] out0[x] == b + inp@[y];
                    assert(out@[x] == b + inp@[y]);
                } else {
                    assert(out@[x] == b + inp@[t as int]);
                }
            }
            assert forall|r: int| b <= r < e && #[trigger] line_q(sv, ps, r) implies
                (exists|x: int| 0 <= x < n + f && out@[x] == r) || (exists|y: int| t + 1 <= y < n1 && b + inp@[y] == r) by {
                if exists|x: int| 0 <= x < n && out0[x] == r {
                    let x = choose|x: int| 0 <= x < n && out0[x] == r;
                    assert(out@[x] == r);
                } else {
                    let y = choose|y: int| t <= y < n1 && b + inp@[y] == r;
                    if y == t {
                        assert(out@[n as int] == r);
                    }
                }
            }
        }
        n = n + f;
        t = t + 1;
    }
    n
}

/// Some part row of key `k` has type `$3` (a search over the part table).
fn part_q_slow(c: &Cols, k: i64, pat: &[u8], plen: usize, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: bool)
    requires cols_ok(*c, sv), pat@ == typ_of(ps), plen == pat@.len(),
    ensures r == exists|p: int| 0 <= p < n_p(sv) && p_key(sv)[p] == k && #[trigger] p_type(sv, p) == typ_of(ps),
    no_unwind
{
    let mut p: usize = 0;
    while p < c.np
        invariant
            cols_ok(*c, sv), pat@ == typ_of(ps), plen == pat@.len(), p <= c.np,
            forall|x: int| 0 <= x < p ==> !(p_key(sv)[x] == k && #[trigger] p_type(sv, x) == typ_of(ps)),
        decreases c.np - p,
    {
        if c.p_key[p] == k {
            let eq = text_eq_at(c.p_toffs, c.p_tbytes, c.p_tnb, p, pat, plen, Ghost(n_p(sv) as int));
            if eq {
                assert(p_type(sv, p as int) == typ_of(ps));
                return true;
            }
        }
        p = p + 1;
    }
    false
}

/// Stage 1 without positional matches: the rows of `b..e` whose part matches, by search (into `out`).
pub fn stage1_slow<const N: usize>(c: &Cols, pat: &[u8], plen: usize, b: usize, e: usize, out: &mut [usize; N], Ghost(sv): Ghost<StoresView>,
    Ghost(ps): Ghost<Seq<Literal>>) -> (n: usize)
    requires cols_ok(*c, sv), pat@ == typ_of(ps), plen == pat@.len(), b <= e <= c.nl, e - b <= old(out)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        list_ok(final(out)@, n as int, b as int, e as int),
        covers(sv, ps, final(out)@, n as int, b as int, e as int),
        all_part(sv, ps, final(out)@, n as int),
    no_unwind
{
    let ghost olen = out@.len();
    let mut n: usize = 0;
    let mut r: usize = b;
    while r < e
        invariant
            cols_ok(*c, sv), pat@ == typ_of(ps), plen == pat@.len(), b <= r <= e <= c.nl, e - b <= olen,
            out@.len() == olen, n <= r - b,
            list_ok(out@, n as int, b as int, r as int),
            covers(sv, ps, out@, n as int, b as int, r as int),
            all_part(sv, ps, out@, n as int),
        decreases e - r,
    {
        let hitp = part_q_slow(c, c.l_pk[r], pat, plen, Ghost(sv), Ghost(ps));
        let ghost out0 = out@;
        if hitp {
            out[n] = r;
            proof {
                let p = choose|p: int| 0 <= p < n_p(sv) && p_key(sv)[p] == l_pkey(sv)[r as int] && #[trigger] p_type(sv, p) == typ_of(ps);
                assert(part_hit(sv, ps, p, r as int));
                assert forall|x: int| 0 <= x < n implies out@[x] == out0[x] by {}
                assert forall|rr: int| b <= rr < r + 1 && #[trigger] line_q(sv, ps, rr)
                    implies exists|x: int| 0 <= x < n + 1 && out@[x] == rr by {
                    if rr < r {
                        let x = choose|x: int| 0 <= x < n && out0[x] == rr;
                        assert(out@[x] == rr);
                    } else {
                        assert(out@[n as int] == rr);
                    }
                }
            }
            n = n + 1;
        } else {
            proof {
                if line_q(sv, ps, r as int) {
                    lemma_q_part(sv, ps, r as int);
                    let p = choose|p: int| 0 <= p < n_p(sv) && #[trigger] part_hit(sv, ps, p, r as int);
                    assert(p_key(sv)[p] == l_pkey(sv)[r as int] && p_type(sv, p) == typ_of(ps));
                }
            }
        }
        r = r + 1;
    }
    n
}

/// Stage 2: the listed rows whose order exists and is dated inside the window (rows into `rows`, order rows into
/// `ords`).
pub fn stage2<const N: usize>(c: &Cols, inp: &[usize; N], n2: usize, b: usize, e: usize, rows: &mut [usize; N], ords: &mut [usize; N],
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (m: usize)
    requires
        cols_ok(*c, sv), keys_ok(sv), b <= e <= c.nl,
        list_ok(inp@, n2 as int, b as int, e as int), covers(sv, ps, inp@, n2 as int, b as int, e as int),
        all_part(sv, ps, inp@, n2 as int),
        n2 <= old(rows)@.len(), n2 <= old(ords)@.len(),
    ensures
        final(rows)@.len() == old(rows)@.len(), final(ords)@.len() == old(ords)@.len(),
        list_ok(final(rows)@, m as int, b as int, e as int),
        covers(sv, ps, final(rows)@, m as int, b as int, e as int),
        all_part(sv, ps, final(rows)@, m as int),
        ords_ok(sv, final(rows)@, final(ords)@, m as int),
    no_unwind
{
    let ghost rlen = rows@.len();
    let ghost olen = ords@.len();
    let mut m: usize = 0;
    let mut t: usize = 0;
    while t < n2
        invariant
            cols_ok(*c, sv), keys_ok(sv), b <= e <= c.nl,
            list_ok(inp@, n2 as int, b as int, e as int), covers(sv, ps, inp@, n2 as int, b as int, e as int),
            all_part(sv, ps, inp@, n2 as int),
            n2 <= rlen, n2 <= olen, rows@.len() == rlen, ords@.len() == olen, m <= t <= n2,
            list_ok(rows@, m as int, b as int, e as int),
            forall|x: int| 0 <= x < m ==> exists|y: int| 0 <= y < t && #[trigger] rows@[x] == inp@[y],
            forall|r: int| b <= r < e && #[trigger] line_q(sv, ps, r) ==>
                (exists|x: int| 0 <= x < m && rows@[x] == r) || (exists|y: int| t <= y < n2 && inp@[y] == r),
            all_part(sv, ps, rows@, m as int),
            ords_ok(sv, rows@, ords@, m as int),
        decreases n2 - t,
    {
        let i = inp[t];
        let ghost rows0 = rows@;
        let ghost ords0 = ords@;
        let found = order_row(c, c.l_ok[i], Ghost(sv));
        let keep = match found {
            Some(j) => {
                let d = c.o_date[j];
                if 9131 <= d && d <= 9861 {
                    rows[m] = i;
                    ords[m] = j;
                    true
                } else {
                    proof {
                        if line_q(sv, ps, i as int) {
                            let tp = line_tup(sv, ps, i as int);
                            assert(tup_ok(sv, ps, i as int, tp));
                            assert(o_key(sv)[tp.o] == o_key(sv)[j as int]);
                        }
                    }
                    false
                }
            },
            None => {
                proof {
                    if line_q(sv, ps, i as int) {
                        let tp = line_tup(sv, ps, i as int);
                        assert(tup_ok(sv, ps, i as int, tp));
                    }
                }
                false
            },
        };
        proof {
            if keep {
                assert forall|x: int| 0 <= x < m implies rows@[x] < i by {
                    let y = choose|y: int| 0 <= y < t && #[trigger] rows0[x] == inp@[y];
                    assert(rows@[x] == rows0[x]);
                }
                assert forall|x: int| 0 <= x < m + 1 implies exists|y: int| 0 <= y < t + 1 && #[trigger] rows@[x] == inp@[y] by {
                    if x < m {
                        let y = choose|y: int| 0 <= y < t && #[trigger] rows0[x] == inp@[y];
                        assert(rows@[x] == inp@[y]);
                    } else {
                        assert(rows@[x] == inp@[t as int]);
                    }
                }
                assert forall|r: int| b <= r < e && #[trigger] line_q(sv, ps, r) implies
                    (exists|x: int| 0 <= x < m + 1 && rows@[x] == r) || (exists|y: int| t + 1 <= y < n2 && inp@[y] == r) by {
                    if exists|x: int| 0 <= x < m && rows0[x] == r {
                        let x = choose|x: int| 0 <= x < m && rows0[x] == r;
                        assert(rows@[x] == r);
                    } else {
                        let y = choose|y: int| t <= y < n2 && inp@[y] == r;
                        if y == t {
                            assert(rows@[m as int] == r);
                        }
                    }
                }
                assert(all_part(sv, ps, rows@, m + 1)) by {
                    assert forall|x: int| 0 <= x < m + 1 implies part_q(sv, ps, #[trigger] rows@[x] as int) by {
                        if x < m { assert(rows@[x] == rows0[x]); } else { assert(rows@[x] == inp@[t as int]); }
                    }
                }
                assert(ords_ok(sv, rows@, ords@, m + 1)) by {
                    assert forall|x: int| 0 <= x < m + 1 implies (#[trigger] ords@[x]) < n_o(sv)
                        && o_key(sv)[ords@[x] as int] == l_okey(sv)[rows@[x] as int] && date_in(o_date(sv)[ords@[x] as int]) by {
                        if x < m { assert(rows@[x] == rows0[x] && ords@[x] == ords0[x]); }
                    }
                }
            } else {
                assert forall|r: int| b <= r < e && #[trigger] line_q(sv, ps, r) implies
                    (exists|x: int| 0 <= x < m && rows@[x] == r) || (exists|y: int| t + 1 <= y < n2 && inp@[y] == r) by {
                    if !(exists|x: int| 0 <= x < m && rows0[x] == r) {
                        let y = choose|y: int| t <= y < n2 && inp@[y] == r;
                        assert(y != t);
                    }
                }
            }
        }
        if keep {
            m = m + 1;
        }
        t = t + 1;
    }
    m
}

/// Stage 3: the totals of the rows `lo..e` from those of `lo..b` and the listed rows of `b..e`.
pub fn stage3<const N: usize>(c: &Cols, d: &Dir, rows: &[usize; N], ords: &[usize; N], m: usize, b: usize, e: usize, acc0: Acc,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(lo): Ghost<int>) -> (acc: Acc)
    requires
        scan_ok(*c, *d, sv, ps), 0 <= lo <= b, b <= e <= c.nl, acc_ok(acc0, sv, ps, lo, b as int),
        list_ok(rows@, m as int, b as int, e as int), covers(sv, ps, rows@, m as int, b as int, e as int),
        all_part(sv, ps, rows@, m as int), ords_ok(sv, rows@, ords@, m as int),
    ensures acc_ok(acc, sv, ps, lo, e as int),
    no_unwind
{
    let mut acc = acc0;
    let mut t: usize = 0;
    let ghost mut p: int = b as int;
    while t < m
        invariant
            scan_ok(*c, *d, sv, ps), 0 <= lo <= b, b <= e <= c.nl,
            list_ok(rows@, m as int, b as int, e as int), covers(sv, ps, rows@, m as int, b as int, e as int),
            all_part(sv, ps, rows@, m as int), ords_ok(sv, rows@, ords@, m as int),
            t <= m, b <= p <= e, acc_ok(acc, sv, ps, lo, p),
            t == 0 ==> p == b,
            t > 0 ==> p == rows@[t - 1] + 1,
        decreases m - t,
    {
        let i = rows[t];
        let j = ords[t];
        proof {
            assert(p <= i) by {
                if t > 0 { assert(rows@[t - 1] < rows@[t as int]); }
            }
            assert forall|r: int| p <= r < i implies !#[trigger] line_q(sv, ps, r) by {
                if line_q(sv, ps, r) {
                    let x = choose|x: int| 0 <= x < m && rows@[x] == r;
                    if x < t {
                        if x < t - 1 { assert(rows@[x] < rows@[t - 1]); }
                    } else if x > t {
                        assert(rows@[t as int] < rows@[x]);
                    }
                }
            }
            lemma_acc_gap(acc, sv, ps, lo, p, i as int);
        }
        acc = acc_step(acc, c, d, i, j, Ghost(sv), Ghost(ps), Ghost(lo));
        proof { p = i + 1; }
        t = t + 1;
    }
    proof {
        assert forall|r: int| p <= r < e implies !#[trigger] line_q(sv, ps, r) by {
            if line_q(sv, ps, r) {
                let x = choose|x: int| 0 <= x < m && rows@[x] == r;
                if m > 0 && x < m - 1 { assert(rows@[x] < rows@[m - 1]); }
            }
        }
        lemma_acc_gap(acc, sv, ps, lo, p, e as int);
    }
    acc
}

// ------------------------------------------------------------------------------------------------ a range

/// The totals of the lineitem rows `lo..hi`, block by block (`u1`, `u2`: stage-1 offset buffers; `b3`, `b4`, `b5`: row
/// buffers; `N` entries each).
pub fn scan_range<const N: usize>(c: &Cols, d: &Dir, pat: &[u8], plen: usize, lo: usize, hi: usize,
    u1: &mut [u32; N], u2: &mut [u32; N], b3: &mut [usize; N], b4: &mut [usize; N], b5: &mut [usize; N],
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (acc: Acc)
    requires
        scan_ok(*c, *d, sv, ps), lo <= hi <= c.nl, pat@ == typ_of(ps), plen == pat@.len(), blk_ok(N),
    ensures acc_ok(acc, sv, ps, lo as int, hi as int),
    no_unwind
{
    let mut acc = acc_zero(Ghost(sv), Ghost(ps), Ghost(lo as int));
    let mut b = lo;
    // pairs of blocks: two streams at once
    if d.pos {
        while hi - b >= 2 * N
            invariant
                scan_ok(*c, *d, sv, ps), d.pos, lo <= b <= hi <= c.nl, blk_ok(N),
                acc_ok(acc, sv, ps, lo as int, b as int),
            decreases hi - b,
        {
            let m = b + N;
            let e = m + N;
            let (na, nb) = stage1x2(c, d, b, m, e, u1, u2, Ghost(sv), Ghost(ps));
            acc = finish_block(c, d, u1, na, b, m, b3, b4, b5, acc, Ghost(sv), Ghost(ps), Ghost(lo as int));
            acc = finish_block(c, d, u2, nb, m, e, b3, b4, b5, acc, Ghost(sv), Ghost(ps), Ghost(lo as int));
            b = e;
        }
    }
    while b < hi
        invariant
            scan_ok(*c, *d, sv, ps), lo <= b <= hi <= c.nl, pat@ == typ_of(ps), plen == pat@.len(), blk_ok(N),
            acc_ok(acc, sv, ps, lo as int, b as int),
        decreases hi - b,
    {
        let e = if hi - b > N { b + N } else { hi };
        let n2 = if d.pos {
            let n1 = stage1(c, d, b, e, u1, Ghost(sv), Ghost(ps));
            stage1b(c, d, u1, n1, b, e, b3, Ghost(sv), Ghost(ps))
        } else {
            stage1_slow(c, pat, plen, b, e, b3, Ghost(sv), Ghost(ps))
        };
        let m = stage2(c, b3, n2, b, e, b4, b5, Ghost(sv), Ghost(ps));
        acc = stage3(c, d, b4, b5, m, b, e, acc, Ghost(sv), Ghost(ps), Ghost(lo as int));
        b = e;
    }
    acc
}

/// One worker task: the totals of the lineitem rows `lo..hi`.
pub struct LineTask {
    pub cols: Cols,
    pub dir: Arc<Dir>,
    pub pat: &'static [u8],
    pub plen: usize,
    pub lo: usize,
    pub hi: usize,
    pub u1: Box<[u32; BLOCK]>,
    pub u2: Box<[u32; BLOCK]>,
    pub b3: Box<[usize; BLOCK]>,
    pub b4: Box<[usize; BLOCK]>,
    pub b5: Box<[usize; BLOCK]>,
    pub sv: Ghost<StoresView>,
    pub ps: Ghost<Seq<Literal>>,
}

impl WorkerTask for LineTask {
    type Output = Acc;

    open spec fn pre(&self) -> bool {
        &&& scan_ok(self.cols, *self.dir, self.sv@, self.ps@)
        &&& self.lo <= self.hi <= self.cols.nl
        &&& self.pat@ == typ_of(self.ps@) && self.plen == self.pat@.len()
    }

    open spec fn post(&self, out: Acc) -> bool {
        acc_ok(out, self.sv@, self.ps@, self.lo as int, self.hi as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: Acc) {
        let d: &Dir = &*self.dir;
        let mut u1 = self.u1;
        let mut u2 = self.u2;
        let mut b3 = self.b3;
        let mut b4 = self.b4;
        let mut b5 = self.b5;
        scan_range(&self.cols, d, self.pat, self.plen, self.lo, self.hi, &mut *u1, &mut *u2, &mut *b3, &mut *b4, &mut *b5,
            self.sv, self.ps)
    }
}

} // verus!
