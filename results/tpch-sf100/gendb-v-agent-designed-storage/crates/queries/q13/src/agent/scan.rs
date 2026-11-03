//! Phase 1 over the orders rows (canonical order), in worker tasks over row ranges `[a, b)` (`ScanTask`). Each row
//! gets a flag (`rflag`): `FLAG_NO` when its 128-bit trigram signature misses a bit the pattern needs (the row
//! cannot match) or the matcher answers no; `FLAG_LIKE` when it matches; `FLAG_DEFER` when it is a candidate whose
//! text is not ASCII (decided later on the calling thread with the general evaluator); `FLAG_ERR` when the matcher
//! raises. The task returns the o_custkey of its `FLAG_LIKE` rows in row order (`lkeys`, read from storage `facts`
//! through its orders key index: canonical row `r` is stored row `srow(r)`), its `FLAG_DEFER` rows (`drows`) and
//! the number of its `FLAG_ERR` rows (`nerr`). Outputs go into buffers allocated on the calling thread with one
//! slot per row (lazily zeroed pages: only the used prefix is touched). When its key buffer has room, a gathering
//! task finally reorders its keys into the segments of the phase-2 key ranges `[blo[t], bhi[t])`
//! (`common::partition`), so each phase-2 task reads only its own segment of every list (`seg_post`).
//!
//! The signature test reads the bit-sliced signatures (`sl_ok`: plane `q` of half `h` holds bit `q` of signature
//! word `h` of every row, 64 rows per word): per word of 64 rows, the AND of the planes of the needed bits `pq`
//! (`cand_word`) has a clear bit for every row it rejects (`mask_ok`), so only those planes are read, never the
//! per-row signature words.
use vstd::prelude::*;
use crate::gendb_entry::parallel::WorkerTask;
use crate::gendb_entry::work::put;
use crate::spec::value::*;
use crate::spec::fns::like::*;
use crate::stores::factext_trislice::interface::common::colfmt::text_of;
use crate::stores::factext_trislice::interface::{bit_at, slice_bit, sig_bit};
use super::like::*;
use super::common::partition::*;

verus! {

/// The row does not match.
pub const FLAG_NO: u8 = 0;
/// The row matches.
pub const FLAG_LIKE: u8 = 1;
/// A candidate with non-ASCII text, decided on the calling thread.
pub const FLAG_DEFER: u8 = 2;
/// The matcher raised an error on the row.
pub const FLAG_ERR: u8 = 3;

/// The column views phase 1 reads, and the pattern.
pub struct ScanCtx {
    /// Signatures, two words per row.
    pub sig: Seq<u64>,
    /// o_comment offsets and bytes.
    pub offs: Seq<u64>,
    pub bytes: Seq<u8>,
    /// Pattern codes and tokens, needed signature bits.
    pub codes: Seq<u16>,
    pub p: Seq<LikeTok>,
    pub need0: u64,
    pub need1: u64,
    /// facts: key index of orders (canonical row -> stored row) and o_custkey (FOR codes and bases).
    pub ic: Seq<u32>,
    pub ib: Seq<u64>,
    pub kc: Seq<u32>,
    pub kb: Seq<i64>,
    pub bs: int,
}

/// The group `i / bs` of row `i`; the usual group size 65536 divides by a constant (a shift), not a runtime divisor.
#[inline(always)]
pub fn grp(i: usize, bs: usize) -> (g: usize)
    requires bs >= 1,
    ensures g == i / bs,
    no_unwind
{
    if bs == 65536 { i / 65536 } else { i / bs }
}

/// Text of row `r`.
pub open spec fn rtext(x: ScanCtx, r: int) -> Seq<u8> {
    text_of(x.offs, x.bytes, r)
}

/// The phase-1 flag of row `r`.
pub open spec fn rflag(x: ScanCtx, r: int) -> u8 {
    if rejects(x.sig[2 * r], x.sig[2 * r + 1], x.need0, x.need1) {
        FLAG_NO
    } else if !is_ascii(rtext(x, r)) {
        FLAG_DEFER
    } else {
        match like_mt(byte_chars(rtext(x, r)), x.p, 0, 0) {
            Ok(LikeRes::Match) => FLAG_LIKE,
            Ok(_) => FLAG_NO,
            Err(_) => FLAG_ERR,
        }
    }
}

/// Canonical orders row `r` is stored row `ib[r / bs] + ic[r]` of storage facts.
pub open spec fn srow(x: ScanCtx, r: int) -> int {
    x.ib[r / x.bs] + x.ic[r]
}

/// The o_custkey of canonical row `r`.
pub open spec fn okey(x: ScanCtx, r: int) -> int {
    x.kb[srow(x, r) / x.bs] + x.kc[srow(x, r)]
}

/// The keys of the `FLAG_LIKE` rows among `a .. m`, in row order.
pub open spec fn lkeys(x: ScanCtx, a: int, m: int) -> Seq<i64>
    decreases m - a,
{
    if m <= a {
        Seq::empty()
    } else {
        let init = lkeys(x, a, m - 1);
        if rflag(x, m - 1) == FLAG_LIKE { init.push(okey(x, m - 1) as i64) } else { init }
    }
}

/// The `FLAG_LIKE` rows among `a .. m`, in row order.
pub open spec fn lrows(x: ScanCtx, a: int, m: int) -> Seq<usize>
    decreases m - a,
{
    if m <= a {
        Seq::empty()
    } else {
        let init = lrows(x, a, m - 1);
        if rflag(x, m - 1) == FLAG_LIKE { init.push((m - 1) as usize) } else { init }
    }
}

/// The `FLAG_DEFER` rows among `a .. m`, in row order.
pub open spec fn drows(x: ScanCtx, a: int, m: int) -> Seq<usize>
    decreases m - a,
{
    if m <= a {
        Seq::empty()
    } else {
        let init = drows(x, a, m - 1);
        if rflag(x, m - 1) == FLAG_DEFER { init.push((m - 1) as usize) } else { init }
    }
}

/// The number of `FLAG_ERR` rows among `a .. m`.
pub open spec fn nerr(x: ScanCtx, a: int, m: int) -> nat
    decreases m - a,
{
    if m <= a { 0 } else { nerr(x, a, m - 1) + if rflag(x, m - 1) == FLAG_ERR { 1nat } else { 0nat } }
}

/// The facts the task reads, over the rows `0 .. n` (the key columns only when it gathers keys).
pub open spec fn ctx_ok(x: ScanCtx, n: int, gather: bool) -> bool {
    &&& x.sig.len() == 2 * n
    &&& x.offs.len() == n + 1
    &&& forall|r: int| 0 <= r < n ==> #[trigger] x.offs[r] <= x.offs[r + 1] && x.offs[r + 1] <= x.bytes.len()
    &&& codes_ok(x.codes, x.p)
    &&& gather ==> keys_ok(x, n)
}

/// The key index and key column are readable at every row.
pub open spec fn keys_ok(x: ScanCtx, n: int) -> bool {
    &&& x.bs >= 1
    &&& x.ic.len() == n && x.kc.len() == n
    &&& forall|r: int| 0 <= r < n ==> #[trigger] key_readable(x, n, r)
}

/// Row `r`'s stored row and key are in range.
pub open spec fn key_readable(x: ScanCtx, n: int, r: int) -> bool {
    &&& (r / x.bs) < x.ib.len()
    &&& 0 <= srow(x, r) < n
    &&& srow(x, r) / x.bs < x.kb.len()
    &&& i64::MIN <= okey(x, r) <= i64::MAX
}

// ------------------------------------------------------------------------------------------------ bit-sliced test

/// The bit-sliced signatures `sl0`, `sl1` (`nw` words per plane) hold bit `q` of signature words 0 and 1 of every row
/// `0 .. n` of `x.sig`.
#[verifier::opaque]
pub open spec fn sl_ok(x: ScanCtx, sl0: Seq<u64>, sl1: Seq<u64>, nw: int, n: int) -> bool {
    &&& n <= 64 * nw
    &&& sl0.len() == 64 * nw
    &&& sl1.len() == 64 * nw
    &&& forall|q: int, r: int| 0 <= q < 64 && 0 <= r < n ==> #[trigger] slice_bit(sl0, nw, q, r) == sig_bit(x.sig, 0, q, r)
    &&& forall|q: int, r: int| 0 <= q < 64 && 0 <= r < n ==> #[trigger] slice_bit(sl1, nw, q, r) == sig_bit(x.sig, 1, q, r)
}

/// Bit `p` (0..128: word `p / 64`, position `p % 64`) of the needed signature bits `n0`, `n1`.
pub open spec fn need_bit(n0: u64, n1: u64, p: int) -> bool {
    if p < 64 { bit_at(n0, p) } else { bit_at(n1, p - 64) }
}

/// The planes `pq` are exactly the bits the pattern needs: each listed plane is needed, and every needed bit is
/// listed.
#[verifier::opaque]
pub open spec fn pq_ok(pq: Seq<usize>, n0: u64, n1: u64) -> bool {
    &&& forall|j: int| 0 <= j < pq.len() ==> #[trigger] pq[j] < 128 && need_bit(n0, n1, pq[j] as int)
    &&& forall|p: int| 0 <= p < 128 && #[trigger] need_bit(n0, n1, p) ==> exists|j: int| 0 <= j < pq.len() && pq[j] == p
}

/// Signature bit `p` (0..128) of row `r`.
pub open spec fn pbit(x: ScanCtx, p: int, r: int) -> bool {
    if p < 64 { sig_bit(x.sig, 0, p, r) } else { sig_bit(x.sig, 1, p - 64, r) }
}

/// Bit `i` of `m` tells whether row `64 w + i` (below `n`) passes its signature test.
pub open spec fn mask_ok(x: ScanCtx, n: int, m: u64, w: int) -> bool {
    forall|i: int| 0 <= i < 64 && 64 * w + i < n ==>
        (#[trigger] bit_at(m, i) == !rejects(x.sig[2 * (64 * w + i)], x.sig[2 * (64 * w + i) + 1], x.need0, x.need1))
}

/// Every bit of the all-ones word is set.
proof fn lemma_ones_bit(i: u64)
    requires i < 64,
    ensures (0xFFFF_FFFF_FFFF_FFFFu64 >> i) & 1u64 == 1u64,
{
    assert((0xFFFF_FFFF_FFFF_FFFFu64 >> i) & 1u64 == 1u64) by (bit_vector) requires i < 64;
}

/// A bit of `a & b` is set exactly when it is set in both.
proof fn lemma_and_bit(a: u64, b: u64, i: u64)
    requires i < 64,
    ensures (((a & b) >> i) & 1u64 == 1u64) == (((a >> i) & 1u64 == 1u64) && ((b >> i) & 1u64 == 1u64)),
{
    assert((((a & b) >> i) & 1u64 == 1u64) == (((a >> i) & 1u64 == 1u64) && ((b >> i) & 1u64 == 1u64)))
        by (bit_vector) requires i < 64;
}

/// A word missing a bit of `nd` does not contain `nd`.
proof fn lemma_miss_rejects(s: u64, nd: u64, q: u64)
    requires q < 64, !((s >> q) & 1u64 == 1u64), (nd >> q) & 1u64 == 1u64,
    ensures s & nd != nd,
{
    assert(s & nd != nd) by (bit_vector) requires q < 64, !((s >> q) & 1u64 == 1u64), (nd >> q) & 1u64 == 1u64;
}

/// The bits `0 .. k` (all 64 when `k == 64`).
pub open spec fn low_mask(k: u64) -> u64 {
    if k >= 64 { 0xFFFF_FFFF_FFFF_FFFFu64 } else { ((1u64 << k) - 1u64) as u64 }
}

/// One more bit of containment: bit `k` of `nd` set in `s` extends agreement below `k` to below `k + 1`.
proof fn lemma_contains_step(s: u64, nd: u64, k: u64)
    requires
        k < 64,
        (s & nd) & low_mask(k) == nd & low_mask(k),
        (nd >> k) & 1u64 == 1u64 ==> (s >> k) & 1u64 == 1u64,
    ensures
        (s & nd) & low_mask((k + 1) as u64) == nd & low_mask((k + 1) as u64),
{
    if k < 63 {
        assert(((s & nd) & (((1u64 << k) - 1u64) as u64) == nd & (((1u64 << k) - 1u64) as u64)
            && ((nd >> k) & 1u64 == 1u64 ==> (s >> k) & 1u64 == 1u64))
            ==> (s & nd) & (((1u64 << ((k + 1) as u64)) - 1u64) as u64) == nd & (((1u64 << ((k + 1) as u64)) - 1u64) as u64))
            by (bit_vector) requires k < 63;
    } else {
        assert(((s & nd) & (((1u64 << 63u64) - 1u64) as u64) == nd & (((1u64 << 63u64) - 1u64) as u64)
            && ((nd >> 63u64) & 1u64 == 1u64 ==> (s >> 63u64) & 1u64 == 1u64))
            ==> (s & nd) & 0xFFFF_FFFF_FFFF_FFFFu64 == nd & 0xFFFF_FFFF_FFFF_FFFFu64)
            by (bit_vector);
    }
}

/// A word holding the bits `0 .. k` of `nd` agrees with `nd` on them.
proof fn lemma_contains_upto(s: u64, nd: u64, k: u64)
    requires
        k <= 64,
        forall|q: int| 0 <= q < 64 && #[trigger] bit_at(nd, q) ==> bit_at(s, q),
    ensures (s & nd) & low_mask(k) == nd & low_mask(k),
    decreases k,
{
    if k == 0 {
        assert((s & nd) & 0u64 == nd & 0u64) by (bit_vector);
        assert(low_mask(0) == 0u64) by (bit_vector);
    } else {
        let k1 = (k - 1) as u64;
        lemma_contains_upto(s, nd, k1);
        assert(bit_at(nd, k1 as int) ==> bit_at(s, k1 as int));
        lemma_contains_step(s, nd, k1);
    }
}

/// A word holding every bit of `nd` contains `nd`.
proof fn lemma_contains(s: u64, nd: u64)
    requires forall|q: int| 0 <= q < 64 && #[trigger] bit_at(nd, q) ==> bit_at(s, q),
    ensures s & nd == nd,
{
    lemma_contains_upto(s, nd, 64);
    assert((s & nd) & 0xFFFF_FFFF_FFFF_FFFFu64 == s & nd && nd & 0xFFFF_FFFF_FFFF_FFFFu64 == nd) by (bit_vector);
}

/// Slot `q * nw + w` lies in the 64 planes.
proof fn lemma_slot(q: int, w: int, nw: int)
    requires 0 <= q < 64, 0 <= w < nw,
    ensures 0 <= q * nw + w < 64 * nw,
{
    assert(q * nw + w < 64 * nw) by (nonlinear_arith) requires 0 <= q < 64, 0 <= w < nw;
    assert(q * nw >= 0) by (nonlinear_arith) requires 0 <= q, 0 <= nw;
}

/// The bit-sliced signatures and the planes to test, as the calling thread hands them to the tasks.
pub struct SliceArgs {
    pub sl0: &'static [u64],
    pub sl1: &'static [u64],
    pub nsl: usize,
    pub nw: usize,
    pub pq: Vec<usize>,
}

/// The slices describe the signatures of the rows `0 .. n` of `x` and the planes are the needed bits.
#[verifier::opaque]
pub open spec fn slice_args_ok(s: &SliceArgs, x: ScanCtx, n: int) -> bool {
    &&& sl_ok(x, s.sl0@, s.sl1@, s.nw as int, n)
    &&& s.nsl == s.sl0@.len()
    &&& pq_ok(s.pq@, x.need0, x.need1)
}

/// The planes of every needed bit of `n0`, `n1` (plane `p`: word `p / 64`, bit `p % 64`), in increasing order.
pub fn need_planes(n0: u64, n1: u64) -> (pq: Vec<usize>)
    ensures pq_ok(pq@, n0, n1),
{
    let mut pq: Vec<usize> = Vec::new();
    let mut p: usize = 0;
    while p < 128
        invariant
            p <= 128,
            forall|j: int| 0 <= j < pq@.len() ==> #[trigger] pq@[j] < 128 && need_bit(n0, n1, pq@[j] as int),
            forall|p2: int| 0 <= p2 < p && #[trigger] need_bit(n0, n1, p2) ==> exists|j: int| 0 <= j < pq@.len() && pq@[j] == p2,
        decreases 128 - p,
    {
        let set = if p < 64 { (n0 >> (p as u64)) & 1u64 == 1u64 } else { (n1 >> ((p - 64) as u64)) & 1u64 == 1u64 };
        assert(set == need_bit(n0, n1, p as int));
        let ghost old_pq = pq@;
        if set {
            pq.push(p);
            proof {
                assert forall|j: int| 0 <= j < pq@.len() implies #[trigger] pq@[j] < 128 && need_bit(n0, n1, pq@[j] as int) by {
                    if j < old_pq.len() {
                        assert(pq@[j] == old_pq[j]);
                    }
                }
                assert(pq@[old_pq.len() as int] == p);
            }
        }
        proof {
            assert forall|p2: int| 0 <= p2 < p + 1 && #[trigger] need_bit(n0, n1, p2) implies
                exists|j: int| 0 <= j < pq@.len() && pq@[j] == p2 by {
                if p2 < p {
                    let j = choose|j: int| 0 <= j < old_pq.len() && old_pq[j] == p2;
                    assert(pq@[j] == old_pq[j]);
                } else {
                    assert(pq@[old_pq.len() as int] == p2);
                }
            }
        }
        p = p + 1;
    }
    proof {
        reveal(pq_ok);
    }
    pq
}

/// The candidate mask of word `w` (rows `64 w .. 64 w + 64`): the AND of word `w` of the planes `pq`.
fn cand_word(sl0: &[u64], sl1: &[u64], nsl: usize, nw: usize, pq: &Vec<usize>, np: usize, w: usize,
    Ghost(x): Ghost<ScanCtx>, Ghost(n): Ghost<int>) -> (m: u64)
    requires
        sl_ok(x, sl0@, sl1@, nw as int, n),
        nsl == sl0@.len(),
        pq_ok(pq@, x.need0, x.need1),
        np == pq@.len(),
        w < nw,
    ensures
        mask_ok(x, n, m, w as int),
    no_unwind
{
    let mut m: u64 = 0xFFFF_FFFF_FFFF_FFFFu64;
    proof {
        assert forall|i: int| 0 <= i < 64 implies #[trigger] bit_at(m, i) by {
            lemma_ones_bit(i as u64);
        }
    }
    let mut j: usize = 0;
    while j < np
        invariant
            sl_ok(x, sl0@, sl1@, nw as int, n),
            nsl == sl0@.len(),
            pq_ok(pq@, x.need0, x.need1),
            np == pq@.len(),
            w < nw,
            j <= np,
            // A clear bit: some listed plane misses the row (so its signature misses a needed bit).
            forall|i: int| 0 <= i < 64 && 64 * w + i < n && !#[trigger] bit_at(m, i) ==>
                rejects(x.sig[2 * (64 * w + i)], x.sig[2 * (64 * w + i) + 1], x.need0, x.need1),
            // A set bit: every plane so far holds the row's bit.
            forall|i: int, j2: int| 0 <= i < 64 && 64 * w + i < n && 0 <= j2 < j && #[trigger] bit_at(m, i) ==>
                #[trigger] pbit(x, pq@[j2] as int, 64 * w + i),
        decreases np - j,
    {
        proof {
            reveal(sl_ok);
            reveal(pq_ok);
        }
        let p = pq[j];
        assert(p < 128 && need_bit(x.need0, x.need1, p as int));
        let q: usize = if p < 64 { p } else { p - 64 };
        proof {
            lemma_slot(q as int, w as int, nw as int);
        }
        let v = if p < 64 { sl0[q * nw + w] } else { sl1[q * nw + w] };
        let ghost m0 = m;
        m = m & v;
        proof {
            // Bit `i` of `v` is signature bit `p` of row `64 w + i`.
            assert forall|i: int| 0 <= i < 64 && 64 * w + i < n implies #[trigger] bit_at(v, i) == pbit(x, p as int, 64 * w + i) by {
                let r = 64 * w + i;
                assert(r / 64 == w && r % 64 == i);
                if p < 64 {
                    assert(slice_bit(sl0@, nw as int, q as int, r) == sig_bit(x.sig, 0, q as int, r));
                } else {
                    assert(slice_bit(sl1@, nw as int, q as int, r) == sig_bit(x.sig, 1, q as int, r));
                }
            }
            assert forall|i: int| 0 <= i < 64 && 64 * w + i < n && !#[trigger] bit_at(m, i) implies
                rejects(x.sig[2 * (64 * w + i)], x.sig[2 * (64 * w + i) + 1], x.need0, x.need1) by {
                lemma_and_bit(m0, v, i as u64);
                if bit_at(m0, i) {
                    let r = 64 * w + i;
                    assert(!bit_at(v, i));
                    assert(!pbit(x, p as int, r));
                    if p < 64 {
                        lemma_miss_rejects(x.sig[2 * r], x.need0, q as u64);
                    } else {
                        lemma_miss_rejects(x.sig[2 * r + 1], x.need1, q as u64);
                    }
                }
            }
            assert forall|i: int, j2: int| 0 <= i < 64 && 64 * w + i < n && 0 <= j2 < j + 1 && #[trigger] bit_at(m, i) implies
                #[trigger] pbit(x, pq@[j2] as int, 64 * w + i) by {
                lemma_and_bit(m0, v, i as u64);
                if j2 < j {
                    assert(bit_at(m0, i));
                    assert(pbit(x, pq@[j2] as int, 64 * w + i));
                } else {
                    assert(bit_at(v, i));
                    assert(pq@[j2] == p);
                }
            }
        }
        j = j + 1;
    }
    proof {
        reveal(pq_ok);
        assert forall|i: int| 0 <= i < 64 && 64 * w + i < n implies
            (#[trigger] bit_at(m, i) == !rejects(x.sig[2 * (64 * w + i)], x.sig[2 * (64 * w + i) + 1], x.need0, x.need1)) by {
            let r = 64 * w + i;
            if bit_at(m, i) {
                // Every needed bit is a listed plane, which holds the row's bit.
                assert forall|q: int| 0 <= q < 64 && #[trigger] bit_at(x.need0, q) implies bit_at(x.sig[2 * r], q) by {
                    assert(need_bit(x.need0, x.need1, q));
                    let j2 = choose|j2: int| 0 <= j2 < pq@.len() && pq@[j2] == q;
                    assert(pbit(x, pq@[j2] as int, r));
                }
                assert forall|q: int| 0 <= q < 64 && #[trigger] bit_at(x.need1, q) implies bit_at(x.sig[2 * r + 1], q) by {
                    assert(need_bit(x.need0, x.need1, q + 64));
                    let j2 = choose|j2: int| 0 <= j2 < pq@.len() && pq@[j2] == q + 64;
                    assert(pbit(x, pq@[j2] as int, r));
                }
                lemma_contains(x.sig[2 * r], x.need0);
                lemma_contains(x.sig[2 * r + 1], x.need1);
            }
        }
    }
    m
}

/// The next row to visit after row `r`: `r + 1`, or the next word (or `b`) when no bit of `m` above row `r`'s is
/// set; the rows skipped are all `FLAG_NO`.
fn next_row(r: usize, b: usize, m: u64, Ghost(x): Ghost<ScanCtx>, Ghost(a): Ghost<int>, Ghost(n): Ghost<int>) -> (r2: usize)
    requires
        a <= r < b <= n,
        mask_ok(x, n, m, r as int / 64),
    ensures
        r < r2 <= b,
        (r2 - 1) / 64 == r as int / 64,
        lkeys(x, a, r2 as int) == lkeys(x, a, r + 1),
        lrows(x, a, r2 as int) == lrows(x, a, r + 1),
        drows(x, a, r2 as int) == drows(x, a, r + 1),
        nerr(x, a, r2 as int) == nerr(x, a, r + 1),
    no_unwind
{
    let s = r % 64;
    if (m >> (s as u64)) >> 1u64 == 0u64 {
        let step = 64 - s;
        let r2 = if step < b - r { r + step } else { b };
        proof {
            let w = r as int / 64;
            assert forall|q: int| r + 1 <= q < r2 implies #[trigger] rflag(x, q) == FLAG_NO by {
                let i = q - 64 * w;
                assert(q / 64 == w && q % 64 == i && 0 <= i < 64);
                lemma_above_clear(m, s as u64, i as u64);
                assert(!bit_at(m, i));
            }
            lemma_skip_no(x, a, r + 1, r2 as int);
        }
        r2
    } else {
        r + 1
    }
}

/// One phase-1 task over the rows `[a, b)`.
pub struct ScanTask {
    pub sig: &'static [u64],
    pub nsig: usize,
    pub offs: &'static [u64],
    pub bytes: &'static [u8],
    pub nbytes: usize,
    pub codes: Vec<u16>,
    pub need0: u64,
    pub need1: u64,
    pub ic: &'static [u32],
    pub ib: &'static [u64],
    pub kc: &'static [u32],
    pub kb: &'static [i64],
    pub bs: usize,
    pub n: usize,
    pub a: usize,
    pub b: usize,
    pub gather: bool,
    pub keys: Vec<i64>,
    pub rows: Vec<usize>,
    pub defer: Vec<usize>,
    pub kcap: usize,
    pub dcap: usize,
    pub toks: Ghost<Seq<LikeTok>>,
    /// The phase-2 key ranges `[blo[t], bhi[t])` (`nb` of them; none: no reordering), and zeroed offset slots
    /// (`nb + 2`) and scratch (`nb + 1`) for the reordering.
    pub blo: Vec<i64>,
    pub bhi: Vec<i64>,
    pub nb: usize,
    pub boff: Vec<usize>,
    pub cur: Vec<usize>,
    /// The bit-sliced signatures (`nsl` words each, `nw` per plane) and the planes `pq` (`np` of them) to test.
    pub sl0: &'static [u64],
    pub sl1: &'static [u64],
    pub nsl: usize,
    pub nw: usize,
    pub pq: Vec<usize>,
    pub np: usize,
}

/// The context of a task's slices.
pub open spec fn task_ctx(t: ScanTask) -> ScanCtx {
    ScanCtx {
        sig: t.sig@, offs: t.offs@, bytes: t.bytes@, codes: t.codes@, p: t.toks@, need0: t.need0, need1: t.need1,
        ic: t.ic@, ib: t.ib@, kc: t.kc@, kb: t.kb@, bs: t.bs as int,
    }
}

/// What a task returns: the keys of its matching rows (`keys[0 .. nk]`, when it gathers) or the rows themselves
/// (`rows[0 .. nk]`, otherwise), its deferred rows (`defer[0 .. nd]`) and its number of error rows; `overflow` when
/// a buffer was too small (only when its capacity is below the row count; the caller then reruns the rows).
pub struct ScanOut {
    pub keys: Vec<i64>,
    pub rows: Vec<usize>,
    pub nk: usize,
    pub defer: Vec<usize>,
    pub nd: usize,
    pub n_err: usize,
    pub overflow: bool,
    /// When `parted`, `keys[0 .. nk]` is cut into the segments of the phase-2 key ranges at the offsets `boff`.
    pub boff: Vec<usize>,
    pub parted: bool,
}

pub open spec fn scan_pre(t: ScanTask) -> bool {
    &&& t.a <= t.b <= t.n
    &&& t.nbytes == t.bytes@.len()
    &&& t.nsig == t.sig@.len()
    &&& ctx_ok(task_ctx(t), t.n as int, t.gather)
    &&& t.gather ==> t.keys@.len() == t.kcap
    &&& t.rows@.len() == t.kcap
    &&& t.defer@.len() == t.dcap
    &&& ranges_ok(t.blo@, t.bhi@)
    &&& t.nb == t.blo@.len()
    &&& t.nb + 2 <= usize::MAX
    &&& t.boff@.len() == t.nb + 2
    &&& forall|i: int| 0 <= i < t.nb + 2 ==> #[trigger] t.boff@[i] == 0
    &&& t.cur@.len() == t.nb + 1
    &&& sl_ok(task_ctx(t), t.sl0@, t.sl1@, t.nw as int, t.n as int)
    &&& t.nsl == t.sl0@.len()
    &&& pq_ok(t.pq@, t.need0, t.need1)
    &&& t.np == t.pq@.len()
}

pub open spec fn scan_post(t: ScanTask, o: ScanOut) -> bool {
    &&& !o.overflow ==> chunk_post(task_ctx(t), t.gather, t.a as int, t.b as int, o)
    &&& !o.overflow ==> seg_post(o, t.blo@, t.bhi@)
    &&& o.overflow ==> t.kcap < t.b - t.a || t.dcap < t.b - t.a
}

/// The outputs of the rows `a .. b`: the keys (or rows) of the matching rows, the deferred rows, the error count.
pub open spec fn chunk_post(x: ScanCtx, gather: bool, a: int, b: int, o: ScanOut) -> bool {
    &&& gather ==> o.nk <= o.keys@.len() && o.nk == lkeys(x, a, b).len()
            && forall|v: int| #[trigger] cnt_rng(o.keys@, v, 0, o.nk as int) == cnt_rng(lkeys(x, a, b), v, 0, o.nk as int)
    &&& !gather ==> o.nk <= o.rows@.len() && o.rows@.subrange(0, o.nk as int) == lrows(x, a, b)
    &&& o.nd <= o.defer@.len()
    &&& o.defer@.subrange(0, o.nd as int) == drows(x, a, b)
    &&& o.n_err == nerr(x, a, b)
}

/// A reordered key list is cut into the segments of the key ranges `[lo[t], hi[t])`.
pub open spec fn seg_post(o: ScanOut, lo: Seq<i64>, hi: Seq<i64>) -> bool {
    o.parted ==> o.nk <= o.keys@.len() && segs_ok(o.keys@.subrange(0, o.nk as int), o.boff@, lo, hi)
}

/// The keys of the matching rows are the keys of their rows, in the same order.
pub proof fn lemma_lkeys_rows(x: ScanCtx, a: int, m: int)
    requires 0 <= a <= m <= usize::MAX,
    ensures
        lrows(x, a, m).len() == lkeys(x, a, m).len(),
        forall|i: int| 0 <= i < lkeys(x, a, m).len() ==> a <= #[trigger] lrows(x, a, m)[i] < m
            && lkeys(x, a, m)[i] == okey(x, lrows(x, a, m)[i] as int) as i64,
    decreases m - a,
{
    if m > a {
        lemma_lkeys_rows(x, a, m - 1);
        lemma_lists_len(x, a, m - 1);
        let (lr, lk) = (lrows(x, a, m - 1), lkeys(x, a, m - 1));
        assert forall|i: int| 0 <= i < lkeys(x, a, m).len() implies a <= #[trigger] lrows(x, a, m)[i] < m
            && lkeys(x, a, m)[i] == okey(x, lrows(x, a, m)[i] as int) as i64 by {
            if i < lk.len() {
                if rflag(x, m - 1) == FLAG_LIKE {
                    assert(lrows(x, a, m)[i] == lr[i] && lkeys(x, a, m)[i] == lk[i]);
                }
            } else {
                assert(rflag(x, m - 1) == FLAG_LIKE);
                assert(lrows(x, a, m)[i] == (m - 1) as usize);
            }
        }
    }
}

/// The rows `r1 .. r2` all flagged `FLAG_NO` add nothing to the outputs.
pub proof fn lemma_skip_no(x: ScanCtx, a: int, r1: int, r2: int)
    requires
        a <= r1 <= r2,
        forall|q: int| r1 <= q < r2 ==> #[trigger] rflag(x, q) == FLAG_NO,
    ensures
        lkeys(x, a, r2) == lkeys(x, a, r1),
        lrows(x, a, r2) == lrows(x, a, r1),
        drows(x, a, r2) == drows(x, a, r1),
        nerr(x, a, r2) == nerr(x, a, r1),
    decreases r2 - r1,
{
    if r2 > r1 {
        lemma_skip_no(x, a, r1, r2 - 1);
        assert(rflag(x, r2 - 1) == FLAG_NO);
    }
}

/// No bit above `s` is set when `m >> s >> 1` is zero.
proof fn lemma_above_clear(m: u64, s: u64, i: u64)
    requires (m >> s) >> 1u64 == 0u64, s < i < 64,
    ensures !((m >> i) & 1u64 == 1u64),
{
    assert(!((m >> i) & 1u64 == 1u64)) by (bit_vector) requires (m >> s) >> 1u64 == 0u64, s < i < 64;
}

/// The output lists of a prefix are no longer than the prefix.
pub proof fn lemma_lists_len(x: ScanCtx, a: int, m: int)
    requires a <= m,
    ensures
        lkeys(x, a, m).len() <= m - a,
        lrows(x, a, m).len() == lkeys(x, a, m).len(),
        drows(x, a, m).len() <= m - a,
        nerr(x, a, m) <= m - a,
    decreases m - a,
{
    if m > a {
        lemma_lists_len(x, a, m - 1);
    }
}

impl WorkerTask for ScanTask {
    type Output = ScanOut;

    open spec fn pre(&self) -> bool {
        scan_pre(*self)
    }

    open spec fn post(&self, out: ScanOut) -> bool {
        scan_post(*self, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.a as u64, self.b as u64)
    }

    fn run(self) -> (out: ScanOut) {
        let ghost task = self;
        let ghost x = task_ctx(self);
        let ScanTask { sig, nsig, offs, bytes, nbytes, codes, need0, need1, ic, ib, kc, kb, bs, n, a, b, gather, keys, rows, defer, kcap, dcap, toks, blo, bhi, nb, boff, cur, sl0, sl1, nsl, nw, pq, np } = self;
        let mut boff = boff;
        let mut cur = cur;
        let ghost p = toks@;
        let mut keys = keys;
        let mut rows = rows;
        let mut defer = defer;
        let mut nk: usize = 0;
        let mut nd: usize = 0;
        let mut n_err: usize = 0;
        // The candidate mask of the word of the previous row.
        let mut m: u64 = 0;
        let mut r = a;
        while r < b
            invariant
                x == task_ctx(task), scan_pre(task),
                task.sig == sig, task.offs == offs, task.bytes == bytes, task.codes == codes, task.need0 == need0,
                task.need1 == need1, task.ic == ic, task.ib == ib, task.kc == kc, task.kb == kb, task.bs == bs,
                task.n == n, task.a == a, task.b == b, task.toks == toks, p == toks@, task.gather == gather,
                nbytes == bytes@.len(),
                nsig == sig@.len(),
                a <= r <= b,
                nk <= r - a,
                nd <= r - a,
                task == self,
                task.kcap == kcap, task.dcap == dcap,
                task.blo == blo, task.bhi == bhi, task.nb == nb, task.boff == boff, task.cur == cur,
                nk <= kcap, nd <= dcap,
                gather ==> keys@.len() == kcap,
                rows@.len() == kcap,
                defer@.len() == dcap,
                nk as int == lkeys(x, a as int, r as int).len(),
                rows@.subrange(0, nk as int) == lrows(x, a as int, r as int),
                nd as int == drows(x, a as int, r as int).len(),
                defer@.subrange(0, nd as int) == drows(x, a as int, r as int),
                n_err == nerr(x, a as int, r as int),
                task.sl0 == sl0, task.sl1 == sl1, task.nsl == nsl, task.nw == nw, task.pq == pq, task.np == np,
                a < r ==> mask_ok(x, n as int, m, (r - 1) / 64),
            decreases b - r,
        {
            proof {
                lemma_lists_len(x, a as int, r as int);
            }
            if r == a || r % 64 == 0 {
                proof {
                    reveal(sl_ok);
                }
                assert(r / 64 < nw);
                m = cand_word(sl0, sl1, nsl, nw, &pq, np, r / 64, Ghost(x), Ghost(n as int));
            }
            assert(mask_ok(x, n as int, m, r as int / 64));
            assert(64 * (r as int / 64) + r as int % 64 == r);
            if (m >> ((r % 64) as u64)) & 1u64 == 1u64 {
                assert(bit_at(m, r as int % 64));
                assert(!rejects(sig@[2 * r as int], sig@[2 * r as int + 1], need0, need1));
                assert(offs@[r as int] <= offs@[r + 1] && offs@[r + 1] <= nbytes);
                let lo = offs[r] as usize;
                let hi = offs[r + 1] as usize;
                let ghost t = rtext(x, r as int);
                if !ascii_range(bytes, lo, hi) {
                    if nd >= dcap {
                        assert(nd <= r - a && r < b);
                        assert(task.dcap < task.b - task.a);
                        return ScanOut { keys, rows, nk, defer, nd, n_err, overflow: true, boff, parted: false };
                    }
                    let ghost old_defer = defer@;
                    put(&mut defer, nd, r);
                    proof {
                        assert(rflag(x, r as int) == FLAG_DEFER);
                        assert(defer@.subrange(0, nd + 1) =~= old_defer.subrange(0, nd as int).push(r));
                    }
                    nd = nd + 1;
                } else {
                    assert(tview(bytes@, lo as int, hi as int) == byte_chars(t));
                    match mt_b(bytes, lo, hi, &codes, Ghost(p), 0, 0) {
                        Ok(LikeRes::Match) => {
                            assert(rflag(x, r as int) == FLAG_LIKE);
                            if nk >= kcap {
                                assert(nk <= r - a && r < b);
                                assert(task.kcap < task.b - task.a);
                                return ScanOut { keys, rows, nk, defer, nd, n_err, overflow: true, boff, parted: false };
                            }
                            let ghost old_rows = rows@;
                            put(&mut rows, nk, r);
                            proof {
                                assert(rows@.subrange(0, nk + 1) =~= old_rows.subrange(0, nk as int).push(r));
                            }
                            nk = nk + 1;
                        },
                        Ok(_) => {
                            assert(rflag(x, r as int) == FLAG_NO);
                        },
                        Err(_) => {
                            assert(rflag(x, r as int) == FLAG_ERR);
                            n_err = n_err + 1;
                        },
                    }
                }
            } else {
                assert(!bit_at(m, r as int % 64));
                assert(rflag(x, r as int) == FLAG_NO);
            }
            // No candidate left in this word: jump to the next word.
            r = next_row(r, b, m, Ghost(x), Ghost(a as int), Ghost(n as int));
        }
        proof {
            lemma_lists_len(x, a as int, b as int);
        }
        // The keys of the matching rows (independent loads: they overlap).
        if gather {
            proof {
                lemma_lkeys_rows(x, a as int, b as int);
            }
            let ghost lk = lkeys(x, a as int, b as int);
            let ghost lr = lrows(x, a as int, b as int);
            let mut j: usize = 0;
            while j < nk
                invariant
                    x == task_ctx(task), scan_pre(task), gather, task.gather == gather, task.a == a,
                    task.ic == ic, task.ib == ib, task.kc == kc, task.kb == kb, task.bs == bs, task.n == n, task.b == b,
                    a <= b,
                    j <= nk, nk <= kcap,
                    keys@.len() == kcap, rows@.len() == kcap,
                    rows@.subrange(0, nk as int) == lr,
                    lk == lkeys(x, a as int, b as int), lr == lrows(x, a as int, b as int),
                    nk == lk.len(), lr.len() == lk.len(),
                    forall|i: int| 0 <= i < lk.len() ==> a <= #[trigger] lr[i] < b && lk[i] == okey(x, lr[i] as int) as i64,
                    forall|i: int| 0 <= i < j ==> #[trigger] keys@[i] == lk[i],
                decreases nk - j,
            {
                let r = rows[j];
                proof {
                    assert(r == lr[j as int]);
                    assert(key_readable(x, n as int, r as int));
                    assert((r as int) / (bs as int) < ib@.len());
                }
                let s = (ib[grp(r, bs)] + ic[r] as u64) as usize;
                assert(s as int == srow(x, r as int));
                let key = kb[grp(s, bs)] + kc[s] as i64;
                put(&mut keys, j, key);
                j = j + 1;
            }
            proof {
                assert(keys@.subrange(0, nk as int) =~= lk);
            }
        }
        let ghost k0 = keys@;
        let mut parted = false;
        if gather && nb > 0 && nk <= kcap - nk {
            partition_prefix(&mut keys, nk, &blo, &bhi, nb, &mut boff, &mut cur);
            parted = true;
        }
        proof {
            if gather {
                let lk = lkeys(x, a as int, b as int);
                assert(k0.subrange(0, nk as int) == lk);
                assert forall|v: int| #[trigger] cnt_rng(keys@, v, 0, nk as int) == cnt_rng(lk, v, 0, nk as int) by {
                    lemma_rng_sub(k0, nk as int, v, 0, nk as int);
                }
            }
        }
        ScanOut { keys, rows, nk, defer, nd, n_err, overflow: false, boff, parted }
    }
}

} // verus!
