//! First occurrence of a short byte literal inside a byte range `[from, to)` of a larger buffer, by windows of 64
//! start positions: a branch-free pass over one window (`window_first`) yields the first position whose first (up
//! to) four bytes match the literal, and the OR of the window's bytes; only at that position is the whole literal
//! compared. Every function is `no_unwind` (usable in worker tasks); slice lengths are passed in (`nbytes`).
//!
//! Positions are absolute indices into `bytes`; `occ(bytes, lit, q, to)` says the literal occurs at `q` and ends
//! at or before `to`.
use vstd::prelude::*;

verus! {

/// `lit` occurs at byte `q` of `bytes` and ends at or before `to`.
pub open spec fn occ(bytes: Seq<u8>, lit: Seq<u8>, q: int, to: int) -> bool {
    &&& 0 <= q
    &&& q + lit.len() <= to
    &&& to <= bytes.len()
    &&& forall|k: int| 0 <= k < lit.len() ==> #[trigger] bytes[q + k] == lit[k]
}

/// No occurrence of `lit` (ending at or before `to`) starts in `[a, b)`.
pub open spec fn no_occ(bytes: Seq<u8>, lit: Seq<u8>, a: int, b: int, to: int) -> bool {
    forall|q: int| a <= q < b ==> !#[trigger] occ(bytes, lit, q, to)
}

/// Byte `q` starts with the literal's first `min(|lit|, 4)` bytes.
pub open spec fn pre4(bytes: Seq<u8>, q: int, lit: Seq<u8>) -> bool {
    forall|k: int| 0 <= k < lit.len() && k < 4 ==> #[trigger] bytes[q + k] == lit[k]
}

/// The comparison pattern of the literal's first four bytes: bytes `c0..c3` and masks `k1..k3` (all ones below the
/// literal's length, zero beyond it, so a masked comparison past the literal always holds).
#[derive(Clone, Copy)]
pub struct Prefix {
    pub c0: u8,
    pub c1: u8,
    pub c2: u8,
    pub c3: u8,
    pub k1: u8,
    pub k2: u8,
    pub k3: u8,
}

pub open spec fn prefix_ok(pf: Prefix, lit: Seq<u8>) -> bool {
    &&& lit.len() >= 1 && pf.c0 == lit[0]
    &&& pf.k1 == (if lit.len() > 1 { 0xffu8 } else { 0u8 }) && pf.c1 == (if lit.len() > 1 { lit[1] } else { 0u8 })
    &&& pf.k2 == (if lit.len() > 2 { 0xffu8 } else { 0u8 }) && pf.c2 == (if lit.len() > 2 { lit[2] } else { 0u8 })
    &&& pf.k3 == (if lit.len() > 3 { 0xffu8 } else { 0u8 }) && pf.c3 == (if lit.len() > 3 { lit[3] } else { 0u8 })
}

/// The comparison pattern of `lit` (`m` bytes, at least one).
pub fn prefix_of(lit: &Vec<u8>, m: usize) -> (pf: Prefix)
    requires m == lit@.len(), m >= 1,
    ensures prefix_ok(pf, lit@),
    no_unwind
{
    Prefix {
        c0: lit[0],
        c1: if m > 1 { lit[1] } else { 0u8 }, k1: if m > 1 { 0xffu8 } else { 0u8 },
        c2: if m > 2 { lit[2] } else { 0u8 }, k2: if m > 2 { 0xffu8 } else { 0u8 },
        c3: if m > 3 { lit[3] } else { 0u8 }, k3: if m > 3 { 0xffu8 } else { 0u8 },
    }
}

/// An occurrence starts with the literal's prefix.
pub proof fn lemma_occ_pre4(bytes: Seq<u8>, lit: Seq<u8>, q: int, to: int)
    requires occ(bytes, lit, q, to),
    ensures pre4(bytes, q, lit),
{
    assert forall|k: int| 0 <= k < lit.len() && k < 4 implies #[trigger] bytes[q + k] == lit[k] by {}
}

/// A narrower end keeps no occurrence out; occurrences need the whole literal before the end.
pub proof fn lemma_occ_end(bytes: Seq<u8>, lit: Seq<u8>, q: int, to: int, to2: int)
    requires occ(bytes, lit, q, to), q + lit.len() <= to2 <= bytes.len(),
    ensures occ(bytes, lit, q, to2),
{
}

/// `x & 0xff == x` and `x & 0 == 0`.
proof fn lemma_mask(b: u8)
    ensures b & 0xffu8 == b, b & 0u8 == 0u8,
{
    assert(b & 0xffu8 == b && b & 0u8 == 0u8) by (bit_vector);
}

/// The OR of bytes is ASCII exactly when both are (used by the ASCII test of a run of rows).
pub proof fn lemma_or_ascii(a: u8, b: u8)
    ensures ((a | b) < 0x80u8) == (a < 0x80u8 && b < 0x80u8),
{
    assert(((a | b) < 0x80u8) == (a < 0x80u8 && b < 0x80u8)) by (bit_vector);
}

/// One masked comparison holds at an occurrence of the prefix.
proof fn lemma_flag(x: u8, k: u8, c: u8, lit: Seq<u8>, i: int)
    requires
        1 <= i < 4,
        k == (if lit.len() > i { 0xffu8 } else { 0u8 }),
        c == (if lit.len() > i { lit[i] } else { 0u8 }),
        lit.len() > i ==> x == lit[i],
    ensures (x & k) == c,
{
    lemma_mask(x);
}

/// Whether some position of the window `p .. p + 64` (three more bytes are read) starts with the literal's prefix:
/// `false` means none does. A branch-free OR over the window (it vectorizes); the cheap test of every window.
pub fn window_any(bytes: &[u8], p: usize, pf: &Prefix, Ghost(lit): Ghost<Seq<u8>>) -> (r: bool)
    requires p + 67 <= bytes@.len(), prefix_ok(*pf, lit),
    ensures !r ==> forall|q: int| p <= q < p + 64 ==> !#[trigger] pre4(bytes@, q, lit),
    no_unwind
{
    let (_, tail) = bytes.split_at(p);
    let (blk, _) = tail.split_at(67);
    assert(blk@ =~= bytes@.subrange(p as int, p + 67));
    let c0 = pf.c0;
    let c1 = pf.c1;
    let c2 = pf.c2;
    let c3 = pf.c3;
    let k1 = pf.k1;
    let k2 = pf.k2;
    let k3 = pf.k3;
    let mut any: u8 = 0;
    let mut j: usize = 0;
    while j < 64
        invariant
            j <= 64, p + 67 <= bytes@.len(), blk@ == bytes@.subrange(p as int, p + 67), prefix_ok(*pf, lit),
            c0 == pf.c0, c1 == pf.c1, c2 == pf.c2, c3 == pf.c3, k1 == pf.k1, k2 == pf.k2, k3 == pf.k3,
            any == 0u8 ==> forall|q: int| p <= q < p + j ==> !#[trigger] pre4(bytes@, q, lit),
        decreases 64 - j,
    {
        let f0: u8 = if blk[j] == c0 { 1 } else { 0 };
        let f1: u8 = if (blk[j + 1] & k1) == c1 { 1 } else { 0 };
        let f2: u8 = if (blk[j + 2] & k2) == c2 { 1 } else { 0 };
        let f3: u8 = if (blk[j + 3] & k3) == c3 { 1 } else { 0 };
        let t: u8 = f0 & f1 & f2 & f3;
        proof {
            if pre4(bytes@, p + j, lit) {
                lemma_flags_one(bytes@, blk@, p as int, j as int, lit, *pf, f0, f1, f2, f3);
            }
            lemma_or_zero(any, t);
        }
        any = any | t;
        j = j + 1;
    }
    any != 0u8
}

/// The four 0/1 flags of position `p + j` are all 1 when the literal's prefix starts there.
proof fn lemma_flags_one(bytes: Seq<u8>, blk: Seq<u8>, p: int, j: int, lit: Seq<u8>, pf: Prefix, f0: u8, f1: u8, f2: u8, f3: u8)
    requires
        0 <= j < 64, p >= 0, p + 67 <= bytes.len(), blk == bytes.subrange(p, p + 67), prefix_ok(pf, lit),
        f0 == (if blk[j] == pf.c0 { 1u8 } else { 0u8 }),
        f1 == (if (blk[j + 1] & pf.k1) == pf.c1 { 1u8 } else { 0u8 }),
        f2 == (if (blk[j + 2] & pf.k2) == pf.c2 { 1u8 } else { 0u8 }),
        f3 == (if (blk[j + 3] & pf.k3) == pf.c3 { 1u8 } else { 0u8 }),
        pre4(bytes, p + j, lit),
    ensures f0 == 1u8 && f1 == 1u8 && f2 == 1u8 && f3 == 1u8, (f0 & f1 & f2 & f3) == 1u8,
{
    let q = p + j;
    assert(blk[j] == bytes[q] && blk[j + 1] == bytes[q + 1] && blk[j + 2] == bytes[q + 2] && blk[j + 3] == bytes[q + 3]);
    assert(bytes[q + 0] == lit[0]);
    if lit.len() > 1 { assert(bytes[q + 1] == lit[1]); }
    if lit.len() > 2 { assert(bytes[q + 2] == lit[2]); }
    if lit.len() > 3 { assert(bytes[q + 3] == lit[3]); }
    lemma_flag(blk[j + 1], pf.k1, pf.c1, lit, 1);
    lemma_flag(blk[j + 2], pf.k2, pf.c2, lit, 2);
    lemma_flag(blk[j + 3], pf.k3, pf.c3, lit, 3);
    assert((1u8 & 1u8 & 1u8 & 1u8) == 1u8) by (bit_vector);
}

/// OR with a flag keeps "zero only if both are zero".
proof fn lemma_or_zero(a: u8, b: u8)
    ensures ((a | b) == 0u8) == (a == 0u8 && b == 0u8),
{
    assert(((a | b) == 0u8) == (a == 0u8 && b == 0u8)) by (bit_vector);
}

/// Window `p .. p + 64` (three more bytes are read): the first position `j < 64` whose bytes start with the
/// literal's prefix (64 when there is none).
pub fn window_first(bytes: &[u8], p: usize, pf: &Prefix, Ghost(lit): Ghost<Seq<u8>>) -> (j: usize)
    requires p + 67 <= bytes@.len(), prefix_ok(*pf, lit),
    ensures
        j <= 64,
        forall|q: int| p <= q < p + j ==> !#[trigger] pre4(bytes@, q, lit),
    no_unwind
{
    let (_, tail) = bytes.split_at(p);
    let (blk, _) = tail.split_at(67);
    assert(blk@ =~= bytes@.subrange(p as int, p + 67));
    let c0 = pf.c0;
    let c1 = pf.c1;
    let c2 = pf.c2;
    let c3 = pf.c3;
    let k1 = pf.k1;
    let k2 = pf.k2;
    let k3 = pf.k3;
    let mut best: u8 = 64;
    let mut j: usize = 0;
    while j < 64
        invariant
            j <= 64, p + 67 <= bytes@.len(), blk@ == bytes@.subrange(p as int, p + 67), prefix_ok(*pf, lit),
            c0 == pf.c0, c1 == pf.c1, c2 == pf.c2, c3 == pf.c3, k1 == pf.k1, k2 == pf.k2, k3 == pf.k3,
            best <= 64,
            forall|q: int| p <= q < p + j && q < p + best ==> !#[trigger] pre4(bytes@, q, lit),
            best < 64 ==> best < j,
        decreases 64 - j,
    {
        // one 0/1 flag per compared byte (branch-free, so the loop vectorizes)
        let f0: u8 = if blk[j] == c0 { 1 } else { 0 };
        let f1: u8 = if (blk[j + 1] & k1) == c1 { 1 } else { 0 };
        let f2: u8 = if (blk[j + 2] & k2) == c2 { 1 } else { 0 };
        let f3: u8 = if (blk[j + 3] & k3) == c3 { 1 } else { 0 };
        let v: u8 = if (f0 & f1 & f2 & f3) == 1u8 { j as u8 } else { 64u8 };
        proof {
            if pre4(bytes@, p + j, lit) {
                lemma_flags_one(bytes@, blk@, p as int, j as int, lit, *pf, f0, f1, f2, f3);
            }
        }
        best = if v < best { v } else { best };
        j = j + 1;
    }
    best as usize
}

/// Whether the whole literal is at `q` (`q + m <= nbytes`).
pub fn lit_at(bytes: &[u8], q: usize, lit: &Vec<u8>, m: usize, Ghost(nbytes): Ghost<int>) -> (r: bool)
    requires q + m <= nbytes == bytes@.len(), nbytes <= usize::MAX, m == lit@.len(),
    ensures r == forall|k: int| 0 <= k < m ==> #[trigger] bytes@[q + k] == lit@[k],
    no_unwind
{
    let mut k: usize = 0;
    while k < m
        invariant k <= m, q + m <= bytes@.len(), bytes@.len() <= usize::MAX, m == lit@.len(),
            forall|t: int| 0 <= t < k ==> #[trigger] bytes@[q + t] == lit@[t],
        decreases m - k,
    {
        if bytes[q + k] != lit[k] {
            return false;
        }
        k = k + 1;
    }
    true
}

/// The first occurrence of `lit` (`m` bytes, prefix pattern `pf`) starting in `[from, to)` and ending at or before
/// `to`: `Some(q)` with no occurrence in `[from, q)`, or `None` when there is none.
pub fn find_first(bytes: &[u8], nbytes: usize, from: usize, to: usize, lit: &Vec<u8>, m: usize, pf: &Prefix)
    -> (r: Option<usize>)
    requires
        from <= to <= nbytes, nbytes == bytes@.len(), m == lit@.len(), m >= 1, prefix_ok(*pf, lit@),
    ensures
        match r {
            Some(q) => from <= q && occ(bytes@, lit@, q as int, to as int)
                && no_occ(bytes@, lit@, from as int, q as int, to as int),
            None => no_occ(bytes@, lit@, from as int, to as int, to as int),
        },
    no_unwind
{
    let ghost bv = bytes@;
    let ghost lv = lit@;
    // the literal often starts right at `from` (a hit of its prefix): test it before scanning windows
    if to - from >= m && lit_at(bytes, from, lit, m, Ghost(nbytes as int)) {
        return Some(from);
    }
    let mut w = from;
    while w < to && to - w >= m
        invariant
            from <= w <= to <= nbytes, nbytes == bv.len(), bv == bytes@, lv == lit@, m == lv.len(), m >= 1,
            prefix_ok(*pf, lv),
            no_occ(bv, lv, from as int, w as int, to as int),
        decreases to - w,
    {
        if nbytes - w < 67 {
            // near the end of the buffer: one position at a time
            let mut q = w;
            while q < to && to - q >= m
                invariant
                    from <= w <= q <= to <= nbytes, nbytes == bv.len(), bv == bytes@, lv == lit@, m == lv.len(), m >= 1,
                    no_occ(bv, lv, from as int, q as int, to as int),
                decreases to - q,
            {
                if lit_at(bytes, q, lit, m, Ghost(nbytes as int)) {
                    return Some(q);
                }
                q = q + 1;
            }
            proof {
                assert forall|t: int| from <= t < to implies !#[trigger] occ(bv, lv, t, to as int) by {
                    if t >= q { assert(t + m > to); }
                }
            }
            return None;
        }
        let j = if window_any(bytes, w, pf, Ghost(lv)) { window_first(bytes, w, pf, Ghost(lv)) } else { 64 };
        proof {
            assert forall|t: int| from <= t < w + j implies !#[trigger] occ(bv, lv, t, to as int) by {
                if t >= w {
                    if occ(bv, lv, t, to as int) { lemma_occ_pre4(bv, lv, t, to as int); }
                }
            }
        }
        if j == 64 {
            w = if to - w >= 64 { w + 64 } else { to };
            proof {
                assert forall|t: int| from <= t < w implies !#[trigger] occ(bv, lv, t, to as int) by {
                    if t >= to { assert(t + m > to); }
                }
            }
        } else {
            let q = w + j;
            if q >= to || to - q < m {
                proof {
                    assert forall|t: int| from <= t < to implies !#[trigger] occ(bv, lv, t, to as int) by {
                        if t >= q { assert(t + m > to); }
                    }
                }
                return None;
            }
            if lit_at(bytes, q, lit, m, Ghost(nbytes as int)) {
                return Some(q);
            }
            w = q + 1;
        }
    }
    proof {
        assert forall|t: int| from <= t < to implies !#[trigger] occ(bv, lv, t, to as int) by {
            if t >= w { assert(t + m > to); }
        }
    }
    None
}

} // verus!
