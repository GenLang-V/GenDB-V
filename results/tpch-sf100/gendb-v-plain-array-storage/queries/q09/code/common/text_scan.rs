//! Substring bitmap over a run of text values in one pass over their bytes: for rows `lo..hi` of a text column
//! (offsets + bytes, `offs_wf`), the bit of row `x` (bit `(x - lo) % 64` of word `(x - lo) / 64`) is set exactly
//! when the value of `x` contains the literal, and the result tells whether every byte of the run is ASCII.
//!
//! The rows' values are contiguous (`offs[lo] .. offs[hi]`), so the scan reads each byte once, in groups of 64
//! bytes (`group_flags`): a branch-free loop over a fixed 67-byte window ORs the bytes (the ASCII test) and flags
//! whether any position of the group starts with the literal's first (up to) four bytes. Only a flagged group, and
//! the bytes after the last full group, take the per-byte step (`step`): at an occurrence of the first byte it
//! moves a row cursor forward to the row holding that position and compares the whole literal inside that row's
//! bounds. Every occurrence inside a row starts with the literal's prefix, so none is missed (`bits_inv`).
use vstd::prelude::*;
use crate::agent::common::bits::{bit, lemma_bit_zero};
use crate::agent::common::like_contains::{sub_at, has_sub, ascii};

verus! {

/// Offsets of `n` values in `blen` bytes: non-decreasing, inside the bytes.
pub open spec fn offs_wf(offs: Seq<i64>, n: int, blen: int) -> bool {
    &&& offs.len() == n + 1
    &&& forall|i: int| 0 <= i < n ==> 0 <= #[trigger] offs[i] <= offs[i + 1] <= blen
}

/// The bytes of value `x`.
pub open spec fn val(offs: Seq<i64>, bytes: Seq<u8>, x: int) -> Seq<u8> {
    bytes.subrange(offs[x] as int, offs[x + 1] as int)
}

/// The bit of row `x` in a bitmap whose bit 0 is row `lo`.
pub open spec fn row_bit(words: Seq<u64>, lo: int, x: int) -> bool {
    bit(words[(x - lo) / 64], ((x - lo) % 64) as u64)
}

/// Offsets are monotone over any pair of rows.
pub proof fn lemma_offs_mono(offs: Seq<i64>, n: int, blen: int, a: int, b: int)
    requires offs_wf(offs, n, blen), 0 <= a < b <= n,
    ensures 0 <= offs[a] <= offs[b] <= blen,
    decreases b - a,
{
    if b > a + 1 {
        lemma_offs_mono(offs, n, blen, a, b - 1);
        assert(offs[b - 1] <= offs[b]);
    } else {
        assert(offs[a] <= offs[a + 1]);
    }
}

/// An occurrence of the literal at offset `j` of row `x` sits inside the row, and its bytes are the literal's.
proof fn lemma_occ_inside(offs: Seq<i64>, bytes: Seq<u8>, n: int, x: int, lit: Seq<u8>, j: int)
    requires offs_wf(offs, n, bytes.len() as int), 0 <= x < n, lit.len() >= 1, sub_at(val(offs, bytes, x), lit, j),
    ensures
        0 <= j, offs[x] + j + lit.len() <= offs[x + 1],
        forall|k: int| 0 <= k < lit.len() ==> #[trigger] bytes[offs[x] + j + k] == lit[k],
{
    let v = val(offs, bytes, x);
    assert(offs[x] <= offs[x + 1] <= bytes.len());
    assert forall|k: int| 0 <= k < lit.len() implies #[trigger] bytes[offs[x] + j + k] == lit[k] by {
        assert(v.subrange(j, j + lit.len())[k] == lit[k]);
        assert(v[j + k] == bytes[offs[x] + j + k]);
    }
}

/// The row holding a byte position is unique.
proof fn lemma_row_unique(offs: Seq<i64>, n: int, blen: int, x: int, r: int, p: int)
    requires
        offs_wf(offs, n, blen), 0 <= x < n, 0 <= r < n,
        offs[x] <= p < offs[x + 1], offs[r] <= p < offs[r + 1],
    ensures x == r,
{
    if x < r {
        if x + 1 < r { lemma_offs_mono(offs, n, blen, x + 1, r); }
    } else if r < x {
        if r + 1 < x { lemma_offs_mono(offs, n, blen, r + 1, x); }
    }
}

/// Setting bit `t` of a word keeps every other bit and sets bit `t`.
proof fn lemma_bit_or(m: u64, t: u64, u: u64)
    requires t < 64, u < 64,
    ensures bit(m | (1u64 << t), u) == (u == t || bit(m, u)),
{
    assert((t < 64 && u < 64) ==> ((((m | (1u64 << t)) >> u) & 1u64 == 1u64) == (u == t || (m >> u) & 1u64 == 1u64)))
        by (bit_vector);
}

/// The OR of bytes is ASCII exactly when both are.
proof fn lemma_or_ascii(a: u8, b: u8)
    ensures ((a | b) < 0x80u8) == (a < 0x80u8 && b < 0x80u8),
{
    assert(((a | b) < 0x80u8) == (a < 0x80u8 && b < 0x80u8)) by (bit_vector);
}

/// The OR of flags is zero exactly when both are.
proof fn lemma_or_zero(a: u8, b: u8)
    ensures ((a | b) == 0u8) == (a == 0u8 && b == 0u8),
{
    assert(((a | b) == 0u8) == (a == 0u8 && b == 0u8)) by (bit_vector);
}

/// The AND of four 0/1 flags is 1 when all are 1.
proof fn lemma_flags(f0: u8, f1: u8, f2: u8, f3: u8)
    requires f0 <= 1, f1 <= 1, f2 <= 1, f3 <= 1,
    ensures (f0 == 1 && f1 == 1 && f2 == 1 && f3 == 1) ==> f0 & f1 & f2 & f3 == 1u8,
{
    assert((f0 == 1u8 && f1 == 1u8 && f2 == 1u8 && f3 == 1u8) ==> f0 & f1 & f2 & f3 == 1u8) by (bit_vector);
}

/// Masking with all ones keeps a byte; masking with zero clears it.
proof fn lemma_mask(b: u8)
    ensures b & 0xffu8 == b, b & 0u8 == 0u8,
{
    assert(b & 0xffu8 == b && b & 0u8 == 0u8) by (bit_vector);
}

/// The bitmap holds only true matches of rows `lo..hi`, no bit of a row at or past `hi`, and the bit of every row
/// with an occurrence starting before byte `p` (opaque: revealed in the lemmas that move it).
#[verifier::opaque]
pub open spec fn bits_inv(offs: Seq<i64>, bytes: Seq<u8>, lo: int, hi: int, lit: Seq<u8>, words: Seq<u64>, p: int) -> bool {
    &&& forall|x: int| lo <= x < hi && #[trigger] row_bit(words, lo, x) ==> has_sub(val(offs, bytes, x), lit)
    &&& forall|x: int| hi <= x < lo + 64 * words.len() ==> !#[trigger] row_bit(words, lo, x)
    &&& forall|x: int, j: int| lo <= x < hi && #[trigger] sub_at(val(offs, bytes, x), lit, j) && offs[x] + j < p
        ==> row_bit(words, lo, x)
}

/// Byte `q` starts with the literal's first `min(m, 4)` bytes.
pub open spec fn pre4(bytes: Seq<u8>, q: int, lit: Seq<u8>) -> bool {
    forall|k: int| 0 <= k < lit.len() && k < 4 ==> #[trigger] bytes[q + k] == lit[k]
}

/// The comparison pattern of the first four literal bytes: masks (all ones below the literal's length) and bytes.
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

/// The comparison pattern of `lit`.
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

/// Group `p..p + 64` (with 3 bytes after it): the OR of its bytes, and a flag that is zero only when no position
/// of the group starts with the literal's prefix.
fn group_flags(bytes: &[u8], p: usize, pf: &Prefix, Ghost(lit): Ghost<Seq<u8>>) -> (r: (u8, u8))
    requires p + 67 <= bytes@.len(), prefix_ok(*pf, lit),
    ensures
        (r.0 < 0x80u8) == (forall|q: int| p <= q < p + 64 ==> #[trigger] bytes@[q] < 0x80u8),
        r.1 == 0u8 ==> forall|q: int| p <= q < p + 64 ==> !#[trigger] pre4(bytes@, q, lit),
    no_unwind
{
    let (_, tail) = bytes.split_at(p);
    let (blk, _) = tail.split_at(67);
    assert(blk@ =~= bytes@.subrange(p as int, p + 67));
    let mut a: u8 = 0;
    let mut any: u8 = 0;
    let mut j: usize = 0;
    while j < 64
        invariant
            j <= 64, p + 67 <= bytes@.len(), blk@ == bytes@.subrange(p as int, p + 67), prefix_ok(*pf, lit),
            (a < 0x80u8) == (forall|q: int| p <= q < p + j ==> #[trigger] bytes@[q] < 0x80u8),
            any == 0u8 ==> forall|q: int| p <= q < p + j ==> !#[trigger] pre4(bytes@, q, lit),
        decreases 64 - j,
    {
        let b = blk[j];
        // one 0/1 flag per compared byte (branch-free, so the loop vectorizes)
        let f0: u8 = if b == pf.c0 { 1 } else { 0 };
        let f1: u8 = if (blk[j + 1] & pf.k1) == pf.c1 { 1 } else { 0 };
        let f2: u8 = if (blk[j + 2] & pf.k2) == pf.c2 { 1 } else { 0 };
        let f3: u8 = if (blk[j + 3] & pf.k3) == pf.c3 { 1 } else { 0 };
        let t: u8 = f0 & f1 & f2 & f3;
        proof {
            lemma_or_ascii(a, b);
            lemma_or_zero(any, t);
            lemma_flags(f0, f1, f2, f3);
            let q = p + j;
            assert(blk@[j as int] == bytes@[q]);
            if pre4(bytes@, q, lit) {
                // a prefix at q passes every masked comparison
                assert(bytes@[q + 0] == lit[0]);
                lemma_mask(blk@[j + 1]);
                lemma_mask(blk@[j + 2]);
                lemma_mask(blk@[j + 3]);
                assert(blk@[j + 1] == bytes@[q + 1] && blk@[j + 2] == bytes@[q + 2] && blk@[j + 3] == bytes@[q + 3]);
                if lit.len() > 1 { assert(bytes@[q + 1] == lit[1]); }
                if lit.len() > 2 { assert(bytes@[q + 2] == lit[2]); }
                if lit.len() > 3 { assert(bytes@[q + 3] == lit[3]); }
                assert(t == 1u8);
            }
        }
        a = a | b;
        any = any | t;
        j = j + 1;
    }
    (a, any)
}

/// No occurrence inside a row starts at a byte other than the literal's first: the invariant moves past `p`.
proof fn lemma_step_other(offs: Seq<i64>, bytes: Seq<u8>, n: int, lo: int, hi: int, lit: Seq<u8>, words: Seq<u64>, p: int)
    requires
        offs_wf(offs, n, bytes.len() as int), 0 <= lo < hi <= n, lit.len() >= 1, 0 <= p < bytes.len(),
        bits_inv(offs, bytes, lo, hi, lit, words, p), bytes[p] != lit[0],
    ensures bits_inv(offs, bytes, lo, hi, lit, words, p + 1),
{
    reveal(bits_inv);
    assert forall|x: int, jj: int| lo <= x < hi && #[trigger] sub_at(val(offs, bytes, x), lit, jj)
        && offs[x] + jj < p + 1 implies row_bit(words, lo, x) by {
        if offs[x] + jj == p {
            lemma_occ_inside(offs, bytes, n, x, lit, jj);
            assert(bytes[offs[x] + jj + 0] == lit[0]);
        }
    }
}

/// Row `r` holds byte `p`, and its bit is set when the literal occurs at `p` inside it (`words` is `w0` with that
/// bit possibly set): the invariant moves past `p`.
proof fn lemma_step_row(offs: Seq<i64>, bytes: Seq<u8>, n: int, lo: int, hi: int, lit: Seq<u8>, w0: Seq<u64>,
    words: Seq<u64>, p: int, r: int)
    requires
        offs_wf(offs, n, bytes.len() as int), 0 <= lo <= r < hi <= n, lit.len() >= 1,
        offs[r] <= p < offs[r + 1], words.len() == w0.len(), hi - lo <= 64 * w0.len(),
        bits_inv(offs, bytes, lo, hi, lit, w0, p),
        forall|x: int| lo <= x < lo + 64 * w0.len() ==> #[trigger] row_bit(words, lo, x)
            == (row_bit(w0, lo, x) || (x == r && sub_at(val(offs, bytes, r), lit, p - offs[r]))),
        sub_at(val(offs, bytes, r), lit, p - offs[r]) ==> row_bit(words, lo, r),
    ensures bits_inv(offs, bytes, lo, hi, lit, words, p + 1),
{
    reveal(bits_inv);
    assert forall|x: int, jj: int| lo <= x < hi && #[trigger] sub_at(val(offs, bytes, x), lit, jj)
        && offs[x] + jj < p + 1 implies row_bit(words, lo, x) by {
        assert(row_bit(words, lo, x) == (row_bit(w0, lo, x) || (x == r && sub_at(val(offs, bytes, r), lit, p - offs[r]))));
        if offs[x] + jj < p {
            assert(row_bit(w0, lo, x));
        } else {
            lemma_occ_inside(offs, bytes, n, x, lit, jj);
            lemma_row_unique(offs, n, bytes.len() as int, x, r, p);
        }
    }
    assert forall|x: int| lo <= x < hi && #[trigger] row_bit(words, lo, x) implies has_sub(val(offs, bytes, x), lit) by {
        assert(row_bit(words, lo, x) == (row_bit(w0, lo, x) || (x == r && sub_at(val(offs, bytes, r), lit, p - offs[r]))));
    }
    assert forall|x: int| hi <= x < lo + 64 * words.len() implies !#[trigger] row_bit(words, lo, x) by {
        assert(row_bit(words, lo, x) == (row_bit(w0, lo, x) || (x == r && sub_at(val(offs, bytes, r), lit, p - offs[r]))));
    }
}

/// Sets the bit of row `r` (bit 0 is row `lo`).
fn set_row_bit(words: &mut Vec<u64>, lo: usize, r: usize)
    requires lo <= r, r - lo < 64 * old(words)@.len(),
    ensures
        final(words)@.len() == old(words)@.len(),
        forall|x: int| lo <= x < lo + 64 * old(words)@.len() ==> #[trigger] row_bit(final(words)@, lo as int, x)
            == (x == r || row_bit(old(words)@, lo as int, x)),
    no_unwind
{
    let ghost w0 = words@;
    let ghost nw = words@.len();
    let wi = (r - lo) / 64;
    let t = ((r - lo) % 64) as u64;
    words[wi] = words[wi] | (1u64 << t);
    proof {
        assert forall|x: int| lo <= x < lo + 64 * nw implies #[trigger] row_bit(words@, lo as int, x)
            == (x == r || row_bit(w0, lo as int, x)) by {
            let xi = (x - lo) / 64;
            let xt = ((x - lo) % 64) as u64;
            lemma_bit_or(w0[wi as int], t, xt);
            if xi != wi {
                assert(words@[xi] == w0[xi]);
                assert(x != r);
            } else if xt == t {
                assert(x - lo == 64 * xi + xt);
                assert(x == r);
            } else {
                assert(x != r);
            }
        }
    }
}

/// The row holding byte `p`: the first row from the cursor `r` whose end is past `p`.
fn row_of(offs: &[i64], hi: usize, r: usize, p: usize, Ghost(n): Ghost<int>, Ghost(blen): Ghost<int>) -> (r2: usize)
    requires offs_wf(offs@, n, blen), r < hi <= n, offs@[r as int] <= p < offs@[hi as int],
    ensures r <= r2 < hi, offs@[r2 as int] <= p < offs@[r2 + 1],
    no_unwind
{
    let ghost offv = offs@;
    let mut x = r;
    loop
        invariant offs_wf(offv, n, blen), offv == offs@, r <= x < hi <= n, offv[x as int] <= p < offv[hi as int],
        decreases hi - x,
    {
        proof {
            assert(0 <= offv[x as int] <= offv[x + 1] <= blen);
            assert((p as i64) as int == p as int);
        }
        let nx = offs[x + 1];
        if (p as i64) < nx {
            return x;
        }
        proof {
            if x + 1 == hi { assert(false); }
        }
        x = x + 1;
    }
}

/// The per-byte step at `p`: when byte `p` is the literal's first byte, the cursor moves to the row holding `p`
/// and the row's bit is set if the whole literal occurs at `p` inside that row. Returns the cursor.
fn step(offs: &[i64], bytes: &[u8], lo: usize, hi: usize, lit: &Vec<u8>, m: usize, c0: u8, words: &mut Vec<u64>,
    p: usize, r: usize, Ghost(n): Ghost<int>, Ghost(e0): Ghost<int>) -> (r2: usize)
    requires
        offs_wf(offs@, n, bytes@.len() as int), bytes@.len() <= usize::MAX, lo <= r < hi <= n, e0 == offs@[hi as int],
        offs@[r as int] <= p < e0, m == lit@.len(), m >= 1, c0 == lit@[0], hi - lo <= 64 * old(words)@.len(),
        bits_inv(offs@, bytes@, lo as int, hi as int, lit@, old(words)@, p as int),
    ensures
        final(words)@.len() == old(words)@.len(), lo <= r2 < hi, offs@[r2 as int] <= p,
        bits_inv(offs@, bytes@, lo as int, hi as int, lit@, final(words)@, p + 1),
    no_unwind
{
    let ghost w0 = words@;
    proof { lemma_offs_mono(offs@, n, bytes@.len() as int, r as int, hi as int); }
    if bytes[p] != c0 {
        proof { lemma_step_other(offs@, bytes@, n, lo as int, hi as int, lit@, words@, p as int); }
        return r;
    }
    let rw = row_of(offs, hi, r, p, Ghost(n), Ghost(bytes@.len() as int));
    proof { assert(0 <= offs@[rw as int] <= offs@[rw + 1] <= bytes@.len()); }
    let rend = offs[rw + 1] as usize;
    let found = rend - p >= m && lit_at(bytes, p, rend, lit, m);
    let ghost j = p - offs@[rw as int];
    proof { lemma_found(offs@, bytes@, n, rw as int, lit@, p as int, found); }
    if found {
        set_row_bit(words, lo, rw);
    }
    proof {
        let occ = sub_at(val(offs@, bytes@, rw as int), lit@, p - offs@[rw as int]);
        assert forall|x: int| lo <= x < lo + 64 * w0.len() implies #[trigger] row_bit(words@, lo as int, x)
            == (row_bit(w0, lo as int, x) || (x == rw && occ)) by {
            if !found { assert(words@ == w0); }
        }
        if occ {
            assert(rw - lo < 64 * w0.len());
            assert(row_bit(words@, lo as int, rw as int) == (row_bit(w0, lo as int, rw as int) || (rw == rw && occ)));
        }
        lemma_step_row(offs@, bytes@, n, lo as int, hi as int, lit@, w0, words@, p as int, rw as int);
    }
    rw
}

/// `found` (the literal fits in row `r` after `p` and its bytes match) is the occurrence at `p` inside row `r`.
proof fn lemma_found(offs: Seq<i64>, bytes: Seq<u8>, n: int, r: int, lit: Seq<u8>, p: int, found: bool)
    requires
        offs_wf(offs, n, bytes.len() as int), 0 <= r < n, lit.len() >= 1, offs[r] <= p < offs[r + 1],
        found == (p + lit.len() <= offs[r + 1] && forall|k: int| 0 <= k < lit.len() ==> #[trigger] bytes[p + k] == lit[k]),
    ensures found == sub_at(val(offs, bytes, r), lit, p - offs[r]),
{
    let j = p - offs[r];
    let v = val(offs, bytes, r);
    let m = lit.len() as int;
    assert(0 <= offs[r] <= offs[r + 1] <= bytes.len());
    if found {
        assert(v.subrange(j, j + m) =~= lit) by {
            assert forall|k: int| 0 <= k < m implies v.subrange(j, j + m)[k] == lit[k] by {
                assert(bytes[p + k] == lit[k]);
            }
        }
    }
    if sub_at(v, lit, j) {
        lemma_occ_inside(offs, bytes, n, r, lit, j);
        assert forall|k: int| 0 <= k < m implies #[trigger] bytes[p + k] == lit[k] by {
            assert(bytes[offs[r] + j + k] == lit[k]);
        }
    }
}

/// Whether `bytes[p..p + m]` is the literal (`p + m <= hi`).
fn lit_at(bytes: &[u8], p: usize, hi: usize, lit: &Vec<u8>, m: usize) -> (r: bool)
    requires p + m <= hi <= bytes@.len(), m == lit@.len(),
    ensures r == forall|k: int| 0 <= k < m ==> #[trigger] bytes@[p + k] == lit@[k],
    no_unwind
{
    let mut k: usize = 0;
    while k < m
        invariant k <= m, p + m <= hi <= bytes@.len(), m == lit@.len(),
            forall|j: int| 0 <= j < k ==> #[trigger] bytes@[p + j] == lit@[j],
        decreases m - k,
    {
        if bytes[p + k] != lit[k] {
            return false;
        }
        k = k + 1;
    }
    true
}

/// A group whose flag is zero has no occurrence inside a row: the bitmap invariant moves past it.
proof fn lemma_skip_group(offs: Seq<i64>, bytes: Seq<u8>, n: int, lo: int, hi: int, lit: Seq<u8>, words: Seq<u64>, p: int)
    requires
        offs_wf(offs, n, bytes.len() as int), 0 <= lo < hi <= n, lit.len() >= 1,
        bits_inv(offs, bytes, lo, hi, lit, words, p),
        forall|q: int| p <= q < p + 64 ==> !#[trigger] pre4(bytes, q, lit),
    ensures bits_inv(offs, bytes, lo, hi, lit, words, p + 64),
{
    reveal(bits_inv);
    assert forall|x: int, jj: int| lo <= x < hi && #[trigger] sub_at(val(offs, bytes, x), lit, jj)
        && offs[x] + jj < p + 64 implies row_bit(words, lo, x) by {
        if offs[x] + jj >= p {
            lemma_occ_inside(offs, bytes, n, x, lit, jj);
            let q = offs[x] + jj;
            assert(pre4(bytes, q, lit)) by {
                assert forall|k: int| 0 <= k < lit.len() && k < 4 implies #[trigger] bytes[q + k] == lit[k] by {
                    assert(bytes[offs[x] + jj + k] == lit[k]);
                }
            }
        }
    }
}

/// The scan state at byte `p` of the run `offs[lo]..offs[hi]`: cursor, bitmap invariant and the ASCII accumulator
/// (opaque: revealed in the lemmas that move it).
#[verifier::opaque]
pub open spec fn run_ok(offs: Seq<i64>, bytes: Seq<u8>, n: int, lo: int, hi: int, lit: Seq<u8>, words: Seq<u64>,
    p: int, r: int, acc: u8) -> bool
{
    &&& offs_wf(offs, n, bytes.len() as int) && 0 <= lo < hi <= n && lit.len() >= 1 && bytes.len() <= usize::MAX
    &&& 0 <= offs[lo] <= p <= offs[hi] <= bytes.len() && hi - lo <= 64 * words.len()
    &&& lo <= r < hi && offs[r] <= p
    &&& bits_inv(offs, bytes, lo, hi, lit, words, p)
    &&& (acc < 0x80u8) == (forall|q: int| offs[lo] <= q < p ==> #[trigger] bytes[q] < 0x80u8)
}

/// The ASCII accumulator after one more chunk `p..p2` whose OR is `a`.
proof fn lemma_acc_step(bytes: Seq<u8>, s0: int, p: int, p2: int, acc: u8, a: u8)
    requires
        s0 <= p <= p2 <= bytes.len(),
        (acc < 0x80u8) == (forall|q: int| s0 <= q < p ==> #[trigger] bytes[q] < 0x80u8),
        (a < 0x80u8) == (forall|q: int| p <= q < p2 ==> #[trigger] bytes[q] < 0x80u8),
    ensures ((acc | a) < 0x80u8) == (forall|q: int| s0 <= q < p2 ==> #[trigger] bytes[q] < 0x80u8),
{
    lemma_or_ascii(acc, a);
    if (acc | a) < 0x80u8 {
        assert forall|q: int| s0 <= q < p2 implies #[trigger] bytes[q] < 0x80u8 by {
            if q < p { assert(acc < 0x80u8); } else { assert(a < 0x80u8); }
        }
    }
}

/// The facts of a scan state the loop bodies need (the bitmap invariant stays opaque).
proof fn lemma_run_facts(offs: Seq<i64>, bytes: Seq<u8>, n: int, lo: int, hi: int, lit: Seq<u8>, words: Seq<u64>,
    p: int, r: int, acc: u8)
    requires run_ok(offs, bytes, n, lo, hi, lit, words, p, r, acc),
    ensures
        offs_wf(offs, n, bytes.len() as int), 0 <= lo < hi <= n, lit.len() >= 1, bytes.len() <= usize::MAX,
        0 <= offs[lo] <= p <= offs[hi] <= bytes.len(), hi - lo <= 64 * words.len(), lo <= r < hi, offs[r] <= p,
        bits_inv(offs, bytes, lo, hi, lit, words, p),
{
    reveal(run_ok);
}

/// The scan state after the bytes `p..p2`: the bitmap invariant moved from `w0` at `p` to `words` at `p2`, the
/// cursor moved forward, and `a` is the OR of the bytes.
proof fn lemma_run_advance(offs: Seq<i64>, bytes: Seq<u8>, n: int, lo: int, hi: int, lit: Seq<u8>, w0: Seq<u64>,
    words: Seq<u64>, p: int, p2: int, r: int, r2: int, acc: u8, a: u8)
    requires
        run_ok(offs, bytes, n, lo, hi, lit, w0, p, r, acc), p <= p2 <= offs[hi], words.len() == w0.len(),
        lo <= r2 < hi, offs[r2] <= p2,
        bits_inv(offs, bytes, lo, hi, lit, words, p2),
        (a < 0x80u8) == (forall|q: int| p <= q < p2 ==> #[trigger] bytes[q] < 0x80u8),
    ensures run_ok(offs, bytes, n, lo, hi, lit, words, p2, r2, acc | a),
{
    reveal(run_ok);
    lemma_acc_step(bytes, offs[lo] as int, p, p2, acc, a);
}

/// The bytes `p..pe` of the run one at a time (`step`), without the ASCII accumulator: returns the cursor.
fn scan_bytes(offs: &[i64], bytes: &[u8], n: usize, lo: usize, hi: usize, lit: &Vec<u8>, m: usize,
    words: &mut Vec<u64>, p: usize, pe: usize, r: usize) -> (r2: usize)
    requires
        offs_wf(offs@, n as int, bytes@.len() as int), bytes@.len() <= usize::MAX, lo < hi <= n, m == lit@.len(), m >= 1,
        p <= pe <= offs@[hi as int], hi - lo <= 64 * old(words)@.len(),
        lo <= r < hi, offs@[r as int] <= p,
        bits_inv(offs@, bytes@, lo as int, hi as int, lit@, old(words)@, p as int),
    ensures
        final(words)@.len() == old(words)@.len(), lo <= r2 < hi, offs@[r2 as int] <= pe,
        bits_inv(offs@, bytes@, lo as int, hi as int, lit@, final(words)@, pe as int),
    no_unwind
{
    let ghost nw = words@.len();
    let c0 = lit[0];
    let mut q = p;
    let mut r = r;
    while q < pe
        invariant
            offs_wf(offs@, n as int, bytes@.len() as int), bytes@.len() <= usize::MAX, lo < hi <= n, m == lit@.len(), m >= 1,
            c0 == lit@[0], p <= q <= pe, pe <= offs@[hi as int], words@.len() == nw, hi - lo <= 64 * nw,
            lo <= r < hi, offs@[r as int] <= q,
            bits_inv(offs@, bytes@, lo as int, hi as int, lit@, words@, q as int),
        decreases pe - q,
    {
        r = step(offs, bytes, lo, hi, lit, m, c0, words, q, r, Ghost(n as int), Ghost(offs@[hi as int] as int));
        q = q + 1;
    }
    r
}

/// Whole groups of 64 bytes from `p` while 67 bytes remain in the run: returns the next byte, cursor and accumulator.
fn scan_groups(offs: &[i64], bytes: &[u8], n: usize, lo: usize, hi: usize, lit: &Vec<u8>, m: usize, pf: &Prefix,
    words: &mut Vec<u64>, p: usize, r: usize, acc: u8) -> (out: (usize, usize, u8))
    requires
        run_ok(offs@, bytes@, n as int, lo as int, hi as int, lit@, old(words)@, p as int, r as int, acc),
        m == lit@.len(), prefix_ok(*pf, lit@),
    ensures
        final(words)@.len() == old(words)@.len(),
        run_ok(offs@, bytes@, n as int, lo as int, hi as int, lit@, final(words)@, out.0 as int, out.1 as int, out.2),
    no_unwind
{
    let ghost offv = offs@;
    let ghost bv = bytes@;
    let ghost litv = lit@;
    let ghost nw = words@.len();
    proof { lemma_run_facts(offv, bv, n as int, lo as int, hi as int, litv, words@, p as int, r as int, acc); }
    let e0 = offs[hi] as usize;
    let c0 = pf.c0;
    let mut pp = p;
    let mut rr = r;
    let mut aa = acc;
    while e0 >= 67 && pp <= e0 - 67
        invariant
            offv == offs@, bv == bytes@, litv == lit@, m == litv.len(), prefix_ok(*pf, litv), c0 == litv[0],
            e0 as int == offv[hi as int], words@.len() == nw,
            run_ok(offv, bv, n as int, lo as int, hi as int, litv, words@, pp as int, rr as int, aa),
        decreases e0 - pp,
    {
        proof { lemma_run_facts(offv, bv, n as int, lo as int, hi as int, litv, words@, pp as int, rr as int, aa); }
        let (a, any) = group_flags(bytes, pp, pf, Ghost(litv));
        let ghost w0 = words@;
        let ghost r0 = rr;
        let ghost a0 = aa;
        if any == 0 {
            proof { lemma_skip_group(offv, bv, n as int, lo as int, hi as int, litv, words@, pp as int); }
        } else {
            rr = scan_bytes(offs, bytes, n, lo, hi, lit, m, words, pp, pp + 64, rr);
        }
        aa = aa | a;
        proof {
            lemma_run_advance(offv, bv, n as int, lo as int, hi as int, litv, w0, words@, pp as int, pp + 64, r0 as int,
                rr as int, a0, a);
        }
        pp = pp + 64;
    }
    (pp, rr, aa)
}

/// The remaining bytes of the run, one at a time: returns the cursor and accumulator at the run's end.
fn scan_tail(offs: &[i64], bytes: &[u8], n: usize, lo: usize, hi: usize, lit: &Vec<u8>, m: usize,
    words: &mut Vec<u64>, p: usize, r: usize, acc: u8) -> (out: (usize, u8))
    requires
        run_ok(offs@, bytes@, n as int, lo as int, hi as int, lit@, old(words)@, p as int, r as int, acc),
        m == lit@.len(),
    ensures
        final(words)@.len() == old(words)@.len(),
        run_ok(offs@, bytes@, n as int, lo as int, hi as int, lit@, final(words)@, offs@[hi as int] as int, out.0 as int, out.1),
    no_unwind
{
    let ghost offv = offs@;
    let ghost bv = bytes@;
    let ghost litv = lit@;
    let ghost nw = words@.len();
    proof { lemma_run_facts(offv, bv, n as int, lo as int, hi as int, litv, words@, p as int, r as int, acc); }
    let e0 = offs[hi] as usize;
    let c0 = lit[0];
    let mut pp = p;
    let mut rr = r;
    let mut aa = acc;
    while pp < e0
        invariant
            offv == offs@, bv == bytes@, litv == lit@, m == litv.len(), c0 == litv[0],
            e0 as int == offv[hi as int], words@.len() == nw,
            run_ok(offv, bv, n as int, lo as int, hi as int, litv, words@, pp as int, rr as int, aa),
        decreases e0 - pp,
    {
        proof { lemma_run_facts(offv, bv, n as int, lo as int, hi as int, litv, words@, pp as int, rr as int, aa); }
        let b = bytes[pp];
        let ghost w0 = words@;
        let ghost r0 = rr;
        let ghost a0 = aa;
        rr = step(offs, bytes, lo, hi, lit, m, c0, words, pp, rr, Ghost(n as int), Ghost(e0 as int));
        aa = aa | b;
        proof {
            assert((b < 0x80u8) == (forall|q: int| pp <= q < pp + 1 ==> #[trigger] bv[q] < 0x80u8)) by {
                assert forall|q: int| pp <= q < pp + 1 implies bv[q] == b by {}
            }
            lemma_run_advance(offv, bv, n as int, lo as int, hi as int, litv, w0, words@, pp as int, pp + 1, r0 as int,
                rr as int, a0, b);
        }
        pp = pp + 1;
    }
    proof { lemma_run_facts(offv, bv, n as int, lo as int, hi as int, litv, words@, pp as int, rr as int, aa); }
    (rr, aa)
}

/// At the run's end the bitmap is exact for rows `lo..hi`, and an ASCII accumulator makes every row ASCII.
proof fn lemma_run_end(offs: Seq<i64>, bytes: Seq<u8>, n: int, lo: int, hi: int, lit: Seq<u8>, words: Seq<u64>,
    r: int, acc: u8)
    requires run_ok(offs, bytes, n, lo, hi, lit, words, offs[hi] as int, r, acc),
    ensures
        forall|x: int| lo <= x < hi ==> #[trigger] row_bit(words, lo, x) == has_sub(val(offs, bytes, x), lit),
        acc < 0x80u8 ==> forall|x: int| lo <= x < hi ==> #[trigger] ascii(val(offs, bytes, x)),
{
    reveal(run_ok);
    reveal(bits_inv);
    assert forall|x: int| lo <= x < hi implies #[trigger] row_bit(words, lo, x) == has_sub(val(offs, bytes, x), lit) by {
        if has_sub(val(offs, bytes, x), lit) {
            let jj = choose|jj: int| #[trigger] sub_at(val(offs, bytes, x), lit, jj);
            lemma_occ_inside(offs, bytes, n, x, lit, jj);
            if x + 1 < hi { lemma_offs_mono(offs, n, bytes.len() as int, x + 1, hi); }
        }
    }
    if acc < 0x80u8 {
        assert forall|x: int| lo <= x < hi implies #[trigger] ascii(val(offs, bytes, x)) by {
            if lo < x { lemma_offs_mono(offs, n, bytes.len() as int, lo, x); }
            if x + 1 < hi { lemma_offs_mono(offs, n, bytes.len() as int, x + 1, hi); }
            assert(offs[x] <= offs[x + 1]);
            let v = val(offs, bytes, x);
            assert forall|i: int| 0 <= i < v.len() implies #[trigger] v[i] < 0x80u8 by {
                assert(v[i] == bytes[offs[x] + i]);
            }
        }
    }
}

/// Sets the bits of rows `lo..hi` whose values contain `lit` in the zeroed bitmap `words` (bit 0 is row `lo`), and
/// returns whether every byte of those rows is ASCII.
pub fn contains_bits(offs: &[i64], bytes: &[u8], n: usize, lo: usize, hi: usize, lit: &Vec<u8>, m: usize,
    words: &mut Vec<u64>) -> (asc: bool)
    requires
        offs_wf(offs@, n as int, bytes@.len() as int), bytes@.len() <= usize::MAX, lo <= hi <= n, m == lit@.len(), m >= 1,
        hi - lo <= 64 * old(words)@.len(), forall|i: int| 0 <= i < old(words)@.len() ==> #[trigger] old(words)@[i] == 0u64,
    ensures
        final(words)@.len() == old(words)@.len(),
        forall|x: int| lo <= x < hi ==> #[trigger] row_bit(final(words)@, lo as int, x) == has_sub(val(offs@, bytes@, x), lit@),
        forall|x: int| hi <= x < lo + 64 * final(words)@.len() ==> !#[trigger] row_bit(final(words)@, lo as int, x),
        asc ==> forall|x: int| lo <= x < hi ==> #[trigger] ascii(val(offs@, bytes@, x)),
    no_unwind
{
    let ghost nw = words@.len();
    proof {
        assert forall|x: int| lo <= x < lo + 64 * nw implies !#[trigger] row_bit(words@, lo as int, x) by {
            assert(words@[(x - lo) / 64] == 0u64);
            lemma_bit_zero(((x - lo) % 64) as u64);
        }
    }
    if lo == hi {
        return true;
    }
    proof { lemma_offs_mono(offs@, n as int, bytes@.len() as int, lo as int, hi as int); }
    let s0 = offs[lo] as usize;
    let pf = prefix_of(lit, m);
    proof {
        reveal(bits_inv);
        reveal(run_ok);
        assert forall|x: int, j: int| lo <= x < hi && #[trigger] sub_at(val(offs@, bytes@, x), lit@, j)
            && offs@[x] + j < s0 implies row_bit(words@, lo as int, x) by {
            lemma_occ_inside(offs@, bytes@, n as int, x, lit@, j);
            if lo < x { lemma_offs_mono(offs@, n as int, bytes@.len() as int, lo as int, x); }
        }
        assert(bits_inv(offs@, bytes@, lo as int, hi as int, lit@, words@, s0 as int));
        assert(run_ok(offs@, bytes@, n as int, lo as int, hi as int, lit@, words@, s0 as int, lo as int, 0u8));
    }
    let (p, r, acc) = scan_groups(offs, bytes, n, lo, hi, lit, m, &pf, words, s0, lo, 0u8);
    let (r, acc) = scan_tail(offs, bytes, n, lo, hi, lit, m, words, p, r, acc);
    proof { lemma_run_end(offs@, bytes@, n as int, lo as int, hi as int, lit@, words@, r as int, acc); }
    acc < 0x80u8
}

} // verus!
