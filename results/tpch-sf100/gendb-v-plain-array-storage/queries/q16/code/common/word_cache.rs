//! A direct-mapped cache in front of a `TextDict` for keys of 8 to 32 bytes: a key is identified by its length and
//! four overlapping little-endian words (at 0, 8, 16 and `len - 8`, clipped to `len - 8`), which together cover
//! every byte (`lemma_words_eq`). A lookup computes the row's words, reads one slot and compares four words and
//! the length; it answers an id only when they all match (so the bytes equal that key), and `ABSENT` otherwise —
//! the caller then asks the dictionary. Keys whose slot is taken are simply not cached.
//!
//! Layout: one `Vec<u64>` of `SLOT = 8` cells per slot (length, four words, id, two unused), so a slot is one
//! 64-byte line and a lookup reads it through one exact subslice.
use vstd::prelude::*;
use crate::agent::common::text_dict::{word_spec, lemma_word_eq, word_at, ABSENT};

verus! {

/// The word offsets of a key of length `n` (`8 <= n <= 32`).
pub open spec fn off1(n: int) -> int { if n - 8 < 8 { n - 8 } else { 8 } }
pub open spec fn off2(n: int) -> int { if n - 8 < 16 { n - 8 } else { 16 } }

/// Lengths the cache handles.
pub open spec fn wordable(n: int) -> bool { 8 <= n <= 32 }

/// `s` has a cached length and these four words.
pub open spec fn words_match(s: Seq<u8>, w0: u64, w1: u64, w2: u64, w3: u64) -> bool {
    let n = s.len() as int;
    &&& wordable(n)
    &&& word_spec(s, 0) == w0 && word_spec(s, off1(n)) == w1 && word_spec(s, off2(n)) == w2 && word_spec(s, n - 8) == w3
}

/// Two strings of one cached length with the same four words are equal.
pub proof fn lemma_words_eq(x: Seq<u8>, y: Seq<u8>, w0: u64, w1: u64, w2: u64, w3: u64)
    requires x.len() == y.len(), words_match(x, w0, w1, w2, w3), words_match(y, w0, w1, w2, w3),
    ensures x == y,
{
    let n = x.len() as int;
    let (o1, o2, o3) = (off1(n), off2(n), n - 8);
    lemma_word_eq(x, 0, y, 0);
    lemma_word_eq(x, o1, y, o1);
    lemma_word_eq(x, o2, y, o2);
    lemma_word_eq(x, o3, y, o3);
    assert forall|i: int| 0 <= i < n implies x[i] == y[i] by {
        if i < 8 {
            assert(x[0 + i] == y[0 + i]);
        } else if i < 16 && o1 == 8 {
            assert(x[o1 + (i - o1)] == y[o1 + (i - o1)]);
        } else if i < 24 && o2 == 16 {
            assert(x[o2 + (i - o2)] == y[o2 + (i - o2)]);
        } else {
            assert(o3 <= i);
            assert(x[o3 + (i - o3)] == y[o3 + (i - o3)]);
        }
    }
    assert(x =~= y);
}

/// A word of a subrange is the word of the whole at the shifted offset.
proof fn lemma_sub_word(b: Seq<u8>, lo: int, hi: int, o: int)
    requires 0 <= lo <= hi <= b.len(), 0 <= o, o + 8 <= hi - lo,
    ensures word_spec(b.subrange(lo, hi), o) == word_spec(b, lo + o),
{
    let s = b.subrange(lo, hi);
    assert(s[o] == b[lo + o] && s[o + 1] == b[lo + o + 1] && s[o + 2] == b[lo + o + 2] && s[o + 3] == b[lo + o + 3]);
    assert(s[o + 4] == b[lo + o + 4] && s[o + 5] == b[lo + o + 5] && s[o + 6] == b[lo + o + 6] && s[o + 7] == b[lo + o + 7]);
}

/// The slot of a length and four words.
pub open spec fn hash4(n: u64, w0: u64, w1: u64, w2: u64, w3: u64) -> u64 {
    let x = w0 ^ (w1 >> 19u64) ^ (w2 >> 22u64) ^ (w3 << 9u64) ^ n;
    x ^ (x >> 29u64)
}

pub fn hash4_exec(n: u64, w0: u64, w1: u64, w2: u64, w3: u64) -> (r: u64)
    ensures r == hash4(n, w0, w1, w2, w3),
    no_unwind
{
    let x = w0 ^ (w1 >> 19u64) ^ (w2 >> 22u64) ^ (w3 << 9u64) ^ n;
    x ^ (x >> 29u64)
}

/// The number of `u64` cells per slot: length, four words, id and two unused cells (one 64-byte line).
pub const SLOT: usize = 8;

/// The cache: `cells[SLOT * p ..]` is slot `p`, empty (length cell `0`) or the length, the four words and the id
/// of a key. A slot fills one cache line, so a lookup touches one line of the cache.
pub struct WordCache {
    pub mask: usize,
    pub cells: Vec<u64>,
}

/// The xor-or of four word pairs is zero exactly when every pair is equal.
pub proof fn lemma_words_xor(a0: u64, a1: u64, a2: u64, a3: u64, b0: u64, b1: u64, b2: u64, b3: u64)
    ensures (((a0 ^ b0) | (a1 ^ b1) | (a2 ^ b2) | (a3 ^ b3)) == 0u64) <==> (a0 == b0 && a1 == b1 && a2 == b2 && a3 == b3),
{
    assert((((a0 ^ b0) | (a1 ^ b1) | (a2 ^ b2) | (a3 ^ b3)) == 0u64) <==> (a0 == b0 && a1 == b1 && a2 == b2 && a3 == b3))
        by (bit_vector);
}

impl WordCache {
    /// Cell `k` of slot `p`.
    pub open spec fn cell(&self, p: int, k: int) -> u64 {
        self.cells@[SLOT * p + k]
    }

    /// Slot `p` is empty or describes key `cell(p, 5)` of `keys`.
    pub open spec fn slot_ok(&self, keys: Seq<Seq<u8>>, p: int) -> bool {
        self.cell(p, 0) != 0 ==> {
            &&& (self.cell(p, 5) as int) < keys.len() && self.cell(p, 5) < 0x1_0000_0000
            &&& keys[self.cell(p, 5) as int].len() == self.cell(p, 0)
            &&& words_match(keys[self.cell(p, 5) as int], self.cell(p, 1), self.cell(p, 2), self.cell(p, 3), self.cell(p, 4))
        }
    }

    pub open spec fn wf(&self, keys: Seq<Seq<u8>>) -> bool {
        &&& self.mask < 0x10_0000
        &&& self.cells@.len() == SLOT * (self.mask + 1)
        &&& forall|p: int| 0 <= p <= self.mask ==> #[trigger] self.slot_ok(keys, p)
    }

    /// An empty cache of `mask + 1` slots.
    pub fn new(mask: usize, Ghost(keys): Ghost<Seq<Seq<u8>>>) -> (c: Self)
        requires mask < 0x10_0000,
        ensures c.wf(keys), c.mask == mask,
    {
        let n = SLOT * (mask + 1);
        let c = WordCache { mask, cells: vec![0u64; n] };
        proof {
            assert forall|p: int| 0 <= p <= mask implies #[trigger] c.slot_ok(keys, p) by {
                assert(SLOT * p + 0 < n) by (nonlinear_arith) requires 0 <= p <= mask, n == SLOT * (mask + 1);
                assert(vstd::pervasive::cloned(0u64, c.cells@[SLOT * p + 0]));
            }
        }
        c
    }

    /// The length, words and slot of `b[lo..hi]`, or `None` when its length is not cached.
    fn probe(&self, b: &[u8], lo: usize, hi: usize) -> (r: Option<(u64, u64, u64, u64, u64, usize)>)
        requires self.mask < 0x10_0000, lo <= hi <= b@.len(),
        ensures
            r matches Some((n, w0, w1, w2, w3, p)) ==> n == hi - lo && words_match(b@.subrange(lo as int, hi as int), w0, w1, w2, w3)
                && p <= self.mask && p == (hash4(n, w0, w1, w2, w3) as usize & self.mask),
            r is None ==> !wordable(hi - lo),
        no_unwind
    {
        let n = hi - lo;
        if n < 8 || n > 32 {
            return None;
        }
        let o1 = if n - 8 < 8 { n - 8 } else { 8 };
        let o2 = if n - 8 < 16 { n - 8 } else { 16 };
        let w0 = word_at(b, lo);
        let w1 = word_at(b, lo + o1);
        let w2 = word_at(b, lo + o2);
        let w3 = word_at(b, hi - 8);
        proof {
            let (bb, l, h) = (b@, lo as int, hi as int);
            lemma_sub_word(bb, l, h, 0);
            lemma_sub_word(bb, l, h, o1 as int);
            lemma_sub_word(bb, l, h, o2 as int);
            lemma_sub_word(bb, l, h, n - 8);
        }
        let h = hash4_exec(n as u64, w0, w1, w2, w3) as usize;
        let m = self.mask;
        let p = h & m;
        assert(p <= m) by (bit_vector) requires p == h & m;
        Some((n as u64, w0, w1, w2, w3, p))
    }

    /// Cache key `k` (`b[lo..hi]`) when its length is cached and its slot is free.
    pub fn insert(&mut self, b: &[u8], lo: usize, hi: usize, k: u32, Ghost(keys): Ghost<Seq<Seq<u8>>>)
        requires old(self).wf(keys), lo <= hi <= b@.len(), (k as int) < keys.len(), keys[k as int] == b@.subrange(lo as int, hi as int),
        ensures final(self).wf(keys), final(self).mask == old(self).mask,
    {
        match self.probe(b, lo, hi) {
            None => {},
            Some((n, w0, w1, w2, w3, p)) => {
                let base = SLOT * p;
                proof {
                    assert(base + SLOT <= self.cells@.len()) by (nonlinear_arith)
                        requires base == SLOT * p, p <= self.mask, self.cells@.len() == SLOT * (self.mask + 1);
                }
                if self.cells[base] == 0 {
                    let ghost old_self = *self;
                    self.cells.set(base, n);
                    self.cells.set(base + 1, w0);
                    self.cells.set(base + 2, w1);
                    self.cells.set(base + 3, w2);
                    self.cells.set(base + 4, w3);
                    self.cells.set(base + 5, k as u64);
                    proof {
                        assert forall|q: int| 0 <= q <= self.mask implies #[trigger] self.slot_ok(keys, q) by {
                            if q != p as int {
                                // Slot `q` lies entirely below or above the cells of slot `p`.
                                assert(SLOT * q + SLOT <= base || SLOT * q >= base + SLOT) by (nonlinear_arith)
                                    requires q != p as int, base == SLOT * p, 0 <= q;
                                assert(old_self.slot_ok(keys, q));
                                assert(self.cell(q, 0) == old_self.cell(q, 0));
                                assert(self.cell(q, 1) == old_self.cell(q, 1));
                                assert(self.cell(q, 2) == old_self.cell(q, 2));
                                assert(self.cell(q, 3) == old_self.cell(q, 3));
                                assert(self.cell(q, 4) == old_self.cell(q, 4));
                                assert(self.cell(q, 5) == old_self.cell(q, 5));
                            } else {
                                assert(self.cell(q, 0) == n && self.cell(q, 5) == k as u64);
                            }
                        }
                    }
                }
            },
        }
    }

    /// The id of `b[lo..hi]` when it is cached; `ABSENT` says nothing.
    pub fn lookup(&self, b: &[u8], lo: usize, hi: usize, Ghost(keys): Ghost<Seq<Seq<u8>>>) -> (r: u32)
        requires self.wf(keys), lo <= hi <= b@.len(),
        ensures r != ABSENT ==> (r as int) < keys.len() && keys[r as int] == b@.subrange(lo as int, hi as int),
        no_unwind
    {
        match self.probe(b, lo, hi) {
            None => ABSENT,
            Some((n, w0, w1, w2, w3, p)) => {
                let base = SLOT * p;
                proof {
                    assert(base + SLOT <= self.cells@.len()) by (nonlinear_arith)
                        requires base == SLOT * p, p <= self.mask, self.cells@.len() == SLOT * (self.mask + 1);
                }
                let c = &self.cells;
                let same = (c[base + 1] ^ w0) | (c[base + 2] ^ w1) | (c[base + 3] ^ w2) | (c[base + 4] ^ w3);
                if c[base] == n && same == 0 {
                    let k = c[base + 5];
                    proof {
                        lemma_words_xor(c@[base + 1], c@[base + 2], c@[base + 3], c@[base + 4], w0, w1, w2, w3);
                        assert(self.slot_ok(keys, p as int));
                        lemma_words_eq(keys[k as int], b@.subrange(lo as int, hi as int), w0, w1, w2, w3);
                    }
                    if k >= ABSENT as u64 { ABSENT } else { k as u32 }
                } else {
                    ABSENT
                }
            },
        }
    }
}

} // verus!
