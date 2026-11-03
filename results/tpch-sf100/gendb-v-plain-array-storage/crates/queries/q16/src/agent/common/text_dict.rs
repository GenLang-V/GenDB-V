//! A dictionary of byte strings with ids `0..n` in insertion order, for lookups from worker tasks (`find`,
//! `no_unwind`) after a serial build (`insert`).
//!
//! Layout: key `i` is `kbytes[koff[i] .. koff[i + 1]]` (`key`); the hash table `slots` holds `0` (empty) or
//! `id + 1`, with linear probing that never wraps: a key's home slot is `hash & mask` (below `mask + 1`), and the
//! table has `2 * (mask + 1)` slots, so a probe path runs from the home slot towards the end. Invariant
//! (`wf`): the keys are distinct, every id has a slot, and every slot between a key's home and its slot is
//! occupied, so a lookup that meets an empty slot (or the end) has seen every slot the key could occupy. An
//! insertion that finds no empty slot before the end fails and leaves the dictionary unchanged.
use vstd::prelude::*;

verus! {

/// `find`'s answer for an absent key, and `insert`'s for a full table.
pub const ABSENT: u32 = 0xFFFF_FFFF;

/// The hash of a byte string: its length and seven bytes (first, second, middle and its neighbours, last two)
/// packed into a word, mixed by shifts.
pub open spec fn byte_or0(s: Seq<u8>, i: int) -> u64 {
    if 0 <= i < s.len() { s[i] as u64 } else { 0 }
}

pub open spec fn hash_spec(s: Seq<u8>) -> u64 {
    let n = s.len() as int;
    let x = ((n % 256) as u64) | (byte_or0(s, 0) << 8u64) | (byte_or0(s, n / 2) << 16u64) | (byte_or0(s, n - 1) << 24u64)
        | (byte_or0(s, n - 2) << 32u64) | (byte_or0(s, 1) << 40u64) | (byte_or0(s, n / 2 + 1) << 48u64)
        | (byte_or0(s, n / 2 - 1) << 56u64);
    x ^ (x >> 23u64) ^ (x >> 27u64) ^ (x >> 45u64)
}

/// The hash of `b[lo..hi]`.
pub fn hash_exec(b: &[u8], lo: usize, hi: usize) -> (r: u64)
    requires lo <= hi <= b@.len(),
    ensures r == hash_spec(b@.subrange(lo as int, hi as int)),
    no_unwind
{
    let ghost s = b@.subrange(lo as int, hi as int);
    let n = hi - lo;
    let b0: u64 = if n >= 1 { b[lo] as u64 } else { 0 };
    let bm: u64 = if n >= 1 { b[lo + n / 2] as u64 } else { 0 };
    let bl: u64 = if n >= 1 { b[hi - 1] as u64 } else { 0 };
    let bl2: u64 = if n >= 2 { b[hi - 2] as u64 } else { 0 };
    let b1: u64 = if n >= 2 { b[lo + 1] as u64 } else { 0 };
    let bm1: u64 = if n / 2 + 1 < n { b[lo + n / 2 + 1] as u64 } else { 0 };
    let bm0: u64 = if n >= 2 { b[lo + n / 2 - 1] as u64 } else { 0 };
    proof {
        assert(b0 == byte_or0(s, 0));
        assert(bm == byte_or0(s, n as int / 2));
        assert(bl == byte_or0(s, n as int - 1));
        assert(bl2 == byte_or0(s, n as int - 2));
        assert(b1 == byte_or0(s, 1));
        assert(bm1 == byte_or0(s, n as int / 2 + 1));
        assert(bm0 == byte_or0(s, n as int / 2 - 1));
    }
    let x: u64 = ((n % 256) as u64) | (b0 << 8u64) | (bm << 16u64) | (bl << 24u64) | (bl2 << 32u64) | (b1 << 40u64)
        | (bm1 << 48u64) | (bm0 << 56u64);
    x ^ (x >> 23u64) ^ (x >> 27u64) ^ (x >> 45u64)
}

/// The little-endian word of bytes `i .. i + 8`.
pub open spec fn word_spec(s: Seq<u8>, i: int) -> u64 {
    (s[i] as u64) | ((s[i + 1] as u64) << 8u64) | ((s[i + 2] as u64) << 16u64) | ((s[i + 3] as u64) << 24u64)
        | ((s[i + 4] as u64) << 32u64) | ((s[i + 5] as u64) << 40u64) | ((s[i + 6] as u64) << 48u64) | ((s[i + 7] as u64) << 56u64)
}

/// Two words are equal exactly when their eight bytes are.
pub proof fn lemma_word_eq(a: Seq<u8>, i: int, b: Seq<u8>, j: int)
    requires 0 <= i, i + 8 <= a.len(), 0 <= j, j + 8 <= b.len(),
    ensures (word_spec(a, i) == word_spec(b, j)) <==> (forall|k: int| 0 <= k < 8 ==> #[trigger] a[i + k] == b[j + k]),
{
    let (x0, x1, x2, x3, x4, x5, x6, x7) = (a[i], a[i + 1], a[i + 2], a[i + 3], a[i + 4], a[i + 5], a[i + 6], a[i + 7]);
    let (y0, y1, y2, y3, y4, y5, y6, y7) = (b[j], b[j + 1], b[j + 2], b[j + 3], b[j + 4], b[j + 5], b[j + 6], b[j + 7]);
    assert(((x0 as u64) | ((x1 as u64) << 8u64) | ((x2 as u64) << 16u64) | ((x3 as u64) << 24u64)
        | ((x4 as u64) << 32u64) | ((x5 as u64) << 40u64) | ((x6 as u64) << 48u64) | ((x7 as u64) << 56u64))
        == ((y0 as u64) | ((y1 as u64) << 8u64) | ((y2 as u64) << 16u64) | ((y3 as u64) << 24u64)
        | ((y4 as u64) << 32u64) | ((y5 as u64) << 40u64) | ((y6 as u64) << 48u64) | ((y7 as u64) << 56u64))
        <==> (x0 == y0 && x1 == y1 && x2 == y2 && x3 == y3 && x4 == y4 && x5 == y5 && x6 == y6 && x7 == y7)) by (bit_vector);
    if word_spec(a, i) == word_spec(b, j) {
        assert forall|k: int| 0 <= k < 8 implies #[trigger] a[i + k] == b[j + k] by {
            if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else if k == 4 {} else if k == 5 {} else if k == 6 {} else {}
        }
    }
    if forall|k: int| 0 <= k < 8 ==> #[trigger] a[i + k] == b[j + k] {
        assert(a[i + 0] == b[j + 0] && a[i + 1] == b[j + 1] && a[i + 2] == b[j + 2] && a[i + 3] == b[j + 3]);
        assert(a[i + 4] == b[j + 4] && a[i + 5] == b[j + 5] && a[i + 6] == b[j + 6] && a[i + 7] == b[j + 7]);
    }
}

/// The word of bytes `i .. i + 8` of a slice.
pub fn word_at(b: &[u8], i: usize) -> (r: u64)
    requires i + 8 <= b@.len(),
    ensures r == word_spec(b@, i as int),
    no_unwind
{
    // An exact eight-byte subslice: its indices need no bounds checks, so the eight byte loads combine into one.
    let (_, t) = b.split_at(i);
    let (w, _) = t.split_at(8);
    proof {
        assert forall|k: int| 0 <= k < 8 implies #[trigger] w@[k] == b@[i + k] by {
            assert(w@[k] == t@[k]);
        }
    }
    (w[0] as u64) | ((w[1] as u64) << 8u64) | ((w[2] as u64) << 16u64) | ((w[3] as u64) << 24u64)
        | ((w[4] as u64) << 32u64) | ((w[5] as u64) << 40u64) | ((w[6] as u64) << 48u64) | ((w[7] as u64) << 56u64)
}

/// The word of bytes `i .. i + 8` of a vector.
pub fn vword_at(b: &Vec<u8>, i: usize) -> (r: u64)
    requires i + 8 <= b@.len(),
    ensures r == word_spec(b@, i as int),
    no_unwind
{
    let _n = b.len();
    (b[i] as u64) | ((b[i + 1] as u64) << 8u64) | ((b[i + 2] as u64) << 16u64) | ((b[i + 3] as u64) << 24u64)
        | ((b[i + 4] as u64) << 32u64) | ((b[i + 5] as u64) << 40u64) | ((b[i + 6] as u64) << 48u64) | ((b[i + 7] as u64) << 56u64)
}

/// Byte equality of `a[alo..ahi]` and `b[blo..bhi]` (eight bytes at a time, then the rest).
pub fn bytes_eq_range(a: &[u8], alo: usize, ahi: usize, b: &[u8], blo: usize, bhi: usize) -> (r: bool)
    requires alo <= ahi <= a@.len(), blo <= bhi <= b@.len(),
    ensures r == (a@.subrange(alo as int, ahi as int) == b@.subrange(blo as int, bhi as int)),
    no_unwind
{
    let n = ahi - alo;
    if n != bhi - blo {
        proof {
            assert(a@.subrange(alo as int, ahi as int).len() != b@.subrange(blo as int, bhi as int).len());
        }
        return false;
    }
    let mut i: usize = 0;
    while n - i >= 8
        invariant
            n == ahi - alo, n == bhi - blo, i <= n, ahi <= a@.len(), bhi <= b@.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] a@[alo + j] == b@[blo + j],
        decreases n - i,
    {
        let wa = word_at(a, alo + i);
        let wb = word_at(b, blo + i);
        proof { lemma_word_eq(a@, alo + i, b@, blo + i); }
        if wa != wb {
            proof {
                let k = choose|k: int| 0 <= k < 8 && !(#[trigger] a@[alo + i + k] == b@[blo + i + k]);
                assert(a@.subrange(alo as int, ahi as int)[i + k] != b@.subrange(blo as int, bhi as int)[i + k]);
            }
            return false;
        }
        proof {
            assert forall|j: int| 0 <= j < i + 8 implies #[trigger] a@[alo + j] == b@[blo + j] by {
                if j >= i { assert(a@[alo + i + (j - i)] == b@[blo + i + (j - i)]); }
            }
        }
        i = i + 8;
    }
    while i < n
        invariant
            n == ahi - alo, n == bhi - blo, i <= n, ahi <= a@.len(), bhi <= b@.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] a@[alo + j] == b@[blo + j],
        decreases n - i,
    {
        if a[alo + i] != b[blo + i] {
            proof {
                assert(a@.subrange(alo as int, ahi as int)[i as int] != b@.subrange(blo as int, bhi as int)[i as int]);
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        assert(a@.subrange(alo as int, ahi as int) =~= b@.subrange(blo as int, bhi as int)) by {
            assert forall|j: int| 0 <= j < n implies a@.subrange(alo as int, ahi as int)[j] == b@.subrange(blo as int, bhi as int)[j] by {
                assert(a@[alo + j] == b@[blo + j]);
            }
        }
    }
    true
}

/// Byte equality of `a[alo..ahi]` (a vector) and `b[blo..bhi]` (eight bytes at a time, then the rest).
pub fn vec_bytes_eq_range(a: &Vec<u8>, alo: usize, ahi: usize, b: &[u8], blo: usize, bhi: usize) -> (r: bool)
    requires alo <= ahi <= a@.len(), blo <= bhi <= b@.len(),
    ensures r == (a@.subrange(alo as int, ahi as int) == b@.subrange(blo as int, bhi as int)),
    no_unwind
{
    let n = ahi - alo;
    if n != bhi - blo {
        proof {
            assert(a@.subrange(alo as int, ahi as int).len() != b@.subrange(blo as int, bhi as int).len());
        }
        return false;
    }
    let mut i: usize = 0;
    while n - i >= 8
        invariant
            n == ahi - alo, n == bhi - blo, i <= n, ahi <= a@.len(), bhi <= b@.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] a@[alo + j] == b@[blo + j],
        decreases n - i,
    {
        let wa = vword_at(a, alo + i);
        let wb = word_at(b, blo + i);
        proof { lemma_word_eq(a@, alo + i, b@, blo + i); }
        if wa != wb {
            proof {
                let k = choose|k: int| 0 <= k < 8 && !(#[trigger] a@[alo + i + k] == b@[blo + i + k]);
                assert(a@.subrange(alo as int, ahi as int)[i + k] != b@.subrange(blo as int, bhi as int)[i + k]);
            }
            return false;
        }
        proof {
            assert forall|j: int| 0 <= j < i + 8 implies #[trigger] a@[alo + j] == b@[blo + j] by {
                if j >= i { assert(a@[alo + i + (j - i)] == b@[blo + i + (j - i)]); }
            }
        }
        i = i + 8;
    }
    while i < n
        invariant
            n == ahi - alo, n == bhi - blo, i <= n, ahi <= a@.len(), bhi <= b@.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] a@[alo + j] == b@[blo + j],
        decreases n - i,
    {
        if a[alo + i] != b[blo + i] {
            proof {
                assert(a@.subrange(alo as int, ahi as int)[i as int] != b@.subrange(blo as int, bhi as int)[i as int]);
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        assert(a@.subrange(alo as int, ahi as int) =~= b@.subrange(blo as int, bhi as int)) by {
            assert forall|j: int| 0 <= j < n implies a@.subrange(alo as int, ahi as int)[j] == b@.subrange(blo as int, bhi as int)[j] by {
                assert(a@[alo + j] == b@[blo + j]);
            }
        }
    }
    true
}

/// The dictionary (see the module comment for the layout and invariant).
pub struct TextDict {
    pub slots: Vec<u32>,
    pub mask: usize,
    pub koff: Vec<usize>,
    pub kbytes: Vec<u8>,
}

impl TextDict {
    /// Number of keys.
    pub open spec fn n(&self) -> nat {
        (self.koff@.len() - 1) as nat
    }

    /// Key `i`.
    pub open spec fn key(&self, i: int) -> Seq<u8> {
        self.kbytes@.subrange(self.koff@[i] as int, self.koff@[i + 1] as int)
    }

    /// The keys in id order.
    pub open spec fn keys(&self) -> Seq<Seq<u8>> {
        Seq::new(self.n(), |i: int| self.key(i))
    }

    /// Home slot of a byte string.
    pub open spec fn home(&self, s: Seq<u8>) -> int {
        ((hash_spec(s) as usize) & self.mask) as int
    }

    /// The id stored in an occupied slot.
    pub open spec fn id_at(&self, p: int) -> int {
        self.slots@[p] as int - 1
    }

    /// Slot `x` holds a key other than `s`.
    pub open spec fn other_at(&self, x: int, s: Seq<u8>) -> bool {
        self.slots@[x] != 0 && self.key(self.id_at(x)) != s
    }

    /// Id `i` is stored in some slot.
    pub open spec fn has_slot(&self, i: int) -> bool {
        exists|p: int| 0 <= p < self.slots@.len() && self.slots@[p] == i + 1
    }

    /// The representation invariant (module comment).
    pub open spec fn wf(&self) -> bool {
        &&& self.koff@.len() >= 1 && self.koff@[0] == 0
        &&& forall|i: int, j: int| 0 <= i <= j <= self.n() ==> self.koff@[i] <= self.koff@[j]
        &&& self.koff@[self.n() as int] == self.kbytes@.len()
        &&& self.mask < 0x1000_0000
        &&& self.slots@.len() == 2 * (self.mask + 1)
        &&& self.n() < 0xFFFF_FFF0
        &&& forall|i: int, j: int| 0 <= i < j < self.n() ==> self.key(i) != self.key(j)
        &&& forall|p: int| 0 <= p < self.slots@.len() ==> self.slots@[p] == 0 || self.id_at(p) < self.n()
        &&& forall|i: int| 0 <= i < self.n() ==> #[trigger] self.has_slot(i)
        &&& forall|p: int| 0 <= p < self.slots@.len() && self.slots@[p] != 0
            ==> self.home(self.key(self.id_at(p))) <= p
                && forall|q: int| self.home(self.key(self.id_at(p))) <= q < p ==> #[trigger] self.slots@[q] != 0
    }

    /// The keys are distinct.
    pub proof fn lemma_keys_distinct(&self)
        requires self.wf(),
        ensures forall|i: int, j: int| 0 <= i < j < self.keys().len() ==> self.keys()[i] != self.keys()[j],
    {
        assert forall|i: int, j: int| 0 <= i < j < self.keys().len() implies self.keys()[i] != self.keys()[j] by {
            assert(self.key(i) != self.key(j));
        }
    }

    /// An empty dictionary with `mask + 1` home slots (`mask` of the form `2^k - 1` gives an even spread).
    pub fn new(mask: usize) -> (d: Self)
        requires mask < 0x1000_0000,
        ensures d.wf(), d.n() == 0, d.mask == mask,
    {
        let size = 2 * (mask + 1);
        let slots = vec![0u32; size];
        proof {
            assert forall|p: int| 0 <= p < slots@.len() implies slots@[p] == 0u32 by {
                assert(vstd::pervasive::cloned(0u32, slots@[p]));
            }
        }
        let mut koff: Vec<usize> = Vec::new();
        koff.push(0);
        TextDict { slots, mask, koff, kbytes: Vec::new() }
    }

    /// Number of keys.
    pub fn count(&self) -> (n: usize)
        requires self.wf(),
        ensures n == self.n(),
        no_unwind
    {
        self.koff.len() - 1
    }

    /// The byte range of key `i` in `kbytes`.
    pub fn key_range(&self, i: usize) -> (r: (usize, usize))
        requires self.wf(), i < self.n(),
        ensures r.0 <= r.1 <= self.kbytes@.len(), self.kbytes@.subrange(r.0 as int, r.1 as int) == self.key(i as int),
        no_unwind
    {
        (self.koff[i], self.koff[i + 1])
    }

    /// The home slot of `b[lo..hi]`.
    pub fn home_exec(&self, b: &[u8], lo: usize, hi: usize) -> (h: usize)
        requires self.wf(), lo <= hi <= b@.len(),
        ensures h == self.home(b@.subrange(lo as int, hi as int)), h <= self.mask,
        no_unwind
    {
        let x = hash_exec(b, lo, hi) as usize;
        let m = self.mask;
        let h = x & m;
        assert(h <= m) by (bit_vector) requires h == x & m;
        h
    }

    /// The id of `b[lo..hi]`, or `ABSENT` when it is not a key.
    pub fn find(&self, b: &[u8], lo: usize, hi: usize) -> (r: u32)
        requires self.wf(), lo <= hi <= b@.len(),
        ensures
            r == ABSENT ==> forall|i: int| 0 <= i < self.n() ==> #[trigger] self.key(i) != b@.subrange(lo as int, hi as int),
            r != ABSENT ==> r < self.n() && self.key(r as int) == b@.subrange(lo as int, hi as int),
        no_unwind
    {
        let ghost s = b@.subrange(lo as int, hi as int);
        let h = self.home_exec(b, lo, hi);
        let size = self.slots.len();
        let mut q = h;
        while q < size
            invariant
                self.wf(), size == self.slots@.len(), lo <= hi <= b@.len(), s == b@.subrange(lo as int, hi as int),
                h == self.home(s), h <= q <= size,
                forall|x: int| h <= x < q ==> #[trigger] self.other_at(x, s),
            decreases size - q,
        {
            let v = self.slots[q];
            if v == 0 {
                proof {
                    self.lemma_absent_at_empty(s, q as int);
                }
                return ABSENT;
            }
            let id = (v - 1) as usize;
            proof {
                assert(self.id_at(q as int) == id);
                assert(id < self.n());
                assert(self.koff@[id as int] <= self.koff@[id + 1] <= self.koff@[self.n() as int]);
            }
            let (x0, x1) = (self.koff[id], self.koff[id + 1]);
            if vec_bytes_eq_range(&self.kbytes, x0, x1, b, lo, hi) {
                return id as u32;
            }
            proof { assert(self.other_at(q as int, s)); }
            q = q + 1;
        }
        proof {
            self.lemma_absent_at_empty(s, size as int);
        }
        ABSENT
    }

    /// `find` with the home slot `h` of `b[lo..hi]` already computed.
    pub fn find_at(&self, b: &[u8], lo: usize, hi: usize, h: usize) -> (r: u32)
        requires self.wf(), lo <= hi <= b@.len(), h == self.home(b@.subrange(lo as int, hi as int)),
        ensures
            r == ABSENT ==> forall|i: int| 0 <= i < self.n() ==> #[trigger] self.key(i) != b@.subrange(lo as int, hi as int),
            r != ABSENT ==> r < self.n() && self.key(r as int) == b@.subrange(lo as int, hi as int),
        no_unwind
    {
        let ghost s = b@.subrange(lo as int, hi as int);
        let size = self.slots.len();
        proof {
            let hh = hash_spec(s) as usize;
            let m = self.mask;
            assert((hh & m) <= m) by (bit_vector);
        }
        let mut q = h;
        while q < size
            invariant
                self.wf(), size == self.slots@.len(), lo <= hi <= b@.len(), s == b@.subrange(lo as int, hi as int),
                h == self.home(s), h <= q <= size,
                forall|x: int| h <= x < q ==> #[trigger] self.other_at(x, s),
            decreases size - q,
        {
            let v = self.slots[q];
            if v == 0 {
                proof {
                    self.lemma_absent_at_empty(s, q as int);
                }
                return ABSENT;
            }
            let id = (v - 1) as usize;
            proof {
                assert(self.id_at(q as int) == id);
                assert(id < self.n());
                assert(self.koff@[id as int] <= self.koff@[id + 1] <= self.koff@[self.n() as int]);
            }
            let (x0, x1) = (self.koff[id], self.koff[id + 1]);
            if vec_bytes_eq_range(&self.kbytes, x0, x1, b, lo, hi) {
                return id as u32;
            }
            proof { assert(self.other_at(q as int, s)); }
            q = q + 1;
        }
        proof {
            self.lemma_absent_at_empty(s, size as int);
        }
        ABSENT
    }

    /// No key is `s` when the slots from its home up to `q` (an empty slot or the end) hold other keys.
    proof fn lemma_absent_at_empty(&self, s: Seq<u8>, q: int)
        requires
            self.wf(),
            self.home(s) <= q <= self.slots@.len(),
            q < self.slots@.len() ==> self.slots@[q] == 0,
            forall|x: int| self.home(s) <= x < q ==> #[trigger] self.other_at(x, s),
        ensures forall|i: int| 0 <= i < self.n() ==> #[trigger] self.key(i) != s,
    {
        assert forall|i: int| 0 <= i < self.n() implies #[trigger] self.key(i) != s by {
            if self.key(i) == s {
                assert(self.has_slot(i));
                let p = choose|p: int| 0 <= p < self.slots@.len() && self.slots@[p] == i + 1;
                assert(self.id_at(p) == i);
                assert(self.home(s) <= p);
                if p < q {
                    assert(self.other_at(p, s));
                } else if p == q {
                } else {
                    assert(self.slots@[q] != 0);
                }
            }
        }
    }

    /// Insert `b[lo..hi]` (a no-op when present): its id, or `ABSENT` (and nothing changed) when the table has no
    /// empty slot on the key's probe path or the id space is used up.
    pub fn insert(&mut self, b: &[u8], lo: usize, hi: usize) -> (r: u32)
        requires old(self).wf(), lo <= hi <= b@.len(),
        ensures
            final(self).wf(),
            final(self).mask == old(self).mask,
            r == ABSENT ==> final(self).keys() == old(self).keys(),
            r != ABSENT ==> r < final(self).n() && final(self).key(r as int) == b@.subrange(lo as int, hi as int)
                && (final(self).keys() == old(self).keys()
                    || final(self).keys() == old(self).keys().push(b@.subrange(lo as int, hi as int))),
    {
        let ghost s = b@.subrange(lo as int, hi as int);
        let f = self.find(b, lo, hi);
        if f != ABSENT {
            return f;
        }
        let n = self.koff.len() - 1;
        if n + 1 >= 0xFFFF_FFF0 {
            return ABSENT;
        }
        let h = self.home_exec(b, lo, hi);
        let size = self.slots.len();
        let mut q = h;
        while q < size && self.slots[q] != 0
            invariant
                self.wf(), size == self.slots@.len(), h <= q <= size,
                forall|x: int| h <= x < q ==> #[trigger] self.slots@[x] != 0,
            decreases size - q,
        {
            q = q + 1;
        }
        if q == size {
            return ABSENT;
        }
        let ghost old_self = *self;
        let ghost old_keys = self.keys();
        // Append the key bytes and the end offset.
        let mut i = lo;
        let start = self.kbytes.len();
        while i < hi
            invariant
                lo <= i <= hi <= b@.len(), start == old_self.kbytes@.len(),
                self.kbytes@ == old_self.kbytes@ + b@.subrange(lo as int, i as int),
                self.koff == old_self.koff, self.slots == old_self.slots, self.mask == old_self.mask,
            decreases hi - i,
        {
            self.kbytes.push(b[i]);
            proof {
                assert(b@.subrange(lo as int, i + 1) =~= b@.subrange(lo as int, i as int).push(b@[i as int]));
            }
            i = i + 1;
        }
        let end = self.kbytes.len();
        self.koff.push(end);
        self.slots[q] = (n + 1) as u32;
        proof {
            let ob = old_self.kbytes@;
            assert(self.kbytes@ == ob + s);
            assert(self.n() == n + 1);
            // Old keys are unchanged: their byte ranges lie in the old bytes.
            assert forall|k: int| 0 <= k < n implies #[trigger] self.key(k) == old_self.key(k) by {
                assert(old_self.koff@[k] <= old_self.koff@[k + 1] <= old_self.koff@[n as int]);
                assert(self.koff@[k] == old_self.koff@[k] && self.koff@[k + 1] == old_self.koff@[k + 1]);
                assert(self.kbytes@.subrange(self.koff@[k] as int, self.koff@[k + 1] as int)
                    =~= ob.subrange(old_self.koff@[k] as int, old_self.koff@[k + 1] as int));
            }
            assert(self.key(n as int) =~= s);
            assert forall|i0: int, j0: int| 0 <= i0 <= j0 <= self.n() implies self.koff@[i0] <= self.koff@[j0] by {
                if j0 == self.n() {
                    assert(old_self.koff@[i0 as int] <= old_self.koff@[n as int] || i0 == self.n());
                }
            }
            assert forall|i0: int, j0: int| 0 <= i0 < j0 < self.n() implies self.key(i0) != self.key(j0) by {
                if j0 == n {
                    assert(old_self.key(i0) != s);
                }
            }
            assert forall|p: int| 0 <= p < self.slots@.len() implies self.slots@[p] == 0 || self.id_at(p) < self.n() by {}
            assert forall|i0: int| 0 <= i0 < self.n() implies #[trigger] self.has_slot(i0) by {
                if i0 == n {
                    assert(self.slots@[q as int] == i0 + 1);
                } else {
                    assert(old_self.has_slot(i0));
                    let p = choose|p: int| 0 <= p < old_self.slots@.len() && old_self.slots@[p] == i0 + 1;
                    assert(p != q);
                    assert(self.slots@[p] == i0 + 1);
                }
            }
            assert forall|p: int| 0 <= p < self.slots@.len() && self.slots@[p] != 0 implies
                self.home(self.key(self.id_at(p))) <= p
                && forall|x: int| self.home(self.key(self.id_at(p))) <= x < p ==> #[trigger] self.slots@[x] != 0 by {
                if p == q {
                    assert(self.id_at(p) == n);
                    assert forall|x: int| self.home(self.key(self.id_at(p))) <= x < p implies #[trigger] self.slots@[x] != 0 by {
                        assert(old_self.slots@[x] != 0);
                    }
                } else {
                    assert(old_self.slots@[p] != 0);
                    assert(self.id_at(p) == old_self.id_at(p));
                    assert(self.key(self.id_at(p)) == old_self.key(old_self.id_at(p)));
                    assert forall|x: int| self.home(self.key(self.id_at(p))) <= x < p implies #[trigger] self.slots@[x] != 0 by {
                        assert(old_self.slots@[x] != 0);
                    }
                }
            }
            assert(self.keys() =~= old_keys.push(s));
        }
        n as u32
    }
}

} // verus!
