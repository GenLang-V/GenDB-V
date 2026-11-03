//! Static chained hash index over items `0..n`, each with a 64-bit hash: ascending bucket chains (a probe meets
//! the items of its bucket in increasing order) and a bitmap of the hashes' top bits that rejects most absent keys
//! with one cache-resident load (about 16 bits per item, between `2^14` and `2^23` bits).
//!
//! Layout (`chains_wf`): the bucket of a hash is its top `64 - shift` bits; `head[b]` is the smallest item of
//! bucket `b` and `next[e]` the next larger item of `e`'s bucket (`NONE` when there is none), exactly as
//! `first_of` states; `bits` has bit `bit_of(h, bshift)` (the top `64 - bshift` bits) set for the hash `h` of every item.
//! A probe walks `head[b], next[head[b]], ..`; `lemma_first_of` says which items it skips (none of bucket `b`).
use vstd::prelude::*;

verus! {

/// The absent item.
pub const NONE: usize = usize::MAX;


/// The index (see the module header). `hashes[e]` is the hash of item `e`.
pub struct Chains {
    pub hashes: Vec<u64>,
    pub head: Vec<usize>,
    pub next: Vec<usize>,
    pub shift: u64,
    pub bits: Vec<u64>,
    pub bshift: u64,
}

/// The bucket of hash `h`: its top `64 - shift` bits.
pub open spec fn bucket_of(h: u64, shift: u64) -> int {
    (h >> shift) as int
}

/// The smallest item `e >= from` whose hash is in bucket `b`, or `-1`.
pub open spec fn first_of(hs: Seq<u64>, shift: u64, b: int, from: int) -> int
    decreases hs.len() - from,
{
    if from >= hs.len() {
        -1
    } else if bucket_of(hs[from], shift) == b {
        from
    } else {
        first_of(hs, shift, b, from + 1)
    }
}

/// An item number (or `-1`) as a stored `usize` (`NONE` for `-1`).
pub open spec fn enc(x: int) -> usize {
    if x < 0 { NONE } else { x as usize }
}

/// The bitmap position of hash `h`: its top `64 - bshift` bits.
pub open spec fn bit_of(h: u64, bshift: u64) -> int {
    (h >> bshift) as int
}

/// The words of a bitmap of `2^(64 - bshift)` bits (hidden: only the bitmap code needs its value).
#[verifier::opaque]
pub open spec fn bitmap_words(bshift: u64) -> int {
    (1u64 << ((58 - bshift) as u64)) as int
}

/// Bit `x` of the bitmap words `bits`.
pub open spec fn bit_set(bits: Seq<u64>, x: int) -> bool {
    (bits[x / 64] >> ((x % 64) as u64)) & 1u64 == 1u64
}

pub open spec fn chains_wf(c: &Chains) -> bool {
    let hs = c.hashes@;
    &&& hs.len() < NONE
    &&& 34 <= c.shift <= 60
    &&& forall|h: u64| #[trigger] bucket_of(h, c.shift) < c.head@.len()
    &&& c.next@.len() == hs.len()
    &&& forall|b: int| 0 <= b < c.head@.len() ==> #[trigger] c.head@[b] == enc(first_of(hs, c.shift, b, 0))
    &&& forall|e: int| 0 <= e < hs.len() ==>
            #[trigger] c.next@[e] == enc(first_of(hs, c.shift, bucket_of(hs[e], c.shift), e + 1))
    &&& bits_ok(hs, c.bits@, c.bshift)
}

/// The bitmap has the bit of every item's hash (hidden: only the bitmap code reads it).
#[verifier::opaque]
pub open spec fn bits_ok(hs: Seq<u64>, bits: Seq<u64>, bshift: u64) -> bool {
    &&& 41 <= bshift <= 50
    &&& bits.len() == bitmap_words(bshift)
    &&& forall|e: int| 0 <= e < hs.len() ==> bit_set(bits, bit_of(#[trigger] hs[e], bshift))
}

/// What `first_of` says: the items in `from .. r` are not in bucket `b`, and `r` is (or no item from `from` on is).
pub proof fn lemma_first_of(hs: Seq<u64>, shift: u64, b: int, from: int)
    requires 0 <= from,
    ensures ({
        let r = first_of(hs, shift, b, from);
        &&& r == -1 || (from <= r < hs.len() && bucket_of(hs[r], shift) == b)
        &&& forall|e: int| from <= e < hs.len() && (r == -1 || e < r) ==> bucket_of(#[trigger] hs[e], shift) != b
    }),
    decreases hs.len() - from,
{
    if from < hs.len() && bucket_of(hs[from], shift) != b {
        lemma_first_of(hs, shift, b, from + 1);
    }
}

/// `first_of` over items `from..` is unchanged by an item `from - 1` of another bucket.
proof fn lemma_first_of_skip(hs: Seq<u64>, shift: u64, b: int, from: int)
    requires 0 < from <= hs.len(), bucket_of(hs[from - 1], shift) != b,
    ensures first_of(hs, shift, b, from - 1) == first_of(hs, shift, b, from),
{
}

/// The bucket bound: `h >> shift < 2^(64 - shift)`.
proof fn lemma_bucket_bound(h: u64, shift: u64)
    requires 34 <= shift <= 60,
    ensures (h >> shift) < (1u64 << ((64u64 - shift) as u64)),
{
    assert((h >> shift) < (1u64 << ((64u64 - shift) as u64))) by (bit_vector)
        requires 34 <= shift <= 60;
}

/// Setting bit `s` of word `w` sets it and keeps every other set bit.
proof fn lemma_set_bit(w: u64, s: u64, t: u64)
    requires s < 64, t < 64,
    ensures
        ((w | (1u64 << s)) >> s) & 1u64 == 1u64,
        (w >> t) & 1u64 == 1u64 ==> ((w | (1u64 << s)) >> t) & 1u64 == 1u64,
{
    assert(((w | (1u64 << s)) >> s) & 1u64 == 1u64) by (bit_vector) requires s < 64;
    assert((w >> t) & 1u64 == 1u64 ==> ((w | (1u64 << s)) >> t) & 1u64 == 1u64) by (bit_vector)
        requires s < 64, t < 64;
}

/// The bitmap word of a position is a word of the bitmap.
proof fn lemma_bit_bound(h: u64, bshift: u64)
    requires 41 <= bshift <= 50,
    ensures (h >> bshift) / 64 < (1u64 << ((58 - bshift) as u64)), (h >> bshift) % 64 < 64, (h >> bshift) < 0x80_0000u64,
{
    assert((h >> bshift) < 0x80_0000u64) by (bit_vector) requires 41 <= bshift <= 50;
    assert((h >> bshift) / 64 < (1u64 << ((58 - bshift) as u64))) by (bit_vector) requires 41 <= bshift <= 50;
    assert((h >> bshift) % 64 < 64) by (bit_vector);
}

/// The bitmap shift for `n` items: about 16 bits per item, between `2^14` and `2^23` bits.
pub fn bshift_for(n: usize) -> (s: u64)
    ensures 41 <= s <= 50,
{
    let mut bits: u64 = 14;
    while bits < 23 && (1usize << (bits - 4)) < n
        invariant 14 <= bits <= 23,
        decreases 23 - bits,
    {
        bits = bits + 1;
    }
    64 - bits
}

/// The bucket shift for `n` items: `2^(64 - shift)` buckets, at least `2n` when that is at most `2^30`.
pub fn shift_for(n: usize) -> (s: u64)
    ensures 34 <= s <= 60,
{
    let mut bits: u64 = 4;
    while bits < 30 && (1usize << bits) / 2 < n
        invariant 4 <= bits <= 30,
        decreases 30 - bits,
    {
        bits = bits + 1;
    }
    64 - bits
}

/// Build the index of `hashes` (fewer than `NONE` items). Items are linked from the last to the first, so every
/// chain is ascending.
pub fn build_chains(hashes: Vec<u64>) -> (c: Chains)
    requires hashes@.len() < NONE,
    ensures chains_wf(&c), c.hashes@ == hashes@,
{
    let n = hashes.len();
    let ghost hs = hashes@;
    let shift = shift_for(n);
    let nb: usize = (1u64 << (64u64 - shift)) as usize;
    proof {
        assert((1u64 << ((64u64 - shift) as u64)) <= 0x4000_0000u64) by (bit_vector) requires 34 <= shift <= 60;
        assert forall|h: u64| #[trigger] bucket_of(h, shift) < nb by {
            lemma_bucket_bound(h, shift);
        }
    }
    let mut head: Vec<usize> = vec![NONE; nb];
    let mut next: Vec<usize> = vec![NONE; n];
    let bshift = bshift_for(n);
    let nwords: usize = 1usize << (58 - bshift);
    proof {
        assert((1usize << ((58 - bshift) as usize)) as int == (1u64 << ((58 - bshift) as u64)) as int) by (bit_vector)
            requires 41 <= bshift <= 50;
    }
    let mut bits: Vec<u64> = vec![0u64; nwords];
    proof {
        reveal(bitmap_words);
    }
    proof {
        assert forall|b: int| 0 <= b < head@.len() implies #[trigger] head@[b] == enc(first_of(hs, shift, b, n as int)) by {}
    }
    let mut e: usize = n;
    while e > 0
        invariant
            hs == hashes@, n == hs.len(), n < NONE, e <= n, 34 <= shift <= 60,
            head@.len() == nb, next@.len() == n, 41 <= bshift <= 50, bits@.len() == bitmap_words(bshift),
            forall|h: u64| #[trigger] bucket_of(h, shift) < nb,
            forall|b: int| 0 <= b < nb ==> #[trigger] head@[b] == enc(first_of(hs, shift, b, e as int)),
            forall|x: int| e <= x < n ==> #[trigger] next@[x] == enc(first_of(hs, shift, bucket_of(hs[x], shift), x + 1)),
            forall|x: int| e <= x < n ==> bit_set(bits@, bit_of(#[trigger] hs[x], bshift)),
        decreases e,
    {
        proof {
            reveal(bitmap_words);
        }
        e = e - 1;
        let h = hashes[e];
        let b: usize = (h >> shift) as usize;
        proof {
            assert(bucket_of(h, shift) < nb);
        }
        let old_head = head[b];
        next[e] = old_head;
        head[b] = e;
        let bb: u64 = h >> bshift;
        proof {
            lemma_bit_bound(h, bshift);
        }
        let w: usize = (bb / 64) as usize;
        let s: u64 = bb % 64;
        let ghost bits0 = bits@;
        let nw = bits[w] | (1u64 << s);
        bits[w] = nw;
        proof {
            let ei = e as int;
            assert(first_of(hs, shift, b as int, ei) == ei);
            assert forall|b2: int| 0 <= b2 < nb implies #[trigger] head@[b2] == enc(first_of(hs, shift, b2, ei)) by {
                if b2 != b as int {
                    lemma_first_of_skip(hs, shift, b2, ei + 1);
                }
            }
            assert forall|x: int| ei <= x < n implies #[trigger] next@[x] == enc(first_of(hs, shift, bucket_of(hs[x], shift), x + 1)) by {
                if x == ei {
                    assert(next@[x] == old_head);
                }
            }
            lemma_set_bit(bits0[w as int], s, s);
            assert(bit_set(bits@, bit_of(hs[ei], bshift))) by {
                assert(bit_of(hs[ei], bshift) / 64 == w as int);
                assert((bit_of(hs[ei], bshift) % 64) as u64 == s);
            }
            assert forall|x: int| ei <= x < n implies bit_set(bits@, bit_of(#[trigger] hs[x], bshift)) by {
                if x != ei {
                    let p = bit_of(hs[x], bshift);
                    lemma_bit_bound(hs[x], bshift);
                    if p / 64 == w as int {
                        lemma_set_bit(bits0[w as int], s, (p % 64) as u64);
                    }
                }
            }
        }
    }
    proof {
        reveal(bits_ok);
    }
    Chains { hashes, head, next, shift, bits, bshift }
}

/// `false` only when no item has hash `h` (one bitmap load).
pub fn may_contain(c: &Chains, h: u64) -> (r: bool)
    requires chains_wf(c),
    ensures !r ==> forall|e: int| 0 <= e < c.hashes@.len() ==> #[trigger] c.hashes@[e] != h,
    no_unwind
{
    proof {
        reveal(bits_ok);
    }
    let bb: u64 = h >> c.bshift;
    proof {
        lemma_bit_bound(h, c.bshift);
        reveal(bitmap_words);
    }
    let w: usize = (bb / 64) as usize;
    let s: u64 = bb % 64;
    let r = (c.bits[w] >> s) & 1u64 == 1u64;
    proof {
        assert(bit_of(h, c.bshift) / 64 == w as int && (bit_of(h, c.bshift) % 64) as u64 == s);
    }
    r
}

/// The first item of the bucket of `h` (`NONE` when the bucket is empty).
pub fn chain_start(c: &Chains, h: u64) -> (e: usize)
    requires chains_wf(c),
    ensures e == enc(first_of(c.hashes@, c.shift, bucket_of(h, c.shift), 0)),
    no_unwind
{
    let bb: u64 = h >> c.shift;
    let hl: usize = c.head.len();
    proof {
        assert(bucket_of(h, c.shift) < c.head@.len());
        assert(bb as int == bucket_of(h, c.shift));
        assert((bb as int) < hl as int);
    }
    let b: usize = bb as usize;
    proof {
        assert(b as int == bucket_of(h, c.shift));
        assert(c.head@[b as int] == enc(first_of(c.hashes@, c.shift, b as int, 0)));
    }
    c.head[b]
}

/// The item after `e` in its bucket (`NONE` at the end).
pub fn chain_next(c: &Chains, e: usize) -> (r: usize)
    requires chains_wf(c), (e as int) < c.hashes@.len(),
    ensures r == enc(first_of(c.hashes@, c.shift, bucket_of(c.hashes@[e as int], c.shift), e as int + 1)),
    no_unwind
{
    c.next[e]
}

/// The smallest item whose hash is exactly `h`, or `NONE` when no item has hash `h` (a walk of `h`'s bucket).
pub fn chains_find(c: &Chains, h: u64) -> (e: usize)
    requires chains_wf(c),
    ensures
        e != NONE ==> (e as int) < c.hashes@.len() && c.hashes@[e as int] == h,
        e == NONE ==> forall|x: int| 0 <= x < c.hashes@.len() ==> #[trigger] c.hashes@[x] != h,
    no_unwind
{
    let ghost hs = c.hashes@;
    let ghost b = bucket_of(h, c.shift);
    let mut e = chain_start(c, h);
    let ghost mut pos: int = 0;
    while e != NONE
        invariant
            chains_wf(c), hs == c.hashes@, b == bucket_of(h, c.shift), 0 <= pos <= hs.len(),
            e == enc(first_of(hs, c.shift, b, pos)),
            forall|x: int| 0 <= x < pos ==> #[trigger] hs[x] != h,
        decreases hs.len() - pos,
    {
        proof {
            lemma_first_of(hs, c.shift, b, pos);
        }
        if c.hashes[e] == h {
            return e;
        }
        let ghost e0 = e as int;
        e = chain_next(c, e);
        proof {
            assert forall|x: int| 0 <= x < e0 + 1 implies #[trigger] hs[x] != h by {
                if pos <= x < e0 {
                    assert(bucket_of(hs[x], c.shift) != b);
                }
            }
            pos = e0 + 1;
        }
    }
    proof {
        lemma_first_of(hs, c.shift, b, pos);
        assert forall|x: int| 0 <= x < hs.len() implies #[trigger] hs[x] != h by {
            if x >= pos {
                assert(bucket_of(hs[x], c.shift) != b);
            }
        }
    }
    NONE
}

} // verus!
