//! A read-only set of `i64` keys for membership probes from worker threads: the keys in a vector (a key's slot is
//! its index), two filters that answer "certainly not in the set" for almost every other key, and an exact slot
//! lookup through a prefix directory (or a binary or linear search).
//!
//! Layout and invariant (`keyset_wf`), with `h = khash(k)` the 64-bit multiplicative hash of a key:
//! - `f1`: `2^16` words (512 KiB), one bit per key: bit `h % 64` of word `h >> 48` (`f1_has`). One `bt` per probe.
//! - `f2`: `2^15` words (256 KiB), two bits per key in one word: bits `h % 64` and `(h >> 6) % 64` of word
//!   `h >> 49` (`f2_has`). Probed only by keys that pass `f1`.
//! - every key passes both filters (`may_have`); a key that fails either is not in the set.
//! - `sorted` implies strictly ascending keys.
//! - the directory (`nd > 0`): every key is non-negative and its prefix `pfx(k) = k >> dsh` is below `nd`, and
//!   `dir[p]` (for `p <= nd`) is the number of keys whose prefix is below `p`; so the keys with prefix `p` are
//!   exactly the slots `dir[p] .. dir[p + 1]` (`dir_ok`). It is built only over ascending non-negative keys.
use vstd::prelude::*;
use crate::agent::common::bits::bit;

verus! {

/// First filter: `2^16` words of 64 bits (512 KiB), one bit per key.
pub const F1_WORDS: usize = 65536;
/// Second filter: `2^15` words of 64 bits (256 KiB), two bits per key in one word.
pub const F2_WORDS: usize = 32768;
/// At most this many directory buckets.
pub const DIR_MAX: u64 = 32768;
/// Multiplier of the key hash (a 64-bit odd constant).
pub const HMUL: u64 = 0x9E3779B97F4A7C15;

/// The 64-bit hash of a key.
pub open spec fn khash(k: i64) -> u64 { (k as u64).wrapping_mul(HMUL) }

/// The first filter's word of a hash (its top 16 bits) and bit (its low 6 bits).
pub open spec fn f1_word(h: u64) -> u64 { h >> 48u64 }
pub open spec fn f1_bit(h: u64) -> u64 { h & 63u64 }

/// Key `k`'s bit is set in the first filter.
pub open spec fn f1_has(f1: Seq<u64>, k: i64) -> bool {
    bit(f1[f1_word(khash(k)) as int], f1_bit(khash(k)))
}

/// The second filter's word of a hash (its top 15 bits) and its two bits (positions `h % 64`, `(h / 64) % 64`).
pub open spec fn f2_word(h: u64) -> u64 { h >> 49u64 }
pub open spec fn f2_mask(h: u64) -> u64 { (1u64 << (h & 63u64)) | (1u64 << ((h >> 6u64) & 63u64)) }

/// Both of key `k`'s bits are set in the second filter.
pub open spec fn f2_has(f2: Seq<u64>, k: i64) -> bool {
    f2[f2_word(khash(k)) as int] & f2_mask(khash(k)) == f2_mask(khash(k))
}

/// Key `k` passes both filters.
pub open spec fn may_have(f1: Seq<u64>, f2: Seq<u64>, k: i64) -> bool {
    f1_has(f1, k) && f2_has(f2, k)
}

/// The directory prefix of a key.
pub open spec fn pfx(k: i64, sh: u64) -> u64 { (k as u64) >> sh }

/// A key set.
pub struct KeySet {
    pub keys: Vec<i64>,
    pub n: usize,
    pub sorted: bool,
    pub f1: Vec<u64>,
    pub f2: Vec<u64>,
    /// `dir[p]`: the number of keys whose prefix is below `p` (`p <= nd`).
    pub dir: Vec<usize>,
    /// The number of directory buckets; 0 when there is no directory.
    pub nd: usize,
    /// The directory shift.
    pub dsh: u64,
}

/// Keys strictly ascending.
pub open spec fn ascending(keys: Seq<i64>) -> bool {
    forall|i: int, j: int| 0 <= i < j < keys.len() ==> keys[i] < keys[j]
}

/// The directory's invariant (when there is one).
pub open spec fn dir_ok(ks: &KeySet) -> bool {
    ks.nd > 0 ==> {
        &&& ks.dir@.len() == ks.nd + 1
        &&& ks.dsh < 64
        &&& forall|s: int| 0 <= s < ks.n ==> #[trigger] ks.keys@[s] >= 0 && pfx(ks.keys@[s], ks.dsh) < ks.nd
        &&& forall|p: int| 0 <= p <= ks.nd ==> #[trigger] ks.dir@[p] <= ks.n
        &&& forall|p: int, s: int| 0 <= p <= ks.nd && 0 <= s < ks.n ==>
                (s < #[trigger] ks.dir@[p]) == (pfx(#[trigger] ks.keys@[s], ks.dsh) < p)
    }
}

/// The key set's invariant.
pub open spec fn keyset_wf(ks: &KeySet) -> bool {
    &&& ks.n == ks.keys@.len()
    &&& ks.f1@.len() == F1_WORDS && ks.f2@.len() == F2_WORDS
    &&& (ks.sorted ==> ascending(ks.keys@))
    &&& forall|s: int| 0 <= s < ks.n ==> may_have(ks.f1@, ks.f2@, #[trigger] ks.keys@[s])
    &&& dir_ok(ks)
}

/// Key `k` is in the set.
pub open spec fn contains_key(keys: Seq<i64>, k: i64) -> bool {
    exists|s: int| 0 <= s < keys.len() && #[trigger] keys[s] == k
}

// ------------------------------------------------------------------------------------------------ bit facts

/// The filter word indexes are inside the filters.
pub proof fn lemma_words(h: u64)
    ensures f1_word(h) < 65536, f2_word(h) < 32768, f1_bit(h) < 64,
{
    assert(h >> 48u64 < 65536u64) by (bit_vector);
    assert(h >> 49u64 < 32768u64) by (bit_vector);
    assert(h & 63u64 < 64u64) by (bit_vector);
}

/// Setting bit `t` of a word: bit `t` is set and every set bit stays set.
pub proof fn lemma_or_bit(w: u64, t: u64, u: u64)
    requires t < 64, u < 64,
    ensures bit(w | (1u64 << t), t), bit(w, u) ==> bit(w | (1u64 << t), u),
{
    assert(t < 64 ==> ((w | (1u64 << t)) >> t) & 1u64 == 1u64) by (bit_vector);
    assert((u < 64 && (w >> u) & 1u64 == 1u64) ==> ((w | (1u64 << t)) >> u) & 1u64 == 1u64) by (bit_vector);
}

/// Setting a mask keeps every mask that was set.
pub proof fn lemma_or_keeps(w: u64, m: u64, m2: u64)
    requires w & m2 == m2,
    ensures (w | m) & m2 == m2,
{
    assert(w & m2 == m2 ==> (w | m) & m2 == m2) by (bit_vector);
}

/// A word with a mask set has it.
pub proof fn lemma_or_has(w: u64, m: u64)
    ensures (w | m) & m == m,
{
    assert((w | m) & m == m) by (bit_vector);
}

/// A right shift keeps the order of two words.
pub proof fn lemma_shr_mono(a: u64, b: u64, s: u64)
    requires a <= b,
    ensures a >> s <= b >> s,
{
    assert(a <= b ==> a >> s <= b >> s) by (bit_vector);
}

/// A non-negative key keeps its value as a `u64`; two of them keep their order.
pub proof fn lemma_cast_mono(a: i64, b: i64)
    requires 0 <= a <= b,
    ensures (a as u64) <= (b as u64), (a as u64) as int == a as int,
{
}

// ------------------------------------------------------------------------------------------------ building

/// The empty key set (calling thread; allocates the filters).
pub fn keyset_new() -> (ks: KeySet)
    ensures keyset_wf(&ks), ks.keys@ == Seq::<i64>::empty(), ks.sorted, ks.nd == 0,
{
    let f1 = vec![0u64; F1_WORDS];
    let f2 = vec![0u64; F2_WORDS];
    KeySet { keys: Vec::new(), n: 0, sorted: true, f1, f2, dir: Vec::new(), nd: 0, dsh: 0 }
}

/// The filter positions of a key, as the specification computes them: first-filter word and bit, second-filter
/// word and mask.
#[inline(always)]
pub fn key_probe(k: i64) -> (r: (usize, u64, usize, u64))
    ensures
        r.0 as int == f1_word(khash(k)) as int, r.0 < F1_WORDS, r.1 == f1_bit(khash(k)), r.1 < 64,
        r.2 as int == f2_word(khash(k)) as int, r.2 < F2_WORDS, r.3 == f2_mask(khash(k)),
    no_unwind
{
    let h = (k as u64).wrapping_mul(HMUL);
    proof { lemma_words(h); }
    let b1 = h & 63u64;
    let b2 = (h >> 6u64) & 63u64;
    assert(b2 < 64u64) by (bit_vector) requires b2 == (h >> 6u64) & 63u64;
    ((h >> 48u64) as usize, b1, (h >> 49u64) as usize, (1u64 << b1) | (1u64 << b2))
}

/// Append a key (calling thread; before the directory is built).
pub fn keyset_push(ks: &mut KeySet, k: i64)
    requires keyset_wf(old(ks)), old(ks).n < usize::MAX, old(ks).nd == 0,
    ensures
        keyset_wf(final(ks)), final(ks).nd == 0,
        final(ks).keys@ == old(ks).keys@.push(k),
        final(ks).sorted == (old(ks).sorted && (old(ks).n == 0 || old(ks).keys@[old(ks).n - 1] < k)),
{
    let n = ks.n;
    let still_sorted = ks.sorted && (n == 0 || ks.keys[n - 1] < k);
    let (w1, b1, w2, m2) = key_probe(k);
    let ghost f10 = ks.f1@;
    let ghost f20 = ks.f2@;
    let old1 = ks.f1[w1];
    ks.f1.set(w1, old1 | (1u64 << b1));
    let old2 = ks.f2[w2];
    ks.f2.set(w2, old2 | m2);
    ks.keys.push(k);
    ks.n = n + 1;
    ks.sorted = still_sorted;
    proof {
        lemma_or_bit(old1, b1, 0);
        lemma_or_has(old2, m2);
        assert forall|s: int| 0 <= s < ks.n implies may_have(ks.f1@, ks.f2@, #[trigger] ks.keys@[s]) by {
            let ks2 = ks.keys@[s];
            if s < n {
                assert(ks2 == old(ks).keys@[s]);
                assert(may_have(f10, f20, ks2));
                let h2 = khash(ks2);
                lemma_words(h2);
                if f1_word(h2) as int == w1 as int {
                    lemma_or_bit(old1, b1, f1_bit(h2));
                }
                if f2_word(h2) as int == w2 as int {
                    lemma_or_keeps(old2, m2, f2_mask(h2));
                }
            }
        }
        if still_sorted {
            assert forall|i: int, j: int| 0 <= i < j < ks.keys@.len() implies ks.keys@[i] < ks.keys@[j] by {
                if j == n as int && i < n as int {
                    if i < n - 1 {
                        assert(old(ks).keys@[i] < old(ks).keys@[n - 1]);
                    }
                }
            }
        }
    }
}

/// Build the prefix directory when the keys ascend and are non-negative (calling thread); otherwise leave the
/// set without one.
pub fn keyset_index(ks: &mut KeySet)
    requires keyset_wf(old(ks)), old(ks).nd == 0,
    ensures keyset_wf(final(ks)), final(ks).keys@ == old(ks).keys@,
{
    let n = ks.n;
    if !ks.sorted || n == 0 || ks.keys[0] < 0 {
        return;
    }
    let ghost keys = ks.keys@;
    // every key is non-negative and at most the last one
    assert forall|s: int| 0 <= s < n implies 0 <= #[trigger] keys[s] <= keys[n - 1] by {
        if s > 0 { assert(keys[0] < keys[s]); }
        if s < n - 1 { assert(keys[s] < keys[n - 1]); }
    }
    let kmax = ks.keys[n - 1] as u64;
    // the smallest shift that leaves at most DIR_MAX buckets
    let mut sh: u64 = 0;
    while (kmax >> sh) >= DIR_MAX
        invariant sh < 64,
        decreases 64 - sh,
    {
        assert((kmax >> sh) >= 32768u64 ==> sh < 63) by (bit_vector);
        sh = sh + 1;
    }
    let nd = (kmax >> sh) as usize + 1;
    let mut dir: Vec<usize> = Vec::with_capacity(nd + 1);
    let mut j: usize = 0;
    let mut p: usize = 0;
    while p <= nd
        invariant
            ks.keys@ == keys, n == keys.len(), ks.n == n, ks.sorted, ascending(keys), n > 0,
            forall|s: int| 0 <= s < n ==> 0 <= #[trigger] keys[s] <= keys[n - 1],
            kmax == keys[n - 1] as u64, sh < 64, nd == (kmax >> sh) + 1, nd <= DIR_MAX,
            p <= nd + 1, dir@.len() == p, j <= n,
            forall|s: int| 0 <= s < j ==> pfx(#[trigger] keys[s], sh) < p,
            forall|q: int| 0 <= q < p ==> #[trigger] dir@[q] <= n,
            forall|q: int, s: int| 0 <= q < p && 0 <= s < n ==> (s < #[trigger] dir@[q]) == (pfx(#[trigger] keys[s], sh) < q),
        decreases nd + 1 - p,
    {
        while j < n && ((ks.keys[j] as u64) >> sh) < p as u64
            invariant
                ks.keys@ == keys, n == keys.len(), j <= n, sh < 64,
                forall|s: int| 0 <= s < j ==> pfx(#[trigger] keys[s], sh) < p,
            decreases n - j,
        {
            j = j + 1;
        }
        proof {
            // the keys from slot j on have prefixes from p on (the prefixes ascend with the keys)
            assert forall|s: int| j <= s < n implies pfx(#[trigger] keys[s], sh) >= p by {
                assert(pfx(keys[j as int], sh) >= p);
                if s > j {
                    assert(keys[j as int] < keys[s]);
                }
                lemma_cast_mono(keys[j as int], keys[s]);
                lemma_shr_mono(keys[j as int] as u64, keys[s] as u64, sh);
            }
        }
        let ghost dir0 = dir@;
        dir.push(j);
        proof {
            assert forall|q: int, s: int| 0 <= q < p + 1 && 0 <= s < n implies
                (s < #[trigger] dir@[q]) == (pfx(#[trigger] keys[s], sh) < q) by {
                if q < p {
                    assert(dir@[q] == dir0[q]);
                }
            }
        }
        p = p + 1;
    }
    proof {
        assert forall|s: int| 0 <= s < n implies #[trigger] keys[s] >= 0 && pfx(keys[s], sh) < nd by {
            lemma_cast_mono(keys[s], keys[n - 1]);
            lemma_shr_mono(keys[s] as u64, kmax, sh);
        }
    }
    ks.dir = dir;
    ks.nd = nd;
    ks.dsh = sh;
}

// ------------------------------------------------------------------------------------------------ probes

/// Filter test: a key that fails either filter is not in the set.
#[inline(always)]
pub fn may_contain(ks: &KeySet, k: i64) -> (b: bool)
    requires keyset_wf(ks),
    ensures b == may_have(ks.f1@, ks.f2@, k), !b ==> !contains_key(ks.keys@, k),
    no_unwind
{
    let (w1, b1, w2, m2) = key_probe(k);
    let b = (ks.f1[w1] >> b1) & 1u64 == 1u64 && ks.f2[w2] & m2 == m2;
    proof {
        if !b {
            assert forall|s: int| 0 <= s < ks.keys@.len() implies #[trigger] ks.keys@[s] != k by {
                assert(may_have(ks.f1@, ks.f2@, ks.keys@[s]));
            }
        }
    }
    b
}

/// The slot of key `k`: the index holding it, or `None` when it is not in the set.
pub fn find_slot(ks: &KeySet, k: i64) -> (r: Option<usize>)
    requires keyset_wf(ks),
    ensures
        r matches Some(s) ==> s < ks.n && ks.keys@[s as int] == k,
        r is None ==> !contains_key(ks.keys@, k),
    no_unwind
{
    let n = ks.n;
    if ks.nd > 0 {
        // the directory: the keys with k's prefix are the slots dir[p] .. dir[p + 1]
        if k < 0 {
            proof {
                assert forall|s: int| 0 <= s < ks.keys@.len() implies #[trigger] ks.keys@[s] != k by {
                    assert(ks.keys@[s] >= 0);
                }
            }
            return None;
        }
        let p = (k as u64) >> ks.dsh;
        if p >= ks.nd as u64 {
            proof {
                assert forall|s: int| 0 <= s < ks.keys@.len() implies #[trigger] ks.keys@[s] != k by {
                    assert(pfx(ks.keys@[s], ks.dsh) < ks.nd);
                }
            }
            return None;
        }
        let pi = p as usize;
        let a = ks.dir[pi];
        let b = ks.dir[pi + 1];
        let mut s = a;
        while s < b
            invariant
                keyset_wf(ks), n == ks.n, ks.nd > 0, pi < ks.nd, pi as u64 == pfx(k, ks.dsh),
                a == ks.dir@[pi as int], b == ks.dir@[pi + 1], b <= n, a <= s,
                forall|t: int| a <= t < s ==> #[trigger] ks.keys@[t] != k,
            decreases b - s,
        {
            if ks.keys[s] == k {
                return Some(s);
            }
            s = s + 1;
        }
        proof {
            assert forall|t: int| 0 <= t < ks.keys@.len() implies #[trigger] ks.keys@[t] != k by {
                if ks.keys@[t] == k {
                    assert((t < ks.dir@[pi as int]) == (pfx(ks.keys@[t], ks.dsh) < pi));
                    assert((t < ks.dir@[pi + 1]) == (pfx(ks.keys@[t], ks.dsh) < pi + 1));
                }
            }
        }
        None
    } else if ks.sorted {
        let mut lo: usize = 0;
        let mut hi: usize = n;
        while lo < hi
            invariant
                keyset_wf(ks), ks.sorted, n == ks.n, lo <= hi <= n,
                forall|s: int| 0 <= s < lo ==> #[trigger] ks.keys@[s] < k,
                forall|s: int| hi <= s < n ==> #[trigger] ks.keys@[s] > k,
            decreases hi - lo,
        {
            let mid = lo + (hi - lo) / 2;
            let x = ks.keys[mid];
            if x < k {
                proof {
                    assert forall|s: int| 0 <= s < mid + 1 implies #[trigger] ks.keys@[s] < k by {
                        if s < mid { assert(ks.keys@[s] < ks.keys@[mid as int]); }
                    }
                }
                lo = mid + 1;
            } else if x > k {
                proof {
                    assert forall|s: int| mid <= s < n implies #[trigger] ks.keys@[s] > k by {
                        if s > mid { assert(ks.keys@[mid as int] < ks.keys@[s]); }
                    }
                }
                hi = mid;
            } else {
                return Some(mid);
            }
        }
        proof {
            assert forall|s: int| 0 <= s < ks.keys@.len() implies #[trigger] ks.keys@[s] != k by {
                if s < lo {} else { assert(s >= hi); }
            }
        }
        None
    } else {
        let mut j: usize = 0;
        while j < n
            invariant
                keyset_wf(ks), n == ks.n, j <= n,
                forall|s: int| 0 <= s < j ==> #[trigger] ks.keys@[s] != k,
            decreases n - j,
        {
            if ks.keys[j] == k {
                return Some(j);
            }
            j = j + 1;
        }
        None
    }
}

} // verus!
