//! Hash dictionary from adsh values to rows of `sub` (open addressing, linear probing). `slots[s]` is 0 (empty) or
//! `j + 1` for a `sub` row `j < nids`. A lookup returns a row only after comparing the value with the row's bytes in
//! `sub` (its covering words for 8 to 24 bytes, else byte by byte), so `Some(j)` always means "row j holds this
//! value"; the hash function and the probing only decide whether a present value is found (a miss sends the query
//! to its general path).
//!
//! A scan task also keeps a small 2-way cache in front of the dictionary (`cached_lookup`): entry `s` is
//! `cache[4s .. 4s + 4]`, the covering words of a 20-byte `sub` value and its row + 1 (0: empty). Like the
//! dictionary, an entry is used only after comparing the words, so the cache never decides soundness.
use vstd::prelude::*;
use crate::agent::cols::*;
use crate::agent::common::bytes::*;

verus! {

/// Hash of three words (any function would do: lookups compare the value).
#[inline(always)]
pub fn hash3(w0: u64, w1: u64, w2: u64) -> (h: u64)
    no_unwind
{
    let h = ((w0 as u128 * 0x9E37_79B9_7F4A_7C15u128) as u64) ^ ((w1 as u128 * 0xC2B2_AE3D_27D4_EB4Fu128) as u64)
        ^ ((w2 as u128 * 0x1656_67B1_9E37_79F9u128) as u64);
    h ^ (h >> 29u64)
}

/// The dictionary: `parts.len()` (a power of two, `1 << pbits`) tables of `mask + 1` slots each; a value whose hash
/// is `h` lives in table `part_of(h, pbits)` (the top `pbits` bits of `h`), from its home slot `h & mask` on.
pub struct Dict {
    pub parts: Vec<Vec<u32>>,
    pub pbits: u64,
    pub mask: usize,
    pub nids: usize,
}

pub open spec fn part_ok(d_mask: usize, nids: usize, slots: Seq<u32>) -> bool {
    &&& slots.len() == d_mask + 1
    &&& forall|s: int| 0 <= s < slots.len() ==> #[trigger] slots[s] <= nids
}

pub open spec fn dict_wf(c: Cols, d: Dict) -> bool {
    &&& d.mask < 0x1000_0000
    &&& d.nids <= c.m
    &&& d.nids < 0x1000_0000
    &&& d.pbits <= 6
    &&& d.parts@.len() == (1u64 << d.pbits) as int
    &&& forall|p: int| 0 <= p < d.parts@.len() ==> #[trigger] part_ok(d.mask, d.nids, d.parts@[p]@)
}

proof fn lemma_and_mask(x: usize, m: usize)
    ensures x & m <= m,
{
    assert(x & m <= m) by (bit_vector);
}

proof fn lemma_and_mask64(x: u64, m: u64)
    ensures x & m <= m,
{
    assert(x & m <= m) by (bit_vector);
}

/// The table of hash `h` among `1 << pbits` tables: the top `pbits` bits of `h`.
#[inline(always)]
pub fn part_of(h: u64, pbits: u64) -> (p: usize)
    requires pbits <= 6,
    ensures p < (1u64 << pbits),
    no_unwind
{
    if pbits == 0 {
        proof { assert(1u64 << 0u64 == 1u64) by (bit_vector); }
        0
    } else {
        let sh: u64 = 64 - pbits;
        proof {
            assert((h >> sh) < (1u64 << pbits)) by (bit_vector)
                requires 1u64 <= pbits <= 6u64, sh == 64u64 - pbits;
        }
        (h >> sh) as usize
    }
}

/// The value of `sub` row `j`: its byte range `b0..b1` and, for 8 to 24 bytes, its covering words (else zeros).
#[inline(always)]
fn sub_words(c: &Cols, j: usize) -> (r: (u64, u64, u64, usize, usize))
    requires cols_wf(*c), j < c.m,
    ensures
        r.3 as int == c.sub_off@[j as int], r.4 as int == c.sub_off@[j + 1], r.3 <= r.4 <= c.sub_len,
        8 <= r.4 - r.3 <= 24 ==> (r.0, r.1, r.2) == w3(c.subtext(j as int)),
    no_unwind
{
    proof { assert(0 <= c.sub_off@[j as int] <= c.sub_off@[j + 1] <= c.sub@.len()); }
    let b0 = c.sub_off[j] as usize;
    let b1 = c.sub_off[j + 1] as usize;
    let len = b1 - b0;
    if 8 <= len && len <= 24 {
        let w = words3(c.sub, c.sub_len, b0, b1);
        (w.0, w.1, w.2, b0, b1)
    } else {
        (0, 0, 0, b0, b1)
    }
}

/// The hash of `sub` row `j`'s value (the one `lookup` computes for an equal value).
#[inline(always)]
fn sub_hash(c: &Cols, j: usize) -> (h: u64)
    requires cols_wf(*c), j < c.m,
    no_unwind
{
    let (w0, w1, w2, b0, b1) = sub_words(c, j);
    hash3(w0, w1, w2) ^ ((b1 - b0) as u64)
}

/// Table sizing for `nids` values in `1 << pbits` tables: the slot mask (a load of at most one third).
pub fn table_mask(nids: usize, pbits: u64) -> (mask: usize)
    requires pbits <= 6, nids < 0x1000_0000,
    ensures mask < 0x1000_0000, mask >= 255,
{
    let per = nids >> (pbits as usize);
    let mut size: usize = 256;
    while size <= 0x0400_0000 && size / 3 <= per
        invariant 256 <= size <= 0x0800_0000,
        decreases 0x0800_0000 - size,
    {
        size = size * 2;
    }
    size - 1
}

/// Fills table `p` (of `1 << pbits`, zeroed, `mask + 1` slots) with the `sub` rows `j < nids` whose values hash
/// to it. `no_unwind`: runs as a worker task.
pub fn fill_part(c: &Cols, nids: usize, pbits: u64, p: usize, mask: usize, slots: &mut Vec<u32>)
    requires
        cols_wf(*c), nids <= c.m, nids < 0x1000_0000, pbits <= 6, mask < 0x1000_0000,
        part_ok(mask, nids, old(slots)@),
    ensures
        part_ok(mask, nids, final(slots)@),
    no_unwind
{
    let size = mask + 1;
    let mut j: usize = 0;
    while j < nids
        invariant
            cols_wf(*c), nids <= c.m, nids < 0x1000_0000, j <= nids, pbits <= 6, mask < 0x1000_0000, size == mask + 1,
            part_ok(mask, nids, slots@),
        decreases nids - j,
    {
        let h = sub_hash(c, j);
        if part_of(h, pbits) == p {
            let mut slot = (h & (mask as u64)) as usize;
            proof { lemma_and_mask64(h, mask as u64); }
            let mut steps: usize = 0;
            while slots[slot] != 0 && steps < size
                invariant slot <= mask, size == mask + 1, slots@.len() == size, steps <= size,
                decreases size - steps,
            {
                let nx = slot + 1;
                slot = nx & mask;
                proof { lemma_and_mask(nx, mask); }
                steps = steps + 1;
            }
            slots[slot] = (j + 1) as u32;
        }
        j = j + 1;
    }
}

/// The number of `sub` rows the dictionary holds (all of them, up to its size bound).
pub fn dict_ids(c: &Cols) -> (nids: usize)
    ensures nids <= c.m, nids < 0x1000_0000,
{
    if c.m < 0x1000_0000 { c.m } else { 0 }
}

/// Builds the dictionary of the `sub` adsh values in one table on this thread.
pub fn build_dict(c: &Cols) -> (d: Dict)
    requires cols_wf(*c),
    ensures dict_wf(*c, d),
{
    let nids = dict_ids(c);
    let mask = table_mask(nids, 0);
    let mut slots: Vec<u32> = vec![0u32; mask + 1];
    fill_part(c, nids, 0, 0, mask, &mut slots);
    let mut parts: Vec<Vec<u32>> = Vec::new();
    parts.push(slots);
    proof {
        assert(1u64 << 0u64 == 1u64) by (bit_vector);
        assert forall|p: int| 0 <= p < parts@.len() implies #[trigger] part_ok(mask, nids, parts@[p]@) by {
            assert(p == 0);
        }
    }
    Dict { parts, pbits: 0, mask, nids }
}

/// The `sub` row holding the adsh bytes `adsh[a0..a1]` (`None`: not found). `w0..w2` are its covering words
/// when it has 8 to 24 bytes.
pub fn lookup(c: &Cols, d: &Dict, a0: usize, a1: usize, w0: u64, w1: u64, w2: u64) -> (r: Option<usize>)
    requires
        cols_wf(*c), dict_wf(*c, *d),
        a0 <= a1 <= c.adsh_len,
        8 <= a1 - a0 <= 24 ==> (w0, w1, w2) == w3(c.adsh@.subrange(a0 as int, a1 as int)),
    ensures
        r matches Some(j) ==> j < c.m && c.subtext(j as int) == c.adsh@.subrange(a0 as int, a1 as int),
    no_unwind
{
    let len = a1 - a0;
    let fast = 8 <= len && len <= 24;
    let h = hash3(w0, w1, w2) ^ (len as u64);
    let p = part_of(h, d.pbits);
    let slots = &d.parts[p];
    proof { assert(part_ok(d.mask, d.nids, d.parts@[p as int]@)); }
    let mut slot = (h & (d.mask as u64)) as usize;
    proof { lemma_and_mask64(h, d.mask as u64); }
    let mut steps: usize = 0;
    while steps <= d.mask
        invariant
            cols_wf(*c), dict_wf(*c, *d), slot <= d.mask, part_ok(d.mask, d.nids, slots@),
            a0 <= a1 <= c.adsh_len, len == a1 - a0, fast == (8 <= len && len <= 24),
            fast ==> (w0, w1, w2) == w3(c.adsh@.subrange(a0 as int, a1 as int)),
        decreases d.mask + 1 - steps,
    {
        let e = slots[slot];
        if e == 0 {
            return None;
        }
        let j = (e - 1) as usize;
        let (x0, x1, x2, b0, b1) = sub_words(c, j);
        if b1 - b0 == len {
            if fast {
                if x0 == w0 && x1 == w1 && x2 == w2 {
                    proof { lemma_w3_eq(c.subtext(j as int), c.adsh@.subrange(a0 as int, a1 as int)); }
                    return Some(j);
                }
            } else if eq_ranges(c.adsh, c.adsh_len, a0, a1, c.sub, c.sub_len, b0, b1) {
                return Some(j);
            }
        }
        let nx = slot + 1;
        slot = nx & d.mask;
        proof { lemma_and_mask(nx, d.mask); }
        steps = steps + 1;
    }
    None
}

/// Entry `s` of a lookup cache: empty, or the covering words of a 20-byte `sub` value and its row + 1.
pub open spec fn centry_ok(c: Cols, cache: Seq<u64>, s: int) -> bool {
    cache[4 * s + 3] != 0 ==> {
        &&& cache[4 * s + 3] - 1 < c.m
        &&& c.subtext(cache[4 * s + 3] - 1).len() == 20
        &&& (cache[4 * s], cache[4 * s + 1], cache[4 * s + 2]) == w3(c.subtext(cache[4 * s + 3] - 1))
    }
}

/// A lookup cache of `cache.len() / 4` entries (at least one pair).
pub open spec fn cache_ok(c: Cols, cache: Seq<u64>) -> bool {
    &&& 8 <= cache.len() < 0x1_0000_0000
    &&& forall|s: int| 0 <= s < cache.len() / 4 ==> #[trigger] centry_ok(c, cache, s)
}

/// An empty cache is a cache.
pub proof fn lemma_cache_empty(c: Cols, cache: Seq<u64>)
    requires 8 <= cache.len() < 0x1_0000_0000, forall|k: int| 0 <= k < cache.len() ==> cache[k] == 0,
    ensures cache_ok(c, cache),
{
    assert forall|s: int| 0 <= s < cache.len() / 4 implies #[trigger] centry_ok(c, cache, s) by {
        assert(cache[4 * s + 3] == 0);
    }
}

/// The `sub` row holding the 20-byte adsh value `adsh[a0..a1]` (words `w0..w2`), through the cache of the task
/// (`None`: not found). The cache is 2-way: the value's hash picks the pair of entries `2p`, `2p + 1`; after a
/// dictionary hit the entry `2p` moves to `2p + 1` and the value takes `2p` (most recent first).
#[inline(always)]
pub fn cached_lookup(c: &Cols, d: &Dict, cache: &mut Vec<u64>, a0: usize, a1: usize, w0: u64, w1: u64, w2: u64)
    -> (r: Option<usize>)
    requires
        cols_wf(*c), dict_wf(*c, *d), cache_ok(*c, old(cache)@),
        a0 + 20 == a1, a1 <= c.adsh_len,
        (w0, w1, w2) == w3(c.adsh@.subrange(a0 as int, a1 as int)),
    ensures
        cache_ok(*c, final(cache)@), final(cache)@.len() == old(cache)@.len(),
        r matches Some(j) ==> j < c.m && c.subtext(j as int) == c.adsh@.subrange(a0 as int, a1 as int),
    no_unwind
{
    let ghost val = c.adsh@.subrange(a0 as int, a1 as int);
    let np = cache.len() / 8;
    let h = hash3(w0, w1, w2);
    let p = ((h >> 40u64) as usize) & (np - 1);
    proof { lemma_and_mask((h >> 40u64) as usize, (np - 1) as usize); }
    let s = 2 * p;
    proof {
        assert(centry_ok(*c, cache@, s as int));
        assert(centry_ok(*c, cache@, s + 1));
    }
    let e = cache[4 * s + 3];
    if e != 0 && cache[4 * s] == w0 && cache[4 * s + 1] == w1 && cache[4 * s + 2] == w2 {
        let j = (e - 1) as usize;
        proof { lemma_w3_eq(c.subtext(j as int), val); }
        return Some(j);
    }
    let e1 = cache[4 * s + 7];
    if e1 != 0 && cache[4 * s + 4] == w0 && cache[4 * s + 5] == w1 && cache[4 * s + 6] == w2 {
        let j = (e1 - 1) as usize;
        proof { lemma_w3_eq(c.subtext(j as int), val); }
        return Some(j);
    }
    match lookup(c, d, a0, a1, w0, w1, w2) {
        Some(j) => {
            let ghost old_cache = cache@;
            let x0 = cache[4 * s];
            let x1 = cache[4 * s + 1];
            let x2 = cache[4 * s + 2];
            cache[4 * s + 4] = x0;
            cache[4 * s + 5] = x1;
            cache[4 * s + 6] = x2;
            cache[4 * s + 7] = e;
            cache[4 * s] = w0;
            cache[4 * s + 1] = w1;
            cache[4 * s + 2] = w2;
            cache[4 * s + 3] = (j + 1) as u64;
            proof {
                assert(val.len() == 20);
                assert forall|s2: int| 0 <= s2 < cache@.len() / 4 implies #[trigger] centry_ok(*c, cache@, s2) by {
                    if s2 != s && s2 != s + 1 {
                        assert(centry_ok(*c, old_cache, s2));
                        assert(cache@[4 * s2] == old_cache[4 * s2]);
                        assert(cache@[4 * s2 + 1] == old_cache[4 * s2 + 1]);
                        assert(cache@[4 * s2 + 2] == old_cache[4 * s2 + 2]);
                        assert(cache@[4 * s2 + 3] == old_cache[4 * s2 + 3]);
                    } else if s2 == s + 1 {
                        assert(centry_ok(*c, old_cache, s as int));
                        assert(cache@[4 * s2] == old_cache[4 * s]);
                        assert(cache@[4 * s2 + 1] == old_cache[4 * s + 1]);
                        assert(cache@[4 * s2 + 2] == old_cache[4 * s + 2]);
                        assert(cache@[4 * s2 + 3] == old_cache[4 * s + 3]);
                    } else {
                        assert(cache@[4 * s2 + 3] - 1 == j);
                    }
                }
            }
            Some(j)
        },
        None => None,
    }
}

} // verus!
