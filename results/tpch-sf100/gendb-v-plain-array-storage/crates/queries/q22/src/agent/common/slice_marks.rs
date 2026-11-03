//! Marks, in a zero bit set over the keys `0..range` (`range <= 2^32`), the keys of a slice range `keys[lo..hi)`,
//! chunk by chunk for cache locality: the keys of a chunk are first grouped by key slice (`k >> shift`) into `np`
//! groups of `cap` slots of one `u32` buffer (group `p` uses slots `p * cap ..`, `fill[p]` of them), then set
//! group by group, so the words of one key slice stay in cache while they are set. A key whose group is full (or
//! beyond the last group) is set at once. The result is exactly the keys below `range` of the range
//! (`marks_ok`); the grouping only changes the order of the writes.
use vstd::prelude::*;
use crate::agent::common::bitset::*;

verus! {

/// Some key of `keys[lo..hi)` equals `k`.
pub open spec fn key_in(keys: Seq<i64>, k: int, lo: int, hi: int) -> bool {
    exists|j: int| lo <= j < hi && #[trigger] keys[j] as int == k
}

/// The bit set holds exactly the keys below `range` of `keys[lo..hi)`.
pub open spec fn marks_ok(bits: Seq<u64>, keys: Seq<i64>, lo: int, hi: int, range: int) -> bool {
    forall|k: int| 0 <= k < range ==> (#[trigger] bit_at(bits, k) == key_in(keys, k, lo, hi))
}

/// Slot `f` of group `p` (groups of `cap` slots).
pub open spec fn slot(cap: int, p: int, f: int) -> int { p * cap + f }

/// The value of slot `f` of group `p`.
pub open spec fn slot_val(buf: Seq<u32>, cap: int, p: int, f: int) -> int { buf[slot(cap, p, f)] as int }

/// Group `p` holds key `k` in one of its first `n` slots.
pub open spec fn in_group(buf: Seq<u32>, cap: int, p: int, n: int, k: int) -> bool {
    exists|f: int| 0 <= f < n && #[trigger] slot_val(buf, cap, p, f) == k
}

/// One of the first `q` groups holds key `k` in a used slot.
pub open spec fn in_groups(buf: Seq<u32>, fill: Seq<usize>, cap: int, q: int, k: int) -> bool {
    exists|p: int| 0 <= p < q && #[trigger] in_group(buf, cap, p, fill[p] as int, k)
}

/// The groups are well formed: `np` groups of `cap` slots, at most `cap` used, every used slot a key below `range`.
pub open spec fn groups_wf(buf: Seq<u32>, fill: Seq<usize>, np: int, cap: int, range: int) -> bool {
    &&& fill.len() == np
    &&& buf.len() == np * cap
    &&& forall|p: int| 0 <= p < np ==> #[trigger] fill[p] <= cap
    &&& forall|p: int, f: int| 0 <= p < np && 0 <= f < fill[p] ==> #[trigger] slot_val(buf, cap, p, f) < range
}

/// Slots of different (group, slot) pairs differ, and every slot lies in the buffer.
pub proof fn lemma_slot(cap: int, np: int, p: int, f: int, p2: int, f2: int)
    requires 0 <= p < np, 0 <= p2 < np, 0 <= f < cap, 0 <= f2 < cap,
    ensures
        0 <= slot(cap, p, f) < np * cap,
        slot(cap, p, f) == slot(cap, p2, f2) ==> p == p2 && f == f2,
{
    assert(0 <= p * cap + f < np * cap) by (nonlinear_arith) requires 0 <= p < np, 0 <= f < cap;
    if p < p2 {
        assert(p * cap + f < p2 * cap + f2) by (nonlinear_arith) requires p < p2, 0 <= f < cap, 0 <= f2;
    } else if p2 < p {
        assert(p2 * cap + f2 < p * cap + f) by (nonlinear_arith) requires p2 < p, 0 <= f2 < cap, 0 <= f;
    }
}

/// Appending `x` to group `p0` adds exactly `x` to the keys the groups hold and keeps them well formed.
pub proof fn lemma_push(buf: Seq<u32>, fill: Seq<usize>, np: int, cap: int, range: int, p0: int, x: u32)
    requires
        groups_wf(buf, fill, np, cap, range), 0 <= p0 < np, fill[p0] < cap, cap <= usize::MAX, (x as int) < range,
    ensures ({
        let buf2 = buf.update(slot(cap, p0, fill[p0] as int), x);
        let fill2 = fill.update(p0, (fill[p0] + 1) as usize);
        &&& groups_wf(buf2, fill2, np, cap, range)
        &&& forall|k: int| #[trigger] in_groups(buf2, fill2, cap, np, k) == (in_groups(buf, fill, cap, np, k) || k == x as int)
    }),
{
    let f0 = fill[p0] as int;
    let s0 = slot(cap, p0, f0);
    let buf2 = buf.update(s0, x);
    let fill2 = fill.update(p0, (fill[p0] + 1) as usize);
    lemma_slot(cap, np, p0, f0, p0, f0);
    // a used slot of the old groups is not the new slot, so it keeps its value
    assert forall|p: int, f: int| 0 <= p < np && 0 <= f < fill[p] implies
        #[trigger] slot_val(buf2, cap, p, f) == slot_val(buf, cap, p, f) by {
        lemma_slot(cap, np, p, f, p0, f0);
    }
    assert forall|p: int, f: int| 0 <= p < np && 0 <= f < fill2[p] implies #[trigger] slot_val(buf2, cap, p, f) < range by {
        if p == p0 && f == f0 {
        } else {
            assert(f < fill[p]);
        }
    }
    assert forall|k: int| #[trigger] in_groups(buf2, fill2, cap, np, k) == (in_groups(buf, fill, cap, np, k) || k == x as int) by {
        if in_groups(buf2, fill2, cap, np, k) {
            let p = choose|p: int| 0 <= p < np && #[trigger] in_group(buf2, cap, p, fill2[p] as int, k);
            let f = choose|f: int| 0 <= f < fill2[p] as int && #[trigger] slot_val(buf2, cap, p, f) == k;
            if !(p == p0 && f == f0) {
                assert(f < fill[p]);
                assert(slot_val(buf, cap, p, f) == k);
                assert(in_group(buf, cap, p, fill[p] as int, k));
            }
        }
        if in_groups(buf, fill, cap, np, k) {
            let p = choose|p: int| 0 <= p < np && #[trigger] in_group(buf, cap, p, fill[p] as int, k);
            let f = choose|f: int| 0 <= f < fill[p] as int && #[trigger] slot_val(buf, cap, p, f) == k;
            assert(slot_val(buf2, cap, p, f) == k);
            assert(in_group(buf2, cap, p, fill2[p] as int, k));
        }
        if k == x as int {
            assert(slot_val(buf2, cap, p0, f0) == k);
            assert(in_group(buf2, cap, p0, fill2[p0] as int, k));
        }
    }
}

/// The first `q + 1` groups hold the keys of the first `q` and those of group `q`.
pub proof fn lemma_groups_step(buf: Seq<u32>, fill: Seq<usize>, cap: int, q: int, k: int)
    requires 0 <= q < fill.len(),
    ensures in_groups(buf, fill, cap, q + 1, k) == (in_groups(buf, fill, cap, q, k) || in_group(buf, cap, q, fill[q] as int, k)),
{
    if in_groups(buf, fill, cap, q + 1, k) {
        let p = choose|p: int| 0 <= p < q + 1 && #[trigger] in_group(buf, cap, p, fill[p] as int, k);
        if p < q { assert(in_groups(buf, fill, cap, q, k)); }
    }
    if in_groups(buf, fill, cap, q, k) {
        let p = choose|p: int| 0 <= p < q && #[trigger] in_group(buf, cap, p, fill[p] as int, k);
        assert(in_groups(buf, fill, cap, q + 1, k));
    }
    if in_group(buf, cap, q, fill[q] as int, k) {
        assert(in_groups(buf, fill, cap, q + 1, k));
    }
}

/// One more slot of group `p`.
pub proof fn lemma_group_step(buf: Seq<u32>, cap: int, p: int, f: int, k: int)
    requires 0 <= f,
    ensures in_group(buf, cap, p, f + 1, k) == (in_group(buf, cap, p, f, k) || slot_val(buf, cap, p, f) == k),
{
    if in_group(buf, cap, p, f + 1, k) {
        let f2 = choose|f2: int| 0 <= f2 < f + 1 && #[trigger] slot_val(buf, cap, p, f2) == k;
        if f2 < f { assert(in_group(buf, cap, p, f, k)); }
    }
    if in_group(buf, cap, p, f, k) {
        let f2 = choose|f2: int| 0 <= f2 < f && #[trigger] slot_val(buf, cap, p, f2) == k;
        assert(in_group(buf, cap, p, f + 1, k));
    }
    if slot_val(buf, cap, p, f) == k {
        assert(in_group(buf, cap, p, f + 1, k));
    }
}

/// One more key of the slice range.
pub proof fn lemma_key_step(keys: Seq<i64>, lo: int, i: int, k: int)
    requires 0 <= lo <= i < keys.len(),
    ensures key_in(keys, k, lo, i + 1) == (key_in(keys, k, lo, i) || keys[i] as int == k),
{
    if key_in(keys, k, lo, i + 1) {
        let j = choose|j: int| lo <= j < i + 1 && #[trigger] keys[j] as int == k;
        if j < i { assert(key_in(keys, k, lo, i)); }
    }
    if key_in(keys, k, lo, i) {
        let j = choose|j: int| lo <= j < i && #[trigger] keys[j] as int == k;
        assert(key_in(keys, k, lo, i + 1));
    }
    if keys[i] as int == k {
        assert(key_in(keys, k, lo, i + 1));
    }
}

/// Setting bit `x` adds exactly `x` to the positions of the bit set.
pub proof fn lemma_set_bit(old_bits: Seq<u64>, bits: Seq<u64>, x: int, range: int)
    requires
        bits.len() == old_bits.len(), 0 <= x, bit_at(bits, x),
        forall|p: int| 0 <= p && p != x && #[trigger] bit_at(bits, p) != bit_at(old_bits, p) ==> !in_bits(old_bits, p),
        forall|k: int| 0 <= k < range ==> in_bits(old_bits, k),
    ensures forall|k: int| 0 <= k < range ==> #[trigger] bit_at(bits, k) == (bit_at(old_bits, k) || k == x),
{
    assert forall|k: int| 0 <= k < range implies #[trigger] bit_at(bits, k) == (bit_at(old_bits, k) || k == x) by {
        if k != x {
            assert(in_bits(old_bits, k));
        }
    }
}

/// Sets bit `k` (below `range`) of the bit set.
fn set_key(bits: &mut Vec<u64>, k: u64, Ghost(range): Ghost<int>)
    requires
        (k as int) < range,
        forall|p: int| 0 <= p < range ==> in_bits(old(bits)@, p),
    ensures
        final(bits)@.len() == old(bits)@.len(),
        forall|p: int| 0 <= p < range ==> in_bits(final(bits)@, p),
        forall|p: int| 0 <= p < range ==> #[trigger] bit_at(final(bits)@, p) == (bit_at(old(bits)@, p) || p == k as int),
    no_unwind
{
    let ghost before = bits@;
    test_set(bits, k);
    proof {
        lemma_set_bit(before, bits@, k as int, range);
        assert forall|p: int| 0 <= p < range implies in_bits(bits@, p) by { assert(in_bits(before, p)); }
    }
}

/// A zero bit set holds no key.
pub proof fn lemma_zero_marks(bits: Seq<u64>, keys: Seq<i64>, lo: int, range: int)
    requires
        forall|w: int| 0 <= w < bits.len() ==> #[trigger] bits[w] == 0u64,
        forall|k: int| 0 <= k < range ==> in_bits(bits, k),
    ensures marks_ok(bits, keys, lo, lo, range),
{
    assert forall|k: int| 0 <= k < range implies (#[trigger] bit_at(bits, k) == key_in(keys, k, lo, lo)) by {
        assert(in_bits(bits, k));
        let s = (k % 64) as u64;
        assert(bits[k / 64] == 0u64);
        assert((0u64 >> s) & 1u64 == 0u64) by (bit_vector);
    }
}

/// The chunk's keys so far are in the bit set or in the groups: together they hold exactly the keys below `range`
/// of `keys[lo..i)`.
pub open spec fn pending_ok(bits: Seq<u64>, buf: Seq<u32>, fill: Seq<usize>, keys: Seq<i64>, lo: int, i: int,
    range: int, np: int, cap: int) -> bool {
    &&& groups_wf(buf, fill, np, cap, range)
    &&& forall|k: int| 0 <= k < range ==>
            (#[trigger] bit_at(bits, k) || in_groups(buf, fill, cap, np, k)) == key_in(keys, k, lo, i)
}

/// Every position below `range` lies in the bit set.
pub open spec fn covers(bits: Seq<u64>, range: int) -> bool {
    forall|k: int| 0 <= k < range ==> in_bits(bits, k)
}

/// Adds key `keys[i]` to the groups (or, when its group is full, to the bit set).
#[verifier::spinoff_prover]
fn group_key(keys: &[i64], lo: usize, i: usize, range: u64, bits: &mut Vec<u64>, buf: &mut Vec<u32>,
    fill: &mut Vec<usize>, shift: u64, np: usize, cap: usize)
    requires
        lo <= i < keys@.len(), range <= 0x1_0000_0000, shift < 64,
        covers(old(bits)@, range as int),
        pending_ok(old(bits)@, old(buf)@, old(fill)@, keys@, lo as int, i as int, range as int, np as int, cap as int),
    ensures
        final(bits)@.len() == old(bits)@.len(), covers(final(bits)@, range as int),
        pending_ok(final(bits)@, final(buf)@, final(fill)@, keys@, lo as int, i + 1, range as int, np as int, cap as int),
    no_unwind
{
    let ghost r = range as int;
    let ghost (b0, u0, f0) = (bits@, buf@, fill@);
    let k = keys[i];
    if k >= 0 && (k as u64) < range {
        let ku = k as u64;
        let p = (ku >> shift) as usize;
        if p < np && fill[p] < cap {
            let f = fill[p];
            let blen = buf.len();
            proof {
                lemma_slot(cap as int, np as int, p as int, f as int, p as int, f as int);
                lemma_push(u0, f0, np as int, cap as int, r, p as int, ku as u32);
            }
            buf[p * cap + f] = ku as u32;
            fill[p] = f + 1;
            proof {
                assert(buf@ == u0.update(slot(cap as int, p as int, f as int), ku as u32));
                assert(fill@ == f0.update(p as int, (f0[p as int] + 1) as usize));
                assert(ku as u32 as int == ku as int);
                assert forall|k2: int| 0 <= k2 < r implies
                    (#[trigger] bit_at(bits@, k2) || in_groups(buf@, fill@, cap as int, np as int, k2)) == key_in(keys@, k2, lo as int, i + 1) by {
                    lemma_key_step(keys@, lo as int, i as int, k2);
                    assert((bit_at(b0, k2) || in_groups(u0, f0, cap as int, np as int, k2)) == key_in(keys@, k2, lo as int, i as int));
                    assert(in_groups(buf@, fill@, cap as int, np as int, k2) == (in_groups(u0, f0, cap as int, np as int, k2) || k2 == ku as int));
                }
            }
        } else {
            set_key(bits, ku, Ghost(r));
            proof {
                assert forall|k2: int| 0 <= k2 < r implies
                    (#[trigger] bit_at(bits@, k2) || in_groups(buf@, fill@, cap as int, np as int, k2)) == key_in(keys@, k2, lo as int, i + 1) by {
                    lemma_key_step(keys@, lo as int, i as int, k2);
                    assert((bit_at(b0, k2) || in_groups(u0, f0, cap as int, np as int, k2)) == key_in(keys@, k2, lo as int, i as int));
                }
            }
        }
    } else {
        proof {
            assert forall|k2: int| 0 <= k2 < r implies
                (#[trigger] bit_at(bits@, k2) || in_groups(buf@, fill@, cap as int, np as int, k2)) == key_in(keys@, k2, lo as int, i + 1) by {
                lemma_key_step(keys@, lo as int, i as int, k2);
                assert(keys@[i as int] as int != k2);
                assert((bit_at(b0, k2) || in_groups(u0, f0, cap as int, np as int, k2)) == key_in(keys@, k2, lo as int, i as int));
            }
        }
    }
}

/// Sets the keys of the groups in the bit set: afterwards it holds the keys it held and those of every group.
#[verifier::spinoff_prover]
fn flush_groups(bits: &mut Vec<u64>, buf: &Vec<u32>, fill: &Vec<usize>, range: u64, np: usize, cap: usize)
    requires
        covers(old(bits)@, range as int), groups_wf(buf@, fill@, np as int, cap as int, range as int),
    ensures
        final(bits)@.len() == old(bits)@.len(), covers(final(bits)@, range as int),
        forall|k: int| 0 <= k < range ==>
            #[trigger] bit_at(final(bits)@, k) == (bit_at(old(bits)@, k) || in_groups(buf@, fill@, cap as int, np as int, k)),
    no_unwind
{
    let ghost r = range as int;
    let ghost bits0 = bits@;
    let blen = buf.len();
    let mut p: usize = 0;
    while p < np
        invariant
            p <= np, r == range as int, groups_wf(buf@, fill@, np as int, cap as int, r), blen == buf@.len(),
            bits@.len() == bits0.len(), covers(bits@, r),
            forall|k: int| 0 <= k < r ==>
                #[trigger] bit_at(bits@, k) == (bit_at(bits0, k) || in_groups(buf@, fill@, cap as int, p as int, k)),
        decreases np - p,
    {
        let n = fill[p];
        let mut f: usize = 0;
        while f < n
            invariant
                p < np, f <= n, n == fill@[p as int], r == range as int, groups_wf(buf@, fill@, np as int, cap as int, r),
                blen == buf@.len(), bits@.len() == bits0.len(), covers(bits@, r),
                forall|k: int| 0 <= k < r ==> #[trigger] bit_at(bits@, k)
                    == (bit_at(bits0, k) || in_groups(buf@, fill@, cap as int, p as int, k) || in_group(buf@, cap as int, p as int, f as int, k)),
            decreases n - f,
        {
            proof { lemma_slot(cap as int, np as int, p as int, f as int, p as int, f as int); }
            let x = buf[p * cap + f] as u64;
            proof { assert(x as int == slot_val(buf@, cap as int, p as int, f as int)); }
            let ghost b1 = bits@;
            set_key(bits, x, Ghost(r));
            proof {
                assert forall|k: int| 0 <= k < r implies #[trigger] bit_at(bits@, k)
                    == (bit_at(bits0, k) || in_groups(buf@, fill@, cap as int, p as int, k) || in_group(buf@, cap as int, p as int, f + 1, k)) by {
                    lemma_group_step(buf@, cap as int, p as int, f as int, k);
                    assert(bit_at(b1, k) == (bit_at(bits0, k) || in_groups(buf@, fill@, cap as int, p as int, k) || in_group(buf@, cap as int, p as int, f as int, k)));
                }
            }
            f = f + 1;
        }
        proof {
            assert forall|k: int| 0 <= k < r implies
                #[trigger] bit_at(bits@, k) == (bit_at(bits0, k) || in_groups(buf@, fill@, cap as int, p + 1, k)) by {
                lemma_groups_step(buf@, fill@, cap as int, p as int, k);
                assert(bit_at(bits@, k) == (bit_at(bits0, k) || in_groups(buf@, fill@, cap as int, p as int, k) || in_group(buf@, cap as int, p as int, n as int, k)));
            }
        }
        p = p + 1;
    }
}

/// Marks the keys below `range` of `keys[lo..hi)` in the zero bit set `bits`, grouping chunks of `chunk` keys by
/// key slice (see the module header). `buf` and `fill` are scratch space of `np` groups of `cap` slots.
#[verifier::spinoff_prover]
pub fn mark_chunked(keys: &[i64], lo: usize, hi: usize, range: u64, bits: &mut Vec<u64>, buf: &mut Vec<u32>,
    fill: &mut Vec<usize>, shift: u64, np: usize, cap: usize, chunk: usize)
    requires
        lo <= hi <= keys@.len(), range <= 0x1_0000_0000, 1 <= chunk, shift < 64,
        forall|k: int| 0 <= k < range ==> in_bits(old(bits)@, k),
        forall|w: int| 0 <= w < old(bits)@.len() ==> #[trigger] old(bits)@[w] == 0u64,
        old(buf)@.len() == np * cap, old(fill)@.len() == np,
    ensures
        final(bits)@.len() == old(bits)@.len(),
        marks_ok(final(bits)@, keys@, lo as int, hi as int, range as int),
    no_unwind
{
    let ghost nbits = bits@.len();
    let ghost r = range as int;
    proof { lemma_zero_marks(bits@, keys@, lo as int, r); }
    let mut j = lo;
    while j < hi
        invariant
            lo <= j <= hi, hi <= keys@.len(), range <= 0x1_0000_0000, 1 <= chunk, shift < 64, r == range as int,
            bits@.len() == nbits, covers(bits@, r),
            buf@.len() == np * cap, fill@.len() == np,
            marks_ok(bits@, keys@, lo as int, j as int, r),
        decreases hi - j,
    {
        let e = if hi - j > chunk { j + chunk } else { hi };
        // empty every group
        let mut b: usize = 0;
        while b < np
            invariant b <= np, fill@.len() == np, forall|p: int| 0 <= p < b ==> #[trigger] fill@[p] == 0usize,
            decreases np - b,
        {
            fill[b] = 0;
            b = b + 1;
        }
        proof {
            assert forall|k: int| 0 <= k < r implies
                (#[trigger] bit_at(bits@, k) || in_groups(buf@, fill@, cap as int, np as int, k)) == key_in(keys@, k, lo as int, j as int) by {
                if in_groups(buf@, fill@, cap as int, np as int, k) {
                    let p = choose|p: int| 0 <= p < np && #[trigger] in_group(buf@, cap as int, p, fill@[p] as int, k);
                    assert(fill@[p] == 0usize);
                }
            }
        }
        // group the keys of the chunk
        let mut i = j;
        while i < e
            invariant
                lo <= j <= i <= e <= hi, hi <= keys@.len(), range <= 0x1_0000_0000, shift < 64, r == range as int,
                bits@.len() == nbits, covers(bits@, r),
                pending_ok(bits@, buf@, fill@, keys@, lo as int, i as int, r, np as int, cap as int),
            decreases e - i,
        {
            group_key(keys, lo, i, range, bits, buf, fill, shift, np, cap);
            i = i + 1;
        }
        // set the grouped keys, group by group
        let ghost bits0 = bits@;
        proof { assert(pending_ok(bits0, buf@, fill@, keys@, lo as int, e as int, r, np as int, cap as int)); }
        flush_groups(bits, buf, fill, range, np, cap);
        proof {
            assert forall|k: int| 0 <= k < r implies (#[trigger] bit_at(bits@, k) == key_in(keys@, k, lo as int, e as int)) by {
                assert((bit_at(bits0, k) || in_groups(buf@, fill@, cap as int, np as int, k)) == key_in(keys@, k, lo as int, e as int));
            }
        }
        j = e;
    }
}

} // verus!
