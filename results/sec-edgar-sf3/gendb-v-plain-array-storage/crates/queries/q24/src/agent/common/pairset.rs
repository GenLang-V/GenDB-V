//! A set of `u64` pairs `(k, x)` with `k != 0`, by open addressing (linear probing without wrap-around), with
//! exact membership: `lookup` answers `has` (`no_unwind`, usable in worker tasks).
//!
//! Layout: one interleaved vector `v`; slot `s` holds `(v[2s], v[2s + 1])` (one 16-byte pair, so a probe touches
//! one cache line), empty when `v[2s] == 0`; there are `mask + 1 + ROOM` slots and a pair starts probing at
//! `bucket(k, x, mask) = (k ^ x) & mask`. Invariant (`set_wf`): every stored pair sits at or after its bucket with
//! every slot in between occupied, so a probe that reaches an empty slot (or the end) without meeting the pair
//! proves it absent. `insert` fails (`false`) instead of running past the last slot.
use vstd::prelude::*;

verus! {

pub const ROOM: usize = 64;

/// `len` zeros (calling thread; allocates).
pub fn zeroed(len: usize) -> (v: Vec<u64>)
    ensures v@ == Seq::new(len as nat, |_i: int| 0u64),
{
    let v = vec![0u64; len];
    proof {
        assert(v@ =~= Seq::new(len as nat, |_i: int| 0u64));
    }
    v
}

pub struct PairSet {
    pub v: Vec<u64>,
    pub mask: u64,
}

/// The number of slots.
pub open spec fn slots(t: PairSet) -> int {
    t.mask + 1 + ROOM
}

pub open spec fn key_at(t: PairSet, s: int) -> u64 {
    t.v@[2 * s]
}

pub open spec fn aux_at(t: PairSet, s: int) -> u64 {
    t.v@[2 * s + 1]
}

pub open spec fn bucket(k: u64, x: u64, mask: u64) -> int {
    ((k ^ x) & mask) as int
}

pub open spec fn occupied(t: PairSet, s: int) -> bool {
    0 <= s < slots(t) && key_at(t, s) != 0
}

pub open spec fn set_wf(t: PairSet) -> bool {
    &&& t.v@.len() == 2 * slots(t)
    &&& forall|s: int| #[trigger] occupied(t, s) ==> {
            &&& bucket(key_at(t, s), aux_at(t, s), t.mask) <= s
            &&& forall|q: int| bucket(key_at(t, s), aux_at(t, s), t.mask) <= q < s ==> #[trigger] occupied(t, q)
        }
}

/// The set holds `(k, x)`.
pub open spec fn has(t: PairSet, k: u64, x: u64) -> bool {
    exists|s: int| #[trigger] occupied(t, s) && key_at(t, s) == k && aux_at(t, s) == x
}

pub fn bucket_exec(k: u64, x: u64, mask: u64) -> (b: usize)
    requires mask < usize::MAX,
    ensures b == bucket(k, x, mask), b <= mask,
    no_unwind
{
    let v = k ^ x;
    assert(v & mask <= mask) by (bit_vector);
    (v & mask) as usize
}

/// An empty set of `mask + 1 + ROOM` slots (calling thread; allocates).
pub fn new_set(mask: u64) -> (t: PairSet)
    requires 2 * (mask as int + 1 + ROOM) <= usize::MAX,
    ensures set_wf(t), t.mask == mask, forall|k: u64, x: u64| !(#[trigger] has(t, k, x)),
{
    let len = 2 * (mask as usize + 1 + ROOM);
    let t = PairSet { v: zeroed(len), mask };
    proof {
        assert forall|s: int| !#[trigger] occupied(t, s) by {
            if 0 <= s < slots(t) {
                assert(key_at(t, s) == 0);
            }
        }
    }
    t
}

/// The probe from the bucket of `(k, x)` up to `pos` saw only occupied slots holding other pairs, and stopped at
/// an empty slot or the end: the set does not hold `(k, x)`.
proof fn lemma_absent(t: PairSet, k: u64, x: u64, pos: int)
    requires
        set_wf(t),
        bucket(k, x, t.mask) <= pos <= slots(t),
        forall|q: int| bucket(k, x, t.mask) <= q < pos ==> #[trigger] occupied(t, q) && !(key_at(t, q) == k && aux_at(t, q) == x),
        pos == slots(t) || !occupied(t, pos),
    ensures !(has(t, k, x)),
{
    if has(t, k, x) {
        let s = choose|s: int| #[trigger] occupied(t, s) && key_at(t, s) == k && aux_at(t, s) == x;
        assert(bucket(k, x, t.mask) <= s);
        if s >= pos {
            assert(pos < slots(t));
            assert(occupied(t, pos));
        }
    }
}

/// The key stored in the bucket slot of `(k, x)` (0: empty). A batch of probes reads these first, with no
/// branch on the loaded values, so their cache misses overlap; `lookup_hinted` then uses the value.
pub fn bucket_key(t: &PairSet, k: u64, x: u64) -> (w: u64)
    requires set_wf(*t),
    ensures w == key_at(*t, bucket(k, x, t.mask)),
    no_unwind
{
    let len = t.v.len();
    assert(t.mask < usize::MAX);
    let b = bucket_exec(k, x, t.mask);
    t.v[2 * b]
}

/// `lookup`, given `first`, the key of the bucket slot of `(k, x)`: an empty bucket proves the pair absent.
pub fn lookup_hinted(t: &PairSet, k: u64, x: u64, first: u64) -> (r: bool)
    requires set_wf(*t), k != 0, first == key_at(*t, bucket(k, x, t.mask)),
    ensures r == has(*t, k, x),
    no_unwind
{
    if first == 0 {
        proof {
            let v = k ^ x;
            let mask = t.mask;
            assert(v & mask <= mask) by (bit_vector);
            lemma_absent(*t, k, x, bucket(k, x, t.mask));
        }
        return false;
    }
    lookup(t, k, x)
}

/// Does the set hold `(k, x)`?
pub fn lookup(t: &PairSet, k: u64, x: u64) -> (r: bool)
    requires set_wf(*t), k != 0,
    ensures r == has(*t, k, x),
    no_unwind
{
    let len = t.v.len();
    let n = len / 2;
    assert(n == slots(*t) && t.mask < usize::MAX);
    let b = bucket_exec(k, x, t.mask);
    let mut pos = b;
    while pos < n && t.v[2 * pos] != 0
        invariant
            set_wf(*t), n == slots(*t), len == t.v@.len(), len == 2 * n, b == bucket(k, x, t.mask), b <= pos <= n,
            forall|q: int| b <= q < pos ==> #[trigger] occupied(*t, q) && !(key_at(*t, q) == k && aux_at(*t, q) == x),
        decreases n - pos,
    {
        if t.v[2 * pos] == k && t.v[2 * pos + 1] == x {
            proof {
                assert(occupied(*t, pos as int));
            }
            return true;
        }
        proof {
            assert(occupied(*t, pos as int));
            assert forall|q: int| b <= q < pos + 1 implies #[trigger] occupied(*t, q) && !(key_at(*t, q) == k && aux_at(*t, q) == x) by {
                if q < pos as int {
                    assert(occupied(*t, q) && !(key_at(*t, q) == k && aux_at(*t, q) == x));
                }
            }
        }
        pos = pos + 1;
    }
    proof {
        lemma_absent(*t, k, x, pos as int);
    }
    false
}

/// Add `(k, x)` (`false`: the probe ran past the last slot; the set is unchanged).
pub fn insert(t: &mut PairSet, k: u64, x: u64) -> (ok: bool)
    requires set_wf(*old(t)), k != 0,
    ensures
        set_wf(*final(t)), final(t).mask == old(t).mask,
        forall|k2: u64, x2: u64| #[trigger] has(*final(t), k2, x2) <==> has(*old(t), k2, x2) || (ok && k2 == k && x2 == x),
    no_unwind
{
    let len = t.v.len();
    let n = len / 2;
    assert(n == slots(*t) && t.mask < usize::MAX);
    let b = bucket_exec(k, x, t.mask);
    let mut pos = b;
    while pos < n && t.v[2 * pos] != 0
        invariant
            set_wf(*t), n == slots(*t), len == t.v@.len(), len == 2 * n, b == bucket(k, x, t.mask), b <= pos <= n,
            forall|q: int| b <= q < pos ==> #[trigger] occupied(*t, q) && !(key_at(*t, q) == k && aux_at(*t, q) == x),
        decreases n - pos,
    {
        if t.v[2 * pos] == k && t.v[2 * pos + 1] == x {
            proof {
                assert(occupied(*t, pos as int));
                assert forall|k2: u64, x2: u64| #[trigger] has(*t, k2, x2) <==> has(*t, k2, x2) || (k2 == k && x2 == x) by {
                    if k2 == k && x2 == x {
                        assert(occupied(*t, pos as int) && key_at(*t, pos as int) == k2 && aux_at(*t, pos as int) == x2);
                    }
                }
            }
            return true;
        }
        proof {
            assert(occupied(*t, pos as int));
            assert forall|q: int| b <= q < pos + 1 implies #[trigger] occupied(*t, q) && !(key_at(*t, q) == k && aux_at(*t, q) == x) by {
                if q < pos as int {
                    assert(occupied(*t, q) && !(key_at(*t, q) == k && aux_at(*t, q) == x));
                }
            }
        }
        pos = pos + 1;
    }
    if pos == n {
        return false;
    }
    let ghost old_t = *t;
    t.v[2 * pos] = k;
    t.v[2 * pos + 1] = x;
    proof {
        assert(!occupied(old_t, pos as int));
        // Every other slot keeps its pair (slot `s` is `v[2s], v[2s + 1]`, disjoint from slot `pos`).
        assert forall|s: int| 0 <= s < slots(*t) && s != pos as int implies
            key_at(*t, s) == key_at(old_t, s) && aux_at(*t, s) == aux_at(old_t, s) by {
        }
        assert(key_at(*t, pos as int) == k && aux_at(*t, pos as int) == x);
        // Occupancy only grows; the new slot sits after its bucket with every slot in between occupied.
        assert forall|s: int| #[trigger] occupied(*t, s) implies {
            &&& bucket(key_at(*t, s), aux_at(*t, s), t.mask) <= s
            &&& forall|q: int| bucket(key_at(*t, s), aux_at(*t, s), t.mask) <= q < s ==> #[trigger] occupied(*t, q)
        } by {
            if s == pos as int {
                assert forall|q: int| bucket(key_at(*t, s), aux_at(*t, s), t.mask) <= q < s implies #[trigger] occupied(*t, q) by {
                    assert(occupied(old_t, q));
                }
            } else {
                assert(occupied(old_t, s));
                assert forall|q: int| bucket(key_at(*t, s), aux_at(*t, s), t.mask) <= q < s implies #[trigger] occupied(*t, q) by {
                    assert(occupied(old_t, q));
                    if q != pos as int {
                        assert(key_at(*t, q) == key_at(old_t, q));
                    }
                }
            }
        }
        assert forall|k2: u64, x2: u64| #[trigger] has(*t, k2, x2) <==> has(old_t, k2, x2) || (k2 == k && x2 == x) by {
            if has(old_t, k2, x2) {
                let s = choose|s: int| #[trigger] occupied(old_t, s) && key_at(old_t, s) == k2 && aux_at(old_t, s) == x2;
                assert(s != pos as int);
                assert(occupied(*t, s));
            }
            if k2 == k && x2 == x {
                assert(occupied(*t, pos as int));
            }
            if has(*t, k2, x2) {
                let s = choose|s: int| #[trigger] occupied(*t, s) && key_at(*t, s) == k2 && aux_at(*t, s) == x2;
                if s != pos as int {
                    assert(occupied(old_t, s));
                }
            }
        }
    }
    true
}

} // verus!
