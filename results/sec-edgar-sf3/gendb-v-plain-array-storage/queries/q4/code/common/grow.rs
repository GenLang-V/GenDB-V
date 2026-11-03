//! A growable chained hash table of items `0..len` (each with a 64-bit hash), for assigning ids to distinct keys
//! as they first appear: `insert` appends an item, and a probe walks the items of a hash's bucket from the newest
//! to the oldest. The caller keeps the keys and compares them; `grow_wf` and `lemma_last_of` say which items a
//! probe skips (none of its bucket).
//!
//! Layout: the bucket of a hash is its top `64 - shift` bits; `head[b]` is the largest item of bucket `b` and
//! `next[g]` the next smaller item of `g`'s bucket (`NONE` when there is none), exactly as `last_of` states.
use vstd::prelude::*;
use crate::agent::common::chains::{NONE, bucket_of, enc, shift_for};

verus! {

pub struct Grow {
    pub hashes: Vec<u64>,
    pub head: Vec<usize>,
    pub next: Vec<usize>,
    pub shift: u64,
}

/// The largest item `g < upto` whose hash is in bucket `b`, or `-1`.
pub open spec fn last_of(hs: Seq<u64>, shift: u64, b: int, upto: int) -> int
    decreases upto,
{
    if upto <= 0 {
        -1
    } else if bucket_of(hs[upto - 1], shift) == b {
        upto - 1
    } else {
        last_of(hs, shift, b, upto - 1)
    }
}

pub open spec fn grow_wf(t: &Grow) -> bool {
    let hs = t.hashes@;
    &&& hs.len() < NONE
    &&& 34 <= t.shift <= 60
    &&& forall|h: u64| #[trigger] bucket_of(h, t.shift) < t.head@.len()
    &&& t.next@.len() == hs.len()
    &&& forall|b: int| 0 <= b < t.head@.len() ==> #[trigger] t.head@[b] == enc(last_of(hs, t.shift, b, hs.len() as int))
    &&& forall|g: int| 0 <= g < hs.len() ==> #[trigger] t.next@[g] == enc(last_of(hs, t.shift, bucket_of(hs[g], t.shift), g))
}

/// What `last_of` says: the items in `r + 1 .. upto` are not in bucket `b`, and `r` is (or none below `upto` is).
pub proof fn lemma_last_of(hs: Seq<u64>, shift: u64, b: int, upto: int)
    requires upto <= hs.len(),
    ensures ({
        let r = last_of(hs, shift, b, upto);
        &&& r == -1 || (0 <= r < upto && bucket_of(hs[r], shift) == b)
        &&& forall|g: int| 0 <= g < upto && r < g ==> bucket_of(#[trigger] hs[g], shift) != b
    }),
    decreases upto,
{
    if upto > 0 && bucket_of(hs[upto - 1], shift) != b {
        lemma_last_of(hs, shift, b, upto - 1);
    }
}

/// `last_of` below `upto` does not look at items from `upto` on.
proof fn lemma_last_of_prefix(hs: Seq<u64>, hs2: Seq<u64>, shift: u64, b: int, upto: int)
    requires upto <= hs.len(), upto <= hs2.len(), forall|g: int| 0 <= g < upto ==> hs[g] == hs2[g],
    ensures last_of(hs, shift, b, upto) == last_of(hs2, shift, b, upto),
    decreases upto,
{
    if upto > 0 {
        lemma_last_of_prefix(hs, hs2, shift, b, upto - 1);
    }
}

/// An empty table with buckets for about `n` items.
pub fn grow_new(n: usize) -> (t: Grow)
    ensures grow_wf(&t), t.hashes@.len() == 0,
{
    let shift = shift_for(n);
    let nb: usize = (1u64 << (64u64 - shift)) as usize;
    proof {
        assert((1u64 << ((64u64 - shift) as u64)) <= 0x4000_0000u64) by (bit_vector) requires 34 <= shift <= 60;
        assert forall|h: u64| #[trigger] bucket_of(h, shift) < nb by {
            assert((h >> shift) < (1u64 << ((64u64 - shift) as u64))) by (bit_vector) requires 34 <= shift <= 60;
        }
    }
    let head: Vec<usize> = vec![NONE; nb];
    let t = Grow { hashes: Vec::new(), head, next: Vec::new(), shift };
    proof {
        assert forall|b: int| 0 <= b < t.head@.len() implies #[trigger] t.head@[b] == enc(last_of(t.hashes@, t.shift, b, 0)) by {}
    }
    t
}

/// The newest item of the bucket of `h` (`NONE` when the bucket is empty).
pub fn grow_start(t: &Grow, h: u64) -> (g: usize)
    requires grow_wf(t),
    ensures g == enc(last_of(t.hashes@, t.shift, bucket_of(h, t.shift), t.hashes@.len() as int)),
{
    let bb: u64 = h >> t.shift;
    let hl: usize = t.head.len();
    proof {
        assert(bucket_of(h, t.shift) < t.head@.len());
        assert(bb as int == bucket_of(h, t.shift));
        assert((bb as int) < hl as int);
    }
    let b: usize = bb as usize;
    t.head[b]
}

/// The next older item of `g`'s bucket (`NONE` at the end).
pub fn grow_next(t: &Grow, g: usize) -> (r: usize)
    requires grow_wf(t), (g as int) < t.hashes@.len(),
    ensures r == enc(last_of(t.hashes@, t.shift, bucket_of(t.hashes@[g as int], t.shift), g as int)),
{
    t.next[g]
}

/// Append an item with hash `h`; it gets the id `t.hashes@.len()`.
pub fn grow_insert(t: &mut Grow, h: u64)
    requires grow_wf(old(t)), old(t).hashes@.len() + 1 < NONE,
    ensures grow_wf(final(t)), final(t).hashes@ == old(t).hashes@.push(h), final(t).shift == old(t).shift,
{
    let ghost hs0 = t.hashes@;
    let n = t.hashes.len();
    let bb: u64 = h >> t.shift;
    let hl: usize = t.head.len();
    proof {
        assert(bucket_of(h, t.shift) < t.head@.len());
        assert(bb as int == bucket_of(h, t.shift));
    }
    let b: usize = bb as usize;
    let old_head = t.head[b];
    t.next.push(old_head);
    t.head.set(b, n);
    t.hashes.push(h);
    proof {
        let hs = t.hashes@;
        assert forall|b2: int| 0 <= b2 < t.head@.len() implies #[trigger] t.head@[b2] == enc(last_of(hs, t.shift, b2, hs.len() as int)) by {
            lemma_last_of_prefix(hs0, hs, t.shift, b2, n as int);
            if b2 != b as int {
                assert(t.head@[b2] == old(t).head@[b2]);
            }
        }
        assert forall|g: int| 0 <= g < hs.len() implies #[trigger] t.next@[g] == enc(last_of(hs, t.shift, bucket_of(hs[g], t.shift), g)) by {
            if g < n {
                lemma_last_of_prefix(hs0, hs, t.shift, bucket_of(hs[g], t.shift), g);
                assert(t.next@[g] == old(t).next@[g]);
            } else {
                lemma_last_of_prefix(hs0, hs, t.shift, bucket_of(h, t.shift), n as int);
            }
        }
    }
}

/// The newest item whose hash is exactly `h`, or `NONE` when no item has hash `h` (a walk of `h`'s bucket).
pub fn grow_find(t: &Grow, h: u64) -> (g: usize)
    requires grow_wf(t),
    ensures
        g != NONE ==> (g as int) < t.hashes@.len() && t.hashes@[g as int] == h,
        g == NONE ==> forall|x: int| 0 <= x < t.hashes@.len() ==> #[trigger] t.hashes@[x] != h,
{
    let ghost hs = t.hashes@;
    let ghost bk = bucket_of(h, t.shift);
    let mut g = grow_start(t, h);
    let ghost mut pos: int = hs.len() as int;
    while g != NONE
        invariant
            grow_wf(t), hs == t.hashes@, bk == bucket_of(h, t.shift), 0 <= pos <= hs.len(),
            g == enc(last_of(hs, t.shift, bk, pos)),
            forall|x: int| pos <= x < hs.len() ==> #[trigger] hs[x] != h,
        decreases pos,
    {
        proof {
            lemma_last_of(hs, t.shift, bk, pos);
        }
        if t.hashes[g] == h {
            return g;
        }
        let ghost g0 = g as int;
        g = grow_next(t, g);
        proof {
            assert forall|x: int| g0 <= x < hs.len() implies #[trigger] hs[x] != h by {
                if g0 < x < pos {
                    assert(bucket_of(hs[x], t.shift) != bk);
                }
            }
            pos = g0;
        }
    }
    proof {
        lemma_last_of(hs, t.shift, bk, pos);
        assert forall|x: int| 0 <= x < hs.len() implies #[trigger] hs[x] != h by {
            if x < pos {
                assert(bucket_of(hs[x], t.shift) != bk);
            }
        }
    }
    NONE
}

} // verus!
