//! A table from `i64` keys to nonzero `u8` tags with open addressing and linear probing, without wrap-around: a
//! key's probe starts at its home slot (`home`, `< m`) and moves to higher slots; the table has `m + cap + 1` slots,
//! at most `cap` of them occupied (`occ_count`), so a probe always meets an empty slot before the end.
//!
//! Invariant (`tags_wf`): every occupied slot `i` holds a key whose home is at most `i`, and every slot between that
//! home and `i` is occupied. So a lookup (`tags_get`) that meets an empty slot has passed every slot that could hold
//! its key (`tags_get` returns 0: no slot holds it), and one that finds the key returns that slot's tag. Insertion
//! (`tags_put`) fills the first empty slot from the key's home. The home of a key is given by the caller as a spec
//! function of the key (`home_of`), computed by the caller in exec code.
use vstd::prelude::*;
use crate::agent::common::selection::range_sum;

verus! {

/// Slot `i` is occupied (its tag is nonzero).
pub open spec fn occ(slots: Seq<(i64, u8)>, i: int) -> bool { slots[i].1 != 0u8 }

/// The occupied slot count of `[lo, hi)`.
pub open spec fn occ_count(slots: Seq<(i64, u8)>, lo: int, hi: int) -> int {
    range_sum(lo, hi, |i: int| if occ(slots, i) { 1int } else { 0int })
}

/// The table: `m + cap + 1` slots, at most `cap` occupied, every occupied slot reachable from its key's home through
/// occupied slots.
pub open spec fn tags_wf(slots: Seq<(i64, u8)>, m: int, cap: int, home: spec_fn(i64) -> int) -> bool {
    &&& 1 <= m && 0 <= cap
    &&& slots.len() == m + cap + 1
    &&& occ_count(slots, 0, slots.len() as int) <= cap
    &&& forall|k: i64| 0 <= #[trigger] home(k) < m
    &&& forall|i: int| 0 <= i < slots.len() && occ(slots, i) ==> home(#[trigger] slots[i].0) <= i
    &&& forall|i: int, j: int| #![trigger occ(slots, i), occ(slots, j)]
            0 <= i < slots.len() && occ(slots, i) && home(slots[i].0) <= j < i ==> occ(slots, j)
}

/// Some occupied slot holds `key` with tag `tag`.
pub open spec fn tags_has(slots: Seq<(i64, u8)>, key: i64, tag: u8) -> bool {
    exists|i: int| 0 <= i < slots.len() && occ(slots, i) && #[trigger] slots[i] == (key, tag)
}

/// Some occupied slot holds `key`.
pub open spec fn tags_key(slots: Seq<(i64, u8)>, key: i64) -> bool {
    exists|i: int| 0 <= i < slots.len() && occ(slots, i) && #[trigger] slots[i].0 == key
}

// ------------------------------------------------------------------------------------------------ counting

/// Counts of adjacent ranges add.
pub proof fn lemma_count_split(slots: Seq<(i64, u8)>, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures occ_count(slots, lo, hi) == occ_count(slots, lo, mid) + occ_count(slots, mid, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_count_split(slots, lo, mid, hi - 1);
    }
}

/// A count is between 0 and the range's length.
pub proof fn lemma_count_bounds(slots: Seq<(i64, u8)>, lo: int, hi: int)
    requires lo <= hi,
    ensures 0 <= occ_count(slots, lo, hi) <= hi - lo,
    decreases hi - lo,
{
    if hi > lo {
        lemma_count_bounds(slots, lo, hi - 1);
    }
}

/// A fully occupied range counts its length.
pub proof fn lemma_count_full(slots: Seq<(i64, u8)>, lo: int, hi: int)
    requires lo <= hi, forall|j: int| lo <= j < hi ==> #[trigger] occ(slots, j),
    ensures occ_count(slots, lo, hi) == hi - lo,
    decreases hi - lo,
{
    if hi > lo {
        lemma_count_full(slots, lo, hi - 1);
    }
}

/// A run of occupied slots `[lo, i]` inside the table is at most `cap` long.
pub proof fn lemma_run_bound(slots: Seq<(i64, u8)>, m: int, cap: int, home: spec_fn(i64) -> int, lo: int, i: int)
    requires
        tags_wf(slots, m, cap, home), 0 <= lo <= i < slots.len(),
        forall|j: int| lo <= j <= i ==> #[trigger] occ(slots, j),
    ensures i - lo + 1 <= cap,
{
    let n = slots.len() as int;
    lemma_count_full(slots, lo, i + 1);
    lemma_count_split(slots, 0, lo, n);
    lemma_count_split(slots, lo, i + 1, n);
    lemma_count_bounds(slots, 0, lo);
    lemma_count_bounds(slots, i + 1, n);
}

/// The counts of a table with one more slot occupied.
pub proof fn lemma_count_fill(slots: Seq<(i64, u8)>, i: int, x: (i64, u8), lo: int, hi: int)
    requires 0 <= i < slots.len(), !occ(slots, i), x.1 != 0u8, lo <= hi,
    ensures occ_count(slots.update(i, x), lo, hi) == occ_count(slots, lo, hi) + if lo <= i < hi { 1int } else { 0int },
    decreases hi - lo,
{
    if hi > lo {
        lemma_count_fill(slots, i, x, lo, hi - 1);
        if hi - 1 != i {
            assert(slots.update(i, x)[hi - 1] == slots[hi - 1]);
        }
    }
}

// ------------------------------------------------------------------------------------------------ operations

/// An empty table of `m + cap + 1` slots.
pub fn tags_new(m: usize, cap: usize, Ghost(home): Ghost<spec_fn(i64) -> int>) -> (slots: Vec<(i64, u8)>)
    requires 1 <= m, m + cap + 1 <= usize::MAX, forall|k: i64| 0 <= #[trigger] home(k) < m,
    ensures
        tags_wf(slots@, m as int, cap as int, home),
        forall|i: int| 0 <= i < slots@.len() ==> !#[trigger] occ(slots@, i),
{
    let n = m + cap + 1;
    let mut slots: Vec<(i64, u8)> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant i <= n, slots@.len() == i, forall|j: int| 0 <= j < i ==> #[trigger] slots@[j] == (0i64, 0u8),
        decreases n - i,
    {
        slots.push((0i64, 0u8));
        i = i + 1;
    }
    proof {
        assert forall|j: int| 0 <= j < slots@.len() implies !#[trigger] occ(slots@, j) by {}
        assert(occ_count(slots@, 0, n as int) == 0) by {
            lemma_count_none(slots@, 0, n as int);
        }
    }
    slots
}

/// A range without occupied slots counts 0.
pub proof fn lemma_count_none(slots: Seq<(i64, u8)>, lo: int, hi: int)
    requires lo <= hi, forall|j: int| lo <= j < hi ==> !#[trigger] occ(slots, j),
    ensures occ_count(slots, lo, hi) == 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_count_none(slots, lo, hi - 1);
    }
}

/// Inserts `(key, tag)` at the first empty slot from `h = home(key)`; the table must have room (fewer than `cap`
/// occupied slots).
pub fn tags_put(slots: &mut Vec<(i64, u8)>, key: i64, tag: u8, h: usize,
    Ghost(m): Ghost<int>, Ghost(cap): Ghost<int>, Ghost(home): Ghost<spec_fn(i64) -> int>)
    requires
        tags_wf(old(slots)@, m, cap, home), tag != 0u8, h as int == home(key), h < m,
        occ_count(old(slots)@, 0, old(slots)@.len() as int) < cap,
    ensures
        tags_wf(final(slots)@, m, cap, home),
        occ_count(final(slots)@, 0, final(slots)@.len() as int) == occ_count(old(slots)@, 0, old(slots)@.len() as int) + 1,
        forall|i: int| 0 <= i < old(slots)@.len() && #[trigger] occ(old(slots)@, i) ==> final(slots)@[i] == old(slots)@[i],
        tags_has(final(slots)@, key, tag),
        forall|i: int| 0 <= i < final(slots)@.len() && occ(final(slots)@, i) ==>
            #[trigger] final(slots)@[i] == (key, tag) || occ(old(slots)@, i) && final(slots)@[i] == old(slots)@[i],
{
    let ghost s0 = slots@;
    let ghost n = s0.len() as int;
    let len = slots.len();
    let mut i = h;
    while slots[i].1 != 0
        invariant
            slots@ == s0, tags_wf(s0, m, cap, home), h as int == home(key), h < m, h <= i < n, n == m + cap + 1, len == n,
            occ_count(s0, 0, n) < cap,
            forall|j: int| h <= j < i ==> #[trigger] occ(s0, j),
        decreases n - i,
    {
        proof {
            assert(occ(s0, i as int));
            lemma_run_bound(s0, m, cap, home, h as int, i as int);
        }
        i = i + 1;
    }
    let ghost x = (key, tag);
    slots.set(i, (key, tag));
    proof {
        let s1 = slots@;
        assert(s1 == s0.update(i as int, x));
        lemma_count_fill(s0, i as int, x, 0, n);
        assert forall|p: int, j: int| #![trigger occ(s1, p), occ(s1, j)]
            0 <= p < s1.len() && occ(s1, p) && home(s1[p].0) <= j < p implies occ(s1, j) by {
            if p != i {
                assert(s1[p] == s0[p]);
                assert(occ(s0, p));
                assert(occ(s0, j));
                if j != i {
                    assert(s1[j] == s0[j]);
                }
            } else {
                assert(h <= j < i);
                assert(occ(s0, j));
                assert(s1[j] == s0[j]);
            }
        }
        assert forall|p: int| 0 <= p < s1.len() && occ(s1, p) implies home(#[trigger] s1[p].0) <= p by {
            if p != i { assert(s1[p] == s0[p]); }
        }
        assert(s1[i as int] == x);
        assert(tags_has(s1, key, tag));
    }
}

/// The tag of `key`, or 0 when no slot holds it (no allocation, `no_unwind`); `n` is the slot count and `h` the
/// key's home.
pub fn tags_get(slots: &Vec<(i64, u8)>, n: usize, key: i64, h: usize,
    Ghost(m): Ghost<int>, Ghost(cap): Ghost<int>, Ghost(home): Ghost<spec_fn(i64) -> int>) -> (tag: u8)
    requires tags_wf(slots@, m, cap, home), n == slots@.len(), h as int == home(key), h < m,
    ensures
        tag != 0u8 ==> tags_has(slots@, key, tag),
        tag == 0u8 ==> !tags_key(slots@, key),
    no_unwind
{
    let mut i = h;
    while slots[i].1 != 0
        invariant
            tags_wf(slots@, m, cap, home), n == slots@.len(), h as int == home(key), h < m, h <= i < n, n == m + cap + 1,
            forall|j: int| h <= j < i ==> #[trigger] occ(slots@, j) && slots@[j].0 != key,
        decreases n - i,
    {
        if slots[i].0 == key {
            return slots[i].1;
        }
        proof {
            assert(occ(slots@, i as int));
            assert(slots@[i as int].0 != key);
            assert forall|j: int| h <= j < i + 1 implies #[trigger] occ(slots@, j) && slots@[j].0 != key by {
                if j < i {
                    assert(occ(slots@, j));
                }
            }
            lemma_run_bound(slots@, m, cap, home, h as int, i as int);
        }
        i = i + 1;
    }
    proof {
        if tags_key(slots@, key) {
            let p = choose|p: int| 0 <= p < slots@.len() && occ(slots@, p) && #[trigger] slots@[p].0 == key;
            assert(home(key) <= p);
            assert(occ(slots@, p));
            if p > i {
                assert(occ(slots@, i as int));
            }
        }
    }
    0
}

} // verus!
