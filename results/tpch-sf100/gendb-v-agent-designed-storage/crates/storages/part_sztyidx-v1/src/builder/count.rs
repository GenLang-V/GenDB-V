//! Counting-sort arithmetic: occurrences of a key in a prefix of a key column (`cnt_int`), prefix sums of a count
//! vector (`psum`), and the facts the directory construction needs (monotone prefix counts and sums, one more
//! occurrence per matching row, disjoint directory entries).
use vstd::prelude::*;

verus! {

/// Number of positions `0 .. m` of `keys` holding `v`.
pub open spec fn cnt_int(keys: Seq<i64>, v: int, m: int) -> nat
    decreases m,
{
    if m <= 0 { 0 } else { cnt_int(keys, v, m - 1) + if keys[m - 1] == v { 1nat } else { 0nat } }
}

/// Sum of `c[0 .. e]`.
pub open spec fn psum(c: Seq<u32>, e: int) -> int
    decreases e,
{
    if e <= 0 { 0 } else { psum(c, e - 1) + c[e - 1] }
}

/// Prefix counts grow with the prefix and never exceed it.
pub proof fn lemma_cnt_mono(keys: Seq<i64>, v: int, a: int, b: int)
    requires 0 <= a <= b,
    ensures cnt_int(keys, v, a) <= cnt_int(keys, v, b), cnt_int(keys, v, b) <= b,
    decreases b,
{
    if b > 0 {
        lemma_cnt_mono(keys, v, if a < b { a } else { b - 1 }, b - 1);
    }
}

/// Prefix sums are monotone.
pub proof fn lemma_psum_mono(c: Seq<u32>, a: int, b: int)
    requires 0 <= a <= b,
    ensures psum(c, a) <= psum(c, b),
    decreases b,
{
    if a < b {
        lemma_psum_mono(c, a, b - 1);
    }
}

/// An element is at most the prefix sum past it.
pub proof fn lemma_psum_elem(c: Seq<u32>, e: int, k: int)
    requires 0 <= e < k,
    ensures c[e] <= psum(c, k),
{
    lemma_psum_mono(c, e + 1, k);
    lemma_psum_mono(c, 0, e);
}

/// Incrementing one element below `k` raises the prefix sum over `k` by one.
pub proof fn lemma_psum_inc(c: Seq<u32>, e: int, k: int, x: u32)
    requires 0 <= e < k <= c.len(), x == c[e] + 1,
    ensures psum(c.update(e, x), k) == psum(c, k) + 1,
    decreases k,
{
    let d = c.update(e, x);
    if k - 1 == e {
        assert forall|i: int| 0 <= i < e implies d[i] == c[i] by {}
        lemma_psum_same(c, d, e);
    } else {
        lemma_psum_inc(c, e, k - 1, x);
    }
}

/// Prefix sums over equal prefixes are equal.
pub proof fn lemma_psum_same(c: Seq<u32>, d: Seq<u32>, k: int)
    requires 0 <= k, k <= c.len(), k <= d.len(), forall|i: int| 0 <= i < k ==> c[i] == d[i],
    ensures psum(c, k) == psum(d, k),
    decreases k,
{
    if k > 0 {
        lemma_psum_same(c, d, k - 1);
    }
}

/// The prefix sum of zeros is zero.
pub proof fn lemma_psum_zero(c: Seq<u32>, k: int)
    requires 0 <= k <= c.len(), forall|i: int| 0 <= i < k ==> c[i] == 0,
    ensures psum(c, k) == 0,
    decreases k,
{
    if k > 0 {
        lemma_psum_zero(c, k - 1);
    }
}

/// Entries `e1 < e2` of the directory `[psum(c, e), psum(c, e + 1))` do not overlap.
pub proof fn lemma_entries_ordered(c: Seq<u32>, e1: int, e2: int)
    requires 0 <= e1 < e2,
    ensures psum(c, e1 + 1) <= psum(c, e2),
{
    lemma_psum_mono(c, e1 + 1, e2);
}

} // verus!
