//! Occurrence counts of values in a sequence of `u32` (`occ`): an event list (one entry per event, naming its
//! counter) stands for per-counter counts. Lemmas: one more entry (`lemma_occ_push`), a prefix grown by one entry
//! (`lemma_occ_step`), and a prefix never counts more than the whole (`lemma_occ_prefix`).
use vstd::prelude::*;

verus! {

/// Number of entries of `v` equal to `t`.
pub open spec fn occ(v: Seq<u32>, t: int) -> nat
    decreases v.len(),
{
    if v.len() == 0 {
        0
    } else {
        occ(v.drop_last(), t) + if v.last() as int == t { 1nat } else { 0nat }
    }
}

/// The empty list counts nothing.
pub proof fn lemma_occ_empty(v: Seq<u32>, t: int)
    requires v.len() == 0,
    ensures occ(v, t) == 0,
{
}

/// One more entry `x` counts once more for `x`.
pub proof fn lemma_occ_push(v: Seq<u32>, x: u32, t: int)
    ensures occ(v.push(x), t) == occ(v, t) + if x as int == t { 1nat } else { 0nat },
{
    assert(v.push(x).drop_last() =~= v);
}

/// The prefix of `i + 1` entries counts entry `i` once more than the prefix of `i` entries.
pub proof fn lemma_occ_step(v: Seq<u32>, i: int, t: int)
    requires 0 <= i < v.len(),
    ensures occ(v.subrange(0, i + 1), t) == occ(v.subrange(0, i), t) + if v[i] as int == t { 1nat } else { 0nat },
{
    assert(v.subrange(0, i + 1) =~= v.subrange(0, i).push(v[i]));
    lemma_occ_push(v.subrange(0, i), v[i], t);
}

/// A prefix counts at most what the whole list counts.
pub proof fn lemma_occ_prefix(v: Seq<u32>, i: int, t: int)
    requires 0 <= i <= v.len(),
    ensures occ(v.subrange(0, i), t) <= occ(v, t),
    decreases v.len(),
{
    if i == v.len() {
        assert(v.subrange(0, i) =~= v);
    } else {
        lemma_occ_prefix(v.drop_last(), i, t);
        assert(v.drop_last().subrange(0, i) =~= v.subrange(0, i));
    }
}

} // verus!
