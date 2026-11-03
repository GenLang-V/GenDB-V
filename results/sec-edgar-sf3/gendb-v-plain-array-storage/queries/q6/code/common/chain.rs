//! Chained hash buckets over nodes `0..len`: `head[b]` is the largest node of bucket `b`, `next[x]` the largest
//! node below `x` in `x`'s bucket (`NONE` when there is none). Only nodes with `inset(x)` are linked; `bkt(x)` is
//! the bucket of node `x`. Inserting node `len` at the head of its bucket keeps the invariant (`lemma_insert`), and a
//! walk from `head[b]` along `next` visits every node of bucket `b` in decreasing order, so a walk that ends at
//! `NONE` without a hit proves that no node of the bucket has the probed property (`lemma_walk_*`).
use vstd::prelude::*;

verus! {

/// The end of a chain.
pub const NONE: usize = usize::MAX;

/// `h` is the largest node below `hi` in bucket `b`, or `NONE` when bucket `b` has no node below `hi`.
pub open spec fn below_ok(h: usize, inset: spec_fn(int) -> bool, bkt: spec_fn(int) -> int, hi: int, b: int) -> bool {
    if h == NONE {
        forall|y: int| 0 <= y < hi && #[trigger] inset(y) ==> bkt(y) != b
    } else {
        &&& h < hi
        &&& inset(h as int)
        &&& bkt(h as int) == b
        &&& forall|y: int| h < y < hi && #[trigger] inset(y) ==> bkt(y) != b
    }
}

/// The chain invariant over nodes `0..len`.
pub open spec fn chain_wf(head: Seq<usize>, next: Seq<usize>, inset: spec_fn(int) -> bool, bkt: spec_fn(int) -> int, len: int) -> bool {
    &&& 0 <= len <= next.len()
    &&& len < NONE
    &&& forall|x: int| 0 <= x < len && #[trigger] inset(x) ==> 0 <= bkt(x) < head.len()
    &&& forall|b: int| 0 <= b < head.len() ==> below_ok(#[trigger] head[b], inset, bkt, len, b)
    &&& forall|x: int| 0 <= x < len && inset(x) ==> below_ok(#[trigger] next[x], inset, bkt, x, bkt(x))
}

/// No node yet.
pub proof fn lemma_empty(head: Seq<usize>, next: Seq<usize>, inset: spec_fn(int) -> bool, bkt: spec_fn(int) -> int)
    requires forall|b: int| 0 <= b < head.len() ==> #[trigger] head[b] == NONE,
    ensures chain_wf(head, next, inset, bkt, 0),
{
}

/// The invariant depends only on the nodes below `len`.
pub proof fn lemma_ext(head: Seq<usize>, next: Seq<usize>, inset: spec_fn(int) -> bool, bkt: spec_fn(int) -> int,
    inset2: spec_fn(int) -> bool, bkt2: spec_fn(int) -> int, next2: Seq<usize>, len: int)
    requires
        chain_wf(head, next, inset, bkt, len),
        len <= next2.len(),
        forall|x: int| 0 <= x < len ==> #[trigger] inset2(x) == inset(x),
        forall|x: int| 0 <= x < len && inset(x) ==> #[trigger] bkt2(x) == bkt(x),
        forall|x: int| 0 <= x < len ==> #[trigger] next2[x] == next[x],
    ensures chain_wf(head, next2, inset2, bkt2, len),
{
    assert forall|b: int| 0 <= b < head.len() implies below_ok(#[trigger] head[b], inset2, bkt2, len, b) by {
        assert(below_ok(head[b], inset, bkt, len, b));
        if head[b] != NONE {
            assert(inset(head[b] as int));
        }
    }
    assert forall|x: int| 0 <= x < len && inset2(x) implies below_ok(#[trigger] next2[x], inset2, bkt2, x, bkt2(x)) by {
        assert(inset(x));
        assert(below_ok(next[x], inset, bkt, x, bkt(x)));
        if next[x] != NONE {
            assert(inset(next[x] as int));
        }
    }
}

/// Node `len` is not linked.
pub proof fn lemma_skip(head: Seq<usize>, next: Seq<usize>, inset: spec_fn(int) -> bool, bkt: spec_fn(int) -> int, len: int)
    requires chain_wf(head, next, inset, bkt, len), !inset(len), len + 1 <= next.len(), len + 1 < NONE,
    ensures chain_wf(head, next, inset, bkt, len + 1),
{
    assert forall|b: int| 0 <= b < head.len() implies below_ok(#[trigger] head[b], inset, bkt, len + 1, b) by {
        assert(below_ok(head[b], inset, bkt, len, b));
    }
}

/// Node `len` of bucket `b` linked at the head of its bucket.
pub proof fn lemma_insert(head: Seq<usize>, next: Seq<usize>, inset: spec_fn(int) -> bool, bkt: spec_fn(int) -> int,
    len: int, b: int)
    requires
        chain_wf(head, next, inset, bkt, len),
        inset(len), bkt(len) == b, 0 <= b < head.len(), len + 1 <= next.len(), len + 1 < NONE,
    ensures chain_wf(head.update(b, len as usize), next.update(len, head[b]), inset, bkt, len + 1),
{
    let h2 = head.update(b, len as usize);
    let n2 = next.update(len, head[b]);
    assert forall|b2: int| 0 <= b2 < h2.len() implies below_ok(#[trigger] h2[b2], inset, bkt, len + 1, b2) by {
        assert(below_ok(head[b2], inset, bkt, len, b2));
    }
    assert forall|x: int| 0 <= x < len + 1 && inset(x) implies below_ok(#[trigger] n2[x], inset, bkt, x, bkt(x)) by {
        if x < len {
            assert(n2[x] == next[x]);
        } else {
            assert(below_ok(head[b], inset, bkt, len, b));
        }
    }
}

/// The walk state: `cur` is `NONE` or a node of bucket `b`, and every node of bucket `b` above `cur` (below `len`)
/// has property `p`.
pub open spec fn walk_ok(cur: usize, inset: spec_fn(int) -> bool, bkt: spec_fn(int) -> int, len: int, b: int,
    p: spec_fn(int) -> bool) -> bool {
    &&& (cur != NONE ==> cur < len && inset(cur as int) && bkt(cur as int) == b)
    &&& forall|y: int| (if cur == NONE { 0 } else { cur + 1 }) <= y < len && #[trigger] inset(y) && bkt(y) == b ==> p(y)
}

/// The walk starts at the head of bucket `b`.
pub proof fn lemma_walk_start(head: Seq<usize>, next: Seq<usize>, inset: spec_fn(int) -> bool, bkt: spec_fn(int) -> int,
    len: int, b: int, p: spec_fn(int) -> bool)
    requires chain_wf(head, next, inset, bkt, len), 0 <= b < head.len(),
    ensures walk_ok(head[b], inset, bkt, len, b, p),
{
    assert(below_ok(head[b], inset, bkt, len, b));
}

/// A node with property `p` passed: the walk continues at its `next`.
pub proof fn lemma_walk_step(head: Seq<usize>, next: Seq<usize>, inset: spec_fn(int) -> bool, bkt: spec_fn(int) -> int,
    len: int, b: int, p: spec_fn(int) -> bool, cur: usize)
    requires chain_wf(head, next, inset, bkt, len), walk_ok(cur, inset, bkt, len, b, p), cur != NONE, p(cur as int),
    ensures walk_ok(next[cur as int], inset, bkt, len, b, p), next[cur as int] == NONE || next[cur as int] < cur,
{
    let x = cur as int;
    assert(below_ok(next[x], inset, bkt, x, bkt(x)));
}

/// A walk that reached `NONE`: every node of bucket `b` has property `p`.
pub proof fn lemma_walk_done(inset: spec_fn(int) -> bool, bkt: spec_fn(int) -> int, len: int, b: int, p: spec_fn(int) -> bool)
    requires walk_ok(NONE, inset, bkt, len, b, p),
    ensures forall|y: int| 0 <= y < len && #[trigger] inset(y) && bkt(y) == b ==> p(y),
{
}

} // verus!
