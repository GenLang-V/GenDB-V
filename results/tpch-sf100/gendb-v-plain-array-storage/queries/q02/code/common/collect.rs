//! Batch selection on an `i64` column: the positions of a row range whose value equals a target, in increasing
//! order, written into a preallocated batch (a sequential, branch-light first pass of a batched scan). The 4-lane
//! form selects from four row ranges at once, one block of `EQ_BLOCK` rows of each in turn, so a single thread
//! keeps four memory streams in flight.
use vstd::prelude::*;

verus! {

/// The positions `x` of `[from, to)` with `vals[x] == target`, in increasing order, as `batch[0..k]`.
pub fn collect_equal(vals: &[i64], n: usize, from: usize, to: usize, target: i64, batch: &mut Vec<usize>) -> (k: usize)
    requires
        vals@.len() == n,
        from <= to <= n,
        to - from <= old(batch)@.len(),
    ensures
        final(batch)@.len() == old(batch)@.len(),
        k <= to - from,
        forall|i: int| 0 <= i < k ==> from <= #[trigger] final(batch)@[i] < to && vals@[final(batch)@[i] as int] == target,
        forall|i: int, i2: int| 0 <= i < i2 < k ==> final(batch)@[i] < final(batch)@[i2],
        forall|y: int| from <= y < to && #[trigger] vals@[y] == target ==> exists|i: int| 0 <= i < k && final(batch)@[i] == y,
    no_unwind
{
    let ghost len0 = batch@.len();
    let mut k: usize = 0;
    let mut x = from;
    while x < to
        invariant
            batch@.len() == len0,
            vals@.len() == n,
            from <= x <= to <= n,
            to - from <= batch@.len(),
            k <= x - from,
            forall|i: int| 0 <= i < k ==> from <= #[trigger] batch@[i] < x && vals@[batch@[i] as int] == target,
            forall|i: int, i2: int| 0 <= i < i2 < k ==> batch@[i] < batch@[i2],
            forall|y: int| from <= y < x && #[trigger] vals@[y] == target ==> exists|i: int| 0 <= i < k && batch@[i] == y,
        decreases to - x,
    {
        let ghost old_batch = batch@;
        let ghost old_k = k;
        if vals[x] == target {
            batch[k] = x;
            k = k + 1;
        }
        proof {
            assert forall|y: int| from <= y < x + 1 && #[trigger] vals@[y] == target
                implies exists|i: int| 0 <= i < k && batch@[i] == y by {
                if y < x {
                    let i = choose|i: int| 0 <= i < old_k && old_batch[i] == y;
                    assert(batch@[i] == y);
                } else {
                    assert(batch@[old_k as int] == y);
                }
            }
        }
        x = x + 1;
    }
    k
}

/// Rows per block of the 4-lane selection.
pub const EQ_BLOCK: usize = 64;

/// `batch[0..k]` lists, in increasing order, exactly the positions `y` of `[from, to)` with `vals[y] == target`.
pub open spec fn eq_collected(vals: Seq<i64>, from: int, to: int, target: i64, batch: Seq<usize>, k: int) -> bool {
    &&& 0 <= k <= to - from
    &&& k <= batch.len()
    &&& forall|i: int| 0 <= i < k ==> from <= #[trigger] batch[i] < to && vals[batch[i] as int] == target
    &&& forall|i: int, i2: int| 0 <= i < i2 < k ==> batch[i] < batch[i2]
    &&& forall|y: int| from <= y < to && #[trigger] vals[y] == target ==> exists|i: int| 0 <= i < k && batch[i] == y
}

/// Extends a selection over `[from, x)` by block `[x, x + EQ_BLOCK)` (taken as a constant-length sub-slice, so
/// the loop has no bounds checks on `vals`).
#[inline(always)]
pub fn equal_block_step(vals: &[i64], n: usize, Ghost(from): Ghost<int>, x: usize, target: i64, batch: &mut Vec<usize>, k0: usize) -> (k: usize)
    requires
        vals@.len() == n,
        from <= x,
        x + EQ_BLOCK <= n,
        k0 + EQ_BLOCK <= old(batch)@.len(),
        eq_collected(vals@, from, x as int, target, old(batch)@, k0 as int),
    ensures
        final(batch)@.len() == old(batch)@.len(),
        k0 <= k <= k0 + EQ_BLOCK,
        eq_collected(vals@, from, x + EQ_BLOCK, target, final(batch)@, k as int),
    no_unwind
{
    let (_, tail) = vals.split_at(x);
    let (blk, _) = tail.split_at(EQ_BLOCK);
    assert(forall|q: int| 0 <= q < EQ_BLOCK ==> #[trigger] blk@[q] == vals@[x + q]);
    let ghost b0 = batch@;
    let blen = batch.len();
    let mut k = k0;
    let mut i: usize = 0;
    while i < EQ_BLOCK
        invariant
            blk@.len() == EQ_BLOCK,
            forall|q: int| 0 <= q < EQ_BLOCK ==> #[trigger] blk@[q] == vals@[x + q],
            vals@.len() == n,
            x + EQ_BLOCK <= n,
            from <= x,
            batch@.len() == b0.len(),
            b0.len() == blen,
            k0 + EQ_BLOCK <= b0.len(),
            i <= EQ_BLOCK,
            k0 <= k <= k0 + i,
            eq_collected(vals@, from, x as int, target, b0, k0 as int),
            forall|q: int| 0 <= q < k0 ==> #[trigger] batch@[q] == b0[q],
            forall|q: int| k0 <= q < k ==> x <= #[trigger] batch@[q] < x + i && vals@[batch@[q] as int] == target,
            forall|q: int, q2: int| k0 <= q < q2 < k ==> batch@[q] < batch@[q2],
            forall|y: int| x <= y < x + i && #[trigger] vals@[y] == target ==> exists|q: int| k0 <= q < k && batch@[q] == y,
        decreases EQ_BLOCK - i,
    {
        let ghost old_batch = batch@;
        let ghost old_k = k;
        if blk[i] == target {
            batch[k] = x + i;
            k = k + 1;
        }
        proof {
            assert forall|y: int| x <= y < x + i + 1 && #[trigger] vals@[y] == target
                implies exists|q: int| k0 <= q < k && batch@[q] == y by {
                if y < x + i {
                    let q = choose|q: int| k0 <= q < old_k && old_batch[q] == y;
                    assert(batch@[q] == y);
                } else {
                    assert(batch@[old_k as int] == y);
                }
            }
        }
        i = i + 1;
    }
    proof {
        assert forall|q: int| 0 <= q < k implies from <= #[trigger] batch@[q] < x + EQ_BLOCK && vals@[batch@[q] as int] == target by {
            if q < k0 { assert(batch@[q] == b0[q]); }
        }
        assert forall|q: int, q2: int| 0 <= q < q2 < k implies batch@[q] < batch@[q2] by {
            if q2 < k0 {
                assert(batch@[q] == b0[q] && batch@[q2] == b0[q2]);
            } else if q < k0 {
                assert(batch@[q] == b0[q]);
            }
        }
        assert forall|y: int| from <= y < x + EQ_BLOCK && #[trigger] vals@[y] == target implies exists|q: int| 0 <= q < k && batch@[q] == y by {
            if y < x {
                let q = choose|q: int| 0 <= q < k0 && b0[q] == y;
                assert(batch@[q] == y);
            } else {
                let q = choose|q: int| k0 <= q < k && batch@[q] == y;
            }
        }
    }
    k
}

/// Four selections at once: lane `l` selects the positions of `[a_l, a_l + len)` with `vals == target` into `b_l`
/// (`len` a multiple of `EQ_BLOCK`), one block of each lane in turn.
pub fn collect_equal4(vals: &[i64], n: usize, a0: usize, a1: usize, a2: usize, a3: usize, len: usize, target: i64,
    b0: &mut Vec<usize>, b1: &mut Vec<usize>, b2: &mut Vec<usize>, b3: &mut Vec<usize>) -> (r: (usize, usize, usize, usize))
    requires
        vals@.len() == n,
        len % EQ_BLOCK == 0,
        a0 + len <= n, a1 + len <= n, a2 + len <= n, a3 + len <= n,
        len <= old(b0)@.len(), len <= old(b1)@.len(), len <= old(b2)@.len(), len <= old(b3)@.len(),
    ensures
        final(b0)@.len() == old(b0)@.len(), final(b1)@.len() == old(b1)@.len(),
        final(b2)@.len() == old(b2)@.len(), final(b3)@.len() == old(b3)@.len(),
        eq_collected(vals@, a0 as int, a0 + len, target, final(b0)@, r.0 as int),
        eq_collected(vals@, a1 as int, a1 + len, target, final(b1)@, r.1 as int),
        eq_collected(vals@, a2 as int, a2 + len, target, final(b2)@, r.2 as int),
        eq_collected(vals@, a3 as int, a3 + len, target, final(b3)@, r.3 as int),
    no_unwind
{
    let ghost (l0, l1, l2, l3) = (b0@.len(), b1@.len(), b2@.len(), b3@.len());
    let mut k0: usize = 0;
    let mut k1: usize = 0;
    let mut k2: usize = 0;
    let mut k3: usize = 0;
    let mut x: usize = 0;
    while x < len
        invariant
            vals@.len() == n,
            len % EQ_BLOCK == 0,
            x % EQ_BLOCK == 0,
            x <= len,
            a0 + len <= n, a1 + len <= n, a2 + len <= n, a3 + len <= n,
            b0@.len() == l0, b1@.len() == l1, b2@.len() == l2, b3@.len() == l3,
            len <= l0, len <= l1, len <= l2, len <= l3,
            eq_collected(vals@, a0 as int, a0 + x, target, b0@, k0 as int),
            eq_collected(vals@, a1 as int, a1 + x, target, b1@, k1 as int),
            eq_collected(vals@, a2 as int, a2 + x, target, b2@, k2 as int),
            eq_collected(vals@, a3 as int, a3 + x, target, b3@, k3 as int),
        decreases len - x,
    {
        assert(x + EQ_BLOCK <= len) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, EQ_BLOCK as int);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(len as int, EQ_BLOCK as int);
        }
        k0 = equal_block_step(vals, n, Ghost(a0 as int), a0 + x, target, b0, k0);
        k1 = equal_block_step(vals, n, Ghost(a1 as int), a1 + x, target, b1, k1);
        k2 = equal_block_step(vals, n, Ghost(a2 as int), a2 + x, target, b2, k2);
        k3 = equal_block_step(vals, n, Ghost(a3 as int), a3 + x, target, b3, k3);
        x = x + EQ_BLOCK;
    }
    (k0, k1, k2, k3)
}

} // verus!
