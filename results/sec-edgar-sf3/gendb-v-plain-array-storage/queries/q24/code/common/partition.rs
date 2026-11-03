//! Partition (counting-sort scatter) of `len` items `(key, aux)` by the top 8 bits of the key into `PARTS`
//! segments, `no_unwind` with caller-allocated buffers (usable in a worker task).
//!
//! Layout of the result (`Parted`): segment `p` is `keys/auxs[starts[p] .. ends[p]]`; segments are disjoint and
//! in partition order. Invariant (`parted_ok`): every item of segment `p` has key partition `p` and is one of the
//! input items (soundness), and every input item lies in the segment of its key's partition (completeness). The
//! scatter fails (`None`) instead of overflowing a segment, so no counting argument is needed: a caller treats a
//! failure as "no result".
use vstd::prelude::*;

verus! {

pub const PART_SHIFT: u64 = 56;
pub const PARTS: usize = 256;

/// The partition of a key: its top 8 bits.
pub open spec fn part_of(k: u64) -> int {
    (k >> PART_SHIFT) as int
}

pub fn part_exec(k: u64) -> (p: usize)
    ensures p == part_of(k), p < PARTS,
    no_unwind
{
    assert((k >> 56u64) < 256u64) by (bit_vector);
    (k >> PART_SHIFT) as usize
}

/// Partitioned items: segment `p` is `keys/auxs[starts[p] .. ends[p]]`.
pub struct Parted {
    pub keys: Vec<u64>,
    pub auxs: Vec<u64>,
    pub starts: Vec<usize>,
    pub ends: Vec<usize>,
}

/// Position `e` lies in segment `p`.
pub open spec fn in_seg(o: Parted, p: int, e: int) -> bool {
    0 <= p < PARTS && o.starts@[p] <= e < o.ends@[p]
}

/// Item `(k, x)` is one of the input items.
pub open spec fn src_item(ks: Seq<u64>, xs: Seq<u64>, k: u64, x: u64) -> bool {
    exists|q: int| 0 <= q < ks.len() && #[trigger] ks[q] == k && xs[q] == x
}

/// Segment `p` of `o` holds item `(k, x)`.
pub open spec fn seg_has(o: Parted, p: int, k: u64, x: u64) -> bool {
    exists|e: int| #[trigger] in_seg(o, p, e) && o.keys@[e] == k && o.auxs@[e] == x
}

/// The segments lie inside the buffers.
pub open spec fn segs_ok(o: Parted) -> bool {
    &&& o.keys@.len() == o.auxs@.len()
    &&& o.starts@.len() == PARTS && o.ends@.len() == PARTS
    &&& forall|p: int| 0 <= p < PARTS ==> #[trigger] o.starts@[p] <= o.ends@[p] && o.ends@[p] <= o.keys@.len()
}

/// `o` partitions the input items `(ks[q], xs[q])`.
pub open spec fn parted_ok(o: Parted, ks: Seq<u64>, xs: Seq<u64>) -> bool {
    &&& segs_ok(o)
    &&& forall|p: int, e: int| #[trigger] in_seg(o, p, e) ==>
            part_of(o.keys@[e]) == p && src_item(ks, xs, o.keys@[e], o.auxs@[e])
    &&& forall|q: int| 0 <= q < ks.len() ==> #[trigger] seg_has(o, part_of(ks[q]), ks[q], xs[q])
}

/// Position `e` of the filled part `b[a] .. cur[a]` of segment `a`.
pub open spec fn filled(b: Seq<usize>, cur: Seq<usize>, a: int, e: int) -> bool {
    0 <= a < PARTS && b[a] <= e < cur[a]
}

/// Item `(k, x)` sits in the filled part of the segment of its key's partition.
pub open spec fn placed(b: Seq<usize>, cur: Seq<usize>, keys: Seq<u64>, auxs: Seq<u64>, k: u64, x: u64) -> bool {
    exists|e: int| #[trigger] filled(b, cur, part_of(k), e) && keys[e] == k && auxs[e] == x
}

/// Partition the first `len` items of `ks`/`xs` into `keys`/`auxs` (at least `len` slots each), with `starts`
/// and `ends` (`PARTS` zeros each) for the segment bounds. `Some` result: `parted_ok`.
pub fn partition(ks: &Vec<u64>, xs: &Vec<u64>, len: usize, keys: Vec<u64>, auxs: Vec<u64>, starts: Vec<usize>,
    ends: Vec<usize>) -> (r: Option<Parted>)
    requires
        len <= ks@.len(), len <= xs@.len(),
        starts@.len() == PARTS, ends@.len() == PARTS,
        forall|p: int| 0 <= p < PARTS ==> #[trigger] ends@[p] == 0,
        keys@.len() >= len, auxs@.len() == keys@.len(),
    ensures
        r matches Some(o) ==> parted_ok(o, ks@.subrange(0, len as int), xs@.subrange(0, len as int)),
    no_unwind
{
    let ghost kss = ks@.subrange(0, len as int);
    let ghost xss = xs@.subrange(0, len as int);
    let mut keys = keys;
    let mut auxs = auxs;
    let mut starts = starts;
    let mut cursor = ends;
    let cap = keys.len();
    // Count the items of every partition (in `cursor`).
    let mut q: usize = 0;
    while q < len
        invariant
            q <= len, len <= ks@.len(), cursor@.len() == PARTS,
            forall|p: int| 0 <= p < PARTS ==> #[trigger] cursor@[p] <= q,
        decreases len - q,
    {
        let p = part_exec(ks[q]);
        let ghost before = cursor@;
        cursor[p] = cursor[p] + 1;
        proof {
            assert forall|p2: int| 0 <= p2 < PARTS implies #[trigger] cursor@[p2] <= q + 1 by {
                if p2 != p as int {
                    assert(cursor@[p2] == before[p2]);
                }
            }
        }
        q = q + 1;
    }
    // Segment starts: `b[p]` is the sum of the counts below `p` (`b[PARTS]` the total); cursors restart at them.
    let ghost mut b: Seq<usize> = seq![0usize];
    let mut acc: usize = 0;
    let mut p: usize = 0;
    while p < PARTS
        invariant
            p <= PARTS, acc <= cap, cursor@.len() == PARTS, starts@.len() == PARTS,
            b.len() == p + 1, b[p as int] == acc,
            forall|a: int, c: int| #![trigger b[a], b[c]] 0 <= a <= c <= p ==> b[a] <= b[c],
            forall|a: int| 0 <= a < p ==> #[trigger] starts@[a] == b[a] && cursor@[a] == b[a],
        decreases PARTS - p,
    {
        let count = cursor[p];
        if count > cap - acc {
            return None;
        }
        starts[p] = acc;
        cursor[p] = acc;
        acc = acc + count;
        proof {
            b = b.push(acc);
        }
        p = p + 1;
    }
    proof {
        assert forall|a: int| 0 <= a < PARTS implies b[a] <= #[trigger] cursor@[a] && cursor@[a] <= b[a + 1] by {
            assert(starts@[a] == b[a]);
            assert(cursor@[a] == b[a]);
            assert(b[a] <= b[a + 1]);
        }
        assert forall|a: int, e: int| #[trigger] filled(b, cursor@, a, e) implies
            part_of(keys@[e]) == a && src_item(kss, xss, keys@[e], auxs@[e]) by {
            assert(starts@[a] == b[a]);
            assert(cursor@[a] == b[a]);
        }
    }
    // Scatter: item `q` goes to the cursor of its partition.
    let mut q: usize = 0;
    while q < len
        invariant
            q <= len, len <= ks@.len(), len <= xs@.len(),
            kss == ks@.subrange(0, len as int), xss == xs@.subrange(0, len as int),
            cursor@.len() == PARTS, starts@.len() == PARTS,
            keys@.len() == cap, auxs@.len() == cap,
            b.len() == PARTS + 1, b[PARTS as int] <= cap, b[PARTS as int] == acc,
            forall|a: int, c: int| #![trigger b[a], b[c]] 0 <= a <= c <= PARTS ==> b[a] <= b[c],
            forall|a: int| 0 <= a < PARTS ==> #[trigger] starts@[a] == b[a],
            forall|a: int| 0 <= a < PARTS ==> b[a] <= #[trigger] cursor@[a] && cursor@[a] <= b[a + 1],
            forall|a: int, e: int| #[trigger] filled(b, cursor@, a, e) ==>
                part_of(keys@[e]) == a && src_item(kss, xss, keys@[e], auxs@[e]),
            forall|t: int| 0 <= t < q ==> #[trigger] placed(b, cursor@, keys@, auxs@, kss[t], xss[t]),
        decreases len - q,
    {
        let k = ks[q];
        let x = xs[q];
        let p = part_exec(k);
        let pos = cursor[p];
        let end = if p + 1 < PARTS { starts[p + 1] } else { acc };
        proof {
            assert(end == b[p + 1]);
        }
        if pos >= end {
            return None;
        }
        let ghost keys0 = keys@;
        let ghost auxs0 = auxs@;
        let ghost cur0 = cursor@;
        keys[pos] = k;
        auxs[pos] = x;
        cursor[p] = pos + 1;
        proof {
            assert(kss[q as int] == k && xss[q as int] == x);
            // `pos` is outside the filled part of every other segment.
            assert forall|a: int, e: int| #[trigger] filled(b, cur0, a, e) && a != p as int implies e != pos as int by {
                if a < p as int {
                    assert(b[a + 1] <= b[p as int]);
                } else {
                    assert(b[p as int + 1] <= b[a]);
                }
            }
            assert forall|a: int, e: int| #[trigger] filled(b, cursor@, a, e) implies
                part_of(keys@[e]) == a && src_item(kss, xss, keys@[e], auxs@[e]) by {
                if e == pos as int {
                    if a != p as int {
                        assert(cursor@[a] == cur0[a]);
                        assert(filled(b, cur0, a, e));
                    }
                    assert(src_item(kss, xss, k, x));
                } else {
                    if a == p as int {
                        assert(filled(b, cur0, a, e));
                    } else {
                        assert(cursor@[a] == cur0[a]);
                        assert(filled(b, cur0, a, e));
                    }
                }
            }
            assert forall|t: int| 0 <= t < q + 1 implies #[trigger] placed(b, cursor@, keys@, auxs@, kss[t], xss[t]) by {
                if t == q as int {
                    let a = part_of(kss[t]);
                    assert(a == p as int);
                    assert(keys@[pos as int] == kss[t]);
                    assert(auxs@[pos as int] == xss[t]);
                    assert(filled(b, cursor@, a, pos as int));
                } else {
                    let a = part_of(kss[t]);
                    assert(placed(b, cur0, keys0, auxs0, kss[t], xss[t]));
                    let e = choose|e: int| #[trigger] filled(b, cur0, a, e) && keys0[e] == kss[t] && auxs0[e] == xss[t];
                    if a != p as int {
                        assert(e != pos as int);
                        assert(cursor@[a] == cur0[a]);
                    } else {
                        assert(e < pos as int);
                    }
                    assert(keys@[e] == keys0[e]);
                    assert(auxs@[e] == auxs0[e]);
                    assert(filled(b, cursor@, a, e));
                }
            }
        }
        q = q + 1;
    }
    let o = Parted { keys, auxs, starts, ends: cursor };
    proof {
        assert forall|a: int| 0 <= a < PARTS implies #[trigger] o.starts@[a] <= o.ends@[a] && o.ends@[a] <= o.keys@.len() by {
            assert(b[a + 1] <= b[PARTS as int]);
        }
        assert forall|a: int, e: int| #[trigger] in_seg(o, a, e) implies
            part_of(o.keys@[e]) == a && src_item(kss, xss, o.keys@[e], o.auxs@[e]) by {
            assert(filled(b, cursor@, a, e));
        }
        assert forall|t: int| 0 <= t < kss.len() implies #[trigger] seg_has(o, part_of(kss[t]), kss[t], xss[t]) by {
            let a = part_of(kss[t]);
            assert(placed(b, cursor@, keys@, auxs@, kss[t], xss[t]));
            let e = choose|e: int| #[trigger] filled(b, cursor@, a, e) && keys@[e] == kss[t] && auxs@[e] == xss[t];
            assert(in_seg(o, a, e));
        }
    }
    Some(o)
}

} // verus!
