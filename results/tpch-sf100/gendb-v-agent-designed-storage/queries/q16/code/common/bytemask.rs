//! Byte filters over chunks of 64 bytes: `eq8_hits` flags every byte equal to one of eight given values (one
//! branch-free loop of comparisons, which the compiler vectorizes), and `compact64` lists the flagged positions in
//! increasing order (branch-free: every position is written, the count advances by its flag). Worker bodies cannot
//! allocate, so the callers own the 64-entry scratch arrays.
use vstd::prelude::*;

verus! {

broadcast use vstd::array::group_array_axioms;

/// `v` is one of the eight values `cv`.
pub open spec fn in8(cv: [u8; 8], v: u8) -> bool {
    exists|i: int| 0 <= i < 8 && cv@[i] == v
}

/// `hits` flags (0 or 1) exactly the bytes of `ch` that are one of `cv`.
pub open spec fn hits_ok(ch: Seq<u8>, cv: [u8; 8], hits: [u8; 64]) -> bool {
    forall|k: int| 0 <= k < 64 ==> #[trigger] hits@[k] <= 1u8 && (hits@[k] == 1u8 <==> in8(cv, ch[k]))
}

/// `idx[..n]` lists the flagged positions of `hits`, in increasing order.
pub open spec fn compact_ok(hits: [u8; 64], idx: [u8; 64], n: int) -> bool {
    &&& 0 <= n <= 64
    &&& forall|i: int| 0 <= i < n ==> #[trigger] idx@[i] < 64 && hits@[idx@[i] as int] == 1u8
    &&& forall|i1: int, i2: int| 0 <= i1 < i2 < n ==> #[trigger] idx@[i1] < #[trigger] idx@[i2]
    &&& forall|k: int| 0 <= k < 64 && #[trigger] hits@[k] == 1u8 ==> exists|i: int| 0 <= i < n && idx@[i] == k
}

proof fn lemma_or8(e0: u8, e1: u8, e2: u8, e3: u8, e4: u8, e5: u8, e6: u8, e7: u8)
    by (bit_vector)
    requires e0 <= 1, e1 <= 1, e2 <= 1, e3 <= 1, e4 <= 1, e5 <= 1, e6 <= 1, e7 <= 1,
    ensures
        (e0 | e1 | e2 | e3 | e4 | e5 | e6 | e7) <= 1u8,
        ((e0 | e1 | e2 | e3 | e4 | e5 | e6 | e7) == 1u8) == (e0 == 1u8 || e1 == 1u8 || e2 == 1u8 || e3 == 1u8
            || e4 == 1u8 || e5 == 1u8 || e6 == 1u8 || e7 == 1u8),
{
}

/// Flags the bytes of `ch` (64 of them) equal to one of `cv`.
pub fn eq8_hits(ch: &[u8], cv: &[u8; 8], hits: &mut [u8; 64])
    requires ch@.len() == 64,
    ensures hits_ok(ch@, *cv, *final(hits)),
    no_unwind
{
    let (c0, c1, c2, c3, c4, c5, c6, c7) = (cv[0], cv[1], cv[2], cv[3], cv[4], cv[5], cv[6], cv[7]);
    let mut k: usize = 0;
    while k < 64
        invariant
            k <= 64, ch@.len() == 64,
            c0 == cv@[0], c1 == cv@[1], c2 == cv@[2], c3 == cv@[3],
            c4 == cv@[4], c5 == cv@[5], c6 == cv@[6], c7 == cv@[7],
            forall|k2: int| 0 <= k2 < k ==> #[trigger] hits@[k2] <= 1u8 && (hits@[k2] == 1u8 <==> in8(*cv, ch@[k2])),
        decreases 64 - k,
    {
        let c = ch[k];
        let e0: u8 = if c == c0 { 1 } else { 0 };
        let e1: u8 = if c == c1 { 1 } else { 0 };
        let e2: u8 = if c == c2 { 1 } else { 0 };
        let e3: u8 = if c == c3 { 1 } else { 0 };
        let e4: u8 = if c == c4 { 1 } else { 0 };
        let e5: u8 = if c == c5 { 1 } else { 0 };
        let e6: u8 = if c == c6 { 1 } else { 0 };
        let e7: u8 = if c == c7 { 1 } else { 0 };
        let h: u8 = e0 | e1 | e2 | e3 | e4 | e5 | e6 | e7;
        proof {
            lemma_or8(e0, e1, e2, e3, e4, e5, e6, e7);
            if in8(*cv, c) {
                let i = choose|i: int| 0 <= i < 8 && cv@[i] == c;
                assert(h == 1u8);
            }
            if h == 1u8 {
                if c == c0 { assert(cv@[0] == c); }
                else if c == c1 { assert(cv@[1] == c); }
                else if c == c2 { assert(cv@[2] == c); }
                else if c == c3 { assert(cv@[3] == c); }
                else if c == c4 { assert(cv@[4] == c); }
                else if c == c5 { assert(cv@[5] == c); }
                else if c == c6 { assert(cv@[6] == c); }
                else { assert(cv@[7] == c); }
            }
        }
        hits[k] = h;
        k = k + 1;
    }
}

/// Lists the flagged positions of `hits` in `idx`, increasing; returns their number.
pub fn compact64(hits: &[u8; 64], idx: &mut [u8; 64]) -> (n: usize)
    requires forall|k: int| 0 <= k < 64 ==> #[trigger] hits@[k] <= 1u8,
    ensures compact_ok(*hits, *final(idx), n as int),
    no_unwind
{
    let mut n: usize = 0;
    let mut k: usize = 0;
    while k < 64
        invariant
            k <= 64, n <= k,
            forall|k2: int| 0 <= k2 < 64 ==> #[trigger] hits@[k2] <= 1u8,
            forall|i: int| 0 <= i < n ==> #[trigger] idx@[i] < k && hits@[idx@[i] as int] == 1u8,
            forall|i1: int, i2: int| 0 <= i1 < i2 < n ==> #[trigger] idx@[i1] < #[trigger] idx@[i2],
            forall|k2: int| 0 <= k2 < k && #[trigger] hits@[k2] == 1u8 ==> exists|i: int| 0 <= i < n && idx@[i] == k2,
        decreases 64 - k,
    {
        let ghost i0 = idx@;
        // Write unconditionally; keep the slot only when the position is flagged.
        idx[n] = k as u8;
        let h = hits[k];
        n = n + h as usize;
        proof {
            assert forall|i: int| 0 <= i < n implies #[trigger] idx@[i] < k + 1 && hits@[idx@[i] as int] == 1u8 by {
                if i < n - h { assert(idx@[i] == i0[i]); }
            }
            assert forall|i1: int, i2: int| 0 <= i1 < i2 < n implies #[trigger] idx@[i1] < #[trigger] idx@[i2] by {
                assert(idx@[i1] == i0[i1]);
                if i2 < n - h { assert(idx@[i2] == i0[i2]); }
            }
            assert forall|k2: int| 0 <= k2 < k + 1 && #[trigger] hits@[k2] == 1u8 implies
                exists|i: int| 0 <= i < n && idx@[i] == k2 by {
                if k2 < k {
                    let i = choose|i: int| 0 <= i < n - h && i0[i] == k2;
                    assert(idx@[i] == i0[i]);
                } else {
                    assert(idx@[n - 1] == k2);
                }
            }
        }
        k = k + 1;
    }
    n
}

} // verus!
