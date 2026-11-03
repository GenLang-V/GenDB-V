//! The run permutation by length: the runs of a run-length directory ordered by length (longest first), then by
//! run index, as U32 run indices and U32 start rows. One pass finds the longest length `lmax`; then one pass per
//! length `lmax, lmax - 1, .., 1` appends the runs of that length in run order, with their start rows (the running
//! sum of the lengths).
//!
//! Proof: only the first class is specified (`long_built`): the pass over length `lmax` appends run `r` exactly
//! when its length is `lmax`, so the class is ascending and lists every run of that length; the later passes only
//! append (`push_class` keeps the prefix).
use vstd::prelude::*;
use crate::stores::liruns::interface::{rstart, long_at, long_listed};
use super::runs::lemma_rstart_mono;

verus! {

/// The first `nlong` entries of `lr` / `ls` are exactly the runs of length `lmax` (no run is longer), ascending,
/// with their start rows.
pub open spec fn long_built(lens: Seq<u8>, lr: Seq<u32>, ls: Seq<u32>, lmax: int, nlong: int) -> bool {
    &&& nlong <= lr.len() && nlong <= ls.len()
    &&& forall|r: int| 0 <= r < lens.len() ==> #[trigger] lens[r] <= lmax
    &&& forall|i: int| 0 <= i < nlong ==> #[trigger] long_at(lens, lr, ls, lmax, i)
    &&& forall|a: int, b: int| 0 <= a < b < nlong ==> #[trigger] lr[a] < #[trigger] lr[b]
    &&& forall|r: int| 0 <= r < lens.len() && lens[r] == lmax ==> #[trigger] long_listed(lr, nlong, r)
}

/// The longest run length.
fn longest(lens: &Vec<u8>) -> (lmax: u8)
    ensures forall|r: int| 0 <= r < lens@.len() ==> #[trigger] lens@[r] <= lmax,
{
    let mut lmax: u8 = 0;
    let mut r: usize = 0;
    while r < lens.len()
        invariant
            r <= lens@.len(),
            forall|t: int| 0 <= t < r ==> #[trigger] lens@[t] <= lmax,
        decreases lens@.len() - r,
    {
        if lens[r] > lmax {
            lmax = lens[r];
        }
        r = r + 1;
    }
    lmax
}

/// Appends the runs of length `k` in run order (their run indices and start rows); keeps every earlier entry.
fn push_class(lens: &Vec<u8>, k: u8, lr: &mut Vec<u32>, ls: &mut Vec<u32>)
    requires
        lens@.len() <= u32::MAX,
        rstart(lens@, lens@.len() as int) <= u32::MAX,
        old(lr)@.len() == old(ls)@.len(),
    ensures
        final(lr)@.len() == final(ls)@.len(),
        final(lr)@.len() >= old(lr)@.len(),
        forall|i: int| 0 <= i < old(lr)@.len() ==> #[trigger] final(lr)@[i] == old(lr)@[i],
        forall|i: int| 0 <= i < old(ls)@.len() ==> #[trigger] final(ls)@[i] == old(ls)@[i],
{
    let ghost lr0 = lr@;
    let ghost ls0 = ls@;
    let ghost total = rstart(lens@, lens@.len() as int);
    let mut pos: u64 = 0;
    let mut r: usize = 0;
    while r < lens.len()
        invariant
            lens@.len() <= u32::MAX,
            total == rstart(lens@, lens@.len() as int), total <= u32::MAX,
            r <= lens@.len(),
            pos as int == rstart(lens@, r as int),
            lr@.len() == ls@.len(), lr@.len() >= lr0.len(),
            forall|i: int| 0 <= i < lr0.len() ==> #[trigger] lr@[i] == lr0[i],
            forall|i: int| 0 <= i < ls0.len() ==> #[trigger] ls@[i] == ls0[i],
            lr0.len() == ls0.len(),
        decreases lens@.len() - r,
    {
        proof {
            lemma_rstart_mono(lens@, r as int + 1, lens@.len() as int);
        }
        let ln = lens[r];
        if ln == k {
            let ghost lr1 = lr@;
            let ghost ls1 = ls@;
            lr.push(r as u32);
            ls.push(pos as u32);
            proof {
                assert forall|i: int| 0 <= i < lr0.len() implies #[trigger] lr@[i] == lr0[i] by {
                    assert(lr1[i] == lr0[i]);
                    assert(lr@[i] == lr1[i]);
                }
                assert forall|i: int| 0 <= i < ls0.len() implies #[trigger] ls@[i] == ls0[i] by {
                    assert(ls1[i] == ls0[i]);
                    assert(ls@[i] == ls1[i]);
                }
            }
        }
        pos = pos + ln as u64;
        r = r + 1;
    }
}

/// The runs of length `lmax` (no run longer) in run order, with their start rows.
fn longest_class(lens: &Vec<u8>, lmax: u8) -> (r: (Vec<u32>, Vec<u32>))
    requires
        lens@.len() <= u32::MAX,
        rstart(lens@, lens@.len() as int) <= u32::MAX,
        forall|t: int| 0 <= t < lens@.len() ==> #[trigger] lens@[t] <= lmax,
    ensures
        r.0@.len() == r.1@.len(),
        long_built(lens@, r.0@, r.1@, lmax as int, r.0@.len() as int),
{
    let ghost total = rstart(lens@, lens@.len() as int);
    let mut lr: Vec<u32> = Vec::new();
    let mut ls: Vec<u32> = Vec::new();
    let mut pos: u64 = 0;
    let mut r: usize = 0;
    while r < lens.len()
        invariant
            lens@.len() <= u32::MAX,
            total == rstart(lens@, lens@.len() as int), total <= u32::MAX,
            forall|t: int| 0 <= t < lens@.len() ==> #[trigger] lens@[t] <= lmax,
            r <= lens@.len(),
            pos as int == rstart(lens@, r as int),
            lr@.len() == ls@.len(),
            forall|i: int| 0 <= i < lr@.len() ==> #[trigger] long_at(lens@, lr@, ls@, lmax as int, i),
            forall|i: int| 0 <= i < lr@.len() ==> #[trigger] lr@[i] < r,
            forall|a: int, b: int| 0 <= a < b < lr@.len() ==> #[trigger] lr@[a] < #[trigger] lr@[b],
            forall|t: int| 0 <= t < r && lens@[t] == lmax ==> #[trigger] long_listed(lr@, lr@.len() as int, t),
        decreases lens@.len() - r,
    {
        proof {
            lemma_rstart_mono(lens@, r as int + 1, lens@.len() as int);
        }
        let ln = lens[r];
        if ln == lmax {
            let ghost lr0 = lr@;
            let ghost ls0 = ls@;
            lr.push(r as u32);
            ls.push(pos as u32);
            proof {
                let n0 = lr0.len() as int;
                assert(lr@ == lr0.push(r as u32) && ls@ == ls0.push(pos as u32));
                assert forall|i: int| 0 <= i < lr@.len() implies #[trigger] long_at(lens@, lr@, ls@, lmax as int, i) by {
                    if i < n0 {
                        assert(long_at(lens@, lr0, ls0, lmax as int, i));
                        assert(lr@[i] == lr0[i] && ls@[i] == ls0[i]);
                    } else {
                        assert(lr@[i] == r as u32 && ls@[i] == pos as u32);
                    }
                }
                assert forall|i: int| 0 <= i < lr@.len() implies #[trigger] lr@[i] < r + 1 by {
                    if i < n0 {
                        assert(lr0[i] < r);
                    }
                }
                assert forall|a: int, b: int| 0 <= a < b < lr@.len() implies #[trigger] lr@[a] < #[trigger] lr@[b] by {
                    assert(lr@[a] == lr0[a]);
                    if b < n0 {
                        assert(lr@[b] == lr0[b]);
                        assert(lr0[a] < lr0[b]);
                    } else {
                        assert(lr0[a] < r);
                    }
                }
                assert forall|t: int| 0 <= t < r + 1 && lens@[t] == lmax implies #[trigger] long_listed(lr@, lr@.len() as int, t) by {
                    if t < r {
                        assert(long_listed(lr0, n0, t));
                        let i = choose|i: int| 0 <= i < n0 && lr0[i] as int == t;
                        assert(lr@[i] == lr0[i]);
                    } else {
                        assert(lr@[n0] as int == t);
                    }
                }
            }
        }
        pos = pos + ln as u64;
        r = r + 1;
    }
    (lr, ls)
}

/// The run permutation by length of the run lengths `lens` (`rstart(lens, len)` rows in all): `(lmax, nlong, run
/// indices, start rows)`, the first `nlong` entries being the runs of the longest length `lmax`.
pub fn build_long(lens: &Vec<u8>) -> (r: (u64, u64, Vec<u32>, Vec<u32>))
    requires
        lens@.len() <= u32::MAX,
        rstart(lens@, lens@.len() as int) <= u32::MAX,
    ensures
        long_built(lens@, r.2@, r.3@, r.0 as int, r.1 as int),
{
    let lmax = longest(lens);
    let (mut lr, mut ls) = longest_class(lens, lmax);
    let nlong = lr.len();
    let ghost (lr0, ls0) = (lr@, ls@);
    let mut k: u8 = lmax;
    while k > 1
        invariant
            lens@.len() <= u32::MAX,
            rstart(lens@, lens@.len() as int) <= u32::MAX,
            lr@.len() == ls@.len(), lr@.len() >= nlong, nlong == lr0.len(), lr0.len() == ls0.len(),
            forall|i: int| 0 <= i < nlong ==> #[trigger] lr@[i] == lr0[i],
            forall|i: int| 0 <= i < nlong ==> #[trigger] ls@[i] == ls0[i],
        decreases k,
    {
        k = k - 1;
        let ghost (lr1, ls1) = (lr@, ls@);
        push_class(lens, k, &mut lr, &mut ls);
        proof {
            assert forall|i: int| 0 <= i < nlong implies #[trigger] lr@[i] == lr0[i] by {
                assert(lr@[i] == lr1[i]);
            }
            assert forall|i: int| 0 <= i < nlong implies #[trigger] ls@[i] == ls0[i] by {
                assert(ls@[i] == ls1[i]);
            }
        }
    }
    proof {
        let n0 = nlong as int;
        assert forall|i: int| 0 <= i < n0 implies #[trigger] long_at(lens@, lr@, ls@, lmax as int, i) by {
            assert(long_at(lens@, lr0, ls0, lmax as int, i));
            assert(lr@[i] == lr0[i] && ls@[i] == ls0[i]);
        }
        assert forall|a: int, b: int| 0 <= a < b < n0 implies #[trigger] lr@[a] < #[trigger] lr@[b] by {
            assert(lr@[a] == lr0[a] && lr@[b] == lr0[b]);
            assert(lr0[a] < lr0[b]);
        }
        assert forall|t: int| 0 <= t < lens@.len() && lens@[t] == lmax implies #[trigger] long_listed(lr@, n0, t) by {
            assert(long_listed(lr0, n0, t));
            let i = choose|i: int| 0 <= i < n0 && lr0[i] as int == t;
            assert(lr@[i] == lr0[i]);
        }
    }
    (lmax as u64, nlong as u64, lr, ls)
}

} // verus!
