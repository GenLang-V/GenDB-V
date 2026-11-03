//! The counting tasks of one round: per local group, the number of distinct supplier rows over every pair task's
//! segment of that group that the subquery does not exclude.
//!
//! `CountTask` (local groups `[g0, g1)`): a bitmap of supplier rows (`common::marks`, empty between groups) marks
//! the group's rows, counting first sightings; afterwards the words of all the group's rows are cleared, which
//! empties the bitmap again (every marked row is one of them).
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::WorkerTask;
use super::kernel::{PairOut, seg_has};
use super::sidx::SIdx;
use super::common::marks::*;

verus! {

/// Every segment of every pair output is well formed and holds supplier rows below `sn`.
pub open spec fn outs_ok<S: SIdx>(outs: Seq<PairOut<S>>, ng: int, sn: int) -> bool {
    forall|t: int| 0 <= t < outs.len() ==> {
        &&& (#[trigger] outs[t]).offs@.len() == ng + 1
        &&& outs[t].offs@[0] == 0
        &&& outs[t].offs@[ng] <= outs[t].out@.len()
        &&& forall|g: int| 0 <= g < ng ==> #[trigger] outs[t].offs@[g] <= outs[t].offs@[g + 1]
        &&& forall|g: int, x: int| 0 <= g < ng && #[trigger] seg_has(outs[t], g, x) ==> 0 <= x < sn
    }
}

/// Some pair output's segment of group `g` holds `x`.
pub open spec fn in_some<S: SIdx>(outs: Seq<PairOut<S>>, g: int, x: int) -> bool {
    exists|t: int| 0 <= t < outs.len() && #[trigger] seg_has(outs[t], g, x)
}

/// The distinct supplier rows of group `g` that the subquery does not exclude.
pub open spec fn dset<S: SIdx>(outs: Seq<PairOut<S>>, excl: Seq<u64>, sn: int, g: int) -> Set<int> {
    Set::range(0, sn).filter(|x: int| in_some(outs, g, x) && !bit_at(excl, x))
}

/// Group `g`'s rows seen after the pair outputs below `t` and positions below `k` of output `t`.
pub open spec fn seen_at<S: SIdx>(outs: Seq<PairOut<S>>, g: int, t: int, k: int, x: int) -> bool {
    (exists|t2: int| 0 <= t2 < t && #[trigger] seg_has(outs[t2], g, x))
        || (0 <= t < outs.len() && exists|p: int| outs[t].offs@[g] <= p < k && #[trigger] outs[t].out@[p].sx() == x)
}

pub open spec fn seen_set<S: SIdx>(outs: Seq<PairOut<S>>, excl: Seq<u64>, sn: int, g: int, t: int, k: int) -> Set<int> {
    Set::range(0, sn).filter(|x: int| seen_at(outs, g, t, k, x) && !bit_at(excl, x))
}

/// Local groups `[g0, g1)`: the number of distinct supplier rows of each.
pub struct CountTask<S: SIdx> {
    pub outs: Arc<Vec<PairOut<S>>>,
    pub excl: Arc<Vec<u64>>,
    pub sn: usize,
    pub ng: usize,
    pub g0: usize,
    pub g1: usize,
    /// One bit per supplier row, all clear.
    pub marks: Vec<u64>,
    /// Output: one count per group (`g1 - g0` entries).
    pub counts: Vec<u64>,
}

impl<S: SIdx> WorkerTask for CountTask<S> {
    type Output = Vec<u64>;

    open spec fn pre(&self) -> bool {
        &&& outs_ok(self.outs@, self.ng as int, self.sn as int)
        &&& self.sn <= 64 * self.excl@.len()
        &&& self.g0 <= self.g1 <= self.ng
        &&& self.sn <= 64 * self.marks@.len()
        &&& holds(self.marks@, Set::empty())
        &&& self.counts@.len() == self.g1 - self.g0
    }

    open spec fn post(&self, out: Vec<u64>) -> bool {
        &&& out@.len() == self.g1 - self.g0
        &&& forall|g: int| self.g0 <= g < self.g1 ==>
            #[trigger] out@[g - self.g0] as int == dset(self.outs@, self.excl@, self.sn as int, g).len()
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.g0 as u64, self.g1 as u64)
    }

    fn run(self) -> (out: Vec<u64>) {
        let CountTask { outs, excl, sn, ng, g0, g1, marks, counts } = self;
        let mut marks = marks;
        let mut counts = counts;
        let os: &Vec<PairOut<S>> = &*outs;
        let ex: &Vec<u64> = &*excl;
        let npairs = os.len();
        let mut g = g0;
        while g < g1
            invariant
                outs_ok(os@, ng as int, sn as int),
                os@ == self.outs@, ex@ == self.excl@, sn == self.sn, ng == self.ng, g0 == self.g0, g1 == self.g1,
                npairs == os@.len(),
                sn <= 64 * ex@.len(),
                g0 <= g <= g1 <= ng,
                sn <= 64 * marks@.len(),
                holds(marks@, Set::empty()),
                counts@.len() == g1 - g0,
                forall|h: int| g0 <= h < g ==> #[trigger] counts@[h - g0] as int == dset(os@, ex@, sn as int, h).len(),
            decreases g1 - g,
        {
            let ghost gi = g as int;
            // Count the group's rows.
            let mut c: u64 = 0;
            let ghost mut seen: Set<int> = Set::empty();
            proof {
                assert(seen =~= seen_set(os@, ex@, sn as int, gi, 0, 0));
            }
            let mut t: usize = 0;
            while t < npairs
                invariant
                    outs_ok(os@, ng as int, sn as int),
                    npairs == os@.len(),
                    sn <= 64 * ex@.len(),
                    g < ng,
                    gi == g,
                    t <= npairs,
                    sn <= 64 * marks@.len(),
                    holds(marks@, seen),
                    seen == seen_set(os@, ex@, sn as int, gi, t as int, if t < npairs { os@[t as int].offs@[gi] as int } else { 0 }),
                    c as int == seen.len(),
                    seen.len() <= sn,
                decreases npairs - t,
            {
                let po = &os[t];
                let a = po.offs[g];
                let b = po.offs[g + 1];
                proof {
                    assert(outs_ok(os@, ng as int, sn as int));
                    assert(po.offs@[gi] <= po.offs@[gi + 1]);
                    lemma_offs_le(os@, ng as int, sn as int, t as int, gi + 1);
                }
                let mut k = a;
                while k < b
                    invariant
                        outs_ok(os@, ng as int, sn as int),
                        npairs == os@.len(),
                        sn <= 64 * ex@.len(),
                        g < ng, gi == g,
                        t < npairs,
                        *po == os@[t as int],
                        a == po.offs@[gi], b == po.offs@[gi + 1],
                        a <= k <= b, b <= po.out@.len(),
                        sn <= 64 * marks@.len(),
                        holds(marks@, seen),
                        seen == seen_set(os@, ex@, sn as int, gi, t as int, k as int),
                        c as int == seen.len(),
                        seen.len() <= sn,
                    decreases b - k,
                {
                    let xv = po.out[k];
                    proof {
                        assert(seg_has(os@[t as int], gi, xv.sx()));
                        assert(xv.sx() < sn);
                    }
                    let x = xv.to_usize();
                    let xi = x;
                    if !get_bit(ex, xi) {
                        let fresh = mark_new(&mut marks, xi, Ghost(seen));
                        proof {
                            lemma_seen_step(os@, ex@, sn as int, gi, t as int, k as int, x as int, seen);
                            vstd::set::lemma_set_insert_len(seen, x as int);
                            lemma_seen_bound(seen.insert(x as int), sn as int);
                            seen = seen.insert(x as int);
                        }
                        if fresh {
                            c = c + 1;
                        }
                    } else {
                        proof {
                            lemma_seen_skip(os@, ex@, sn as int, gi, t as int, k as int, x as int, seen);
                        }
                    }
                    k = k + 1;
                }
                proof {
                    lemma_seen_next(os@, ex@, sn as int, gi, t as int, b as int, ng as int);
                }
                t = t + 1;
            }
            proof {
                lemma_seen_all(os@, ex@, sn as int, gi);
            }
            counts[g - g0] = c;
            // Clear the words of the group's rows: the bitmap is empty again.
            let ghost mut left: Set<int> = seen;
            let mut t: usize = 0;
            while t < npairs
                invariant
                    outs_ok(os@, ng as int, sn as int),
                    npairs == os@.len(),
                    g < ng, gi == g,
                    t <= npairs,
                    sn <= 64 * marks@.len(),
                    holds(marks@, left),
                    seen == dset(os@, ex@, sn as int, gi),
                    forall|x: int| #[trigger] left.contains(x) ==> seen.contains(x)
                        && !seen_at(os@, gi, t as int, if t < npairs { os@[t as int].offs@[gi] as int } else { 0 }, x),
                decreases npairs - t,
            {
                let po = &os[t];
                let a = po.offs[g];
                let b = po.offs[g + 1];
                proof {
                    lemma_offs_le(os@, ng as int, sn as int, t as int, gi + 1);
                    assert forall|x: int| #[trigger] left.contains(x) implies seen.contains(x)
                        && !seen_at(os@, gi, t as int, a as int, x) by {}
                }
                let mut k = a;
                while k < b
                    invariant
                        outs_ok(os@, ng as int, sn as int),
                        npairs == os@.len(),
                        g < ng, gi == g,
                        t < npairs,
                        *po == os@[t as int],
                        a == po.offs@[gi], b == po.offs@[gi + 1],
                        a <= k <= b, b <= po.out@.len(),
                        sn <= 64 * marks@.len(),
                        holds(marks@, left),
                        seen == dset(os@, ex@, sn as int, gi),
                        forall|x: int| #[trigger] left.contains(x) ==> seen.contains(x) && !seen_at(os@, gi, t as int, k as int, x),
                    decreases b - k,
                {
                    let xv = po.out[k];
                    proof {
                        assert(seg_has(os@[t as int], gi, xv.sx()));
                    }
                    let x = xv.to_usize();
                    clear_word(&mut marks, x, Ghost(left));
                    proof {
                        let l2 = left.filter(|y: int| y / 64 != (x as int) / 64);
                        assert forall|y: int| #[trigger] l2.contains(y) implies seen.contains(y)
                            && !seen_at(os@, gi, t as int, k + 1, y) by {
                            assert(left.contains(y));
                            assert(y != x as int);
                            if seen_at(os@, gi, t as int, k + 1, y) {
                                if exists|p: int| os@[t as int].offs@[gi] <= p < k + 1 && #[trigger] os@[t as int].out@[p].sx() == y {
                                    let p = choose|p: int| os@[t as int].offs@[gi] <= p < k + 1 && #[trigger] os@[t as int].out@[p].sx() == y;
                                    assert(p != k as int);
                                    assert(seen_at(os@, gi, t as int, k as int, y));
                                }
                            }
                        }
                        left = l2;
                    }
                    k = k + 1;
                }
                proof {
                    assert forall|x: int| #[trigger] left.contains(x) implies seen.contains(x)
                        && !seen_at(os@, gi, t + 1, if t + 1 < npairs { os@[t + 1].offs@[gi] as int } else { 0 }, x) by {
                        lemma_seen_whole(os@, gi, t as int, b as int, x);
                    }
                }
                t = t + 1;
            }
            proof {
                assert(left =~= Set::<int>::empty()) by {
                    assert forall|x: int| !left.contains(x) by {
                        if left.contains(x) {
                            assert(seen.contains(x));
                            assert(in_some(os@, gi, x));
                            let t2 = choose|t2: int| 0 <= t2 < os@.len() && #[trigger] seg_has(os@[t2], gi, x);
                            assert(seen_at(os@, gi, npairs as int, 0, x));
                        }
                    }
                }
            }
            g = g + 1;
        }
        counts
    }
}

/// A group's segment of output `t` ends inside the output.
proof fn lemma_offs_le<S: SIdx>(outs: Seq<PairOut<S>>, ng: int, sn: int, t: int, g: int)
    requires outs_ok(outs, ng, sn), 0 <= t < outs.len(), 0 <= g <= ng,
    ensures outs[t].offs@[g] <= outs[t].out@.len(),
    decreases ng - g,
{
    if g < ng {
        lemma_offs_le(outs, ng, sn, t, g + 1);
        assert(outs[t].offs@[g] <= outs[t].offs@[g + 1]);
    }
}

/// The seen rows are supplier rows.
proof fn lemma_seen_bound(s: Set<int>, sn: int)
    requires sn >= 0, forall|x: int| #[trigger] s.contains(x) ==> 0 <= x < sn,
    ensures s.len() <= sn,
{
    vstd::set_lib::lemma_int_range(0, sn);
    assert(s.subset_of(Set::range(0int, sn)));
    vstd::set_lib::lemma_len_subset(s, Set::range(0int, sn));
}

/// Seeing a row the subquery does not exclude adds it.
proof fn lemma_seen_step<S: SIdx>(outs: Seq<PairOut<S>>, excl: Seq<u64>, sn: int, g: int, t: int, k: int, x: int, seen: Set<int>)
    requires
        0 <= t < outs.len(),
        0 <= x < sn, sn <= 64 * excl.len(), !bit_at(excl, x),
        outs[t].out@[k].sx() == x,
        outs[t].offs@[g] <= k,
        seen == seen_set(outs, excl, sn, g, t, k),
    ensures
        seen.insert(x) == seen_set(outs, excl, sn, g, t, k + 1),
        forall|y: int| #[trigger] seen.insert(x).contains(y) ==> 0 <= y < sn,
{
    let s2 = seen_set(outs, excl, sn, g, t, k + 1);
    assert forall|y: int| #[trigger] seen.insert(x).contains(y) == s2.contains(y) by {
        if y == x {
            assert(seen_at(outs, g, t, k + 1, y));
        } else if seen_at(outs, g, t, k + 1, y) && !seen_at(outs, g, t, k, y) {
            let p = choose|p: int| outs[t].offs@[g] <= p < k + 1 && #[trigger] outs[t].out@[p].sx() == y;
            assert(p != k);
        }
    }
    assert(seen.insert(x) =~= s2);
}

/// An excluded row adds nothing.
proof fn lemma_seen_skip<S: SIdx>(outs: Seq<PairOut<S>>, excl: Seq<u64>, sn: int, g: int, t: int, k: int, x: int, seen: Set<int>)
    requires
        0 <= t < outs.len(),
        0 <= x < sn, sn <= 64 * excl.len(), bit_at(excl, x),
        outs[t].out@[k].sx() == x,
        outs[t].offs@[g] <= k,
        seen == seen_set(outs, excl, sn, g, t, k),
    ensures seen == seen_set(outs, excl, sn, g, t, k + 1),
{
    let s2 = seen_set(outs, excl, sn, g, t, k + 1);
    assert forall|y: int| #[trigger] seen.contains(y) == s2.contains(y) by {
        if y != x && seen_at(outs, g, t, k + 1, y) && !seen_at(outs, g, t, k, y) {
            let p = choose|p: int| outs[t].offs@[g] <= p < k + 1 && #[trigger] outs[t].out@[p].sx() == y;
            assert(p != k);
        }
    }
    assert(seen =~= s2);
}

/// After a whole segment of output `t`, the next output starts.
proof fn lemma_seen_whole<S: SIdx>(outs: Seq<PairOut<S>>, g: int, t: int, b: int, x: int)
    requires 0 <= t < outs.len(), b == outs[t].offs@[g + 1],
    ensures
        seen_at(outs, g, t + 1, if t + 1 < outs.len() { outs[t + 1].offs@[g] as int } else { 0 }, x)
            == seen_at(outs, g, t, b, x),
{
    let lhs = seen_at(outs, g, t + 1, if t + 1 < outs.len() { outs[t + 1].offs@[g] as int } else { 0 }, x);
    let rhs = seen_at(outs, g, t, b, x);
    if lhs {
        if exists|t2: int| 0 <= t2 < t + 1 && #[trigger] seg_has(outs[t2], g, x) {
            let t2 = choose|t2: int| 0 <= t2 < t + 1 && #[trigger] seg_has(outs[t2], g, x);
            if t2 == t {
                let p = choose|p: int| outs[t].offs@[g] <= p < outs[t].offs@[g + 1] && #[trigger] outs[t].out@[p].sx() == x;
                assert(rhs);
            }
        }
    }
    if rhs {
        if exists|p: int| outs[t].offs@[g] <= p < b && #[trigger] outs[t].out@[p].sx() == x {
            let p = choose|p: int| outs[t].offs@[g] <= p < b && #[trigger] outs[t].out@[p].sx() == x;
            assert(seg_has(outs[t], g, x));
        }
    }
}

/// After a whole segment of output `t`, the seen set is the next output's start set.
proof fn lemma_seen_next<S: SIdx>(outs: Seq<PairOut<S>>, excl: Seq<u64>, sn: int, g: int, t: int, b: int, ng: int)
    requires 0 <= t < outs.len(), b == outs[t].offs@[g + 1],
    ensures
        seen_set(outs, excl, sn, g, t, b)
            == seen_set(outs, excl, sn, g, t + 1, if t + 1 < outs.len() { outs[t + 1].offs@[g] as int } else { 0 }),
{
    let s1 = seen_set(outs, excl, sn, g, t, b);
    let s2 = seen_set(outs, excl, sn, g, t + 1, if t + 1 < outs.len() { outs[t + 1].offs@[g] as int } else { 0 });
    assert forall|x: int| #[trigger] s1.contains(x) == s2.contains(x) by {
        lemma_seen_whole(outs, g, t, b, x);
    }
    assert(s1 =~= s2);
}

/// After every output, the seen set is the group's distinct set.
proof fn lemma_seen_all<S: SIdx>(outs: Seq<PairOut<S>>, excl: Seq<u64>, sn: int, g: int)
    ensures seen_set(outs, excl, sn, g, outs.len() as int, 0) == dset(outs, excl, sn, g),
{
    let s1 = seen_set(outs, excl, sn, g, outs.len() as int, 0);
    let s2 = dset(outs, excl, sn, g);
    assert forall|x: int| #[trigger] s1.contains(x) == s2.contains(x) by {
        if seen_at(outs, g, outs.len() as int, 0, x) {
            let t2 = choose|t2: int| 0 <= t2 < outs.len() && #[trigger] seg_has(outs[t2], g, x);
            assert(in_some(outs, g, x));
        }
        if in_some(outs, g, x) {
            let t2 = choose|t2: int| 0 <= t2 < outs.len() && #[trigger] seg_has(outs[t2], g, x);
            assert(seen_at(outs, g, outs.len() as int, 0, x));
        }
    }
    assert(s1 =~= s2);
}

} // verus!
