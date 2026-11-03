//! Merge sort of `u64` values, ascending, allocation-free with a scratch vector of the same length (adapted from an
//! admitted query's merge sort of value/key pairs): `sort_range` sorts `[lo, hi)` in place, keeps the multiset of
//! values and leaves everything outside the range unchanged; `merge_ranges` merges two ascending ranges into an
//! output range.
use vstd::prelude::*;
use vstd::multiset::Multiset;

verus! {

/// Values do not decrease.
pub open spec fn asc(s: Seq<u64>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

/// Every value of `s` is at most `x`.
pub open spec fn all_le(s: Seq<u64>, x: u64) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i]) <= x
}

/// Merge the ascending ranges `x[xlo..xhi)` and `y[ylo..yhi)` into `o[olo..olo + n)` (`n` the total length).
pub fn merge_ranges(x: &Vec<u64>, xlo: usize, xhi: usize, y: &Vec<u64>, ylo: usize, yhi: usize, o: &mut Vec<u64>, olo: usize)
    requires
        xlo <= xhi <= x@.len(),
        ylo <= yhi <= y@.len(),
        olo + (xhi - xlo) + (yhi - ylo) <= old(o)@.len(),
        asc(x@.subrange(xlo as int, xhi as int)),
        asc(y@.subrange(ylo as int, yhi as int)),
    ensures ({
        let ohi = olo + (xhi - xlo) + (yhi - ylo);
        &&& final(o)@.len() == old(o)@.len()
        &&& asc(final(o)@.subrange(olo as int, ohi))
        &&& final(o)@.subrange(olo as int, ohi).to_multiset()
            == x@.subrange(xlo as int, xhi as int).to_multiset().add(y@.subrange(ylo as int, yhi as int).to_multiset())
        &&& forall|i: int| 0 <= i < final(o)@.len() && !(olo <= i < ohi) ==> final(o)@[i] == old(o)@[i]
    }),
    no_unwind
{
    broadcast use vstd::multiset::group_multiset_axioms, vstd::seq_lib::group_to_multiset_ensures;
    let ghost o0 = o@;
    let ghost xs = x@.subrange(xlo as int, xhi as int);
    let ghost ys = y@.subrange(ylo as int, yhi as int);
    let olen = o.len();
    let n = (xhi - xlo) + (yhi - ylo);
    let mut p = xlo;
    let mut q = ylo;
    let mut k = olo;
    proof {
        assert(o@.subrange(olo as int, olo as int) =~= Seq::<u64>::empty());
        assert(x@.subrange(xlo as int, xlo as int) =~= Seq::<u64>::empty());
        assert(y@.subrange(ylo as int, ylo as int) =~= Seq::<u64>::empty());
        assert(Seq::<u64>::empty().to_multiset() =~= Multiset::<u64>::empty());
        assert(Multiset::<u64>::empty().add(Multiset::<u64>::empty()) =~= Multiset::<u64>::empty());
    }
    while k < olo + n
        invariant
            xlo <= p <= xhi, ylo <= q <= yhi, xhi <= x@.len(), yhi <= y@.len(),
            n == (xhi - xlo) + (yhi - ylo), olo + n <= o@.len(), o@.len() == o0.len(), olen == o@.len(),
            k == olo + (p - xlo) + (q - ylo),
            xs == x@.subrange(xlo as int, xhi as int), ys == y@.subrange(ylo as int, yhi as int),
            asc(xs), asc(ys),
            asc(o@.subrange(olo as int, k as int)),
            o@.subrange(olo as int, k as int).to_multiset()
                == x@.subrange(xlo as int, p as int).to_multiset().add(y@.subrange(ylo as int, q as int).to_multiset()),
            p < xhi ==> all_le(o@.subrange(olo as int, k as int), x@[p as int]),
            q < yhi ==> all_le(o@.subrange(olo as int, k as int), y@[q as int]),
            forall|i: int| 0 <= i < o@.len() && !(olo <= i < k) ==> o@[i] == o0[i],
        decreases olo + n - k,
    {
        let ghost before = o@.subrange(olo as int, k as int);
        let take_x = p < xhi && (q >= yhi || x[p] <= y[q]);
        let v = if take_x { x[p] } else { y[q] };
        o[k] = v;
        proof {
            assert(o@.subrange(olo as int, k as int) =~= before);
            let after = o@.subrange(olo as int, k + 1);
            assert(after =~= before.push(v));
            let mx = x@.subrange(xlo as int, p as int).to_multiset();
            let my = y@.subrange(ylo as int, q as int).to_multiset();
            vstd::seq_lib::to_multiset_build(before, v);
            assert(after.to_multiset() =~= before.to_multiset().insert(v));
            if take_x {
                assert(x@.subrange(xlo as int, p + 1) =~= x@.subrange(xlo as int, p as int).push(v));
                vstd::seq_lib::to_multiset_build(x@.subrange(xlo as int, p as int), v);
                assert(after.to_multiset() =~= mx.insert(v).add(my));
                assert(xs[p - xlo] == x@[p as int]);
                if p + 1 < xhi { assert(xs[p - xlo] <= xs[p + 1 - xlo]); }
            } else {
                assert(y@.subrange(ylo as int, q + 1) =~= y@.subrange(ylo as int, q as int).push(v));
                vstd::seq_lib::to_multiset_build(y@.subrange(ylo as int, q as int), v);
                assert(after.to_multiset() =~= mx.add(my.insert(v)));
                assert(ys[q - ylo] == y@[q as int]);
                if q + 1 < yhi { assert(ys[q - ylo] <= ys[q + 1 - ylo]); }
            }
            assert forall|i: int, j: int| 0 <= i < j < after.len() implies after[i] <= after[j] by {
                if j < before.len() {
                    assert(after[i] == before[i] && after[j] == before[j]);
                } else {
                    assert(after[i] == before[i]);
                }
            }
        }
        if take_x { p = p + 1; } else { q = q + 1; }
        k = k + 1;
        proof {
            let after = o@.subrange(olo as int, k as int);
            if p < xhi {
                assert forall|i: int| 0 <= i < after.len() implies (#[trigger] after[i]) <= x@[p as int] by {
                    if take_x {
                        assert(xs[p - 1 - xlo] <= xs[p - xlo]);
                    }
                    if i < after.len() - 1 {
                        assert(after[i] == before[i]);
                    }
                }
            }
            if q < yhi {
                assert forall|i: int| 0 <= i < after.len() implies (#[trigger] after[i]) <= y@[q as int] by {
                    if !take_x {
                        assert(ys[q - 1 - ylo] <= ys[q - ylo]);
                    }
                    if i < after.len() - 1 {
                        assert(after[i] == before[i]);
                    }
                }
            }
        }
    }
    proof {
        assert(p == xhi && q == yhi);
        assert(x@.subrange(xlo as int, p as int) =~= xs);
        assert(y@.subrange(ylo as int, q as int) =~= ys);
    }
}

/// Copy `[lo, hi)` of `s` into `d` (same length).
pub fn copy_range(s: &Vec<u64>, d: &mut Vec<u64>, lo: usize, hi: usize)
    requires lo <= hi <= s@.len(), old(d)@.len() == s@.len(),
    ensures
        final(d)@.len() == old(d)@.len(),
        forall|i: int| lo <= i < hi ==> final(d)@[i] == s@[i],
        forall|i: int| 0 <= i < final(d)@.len() && !(lo <= i < hi) ==> final(d)@[i] == old(d)@[i],
    no_unwind
{
    let ghost d0 = d@;
    let mut i = lo;
    while i < hi
        invariant
            lo <= i <= hi <= s@.len(), d@.len() == s@.len(), d0.len() == d@.len(),
            forall|j: int| lo <= j < i ==> d@[j] == s@[j],
            forall|j: int| 0 <= j < d@.len() && !(lo <= j < i) ==> d@[j] == d0[j],
        decreases hi - i,
    {
        d[i] = s[i];
        i = i + 1;
    }
}

/// Sort `[lo, hi)` of `a` ascending, using `b` as scratch (same length).
pub fn sort_range(a: &mut Vec<u64>, b: &mut Vec<u64>, lo: usize, hi: usize)
    requires lo <= hi <= old(a)@.len(), old(b)@.len() == old(a)@.len(),
    ensures
        final(a)@.len() == old(a)@.len(), final(b)@.len() == old(b)@.len(),
        asc(final(a)@.subrange(lo as int, hi as int)),
        final(a)@.subrange(lo as int, hi as int).to_multiset() == old(a)@.subrange(lo as int, hi as int).to_multiset(),
        forall|i: int| 0 <= i < final(a)@.len() && !(lo <= i < hi) ==> final(a)@[i] == old(a)@[i],
    decreases hi - lo,
    no_unwind
{
    if hi - lo <= 1 {
        return;
    }
    let ghost a0 = a@;
    let mid = lo + (hi - lo) / 2;
    sort_range(a, b, lo, mid);
    let ghost a1 = a@;
    sort_range(a, b, mid, hi);
    let ghost a2 = a@;
    proof {
        assert(a2.subrange(lo as int, mid as int) =~= a1.subrange(lo as int, mid as int));
        assert(a1.subrange(mid as int, hi as int) =~= a0.subrange(mid as int, hi as int));
    }
    merge_ranges(a, lo, mid, a, mid, hi, b, lo);
    let ghost b1 = b@;
    copy_range(b, a, lo, hi);
    proof {
        assert(a@.subrange(lo as int, hi as int) =~= b1.subrange(lo as int, hi as int));
        assert(a0.subrange(lo as int, hi as int) =~= a0.subrange(lo as int, mid as int) + a0.subrange(mid as int, hi as int));
        vstd::seq_lib::lemma_multiset_commutative(a0.subrange(lo as int, mid as int), a0.subrange(mid as int, hi as int));
    }
}

/// Sort `v` ascending (allocates the scratch vector on the calling thread).
pub fn sort_u64(v: Vec<u64>) -> (r: Vec<u64>)
    ensures asc(r@), r@.to_multiset() == v@.to_multiset(), r@.len() == v@.len(),
{
    let n = v.len();
    let mut a = v;
    let mut b = vec![0u64; n];
    sort_range(&mut a, &mut b, 0, n);
    proof {
        assert(a@.subrange(0, n as int) =~= a@);
        assert(v@.subrange(0, n as int) =~= v@);
    }
    a
}

} // verus!
