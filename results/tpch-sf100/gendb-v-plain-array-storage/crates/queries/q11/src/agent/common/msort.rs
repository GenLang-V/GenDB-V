//! Merge sort of (value, key) pairs held in two parallel vectors (`Vec<i128>` values, `Vec<i64>` keys), by value,
//! descending (ties in any order), allocation-free and `no_unwind` (usable in worker tasks with buffers allocated by
//! the calling thread), plus the merge of two descending ranges into an output range.
//!
//! View: `pairs(v, k, lo, hi)` is the sequence of `(v[i], k[i])` for `i` in `[lo, hi)`; `desc` is "values do not
//! increase". `merge_ranges` writes the merge of two descending ranges into `[olo, olo + n)` of the output and
//! keeps the multiset of pairs; `sort_range` sorts `[lo, hi)` in place (scratch vectors of the same length), keeps
//! the multiset and leaves everything outside the range unchanged.
use vstd::prelude::*;
use vstd::multiset::Multiset;

verus! {

/// The pairs `(v[i], k[i])` of `[lo, hi)`.
pub open spec fn pairs(v: Seq<i128>, k: Seq<i64>, lo: int, hi: int) -> Seq<(int, int)> {
    Seq::new((hi - lo) as nat, |i: int| (v[lo + i] as int, k[lo + i] as int))
}

/// Values do not increase.
pub open spec fn desc(s: Seq<(int, int)>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> (#[trigger] s[i]).0 >= (#[trigger] s[j]).0
}

/// Every pair of `s` has a value at least `x`.
pub open spec fn all_ge(s: Seq<(int, int)>, x: int) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i]).0 >= x
}

/// Two adjacent ranges.
pub proof fn lemma_pairs_split(v: Seq<i128>, k: Seq<i64>, lo: int, mid: int, hi: int)
    requires 0 <= lo <= mid <= hi <= v.len(), hi <= k.len(),
    ensures pairs(v, k, lo, hi) == pairs(v, k, lo, mid) + pairs(v, k, mid, hi),
{
    assert(pairs(v, k, lo, hi) =~= pairs(v, k, lo, mid) + pairs(v, k, mid, hi));
}

/// One more pair at the end of a range.
pub proof fn lemma_pairs_push(v: Seq<i128>, k: Seq<i64>, lo: int, hi: int)
    requires 0 <= lo <= hi < v.len(), hi < k.len(),
    ensures pairs(v, k, lo, hi + 1) == pairs(v, k, lo, hi).push((v[hi] as int, k[hi] as int)),
{
    assert(pairs(v, k, lo, hi + 1) =~= pairs(v, k, lo, hi).push((v[hi] as int, k[hi] as int)));
}

/// A range is unchanged when its elements are.
pub proof fn lemma_pairs_frame(v1: Seq<i128>, k1: Seq<i64>, v2: Seq<i128>, k2: Seq<i64>, lo: int, hi: int)
    requires
        0 <= lo <= hi, hi <= v1.len(), hi <= v2.len(), hi <= k1.len(), hi <= k2.len(),
        forall|i: int| lo <= i < hi ==> v1[i] == v2[i] && k1[i] == k2[i],
    ensures pairs(v1, k1, lo, hi) == pairs(v2, k2, lo, hi),
{
    assert(pairs(v1, k1, lo, hi) =~= pairs(v2, k2, lo, hi));
}

/// Merge the descending ranges `x[xlo..xhi)` and `y[ylo..yhi)` into `o[olo..olo + n)` (`n` the total length).
pub fn merge_ranges(xv: &Vec<i128>, xk: &Vec<i64>, xlo: usize, xhi: usize, yv: &Vec<i128>, yk: &Vec<i64>, ylo: usize,
    yhi: usize, ov: &mut Vec<i128>, ok: &mut Vec<i64>, olo: usize)
    requires
        xlo <= xhi <= xv@.len(), xhi <= xk@.len(),
        ylo <= yhi <= yv@.len(), yhi <= yk@.len(),
        olo + (xhi - xlo) + (yhi - ylo) <= old(ov)@.len(),
        old(ov)@.len() == old(ok)@.len(),
        desc(pairs(xv@, xk@, xlo as int, xhi as int)),
        desc(pairs(yv@, yk@, ylo as int, yhi as int)),
    ensures ({
        let ohi = olo + (xhi - xlo) + (yhi - ylo);
        &&& final(ov)@.len() == old(ov)@.len() && final(ok)@.len() == old(ok)@.len()
        &&& desc(pairs(final(ov)@, final(ok)@, olo as int, ohi))
        &&& pairs(final(ov)@, final(ok)@, olo as int, ohi).to_multiset()
            == pairs(xv@, xk@, xlo as int, xhi as int).to_multiset().add(pairs(yv@, yk@, ylo as int, yhi as int).to_multiset())
        &&& forall|i: int| 0 <= i < final(ov)@.len() && !(olo <= i < ohi) ==> final(ov)@[i] == old(ov)@[i] && final(ok)@[i] == old(ok)@[i]
    }),
    no_unwind
{
    broadcast use vstd::multiset::group_multiset_axioms, vstd::seq_lib::group_to_multiset_ensures;
    let ghost ov0 = ov@;
    let ghost ok0 = ok@;
    let ghost xs = pairs(xv@, xk@, xlo as int, xhi as int);
    let ghost ys = pairs(yv@, yk@, ylo as int, yhi as int);
    let olen = ov.len();
    let n = (xhi - xlo) + (yhi - ylo);
    let mut p = xlo;
    let mut q = ylo;
    let mut o = olo;
    proof {
        assert(pairs(ov@, ok@, olo as int, olo as int) =~= Seq::<(int, int)>::empty());
        assert(pairs(xv@, xk@, xlo as int, xlo as int) =~= Seq::<(int, int)>::empty());
        assert(pairs(yv@, yk@, ylo as int, ylo as int) =~= Seq::<(int, int)>::empty());
        assert(Seq::<(int, int)>::empty().to_multiset() =~= Multiset::<(int, int)>::empty());
        assert(Multiset::<(int, int)>::empty().add(Multiset::<(int, int)>::empty()) =~= Multiset::<(int, int)>::empty());
    }
    while o < olo + n
        invariant
            xlo <= p <= xhi, ylo <= q <= yhi,
            xhi <= xv@.len(), xhi <= xk@.len(), yhi <= yv@.len(), yhi <= yk@.len(),
            n == (xhi - xlo) + (yhi - ylo),
            olo + n <= ov@.len(), olen == ov@.len(),
            ov@.len() == ov0.len(), ok@.len() == ok0.len(), ov0.len() == ok0.len(),
            o == olo + (p - xlo) + (q - ylo),
            xs == pairs(xv@, xk@, xlo as int, xhi as int),
            ys == pairs(yv@, yk@, ylo as int, yhi as int),
            desc(xs), desc(ys),
            desc(pairs(ov@, ok@, olo as int, o as int)),
            pairs(ov@, ok@, olo as int, o as int).to_multiset()
                == pairs(xv@, xk@, xlo as int, p as int).to_multiset().add(pairs(yv@, yk@, ylo as int, q as int).to_multiset()),
            p < xhi ==> all_ge(pairs(ov@, ok@, olo as int, o as int), xv@[p as int] as int),
            q < yhi ==> all_ge(pairs(ov@, ok@, olo as int, o as int), yv@[q as int] as int),
            forall|i: int| 0 <= i < ov@.len() && !(olo <= i < o) ==> ov@[i] == ov0[i] && ok@[i] == ok0[i],
        decreases olo + n - o,
    {
        let ghost before = pairs(ov@, ok@, olo as int, o as int);
        let take_x = p < xhi && (q >= yhi || xv[p] >= yv[q]);
        let (val, key) = if take_x { (xv[p], xk[p]) } else { (yv[q], yk[q]) };
        ov[o] = val;
        ok[o] = key;
        proof {
            assert(pairs(ov@, ok@, olo as int, o as int) =~= before);
            lemma_pairs_push(ov@, ok@, olo as int, o as int);
            let after = pairs(ov@, ok@, olo as int, o + 1);
            assert(after == before.push((val as int, key as int)));
            let e = (val as int, key as int);
            let mx = pairs(xv@, xk@, xlo as int, p as int).to_multiset();
            let my = pairs(yv@, yk@, ylo as int, q as int).to_multiset();
            vstd::seq_lib::to_multiset_build(before, e);
            assert(after.to_multiset() =~= before.to_multiset().insert(e));
            if take_x {
                lemma_pairs_push(xv@, xk@, xlo as int, p as int);
                vstd::seq_lib::to_multiset_build(pairs(xv@, xk@, xlo as int, p as int), e);
                assert(pairs(xv@, xk@, xlo as int, p + 1).to_multiset() =~= mx.insert(e));
                assert(after.to_multiset() =~= mx.insert(e).add(my));
            } else {
                lemma_pairs_push(yv@, yk@, ylo as int, q as int);
                vstd::seq_lib::to_multiset_build(pairs(yv@, yk@, ylo as int, q as int), e);
                assert(pairs(yv@, yk@, ylo as int, q + 1).to_multiset() =~= my.insert(e));
                assert(after.to_multiset() =~= mx.add(my.insert(e)));
            }
            // the written value bounds what remains of both ranges
            if take_x {
                assert(xs[p - xlo] == (xv@[p as int] as int, xk@[p as int] as int));
                if p + 1 < xhi {
                    assert(xs[p - xlo].0 >= xs[p + 1 - xlo].0);
                }
            } else {
                lemma_pairs_push(yv@, yk@, ylo as int, q as int);
                assert(ys[q - ylo] == (yv@[q as int] as int, yk@[q as int] as int));
                if q + 1 < yhi {
                    assert(ys[q - ylo].0 >= ys[q + 1 - ylo].0);
                }
            }
            assert forall|i: int, j: int| 0 <= i < j < after.len() implies (#[trigger] after[i]).0 >= (#[trigger] after[j]).0 by {
                if j < before.len() {
                    assert(after[i] == before[i] && after[j] == before[j]);
                } else {
                    assert(after[i] == before[i]);
                }
            }
        }
        if take_x { p = p + 1; } else { q = q + 1; }
        o = o + 1;
        proof {
            let after = pairs(ov@, ok@, olo as int, o as int);
            if p < xhi {
                assert forall|i: int| 0 <= i < after.len() implies (#[trigger] after[i]).0 >= xv@[p as int] as int by {
                    if take_x {
                        assert(xs[p - 1 - xlo].0 >= xs[p - xlo].0);
                        assert(xs[p - xlo] == (xv@[p as int] as int, xk@[p as int] as int));
                    }
                    if i < after.len() - 1 {
                        assert(after[i] == before[i]);
                    }
                }
            }
            if q < yhi {
                assert forall|i: int| 0 <= i < after.len() implies (#[trigger] after[i]).0 >= yv@[q as int] as int by {
                    if !take_x {
                        assert(ys[q - 1 - ylo].0 >= ys[q - ylo].0);
                        assert(ys[q - ylo] == (yv@[q as int] as int, yk@[q as int] as int));
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
    }
}

/// Copy `[lo, hi)` of `s` into `d`.
pub fn copy_range(sv: &Vec<i128>, sk: &Vec<i64>, dv: &mut Vec<i128>, dk: &mut Vec<i64>, lo: usize, hi: usize)
    requires
        lo <= hi <= sv@.len(), sv@.len() == sk@.len(), old(dv)@.len() == sv@.len(), old(dk)@.len() == sv@.len(),
    ensures
        final(dv)@.len() == old(dv)@.len(), final(dk)@.len() == old(dk)@.len(),
        forall|i: int| lo <= i < hi ==> final(dv)@[i] == sv@[i] && final(dk)@[i] == sk@[i],
        forall|i: int| 0 <= i < final(dv)@.len() && !(lo <= i < hi) ==> final(dv)@[i] == old(dv)@[i] && final(dk)@[i] == old(dk)@[i],
    no_unwind
{
    let ghost dv0 = dv@;
    let ghost dk0 = dk@;
    let mut i = lo;
    while i < hi
        invariant
            lo <= i <= hi <= sv@.len(), sv@.len() == sk@.len(), dv@.len() == sv@.len(), dk@.len() == sv@.len(),
            dv0.len() == dv@.len(), dk0.len() == dk@.len(),
            forall|j: int| lo <= j < i ==> dv@[j] == sv@[j] && dk@[j] == sk@[j],
            forall|j: int| 0 <= j < dv@.len() && !(lo <= j < i) ==> dv@[j] == dv0[j] && dk@[j] == dk0[j],
        decreases hi - i,
    {
        dv[i] = sv[i];
        dk[i] = sk[i];
        i = i + 1;
    }
}

/// Sort `[lo, hi)` of `a` by value, descending, using `b` as scratch (same length).
pub fn sort_range(av: &mut Vec<i128>, ak: &mut Vec<i64>, bv: &mut Vec<i128>, bk: &mut Vec<i64>, lo: usize, hi: usize)
    requires
        lo <= hi <= old(av)@.len(),
        old(av)@.len() == old(ak)@.len(), old(bv)@.len() == old(av)@.len(), old(bk)@.len() == old(av)@.len(),
    ensures
        final(av)@.len() == old(av)@.len(), final(ak)@.len() == old(ak)@.len(),
        final(bv)@.len() == old(bv)@.len(), final(bk)@.len() == old(bk)@.len(),
        desc(pairs(final(av)@, final(ak)@, lo as int, hi as int)),
        pairs(final(av)@, final(ak)@, lo as int, hi as int).to_multiset() == pairs(old(av)@, old(ak)@, lo as int, hi as int).to_multiset(),
        forall|i: int| 0 <= i < final(av)@.len() && !(lo <= i < hi) ==> final(av)@[i] == old(av)@[i] && final(ak)@[i] == old(ak)@[i],
    decreases hi - lo,
    no_unwind
{
    if hi - lo <= 1 {
        proof {
            let s = pairs(av@, ak@, lo as int, hi as int);
            assert(desc(s));
        }
        return;
    }
    let ghost a0v = av@;
    let ghost a0k = ak@;
    let mid = lo + (hi - lo) / 2;
    sort_range(av, ak, bv, bk, lo, mid);
    let ghost a1v = av@;
    let ghost a1k = ak@;
    sort_range(av, ak, bv, bk, mid, hi);
    let ghost a2v = av@;
    let ghost a2k = ak@;
    proof {
        lemma_pairs_frame(a1v, a1k, a2v, a2k, lo as int, mid as int);
        lemma_pairs_frame(a0v, a0k, a1v, a1k, mid as int, hi as int);
    }
    merge_ranges(av, ak, lo, mid, av, ak, mid, hi, bv, bk, lo);
    let ghost bv1 = bv@;
    let ghost bk1 = bk@;
    copy_range(bv, bk, av, ak, lo, hi);
    proof {
        lemma_pairs_frame(av@, ak@, bv1, bk1, lo as int, hi as int);
        lemma_pairs_split(a0v, a0k, lo as int, mid as int, hi as int);
        vstd::seq_lib::lemma_multiset_commutative(pairs(a0v, a0k, lo as int, mid as int), pairs(a0v, a0k, mid as int, hi as int));
    }
}

} // verus!
