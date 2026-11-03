//! Merge sort over any element type with a total preorder (`SortOrder`), proved to return a sorted permutation
//! (same multiset) of its input, without allocation (`no_unwind`, usable in worker bodies). Adapted from the admitted
//! builder module `builder/common/sort.rs` (storage `pre`): the generic trait, merge and top-down sort are unchanged;
//! the orders of this query (implemented here, since the source rules let a trait be implemented only in the file
//! that defines it) are at the end.
use vstd::prelude::*;
use crate::gendb_entry::work::put;
use crate::agent::join::Partial;
use crate::agent::filings::Filing;

verus! {

broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms};

/// A total preorder on elements `E` that satisfy `ok`, decided by `le_exec` (usable in worker bodies).
pub trait SortOrder<E> {
    /// The order's own well-formedness (e.g. a text column with well-formed offsets).
    spec fn wf(&self) -> bool;

    /// Elements the order can compare (e.g. row ids inside the column).
    spec fn ok(&self, a: E) -> bool;

    /// `a` sorts before or together with `b`.
    spec fn le(&self, a: E, b: E) -> bool;

    proof fn lemma_total(&self, a: E, b: E)
        requires self.wf(), self.ok(a), self.ok(b),
        ensures self.le(a, b) || self.le(b, a);

    proof fn lemma_trans(&self, a: E, b: E, c: E)
        requires self.wf(), self.ok(a), self.ok(b), self.ok(c), self.le(a, b), self.le(b, c),
        ensures self.le(a, c);

    fn le_exec(&self, a: E, b: E) -> (r: bool)
        requires self.wf(), self.ok(a), self.ok(b),
        ensures r == self.le(a, b),
        no_unwind;
}

/// Every element of `s` is comparable.
pub open spec fn all_ok<E, O: SortOrder<E>>(o: O, s: Seq<E>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> o.ok(#[trigger] s[i])
}

/// `s` is sorted by `o`: every earlier element sorts before or together with every later one.
pub open spec fn sorted_by<E, O: SortOrder<E>>(o: O, s: Seq<E>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> o.le(#[trigger] s[i], #[trigger] s[j])
}


// ----------------------------------------------------------------------------------------------- merge of two runs

/// Pushing `x` after a sorted `s` whose last element sorts before `x` keeps it sorted.
proof fn lemma_sorted_push<E, O: SortOrder<E>>(o: O, s: Seq<E>, x: E)
    requires
        o.wf(), sorted_by(o, s), all_ok(o, s), o.ok(x),
        s.len() > 0 ==> o.le(s.last(), x),
    ensures
        sorted_by(o, s.push(x)),
{
    let t = s.push(x);
    assert forall|i: int, j: int| 0 <= i < j < t.len() implies o.le(#[trigger] t[i], #[trigger] t[j]) by {
        if j == s.len() {
            if i < s.len() - 1 {
                o.lemma_trans(s[i], s.last(), x);
            }
        }
    }
}

/// Merge the sorted ranges `a[alo..ahi]` and `b[blo..bhi]` into `dst[dlo..dlo + len]` (sorted, the same multiset);
/// the rest of `dst` is unchanged. `no_unwind`.
pub fn merge_into<E: Copy, O: SortOrder<E>>(
    o: &O, a: &Vec<E>, alo: usize, ahi: usize, b: &Vec<E>, blo: usize, bhi: usize, dst: &mut Vec<E>, dlo: usize,
)
    requires
        o.wf(),
        alo <= ahi <= a@.len(),
        blo <= bhi <= b@.len(),
        dlo + (ahi - alo) + (bhi - blo) <= old(dst)@.len(),
        sorted_by(*o, a@.subrange(alo as int, ahi as int)),
        sorted_by(*o, b@.subrange(blo as int, bhi as int)),
        all_ok(*o, a@.subrange(alo as int, ahi as int)),
        all_ok(*o, b@.subrange(blo as int, bhi as int)),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        sorted_by(*o, final(dst)@.subrange(dlo as int, dlo + (ahi - alo) + (bhi - blo))),
        all_ok(*o, final(dst)@.subrange(dlo as int, dlo + (ahi - alo) + (bhi - blo))),
        final(dst)@.subrange(dlo as int, dlo + (ahi - alo) + (bhi - blo)).to_multiset()
            == a@.subrange(alo as int, ahi as int).to_multiset().add(b@.subrange(blo as int, bhi as int).to_multiset()),
        forall|k: int| 0 <= k < old(dst)@.len() && !(dlo <= k < dlo + (ahi - alo) + (bhi - blo))
            ==> final(dst)@[k] == old(dst)@[k],
    no_unwind
{
    let ghost sa = a@.subrange(alo as int, ahi as int);
    let ghost sb = b@.subrange(blo as int, bhi as int);
    let ghost d0 = dst@;
    let dn = dst.len();
    let mut i = alo;
    let mut j = blo;
    let mut k = dlo;
    assert(a@.subrange(alo as int, alo as int) =~= Seq::<E>::empty());
    assert(b@.subrange(blo as int, blo as int) =~= Seq::<E>::empty());
    assert(dst@.subrange(dlo as int, dlo as int) =~= Seq::<E>::empty());
    while i < ahi || j < bhi
        invariant
            o.wf(),
            alo <= i <= ahi <= a@.len(),
            blo <= j <= bhi <= b@.len(),
            sa == a@.subrange(alo as int, ahi as int),
            sb == b@.subrange(blo as int, bhi as int),
            sorted_by(*o, sa), sorted_by(*o, sb), all_ok(*o, sa), all_ok(*o, sb),
            k == dlo + (i - alo) + (j - blo),
            dlo + (ahi - alo) + (bhi - blo) <= d0.len(),
            dn == d0.len(),
            dst@.len() == d0.len(),
            sorted_by(*o, dst@.subrange(dlo as int, k as int)),
            all_ok(*o, dst@.subrange(dlo as int, k as int)),
            dst@.subrange(dlo as int, k as int).to_multiset()
                == a@.subrange(alo as int, i as int).to_multiset().add(b@.subrange(blo as int, j as int).to_multiset()),
            k > dlo && i < ahi ==> o.le(dst@[k - 1], a@[i as int]),
            k > dlo && j < bhi ==> o.le(dst@[k - 1], b@[j as int]),
            forall|q: int| 0 <= q < d0.len() && !(dlo <= q < k) ==> dst@[q] == d0[q],
        decreases (ahi - i) + (bhi - j),
    {
        let ghost before = dst@.subrange(dlo as int, k as int);
        let take_a = if i == ahi {
            false
        } else if j == bhi {
            true
        } else {
            proof {
                assert(sa[i - alo] == a@[i as int]);
                assert(sb[j - blo] == b@[j as int]);
            }
            o.le_exec(a[i], b[j])
        };
        let x = if take_a { a[i] } else { b[j] };
        proof {
            if take_a {
                assert(sa[i - alo] == a@[i as int]);
                assert(o.ok(x));
                assert(a@.subrange(alo as int, i + 1) =~= a@.subrange(alo as int, i as int).push(x));
            } else {
                assert(sb[j - blo] == b@[j as int]);
                assert(o.ok(x));
                assert(b@.subrange(blo as int, j + 1) =~= b@.subrange(blo as int, j as int).push(x));
            }
            if k > dlo {
                assert(before.last() == dst@[k - 1]);
            }
            lemma_sorted_push(*o, before, x);
        }
        put(dst, k, x);
        proof {
            assert(dst@.subrange(dlo as int, k + 1) =~= before.push(x));
            if take_a {
                if i + 1 < ahi {
                    assert(sa[i - alo] == a@[i as int] && sa[i + 1 - alo] == a@[i + 1]);
                    assert(o.le(sa[i - alo], sa[i + 1 - alo]));
                }
                if j < bhi && i < ahi && j != bhi {
                    // x was chosen because it sorts before b[j]
                }
            } else {
                if j + 1 < bhi {
                    assert(sb[j - blo] == b@[j as int] && sb[j + 1 - blo] == b@[j + 1]);
                    assert(o.le(sb[j - blo], sb[j + 1 - blo]));
                }
                if i < ahi {
                    assert(sa[i - alo] == a@[i as int]);
                    assert(sb[j - blo] == b@[j as int]);
                    o.lemma_total(a@[i as int], b@[j as int]);
                }
            }
            let t = dst@.subrange(dlo as int, k + 1);
            assert forall|q: int| 0 <= q < t.len() implies o.ok(#[trigger] t[q]) by {
                if q < k - dlo {
                    assert(t[q] == before[q]);
                }
            }
        }
        if take_a {
            i = i + 1;
        } else {
            j = j + 1;
        }
        k = k + 1;
    }
    proof {
        assert(a@.subrange(alo as int, i as int) =~= sa);
        assert(b@.subrange(blo as int, j as int) =~= sb);
    }
}

// --------------------------------------------------------------------------------------- sorting one range of a vector

/// Copy `src[lo..hi]` over `dst[lo..hi]`; the rest of `dst` is unchanged. `no_unwind`.
fn copy_range<E: Copy>(src: &Vec<E>, dst: &mut Vec<E>, lo: usize, hi: usize)
    requires lo <= hi <= src@.len(), old(dst)@.len() == src@.len(),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        final(dst)@.subrange(lo as int, hi as int) == src@.subrange(lo as int, hi as int),
        forall|q: int| 0 <= q < old(dst)@.len() && !(lo <= q < hi) ==> final(dst)@[q] == old(dst)@[q],
    no_unwind
{
    let ghost d0 = dst@;
    let mut p = lo;
    while p < hi
        invariant
            lo <= p <= hi <= src@.len(),
            dst@.len() == src@.len(),
            forall|q: int| lo <= q < p ==> dst@[q] == src@[q],
            forall|q: int| 0 <= q < d0.len() && !(lo <= q < p) ==> dst@[q] == d0[q],
        decreases hi - p,
    {
        let x = src[p];
        put(dst, p, x);
        p = p + 1;
    }
    assert(dst@.subrange(lo as int, hi as int) =~= src@.subrange(lo as int, hi as int));
}

/// Two sorted halves `v2[lo..mid)` and `v2[mid..hi)` (permutations of the halves of `v0`) whose boundary elements
/// are in order make `v2[lo..hi)` a sorted permutation of `v0[lo..hi)`.
proof fn lemma_halves_in_order<E, O: SortOrder<E>>(o: O, v0: Seq<E>, v2: Seq<E>, lo: int, mid: int, hi: int)
    requires
        o.wf(), 0 <= lo < mid < hi <= v0.len(), v2.len() == v0.len(),
        sorted_by(o, v2.subrange(lo, mid)), all_ok(o, v2.subrange(lo, mid)),
        sorted_by(o, v2.subrange(mid, hi)), all_ok(o, v2.subrange(mid, hi)),
        v2.subrange(lo, mid).to_multiset() == v0.subrange(lo, mid).to_multiset(),
        v2.subrange(mid, hi).to_multiset() == v0.subrange(mid, hi).to_multiset(),
        o.le(v2[mid - 1], v2[mid]),
    ensures
        sorted_by(o, v2.subrange(lo, hi)),
        all_ok(o, v2.subrange(lo, hi)),
        v2.subrange(lo, hi).to_multiset() == v0.subrange(lo, hi).to_multiset(),
{
    let a = v2.subrange(lo, mid);
    let b = v2.subrange(mid, hi);
    let s = v2.subrange(lo, hi);
    assert(s =~= a + b);
    assert forall|i: int| 0 <= i < s.len() implies o.ok(#[trigger] s[i]) by {
        if i < mid - lo { assert(s[i] == a[i]); } else { assert(s[i] == b[i - (mid - lo)]); }
    }
    assert forall|i: int, j: int| 0 <= i < j < s.len() implies o.le(#[trigger] s[i], #[trigger] s[j]) by {
        let m = mid - lo;
        if j < m {
            assert(s[i] == a[i] && s[j] == a[j]);
        } else if i >= m {
            assert(s[i] == b[i - m] && s[j] == b[j - m]);
        } else {
            assert(s[i] == a[i] && s[j] == b[j - m]);
            assert(a[m - 1] == v2[mid - 1] && b[0] == v2[mid]);
            if i < m - 1 {
                assert(o.le(a[i], a[m - 1]));
            }
            if j > m {
                assert(o.le(b[0], b[j - m]));
            }
            if i < m - 1 && j > m {
                o.lemma_trans(a[i], a[m - 1], b[0]);
                o.lemma_trans(a[i], b[0], b[j - m]);
            } else if i < m - 1 {
                o.lemma_trans(a[i], a[m - 1], b[0]);
            } else if j > m {
                o.lemma_trans(a[m - 1], b[0], b[j - m]);
            }
        }
    }
    vstd::seq_lib::lemma_multiset_commutative(a, b);
    let s0 = v0.subrange(lo, hi);
    assert(s0 =~= v0.subrange(lo, mid) + v0.subrange(mid, hi));
    vstd::seq_lib::lemma_multiset_commutative(v0.subrange(lo, mid), v0.subrange(mid, hi));
}

/// Sort `v[lo..hi]` (top-down merge sort, `tmp` as scratch of the same length; two sorted halves already in order
/// are not merged); the rest of `v` is unchanged.
pub fn sort_range<E: Copy, O: SortOrder<E>>(o: &O, v: &mut Vec<E>, tmp: &mut Vec<E>, lo: usize, hi: usize)
    requires
        o.wf(),
        lo <= hi <= old(v)@.len(),
        old(tmp)@.len() == old(v)@.len(),
        all_ok(*o, old(v)@.subrange(lo as int, hi as int)),
    ensures
        final(v)@.len() == old(v)@.len(),
        final(tmp)@.len() == old(tmp)@.len(),
        sorted_by(*o, final(v)@.subrange(lo as int, hi as int)),
        all_ok(*o, final(v)@.subrange(lo as int, hi as int)),
        final(v)@.subrange(lo as int, hi as int).to_multiset() == old(v)@.subrange(lo as int, hi as int).to_multiset(),
        forall|q: int| 0 <= q < old(v)@.len() && !(lo <= q < hi) ==> final(v)@[q] == old(v)@[q],
    decreases hi - lo,
    no_unwind
{
    if hi - lo <= 1 {
        proof {
            let s = v@.subrange(lo as int, hi as int);
            assert forall|i: int, j: int| 0 <= i < j < s.len() implies o.le(#[trigger] s[i], #[trigger] s[j]) by {}
        }
        return;
    }
    let ghost v0 = v@;
    let mid = lo + (hi - lo) / 2;
    proof {
        let s = v0.subrange(lo as int, hi as int);
        assert forall|q: int| 0 <= q < mid - lo implies o.ok(#[trigger] v0.subrange(lo as int, mid as int)[q]) by {
            assert(v0.subrange(lo as int, mid as int)[q] == s[q]);
        }
    }
    sort_range(o, v, tmp, lo, mid);
    let ghost v1 = v@;
    proof {
        let s = v0.subrange(lo as int, hi as int);
        assert forall|q: int| 0 <= q < hi - mid implies o.ok(#[trigger] v1.subrange(mid as int, hi as int)[q]) by {
            assert(v1[mid + q] == v0[mid + q]);
            assert(s[mid - lo + q] == v0[mid + q]);
        }
        assert(v1.subrange(mid as int, hi as int) =~= v0.subrange(mid as int, hi as int));
    }
    sort_range(o, v, tmp, mid, hi);
    let ghost v2 = v@;
    proof {
        assert(v2.subrange(lo as int, mid as int) =~= v1.subrange(lo as int, mid as int));
    }
    // already in order across the halves (common for concatenated sorted runs): no merge needed
    proof {
        assert(v2.subrange(lo as int, mid as int)[mid - lo - 1] == v2[mid - 1]);
        assert(v2.subrange(mid as int, hi as int)[0] == v2[mid as int]);
    }
    if o.le_exec(v[mid - 1], v[mid]) {
        proof { lemma_halves_in_order(*o, v0, v2, lo as int, mid as int, hi as int); }
        return;
    }
    merge_into(o, v, lo, mid, v, mid, hi, tmp, lo);
    let ghost t = tmp@;
    copy_range(tmp, v, lo, hi);
    proof {
        let s0 = v0.subrange(lo as int, hi as int);
        assert(s0 =~= v0.subrange(lo as int, mid as int) + v0.subrange(mid as int, hi as int));
        vstd::seq_lib::lemma_multiset_commutative(v0.subrange(lo as int, mid as int), v0.subrange(mid as int, hi as int));
        assert(v@.subrange(lo as int, hi as int) == t.subrange(lo as int, lo + (mid - lo) + (hi - mid)));
    }
}

// --------------------------------------------------------------------------------------------------- parallel driver

// ------------------------------------------------------------------------------------------- the orders of this query

/// Group keys `(nm, tag, pk)` in lexicographic order.
pub open spec fn key_le(a: Partial, b: Partial) -> bool {
    a.nm < b.nm || (a.nm == b.nm && (a.tag < b.tag || (a.tag == b.tag && a.pk <= b.pk)))
}

pub struct KeyOrder {}

impl SortOrder<Partial> for KeyOrder {
    open spec fn wf(&self) -> bool {
        true
    }

    open spec fn ok(&self, a: Partial) -> bool {
        true
    }

    open spec fn le(&self, a: Partial, b: Partial) -> bool {
        key_le(a, b)
    }

    proof fn lemma_total(&self, a: Partial, b: Partial) {
    }

    proof fn lemma_trans(&self, a: Partial, b: Partial, c: Partial) {
    }

    fn le_exec(&self, a: Partial, b: Partial) -> (r: bool) {
        a.nm < b.nm || (a.nm == b.nm && (a.tag < b.tag || (a.tag == b.tag && a.pk <= b.pk)))
    }
}

/// Groups by sum, largest first.
pub struct SumOrder {}

impl SortOrder<Partial> for SumOrder {
    open spec fn wf(&self) -> bool {
        true
    }

    open spec fn ok(&self, a: Partial) -> bool {
        true
    }

    open spec fn le(&self, a: Partial, b: Partial) -> bool {
        a.sum >= b.sum
    }

    proof fn lemma_total(&self, a: Partial, b: Partial) {
    }

    proof fn lemma_trans(&self, a: Partial, b: Partial, c: Partial) {
    }

    fn le_exec(&self, a: Partial, b: Partial) -> (r: bool) {
        a.sum >= b.sum
    }
}

/// Filings by name code.
pub struct NameOrder {}

impl SortOrder<Filing> for NameOrder {
    open spec fn wf(&self) -> bool {
        true
    }

    open spec fn ok(&self, a: Filing) -> bool {
        true
    }

    open spec fn le(&self, a: Filing, b: Filing) -> bool {
        a.nm <= b.nm
    }

    proof fn lemma_total(&self, a: Filing, b: Filing) {
    }

    proof fn lemma_trans(&self, a: Filing, b: Filing, c: Filing) {
    }

    fn le_exec(&self, a: Filing, b: Filing) -> (r: bool) {
        a.nm <= b.nm
    }
}


} // verus!
