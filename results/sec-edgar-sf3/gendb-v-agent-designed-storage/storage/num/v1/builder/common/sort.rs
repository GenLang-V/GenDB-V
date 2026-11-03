//! Parallel merge sort over any element type with a total preorder (`SortOrder`), proved to return a sorted
//! permutation (same multiset) of its input.
//!
//! Layout of the algorithm: the input is cut into at most `workers` contiguous chunks; each chunk is sorted by one
//! worker task (top-down recursive merge sort with one scratch buffer, no allocation inside the task); then sorted
//! runs are merged pairwise, one worker task per pair, until one run is left. Every task's output is allocated on
//! the calling thread and moved into the task.
//!
//! Orders are implemented in this file (the source rules let a trait be implemented only in the file that defines
//! it): `TextOrder` (row ids of a text column by byte order, `lex_cmp`) and `KeyOrder` (lexicographic `Key4`).
use vstd::prelude::*;
use vstd::multiset::Multiset;
use crate::spec::text::lex_cmp;
use crate::link::query::{text_at, text_wf, TextCol, TextView};
use crate::bridge::order::{lemma_lex_cmp_antisym, lemma_lex_cmp_trans};
use crate::gendb_entry::parallel::{fork_join, Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::work::{filled, put, text_bytes};

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

// ------------------------------------------------------------------------------------------------- the two orders

/// Row ids `0..rows` of a text column, ordered by their values' bytes (`lex_cmp`).
#[derive(Clone, Copy)]
pub struct TextOrder {
    pub offsets: &'static [i64],
    pub bytes: &'static [u8],
    pub rows: u64,
}

impl TextOrder {
    pub open spec fn text(&self) -> TextView {
        TextView { offsets: self.offsets@, bytes: self.bytes@ }
    }

    /// Bytes of row `a`.
    pub open spec fn value(&self, a: u64) -> Seq<u8> {
        text_at(self.text(), a as int)
    }
}

/// Byte order of two slices, `no_unwind` (lengths passed in: slice `len` is not `no_unwind`).
pub fn lex_cmp_slices(x: &[u8], xn: usize, y: &[u8], yn: usize) -> (r: i8)
    requires xn == x@.len(), yn == y@.len(),
    ensures r as int == lex_cmp(x@, y@),
    no_unwind
{
    let mut i: usize = 0;
    assert(x@.subrange(0, xn as int) =~= x@);
    assert(y@.subrange(0, yn as int) =~= y@);
    while i < xn && i < yn
        invariant
            xn == x@.len(), yn == y@.len(), i <= xn, i <= yn,
            lex_cmp(x@.subrange(i as int, xn as int), y@.subrange(i as int, yn as int)) == lex_cmp(x@, y@),
        decreases xn - i,
    {
        let ghost sx = x@.subrange(i as int, xn as int);
        let ghost sy = y@.subrange(i as int, yn as int);
        if x[i] < y[i] {
            return -1;
        } else if x[i] > y[i] {
            return 1;
        }
        assert(sx.drop_first() =~= x@.subrange(i + 1, xn as int));
        assert(sy.drop_first() =~= y@.subrange(i + 1, yn as int));
        i = i + 1;
    }
    if i < xn { 1 } else if i < yn { -1 } else { 0 }
}

/// Bytes of row `a` of a text column with its length, `no_unwind`.
pub fn text_value(offsets: &'static [i64], bytes: &'static [u8], a: usize) -> (r: (&'static [u8], usize))
    requires
        a + 1 < offsets@.len(),
        a + 1 < usize::MAX,
        0 <= offsets@[a as int] <= offsets@[a + 1] <= bytes@.len(),
    ensures
        r.0@ == text_at(TextView { offsets: offsets@, bytes: bytes@ }, a as int),
        r.1 == r.0@.len(),
    no_unwind
{
    let c = TextCol { offsets, bytes };
    let s = text_bytes(&c, a);
    let hi = offsets[a + 1];
    let lo = offsets[a];
    assert(s@.len() == hi - lo);
    assert(hi <= bytes.len());
    let n = (hi - lo) as usize;
    (s, n)
}

impl SortOrder<u64> for TextOrder {
    open spec fn wf(&self) -> bool {
        &&& self.rows < u64::MAX
        &&& self.rows < usize::MAX
        &&& text_wf(self.text(), self.rows as int)
    }

    open spec fn ok(&self, a: u64) -> bool {
        a < self.rows
    }

    open spec fn le(&self, a: u64, b: u64) -> bool {
        lex_cmp(self.value(a), self.value(b)) <= 0
    }

    proof fn lemma_total(&self, a: u64, b: u64) {
        lemma_lex_cmp_antisym(self.value(a), self.value(b));
    }

    proof fn lemma_trans(&self, a: u64, b: u64, c: u64) {
        lemma_lex_cmp_trans(self.value(a), self.value(b), self.value(c));
    }

    fn le_exec(&self, a: u64, b: u64) -> (r: bool) {
        proof {
            assert(0 <= self.offsets@[a as int] <= self.offsets@[a + 1] <= self.bytes@.len());
            assert(0 <= self.offsets@[b as int] <= self.offsets@[b + 1] <= self.bytes@.len());
        }
        let (x, xn) = text_value(self.offsets, self.bytes, a as usize);
        let (y, yn) = text_value(self.offsets, self.bytes, b as usize);
        lex_cmp_slices(x, xn, y, yn) <= 0
    }
}

/// A sort key of four unsigned words, ordered lexicographically (k0 first).
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Key4 {
    pub k0: u64,
    pub k1: u64,
    pub k2: u64,
    pub k3: u64,
}

/// Lexicographic order of `Key4`.
pub open spec fn key4_le(a: Key4, b: Key4) -> bool {
    a.k0 < b.k0 || (a.k0 == b.k0 && (a.k1 < b.k1 || (a.k1 == b.k1 && (a.k2 < b.k2 || (a.k2 == b.k2 && a.k3 <= b.k3)))))
}

/// The lexicographic order of `Key4` values.
#[derive(Clone, Copy)]
pub struct KeyOrder {}

impl SortOrder<Key4> for KeyOrder {
    open spec fn wf(&self) -> bool {
        true
    }

    open spec fn ok(&self, a: Key4) -> bool {
        true
    }

    open spec fn le(&self, a: Key4, b: Key4) -> bool {
        key4_le(a, b)
    }

    proof fn lemma_total(&self, a: Key4, b: Key4) {
    }

    proof fn lemma_trans(&self, a: Key4, b: Key4, c: Key4) {
    }

    fn le_exec(&self, a: Key4, b: Key4) -> (r: bool) {
        a.k0 < b.k0 || (a.k0 == b.k0 && (a.k1 < b.k1 || (a.k1 == b.k1 && (a.k2 < b.k2 || (a.k2 == b.k2 && a.k3 <= b.k3)))))
    }
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

/// Sort `v[lo..hi]` (top-down merge sort, `tmp` as scratch of the same length); the rest of `v` is unchanged.
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

/// Sum of the multisets of a list of runs.
pub open spec fn runs_multiset<E>(runs: Seq<Vec<E>>) -> Multiset<E>
    decreases runs.len(),
{
    if runs.len() == 0 {
        Multiset::empty()
    } else {
        runs_multiset(runs.drop_last()).add(runs.last()@.to_multiset())
    }
}

/// Runs with pointwise equal multisets have equal sums.
proof fn lemma_runs_multiset_pointwise<E>(a: Seq<Vec<E>>, b: Seq<Vec<E>>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i])@.to_multiset() == b[i]@.to_multiset(),
    ensures
        runs_multiset(a) == runs_multiset(b),
    decreases a.len(),
{
    if a.len() > 0 {
        lemma_runs_multiset_pointwise(a.drop_last(), b.drop_last());
    }
}

/// The multiset of an optional run (empty when absent).
pub open spec fn option_multiset<E>(r: Option<Vec<E>>) -> Multiset<E> {
    match r {
        Some(c) => c@.to_multiset(),
        None => Multiset::empty(),
    }
}

/// Every run is sorted, comparable and nonempty.
pub open spec fn runs_ok<E, O: SortOrder<E>>(o: O, runs: Seq<Vec<E>>) -> bool {
    forall|i: int| 0 <= i < runs.len() ==> sorted_by(o, (#[trigger] runs[i])@) && all_ok(o, runs[i]@) && runs[i]@.len() > 0
}

/// Sum over merge tasks of the multisets of both their runs.
pub open spec fn tasks_multiset<E, O>(tasks: Seq<RunMergeTask<E, O>>) -> Multiset<E>
    decreases tasks.len(),
{
    if tasks.len() == 0 {
        Multiset::empty()
    } else {
        tasks_multiset(tasks.drop_last()).add(tasks.last().left@.to_multiset().add(tasks.last().right@.to_multiset()))
    }
}

/// The merged outputs of the tasks hold the tasks' runs.
proof fn lemma_merge_outputs<E: Copy + Send + 'static, O: SortOrder<E> + Copy + Send + 'static>(
    tasks: Seq<RunMergeTask<E, O>>, outs: Seq<Vec<E>>,
)
    requires
        outs.len() == tasks.len(),
        forall|i: int| 0 <= i < tasks.len() ==> (#[trigger] tasks[i]).post(outs[i]),
    ensures
        runs_multiset(outs) == tasks_multiset(tasks),
    decreases tasks.len(),
{
    if tasks.len() > 0 {
        let k = tasks.len() - 1;
        assert(tasks[k].post(outs[k]));
        lemma_merge_outputs(tasks.drop_last(), outs.drop_last());
    }
}

/// Sorts one chunk inside a worker.
pub struct ChunkSortTask<E, O> {
    pub order: O,
    pub data: Vec<E>,
    pub scratch: Vec<E>,
}

impl<E: Copy + Send + 'static, O: SortOrder<E> + Copy + Send + 'static> WorkerTask for ChunkSortTask<E, O> {
    type Output = Vec<E>;

    open spec fn pre(&self) -> bool {
        &&& self.order.wf()
        &&& self.scratch@.len() == self.data@.len()
        &&& all_ok(self.order, self.data@)
    }

    open spec fn post(&self, out: Vec<E>) -> bool {
        &&& sorted_by(self.order, out@)
        &&& all_ok(self.order, out@)
        &&& out@.to_multiset() == self.data@.to_multiset()
    }

    fn declared_rows(&self) -> (u64, u64) {
        (0, 0)
    }

    fn run(self) -> (out: Vec<E>) {
        let o = self.order;
        let mut v = self.data;
        let mut t = self.scratch;
        let n = v.len();
        proof {
            assert(v@.subrange(0, n as int) =~= v@);
        }
        let ghost v0 = v@;
        sort_range(&o, &mut v, &mut t, 0, n);
        proof {
            assert(v@.subrange(0, n as int) =~= v@);
        }
        v
    }
}

/// Merges two sorted runs inside a worker.
pub struct RunMergeTask<E, O> {
    pub order: O,
    pub left: Vec<E>,
    pub right: Vec<E>,
    pub out: Vec<E>,
}

impl<E: Copy + Send + 'static, O: SortOrder<E> + Copy + Send + 'static> WorkerTask for RunMergeTask<E, O> {
    type Output = Vec<E>;

    open spec fn pre(&self) -> bool {
        &&& self.order.wf()
        &&& self.out@.len() == self.left@.len() + self.right@.len()
        &&& sorted_by(self.order, self.left@) && all_ok(self.order, self.left@)
        &&& sorted_by(self.order, self.right@) && all_ok(self.order, self.right@)
    }

    open spec fn post(&self, out: Vec<E>) -> bool {
        &&& sorted_by(self.order, out@)
        &&& all_ok(self.order, out@)
        &&& out@.to_multiset() == self.left@.to_multiset().add(self.right@.to_multiset())
    }

    fn declared_rows(&self) -> (u64, u64) {
        (0, 0)
    }

    fn run(self) -> (out: Vec<E>) {
        let o = self.order;
        let a = self.left;
        let b = self.right;
        let mut d = self.out;
        let an = a.len();
        let bn = b.len();
        proof {
            assert(a@.subrange(0, an as int) =~= a@);
            assert(b@.subrange(0, bn as int) =~= b@);
        }
        merge_into(&o, &a, 0, an, &b, 0, bn, &mut d, 0);
        proof {
            assert(d@.subrange(0, (an + bn) as int) =~= d@);
        }
        d
    }
}

/// Copy `v[lo..hi]` into a new vector (calling thread).
fn copy_out<E: Copy>(v: &Vec<E>, lo: usize, hi: usize) -> (r: Vec<E>)
    requires lo <= hi <= v@.len(),
    ensures r@ == v@.subrange(lo as int, hi as int),
{
    let mut r: Vec<E> = Vec::with_capacity(hi - lo);
    let mut p = lo;
    while p < hi
        invariant lo <= p <= hi <= v@.len(), r@ == v@.subrange(lo as int, p as int),
        decreases hi - p,
    {
        r.push(v[p]);
        p = p + 1;
        proof {
            assert(r@ =~= v@.subrange(lo as int, p as int));
        }
    }
    r
}

/// Sort `v` with at most `workers` threads: a sorted permutation (same multiset) of `v`.
pub fn par_sort<E: Copy + Send + 'static, O: SortOrder<E> + Copy + Send + 'static>(
    o: O, v: Vec<E>, workers: usize, dispatch: &mut Dispatch,
) -> (r: Result<Vec<E>, QueryError>)
    requires
        o.wf(),
        all_ok(o, v@),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(s) ==> sorted_by(o, s@) && all_ok(o, s@) && s@.to_multiset() == v@.to_multiset(),
        r matches Err(e) ==> e is WorkerFailed,
{
    let n = v.len();
    if n == 0 {
        proof {
            assert forall|i: int, j: int| 0 <= i < j < v@.len() implies o.le(#[trigger] v@[i], #[trigger] v@[j]) by {}
        }
        return Ok(v);
    }
    let runs = sort_chunks(o, &v, workers, dispatch)?;
    proof { assert(v@.to_multiset().len() == v@.len()); }
    merge_runs(o, runs, dispatch, Ghost(v@.to_multiset()))
}

/// Phase 1: cut `v` into at most `workers` nonempty chunks and sort each in its own task.
fn sort_chunks<E: Copy + Send + 'static, O: SortOrder<E> + Copy + Send + 'static>(
    o: O, v: &Vec<E>, workers: usize, dispatch: &mut Dispatch,
) -> (r: Result<Vec<Vec<E>>, QueryError>)
    requires
        o.wf(),
        all_ok(o, v@),
        v@.len() > 0,
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(runs) ==> 1 <= runs@.len() <= MAX_WORKERS && runs_ok(o, runs@)
            && runs_multiset(runs@) == v@.to_multiset(),
        r matches Err(e) ==> e is WorkerFailed,
{
    let n = v.len();
    let chunks = if n < workers { n } else { workers };
    let step = n / chunks;
    proof {
        assert(step >= 1) by (nonlinear_arith) requires chunks <= n, chunks >= 1, step == n / chunks;
        assert(step * chunks <= n) by (nonlinear_arith) requires chunks >= 1, step == n / chunks;
    }
    let mut tasks: Vec<ChunkSortTask<E, O>> = Vec::new();
    let mut c: usize = 0;
    let mut lo: usize = 0;
    while c < chunks
        invariant
            1 <= chunks <= n, chunks <= MAX_WORKERS, step >= 1, step * chunks <= n, n == v@.len(),
            c <= chunks, c < chunks ==> lo == c * step, lo <= n, c < chunks ==> lo < n,
            o.wf(), all_ok(o, v@),
            tasks@.len() == c,
            forall|t: int| 0 <= t < c ==> (#[trigger] tasks@[t]).pre() && tasks@[t].order == o && tasks@[t].data@.len() > 0,
            runs_multiset(Seq::new(c as nat, |t: int| tasks@[t].data)) == v@.subrange(0, lo as int).to_multiset(),
            c == chunks ==> lo == n,
        decreases chunks - c,
    {
        proof {
            assert((c + 1) * step == lo + step) by (nonlinear_arith) requires lo == c * step;
            assert((c + 1) * step <= chunks * step) by (nonlinear_arith) requires c + 1 <= chunks, step >= 1;
        }
        let hi = if c + 1 == chunks { n } else { lo + step };
        let data = copy_out(v, lo, hi);
        let scratch = filled(hi - lo, v[lo]);
        proof {
            assert forall|i: int| 0 <= i < data@.len() implies o.ok(#[trigger] data@[i]) by {
                assert(data@[i] == v@[lo + i]);
            }
        }
        let ghost before = tasks@;
        tasks.push(ChunkSortTask { order: o, data, scratch });
        proof {
            let runs = Seq::new((c + 1) as nat, |t: int| tasks@[t].data);
            assert(runs.drop_last() =~= Seq::new(c as nat, |t: int| before[t].data));
            assert(v@.subrange(0, hi as int) =~= v@.subrange(0, lo as int) + v@.subrange(lo as int, hi as int));
            vstd::seq_lib::lemma_multiset_commutative(v@.subrange(0, lo as int), v@.subrange(lo as int, hi as int));
        }
        lo = hi;
        c = c + 1;
        proof {
            if c < chunks {
                assert(lo == c * step) by (nonlinear_arith) requires lo == (c - 1) * step + step;
                assert(c * step < n) by (nonlinear_arith) requires c < chunks, step * chunks <= n, step >= 1;
            }
        }
    }
    proof {
        assert(v@.subrange(0, n as int) =~= v@);
    }
    let ghost task_view = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(outs) => outs,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    proof {
        assert forall|t: int| 0 <= t < chunks implies (#[trigger] outs@[t])@.to_multiset()
            == Seq::new(chunks as nat, |t: int| task_view[t].data)[t]@.to_multiset() by {
            assert(task_view[t].post(outs@[t]));
        }
        lemma_runs_multiset_pointwise(outs@, Seq::new(chunks as nat, |t: int| task_view[t].data));
        assert forall|t: int| 0 <= t < outs@.len() implies sorted_by(o, (#[trigger] outs@[t])@)
            && all_ok(o, outs@[t]@) && outs@[t]@.len() > 0 by {
            assert(task_view[t].post(outs@[t]));
            assert(outs@[t]@.to_multiset().len() == task_view[t].data@.to_multiset().len());
        }
    }
    Ok(outs)
}

/// Phase 2: merge pairs of sorted runs, one task per pair, until one run is left.
fn merge_runs<E: Copy + Send + 'static, O: SortOrder<E> + Copy + Send + 'static>(
    o: O, runs: Vec<Vec<E>>, dispatch: &mut Dispatch, Ghost(total): Ghost<Multiset<E>>,
) -> (r: Result<Vec<E>, QueryError>)
    requires
        o.wf(),
        1 <= runs@.len() <= MAX_WORKERS,
        runs_ok(o, runs@),
        runs_multiset(runs@) == total,
        total.len() <= usize::MAX,
    ensures
        r matches Ok(s) ==> sorted_by(o, s@) && all_ok(o, s@) && s@.to_multiset() == total,
        r matches Err(e) ==> e is WorkerFailed,
{
    let mut runs = runs;
    while runs.len() > 1
        invariant
            o.wf(),
            1 <= runs@.len() <= MAX_WORKERS,
            runs_ok(o, runs@),
            runs_multiset(runs@) == total,
            total.len() <= usize::MAX,
        decreases runs@.len(),
    {
        let old_len = runs.len();
        let mut carry: Option<Vec<E>> = None;
        if runs.len() % 2 == 1 {
            let ghost before = runs@;
            let last = runs.pop().unwrap();
            proof {
                assert(runs@ =~= before.drop_last());
                assert(last == before.last());
            }
            carry = Some(last);
        }
        let mut tasks: Vec<RunMergeTask<E, O>> = Vec::new();
        while runs.len() >= 2
            invariant
                o.wf(),
                runs@.len() % 2 == 0,
                runs@.len() + 2 * tasks@.len() + (if carry is Some { 1int } else { 0int }) == old_len,
                old_len <= MAX_WORKERS,
                runs_ok(o, runs@),
                carry matches Some(c) ==> sorted_by(o, c@) && all_ok(o, c@) && c@.len() > 0,
                forall|t: int| 0 <= t < tasks@.len() ==> (#[trigger] tasks@[t]).pre() && tasks@[t].order == o
                    && tasks@[t].left@.len() > 0,
                total.len() <= usize::MAX,
                runs_multiset(runs@).add(tasks_multiset(tasks@)).add(option_multiset(carry)) == total,
            decreases runs@.len(),
        {
            let ghost before = runs@;
            let right = runs.pop().unwrap();
            let left = runs.pop().unwrap();
            proof {
                assert(runs@ =~= before.drop_last().drop_last());
                assert(right == before.last());
                assert(left == before.drop_last().last());
                assert(runs_multiset(before) == runs_multiset(before.drop_last()).add(right@.to_multiset()));
                assert(runs_multiset(before.drop_last())
                    == runs_multiset(before.drop_last().drop_last()).add(left@.to_multiset()));
                assert(left@.len() > 0 && right@.len() > 0) by {
                    assert(before[before.len() - 1] == right);
                    assert(before[before.len() - 2] == left);
                }
                assert(runs_multiset(before).len() + tasks_multiset(tasks@).len() + option_multiset(carry).len()
                    == total.len());
                assert(left@.to_multiset().len() + right@.to_multiset().len() <= runs_multiset(before).len());
            }
            let out = filled(left.len() + right.len(), left[0]);
            let ghost tbefore = tasks@;
            tasks.push(RunMergeTask { order: o, left, right, out });
            proof {
                assert(tasks@.drop_last() =~= tbefore);
                let a = runs_multiset(runs@);
                let l = left@.to_multiset();
                let rr = right@.to_multiset();
                assert(runs_multiset(before) == a.add(l).add(rr));
                assert(tasks_multiset(tasks@) == tasks_multiset(tbefore).add(l.add(rr)));
                assert(runs_multiset(runs@).add(tasks_multiset(tasks@)) =~= runs_multiset(before).add(tasks_multiset(tbefore)));
            }
        }
        let ghost task_view = tasks@;
        let outs = match fork_join(dispatch, tasks) {
            Ok(outs) => outs,
            Err(e) => return Err(QueryError::WorkerFailed(e)),
        };
        proof {
            assert(runs@.len() == 0);
            assert(runs_multiset(runs@) == Multiset::<E>::empty());
            lemma_merge_outputs(task_view, outs@);
            assert forall|t: int| 0 <= t < outs@.len() implies sorted_by(o, (#[trigger] outs@[t])@)
                && all_ok(o, outs@[t]@) && outs@[t]@.len() > 0 by {
                assert(task_view[t].post(outs@[t]));
                assert(outs@[t]@.to_multiset().len() == task_view[t].left@.to_multiset().len()
                    + task_view[t].right@.to_multiset().len());
                assert(task_view[t].left@.len() > 0);
            }
        }
        runs = outs;
        match carry {
            Some(c) => {
                let ghost before = runs@;
                runs.push(c);
                proof {
                    assert(runs@.drop_last() =~= before);
                }
            },
            None => {
                proof {
                    assert(runs_multiset(runs@).add(Multiset::empty()) =~= runs_multiset(runs@));
                }
            },
        }
        proof {
            assert(runs_multiset(runs@) =~= total);
        }
    }
    let ghost before = runs@;
    let s = runs.pop().unwrap();
    proof {
        assert(before.drop_last().len() == 0);
        assert(runs_multiset(before.drop_last()) == Multiset::<E>::empty());
        assert(s == before.last());
        assert(runs_multiset(before) =~= s@.to_multiset());
    }
    Ok(s)
}

} // verus!
