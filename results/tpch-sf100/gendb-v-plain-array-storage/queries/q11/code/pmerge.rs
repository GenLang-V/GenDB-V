//! Parallel merge of sorted lists of (value, key) pairs (values descending) by value buckets.
//!
//! Layout: bucket bounds `sp[0] = top() > ... >= sp[nb] = bot()` (ghost; the inner `nb - 1` are i128 splitters
//! taken from the longest list); bucket `j` holds the pairs with value in `(sp[j + 1], sp[j]]`. Each list is sorted,
//! so the pairs of list `i` above `sp[j]` are its prefix `[0, cuts[i][j])` and bucket `j` of list `i` is the slice
//! `[cuts[i][j], cuts[i][j + 1])`. One worker task per bucket copies its slices into buffers allocated by the calling
//! thread and sorts them (`BucketTask`); the calling thread concatenates the buckets in order.
//!
//! Proof: `prefix_ms(j)` (the pairs above `sp[j]` of all lists) grows by `bucket_ms(j)` from bound `j` to `j + 1`
//! (`lemma_prefix_step`), from the empty multiset (`j = 0`) to all pairs (`j = nb`, `lemma_prefix_all`); the
//! concatenation is sorted because every pair of bucket `j` is above `sp[j + 1]` and every later pair is not.
use vstd::prelude::*;
use vstd::multiset::Multiset;
use std::sync::Arc;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS, WorkerTask, fork_join};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::agent::common::msort::{pairs, desc, sort_range, lemma_pairs_split, lemma_pairs_frame};
use crate::agent::filter::{Sorted, ms_all, all_sorted, n_all, lemma_n_all, copy_to, lemma_pairs_ms_split};

verus! {

broadcast use vstd::multiset::group_multiset_axioms, vstd::seq_lib::group_to_multiset_ensures;

/// A bound above every `i128`.
pub open spec fn top() -> int { i128::MAX as int + 1 }

/// A bound below every `i128`.
pub open spec fn bot() -> int { i128::MIN as int - 1 }

/// `nb + 1` non-increasing bucket bounds from `top()` to `bot()`.
pub open spec fn bounds_ok(sp: Seq<int>, nb: int) -> bool {
    &&& nb >= 1 && sp.len() == nb + 1
    &&& sp[0] == top() && sp[nb] == bot()
    &&& forall|j: int| 0 <= j < nb ==> #[trigger] sp[j] >= sp[j + 1]
}

/// `c` cuts the sorted list `l` at bound `x`: its pairs before `c` are above `x`, the others are not.
pub open spec fn cut_at(l: Sorted, c: int, x: int) -> bool {
    &&& 0 <= c <= l.n
    &&& forall|q: int| 0 <= q < c ==> (#[trigger] l.v@[q]) > x
    &&& forall|q: int| c <= q < l.n ==> (#[trigger] l.v@[q]) <= x
}

/// `cuts[i][j]` cuts list `i` at bound `sp[j]`.
pub open spec fn cuts_ok(ls: Seq<Sorted>, cuts: Seq<Vec<usize>>, sp: Seq<int>) -> bool {
    &&& cuts.len() == ls.len()
    &&& forall|i: int| 0 <= i < ls.len() ==> (#[trigger] cuts[i])@.len() == sp.len()
    &&& forall|i: int, j: int| 0 <= i < ls.len() && 0 <= j < sp.len() ==> cut_at(ls[i], (#[trigger] cuts[i]@[j]) as int, sp[j])
}

/// The pairs of list `i` in bucket `j`.
pub open spec fn slice_of(ls: Seq<Sorted>, cuts: Seq<Vec<usize>>, i: int, j: int) -> Seq<(int, int)> {
    pairs(ls[i].v@, ls[i].k@, cuts[i]@[j] as int, cuts[i]@[j + 1] as int)
}

/// The pairs of bucket `j` of the first `t` lists.
pub open spec fn bucket_ms(ls: Seq<Sorted>, cuts: Seq<Vec<usize>>, j: int, t: int) -> Multiset<(int, int)>
    decreases t,
{
    if t <= 0 { Multiset::empty() } else { bucket_ms(ls, cuts, j, t - 1).add(slice_of(ls, cuts, t - 1, j).to_multiset()) }
}

/// The number of pairs of bucket `j` of the first `t` lists.
pub open spec fn bucket_count(ls: Seq<Sorted>, cuts: Seq<Vec<usize>>, j: int, t: int) -> int
    decreases t,
{
    if t <= 0 { 0 } else { bucket_count(ls, cuts, j, t - 1) + (cuts[t - 1]@[j + 1] - cuts[t - 1]@[j]) }
}

/// The pairs above bound `j` of the first `t` lists.
pub open spec fn prefix_ms(ls: Seq<Sorted>, cuts: Seq<Vec<usize>>, j: int, t: int) -> Multiset<(int, int)>
    decreases t,
{
    if t <= 0 {
        Multiset::empty()
    } else {
        prefix_ms(ls, cuts, j, t - 1).add(pairs(ls[t - 1].v@, ls[t - 1].k@, 0, cuts[t - 1]@[j] as int).to_multiset())
    }
}

/// Cuts at non-increasing bounds do not decrease.
pub proof fn lemma_cut_mono(l: Sorted, c1: int, x1: int, c2: int, x2: int)
    requires cut_at(l, c1, x1), cut_at(l, c2, x2), x1 >= x2,
    ensures c1 <= c2,
{
    if c2 < c1 {
        assert(l.v@[c2] > x1);
        assert(l.v@[c2] <= x2);
    }
}

/// The facts of the cuts of list `i` at bounds `j` and `j + 1`.
pub proof fn lemma_cut_pair(ls: Seq<Sorted>, cuts: Seq<Vec<usize>>, sp: Seq<int>, nb: int, i: int, j: int)
    requires all_sorted(ls), bounds_ok(sp, nb), cuts_ok(ls, cuts, sp), 0 <= i < ls.len(), 0 <= j < nb,
    ensures
        0 <= cuts[i]@[j] <= cuts[i]@[j + 1] <= ls[i].n <= ls[i].v@.len(), ls[i].v@.len() == ls[i].k@.len(),
        cut_at(ls[i], cuts[i]@[j] as int, sp[j]), cut_at(ls[i], cuts[i]@[j + 1] as int, sp[j + 1]),
{
    assert(ls[i].wf());
    assert(cut_at(ls[i], cuts[i]@[j] as int, sp[j]));
    assert(cut_at(ls[i], cuts[i]@[j + 1] as int, sp[j + 1]));
    assert(sp[j] >= sp[j + 1]);
    lemma_cut_mono(ls[i], cuts[i]@[j] as int, sp[j], cuts[i]@[j + 1] as int, sp[j + 1]);
}

/// From bound `j` to bound `j + 1` the prefixes gain bucket `j`.
pub proof fn lemma_prefix_step(ls: Seq<Sorted>, cuts: Seq<Vec<usize>>, sp: Seq<int>, nb: int, j: int, t: int)
    requires all_sorted(ls), bounds_ok(sp, nb), cuts_ok(ls, cuts, sp), 0 <= j < nb, 0 <= t <= ls.len(),
    ensures
        prefix_ms(ls, cuts, j + 1, t) == prefix_ms(ls, cuts, j, t).add(bucket_ms(ls, cuts, j, t)),
        bucket_ms(ls, cuts, j, t).len() == bucket_count(ls, cuts, j, t),
    decreases t,
{
    if t <= 0 {
        assert(prefix_ms(ls, cuts, j + 1, t) =~= prefix_ms(ls, cuts, j, t).add(bucket_ms(ls, cuts, j, t)));
    } else {
        lemma_prefix_step(ls, cuts, sp, nb, j, t - 1);
        let i = t - 1;
        lemma_cut_pair(ls, cuts, sp, nb, i, j);
        let l = ls[i];
        lemma_pairs_ms_split(l.v@, l.k@, 0, cuts[i]@[j] as int, cuts[i]@[j + 1] as int);
        assert(prefix_ms(ls, cuts, j + 1, t) =~= prefix_ms(ls, cuts, j, t).add(bucket_ms(ls, cuts, j, t)));
    }
}

/// No pair is above `top()`; every pair is above `bot()`: the prefixes at the outer bounds.
pub proof fn lemma_prefix_ends(ls: Seq<Sorted>, cuts: Seq<Vec<usize>>, sp: Seq<int>, nb: int, t: int)
    requires all_sorted(ls), bounds_ok(sp, nb), cuts_ok(ls, cuts, sp), 0 <= t <= ls.len(),
    ensures prefix_ms(ls, cuts, 0, t) == Multiset::<(int, int)>::empty(), prefix_ms(ls, cuts, nb, t) == ms_all(ls.take(t)),
    decreases t,
{
    if t <= 0 {
        assert(ls.take(t) =~= Seq::<Sorted>::empty());
    } else {
        lemma_prefix_ends(ls, cuts, sp, nb, t - 1);
        let i = t - 1;
        let l = ls[i];
        assert(l.wf());
        assert(cut_at(l, cuts[i]@[0] as int, sp[0]));
        assert(cut_at(l, cuts[i]@[nb] as int, sp[nb]));
        if cuts[i]@[0] > 0 {
            assert(l.v@[0] > top());
        }
        if cuts[i]@[nb] < l.n {
            assert(l.v@[cuts[i]@[nb] as int] <= bot());
        }
        assert(pairs(l.v@, l.k@, 0, 0) =~= Seq::<(int, int)>::empty());
        assert(prefix_ms(ls, cuts, 0, t) =~= Multiset::<(int, int)>::empty());
        assert(ls.take(t).drop_last() =~= ls.take(t - 1));
        assert(ls.take(t).last() == l);
    }
}

/// Bucket `j` of the first `t` lists has at most as many pairs as all lists.
pub proof fn lemma_counts(ls: Seq<Sorted>, cuts: Seq<Vec<usize>>, sp: Seq<int>, nb: int, j: int)
    requires all_sorted(ls), bounds_ok(sp, nb), cuts_ok(ls, cuts, sp), 0 <= j < nb,
    ensures
        prefix_ms(ls, cuts, j, ls.len() as int).len() + bucket_count(ls, cuts, j, ls.len() as int) <= ms_all(ls).len(),
        forall|t: int| 0 <= t <= ls.len() ==> 0 <= #[trigger] bucket_count(ls, cuts, j, t) <= bucket_count(ls, cuts, j, ls.len() as int),
{
    let nl = ls.len() as int;
    lemma_prefix_step(ls, cuts, sp, nb, j, nl);
    lemma_prefix_le(ls, cuts, sp, nb, j + 1, nl);
    lemma_prefix_ends(ls, cuts, sp, nb, nl);
    assert(ls.take(nl) =~= ls);
    assert forall|t: int| 0 <= t <= ls.len() implies 0 <= #[trigger] bucket_count(ls, cuts, j, t) <= bucket_count(ls, cuts, j, nl) by {
        lemma_count_mono(ls, cuts, sp, nb, j, t, nl);
    }
}

/// The prefixes grow with the bound index.
pub proof fn lemma_prefix_le(ls: Seq<Sorted>, cuts: Seq<Vec<usize>>, sp: Seq<int>, nb: int, j: int, t: int)
    requires all_sorted(ls), bounds_ok(sp, nb), cuts_ok(ls, cuts, sp), 0 <= j <= nb, 0 <= t <= ls.len(),
    ensures prefix_ms(ls, cuts, j, t).len() <= prefix_ms(ls, cuts, nb, t).len(),
    decreases nb - j,
{
    if j < nb {
        lemma_prefix_le(ls, cuts, sp, nb, j + 1, t);
        lemma_prefix_step(ls, cuts, sp, nb, j, t);
    }
}

/// Bucket counts of prefixes of the lists do not decrease.
pub proof fn lemma_count_mono(ls: Seq<Sorted>, cuts: Seq<Vec<usize>>, sp: Seq<int>, nb: int, j: int, t: int, u: int)
    requires all_sorted(ls), bounds_ok(sp, nb), cuts_ok(ls, cuts, sp), 0 <= j < nb, 0 <= t <= u <= ls.len(),
    ensures 0 <= bucket_count(ls, cuts, j, t) <= bucket_count(ls, cuts, j, u),
    decreases u,
{
    if u > t {
        lemma_count_mono(ls, cuts, sp, nb, j, t, u - 1);
        lemma_cut_pair(ls, cuts, sp, nb, u - 1, j);
    } else if t > 0 {
        lemma_count_mono(ls, cuts, sp, nb, j, t - 1, t - 1);
        lemma_cut_pair(ls, cuts, sp, nb, t - 1, j);
    }
}

// ------------------------------------------------------------------------------------------ the bucket task

/// Copy pairs `[lo, hi)` of `(sv, sk)` to `[off, off + hi - lo)` of `(dv, dk)`, leaving everything else unchanged.
fn copy_slice(sv: &Vec<i128>, sk: &Vec<i64>, lo: usize, hi: usize, dv: &mut Vec<i128>, dk: &mut Vec<i64>, off: usize)
    requires
        lo <= hi <= sv@.len(), hi <= sk@.len(), off + (hi - lo) <= old(dv)@.len(), old(dv)@.len() == old(dk)@.len(),
    ensures
        final(dv)@.len() == old(dv)@.len(), final(dk)@.len() == old(dk)@.len(),
        pairs(final(dv)@, final(dk)@, off as int, off + (hi - lo)) == pairs(sv@, sk@, lo as int, hi as int),
        forall|i: int| 0 <= i < final(dv)@.len() && !(off <= i < off + (hi - lo)) ==> final(dv)@[i] == old(dv)@[i] && final(dk)@[i] == old(dk)@[i],
    no_unwind
{
    let ghost dv0 = dv@;
    let ghost dk0 = dk@;
    let dl = dv.len();
    let mut q = lo;
    while q < hi
        invariant
            dl == dv@.len(),
            lo <= q <= hi <= sv@.len(), hi <= sk@.len(), off + (hi - lo) <= dv@.len(), dv@.len() == dk@.len(),
            dv@.len() == dv0.len(), dk@.len() == dk0.len(),
            forall|x: int| lo <= x < q ==> dv@[off + x - lo] == sv@[x] && dk@[off + x - lo] == sk@[x],
            forall|x: int| 0 <= x < dv@.len() && !(off <= x < off + (q - lo)) ==> dv@[x] == dv0[x] && dk@[x] == dk0[x],
        decreases hi - q,
    {
        assert(off + (q - lo) < dv@.len());
        let o = off + (q - lo);
        dv[o] = sv[q];
        dk[o] = sk[q];
        q = q + 1;
    }
    assert(pairs(dv@, dk@, off as int, off + (hi - lo)) =~= pairs(sv@, sk@, lo as int, hi as int));
}

/// Bucket `j` of every list, sorted: buffers of `m` pairs (the bucket's size) allocated by the calling thread.
pub struct BucketTask {
    pub lists: Arc<Vec<Sorted>>,
    pub cuts: Arc<Vec<Vec<usize>>>,
    pub j: usize,
    pub m: usize,
    pub av: Vec<i128>,
    pub ak: Vec<i64>,
    pub bv: Vec<i128>,
    pub bk: Vec<i64>,
    pub sp: Ghost<Seq<int>>,
}

impl BucketTask {
    /// What the task needs, with `nb` buckets.
    pub open spec fn ready(&self, nb: int) -> bool {
        let ls = (*self.lists)@;
        let cs = (*self.cuts)@;
        &&& all_sorted(ls) && bounds_ok(self.sp@, nb) && cuts_ok(ls, cs, self.sp@)
        &&& 0 <= self.j < nb < usize::MAX
        &&& self.m == bucket_count(ls, cs, self.j as int, ls.len() as int)
        &&& self.av@.len() == self.m && self.ak@.len() == self.m && self.bv@.len() == self.m && self.bk@.len() == self.m
    }

    /// The task's output: bucket `j`, sorted.
    pub open spec fn done(&self, out: Sorted) -> bool {
        let ls = (*self.lists)@;
        let cs = (*self.cuts)@;
        let j = self.j as int;
        &&& out.wf() && out.n == self.m && desc(out.view())
        &&& out.view().to_multiset() == bucket_ms(ls, cs, j, ls.len() as int)
        &&& forall|q: int| 0 <= q < out.n ==> self.sp@[j + 1] < (#[trigger] out.view()[q]).0 <= self.sp@[j]
    }
}

impl WorkerTask for BucketTask {
    type Output = Sorted;

    open spec fn pre(&self) -> bool {
        self.ready(self.sp@.len() - 1)
    }

    open spec fn post(&self, out: Sorted) -> bool {
        self.done(out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (0, self.m as u64)
    }

    fn run(self) -> (out: Sorted) {
        let ghost task = self;
        let BucketTask { lists, cuts, j, m, av, ak, bv, bk, sp } = self;
        let ghost sp = sp@;
        let ghost nb = sp.len() - 1;
        let ls: &Vec<Sorted> = &*lists;
        let cs: &Vec<Vec<usize>> = &*cuts;
        let ghost lsv = ls@;
        let ghost csv = cs@;
        let mut av = av;
        let mut ak = ak;
        let mut bv = bv;
        let mut bk = bk;
        let nl = ls.len();
        proof {
            lemma_counts(lsv, csv, sp, nb, j as int);
            assert(pairs(av@, ak@, 0, 0) =~= Seq::<(int, int)>::empty());
        }
        let mut off: usize = 0;
        let mut i: usize = 0;
        while i < nl
            invariant
                nl == lsv.len(), i <= nl, ls@ == lsv, cs@ == csv,
                all_sorted(lsv), bounds_ok(sp, nb), cuts_ok(lsv, csv, sp), 0 <= j < nb < usize::MAX,
                m == bucket_count(lsv, csv, j as int, nl as int),
                forall|t: int| 0 <= t <= lsv.len() ==> 0 <= #[trigger] bucket_count(lsv, csv, j as int, t) <= m,
                av@.len() == m, ak@.len() == m, bv@.len() == m, bk@.len() == m,
                off == bucket_count(lsv, csv, j as int, i as int),
                pairs(av@, ak@, 0, off as int).to_multiset() == bucket_ms(lsv, csv, j as int, i as int),
                forall|q: int| 0 <= q < off ==> sp[j + 1] < (#[trigger] av@[q]) <= sp[j as int],
            decreases nl - i,
        {
            let l = &ls[i];
            let ghost av0 = av@;
            let ghost ak0 = ak@;
            proof {
                lemma_cut_pair(lsv, csv, sp, nb, i as int, j as int);
                assert(bucket_count(lsv, csv, j as int, i + 1) <= m);
            }
            let lo = cs[i][j];
            let hi = cs[i][j + 1];
            copy_slice(&l.v, &l.k, lo, hi, &mut av, &mut ak, off);
            proof {
                let s = slice_of(lsv, csv, i as int, j as int);
                assert(s == pairs(l.v@, l.k@, lo as int, hi as int));
                lemma_pairs_frame(av0, ak0, av@, ak@, 0, off as int);
                lemma_pairs_ms_split(av@, ak@, 0, off as int, off + (hi - lo));
                assert forall|q: int| 0 <= q < off + (hi - lo) implies sp[j + 1] < (#[trigger] av@[q]) <= sp[j as int] by {
                    if q >= off {
                        let x = lo + (q - off);
                        assert(pairs(av@, ak@, off as int, off + (hi - lo))[q - off] == s[q - off]);
                        assert(av@[q] == l.v@[x]);
                        assert(cut_at(*l, lo as int, sp[j as int]));
                        assert(cut_at(*l, hi as int, sp[j + 1]));
                    } else {
                        assert(av@[q] == av0[q]);
                    }
                }
            }
            off = off + (hi - lo);
            i = i + 1;
        }
        let ghost unsorted = pairs(av@, ak@, 0, m as int);
        sort_range(&mut av, &mut ak, &mut bv, &mut bk, 0, m);
        let out = Sorted { v: av, k: ak, n: m };
        proof {
            let sorted = out.view();
            assert(sorted == pairs(av@, ak@, 0, m as int));
            assert forall|q: int| 0 <= q < m implies sp[j + 1] < (#[trigger] sorted[q]).0 <= sp[j as int] by {
                let e = sorted[q];
                assert(sorted.to_multiset().contains(e));
                assert(unsorted.to_multiset().contains(e));
                let x = choose|x: int| 0 <= x < unsorted.len() && unsorted[x] == e;
                assert(unsorted[x].0 == av@[x] || true);
            }
        }
        out
    }
}

// ------------------------------------------------------------------------------------------ the calling thread

/// Merge sorted lists into one sorted list holding all their pairs, with `nb` bucket tasks.
pub fn parallel_merge(lists: Vec<Sorted>, nb: usize, dispatch: &mut Dispatch) -> (r: Result<Sorted, WorkerFailure>)
    requires all_sorted(lists@), ms_all(lists@).len() <= usize::MAX, 2 <= nb <= MAX_WORKERS, lists@.len() >= 1,
    ensures r matches Ok(s) ==> s.wf() && desc(s.view()) && s.view().to_multiset() == ms_all(lists@),
{
    let ghost ls = lists@;
    let nl = lists.len();
    proof {
        lemma_n_all(ls);
    }
    // the longest list gives the splitters
    let mut longest: usize = 0;
    let mut t: usize = 1;
    while t < nl
        invariant nl == lists@.len(), 1 <= t <= nl, longest < nl,
        decreases nl - t,
    {
        if lists[t].n > lists[longest].n {
            longest = t;
        }
        t = t + 1;
    }
    let l0 = &lists[longest];
    // splitters `sp[1..nb)`, non-increasing (each clamped to the previous one)
    let mut spv: Vec<i128> = Vec::new();
    let ghost mut sp: Seq<int> = seq![top()];
    let mut prev: i128 = i128::MAX;
    let mut j: usize = 1;
    while j < nb
        invariant
            1 <= j <= nb, sp.len() == j, spv@.len() + 1 == j, sp[0] == top(),
            l0.wf(),
            forall|x: int| 1 <= x < j ==> #[trigger] sp[x] == spv@[x - 1] as int,
            forall|x: int| 0 <= x < j - 1 ==> #[trigger] sp[x] >= sp[x + 1],
            j > 1 ==> prev as int == sp[j - 1],
        decreases nb - j,
    {
        let c = if l0.n > 0 {
            let ln = l0.n as u128;
            let ju = j as u128;
            assert(ln * ju <= 0xFFFF_FFFF_FFFF_FFFF * 0xFFFF_FFFF_FFFF_FFFFu128) by (nonlinear_arith)
                requires ln <= 0xFFFF_FFFF_FFFF_FFFFu128, ju <= 0xFFFF_FFFF_FFFF_FFFFu128;
            let idx = (ln * ju / (nb as u128)) as usize;
            if idx < l0.n { l0.v[idx] } else { i128::MIN }
        } else {
            i128::MIN
        };
        let s = if c < prev { c } else { prev };
        spv.push(s);
        proof {
            sp = sp.push(s as int);
        }
        prev = s;
        j = j + 1;
    }
    proof {
        sp = sp.push(bot());
        assert(bounds_ok(sp, nb as int));
    }
    // the cuts of every list at every bound
    let mut cuts: Vec<Vec<usize>> = Vec::new();
    let mut t: usize = 0;
    while t < nl
        invariant
            nl == ls.len(), lists@ == ls, t <= nl, all_sorted(ls), bounds_ok(sp, nb as int),
            spv@.len() + 1 == nb, forall|x: int| 1 <= x < nb ==> #[trigger] sp[x] == spv@[x - 1] as int,
            cuts@.len() == t,
            forall|i: int| 0 <= i < t ==> (#[trigger] cuts@[i])@.len() == sp.len(),
            forall|i: int, x: int| 0 <= i < t && 0 <= x < sp.len() ==> cut_at(ls[i], (#[trigger] cuts@[i]@[x]) as int, sp[x]),
        decreases nl - t,
    {
        let l = &lists[t];
        proof {
            assert(l.wf() && desc(l.view()));
        }
        let mut row: Vec<usize> = Vec::new();
        row.push(0);
        let mut q: usize = 0;
        let mut x: usize = 1;
        proof {
            assert(cut_at(*l, 0, sp[0]));
        }
        while x < nb
            invariant
                1 <= x <= nb, row@.len() == x, l.wf(), desc(l.view()), bounds_ok(sp, nb as int),
                spv@.len() + 1 == nb, forall|y: int| 1 <= y < nb ==> #[trigger] sp[y] == spv@[y - 1] as int,
                q <= l.n,
                forall|y: int| 0 <= y < x ==> cut_at(*l, (#[trigger] row@[y]) as int, sp[y]),
                row@[x - 1] == q,
            decreases nb - x,
        {
            let s = spv[x - 1];
            let ghost q0 = q;
            while q < l.n && l.v[q] > s
                invariant
                    q0 <= q <= l.n, l.wf(),
                    forall|z: int| q0 <= z < q ==> (#[trigger] l.v@[z]) > s,
                decreases l.n - q,
            {
                q = q + 1;
            }
            proof {
                assert(sp[x as int] == s as int);
                assert(sp[x - 1] >= sp[x as int]);
                assert(cut_at(*l, q0 as int, sp[x - 1]));
                assert forall|z: int| q <= z < l.n implies (#[trigger] l.v@[z]) <= s by {
                    assert(l.view()[q as int].0 >= l.view()[z].0);
                }
            }
            row.push(q);
            x = x + 1;
        }
        row.push(l.n);
        proof {
            assert(cut_at(*l, l.n as int, sp[nb as int]));
        }
        let ghost c0 = cuts@;
        cuts.push(row);
        proof {
            assert forall|i: int, y: int| 0 <= i < t + 1 && 0 <= y < sp.len() implies cut_at(ls[i], (#[trigger] cuts@[i]@[y]) as int, sp[y]) by {
                if i < t { assert(cuts@[i] == c0[i]); }
            }
            assert forall|i: int| 0 <= i < t + 1 implies (#[trigger] cuts@[i])@.len() == sp.len() by {
                if i < t { assert(cuts@[i] == c0[i]); }
            }
        }
        t = t + 1;
    }
    let ghost csv = cuts@;
    proof {
        assert(cuts_ok(ls, csv, sp));
        lemma_prefix_ends(ls, csv, sp, nb as int, nl as int);
        assert(ls.take(nl as int) =~= ls);
    }
    // the bucket sizes and tasks
    let lists = Arc::new(lists);
    let cuts = Arc::new(cuts);
    let mut tasks: Vec<BucketTask> = Vec::new();
    let mut j: usize = 0;
    while j < nb
        invariant
            j <= nb, nb <= MAX_WORKERS, (*lists)@ == ls, (*cuts)@ == csv, nl == ls.len(),
            all_sorted(ls), bounds_ok(sp, nb as int), cuts_ok(ls, csv, sp), ms_all(ls).len() <= usize::MAX,
            tasks@.len() == j,
            forall|x: int| 0 <= x < j ==> (#[trigger] tasks@[x]).ready(nb as int) && tasks@[x].j == x
                && (*tasks@[x].lists)@ == ls && (*tasks@[x].cuts)@ == csv && tasks@[x].sp@ == sp,
        decreases nb - j,
    {
        proof {
            lemma_counts(ls, csv, sp, nb as int, j as int);
        }
        let cs: &Vec<Vec<usize>> = &*cuts;
        let mut m: usize = 0;
        let mut i: usize = 0;
        while i < nl
            invariant
                i <= nl, nl == ls.len(), cs@ == csv, all_sorted(ls), bounds_ok(sp, nb as int), cuts_ok(ls, csv, sp), j < nb,
                m == bucket_count(ls, csv, j as int, i as int),
                forall|t: int| 0 <= t <= ls.len() ==> 0 <= #[trigger] bucket_count(ls, csv, j as int, t) <= bucket_count(ls, csv, j as int, nl as int),
                bucket_count(ls, csv, j as int, nl as int) <= usize::MAX,
            decreases nl - i,
        {
            proof {
                lemma_cut_pair(ls, csv, sp, nb as int, i as int, j as int);
                assert(bucket_count(ls, csv, j as int, i + 1) <= bucket_count(ls, csv, j as int, nl as int));
            }
            m = m + (cs[i][j + 1] - cs[i][j]);
            i = i + 1;
        }
        let l2 = lists.clone();
        let c2 = cuts.clone();
        assert(l2 == lists && c2 == cuts);
        let task = BucketTask { lists: l2, cuts: c2, j, m,
            av: vec![0i128; m], ak: vec![0i64; m], bv: vec![0i128; m], bk: vec![0i64; m], sp: Ghost(sp) };
        proof {
            assert((*task.lists)@ == ls && (*task.cuts)@ == csv);
            assert(task.m == bucket_count(ls, csv, j as int, nl as int));
            assert(task.av@.len() == m && task.ak@.len() == m && task.bv@.len() == m && task.bk@.len() == m);
            assert(task.ready(nb as int));
        }
        let ghost tk0 = tasks@;
        tasks.push(task);
        proof {
            assert forall|x: int| 0 <= x < j + 1 implies (#[trigger] tasks@[x]).ready(nb as int) && tasks@[x].j == x
                && (*tasks@[x].lists)@ == ls && (*tasks@[x].cuts)@ == csv && tasks@[x].sp@ == sp by {
                if x < j { assert(tasks@[x] == tk0[x]); }
            }
        }
        j = j + 1;
    }
    let ghost tg = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    proof {
        assert forall|x: int| 0 <= x < nb implies (#[trigger] tg[x]).done(outs@[x]) by {
            assert(tg[x].post(outs@[x]));
        }
        lemma_prefix_ends(ls, csv, sp, nb as int, nl as int);
        assert(ls.take(nl as int) =~= ls);
    }
    // concatenate the buckets in order
    let total = n_all_exec(&*lists);
    let mut rv: Vec<i128> = vec![0i128; total];
    let mut rk: Vec<i64> = vec![0i64; total];
    let mut off: usize = 0;
    let mut j: usize = 0;
    proof {
        assert(pairs(rv@, rk@, 0, 0) =~= Seq::<(int, int)>::empty());
    }
    while j < nb
        invariant
            j <= nb, outs@.len() == nb, tg.len() == nb, nl == ls.len(),
            all_sorted(ls), bounds_ok(sp, nb as int), cuts_ok(ls, csv, sp),
            forall|x: int| 0 <= x < nb ==> (#[trigger] tg[x]).done(outs@[x]) && tg[x].j == x
                && (*tg[x].lists)@ == ls && (*tg[x].cuts)@ == csv && tg[x].sp@ == sp && tg[x].m == bucket_count(ls, csv, x, nl as int),
            total == ms_all(ls).len(), rv@.len() == total, rk@.len() == total,
            prefix_ms(ls, csv, nb as int, nl as int) == ms_all(ls),
            off == prefix_ms(ls, csv, j as int, nl as int).len(), off <= total,
            pairs(rv@, rk@, 0, off as int).to_multiset() == prefix_ms(ls, csv, j as int, nl as int),
            desc(pairs(rv@, rk@, 0, off as int)),
            forall|q: int| 0 <= q < off ==> (#[trigger] rv@[q]) > sp[j as int],
        decreases nb - j,
    {
        let o = &outs[j];
        proof {
            assert(tg[j as int].done(outs@[j as int]));
            lemma_prefix_step(ls, csv, sp, nb as int, j as int, nl as int);
            lemma_prefix_le(ls, csv, sp, nb as int, j + 1, nl as int);
            assert(o.n == bucket_count(ls, csv, j as int, nl as int));
            assert(off + o.n <= total);
        }
        let ghost rv0 = rv@;
        let ghost rk0 = rk@;
        let ghost a = pairs(rv0, rk0, 0, off as int);
        let ghost b = o.view();
        copy_to(&o.v, &o.k, o.n, &mut rv, &mut rk, off);
        proof {
            let hi = off + o.n;
            lemma_pairs_frame(rv0, rk0, rv@, rk@, 0, off as int);
            lemma_pairs_split(rv@, rk@, 0, off as int, hi);
            lemma_pairs_ms_split(rv@, rk@, 0, off as int, hi);
            let c = pairs(rv@, rk@, 0, hi);
            assert(c == a + b);
            assert forall|x: int, y: int| 0 <= x < y < c.len() implies (#[trigger] c[x]).0 >= (#[trigger] c[y]).0 by {
                if y < a.len() {
                } else if x >= a.len() {
                    assert(c[x] == b[x - a.len()] && c[y] == b[y - a.len()]);
                } else {
                    assert(c[x] == a[x] && c[y] == b[y - a.len()]);
                    assert(a[x].0 == rv0[x]);
                    assert(b[y - a.len()].0 <= sp[j as int]);
                }
            }
            assert forall|q: int| 0 <= q < hi implies (#[trigger] rv@[q]) > sp[j + 1] by {
                if q < off {
                    assert(rv@[q] == rv0[q]);
                    assert(sp[j as int] >= sp[j + 1]);
                } else {
                    assert(c[q] == b[q - off]);
                }
            }
        }
        off = off + o.n;
        j = j + 1;
    }
    proof {
        assert(off == total);
    }
    Ok(Sorted { v: rv, k: rk, n: total })
}

/// The number of pairs of all lists (at most `usize::MAX`).
fn n_all_exec(lists: &Vec<Sorted>) -> (n: usize)
    requires all_sorted(lists@), ms_all(lists@).len() <= usize::MAX,
    ensures n == ms_all(lists@).len(),
{
    proof {
        lemma_n_all(lists@);
    }
    let mut n: usize = 0;
    let mut t: usize = 0;
    while t < lists.len()
        invariant t <= lists@.len(), n == n_all(lists@.take(t as int)), all_sorted(lists@), n_all(lists@) <= usize::MAX,
        decreases lists@.len() - t,
    {
        proof {
            crate::agent::filter::lemma_n_all_take(lists@, t + 1);
            crate::agent::filter::lemma_n_all_mono(lists@, t + 1);
        }
        n = n + lists[t].n;
        t = t + 1;
    }
    proof {
        assert(lists@.take(lists@.len() as int) =~= lists@);
    }
    n
}

} // verus!
