//! HAVING and ORDER BY over group tables: a worker task keeps the (sum, key) pairs of one table whose sum exceeds the
//! threshold and sorts them by sum, descending (`FilterTask`); the calling thread merges sorted lists bottom-up
//! between two buffers (`merge_all`: the lists become runs of one buffer, adjacent runs are merged level by level,
//! `merge_level`). The multiset of pairs is kept throughout (`ms_all`).
use vstd::prelude::*;
use vstd::multiset::Multiset;
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::groups::{above, lemma_above};
use crate::agent::common::msort::{pairs, desc, merge_ranges, sort_range, copy_range, lemma_pairs_push, lemma_pairs_frame, lemma_pairs_split};

verus! {

/// A sorted list: the pairs `(v[i], k[i])` for `i < n`.
pub struct Sorted {
    pub v: Vec<i128>,
    pub k: Vec<i64>,
    pub n: usize,
}

impl Sorted {
    pub open spec fn wf(&self) -> bool {
        self.v@.len() == self.k@.len() && self.n <= self.v@.len()
    }

    pub open spec fn view(&self) -> Seq<(int, int)> {
        pairs(self.v@, self.k@, 0, self.n as int)
    }
}

/// Keep the pairs of `(sums, keys)[0..used)` whose sum exceeds `thr`, sorted by sum, descending.
pub struct FilterTask {
    pub keys: Vec<i64>,
    pub sums: Vec<i128>,
    pub used: usize,
    pub thr: i128,
    pub av: Vec<i128>,
    pub ak: Vec<i64>,
    pub bv: Vec<i128>,
    pub bk: Vec<i64>,
}

impl FilterTask {
    /// The input pairs.
    pub open spec fn input(&self) -> Seq<(int, int)> {
        pairs(self.sums@, self.keys@, 0, self.used as int)
    }
}

impl WorkerTask for FilterTask {
    type Output = Sorted;

    open spec fn pre(&self) -> bool {
        &&& self.used <= self.keys@.len() && self.keys@.len() == self.sums@.len()
        &&& self.av@.len() == self.ak@.len() && self.bv@.len() == self.av@.len() && self.bk@.len() == self.av@.len()
        &&& self.used <= self.av@.len()
    }

    open spec fn post(&self, out: Sorted) -> bool {
        &&& out.wf()
        &&& desc(out.view())
        &&& out.view().to_multiset() == above(self.input(), self.thr as int).to_multiset()
    }

    fn declared_rows(&self) -> (u64, u64) {
        (0, self.used as u64)
    }

    fn run(self) -> (out: Sorted) {
        let ghost task = self;
        let FilterTask { keys, sums, used, thr, av, ak, bv, bk } = self;
        let mut av = av;
        let mut ak = ak;
        let mut bv = bv;
        let mut bk = bk;
        let mut n: usize = 0;
        let mut j: usize = 0;
        proof {
            assert(pairs(av@, ak@, 0, 0) =~= Seq::<(int, int)>::empty());
            assert(pairs(sums@, keys@, 0, 0) =~= Seq::<(int, int)>::empty());
        }
        while j < used
            invariant
                used <= keys@.len(), keys@.len() == sums@.len(),
                av@.len() == ak@.len(), bv@.len() == av@.len(), bk@.len() == av@.len(), used <= av@.len(),
                n <= j <= used,
                pairs(av@, ak@, 0, n as int) == above(pairs(sums@, keys@, 0, j as int), thr as int),
                task.keys == keys && task.sums == sums && task.used == used && task.thr == thr && task == self,
            decreases used - j,
        {
            let ghost before = pairs(av@, ak@, 0, n as int);
            let s = sums[j];
            proof {
                lemma_pairs_push(sums@, keys@, 0, j as int);
                let e = (sums@[j as int] as int, keys@[j as int] as int);
                assert(pairs(sums@, keys@, 0, j + 1).drop_last() =~= pairs(sums@, keys@, 0, j as int));
                assert(pairs(sums@, keys@, 0, j + 1).last() == e);
            }
            if s > thr {
                let ghost av0 = av@;
                let ghost ak0 = ak@;
                av[n] = s;
                ak[n] = keys[j];
                proof {
                    lemma_pairs_frame(av0, ak0, av@, ak@, 0, n as int);
                    lemma_pairs_push(av@, ak@, 0, n as int);
                }
                n = n + 1;
            }
            j = j + 1;
        }
        let ghost unsorted = pairs(av@, ak@, 0, n as int);
        sort_range(&mut av, &mut ak, &mut bv, &mut bk, 0, n);
        Sorted { v: av, k: ak, n }
    }
}

// ------------------------------------------------------------------------------------------ merging

/// The multiset of all pairs of a sequence of sorted lists.
pub open spec fn ms_all(s: Seq<Sorted>) -> Multiset<(int, int)>
    decreases s.len(),
{
    if s.len() == 0 { Multiset::empty() } else { ms_all(s.drop_last()).add(s.last().view().to_multiset()) }
}

/// The first list and the rest.
pub proof fn lemma_ms_all_first(s: Seq<Sorted>)
    requires s.len() > 0,
    ensures ms_all(s) == s[0].view().to_multiset().add(ms_all(s.drop_first())),
    decreases s.len(),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    if s.len() == 1 {
        assert(s.drop_last() =~= Seq::<Sorted>::empty());
        assert(s.drop_first() =~= Seq::<Sorted>::empty());
        assert(ms_all(s) =~= s[0].view().to_multiset().add(ms_all(s.drop_first())));
    } else {
        lemma_ms_all_first(s.drop_last());
        assert(s.drop_last().drop_first() =~= s.drop_first().drop_last());
        assert(s.drop_first().last() == s.last());
        assert(s.drop_last()[0] == s[0]);
        assert(ms_all(s) =~= s[0].view().to_multiset().add(ms_all(s.drop_first())));
    }
}

/// One more list.
pub proof fn lemma_ms_all_push(s: Seq<Sorted>, x: Sorted)
    ensures ms_all(s.push(x)) == ms_all(s).add(x.view().to_multiset()),
{
    assert(s.push(x).drop_last() =~= s);
}

/// Every list is well formed and sorted.
pub open spec fn all_sorted(s: Seq<Sorted>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i]).wf() && desc(s[i].view())
}

/// The number of pairs of a sequence of sorted lists.
pub open spec fn n_all(s: Seq<Sorted>) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { n_all(s.drop_last()) + s.last().n }
}

/// The multiset of all pairs has `n_all` elements.
pub proof fn lemma_n_all(s: Seq<Sorted>)
    requires forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i]).wf(),
    ensures ms_all(s).len() == n_all(s),
    decreases s.len(),
{
    broadcast use vstd::multiset::group_multiset_axioms, vstd::seq_lib::group_to_multiset_ensures;
    if s.len() > 0 {
        let d = s.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies (#[trigger] d[i]).wf() by {
            assert(d[i] == s[i]);
        }
        lemma_n_all(d);
        assert(s.last() == s[s.len() - 1]);
        assert(s.last().view().len() == s.last().n);
    }
}

/// Runs `[bnd[i], bnd[i + 1])` of `(v, k)` cover `[0, total)` in order, each sorted by value, descending.
pub open spec fn runs_wf(v: Seq<i128>, k: Seq<i64>, bnd: Seq<usize>, total: int) -> bool {
    &&& v.len() == k.len() && total <= v.len()
    &&& bnd.len() >= 1 && bnd[0] == 0 && bnd.last() == total
    &&& forall|i: int, j: int| 0 <= i <= j < bnd.len() ==> #[trigger] bnd[i] <= #[trigger] bnd[j]
    &&& forall|i: int| 0 <= i < bnd.len() - 1 ==> desc(#[trigger] pairs(v, k, bnd[i] as int, bnd[i + 1] as int))
}

/// Copy the first `n` pairs of `(sv, sk)` to `[off, off + n)` of `(dv, dk)`, leaving everything else unchanged.
pub fn copy_to(sv: &Vec<i128>, sk: &Vec<i64>, n: usize, dv: &mut Vec<i128>, dk: &mut Vec<i64>, off: usize)
    requires
        n <= sv@.len(), n <= sk@.len(), off + n <= old(dv)@.len(), old(dv)@.len() == old(dk)@.len(),
        off + n <= usize::MAX,
    ensures
        final(dv)@.len() == old(dv)@.len(), final(dk)@.len() == old(dk)@.len(),
        pairs(final(dv)@, final(dk)@, off as int, off + n) == pairs(sv@, sk@, 0, n as int),
        forall|i: int| 0 <= i < final(dv)@.len() && !(off <= i < off + n) ==> final(dv)@[i] == old(dv)@[i] && final(dk)@[i] == old(dk)@[i],
{
    let ghost dv0 = dv@;
    let ghost dk0 = dk@;
    let mut i: usize = 0;
    while i < n
        invariant
            n <= sv@.len(), n <= sk@.len(), off + n <= dv@.len(), dv@.len() == dk@.len(), i <= n,
            off + n <= usize::MAX,
            dv@.len() == dv0.len(), dk@.len() == dk0.len(),
            forall|j: int| 0 <= j < i ==> dv@[off + j] == sv@[j] && dk@[off + j] == sk@[j],
            forall|j: int| 0 <= j < dv@.len() && !(off <= j < off + i) ==> dv@[j] == dv0[j] && dk@[j] == dk0[j],
        decreases n - i,
    {
        assert(off + i < dv@.len());
        dv[off + i] = sv[i];
        dk[off + i] = sk[i];
        i = i + 1;
    }
    assert(pairs(dv@, dk@, off as int, off + n) =~= pairs(sv@, sk@, 0, n as int));
}

/// The multiset of pairs of adjacent ranges.
pub proof fn lemma_pairs_ms_split(v: Seq<i128>, k: Seq<i64>, lo: int, mid: int, hi: int)
    requires 0 <= lo <= mid <= hi <= v.len(), hi <= k.len(),
    ensures pairs(v, k, lo, hi).to_multiset() == pairs(v, k, lo, mid).to_multiset().add(pairs(v, k, mid, hi).to_multiset()),
{
    lemma_pairs_split(v, k, lo, mid, hi);
    vstd::seq_lib::lemma_multiset_commutative(pairs(v, k, lo, mid), pairs(v, k, mid, hi));
}

/// One level of the bottom-up merge: runs `2j` and `2j + 1` of `a` merged into one run of `b` (an odd last run
/// copied). The pairs of `[0, total)` keep their multiset.
fn merge_level(av: &Vec<i128>, ak: &Vec<i64>, bnd: &Vec<usize>, total: usize, bv: &mut Vec<i128>, bk: &mut Vec<i64>)
    -> (bnd2: Vec<usize>)
    requires
        runs_wf(av@, ak@, bnd@, total as int), bnd@.len() >= 2,
        old(bv)@.len() == av@.len(), old(bk)@.len() == av@.len(),
    ensures
        final(bv)@.len() == av@.len(), final(bk)@.len() == av@.len(),
        runs_wf(final(bv)@, final(bk)@, bnd2@, total as int),
        bnd2@.len() < bnd@.len() || bnd@.len() <= 2,
        bnd2@.len() >= 2 || bnd@.len() <= 2,
        bnd@.len() <= 2 ==> bnd2@.len() == 2,
        pairs(final(bv)@, final(bk)@, 0, total as int).to_multiset() == pairs(av@, ak@, 0, total as int).to_multiset(),
{
    broadcast use vstd::multiset::group_multiset_axioms, vstd::seq_lib::group_to_multiset_ensures;
    let nb = bnd.len();
    let runs = nb - 1;
    let mut bnd2: Vec<usize> = Vec::new();
    bnd2.push(0);
    let mut j: usize = 0;
    proof {
        assert(pairs(bv@, bk@, 0, 0) =~= Seq::<(int, int)>::empty());
        assert(pairs(av@, ak@, 0, 0) =~= Seq::<(int, int)>::empty());
    }
    while 2 * j < runs
        invariant
            runs_wf(av@, ak@, bnd@, total as int), nb == bnd@.len(), runs == nb - 1, nb >= 2,
            bv@.len() == av@.len(), bk@.len() == av@.len(),
            2 * j <= runs + 1, bnd2@.len() == j + 1,
            bnd2@[0] == 0,
            bnd2@.last() == bnd@[if 2 * j <= runs { 2 * j as int } else { runs as int }],
            forall|a: int, b: int| 0 <= a <= b < bnd2@.len() ==> #[trigger] bnd2@[a] <= #[trigger] bnd2@[b],
            forall|a: int| 0 <= a < bnd2@.len() ==> #[trigger] bnd2@[a] <= total,
            forall|a: int| 0 <= a < bnd2@.len() - 1 ==> desc(#[trigger] pairs(bv@, bk@, bnd2@[a] as int, bnd2@[a + 1] as int)),
            pairs(bv@, bk@, 0, bnd2@.last() as int).to_multiset() == pairs(av@, ak@, 0, bnd2@.last() as int).to_multiset(),
        decreases runs + 1 - 2 * j,
    {
        let lo = bnd[2 * j];
        let ghost bv0 = bv@;
        let ghost bk0 = bk@;
        let ghost b2 = bnd2@;
        proof {
            assert(bnd@[2 * j as int] <= bnd@[nb - 1]);
            assert(b2.last() == lo);
        }
        if 2 * j + 1 < runs {
            let mid = bnd[2 * j + 1];
            let hi = bnd[2 * j + 2];
            proof {
                assert(bnd@[2 * j as int] <= bnd@[2 * j + 1] && bnd@[2 * j + 1] <= bnd@[2 * j + 2]);
                assert(bnd@[2 * j + 2] <= bnd@[nb - 1]);
                let i0 = 2 * j as int;
                let i1 = 2 * j + 1;
                assert(desc(pairs(av@, ak@, bnd@[i0] as int, bnd@[i0 + 1] as int)));
                assert(desc(pairs(av@, ak@, bnd@[i1] as int, bnd@[i1 + 1] as int)));
            }
            merge_ranges(av, ak, lo, mid, av, ak, mid, hi, bv, bk, lo);
            bnd2.push(hi);
            proof {
                lemma_pairs_frame(bv0, bk0, bv@, bk@, 0, lo as int);
                lemma_pairs_ms_split(bv@, bk@, 0, lo as int, hi as int);
                lemma_pairs_ms_split(av@, ak@, 0, lo as int, hi as int);
                lemma_pairs_ms_split(av@, ak@, lo as int, mid as int, hi as int);
                assert(bnd2@.last() == hi);
                assert(2 * (j + 1) <= runs ==> bnd@[2 * (j + 1)] == hi);
                assert(2 * (j + 1) > runs ==> 2 * j + 2 == runs);
            }
        } else {
            let hi = bnd[2 * j + 1];
            proof {
                assert(bnd@[2 * j as int] <= bnd@[2 * j + 1]);
                assert(desc(pairs(av@, ak@, bnd@[2 * j as int] as int, bnd@[2 * j + 1] as int)));
            }
            copy_range(av, ak, bv, bk, lo, hi);
            bnd2.push(hi);
            proof {
                assert(pairs(bv@, bk@, lo as int, hi as int) =~= pairs(av@, ak@, lo as int, hi as int));
                lemma_pairs_frame(bv0, bk0, bv@, bk@, 0, lo as int);
                lemma_pairs_ms_split(bv@, bk@, 0, lo as int, hi as int);
                lemma_pairs_ms_split(av@, ak@, 0, lo as int, hi as int);
            }
        }
        proof {
            let b3 = bnd2@;
            assert(b3.len() == b2.len() + 1);
            assert forall|a: int| 0 <= a < b3.len() - 1 implies desc(#[trigger] pairs(bv@, bk@, b3[a] as int, b3[a + 1] as int)) by {
                if a < b2.len() - 1 {
                    assert(b3[a] == b2[a] && b3[a + 1] == b2[a + 1]);
                    assert(b2[a + 1] <= b2.last());
                    lemma_pairs_frame(bv0, bk0, bv@, bk@, b2[a] as int, b2[a + 1] as int);
                }
            }
            assert forall|a: int, b: int| 0 <= a <= b < b3.len() implies #[trigger] b3[a] <= #[trigger] b3[b] by {
                if b < b2.len() {
                    assert(b3[a] == b2[a] && b3[b] == b2[b]);
                } else if a < b2.len() {
                    assert(b3[a] == b2[a]);
                    assert(b2[a] <= b2.last());
                }
            }
            assert forall|a: int| 0 <= a < b3.len() implies #[trigger] b3[a] <= total by {
                if a < b2.len() { assert(b3[a] == b2[a]); }
            }
        }
        j = j + 1;
    }
    proof {
        assert(bnd2@.last() == total);
        assert(2 * j >= runs);
    }
    bnd2
}

/// Merge all lists into one sorted list with all their pairs (at most `usize::MAX` of them): the lists are copied
/// as runs into one buffer, then adjacent runs are merged level by level between two buffers (two allocations in
/// all, instead of one per merge).
pub fn merge_all(lists: Vec<Sorted>) -> (r: Sorted)
    requires all_sorted(lists@), ms_all(lists@).len() <= usize::MAX,
    ensures r.wf(), desc(r.view()), r.view().to_multiset() == ms_all(lists@),
{
    broadcast use vstd::multiset::group_multiset_axioms, vstd::seq_lib::group_to_multiset_ensures;
    let nl = lists.len();
    proof {
        lemma_n_all(lists@);
    }
    // the total count, the runs' boundaries
    let mut total: usize = 0;
    let mut bnd: Vec<usize> = Vec::new();
    bnd.push(0);
    let mut t: usize = 0;
    while t < nl
        invariant
            nl == lists@.len(), t <= nl, all_sorted(lists@),
            n_all(lists@) == ms_all(lists@).len(), ms_all(lists@).len() <= usize::MAX,
            total == n_all(lists@.take(t as int)),
            bnd@.len() == t + 1, bnd@[0] == 0, bnd@.last() == total,
            forall|a: int| 0 <= a < t ==> #[trigger] bnd@[a + 1] == bnd@[a] + lists@[a].n,
        decreases nl - t,
    {
        proof {
            lemma_n_all_take(lists@, t + 1);
            lemma_n_all_mono(lists@, t + 1);
            assert(lists@.take(t + 1).drop_last() =~= lists@.take(t as int));
        }
        let ghost b0 = bnd@;
        total = total + lists[t].n;
        bnd.push(total);
        proof {
            assert forall|a: int| 0 <= a < t + 1 implies #[trigger] bnd@[a + 1] == bnd@[a] + lists@[a].n by {
                if a < t { assert(bnd@[a + 1] == b0[a + 1] && bnd@[a] == b0[a]); }
            }
        }
        t = t + 1;
    }
    proof {
        assert(lists@.take(nl as int) =~= lists@);
        lemma_bounds_mono(bnd@, lists@);
    }
    // level 0: copy the lists as runs into one buffer
    let mut av: Vec<i128> = vec![0i128; total];
    let mut ak: Vec<i64> = vec![0i64; total];
    let mut t: usize = 0;
    proof {
        assert(pairs(av@, ak@, 0, 0) =~= Seq::<(int, int)>::empty());
        assert(lists@.take(0) =~= Seq::<Sorted>::empty());
    }
    while t < nl
        invariant
            nl == lists@.len(), t <= nl, all_sorted(lists@),
            av@.len() == total, ak@.len() == total,
            bnd@.len() == nl + 1, bnd@[0] == 0, bnd@.last() == total,
            forall|a: int| 0 <= a < nl ==> #[trigger] bnd@[a + 1] == bnd@[a] + lists@[a].n,
            forall|a: int, b: int| 0 <= a <= b < bnd@.len() ==> #[trigger] bnd@[a] <= #[trigger] bnd@[b],
            forall|a: int| 0 <= a < t ==> desc(#[trigger] pairs(av@, ak@, bnd@[a] as int, bnd@[a + 1] as int)),
            pairs(av@, ak@, 0, bnd@[t as int] as int).to_multiset() == ms_all(lists@.take(t as int)),
        decreases nl - t,
    {
        let l = &lists[t];
        let off = bnd[t];
        let ghost av0 = av@;
        let ghost ak0 = ak@;
        proof {
            assert(lists@[t as int].wf() && desc(lists@[t as int].view()));
            assert(bnd@[t + 1] <= bnd@[nl as int]);
        }
        copy_to(&l.v, &l.k, l.n, &mut av, &mut ak, off);
        proof {
            let hi = bnd@[t + 1] as int;
            assert(hi == off + l.n);
            lemma_pairs_frame(av0, ak0, av@, ak@, 0, off as int);
            lemma_pairs_ms_split(av@, ak@, 0, off as int, hi);
            assert(pairs(av@, ak@, off as int, hi) == l.view());
            assert(lists@.take(t + 1).drop_last() =~= lists@.take(t as int));
            assert(lists@.take(t + 1).last() == lists@[t as int]);
            assert forall|a: int| 0 <= a < t + 1 implies desc(#[trigger] pairs(av@, ak@, bnd@[a] as int, bnd@[a + 1] as int)) by {
                if a < t {
                    assert(bnd@[a + 1] <= bnd@[t as int]);
                    lemma_pairs_frame(av0, ak0, av@, ak@, bnd@[a] as int, bnd@[a + 1] as int);
                }
            }
        }
        t = t + 1;
    }
    proof {
        assert(lists@.take(nl as int) =~= lists@);
    }
    // the levels
    let mut bv: Vec<i128> = vec![0i128; total];
    let mut bk: Vec<i64> = vec![0i64; total];
    while bnd.len() > 2
        invariant
            runs_wf(av@, ak@, bnd@, total as int), av@.len() == total,
            bv@.len() == total, bk@.len() == total,
            pairs(av@, ak@, 0, total as int).to_multiset() == ms_all(lists@),
        decreases bnd@.len(),
    {
        let bnd2 = merge_level(&av, &ak, &bnd, total, &mut bv, &mut bk);
        let tv = av;
        let tk = ak;
        av = bv;
        ak = bk;
        bv = tv;
        bk = tk;
        bnd = bnd2;
    }
    let r = Sorted { v: av, k: ak, n: total };
    proof {
        if bnd@.len() == 2 {
            assert(desc(pairs(r.v@, r.k@, bnd@[0] as int, bnd@[1] as int)));
        } else {
            assert(total == 0);
            assert(r.view() =~= Seq::<(int, int)>::empty());
        }
    }
    r
}

/// The counts of a prefix of lists.
pub proof fn lemma_n_all_take(s: Seq<Sorted>, t: int)
    requires 0 < t <= s.len(),
    ensures n_all(s.take(t)) == n_all(s.take(t - 1)) + s[t - 1].n,
{
    assert(s.take(t).drop_last() =~= s.take(t - 1));
    assert(s.take(t).last() == s[t - 1]);
}

/// The count of a prefix is at most the count of all lists.
pub proof fn lemma_n_all_mono(s: Seq<Sorted>, t: int)
    requires 0 <= t <= s.len(),
    ensures n_all(s.take(t)) <= n_all(s),
    decreases s.len() - t,
{
    if t < s.len() {
        lemma_n_all_mono(s, t + 1);
        lemma_n_all_take(s, t + 1);
    } else {
        assert(s.take(t) =~= s);
    }
}

/// Cumulative counts do not decrease.
proof fn lemma_bounds_mono(bnd: Seq<usize>, s: Seq<Sorted>)
    requires bnd.len() == s.len() + 1, forall|a: int| 0 <= a < s.len() ==> #[trigger] bnd[a + 1] == bnd[a] + s[a].n,
    ensures forall|a: int, b: int| 0 <= a <= b < bnd.len() ==> #[trigger] bnd[a] <= #[trigger] bnd[b],
{
    assert forall|a: int, b: int| 0 <= a <= b < bnd.len() implies #[trigger] bnd[a] <= #[trigger] bnd[b] by {
        lemma_bounds_step(bnd, s, a, b);
    }
}

proof fn lemma_bounds_step(bnd: Seq<usize>, s: Seq<Sorted>, a: int, b: int)
    requires
        bnd.len() == s.len() + 1, forall|i: int| 0 <= i < s.len() ==> #[trigger] bnd[i + 1] == bnd[i] + s[i].n,
        0 <= a <= b < bnd.len(),
    ensures bnd[a] <= bnd[b],
    decreases b - a,
{
    if a < b {
        lemma_bounds_step(bnd, s, a, b - 1);
        let i = b - 1;
        assert(bnd[i + 1] == bnd[i] + s[i].n);
    }
}

} // verus!
