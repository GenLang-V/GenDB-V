//! One `fork_join` task of Q4 (`MTask`): `lineitem` rows `[lo, hi)` and `orders` rows `[olo, ohi)`.
//!
//! The task walks its orders in batches of at most `BATCH` rows:
//! 1. the rows in the date window (`batch_window`: branch-free append of the row, then a gather of their keys);
//! 2. for each of them, the run `[s, e)` of its key in `l_orderkey` and whether it has a late row (`batch_runs_found`):
//!    the run start is searched forward from a hint `p` (the end of the previous run) in steps of 8 rows when the key
//!    before `p` is below the key, else by a binary search (`run_start`); the found rows are kept;
//! 3. the adjacent pairs of `l_orderkey` the runs passed, `[chk, p)`, checked by a branch-free pass that vectorizes
//!    (`check_pairs`), while those rows are still cached;
//! 4. the priority extent of each found row, then its group slot (`batch_extents`, `batch_group`), with a one-entry
//!    cache per (first byte, length) hash.
//! Finally it checks the remaining adjacent pairs of its `lineitem` rows (`check_pairs` up to `chunk_end`).
//!
//! The run search reads only run boundaries (`run_ok`), so it is correct on any data; the pair checks make it complete:
//! what it proves (`task_post`): its table holds the groups of the rows it added (`p`); when `l_orderkey` is sorted those
//! rows are exactly the qualifying orders of `[olo, ohi)`; and `ok` means every adjacent pair `(j - 1, j)`, `lo < j <=
//! hi` (`j < nl`) is in key order. Sortedness of the whole column is then the conjunction over the tasks.
use vstd::prelude::*;
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::cols::*;
use crate::agent::lists::*;
use crate::agent::table::*;

verus! {

/// Orders rows per batch.
pub const BATCH: usize = 4096;

/// Group slots per task (more distinct priorities send the query to the sequential path).
pub const SLOTS: usize = 64;

/// Entries of the slot cache.
pub const CACHE: usize = 256;

/// End of the pairs a task checks: the row after `hi`, or `nl`.
pub open spec fn chunk_end(l: LCols, hi: int) -> int {
    if hi < l.nl { hi + 1 } else { l.nl as int }
}

/// Stage 1: the rows of `[i0, i1)` in the window, into `bi` (rows) and `bk` (keys).
#[inline(always)]
fn batch_window(o: &OCols, w: Win, i0: usize, i1: usize, bi: &mut Vec<usize>, bk: &mut Vec<i64>) -> (nq: usize)
    requires
        ocols_wf(*o),
        i0 <= i1 <= o.no,
        i1 - i0 <= old(bi)@.len(),
        i1 - i0 <= old(bk)@.len(),
    ensures
        final(bi)@.len() == old(bi)@.len(),
        final(bk)@.len() == old(bk)@.len(),
        nq <= i1 - i0,
        final(bi)@.subrange(0, nq as int) == win_list(*o, w, i0 as int, i1 as int),
        forall|q: int| 0 <= q < nq ==> #[trigger] final(bk)@[q] == o.okey@[final(bi)@[q] as int],
    no_unwind
{
    let mut nq: usize = 0;
    let mut i = i0;
    while i < i1
        invariant
            ocols_wf(*o),
            i0 <= i <= i1 <= o.no,
            i1 - i0 <= bi@.len(),
            i1 - i0 <= bk@.len(),
            bi@.len() == old(bi)@.len(),
            bk@.len() == old(bk)@.len(),
            nq <= i - i0,
            bi@.subrange(0, nq as int) == win_list(*o, w, i0 as int, i as int),
        decreases i1 - i,
    {
        let d = o.odate[i] as i64;
        let ghost b0 = bi@;
        bi[nq] = i;
        proof {
            lemma_win_list_step(*o, w, i0 as int, i as int);
            assert(bi@.subrange(0, nq as int) =~= b0.subrange(0, nq as int));
        }
        // Branch-free: the window test of one row is unpredictable.
        let lo_ok: usize = if d >= w.dlo { 1 } else { 0 };
        let hi_ok: usize = if d < w.dhi { 1 } else { 0 };
        let inc = lo_ok & hi_ok;
        proof {
            assert(inc == 0 || inc == 1) by (bit_vector)
                requires inc == lo_ok & hi_ok, lo_ok == 0 || lo_ok == 1, hi_ok == 0 || hi_ok == 1;
            assert(inc == 1 <==> (lo_ok == 1 && hi_ok == 1)) by (bit_vector)
                requires inc == lo_ok & hi_ok, lo_ok == 0 || lo_ok == 1, hi_ok == 0 || hi_ok == 1;
            if inc == 1 {
                assert(bi@.subrange(0, nq + 1) =~= b0.subrange(0, nq as int).push(i));
            }
        }
        nq = nq + inc;
        i = i + 1;
    }
    // The keys of the window rows only (a gather: most lines of `o_orderkey` hold no window row).
    proof {
        lemma_win_list(*o, w, i0 as int, i1 as int);
    }
    let ghost rows = bi@.subrange(0, nq as int);
    let mut q: usize = 0;
    while q < nq
        invariant
            ocols_wf(*o),
            i1 <= o.no,
            nq <= bi@.len(),
            nq <= bk@.len(),
            bk@.len() == old(bk)@.len(),
            rows == bi@.subrange(0, nq as int),
            rows == win_list(*o, w, i0 as int, i1 as int),
            within(rows, i0 as int, i1 as int),
            q <= nq,
            forall|x: int| 0 <= x < q ==> #[trigger] bk@[x] == o.okey@[bi@[x] as int],
        decreases nq - q,
    {
        assert(rows[q as int] == bi@[q as int]);
        let r = bi[q];
        let ghost k0 = bk@;
        bk[q] = o.okey[r];
        proof {
            assert forall|x: int| 0 <= x < q + 1 implies #[trigger] bk@[x] == o.okey@[bi@[x] as int] by {
                if x < q {
                    assert(bk@[x] == k0[x]);
                }
            }
        }
        q = q + 1;
    }
    nq
}

/// The first `nq` window rows of a batch and their keys.
pub open spec fn rows_ok(o: OCols, bi: Seq<usize>, bk: Seq<i64>, nq: int) -> bool {
    forall|q: int| 0 <= q < nq ==> #[trigger] bk[q] == o.okey@[bi[q] as int] && bi[q] < o.no
}

/// First row `s` of the run of key `k`, searched forward from the hint `p` when the key before `p` is below `k` (by
/// steps of 8 rows, then single rows, inside `[p, hi)`), else by a binary search over all rows. The result is a run
/// boundary on any data (`lower_bound`'s ensures); only its speed depends on the keys being sorted.
#[inline(always)]
fn run_start(l: &LCols, k: i64, p: usize, hi: usize) -> (s: usize)
    requires
        lcols_wf(*l),
        p <= hi <= l.nl,
    ensures
        s <= l.nl,
        s == 0 || l.lk@[s - 1] < k,
        s == l.nl || l.lk@[s as int] >= k,
    no_unwind
{
    if p == 0 || l.lk[p - 1] < k {
        let mut x = p;
        while hi - x >= 8 && l.lk[x + 7] < k
            invariant
                lcols_wf(*l),
                x <= hi <= l.nl,
                x == 0 || l.lk@[x - 1] < k,
            decreases hi - x,
        {
            x = x + 8;
        }
        while x < hi && l.lk[x] < k
            invariant
                lcols_wf(*l),
                x <= hi <= l.nl,
                x == 0 || l.lk@[x - 1] < k,
            decreases hi - x,
        {
            x = x + 1;
        }
        if x < hi {
            x
        } else {
            lower_bound(l, k, x)
        }
    } else {
        lower_bound(l, k, 0)
    }
}

/// Stage 2: for each window row `q < nq`, the run of its key in `l_orderkey` (`run_start`, `run_end`) and whether it has
/// a late row (`run_has_late`); the rows of the found orders, in order, into `bf`. The hint `p` moves to the end of
/// each run (at most `hi`).
#[inline(always)]
fn batch_runs_found(l: &LCols, o: &OCols, hi: usize, nq: usize, bi: &Vec<usize>, bk: &Vec<i64>, bf: &mut Vec<usize>,
    p: &mut usize) -> (nf: usize)
    requires
        lcols_wf(*l),
        ocols_wf(*o),
        *old(p) <= hi <= l.nl,
        nq <= bi@.len(),
        nq <= bk@.len(),
        nq <= old(bf)@.len(),
        rows_ok(*o, bi@, bk@, nq as int),
    ensures
        final(bf)@.len() == old(bf)@.len(),
        *final(p) <= hi,
        nf <= nq,
        forall|f: int| 0 <= f < nf ==> #[trigger] final(bf)@[f] < o.no,
        sorted(*l) ==> final(bf)@.subrange(0, nf as int) == has_filter(*l, *o, bi@.subrange(0, nq as int)),
    no_unwind
{
    // The hint in a local (register) for the loop; written back at the end.
    let mut pp = *p;
    let mut nf: usize = 0;
    let mut q: usize = 0;
    while q < nq
        invariant
            lcols_wf(*l),
            ocols_wf(*o),
            pp <= hi <= l.nl,
            nq <= bi@.len(),
            nq <= bk@.len(),
            nq <= bf@.len(),
            bf@.len() == old(bf)@.len(),
            rows_ok(*o, bi@, bk@, nq as int),
            q <= nq,
            nf <= q,
            forall|f: int| 0 <= f < nf ==> #[trigger] bf@[f] < o.no,
            sorted(*l) ==> bf@.subrange(0, nf as int) == has_filter(*l, *o, bi@.subrange(0, q as int)),
        decreases nq - q,
    {
        let k = bk[q];
        let s = run_start(l, k, pp, hi);
        let e = run_end(l, k, s);
        proof {
            assert(run_ok(*l, k as int, s as int, e as int));
        }
        pp = if e < hi { e } else { hi };
        let found = run_has_late(l, Ghost(k as int), s, e);
        let r = bi[q];
        let ghost f0 = bf@;
        bf[nf] = r;
        proof {
            assert(bi@.subrange(0, q + 1) =~= bi@.subrange(0, q as int).push(r));
            lemma_has_filter_push(*l, *o, bi@.subrange(0, q as int), r);
            if sorted(*l) {
                lemma_run(*l, k as int, s as int, e as int);
                assert(bf@.subrange(0, nf as int) =~= f0.subrange(0, nf as int));
                if found {
                    assert(bf@.subrange(0, nf + 1) =~= f0.subrange(0, nf as int).push(r));
                }
            }
            assert forall|f: int| 0 <= f < nf + 1 implies #[trigger] bf@[f] < o.no by {
                if f < nf {
                    assert(bf@[f] == f0[f]);
                }
            }
        }
        nf = nf + if found { 1usize } else { 0usize };
        q = q + 1;
    }
    *p = pp;
    nf
}

/// The pairs `(j - 1, j)`, `a <= j < b`, `j > lo`, are in key order unless `r > 0`: a branch-free pass (it vectorizes)
/// that extends the checked prefix `[lo, a)` (when `bad == 0`) to `[lo, b)`.
#[inline(always)]
fn check_pairs(l: &LCols, lo: usize, a: usize, b: usize, bad: u64) -> (r: u64)
    requires
        lcols_wf(*l),
        lo <= a <= b <= l.nl,
        bad == 0 ==> pairs_ok(*l, lo as int, a as int),
    ensures r == 0 ==> pairs_ok(*l, lo as int, b as int),
    no_unwind
{
    if a >= b {
        return bad;
    }
    let mut acc = bad;
    let mut j = if a > lo { a } else { lo + 1 };
    proof {
        if acc == 0 && j == lo + 1 {
            assert forall|x: int| lo < x < j implies #[trigger] pair_ok(*l, x) by {}
        }
    }
    while j < b
        invariant
            lcols_wf(*l),
            lo < j,
            b <= l.nl,
            acc == 0 ==> pairs_ok(*l, lo as int, j as int),
        decreases b - j,
    {
        let x: u64 = if l.lk[j - 1] > l.lk[j] { 1 } else { 0 };
        let acc1 = acc | x;
        proof {
            assert(acc1 == 0 ==> acc == 0 && x == 0) by (bit_vector)
                requires acc1 == acc | x;
            if acc1 == 0 {
                assert forall|y: int| lo < y < j + 1 implies #[trigger] pair_ok(*l, y) by {
                    if y < j {
                        assert(pairs_ok(*l, lo as int, j as int));
                    }
                }
            }
        }
        acc = acc1;
        j = j + 1;
    }
    proof {
        if acc == 0 {
            assert forall|y: int| lo < y < b implies #[trigger] pair_ok(*l, y) by {
                if j <= b {
                    assert(pairs_ok(*l, lo as int, j as int));
                }
            }
        }
    }
    acc
}

/// Entry `x` of the extent buffers: the priority bytes `[bs[x], be[x])` of row `bf[x]`, and its cache entry.
pub open spec fn ext_ok(o: OCols, bs: Seq<usize>, be: Seq<usize>, bh: Seq<usize>, bf: Seq<usize>, x: int) -> bool {
    &&& bs[x] <= be[x] <= o.pbytes@.len()
    &&& o.pbytes@.subrange(bs[x] as int, be[x] as int) == prio(o, bf[x] as int)
    &&& bh[x] < CACHE
}

/// The cache entry of a priority: its first byte and length (mod 256), `< CACHE`.
#[inline(always)]
fn key_hash(o: &OCols, a: usize, b: usize) -> (h: usize)
    requires a <= b <= o.pbytes@.len(),
    ensures h < CACHE,
    no_unwind
{
    if b > a {
        let d = b - a;
        let len = d & 255;
        assert(len <= 255) by (bit_vector)
            requires len == d & 255;
        let x = (o.pbytes[a] as usize) * 31 + len;
        let h = x & 255;
        assert(h < 256) by (bit_vector)
            requires h == x & 255;
        h
    } else {
        0
    }
}

/// Stage 4: the priority extent (`bs`, `be`) and cache entry (`bh`) of each found row.
#[inline(always)]
fn batch_extents(o: &OCols, nf: usize, bf: &Vec<usize>, bs: &mut Vec<usize>, be: &mut Vec<usize>, bh: &mut Vec<usize>)
    requires
        ocols_wf(*o),
        nf <= bf@.len(),
        nf <= old(bs)@.len(),
        nf <= old(be)@.len(),
        nf <= old(bh)@.len(),
        forall|f: int| 0 <= f < nf ==> #[trigger] bf@[f] < o.no,
    ensures
        final(bs)@.len() == old(bs)@.len(),
        final(be)@.len() == old(be)@.len(),
        final(bh)@.len() == old(bh)@.len(),
        forall|f: int| 0 <= f < nf ==> #[trigger] ext_ok(*o, final(bs)@, final(be)@, final(bh)@, bf@, f),
    no_unwind
{
    let mut f: usize = 0;
    while f < nf
        invariant
            ocols_wf(*o),
            nf <= bf@.len(),
            nf <= bs@.len(),
            nf <= be@.len(),
            nf <= bh@.len(),
            bs@.len() == old(bs)@.len(),
            be@.len() == old(be)@.len(),
            bh@.len() == old(bh)@.len(),
            forall|x: int| 0 <= x < nf ==> #[trigger] bf@[x] < o.no,
            f <= nf,
            forall|x: int| 0 <= x < f ==> #[trigger] ext_ok(*o, bs@, be@, bh@, bf@, x),
        decreases nf - f,
    {
        let (a, b) = prio_extent(o, bf[f]);
        let h = key_hash(o, a, b);
        let ghost (s0, e0, h0) = (bs@, be@, bh@);
        bs[f] = a;
        be[f] = b;
        bh[f] = h;
        proof {
            assert forall|x: int| 0 <= x < f + 1 implies #[trigger] ext_ok(*o, bs@, be@, bh@, bf@, x) by {
                if x < f {
                    assert(ext_ok(*o, s0, e0, h0, bf@, x));
                    assert(bs@[x] == s0[x] && be@[x] == e0[x] && bh@[x] == h0[x]);
                } else {
                    assert(bs@[x] == a && be@[x] == b && bh@[x] == h);
                    assert(bf@[x] == bf@[f as int]);
                }
            }
        }
        f = f + 1;
    }
}

/// Stage 5: adds the found rows to the table (`false` when the table is full; it is then unusable).
#[inline(always)]
fn batch_group(o: &OCols, nf: usize, bf: &Vec<usize>, bs: &Vec<usize>, be: &Vec<usize>, bh: &Vec<usize>,
    reps: &mut Vec<usize>, counts: &mut Vec<u64>, ng: &mut usize, cache: &mut Vec<usize>, Ghost(p0): Ghost<Seq<usize>>)
    -> (added: bool)
    requires
        ocols_wf(*o),
        nf <= bf@.len(),
        nf <= bs@.len(),
        nf <= be@.len(),
        nf <= bh@.len(),
        old(cache)@.len() == CACHE,
        forall|f: int| 0 <= f < nf ==> #[trigger] bf@[f] < o.no,
        forall|f: int| 0 <= f < nf ==> #[trigger] ext_ok(*o, bs@, be@, bh@, bf@, f),
        tbl_ok(*o, old(reps)@, old(counts)@, *old(ng) as int, p0),
        p0.len() + nf <= usize::MAX,
    ensures
        final(reps)@.len() == old(reps)@.len(),
        final(counts)@.len() == old(counts)@.len(),
        final(cache)@.len() == CACHE,
        added ==> tbl_ok(*o, final(reps)@, final(counts)@, *final(ng) as int, p0 + bf@.subrange(0, nf as int)),
    no_unwind
{
    let mut f: usize = 0;
    proof {
        assert(p0 + bf@.subrange(0, 0) =~= p0);
    }
    while f < nf
        invariant
            ocols_wf(*o),
            nf <= bf@.len(),
            nf <= bs@.len(),
            nf <= be@.len(),
            nf <= bh@.len(),
            cache@.len() == CACHE,
            reps@.len() == old(reps)@.len(),
            counts@.len() == old(counts)@.len(),
            forall|x: int| 0 <= x < nf ==> #[trigger] bf@[x] < o.no,
            forall|x: int| 0 <= x < nf ==> #[trigger] ext_ok(*o, bs@, be@, bh@, bf@, x),
            p0.len() + nf <= usize::MAX,
            f <= nf,
            tbl_ok(*o, reps@, counts@, *ng as int, p0 + bf@.subrange(0, f as int)),
        decreases nf - f,
    {
        let ghost p = p0 + bf@.subrange(0, f as int);
        proof {
            assert(ext_ok(*o, bs@, be@, bh@, bf@, f as int));
        }
        let r = bf[f];
        let a = bs[f];
        let b = be[f];
        let h = bh[f];
        let hint = cache[h];
        proof {
            assert(ext_ok(*o, bs@, be@, bh@, bf@, f as int));
        }
        let (ok, g) = tbl_add_fixed(o, reps, counts, ng, r, a, b, hint, Ghost(p));
        if !ok {
            return false;
        }
        cache[h] = g;
        proof {
            assert(p.push(r) =~= p0 + bf@.subrange(0, f + 1));
        }
        f = f + 1;
    }
    true
}

/// A task: `lineitem` rows `[lo, hi)`, `orders` rows `[olo, ohi)`, the window, and its preallocated buffers.
pub struct MTask {
    pub l: LCols,
    pub o: OCols,
    pub w: Win,
    pub lo: usize,
    pub hi: usize,
    pub olo: usize,
    pub ohi: usize,
    pub reps: Vec<usize>,
    pub counts: Vec<u64>,
    pub bk: Vec<i64>,
    pub bi: Vec<usize>,
    pub bs: Vec<usize>,
    pub be: Vec<usize>,
    pub bf: Vec<usize>,
    pub cache: Vec<usize>,
}

/// A task's result: its group table (`ng` slots) of the rows it added (`p`), whether the table filled up, and whether
/// its `lineitem` pairs are in key order.
pub struct MOut {
    pub ok: bool,
    pub full: bool,
    pub reps: Vec<usize>,
    pub counts: Vec<u64>,
    pub ng: usize,
    pub p: Ghost<Seq<usize>>,
}

pub open spec fn task_pre(l: LCols, o: OCols, lo: usize, hi: usize, olo: usize, ohi: usize, reps: Seq<usize>,
    counts: Seq<u64>, bk: Seq<i64>, bi: Seq<usize>, bs: Seq<usize>, be: Seq<usize>, bf: Seq<usize>, cache: Seq<usize>) -> bool {
    &&& lcols_wf(l)
    &&& ocols_wf(o)
    &&& lo <= hi <= l.nl
    &&& olo <= ohi <= o.no
    &&& reps.len() == SLOTS
    &&& counts.len() == SLOTS
    &&& bk.len() == BATCH
    &&& bi.len() == BATCH
    &&& bs.len() == BATCH
    &&& be.len() == BATCH
    &&& bf.len() == BATCH
    &&& cache.len() == CACHE
}

pub open spec fn task_post(l: LCols, o: OCols, w: Win, lo: usize, hi: usize, olo: usize, ohi: usize, out: MOut) -> bool {
    &&& !out.full ==> tbl_ok(o, out.reps@, out.counts@, out.ng as int, out.p@)
    &&& !out.full ==> (sorted(l) ==> out.p@ == q_list(l, o, w, olo as int, ohi as int))
    &&& !out.full ==> out.p@.len() <= ohi - olo
    &&& (!out.full && out.ok) ==> pairs_ok(l, lo as int, chunk_end(l, hi as int))
}

impl WorkerTask for MTask {
    type Output = MOut;

    open spec fn pre(&self) -> bool {
        task_pre(self.l, self.o, self.lo, self.hi, self.olo, self.ohi, self.reps@, self.counts@, self.bk@, self.bi@,
            self.bs@, self.be@, self.bf@, self.cache@)
    }

    open spec fn post(&self, out: MOut) -> bool {
        task_post(self.l, self.o, self.w, self.lo, self.hi, self.olo, self.ohi, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.olo as u64, self.ohi as u64)
    }

    fn run(self) -> (out: MOut) {
        let MTask { l, o, w, lo, hi, olo, ohi, reps, counts, bk, bi, bs, be, bf, cache } = self;
        let mut reps = reps;
        let mut counts = counts;
        let mut bk = bk;
        let mut bi = bi;
        let mut bs = bs;
        let mut be = be;
        let mut bf = bf;
        let mut cache = cache;
        let mut ng: usize = 0;
        let ghost mut gp: Seq<usize> = Seq::empty();
        proof {
            lemma_tbl_empty(o, reps@, counts@);
            assert(q_list(l, o, w, olo as int, olo as int) == Seq::<usize>::empty());
        }
        // `p`: the run hint; `chk`: the pairs of `[lo, chk)` are checked (in order unless `bad > 0`).
        let mut p = lo;
        let mut chk = lo;
        let mut bad: u64 = 0;
        proof {
            assert forall|j: int| lo < j < lo implies #[trigger] pair_ok(l, j) by {}
        }
        let mut i0 = olo;
        while i0 < ohi
            invariant
                lcols_wf(l),
                ocols_wf(o),
                olo <= i0 <= ohi <= o.no,
                reps@.len() == SLOTS,
                counts@.len() == SLOTS,
                bk@.len() == BATCH,
                bi@.len() == BATCH,
                bs@.len() == BATCH,
                be@.len() == BATCH,
                bf@.len() == BATCH,
                cache@.len() == CACHE,
                lo <= hi <= l.nl,
                p <= hi,
                lo <= chk <= hi,
                bad == 0 ==> pairs_ok(l, lo as int, chk as int),
                tbl_ok(o, reps@, counts@, ng as int, gp),
                gp.len() <= i0 - olo,
                sorted(l) ==> gp == q_list(l, o, w, olo as int, i0 as int),
            decreases ohi - i0,
        {
            let i1 = if ohi - i0 > BATCH { i0 + BATCH } else { ohi };
            let nq = batch_window(&o, w, i0, i1, &mut bi, &mut bk);
            let ghost rows = bi@.subrange(0, nq as int);
            proof {
                lemma_win_list(o, w, i0 as int, i1 as int);
                assert forall|q: int| 0 <= q < nq implies #[trigger] bk@[q] == o.okey@[bi@[q] as int] && bi@[q] < o.no by {
                    assert(bi@[q] == rows[q]);
                    assert(rows[q] == win_list(o, w, i0 as int, i1 as int)[q]);
                    assert(i0 <= win_list(o, w, i0 as int, i1 as int)[q] < i1);
                }
                assert(rows_ok(o, bi@, bk@, nq as int));
            }
            let nf = batch_runs_found(&l, &o, hi, nq, &bi, &bk, &mut bf, &mut p);
            // The pairs the runs of this batch passed, while their rows are cached.
            if p > chk {
                bad = check_pairs(&l, lo, chk, p, bad);
                chk = p;
            }
            batch_extents(&o, nf, &bf, &mut bs, &mut be, &mut bi);
            let added = batch_group(&o, nf, &bf, &bs, &be, &bi, &mut reps, &mut counts, &mut ng, &mut cache, Ghost(gp));
            if !added {
                return MOut { ok: false, full: true, reps, counts, ng, p: Ghost(gp) };
            }
            proof {
                let found = bf@.subrange(0, nf as int);
                if sorted(l) {
                    lemma_q_list_filter(l, o, w, i0 as int, i1 as int);
                    lemma_q_list_split(l, o, w, olo as int, i0 as int, i1 as int);
                }
                gp = gp + found;
            }
            i0 = i1;
        }
        let end = if hi < l.nl { hi + 1 } else { l.nl };
        bad = check_pairs(&l, lo, chk, end, bad);
        MOut { ok: bad == 0, full: false, reps, counts, ng, p: Ghost(gp) }
    }
}

} // verus!
