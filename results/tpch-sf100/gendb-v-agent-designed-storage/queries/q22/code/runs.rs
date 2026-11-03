//! The fused kernel of the fast path: one pass over the selected runs of the country-code order (storage
//! `cust_phoneidx`), window by window over the rows (`WINDOW_ROWS` rows: the balances and directory entries of a
//! window are first streamed into the cache by `touch_window`, then every selected run gathers from them).
//! - task table `bt` (`bt_ok`): a task covers the positions `bt[s][w_lo] .. bt[s][w_hi]` of run `s`; inside it a
//!   cursor per run advances window by window while the row at the cursor is below the window's end (the rows of
//!   a run ascend, so each window gathers from its own rows; the last window takes every remaining position, so
//!   the coverage never depends on that order);
//! - per position `j` (row `r = p[j]`): the balance `ab[r >> 16] + ac[r]` (blocks of 65536 rows), and the absence
//!   of orders `offs[d + r + 1] == offs[d + r]` (dense keys, `dense_ok`: the directory entry of row `r` is `d + r`;
//!   an entry from `nk` on is past the directory: no orders);
//! - per run, a task accumulates the positive balances (`tpc`/`tps`, the AVG subquery's input) and lists the
//!   balances of at least `bl` of the rows without orders (`pband`) in its own region `base[s] ..` of the task's
//!   buffer. `bl` is a little below an estimate of the average, so the list stays short; with `bl == i64::MIN` it
//!   holds every such balance.
//! `TaskF` keeps `cur_ok` for every run's cursor and ends with `run_ok` over its whole range of every run.
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::WorkerTask;
use crate::gendb_entry::work::put;
use super::model::*;
use super::pmodel::*;

verus! {

/// Rows per window of the scan.
pub const WINDOW_ROWS: usize = 16384;

/// The directory entry of row `r`'s key is `d + r` (dense keys); entries from `nk` on are outside the directory.
pub open spec fn dense_ok(v: Cv, d: int) -> bool {
    &&& v.dir
    &&& 0 <= d
    &&& d + v.n <= usize::MAX
    &&& forall|r: int| 0 <= r < v.n ==> #[trigger] rkey(v, r) == v.kmin + d + r
}

/// What the kernel reads: the views, the order `p` over the `n` rows.
pub open spec fn kern_ok(v: Cv, p: Seq<u32>, ac: Seq<u32>, ab: Seq<i64>, offs: Seq<u32>, d: int, nk: int) -> bool {
    &&& view_ok(v, ac, ab, offs, d, nk)
    &&& p.len() == v.n
    &&& rows_in(v, p, 0, v.n)
}

/// Window table of `ns` runs over `nw` windows: nondecreasing boundaries, at most `n`.
pub open spec fn bt_ok(bt: Seq<Vec<usize>>, ns: int, nw: int, n: int) -> bool {
    &&& bt.len() == ns
    &&& forall|s: int| 0 <= s < ns ==> (#[trigger] bt[s])@.len() == nw + 1
    &&& forall|s: int, w: int| 0 <= s < ns && 0 <= w < nw ==> #[trigger] bt[s]@[w] <= bt[s]@[w + 1]
    &&& forall|s: int| 0 <= s < ns ==> (#[trigger] bt[s])@[nw] <= n
}

/// Boundaries of a run never decrease across windows.
pub proof fn lemma_bt_mono(bt: Seq<Vec<usize>>, ns: int, nw: int, n: int, s: int, a: int, b: int)
    requires bt_ok(bt, ns, nw, n), 0 <= s < ns, 0 <= a <= b <= nw,
    ensures bt[s]@[a] <= bt[s]@[b], bt[s]@[b] <= n,
    decreases b - a,
{
    if a < b {
        lemma_bt_mono(bt, ns, nw, n, s, a, b - 1);
        assert(bt[s]@[b - 1] <= bt[s]@[b]);
    }
    lemma_bt_top(bt, ns, nw, n, s, b);
}

/// Boundaries are at most `n`.
proof fn lemma_bt_top(bt: Seq<Vec<usize>>, ns: int, nw: int, n: int, s: int, b: int)
    requires bt_ok(bt, ns, nw, n), 0 <= s < ns, 0 <= b <= nw,
    ensures bt[s]@[b] <= n,
    decreases nw - b,
{
    if b < nw {
        lemma_bt_top(bt, ns, nw, n, s, b + 1);
        assert(bt[s]@[b] <= bt[s]@[b + 1]);
    }
}

/// Candidate `q` of run `s` in a task's buffer.
pub open spec fn cand_at(buf: Seq<i64>, base: Seq<usize>, s: int, q: int) -> int {
    buf[base[s] + q] as int
}

/// The accumulators of run `s` cover its positions `[lo, hi)`: the positive balances (`acnt`/`asum`) and the
/// `kcnt` listed balances of at least `bl` of the rows without orders (`pband`, at `buf[base[s] ..]`).
pub open spec fn run_ok(v: Cv, p: Seq<u32>, acnt: Seq<u64>, asum: Seq<i128>, kcnt: Seq<usize>, buf: Seq<i64>,
    base: Seq<usize>, s: int, lo: int, hi: int, bl: int) -> bool {
    &&& acnt[s] == tpc(v, p, lo, hi)
    &&& asum[s] == tps(v, p, lo, hi)
    &&& kcnt[s] == pband(v, p, lo, hi, bl).len()
    &&& forall|q: int| 0 <= q < kcnt[s] ==> #[trigger] cand_at(buf, base, s, q) == pband(v, p, lo, hi, bl)[q]
}

/// Buffer regions: region `s` holds `size(s)` slots from `base[s]`, in order, inside the buffer.
pub open spec fn regions_ok(base: Seq<usize>, ns: int, sizes: spec_fn(int) -> int, blen: int) -> bool {
    &&& base.len() == ns + 1
    &&& base[0] == 0
    &&& forall|s: int| 0 <= s < ns ==> 0 <= #[trigger] sizes(s) && base[s] + sizes(s) <= base[s + 1]
    &&& base[ns] <= blen
}

/// Region starts never decrease.
pub proof fn lemma_base_mono(base: Seq<usize>, ns: int, sizes: spec_fn(int) -> int, blen: int, a: int, b: int)
    requires regions_ok(base, ns, sizes, blen), 0 <= a <= b <= ns,
    ensures base[a] <= base[b],
    decreases b - a,
{
    if a < b {
        lemma_base_mono(base, ns, sizes, blen, a, b - 1);
        assert(base[b - 1] + sizes(b - 1) <= base[b]);
    }
}

/// `x & y` of two 0/1 flags is their conjunction.
proof fn lemma_flag_and(x: u64, y: u64)
    requires x <= 1, y <= 1,
    ensures (x & y) <= 1, ((x & y) == 1) == (x == 1 && y == 1),
{
    assert((x & y) <= 1 && (((x & y) == 1) == (x == 1 && y == 1))) by (bit_vector) requires x <= 1, y <= 1;
}

/// The rows of the views the kernel reads: blocks of 65536 rows, dense keys (directory entry `d + r`).
pub open spec fn view_ok(v: Cv, ac: Seq<u32>, ab: Seq<i64>, offs: Seq<u32>, d: int, nk: int) -> bool {
    &&& cv_ok(v)
    &&& v.ac == ac && v.ab == ab && v.offs == offs && v.nk == nk
    &&& v.bs == 65536
    &&& offs.len() <= usize::MAX
    &&& dense_ok(v, d)
}

/// Row `r`'s balance and the absence of orders, read from the views.
fn row_direct(ac: &[u32], ab: &[i64], offs: &[u32], d: usize, nk: usize, r: usize, Ghost(v): Ghost<Cv>) -> (x: (i64, bool))
    requires view_ok(v, ac@, ab@, offs@, d as int, nk as int), r < v.n,
    ensures x.0 as int == racct(v, r as int), x.1 == rnoord(v, r as int),
    no_unwind
{
    proof {
        assert((r >> 16) == r / 65536) by (bit_vector);
        assert(-acct_bound() < racct(v, r as int) < acct_bound());
        assert(rkey(v, r as int) == v.kmin + d + r);
    }
    let a: i64 = ab[r >> 16] + ac[r] as i64;
    let e = r + d;
    let none = if e < nk { offs[e + 1] == offs[e] } else { true };
    (a, none)
}

/// Reads one entry per 64-byte line of the balances and directory entries of rows `r0 .. r1` (in row order, so
/// the hardware prefetcher streams them into the cache before the runs gather from them); returns the XOR of the
/// entries read so the reads are kept. A cache warm-up only: no result depends on it.
fn touch_window(ac: &[u32], offs: &[u32], d: usize, nk: usize, r0: usize, r1: usize) -> (x: u64)
    requires r1 <= ac@.len(), offs@.len() == nk + 1, offs@.len() <= usize::MAX,
    no_unwind
{
    // Rows whose directory entry `d + r` lies inside the directory.
    let lim_o = if nk + 1 > d { nk + 1 - d } else { 0 };
    let lim = if r1 < lim_o { r1 } else { lim_o };
    let mut x: u64 = 0;
    let mut r = r0;
    while r < lim
        invariant lim <= ac@.len(), lim > 0 ==> lim + d <= offs@.len(), offs@.len() <= usize::MAX,
        decreases lim - r,
    {
        x = x ^ (ac[r] as u64) ^ (offs[r + d] as u64);
        r = if lim - r <= 16 { lim } else { r + 16 };
    }
    x
}

/// One piece of a run from position `lo`: extends the run's accumulators from `[L, lo)` to `[L, j)`, where `j`
/// is the first position from `lo` that is `hi` or whose row is at least `lim` (with `lim == u64::MAX`: `hi`).
/// Writes only buffer slots `b0 .. bend`.
fn scan_piece(perm: &[u32], ac: &[u32], ab: &[i64], offs: &[u32], d: usize, nk: usize, bl: i64, lo: usize, hi: usize,
    lim: u64, c0: u64, s0: i128, k0: usize, buf: &mut Vec<i64>, b0: usize, bend: usize, Ghost(v): Ghost<Cv>, Ghost(l): Ghost<int>)
    -> (r: (u64, i128, usize, usize))
    requires
        kern_ok(v, perm@, ac@, ab@, offs@, d as int, nk as int),
        0 <= l <= lo <= hi <= v.n,
        c0 == tpc(v, perm@, l, lo as int),
        s0 == tps(v, perm@, l, lo as int),
        k0 == pband(v, perm@, l, lo as int, bl as int).len(),
        forall|q: int| 0 <= q < k0 ==> #[trigger] old(buf)@[b0 + q] as int == pband(v, perm@, l, lo as int, bl as int)[q],
        b0 + (hi - l) <= bend <= old(buf)@.len(),
    ensures
        lo <= r.3 <= hi,
        lim == u64::MAX ==> r.3 == hi,
        r.0 == tpc(v, perm@, l, r.3 as int),
        r.1 == tps(v, perm@, l, r.3 as int),
        r.2 == pband(v, perm@, l, r.3 as int, bl as int).len(),
        forall|q: int| 0 <= q < r.2 ==> #[trigger] final(buf)@[b0 + q] as int == pband(v, perm@, l, r.3 as int, bl as int)[q],
        final(buf)@.len() == old(buf)@.len(),
        forall|i: int| 0 <= i < old(buf)@.len() && !(b0 <= i < bend) ==> #[trigger] final(buf)@[i] == old(buf)@[i],
    no_unwind
{
    let ghost p = perm@;
    let ghost b_in = buf@;
    let mut c = c0;
    let mut sm = s0;
    let mut kk = k0;
    let mut j = lo;
    proof {
        lemma_t_bound(v, p, l, lo as int, bl as int);
    }
    while j < hi && (perm[j] as u64) < lim
        invariant
            kern_ok(v, p, ac@, ab@, offs@, d as int, nk as int),
            p == perm@,
            0 <= l <= lo <= j <= hi <= v.n,
            c == tpc(v, p, l, j as int),
            sm == tps(v, p, l, j as int),
            kk == pband(v, p, l, j as int, bl as int).len(),
            kk <= j - l,
            forall|q: int| 0 <= q < kk ==> #[trigger] buf@[b0 + q] as int == pband(v, p, l, j as int, bl as int)[q],
            b0 + (hi - l) <= bend <= b_in.len(),
            buf@.len() == b_in.len(),
            forall|i: int| 0 <= i < b_in.len() && !(b0 <= i < bend) ==> #[trigger] buf@[i] == b_in[i],
        decreases hi - j,
    {
        let ghost bj = buf@;
        let r = perm[j] as usize;
        proof {
            assert(p[j as int] < v.n);
        }
        let (a, none) = row_direct(ac, ab, offs, d, nk, r, Ghost(v));
        put(buf, b0 + kk, a);
        proof {
            assert(a as int == pa(v, p, j as int));
            assert(none == rnoord(v, r as int));
            lemma_t_bound(v, p, l, j + 1, bl as int);
            let cc = tpc(v, p, l, j + 1) as int;
            assert(cc * acct_bound() <= 0x1_0000_0000_0000_0000 * acct_bound()) by (nonlinear_arith)
                requires 0 <= cc <= 0x1_0000_0000_0000_0000;
        }
        // Branch-free accumulation (the comparisons are unpredictable): 0/1 flags combined with `&`.
        let pos = a > 0;
        c = c + if pos { 1u64 } else { 0u64 };
        sm = sm + if pos { a as i128 } else { 0i128 };
        let nz: u64 = if none { 1 } else { 0 };
        let ge: u64 = if a >= bl { 1 } else { 0 };
        let listed: u64 = nz & ge;
        proof {
            lemma_flag_and(nz, ge);
        }
        let ghost kk0 = kk as int;
        kk = kk + listed as usize;
        proof {
            let pc = pband(v, p, l, j + 1, bl as int);
            assert forall|q: int| 0 <= q < kk implies #[trigger] buf@[b0 + q] as int == pc[q] by {
                if q < kk0 {
                    assert(buf@[b0 + q] == bj[b0 + q]);
                } else {
                    assert(q == kk0 && none && a >= bl);
                    assert(buf@[b0 + q] == a);
                }
            }
            assert forall|i: int| 0 <= i < b_in.len() && !(b0 <= i < bend) implies #[trigger] buf@[i] == b_in[i] by {
                assert(buf@[i] == bj[i]);
            }
        }
        j = j + 1;
    }
    proof {
        if lim == u64::MAX && j < hi {
            assert((perm@[j as int] as u64) < lim);
        }
    }
    (c, sm, kk, j)
}

/// The kernel's output: per selected run, the positive-balance count and sum and the number of candidates;
/// the candidates of run `s` at `buf[base[s] ..]`.
pub struct FOut {
    pub acnt: Vec<u64>,
    pub asum: Vec<i128>,
    pub kcnt: Vec<usize>,
    pub buf: Vec<i64>,
    /// The XOR of the cache warm-up reads (`touch_window`), no meaning.
    pub touched: u64,
}

/// One task: table columns `w_lo .. w_hi` of every selected run (positions `bt[s][w_lo] .. bt[s][w_hi]`), scanned
/// window by window over the rows `row_lo .. row_hi` (a position is taken in the first window whose end is above
/// its row; the last window takes every remaining position). `bal`/`nf`/`cur` are preallocated scratch.
pub struct TaskF {
    pub perm: &'static [u32],
    pub ac: &'static [u32],
    pub ab: &'static [i64],
    pub offs: &'static [u32],
    pub d: usize,
    pub nk: usize,
    pub bl: i64,
    pub bt: Arc<Vec<Vec<usize>>>,
    pub ns: usize,
    pub nw: usize,
    pub w_lo: usize,
    pub w_hi: usize,
    pub row_lo: usize,
    pub row_hi: usize,
    pub base: Arc<Vec<usize>>,
    pub cur: Vec<usize>,
    pub out: FOut,
    pub v: Ghost<Cv>,
}

/// First position of run `s` in the task.
pub open spec fn lo_of(t: TaskF, s: int) -> int {
    t.bt@[s]@[t.w_lo as int] as int
}

/// End of run `s` in the task.
pub open spec fn hi_of(t: TaskF, s: int) -> int {
    t.bt@[s]@[t.w_hi as int] as int
}

/// Positions of run `s` in the task.
pub open spec fn size_of(t: TaskF) -> spec_fn(int) -> int {
    |s: int| hi_of(t, s) - lo_of(t, s)
}

/// What a task reads and the shape of its preallocated output and scratch.
pub open spec fn task_ok(t: TaskF) -> bool {
    let v = t.v@;
    let ns = t.ns as int;
    &&& kern_ok(v, t.perm@, t.ac@, t.ab@, t.offs@, t.d as int, t.nk as int)
    &&& bt_ok(t.bt@, ns, t.nw as int, v.n)
    &&& t.w_lo <= t.w_hi <= t.nw
    &&& t.row_lo <= t.row_hi <= v.n
    &&& regions_ok(t.base@, ns, size_of(t), t.out.buf@.len() as int)
    &&& t.out.acnt@.len() == ns && t.out.asum@.len() == ns && t.out.kcnt@.len() == ns
    &&& t.cur@.len() == ns
}

/// Every run's accumulators are empty (cover `[lo_of, lo_of)`).
pub open spec fn task_fresh(t: TaskF) -> bool {
    forall|s: int| #![trigger t.out.acnt@[s]] 0 <= s < t.ns ==> t.out.acnt@[s] == 0 && t.out.asum@[s] == 0 && t.out.kcnt@[s] == 0
}

/// Run `s`'s cursor lies in its task range and its accumulators cover the positions up to it.
pub open spec fn cur_ok(t: TaskF, acnt: Seq<u64>, asum: Seq<i128>, kcnt: Seq<usize>, buf: Seq<i64>, cur: Seq<usize>,
    s: int) -> bool {
    &&& lo_of(t, s) <= cur[s] <= hi_of(t, s)
    &&& run_ok(t.v@, t.perm@, acnt, asum, kcnt, buf, t.base@, s, lo_of(t, s), cur[s] as int, t.bl as int)
}

/// Every cursor of the task (a quantifier over `cur_ok`).
pub open spec fn curs_ok(t: TaskF, acnt: Seq<u64>, asum: Seq<i128>, kcnt: Seq<usize>, buf: Seq<i64>, cur: Seq<usize>)
    -> bool {
    forall|s: int| 0 <= s < t.ns ==> #[trigger] cur_ok(t, acnt, asum, kcnt, buf, cur, s)
}

/// Advancing run `si` (its accumulators and buffer region `base[si] .. base[si + 1]`) keeps the accumulators of
/// another run `s2` over its positions `[lo, cur)`.
proof fn lemma_other_run(v: Cv, p: Seq<u32>, a0: Seq<u64>, s0: Seq<i128>, k0: Seq<usize>, b0: Seq<i64>,
    a1: Seq<u64>, s1: Seq<i128>, k1: Seq<usize>, b1: Seq<i64>, base: Seq<usize>, ns: int, sizes: spec_fn(int) -> int,
    blen: int, si: int, s2: int, lo: int, cur: int, bl: int)
    requires
        cv_ok(v), rows_in(v, p, 0, v.n), 0 <= lo <= cur <= v.n,
        regions_ok(base, ns, sizes, blen), b0.len() == blen,
        0 <= si < ns, 0 <= s2 < ns, si != s2,
        cur - lo <= sizes(s2),
        run_ok(v, p, a0, s0, k0, b0, base, s2, lo, cur, bl),
        a1[s2] == a0[s2], s1[s2] == s0[s2], k1[s2] == k0[s2],
        b1.len() == b0.len(),
        forall|i: int| 0 <= i < b0.len() && !(base[si] <= i < base[si + 1]) ==> #[trigger] b1[i] == b0[i],
    ensures
        run_ok(v, p, a1, s1, k1, b1, base, s2, lo, cur, bl),
{
    lemma_t_bound(v, p, lo, cur, bl);
    assert(base[s2] + sizes(s2) <= base[s2 + 1]);
    assert(base[si] + sizes(si) <= base[si + 1]);
    lemma_base_mono(base, ns, sizes, blen, s2 + 1, ns);
    if s2 < si {
        lemma_base_mono(base, ns, sizes, blen, s2 + 1, si);
    } else {
        lemma_base_mono(base, ns, sizes, blen, si + 1, s2);
    }
    assert forall|q: int| 0 <= q < k1[s2] implies #[trigger] cand_at(b1, base, s2, q) == pband(v, p, lo, cur, bl)[q] by {
        let i = base[s2] + q;
        assert(!(base[si] <= i < base[si + 1]));
        assert(b1[i] == b0[i]);
        assert(cand_at(b0, base, s2, q) == pband(v, p, lo, cur, bl)[q]);
    }
}

impl WorkerTask for TaskF {
    type Output = FOut;

    open spec fn pre(&self) -> bool {
        task_ok(*self) && task_fresh(*self)
    }

    open spec fn post(&self, out: FOut) -> bool {
        &&& out.acnt@.len() == self.ns && out.asum@.len() == self.ns && out.kcnt@.len() == self.ns
        &&& out.buf@.len() == self.out.buf@.len()
        &&& forall|s: int| 0 <= s < self.ns ==> #[trigger] run_ok(self.v@, self.perm@, out.acnt@, out.asum@, out.kcnt@,
                out.buf@, self.base@, s, lo_of(*self, s), hi_of(*self, s), self.bl as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.row_lo as u64, self.row_hi as u64)
    }

    fn run(self) -> (out: FOut) {
        let ghost task = self;
        let ghost v = self.v@;
        let ghost p = self.perm@;
        let ghost sizes = size_of(self);
        let TaskF { perm, ac, ab, offs, d, nk, bl, bt, ns, nw, w_lo, w_hi, row_lo, row_hi, base, cur, out, v: gv } = self;
        let btv: &Vec<Vec<usize>> = &*bt;
        let basev: &Vec<usize> = &*base;
        let FOut { acnt, asum, kcnt, buf, touched: _ } = out;
        let mut acnt = acnt;
        let mut asum = asum;
        let mut kcnt = kcnt;
        let mut buf = buf;
        let mut cur = cur;
        let ghost blen = buf@.len() as int;
        // Cursors at the task's first position of every run.
        let mut s: usize = 0;
        while s < ns
            invariant
                task_ok(task), ns == task.ns, w_lo == task.w_lo, bt@ == task.bt@, btv@ == bt@,
                cur@.len() == ns, s <= ns,
                forall|s2: int| 0 <= s2 < s ==> #[trigger] cur@[s2] == lo_of(task, s2),
            decreases ns - s,
        {
            let row: &Vec<usize> = &btv[s];
            proof {
                assert(row@ == bt@[s as int]@);
            }
            let x = row[w_lo];
            put(&mut cur, s, x);
            s = s + 1;
        }
        proof {
            assert forall|s2: int| 0 <= s2 < ns implies #[trigger] cur_ok(task, acnt@, asum@, kcnt@, buf@, cur@, s2) by {
                assert(acnt@ == task.out.acnt@ && asum@ == task.out.asum@ && kcnt@ == task.out.kcnt@);
                assert(task_fresh(task));
                assert(0 <= s2 < task.ns);
                let a0 = task.out.acnt@[s2];
                assert(task.out.acnt@[s2] == 0 && task.out.asum@[s2] == 0 && task.out.kcnt@[s2] == 0);
                lemma_bt_mono(bt@, ns as int, nw as int, v.n, s2, w_lo as int, w_hi as int);
            }
        }
        let mut r0 = row_lo;
        let mut done = false;
        let mut touched: u64 = 0;
        while !done
            invariant
                task_ok(task), v == task.v@, p == task.perm@, sizes == size_of(task),
                perm == task.perm, ac == task.ac, ab == task.ab, offs == task.offs, d == task.d, nk == task.nk, bl == task.bl, bt@ == task.bt@, btv@ == bt@,
                ns == task.ns, nw == task.nw, w_lo == task.w_lo, w_hi == task.w_hi, base@ == task.base@, basev@ == base@,
                row_lo == task.row_lo, row_hi == task.row_hi,
                row_lo <= r0 <= row_hi,
                acnt@.len() == ns, asum@.len() == ns, kcnt@.len() == ns, buf@.len() == blen, cur@.len() == ns,
                blen == task.out.buf@.len(),
                curs_ok(task, acnt@, asum@, kcnt@, buf@, cur@),
                done ==> forall|s2: int| 0 <= s2 < ns ==> #[trigger] cur@[s2] == hi_of(task, s2),
            decreases (row_hi - r0) + (if done { 0int } else { 1int }),
        {
            let r1 = if row_hi - r0 > WINDOW_ROWS { r0 + WINDOW_ROWS } else { row_hi };
            let tx = touch_window(ac, offs, d, nk, r0, r1);
            touched = touched ^ tx;
            let last = r1 >= row_hi;
            let lim: u64 = if last { u64::MAX } else { r1 as u64 };
            let mut s: usize = 0;
            while s < ns
                invariant
                    task_ok(task), v == task.v@, p == task.perm@, sizes == size_of(task),
                    perm == task.perm, ac == task.ac, ab == task.ab, offs == task.offs, d == task.d, nk == task.nk, bl == task.bl, bt@ == task.bt@, btv@ == bt@,
                    ns == task.ns, nw == task.nw, w_lo == task.w_lo, w_hi == task.w_hi, base@ == task.base@, basev@ == base@,
                    last ==> lim == u64::MAX,
                    s <= ns,
                    acnt@.len() == ns, asum@.len() == ns, kcnt@.len() == ns, buf@.len() == blen, cur@.len() == ns,
                    blen == task.out.buf@.len(),
                    curs_ok(task, acnt@, asum@, kcnt@, buf@, cur@),
                    last ==> forall|s2: int| 0 <= s2 < s ==> #[trigger] cur@[s2] == hi_of(task, s2),
                decreases ns - s,
            {
                let ghost si = s as int;
                let row: &Vec<usize> = &btv[s];
                proof {
                    assert(row@ == bt@[si]@);
                    assert(cur_ok(task, acnt@, asum@, kcnt@, buf@, cur@, si));
                    assert(base@[si] + sizes(si) <= base@[si + 1]);
                    lemma_base_mono(base@, ns as int, sizes, blen, si + 1, ns as int);
                    lemma_bt_mono(bt@, ns as int, nw as int, v.n, si, w_lo as int, w_hi as int);
                }
                let lo = cur[s];
                let hi = row[w_hi];
                let b0 = basev[s];
                let bend = basev[s + 1];
                let ghost l = lo_of(task, si);
                let ghost (a0, s0, k0, bb0, c0) = (acnt@, asum@, kcnt@, buf@, cur@);
                proof {
                    assert forall|q: int| 0 <= q < kcnt@[si] implies #[trigger] buf@[b0 + q] as int == pband(v, p, l, lo as int, bl as int)[q] by {
                        assert(cand_at(buf@, base@, si, q) == pband(v, p, l, lo as int, bl as int)[q]);
                    }
                }
                let (c, sm, kk, j) = scan_piece(perm, ac, ab, offs, d, nk, bl, lo, hi, lim,
                    acnt[s], asum[s], kcnt[s], &mut buf, b0, bend, Ghost(v), Ghost(l));
                put(&mut acnt, s, c);
                put(&mut asum, s, sm);
                put(&mut kcnt, s, kk);
                put(&mut cur, s, j);
                proof {
                    assert forall|s2: int| 0 <= s2 < ns implies #[trigger] cur_ok(task, acnt@, asum@, kcnt@, buf@, cur@, s2) by {
                        if s2 == si {
                            assert forall|q: int| 0 <= q < kcnt@[s2] implies #[trigger] cand_at(buf@, base@, s2, q)
                                == pband(v, p, l, j as int, bl as int)[q] by {
                                assert(buf@[b0 + q] as int == pband(v, p, l, j as int, bl as int)[q]);
                            }
                        } else {
                            assert(curs_ok(task, a0, s0, k0, bb0, c0));
                            assert(cur_ok(task, a0, s0, k0, bb0, c0, s2));
                            assert(cur@[s2] == c0[s2]);
                            lemma_bt_mono(bt@, ns as int, nw as int, v.n, s2, w_lo as int, w_hi as int);
                            assert(sizes(s2) == hi_of(task, s2) - lo_of(task, s2));
                            lemma_other_run(v, p, a0, s0, k0, bb0, acnt@, asum@, kcnt@, buf@, base@, ns as int, sizes,
                                blen, si, s2, lo_of(task, s2), c0[s2] as int, bl as int);
                        }
                    }
                    if last {
                        assert forall|s2: int| 0 <= s2 < s + 1 implies #[trigger] cur@[s2] == hi_of(task, s2) by {
                            if s2 < si {
                                assert(c0[s2] == hi_of(task, s2));
                            }
                        }
                    }
                }
                s = s + 1;
            }
            r0 = r1;
            done = last;
        }
        proof {
            assert forall|s: int| 0 <= s < ns implies #[trigger] run_ok(v, p, acnt@, asum@, kcnt@, buf@, base@, s,
                lo_of(task, s), hi_of(task, s), bl as int) by {
                assert(cur_ok(task, acnt@, asum@, kcnt@, buf@, cur@, s));
            }
        }
        FOut { acnt, asum, kcnt, buf, touched }
    }
}

} // verus!
