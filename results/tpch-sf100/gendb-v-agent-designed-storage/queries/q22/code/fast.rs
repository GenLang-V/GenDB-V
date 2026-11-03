//! The fast path over the country-code order of storage `cust_phoneidx`, on the calling thread around the fused
//! kernel (`runs::TaskF`):
//! 1. `select_runs`: the group of every run (its first row's code, `scan::row_gid`); the runs of a listed code
//!    are selected (`sel_ok`; `sel_of[t]` is run `t`'s selection index, or at least `ns` when not selected);
//! 2. `make_table`: per selected run, its first position in each task's rows (`scan::make_bounds` over the rows,
//!    a binary search per boundary, clamped to stay monotone);
//! 3. `run_fused`: one task per range of rows, each with its own candidate buffer cut into one region per run
//!    (`regions_ok`); one task runs on the calling thread, more go through `fork_join`; `outs_ok` is what the
//!    outputs cover;
//! 4. `combine_a`: per run the positive-balance count and sum over all tasks, then over every run of the order
//!    (unselected runs contribute nothing, `pmodel::lemma_run_a`) and back to row order (`lemma_reindex_a`);
//! 5. `finish_b`: per run the candidates above the average threshold (`pcgt`/`psgt`: the listed balances above
//!    it, `lemma_band`), into the run's group,
//!    then back to row order per group (`lemma_run_b`, `lemma_reindex_b`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::spec::value::*;
use crate::stores::cust_phoneidx::interface::in_run;
use super::model::*;
use super::pmodel::*;
use super::runs::*;
use super::scan::*;
use super::fbind::*;

verus! {

/// Most selected runs the fast path handles (per-task arrays hold one entry per selected run).
pub const MAX_SEL: usize = 4096;

// ------------------------------------------------------------------------------------------------ selection

/// The selected runs: run `sel_of[t]` of `starts`/`ends` is run `t` of the order (a listed group); every other
/// run is of no listed group.
pub open spec fn sel_ok(v: Cv, p: Seq<u32>, rs: Seq<u64>, starts: Seq<usize>, ends: Seq<usize>, gids: Seq<usize>,
    sel_of: Seq<usize>) -> bool {
    let ns = starts.len() as int;
    &&& ends.len() == ns && gids.len() == ns
    &&& sel_of.len() == nruns(rs)
    &&& forall|s: int| 0 <= s < ns ==> #[trigger] starts[s] <= ends[s] <= v.n
    &&& forall|s: int| 0 <= s < ns ==> #[trigger] gids[s] < 7
    &&& forall|s: int| 0 <= s < ns ==> one_group(v, p, starts[s] as int, ends[s] as int, #[trigger] gids[s] as int)
    &&& forall|t: int| 0 <= t < nruns(rs) && #[trigger] sel_of[t] < ns ==>
            starts[sel_of[t] as int] == rs[t] && ends[sel_of[t] as int] == rs[t + 1]
    &&& forall|t: int| 0 <= t < nruns(rs) && #[trigger] sel_of[t] >= ns ==>
            one_group(v, p, rs[t] as int, rs[t + 1] as int, 7)
}

/// Every position of run `t` has the group of the run's first row.
proof fn lemma_run_group(v: Cv, p: Seq<u32>, rs: Seq<u64>, t: int)
    requires corder_ok(v, p, rs), 0 <= t < nruns(rs),
    ensures one_group(v, p, rs[t] as int, rs[t + 1] as int, rgid(v, p[rs[t] as int] as int)),
{
    assert forall|j: int| rs[t] <= j < rs[t + 1] implies #[trigger] rgid(v, p[j] as int) == rgid(v, p[rs[t] as int] as int) by {
        assert(in_run(rs, t, j));
    }
}

/// Run starts lie in `[0, n]`.
proof fn lemma_rs_bound(v: Cv, p: Seq<u32>, rs: Seq<u64>, t: int)
    requires corder_ok(v, p, rs), 0 <= t <= nruns(rs),
    ensures rs[t] <= v.n, t < nruns(rs) ==> rs[t] < v.n,
{
    crate::stores::cust_phoneidx::interface::lemma_runs_mono(rs, nruns(rs), t, nruns(rs));
}

/// The groups of the runs, and the selected (listed) ones; `None` with more than `MAX_SEL` selected runs.
pub fn select_runs(poffs: &[u64], pbytes: &[u8], perm: &[u32], runs: &[u64], table: &Vec<u8>,
    pats: &Vec<&'static [u8]>, plens: &Vec<usize>, Ghost(v): Ghost<Cv>)
    -> (r: Option<(Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>)>)
    requires
        cv_ok(v),
        v.poffs == poffs@,
        v.pbytes == pbytes@,
        v.n <= usize::MAX,
        table_ok(table@, v.ps),
        pats_ok(pats@, plens@, v.ps),
        corder_ok(v, perm@, runs@),
    ensures
        r matches Some(x) ==> sel_ok(v, perm@, runs@, x.0@, x.1@, x.2@, x.3@) && x.0@.len() <= MAX_SEL,
{
    let ghost (p, rs) = (perm@, runs@);
    let m = runs.len() - 1;
    let mut starts: Vec<usize> = Vec::new();
    let mut ends: Vec<usize> = Vec::new();
    let mut gids: Vec<usize> = Vec::new();
    let mut sel_of: Vec<usize> = Vec::new();
    let mut t: usize = 0;
    while t < m
        invariant
            cv_ok(v), v.poffs == poffs@, v.pbytes == pbytes@, v.n <= usize::MAX,
            table_ok(table@, v.ps), pats_ok(pats@, plens@, v.ps),
            corder_ok(v, p, rs), p == perm@, rs == runs@,
            m == nruns(rs),
            t <= m,
            starts@.len() <= MAX_SEL,
            ends@.len() == starts@.len() && gids@.len() == starts@.len(),
            sel_of@.len() == t,
            forall|s: int| 0 <= s < starts@.len() ==> #[trigger] starts@[s] <= ends@[s] <= v.n,
            forall|s: int| 0 <= s < starts@.len() ==> #[trigger] gids@[s] < 7,
            forall|s: int| 0 <= s < starts@.len() ==> one_group(v, p, starts@[s] as int, ends@[s] as int, #[trigger] gids@[s] as int),
            forall|q: int| 0 <= q < t && #[trigger] sel_of@[q] < starts@.len() ==>
                starts@[sel_of@[q] as int] == rs[q] && ends@[sel_of@[q] as int] == rs[q + 1],
            forall|q: int| 0 <= q < t ==> #[trigger] sel_of@[q] < starts@.len() || sel_of@[q] == MAX_SEL,
            forall|q: int| 0 <= q < t && #[trigger] sel_of@[q] == MAX_SEL ==> one_group(v, p, rs[q] as int, rs[q + 1] as int, 7),
        decreases m - t,
    {
        proof {
            lemma_rs_bound(v, p, rs, t as int);
            lemma_rs_bound(v, p, rs, t + 1);
            lemma_run_group(v, p, rs, t as int);
            assert(rs[t as int] < rs[t + 1]);
        }
        let a = runs[t] as usize;
        let b = runs[t + 1] as usize;
        let r0 = perm[a] as usize;
        proof {
            assert(p[a as int] < v.n);
        }
        let g = row_gid(poffs, pbytes, r0, table, pats, plens, Ghost(v));
        let ghost (st0, en0, gi0, so0) = (starts@, ends@, gids@, sel_of@);
        if g < 7 {
            if starts.len() >= MAX_SEL {
                return None;
            }
            sel_of.push(starts.len());
            starts.push(a);
            ends.push(b);
            gids.push(g);
            proof {
                assert forall|q: int| 0 <= q < t + 1 && #[trigger] sel_of@[q] < starts@.len() implies
                    starts@[sel_of@[q] as int] == rs[q] && ends@[sel_of@[q] as int] == rs[q + 1] by {
                    if q < t {
                        assert(so0[q] < st0.len() || so0[q] == MAX_SEL);
                        if so0[q] == MAX_SEL {
                            assert(sel_of@[q] == MAX_SEL);
                            assert(starts@.len() <= MAX_SEL);
                        }
                    }
                }
                assert forall|s: int| 0 <= s < starts@.len() implies one_group(v, p, starts@[s] as int, ends@[s] as int, #[trigger] gids@[s] as int) by {
                    if s < st0.len() {
                        assert(one_group(v, p, st0[s] as int, en0[s] as int, gi0[s] as int));
                    }
                }
                assert forall|q: int| 0 <= q < t + 1 implies #[trigger] sel_of@[q] < starts@.len() || sel_of@[q] == MAX_SEL by {
                    if q < t {
                        assert(so0[q] < st0.len() || so0[q] == MAX_SEL);
                    }
                }
            }
        } else {
            sel_of.push(MAX_SEL);
            proof {
                assert(g == 7);
                assert forall|q: int| 0 <= q < t + 1 && #[trigger] sel_of@[q] < starts@.len() implies
                    starts@[sel_of@[q] as int] == rs[q] && ends@[sel_of@[q] as int] == rs[q + 1] by {
                    if q == t {
                        assert(sel_of@[q] == MAX_SEL);
                    }
                }
                assert forall|q: int| 0 <= q < t + 1 implies #[trigger] sel_of@[q] < starts@.len() || sel_of@[q] == MAX_SEL by {
                    if q < t {
                        assert(so0[q] < st0.len() || so0[q] == MAX_SEL);
                    }
                }
            }
        }
        t = t + 1;
    }
    proof {
        let ns = starts@.len() as int;
        assert forall|q: int| 0 <= q < nruns(rs) && #[trigger] sel_of@[q] >= ns implies one_group(v, p, rs[q] as int, rs[q + 1] as int, 7) by {
            assert(sel_of@[q] < ns || sel_of@[q] == MAX_SEL);
        }
    }
    Some((starts, ends, gids, sel_of))
}

// ------------------------------------------------------------------------------------------------ windows

/// The first position of `lo .. hi` whose row is at least `x` when the rows ascend there (binary search); any
/// position of `lo ..= hi` otherwise.
fn first_ge(perm: &[u32], lo: usize, hi: usize, x: usize) -> (j: usize)
    requires lo <= hi <= perm@.len(),
    ensures lo <= j <= hi,
{
    let mut a = lo;
    let mut b = hi;
    while a < b
        invariant lo <= a <= b <= hi, hi <= perm@.len(),
        decreases b - a,
    {
        let m = a + (b - a) / 2;
        if (perm[m] as usize) < x {
            a = m + 1;
        } else {
            b = m;
        }
    }
    a
}

/// Per selected run, `k + 1` task boundaries from its start to its end: boundary `t` is the run's first position
/// whose row is at least `rb[t]` (clamped to stay monotone), so task `t` takes the rows `rb[t] .. rb[t + 1]`.
pub fn make_table(perm: &[u32], starts: &Vec<usize>, ends: &Vec<usize>, rb: &Vec<usize>, k: usize, Ghost(n): Ghost<int>)
    -> (bt: Vec<Vec<usize>>)
    requires
        starts@.len() == ends@.len(),
        perm@.len() == n,
        forall|s: int| 0 <= s < starts@.len() ==> #[trigger] starts@[s] <= ends@[s] <= n,
        k >= 1,
        rb@.len() == k + 1,
    ensures
        bt_ok(bt@, starts@.len() as int, k as int, n),
        forall|s: int| 0 <= s < starts@.len() ==> (#[trigger] bt@[s])@[0] == starts@[s] && bt@[s]@[k as int] == ends@[s],
{
    let ns = starts.len();
    let nw = k;
    let mut bt: Vec<Vec<usize>> = Vec::new();
    let mut s: usize = 0;
    while s < ns
        invariant
            ns == starts@.len(), ns == ends@.len(), nw == k, nw >= 1, s <= ns, perm@.len() == n, rb@.len() == k + 1,
            forall|s2: int| 0 <= s2 < ns ==> #[trigger] starts@[s2] <= ends@[s2] <= n,
            bt_ok(bt@, s as int, nw as int, n),
            forall|s2: int| 0 <= s2 < s ==> (#[trigger] bt@[s2])@[0] == starts@[s2] && bt@[s2]@[nw as int] == ends@[s2],
        decreases ns - s,
    {
        let lo = starts[s];
        let hi = ends[s];
        let mut row: Vec<usize> = Vec::new();
        row.push(lo);
        let mut prev = lo;
        let mut w: usize = 1;
        while w < nw
            invariant
                1 <= w <= nw, nw == k, rb@.len() == k + 1, lo <= prev <= hi, lo == starts@[s as int], hi == ends@[s as int],
                hi <= n, perm@.len() == n,
                row@.len() == w, row@[0] == lo, row@[w - 1] == prev,
                forall|x: int| 0 <= x < w - 1 ==> #[trigger] row@[x] <= row@[x + 1],
            decreases nw - w,
        {
            let x = first_ge(perm, lo, hi, rb[w]);
            let y = if x < prev { prev } else { x };
            row.push(y);
            prev = y;
            w = w + 1;
        }
        row.push(hi);
        let ghost b0 = bt@;
        bt.push(row);
        proof {
            assert forall|s2: int, x: int| 0 <= s2 < s + 1 && 0 <= x < nw implies #[trigger] bt@[s2]@[x] <= bt@[s2]@[x + 1] by {
                if s2 < s {
                    assert(bt@[s2] == b0[s2]);
                }
            }
            assert forall|s2: int| 0 <= s2 < s + 1 implies (#[trigger] bt@[s2])@.len() == nw + 1 by {
                if s2 < s {
                    assert(bt@[s2] == b0[s2]);
                }
            }
            assert forall|s2: int| 0 <= s2 < s + 1 implies (#[trigger] bt@[s2])@[nw as int] <= n by {
                if s2 < s {
                    assert(bt@[s2] == b0[s2]);
                }
            }
            assert forall|s2: int| 0 <= s2 < s + 1 implies (#[trigger] bt@[s2])@[0] == starts@[s2] && bt@[s2]@[nw as int] == ends@[s2] by {
                if s2 < s {
                    assert(bt@[s2] == b0[s2]);
                }
            }
        }
        s = s + 1;
    }
    bt
}

/// The bounds `0, 1, .., k` (task `t` takes table column range `t .. t + 1`).
fn unit_bounds(k: usize) -> (b: Vec<usize>)
    ensures bounds_ok(b@, k as int, k as int),
{
    let mut b: Vec<usize> = Vec::new();
    b.push(0);
    let mut t: usize = 0;
    while t < k
        invariant
            t <= k, b@.len() == t + 1,
            forall|x: int| 0 <= x <= t ==> #[trigger] b@[x] == x,
        decreases k - t,
    {
        t = t + 1;
        b.push(t);
    }
    b
}

// ------------------------------------------------------------------------------------------------ band

/// Positions sampled per selected run for the band estimate, and in total.
pub const SAMPLE_RUN: usize = 4096;
pub const SAMPLE_MAX: usize = 65536;

/// The lower end `bl` of the listed balances: the mean positive balance of the first positions of every selected
/// run, minus a 32nd of it and 2.00. Only a guess: any `bl` is correct, one above the average costs a second kernel
/// pass (`i64::MIN` when nothing is sampled).
pub fn estimate_bl(perm: &[u32], ac: &[u32], ab: &[i64], starts: &Vec<usize>, ends: &Vec<usize>, Ghost(v): Ghost<Cv>)
    -> (bl: i64)
    requires
        cv_ok(v),
        v.ac == ac@, v.ab == ab@, v.bs == 65536,
        perm@.len() == v.n,
        rows_in(v, perm@, 0, v.n),
        starts@.len() == ends@.len(),
        forall|s: int| 0 <= s < starts@.len() ==> #[trigger] starts@[s] <= ends@[s] <= v.n,
{
    let mut c: u64 = 0;
    let mut sm: i128 = 0;
    let mut taken: usize = 0;
    let mut s: usize = 0;
    while s < starts.len() && taken < SAMPLE_MAX
        invariant
            cv_ok(v), v.ac == ac@, v.ab == ab@, v.bs == 65536, perm@.len() == v.n, rows_in(v, perm@, 0, v.n),
            starts@.len() == ends@.len(),
            forall|s2: int| 0 <= s2 < starts@.len() ==> #[trigger] starts@[s2] <= ends@[s2] <= v.n,
            c <= taken <= SAMPLE_MAX,
            -(c as int) * acct_bound() <= sm <= (c as int) * acct_bound(),
        decreases starts@.len() - s,
    {
        let lo = starts[s];
        let hi0 = ends[s];
        let hi = if hi0 - lo > SAMPLE_RUN { lo + SAMPLE_RUN } else { hi0 };
        let mut j = lo;
        while j < hi && taken < SAMPLE_MAX
            invariant
                cv_ok(v), v.ac == ac@, v.ab == ab@, v.bs == 65536, perm@.len() == v.n, rows_in(v, perm@, 0, v.n),
                lo <= j <= hi <= v.n,
                c <= taken <= SAMPLE_MAX,
                -(c as int) * acct_bound() <= sm <= (c as int) * acct_bound(),
            decreases hi - j,
        {
            let r = perm[j] as usize;
            proof {
                assert(perm@[j as int] < v.n);
                assert((r >> 16) == r / 65536) by (bit_vector);
                assert(-acct_bound() < racct(v, r as int) < acct_bound());
            }
            let a: i64 = ab[r >> 16] + ac[r] as i64;
            if a > 0 {
                sm = sm + a as i128;
                c = c + 1;
            }
            taken = taken + 1;
            j = j + 1;
        }
        s = s + 1;
    }
    if c == 0 {
        return i64::MIN;
    }
    let est: i128 = sm / (c as i128);
    let lo: i128 = est - (if est < 0 { -est } else { est }) / 32 - 200;
    if lo < i64::MIN as i128 { i64::MIN } else if lo > i64::MAX as i128 { i64::MAX } else { lo as i64 }
}

// ------------------------------------------------------------------------------------------------ the kernel

/// The joined outputs: task `t` covered positions `bt[s][wb[t]] .. bt[s][wb[t + 1]]` of every selected run `s`.
pub open spec fn outs_ok(v: Cv, p: Seq<u32>, bt: Seq<Vec<usize>>, ns: int, k: int, wb: Seq<usize>,
    bases: Seq<Arc<Vec<usize>>>, outs: Seq<FOut>, bl: int) -> bool {
    &&& outs.len() == k && bases.len() == k
    &&& forall|t: int| 0 <= t < k ==> (#[trigger] outs[t]).acnt@.len() == ns && outs[t].asum@.len() == ns
            && outs[t].kcnt@.len() == ns && bases[t]@.len() == ns + 1
    &&& forall|t: int, s: int| 0 <= t < k && 0 <= s < ns ==> #[trigger] run_ok(v, p, outs[t].acnt@, outs[t].asum@,
            outs[t].kcnt@, outs[t].buf@, bases[t]@, s, bt[s]@[wb[t] as int] as int, bt[s]@[wb[t + 1] as int] as int, bl as int)
    &&& forall|t: int, s: int| 0 <= t < k && 0 <= s < ns ==>
            bases[t]@[s] + (#[trigger] outs[t].kcnt@[s]) <= outs[t].buf@.len()
}

/// Positions of run `s` in windows `wl .. wh`.
pub open spec fn wsize(bt: Seq<Vec<usize>>, wl: int, wh: int) -> spec_fn(int) -> int {
    |s: int| bt[s]@[wh] - bt[s]@[wl]
}

/// The region starts of one task's buffer (`None` on overflow).
fn task_base(btv: &Vec<Vec<usize>>, ns: usize, nw: usize, wl: usize, wh: usize, Ghost(n): Ghost<int>)
    -> (r: Option<Vec<usize>>)
    requires bt_ok(btv@, ns as int, nw as int, n), wl <= wh <= nw,
    ensures
        r matches Some(b) ==> {
            &&& b@.len() == ns + 1
            &&& b@[0] == 0
            &&& forall|s: int| 0 <= s < ns ==> 0 <= #[trigger] wsize(btv@, wl as int, wh as int)(s)
                    && b@[s] + wsize(btv@, wl as int, wh as int)(s) == b@[s + 1]
        },
{
    let ghost sizes = wsize(btv@, wl as int, wh as int);
    let mut base: Vec<usize> = Vec::new();
    base.push(0);
    let mut cur: usize = 0;
    let mut s: usize = 0;
    while s < ns
        invariant
            bt_ok(btv@, ns as int, nw as int, n),
            wl <= wh <= nw, s <= ns,
            sizes == wsize(btv@, wl as int, wh as int),
            base@.len() == s + 1, base@[0] == 0, base@[s as int] == cur,
            forall|s2: int| 0 <= s2 < s ==> 0 <= #[trigger] sizes(s2) && base@[s2] + sizes(s2) == base@[s2 + 1],
        decreases ns - s,
    {
        let row: &Vec<usize> = &btv[s];
        proof {
            lemma_bt_mono(btv@, ns as int, nw as int, n, s as int, wl as int, wh as int);
            assert(row@ == btv@[s as int]@);
        }
        let sz = row[wh] - row[wl];
        if sz > usize::MAX - cur {
            return None;
        }
        cur = cur + sz;
        let ghost b0 = base@;
        base.push(cur);
        proof {
            assert forall|s2: int| 0 <= s2 < s + 1 implies 0 <= #[trigger] sizes(s2) && base@[s2] + sizes(s2) == base@[s2 + 1] by {
                if s2 < s {
                    assert(base@[s2] == b0[s2] && base@[s2 + 1] == b0[s2 + 1]);
                }
            }
        }
        s = s + 1;
    }
    Some(base)
}

/// The joined outputs of the tasks meet `outs_ok`.
proof fn lemma_joined(v: Cv, p: Seq<u32>, bt: Seq<Vec<usize>>, ns: int, nw: int, k: int, wb: Seq<usize>,
    bases: Seq<Arc<Vec<usize>>>, tv: Seq<TaskF>, outs: Seq<FOut>, bl: int)
    requires
        bt_ok(bt, ns, nw, v.n),
        tv.len() == k, outs.len() == k, bases.len() == k,
        forall|q: int| 0 <= q < k ==> (#[trigger] tv[q]).pre() && tv[q].post(outs[q]),
        forall|q: int| 0 <= q < k ==> (#[trigger] tv[q]).v@ == v && tv[q].perm@ == p && tv[q].bt@ == bt
            && tv[q].ns == ns && tv[q].w_lo == wb[q] && tv[q].w_hi == wb[q + 1] && tv[q].base@ == bases[q]@
            && tv[q].bl == bl,
    ensures
        outs_ok(v, p, bt, ns, k, wb, bases, outs, bl),
{
    assert forall|q: int| 0 <= q < k implies (#[trigger] outs[q]).acnt@.len() == ns && outs[q].asum@.len() == ns
        && outs[q].kcnt@.len() == ns && bases[q]@.len() == ns + 1 by {
        assert(tv[q].pre() && tv[q].post(outs[q]));
    }
    assert forall|q: int, s: int| 0 <= q < k && 0 <= s < ns implies #[trigger] run_ok(v, p, outs[q].acnt@, outs[q].asum@,
        outs[q].kcnt@, outs[q].buf@, bases[q]@, s, bt[s]@[wb[q] as int] as int, bt[s]@[wb[q + 1] as int] as int, bl) by {
        assert(tv[q].post(outs[q]));
        assert(run_ok(v, p, outs[q].acnt@, outs[q].asum@, outs[q].kcnt@, outs[q].buf@, tv[q].base@, s,
            lo_of(tv[q], s), hi_of(tv[q], s), bl));
    }
    assert forall|q: int, s: int| 0 <= q < k && 0 <= s < ns implies
        bases[q]@[s] + (#[trigger] outs[q].kcnt@[s]) <= outs[q].buf@.len() by {
        let tk = tv[q];
        assert(tk.pre() && tk.post(outs[q]));
        assert(run_ok(v, p, outs[q].acnt@, outs[q].asum@, outs[q].kcnt@, outs[q].buf@, tk.base@, s,
            lo_of(tk, s), hi_of(tk, s), bl));
        lemma_bt_mono(bt, ns, nw, v.n, s, tk.w_lo as int, tk.w_hi as int);
        lemma_t_bound(v, p, lo_of(tk, s), hi_of(tk, s), bl);
        assert(0 <= size_of(tk)(s) && tk.base@[s] + size_of(tk)(s) <= tk.base@[s + 1]);
        lemma_base_mono(tk.base@, ns, size_of(tk), tk.out.buf@.len() as int, s + 1, ns);
    }
}

/// The fused kernel over `k` tasks; `None` when a task's buffer size would overflow.
pub fn run_fused(perm: &'static [u32], ac: &'static [u32], ab: &'static [i64], offs: &'static [u32], d: usize, nk: usize,
    bl: i64, bt: &Arc<Vec<Vec<usize>>>, ns: usize, nw: usize, k: usize, rb: &Vec<usize>, dispatch: &mut Dispatch,
    Ghost(v): Ghost<Cv>)
    -> (r: Result<Option<(Vec<FOut>, Vec<Arc<Vec<usize>>>, Vec<usize>)>, WorkerFailure>)
    requires
        kern_ok(v, perm@, ac@, ab@, offs@, d as int, nk as int),
        bt_ok(bt@, ns as int, nw as int, v.n),
        1 <= k <= MAX_WORKERS,
        nw == k,
        bounds_ok(rb@, k as int, v.n),
    ensures
        r matches Ok(Some(x)) ==> bounds_ok(x.2@, k as int, nw as int) && outs_ok(v, perm@, bt@, ns as int, k as int, x.2@, x.1@, x.0@, bl as int),
{
    let ghost p = perm@;
    let wb = unit_bounds(k);
    let btv: &Vec<Vec<usize>> = &*bt;
    let mut tasks: Vec<TaskF> = Vec::new();
    let mut bases: Vec<Arc<Vec<usize>>> = Vec::new();
    let mut t: usize = 0;
    while t < k
        invariant
            kern_ok(v, p, ac@, ab@, offs@, d as int, nk as int), p == perm@,
            bt_ok(bt@, ns as int, nw as int, v.n), btv@ == bt@,
            1 <= k <= MAX_WORKERS, nw == k,
            bounds_ok(wb@, k as int, nw as int),
            bounds_ok(rb@, k as int, v.n),
            t <= k,
            tasks@.len() == t, bases@.len() == t,
            forall|q: int| 0 <= q < t ==> (#[trigger] tasks@[q]).pre(),
            forall|q: int| 0 <= q < t ==> (#[trigger] tasks@[q]).v@ == v && tasks@[q].perm@ == p && tasks@[q].bt@ == bt@
                && tasks@[q].ns == ns && tasks@[q].w_lo == wb@[q] && tasks@[q].w_hi == wb@[q + 1]
                && tasks@[q].base@ == bases@[q]@ && tasks@[q].bl == bl,
        decreases k - t,
    {
        proof {
            lemma_bounds_le(wb@, k as int, nw as int, t as int);
            lemma_bounds_le(rb@, k as int, v.n, t as int);
        }
        let (wl, wh) = (wb[t], wb[t + 1]);
        let (rl, rh) = (rb[t], rb[t + 1]);
        let base = match task_base(btv, ns, nw, wl, wh, Ghost(v.n)) {
            Some(b) => b,
            None => return Ok(None),
        };
        let total = base[ns];
        let buf: Vec<i64> = vec![0i64; total];
        let acnt: Vec<u64> = vec![0u64; ns];
        let asum: Vec<i128> = vec![0i128; ns];
        let kcnt: Vec<usize> = vec![0usize; ns];
        let cur: Vec<usize> = vec![0usize; ns];
        let base = Arc::new(base);
        let task = TaskF {
            perm, ac, ab, offs, d, nk, bl, bt: bt.clone(), ns, nw, w_lo: wl, w_hi: wh, row_lo: rl, row_hi: rh,
            base: base.clone(), cur, out: FOut { acnt, asum, kcnt, buf, touched: 0 }, v: Ghost(v),
        };
        proof {
            let sizes = wsize(bt@, wl as int, wh as int);
            assert(size_of(task) =~= sizes) by {
                assert forall|s2: int| #[trigger] size_of(task)(s2) == sizes(s2) by {}
            }
            assert forall|s2: int| 0 <= s2 < ns implies 0 <= #[trigger] size_of(task)(s2)
                && task.base@[s2] + size_of(task)(s2) <= task.base@[s2 + 1] by {
                assert(sizes(s2) == size_of(task)(s2));
            }
            assert(regions_ok(task.base@, ns as int, size_of(task), task.out.buf@.len() as int));
            assert(task_fresh(task));
        }
        tasks.push(task);
        bases.push(base);
        t = t + 1;
    }
    let ghost tv = tasks@;
    let outs = if k == 1 {
        // One task: it runs on the calling thread (no worker thread to start).
        let mut tasks = tasks;
        let t0 = tasks.pop().unwrap();
        proof {
            assert(t0 == tv[0]);
        }
        let o0 = t0.run();
        let mut o: Vec<FOut> = Vec::new();
        o.push(o0);
        o
    } else {
        match fork_join(dispatch, tasks) {
            Ok(o) => o,
            Err(f) => return Err(f),
        }
    };
    proof {
        assert forall|q: int| 0 <= q < k implies #[trigger] tv[q].pre() && tv[q].post(outs@[q]) by {}
        lemma_joined(v, p, bt@, ns as int, nw as int, k as int, wb@, bases@, tv, outs@, bl as int);
    }
    Ok(Some((outs, bases, wb)))
}

/// The facts the merges share.
pub open spec fn merge_ok(v: Cv, p: Seq<u32>, rs: Seq<u64>, starts: Seq<usize>, ends: Seq<usize>, gids: Seq<usize>,
    sel_of: Seq<usize>, bt: Seq<Vec<usize>>, ns: int, nw: int, k: int, wb: Seq<usize>, bases: Seq<Arc<Vec<usize>>>,
    outs: Seq<FOut>, bl: int) -> bool {
    &&& cv_ok(v)
    &&& corder_ok(v, p, rs)
    &&& sel_ok(v, p, rs, starts, ends, gids, sel_of)
    &&& ns == starts.len()
    &&& bt_ok(bt, ns, nw, v.n)
    &&& forall|s: int| 0 <= s < ns ==> (#[trigger] bt[s])@[0] == starts[s] && bt[s]@[nw] == ends[s]
    &&& bounds_ok(wb, k, nw)
    &&& outs_ok(v, p, bt, ns, k, wb, bases, outs, bl)
}

// ------------------------------------------------------------------------------------------------ pass A

/// Run `s`'s positive balances over all tasks: `tpc`/`tps` over its positions `starts[s] .. ends[s]`.
fn total_a(outs: &Vec<FOut>, k: usize, wb: &Vec<usize>, bt: &Vec<Vec<usize>>, ns: usize, nw: usize, s: usize,
    bl: i64, Ghost(v): Ghost<Cv>, Ghost(p): Ghost<Seq<u32>>, Ghost(bases): Ghost<Seq<Arc<Vec<usize>>>>,
    Ghost(lo): Ghost<int>, Ghost(hi): Ghost<int>) -> (r: (u64, i128))
    requires
        cv_ok(v),
        rows_in(v, p, 0, v.n),
        bt_ok(bt@, ns as int, nw as int, v.n),
        s < ns,
        bt@[s as int]@[0] == lo, bt@[s as int]@[nw as int] == hi,
        bounds_ok(wb@, k as int, nw as int),
        outs_ok(v, p, bt@, ns as int, k as int, wb@, bases, outs@, bl as int),
    ensures
        r.0 == tpc(v, p, lo, hi),
        r.1 == tps(v, p, lo, hi),
{
    let ghost si = s as int;
    let mut c: u64 = 0;
    let mut sm: i128 = 0;
    let mut t: usize = 0;
    while t < k
        invariant
            cv_ok(v), rows_in(v, p, 0, v.n),
            bt_ok(bt@, ns as int, nw as int, v.n),
            s < ns, si == s,
            bt@[si]@[0] == lo, bt@[si]@[nw as int] == hi,
            bounds_ok(wb@, k as int, nw as int),
            outs_ok(v, p, bt@, ns as int, k as int, wb@, bases, outs@, bl as int),
            t <= k,
            c == tpc(v, p, lo, bt@[si]@[wb@[t as int] as int] as int),
            sm == tps(v, p, lo, bt@[si]@[wb@[t as int] as int] as int),
        decreases k - t,
    {
        let ghost ti = t as int;
        proof {
            lemma_bounds_le(wb@, k as int, nw as int, ti);
            let (x, y) = (bt@[si]@[wb@[ti] as int] as int, bt@[si]@[wb@[ti + 1] as int] as int);
            lemma_bt_mono(bt@, ns as int, nw as int, v.n, si, 0, wb@[ti] as int);
            lemma_bt_mono(bt@, ns as int, nw as int, v.n, si, wb@[ti] as int, wb@[ti + 1] as int);
            assert(outs@[ti].acnt@.len() == ns);
            assert(run_ok(v, p, outs@[ti].acnt@, outs@[ti].asum@, outs@[ti].kcnt@, outs@[ti].buf@, bases[ti]@, si, x, y, bl as int));
            lemma_t_split(v, p, lo, x, y, bl as int);
            lemma_t_bound(v, p, lo, y, bl as int);
            let cc = tpc(v, p, lo, y) as int;
            assert(cc * acct_bound() <= 0x1_0000_0000_0000_0000 * acct_bound()) by (nonlinear_arith)
                requires 0 <= cc <= 0x1_0000_0000_0000_0000;
        }
        let o: &FOut = &outs[t];
        c = c + o.acnt[s];
        sm = sm + o.asum[s];
        t = t + 1;
    }
    proof {
        assert(wb@[k as int] == nw);
    }
    (c, sm)
}

/// Pass A from the kernel's outputs: the count and sum of the subquery's rows over `[0, n)`.
pub fn combine_a(outs: &Vec<FOut>, k: usize, wb: &Vec<usize>, bases: &Vec<Arc<Vec<usize>>>, bt: &Vec<Vec<usize>>,
    ns: usize, nw: usize, bl: i64, starts: &Vec<usize>, ends: &Vec<usize>, gids: &Vec<usize>, sel_of: &Vec<usize>,
    runs: &[u64], Ghost(v): Ghost<Cv>, Ghost(p): Ghost<Seq<u32>>) -> (r: (i128, u64))
    requires
        merge_ok(v, p, runs@, starts@, ends@, gids@, sel_of@, bt@, ns as int, nw as int, k as int, wb@, bases@, outs@, bl as int),
    ensures
        r.0 == suma(v, 0, v.n),
        r.1 == cnta(v, 0, v.n),
{
    let ghost rs = runs@;
    // Per selected run: the positive balances over all tasks.
    let mut tc: Vec<u64> = Vec::new();
    let mut ts: Vec<i128> = Vec::new();
    let mut s: usize = 0;
    while s < ns
        invariant
            merge_ok(v, p, rs, starts@, ends@, gids@, sel_of@, bt@, ns as int, nw as int, k as int, wb@, bases@, outs@, bl as int),
            rs == runs@,
            s <= ns, tc@.len() == s, ts@.len() == s,
            forall|s2: int| 0 <= s2 < s ==> #[trigger] tc@[s2] == tpc(v, p, starts@[s2] as int, ends@[s2] as int)
                && ts@[s2] == tps(v, p, starts@[s2] as int, ends@[s2] as int),
        decreases ns - s,
    {
        let (c, sm) = total_a(outs, k, wb, bt, ns, nw, s, bl, Ghost(v), Ghost(p), Ghost(bases@),
            Ghost(starts@[s as int] as int), Ghost(ends@[s as int] as int));
        tc.push(c);
        ts.push(sm);
        s = s + 1;
    }
    // Over every run of the order, in order.
    let m = runs.len() - 1;
    let mut cnt: u64 = 0;
    let mut sum: i128 = 0;
    let mut t: usize = 0;
    while t < m
        invariant
            cv_ok(v), corder_ok(v, p, rs), rs == runs@, m == nruns(rs),
            sel_ok(v, p, rs, starts@, ends@, gids@, sel_of@), ns == starts@.len(),
            tc@.len() == ns, ts@.len() == ns,
            forall|s2: int| 0 <= s2 < ns ==> #[trigger] tc@[s2] == tpc(v, p, starts@[s2] as int, ends@[s2] as int)
                && ts@[s2] == tps(v, p, starts@[s2] as int, ends@[s2] as int),
            t <= m,
            cnt == pcnta(v, p, 0, rs[t as int] as int),
            sum == psuma(v, p, 0, rs[t as int] as int),
        decreases m - t,
    {
        let ghost (x, y) = (rs[t as int] as int, rs[t + 1] as int);
        proof {
            lemma_rs_bound(v, p, rs, t + 1);
            assert(rs[t as int] < rs[t + 1]);
            lemma_p_split(v, Val::Null, 0, p, 0, x, y);
            lemma_pa_bound(v, p, 0, y);
            let cc = pcnta(v, p, 0, y) as int;
            assert(cc * acct_bound() <= 0x1_0000_0000_0000_0000 * acct_bound()) by (nonlinear_arith)
                requires 0 <= cc <= 0x1_0000_0000_0000_0000;
        }
        let si = sel_of[t];
        if si < ns {
            proof {
                assert(starts@[si as int] == x && ends@[si as int] == y);
                assert(one_group(v, p, x, y, gids@[si as int] as int));
                lemma_run_a(v, p, x, y, gids@[si as int] as int);
            }
            cnt = cnt + tc[si];
            sum = sum + ts[si];
        } else {
            proof {
                lemma_run_a(v, p, x, y, 7);
            }
        }
        t = t + 1;
    }
    proof {
        lemma_reindex_a(v, p, v.n);
    }
    (sum, cnt)
}

// ------------------------------------------------------------------------------------------------ pass B

/// One task's candidates of run `s` (`kc` slots of `buf` from `b0`, the list `piece`), added to `cnt_gt`/`sum_gt`
/// of `prev`.
fn region_gt(buf: &Vec<i64>, b0: usize, kc: usize, thr: i128, c0: u64, s0: i128, Ghost(prev): Ghost<Seq<int>>,
    Ghost(piece): Ghost<Seq<int>>, Ghost(n): Ghost<int>) -> (r: (u64, i128))
    requires
        b0 + kc <= buf@.len(),
        piece.len() == kc,
        forall|q: int| 0 <= q < kc ==> #[trigger] buf@[b0 + q] as int == piece[q],
        forall|q: int| 0 <= q < (prev + piece).len() ==> -acct_bound() < #[trigger] (prev + piece)[q] < acct_bound(),
        (prev + piece).len() <= n < 0x1_0000_0000_0000_0000,
        c0 == cnt_gt(prev, thr as int),
        s0 == sum_gt(prev, thr as int),
    ensures
        r.0 == cnt_gt(prev + piece, thr as int),
        r.1 == sum_gt(prev + piece, thr as int),
{
    let ghost th = thr as int;
    let blen = buf.len();
    let mut c = c0;
    let mut sm = s0;
    let mut q: usize = 0;
    proof {
        assert(prev + piece.subrange(0, 0) =~= prev);
    }
    while q < kc
        invariant
            b0 + kc <= buf@.len(), blen == buf@.len(),
            piece.len() == kc, q <= kc,
            forall|q2: int| 0 <= q2 < kc ==> #[trigger] buf@[b0 + q2] as int == piece[q2],
            forall|q2: int| 0 <= q2 < (prev + piece).len() ==> -acct_bound() < #[trigger] (prev + piece)[q2] < acct_bound(),
            (prev + piece).len() <= n < 0x1_0000_0000_0000_0000,
            th == thr as int,
            c == cnt_gt(prev + piece.subrange(0, q as int), th),
            sm == sum_gt(prev + piece.subrange(0, q as int), th),
        decreases kc - q,
    {
        let ghost qi = q as int;
        let a = buf[b0 + q];
        proof {
            assert(a as int == piece[qi]);
            let all = prev + piece.subrange(0, qi + 1);
            assert(all =~= (prev + piece.subrange(0, qi)).push(piece[qi]));
            lemma_gt_push(prev + piece.subrange(0, qi), piece[qi], th);
            assert forall|q2: int| 0 <= q2 < all.len() implies -acct_bound() < #[trigger] all[q2] < acct_bound() by {
                assert(all[q2] == (prev + piece)[q2]);
            }
            lemma_gt_bound(all, th);
            let cc = cnt_gt(all, th) as int;
            assert(cc * acct_bound() <= 0x1_0000_0000_0000_0000 * acct_bound()) by (nonlinear_arith)
                requires 0 <= cc <= 0x1_0000_0000_0000_0000;
        }
        let gt = a as i128 > thr;
        c = c + if gt { 1u64 } else { 0u64 };
        sm = sm + if gt { a as i128 } else { 0i128 };
        q = q + 1;
    }
    proof {
        assert(piece.subrange(0, kc as int) =~= piece);
    }
    (c, sm)
}

/// Run `s`'s candidates above the threshold over all tasks (`pcgt`/`psgt` over its positions): the listed balances
/// above it (`region_gt`), the threshold being at least `bl` (`lemma_band`).
fn total_b(outs: &Vec<FOut>, k: usize, wb: &Vec<usize>, bases: &Vec<Arc<Vec<usize>>>, bt: &Vec<Vec<usize>>, ns: usize,
    nw: usize, s: usize, bl: i64, thr: i128, Ghost(v): Ghost<Cv>, Ghost(p): Ghost<Seq<u32>>, Ghost(lo): Ghost<int>,
    Ghost(hi): Ghost<int>) -> (r: (u64, i128))
    requires
        cv_ok(v),
        rows_in(v, p, 0, v.n),
        bt_ok(bt@, ns as int, nw as int, v.n),
        s < ns,
        bt@[s as int]@[0] == lo, bt@[s as int]@[nw as int] == hi,
        bounds_ok(wb@, k as int, nw as int),
        outs_ok(v, p, bt@, ns as int, k as int, wb@, bases@, outs@, bl as int),
        bl as int <= thr as int,
    ensures
        r.0 == pcgt(v, p, lo, hi, thr as int),
        r.1 == psgt(v, p, lo, hi, thr as int),
{
    let ghost si = s as int;
    let ghost th = thr as int;
    let mut c: u64 = 0;
    let mut sm: i128 = 0;
    let mut t: usize = 0;
    while t < k
        invariant
            cv_ok(v), rows_in(v, p, 0, v.n),
            bt_ok(bt@, ns as int, nw as int, v.n),
            s < ns, si == s, th == thr as int, bl as int <= th,
            bt@[si]@[0] == lo, bt@[si]@[nw as int] == hi,
            bounds_ok(wb@, k as int, nw as int),
            outs_ok(v, p, bt@, ns as int, k as int, wb@, bases@, outs@, bl as int),
            t <= k,
            c == cnt_gt(pband(v, p, lo, bt@[si]@[wb@[t as int] as int] as int, bl as int), th),
            sm == sum_gt(pband(v, p, lo, bt@[si]@[wb@[t as int] as int] as int, bl as int), th),
        decreases k - t,
    {
        let ghost ti = t as int;
        proof {
            lemma_bounds_le(wb@, k as int, nw as int, ti);
            lemma_bt_mono(bt@, ns as int, nw as int, v.n, si, 0, wb@[ti] as int);
            lemma_bt_mono(bt@, ns as int, nw as int, v.n, si, wb@[ti] as int, wb@[ti + 1] as int);
        }
        let ghost (x, y) = (bt@[si]@[wb@[ti] as int] as int, bt@[si]@[wb@[ti + 1] as int] as int);
        let o: &FOut = &outs[t];
        let bv: &Vec<usize> = &*bases[t];
        proof {
            assert(outs@[ti].acnt@.len() == ns && bases@[ti]@.len() == ns + 1);
            assert(run_ok(v, p, o.acnt@, o.asum@, o.kcnt@, o.buf@, bv@, si, x, y, bl as int));
            assert(bv@[si] + o.kcnt@[si] <= o.buf@.len());
            lemma_t_split(v, p, lo, x, y, bl as int);
            lemma_t_bound(v, p, lo, y, bl as int);
        }
        let b0 = bv[s];
        let kc = o.kcnt[s];
        let ghost piece = pband(v, p, x, y, bl as int);
        proof {
            assert forall|q: int| 0 <= q < kc implies #[trigger] o.buf@[b0 + q] as int == piece[q] by {
                assert(cand_at(o.buf@, bv@, si, q) == piece[q]);
            }
        }
        let (c2, s2) = region_gt(&o.buf, b0, kc, thr, c, sm, Ghost(pband(v, p, lo, x, bl as int)), Ghost(piece), Ghost(v.n));
        c = c2;
        sm = s2;
        t = t + 1;
    }
    proof {
        assert(wb@[k as int] == nw);
        lemma_band(v, p, lo, hi, bl as int, th);
    }
    (c, sm)
}

/// Pass B from the kernel's outputs: per group, the count and sum of the result rows over `[0, n)`.
pub fn finish_b(outs: &Vec<FOut>, k: usize, wb: &Vec<usize>, bases: &Vec<Arc<Vec<usize>>>, bt: &Vec<Vec<usize>>,
    ns: usize, nw: usize, bl: i64, starts: &Vec<usize>, ends: &Vec<usize>, gids: &Vec<usize>, sel_of: &Vec<usize>,
    runs: &[u64], thr: i128, Ghost(v): Ghost<Cv>, Ghost(p): Ghost<Seq<u32>>, Ghost(avg): Ghost<Val>)
    -> (r: (Vec<u64>, Vec<i128>))
    requires
        merge_ok(v, p, runs@, starts@, ends@, gids@, sel_of@, bt@, ns as int, nw as int, k as int, wb@, bases@, outs@, bl as int),
        thr_ok(thr, avg),
        bl as int <= thr as int,
    ensures
        post_b(v, avg, 0, v.n, r.0@, r.1@),
{
    let ghost rs = runs@;
    let ghost th = thr as int;
    proof {
        assert forall|a: int| -acct_bound() < a < acct_bound() implies #[trigger] gt_avg(a, avg) == (a > th) by {
            assert(gt_avg(a, avg) == (a > thr));
        }
        assert(thr_of(th, avg));
    }
    // Per selected run: its candidates above the threshold over all tasks.
    let mut tc: Vec<u64> = Vec::new();
    let mut ts: Vec<i128> = Vec::new();
    let mut s: usize = 0;
    while s < ns
        invariant
            merge_ok(v, p, rs, starts@, ends@, gids@, sel_of@, bt@, ns as int, nw as int, k as int, wb@, bases@, outs@, bl as int),
            rs == runs@, th == thr as int, bl as int <= th,
            s <= ns, tc@.len() == s, ts@.len() == s,
            forall|s2: int| 0 <= s2 < s ==> #[trigger] tc@[s2] == pcgt(v, p, starts@[s2] as int, ends@[s2] as int, th)
                && ts@[s2] == psgt(v, p, starts@[s2] as int, ends@[s2] as int, th),
        decreases ns - s,
    {
        let (c, sm) = total_b(outs, k, wb, bases, bt, ns, nw, s, bl, thr, Ghost(v), Ghost(p),
            Ghost(starts@[s as int] as int), Ghost(ends@[s as int] as int));
        tc.push(c);
        ts.push(sm);
        s = s + 1;
    }
    // Over every run of the order, into the run's group.
    let m = runs.len() - 1;
    let mut cnts: Vec<u64> = vec![0u64; 7];
    let mut sums: Vec<i128> = vec![0i128; 7];
    let mut t: usize = 0;
    while t < m
        invariant
            cv_ok(v), corder_ok(v, p, rs), rs == runs@, m == nruns(rs),
            sel_ok(v, p, rs, starts@, ends@, gids@, sel_of@), ns == starts@.len(),
            thr_of(th, avg),
            tc@.len() == ns, ts@.len() == ns,
            forall|s2: int| 0 <= s2 < ns ==> #[trigger] tc@[s2] == pcgt(v, p, starts@[s2] as int, ends@[s2] as int, th)
                && ts@[s2] == psgt(v, p, starts@[s2] as int, ends@[s2] as int, th),
            t <= m,
            cnts@.len() == 7, sums@.len() == 7,
            forall|g: int| 0 <= g < 7 ==> #[trigger] cnts@[g] == pcntb(v, avg, g, p, 0, rs[t as int] as int)
                && sums@[g] == psumb(v, avg, g, p, 0, rs[t as int] as int),
        decreases m - t,
    {
        let ghost (x, y) = (rs[t as int] as int, rs[t + 1] as int);
        proof {
            lemma_rs_bound(v, p, rs, t + 1);
            assert(rs[t as int] < rs[t + 1]);
            assert forall|g: int| 0 <= g < 7 implies #[trigger] pcntb(v, avg, g, p, 0, y)
                == pcntb(v, avg, g, p, 0, x) + pcntb(v, avg, g, p, x, y)
                && psumb(v, avg, g, p, 0, y) == psumb(v, avg, g, p, 0, x) + psumb(v, avg, g, p, x, y) by {
                lemma_p_split(v, avg, g, p, 0, x, y);
            }
        }
        let si = sel_of[t];
        if si < ns {
            let g = gids[si];
            proof {
                assert(starts@[si as int] == x && ends@[si as int] == y);
                assert(one_group(v, p, x, y, gids@[si as int] as int));
                assert forall|g2: int| 0 <= g2 < 7 implies #[trigger] pcntb(v, avg, g2, p, x, y)
                    == (if g2 == g { pcgt(v, p, x, y, th) } else { 0 })
                    && psumb(v, avg, g2, p, x, y) == (if g2 == g { psgt(v, p, x, y, th) } else { 0 }) by {
                    lemma_run_b(v, avg, th, g2, p, x, y, g as int);
                }
                lemma_pb_bound(v, avg, g as int, p, 0, y);
                let cc = pcntb(v, avg, g as int, p, 0, y) as int;
                assert(cc * acct_bound() <= 0x1_0000_0000_0000_0000 * acct_bound()) by (nonlinear_arith)
                    requires 0 <= cc <= 0x1_0000_0000_0000_0000;
            }
            let nc = cnts[g] + tc[si];
            let nsm = sums[g] + ts[si];
            cnts.set(g, nc);
            sums.set(g, nsm);
        } else {
            proof {
                assert forall|g2: int| 0 <= g2 < 7 implies #[trigger] pcntb(v, avg, g2, p, x, y) == 0
                    && psumb(v, avg, g2, p, x, y) == 0 by {
                    lemma_run_b(v, avg, th, g2, p, x, y, 7);
                }
            }
        }
        t = t + 1;
    }
    proof {
        assert forall|g: int| 0 <= g < 7 implies #[trigger] cnts@[g] == cntb(v, avg, g, 0, v.n) && sums@[g] == sumb(v, avg, g, 0, v.n) by {
            lemma_reindex_b(v, avg, g, p, v.n);
        }
    }
    (cnts, sums)
}

} // verus!
