//! The fast path (`fast_path`): `T` scan tasks (`agent::scan`), then customer tasks over the buckets
//! (`agent::cagg`), then the merge of their top lists.
//!
//! Plan: scan task `t` checks the lineitem pairs of rows `[ls[t], ls[t + 1])` (equal row ranges) and handles the
//! orders `[os[t], os[t + 1])`, where `os[t]` is the first order whose key reaches the first key of lineitem range
//! `t` (a binary search that assumes nothing: any monotone split is correct, a good one balances the work). When all
//! scan tasks succeed, every adjacent pair of `l_orderkey` is in order (`lemma_sorted`), so each task's bucket lists
//! hold exactly its hitting orders with their revenues. The `nb = ceil(nc / CPB)` buckets are then split into
//! `np <= min(workers, 32)` consecutive ranges, one customer task each; each returns a top-`TOPN` list of its customers'
//! groups and has checked its customer keys positional. Offering every list's ids to one buffer gives a top-`TOPN`
//! list of all groups (`common::topn::lemma_top_merge`). With one task a phase runs on the calling thread.
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS, WorkerTask, fork_join};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::link::expr::i128_max;
use crate::agent::cols::*;
use crate::agent::normal::*;
use crate::agent::xcols::*;
use crate::agent::enc::*;
use crate::agent::runs::*;
use crate::agent::scan::*;
use crate::agent::cagg::*;
use crate::agent::answer::*;
use crate::agent::output::{zeros_i64, zeros_usize};
use crate::agent::common::topn::*;

verus! {

/// What the fast path delivers: a top-`TOPN` list of all groups, with their revenues, and every group within the SUM
/// capacity.
pub open spec fn fast_ok(t: Top, sv: StoresView, dlo: int, dhi: int) -> bool {
    &&& t.cap == TOPN && t.k <= t.cap && t.rows@.len() == t.cap && t.vals@.len() == t.cap
    &&& top_of(tsel(t), all_groups(sv, dlo, dhi), cval(sv, dlo, dhi), TOPN as int)
    &&& forall|k: int| 0 <= k < t.k ==> #[trigger] t.vals@[k] as int == ctot(sv, dlo, dhi, t.rows@[k] as int)
    &&& groups_capped(sv, dlo, dhi)
}

/// The first position in `keys[0..n)` whose key is not below `k` (when the keys ascend); any position is sound.
fn lower_bound(keys: &[i64], n: usize, k: i64) -> (r: usize)
    requires n <= keys@.len(),
    ensures r <= n,
{
    let mut lo: usize = 0;
    let mut hi: usize = n;
    while lo < hi
        invariant lo <= hi <= n, n <= keys@.len(),
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        if keys[mid] < k { lo = mid + 1; } else { hi = mid; }
    }
    lo
}

// ------------------------------------------------------------------------------------------------ the scan phase

/// The ranges of the scan tasks: lineitem rows `[ls[t], ls[t + 1])`, orders `[os[t], os[t + 1])`, each covering its
/// table once, in order.
pub open spec fn ranges_ok(sv: StoresView, ls: Seq<int>, os: Seq<int>, t: int) -> bool {
    &&& t >= 1 && ls.len() == t + 1 && os.len() == t + 1
    &&& ls[0] == 0 && ls[t] == n_l(sv) && forall|u: int| 0 <= u < t ==> #[trigger] ls[u] <= ls[u + 1]
    &&& os[0] == 0 && os[t] == n_o(sv) && forall|u: int| 0 <= u < t ==> #[trigger] os[u] <= os[u + 1]
}

/// The rows of `bucket count * rcap` fit: `nb * ((n / (nb * 20)) + 64) <= n / 20 + 64 * nb`.
proof fn lemma_cap_fit(n: int, nb: int, rcap: int)
    requires n >= 0, nb >= 1, rcap == n / (nb * 20) + 64,
    ensures nb * rcap <= n + 64 * nb,
{
    let q = n / (nb * 20);
    assert(q * (nb * 20) <= n) by (nonlinear_arith) requires q == n / (nb * 20), nb >= 1, n >= 0;
    assert(nb * q <= n) by (nonlinear_arith) requires q * (nb * 20) <= n, nb >= 1, q >= 0;
    assert(nb * rcap == nb * q + 64 * nb) by (nonlinear_arith) requires rcap == q + 64;
}

/// The scan tasks of the plan.
fn build_scans(c: &Cols, nt: usize, nb: usize, Ghost(sv): Ghost<StoresView>) -> (r: (Vec<STask>, Ghost<(Seq<int>, Seq<int>)>))
    requires
        cols_ok(*c, sv), 1 <= nt <= MAX_WORKERS, 1 <= nb <= 0x1_0000, c.nc < 0x8000_0000, c.nc <= nb * CPB,
        c.no <= usize::MAX - 0x40_0000,
    ensures ({
        let (tasks, g) = r;
        let (ls, os) = g@;
        &&& ranges_ok(sv, ls, os, nt as int)
        &&& tasks@.len() == nt
        &&& forall|u: int| 0 <= u < nt ==> (#[trigger] tasks@[u]).pre() && tasks@[u].c == *c && tasks@[u].sv@ == sv
            && tasks@[u].lo == ls[u] && tasks@[u].hi == ls[u + 1] && tasks@[u].olo == os[u] && tasks@[u].ohi == os[u + 1]
            && tasks@[u].nb == nb
    }),
{
    let nl = c.nl;
    let no = c.no;
    let lch = nl / nt;
    let mut tasks: Vec<STask> = Vec::new();
    let ghost mut ls: Seq<int> = seq![0int];
    let ghost mut os: Seq<int> = seq![0int];
    let mut prev_o: usize = 0;
    let mut t: usize = 0;
    while t < nt
        invariant
            cols_ok(*c, sv), 1 <= nt <= MAX_WORKERS, 1 <= nb <= 0x1_0000, c.nc < 0x8000_0000, c.nc <= nb * CPB,
            c.no <= usize::MAX - 0x40_0000, nl == c.nl, no == c.no, lch == nl / nt, t <= nt,
            tasks@.len() == t, ls.len() == t + 1, os.len() == t + 1, ls[0] == 0, os[0] == 0,
            t < nt ==> ls[t as int] == t * lch, os[t as int] == prev_o, prev_o <= no,
            t * lch <= nl,
            forall|u: int| 0 <= u < t ==> #[trigger] ls[u] <= ls[u + 1],
            forall|u: int| 0 <= u < t ==> #[trigger] os[u] <= os[u + 1],
            t == nt ==> ls[t as int] == nl && os[t as int] == no,
            forall|u: int| 0 <= u < t ==> (#[trigger] tasks@[u]).pre() && tasks@[u].c == *c && tasks@[u].sv@ == sv
                && tasks@[u].lo == ls[u] && tasks@[u].hi == ls[u + 1] && tasks@[u].olo == os[u] && tasks@[u].ohi == os[u + 1]
                && tasks@[u].nb == nb,
        decreases nt - t,
    {
        proof {
            assert(t * lch <= nl) by (nonlinear_arith) requires lch == nl / nt, t <= nt, nt >= 1;
            assert((t + 1) * lch <= nl) by (nonlinear_arith) requires lch == nl / nt, t + 1 <= nt, nt >= 1;
            assert(t * lch <= (t + 1) * lch) by (nonlinear_arith) requires lch >= 0;
        }
        let lo = t * lch;
        let hi = if t + 1 == nt { nl } else { (t + 1) * lch };
        let olo = prev_o;
        let ohi = if t + 1 == nt {
            no
        } else if hi < nl {
            let x = lower_bound(c.ok, no, c.lk[hi]);
            if x < olo { olo } else { x }
        } else {
            olo
        };
        proof {
            assert((ohi - olo) / (nb * 20) <= ohi - olo) by (nonlinear_arith) requires nb >= 1, ohi >= olo;
        }
        let rcap = (ohi - olo) / (nb * 20) + 64;
        proof {
            lemma_cap_fit((ohi - olo) as int, nb as int, rcap as int);
            assert(nb * rcap <= usize::MAX);
        }
        let nbr = nb * rcap;
        let task = STask {
            c: *c, lo, hi, olo, ohi, nb, rcap,
            rv: zeros_i64(nbr), cnt: zeros_usize(nb),
            bi: zeros_usize(BATCH), bk: zeros_i64(BATCH), bc: zeros_i64(BATCH), bs: zeros_usize(BATCH), be: zeros_usize(BATCH),
            sv: Ghost(sv),
        };
        proof {
            assert(scan_pre(task)) by {
                assert forall|b: int| 0 <= b < nb implies #[trigger] task.cnt@[b] == 0 by {}
            }
        }
        tasks.push(task);
        proof {
            ls = ls.push(hi as int);
            os = os.push(ohi as int);
        }
        prev_o = ohi;
        t = t + 1;
    }
    (tasks, Ghost((ls, os)))
}

/// Runs the scan tasks (on the calling thread with one task).
fn run_scans(tasks: Vec<STask>, dispatch: &mut Dispatch) -> (r: Result<Vec<SOut>, WorkerFailure>)
    requires tasks@.len() <= MAX_WORKERS, tasks@.len() >= 1, forall|u: int| 0 <= u < tasks@.len() ==> (#[trigger] tasks@[u]).pre(),
    ensures r matches Ok(outs) ==> outs@.len() == tasks@.len() && forall|u: int| 0 <= u < tasks@.len() ==> #[trigger] tasks@[u].post(outs@[u]),
{
    if tasks.len() == 1 {
        let ghost tv = tasks@;
        let mut tasks = tasks;
        let task = tasks.pop().unwrap();
        assert(task == tv[0]);
        let out = task.run();
        let mut outs: Vec<SOut> = Vec::new();
        outs.push(out);
        Ok(outs)
    } else {
        fork_join(dispatch, tasks)
    }
}

/// Runs the customer tasks (on the calling thread with one task).
fn run_custs(tasks: Vec<CTask>, dispatch: &mut Dispatch) -> (r: Result<Vec<COut>, WorkerFailure>)
    requires tasks@.len() <= MAX_WORKERS, tasks@.len() >= 1, forall|u: int| 0 <= u < tasks@.len() ==> (#[trigger] tasks@[u]).pre(),
    ensures r matches Ok(outs) ==> outs@.len() == tasks@.len() && forall|u: int| 0 <= u < tasks@.len() ==> #[trigger] tasks@[u].post(outs@[u]),
{
    if tasks.len() == 1 {
        let ghost tv = tasks@;
        let mut tasks = tasks;
        let task = tasks.pop().unwrap();
        assert(task == tv[0]);
        let out = task.run();
        let mut outs: Vec<COut> = Vec::new();
        outs.push(out);
        Ok(outs)
    } else {
        fork_join(dispatch, tasks)
    }
}

// ------------------------------------------------------------------------------------------------ global facts

/// The scan tasks' pair checks join over the first `u` tasks.
proof fn lemma_pairs_prefix(sv: StoresView, ls: Seq<int>, os: Seq<int>, t: int, outs: Seq<SOut>, u: int)
    requires
        ranges_ok(sv, ls, os, t), 0 <= u <= t,
        forall|w: int| 0 <= w < t ==> pairs_ok(lk(sv), pair_lo(n_l(sv), #[trigger] ls[w]), pair_hi(n_l(sv), ls[w + 1])),
    ensures pairs_ok(lk(sv), pair_lo(n_l(sv), ls[0]), pair_lo(n_l(sv), ls[u])),
    decreases u,
{
    if u > 0 {
        lemma_pairs_prefix(sv, ls, os, t, outs, u - 1);
        assert(pairs_ok(lk(sv), pair_lo(n_l(sv), ls[u - 1]), pair_hi(n_l(sv), ls[u])));
        assert(pair_hi(n_l(sv), ls[u]) == pair_lo(n_l(sv), ls[u]));
        lemma_pairs_join(lk(sv), pair_lo(n_l(sv), ls[0]), pair_lo(n_l(sv), ls[u - 1]), pair_lo(n_l(sv), ls[u]));
    }
}

/// When every scan task's pairs are in order, `l_orderkey` is sorted.
proof fn lemma_sorted(sv: StoresView, ls: Seq<int>, os: Seq<int>, t: int, outs: Seq<SOut>)
    requires
        ranges_ok(sv, ls, os, t),
        forall|w: int| 0 <= w < t ==> pairs_ok(lk(sv), pair_lo(n_l(sv), #[trigger] ls[w]), pair_hi(n_l(sv), ls[w + 1])),
    ensures lk_sorted(sv),
{
    lemma_pairs_prefix(sv, ls, os, t, outs, t);
    let nl = n_l(sv);
    assert(pair_lo(nl, ls[t]) == nl);
    if nl >= 2 {
        assert(pair_lo(nl, ls[0]) == 1);
    }
}

/// The range of a row in a monotone cover.
proof fn lemma_find_range(s: Seq<int>, t: int, i: int) -> (u: int)
    requires t >= 1, s.len() == t + 1, s[0] <= i < s[t], forall|w: int| 0 <= w < t ==> #[trigger] s[w] <= s[w + 1],
    ensures 0 <= u < t, s[u] <= i < s[u + 1],
    decreases t,
{
    if i >= s[t - 1] { t - 1 } else {
        lemma_find_range(s.subrange(0, t), t - 1, i)
    }
}

/// The customer sum of `a` over orders whose absolute masses are their sums: its absolute mass is its sum.
proof fn lemma_cust_abs(c: Cols, sv: StoresView, a: int, lo: int, hi: int)
    requires
        cols_ok(c, sv), 0 <= a < n_c(sv), 0 <= lo <= hi <= n_o(sv), ck(sv)[a] as int == c.cbase + a,
        forall|j: int| 0 <= j < n_o(sv) && qualifies(sv, c.dlo as int, c.dhi as int, c.cbase as int, j) ==>
            #[trigger] kabs(sv, okey(sv, j), 0, n_l(sv)) == ksum(sv, okey(sv, j), 0, n_l(sv)),
    ensures cabs(sv, c.dlo as int, c.dhi as int, a, lo, hi) == csum(sv, c.dlo as int, c.dhi as int, a, lo, hi),
    decreases hi - lo,
{
    let (dlo, dhi, cbase) = (c.dlo as int, c.dhi as int, c.cbase as int);
    if hi > lo {
        lemma_cust_abs(c, sv, a, lo, hi - 1);
        let j = hi - 1;
        if cmatch(sv, dlo, dhi, a, j) {
            assert(qualifies(sv, dlo, dhi, cbase, j));
            assert(kabs(sv, okey(sv, j), 0, n_l(sv)) == ksum(sv, okey(sv, j), 0, n_l(sv)));
        }
    }
}

/// The groups of `[0, x)` from 0 are the statement's groups list.
proof fn lemma_grange_glist(sv: StoresView, dlo: int, dhi: int, x: int)
    requires 0 <= x,
    ensures grange(sv, dlo, dhi, 0, x) == glist(sv, dlo, dhi, x),
    decreases x,
{
    if x > 0 {
        lemma_grange_glist(sv, dlo, dhi, x - 1);
    }
}

// ------------------------------------------------------------------------------------------------ the merge

/// A list of ids of a part of `[lo, hi)` lies in it.
proof fn lemma_part_ids(sv: StoresView, dlo: int, dhi: int, sel: Seq<int>, lo: int, hi: int)
    requires top_of(sel, grange(sv, dlo, dhi, lo, hi), cval(sv, dlo, dhi), TOPN as int), lo <= hi,
    ensures forall|i: int| 0 <= i < sel.len() ==> lo <= #[trigger] sel[i] < hi,
{
    lemma_grange(sv, dlo, dhi, lo, hi);
    assert forall|i: int| 0 <= i < sel.len() implies lo <= #[trigger] sel[i] < hi by {
        assert(grange(sv, dlo, dhi, lo, hi).contains(sel[i]));
    }
}

/// What a customer task delivers for its range `[lo, hi)`.
pub open spec fn part_ok(sv: StoresView, dlo: int, dhi: int, o: COut, lo: int, hi: int) -> bool {
    &&& o.top.cap == TOPN
    &&& exists|s: Seq<int>| top_inv(o.top, s, cval(sv, dlo, dhi))
    &&& top_of(tsel(o.top), grange(sv, dlo, dhi, lo, hi), cval(sv, dlo, dhi), TOPN as int)
}

/// The merge invariant: offered ids are groups of the earlier ranges or of the first `i` ids of range `q`'s list;
/// the lists of the earlier ranges and those first ids are offered.
pub open spec fn merge_inv(sv: StoresView, dlo: int, dhi: int, outs: Seq<COut>, s: Seq<int>, q: int, i: int, cr: Seq<int>) -> bool {
    &&& forall|y: int| #[trigger] s.contains(y) ==> is_group(sv, dlo, dhi, y) && 0 <= y
            && (y < cr[q] || exists|j: int| 0 <= j < i && tsel(outs[q].top)[j] == y)
    &&& forall|w: int, j: int| 0 <= w < q && 0 <= j < tsel(outs[w].top).len() ==> s.contains(#[trigger] tsel(outs[w].top)[j])
    &&& forall|j: int| 0 <= j < i ==> s.contains(#[trigger] tsel(outs[q].top)[j])
}

/// Offering range `q`'s id at `i` keeps the merge invariant.
proof fn lemma_merge_step(sv: StoresView, dlo: int, dhi: int, outs: Seq<COut>, s: Seq<int>, q: int, i: int, cr: Seq<int>)
    requires
        merge_inv(sv, dlo, dhi, outs, s, q, i, cr),
        0 <= q < outs.len(), 0 <= i < tsel(outs[q].top).len(), q + 1 < cr.len(),
        part_ok(sv, dlo, dhi, outs[q], cr[q], cr[q + 1]), cr[q] <= cr[q + 1],
    ensures
        !s.contains(tsel(outs[q].top)[i]),
        merge_inv(sv, dlo, dhi, outs, s.push(tsel(outs[q].top)[i]), q, i + 1, cr),
{
    let l = tsel(outs[q].top);
    let (lo, hi) = (cr[q], cr[q + 1]);
    let x = l[i];
    lemma_part_ids(sv, dlo, dhi, l, lo, hi);
    lemma_grange(sv, dlo, dhi, lo, hi);
    assert(grange(sv, dlo, dhi, lo, hi).contains(x));
    if s.contains(x) {
        let j = choose|j: int| 0 <= j < i && l[j] == x;
        assert(l.no_duplicates());
    }
    let s2 = s.push(x);
    assert forall|y: int| #[trigger] s2.contains(y) implies is_group(sv, dlo, dhi, y) && 0 <= y
        && (y < lo || exists|j: int| 0 <= j < i + 1 && l[j] == y) by {
        vstd::seq_lib::lemma_seq_contains_after_push(s, x, y);
        if y == x {
            assert(l[i] == y);
        } else {
            assert(s.contains(y));
            if !(y < lo) {
                let j = choose|j: int| 0 <= j < i && l[j] == y;
                assert(0 <= j < i + 1 && l[j] == y);
            }
        }
    }
    assert forall|w: int, j: int| 0 <= w < q && 0 <= j < tsel(outs[w].top).len() implies s2.contains(#[trigger] tsel(outs[w].top)[j]) by {
        vstd::seq_lib::lemma_seq_contains_after_push(s, x, tsel(outs[w].top)[j]);
    }
    assert forall|j: int| 0 <= j < i + 1 implies s2.contains(#[trigger] l[j]) by {
        vstd::seq_lib::lemma_seq_contains_after_push(s, x, l[j]);
    }
}

/// After range `q`'s whole list, the invariant holds for range `q + 1` from its start.
proof fn lemma_merge_next(sv: StoresView, dlo: int, dhi: int, outs: Seq<COut>, s: Seq<int>, q: int, cr: Seq<int>)
    requires
        merge_inv(sv, dlo, dhi, outs, s, q, tsel(outs[q].top).len() as int, cr),
        0 <= q < outs.len(), q + 1 < cr.len(),
        part_ok(sv, dlo, dhi, outs[q], cr[q], cr[q + 1]), cr[q] <= cr[q + 1],
    ensures merge_inv(sv, dlo, dhi, outs, s, q + 1, 0, cr),
{
    let l = tsel(outs[q].top);
    let (lo, hi) = (cr[q], cr[q + 1]);
    lemma_part_ids(sv, dlo, dhi, l, lo, hi);
    assert forall|y: int| #[trigger] s.contains(y) implies is_group(sv, dlo, dhi, y) && 0 <= y && y < hi by {
        if !(y < lo) {
            let j = choose|j: int| 0 <= j < l.len() && l[j] == y;
        }
    }
    assert forall|w: int, j: int| 0 <= w < q + 1 && 0 <= j < tsel(outs[w].top).len() implies s.contains(#[trigger] tsel(outs[w].top)[j]) by {
        if w == q {}
    }
}

/// The merged buffer is a top list of all groups.
proof fn lemma_merge_done(sv: StoresView, dlo: int, dhi: int, outs: Seq<COut>, g: Top, s: Seq<int>, np: int, cr: Seq<int>)
    requires
        np >= 1, outs.len() == np, cr.len() == np + 1, cr[0] == 0, cr[np] == n_c(sv),
        forall|q: int| 0 <= q < np ==> #[trigger] cr[q] <= cr[q + 1],
        top_inv(g, s, cval(sv, dlo, dhi)), g.cap == TOPN,
        forall|y: int| #[trigger] s.contains(y) ==> is_group(sv, dlo, dhi, y) && 0 <= y < n_c(sv),
        forall|w: int, j: int| 0 <= w < np && 0 <= j < tsel(outs[w].top).len() ==> s.contains(#[trigger] tsel(outs[w].top)[j]),
        forall|w: int| 0 <= w < np ==> part_ok(sv, dlo, dhi, #[trigger] outs[w], cr[w], cr[w + 1]),
    ensures top_of(tsel(g), glist(sv, dlo, dhi, n_c(sv)), cval(sv, dlo, dhi), TOPN as int),
{
    let nc = n_c(sv);
    let gall = glist(sv, dlo, dhi, nc);
    let vf = cval(sv, dlo, dhi);
    lemma_glist(sv, dlo, dhi, nc);
    assert forall|y: int| #[trigger] s.contains(y) implies gall.contains(y) by {}
    assert forall|y: int| #[trigger] gall.contains(y) && !s.contains(y) implies exists|l: Seq<int>| #[trigger] dominated(l, y, s, vf, TOPN as int) by {
        let q = lemma_find_range(cr, np, y);
        let (lo, hi) = (cr[q], cr[q + 1]);
        assert(part_ok(sv, dlo, dhi, outs[q], lo, hi));
        let l = tsel(outs[q].top);
        lemma_grange(sv, dlo, dhi, lo, hi);
        assert(grange(sv, dlo, dhi, lo, hi).contains(y));
        if l.contains(y) {
            let j = choose|j: int| 0 <= j < l.len() && l[j] == y;
            assert(s.contains(l[j]));
        }
        assert forall|i: int| 0 <= i < l.len() implies s.contains(#[trigger] l[i]) by {}
        lemma_dominated(l, grange(sv, dlo, dhi, lo, hi), s, y, vf, TOPN as int);
    }
    lemma_top_merge(tsel(g), s, gall, vf, TOPN as int);
}

// ------------------------------------------------------------------------------------------------ the fast path

/// The first bucket of customer task `q` of `np`: `q * nb / np`.
pub open spec fn bq_of(q: int, nb: int, np: int) -> int { q * nb / np }

proof fn lemma_bq(q: int, nb: int, np: int)
    requires 0 <= q < np, nb >= 0, np >= 1,
    ensures 0 <= bq_of(q, nb, np) <= bq_of(q + 1, nb, np) <= nb, bq_of(0, nb, np) == 0, bq_of(np, nb, np) == nb,
{
    assert(0 <= q * nb / np <= (q + 1) * nb / np) by (nonlinear_arith) requires 0 <= q, nb >= 0, np >= 1;
    assert((q + 1) * nb / np <= nb) by (nonlinear_arith) requires q + 1 <= np, nb >= 0, np >= 1;
    assert(0 * nb / np == 0) by (nonlinear_arith) requires np >= 1;
    assert(np * nb / np == nb) by (nonlinear_arith) requires np >= 1;
}

/// The facts of successful scan tasks: `l_orderkey` is sorted, the outputs are complete for every bucket, and every
/// qualifying order's absolute mass is its revenue.
proof fn lemma_scan_facts(c: Cols, sv: StoresView, ls: Seq<int>, os: Seq<int>, nt: int, nb: int, tv: Seq<STask>, ov: Seq<SOut>)
    requires
        cols_ok(c, sv), ranges_ok(sv, ls, os, nt), tv.len() == nt, ov.len() == nt,
        forall|w: int| 0 <= w < nt ==> (#[trigger] tv[w]).post(ov[w]) && tv[w].c == c && tv[w].sv@ == sv
            && tv[w].lo == ls[w] && tv[w].hi == ls[w + 1] && tv[w].olo == os[w] && tv[w].ohi == os[w + 1] && tv[w].nb == nb,
        forall|w: int| 0 <= w < nt ==> (#[trigger] ov[w]).ok,
    ensures
        lk_sorted(sv),
        forall|b: int| 0 <= b < nb ==> #[trigger] outs_ok(c, sv, ov, os, nb, b),
        forall|j: int| 0 <= j < n_o(sv) && qualifies(sv, c.dlo as int, c.dhi as int, c.cbase as int, j) ==>
            #[trigger] kabs(sv, okey(sv, j), 0, n_l(sv)) == ksum(sv, okey(sv, j), 0, n_l(sv)),
{
    let (dlo, dhi, cbase) = (c.dlo as int, c.dhi as int, c.cbase as int);
    assert forall|w: int| 0 <= w < nt implies scan_post(c, sv, ls[w], ls[w + 1], os[w], os[w + 1], nb,
        (#[trigger] ov[w]).rcap as int, ov[w]) by {
        assert(tv[w].post(ov[w]));
    }
    assert forall|w: int| 0 <= w < nt implies pairs_ok(lk(sv), pair_lo(n_l(sv), #[trigger] ls[w]), pair_hi(n_l(sv), ls[w + 1])) by {
        assert(scan_post(c, sv, ls[w], ls[w + 1], os[w], os[w + 1], nb, ov[w].rcap as int, ov[w]));
    }
    lemma_sorted(sv, ls, os, nt, ov);
    reveal(outs_ok);
    assert forall|b: int| 0 <= b < nb implies #[trigger] outs_ok(c, sv, ov, os, nb, b) by {
        assert forall|t: int| 0 <= t < ov.len() implies #[trigger] out_wf(ov[t], nb) by {
            assert(scan_post(c, sv, ls[t], ls[t + 1], os[t], os[t + 1], nb, ov[t].rcap as int, ov[t]));
        }
        assert forall|t: int| 0 <= t < ov.len() implies #[trigger] bucket_ok(c, sv, ov[t].rv@, ov[t].cnt@,
            ov[t].lists@, ov[t].rcap as int, os[t], os[t + 1], b) by {
            assert(scan_post(c, sv, ls[t], ls[t + 1], os[t], os[t + 1], nb, ov[t].rcap as int, ov[t]));
            assert(buckets_ok(c, sv, ov[t].rv@, ov[t].cnt@, ov[t].lists@, nb, ov[t].rcap as int, os[t], os[t + 1]));
        }
    }
    assert forall|j: int| 0 <= j < n_o(sv) && qualifies(sv, dlo, dhi, cbase, j) implies
        #[trigger] kabs(sv, okey(sv, j), 0, n_l(sv)) == ksum(sv, okey(sv, j), 0, n_l(sv)) by {
        let w = lemma_find_range(os, nt, j);
        assert(scan_post(c, sv, ls[w], ls[w + 1], os[w], os[w + 1], nb, ov[w].rcap as int, ov[w]));
        assert(abs_ok(c, sv, os[w], os[w + 1]));
    }
}

/// The customer tasks: `np` consecutive bucket ranges, customer rows `[cr[q], cr[q + 1])`.
fn build_custs(c: &Cols, arc: &Arc<Vec<SOut>>, Ghost(os): Ghost<Seq<int>>, nb: usize, np: usize, Ghost(sv): Ghost<StoresView>)
    -> (r: (Vec<CTask>, Ghost<Seq<int>>))
    requires
        cols_ok(*c, sv), lk_sorted(sv), 1 <= np <= nb, np <= MAX_WORKERS, 1 <= c.nc < 0x8000_0000,
        1 <= nb <= 0x1_0000, c.nc <= nb * CPB, nb * CPB < c.nc + CPB, (**arc)@.len() >= 1,
        forall|b: int| 0 <= b < nb ==> #[trigger] outs_ok(*c, sv, (**arc)@, os, nb as int, b),
    ensures ({
        let (tasks, cr) = r;
        &&& tasks@.len() == np && cr@.len() == np + 1 && cr@[0] == 0 && cr@[np as int] == c.nc
        &&& forall|w: int| 0 <= w < np ==> #[trigger] cr@[w] <= cr@[w + 1]
        &&& forall|w: int| 0 <= w < np ==> (#[trigger] tasks@[w]).pre() && tasks@[w].c == *c && tasks@[w].sv@ == sv
                && bstart(tasks@[w].b0 as int, c.nc as int) == cr@[w] && bstart(tasks@[w].b1 as int, c.nc as int) == cr@[w + 1]
    }),
{
    let ghost vf = cval(sv, c.dlo as int, c.dhi as int);
    let nc = c.nc;
    let mut ctasks: Vec<CTask> = Vec::new();
    let ghost mut cr: Seq<int> = seq![0int];
    proof {
        lemma_bq(0, nb as int, np as int);
    }
    let mut q: usize = 0;
    while q < np
        invariant
            cols_ok(*c, sv), lk_sorted(sv), q <= np, 1 <= np <= nb, np <= MAX_WORKERS, nc == c.nc, 1 <= nc < 0x8000_0000,
            1 <= nb <= 0x1_0000, nc <= nb * CPB, nb * CPB < nc + CPB, (**arc)@.len() >= 1,
            forall|b: int| 0 <= b < nb ==> #[trigger] outs_ok(*c, sv, (**arc)@, os, nb as int, b),
            ctasks@.len() == q, cr.len() == q + 1, cr[0] == 0, cr[q as int] == bstart(bq_of(q as int, nb as int, np as int), nc as int),
            forall|w: int| 0 <= w < q ==> #[trigger] cr[w] <= cr[w + 1],
            forall|w: int| 0 <= w < q ==> (#[trigger] ctasks@[w]).pre() && ctasks@[w].c == *c && ctasks@[w].sv@ == sv
                && bstart(ctasks@[w].b0 as int, nc as int) == cr[w] && bstart(ctasks@[w].b1 as int, nc as int) == cr[w + 1],
        decreases np - q,
    {
        proof {
            lemma_bq(q as int, nb as int, np as int);
            assert(q * nb <= 64 * 0x1_0000 && (q + 1) * nb <= 64 * 0x1_0000) by (nonlinear_arith)
                requires q < np, np <= 64, nb <= 0x1_0000;
        }
        let b0 = q * nb / np;
        let b1 = (q + 1) * nb / np;
        let task = CTask {
            c: *c, outs: arc.clone(), os: Ghost(os), nb, b0, b1, acc: zeros_i64(CPB), top: top_new(TOPN, Ghost(vf)),
            sv: Ghost(sv),
        };
        proof {
            assert(cust_pre(task));
            assert(bstart(b0 as int, nc as int) <= bstart(b1 as int, nc as int)) by {
                assert(b0 * CPB <= b1 * CPB) by (nonlinear_arith) requires b0 <= b1;
            }
        }
        ctasks.push(task);
        proof {
            cr = cr.push(bstart(b1 as int, nc as int));
        }
        q = q + 1;
    }
    proof {
        lemma_bq(0, nb as int, np as int);
        assert(bstart(nb as int, nc as int) == nc);
    }
    (ctasks, Ghost(cr))
}

/// The merge of the customer tasks' top lists into one top list of all groups.
fn merge_tops(couts: &Vec<COut>, np: usize, Ghost(cr): Ghost<Seq<int>>, Ghost(sv): Ghost<StoresView>, Ghost(dlo): Ghost<int>,
    Ghost(dhi): Ghost<int>) -> (g: Top)
    requires
        np >= 1, couts@.len() == np, cr.len() == np + 1, cr[0] == 0, cr[np as int] == n_c(sv),
        forall|v: int| 0 <= v < np ==> #[trigger] cr[v] <= cr[v + 1],
        forall|v: int| 0 <= v < np ==> part_ok(sv, dlo, dhi, #[trigger] couts@[v], cr[v], cr[v + 1]),
    ensures
        g.cap == TOPN && g.k <= g.cap && g.rows@.len() == g.cap && g.vals@.len() == g.cap,
        top_of(tsel(g), glist(sv, dlo, dhi, n_c(sv)), cval(sv, dlo, dhi), TOPN as int),
        forall|k: int| 0 <= k < g.k ==> #[trigger] g.vals@[k] as int == ctot(sv, dlo, dhi, g.rows@[k] as int),
{
    let ghost co = couts@;
    let ghost vf = cval(sv, dlo, dhi);
    let ghost nc = n_c(sv);
    let mut g = top_new(TOPN, Ghost(vf));
    let ghost mut s: Seq<int> = Seq::empty();
    let mut q: usize = 0;
    while q < np
        invariant
            q <= np, couts@ == co, co.len() == np, vf == cval(sv, dlo, dhi), cr.len() == np + 1, nc == n_c(sv),
            forall|v: int| 0 <= v < np ==> #[trigger] cr[v] <= cr[v + 1], cr[0] == 0, cr[np as int] == nc,
            top_inv(g, s, vf), g.cap == TOPN,
            forall|v: int| 0 <= v < np ==> part_ok(sv, dlo, dhi, #[trigger] co[v], cr[v], cr[v + 1]),
            q < np ==> merge_inv(sv, dlo, dhi, co, s, q as int, 0, cr),
            q == np ==> forall|y: int| #[trigger] s.contains(y) ==> is_group(sv, dlo, dhi, y) && 0 <= y < nc,
            forall|v: int, j: int| 0 <= v < q && 0 <= j < tsel(co[v].top).len() ==> s.contains(#[trigger] tsel(co[v].top)[j]),
        decreases np - q,
    {
        let tq = &couts[q].top;
        let ghost l = tsel(*tq);
        proof {
            assert(part_ok(sv, dlo, dhi, co[q as int], cr[q as int], cr[q + 1]));
            let sq = choose|sq: Seq<int>| top_inv(*tq, sq, vf);
            assert(top_inv(*tq, sq, vf));
        }
        let k = tq.k;
        let mut i: usize = 0;
        while i < k
            invariant
                q < np, couts@ == co, co.len() == np, vf == cval(sv, dlo, dhi), *tq == co[q as int].top, k == tq.k, i <= k,
                l == tsel(*tq), k <= tq.cap, tq.rows@.len() == tq.cap, tq.vals@.len() == tq.cap, cr.len() == np + 1,
                forall|j: int| 0 <= j < k ==> #[trigger] tq.vals@[j] as int == vf(tq.rows@[j] as int),
                top_inv(g, s, vf), g.cap == TOPN,
                part_ok(sv, dlo, dhi, co[q as int], cr[q as int], cr[q + 1]), cr[q as int] <= cr[q + 1],
                merge_inv(sv, dlo, dhi, co, s, q as int, i as int, cr),
            decreases k - i,
        {
            proof {
                lemma_merge_step(sv, dlo, dhi, co, s, q as int, i as int, cr);
            }
            top_offer(&mut g, tq.rows[i], tq.vals[i], Ghost(s), Ghost(vf));
            proof {
                s = s.push(l[i as int]);
            }
            i = i + 1;
        }
        proof {
            lemma_merge_next(sv, dlo, dhi, co, s, q as int, cr);
            if q + 1 == np {
                assert forall|y: int| #[trigger] s.contains(y) implies is_group(sv, dlo, dhi, y) && 0 <= y < nc by {
                    assert(merge_inv(sv, dlo, dhi, co, s, q + 1, 0, cr));
                }
            }
        }
        q = q + 1;
    }
    proof {
        lemma_merge_done(sv, dlo, dhi, co, g, s, np as int, cr);
    }
    g
}

/// The fast path: a top-`TOPN` list of all groups (`fast_ok`), `None` when a check failed.
pub fn fast_path(c: &Cols, workers: usize, dispatch: &mut Dispatch, Ghost(sv): Ghost<StoresView>)
    -> (r: Result<Option<Top>, WorkerFailure>)
    requires cols_ok(*c, sv), 1 <= workers <= MAX_WORKERS, 1 <= c.nc < 0x8000_0000, c.no >= 1,
    ensures r matches Ok(Some(t)) ==> fast_ok(t, sv, c.dlo as int, c.dhi as int),
{
    let ghost (dlo, dhi, cbase) = (c.dlo as int, c.dhi as int, c.cbase as int);
    if c.no > usize::MAX - 0x40_0000 {
        return Ok(None);
    }
    let nc = c.nc;
    let nb = (nc + CPB - 1) / CPB;
    proof {
        assert(1 <= nb <= 0x1_0000) by (nonlinear_arith) requires nb == (nc + 131071) / 131072, 1 <= nc < 0x8000_0000;
        assert(nc <= nb * CPB && nb * CPB < nc + CPB) by (nonlinear_arith) requires nb == (nc + 131071) / 131072, nc >= 1;
    }
    // the scan phase
    let nt = workers;
    let (tasks, granges) = build_scans(c, nt, nb, Ghost(sv));
    let ghost (ls, os) = granges@;
    let ghost tv = tasks@;
    let outs = match run_scans(tasks, dispatch) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    let mut sink: i64 = 0;
    let mut u: usize = 0;
    while u < nt
        invariant u <= nt, outs@.len() == nt, forall|w: int| 0 <= w < u ==> (#[trigger] outs@[w]).ok,
        decreases nt - u,
    {
        if !outs[u].ok {
            return Ok(None);
        }
        sink = sink ^ outs[u].sink;
        u = u + 1;
    }
    if sink == 0x5eed_5eed_5eed_5eed {
        // keeps the scan tasks' touch loads (`scan::touch`); never taken in practice, always sound
        return Ok(None);
    }
    let ghost ov = outs@;
    proof {
        lemma_scan_facts(*c, sv, ls, os, nt as int, nb as int, tv, ov);
    }
    // the customer phase
    // at most 32 customer tasks: each faults in its own accumulator (`CPB` entries)
    let np0 = if workers < nb { workers } else { nb };
    let np = if np0 > 32 { 32 } else { np0 };
    let arc: Arc<Vec<SOut>> = Arc::new(outs);
    let (ctasks, gcr) = build_custs(c, &arc, Ghost(os), nb, np, Ghost(sv));
    let ghost cr = gcr@;
    let ghost ctv = ctasks@;
    let couts = match run_custs(ctasks, dispatch) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    let mut w: usize = 0;
    while w < np
        invariant w <= np, couts@.len() == np, forall|v: int| 0 <= v < w ==> (#[trigger] couts@[v]).ok,
        decreases np - w,
    {
        if !couts[w].ok {
            return Ok(None);
        }
        w = w + 1;
    }
    let ghost co = couts@;
    proof {
        assert forall|v: int| 0 <= v < np implies cust_post(*c, sv, cr[v], cr[v + 1], #[trigger] co[v]) by {
            assert(ctv[v].post(co[v]));
        }
        assert forall|v: int| 0 <= v < np implies part_ok(sv, dlo, dhi, #[trigger] co[v], cr[v], cr[v + 1]) by {
            assert(cust_post(*c, sv, cr[v], cr[v + 1], co[v]));
        }
    }
    // the merge
    let g = merge_tops(&couts, np, Ghost(cr), Ghost(sv), Ghost(dlo), Ghost(dhi));
    proof {
        lemma_fast_final(*c, sv, co, cr, np as int);
        lemma_grange_glist(sv, dlo, dhi, nc as int);
    }
    Ok(Some(g))
}

/// Every group is within the SUM capacity: the customer tasks checked every customer positional and bounded every
/// revenue below `CAP`, and every qualifying order's absolute mass is its revenue.
proof fn lemma_fast_final(c: Cols, sv: StoresView, co: Seq<COut>, cr: Seq<int>, np: int)
    requires
        cols_ok(c, sv), np >= 1, co.len() == np, cr.len() == np + 1, cr[0] == 0, cr[np] == n_c(sv),
        forall|v: int| 0 <= v < np ==> #[trigger] cr[v] <= cr[v + 1],
        forall|v: int| 0 <= v < np ==> cust_post(c, sv, cr[v], cr[v + 1], #[trigger] co[v]) && co[v].ok,
        forall|j: int| 0 <= j < n_o(sv) && qualifies(sv, c.dlo as int, c.dhi as int, c.cbase as int, j) ==>
            #[trigger] kabs(sv, okey(sv, j), 0, n_l(sv)) == ksum(sv, okey(sv, j), 0, n_l(sv)),
    ensures groups_capped(sv, c.dlo as int, c.dhi as int),
{
    let (dlo, dhi, cbase) = (c.dlo as int, c.dhi as int, c.cbase as int);
    assert forall|a: int| #[trigger] is_group(sv, dlo, dhi, a) implies ctabs(sv, dlo, dhi, a) <= i128_max() by {
        let v = lemma_find_range(cr, np, a);
        assert(cust_post(c, sv, cr[v], cr[v + 1], co[v]));
        assert(ck(sv)[a] as int == cbase + a && 0 <= ctot(sv, dlo, dhi, a) < CAP);
        lemma_cust_abs(c, sv, a, 0, n_o(sv));
    }
}

} // verus!
