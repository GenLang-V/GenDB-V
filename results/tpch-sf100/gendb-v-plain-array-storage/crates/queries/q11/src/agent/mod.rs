//! TPC-H Q11 (important stock identification) over the flat storages: per part, the value
//! `SUM(ps_supplycost * ps_availqty)` of its suppliers in the nation `$1`, kept when above `$2` times the nation's
//! total, ordered by value descending.
//!
//! Plan of a call (`query`):
//! 1. the keys of the nations named `$1` (`supp::nations_named`);
//! 2. the supplier bitmap (`supp::supplier_bits`, parallel): one bit per supplier row for "its nation is named `$1`",
//!    and whether the supplier keys are dense (`s_suppkey = s_suppkey[0] + row`);
//! 3. a lower bound `lb` of the HAVING threshold estimated from a sample of the qualifying rows (`sample_lb`; only
//!    a hint, checked in step 5);
//! 4. the partsupp scan (`scan::ScanTask`, one task per row range, the ranges' ends moved to a change of
//!    `ps_partkey`): per block, the qualifying rows (dense supplier lookup and bitmap), their part key and value,
//!    and runs of equal part keys with their sums; runs above `lb` are stored and sorted by sum, descending; per
//!    range the total, the absolute mass and the keys of the first and last run;
//! 5. the combination (`combine`): every range done, every range's keys increasing and the ranges' keys increasing
//!    from range to range; then each run is a whole group. The HAVING threshold is `total * $2 / 10^10` rounded
//!    down; when it is below `lb` the scan is repeated with no bound (`attempt`);
//! 6. HAVING and ORDER BY: each range's sorted list cut after its last entry above the threshold (`cut_lists`),
//!    the lists merged into the answer's columns (`filter::merge_all`).
//! Supplier keys that are not dense, keys out of order, or a full run buffer take the general serial path
//! (`answer::general_answer`); an absolute mass or `total * $2` beyond `i128` is the capacity answer.
//!
//! Proof: `sem`/`normal`/`body`/`capacity` give the statement's meaning over the stored arrays (`normal::rsum`);
//! `scan`/`groups` relate the runs to those sums; `output::lemma_answer_rows` turns a sorted permutation of the
//! passing groups into an allowed output.
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::query::param_domain;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db};
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS, WorkerTask, fork_join};
use crate::gendb_entry::runtime::{QueryError, WorkerFailure};
use crate::gendb_params::Params;
use crate::stores::flat_partsupp::interface as psi;
use crate::stores::flat_supplier::interface as si;
use crate::agent::model::*;
use crate::agent::sem::{params_of, lemma_product_bound};
use crate::agent::normal::*;
use crate::agent::groups::*;
use crate::agent::output::*;
use crate::agent::scan::*;
use crate::agent::supp::*;
use crate::agent::filter::*;
use crate::agent::common::msort::pairs;
use crate::agent::answer::*;
use crate::agent::pmerge::parallel_merge;
use crate::agent::common::msort::desc;

pub mod common;
pub mod model;
pub mod sem;
pub mod normal;
pub mod body;
pub mod capacity;
pub mod groups;
pub mod scan;
pub mod supp;
pub mod output;
pub mod filter;
pub mod fallback;
pub mod answer;
pub mod pmerge;

verus! {

// ------------------------------------------------------------------------------------------ the scan phase

/// Run buffer slots of a task: at least 32 MiB of `i64` keys, so that every run and scratch buffer is a fresh
/// lazily zeroed mapping (see `scan`).
pub const BIG: usize = 4_400_000;

/// Row ranges `[rg[t].0, rg[t].1)` that cover `[0, n)` in order.
#[verifier::opaque]
pub open spec fn ranges_ok(rg: Seq<(int, int)>, n: int) -> bool {
    &&& rg.len() >= 1
    &&& rg[0].0 == 0 && rg[rg.len() - 1].1 == n
    &&& forall|t: int| 0 <= t < rg.len() ==> (#[trigger] rg[t]).0 <= rg[t].1
    &&& forall|t: int| 0 < t < rg.len() ==> (#[trigger] rg[t]).0 == rg[t - 1].1
}

/// Scan the partsupp rows in `nt` ranges (the ends moved forward to a change of part key), storing runs above `lb`.
fn scan_all(pk: &'static [i64], sk: &'static [i64], aq: &'static [i64], cost: &'static [i128], n: usize,
    bits: &Arc<Vec<u64>>, ns: usize, base: i64, nt: usize, lb: i128, dispatch: &mut Dispatch,
    Ghost(sv): Ghost<StoresView>, Ghost(p): Ghost<Seq<u8>>) -> (r: Result<(Vec<ScanOut>, Ghost<Seq<(int, int)>>), WorkerFailure>)
    requires
        stores_wf(sv), bounds_ok(sv),
        pk@ == ps_pkeys(sv), sk@ == ps_skeys(sv), aq@ == ps_aqs(sv), cost@ == ps_costs(sv), n == ps_n(sv),
        bits_ok((**bits)@, ns as int, sv, p), dense_ok(sv, base as int, base + ns - 1), 0 <= base <= off_bound(), ns <= off_bound(),
        1 <= nt <= MAX_WORKERS,
    ensures
        r matches Ok((outs, rg)) ==> outs@.len() == rg@.len() && rg@.len() == nt && ranges_ok(rg@, n as int)
            && forall|t: int| 0 <= t < nt ==> scan_post(sv, p, (#[trigger] rg@[t]).0, rg@[t].1, lb as int, outs@[t]),
{
    let q = n / nt;
    let per = if q < usize::MAX { q + 1 } else { q };
    let mut tasks: Vec<ScanTask> = Vec::new();
    let ghost mut rg: Seq<(int, int)> = Seq::empty();
    let mut lo: usize = 0;
    let mut t: usize = 0;
    while t < nt
        invariant
            stores_wf(sv), bounds_ok(sv),
            pk@ == ps_pkeys(sv), sk@ == ps_skeys(sv), aq@ == ps_aqs(sv), cost@ == ps_costs(sv), n == ps_n(sv),
            bits_ok((**bits)@, ns as int, sv, p), dense_ok(sv, base as int, base + ns - 1), 0 <= base <= off_bound(), ns <= off_bound(),
            1 <= nt <= MAX_WORKERS, t <= nt, lo <= n,
            tasks@.len() == t, rg.len() == t,
            forall|i: int| 0 <= i < t ==> (#[trigger] tasks@[i]).pre() && tasks@[i].lo == rg[i].0 && tasks@[i].hi == rg[i].1
                && tasks@[i].sv@ == sv && tasks@[i].p@ == p && tasks@[i].st.lb == lb,
            forall|i: int| 0 <= i < t ==> (#[trigger] rg[i]).0 <= rg[i].1,
            forall|i: int| 0 < i < t ==> (#[trigger] rg[i]).0 == rg[i - 1].1,
            t == 0 ==> lo == 0,
            t > 0 ==> rg[0].0 == 0 && rg[t - 1].1 == lo,
            t == nt ==> lo == n,
        decreases nt - t,
    {
        let mut hi = if t + 1 == nt { n } else if n - lo > per { lo + per } else { n };
        // a range ends where the part key changes (so that dbgen's groups never straddle two ranges)
        while hi < n && hi > lo && pk[hi] == pk[hi - 1]
            invariant lo <= hi <= n, pk@.len() == n, t + 1 == nt ==> hi == n,
            decreases n - hi,
        {
            hi = hi + 1;
        }
        let rows = hi - lo;
        let cap = if rows >= BIG && rows < usize::MAX { rows + 1 } else { BIG };
        let st = new_state(cap, lb);
        let b2 = bits.clone();
        assert(b2 == *bits);
        let task = ScanTask { pk, sk, aq, cost, lo, hi, bits: b2, nbits: ns, base, st,
            bv: vec![0i128; cap], bk: vec![0i64; cap], sel: vec![0u32; BLK], gk: vec![0i64; BLK], gv: vec![0i128; BLK],
            sv: Ghost(sv), p: Ghost(p) };
        let ghost tasks0 = tasks@;
        let ghost rg0 = rg;
        tasks.push(task);
        proof {
            rg = rg.push((lo as int, hi as int));
            assert forall|i: int| 0 <= i < t + 1 implies (#[trigger] tasks@[i]).pre() && tasks@[i].lo == rg[i].0 && tasks@[i].hi == rg[i].1
                && tasks@[i].sv@ == sv && tasks@[i].p@ == p && tasks@[i].st.lb == lb by {
                if i < t { assert(tasks@[i] == tasks0[i] && rg[i] == rg0[i]); }
            }
            assert forall|i: int| 0 <= i < t + 1 implies (#[trigger] rg[i]).0 <= rg[i].1 by {
                if i < t { assert(rg[i] == rg0[i]); }
            }
            assert forall|i: int| 0 < i < t + 1 implies (#[trigger] rg[i]).0 == rg[i - 1].1 by {
                if i < t { assert(rg[i] == rg0[i] && rg[i - 1] == rg0[i - 1]); }
            }
        }
        lo = hi;
        t = t + 1;
    }
    let ghost tg = tasks@;
    let outs = if nt == 1 {
        let mut tasks = tasks;
        let only = tasks.pop().unwrap();
        assert(only == tg[0]);
        let o = only.run();
        let mut v: Vec<ScanOut> = Vec::new();
        v.push(o);
        v
    } else {
        match fork_join(dispatch, tasks) {
            Ok(o) => o,
            Err(e) => return Err(e),
        }
    };
    proof {
        assert forall|i: int| 0 <= i < nt implies scan_post(sv, p, (#[trigger] rg[i]).0, rg[i].1, lb as int, outs@[i]) by {
            assert(tg[i].post(outs@[i]));
        }
        reveal(ranges_ok);
    }
    Ok((outs, Ghost(rg)))
}

// ------------------------------------------------------------------------------------------ the lower bound

/// Sample blocks and rows per block of the lower-bound estimate.
pub const SAMPLE_BLOCKS: usize = 1024;
pub const SAMPLE_ROWS: usize = 64;

/// A lower bound estimate of the HAVING threshold `total * c2 / 10^10`: 15/16 of the threshold of the total
/// extrapolated from `SAMPLE_BLOCKS` blocks of `SAMPLE_ROWS` rows, one at a pseudo-random offset inside each of
/// `SAMPLE_BLOCKS` equal slices (evenly spaced blocks alias with dbgen's supplier assignment, where part `p`'s
/// suppliers follow `p mod |supplier|`, and gave estimates 15% off); `i128::MIN` (store every run) when there is no
/// positive estimate. Only a performance hint: the caller checks it against the real threshold.
fn sample_lb(sk: &'static [i64], aq: &'static [i64], cost: &'static [i128], n: usize, bw: &Vec<u64>, nbits: usize,
    base: i64, c2: i128, Ghost(sv): Ghost<StoresView>) -> i128
    requires
        stores_wf(sv), bounds_ok(sv),
        sk@ == ps_skeys(sv), aq@ == ps_aqs(sv), cost@ == ps_costs(sv), n == ps_n(sv),
        64 * bw@.len() >= nbits, 0 <= base, nbits <= i64::MAX,
{
    if n < 2 * SAMPLE_BLOCKS * SAMPLE_ROWS || c2 <= 0 {
        return i128::MIN;
    }
    let step = n / SAMPLE_BLOCKS;
    assert(step * SAMPLE_BLOCKS <= n && step >= 2 * SAMPLE_ROWS) by (nonlinear_arith)
        requires step == n / SAMPLE_BLOCKS, n >= 2 * SAMPLE_BLOCKS * SAMPLE_ROWS;
    let mut s: i128 = 0;
    let mut i: usize = 0;
    while i < SAMPLE_BLOCKS
        invariant
            stores_wf(sv), bounds_ok(sv),
            sk@ == ps_skeys(sv), aq@ == ps_aqs(sv), cost@ == ps_costs(sv), n == ps_n(sv),
            64 * bw@.len() >= nbits, 0 <= base, nbits <= i64::MAX,
            step * SAMPLE_BLOCKS <= n, step >= 2 * SAMPLE_ROWS, i <= SAMPLE_BLOCKS,
        decreases SAMPLE_BLOCKS - i,
    {
        assert(i * step + step <= n) by (nonlinear_arith)
            requires i < SAMPLE_BLOCKS, step * SAMPLE_BLOCKS <= n;
        // a pseudo-random offset (Fibonacci hashing of the slice number) inside slice `i`
        let jitter = ((i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15u64) % ((step - SAMPLE_ROWS) as u64)) as usize;
        let lo = i * step + jitter;
        assert(lo + SAMPLE_ROWS <= n);
        let mut c = lo;
        while c < lo + SAMPLE_ROWS
            invariant
                stores_wf(sv), bounds_ok(sv),
                sk@ == ps_skeys(sv), aq@ == ps_aqs(sv), cost@ == ps_costs(sv), n == ps_n(sv),
                64 * bw@.len() >= nbits, 0 <= base, nbits <= i64::MAX, lo <= c <= lo + SAMPLE_ROWS, lo + SAMPLE_ROWS <= n,
            decreases lo + SAMPLE_ROWS - c,
        {
            let x = sk[c];
            if x >= base && x - base < nbits as i64 {
                let o = (x - base) as usize;
                assert(o / 64 < bw@.len()) by (nonlinear_arith) requires o < nbits, 64 * bw@.len() >= nbits;
                if (bw[o / 64] >> ((o % 64) as u64)) & 1u64 == 1u64 {
                    proof {
                        assert(-cost_bound() < ps_costs(sv)[c as int] < cost_bound());
                        lemma_product_bound(ps_costs(sv)[c as int] as int, ps_aqs(sv)[c as int] as int);
                    }
                    let v = cost[c] * (aq[c] as i128);
                    match s.checked_add(v) {
                        Some(t) => { s = t; },
                        None => { return i128::MIN; },
                    }
                }
            }
            c = c + 1;
        }
        i = i + 1;
    }
    if s <= 0 {
        return i128::MIN;
    }
    // the estimated total: s * n / (SAMPLE_BLOCKS * SAMPLE_ROWS)
    let sn = match s.checked_mul(n as i128) {
        Some(t) => t,
        None => { return i128::MIN; },
    };
    let est = sn / ((SAMPLE_BLOCKS * SAMPLE_ROWS) as i128);
    let est_low = est / 16 * 15;
    match est_low.checked_mul(c2) {
        Some(t) => t / 10_000_000_000,
        None => i128::MIN,
    }
}

// ------------------------------------------------------------------------------------------ the combination

/// Combination verdicts: the run lists are the groups; the absolute mass leaves `i128`; take the general path.
pub const RUNS: u8 = 0;
pub const MASS: u8 = 1;
pub const GENERAL: u8 = 2;

/// The combination of the ranges' outcomes.
pub struct Combined {
    pub verdict: u8,
    pub total: i128,
    pub mass: i128,
    /// Each range's run list, and the concatenations of the first `t` of them.
    pub rss: Ghost<Seq<Seq<(int, int)>>>,
    pub pre: Ghost<Seq<Seq<(int, int)>>>,
}

/// What the combination establishes.
pub open spec fn combined_ok(sv: StoresView, p: Seq<u8>, n: int, lb: int, outs: Seq<ScanOut>, c: Combined) -> bool {
    let rss = c.rss@;
    let pre = c.pre@;
    &&& c.verdict == MASS ==> rsum(sv, p, t_absv(sv), 0, n) > imax()
    &&& c.verdict == RUNS ==> {
        &&& rss.len() == outs.len() && pre.len() == outs.len() + 1
        &&& forall|t: int| 0 <= t < outs.len() ==> (#[trigger] outs[t]).status == GO && rss[t] == outs[t].all@
            && outs[t].list.wf() && desc(outs[t].list.view())
            && outs[t].list.view().to_multiset() == above(outs[t].all@, lb).to_multiset()
        &&& pre[0] == Seq::<(int, int)>::empty()
        &&& forall|t: int| 0 <= t < outs.len() ==> #[trigger] pre[t + 1] == pre[t] + rss[t]
        &&& runs_ok(sv, p, 0, n, pre[outs.len() as int])
        &&& strict(pre[outs.len() as int])
        &&& c.total == rsum(sv, p, t_val(sv), 0, n)
        &&& c.mass == rsum(sv, p, t_absv(sv), 0, n)
    }
}

/// The combination's state after the first `t` ranges (all done, with increasing keys).
#[verifier::opaque]
pub open spec fn runs_inv(sv: StoresView, p: Seq<u8>, lb: int, rg: Seq<(int, int)>, outs: Seq<ScanOut>, t: int,
    rss: Seq<Seq<(int, int)>>, pre: Seq<Seq<(int, int)>>, total: i128, mass: i128, have_prev: bool, prev_last: i64) -> bool
{
    let pos = if t == 0 { 0 } else { rg[t - 1].1 };
    &&& rss.len() == t && pre.len() == t + 1
    &&& forall|i: int| 0 <= i < t ==> (#[trigger] outs[i]).status == GO && rss[i] == outs[i].all@
        && outs[i].list.wf() && desc(outs[i].list.view())
        && outs[i].list.view().to_multiset() == above(outs[i].all@, lb).to_multiset()
    &&& pre[0] == Seq::<(int, int)>::empty()
    &&& forall|i: int| 0 <= i < t ==> #[trigger] pre[i + 1] == pre[i] + rss[i]
    &&& runs_ok(sv, p, 0, pos, pre[t])
    &&& strict(pre[t])
    &&& total == rsum(sv, p, t_val(sv), 0, pos)
    &&& mass == rsum(sv, p, t_absv(sv), 0, pos)
    &&& have_prev == (pre[t].len() > 0)
    &&& have_prev ==> prev_last == pre[t].last().1
}

/// One more done range with increasing keys, above the previous ones.
proof fn lemma_runs_step(sv: StoresView, p: Seq<u8>, lb: int, rg: Seq<(int, int)>, outs: Seq<ScanOut>, t: int,
    rss: Seq<Seq<(int, int)>>, pre: Seq<Seq<(int, int)>>, total: i128, mass: i128, have_prev: bool,
    prev_last: i64, lo: int, hi: int)
    requires
        runs_inv(sv, p, lb, rg, outs, t, rss, pre, total, mass, have_prev, prev_last),
        0 <= t < outs.len(), t < rg.len(), rg[t] == (lo, hi), lo == (if t == 0 { 0 } else { rg[t - 1].1 }), 0 <= lo <= hi,
        outs[t].status == GO, outs[t].sorted, out_done(sv, p, lo, hi, lb, outs[t]),
        outs[t].mass <= i128::MAX - mass,
        !(outs[t].any && have_prev && prev_last >= outs[t].first_key),
    ensures ({
        let o = outs[t];
        let rs = o.all@;
        let have2 = have_prev || o.any;
        let last2 = if o.any { o.last_key } else { prev_last };
        &&& i128::MIN <= total + o.total <= i128::MAX
        &&& runs_inv(sv, p, lb, rg, outs, t + 1, rss.push(rs), pre.push(pre[t] + rs), (total + o.total) as i128,
            (mass + o.mass) as i128, have2, last2)
    }),
{
    reveal(runs_inv);
    let o = outs[t];
    let rs = o.all@;
    let a = pre[t];
    lemma_rsum_split(sv, p, t_absv(sv), 0, lo, hi);
    lemma_rsum_split(sv, p, t_val(sv), 0, lo, hi);
    lemma_rsum_bounds(sv, p, 0, 0, hi);
    lemma_rsum_nonneg(sv, p, t_absv(sv), 0, lo);
    lemma_runs_concat(sv, p, 0, lo, hi, a, rs);
    if a.len() > 0 && rs.len() > 0 {
        assert forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < rs.len() implies (#[trigger] a[i]).1 < (#[trigger] rs[j]).1 by {
            if i < a.len() - 1 { assert(a[i].1 < a[a.len() - 1].1); }
            if j > 0 { assert(rs[0].1 < rs[j].1); }
        }
    }
    lemma_strict_concat(a, rs);
    let rss2 = rss.push(rs);
    let pre2 = pre.push(a + rs);
    assert forall|i: int| 0 <= i < t + 1 implies (#[trigger] outs[i]).status == GO && rss2[i] == outs[i].all@
        && outs[i].list.wf() && desc(outs[i].list.view())
        && outs[i].list.view().to_multiset() == above(outs[i].all@, lb).to_multiset() by {
        if i < t { assert(rss2[i] == rss[i]); }
    }
    assert forall|i: int| 0 <= i < t + 1 implies #[trigger] pre2[i + 1] == pre2[i] + rss2[i] by {
        if i < t { assert(pre2[i + 1] == pre[i + 1] && pre2[i] == pre[i] && rss2[i] == rss[i]); }
    }
    if rs.len() > 0 {
        assert((a + rs).last() == rs.last());
    } else {
        assert(a + rs =~= a);
    }
    assert(rg[t].1 == hi);
}

/// The visible facts of the combination's state.
proof fn lemma_runs_facts(sv: StoresView, p: Seq<u8>, lb: int, rg: Seq<(int, int)>, outs: Seq<ScanOut>, t: int,
    rss: Seq<Seq<(int, int)>>, pre: Seq<Seq<(int, int)>>, total: i128, mass: i128, have_prev: bool, prev_last: i64)
    requires runs_inv(sv, p, lb, rg, outs, t, rss, pre, total, mass, have_prev, prev_last),
    ensures
        pre.len() == t + 1, rss.len() == t,
        mass == rsum(sv, p, t_absv(sv), 0, if t == 0 { 0 } else { rg[t - 1].1 }),
        0 <= mass,
{
    reveal(runs_inv);
    lemma_rsum_nonneg(sv, p, t_absv(sv), 0, if t == 0 { 0 } else { rg[t - 1].1 });
}

/// No range yet.
proof fn lemma_runs_start(sv: StoresView, p: Seq<u8>, lb: int, rg: Seq<(int, int)>, outs: Seq<ScanOut>)
    ensures runs_inv(sv, p, lb, rg, outs, 0, Seq::empty(), seq![Seq::<(int, int)>::empty()], 0, 0, false, 0),
{
    reveal(runs_inv);
    lemma_runs_empty(sv, p, 0);
}

/// All ranges: the combination's result.
proof fn lemma_runs_end(sv: StoresView, p: Seq<u8>, lb: int, rg: Seq<(int, int)>, n: int, outs: Seq<ScanOut>, c: Combined,
    have_prev: bool, prev_last: i64)
    requires
        ranges_ok(rg, n), outs.len() == rg.len(), c.verdict == RUNS,
        runs_inv(sv, p, lb, rg, outs, outs.len() as int, c.rss@, c.pre@, c.total, c.mass, have_prev, prev_last),
    ensures combined_ok(sv, p, n, lb, outs, c),
{
    reveal(runs_inv);
    reveal(ranges_ok);
    assert(rg[outs.len() - 1].1 == n);
}

/// Check the ranges' outcomes and combine their run lists, totals and masses.
fn combine(outs: &Vec<ScanOut>, Ghost(rg): Ghost<Seq<(int, int)>>, n: usize, Ghost(lb): Ghost<int>,
    Ghost(sv): Ghost<StoresView>, Ghost(p): Ghost<Seq<u8>>) -> (c: Combined)
    requires
        stores_wf(sv), n == ps_n(sv),
        outs@.len() == rg.len(), ranges_ok(rg, n as int),
        forall|t: int| 0 <= t < rg.len() ==> scan_post(sv, p, (#[trigger] rg[t]).0, rg[t].1, lb, outs@[t]),
    ensures combined_ok(sv, p, n as int, lb, outs@, c),
{
    let nt = outs.len();
    let mut verdict = RUNS;
    let mut total: i128 = 0;
    let mut mass: i128 = 0;
    let mut have_prev = false;
    let mut prev_last: i64 = 0;
    let ghost mut rss: Seq<Seq<(int, int)>> = Seq::empty();
    let ghost mut pre: Seq<Seq<(int, int)>> = seq![Seq::<(int, int)>::empty()];
    let mut t: usize = 0;
    proof {
        lemma_runs_start(sv, p, lb, rg, outs@);
    }
    while t < nt
        invariant
            stores_wf(sv), n == ps_n(sv),
            nt == outs@.len(), nt == rg.len(), ranges_ok(rg, n as int), t <= nt,
            forall|i: int| 0 <= i < rg.len() ==> scan_post(sv, p, (#[trigger] rg[i]).0, rg[i].1, lb, outs@[i]),
            verdict == RUNS || verdict == MASS || verdict == GENERAL,
            verdict == MASS ==> rsum(sv, p, t_absv(sv), 0, n as int) > imax(),
            verdict == RUNS ==> runs_inv(sv, p, lb, rg, outs@, t as int, rss, pre, total, mass, have_prev, prev_last),
        decreases nt - t,
    {
        let o = &outs[t];
        let ghost (lo, hi) = rg[t as int];
        proof {
            assert(scan_post(sv, p, lo, hi, lb, outs@[t as int]));
            lemma_scan_post(sv, p, lo, hi, lb, outs@[t as int]);
            lemma_range_at(rg, n as int, t as int);
            if verdict == RUNS {
                lemma_runs_facts(sv, p, lb, rg, outs@, t as int, rss, pre, total, mass, have_prev, prev_last);
            }
        }
        if verdict == RUNS {
            if o.status == OVER {
                proof {
                    lemma_mass_sub(sv, p, 0, lo, hi, n as int);
                }
                verdict = MASS;
            } else if o.status != GO || !o.sorted {
                verdict = GENERAL;
            } else if o.mass > i128::MAX - mass {
                proof {
                    lemma_rsum_split(sv, p, t_absv(sv), 0, lo, hi);
                    lemma_mass_sub(sv, p, 0, 0, hi, n as int);
                }
                verdict = MASS;
            } else if o.any && have_prev && prev_last >= o.first_key {
                verdict = GENERAL;
            } else {
                proof {
                    lemma_runs_step(sv, p, lb, rg, outs@, t as int, rss, pre, total, mass, have_prev, prev_last, lo, hi);
                }
                let ghost rs = o.all@;
                mass = mass + o.mass;
                total = total + o.total;
                if o.any {
                    have_prev = true;
                    prev_last = o.last_key;
                }
                proof {
                    pre = pre.push(pre[t as int] + rs);
                    rss = rss.push(rs);
                }
            }
        }
        t = t + 1;
    }
    let c = Combined { verdict, total, mass, rss: Ghost(rss), pre: Ghost(pre) };
    proof {
        if verdict == RUNS {
            lemma_runs_end(sv, p, lb, rg, n as int, outs@, c, have_prev, prev_last);
        }
    }
    c
}

/// Range `t`: it starts where the previous one ends (at 0 for the first), lies inside `[0, n)`, and the last
/// one ends at `n`.
proof fn lemma_range_at(rg: Seq<(int, int)>, n: int, t: int)
    requires ranges_ok(rg, n), 0 <= t < rg.len(),
    ensures
        rg[t].0 == (if t == 0 { 0 } else { rg[t - 1].1 }),
        0 <= rg[t].0 <= rg[t].1 <= n,
        t == rg.len() - 1 ==> rg[t].1 == n,
{
    reveal(ranges_ok);
    lemma_range_bounds(rg, n, t);
}

/// Every range lies inside `[0, n)`.
proof fn lemma_range_bounds(rg: Seq<(int, int)>, n: int, t: int)
    requires
        0 <= t < rg.len(), rg[0].0 == 0, rg[rg.len() - 1].1 == n,
        forall|i: int| 0 <= i < rg.len() ==> (#[trigger] rg[i]).0 <= rg[i].1,
        forall|i: int| 0 < i < rg.len() ==> (#[trigger] rg[i]).0 == rg[i - 1].1,
    ensures 0 <= rg[t].0 <= rg[t].1 <= n,
    decreases rg.len() - t,
{
    if t < rg.len() - 1 {
        lemma_range_bounds(rg, n, t + 1);
        assert(rg[t + 1].0 == rg[t].1);
    }
    lemma_range_lo(rg, t);
}

/// Every range starts at or after 0.
proof fn lemma_range_lo(rg: Seq<(int, int)>, t: int)
    requires
        0 <= t < rg.len(), rg[0].0 == 0,
        forall|i: int| 0 <= i < rg.len() ==> (#[trigger] rg[i]).0 <= rg[i].1,
        forall|i: int| 0 < i < rg.len() ==> (#[trigger] rg[i]).0 == rg[i - 1].1,
    ensures 0 <= rg[t].0,
    decreases t,
{
    if t > 0 {
        lemma_range_lo(rg, t - 1);
        assert(rg[t].0 == rg[t - 1].1);
    }
}

// ------------------------------------------------------------------------------------------ HAVING and ORDER BY

/// Each range's sorted list cut after its last pair above `thr` (with `lb <= thr`): the pairs of range `t` above
/// the threshold, sorted by sum; `None` when the total count of pairs leaves `usize`.
fn cut_lists(outs: Vec<ScanOut>, thr: i128, Ghost(lb): Ghost<int>, Ghost(rss): Ghost<Seq<Seq<(int, int)>>>)
    -> (r: Option<Vec<Sorted>>)
    requires
        lb <= thr, rss.len() == outs@.len(),
        forall|t: int| 0 <= t < outs@.len() ==> (#[trigger] outs@[t]).list.wf() && desc(outs@[t].list.view())
            && outs@[t].list.view().to_multiset() == above(rss[t], lb).to_multiset(),
    ensures
        r matches Some(fs) ==> fs@.len() == rss.len() && ms_all(fs@).len() <= usize::MAX && forall|t: int| 0 <= t < rss.len() ==>
            (#[trigger] fs@[t]).wf() && desc(fs@[t].view()) && fs@[t].view().to_multiset() == above(rss[t], thr as int).to_multiset(),
{
    let nt = outs.len();
    let ghost o0 = outs@;
    let mut outs = outs;
    let mut fs: Vec<Sorted> = Vec::new();
    let mut count: usize = 0;
    let mut t: usize = 0;
    while t < nt
        invariant
            nt == o0.len(), t <= nt, rss.len() == nt, lb <= thr,
            outs@ == o0.subrange(t as int, nt as int),
            forall|i: int| 0 <= i < nt ==> (#[trigger] o0[i]).list.wf() && desc(o0[i].list.view())
                && o0[i].list.view().to_multiset() == above(rss[i], lb).to_multiset(),
            fs@.len() == t, count == n_all(fs@),
            forall|i: int| 0 <= i < t ==> (#[trigger] fs@[i]).wf() && desc(fs@[i].view())
                && fs@[i].view().to_multiset() == above(rss[i], thr as int).to_multiset(),
        decreases nt - t,
    {
        let o = outs.remove(0);
        proof {
            assert(o == o0[t as int]);
            assert(outs@ =~= o0.subrange(t + 1, nt as int));
        }
        let ScanOut { list, status: _, sorted: _, any: _, first_key: _, last_key: _, total: _, mass: _, all: _ } = o;
        let Sorted { v, k, n } = list;
        let ghost whole = pairs(v@, k@, 0, n as int);
        let mut q: usize = 0;
        while q < n && v[q] > thr
            invariant
                q <= n, n <= v@.len(), v@.len() == k@.len(), whole == pairs(v@, k@, 0, n as int),
                forall|i: int| 0 <= i < q ==> (#[trigger] whole[i]).0 > thr,
            decreases n - q,
        {
            q = q + 1;
        }
        let f = Sorted { v, k, n: q };
        proof {
            lemma_desc_prefix(whole, q as int, thr as int);
            assert(f.view() =~= whole.take(q as int));
            lemma_above_ms(whole, above(rss[t as int], lb), thr as int);
            lemma_above_above(rss[t as int], lb, thr as int);
        }
        if q > usize::MAX - count {
            return None;
        }
        let ghost fs0 = fs@;
        fs.push(f);
        count = count + q;
        proof {
            assert(fs@.drop_last() =~= fs0);
            assert forall|i: int| 0 <= i < t + 1 implies (#[trigger] fs@[i]).wf() && desc(fs@[i].view())
                && fs@[i].view().to_multiset() == above(rss[i], thr as int).to_multiset() by {
                if i < t { assert(fs@[i] == fs0[i]); }
            }
        }
        t = t + 1;
    }
    proof {
        lemma_n_all(fs@);
    }
    Some(fs)
}

/// The multiset of the first `t` sorted lists is that of the passing runs of the first `t` ranges.
proof fn lemma_ms_prefix(fs: Seq<Sorted>, rss: Seq<Seq<(int, int)>>, pre: Seq<Seq<(int, int)>>, thr: int, t: int)
    requires
        fs.len() == rss.len(), pre.len() == rss.len() + 1, 0 <= t <= fs.len(),
        pre[0] == Seq::<(int, int)>::empty(),
        forall|i: int| 0 <= i < rss.len() ==> #[trigger] pre[i + 1] == pre[i] + rss[i],
        forall|i: int| 0 <= i < rss.len() ==> (#[trigger] fs[i]).view().to_multiset() == above(rss[i], thr).to_multiset(),
    ensures ms_all(fs.take(t)) == above(pre[t], thr).to_multiset(),
    decreases t,
{
    broadcast use vstd::multiset::group_multiset_axioms, vstd::seq_lib::group_to_multiset_ensures;
    if t == 0 {
        assert(fs.take(0) =~= Seq::<Sorted>::empty());
        assert(above(pre[0], thr) =~= Seq::<(int, int)>::empty());
        assert(above(pre[0], thr).to_multiset() =~= vstd::multiset::Multiset::<(int, int)>::empty());
    } else {
        lemma_ms_prefix(fs, rss, pre, thr, t - 1);
        assert(fs.take(t).drop_last() =~= fs.take(t - 1));
        assert(fs.take(t).last() == fs[t - 1]);
        let i = t - 1;
        assert(pre[i + 1] == pre[i] + rss[i]);
        assert(i + 1 == t);
        lemma_above_concat(pre[t - 1], rss[t - 1], thr);
        vstd::seq_lib::lemma_multiset_commutative(above(pre[t - 1], thr), above(rss[t - 1], thr));
    }
}

// ------------------------------------------------------------------------------------------ one attempt

/// Bucket tasks of the parallel merge (at most the worker count).
pub const MERGE_BUCKETS: usize = 8;

/// The fast path with lower bound `lb`: `None` when the threshold is below `lb` (some passing group may not have
/// been stored; the caller retries with a smaller bound), otherwise the answer.
fn attempt(pk: &'static [i64], sk: &'static [i64], aq: &'static [i64], cost: &'static [i128], n: usize,
    skeys: &'static [i64], ns: usize, bits: &Arc<Vec<u64>>, base: i64, c2: i128, lb: i128, workers: usize,
    dispatch: &mut Dispatch, Ghost(sv): Ghost<StoresView>, Ghost(pp): Ghost<Seq<u8>>) -> (r: Option<Result<Answer, QueryError>>)
    requires
        stores_wf(sv), keys_ok(sv), bounds_ok(sv),
        pk@ == ps_pkeys(sv), sk@ == ps_skeys(sv), aq@ == ps_aqs(sv), cost@ == ps_costs(sv), n == ps_n(sv),
        skeys@ == s_keys(sv), ns == supp_n(sv),
        bits_ok((**bits)@, ns as int, sv, pp), dense_ok(sv, base as int, base + ns - 1), 0 <= base <= off_bound(), ns <= off_bound(),
        -100000000000000000000000000000000000000 < c2 < 100000000000000000000000000000000000000,
        1 <= workers <= MAX_WORKERS,
    ensures r matches Some(a) ==> answer_meets(sv, params_of(pp, c2 as int), a),
{
    let (outs, Ghost(rg)) = match scan_all(pk, sk, aq, cost, n, bits, ns, base, workers, lb, dispatch, Ghost(sv), Ghost(pp)) {
        Ok(x) => x,
        Err(e) => return Some(Err(QueryError::WorkerFailed(e))),
    };
    let comb = combine(&outs, Ghost(rg), n, Ghost(lb as int), Ghost(sv), Ghost(pp));
    if comb.verdict == MASS {
        proof {
            lemma_some_row(sv, pp, 0, n as int);
            lemma_answer_capacity(sv, pp, c2 as int);
        }
        return Some(Ok(Answer::Capacity));
    }
    if comb.verdict != RUNS {
        let a = general_answer(pk, sk, aq, cost, n, skeys, ns, &**bits, c2, Ghost(sv), Ghost(pp));
        return Some(Ok(a));
    }
    let ghost rss = comb.rss@;
    let ghost pre = comb.pre@;
    let ghost rstar = pre[outs@.len() as int];
    let thr = match threshold(comb.total, c2) {
        Some(t) => t,
        None => {
            proof {
                lemma_some_row(sv, pp, 0, n as int);
                lemma_answer_capacity(sv, pp, c2 as int);
            }
            return Some(Ok(Answer::Capacity));
        },
    };
    if thr < lb {
        return None;
    }
    let fs = match cut_lists(outs, thr, Ghost(lb as int), Ghost(rss)) {
        Some(x) => x,
        None => {
            let a = general_answer(pk, sk, aq, cost, n, skeys, ns, &**bits, c2, Ghost(sv), Ghost(pp));
            return Some(Ok(a));
        },
    };
    proof {
        lemma_ms_prefix(fs@, rss, pre, thr as int, fs@.len() as int);
        assert(fs@.take(fs@.len() as int) =~= fs@);
        assert forall|i: int| 0 <= i < fs@.len() implies (#[trigger] fs@[i]).wf() && desc(fs@[i].view()) by {}
    }
    // ORDER BY: the sorted lists merged by value buckets in parallel, or on this thread
    let ghost fsv = fs@;
    let f = if fs.len() >= 2 && workers >= 2 {
        let nb = if workers > MERGE_BUCKETS { MERGE_BUCKETS } else { workers };
        match parallel_merge(fs, nb, dispatch) {
            Ok(x) => x,
            Err(e) => return Some(Err(QueryError::WorkerFailed(e))),
        }
    } else {
        merge_all(fs)
    };
    assert(f.wf() && desc(f.view()) && f.view().to_multiset() == ms_all(fsv));
    let ghost fv = f.view();
    let c = columns_of(f);
    proof {
        // the runs are the groups: the passing ones are complete and distinct
        lemma_strict_distinct(rstar);
        assert forall|i: int| 0 <= i < rstar.len() implies grp_ok(sv, pp, #[trigger] rstar[i]) by {
            lemma_strict_entry(sv, pp, 0, n as int, rstar, i);
        }
        assert forall|k: int| rsum(sv, pp, t_cnt(sv, k), 0, ps_n(sv) as int) > 0
            implies exists|i: int| 0 <= i < rstar.len() && #[trigger] rstar[i].1 == k by {
            assert(rs_has(rstar, k));
        }
        lemma_list_from_table(sv, pp, thr as int, rstar);
        lemma_answer_rows(sv, pp, c2 as int, thr as int, above(rstar, thr as int), fv);
    }
    Some(Ok(Answer::Columns(c)))
}

// ------------------------------------------------------------------------------------------ the entry

/// TPC-H Q11 over the flat storages (see the module comment).
pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures
        answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    proof {
        let db0 = choose|db: Database| #[trigger] bound_db(sv, db);
        lemma_tables(sv, db0);
        lemma_keys(sv, db0);
        lemma_bounds(sv, db0);
    }
    let p = params.p0;
    let c2 = params.p1;
    let ghost pp = p@;
    proof {
        assert(params@ =~= params_of(pp, c2 as int));
    }
    let want = nations_named(stores, p, Ghost(sv));
    // the columns, as whole stored parts
    let ns = stores.flat_supplier.part_len(si::S_SUPPKEY);
    let skeys = stores.flat_supplier.extent_i64(si::S_SUPPKEY, 0, ns);
    let snk = stores.flat_supplier.extent_i64(si::S_NATIONKEY, 0, ns);
    let n = stores.flat_partsupp.part_len(psi::PS_PARTKEY);
    let pk = stores.flat_partsupp.extent_i64(psi::PS_PARTKEY, 0, n);
    let sk = stores.flat_partsupp.extent_i64(psi::PS_SUPPKEY, 0, n);
    let aq = stores.flat_partsupp.extent_i64(psi::PS_AVAILQTY, 0, n);
    let cost = stores.flat_partsupp.extent_i128(psi::PS_SUPPLYCOST, 0, n);
    proof {
        assert(skeys@ =~= s_keys(sv));
        assert(snk@ =~= s_nks(sv));
        assert(pk@ =~= ps_pkeys(sv));
        assert(sk@ =~= ps_skeys(sv));
        assert(aq@ =~= ps_aqs(sv));
        assert(cost@ =~= ps_costs(sv));
    }
    // the supplier bitmap
    let base: i64 = if ns > 0 { skeys[0] } else { 0 };
    let stasks = if workers > 8 { 8 } else { workers };
    let (bits, dense) = match supplier_bits(skeys, snk, ns, base, want, stasks, dispatch, Ghost(sv), Ghost(pp)) {
        Ok(x) => x,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    if ns == 0 || !dense || base < 0 || base > 0x4000_0000_0000_0000 || ns as u64 > 0x4000_0000_0000_0000u64 {
        let a = general_answer(pk, sk, aq, cost, n, skeys, ns, &bits, c2, Ghost(sv), Ghost(pp));
        return Ok(a);
    }
    proof {
        assert(dense_ok(sv, base as int, base + ns - 1));
    }
    // a lower bound of the HAVING threshold, then the scan (again with no bound when it was too high)
    let lb = sample_lb(sk, aq, cost, n, &bits, ns, base, c2, Ghost(sv));
    let bits = Arc::new(bits);
    match attempt(pk, sk, aq, cost, n, skeys, ns, &bits, base, c2, lb, workers, dispatch, Ghost(sv), Ghost(pp)) {
        Some(a) => a,
        None => match attempt(pk, sk, aq, cost, n, skeys, ns, &bits, base, c2, i128::MIN, workers, dispatch, Ghost(sv), Ghost(pp)) {
            Some(a) => a,
            None => Ok(general_answer(pk, sk, aq, cost, n, skeys, ns, &*bits, c2, Ghost(sv), Ghost(pp))),
        },
    }
}

} // verus!
