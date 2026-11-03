//! The order of the tasks' runs: when it never decreases from task to task (`runs_in_order`, checked on each task's
//! first and last run), no order below a task's last run is hit after the task (`lemma_tail_zero`).
use vstd::prelude::*;
use crate::gendb_entry::stores::StoresView;
use crate::agent::tables::*;
use crate::agent::normal_form::*;
use crate::agent::runs::*;
use crate::agent::scan::*;

verus! {

/// Mass bounds of adjacent ranges combine.
pub proof fn lemma_mass_split(sv: StoresView, seg: Seq<u8>, dl: int, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi, mass_bounded(sv, seg, dl, lo, mid), mass_bounded(sv, seg, dl, mid, hi),
    ensures mass_bounded(sv, seg, dl, lo, hi),
{
    assert forall|j: int| 0 <= j < n_o(sv) implies
        #[trigger] order_abs(sv, seg, dl, j, lo, hi) <= order_count(sv, seg, dl, j, lo, hi) * (VMAX as int) by {
        lemma_order_split(sv, seg, dl, j, lo, mid, hi);
        assert(order_abs(sv, seg, dl, j, lo, mid) <= order_count(sv, seg, dl, j, lo, mid) * (VMAX as int));
        assert(order_abs(sv, seg, dl, j, mid, hi) <= order_count(sv, seg, dl, j, mid, hi) * (VMAX as int));
        let (a, b) = (order_count(sv, seg, dl, j, lo, mid) as int, order_count(sv, seg, dl, j, mid, hi) as int);
        assert((a + b) * (VMAX as int) == a * (VMAX as int) + b * (VMAX as int)) by (nonlinear_arith);
    }
}

/// The runs of the tasks from `t` on are at least `v`.
pub open spec fn tail_above(outs: Seq<ScanOut>, t: int, v: int) -> bool {
    forall|u: int, y: int| t <= u < outs.len() && 0 <= y < outs[u].n ==> v <= #[trigger] outs[u].rj@[y]
}

/// No order below `v` is hit in the rows from `hi` on.
pub open spec fn tail_zero(sv: StoresView, seg: Seq<u8>, dl: int, hi: int, v: int) -> bool {
    forall|j: int| 0 <= j < n_o(sv) && j < v ==> #[trigger] order_count(sv, seg, dl, j, hi, n_l(sv)) == 0
}

/// Every task's ranges from `k` on: no hit of an order below the runs of these tasks.
pub proof fn lemma_tail_count(outs: Seq<ScanOut>, bounds: Seq<int>, sv: StoresView, seg: Seq<u8>, dl: int, k: int, v: int, j: int)
    requires
        bounds_ok(bounds, n_l(sv)), bounds.len() == outs.len() + 1,
        forall|u: int| 0 <= u < outs.len() ==> scan_out_ok(#[trigger] outs[u], sv, seg, dl, bounds[u], bounds[u + 1]),
        0 <= k <= outs.len(), tail_above(outs, k, v), 0 <= j < n_o(sv), j < v,
    ensures order_count(sv, seg, dl, j, bounds[k], bounds[outs.len() as int]) == 0,
    decreases outs.len() - k,
{
    let nt = outs.len() as int;
    if k == nt {
        lemma_order_bounds(sv, seg, dl, j, bounds[k], bounds[k]);
    } else {
        lemma_tail_count(outs, bounds, sv, seg, dl, k + 1, v, j);
        lemma_bounds_mono(bounds, k + 1, nt);
        assert(bounds[k] <= bounds[k + 1]);
        lemma_order_split(sv, seg, dl, j, bounds[k], bounds[k + 1], bounds[nt]);
        assert(scan_out_ok(outs[k], sv, seg, dl, bounds[k], bounds[k + 1]));
        if order_count(sv, seg, dl, j, bounds[k], bounds[k + 1]) > 0 {
            let y = choose|y: int| 0 <= y < outs[k].n && outs[k].rj@[y] == j;
            assert(v <= outs[k].rj@[y]);
        }
    }
}

pub proof fn lemma_tail_zero(outs: Seq<ScanOut>, bounds: Seq<int>, sv: StoresView, seg: Seq<u8>, dl: int, k: int, v: int)
    requires
        bounds_ok(bounds, n_l(sv)), bounds.len() == outs.len() + 1,
        forall|u: int| 0 <= u < outs.len() ==> scan_out_ok(#[trigger] outs[u], sv, seg, dl, bounds[u], bounds[u + 1]),
        0 <= k <= outs.len(), tail_above(outs, k, v),
    ensures tail_zero(sv, seg, dl, bounds[k], v),
{
    assert forall|j: int| 0 <= j < n_o(sv) && j < v implies #[trigger] order_count(sv, seg, dl, j, bounds[k], n_l(sv)) == 0 by {
        lemma_tail_count(outs, bounds, sv, seg, dl, k, v, j);
    }
}

/// The tasks' row ranges: consecutive, covering `0..nl`.
pub open spec fn bounds_ok(bounds: Seq<int>, nl: int) -> bool {
    &&& bounds.len() >= 1
    &&& bounds[0] == 0
    &&& bounds.last() == nl
    &&& forall|t: int| 0 <= t < bounds.len() - 1 ==> #[trigger] bounds[t] <= bounds[t + 1]
}

/// Whether the runs never decrease from task to task (checked on each task's first and last run): then the runs of
/// the tasks after a task are at least its last run.
pub fn runs_in_order(outs: &Vec<ScanOut>, Ghost(bounds): Ghost<Seq<int>>, Ghost(sv): Ghost<StoresView>, Ghost(seg): Ghost<Seq<u8>>,
    Ghost(dl): Ghost<int>) -> (ok: bool)
    requires
        bounds.len() == outs@.len() + 1,
        forall|u: int| 0 <= u < outs@.len() ==> scan_out_ok(#[trigger] outs@[u], sv, seg, dl, bounds[u], bounds[u + 1]),
    ensures
        ok ==> forall|u: int| 0 <= u < outs@.len() && #[trigger] outs@[u].n > 0 ==>
            tail_above(outs@, u + 1, outs@[u].rj@[outs@[u].n - 1] as int),
{
    let nt = outs.len();
    let mut some = false;
    let mut minv: usize = 0;
    let mut t = nt;
    while t > 0
        invariant
            t <= nt, nt == outs@.len(), bounds.len() == outs@.len() + 1,
            forall|u: int| 0 <= u < outs@.len() ==> scan_out_ok(#[trigger] outs@[u], sv, seg, dl, bounds[u], bounds[u + 1]),
            some ==> tail_above(outs@, t as int, minv as int),
            !some ==> forall|u: int| t <= u < nt ==> #[trigger] outs@[u].n == 0,
            forall|u: int| t <= u < nt && #[trigger] outs@[u].n > 0 ==>
                tail_above(outs@, u + 1, outs@[u].rj@[outs@[u].n - 1] as int),
        decreases t,
    {
        let k = t - 1;
        let o = &outs[k];
        assert(scan_out_ok(outs@[k as int], sv, seg, dl, bounds[k as int], bounds[k + 1]));
        if o.n > 0 {
            let last = o.lj;
            if some && last > minv {
                return false;
            }
            proof {
                assert forall|u: int, y: int| k + 1 <= u < nt && 0 <= y < outs@[u].n implies last as int <= #[trigger] outs@[u].rj@[y] by {
                    if some {
                        assert(minv <= outs@[u].rj@[y]);
                    } else {
                        assert(outs@[u].n == 0);
                    }
                }
                assert(tail_above(outs@, k + 1, last as int));
                assert forall|u: int, y: int| k <= u < nt && 0 <= y < outs@[u].n implies o.rj@[0] as int <= #[trigger] outs@[u].rj@[y] by {
                    if u == k {
                        if y > 0 {
                            assert(o.rj@[0] < o.rj@[y]);
                        }
                    } else {
                        assert(last as int <= outs@[u].rj@[y]);
                        if o.n - 1 > 0 {
                            assert(o.rj@[0] < o.rj@[o.n - 1]);
                        }
                    }
                }
            }
            some = true;
            minv = o.fj;
        } else {
            proof {
                if some {
                    assert forall|u: int, y: int| k <= u < nt && 0 <= y < outs@[u].n implies minv as int <= #[trigger] outs@[u].rj@[y] by {
                        if u == k {
                            assert(outs@[u].n == 0);
                        }
                    }
                }
            }
        }
        t = k;
    }
    true
}

pub proof fn lemma_bounds_mono(bounds: Seq<int>, a: int, b: int)
    requires 0 <= a <= b < bounds.len(), forall|t: int| 0 <= t < bounds.len() - 1 ==> #[trigger] bounds[t] <= bounds[t + 1],
    ensures bounds[a] <= bounds[b],
    decreases b - a,
{
    if a < b {
        lemma_bounds_mono(bounds, a, b - 1);
        assert(bounds[b - 1] <= bounds[b]);
    }
}

} // verus!
