//! Combining the tasks' results into the top 10 groups, reading only a few runs per task.
//!
//! When the runs never decrease from task to task (checked on each task's first and last run, `runs_in_order`), an
//! order's lineitem hits all lie in the tasks where it has a run, and an *interior* run of a task (neither its first
//! nor its last) is the order's only run: its sum over the task is the order's final sum. Each task selected the top
//! 10 of its interior runs itself (`scan::ltop_ok`). Here the first and last runs of the tasks are merged (an order may
//! span tasks) and given, with the tasks' selections, to the final selection (`topk::top_step`); those are the
//! *candidates* `c`. An interior run outside its task's selection sorts no earlier than the 10th entry of that full
//! selection, whose entries are candidates: so it sorts no earlier than a *witness* `(wv, wd)` that ten distinct
//! candidates sort no later than (the best such 10th entry so far). At the end the selection is full and its last
//! entry sorts no later than the witness (`topk::lemma_top_pigeon`), so the selection is the top 10 of all groups
//! (`lemma_comb_final`), listed canonically by `qual`.
use vstd::prelude::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::link::expr::i128_max;
use crate::agent::tables::*;
use crate::agent::normal_form::*;
use crate::agent::runs::*;
use crate::agent::scan::*;
use crate::agent::topk::*;
use crate::agent::answer::*;
use crate::agent::merge::{tail_above, tail_zero, lemma_tail_zero, bounds_ok, lemma_bounds_mono, lemma_mass_split, runs_in_order};

verus! {

/// The combination's state: the selection over the candidates `c` (ghost, with sums `cs`), the open group
/// (`open`, `cj`, `csum`: the last run seen, maybe continued by the next task), and the witness.
pub struct Comb {
    pub top: Top,
    pub c: Ghost<Seq<usize>>,
    pub cs: Ghost<Seq<i128>>,
    pub open: bool,
    pub cj: usize,
    pub csum: i128,
    pub wit: Ghost<bool>,
    pub wv: Ghost<int>,
    pub wd: Ghost<int>,
    pub lw: Ghost<Seq<usize>>,
}

/// Order `j` sorts no earlier than the witness.
pub open spec fn dominated(m: Comb, sv: StoresView, ps: Seq<Literal>, j: int) -> bool {
    m.wit@ && row_cmp(m.wv@, m.wd@, fin(sv, ps)(j), odf(sv)(j)) <= 0
}

/// Ten distinct candidates sort no later than the witness.
pub open spec fn wit_ok(m: Comb, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& m.wit@ ==> m.lw@.len() == 10 && m.lw@.no_duplicates()
    &&& m.wit@ ==> forall|k: int| 0 <= k < 10 ==> m.c@.contains(#[trigger] m.lw@[k])
            && row_cmp(fin(sv, ps)(m.lw@[k] as int), odf(sv)(m.lw@[k] as int), m.wv@, m.wd@) <= 0
}

/// The candidates: final groups, each hit, and the selection is their top 10.
pub open spec fn cand_ok(m: Comb, sv: StoresView, seg: Seq<u8>, dl: int, ps: Seq<Literal>) -> bool {
    &&& scan_facts(sv, seg, dl) && seg == seg_of(ps) && dl == dl_of(ps)
    &&& groups_final(m.c@, m.cs@, sv, ps)
    &&& forall|i: int| 0 <= i < m.c@.len() ==> #[trigger] order_count(sv, seg, dl, m.c@[i] as int, 0, n_l(sv)) > 0
    &&& top_inv(m.top, m.c@, m.cs@, sv, ps)
    &&& wit_ok(m, sv, ps)
}

/// After the tasks covering rows `0..b`: the open group is the last run seen, with its sum over `0..b`; every order hit
/// in `0..b` is a candidate, the open group, or dominated; nothing above the open group is hit.
pub open spec fn comb_inv(m: Comb, sv: StoresView, seg: Seq<u8>, dl: int, ps: Seq<Literal>, b: int) -> bool {
    &&& cand_ok(m, sv, seg, dl, ps)
    &&& 0 <= b <= n_l(sv)
    &&& m.open ==> (m.cj as int) < n_o(sv) && m.csum as int == order_sum(sv, seg, dl, m.cj as int, 0, b)
            && order_count(sv, seg, dl, m.cj as int, 0, b) > 0
    &&& m.open ==> forall|i: int| 0 <= i < m.c@.len() ==> #[trigger] m.c@[i] < m.cj
    &&& !m.open ==> m.c@.len() == 0 && !m.wit@
    &&& forall|j: int| 0 <= j < n_o(sv) && #[trigger] order_count(sv, seg, dl, j, 0, b) > 0 ==>
            m.c@.contains(j as usize) || (m.open && j == m.cj) || dominated(m, sv, ps, j)
    &&& mass_bounded(sv, seg, dl, 0, b)
    &&& m.open ==> forall|j: int| m.cj < j < n_o(sv) ==> #[trigger] order_count(sv, seg, dl, j, 0, b) == 0
    &&& !m.open ==> forall|j: int| 0 <= j < n_o(sv) ==> #[trigger] order_count(sv, seg, dl, j, 0, b) == 0
}

/// After the first run of the task over `lo..hi`, now the open group (its sum over `0..hi`: it has no other run).
pub open spec fn mid_inv(m: Comb, sv: StoresView, seg: Seq<u8>, dl: int, ps: Seq<Literal>, lo: int, hi: int) -> bool {
    &&& cand_ok(m, sv, seg, dl, ps)
    &&& 0 <= lo <= hi <= n_l(sv)
    &&& m.open && (m.cj as int) < n_o(sv)
    &&& m.csum as int == order_sum(sv, seg, dl, m.cj as int, 0, hi) && order_count(sv, seg, dl, m.cj as int, 0, hi) > 0
    &&& forall|i: int| 0 <= i < m.c@.len() ==> #[trigger] m.c@[i] < m.cj
    &&& forall|j: int| 0 <= j < n_o(sv) && #[trigger] order_count(sv, seg, dl, j, 0, lo) > 0 ==>
            m.c@.contains(j as usize) || j == m.cj || dominated(m, sv, ps, j)
    &&& mass_bounded(sv, seg, dl, 0, lo)
    &&& forall|j: int| m.cj < j < n_o(sv) ==> #[trigger] order_count(sv, seg, dl, j, 0, lo) == 0
}

pub fn comb_new(Ghost(sv): Ghost<StoresView>, Ghost(seg): Ghost<Seq<u8>>, Ghost(dl): Ghost<int>, Ghost(ps): Ghost<Seq<Literal>>) -> (m: Comb)
    requires scan_facts(sv, seg, dl), seg == seg_of(ps), dl == dl_of(ps),
    ensures comb_inv(m, sv, seg, dl, ps, 0),
{
    let m = Comb {
        top: top_new(Ghost(sv), Ghost(ps)), c: Ghost(Seq::empty()), cs: Ghost(Seq::empty()), open: false, cj: 0, csum: 0,
        wit: Ghost(false), wv: Ghost(0), wd: Ghost(0), lw: Ghost(Seq::empty()),
    };
    proof {
        assert forall|j: int| 0 <= j < n_o(sv) implies
            #[trigger] order_abs(sv, seg, dl, j, 0, 0) <= order_count(sv, seg, dl, j, 0, 0) * (VMAX as int) by {}
    }
    m
}

/// Add the group `(x, s)`, `s` its final sum, to the candidates and the selection.
fn comb_add(m: &mut Comb, x: usize, s: i128, odate: &[i32], Ghost(sv): Ghost<StoresView>, Ghost(seg): Ghost<Seq<u8>>,
    Ghost(dl): Ghost<int>, Ghost(ps): Ghost<Seq<Literal>>)
    requires
        cand_ok(*old(m), sv, seg, dl, ps),
        !old(m).c@.contains(x), (x as int) < n_o(sv),
        s as int == order_sum(sv, seg, dl, x as int, 0, n_l(sv)),
        order_count(sv, seg, dl, x as int, 0, n_l(sv)) > 0,
        odate@ == od(sv),
    ensures
        cand_ok(*final(m), sv, seg, dl, ps),
        final(m).c@ == old(m).c@.push(x), final(m).cs@ == old(m).cs@.push(s),
        final(m).open == old(m).open, final(m).cj == old(m).cj, final(m).csum == old(m).csum,
        final(m).wit == old(m).wit, final(m).wv == old(m).wv, final(m).wd == old(m).wd, final(m).lw == old(m).lw,
{
    let ghost m0 = *m;
    proof {
        let (qj, qs) = (m.c@.push(x), m.cs@.push(s));
        assert forall|a: int, b: int| 0 <= a < qj.len() && 0 <= b < qj.len() && a != b implies qj[a] != qj[b] by {
            if a == m.c@.len() {
                assert(qj[b] == m.c@[b]);
                assert(m.c@.contains(m.c@[b]));
            } else if b == m.c@.len() {
                assert(qj[a] == m.c@[a]);
                assert(m.c@.contains(m.c@[a]));
            } else {
                assert(qj[a] == m.c@[a] && qj[b] == m.c@[b]);
            }
        }
        assert forall|a: int| 0 <= a < qj.len() implies (#[trigger] qj[a] as int) < n_o(sv) by {
            if a < m.c@.len() {
                assert(qj[a] == m.c@[a]);
            }
        }
        assert forall|a: int| 0 <= a < qj.len() implies #[trigger] qs[a] as int == fin(sv, ps)(qj[a] as int) by {
            if a < m.c@.len() {
                assert(qj[a] == m.c@[a] && qs[a] == m.cs@[a]);
            }
        }
    }
    top_step(&mut m.top, x, s, odate, m.c, m.cs, Ghost(sv), Ghost(ps));
    m.c = Ghost(m.c@.push(x));
    m.cs = Ghost(m.cs@.push(s));
    proof {
        assert forall|i: int| 0 <= i < m.c@.len() implies #[trigger] order_count(sv, seg, dl, m.c@[i] as int, 0, n_l(sv)) > 0 by {
            if i < m0.c@.len() {
                assert(m.c@[i] == m0.c@[i]);
            }
        }
        if m.wit@ {
            assert forall|k: int| 0 <= k < 10 implies m.c@.contains(#[trigger] m.lw@[k])
                && row_cmp(fin(sv, ps)(m.lw@[k] as int), odf(sv)(m.lw@[k] as int), m.wv@, m.wd@) <= 0 by {
                assert(m0.c@.contains(m.lw@[k]));
                let i = choose|i: int| 0 <= i < m0.c@.len() && m0.c@[i] == m.lw@[k];
                assert(m.c@[i] == m.lw@[k]);
            }
        }
    }
}

/// A task without runs: no row of it is hit.
proof fn lemma_comb_empty(m: Comb, sv: StoresView, seg: Seq<u8>, dl: int, ps: Seq<Literal>, o: ScanOut, lo: int, hi: int)
    requires comb_inv(m, sv, seg, dl, ps, lo), scan_out_ok(o, sv, seg, dl, lo, hi), lo <= hi <= n_l(sv), o.n == 0,
    ensures comb_inv(m, sv, seg, dl, ps, hi),
{
    assert forall|j: int| 0 <= j < n_o(sv) implies
        #[trigger] order_count(sv, seg, dl, j, 0, hi) == order_count(sv, seg, dl, j, 0, lo)
        && order_sum(sv, seg, dl, j, 0, hi) == order_sum(sv, seg, dl, j, 0, lo) by {
        if order_count(sv, seg, dl, j, lo, hi) > 0 {
            let t = choose|t: int| 0 <= t < o.n && o.rj@[t] == j;
        }
        lemma_order_bounds(sv, seg, dl, j, lo, hi);
        lemma_order_split(sv, seg, dl, j, 0, lo, hi);
    }
    lemma_mass_split(sv, seg, dl, 0, lo, hi);
    if m.open {
        assert(order_count(sv, seg, dl, m.cj as int, 0, hi) == order_count(sv, seg, dl, m.cj as int, 0, lo));
        assert forall|j: int| m.cj < j < n_o(sv) implies #[trigger] order_count(sv, seg, dl, j, 0, hi) == 0 by {
            assert(order_count(sv, seg, dl, j, 0, hi) == order_count(sv, seg, dl, j, 0, lo));
        }
    } else {
        assert forall|j: int| 0 <= j < n_o(sv) implies #[trigger] order_count(sv, seg, dl, j, 0, hi) == 0 by {
            assert(order_count(sv, seg, dl, j, 0, hi) == order_count(sv, seg, dl, j, 0, lo));
        }
    }
    assert forall|j: int| 0 <= j < n_o(sv) && #[trigger] order_count(sv, seg, dl, j, 0, hi) > 0 implies
        m.c@.contains(j as usize) || (m.open && j == m.cj) || dominated(m, sv, ps, j) by {
        assert(order_count(sv, seg, dl, j, 0, hi) == order_count(sv, seg, dl, j, 0, lo));
    }
}

/// The first run of the task over `lo..hi`: merged into the open group, or it closes the open group (whose sum is
/// then final) and opens its own; `false` when it is below the open group.
fn comb_first(m: &mut Comb, o: &ScanOut, odate: &[i32], Ghost(sv): Ghost<StoresView>, Ghost(seg): Ghost<Seq<u8>>, Ghost(dl): Ghost<int>,
    Ghost(ps): Ghost<Seq<Literal>>, Ghost(lo): Ghost<int>, Ghost(hi): Ghost<int>) -> (ok: bool)
    requires
        comb_inv(*old(m), sv, seg, dl, ps, lo), scan_out_ok(*o, sv, seg, dl, lo, hi), lo <= hi <= n_l(sv), o.n > 0,
        tail_zero(sv, seg, dl, hi, o.rj@[o.n - 1] as int), odate@ == od(sv),
    ensures ok ==> mid_inv(*final(m), sv, seg, dl, ps, lo, hi) && final(m).cj == o.rj@[0],
{
    let j0 = o.fj;
    let s0 = o.fs;
    let ghost m0 = *m;
    proof {
        if o.n > 1 {
            assert(o.rj@[0] < o.rj@[o.n - 1]);
        }
        assert(s0 as int == order_sum(sv, seg, dl, j0 as int, lo, hi) && order_count(sv, seg, dl, j0 as int, lo, hi) > 0);
        assert((j0 as int) < n_o(sv));
        lemma_mass_split(sv, seg, dl, 0, lo, hi);
        lemma_order_split(sv, seg, dl, j0 as int, 0, lo, hi);
    }
    if m.open && j0 == m.cj {
        proof {
            lemma_sum_bound(sv, seg, dl, j0 as int, 0, hi);
            lemma_sum_bound(sv, seg, dl, j0 as int, 0, lo);
            assert((NL_MAX as int) * (VMAX as int) < i128::MAX);
        }
        m.csum = m.csum + s0;
        proof {
            assert forall|j: int| 0 <= j < n_o(sv) && #[trigger] order_count(sv, seg, dl, j, 0, lo) > 0 implies
                m.c@.contains(j as usize) || j == m.cj || dominated(*m, sv, ps, j) by {
                assert(dominated(*m, sv, ps, j) == dominated(m0, sv, ps, j));
            }
        }
        true
    } else if !m.open || j0 > m.cj {
        if m.open {
            let cj = m.cj;
            let cs = m.csum;
            proof {
                // the open group is final: no run of this task, none after it
                let c = cj as int;
                if order_count(sv, seg, dl, c, lo, hi) > 0 {
                    let t = choose|t: int| 0 <= t < o.n && o.rj@[t] == c;
                    if t > 0 {
                        assert(o.rj@[0] < o.rj@[t]);
                    }
                }
                lemma_order_bounds(sv, seg, dl, c, lo, hi);
                assert(c < o.rj@[o.n - 1]);
                assert(order_count(sv, seg, dl, c, hi, n_l(sv)) == 0);
                lemma_order_bounds(sv, seg, dl, c, hi, n_l(sv));
                lemma_order_split(sv, seg, dl, c, 0, lo, hi);
                lemma_order_split(sv, seg, dl, c, 0, hi, n_l(sv));
                assert forall|i: int| 0 <= i < m.c@.len() implies m.c@[i] != cj by {
                    assert(m.c@[i] < cj);
                }
            }
            comb_add(m, cj, cs, odate, Ghost(sv), Ghost(seg), Ghost(dl), Ghost(ps));
        }
        let ghost m1 = *m;
        m.open = true;
        m.cj = j0;
        m.csum = s0;
        proof {
            // nothing hit j0 before this task
            assert(order_count(sv, seg, dl, j0 as int, 0, lo) == 0);
            lemma_order_bounds(sv, seg, dl, j0 as int, 0, lo);
            assert forall|i: int| 0 <= i < m.c@.len() implies #[trigger] m.c@[i] < m.cj by {
                if i < m0.c@.len() {
                    assert(m.c@[i] == m0.c@[i]);
                    assert(m0.c@[i] < m0.cj);
                } else {
                    assert(m.c@[i] == m0.cj);
                }
            }
            assert forall|j: int| 0 <= j < n_o(sv) && #[trigger] order_count(sv, seg, dl, j, 0, lo) > 0 implies
                m.c@.contains(j as usize) || j == m.cj || dominated(*m, sv, ps, j) by {
                assert(dominated(*m, sv, ps, j) == dominated(m0, sv, ps, j));
                if m0.c@.contains(j as usize) {
                    let i = choose|i: int| 0 <= i < m0.c@.len() && m0.c@[i] == j as usize;
                    assert(m.c@[i] == j as usize);
                } else if m0.open && j == m0.cj {
                    assert(m.c@[m0.c@.len() as int] == j as usize);
                }
            }
            assert forall|j: int| m.cj < j < n_o(sv) implies #[trigger] order_count(sv, seg, dl, j, 0, lo) == 0 by {}
            assert(wit_ok(*m, sv, ps)) by {
                assert(m.c@ == m1.c@ && m.lw@ == m1.lw@ && m.wit@ == m1.wit@);
            }
        }
        true
    } else {
        false
    }
}


/// An interior run `r` of the task: its order lies strictly between the first and the last run's, and its sum over
/// the task is the order's final sum.
proof fn lemma_interior_final(m: Comb, sv: StoresView, seg: Seq<u8>, dl: int, ps: Seq<Literal>, o: ScanOut, lo: int, hi: int, r: int)
    requires
        mid_inv(m, sv, seg, dl, ps, lo, hi), scan_out_ok(o, sv, seg, dl, lo, hi), m.cj == o.rj@[0], 1 <= r < o.n - 1,
        tail_zero(sv, seg, dl, hi, o.rj@[o.n - 1] as int),
    ensures
        (o.rj@[r] as int) < n_o(sv),
        m.cj < o.rj@[r] < o.rj@[o.n - 1],
        o.rsum@[r] as int == order_sum(sv, seg, dl, o.rj@[r] as int, 0, n_l(sv)),
        order_count(sv, seg, dl, o.rj@[r] as int, 0, n_l(sv)) > 0,
{
    let x = o.rj@[r] as int;
    assert(0 <= r < o.n);
    assert(o.rsum@[r] as int == order_sum(sv, seg, dl, o.rj@[r] as int, lo, hi));
    assert(o.rj@[0] < o.rj@[r]);
    assert(o.rj@[r] < o.rj@[o.n - 1]);
    assert(o.rsum@[r] as int == order_sum(sv, seg, dl, x, lo, hi) && order_count(sv, seg, dl, x, lo, hi) > 0);
    assert(order_count(sv, seg, dl, x, 0, lo) == 0);
    lemma_order_bounds(sv, seg, dl, x, 0, lo);
    assert(order_count(sv, seg, dl, x, hi, n_l(sv)) == 0);
    lemma_order_bounds(sv, seg, dl, x, hi, n_l(sv));
    lemma_order_split(sv, seg, dl, x, 0, lo, hi);
    lemma_order_split(sv, seg, dl, x, 0, hi, n_l(sv));
}

/// The facts of a task's selection: entry `q` is an interior run with the run's sum and its order's date; the entries
/// are distinct.
proof fn lemma_sel_entry(o: ScanOut, sv: StoresView, q: int)
    requires ltop_ok(o, sv), 0 <= q < o.top.k,
    ensures
        1 <= o.top.ti@[q] < o.n - 1,
        o.top.ts@[q] == o.rsum@[o.top.ti@[q] as int],
        o.top.td@[q] as int == od(sv)[o.rj@[o.top.ti@[q] as int] as int] as int,
{
    let t = o.top;
    assert(fsel(t)[q] == t.ti@[q] && fss(t)[q] == t.ts@[q] && fsd(t)[q] == t.td@[q]);
    let items = litems(o.n);
    assert(among(items, items.len() as int, fsel(t)[q]));
    let h = choose|h: int| 0 <= h < items.len() && items[h] == fsel(t)[q];
    assert(items[h] == (h + 1) as usize);
}

/// A task with a single run: it is the open group.
proof fn lemma_rest_single(m: Comb, sv: StoresView, seg: Seq<u8>, dl: int, ps: Seq<Literal>, o: ScanOut, lo: int, hi: int)
    requires
        mid_inv(m, sv, seg, dl, ps, lo, hi), scan_out_ok(o, sv, seg, dl, lo, hi), o.n == 1, m.cj == o.rj@[0],
    ensures comb_inv(m, sv, seg, dl, ps, hi),
{
    lemma_mass_split(sv, seg, dl, 0, lo, hi);
    assert forall|j: int| 0 <= j < n_o(sv) && #[trigger] order_count(sv, seg, dl, j, 0, hi) > 0 implies
        m.c@.contains(j as usize) || (m.open && j == m.cj) || dominated(m, sv, ps, j) by {
        lemma_order_split(sv, seg, dl, j, 0, lo, hi);
        if order_count(sv, seg, dl, j, lo, hi) > 0 {
            let t = choose|t: int| 0 <= t < o.n && o.rj@[t] == j;
        }
    }
    assert forall|j: int| m.cj < j < n_o(sv) implies #[trigger] order_count(sv, seg, dl, j, 0, hi) == 0 by {
        lemma_order_split(sv, seg, dl, j, 0, lo, hi);
        if order_count(sv, seg, dl, j, lo, hi) > 0 {
            let t = choose|t: int| 0 <= t < o.n && o.rj@[t] == j;
        }
    }
}

/// The rest of the task over `lo..hi` after its first run: close the first run's group (final), add the task's
/// selection, update the witness, and open the last run.
fn comb_rest(m: &mut Comb, o: &ScanOut, odate: &[i32], Ghost(sv): Ghost<StoresView>, Ghost(seg): Ghost<Seq<u8>>, Ghost(dl): Ghost<int>,
    Ghost(ps): Ghost<Seq<Literal>>, Ghost(lo): Ghost<int>, Ghost(hi): Ghost<int>)
    requires
        mid_inv(*old(m), sv, seg, dl, ps, lo, hi), scan_out_ok(*o, sv, seg, dl, lo, hi), ltop_ok(*o, sv), o.n > 0,
        old(m).cj == o.rj@[0], tail_zero(sv, seg, dl, hi, o.rj@[o.n - 1] as int), odate@ == od(sv),
    ensures comb_inv(*final(m), sv, seg, dl, ps, hi),
{
    let n = o.n;
    let ghost m0 = *m;
    if n == 1 {
        proof {
            lemma_rest_single(*m, sv, seg, dl, ps, *o, lo, hi);
        }
        return;
    }
    // the first run's group is final
    let cj = m.cj;
    let cs = m.csum;
    proof {
        assert(o.rj@[0] < o.rj@[n - 1]);
        assert(order_count(sv, seg, dl, cj as int, hi, n_l(sv)) == 0);
        lemma_order_bounds(sv, seg, dl, cj as int, hi, n_l(sv));
        lemma_order_split(sv, seg, dl, cj as int, 0, hi, n_l(sv));
        assert forall|i: int| 0 <= i < m.c@.len() implies m.c@[i] != cj by {
            assert(m.c@[i] < cj);
        }
    }
    comb_add(m, cj, cs, odate, Ghost(sv), Ghost(seg), Ghost(dl), Ghost(ps));
    let ghost c1 = m.c@;
    proof {
        assert forall|i: int| 0 <= i < c1.len() implies c1[i] <= cj by {
            if i < m0.c@.len() {
                assert(c1[i] == m0.c@[i]);
            }
        }
    }
    // the task's selection: interior runs, final sums
    let k = o.top.k;
    let mut q: usize = 0;
    while q < k
        invariant
            mid_inv(m0, sv, seg, dl, ps, lo, hi), scan_out_ok(*o, sv, seg, dl, lo, hi), ltop_ok(*o, sv), n == o.n, n >= 2,
            m0.cj == o.rj@[0], cj == m0.cj, tail_zero(sv, seg, dl, hi, o.rj@[o.n - 1] as int), odate@ == od(sv),
            k == o.top.k, q <= k,
            cand_ok(*m, sv, seg, dl, ps),
            m.c@ == c1 + Seq::new(q as nat, |i: int| o.rj@[o.top.ti@[i] as int]),
            forall|i: int| 0 <= i < c1.len() ==> c1[i] <= cj,
            m.open == m0.open, m.cj == m0.cj, m.csum == m0.csum,
            m.wit == m0.wit, m.wv == m0.wv, m.wd == m0.wd, m.lw == m0.lw,
        decreases k - q,
    {
        let r = o.top.ti[q];
        proof {
            lemma_sel_entry(*o, sv, q as int);
        }
        // the entry's order (its tag) and sum
        let x = o.top.to[q];
        let s = o.top.ts[q];
        proof {
            assert(o.top.to@[q as int] as int == lof(o.rj@)(o.top.ti@[q as int] as int));
            assert(x == o.rj@[r as int] && s == o.rsum@[r as int]);
        }
        proof {
            lemma_interior_final(m0, sv, seg, dl, ps, *o, lo, hi, r as int);
            let added = Seq::new(q as nat, |i: int| o.rj@[o.top.ti@[i] as int]);
            assert(!m.c@.contains(x)) by {
                if m.c@.contains(x) {
                    let i = choose|i: int| 0 <= i < m.c@.len() && m.c@[i] == x;
                    if i < c1.len() {
                        assert(m.c@[i] == c1[i]);
                    } else {
                        let i2 = i - c1.len();
                        assert(m.c@[i] == added[i2]);
                        lemma_sel_entry(*o, sv, i2);
                        let r2 = o.top.ti@[i2] as int;
                        assert(fsel(o.top)[i2] == o.top.ti@[i2] && fsel(o.top)[q as int] == o.top.ti@[q as int]);
                        assert(r2 != r as int);
                        if r2 < r { assert(o.rj@[r2] < o.rj@[r as int]); } else { assert(o.rj@[r as int] < o.rj@[r2]); }
                    }
                }
            }
        }
        comb_add(m, x, s, odate, Ghost(sv), Ghost(seg), Ghost(dl), Ghost(ps));
        proof {
            assert(m.c@ =~= c1 + Seq::new((q + 1) as nat, |i: int| o.rj@[o.top.ti@[i] as int]));
        }
        q = q + 1;
    }
    // the witness: the better of the old one and this task's 10th entry (when its selection is full)
    let ghost lt = Seq::new(10, |i: int| o.rj@[o.top.ti@[i] as int]);
    let ghost (lv, ld) = (o.top.ts@[9] as int, o.top.td@[9] as int);
    let ghost take = k == 10 && (!m.wit@ || row_cmp(lv, ld, m.wv@, m.wd@) < 0);
    let ghost m2 = *m;
    let ghost wit2 = m.wit@ || k == 10;
    let ghost wv2 = if take { lv } else { m.wv@ };
    let ghost wd2 = if take { ld } else { m.wd@ };
    let ghost lw2 = if take { lt } else { m.lw@ };
    m.wit = Ghost(wit2);
    m.wv = Ghost(wv2);
    m.wd = Ghost(wd2);
    m.lw = Ghost(lw2);
    // the last run is the open group
    m.cj = o.lj;
    m.csum = o.ls;
    m.open = true;
    proof {
        lemma_rest_final(m0, m2, *m, c1, sv, seg, dl, ps, *o, lo, hi, take, lt, lv, ld);
    }
}

/// The state after a task with at least two runs is the invariant at its end.
proof fn lemma_rest_final(m0: Comb, m2: Comb, m: Comb, c1: Seq<usize>, sv: StoresView, seg: Seq<u8>, dl: int, ps: Seq<Literal>,
    o: ScanOut, lo: int, hi: int, take: bool, lt: Seq<usize>, lv: int, ld: int)
    requires
        mid_inv(m0, sv, seg, dl, ps, lo, hi), scan_out_ok(o, sv, seg, dl, lo, hi), ltop_ok(o, sv), o.n >= 2,
        m0.cj == o.rj@[0], tail_zero(sv, seg, dl, hi, o.rj@[o.n - 1] as int),
        c1 == m0.c@.push(m0.cj),
        cand_ok(m2, sv, seg, dl, ps),
        m2.c@ == c1 + Seq::new(o.top.k as nat, |i: int| o.rj@[o.top.ti@[i] as int]),
        m2.wit == m0.wit, m2.wv == m0.wv, m2.wd == m0.wd, m2.lw == m0.lw,
        lt == Seq::new(10, |i: int| o.rj@[o.top.ti@[i] as int]),
        lv == o.top.ts@[9] as int, ld == o.top.td@[9] as int,
        take == (o.top.k == 10 && (!m0.wit@ || row_cmp(lv, ld, m0.wv@, m0.wd@) < 0)),
        m.top == m2.top, m.c == m2.c, m.cs == m2.cs,
        m.wit@ == (m0.wit@ || o.top.k == 10),
        m.wv@ == (if take { lv } else { m0.wv@ }), m.wd@ == (if take { ld } else { m0.wd@ }),
        m.lw@ == (if take { lt } else { m0.lw@ }),
        m.open, m.cj == o.rj@[o.n - 1], m.csum == o.rsum@[o.n - 1],
    ensures comb_inv(m, sv, seg, dl, ps, hi),
{
    let n = o.n as int;
    let k = o.top.k as int;
    let added = Seq::new(o.top.k as nat, |i: int| o.rj@[o.top.ti@[i] as int]);
    let last = o.rj@[n - 1] as int;
    lemma_mass_split(sv, seg, dl, 0, lo, hi);
    assert(o.rj@[0] < o.rj@[n - 1]);
    // the selection's entries
    assert forall|i: int| 0 <= i < k implies #[trigger] added[i] as int == o.rj@[o.top.ti@[i] as int] as int
        && 1 <= o.top.ti@[i] < n - 1 && o.rj@[o.top.ti@[i] as int] < o.rj@[n - 1] by {
        lemma_sel_entry(o, sv, i);
        assert(o.rj@[o.top.ti@[i] as int] < o.rj@[n - 1]);
    }
    // the open group: the last run, nothing of it before lo
    assert(o.rsum@[n - 1] as int == order_sum(sv, seg, dl, last, lo, hi) && order_count(sv, seg, dl, last, lo, hi) > 0);
    assert((o.rj@[n - 1] as int) < n_o(sv));
    assert(order_count(sv, seg, dl, last, 0, lo) == 0);
    lemma_order_bounds(sv, seg, dl, last, 0, lo);
    lemma_order_split(sv, seg, dl, last, 0, lo, hi);
    // candidates below the last run
    assert forall|i: int| 0 <= i < m.c@.len() implies #[trigger] m.c@[i] < m.cj by {
        if i < c1.len() {
            assert(m.c@[i] == c1[i]);
            if i < m0.c@.len() {
                assert(c1[i] == m0.c@[i]);
                assert(m0.c@[i] < m0.cj);
            }
        } else {
            assert(m.c@[i] == added[i - c1.len()]);
        }
    }
    // the witness
    if take {
        assert forall|i: int| 0 <= i < 10 implies #[trigger] lt[i] == m.c@[c1.len() + i] by {
            assert(m.c@[c1.len() + i] == added[i]);
        }
        assert(lt.no_duplicates()) by {
            assert forall|a: int, b: int| 0 <= a < 10 && 0 <= b < 10 && a != b implies lt[a] != lt[b] by {
                lemma_sel_entry(o, sv, a);
                lemma_sel_entry(o, sv, b);
                let (ra, rb) = (o.top.ti@[a] as int, o.top.ti@[b] as int);
                assert(fsel(o.top)[a] == o.top.ti@[a] && fsel(o.top)[b] == o.top.ti@[b]);
                assert(ra != rb);
                if ra < rb { assert(o.rj@[ra] < o.rj@[rb]); } else { assert(o.rj@[rb] < o.rj@[ra]); }
            }
        }
        assert forall|i: int| 0 <= i < 10 implies m.c@.contains(#[trigger] lt[i])
            && row_cmp(fin(sv, ps)(lt[i] as int), odf(sv)(lt[i] as int), lv, ld) <= 0 by {
            assert(lt[i] == m.c@[c1.len() + i]);
            lemma_sel_entry(o, sv, i);
            let r = o.top.ti@[i] as int;
            lemma_interior_final(m0, sv, seg, dl, ps, o, lo, hi, r);
            assert(fss(o.top)[i] == o.top.ts@[i] && fsd(o.top)[i] == o.top.td@[i]);
            assert(fss(o.top)[9] == o.top.ts@[9] && fsd(o.top)[9] == o.top.td@[9]);
            if i < 9 {
                assert(row_cmp(fss(o.top)[i] as int, fsd(o.top)[i] as int, fss(o.top)[9] as int, fsd(o.top)[9] as int) <= 0);
            }
        }
    } else if m0.wit@ {
        assert forall|i: int| 0 <= i < 10 implies m.c@.contains(#[trigger] m.lw@[i]) by {
            assert(m0.c@.contains(m0.lw@[i]));
            let a = choose|a: int| 0 <= a < m0.c@.len() && m0.c@[a] == m0.lw@[i];
            assert(m.c@[a] == c1[a]);
        }
    }
    // the old witness's dominated orders stay dominated
    assert forall|j: int| dominated(m0, sv, ps, j) implies dominated(m, sv, ps, j) by {
        if take {
            lemma_row_cmp_facts(lv, ld, m0.wv@, m0.wd@, fin(sv, ps)(j), odf(sv)(j));
        }
    }
    // every order hit in 0..hi
    assert forall|j: int| 0 <= j < n_o(sv) && #[trigger] order_count(sv, seg, dl, j, 0, hi) > 0 implies
        m.c@.contains(j as usize) || (m.open && j == m.cj) || dominated(m, sv, ps, j) by {
        lemma_order_split(sv, seg, dl, j, 0, lo, hi);
        if order_count(sv, seg, dl, j, 0, lo) > 0 {
            if m0.c@.contains(j as usize) {
                let a = choose|a: int| 0 <= a < m0.c@.len() && m0.c@[a] == j as usize;
                assert(m.c@[a] == j as usize);
            } else if j == m0.cj {
                assert(m.c@[m0.c@.len() as int] == j as usize);
            } else {
                assert(dominated(m0, sv, ps, j));
            }
        } else {
            let t = choose|t: int| 0 <= t < o.n && o.rj@[t] == j;
            if t == 0 {
                assert(m.c@[m0.c@.len() as int] == j as usize);
            } else if t < n - 1 {
                let items = litems(o.n);
                assert(items[t - 1] == t as usize);
                lemma_interior_final(m0, sv, seg, dl, ps, o, lo, hi, t);
                if fsel(o.top).contains(t as usize) {
                    let q = choose|q: int| 0 <= q < fsel(o.top).len() && fsel(o.top)[q] == t as usize;
                    assert(m.c@[c1.len() + q] == added[q]);
                    assert(o.top.ti@[q] == t as usize);
                } else {
                    // excluded from the task's full selection: no earlier than its 10th entry
                    assert(fsel(o.top).len() == 10) by {
                        if fsel(o.top).len() < 10 {
                            assert(fsel(o.top).contains(items[t - 1]));
                        }
                    }
                    assert(row_cmp(fss(o.top).last() as int, fsd(o.top).last() as int, lvals(o.n, o.rsum@)[t - 1] as int,
                        ldf(o.rj@, sv)(items[t - 1] as int)) <= 0);
                    assert(fss(o.top).last() == o.top.ts@[9] && fsd(o.top).last() == o.top.td@[9]);
                    assert(lvals(o.n, o.rsum@)[t - 1] == o.rsum@[t]);
                    if !take {
                        lemma_row_cmp_facts(m0.wv@, m0.wd@, lv, ld, fin(sv, ps)(j), odf(sv)(j));
                    }
                }
            }
        }
    }
    // nothing above the last run
    assert forall|j: int| m.cj < j < n_o(sv) implies #[trigger] order_count(sv, seg, dl, j, 0, hi) == 0 by {
        lemma_order_split(sv, seg, dl, j, 0, lo, hi);
        if order_count(sv, seg, dl, j, lo, hi) > 0 {
            let t = choose|t: int| 0 <= t < o.n && o.rj@[t] == j;
            if t < n - 1 {
                assert(o.rj@[t] < o.rj@[n - 1]);
            }
        }
    }
}


/// One task over `lo..hi`.
fn comb_task(m: &mut Comb, o: &ScanOut, odate: &[i32], Ghost(sv): Ghost<StoresView>, Ghost(seg): Ghost<Seq<u8>>, Ghost(dl): Ghost<int>,
    Ghost(ps): Ghost<Seq<Literal>>, Ghost(lo): Ghost<int>, Ghost(hi): Ghost<int>) -> (ok: bool)
    requires
        comb_inv(*old(m), sv, seg, dl, ps, lo), scan_out_ok(*o, sv, seg, dl, lo, hi), ltop_ok(*o, sv), lo <= hi <= n_l(sv),
        o.n > 0 ==> tail_zero(sv, seg, dl, hi, o.rj@[o.n - 1] as int), odate@ == od(sv),
    ensures ok ==> comb_inv(*final(m), sv, seg, dl, ps, hi),
{
    if o.n == 0 {
        proof {
            lemma_comb_empty(*m, sv, seg, dl, ps, *o, lo, hi);
        }
        return true;
    }
    if !comb_first(m, o, odate, Ghost(sv), Ghost(seg), Ghost(dl), Ghost(ps), Ghost(lo), Ghost(hi)) {
        return false;
    }
    comb_rest(m, o, odate, Ghost(sv), Ghost(seg), Ghost(dl), Ghost(ps), Ghost(lo), Ghost(hi));
    true
}

// ------------------------------------------------------------------------------------------------ the result

/// The qualifying orders below `k` that some lineitem row hits, in order: the canonical list of the groups.
pub open spec fn qual_upto(sv: StoresView, ps: Seq<Literal>, k: int) -> Seq<int>
    decreases k,
{
    if k <= 0 {
        Seq::empty()
    } else {
        let s = qual_upto(sv, ps, k - 1);
        if order_ok(sv, seg_of(ps), dl_of(ps), k - 1) && order_count(sv, seg_of(ps), dl_of(ps), k - 1, 0, n_l(sv)) > 0 {
            s.push(k - 1)
        } else {
            s
        }
    }
}

pub open spec fn qual(sv: StoresView, ps: Seq<Literal>) -> Seq<int> {
    qual_upto(sv, ps, n_o(sv))
}

pub open spec fn qualifies(sv: StoresView, ps: Seq<Literal>, j: int) -> bool {
    order_ok(sv, seg_of(ps), dl_of(ps), j) && order_count(sv, seg_of(ps), dl_of(ps), j, 0, n_l(sv)) > 0
}

proof fn lemma_qual_upto(sv: StoresView, ps: Seq<Literal>, k: int)
    requires 0 <= k,
    ensures
        forall|a: int, b: int| 0 <= a < b < qual_upto(sv, ps, k).len() ==> qual_upto(sv, ps, k)[a] < qual_upto(sv, ps, k)[b],
        forall|a: int| 0 <= a < qual_upto(sv, ps, k).len() ==> 0 <= #[trigger] qual_upto(sv, ps, k)[a] < k
            && qualifies(sv, ps, qual_upto(sv, ps, k)[a]),
        forall|j: int| 0 <= j < k && #[trigger] qualifies(sv, ps, j) ==> qual_upto(sv, ps, k).contains(j),
    decreases k,
{
    if k > 0 {
        lemma_qual_upto(sv, ps, k - 1);
        let s = qual_upto(sv, ps, k - 1);
        let q = qual_upto(sv, ps, k);
        if qualifies(sv, ps, k - 1) {
            assert(q == s.push(k - 1));
            assert forall|j: int| 0 <= j < k && #[trigger] qualifies(sv, ps, j) implies q.contains(j) by {
                if j < k - 1 {
                    let a = choose|a: int| 0 <= a < s.len() && s[a] == j;
                    assert(q[a] == j);
                } else {
                    assert(q[s.len() as int] == j);
                }
            }
        }
    }
}

/// The selection's rows and sums, and the groups (canonically listed): the facts the final claim needs.
pub open spec fn fast_ok(sel: Seq<usize>, ss: Seq<i128>, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& sel.len() == ss.len()
    &&& forall|k: int| 0 <= k < sel.len() ==> #[trigger] ss[k] as int == order_sum(sv, seg_of(ps), dl_of(ps), sel[k] as int, 0, n_l(sv))
    &&& forall|k: int| 0 <= k < sel.len() ==> (#[trigger] sel[k] as int) < n_o(sv)
    &&& groups_complete(sv, ps, qual(sv, ps))
    &&& groups_capped(sv, ps, qual(sv, ps))
    &&& top_rows_ok(sv, ps, qual(sv, ps), sel.map_values(|x: usize| x as int))
}

/// The canonical list holds exactly the groups, each within the SUM capacity.
proof fn lemma_qual_groups(sv: StoresView, seg: Seq<u8>, dl: int, ps: Seq<Literal>)
    requires scan_facts(sv, seg, dl), seg == seg_of(ps), dl == dl_of(ps), mass_bounded(sv, seg, dl, 0, n_l(sv)),
    ensures
        groups_complete(sv, ps, qual(sv, ps)),
        groups_capped(sv, ps, qual(sv, ps)),
        forall|a: int| 0 <= a < qual(sv, ps).len() ==> 0 <= #[trigger] qual(sv, ps)[a] < n_o(sv)
            && qualifies(sv, ps, qual(sv, ps)[a]),
        forall|j: int| 0 <= j < n_o(sv) && #[trigger] qualifies(sv, ps, j) ==> qual(sv, ps).contains(j),
{
    let q = qual(sv, ps);
    lemma_qual_upto(sv, ps, n_o(sv));
    assert(q.no_duplicates()) by {
        assert forall|a: int, b: int| 0 <= a < q.len() && 0 <= b < q.len() && a != b implies q[a] != q[b] by {
            if a < b { assert(q[a] < q[b]); } else { assert(q[b] < q[a]); }
        }
    }
    assert forall|j: int| 0 <= j < n_o(sv) && order_ok(sv, seg_of(ps), dl_of(ps), j)
        && #[trigger] order_count(sv, seg_of(ps), dl_of(ps), j, 0, n_l(sv)) > 0 implies q.contains(j) by {
        assert(qualifies(sv, ps, j));
    }
    assert forall|t: int| 0 <= t < q.len() implies #[trigger] order_abs(sv, seg_of(ps), dl_of(ps), q[t], 0, n_l(sv)) <= i128_max() by {
        let j = q[t];
        assert(order_abs(sv, seg, dl, j, 0, n_l(sv)) <= order_count(sv, seg, dl, j, 0, n_l(sv)) * (VMAX as int));
        lemma_sum_bound(sv, seg, dl, j, 0, n_l(sv));
        assert((NL_MAX as int) * (VMAX as int) <= i128_max());
    }
}

/// The candidates are groups; the selection has `min(10, |groups|)` entries.
proof fn lemma_comb_size(m: Comb, sv: StoresView, seg: Seq<u8>, dl: int, ps: Seq<Literal>)
    requires
        cand_ok(m, sv, seg, dl, ps),
        mass_bounded(sv, seg, dl, 0, n_l(sv)),
        n_o(sv) <= usize::MAX,
        forall|j: int| 0 <= j < n_o(sv) && #[trigger] order_count(sv, seg, dl, j, 0, n_l(sv)) > 0 ==>
            m.c@.contains(j as usize) || dominated(m, sv, ps, j),
    ensures
        forall|i: int| 0 <= i < m.c@.len() ==> qual(sv, ps).contains(#[trigger] m.c@[i] as int),
        m.top.sel@.len() == if qual(sv, ps).len() <= 10 { qual(sv, ps).len() as int } else { 10 },
{
    let (c, cs, sel, ss, sd) = (m.c@, m.cs@, m.top.sel@, m.top.ss@, m.top.sd@);
    let q = qual(sv, ps);
    lemma_qual_groups(sv, seg, dl, ps);
    assert forall|i: int| 0 <= i < c.len() implies q.contains(#[trigger] c[i] as int) by {
        let j = c[i] as int;
        assert(order_count(sv, seg, dl, j, 0, n_l(sv)) > 0);
        if !order_ok(sv, seg, dl, j) {
            lemma_order_not_ok(sv, seg, dl, j, 0, n_l(sv));
        }
        assert(qualifies(sv, ps, j));
    }
    let ci = c.map_values(|x: usize| x as int);
    assert(ci.no_duplicates()) by {
        assert forall|a: int, b: int| 0 <= a < ci.len() && 0 <= b < ci.len() && a != b implies ci[a] != ci[b] by {
            assert(c[a] != c[b]);
        }
    }
    assert(q.no_duplicates());
    ci.unique_seq_to_set();
    q.unique_seq_to_set();
    assert(ci.to_set().subset_of(q.to_set())) by {
        assert forall|e: int| ci.to_set().contains(e) implies q.to_set().contains(e) by {
            let i = choose|i: int| 0 <= i < ci.len() && ci[i] == e;
            assert(q.contains(c[i] as int));
        }
    }
    vstd::set_lib::lemma_len_subset(ci.to_set(), q.to_set());
    if c.len() < 10 {
        assert(!m.wit@) by {
            if m.wit@ {
                lemma_top_pigeon(sel, ss, sd, c, cs, fin(sv, ps), odf(sv), m.lw@, m.wv@, m.wd@);
            }
        }
        assert(q.to_set().subset_of(ci.to_set())) by {
            assert forall|e: int| q.to_set().contains(e) implies ci.to_set().contains(e) by {
                let a = choose|a: int| 0 <= a < q.len() && q[a] == e;
                assert(qualifies(sv, ps, e) && 0 <= e < n_o(sv));
                assert(order_count(sv, seg, dl, e, 0, n_l(sv)) > 0);
                assert(c.contains(e as usize));
                let i = choose|i: int| 0 <= i < c.len() && c[i] == e as usize;
                assert(ci[i] == c[i] as int);
                assert(ci[i] == e);
            }
        }
        vstd::set_lib::lemma_len_subset(q.to_set(), ci.to_set());
    }
}

/// At the end: every hit order is a candidate or dominated, so the selection is the top 10 of all groups.
proof fn lemma_comb_final(m: Comb, sv: StoresView, seg: Seq<u8>, dl: int, ps: Seq<Literal>)
    requires
        cand_ok(m, sv, seg, dl, ps),
        mass_bounded(sv, seg, dl, 0, n_l(sv)),
        n_o(sv) <= usize::MAX,
        forall|j: int| 0 <= j < n_o(sv) && #[trigger] order_count(sv, seg, dl, j, 0, n_l(sv)) > 0 ==>
            m.c@.contains(j as usize) || dominated(m, sv, ps, j),
    ensures fast_ok(m.top.sel@, m.top.ss@, sv, ps),
{
    let (c, cs, sel, ss, sd) = (m.c@, m.cs@, m.top.sel@, m.top.ss@, m.top.sd@);
    let q = qual(sv, ps);
    lemma_qual_groups(sv, seg, dl, ps);
    lemma_comb_size(m, sv, seg, dl, ps);
    // the selection's entries
    assert forall|k: int| 0 <= k < sel.len() implies c.contains(#[trigger] sel[k]) && (sel[k] as int) < n_o(sv)
        && ss[k] as int == order_sum(sv, seg_of(ps), dl_of(ps), sel[k] as int, 0, n_l(sv)) && sd[k] == od(sv)[sel[k] as int] by {
        assert(among(c, c.len() as int, sel[k]));
        let h = choose|h: int| 0 <= h < c.len() && c[h] == sel[k];
        assert(c[h] == sel[k]);
        assert(sel_okg(fin(sv, ps), odf(sv), sel, ss, sd));
        lemma_sel_okg_at(fin(sv, ps), odf(sv), sel, ss, sd, k);
    }
    lemma_comb_rows(m, sv, seg, dl, ps);
}

/// The selection's rows are sorted, and no group outside it sorts before its last row.
proof fn lemma_comb_rows(m: Comb, sv: StoresView, seg: Seq<u8>, dl: int, ps: Seq<Literal>)
    requires
        cand_ok(m, sv, seg, dl, ps),
        mass_bounded(sv, seg, dl, 0, n_l(sv)),
        n_o(sv) <= usize::MAX,
        forall|j: int| 0 <= j < n_o(sv) && #[trigger] order_count(sv, seg, dl, j, 0, n_l(sv)) > 0 ==>
            m.c@.contains(j as usize) || dominated(m, sv, ps, j),
        forall|k: int| 0 <= k < m.top.sel@.len() ==> m.c@.contains(#[trigger] m.top.sel@[k]) && (m.top.sel@[k] as int) < n_o(sv)
            && m.top.ss@[k] as int == order_sum(sv, seg_of(ps), dl_of(ps), m.top.sel@[k] as int, 0, n_l(sv))
            && m.top.sd@[k] == od(sv)[m.top.sel@[k] as int],
    ensures top_rows_ok(sv, ps, qual(sv, ps), m.top.sel@.map_values(|x: usize| x as int)),
{
    let (c, cs, sel, ss, sd) = (m.c@, m.cs@, m.top.sel@, m.top.ss@, m.top.sd@);
    let q = qual(sv, ps);
    let (vf, df) = (fin(sv, ps), odf(sv));
    lemma_qual_groups(sv, seg, dl, ps);
    lemma_comb_size(m, sv, seg, dl, ps);
    let si = sel.map_values(|x: usize| x as int);
    let rows = si.map_values(|j: int| group_row(sv, ps, j));
    assert(si.no_duplicates()) by {
        assert forall|a: int, b: int| 0 <= a < si.len() && 0 <= b < si.len() && a != b implies si[a] != si[b] by {
            assert(sel[a] != sel[b]);
        }
    }
    assert forall|t: int| 0 <= t < si.len() implies q.contains(#[trigger] si[t]) by {
        assert(c.contains(sel[t]));
        let i = choose|i: int| 0 <= i < c.len() && c[i] == sel[t];
        assert(q.contains(c[i] as int));
    }
    assert forall|a: int, b: int| 0 <= a < b < rows.len() implies
        crate::spec::order::keys_cmp(crate::agent::denotation::q3_order_keys(), #[trigger] rows[a], #[trigger] rows[b]) <= 0 by {
        lemma_order_row_cmp(sv, si[a], ss[a] as int, si[b], ss[b] as int);
        assert(rows[a] == order_row(sv, si[a], ss[a] as int));
        assert(rows[b] == order_row(sv, si[b], ss[b] as int));
    }
    if si.len() > 0 {
        let last = si.len() - 1;
        assert(rows.last() == order_row(sv, si[last], ss[last] as int));
        assert forall|j: int| #[trigger] q.contains(j) && !si.contains(j) implies
            crate::spec::order::keys_cmp(crate::agent::denotation::q3_order_keys(), rows.last(), group_row(sv, ps, j)) <= 0 by {
            let a = choose|a: int| 0 <= a < q.len() && q[a] == j;
            assert(qualifies(sv, ps, j) && 0 <= j < n_o(sv));
            lemma_order_row_cmp(sv, si[last], ss[last] as int, j, order_sum(sv, seg_of(ps), dl_of(ps), j, 0, n_l(sv)));
            if c.contains(j as usize) {
                let h = choose|h: int| 0 <= h < c.len() && c[h] == j as usize;
                assert(!sel.contains(c[h])) by {
                    if sel.contains(c[h]) {
                        let k = choose|k: int| 0 <= k < sel.len() && sel[k] == c[h];
                        assert(si[k] == j);
                    }
                }
                assert(row_cmp(ss.last() as int, sd.last() as int, cs[h] as int, df(c[h] as int)) <= 0);
                assert(cs[h] as int == vf(c[h] as int));
            } else {
                assert(dominated(m, sv, ps, j));
                lemma_top_pigeon(sel, ss, sd, c, cs, vf, df, m.lw@, m.wv@, m.wd@);
                lemma_row_cmp_facts(ss.last() as int, sd.last() as int, m.wv@, m.wd@, vf(j), df(j));
            }
        }
    }
}

/// Merge the tasks' first and last runs and selections into the top 10 groups; `None` when the runs are not in order.
pub fn combine(outs: &Vec<ScanOut>, odate: &[i32], Ghost(bounds): Ghost<Seq<int>>, Ghost(sv): Ghost<StoresView>,
    Ghost(seg): Ghost<Seq<u8>>, Ghost(dl): Ghost<int>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Option<(Vec<usize>, Vec<i128>)>)
    requires
        scan_facts(sv, seg, dl),
        bounds_ok(bounds, n_l(sv)),
        bounds.len() == outs@.len() + 1,
        forall|u: int| 0 <= u < outs@.len() ==> #[trigger] outs@[u].ok
            && scan_out_ok(outs@[u], sv, seg, dl, bounds[u], bounds[u + 1]) && ltop_ok(outs@[u], sv),
        seg == seg_of(ps), dl == dl_of(ps), odate@ == od(sv), n_o(sv) <= usize::MAX,
    ensures r matches Some((sel, ss)) ==> fast_ok(sel@, ss@, sv, ps),
{
    proof {
        assert forall|u: int| 0 <= u < outs@.len() implies scan_out_ok(#[trigger] outs@[u], sv, seg, dl, bounds[u], bounds[u + 1]) by {
            assert(outs@[u].ok);
        }
    }
    if !runs_in_order(outs, Ghost(bounds), Ghost(sv), Ghost(seg), Ghost(dl)) {
        return None;
    }
    let mut m = comb_new(Ghost(sv), Ghost(seg), Ghost(dl), Ghost(ps));
    let nt = outs.len();
    assert(forall|u: int| 0 <= u < outs@.len() ==> #[trigger] outs@[u].ok
        && scan_out_ok(outs@[u], sv, seg, dl, bounds[u], bounds[u + 1]) && ltop_ok(outs@[u], sv));
    let mut t: usize = 0;
    while t < nt
        invariant
            scan_facts(sv, seg, dl), bounds_ok(bounds, n_l(sv)), bounds.len() == outs@.len() + 1, nt == outs@.len(), t <= nt,
            forall|u: int| 0 <= u < outs@.len() ==> #[trigger] outs@[u].ok
                && scan_out_ok(outs@[u], sv, seg, dl, bounds[u], bounds[u + 1]) && ltop_ok(outs@[u], sv),
            forall|u: int| 0 <= u < outs@.len() ==> scan_out_ok(#[trigger] outs@[u], sv, seg, dl, bounds[u], bounds[u + 1]),
            forall|u: int| 0 <= u < outs@.len() && #[trigger] outs@[u].n > 0 ==>
                tail_above(outs@, u + 1, outs@[u].rj@[outs@[u].n - 1] as int),
            seg == seg_of(ps), dl == dl_of(ps), odate@ == od(sv), n_o(sv) <= usize::MAX,
            comb_inv(m, sv, seg, dl, ps, bounds[t as int]),
        decreases nt - t,
    {
        let o = &outs[t];
        let ghost (lo, hi) = (bounds[t as int], bounds[t + 1]);
        proof {
            assert(outs@[t as int].ok);
            lemma_bounds_mono(bounds, t + 1, bounds.len() - 1);
            assert(lo <= hi);
            if o.n > 0 {
                assert(outs@[t as int].n > 0);
                lemma_tail_zero(outs@, bounds, sv, seg, dl, t + 1, o.rj@[o.n - 1] as int);
            }
        }
        if !comb_task(&mut m, o, odate, Ghost(sv), Ghost(seg), Ghost(dl), Ghost(ps), Ghost(lo), Ghost(hi)) {
            return None;
        }
        t = t + 1;
    }
    // close the open group: its sum is final
    proof {
        assert(bounds[nt as int] == n_l(sv));
    }
    let ghost m1 = m;
    if m.open {
        let cj = m.cj;
        let cs = m.csum;
        proof {
            assert forall|i: int| 0 <= i < m.c@.len() implies m.c@[i] != cj by {
                assert(m.c@[i] < cj);
            }
        }
        comb_add(&mut m, cj, cs, odate, Ghost(sv), Ghost(seg), Ghost(dl), Ghost(ps));
    }
    proof {
        assert forall|j: int| 0 <= j < n_o(sv) && #[trigger] order_count(sv, seg, dl, j, 0, n_l(sv)) > 0 implies
            m.c@.contains(j as usize) || dominated(m, sv, ps, j) by {
            assert(dominated(m, sv, ps, j) == dominated(m1, sv, ps, j));
            if m1.c@.contains(j as usize) {
                let i = choose|i: int| 0 <= i < m1.c@.len() && m1.c@[i] == j as usize;
                assert(m.c@[i] == j as usize);
            } else if m1.open && j == m1.cj {
                assert(m.c@[m1.c@.len() as int] == j as usize);
            }
        }
        lemma_comb_final(m, sv, seg, dl, ps);
    }
    Some((m.top.sel, m.top.ss))
}

} // verus!
