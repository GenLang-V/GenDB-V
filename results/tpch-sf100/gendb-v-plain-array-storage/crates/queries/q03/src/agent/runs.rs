//! Per-task group accumulator over a range of lineitem rows (`Runs`), and the accounting of one row.
//!
//! A task scans lineitem rows `lo..q` in order; every row is mapped to an orders row (`o_orderkey` equal to its
//! `l_orderkey`), and the mapped order never decreases along the scan. A hitting row adds its value to the group of
//! its order; since the order only grows, a group is one *run* of consecutive hits, and a closed run is final.
//! `Runs` describes the closed runs as ghost sequences (`rj[t]`, `rsum[t]`, `t < n`, strictly increasing orders) and
//! keeps in memory only what the combination reads: the first closed run (`fj`, `fs`), the open run (`cur_j`,
//! `cur_sum`) and the top 10 of the other closed runs (`top`, by sum then date, each entry tagged with its order),
//! updated as each run closes (no per-run buffer). `runs_inv` relates them to the per-order sums over `lo..q`
//! (`order_sum`), states that every hit order has a run, and bounds every value by `VMAX` so that no sum can
//! overflow.
use vstd::prelude::*;
use crate::spec::numeric::abs;
use crate::gendb_entry::stores::StoresView;
use crate::agent::tables::*;
use crate::agent::normal_form::*;
use crate::agent::topk::*;

verus! {

/// Bound on `|l_extendedprice * (1 - l_discount)|` (coefficient) of a hitting row on the fast path: `2^88`.
pub const VMAX: i128 = 0x100_0000_0000_0000_0000_0000;

/// Bound on the lineitem row count on the fast path: `2^38`, so that `nl * VMAX < 2^127`.
pub const NL_MAX: u64 = 0x40_0000_0000;

/// The closed runs (ghost), the first of them, the top 10 of the others, and the open run of a task.
pub struct Runs {
    pub rj: Ghost<Seq<usize>>,
    pub rsum: Ghost<Seq<i128>>,
    pub fj: usize,
    pub fs: i128,
    pub top: FixTop,
    pub odate: &'static [i32],
    pub n: usize,
    pub open: bool,
    pub cur_j: usize,
    pub cur_sum: i128,
    pub hits: Ghost<int>,
}

/// Scan facts of a task: the column views it reads and the facts about them it relies on.
pub open spec fn scan_facts(sv: StoresView, seg: Seq<u8>, dl: int) -> bool {
    &&& parts_shape(sv)
    &&& ls(sv).len() == n_l(sv) && lp(sv).len() == n_l(sv) && ld(sv).len() == n_l(sv)
    &&& oc(sv).len() == n_o(sv) && od(sv).len() == n_o(sv)
    &&& keys_unique(ok(sv))
    &&& n_l(sv) <= NL_MAX
    &&& forall|i: int| 0 <= i < n_l(sv) ==> num15(#[trigger] lp(sv)[i]) && num15(ld(sv)[i])
}

/// `|value| <= VMAX` for every hit, summed per order: the absolute mass is at most `count * VMAX`.
pub open spec fn mass_bounded(sv: StoresView, seg: Seq<u8>, dl: int, lo: int, q: int) -> bool {
    forall|j: int| 0 <= j < n_o(sv) ==>
        #[trigger] order_abs(sv, seg, dl, j, lo, q) <= order_count(sv, seg, dl, j, lo, q) * (VMAX as int)
}

/// The interior runs of `n` runs (all but the first and the last), as run indices, and their sums.
pub open spec fn litems(n: usize) -> Seq<usize> {
    Seq::new(if n >= 2 { (n - 2) as nat } else { 0 }, |h: int| (h + 1) as usize)
}

pub open spec fn lvals(n: usize, rsum: Seq<i128>) -> Seq<i128> {
    Seq::new(litems(n).len(), |h: int| rsum[h + 1])
}

/// A run's sum, its order's date, and its order.
pub open spec fn lvf(rsum: Seq<i128>) -> spec_fn(int) -> int {
    |r: int| rsum[r] as int
}

pub open spec fn ldf(rj: Seq<usize>, sv: StoresView) -> spec_fn(int) -> int {
    |r: int| od(sv)[rj[r] as int] as int
}

pub open spec fn lof(rj: Seq<usize>) -> spec_fn(int) -> int {
    |r: int| rj[r] as int
}

/// `top` is the top 10 of the closed runs after the first (the interior runs once the open run closes), each entry
/// tagged with its order.
pub open spec fn rtop_ok(top: FixTop, n: usize, rj: Seq<usize>, rsum: Seq<i128>, sv: StoresView) -> bool {
    &&& fix_inv(top, litems((n + 1) as usize), lvals((n + 1) as usize, rsum), lvf(rsum), ldf(rj, sv))
    &&& fix_tags(top, lof(rj))
}

/// The accumulator after rows `lo..q`, whose last row maps to order `jnow`.
pub open spec fn runs_inv(r: Runs, sv: StoresView, seg: Seq<u8>, dl: int, lo: int, q: int, jnow: int, cap: int) -> bool {
    &&& r.rj@.len() == r.n && r.rsum@.len() == r.n && cap <= usize::MAX
    &&& r.n > 0 ==> r.fj == r.rj@[0] && r.fs == r.rsum@[0]
    &&& r.odate@ == od(sv) && od(sv).len() == n_o(sv)
    &&& rtop_ok(r.top, r.n, r.rj@, r.rsum@, sv)
    &&& lo <= q && q - lo <= cap
    &&& r.n + (if r.open { 1int } else { 0int }) <= r.hits@ <= q - lo
    &&& r.n > 0 ==> r.open
    &&& r.open ==> r.cur_j <= jnow && (r.cur_j as int) < n_o(sv)
    &&& forall|t: int, u: int| 0 <= t < u < r.n ==> r.rj@[t] < r.rj@[u]
    &&& forall|t: int| 0 <= t < r.n ==> r.rj@[t] < r.cur_j
    &&& forall|t: int| 0 <= t < r.n ==> #[trigger] r.rsum@[t] as int == order_sum(sv, seg, dl, r.rj@[t] as int, lo, q)
            && order_count(sv, seg, dl, r.rj@[t] as int, lo, q) > 0
    &&& r.open ==> r.cur_sum as int == order_sum(sv, seg, dl, r.cur_j as int, lo, q)
            && order_count(sv, seg, dl, r.cur_j as int, lo, q) > 0
    &&& forall|j: int| 0 <= j < n_o(sv) && #[trigger] order_count(sv, seg, dl, j, lo, q) > 0 ==>
            (exists|t: int| 0 <= t < r.n && r.rj@[t] == j) || (r.open && j == r.cur_j)
    &&& mass_bounded(sv, seg, dl, lo, q)
}

/// Lineitem row `i` belongs to order `m` (equal keys).
pub open spec fn maps_to(sv: StoresView, i: int, m: int) -> bool {
    0 <= i < n_l(sv) && 0 <= m < n_o(sv) && lk(sv)[i] == ok(sv)[m]
}

/// Row `q` of order `m` changes only `m`'s per-order quantities (the order key is unique).
pub proof fn lemma_account_row(sv: StoresView, seg: Seq<u8>, dl: int, lo: int, q: int, m: int)
    requires lo <= q, keys_unique(ok(sv)), maps_to(sv, q, m),
    ensures
        forall|j: int| 0 <= j < n_o(sv) && j != m ==> #[trigger] order_sum(sv, seg, dl, j, lo, q + 1) == order_sum(sv, seg, dl, j, lo, q),
        forall|j: int| 0 <= j < n_o(sv) && j != m ==> #[trigger] order_count(sv, seg, dl, j, lo, q + 1) == order_count(sv, seg, dl, j, lo, q),
        forall|j: int| 0 <= j < n_o(sv) && j != m ==> #[trigger] order_abs(sv, seg, dl, j, lo, q + 1) == order_abs(sv, seg, dl, j, lo, q),
        order_sum(sv, seg, dl, m, lo, q + 1) == order_sum(sv, seg, dl, m, lo, q)
            + if line_hit(sv, seg, dl, q, m) { line_value(sv, q) } else { 0 },
        order_count(sv, seg, dl, m, lo, q + 1) == order_count(sv, seg, dl, m, lo, q)
            + if line_hit(sv, seg, dl, q, m) { 1nat } else { 0nat },
        order_abs(sv, seg, dl, m, lo, q + 1) == order_abs(sv, seg, dl, m, lo, q)
            + if line_hit(sv, seg, dl, q, m) { abs(line_value(sv, q)) } else { 0 },
{
    assert forall|j: int| 0 <= j < n_o(sv) && j != m implies !line_hit(sv, seg, dl, q, j) by {
        if line_hit(sv, seg, dl, q, j) {
            assert(ok(sv)[j] == ok(sv)[m]);
        }
    }
}

/// A row that hits nothing (its order `m` is not hit by it) leaves every per-order quantity unchanged.
pub proof fn lemma_account_miss(sv: StoresView, seg: Seq<u8>, dl: int, lo: int, q: int, m: int)
    requires lo <= q, keys_unique(ok(sv)), maps_to(sv, q, m), !line_hit(sv, seg, dl, q, m),
    ensures
        forall|j: int| 0 <= j < n_o(sv) ==> #[trigger] order_sum(sv, seg, dl, j, lo, q + 1) == order_sum(sv, seg, dl, j, lo, q),
        forall|j: int| 0 <= j < n_o(sv) ==> #[trigger] order_count(sv, seg, dl, j, lo, q + 1) == order_count(sv, seg, dl, j, lo, q),
        forall|j: int| 0 <= j < n_o(sv) ==> #[trigger] order_abs(sv, seg, dl, j, lo, q + 1) == order_abs(sv, seg, dl, j, lo, q),
{
    lemma_account_row(sv, seg, dl, lo, q, m);
}

/// Rows `q..q2` hit nothing: every per-order quantity is unchanged.
pub proof fn lemma_account_misses(sv: StoresView, seg: Seq<u8>, dl: int, lo: int, q: int, q2: int, mf: spec_fn(int) -> int)
    requires
        lo <= q <= q2, keys_unique(ok(sv)),
        forall|i: int| q <= i < q2 ==> maps_to(sv, i, #[trigger] mf(i)) && !line_hit(sv, seg, dl, i, mf(i)),
    ensures
        forall|j: int| 0 <= j < n_o(sv) ==> #[trigger] order_sum(sv, seg, dl, j, lo, q2) == order_sum(sv, seg, dl, j, lo, q),
        forall|j: int| 0 <= j < n_o(sv) ==> #[trigger] order_count(sv, seg, dl, j, lo, q2) == order_count(sv, seg, dl, j, lo, q),
        forall|j: int| 0 <= j < n_o(sv) ==> #[trigger] order_abs(sv, seg, dl, j, lo, q2) == order_abs(sv, seg, dl, j, lo, q),
    decreases q2 - q,
{
    if q2 > q {
        lemma_account_misses(sv, seg, dl, lo, q, q2 - 1, mf);
        let m = mf(q2 - 1);
        assert(maps_to(sv, q2 - 1, m) && !line_hit(sv, seg, dl, q2 - 1, m));
        lemma_account_miss(sv, seg, dl, lo, q2 - 1, m);
        assert forall|j: int| 0 <= j < n_o(sv) implies #[trigger] order_sum(sv, seg, dl, j, lo, q2) == order_sum(sv, seg, dl, j, lo, q) by {
            assert(order_sum(sv, seg, dl, j, lo, q2) == order_sum(sv, seg, dl, j, lo, q2 - 1));
            assert(order_sum(sv, seg, dl, j, lo, q2 - 1) == order_sum(sv, seg, dl, j, lo, q));
        }
        assert forall|j: int| 0 <= j < n_o(sv) implies #[trigger] order_count(sv, seg, dl, j, lo, q2) == order_count(sv, seg, dl, j, lo, q) by {
            assert(order_count(sv, seg, dl, j, lo, q2) == order_count(sv, seg, dl, j, lo, q2 - 1));
            assert(order_count(sv, seg, dl, j, lo, q2 - 1) == order_count(sv, seg, dl, j, lo, q));
        }
        assert forall|j: int| 0 <= j < n_o(sv) implies #[trigger] order_abs(sv, seg, dl, j, lo, q2) == order_abs(sv, seg, dl, j, lo, q) by {
            assert(order_abs(sv, seg, dl, j, lo, q2) == order_abs(sv, seg, dl, j, lo, q2 - 1));
            assert(order_abs(sv, seg, dl, j, lo, q2 - 1) == order_abs(sv, seg, dl, j, lo, q));
        }
    }
}

/// The invariant survives rows that hit nothing.
pub proof fn lemma_runs_misses(r: Runs, sv: StoresView, seg: Seq<u8>, dl: int, lo: int, q: int, q2: int, jnow: int, jnow2: int,
    cap: int, mf: spec_fn(int) -> int)
    requires
        runs_inv(r, sv, seg, dl, lo, q, jnow, cap),
        q <= q2, q2 - lo <= cap, jnow <= jnow2, keys_unique(ok(sv)),
        forall|i: int| q <= i < q2 ==> maps_to(sv, i, #[trigger] mf(i)) && !line_hit(sv, seg, dl, i, mf(i)),
    ensures runs_inv(r, sv, seg, dl, lo, q2, jnow2, cap),
{
    lemma_account_misses(sv, seg, dl, lo, q, q2, mf);
    assert forall|j: int| 0 <= j < n_o(sv) && #[trigger] order_count(sv, seg, dl, j, lo, q2) > 0 implies
        (exists|t: int| 0 <= t < r.n && r.rj@[t] == j) || (r.open && j == r.cur_j) by {
        assert(order_count(sv, seg, dl, j, lo, q) > 0);
    }
    assert forall|t: int| 0 <= t < r.n implies #[trigger] r.rsum@[t] as int == order_sum(sv, seg, dl, r.rj@[t] as int, lo, q2)
        && order_count(sv, seg, dl, r.rj@[t] as int, lo, q2) > 0 by {
        assert(r.rsum@[t] as int == order_sum(sv, seg, dl, r.rj@[t] as int, lo, q));
    }
    assert(mass_bounded(sv, seg, dl, lo, q2)) by {
        assert forall|j: int| 0 <= j < n_o(sv) implies
            #[trigger] order_abs(sv, seg, dl, j, lo, q2) <= order_count(sv, seg, dl, j, lo, q2) * (VMAX as int) by {
            assert(order_abs(sv, seg, dl, j, lo, q) <= order_count(sv, seg, dl, j, lo, q) * (VMAX as int));
        }
    }
}

/// An empty accumulator over `lo..lo`.
pub proof fn lemma_runs_empty(r: Runs, sv: StoresView, seg: Seq<u8>, dl: int, lo: int, jnow: int, cap: int)
    requires
        r.rj@.len() == 0, r.rsum@.len() == 0, 0 <= cap <= usize::MAX,
        r.n == 0, !r.open, r.hits@ == 0, fix_wf(r.top), r.top.k == 0,
        r.odate@ == od(sv), od(sv).len() == n_o(sv),
    ensures runs_inv(r, sv, seg, dl, lo, lo, jnow, cap),
{
    lemma_top_empty(lvf(r.rsum@), ldf(r.rj@, sv));
    assert(litems(1) =~= Seq::<usize>::empty());
    assert(lvals(1, r.rsum@) =~= Seq::<i128>::empty());
    assert(fsel(r.top) =~= Seq::<usize>::empty());
    assert(fss(r.top) =~= Seq::<i128>::empty());
    assert(fsd(r.top) =~= Seq::<i32>::empty());
}

/// The selected runs are interior runs `1..n` of the closed runs.
pub proof fn lemma_rtop_below(top: FixTop, n: usize, rj: Seq<usize>, rsum: Seq<i128>, sv: StoresView)
    requires rtop_ok(top, n, rj, rsum, sv), n + 1 <= usize::MAX,
    ensures forall|q: int| 0 <= q < top.k ==> 1 <= #[trigger] top.ti@[q] < n,
{
    let items = litems((n + 1) as usize);
    assert forall|q: int| 0 <= q < top.k implies 1 <= #[trigger] top.ti@[q] < n by {
        assert(fsel(top)[q] == top.ti@[q]);
        assert(among(items, items.len() as int, fsel(top)[q]));
        let h = choose|h: int| 0 <= h < items.len() && items[h] == fsel(top)[q];
        assert(items[h] == (h + 1) as usize);
    }
}

/// Closing run `n` (order `j`, sum `s`) after the closed runs `rj`/`rsum`: the selection over the runs after the
/// first carries over to the longer sequences (as is when `n == 0`, else after `fix_step` with item `n`).
pub proof fn lemma_rtop_close(top: FixTop, n: usize, rj: Seq<usize>, rsum: Seq<i128>, j: usize, s: i128, sv: StoresView)
    requires rtop_ok(top, n, rj, rsum, sv), rj.len() == n, rsum.len() == n, n + 1 <= usize::MAX,
    ensures
        n == 0 ==> rtop_ok(top, (n + 1) as usize, rj.push(j), rsum.push(s), sv),
        n > 0 ==> fix_inv(top, litems((n + 1) as usize), lvals((n + 1) as usize, rsum), lvf(rsum.push(s)), ldf(rj.push(j), sv))
            && fix_tags(top, lof(rj.push(j))),
        n > 0 && n + 2 <= usize::MAX ==> {
            &&& items_ok(litems((n + 1) as usize).push(n), lvals((n + 1) as usize, rsum).push(s), lvf(rsum.push(s)))
            &&& litems((n + 1) as usize).push(n) == litems((n + 2) as usize)
            &&& lvals((n + 1) as usize, rsum).push(s) == lvals((n + 2) as usize, rsum.push(s))
            &&& ldf(rj.push(j), sv)(n as int) == od(sv)[j as int] as int
            &&& lof(rj.push(j))(n as int) == j as int
        },
{
    let (rj1, rs1) = (rj.push(j), rsum.push(s));
    let items = litems((n + 1) as usize);
    lemma_rtop_below(top, n, rj, rsum, sv);
    assert forall|h: int| 0 <= h < items.len() implies lvf(rsum)(#[trigger] items[h] as int) == lvf(rs1)(items[h] as int)
        && ldf(rj, sv)(items[h] as int) == ldf(rj1, sv)(items[h] as int) by {
        assert(items[h] == (h + 1) as usize);
        assert(rs1[h + 1] == rsum[h + 1] && rj1[h + 1] == rj[h + 1]);
    }
    lemma_fix_congr(top, items, lvals((n + 1) as usize, rsum), lvf(rsum), ldf(rj, sv), lvf(rs1), ldf(rj1, sv));
    assert forall|q: int| 0 <= q < top.k implies lof(rj)(#[trigger] top.ti@[q] as int) == lof(rj1)(top.ti@[q] as int) by {
        assert(rj1[top.ti@[q] as int] == rj[top.ti@[q] as int]);
    }
    lemma_tags_congr(top, lof(rj), lof(rj1));
    if n == 0 {
        assert(litems(2) =~= litems(1));
        assert(lvals(2, rs1) =~= lvals(1, rsum));
    } else if n + 2 <= usize::MAX {
        let (gj, gs) = (items.push(n), lvals((n + 1) as usize, rsum).push(s));
        assert(gj =~= litems((n + 2) as usize));
        assert(gs =~= lvals((n + 2) as usize, rs1)) by {
            assert forall|h: int| 0 <= h < gs.len() implies gs[h] == lvals((n + 2) as usize, rs1)[h] by {
                assert(rs1[h + 1] == if h + 1 < n { rsum[h + 1] } else { s });
            }
        }
        assert(gj.no_duplicates()) by {
            assert forall|a: int, b: int| 0 <= a < gj.len() && 0 <= b < gj.len() && a != b implies gj[a] != gj[b] by {
                assert(gj[a] == (a + 1) as usize && gj[b] == (b + 1) as usize);
            }
        }
        assert forall|h: int| 0 <= h < gj.len() implies #[trigger] gs[h] as int == lvf(rs1)(gj[h] as int) by {
            assert(gj[h] == (h + 1) as usize);
            assert(gs[h] == lvals((n + 2) as usize, rs1)[h]);
        }
    }
}

/// Absolute sums bound sums; counts bound masses.
pub proof fn lemma_sum_bound(sv: StoresView, seg: Seq<u8>, dl: int, j: int, lo: int, q: int)
    requires
        lo <= q, q - lo <= NL_MAX, 0 <= j < n_o(sv),
        order_abs(sv, seg, dl, j, lo, q) <= order_count(sv, seg, dl, j, lo, q) * (VMAX as int),
    ensures
        -(order_count(sv, seg, dl, j, lo, q) * (VMAX as int)) <= order_sum(sv, seg, dl, j, lo, q) <= order_count(sv, seg, dl, j, lo, q) * (VMAX as int),
        order_count(sv, seg, dl, j, lo, q) * (VMAX as int) <= (NL_MAX as int) * (VMAX as int),
{
    lemma_order_bounds(sv, seg, dl, j, lo, q);
    let c = order_count(sv, seg, dl, j, lo, q) as int;
    assert(c * (VMAX as int) <= (NL_MAX as int) * (VMAX as int)) by (nonlinear_arith)
        requires 0 <= c <= NL_MAX, VMAX > 0;
}

/// Row `q` hits order `m` (the scan's current order, at least `jnow`), with `|value| <= VMAX`: add it to the open
/// run, or close the open run and open a run for `m`.
pub fn runs_hit(r: &mut Runs, m: usize, v: i128, Ghost(sv): Ghost<StoresView>, Ghost(seg): Ghost<Seq<u8>>, Ghost(dl): Ghost<int>,
    Ghost(lo): Ghost<int>, Ghost(q): Ghost<int>, Ghost(jnow): Ghost<int>, Ghost(cap): Ghost<int>)
    requires
        runs_inv(*old(r), sv, seg, dl, lo, q, jnow, cap),
        q + 1 - lo <= cap, q - lo < NL_MAX,
        keys_unique(ok(sv)),
        maps_to(sv, q, m as int), jnow <= m,
        line_hit(sv, seg, dl, q, m as int),
        v as int == line_value(sv, q),
        -VMAX <= v <= VMAX,
    ensures runs_inv(*final(r), sv, seg, dl, lo, q + 1, m as int, cap),
    no_unwind
{
    proof {
        lemma_account_row(sv, seg, dl, lo, q, m as int);
    }
    let ghost old_r = *r;
    if r.open && r.cur_j == m {
        proof {
            lemma_sum_bound(sv, seg, dl, m as int, lo, q);
        }
        r.cur_sum = r.cur_sum + v;
    } else {
        if r.open {
            let n = r.n;
            let cj = r.cur_j;
            let cs = r.cur_sum;
            let ghost (rj0, rs0) = (r.rj@, r.rsum@);
            proof {
                // the open run and the hitting row q are counted: n + 2 <= q + 1 - lo <= cap
                assert(n + 2 <= cap);
                lemma_rtop_close(r.top, n, rj0, rs0, cj, cs, sv);
            }
            if n == 0 {
                r.fj = cj;
                r.fs = cs;
            } else {
                // the closed run is interior (a later run exists): it competes for the task's top 10
                fix_step(&mut r.top, n, cs, r.odate, cj, cj, Ghost(litems((n + 1) as usize)), Ghost(lvals((n + 1) as usize, rs0)),
                    Ghost(lvf(rs0.push(cs))), Ghost(ldf(rj0.push(cj), sv)), Ghost(lof(rj0.push(cj))), Ghost(od(sv).len() as int));
            }
            r.rj = Ghost(rj0.push(cj));
            r.rsum = Ghost(rs0.push(cs));
            r.n = n + 1;
        }
        r.open = true;
        r.cur_j = m;
        r.cur_sum = v;
    }
    r.hits = Ghost(r.hits@ + 1);
    proof {
        let ghost old_count = order_count(sv, seg, dl, m as int, lo, q);
        if old_r.open && old_r.cur_j != m {
            // m is past the old open run, so it has no run yet and nothing counted before
            assert(old_r.cur_j < m);
        }
        if !(old_r.open && old_r.cur_j == m) {
            assert(old_count == 0) by {
                if old_count > 0 {
                    if exists|t: int| 0 <= t < old_r.n && old_r.rj@[t] == m {
                        let t = choose|t: int| 0 <= t < old_r.n && old_r.rj@[t] == m;
                        assert(old_r.rj@[t] < old_r.cur_j);
                    }
                }
            }
            lemma_order_bounds(sv, seg, dl, m as int, lo, q);
        }
        assert forall|j: int| 0 <= j < n_o(sv) && #[trigger] order_count(sv, seg, dl, j, lo, q + 1) > 0 implies
            (exists|t: int| 0 <= t < r.n && r.rj@[t] == j) || (r.open && j == r.cur_j) by {
            if j != m {
                assert(order_count(sv, seg, dl, j, lo, q) > 0);
                if old_r.open && j == old_r.cur_j && old_r.cur_j != m {
                    assert(r.rj@[old_r.n as int] == j);
                } else if exists|t: int| 0 <= t < old_r.n && old_r.rj@[t] == j {
                    let t = choose|t: int| 0 <= t < old_r.n && old_r.rj@[t] == j;
                    assert(r.rj@[t] == j);
                }
            }
        }
        assert forall|t: int| 0 <= t < r.n implies #[trigger] r.rsum@[t] as int == order_sum(sv, seg, dl, r.rj@[t] as int, lo, q + 1)
            && order_count(sv, seg, dl, r.rj@[t] as int, lo, q + 1) > 0 by {
            if t < old_r.n {
                assert(r.rj@[t] == old_r.rj@[t] && r.rsum@[t] == old_r.rsum@[t]);
                assert(old_r.rj@[t] < old_r.cur_j);
                assert(old_r.rj@[t] as int != m);
            } else {
                assert(r.rj@[t] == old_r.cur_j && old_r.cur_j as int != m);
            }
        }
        assert forall|t: int, u: int| 0 <= t < u < r.n implies r.rj@[t] < r.rj@[u] by {
            if u == old_r.n && old_r.open && old_r.cur_j != m {
                assert(r.rj@[t] == old_r.rj@[t]);
            }
        }
        assert(mass_bounded(sv, seg, dl, lo, q + 1)) by {
            assert forall|j: int| 0 <= j < n_o(sv) implies
                #[trigger] order_abs(sv, seg, dl, j, lo, q + 1) <= order_count(sv, seg, dl, j, lo, q + 1) * (VMAX as int) by {
                assert(order_abs(sv, seg, dl, j, lo, q) <= order_count(sv, seg, dl, j, lo, q) * (VMAX as int));
                if j == m {
                    let c = order_count(sv, seg, dl, j, lo, q) as int;
                    assert((c + 1) * (VMAX as int) == c * (VMAX as int) + VMAX as int) by (nonlinear_arith);
                }
            }
        }
    }
}

} // verus!
