//! The qualification of each hit row and the result totals: a hit row qualifies when its quantity is below the
//! subquery's value of its part key (`joined::below`), and the result is the number and price sum of the
//! qualifying rows (`f_cnt`/`f_price`, as range sums over the lineitem rows).
//!
//! - Fast path (`all_fast`: every non-empty slot has `|sum| < 10^6` and fewer than `2 * 10^14` rows): the test is
//!   `5 * q * cnt < sum` (`avgcmp::lemma_below_fast`), on the calling thread.
//! - Exact path (otherwise; calling thread): per non-empty slot PostgreSQL's AVG `A` at scale `r`
//!   (`num_div_exec`), and the test `5 * q * 10^(r - 2) < A` (`cmp_scaled`, `avgcmp::lemma_below_scaled`); a slot
//!   whose division leaves its executable domain is reported (`Err(slot)`, the capacity outcome).
use vstd::prelude::*;
use crate::spec::ast::Literal;
use crate::spec::fns::div::*;
use crate::spec::value::*;
use crate::gendb_entry::stores::StoresView;
use crate::exec::value::{EVal, view_result};
use crate::exec::fns::div::num_div_exec;
use crate::exec::numeric::cmp_scaled;
use crate::agent::tables::*;
use crate::agent::sub::*;
use crate::agent::joined::*;
use crate::agent::avgcmp::*;
use crate::agent::keys::*;
use crate::agent::scan::*;
use crate::agent::group::*;
use crate::agent::parts::{split_at, lemma_split};
use crate::agent::common::selection::*;
use crate::agent::common::keyset::*;

verus! {

// ------------------------------------------------------------------------------------------------ per-row terms

/// The terms of a hit row: 1 / its price coefficient when its quantity is below its key's subquery value.
pub open spec fn fcnt(sv: StoresView) -> spec_fn(int) -> int {
    |l: int| if below(sv, l_qty(sv)[l] as int, l_pkey(sv)[l] as int) { 1int } else { 0int }
}
pub open spec fn fprice(sv: StoresView) -> spec_fn(int) -> int {
    |l: int| if below(sv, l_qty(sv)[l] as int, l_pkey(sv)[l] as int) { l_price(sv)[l] as int } else { 0int }
}

/// The comparison with the subquery's value of a non-empty key is the AVG comparison of its totals.
pub proof fn lemma_below_avg(sv: StoresView, q: int, k: int)
    requires kcnt(sv, k) > 0,
    ensures below(sv, q, k) == below_avg(q, ksum(sv, k), kcnt(sv, k)),
{
}

// ------------------------------------------------------------------------------------------------ the slot totals

/// The per-slot totals, shared by the final tasks.
pub struct Thr {
    pub sums: Vec<i128>,
    pub cnts: Vec<i128>,
}

/// The totals of every slot's key.
pub open spec fn thr_ok(thr: &Thr, keys: Seq<i64>, sv: StoresView) -> bool {
    &&& thr.sums@.len() == keys.len() && thr.cnts@.len() == keys.len()
    &&& forall|s: int| 0 <= s < keys.len() ==> #[trigger] thr.sums@[s] as int == ksum(sv, keys[s] as int)
            && thr.cnts@[s] as int == kcnt(sv, keys[s] as int)
}

/// Slot `s` is empty or inside the fast form's bounds.
pub open spec fn slot_fast(thr: &Thr, s: int) -> bool {
    thr.cnts@[s] == 0 || (thr.cnts@[s] < 200_000_000_000_000 && -1_000_000 < thr.sums@[s] < 1_000_000)
}

pub open spec fn all_fast(thr: &Thr) -> bool {
    forall|s: int| 0 <= s < thr.cnts@.len() ==> #[trigger] slot_fast(thr, s)
}

/// Whether every slot is inside the fast form's bounds.
pub fn check_fast(thr: &Thr) -> (b: bool)
    requires thr.sums@.len() == thr.cnts@.len(),
    ensures b == all_fast(thr),
{
    let n = thr.cnts.len();
    let mut s: usize = 0;
    while s < n
        invariant n == thr.cnts@.len(), thr.sums@.len() == n, s <= n,
            forall|u: int| 0 <= u < s ==> #[trigger] slot_fast(thr, u),
        decreases n - s,
    {
        let c = thr.cnts[s];
        let m = thr.sums[s];
        if !(c == 0 || (c < 200_000_000_000_000 && -1_000_000 < m && m < 1_000_000)) {
            assert(!slot_fast(thr, s as int));
            return false;
        }
        s = s + 1;
    }
    true
}

// ------------------------------------------------------------------------------------------------ fast path

/// The fast test of one hit record: `5 * q * cnt < sum`, which is `below` for the record's row.
fn fast_below(h: &Hits, j: usize, thr: &Thr, Ghost(rows): Ghost<Seq<int>>, Ghost(keys): Ghost<Seq<i64>>, Ghost(sv): Ghost<StoresView>)
    -> (b: bool)
    requires hits_ok(h, rows, keys, sv), j < h.used, thr_ok(thr, keys, sv), all_fast(thr), domains_ok(sv), sizes_ok(sv),
    ensures b == below(sv, l_qty(sv)[rows[j as int]] as int, l_pkey(sv)[rows[j as int]] as int),
    no_unwind
{
    let (s, q, _pr) = h.recs[j];
    let ghost l = rows[j as int];
    proof {
        assert(rec_ok(h.recs@[j as int], l, keys, sv));
        assert(num15(l_qty(sv)[l]));
        let k = keys[s as int] as int;
        assert(k == l_pkey(sv)[l] as int);
        lemma_kcnt_pos(sv, l);
        assert(slot_fast(thr, s as int));
        lemma_below_fast(q as int, thr.sums@[s as int] as int, thr.cnts@[s as int] as int);
        lemma_below_avg(sv, q as int, k);
    }
    let c = thr.cnts[s];
    let m = thr.sums[s];
    let q5 = 5 * (q as i128);
    assert(-5_000_000_000_000_000 < q5 < 5_000_000_000_000_000);
    assert(-1_000_000_000_000_000_000_000_000_000_000 < q5 * c < 1_000_000_000_000_000_000_000_000_000_000) by (nonlinear_arith)
        requires -5_000_000_000_000_000 < q5 < 5_000_000_000_000_000, 0 < c < 200_000_000_000_000;
    assert(q5 * c == 5 * (q as int) * (c as int)) by (nonlinear_arith) requires q5 == 5 * (q as int);
    q5 * c < m
}

/// The totals of the qualifying rows among the hit records `h` (rows `rows`).
pub fn final_hits(h: &Hits, thr: &Thr, Ghost(rows): Ghost<Seq<int>>, Ghost(keys): Ghost<Seq<i64>>, Ghost(sv): Ghost<StoresView>)
    -> (r: (i128, i128))
    requires
        hits_ok(h, rows, keys, sv), thr_ok(thr, keys, sv), all_fast(thr), domains_ok(sv), sizes_ok(sv),
        rows.len() <= n_l(sv),
    ensures r.0 as int == seq_sum(rows, fprice(sv)), r.1 as int == seq_sum(rows, fcnt(sv)),
    no_unwind
{
    let used = h.used;
    let mut tot: i128 = 0;
    let mut cnt: i128 = 0;
    let mut j: usize = 0;
    while j < used
        invariant
            hits_ok(h, rows, keys, sv), thr_ok(thr, keys, sv), all_fast(thr), domains_ok(sv), sizes_ok(sv),
            used == h.used, j <= used, rows.len() <= n_l(sv),
            tot as int == seq_sum(rows.take(j as int), fprice(sv)),
            cnt as int == seq_sum(rows.take(j as int), fcnt(sv)),
        decreases used - j,
    {
        let ghost l = rows[j as int];
        let ghost xs = rows.take(j as int);
        proof {
            assert(rec_ok(h.recs@[j as int], l, keys, sv));
            assert forall|u: int| 0 <= u < xs.len() implies -999_999_999_999_999 <= #[trigger] (fprice(sv))(xs[u]) <= 999_999_999_999_999 by {
                assert(rec_ok(h.recs@[u], rows[u], keys, sv));
                assert(xs[u] == rows[u]);
                assert(num15(l_qty(sv)[xs[u]]) && num15(l_price(sv)[xs[u]]));
            }
            lemma_seq_sum_bound(xs, fprice(sv));
            assert forall|u: int| 0 <= u < xs.len() implies -999_999_999_999_999 <= #[trigger] (fcnt(sv))(xs[u]) <= 999_999_999_999_999 by {}
            lemma_seq_sum_bound(xs, fcnt(sv));
            lemma_sum_bound_small();
            let m = xs.len() + 1;
            assert(m <= n_l(sv));
            assert(n_l(sv) <= usize::MAX as int);
            assert(usize::MAX as int <= 0xffff_ffff_ffff_ffff);
            assert(999_999_999_999_999 * m < sum_bound()) by (nonlinear_arith)
                requires 0 <= m <= 0xffff_ffff_ffff_ffff;
            assert(num15(l_qty(sv)[l]) && num15(l_price(sv)[l]));
            lemma_seq_sum_push(xs, l, fprice(sv));
            lemma_seq_sum_push(xs, l, fcnt(sv));
            assert(rows.take(j + 1) =~= xs.push(l));
        }
        if fast_below(h, j, thr, Ghost(rows), Ghost(keys), Ghost(sv)) {
            tot = tot + h.recs[j].2 as i128;
            cnt = cnt + 1;
        }
        j = j + 1;
    }
    proof { assert(rows.take(used as int) =~= rows); }
    (tot, cnt)
}

/// The rows of range `t` of `nt` listed by `keys`.
pub open spec fn range_rows(sv: StoresView, keys: Seq<i64>, nt: int, t: int) -> Seq<int> {
    range_filter(split_at(n_l(sv) as int, nt, t), split_at(n_l(sv) as int, nt, t + 1), inrow(keys, sv))
}

/// The totals of all hit rows from the totals `res[t]` of each range, summed in range order.
fn sum_ranges(res: &Vec<(i128, i128)>, nt: usize, Ghost(keys): Ghost<Seq<i64>>, Ghost(sv): Ghost<StoresView>) -> (r: (i128, i128))
    requires
        1 <= nt, res@.len() == nt, domains_ok(sv), sizes_ok(sv),
        forall|u: int| 0 <= u < nt ==> (#[trigger] res@[u]).0 as int == seq_sum(range_rows(sv, keys, nt as int, u), fprice(sv))
            && res@[u].1 as int == seq_sum(range_rows(sv, keys, nt as int, u), fcnt(sv)),
    ensures
        r.0 as int == seq_sum(range_filter(0, n_l(sv) as int, inrow(keys, sv)), fprice(sv)),
        r.1 as int == seq_sum(range_filter(0, n_l(sv) as int, inrow(keys, sv)), fcnt(sv)),
{
    let ghost nl = n_l(sv) as int;
    let ghost p = inrow(keys, sv);
    let mut tot: i128 = 0;
    let mut cnt: i128 = 0;
    let mut t: usize = 0;
    proof {
        lemma_split(nl, nt as int, 0);
        assert(range_filter(0, 0, p) =~= Seq::<int>::empty());
    }
    while t < nt
        invariant
            1 <= nt, t <= nt, res@.len() == nt, p == inrow(keys, sv), nl == n_l(sv), domains_ok(sv), sizes_ok(sv),
            forall|u: int| 0 <= u < nt ==> (#[trigger] res@[u]).0 as int == seq_sum(range_rows(sv, keys, nt as int, u), fprice(sv))
                && res@[u].1 as int == seq_sum(range_rows(sv, keys, nt as int, u), fcnt(sv)),
            tot as int == seq_sum(range_filter(0, split_at(nl, nt as int, t as int), p), fprice(sv)),
            cnt as int == seq_sum(range_filter(0, split_at(nl, nt as int, t as int), p), fcnt(sv)),
        decreases nt - t,
    {
        let ghost x0 = range_filter(0, split_at(nl, nt as int, t as int), p);
        let ghost rt = range_rows(sv, keys, nt as int, t as int);
        proof {
            lemma_split(nl, nt as int, t as int);
            lemma_flat_step(nl, nt as int, t as int, p);
            let x1 = range_filter(0, split_at(nl, nt as int, t + 1), p);
            lemma_range_filter_members(0, split_at(nl, nt as int, t + 1), p);
            assert(x0 + rt == x1);
            lemma_seq_sum_concat(x0, rt, fprice(sv));
            lemma_seq_sum_concat(x0, rt, fcnt(sv));
            // bounds of the totals so far
            assert forall|u: int| 0 <= u < x1.len() implies -999_999_999_999_999 <= #[trigger] (fprice(sv))(x1[u]) <= 999_999_999_999_999 by {
                assert(0 <= x1[u] < nl);
                assert(num15(l_qty(sv)[x1[u]]) && num15(l_price(sv)[x1[u]]));
            }
            lemma_seq_sum_bound(x1, fprice(sv));
            assert forall|u: int| 0 <= u < x1.len() implies -999_999_999_999_999 <= #[trigger] (fcnt(sv))(x1[u]) <= 999_999_999_999_999 by {}
            lemma_seq_sum_bound(x1, fcnt(sv));
            lemma_sum_bound_small();
            let m = x1.len();
            assert(m <= nl);
            assert(nl <= usize::MAX as int);
            assert(usize::MAX as int <= 0xffff_ffff_ffff_ffff);
            assert(999_999_999_999_999 * m < sum_bound()) by (nonlinear_arith)
                requires 0 <= m <= 0xffff_ffff_ffff_ffff;
        }
        let (a, b) = res[t];
        tot = tot + a;
        cnt = cnt + b;
        t = t + 1;
    }
    proof { lemma_split(nl, nt as int, (nt - 1) as int); }
    (tot, cnt)
}


/// The totals of every hit row (the listed rows), with the fast test, on the calling thread (a few hundred
/// thousand records: cheaper than spawning workers).
pub fn final_fast(outs: &Vec<Hits>, nt: usize, thr: &Thr, Ghost(keys): Ghost<Seq<i64>>, Ghost(sv): Ghost<StoresView>)
    -> (r: (i128, i128))
    requires
        1 <= nt, scan_ok(outs@, nt as int, keys, sv),
        thr_ok(thr, keys, sv), all_fast(thr), domains_ok(sv), sizes_ok(sv),
    ensures
        r.0 as int == seq_sum(range_filter(0, n_l(sv) as int, inrow(keys, sv)), fprice(sv)),
        r.1 as int == seq_sum(range_filter(0, n_l(sv) as int, inrow(keys, sv)), fcnt(sv)),
{
    let ghost nl = n_l(sv) as int;
    let ghost p = inrow(keys, sv);
    // the totals of each range
    let mut res: Vec<(i128, i128)> = Vec::new();
    let mut t: usize = 0;
    while t < nt
        invariant
            1 <= nt, t <= nt, scan_ok(outs@, nt as int, keys, sv), p == inrow(keys, sv), nl == n_l(sv),
            thr_ok(thr, keys, sv), all_fast(thr), domains_ok(sv), sizes_ok(sv),
            res@.len() == t,
            forall|u: int| 0 <= u < t ==> (#[trigger] res@[u]).0 as int == seq_sum(range_rows(sv, keys, nt as int, u), fprice(sv))
                && res@[u].1 as int == seq_sum(range_rows(sv, keys, nt as int, u), fcnt(sv)),
        decreases nt - t,
    {
        proof {
            lemma_split(nl, nt as int, t as int);
            lemma_range_filter_members(split_at(nl, nt as int, t as int), split_at(nl, nt as int, t + 1), p);
        }
        let r0 = final_hits(&outs[t], thr, Ghost(range_rows(sv, keys, nt as int, t as int)), Ghost(keys), Ghost(sv));
        res.push(r0);
        t = t + 1;
    }
    sum_ranges(&res, nt, Ghost(keys), Ghost(sv))
}

// ------------------------------------------------------------------------------------------------ exact path

/// The AVG of every non-empty slot: coefficient and scale.
pub struct Avgs {
    pub coef: Vec<i128>,
    pub scale: Vec<u32>,
}

pub open spec fn avgs_ok(av: &Avgs, thr: &Thr, keys: Seq<i64>, sv: StoresView) -> bool {
    &&& av.coef@.len() == keys.len() && av.scale@.len() == keys.len()
    &&& forall|s: int| 0 <= s < keys.len() && #[trigger] thr.cnts@[s] != 0 ==>
            av.coef@[s] as int == avg_coeff(sv, keys[s] as int) && av.scale@[s] as nat == avg_scale(sv, keys[s] as int)
}

/// The AVG of every non-empty slot (`num_div_exec`), or the first slot whose division leaves its executable
/// domain.
pub fn slot_avgs(thr: &Thr, Ghost(keys): Ghost<Seq<i64>>, Ghost(sv): Ghost<StoresView>) -> (r: Result<Avgs, usize>)
    requires thr_ok(thr, keys, sv), domains_ok(sv), sizes_ok(sv),
    ensures
        r matches Ok(av) ==> avgs_ok(&av, thr, keys, sv),
        r matches Err(s) ==> s < keys.len() && kcnt(sv, keys[s as int] as int) > 0
            && !num_div_fits(ksum(sv, keys[s as int] as int), 2, kcnt(sv, keys[s as int] as int), 0),
{
    let n = thr.cnts.len();
    let mut coef: Vec<i128> = Vec::new();
    let mut scale: Vec<u32> = Vec::new();
    let mut s: usize = 0;
    while s < n
        invariant
            thr_ok(thr, keys, sv), domains_ok(sv), sizes_ok(sv), n == keys.len(), s <= n,
            coef@.len() == s, scale@.len() == s,
            forall|u: int| 0 <= u < s && #[trigger] thr.cnts@[u] != 0 ==>
                coef@[u] as int == avg_coeff(sv, keys[u] as int) && scale@[u] as nat == avg_scale(sv, keys[u] as int),
        decreases n - s,
    {
        let c = thr.cnts[s];
        if c == 0 {
            coef.push(0);
            scale.push(0);
        } else {
            let ghost k = keys[s as int] as int;
            proof {
                assert(thr.sums@[s as int] as int == ksum(sv, k));
                assert(thr.cnts@[s as int] as int == kcnt(sv, k));
                lemma_ktotals_bounds(sv, k);
                lemma_avg_in_range(sv, k);
            }
            match num_div_exec(thr.sums[s], 2, c, 0) {
                Ok(Ok(EVal::Num { coeff, scale: sc })) => {
                    coef.push(coeff);
                    scale.push(sc);
                },
                Ok(_) => {
                    proof { assert(false); }
                    return Err(s);
                },
                Err(_) => {
                    return Err(s);
                },
            }
        }
        s = s + 1;
    }
    Ok(Avgs { coef, scale })
}

/// The exact test of one hit record: `5 * q * 10^(r - 2) < A`, which is `below` for the record's row.
fn exact_below(h: &Hits, j: usize, thr: &Thr, av: &Avgs, Ghost(rows): Ghost<Seq<int>>, Ghost(keys): Ghost<Seq<i64>>,
    Ghost(sv): Ghost<StoresView>) -> (b: bool)
    requires hits_ok(h, rows, keys, sv), j < h.used, thr_ok(thr, keys, sv), avgs_ok(av, thr, keys, sv), domains_ok(sv), sizes_ok(sv),
    ensures b == below(sv, l_qty(sv)[rows[j as int]] as int, l_pkey(sv)[rows[j as int]] as int),
{
    let (s, q, _pr) = h.recs[j];
    let ghost l = rows[j as int];
    let ghost k = keys[s as int] as int;
    proof {
        assert(rec_ok(h.recs@[j as int], l, keys, sv));
        assert(num15(l_qty(sv)[l]));
        assert(k == l_pkey(sv)[l] as int);
        lemma_kcnt_pos(sv, l);
        assert(thr.sums@[s as int] as int == ksum(sv, k));
        assert(thr.cnts@[s as int] != 0);
        lemma_below_scaled(q as int, ksum(sv, k), kcnt(sv, k));
        lemma_below_avg(sv, q as int, k);
    }
    let a = av.coef[s];
    let r = av.scale[s];
    let q5 = 5 * (q as i128);
    let c = cmp_scaled(q5, r - 2, a);
    c < 0
}

/// The totals of the qualifying rows among the hit records `h` (rows `rows`), with the exact test.
pub fn exact_hits(h: &Hits, thr: &Thr, av: &Avgs, Ghost(rows): Ghost<Seq<int>>, Ghost(keys): Ghost<Seq<i64>>, Ghost(sv): Ghost<StoresView>)
    -> (r: (i128, i128))
    requires
        hits_ok(h, rows, keys, sv), thr_ok(thr, keys, sv), avgs_ok(av, thr, keys, sv), domains_ok(sv), sizes_ok(sv),
        rows.len() <= n_l(sv),
    ensures r.0 as int == seq_sum(rows, fprice(sv)), r.1 as int == seq_sum(rows, fcnt(sv)),
{
    let used = h.used;
    let mut tot: i128 = 0;
    let mut cnt: i128 = 0;
    let mut j: usize = 0;
    while j < used
        invariant
            hits_ok(h, rows, keys, sv), thr_ok(thr, keys, sv), avgs_ok(av, thr, keys, sv), domains_ok(sv), sizes_ok(sv),
            used == h.used, j <= used, rows.len() <= n_l(sv),
            tot as int == seq_sum(rows.take(j as int), fprice(sv)),
            cnt as int == seq_sum(rows.take(j as int), fcnt(sv)),
        decreases used - j,
    {
        let ghost l = rows[j as int];
        let ghost xs = rows.take(j as int);
        proof {
            assert(rec_ok(h.recs@[j as int], l, keys, sv));
            assert forall|u: int| 0 <= u < xs.len() implies -999_999_999_999_999 <= #[trigger] (fprice(sv))(xs[u]) <= 999_999_999_999_999 by {
                assert(rec_ok(h.recs@[u], rows[u], keys, sv));
                assert(xs[u] == rows[u]);
                assert(num15(l_qty(sv)[xs[u]]) && num15(l_price(sv)[xs[u]]));
            }
            lemma_seq_sum_bound(xs, fprice(sv));
            assert forall|u: int| 0 <= u < xs.len() implies -999_999_999_999_999 <= #[trigger] (fcnt(sv))(xs[u]) <= 999_999_999_999_999 by {}
            lemma_seq_sum_bound(xs, fcnt(sv));
            lemma_sum_bound_small();
            let m = xs.len() + 1;
            assert(m <= n_l(sv));
            assert(n_l(sv) <= usize::MAX as int);
            assert(usize::MAX as int <= 0xffff_ffff_ffff_ffff);
            assert(999_999_999_999_999 * m < sum_bound()) by (nonlinear_arith)
                requires 0 <= m <= 0xffff_ffff_ffff_ffff;
            assert(num15(l_qty(sv)[l]) && num15(l_price(sv)[l]));
            lemma_seq_sum_push(xs, l, fprice(sv));
            lemma_seq_sum_push(xs, l, fcnt(sv));
            assert(rows.take(j + 1) =~= xs.push(l));
        }
        if exact_below(h, j, thr, av, Ghost(rows), Ghost(keys), Ghost(sv)) {
            tot = tot + h.recs[j].2 as i128;
            cnt = cnt + 1;
        }
        j = j + 1;
    }
    proof { assert(rows.take(used as int) =~= rows); }
    (tot, cnt)
}

/// The totals of every hit row (the listed rows), with the exact test, on the calling thread.
pub fn final_exact(outs: &Vec<Hits>, nt: usize, thr: &Thr, av: &Avgs, Ghost(keys): Ghost<Seq<i64>>, Ghost(sv): Ghost<StoresView>)
    -> (r: (i128, i128))
    requires
        1 <= nt, scan_ok(outs@, nt as int, keys, sv),
        thr_ok(thr, keys, sv), avgs_ok(av, thr, keys, sv), domains_ok(sv), sizes_ok(sv),
    ensures
        r.0 as int == seq_sum(range_filter(0, n_l(sv) as int, inrow(keys, sv)), fprice(sv)),
        r.1 as int == seq_sum(range_filter(0, n_l(sv) as int, inrow(keys, sv)), fcnt(sv)),
{
    let ghost nl = n_l(sv) as int;
    let ghost p = inrow(keys, sv);
    // the totals of each range
    let mut res: Vec<(i128, i128)> = Vec::new();
    let mut t: usize = 0;
    while t < nt
        invariant
            1 <= nt, t <= nt, scan_ok(outs@, nt as int, keys, sv), p == inrow(keys, sv), nl == n_l(sv),
            thr_ok(thr, keys, sv), avgs_ok(av, thr, keys, sv), domains_ok(sv), sizes_ok(sv),
            res@.len() == t,
            forall|u: int| 0 <= u < t ==> (#[trigger] res@[u]).0 as int == seq_sum(range_rows(sv, keys, nt as int, u), fprice(sv))
                && res@[u].1 as int == seq_sum(range_rows(sv, keys, nt as int, u), fcnt(sv)),
        decreases nt - t,
    {
        proof {
            lemma_split(nl, nt as int, t as int);
            lemma_range_filter_members(split_at(nl, nt as int, t as int), split_at(nl, nt as int, t + 1), p);
        }
        let r0 = exact_hits(&outs[t], thr, av, Ghost(range_rows(sv, keys, nt as int, t as int)), Ghost(keys), Ghost(sv));
        res.push(r0);
        t = t + 1;
    }
    sum_ranges(&res, nt, Ghost(keys), Ghost(sv))
}

// ------------------------------------------------------------------------------------------------ the totals

/// The totals over the listed rows are the result totals `body::tot`.
pub proof fn lemma_final_tot(keys: Seq<i64>, srows: Seq<int>, sv: StoresView, ps: Seq<Literal>)
    requires keys_ok(keys, srows, sv, ps), keys_unique(p_key(sv)),
    ensures
        seq_sum(range_filter(0, n_l(sv) as int, inrow(keys, sv)), fprice(sv)) == range_sum(0, n_l(sv) as int, f_price(sv, ps)),
        seq_sum(range_filter(0, n_l(sv) as int, inrow(keys, sv)), fcnt(sv)) == range_sum(0, n_l(sv) as int, f_cnt(sv, ps)),
{
    let nl = n_l(sv) as int;
    let p = inrow(keys, sv);
    lemma_sum_range_filter(0, nl, p, fprice(sv));
    lemma_sum_range_filter(0, nl, p, fcnt(sv));
    assert forall|l: int| 0 <= l < nl implies #[trigger] guard(p, fprice(sv))(l) == f_price(sv, ps)(l) by {
        lemma_inrow_insel(keys, srows, sv, ps, l);
    }
    assert forall|l: int| 0 <= l < nl implies #[trigger] guard(p, fcnt(sv))(l) == f_cnt(sv, ps)(l) by {
        lemma_inrow_insel(keys, srows, sv, ps, l);
    }
    lemma_range_sum_ext(0, nl, guard(p, fprice(sv)), f_price(sv, ps));
    lemma_range_sum_ext(0, nl, guard(p, fcnt(sv)), f_cnt(sv, ps));
}

} // verus!
