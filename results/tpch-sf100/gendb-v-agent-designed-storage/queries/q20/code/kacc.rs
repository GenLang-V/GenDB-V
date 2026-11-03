//! The lineitem subquery's SUM and COUNT for one part key and up to four supplier keys at once (`li_acc`): over the
//! index entry of the key (positions in date order; only rows of the date window are read), or, without the index,
//! over every stored row. One pass serves the four suppliers: each row adds its quantity to the slots of equal
//! supplier key (selects, no branches on the supplier).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::gendb_entry::layout::PartView;
use crate::link::join::*;
use crate::link::expr::ival;
use crate::stores::li_pkdate::interface as li;
use super::typed::p15;
use super::bind_pl::*;
use super::kctx::*;

verus! {

/// SUM coefficients and COUNTs of four supplier slots.
pub struct Acc {
    pub a0: i128,
    pub a1: i128,
    pub a2: i128,
    pub a3: i128,
    pub c0: u64,
    pub c1: u64,
    pub c2: u64,
    pub c3: u64,
    /// A value derived from early touches of the index rows (kept so the loads are not removed).
    pub junk: u64,
}

/// One slot holds the sums of `rows` for part `k`, supplier `s`.
pub open spec fn slot_ok(a: i128, c: u64, rows: Seq<Row>, k: int, s: int, d0: int, d1: int) -> bool {
    &&& a == sum_of(rows, lq4(k, s, d0, d1))
    &&& c == sum_of(rows, lc4(k, s, d0, d1))
}

/// The four slots, with their bounds.
pub open spec fn acc_ok(acc: Acc, rows: Seq<Row>, k: int, s0: int, s1: int, s2: int, s3: int, d0: int, d1: int) -> bool {
    let n = rows.len() as int;
    &&& slot_ok(acc.a0, acc.c0, rows, k, s0, d0, d1)
    &&& slot_ok(acc.a1, acc.c1, rows, k, s1, d0, d1)
    &&& slot_ok(acc.a2, acc.c2, rows, k, s2, d0, d1)
    &&& slot_ok(acc.a3, acc.c3, rows, k, s3, d0, d1)
    &&& -n * p15() <= acc.a0 <= n * p15() && -n * p15() <= acc.a1 <= n * p15()
    &&& -n * p15() <= acc.a2 <= n * p15() && -n * p15() <= acc.a3 <= n * p15()
    &&& acc.c0 <= n && acc.c1 <= n && acc.c2 <= n && acc.c3 <= n
}

/// The four slots hold the subquery's sums over all of lineitem.
pub open spec fn acc_final(acc: Acc, lp: Seq<PartView>, k: int, s0: int, s1: int, s2: int, s3: int, d0: int, d1: int) -> bool {
    &&& acc.a0 == sl_lsum(lp, k, s0, d0, d1) && acc.c0 == sl_lcnt(lp, k, s0, d0, d1)
    &&& acc.a1 == sl_lsum(lp, k, s1, d0, d1) && acc.c1 == sl_lcnt(lp, k, s1, d0, d1)
    &&& acc.a2 == sl_lsum(lp, k, s2, d0, d1) && acc.c2 == sl_lcnt(lp, k, s2, d0, d1)
    &&& acc.a3 == sl_lsum(lp, k, s3, d0, d1) && acc.c3 == sl_lcnt(lp, k, s3, d0, d1)
}

/// One more row of a range.
pub proof fn lemma_sum_step(x: Seq<Row>, a: int, p: int, f: spec_fn(Row) -> int)
    requires 0 <= a <= p < x.len(),
    ensures sum_of(x.subrange(a, p + 1), f) == sum_of(x.subrange(a, p), f) + f(x[p]),
{
    assert(x.subrange(a, p + 1).drop_last() =~= x.subrange(a, p));
    assert(x.subrange(a, p + 1).last() == x[p]);
}

/// Rows outside `[a, b)` add nothing.
pub proof fn lemma_sum_inside(x: Seq<Row>, a: int, b: int, f: spec_fn(Row) -> int)
    requires
        0 <= a <= b <= x.len(),
        forall|p: int| 0 <= p < x.len() && !(a <= p < b) ==> f(#[trigger] x[p]) == 0,
    ensures sum_of(x, f) == sum_of(x.subrange(a, b), f),
{
    let (l, m, r) = (x.subrange(0, a), x.subrange(a, b), x.subrange(b, x.len() as int));
    assert(x =~= l + m + r);
    lemma_sum_of_append(l + m, r, f);
    lemma_sum_of_append(l, m, f);
    assert forall|i: int| 0 <= i < l.len() implies f(#[trigger] l[i]) == 0 by {
        assert(l[i] == x[i]);
    }
    assert forall|i: int| 0 <= i < r.len() implies f(#[trigger] r[i]) == 0 by {
        assert(r[i] == x[b + i]);
    }
    lemma_sum_of_zero(l, f);
    lemma_sum_of_zero(r, f);
}

/// The empty range.
proof fn lemma_acc_empty(x: Seq<Row>, a: int, k: int, s0: int, s1: int, s2: int, s3: int, d0: int, d1: int)
    requires 0 <= a <= x.len(),
    ensures acc_ok(Acc { a0: 0, a1: 0, a2: 0, a3: 0, c0: 0, c1: 0, c2: 0, c3: 0, junk: 0 }, x.subrange(a, a), k, s0, s1, s2, s3, d0, d1),
{
    assert(x.subrange(a, a) =~= Seq::<Row>::empty());
}

/// One slot after one more row: the row adds `q` and 1 when it is selected.
proof fn lemma_slot_step(x: Seq<Row>, a: int, p: int, k: int, s: int, d0: int, d1: int, sel: bool, q: int)
    requires
        0 <= a <= p < x.len(),
        wsel(k, s, d0, d1, x[p]) == sel,
        ival(x[p][2]) == q,
    ensures
        sum_of(x.subrange(a, p + 1), lq4(k, s, d0, d1)) == sum_of(x.subrange(a, p), lq4(k, s, d0, d1)) + (if sel { q } else { 0 }),
        sum_of(x.subrange(a, p + 1), lc4(k, s, d0, d1)) == sum_of(x.subrange(a, p), lc4(k, s, d0, d1)) + (if sel { 1int } else { 0 }),
{
    lemma_sum_step(x, a, p, lq4(k, s, d0, d1));
    lemma_sum_step(x, a, p, lc4(k, s, d0, d1));
}

/// Index position `p`'s date code lies in the window.
pub open spec fn in_win(ctx: &Ctx, p: int) -> bool {
    ctx.dlo <= li::idx_dates(ctx.lp())[p] && li::idx_dates(ctx.lp())[p] < ctx.dhi
}

/// The positions of entry `e` whose date lies in the window: one range (dates are sorted within an entry).
fn window(ctx: &Ctx, e: usize, e0: usize, e1: usize) -> (r: (usize, usize))
    requires
        ctx.wf_li(), ctx.idx,
        e < ctx.nkeys,
        e0 == li::idx_offs(ctx.lp())[e as int], e1 == li::idx_offs(ctx.lp())[e + 1],
        e0 <= e1 <= ctx.nl,
    ensures
        e0 <= r.0 <= r.1 <= e1,
        forall|p: int| e0 <= p < e1 ==> (r.0 <= p < r.1) == #[trigger] in_win(ctx, p),
    no_unwind
{
    let ghost lp = ctx.lp();
    let ghost n = ctx.nl as int;
    let mut c0 = e0;
    while c0 < e1 && (ctx.idates[c0] as i64) < ctx.dlo
        invariant
            ctx.wf_li(), ctx.idx, lp == ctx.lp(),
            e0 <= c0 <= e1 <= ctx.nl,
            forall|p: int| e0 <= p < c0 ==> (li::idx_dates(lp)[p] as int) < ctx.dlo,
        decreases e1 - c0,
    {
        c0 = c0 + 1;
    }
    let mut c1 = c0;
    while c1 < e1 && (ctx.idates[c1] as i64) < ctx.dhi
        invariant
            ctx.wf_li(), ctx.idx, lp == ctx.lp(),
            e0 <= c0 <= c1 <= e1 <= ctx.nl,
            forall|p: int| c0 <= p < c1 ==> (li::idx_dates(lp)[p] as int) < ctx.dhi,
        decreases e1 - c1,
    {
        c1 = c1 + 1;
    }
    proof {
        assert forall|p: int| e0 <= p < e1 implies (c0 <= p < c1) == #[trigger] in_win(ctx, p) by {
            if c0 <= p {
                li::lemma_dates_sorted(lp, n, e as int, c0 as int, p);
            }
            if c1 <= p {
                li::lemma_dates_sorted(lp, n, e as int, c1 as int, p);
            }
        }
    }
    (c0, c1)
}

/// The four slots over positions `[c0, c1)` (all of key `k`, all in the date window).
fn acc_gather(ctx: &Ctx, c0: usize, c1: usize, k: i64, s0: i64, s1: i64, s2: i64, s3: i64) -> (acc: Acc)
    requires
        ctx.wf_li(), ctx.idx,
        c0 <= c1 <= ctx.nl,
        forall|p: int| c0 <= p < c1 ==> #[trigger] li::key_at(ctx.lp(), li::irow(ctx.lp(), p)) == k && in_win(ctx, p),
    ensures
        acc_ok(acc, prows(ctx.lp()).subrange(c0 as int, c1 as int), k as int, s0 as int, s1 as int, s2 as int, s3 as int,
            ctx.d0 as int, ctx.d1 as int),
    no_unwind
{
    let ghost lp = ctx.lp();
    let ghost x = prows(lp);
    let ghost (d0, d1) = (ctx.d0 as int, ctx.d1 as int);
    let mut acc = Acc { a0: 0, a1: 0, a2: 0, a3: 0, c0: 0, c1: 0, c2: 0, c3: 0, junk: 0 };
    proof {
        lemma_acc_empty(x, c0 as int, k as int, s0 as int, s1 as int, s2 as int, s3 as int, d0, d1);
    }
    let mut p = c0;
    while p < c1
        invariant
            ctx.wf_li(), ctx.idx,
            c0 <= p <= c1 <= ctx.nl,
            lp == ctx.lp(), x == prows(lp), d0 == ctx.d0, d1 == ctx.d1,
            forall|t: int| c0 <= t < c1 ==> #[trigger] li::key_at(lp, li::irow(lp, t)) == k && in_win(ctx, t),
            acc_ok(acc, x.subrange(c0 as int, p as int), k as int, s0 as int, s1 as int, s2 as int, s3 as int, d0, d1),
        decreases c1 - p,
    {
        proof {
            assert(li::date_key_ok(lp, p as int));
            assert(0 <= li::irow(lp, p as int) < ctx.nl);
            assert(li::key_at(lp, li::irow(lp, p as int)) == k && in_win(ctx, p as int));
        }
        let si = ctx.irows[p] as usize;
        let su = ctx.get_lsk(si);
        // the quantity only of a row of one of the four suppliers (the others add nothing)
        let hit = su == s0 || su == s1 || su == s2 || su == s3;
        let q = if hit { ctx.get_lq(si) } else { 0 };
        proof {
            let row = x[p as int];
            assert(row == wrow(lp, si as int));
            assert(row[0] == Val::Int(k as int));
            assert(d0 <= ival(row[3]) && ival(row[3]) < d1);
            assert(row[1] == Val::Int(su as int));
            assert(hit ==> ival(row[2]) == q);
            assert(lrow_vals_ok(lp, si as int));
            lemma_slot_step(x, c0 as int, p as int, k as int, s0 as int, d0, d1, su == s0, ival(row[2]));
            lemma_slot_step(x, c0 as int, p as int, k as int, s1 as int, d0, d1, su == s1, ival(row[2]));
            lemma_slot_step(x, c0 as int, p as int, k as int, s2 as int, d0, d1, su == s2, ival(row[2]));
            lemma_slot_step(x, c0 as int, p as int, k as int, s3 as int, d0, d1, su == s3, ival(row[2]));
        }
        let q = q as i128;
        acc.a0 = acc.a0 + if su == s0 { q } else { 0 };
        acc.a1 = acc.a1 + if su == s1 { q } else { 0 };
        acc.a2 = acc.a2 + if su == s2 { q } else { 0 };
        acc.a3 = acc.a3 + if su == s3 { q } else { 0 };
        acc.c0 = acc.c0 + if su == s0 { 1 } else { 0 };
        acc.c1 = acc.c1 + if su == s1 { 1 } else { 0 };
        acc.c2 = acc.c2 + if su == s2 { 1 } else { 0 };
        acc.c3 = acc.c3 + if su == s3 { 1 } else { 0 };
        p = p + 1;
    }
    acc
}

/// Within an entry, the positions outside the window add nothing.
proof fn lemma_slot_window(ctx: &Ctx, e0: int, e1: int, c0: int, c1: int, k: int, s: int)
    requires
        ctx.wf_li(), ctx.idx,
        0 <= e0 <= c0 <= c1 <= e1 <= ctx.nl,
        forall|p: int| e0 <= p < e1 ==> (c0 <= p < c1) == #[trigger] in_win(ctx, p),
    ensures
        sum_of(prows(ctx.lp()).subrange(e0, e1), lq4(k, s, ctx.d0 as int, ctx.d1 as int))
            == sum_of(prows(ctx.lp()).subrange(c0, c1), lq4(k, s, ctx.d0 as int, ctx.d1 as int)),
        sum_of(prows(ctx.lp()).subrange(e0, e1), lc4(k, s, ctx.d0 as int, ctx.d1 as int))
            == sum_of(prows(ctx.lp()).subrange(c0, c1), lc4(k, s, ctx.d0 as int, ctx.d1 as int)),
{
    let lp = ctx.lp();
    let (d0, d1) = (ctx.d0 as int, ctx.d1 as int);
    let n = ctx.nl as int;
    assert(n == li::n_rows(lp));
    assert(lp_ok(lp) && li::has_idx(lp));
    assert(li::idx_ok(lp, n));
    assert(prows(lp).len() == n);
    let y = prows(lp).subrange(e0, e1);
    assert forall|i: int| 0 <= i < y.len() && !(c0 - e0 <= i < c1 - e0) implies
        lq4(k, s, d0, d1)(#[trigger] y[i]) == 0 && lc4(k, s, d0, d1)(y[i]) == 0 by {
        let p = e0 + i;
        assert(e0 <= p < e1);
        assert((c0 <= p < c1) == in_win(ctx, p));
        assert(!in_win(ctx, p));
        assert(li::date_key_ok(lp, p));
        assert(0 <= li::irow(lp, p) < ctx.nl);
        assert(y[i] == wrow(lp, li::irow(lp, p)));
    }
    lemma_sum_inside(y, c0 - e0, c1 - e0, lq4(k, s, d0, d1));
    lemma_sum_inside(y, c0 - e0, c1 - e0, lc4(k, s, d0, d1));
    assert(y.subrange(c0 - e0, c1 - e0) =~= prows(lp).subrange(c0, c1));
}

/// The four slots over every stored row (no index).
fn acc_scan(ctx: &Ctx, k: i64, s0: i64, s1: i64, s2: i64, s3: i64) -> (acc: Acc)
    requires ctx.wf_li(),
    ensures
        acc_ok(acc, wrows(ctx.lp()).subrange(0, ctx.nl as int), k as int, s0 as int, s1 as int, s2 as int, s3 as int,
            ctx.d0 as int, ctx.d1 as int),
    no_unwind
{
    let ghost lp = ctx.lp();
    let ghost x = wrows(lp);
    let ghost (d0, d1) = (ctx.d0 as int, ctx.d1 as int);
    let mut acc = Acc { a0: 0, a1: 0, a2: 0, a3: 0, c0: 0, c1: 0, c2: 0, c3: 0, junk: 0 };
    proof {
        lemma_acc_empty(x, 0, k as int, s0 as int, s1 as int, s2 as int, s3 as int, d0, d1);
    }
    let mut s: usize = 0;
    while s < ctx.nl
        invariant
            ctx.wf_li(),
            s <= ctx.nl,
            lp == ctx.lp(), x == wrows(lp), d0 == ctx.d0, d1 == ctx.d1,
            acc_ok(acc, x.subrange(0, s as int), k as int, s0 as int, s1 as int, s2 as int, s3 as int, d0, d1),
        decreases ctx.nl - s,
    {
        let ghost row = x[s as int];
        proof {
            assert(row == wrow(lp, s as int));
        }
        let kk = ctx.get_lkey(s);
        let dt = ctx.get_ldt(s);
        let sel = kk == k && dt >= ctx.d0 && dt < ctx.d1;
        if sel {
            let su = ctx.get_lsk(s);
            let q = ctx.get_lq(s);
            proof {
                assert(row[1] == Val::Int(su as int) && ival(row[2]) == q);
                lemma_slot_step(x, 0, s as int, k as int, s0 as int, d0, d1, su == s0, q as int);
                lemma_slot_step(x, 0, s as int, k as int, s1 as int, d0, d1, su == s1, q as int);
                lemma_slot_step(x, 0, s as int, k as int, s2 as int, d0, d1, su == s2, q as int);
                lemma_slot_step(x, 0, s as int, k as int, s3 as int, d0, d1, su == s3, q as int);
            }
            let q = q as i128;
            acc.a0 = acc.a0 + if su == s0 { q } else { 0 };
            acc.a1 = acc.a1 + if su == s1 { q } else { 0 };
            acc.a2 = acc.a2 + if su == s2 { q } else { 0 };
            acc.a3 = acc.a3 + if su == s3 { q } else { 0 };
            acc.c0 = acc.c0 + if su == s0 { 1 } else { 0 };
            acc.c1 = acc.c1 + if su == s1 { 1 } else { 0 };
            acc.c2 = acc.c2 + if su == s2 { 1 } else { 0 };
            acc.c3 = acc.c3 + if su == s3 { 1 } else { 0 };
        } else {
            proof {
                lemma_slot_step(x, 0, s as int, k as int, s0 as int, d0, d1, false, ival(row[2]));
                lemma_slot_step(x, 0, s as int, k as int, s1 as int, d0, d1, false, ival(row[2]));
                lemma_slot_step(x, 0, s as int, k as int, s2 as int, d0, d1, false, ival(row[2]));
                lemma_slot_step(x, 0, s as int, k as int, s3 as int, d0, d1, false, ival(row[2]));
            }
        }
        s = s + 1;
    }
    acc
}

/// The sums of one slot over all positions are those of the entry's positions.
proof fn lemma_slot_entry(lp: Seq<PartView>, e: int, k: int, s: int, d0: int, d1: int)
    requires lp_ok(lp), li::has_idx(lp), 0 <= e < li::idx_nkeys(lp), k == li::idx_kmin(lp) + e,
    ensures
        li::idx_offs(lp)[e] <= li::idx_offs(lp)[e + 1] <= li::n_rows(lp),
        sl_lsum(lp, k, s, d0, d1) == sum_of(prows(lp).subrange(li::idx_offs(lp)[e] as int, li::idx_offs(lp)[e + 1] as int), lq4(k, s, d0, d1)),
        sl_lcnt(lp, k, s, d0, d1) == sum_of(prows(lp).subrange(li::idx_offs(lp)[e] as int, li::idx_offs(lp)[e + 1] as int), lc4(k, s, d0, d1)),
{
    let n = li::n_rows(lp);
    let x = prows(lp);
    li::lemma_offs_mono(lp, n, e, e + 1);
    li::lemma_offs_mono(lp, n, e + 1, li::idx_nkeys(lp));
    let (a, b) = (li::idx_offs(lp)[e] as int, li::idx_offs(lp)[e + 1] as int);
    lemma_pos_sum(lp, lq4(k, s, d0, d1));
    lemma_pos_sum(lp, lc4(k, s, d0, d1));
    assert forall|p: int| 0 <= p < x.len() && !(a <= p < b) implies lq4(k, s, d0, d1)(#[trigger] x[p]) == 0
        && lc4(k, s, d0, d1)(x[p]) == 0 by {
        li::lemma_entry_exact(lp, n, e, p);
        assert(x[p] == wrow(lp, li::irow(lp, p)));
    }
    lemma_sum_inside(x, a, b, lq4(k, s, d0, d1));
    lemma_sum_inside(x, a, b, lc4(k, s, d0, d1));
}

/// A key outside the directory's range has no rows: zero sums.
proof fn lemma_slot_none(lp: Seq<PartView>, k: int, s: int, d0: int, d1: int)
    requires lp_ok(lp), li::has_idx(lp), !(li::idx_kmin(lp) <= k < li::idx_kmin(lp) + li::idx_nkeys(lp)),
    ensures sl_lsum(lp, k, s, d0, d1) == 0, sl_lcnt(lp, k, s, d0, d1) == 0,
{
    let n = li::n_rows(lp);
    let x = prows(lp);
    lemma_pos_sum(lp, lq4(k, s, d0, d1));
    lemma_pos_sum(lp, lc4(k, s, d0, d1));
    assert forall|p: int| 0 <= p < x.len() implies lq4(k, s, d0, d1)(#[trigger] x[p]) == 0 && lc4(k, s, d0, d1)(x[p]) == 0 by {
        li::lemma_outside_none(lp, n, k, p);
        assert(x[p] == wrow(lp, li::irow(lp, p)));
    }
    lemma_sum_of_zero(x, lq4(k, s, d0, d1));
    lemma_sum_of_zero(x, lc4(k, s, d0, d1));
}

/// The subquery's SUM and COUNT for part `k` and the four supplier keys.
pub fn li_acc(ctx: &Ctx, k: i64, s0: i64, s1: i64, s2: i64, s3: i64) -> (acc: Acc)
    requires ctx.wf_li(),
    ensures
        acc_final(acc, ctx.lp(), k as int, s0 as int, s1 as int, s2 as int, s3 as int, ctx.d0 as int, ctx.d1 as int),
        -(ctx.nl as int) * p15() <= acc.a0 <= ctx.nl as int * p15(), -(ctx.nl as int) * p15() <= acc.a1 <= ctx.nl as int * p15(),
        -(ctx.nl as int) * p15() <= acc.a2 <= ctx.nl as int * p15(), -(ctx.nl as int) * p15() <= acc.a3 <= ctx.nl as int * p15(),
    no_unwind
{
    let ghost lp = ctx.lp();
    let ghost (d0, d1) = (ctx.d0 as int, ctx.d1 as int);
    if ctx.idx {
        let e = k as i128 - ctx.kmin as i128;
        if e >= 0 && e < ctx.nkeys as i128 {
            let e = e as usize;
            proof {
                lemma_slot_entry(lp, e as int, k as int, s0 as int, d0, d1);
                lemma_slot_entry(lp, e as int, k as int, s1 as int, d0, d1);
                lemma_slot_entry(lp, e as int, k as int, s2 as int, d0, d1);
                lemma_slot_entry(lp, e as int, k as int, s3 as int, d0, d1);
            }
            let e0 = ctx.offs[e] as usize;
            let e1 = ctx.offs[e + 1] as usize;
            // touch the entry's index rows now: their misses overlap the date scan
            let junk = if e0 < e1 && e1 <= ctx.nl { (ctx.irows[e0] as u64) ^ (ctx.irows[e1 - 1] as u64) } else { 0 };
            let (c0, c1) = window(ctx, e, e0, e1);
            proof {
                assert forall|p: int| c0 <= p < c1 implies #[trigger] li::key_at(lp, li::irow(lp, p)) == k && in_win(ctx, p) by {
                    li::lemma_entry_exact(lp, ctx.nl as int, e as int, p);
                }
            }
            let mut acc = acc_gather(ctx, c0, c1, k, s0, s1, s2, s3);
            acc.junk = junk;
            proof {
                lemma_slot_window(ctx, e0 as int, e1 as int, c0 as int, c1 as int, k as int, s0 as int);
                lemma_slot_window(ctx, e0 as int, e1 as int, c0 as int, c1 as int, k as int, s1 as int);
                lemma_slot_window(ctx, e0 as int, e1 as int, c0 as int, c1 as int, k as int, s2 as int);
                lemma_slot_window(ctx, e0 as int, e1 as int, c0 as int, c1 as int, k as int, s3 as int);
                assert((c1 - c0) as int <= ctx.nl as int);
                assert((c1 - c0) as int * p15() <= ctx.nl as int * p15()) by (nonlinear_arith)
                    requires (c1 - c0) as int <= ctx.nl as int, p15() > 0;
            }
            acc
        } else {
            proof {
                lemma_slot_none(lp, k as int, s0 as int, d0, d1);
                lemma_slot_none(lp, k as int, s1 as int, d0, d1);
                lemma_slot_none(lp, k as int, s2 as int, d0, d1);
                lemma_slot_none(lp, k as int, s3 as int, d0, d1);
            }
            Acc { a0: 0, a1: 0, a2: 0, a3: 0, c0: 0, c1: 0, c2: 0, c3: 0, junk: 0 }
        }
    } else {
        let acc = acc_scan(ctx, k, s0, s1, s2, s3);
        proof {
            assert(wrows(lp).subrange(0, ctx.nl as int) =~= wrows(lp));
        }
        acc
    }
}

} // verus!
