//! TPC-H Q12 (shipping modes and order priority) over the flat `lineitem` and `orders` storages: per ship mode `$1`,
//! `$2`, the lineitems received in the year from `$3` (committed before receipt, shipped before commit), counted by
//! whether their order's priority is `1-URGENT`/`2-HIGH` or not.
//!
//! Plan of a call (`query`):
//! 1. read the columns as whole stored parts (`l_receiptdate`, `l_commitdate`, `l_shipdate`, `l_shipmode`,
//!    `l_orderkey`; `o_orderkey`, `o_orderpriority`); compute the receipt window `[$3, $3 + 1 year)` on stored days
//!    (`window`; a failing `$3 + 1 year` is that SQL error when FROM is not empty);
//! 2. the lineitem scan (`plan::count_all`: one task per worker, at most 32, over consecutive row ranges, `scan`): per 64-row word
//!    a vectorized mask of the date conditions, then for the candidates (about 2%) the ship mode, then for the rows
//!    of `$1`/`$2` (about 0.5%) the order (its dbgen row, checked against `o_orderkey`) and its priority; per mode slot
//!    the row count and the high-priority count;
//! 3. the answer (`answer_rows`): a sum beyond int8 is the SQL error 22003; otherwise one row per non-empty mode,
//!    ordered by mode.
//!
//! The proof: the statement's body is a GROUP BY over the filtered product `orders x lineitem` (`normal`, `body`,
//! with the int4 SUM link of `common::int_groups`); the primary key of `orders` collapses every group's sums over
//! the product to sums over lineitem rows (`sums`), which the scan computes (`scan`, `plan`); `outcome` states the
//! fixed claim for each outcome over every bound database.
use vstd::prelude::*;

pub mod common;
pub mod tables;
pub mod normal;
pub mod body;
pub mod sums;
pub mod scan;
pub mod plan;
pub mod outcome;

use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::ast::Literal;
use crate::spec::order::*;
use crate::spec::datetime::*;
use crate::spec::text::lex_cmp;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db, outcome_ok};
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::query::{param_domain, query_spec_at};
use crate::exec::value::{EVal, view_row};
use crate::exec::datetime::{date_from_civil_exec, date_to_ts_exec, ts_add_interval_exec, floor_divmod};
use crate::exec::text::lex_cmp_exec;
use crate::link::query::*;
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::bridge::order::lemma_lex_cmp_antisym;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_orders::interface as oi;
use crate::agent::common::int_groups::*;
use crate::agent::tables::*;
use crate::agent::normal::*;
use crate::agent::sums::*;
use crate::agent::scan::*;
use crate::agent::plan::*;
use crate::agent::outcome::*;

verus! {

/// A copy of a byte slice.
fn copy_bytes(p: &[u8]) -> (v: Vec<u8>)
    ensures v@ == p@,
{
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < p.len()
        invariant i <= p@.len(), v@ == p@.subrange(0, i as int),
        decreases p@.len() - i,
    {
        v.push(p[i]);
        i = i + 1;
        proof { assert(v@ =~= p@.subrange(0, i as int)); }
    }
    proof { assert(v@ =~= p@); }
    v
}

/// `$3 + interval '1 year'` (timestamp microseconds) from the parameter day `pd` (days since 2000-01-01).
fn hi_bound(pd: i64) -> (r: Result<i64, SqlError>)
    requires -730119 <= pd <= 2921939,
    ensures
        match (r, hi_res(pd as int)) {
            (Ok(a), Ok(b)) => a as int == b,
            (Err(e), Err(f)) => e == f,
            _ => false,
        },
{
    match date_to_ts_exec(pd as i32) {
        Ok(t0) => ts_add_interval_exec(t0, 12, 0, 0),
        Err(e) => Err(e),
    }
}

/// The receipt window on stored days: from `pd` to the first day whose midnight is not below `t1`.
fn window(pd: i64, t1: i64) -> (w: (i32, i32))
    requires -730119 <= pd <= 2921939, ts_valid(t1 as int),
    ensures win_of(w.0 as int, w.1 as int, pd as int, t1 as int),
{
    let (hq, _rem) = floor_divmod(t1 + 86_399_999_999, 86_400_000_000);
    assert(hq * 86_400_000_000 >= t1 && (hq - 1) * 86_400_000_000 < t1);
    assert(-2_500_000 <= hq <= 107_000_000) by (nonlinear_arith)
        requires hq * 86_400_000_000 >= t1, (hq - 1) * 86_400_000_000 < t1,
            -211813488000000000 <= t1 < 9223371331200000000;
    ((pd + 10957) as i32, (hq + 10957) as i32)
}

/// Output row `[m, h, n - h]` (the group of ship mode `m` with `n` rows, `h` of them high).
fn out_row(m: &[u8], n: u64, h: u64) -> (row: Vec<EVal>)
    requires h <= n, h <= i64::MAX, n - h <= i64::MAX,
    ensures view_row(row@) == seq![Val::Text(m@), Val::Int(h as int), Val::Int(n - h)],
{
    let mut row: Vec<EVal> = Vec::new();
    row.push(EVal::Text(copy_bytes(m)));
    row.push(EVal::Int(h as i64));
    row.push(EVal::Int((n - h) as i64));
    proof {
        assert(view_row(row@) =~= seq![Val::Text(m@), Val::Int(h as int), Val::Int(n - h)]);
    }
    row
}

/// The group row of mode `m` is the normal form's GROUP BY row.
proof fn lemma_group_row(sv: StoresView, ps: Seq<Literal>, t1: int, m: Seq<u8>, n: int, h: int)
    requires group_is(ps, t1, sv, m, n, h),
    ensures int_full_row(g_call(ps, t1), xs_of(sv), gk(m)) == seq![Val::Text(m), Val::Int(h), Val::Int(n - h)],
{
    let g = g_call(ps, t1);
    assert(int_outs(g, xs_of(sv), gk(m)) =~= seq![Val::Int(h), Val::Int(n - h)]);
    assert(int_full_row(g, xs_of(sv), gk(m)) =~= seq![Val::Text(m), Val::Int(h), Val::Int(n - h)]);
}

/// Two rows whose first columns are the texts `a` before `b` in byte order are sorted by the ORDER BY key.
proof fn lemma_sorted_two(r0: Row, r1: Row, a: Seq<u8>, b: Seq<u8>)
    requires r0.len() > 0, r1.len() > 0, r0[0] == Val::Text(a), r1[0] == Val::Text(b), lex_cmp(a, b) <= 0,
    ensures sorted_by(ast_order_keys(), seq![r0, r1]),
{
    let keys = ast_order_keys();
    assert(keys_cmp(keys.drop_first(), r0, r1) == 0);
    assert(keys_cmp(keys, r0, r1) <= 0);
    let s = seq![r0, r1];
    assert forall|i: int, j: int| 0 <= i < j < s.len() implies keys_cmp(keys, #[trigger] s[i], #[trigger] s[j]) <= 0 by {
        assert(i == 0 && j == 1);
    }
}

/// The answer from the counts of all rows: the error 22003 when a sum leaves int8, otherwise the rows of the
/// non-empty modes in byte order of the mode.
fn answer_rows(q: &Probe, acc: &Counts, ord: i8, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>,
    Ghost(t1): Ghost<int>) -> (r: Answer)
    requires
        call_facts(sv, ps, *q, t1),
        acc_ok(*acc, sv, *q, 0, n_l(sv)),
        ord as int == lex_cmp(q.p1@, q.p2@),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(r)),
{
    let ghost g = g_call(ps, t1);
    let ghost xs = xs_of(sv);
    let ghost (k1, k2) = (gk(q.p1@), gk(q.p2@));
    proof {
        lemma_slot_groups(sv, ps, *q, t1, *acc);
        lemma_lex_cmp_zero(q.p1@, q.p2@);
        lemma_lex_cmp_antisym(q.p1@, q.p2@);
        if !q.two {
            assert(k1 == k2);
        } else {
            assert(k1[0] != k2[0]);
        }
    }
    let max = i64::MAX as u64;
    // a sum beyond int8: the error 22003
    if acc.h0 > max || acc.n0 - acc.h0 > max || (q.two && (acc.h1 > max || acc.n1 - acc.h1 > max)) {
        proof {
            let (k, j) = if acc.h0 > max { (k1, 0int) } else if acc.n0 - acc.h0 > max { (k1, 1int) }
                else if acc.h1 > max { (k2, 0int) } else { (k2, 1int) };
            lemma_sum_err_all(sv, ps, *q, t1, k, j);
        }
        return Answer::SqlError(SqlError::NumericValueOutOfRange);
    }
    proof {
        assert forall|k: Row, j: int| 0 <= j < g.aggs.len() implies int_in_range(IntKind::Int8, #[trigger] gsum(g, xs, k, j)) by {
            if k != k1 && k != k2 {
                lemma_other_groups(sv, ps, *q, t1, k);
            }
        }
        assert forall|k: Row| k != k1 && k != k2 implies #[trigger] gcount(g, xs, k) == 0 by {
            lemma_other_groups(sv, ps, *q, t1, k);
        }
    }
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let ghost mut ks: Seq<Row> = Seq::empty();
    // the modes in output order: `first` before `second` (the second only when the modes differ)
    let first_is_p1 = ord <= 0;
    let (fm, fn_, fh, sm, sn, sh) = if first_is_p1 {
        (q.p1, acc.n0, acc.h0, q.p2, acc.n1, acc.h1)
    } else {
        (q.p2, acc.n1, acc.h1, q.p1, acc.n0, acc.h0)
    };
    proof {
        if first_is_p1 {
            lemma_group_row(sv, ps, t1, q.p1@, acc.n0 as int, acc.h0 as int);
            if q.two { lemma_group_row(sv, ps, t1, q.p2@, acc.n1 as int, acc.h1 as int); }
        } else {
            lemma_group_row(sv, ps, t1, q.p1@, acc.n0 as int, acc.h0 as int);
            lemma_group_row(sv, ps, t1, q.p2@, acc.n1 as int, acc.h1 as int);
        }
    }
    let second_on = q.two;
    if fn_ > 0 {
        let row = out_row(fm, fn_, fh);
        rows.push(row);
        proof { ks = ks.push(gk(fm@)); }
    }
    if second_on && sn > 0 {
        let row = out_row(sm, sn, sh);
        rows.push(row);
        proof { ks = ks.push(gk(sm@)); }
    }
    proof {
        let full = view_rows(rows@);
        assert(full.len() == ks.len());
        assert forall|i: int| 0 <= i < full.len() implies #[trigger] full[i] == int_full_row(g, xs, ks[i]) by {
            assert(full[i] == view_row(rows@[i]@));
        }
        assert(ks.no_duplicates()) by {
            if ks.len() == 2 {
                assert(ks[0] != ks[1]);
            }
        }
        assert forall|k: Row| #[trigger] ks.contains(k) <==> gcount(g, xs, k) > 0 by {
            if ks.contains(k) {
                let i = choose|i: int| 0 <= i < ks.len() && ks[i] == k;
            }
            if gcount(g, xs, k) > 0 {
                if k == k1 {
                    if first_is_p1 { assert(ks[0] == k); } else if q.two { assert(ks[ks.len() - 1] == k); } else { assert(ks[0] == k); }
                } else {
                    assert(k == k2 && q.two);
                    if first_is_p1 { assert(ks[ks.len() - 1] == k); } else { assert(ks[0] == k); }
                }
            }
        }
        if full.len() == 2 {
            lemma_sorted_two(full[0], full[1], fm@, sm@);
            assert(full =~= seq![full[0], full[1]]);
        } else if full.len() == 1 {
            assert(full =~= seq![full[0]]);
            lemma_sorted_single(ast_order_keys(), full[0]);
        } else {
            assert(sorted_by(ast_order_keys(), full));
        }
        lemma_rows_all(sv, ps, *q, t1, ks, full);
    }
    Answer::Rows(rows)
}

pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures
        answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    let ghost ps = params@;
    let ghost db0 = choose|db: Database| #[trigger] bound_db(sv, db);
    proof {
        lemma_parts_shape(sv, db0);
        lemma_okey_unique(sv, db0);
        lemma_params(ps);
    }
    // 1. the columns (whole parts; the scan touches only what it needs)
    let nl = stores.flat_lineitem.part_len(li::L_ORDERKEY);
    let lokey = stores.flat_lineitem.extent_i64(li::L_ORDERKEY, 0, nl);
    let rcpt = stores.flat_lineitem.extent_i32(li::L_RECEIPTDATE, 0, nl);
    let cmt = stores.flat_lineitem.extent_i32(li::L_COMMITDATE, 0, nl);
    let ship = stores.flat_lineitem.extent_i32(li::L_SHIPDATE, 0, nl);
    let nmo = stores.flat_lineitem.part_len(li::L_SHIPMODE_OFFSETS);
    let moff = stores.flat_lineitem.extent_i64(li::L_SHIPMODE_OFFSETS, 0, nmo);
    let nmb = stores.flat_lineitem.part_len(li::L_SHIPMODE_BYTES);
    let mbytes = stores.flat_lineitem.extent_u8(li::L_SHIPMODE_BYTES, 0, nmb);
    let no = stores.flat_orders.part_len(oi::O_ORDERKEY);
    let okey = stores.flat_orders.extent_i64(oi::O_ORDERKEY, 0, no);
    let npo = stores.flat_orders.part_len(oi::O_ORDERPRIORITY_OFFSETS);
    let poff = stores.flat_orders.extent_i64(oi::O_ORDERPRIORITY_OFFSETS, 0, npo);
    let npb = stores.flat_orders.part_len(oi::O_ORDERPRIORITY_BYTES);
    let pbytes = stores.flat_orders.extent_u8(oi::O_ORDERPRIORITY_BYTES, 0, npb);
    let c = Cols { rcpt, cmt, ship, moff, mbytes, lokey, okey, poff, pbytes, nl, no, nmb, npb };
    proof {
        assert(stores@ == sv);
        assert(lokey@ =~= lok(sv) && rcpt@ =~= lrd(sv) && cmt@ =~= lcd(sv) && ship@ =~= lsd(sv));
        assert(moff@ =~= lmode(sv).offsets && mbytes@ =~= lmode(sv).bytes);
        assert(okey@ =~= ok(sv) && poff@ =~= oprio(sv).offsets && pbytes@ =~= oprio(sv).bytes);
        assert(cols_ok(c, sv));
    }
    // the receipt window, or the error of `$3 + 1 year`
    let pd = date_from_civil_exec(params.p2.y as i64, params.p2.m as i64, params.p2.d as i64);
    proof { assert(pd as int == pd_of(ps)); }
    let (dlo, dhi, t1_ghost) = match hi_bound(pd) {
        Ok(t1) => {
            proof { assert(ts_valid(t1 as int)); }
            let (a, b) = window(pd, t1);
            (a, b, Ghost(t1 as int))
        },
        Err(e) => {
            if no > 0 && nl > 0 {
                proof { lemma_hi_err_all(sv, ps, e); }
                return Ok(Answer::SqlError(e));
            }
            // FROM is empty: any window gives the (empty) answer
            let d = (pd + 10957) as i32;
            proof {
                let u = usecs();
                assert((pd - 1) * u < pd * u) by (nonlinear_arith) requires u > 0;
                assert(win_of(d as int, d as int, pd as int, pd * u));
            }
            (d, d, Ghost(pd * usecs()))
        },
    };
    let ghost t1 = t1_ghost@;
    // the parameters
    let p1: &'static [u8] = params.p0;
    let p2: &'static [u8] = params.p1;
    let ord = lex_cmp_exec(&copy_bytes(p1), &copy_bytes(p2));
    proof { lemma_lex_cmp_zero(p1@, p2@); }
    let q = Probe { p1, p1len: p1.len(), p2, p2len: p2.len(), two: ord != 0, dlo, dhi };
    proof {
        assert(call_facts(sv, ps, q, t1));
    }
    // 2. the scan
    let acc = match count_all(c, q, workers, dispatch, Ghost(sv)) {
        Ok(a) => a,
        Err(e) => { return Err(QueryError::WorkerFailed(e)); },
    };
    // 3. the answer
    let ans = answer_rows(&q, &acc, ord, Ghost(sv), Ghost(ps), Ghost(t1));
    Ok(ans)
}

} // verus!
