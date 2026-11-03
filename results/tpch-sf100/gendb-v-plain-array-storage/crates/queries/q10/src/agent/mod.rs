//! TPC-H Q10 (returned item reporting) over the flat storages: the 20 customers with the most revenue
//! `SUM(l_extendedprice * (1 - l_discount))` from returned (`l_returnflag = 'R'`) lineitems of their orders placed
//! in the three months from `$1`, with their name, account balance, nation, address, phone and comment.
//!
//! Plan of a call (`query`):
//! 1. the window `[$1, $1 + 3 months)` on stored days (`window`; a failing `$1 + 3 months` is that SQL error on a
//!    non-empty FROM);
//! 2. the fast path (`plan::fast_path`): scan tasks (`scan`, one per worker) walk their orders in batches: the rows
//!    in the window (64-row masks), their keys and customer rows, the run of each key in `l_orderkey` (`runs`, with
//!    the adjacent pairs checked so the runs are complete), the `R` rows' revenue per order, appended to the bucket
//!    of the order's customer row; then customer tasks (`cagg`) sum each bucket's entries per customer in a small
//!    accumulator and keep their top 20 customers whose nation exists; then the top 20 of those lists;
//! 3. when a fast-path check fails (keys out of order, values the fast accumulators do not take, non-positional
//!    customer keys), the general path (`general`); a group beyond the SUM capacity answers `Capacity`;
//! 4. the output rows of the 20 customers, by revenue descending (`output`).
//!
//! The proof: `denot` gives the SQL meaning of the statement in the accumulator normal form of `link::query`,
//! `groups` shows the groups are the customers with their totals (`normal`), `scan`/`cagg`/`plan` relate the tasks'
//! results to those totals, `common::topn` the top lists, and `answer` turns a top-20 list of the groups into the
//! fixed claim; `capacity` covers `Capacity`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::datetime::*;
use crate::spec::order::ordered_ok;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::{answer_meets, stores_ready, bound_db, outcome_ok, Answer};
use crate::gendb_params::Params;
use crate::query::{param_domain, query_spec_at};
use crate::exec::value::EVal;
use crate::exec::datetime::{date_from_civil_exec, date_to_ts_exec, ts_add_interval_exec, floor_divmod};
use crate::link::query::view_rows;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_orders::interface as oi;
use crate::stores::flat_customer::interface as ci;
use crate::stores::flat_nation::interface as ni;

pub mod common;
pub mod cols;
pub mod normal;
pub mod denot;
pub mod groups;
pub mod answer;
pub mod xcols;
pub mod enc;
pub mod capacity;
pub mod general;
pub mod output;
pub mod plan;
pub mod runs;
pub mod scan;
pub mod cagg;

use cols::*;
use normal::*;
use denot::*;
use answer::*;
use xcols::*;
use cagg::{TOPN, cval};
use general::{GenOut, general};
use plan::{fast_path, fast_ok};
use output::out_row;
use common::topn::*;

verus! {

// ------------------------------------------------------------------------------------------------ the parameter

/// The parameter literal is a date with its day number in range.
proof fn lemma_param(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures ({
        let p = ps[0];
        &&& p is Date
        &&& 1 <= p->Date_m <= 12
        &&& 1 <= p->Date_d <= 31
        &&& -730119 <= date_from_civil(p->Date_y, p->Date_m, p->Date_d) <= 2921939
        &&& pd_of(ps) == date_from_civil(p->Date_y, p->Date_m, p->Date_d)
    }),
{
    assert(date_from_civil(1, 1, 1) == -730119) by (compute);
    assert(date_from_civil(9999, 12, 31) == 2921939) by (compute);
    let p = ps[0];
    assert(days_in_month(p->Date_y, p->Date_m) <= 31);
}

/// `$1` as days since 2000-01-01.
fn param_day(params: &Params) -> (pd: i64)
    requires param_domain(params@),
    ensures pd as int == pd_of(params@), -730119 <= pd <= 2921939,
{
    proof {
        lemma_param(params@);
        assert(params@[0] == Literal::Date { y: params.p0.y as int, m: params.p0.m as int, d: params.p0.d as int });
    }
    date_from_civil_exec(params.p0.y as i64, params.p0.m as i64, params.p0.d as i64)
}

/// `$1 + interval '3 month'` (timestamp microseconds) from the parameter day `pd` (days since 2000-01-01).
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
        Ok(t0) => ts_add_interval_exec(t0, 3, 0, 0),
        Err(e) => Err(e),
    }
}

/// A computed upper bound is a valid timestamp.
proof fn lemma_hi_valid(pd: int, t1: int)
    requires hi_res(pd) == Ok::<int, SqlError>(t1),
    ensures ts_valid(t1),
{
}

/// The window on stored days: from `pd` to the first day whose midnight is not below `t1`.
fn window(pd: i64, t1: i64) -> (w: (i64, i64))
    requires -730119 <= pd <= 2921939, ts_valid(t1 as int),
    ensures win_of(w.0 as int, w.1 as int, pd as int, t1 as int),
{
    let (hq, _rem) = floor_divmod(t1 + 86_399_999_999, 86_400_000_000);
    assert(hq * 86_400_000_000 >= t1 && (hq - 1) * 86_400_000_000 < t1);
    (pd + 10957, hq + 10957)
}

// ------------------------------------------------------------------------------------------------ outcomes

/// A top list of all groups in `common::topn`'s terms is a sorted top-20 of the groups in `answer`'s.
proof fn lemma_top_ok(sv: StoresView, dlo: int, dhi: int, sel: Seq<int>)
    requires top_of(sel, all_groups(sv, dlo, dhi), cval(sv, dlo, dhi), TOPN as int),
    ensures top_ok(sv, dlo, dhi, sel),
{
    lemma_glist(sv, dlo, dhi, n_c(sv));
    assert forall|t: int| 0 <= t < sel.len() implies is_group(sv, dlo, dhi, #[trigger] sel[t]) by {
        assert(all_groups(sv, dlo, dhi).contains(sel[t]));
    }
    assert forall|i: int, j: int| 0 <= i < j < sel.len() implies ctot(sv, dlo, dhi, #[trigger] sel[i]) >= ctot(sv, dlo, dhi, #[trigger] sel[j]) by {
        assert(cval(sv, dlo, dhi)(sel[i]) >= cval(sv, dlo, dhi)(sel[j]));
    }
    if sel.len() > 0 {
        assert forall|a: int| #[trigger] is_group(sv, dlo, dhi, a) && !sel.contains(a)
            implies ctot(sv, dlo, dhi, sel.last()) >= ctot(sv, dlo, dhi, a) by {
            assert(all_groups(sv, dlo, dhi).contains(a));
        }
    }
}

/// An empty window has no group.
proof fn lemma_no_groups(sv: StoresView, dlo: int, dhi: int)
    requires dhi <= dlo,
    ensures all_groups(sv, dlo, dhi).len() == 0, groups_capped(sv, dlo, dhi), top_ok(sv, dlo, dhi, Seq::empty()),
{
    lemma_glist(sv, dlo, dhi, n_c(sv));
    assert forall|a: int| !#[trigger] is_group(sv, dlo, dhi, a) by {
        if 0 <= a < n_c(sv) {
            assert forall|j: int| 0 <= j < n_o(sv) implies !#[trigger] cmatch(sv, dlo, dhi, a, j) by {}
            lemma_c_none(sv, dlo, dhi, a, 0, n_o(sv));
        }
    }
    let g = all_groups(sv, dlo, dhi);
    if g.len() > 0 {
        assert(g.contains(g[0]));
    }
}

/// The rows of the selected groups: an allowed output on every bound database.
proof fn lemma_rows_out(sv: StoresView, ps: Seq<Literal>, t1: int, dlo: int, dhi: int, sel: Seq<int>, out: Seq<Row>)
    requires
        param_domain(ps), hi_res(pd_of(ps)) == Ok::<int, SqlError>(t1), win_of(dlo, dhi, pd_of(ps), t1),
        groups_capped(sv, dlo, dhi), top_ok(sv, dlo, dhi, sel),
        out == sel.map_values(|a: int| grow(sv, dlo, dhi, a)),
    ensures forall|db: Database| #[trigger] bound_db(sv, db) ==> ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)) by {
        lemma_answer(sv, db, ps, t1, dlo, dhi, sel);
    }
}

/// The answer meets the claim: the rows of a top list of the groups.
proof fn lemma_meets_rows(sv: StoresView, ps: Seq<Literal>, t1: int, dlo: int, dhi: int, top: Top, rows: Vec<Vec<EVal>>)
    requires
        param_domain(ps), hi_res(pd_of(ps)) == Ok::<int, SqlError>(t1), win_of(dlo, dhi, pd_of(ps), t1),
        fast_ok(top, sv, dlo, dhi),
        view_rows(rows@) == tsel(top).map_values(|a: int| grow(sv, dlo, dhi, a)),
    ensures answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Rows(rows))),
{
    lemma_top_ok(sv, dlo, dhi, tsel(top));
    lemma_rows_out(sv, ps, t1, dlo, dhi, tsel(top), view_rows(rows@));
}

/// The answer meets the claim: no rows for an empty window.
proof fn lemma_meets_no_window(sv: StoresView, ps: Seq<Literal>, t1: int, dlo: int, dhi: int, rows: Vec<Vec<EVal>>)
    requires
        param_domain(ps), hi_res(pd_of(ps)) == Ok::<int, SqlError>(t1), win_of(dlo, dhi, pd_of(ps), t1),
        dhi <= dlo, rows@.len() == 0,
    ensures answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Rows(rows))),
{
    lemma_no_groups(sv, dlo, dhi);
    assert(view_rows(rows@) =~= Seq::<int>::empty().map_values(|a: int| grow(sv, dlo, dhi, a)));
    lemma_rows_out(sv, ps, t1, dlo, dhi, Seq::empty(), view_rows(rows@));
}

/// The answer meets the claim: the window's bound fails on a non-empty FROM.
proof fn lemma_meets_err(sv: StoresView, ps: Seq<Literal>, e: SqlError)
    requires
        stores_ready(sv), param_domain(ps), hi_res(pd_of(ps)) == Err::<int, SqlError>(e),
        n_c(sv) > 0, n_o(sv) > 0, n_l(sv) > 0, n_n(sv) > 0,
    ensures answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::SqlError(e))),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::SqlError(e))) by {
        lemma_body_hi_err(sv, db, ps, e);
    }
}

/// The answer meets the claim: no rows when FROM is empty.
proof fn lemma_meets_empty_from(sv: StoresView, ps: Seq<Literal>, rows: Vec<Vec<EVal>>)
    requires
        param_domain(ps), rows@.len() == 0,
        n_c(sv) == 0 || n_o(sv) == 0 || n_l(sv) == 0 || n_n(sv) == 0,
    ensures answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Rows(rows))),
{
    assert(view_rows(rows@) =~= Seq::<Row>::empty());
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
        lemma_body_empty(sv, db, ps);
        lemma_denote_empty(sv, db, ps);
        let p = Seq::<Row>::empty();
        assert(crate::spec::order::sorted_by(query_spec_at(ps).keys, p));
        assert(crate::spec::order::slice_rows(p, 0, Some(20nat)) =~= p);
        lemma_query_shape(ps);
    }
}

/// The answer meets the claim: a group beyond the SUM capacity.
proof fn lemma_meets_capacity(sv: StoresView, ps: Seq<Literal>, t1: int, dlo: int, dhi: int, a: int)
    requires
        param_domain(ps), hi_res(pd_of(ps)) == Ok::<int, SqlError>(t1), win_of(dlo, dhi, pd_of(ps), t1),
        0 <= a < n_c(sv), natok(sv, a), ctabs(sv, dlo, dhi, a) > crate::link::expr::i128_max(),
    ensures answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Capacity)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity)) by {
        crate::agent::capacity::lemma_capacity(sv, db, ps, t1, dlo, dhi, a);
    }
}

/// The table sizes as the parts give them.
fn table_sizes(stores: &Stores, Ghost(db): Ghost<Database>) -> (r: (usize, usize, usize, usize))
    requires bound_db(stores@, db),
    ensures r.0 == n_l(stores@), r.1 == n_o(stores@), r.2 == n_c(stores@), r.3 == n_n(stores@),
{
    proof { lemma_parts_shape(stores@, db); }
    let nl = stores.flat_lineitem.part_len(li::L_ORDERKEY);
    let no = stores.flat_orders.part_len(oi::O_ORDERKEY);
    let nc = stores.flat_customer.part_len(ci::C_CUSTKEY);
    let nn = stores.flat_nation.part_len(ni::N_NATIONKEY);
    (nl, no, nc, nn)
}

/// The output rows of the selected groups.
fn out_rows(stores: &mut Stores, c: &Cols, top: &Top, Ghost(db): Ghost<Database>, Ghost(dlo): Ghost<int>, Ghost(dhi): Ghost<int>)
    -> (rows: Vec<Vec<EVal>>)
    requires bound_db(old(stores)@, db), cols_ok(*c, old(stores)@), fast_ok(*top, old(stores)@, dlo, dhi),
    ensures
        final(stores)@ == old(stores)@,
        view_rows(rows@) == tsel(*top).map_values(|a: int| grow(old(stores)@, dlo, dhi, a)),
{
    let ghost sv = stores@;
    let ghost sel = tsel(*top);
    proof {
        lemma_glist(sv, dlo, dhi, n_c(sv));
    }
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let mut k: usize = 0;
    while k < top.k
        invariant
            k <= top.k, top.k <= top.cap, top.rows@.len() == top.cap, top.vals@.len() == top.cap,
            fast_ok(*top, sv, dlo, dhi), sel == tsel(*top),
            bound_db(stores@, db), stores@ == sv, cols_ok(*c, sv),
            forall|x: int| #[trigger] all_groups(sv, dlo, dhi).contains(x) <==> 0 <= x < n_c(sv) && is_group(sv, dlo, dhi, x),
            rows@.len() == k,
            forall|j: int| 0 <= j < k ==> crate::exec::value::view_row(#[trigger] rows@[j]@) == grow(sv, dlo, dhi, sel[j]),
        decreases top.k - k,
    {
        let a = top.rows[k];
        proof {
            assert(sel[k as int] == a as int);
            assert(all_groups(sv, dlo, dhi).contains(sel[k as int]));
            assert(top.vals@[k as int] as int == ctot(sv, dlo, dhi, a as int));
        }
        let row = out_row(stores, c, a, top.vals[k], Ghost(db));
        rows.push(row);
        k = k + 1;
    }
    proof {
        let out = sel.map_values(|a: int| grow(sv, dlo, dhi, a));
        assert(view_rows(rows@) =~= out) by {
            assert forall|j: int| 0 <= j < out.len() implies view_rows(rows@)[j] == out[j] by {
                assert(view_rows(rows@)[j] == crate::exec::value::view_row(rows@[j]@));
            }
        }
    }
    rows
}

/// The top groups: the fast path, or the general path when a fast-path check fails; `Err(a)` names a group beyond
/// the SUM capacity.
fn top_groups(c: &Cols, workers: usize, dispatch: &mut Dispatch, Ghost(sv): Ghost<StoresView>)
    -> (r: Result<Result<Top, usize>, crate::gendb_entry::runtime::WorkerFailure>)
    requires cols_ok(*c, sv), 1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(Ok(t)) ==> fast_ok(t, sv, c.dlo as int, c.dhi as int),
        r matches Ok(Err(a)) ==> 0 <= a < n_c(sv) && natok(sv, a as int)
            && ctabs(sv, c.dlo as int, c.dhi as int, a as int) > crate::link::expr::i128_max(),
{
    if c.nc >= 1 && c.nc < 0x8000_0000 && c.no >= 1 {
        match fast_path(c, workers, dispatch, Ghost(sv)) {
            Ok(Some(t)) => return Ok(Ok(t)),
            Ok(None) => {},
            Err(e) => return Err(e),
        }
    }
    match general(c, top_new(TOPN, Ghost(cval(sv, c.dlo as int, c.dhi as int))), Ghost(sv)) {
        GenOut::Top(t) => {
            assert(fast_ok(t, sv, c.dlo as int, c.dhi as int));
            Ok(Ok(t))
        },
        GenOut::Over(a) => Ok(Err(a)),
    }
}

// ------------------------------------------------------------------------------------------------ the entry

pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures
        answer_meets(old(stores)@, params@, r),
{
    hide(cols_ok);
    hide(fast_ok);
    hide(answer_meets);
    hide(query_spec_at);
    hide(hi_res);
    let ghost sv = stores@;
    let ghost ps = params@;
    let ghost db0 = choose|db: Database| bound_db(sv, db);
    let pd = param_day(params);
    // 1. the window
    let t1 = match hi_bound(pd) {
        Ok(t) => t,
        Err(e) => {
            let (nl, no, nc, nn) = table_sizes(stores, Ghost(db0));
            if nl > 0 && no > 0 && nc > 0 && nn > 0 {
                proof { lemma_meets_err(sv, ps, e); }
                return Ok(Answer::SqlError(e));
            }
            let rows: Vec<Vec<EVal>> = Vec::new();
            proof { lemma_meets_empty_from(sv, ps, rows); }
            return Ok(Answer::Rows(rows));
        },
    };
    proof { lemma_hi_valid(pd as int, t1 as int); }
    let (dlo, dhi) = window(pd, t1);
    if dhi <= dlo {
        let rows: Vec<Vec<EVal>> = Vec::new();
        proof { lemma_meets_no_window(sv, ps, t1 as int, dlo as int, dhi as int, rows); }
        return Ok(Answer::Rows(rows));
    }
    // 2./3. the top groups
    let c = read_cols(stores, dlo, dhi, Ghost(db0));
    let top: Top = match top_groups(&c, workers, dispatch, Ghost(sv)) {
        Ok(Ok(t)) => t,
        Ok(Err(a)) => {
            proof { lemma_meets_capacity(sv, ps, t1 as int, dlo as int, dhi as int, a as int); }
            return Ok(Answer::Capacity);
        },
        Err(e) => {
            proof { reveal(answer_meets); }
            return Err(QueryError::WorkerFailed(e));
        },
    };
    // 4. the output rows
    let rows = out_rows(stores, &c, &top, Ghost(db0), Ghost(dlo as int), Ghost(dhi as int));
    proof { lemma_meets_rows(sv, ps, t1 as int, dlo as int, dhi as int, top, rows); }
    Ok(Answer::Rows(rows))
}

} // verus!
