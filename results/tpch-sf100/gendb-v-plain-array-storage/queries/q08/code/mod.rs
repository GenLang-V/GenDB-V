//! TPC-H Q8 (national market share) over the flat storages: per order year 1995 and 1996, the share of the
//! volume `l_extendedprice * (1 - l_discount)` of the parts of type `$3` sold to customers of region `$2` that
//! suppliers of nation `$1` supplied.
//!
//! Plan of a call (`query`):
//! 1. the part pass (`partpass`, parallel over `workers - workers / 8` tasks from 16 workers on): one bit per part row for `p_type = $3`, whether the matching rows are
//!    positional, and a 256 KiB hashed filter of the matching rows' key groups; the nation directory (`lookup`);
//! 2. the lineitem pass (`stages`, `plan`, parallel over row ranges): per block of rows, the coarse filter, the
//!    exact part bit, the order (row by key, date inside the window), then customer, nations, region and supplier,
//!    accumulating per year the volume, the `$1` volume, their absolute masses and counts (`acc`);
//! 3. the outcome (`decide`): per present year the exact numeric division (PostgreSQL scale rules); rows ordered
//!    by year, or the SQL error / `Capacity` of the canonical evaluation (when the two years fail differently, the
//!    first group in the GROUP BY's order decides, `first`).
//!
//! Proof: the tables are the stored arrays (`tables`); the statement's FROM/WHERE keeps exactly one joined row per
//! qualifying lineitem row (`from`, `pred`, `bag`), so the GROUP BY's sums are the scan's totals (`group`,
//! `groupby`), and `body` states the statement's outcome from the totals. The per-lineitem normal form is `line`.
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::fns::div::{num_div, num_div_fits};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::{answer_meets, stores_ready, bound_db, outcome_ok, Answer};
use crate::gendb_params::Params;
use crate::query::{param_domain, query_spec_at};
use crate::exec::value::{EVal, view_row, view_result};
use crate::exec::fns::div::num_div_exec;
use crate::link::query::view_rows;
use crate::link::expr::i128_max;

pub mod common;
pub mod tables;
pub mod line;
pub mod ast;
pub mod from;
pub mod pred;
pub mod bag;
pub mod group;
pub mod groupby;
pub mod body;
pub mod cols;
pub mod lookup;
pub mod partpass;
pub mod acc;
pub mod stages;
pub mod first;
pub mod plan;

use tables::*;
use line::*;
use cols::*;
use acc::*;
use body::*;

verus! {

/// The outcome of one year's division: the quotient, its SQL error, or outside its executable domain.
pub open spec fn year_out(t: Tot, o: Result<Result<EVal, SqlError>, crate::exec::value::Capacity>) -> bool {
    match o {
        Ok(Ok(v)) => div_fits_of(t) && div_of(t) == Ok::<Val, SqlError>(v@),
        Ok(Err(e)) => div_fits_of(t) && div_of(t) == Err::<Val, SqlError>(e),
        Err(_) => !div_fits_of(t),
    }
}

/// One year's division from its totals.
fn year_div(a: YAcc, Ghost(t): Ghost<Tot>) -> (o: Result<Result<EVal, SqlError>, crate::exec::value::Capacity>)
    requires yacc_is(a, t),
    ensures year_out(t, o),
{
    let s0: u32 = if a.n_then > 0 { 4 } else { 0 };
    let o = num_div_exec(a.s_then, s0, a.s_all, 4);
    proof {
        assert(s0 as nat == crate::agent::groupby::s0_of(t));
    }
    o
}

/// The output row of year `y` with quotient `v`.
fn year_row(y: i128, v: EVal) -> (r: Vec<EVal>)
    ensures view_row(r@) == out_row(y as int, v@),
{
    let mut r: Vec<EVal> = Vec::new();
    r.push(EVal::Num { coeff: y, scale: 0 });
    r.push(v);
    proof { assert(view_row(r@) =~= out_row(y as int, v@)); }
    r
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
    let ghost db0 = choose|db: Database| bound_db(sv, db);
    proof {
        lemma_model(sv, db0);
        assert(nat_of(ps) == params.p0@ && reg_of(ps) == params.p1@ && typ_of(ps) == params.p2@);
    }
    let c = read_cols(stores, Ghost(sv));
    // threads per pass: the scans saturate memory bandwidth well below the worker bound, so leave every eighth
    // worker's core free for the host's other load (fewer stragglers)
    let nt = if workers >= 16 { workers - workers / 8 } else { workers };
    let dir = match plan::build_dir(&c, params.p0, params.p1, params.p2, nt, dispatch, Ghost(sv), Ghost(ps)) {
        Ok(d) => d,
        Err(e) => { return Err(QueryError::WorkerFailed(e)); },
    };
    let plen = params.p2.len();
    let dir = Arc::new(dir);
    let acc = match plan::line_pass(c, dir.clone(), params.p2, plen, nt, dispatch, Ghost(sv), Ghost(ps)) {
        Ok(a) => a,
        Err(e) => { return Err(QueryError::WorkerFailed(e)); },
    };
    let ghost t95 = tot_y(sv, ps, 1995);
    let ghost t96 = tot_y(sv, ps, 1996);
    // a year's volume mass leaves i128: outside the capacity domain
    if acc.over {
        proof {
            let y = if t95.a_all > i128_max() { 1995int } else { 1996int };
            assert forall|db: Database| #[trigger] bound_db(sv, db) implies
                outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity)) by {
                lemma_model(sv, db);
                lemma_body_group_cap(db, sv, ps, y);
            }
        }
        return Ok(Answer::Capacity);
    }
    assert(masses_fit(sv, ps));
    let p95 = acc.y95.cnt > 0;
    let p96 = acc.y96.cnt > 0;
    let o95 = if p95 { Some(year_div(acc.y95, Ghost(t95))) } else { None };
    let o96 = if p96 { Some(year_div(acc.y96, Ghost(t96))) } else { None };
    decide(&c, &*dir, params.p2, plen, o95, o96, Ghost(sv), Ghost(ps))
}

// ------------------------------------------------------------------------------------------------ outcomes

/// The present years' rows are the answer for every bound database.
proof fn lemma_meets_rows(sv: StoresView, ps: Seq<Literal>, rows: Vec<Vec<EVal>>, v95: Val, v96: Val)
    requires
        model_ok(sv), param_domain(ps), masses_fit(sv, ps),
        present(sv, ps, 1995) ==> div_of(tot_y(sv, ps, 1995)) == Ok::<Val, SqlError>(v95),
        present(sv, ps, 1996) ==> div_of(tot_y(sv, ps, 1996)) == Ok::<Val, SqlError>(v96),
        view_rows(rows@) == out_rows(present(sv, ps, 1995), v95, present(sv, ps, 1996), v96),
    ensures answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Rows(rows))),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
        lemma_model(sv, db);
        lemma_body_rows(db, sv, ps, v95, v96);
    }
}

/// A uniform division error is the answer for every bound database.
proof fn lemma_meets_err(sv: StoresView, ps: Seq<Literal>, y: int, e: SqlError)
    requires
        model_ok(sv), param_domain(ps), masses_fit(sv, ps),
        present(sv, ps, y), div_of(tot_y(sv, ps, y)) == Err::<Val, SqlError>(e),
        present(sv, ps, 1995) ==> div_of(tot_y(sv, ps, 1995)) is Ok || div_of(tot_y(sv, ps, 1995)) == Err::<Val, SqlError>(e),
        present(sv, ps, 1996) ==> div_of(tot_y(sv, ps, 1996)) is Ok || div_of(tot_y(sv, ps, 1996)) == Err::<Val, SqlError>(e),
    ensures answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::SqlError(e))),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::SqlError(e))) by {
        lemma_model(sv, db);
        lemma_body_err(db, sv, ps, y, e);
    }
}

/// A division outside its domain, every division inside its domain succeeding: `Capacity` for every bound database.
proof fn lemma_meets_cap(sv: StoresView, ps: Seq<Literal>, y: int)
    requires
        model_ok(sv), param_domain(ps), masses_fit(sv, ps),
        present(sv, ps, y), !div_fits_of(tot_y(sv, ps, y)),
        present(sv, ps, 1995) && div_fits_of(tot_y(sv, ps, 1995)) ==> div_of(tot_y(sv, ps, 1995)) is Ok,
        present(sv, ps, 1996) && div_fits_of(tot_y(sv, ps, 1996)) ==> div_of(tot_y(sv, ps, 1996)) is Ok,
    ensures answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Capacity)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity)) by {
        lemma_model(sv, db);
        lemma_body_cap(db, sv, ps, y);
    }
}

/// The first group's failing division decides, for every bound database.
proof fn lemma_meets_first(sv: StoresView, ps: Seq<Literal>, y: int)
    requires
        model_ok(sv), param_domain(ps), masses_fit(sv, ps),
        crate::agent::group::dkeys(crate::agent::pred::zrows(sv, ps)).len() > 0,
        crate::agent::group::dkeys(crate::agent::pred::zrows(sv, ps))[0] == crate::agent::bag::ykey(y),
    ensures
        div_fits_of(tot_y(sv, ps, y)) && div_of(tot_y(sv, ps, y)) is Err
            ==> answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::SqlError(div_of(tot_y(sv, ps, y))->Err_0))),
        !div_fits_of(tot_y(sv, ps, y)) ==> answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Capacity)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        (div_fits_of(tot_y(sv, ps, y)) && div_of(tot_y(sv, ps, y)) is Err ==>
            outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::SqlError(div_of(tot_y(sv, ps, y))->Err_0))))
        && (!div_fits_of(tot_y(sv, ps, y)) ==> outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity))) by {
        lemma_model(sv, db);
        lemma_body_first(db, sv, ps, y);
    }
}

/// The answer when every present year's division succeeds: the rows, by year.
fn answer_rows(o95: Option<Result<Result<EVal, SqlError>, crate::exec::value::Capacity>>,
    o96: Option<Result<Result<EVal, SqlError>, crate::exec::value::Capacity>>,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Result<Answer, QueryError>)
    requires
        model_ok(sv), param_domain(ps), masses_fit(sv, ps),
        (o95 is Some) == present(sv, ps, 1995),
        (o96 is Some) == present(sv, ps, 1996),
        o95 matches Some(o) ==> o matches Ok(Ok(_)) && year_out(tot_y(sv, ps, 1995), o),
        o96 matches Some(o) ==> o matches Ok(Ok(_)) && year_out(tot_y(sv, ps, 1996), o),
    ensures answer_meets(sv, ps, r),
{
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let ghost mut v95 = Val::Null;
    let ghost mut v96 = Val::Null;
    match o95 {
        Some(Ok(Ok(v))) => {
            proof { v95 = v@; }
            rows.push(year_row(1995, v));
        },
        _ => {},
    }
    match o96 {
        Some(Ok(Ok(v))) => {
            proof { v96 = v@; }
            rows.push(year_row(1996, v));
        },
        _ => {},
    }
    proof {
        let (b95, b96) = (present(sv, ps, 1995), present(sv, ps, 1996));
        assert(view_rows(rows@) =~= out_rows(b95, v95, b96, v96));
        lemma_meets_rows(sv, ps, rows, v95, v96);
    }
    Ok(Answer::Rows(rows))
}

/// The answer from the present years' division outcomes.
fn decide(c: &Cols, d: &Dir, pat: &'static [u8], plen: usize,
    o95: Option<Result<Result<EVal, SqlError>, crate::exec::value::Capacity>>,
    o96: Option<Result<Result<EVal, SqlError>, crate::exec::value::Capacity>>,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Result<Answer, QueryError>)
    requires
        model_ok(sv), param_domain(ps), scan_ok(*c, *d, sv, ps),
        pat@ == typ_of(ps), plen == pat@.len(),
        masses_fit(sv, ps),
        (o95 is Some) == present(sv, ps, 1995),
        (o96 is Some) == present(sv, ps, 1996),
        o95 matches Some(o) ==> year_out(tot_y(sv, ps, 1995), o),
        o96 matches Some(o) ==> year_out(tot_y(sv, ps, 1996), o),
    ensures answer_meets(sv, ps, r),
{
    let ok95 = match &o95 { Some(Ok(Ok(_))) => true, None => true, _ => false };
    let ok96 = match &o96 { Some(Ok(Ok(_))) => true, None => true, _ => false };
    if ok95 && ok96 {
        return answer_rows(o95, o96, Ghost(sv), Ghost(ps));
    }
    let e95: Option<SqlError> = match &o95 { Some(Ok(Err(e))) => Some(*e), _ => None };
    let e96: Option<SqlError> = match &o96 { Some(Ok(Err(e))) => Some(*e), _ => None };
    let cap95 = match &o95 { Some(Err(_)) => true, _ => false };
    let cap96 = match &o96 { Some(Err(_)) => true, _ => false };
    // one year's division fails with an error, the other succeeds (or is absent): that error
    if e95.is_some() && !cap96 && e96.is_none() {
        let e = e95.unwrap();
        proof { lemma_meets_err(sv, ps, 1995, e); }
        return Ok(Answer::SqlError(e));
    }
    if e96.is_some() && !cap95 && e95.is_none() {
        let e = e96.unwrap();
        proof { lemma_meets_err(sv, ps, 1996, e); }
        return Ok(Answer::SqlError(e));
    }
    // divisions leave their domain and none fails with an error: `Capacity`
    if (cap95 || cap96) && e95.is_none() && e96.is_none() {
        let y: i64 = if cap95 { 1995 } else { 1996 };
        proof { lemma_meets_cap(sv, ps, y as int); }
        return Ok(Answer::Capacity);
    }
    // both years fail: the first group in the GROUP BY's order decides
    let fy = first::first_year(c, d, pat, plen, Ghost(sv), Ghost(ps));
    let y = match fy {
        Some(y) => y,
        None => {
            proof {
                lemma_tot_gap(sv, ps, 1995, 0, n_l(sv) as int);
                lemma_tot_gap(sv, ps, 1996, 0, n_l(sv) as int);
            }
            return Ok(Answer::Capacity);
        },
    };
    proof {
        first_key_present(sv, ps, y as int);
        lemma_meets_first(sv, ps, y as int);
    }
    let o = if y == 1995 { o95 } else { o96 };
    match o {
        Some(Ok(Err(e))) => Ok(Answer::SqlError(e)),
        _ => Ok(Answer::Capacity),
    }
}

/// The first group's year is a present year.
proof fn first_key_present(sv: StoresView, ps: Seq<Literal>, y: int)
    requires
        model_ok(sv),
        crate::agent::group::dkeys(crate::agent::pred::zrows(sv, ps)).len() > 0,
        crate::agent::group::dkeys(crate::agent::pred::zrows(sv, ps))[0] == crate::agent::bag::ykey(y),
    ensures (y == 1995 || y == 1996) && present(sv, ps, y),
{
    lemma_group_keys(sv, ps, 0);
    assert(crate::agent::bag::ykey(y)[0]->Num_coeff == y);
}

} // verus!
