//! TPC-H Q14 (promotion effect) over the flat storages: `100.00 * SUM(promotional volume) / SUM(volume)` of the
//! lineitems shipped in the month from `$1`, the volume being `l_extendedprice * (1 - l_discount)` and a lineitem
//! promotional when its part's `p_type` starts with `PROMO`.
//!
//! Plan of a call (`query`):
//! 1. read the columns as whole stored parts (`cols`); the ship window `[$1, $1 + 1 month)` in stored days
//!    (`bounds`; a failing `$1 + INTERVAL '1' MONTH` is that SQL error when both tables have rows);
//! 2. the part pass (`parts`, parallel over 64-row words): one bit per part row for "`p_type` starts with the
//!    characters `PROMO`", and whether every part key is `row + 1`;
//! 3. the lineitem pass (`plan`, `scan`, parallel over row ranges): per 64-row word a vectorized window mask of the
//!    ship dates, then for the rows inside the window the part row (by subtraction, or a linear search when the keys
//!    are not positional), the volume and the part's bit, summed into exact accumulators with a saturating absolute
//!    mass;
//! 4. the outcome: `Capacity` when the volume mass leaves `i128` or `10000 * sum0` leaves `i128`; NULL without a
//!    qualifying row; else PostgreSQL's numeric division (`exec::fns::div::num_div_exec`), its SQL error, or
//!    `Capacity` outside its executable domain.
//!
//! Proof: the tables are the stored arrays (`tables`); the WHERE keeps the joined rows whose keys match inside the
//! window (`joined`), whose sums are the per-lineitem totals `line::tot` since the part key is a primary key
//! (`common::sum_pick`); the aggregate (`agg`) and the division (`body`) are stated from these totals; `outcome`
//! states the fixed claim for each outcome over every bound database.
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db};
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::query::param_domain;
use crate::exec::value::EVal;
use crate::exec::fns::div::num_div_exec;
use crate::link::expr::i128_max;

pub mod common;
pub mod tables;
pub mod ast;
pub mod line;
pub mod joined;
pub mod agg;
pub mod body;
pub mod cols;
pub mod bounds;
pub mod parts;
pub mod scan;
pub mod plan;
pub mod outcome;

use tables::*;
use line::*;
use body::*;
use cols::*;
use bounds::*;
use parts::*;
use scan::*;
use outcome::*;

verus! {

/// `|x| <= MUL_LIM` exactly when `10000 * x` fits `i128`.
pub const MUL_LIM: i128 = 17014118346046923173168730371588410;

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
        lemma_param(ps);
    }
    let c = read_cols(stores, Ghost(sv));
    let x = match param_window(params) {
        Ok(x) => x,
        Err(e) => {
            if c.nl == 0 || c.np == 0 {
                let rows = single_row(EVal::Null);
                proof { lemma_meets_empty(sv, ps, rows); }
                return Ok(Answer::Rows(rows));
            }
            proof { lemma_meets_month_err(sv, ps, param_day(ps), e); }
            return Ok(Answer::SqlError(e));
        },
    };
    let ghost w = win_of(x);
    let ghost t1 = x.t1 as int;
    // the part pass
    let pc = PartCols { key: c.p_key, offs: c.p_toffs, bytes: c.p_tbytes, nb: c.p_tnb, np: c.np };
    let (bits, pos) = match part_pass(pc, workers, dispatch, Ghost(sv)) {
        Ok(r) => r,
        Err(e) => { return Err(QueryError::WorkerFailed(e)); },
    };
    // the lineitem pass
    let sc = ScanCols { ship: c.l_ship, pkey: c.l_pkey, price: c.l_price, disc: c.l_disc, nl: c.nl, part_key: c.p_key, np: c.np };
    let acc = match plan::line_pass(sc, x, Arc::new(bits), pos, workers, dispatch, Ghost(sv)) {
        Ok(a) => a,
        Err(e) => { return Err(QueryError::WorkerFailed(e)); },
    };
    let ghost t = tot(sv, w, 0, n_l(sv) as int);
    // the volume mass leaves i128
    if acc.mass == MASS_CAP {
        proof { lemma_meets_capacity(sv, ps, w, t1); }
        return Ok(Answer::Capacity);
    }
    assert(t.a_all <= i128_max());
    if acc.cnt == 0 {
        let rows = single_row(EVal::Null);
        proof { lemma_meets_row(sv, ps, w, t1, rows, Val::Null); }
        return Ok(Answer::Rows(rows));
    }
    // 100.00 * sum0: the coefficient 10000 * s_pr must fit i128
    if acc.s_pr < -MUL_LIM || acc.s_pr > MUL_LIM {
        proof {
            assert(!crate::link::expr::fits_i128(10000 * t.s_pr)) by (nonlinear_arith)
                requires t.s_pr < -17014118346046923173168730371588410 || t.s_pr > 17014118346046923173168730371588410;
            lemma_meets_capacity(sv, ps, w, t1);
        }
        return Ok(Answer::Capacity);
    }
    let m = acc.s_pr * 10000;
    let s0: u32 = if acc.n_pr > 0 { 4 } else { 0 };
    proof {
        assert(s0 as nat == crate::agent::agg::s0_of(t));
        assert(crate::link::expr::fits_i128(10000 * t.s_pr));
    }
    match num_div_exec(m, 2 + s0, acc.s_all, 4) {
        Ok(Ok(v)) => {
            let rows = single_row(v);
            proof { lemma_meets_row(sv, ps, w, t1, rows, v@); }
            Ok(Answer::Rows(rows))
        },
        Ok(Err(e)) => {
            proof { lemma_meets_div_err(sv, ps, w, t1, e); }
            Ok(Answer::SqlError(e))
        },
        Err(_) => {
            proof { lemma_meets_capacity(sv, ps, w, t1); }
            Ok(Answer::Capacity)
        },
    }
}

} // verus!
