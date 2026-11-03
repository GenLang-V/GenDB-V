//! TPC-H Q19 (discounted revenue) over the flat `lineitem` and `part` storages: `SUM(l_extendedprice * (1 -
//! l_discount))` over the lineitems whose part satisfies one of three branches (brand `$1`/`$3`/`$5`, a container
//! family, a size range) together with the branch's quantity window (`$2`/`$4`/`$6` to `+ 10`), shipped by air and
//! delivered in person.
//!
//! Plan of a call (`query`):
//! 1. read the columns as whole stored parts (`cols`); bind the parameters (`bind`; when some `$k + 10` leaves int4,
//!    the WHERE condition fails with that error on every joined row);
//! 2. the part pass (`parts`, parallel over 64-row words): per task, the keys and branch codes of its part rows that
//!    satisfy some branch;
//! 3. the key map (`keymap`, calling thread): the tasks' keys in a 512 KiB Bloom filter and in a table from key to
//!    branch code (`common::key_tags`);
//! 4. the lineitem pass (`plan`, `scan`, parallel over row ranges): per 64-row word a branch-free probe of
//!    `l_partkey` in the filter, then for the few candidates the branch code from the table, the quantity windows,
//!    ship instruction and mode, and the volume `l_extendedprice * (1 - l_discount)` summed exactly with a
//!    saturating absolute mass;
//! 5. the outcome: `Capacity` when the volume mass leaves `i128`; NULL without a qualifying row; else the sum at
//!    scale 4.
//!
//! Proof: the tables are the stored arrays (`tables`); the statement's tree is cut into named parts (`ast`); on the
//! joined rows the WHERE condition is a two-valued function or the error of `$k + 10` (`joined`); the kept rows'
//! sums are the per-lineitem totals `line::tot` since the part key is a primary key (`common::sum_pick`); the
//! aggregate (`agg`) and the body (`body`) are stated from these totals; `outcome` states the fixed claim for each
//! outcome over every bound database. The executable passes prove their results against `line::tot` row range by
//! row range.
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

pub mod common;
pub mod tables;
pub mod line;
pub mod ast;
pub mod joined;
pub mod agg;
pub mod body;
pub mod outcome;
pub mod cols;
pub mod bind;
pub mod parts;
pub mod keymap;
pub mod scan;
pub mod gather;
pub mod plan;

use tables::*;
use line::*;
use cols::*;
use bind::*;
use parts::*;
use keymap::*;
use scan::*;
use agg::grow;
use outcome::*;

verus! {

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
    }
    let lc = read_line(stores, Ghost(sv));
    let pc = read_part(stores, Ghost(sv));
    // the parameters, or the error of `$k + 10` on a non-empty product
    let x = match make_bind(params) {
        Some(x) => x,
        None => {
            if lc.nl == 0 || pc.np == 0 {
                let rows = single_row(EVal::Null);
                proof { lemma_meets_empty(sv, ps, rows); }
                return Ok(Answer::Rows(rows));
            }
            proof { lemma_meets_err(sv, ps); }
            return Ok(Answer::SqlError(SqlError::NumericValueOutOfRange));
        },
    };
    // the part pass and the key map
    let (outs, nt) = match part_pass(pc, x, workers, dispatch, Ghost(sv), Ghost(ps)) {
        Ok(b) => b,
        Err(e) => { return Err(QueryError::WorkerFailed(e)); },
    };
    // the task lists in order, or (when some task's buffers filled up) the list made on this thread
    let (keys, codes) = if any_full(&outs) {
        serial_keys(&pc, &x, Ghost(sv), Ghost(ps))
    } else {
        concat_keys(&outs, nt, pc.np, Ghost(sv), Ghost(ps))
    };
    let km = build_keymap(keys, codes, Ghost(sv), Ghost(ps));
    // the lineitem pass
    let sc = ScanCols { line: lc };
    let acc = match plan::line_pass(sc, x, Arc::new(km), workers, dispatch, Ghost(sv), Ghost(ps)) {
        Ok(a) => a,
        Err(e) => { return Err(QueryError::WorkerFailed(e)); },
    };
    let ghost t = tot(sv, ps, 0, n_l(sv) as int);
    // the volume mass leaves i128
    if acc.mass == MASS_CAP {
        proof { lemma_meets_capacity(sv, ps); }
        return Ok(Answer::Capacity);
    }
    let v = if acc.cnt == 0 { EVal::Null } else { EVal::Num { coeff: acc.s_all, scale: 4 } };
    let rows = single_row(v);
    proof {
        assert(seq![v@] == grow(t));
        lemma_meets_row(sv, ps, rows);
    }
    Ok(Answer::Rows(rows))
}

} // verus!
