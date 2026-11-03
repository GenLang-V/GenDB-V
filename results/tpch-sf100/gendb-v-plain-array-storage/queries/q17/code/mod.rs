//! TPC-H Q17 (small-quantity-order revenue) over the flat `lineitem` and `part` storages:
//! `SUM(l_extendedprice) / 7.0` over the lineitems of the parts of brand `$1` and container `$2` whose quantity is
//! below `0.2 * AVG(l_quantity)` of their part.
//!
//! Plan of a call (`query`); `workers` is a maximum, and each phase picks its own task count:
//! 1. read the columns as whole stored parts (`cols`);
//! 2. the part pass (`parts`, parallel over 64-row words, up to `MAX_PART_TASKS`): one bit per part row for
//!    "brand = `$1` and container = `$2`";
//! 3. the keys of the selected part rows, in row order (`keys`, visiting only set bits), as a key set with a
//!    one-bit filter (512 KiB), a two-bit filter (256 KiB) and a prefix directory for exact slot lookup
//!    (`common::keyset`);
//! 4. the lineitem scan (`scan`, parallel over row ranges, up to `MAX_SCAN_TASKS`): per row one `bt` test in the
//!    first filter (the second only for the ~0.5% that pass), collecting candidate rows; then per candidate the
//!    exact lookup and its quantity and price as a hit record (slot, quantity, price);
//! 5. per slot the quantity sum and row count of its key (`group`, calling thread);
//! 6. the qualifying hits and their price sum (`qualify`, calling thread): when every slot is small
//!    (`|sum| < 10^6`, fewer than `2 * 10^14` rows) the test `5 * q * cnt < sum`, which is exactly
//!    `q < 0.2 * AVG` with PostgreSQL's rounded AVG (`avgcmp`); otherwise each slot's AVG by `num_div_exec` and an
//!    exact scaled comparison;
//! 7. the outcome: NULL without a qualifying row, else PostgreSQL's numeric division `sum / 7.0`, its SQL error,
//!    or `Capacity` outside its executable domain (or a slot's AVG outside its domain).
//!
//! Proof: the tables are the stored arrays (`tables`); the subquery's value is computed for every outer row
//! (`sub`); the WHERE keeps the joined rows that join a selected part with a quantity below that value
//! (`joined`); its sums are per-lineitem range sums since the part key is a primary key (`common::sum_pick`); the
//! aggregate and the division are stated from these totals (`body`); `outcome` (and `capacity`) state the fixed
//! claim for each outcome over every bound database.
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

pub mod common;
pub mod tables;
pub mod ast;
pub mod sub;
pub mod joined;
pub mod body;
pub mod avgcmp;
pub mod capacity;
pub mod outcome;
pub mod cols;
pub mod parts;
pub mod keys;
pub mod scan;
pub mod group;
pub mod qualify;

use tables::*;
use sub::sizes_ok;
use joined::{pb, pc};
use body::*;
use cols::*;
use parts::*;
use keys::*;
use scan::*;
use group::*;
use qualify::*;
use outcome::*;

verus! {

/// Part words per part task below which the part pass stays on fewer tasks.
pub const MIN_PART_WORDS: usize = 1024;
/// Lineitem rows per scan task below which the scan stays on fewer tasks.
pub const MIN_SCAN_ROWS: usize = 65536;
/// At most this many part tasks.
pub const MAX_PART_TASKS: usize = 64;
/// At most this many scan tasks: the scan is bound by memory bandwidth well before 64 threads, and every extra
/// thread costs a spawn on the calling thread (measured: 48 tasks at 64 workers ran faster than 64).
pub const MAX_SCAN_TASKS: usize = 48;

/// The task count for `n` units of work: at most `workers` and `cap`, at least 1, and at most one per `per` units.
fn task_count(n: usize, per: usize, workers: usize, cap: usize) -> (t: usize)
    requires 1 <= workers <= MAX_WORKERS, per >= 1,
    ensures 1 <= t <= workers,
{
    let mut t = if workers < cap { workers } else { cap };
    if n / per < t {
        t = n / per;
    }
    if t < 1 {
        t = 1;
    }
    t
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
        lemma_params_text(ps);
    }
    let c = read_cols(stores, Ghost(sv));
    // the part pass
    let pc_ = PartCols {
        b_offs: c.b_offs, b_bytes: c.b_bytes, c_offs: c.c_offs, c_bytes: c.c_bytes, np: c.np,
        b_nb: c.b_nb, c_nb: c.c_nb,
        pb: params.p0, pbn: params.p0.len(), pc: params.p1, pcn: params.p1.len(),
    };
    proof {
        assert(params.p0@ == pb(ps));
        assert(params.p1@ == pc(ps));
    }
    let nw = c.np / 64 + 1;
    let ntp = task_count(nw, MIN_PART_WORDS, workers, MAX_PART_TASKS);
    let bits = match part_pass(pc_, ntp, dispatch, Ghost(sv), Ghost(ps)) {
        Ok(b) => b,
        Err(e) => { return Err(QueryError::WorkerFailed(e)); },
    };
    // the selected keys
    let (ks, Ghost(srows)) = build_keys(&bits, c.p_key, c.np, Ghost(sv), Ghost(ps));
    let ghost keys = ks.keys@;
    let ks = Arc::new(ks);
    // the lineitem scan
    let lc = LineCols { l_pkey: c.l_pkey, l_qty: c.l_qty, l_price: c.l_price, nl: c.nl };
    let nt = task_count(c.nl, MIN_SCAN_ROWS, workers, MAX_SCAN_TASKS);
    let outs = match scan_pass(lc, ks.clone(), nt, dispatch, Ghost(sv)) {
        Ok(o) => o,
        Err(e) => { return Err(QueryError::WorkerFailed(e)); },
    };
    // the per-slot totals
    let (sums, cnts) = slot_sums(&outs, nt, &*ks, Ghost(sv), Ghost(srows), Ghost(ps));
    let thr = Thr { sums, cnts };
    assert(thr_ok(&thr, keys, sv));
    // the qualifying hits
    let (price_sum, nqual) = if check_fast(&thr) {
        final_fast(&outs, nt, &thr, Ghost(keys), Ghost(sv))
    } else {
        match slot_avgs(&thr, Ghost(keys), Ghost(sv)) {
            Ok(av) => final_exact(&outs, nt, &thr, &av, Ghost(keys), Ghost(sv)),
            Err(s) => {
                proof { lemma_meets_capacity_avg(sv, ps, keys, srows, s as int); }
                return Ok(Answer::Capacity);
            },
        }
    };
    let ghost t = tot(sv, ps);
    proof {
        lemma_final_tot(keys, srows, sv, ps);
        assert(price_sum as int == t.sum && nqual as int == t.cnt);
        lemma_tot_bounds(sv, ps);
    }
    // the outcome
    if nqual == 0 {
        let rows = single_row(EVal::Null);
        proof { lemma_meets_row(sv, ps, rows, Val::Null); }
        return Ok(Answer::Rows(rows));
    }
    match num_div_exec(price_sum, 2, 70, 1) {
        Ok(Ok(v)) => {
            let rows = single_row(v);
            proof { lemma_meets_row(sv, ps, rows, v@); }
            Ok(Answer::Rows(rows))
        },
        Ok(Err(e)) => {
            proof { lemma_meets_div_err(sv, ps, e); }
            Ok(Answer::SqlError(e))
        },
        Err(_) => {
            proof { lemma_meets_capacity(sv, ps); }
            Ok(Answer::Capacity)
        },
    }
}

} // verus!
