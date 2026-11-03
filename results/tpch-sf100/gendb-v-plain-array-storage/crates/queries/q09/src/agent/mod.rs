//! TPC-H Q9 (product type profit measure) over the flat storages: per supplier nation and order year, the profit
//! `l_extendedprice * (1 - l_discount) - ps_supplycost * l_quantity` of the lineitems whose part's name matches `$1`.
//!
//! Plan of a call (`query`):
//! 1. read the columns (`columns`); an empty table makes FROM empty (no rows);
//! 2. the part bitmap (`partmatch`): for `'%<lit>%'` a parallel byte-substring scan of the names (ASCII names),
//!    otherwise the verified `LIKE` on every name, which also finds a name whose `LIKE` raises (the statement's
//!    error, `like_error`);
//! 3. the fast path (TPC-H layouts: positional part and supplier keys, at most 32 nations with keys below 256): the
//!    nation groups and the supplier slots (`nations`), the word locations and compact partsupp records of the
//!    matching parts (`records`, parallel), the day-to-year table, then the parallel lineitem scan into
//!    group-by-year tables (`scan`, `fastpath`);
//! 4. when the fast path does not apply or cannot place a row, the general serial path (`general`);
//! 5. the groups sorted by nation name, then year descending (`entries`); `Capacity` when a group's absolute
//!    amount exceeds `i128::MAX` (`capacity`).
//! The proof: the statement's meaning is a GROUP BY over the projected six-table product (`denotation`), which the
//! primary keys collapse to sums over the lineitem rows (`groups`, `lines`); per nation group and year these are
//! `answer::tsum`, which the scans compute; `answer::lemma_answer` gives the fixed claim for the sorted groups.
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db, outcome_ok};
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::query::{param_domain, query_spec_at};
use crate::link::query::view_rows;

pub mod common;
pub mod tables;
pub mod normal_form;
pub mod denotation;
pub mod lines;
pub mod groups;
pub mod like_error;
pub mod answer;
pub mod capacity;
pub mod columns;
pub mod partmatch;
pub mod nations;
pub mod records;
pub mod scan;
pub mod fastpath;
pub mod entries;
pub mod general;

use tables::*;
use normal_form::*;
use denotation::likes_ok;
use answer::*;
use columns::*;
use partmatch::*;
use nations::*;
use records::*;
use scan::*;
use fastpath::*;
use entries::*;
use general::*;

verus! {

/// The fast path's groups, when its layout facts hold and it places every row (`Ok(None)` otherwise).
fn fast_groups(c: &Cols, bits_a: Arc<Vec<u64>>, reps: &Vec<usize>, ppos: bool, pbase: i64, workers: usize, dispatch: &mut Dispatch,
    Ghost(sv): Ghost<crate::gendb_entry::stores::StoresView>, Ghost(ps): Ghost<Seq<crate::spec::ast::Literal>>)
    -> (r: Result<Option<Vec<Entry>>, crate::gendb_entry::runtime::WorkerFailure>)
    requires
        cols_ok(*c, sv), bits_ok(bits_a@, sv, ps), 1 <= workers <= MAX_WORKERS,
        reps@.len() == c.nn, forall|a: int| 0 <= a < c.nn ==> #[trigger] reps@[a] as int == nrep(sv, a),
        ppos ==> positional(pk(sv), pbase as int), 0 <= pbase, pbase + c.np < i64::MAX,
        c.ns > 0,
    ensures r matches Ok(Some(es)) ==> elist_ok(es@, sv, ps, n_l(sv)),
{
    if !ppos || c.np >= 0x800_0000 {
        return Ok(None);
    }
    let ntab = match nation_table(c, reps, Ghost(sv)) { Some(t) => t, None => { return Ok(None); } };
    let sbase = c.skey[0];
    if sbase < 0 || sbase as i128 + c.ns as i128 >= i64::MAX as i128 || c.ns >= 0x8000_0000 {
        return Ok(None);
    }
    let (sslot, spos) = supplier_slots(c, &ntab, sbase, Ghost(sv));
    if !spos {
        return Ok(None);
    }
    let k = workers;
    let (wl, counts) = match word_locs(&*bits_a, k) { Some(x) => x, None => { return Ok(None); } };
    let pc = match crate::agent::common::popc::pc_table() { Some(t) => t, None => { return Ok(None); } };
    let sslot_a = Arc::new(sslot);
    proof {
        assert forall|u: int| 0 <= u < 64 * bits_a@.len() && #[trigger] crate::agent::common::bits::word_bit(bits_a@, u) implies u < n_p(sv) by {}
    }
    let recs = match build_records(c, bits_a.clone(), sslot_a, sbase, pbase, &counts, k, dispatch, Ghost(sv)) {
        Ok(r) => r,
        Err(e) => { return Err(e); },
    };
    let ytab = year_table();
    let par = ScanPar { pbase, sbase, k };
    proof {
        assert(scan_ok(*c, bits_a@, wl@, recs@, ytab@, pc@, par, sv, ps));
    }
    match fast_scan(c, bits_a, Arc::new(wl), Arc::new(recs), Arc::new(ytab), pc, par, workers, dispatch, Ghost(sv), Ghost(ps)) {
        Ok(Some((acc, cnt, mass))) => Ok(Some(table_entries(&acc, &cnt, mass, Ghost(sv), Ghost(ps)))),
        Ok(None) => Ok(None),
        Err(e) => Err(e),
    }
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
    let c = read_cols(stores, Ghost(sv));
    // 1. an empty table: FROM is empty, no rows
    if c.np == 0 || c.ns == 0 || c.nl == 0 || c.nps == 0 || c.no == 0 || c.nn == 0 {
        let rows: Vec<Vec<crate::exec::value::EVal>> = Vec::new();
        proof {
            assert(view_rows(rows@) =~= Seq::<Row>::empty());
            assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
                like_error::lemma_from_empty(sv, db);
                like_error::lemma_empty_outcome(sv, db, ps);
            }
        }
        return Ok(Answer::Rows(rows));
    }
    let pat: &'static [u8] = params.p0;
    assert(pat@ == pat_of(ps));
    let np = c.np;
    let pbase = c.pkey[0];
    let pb_ok = 0 <= pbase && (pbase as i128) + (np as i128) < i64::MAX as i128 && np < 0x800_0000;
    // 2. the part bitmap
    let mut fast_bits: Option<(Vec<u64>, bool)> = None;
    if pb_ok {
        match contains_pattern_exec(pat) {
            Some(lit) => {
                match part_pass_fast(&c, lit, pbase, workers, dispatch, Ghost(sv), Ghost(ps)) {
                    Ok((bits, asc, pos)) => {
                        if asc {
                            fast_bits = Some((bits, pos));
                        }
                    },
                    Err(e) => { return Err(QueryError::WorkerFailed(e)); },
                }
            },
            None => {},
        }
    }
    let (bits, ppos) = match fast_bits {
        Some(x) => x,
        None => {
            match part_pass_general(&c, pat, Ghost(sv), Ghost(ps)) {
                Ok(bits) => {
                    let pos = if pb_ok { positional_check(c.pkey, np, pbase) } else { false };
                    (bits, pos)
                },
                Err(p) => {
                    proof {
                        assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps),
                            Ok::<Answer, QueryError>(Answer::SqlError(SqlError::InvalidEscapeSequence))) by {
                            like_error::lemma_like_error_outcome(sv, db, ps, p as int);
                        }
                    }
                    return Ok(Answer::SqlError(SqlError::InvalidEscapeSequence));
                },
            }
        },
    };
    assert(bits_ok(bits@, sv, ps) && likes_all_ok(sv, ps));
    let ghost bv = bits@;
    let bits_a = Arc::new(bits);
    assert(bits_a@ == bv);
    // 3. the groups: fast path, else the general path
    let reps = nation_reps(&c, Ghost(sv));
    let fast = if pb_ok {
        match fast_groups(&c, bits_a.clone(), &reps, ppos, pbase, workers, dispatch, Ghost(sv), Ghost(ps)) {
            Ok(x) => x,
            Err(e) => { return Err(QueryError::WorkerFailed(e)); },
        }
    } else {
        None
    };
    let es = match fast {
        Some(es) => es,
        None => {
            match general_path(&c, &*bits_a, &reps, Ghost(sv), Ghost(ps)) {
                GenOut::Entries(es) => es,
                GenOut::Over(a, y) => {
                    proof {
                        assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps),
                            Ok::<Answer, QueryError>(Answer::Capacity)) by {
                            assert(likes_ok(sv, db, ps));
                            capacity::lemma_capacity(sv, db, ps, a as int, y as int);
                        }
                    }
                    return Ok(Answer::Capacity);
                },
            }
        },
    };
    // 4. the rows
    let (rows, ent) = output_rows(&c, &es, Ghost(sv), Ghost(ps));
    proof {
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps),
            Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
            assert(likes_ok(sv, db, ps));
            lemma_answer(sv, db, ps, ent@);
        }
    }
    Ok(Answer::Rows(rows))
}

} // verus!
