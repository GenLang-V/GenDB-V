//! TPC-H Q20 (potential part promotion) over the flat storages: the suppliers of nation `$3` that have, for some part
//! whose name matches `$1`, an availability above half of the quantity they shipped of it in the year from `$2`;
//! their names and addresses ordered by name.
//!
//! Plan of a call (`query`), every structure built inside the call:
//! 1. read the columns as whole stored parts (`cols`) and the stored-day window of `$2` (`params::date_window`);
//! 2. the part pass (`partpass`): the keys of the parts whose name matches `$1`, by parallel tasks testing the name
//!    bytes for a `'lit%'` pattern (`common::like_prefix`), else by the verified `LIKE` on every name (which also
//!    finds a name whose `LIKE` raises: then the statement is the error 22025 when supplier, nation and partsupp
//!    are non-empty);
//! 3. the fast path (`fast`): a bitmap of the part keys with a coarse bitmap; one parallel scan (`scan`) in which
//!    each task takes a range of partsupp (its rows whose part matches) and a range of lineitem (per block of 64
//!    rows, the rows in the date window whose part matches, recorded as part key, supplier key and quantity), both
//!    written into `nb` part-key buckets (`bucket`, `common::buckets`: one bucket per worker, 64 in a serial call);
//!    then per bucket (`decide`) the bucket's partsupp rows of all tasks as local slots with a directory, the bucket's
//!    records of all tasks summed into them and every row decided; the supplier keys of the qualifying rows (`supp`).
//!    When a layout fact fails, the general path (`supp::supp_naive`) decides from the definitions;
//! 4. the output rows in the body's order (`out`): for each supplier with a nation row named `$3` holding its
//!    nation key (checked first) and a qualifying supplier key, its row; already in `ORDER BY s_name` order when the
//!    names do not decrease (checked), else sorted.
//!
//! Proof: the statement's meaning over every bound database is `normal::out_rows` (`den_body`, from the subqueries'
//! meanings `den_li`, `den_part`, `den_ps`) or the error 22025 (`den_body::lemma_body_err`); the phases compute
//! exactly its parts.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db, outcome_ok};
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::results::*;
use crate::gendb_params::Params;
use crate::query::{param_domain, query_spec_at, lemma_query_wf_at};
use crate::exec::value::EVal;
use crate::exec::ast::EOrderKey;
use crate::exec::relational::order::{sort_rows_exec, view_keys};
use crate::link::query::{view_rows, lemma_slice_all};
use crate::link::outcome::{lemma_outcome_sorted, lemma_outcome_err};

pub mod common;
pub mod tables;
pub mod ast;
pub mod params;
pub mod normal;
pub mod den_li;
pub mod den_part;
pub mod den_ps;
pub mod den_body;
pub mod cols;
pub mod partpass;
pub mod keys;
pub mod pspass;
pub mod slots;
pub mod linepass;
pub mod bucket;
pub mod scan;
pub mod agg;
pub mod decide;
pub mod supp;
pub mod out;
pub mod fast;

use tables::*;
use params::*;
use normal::*;
use cols::*;
use partpass::*;
use keys::ints;
use pspass::keys_decide;
use supp::*;
use out::*;
use den_li::sizes_ok;
use common::like_prefix::{prefix_pattern, prefix_pattern_exec, prefix_lit};

verus! {

/// The statement's outcome over every bound database is the body's rows `out` (in the body's order, when the
/// names already ascend), or their sort.
proof fn lemma_rows_answer(sv: crate::gendb_entry::stores::StoresView, ps: Seq<Literal>, lo: int, hi: int, db: Database)
    requires
        bound_db(sv, db), model_ok(sv), sizes_ok(sv), param_domain(ps), win_ok(ps, lo, hi),
        likes_ok(sv, ps) || n_ps(sv) == 0 || n_s(sv) == 0 || n_n(sv) == 0,
    ensures
        crate::spec::order::denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(out_rows(sv, ps, lo, hi)),
        sorted_by(ast::q_keys(), out_rows(sv, ps, lo, hi))
            ==> ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out_rows(sv, ps, lo, hi))),
        ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(sort_rows(ast::q_keys(), out_rows(sv, ps, lo, hi)))),
{
    lemma_model(sv, db);
    ast::lemma_query_shape(ps);
    den_body::lemma_body_rows(db, sv, ps, lo, hi);
    let out = out_rows(sv, ps, lo, hi);
    let oq = query_spec_at(ps);
    if sorted_by(ast::q_keys(), out) {
        lemma_outcome_sorted(db, oq, out, out);
        lemma_slice_all(out);
    }
    lemma_query_wf_at(ps);
    crate::bridge::order::lemma_denote_top_ok(db, oq);
    lemma_slice_all(sort_rows(ast::q_keys(), out));
}

/// The answer's rows: the columns when the names ascend, else the sorted rows.
fn answer_of(rc: ResultColumns, Ghost(out): Ghost<Seq<Row>>) -> (r: Answer)
    requires out_ok(rc, out),
    ensures
        r matches Answer::Columns(c) ==> columns_wf(c) && columns_view(c) == out && sorted_by(ast::q_keys(), out),
        r matches Answer::Rows(rows) ==> view_rows(rows@) == sort_rows(ast::q_keys(), out),
        r is Columns || r is Rows,
{
    if names_sorted(&rc, Ghost(out)) {
        Answer::Columns(rc)
    } else {
        let rows = rows_of(&rc, Ghost(out));
        let mut keys: Vec<EOrderKey> = Vec::new();
        keys.push(EOrderKey { col: 0, desc: false, nulls_first: false });
        proof { assert(view_keys(keys@) =~= ast::q_keys()); }
        let sorted = sort_rows_exec(&keys, rows);
        Answer::Rows(sorted)
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
    let ghost db0 = choose|db: Database| bound_db(sv, db);
    proof {
        lemma_model(sv, db0);
        lemma_param(ps);
    }
    let c = read_cols(stores, Ghost(sv));
    proof { assert(sizes_ok(sv)); }
    let (dlo, dhi) = date_window(params);
    let ghost (lo, hi) = (dlo as int, dhi as int);
    // 2. the part keys
    let pat = params.p0;
    let keys: Vec<i64> = if prefix_pattern_exec(pat) {
        let lit = copy_bytes(pat, 0, pat.len() - 1);
        proof {
            assert(lit@ == prefix_lit(pat_of(ps)));
        }
        match part_keys_fast(&c, lit, workers, dispatch, Ghost(sv), Ghost(ps)) {
            Ok(k) => {
                proof {
                    assert forall|p: int| 0 <= p < n_p(sv) implies like_ok(#[trigger] pname(sv, p), pat_of(ps)) by {
                        lemma_pmatch_prefix(sv, ps, p);
                    }
                }
                k
            },
            Err(e) => { return Err(QueryError::WorkerFailed(e)); },
        }
    } else {
        match part_keys_general(&c, pat, Ghost(sv), Ghost(ps)) {
            Ok(k) => k,
            Err(()) => {
                if c.nps > 0 && c.ns > 0 && c.nn > 0 {
                    // a part name's LIKE raises: the statement is that error
                    proof {
                        assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps),
                            Ok::<Answer, QueryError>(Answer::SqlError(SqlError::InvalidEscapeSequence))) by {
                            lemma_model(sv, db);
                            ast::lemma_query_shape(ps);
                            den_body::lemma_body_err(db, sv, ps);
                            lemma_outcome_err(db, query_spec_at(ps), SqlError::InvalidEscapeSequence);
                        }
                    }
                    return Ok(Answer::SqlError(SqlError::InvalidEscapeSequence));
                }
                // some of supplier, nation, partsupp is empty: no rows
                let rows: Vec<Vec<EVal>> = Vec::new();
                proof {
                    den_body::lemma_out_rows_empty(sv, ps, lo, hi);
                    assert(view_rows(rows@) =~= Seq::<Row>::empty());
                    assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps),
                        Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
                        lemma_rows_answer(sv, ps, lo, hi, db);
                        assert(sorted_by(ast::q_keys(), Seq::<Row>::empty()));
                    }
                }
                return Ok(Answer::Rows(rows));
            },
        }
    };
    proof {
        assert forall|v: int| #[trigger] ints(keys@).contains(v) == in_part(sv, ps, v) by {
            lemma_pkeys_in_part(sv, ps, v);
            let all = pkeys(sv, ps, 0, n_p(sv) as int);
            assert(ints(keys@) =~= all);
        }
        assert(keys_decide(ints(keys@), sv, ps));
    }
    // 3. the qualifying supplier keys
    let ss = match fast::fast_supp(&c, &keys, dlo, dhi, workers, dispatch, Ghost(sv), Ghost(ps)) {
        Ok(Some(s)) => s,
        Ok(None) => supp_naive(&c, &keys, dlo, dhi, Ghost(sv), Ghost(ps)),
        Err(e) => { return Err(QueryError::WorkerFailed(e)); },
    };
    // 4. the output rows
    let ma = nation_rows(&c, params.p2, Ghost(sv), Ghost(ps));
    let rc = build_output(&c, &ss, &ma, Ghost(sv), Ghost(ps), Ghost(lo), Ghost(hi));
    let ghost out = out_rows(sv, ps, lo, hi);
    let answer = answer_of(rc, Ghost(out));
    proof {
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps),
            Ok::<Answer, QueryError>(answer)) by {
            lemma_rows_answer(sv, ps, lo, hi, db);
        }
    }
    Ok(answer)
}

} // verus!
