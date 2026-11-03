//! SEC Q4: per (sic, tlabel, stmt) the distinct companies, SUM and AVG of the values of `$1` facts presented in
//! statement `$2` by filings of sic in `[$3, $4]`, HAVING two companies, the 500 largest sums.
//!
//! Plan (pre-driven join): map every pre (tag, version) pair to its num pair code and its tag row (parallel
//! dictionary and pair merges), select the qualifying filings sorted by (sic, cik), look up each filing's num run
//! and pre adsh code (parallel), then per filing and qualifying pre row sum the run's rows of the pair code (one
//! contribution each), aggregate the contributions per (sic, tlabel slot) one sic block at a time, sort by SUM.
//! The proof reduces the statement's rows to these contributions (`filing::lemma_all`, `result`).
use vstd::prelude::*;
pub mod common;
pub mod sem;
pub mod group;
pub mod chain;
pub mod levels;
pub mod filing;
pub mod maps;
pub mod pairs;
pub mod mapfacts;
pub mod filings;
pub mod join;
pub mod cbuf;
pub mod weights;
pub mod agg;
pub mod avg;
pub mod result;
pub mod inputs;
pub mod pipeline;
pub mod output;
pub mod prove;
use std::sync::Arc;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db, outcome_ok};
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::query::param_domain;
use crate::spec::value::Database;
use crate::agent::mapfacts::tvi;
use crate::agent::filing::*;
use crate::agent::join::*;
use crate::agent::cbuf::{CBuf, cflat};
use crate::agent::agg::*;
use crate::agent::result::*;
use crate::agent::inputs::*;
use crate::agent::pipeline::*;
use crate::agent::output::build_output;
use crate::agent::prove::*;
use crate::agent::pairs::*;
use crate::agent::filings::{lk_ok, qn_spec};
use crate::agent::common::dictmap::NONE;
use crate::spec::numeric::abs;
use crate::stores::num::interface as N;
use crate::stores::pre::interface as P;

verus! {

pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires stores_ready(old(stores)@), param_domain(params@), 1 <= workers <= MAX_WORKERS,
    ensures answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    // At most 32 threads per parallel stage: 64 were never faster here (SMT siblings) and spawn twice the threads.
    let workers: usize = if workers > 32 { 32 } else { workers };
    proof { lemma_layouts(sv); }
    let nin = read_num(&mut stores.num);
    let pin = read_pre(&mut stores.pre);
    let tin = read_tag(&mut stores.tag_tv);
    let sin = read_sub(&mut stores.sub_sic);
    let ghost (num, pre, tag, sub) = (sv.num, sv.pre, sv.tag_tv, sv.sub_sic);
    let ghost (b0, b1, lo, hi) = (params.p0@, params.p1@, params.p2 as int, params.p3 as int);
    let (u, sc, r0, r1, gqv) = stage_keys(&nin, &pin, params.p0, params.p1, Ghost(num), Ghost(pre));
    let (filv, fsv, fcv) = stage_filings(&sin, params.p2, params.p3, Ghost(sub));
    let ghost fil = filv@;
    let fila = Arc::new(filv);
    let gqa = Arc::new(gqv);
    let look = match stage_look(dispatch, workers, &nin, &pin, &sin, fila, u, sc, r0, r1, gqa.clone(),
        Ghost(num), Ghost(pre), Ghost(sub), Ghost(b0)) {
        Ok(x) => x,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let ghost lookv = look@;
    let ghost cx = mk_cx(b0, b1, lo, hi, num, sub, tag, pre, tvi(u), tvi(sc), fil, lookv);
    proof {
        assert forall|f: int| 0 <= f < lookv.len() implies tvi((#[trigger] lookv[f]).0) < N::run_count(cx.num)
            && tvi(lookv[f].1) < P::adsh_count(cx.pre)
            && (lookv[f].0 == NONE ==> lookv[f].1 == NONE)
            && lookv[f].2 as int == (if lookv[f].0 != NONE && lookv[f].1 != NONE { qn_spec(cx.pre, cx.sc, lookv[f].1 as int) } else { 0 })
            && lookv[f].2 <= P::row_count(cx.pre) by {
            assert(lk_ok(num, pre, b0, tvi(u), tvi(sc), text_entry_s(sin, fil[f] as int), lookv[f]));
        }
    }
    let looka = Arc::new(look);
    let lk = lk_inputs(&nin, &pin, &tin, Ghost(num), Ghost(pre), Ghost(tag));
    let pi = match pair_lookups(dispatch, workers, lk, looka.clone(), pin.adsh_subs, pin.sub_group, pin.sub_start, pin.tv,
        gqa.clone(), Ghost(num), Ghost(pre), Ghost(tag)) {
        Ok(x) => x,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let bufs = match stage_join(dispatch, workers, Ghost(cx), looka, &nin, &pin, &tin, gqa, pi, lk, Ghost(fil)) {
        Ok(x) => x,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    // The contributions, kept as the join tasks' vectors in filing order.
    let ghost cs = cflat(bufs@);
    let ns = tin.tl.off.len();
    proof {
        assert(join_out_ok(cx, tin.tl.n as u64, cs));
        assert(ns == ntl(cx) + 1);
        assert(stages_ok(sv, cx, nin, pin, tin, sin, fil, fsv@, fcv@, lookv));
        assert(cs_sorted(fsv@, fcv@, cs, ns as int)) by {
            assert forall|k1: int, k2: int| 0 <= k1 < k2 < cs.len() implies
                fsv@[(#[trigger] cs[k1]).f as int] < fsv@[(#[trigger] cs[k2]).f as int]
                || (fsv@[cs[k1].f as int] == fsv@[cs[k2].f as int] && fcv@[cs[k1].f as int] <= fcv@[cs[k2].f as int]) by {
                assert(cs[k1].f <= cs[k2].f && cs[k2].f < fil.len());
                assert(fil_ok(sin, lo, hi, fil, fsv@, fcv@));
            }
            assert forall|k: int| 0 <= k < cs.len() implies (#[trigger] cs[k]).f < fsv@.len() && cs[k].f < fcv@.len()
                && cs[k].slot < ns && cs[k].cnt > 0 by {
                assert(contrib_ok(cx.num, cs[k]));
            }
        }
        assert forall|k: int| 0 <= k < cs.len() implies (#[trigger] cs[k]).ok ==> abs(cs[k].sum as int) <= cs[k].mass as int
            && cs[k].mass <= i128::MAX as u128 by {
            assert(contrib_ok(cx.num, cs[k]));
            lemma_triangle(cx.num, cs[k].rs@, cs[k].re@, cs[k].nq@);
        }
        assert(cs.len() <= u64::MAX);
    }
    proof { lemma_query_ps(params@, b0, b1, lo, hi); }
    match aggregate(&bufs, &fsv, &fcv, ns) {
        Err(cap) => {
            proof {
                assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, crate::query::query_spec_at(params@), Ok::<Answer, QueryError>(Answer::Capacity)) by {
                    lemma_cx_ok(db, sv, cx, nin, pin, tin, sin, fil, fsv@, fcv@, lookv);
                    lemma_answer_cap(db, params@, cx, cs, fsv@, fcv@, cap);
                }
            }
            Ok(Answer::Capacity)
        },
        Ok(gs) => {
            let (rows, Ghost(p)) = build_output(&gs, &tin.tl, params.p1, Ghost(cx), Ghost(fsv@), Ghost(fcv@), Ghost(cs));
            proof {
                assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, crate::query::query_spec_at(params@), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
                    lemma_cx_ok(db, sv, cx, nin, pin, tin, sin, fil, fsv@, fcv@, lookv);
                    assert(res_pre(db, cx, cs, fsv@, fcv@, gs@));
                    lemma_answer_rows(db, params@, cx, cs, fsv@, fcv@, gs@, p, rows@);
                }
            }
            Ok(Answer::Rows(rows))
        },
    }
}

/// The binding's view is `ps_of` of its fields, inside the int4 domain.
proof fn lemma_query_ps(ps: Seq<crate::spec::ast::Literal>, b0: Seq<u8>, b1: Seq<u8>, lo: int, hi: int)
    requires
        param_domain(ps),
        ps == crate::agent::sem::ps_of(b0, b1, lo, hi),
    ensures crate::agent::sem::bind_ok(lo, hi),
{
}

} // verus!
