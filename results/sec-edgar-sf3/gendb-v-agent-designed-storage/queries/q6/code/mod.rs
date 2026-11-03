// AUTHOR MODULE ROOT (crate::agent). You own every file under src/agent/.
//! Query entry: SUM/COUNT per (name, stmt, tag, plabel) over num JOIN sub JOIN pre, top 200 by sum.
//!
//! Plan: `$1`, `$2` as dictionary codes (a missing value: the empty answer); parallel phases over name ranges
//! and pair-code buckets (`phases`): A finds the filings (`sub` rows with fy = `$3`, their num run of uom `$1` and
//! their pre sub-runs), D joins and groups each name range and keeps its best `TOP` groups; then the merge, the flags
//! and the first `TOP` rows (`output`). Each D task answers its own pair codes: with one worker by marking them in a
//! need list over all pre pair codes (`paths::d_local`), with more from a sorted list of its rows' codes
//! (`paths::d_self`). (Phases B and C of `paths::d_routed`, routing codes to per-bucket answer tasks, are unused.)
//! The proof of the answer is `assemble` (accounting and the SQL outcome).
use vstd::prelude::*;
use crate::spec::value::Database;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db};
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::query::param_domain;

pub mod common;
pub mod meaning;
pub mod views;
pub mod reorg;
pub mod fspec;
pub mod bound;
pub mod filings;
pub mod route;
pub mod pairs;
pub mod join;
pub mod assemble;
pub mod load;
pub mod lookup;
pub mod phases;
pub mod output;
pub mod paths;

use crate::stores::num::interface as ni;
use crate::agent::meaning::lemma_ps_ok;
use crate::agent::bound::lemma_bound_facts;
use crate::agent::load::load;
use crate::agent::lookup::{find_uom, find_stmt, lemma_no_uom, lemma_no_stmt};
use crate::agent::assemble::lemma_answer_empty;
use crate::agent::filings::Filing;
use crate::agent::phases::*;
use crate::agent::output::{finish, tasks_done};
use crate::agent::paths::{a_ready, d_all, d_local, d_self};

verus! {

pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires stores_ready(old(stores)@), param_domain(params@), 1 <= workers <= MAX_WORKERS,
    ensures answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    let ghost ps = params@;
    proof {
        let db = choose|db: Database| #[trigger] bound_db(sv, db);
        lemma_bound_facts(sv, db);
        lemma_ps_ok(ps);
    }
    let inp = load(stores, Ghost(sv));
    let u = match find_uom(stores, params.p0, Ghost(sv), Ghost(ps)) {
        Some(u) => u,
        None => {
            let rows = Vec::new();
            proof {
                lemma_no_uom(sv, ps);
                lemma_answer_empty(sv, ps);
                assert(rows@ =~= Seq::<Vec<crate::exec::value::EVal>>::empty());
            }
            return Ok(Answer::Rows(rows));
        },
    };
    let key = match find_stmt(stores, params.p1, Ghost(sv), Ghost(ps)) {
        Some(k) => k,
        None => {
            let rows = Vec::new();
            proof {
                lemma_no_stmt(sv, ps);
                lemma_answer_empty(sv, ps);
                assert(rows@ =~= Seq::<Vec<crate::exec::value::EVal>>::empty());
            }
            return Ok(Answer::Rows(rows));
        },
    };
    proof {
        assert(ni::num_layout_ok(sv.num));
        ni::lemma_uom_runs(sv.num, u as int);
    }
    let rs_n = stores.num.part_len(ni::P_RUN_START);
    let ur_lo = inp.uom_runs[u] as usize;
    let ur_hi = inp.uom_runs[u + 1] as usize;
    let run_adsh = stores.num.extent_u64(ni::P_RUN_ADSH, ur_lo, ur_hi);
    let run_start = stores.num.extent_u64(ni::P_RUN_START, ur_lo, ur_hi + 1);
    let w = workers;
    let nb = workers;
    let c = Ctx {
        inp, run_adsh, run_start, nruns: ur_hi - ur_lo, stmt_key: key, fy_param: params.p2, nb,
        u: Ghost(u as int), ur_lo: Ghost(ur_lo as int), sv: Ghost(sv), ps: Ghost(ps),
    };
    let cuts = bucket_cuts(inp.dicts.ppair_tag, inp.dicts.npp, nb);
    let (ncuts, caps) = name_ranges(&inp, params.p2, w);
    // A: the filings of every name range
    let aouts = match phase_a(c, &cuts, &ncuts, &caps, w, dispatch) {
        Ok(o) => o,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let ghost a_seq = aouts@;
    proof {
        assert(c.sv@ == sv && c.ps@ == ps);
        assert forall|k: int| 0 <= k < w implies #[trigger] a_done(sv, ps, ncuts@[k] as int, ncuts@[k + 1] as int, a_seq[k]) by {
            assert(a_done(c.sv@, c.ps@, ncuts@[k] as int, ncuts@[k + 1] as int, aouts@[k]));
        }
        assert forall|k: int| 0 <= k < w implies #[trigger] a_seq[k].len <= a_seq[k].filings@.len()
            && dfil_ok(sv, ps, a_seq[k].filings@, a_seq[k].len as int) by {
            assert(a_done(sv, ps, ncuts@[k] as int, ncuts@[k + 1] as int, a_seq[k]));
            lemma_a_dfil(sv, ps, ncuts@[k] as int, ncuts@[k + 1] as int, a_seq[k]);
        }
    }
    let mut dcaps: Vec<usize> = Vec::new();
    let mut k: usize = 0;
    while k < w
        invariant
            k <= w, aouts@ == a_seq, a_seq.len() == w, dcaps@.len() == k,
            forall|i: int| 0 <= i < w ==> #[trigger] a_done(sv, ps, ncuts@[i] as int, ncuts@[i + 1] as int, a_seq[i]),
            forall|i: int| 0 <= i < w ==> #[trigger] a_seq[i].len <= a_seq[i].filings@.len()
                && dfil_ok(sv, ps, a_seq[i].filings@, a_seq[i].len as int),
        decreases w - k,
    {
        let m = aouts[k].max_seg;
        dcaps.push(if m <= usize::MAX as u64 { m as usize } else { 0 });
        k = k + 1;
    }
    proof {
        assert(a_ready(sv, ps, a_seq, w as int));
    }
    // one worker: phase D alone, its task answering its own pair codes; more: phases B, C and D
    let gouts = if w == 1 {
        match d_local(c, &cuts, aouts, &dcaps, w, dispatch) {
            Ok(o) => o,
            Err(e) => return Err(QueryError::WorkerFailed(e)),
        }
    } else {
        match d_self(c, &cuts, aouts, &dcaps, w, dispatch) {
            Ok(o) => o,
            Err(e) => return Err(QueryError::WorkerFailed(e)),
        }
    };
    proof {
        assert(c.sv@ == sv && c.ps@ == ps);
        assert(d_all(sv, ps, a_seq, gouts@, w as int));
        assert forall|k: int| 0 <= k < w implies #[trigger] a_done(sv, ps, ncuts@[k] as int, ncuts@[k + 1] as int, a_seq[k])
            && d_done(sv, ps, a_seq[k].filings@, a_seq[k].len as int, gouts@[k]) by {
        }
        assert(tasks_done(sv, ps, ncuts@, a_seq, gouts@, w as int));
    }
    let ans = finish(&inp, params.p1, &ncuts, &gouts, w, Ghost(sv), Ghost(ps), Ghost(a_seq));
    Ok(ans)
}

} // verus!
