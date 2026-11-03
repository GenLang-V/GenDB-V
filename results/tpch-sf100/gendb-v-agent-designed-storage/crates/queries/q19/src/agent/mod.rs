// AUTHOR MODULE ROOT (crate::agent). You own every file under src/agent/.
//! TPC-H Q19 (discounted revenue) over the storages `facts` (lineitem, clustered by order, with an l_partkey key
//! index) and `custpart` (part in key order, p_brand / p_container sorted dictionaries).
//!
//! Plan: `$2 + 10`, `$4 + 10` and `$6 + 10` are int4 additions evaluated on every row of `lineitem x part` (AND/OR
//! are strict), so when one leaves int4 the statement's meaning is that error on a non-empty product (a NULL sum on
//! an empty one). Otherwise: the dictionary indices of every text literal and brand parameter are looked up once
//! (`tables`); the part rows are split into ranges, one worker task each (`kernel::ScanTask`); a part row whose
//! brand, container and size satisfy an arm looks up its lineitem rows in the key index and adds the value of every
//! row satisfying that arm's quantity window, ship mode and ship instruction. The calling thread adds the ranges'
//! accumulators (`kernel::merge`); a mass beyond `i128::MAX` is outside the capacity domain.
//!
//! Proof: `terms` states the condition and the accumulators over the stored rows, `kernel` proves the scan against
//! them, `bind` relates the stored parts to the database's rows, `sqlrow` evaluates the WHERE condition and the SUM
//! argument on one row of the product, and `answer` closes the chain for every database bound to the parts.
use vstd::prelude::*;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db, outcome_ok};
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::exec::value::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::link::query::view_rows;
use crate::query::{param_domain, query_spec_at};
use crate::stores::facts::interface::LI_QUANTITY_CODES;
use crate::stores::custpart::interface::{PART_FIRST, PA_PARTKEY_CODES};
use crate::stores::li_partdir::interface as lpd;
use crate::gendb_entry::stored::StoredParts;

pub mod common;
pub mod model;
pub mod terms;
pub mod decode;
pub mod sums;
pub mod kernel;
pub mod tables;
pub mod bind;
pub mod sqlrow;
pub mod joinsum;
pub mod answer;
pub mod sortscan;
pub mod ixmodel;
pub mod fast;

use model::*;
use terms::*;
use kernel::*;
use tables::*;
use answer::*;

verus! {

/// The one result row `[v]`.
fn one_row(v: EVal) -> (rows: Vec<Vec<EVal>>)
    ensures view_rows(rows@) == seq![seq![v@]],
{
    let mut row: Vec<EVal> = Vec::new();
    row.push(v);
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    rows.push(row);
    proof {
        assert(crate::exec::value::view_row(rows@[0]@) =~= seq![v@]);
        assert(view_rows(rows@) =~= seq![seq![v@]]);
    }
    rows
}

/// The keys at the first and last key index positions (guesses for the key search; `(0, 0)` without an index).
fn key_extremes(li: &LiCols, Ghost(fp): Ghost<Seq<PartView>>) -> (r: (i64, i64))
    requires li_cols_ok(*li, fp),
{
    if li.n == 0 || li.kind == 0 {
        return (0, 0);
    }
    let s0 = pos_row(li, 0, Ghost(fp));
    let s1 = pos_row(li, li.n - 1, Ghost(fp));
    (row_key(li, s0, Ghost(fp)), row_key(li, s1, Ghost(fp)))
}

/// The key directory of storage `li_partdir` (guesses only).
fn read_dir(f: &mut StoredParts, Ghost(lp): Ghost<Seq<PartView>>) -> (d: Dir)
    requires old(f)@ == lp, bind::dir_shape(lp),
    ensures final(f)@ == lp, dir_ok(d),
{
    let meta = f.extent_i64(lpd::DIR_META, 0, 2);
    let n = f.part_len(lpd::DIR_OFFS);
    let offs = f.extent_u32(lpd::DIR_OFFS, 0, n);
    Dir { mode: meta[0], kmin: meta[1], offs, n: offs.len() }
}

/// The accumulators over every part row: serially, or in `workers` parallel ranges.
fn run_scan(li: &LiCols, pa: &PaCols, lk: &LiK, arms: &Arms, dir: &Dir, workers: usize, dispatch: &mut Dispatch,
    Ghost(fp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: Result<Option<Acc>, QueryError>)
    requires
        scan_pre(*li, *pa, *lk, *arms, fp, cp, ps),
        dir_ok(*dir),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(o) ==> out_ok(fp, cp, ps, 0, n_pa(cp), o),
        r matches Err(e) ==> e is WorkerFailed,
{
    match sortscan::sorted_plan(li, pa, lk, arms, dir, workers, dispatch, Ghost(fp), Ghost(cp), Ghost(ps)) {
        Some(r) => {
            return r;
        },
        None => {},
    }
    let (kmin, kmax) = key_extremes(li, Ghost(fp));
    if workers == 1 || pa.n < 65536 {
        return Ok(scan_range(li, pa, lk, arms, dir, kmin, kmax, 0, pa.n, Ghost(fp), Ghost(cp), Ghost(ps)));
    }
    let (tasks, Ghost(bnds)) = make_tasks(li, pa, lk, arms, dir, kmin, kmax, workers, Ghost(fp), Ghost(cp), Ghost(ps));
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    Ok(merge(&outs, Ghost(tv), Ghost(bnds), pa.n, Ghost(fp), Ghost(cp), Ghost(ps)))
}

/// The answer of the index plan (`fast::index_plan`), or `None` when it does not apply (the caller then runs the
/// incumbent plan); the stores are unchanged.
fn index_answer(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch, Ghost(db0): Ghost<Database>)
    -> (r: Option<Answer>)
    requires
        bound_db(old(stores)@, db0),
        param_domain(params@),
        no_ovf(params@),
        params.p1 <= 2147483637 && params.p3 <= 2147483637 && params.p5 <= 2147483637,
        1 <= workers <= MAX_WORKERS,
    ensures
        final(stores)@ == old(stores)@,
        r matches Some(ans) ==> answer_meets(old(stores)@, params@, Ok::<Answer, QueryError>(ans)),
{
    let ghost sv = stores@;
    let ghost ps = params@;
    let ghost lp = sv.li_pkship;
    let ghost pp = sv.part_bcs;
    proof {
        ixmodel::lemma_l_link(sv, db0);
        ixmodel::lemma_p_link(sv, db0);
        sqlrow::lemma_params(ps, 0);
        sqlrow::lemma_params(ps, 1);
        sqlrow::lemma_params(ps, 2);
    }
    match fast::index_plan(&mut stores.part_bcs, &mut stores.li_pkship, params.p0, params.p1, params.p2, params.p3,
        params.p4, params.p5, workers, dispatch, Ghost(pp), Ghost(lp), Ghost(ps)) {
        Some(acc) => {
            proof {
                assert(stores@ == sv);
                ixmodel::lemma_ix_tot(sv, db0, ps, 0);
                ixmodel::lemma_ix_tot(sv, db0, ps, 1);
                ixmodel::lemma_ix_tot(sv, db0, ps, 2);
                assert(acc_ok(acc, sv.facts, sv.custpart, ps, 0, n_pa(sv.custpart)));
                assert(acc_small(acc));
            }
            let v = if acc.any { EVal::Num { coeff: acc.sum, scale: 4 } } else { EVal::Null };
            let rows = one_row(v);
            proof {
                lemma_answer_rows(sv, ps, acc, rows);
            }
            Some(Answer::Rows(rows))
        },
        None => {
            proof {
                assert(stores@ == sv);
            }
            None
        },
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
    let ghost fp = sv.facts;
    let ghost cp = sv.custpart;
    let ghost db0 = choose|db: Database| #[trigger] bound_db(sv, db);
    proof {
        bind::lemma_li_link(sv, db0);
        bind::lemma_pa_link(sv, db0);
        bind::lemma_dir_link(sv, db0);
    }
    // `$q + 10` outside int4: the error of every product row.
    if params.p1 > 2147483637 || params.p3 > 2147483637 || params.p5 > 2147483637 {
        let nl = stores.facts.part_len(LI_QUANTITY_CODES);
        let np = stores.custpart.part_len(PART_FIRST + PA_PARTKEY_CODES);
        if nl > 0 && np > 0 {
            proof {
                lemma_answer_err(sv, ps);
            }
            return Ok(Answer::SqlError(SqlError::NumericValueOutOfRange));
        }
        let rows = one_row(EVal::Null);
        proof {
            lemma_answer_empty(sv, ps, rows);
        }
        return Ok(Answer::Rows(rows));
    }
    // The index plan (storages part_bcs and li_pkship), when both indexes are present and the mass fits.
    match index_answer(stores, params, workers, dispatch, Ghost(db0)) {
        Some(ans) => {
            return Ok(ans);
        },
        None => {},
    }
    let li = read_li(&mut stores.facts, Ghost(fp));
    let pa = read_pa(&mut stores.custpart, Ghost(cp));
    let d = read_dicts(&mut stores.facts, &mut stores.custpart, Ghost(fp), Ghost(cp));
    let lk = build_lik(&d, Ghost(fp), Ghost(cp));
    let dir = read_dir(&mut stores.li_partdir, Ghost(sv.li_partdir));
    let nb = d.bo.len();
    let nc = d.co.len();
    proof {
        assert(nb as int <= u64::MAX && nc as int <= u64::MAX);
    }
    let arms = Arms {
        a0: build_arm(&d, params.p0, params.p1, 0, Ghost(fp), Ghost(cp), Ghost(ps)),
        a1: build_arm(&d, params.p2, params.p3, 1, Ghost(fp), Ghost(cp), Ghost(ps)),
        a2: build_arm(&d, params.p4, params.p5, 2, Ghost(fp), Ghost(cp), Ghost(ps)),
    };
    let out = match run_scan(&li, &pa, &lk, &arms, &dir, workers, dispatch, Ghost(fp), Ghost(cp), Ghost(ps)) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    match out {
        None => {
            proof {
                lemma_answer_cap(sv, ps);
            }
            Ok(Answer::Capacity)
        },
        Some(acc) => {
            let v = if acc.any { EVal::Num { coeff: acc.sum, scale: 4 } } else { EVal::Null };
            let rows = one_row(v);
            proof {
                lemma_answer_rows(sv, ps, acc, rows);
            }
            Ok(Answer::Rows(rows))
        },
    }
}

} // verus!
