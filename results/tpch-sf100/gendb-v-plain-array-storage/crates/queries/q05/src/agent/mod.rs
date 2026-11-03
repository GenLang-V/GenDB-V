//! TPC-H Q5 (local supplier volume) over the flat storages.
//!
//! Plan (every structure is built inside the call):
//! 1. the nation tables (`nations`): which nations lie in the region `$1`, their name groups and one-byte slots;
//! 2. phase 1, parallel (`codes`): the nation slot of every customer and supplier, a bitmap of the customers in the
//!    region (`common::bitmap`), and whether the customer and supplier key columns are dense (a key lookup is then
//!    a subtraction);
//! 3. phase A, parallel (`qkeys`): per chunk of order rows and per batch of 1024 orders, the orders dated in the
//!    year whose customer lies in the region (`batch`, testing the customer bitmap first), and their order keys
//!    (read only for them); the calling thread concatenates the chunk lists and checks that they ascend strictly;
//! 4. phase B, parallel (`scan`, `driver`): each task takes an equal range of lineitem rows and merges their order
//!    keys against that list: whole blocks of keys between two listed keys are skipped by a vector test
//!    (`common::key_skip`), rows of listed orders are checked against their supplier's slot and their revenue is
//!    added to their nation group's exact `i128` accumulator (`common::exact_sum`). If the list does not ascend,
//!    or more than 253 nations lie in the region, every row is computed from scratch (`rows::slow_contrib`);
//! 5. the output (`output`): `Capacity` when a group's SUM mass leaves `i128`, else one row per non-empty group by
//!    revenue descending.
//!
//! The proof: `sem_*` give the statement's meaning in the accumulator normal form of `link::query` over the six-way
//! FROM (`sem_body`), `plan` reduces the groups to sums over lineitem rows (primary keys make each kept FROM row
//! determined by its lineitem row), `contrib` states those sums in the executable code's terms, and the scan
//! proves its accumulators equal them.
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::spec::datetime::*;
use crate::exec::value::EVal;
use crate::query::{param_domain, query_spec_at, param_typed};
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db, capacity_domain};
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::link::query::*;
use crate::agent::model::*;
use crate::agent::sem_ast::*;
use crate::agent::sem_from::*;
use crate::agent::sem_pred::*;
use crate::agent::sem_body::*;
use crate::agent::contrib::*;
use crate::agent::cols::*;
use crate::agent::nations::*;
use crate::agent::codes::*;
use crate::agent::date::*;
use crate::agent::rows::*;
use crate::agent::driver::*;
use crate::agent::qkeys::*;
use crate::agent::output::*;
use crate::agent::common::exact_sum::*;
use crate::agent::common::lookup::dense_keys;

pub mod common;
pub mod model;
pub mod sem_ast;
pub mod sem_from;
pub mod sem_pred;
pub mod sem_body;
pub mod plan;
pub mod contrib;
pub mod cols;
pub mod nations;
pub mod codes;
pub mod date;
pub mod rows;
pub mod batch;
pub mod qkeys;
pub mod scan;
pub mod driver;
pub mod output;

verus! {

/// The parameters of a binding in the domain: `$1` is the text `rp`, `$2` a valid civil date whose day `pd` lies in
/// `[0001-01-01, 9999-12-31]`.
proof fn lemma_params(ps: Seq<Literal>, p0: Seq<u8>, y: i32, m: i32, d: i32)
    requires param_domain(ps), ps == seq![Literal::Text(p0), Literal::Date { y: y as int, m: m as int, d: d as int }],
    ensures ({
        let pd = date_from_civil(y as int, m as int, d as int);
        &&& params_are(ps, p0, pd)
        &&& 1 <= m <= 12
        &&& 1 <= d <= 31
        &&& -730119 <= pd <= 2921939
    }),
{
    assert(date_from_civil(1, 1, 1) == -730119) by (compute);
    assert(date_from_civil(9999, 12, 31) == 2921939) by (compute);
    assert(param_typed(ps));
    assert(days_in_month(y as int, m as int) <= 31);
}

/// An empty table makes the statement's value the empty result.
proof fn lemma_answer_empty(sv: StoresView, ps: Seq<Literal>, rp: Seq<u8>, pd: int)
    requires
        stores_wf(sv), vals_ok(sv), params_are(ps, rp, pd),
        nl(sv) == 0 || no(sv) == 0 || nc(sv) == 0 || ns(sv) == 0 || nn(sv) == 0 || nr(sv) == 0,
    ensures forall|db: Database| #[trigger] bound_db(sv, db) ==> ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(Seq::<Row>::empty())),
{
    lemma_from6_len(sv);
    let n6 = nc(sv) * no(sv) * nl(sv) * ns(sv) * nn(sv) * nr(sv);
    assert(n6 == 0) by (nonlinear_arith)
        requires n6 == nc(sv) * no(sv) * nl(sv) * ns(sv) * nn(sv) * nr(sv),
            nl(sv) == 0 || no(sv) == 0 || nc(sv) == 0 || ns(sv) == 0 || nn(sv) == 0 || nr(sv) == 0;
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(Seq::<Row>::empty())) by {
        lemma_tables(sv, db);
        lemma_query_shape(ps);
        lemma_body_empty(db, sv, ps, rp, pd);
        let oq = query_spec_at(ps);
        let e = Seq::<Row>::empty();
        assert(denote_body(db, oq) == Ok::<Relation, SqlError>(e));
        assert(sorted_by(oq.keys, e));
        assert(slice_rows(e, oq.offset, oq.limit) =~= e);
        assert(e.to_multiset() == e.to_multiset());
    }
}

/// Without the timestamp bound and with every table non-empty, the statement's value is the bound's error.
proof fn lemma_answer_err(sv: StoresView, ps: Seq<Literal>, rp: Seq<u8>, pd: int, e: SqlError)
    requires
        stores_wf(sv), params_are(ps, rp, pd), hi_res(pd) == Err::<int, SqlError>(e),
        nl(sv) > 0 && no(sv) > 0 && nc(sv) > 0 && ns(sv) > 0 && nn(sv) > 0 && nr(sv) > 0,
    ensures forall|db: Database| #[trigger] bound_db(sv, db) ==> ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(e)),
{
    lemma_from6_len(sv);
    let n6 = nc(sv) * no(sv) * nl(sv) * ns(sv) * nn(sv) * nr(sv);
    assert(n6 > 0) by (nonlinear_arith)
        requires n6 == nc(sv) * no(sv) * nl(sv) * ns(sv) * nn(sv) * nr(sv),
            nl(sv) > 0 && no(sv) > 0 && nc(sv) > 0 && ns(sv) > 0 && nn(sv) > 0 && nr(sv) > 0;
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(e)) by {
        lemma_tables(sv, db);
        lemma_query_shape(ps);
        lemma_body_err(db, sv, ps, rp, pd, e);
    }
}

/// A non-empty group whose SUM mass leaves `i128` puts the statement outside the capacity domain.
proof fn lemma_answer_capacity(sv: StoresView, ps: Seq<Literal>, rp: Seq<u8>, pd: int, t: int, inregv: Seq<bool>, gids: Seq<usize>,
    reps: Seq<usize>, totals: Seq<Acc>, g: int)
    requires
        stores_wf(sv), keys_ok(sv), vals_ok(sv), params_are(ps, rp, pd), hi_res(pd) == Ok::<int, SqlError>(t),
        nation_ok(sv, rp, inregv, gids, reps),
        totals_rel(sv, rp, pd, t, gids, reps.len() as int, totals),
        0 <= g < reps.len(), totals[g].cnt > 0, totals[g].over,
    ensures forall|db: Database| #[trigger] bound_db(sv, db) ==> !capacity_domain(db, query_spec_at(ps)),
{
    lemma_over_group(sv, rp, pd, t, inregv, gids, reps, totals, g);
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies !capacity_domain(db, query_spec_at(ps)) by {
        lemma_tables(sv, db);
        lemma_query_shape(ps);
        lemma_body_capacity(db, sv, ps, rp, pd, t, gkey(sv, reps, g));
    }
}

/// The ordered group rows are an allowed output of the statement.
proof fn lemma_answer_rows_all(sv: StoresView, ps: Seq<Literal>, rp: Seq<u8>, pd: int, t: int, inregv: Seq<bool>, gids: Seq<usize>,
    reps: Seq<usize>, totals: Seq<Acc>, ord: Seq<usize>, out: Seq<Row>)
    requires
        vals_ok(sv), params_are(ps, rp, pd), hi_res(pd) == Ok::<int, SqlError>(t),
        answer_hyps(sv, rp, pd, t, inregv, gids, reps, totals, ord),
        out == ord.map_values(|g: usize| grow(sv, reps, g as int, totals[g as int].sum as int)),
    ensures forall|db: Database| #[trigger] bound_db(sv, db) ==> ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    lemma_answer_rows(sv, rp, pd, t, inregv, gids, reps, totals, ord, out);
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)) by {
        lemma_tables(sv, db);
        lemma_query_shape(ps);
        lemma_body_ok(db, sv, ps, rp, pd, t);
        lemma_ordered_link(db, query_spec_at(ps), q5_spec(rp, pd, t), from6(sv), out);
    }
}

/// TPC-H Q5 over the flat storages (see the module comment).
pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures
        answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    let ghost db0 = choose|db: Database| #[trigger] bound_db(sv, db);
    proof {
        lemma_tables(sv, db0);
        lemma_keys(sv, db0);
        lemma_vals(sv, db0);
    }
    let rp = params.p0;
    let ghost ps = params@;
    let ghost pd = date_from_civil(params.p1.y as int, params.p1.m as int, params.p1.d as int);
    proof { lemma_params(ps, rp@, params.p1.y, params.p1.m, params.p1.d); }
    let c = read_cols(stores, Ghost(sv));
    if c.nl == 0 || c.no == 0 || c.nc == 0 || c.ns == 0 || c.nn == 0 || c.nr == 0 {
        proof { lemma_answer_empty(sv, ps, rp@, pd); }
        let out: Vec<Vec<EVal>> = Vec::new();
        proof { assert(view_rows(out@) =~= Seq::<Row>::empty()); }
        return Ok(Answer::Rows(out));
    }
    let (dlo, dhi) = match date_bounds(&params.p1, Ghost(pd)) {
        Ok(b) => b,
        Err(e) => {
            proof { lemma_answer_err(sv, ps, rp@, pd, e); }
            return Ok(Answer::SqlError(e));
        },
    };
    let ghost t = hi_res(pd)->Ok_0;
    let tabs = nation_tables(&c, rp, Ghost(sv));
    let NationTabs { inreg, gids, reps, slots, gos, fast } = tabs;
    let nt = if workers < c.no { workers } else { c.no };
    let ghost x = Ctx { sv, rp: rp@, pd, t, slots: slots@ };
    let codes = if fast {
        match build_codes(&c, &slots, nt, dispatch, Ghost(sv)) {
            Ok(k) => k,
            Err(e) => return Err(QueryError::WorkerFailed(e)),
        }
    } else {
        Codes { ccode: Vec::new(), scode: Vec::new(), bits: Vec::new(), cdense: false, sdense: false }
    };
    let ng = reps.len();
    let ghost inregv = inreg@;
    let ghost gidv = gids@;
    let ghost repv = reps@;
    let Codes { ccode, scode, bits, cdense, sdense } = codes;
    let ck = dense_keys(c.ckeys, c.nc, cdense);
    let sk = dense_keys(c.skeys, c.ns, sdense);
    let shared = Shared { c, ccode, scode, bits, cdense, sdense, ck, sk, inreg, gids, gos, ng, dlo, dhi, fast };
    assert(shared_ok(shared, x));
    let sh = Arc::new(shared);
    // Phase A: per order chunk, the qualifying keys (`None` when they do not ascend over all chunks).
    let qk = if fast {
        match build_qkeys(&sh, nt, dispatch, Ghost(x)) {
            Err(e) => return Err(QueryError::WorkerFailed(e)),
            Ok(o) => o,
        }
    } else {
        None
    };
    // Phase B: the lineitem rows against the chunk lists (or from scratch).
    let totals = match qk {
        Some(chunks) => match scan_all(&sh, chunks, true, nt, dispatch, Ghost(x)) {
            Err(e) => return Err(QueryError::WorkerFailed(e)),
            Ok(tt) => tt,
        },
        None => match scan_all(&sh, Vec::new(), false, workers, dispatch, Ghost(x)) {
            Err(e) => return Err(QueryError::WorkerFailed(e)),
            Ok(tt) => tt,
        },
    };
    assert(totals_rel(sv, rp@, pd, t, gidv, repv.len() as int, totals@));
    match over_group(&totals) {
        Some(g) => {
            proof { lemma_answer_capacity(sv, ps, rp@, pd, t, inregv, gidv, repv, totals@, g as int); }
            return Ok(Answer::Capacity);
        },
        None => {},
    }
    let ord = order_groups(&totals);
    let out = build_rows(&sh.c, &reps, &totals, &ord, Ghost(sv));
    proof {
        lemma_answer_rows_all(sv, ps, rp@, pd, t, inregv, gidv, repv, totals@, ord@, view_rows(out@));
    }
    Ok(Answer::Rows(out))
}

} // verus!
