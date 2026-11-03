// AUTHOR MODULE ROOT (crate::agent). You own every file under src/agent/.
//! Query: per (name, cik) the SUM of `num.value` over the `num` rows of unit `$1` joined to the `sub` filings of
//! fiscal year `$2`, kept when above the average of the per-cik sums, by decreasing sum, first 100 rows.
//!
//! Plan (storages `num`, clustered by (uom, adsh), and `sub_fy`, sub in canonical order with a fiscal-year order):
//! 1. look up the uom code of `$1` (sorted dictionary) and its run range (uom directory);
//! 2. binary search of the `fy = $2` range of `sub_fy.fy_order` (rows by fy, cik, name code, row) and a scan of it:
//!    each row finds its run of `(uom, adsh)` (adsh code near its rank, then a code -> run map) and sums it. Several
//!    workers: parallel tasks over position ranges (`scan`); one worker: three passes on the calling thread (`serial`:
//!    match all rows, sum the claimed runs in increasing address order, collect in position order);
//! 3. the qualifying filings come out sorted by (cik, name code): sum each (cik, name) group and each cik
//!    (`groups`);
//! 4. AVG of the per-cik sums, HAVING, sort the kept groups by decreasing sum, first 100.
//! The proof: `nf` (normal form over the source tables), `numlink`/`link` (storages), `eval` (SQL operators),
//! `assemble` (computed groups = SQL groups), `output` (ORDER BY/LIMIT), `cap`/`exits` (Capacity and empty answers).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db, outcome_ok};
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::parallel::{fork_join, Dispatch, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::work::TaskBuffer;
use crate::gendb_params::Params;
use crate::query::{param_domain, query_spec_at};
use crate::exec::value::EVal;
use crate::exec::numeric::num_cmp_exec;
use crate::link::query::{exec_avg_finalize, view_rows, lemma_avg_ok};
use crate::stores::num::interface as num_if;
use crate::stores::sub_fy::interface as sub_if;
use crate::stores::num::interface::common::text::{find_text, text_entry_of};
use common::sort::{par_sort, Filing, FilingOrder, SumRef, DescSumOrder};
use common::sums::rsum;
use scan::{ScanTask, ScanCtx};

pub mod assemble;
pub mod ast;
pub mod cap;
pub mod common;
pub mod eval;
pub mod exits;
pub mod groups;
pub mod link;
pub mod nf;
pub mod numlink;
pub mod output;
pub mod scan;
pub mod serial;
pub mod steps;

verus! {

/// The answer is correct for every database bound to the stores.
pub open spec fn meets(sv: StoresView, p0: Seq<u8>, p1: int, r: Result<Answer, QueryError>) -> bool {
    forall|db: Database| #[trigger] bound_db(sv, db) ==> outcome_ok(db, query_spec_at(nf::lits(p0, p1)), r)
}

/// The stores' parts as a scan context with uom code `u` and its run range.
pub open spec fn ctx_of(sv: StoresView, u: int, p1: int) -> ScanCtx {
    ScanCtx {
        np: sv.num,
        sp: sv.sub_fy,
        u,
        r0: num_if::u64s(sv.num, num_if::P_UOM_RUNS)[u] as int,
        r1: num_if::u64s(sv.num, num_if::P_UOM_RUNS)[u + 1] as int,
        p1,
    }
}

/// Some database is bound: the storages' layouts hold.
proof fn lemma_ready(sv: StoresView)
    requires stores_ready(sv),
    ensures num_if::num_layout_ok(sv.num), sub_if::sub_layout_ok(sv.sub_fy),
{
    let db0 = choose|db: Database| #[trigger] bound_db(sv, db);
    nf::lemma_rows_ok(db0);
}

proof fn outcome_no_uom(sv: StoresView, p0: Seq<u8>, p1: int, empty: Vec<Vec<EVal>>)
    requires
        stores_ready(sv), int_in_range(IntKind::Int4, p1), empty@.len() == 0,
        forall|k: int| 0 <= k < num_if::uom_count(sv.num) ==> num_if::dict_entry(sv.num, num_if::P_UOM_OFF, k) != p0,
    ensures meets(sv, p0, p1, Ok(Answer::Rows(empty))),
{
    lemma_ready(sv);
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(nf::lits(p0, p1)), Ok::<Answer, QueryError>(Answer::Rows(empty))) by {
        let c = ScanCtx { np: sv.num, sp: sv.sub_fy, u: 0, r0: 0, r1: 0, p1 };
        lemma_bound(sv, db, c);
        exits::lemma_no_uom(db, c, p0);
        exits::lemma_empty_answer(db, p0, p1);
        assert(view_rows(empty@) =~= Seq::<Row>::empty());
    }
}

proof fn outcome_big(sv: StoresView, c: ScanCtx, p0: Seq<u8>)
    requires
        stores_ready(sv), c.np == sv.num, c.sp == sv.sub_fy, scan::ctx_ok(c), link::uom_is(c, p0),
        int_in_range(IntKind::Int4, c.p1),
        exists|p: int| 0 <= p < scan::n_sub(c) && #[trigger] scan::big(c, scan::row_at(c, p)),
    ensures meets(sv, p0, c.p1, Ok(Answer::Capacity)),
{
    let p = choose|p: int| 0 <= p < scan::n_sub(c) && #[trigger] scan::big(c, scan::row_at(c, p));
    ast::lemma_query_shape(nf::lits(p0, c.p1));
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(nf::lits(p0, c.p1)), Ok::<Answer, QueryError>(Answer::Capacity)) by {
        lemma_bound(sv, db, c);
        exits::lemma_cap_big(db, c, p0, p);
    }
}

proof fn outcome_top(sv: StoresView, c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>)
    requires
        stores_ready(sv), c.np == sv.num, c.sp == sv.sub_fy, assemble::run_ok(c, p0, l), int_in_range(IntKind::Int4, c.p1),
        exists|t: int| 0 <= t < l.len()
            && common::sums::ssum(l, groups::mass_f(groups::gkey(#[trigger] l[t], true), true)) > i128::MAX as int,
    ensures meets(sv, p0, c.p1, Ok(Answer::Capacity)),
{
    let t = choose|t: int| 0 <= t < l.len()
        && common::sums::ssum(l, groups::mass_f(groups::gkey(#[trigger] l[t], true), true)) > i128::MAX as int;
    ast::lemma_query_shape(nf::lits(p0, c.p1));
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(nf::lits(p0, c.p1)), Ok::<Answer, QueryError>(Answer::Capacity)) by {
        lemma_bound(sv, db, c);
        exits::lemma_cap_top_group(db, c, p0, l, t);
    }
}

proof fn outcome_cik(sv: StoresView, c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>, g: groups::Groups)
    requires
        stores_ready(sv), c.np == sv.num, c.sp == sv.sub_fy, assemble::run_ok(c, p0, l), groups::groups_ok(g, l, true),
        int_in_range(IntKind::Int4, c.p1),
        exists|t: int| 0 <= t < l.len()
            && common::sums::ssum(l, groups::mass_f(groups::gkey(#[trigger] l[t], false), false)) > i128::MAX as int,
    ensures meets(sv, p0, c.p1, Ok(Answer::Capacity)),
{
    let t = choose|t: int| 0 <= t < l.len()
        && common::sums::ssum(l, groups::mass_f(groups::gkey(#[trigger] l[t], false), false)) > i128::MAX as int;
    ast::lemma_query_shape(nf::lits(p0, c.p1));
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(nf::lits(p0, c.p1)), Ok::<Answer, QueryError>(Answer::Capacity)) by {
        lemma_bound(sv, db, c);
        exits::lemma_cap_cik_group(db, c, p0, l, g, t);
    }
}

proof fn outcome_avg_mass(sv: StoresView, c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>, g: groups::Groups,
    cg: groups::Groups, h0: int)
    requires
        stores_ready(sv), c.np == sv.num, c.sp == sv.sub_fy, assemble::run_ok(c, p0, l), groups::groups_ok(g, l, true),
        groups::groups_ok(cg, l, false), int_in_range(IntKind::Int4, c.p1), 0 < h0 <= cg.sum@.len(),
        common::sums::rsum(0, h0, |i: int| crate::spec::numeric::abs(cg.sum@[i] as int)) > i128::MAX as int,
    ensures meets(sv, p0, c.p1, Ok(Answer::Capacity)),
{
    ast::lemma_query_shape(nf::lits(p0, c.p1));
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(nf::lits(p0, c.p1)), Ok::<Answer, QueryError>(Answer::Capacity)) by {
        lemma_bound(sv, db, c);
        exits::lemma_cap_avg_mass(db, c, p0, l, g, cg, h0);
    }
}

proof fn outcome_empty(sv: StoresView, c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>, g: groups::Groups,
    cg: groups::Groups, empty: Vec<Vec<EVal>>)
    requires
        stores_ready(sv), c.np == sv.num, c.sp == sv.sub_fy, assemble::run_ok(c, p0, l), groups::groups_ok(g, l, true),
        groups::groups_ok(cg, l, false), int_in_range(IntKind::Int4, c.p1), cg.sum@.len() == 0, empty@.len() == 0,
    ensures meets(sv, p0, c.p1, Ok(Answer::Rows(empty))),
{
    lemma_pass_sizes(l, cg, false);
    lemma_pass_sizes(l, g, true);
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(nf::lits(p0, c.p1)), Ok::<Answer, QueryError>(Answer::Rows(empty))) by {
        lemma_bound(sv, db, c);
        exits::lemma_no_filings(db, c, p0, l, g);
        exits::lemma_empty_answer(db, p0, c.p1);
        assert(view_rows(empty@) =~= Seq::<Row>::empty());
    }
}

proof fn outcome_div(sv: StoresView, c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>, g: groups::Groups,
    cg: groups::Groups, total: int)
    requires
        stores_ready(sv), c.np == sv.num, c.sp == sv.sub_fy, assemble::run_ok(c, p0, l), groups::groups_ok(g, l, true),
        groups::groups_ok(cg, l, false), int_in_range(IntKind::Int4, c.p1), cg.sum@.len() > 0,
        total == common::sums::rsum(0, cg.sum@.len() as int, |i: int| cg.sum@[i] as int),
        !crate::spec::fns::div::num_div_fits(total, 4, cg.sum@.len() as int, 0),
    ensures meets(sv, p0, c.p1, Ok(Answer::Capacity)),
{
    ast::lemma_query_shape(nf::lits(p0, c.p1));
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(nf::lits(p0, c.p1)), Ok::<Answer, QueryError>(Answer::Capacity)) by {
        lemma_bound(sv, db, c);
        exits::lemma_cap_avg_div(db, c, p0, l, g, cg, total);
    }
}

proof fn outcome_rows(sv: StoresView, c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>, g: groups::Groups,
    cg: groups::Groups, total: int, ac: int, asc: nat, sorted: Seq<SumRef>, rows: Vec<Vec<EVal>>)
    requires
        stores_ready(sv), c.np == sv.num, c.sp == sv.sub_fy, assemble::run_ok(c, p0, l), groups::groups_ok(g, l, true),
        groups::groups_ok(cg, l, false), int_in_range(IntKind::Int4, c.p1),
        total == common::sums::rsum(0, cg.sum@.len() as int, |h: int| cg.sum@[h] as int),
        -crate::link::expr::i128_max() <= total <= crate::link::expr::i128_max(),
        cg.sum@.len() > 0,
        crate::spec::fns::div::num_div_fits(total, 4, cg.sum@.len() as int, 0),
        crate::link::query::avg_of(total, 4, cg.sum@.len()) == (Val::Num { coeff: ac, scale: asc }),
        g.sum@.len() <= u64::MAX,
        sorted.to_multiset() == output::kept_upto(g, ac, asc, g.sum@.len() as int).to_multiset(),
        common::sort::sorted_by(DescSumOrder {}, sorted),
        view_rows(rows@) == crate::spec::order::slice_rows(sorted.map_values(output::rr_of(c.sp, g)), 0, Some(100nat)),
    ensures meets(sv, p0, c.p1, Ok(Answer::Rows(rows))),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(nf::lits(p0, c.p1)), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
        lemma_bound(sv, db, c);
        output::lemma_rows_answer(db, c, p0, l, g, cg, total, ac, asc, sorted, view_rows(rows@));
    }
}


/// Every database bound to the stores is bound to the scan context's parts.
proof fn lemma_bound(sv: StoresView, db: Database, c: ScanCtx)
    requires bound_db(sv, db), c.np == sv.num, c.sp == sv.sub_fy,
    ensures link::bound(db, c), crate::spec::typing::db_wf(db), db.schema == crate::schema::schema_spec(),
{
    nf::lemma_rows_ok(db);
}

/// A pass has groups exactly when it has filings.
proof fn lemma_pass_sizes(l: Seq<Filing>, g: groups::Groups, by_name: bool)
    requires groups::groups_ok(g, l, by_name),
    ensures (g.sum@.len() == 0) == (l.len() == 0),
{
    reveal(groups::gf_wit);
    reveal(groups::gf_cover);
    if l.len() > 0 {
        let h = choose|h: int| 0 <= h < g.sum@.len() && #[trigger] groups::gk(g.cik@, g.name@, h, by_name)
            == groups::gkey(l[0], by_name);
    }
    if g.sum@.len() > 0 {
        let t = choose|i: int| 0 <= i < l.len() && groups::gkey(#[trigger] l[i], by_name) == groups::gk(g.cik@, g.name@, 0, by_name);
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
    let ghost p0 = params.p0@;
    let ghost p1 = params.p1 as int;
    proof {
        lemma_ready(sv);
        assert(params@ =~= nf::lits(p0, p1));
        assert(int_in_range(IntKind::Int4, p1));
    }
    let r = query_steps(stores, params, workers, dispatch, Ghost(sv));
    r
}

/// The steps of `query`, with the answer's meaning stated at the parameters' literals.
fn query_steps(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch, Ghost(sv): Ghost<StoresView>)
    -> (r: Result<Answer, QueryError>)
    requires
        old(stores)@ == sv,
        stores_ready(sv),
        num_if::num_layout_ok(sv.num), sub_if::sub_layout_ok(sv.sub_fy),
        int_in_range(IntKind::Int4, params.p1 as int),
        1 <= workers <= MAX_WORKERS,
    ensures
        r is Err ==> r->Err_0 is WorkerFailed,
        r is Ok ==> meets(sv, params.p0@, params.p1 as int, r),
{
    hide(scan::filt);
    hide(steps::inputs_ok);
    hide(scan::slices_ok);
    hide(num_if::num_layout_ok);
    hide(sub_if::sub_layout_ok);
    let ghost p0 = params.p0@;
    let ghost p1 = params.p1 as int;
    // ---- 1. uom code, its runs and the parts the scan reads
    let u = match steps::lookup_uom(&mut stores.num, params.p0) {
        Some(u) => u,
        None => {
            let empty: Vec<Vec<EVal>> = Vec::new();
            proof { outcome_no_uom(sv, p0, p1, empty); }
            return Ok(Answer::Rows(empty));
        },
    };
    let ghost c = ctx_of(sv, u as int, p1);
    let (ni, si) = steps::read_inputs(stores, u, params.p1, Ghost(c));
    proof {
        assert(link::uom_is(c, p0));
    }
    // ---- 2. the parallel scan
    let filings = match steps::scan_all(&ni, &si, params.p1, workers, dispatch, Ghost(c)) {
        Ok(Ok(f)) => f,
        Ok(Err(_)) => {
            proof { outcome_big(sv, c, p0); }
            return Ok(Answer::Capacity);
        },
        Err(e) => return Err(e),
    };
    // ---- 3. the filings (already in (cik, name) order) and their groups
    let sorted = filings;
    let ghost l = sorted@;
    proof {
        reveal(sub_if::sub_layout_ok);
        assemble::lemma_filt_sorted(c, scan::n_sub(c));
        assert(assemble::run_ok(c, p0, l));
        assemble::lemma_filings_ok(c, p0, l);
    }
    let g = match groups::group_pass(&sorted, true) {
        Ok(g) => g,
        Err(_) => {
            proof { outcome_top(sv, c, p0, l); }
            return Ok(Answer::Capacity);
        },
    };
    let cg = match groups::group_pass(&sorted, false) {
        Ok(cg) => cg,
        Err(_) => {
            proof { outcome_cik(sv, c, p0, l, g); }
            return Ok(Answer::Capacity);
        },
    };
    let total = match steps::cik_totals(&cg) {
        Ok(t) => t,
        Err(h0) => {
            proof { outcome_avg_mass(sv, c, p0, l, g, cg, h0 as int); }
            return Ok(Answer::Capacity);
        },
    };
    let nc = cg.sum.len();
    if nc == 0 {
        let empty: Vec<Vec<EVal>> = Vec::new();
        proof { outcome_empty(sv, c, p0, l, g, cg, empty); }
        return Ok(Answer::Rows(empty));
    }
    // ---- 4. AVG, HAVING, ORDER BY sum DESC, LIMIT
    let (avg_c, avg_s) = match exec_avg_finalize(total, 4, nc as u64) {
        Ok(EVal::Num { coeff, scale }) => (coeff, scale),
        Ok(_) => {
            proof {
                lemma_avg_ok(total as int, 4, nc as int);
                assert(false);
            }
            return Err(QueryError::Malformed);
        },
        Err(_) => {
            proof { outcome_div(sv, c, p0, l, g, cg, total as int); }
            return Ok(Answer::Capacity);
        },
    };
    let kept = steps::having(&g, avg_c, avg_s);
    let ghost kept_all = kept@;
    let ng = g.sum.len();
    let kept = common::sort::seq_sort(&DescSumOrder {}, kept);
    proof {
        output::lemma_sorted_kept(c.sp, g, avg_c as int, avg_s as nat, kept@);
        assert forall|h: int| 0 <= h < ng implies #[trigger] link::key_valid(c.sp, assemble::hkey(g, h, true), true) by {
            assemble::lemma_hkey_valid(c, p0, l, g, true, h);
        }
        reveal(groups::gf_vals);
    }
    let rows = steps::output_rows(&kept, &g, &si, Ghost(c.sp));
    proof {
        assert(crate::link::expr::i128_max() == i128::MAX as int);
        outcome_rows(sv, c, p0, l, g, cg, total as int, avg_c as int, avg_s as nat, kept@, rows);
    }
    Ok(Answer::Rows(rows))
}

} // verus!
