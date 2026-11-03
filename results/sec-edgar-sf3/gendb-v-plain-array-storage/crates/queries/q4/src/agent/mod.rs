//! Query: per `(sic, tlabel, stmt)` group of the `num` rows with `uom = $1` joined with their `sub` row (sic in
//! `[$3, $4]`), their non-abstract `tag` row and every `pre` row of the same adsh, tag and version with
//! `stmt = $2`: COUNT(DISTINCT cik), SUM(value), AVG(value); groups with at least two ciks, top 500 by sum.
//!
//! Plan (every phase is exact; buffer sizes, thresholds and the filter order are heuristics):
//! 1. `sub`: index of the sub rows with sic in range, by adsh (`sub`);
//! 2. `pre` (parallel): rows with `stmt = $2` and a selected sub row (`pre`, `drive::run_pre`);
//! 3. `tag` (parallel): the tag row (`abstract = 0`) of each candidate's tag and version, by one scan of `tag`
//!    against an index of the candidates (`tagres`); the candidates with one are the pre entries (`ents`), indexed
//!    by sub row, tag and version, with group ids `(sic, tlabel)` and pair ids `(group, cik)` (`groups`);
//! 4. `num` (parallel): for each num row with `uom = $1` and a selected sub row, one record per matching entry,
//!    in row order (`scan`, `drive::run_scan`);
//! 5. the GROUP BY fold over the records in order (`fold`); a group whose sum leaves `i128` or whose average is
//!    outside the division domain makes the answer `Capacity` (`answer::lemma_capacity`);
//! 6. HAVING, ORDER BY sum DESC, LIMIT 500: the candidates above about the 500th largest sum, stably sorted
//!    (`topk`, `rows`).
//! The proof that this is the statement's meaning: `sem`, `join`, `decomp` (FROM/WHERE = records), `group`
//! (GroupBy = fold), `answer` (body, ordered output, capacity).
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::Answer;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::stores::Stores;
use crate::gendb_params::Params;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::int::*;
use crate::exec::value::{EVal, view_row};
use crate::link::query::{view_rows, exec_avg_finalize};
use crate::stores::flat_num::interface as ni;
use crate::stores::flat_sub::interface as si;
use crate::stores::flat_tag::interface as ti;
use crate::stores::flat_pre::interface as pi;
use crate::link::query::text_wf;
use crate::agent::common::hash::text_hash;
use crate::agent::common::chains::may_contain;
use crate::agent::common::text::{text_val, bytes_eq};
use crate::agent::common::select::kth_largest;
use crate::agent::cols::*;
use crate::agent::sub::*;
use crate::agent::pre::*;
use crate::agent::tagres::*;
use crate::agent::ents::*;
use crate::agent::groups::*;
use crate::agent::scan::*;
use crate::agent::fold::*;
use crate::agent::group::g_row;
use crate::agent::topk::*;
use crate::agent::answer::*;
use crate::agent::drive::*;
use crate::agent::rows::*;

pub mod common;
pub mod cols;
pub mod nf;
pub mod sub;
pub mod pre;
pub mod tagres;
pub mod ents;
pub mod groups;
pub mod scan;
pub mod fold;
pub mod sem;
pub mod join;
pub mod decomp;
pub mod group;
pub mod topk;
pub mod answer;
pub mod drive;
pub mod rows;

verus! {

/// The binding of the parameters is the context's.
proof fn lemma_lits(c: Ctx, ps: Seq<Literal>, params: &Params)
    requires
        crate::query::param_domain(ps), ps == params@,
        c.uom == params.p0@, c.stmt == params.p1@, c.lo == params.p2 as int, c.hi == params.p3 as int,
    ensures crate::agent::sem::lits_ok(c, ps),
{
    assert(ps[2] == (Literal::Int { v: params.p2 as int, kind: IntKind::Int4 }));
    assert(ps[3] == (Literal::Int { v: params.p3 as int, kind: IntKind::Int4 }));
}

/// Every database bound to the parts has the context's tables (the stored relations are determined by the parts).
proof fn lemma_every_db(sv: crate::gendb_entry::stores::StoresView, db: Database, db2: Database, c: Ctx)
    requires
        crate::gendb_entry::bound_db(sv, db), crate::gendb_entry::bound_db(sv, db2), rels_ok(sv, db, c),
    ensures db_ok(db2, c),
{
    ni::lemma_represents_determines(sv.flat_num, crate::stores::flat_num::declaration::stored_relations(db),
        crate::stores::flat_num::declaration::stored_relations(db2));
    si::lemma_represents_determines(sv.flat_sub, crate::stores::flat_sub::declaration::stored_relations(db),
        crate::stores::flat_sub::declaration::stored_relations(db2));
    ti::lemma_represents_determines(sv.flat_tag, crate::stores::flat_tag::declaration::stored_relations(db),
        crate::stores::flat_tag::declaration::stored_relations(db2));
    pi::lemma_represents_determines(sv.flat_pre, crate::stores::flat_pre::declaration::stored_relations(db),
        crate::stores::flat_pre::declaration::stored_relations(db2));
    lemma_bound(sv, db2, c);
}

/// Sample the first filter: `true` when the adsh bitmap rejects at least as many sampled rows as `uom = $1`.
fn adsh_first(k: &Cols, sx: &SubIndex, uom: &[u8], uom_len: usize, Ghost(c): Ghost<Ctx>) -> bool
    requires cols_ok(k, c), ctx_ok(c), sub_index_ok(sx, c), uom@ == c.uom, uom_len == uom@.len(),
{
    proof {
        lemma_views(c);
    }
    let n = k.n_val.len();
    if n == 0 {
        return true;
    }
    let lim: usize = if n < 4096 { n } else { 4096 };
    let step = n / lim;
    let mut su: usize = 0;
    let mut sa: usize = 0;
    let mut q: usize = 0;
    while q < lim
        invariant
            cols_ok(k, c), ctx_ok(c), sub_index_ok(sx, c), n == c.n, lim <= n, step == n / lim, lim > 0, q <= lim,
            su <= q, sa <= q, uom_len == uom@.len(),
            text_wf(k.n_uom@, c.n), text_wf(k.n_adsh@, c.n),
        decreases lim - q,
    {
        proof {
            assert(q * step <= (lim - 1) * step) by (nonlinear_arith) requires q < lim, step >= 0;
            assert((lim - 1) * step < n) by (nonlinear_arith) requires step == n / lim, lim > 0, lim <= n;
        }
        let i = q * step;
        let (u, ul) = text_val(&k.n_uom, i, Ghost(c.n));
        if bytes_eq(u, ul, uom, uom_len) {
            su = su + 1;
        }
        let (a, al) = text_val(&k.n_adsh, i, Ghost(c.n));
        let h = text_hash(0, a, al);
        if may_contain(&sx.chains, h) {
            sa = sa + 1;
        }
        q = q + 1;
    }
    sa <= su
}

/// The results of phases 1 to 5.
pub struct Run {
    pub cols: Cols,
    pub ents: Arc<Entries>,
    pub gr: Groups,
    pub recs: Ghost<Seq<Rec>>,
    pub fold: FoldOut,
}

pub open spec fn run_struct_ok(r: &Run, c: Ctx, ps: Seq<Literal>) -> bool {
    &&& cols_ok(&r.cols, c)
    &&& run_ok(c, ps, r.ents.list@, r.recs@, &r.gr, r.fold.order@, r.fold.seen@, r.fold.cnt@, r.fold.sum@, r.fold.ovf@,
        r.fold.dcnt@, r.fold.pseen@)
}

/// The results of phases 1 to 3.
pub struct Front {
    pub cols: Cols,
    pub sx: Arc<SubIndex>,
    pub ents: Entries,
    pub gr: Groups,
}

pub open spec fn front_ok(r: &Front, c: Ctx) -> bool {
    &&& cols_ok(&r.cols, c) && sub_index_ok(&*r.sx, c) && ents_index_ok(&r.ents, c)
    &&& groups_ok(c, r.ents.list@, &r.gr)
    &&& r.ents.list@.len() < crate::agent::common::chains::NONE
    &&& c.n < usize::MAX
}

/// Phases 1 to 3: the sub index, the candidate pre rows, their tag rows, the entries and their groups.
fn front(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch, np: usize, nt: usize,
    Ghost(c): Ghost<Ctx>) -> (r: Result<Front, crate::gendb_entry::runtime::WorkerFailure>)
    requires
        ctx_ok(c), 1 <= workers <= MAX_WORKERS,
        c.np == old(stores)@.flat_num, c.sp == old(stores)@.flat_sub, c.tp == old(stores)@.flat_tag, c.pp == old(stores)@.flat_pre,
        c.nt == nt as int, c.npre == np as int,
        c.stmt == params.p1@, c.lo == params.p2 as int, c.hi == params.p3 as int,
    ensures r matches Ok(x) ==> front_ok(&x, c),
{
    let k = read_cols(stores, Ghost(c));
    proof {
        lemma_sizes(&k, c);
        lemma_views(c);
    }
    let stmt_len = params.p1.len();
    // 1. The selected sub rows.
    let sx = Arc::new(build_sub(&k, params.p2, params.p3, Ghost(c)));
    // 2. The candidate pre rows.
    let pscan = PreScan {
        p_adsh: tc(&k.p_adsh), p_stmt: tc(&k.p_stmt), p_stmtv: k.p_stmtv, p_tag: tc(&k.p_tag), p_ver: tc(&k.p_ver),
        stmt: params.p1, stmt_len, sx: sx.clone(),
    };
    proof {
        reveal(pre_scan_ok);
    }
    let cands = match run_pre(&pscan, np, workers, dispatch, Ghost(c)) {
        Ok(v) => v,
        Err(e) => return Err(e),
    };
    // 3. Their tag rows; the entries, their index and group ids.
    let cx = Arc::new(build_cands(cands, &k.p_tag, &k.p_ver, Ghost(c)));
    let sl = Arc::new(build_slots(&*cx));
    let tscan = TagScan { t_tag: tc(&k.t_tag), t_ver: tc(&k.t_ver), t_abs: k.t_abs, sl: sl.clone() };
    proof {
        reveal(tag_scan_ok);
    }
    let hits = match run_tag(&tscan, nt, workers, dispatch, Ghost(c)) {
        Ok(v) => v,
        Err(e) => return Err(e),
    };
    let tvrow = slot_rows(&*sl, &hits, Ghost(c));
    let vs = VerScan {
        cx: cx.clone(), sl: sl.clone(), tvrow: Arc::new(tvrow), hits: Arc::new(hits), t_tag: tc(&k.t_tag),
        t_ver: tc(&k.t_ver),
    };
    proof {
        reveal(ver_scan_ok);
    }
    let tagrow = match run_ver(&vs, workers, dispatch, Ghost(c)) {
        Ok(v) => v,
        Err(e) => return Err(e),
    };
    let ex = build_entries(&*cx, &tagrow, &k.t_tag, &k.t_ver, Ghost(c));
    let kc = KeyCols { s_sic: k.s_sic, s_cik: k.s_cik, t_label: tc(&k.t_label), t_labelv: k.t_labelv };
    proof {
        assert(ex.list@.len() < crate::agent::common::chains::NONE) by {
            assert(ex.chains.hashes@.len() == ex.list@.len());
        }
    }
    let gr = build_groups(&kc, &ex.list, nt, Ghost(c));
    Ok(Front { cols: k, sx, ents: ex, gr })
}

/// Phases 4 and 5: the contribution records and the GROUP BY fold over them.
fn back(fr: Front, params: &Params, workers: usize, dispatch: &mut Dispatch, n: usize, Ghost(c): Ghost<Ctx>,
    Ghost(ps): Ghost<Seq<Literal>>) -> (r: Result<Run, crate::gendb_entry::runtime::WorkerFailure>)
    requires
        front_ok(&fr, c), ctx_ok(c), crate::agent::sem::lits_ok(c, ps), 1 <= workers <= MAX_WORKERS, c.n == n as int,
        c.uom == params.p0@,
    ensures r matches Ok(x) ==> run_struct_ok(&x, c, ps),
{
    let Front { cols: k, sx, ents: ex, gr } = fr;
    let ghost ents = ex.list@;
    proof {
        lemma_views(c);
    }
    let uom_len = params.p0.len();
    let exa = Arc::new(ex);
    let first = adsh_first(&k, &*sx, params.p0, uom_len, Ghost(c));
    let nscan = NumScan {
        n_uom: tc(&k.n_uom), n_adsh: tc(&k.n_adsh), n_tag: tc(&k.n_tag), n_ver: tc(&k.n_ver), n_val: k.n_val,
        uom: params.p0, uom_len, sx: sx.clone(), ex: exa.clone(), adsh_first: first,
    };
    proof {
        reveal(num_scan_ok);
    }
    let segs = match run_scan(&nscan, n, workers, dispatch, Ghost(c)) {
        Ok(v) => bound_segs(v),
        Err(e) => return Err(e),
    };
    let ghost recs = flat(segs@);
    proof {
        crate::agent::group::lemma_contrib_mem(c, ents, 0, c.n);
        assert(recs_ok(ents, recs)) by {
            assert forall|q: int| 0 <= q < recs.len() implies ((#[trigger] recs[q]).1 as int) < ents.len() by {}
        }
    }
    let f = fold(&segs, &gr, Ghost(c), Ghost(ents));
    proof {
        reveal(run_ok);
    }
    Ok(Run { cols: k, ents: exa, gr, recs: Ghost(recs), fold: f })
}

/// Every database bound to the parts has the context's tables.
pub open spec fn all_bound_ok(sv: crate::gendb_entry::stores::StoresView, c: Ctx) -> bool {
    forall|db2: Database| #[trigger] crate::gendb_entry::bound_db(sv, db2) ==> db_ok(db2, c)
}

/// Phase 5 (capacity check) and 6 (HAVING, ORDER BY, LIMIT): the answer.
fn finish(x: &Run, params: &Params, Ghost(c): Ghost<Ctx>, Ghost(ps): Ghost<Seq<Literal>>,
    Ghost(sv): Ghost<crate::gendb_entry::stores::StoresView>) -> (r: Answer)
    requires run_struct_ok(x, c, ps), all_bound_ok(sv, c), c.stmt == params.p1@, ps == params@,
    ensures crate::gendb_entry::answer_meets(sv, ps, Ok::<Answer, QueryError>(r)),
{
    let f = &x.fold;
    let gr = &x.gr;
    let ghost ents = x.ents.list@;
    proof {
        lemma_run_facts(c, ps, ents, x.recs@, gr, f.order@, f.seen@, f.cnt@, f.sum@, f.ovf@, f.dcnt@, f.pseen@);
    }
    // Capacity: a sum beyond `i128` or an average outside the division domain.
    let no = f.order.len();
    let mut y: usize = 0;
    while y < no
        invariant
            run_struct_ok(x, c, ps), f == &x.fold, gr == &x.gr, no == f.order@.len(), y <= no, all_bound_ok(sv, c),
            ents == x.ents.list@,
            f.ovf@.len() == gr.reps@.len(), f.sum@.len() == gr.reps@.len(), f.cnt@.len() == gr.reps@.len(),
            forall|w: int| 0 <= w < f.order@.len() ==> (#[trigger] f.order@[w] as int) < gr.reps@.len(),
            forall|w: int| 0 <= w < y ==> !f.ovf@[#[trigger] f.order@[w] as int]
                && crate::spec::fns::div::num_div_fits(f.sum@[f.order@[w] as int] as int, 4, f.cnt@[f.order@[w] as int] as int, 0),
        decreases no - y,
    {
        let g = f.order[y];
        let bad = if f.ovf[g] {
            true
        } else {
            match exec_avg_finalize(f.sum[g], 4, f.cnt[g] as u64) {
                Ok(_) => false,
                Err(_) => true,
            }
        };
        if bad {
            proof {
                assert forall|db2: Database| #[trigger] crate::gendb_entry::bound_db(sv, db2) implies
                    crate::gendb_entry::outcome_ok(db2, crate::query::query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity)) by {
                    lemma_capacity(db2, c, ps, ents, x.recs@, gr, f.order@, f.seen@, f.cnt@, f.sum@, f.ovf@, f.dcnt@, f.pseen@, y as int);
                }
            }
            return Answer::Capacity;
        }
        y = y + 1;
    }
    // 6. HAVING, ORDER BY sum DESC, LIMIT 500: a threshold near the 500th largest sum.
    let mut hs: Vec<i128> = Vec::new();
    let mut w: usize = 0;
    while w < no
        invariant
            f == &x.fold, no == f.order@.len(), w <= no, f.sum@.len() == gr.reps@.len(), f.dcnt@.len() == gr.reps@.len(),
            forall|v: int| 0 <= v < f.order@.len() ==> (#[trigger] f.order@[v] as int) < gr.reps@.len(),
        decreases no - w,
    {
        let g = f.order[w];
        if f.dcnt[g] >= 2 {
            hs.push(f.sum[g]);
        }
        w = w + 1;
    }
    let mut t: i128 = i128::MIN;
    if hs.len() > 500 {
        t = kth_largest(&hs, 500);
    }
    let mut cand = select_cands(&f.order, &f.sum, &f.dcnt, t);
    if cand.len() < 500 && t != i128::MIN {
        t = i128::MIN;
        cand = select_cands(&f.order, &f.sum, &f.dcnt, t);
    }
    proof {
        lemma_filt_mem(f.order@, cand_at(f.dcnt@, f.sum@, t as int));
        assert forall|q: int| 0 <= q < cand@.len() implies (#[trigger] cand@[q] as int) < f.sum@.len() by {
            assert(f.order@.contains(cand@[q]));
        }
    }
    let pos = sort_positions(&cand, &f.sum, Ghost(c), Ghost(gr.reps@), Ghost(f.cnt@), Ghost(f.dcnt@));
    let lim: usize = if cand.len() < 500 { cand.len() } else { 500 };
    let ghost sorted = crate::spec::order::sort_rows(crate::agent::sem::order_keys(), grows(c, gr.reps@, f.sum@, f.cnt@, f.dcnt@, cand@));
    let stmt_len = params.p1.len();
    let mut out: Vec<Vec<EVal>> = Vec::new();
    let mut q: usize = 0;
    proof {
        lemma_views(c);
        assert(view_rows(out@) =~= sorted.take(0));
    }
    while q < lim
        invariant
            f == &x.fold, gr == &x.gr, run_struct_ok(x, c, ps), ctx_ok(c), reps_ok(c, gr.reps@), all_bound_ok(sv, c),
            ents == x.ents.list@,
            q <= lim, lim <= cand@.len(), cand@ == filt(f.order@, cand_at(f.dcnt@, f.sum@, t as int)),
            pos@.len() == cand@.len(), forall|v: int| 0 <= v < pos@.len() ==> #[trigger] pos@[v] < cand@.len(),
            ordered_view(grows(c, gr.reps@, f.sum@, f.cnt@, f.dcnt@, cand@), pos@) == sorted,
            forall|v: int| 0 <= v < cand@.len() ==> f.order@.contains(#[trigger] cand@[v]),
            forall|v: int| 0 <= v < no ==> !f.ovf@[#[trigger] f.order@[v] as int]
                && crate::spec::fns::div::num_div_fits(f.sum@[f.order@[v] as int] as int, 4, f.cnt@[f.order@[v] as int] as int, 0),
            no == f.order@.len(), stmt_len == params.p1@.len(), c.stmt == params.p1@,
            text_wf(x.cols.t_label@, c.nt), x.cols.t_labelv@.len() == c.nt, x.cols.s_sic@.len() == c.m,
            f.cnt@.len() == gr.reps@.len() && f.sum@.len() == gr.reps@.len() && f.dcnt@.len() == gr.reps@.len(),
            forall|v: int| 0 <= v < f.order@.len() ==> (#[trigger] f.order@[v] as int) < gr.reps@.len(),
            forall|g: int| 0 <= g < gr.reps@.len() ==> #[trigger] f.dcnt@[g] <= 0x1_0000_0000,
            view_rows(out@) == sorted.take(q as int),
        decreases lim - q,
    {
        let g = cand[pos[q]];
        proof {
            assert(f.order@.contains(g));
            let wi = choose|wi: int| 0 <= wi < f.order@.len() && f.order@[wi] == g;
            lemma_ordered_at(grows(c, gr.reps@, f.sum@, f.cnt@, f.dcnt@, cand@), pos@, q as int);
        }
        let row = out_row(&x.cols, params.p1, stmt_len, gr, &f.sum, &f.cnt, &f.dcnt, g, Ghost(c));
        let ghost o0 = out@;
        out.push(row);
        proof {
            assert(view_rows(out@) =~= view_rows(o0).push(view_row(row@)));
            assert(sorted.take(q + 1) =~= sorted.take(q as int).push(sorted[q as int]));
        }
        q = q + 1;
    }
    proof {
        assert forall|db2: Database| #[trigger] crate::gendb_entry::bound_db(sv, db2) implies
            crate::gendb_entry::outcome_ok(db2, crate::query::query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(out))) by {
            lemma_body(db2, c, ps, ents, x.recs@, gr, f.order@, f.seen@, f.cnt@, f.sum@, f.ovf@, f.dcnt@, f.pseen@);
            assert(view_rows(out@) == sorted.take(lim as int));
            lemma_answer(db2, c, ps, gr.reps@, f.order@, f.sum@, f.cnt@, f.dcnt@, t as int, view_rows(out@));
        }
    }
    Answer::Rows(out)
}

#[verifier::spinoff_prover]
pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        crate::gendb_entry::stores_ready(old(stores)@),
        crate::query::param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures
        crate::gendb_entry::answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    let ghost ps = params@;
    let ghost db = choose|db: Database| #[trigger] crate::gendb_entry::bound_db(stores@, db);
    let ghost nrels = crate::stores::flat_num::declaration::stored_relations(db);
    let ghost srels = crate::stores::flat_sub::declaration::stored_relations(db);
    let ghost trels = crate::stores::flat_tag::declaration::stored_relations(db);
    let ghost prels = crate::stores::flat_pre::declaration::stored_relations(db);
    let n = ni::stored_rows(&stores.flat_num, Ghost(nrels));
    let m = si::stored_rows(&stores.flat_sub, Ghost(srels));
    let nt = ti::stored_rows(&stores.flat_tag, Ghost(trels));
    let np = pi::stored_rows(&stores.flat_pre, Ghost(prels));
    let ghost c = Ctx {
        np: stores.flat_num@, n: n as int, sp: stores.flat_sub@, m: m as int, tp: stores.flat_tag@, nt: nt as int,
        pp: stores.flat_pre@, npre: np as int, uom: params.p0@, stmt: params.p1@, lo: params.p2 as int, hi: params.p3 as int,
    };
    proof {
        lemma_bound(sv, db, c);
        lemma_lits(c, ps, params);
        assert forall|db2: Database| #[trigger] crate::gendb_entry::bound_db(sv, db2) implies db_ok(db2, c) by {
            lemma_every_db(sv, db, db2, c);
        }
    }
    let fr = match front(stores, params, workers, dispatch, np, nt, Ghost(c)) {
        Ok(x) => x,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    proof {
        lemma_views(c);
        assert(c.n < usize::MAX);
    }
    let x = match back(fr, params, workers, dispatch, n, Ghost(c), Ghost(ps)) {
        Ok(x) => x,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    Ok(finish(&x, params, Ghost(c), Ghost(ps), Ghost(sv)))
}

} // verus!
