//! The claim from the parts' outcome: for every database bound to the parts, the statement's body is `sl_outcome`
//! (`lemma_denote`), so a columnar answer of its rows in s_name order (`lemma_ok_columns`), the sorted rows
//! (`lemma_ok_rows`) or its error (`lemma_err`) meets `answer_meets`. `lemma_flags`: the merged task flags are
//! exactly the qualifying supplier rows.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::order::*;
use crate::gendb_entry::{Answer, answer_meets, bound_db, outcome_ok};
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::results::*;
use crate::gendb_entry::parallel::WorkerTask;
use crate::exec::value::ERow;
use crate::link::query::view_rows;
use crate::query::{param_domain, query_spec_at};
use crate::stores::part_nameidx::interface as pi;
use crate::stores::li_pkdate::interface as li;
use super::nf::*;
use super::ast::*;
use super::bind_sp::*;
use super::bind_pl::*;
use super::sl::*;
use super::pfind::hit_row;
use super::kern::*;
use super::run::flagged;
use super::bits::bit;

verus! {

/// For a database bound to the parts, the body's meaning is the parts' outcome.
pub proof fn lemma_denote(sv: StoresView, db: Database, ps: Seq<Literal>, d1: int)
    requires bound_db(sv, db), param_domain(ps), d1_ok(ps, d1),
    ensures
        denote_body(db, query_spec_at(ps)) == sl_outcome(sv, ps, d1),
        query_spec_at(ps).keys == q_keys(),
        query_spec_at(ps).offset == 0,
        query_spec_at(ps).limit is None,
{
    lemma_bound(sv, db);
    lemma_query_shape(ps);
    assert(lt(db).len() == li::n_rows(sv.li_pkdate));
    assert(super::sem_ps::sem_ok(db, ps, d1));
    super::sem_top::lemma_body(db, ps, d1);
    lemma_sl_outcome(sv, db, ps, d1);
}

/// The rows of the parts' outcome, in s_name order, as columns.
pub proof fn lemma_ok_columns(sv: StoresView, ps: Seq<Literal>, d1: int, c: ResultColumns)
    requires
        param_domain(ps), d1_ok(ps, d1),
        sl_outcome(sv, ps, d1) is Ok,
        columns_wf(c),
        columns_view(c) == sl_outcome(sv, ps, d1)->Ok_0,
        sorted_by(q_keys(), columns_view(c)),
    ensures answer_meets(sv, ps, Ok::<Answer, crate::gendb_entry::runtime::QueryError>(Answer::Columns(c))),
{
    let rs = columns_view(c);
    assert forall|db: Database| #[trigger] bound_db(sv, db)
        implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, crate::gendb_entry::runtime::QueryError>(Answer::Columns(c))) by {
        lemma_denote(sv, db, ps, d1);
        let oq = query_spec_at(ps);
        crate::link::outcome::lemma_outcome_sorted(db, oq, rs, rs);
        assert(slice_rows(rs, oq.offset, oq.limit) =~= rs);
    }
}

/// The rows of the parts' outcome, sorted by s_name.
pub proof fn lemma_ok_rows(sv: StoresView, ps: Seq<Literal>, d1: int, out: Vec<ERow>)
    requires
        param_domain(ps), d1_ok(ps, d1),
        sl_outcome(sv, ps, d1) is Ok,
        view_rows(out@).to_multiset() == (sl_outcome(sv, ps, d1)->Ok_0).to_multiset(),
        sorted_by(q_keys(), view_rows(out@)),
    ensures answer_meets(sv, ps, Ok::<Answer, crate::gendb_entry::runtime::QueryError>(Answer::Rows(out))),
{
    let p = view_rows(out@);
    assert forall|db: Database| #[trigger] bound_db(sv, db)
        implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, crate::gendb_entry::runtime::QueryError>(Answer::Rows(out))) by {
        lemma_denote(sv, db, ps, d1);
        let oq = query_spec_at(ps);
        crate::link::outcome::lemma_outcome_sorted(db, oq, sl_outcome(sv, ps, d1)->Ok_0, p);
        assert(slice_rows(p, oq.offset, oq.limit) =~= p);
    }
}

/// The parts' outcome is an error.
pub proof fn lemma_err(sv: StoresView, ps: Seq<Literal>, d1: int)
    requires param_domain(ps), d1_ok(ps, d1), sl_outcome(sv, ps, d1) is Err,
    ensures answer_meets(sv, ps, Ok::<Answer, crate::gendb_entry::runtime::QueryError>(Answer::SqlError(sl_outcome(sv, ps, d1)->Err_0))),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db)
        implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, crate::gendb_entry::runtime::QueryError>(Answer::SqlError(sl_outcome(sv, ps, d1)->Err_0))) by {
        lemma_denote(sv, db, ps, d1);
    }
}

/// What the calling thread knows of task `w` and its output.
pub open spec fn task_done(t: PartTask, e: Emit, sv: StoresView, ps: Seq<Literal>, d1: int, ns: int, nps: int) -> bool {
    &&& t.post(e)
    &&& t.ctx.sv@ == sv && t.ctx.ps@ == ps && t.ctx.d1g@ == d1
    &&& t.ctx.ns == ns && t.ctx.nps == nps
}

/// Part row `r` is in task `t`'s list.
pub open spec fn in_task(t: PartTask, r: int) -> bool {
    exists|i: int| 0 <= i < t.lst().len() && #[trigger] t.lst()[i] == r
}

/// Some task's list holds part row `r`.
pub open spec fn covered_by(ts: Seq<PartTask>, r: int) -> bool {
    exists|w: int| 0 <= w < ts.len() && #[trigger] in_task(ts[w], r)
}

/// The merged flags of the tasks are the qualifying supplier rows: every flagged row qualifies, and a qualifying row
/// is flagged by the task whose part rows hold a matching part of its partsupp row.
pub proof fn lemma_flags(sv: StoresView, ps: Seq<Literal>, d1: int, ts: Seq<PartTask>, outs: Seq<Emit>, x: int)
    requires
        sl_ok(sv),
        ts.len() == outs.len(),
        forall|w: int| 0 <= w < ts.len() ==> #[trigger] task_done(ts[w], outs[w], sv, ps, d1, tn(sv.suppliers, 13), tn(sv.suppliers, 0)),
        forall|w: int| 0 <= w < outs.len() ==> !lost(#[trigger] outs[w]),
        forall|r: int| 0 <= r < pi::n_rows(sv.part_nameidx) && #[trigger] hit_row(sv.part_nameidx, pat_of(ps), r)
            ==> covered_by(ts, r),
        0 <= x < tn(sv.suppliers, 13),
    ensures flagged(outs, outs.len() as int, x) == sl_s_qual(sv, ps, d1, x),
{
    let sp = sv.suppliers;
    let pp = sv.part_nameidx;
    let (pat, d0) = (pat_of(ps), d0_of(ps));
    if flagged(outs, outs.len() as int, x) {
        let w = choose|w: int| 0 <= w < outs.len() && #[trigger] has(outs[w], x);
        assert(task_done(ts[w], outs[w], sv, ps, d1, tn(sp, 13), tn(sp, 0)));
        assert(ts[w].post(outs[w]));
        assert(outs[w].sound(sv, ps, d1, tn(sp, 13)));
    }
    if sl_s_qual(sv, ps, d1, x) {
        let j = choose|j: int| 0 <= j < tn(sp, 0) && #[trigger] sl_ps_qual(sv, pat, d0, d1, j) && pss(sp, j) == suk(sp, x);
        let k = psk(sp, j);
        let r = choose|r: int| 0 <= r < pi::n_rows(pp) && pi::pkey_at(pp, r) == k && #[trigger] like_hit(pi::name_at(pp, r), pat);
        assert(hit_row(pp, pat, r));
        assert(covered_by(ts, r));
        let w = choose|w: int| 0 <= w < ts.len() && #[trigger] in_task(ts[w], r);
        assert(task_done(ts[w], outs[w], sv, ps, d1, tn(sp, 13), tn(sp, 0)));
        let t = ts[w];
        let i = choose|i: int| 0 <= i < t.lst().len() && #[trigger] t.lst()[i] == r;
        assert(t.post(outs[w]));
        assert(t.ctx.pp() == pp && t.ctx.pat() == pat && t.ctx.sp() == sp);
        assert(0 <= j < t.ctx.nps);
        assert(pi::pkey_at(pp, t.lst()[i] as int) == k);
        assert(hitl(t.ctx.pp(), t.lst(), psk(t.ctx.sp(), j)));
        assert(jdone(t.ctx.sv@, t.ctx.ps@, t.ctx.d1g@, outs[w], j));
        assert(jdone(sv, ps, d1, outs[w], j));
        assert(!lost(outs[w]));
        assert(has(outs[w], x));
        assert(flagged(outs, outs.len() as int, x));
    }
}

} // verus!
