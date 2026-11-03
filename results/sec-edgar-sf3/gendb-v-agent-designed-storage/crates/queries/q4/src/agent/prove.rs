//! The claim for every database bound to the parts: the stage results make the context (`cx_ok`) and the
//! aggregation inputs (`ag_ok`) hold, and the answer is then an allowed outcome (`lemma_answer_rows`,
//! `lemma_answer_cap`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::schema::schema_spec;
use crate::spec::typing::db_wf;
use crate::exec::value::EVal;
use crate::link::query::view_rows;
use crate::link::join::keep;
use crate::gendb_entry::{Answer, bound_db, outcome_ok, capacity_domain};
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::runtime::QueryError;
use crate::query::query_spec_at;
use crate::stores::num::interface as N;
use crate::stores::pre::interface as P;
use crate::stores::sub_sic::interface as S;
use crate::stores::tag_tv::interface as T;
use crate::agent::mapfacts::tvi;
use crate::agent::pairs::*;
use crate::agent::sem::*;
use crate::agent::group::*;
use crate::agent::levels::*;
use crate::agent::filing::*;
use crate::agent::filings::*;
use crate::agent::join::*;
use crate::agent::agg::*;
use crate::agent::result::*;
use crate::agent::inputs::*;
use crate::agent::pipeline::*;

verus! {

/// The layouts of the parts (from any bound database).
pub proof fn lemma_layouts(sv: StoresView)
    requires exists|db: Database| #[trigger] bound_db(sv, db),
    ensures N::num_layout_ok(sv.num), P::pre_layout_ok(sv.pre), T::tag_layout_ok(sv.tag_tv), S::sub_layout_ok(sv.sub_sic),
{
    let db = choose|db: Database| #[trigger] bound_db(sv, db);
    lemma_rels(db);
}

/// The stage results of one call (database free).
pub open spec fn stages_ok(sv: StoresView, cx: Cx, nin: NumIn, pin: PreIn, tin: TagIn, sin: SubIn, fil: Seq<u64>,
    fs: Seq<i32>, fc: Seq<i32>, look: Seq<(u64, u64, u64)>) -> bool
{
    &&& cx == mk_cx(cx.b0, cx.b1, cx.lo, cx.hi, sv.num, sv.sub_sic, sv.tag_tv, sv.pre, cx.u, cx.sc, fil, look)
    &&& num_in_ok(sv.num, nin) && pre_in_ok(sv.pre, pin) && tag_in_ok(sv.tag_tv, tin) && sub_in_ok(sv.sub_sic, sin)
    &&& sc_ok(sv.pre, cx.b1, cx.sc)
    &&& fil_ok(sin, cx.lo, cx.hi, fil, fs, fc)
    &&& look.len() == fil.len()
    &&& forall|f: int| 0 <= f < fil.len() ==>
            lk_ok(sv.num, sv.pre, cx.b0, cx.u, cx.sc, text_entry_s(sin, fil[f] as int), #[trigger] look[f])
}

pub open spec fn text_entry_s(sin: SubIn, i: int) -> Seq<u8> {
    crate::stores::num::interface::common::text::text_entry(sin.adsh_off@, sin.adsh_bytes@, i)
}

/// Sub row `i` of a bound database: its adsh, cik, sic from the parts.
proof fn lemma_sub_row(db: Database, sv: StoresView, sin: SubIn, i: int)
    requires bound_db(sv, db), sub_in_ok(sv.sub_sic, sin), 0 <= i < sin.n,
    ensures
        db.tables[0].len() == sin.n,
        db.tables[0][i][0] == Val::Text(text_entry_s(sin, i)),
        db.tables[0][i][1] == Val::Int(sin.cik@[i] as int),
        db.tables[0][i][3] == if sin.sicv@[i] == 0 { Val::Null } else { Val::Int(sin.sic@[i] as int) },
{
    lemma_rels(db);
    assert(S::represents(sv.sub_sic, seq![db.tables[0]]));
    assert(S::sub_row_ok(sv.sub_sic, db.tables[0][i], i));
}

/// The context's facts on a bound database.
pub proof fn lemma_cx_ok(db: Database, sv: StoresView, cx: Cx, nin: NumIn, pin: PreIn, tin: TagIn, sin: SubIn, fil: Seq<u64>,
    fs: Seq<i32>, fc: Seq<i32>, look: Seq<(u64, u64, u64)>)
    requires bound_db(sv, db), stages_ok(sv, cx, nin, pin, tin, sin, fil, fs, fc, look),
    ensures
        cx_ok(db, cx),
        forall|f: int| 0 <= f < cx.fil.len() ==> #[trigger] fs[f] as int == sic_of(db, cx, f) && fc[f] as int == cik_of(db, cx, f),
{
    hide(N::num_layout_ok);
    hide(P::pre_layout_ok);
    hide(T::tag_layout_ok);
    hide(S::sub_layout_ok);
    lemma_rels(db);
    let nf = fil.len() as int;
    assert(db.tables[0].len() == sin.n) by {
        assert(S::represents(sv.sub_sic, seq![db.tables[0]]));
    }
    assert forall|q: int| 0 <= q < P::pair_count(cx.pre) implies
        pair_found(cx.num, ptag(cx, q), pver(cx, q), #[trigger] cx.t3[q]) && tag_found(cx.tag, ptag(cx, q), pver(cx, q), cx.t6[q]) by {
        reveal(N::num_layout_ok);
        reveal(T::tag_layout_ok);
        assert(ptag(cx, q) == pq_tag(sv.pre, q) && pver(cx, q) == pq_ver(sv.pre, q));
        lemma_t3c_found(sv.num, pq_tag(sv.pre, q), pq_ver(sv.pre, q));
        lemma_t6c_found(sv.tag_tv, pq_tag(sv.pre, q), pq_ver(sv.pre, q));
    }
    assert(cx.fil.no_duplicates()) by {
        assert forall|a: int, b: int| 0 <= a < b < nf implies cx.fil[a] != cx.fil[b] by {
            assert(fil[a] != fil[b]);
        }
    }
    assert forall|f: int| 0 <= f < nf implies 0 <= #[trigger] cx.fil[f] < db.tables[0].len() && sub_qual(cx, srow_of(db, cx, f))
        && fs[f] as int == sic_of(db, cx, f) && fc[f] as int == cik_of(db, cx, f)
        && run_found(cx.num, cx.b0, adsh_of(db, cx, f), cx.u, cx.runs[f])
        && (cx.runs[f] >= 0 ==> pre_found(cx.pre, adsh_of(db, cx, f), cx.b1, cx.pcs[f], cx.sc)) by {
        let i = fil[f] as int;
        assert(fil[f] < sin.n && squal(sin.sic@, sin.sicv@, cx.lo, cx.hi, i));
        lemma_sub_row(db, sv, sin, i);
        assert(adsh_of(db, cx, f) == text_entry_s(sin, i));
        assert(lk_ok(sv.num, sv.pre, cx.b0, cx.u, cx.sc, text_entry_s(sin, i), look[f]));
    }
    assert forall|i: int| 0 <= i < db.tables[0].len() && sub_qual(cx, #[trigger] db.tables[0][i]) implies cx.fil.contains(i) by {
        lemma_sub_row(db, sv, sin, i);
        assert(squal(sin.sic@, sin.sicv@, cx.lo, cx.hi, i));
        assert(fil.contains(i as u64));
        let f = choose|f: int| 0 <= f < fil.len() && fil[f] == i as u64;
        assert(cx.fil[f] == i);
    }
    reveal(N::num_layout_ok);
    reveal(P::pre_layout_ok);
    reveal(T::tag_layout_ok);
    reveal(S::sub_layout_ok);
}

/// A row answer: the sorted permutation `p` of the emitted groups' rows, sliced.
pub proof fn lemma_answer_rows(db: Database, ps: Seq<Literal>, cx: Cx, cs: Seq<Contrib>, fs: Seq<i32>, fc: Seq<i32>,
    gs: Seq<Grp>, p: Seq<Row>, out: Seq<Vec<EVal>>)
    requires
        res_pre(db, cx, cs, fs, fc, gs),
        ps == ps_of(cx.b0, cx.b1, cx.lo, cx.hi), bind_ok(cx.lo, cx.hi),
        p.to_multiset() == grp_rows(cx, gs).to_multiset(),
        sorted_by(order_keys(), p),
        view_rows(out) == slice_rows(p, 0, Some(500nat)),
    ensures ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(view_rows(out))),
{
    lemma_result_rows(db, cx, cs, fs, fc, gs);
    lemma_eval_having(db, cx.b0, cx.b1, cx.lo, cx.hi);
    lemma_query_parts(ps);
    let oq = query_spec_at(ps);
    let rows = keep(grows(qr(db, cx)), |r: Row| having_ok(r));
    assert(denote_body(db, oq) == Ok::<Relation, SqlError>(rows));
    crate::link::outcome::lemma_outcome_sorted(db, oq, rows, p);
}

/// A capacity answer.
pub proof fn lemma_answer_cap(db: Database, ps: Seq<Literal>, cx: Cx, cs: Seq<Contrib>, fs: Seq<i32>, fc: Seq<i32>, cap: Cap)
    requires
        ag_ok(db, cx, cs, fs, fc), cap_ok(fs, cs, cap),
        ps == ps_of(cx.b0, cx.b1, cx.lo, cx.hi), bind_ok(cx.lo, cx.hi),
    ensures !capacity_domain(db, query_spec_at(ps)),
{
    lemma_cap(db, cx, cs, fs, fc, cap);
    let k = key(cx, fs[cs[cap.k@].f as int] as int, cs[cap.k@].slot as int);
    lemma_group_capacity(db, cx.b0, cx.b1, cx.lo, cx.hi, k);
    lemma_query_parts(ps);
}

} // verus!
