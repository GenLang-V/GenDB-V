//! `ps_partkey IN (SELECT p_partkey FROM part WHERE p_name LIKE $1)`, evaluated with a 16-value context (the outer
//! row and a partsupp row) whose `ps_partkey` (position 11) is `a`:
//!
//! - `LIKE` of two texts is a Boolean or the matcher's error, and the matcher raises only 22025 (`lemma_like_res`,
//!   `lemma_like_err_kind`);
//! - when no part name's `LIKE` raises (`likes_ok`), the subquery's rows are `[p_partkey]` of the matching parts
//!   (`lemma_part_sub`) and the IN condition is `in_part(a)` (`lemma_in_part_pred`);
//! - otherwise the subquery, and so the IN condition, is the error 22025 (`lemma_in_part_pred_err`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::chars::*;
use crate::spec::fns::like::*;
use crate::spec::fns::apply_fn;
use crate::gendb_entry::stores::StoresView;
use crate::query::param_domain;
use crate::exec::relational::domain::*;
use crate::link::join::{keep, lemma_keep_members};
use crate::link::expr::tval;
use crate::link::capacity::{lemma_filter_err, lemma_first_input};
use crate::bridge::collect::{lemma_collect_all, lemma_collect_pointwise};
use crate::stores::flat_part::interface as pi;
use crate::agent::tables::*;
use crate::agent::ast::*;
use crate::agent::params::*;
use crate::agent::normal::*;
use crate::agent::common::rows::*;

verus! {

// ------------------------------------------------------------------------------------------------ LIKE values

/// The escape string has one character.
proof fn lemma_esc_chars()
    ensures chars(esc()).len() == 1,
{
    let b = esc();
    assert(b.drop_last() =~= Seq::<u8>::empty());
    assert(chars(b.drop_last()) == Seq::<Seq<u8>>::empty());
    assert(!is_cont(b.last()));
}

/// `LIKE` of two texts is a Boolean or the matcher's error.
pub proof fn lemma_like_res(name: Seq<u8>, pat: Seq<u8>)
    ensures like_ok(name, pat) ==> like_res(name, pat) == Ok::<Val, SqlError>(Val::Bool(like_true(name, pat))),
{
    lemma_esc_chars();
}

/// `like_end` never raises.
proof fn lemma_end_ok(p: Seq<LikeTok>, j: int)
    ensures like_end(p, j) is Ok,
    decreases p.len() - j,
{
    if 0 <= j < p.len() {
        if p[j] is Any {
            lemma_end_ok(p, j + 1);
        }
    }
}

/// `like_mt` raises only 22025.
proof fn lemma_mt_err(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int, j: int)
    ensures like_mt(t, p, i, j) is Err ==> like_mt(t, p, i, j) == Err::<LikeRes, SqlError>(SqlError::InvalidEscapeSequence),
    decreases p.len() - j, 0int, t.len() - i,
{
    if 0 <= i < t.len() && 0 <= j < p.len() {
        match p[j] {
            LikeTok::Dangling => {},
            LikeTok::Lit(c) => { if t[i] == c { lemma_mt_err(t, p, i + 1, j + 1); } },
            LikeTok::One => { lemma_mt_err(t, p, i + 1, j + 1); },
            LikeTok::Any => { lemma_any_err(t, p, i, j + 1); },
        }
    } else if 0 <= i < t.len() {
    } else {
        lemma_end_ok(p, j);
    }
}

/// `like_any` raises only 22025.
proof fn lemma_any_err(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int, j: int)
    ensures like_any(t, p, i, j) is Err ==> like_any(t, p, i, j) == Err::<LikeRes, SqlError>(SqlError::InvalidEscapeSequence),
    decreases p.len() - j, 2int, t.len() - i,
{
    if 0 <= j < p.len() {
        match p[j] {
            LikeTok::Any => { lemma_any_err(t, p, i, j + 1); },
            LikeTok::One => { if 0 <= i < t.len() { lemma_any_err(t, p, i + 1, j + 1); } },
            LikeTok::Dangling => {},
            LikeTok::Lit(_) => { lemma_scan_err(t, p, i, j); },
        }
    }
}

/// `like_scan` raises only 22025.
proof fn lemma_scan_err(t: Seq<Seq<u8>>, p: Seq<LikeTok>, k: int, j: int)
    ensures like_scan(t, p, k, j) is Err ==> like_scan(t, p, k, j) == Err::<LikeRes, SqlError>(SqlError::InvalidEscapeSequence),
    decreases p.len() - j, 1int, t.len() - k,
{
    if 0 <= k < t.len() {
        lemma_mt_err(t, p, k, j);
        if like_mt(t, p, k, j) == Ok::<LikeRes, SqlError>(LikeRes::NoMatch) {
            lemma_scan_err(t, p, k + 1, j);
        }
    }
}

/// `name LIKE pat` raises only 22025 (the escape string has one character, so the matcher decides).
pub proof fn lemma_like_err_kind(name: Seq<u8>, pat: Seq<u8>)
    ensures !like_ok(name, pat) ==> like_res(name, pat) == Err::<Val, SqlError>(SqlError::InvalidEscapeSequence),
{
    lemma_esc_chars();
    lemma_mt_err(chars(name), like_tokens(chars(pat), escape_of(chars(esc())), 0), 0, 0);
}

// ------------------------------------------------------------------------------------------------ one part row

/// Part row `p` as the evaluator sees it: arity, key, name.
pub proof fn lemma_part_row(sv: StoresView, p: int)
    requires stores_wf(sv), 0 <= p < n_p(sv),
    ensures ({
        let r = part_rows(sv)[p];
        &&& r == pi::row_at(sv.flat_part, p)
        &&& r.len() == 9
        &&& r[0] == Val::Int(pk(sv)[p] as int)
        &&& r[1] == Val::Text(pname(sv, p))
    }),
{
}

/// The `LIKE` call's arguments on an environment whose position 17 is the text `name`.
proof fn lemma_like_args(db: Database, env: Row, p0: Literal, pat: Seq<u8>, name: Seq<u8>)
    requires p0 == Literal::Text(pat), env.len() == 25, env[17] == Val::Text(name),
    ensures eval_exprs(db, env, seq![Expr::Col(17), Expr::Lit(p0), Expr::Lit(esc_lit())])
        == Ok::<Row, SqlError>(seq![Val::Text(name), Val::Text(pat), Val::Text(esc())]),
{
    let args = seq![Expr::Col(17), Expr::Lit(p0), Expr::Lit(esc_lit())];
    let vs = seq![Val::Text(name), Val::Text(pat), Val::Text(esc())];
    lemma_expr_results_index(db, env, args);
    let rs = expr_results(db, env, args);
    assert(eval_expr(db, env, Expr::Col(17)) == Ok::<Val, SqlError>(vs[0]));
    assert(eval_expr(db, env, Expr::Lit(p0)) == Ok::<Val, SqlError>(vs[1]));
    assert(eval_expr(db, env, Expr::Lit(esc_lit())) == Ok::<Val, SqlError>(vs[2]));
    assert(rs[0] == Ok::<Val, SqlError>(vs[0]));
    assert(rs[1] == Ok::<Val, SqlError>(vs[1]));
    assert(rs[2] == Ok::<Val, SqlError>(vs[2]));
    lemma_collect_all(rs, vs);
}

/// The `LIKE` call on an environment whose position 17 is the text `name`.
proof fn lemma_like_call(db: Database, env: Row, p0: Literal, pat: Seq<u8>, name: Seq<u8>)
    requires p0 == Literal::Text(pat), env.len() == 25, env[17] == Val::Text(name),
    ensures eval_expr(db, env, like_expr(p0)) == like_res(name, pat),
{
    hide(like_value);
    lemma_like_args(db, env, p0, pat, name);
    let args = seq![Expr::Col(17), Expr::Lit(p0), Expr::Lit(esc_lit())];
    let vs = seq![Val::Text(name), Val::Text(pat), Val::Text(esc())];
    assert(like_expr(p0) == Expr::Call { f: ScalarFn::Like, args });
    assert(apply_fn(ScalarFn::Like, vs) == like_res(name, pat));
    assert(eval_expr(db, env, Expr::Call { f: ScalarFn::Like, args }) == apply_fn(ScalarFn::Like, vs));
}

/// `p_name LIKE $1` as a condition: the truth of `like_true`, or the error 22025.
pub proof fn lemma_like_pred(db: Database, env: Row, ps: Seq<Literal>, name: Seq<u8>)
    requires param_domain(ps), env.len() == 25, env[17] == Val::Text(name),
    ensures
        like_ok(name, pat_of(ps)) ==> eval_pred(db, env, part_pred(ps[0])) == Ok::<Truth, SqlError>(truth_of(like_true(name, pat_of(ps)))),
        !like_ok(name, pat_of(ps)) ==> eval_pred(db, env, part_pred(ps[0])) == Err::<Truth, SqlError>(SqlError::InvalidEscapeSequence),
{
    lemma_param(ps);
    lemma_like_call(db, env, ps[0], pat_of(ps), name);
    lemma_like_res(name, pat_of(ps));
    lemma_like_err_kind(name, pat_of(ps));
}

// ------------------------------------------------------------------------------------------------ the subquery

/// The part rows the subquery's WHERE keeps (position 1 is the name).
pub open spec fn pf(pat: Seq<u8>) -> spec_fn(Row) -> bool { |r: Row| like_true(tval(r[1]), pat) }

/// The subquery's rows: `[p_partkey]` of every kept part row.
pub open spec fn part_out(sv: StoresView, ps: Seq<Literal>) -> Seq<Row> {
    keep(part_rows(sv), pf(pat_of(ps))).map_values(|r: Row| seq![r[0]])
}

/// The subquery's WHERE under a 16-value context, when no `LIKE` raises.
proof fn lemma_part_filter(db: Database, sv: StoresView, ps: Seq<Literal>, ctx: Row)
    requires tables_of(sv, db), stores_wf(sv), param_domain(ps), likes_ok(sv, ps), ctx.len() == 16,
    ensures eval_query(db, ctx, part_filter(ps[0])) == Ok::<Relation, SqlError>(keep(part_rows(sv), pf(pat_of(ps)))),
{
    let rows = part_rows(sv);
    let f = pf(pat_of(ps));
    let pred = part_pred(ps[0]);
    assert(eval_query(db, ctx, Query::Table(3)) == Ok::<Relation, SqlError>(rows));
    let truths = Seq::new(rows.len(), |i: int| truth_of(f(rows[i])));
    let prs = Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred));
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        lemma_part_row(sv, i);
        let e = ctx + rows[i];
        assert(e[17] == rows[i][1]);
        assert(like_ok(pname(sv, i), pat_of(ps)));
        lemma_like_pred(db, e, ps, pname(sv, i));
    }
    lemma_collect_all(prs, truths);
    lemma_collect_pointwise::<Truth>();
    crate::link::join::lemma_keep_true_keep(rows, truths, f);
}

/// The subquery under a 16-value context, when no `LIKE` raises: `part_out`.
pub proof fn lemma_part_sub(db: Database, sv: StoresView, ps: Seq<Literal>, ctx: Row)
    requires tables_of(sv, db), stores_wf(sv), param_domain(ps), likes_ok(sv, ps), ctx.len() == 16,
    ensures eval_query(db, ctx, part_sub(ps[0])) == Ok::<Relation, SqlError>(part_out(sv, ps)),
{
    let rows = part_rows(sv);
    let f = pf(pat_of(ps));
    let kept = keep(rows, f);
    lemma_part_filter(db, sv, ps, ctx);
    let es = seq![Expr::Col(16)];
    lemma_eval_project(db, ctx, es, Box::new(part_filter(ps[0])));
    let pr = project_results(db, ctx, kept, es);
    let out = part_out(sv, ps);
    lemma_keep_members(rows, f);
    assert forall|t: int| 0 <= t < pr.len() implies #[trigger] pr[t] == Ok::<Row, SqlError>(out[t]) by {
        assert(rows.contains(kept[t]));
        let p = choose|p: int| 0 <= p < rows.len() && rows[p] == kept[t];
        lemma_part_row(sv, p);
        let e = ctx + kept[t];
        assert(e[16] == kept[t][0]);
        let er = expr_results(db, e, es);
        lemma_expr_results_index(db, e, es);
        lemma_collect_all(er, seq![kept[t][0]]);
    }
    lemma_collect_all(pr, out);
}

/// The IN condition when no `LIKE` raises: `in_part(a)`.
pub proof fn lemma_in_part_pred(db: Database, sv: StoresView, ps: Seq<Literal>, ctx: Row, a: int)
    requires
        tables_of(sv, db), stores_wf(sv), param_domain(ps), likes_ok(sv, ps),
        ctx.len() == 16, ctx[11] == Val::Int(a),
    ensures eval_pred(db, ctx, ps_in_pred(ps[0])) == Ok::<Truth, SqlError>(truth_of(in_part(sv, ps, a))),
{
    let rows = part_rows(sv);
    let f = pf(pat_of(ps));
    let kept = keep(rows, f);
    let out = part_out(sv, ps);
    lemma_part_sub(db, sv, ps, ctx);
    assert(eval_expr(db, ctx, Expr::Col(11)) == Ok::<Val, SqlError>(Val::Int(a)));
    lemma_keep_members(rows, f);
    assert forall|t: int| 0 <= t < out.len() implies exists|w: int| #[trigger] out[t] == seq![Val::Int(w)] by {
        assert(rows.contains(kept[t]));
        let p = choose|p: int| 0 <= p < rows.len() && rows[p] == kept[t];
        lemma_part_row(sv, p);
        assert(out[t] == seq![Val::Int(pk(sv)[p] as int)]);
    }
    lemma_any_eq(a, out);
    let ex = exists|t: int| 0 <= t < out.len() && #[trigger] out[t] == seq![Val::Int(a)];
    if ex {
        let t = choose|t: int| 0 <= t < out.len() && #[trigger] out[t] == seq![Val::Int(a)];
        assert(rows.contains(kept[t]));
        let p = choose|p: int| 0 <= p < rows.len() && rows[p] == kept[t];
        lemma_part_row(sv, p);
        assert(out[t] == seq![kept[t][0]]);
        assert(seq![kept[t][0]][0] == seq![Val::Int(a)][0]);
        assert(pk(sv)[p] as int == a);
        assert(f(kept[t]));
        assert(pmatch(sv, ps, p));
        assert(in_part(sv, ps, a));
    }
    if in_part(sv, ps, a) {
        let p = choose|p: int| 0 <= p < n_p(sv) && #[trigger] pk(sv)[p] as int == a && pmatch(sv, ps, p);
        lemma_part_row(sv, p);
        assert(f(rows[p]));
        lemma_keep_has(rows, f, p);
        let t = choose|t: int| 0 <= t < kept.len() && kept[t] == rows[p];
        assert(out[t] == seq![kept[t][0]]);
        assert(out[t] =~= seq![Val::Int(a)]);
    }
}

/// The IN condition when some part name's `LIKE` raises: the error 22025.
pub proof fn lemma_in_part_pred_err(db: Database, sv: StoresView, ps: Seq<Literal>, ctx: Row)
    requires tables_of(sv, db), stores_wf(sv), param_domain(ps), !likes_ok(sv, ps), ctx.len() == 16,
    ensures eval_pred(db, ctx, ps_in_pred(ps[0])) == Err::<Truth, SqlError>(SqlError::InvalidEscapeSequence),
{
    let e = SqlError::InvalidEscapeSequence;
    let rows = part_rows(sv);
    let pred = part_pred(ps[0]);
    assert(eval_query(db, ctx, Query::Table(3)) == Ok::<Relation, SqlError>(rows));
    let p0 = choose|p: int| 0 <= p < n_p(sv) && !like_ok(#[trigger] pname(sv, p), pat_of(ps));
    assert forall|k: int| 0 <= k < rows.len() implies #[trigger] eval_pred(db, ctx + rows[k], pred) is Ok
        || eval_pred(db, ctx + rows[k], pred) == Err::<Truth, SqlError>(e) by {
        lemma_part_row(sv, k);
        assert((ctx + rows[k])[17] == rows[k][1]);
        lemma_like_pred(db, ctx + rows[k], ps, pname(sv, k));
    }
    lemma_part_row(sv, p0);
    assert((ctx + rows[p0])[17] == rows[p0][1]);
    lemma_like_pred(db, ctx + rows[p0], ps, pname(sv, p0));
    lemma_filter_err(db, ctx, pred, Box::new(Query::Table(3)), rows, e, p0);
    lemma_first_input(db, ctx, part_sub(ps[0]));
    assert(eval_query(db, ctx, part_sub(ps[0])) == Err::<Relation, SqlError>(e));
    assert(eval_expr(db, ctx, Expr::Col(11)) == Ok::<Val, SqlError>(ctx[11]));
}

} // verus!
