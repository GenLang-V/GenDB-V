//! The NOT IN subquery `SELECT s_suppkey FROM supplier WHERE s_comment LIKE '%Customer%Complaints%'`: in any
//! outer row (14 positions) it evaluates, without error, to the one-column rows of the keys of the suppliers whose
//! comment matches (`lemma_sub_query`); `ps_suppkey IN (..)` is then true exactly when the key is one of them
//! (`lemma_in_sub`), i.e. `excluded`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::fns::like::like_value;
use crate::spec::fns::apply_fn;
use crate::link::join::{keep, lemma_keep_true_keep, lemma_keep_members};
use crate::bridge::collect::{lemma_collect_all, lemma_collect_pointwise};
use crate::gendb_entry::stores::StoresView;
use crate::agent::model::*;
use crate::agent::sem_ast::*;
use crate::agent::common::like_two::{plain_pattern, lemma_like_plain};
use crate::stores::flat_supplier::interface as si;

verus! {

/// `s LIKE pat` with the backslash escape.
pub open spec fn like_res(s: Seq<u8>, pat: Seq<u8>) -> Result<Val, SqlError> {
    like_value(Val::Text(s), Val::Text(pat), Val::Text(backslash()))
}

/// A comment matching `'%Customer%Complaints%'`.
pub open spec fn comment_hit(s: Seq<u8>) -> bool {
    like_res(s, comment_pat()) == Ok::<Val, SqlError>(Val::Bool(true))
}

/// The condition of the subquery on a supplier row (its comment, position 6).
pub open spec fn comment_row(r: Row) -> bool {
    match r[6] { Val::Text(s) => comment_hit(s), _ => false }
}

/// The supplier row `b` has a matching comment.
pub open spec fn supp_hit(sv: StoresView, b: int) -> bool {
    comment_hit(s_comment(sv, b))
}

/// `k` is the key of a supplier with a matching comment (the subquery's value set).
pub open spec fn excluded(sv: StoresView, k: int) -> bool {
    exists|b: int| 0 <= b < supp_n(sv) && #[trigger] supp_hit(sv, b) && s_keys(sv)[b] == k
}

/// The subquery's rows: the key of every matching supplier row, in row order.
pub open spec fn sub_rows(sv: StoresView) -> Seq<Row> {
    keep(supp_rows(sv), |r: Row| comment_row(r)).map_values(|r: Row| seq![r[0]])
}

/// The pattern `'%Customer%Complaints%'` has no backslash, so the comment test is always a boolean.
pub proof fn lemma_comment_plain()
    ensures plain_pattern(comment_pat()),
{
    reveal(comment_pat);
    let p = comment_pat();
    assert forall|i: int| 0 <= i < p.len() implies #[trigger] p[i] < 0x80u8 && p[i] != 0x5Cu8 by {
        assert(p[i] == seq![37u8, 67u8, 117u8, 115u8, 116u8, 111u8, 109u8, 101u8, 114u8, 37u8, 67u8, 111u8, 109u8,
            112u8, 108u8, 97u8, 105u8, 110u8, 116u8, 115u8, 37u8][i]);
    }
}

/// The comment test of any text is a boolean.
pub proof fn lemma_comment_bool(s: Seq<u8>)
    ensures like_res(s, comment_pat()) == Ok::<Val, SqlError>(Val::Bool(comment_hit(s))),
{
    lemma_comment_plain();
    lemma_like_plain(s, comment_pat());
}

/// The values of a supplier row the subquery reads.
pub proof fn lemma_supp_row(sv: StoresView, b: int)
    requires stores_wf(sv), 0 <= b < supp_n(sv),
    ensures
        supp_rows(sv)[b].len() == 7,
        supp_rows(sv)[b][0] == Val::Int(s_keys(sv)[b] as int),
        supp_rows(sv)[b][6] == Val::Text(s_comment(sv, b)),
        comment_row(supp_rows(sv)[b]) == supp_hit(sv, b),
{
    assert(supp_rows(sv)[b] == si::row_at(sv.flat_supplier, b));
}

/// `col LIKE pat` (escape backslash) as an AST call.
pub open spec fn like_call(col: nat, pat: Seq<u8>) -> Expr {
    Expr::Call { f: ScalarFn::Like, args: seq![Expr::Col(col), Expr::Lit(Literal::Text(pat)), Expr::Lit(Literal::Text(backslash()))] }
}

/// The three arguments of `col LIKE pat` evaluate to the text at `col`, the pattern and the escape.
#[verifier::spinoff_prover]
proof fn lemma_like_args(db: Database, x: Row, col: nat, pat: Seq<u8>, s: Seq<u8>)
    requires col < x.len(), x[col as int] == Val::Text(s),
    ensures
        eval_exprs(db, x, seq![Expr::Col(col), Expr::Lit(Literal::Text(pat)), Expr::Lit(Literal::Text(backslash()))])
            == Ok::<Row, SqlError>(seq![Val::Text(s), Val::Text(pat), Val::Text(backslash())]),
{
    let e0 = Expr::Col(col);
    let e1 = Expr::Lit(Literal::Text(pat));
    let e2 = Expr::Lit(Literal::Text(backslash()));
    let a1 = seq![e0];
    let a2 = seq![e0, e1];
    let a3 = seq![e0, e1, e2];
    lemma_eval_exprs_empty(db, x);
    assert(a1.drop_last() =~= Seq::<Expr>::empty());
    lemma_eval_exprs_step(db, x, a1);
    assert(eval_exprs(db, x, a1) == Ok::<Row, SqlError>(seq![Val::Text(s)])) by {
        assert(Seq::<Val>::empty().push(Val::Text(s)) =~= seq![Val::Text(s)]);
    }
    assert(a2.drop_last() =~= a1);
    lemma_eval_exprs_step(db, x, a2);
    assert(eval_exprs(db, x, a2) == Ok::<Row, SqlError>(seq![Val::Text(s), Val::Text(pat)])) by {
        assert(seq![Val::Text(s)].push(Val::Text(pat)) =~= seq![Val::Text(s), Val::Text(pat)]);
    }
    assert(a3.drop_last() =~= a2);
    lemma_eval_exprs_step(db, x, a3);
    assert(seq![Val::Text(s), Val::Text(pat)].push(Val::Text(backslash())) =~= seq![Val::Text(s), Val::Text(pat), Val::Text(backslash())]);
}

/// `WHERE col LIKE pat` in an environment whose position `col` is the text `s`: the boolean of `like_res`, or its
/// error.
#[verifier::spinoff_prover]
pub proof fn lemma_like_pred(db: Database, x: Row, col: nat, pat: Seq<u8>, s: Seq<u8>)
    requires col < x.len(), x[col as int] == Val::Text(s),
    ensures
        eval_expr(db, x, like_call(col, pat)) == like_res(s, pat),
        like_res(s, pat) matches Err(err) ==> eval_pred(db, x, Pred::OfBool(like_call(col, pat))) == Err::<Truth, SqlError>(err),
        like_res(s, pat) is Ok ==> like_res(s, pat)->Ok_0 is Bool
            && eval_pred(db, x, Pred::OfBool(like_call(col, pat))) == Ok::<Truth, SqlError>(truth_of(like_res(s, pat)->Ok_0->Bool_0)),
{
    hide(like_value);
    let vals = seq![Val::Text(s), Val::Text(pat), Val::Text(backslash())];
    lemma_like_args(db, x, col, pat, s);
    assert(apply_fn(ScalarFn::Like, vals) == like_res(s, pat));
    reveal(like_value);
    crate::agent::common::like_two::lemma_like_shape(s, pat);
}

/// The subquery's condition in an environment whose position 20 is the text `s`.
#[verifier::spinoff_prover]
proof fn lemma_comment_cond(db: Database, env: Row, s: Seq<u8>)
    requires env.len() == 21, env[20] == Val::Text(s),
    ensures eval_pred(db, env, Pred::OfBool(comment_like())) == Ok::<Truth, SqlError>(truth_of(comment_hit(s))),
{
    lemma_like_pred(db, env, 20, comment_pat(), s);
    lemma_comment_bool(s);
    assert(comment_like() == like_call(20, comment_pat()));
}

/// The subquery's condition on supplier row `i` in outer row `ctx`.
#[verifier::spinoff_prover]
proof fn lemma_sub_cond(db: Database, sv: StoresView, ctx: Row, i: int)
    requires stores_wf(sv), ctx.len() == 14, 0 <= i < supp_n(sv),
    ensures
        eval_pred(db, ctx + supp_rows(sv)[i], Pred::OfBool(comment_like()))
            == Ok::<Truth, SqlError>(truth_of(comment_row(supp_rows(sv)[i]))),
{
    let r = supp_rows(sv)[i];
    lemma_supp_row(sv, i);
    let env = ctx + r;
    assert(env.len() == 21);
    assert(env[20] == r[6]);
    lemma_comment_cond(db, env, s_comment(sv, i));
}

/// The subquery in any outer row of 14 positions: the keys of the matching suppliers.
#[verifier::spinoff_prover]
pub proof fn lemma_sub_query(db: Database, sv: StoresView, ctx: Row)
    requires tables_of(sv, db), stores_wf(sv), ctx.len() == 14,
    ensures eval_query(db, ctx, sub_query()) == Ok::<Relation, SqlError>(sub_rows(sv)),
{
    let rows = supp_rows(sv);
    let f = |r: Row| comment_row(r);
    assert(eval_query(db, ctx, Query::Table(5)) == Ok::<Relation, SqlError>(rows));
    // The WHERE of the subquery: no error, the comment test.
    let prs = Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], Pred::OfBool(comment_like())));
    let truths = Seq::new(rows.len(), |i: int| truth_of(f(rows[i])));
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        lemma_sub_cond(db, sv, ctx, i);
    }
    lemma_collect_all(prs, truths);
    lemma_collect_pointwise::<Truth>();
    lemma_keep_true_keep(rows, truths, f);
    let kept = keep(rows, f);
    assert(eval_query(db, ctx, sub_filter()) == Ok::<Relation, SqlError>(kept));
    // The projection on s_suppkey (position 14 of `ctx ++ row`).
    lemma_keep_members(rows, f);
    let out = kept.map_values(|r: Row| seq![r[0]]);
    let qrs = Seq::new(kept.len(), |i: int| eval_exprs(db, ctx + kept[i], seq![Expr::Col(14)]));
    assert forall|i: int| 0 <= i < qrs.len() implies #[trigger] qrs[i] == Ok::<Row, SqlError>(out[i]) by {
        assert(rows.contains(kept[i]));
        let b = choose|b: int| 0 <= b < rows.len() && rows[b] == kept[i];
        lemma_supp_row(sv, b);
        let env = ctx + kept[i];
        assert(env[14] == kept[i][0]);
        let es = seq![Expr::Col(14)];
        let ers = expr_results(db, env, es);
        lemma_expr_results_index(db, env, es);
        assert(ers[0] == Ok::<Val, SqlError>(kept[i][0]));
        lemma_collect_all(ers, seq![kept[i][0]]);
    }
    lemma_collect_all(qrs, out);
    lemma_collect_pointwise::<Row>();
}

/// `v = ANY (rows)` over one-column integer rows: true exactly when some row holds `v`.
pub proof fn lemma_any_int(k: int, rows: Seq<Row>)
    requires forall|i: int| 0 <= i < rows.len() ==> (#[trigger] rows[i]).len() == 1 && rows[i][0] is Int,
    ensures
        any_cmp_truth(CmpOp::Eq, Val::Int(k), rows)
            == Ok::<Truth, SqlError>(truth_of(exists|i: int| 0 <= i < rows.len() && #[trigger] rows[i][0] == Val::Int(k))),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let d = rows.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies (#[trigger] d[i]).len() == 1 && d[i][0] is Int by {
            assert(d[i] == rows[i]);
        }
        lemma_any_int(k, d);
        let x = rows.last()[0];
        let y = x->Int_0;
        assert(first_col(rows.last()) == Ok::<Val, SqlError>(x));
        crate::link::expr::lemma_compare_int(k, y);
        assert(cmp_truth(CmpOp::Eq, Val::Int(k), x) == Ok::<Truth, SqlError>(truth_of(k == y)));
        let e_d = exists|i: int| 0 <= i < d.len() && #[trigger] d[i][0] == Val::Int(k);
        let e = exists|i: int| 0 <= i < rows.len() && #[trigger] rows[i][0] == Val::Int(k);
        if e_d {
            let i = choose|i: int| 0 <= i < d.len() && #[trigger] d[i][0] == Val::Int(k);
            assert(rows[i][0] == Val::Int(k));
        }
        if e {
            let i = choose|i: int| 0 <= i < rows.len() && #[trigger] rows[i][0] == Val::Int(k);
            if i < d.len() {
                assert(d[i][0] == Val::Int(k));
            } else {
                assert(x == Val::Int(k));
            }
        }
        if k == y {
            assert(rows[rows.len() - 1][0] == Val::Int(k));
        }
    }
}

/// A row satisfying the condition is among the kept rows.
pub proof fn lemma_keep_has(rows: Seq<Row>, f: spec_fn(Row) -> bool, b: int)
    requires 0 <= b < rows.len(), f(rows[b]),
    ensures exists|i: int| 0 <= i < keep(rows, f).len() && #[trigger] keep(rows, f)[i] == rows[b],
    decreases rows.len(),
{
    let d = rows.drop_last();
    if b < d.len() {
        assert(d[b] == rows[b]);
        lemma_keep_has(d, f, b);
        let i = choose|i: int| 0 <= i < keep(d, f).len() && #[trigger] keep(d, f)[i] == d[b];
        if f(rows.last()) {
            assert(keep(rows, f) == keep(d, f).push(rows.last()));
            assert(keep(rows, f)[i] == rows[b]);
        } else {
            assert(keep(rows, f)[i] == rows[b]);
        }
    } else {
        assert(keep(rows, f) == keep(d, f).push(rows.last()));
        let i = keep(d, f).len() as int;
        assert(keep(rows, f)[i] == rows[b]);
    }
}

/// `ps_suppkey IN (subquery)` in any product row whose position 1 is the integer `k`: whether `k` is excluded.
#[verifier::spinoff_prover]
pub proof fn lemma_in_sub(db: Database, sv: StoresView, env: Row, k: int)
    requires tables_of(sv, db), stores_wf(sv), env.len() == 14, env[1] == Val::Int(k),
    ensures eval_pred(db, env, in_sub()) == Ok::<Truth, SqlError>(truth_of(excluded(sv, k))),
{
    lemma_sub_query(db, sv, env);
    let rows = supp_rows(sv);
    let f = |r: Row| comment_row(r);
    let kept = keep(rows, f);
    let sr = sub_rows(sv);
    lemma_keep_members(rows, f);
    assert forall|i: int| 0 <= i < sr.len() implies (#[trigger] sr[i]).len() == 1 && sr[i][0] is Int by {
        assert(rows.contains(kept[i]));
        let b = choose|b: int| 0 <= b < rows.len() && rows[b] == kept[i];
        lemma_supp_row(sv, b);
    }
    lemma_any_int(k, sr);
    let e = exists|i: int| 0 <= i < sr.len() && #[trigger] sr[i][0] == Val::Int(k);
    if e {
        let i = choose|i: int| 0 <= i < sr.len() && #[trigger] sr[i][0] == Val::Int(k);
        assert(rows.contains(kept[i]) && f(kept[i]));
        let b = choose|b: int| 0 <= b < rows.len() && rows[b] == kept[i];
        lemma_supp_row(sv, b);
        assert(supp_hit(sv, b) && s_keys(sv)[b] == k);
    }
    if excluded(sv, k) {
        let b = choose|b: int| 0 <= b < supp_n(sv) && #[trigger] supp_hit(sv, b) && s_keys(sv)[b] == k;
        lemma_supp_row(sv, b);
        lemma_keep_has(rows, f, b);
        let i = choose|i: int| 0 <= i < kept.len() && #[trigger] kept[i] == rows[b];
        assert(sr[i][0] == Val::Int(k));
    }
    assert(eval_expr(db, env, Expr::Col(1)) == Ok::<Val, SqlError>(Val::Int(k)));
}

} // verus!
