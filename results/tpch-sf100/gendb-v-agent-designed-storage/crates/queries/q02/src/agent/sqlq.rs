//! The statement's AST in named pieces (`q_body`, `outer_pred`, `sub_q`, ...; `lemma_query_shape` identifies them
//! with the fixed `query_spec_at`) and the evaluation of its two WHERE conditions on one row.
//!
//! Outer rows (`xrow_ok`) are `part ++ supplier ++ partsupp ++ nation ++ region` (28 values); inner rows of the
//! subquery (`yrow_ok`) are `partsupp ++ supplier ++ nation ++ region` (19 values), evaluated after the outer row.
//! `lemma_inner_pred`: the inner condition is the two-valued `gq`. `lemma_outer_pred`: the outer condition is the
//! LIKE error of the row's p_type when there is one, else a truth that is `True` exactly when `pre_q` holds and the
//! row's ps_supplycost equals the subquery's value.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::collect;
use crate::spec::chars::chars;
use crate::spec::fns::like::*;
use crate::query::{query_spec_at, param_domain};
use crate::link::expr::{lemma_pred_cmp, lemma_pred_and, lemma_pred_text_cmp, ival};
use crate::bridge::collect::lemma_collect_all;
use super::q2spec::*;

verus! {

// ------------------------------------------------------------------------------------------------ AST pieces

/// `Col(a) = Col(b)`.
pub open spec fn ceq(a: nat, b: nat) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(a), b: Expr::Col(b) }
}

/// `Col(c) = literal`.
pub open spec fn clit(c: nat, l: Literal) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(c), b: Expr::Lit(l) }
}

pub open spec fn cand(a: Pred, b: Pred) -> Pred {
    Pred::And(Box::new(a), Box::new(b))
}

/// The subquery's WHERE (environment: outer row ++ inner row).
pub open spec fn inner_pred(ps: Seq<Literal>) -> Pred {
    cand(cand(cand(cand(ceq(0, 28), ceq(33, 29)), ceq(36, 40)), ceq(42, 44)), clit(45, ps[2]))
}

/// The subquery's FROM: partsupp, supplier, nation, region.
pub open spec fn inner_from() -> Query {
    Query::Product {
        left: Box::new(Query::Product {
            left: Box::new(Query::Product { left: Box::new(Query::Table(4)), right: Box::new(Query::Table(5)) }),
            right: Box::new(Query::Table(6)),
        }),
        right: Box::new(Query::Table(7)),
    }
}

/// `SELECT MIN(ps_supplycost) FROM ... WHERE ...`.
pub open spec fn sub_q(ps: Seq<Literal>) -> Query {
    Query::Aggregate {
        aggs: seq![Agg::Min(Expr::Col(31))],
        input: Box::new(Query::Filter { pred: inner_pred(ps), input: Box::new(inner_from()) }),
    }
}

/// `p_type LIKE $2` (escape `\`).
pub open spec fn like_expr(ps: Seq<Literal>) -> Expr {
    Expr::Call { f: ScalarFn::Like, args: seq![Expr::Col(4), Expr::Lit(ps[1]), Expr::Lit(Literal::Text(seq![92u8]))] }
}

/// The outer WHERE without the subquery comparison.
pub open spec fn pre_pred(ps: Seq<Literal>) -> Pred {
    cand(cand(cand(cand(cand(cand(ceq(0, 16), ceq(9, 17)), clit(5, ps[0])), Pred::OfBool(like_expr(ps))), ceq(12, 21)),
        ceq(23, 25)), clit(26, ps[2]))
}

/// The outer WHERE.
pub open spec fn outer_pred(ps: Seq<Literal>) -> Pred {
    cand(pre_pred(ps), Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(19), b: Expr::Subquery(Box::new(sub_q(ps))) })
}

/// The outer FROM: part, supplier, partsupp, nation, region.
pub open spec fn outer_from() -> Query {
    Query::Product {
        left: Box::new(Query::Product {
            left: Box::new(Query::Product {
                left: Box::new(Query::Product { left: Box::new(Query::Table(3)), right: Box::new(Query::Table(5)) }),
                right: Box::new(Query::Table(4)),
            }),
            right: Box::new(Query::Table(6)),
        }),
        right: Box::new(Query::Table(7)),
    }
}

/// The SELECT list: s_acctbal, s_name, n_name, p_partkey, p_mfgr, s_address, s_phone, s_comment.
pub open spec fn out_cols() -> Seq<nat> {
    seq![14nat, 10, 22, 0, 2, 11, 13, 15]
}

pub open spec fn out_exprs() -> Seq<Expr> {
    seq![Expr::Col(14), Expr::Col(10), Expr::Col(22), Expr::Col(0), Expr::Col(2), Expr::Col(11), Expr::Col(13), Expr::Col(15)]
}

/// ORDER BY s_acctbal DESC, n_name, s_name, p_partkey.
pub open spec fn q_keys() -> Seq<OrderKey> {
    seq![
        OrderKey { col: 0, desc: true, nulls_first: true },
        OrderKey { col: 2, desc: false, nulls_first: false },
        OrderKey { col: 1, desc: false, nulls_first: false },
        OrderKey { col: 3, desc: false, nulls_first: false },
    ]
}

pub open spec fn q_filter(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: outer_pred(ps), input: Box::new(outer_from()) }
}

pub open spec fn q_body(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: out_exprs(), input: Box::new(q_filter(ps)) }
}

/// The fixed statement is these pieces.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures query_spec_at(ps) == (OrderedQuery { body: q_body(ps), keys: q_keys(), limit: Some(100nat), offset: 0nat }),
{
}

// ------------------------------------------------------------------------------------------------ parameters

/// The bound parameters as a `Prm`.
pub open spec fn prm_of(ps: Seq<Literal>) -> Prm {
    Prm {
        size: match ps[0] { Literal::Int { v, .. } => v, _ => 0 },
        pat: match ps[1] { Literal::Text(b) => b, _ => Seq::empty() },
        rname: match ps[2] { Literal::Text(b) => b, _ => Seq::empty() },
    }
}

/// The parameters' values: `$1` an int4 literal, `$2` and `$3` texts.
pub open spec fn params_ok(ps: Seq<Literal>) -> bool {
    &&& ps.len() == 3
    &&& ps[0] matches Literal::Int { v, kind } && kind == IntKind::Int4 && int_in_range(IntKind::Int4, v)
    &&& ps[1] is Text
    &&& ps[2] is Text
}

pub proof fn lemma_params_ok(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures params_ok(ps),
{
}

// ------------------------------------------------------------------------------------------------ comparisons

/// Equality of two integer columns.
pub proof fn lemma_eq_int(db: Database, env: Row, a: nat, b: nat)
    requires a < env.len(), b < env.len(), env[a as int] is Int, env[b as int] is Int,
    ensures eval_pred(db, env, ceq(a, b)) == Ok::<Truth, SqlError>(truth_of(env[a as int] == env[b as int])),
{
    let (x, y) = (ival(env[a as int]), ival(env[b as int]));
    lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(a), Expr::Col(b), env[a as int], env[b as int], x, y);
}

/// Equality of a text column with a text literal.
pub proof fn lemma_eq_text_lit(db: Database, env: Row, c: nat, l: Literal)
    requires c < env.len(), env[c as int] is Text, l is Text,
    ensures eval_pred(db, env, clit(c, l)) == Ok::<Truth, SqlError>(truth_of(env[c as int] == Val::Text(l->Text_0))),
{
    let x = env[c as int]->Text_0;
    lemma_pred_text_cmp(db, env, CmpOp::Eq, Expr::Col(c), Expr::Lit(l), x, l->Text_0);
}

/// Equality of an integer column with an int4 literal.
pub proof fn lemma_eq_int_lit(db: Database, env: Row, c: nat, l: Literal)
    requires c < env.len(), env[c as int] is Int, l matches Literal::Int { v, kind } && int_in_range(kind, v),
    ensures eval_pred(db, env, clit(c, l)) == Ok::<Truth, SqlError>(truth_of(env[c as int] == Val::Int(l->v))),
{
    let (x, y) = (ival(env[c as int]), l->v);
    lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(c), Expr::Lit(l), env[c as int], Val::Int(y), x, y);
}

// ------------------------------------------------------------------------------------------------ inner condition

/// An inner row: partsupp (5) ++ supplier (7) ++ nation (4) ++ region (3), with the types the condition reads.
pub open spec fn yrow_ok(y: Row) -> bool {
    &&& y.len() == 19
    &&& y[0] is Int && y[1] is Int && y[5] is Int && y[8] is Int
    &&& y[12] is Int && y[14] is Int && y[16] is Int && y[17] is Text
}

/// The inner condition for partkey value `pkv`: `pkv = ps_partkey AND s_suppkey = ps_suppkey AND s_nationkey =
/// n_nationkey AND n_regionkey = r_regionkey AND r_name = $3`.
pub open spec fn gq(pkv: Val, rname: Seq<u8>, y: Row) -> bool {
    &&& pkv == y[0]
    &&& y[5] == y[1]
    &&& y[8] == y[12]
    &&& y[14] == y[16]
    &&& y[17] == Val::Text(rname)
}

pub proof fn lemma_inner_pred(db: Database, ps: Seq<Literal>, x: Row, y: Row)
    requires params_ok(ps), x.len() == 28, x[0] is Int, yrow_ok(y),
    ensures eval_pred(db, x + y, inner_pred(ps)) == Ok::<Truth, SqlError>(truth_of(gq(x[0], prm_of(ps).rname, y))),
{
    let env = x + y;
    assert(env[0] == x[0]);
    assert(env[28] == y[0] && env[29] == y[1] && env[33] == y[5] && env[36] == y[8]);
    assert(env[40] == y[12] && env[42] == y[14] && env[44] == y[16] && env[45] == y[17]);
    lemma_eq_int(db, env, 0, 28);
    lemma_eq_int(db, env, 33, 29);
    lemma_eq_int(db, env, 36, 40);
    lemma_eq_int(db, env, 42, 44);
    lemma_eq_text_lit(db, env, 45, ps[2]);
    let a1 = env[0] == env[28];
    let a2 = env[33] == env[29];
    let a3 = env[36] == env[40];
    let a4 = env[42] == env[44];
    let a5 = env[45] == Val::Text(ps[2]->Text_0);
    lemma_pred_and(db, env, ceq(0, 28), ceq(33, 29), a1, a2);
    lemma_pred_and(db, env, cand(ceq(0, 28), ceq(33, 29)), ceq(36, 40), a1 && a2, a3);
    lemma_pred_and(db, env, cand(cand(ceq(0, 28), ceq(33, 29)), ceq(36, 40)), ceq(42, 44), a1 && a2 && a3, a4);
    lemma_pred_and(db, env, cand(cand(cand(ceq(0, 28), ceq(33, 29)), ceq(36, 40)), ceq(42, 44)), clit(45, ps[2]),
        a1 && a2 && a3 && a4, a5);
}

// ------------------------------------------------------------------------------------------------ LIKE

/// The escape `\` is one character.
pub proof fn lemma_chars_backslash()
    ensures chars(seq![92u8]) == seq![seq![92u8]],
{
    reveal_with_fuel(chars, 2);
    assert(seq![92u8].drop_last() =~= Seq::<u8>::empty());
    assert(chars(seq![92u8]) =~= seq![seq![92u8]]);
}

/// `s LIKE $2` on a text value is a boolean or the matcher's error.
pub proof fn lemma_like_shape(s: Seq<u8>, pat: Seq<u8>)
    ensures
        like_res(Val::Text(s), pat) is Err || like_res(Val::Text(s), pat) == Ok::<Val, SqlError>(Val::Bool(true))
            || like_res(Val::Text(s), pat) == Ok::<Val, SqlError>(Val::Bool(false)),
        like_res(Val::Text(s), pat) == match like_mt(chars(s), like_tokens(chars(pat), Some(seq![92u8]), 0), 0, 0) {
            Ok(r) => Ok::<Val, SqlError>(Val::Bool(r is Match)),
            Err(e) => Err(e),
        },
{
    lemma_chars_backslash();
    assert(escape_of(chars(seq![92u8])) == Some(seq![92u8]));
}

/// The LIKE call on an outer row is `like_res` of its p_type.
pub proof fn lemma_like_expr(db: Database, ps: Seq<Literal>, x: Row)
    requires params_ok(ps), x.len() == 28, x[4] is Text,
    ensures eval_expr(db, x, like_expr(ps)) == like_res(x[4], prm_of(ps).pat),
{
    let args = seq![Expr::Col(4), Expr::Lit(ps[1]), Expr::Lit(Literal::Text(seq![92u8]))];
    let vs = seq![x[4], Val::Text(ps[1]->Text_0), Val::Text(seq![92u8])];
    let rs = expr_results(db, x, args);
    lemma_expr_results_index(db, x, args);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Val, SqlError>(vs[i]) by {
        assert(rs[i] == eval_expr(db, x, args[i]));
    }
    lemma_collect_all(rs, vs);
    assert(eval_exprs(db, x, args) == Ok::<Row, SqlError>(vs));
}

// ------------------------------------------------------------------------------------------------ outer condition

/// An outer row: part (9) ++ supplier (7) ++ partsupp (5) ++ nation (4) ++ region (3), with the types the
/// condition reads.
pub open spec fn xrow_ok(x: Row) -> bool {
    &&& x.len() == 28
    &&& x[0] is Int && x[16] is Int && x[9] is Int && x[17] is Int && x[5] is Int
    &&& x[4] is Text
    &&& x[12] is Int && x[21] is Int && x[23] is Int && x[25] is Int
    &&& x[26] is Text
    &&& x[19] is Num && x[19]->scale == 2
}

/// The outer condition without the subquery comparison (two-valued on rows whose LIKE does not fail).
pub open spec fn pre_q(m: Prm, x: Row) -> bool {
    &&& x[0] == x[16]
    &&& x[9] == x[17]
    &&& x[5] == Val::Int(m.size)
    &&& like_true(x[4], m.pat)
    &&& x[12] == x[21]
    &&& x[23] == x[25]
    &&& x[26] == Val::Text(m.rname)
}

/// An error of the left operand of AND is the outcome.
pub proof fn lemma_and_err_left(db: Database, env: Row, a: Pred, b: Pred, e: SqlError)
    requires eval_pred(db, env, a) == Err::<Truth, SqlError>(e),
    ensures eval_pred(db, env, cand(a, b)) == Err::<Truth, SqlError>(e),
{
}

/// An error of the right operand of AND after a value of the left one is the outcome.
pub proof fn lemma_and_err_right(db: Database, env: Row, a: Pred, b: Pred, t: Truth, e: SqlError)
    requires eval_pred(db, env, a) == Ok::<Truth, SqlError>(t), eval_pred(db, env, b) == Err::<Truth, SqlError>(e),
    ensures eval_pred(db, env, cand(a, b)) == Err::<Truth, SqlError>(e),
{
}

/// AND of a two-valued truth with any truth `u` is `True` exactly when both are.
pub proof fn lemma_and_true(db: Database, env: Row, a: Pred, b: Pred, x: bool, u: Truth)
    requires eval_pred(db, env, a) == Ok::<Truth, SqlError>(truth_of(x)), eval_pred(db, env, b) == Ok::<Truth, SqlError>(u),
    ensures
        eval_pred(db, env, cand(a, b)) is Ok,
        (eval_pred(db, env, cand(a, b))->Ok_0 == Truth::True) == (x && u == Truth::True),
{
}

/// `OfBool(p_type LIKE $2)`: the LIKE error, or the two-valued `like_true`.
pub proof fn lemma_like_pred(db: Database, ps: Seq<Literal>, x: Row)
    requires params_ok(ps), x.len() == 28, x[4] is Text,
    ensures
        like_res(x[4], prm_of(ps).pat) matches Err(e) ==> eval_pred(db, x, Pred::OfBool(like_expr(ps))) == Err::<Truth, SqlError>(e),
        like_res(x[4], prm_of(ps).pat) is Ok ==> eval_pred(db, x, Pred::OfBool(like_expr(ps)))
            == Ok::<Truth, SqlError>(truth_of(like_true(x[4], prm_of(ps).pat))),
{
    lemma_like_expr(db, ps, x);
    lemma_like_shape(x[4]->Text_0, prm_of(ps).pat);
}

/// The outer condition without the subquery comparison.
pub proof fn lemma_pre_pred(db: Database, ps: Seq<Literal>, x: Row)
    requires params_ok(ps), xrow_ok(x),
    ensures
        like_res(x[4], prm_of(ps).pat) matches Err(e) ==> eval_pred(db, x, pre_pred(ps)) == Err::<Truth, SqlError>(e),
        like_res(x[4], prm_of(ps).pat) is Ok ==> eval_pred(db, x, pre_pred(ps)) == Ok::<Truth, SqlError>(truth_of(pre_q(prm_of(ps), x))),
{
    let m = prm_of(ps);
    lemma_eq_int(db, x, 0, 16);
    lemma_eq_int(db, x, 9, 17);
    lemma_eq_int_lit(db, x, 5, ps[0]);
    lemma_like_pred(db, ps, x);
    lemma_eq_int(db, x, 12, 21);
    lemma_eq_int(db, x, 23, 25);
    lemma_eq_text_lit(db, x, 26, ps[2]);
    let b1 = x[0] == x[16];
    let b2 = x[9] == x[17];
    let b3 = x[5] == Val::Int(m.size);
    let b5 = x[12] == x[21];
    let b6 = x[23] == x[25];
    let b7 = x[26] == Val::Text(m.rname);
    let lp = Pred::OfBool(like_expr(ps));
    let p2 = cand(ceq(0, 16), ceq(9, 17));
    let p3 = cand(p2, clit(5, ps[0]));
    let p4 = cand(p3, lp);
    let p5 = cand(p4, ceq(12, 21));
    let p6 = cand(p5, ceq(23, 25));
    lemma_pred_and(db, x, ceq(0, 16), ceq(9, 17), b1, b2);
    lemma_pred_and(db, x, p2, clit(5, ps[0]), b1 && b2, b3);
    match like_res(x[4], m.pat) {
        Err(e) => {
            lemma_and_err_right(db, x, p3, lp, truth_of(b1 && b2 && b3), e);
            lemma_and_err_left(db, x, p4, ceq(12, 21), e);
            lemma_and_err_left(db, x, p5, ceq(23, 25), e);
            lemma_and_err_left(db, x, p6, clit(26, ps[2]), e);
        },
        Ok(v) => {
            let b4 = like_true(x[4], m.pat);
            lemma_pred_and(db, x, p3, lp, b1 && b2 && b3, b4);
            lemma_pred_and(db, x, p4, ceq(12, 21), b1 && b2 && b3 && b4, b5);
            lemma_pred_and(db, x, p5, ceq(23, 25), b1 && b2 && b3 && b4 && b5, b6);
            lemma_pred_and(db, x, p6, clit(26, ps[2]), b1 && b2 && b3 && b4 && b5 && b6, b7);
        },
    }
}

/// `ps_supplycost = (subquery)` with subquery value `sv`: `Unknown` for NULL, else equality of the numerics.
pub proof fn lemma_last_cmp(db: Database, ps: Seq<Literal>, x: Row, sv: Val)
    requires
        xrow_ok(x),
        eval_expr(db, x, Expr::Subquery(Box::new(sub_q(ps)))) == Ok::<Val, SqlError>(sv),
        sv is Null || (sv is Num && sv->scale == 2),
    ensures ({
        let last = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(19), b: Expr::Subquery(Box::new(sub_q(ps))) };
        &&& eval_pred(db, x, last) is Ok
        &&& (eval_pred(db, x, last)->Ok_0 == Truth::True) == (x[19] == sv)
    }),
{
    let last = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(19), b: Expr::Subquery(Box::new(sub_q(ps))) };
    assert(eval_expr(db, x, Expr::Col(19)) == Ok::<Val, SqlError>(x[19]));
    if sv is Null {
        assert(eval_pred(db, x, last) == Ok::<Truth, SqlError>(Truth::Unknown));
    } else {
        let (c1, c2) = (x[19]->coeff, sv->coeff);
        assert(x[19] == (Val::Num { coeff: c1, scale: 2 }));
        assert(sv == (Val::Num { coeff: c2, scale: 2 }));
        crate::link::expr::lemma_compare_num(c1, 2, c2, 2);
        crate::link::expr::lemma_align_same(c1, 2);
        crate::link::expr::lemma_align_same(c2, 2);
        assert(crate::spec::numeric::max_nat(2, 2) == 2);
        assert(compare(x[19], sv) == Some(crate::spec::numeric::sign(c1 - c2)));
        assert((crate::spec::numeric::sign(c1 - c2) == 0) == (c1 == c2));
        assert(eval_pred(db, x, last) == Ok::<Truth, SqlError>(truth_of(c1 == c2)));
        assert((c1 == c2) == (x[19] == sv));
    }
}

/// The outer condition on one row whose subquery value is `sv` (NULL or a numeric of scale 2).
pub proof fn lemma_outer_pred(db: Database, ps: Seq<Literal>, x: Row, sv: Val)
    requires
        params_ok(ps), xrow_ok(x),
        eval_expr(db, x, Expr::Subquery(Box::new(sub_q(ps)))) == Ok::<Val, SqlError>(sv),
        sv is Null || (sv is Num && sv->scale == 2),
    ensures
        like_res(x[4], prm_of(ps).pat) matches Err(e) ==> eval_pred(db, x, outer_pred(ps)) == Err::<Truth, SqlError>(e),
        like_res(x[4], prm_of(ps).pat) is Ok ==> eval_pred(db, x, outer_pred(ps)) is Ok
            && (eval_pred(db, x, outer_pred(ps))->Ok_0 == Truth::True) == (pre_q(prm_of(ps), x) && x[19] == sv),
{
    let last = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(19), b: Expr::Subquery(Box::new(sub_q(ps))) };
    lemma_pre_pred(db, ps, x);
    lemma_last_cmp(db, ps, x, sv);
    match like_res(x[4], prm_of(ps).pat) {
        Err(e) => {
            lemma_and_err_left(db, x, pre_pred(ps), last, e);
        },
        Ok(v) => {
            lemma_and_true(db, x, pre_pred(ps), last, pre_q(prm_of(ps), x), eval_pred(db, x, last)->Ok_0);
        },
    }
}

} // verus!
