//! Per-row meaning of the statement's conditions: `SUBSTRING(c_phone, 1, 2)` (`lemma_sub2_eval`), the IN list
//! (`lemma_in7_eval`), `NOT EXISTS` over orders (`lemma_ex_eval`), the comparison with the AVG subquery's value
//! (`lemma_gt_eval`) and the whole outer WHERE condition (`lemma_where_eval`: true exactly on qualifying rows).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::fns::*;
use crate::spec::fns::substring::*;
use crate::spec::fns::div::*;
use crate::gendb_entry::stores::StoresView;
use crate::link::expr::*;
use crate::link::exists::lemma_exists_filter_table;
use crate::bridge::collect::lemma_collect_all;
use crate::agent::common::prefix2::prefix2;
use crate::agent::common::avg_threshold::*;
use crate::agent::tables::*;
use crate::agent::normal::*;
use crate::agent::ast::*;

verus! {

/// A three-expression list over evaluated expressions.
#[verifier::spinoff_prover]
proof fn lemma_eval_triple(db: Database, env: Row, a: Expr, b: Expr, c: Expr, va: Val, vb: Val, vc: Val)
    requires
        eval_expr(db, env, a) == Ok::<Val, SqlError>(va),
        eval_expr(db, env, b) == Ok::<Val, SqlError>(vb),
        eval_expr(db, env, c) == Ok::<Val, SqlError>(vc),
    ensures eval_exprs(db, env, seq![a, b, c]) == Ok::<Row, SqlError>(seq![va, vb, vc]),
{
    hide(eval_expr);
    hide(collect);
    hide(eval_exprs);
    let es = seq![a, b, c];
    let vs = seq![va, vb, vc];
    let rs = expr_results(db, env, es);
    lemma_expr_results_index(db, env, es);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Val, SqlError>(vs[i]) by {
        if i == 0 {} else if i == 1 {} else {}
    }
    lemma_collect_all(rs, vs);
    assert(eval_exprs(db, env, es) == collect(expr_results(db, env, es))) by { reveal(eval_exprs); }
}

/// An int4 literal.
#[verifier::spinoff_prover]
proof fn lemma_lit_int4(db: Database, env: Row, v: int)
    requires int_in_range(IntKind::Int4, v),
    ensures eval_expr(db, env, Expr::Lit(Literal::Int { v, kind: IntKind::Int4 })) == Ok::<Val, SqlError>(Val::Int(v)),
{
}

/// The argument list `[Col(c), 1, 2]` of `SUBSTRING`.
#[verifier::spinoff_prover]
proof fn lemma_sub2_args(db: Database, env: Row, c: nat, b: Seq<u8>)
    requires c < env.len(), env[c as int] == Val::Text(b),
    ensures
        eval_exprs(db, env, seq![Expr::Col(c), Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 }),
            Expr::Lit(Literal::Int { v: 2, kind: IntKind::Int4 })])
            == Ok::<Row, SqlError>(seq![Val::Text(b), Val::Int(1), Val::Int(2)]),
{
    hide(eval_expr);
    hide(eval_exprs);
    lemma_expr_col(db, env, c);
    assert(int_in_range(IntKind::Int4, 1) && int_in_range(IntKind::Int4, 2));
    lemma_lit_int4(db, env, 1);
    lemma_lit_int4(db, env, 2);
    lemma_eval_triple(db, env, Expr::Col(c), Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 }),
        Expr::Lit(Literal::Int { v: 2, kind: IntKind::Int4 }), Val::Text(b), Val::Int(1), Val::Int(2));
}

/// `SUBSTRING` applied to `[Text(b), 1, 2]`.
#[verifier::spinoff_prover]
proof fn lemma_sub2_apply(b: Seq<u8>)
    ensures apply_fn(ScalarFn::Substring3, seq![Val::Text(b), Val::Int(1), Val::Int(2)]) == Ok::<Val, SqlError>(Val::Text(prefix2(b))),
{
    reveal(prefix2);
    let vs = seq![Val::Text(b), Val::Int(1), Val::Int(2)];
    assert(!(exists|k: int| 0 <= k < vs.len() && #[trigger] vs[k] is Null)) by {
        assert forall|k: int| 0 <= k < vs.len() implies !(#[trigger] vs[k] is Null) by {
            if k == 0 {} else if k == 1 {} else {}
        }
    }
    assert(apply_substring(ScalarFn::Substring3, vs) == Ok::<Val, SqlError>(Val::Text(prefix2(b))));
}

/// One evaluation step of a call over evaluated arguments.
#[verifier::spinoff_prover]
proof fn lemma_call_node(db: Database, env: Row, f: ScalarFn, args: Seq<Expr>, vs: Seq<Val>)
    requires eval_exprs(db, env, args) == Ok::<Row, SqlError>(vs),
    ensures eval_expr(db, env, Expr::Call { f, args }) == apply_fn(f, vs),
{
}

/// `SUBSTRING(Col(c), 1, 2)` of a text value is its two-character prefix.
#[verifier::spinoff_prover]
pub proof fn lemma_sub2_eval(db: Database, env: Row, c: nat, b: Seq<u8>)
    requires c < env.len(), env[c as int] == Val::Text(b),
    ensures eval_expr(db, env, sub2(c)) == Ok::<Val, SqlError>(Val::Text(prefix2(b))),
{
    hide(eval_exprs);
    hide(apply_fn);
    hide(eval_expr);
    let args = seq![Expr::Col(c), Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 }),
        Expr::Lit(Literal::Int { v: 2, kind: IntKind::Int4 })];
    let vs = seq![Val::Text(b), Val::Int(1), Val::Int(2)];
    lemma_sub2_args(db, env, c, b);
    lemma_sub2_apply(b);
    lemma_call_node(db, env, ScalarFn::Substring3, args, vs);
}

/// `SUBSTRING(Col(c), 1, 2) = p`.
#[verifier::spinoff_prover]
pub proof fn lemma_eqp_eval(db: Database, env: Row, c: nat, b: Seq<u8>, p: Seq<u8>)
    requires c < env.len(), env[c as int] == Val::Text(b),
    ensures eval_pred(db, env, eqp(c, Literal::Text(p))) == Ok::<Truth, SqlError>(truth_of(prefix2(b) == p)),
{
    lemma_sub2_eval(db, env, c, b);
    lemma_expr_text(db, env, p);
    lemma_pred_text_cmp(db, env, CmpOp::Eq, sub2(c), Expr::Lit(Literal::Text(p)), prefix2(b), p);
}

/// The IN list: true exactly when the prefix is one of the seven parameters.
#[verifier::spinoff_prover]
pub proof fn lemma_in7_eval(db: Database, env: Row, c: nat, b: Seq<u8>, ps: Seq<Literal>)
    requires c < env.len(), env[c as int] == Val::Text(b), ps_ok(ps),
    ensures eval_pred(db, env, in7(c, ps)) == Ok::<Truth, SqlError>(truth_of(code_hit(ps, prefix2(b)))),
{
    hide(eval_pred);
    let t = prefix2(b);
    assert forall|k: int| 0 <= k < 7 implies ps[k] == Literal::Text(#[trigger] pt(ps, k)) by {
        assert(ps[k] is Text);
    }
    assert(ps[0] == Literal::Text(pt(ps, 0)));
    assert(ps[1] == Literal::Text(pt(ps, 1)));
    assert(ps[2] == Literal::Text(pt(ps, 2)));
    assert(ps[3] == Literal::Text(pt(ps, 3)));
    assert(ps[4] == Literal::Text(pt(ps, 4)));
    assert(ps[5] == Literal::Text(pt(ps, 5)));
    assert(ps[6] == Literal::Text(pt(ps, 6)));
    lemma_eqp_eval(db, env, c, b, pt(ps, 0));
    lemma_eqp_eval(db, env, c, b, pt(ps, 1));
    lemma_eqp_eval(db, env, c, b, pt(ps, 2));
    lemma_eqp_eval(db, env, c, b, pt(ps, 3));
    lemma_eqp_eval(db, env, c, b, pt(ps, 4));
    lemma_eqp_eval(db, env, c, b, pt(ps, 5));
    lemma_eqp_eval(db, env, c, b, pt(ps, 6));
    let (e0, e1, e2, e3, e4, e5, e6) = (eqp(c, ps[0]), eqp(c, ps[1]), eqp(c, ps[2]), eqp(c, ps[3]), eqp(c, ps[4]),
        eqp(c, ps[5]), eqp(c, ps[6]));
    let (h0, h1, h2, h3, h4, h5, h6) = (t == pt(ps, 0), t == pt(ps, 1), t == pt(ps, 2), t == pt(ps, 3), t == pt(ps, 4),
        t == pt(ps, 5), t == pt(ps, 6));
    lemma_pred_or(db, env, e0, e1, h0, h1);
    lemma_pred_or(db, env, or(e0, e1), e2, h0 || h1, h2);
    lemma_pred_or(db, env, or(or(e0, e1), e2), e3, (h0 || h1) || h2, h3);
    lemma_pred_or(db, env, or(or(or(e0, e1), e2), e3), e4, ((h0 || h1) || h2) || h3, h4);
    lemma_pred_or(db, env, or(or(or(or(e0, e1), e2), e3), e4), e5, (((h0 || h1) || h2) || h3) || h4, h5);
    lemma_pred_or(db, env, or(or(or(or(or(e0, e1), e2), e3), e4), e5), e6, ((((h0 || h1) || h2) || h3) || h4) || h5, h6);
}

/// `EXISTS (SELECT * FROM orders WHERE o_custkey = c_custkey)` for an outer row with key `k`.
#[verifier::spinoff_prover]
pub proof fn lemma_ex_eval(db: Database, sv: StoresView, x: Row, k: int)
    requires tables_of(sv, db), x.len() == 8, x[0] == Val::Int(k),
    ensures eval_pred(db, x, ex()) == Ok::<Truth, SqlError>(truth_of(has_ord(sv, k))),
{
    let ot = db.tables[1];
    assert forall|j: int| 0 <= j < ot.len() implies
        #[trigger] eval_pred(db, x + ot[j], ex_pred()) == Ok::<Truth, SqlError>(truth_of(ock(sv)[j] as int == k)) by {
        lemma_orders_row(sv, j);
        let e = x + ot[j];
        let o = ock(sv)[j] as int;
        assert(e[9] == Val::Int(o));
        assert(e[0] == Val::Int(k));
        lemma_expr_col(db, e, 9);
        lemma_expr_col(db, e, 0);
        lemma_compare_int(o, k);
        lemma_pred_cmp(db, e, CmpOp::Eq, Expr::Col(9), Expr::Col(0), Val::Int(o), Val::Int(k), o, k);
    }
    lemma_exists_filter_table(db, x, ex_pred(), 1);
    let w1 = exists|j: int| 0 <= j < ot.len() && #[trigger] eval_pred(db, x + ot[j], ex_pred()) == Ok::<Truth, SqlError>(Truth::True);
    if w1 {
        let j = choose|j: int| 0 <= j < ot.len() && #[trigger] eval_pred(db, x + ot[j], ex_pred()) == Ok::<Truth, SqlError>(Truth::True);
        assert(ock(sv)[j] as int == k);
    }
    if has_ord(sv, k) {
        let j = choose|j: int| 0 <= j < n_o(sv) && #[trigger] ock(sv)[j] as int == k;
        assert(eval_pred(db, x + ot[j], ex_pred()) == Ok::<Truth, SqlError>(Truth::True));
    }
}

/// The value of the AVG subquery: NULL on an empty population, else PostgreSQL's quotient.
pub open spec fn avg_val(sv: StoresView, ps: Seq<Literal>) -> Val {
    if avg_n(sv, ps) == 0 {
        Val::Null
    } else {
        Val::Num { coeff: num_div_coeff(avg_s(sv, ps), 2, avg_n(sv, ps), 0), scale: div_scale(avg_s(sv, ps), 2, avg_n(sv, ps), 0) }
    }
}

/// The truth of `c_acctbal > (subquery)` for a balance `c`: unknown on an empty population.
pub open spec fn gt_truth(sv: StoresView, ps: Seq<Literal>, c: int) -> Truth {
    if avg_n(sv, ps) == 0 { Truth::Unknown } else { truth_of(c > thr(sv, ps)) }
}

/// `c_acctbal > (subquery)` once the subquery's value is known.
#[verifier::spinoff_prover]
pub proof fn lemma_gt_eval(db: Database, sv: StoresView, ps: Seq<Literal>, x: Row, c: int)
    requires
        x.len() == 8,
        x[5] == (Val::Num { coeff: c, scale: 2 }),
        eval_expr(db, x, Expr::Subquery(Box::new(sub_agg(ps)))) == Ok::<Val, SqlError>(avg_val(sv, ps)),
        avg_n(sv, ps) >= 0,
        avg_s(sv, ps) >= 0,
    ensures eval_pred(db, x, gt_pred(ps)) == Ok::<Truth, SqlError>(gt_truth(sv, ps, c)),
{
    lemma_expr_col(db, x, 5);
    let v = avg_val(sv, ps);
    if avg_n(sv, ps) > 0 {
        let (s, n) = (avg_s(sv, ps), avg_n(sv, ps));
        let a = num_div_coeff(s, 2, n, 0);
        let r = div_scale(s, 2, n, 0);
        lemma_gt_avg(c, s, 2, n);
        assert(compare(Val::Num { coeff: c, scale: 2 }, Val::Num { coeff: a, scale: r }) == Some(num_cmp(c, 2, a, r)));
        assert(cmp_truth(CmpOp::Gt, Val::Num { coeff: c, scale: 2 }, v) == Ok::<Truth, SqlError>(truth_of(c > thr(sv, ps))));
    }
}

/// The outer WHERE condition on customer row `i`, given its parts: true exactly when the row qualifies.
#[verifier::spinoff_prover]
pub proof fn lemma_where_eval(db: Database, sv: StoresView, ps: Seq<Literal>, i: int)
    requires
        tables_of(sv, db),
        ps_ok(ps),
        0 <= i < n_c(sv),
        avg_n(sv, ps) >= 0,
        avg_s(sv, ps) >= 0,
        eval_expr(db, cust_rows(sv)[i], Expr::Subquery(Box::new(sub_agg(ps)))) == Ok::<Val, SqlError>(avg_val(sv, ps)),
    ensures ({
        let t = eval_pred(db, cust_rows(sv)[i], where_pred(ps));
        &&& t is Ok
        &&& (t->Ok_0 is True) == qual(sv, ps, i)
    }),
{
    hide(eval_expr);
    let x = cust_rows(sv)[i];
    lemma_cust_row(sv, i);
    let c = bal(sv)[i] as int;
    lemma_in7_eval(db, x, 4, phone(sv, i), ps);
    lemma_gt_eval(db, sv, ps, x, c);
    lemma_ex_eval(db, sv, x, cck(sv)[i] as int);
    let ti = truth_of(code_hit(ps, code_of(sv, i)));
    let tg = gt_truth(sv, ps, c);
    let te = truth_of(has_ord(sv, cck(sv)[i] as int));
    assert(eval_pred(db, x, and(in7(4, ps), gt_pred(ps))) == Ok::<Truth, SqlError>(truth_and(ti, tg)));
    assert(eval_pred(db, x, Pred::Not(Box::new(ex()))) == Ok::<Truth, SqlError>(truth_not(te)));
    assert(eval_pred(db, x, where_pred(ps)) == Ok::<Truth, SqlError>(truth_and(truth_and(ti, tg), truth_not(te))));
}

} // verus!
