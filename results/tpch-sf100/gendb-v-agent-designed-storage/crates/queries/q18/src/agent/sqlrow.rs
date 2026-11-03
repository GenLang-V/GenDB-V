//! The Q18 statement's AST in named pieces (`q18_*`; `lemma_q18_shape` identifies them with `query::query_spec_at`)
//! and its per-row meaning: on a joined row `customer ++ orders ++ lineitem` (33 columns) whose read columns hold
//! `ck` (c_custkey), `ok` (o_orderkey), `oc` (o_custkey), `lk` (l_orderkey), the WHERE condition is the two-valued
//! `big(ok) && ck == oc && ok == lk` (`lemma_pred_eval`, the IN subquery by `subq::lemma_in_pred`); the group key is
//! (c_name, c_custkey, o_orderkey, o_orderdate, o_totalprice) and the SUM argument is l_quantity.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::collect;
use crate::query::{query_spec_at, param_domain};
use crate::link::query::{col_exprs, lemma_eval_cols, select};
use crate::link::expr::{lemma_expr_col, lemma_pred_cmp, lemma_pred_and, lemma_compare_int};
use super::model::*;
use super::qspec::*;
use super::rels::*;
use super::subq::*;

verus! {

/// `o_orderkey IN (..) AND c_custkey = o_custkey AND o_orderkey = l_orderkey` over the joined row.
pub open spec fn q18_pred(ps: Seq<Literal>) -> Pred {
    Pred::And(
        Box::new(Pred::And(
            Box::new(in_pred(ps)),
            Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) }),
        )),
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(8), b: Expr::Col(17) }),
    )
}

/// GROUP BY c_name, c_custkey, o_orderkey, o_orderdate, o_totalprice.
pub open spec fn q18_gkeys() -> Seq<Expr> {
    seq![Expr::Col(1), Expr::Col(0), Expr::Col(8), Expr::Col(12), Expr::Col(11)]
}

/// SUM(l_quantity).
pub open spec fn q18_aggs() -> Seq<Agg> {
    seq![Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(21) }]
}

/// FROM customer, orders, lineitem.
pub open spec fn q18_from() -> Query {
    Query::Product { left: Box::new(Query::Product { left: Box::new(Query::Table(2)), right: Box::new(Query::Table(1)) }), right: Box::new(Query::Table(0)) }
}

pub open spec fn q18_filter(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: q18_pred(ps), input: Box::new(q18_from()) }
}

/// The body: the GROUP BY row is the SELECT list (no projection).
pub open spec fn q18_body(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: q18_gkeys(), aggs: q18_aggs(), input: Box::new(q18_filter(ps)) }
}

/// The statement is these pieces, ordered by `q18_keys` with LIMIT 100.
pub proof fn lemma_q18_shape(ps: Seq<Literal>)
    ensures
        query_spec_at(ps).body == q18_body(ps),
        query_spec_at(ps).keys == q18_keys(),
        query_spec_at(ps).limit == Some(100nat),
        query_spec_at(ps).offset == 0,
{
    assert(query_spec_at(ps).keys =~= q18_keys());
    assert(q18_gkeys() =~= seq![Expr::Col(1), Expr::Col(0), Expr::Col(8), Expr::Col(12), Expr::Col(11)]);
}

/// The WHERE condition on a joined row, from the values of its read columns.
pub proof fn lemma_pred_eval(db: Database, m: M, ps: Seq<Literal>, env: Row, ck: int, ok: int, oc: int, lk: int)
    requires
        sub_ok(db, m),
        param_domain(ps),
        env.len() == 33,
        env[0] == Val::Int(ck),
        env[8] == Val::Int(ok),
        env[9] == Val::Int(oc),
        env[17] == Val::Int(lk),
    ensures
        eval_pred(db, env, q18_pred(ps)) == Ok::<Truth, SqlError>(truth_of(big(m, qp_of(ps), ok) && ck == oc && ok == lk)),
{
    let p = qp_of(ps);
    // o_orderkey IN (..)
    lemma_in_pred(db, m, ps, env, ok);
    // c_custkey = o_custkey
    lemma_expr_col(db, env, 0);
    lemma_expr_col(db, env, 9);
    lemma_compare_int(ck, oc);
    lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(0), Expr::Col(9), Val::Int(ck), Val::Int(oc), ck, oc);
    let pc = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) };
    lemma_pred_and(db, env, in_pred(ps), pc, big(m, p, ok), ck == oc);
    let pa = Pred::And(Box::new(in_pred(ps)), Box::new(pc));
    // o_orderkey = l_orderkey
    lemma_expr_col(db, env, 8);
    lemma_expr_col(db, env, 17);
    lemma_compare_int(ok, lk);
    lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(8), Expr::Col(17), Val::Int(ok), Val::Int(lk), ok, lk);
    let pl = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(8), b: Expr::Col(17) };
    lemma_pred_and(db, env, pa, pl, big(m, p, ok) && ck == oc, ok == lk);
}

/// The group key on a joined row.
pub proof fn lemma_keys_eval(db: Database, env: Row)
    requires env.len() == 33,
    ensures
        eval_exprs(db, env, q18_gkeys()) == Ok::<Row, SqlError>(seq![env[1], env[0], env[8], env[12], env[11]]),
{
    let idx = seq![1nat, 0, 8, 12, 11];
    assert(q18_gkeys() =~= col_exprs(idx));
    lemma_eval_cols(db, env, idx);
    assert(select(env, idx) =~= seq![env[1], env[0], env[8], env[12], env[11]]);
}

/// The SUM argument list on a joined row: l_quantity.
pub proof fn lemma_args_eval(db: Database, env: Row)
    requires env.len() == 33,
    ensures agg_args(db, env, q18_aggs()) == Ok::<Row, SqlError>(seq![env[21]]),
{
    let v = env[21];
    lemma_expr_col(db, env, 21);
    let rs = agg_arg_results(db, env, q18_aggs());
    lemma_agg_arg_results_index(db, env, q18_aggs());
    assert(rs[0] == agg_arg(db, env, q18_aggs()[0]));
    assert(rs.len() == 1);
    assert(rs.drop_last().len() == 0);
    assert(collect(rs.drop_last()) == Ok::<Seq<Val>, SqlError>(Seq::empty()));
    assert(rs.last() == Ok::<Val, SqlError>(v));
    assert(Seq::<Val>::empty().push(v) =~= seq![v]);
}

} // verus!
