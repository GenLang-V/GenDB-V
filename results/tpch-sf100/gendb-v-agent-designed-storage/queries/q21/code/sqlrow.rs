//! The Q21 statement's AST in named pieces (`q21_*`; `lemma_q21_shape` identifies them with `query::query_spec_at`)
//! and its per-row meaning. A FROM row is `supplier ++ lineitem ++ orders ++ nation` (7 + 16 + 9 + 4 = 36 columns);
//! the WHERE condition reads s_suppkey 0, s_nationkey 3, l_orderkey 7, l_suppkey 9, l_commitdate 18,
//! l_receiptdate 19, o_orderkey 23, o_orderstatus 25, n_nationkey 32 and n_name 33. On a row whose read columns hold
//! non-NULL values of their types, and on a database whose lineitem rows do too, the condition is the two-valued
//! `qual_env` (`lemma_pred_eval`): the joins, `o_orderstatus = 'F'`, lateness, the EXISTS as `ex2` and the
//! NOT EXISTS as `!ex3` (both over the lineitem table, `lemma_exists2`, `lemma_exists3`) and `n_name = $1`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::scalar::{compare, CmpOp};
use crate::spec::numeric::sign;
use crate::query::query_spec_at;
use crate::link::expr::{ival, tval, int_cmp, text_cmp, lemma_expr_col, lemma_expr_text, lemma_pred_cmp,
    lemma_pred_text_cmp, lemma_pred_and, lemma_pred_not, lemma_compare_int, lemma_compare_date};
use crate::link::exists::lemma_exists_filter_table;
use super::cand::q21_keys;

verus! {

// ------------------------------------------------------------------------------------------------ the pieces

pub open spec fn c_eq(a: nat, b: nat) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(a), b: Expr::Col(b) }
}

pub open spec fn c_op(op: CmpOp, a: nat, b: nat) -> Pred {
    Pred::Cmp { op, a: Expr::Col(a), b: Expr::Col(b) }
}

pub open spec fn and(a: Pred, b: Pred) -> Pred {
    Pred::And(Box::new(a), Box::new(b))
}

/// `'F'`.
pub open spec fn f_text() -> Seq<u8> {
    seq![70u8]
}

/// `s_suppkey = l_suppkey AND o_orderkey = l_orderkey`.
pub open spec fn p8() -> Pred { and(c_eq(0, 9), c_eq(23, 7)) }

/// `.. AND o_orderstatus = 'F'`.
pub open spec fn p13() -> Pred {
    and(p8(), Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(25), b: Expr::Lit(Literal::Text(f_text())) })
}

/// `.. AND l1.l_receiptdate > l1.l_commitdate`.
pub open spec fn p17() -> Pred { and(p13(), c_op(CmpOp::Gt, 19, 18)) }

/// The EXISTS condition on `row ++ l2`: `l2.l_orderkey = l1.l_orderkey AND l2.l_suppkey <> l1.l_suppkey`.
pub open spec fn sub2() -> Pred { and(c_eq(36, 7), c_op(CmpOp::Ne, 38, 9)) }

pub open spec fn ex2_pred() -> Pred {
    Pred::Exists(Box::new(Query::Filter { pred: sub2(), input: Box::new(Query::Table(0)) }))
}

/// `.. AND EXISTS (..)`.
pub open spec fn p28() -> Pred { and(p17(), ex2_pred()) }

/// The NOT EXISTS condition on `row ++ l3`: the EXISTS condition and `l3.l_receiptdate > l3.l_commitdate`.
pub open spec fn sub3() -> Pred { and(sub2(), c_op(CmpOp::Gt, 48, 47)) }

pub open spec fn ex3_pred() -> Pred {
    Pred::Exists(Box::new(Query::Filter { pred: sub3(), input: Box::new(Query::Table(0)) }))
}

/// `.. AND NOT EXISTS (..)`.
pub open spec fn p44() -> Pred { and(p28(), Pred::Not(Box::new(ex3_pred()))) }

/// `.. AND s_nationkey = n_nationkey`.
pub open spec fn p48() -> Pred { and(p44(), c_eq(3, 32)) }

/// The WHERE condition: `.. AND n_name = $1`.
pub open spec fn q21_pred(ps: Seq<Literal>) -> Pred {
    and(p48(), Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(33), b: Expr::Lit(ps[0]) })
}

/// FROM supplier, lineitem, orders, nation.
pub open spec fn q21_from() -> Query {
    Query::Product {
        left: Box::new(Query::Product {
            left: Box::new(Query::Product { left: Box::new(Query::Table(5)), right: Box::new(Query::Table(0)) }),
            right: Box::new(Query::Table(1)),
        }),
        right: Box::new(Query::Table(6)),
    }
}

pub open spec fn q21_filter(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: q21_pred(ps), input: Box::new(q21_from()) }
}

/// GROUP BY s_name.
pub open spec fn q21_gkeys() -> Seq<Expr> {
    seq![Expr::Col(1)]
}

/// COUNT(*).
pub open spec fn q21_aggs() -> Seq<Agg> {
    seq![Agg::CountStar]
}

pub open spec fn q21_body(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: q21_gkeys(), aggs: q21_aggs(), input: Box::new(q21_filter(ps)) }
}

/// The statement is these pieces, ordered by `cand::q21_keys` with LIMIT 100.
pub proof fn lemma_q21_shape(ps: Seq<Literal>)
    ensures
        query_spec_at(ps).body == q21_body(ps),
        query_spec_at(ps).keys == q21_keys(),
        query_spec_at(ps).limit == Some(100nat),
        query_spec_at(ps).offset == 0,
{
    assert(query_spec_at(ps).keys =~= q21_keys());
    assert(f_text() =~= seq![70u8]);
}

// ------------------------------------------------------------------------------------------------ per-row meaning

/// A lineitem row of the table: 16 columns, l_orderkey and l_suppkey integers, the dates dates.
pub open spec fn lrow_typed(r: Row) -> bool {
    &&& r.len() == 16
    &&& r[0] is Int
    &&& r[2] is Int
    &&& r[11] is Date
    &&& r[12] is Date
}

/// Every row of the lineitem table is typed.
pub open spec fn lines_typed(db: Database) -> bool {
    &&& db.tables.len() == 8
    &&& forall|i: int| 0 <= i < db.tables[0].len() ==> #[trigger] lrow_typed(db.tables[0][i])
}

/// Lineitem row `r` has order key `k` and a supplier other than `s`.
pub open spec fn sub2_hit(r: Row, k: int, s: int) -> bool {
    ival(r[0]) == k && ival(r[2]) != s
}

/// ... and is late.
pub open spec fn sub3_hit(r: Row, k: int, s: int) -> bool {
    sub2_hit(r, k, s) && ival(r[12]) > ival(r[11])
}

/// The EXISTS: some lineitem row of order key `k` has a supplier other than `s`.
pub open spec fn ex2_db(db: Database, k: int, s: int) -> bool {
    exists|i: int| 0 <= i < db.tables[0].len() && #[trigger] sub2_hit(db.tables[0][i], k, s)
}

/// The NOT EXISTS subquery's rows: some late lineitem row of order key `k` has a supplier other than `s`.
pub open spec fn ex3_db(db: Database, k: int, s: int) -> bool {
    exists|i: int| 0 <= i < db.tables[0].len() && #[trigger] sub3_hit(db.tables[0][i], k, s)
}

/// The FROM row's read columns are non-NULL values of their types.
pub open spec fn env_typed(env: Row) -> bool {
    &&& env.len() == 36
    &&& env[0] is Int && env[1] is Text && env[3] is Int && env[7] is Int && env[9] is Int
    &&& env[18] is Date && env[19] is Date
    &&& env[23] is Int && env[25] is Text
    &&& env[32] is Int && env[33] is Text
}

/// The WHERE condition on a FROM row (two-valued).
pub open spec fn qual_env(db: Database, nm: Seq<u8>, env: Row) -> bool {
    &&& ival(env[0]) == ival(env[9])
    &&& ival(env[23]) == ival(env[7])
    &&& tval(env[25]) == f_text()
    &&& ival(env[19]) > ival(env[18])
    &&& ex2_db(db, ival(env[7]), ival(env[9]))
    &&& !ex3_db(db, ival(env[7]), ival(env[9]))
    &&& ival(env[3]) == ival(env[32])
    &&& tval(env[33]) == nm
}

/// Integer or date columns `a`, `b` of `env` compare as their integers.
proof fn lemma_cmp_cols(db: Database, env: Row, op: CmpOp, a: nat, b: nat)
    requires
        a < env.len(), b < env.len(),
        (env[a as int] is Int && env[b as int] is Int) || (env[a as int] is Date && env[b as int] is Date),
    ensures
        eval_pred(db, env, c_op(op, a, b)) == Ok::<Truth, SqlError>(truth_of(int_cmp(op, ival(env[a as int]), ival(env[b as int])))),
{
    lemma_expr_col(db, env, a);
    lemma_expr_col(db, env, b);
    let (va, vb) = (env[a as int], env[b as int]);
    if va is Int {
        lemma_compare_int(ival(va), ival(vb));
    } else {
        lemma_compare_date(ival(va), ival(vb));
    }
    lemma_pred_cmp(db, env, op, Expr::Col(a), Expr::Col(b), va, vb, ival(va), ival(vb));
}

/// The subqueries' conditions on `env ++ r`.
proof fn lemma_sub_row(db: Database, env: Row, r: Row)
    requires env_typed(env), lrow_typed(r),
    ensures
        eval_pred(db, env + r, sub2()) == Ok::<Truth, SqlError>(truth_of(sub2_hit(r, ival(env[7]), ival(env[9])))),
        eval_pred(db, env + r, sub3()) == Ok::<Truth, SqlError>(truth_of(sub3_hit(r, ival(env[7]), ival(env[9])))),
{
    let e = env + r;
    assert(e.len() == 52);
    assert(e[36] == r[0] && e[38] == r[2] && e[47] == r[11] && e[48] == r[12]);
    assert(e[7] == env[7] && e[9] == env[9]);
    lemma_cmp_cols(db, e, CmpOp::Eq, 36, 7);
    lemma_cmp_cols(db, e, CmpOp::Ne, 38, 9);
    lemma_cmp_cols(db, e, CmpOp::Gt, 48, 47);
    assert(c_eq(36, 7) == c_op(CmpOp::Eq, 36, 7));
    lemma_pred_and(db, e, c_eq(36, 7), c_op(CmpOp::Ne, 38, 9), ival(r[0]) == ival(env[7]), ival(r[2]) != ival(env[9]));
    lemma_pred_and(db, e, sub2(), c_op(CmpOp::Gt, 48, 47), sub2_hit(r, ival(env[7]), ival(env[9])), ival(r[12]) > ival(r[11]));
}

/// The EXISTS is `ex2_db`.
pub proof fn lemma_exists2(db: Database, env: Row)
    requires env_typed(env), lines_typed(db),
    ensures eval_pred(db, env, ex2_pred()) == Ok::<Truth, SqlError>(truth_of(ex2_db(db, ival(env[7]), ival(env[9])))),
{
    let t = db.tables[0];
    let (k, s) = (ival(env[7]), ival(env[9]));
    assert forall|i: int| 0 <= i < t.len() implies #[trigger] eval_pred(db, env + t[i], sub2()) is Ok by {
        assert(lrow_typed(t[i]));
        lemma_sub_row(db, env, t[i]);
    }
    lemma_exists_filter_table(db, env, sub2(), 0);
    let w = exists|i: int| 0 <= i < t.len() && #[trigger] eval_pred(db, env + t[i], sub2()) == Ok::<Truth, SqlError>(Truth::True);
    if w {
        let i = choose|i: int| 0 <= i < t.len() && #[trigger] eval_pred(db, env + t[i], sub2()) == Ok::<Truth, SqlError>(Truth::True);
        assert(lrow_typed(t[i]));
        lemma_sub_row(db, env, t[i]);
        assert(sub2_hit(t[i], k, s));
    }
    if ex2_db(db, k, s) {
        let i = choose|i: int| 0 <= i < t.len() && #[trigger] sub2_hit(t[i], k, s);
        assert(lrow_typed(t[i]));
        lemma_sub_row(db, env, t[i]);
        assert(eval_pred(db, env + t[i], sub2()) == Ok::<Truth, SqlError>(Truth::True));
    }
}

/// The NOT EXISTS subquery's EXISTS is `ex3_db`.
pub proof fn lemma_exists3(db: Database, env: Row)
    requires env_typed(env), lines_typed(db),
    ensures eval_pred(db, env, ex3_pred()) == Ok::<Truth, SqlError>(truth_of(ex3_db(db, ival(env[7]), ival(env[9])))),
{
    let t = db.tables[0];
    let (k, s) = (ival(env[7]), ival(env[9]));
    assert forall|i: int| 0 <= i < t.len() implies #[trigger] eval_pred(db, env + t[i], sub3()) is Ok by {
        assert(lrow_typed(t[i]));
        lemma_sub_row(db, env, t[i]);
    }
    lemma_exists_filter_table(db, env, sub3(), 0);
    let w = exists|i: int| 0 <= i < t.len() && #[trigger] eval_pred(db, env + t[i], sub3()) == Ok::<Truth, SqlError>(Truth::True);
    if w {
        let i = choose|i: int| 0 <= i < t.len() && #[trigger] eval_pred(db, env + t[i], sub3()) == Ok::<Truth, SqlError>(Truth::True);
        assert(lrow_typed(t[i]));
        lemma_sub_row(db, env, t[i]);
        assert(sub3_hit(t[i], k, s));
    }
    if ex3_db(db, k, s) {
        let i = choose|i: int| 0 <= i < t.len() && #[trigger] sub3_hit(t[i], k, s);
        assert(lrow_typed(t[i]));
        lemma_sub_row(db, env, t[i]);
        assert(eval_pred(db, env + t[i], sub3()) == Ok::<Truth, SqlError>(Truth::True));
    }
}

/// The WHERE condition on a typed FROM row, with `$1` the text `nm`.
pub proof fn lemma_pred_eval(db: Database, env: Row, ps: Seq<Literal>, nm: Seq<u8>)
    requires
        env_typed(env),
        lines_typed(db),
        ps.len() >= 1,
        ps[0] == Literal::Text(nm),
    ensures
        eval_pred(db, env, q21_pred(ps)) == Ok::<Truth, SqlError>(truth_of(qual_env(db, nm, env))),
{
    let (k, s) = (ival(env[7]), ival(env[9]));
    lemma_cmp_cols(db, env, CmpOp::Eq, 0, 9);
    lemma_cmp_cols(db, env, CmpOp::Eq, 23, 7);
    assert(c_eq(0, 9) == c_op(CmpOp::Eq, 0, 9) && c_eq(23, 7) == c_op(CmpOp::Eq, 23, 7));
    let b4 = ival(env[0]) == ival(env[9]);
    let b7 = ival(env[23]) == ival(env[7]);
    lemma_pred_and(db, env, c_eq(0, 9), c_eq(23, 7), b4, b7);
    lemma_expr_col(db, env, 25);
    lemma_expr_text(db, env, f_text());
    lemma_pred_text_cmp(db, env, CmpOp::Eq, Expr::Col(25), Expr::Lit(Literal::Text(f_text())), tval(env[25]), f_text());
    let b12 = tval(env[25]) == f_text();
    lemma_pred_and(db, env, p8(), Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(25), b: Expr::Lit(Literal::Text(f_text())) }, b4 && b7, b12);
    lemma_cmp_cols(db, env, CmpOp::Gt, 19, 18);
    let b16 = ival(env[19]) > ival(env[18]);
    lemma_pred_and(db, env, p13(), c_op(CmpOp::Gt, 19, 18), b4 && b7 && b12, b16);
    lemma_exists2(db, env);
    let b27 = ex2_db(db, k, s);
    lemma_pred_and(db, env, p17(), ex2_pred(), b4 && b7 && b12 && b16, b27);
    lemma_exists3(db, env);
    let b42 = ex3_db(db, k, s);
    lemma_pred_not(db, env, ex3_pred(), b42);
    lemma_pred_and(db, env, p28(), Pred::Not(Box::new(ex3_pred())), b4 && b7 && b12 && b16 && b27, !b42);
    lemma_cmp_cols(db, env, CmpOp::Eq, 3, 32);
    assert(c_eq(3, 32) == c_op(CmpOp::Eq, 3, 32));
    let b47 = ival(env[3]) == ival(env[32]);
    lemma_pred_and(db, env, p44(), c_eq(3, 32), b4 && b7 && b12 && b16 && b27 && !b42, b47);
    lemma_expr_col(db, env, 33);
    lemma_expr_text(db, env, nm);
    lemma_pred_text_cmp(db, env, CmpOp::Eq, Expr::Col(33), Expr::Lit(Literal::Text(nm)), tval(env[33]), nm);
    let b52 = tval(env[33]) == nm;
    lemma_pred_and(db, env, p48(), Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(33), b: Expr::Lit(ps[0]) },
        b4 && b7 && b12 && b16 && b27 && !b42 && b47, b52);
}

} // verus!
