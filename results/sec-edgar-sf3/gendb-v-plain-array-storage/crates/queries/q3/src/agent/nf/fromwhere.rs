//! The FROM/WHERE block `num JOIN sub ON adsh WHERE uom = $1 AND fy = $2 AND value IS NOT NULL` of both query
//! blocks, at any outer context of length `d` (0 at top level, 3 inside the HAVING subquery): it evaluates to the
//! rows of the product `num x sub` (each row `num_i ++ sub_j`, 29 values) that satisfy `jq`. The WHERE condition is
//! three-valued (a NULL fy gives `Unknown`); a row is kept exactly when it is `True`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::text::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::exec::relational::domain::{filter_results, lemma_eval_filter};
use crate::bridge::collect::lemma_collect_all;
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::link::join::{keep, lemma_keep_members, lemma_keep_keep, lemma_keep_ext, lemma_product_index};
use crate::agent::nf::ast::*;

verus! {

/// The binding `ps` is the text `p0` and the int4 `p1`.
pub open spec fn binding(ps: Seq<Literal>, p0: Seq<u8>, p1: int) -> bool {
    &&& ps == seq![Literal::Text(p0), Literal::Int { v: p1, kind: IntKind::Int4 }]
    &&& int_in_range(IntKind::Int4, p1)
}

/// The join and WHERE condition on a joined row `num_i ++ sub_j`.
pub open spec fn jq(p0: Seq<u8>, p1: int, x: Row) -> bool {
    x[0] == x[9] && x[5] == Val::Text(p0) && x[19] == Val::Int(p1)
}

pub open spec fn jq_fn(p0: Seq<u8>, p1: int) -> spec_fn(Row) -> bool {
    |x: Row| jq(p0, p1, x)
}

/// The columns of a num row the query reads, by kind.
pub open spec fn shape_num(r: Row) -> bool {
    r.len() == 9 && r[0] is Text && r[5] is Text && r[7] is Num
}

/// The columns of a sub row the query reads, by kind (fy is nullable).
pub open spec fn shape_sub(r: Row) -> bool {
    r.len() == 20 && r[0] is Text && r[1] is Int && r[2] is Text && (r[10] is Null || r[10] is Int)
}

/// A joined row `num_i ++ sub_j`.
pub open spec fn shape_joined(x: Row) -> bool {
    &&& x.len() == 29
    &&& x[0] is Text && x[5] is Text && x[7] is Num
    &&& x[9] is Text && x[10] is Int && x[11] is Text && (x[19] is Null || x[19] is Int)
}

/// Every row of the two tables has its shape.
pub open spec fn tables_shaped(db: Database) -> bool {
    &&& db.tables.len() >= 2
    &&& forall|i: int| 0 <= i < db.tables[1].len() ==> shape_num(#[trigger] db.tables[1][i])
    &&& forall|j: int| 0 <= j < db.tables[0].len() ==> shape_sub(#[trigger] db.tables[0][j])
}

/// `num x sub`.
pub open spec fn joined(db: Database) -> Seq<Row> {
    product_rows(db.tables[1], db.tables[0])
}

pub proof fn lemma_joined_shape(a: Row, b: Row)
    requires shape_num(a), shape_sub(b),
    ensures
        shape_joined(a + b),
        (a + b)[0] == a[0], (a + b)[5] == a[5], (a + b)[7] == a[7],
        (a + b)[9] == b[0], (a + b)[10] == b[1], (a + b)[11] == b[2], (a + b)[19] == b[10],
{
}

/// Every row of the product is a joined row; row `i * |sub| + j` is `num_i ++ sub_j`.
pub proof fn lemma_joined_rows(db: Database)
    requires tables_shaped(db),
    ensures
        joined(db).len() == db.tables[1].len() * db.tables[0].len(),
        forall|p: int| 0 <= p < joined(db).len() ==> shape_joined(#[trigger] joined(db)[p]),
{
    let (a, b) = (db.tables[1], db.tables[0]);
    lemma_product_index(a, b);
    assert forall|p: int| 0 <= p < joined(db).len() implies shape_joined(#[trigger] joined(db)[p]) by {
        let n = b.len() as int;
        assert(n > 0) by (nonlinear_arith) requires 0 <= p < a.len() * n, a.len() >= 0, n >= 0;
        let i = p / n;
        let j = p % n;
        assert(p == i * n + j && 0 <= j < n) by (nonlinear_arith) requires n > 0, i == p / n, j == p % n;
        assert(0 <= i < a.len()) by (nonlinear_arith) requires 0 <= p < a.len() * n, n > 0, i == p / n;
        assert(joined(db)[i * n + j] == a[i] + b[j]);
        lemma_joined_shape(a[i], b[j]);
    }
}

/// One comparison node.
pub proof fn lemma_cmp_node(db: Database, env: Row, op: CmpOp, a: Expr, b: Expr, va: Val, vb: Val)
    requires eval_expr(db, env, a) == Ok::<Val, SqlError>(va), eval_expr(db, env, b) == Ok::<Val, SqlError>(vb),
    ensures eval_pred(db, env, Pred::Cmp { op, a, b }) == cmp_truth(op, va, vb),
{
}

/// One conjunction node (Kleene).
pub proof fn lemma_and_node(db: Database, env: Row, p: Pred, q: Pred, tp: Truth, tq: Truth)
    requires eval_pred(db, env, p) == Ok::<Truth, SqlError>(tp), eval_pred(db, env, q) == Ok::<Truth, SqlError>(tq),
    ensures eval_pred(db, env, Pred::And(Box::new(p), Box::new(q))) == Ok::<Truth, SqlError>(truth_and(tp, tq)),
{
}

/// `NOT (e IS NULL)` on a non-NULL value.
pub proof fn lemma_not_null_node(db: Database, env: Row, e: Expr, v: Val)
    requires eval_expr(db, env, e) == Ok::<Val, SqlError>(v), !(v is Null),
    ensures eval_pred(db, env, Pred::Not(Box::new(Pred::IsNull(e)))) == Ok::<Truth, SqlError>(Truth::True),
{
    assert(eval_pred(db, env, Pred::IsNull(e)) == Ok::<Truth, SqlError>(Truth::False));
}

/// A column of the environment.
pub proof fn lemma_col_node(db: Database, env: Row, k: nat)
    requires k < env.len(),
    ensures eval_expr(db, env, Expr::Col(k)) == Ok::<Val, SqlError>(env[k as int]),
{
}

/// A literal.
pub proof fn lemma_lit_node(db: Database, env: Row, l: Literal, v: Val)
    requires lit_val(l) == Ok::<Val, SqlError>(v),
    ensures eval_expr(db, env, Expr::Lit(l)) == Ok::<Val, SqlError>(v),
{
}

/// Text equality: `True` or `False` as the bytes are equal.
pub proof fn lemma_text_eq(a: Seq<u8>, b: Seq<u8>)
    ensures cmp_truth(CmpOp::Eq, Val::Text(a), Val::Text(b)) == Ok::<Truth, SqlError>(truth_of(a == b)),
{
    lemma_lex_cmp_zero(a, b);
}

/// `n.adsh = s.adsh` on a joined row is the byte equality of the two adsh values.
pub proof fn lemma_join_truth(db: Database, ctx: Row, x: Row)
    requires shape_joined(x),
    ensures eval_pred(db, ctx + x, join_pred(ctx.len())) == Ok::<Truth, SqlError>(truth_of(x[0] == x[9])),
{
    hide(eval_pred);
    hide(eval_expr);
    let env = ctx + x;
    let d = ctx.len();
    assert(env[(0 + d) as int] == x[0]);
    assert(env[(9 + d) as int] == x[9]);
    lemma_col_node(db, env, 0 + d);
    lemma_col_node(db, env, 9 + d);
    lemma_cmp_node(db, env, CmpOp::Eq, Expr::Col(0 + d), Expr::Col(9 + d), x[0], x[9]);
    lemma_text_eq(x[0]->Text_0, x[9]->Text_0);
}

/// `fy = $2`: `Unknown` for a NULL fy, otherwise `True` or `False`.
pub proof fn lemma_fy_truth(fy: Val, p1: int)
    requires fy is Null || fy is Int,
    ensures
        cmp_truth(CmpOp::Eq, fy, Val::Int(p1)) is Ok,
        (cmp_truth(CmpOp::Eq, fy, Val::Int(p1))->Ok_0 is True) == (fy == Val::Int(p1)),
{
}

/// The WHERE condition on a joined row is `True` exactly when uom is `$1` and fy is `$2` (a NULL fy gives
/// `Unknown`).
pub proof fn lemma_where_truth(db: Database, ctx: Row, ps: Seq<Literal>, p0: Seq<u8>, p1: int, x: Row)
    requires binding(ps, p0, p1), shape_joined(x),
    ensures
        eval_pred(db, ctx + x, where_pred(ctx.len(), ps)) is Ok,
        (eval_pred(db, ctx + x, where_pred(ctx.len(), ps))->Ok_0 is True) == (x[5] == Val::Text(p0) && x[19] == Val::Int(p1)),
{
    hide(eval_pred);
    hide(eval_expr);
    let env = ctx + x;
    let d = ctx.len();
    assert(env[(5 + d) as int] == x[5]);
    assert(env[(19 + d) as int] == x[19]);
    assert(env[(7 + d) as int] == x[7]);
    assert(ps[0] == Literal::Text(p0));
    assert(ps[1] == Literal::Int { v: p1, kind: IntKind::Int4 });
    lemma_col_node(db, env, 5 + d);
    lemma_col_node(db, env, 19 + d);
    lemma_col_node(db, env, 7 + d);
    lemma_lit_node(db, env, ps[0], Val::Text(p0));
    lemma_lit_node(db, env, ps[1], Val::Int(p1));
    let c_uom = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(5 + d), b: Expr::Lit(ps[0]) };
    let c_fy = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(19 + d), b: Expr::Lit(ps[1]) };
    let nn = Pred::Not(Box::new(Pred::IsNull(Expr::Col(7 + d))));
    lemma_cmp_node(db, env, CmpOp::Eq, Expr::Col(5 + d), Expr::Lit(ps[0]), x[5], Val::Text(p0));
    lemma_text_eq(x[5]->Text_0, p0);
    lemma_cmp_node(db, env, CmpOp::Eq, Expr::Col(19 + d), Expr::Lit(ps[1]), x[19], Val::Int(p1));
    lemma_fy_truth(x[19], p1);
    let t_uom = truth_of(x[5] == Val::Text(p0));
    let t_fy = cmp_truth(CmpOp::Eq, x[19], Val::Int(p1))->Ok_0;
    lemma_and_node(db, env, c_uom, c_fy, t_uom, t_fy);
    lemma_not_null_node(db, env, Expr::Col(7 + d), x[7]);
    lemma_and_node(db, env, Pred::And(Box::new(c_uom), Box::new(c_fy)), nn, truth_and(t_uom, t_fy), Truth::True);
    assert(where_pred(d, ps) == Pred::And(Box::new(Pred::And(Box::new(c_uom), Box::new(c_fy))), Box::new(nn)));
}

/// `keep_true` of truths whose `True` cases are exactly `h` is `keep` of `h`.
pub proof fn lemma_keep_true3(rows: Seq<Row>, truths: Seq<Truth>, h: spec_fn(Row) -> bool)
    requires
        truths.len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] truths[i] is True) == h(rows[i]),
    ensures keep_true(rows, truths) == keep(rows, h),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let (ri, ti) = (rows.drop_last(), truths.drop_last());
        assert forall|i: int| 0 <= i < ri.len() implies (#[trigger] ti[i] is True) == h(ri[i]) by {
            assert(ti[i] == truths[i] && ri[i] == rows[i]);
        }
        lemma_keep_true3(ri, ti, h);
        assert(truths.last() == truths[truths.len() - 1]);
    }
}

/// A WHERE condition over an input that evaluates to `rows`, `True` exactly on the rows satisfying `h`.
pub proof fn lemma_filter_rows3(db: Database, ctx: Row, pred: Pred, input: Query, rows: Seq<Row>, h: spec_fn(Row) -> bool)
    requires
        eval_query(db, ctx, input) == Ok::<Relation, SqlError>(rows),
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] eval_pred(db, ctx + rows[i], pred)) is Ok
            && (eval_pred(db, ctx + rows[i], pred)->Ok_0 is True) == h(rows[i]),
    ensures
        eval_query(db, ctx, Query::Filter { pred, input: Box::new(input) }) == Ok::<Relation, SqlError>(keep(rows, h)),
{
    lemma_eval_filter(db, ctx, pred, Box::new(input));
    let rs = filter_results(db, ctx, rows, pred);
    let truths = Seq::new(rows.len(), |i: int| rs[i]->Ok_0);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        assert(rs[i] == eval_pred(db, ctx + rows[i], pred));
    }
    lemma_collect_all(rs, truths);
    assert forall|i: int| 0 <= i < rows.len() implies (#[trigger] truths[i] is True) == h(rows[i]) by {
        assert(rs[i] == eval_pred(db, ctx + rows[i], pred));
    }
    lemma_keep_true3(rows, truths, h);
}

/// The FROM/WHERE block at a context of length 0 or 3 is the joined rows satisfying `jq`.
pub proof fn lemma_where_rows(db: Database, ctx: Row, ps: Seq<Literal>, p0: Seq<u8>, p1: int)
    requires
        binding(ps, p0, p1),
        ctx.len() == 0 || ctx.len() == 3,
        tables_shaped(db),
    ensures
        eval_query(db, ctx, where_q(ctx.len(), ps)) == Ok::<Relation, SqlError>(keep(joined(db), jq_fn(p0, p1))),
{
    let d = ctx.len();
    let p = joined(db);
    lemma_joined_rows(db);
    // FROM: the product of the two tables (a table does not read the context).
    assert(eval_query(db, ctx, Query::Table(1)) == Ok::<Relation, SqlError>(db.tables[1]));
    assert(eval_query(db, ctx, Query::Table(0)) == Ok::<Relation, SqlError>(db.tables[0]));
    assert(eval_query(db, ctx, from_q()) == Ok::<Relation, SqlError>(p));
    // ON: adsh equality.
    let h1 = |x: Row| x[0] == x[9];
    assert forall|i: int| 0 <= i < p.len() implies (#[trigger] eval_pred(db, ctx + p[i], join_pred(d))) is Ok
        && (eval_pred(db, ctx + p[i], join_pred(d))->Ok_0 is True) == h1(p[i]) by {
        lemma_join_truth(db, ctx, p[i]);
    }
    lemma_filter_rows3(db, ctx, join_pred(d), from_q(), p, h1);
    // WHERE over the joined rows.
    let k1 = keep(p, h1);
    let h2 = |x: Row| x[5] == Val::Text(p0) && x[19] == Val::Int(p1);
    lemma_keep_members(p, h1);
    assert forall|i: int| 0 <= i < k1.len() implies (#[trigger] eval_pred(db, ctx + k1[i], where_pred(d, ps))) is Ok
        && (eval_pred(db, ctx + k1[i], where_pred(d, ps))->Ok_0 is True) == h2(k1[i]) by {
        assert(p.contains(k1[i]));
        let m = choose|m: int| 0 <= m < p.len() && p[m] == k1[i];
        assert(shape_joined(p[m]));
        lemma_where_truth(db, ctx, ps, p0, p1, k1[i]);
    }
    lemma_filter_rows3(db, ctx, where_pred(d, ps), join_q(d), k1, h2);
    lemma_keep_keep(p, h1, h2);
    lemma_keep_ext(p, |x: Row| h1(x) && h2(x), jq_fn(p0, p1));
}

} // verus!
