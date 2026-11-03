//! The statement's meaning on a database whose `num` and `sub` tables are the flat parts (`db_ok`): the body
//! evaluates to `norm(c, n)`, one row `[sub.name, tag, value]` per `num` row with `body_ok`, in row order.
//!
//! Proof outline (`lemma_body`): the FROM tree `((num x sub) WHERE n.adsh = s.adsh) x m` and the two WHERE
//! conditions evaluate to the product rows kept by the conjunction `full_cond` of the three conditions
//! (`link::join` composition; conditions that are not two-valued are handled by `lemma_filter_true`). By
//! associativity the product is `num x (sub x m)`; for one `num` row the condition splits into a condition on the
//! `sub` row and one on the `m` row (`lemma_split_cond`), each of which keeps at most one row (the `sub` key; the
//! group keys are distinct), so each `num` row contributes its answer row exactly when it is `body_ok`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::scalar::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::bridge::collect::lemma_collect_all;
use crate::bridge::relation::{is_concat, lemma_product_rows_elems};
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::exec::relational::domain::lemma_collect_pointwise;
use crate::link::query::*;
use crate::link::join::*;
use crate::link::expr::*;
use crate::stores::flat_num::interface as ni;
use crate::stores::flat_sub::interface as si;
use crate::agent::spec::*;
use crate::agent::group::*;

verus! {

// ------------------------------------------------------------------------------------------------ AST nodes

pub open spec fn p_join() -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) }
}

pub open spec fn q_ns() -> Query {
    Query::Filter { pred: p_join(), input: Box::new(Query::Product { left: Box::new(Query::Table(1)), right: Box::new(Query::Table(0)) }) }
}

pub open spec fn p_grp(l1: Literal) -> Pred {
    Pred::And(
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(5), b: Expr::Lit(l1) }),
        Box::new(Pred::Not(Box::new(Pred::IsNull(Expr::Col(7))))),
    )
}

pub open spec fn q_grp_input(l1: Literal) -> Query {
    Query::Filter { pred: p_grp(l1), input: Box::new(Query::Table(1)) }
}

pub open spec fn q_grp(l1: Literal) -> Query {
    Query::GroupBy { keys: seq![Expr::Col(0), Expr::Col(1)], aggs: seq![Agg::Max(Expr::Col(7))], input: Box::new(q_grp_input(l1)) }
}

pub open spec fn p_m() -> Pred {
    Pred::And(
        Box::new(Pred::And(
            Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(29) }),
            Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(1), b: Expr::Col(30) }),
        )),
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(7), b: Expr::Col(31) }),
    )
}

pub open spec fn p_w(l1: Literal, l2: Literal) -> Pred {
    Pred::And(
        Box::new(Pred::And(
            Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(5), b: Expr::Lit(l1) }),
            Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(19), b: Expr::Lit(l2) }),
        )),
        Box::new(Pred::Not(Box::new(Pred::IsNull(Expr::Col(7))))),
    )
}

pub open spec fn q_joined(l1: Literal) -> Query {
    Query::Product { left: Box::new(q_ns()), right: Box::new(q_grp(l1)) }
}

pub open spec fn q_m(l1: Literal) -> Query {
    Query::Filter { pred: p_m(), input: Box::new(q_joined(l1)) }
}

pub open spec fn q_where(l1: Literal, l2: Literal) -> Query {
    Query::Filter { pred: p_w(l1, l2), input: Box::new(q_m(l1)) }
}

pub open spec fn out_cols() -> Seq<nat> {
    seq![11nat, 1, 7]
}

pub open spec fn q_body(l1: Literal, l2: Literal) -> Query {
    Query::Project { exprs: col_exprs(out_cols()), input: Box::new(q_where(l1, l2)) }
}

pub open spec fn order_keys() -> Seq<OrderKey> {
    seq![
        OrderKey { col: 2, desc: true, nulls_first: true },
        OrderKey { col: 0, desc: false, nulls_first: false },
        OrderKey { col: 1, desc: false, nulls_first: false },
    ]
}

/// The generated statement, named node by node.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures
        crate::query::query_spec_at(ps).body == q_body(ps[0], ps[1]),
        crate::query::query_spec_at(ps).keys == order_keys(),
        crate::query::query_spec_at(ps).limit == Some(100nat),
        crate::query::query_spec_at(ps).offset == 0,
{
    assert(col_exprs(out_cols()) =~= seq![Expr::Col(11), Expr::Col(1), Expr::Col(7)]);
}

// ------------------------------------------------------------------------------------------------ the database

/// `db`'s `num` and `sub` tables are the rows of the parts of `c`, and `sub`'s adsh identifies its rows.
pub open spec fn db_ok(db: Database, c: Ctx) -> bool {
    &&& ctx_ok(c)
    &&& db.tables.len() == 4
    &&& db.tables[1].len() == c.n
    &&& db.tables[0].len() == c.m
    &&& forall|i: int| 0 <= i < c.n ==> #[trigger] db.tables[1][i] == nrow(c, i)
    &&& forall|s: int| 0 <= s < c.m ==> #[trigger] db.tables[0][s] == srow(c, s)
    &&& sub_key(c)
}

/// The binding: `$1` is the text `c.pv`, `$2` the int4 `c.fy`.
pub open spec fn lits_ok(c: Ctx, l1: Literal, l2: Literal) -> bool {
    &&& l1 == Literal::Text(c.pv)
    &&& l2 == Literal::Int { v: c.fy, kind: IntKind::Int4 }
    &&& int_in_range(IntKind::Int4, c.fy)
}

#[verifier::opaque]
pub open spec fn nrow(c: Ctx, i: int) -> Row {
    ni::row_at(c.np, i)
}

#[verifier::opaque]
pub open spec fn srow(c: Ctx, s: int) -> Row {
    si::row_at(c.sp, s)
}

/// The `sub` row matching `num` row `i` (unique by the `sub` key when it exists).
pub open spec fn sub_of(c: Ctx, i: int) -> int {
    choose|s: int| sub_match(c, i, s)
}

/// The answer row of `num` row `i`: `[sub.name, tag, value]`.
pub open spec fn out_row(c: Ctx, i: int) -> Row {
    seq![Val::Text(sname_text(c, sub_of(c, i))), Val::Text(tag_text(c, i)), (Val::Num { coeff: coeff(c, i), scale: 4 })]
}

/// `out_row` as a function.
pub open spec fn out_p(c: Ctx) -> spec_fn(int) -> Row {
    |i: int| out_row(c, i)
}

/// The answer rows of rows `0..k`, in row order.
pub open spec fn norm(c: Ctx, k: int) -> Seq<Row>
    decreases k,
{
    if k <= 0 {
        Seq::empty()
    } else {
        norm(c, k - 1) + if body_ok(c, k - 1) { seq![out_row(c, k - 1)] } else { Seq::<Row>::empty() }
    }
}

/// The value cells of the `num` and `sub` rows.
pub proof fn lemma_row_cells(c: Ctx, i: int, s: int)
    ensures
        nrow(c, i).len() == 9,
        nrow(c, i)[0] == Val::Text(adsh_text(c, i)),
        nrow(c, i)[1] == Val::Text(tag_text(c, i)),
        nrow(c, i)[5] == Val::Text(uom_text(c, i)),
        nrow(c, i)[7] == (Val::Num { coeff: coeff(c, i), scale: 4 }),
        srow(c, s).len() == 20,
        srow(c, s)[0] == Val::Text(sadsh_text(c, s)),
        srow(c, s)[2] == Val::Text(sname_text(c, s)),
        srow(c, s)[10] == (if fy_valid_seq(c.sp)[s] == 0 { Val::Null } else { Val::Int(fy_seq(c.sp)[s] as int) }),
{
    reveal(nrow);
    reveal(srow);
}

pub proof fn lemma_num_rows_ok(db: Database, c: Ctx)
    requires db_ok(db, c),
    ensures forall|i: int| 0 <= i < db.tables[1].len() ==> num_row_ok(#[trigger] db.tables[1][i]),
{
    assert forall|i: int| 0 <= i < db.tables[1].len() implies num_row_ok(#[trigger] db.tables[1][i]) by {
        lemma_row_cells(c, i, 0);
    }
}

// ------------------------------------------------------------------------------------------------ conditions

/// The text comparison `=` of two text cells.
proof fn lemma_text_eq(db: Database, env: Row, a: nat, b: nat, x: Seq<u8>, y: Seq<u8>)
    requires a < env.len(), b < env.len(), env[a as int] == Val::Text(x), env[b as int] == Val::Text(y),
    ensures eval_pred(db, env, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(a), b: Expr::Col(b) })
        == Ok::<Truth, SqlError>(truth_of(x == y)),
{
    lemma_pred_text_cmp(db, env, CmpOp::Eq, Expr::Col(a), Expr::Col(b), x, y);
}

/// The join condition on `num` row `i` joined with `sub` row `s`.
pub proof fn lemma_join_cond(db: Database, c: Ctx, i: int, s: int)
    ensures eval_pred(db, nrow(c, i) + srow(c, s), p_join()) == Ok::<Truth, SqlError>(truth_of(adsh_text(c, i) == sadsh_text(c, s))),
{
    lemma_row_cells(c, i, s);
    let env = nrow(c, i) + srow(c, s);
    assert(env[0] == nrow(c, i)[0]);
    assert(env[9] == srow(c, s)[0]);
    lemma_text_eq(db, env, 0, 9, adsh_text(c, i), sadsh_text(c, s));
}

/// An `m` row: `[Text a, Text t, Num(mx, 4)]`.
pub open spec fn grow_ok(g: Row) -> bool {
    &&& g.len() == 3
    &&& g[0] is Text
    &&& g[1] is Text
    &&& g[2] is Num
    &&& g[2]->Num_scale == 4
}

/// The `m` condition on `num` row `i`, `sub` row `s` and `m` row `g`: same adsh, same tag, value = max.
pub proof fn lemma_m_cond(db: Database, c: Ctx, i: int, s: int, g: Row)
    requires grow_ok(g),
    ensures eval_pred(db, nrow(c, i) + srow(c, s) + g, p_m()) == Ok::<Truth, SqlError>(truth_of(
        g[0] == Val::Text(adsh_text(c, i)) && g[1] == Val::Text(tag_text(c, i)) && g[2] == nrow(c, i)[7])),
{
    lemma_row_cells(c, i, s);
    let env = nrow(c, i) + srow(c, s) + g;
    assert(env[0] == nrow(c, i)[0]);
    assert(env[1] == nrow(c, i)[1]);
    assert(env[7] == nrow(c, i)[7]);
    assert(env[29] == g[0]);
    assert(env[30] == g[1]);
    assert(env[31] == g[2]);
    let (ga, gt) = (g[0]->Text_0, g[1]->Text_0);
    lemma_text_eq(db, env, 0, 29, adsh_text(c, i), ga);
    lemma_text_eq(db, env, 1, 30, tag_text(c, i), gt);
    let mx = g[2]->Num_coeff;
    lemma_compare_num(coeff(c, i), 4, mx, 4);
    lemma_align_same(coeff(c, i), 4);
    lemma_align_same(mx, 4);
    lemma_expr_col(db, env, 7);
    lemma_expr_col(db, env, 31);
    lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(7), Expr::Col(31), env[7], env[31], coeff(c, i), mx);
    let a1 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(29) };
    let a2 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(1), b: Expr::Col(30) };
    let a3 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(7), b: Expr::Col(31) };
    lemma_pred_and(db, env, a1, a2, adsh_text(c, i) == ga, tag_text(c, i) == gt);
    lemma_pred_and(db, env, Pred::And(Box::new(a1), Box::new(a2)), a3, adsh_text(c, i) == ga && tag_text(c, i) == gt,
        int_cmp(CmpOp::Eq, coeff(c, i), mx));
    assert(g[2] == (Val::Num { coeff: mx, scale: 4 }));
}

/// `NOT (x IS NULL)` on a numeric cell is `True`.
pub proof fn lemma_not_null(db: Database, env: Row, i: nat)
    requires i < env.len(), env[i as int] is Num,
    ensures eval_pred(db, env, Pred::Not(Box::new(Pred::IsNull(Expr::Col(i))))) == Ok::<Truth, SqlError>(Truth::True),
{
    lemma_expr_col(db, env, i);
    assert(eval_pred(db, env, Pred::IsNull(Expr::Col(i))) == Ok::<Truth, SqlError>(Truth::False));
}

/// `s.fy = $2` on an int4-or-NULL cell: `Unknown` for NULL, else equality.
pub proof fn lemma_fy_cmp(db: Database, env: Row, l2: Literal, fy: int, fv: Val)
    requires
        env.len() > 19,
        env[19] == fv,
        fv is Null || fv is Int,
        l2 == (Literal::Int { v: fy, kind: IntKind::Int4 }),
        int_in_range(IntKind::Int4, fy),
    ensures
        eval_pred(db, env, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(19), b: Expr::Lit(l2) })
            == Ok::<Truth, SqlError>(if fv is Null { Truth::Unknown } else { truth_of(fv == Val::Int(fy)) }),
{
    lemma_expr_col(db, env, 19);
    assert(eval_expr(db, env, Expr::Lit(l2)) == Ok::<Val, SqlError>(Val::Int(fy)));
    if fv is Int {
        lemma_compare_int(fv->Int_0, fy);
        lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(19), Expr::Lit(l2), fv, Val::Int(fy), fv->Int_0, fy);
    }
}

/// The WHERE condition on a joined row with `uom` text `u`, a numeric value and `sub.fy` cell `fv`.
#[verifier::spinoff_prover]
pub proof fn lemma_w_env(db: Database, env: Row, l1: Literal, l2: Literal, pv: Seq<u8>, fy: int, u: Seq<u8>, fv: Val)
    requires
        env.len() == 32,
        env[5] == Val::Text(u),
        env[7] is Num,
        env[19] == fv,
        fv is Null || fv is Int,
        l1 == Literal::Text(pv),
        l2 == (Literal::Int { v: fy, kind: IntKind::Int4 }),
        int_in_range(IntKind::Int4, fy),
    ensures
        eval_pred(db, env, p_w(l1, l2)) is Ok,
        (eval_pred(db, env, p_w(l1, l2)) == Ok::<Truth, SqlError>(Truth::True)) == (u == pv && fv == Val::Int(fy)),
{
    let a1 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(5), b: Expr::Lit(l1) };
    let a2 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(19), b: Expr::Lit(l2) };
    let a3 = Pred::Not(Box::new(Pred::IsNull(Expr::Col(7))));
    lemma_expr_col(db, env, 5);
    lemma_expr_text(db, env, pv);
    lemma_pred_text_cmp(db, env, CmpOp::Eq, Expr::Col(5), Expr::Lit(l1), u, pv);
    lemma_fy_cmp(db, env, l2, fy, fv);
    lemma_not_null(db, env, 7);
    let t1 = truth_of(u == pv);
    let t2 = if fv is Null { Truth::Unknown } else { truth_of(fv == Val::Int(fy)) };
    assert(eval_pred(db, env, Pred::And(Box::new(a1), Box::new(a2))) == Ok::<Truth, SqlError>(truth_and(t1, t2)));
    assert(eval_pred(db, env, p_w(l1, l2)) == Ok::<Truth, SqlError>(truth_and(truth_and(t1, t2), Truth::True)));
}

/// The WHERE condition: `True` exactly when `uom = $1` and `sub` row `s` has `fy = $2` (never an error).
pub proof fn lemma_w_cond(db: Database, c: Ctx, l1: Literal, l2: Literal, i: int, s: int, g: Row)
    requires lits_ok(c, l1, l2), g.len() == 3,
    ensures
        eval_pred(db, nrow(c, i) + srow(c, s) + g, p_w(l1, l2)) is Ok,
        (eval_pred(db, nrow(c, i) + srow(c, s) + g, p_w(l1, l2)) == Ok::<Truth, SqlError>(Truth::True))
            == (uom_text(c, i) == c.pv && fy_valid_seq(c.sp)[s] != 0 && fy_seq(c.sp)[s] as int == c.fy),
{
    lemma_row_cells(c, i, s);
    let env = nrow(c, i) + srow(c, s) + g;
    assert(env[5] == nrow(c, i)[5]);
    assert(env[7] == nrow(c, i)[7]);
    assert(env[19] == srow(c, s)[10]);
    lemma_w_env(db, env, l1, l2, c.pv, c.fy, uom_text(c, i), srow(c, s)[10]);
}

// ------------------------------------------------------------------------------------------------ filters

/// SQL WHERE keeps the rows whose truth is `True`.
pub proof fn lemma_keep_true_is(rows: Seq<Row>, truths: Seq<Truth>, f: spec_fn(Row) -> bool)
    requires
        truths.len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] truths[i] is True) == f(rows[i]),
    ensures keep_true(rows, truths) == keep(rows, f),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let (ri, ti) = (rows.drop_last(), truths.drop_last());
        assert forall|i: int| 0 <= i < ri.len() implies (#[trigger] ti[i] is True) == f(ri[i]) by {
            assert(ti[i] == truths[i] && ri[i] == rows[i]);
        }
        lemma_keep_true_is(ri, ti, f);
        assert((truths[rows.len() - 1] is True) == f(rows[rows.len() - 1]));
    }
}

/// A WHERE over kept rows whose condition evaluates without error: the rows kept by both conditions.
pub proof fn lemma_filter_true(db: Database, src: Query, rows: Seq<Row>, f: spec_fn(Row) -> bool, pred: Pred, fh: spec_fn(Row) -> bool)
    requires
        eval_query(db, Seq::empty(), src) == Ok::<Relation, SqlError>(keep(rows, f)),
        forall|i: int| 0 <= i < rows.len() && f(#[trigger] rows[i]) ==> eval_pred(db, rows[i], pred) is Ok,
        forall|i: int| 0 <= i < rows.len() ==> fh(#[trigger] rows[i])
            == (f(rows[i]) && eval_pred(db, rows[i], pred) == Ok::<Truth, SqlError>(Truth::True)),
    ensures
        eval_query(db, Seq::empty(), Query::Filter { pred, input: Box::new(src) }) == Ok::<Relation, SqlError>(keep(rows, fh)),
{
    let kept = keep(rows, f);
    let ctx = Seq::<Val>::empty();
    let h = |x: Row| eval_pred(db, x, pred) == Ok::<Truth, SqlError>(Truth::True);
    lemma_keep_members(rows, f);
    let truths = Seq::new(kept.len(), |i: int| eval_pred(db, kept[i], pred)->Ok_0);
    let prs = Seq::new(kept.len(), |i: int| eval_pred(db, ctx + kept[i], pred));
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        assert(ctx + kept[i] =~= kept[i]);
        assert(rows.contains(kept[i]) && f(kept[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
        assert(f(rows[m]));
    }
    lemma_collect_all(prs, truths);
    lemma_collect_pointwise::<Truth>();
    assert(collect(Seq::new(kept.len(), |i: int| eval_pred(db, ctx + kept[i], pred))) == Ok::<Seq<Truth>, SqlError>(truths));
    assert forall|i: int| 0 <= i < kept.len() implies (#[trigger] truths[i] is True) == h(kept[i]) by {
        assert(rows.contains(kept[i]) && f(kept[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
        assert(f(rows[m]));
    }
    lemma_keep_true_is(kept, truths, h);
    lemma_keep_keep(rows, f, h);
    lemma_keep_ext(rows, |x: Row| f(x) && h(x), fh);
}

// ------------------------------------------------------------------------------------------------ the subquery m

/// The rows of `m` (the group subquery) on `db`.
pub open spec fn m_rows(db: Database, c: Ctx) -> Seq<Row> {
    group_rows_nf(c.pv, db.tables[1])
}

pub proof fn lemma_m_eval(db: Database, c: Ctx, l1: Literal, l2: Literal)
    requires db_ok(db, c), lits_ok(c, l1, l2),
    ensures eval_query(db, Seq::empty(), q_grp(l1)) == Ok::<Relation, SqlError>(m_rows(db, c)),
{
    let xs = db.tables[1];
    let g = gq(c.pv);
    lemma_num_rows_ok(db, c);
    assert forall|i: int| 0 <= i < xs.len() implies (#[trigger] xs[i]).len() == 9 by {
        assert(num_row_ok(xs[i]));
    }
    lemma_proj_identity(xs);
    let cols = id_cols();
    // The WHERE of the subquery is two-valued: `uom = $1` (value is never NULL).
    assert forall|i: int| 0 <= i < xs.len() implies
        eval_pred(db, #[trigger] xs[i], p_grp(l1)) == Ok::<Truth, SqlError>(truth_of((g.qual)(proj(xs[i], cols)))) by {
        lemma_row_cells(c, i, 0);
        lemma_grp_env(db, xs[i], l1, c.pv, uom_text(c, i));
        assert(proj(xs[i], cols) == xs[i]);
    }
    assert(pred_agrees(db, xs, cols, p_grp(l1), g));
    lemma_filter_rows(db, Query::Table(1), xs, cols, p_grp(l1), g);
    lemma_group_query_max(db, xs, q_grp_input(l1), seq![Expr::Col(0), Expr::Col(1)], seq![Agg::Max(Expr::Col(7))], c.pv);
}

/// The WHERE of the group subquery on a `num` row with `uom` text `u` and a numeric value.
#[verifier::spinoff_prover]
pub proof fn lemma_grp_env(db: Database, env: Row, l1: Literal, pv: Seq<u8>, u: Seq<u8>)
    requires env.len() == 9, env[5] == Val::Text(u), env[7] is Num, l1 == Literal::Text(pv),
    ensures eval_pred(db, env, p_grp(l1)) == Ok::<Truth, SqlError>(truth_of(env[5] == Val::Text(pv))),
{
    lemma_expr_col(db, env, 5);
    lemma_expr_text(db, env, pv);
    lemma_pred_text_cmp(db, env, CmpOp::Eq, Expr::Col(5), Expr::Lit(l1), u, pv);
    lemma_expr_col(db, env, 7);
    let a3 = Pred::Not(Box::new(Pred::IsNull(Expr::Col(7))));
    assert(eval_pred(db, env, Pred::IsNull(Expr::Col(7))) == Ok::<Truth, SqlError>(Truth::False));
    assert(eval_pred(db, env, a3) == Ok::<Truth, SqlError>(Truth::True));
    lemma_pred_and(db, env, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(5), b: Expr::Lit(l1) }, a3, u == pv, true);
}

/// Every `m` row is `[adsh, tag, Num(max, 4)]` of a group key, the key of some `uom = $1` row.
pub proof fn lemma_m_rows(db: Database, c: Ctx)
    requires db_ok(db, c),
    ensures
        forall|q: int| 0 <= q < m_rows(db, c).len() ==> grow_ok(#[trigger] m_rows(db, c)[q]),
        gkeys(gq(c.pv), db.tables[1]).no_duplicates(),
        m_rows(db, c).len() == gkeys(gq(c.pv), db.tables[1]).len(),
        forall|q: int| 0 <= q < m_rows(db, c).len() ==> #[trigger] m_rows(db, c)[q]
            == group_row(c.pv, db.tables[1], gkeys(gq(c.pv), db.tables[1])[q]),
        forall|q: int| 0 <= q < m_rows(db, c).len() ==> (#[trigger] gkeys(gq(c.pv), db.tables[1])[q]).len() == 2,
{
    let xs = db.tables[1];
    let g = gq(c.pv);
    let ks = gkeys(g, xs);
    lemma_gkeys(g, xs);
    lemma_num_rows_ok(db, c);
    assert forall|q: int| 0 <= q < ks.len() implies (#[trigger] ks[q]).len() == 2 && ks[q][0] is Text && ks[q][1] is Text by {
        let k = ks[q];
        assert(ks.contains(k));
        lemma_gkeys_witness(g, xs, k);
        let j = choose|j: int| 0 <= j < xs.len() && #[trigger] hit(g, xs[j], k);
        assert(num_row_ok(xs[j]));
        assert(k == seq![xs[j][0], xs[j][1]]);
    }
    assert forall|q: int| 0 <= q < m_rows(db, c).len() implies grow_ok(#[trigger] m_rows(db, c)[q]) by {
        let k = ks[q];
        assert(k.len() == 2 && k[0] is Text && k[1] is Text);
        let r = group_row(c.pv, xs, k);
        assert(r == m_rows(db, c)[q]);
        assert(r[0] == k[0] && r[1] == k[1]);
    }
}

// ------------------------------------------------------------------------------------------------ one num row

/// The condition on the `sub` row of a joined row with `num` row `i`.
pub open spec fn s_cond(c: Ctx, i: int, s: Row) -> bool {
    uom_text(c, i) == c.pv && s[0] == Val::Text(adsh_text(c, i)) && s[10] == Val::Int(c.fy)
}

/// The condition on the `m` row of a joined row with `num` row `i`.
pub open spec fn g_cond(c: Ctx, i: int, g: Row) -> bool {
    g[0] == Val::Text(adsh_text(c, i)) && g[1] == Val::Text(tag_text(c, i)) && g[2] == (Val::Num { coeff: coeff(c, i), scale: 4 })
}

/// The conjunction of the three conditions on a joined row (`num ++ sub ++ m`, 32 columns).
pub open spec fn full_cond(db: Database, l1: Literal, l2: Literal, x: Row) -> bool {
    &&& eval_pred(db, left_of(x, 29), p_join()) == Ok::<Truth, SqlError>(Truth::True)
    &&& eval_pred(db, x, p_m()) == Ok::<Truth, SqlError>(Truth::True)
    &&& eval_pred(db, x, p_w(l1, l2)) == Ok::<Truth, SqlError>(Truth::True)
}

/// For one `num` row the full condition splits into a condition on the `sub` row and one on the `m` row.
pub proof fn lemma_split_cond(db: Database, c: Ctx, l1: Literal, l2: Literal, i: int, s: int, g: Row)
    requires lits_ok(c, l1, l2), grow_ok(g), 0 <= s < c.m,
    ensures full_cond(db, l1, l2, nrow(c, i) + (srow(c, s) + g)) == (s_cond(c, i, srow(c, s)) && g_cond(c, i, g)),
{
    let x = nrow(c, i) + (srow(c, s) + g);
    lemma_row_cells(c, i, s);
    assert(x =~= nrow(c, i) + srow(c, s) + g);
    assert(left_of(x, 29) =~= nrow(c, i) + srow(c, s));
    lemma_join_cond(db, c, i, s);
    lemma_m_cond(db, c, i, s, g);
    lemma_w_cond(db, c, l1, l2, i, s, g);
}

/// Rows kept by a condition that exactly one position satisfies.
pub proof fn lemma_keep_one(rows: Seq<Row>, f: spec_fn(Row) -> bool, j: int)
    requires
        0 <= j < rows.len(),
        f(rows[j]),
        forall|i: int| 0 <= i < rows.len() && i != j ==> !f(#[trigger] rows[i]),
    ensures keep(rows, f) == seq![rows[j]],
    decreases rows.len(),
{
    let d = rows.drop_last();
    if j == rows.len() - 1 {
        assert forall|i: int| 0 <= i < d.len() implies !f(#[trigger] d[i]) by {
            assert(d[i] == rows[i]);
        }
        lemma_keep_none(d, f);
        assert(Seq::<Row>::empty().push(rows.last()) =~= seq![rows[j]]);
    } else {
        assert forall|i: int| 0 <= i < d.len() && i != j implies !f(#[trigger] d[i]) by {
            assert(d[i] == rows[i]);
        }
        assert(d[j] == rows[j]);
        lemma_keep_one(d, f, j);
        assert(!f(rows[rows.len() - 1]));
    }
}

/// The product with an empty right input is empty.
pub proof fn lemma_product_empty_right(a: Seq<Row>)
    ensures product_rows(a, Seq::<Row>::empty()) == Seq::<Row>::empty(),
    decreases a.len(),
{
    if a.len() > 0 {
        lemma_product_empty_right(a.drop_last());
        assert(Seq::<Row>::empty().map_values(|r: Row| a.last() + r) =~= Seq::<Row>::empty());
        assert(Seq::<Row>::empty() + Seq::<Row>::empty() =~= Seq::<Row>::empty());
    }
}

/// The `sub` rows kept for `num` row `i`: its matching row when `uom = $1` and it has one, else none.
pub proof fn lemma_keep_sub(db: Database, c: Ctx, i: int)
    requires db_ok(db, c), 0 <= i < c.n,
    ensures
        keep(db.tables[0], |s: Row| s_cond(c, i, s)) == if uom_text(c, i) == c.pv && has_sub(c, i) {
            seq![srow(c, sub_of(c, i))]
        } else {
            Seq::<Row>::empty()
        },
{
    let rows = db.tables[0];
    let f = |s: Row| s_cond(c, i, s);
    assert forall|s: int| 0 <= s < rows.len() implies #[trigger] f(rows[s]) == (uom_text(c, i) == c.pv && sub_match(c, i, s)) by {
        lemma_row_cells(c, i, s);
        assert(rows[s] == srow(c, s));
    }
    if uom_text(c, i) == c.pv && has_sub(c, i) {
        let s0 = sub_of(c, i);
        assert(sub_match(c, i, s0));
        assert forall|s: int| 0 <= s < rows.len() && s != s0 implies !f(#[trigger] rows[s]) by {
            if f(rows[s]) {
                assert(sub_match(c, i, s));
                assert(sadsh_text(c, s) == sadsh_text(c, s0));
            }
        }
        lemma_keep_one(rows, f, s0);
        assert(rows[s0] == srow(c, s0));
    } else {
        assert forall|s: int| 0 <= s < rows.len() implies !f(#[trigger] rows[s]) by {
            if f(rows[s]) {
                assert(sub_match(c, i, s));
            }
        }
        lemma_keep_none(rows, f);
    }
}

/// The `m` rows kept for `num` row `i` with `uom = $1`: its group's row when its value is the group maximum.
pub proof fn lemma_keep_m(db: Database, c: Ctx, i: int)
    requires db_ok(db, c), 0 <= i < c.n, uom_text(c, i) == c.pv,
    ensures
        keep(m_rows(db, c), |g: Row| g_cond(c, i, g)) == if gmax(c, i) {
            seq![group_row(c.pv, db.tables[1], seq![nrow(c, i)[0], nrow(c, i)[1]])]
        } else {
            Seq::<Row>::empty()
        },
{
    let xs = db.tables[1];
    let gs = gq(c.pv);
    let rows = m_rows(db, c);
    let ks = gkeys(gs, xs);
    let f = |g: Row| g_cond(c, i, g);
    let k = seq![nrow(c, i)[0], nrow(c, i)[1]];
    lemma_m_rows(db, c);
    lemma_num_rows_ok(db, c);
    lemma_row_cells(c, i, 0);
    // The group of row i exists: row i is in it.
    assert(xs[i] == nrow(c, i));
    assert(hit(gs, xs[i], k));
    lemma_gcount_hit(gs, xs, k, i);
    lemma_gkeys(gs, xs);
    assert(ks.contains(k));
    let q0 = choose|q: int| 0 <= q < ks.len() && ks[q] == k;
    // Members of the group of row i are exactly its mates.
    lemma_members_max(c.pv, xs, k);
    assert forall|j: int| 0 <= j < xs.len() implies #[trigger] hit(gs, xs[j], k) == mate(c, i, j) by {
        lemma_row_cells(c, j, 0);
        assert(xs[j] == nrow(c, j));
        if hit(gs, xs[j], k) {
            assert(seq![xs[j][0], xs[j][1]][0] == k[0]);
            assert(seq![xs[j][0], xs[j][1]][1] == k[1]);
        }
        if mate(c, i, j) {
            assert(seq![xs[j][0], xs[j][1]] =~= k);
        }
    }
    let mx = gmaxc(c.pv, xs, k);
    assert(gmax(c, i) == (mx == coeff(c, i))) by {
        assert(vcoeff(xs[i][7]) == coeff(c, i));
        if gmax(c, i) {
            let j = choose|j: int| 0 <= j < xs.len() && #[trigger] hit(gs, xs[j], k) && vcoeff(xs[j][7]) == mx;
            lemma_row_cells(c, j, 0);
            assert(xs[j] == nrow(c, j));
            assert(mate(c, i, j));
        }
        if mx == coeff(c, i) {
            assert forall|j: int| 0 <= j < c.n && #[trigger] mate(c, i, j) implies coeff(c, j) <= coeff(c, i) by {
                lemma_row_cells(c, j, 0);
                assert(xs[j] == nrow(c, j));
                assert(hit(gs, xs[j], k));
            }
        }
    }
    // Only the row of i's group can satisfy the condition.
    assert forall|q: int| 0 <= q < rows.len() && q != q0 implies !f(#[trigger] rows[q]) by {
        if f(rows[q]) {
            let kq = ks[q];
            assert(rows[q] == group_row(c.pv, xs, kq));
            assert(kq.len() == 2);
            assert(rows[q][0] == kq[0] && rows[q][1] == kq[1]);
            assert(kq =~= k);
            assert(ks.no_duplicates());
        }
    }
    assert(rows[q0] == group_row(c.pv, xs, k));
    assert(group_row(c.pv, xs, k)[0] == k[0] && group_row(c.pv, xs, k)[1] == k[1]);
    assert(group_row(c.pv, xs, k)[2] == (Val::Num { coeff: mx, scale: 4 }));
    if gmax(c, i) {
        lemma_keep_one(rows, f, q0);
    } else {
        assert(!f(rows[q0]));
        assert forall|q: int| 0 <= q < rows.len() implies !f(#[trigger] rows[q]) by {}
        lemma_keep_none(rows, f);
    }
}

/// The output columns of a joined row `num ++ (sub ++ m)`.
pub proof fn lemma_select_joined(c: Ctx, i: int, s: int, g: Row)
    requires g.len() == 3,
    ensures select(nrow(c, i) + (srow(c, s) + g), out_cols())
        == seq![Val::Text(sname_text(c, s)), Val::Text(tag_text(c, i)), (Val::Num { coeff: coeff(c, i), scale: 4 })],
{
    lemma_row_cells(c, i, s);
    let x = nrow(c, i) + (srow(c, s) + g);
    assert(x[11] == srow(c, s)[2]);
    assert(x[1] == nrow(c, i)[1]);
    assert(x[7] == nrow(c, i)[7]);
    assert(select(x, out_cols()) =~= seq![x[11], x[1], x[7]]);
}

/// The answer rows contributed by `num` row `i`.
pub proof fn lemma_one_num_row(db: Database, c: Ctx, l1: Literal, l2: Literal, i: int)
    requires db_ok(db, c), lits_ok(c, l1, l2), 0 <= i < c.n,
    ensures ({
        let r = product_rows(db.tables[0], m_rows(db, c));
        let m = |y: Row| nrow(c, i) + y;
        keep(r.map_values(m), |x: Row| full_cond(db, l1, l2, x)).map_values(|x: Row| select(x, out_cols()))
            == if body_ok(c, i) { seq![out_row(c, i)] } else { Seq::<Row>::empty() }
    }),
{
    let ss = db.tables[0];
    let gs = m_rows(db, c);
    let r = product_rows(ss, gs);
    let m = |y: Row| nrow(c, i) + y;
    let fw = |x: Row| full_cond(db, l1, l2, x);
    let sel = |x: Row| select(x, out_cols());
    let fs = |s: Row| s_cond(c, i, s);
    let fg = |g: Row| g_cond(c, i, g);
    lemma_keep_map(r, m, fw);
    lemma_m_rows(db, c);
    lemma_product_rows_elems(ss, gs);
    // On the rows of sub x m the condition splits.
    assert forall|q: int| 0 <= q < r.len() implies
        #[trigger] fw(m(r[q])) == (fs(left_of(r[q], 20)) && fg(right_of(r[q], 20))) by {
        assert(is_concat(r[q], ss, gs));
        let (a, b) = choose|a: int, b: int| 0 <= a < ss.len() && 0 <= b < gs.len() && r[q] == #[trigger] ss[a] + #[trigger] gs[b];
        assert(ss[a] == srow(c, a));
        lemma_row_cells(c, i, a);
        assert(grow_ok(gs[b]));
        lemma_split_cond(db, c, l1, l2, i, a, gs[b]);
        assert(left_of(r[q], 20) =~= ss[a]);
        assert(right_of(r[q], 20) =~= gs[b]);
    }
    assert forall|a: int| 0 <= a < ss.len() implies (#[trigger] ss[a]).len() == 20 by {
        assert(ss[a] == srow(c, a));
        lemma_row_cells(c, i, a);
    }
    lemma_product_keep(ss, gs, fs, fg, 20);
    lemma_keep_ext(r, |y: Row| fw(m(y)), |y: Row| fs(left_of(y, 20)) && fg(right_of(y, 20)));
    let kept = product_rows(keep(ss, fs), keep(gs, fg));
    assert(keep(r, |y: Row| fw(m(y))) == kept);
    lemma_keep_sub(db, c, i);
    if uom_text(c, i) == c.pv && has_sub(c, i) {
        let s0 = sub_of(c, i);
        assert(sub_match(c, i, s0));
        lemma_keep_m(db, c, i);
        if gmax(c, i) {
            let g0 = group_row(c.pv, db.tables[1], seq![nrow(c, i)[0], nrow(c, i)[1]]);
            lemma_product_one(srow(c, s0), g0);
            assert(g0.len() == 3) by {
                lemma_row_cells(c, i, 0);
            }
            lemma_select_joined(c, i, s0, g0);
            assert(kept.map_values(m).map_values(sel) =~= seq![out_row(c, i)]);
        } else {
            lemma_product_empty_right(seq![srow(c, s0)]);
            assert(kept.map_values(m).map_values(sel) =~= Seq::<Row>::empty());
        }
    } else {
        assert(product_rows(Seq::<Row>::empty(), keep(gs, fg)) == Seq::<Row>::empty());
        assert(kept.map_values(m).map_values(sel) =~= Seq::<Row>::empty());
    }
}

/// The joined rows of the first `k` `num` rows, kept and projected, are the answer rows of rows `0..k`.
pub proof fn lemma_body_prefix(db: Database, c: Ctx, l1: Literal, l2: Literal, k: int)
    requires db_ok(db, c), lits_ok(c, l1, l2), 0 <= k <= c.n,
    ensures ({
        let r = product_rows(db.tables[0], m_rows(db, c));
        keep(product_rows(db.tables[1].take(k), r), |x: Row| full_cond(db, l1, l2, x)).map_values(|x: Row| select(x, out_cols()))
            == norm(c, k)
    }),
    decreases k,
{
    let r = product_rows(db.tables[0], m_rows(db, c));
    let fw = |x: Row| full_cond(db, l1, l2, x);
    let sel = |x: Row| select(x, out_cols());
    if k == 0 {
        assert(db.tables[1].take(0) =~= Seq::<Row>::empty());
        assert(keep(Seq::<Row>::empty(), fw) == Seq::<Row>::empty());
        assert(Seq::<Row>::empty().map_values(sel) =~= Seq::<Row>::empty());
    } else {
        lemma_body_prefix(db, c, l1, l2, k - 1);
        let nk = db.tables[1].take(k);
        assert(nk.drop_last() =~= db.tables[1].take(k - 1));
        assert(nk.last() == nrow(c, k - 1));
        let m = |y: Row| nrow(c, k - 1) + y;
        assert(product_rows(nk, r) == product_rows(db.tables[1].take(k - 1), r) + r.map_values(|y: Row| nk.last() + y));
        assert(r.map_values(|y: Row| nk.last() + y) =~= r.map_values(m));
        lemma_keep_append(product_rows(db.tables[1].take(k - 1), r), r.map_values(m), fw);
        lemma_one_num_row(db, c, l1, l2, k - 1);
        let a = keep(product_rows(db.tables[1].take(k - 1), r), fw);
        let b = keep(r.map_values(m), fw);
        assert((a + b).map_values(sel) =~= a.map_values(sel) + b.map_values(sel));
    }
}

// ------------------------------------------------------------------------------------------------ the FROM tree

pub open spec fn f_true() -> spec_fn(Row) -> bool {
    |x: Row| true
}

/// The ON condition of the first join holds.
pub open spec fn f_join(db: Database) -> spec_fn(Row) -> bool {
    |x: Row| eval_pred(db, x, p_join()) == Ok::<Truth, SqlError>(Truth::True)
}

/// The first join's condition on the left part of a joined row.
pub open spec fn f_left(db: Database) -> spec_fn(Row) -> bool {
    |x: Row| f_join(db)(left_of(x, 29)) && f_true()(right_of(x, 29))
}

/// ... and the ON condition of the second join.
pub open spec fn f_mm(db: Database) -> spec_fn(Row) -> bool {
    |x: Row| f_left(db)(x) && eval_pred(db, x, p_m()) == Ok::<Truth, SqlError>(Truth::True)
}

/// All three conditions.
pub open spec fn f_full(db: Database, l1: Literal, l2: Literal) -> spec_fn(Row) -> bool {
    |x: Row| full_cond(db, l1, l2, x)
}

pub open spec fn p1_rows(db: Database) -> Seq<Row> {
    product_rows(db.tables[1], db.tables[0])
}

pub open spec fn p2_rows(db: Database, c: Ctx) -> Seq<Row> {
    product_rows(p1_rows(db), m_rows(db, c))
}

/// The row widths of `num` and `sub`.
pub proof fn lemma_widths(db: Database, c: Ctx)
    requires db_ok(db, c),
    ensures
        forall|i: int| 0 <= i < db.tables[1].len() ==> (#[trigger] db.tables[1][i]).len() == 9,
        forall|s: int| 0 <= s < db.tables[0].len() ==> (#[trigger] db.tables[0][s]).len() == 20,
{
    assert forall|i: int| 0 <= i < db.tables[1].len() implies (#[trigger] db.tables[1][i]).len() == 9 by {
        lemma_row_cells(c, i, 0);
    }
    assert forall|s: int| 0 <= s < db.tables[0].len() implies (#[trigger] db.tables[0][s]).len() == 20 by {
        lemma_row_cells(c, 0, s);
    }
}

/// `num x sub` with the first ON condition.
#[verifier::spinoff_prover]
pub proof fn lemma_eval_ns(db: Database, c: Ctx)
    requires db_ok(db, c),
    ensures
        eval_query(db, Seq::empty(), q_ns()) == Ok::<Relation, SqlError>(keep(p1_rows(db), f_join(db))),
        forall|q: int| 0 <= q < p1_rows(db).len() ==> (#[trigger] p1_rows(db)[q]).len() == 29,
{
    let nn = db.tables[1];
    let ss = db.tables[0];
    let tt = f_true();
    lemma_eval_table(db, 1, tt);
    lemma_eval_table(db, 0, tt);
    lemma_widths(db, c);
    let p1 = p1_rows(db);
    lemma_product_rows_elems(nn, ss);
    lemma_eval_product(db, Query::Table(1), Query::Table(0), nn, tt, 9, ss, tt, p1, tt);
    assert forall|q: int| 0 <= q < p1.len() implies (#[trigger] p1[q]).len() == 29 && eval_pred(db, p1[q], p_join()) is Ok by {
        assert(is_concat(p1[q], nn, ss));
        let (a, b) = choose|a: int, b: int| 0 <= a < nn.len() && 0 <= b < ss.len() && p1[q] == #[trigger] nn[a] + #[trigger] ss[b];
        assert(nn[a] == nrow(c, a) && ss[b] == srow(c, b));
        lemma_join_cond(db, c, a, b);
    }
    lemma_filter_true(db, Query::Product { left: Box::new(Query::Table(1)), right: Box::new(Query::Table(0)) }, p1, tt, p_join(), f_join(db));
}

/// One joined row `num ++ sub ++ m`: its width and its conditions.
#[verifier::spinoff_prover]
pub proof fn lemma_p2_row(db: Database, c: Ctx, l1: Literal, l2: Literal, q: int)
    requires db_ok(db, c), lits_ok(c, l1, l2), 0 <= q < p2_rows(db, c).len(),
    ensures ({
        let x = p2_rows(db, c)[q];
        &&& x.len() == 32
        &&& eval_pred(db, x, p_m()) is Ok
        &&& eval_pred(db, x, p_w(l1, l2)) is Ok
        &&& f_full(db, l1, l2)(x) == (f_mm(db)(x) && eval_pred(db, x, p_w(l1, l2)) == Ok::<Truth, SqlError>(Truth::True))
    }),
{
    let nn = db.tables[1];
    let ss = db.tables[0];
    let p1 = p1_rows(db);
    let gs = m_rows(db, c);
    let p2 = p2_rows(db, c);
    lemma_m_rows(db, c);
    lemma_product_rows_elems(p1, gs);
    lemma_product_rows_elems(nn, ss);
    assert(is_concat(p2[q], p1, gs));
    let (a, b) = choose|a: int, b: int| 0 <= a < p1.len() && 0 <= b < gs.len() && p2[q] == #[trigger] p1[a] + #[trigger] gs[b];
    assert(is_concat(p1[a], nn, ss));
    let (u, v) = choose|u: int, v: int| 0 <= u < nn.len() && 0 <= v < ss.len() && p1[a] == #[trigger] nn[u] + #[trigger] ss[v];
    assert(nn[u] == nrow(c, u) && ss[v] == srow(c, v));
    assert(grow_ok(gs[b]));
    lemma_row_cells(c, u, v);
    lemma_m_cond(db, c, u, v, gs[b]);
    lemma_w_cond(db, c, l1, l2, u, v, gs[b]);
    assert(left_of(p2[q], 29) =~= p1[a]);
}

/// `(num x sub) x m` with both ON conditions.
#[verifier::spinoff_prover]
pub proof fn lemma_eval_qm(db: Database, c: Ctx, l1: Literal, l2: Literal)
    requires db_ok(db, c), lits_ok(c, l1, l2),
    ensures eval_query(db, Seq::empty(), q_m(l1)) == Ok::<Relation, SqlError>(keep(p2_rows(db, c), f_mm(db))),
{
    let tt = f_true();
    let p1 = p1_rows(db);
    let gs = m_rows(db, c);
    let p2 = p2_rows(db, c);
    lemma_eval_ns(db, c);
    lemma_m_eval(db, c, l1, l2);
    crate::link::join::lemma_keep_all(gs, tt);
    lemma_eval_product(db, q_ns(), q_grp(l1), p1, f_join(db), 29, gs, tt, p2, f_left(db));
    assert forall|q: int| 0 <= q < p2.len() && f_left(db)(#[trigger] p2[q]) implies eval_pred(db, p2[q], p_m()) is Ok by {
        lemma_p2_row(db, c, l1, l2, q);
    }
    lemma_filter_true(db, q_joined(l1), p2, f_left(db), p_m(), f_mm(db));
}

/// ... and the WHERE.
#[verifier::spinoff_prover]
pub proof fn lemma_eval_where(db: Database, c: Ctx, l1: Literal, l2: Literal)
    requires db_ok(db, c), lits_ok(c, l1, l2),
    ensures
        eval_query(db, Seq::empty(), q_where(l1, l2)) == Ok::<Relation, SqlError>(keep(p2_rows(db, c), f_full(db, l1, l2))),
        forall|q: int| 0 <= q < keep(p2_rows(db, c), f_full(db, l1, l2)).len()
            ==> (#[trigger] keep(p2_rows(db, c), f_full(db, l1, l2))[q]).len() == 32,
{
    let p2 = p2_rows(db, c);
    lemma_eval_qm(db, c, l1, l2);
    assert forall|q: int| 0 <= q < p2.len() && f_mm(db)(#[trigger] p2[q]) implies eval_pred(db, p2[q], p_w(l1, l2)) is Ok by {
        lemma_p2_row(db, c, l1, l2, q);
    }
    assert forall|q: int| 0 <= q < p2.len() implies #[trigger] f_full(db, l1, l2)(p2[q])
        == (f_mm(db)(p2[q]) && eval_pred(db, p2[q], p_w(l1, l2)) == Ok::<Truth, SqlError>(Truth::True)) by {
        lemma_p2_row(db, c, l1, l2, q);
    }
    lemma_filter_true(db, q_m(l1), p2, f_mm(db), p_w(l1, l2), f_full(db, l1, l2));
    let kept = keep(p2, f_full(db, l1, l2));
    lemma_keep_members(p2, f_full(db, l1, l2));
    assert forall|q: int| 0 <= q < kept.len() implies (#[trigger] kept[q]).len() == 32 by {
        let w = choose|w: int| 0 <= w < p2.len() && p2[w] == kept[q];
        lemma_p2_row(db, c, l1, l2, w);
    }
}

/// The body of the statement on a bound database is `norm(c, n)`.
#[verifier::spinoff_prover]
pub proof fn lemma_body(db: Database, c: Ctx, l1: Literal, l2: Literal)
    requires db_ok(db, c), lits_ok(c, l1, l2),
    ensures eval_query(db, Seq::empty(), q_body(l1, l2)) == Ok::<Relation, SqlError>(norm(c, c.n)),
{
    let nn = db.tables[1];
    let ss = db.tables[0];
    let gs = m_rows(db, c);
    let fw = f_full(db, l1, l2);
    lemma_eval_where(db, c, l1, l2);
    lemma_project_cols(db, q_where(l1, l2), keep(p2_rows(db, c), fw), out_cols(), 32);
    // num x (sub x m), one num row at a time
    lemma_product_assoc(nn, ss, gs);
    assert(nn.take(c.n) =~= nn);
    lemma_body_prefix(db, c, l1, l2, c.n);
    let a = keep(product_rows(nn, product_rows(ss, gs)), |x: Row| full_cond(db, l1, l2, x));
    lemma_keep_ext(p2_rows(db, c), fw, |x: Row| full_cond(db, l1, l2, x));
}

/// A row of the group counts toward it.
pub proof fn lemma_gcount_hit(g: QuerySpec, xs: Seq<Row>, k: Row, i: int)
    requires 0 <= i < xs.len(), hit(g, xs[i], k),
    ensures gcount(g, xs, k) > 0,
    decreases xs.len(),
{
    if i < xs.len() - 1 {
        assert(xs.drop_last()[i] == xs[i]);
        lemma_gcount_hit(g, xs.drop_last(), k, i);
    }
}

} // verus!
