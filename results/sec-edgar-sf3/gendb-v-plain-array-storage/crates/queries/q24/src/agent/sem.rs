//! The statement's meaning on a database whose `num` and `pre` tables are the flat parts (`db_ok`): the body
//! evaluates to `having(grp_rows(xrows(c, keep_range(c, 0, n))))` (`lemma_body`), the groups of the kept `num`
//! rows (`spec::keep`) with their COUNT(*) and SUM(value), first-occurrence order, filtered by `COUNT(*) > 10`.
//!
//! Proof outline:
//! 1. the LEFT JOIN evaluates to `left_join_rows(num, pre, lj_truths(c), 10)`: the ON condition of `num` row `i`
//!    and `pre` row `j` is `truth_of(same_key(c, i, j))` (`lemma_eval_lj`);
//! 2. the WHERE agrees with the normal form `nf(c)` (a `link::query::QuerySpec` over the joined rows projected on
//!    `cols()` = tag, version, ddate, uom, value, pre.adsh): matched rows have a non-NULL `pre.adsh`, so only
//!    NULL-padded rows of kept `num` rows qualify (`lemma_pred_agrees`);
//! 3. the qualifying projected rows of the join are exactly `xrows(c, keep_range(c, 0, n))`
//!    (`lemma_lj_qrows`), and the accumulators only see qualifying rows (`lemma_qrows_same`), so
//!    `link::query::lemma_group_query` gives the GROUP BY rows over `xrows(..)`;
//! 4. the HAVING keeps the group rows whose count exceeds 10 (`lemma_having`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::scalar::*;
use crate::spec::int::*;
use crate::spec::limits::int8_max;
use crate::spec::order::*;
use crate::spec::equality::*;
use crate::bridge::collect::lemma_collect_all;
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::bridge::relation::lemma_keep_true_sub;
use crate::exec::relational::domain::lemma_collect_pointwise;
use crate::link::query::*;
use crate::link::expr::{i128_max, lemma_expr_col, lemma_expr_text};
use crate::stores::flat_num::interface as ni;
use crate::stores::flat_pre::interface as pi;
use crate::agent::spec::*;

verus! {

// ------------------------------------------------------------------------------------------------ AST nodes

pub open spec fn p_on() -> Pred {
    Pred::And(
        Box::new(Pred::And(
            Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(1), b: Expr::Col(15) }),
            Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(2), b: Expr::Col(16) }),
        )),
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) }),
    )
}

pub open spec fn q_lj() -> Query {
    Query::LeftJoin { left: Box::new(Query::Table(1)), right: Box::new(Query::Table(3)), on: p_on() }
}

/// `uom = $1 AND (ddate >= $2 AND ddate <= $3)`.
pub open spec fn p_num(l1: Literal, l2: Literal, l3: Literal) -> Pred {
    Pred::And(
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(5), b: Expr::Lit(l1) }),
        Box::new(Pred::And(
            Box::new(Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(3), b: Expr::Lit(l2) }),
            Box::new(Pred::Cmp { op: CmpOp::Le, a: Expr::Col(3), b: Expr::Lit(l3) }),
        )),
    )
}

/// The WHERE condition.
pub open spec fn p_where(l1: Literal, l2: Literal, l3: Literal) -> Pred {
    Pred::And(
        Box::new(Pred::And(
            Box::new(p_num(l1, l2, l3)),
            Box::new(Pred::Not(Box::new(Pred::IsNull(Expr::Col(7))))),
        )),
        Box::new(Pred::IsNull(Expr::Col(9))),
    )
}

pub open spec fn q_where(l1: Literal, l2: Literal, l3: Literal) -> Query {
    Query::Filter { pred: p_where(l1, l2, l3), input: Box::new(q_lj()) }
}

pub open spec fn group_keys() -> Seq<Expr> {
    seq![Expr::Col(1), Expr::Col(2)]
}

pub open spec fn group_aggs() -> Seq<Agg> {
    seq![Agg::CountStar, Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(7) }]
}

pub open spec fn q_group(l1: Literal, l2: Literal, l3: Literal) -> Query {
    Query::GroupBy { keys: group_keys(), aggs: group_aggs(), input: Box::new(q_where(l1, l2, l3)) }
}

/// The HAVING condition `COUNT(*) > 10`.
pub open spec fn p_having() -> Pred {
    Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(2), b: Expr::Lit(Literal::Int { v: 10, kind: IntKind::Int4 }) }
}

pub open spec fn q_body(l1: Literal, l2: Literal, l3: Literal) -> Query {
    Query::Filter { pred: p_having(), input: Box::new(q_group(l1, l2, l3)) }
}

pub open spec fn order_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 2, desc: true, nulls_first: true }]
}

/// The generated statement, node by node.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures
        crate::query::query_spec_at(ps).body == q_body(ps[0], ps[1], ps[2]),
        crate::query::query_spec_at(ps).keys == order_keys(),
        crate::query::query_spec_at(ps).limit == Some(100nat),
        crate::query::query_spec_at(ps).offset == 0,
{
}

// ------------------------------------------------------------------------------------------------ the database

/// `db`'s `num` and `pre` tables are the rows of the parts of `c`.
pub open spec fn db_ok(db: Database, c: Ctx) -> bool {
    &&& ctx_ok(c)
    &&& db.schema == crate::schema::schema_spec()
    &&& db.tables.len() == 4
    &&& db.tables[1].len() == c.n
    &&& db.tables[3].len() == c.m
    &&& forall|i: int| 0 <= i < c.n ==> #[trigger] db.tables[1][i] == ni::row_at(c.np, i)
    &&& forall|j: int| 0 <= j < c.m ==> #[trigger] db.tables[3][j] == pi::row_at(c.pp, j)
}

/// The binding: `$1` is the text `c.pv`, `$2` and `$3` the int4 values `c.dlo`, `c.dhi`.
pub open spec fn lits_ok(c: Ctx, ps: Seq<Literal>) -> bool {
    &&& ps.len() == 3
    &&& ps[0] == Literal::Text(c.pv)
    &&& ps[1] == Literal::Int { v: c.dlo, kind: IntKind::Int4 }
    &&& ps[2] == Literal::Int { v: c.dhi, kind: IntKind::Int4 }
    &&& int_in_range(IntKind::Int4, c.dlo)
    &&& int_in_range(IntKind::Int4, c.dhi)
}

pub open spec fn nrow(c: Ctx, i: int) -> Row {
    ni::row_at(c.np, i)
}

pub open spec fn prow(c: Ctx, j: int) -> Row {
    pi::row_at(c.pp, j)
}

/// The cells of a `num` row the statement reads.
pub proof fn lemma_nrow_cells(c: Ctx, i: int)
    ensures
        nrow(c, i).len() == 9,
        nrow(c, i)[0] == Val::Text(nadsh(c, i)),
        nrow(c, i)[1] == Val::Text(ntag(c, i)),
        nrow(c, i)[2] == Val::Text(nver(c, i)),
        nrow(c, i)[3] == Val::Int(ddate(c, i)),
        nrow(c, i)[5] == Val::Text(nuom(c, i)),
        nrow(c, i)[7] == (Val::Num { coeff: coeff(c, i), scale: 4 }),
{
}

/// The cells of a `pre` row the statement reads.
pub proof fn lemma_prow_cells(c: Ctx, j: int)
    ensures
        prow(c, j).len() == 10,
        prow(c, j)[0] == Val::Text(padsh(c, j)),
        prow(c, j)[6] == Val::Text(ptag(c, j)),
        prow(c, j)[7] == Val::Text(pver(c, j)),
{
}

// ------------------------------------------------------------------------------------------------ LEFT JOIN

/// Text equality as SQL `=` on two text values.
pub proof fn lemma_text_eq(op: CmpOp, a: Seq<u8>, b: Seq<u8>)
    requires op == CmpOp::Eq,
    ensures cmp_truth(op, Val::Text(a), Val::Text(b)) == Ok::<Truth, SqlError>(truth_of(a == b)),
{
    lemma_lex_cmp_zero(a, b);
}

/// The ON condition of `num` row `i` and `pre` row `j`.
pub proof fn lemma_on(db: Database, c: Ctx, i: int, j: int)
    ensures eval_pred(db, nrow(c, i) + prow(c, j), p_on()) == Ok::<Truth, SqlError>(truth_of(same_key(c, i, j))),
{
    let env = nrow(c, i) + prow(c, j);
    lemma_nrow_cells(c, i);
    lemma_prow_cells(c, j);
    assert(env[1] == Val::Text(ntag(c, i)));
    assert(env[15] == Val::Text(ptag(c, j)));
    assert(env[2] == Val::Text(nver(c, i)));
    assert(env[16] == Val::Text(pver(c, j)));
    assert(env[0] == Val::Text(nadsh(c, i)));
    assert(env[9] == Val::Text(padsh(c, j)));
    lemma_text_eq(CmpOp::Eq, ntag(c, i), ptag(c, j));
    lemma_text_eq(CmpOp::Eq, nver(c, i), pver(c, j));
    lemma_text_eq(CmpOp::Eq, nadsh(c, i), padsh(c, j));
    lemma_expr_col(db, env, 0);
    lemma_expr_col(db, env, 1);
    lemma_expr_col(db, env, 2);
    lemma_expr_col(db, env, 9);
    lemma_expr_col(db, env, 15);
    lemma_expr_col(db, env, 16);
    let c1 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(1), b: Expr::Col(15) };
    let c2 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(2), b: Expr::Col(16) };
    let c3 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) };
    assert(eval_pred(db, env, c1) == Ok::<Truth, SqlError>(truth_of(ntag(c, i) == ptag(c, j))));
    assert(eval_pred(db, env, c2) == Ok::<Truth, SqlError>(truth_of(nver(c, i) == pver(c, j))));
    assert(eval_pred(db, env, c3) == Ok::<Truth, SqlError>(truth_of(nadsh(c, i) == padsh(c, j))));
    let a12 = Pred::And(Box::new(c1), Box::new(c2));
    assert(eval_pred(db, env, a12) == Ok::<Truth, SqlError>(truth_of(ntag(c, i) == ptag(c, j) && nver(c, i) == pver(c, j))));
}

/// The ON truth values of every `num` row with every `pre` row.
pub open spec fn lj_truths(c: Ctx) -> Seq<Seq<Truth>> {
    Seq::new(c.n as nat, |i: int| Seq::new(c.m as nat, |j: int| truth_of(same_key(c, i, j))))
}

pub open spec fn nrows(c: Ctx) -> Seq<Row> {
    Seq::new(c.n as nat, |i: int| nrow(c, i))
}

pub open spec fn prows(c: Ctx) -> Seq<Row> {
    Seq::new(c.m as nat, |j: int| prow(c, j))
}

/// The joined rows of `num` rows `0..k`.
pub open spec fn lj_rows(c: Ctx, k: int) -> Seq<Row> {
    left_join_rows(nrows(c).take(k), prows(c), lj_truths(c).take(k), 10)
}

/// The ON truth values of the LEFT JOIN, as its evaluation collects them.
pub proof fn lemma_lj_truths(db: Database, c: Ctx)
    requires db_ok(db, c),
    ensures ({
        let ctx = Seq::<Val>::empty();
        let l = db.tables[1];
        let r = db.tables[3];
        collect(crate::exec::relational::domain::left_join_results(db, ctx, l, r, p_on()))
            == Ok::<Seq<Seq<Truth>>, SqlError>(lj_truths(c))
    }),
{
    hide(eval_pred);
    let ctx = Seq::<Val>::empty();
    let l = db.tables[1];
    let r = db.tables[3];
    let outer = crate::exec::relational::domain::left_join_results(db, ctx, l, r, p_on());
    let truths = lj_truths(c);
    assert forall|i: int| 0 <= i < outer.len() implies #[trigger] outer[i] == Ok::<Seq<Truth>, SqlError>(truths[i]) by {
        let rs = Seq::new(r.len(), |j: int| eval_pred(db, ctx + l[i] + r[j], p_on()));
        assert forall|j: int| 0 <= j < rs.len() implies #[trigger] rs[j] == Ok::<Truth, SqlError>(truths[i][j]) by {
            assert(l[i] == nrow(c, i));
            assert(r[j] == prow(c, j));
            assert(ctx + l[i] + r[j] =~= nrow(c, i) + prow(c, j));
            lemma_on(db, c, i, j);
        }
        lemma_collect_all(rs, truths[i]);
        assert(outer[i] == collect(rs));
    }
    lemma_collect_all(outer, truths);
}

pub proof fn lemma_eval_lj(db: Database, c: Ctx)
    requires db_ok(db, c),
    ensures eval_query(db, Seq::empty(), q_lj()) == Ok::<Relation, SqlError>(lj_rows(c, c.n)),
{
    let ctx = Seq::<Val>::empty();
    crate::exec::relational::domain::lemma_eval_left_join(db, ctx, Box::new(Query::Table(1)), Box::new(Query::Table(3)), p_on());
    assert(eval_query(db, ctx, Query::Table(1)) == Ok::<Relation, SqlError>(db.tables[1]));
    assert(eval_query(db, ctx, Query::Table(3)) == Ok::<Relation, SqlError>(db.tables[3]));
    lemma_lj_truths(db, c);
    crate::stores::flat_pre::declaration::lemma_declared_schema();
    assert(query_arity(db.schema, Query::Table(3)) == 10);
    assert(db.tables[1] =~= nrows(c).take(c.n));
    assert(db.tables[3] =~= prows(c));
    assert(lj_truths(c).take(c.n) =~= lj_truths(c));
}

// ------------------------------------------------------------------------------------------------ the normal form

/// The joined-row columns the statement reads: num.tag, num.version, num.ddate, num.uom, num.value, pre.adsh.
pub open spec fn cols() -> Seq<nat> {
    seq![1nat, 2, 3, 5, 7, 9]
}

/// A projected joined row qualifies: `uom = pv`, `ddate` in range, `value` not NULL and no `pre` partner.
pub open spec fn nf_qual(pv: Seq<u8>, dlo: int, dhi: int, x: Row) -> bool {
    &&& x[3] == Val::Text(pv)
    &&& x[2] is Int
    &&& dlo <= x[2]->Int_0 <= dhi
    &&& !(x[4] is Null)
    &&& x[5] is Null
}

pub open spec fn nf_key(x: Row) -> Row {
    seq![x[0], x[1]]
}

/// The SUM argument coefficient (the COUNT argument is unused).
pub open spec fn nf_arg(j: int, x: Row) -> int {
    match x[4] {
        Val::Num { coeff, .. } => coeff,
        _ => 0,
    }
}

pub open spec fn nf(c: Ctx) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| nf_qual(c.pv, c.dlo, c.dhi, x),
        key: |x: Row| nf_key(x),
        arg: |j: int, x: Row| nf_arg(j, x),
        aggs: seq![AggKind::Count, AggKind::Sum { scale: 4 }],
        outs: seq![0nat, 1, 2, 3],
        grouped: true,
    }
}

/// The projected row of kept `num` row `i` (NULL-padded: `pre.adsh` is NULL).
pub open spec fn xrow(c: Ctx, i: int) -> Row {
    seq![Val::Text(ntag(c, i)), Val::Text(nver(c, i)), Val::Int(ddate(c, i)), Val::Text(nuom(c, i)),
        Val::Num { coeff: coeff(c, i), scale: 4 }, Val::Null]
}

/// The projected rows of a sequence of `num` rows.
pub open spec fn xrows(c: Ctx, us: Seq<int>) -> Seq<Row> {
    us.map_values(|i: int| xrow(c, i))
}

/// The projection of a padded joined row of `num` row `i`.
pub proof fn lemma_proj_padded(c: Ctx, i: int)
    ensures proj(nrow(c, i) + null_row(10), cols()) == xrow(c, i),
{
    lemma_nrow_cells(c, i);
    let r = nrow(c, i) + null_row(10);
    assert(r[9] == Val::Null);
    assert(proj(r, cols()) =~= xrow(c, i));
}

/// The projection of a matched joined row has a non-NULL `pre.adsh` (it does not qualify).
pub proof fn lemma_proj_matched(c: Ctx, i: int, j: int)
    ensures
        proj(nrow(c, i) + prow(c, j), cols())[5] == Val::Text(padsh(c, j)),
        !nf_qual(c.pv, c.dlo, c.dhi, proj(nrow(c, i) + prow(c, j), cols())),
{
    lemma_nrow_cells(c, i);
    lemma_prow_cells(c, j);
    let r = nrow(c, i) + prow(c, j);
    assert(r[9] == prow(c, j)[0]);
}

/// Kept rows qualify; a qualifying padded row is a kept row of an unmatched `num` row.
pub proof fn lemma_xrow_qual(c: Ctx, i: int)
    ensures nf_qual(c.pv, c.dlo, c.dhi, xrow(c, i)) == qual(c, i),
{
}

// ------------------------------------------------------------------------------------------------ WHERE

/// `r` is `num` row `i` joined with `pre` row `j`.
pub open spec fn is_mrow(c: Ctx, r: Row, i: int, j: int) -> bool {
    0 <= i < c.n && 0 <= j < c.m && r == nrow(c, i) + prow(c, j)
}

/// `r` is `num` row `i` padded with NULLs.
pub open spec fn is_prow(c: Ctx, r: Row, i: int) -> bool {
    0 <= i < c.n && r == nrow(c, i) + null_row(10)
}

/// A joined row: matched or padded.
pub open spec fn lj_shape(c: Ctx, r: Row) -> bool {
    (exists|i: int, j: int| #[trigger] is_mrow(c, r, i, j)) || (exists|i: int| #[trigger] is_prow(c, r, i))
}

/// The left part of the WHERE (on the `num` columns) of a joined row of `num` row `i`.
pub proof fn lemma_where_num(db: Database, c: Ctx, ps: Seq<Literal>, r: Row, i: int)
    requires
        lits_ok(c, ps), 0 <= i < c.n, r.len() == 19,
        forall|k: int| 0 <= k < 9 ==> #[trigger] r[k] == nrow(c, i)[k],
    ensures
        eval_pred(db, r, Pred::And(Box::new(p_num(ps[0], ps[1], ps[2])), Box::new(Pred::Not(Box::new(Pred::IsNull(Expr::Col(7)))))))
            == Ok::<Truth, SqlError>(truth_of(qual(c, i))),
{
    lemma_nrow_cells(c, i);
    assert(r[5] == Val::Text(nuom(c, i)));
    assert(r[3] == Val::Int(ddate(c, i)));
    assert(r[7] == (Val::Num { coeff: coeff(c, i), scale: 4 }));
    lemma_text_eq(CmpOp::Eq, nuom(c, i), c.pv);
    lemma_expr_col(db, r, 3);
    lemma_expr_col(db, r, 5);
    lemma_expr_col(db, r, 7);
    lemma_expr_text(db, r, c.pv);
    assert(eval_expr(db, r, Expr::Lit(ps[1])) == Ok::<Val, SqlError>(Val::Int(c.dlo)));
    assert(eval_expr(db, r, Expr::Lit(ps[2])) == Ok::<Val, SqlError>(Val::Int(c.dhi)));
    let e = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(5), b: Expr::Lit(ps[0]) };
    let ge = Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(3), b: Expr::Lit(ps[1]) };
    let le = Pred::Cmp { op: CmpOp::Le, a: Expr::Col(3), b: Expr::Lit(ps[2]) };
    assert(eval_pred(db, r, e) == Ok::<Truth, SqlError>(truth_of(nuom(c, i) == c.pv)));
    assert(eval_pred(db, r, ge) == Ok::<Truth, SqlError>(truth_of(ddate(c, i) >= c.dlo)));
    assert(eval_pred(db, r, le) == Ok::<Truth, SqlError>(truth_of(ddate(c, i) <= c.dhi)));
    let rng = Pred::And(Box::new(ge), Box::new(le));
    assert(eval_pred(db, r, rng) == Ok::<Truth, SqlError>(truth_of(c.dlo <= ddate(c, i) <= c.dhi)));
    assert(eval_pred(db, r, p_num(ps[0], ps[1], ps[2])) == Ok::<Truth, SqlError>(truth_of(qual(c, i))));
    let nn = Pred::IsNull(Expr::Col(7));
    assert(eval_pred(db, r, nn) == Ok::<Truth, SqlError>(Truth::False));
    assert(eval_pred(db, r, Pred::Not(Box::new(nn))) == Ok::<Truth, SqlError>(Truth::True));
}

/// The WHERE condition of a joined row.
pub proof fn lemma_where_row(db: Database, c: Ctx, ps: Seq<Literal>, r: Row)
    requires db_ok(db, c), lits_ok(c, ps), lj_shape(c, r),
    ensures
        eval_pred(db, r, p_where(ps[0], ps[1], ps[2])) == Ok::<Truth, SqlError>(truth_of(nf_qual(c.pv, c.dlo, c.dhi, proj(r, cols())))),
{
    let left = Pred::And(Box::new(p_num(ps[0], ps[1], ps[2])), Box::new(Pred::Not(Box::new(Pred::IsNull(Expr::Col(7))))));
    let isn = Pred::IsNull(Expr::Col(9));
    if exists|i: int, j: int| #[trigger] is_mrow(c, r, i, j) {
        let (i, j) = choose|i: int, j: int| #[trigger] is_mrow(c, r, i, j);
        lemma_nrow_cells(c, i);
        lemma_prow_cells(c, j);
        lemma_where_num(db, c, ps, r, i);
        assert(r[9] == Val::Text(padsh(c, j)));
        lemma_expr_col(db, r, 9);
        assert(eval_pred(db, r, isn) == Ok::<Truth, SqlError>(Truth::False));
        lemma_proj_matched(c, i, j);
    } else {
        let i = choose|i: int| #[trigger] is_prow(c, r, i);
        lemma_nrow_cells(c, i);
        lemma_where_num(db, c, ps, r, i);
        assert(r[9] == Val::Null);
        lemma_expr_col(db, r, 9);
        assert(eval_pred(db, r, isn) == Ok::<Truth, SqlError>(Truth::True));
        lemma_proj_padded(c, i);
    }
}

/// Every joined row is a matched or a padded row of the table rows.
pub proof fn lemma_lj_elems(c: Ctx, k: int)
    requires ctx_ok(c), 0 <= k <= c.n,
    ensures forall|q: int| 0 <= q < lj_rows(c, k).len() ==> lj_shape(c, #[trigger] lj_rows(c, k)[q]),
{
    let l = nrows(c).take(k);
    let r = prows(c);
    crate::bridge::relation::lemma_left_join_rows_elems(l, r, lj_truths(c).take(k), 10);
    let s = lj_rows(c, k);
    assert forall|q: int| 0 <= q < s.len() implies lj_shape(c, #[trigger] s[q]) by {
        if crate::bridge::relation::is_concat(s[q], l, r) {
            let (i, j) = choose|i: int, j: int| 0 <= i < l.len() && 0 <= j < r.len() && s[q] == #[trigger] l[i] + #[trigger] r[j];
            assert(l[i] == nrows(c)[i]);
            assert(l[i] == nrow(c, i));
            assert(r[j] == prow(c, j));
            assert(is_mrow(c, s[q], i, j));
        } else {
            let i = choose|i: int| 0 <= i < l.len() && s[q] == #[trigger] l[i] + null_row(10);
            assert(l[i] == nrows(c)[i]);
            assert(l[i] == nrow(c, i));
            assert(is_prow(c, s[q], i));
        }
    }
}

/// The length of a joined row, and its qualifying projection is a padded kept row.
pub proof fn lemma_shape_facts(c: Ctx, r: Row)
    requires lj_shape(c, r),
    ensures
        r.len() == 19,
        nf_qual(c.pv, c.dlo, c.dhi, proj(r, cols())) ==> exists|i: int| #[trigger] is_prow(c, r, i),
{
    if exists|i: int, j: int| #[trigger] is_mrow(c, r, i, j) {
        let (i, j) = choose|i: int, j: int| #[trigger] is_mrow(c, r, i, j);
        lemma_nrow_cells(c, i);
        lemma_prow_cells(c, j);
        lemma_proj_matched(c, i, j);
    } else {
        let i = choose|i: int| #[trigger] is_prow(c, r, i);
        lemma_nrow_cells(c, i);
    }
}

pub proof fn lemma_pred_agrees(db: Database, c: Ctx, ps: Seq<Literal>)
    requires db_ok(db, c), lits_ok(c, ps),
    ensures pred_agrees(db, lj_rows(c, c.n), cols(), p_where(ps[0], ps[1], ps[2]), nf(c)),
{
    hide(eval_pred);
    let rows = lj_rows(c, c.n);
    lemma_lj_elems(c, c.n);
    assert forall|q: int| 0 <= q < rows.len() implies
        eval_pred(db, #[trigger] rows[q], p_where(ps[0], ps[1], ps[2]))
            == Ok::<Truth, SqlError>(truth_of((nf(c).qual)(proj(rows[q], cols())))) by {
        lemma_where_row(db, c, ps, rows[q]);
    }
}

// ------------------------------------------------------------------------------------------------ qualifying rows

/// The accumulators and group keys see only the qualifying rows.
pub proof fn lemma_qrows_same(g: QuerySpec, a: Seq<Row>, k: Row, j: int)
    ensures
        gcount(g, a, k) == gcount(g, qrows(g, a), k),
        gsum(g, a, k, j) == gsum(g, qrows(g, a), k, j),
        gabs(g, a, k, j) == gabs(g, qrows(g, a), k, j),
        gkeys(g, a) == gkeys(g, qrows(g, a)),
    decreases a.len(),
{
    if a.len() > 0 {
        lemma_qrows_same(g, a.drop_last(), k, j);
        let q = qrows(g, a.drop_last());
        if (g.qual)(a.last()) {
            assert(qrows(g, a) == q.push(a.last()));
            assert(q.push(a.last()).drop_last() =~= q);
            assert(q.push(a.last()).last() == a.last());
        }
    }
}

/// `qrows` of a concatenation.
pub proof fn lemma_qrows_append(g: QuerySpec, a: Seq<Row>, b: Seq<Row>)
    ensures qrows(g, a + b) == qrows(g, a) + qrows(g, b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(qrows(g, a) + qrows(g, b) =~= qrows(g, a));
    } else {
        lemma_qrows_append(g, a, b.drop_last());
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
        if (g.qual)(b.last()) {
            assert(qrows(g, a) + qrows(g, b.drop_last()).push(b.last()) =~= (qrows(g, a) + qrows(g, b.drop_last())).push(b.last()));
        }
    }
}

/// Rows none of which qualifies have no qualifying rows.
pub proof fn lemma_qrows_none(g: QuerySpec, a: Seq<Row>)
    requires forall|q: int| 0 <= q < a.len() ==> !(g.qual)(#[trigger] a[q]),
    ensures qrows(g, a) == Seq::<Row>::empty(),
    decreases a.len(),
{
    if a.len() > 0 {
        let d = a.drop_last();
        assert forall|q: int| 0 <= q < d.len() implies !(g.qual)(#[trigger] d[q]) by {
            assert(d[q] == a[q]);
        }
        lemma_qrows_none(g, d);
        assert(!(g.qual)(a[a.len() - 1]));
    }
}

/// Projection distributes over concatenation.
pub proof fn lemma_proj_all_append(a: Seq<Row>, b: Seq<Row>, cs: Seq<nat>)
    ensures proj_all(a + b, cs) == proj_all(a, cs) + proj_all(b, cs),
{
    assert(proj_all(a + b, cs) =~= proj_all(a, cs) + proj_all(b, cs));
}

/// `keep_true` keeps nothing exactly when no truth value is `True`.
pub proof fn lemma_keep_true_empty(rows: Seq<Row>, truths: Seq<Truth>)
    requires rows.len() == truths.len(),
    ensures (keep_true(rows, truths).len() == 0) <==> (forall|j: int| 0 <= j < truths.len() ==> !(#[trigger] truths[j] is True)),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let (ri, ti) = (rows.drop_last(), truths.drop_last());
        lemma_keep_true_empty(ri, ti);
        if keep_true(rows, truths).len() == 0 {
            assert forall|j: int| 0 <= j < truths.len() implies !(#[trigger] truths[j] is True) by {
                if j < ti.len() {
                    assert(ti[j] == truths[j]);
                }
            }
        }
        if forall|j: int| 0 <= j < truths.len() ==> !(#[trigger] truths[j] is True) {
            assert forall|j: int| 0 <= j < ti.len() implies !(#[trigger] ti[j] is True) by {
                assert(ti[j] == truths[j]);
            }
            assert(!(truths[truths.len() - 1] is True));
        }
    }
}

/// The joined rows of one `num` row project to its qualifying row when it is kept, and to no qualifying row
/// otherwise.
pub proof fn lemma_block_qrows(c: Ctx, i: int)
    requires ctx_ok(c), 0 <= i < c.n,
    ensures ({
        let b = left_join_one(nrow(c, i), prows(c), lj_truths(c)[i], 10);
        qrows(nf(c), proj_all(b, cols())) == if keep(c, i) { seq![xrow(c, i)] } else { Seq::<Row>::empty() }
    }),
{
    let g = nf(c);
    let r = prows(c);
    let t = lj_truths(c)[i];
    let b = left_join_one(nrow(c, i), r, t, 10);
    let matched_rows = keep_true(r, t);
    lemma_keep_true_empty(r, t);
    if matched_rows.len() == 0 {
        assert(!matched(c, i)) by {
            if matched(c, i) {
                let j = choose|j: int| 0 <= j < c.m && #[trigger] same_key(c, i, j);
                assert(t[j] is True);
            }
        }
        assert(b == seq![nrow(c, i) + null_row(10)]);
        lemma_proj_padded(c, i);
        assert(proj_all(b, cols()) =~= seq![xrow(c, i)]);
        lemma_xrow_qual(c, i);
        let x = xrow(c, i);
        assert(seq![x].drop_last() =~= Seq::<Row>::empty());
        assert(qrows(g, Seq::<Row>::empty()) == Seq::<Row>::empty());
        if qual(c, i) {
            assert(Seq::<Row>::empty().push(x) =~= seq![x]);
        }
    } else {
        let j0 = choose|j: int| 0 <= j < t.len() && #[trigger] t[j] is True;
        assert(same_key(c, i, j0));
        assert(matched(c, i));
        lemma_keep_true_sub(r, t);
        let xs = proj_all(b, cols());
        assert forall|q: int| 0 <= q < xs.len() implies !(g.qual)(#[trigger] xs[q]) by {
            assert(b[q] == nrow(c, i) + matched_rows[q]);
            assert(r.contains(matched_rows[q]));
            let j = choose|j: int| 0 <= j < r.len() && r[j] == matched_rows[q];
            assert(r[j] == prow(c, j));
            lemma_proj_matched(c, i, j);
            assert(xs[q] == proj(b[q], cols()));
        }
        lemma_qrows_none(g, xs);
    }
}

/// The qualifying projected joined rows of `num` rows `0..k` are the projected kept rows.
pub proof fn lemma_lj_qrows(c: Ctx, k: int)
    requires ctx_ok(c), 0 <= k <= c.n,
    ensures qrows(nf(c), proj_all(lj_rows(c, k), cols())) == xrows(c, keep_range(c, 0, k)),
    decreases k,
{
    let g = nf(c);
    if k == 0 {
        assert(nrows(c).take(0).len() == 0);
        assert(lj_rows(c, 0) == Seq::<Row>::empty());
        assert(proj_all(Seq::<Row>::empty(), cols()) =~= Seq::<Row>::empty());
        assert(xrows(c, Seq::<int>::empty()) =~= Seq::<Row>::empty());
    } else {
        lemma_lj_qrows(c, k - 1);
        let l = nrows(c).take(k);
        let tr = lj_truths(c).take(k);
        assert(l.drop_last() =~= nrows(c).take(k - 1));
        assert(tr.drop_last() =~= lj_truths(c).take(k - 1));
        assert(l.last() == nrow(c, k - 1));
        assert(tr.last() == lj_truths(c)[k - 1]);
        let b = left_join_one(nrow(c, k - 1), prows(c), lj_truths(c)[k - 1], 10);
        assert(lj_rows(c, k) == lj_rows(c, k - 1) + b);
        lemma_proj_all_append(lj_rows(c, k - 1), b, cols());
        lemma_qrows_append(g, proj_all(lj_rows(c, k - 1), cols()), proj_all(b, cols()));
        lemma_block_qrows(c, k - 1);
        let prev = xrows(c, keep_range(c, 0, k - 1));
        if keep(c, k - 1) {
            assert(keep_range(c, 0, k) == keep_range(c, 0, k - 1).push(k - 1));
            assert(xrows(c, keep_range(c, 0, k)) =~= prev + seq![xrow(c, k - 1)]);
        } else {
            assert(keep_range(c, 0, k) == keep_range(c, 0, k - 1));
            assert(prev + Seq::<Row>::empty() =~= prev);
        }
    }
}

// ------------------------------------------------------------------------------------------------ GROUP BY

/// The GROUP BY rows over the kept rows `xs`: one `key ++ [COUNT, SUM]` row per key, first-occurrence order.
pub open spec fn grp_rows(c: Ctx, xs: Seq<Row>) -> Seq<Row> {
    gkeys(nf(c), xs).map_values(|k: Row| full_row(nf(c), xs, k))
}

/// The arithmetic domain the engine checks: every group count fits int8 and every group's absolute value sum
/// fits `i128`.
pub open spec fn caps_ok(c: Ctx, xs: Seq<Row>) -> bool {
    &&& forall|k: Row| #[trigger] gcount(nf(c), xs, k) <= int8_max()
    &&& forall|k: Row| #[trigger] gabs(nf(c), xs, k, 1) <= i128_max()
}

/// The GROUP BY key of a qualifying joined row.
pub proof fn lemma_keys_row(db: Database, c: Ctx, r: Row)
    requires lj_shape(c, r), nf_qual(c.pv, c.dlo, c.dhi, proj(r, cols())),
    ensures eval_exprs(db, r, group_keys()) == Ok::<Row, SqlError>(nf_key(proj(r, cols()))),
{
    lemma_shape_facts(c, r);
    assert(group_keys() =~= col_exprs(seq![1nat, 2]));
    lemma_eval_cols(db, r, seq![1nat, 2]);
    assert(select(r, seq![1nat, 2]) =~= nf_key(proj(r, cols())));
}

/// GROUP BY keys agree with the normal form on qualifying joined rows.
pub proof fn lemma_keys_agree(db: Database, c: Ctx)
    requires db_ok(db, c),
    ensures keys_agree(db, lj_rows(c, c.n), cols(), group_keys(), nf(c)),
{
    let g = nf(c);
    let rows = lj_rows(c, c.n);
    lemma_lj_elems(c, c.n);
    assert forall|q: int| 0 <= q < rows.len() && (g.qual)(proj(#[trigger] rows[q], cols())) implies
        eval_exprs(db, rows[q], group_keys()) == Ok::<Row, SqlError>((g.key)(proj(rows[q], cols()))) by {
        lemma_keys_row(db, c, rows[q]);
    }
}

/// The aggregate arguments of a joined row: no argument for COUNT(*), `value` for SUM.
pub proof fn lemma_agg_args_row(db: Database, r: Row)
    requires r.len() > 7,
    ensures agg_args(db, r, group_aggs()) == Ok::<Row, SqlError>(seq![Val::Null, r[7]]),
{
    let aggs = group_aggs();
    let ar = agg_arg_results(db, r, aggs);
    let av = seq![Val::Null, r[7]];
    assert(ar.len() == 2);
    assert(ar[0] == Ok::<Val, SqlError>(Val::Null)) by {
        assert(ar[0] == agg_arg(db, r, aggs[0]));
    }
    assert(ar[1] == Ok::<Val, SqlError>(r[7])) by {
        assert(ar[1] == agg_arg(db, r, aggs[1]));
        lemma_expr_col(db, r, 7);
    }
    assert forall|m: int| 0 <= m < ar.len() implies #[trigger] ar[m] == Ok::<Val, SqlError>(av[m]) by {
        if m == 0 {} else {}
    }
    lemma_collect_all(ar, av);
}

/// The normal form's arguments of a projected kept row.
pub proof fn lemma_arg_vals_x(c: Ctx, i: int)
    ensures arg_vals(nf(c), xrow(c, i)) == seq![Val::Null, Val::Num { coeff: coeff(c, i), scale: 4 }],
{
    assert(arg_vals(nf(c), xrow(c, i)) =~= seq![Val::Null, Val::Num { coeff: coeff(c, i), scale: 4 }]);
}

/// The aggregate arguments of a qualifying joined row.
pub proof fn lemma_args_row(db: Database, c: Ctx, r: Row)
    requires lj_shape(c, r), nf_qual(c.pv, c.dlo, c.dhi, proj(r, cols())),
    ensures agg_args(db, r, group_aggs()) == Ok::<Row, SqlError>(arg_vals(nf(c), proj(r, cols()))),
{
    lemma_shape_facts(c, r);
    let i = choose|i: int| #[trigger] is_prow(c, r, i);
    lemma_nrow_cells(c, i);
    lemma_proj_padded(c, i);
    assert(r[7] == (Val::Num { coeff: coeff(c, i), scale: 4 }));
    lemma_agg_args_row(db, r);
    lemma_arg_vals_x(c, i);
}

/// The aggregate arguments agree with the normal form on qualifying joined rows.
pub proof fn lemma_args_agree(db: Database, c: Ctx)
    requires db_ok(db, c),
    ensures args_agree(db, lj_rows(c, c.n), cols(), group_aggs(), nf(c)),
{
    let g = nf(c);
    let rows = lj_rows(c, c.n);
    lemma_lj_elems(c, c.n);
    assert forall|q: int| 0 <= q < rows.len() && (g.qual)(proj(#[trigger] rows[q], cols())) implies
        agg_args(db, rows[q], group_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[q], cols()))) by {
        lemma_args_row(db, c, rows[q]);
    }
}

/// The key of a qualifying projected joined row is two texts.
pub proof fn lemma_qual_key(c: Ctx, r: Row)
    requires lj_shape(c, r), nf_qual(c.pv, c.dlo, c.dhi, proj(r, cols())),
    ensures ({
        let k = nf_key(proj(r, cols()));
        k.len() == 2 && k[0] is Text && k[1] is Text
    }),
{
    lemma_shape_facts(c, r);
    let i = choose|i: int| #[trigger] is_prow(c, r, i);
    lemma_proj_padded(c, i);
}

/// Two keys of two texts each: SQL "not distinct" is equality.
pub proof fn lemma_text_keys_exact(ka: Row, kb: Row)
    requires ka.len() == 2 && ka[0] is Text && ka[1] is Text, kb.len() == 2 && kb[0] is Text && kb[1] is Text,
    ensures row_not_distinct(ka, kb) <==> ka == kb,
{
    lemma_row_exact(ka, kb);
}

/// On qualifying joined rows the keys are two texts: SQL "not distinct" is equality.
pub proof fn lemma_keys_exact(c: Ctx)
    requires ctx_ok(c),
    ensures keys_exact(nf(c), proj_all(lj_rows(c, c.n), cols())),
{
    let g = nf(c);
    let rows = lj_rows(c, c.n);
    let xs = proj_all(rows, cols());
    lemma_lj_elems(c, c.n);
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        assert(xs[a] == proj(rows[a], cols()));
        assert(xs[b] == proj(rows[b], cols()));
        lemma_qual_key(c, rows[a]);
        lemma_qual_key(c, rows[b]);
        lemma_text_keys_exact((g.key)(xs[a]), (g.key)(xs[b]));
    }
}

/// `caps_ok` of the kept rows is `group_caps` of the joined rows.
pub proof fn lemma_caps(c: Ctx)
    requires ctx_ok(c), caps_ok(c, xrows(c, keep_range(c, 0, c.n))),
    ensures group_caps(nf(c), proj_all(lj_rows(c, c.n), cols())),
{
    let g = nf(c);
    let xs = proj_all(lj_rows(c, c.n), cols());
    let kx = xrows(c, keep_range(c, 0, c.n));
    lemma_lj_qrows(c, c.n);
    assert forall|k: Row, j: int| #![trigger gcount(g, xs, k), g.aggs[j]] 0 <= j < g.aggs.len() && g.aggs[j] is Count implies gcount(g, xs, k) <= int8_max() by {
        lemma_qrows_same(g, xs, k, 1);
        assert(gcount(g, kx, k) <= int8_max());
    }
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies #[trigger] gabs(g, xs, k, j) <= i128_max() by {
        assert(j == 1);
        lemma_qrows_same(g, xs, k, 1);
        assert(gabs(g, kx, k, 1) <= i128_max());
    }
}

/// The group rows of the joined rows are the group rows of the kept rows.
pub proof fn lemma_grp_rows_kept(c: Ctx)
    requires ctx_ok(c),
    ensures ({
        let xs = proj_all(lj_rows(c, c.n), cols());
        gkeys(nf(c), xs).map_values(|k: Row| full_row(nf(c), xs, k)) == grp_rows(c, xrows(c, keep_range(c, 0, c.n)))
    }),
{
    let g = nf(c);
    let xs = proj_all(lj_rows(c, c.n), cols());
    let kx = xrows(c, keep_range(c, 0, c.n));
    lemma_lj_qrows(c, c.n);
    let k1 = gkeys(g, xs);
    lemma_qrows_same(g, xs, Seq::empty(), 1);
    assert(k1 == gkeys(g, kx));
    assert forall|q: int| 0 <= q < k1.len() implies #[trigger] full_row(g, xs, k1[q]) == full_row(g, kx, k1[q]) by {
        lemma_qrows_same(g, xs, k1[q], 0);
        lemma_qrows_same(g, xs, k1[q], 1);
        assert(agg_outs(g, xs, k1[q]) =~= agg_outs(g, kx, k1[q]));
    }
    assert(k1.map_values(|k: Row| full_row(g, xs, k)) =~= gkeys(g, kx).map_values(|k: Row| full_row(g, kx, k)));
}

pub proof fn lemma_group(db: Database, c: Ctx, ps: Seq<Literal>)
    requires
        db_ok(db, c), lits_ok(c, ps),
        caps_ok(c, xrows(c, keep_range(c, 0, c.n))),
    ensures
        eval_query(db, Seq::empty(), q_group(ps[0], ps[1], ps[2]))
            == Ok::<Relation, SqlError>(grp_rows(c, xrows(c, keep_range(c, 0, c.n)))),
{
    hide(eval_pred);
    hide(eval_exprs);
    hide(agg_args);
    hide(group_rows);
    let g = nf(c);
    let rows = lj_rows(c, c.n);
    lemma_eval_lj(db, c);
    lemma_pred_agrees(db, c, ps);
    lemma_filter_rows(db, q_lj(), rows, cols(), p_where(ps[0], ps[1], ps[2]), g);
    lemma_keys_agree(db, c);
    lemma_args_agree(db, c);
    lemma_keys_exact(c);
    lemma_caps(c);
    assert(aggs_match(group_aggs(), g));
    lemma_group_query(db, rows, cols(), q_lj_filter(ps), group_keys(), group_aggs(), g);
    lemma_grp_rows_kept(c);
}

pub open spec fn q_lj_filter(ps: Seq<Literal>) -> Query {
    q_where(ps[0], ps[1], ps[2])
}

// ------------------------------------------------------------------------------------------------ HAVING

/// The COUNT(*) of a group row.
pub open spec fn row_cnt(r: Row) -> int {
    match r[2] {
        Val::Int(x) => x,
        _ => 0,
    }
}

pub open spec fn having_truths(rows: Seq<Row>) -> Seq<Truth> {
    Seq::new(rows.len(), |q: int| truth_of(row_cnt(rows[q]) > 10))
}

/// The group rows with COUNT(*) > 10, in order.
pub open spec fn having(rows: Seq<Row>) -> Seq<Row> {
    keep_true(rows, having_truths(rows))
}

/// Every group row's third column is its count (an integer).
pub proof fn lemma_grp_row_shape(c: Ctx, xs: Seq<Row>, q: int)
    requires 0 <= q < grp_rows(c, xs).len(),
    ensures
        grp_rows(c, xs)[q].len() == 4,
        grp_rows(c, xs)[q][2] == Val::Int(gcount(nf(c), xs, gkeys(nf(c), xs)[q]) as int),
{
    let g = nf(c);
    let k = gkeys(g, xs)[q];
    lemma_gkeys_len(g, xs, q);
    assert(agg_outs(g, xs, k).len() == 2);
    assert(full_row(g, xs, k)[2] == agg_outs(g, xs, k)[0]);
}

/// Every group key has two values.
pub proof fn lemma_gkeys_len(g: QuerySpec, xs: Seq<Row>, q: int)
    requires 0 <= q < gkeys(g, xs).len(), forall|x: Row| (#[trigger] (g.key)(x)).len() == 2,
    ensures gkeys(g, xs)[q].len() == 2,
    decreases xs.len(),
{
    if xs.len() > 0 {
        let d = gkeys(g, xs.drop_last());
        if q < d.len() {
            if (g.qual)(xs.last()) && !d.contains((g.key)(xs.last())) {
                assert(gkeys(g, xs)[q] == d[q]);
            }
            lemma_gkeys_len(g, xs.drop_last(), q);
        }
    }
}

pub proof fn lemma_having(db: Database, c: Ctx, ps: Seq<Literal>)
    requires
        db_ok(db, c), lits_ok(c, ps),
        caps_ok(c, xrows(c, keep_range(c, 0, c.n))),
    ensures
        denote_body(db, crate::query::query_spec_at(ps))
            == Ok::<Relation, SqlError>(having(grp_rows(c, xrows(c, keep_range(c, 0, c.n))))),
{
    lemma_query_shape(ps);
    lemma_group(db, c, ps);
    let kx = xrows(c, keep_range(c, 0, c.n));
    let gr = grp_rows(c, kx);
    let ctx = Seq::<Val>::empty();
    let prs = Seq::new(gr.len(), |q: int| eval_pred(db, ctx + gr[q], p_having()));
    let truths = having_truths(gr);
    assert forall|q: int| 0 <= q < prs.len() implies #[trigger] prs[q] == Ok::<Truth, SqlError>(truths[q]) by {
        assert(ctx + gr[q] =~= gr[q]);
        lemma_grp_row_shape(c, kx, q);
        lemma_expr_col(db, gr[q], 2);
        assert(int_in_range(IntKind::Int4, 10));
        assert(eval_expr(db, gr[q], Expr::Lit(Literal::Int { v: 10, kind: IntKind::Int4 })) == Ok::<Val, SqlError>(Val::Int(10)));
        assert(row_cnt(gr[q]) == gcount(nf(c), kx, gkeys(nf(c), kx)[q]) as int);
    }
    lemma_collect_all(prs, truths);
    lemma_collect_pointwise::<Truth>();
}

} // verus!
