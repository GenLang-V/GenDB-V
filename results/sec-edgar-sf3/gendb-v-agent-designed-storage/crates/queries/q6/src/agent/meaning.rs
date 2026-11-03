//! The meaning of this statement in the accumulator normal form of `link::query` (`QuerySpec`), and the proof that
//! the statement's body evaluates to that form's group rows.
//!
//! The FROM relation is `R = (num x sub) x pre` (`joined`), rows of 39 values: `num` at 0..9, `sub` at 9..29, `pre` at
//! 29..39. A row qualifies (`qual`) when the three join conditions and the WHERE condition hold:
//! `num.adsh = sub.adsh`, `num.adsh = pre.adsh`, `num.tag = pre.tag`, `num.version = pre.version`, `num.uom = $1`,
//! `pre.stmt = $2`, `sub.fy = $3` (`num.value IS NOT NULL` always holds: the column is NOT NULL). Its group key is
//! `(sub.name, pre.stmt, num.tag, pre.plabel)` (`key_of`), its SUM argument the coefficient of `num.value` (scale 4).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::types::*;
use crate::spec::int::*;
use crate::spec::limits::int8_max;
use crate::spec::numeric::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::order::*;
use crate::spec::typing::*;
use crate::spec::equality::*;
use crate::spec::scalar::*;
use crate::schema::schema_spec;
use crate::query::{query_spec_at, param_domain, param_typed};
use crate::link::query::*;
use crate::link::join::*;
use crate::link::expr::*;
use crate::bridge::relation::{is_concat, lemma_product_rows_elems};
use crate::bridge::collect::lemma_collect_all;
use crate::exec::relational::domain::lemma_collect_pointwise;
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::exec::relational::domain::{fits_agg_value, sum_mass, sum_mass_fits, num_mass_at, num_max_scale};
use crate::link::capacity::{lemma_group_by_err, lemma_group_by_capacity, lemma_count_value, lemma_sum_inside_ok, aggs_ok_inside};

verus! {

// ------------------------------------------------------------------------------------------------ parameters

pub open spec fn p_uom(ps: Seq<Literal>) -> Seq<u8> {
    ps[0]->Text_0
}

pub open spec fn p_stmt(ps: Seq<Literal>) -> Seq<u8> {
    ps[1]->Text_0
}

pub open spec fn p_fy(ps: Seq<Literal>) -> int {
    ps[2]->Int_v
}

/// The shape of a binding in the declared domain.
pub open spec fn ps_ok(ps: Seq<Literal>) -> bool {
    &&& ps.len() == 3
    &&& ps[0] is Text
    &&& ps[1] is Text
    &&& ps[2] is Int && ps[2]->Int_kind == IntKind::Int4 && -2147483648 <= ps[2]->Int_v <= 2147483647
}

pub proof fn lemma_ps_ok(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures ps_ok(ps),
{
    assert(param_typed(ps));
    match ps[0] { Literal::Text(_) => {}, _ => {} }
    match ps[2] { Literal::Int { v, kind } => {}, _ => {} }
    assert(type_lit(ps[2]) == Some(nn(ScalarTy::Int4)));
}

// ------------------------------------------------------------------------------------------------ the normal form

/// A FROM row qualifies: the join and WHERE conditions hold.
pub open spec fn qual(ps: Seq<Literal>, x: Row) -> bool {
    &&& x.len() == 39
    &&& x[0] == x[9]
    &&& x[0] == x[29]
    &&& x[1] == x[35]
    &&& x[2] == x[36]
    &&& x[5] == Val::Text(p_uom(ps))
    &&& x[32] == Val::Text(p_stmt(ps))
    &&& x[19] == Val::Int(p_fy(ps))
}

/// The group key `(sub.name, pre.stmt, num.tag, pre.plabel)`.
pub open spec fn key_of(x: Row) -> Row {
    seq![x[11], x[32], x[1], x[37]]
}

pub open spec fn coeff_of(v: Val) -> int {
    match v {
        Val::Num { coeff, scale } => coeff,
        _ => 0,
    }
}

pub open spec fn qspec(ps: Seq<Literal>) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| qual(ps, x),
        key: |x: Row| key_of(x),
        arg: |j: int, x: Row| if j == 0 { coeff_of(x[7]) } else { 0 },
        aggs: seq![AggKind::Sum { scale: 4 }, AggKind::Count],
        outs: seq![0nat, 1, 2, 3, 4, 5],
        grouped: true,
    }
}

/// The FROM relation `(num x sub) x pre`.
pub open spec fn joined(db: Database) -> Seq<Row> {
    product_rows(product_rows(db.tables[1], db.tables[0]), db.tables[3])
}

// ------------------------------------------------------------------------------------------------ the AST

pub open spec fn eq_cols(a: nat, b: nat) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(a), b: Expr::Col(b) }
}

pub open spec fn eq_lit(a: nat, l: Literal) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(a), b: Expr::Lit(l) }
}

pub open spec fn pred38() -> Pred {
    eq_cols(0, 9)
}

pub open spec fn pred35() -> Pred {
    Pred::And(Box::new(Pred::And(Box::new(eq_cols(0, 29)), Box::new(eq_cols(1, 35)))), Box::new(eq_cols(2, 36)))
}

pub open spec fn pred24(ps: Seq<Literal>) -> Pred {
    Pred::And(
        Box::new(Pred::And(
            Box::new(Pred::And(Box::new(eq_lit(5, ps[0])), Box::new(eq_lit(32, ps[1])))),
            Box::new(eq_lit(19, ps[2])),
        )),
        Box::new(Pred::Not(Box::new(Pred::IsNull(Expr::Col(7))))),
    )
}

pub open spec fn q_prod1() -> Query {
    Query::Product { left: Box::new(Query::Table(1)), right: Box::new(Query::Table(0)) }
}

pub open spec fn q_ns() -> Query {
    Query::Filter { pred: pred38(), input: Box::new(q_prod1()) }
}

pub open spec fn q_prod2() -> Query {
    Query::Product { left: Box::new(q_ns()), right: Box::new(Query::Table(3)) }
}

pub open spec fn q_nsp() -> Query {
    Query::Filter { pred: pred35(), input: Box::new(q_prod2()) }
}

pub open spec fn q_where(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: pred24(ps), input: Box::new(q_nsp()) }
}

pub open spec fn key_exprs() -> Seq<Expr> {
    seq![Expr::Col(11), Expr::Col(32), Expr::Col(1), Expr::Col(37)]
}

pub open spec fn agg_exprs() -> Seq<Agg> {
    seq![Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(7) }, Agg::CountStar]
}

pub open spec fn order_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 4, desc: true, nulls_first: true }]
}

pub open spec fn q_body(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: key_exprs(), aggs: agg_exprs(), input: Box::new(q_where(ps)) }
}

/// The statement is the GROUP BY over the WHERE, ordered by column 4 descending, LIMIT 200.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures
        query_spec_at(ps).body == q_body(ps),
        query_spec_at(ps).keys == order_keys(),
        query_spec_at(ps).limit == Some(200nat),
        query_spec_at(ps).offset == 0,
{
}

// ------------------------------------------------------------------------------------------------ row typing

pub open spec fn is_text(v: Val) -> bool {
    v is Text
}

pub open spec fn text_or_null(v: Val) -> bool {
    v is Text || v is Null
}

pub open spec fn num_ok(r: Row) -> bool {
    &&& r.len() == 9
    &&& is_text(r[0]) && is_text(r[1]) && is_text(r[2]) && is_text(r[5])
    &&& r[7] is Num && r[7]->Num_scale == 4 && abs(r[7]->Num_coeff) < pow10(28)
}

pub open spec fn sub_ok(r: Row) -> bool {
    &&& r.len() == 20
    &&& is_text(r[0]) && is_text(r[2])
    &&& (r[10] is Int || r[10] is Null)
}

pub open spec fn pre_ok(r: Row) -> bool {
    &&& r.len() == 10
    &&& is_text(r[0]) && text_or_null(r[3]) && is_text(r[6]) && is_text(r[7]) && text_or_null(r[8])
}

/// The base facts of a database of the schema in the semantics' domain.
pub open spec fn tables_ok(db: Database) -> bool {
    &&& db.tables.len() == 4
    &&& forall|i: int| 0 <= i < db.tables[1].len() ==> num_ok(#[trigger] db.tables[1][i])
    &&& forall|i: int| 0 <= i < db.tables[0].len() ==> sub_ok(#[trigger] db.tables[0][i])
    &&& forall|i: int| 0 <= i < db.tables[3].len() ==> pre_ok(#[trigger] db.tables[3][i])
}

proof fn lemma_schema_columns()
    ensures
        schema_spec().len() == 4,
        schema_spec()[1].columns.len() == 9,
        schema_spec()[1].columns[0] == (Column { ty: SqlType::Text, nullable: false }),
        schema_spec()[1].columns[1] == (Column { ty: SqlType::Text, nullable: false }),
        schema_spec()[1].columns[2] == (Column { ty: SqlType::Text, nullable: false }),
        schema_spec()[1].columns[5] == (Column { ty: SqlType::Text, nullable: false }),
        schema_spec()[1].columns[7] == (Column { ty: SqlType::Numeric { precision: 28, scale: 4 }, nullable: false }),
        schema_spec()[0].columns.len() == 20,
        schema_spec()[0].columns[0] == (Column { ty: SqlType::Text, nullable: false }),
        schema_spec()[0].columns[2] == (Column { ty: SqlType::Text, nullable: false }),
        schema_spec()[0].columns[10] == (Column { ty: SqlType::Int4, nullable: true }),
        schema_spec()[3].columns.len() == 10,
        schema_spec()[3].columns[0] == (Column { ty: SqlType::Text, nullable: false }),
        schema_spec()[3].columns[3] == (Column { ty: SqlType::Text, nullable: true }),
        schema_spec()[3].columns[6] == (Column { ty: SqlType::Text, nullable: false }),
        schema_spec()[3].columns[7] == (Column { ty: SqlType::Text, nullable: false }),
        schema_spec()[3].columns[8] == (Column { ty: SqlType::Text, nullable: true }),
{
    assert(schema_spec().len() == 4) by (compute);
    assert(schema_spec()[1].columns.len() == 9) by (compute);
    assert(schema_spec()[1].columns[0] == Column { ty: SqlType::Text, nullable: false }) by (compute);
    assert(schema_spec()[1].columns[1] == Column { ty: SqlType::Text, nullable: false }) by (compute);
    assert(schema_spec()[1].columns[2] == Column { ty: SqlType::Text, nullable: false }) by (compute);
    assert(schema_spec()[1].columns[5] == Column { ty: SqlType::Text, nullable: false }) by (compute);
    assert(schema_spec()[1].columns[7] == Column { ty: SqlType::Numeric { precision: 28, scale: 4 }, nullable: false }) by (compute);
    assert(schema_spec()[0].columns.len() == 20) by (compute);
    assert(schema_spec()[0].columns[0] == Column { ty: SqlType::Text, nullable: false }) by (compute);
    assert(schema_spec()[0].columns[2] == Column { ty: SqlType::Text, nullable: false }) by (compute);
    assert(schema_spec()[0].columns[10] == Column { ty: SqlType::Int4, nullable: true }) by (compute);
    assert(schema_spec()[3].columns.len() == 10) by (compute);
    assert(schema_spec()[3].columns[0] == Column { ty: SqlType::Text, nullable: false }) by (compute);
    assert(schema_spec()[3].columns[3] == Column { ty: SqlType::Text, nullable: true }) by (compute);
    assert(schema_spec()[3].columns[6] == Column { ty: SqlType::Text, nullable: false }) by (compute);
    assert(schema_spec()[3].columns[7] == Column { ty: SqlType::Text, nullable: false }) by (compute);
    assert(schema_spec()[3].columns[8] == Column { ty: SqlType::Text, nullable: true }) by (compute);
}

pub proof fn lemma_tables_ok(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures tables_ok(db),
{
    lemma_schema_columns();
    let s = schema_spec();
    assert forall|i: int| 0 <= i < db.tables[1].len() implies num_ok(#[trigger] db.tables[1][i]) by {
        let r = db.tables[1][i];
        assert(row_in_table(r, s[1]));
        assert(value_in_column(r[0], s[1].columns[0]));
        assert(value_in_column(r[1], s[1].columns[1]));
        assert(value_in_column(r[2], s[1].columns[2]));
        assert(value_in_column(r[5], s[1].columns[5]));
        assert(value_in_column(r[7], s[1].columns[7]));
    }
    assert forall|i: int| 0 <= i < db.tables[0].len() implies sub_ok(#[trigger] db.tables[0][i]) by {
        let r = db.tables[0][i];
        assert(row_in_table(r, s[0]));
        assert(value_in_column(r[0], s[0].columns[0]));
        assert(value_in_column(r[2], s[0].columns[2]));
        assert(value_in_column(r[10], s[0].columns[10]));
    }
    assert forall|i: int| 0 <= i < db.tables[3].len() implies pre_ok(#[trigger] db.tables[3][i]) by {
        let r = db.tables[3][i];
        assert(row_in_table(r, s[3]));
        assert(value_in_column(r[0], s[3].columns[0]));
        assert(value_in_column(r[3], s[3].columns[3]));
        assert(value_in_column(r[6], s[3].columns[6]));
        assert(value_in_column(r[7], s[3].columns[7]));
        assert(value_in_column(r[8], s[3].columns[8]));
    }
}

/// A joined row: one row of each table, concatenated.
pub open spec fn joined_ok(x: Row) -> bool {
    &&& x.len() == 39
    &&& is_text(x[0]) && is_text(x[1]) && is_text(x[2]) && is_text(x[5])
    &&& x[7] is Num && x[7]->Num_scale == 4 && abs(x[7]->Num_coeff) < pow10(28)
    &&& is_text(x[9]) && is_text(x[11]) && (x[19] is Int || x[19] is Null)
    &&& is_text(x[29]) && text_or_null(x[32]) && is_text(x[35]) && is_text(x[36]) && text_or_null(x[37])
}

proof fn lemma_concat_ok(n: Row, s: Row, p: Row)
    requires num_ok(n), sub_ok(s), pre_ok(p),
    ensures joined_ok(n + s + p), (n + s + p).subrange(0, 29) == n + s,
{
    let x = n + s + p;
    assert(x[0] == n[0] && x[1] == n[1] && x[2] == n[2] && x[5] == n[5] && x[7] == n[7]);
    assert(x[9] == s[0] && x[11] == s[2] && x[19] == s[10]);
    assert(x[29] == p[0] && x[32] == p[3] && x[35] == p[6] && x[36] == p[7] && x[37] == p[8]);
    assert(x.subrange(0, 29) =~= n + s);
}

proof fn lemma_ns_rows(db: Database)
    requires tables_ok(db),
    ensures
        forall|k: int| 0 <= k < product_rows(db.tables[1], db.tables[0]).len() ==> {
            let y = #[trigger] product_rows(db.tables[1], db.tables[0])[k];
            &&& y.len() == 29 && is_text(y[0]) && is_text(y[9])
            &&& exists|a: int, b: int| 0 <= a < db.tables[1].len() && 0 <= b < db.tables[0].len()
                && y == db.tables[1][a] + db.tables[0][b]
        },
{
    let (nt, st) = (db.tables[1], db.tables[0]);
    lemma_product_rows_elems(nt, st);
    assert forall|k: int| 0 <= k < product_rows(nt, st).len() implies {
        let y = #[trigger] product_rows(nt, st)[k];
        &&& y.len() == 29 && is_text(y[0]) && is_text(y[9])
        &&& exists|a: int, b: int| 0 <= a < nt.len() && 0 <= b < st.len() && y == nt[a] + st[b]
    } by {
        let y = product_rows(nt, st)[k];
        assert(is_concat(y, nt, st));
        let (a, b) = choose|a: int, b: int| 0 <= a < nt.len() && 0 <= b < st.len() && y == #[trigger] nt[a] + #[trigger] st[b];
        assert(num_ok(nt[a]) && sub_ok(st[b]));
        assert(y[0] == nt[a][0] && y[9] == st[b][0]);
    }
}

/// `x` is one row of each table, concatenated.
pub open spec fn from_tables(db: Database, x: Row) -> bool {
    exists|a: int, b: int, c: int|
        0 <= a < db.tables[1].len() && 0 <= b < db.tables[0].len() && 0 <= c < db.tables[3].len()
        && x == db.tables[1][a] + db.tables[0][b] + db.tables[3][c]
}

/// Every row of `R` is one row of each table, and is `joined_ok`.
pub proof fn lemma_joined_rows(db: Database)
    requires tables_ok(db),
    ensures
        forall|k: int| 0 <= k < joined(db).len() ==> joined_ok(#[trigger] joined(db)[k]),
        forall|k: int| 0 <= k < joined(db).len() ==> (#[trigger] joined(db)[k]).subrange(0, 29)[0] == joined(db)[k][0]
            && joined(db)[k].subrange(0, 29)[9] == joined(db)[k][9],
        forall|k: int| 0 <= k < joined(db).len() ==> from_tables(db, #[trigger] joined(db)[k]),
{
    let ns = product_rows(db.tables[1], db.tables[0]);
    let pt = db.tables[3];
    lemma_ns_rows(db);
    lemma_product_rows_elems(ns, pt);
    assert forall|k: int| 0 <= k < joined(db).len() implies joined_ok(#[trigger] joined(db)[k])
        && joined(db)[k].subrange(0, 29)[0] == joined(db)[k][0] && joined(db)[k].subrange(0, 29)[9] == joined(db)[k][9]
        && from_tables(db, joined(db)[k]) by {
        let x = joined(db)[k];
        assert(is_concat(x, ns, pt));
        let (i, c) = choose|i: int, c: int| 0 <= i < ns.len() && 0 <= c < pt.len() && x == #[trigger] ns[i] + #[trigger] pt[c];
        let y = ns[i];
        let (a, b) = choose|a: int, b: int| 0 <= a < db.tables[1].len() && 0 <= b < db.tables[0].len()
            && y == db.tables[1][a] + db.tables[0][b];
        lemma_concat_ok(db.tables[1][a], db.tables[0][b], pt[c]);
        assert(x == db.tables[1][a] + db.tables[0][b] + pt[c]);
    }
}

// ------------------------------------------------------------------------------------------------ conditions

/// Text equality of two text values is the SQL `=`.
proof fn lemma_eq_cols(db: Database, x: Row, a: nat, b: nat)
    requires a < x.len(), b < x.len(), is_text(x[a as int]), is_text(x[b as int]),
    ensures eval_pred(db, x, eq_cols(a, b)) == Ok::<Truth, SqlError>(truth_of(x[a as int] == x[b as int])),
{
    lemma_expr_col(db, x, a);
    lemma_expr_col(db, x, b);
    lemma_pred_text_cmp(db, x, CmpOp::Eq, Expr::Col(a), Expr::Col(b), x[a as int]->Text_0, x[b as int]->Text_0);
}

proof fn lemma_eval_pred38(db: Database, y: Row)
    requires y.len() == 29, is_text(y[0]), is_text(y[9]),
    ensures eval_pred(db, y, pred38()) == Ok::<Truth, SqlError>(truth_of(y[0] == y[9])),
{
    lemma_eq_cols(db, y, 0, 9);
}

pub open spec fn cond35(x: Row) -> bool {
    x[0] == x[29] && x[1] == x[35] && x[2] == x[36]
}

proof fn lemma_eval_pred35(db: Database, x: Row)
    requires joined_ok(x),
    ensures eval_pred(db, x, pred35()) == Ok::<Truth, SqlError>(truth_of(cond35(x))),
{
    lemma_eq_cols(db, x, 0, 29);
    lemma_eq_cols(db, x, 1, 35);
    lemma_eq_cols(db, x, 2, 36);
    lemma_pred_and(db, x, eq_cols(0, 29), eq_cols(1, 35), x[0] == x[29], x[1] == x[35]);
    lemma_pred_and(db, x, Pred::And(Box::new(eq_cols(0, 29)), Box::new(eq_cols(1, 35))), eq_cols(2, 36),
        x[0] == x[29] && x[1] == x[35], x[2] == x[36]);
}

pub open spec fn cond24(ps: Seq<Literal>, x: Row) -> bool {
    x[5] == Val::Text(p_uom(ps)) && x[32] == Val::Text(p_stmt(ps)) && x[19] == Val::Int(p_fy(ps))
}

/// The WHERE condition is `True` exactly when `cond24` holds (it is `Unknown` on a NULL stmt or fy).
proof fn lemma_eval_pred24(db: Database, ps: Seq<Literal>, x: Row)
    requires joined_ok(x), ps_ok(ps),
    ensures
        eval_pred(db, x, pred24(ps)) is Ok,
        (eval_pred(db, x, pred24(ps))->Ok_0 == Truth::True) == cond24(ps, x),
{
    let (b0, b1, v) = (p_uom(ps), p_stmt(ps), p_fy(ps));
    lemma_expr_col(db, x, 5);
    lemma_expr_col(db, x, 32);
    lemma_expr_col(db, x, 19);
    lemma_expr_col(db, x, 7);
    assert(eval_expr(db, x, Expr::Lit(ps[0])) == Ok::<Val, SqlError>(Val::Text(b0)));
    assert(eval_expr(db, x, Expr::Lit(ps[1])) == Ok::<Val, SqlError>(Val::Text(b1)));
    assert(int_in_range(IntKind::Int4, v));
    assert(eval_expr(db, x, Expr::Lit(ps[2])) == Ok::<Val, SqlError>(Val::Int(v)));
    // uom
    lemma_pred_text_cmp(db, x, CmpOp::Eq, Expr::Col(5), Expr::Lit(ps[0]), x[5]->Text_0, b0);
    let t1 = truth_of(x[5] == Val::Text(b0));
    assert(eval_pred(db, x, eq_lit(5, ps[0])) == Ok::<Truth, SqlError>(t1));
    // stmt: Unknown when NULL
    let t2 = if x[32] is Null { Truth::Unknown } else { truth_of(x[32] == Val::Text(b1)) };
    if x[32] is Text {
        lemma_pred_text_cmp(db, x, CmpOp::Eq, Expr::Col(32), Expr::Lit(ps[1]), x[32]->Text_0, b1);
    }
    assert(eval_pred(db, x, eq_lit(32, ps[1])) == Ok::<Truth, SqlError>(t2));
    // fy: Unknown when NULL
    let t3 = if x[19] is Null { Truth::Unknown } else { truth_of(x[19] == Val::Int(v)) };
    if x[19] is Int {
        lemma_compare_int(x[19]->Int_0, v);
        lemma_pred_cmp(db, x, CmpOp::Eq, Expr::Col(19), Expr::Lit(ps[2]), x[19], Val::Int(v), x[19]->Int_0, v);
    }
    assert(eval_pred(db, x, eq_lit(19, ps[2])) == Ok::<Truth, SqlError>(t3));
    // value IS NOT NULL
    assert(eval_pred(db, x, Pred::IsNull(Expr::Col(7))) == Ok::<Truth, SqlError>(Truth::False));
    assert(eval_pred(db, x, Pred::Not(Box::new(Pred::IsNull(Expr::Col(7))))) == Ok::<Truth, SqlError>(Truth::True));
    let a12 = truth_and(t1, t2);
    let a123 = truth_and(a12, t3);
    assert(eval_pred(db, x, Pred::And(Box::new(eq_lit(5, ps[0])), Box::new(eq_lit(32, ps[1])))) == Ok::<Truth, SqlError>(a12));
    assert(eval_pred(db, x, Pred::And(
        Box::new(Pred::And(Box::new(eq_lit(5, ps[0])), Box::new(eq_lit(32, ps[1])))),
        Box::new(eq_lit(19, ps[2])))) == Ok::<Truth, SqlError>(a123));
    assert(eval_pred(db, x, pred24(ps)) == Ok::<Truth, SqlError>(truth_and(a123, Truth::True)));
}

// ------------------------------------------------------------------------------------------------ WHERE over truths

/// `keep_true` keeps exactly the rows whose truth is `True` (for any three-valued truths).
proof fn lemma_keep_true_keep3(rows: Seq<Row>, truths: Seq<Truth>, f: spec_fn(Row) -> bool)
    requires
        truths.len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] truths[i] == Truth::True) == f(rows[i]),
    ensures keep_true(rows, truths) == keep(rows, f),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let (ri, ti) = (rows.drop_last(), truths.drop_last());
        assert forall|i: int| 0 <= i < ri.len() implies (#[trigger] ti[i] == Truth::True) == f(ri[i]) by {
            assert(ti[i] == truths[i] && ri[i] == rows[i]);
        }
        lemma_keep_true_keep3(ri, ti, f);
        assert((truths[rows.len() - 1] == Truth::True) == f(rows[rows.len() - 1]));
    }
}

/// A WHERE whose condition evaluates without error on every row reaching it, `True` exactly when `h` holds.
proof fn lemma_eval_filter3(db: Database, src: Query, rows: Seq<Row>, f: spec_fn(Row) -> bool, pred: Pred,
    h: spec_fn(Row) -> bool, fh: spec_fn(Row) -> bool)
    requires
        eval_query(db, Seq::empty(), src) == Ok::<Relation, SqlError>(keep(rows, f)),
        forall|i: int| 0 <= i < rows.len() && f(#[trigger] rows[i]) ==>
            eval_pred(db, rows[i], pred) is Ok && (eval_pred(db, rows[i], pred)->Ok_0 == Truth::True) == h(rows[i]),
        forall|i: int| 0 <= i < rows.len() ==> fh(#[trigger] rows[i]) == (f(rows[i]) && h(rows[i])),
    ensures
        eval_query(db, Seq::empty(), Query::Filter { pred, input: Box::new(src) }) == Ok::<Relation, SqlError>(keep(rows, fh)),
{
    let kept = keep(rows, f);
    let ctx = Seq::<Val>::empty();
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
    assert forall|i: int| 0 <= i < kept.len() implies (#[trigger] truths[i] == Truth::True) == h(kept[i]) by {
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
        assert(f(rows[m]));
    }
    lemma_keep_true_keep3(kept, truths, h);
    lemma_keep_keep(rows, f, h);
    lemma_keep_ext(rows, |x: Row| f(x) && h(x), fh);
}

// ------------------------------------------------------------------------------------------------ the FROM/WHERE chain

pub open spec fn true_row() -> spec_fn(Row) -> bool {
    |r: Row| true
}

pub open spec fn f38(y: Row) -> bool {
    y[0] == y[9]
}

pub open spec fn f_ns_p(x: Row) -> bool {
    x[0] == x[9]
}

pub open spec fn f_nsp(x: Row) -> bool {
    x[0] == x[9] && cond35(x)
}

/// The WHERE input: `R` kept by the join conditions.
proof fn lemma_eval_nsp(db: Database)
    requires tables_ok(db),
    ensures eval_query(db, Seq::empty(), q_nsp()) == Ok::<Relation, SqlError>(keep(joined(db), |x: Row| f_nsp(x))),
{
    let (nt, st, pt) = (db.tables[1], db.tables[0], db.tables[3]);
    let ns = product_rows(nt, st);
    let tr = true_row();
    lemma_eval_table(db, 1, tr);
    lemma_eval_table(db, 0, tr);
    assert forall|i: int| 0 <= i < nt.len() implies (#[trigger] nt[i]).len() == 9 by {
        assert(num_ok(nt[i]));
    }
    lemma_eval_product(db, Query::Table(1), Query::Table(0), nt, tr, 9, st, tr, ns, tr);
    lemma_ns_rows(db);
    assert forall|i: int| 0 <= i < ns.len() && tr(#[trigger] ns[i]) implies
        eval_pred(db, ns[i], pred38()) == Ok::<Truth, SqlError>(truth_of(f38(ns[i]))) by {
        lemma_eval_pred38(db, ns[i]);
    }
    let ff38 = |y: Row| f38(y);
    lemma_eval_filter(db, q_prod1(), ns, tr, pred38(), ff38, ff38);
    // (num x sub) filtered, times pre
    lemma_eval_table(db, 3, tr);
    assert forall|i: int| 0 <= i < ns.len() implies (#[trigger] ns[i]).len() == 29 by {}
    lemma_joined_rows(db);
    let fp = |x: Row| f_ns_p(x);
    assert forall|i: int| 0 <= i < joined(db).len() implies fp(#[trigger] joined(db)[i])
        == (ff38(left_of(joined(db)[i], 29)) && tr(right_of(joined(db)[i], 29))) by {
        let x = joined(db)[i];
        assert(left_of(x, 29) == x.subrange(0, 29));
    }
    lemma_eval_product(db, q_ns(), Query::Table(3), ns, ff38, 29, pt, tr, joined(db), fp);
    // join conditions with pre
    assert forall|i: int| 0 <= i < joined(db).len() && fp(#[trigger] joined(db)[i]) implies
        eval_pred(db, joined(db)[i], pred35()) == Ok::<Truth, SqlError>(truth_of(cond35(joined(db)[i]))) by {
        lemma_eval_pred35(db, joined(db)[i]);
    }
    let c35 = |x: Row| cond35(x);
    lemma_eval_filter(db, q_prod2(), joined(db), fp, pred35(), c35, |x: Row| f_nsp(x));
}

/// The WHERE output: `R` kept by `qual`.
pub proof fn lemma_eval_where(db: Database, ps: Seq<Literal>)
    requires tables_ok(db), ps_ok(ps),
    ensures eval_query(db, Seq::empty(), q_where(ps)) == Ok::<Relation, SqlError>(keep(joined(db), |x: Row| qual(ps, x))),
{
    lemma_eval_nsp(db);
    lemma_joined_rows(db);
    let r = joined(db);
    assert forall|i: int| 0 <= i < r.len() && f_nsp(#[trigger] r[i]) implies
        eval_pred(db, r[i], pred24(ps)) is Ok && (eval_pred(db, r[i], pred24(ps))->Ok_0 == Truth::True) == cond24(ps, r[i]) by {
        lemma_eval_pred24(db, ps, r[i]);
    }
    assert forall|i: int| 0 <= i < r.len() implies qual(ps, #[trigger] r[i]) == (f_nsp(r[i]) && cond24(ps, r[i])) by {
        assert(joined_ok(r[i]));
    }
    lemma_eval_filter3(db, q_nsp(), r, |x: Row| f_nsp(x), pred24(ps), |x: Row| cond24(ps, x), |x: Row| qual(ps, x));
}

// ------------------------------------------------------------------------------------------------ GROUP BY

pub open spec fn id_cols() -> Seq<nat> {
    Seq::new(39, |i: int| i as nat)
}

/// Projecting 39-value rows on all their columns keeps them.
pub proof fn lemma_proj_id(rows: Seq<Row>)
    requires forall|i: int| 0 <= i < rows.len() ==> (#[trigger] rows[i]).len() == 39,
    ensures proj_all(rows, id_cols()) == rows,
{
    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] proj_all(rows, id_cols())[i] == rows[i] by {
        assert(proj(rows[i], id_cols()) =~= rows[i]);
    }
    assert(proj_all(rows, id_cols()) =~= rows);
}

/// Text-or-NULL values: SQL "not distinct" is equality.
proof fn lemma_val_nd(a: Val, b: Val)
    requires text_or_null(a), text_or_null(b),
    ensures val_not_distinct(a, b) == (a == b),
{
    if a is Text && b is Text {
        lemma_lex_cmp_zero(a->Text_0, b->Text_0);
    }
}

pub open spec fn key_ok(k: Row) -> bool {
    k.len() == 4 && is_text(k[0]) && text_or_null(k[1]) && is_text(k[2]) && text_or_null(k[3])
}

/// Keys of text-or-NULL values: SQL "not distinct" is equality.
pub proof fn lemma_key_nd(u: Row, v: Row)
    requires key_ok(u), key_ok(v),
    ensures row_not_distinct(u, v) == (u == v),
{
    lemma_val_nd(u[0], v[0]);
    lemma_val_nd(u[1], v[1]);
    lemma_val_nd(u[2], v[2]);
    lemma_val_nd(u[3], v[3]);
    if row_not_distinct(u, v) {
        assert(val_not_distinct(u[0], v[0]) && val_not_distinct(u[1], v[1]));
        assert(val_not_distinct(u[2], v[2]) && val_not_distinct(u[3], v[3]));
        assert(u =~= v);
    }
}

pub proof fn lemma_key_of_ok(x: Row)
    requires joined_ok(x),
    ensures key_ok(key_of(x)),
{
    let k = key_of(x);
    assert(k.len() == 4);
    assert(k[0] == x[11]);
    assert(k[1] == x[32]);
    assert(k[2] == x[1]);
    assert(k[3] == x[37]);
    assert(is_text(k[0]) && text_or_null(k[1]) && is_text(k[2]) && text_or_null(k[3]));
}

proof fn lemma_input_kept(db: Database, ps: Seq<Literal>)
    requires tables_ok(db), ps_ok(ps),
    ensures
        eval_query(db, Seq::empty(), q_where(ps)) == Ok::<Relation, SqlError>(keep_true(joined(db),
            qual_truths(qspec(ps), proj_all(joined(db), id_cols())))),
        proj_all(joined(db), id_cols()) == joined(db),
{
    let g = qspec(ps);
    let r = joined(db);
    let cols = id_cols();
    lemma_joined_rows(db);
    assert forall|i: int| 0 <= i < r.len() implies (#[trigger] r[i]).len() == 39 by {
        assert(joined_ok(r[i]));
    }
    lemma_proj_id(r);
    lemma_eval_where(db, ps);
    let truths = qual_truths(g, proj_all(r, cols));
    lemma_keep_true_keep(r, truths, g.qual);
    lemma_keep_ext(r, |x: Row| qual(ps, x), g.qual);
}

proof fn lemma_keys_agree(db: Database, ps: Seq<Literal>)
    requires tables_ok(db), proj_all(joined(db), id_cols()) == joined(db),
    ensures keys_agree(db, joined(db), id_cols(), key_exprs(), qspec(ps)),
{
    hide(eval_exprs);
    let g = qspec(ps);
    let r = joined(db);
    let cols = id_cols();
    let kidx = seq![11nat, 32, 1, 37];
    assert(key_exprs() =~= col_exprs(kidx));
    lemma_joined_rows(db);
    assert forall|i: int| 0 <= i < r.len() && (g.qual)(proj(#[trigger] r[i], cols)) implies
        eval_exprs(db, r[i], key_exprs()) == Ok::<Row, SqlError>((g.key)(proj(r[i], cols))) by {
        assert(proj(r[i], cols) == proj_all(r, cols)[i]);
        assert(joined_ok(r[i]));
        lemma_eval_cols(db, r[i], kidx);
        assert(select(r[i], kidx) =~= key_of(r[i]));
    }
}

proof fn lemma_arg_one(db: Database, ps: Seq<Literal>, x: Row)
    requires joined_ok(x),
    ensures agg_args(db, x, agg_exprs()) == Ok::<Row, SqlError>(arg_vals(qspec(ps), x)),
{
    hide(eval_expr);
    hide(agg_arg);
    let g = qspec(ps);
    let rs = agg_arg_results(db, x, agg_exprs());
    lemma_agg_arg_results_index(db, x, agg_exprs());
    lemma_expr_col(db, x, 7);
    lemma_agg_arg_sum(db, x, NumKind::Numeric, Expr::Col(7));
    lemma_agg_arg_count(db, x);
    let vals = arg_vals(g, x);
    assert(vals[0] == Val::Num { coeff: coeff_of(x[7]), scale: 4 });
    assert(x[7] == Val::Num { coeff: coeff_of(x[7]), scale: 4 });
    assert(rs[0] == Ok::<Val, SqlError>(vals[0]));
    assert(rs[1] == Ok::<Val, SqlError>(vals[1]));
    assert forall|j: int| 0 <= j < rs.len() implies #[trigger] rs[j] == Ok::<Val, SqlError>(vals[j]) by {
        if j == 0 {} else {}
    }
    lemma_collect_all(rs, vals);
}

proof fn lemma_args_agree(db: Database, ps: Seq<Literal>)
    requires tables_ok(db), proj_all(joined(db), id_cols()) == joined(db),
    ensures args_agree(db, joined(db), id_cols(), agg_exprs(), qspec(ps)),
{
    hide(agg_args);
    let g = qspec(ps);
    let r = joined(db);
    let cols = id_cols();
    lemma_joined_rows(db);
    assert forall|i: int| 0 <= i < r.len() && (g.qual)(proj(#[trigger] r[i], cols)) implies
        agg_args(db, r[i], agg_exprs()) == Ok::<Row, SqlError>(arg_vals(g, proj(r[i], cols))) by {
        assert(proj(r[i], cols) == proj_all(r, cols)[i]);
        assert(joined_ok(r[i]));
        lemma_arg_one(db, ps, r[i]);
    }
}

proof fn lemma_keys_exact(db: Database, ps: Seq<Literal>)
    requires tables_ok(db), proj_all(joined(db), id_cols()) == joined(db),
    ensures keys_exact(qspec(ps), proj_all(joined(db), id_cols())),
{
    let g = qspec(ps);
    let r = joined(db);
    lemma_joined_rows(db);
    assert forall|a: int, b: int| 0 <= a < r.len() && 0 <= b < r.len() && (g.qual)(r[a]) && (g.qual)(r[b]) implies
        (row_not_distinct(#[trigger] (g.key)(r[a]), #[trigger] (g.key)(r[b])) <==> (g.key)(r[a]) == (g.key)(r[b])) by {
        assert(joined_ok(r[a]) && joined_ok(r[b]));
        lemma_key_of_ok(r[a]);
        lemma_key_of_ok(r[b]);
        lemma_key_nd(key_of(r[a]), key_of(r[b]));
    }
}

proof fn lemma_aggs_match(ps: Seq<Literal>)
    ensures aggs_match(agg_exprs(), qspec(ps)),
{
    let g = qspec(ps);
    assert forall|j: int| 0 <= j < agg_exprs().len() implies agg_matches(#[trigger] agg_exprs()[j], g.aggs[j]) by {
        if j == 0 {} else {}
    }
}

/// The body (GROUP BY over the WHERE) evaluates to the normal form's group rows, when the groups are inside
/// `group_caps`.
pub proof fn lemma_eval_body(db: Database, ps: Seq<Literal>)
    requires tables_ok(db), ps_ok(ps), group_caps(qspec(ps), joined(db)),
    ensures
        eval_query(db, Seq::empty(), q_body(ps))
            == Ok::<Relation, SqlError>(gkeys(qspec(ps), joined(db)).map_values(|k: Row| full_row(qspec(ps), joined(db), k))),
{
    hide(eval_query);
    lemma_input_kept(db, ps);
    lemma_keys_agree(db, ps);
    lemma_args_agree(db, ps);
    lemma_keys_exact(db, ps);
    lemma_aggs_match(ps);
    lemma_group_query(db, joined(db), id_cols(), q_where(ps), key_exprs(), agg_exprs(), qspec(ps));
}

/// Every group key is the key of a qualifying row (four text-or-NULL values).
pub proof fn lemma_gkey_ok(db: Database, ps: Seq<Literal>, k: Row)
    requires tables_ok(db), gkeys(qspec(ps), joined(db)).contains(k),
    ensures key_ok(k), gcount(qspec(ps), joined(db), k) > 0,
{
    let g = qspec(ps);
    let r = joined(db);
    lemma_gkeys_witness(g, r, k);
    let m = choose|m: int| 0 <= m < r.len() && #[trigger] hit(g, r[m], k);
    lemma_joined_rows(db);
    assert(joined_ok(r[m]));
}

/// The body's rows are the normal form's result rows.
pub proof fn lemma_denote_body(db: Database, ps: Seq<Literal>)
    requires tables_ok(db), ps_ok(ps), group_caps(qspec(ps), joined(db)),
    ensures denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(result_rows(qspec(ps), joined(db))),
{
    let g = qspec(ps);
    let r = joined(db);
    lemma_query_shape(ps);
    lemma_eval_body(db, ps);
    let ks = gkeys(g, r);
    assert forall|i: int| 0 <= i < ks.len() implies
        #[trigger] out_row(g, r, ks[i]) == full_row(g, r, ks[i]) by {
        assert(ks.contains(ks[i]));
        lemma_gkey_ok(db, ps, ks[i]);
        let fr = full_row(g, r, ks[i]);
        assert(fr.len() == 6);
        lemma_select_identity(fr, g.outs);
    }
    assert(ks.map_values(|k: Row| out_row(g, r, k)) =~= ks.map_values(|k: Row| full_row(g, r, k)));
}

// ------------------------------------------------------------------------------------------------ errors and capacity

/// The GROUP BY's prepared inputs over the kept rows: per row its key and arguments; the distinct keys are the
/// normal form's group keys and a group's members are `members`.
proof fn lemma_group_setup(db: Database, ps: Seq<Literal>)
    requires tables_ok(db), ps_ok(ps),
    ensures ({
        let g = qspec(ps);
        let r = joined(db);
        let kept = keep_true(r, qual_truths(g, proj_all(r, id_cols())));
        let ks = qkeys(g, r);
        let args = qrows(g, r).map_values(|x: Row| arg_vals(g, x));
        &&& eval_query(db, Seq::empty(), q_where(ps)) == Ok::<Relation, SqlError>(kept)
        &&& ks.len() == kept.len() && args.len() == kept.len()
        &&& forall|i: int| 0 <= i < kept.len() ==> #[trigger] group_input(db, Seq::<Val>::empty() + kept[i], key_exprs(), agg_exprs())
            == Ok::<(Row, Row), SqlError>((ks[i], args[i]))
        &&& distinct_rows(ks) == gkeys(g, r)
        &&& forall|k: Row| #[trigger] gkeys(g, r).contains(k) ==> group_members(ks, args, k) == members(g, r, k)
    }),
{
    hide(eval_exprs);
    hide(agg_args);
    let g = qspec(ps);
    let r = joined(db);
    let cols = id_cols();
    lemma_input_kept(db, ps);
    lemma_keys_agree(db, ps);
    lemma_args_agree(db, ps);
    lemma_keys_exact(db, ps);
    lemma_kept_rows(g, r, cols);
    let kept = keep_true(r, qual_truths(g, proj_all(r, cols)));
    let q = qrows(g, r);
    let ks = qkeys(g, r);
    let args = q.map_values(|x: Row| arg_vals(g, x));
    assert(proj_all(kept, cols).len() == kept.len());
    assert forall|i: int| 0 <= i < kept.len() implies #[trigger] group_input(db, Seq::<Val>::empty() + kept[i], key_exprs(), agg_exprs())
        == Ok::<(Row, Row), SqlError>((ks[i], args[i])) by {
        assert(Seq::<Val>::empty() + kept[i] =~= kept[i]);
        let m = choose|m: int| 0 <= m < r.len() && r[m] == kept[i];
        assert(proj(r[m], cols) == proj_all(r, cols)[m]);
        assert(proj(kept[i], cols) == q[i]);
        assert((g.qual)(proj(r[m], cols)));
        assert(eval_exprs(db, r[m], key_exprs()) == Ok::<Row, SqlError>((g.key)(proj(r[m], cols))));
        assert(agg_args(db, r[m], agg_exprs()) == Ok::<Row, SqlError>(arg_vals(g, proj(r[m], cols))));
    }
    let pool = key_pool(g, r);
    lemma_pool_exact(g, r);
    assert forall|i: int| 0 <= i < qkeys(g, r).len() implies pool.contains(#[trigger] qkeys(g, r)[i]) by {
        assert(pool[i] == qkeys(g, r)[i]);
    }
    lemma_distinct_gkeys(g, r, pool);
    assert forall|k: Row| #[trigger] gkeys(g, r).contains(k) implies group_members(ks, args, k) == members(g, r, k) by {
        let t = choose|t: int| 0 <= t < gkeys(g, r).len() && gkeys(g, r)[t] == k;
        assert(pool.contains(gkeys(g, r)[t]));
        lemma_group_members(g, r, k, pool);
    }
}

/// Every aggregate value of every group succeeds or fails with 22003.
proof fn lemma_agg_values(ps: Seq<Literal>, xs: Seq<Row>, k: Row, j: int)
    requires 0 <= j < 2,
    ensures ({
        let v = agg_value(agg_exprs()[j], column(members(qspec(ps), xs, k), j));
        v is Ok || v == Err::<Val, SqlError>(SqlError::NumericValueOutOfRange)
    }),
{
    let g = qspec(ps);
    lemma_members_col(g, xs, k, j);
    let vs = column(members(g, xs, k), j);
    if j == 1 {
        lemma_count_value(Agg::CountStar, vs);
    } else {
        assert(all_of_kind(NumKind::Numeric, vs));
    }
}

/// A group whose count exceeds int8: the body's meaning is the SQL error 22003.
pub proof fn lemma_body_count_err(db: Database, ps: Seq<Literal>, k: Row)
    requires tables_ok(db), ps_ok(ps), gcount(qspec(ps), joined(db), k) > int8_max(),
    ensures denote_body(db, query_spec_at(ps)) == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange),
{
    let g = qspec(ps);
    let r = joined(db);
    lemma_query_shape(ps);
    lemma_group_setup(db, ps);
    let kept = keep_true(r, qual_truths(g, proj_all(r, id_cols())));
    let ks = qkeys(g, r);
    let args = qrows(g, r).map_values(|x: Row| arg_vals(g, x));
    lemma_gkeys(g, r);
    let ds = gkeys(g, r);
    assert(ds.contains(k));
    let gi = choose|t: int| 0 <= t < ds.len() && ds[t] == k;
    assert forall|h: int, j: int| 0 <= h < distinct_rows(ks).len() && 0 <= j < agg_exprs().len()
        implies #[trigger] agg_value(agg_exprs()[j], column(group_members(ks, args, distinct_rows(ks)[h]), j)) is Ok
            || agg_value(agg_exprs()[j], column(group_members(ks, args, distinct_rows(ks)[h]), j))
                == Err::<Val, SqlError>(SqlError::NumericValueOutOfRange) by {
        assert(ds.contains(ds[h]));
        lemma_agg_values(ps, r, ds[h], j);
    }
    lemma_members_col(g, r, k, 1);
    lemma_count_value(Agg::CountStar, column(members(g, r, k), 1));
    assert(agg_value(agg_exprs()[1], column(group_members(ks, args, distinct_rows(ks)[gi]), 1))
        == Err::<Val, SqlError>(SqlError::NumericValueOutOfRange));
    lemma_group_by_err(db, Seq::empty(), key_exprs(), agg_exprs(), Box::new(q_where(ps)), kept, ks, args,
        SqlError::NumericValueOutOfRange, gi, 1);
}

/// The SUM column of a non-empty group: scale 4 and absolute mass `gabs`.
proof fn lemma_members_mass(ps: Seq<Literal>, xs: Seq<Row>, k: Row)
    ensures ({
        let vs = column(members(qspec(ps), xs, k), 0);
        &&& gcount(qspec(ps), xs, k) > 0 ==> num_max_scale(vs) == 4
        &&& gcount(qspec(ps), xs, k) == 0 ==> num_max_scale(vs) == 0
        &&& num_mass_at(vs, 4) == gabs(qspec(ps), xs, k, 0)
    }),
    decreases xs.len(),
{
    let g = qspec(ps);
    let vs = column(members(g, xs, k), 0);
    if xs.len() > 0 {
        let xi = xs.drop_last();
        let x = xs.last();
        lemma_members_mass(ps, xi, k);
        let vsi = column(members(g, xi, k), 0);
        if hit(g, x, k) {
            assert(vs =~= vsi.push(arg_vals(g, x)[0]));
            assert(vs.drop_last() =~= vsi);
            assert(arg_vals(g, x)[0] == Val::Num { coeff: (g.arg)(0, x), scale: 4 });
            assert(pow10(0) == 1);
            assert(abs((g.arg)(0, x)) * pow10(0) == abs((g.arg)(0, x)));
        } else {
            assert(vs =~= vsi);
        }
    } else {
        assert(vs =~= Seq::<Val>::empty());
    }
}

/// Every group count fits int8 and one group's absolute mass exceeds `i128`: outside the capacity domain.
pub proof fn lemma_body_capacity(db: Database, ps: Seq<Literal>, k: Row)
    requires
        tables_ok(db), ps_ok(ps),
        forall|k2: Row| #[trigger] gcount(qspec(ps), joined(db), k2) <= int8_max(),
        gabs(qspec(ps), joined(db), k, 0) > i128::MAX,
    ensures !crate::gendb_entry::capacity_domain(db, query_spec_at(ps)),
{
    let g = qspec(ps);
    let r = joined(db);
    lemma_query_shape(ps);
    lemma_group_setup(db, ps);
    let kept = keep_true(r, qual_truths(g, proj_all(r, id_cols())));
    let ks = qkeys(g, r);
    let args = qrows(g, r).map_values(|x: Row| arg_vals(g, x));
    if gcount(g, r, k) == 0 {
        lemma_zero_count(g, r, k, 0);
    }
    lemma_gkeys(g, r);
    let ds = gkeys(g, r);
    assert(ds.contains(k));
    let gi = choose|t: int| 0 <= t < ds.len() && ds[t] == k;
    assert forall|h: int| 0 <= h < distinct_rows(ks).len() implies #[trigger] aggs_ok_inside(agg_exprs(), group_members(ks, args, distinct_rows(ks)[h])) by {
        let kh = ds[h];
        assert(ds.contains(kh));
        let m = members(g, r, kh);
        assert forall|j: int| 0 <= j < agg_exprs().len() && #[trigger] fits_agg_value(agg_exprs()[j], column(m, j))
            implies agg_value(agg_exprs()[j], column(m, j)) is Ok by {
            lemma_members_col(g, r, kh, j);
            if j == 1 {
                lemma_count_value(Agg::CountStar, column(m, 1));
                assert(gcount(g, r, kh) <= int8_max());
            } else {
                lemma_sum_inside_ok(NumKind::Numeric, Expr::Col(7), column(m, 0));
            }
        }
    }
    let m = members(g, r, k);
    lemma_members_col(g, r, k, 0);
    lemma_members_mass(ps, r, k);
    assert(sum_mass(NumKind::Numeric, column(m, 0)) == gabs(g, r, k, 0));
    assert(!fits_agg_value(agg_exprs()[0], column(group_members(ks, args, distinct_rows(ks)[gi]), 0)));
    lemma_group_by_capacity(db, Seq::empty(), key_exprs(), agg_exprs(), Box::new(q_where(ps)), kept, ks, args, gi, 0);
}

} // verus!
