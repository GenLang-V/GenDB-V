//! SQL meaning of Q12 in normal form (`link::query::QuerySpec` with int4 SUMs, `common::isum`) over the stored
//! relations of `facts`.
//!
//! The statement's body is `GROUP BY l_shipmode` with two `SUM(CASE .. THEN 1 ELSE 0 END)` over the filtered product
//! `orders x lineitem` (orders first: 9 + 16 columns). Its normal form ranges over the product of the stored
//! relations `xs = orel x lrel` (7 + 15 = 22 columns: o_orderkey 0, o_orderpriority 5, then l_orderkey 7,
//! l_shipdate 17, l_commitdate 18, l_receiptdate 19, l_shipmode 21): `q12_qual` is the WHERE condition with the
//! receipt-date window in days `[lo, hi]` (`hi` the last day before `$3 + 1 year`), the key is `[l_shipmode]`, the
//! arguments are 1/0 by the order priority (`q12_arg`).
//!
//! `lemma_body`: the body evaluates to the normal form's rows; `lemma_body_sum_err`: a group sum beyond int8 is
//! error 22003; `lemma_body_date_err`: an error of `$3 + 1 year` is the statement's error on a non-empty product.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::int::*;
use crate::spec::scalar::*;
use crate::spec::eval::*;
use crate::spec::numeric::sign;
use crate::spec::datetime::*;
use crate::spec::relation::*;
use crate::spec::typing::*;
use crate::spec::types::*;
use crate::spec::order::*;
use crate::spec::equality::*;
use crate::link::query::*;
use crate::link::join::{shift, lemma_proj_product};
use crate::link::source::lemma_proj_all_index;
use crate::bridge::collect::*;
use crate::bridge::equality::same_exact_type;
use crate::bridge::relation::{is_concat, lemma_product_rows_elems};
use crate::query::{query_spec_at, param_typed, param_domain};
use crate::schema::schema_spec;
use crate::stores::facts::declaration::*;
use crate::agent::common::isum::*;

verus! {

// ------------------------------------------------------------------------------------------------ statement pieces

/// `'1-URGENT'`.
pub open spec fn urgent() -> Seq<u8> {
    seq![49u8, 45u8, 85u8, 82u8, 71u8, 69u8, 78u8, 84u8]
}

/// `'2-HIGH'`.
pub open spec fn high2() -> Seq<u8> {
    seq![50u8, 45u8, 72u8, 73u8, 71u8, 72u8]
}

pub open spec fn and_p(a: Pred, b: Pred) -> Pred {
    Pred::And(Box::new(a), Box::new(b))
}

pub open spec fn or_p(a: Pred, b: Pred) -> Pred {
    Pred::Or(Box::new(a), Box::new(b))
}

pub open spec fn cmp_p(op: CmpOp, a: Expr, b: Expr) -> Pred {
    Pred::Cmp { op, a, b }
}

/// `$3 + INTERVAL '1' YEAR` (a timestamp).
pub open spec fn hi_expr(ps: Seq<Literal>) -> Expr {
    Expr::AddInterval {
        arg: Box::new(Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(Expr::Lit(ps[2])) }),
        months: 12i32,
        days: 0i32,
        micros: 0i64,
    }
}

/// `o_orderkey = l_orderkey`.
pub open spec fn key_pred() -> Pred {
    cmp_p(CmpOp::Eq, Expr::Col(0), Expr::Col(9))
}

/// `l_shipmode IN ($1, $2)`.
pub open spec fn mode_pred(ps: Seq<Literal>) -> Pred {
    or_p(cmp_p(CmpOp::Eq, Expr::Col(23), Expr::Lit(ps[0])), cmp_p(CmpOp::Eq, Expr::Col(23), Expr::Lit(ps[1])))
}

/// `l_commitdate < l_receiptdate`.
pub open spec fn cr_pred() -> Pred {
    cmp_p(CmpOp::Lt, Expr::Col(20), Expr::Col(21))
}

/// `l_shipdate < l_commitdate`.
pub open spec fn sc_pred() -> Pred {
    cmp_p(CmpOp::Lt, Expr::Col(19), Expr::Col(20))
}

/// `l_receiptdate >= $3`.
pub open spec fn ge_pred(ps: Seq<Literal>) -> Pred {
    cmp_p(CmpOp::Ge, Expr::Col(21), Expr::Lit(ps[2]))
}

/// `l_receiptdate < $3 + INTERVAL '1' YEAR`.
pub open spec fn lt_pred(ps: Seq<Literal>) -> Pred {
    cmp_p(CmpOp::Lt, Expr::Col(21), hi_expr(ps))
}

/// Every conjunct before the last.
pub open spec fn head_pred(ps: Seq<Literal>) -> Pred {
    and_p(and_p(and_p(and_p(key_pred(), mode_pred(ps)), cr_pred()), sc_pred()), ge_pred(ps))
}

/// The WHERE condition.
pub open spec fn where_pred(ps: Seq<Literal>) -> Pred {
    and_p(head_pred(ps), lt_pred(ps))
}

/// `o_orderpriority = '1-URGENT' OR o_orderpriority = '2-HIGH'`.
pub open spec fn hi_cond() -> Pred {
    or_p(cmp_p(CmpOp::Eq, Expr::Col(5), Expr::Lit(Literal::Text(urgent()))),
        cmp_p(CmpOp::Eq, Expr::Col(5), Expr::Lit(Literal::Text(high2()))))
}

/// `o_orderpriority <> '1-URGENT' AND o_orderpriority <> '2-HIGH'`.
pub open spec fn lo_cond() -> Pred {
    and_p(cmp_p(CmpOp::Ne, Expr::Col(5), Expr::Lit(Literal::Text(urgent()))),
        cmp_p(CmpOp::Ne, Expr::Col(5), Expr::Lit(Literal::Text(high2()))))
}

/// `CASE WHEN c THEN 1 ELSE 0 END`.
pub open spec fn one_zero(c: Pred) -> Expr {
    Expr::If {
        cond: Box::new(c),
        then_e: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })),
        else_e: Box::new(Expr::Lit(Literal::Int { v: 0, kind: IntKind::Int4 })),
    }
}

pub open spec fn q12_aggs() -> Seq<Agg> {
    seq![Agg::Sum { kind: NumKind::Int4, arg: one_zero(hi_cond()) }, Agg::Sum { kind: NumKind::Int4, arg: one_zero(lo_cond()) }]
}

pub open spec fn q12_keys() -> Seq<Expr> {
    seq![Expr::Col(23)]
}

/// `FROM orders, lineitem`.
pub open spec fn from_q() -> Query {
    Query::Product { left: Box::new(Query::Table(1)), right: Box::new(Query::Table(0)) }
}

pub open spec fn filter_q(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: where_pred(ps), input: Box::new(from_q()) }
}

/// The ORDER BY key: l_shipmode ascending.
pub open spec fn order_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 0, desc: false, nulls_first: false }]
}

/// The statement, piece by piece.
pub proof fn lemma_statement(ps: Seq<Literal>)
    ensures
        query_spec_at(ps).body == (Query::GroupBy { keys: q12_keys(), aggs: q12_aggs(), input: Box::new(filter_q(ps)) }),
        query_spec_at(ps).keys == order_keys(),
        query_spec_at(ps).offset == 0,
        query_spec_at(ps).limit is None,
{
    assert(q12_aggs() =~= seq![Agg::Sum { kind: NumKind::Int4, arg: one_zero(hi_cond()) }, Agg::Sum { kind: NumKind::Int4, arg: one_zero(lo_cond()) }]);
}

// ------------------------------------------------------------------------------------------------ normal form

/// The bound parameters: `$1`, `$2` bytes and the receipt-date window `[lo, hi]` in days.
pub struct Prm {
    pub p0: Seq<u8>,
    pub p1: Seq<u8>,
    pub lo: int,
    pub hi: int,
}

/// The day count of a date value (0 otherwise; typing excludes it).
pub open spec fn day_of(v: Val) -> int {
    match v {
        Val::Date(d) => d,
        _ => 0,
    }
}

/// A high order priority (`'1-URGENT'` or `'2-HIGH'`).
pub open spec fn prio_high(v: Val) -> bool {
    v == Val::Text(urgent()) || v == Val::Text(high2())
}

/// The WHERE condition over a joined stored row `x = o ++ l` (7 + 15 columns).
pub open spec fn q12_qual(prm: Prm, x: Row) -> bool {
    &&& x[0] == x[7]
    &&& (x[21] == Val::Text(prm.p0) || x[21] == Val::Text(prm.p1))
    &&& day_of(x[18]) < day_of(x[19])
    &&& day_of(x[17]) < day_of(x[18])
    &&& prm.lo <= day_of(x[19])
    &&& day_of(x[19]) <= prm.hi
}

/// Argument of SUM `j` (0: high, 1: low) on a joined stored row: 1 when the order priority belongs to it.
pub open spec fn q12_arg(j: int, x: Row) -> int {
    if (j == 0) == prio_high(x[5]) { 1 } else { 0 }
}

/// Q12 in normal form over the joined stored rows.
pub open spec fn q12_g(prm: Prm) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| q12_qual(prm, x),
        key: |x: Row| seq![x[21]],
        arg: |j: int, x: Row| q12_arg(j, x),
        aggs: seq![AggKind::Sum { scale: 0 }, AggKind::Sum { scale: 0 }],
        outs: seq![0nat, 1nat, 2nat],
        grouped: true,
    }
}

/// `$3` as a day number.
pub open spec fn lo_of(ps: Seq<Literal>) -> int {
    match ps[2] {
        Literal::Date { y, m, d } => date_from_civil(y, m, d),
        _ => 0,
    }
}

/// The value of `$3 + 1 year` from `$3`'s day number.
pub open spec fn hi_value(lo: int) -> Result<int, SqlError> {
    match date_to_ts(lo) {
        Err(e) => Err(e),
        Ok(t) => ts_add_interval(t, 12, 0, 0),
    }
}

/// `hi` is the last day before the timestamp `$3 + 1 year`.
pub open spec fn hi_ok(lo: int, hi: int) -> bool {
    &&& hi_value(lo) is Ok
    &&& hi == (hi_value(lo)->Ok_0 - 1) / usecs_per_day()
}

/// The parameters as values, with window end `hi`.
pub open spec fn prm_of(ps: Seq<Literal>, hi: int) -> Prm {
    Prm {
        p0: match ps[0] { Literal::Text(b) => b, _ => Seq::empty() },
        p1: match ps[1] { Literal::Text(b) => b, _ => Seq::empty() },
        lo: lo_of(ps),
        hi,
    }
}

/// The stored lineitem relation of `db`.
pub open spec fn lrel_of(db: Database) -> Seq<Row> {
    stored_relations(db)[0]
}

/// The stored orders relation of `db`.
pub open spec fn orel_of(db: Database) -> Seq<Row> {
    stored_relations(db)[1]
}

/// The joined stored rows: the product of the stored orders and lineitem relations.
pub open spec fn xs_of(db: Database) -> Seq<Row> {
    product_rows(orel_of(db), lrel_of(db))
}

/// The stored columns of the full joined rows (orders 9 columns, then lineitem).
pub open spec fn q12_cols() -> Seq<nat> {
    stored_cols_t1() + shift(stored_cols_t0(), 9)
}

/// The full joined rows of the FROM product.
pub open spec fn full_rows(db: Database) -> Seq<Row> {
    product_rows(db.tables[1], db.tables[0])
}

/// The database facts every lemma here uses.
pub open spec fn db_ok(db: Database) -> bool {
    db.schema == schema_spec() && db_wf(db)
}

// ------------------------------------------------------------------------------------------------ typing

/// An orders table row of the statement's shape.
pub open spec fn orow_typed(o: Row) -> bool {
    &&& o.len() == 9
    &&& o[0] is Int
    &&& o[5] is Text
}

/// A lineitem table row of the statement's shape.
pub open spec fn lrow_typed(l: Row) -> bool {
    &&& l.len() == 16
    &&& l[0] is Int
    &&& l[10] is Date
    &&& l[11] is Date
    &&& l[12] is Date
    &&& l[14] is Text
}

/// Row shapes and value kinds of the two tables.
pub open spec fn rows_typed(db: Database) -> bool {
    &&& db.tables.len() == 8
    &&& forall|i: int| 0 <= i < db.tables[1].len() ==> #[trigger] orow_typed(db.tables[1][i])
    &&& forall|j: int| 0 <= j < db.tables[0].len() ==> #[trigger] lrow_typed(db.tables[0][j])
}

/// `proj_columns` at one position (a named instance of its definition).
pub open spec fn proj_columns_at(ts: TableSchema, cols: Seq<nat>, k: int) -> Column {
    crate::link::source::proj_columns(ts, cols)[k]
}

pub proof fn lemma_rows_typed(db: Database)
    requires db_ok(db),
    ensures rows_typed(db),
{
    lemma_declared_schema();
    let s = schema_spec();
    let (c0, c1) = (stored_cols_t0(), stored_cols_t1());
    assert(c1[0] == 0 && c1[5] == 5);
    assert(c0[0] == 0 && c0[10] == 10 && c0[11] == 11 && c0[12] == 12 && c0[14] == 14);
    assert(proj_columns_at(s[1], c1, 0) == s[1].columns[0]);
    assert(s[1].columns[0] == stored_columns_t1()[0]);
    assert(s[1].columns[5] == stored_columns_t1()[5]);
    assert(s[0].columns[0] == stored_columns_t0()[0]);
    assert(s[0].columns[10] == stored_columns_t0()[10]);
    assert(s[0].columns[11] == stored_columns_t0()[11]);
    assert(s[0].columns[12] == stored_columns_t0()[12]);
    assert(s[0].columns[14] == stored_columns_t0()[14]);
    assert forall|i: int| 0 <= i < db.tables[1].len() implies #[trigger] orow_typed(db.tables[1][i]) by {
        assert(row_in_table(db.tables[1][i], db.schema[1]));
        assert(value_in_column(db.tables[1][i][0], s[1].columns[0]));
        assert(value_in_column(db.tables[1][i][5], s[1].columns[5]));
    }
    assert forall|j: int| 0 <= j < db.tables[0].len() implies #[trigger] lrow_typed(db.tables[0][j]) by {
        assert(row_in_table(db.tables[0][j], db.schema[0]));
        assert(value_in_column(db.tables[0][j][0], s[0].columns[0]));
        assert(value_in_column(db.tables[0][j][10], s[0].columns[10]));
        assert(value_in_column(db.tables[0][j][11], s[0].columns[11]));
        assert(value_in_column(db.tables[0][j][12], s[0].columns[12]));
        assert(value_in_column(db.tables[0][j][14], s[0].columns[14]));
    }
}

/// The orders part of a full joined row.
pub open spec fn opart(r: Row) -> Row {
    r.subrange(0, 9)
}

/// The lineitem part of a full joined row.
pub open spec fn lpart(r: Row) -> Row {
    r.subrange(9, r.len() as int)
}

/// Every full joined row is one typed orders row followed by one typed lineitem row.
pub proof fn lemma_full_typed(db: Database)
    requires rows_typed(db),
    ensures
        forall|k: int| 0 <= k < full_rows(db).len() ==> {
            &&& orow_typed(opart(#[trigger] full_rows(db)[k]))
            &&& lrow_typed(lpart(full_rows(db)[k]))
            &&& full_rows(db)[k] == opart(full_rows(db)[k]) + lpart(full_rows(db)[k])
        },
{
    let (a, b) = (db.tables[1], db.tables[0]);
    lemma_product_rows_elems(a, b);
    assert forall|k: int| 0 <= k < full_rows(db).len() implies {
        &&& orow_typed(opart(#[trigger] full_rows(db)[k]))
        &&& lrow_typed(lpart(full_rows(db)[k]))
        &&& full_rows(db)[k] == opart(full_rows(db)[k]) + lpart(full_rows(db)[k])
    } by {
        let r = full_rows(db)[k];
        assert(is_concat(r, a, b));
        let (i, j) = choose|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && r == #[trigger] a[i] + #[trigger] b[j];
        assert(orow_typed(a[i]) && lrow_typed(b[j]));
        assert(opart(r) =~= a[i]);
        assert(lpart(r) =~= b[j]);
        assert(r =~= opart(r) + lpart(r));
    }
}

/// Positions of a full joined row `o ++ l` in its stored projection.
pub proof fn lemma_proj_positions(o: Row, l: Row)
    requires o.len() == 9, l.len() == 16,
    ensures ({
        let x = proj(o + l, q12_cols());
        &&& x.len() == 22
        &&& x[0] == o[0]
        &&& x[5] == o[5]
        &&& x[7] == l[0]
        &&& x[17] == l[10]
        &&& x[18] == l[11]
        &&& x[19] == l[12]
        &&& x[21] == l[14]
    }),
{
    let cs = q12_cols();
    let (c0, c1) = (stored_cols_t0(), stored_cols_t1());
    assert(c1.len() == 7 && c0.len() == 15);
    assert(cs.len() == 22);
    assert(cs[0] == 0 && cs[5] == 5);
    assert(cs[7] == c0[0] + 9);
    assert(cs[17] == c0[10] + 9);
    assert(cs[18] == c0[11] + 9);
    assert(cs[19] == c0[12] + 9);
    assert(cs[21] == c0[14] + 9);
}

/// The stored projection of the full joined rows is the product of the stored relations.
pub proof fn lemma_xs(db: Database)
    requires db_ok(db),
    ensures proj_all(full_rows(db), q12_cols()) == xs_of(db),
{
    lemma_rows_typed(db);
    lemma_declared_schema();
    let (a, b) = (db.tables[1], db.tables[0]);
    let (ca, cb) = (stored_cols_t1(), stored_cols_t0());
    assert forall|i: int| 0 <= i < a.len() implies (#[trigger] a[i]).len() == 9 by {
        assert(orow_typed(a[i]));
    }
    assert forall|i: int| 0 <= i < b.len() implies (#[trigger] b[i]).len() == 16 by {
        assert(lrow_typed(b[i]));
    }
    assert forall|k: int| 0 <= k < ca.len() implies #[trigger] ca[k] < 9 by {}
    assert forall|k: int| 0 <= k < cb.len() implies #[trigger] cb[k] < 16 by {}
    lemma_proj_product(a, b, ca, cb, 9, 16);
}

// ------------------------------------------------------------------------------------------------ per-row conditions

/// `x * U < t` exactly when `x <= (t - 1) / U` (floor division, `U > 0`).
pub proof fn lemma_lt_floor(x: int, t: int, u: int)
    requires u > 0,
    ensures (x * u < t) == (x <= (t - 1) / u),
{
    let q = (t - 1) / u;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(t - 1, u);
    vstd::arithmetic::div_mod::lemma_mod_bound(t - 1, u);
    if x <= q {
        assert(x * u <= q * u) by (nonlinear_arith) requires x <= q, u > 0;
        assert(u * q == q * u) by (nonlinear_arith);
    } else {
        assert(x * u >= (q + 1) * u) by (nonlinear_arith) requires x >= q + 1, u > 0;
        assert((q + 1) * u == q * u + u) by (nonlinear_arith);
        assert(u * q == q * u) by (nonlinear_arith);
    }
}

/// `$3` is a valid date literal: it evaluates to its day number.
pub proof fn lemma_lit(ps: Seq<Literal>)
    requires param_typed(ps),
    ensures
        ps[2] is Date,
        lit_val(ps[2]) == Ok::<Val, SqlError>(Val::Date(lo_of(ps))),
        date_valid(lo_of(ps)),
{
}

/// `$3 + 1 year` evaluates (in any environment) to `hi_value`.
pub proof fn lemma_hi_expr(db: Database, env: Row, ps: Seq<Literal>)
    requires param_typed(ps),
    ensures
        eval_expr(db, env, hi_expr(ps)) == match hi_value(lo_of(ps)) {
            Ok(t) => Ok::<Val, SqlError>(Val::Ts(t)),
            Err(e) => Err::<Val, SqlError>(e),
        },
{
    lemma_lit(ps);
    let lit = Expr::Lit(ps[2]);
    let cast_e = Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(lit) };
    assert(eval_expr(db, env, lit) == Ok::<Val, SqlError>(Val::Date(lo_of(ps))));
    match date_to_ts(lo_of(ps)) {
        Ok(t) => {
            assert(eval_expr(db, env, cast_e) == Ok::<Val, SqlError>(Val::Ts(t)));
        },
        Err(e) => {
            assert(eval_expr(db, env, cast_e) == Err::<Val, SqlError>(e));
        },
    }
}

/// The conjuncts before the last on a full joined row `o ++ l`.
pub proof fn lemma_head_row(db: Database, o: Row, l: Row, ps: Seq<Literal>)
    requires
        param_domain(ps),
        orow_typed(o),
        lrow_typed(l),
    ensures ({
        let x = proj(o + l, q12_cols());
        let prm = prm_of(ps, 0);
        eval_pred(db, o + l, head_pred(ps)) == Ok::<Truth, SqlError>(truth_of(
            x[0] == x[7]
            && (x[21] == Val::Text(prm.p0) || x[21] == Val::Text(prm.p1))
            && day_of(x[18]) < day_of(x[19])
            && day_of(x[17]) < day_of(x[18])
            && prm.lo <= day_of(x[19])))
    }),
{
    hide(eval_expr);
    hide(eval_pred);
    let r = o + l;
    assert(r.len() == 25);
    assert(r[0] == o[0] && r[5] == o[5] && r[9] == l[0] && r[19] == l[10] && r[20] == l[11] && r[21] == l[12] && r[23] == l[14]);
    lemma_proj_positions(o, l);
    let prm = prm_of(ps, 0);
    let (ko, kl) = (o[0]->Int_0, l[0]->Int_0);
    let (sd, cd, rd) = (l[10]->Date_0, l[11]->Date_0, l[12]->Date_0);
    let m = l[14]->Text_0;
    crate::link::expr::lemma_expr_col(db, r, 0);
    crate::link::expr::lemma_expr_col(db, r, 9);
    crate::link::expr::lemma_expr_col(db, r, 19);
    crate::link::expr::lemma_expr_col(db, r, 20);
    crate::link::expr::lemma_expr_col(db, r, 21);
    crate::link::expr::lemma_expr_col(db, r, 23);
    // o_orderkey = l_orderkey
    crate::link::expr::lemma_compare_int(ko, kl);
    crate::link::expr::lemma_pred_cmp(db, r, CmpOp::Eq, Expr::Col(0), Expr::Col(9), o[0], l[0], ko, kl);
    // l_shipmode IN ($1, $2)
    assert(eval_expr(db, r, Expr::Lit(ps[0])) == Ok::<Val, SqlError>(Val::Text(prm.p0))) by { reveal(eval_expr); }
    assert(eval_expr(db, r, Expr::Lit(ps[1])) == Ok::<Val, SqlError>(Val::Text(prm.p1))) by { reveal(eval_expr); }
    crate::link::expr::lemma_pred_text_cmp(db, r, CmpOp::Eq, Expr::Col(23), Expr::Lit(ps[0]), m, prm.p0);
    crate::link::expr::lemma_pred_text_cmp(db, r, CmpOp::Eq, Expr::Col(23), Expr::Lit(ps[1]), m, prm.p1);
    let e0 = cmp_p(CmpOp::Eq, Expr::Col(23), Expr::Lit(ps[0]));
    let e1 = cmp_p(CmpOp::Eq, Expr::Col(23), Expr::Lit(ps[1]));
    crate::link::expr::lemma_pred_or(db, r, e0, e1, m == prm.p0, m == prm.p1);
    // dates
    crate::link::expr::lemma_compare_date(cd, rd);
    crate::link::expr::lemma_pred_cmp(db, r, CmpOp::Lt, Expr::Col(20), Expr::Col(21), l[11], l[12], cd, rd);
    crate::link::expr::lemma_compare_date(sd, cd);
    crate::link::expr::lemma_pred_cmp(db, r, CmpOp::Lt, Expr::Col(19), Expr::Col(20), l[10], l[11], sd, cd);
    lemma_lit(ps);
    assert(eval_expr(db, r, Expr::Lit(ps[2])) == Ok::<Val, SqlError>(Val::Date(lo_of(ps)))) by { reveal(eval_expr); }
    crate::link::expr::lemma_compare_date(rd, lo_of(ps));
    crate::link::expr::lemma_pred_cmp(db, r, CmpOp::Ge, Expr::Col(21), Expr::Lit(ps[2]), l[12], Val::Date(lo_of(ps)), rd, lo_of(ps));
    // conjunctions
    let a1 = key_pred();
    let a2 = mode_pred(ps);
    crate::link::expr::lemma_pred_and(db, r, a1, a2, ko == kl, m == prm.p0 || m == prm.p1);
    crate::link::expr::lemma_pred_and(db, r, and_p(a1, a2), cr_pred(), ko == kl && (m == prm.p0 || m == prm.p1), cd < rd);
    crate::link::expr::lemma_pred_and(db, r, and_p(and_p(a1, a2), cr_pred()), sc_pred(),
        ko == kl && (m == prm.p0 || m == prm.p1) && cd < rd, sd < cd);
    crate::link::expr::lemma_pred_and(db, r, and_p(and_p(and_p(a1, a2), cr_pred()), sc_pred()), ge_pred(ps),
        ko == kl && (m == prm.p0 || m == prm.p1) && cd < rd && sd < cd, rd >= lo_of(ps));
    assert((ko == kl) == (o[0] == l[0]));
    assert((m == prm.p0) == (l[14] == Val::Text(prm.p0)));
    assert((m == prm.p1) == (l[14] == Val::Text(prm.p1)));
}

/// The WHERE condition on a full joined row is the normal form's qualification of its stored projection.
pub proof fn lemma_where_row(db: Database, o: Row, l: Row, ps: Seq<Literal>, hi: int)
    requires
        param_domain(ps),
        orow_typed(o),
        lrow_typed(l),
        hi_ok(lo_of(ps), hi),
    ensures
        eval_pred(db, o + l, where_pred(ps)) == Ok::<Truth, SqlError>(truth_of(q12_qual(prm_of(ps, hi), proj(o + l, q12_cols())))),
{
    hide(eval_expr);
    hide(eval_pred);
    let r = o + l;
    let x = proj(r, q12_cols());
    assert(r[21] == l[12]);
    lemma_proj_positions(o, l);
    lemma_head_row(db, o, l, ps);
    let rd = l[12]->Date_0;
    let t1 = hi_value(lo_of(ps))->Ok_0;
    let u = usecs_per_day();
    lemma_hi_expr(db, r, ps);
    crate::link::expr::lemma_expr_col(db, r, 21);
    assert(compare(Val::Date(rd), Val::Ts(t1)) == Some(sign(rd * u - t1)));
    crate::link::expr::lemma_pred_cmp(db, r, CmpOp::Lt, Expr::Col(21), hi_expr(ps), l[12], Val::Ts(t1), rd * u, t1);
    lemma_lt_floor(rd, t1, u);
    let prm0 = prm_of(ps, 0);
    let h = x[0] == x[7]
        && (x[21] == Val::Text(prm0.p0) || x[21] == Val::Text(prm0.p1))
        && day_of(x[18]) < day_of(x[19])
        && day_of(x[17]) < day_of(x[18])
        && prm0.lo <= day_of(x[19]);
    crate::link::expr::lemma_pred_and(db, r, head_pred(ps), lt_pred(ps), h, rd * u < t1);
}

/// An error of `$3 + 1 year` is the outcome of the WHERE condition on every full joined row.
pub proof fn lemma_where_row_err(db: Database, o: Row, l: Row, ps: Seq<Literal>)
    requires
        param_domain(ps),
        orow_typed(o),
        lrow_typed(l),
        hi_value(lo_of(ps)) is Err,
    ensures
        eval_pred(db, o + l, where_pred(ps)) == Err::<Truth, SqlError>(hi_value(lo_of(ps))->Err_0),
{
    hide(eval_expr);
    hide(eval_pred);
    let r = o + l;
    let e = hi_value(lo_of(ps))->Err_0;
    assert(r[21] == l[12]);
    lemma_head_row(db, o, l, ps);
    lemma_hi_expr(db, r, ps);
    crate::link::expr::lemma_expr_col(db, r, 21);
    reveal(eval_pred);
    assert(eval_pred(db, r, lt_pred(ps)) == Err::<Truth, SqlError>(e));
    assert(eval_pred(db, r, where_pred(ps)) == Err::<Truth, SqlError>(e));
}

/// `CASE WHEN c THEN 1 ELSE 0 END` of a two-valued condition.
pub proof fn lemma_one_zero(db: Database, env: Row, c: Pred, b: bool)
    requires eval_pred(db, env, c) == Ok::<Truth, SqlError>(truth_of(b)),
    ensures eval_expr(db, env, one_zero(c)) == Ok::<Val, SqlError>(Val::Int(if b { 1 } else { 0 })),
{
    hide(eval_pred);
    hide(eval_expr);
    let one = Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 });
    let zero = Expr::Lit(Literal::Int { v: 0, kind: IntKind::Int4 });
    lemma_expr_int4(db, env, 1);
    lemma_expr_int4(db, env, 0);
    lemma_expr_if(db, env, c, one, zero);
}

/// One unfolding step: an int4 literal in range is its value.
pub proof fn lemma_expr_int4(db: Database, env: Row, v: int)
    requires -2147483648 <= v <= 2147483647,
    ensures eval_expr(db, env, Expr::Lit(Literal::Int { v, kind: IntKind::Int4 })) == Ok::<Val, SqlError>(Val::Int(v)),
{
    assert(int_in_range(IntKind::Int4, v));
}

/// One unfolding step: `CASE WHEN c THEN a ELSE b END`.
pub proof fn lemma_expr_if(db: Database, env: Row, c: Pred, a: Expr, b: Expr)
    ensures
        eval_expr(db, env, Expr::If { cond: Box::new(c), then_e: Box::new(a), else_e: Box::new(b) }) == match eval_pred(db, env, c) {
            Err(err) => Err(err),
            Ok(Truth::True) => eval_expr(db, env, a),
            Ok(_) => eval_expr(db, env, b),
        },
{
}

/// The priority conditions on a full joined row.
pub proof fn lemma_prio_conds(db: Database, o: Row, l: Row)
    requires orow_typed(o), lrow_typed(l),
    ensures
        eval_pred(db, o + l, hi_cond()) == Ok::<Truth, SqlError>(truth_of(prio_high(o[5]))),
        eval_pred(db, o + l, lo_cond()) == Ok::<Truth, SqlError>(truth_of(!prio_high(o[5]))),
{
    hide(eval_expr);
    hide(eval_pred);
    let r = o + l;
    assert(r[5] == o[5]);
    let p = o[5]->Text_0;
    crate::link::expr::lemma_expr_col(db, r, 5);
    crate::link::expr::lemma_expr_text(db, r, urgent());
    crate::link::expr::lemma_expr_text(db, r, high2());
    let eu = Expr::Lit(Literal::Text(urgent()));
    let eh = Expr::Lit(Literal::Text(high2()));
    crate::link::expr::lemma_pred_text_cmp(db, r, CmpOp::Eq, Expr::Col(5), eu, p, urgent());
    crate::link::expr::lemma_pred_text_cmp(db, r, CmpOp::Eq, Expr::Col(5), eh, p, high2());
    crate::link::expr::lemma_pred_text_cmp(db, r, CmpOp::Ne, Expr::Col(5), eu, p, urgent());
    crate::link::expr::lemma_pred_text_cmp(db, r, CmpOp::Ne, Expr::Col(5), eh, p, high2());
    crate::link::expr::lemma_pred_or(db, r, cmp_p(CmpOp::Eq, Expr::Col(5), eu), cmp_p(CmpOp::Eq, Expr::Col(5), eh),
        p == urgent(), p == high2());
    crate::link::expr::lemma_pred_and(db, r, cmp_p(CmpOp::Ne, Expr::Col(5), eu), cmp_p(CmpOp::Ne, Expr::Col(5), eh),
        p != urgent(), p != high2());
    assert((p == urgent()) == (o[5] == Val::Text(urgent())));
    assert((p == high2()) == (o[5] == Val::Text(high2())));
}

/// Argument outcomes of two int4 SUMs whose argument expressions evaluate to integers.
pub proof fn lemma_two_sum_args(db: Database, env: Row, e0: Expr, e1: Expr, v0: int, v1: int)
    requires
        eval_expr(db, env, e0) == Ok::<Val, SqlError>(Val::Int(v0)),
        eval_expr(db, env, e1) == Ok::<Val, SqlError>(Val::Int(v1)),
    ensures
        agg_arg_results(db, env, seq![Agg::Sum { kind: NumKind::Int4, arg: e0 }, Agg::Sum { kind: NumKind::Int4, arg: e1 }])
            == seq![Ok::<Val, SqlError>(Val::Int(v0)), Ok::<Val, SqlError>(Val::Int(v1))],
{
    hide(eval_expr);
    hide(agg_arg);
    let aggs = seq![Agg::Sum { kind: NumKind::Int4, arg: e0 }, Agg::Sum { kind: NumKind::Int4, arg: e1 }];
    lemma_agg_arg_sum(db, env, NumKind::Int4, e0);
    lemma_agg_arg_sum(db, env, NumKind::Int4, e1);
    lemma_agg_arg_results_index(db, env, aggs);
    assert(agg_arg_results(db, env, aggs) =~= seq![Ok::<Val, SqlError>(Val::Int(v0)), Ok::<Val, SqlError>(Val::Int(v1))]);
}

/// The two SUM argument outcomes in an environment where the priority conditions are two-valued: `1/0` by `hb`.
pub proof fn lemma_arg_results_env(db: Database, env: Row, hb: bool)
    requires
        eval_pred(db, env, hi_cond()) == Ok::<Truth, SqlError>(truth_of(hb)),
        eval_pred(db, env, lo_cond()) == Ok::<Truth, SqlError>(truth_of(!hb)),
    ensures
        agg_arg_results(db, env, q12_aggs()) == seq![
            Ok::<Val, SqlError>(Val::Int(if hb { 1int } else { 0int })),
            Ok::<Val, SqlError>(Val::Int(if hb { 0int } else { 1int }))],
{
    hide(eval_expr);
    hide(eval_pred);
    hide(agg_arg_results);
    hide(hi_cond);
    hide(lo_cond);
    lemma_one_zero(db, env, hi_cond(), hb);
    lemma_one_zero(db, env, lo_cond(), !hb);
    lemma_two_sum_args(db, env, one_zero(hi_cond()), one_zero(lo_cond()), if hb { 1int } else { 0int },
        if hb { 0int } else { 1int });
}

/// The two SUM argument outcomes on a full joined row: `1/0` by the order priority.
pub proof fn lemma_arg_results(db: Database, o: Row, l: Row)
    requires orow_typed(o), lrow_typed(l),
    ensures
        agg_arg_results(db, o + l, q12_aggs()) == seq![
            Ok::<Val, SqlError>(Val::Int(if prio_high(o[5]) { 1int } else { 0int })),
            Ok::<Val, SqlError>(Val::Int(if prio_high(o[5]) { 0int } else { 1int }))],
{
    hide(eval_expr);
    hide(eval_pred);
    hide(agg_arg_results);
    lemma_prio_conds(db, o, l);
    lemma_arg_results_env(db, o + l, prio_high(o[5]));
}

/// The normal form's integer arguments of a joined stored row with order priority `v`.
pub proof fn lemma_iargs_row(prm: Prm, x: Row)
    ensures
        iargs(q12_g(prm), x) == seq![
            Val::Int(if prio_high(x[5]) { 1int } else { 0int }),
            Val::Int(if prio_high(x[5]) { 0int } else { 1int })],
{
    let g = q12_g(prm);
    assert(g.aggs.len() == 2);
    assert(iargs(g, x)[0] == Val::Int(q12_arg(0, x)));
    assert(iargs(g, x)[1] == Val::Int(q12_arg(1, x)));
    assert(iargs(g, x) =~= seq![
        Val::Int(if prio_high(x[5]) { 1int } else { 0int }),
        Val::Int(if prio_high(x[5]) { 0int } else { 1int })]);
}

/// The SUM arguments on a full joined row are the normal form's integer arguments.
pub proof fn lemma_args_row(db: Database, o: Row, l: Row, prm: Prm)
    requires orow_typed(o), lrow_typed(l),
    ensures agg_args(db, o + l, q12_aggs()) == Ok::<Row, SqlError>(iargs(q12_g(prm), proj(o + l, q12_cols()))),
{
    hide(eval_expr);
    hide(eval_exprs);
    hide(expr_results);
    hide(eval_pred);
    hide(eval_query);
    hide(agg_arg);
    hide(agg_args);
    hide(agg_arg_results);
    let r = o + l;
    let x = proj(r, q12_cols());
    lemma_proj_positions(o, l);
    lemma_arg_results(db, o, l);
    lemma_iargs_row(prm, x);
    crate::exec::relational::domain::lemma_agg_args(db, r, q12_aggs());
    let rs = agg_arg_results(db, r, q12_aggs());
    let vs = iargs(q12_g(prm), x);
    assert forall|j: int| 0 <= j < rs.len() implies #[trigger] rs[j] == Ok::<Val, SqlError>(vs[j]) by {}
    lemma_collect_all(rs, vs);
}

/// The GROUP BY key on a full joined row.
pub proof fn lemma_key_row(db: Database, o: Row, l: Row, prm: Prm)
    requires orow_typed(o), lrow_typed(l),
    ensures eval_exprs(db, o + l, q12_keys()) == Ok::<Row, SqlError>((q12_g(prm).key)(proj(o + l, q12_cols()))),
{
    let r = o + l;
    lemma_proj_positions(o, l);
    assert(r.len() == 25 && r[23] == l[14]);
    lemma_eval_cols(db, r, seq![23nat]);
    assert(col_exprs(seq![23nat]) =~= q12_keys());
    assert(select(r, seq![23nat]) =~= seq![r[23]]);
    assert((q12_g(prm).key)(proj(r, q12_cols())) =~= seq![r[23]]);
}

// ------------------------------------------------------------------------------------------------ the body

/// The FROM product evaluates to the full joined rows.
pub proof fn lemma_from(db: Database)
    requires db.tables.len() == 8,
    ensures eval_query(db, Seq::empty(), from_q()) == Ok::<Relation, SqlError>(full_rows(db)),
{
    assert(eval_query(db, Seq::empty(), Query::Table(1)) == Ok::<Relation, SqlError>(db.tables[1]));
    assert(eval_query(db, Seq::empty(), Query::Table(0)) == Ok::<Relation, SqlError>(db.tables[0]));
}

/// The WHERE condition, keys and arguments agree with the normal form on every full joined row.
pub proof fn lemma_agree(db: Database, ps: Seq<Literal>, hi: int)
    requires
        db_ok(db),
        param_domain(ps),
        full_rows(db).len() > 0 ==> hi_ok(lo_of(ps), hi),
    ensures ({
        let g = q12_g(prm_of(ps, hi));
        let rows = full_rows(db);
        &&& pred_agrees(db, rows, q12_cols(), where_pred(ps), g)
        &&& keys_agree(db, rows, q12_cols(), q12_keys(), g)
        &&& iargs_agree(db, rows, q12_cols(), q12_aggs(), g)
        &&& iaggs_match(q12_aggs(), g)
    }),
{
    hide(eval_pred);
    hide(eval_exprs);
    hide(agg_args);
    let prm = prm_of(ps, hi);
    let g = q12_g(prm);
    let rows = full_rows(db);
    let cols = q12_cols();
    lemma_rows_typed(db);
    lemma_full_typed(db);
    assert forall|i: int| 0 <= i < rows.len() implies
        eval_pred(db, #[trigger] rows[i], where_pred(ps)) == Ok::<Truth, SqlError>(truth_of((g.qual)(proj(rows[i], cols)))) by {
        let (o, l) = (opart(rows[i]), lpart(rows[i]));
        lemma_where_row(db, o, l, ps, hi);
    }
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], cols)) implies
        eval_exprs(db, rows[i], q12_keys()) == Ok::<Row, SqlError>((g.key)(proj(rows[i], cols))) by {
        let (o, l) = (opart(rows[i]), lpart(rows[i]));
        lemma_key_row(db, o, l, prm);
    }
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], cols)) implies
        agg_args(db, rows[i], q12_aggs()) == Ok::<Row, SqlError>(iargs(g, proj(rows[i], cols))) by {
        let (o, l) = (opart(rows[i]), lpart(rows[i]));
        lemma_args_row(db, o, l, prm);
    }
    let aggs = q12_aggs();
    assert forall|j: int| 0 <= j < aggs.len() implies (#[trigger] aggs[j]) is Sum && aggs[j]->Sum_kind == NumKind::Int4 by {}
}

/// The GROUP BY keys (l_shipmode, a text) are exact: not distinct means equal.
pub proof fn lemma_keys_exact(db: Database, prm: Prm)
    requires db_ok(db),
    ensures keys_exact(q12_g(prm), xs_of(db)),
{
    let g = q12_g(prm);
    lemma_xs(db);
    lemma_rows_typed(db);
    lemma_full_typed(db);
    let rows = full_rows(db);
    let xs = xs_of(db);
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        let (oa, la) = (opart(rows[a]), lpart(rows[a]));
        let (ob, lb) = (opart(rows[b]), lpart(rows[b]));
        lemma_proj_positions(oa, la);
        lemma_proj_positions(ob, lb);
        assert(xs[a] == proj(rows[a], q12_cols()));
        assert(xs[b] == proj(rows[b], q12_cols()));
        let (ka, kb) = ((g.key)(xs[a]), (g.key)(xs[b]));
        assert(same_exact_type(ka[0], kb[0]));
        lemma_row_exact(ka, kb);
    }
}

/// The filter evaluates to the qualifying full joined rows.
pub proof fn lemma_filter(db: Database, ps: Seq<Literal>, hi: int)
    requires
        db_ok(db),
        param_domain(ps),
        full_rows(db).len() > 0 ==> hi_ok(lo_of(ps), hi),
    ensures ({
        let g = q12_g(prm_of(ps, hi));
        let rows = full_rows(db);
        eval_query(db, Seq::empty(), filter_q(ps))
            == Ok::<Relation, SqlError>(keep_true(rows, qual_truths(g, proj_all(rows, q12_cols()))))
    }),
{
    hide(eval_pred);
    lemma_rows_typed(db);
    lemma_from(db);
    lemma_agree(db, ps, hi);
    lemma_filter_rows(db, from_q(), full_rows(db), q12_cols(), where_pred(ps), q12_g(prm_of(ps, hi)));
}

/// The body evaluates to the normal form's rows (`key ++ sums` per group) when every group sum fits int8.
pub proof fn lemma_body(db: Database, ps: Seq<Literal>, hi: int)
    requires
        db_ok(db),
        param_domain(ps),
        full_rows(db).len() > 0 ==> hi_ok(lo_of(ps), hi),
        isum_caps(q12_g(prm_of(ps, hi)), xs_of(db)),
    ensures ({
        let g = q12_g(prm_of(ps, hi));
        denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(gkeys(g, xs_of(db)).map_values(|k: Row| ifull_row(g, xs_of(db), k)))
    }),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_exprs);
    hide(agg_args);
    let g = q12_g(prm_of(ps, hi));
    lemma_statement(ps);
    lemma_filter(db, ps, hi);
    lemma_agree(db, ps, hi);
    lemma_xs(db);
    lemma_keys_exact(db, prm_of(ps, hi));
    lemma_igroup_query(db, full_rows(db), q12_cols(), filter_q(ps), q12_keys(), q12_aggs(), g);
}

/// A non-empty group whose sum leaves int8 makes the statement's outcome error 22003.
pub proof fn lemma_body_sum_err(db: Database, ps: Seq<Literal>, hi: int, k0: Row, j0: int)
    requires
        db_ok(db),
        param_domain(ps),
        full_rows(db).len() > 0 ==> hi_ok(lo_of(ps), hi),
        gcount(q12_g(prm_of(ps, hi)), xs_of(db), k0) > 0,
        0 <= j0 < 2,
        !int_in_range(IntKind::Int8, gsum(q12_g(prm_of(ps, hi)), xs_of(db), k0, j0)),
    ensures
        denote_body(db, query_spec_at(ps)) == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_exprs);
    hide(agg_args);
    let g = q12_g(prm_of(ps, hi));
    lemma_statement(ps);
    lemma_filter(db, ps, hi);
    lemma_agree(db, ps, hi);
    lemma_xs(db);
    lemma_keys_exact(db, prm_of(ps, hi));
    lemma_igroup_err(db, full_rows(db), q12_cols(), filter_q(ps), q12_keys(), q12_aggs(), g, k0, j0);
}

/// One unfolding step: a GROUP BY over a failing input fails with the input's error.
pub proof fn lemma_groupby_err_input(db: Database, keys: Seq<Expr>, aggs: Seq<Agg>, input: Query, e: SqlError)
    requires eval_query(db, Seq::empty(), input) == Err::<Relation, SqlError>(e),
    ensures eval_query(db, Seq::empty(), Query::GroupBy { keys, aggs, input: Box::new(input) }) == Err::<Relation, SqlError>(e),
{
}

/// On a non-empty product, an error of `$3 + 1 year` is the statement's error.
pub proof fn lemma_body_date_err(db: Database, ps: Seq<Literal>)
    requires
        db_ok(db),
        param_domain(ps),
        full_rows(db).len() > 0,
        hi_value(lo_of(ps)) is Err,
    ensures
        denote_body(db, query_spec_at(ps)) == Err::<Relation, SqlError>(hi_value(lo_of(ps))->Err_0),
{
    hide(eval_query);
    hide(eval_pred);
    let e = hi_value(lo_of(ps))->Err_0;
    let rows = full_rows(db);
    let ctx = Seq::<Val>::empty();
    lemma_statement(ps);
    lemma_rows_typed(db);
    lemma_full_typed(db);
    lemma_from(db);
    assert forall|k: int| 0 <= k < rows.len() implies #[trigger] eval_pred(db, ctx + rows[k], where_pred(ps)) is Ok
        || eval_pred(db, ctx + rows[k], where_pred(ps)) == Err::<Truth, SqlError>(e) by {
        assert(ctx + rows[k] =~= rows[k]);
        let (o, l) = (opart(rows[k]), lpart(rows[k]));
        lemma_where_row_err(db, o, l, ps);
    }
    assert(ctx + rows[0] =~= rows[0]);
    let (o, l) = (opart(rows[0]), lpart(rows[0]));
    lemma_where_row_err(db, o, l, ps);
    crate::link::capacity::lemma_filter_err(db, ctx, where_pred(ps), Box::new(from_q()), rows, e, 0);
    lemma_groupby_err_input(db, q12_keys(), q12_aggs(), filter_q(ps), e);
}

/// On an empty product the body has no rows.
pub proof fn lemma_body_empty(db: Database, ps: Seq<Literal>)
    requires
        db_ok(db),
        param_domain(ps),
        full_rows(db).len() == 0,
    ensures
        denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(Seq::<Row>::empty()),
{
    let g = q12_g(prm_of(ps, 0));
    lemma_xs(db);
    assert(xs_of(db).len() == 0);
    assert(gkeys(g, xs_of(db)) =~= Seq::<Row>::empty());
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() implies int_in_range(IntKind::Int8, #[trigger] gsum(g, xs_of(db), k, j)) by {}
    lemma_body(db, ps, 0);
    assert(gkeys(g, xs_of(db)).map_values(|k: Row| ifull_row(g, xs_of(db), k)) =~= Seq::<Row>::empty());
}

// ------------------------------------------------------------------------------------------------ the answer

/// The output row of group `k = [v]`: `[v, high sum, low sum]`.
pub open spec fn group_row(g: QuerySpec, xs: Seq<Row>, k: Row) -> Row {
    seq![k[0], Val::Int(gsum(g, xs, k, 0)), Val::Int(gsum(g, xs, k, 1))]
}

/// A table of exact group rows, one per non-empty group, sorted by the ORDER BY key, is an allowed output.
pub proof fn lemma_answer(db: Database, ps: Seq<Literal>, hi: int, ks: Seq<Row>, out: Seq<Row>)
    requires
        denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(
            gkeys(q12_g(prm_of(ps, hi)), xs_of(db)).map_values(|k: Row| ifull_row(q12_g(prm_of(ps, hi)), xs_of(db), k))),
        ks.no_duplicates(),
        forall|k: Row| #[trigger] ks.contains(k) <==> gcount(q12_g(prm_of(ps, hi)), xs_of(db), k) > 0,
        forall|i: int| 0 <= i < ks.len() ==> (#[trigger] ks[i]).len() == 1,
        out.len() == ks.len(),
        forall|i: int| 0 <= i < out.len() ==> #[trigger] out[i] == group_row(q12_g(prm_of(ps, hi)), xs_of(db), ks[i]),
        sorted_by(order_keys(), out),
    ensures
        ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    let g = q12_g(prm_of(ps, hi));
    let xs = xs_of(db);
    let gk = gkeys(g, xs);
    let full = gk.map_values(|k: Row| ifull_row(g, xs, k));
    lemma_statement(ps);
    lemma_gkeys(g, xs);
    // `ks` and `gkeys` hold the same keys, each once: `out` is a permutation of the body's rows.
    assert forall|k: Row| #[trigger] gk.contains(k) <==> ks.contains(k) by {
        if gk.contains(k) {
            lemma_gkeys_witness(g, xs, k);
            let w = choose|w: int| 0 <= w < xs.len() && #[trigger] hit(g, xs[w], k);
            lemma_count_pos(g, xs, k, w);
        }
        if ks.contains(k) {
            lemma_count_witness(g, xs, k);
        }
    }
    lemma_nodup_same_multiset(gk, ks);
    assert forall|i: int| 0 <= i < out.len() implies #[trigger] out[i] == ifull_row(g, xs, ks[i]) by {
        let k = ks[i];
        assert(isum_outs(g, xs, k) =~= seq![Val::Int(gsum(g, xs, k, 0)), Val::Int(gsum(g, xs, k, 1))]);
        assert(ifull_row(g, xs, k) =~= seq![k[0], Val::Int(gsum(g, xs, k, 0)), Val::Int(gsum(g, xs, k, 1))]);
    }
    assert(out =~= ks.map_values(|k: Row| ifull_row(g, xs, k)));
    lemma_map_multiset(gk, ks, |k: Row| ifull_row(g, xs, k));
    lemma_slice_all(out);
    assert(out.to_multiset() == full.to_multiset() && sorted_by(order_keys(), out) && out == slice_rows(out, 0, None));
}

} // verus!
