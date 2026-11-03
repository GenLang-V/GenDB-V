//! SQL meaning of Q4 in normal form (`link::query::QuerySpec`) over the stored relations of `facts`.
//!
//! The statement's body is `GROUP BY o_orderpriority, COUNT(*)` over `orders WHERE <date window> AND EXISTS (lineitem
//! WHERE l_orderkey = o_orderkey AND l_commitdate < l_receiptdate)`. Over the stored orders relation `orel`
//! (columns o_orderkey, o_custkey, o_orderstatus, o_totalprice, o_orderdate, o_orderpriority, o_shippriority) the
//! normal form `qspec(lrel, lo, hi)` qualifies a row when its date lies in `[lo, hi]` (days; `hi` is the last day
//! before `$1 + 3 months`) and some stored lineitem row `l` has `l[0] == o_orderkey` and `l[11] < l[12]`
//! (`has_line`); its key is `[o_orderpriority]`, its one aggregate COUNT(*).
//!
//! `lemma_body`: the body evaluates to the normal form's rows; `lemma_body_date_err`: an error of `$1 + 3 months` is
//! the statement's error on non-empty orders; `lemma_body_count_err`: a group count beyond int8 is error 22003;
//! `lemma_answer`: a sorted table of exact group rows is an allowed output.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::eval::*;
use crate::spec::numeric::sign;
use crate::spec::datetime::*;
use crate::spec::limits::*;
use crate::spec::relation::*;
use crate::spec::typing::*;
use crate::spec::types::*;
use crate::spec::order::*;
use crate::spec::equality::*;
use crate::link::query::*;
use crate::link::exists::lemma_exists_filter_table;
use crate::link::source::lemma_proj_all_index;
use crate::bridge::collect::*;
use crate::bridge::equality::same_exact_type;
use crate::query::{query_spec_at, param_typed};
use crate::schema::schema_spec;
use crate::stores::facts::declaration::*;

verus! {

// ------------------------------------------------------------------------------------------------ statement pieces

/// `$1 + INTERVAL '3' MONTH` (a timestamp).
pub open spec fn hi_expr(ps: Seq<Literal>) -> Expr {
    Expr::AddInterval {
        arg: Box::new(Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(Expr::Lit(ps[0])) }),
        months: 3i32,
        days: 0i32,
        micros: 0i64,
    }
}

/// `o_orderdate >= $1 AND o_orderdate < $1 + INTERVAL '3' MONTH`.
pub open spec fn date_pred(ps: Seq<Literal>) -> Pred {
    Pred::And(
        Box::new(Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(4), b: Expr::Lit(ps[0]) }),
        Box::new(Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(4), b: hi_expr(ps) }),
    )
}

/// `l_orderkey = o_orderkey AND l_commitdate < l_receiptdate` (orders columns 0..9, then lineitem columns).
pub open spec fn line_pred() -> Pred {
    Pred::And(
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(9), b: Expr::Col(0) }),
        Box::new(Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(20), b: Expr::Col(21) }),
    )
}

/// The EXISTS subquery condition.
pub open spec fn exists_pred() -> Pred {
    Pred::Exists(Box::new(Query::Filter { pred: line_pred(), input: Box::new(Query::Table(0)) }))
}

/// The WHERE condition.
pub open spec fn where_pred(ps: Seq<Literal>) -> Pred {
    Pred::And(Box::new(date_pred(ps)), Box::new(exists_pred()))
}

/// `orders WHERE ..`.
pub open spec fn filter_q(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: where_pred(ps), input: Box::new(Query::Table(1)) }
}

/// The ORDER BY key: o_orderpriority ascending.
pub open spec fn order_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 0, desc: false, nulls_first: false }]
}

/// The statement, piece by piece.
pub proof fn lemma_statement(ps: Seq<Literal>)
    ensures
        query_spec_at(ps).body == (Query::GroupBy { keys: seq![Expr::Col(5)], aggs: seq![Agg::CountStar], input: Box::new(filter_q(ps)) }),
        query_spec_at(ps).keys == order_keys(),
        query_spec_at(ps).offset == 0,
        query_spec_at(ps).limit is None,
{
}

// ------------------------------------------------------------------------------------------------ normal form

/// Lineitem row `l` has order key `k` and `l_commitdate < l_receiptdate`.
pub open spec fn line_hit(l: Row, k: Val) -> bool {
    &&& l[0] == k
    &&& l[11] is Date
    &&& l[12] is Date
    &&& l[11]->Date_0 < l[12]->Date_0
}

/// Some row of `lrel` is a late line of order key `k`.
pub open spec fn has_line(lrel: Seq<Row>, k: Val) -> bool {
    exists|i: int| 0 <= i < lrel.len() && #[trigger] line_hit(lrel[i], k)
}

/// The stored orders row `x` has its date in `[lo, hi]`.
pub open spec fn in_window(x: Row, lo: int, hi: int) -> bool {
    &&& x[4] is Date
    &&& lo <= x[4]->Date_0 <= hi
}

/// Q4 in normal form over the stored orders rows.
pub open spec fn qspec(lrel: Seq<Row>, lo: int, hi: int) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| in_window(x, lo, hi) && has_line(lrel, x[0]),
        key: |x: Row| seq![x[5]],
        arg: |j: int, x: Row| 0int,
        aggs: seq![AggKind::Count],
        outs: seq![0nat, 1nat],
        grouped: true,
    }
}

/// `$1` as a day number.
pub open spec fn lo_of(ps: Seq<Literal>) -> int {
    match ps[0] {
        Literal::Date { y, m, d } => date_from_civil(y, m, d),
        _ => 0,
    }
}

/// The value of `$1 + 3 months` from `$1`'s day number.
pub open spec fn hi_value(lo: int) -> Result<int, SqlError> {
    match date_to_ts(lo) {
        Err(e) => Err(e),
        Ok(t) => ts_add_interval(t, 3, 0, 0),
    }
}

/// `hi` is the last day before the timestamp `$1 + 3 months`.
pub open spec fn hi_ok(lo: int, hi: int) -> bool {
    &&& hi_value(lo) is Ok
    &&& hi == (hi_value(lo)->Ok_0 - 1) / usecs_per_day()
}

/// The stored lineitem relation of `db`.
pub open spec fn lrel_of(db: Database) -> Seq<Row> {
    stored_relations(db)[0]
}

/// The stored orders relation of `db`.
pub open spec fn orel_of(db: Database) -> Seq<Row> {
    stored_relations(db)[1]
}

/// The database facts every lemma here uses.
pub open spec fn db_ok(db: Database) -> bool {
    db.schema == schema_spec() && db_wf(db)
}

// ------------------------------------------------------------------------------------------------ typing

/// Row shapes and value kinds of the two tables.
pub open spec fn rows_typed(db: Database) -> bool {
    &&& db.tables.len() == 8
    &&& forall|i: int| 0 <= i < db.tables[1].len() ==> {
        &&& (#[trigger] db.tables[1][i]).len() == 9
        &&& db.tables[1][i][0] is Int
        &&& db.tables[1][i][4] is Date
        &&& db.tables[1][i][5] is Text
    }
    &&& forall|j: int| 0 <= j < db.tables[0].len() ==> {
        &&& (#[trigger] db.tables[0][j]).len() == 16
        &&& db.tables[0][j][0] is Int
        &&& db.tables[0][j][11] is Date
        &&& db.tables[0][j][12] is Date
    }
}

pub proof fn lemma_rows_typed(db: Database)
    requires db_ok(db),
    ensures rows_typed(db),
{
    lemma_declared_schema();
    let s = schema_spec();
    let (c0, c1) = (stored_cols_t0(), stored_cols_t1());
    assert(c1[0] == 0 && c1[4] == 4 && c1[5] == 5);
    assert(c0[0] == 0 && c0[11] == 11 && c0[12] == 12);
    assert(proj_columns_at(s[1], c1, 0) == s[1].columns[0]);
    assert(s[1].columns[0] == stored_columns_t1()[0]);
    assert(s[1].columns[4] == stored_columns_t1()[4]);
    assert(s[1].columns[5] == stored_columns_t1()[5]);
    assert(s[0].columns[0] == stored_columns_t0()[0]);
    assert(s[0].columns[11] == stored_columns_t0()[11]);
    assert(s[0].columns[12] == stored_columns_t0()[12]);
    assert(s[0].columns.len() == 16);
    assert forall|i: int| 0 <= i < db.tables[1].len() implies {
        &&& (#[trigger] db.tables[1][i]).len() == 9
        &&& db.tables[1][i][0] is Int
        &&& db.tables[1][i][4] is Date
        &&& db.tables[1][i][5] is Text
    } by {
        assert(row_in_table(db.tables[1][i], db.schema[1]));
        assert(value_in_column(db.tables[1][i][0], s[1].columns[0]));
        assert(value_in_column(db.tables[1][i][4], s[1].columns[4]));
        assert(value_in_column(db.tables[1][i][5], s[1].columns[5]));
    }
    assert forall|j: int| 0 <= j < db.tables[0].len() implies {
        &&& (#[trigger] db.tables[0][j]).len() == 16
        &&& db.tables[0][j][0] is Int
        &&& db.tables[0][j][11] is Date
        &&& db.tables[0][j][12] is Date
    } by {
        assert(row_in_table(db.tables[0][j], db.schema[0]));
        assert(value_in_column(db.tables[0][j][0], s[0].columns[0]));
        assert(value_in_column(db.tables[0][j][11], s[0].columns[11]));
        assert(value_in_column(db.tables[0][j][12], s[0].columns[12]));
    }
}

/// `proj_columns` at one position (a named instance of its definition).
pub open spec fn proj_columns_at(ts: TableSchema, cols: Seq<nat>, k: int) -> Column {
    crate::link::source::proj_columns(ts, cols)[k]
}

/// Positions 0, 11 and 12 of a stored lineitem row are those of its table row; positions 0, 4 and 5 of a stored
/// orders row are those of its table row.
pub proof fn lemma_stored_positions(db: Database)
    ensures
        lrel_of(db).len() == db.tables[0].len(),
        orel_of(db).len() == db.tables[1].len(),
        forall|j: int| 0 <= j < db.tables[0].len() ==> {
            &&& (#[trigger] lrel_of(db)[j])[0] == db.tables[0][j][0]
            &&& lrel_of(db)[j][11] == db.tables[0][j][11]
            &&& lrel_of(db)[j][12] == db.tables[0][j][12]
        },
        forall|i: int| 0 <= i < db.tables[1].len() ==> {
            &&& (#[trigger] orel_of(db)[i]) == proj(db.tables[1][i], stored_cols_t1())
            &&& orel_of(db)[i][0] == db.tables[1][i][0]
            &&& orel_of(db)[i][4] == db.tables[1][i][4]
            &&& orel_of(db)[i][5] == db.tables[1][i][5]
        },
{
    lemma_proj_all_index(db.tables[0], stored_cols_t0());
    lemma_proj_all_index(db.tables[1], stored_cols_t1());
    let (c0, c1) = (stored_cols_t0(), stored_cols_t1());
    assert(c1[0] == 0 && c1[4] == 4 && c1[5] == 5);
    assert(c0[0] == 0 && c0[11] == 11 && c0[12] == 12);
    assert(c0.len() == 15 && c1.len() == 7);
}

// ------------------------------------------------------------------------------------------------ per-row conditions

/// `x * U < t` exactly when `x <= (t - 1) / U` (floor division, `U > 0`).
pub proof fn lemma_lt_floor(x: int, t: int, u: int)
    requires u > 0,
    ensures (x * u < t) == (x <= (t - 1) / u),
{
    let q = (t - 1) / u;
    let r = (t - 1) % u;
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

/// `$1` is a valid date literal: it evaluates to its day number.
pub proof fn lemma_lit(ps: Seq<Literal>)
    requires param_typed(ps),
    ensures
        ps[0] is Date,
        lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(lo_of(ps))),
        date_valid(lo_of(ps)),
{
}

/// One unfolding step: a literal evaluates to its value.
pub proof fn lemma_expr_lit(db: Database, env: Row, l: Literal)
    ensures eval_expr(db, env, Expr::Lit(l)) == lit_val(l),
{
}

/// One unfolding step: a cast of an evaluated operand.
pub proof fn lemma_expr_cast(db: Database, env: Row, op: CastOp, a: Expr)
    ensures
        eval_expr(db, env, Expr::Cast { cast: op, arg: Box::new(a) }) == match eval_expr(db, env, a) {
            Err(err) => Err(err),
            Ok(v) => cast(op, v),
        },
{
}

/// One unfolding step: an interval added to an evaluated operand.
pub proof fn lemma_expr_add_interval(db: Database, env: Row, a: Expr, months: i32, days: i32, micros: i64)
    ensures
        eval_expr(db, env, Expr::AddInterval { arg: Box::new(a), months, days, micros }) == match eval_expr(db, env, a) {
            Err(err) => Err(err),
            Ok(v) => add_interval(v, months, days, micros),
        },
{
}

/// One unfolding step: a comparison whose right operand fails.
pub proof fn lemma_cmp_err_right(db: Database, env: Row, op: CmpOp, a: Expr, b: Expr, va: Val, e: SqlError)
    requires
        eval_expr(db, env, a) == Ok::<Val, SqlError>(va),
        eval_expr(db, env, b) == Err::<Val, SqlError>(e),
    ensures eval_pred(db, env, Pred::Cmp { op, a, b }) == Err::<Truth, SqlError>(e),
{
}

/// One unfolding step: a conjunction whose left operand fails.
pub proof fn lemma_and_err_left(db: Database, env: Row, a: Pred, b: Pred, e: SqlError)
    requires eval_pred(db, env, a) == Err::<Truth, SqlError>(e),
    ensures eval_pred(db, env, Pred::And(Box::new(a), Box::new(b))) == Err::<Truth, SqlError>(e),
{
}

/// One unfolding step: a conjunction whose right operand fails after the left one succeeded.
pub proof fn lemma_and_err_right(db: Database, env: Row, a: Pred, b: Pred, t: Truth, e: SqlError)
    requires
        eval_pred(db, env, a) == Ok::<Truth, SqlError>(t),
        eval_pred(db, env, b) == Err::<Truth, SqlError>(e),
    ensures eval_pred(db, env, Pred::And(Box::new(a), Box::new(b))) == Err::<Truth, SqlError>(e),
{
}

/// `$1 + 3 months` evaluates (in any environment) to `hi_value`.
pub proof fn lemma_hi_expr(db: Database, env: Row, ps: Seq<Literal>)
    requires param_typed(ps),
    ensures
        eval_expr(db, env, hi_expr(ps)) == match hi_value(lo_of(ps)) {
            Ok(t) => Ok::<Val, SqlError>(Val::Ts(t)),
            Err(e) => Err::<Val, SqlError>(e),
        },
{
    hide(eval_expr);
    lemma_lit(ps);
    lemma_expr_lit(db, env, ps[0]);
    let lit = Expr::Lit(ps[0]);
    let cast_e = Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(lit) };
    lemma_expr_cast(db, env, CastOp::DateToTimestamp, lit);
    lemma_expr_add_interval(db, env, cast_e, 3i32, 0i32, 0i64);
    match date_to_ts(lo_of(ps)) {
        Ok(t) => {
            assert(eval_expr(db, env, cast_e) == Ok::<Val, SqlError>(Val::Ts(t)));
        },
        Err(e) => {
            assert(eval_expr(db, env, cast_e) == Err::<Val, SqlError>(e));
        },
    }
}

/// The date window on an orders row.
pub proof fn lemma_date_row(db: Database, r: Row, ps: Seq<Literal>, hi: int)
    requires
        param_typed(ps),
        r.len() == 9,
        r[4] is Date,
        hi_ok(lo_of(ps), hi),
    ensures
        eval_pred(db, r, date_pred(ps)) == Ok::<Truth, SqlError>(truth_of(lo_of(ps) <= r[4]->Date_0 <= hi)),
{
    hide(eval_expr);
    hide(eval_pred);
    let x = r[4]->Date_0;
    let lo = lo_of(ps);
    let t1 = hi_value(lo)->Ok_0;
    let u = usecs_per_day();
    lemma_lit(ps);
    lemma_hi_expr(db, r, ps);
    lemma_expr_lit(db, r, ps[0]);
    crate::link::expr::lemma_expr_col(db, r, 4);
    crate::link::expr::lemma_compare_date(x, lo);
    crate::link::expr::lemma_pred_cmp(db, r, CmpOp::Ge, Expr::Col(4), Expr::Lit(ps[0]), Val::Date(x), Val::Date(lo), x, lo);
    assert(compare(Val::Date(x), Val::Ts(t1)) == Some(sign(x * u - t1)));
    crate::link::expr::lemma_pred_cmp(db, r, CmpOp::Lt, Expr::Col(4), hi_expr(ps), Val::Date(x), Val::Ts(t1), x * u, t1);
    lemma_lt_floor(x, t1, u);
    let ge = Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(4), b: Expr::Lit(ps[0]) };
    let lt = Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(4), b: hi_expr(ps) };
    crate::link::expr::lemma_pred_and(db, r, ge, lt, x >= lo, x * u < t1);
}

/// An error of `$1 + 3 months` is the outcome of the WHERE condition on every orders row.
pub proof fn lemma_where_row_err(db: Database, r: Row, ps: Seq<Literal>)
    requires
        param_typed(ps),
        r.len() == 9,
        r[4] is Date,
        hi_value(lo_of(ps)) is Err,
    ensures
        eval_pred(db, r, where_pred(ps)) == Err::<Truth, SqlError>(hi_value(lo_of(ps))->Err_0),
{
    hide(eval_expr);
    hide(eval_pred);
    let e = hi_value(lo_of(ps))->Err_0;
    let x = r[4]->Date_0;
    let lo = lo_of(ps);
    lemma_lit(ps);
    lemma_hi_expr(db, r, ps);
    lemma_expr_lit(db, r, ps[0]);
    crate::link::expr::lemma_expr_col(db, r, 4);
    crate::link::expr::lemma_compare_date(x, lo);
    let ge = Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(4), b: Expr::Lit(ps[0]) };
    let lt = Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(4), b: hi_expr(ps) };
    crate::link::expr::lemma_pred_cmp(db, r, CmpOp::Ge, Expr::Col(4), Expr::Lit(ps[0]), Val::Date(x), Val::Date(lo), x, lo);
    lemma_cmp_err_right(db, r, CmpOp::Lt, Expr::Col(4), hi_expr(ps), r[4], e);
    lemma_and_err_right(db, r, ge, lt, truth_of(crate::link::expr::int_cmp(CmpOp::Ge, x, lo)), e);
    lemma_and_err_left(db, r, date_pred(ps), exists_pred(), e);
}

/// The correlated condition on orders row `r` and lineitem row `l`.
pub proof fn lemma_line_row(db: Database, r: Row, l: Row)
    requires
        r.len() == 9,
        r[0] is Int,
        l.len() == 16,
        l[0] is Int,
        l[11] is Date,
        l[12] is Date,
    ensures
        eval_pred(db, r + l, line_pred()) == Ok::<Truth, SqlError>(truth_of(line_hit(l, r[0]))),
{
    hide(eval_expr);
    hide(eval_pred);
    let env = r + l;
    assert(env[9] == l[0] && env[0] == r[0] && env[20] == l[11] && env[21] == l[12]);
    assert(env.len() == 25);
    let (a, b) = (l[0]->Int_0, r[0]->Int_0);
    let (x, y) = (l[11]->Date_0, l[12]->Date_0);
    crate::link::expr::lemma_expr_col(db, env, 9);
    crate::link::expr::lemma_expr_col(db, env, 0);
    crate::link::expr::lemma_expr_col(db, env, 20);
    crate::link::expr::lemma_expr_col(db, env, 21);
    crate::link::expr::lemma_compare_int(a, b);
    crate::link::expr::lemma_compare_date(x, y);
    crate::link::expr::lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(9), Expr::Col(0), l[0], r[0], a, b);
    crate::link::expr::lemma_pred_cmp(db, env, CmpOp::Lt, Expr::Col(20), Expr::Col(21), l[11], l[12], x, y);
    let eq = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(9), b: Expr::Col(0) };
    let lt = Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(20), b: Expr::Col(21) };
    crate::link::expr::lemma_pred_and(db, env, eq, lt, a == b, x < y);
    assert((a == b) == (l[0] == r[0]));
}

/// The EXISTS condition on orders row `i`: some stored lineitem row is a late line of its order.
pub proof fn lemma_exists_row(db: Database, i: int)
    requires
        rows_typed(db),
        0 <= i < db.tables[1].len(),
    ensures
        eval_pred(db, db.tables[1][i], exists_pred())
            == Ok::<Truth, SqlError>(truth_of(has_line(lrel_of(db), db.tables[1][i][0]))),
{
    hide(eval_pred);
    hide(eval_query);
    lemma_stored_positions(db);
    let r = db.tables[1][i];
    let t0 = db.tables[0];
    let lrel = lrel_of(db);
    assert forall|j: int| 0 <= j < t0.len() implies #[trigger] eval_pred(db, r + t0[j], line_pred()) is Ok by {
        lemma_line_row(db, r, t0[j]);
    }
    lemma_exists_filter_table(db, r, line_pred(), 0);
    let ex_sql = exists|j: int| 0 <= j < t0.len()
        && #[trigger] eval_pred(db, r + t0[j], line_pred()) == Ok::<Truth, SqlError>(Truth::True);
    if ex_sql {
        let j = choose|j: int| 0 <= j < t0.len()
            && #[trigger] eval_pred(db, r + t0[j], line_pred()) == Ok::<Truth, SqlError>(Truth::True);
        lemma_line_row(db, r, t0[j]);
        assert(line_hit(lrel[j], r[0]));
    }
    if has_line(lrel, r[0]) {
        let j = choose|j: int| 0 <= j < lrel.len() && #[trigger] line_hit(lrel[j], r[0]);
        lemma_line_row(db, r, t0[j]);
        assert(eval_pred(db, r + t0[j], line_pred()) == Ok::<Truth, SqlError>(Truth::True));
    }
}

/// The WHERE condition on orders row `i` is the normal form's qualification of its stored row.
pub proof fn lemma_where_row(db: Database, ps: Seq<Literal>, hi: int, i: int)
    requires
        rows_typed(db),
        param_typed(ps),
        hi_ok(lo_of(ps), hi),
        0 <= i < db.tables[1].len(),
    ensures
        eval_pred(db, db.tables[1][i], where_pred(ps)) == Ok::<Truth, SqlError>(truth_of(
            (qspec(lrel_of(db), lo_of(ps), hi).qual)(proj(db.tables[1][i], stored_cols_t1())))),
{
    hide(eval_pred);
    hide(eval_query);
    hide(eval_expr);
    lemma_stored_positions(db);
    let r = db.tables[1][i];
    let x = orel_of(db)[i];
    assert(x == proj(r, stored_cols_t1()));
    lemma_date_row(db, r, ps, hi);
    lemma_exists_row(db, i);
    assert(x[4] == r[4] && x[0] == r[0]);
    crate::link::expr::lemma_pred_and(db, r, date_pred(ps), exists_pred(),
        lo_of(ps) <= r[4]->Date_0 <= hi, has_line(lrel_of(db), r[0]));
}

// ------------------------------------------------------------------------------------------------ the body

/// One unfolding step: a base table evaluates to its rows.
pub proof fn lemma_table(db: Database, t: nat)
    requires t < db.tables.len(),
    ensures eval_query(db, Seq::empty(), Query::Table(t)) == Ok::<Relation, SqlError>(db.tables[t as int]),
{
}

/// The WHERE condition agrees with the normal form on every orders row.
pub proof fn lemma_pred_agrees(db: Database, ps: Seq<Literal>, hi: int)
    requires
        rows_typed(db),
        param_typed(ps),
        db.tables[1].len() > 0 ==> hi_ok(lo_of(ps), hi),
    ensures
        pred_agrees(db, db.tables[1], stored_cols_t1(), where_pred(ps), qspec(lrel_of(db), lo_of(ps), hi)),
{
    hide(eval_pred);
    let g = qspec(lrel_of(db), lo_of(ps), hi);
    let rows = db.tables[1];
    let cols = stored_cols_t1();
    assert forall|i: int| 0 <= i < rows.len() implies
        eval_pred(db, #[trigger] rows[i], where_pred(ps)) == Ok::<Truth, SqlError>(truth_of((g.qual)(proj(rows[i], cols)))) by {
        lemma_where_row(db, ps, hi, i);
    }
}

/// The GROUP BY key and the COUNT(*) argument agree with the normal form on every orders row.
pub proof fn lemma_key_arg_agree(db: Database, lrel: Seq<Row>, lo: int, hi: int)
    requires rows_typed(db),
    ensures
        keys_agree(db, db.tables[1], stored_cols_t1(), seq![Expr::Col(5)], qspec(lrel, lo, hi)),
        args_agree(db, db.tables[1], stored_cols_t1(), seq![Agg::CountStar], qspec(lrel, lo, hi)),
        aggs_match(seq![Agg::CountStar], qspec(lrel, lo, hi)),
{
    hide(eval_expr);
    hide(eval_exprs);
    hide(agg_arg);
    hide(agg_args);
    let g = qspec(lrel, lo, hi);
    let rows = db.tables[1];
    let cols = stored_cols_t1();
    assert(cols[5] == 5);
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], cols)) implies
        eval_exprs(db, rows[i], seq![Expr::Col(5)]) == Ok::<Row, SqlError>((g.key)(proj(rows[i], cols))) by {
        crate::link::query::lemma_eval_cols(db, rows[i], seq![5nat]);
        assert(col_exprs(seq![5nat]) =~= seq![Expr::Col(5)]);
        assert(select(rows[i], seq![5nat]) =~= seq![rows[i][5]]);
        assert(proj(rows[i], cols)[5] == rows[i][5]);
        assert((g.key)(proj(rows[i], cols)) =~= seq![rows[i][5]]);
    }
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], cols)) implies
        agg_args(db, rows[i], seq![Agg::CountStar]) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[i], cols))) by {
        reveal(agg_args);
        let rs = agg_arg_results(db, rows[i], seq![Agg::CountStar]);
        lemma_agg_arg_results_index(db, rows[i], seq![Agg::CountStar]);
        lemma_agg_arg_count(db, rows[i]);
        lemma_collect_all(rs, seq![Val::Null]);
        assert(arg_vals(g, proj(rows[i], cols)) =~= seq![Val::Null]);
    }
    assert(agg_matches(seq![Agg::CountStar][0], g.aggs[0]));
}

/// The GROUP BY keys (o_orderpriority, a text) are exact: not distinct means equal.
pub proof fn lemma_keys_exact(db: Database, lrel: Seq<Row>, lo: int, hi: int)
    requires rows_typed(db),
    ensures
        keys_exact(qspec(lrel, lo, hi), orel_of(db)),
        proj_all(db.tables[1], stored_cols_t1()) == orel_of(db),
{
    let g = qspec(lrel, lo, hi);
    let rows = db.tables[1];
    let cols = stored_cols_t1();
    lemma_stored_positions(db);
    let xs = orel_of(db);
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        assert(xs[a][5] == rows[a][5] && xs[b][5] == rows[b][5]);
        let (ka, kb) = ((g.key)(xs[a]), (g.key)(xs[b]));
        assert(same_exact_type(ka[0], kb[0]));
        lemma_row_exact(ka, kb);
    }
}

/// The filter evaluates to the qualifying orders rows.
pub proof fn lemma_filter(db: Database, ps: Seq<Literal>, hi: int)
    requires
        rows_typed(db),
        param_typed(ps),
        db.tables[1].len() > 0 ==> hi_ok(lo_of(ps), hi),
    ensures ({
        let g = qspec(lrel_of(db), lo_of(ps), hi);
        let rows = db.tables[1];
        eval_query(db, Seq::empty(), filter_q(ps))
            == Ok::<Relation, SqlError>(keep_true(rows, qual_truths(g, proj_all(rows, stored_cols_t1()))))
    }),
{
    hide(eval_query);
    hide(eval_pred);
    let g = qspec(lrel_of(db), lo_of(ps), hi);
    lemma_table(db, 1);
    lemma_pred_agrees(db, ps, hi);
    lemma_filter_rows(db, Query::Table(1), db.tables[1], stored_cols_t1(), where_pred(ps), g);
}

/// The body evaluates to the normal form's rows.
pub proof fn lemma_body(db: Database, ps: Seq<Literal>, hi: int)
    requires
        db_ok(db),
        param_typed(ps),
        db.tables[1].len() > 0 ==> hi_ok(lo_of(ps), hi),
        forall|k: Row| #[trigger] gcount(qspec(lrel_of(db), lo_of(ps), hi), orel_of(db), k) <= int8_max(),
    ensures
        denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(result_rows(qspec(lrel_of(db), lo_of(ps), hi), orel_of(db))),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_expr);
    hide(eval_exprs);
    hide(agg_args);
    let g = qspec(lrel_of(db), lo_of(ps), hi);
    let rows = db.tables[1];
    let cols = stored_cols_t1();
    let xs = orel_of(db);
    lemma_statement(ps);
    lemma_rows_typed(db);
    lemma_filter(db, ps, hi);
    lemma_key_arg_agree(db, lrel_of(db), lo_of(ps), hi);
    lemma_keys_exact(db, lrel_of(db), lo_of(ps), hi);
    assert(group_caps(g, xs)) by {
        assert forall|k: Row, j: int| #![trigger gcount(g, xs, k), g.aggs[j]] 0 <= j < g.aggs.len() && g.aggs[j] is Count implies gcount(g, xs, k) <= int8_max() by {}
    }
    lemma_group_query(db, rows, cols, filter_q(ps), seq![Expr::Col(5)], seq![Agg::CountStar], g);
    // The output row of a group is its full row (key and count: two columns).
    let fulls = gkeys(g, xs).map_values(|k: Row| full_row(g, xs, k));
    let res = result_rows(g, xs);
    assert(fulls.len() == res.len());
    assert forall|m: int| 0 <= m < fulls.len() implies #[trigger] fulls[m] == res[m] by {
        let k = gkeys(g, xs)[m];
        assert(gkeys(g, xs).contains(k));
        lemma_gkeys_witness(g, xs, k);
        let w = choose|w: int| 0 <= w < xs.len() && #[trigger] hit(g, xs[w], k);
        assert(k == seq![xs[w][5]]);
        assert(full_row(g, xs, k).len() == 2);
        lemma_select_identity(full_row(g, xs, k), g.outs);
    }
    assert(fulls =~= res);
}

/// One unfolding step: a GROUP BY over a failing input fails with the input's error.
pub proof fn lemma_groupby_err_input(db: Database, keys: Seq<Expr>, aggs: Seq<Agg>, input: Query, e: SqlError)
    requires eval_query(db, Seq::empty(), input) == Err::<Relation, SqlError>(e),
    ensures eval_query(db, Seq::empty(), Query::GroupBy { keys, aggs, input: Box::new(input) }) == Err::<Relation, SqlError>(e),
{
}

/// On non-empty orders, an error of `$1 + 3 months` is the statement's error.
pub proof fn lemma_body_date_err(db: Database, ps: Seq<Literal>)
    requires
        db_ok(db),
        param_typed(ps),
        db.tables[1].len() > 0,
        hi_value(lo_of(ps)) is Err,
    ensures
        denote_body(db, query_spec_at(ps)) == Err::<Relation, SqlError>(hi_value(lo_of(ps))->Err_0),
{
    hide(eval_query);
    hide(eval_pred);
    let e = hi_value(lo_of(ps))->Err_0;
    let rows = db.tables[1];
    lemma_statement(ps);
    lemma_rows_typed(db);
    lemma_table(db, 1);
    assert forall|k: int| 0 <= k < rows.len() implies #[trigger] eval_pred(db, Seq::<Val>::empty() + rows[k], where_pred(ps)) is Ok
        || eval_pred(db, Seq::<Val>::empty() + rows[k], where_pred(ps)) == Err::<Truth, SqlError>(e) by {
        assert(Seq::<Val>::empty() + rows[k] =~= rows[k]);
        lemma_where_row_err(db, rows[k], ps);
    }
    assert(Seq::<Val>::empty() + rows[0] =~= rows[0]);
    lemma_where_row_err(db, rows[0], ps);
    crate::link::capacity::lemma_filter_err(db, Seq::empty(), where_pred(ps), Box::new(Query::Table(1)), rows, e, 0);
    lemma_groupby_err_input(db, seq![Expr::Col(5)], seq![Agg::CountStar], filter_q(ps), e);
}

/// The body is the GROUP BY of the qualifying rows' (key, COUNT argument) sequence.
pub proof fn lemma_body_groups(db: Database, ps: Seq<Literal>, hi: int)
    requires
        db_ok(db),
        param_typed(ps),
        db.tables[1].len() > 0 ==> hi_ok(lo_of(ps), hi),
    ensures ({
        let g = qspec(lrel_of(db), lo_of(ps), hi);
        let xs = orel_of(db);
        &&& keys_exact(g, xs)
        &&& denote_body(db, query_spec_at(ps)) == group_rows(seq![Agg::CountStar], qkeys(g, xs),
                qrows(g, xs).map_values(|x: Row| arg_vals(g, x)))
    }),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_expr);
    hide(eval_exprs);
    hide(agg_args);
    hide(group_rows);
    let g = qspec(lrel_of(db), lo_of(ps), hi);
    let rows = db.tables[1];
    let cols = stored_cols_t1();
    let keys = seq![Expr::Col(5)];
    let aggs = seq![Agg::CountStar];
    lemma_statement(ps);
    lemma_rows_typed(db);
    lemma_filter(db, ps, hi);
    lemma_key_arg_agree(db, lrel_of(db), lo_of(ps), hi);
    lemma_keys_exact(db, lrel_of(db), lo_of(ps), hi);
    let xs = proj_all(rows, cols);
    let kept = keep_true(rows, qual_truths(g, xs));
    let q = qrows(g, xs);
    lemma_kept_rows(g, rows, cols);
    lemma_prepared(db, rows, kept, cols, keys, aggs, g);
    let prep = Seq::new(kept.len(), |i: int| ((g.key)(proj(kept[i], cols)), arg_vals(g, proj(kept[i], cols))));
    assert(prep.map_values(|p: (Row, Row)| p.0) =~= qkeys(g, xs));
    assert(prep.map_values(|p: (Row, Row)| p.1) =~= q.map_values(|x: Row| arg_vals(g, x)));
    lemma_groupby_unfold(db, filter_q(ps), keys, aggs, kept, prep);
}

/// GROUP BY with COUNT(*): when some group's count is beyond int8, the outcome is error 22003 (every group's COUNT
/// either succeeds or fails with that error, so the first failure is it).
pub proof fn lemma_groups_count_err(g: QuerySpec, xs: Seq<Row>, k0: Row)
    requires
        g.aggs == seq![AggKind::Count],
        keys_exact(g, xs),
        gcount(g, xs, k0) > int8_max(),
    ensures
        group_rows(seq![Agg::CountStar], qkeys(g, xs), qrows(g, xs).map_values(|x: Row| arg_vals(g, x)))
            == Err::<Seq<Row>, SqlError>(SqlError::NumericValueOutOfRange),
{
    let aggs = seq![Agg::CountStar];
    let e = SqlError::NumericValueOutOfRange;
    let ks = qkeys(g, xs);
    let avs = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    let pool = key_pool(g, xs);
    lemma_pool_exact(g, xs);
    assert forall|i: int| 0 <= i < qkeys(g, xs).len() implies pool.contains(#[trigger] qkeys(g, xs)[i]) by {
        assert(pool[i] == qkeys(g, xs)[i]);
    }
    lemma_distinct_gkeys(g, xs, pool);
    let ds = gkeys(g, xs);
    lemma_gkeys(g, xs);
    let grs = Seq::new(ds.len(), |gi: int|
        match agg_row(aggs, group_members(ks, avs, ds[gi])) {
            Ok(a) => Ok(ds[gi] + a),
            Err(err) => Err(err),
        });
    assert forall|gi: int| 0 <= gi < grs.len() implies #[trigger] grs[gi] is Ok || grs[gi] == Err::<Row, SqlError>(e) by {
        let ms = group_members(ks, avs, ds[gi]);
        crate::link::capacity::lemma_count_value(Agg::CountStar, column(ms, 0));
        let vr = Seq::new(aggs.len(), |j: int| agg_value(aggs[j], column(ms, j)));
        assert(vr =~= seq![agg_value(Agg::CountStar, column(ms, 0))]);
        if agg_value(Agg::CountStar, column(ms, 0)) is Ok {
            lemma_collect_all(vr, seq![agg_value(Agg::CountStar, column(ms, 0))->Ok_0]);
        } else {
            lemma_collect_first_err(vr, 0);
        }
    }
    assert(ds.contains(k0));
    let g0 = choose|gi: int| 0 <= gi < ds.len() && ds[gi] == k0;
    assert(grs[g0] == Err::<Row, SqlError>(e)) by {
        assert(pool.contains(k0));
        lemma_group_members(g, xs, k0, pool);
        let ms = group_members(ks, avs, k0);
        lemma_members_col(g, xs, k0, 0);
        crate::link::capacity::lemma_count_value(Agg::CountStar, column(ms, 0));
        let vr = Seq::new(aggs.len(), |j: int| agg_value(aggs[j], column(ms, j)));
        assert(vr =~= seq![agg_value(Agg::CountStar, column(ms, 0))]);
        lemma_collect_first_err(vr, 0);
    }
    crate::link::capacity::lemma_collect_uniform_err(grs, e, g0);
}

/// A group count beyond int8 makes the statement's outcome error 22003.
pub proof fn lemma_body_count_err(db: Database, ps: Seq<Literal>, hi: int, k0: Row)
    requires
        db_ok(db),
        param_typed(ps),
        db.tables[1].len() > 0 ==> hi_ok(lo_of(ps), hi),
        gcount(qspec(lrel_of(db), lo_of(ps), hi), orel_of(db), k0) > int8_max(),
    ensures
        denote_body(db, query_spec_at(ps)) == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange),
{
    lemma_body_groups(db, ps, hi);
    lemma_groups_count_err(qspec(lrel_of(db), lo_of(ps), hi), orel_of(db), k0);
}

// ------------------------------------------------------------------------------------------------ the answer

/// The output row of group `k = [v]`: `[v, COUNT]`.
pub open spec fn group_row(g: QuerySpec, xs: Seq<Row>, k: Row) -> Row {
    seq![k[0], Val::Int(gcount(g, xs, k) as int)]
}

/// A table of exact group rows, one per non-empty group, sorted by the ORDER BY key, is an allowed output.
pub proof fn lemma_answer(db: Database, ps: Seq<Literal>, hi: int, ks: Seq<Row>, out: Seq<Row>)
    requires
        denote_body(db, query_spec_at(ps))
            == Ok::<Relation, SqlError>(result_rows(qspec(lrel_of(db), lo_of(ps), hi), orel_of(db))),
        ks.no_duplicates(),
        forall|k: Row| #[trigger] ks.contains(k) <==> gcount(qspec(lrel_of(db), lo_of(ps), hi), orel_of(db), k) > 0,
        forall|i: int| 0 <= i < ks.len() ==> (#[trigger] ks[i]).len() == 1,
        out.len() == ks.len(),
        forall|i: int| 0 <= i < out.len() ==> #[trigger] out[i] == group_row(qspec(lrel_of(db), lo_of(ps), hi), orel_of(db), ks[i]),
        sorted_by(order_keys(), out),
    ensures
        ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    let g = qspec(lrel_of(db), lo_of(ps), hi);
    let xs = orel_of(db);
    lemma_statement(ps);
    assert forall|i: int| 0 <= i < out.len() implies #[trigger] out[i] == out_row(g, xs, ks[i]) by {
        let k = ks[i];
        assert(agg_outs(g, xs, k) =~= seq![Val::Int(gcount(g, xs, k) as int)]);
        assert(out_row(g, xs, k) =~= seq![k[0], Val::Int(gcount(g, xs, k) as int)]);
    }
    lemma_result_from_keys(g, order_keys(), 0, None, xs, ks, out);
    lemma_slice_all(out);
    lemma_ordered_link(db, query_spec_at(ps), g, xs, out);
}

} // verus!
