//! The statement's body in the accumulator normal form (`lemma_denotation`), and its error (`lemma_body_hi_err`).
//!
//! FROM is the left-deep product `((customer x orders) x lineitem) x nation` of the database tables (`q_rows`); every
//! joined row is `C[a] ++ O[b] ++ L[i] ++ N[n]` (`lemma_joined_witness`), whose sixteen read columns have the stored
//! values (`lemma_joined_values`). On such a row the WHERE condition evaluates without error to `q_qual` of the
//! projection (`lemma_pred_joined`), the group key to `q_key` and the SUM argument to the scale-4 coefficient
//! `q_arg`. The keys have one exact type per position, so SQL "not distinct" is equality on them. Then
//! `link::query::lemma_group_query` (under `group_caps`) and `lemma_project_cols` give `result_rows`. When the window's
//! upper bound `$1 + 3 months` fails, the WHERE fails on every joined row, so a non-empty FROM makes the body that
//! error.
//!
//! Projected row `x` (`q_cols`): `x[0] c_custkey, x[1] c_name, x[2] c_address, x[3] c_nationkey, x[4] c_phone,
//! x[5] c_acctbal, x[6] c_comment, x[7] o_orderkey, x[8] o_custkey, x[9] o_orderdate, x[10] l_orderkey,
//! x[11] l_extendedprice, x[12] l_discount, x[13] l_returnflag, x[14] n_nationkey, x[15] n_name`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::order::*;
use crate::spec::datetime::*;
use crate::spec::equality::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::source_check::date32_val;
use crate::query::{query_spec_at, param_domain};
use crate::link::query::*;
use crate::link::expr::{lemma_expr_col, lemma_compare_int, lemma_compare_date, lemma_pred_cmp, lemma_pred_text_cmp, lemma_pred_and, int_cmp, text_cmp};
use crate::link::capacity::{lemma_filter_err, lemma_first_input};
use crate::bridge::equality::same_exact_type;
use crate::bridge::collect::lemma_collect_all;
use crate::link::join::lemma_product_index;
use crate::link::source::lemma_proj_all_index;
use crate::agent::cols::*;
use crate::agent::normal::*;

verus! {

// ------------------------------------------------------------------------------------------------ the AST

/// `$1::timestamp + interval '3 month'`.
pub open spec fn hi_expr(p: Literal) -> Expr {
    Expr::AddInterval {
        arg: Box::new(Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(Expr::Lit(p)) }),
        months: 3i32,
        days: 0i32,
        micros: 0i64,
    }
}

/// `c_custkey = o_custkey AND l_orderkey = o_orderkey AND o_orderdate >= $1`.
pub open spec fn q_pred_a(p: Literal) -> Pred {
    let n25 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) };
    let n28 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(17), b: Expr::Col(8) };
    let n29 = Pred::And(Box::new(n25), Box::new(n28));
    let n33 = Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(12), b: Expr::Lit(p) };
    Pred::And(Box::new(n29), Box::new(n33))
}

/// `o_orderdate < $1 + INTERVAL '3' MONTH`.
pub open spec fn q_pred_lt(p: Literal) -> Pred { Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(12), b: hi_expr(p) } }

/// `l_returnflag = 'R'`.
pub open spec fn q_pred_r() -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(25), b: Expr::Lit(Literal::Text(seq![82u8])) }
}

/// `c_nationkey = n_nationkey`.
pub open spec fn q_pred_n() -> Pred { Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(3), b: Expr::Col(33) } }

/// The WHERE (left-nested ANDs, as the statement writes them).
pub open spec fn q_pred(p: Literal) -> Pred {
    let n41 = Pred::And(Box::new(q_pred_a(p)), Box::new(q_pred_lt(p)));
    let n46 = Pred::And(Box::new(n41), Box::new(q_pred_r()));
    Pred::And(Box::new(n46), Box::new(q_pred_n()))
}

/// FROM customer, orders, lineitem, nation.
pub open spec fn q_from() -> Query {
    Query::Product {
        left: Box::new(Query::Product {
            left: Box::new(Query::Product { left: Box::new(Query::Table(2)), right: Box::new(Query::Table(1)) }),
            right: Box::new(Query::Table(0)),
        }),
        right: Box::new(Query::Table(6)),
    }
}

/// l_extendedprice * (1 - l_discount).
pub open spec fn q_sum_arg() -> Expr {
    let n18 = Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) };
    let n20 = Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(n18), b: Box::new(Expr::Col(23)) };
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Col(22)), b: Box::new(n20) }
}

/// GROUP BY c_custkey, c_name, c_acctbal, c_phone, n_name, c_address, c_comment.
pub open spec fn q_group_keys() -> Seq<Expr> {
    seq![Expr::Col(0), Expr::Col(1), Expr::Col(5), Expr::Col(4), Expr::Col(34), Expr::Col(2), Expr::Col(7)]
}

pub open spec fn q_aggs() -> Seq<Agg> { seq![Agg::Sum { kind: NumKind::Numeric, arg: q_sum_arg() }] }

pub open spec fn q_filter(p: Literal) -> Query { Query::Filter { pred: q_pred(p), input: Box::new(q_from()) } }

pub open spec fn q_group(p: Literal) -> Query {
    Query::GroupBy { keys: q_group_keys(), aggs: q_aggs(), input: Box::new(q_filter(p)) }
}

/// The SELECT list as positions in `key ++ [revenue]`.
pub open spec fn q_outs() -> Seq<nat> { seq![0nat, 1, 7, 2, 4, 5, 3, 6] }

pub open spec fn q_body(p: Literal) -> Query {
    Query::Project { exprs: col_exprs(q_outs()), input: Box::new(q_group(p)) }
}

/// ORDER BY revenue DESC.
pub open spec fn q_order_keys() -> Seq<OrderKey> { seq![OrderKey { col: 2, desc: true, nulls_first: true }] }

/// The statement is this AST with LIMIT 20.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures query_spec_at(ps) == (OrderedQuery { body: q_body(ps[0]), keys: q_order_keys(), limit: Some(20nat), offset: 0nat }),
{
    assert(col_exprs(q_outs()) =~= seq![Expr::Col(0), Expr::Col(1), Expr::Col(7), Expr::Col(2), Expr::Col(4), Expr::Col(5),
        Expr::Col(3), Expr::Col(6)]);
}

// ------------------------------------------------------------------------------------------------ joined rows

/// FROM's rows: the left-deep product of the database tables.
pub open spec fn q_rows(db: Database) -> Seq<Row> {
    product_rows(product_rows(product_rows(db.tables[2], db.tables[1]), db.tables[0]), db.tables[6])
}

/// Positions of the sixteen read columns in a joined row `C (0..8) ++ O (8..17) ++ L (17..33) ++ N (33..37)`
/// (opaque: its elements are stated once by `lemma_q_cols`).
#[verifier::opaque]
pub open spec fn q_cols() -> Seq<nat> { seq![0nat, 1, 2, 3, 4, 5, 7, 8, 9, 12, 17, 22, 23, 25, 33, 34] }

/// The elements of `q_cols`.
pub proof fn lemma_q_cols()
    ensures
        q_cols().len() == 16,
        q_cols()[0] == 0, q_cols()[1] == 1, q_cols()[2] == 2, q_cols()[3] == 3, q_cols()[4] == 4, q_cols()[5] == 5,
        q_cols()[6] == 7, q_cols()[7] == 8, q_cols()[8] == 9, q_cols()[9] == 12, q_cols()[10] == 17, q_cols()[11] == 22,
        q_cols()[12] == 23, q_cols()[13] == 25, q_cols()[14] == 33, q_cols()[15] == 34,
{
    reveal(q_cols);
}

/// The projected joined rows the normal form ranges over.
pub open spec fn q_xs(db: Database) -> Seq<Row> { proj_all(q_rows(db), q_cols()) }

/// FROM evaluates to the product of the tables.
pub proof fn lemma_eval_from(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures eval_query(db, Seq::empty(), q_from()) == Ok::<Relation, SqlError>(q_rows(db)),
{
    lemma_parts_shape(sv, db);
    let e = Seq::<Val>::empty();
    assert(eval_query(db, e, Query::Table(2)) == Ok::<Relation, SqlError>(db.tables[2]));
    assert(eval_query(db, e, Query::Table(1)) == Ok::<Relation, SqlError>(db.tables[1]));
    assert(eval_query(db, e, Query::Table(0)) == Ok::<Relation, SqlError>(db.tables[0]));
    assert(eval_query(db, e, Query::Table(6)) == Ok::<Relation, SqlError>(db.tables[6]));
    let co = Query::Product { left: Box::new(Query::Table(2)), right: Box::new(Query::Table(1)) };
    assert(eval_query(db, e, co) == Ok::<Relation, SqlError>(product_rows(db.tables[2], db.tables[1])));
    let col = Query::Product { left: Box::new(co), right: Box::new(Query::Table(0)) };
    assert(eval_query(db, e, col) == Ok::<Relation, SqlError>(product_rows(product_rows(db.tables[2], db.tables[1]), db.tables[0])));
}

/// Row `k` of a product is the concatenation of a row of each side.
pub proof fn lemma_product_witness(a: Seq<Row>, b: Seq<Row>, k: int) -> (ij: (int, int))
    requires 0 <= k < product_rows(a, b).len(),
    ensures
        0 <= ij.0 < a.len(), 0 <= ij.1 < b.len(),
        product_rows(a, b)[k] == a[ij.0] + b[ij.1],
{
    lemma_product_index(a, b);
    let nb = b.len() as int;
    assert(nb > 0) by (nonlinear_arith) requires 0 <= k < a.len() * nb, a.len() >= 0;
    let i = k / nb;
    let j = k % nb;
    assert(k == i * nb + j && 0 <= j < nb) by (nonlinear_arith) requires nb > 0, i == k / nb, j == k % nb;
    assert(0 <= i < a.len()) by (nonlinear_arith) requires nb > 0, i == k / nb, 0 <= k < a.len() * nb;
    assert(product_rows(a, b)[i * nb + j] == a[i] + b[j]);
    (i, j)
}

/// Joined row `C[a] ++ O[b] ++ L[i] ++ N[n]` (opaque: its values are stated by `lemma_joined_values`).
#[verifier::opaque]
pub open spec fn joined(db: Database, a: int, b: int, i: int, n: int) -> Row {
    db.tables[2][a] + db.tables[1][b] + db.tables[0][i] + db.tables[6][n]
}

/// Row indices of a joined row: customer, orders, lineitem, nation.
pub struct JRow { pub a: int, pub b: int, pub i: int, pub n: int }

pub open spec fn jrow_ok(sv: StoresView, w: JRow) -> bool {
    0 <= w.a < n_c(sv) && 0 <= w.b < n_o(sv) && 0 <= w.i < n_l(sv) && 0 <= w.n < n_n(sv)
}

/// Every joined row is `joined(db, a, b, i, n)` for some rows of the four tables.
pub proof fn lemma_joined_witness(sv: StoresView, db: Database, k: int) -> (w: JRow)
    requires bound_db(sv, db), 0 <= k < q_rows(db).len(),
    ensures jrow_ok(sv, w), q_rows(db)[k] == joined(db, w.a, w.b, w.i, w.n),
{
    lemma_parts_shape(sv, db);
    let co = product_rows(db.tables[2], db.tables[1]);
    let col = product_rows(co, db.tables[0]);
    let (y, n) = lemma_product_witness(col, db.tables[6], k);
    let (x, i) = lemma_product_witness(co, db.tables[0], y);
    let (a, b) = lemma_product_witness(db.tables[2], db.tables[1], x);
    reveal(joined);
    JRow { a, b, i, n }
}

/// The values a joined row has at the positions the statement reads.
pub open spec fn joined_vals_ok(sv: StoresView, r: Row, w: JRow) -> bool {
    let (a, b, i, n) = (w.a, w.b, w.i, w.n);
    &&& r.len() == 37
    &&& r[0] == Val::Int(ck(sv)[a] as int)
    &&& r[1] == Val::Text(text_at(cname_col(sv), a))
    &&& r[2] == Val::Text(text_at(caddr_col(sv), a))
    &&& r[3] == Val::Int(cnk(sv)[a] as int)
    &&& r[4] == Val::Text(text_at(cphone_col(sv), a))
    &&& r[5] == (Val::Num { coeff: cacct(sv)[a] as int, scale: 2 })
    &&& r[7] == Val::Text(text_at(ccomm_col(sv), a))
    &&& r[8] == Val::Int(ok(sv)[b] as int)
    &&& r[9] == Val::Int(oc(sv)[b] as int)
    &&& r[12] == date32_val(od(sv)[b])
    &&& r[17] == Val::Int(lk(sv)[i] as int)
    &&& r[22] == (Val::Num { coeff: lp(sv)[i] as int, scale: 2 })
    &&& r[23] == (Val::Num { coeff: ld(sv)[i] as int, scale: 2 })
    &&& r[25] == Val::Text(rf(sv, i))
    &&& r[33] == Val::Int(nk(sv)[n] as int)
    &&& r[34] == Val::Text(text_at(nname_col(sv), n))
    &&& num15(lp(sv)[i]) && num15(ld(sv)[i])
}

pub proof fn lemma_joined_values(sv: StoresView, db: Database, w: JRow)
    requires bound_db(sv, db), jrow_ok(sv, w),
    ensures joined_vals_ok(sv, joined(db, w.a, w.b, w.i, w.n), w),
{
    let (a, b, i, n) = (w.a, w.b, w.i, w.n);
    reveal(joined);
    lemma_parts_shape(sv, db);
    lemma_customer_row(sv, db, a);
    lemma_orders_row(sv, db, b);
    lemma_lineitem_row(sv, db, i);
    lemma_nation_row(sv, db, n);
    let c = db.tables[2][a];
    let o = db.tables[1][b];
    let l = db.tables[0][i];
    let t = db.tables[6][n];
    let co = c + o;
    let col = co + l;
    let r = col + t;
    assert(co[0] == c[0] && co[1] == c[1] && co[2] == c[2] && co[3] == c[3] && co[4] == c[4] && co[5] == c[5] && co[7] == c[7]);
    assert(co[8] == o[0] && co[9] == o[1] && co[12] == o[4]);
    assert(col[0] == co[0] && col[1] == co[1] && col[2] == co[2] && col[3] == co[3] && col[4] == co[4] && col[5] == co[5]);
    assert(col[7] == co[7] && col[8] == co[8] && col[9] == co[9] && col[12] == co[12]);
    assert(col[17] == l[0] && col[22] == l[5] && col[23] == l[6] && col[25] == l[8]);
    assert(r[0] == col[0] && r[1] == col[1] && r[2] == col[2] && r[3] == col[3] && r[4] == col[4] && r[5] == col[5]);
    assert(r[7] == col[7] && r[8] == col[8] && r[9] == col[9] && r[12] == col[12]);
    assert(r[17] == col[17] && r[22] == col[22] && r[23] == col[23] && r[25] == col[25]);
    assert(r[33] == t[0] && r[34] == t[1]);
}

/// The projection of a joined row onto the read columns.
pub proof fn lemma_joined_proj(r: Row)
    requires r.len() == 37,
    ensures proj(r, q_cols()) == seq![r[0], r[1], r[2], r[3], r[4], r[5], r[7], r[8], r[9], r[12], r[17], r[22], r[23],
        r[25], r[33], r[34]],
{
    lemma_q_cols();
    assert(proj(r, q_cols()) =~= seq![r[0], r[1], r[2], r[3], r[4], r[5], r[7], r[8], r[9], r[12], r[17], r[22], r[23],
        r[25], r[33], r[34]]);
}

// ------------------------------------------------------------------------------------------------ the normal form

pub open spec fn date_ge(v: Val, p: int) -> bool { match v { Val::Date(d) => d >= p, _ => false } }

pub open spec fn date_lt_ts(v: Val, t1: int) -> bool { match v { Val::Date(d) => d * usecs() < t1, _ => false } }

pub open spec fn coeff_of(v: Val) -> int { match v { Val::Num { coeff, .. } => coeff, _ => 0 } }

/// WHERE on a projected row `x` (two-valued: every operand is a non-NULL value of its column's type).
pub open spec fn q_qual(pd: int, t1: int, x: Row) -> bool {
    &&& x[0] == x[8]
    &&& x[10] == x[7]
    &&& date_ge(x[9], pd)
    &&& date_lt_ts(x[9], t1)
    &&& x[13] == Val::Text(seq![82u8])
    &&& x[3] == x[14]
}

/// GROUP BY c_custkey, c_name, c_acctbal, c_phone, n_name, c_address, c_comment.
pub open spec fn q_key(x: Row) -> Row { seq![x[0], x[1], x[5], x[4], x[15], x[2], x[6]] }

/// Coefficient (scale 4) of `l_extendedprice * (1 - l_discount)`.
pub open spec fn q_arg(x: Row) -> int { coeff_of(x[11]) * (100 - coeff_of(x[12])) }

/// The statement's normal form at parameter day `pd` and window bound `t1`: one SUM at scale 4; output
/// `c_custkey, c_name, revenue, c_acctbal, n_name, c_address, c_phone, c_comment` = positions `q_outs()` of
/// `key ++ [sum]`.
pub open spec fn q_spec(pd: int, t1: int) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| q_qual(pd, t1, x),
        key: |x: Row| q_key(x),
        arg: |j: int, x: Row| q_arg(x),
        aggs: seq![AggKind::Sum { scale: 4 }],
        outs: q_outs(),
        grouped: true,
    }
}

/// The joined row `w` qualifies: customer and order match, the lineitem is the order's and has flag `R`, the order
/// lies in the window and the nation is the customer's.
pub open spec fn jqual(sv: StoresView, dlo: int, dhi: int, w: JRow) -> bool {
    &&& ck(sv)[w.a] == oc(sv)[w.b]
    &&& lk(sv)[w.i] == ok(sv)[w.b]
    &&& win(sv, dlo, dhi, w.b)
    &&& is_r(sv, w.i)
    &&& cnk(sv)[w.a] == nk(sv)[w.n]
}

/// The key of a joined row: the customer's columns and the nation's name.
pub open spec fn jkey(sv: StoresView, w: JRow) -> Row {
    seq![
        Val::Int(ck(sv)[w.a] as int),
        Val::Text(text_at(cname_col(sv), w.a)),
        Val::Num { coeff: cacct(sv)[w.a] as int, scale: 2 },
        Val::Text(text_at(cphone_col(sv), w.a)),
        Val::Text(text_at(nname_col(sv), w.n)),
        Val::Text(text_at(caddr_col(sv), w.a)),
        Val::Text(text_at(ccomm_col(sv), w.a)),
    ]
}

/// The normal form on a joined row of the database: qualification, key and argument.
pub proof fn lemma_joined_normal_form(sv: StoresView, db: Database, pd: int, t1: int, dlo: int, dhi: int, w: JRow)
    requires bound_db(sv, db), jrow_ok(sv, w), win_of(dlo, dhi, pd, t1),
    ensures ({
        let x = proj(joined(db, w.a, w.b, w.i, w.n), q_cols());
        let g = q_spec(pd, t1);
        &&& (g.qual)(x) == jqual(sv, dlo, dhi, w)
        &&& (g.key)(x) == jkey(sv, w)
        &&& (g.arg)(0, x) == lval(sv, w.i)
    }),
{
    let r = joined(db, w.a, w.b, w.i, w.n);
    lemma_joined_values(sv, db, w);
    lemma_joined_proj(r);
    let x = proj(r, q_cols());
    let d = od(sv)[w.b] as int - 10957;
    assert(x[9] == Val::Date(d));
    lemma_win_hi(dlo, dhi, pd, t1, d);
    assert(date_ge(x[9], pd) == (dlo <= od(sv)[w.b] as int));
    assert(date_lt_ts(x[9], t1) == ((od(sv)[w.b] as int) < dhi));
    assert(q_key(x) =~= jkey(sv, w));
}

// ------------------------------------------------------------------------------------------------ per-row evaluation

pub proof fn lemma_lit_one()
    ensures lit_val(Literal::Int { v: 1, kind: IntKind::Int4 }) == Ok::<Val, SqlError>(Val::Int(1)),
{
}

pub proof fn lemma_eval_lit(db: Database, r: Row, l: Literal)
    ensures eval_expr(db, r, Expr::Lit(l)) == lit_val(l),
{
}

pub proof fn lemma_eval_cast(db: Database, r: Row, arg: Expr, x: int)
    requires eval_expr(db, r, arg) == Ok::<Val, SqlError>(Val::Int(x)),
    ensures eval_expr(db, r, Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(arg) }) == Ok::<Val, SqlError>(Val::Num { coeff: x, scale: 0 }),
{
}

/// `1::numeric`.
pub proof fn lemma_eval_cast_one(db: Database, r: Row)
    ensures eval_expr(db, r, Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) })
        == Ok::<Val, SqlError>(Val::Num { coeff: 1, scale: 0 }),
{
    lemma_lit_one();
    lemma_eval_lit(db, r, Literal::Int { v: 1, kind: IntKind::Int4 });
    lemma_eval_cast(db, r, Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 }), 1);
}

/// The upper bound expression evaluates to `hi_res` (independent of the row).
pub proof fn lemma_hi_expr(db: Database, env: Row, p: Literal, pd: int)
    requires lit_val(p) == Ok::<Val, SqlError>(Val::Date(pd)),
    ensures
        eval_expr(db, env, hi_expr(p)) == match hi_res(pd) {
            Ok(t1) => Ok::<Val, SqlError>(Val::Ts(t1)),
            Err(e) => Err::<Val, SqlError>(e),
        },
{
    let c = Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(Expr::Lit(p)) };
    assert(eval_expr(db, env, Expr::Lit(p)) == Ok::<Val, SqlError>(Val::Date(pd)));
    match date_to_ts(pd) {
        Ok(t) => {
            assert(eval_expr(db, env, c) == Ok::<Val, SqlError>(Val::Ts(t)));
        },
        Err(e) => {
            assert(eval_expr(db, env, c) == Err::<Val, SqlError>(e));
        },
    }
}

/// The literal value of `$1`.
pub proof fn lemma_param_value(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(pd_of(ps))),
{
}

/// The first three conjuncts on a joined row.
proof fn lemma_pred_a_joined(sv: StoresView, db: Database, ps: Seq<Literal>, r: Row, w: JRow)
    requires param_domain(ps), joined_vals_ok(sv, r, w),
    ensures eval_pred(db, r, q_pred_a(ps[0])) == Ok::<Truth, SqlError>(truth_of(
        ck(sv)[w.a] == oc(sv)[w.b] && lk(sv)[w.i] == ok(sv)[w.b] && od(sv)[w.b] as int - 10957 >= pd_of(ps))),
{
    let p = ps[0];
    let pd = pd_of(ps);
    lemma_param_value(ps);
    lemma_expr_col(db, r, 0);
    lemma_expr_col(db, r, 9);
    lemma_expr_col(db, r, 17);
    lemma_expr_col(db, r, 8);
    lemma_expr_col(db, r, 12);
    let (x0, x9, x17, x8) = (ck(sv)[w.a] as int, oc(sv)[w.b] as int, lk(sv)[w.i] as int, ok(sv)[w.b] as int);
    let d = od(sv)[w.b] as int - 10957;
    lemma_compare_int(x0, x9);
    lemma_compare_int(x17, x8);
    lemma_compare_date(d, pd);
    let n25 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) };
    let n28 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(17), b: Expr::Col(8) };
    let n33 = Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(12), b: Expr::Lit(p) };
    lemma_pred_cmp(db, r, CmpOp::Eq, Expr::Col(0), Expr::Col(9), Val::Int(x0), Val::Int(x9), x0, x9);
    lemma_pred_cmp(db, r, CmpOp::Eq, Expr::Col(17), Expr::Col(8), Val::Int(x17), Val::Int(x8), x17, x8);
    lemma_pred_cmp(db, r, CmpOp::Ge, Expr::Col(12), Expr::Lit(p), Val::Date(d), Val::Date(pd), d, pd);
    lemma_pred_and(db, r, n25, n28, x0 == x9, x17 == x8);
    let n29 = Pred::And(Box::new(n25), Box::new(n28));
    lemma_pred_and(db, r, n29, n33, x0 == x9 && x17 == x8, d >= pd);
}

/// The WHERE condition on a joined row, inside the timestamp range.
pub proof fn lemma_pred_joined(sv: StoresView, db: Database, ps: Seq<Literal>, t1: int, r: Row, w: JRow)
    requires param_domain(ps), joined_vals_ok(sv, r, w), hi_res(pd_of(ps)) == Ok::<int, SqlError>(t1),
    ensures eval_pred(db, r, q_pred(ps[0])) == Ok::<Truth, SqlError>(truth_of(
        ck(sv)[w.a] == oc(sv)[w.b] && lk(sv)[w.i] == ok(sv)[w.b] && od(sv)[w.b] as int - 10957 >= pd_of(ps)
        && (od(sv)[w.b] as int - 10957) * usecs() < t1 && rf(sv, w.i) == seq![82u8] && cnk(sv)[w.a] == nk(sv)[w.n])),
{
    let p = ps[0];
    let pd = pd_of(ps);
    lemma_param_value(ps);
    lemma_pred_a_joined(sv, db, ps, r, w);
    let d = od(sv)[w.b] as int - 10957;
    let ea = ck(sv)[w.a] == oc(sv)[w.b] && lk(sv)[w.i] == ok(sv)[w.b] && d >= pd;
    // o_orderdate < $1 + 3 months
    lemma_expr_col(db, r, 12);
    lemma_hi_expr(db, r, p, pd);
    assert(compare(Val::Date(d), Val::Ts(t1)) == Some(sign(d * usecs() - t1)));
    lemma_pred_cmp(db, r, CmpOp::Lt, Expr::Col(12), hi_expr(p), Val::Date(d), Val::Ts(t1), d * usecs(), t1);
    lemma_pred_and(db, r, q_pred_a(p), q_pred_lt(p), ea, d * usecs() < t1);
    let n41 = Pred::And(Box::new(q_pred_a(p)), Box::new(q_pred_lt(p)));
    // l_returnflag = 'R'
    lemma_expr_col(db, r, 25);
    crate::link::expr::lemma_expr_text(db, r, seq![82u8]);
    lemma_pred_text_cmp(db, r, CmpOp::Eq, Expr::Col(25), Expr::Lit(Literal::Text(seq![82u8])), rf(sv, w.i), seq![82u8]);
    lemma_pred_and(db, r, n41, q_pred_r(), ea && d * usecs() < t1, rf(sv, w.i) == seq![82u8]);
    let n46 = Pred::And(Box::new(n41), Box::new(q_pred_r()));
    // c_nationkey = n_nationkey
    lemma_expr_col(db, r, 3);
    lemma_expr_col(db, r, 33);
    let (x3, x33) = (cnk(sv)[w.a] as int, nk(sv)[w.n] as int);
    lemma_compare_int(x3, x33);
    lemma_pred_cmp(db, r, CmpOp::Eq, Expr::Col(3), Expr::Col(33), Val::Int(x3), Val::Int(x33), x3, x33);
    lemma_pred_and(db, r, n46, q_pred_n(), ea && d * usecs() < t1 && rf(sv, w.i) == seq![82u8], x3 == x33);
}

/// The WHERE condition on a joined row, when the window's upper bound fails: that error.
pub proof fn lemma_pred_joined_err(sv: StoresView, db: Database, ps: Seq<Literal>, e: SqlError, r: Row, w: JRow)
    requires param_domain(ps), joined_vals_ok(sv, r, w), hi_res(pd_of(ps)) == Err::<int, SqlError>(e),
    ensures eval_pred(db, r, q_pred(ps[0])) == Err::<Truth, SqlError>(e),
{
    let p = ps[0];
    let pd = pd_of(ps);
    lemma_param_value(ps);
    lemma_pred_a_joined(sv, db, ps, r, w);
    lemma_expr_col(db, r, 12);
    lemma_hi_expr(db, r, p, pd);
    assert(eval_pred(db, r, q_pred_lt(p)) == Err::<Truth, SqlError>(e));
    let n41 = Pred::And(Box::new(q_pred_a(p)), Box::new(q_pred_lt(p)));
    assert(eval_pred(db, r, n41) == Err::<Truth, SqlError>(e));
    let n46 = Pred::And(Box::new(n41), Box::new(q_pred_r()));
    assert(eval_pred(db, r, n46) == Err::<Truth, SqlError>(e));
}

/// The group key on a joined row.
pub proof fn lemma_keys_joined(db: Database, r: Row)
    requires r.len() == 37,
    ensures eval_exprs(db, r, q_group_keys()) == Ok::<Row, SqlError>(seq![r[0], r[1], r[5], r[4], r[34], r[2], r[7]]),
{
    let idxs = seq![0nat, 1, 5, 4, 34, 2, 7];
    assert(col_exprs(idxs) =~= q_group_keys());
    lemma_eval_cols(db, r, idxs);
    assert(select(r, idxs) =~= seq![r[0], r[1], r[5], r[4], r[34], r[2], r[7]]);
}

/// The SUM argument on a row with these price and discount coefficients (numeric(15,2)).
pub proof fn lemma_sum_arg_row(db: Database, r: Row, price: int, disc: int)
    requires
        r.len() == 37,
        r[22] == (Val::Num { coeff: price, scale: 2 }),
        r[23] == (Val::Num { coeff: disc, scale: 2 }),
        abs(price) < pow10(15), abs(disc) < pow10(15),
    ensures
        eval_expr(db, r, q_sum_arg()) == Ok::<Val, SqlError>(Val::Num { coeff: price * (100 - disc), scale: 4 }),
        agg_args(db, r, q_aggs()) == Ok::<Row, SqlError>(seq![Val::Num { coeff: price * (100 - disc), scale: 4 }]),
{
    let n18 = Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) };
    lemma_eval_cast_one(db, r);
    lemma_expr_col(db, r, 22);
    lemma_expr_col(db, r, 23);
    assert(pow10(1) == 10 && pow10(2) == 100 && pow10(0) == 1) by (compute);
    assert(crate::spec::limits::numeric_int_digits_max() >= 100) by (compute);
    lemma_node_add(db, r, ArithOp::Sub, n18, Expr::Col(23), 1, 0, 1, disc, 2, 15, 2, 100, 1, 16);
    let n20 = Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(n18), b: Box::new(Expr::Col(23)) };
    assert(1 * 100 - disc * 1 == 100 - disc);
    lemma_node_mul(db, r, Expr::Col(22), n20, price, 2, 15, 100 - disc, 2, 16);
    let rs = agg_arg_results(db, r, q_aggs());
    lemma_agg_arg_results_index(db, r, q_aggs());
    let vs = seq![Val::Num { coeff: price * (100 - disc), scale: 4 }];
    assert(rs[0] == agg_arg(db, r, q_aggs()[0]));
    assert(rs[0] == Ok::<Val, SqlError>(vs[0]));
    lemma_collect_all(rs, vs);
}

// ------------------------------------------------------------------------------------------------ agreement

/// WHERE agrees with the normal form on every joined row.
pub proof fn lemma_pred_agrees(sv: StoresView, db: Database, ps: Seq<Literal>, t1: int, dlo: int, dhi: int)
    requires bound_db(sv, db), param_domain(ps), hi_res(pd_of(ps)) == Ok::<int, SqlError>(t1), win_of(dlo, dhi, pd_of(ps), t1),
    ensures pred_agrees(db, q_rows(db), q_cols(), q_pred(ps[0]), q_spec(pd_of(ps), t1)),
{
    let rows = q_rows(db);
    let g = q_spec(pd_of(ps), t1);
    assert forall|k: int| 0 <= k < rows.len() implies
        eval_pred(db, #[trigger] rows[k], q_pred(ps[0])) == Ok::<Truth, SqlError>(truth_of((g.qual)(proj(rows[k], q_cols())))) by {
        let w = lemma_joined_witness(sv, db, k);
        let r = joined(db, w.a, w.b, w.i, w.n);
        lemma_joined_values(sv, db, w);
        lemma_pred_joined(sv, db, ps, t1, r, w);
        lemma_joined_normal_form(sv, db, pd_of(ps), t1, dlo, dhi, w);
        lemma_win_hi(dlo, dhi, pd_of(ps), t1, od(sv)[w.b] as int - 10957);
    }
}

/// GROUP BY keys agree with the normal form on every joined row.
pub proof fn lemma_keys_agree(sv: StoresView, db: Database, ps: Seq<Literal>, t1: int)
    requires bound_db(sv, db),
    ensures keys_agree(db, q_rows(db), q_cols(), q_group_keys(), q_spec(pd_of(ps), t1)),
{
    let rows = q_rows(db);
    let g = q_spec(pd_of(ps), t1);
    assert forall|k: int| 0 <= k < rows.len() && (g.qual)(proj(#[trigger] rows[k], q_cols())) implies
        eval_exprs(db, rows[k], q_group_keys()) == Ok::<Row, SqlError>((g.key)(proj(rows[k], q_cols()))) by {
        let w = lemma_joined_witness(sv, db, k);
        let r = joined(db, w.a, w.b, w.i, w.n);
        lemma_joined_values(sv, db, w);
        lemma_keys_joined(db, r);
        lemma_joined_proj(r);
        assert(q_key(proj(r, q_cols())) =~= seq![r[0], r[1], r[5], r[4], r[34], r[2], r[7]]);
    }
}

/// The lineitem columns of a joined row (a narrow form of `lemma_joined_values`).
proof fn lemma_joined_li(sv: StoresView, db: Database, w: JRow)
    requires bound_db(sv, db), jrow_ok(sv, w),
    ensures ({
        let r = joined(db, w.a, w.b, w.i, w.n);
        &&& r.len() == 37
        &&& r[22] == (Val::Num { coeff: lp(sv)[w.i] as int, scale: 2 })
        &&& r[23] == (Val::Num { coeff: ld(sv)[w.i] as int, scale: 2 })
        &&& num15(lp(sv)[w.i]) && num15(ld(sv)[w.i])
    }),
{
    lemma_joined_values(sv, db, w);
}

/// The SUM argument on joined row `k`.
proof fn lemma_args_row(sv: StoresView, db: Database, ps: Seq<Literal>, t1: int, k: int)
    requires bound_db(sv, db), 0 <= k < q_rows(db).len(),
    ensures agg_args(db, q_rows(db)[k], q_aggs()) == Ok::<Row, SqlError>(arg_vals(q_spec(pd_of(ps), t1), proj(q_rows(db)[k], q_cols()))),
{
    let g = q_spec(pd_of(ps), t1);
    let w = lemma_joined_witness(sv, db, k);
    let r = joined(db, w.a, w.b, w.i, w.n);
    lemma_joined_li(sv, db, w);
    let (price, disc) = (lp(sv)[w.i] as int, ld(sv)[w.i] as int);
    assert(pow10(15) == 1_000_000_000_000_000) by (compute);
    lemma_sum_arg_row(db, r, price, disc);
    let x = proj(r, q_cols());
    lemma_q_cols();
    assert(x[11] == r[22] && x[12] == r[23]);
    assert(q_arg(x) == price * (100 - disc));
    assert(arg_vals(g, x) =~= seq![Val::Num { coeff: price * (100 - disc), scale: 4 }]);
}

/// The SUM argument agrees with the normal form on every joined row.
pub proof fn lemma_args_agree(sv: StoresView, db: Database, ps: Seq<Literal>, t1: int)
    requires bound_db(sv, db),
    ensures args_agree(db, q_rows(db), q_cols(), q_aggs(), q_spec(pd_of(ps), t1)),
{
    let rows = q_rows(db);
    let g = q_spec(pd_of(ps), t1);
    assert forall|k: int| 0 <= k < rows.len() && (g.qual)(proj(#[trigger] rows[k], q_cols())) implies
        agg_args(db, rows[k], q_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[k], q_cols()))) by {
        lemma_args_row(sv, db, ps, t1, k);
    }
}

/// Every projected joined row's key is `(int, text, numeric scale 2, text, text, text, text)`.
pub proof fn lemma_key_types(sv: StoresView, db: Database, ps: Seq<Literal>, t1: int, m: int)
    requires bound_db(sv, db), 0 <= m < q_xs(db).len(),
    ensures ({
        let k = (q_spec(pd_of(ps), t1).key)(q_xs(db)[m]);
        &&& k.len() == 7
        &&& k[0] is Int && k[1] is Text && k[3] is Text && k[4] is Text && k[5] is Text && k[6] is Text
        &&& k[2] is Num && k[2]->Num_scale == 2
    }),
{
    let rows = q_rows(db);
    lemma_proj_all_index(rows, q_cols());
    let w = lemma_joined_witness(sv, db, m);
    let r = joined(db, w.a, w.b, w.i, w.n);
    lemma_joined_values(sv, db, w);
    lemma_joined_proj(r);
}

/// SQL "not distinct" is equality on the keys of the joined rows.
pub proof fn lemma_keys_exact(sv: StoresView, db: Database, ps: Seq<Literal>, t1: int)
    requires bound_db(sv, db),
    ensures keys_exact(q_spec(pd_of(ps), t1), q_xs(db)),
{
    let g = q_spec(pd_of(ps), t1);
    let xs = q_xs(db);
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        lemma_key_types(sv, db, ps, t1, a);
        lemma_key_types(sv, db, ps, t1, b);
        let (ka, kb) = ((g.key)(xs[a]), (g.key)(xs[b]));
        assert forall|t: int| 0 <= t < ka.len() implies same_exact_type(#[trigger] ka[t], kb[t]) by {
            if t == 0 {} else if t == 1 {} else if t == 2 {} else if t == 3 {} else if t == 4 {} else if t == 5 {} else {}
        }
        lemma_row_exact(ka, kb);
    }
}

// ------------------------------------------------------------------------------------------------ the body

/// The GROUP BY rows: the full row of every group key, in first-occurrence order.
pub open spec fn q_group_rows(pd: int, t1: int, db: Database) -> Seq<Row> {
    gkeys(q_spec(pd, t1), q_xs(db)).map_values(|k: Row| full_row(q_spec(pd, t1), q_xs(db), k))
}

pub proof fn lemma_group_eval(sv: StoresView, db: Database, ps: Seq<Literal>, t1: int, dlo: int, dhi: int)
    requires
        bound_db(sv, db), param_domain(ps), hi_res(pd_of(ps)) == Ok::<int, SqlError>(t1), win_of(dlo, dhi, pd_of(ps), t1),
        group_caps(q_spec(pd_of(ps), t1), q_xs(db)),
    ensures eval_query(db, Seq::empty(), q_group(ps[0])) == Ok::<Relation, SqlError>(q_group_rows(pd_of(ps), t1, db)),
{
    let rows = q_rows(db);
    let cols = q_cols();
    let g = q_spec(pd_of(ps), t1);
    lemma_eval_from(sv, db);
    lemma_pred_agrees(sv, db, ps, t1, dlo, dhi);
    lemma_filter_rows(db, q_from(), rows, cols, q_pred(ps[0]), g);
    lemma_keys_agree(sv, db, ps, t1);
    lemma_args_agree(sv, db, ps, t1);
    lemma_keys_exact(sv, db, ps, t1);
    assert(aggs_match(q_aggs(), g)) by {
        assert(agg_matches(q_aggs()[0], g.aggs[0]));
    }
    lemma_group_query(db, rows, cols, q_filter(ps[0]), q_group_keys(), q_aggs(), g);
}

/// Every GROUP BY row has the 7 key values and the sum.
pub proof fn lemma_group_widths(sv: StoresView, db: Database, ps: Seq<Literal>, t1: int)
    requires bound_db(sv, db),
    ensures forall|t: int| 0 <= t < q_group_rows(pd_of(ps), t1, db).len() ==> (#[trigger] q_group_rows(pd_of(ps), t1, db)[t]).len() == 8,
{
    let g = q_spec(pd_of(ps), t1);
    let xs = q_xs(db);
    let gk = gkeys(g, xs);
    let grows = q_group_rows(pd_of(ps), t1, db);
    assert forall|t: int| 0 <= t < grows.len() implies (#[trigger] grows[t]).len() == 8 by {
        lemma_gkeys(g, xs);
        assert(gk.contains(gk[t]));
        lemma_gkeys_witness(g, xs, gk[t]);
        let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], gk[t]);
        lemma_key_types(sv, db, ps, t1, m);
        assert(grows[t] == full_row(g, xs, gk[t]));
    }
}

/// Projecting the GROUP BY rows onto the SELECT list gives the normal form's result rows.
proof fn lemma_project_result(g: QuerySpec, xs: Seq<Row>)
    requires g.outs == q_outs(), g.grouped,
    ensures gkeys(g, xs).map_values(|k: Row| full_row(g, xs, k)).map_values(|r: Row| select(r, q_outs())) == result_rows(g, xs),
{
    let grows = gkeys(g, xs).map_values(|k: Row| full_row(g, xs, k));
    assert(grows.map_values(|r: Row| select(r, q_outs())) =~= result_rows(g, xs));
}

/// The body of the statement evaluates to the normal form's result rows (inside the arithmetic domain of the
/// groups, `group_caps`).
pub proof fn lemma_denotation(sv: StoresView, db: Database, ps: Seq<Literal>, t1: int, dlo: int, dhi: int)
    requires
        bound_db(sv, db), param_domain(ps), hi_res(pd_of(ps)) == Ok::<int, SqlError>(t1), win_of(dlo, dhi, pd_of(ps), t1),
        group_caps(q_spec(pd_of(ps), t1), q_xs(db)),
    ensures denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(result_rows(q_spec(pd_of(ps), t1), q_xs(db))),
{
    let g = q_spec(pd_of(ps), t1);
    let xs = q_xs(db);
    lemma_query_shape(ps);
    lemma_group_eval(sv, db, ps, t1, dlo, dhi);
    lemma_group_widths(sv, db, ps, t1);
    let grows = q_group_rows(pd_of(ps), t1, db);
    let outs = q_outs();
    assert forall|m: int| 0 <= m < outs.len() implies #[trigger] outs[m] < 8 by {}
    lemma_project_cols(db, q_group(ps[0]), grows, outs, 8);
    lemma_project_result(g, xs);
}

/// When the window's upper bound fails and FROM has a row, the body is that error.
pub proof fn lemma_body_hi_err(sv: StoresView, db: Database, ps: Seq<Literal>, e: SqlError)
    requires
        bound_db(sv, db), param_domain(ps), hi_res(pd_of(ps)) == Err::<int, SqlError>(e),
        n_c(sv) > 0, n_o(sv) > 0, n_l(sv) > 0, n_n(sv) > 0,
    ensures denote_body(db, query_spec_at(ps)) == Err::<Relation, SqlError>(e),
{
    let ctx = Seq::<Val>::empty();
    let rows = q_rows(db);
    lemma_parts_shape(sv, db);
    lemma_query_shape(ps);
    lemma_eval_from(sv, db);
    lemma_product_index(db.tables[2], db.tables[1]);
    lemma_product_index(product_rows(db.tables[2], db.tables[1]), db.tables[0]);
    lemma_product_index(product_rows(product_rows(db.tables[2], db.tables[1]), db.tables[0]), db.tables[6]);
    assert(rows.len() > 0) by (nonlinear_arith)
        requires
            rows.len() == db.tables[2].len() * db.tables[1].len() * db.tables[0].len() * db.tables[6].len(),
            db.tables[2].len() > 0, db.tables[1].len() > 0, db.tables[0].len() > 0, db.tables[6].len() > 0;
    assert forall|k: int| 0 <= k < rows.len() implies #[trigger] eval_pred(db, ctx + rows[k], q_pred(ps[0])) is Ok
        || eval_pred(db, ctx + rows[k], q_pred(ps[0])) == Err::<Truth, SqlError>(e) by {
        assert(ctx + rows[k] =~= rows[k]);
        let w = lemma_joined_witness(sv, db, k);
        lemma_joined_values(sv, db, w);
        lemma_pred_joined_err(sv, db, ps, e, rows[k], w);
    }
    assert(ctx + rows[0] =~= rows[0]);
    let w0 = lemma_joined_witness(sv, db, 0);
    lemma_joined_values(sv, db, w0);
    lemma_pred_joined_err(sv, db, ps, e, rows[0], w0);
    lemma_filter_err(db, ctx, q_pred(ps[0]), Box::new(q_from()), rows, e, 0);
    lemma_first_input(db, ctx, q_group(ps[0]));
    lemma_first_input(db, ctx, q_body(ps[0]));
}

/// On an empty FROM every agreement condition holds vacuously.
proof fn lemma_empty_conds(db: Database, ps: Seq<Literal>, g: QuerySpec)
    requires q_rows(db).len() == 0, g == q_spec(pd_of(ps), 0),
    ensures
        pred_agrees(db, q_rows(db), q_cols(), q_pred(ps[0]), g),
        keys_agree(db, q_rows(db), q_cols(), q_group_keys(), g),
        args_agree(db, q_rows(db), q_cols(), q_aggs(), g),
        keys_exact(g, q_xs(db)),
        aggs_match(q_aggs(), g),
        group_caps(g, q_xs(db)),
        q_xs(db) == Seq::<Row>::empty(),
{
    assert(q_xs(db) =~= Seq::<Row>::empty());
    assert(agg_matches(q_aggs()[0], g.aggs[0]));
    lemma_caps_empty(g);
}

/// When FROM has no row, the body is the empty relation (whatever the window's bound).
pub proof fn lemma_denote_empty(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps), q_rows(db).len() == 0,
    ensures denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(Seq::<Row>::empty()),
{
    hide(eval_pred);
    hide(eval_exprs);
    hide(agg_args);
    let g = q_spec(pd_of(ps), 0);
    let rows = q_rows(db);
    let cols = q_cols();
    lemma_empty_conds(db, ps, g);
    lemma_query_shape(ps);
    lemma_eval_from(sv, db);
    lemma_filter_rows(db, q_from(), rows, cols, q_pred(ps[0]), g);
    lemma_group_query(db, rows, cols, q_filter(ps[0]), q_group_keys(), q_aggs(), g);
    let xs = q_xs(db);
    assert(gkeys(g, xs) =~= Seq::<Row>::empty());
    let grows = gkeys(g, xs).map_values(|k: Row| full_row(g, xs, k));
    assert(grows =~= Seq::<Row>::empty());
    assert forall|m: int| 0 <= m < q_outs().len() implies #[trigger] q_outs()[m] < 8 by {}
    lemma_project_cols(db, q_group(ps[0]), grows, q_outs(), 8);
    assert(grows.map_values(|r: Row| select(r, q_outs())) =~= Seq::<Row>::empty());
}

/// When FROM has no row, the body has no row.
pub proof fn lemma_body_empty(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires
        bound_db(sv, db), param_domain(ps),
        n_c(sv) == 0 || n_o(sv) == 0 || n_l(sv) == 0 || n_n(sv) == 0,
    ensures q_rows(db).len() == 0,
{
    lemma_parts_shape(sv, db);
    lemma_product_index(db.tables[2], db.tables[1]);
    lemma_product_index(product_rows(db.tables[2], db.tables[1]), db.tables[0]);
    lemma_product_index(product_rows(product_rows(db.tables[2], db.tables[1]), db.tables[0]), db.tables[6]);
    let (x, y, z, u) = (db.tables[2].len() as int, db.tables[1].len() as int, db.tables[0].len() as int, db.tables[6].len() as int);
    assert(x * y * z * u == 0) by (nonlinear_arith) requires x == 0 || y == 0 || z == 0 || u == 0;
}

} // verus!
