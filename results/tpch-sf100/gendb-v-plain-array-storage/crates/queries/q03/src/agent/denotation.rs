//! The statement's body evaluates to the normal form's result rows (`lemma_denotation`).
//!
//! Path: FROM is the left-deep product `(customer x orders) x lineitem` of the database tables (`q3_rows`); every
//! joined row is `C[a] ++ O[b] ++ L[i]` (`lemma_joined_witness`), whose ten read columns have the stored values
//! (`lemma_joined_values`). On such a row the WHERE condition evaluates without error to `q3_qual` of the
//! projection (`lemma_pred_row`), the group key to `q3_key` (`lemma_keys_row`) and the SUM argument to the scale-4
//! coefficient `q3_arg` (`lemma_args_row`). The keys have one exact type per position, so SQL "not distinct" is
//! equality on them. Then `link::query::lemma_group_query` (under `group_caps`) and `lemma_project_cols` give
//! `result_rows`.
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
use crate::spec::text::lex_cmp;
use crate::spec::equality::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::source_check::date32_val;
use crate::query::{query_spec_at, param_domain, param_typed};
use crate::link::query::*;
use crate::bridge::equality::{lemma_lex_cmp_zero, same_exact_type};
use crate::bridge::collect::lemma_collect_all;
use crate::link::join::lemma_product_index;
use crate::link::source::lemma_proj_all_index;
use crate::agent::tables::*;
use crate::agent::normal_form::*;

verus! {

// ------------------------------------------------------------------------------------------------ the AST

/// WHERE c_mktsegment = $1 AND c_custkey = o_custkey AND l_orderkey = o_orderkey AND o_orderdate < $2
/// AND l_shipdate > $2 (left-nested ANDs, as the statement writes them).
pub open spec fn q3_pred(ps: Seq<Literal>) -> Pred {
    let n18 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(6), b: Expr::Lit(ps[0]) };
    let n21 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) };
    let n22 = Pred::And(Box::new(n18), Box::new(n21));
    let n25 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(17), b: Expr::Col(8) };
    let n26 = Pred::And(Box::new(n22), Box::new(n25));
    let n30 = Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(12), b: Expr::Lit(ps[1]) };
    let n31 = Pred::And(Box::new(n26), Box::new(n30));
    let n35 = Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(27), b: Expr::Lit(ps[1]) };
    Pred::And(Box::new(n31), Box::new(n35))
}

/// FROM customer, orders, lineitem.
pub open spec fn q3_from() -> Query {
    Query::Product {
        left: Box::new(Query::Product { left: Box::new(Query::Table(2)), right: Box::new(Query::Table(1)) }),
        right: Box::new(Query::Table(0)),
    }
}

/// l_extendedprice * (1 - l_discount).
pub open spec fn q3_sum_arg() -> Expr {
    let n10 = Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) };
    let n12 = Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(n10), b: Box::new(Expr::Col(23)) };
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Col(22)), b: Box::new(n12) }
}

pub open spec fn q3_group_keys() -> Seq<Expr> { seq![Expr::Col(17), Expr::Col(12), Expr::Col(15)] }

pub open spec fn q3_aggs() -> Seq<Agg> { seq![Agg::Sum { kind: NumKind::Numeric, arg: q3_sum_arg() }] }

pub open spec fn q3_filter(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: q3_pred(ps), input: Box::new(q3_from()) }
}

pub open spec fn q3_group(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: q3_group_keys(), aggs: q3_aggs(), input: Box::new(q3_filter(ps)) }
}

pub open spec fn q3_out_positions() -> Seq<nat> { seq![0nat, 3, 1, 2] }

pub open spec fn q3_body(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: col_exprs(q3_out_positions()), input: Box::new(q3_group(ps)) }
}

/// ORDER BY revenue DESC, o_orderdate.
pub open spec fn q3_order_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 1, desc: true, nulls_first: true }, OrderKey { col: 2, desc: false, nulls_first: false }]
}

/// The statement is this AST with LIMIT 10.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures query_spec_at(ps) == (OrderedQuery { body: q3_body(ps), keys: q3_order_keys(), limit: Some(10nat), offset: 0nat }),
{
    let outs = q3_out_positions();
    assert(col_exprs(outs) =~= seq![Expr::Col(0), Expr::Col(3), Expr::Col(1), Expr::Col(2)]);
}

// ------------------------------------------------------------------------------------------------ joined rows

/// FROM's rows: the left-deep product of the database tables.
pub open spec fn q3_rows(db: Database) -> Seq<Row> {
    product_rows(product_rows(db.tables[2], db.tables[1]), db.tables[0])
}

/// The projected joined rows the normal form ranges over.
pub open spec fn q3_xs(db: Database) -> Seq<Row> { proj_all(q3_rows(db), q3_cols()) }

/// FROM evaluates to the product of the tables.
pub proof fn lemma_eval_from(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures eval_query(db, Seq::empty(), q3_from()) == Ok::<Relation, SqlError>(q3_rows(db)),
{
    lemma_parts_shape(sv, db);
    let e = Seq::<Val>::empty();
    assert(eval_query(db, e, Query::Table(2)) == Ok::<Relation, SqlError>(db.tables[2]));
    assert(eval_query(db, e, Query::Table(1)) == Ok::<Relation, SqlError>(db.tables[1]));
    assert(eval_query(db, e, Query::Table(0)) == Ok::<Relation, SqlError>(db.tables[0]));
    let co = Query::Product { left: Box::new(Query::Table(2)), right: Box::new(Query::Table(1)) };
    assert(eval_query(db, e, co) == Ok::<Relation, SqlError>(product_rows(db.tables[2], db.tables[1])));
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

/// Joined row `C[a] ++ O[b] ++ L[i]`.
pub open spec fn joined(db: Database, a: int, b: int, i: int) -> Row {
    db.tables[2][a] + db.tables[1][b] + db.tables[0][i]
}

/// Every joined row is `joined(db, a, b, i)` for some rows `a`, `b`, `i` of the three tables.
pub proof fn lemma_joined_witness(sv: StoresView, db: Database, k: int) -> (w: (int, int, int))
    requires bound_db(sv, db), 0 <= k < q3_rows(db).len(),
    ensures
        0 <= w.0 < n_c(sv), 0 <= w.1 < n_o(sv), 0 <= w.2 < n_l(sv),
        q3_rows(db)[k] == joined(db, w.0, w.1, w.2),
{
    lemma_parts_shape(sv, db);
    let co = product_rows(db.tables[2], db.tables[1]);
    let (x, i) = lemma_product_witness(co, db.tables[0], k);
    let (a, b) = lemma_product_witness(db.tables[2], db.tables[1], x);
    (a, b, i)
}

/// The values a joined row has at the positions the statement reads.
pub proof fn lemma_joined_values(sv: StoresView, db: Database, a: int, b: int, i: int)
    requires bound_db(sv, db), 0 <= a < n_c(sv), 0 <= b < n_o(sv), 0 <= i < n_l(sv),
    ensures ({
        let r = joined(db, a, b, i);
        &&& r.len() == 33
        &&& r[0] == Val::Int(ck(sv)[a] as int)
        &&& r[6] == Val::Text(cseg(sv, a))
        &&& r[8] == Val::Int(ok(sv)[b] as int)
        &&& r[9] == Val::Int(oc(sv)[b] as int)
        &&& r[12] == date32_val(od(sv)[b])
        &&& r[15] == Val::Int(os(sv)[b] as int)
        &&& r[17] == Val::Int(lk(sv)[i] as int)
        &&& r[22] == (Val::Num { coeff: lp(sv)[i] as int, scale: 2 })
        &&& r[23] == (Val::Num { coeff: ld(sv)[i] as int, scale: 2 })
        &&& r[27] == date32_val(ls(sv)[i])
        &&& num15(lp(sv)[i]) && num15(ld(sv)[i])
    }),
{
    lemma_parts_shape(sv, db);
    lemma_customer_row(sv, db, a);
    lemma_orders_row(sv, db, b);
    lemma_lineitem_row(sv, db, i);
    let c = db.tables[2][a];
    let o = db.tables[1][b];
    let l = db.tables[0][i];
    let co = c + o;
    let r = co + l;
    assert(co[0] == c[0] && co[6] == c[6]);
    assert(co[8] == o[0] && co[9] == o[1] && co[12] == o[4] && co[15] == o[7]);
    assert(r[0] == co[0] && r[6] == co[6] && r[8] == co[8] && r[9] == co[9] && r[12] == co[12] && r[15] == co[15]);
    assert(r[17] == l[0] && r[22] == l[5] && r[23] == l[6] && r[27] == l[10]);
}

/// The projection of a joined row onto the read columns.
pub proof fn lemma_joined_proj(r: Row)
    requires r.len() == 33,
    ensures proj(r, q3_cols()) == seq![r[0], r[6], r[8], r[9], r[12], r[15], r[17], r[22], r[23], r[27]],
{
    assert(proj(r, q3_cols()) =~= seq![r[0], r[6], r[8], r[9], r[12], r[15], r[17], r[22], r[23], r[27]]);
}

// ------------------------------------------------------------------------------------------------ one evaluator step each

pub proof fn lemma_eval_col(db: Database, r: Row, k: nat)
    requires k < r.len(),
    ensures eval_expr(db, r, Expr::Col(k)) == Ok::<Val, SqlError>(r[k as int]),
{
}

pub proof fn lemma_eval_lit(db: Database, r: Row, l: Literal)
    ensures eval_expr(db, r, Expr::Lit(l)) == lit_val(l),
{
}

pub proof fn lemma_eval_cmp(db: Database, r: Row, op: CmpOp, a: Expr, b: Expr, va: Val, vb: Val)
    requires eval_expr(db, r, a) == Ok::<Val, SqlError>(va), eval_expr(db, r, b) == Ok::<Val, SqlError>(vb),
    ensures eval_pred(db, r, Pred::Cmp { op, a, b }) == cmp_truth(op, va, vb),
{
}

pub proof fn lemma_eval_and(db: Database, r: Row, a: Pred, b: Pred, x: bool, y: bool)
    requires eval_pred(db, r, a) == Ok::<Truth, SqlError>(truth_of(x)), eval_pred(db, r, b) == Ok::<Truth, SqlError>(truth_of(y)),
    ensures eval_pred(db, r, Pred::And(Box::new(a), Box::new(b))) == Ok::<Truth, SqlError>(truth_of(x && y)),
{
}

pub proof fn lemma_lit_one()
    ensures lit_val(Literal::Int { v: 1, kind: IntKind::Int4 }) == Ok::<Val, SqlError>(Val::Int(1)),
{
}

pub proof fn lemma_eval_cast(db: Database, r: Row, arg: Expr, x: int)
    requires eval_expr(db, r, arg) == Ok::<Val, SqlError>(Val::Int(x)),
    ensures eval_expr(db, r, Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(arg) }) == Ok::<Val, SqlError>(Val::Num { coeff: x, scale: 0 }),
{
}

pub proof fn lemma_eval_cast_one(db: Database, r: Row)
    ensures eval_expr(db, r, Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) })
        == Ok::<Val, SqlError>(Val::Num { coeff: 1, scale: 0 }),
{
    lemma_lit_one();
    lemma_eval_lit(db, r, Literal::Int { v: 1, kind: IntKind::Int4 });
    lemma_eval_cast(db, r, Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 }), 1);
}

/// Comparison of two integer values.
pub proof fn lemma_cmp_int_eq(x: int, y: int)
    ensures cmp_truth(CmpOp::Eq, Val::Int(x), Val::Int(y)) == Ok::<Truth, SqlError>(truth_of(x == y)),
{
}

/// Comparisons of two dates.
pub proof fn lemma_cmp_date(x: int, y: int)
    ensures
        cmp_truth(CmpOp::Lt, Val::Date(x), Val::Date(y)) == Ok::<Truth, SqlError>(truth_of(x < y)),
        cmp_truth(CmpOp::Gt, Val::Date(x), Val::Date(y)) == Ok::<Truth, SqlError>(truth_of(x > y)),
{
}

/// Byte equality of two texts.
pub proof fn lemma_cmp_text(x: Seq<u8>, y: Seq<u8>)
    ensures cmp_truth(CmpOp::Eq, Val::Text(x), Val::Text(y)) == Ok::<Truth, SqlError>(truth_of(x == y)),
{
    lemma_lex_cmp_zero(x, y);
}

/// The literal values of the two parameters.
pub proof fn lemma_param_values(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures
        lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Text(seg_of(ps))),
        lit_val(ps[1]) == Ok::<Val, SqlError>(Val::Date(day_of(ps))),
{
}

// ------------------------------------------------------------------------------------------------ per-row evaluation

/// A joined row as the statement sees it: 33 values; the ten it reads have these types and values.
pub open spec fn row_shape(r: Row, cust_key: int, seg: Seq<u8>, okey: int, ocust: int, odate: int, oship: int,
    lkey: int, price: int, disc: int, ship: int) -> bool
{
    &&& r.len() == 33
    &&& r[0] == Val::Int(cust_key)
    &&& r[6] == Val::Text(seg)
    &&& r[8] == Val::Int(okey)
    &&& r[9] == Val::Int(ocust)
    &&& r[12] == Val::Date(odate)
    &&& r[15] == Val::Int(oship)
    &&& r[17] == Val::Int(lkey)
    &&& r[22] == (Val::Num { coeff: price, scale: 2 })
    &&& r[23] == (Val::Num { coeff: disc, scale: 2 })
    &&& r[27] == Val::Date(ship)
}

/// The WHERE condition on a row of this shape.
pub proof fn lemma_pred_shape(db: Database, ps: Seq<Literal>, r: Row, cust_key: int, seg: Seq<u8>, okey: int, ocust: int,
    odate: int, oship: int, lkey: int, price: int, disc: int, ship: int)
    requires
        param_domain(ps),
        row_shape(r, cust_key, seg, okey, ocust, odate, oship, lkey, price, disc, ship),
    ensures
        eval_pred(db, r, q3_pred(ps)) == Ok::<Truth, SqlError>(truth_of(
            seg == seg_of(ps) && cust_key == ocust && lkey == okey && odate < day_of(ps) && ship > day_of(ps))),
{
    lemma_param_values(ps);
    let p = day_of(ps);
    lemma_eval_col(db, r, 6);
    lemma_eval_col(db, r, 0);
    lemma_eval_col(db, r, 9);
    lemma_eval_col(db, r, 17);
    lemma_eval_col(db, r, 8);
    lemma_eval_col(db, r, 12);
    lemma_eval_col(db, r, 27);
    lemma_eval_lit(db, r, ps[0]);
    lemma_eval_lit(db, r, ps[1]);
    lemma_cmp_text(seg, seg_of(ps));
    lemma_cmp_int_eq(cust_key, ocust);
    lemma_cmp_int_eq(lkey, okey);
    lemma_cmp_date(odate, p);
    lemma_cmp_date(ship, p);
    let n18 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(6), b: Expr::Lit(ps[0]) };
    let n21 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) };
    let n25 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(17), b: Expr::Col(8) };
    let n30 = Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(12), b: Expr::Lit(ps[1]) };
    let n35 = Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(27), b: Expr::Lit(ps[1]) };
    lemma_eval_cmp(db, r, CmpOp::Eq, Expr::Col(6), Expr::Lit(ps[0]), Val::Text(seg), Val::Text(seg_of(ps)));
    lemma_eval_cmp(db, r, CmpOp::Eq, Expr::Col(0), Expr::Col(9), Val::Int(cust_key), Val::Int(ocust));
    lemma_eval_cmp(db, r, CmpOp::Eq, Expr::Col(17), Expr::Col(8), Val::Int(lkey), Val::Int(okey));
    lemma_eval_cmp(db, r, CmpOp::Lt, Expr::Col(12), Expr::Lit(ps[1]), Val::Date(odate), Val::Date(p));
    lemma_eval_cmp(db, r, CmpOp::Gt, Expr::Col(27), Expr::Lit(ps[1]), Val::Date(ship), Val::Date(p));
    let (e18, e21, e25, e30, e35) = (seg == seg_of(ps), cust_key == ocust, lkey == okey, odate < p, ship > p);
    lemma_eval_and(db, r, n18, n21, e18, e21);
    let n22 = Pred::And(Box::new(n18), Box::new(n21));
    lemma_eval_and(db, r, n22, n25, e18 && e21, e25);
    let n26 = Pred::And(Box::new(n22), Box::new(n25));
    lemma_eval_and(db, r, n26, n30, e18 && e21 && e25, e30);
    let n31 = Pred::And(Box::new(n26), Box::new(n30));
    lemma_eval_and(db, r, n31, n35, e18 && e21 && e25 && e30, e35);
}

/// The group key on a row of this shape.
pub proof fn lemma_keys_shape(db: Database, r: Row, cust_key: int, seg: Seq<u8>, okey: int, ocust: int,
    odate: int, oship: int, lkey: int, price: int, disc: int, ship: int)
    requires row_shape(r, cust_key, seg, okey, ocust, odate, oship, lkey, price, disc, ship),
    ensures eval_exprs(db, r, q3_group_keys()) == Ok::<Row, SqlError>(seq![Val::Int(lkey), Val::Date(odate), Val::Int(oship)]),
{
    let idxs = seq![17nat, 12, 15];
    assert(col_exprs(idxs) =~= q3_group_keys());
    lemma_eval_cols(db, r, idxs);
    assert(select(r, idxs) =~= seq![Val::Int(lkey), Val::Date(odate), Val::Int(oship)]);
}

/// The SUM argument on a row of this shape (prices and discounts of numeric(15,2)).
pub proof fn lemma_sum_arg_shape(db: Database, r: Row, cust_key: int, seg: Seq<u8>, okey: int, ocust: int,
    odate: int, oship: int, lkey: int, price: int, disc: int, ship: int)
    requires
        row_shape(r, cust_key, seg, okey, ocust, odate, oship, lkey, price, disc, ship),
        abs(price) < pow10(15), abs(disc) < pow10(15),
    ensures eval_expr(db, r, q3_sum_arg()) == Ok::<Val, SqlError>(Val::Num { coeff: price * (100 - disc), scale: 4 }),
{
    let n10 = Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) };
    lemma_eval_cast_one(db, r);
    lemma_eval_col(db, r, 22);
    lemma_eval_col(db, r, 23);
    assert(pow10(1) == 10 && pow10(2) == 100 && pow10(0) == 1) by (compute);
    assert(crate::spec::limits::numeric_int_digits_max() >= 100) by (compute);
    lemma_node_add(db, r, ArithOp::Sub, n10, Expr::Col(23), 1, 0, 1, disc, 2, 15, 2, 100, 1, 16);
    let n12 = Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(n10), b: Box::new(Expr::Col(23)) };
    assert(1 * 100 - disc * 1 == 100 - disc);
    lemma_node_mul(db, r, Expr::Col(22), n12, price, 2, 15, 100 - disc, 2, 16);
}

/// The aggregate arguments on a row of this shape: one value, the SUM argument.
pub proof fn lemma_args_shape(db: Database, ps: Seq<Literal>, r: Row, cust_key: int, seg: Seq<u8>, okey: int, ocust: int,
    odate: int, oship: int, lkey: int, price: int, disc: int, ship: int)
    requires
        row_shape(r, cust_key, seg, okey, ocust, odate, oship, lkey, price, disc, ship),
        abs(price) < pow10(15), abs(disc) < pow10(15),
    ensures agg_args(db, r, q3_aggs()) == Ok::<Row, SqlError>(seq![Val::Num { coeff: price * (100 - disc), scale: 4 }]),
{
    lemma_sum_arg_shape(db, r, cust_key, seg, okey, ocust, odate, oship, lkey, price, disc, ship);
    let rs = agg_arg_results(db, r, q3_aggs());
    lemma_agg_arg_results_index(db, r, q3_aggs());
    let vs = seq![Val::Num { coeff: price * (100 - disc), scale: 4 }];
    assert(rs[0] == agg_arg(db, r, q3_aggs()[0]));
    assert(rs[0] == Ok::<Val, SqlError>(vs[0]));
    lemma_collect_all(rs, vs);
}

// ------------------------------------------------------------------------------------------------ joined rows of the database

/// A joined row of the database has the shape, with the stored values.
pub proof fn lemma_joined_shape(sv: StoresView, db: Database, a: int, b: int, i: int)
    requires bound_db(sv, db), 0 <= a < n_c(sv), 0 <= b < n_o(sv), 0 <= i < n_l(sv),
    ensures
        row_shape(joined(db, a, b, i), ck(sv)[a] as int, cseg(sv, a), ok(sv)[b] as int, oc(sv)[b] as int,
            od(sv)[b] as int - 10957, os(sv)[b] as int, lk(sv)[i] as int, lp(sv)[i] as int, ld(sv)[i] as int,
            ls(sv)[i] as int - 10957),
        abs(lp(sv)[i] as int) < pow10(15), abs(ld(sv)[i] as int) < pow10(15),
{
    lemma_joined_values(sv, db, a, b, i);
    assert(pow10(15) == 1_000_000_000_000_000) by (compute);
}

/// The joined row `(a, b, i)` qualifies exactly when the customer has segment `$1` and is the order's customer,
/// the lineitem is the order's, the order is dated before `$2` and the lineitem ships after it.
pub open spec fn joined_qual(sv: StoresView, ps: Seq<Literal>, a: int, b: int, i: int) -> bool {
    &&& cseg(sv, a) == seg_of(ps)
    &&& ck(sv)[a] == oc(sv)[b]
    &&& lk(sv)[i] == ok(sv)[b]
    &&& (od(sv)[b] as int) < dl_of(ps)
    &&& (ls(sv)[i] as int) > dl_of(ps)
}

/// The normal form on a joined row of the database: qualification, key and argument.
pub proof fn lemma_joined_normal_form(sv: StoresView, db: Database, ps: Seq<Literal>, a: int, b: int, i: int)
    requires bound_db(sv, db), 0 <= a < n_c(sv), 0 <= b < n_o(sv), 0 <= i < n_l(sv),
    ensures ({
        let x = proj(joined(db, a, b, i), q3_cols());
        let g = q3_spec(ps);
        &&& (g.qual)(x) == joined_qual(sv, ps, a, b, i)
        &&& (g.key)(x) == seq![Val::Int(lk(sv)[i] as int), date32_val(od(sv)[b]), Val::Int(os(sv)[b] as int)]
        &&& (g.arg)(0, x) == line_value(sv, i)
    }),
{
    let r = joined(db, a, b, i);
    lemma_joined_values(sv, db, a, b, i);
    lemma_joined_proj(r);
}

/// WHERE agrees with the normal form on every joined row.
pub proof fn lemma_pred_agrees(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps),
    ensures pred_agrees(db, q3_rows(db), q3_cols(), q3_pred(ps), q3_spec(ps)),
{
    let rows = q3_rows(db);
    let g = q3_spec(ps);
    assert forall|k: int| 0 <= k < rows.len() implies
        eval_pred(db, #[trigger] rows[k], q3_pred(ps)) == Ok::<Truth, SqlError>(truth_of((g.qual)(proj(rows[k], q3_cols())))) by {
        let (a, b, i) = lemma_joined_witness(sv, db, k);
        lemma_joined_shape(sv, db, a, b, i);
        lemma_pred_shape(db, ps, joined(db, a, b, i), ck(sv)[a] as int, cseg(sv, a), ok(sv)[b] as int, oc(sv)[b] as int,
            od(sv)[b] as int - 10957, os(sv)[b] as int, lk(sv)[i] as int, lp(sv)[i] as int, ld(sv)[i] as int,
            ls(sv)[i] as int - 10957);
        lemma_joined_normal_form(sv, db, ps, a, b, i);
    }
}

/// GROUP BY keys agree with the normal form on every joined row.
pub proof fn lemma_keys_agree(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps),
    ensures keys_agree(db, q3_rows(db), q3_cols(), q3_group_keys(), q3_spec(ps)),
{
    let rows = q3_rows(db);
    let g = q3_spec(ps);
    assert forall|k: int| 0 <= k < rows.len() && (g.qual)(proj(#[trigger] rows[k], q3_cols())) implies
        eval_exprs(db, rows[k], q3_group_keys()) == Ok::<Row, SqlError>((g.key)(proj(rows[k], q3_cols()))) by {
        let (a, b, i) = lemma_joined_witness(sv, db, k);
        lemma_joined_shape(sv, db, a, b, i);
        lemma_keys_shape(db, joined(db, a, b, i), ck(sv)[a] as int, cseg(sv, a), ok(sv)[b] as int, oc(sv)[b] as int,
            od(sv)[b] as int - 10957, os(sv)[b] as int, lk(sv)[i] as int, lp(sv)[i] as int, ld(sv)[i] as int,
            ls(sv)[i] as int - 10957);
        lemma_joined_normal_form(sv, db, ps, a, b, i);
    }
}

/// The SUM argument agrees with the normal form on every joined row.
pub proof fn lemma_args_agree(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps),
    ensures args_agree(db, q3_rows(db), q3_cols(), q3_aggs(), q3_spec(ps)),
{
    let rows = q3_rows(db);
    let g = q3_spec(ps);
    assert forall|k: int| 0 <= k < rows.len() && (g.qual)(proj(#[trigger] rows[k], q3_cols())) implies
        agg_args(db, rows[k], q3_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[k], q3_cols()))) by {
        let (a, b, i) = lemma_joined_witness(sv, db, k);
        lemma_joined_shape(sv, db, a, b, i);
        lemma_args_shape(db, ps, joined(db, a, b, i), ck(sv)[a] as int, cseg(sv, a), ok(sv)[b] as int, oc(sv)[b] as int,
            od(sv)[b] as int - 10957, os(sv)[b] as int, lk(sv)[i] as int, lp(sv)[i] as int, ld(sv)[i] as int,
            ls(sv)[i] as int - 10957);
        lemma_joined_normal_form(sv, db, ps, a, b, i);
        let x = proj(rows[k], q3_cols());
        assert(arg_vals(g, x) =~= seq![Val::Num { coeff: line_value(sv, i), scale: 4 }]);
    }
}

/// Every projected joined row's key is `(int, date, int)`.
pub proof fn lemma_key_types(sv: StoresView, db: Database, ps: Seq<Literal>, m: int)
    requires bound_db(sv, db), 0 <= m < q3_xs(db).len(),
    ensures ({
        let k = (q3_spec(ps).key)(q3_xs(db)[m]);
        &&& k.len() == 3
        &&& k[0] is Int && k[1] is Date && k[2] is Int
    }),
{
    let rows = q3_rows(db);
    lemma_proj_all_index(rows, q3_cols());
    let (a, b, i) = lemma_joined_witness(sv, db, m);
    lemma_joined_normal_form(sv, db, ps, a, b, i);
}

/// SQL "not distinct" is equality on the keys of the joined rows.
pub proof fn lemma_keys_exact(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db),
    ensures keys_exact(q3_spec(ps), q3_xs(db)),
{
    let g = q3_spec(ps);
    let xs = q3_xs(db);
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        lemma_key_types(sv, db, ps, a);
        lemma_key_types(sv, db, ps, b);
        let (ka, kb) = ((g.key)(xs[a]), (g.key)(xs[b]));
        assert forall|t: int| 0 <= t < ka.len() implies same_exact_type(#[trigger] ka[t], kb[t]) by {
            if t == 0 {} else if t == 1 {} else {}
        }
        lemma_row_exact(ka, kb);
    }
}

/// The GROUP BY rows: the full row of every group key, in first-occurrence order.
pub open spec fn q3_group_rows(ps: Seq<Literal>, db: Database) -> Seq<Row> {
    gkeys(q3_spec(ps), q3_xs(db)).map_values(|k: Row| full_row(q3_spec(ps), q3_xs(db), k))
}

pub proof fn lemma_group_eval(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps), group_caps(q3_spec(ps), q3_xs(db)),
    ensures eval_query(db, Seq::empty(), q3_group(ps)) == Ok::<Relation, SqlError>(q3_group_rows(ps, db)),
{
    let rows = q3_rows(db);
    let cols = q3_cols();
    let g = q3_spec(ps);
    lemma_eval_from(sv, db);
    lemma_pred_agrees(sv, db, ps);
    lemma_filter_rows(db, q3_from(), rows, cols, q3_pred(ps), g);
    lemma_keys_agree(sv, db, ps);
    lemma_args_agree(sv, db, ps);
    lemma_keys_exact(sv, db, ps);
    assert(aggs_match(q3_aggs(), g)) by {
        assert(agg_matches(q3_aggs()[0], g.aggs[0]));
    }
    lemma_group_query(db, rows, cols, q3_filter(ps), q3_group_keys(), q3_aggs(), g);
}

/// Every GROUP BY row has the 3 key values and the sum.
pub proof fn lemma_group_widths(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db),
    ensures forall|t: int| 0 <= t < q3_group_rows(ps, db).len() ==> (#[trigger] q3_group_rows(ps, db)[t]).len() == 4,
{
    let g = q3_spec(ps);
    let xs = q3_xs(db);
    let gk = gkeys(g, xs);
    let grows = q3_group_rows(ps, db);
    assert forall|t: int| 0 <= t < grows.len() implies (#[trigger] grows[t]).len() == 4 by {
        lemma_gkeys(g, xs);
        assert(gk.contains(gk[t]));
        lemma_gkeys_witness(g, xs, gk[t]);
        let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], gk[t]);
        lemma_key_types(sv, db, ps, m);
        assert(grows[t] == full_row(g, xs, gk[t]));
    }
}

/// The body of the statement evaluates to the normal form's result rows (inside the arithmetic domain of the
/// groups, `group_caps`).
pub proof fn lemma_denotation(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps), group_caps(q3_spec(ps), q3_xs(db)),
    ensures denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(result_rows(q3_spec(ps), q3_xs(db))),
{
    let g = q3_spec(ps);
    let xs = q3_xs(db);
    lemma_query_shape(ps);
    lemma_group_eval(sv, db, ps);
    lemma_group_widths(sv, db, ps);
    let grows = q3_group_rows(ps, db);
    let outs = q3_out_positions();
    lemma_project_cols(db, q3_group(ps), grows, outs, 4);
    assert(grows.map_values(|r: Row| select(r, outs)) =~= result_rows(g, xs));
}

} // verus!
