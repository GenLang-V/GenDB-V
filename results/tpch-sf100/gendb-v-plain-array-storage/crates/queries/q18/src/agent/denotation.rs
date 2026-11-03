//! The statement's body evaluates to the normal form's result rows (`lemma_denotation`).
//!
//! Normal form (`q_spec`, over the joined rows of `FROM customer, orders, lineitem` projected by `q_cols` to
//! `x = [c_custkey, c_name, o_orderkey, o_custkey, o_totalprice, o_orderdate, l_orderkey, l_quantity]`): a row
//! qualifies when its order key is in the subquery's result (`subquery::in_sub`), its customer is the order's and
//! its lineitem is the order's; the group key is `(c_name, c_custkey, o_orderkey, o_orderdate, o_totalprice)`; the
//! SUM argument is the `l_quantity` coefficient (scale 2); the output is the GROUP BY row itself.
//!
//! Path: FROM is the left-deep product `(customer x orders) x lineitem` (`q_rows`); every joined row is
//! `C[a] ++ O[b] ++ L[i]` (`lemma_joined_witness`) with the stored values (`lemma_joined_values`). On such a row the
//! WHERE condition is two-valued and equals the normal form's (`lemma_pred_joined`, with the subquery's
//! `lemma_in_pred`), the keys and the SUM argument evaluate to the normal form's. The keys have one exact type per
//! position, so SQL "not distinct" is equality. `link::query::lemma_group_query` (inside `group_caps`) gives the
//! GROUP BY rows, which are the result rows (the output selects every column, `lemma_select_identity`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::order::*;
use crate::spec::equality::*;
use crate::spec::text::lex_cmp;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::source_check::date32_val;
use crate::query::{query_spec_at, param_domain};
use crate::link::query::*;
use crate::link::expr::{lemma_pred_and};
use crate::bridge::equality::{lemma_lex_cmp_zero, same_exact_type};
use crate::bridge::collect::lemma_collect_all;
use crate::link::join::lemma_product_index;
use crate::link::source::lemma_proj_all_index;
use crate::agent::tables::*;
use crate::agent::subquery::*;

verus! {

// ------------------------------------------------------------------------------------------------ the AST

/// WHERE o_orderkey IN (..) AND c_custkey = o_custkey AND o_orderkey = l_orderkey (left-nested ANDs).
pub open spec fn q_pred(ps: Seq<Literal>) -> Pred {
    let n24 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) };
    let n25 = Pred::And(Box::new(in_pred(ps)), Box::new(n24));
    let n28 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(8), b: Expr::Col(17) };
    Pred::And(Box::new(n25), Box::new(n28))
}

/// FROM customer, orders, lineitem.
pub open spec fn q_from() -> Query {
    Query::Product {
        left: Box::new(Query::Product { left: Box::new(Query::Table(2)), right: Box::new(Query::Table(1)) }),
        right: Box::new(Query::Table(0)),
    }
}

/// GROUP BY c_name, c_custkey, o_orderkey, o_orderdate, o_totalprice.
pub open spec fn q_group_keys() -> Seq<Expr> { seq![Expr::Col(1), Expr::Col(0), Expr::Col(8), Expr::Col(12), Expr::Col(11)] }

/// SUM(l_quantity).
pub open spec fn q_aggs() -> Seq<Agg> { seq![Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(21) }] }

pub open spec fn q_filter(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: q_pred(ps), input: Box::new(q_from()) }
}

pub open spec fn q_body(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: q_group_keys(), aggs: q_aggs(), input: Box::new(q_filter(ps)) }
}

/// ORDER BY o_totalprice DESC, o_orderdate.
pub open spec fn q_order_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 4, desc: true, nulls_first: true }, OrderKey { col: 3, desc: false, nulls_first: false }]
}

/// The statement is this AST with LIMIT 100.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures query_spec_at(ps) == (OrderedQuery { body: q_body(ps), keys: q_order_keys(), limit: Some(100nat), offset: 0nat }),
{
}

// ------------------------------------------------------------------------------------------------ normal form

/// Positions read, in the joined row `customer (0..8) ++ orders (8..17) ++ lineitem (17..33)`.
pub open spec fn q_cols() -> Seq<nat> { seq![0nat, 1, 8, 9, 11, 12, 17, 21] }

/// The value is an order key in the subquery's result.
pub open spec fn sub_val(sv: StoresView, ps: Seq<Literal>, v: Val) -> bool {
    match v { Val::Int(w) => in_sub(sv, ps, w), _ => false }
}

pub open spec fn q_qual(sv: StoresView, ps: Seq<Literal>, x: Row) -> bool {
    &&& sub_val(sv, ps, x[2])
    &&& x[0] == x[3]
    &&& x[2] == x[6]
}

pub open spec fn q_key(x: Row) -> Row { seq![x[1], x[0], x[2], x[5], x[4]] }

/// The statement's normal form at binding `ps` over the stored data `sv`.
pub open spec fn q_spec(sv: StoresView, ps: Seq<Literal>) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| q_qual(sv, ps, x),
        key: |x: Row| q_key(x),
        arg: |j: int, x: Row| coeff_of(x[7]),
        aggs: seq![AggKind::Sum { scale: 2 }],
        outs: seq![0nat, 1, 2, 3, 4, 5],
        grouped: true,
    }
}

// ------------------------------------------------------------------------------------------------ joined rows

/// FROM's rows: the left-deep product of the database tables.
pub open spec fn q_rows(db: Database) -> Seq<Row> {
    product_rows(product_rows(db.tables[2], db.tables[1]), db.tables[0])
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
    requires bound_db(sv, db), 0 <= k < q_rows(db).len(),
    ensures
        0 <= w.0 < n_c(sv), 0 <= w.1 < n_o(sv), 0 <= w.2 < n_l(sv),
        q_rows(db)[k] == joined(db, w.0, w.1, w.2),
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
        &&& r[1] == Val::Text(cname(sv, a))
        &&& r[8] == Val::Int(ok(sv)[b] as int)
        &&& r[9] == Val::Int(oc(sv)[b] as int)
        &&& r[11] == (Val::Num { coeff: otp(sv)[b] as int, scale: 2 })
        &&& r[12] == date32_val(od(sv)[b])
        &&& r[17] == Val::Int(lk(sv)[i] as int)
        &&& r[21] == (Val::Num { coeff: lq(sv)[i] as int, scale: 2 })
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
    assert(co[0] == c[0] && co[1] == c[1]);
    assert(co[8] == o[0] && co[9] == o[1] && co[11] == o[3] && co[12] == o[4]);
    assert(r[0] == co[0] && r[1] == co[1] && r[8] == co[8] && r[9] == co[9] && r[11] == co[11] && r[12] == co[12]);
    assert(r[17] == l[0] && r[21] == l[4]);
}

/// The projection of a joined row onto the read columns.
pub proof fn lemma_joined_proj(r: Row)
    requires r.len() == 33,
    ensures proj(r, q_cols()) == seq![r[0], r[1], r[8], r[9], r[11], r[12], r[17], r[21]],
{
    assert(proj(r, q_cols()) =~= seq![r[0], r[1], r[8], r[9], r[11], r[12], r[17], r[21]]);
}

/// The stored date `d` as a VERUS_SQL date (days since 2000-01-01).
pub proof fn lemma_date32(d: i32)
    ensures date32_val(d) == Val::Date(d as int - 10957),
{
}

// ------------------------------------------------------------------------------------------------ per-row evaluation

/// Equality of two integer columns.
proof fn lemma_eq_cols(db: Database, r: Row, p: nat, q: nat, x: int, y: int)
    requires p < r.len(), q < r.len(), r[p as int] == Val::Int(x), r[q as int] == Val::Int(y),
    ensures eval_pred(db, r, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(p), b: Expr::Col(q) }) == Ok::<Truth, SqlError>(truth_of(x == y)),
{
    assert(eval_expr(db, r, Expr::Col(p)) == Ok::<Val, SqlError>(Val::Int(x)));
    assert(eval_expr(db, r, Expr::Col(q)) == Ok::<Val, SqlError>(Val::Int(y)));
    assert(compare(Val::Int(x), Val::Int(y)) == Some(sign(x - y)));
}

/// The joined row `(a, b, i)` qualifies exactly when the order key is in the subquery's result, the customer is
/// the order's and the lineitem is the order's.
pub open spec fn joined_qual(sv: StoresView, ps: Seq<Literal>, a: int, b: int, i: int) -> bool {
    &&& in_sub(sv, ps, ok(sv)[b] as int)
    &&& ck(sv)[a] == oc(sv)[b]
    &&& ok(sv)[b] == lk(sv)[i]
}

/// WHERE on a joined row of the database.
pub proof fn lemma_pred_joined(sv: StoresView, db: Database, ps: Seq<Literal>, a: int, b: int, i: int)
    requires bound_db(sv, db), small(sv), param_domain(ps), 0 <= a < n_c(sv), 0 <= b < n_o(sv), 0 <= i < n_l(sv),
    ensures eval_pred(db, joined(db, a, b, i), q_pred(ps)) == Ok::<Truth, SqlError>(truth_of(joined_qual(sv, ps, a, b, i))),
{
    let r = joined(db, a, b, i);
    lemma_joined_values(sv, db, a, b, i);
    let (x1, x2, x3) = (in_sub(sv, ps, ok(sv)[b] as int), ck(sv)[a] == oc(sv)[b], ok(sv)[b] == lk(sv)[i]);
    lemma_in_pred(sv, db, ps, r, ok(sv)[b] as int);
    let n24 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) };
    let n28 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(8), b: Expr::Col(17) };
    lemma_eq_cols(db, r, 0, 9, ck(sv)[a] as int, oc(sv)[b] as int);
    lemma_eq_cols(db, r, 8, 17, ok(sv)[b] as int, lk(sv)[i] as int);
    lemma_pred_and(db, r, in_pred(ps), n24, x1, x2);
    let n25 = Pred::And(Box::new(in_pred(ps)), Box::new(n24));
    lemma_pred_and(db, r, n25, n28, x1 && x2, x3);
}

/// The normal form on a joined row of the database: qualification, key and argument.
pub proof fn lemma_joined_normal_form(sv: StoresView, db: Database, ps: Seq<Literal>, a: int, b: int, i: int)
    requires bound_db(sv, db), 0 <= a < n_c(sv), 0 <= b < n_o(sv), 0 <= i < n_l(sv),
    ensures ({
        let x = proj(joined(db, a, b, i), q_cols());
        let g = q_spec(sv, ps);
        &&& (g.qual)(x) == joined_qual(sv, ps, a, b, i)
        &&& (g.key)(x) == seq![Val::Text(cname(sv, a)), Val::Int(ck(sv)[a] as int), Val::Int(ok(sv)[b] as int),
                date32_val(od(sv)[b]), Val::Num { coeff: otp(sv)[b] as int, scale: 2 }]
        &&& (g.arg)(0, x) == lq(sv)[i] as int
        &&& x[7] == (Val::Num { coeff: lq(sv)[i] as int, scale: 2 })
    }),
{
    let r = joined(db, a, b, i);
    lemma_joined_values(sv, db, a, b, i);
    lemma_joined_proj(r);
    let x = proj(r, q_cols());
    assert(q_key(x) =~= seq![Val::Text(cname(sv, a)), Val::Int(ck(sv)[a] as int), Val::Int(ok(sv)[b] as int),
        date32_val(od(sv)[b]), Val::Num { coeff: otp(sv)[b] as int, scale: 2 }]);
}

/// WHERE agrees with the normal form on every joined row.
pub proof fn lemma_pred_agrees(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), small(sv), param_domain(ps),
    ensures pred_agrees(db, q_rows(db), q_cols(), q_pred(ps), q_spec(sv, ps)),
{
    let rows = q_rows(db);
    let g = q_spec(sv, ps);
    assert forall|k: int| 0 <= k < rows.len() implies
        eval_pred(db, #[trigger] rows[k], q_pred(ps)) == Ok::<Truth, SqlError>(truth_of((g.qual)(proj(rows[k], q_cols())))) by {
        let (a, b, i) = lemma_joined_witness(sv, db, k);
        lemma_pred_joined(sv, db, ps, a, b, i);
        lemma_joined_normal_form(sv, db, ps, a, b, i);
    }
}

/// The GROUP BY keys on any 33-value row: the read columns, as the normal form's key.
proof fn lemma_keys_row(db: Database, r: Row)
    requires r.len() == 33,
    ensures eval_exprs(db, r, q_group_keys()) == Ok::<Row, SqlError>(q_key(proj(r, q_cols()))),
{
    hide(eval_exprs);
    hide(eval_expr);
    let idxs = seq![1nat, 0, 8, 12, 11];
    assert(col_exprs(idxs) =~= q_group_keys());
    lemma_eval_cols(db, r, idxs);
    let x = proj(r, q_cols());
    lemma_joined_proj(r);
    assert(x[0] == r[0] && x[1] == r[1] && x[2] == r[8] && x[4] == r[11] && x[5] == r[12]);
    let sel = select(r, idxs);
    assert(sel.len() == 5);
    assert(sel[0] == r[1] && sel[1] == r[0] && sel[2] == r[8] && sel[3] == r[12] && sel[4] == r[11]);
    assert(sel =~= q_key(x));
}

/// The GROUP BY keys on one joined row.
proof fn lemma_keys_joined(sv: StoresView, db: Database, ps: Seq<Literal>, a: int, b: int, i: int)
    requires bound_db(sv, db), 0 <= a < n_c(sv), 0 <= b < n_o(sv), 0 <= i < n_l(sv),
    ensures eval_exprs(db, joined(db, a, b, i), q_group_keys()) == Ok::<Row, SqlError>(q_key(proj(joined(db, a, b, i), q_cols()))),
{
    lemma_joined_values(sv, db, a, b, i);
    lemma_keys_row(db, joined(db, a, b, i));
}

/// GROUP BY keys agree with the normal form on every joined row.
pub proof fn lemma_keys_agree(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db),
    ensures keys_agree(db, q_rows(db), q_cols(), q_group_keys(), q_spec(sv, ps)),
{
    let rows = q_rows(db);
    let g = q_spec(sv, ps);
    assert forall|k: int| 0 <= k < rows.len() && (g.qual)(proj(#[trigger] rows[k], q_cols())) implies
        eval_exprs(db, rows[k], q_group_keys()) == Ok::<Row, SqlError>((g.key)(proj(rows[k], q_cols()))) by {
        let (a, b, i) = lemma_joined_witness(sv, db, k);
        lemma_keys_joined(sv, db, ps, a, b, i);
    }
}

/// The SUM argument agrees with the normal form on every joined row.
pub proof fn lemma_args_agree(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db),
    ensures args_agree(db, q_rows(db), q_cols(), q_aggs(), q_spec(sv, ps)),
{
    let rows = q_rows(db);
    let g = q_spec(sv, ps);
    assert forall|k: int| 0 <= k < rows.len() && (g.qual)(proj(#[trigger] rows[k], q_cols())) implies
        agg_args(db, rows[k], q_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[k], q_cols()))) by {
        let (a, b, i) = lemma_joined_witness(sv, db, k);
        let r = joined(db, a, b, i);
        lemma_joined_values(sv, db, a, b, i);
        lemma_joined_normal_form(sv, db, ps, a, b, i);
        let rs = agg_arg_results(db, r, q_aggs());
        lemma_agg_arg_results_index(db, r, q_aggs());
        let x = proj(r, q_cols());
        let vs = arg_vals(g, x);
        assert(vs =~= seq![Val::Num { coeff: lq(sv)[i] as int, scale: 2 }]);
        assert(rs[0] == eval_expr(db, r, Expr::Col(21)));
        lemma_collect_all(rs, vs);
    }
}

/// Every projected joined row's key is `(text, int, int, date, numeric scale 2)`.
pub proof fn lemma_key_types(sv: StoresView, db: Database, ps: Seq<Literal>, m: int)
    requires bound_db(sv, db), 0 <= m < q_xs(db).len(),
    ensures ({
        let k = (q_spec(sv, ps).key)(q_xs(db)[m]);
        &&& k.len() == 5
        &&& k[0] is Text && k[1] is Int && k[2] is Int && k[3] is Date
        &&& k[4] is Num && k[4]->Num_scale == 2
    }),
{
    let rows = q_rows(db);
    lemma_proj_all_index(rows, q_cols());
    let (a, b, i) = lemma_joined_witness(sv, db, m);
    lemma_joined_normal_form(sv, db, ps, a, b, i);
}

/// SQL "not distinct" is equality on the keys of the joined rows.
pub proof fn lemma_keys_exact(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db),
    ensures keys_exact(q_spec(sv, ps), q_xs(db)),
{
    let g = q_spec(sv, ps);
    let xs = q_xs(db);
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        lemma_key_types(sv, db, ps, a);
        lemma_key_types(sv, db, ps, b);
        let (ka, kb) = ((g.key)(xs[a]), (g.key)(xs[b]));
        assert forall|t: int| 0 <= t < ka.len() implies same_exact_type(#[trigger] ka[t], kb[t]) by {
            if t == 0 {} else if t == 1 {} else if t == 2 {} else if t == 3 {} else {}
        }
        lemma_row_exact(ka, kb);
    }
}

/// The GROUP BY rows: the full row of every group key, in first-occurrence order.
pub open spec fn q_group_rows(sv: StoresView, ps: Seq<Literal>, db: Database) -> Seq<Row> {
    gkeys(q_spec(sv, ps), q_xs(db)).map_values(|k: Row| full_row(q_spec(sv, ps), q_xs(db), k))
}

/// The GROUP BY node evaluates to the groups' full rows.
proof fn lemma_group_eval(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), small(sv), param_domain(ps), group_caps(q_spec(sv, ps), q_xs(db)),
    ensures eval_query(db, Seq::empty(), q_body(ps)) == Ok::<Relation, SqlError>(q_group_rows(sv, ps, db)),
{
    let rows = q_rows(db);
    let cols = q_cols();
    let g = q_spec(sv, ps);
    lemma_eval_from(sv, db);
    lemma_pred_agrees(sv, db, ps);
    lemma_filter_rows(db, q_from(), rows, cols, q_pred(ps), g);
    lemma_keys_agree(sv, db, ps);
    lemma_args_agree(sv, db, ps);
    lemma_keys_exact(sv, db, ps);
    assert(aggs_match(q_aggs(), g)) by {
        assert(agg_matches(q_aggs()[0], g.aggs[0]));
    }
    lemma_group_query(db, rows, cols, q_filter(ps), q_group_keys(), q_aggs(), g);
}

/// The result rows are the GROUP BY rows (the output keeps all six columns).
proof fn lemma_result_rows(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db),
    ensures result_rows(q_spec(sv, ps), q_xs(db)) == q_group_rows(sv, ps, db),
{
    let g = q_spec(sv, ps);
    let xs = q_xs(db);
    let gk = gkeys(g, xs);
    lemma_gkeys(g, xs);
    assert forall|t: int| 0 <= t < gk.len() implies #[trigger] out_row(g, xs, gk[t]) == full_row(g, xs, gk[t]) by {
        assert(gk.contains(gk[t]));
        lemma_gkeys_witness(g, xs, gk[t]);
        let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], gk[t]);
        lemma_key_types(sv, db, ps, m);
        let fr = full_row(g, xs, gk[t]);
        assert(agg_outs(g, xs, gk[t]).len() == 1);
        assert(fr.len() == 6);
        assert forall|m2: int| 0 <= m2 < g.outs.len() implies #[trigger] g.outs[m2] == m2 by {
            if m2 == 0 {} else if m2 == 1 {} else if m2 == 2 {} else if m2 == 3 {} else if m2 == 4 {} else {}
        }
        lemma_select_identity(fr, g.outs);
    }
    assert(result_rows(g, xs) =~= q_group_rows(sv, ps, db));
}

/// The body of the statement evaluates to the normal form's result rows (inside the arithmetic domain of the
/// groups, `group_caps`).
pub proof fn lemma_denotation(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), small(sv), param_domain(ps), group_caps(q_spec(sv, ps), q_xs(db)),
    ensures denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(result_rows(q_spec(sv, ps), q_xs(db))),
{
    lemma_query_shape(ps);
    lemma_group_eval(sv, db, ps);
    lemma_result_rows(sv, db, ps);
}

} // verus!
