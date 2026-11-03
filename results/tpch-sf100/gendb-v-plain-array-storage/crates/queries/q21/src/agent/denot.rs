//! The statement's body in the accumulator normal form of `link::query` (`lemma_body_ok`), and its error when a
//! COUNT leaves int8 (`lemma_body_count_error`).
//!
//! FROM is the left-deep product `((supplier x lineitem) x orders) x nation` of the database tables (`q_rows`); every
//! joined row is `S[a] ++ L[i] ++ O[b] ++ N[n]` (`lemma_joined_witness`), whose read columns have the stored values
//! (`lemma_joined_values`). On such a row the WHERE condition, with its two correlated subqueries over `lineitem`,
//! evaluates without error to `q_qual` of the projection (`lemma_pred_joined`): the subqueries are `ex2` / `ex3` of
//! the lineitem row (`lemma_exists2_row`, `lemma_exists3_row`). The group key is `s_name`, the one aggregate
//! COUNT(*). The keys are texts, so SQL "not distinct" is equality on them, and `link::query::lemma_group_query`
//! (inside `group_caps`) gives `result_rows`.
//!
//! Joined row positions: `S 0..7` (s_suppkey 0, s_name 1, s_nationkey 3), `L 7..23` (l_orderkey 7, l_suppkey 9,
//! l_commitdate 18, l_receiptdate 19), `O 23..32` (o_orderkey 23, o_orderstatus 25), `N 32..36` (n_nationkey 32,
//! n_name 33). Projected row `x` (`q_cols`): `x[0] s_suppkey, x[1] s_name, x[2] s_nationkey, x[3] l_orderkey,
//! x[4] l_suppkey, x[5] l_commitdate, x[6] l_receiptdate, x[7] o_orderkey, x[8] o_orderstatus, x[9] n_nationkey,
//! x[10] n_name`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::order::*;
use crate::spec::limits::int8_max;
use crate::spec::equality::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::source_check::date32_val;
use crate::exec::relational::domain::*;
use crate::query::{query_spec_at, param_domain};
use crate::link::query::*;
use crate::link::expr::{lemma_expr_col, lemma_expr_text, lemma_compare_int, lemma_compare_date, lemma_pred_cmp,
    lemma_pred_text_cmp, lemma_pred_and, lemma_pred_not, int_cmp, text_cmp};
use crate::link::exists::lemma_exists_filter_table;
use crate::link::capacity::*;
use crate::link::join::lemma_product_index;
use crate::bridge::equality::same_exact_type;
use crate::bridge::collect::lemma_collect_all;
use crate::agent::cols::*;
use crate::agent::nf::*;

verus! {

// ------------------------------------------------------------------------------------------------ the AST

/// `l2.l_orderkey = l1.l_orderkey AND l2.l_suppkey <> l1.l_suppkey` (outer row, then the `l2` row at 36..52).
pub open spec fn p_other() -> Pred {
    Pred::And(
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(36), b: Expr::Col(7) }),
        Box::new(Pred::Cmp { op: CmpOp::Ne, a: Expr::Col(38), b: Expr::Col(9) }),
    )
}

/// `... AND l3.l_receiptdate > l3.l_commitdate`.
pub open spec fn p_other_late() -> Pred {
    Pred::And(Box::new(p_other()), Box::new(Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(48), b: Expr::Col(47) }))
}

/// `EXISTS (SELECT * FROM lineitem l2 WHERE ..)`.
pub open spec fn p_ex2() -> Pred {
    Pred::Exists(Box::new(Query::Filter { pred: p_other(), input: Box::new(Query::Table(0)) }))
}

/// `EXISTS (SELECT * FROM lineitem l3 WHERE ..)` (under NOT).
pub open spec fn p_ex3() -> Pred {
    Pred::Exists(Box::new(Query::Filter { pred: p_other_late(), input: Box::new(Query::Table(0)) }))
}

/// `s_suppkey = l1.l_suppkey AND o_orderkey = l1.l_orderkey AND o_orderstatus = 'F' AND l1.l_receiptdate > l1.l_commitdate`.
pub open spec fn p_a() -> Pred {
    let n4 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) };
    let n7 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(23), b: Expr::Col(7) };
    let n8 = Pred::And(Box::new(n4), Box::new(n7));
    let n12 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(25), b: Expr::Lit(Literal::Text(seq![70u8])) };
    let n13 = Pred::And(Box::new(n8), Box::new(n12));
    let n16 = Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(19), b: Expr::Col(18) };
    Pred::And(Box::new(n13), Box::new(n16))
}

/// `s_nationkey = n_nationkey`.
pub open spec fn p_nat() -> Pred { Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(3), b: Expr::Col(32) } }

/// `n_name = $1`.
pub open spec fn p_name(p: Literal) -> Pred { Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(33), b: Expr::Lit(p) } }

/// The WHERE (left-nested ANDs, as the statement writes them).
pub open spec fn q_pred(p: Literal) -> Pred {
    let n28 = Pred::And(Box::new(p_a()), Box::new(p_ex2()));
    let n44 = Pred::And(Box::new(n28), Box::new(Pred::Not(Box::new(p_ex3()))));
    let n48 = Pred::And(Box::new(n44), Box::new(p_nat()));
    Pred::And(Box::new(n48), Box::new(p_name(p)))
}

/// FROM supplier, lineitem l1, orders, nation.
pub open spec fn q_from() -> Query {
    Query::Product {
        left: Box::new(Query::Product {
            left: Box::new(Query::Product { left: Box::new(Query::Table(5)), right: Box::new(Query::Table(0)) }),
            right: Box::new(Query::Table(1)),
        }),
        right: Box::new(Query::Table(6)),
    }
}

pub open spec fn q_filter(p: Literal) -> Query { Query::Filter { pred: q_pred(p), input: Box::new(q_from()) } }

pub open spec fn q_keys() -> Seq<Expr> { seq![Expr::Col(1)] }

pub open spec fn q_aggs() -> Seq<Agg> { seq![Agg::CountStar] }

pub open spec fn q_body(p: Literal) -> Query {
    Query::GroupBy { keys: q_keys(), aggs: q_aggs(), input: Box::new(q_filter(p)) }
}

/// ORDER BY numwait DESC, s_name.
pub open spec fn q_order_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 1, desc: true, nulls_first: true }, OrderKey { col: 0, desc: false, nulls_first: false }]
}

/// The statement is this AST with LIMIT 100.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures query_spec_at(ps) == (OrderedQuery { body: q_body(ps[0]), keys: q_order_keys(), limit: Some(100nat), offset: 0nat }),
{
}

// ------------------------------------------------------------------------------------------------ joined rows

/// FROM's rows: the left-deep product of the database tables.
pub open spec fn q_rows(db: Database) -> Seq<Row> {
    product_rows(product_rows(product_rows(db.tables[5], db.tables[0]), db.tables[1]), db.tables[6])
}

/// Positions of the eleven read columns in a joined row (opaque: its elements are stated by `lemma_q_cols`).
#[verifier::opaque]
pub open spec fn q_cols() -> Seq<nat> { seq![0nat, 1, 3, 7, 9, 18, 19, 23, 25, 32, 33] }

pub proof fn lemma_q_cols()
    ensures
        q_cols().len() == 11,
        q_cols()[0] == 0, q_cols()[1] == 1, q_cols()[2] == 3, q_cols()[3] == 7, q_cols()[4] == 9, q_cols()[5] == 18,
        q_cols()[6] == 19, q_cols()[7] == 23, q_cols()[8] == 25, q_cols()[9] == 32, q_cols()[10] == 33,
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
    assert(eval_query(db, e, Query::Table(5)) == Ok::<Relation, SqlError>(db.tables[5]));
    assert(eval_query(db, e, Query::Table(0)) == Ok::<Relation, SqlError>(db.tables[0]));
    assert(eval_query(db, e, Query::Table(1)) == Ok::<Relation, SqlError>(db.tables[1]));
    assert(eval_query(db, e, Query::Table(6)) == Ok::<Relation, SqlError>(db.tables[6]));
    let sl = Query::Product { left: Box::new(Query::Table(5)), right: Box::new(Query::Table(0)) };
    assert(eval_query(db, e, sl) == Ok::<Relation, SqlError>(product_rows(db.tables[5], db.tables[0])));
    let slo = Query::Product { left: Box::new(sl), right: Box::new(Query::Table(1)) };
    assert(eval_query(db, e, slo) == Ok::<Relation, SqlError>(product_rows(product_rows(db.tables[5], db.tables[0]), db.tables[1])));
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

/// Joined row `S[a] ++ L[i] ++ O[b] ++ N[n]` (opaque: its values are stated by `lemma_joined_values`).
#[verifier::opaque]
pub open spec fn joined(db: Database, a: int, i: int, b: int, n: int) -> Row {
    db.tables[5][a] + db.tables[0][i] + db.tables[1][b] + db.tables[6][n]
}

/// Row indices of a joined row: supplier, lineitem, orders, nation.
pub struct JRow { pub a: int, pub i: int, pub b: int, pub n: int }

pub open spec fn jrow_ok(sv: StoresView, w: JRow) -> bool {
    0 <= w.a < n_s(sv) && 0 <= w.i < n_l(sv) && 0 <= w.b < n_o(sv) && 0 <= w.n < n_n(sv)
}

/// Every joined row is `joined(db, a, i, b, n)` for some rows of the four tables.
pub proof fn lemma_joined_witness(sv: StoresView, db: Database, k: int) -> (w: JRow)
    requires bound_db(sv, db), 0 <= k < q_rows(db).len(),
    ensures jrow_ok(sv, w), q_rows(db)[k] == joined(db, w.a, w.i, w.b, w.n),
{
    lemma_parts_shape(sv, db);
    let sl = product_rows(db.tables[5], db.tables[0]);
    let slo = product_rows(sl, db.tables[1]);
    let (y, n) = lemma_product_witness(slo, db.tables[6], k);
    let (x, b) = lemma_product_witness(sl, db.tables[1], y);
    let (a, i) = lemma_product_witness(db.tables[5], db.tables[0], x);
    reveal(joined);
    JRow { a, i, b, n }
}

/// The values a joined row has at the positions the statement reads.
pub open spec fn joined_vals_ok(sv: StoresView, r: Row, w: JRow) -> bool {
    let (a, i, b, n) = (w.a, w.i, w.b, w.n);
    &&& r.len() == 36
    &&& r[0] == Val::Int(skey(sv)[a] as int)
    &&& r[1] == Val::Text(sname(sv, a))
    &&& r[3] == Val::Int(snk(sv)[a] as int)
    &&& r[7] == Val::Int(lk(sv)[i] as int)
    &&& r[9] == Val::Int(ls(sv)[i] as int)
    &&& r[18] == date32_val(lc(sv)[i])
    &&& r[19] == date32_val(lr(sv)[i])
    &&& r[23] == Val::Int(ok(sv)[b] as int)
    &&& r[25] == Val::Text(ostat(sv, b))
    &&& r[32] == Val::Int(nkey(sv)[n] as int)
    &&& r[33] == Val::Text(nname(sv, n))
}

pub proof fn lemma_joined_values(sv: StoresView, db: Database, w: JRow)
    requires bound_db(sv, db), jrow_ok(sv, w),
    ensures joined_vals_ok(sv, joined(db, w.a, w.i, w.b, w.n), w),
{
    let (a, i, b, n) = (w.a, w.i, w.b, w.n);
    reveal(joined);
    lemma_parts_shape(sv, db);
    lemma_supplier_row(sv, db, a);
    lemma_lineitem_row(sv, db, i);
    lemma_orders_row(sv, db, b);
    lemma_nation_row(sv, db, n);
    let s = db.tables[5][a];
    let l = db.tables[0][i];
    let o = db.tables[1][b];
    let t = db.tables[6][n];
    let sl = s + l;
    let slo = sl + o;
    let r = slo + t;
    assert(sl[0] == s[0] && sl[1] == s[1] && sl[3] == s[3]);
    assert(sl[7] == l[0] && sl[9] == l[2] && sl[18] == l[11] && sl[19] == l[12]);
    assert(slo[0] == sl[0] && slo[1] == sl[1] && slo[3] == sl[3] && slo[7] == sl[7] && slo[9] == sl[9]);
    assert(slo[18] == sl[18] && slo[19] == sl[19]);
    assert(slo[23] == o[0] && slo[25] == o[2]);
    assert(r[0] == slo[0] && r[1] == slo[1] && r[3] == slo[3] && r[7] == slo[7] && r[9] == slo[9]);
    assert(r[18] == slo[18] && r[19] == slo[19] && r[23] == slo[23] && r[25] == slo[25]);
    assert(r[32] == t[0] && r[33] == t[1]);
}

/// The projection of a joined row onto the read columns.
pub proof fn lemma_joined_proj(r: Row)
    requires r.len() == 36,
    ensures proj(r, q_cols()) == seq![r[0], r[1], r[3], r[7], r[9], r[18], r[19], r[23], r[25], r[32], r[33]],
{
    lemma_q_cols();
    assert(proj(r, q_cols()) =~= seq![r[0], r[1], r[3], r[7], r[9], r[18], r[19], r[23], r[25], r[32], r[33]]);
}

// ------------------------------------------------------------------------------------------------ the normal form

/// `v1 > v2` for two dates.
pub open spec fn date_gt(v1: Val, v2: Val) -> bool {
    match (v1, v2) { (Val::Date(d1), Val::Date(d2)) => d1 > d2, _ => false }
}

/// Lineitem row `j` has order key value `ko` and a supplier key value other than `ks`.
pub open spec fn other_v(sv: StoresView, j: int, ko: Val, ks: Val) -> bool {
    Val::Int(lk(sv)[j] as int) == ko && Val::Int(ls(sv)[j] as int) != ks
}

/// The EXISTS over lineitem for an outer row with order key value `ko` and supplier key value `ks`.
pub open spec fn exv2(sv: StoresView, ko: Val, ks: Val) -> bool {
    exists|j: int| 0 <= j < n_l(sv) && #[trigger] other_v(sv, j, ko, ks)
}

/// The NOT EXISTS's subquery for an outer row with order key value `ko` and supplier key value `ks`.
pub open spec fn exv3(sv: StoresView, ko: Val, ks: Val) -> bool {
    exists|j: int| 0 <= j < n_l(sv) && #[trigger] other_v(sv, j, ko, ks) && late(sv, j)
}

/// WHERE on a projected row `x` (two-valued: every operand is a non-NULL value of its column's type).
pub open spec fn q_qual(sv: StoresView, p: Seq<u8>, x: Row) -> bool {
    &&& x[0] == x[4]
    &&& x[7] == x[3]
    &&& x[8] == Val::Text(seq![70u8])
    &&& date_gt(x[6], x[5])
    &&& exv2(sv, x[3], x[4])
    &&& !exv3(sv, x[3], x[4])
    &&& x[2] == x[9]
    &&& x[10] == Val::Text(p)
}

/// GROUP BY s_name.
pub open spec fn q_key(x: Row) -> Row { seq![x[1]] }

/// The statement's normal form at parameter bytes `p`: COUNT(*) per `s_name`; output `s_name, numwait`.
pub open spec fn q_spec(sv: StoresView, p: Seq<u8>) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| q_qual(sv, p, x),
        key: |x: Row| q_key(x),
        arg: |j: int, x: Row| 0,
        aggs: seq![AggKind::Count],
        outs: seq![0nat, 1nat],
        grouped: true,
    }
}

/// The joined row `w` qualifies (in stored terms).
pub open spec fn jqual(sv: StoresView, p: Seq<u8>, w: JRow) -> bool {
    &&& skey(sv)[w.a] == ls(sv)[w.i]
    &&& ok(sv)[w.b] == lk(sv)[w.i]
    &&& fstat(sv, w.b)
    &&& lq(sv, w.i)
    &&& nhit(sv, p, snk(sv)[w.a] as int, w.n)
}

/// `exv2` / `exv3` of a lineitem row's own key values are `ex2` / `ex3`.
pub proof fn lemma_exv(sv: StoresView, i: int)
    ensures
        exv2(sv, Val::Int(lk(sv)[i] as int), Val::Int(ls(sv)[i] as int)) == ex2(sv, i),
        exv3(sv, Val::Int(lk(sv)[i] as int), Val::Int(ls(sv)[i] as int)) == ex3(sv, i),
{
    let (ko, ks) = (Val::Int(lk(sv)[i] as int), Val::Int(ls(sv)[i] as int));
    if exv2(sv, ko, ks) {
        let j = choose|j: int| 0 <= j < n_l(sv) && #[trigger] other_v(sv, j, ko, ks);
        assert(other_at(sv, i, j));
    }
    if ex2(sv, i) {
        let j = choose|j: int| 0 <= j < n_l(sv) && #[trigger] other_at(sv, i, j);
        assert(other_v(sv, j, ko, ks));
    }
    if exv3(sv, ko, ks) {
        let j = choose|j: int| 0 <= j < n_l(sv) && #[trigger] other_v(sv, j, ko, ks) && late(sv, j);
        assert(other_at(sv, i, j));
    }
    if ex3(sv, i) {
        let j = choose|j: int| 0 <= j < n_l(sv) && #[trigger] other_at(sv, i, j) && late(sv, j);
        assert(other_v(sv, j, ko, ks));
    }
}

/// The normal form on a joined row of the database: qualification and key.
pub proof fn lemma_joined_normal_form(sv: StoresView, db: Database, p: Seq<u8>, w: JRow)
    requires bound_db(sv, db), jrow_ok(sv, w),
    ensures ({
        let x = proj(joined(db, w.a, w.i, w.b, w.n), q_cols());
        let g = q_spec(sv, p);
        &&& (g.qual)(x) == jqual(sv, p, w)
        &&& (g.key)(x) == seq![Val::Text(sname(sv, w.a))]
    }),
{
    let r = joined(db, w.a, w.i, w.b, w.n);
    lemma_joined_values(sv, db, w);
    lemma_joined_proj(r);
    lemma_exv(sv, w.i);
    let x = proj(r, q_cols());
    assert(x[6] == date32_val(lr(sv)[w.i]) && x[5] == date32_val(lc(sv)[w.i]));
    assert(date_gt(x[6], x[5]) == late(sv, w.i));
    assert(q_key(x) =~= seq![Val::Text(sname(sv, w.a))]);
}

// ------------------------------------------------------------------------------------------------ per-row evaluation

/// The inner condition of the EXISTS on joined row `r` (lineitem values of row `w.i`) and lineitem row `j`.
proof fn lemma_other_row(sv: StoresView, db: Database, r: Row, w: JRow, j: int)
    requires bound_db(sv, db), joined_vals_ok(sv, r, w), 0 <= j < n_l(sv),
    ensures
        eval_pred(db, r + db.tables[0][j], p_other()) == Ok::<Truth, SqlError>(truth_of(other_at(sv, w.i, j))),
        eval_pred(db, r + db.tables[0][j], p_other_late())
            == Ok::<Truth, SqlError>(truth_of(other_at(sv, w.i, j) && late(sv, j))),
{
    lemma_parts_shape(sv, db);
    lemma_lineitem_row(sv, db, j);
    let lrow = db.tables[0][j];
    let env = r + lrow;
    assert(env[36] == lrow[0] && env[38] == lrow[2] && env[47] == lrow[11] && env[48] == lrow[12]);
    assert(env[7] == r[7] && env[9] == r[9]);
    lemma_expr_col(db, env, 36);
    lemma_expr_col(db, env, 7);
    lemma_expr_col(db, env, 38);
    lemma_expr_col(db, env, 9);
    lemma_expr_col(db, env, 47);
    lemma_expr_col(db, env, 48);
    let (k2, k1) = (lk(sv)[j] as int, lk(sv)[w.i] as int);
    let (s2, s1) = (ls(sv)[j] as int, ls(sv)[w.i] as int);
    lemma_compare_int(k2, k1);
    lemma_compare_int(s2, s1);
    let eq = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(36), b: Expr::Col(7) };
    let ne = Pred::Cmp { op: CmpOp::Ne, a: Expr::Col(38), b: Expr::Col(9) };
    lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(36), Expr::Col(7), env[36], env[7], k2, k1);
    lemma_pred_cmp(db, env, CmpOp::Ne, Expr::Col(38), Expr::Col(9), env[38], env[9], s2, s1);
    lemma_pred_and(db, env, eq, ne, k2 == k1, s2 != s1);
    let (x, y) = (lr(sv)[j] as int - 10957, lc(sv)[j] as int - 10957);
    lemma_compare_date(x, y);
    lemma_pred_cmp(db, env, CmpOp::Gt, Expr::Col(48), Expr::Col(47), env[48], env[47], x, y);
    lemma_pred_and(db, env, p_other(), Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(48), b: Expr::Col(47) },
        k2 == k1 && s2 != s1, x > y);
}

/// The EXISTS on a joined row: `ex2` of its lineitem row.
pub proof fn lemma_exists2_row(sv: StoresView, db: Database, r: Row, w: JRow)
    requires bound_db(sv, db), joined_vals_ok(sv, r, w), 0 <= w.i < n_l(sv),
    ensures eval_pred(db, r, p_ex2()) == Ok::<Truth, SqlError>(truth_of(ex2(sv, w.i))),
{
    hide(eval_pred);
    lemma_parts_shape(sv, db);
    let rows = db.tables[0];
    assert forall|j: int| 0 <= j < rows.len() implies #[trigger] eval_pred(db, r + rows[j], p_other()) is Ok by {
        lemma_other_row(sv, db, r, w, j);
    }
    lemma_exists_filter_table(db, r, p_other(), 0);
    if exists|j: int| 0 <= j < rows.len() && #[trigger] eval_pred(db, r + rows[j], p_other()) == Ok::<Truth, SqlError>(Truth::True) {
        let j = choose|j: int| 0 <= j < rows.len() && #[trigger] eval_pred(db, r + rows[j], p_other()) == Ok::<Truth, SqlError>(Truth::True);
        lemma_other_row(sv, db, r, w, j);
        assert(other_at(sv, w.i, j));
    }
    if ex2(sv, w.i) {
        let j = choose|j: int| 0 <= j < n_l(sv) && #[trigger] other_at(sv, w.i, j);
        lemma_other_row(sv, db, r, w, j);
        assert(eval_pred(db, r + rows[j], p_other()) == Ok::<Truth, SqlError>(Truth::True));
    }
}

/// The NOT EXISTS's subquery on a joined row: `ex3` of its lineitem row.
pub proof fn lemma_exists3_row(sv: StoresView, db: Database, r: Row, w: JRow)
    requires bound_db(sv, db), joined_vals_ok(sv, r, w), 0 <= w.i < n_l(sv),
    ensures eval_pred(db, r, p_ex3()) == Ok::<Truth, SqlError>(truth_of(ex3(sv, w.i))),
{
    hide(eval_pred);
    lemma_parts_shape(sv, db);
    let rows = db.tables[0];
    assert forall|j: int| 0 <= j < rows.len() implies #[trigger] eval_pred(db, r + rows[j], p_other_late()) is Ok by {
        lemma_other_row(sv, db, r, w, j);
    }
    lemma_exists_filter_table(db, r, p_other_late(), 0);
    if exists|j: int| 0 <= j < rows.len() && #[trigger] eval_pred(db, r + rows[j], p_other_late()) == Ok::<Truth, SqlError>(Truth::True) {
        let j = choose|j: int| 0 <= j < rows.len() && #[trigger] eval_pred(db, r + rows[j], p_other_late()) == Ok::<Truth, SqlError>(Truth::True);
        lemma_other_row(sv, db, r, w, j);
        assert(other_at(sv, w.i, j) && late(sv, j));
    }
    if ex3(sv, w.i) {
        let j = choose|j: int| 0 <= j < n_l(sv) && #[trigger] other_at(sv, w.i, j) && late(sv, j);
        lemma_other_row(sv, db, r, w, j);
        assert(eval_pred(db, r + rows[j], p_other_late()) == Ok::<Truth, SqlError>(Truth::True));
    }
}

/// The first four conjuncts on a joined row.
proof fn lemma_pred_a_joined(sv: StoresView, db: Database, r: Row, w: JRow)
    requires joined_vals_ok(sv, r, w),
    ensures eval_pred(db, r, p_a()) == Ok::<Truth, SqlError>(truth_of(
        skey(sv)[w.a] == ls(sv)[w.i] && ok(sv)[w.b] == lk(sv)[w.i] && ostat(sv, w.b) == seq![70u8] && late(sv, w.i))),
{
    lemma_expr_col(db, r, 0);
    lemma_expr_col(db, r, 9);
    lemma_expr_col(db, r, 23);
    lemma_expr_col(db, r, 7);
    lemma_expr_col(db, r, 25);
    lemma_expr_col(db, r, 19);
    lemma_expr_col(db, r, 18);
    let (x0, x9, x23, x7) = (skey(sv)[w.a] as int, ls(sv)[w.i] as int, ok(sv)[w.b] as int, lk(sv)[w.i] as int);
    lemma_compare_int(x0, x9);
    lemma_compare_int(x23, x7);
    let n4 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) };
    let n7 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(23), b: Expr::Col(7) };
    lemma_pred_cmp(db, r, CmpOp::Eq, Expr::Col(0), Expr::Col(9), r[0], r[9], x0, x9);
    lemma_pred_cmp(db, r, CmpOp::Eq, Expr::Col(23), Expr::Col(7), r[23], r[7], x23, x7);
    lemma_pred_and(db, r, n4, n7, x0 == x9, x23 == x7);
    let n8 = Pred::And(Box::new(n4), Box::new(n7));
    let f = seq![70u8];
    lemma_expr_text(db, r, f);
    let n12 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(25), b: Expr::Lit(Literal::Text(f)) };
    lemma_pred_text_cmp(db, r, CmpOp::Eq, Expr::Col(25), Expr::Lit(Literal::Text(f)), ostat(sv, w.b), f);
    lemma_pred_and(db, r, n8, n12, x0 == x9 && x23 == x7, ostat(sv, w.b) == f);
    let n13 = Pred::And(Box::new(n8), Box::new(n12));
    let (d19, d18) = (lr(sv)[w.i] as int - 10957, lc(sv)[w.i] as int - 10957);
    lemma_compare_date(d19, d18);
    let n16 = Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(19), b: Expr::Col(18) };
    lemma_pred_cmp(db, r, CmpOp::Gt, Expr::Col(19), Expr::Col(18), r[19], r[18], d19, d18);
    lemma_pred_and(db, r, n13, n16, x0 == x9 && x23 == x7 && ostat(sv, w.b) == f, d19 > d18);
}

/// `s_nationkey = n_nationkey` on a joined row.
proof fn lemma_pred_nat_joined(sv: StoresView, db: Database, r: Row, w: JRow)
    requires joined_vals_ok(sv, r, w),
    ensures eval_pred(db, r, p_nat()) == Ok::<Truth, SqlError>(truth_of(snk(sv)[w.a] as int == nkey(sv)[w.n] as int)),
{
    lemma_expr_col(db, r, 3);
    lemma_expr_col(db, r, 32);
    let (x3, x32) = (snk(sv)[w.a] as int, nkey(sv)[w.n] as int);
    lemma_compare_int(x3, x32);
    lemma_pred_cmp(db, r, CmpOp::Eq, Expr::Col(3), Expr::Col(32), r[3], r[32], x3, x32);
}

/// `n_name = $1` on a joined row.
proof fn lemma_pred_name_joined(sv: StoresView, db: Database, ps: Seq<Literal>, r: Row, w: JRow)
    requires param_domain(ps), joined_vals_ok(sv, r, w),
    ensures eval_pred(db, r, p_name(ps[0])) == Ok::<Truth, SqlError>(truth_of(nname(sv, w.n) == ps[0]->Text_0)),
{
    let p = ps[0];
    lemma_expr_col(db, r, 33);
    assert(eval_expr(db, r, Expr::Lit(p)) == Ok::<Val, SqlError>(Val::Text(p->Text_0)));
    lemma_pred_text_cmp(db, r, CmpOp::Eq, Expr::Col(33), Expr::Lit(p), nname(sv, w.n), p->Text_0);
}

/// The WHERE condition on a joined row.
pub proof fn lemma_pred_joined(sv: StoresView, db: Database, ps: Seq<Literal>, r: Row, w: JRow)
    requires bound_db(sv, db), param_domain(ps), joined_vals_ok(sv, r, w), jrow_ok(sv, w),
    ensures eval_pred(db, r, q_pred(ps[0])) == Ok::<Truth, SqlError>(truth_of(jqual(sv, ps[0]->Text_0, w))),
{
    hide(eval_pred);
    let p = ps[0];
    let pb = p->Text_0;
    lemma_pred_a_joined(sv, db, r, w);
    lemma_exists2_row(sv, db, r, w);
    lemma_exists3_row(sv, db, r, w);
    let ea = skey(sv)[w.a] == ls(sv)[w.i] && ok(sv)[w.b] == lk(sv)[w.i] && ostat(sv, w.b) == seq![70u8] && late(sv, w.i);
    lemma_pred_and(db, r, p_a(), p_ex2(), ea, ex2(sv, w.i));
    let n28 = Pred::And(Box::new(p_a()), Box::new(p_ex2()));
    lemma_pred_not(db, r, p_ex3(), ex3(sv, w.i));
    lemma_pred_and(db, r, n28, Pred::Not(Box::new(p_ex3())), ea && ex2(sv, w.i), !ex3(sv, w.i));
    let n44 = Pred::And(Box::new(n28), Box::new(Pred::Not(Box::new(p_ex3()))));
    let (x3, x32) = (snk(sv)[w.a] as int, nkey(sv)[w.n] as int);
    lemma_pred_nat_joined(sv, db, r, w);
    lemma_pred_and(db, r, n44, p_nat(), ea && ex2(sv, w.i) && !ex3(sv, w.i), x3 == x32);
    let n48 = Pred::And(Box::new(n44), Box::new(p_nat()));
    lemma_pred_name_joined(sv, db, ps, r, w);
    lemma_pred_and(db, r, n48, p_name(p), ea && ex2(sv, w.i) && !ex3(sv, w.i) && x3 == x32, nname(sv, w.n) == pb);
}

/// The group key on a joined row.
pub proof fn lemma_keys_joined(db: Database, r: Row)
    requires r.len() == 36,
    ensures eval_exprs(db, r, q_keys()) == Ok::<Row, SqlError>(seq![r[1]]),
{
    let idxs = seq![1nat];
    assert(col_exprs(idxs) =~= q_keys());
    lemma_eval_cols(db, r, idxs);
    assert(select(r, idxs) =~= seq![r[1]]);
}

/// The COUNT(*) argument on any row (none: NULL stands in).
pub proof fn lemma_args_any(db: Database, r: Row, sv: StoresView, p: Seq<u8>, x: Row)
    ensures agg_args(db, r, q_aggs()) == Ok::<Row, SqlError>(arg_vals(q_spec(sv, p), x)),
{
    let g = q_spec(sv, p);
    let rs = agg_arg_results(db, r, q_aggs());
    let vs = arg_vals(g, x);
    lemma_agg_arg_results_index(db, r, q_aggs());
    assert(vs =~= seq![Val::Null]);
    assert(rs[0] == agg_arg(db, r, Agg::CountStar));
    lemma_collect_all(rs, vs);
}

// ------------------------------------------------------------------------------------------------ agreement

pub open spec fn pb_of(ps: Seq<Literal>) -> Seq<u8> { ps[0]->Text_0 }

/// WHERE agrees with the normal form on every joined row.
pub proof fn lemma_pred_agrees(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps),
    ensures pred_agrees(db, q_rows(db), q_cols(), q_pred(ps[0]), q_spec(sv, pb_of(ps))),
{
    let rows = q_rows(db);
    let g = q_spec(sv, pb_of(ps));
    assert forall|k: int| 0 <= k < rows.len() implies
        eval_pred(db, #[trigger] rows[k], q_pred(ps[0])) == Ok::<Truth, SqlError>(truth_of((g.qual)(proj(rows[k], q_cols())))) by {
        let w = lemma_joined_witness(sv, db, k);
        let r = joined(db, w.a, w.i, w.b, w.n);
        lemma_joined_values(sv, db, w);
        lemma_pred_joined(sv, db, ps, r, w);
        lemma_joined_normal_form(sv, db, pb_of(ps), w);
    }
}

/// GROUP BY keys agree with the normal form on every joined row.
pub proof fn lemma_keys_agree(sv: StoresView, db: Database, p: Seq<u8>)
    requires bound_db(sv, db),
    ensures keys_agree(db, q_rows(db), q_cols(), q_keys(), q_spec(sv, p)),
{
    let rows = q_rows(db);
    let g = q_spec(sv, p);
    assert forall|k: int| 0 <= k < rows.len() && (g.qual)(proj(#[trigger] rows[k], q_cols())) implies
        eval_exprs(db, rows[k], q_keys()) == Ok::<Row, SqlError>((g.key)(proj(rows[k], q_cols()))) by {
        let w = lemma_joined_witness(sv, db, k);
        let r = joined(db, w.a, w.i, w.b, w.n);
        lemma_joined_values(sv, db, w);
        lemma_keys_joined(db, r);
        lemma_joined_proj(r);
        assert(q_key(proj(r, q_cols())) =~= seq![r[1]]);
    }
}

/// The COUNT(*) argument agrees with the normal form on every row.
pub proof fn lemma_args_agree(sv: StoresView, db: Database, p: Seq<u8>)
    ensures args_agree(db, q_rows(db), q_cols(), q_aggs(), q_spec(sv, p)),
{
    let rows = q_rows(db);
    let g = q_spec(sv, p);
    assert forall|k: int| 0 <= k < rows.len() && (g.qual)(proj(#[trigger] rows[k], q_cols())) implies
        agg_args(db, rows[k], q_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[k], q_cols()))) by {
        lemma_args_any(db, rows[k], sv, p, proj(rows[k], q_cols()));
    }
}

/// The key of every projected joined row is one text.
pub proof fn lemma_key_types(sv: StoresView, db: Database, p: Seq<u8>, m: int)
    requires bound_db(sv, db), 0 <= m < q_xs(db).len(),
    ensures ({
        let k = (q_spec(sv, p).key)(q_xs(db)[m]);
        &&& k.len() == 1
        &&& k[0] is Text
    }),
{
    let rows = q_rows(db);
    lemma_proj_all_index_local(rows, q_cols());
    let w = lemma_joined_witness(sv, db, m);
    let r = joined(db, w.a, w.i, w.b, w.n);
    lemma_joined_values(sv, db, w);
    lemma_joined_proj(r);
}

proof fn lemma_proj_all_index_local(rows: Seq<Row>, cols: Seq<nat>)
    ensures
        proj_all(rows, cols).len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> #[trigger] proj_all(rows, cols)[i] == proj(rows[i], cols),
{
    crate::link::source::lemma_proj_all_index(rows, cols);
}

/// SQL "not distinct" is equality on the keys of the joined rows.
pub proof fn lemma_keys_exact(sv: StoresView, db: Database, p: Seq<u8>)
    requires bound_db(sv, db),
    ensures keys_exact(q_spec(sv, p), q_xs(db)),
{
    let g = q_spec(sv, p);
    let xs = q_xs(db);
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        lemma_key_types(sv, db, p, a);
        lemma_key_types(sv, db, p, b);
        let (ka, kb) = ((g.key)(xs[a]), (g.key)(xs[b]));
        assert forall|t: int| 0 <= t < ka.len() implies same_exact_type(#[trigger] ka[t], kb[t]) by {}
        lemma_row_exact(ka, kb);
    }
}

pub proof fn lemma_aggs_match(sv: StoresView, p: Seq<u8>)
    ensures aggs_match(q_aggs(), q_spec(sv, p)),
{
    let g = q_spec(sv, p);
    assert(agg_matches(q_aggs()[0], g.aggs[0]));
}

// ------------------------------------------------------------------------------------------------ the body

/// The rows the WHERE keeps (the GROUP BY's input), under the normal form's condition.
pub open spec fn kept_rows(sv: StoresView, p: Seq<u8>, db: Database) -> Seq<Row> {
    keep_true(q_rows(db), qual_truths(q_spec(sv, p), q_xs(db)))
}

/// The WHERE evaluates to the kept rows.
pub proof fn lemma_input(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps),
    ensures eval_query(db, Seq::empty(), q_filter(ps[0])) == Ok::<Relation, SqlError>(kept_rows(sv, pb_of(ps), db)),
{
    lemma_eval_from(sv, db);
    lemma_pred_agrees(sv, db, ps);
    lemma_filter_rows(db, q_from(), q_rows(db), q_cols(), q_pred(ps[0]), q_spec(sv, pb_of(ps)));
}

/// Inside `group_caps` the body is the normal form's result rows.
pub proof fn lemma_body_ok(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires
        bound_db(sv, db), param_domain(ps),
        group_caps(q_spec(sv, pb_of(ps)), q_xs(db)),
    ensures denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(result_rows(q_spec(sv, pb_of(ps)), q_xs(db))),
{
    hide(eval_pred);
    hide(eval_exprs);
    hide(agg_args);
    let p = pb_of(ps);
    let g = q_spec(sv, p);
    let xs = q_xs(db);
    lemma_query_shape(ps);
    lemma_input(sv, db, ps);
    lemma_keys_agree(sv, db, p);
    lemma_args_agree(sv, db, p);
    lemma_keys_exact(sv, db, p);
    lemma_aggs_match(sv, p);
    lemma_group_query(db, q_rows(db), q_cols(), q_filter(ps[0]), q_keys(), q_aggs(), g);
    let ks = gkeys(g, xs);
    let fulls = ks.map_values(|k: Row| full_row(g, xs, k));
    let outs = ks.map_values(|k: Row| out_row(g, xs, k));
    assert forall|i: int| 0 <= i < ks.len() implies #[trigger] fulls[i] == outs[i] by {
        let k = ks[i];
        lemma_gkeys(g, xs);
        assert(ks.contains(k));
        lemma_gkeys_witness(g, xs, k);
        let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], k);
        lemma_key_types(sv, db, p, m);
        let f = full_row(g, xs, k);
        assert(agg_outs(g, xs, k).len() == 1);
        lemma_select_identity(f, seq![0nat, 1nat]);
    }
    assert(fulls =~= outs);
}

/// The GROUP BY's prepared inputs and groups in normal-form terms.
pub proof fn lemma_groups_setup(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps),
    ensures ({
        let g = q_spec(sv, pb_of(ps));
        let xs = q_xs(db);
        let kept = kept_rows(sv, pb_of(ps), db);
        let ks = qkeys(g, xs);
        let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
        &&& ks.len() == kept.len()
        &&& args.len() == kept.len()
        &&& forall|i: int| 0 <= i < kept.len() ==> #[trigger] group_input(db, Seq::<Val>::empty() + kept[i], q_keys(), q_aggs())
                == Ok::<(Row, Row), SqlError>((ks[i], args[i]))
        &&& distinct_rows(ks) == gkeys(g, xs)
        &&& forall|k: Row| #[trigger] gkeys(g, xs).contains(k) ==> group_members(ks, args, k) == members(g, xs, k)
    }),
{
    hide(eval_query);
    hide(eval_exprs);
    hide(agg_args);
    hide(group_input);
    let p = pb_of(ps);
    let g = q_spec(sv, p);
    let rows = q_rows(db);
    let cols = q_cols();
    let xs = q_xs(db);
    let kept = kept_rows(sv, p, db);
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    lemma_kept_rows(g, rows, cols);
    lemma_proj_all_index_local(kept, cols);
    lemma_keys_agree(sv, db, p);
    assert forall|i: int| 0 <= i < kept.len() implies #[trigger] group_input(db, Seq::<Val>::empty() + kept[i], q_keys(), q_aggs())
        == Ok::<(Row, Row), SqlError>((ks[i], args[i])) by {
        assert(Seq::<Val>::empty() + kept[i] =~= kept[i]);
        assert(rows.contains(kept[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
        assert((g.qual)(proj(rows[m], cols)));
        assert(eval_exprs(db, rows[m], q_keys()) == Ok::<Row, SqlError>((g.key)(proj(rows[m], cols))));
        lemma_args_any(db, kept[i], sv, p, qrows(g, xs)[i]);
        lemma_group_input_unfold(db, kept[i], q_keys(), q_aggs());
        assert(proj(kept[i], cols) == qrows(g, xs)[i]);
    }
    lemma_keys_exact(sv, db, p);
    let pool = key_pool(g, xs);
    lemma_pool_exact(g, xs);
    assert forall|i: int| 0 <= i < qkeys(g, xs).len() implies pool.contains(#[trigger] qkeys(g, xs)[i]) by {
        assert(pool[i] == qkeys(g, xs)[i]);
    }
    lemma_distinct_gkeys(g, xs, pool);
    assert forall|k: Row| #[trigger] gkeys(g, xs).contains(k) implies group_members(ks, args, k) == members(g, xs, k) by {
        let i = choose|i: int| 0 <= i < gkeys(g, xs).len() && gkeys(g, xs)[i] == k;
        assert(pool.contains(gkeys(g, xs)[i]));
        lemma_group_members(g, xs, k, pool);
    }
}

/// A group with more than int8 rows makes the statement's meaning the error 22003 (COUNT beyond int8; every other
/// group's COUNT is a value or the same error, so the group order does not matter).
pub proof fn lemma_body_count_error(sv: StoresView, db: Database, ps: Seq<Literal>, k: Row)
    requires
        bound_db(sv, db), param_domain(ps),
        gcount(q_spec(sv, pb_of(ps)), q_xs(db), k) > int8_max(),
    ensures denote_body(db, query_spec_at(ps)) == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange),
{
    hide(eval_query);
    hide(group_input);
    let p = pb_of(ps);
    let g = q_spec(sv, p);
    let xs = q_xs(db);
    let kept = kept_rows(sv, p, db);
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    let ctx = Seq::<Val>::empty();
    let e = SqlError::NumericValueOutOfRange;
    lemma_query_shape(ps);
    lemma_input(sv, db, ps);
    lemma_groups_setup(sv, db, ps);
    lemma_gkeys(g, xs);
    let ds = distinct_rows(ks);
    assert(ds.contains(k));
    let gi = choose|gi: int| 0 <= gi < ds.len() && ds[gi] == k;
    assert forall|h: int, j: int| 0 <= h < ds.len() && 0 <= j < q_aggs().len() implies
        #[trigger] agg_value(q_aggs()[j], column(group_members(ks, args, ds[h]), j)) is Ok
            || agg_value(q_aggs()[j], column(group_members(ks, args, ds[h]), j)) == Err::<Val, SqlError>(e) by {
        assert(ds.contains(ds[h]));
        lemma_members_col(g, xs, ds[h], j);
        lemma_count_value(Agg::CountStar, column(members(g, xs, ds[h]), j));
    }
    lemma_members_col(g, xs, k, 0);
    lemma_count_value(Agg::CountStar, column(members(g, xs, k), 0));
    assert(group_members(ks, args, ds[gi]) == members(g, xs, k));
    lemma_group_by_err(db, ctx, q_keys(), q_aggs(), Box::new(q_filter(ps[0])), kept, ks, args, e, gi, 0);
}

} // verus!
