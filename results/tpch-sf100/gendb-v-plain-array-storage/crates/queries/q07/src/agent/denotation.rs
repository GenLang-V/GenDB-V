//! The statement's body evaluates to the normal form's result rows (`lemma_denotation`).
//!
//! Path: FROM is the left-deep product `from6` of the database tables (`lemma_eval_from`); every joined row is
//! `joined6(s, l, o, c, a, b)` (`lemma_from6_witness`), whose fifteen read columns hold the stored values
//! (`lemma_joined_shape`). On such a row the WHERE condition evaluates without error to `q7_qual` of the projection
//! (`lemma_pred_shape`), and on a qualifying row the SELECT list evaluates to `out4` of the projection
//! (`lemma_exprs_shape`). So the WHERE keeps `kept(db, ps)` and the SELECT gives `sel_rows(db, ps)`, its rows mapped by
//! `select_of`; the GROUP BY over those four-column rows is `link::query::lemma_group_query` with the normal form
//! `g2` (all rows qualify; the keys `(text, text, numeric scale 0)` have one exact type per position) inside
//! `group_caps`.
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
use crate::spec::fns::apply_fn;
use crate::spec::fns::extract::*;
use crate::spec::equality::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::source_check::date32_val;
use crate::query::{query_spec_at, param_domain};
use crate::link::query::*;
use crate::link::join::lemma_product_index;
use crate::link::source::lemma_proj_all_index;
use crate::link::expr::{lemma_pred_cmp, lemma_pred_text_cmp, lemma_pred_and, lemma_pred_or, int_cmp, text_cmp};
use crate::bridge::equality::same_exact_type;
use crate::bridge::collect::lemma_collect_all;
use crate::agent::tables::*;
use crate::agent::normal_form::*;

verus! {

// ------------------------------------------------------------------------------------------------ the AST

/// WHERE: the five join equalities, the nation names, the ship window (left-nested ANDs, as written).
pub open spec fn q7_pred(ps: Seq<Literal>) -> Pred {
    let n18 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) };
    let n21 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(23), b: Expr::Col(7) };
    let n22 = Pred::And(Box::new(n18), Box::new(n21));
    let n25 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(32), b: Expr::Col(24) };
    let n26 = Pred::And(Box::new(n22), Box::new(n25));
    let n29 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(3), b: Expr::Col(40) };
    let n30 = Pred::And(Box::new(n26), Box::new(n29));
    let n33 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(35), b: Expr::Col(44) };
    let n34 = Pred::And(Box::new(n30), Box::new(n33));
    let n53 = q7_names(ps);
    let n54 = Pred::And(Box::new(n34), Box::new(n53));
    Pred::And(Box::new(n54), Box::new(q7_window()))
}

/// `(n1.n_name = $1 AND n2.n_name = $2) OR (n1.n_name = $2 AND n2.n_name = $1)`.
pub open spec fn q7_names(ps: Seq<Literal>) -> Pred {
    let n38 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(41), b: Expr::Lit(ps[0]) };
    let n42 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(45), b: Expr::Lit(ps[1]) };
    let n43 = Pred::And(Box::new(n38), Box::new(n42));
    let n47 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(41), b: Expr::Lit(ps[1]) };
    let n51 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(45), b: Expr::Lit(ps[0]) };
    let n52 = Pred::And(Box::new(n47), Box::new(n51));
    Pred::Or(Box::new(n43), Box::new(n52))
}

/// `l_shipdate BETWEEN DATE '1995-01-01' AND DATE '1996-12-31'`.
pub open spec fn q7_window() -> Pred {
    let n58 = Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(17), b: Expr::Lit(Literal::Date { y: 1995, m: 1, d: 1 }) };
    let n62 = Pred::Cmp { op: CmpOp::Le, a: Expr::Col(17), b: Expr::Lit(Literal::Date { y: 1996, m: 12, d: 31 }) };
    Pred::And(Box::new(n58), Box::new(n62))
}

/// FROM supplier, lineitem, orders, customer, nation n1, nation n2.
pub open spec fn q7_from() -> Query {
    let n67 = Query::Product { left: Box::new(Query::Table(5)), right: Box::new(Query::Table(0)) };
    let n69 = Query::Product { left: Box::new(n67), right: Box::new(Query::Table(1)) };
    let n71 = Query::Product { left: Box::new(n69), right: Box::new(Query::Table(2)) };
    let n73 = Query::Product { left: Box::new(n71), right: Box::new(Query::Table(6)) };
    Query::Product { left: Box::new(n73), right: Box::new(Query::Table(6)) }
}

/// `1 - l_discount` (the integer 1 cast to numeric).
pub open spec fn q7_one_minus() -> Expr {
    let n12 = Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) };
    Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(n12), b: Box::new(Expr::Col(13)) }
}

/// `l_extendedprice * (1 - l_discount)`.
pub open spec fn q7_volume() -> Expr {
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Col(12)), b: Box::new(q7_one_minus()) }
}

/// `EXTRACT(YEAR FROM l_shipdate)`.
pub open spec fn q7_year() -> Expr { Expr::Call { f: ScalarFn::ExtractYear, args: seq![Expr::Col(17)] } }

/// The SELECT list of the subquery `shipping`.
pub open spec fn q7_exprs() -> Seq<Expr> { seq![Expr::Col(41), Expr::Col(45), q7_year(), q7_volume()] }

pub open spec fn q7_filter(ps: Seq<Literal>) -> Query { Query::Filter { pred: q7_pred(ps), input: Box::new(q7_from()) } }

pub open spec fn q7_project(ps: Seq<Literal>) -> Query { Query::Project { exprs: q7_exprs(), input: Box::new(q7_filter(ps)) } }

pub open spec fn q7_keys() -> Seq<Expr> { seq![Expr::Col(0), Expr::Col(1), Expr::Col(2)] }

pub open spec fn q7_aggs() -> Seq<Agg> { seq![Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(3) }] }

/// GROUP BY supp_nation, cust_nation, l_year with SUM(volume).
pub open spec fn q7_body(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: q7_keys(), aggs: q7_aggs(), input: Box::new(q7_project(ps)) }
}

/// ORDER BY supp_nation, cust_nation, l_year.
pub open spec fn q7_order_keys() -> Seq<OrderKey> {
    seq![
        OrderKey { col: 0, desc: false, nulls_first: false },
        OrderKey { col: 1, desc: false, nulls_first: false },
        OrderKey { col: 2, desc: false, nulls_first: false },
    ]
}

/// The statement is this AST, without LIMIT or OFFSET.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures query_spec_at(ps) == (OrderedQuery { body: q7_body(ps), keys: q7_order_keys(), limit: None, offset: 0nat }),
{
}

// ------------------------------------------------------------------------------------------------ joined rows

/// FROM evaluates to the product of the tables.
pub proof fn lemma_eval_from(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures eval_query(db, Seq::empty(), q7_from()) == Ok::<Relation, SqlError>(from6(db)),
{
    lemma_parts_shape(sv, db);
    let e = Seq::<Val>::empty();
    assert(eval_query(db, e, Query::Table(5)) == Ok::<Relation, SqlError>(db.tables[5]));
    assert(eval_query(db, e, Query::Table(0)) == Ok::<Relation, SqlError>(db.tables[0]));
    assert(eval_query(db, e, Query::Table(1)) == Ok::<Relation, SqlError>(db.tables[1]));
    assert(eval_query(db, e, Query::Table(2)) == Ok::<Relation, SqlError>(db.tables[2]));
    assert(eval_query(db, e, Query::Table(6)) == Ok::<Relation, SqlError>(db.tables[6]));
    let n67 = Query::Product { left: Box::new(Query::Table(5)), right: Box::new(Query::Table(0)) };
    let n69 = Query::Product { left: Box::new(n67), right: Box::new(Query::Table(1)) };
    let n71 = Query::Product { left: Box::new(n69), right: Box::new(Query::Table(2)) };
    let n73 = Query::Product { left: Box::new(n71), right: Box::new(Query::Table(6)) };
    assert(eval_query(db, e, n67) == Ok::<Relation, SqlError>(from2(db)));
    assert(eval_query(db, e, n69) == Ok::<Relation, SqlError>(from3(db)));
    assert(eval_query(db, e, n71) == Ok::<Relation, SqlError>(from4(db)));
    assert(eval_query(db, e, n73) == Ok::<Relation, SqlError>(from5(db)));
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

/// Index tuples of the joined rows.
pub open spec fn in6(sv: StoresView, s: int, l: int, o: int, c: int, a: int, b: int) -> bool {
    &&& 0 <= s < n_s(sv) && 0 <= l < n_l(sv) && 0 <= o < n_o(sv) && 0 <= c < n_c(sv)
    &&& 0 <= a < n_n(sv) && 0 <= b < n_n(sv)
}

/// Every joined row is `joined6` of some rows of the six inputs.
pub proof fn lemma_from6_witness(sv: StoresView, db: Database, k: int) -> (w: (int, int, int, int, int, int))
    requires bound_db(sv, db), 0 <= k < from6(db).len(),
    ensures
        in6(sv, w.0, w.1, w.2, w.3, w.4, w.5),
        from6(db)[k] == joined6(db, w.0, w.1, w.2, w.3, w.4, w.5),
{
    lemma_parts_shape(sv, db);
    let (k5, b) = lemma_product_witness(from5(db), db.tables[6], k);
    let (k4, a) = lemma_product_witness(from4(db), db.tables[6], k5);
    let (k3, c) = lemma_product_witness(from3(db), db.tables[2], k4);
    let (k2, o) = lemma_product_witness(from2(db), db.tables[1], k3);
    let (s, l) = lemma_product_witness(db.tables[5], db.tables[0], k2);
    (s, l, o, c, a, b)
}

/// A 48-column row as the statement sees it: the fifteen values it reads have these types and values.
pub open spec fn row_shape(r: Row, skey: int, snat: int, lokey: int, lsupp: int, price: int, disc: int, ship: int,
    okey: int, ocust: int, ckey: int, cnat: int, nk1: int, nm1: Seq<u8>, nk2: int, nm2: Seq<u8>) -> bool
{
    &&& r.len() == 48
    &&& r[0] == Val::Int(skey) && r[3] == Val::Int(snat)
    &&& r[7] == Val::Int(lokey) && r[9] == Val::Int(lsupp)
    &&& r[12] == (Val::Num { coeff: price, scale: 2 }) && r[13] == (Val::Num { coeff: disc, scale: 2 })
    &&& r[17] == Val::Date(ship)
    &&& r[23] == Val::Int(okey) && r[24] == Val::Int(ocust)
    &&& r[32] == Val::Int(ckey) && r[35] == Val::Int(cnat)
    &&& r[40] == Val::Int(nk1) && r[41] == Val::Text(nm1)
    &&& r[44] == Val::Int(nk2) && r[45] == Val::Text(nm2)
}

/// The joined row of an index tuple has the shape, with the stored values.
pub proof fn lemma_joined_shape(sv: StoresView, db: Database, s: int, l: int, o: int, c: int, a: int, b: int)
    requires bound_db(sv, db), in6(sv, s, l, o, c, a, b),
    ensures
        row_shape(joined6(db, s, l, o, c, a, b), sk(sv)[s] as int, sn(sv)[s] as int, lok(sv)[l] as int,
            lsk(sv)[l] as int, lpr(sv)[l] as int, ldc(sv)[l] as int, lsd(sv)[l] as int - 10957, ok(sv)[o] as int,
            oc(sv)[o] as int, ck(sv)[c] as int, cn(sv)[c] as int, nk(sv)[a] as int, nname(sv, a), nk(sv)[b] as int,
            nname(sv, b)),
        num15(lpr(sv)[l]), num15(ldc(sv)[l]),
{
    lemma_parts_shape(sv, db);
    lemma_supplier_row(sv, db, s);
    lemma_lineitem_row(sv, db, l);
    lemma_orders_row(sv, db, o);
    lemma_customer_row(sv, db, c);
    lemma_nation_row(sv, db, a);
    lemma_nation_row(sv, db, b);
    let (rs, rl, ro, rc, ra, rb) = (db.tables[5][s], db.tables[0][l], db.tables[1][o], db.tables[2][c], db.tables[6][a], db.tables[6][b]);
    let r2 = rs + rl;
    let r3 = r2 + ro;
    let r4 = r3 + rc;
    let r5 = r4 + ra;
    let r = r5 + rb;
    assert(r2[0] == rs[0] && r2[3] == rs[3] && r2[7] == rl[0] && r2[9] == rl[2] && r2[12] == rl[5] && r2[13] == rl[6]
        && r2[17] == rl[10]);
    assert(r3[23] == ro[0] && r3[24] == ro[1]);
    assert(r4[32] == rc[0] && r4[35] == rc[3]);
    assert(r5[40] == ra[0] && r5[41] == ra[1]);
    assert(r[44] == rb[0] && r[45] == rb[1]);
    assert(r[0] == r2[0] && r[3] == r2[3] && r[7] == r2[7] && r[9] == r2[9] && r[12] == r2[12] && r[13] == r2[13]
        && r[17] == r2[17]);
    assert(r[23] == r3[23] && r[24] == r3[24] && r[32] == r4[32] && r[35] == r4[35] && r[40] == r5[40] && r[41] == r5[41]);
}

/// The projection of a 48-column row onto the read columns.
pub proof fn lemma_joined_proj(r: Row)
    requires r.len() == 48,
    ensures proj(r, q7_cols()) == seq![r[0], r[3], r[7], r[9], r[12], r[13], r[17], r[23], r[24], r[32], r[35], r[40],
        r[41], r[44], r[45]],
{
    assert(proj(r, q7_cols()) =~= seq![r[0], r[3], r[7], r[9], r[12], r[13], r[17], r[23], r[24], r[32], r[35], r[40],
        r[41], r[44], r[45]]);
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

/// The literal values of the two parameters and of the two window dates (SQL days).
pub proof fn lemma_literals(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures
        lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Text(p1_of(ps))),
        lit_val(ps[1]) == Ok::<Val, SqlError>(Val::Text(p2_of(ps))),
        lit_val(Literal::Date { y: 1995, m: 1, d: 1 }) == Ok::<Val, SqlError>(Val::Date(-1826)),
        lit_val(Literal::Date { y: 1996, m: 12, d: 31 }) == Ok::<Val, SqlError>(Val::Date(-1096)),
{
    assert(lit_val(Literal::Date { y: 1995, m: 1, d: 1 }) == Ok::<Val, SqlError>(Val::Date(-1826))) by (compute);
    assert(lit_val(Literal::Date { y: 1996, m: 12, d: 31 }) == Ok::<Val, SqlError>(Val::Date(-1096))) by (compute);
}

/// An integer equality of two columns.
proof fn lemma_cols_eq(db: Database, r: Row, i: nat, j: nat, x: int, y: int)
    requires i < r.len(), j < r.len(), r[i as int] == Val::Int(x), r[j as int] == Val::Int(y),
    ensures eval_pred(db, r, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(i), b: Expr::Col(j) }) == Ok::<Truth, SqlError>(truth_of(x == y)),
{
    lemma_eval_col(db, r, i);
    lemma_eval_col(db, r, j);
    lemma_pred_cmp(db, r, CmpOp::Eq, Expr::Col(i), Expr::Col(j), Val::Int(x), Val::Int(y), x, y);
}

/// A text column equal to a text literal.
proof fn lemma_col_text_eq(db: Database, r: Row, i: nat, lit: Literal, x: Seq<u8>, y: Seq<u8>)
    requires i < r.len(), r[i as int] == Val::Text(x), lit_val(lit) == Ok::<Val, SqlError>(Val::Text(y)),
    ensures eval_pred(db, r, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(i), b: Expr::Lit(lit) }) == Ok::<Truth, SqlError>(truth_of(x == y)),
{
    lemma_eval_col(db, r, i);
    lemma_eval_lit(db, r, lit);
    lemma_pred_text_cmp(db, r, CmpOp::Eq, Expr::Col(i), Expr::Lit(lit), x, y);
}

/// A date column compared with a date literal.
proof fn lemma_col_date_cmp(db: Database, r: Row, i: nat, op: CmpOp, lit: Literal, x: int, y: int)
    requires i < r.len(), r[i as int] == Val::Date(x), lit_val(lit) == Ok::<Val, SqlError>(Val::Date(y)),
    ensures eval_pred(db, r, Pred::Cmp { op, a: Expr::Col(i), b: Expr::Lit(lit) }) == Ok::<Truth, SqlError>(truth_of(int_cmp(op, x, y))),
{
    lemma_eval_col(db, r, i);
    lemma_eval_lit(db, r, lit);
    lemma_pred_cmp(db, r, op, Expr::Col(i), Expr::Lit(lit), Val::Date(x), Val::Date(y), x, y);
}

/// The nation-name condition on a row of the shape.
proof fn lemma_names_shape(db: Database, ps: Seq<Literal>, r: Row, nm1: Seq<u8>, nm2: Seq<u8>)
    requires param_domain(ps), r.len() == 48, r[41] == Val::Text(nm1), r[45] == Val::Text(nm2),
    ensures eval_pred(db, r, q7_names(ps)) == Ok::<Truth, SqlError>(truth_of(
        (nm1 == p1_of(ps) && nm2 == p2_of(ps)) || (nm1 == p2_of(ps) && nm2 == p1_of(ps)))),
{
    lemma_literals(ps);
    let (p1, p2) = (p1_of(ps), p2_of(ps));
    lemma_col_text_eq(db, r, 41, ps[0], nm1, p1);
    lemma_col_text_eq(db, r, 45, ps[1], nm2, p2);
    lemma_col_text_eq(db, r, 41, ps[1], nm1, p2);
    lemma_col_text_eq(db, r, 45, ps[0], nm2, p1);
    let n38 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(41), b: Expr::Lit(ps[0]) };
    let n42 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(45), b: Expr::Lit(ps[1]) };
    let n47 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(41), b: Expr::Lit(ps[1]) };
    let n51 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(45), b: Expr::Lit(ps[0]) };
    lemma_pred_and(db, r, n38, n42, nm1 == p1, nm2 == p2);
    lemma_pred_and(db, r, n47, n51, nm1 == p2, nm2 == p1);
    lemma_pred_or(db, r, Pred::And(Box::new(n38), Box::new(n42)), Pred::And(Box::new(n47), Box::new(n51)),
        nm1 == p1 && nm2 == p2, nm1 == p2 && nm2 == p1);
}

/// The ship window on a row of the shape.
proof fn lemma_window_shape(db: Database, ps: Seq<Literal>, r: Row, ship: int)
    requires param_domain(ps), r.len() == 48, r[17] == Val::Date(ship),
    ensures eval_pred(db, r, q7_window()) == Ok::<Truth, SqlError>(truth_of(-1826 <= ship <= -1096)),
{
    lemma_literals(ps);
    let lo = Literal::Date { y: 1995, m: 1, d: 1 };
    let hi = Literal::Date { y: 1996, m: 12, d: 31 };
    lemma_col_date_cmp(db, r, 17, CmpOp::Ge, lo, ship, -1826);
    lemma_col_date_cmp(db, r, 17, CmpOp::Le, hi, ship, -1096);
    lemma_pred_and(db, r, Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(17), b: Expr::Lit(lo) },
        Pred::Cmp { op: CmpOp::Le, a: Expr::Col(17), b: Expr::Lit(hi) }, ship >= -1826, ship <= -1096);
}

/// The WHERE condition on a row of the shape.
pub proof fn lemma_pred_shape(db: Database, ps: Seq<Literal>, r: Row, skey: int, snat: int, lokey: int, lsupp: int,
    price: int, disc: int, ship: int, okey: int, ocust: int, ckey: int, cnat: int, nk1: int, nm1: Seq<u8>, nk2: int,
    nm2: Seq<u8>)
    requires
        param_domain(ps),
        row_shape(r, skey, snat, lokey, lsupp, price, disc, ship, okey, ocust, ckey, cnat, nk1, nm1, nk2, nm2),
    ensures
        eval_pred(db, r, q7_pred(ps)) == Ok::<Truth, SqlError>(truth_of(
            skey == lsupp && okey == lokey && ckey == ocust && snat == nk1 && cnat == nk2
            && ((nm1 == p1_of(ps) && nm2 == p2_of(ps)) || (nm1 == p2_of(ps) && nm2 == p1_of(ps)))
            && -1826 <= ship <= -1096)),
{
    lemma_cols_eq(db, r, 0, 9, skey, lsupp);
    lemma_cols_eq(db, r, 23, 7, okey, lokey);
    lemma_cols_eq(db, r, 32, 24, ckey, ocust);
    lemma_cols_eq(db, r, 3, 40, snat, nk1);
    lemma_cols_eq(db, r, 35, 44, cnat, nk2);
    lemma_names_shape(db, ps, r, nm1, nm2);
    lemma_window_shape(db, ps, r, ship);
    let n18 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) };
    let n21 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(23), b: Expr::Col(7) };
    let n25 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(32), b: Expr::Col(24) };
    let n29 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(3), b: Expr::Col(40) };
    let n33 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(35), b: Expr::Col(44) };
    let (e18, e21, e25, e29, e33) = (skey == lsupp, okey == lokey, ckey == ocust, snat == nk1, cnat == nk2);
    let names = (nm1 == p1_of(ps) && nm2 == p2_of(ps)) || (nm1 == p2_of(ps) && nm2 == p1_of(ps));
    let win = -1826 <= ship <= -1096;
    lemma_pred_and(db, r, n18, n21, e18, e21);
    let n22 = Pred::And(Box::new(n18), Box::new(n21));
    lemma_pred_and(db, r, n22, n25, e18 && e21, e25);
    let n26 = Pred::And(Box::new(n22), Box::new(n25));
    lemma_pred_and(db, r, n26, n29, e18 && e21 && e25, e29);
    let n30 = Pred::And(Box::new(n26), Box::new(n29));
    lemma_pred_and(db, r, n30, n33, e18 && e21 && e25 && e29, e33);
    let n34 = Pred::And(Box::new(n30), Box::new(n33));
    lemma_pred_and(db, r, n34, q7_names(ps), e18 && e21 && e25 && e29 && e33, names);
    let n54 = Pred::And(Box::new(n34), Box::new(q7_names(ps)));
    lemma_pred_and(db, r, n54, q7_window(), e18 && e21 && e25 && e29 && e33 && names, win);
}

/// `EXTRACT(YEAR FROM l_shipdate)` on a row of the shape.
proof fn lemma_year_shape(db: Database, r: Row, ship: int)
    requires r.len() == 48, r[17] == Val::Date(ship),
    ensures eval_expr(db, r, q7_year()) == Ok::<Val, SqlError>(year_val(Val::Date(ship))),
{
    let args = seq![Expr::Col(17)];
    lemma_eval_col(db, r, 17);
    lemma_expr_results_index(db, r, args);
    lemma_collect_all(expr_results(db, r, args), seq![Val::Date(ship)]);
    assert(eval_exprs(db, r, args) == Ok::<Row, SqlError>(seq![Val::Date(ship)]));
    assert(apply_fn(ScalarFn::ExtractYear, seq![Val::Date(ship)]) == apply_extract(ScalarFn::ExtractYear, seq![Val::Date(ship)]));
}

/// `l_extendedprice * (1 - l_discount)` on a row of the shape (prices and discounts of numeric(15,2)).
proof fn lemma_volume_shape(db: Database, r: Row, price: int, disc: int)
    requires
        r.len() == 48, r[12] == (Val::Num { coeff: price, scale: 2 }), r[13] == (Val::Num { coeff: disc, scale: 2 }),
        abs(price) < pow10(15), abs(disc) < pow10(15),
    ensures eval_expr(db, r, q7_volume()) == Ok::<Val, SqlError>(Val::Num { coeff: price * (100 - disc), scale: 4 }),
{
    let one = Literal::Int { v: 1, kind: IntKind::Int4 };
    let n12 = Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(one)) };
    assert(lit_val(one) == Ok::<Val, SqlError>(Val::Int(1)));
    lemma_eval_lit(db, r, one);
    assert(eval_expr(db, r, n12) == Ok::<Val, SqlError>(Val::Num { coeff: 1, scale: 0 }));
    lemma_eval_col(db, r, 12);
    lemma_eval_col(db, r, 13);
    assert(pow10(1) == 10 && pow10(2) == 100 && pow10(0) == 1) by (compute);
    assert(crate::spec::limits::numeric_int_digits_max() >= 100) by (compute);
    lemma_node_add(db, r, ArithOp::Sub, n12, Expr::Col(13), 1, 0, 1, disc, 2, 15, 2, 100, 1, 16);
    assert(1 * 100 - disc * 1 == 100 - disc);
    lemma_node_mul(db, r, Expr::Col(12), q7_one_minus(), price, 2, 15, 100 - disc, 2, 16);
}

/// The normal form's SELECT row of a row of the shape.
pub proof fn lemma_select_of_shape(r: Row, skey: int, snat: int, lokey: int, lsupp: int, price: int, disc: int,
    ship: int, okey: int, ocust: int, ckey: int, cnat: int, nk1: int, nm1: Seq<u8>, nk2: int, nm2: Seq<u8>)
    requires row_shape(r, skey, snat, lokey, lsupp, price, disc, ship, okey, ocust, ckey, cnat, nk1, nm1, nk2, nm2),
    ensures select_of(r) == seq![Val::Text(nm1), Val::Text(nm2), year_val(Val::Date(ship)),
        Val::Num { coeff: price * (100 - disc), scale: 4 }],
{
    lemma_joined_proj(r);
}

/// Four values of four expressions: the list evaluates to them.
proof fn lemma_eval_four(db: Database, r: Row, es: Seq<Expr>, vs: Row)
    requires
        es.len() == 4, vs.len() == 4,
        eval_expr(db, r, es[0]) == Ok::<Val, SqlError>(vs[0]),
        eval_expr(db, r, es[1]) == Ok::<Val, SqlError>(vs[1]),
        eval_expr(db, r, es[2]) == Ok::<Val, SqlError>(vs[2]),
        eval_expr(db, r, es[3]) == Ok::<Val, SqlError>(vs[3]),
    ensures eval_exprs(db, r, es) == Ok::<Row, SqlError>(vs),
{
    lemma_expr_results_index(db, r, es);
    let rs = expr_results(db, r, es);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Val, SqlError>(vs[i]) by {
        assert(rs[i] == eval_expr(db, r, es[i]));
    }
    lemma_collect_all(rs, vs);
}

/// The SELECT list on a row of the shape.
pub proof fn lemma_exprs_shape(db: Database, r: Row, skey: int, snat: int, lokey: int, lsupp: int, price: int,
    disc: int, ship: int, okey: int, ocust: int, ckey: int, cnat: int, nk1: int, nm1: Seq<u8>, nk2: int, nm2: Seq<u8>)
    requires
        row_shape(r, skey, snat, lokey, lsupp, price, disc, ship, okey, ocust, ckey, cnat, nk1, nm1, nk2, nm2),
        abs(price) < pow10(15), abs(disc) < pow10(15),
    ensures eval_exprs(db, r, q7_exprs()) == Ok::<Row, SqlError>(select_of(r)),
{
    let es = q7_exprs();
    let vs = seq![Val::Text(nm1), Val::Text(nm2), year_val(Val::Date(ship)), Val::Num { coeff: price * (100 - disc), scale: 4 }];
    lemma_eval_col(db, r, 41);
    lemma_eval_col(db, r, 45);
    lemma_year_shape(db, r, ship);
    lemma_volume_shape(db, r, price, disc);
    assert(es[0] == Expr::Col(41) && es[1] == Expr::Col(45) && es[2] == q7_year() && es[3] == q7_volume());
    lemma_eval_four(db, r, es, vs);
    lemma_select_of_shape(r, skey, snat, lokey, lsupp, price, disc, ship, okey, ocust, ckey, cnat, nk1, nm1, nk2, nm2);
}

// ------------------------------------------------------------------------------------------------ WHERE and SELECT

/// The joined row of an index tuple, projected: the normal form's WHERE is the shape's condition.
pub proof fn lemma_qual_joined(sv: StoresView, db: Database, ps: Seq<Literal>, s: int, l: int, o: int, c: int, a: int, b: int)
    requires bound_db(sv, db), in6(sv, s, l, o, c, a, b),
    ensures
        qual_row(ps, joined6(db, s, l, o, c, a, b)) == (
            sk(sv)[s] == lsk(sv)[l] && ok(sv)[o] == lok(sv)[l] && ck(sv)[c] == oc(sv)[o] && sn(sv)[s] == nk(sv)[a]
            && cn(sv)[c] == nk(sv)[b]
            && names_ok(Val::Text(nname(sv, a)), Val::Text(nname(sv, b)), p1_of(ps), p2_of(ps))
            && ship_in(lsd(sv)[l] as int)),
        select_of(joined6(db, s, l, o, c, a, b)) == seq![Val::Text(nname(sv, a)), Val::Text(nname(sv, b)),
            year_val(date32_val(lsd(sv)[l])), Val::Num { coeff: lpr(sv)[l] * (100 - ldc(sv)[l]), scale: 4 }],
{
    let r = joined6(db, s, l, o, c, a, b);
    lemma_joined_shape(sv, db, s, l, o, c, a, b);
    lemma_joined_proj(r);
}

/// WHERE agrees with the normal form on every joined row.
pub proof fn lemma_pred_agrees(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps),
    ensures pred_agrees(db, from6(db), q7_cols(), q7_pred(ps), g1(ps)),
{
    let rows = from6(db);
    let g = g1(ps);
    assert forall|k: int| 0 <= k < rows.len() implies
        eval_pred(db, #[trigger] rows[k], q7_pred(ps)) == Ok::<Truth, SqlError>(truth_of((g.qual)(proj(rows[k], q7_cols())))) by {
        let (s, l, o, c, a, b) = lemma_from6_witness(sv, db, k);
        lemma_joined_shape(sv, db, s, l, o, c, a, b);
        let r = joined6(db, s, l, o, c, a, b);
        lemma_pred_shape(db, ps, r, sk(sv)[s] as int, sn(sv)[s] as int, lok(sv)[l] as int, lsk(sv)[l] as int,
            lpr(sv)[l] as int, ldc(sv)[l] as int, lsd(sv)[l] as int - 10957, ok(sv)[o] as int, oc(sv)[o] as int,
            ck(sv)[c] as int, cn(sv)[c] as int, nk(sv)[a] as int, nname(sv, a), nk(sv)[b] as int, nname(sv, b));
        lemma_joined_proj(r);
    }
}

/// The rows the WHERE keeps.
pub open spec fn kept(db: Database, ps: Seq<Literal>) -> Seq<Row> {
    keep_true(from6(db), qual_truths(g1(ps), proj_all(from6(db), q7_cols())))
}

/// The SELECT rows of the subquery `shipping`: `select_of` of every kept row.
pub open spec fn sel_rows(db: Database, ps: Seq<Literal>) -> Seq<Row> {
    kept(db, ps).map_values(|r: Row| select_of(r))
}

/// The WHERE keeps `kept(db, ps)`: joined rows (of some index tuple) that qualify.
pub proof fn lemma_eval_filter(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps),
    ensures
        eval_query(db, Seq::empty(), q7_filter(ps)) == Ok::<Relation, SqlError>(kept(db, ps)),
        forall|i: int| 0 <= i < kept(db, ps).len() ==> from6(db).contains(#[trigger] kept(db, ps)[i])
            && qual_row(ps, kept(db, ps)[i]),
{
    lemma_eval_from(sv, db);
    lemma_pred_agrees(sv, db, ps);
    lemma_filter_rows(db, q7_from(), from6(db), q7_cols(), q7_pred(ps), g1(ps));
    lemma_kept_rows(g1(ps), from6(db), q7_cols());
}

/// The SELECT list evaluates on every kept row.
pub proof fn lemma_eval_project(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps),
    ensures eval_query(db, Seq::empty(), q7_project(ps)) == Ok::<Relation, SqlError>(sel_rows(db, ps)),
{
    lemma_eval_filter(sv, db, ps);
    let ks = kept(db, ps);
    let ctx = Seq::<Val>::empty();
    let rs = Seq::new(ks.len(), |i: int| eval_exprs(db, ctx + ks[i], q7_exprs()));
    let vs = sel_rows(db, ps);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(vs[i]) by {
        assert(ctx + ks[i] =~= ks[i]);
        assert(from6(db).contains(ks[i]));
        let k = choose|k: int| 0 <= k < from6(db).len() && from6(db)[k] == ks[i];
        let (s, l, o, c, a, b) = lemma_from6_witness(sv, db, k);
        lemma_joined_shape(sv, db, s, l, o, c, a, b);
        assert(pow10(15) == 1_000_000_000_000_000) by (compute);
        lemma_exprs_shape(db, ks[i], sk(sv)[s] as int, sn(sv)[s] as int, lok(sv)[l] as int, lsk(sv)[l] as int,
            lpr(sv)[l] as int, ldc(sv)[l] as int, lsd(sv)[l] as int - 10957, ok(sv)[o] as int, oc(sv)[o] as int,
            ck(sv)[c] as int, cn(sv)[c] as int, nk(sv)[a] as int, nname(sv, a), nk(sv)[b] as int, nname(sv, b));
    }
    lemma_collect_all(rs, vs);
    crate::exec::relational::domain::lemma_collect_pointwise::<Row>();
}

// ------------------------------------------------------------------------------------------------ GROUP BY

/// Every SELECT row has four columns: two names, a year at scale 0, a volume at scale 4.
pub open spec fn sel_row_ok(x: Row) -> bool {
    &&& x.len() == 4
    &&& x[0] is Text && x[1] is Text
    &&& x[2] is Num && x[2]->Num_scale == 0
    &&& x[3] is Num && x[3]->Num_scale == 4
}

pub proof fn lemma_sel_rows_ok(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps),
    ensures forall|i: int| 0 <= i < sel_rows(db, ps).len() ==> sel_row_ok(#[trigger] sel_rows(db, ps)[i]),
{
    lemma_eval_filter(sv, db, ps);
    let ks = kept(db, ps);
    assert forall|i: int| 0 <= i < sel_rows(db, ps).len() implies sel_row_ok(#[trigger] sel_rows(db, ps)[i]) by {
        assert(from6(db).contains(ks[i]));
        let k = choose|k: int| 0 <= k < from6(db).len() && from6(db)[k] == ks[i];
        let (s, l, o, c, a, b) = lemma_from6_witness(sv, db, k);
        lemma_qual_joined(sv, db, ps, s, l, o, c, a, b);
    }
}

/// Projecting the SELECT rows on all four columns keeps them.
pub proof fn lemma_sel_proj(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps),
    ensures proj_all(sel_rows(db, ps), c4()) == sel_rows(db, ps),
{
    let xs = sel_rows(db, ps);
    lemma_sel_rows_ok(sv, db, ps);
    lemma_proj_all_index(xs, c4());
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] proj_all(xs, c4())[i] == xs[i] by {
        assert(xs[i].len() == 4);
        assert(proj(xs[i], c4()) =~= xs[i]);
    }
    assert(proj_all(xs, c4()) =~= xs);
}

/// GROUP BY keys agree with `g2` on rows of the SELECT shape.
proof fn lemma_keys_agree(db: Database, xs: Seq<Row>)
    requires forall|i: int| 0 <= i < xs.len() ==> sel_row_ok(#[trigger] xs[i]),
    ensures keys_agree(db, xs, c4(), q7_keys(), g2()),
{
    let g = g2();
    assert forall|i: int| 0 <= i < xs.len() && (g.qual)(proj(#[trigger] xs[i], c4())) implies
        eval_exprs(db, xs[i], q7_keys()) == Ok::<Row, SqlError>((g.key)(proj(xs[i], c4()))) by {
        let x = xs[i];
        assert(sel_row_ok(x));
        assert(proj(x, c4()) =~= x);
        let idxs = seq![0nat, 1, 2];
        assert(col_exprs(idxs) =~= q7_keys());
        lemma_eval_cols(db, x, idxs);
        assert(select(x, idxs) =~= seq![x[0], x[1], x[2]]);
    }
}

/// The SUM argument agrees with `g2` on rows of the SELECT shape.
proof fn lemma_args_agree(db: Database, xs: Seq<Row>)
    requires forall|i: int| 0 <= i < xs.len() ==> sel_row_ok(#[trigger] xs[i]),
    ensures args_agree(db, xs, c4(), q7_aggs(), g2()),
{
    let g = g2();
    assert forall|i: int| 0 <= i < xs.len() && (g.qual)(proj(#[trigger] xs[i], c4())) implies
        agg_args(db, xs[i], q7_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(xs[i], c4()))) by {
        let x = xs[i];
        assert(sel_row_ok(x));
        assert(proj(x, c4()) =~= x);
        let rs = agg_arg_results(db, x, q7_aggs());
        lemma_agg_arg_results_index(db, x, q7_aggs());
        lemma_eval_col(db, x, 3);
        let vs = seq![Val::Num { coeff: coeff_of(x[3]), scale: 4 }];
        assert(rs[0] == agg_arg(db, x, q7_aggs()[0]));
        assert(rs[0] == Ok::<Val, SqlError>(vs[0]));
        lemma_collect_all(rs, vs);
        assert(arg_vals(g, x) =~= vs);
    }
}

/// On rows of the SELECT shape SQL "not distinct" of the keys is equality (text, text, numeric scale 0).
proof fn lemma_keys_exact(xs: Seq<Row>)
    requires forall|i: int| 0 <= i < xs.len() ==> sel_row_ok(#[trigger] xs[i]),
    ensures keys_exact(g2(), xs),
{
    let g = g2();
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        let (ka, kb) = ((g.key)(xs[a]), (g.key)(xs[b]));
        assert(sel_row_ok(xs[a]) && sel_row_ok(xs[b]));
        assert forall|t: int| 0 <= t < ka.len() implies same_exact_type(#[trigger] ka[t], kb[t]) by {
            if t == 0 {} else if t == 1 {} else {}
        }
        lemma_row_exact(ka, kb);
    }
}

/// GROUP BY keys and arguments agree with `g2` on every SELECT row; the keys are exact.
pub proof fn lemma_group_premises(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps),
    ensures
        keys_agree(db, sel_rows(db, ps), c4(), q7_keys(), g2()),
        args_agree(db, sel_rows(db, ps), c4(), q7_aggs(), g2()),
        aggs_match(q7_aggs(), g2()),
        keys_exact(g2(), proj_all(sel_rows(db, ps), c4())),
{
    let xs = sel_rows(db, ps);
    lemma_sel_rows_ok(sv, db, ps);
    lemma_sel_proj(sv, db, ps);
    lemma_keys_agree(db, xs);
    lemma_args_agree(db, xs);
    lemma_keys_exact(xs);
    assert(agg_matches(q7_aggs()[0], g2().aggs[0]));
}

/// The GROUP BY rows: the full row of every group key, in first-occurrence order (inside the arithmetic domain).
pub proof fn lemma_group_eval(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps), group_caps(g2(), sel_rows(db, ps)),
    ensures eval_query(db, Seq::empty(), q7_body(ps)) == Ok::<Relation, SqlError>(
        gkeys(g2(), sel_rows(db, ps)).map_values(|k: Row| full_row(g2(), sel_rows(db, ps), k))),
{
    let xs = sel_rows(db, ps);
    let g = g2();
    lemma_eval_project(sv, db, ps);
    lemma_sel_proj(sv, db, ps);
    assert forall|x: Row| #[trigger] (g.qual)(x) by {}
    lemma_table_rows(db, q7_project(ps), xs, c4(), g);
    lemma_group_premises(sv, db, ps);
    lemma_group_query(db, xs, c4(), q7_project(ps), q7_keys(), q7_aggs(), g);
}

/// The body of the statement evaluates to the normal form's result rows (inside `group_caps`).
pub proof fn lemma_denotation(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps), group_caps(g2(), sel_rows(db, ps)),
    ensures denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(result_rows(g2(), sel_rows(db, ps))),
{
    let xs = sel_rows(db, ps);
    let g = g2();
    lemma_query_shape(ps);
    lemma_group_eval(sv, db, ps);
    let full = gkeys(g, xs).map_values(|k: Row| full_row(g, xs, k));
    let res = result_rows(g, xs);
    lemma_gkeys(g, xs);
    assert forall|t: int| 0 <= t < res.len() implies res[t] == full[t] by {
        let k = gkeys(g, xs)[t];
        assert(gkeys(g, xs).contains(k));
        lemma_gkeys_witness(g, xs, k);
        let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], k);
        assert(k.len() == 3);
        let fr = full_row(g, xs, k);
        assert(agg_outs(g, xs, k).len() == 1);
        assert(fr.len() == 4);
        lemma_select_identity(fr, g.outs);
    }
    assert(res =~= full);
}

} // verus!
