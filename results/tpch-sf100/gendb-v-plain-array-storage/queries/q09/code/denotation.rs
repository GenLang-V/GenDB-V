//! The statement's body evaluates to the normal form's result rows (`lemma_denotation`).
//!
//! Path: FROM is the left-deep product `from6` of the database tables (`lemma_eval_from`); every joined row is
//! `joined6(p, s, l, q, o, a)` (`lemma_from6_witness`), whose seventeen read columns hold the stored values
//! (`shape`, `lemma_joined_shape`). On such a row the WHERE condition evaluates to `q9_qual` of the projection when
//! the part's `LIKE` does not raise, and to the `LIKE` error otherwise (`lemma_pred_shape`); on a qualifying row the
//! SELECT list evaluates to `out3` of the projection (`lemma_exprs_shape`). When no joined row's `LIKE` raises
//! (`likes_ok`) the WHERE keeps `kept(db, ps)` and the SELECT gives `sel_rows(db, ps)`, its rows mapped by
//! `select_of`; the GROUP BY over those three-column rows is `link::query::lemma_group_query` with the normal form
//! `g2` (all rows qualify; the keys `(text, numeric scale 0)` have one exact type per position) inside `group_caps`.
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
use crate::spec::chars::*;
use crate::spec::fns::apply_fn;
use crate::spec::fns::extract::*;
use crate::spec::fns::like::*;
use crate::spec::equality::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::source_check::date32_val;
use crate::query::{query_spec_at, param_domain};
use crate::link::query::*;
use crate::link::join::lemma_product_index;
use crate::link::source::lemma_proj_all_index;
use crate::link::expr::{lemma_pred_cmp, lemma_pred_and, int_cmp};
use crate::bridge::equality::same_exact_type;
use crate::bridge::collect::lemma_collect_all;
use crate::agent::tables::*;
use crate::agent::normal_form::*;

verus! {

// ------------------------------------------------------------------------------------------------ the AST

/// The six key equalities of the WHERE (left-nested ANDs, as written).
pub open spec fn q9_eqs() -> Pred {
    let n20 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(9), b: Expr::Col(18) };
    let n23 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(33), b: Expr::Col(18) };
    let n24 = Pred::And(Box::new(n20), Box::new(n23));
    let n27 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(32), b: Expr::Col(17) };
    let n28 = Pred::And(Box::new(n24), Box::new(n27));
    let n31 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(17) };
    let n32 = Pred::And(Box::new(n28), Box::new(n31));
    let n35 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(37), b: Expr::Col(16) };
    let n36 = Pred::And(Box::new(n32), Box::new(n35));
    let n39 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(12), b: Expr::Col(46) };
    Pred::And(Box::new(n36), Box::new(n39))
}

/// `p_name LIKE $1` (escape backslash).
pub open spec fn q9_like_call(ps: Seq<Literal>) -> Expr {
    Expr::Call { f: ScalarFn::Like, args: seq![Expr::Col(1), Expr::Lit(ps[0]), Expr::Lit(Literal::Text(seq![92u8]))] }
}

pub open spec fn q9_like(ps: Seq<Literal>) -> Pred { Pred::OfBool(q9_like_call(ps)) }

/// WHERE: the key equalities, then the `LIKE`.
pub open spec fn q9_pred(ps: Seq<Literal>) -> Pred { Pred::And(Box::new(q9_eqs()), Box::new(q9_like(ps))) }

/// FROM part, supplier, lineitem, partsupp, orders, nation.
pub open spec fn q9_from() -> Query {
    let n51 = Query::Product { left: Box::new(Query::Table(3)), right: Box::new(Query::Table(5)) };
    let n53 = Query::Product { left: Box::new(n51), right: Box::new(Query::Table(0)) };
    let n55 = Query::Product { left: Box::new(n53), right: Box::new(Query::Table(4)) };
    let n57 = Query::Product { left: Box::new(n55), right: Box::new(Query::Table(1)) };
    Query::Product { left: Box::new(n57), right: Box::new(Query::Table(6)) }
}

/// `1 - l_discount` (the integer 1 cast to numeric).
pub open spec fn q9_one_minus() -> Expr {
    let n10 = Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) };
    Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(n10), b: Box::new(Expr::Col(22)) }
}

/// `l_extendedprice * (1 - l_discount)`.
pub open spec fn q9_rev() -> Expr {
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Col(21)), b: Box::new(q9_one_minus()) }
}

/// `ps_supplycost * l_quantity`.
pub open spec fn q9_cost() -> Expr {
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Col(35)), b: Box::new(Expr::Col(20)) }
}

/// `l_extendedprice * (1 - l_discount) - ps_supplycost * l_quantity`.
pub open spec fn q9_amount() -> Expr {
    Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(q9_rev()), b: Box::new(q9_cost()) }
}

/// `EXTRACT(YEAR FROM o_orderdate)`.
pub open spec fn q9_year() -> Expr { Expr::Call { f: ScalarFn::ExtractYear, args: seq![Expr::Col(41)] } }

/// The SELECT list of the subquery `profit`.
pub open spec fn q9_exprs() -> Seq<Expr> { seq![Expr::Col(47), q9_year(), q9_amount()] }

pub open spec fn q9_filter(ps: Seq<Literal>) -> Query { Query::Filter { pred: q9_pred(ps), input: Box::new(q9_from()) } }

pub open spec fn q9_project(ps: Seq<Literal>) -> Query { Query::Project { exprs: q9_exprs(), input: Box::new(q9_filter(ps)) } }

pub open spec fn q9_keys() -> Seq<Expr> { seq![Expr::Col(0), Expr::Col(1)] }

pub open spec fn q9_aggs() -> Seq<Agg> { seq![Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(2) }] }

/// GROUP BY nation, o_year with SUM(amount).
pub open spec fn q9_body(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: q9_keys(), aggs: q9_aggs(), input: Box::new(q9_project(ps)) }
}

/// ORDER BY nation, o_year DESC.
pub open spec fn q9_order_keys() -> Seq<OrderKey> {
    seq![
        OrderKey { col: 0, desc: false, nulls_first: false },
        OrderKey { col: 1, desc: true, nulls_first: true },
    ]
}

/// The statement is this AST, without LIMIT or OFFSET.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures query_spec_at(ps) == (OrderedQuery { body: q9_body(ps), keys: q9_order_keys(), limit: None, offset: 0nat }),
{
}

// ------------------------------------------------------------------------------------------------ joined rows

/// FROM evaluates to the product of the tables.
pub proof fn lemma_eval_from(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures eval_query(db, Seq::empty(), q9_from()) == Ok::<Relation, SqlError>(from6(db)),
{
    lemma_parts_shape(sv, db);
    let e = Seq::<Val>::empty();
    assert(eval_query(db, e, Query::Table(3)) == Ok::<Relation, SqlError>(db.tables[3]));
    assert(eval_query(db, e, Query::Table(5)) == Ok::<Relation, SqlError>(db.tables[5]));
    assert(eval_query(db, e, Query::Table(0)) == Ok::<Relation, SqlError>(db.tables[0]));
    assert(eval_query(db, e, Query::Table(4)) == Ok::<Relation, SqlError>(db.tables[4]));
    assert(eval_query(db, e, Query::Table(1)) == Ok::<Relation, SqlError>(db.tables[1]));
    assert(eval_query(db, e, Query::Table(6)) == Ok::<Relation, SqlError>(db.tables[6]));
    let n51 = Query::Product { left: Box::new(Query::Table(3)), right: Box::new(Query::Table(5)) };
    let n53 = Query::Product { left: Box::new(n51), right: Box::new(Query::Table(0)) };
    let n55 = Query::Product { left: Box::new(n53), right: Box::new(Query::Table(4)) };
    let n57 = Query::Product { left: Box::new(n55), right: Box::new(Query::Table(1)) };
    assert(eval_query(db, e, n51) == Ok::<Relation, SqlError>(from2(db)));
    assert(eval_query(db, e, n53) == Ok::<Relation, SqlError>(from3(db)));
    assert(eval_query(db, e, n55) == Ok::<Relation, SqlError>(from4(db)));
    assert(eval_query(db, e, n57) == Ok::<Relation, SqlError>(from5(db)));
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
pub open spec fn in6(sv: StoresView, p: int, s: int, l: int, q: int, o: int, a: int) -> bool {
    &&& 0 <= p < n_p(sv) && 0 <= s < n_s(sv) && 0 <= l < n_l(sv)
    &&& 0 <= q < n_ps(sv) && 0 <= o < n_o(sv) && 0 <= a < n_n(sv)
}

/// Every joined row is `joined6` of some rows of the six inputs.
pub proof fn lemma_from6_witness(sv: StoresView, db: Database, k: int) -> (w: (int, int, int, int, int, int))
    requires bound_db(sv, db), 0 <= k < from6(db).len(),
    ensures
        in6(sv, w.0, w.1, w.2, w.3, w.4, w.5),
        from6(db)[k] == joined6(db, w.0, w.1, w.2, w.3, w.4, w.5),
{
    lemma_parts_shape(sv, db);
    let (k5, a) = lemma_product_witness(from5(db), db.tables[6], k);
    let (k4, o) = lemma_product_witness(from4(db), db.tables[1], k5);
    let (k3, q) = lemma_product_witness(from3(db), db.tables[4], k4);
    let (k2, l) = lemma_product_witness(from2(db), db.tables[0], k3);
    let (p, s) = lemma_product_witness(db.tables[3], db.tables[5], k2);
    (p, s, l, q, o, a)
}

/// A 50-column row as the statement sees it: the seventeen values it reads are those of the stored rows `p` (part),
/// `s` (supplier), `l` (lineitem), `q` (partsupp), `o` (orders) and `a` (nation).
pub open spec fn shape(sv: StoresView, r: Row, p: int, s: int, l: int, q: int, o: int, a: int) -> bool {
    &&& r.len() == 50
    &&& r[0] == Val::Int(pk(sv)[p] as int) && r[1] == Val::Text(pname(sv, p))
    &&& r[9] == Val::Int(sk(sv)[s] as int) && r[12] == Val::Int(sn(sv)[s] as int)
    &&& r[16] == Val::Int(lok(sv)[l] as int) && r[17] == Val::Int(lpk(sv)[l] as int) && r[18] == Val::Int(lsk(sv)[l] as int)
    &&& r[20] == (Val::Num { coeff: lqt(sv)[l] as int, scale: 2 })
    &&& r[21] == (Val::Num { coeff: lpr(sv)[l] as int, scale: 2 })
    &&& r[22] == (Val::Num { coeff: ldc(sv)[l] as int, scale: 2 })
    &&& r[32] == Val::Int(pspk(sv)[q] as int) && r[33] == Val::Int(pssk(sv)[q] as int)
    &&& r[35] == (Val::Num { coeff: psc(sv)[q] as int, scale: 2 })
    &&& r[37] == Val::Int(ok(sv)[o] as int) && r[41] == date32_val(od(sv)[o])
    &&& r[46] == Val::Int(nk(sv)[a] as int) && r[47] == Val::Text(nname(sv, a))
}

/// The numeric values a joined row of the index tuple reads are inside numeric(15,2).
pub open spec fn shape_nums(sv: StoresView, l: int, q: int) -> bool {
    num15(lqt(sv)[l]) && num15(lpr(sv)[l]) && num15(ldc(sv)[l]) && num15(psc(sv)[q])
}

/// The joined row of an index tuple has the shape, with the stored values.
pub proof fn lemma_joined_shape(sv: StoresView, db: Database, p: int, s: int, l: int, q: int, o: int, a: int)
    requires bound_db(sv, db), in6(sv, p, s, l, q, o, a),
    ensures shape(sv, joined6(db, p, s, l, q, o, a), p, s, l, q, o, a), shape_nums(sv, l, q),
{
    lemma_parts_shape(sv, db);
    lemma_part_row(sv, db, p);
    lemma_supplier_row(sv, db, s);
    lemma_lineitem_row(sv, db, l);
    lemma_partsupp_row(sv, db, q);
    lemma_orders_row(sv, db, o);
    lemma_nation_row(sv, db, a);
    let (rp, rs, rl, rq, ro, ra) = (db.tables[3][p], db.tables[5][s], db.tables[0][l], db.tables[4][q], db.tables[1][o], db.tables[6][a]);
    let r2 = rp + rs;
    let r3 = r2 + rl;
    let r4 = r3 + rq;
    let r5 = r4 + ro;
    let r = r5 + ra;
    assert(r2[0] == rp[0] && r2[1] == rp[1] && r2[9] == rs[0] && r2[12] == rs[3]);
    assert(r3[16] == rl[0] && r3[17] == rl[1] && r3[18] == rl[2] && r3[20] == rl[4] && r3[21] == rl[5] && r3[22] == rl[6]);
    assert(r4[32] == rq[0] && r4[33] == rq[1] && r4[35] == rq[3]);
    assert(r5[37] == ro[0] && r5[41] == ro[4]);
    assert(r[46] == ra[0] && r[47] == ra[1]);
    assert(r3[0] == r2[0] && r3[1] == r2[1] && r3[9] == r2[9] && r3[12] == r2[12]);
    assert(r4[0] == r3[0] && r4[1] == r3[1] && r4[9] == r3[9] && r4[12] == r3[12] && r4[16] == r3[16] && r4[17] == r3[17]
        && r4[18] == r3[18] && r4[20] == r3[20] && r4[21] == r3[21] && r4[22] == r3[22]);
    assert(r5[0] == r4[0] && r5[1] == r4[1] && r5[9] == r4[9] && r5[12] == r4[12] && r5[16] == r4[16] && r5[17] == r4[17]
        && r5[18] == r4[18] && r5[20] == r4[20] && r5[21] == r4[21] && r5[22] == r4[22] && r5[32] == r4[32] && r5[33] == r4[33]
        && r5[35] == r4[35]);
    assert(r[0] == r5[0] && r[1] == r5[1] && r[9] == r5[9] && r[12] == r5[12] && r[16] == r5[16] && r[17] == r5[17]
        && r[18] == r5[18] && r[20] == r5[20] && r[21] == r5[21] && r[22] == r5[22] && r[32] == r5[32] && r[33] == r5[33]
        && r[35] == r5[35] && r[37] == r5[37] && r[41] == r5[41]);
}

/// The projection of a 50-column row onto the read columns.
pub proof fn lemma_joined_proj(r: Row)
    requires r.len() == 50,
    ensures proj(r, q9_cols()) == seq![r[0], r[1], r[9], r[12], r[16], r[17], r[18], r[20], r[21], r[22], r[32], r[33],
        r[35], r[37], r[41], r[46], r[47]],
{
    assert(proj(r, q9_cols()) =~= seq![r[0], r[1], r[9], r[12], r[16], r[17], r[18], r[20], r[21], r[22], r[32], r[33],
        r[35], r[37], r[41], r[46], r[47]]);
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

/// The literal value of the parameter.
pub proof fn lemma_literals(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Text(pat_of(ps))),
{
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

/// The six key equalities on a row of the shape.
pub proof fn lemma_eqs_shape(sv: StoresView, db: Database, r: Row, p: int, s: int, l: int, q: int, o: int, a: int)
    requires shape(sv, r, p, s, l, q, o, a),
    ensures eval_pred(db, r, q9_eqs()) == Ok::<Truth, SqlError>(truth_of(eqs_hold(sv, p, s, l, q, o, a))),
{
    lemma_cols_eq(db, r, 9, 18, sk(sv)[s] as int, lsk(sv)[l] as int);
    lemma_cols_eq(db, r, 33, 18, pssk(sv)[q] as int, lsk(sv)[l] as int);
    lemma_cols_eq(db, r, 32, 17, pspk(sv)[q] as int, lpk(sv)[l] as int);
    lemma_cols_eq(db, r, 0, 17, pk(sv)[p] as int, lpk(sv)[l] as int);
    lemma_cols_eq(db, r, 37, 16, ok(sv)[o] as int, lok(sv)[l] as int);
    lemma_cols_eq(db, r, 12, 46, sn(sv)[s] as int, nk(sv)[a] as int);
    let n20 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(9), b: Expr::Col(18) };
    let n23 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(33), b: Expr::Col(18) };
    let n27 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(32), b: Expr::Col(17) };
    let n31 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(17) };
    let n35 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(37), b: Expr::Col(16) };
    let n39 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(12), b: Expr::Col(46) };
    let e20 = sk(sv)[s] == lsk(sv)[l];
    let e23 = pssk(sv)[q] == lsk(sv)[l];
    let e27 = pspk(sv)[q] == lpk(sv)[l];
    let e31 = pk(sv)[p] == lpk(sv)[l];
    let e35 = ok(sv)[o] == lok(sv)[l];
    let e39 = sn(sv)[s] == nk(sv)[a];
    lemma_pred_and(db, r, n20, n23, e20, e23);
    let n24 = Pred::And(Box::new(n20), Box::new(n23));
    lemma_pred_and(db, r, n24, n27, e20 && e23, e27);
    let n28 = Pred::And(Box::new(n24), Box::new(n27));
    lemma_pred_and(db, r, n28, n31, e20 && e23 && e27, e31);
    let n32 = Pred::And(Box::new(n28), Box::new(n31));
    lemma_pred_and(db, r, n32, n35, e20 && e23 && e27 && e31, e35);
    let n36 = Pred::And(Box::new(n32), Box::new(n35));
    lemma_pred_and(db, r, n36, n39, e20 && e23 && e27 && e31 && e35, e39);
}

/// The key equalities of an index tuple (the stored keys join).
pub open spec fn eqs_hold(sv: StoresView, p: int, s: int, l: int, q: int, o: int, a: int) -> bool {
    &&& sk(sv)[s] == lsk(sv)[l]
    &&& pssk(sv)[q] == lsk(sv)[l]
    &&& pspk(sv)[q] == lpk(sv)[l]
    &&& pk(sv)[p] == lpk(sv)[l]
    &&& ok(sv)[o] == lok(sv)[l]
    &&& sn(sv)[s] == nk(sv)[a]
}

/// The escape string has one character (a backslash), so `like_value` reaches the matcher.
proof fn lemma_esc_chars()
    ensures chars(esc_bytes()).len() == 1,
{
    let b = esc_bytes();
    assert(b.drop_last() =~= Seq::<u8>::empty());
    assert(chars(b.drop_last()) == Seq::<Seq<u8>>::empty());
    assert(!is_cont(b.last()));
}

/// `LIKE` of two texts is a Boolean or the matcher's error.
pub proof fn lemma_like_res(name: Seq<u8>, pat: Seq<u8>)
    ensures
        like_ok(name, pat) ==> like_res(name, pat) == Ok::<Val, SqlError>(Val::Bool(like_true(name, pat))),
{
    lemma_esc_chars();
}

/// The `LIKE` predicate on a row whose `p_name` is `name`: the truth of `like_true`, or the error of `like_res`.
pub proof fn lemma_like_shape(db: Database, ps: Seq<Literal>, r: Row, name: Seq<u8>)
    requires param_domain(ps), r.len() == 50, r[1] == Val::Text(name),
    ensures
        like_ok(name, pat_of(ps)) ==> eval_pred(db, r, q9_like(ps)) == Ok::<Truth, SqlError>(truth_of(like_true(name, pat_of(ps)))),
        !like_ok(name, pat_of(ps)) ==> eval_pred(db, r, q9_like(ps)) == Err::<Truth, SqlError>(like_res(name, pat_of(ps))->Err_0),
{
    let pat = pat_of(ps);
    lemma_literals(ps);
    let args = seq![Expr::Col(1), Expr::Lit(ps[0]), Expr::Lit(Literal::Text(seq![92u8]))];
    lemma_eval_col(db, r, 1);
    lemma_eval_lit(db, r, ps[0]);
    lemma_eval_lit(db, r, Literal::Text(seq![92u8]));
    let vs = seq![Val::Text(name), Val::Text(pat), Val::Text(esc_bytes())];
    lemma_expr_results_index(db, r, args);
    let rs = expr_results(db, r, args);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Val, SqlError>(vs[i]) by {
        assert(rs[i] == eval_expr(db, r, args[i]));
    }
    lemma_collect_all(rs, vs);
    assert(eval_exprs(db, r, args) == Ok::<Row, SqlError>(vs));
    assert(apply_fn(ScalarFn::Like, vs) == like_res(name, pat));
    assert(eval_expr(db, r, q9_like_call(ps)) == like_res(name, pat));
    lemma_like_res(name, pat);
}

/// The WHERE condition on a row of the shape: the truth of the equalities and the `LIKE` when the `LIKE` does not
/// raise, else the `LIKE`'s error (the equalities evaluate first and never fail).
pub proof fn lemma_pred_shape(sv: StoresView, db: Database, ps: Seq<Literal>, r: Row, p: int, s: int, l: int, q: int, o: int, a: int)
    requires param_domain(ps), shape(sv, r, p, s, l, q, o, a),
    ensures
        like_ok(pname(sv, p), pat_of(ps)) ==> eval_pred(db, r, q9_pred(ps)) == Ok::<Truth, SqlError>(truth_of(
            eqs_hold(sv, p, s, l, q, o, a) && like_true(pname(sv, p), pat_of(ps)))),
        !like_ok(pname(sv, p), pat_of(ps)) ==> eval_pred(db, r, q9_pred(ps))
            == Err::<Truth, SqlError>(like_res(pname(sv, p), pat_of(ps))->Err_0),
{
    lemma_eqs_shape(sv, db, r, p, s, l, q, o, a);
    lemma_like_shape(db, ps, r, pname(sv, p));
    if like_ok(pname(sv, p), pat_of(ps)) {
        lemma_pred_and(db, r, q9_eqs(), q9_like(ps), eqs_hold(sv, p, s, l, q, o, a), like_true(pname(sv, p), pat_of(ps)));
    }
}

/// `EXTRACT(YEAR FROM o_orderdate)` on a row of the shape.
proof fn lemma_year_shape(db: Database, r: Row, d: int)
    requires r.len() == 50, r[41] == Val::Date(d),
    ensures eval_expr(db, r, q9_year()) == Ok::<Val, SqlError>(year_val(Val::Date(d))),
{
    let args = seq![Expr::Col(41)];
    lemma_eval_col(db, r, 41);
    lemma_expr_results_index(db, r, args);
    lemma_collect_all(expr_results(db, r, args), seq![Val::Date(d)]);
    assert(eval_exprs(db, r, args) == Ok::<Row, SqlError>(seq![Val::Date(d)]));
    assert(apply_fn(ScalarFn::ExtractYear, seq![Val::Date(d)]) == apply_extract(ScalarFn::ExtractYear, seq![Val::Date(d)]));
}

/// `l_extendedprice * (1 - l_discount) - ps_supplycost * l_quantity` on a row of the shape (numeric(15,2) values).
proof fn lemma_amount_shape(db: Database, r: Row, price: int, disc: int, cost: int, qty: int)
    requires
        r.len() == 50,
        r[21] == (Val::Num { coeff: price, scale: 2 }), r[22] == (Val::Num { coeff: disc, scale: 2 }),
        r[35] == (Val::Num { coeff: cost, scale: 2 }), r[20] == (Val::Num { coeff: qty, scale: 2 }),
        abs(price) < pow10(15), abs(disc) < pow10(15), abs(cost) < pow10(15), abs(qty) < pow10(15),
    ensures eval_expr(db, r, q9_amount()) == Ok::<Val, SqlError>(Val::Num { coeff: amount(price, disc, cost, qty), scale: 4 }),
{
    let one = Literal::Int { v: 1, kind: IntKind::Int4 };
    let n10 = Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(one)) };
    assert(lit_val(one) == Ok::<Val, SqlError>(Val::Int(1)));
    lemma_eval_lit(db, r, one);
    assert(eval_expr(db, r, n10) == Ok::<Val, SqlError>(Val::Num { coeff: 1, scale: 0 }));
    lemma_eval_col(db, r, 20);
    lemma_eval_col(db, r, 21);
    lemma_eval_col(db, r, 22);
    lemma_eval_col(db, r, 35);
    assert(pow10(1) == 10 && pow10(2) == 100 && pow10(0) == 1) by (compute);
    assert(crate::spec::limits::numeric_int_digits_max() >= 100) by (compute);
    lemma_node_add(db, r, ArithOp::Sub, n10, Expr::Col(22), 1, 0, 1, disc, 2, 15, 2, 100, 1, 16);
    assert(1 * 100 - disc * 1 == 100 - disc);
    lemma_node_mul(db, r, Expr::Col(21), q9_one_minus(), price, 2, 15, 100 - disc, 2, 16);
    lemma_node_mul(db, r, Expr::Col(35), Expr::Col(20), cost, 2, 15, qty, 2, 15);
    lemma_node_add(db, r, ArithOp::Sub, q9_rev(), q9_cost(), price * (100 - disc), 4, 31, cost * qty, 4, 30, 4, 1, 1, 32);
    assert(price * (100 - disc) * 1 - cost * qty * 1 == amount(price, disc, cost, qty));
}

/// Three values of three expressions: the list evaluates to them.
proof fn lemma_eval_three(db: Database, r: Row, es: Seq<Expr>, vs: Row)
    requires
        es.len() == 3, vs.len() == 3,
        eval_expr(db, r, es[0]) == Ok::<Val, SqlError>(vs[0]),
        eval_expr(db, r, es[1]) == Ok::<Val, SqlError>(vs[1]),
        eval_expr(db, r, es[2]) == Ok::<Val, SqlError>(vs[2]),
    ensures eval_exprs(db, r, es) == Ok::<Row, SqlError>(vs),
{
    lemma_expr_results_index(db, r, es);
    let rs = expr_results(db, r, es);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Val, SqlError>(vs[i]) by {
        assert(rs[i] == eval_expr(db, r, es[i]));
    }
    lemma_collect_all(rs, vs);
}

/// The SELECT row of a row of the shape.
pub open spec fn shape_select(sv: StoresView, l: int, q: int, o: int, a: int) -> Row {
    seq![Val::Text(nname(sv, a)), year_val(date32_val(od(sv)[o])),
        Val::Num { coeff: amount(lpr(sv)[l] as int, ldc(sv)[l] as int, psc(sv)[q] as int, lqt(sv)[l] as int), scale: 4 }]
}

/// The normal form's SELECT row of a row of the shape.
pub proof fn lemma_select_of_shape(sv: StoresView, r: Row, p: int, s: int, l: int, q: int, o: int, a: int)
    requires shape(sv, r, p, s, l, q, o, a),
    ensures select_of(r) == shape_select(sv, l, q, o, a),
{
    lemma_joined_proj(r);
    assert(select_of(r) =~= shape_select(sv, l, q, o, a));
}

/// The SELECT list on a row of the shape.
pub proof fn lemma_exprs_shape(sv: StoresView, db: Database, r: Row, p: int, s: int, l: int, q: int, o: int, a: int)
    requires shape(sv, r, p, s, l, q, o, a), shape_nums(sv, l, q),
    ensures eval_exprs(db, r, q9_exprs()) == Ok::<Row, SqlError>(select_of(r)),
{
    let es = q9_exprs();
    let vs = shape_select(sv, l, q, o, a);
    assert(pow10(15) == 1_000_000_000_000_000) by (compute);
    lemma_eval_col(db, r, 47);
    lemma_year_shape(db, r, od(sv)[o] as int - 10957);
    lemma_amount_shape(db, r, lpr(sv)[l] as int, ldc(sv)[l] as int, psc(sv)[q] as int, lqt(sv)[l] as int);
    assert(es[0] == Expr::Col(47) && es[1] == q9_year() && es[2] == q9_amount());
    lemma_eval_three(db, r, es, vs);
    lemma_select_of_shape(sv, r, p, s, l, q, o, a);
}

// ------------------------------------------------------------------------------------------------ WHERE and SELECT

/// The joined row of an index tuple, projected: the normal form's WHERE is the stored condition, and its SELECT row.
pub proof fn lemma_qual_joined(sv: StoresView, db: Database, ps: Seq<Literal>, p: int, s: int, l: int, q: int, o: int, a: int)
    requires bound_db(sv, db), in6(sv, p, s, l, q, o, a),
    ensures
        qual_row(ps, joined6(db, p, s, l, q, o, a)) == (eqs_hold(sv, p, s, l, q, o, a) && like_true(pname(sv, p), pat_of(ps))),
        select_of(joined6(db, p, s, l, q, o, a)) == shape_select(sv, l, q, o, a),
{
    let r = joined6(db, p, s, l, q, o, a);
    lemma_joined_shape(sv, db, p, s, l, q, o, a);
    lemma_joined_proj(r);
    lemma_select_of_shape(sv, r, p, s, l, q, o, a);
}

/// No joined row's `LIKE` raises: FROM is empty, or no part name raises.
pub open spec fn likes_ok(sv: StoresView, db: Database, ps: Seq<Literal>) -> bool {
    from6(db).len() == 0 || forall|p: int| 0 <= p < n_p(sv) ==> #[trigger] like_ok(pname(sv, p), pat_of(ps))
}

/// WHERE agrees with the normal form on every joined row (when no `LIKE` raises).
pub proof fn lemma_pred_agrees(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps), likes_ok(sv, db, ps),
    ensures pred_agrees(db, from6(db), q9_cols(), q9_pred(ps), g1(ps)),
{
    let rows = from6(db);
    let g = g1(ps);
    assert forall|k: int| 0 <= k < rows.len() implies
        eval_pred(db, #[trigger] rows[k], q9_pred(ps)) == Ok::<Truth, SqlError>(truth_of((g.qual)(proj(rows[k], q9_cols())))) by {
        let (p, s, l, q, o, a) = lemma_from6_witness(sv, db, k);
        lemma_joined_shape(sv, db, p, s, l, q, o, a);
        let r = joined6(db, p, s, l, q, o, a);
        assert(like_ok(pname(sv, p), pat_of(ps)));
        lemma_pred_shape(sv, db, ps, r, p, s, l, q, o, a);
        lemma_qual_joined(sv, db, ps, p, s, l, q, o, a);
    }
}

/// The rows the WHERE keeps.
pub open spec fn kept(db: Database, ps: Seq<Literal>) -> Seq<Row> {
    keep_true(from6(db), qual_truths(g1(ps), proj_all(from6(db), q9_cols())))
}

/// The SELECT rows of the subquery `profit`: `select_of` of every kept row.
pub open spec fn sel_rows(db: Database, ps: Seq<Literal>) -> Seq<Row> {
    kept(db, ps).map_values(|r: Row| select_of(r))
}

/// The WHERE keeps `kept(db, ps)`: joined rows (of some index tuple) that qualify.
pub proof fn lemma_eval_filter(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps), likes_ok(sv, db, ps),
    ensures
        eval_query(db, Seq::empty(), q9_filter(ps)) == Ok::<Relation, SqlError>(kept(db, ps)),
        forall|i: int| 0 <= i < kept(db, ps).len() ==> from6(db).contains(#[trigger] kept(db, ps)[i])
            && qual_row(ps, kept(db, ps)[i]),
{
    lemma_eval_from(sv, db);
    lemma_pred_agrees(sv, db, ps);
    lemma_filter_rows(db, q9_from(), from6(db), q9_cols(), q9_pred(ps), g1(ps));
    lemma_kept_rows(g1(ps), from6(db), q9_cols());
}

/// The SELECT list evaluates on every kept row.
pub proof fn lemma_eval_project(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps), likes_ok(sv, db, ps),
    ensures eval_query(db, Seq::empty(), q9_project(ps)) == Ok::<Relation, SqlError>(sel_rows(db, ps)),
{
    lemma_eval_filter(sv, db, ps);
    let ks = kept(db, ps);
    let ctx = Seq::<Val>::empty();
    let rs = Seq::new(ks.len(), |i: int| eval_exprs(db, ctx + ks[i], q9_exprs()));
    let vs = sel_rows(db, ps);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(vs[i]) by {
        assert(ctx + ks[i] =~= ks[i]);
        assert(from6(db).contains(ks[i]));
        let k = choose|k: int| 0 <= k < from6(db).len() && from6(db)[k] == ks[i];
        let (p, s, l, q, o, a) = lemma_from6_witness(sv, db, k);
        lemma_joined_shape(sv, db, p, s, l, q, o, a);
        lemma_exprs_shape(sv, db, ks[i], p, s, l, q, o, a);
    }
    lemma_collect_all(rs, vs);
    crate::exec::relational::domain::lemma_collect_pointwise::<Row>();
}

// ------------------------------------------------------------------------------------------------ GROUP BY

/// Every SELECT row has three columns: a name, a year at scale 0, an amount at scale 4.
pub open spec fn sel_row_ok(x: Row) -> bool {
    &&& x.len() == 3
    &&& x[0] is Text
    &&& x[1] is Num && x[1]->Num_scale == 0
    &&& x[2] is Num && x[2]->Num_scale == 4
}

pub proof fn lemma_shape_select_ok(sv: StoresView, l: int, q: int, o: int, a: int)
    ensures sel_row_ok(shape_select(sv, l, q, o, a)),
{
}

pub proof fn lemma_sel_rows_ok(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps), likes_ok(sv, db, ps),
    ensures forall|i: int| 0 <= i < sel_rows(db, ps).len() ==> sel_row_ok(#[trigger] sel_rows(db, ps)[i]),
{
    lemma_eval_filter(sv, db, ps);
    let ks = kept(db, ps);
    assert forall|i: int| 0 <= i < sel_rows(db, ps).len() implies sel_row_ok(#[trigger] sel_rows(db, ps)[i]) by {
        assert(from6(db).contains(ks[i]));
        let k = choose|k: int| 0 <= k < from6(db).len() && from6(db)[k] == ks[i];
        let (p, s, l, q, o, a) = lemma_from6_witness(sv, db, k);
        lemma_qual_joined(sv, db, ps, p, s, l, q, o, a);
        lemma_shape_select_ok(sv, l, q, o, a);
    }
}

/// Projecting the SELECT rows on all three columns keeps them.
pub proof fn lemma_sel_proj(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps), likes_ok(sv, db, ps),
    ensures proj_all(sel_rows(db, ps), c3()) == sel_rows(db, ps),
{
    let xs = sel_rows(db, ps);
    lemma_sel_rows_ok(sv, db, ps);
    lemma_proj_all_index(xs, c3());
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] proj_all(xs, c3())[i] == xs[i] by {
        assert(xs[i].len() == 3);
        assert(proj(xs[i], c3()) =~= xs[i]);
    }
    assert(proj_all(xs, c3()) =~= xs);
}

/// GROUP BY keys agree with `g2` on rows of the SELECT shape.
proof fn lemma_keys_agree(db: Database, xs: Seq<Row>)
    requires forall|i: int| 0 <= i < xs.len() ==> sel_row_ok(#[trigger] xs[i]),
    ensures keys_agree(db, xs, c3(), q9_keys(), g2()),
{
    let g = g2();
    assert forall|i: int| 0 <= i < xs.len() && (g.qual)(proj(#[trigger] xs[i], c3())) implies
        eval_exprs(db, xs[i], q9_keys()) == Ok::<Row, SqlError>((g.key)(proj(xs[i], c3()))) by {
        let x = xs[i];
        assert(sel_row_ok(x));
        assert(proj(x, c3()) =~= x);
        let idxs = seq![0nat, 1];
        assert(col_exprs(idxs) =~= q9_keys());
        lemma_eval_cols(db, x, idxs);
        assert(select(x, idxs) =~= seq![x[0], x[1]]);
    }
}

/// The SUM argument agrees with `g2` on rows of the SELECT shape.
proof fn lemma_args_agree(db: Database, xs: Seq<Row>)
    requires forall|i: int| 0 <= i < xs.len() ==> sel_row_ok(#[trigger] xs[i]),
    ensures args_agree(db, xs, c3(), q9_aggs(), g2()),
{
    let g = g2();
    assert forall|i: int| 0 <= i < xs.len() && (g.qual)(proj(#[trigger] xs[i], c3())) implies
        agg_args(db, xs[i], q9_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(xs[i], c3()))) by {
        let x = xs[i];
        assert(sel_row_ok(x));
        assert(proj(x, c3()) =~= x);
        let rs = agg_arg_results(db, x, q9_aggs());
        lemma_agg_arg_results_index(db, x, q9_aggs());
        lemma_eval_col(db, x, 2);
        let vs = seq![Val::Num { coeff: coeff_of(x[2]), scale: 4 }];
        assert(rs[0] == agg_arg(db, x, q9_aggs()[0]));
        assert(rs[0] == Ok::<Val, SqlError>(vs[0]));
        lemma_collect_all(rs, vs);
        assert(arg_vals(g, x) =~= vs);
    }
}

/// On rows of the SELECT shape SQL "not distinct" of the keys is equality (text, numeric scale 0).
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
            if t == 0 {} else {}
        }
        lemma_row_exact(ka, kb);
    }
}

/// GROUP BY keys and arguments agree with `g2` on every SELECT row; the keys are exact.
pub proof fn lemma_group_premises(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps), likes_ok(sv, db, ps),
    ensures
        keys_agree(db, sel_rows(db, ps), c3(), q9_keys(), g2()),
        args_agree(db, sel_rows(db, ps), c3(), q9_aggs(), g2()),
        aggs_match(q9_aggs(), g2()),
        keys_exact(g2(), proj_all(sel_rows(db, ps), c3())),
{
    let xs = sel_rows(db, ps);
    lemma_sel_rows_ok(sv, db, ps);
    lemma_sel_proj(sv, db, ps);
    lemma_keys_agree(db, xs);
    lemma_args_agree(db, xs);
    lemma_keys_exact(xs);
    assert(agg_matches(q9_aggs()[0], g2().aggs[0]));
}

/// The GROUP BY rows: the full row of every group key, in first-occurrence order (inside the arithmetic domain).
pub proof fn lemma_group_eval(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps), likes_ok(sv, db, ps), group_caps(g2(), sel_rows(db, ps)),
    ensures eval_query(db, Seq::empty(), q9_body(ps)) == Ok::<Relation, SqlError>(
        gkeys(g2(), sel_rows(db, ps)).map_values(|k: Row| full_row(g2(), sel_rows(db, ps), k))),
{
    let xs = sel_rows(db, ps);
    let g = g2();
    lemma_eval_project(sv, db, ps);
    lemma_sel_proj(sv, db, ps);
    assert forall|x: Row| #[trigger] (g.qual)(x) by {}
    lemma_table_rows(db, q9_project(ps), xs, c3(), g);
    lemma_group_premises(sv, db, ps);
    lemma_group_query(db, xs, c3(), q9_project(ps), q9_keys(), q9_aggs(), g);
}

/// The body of the statement evaluates to the normal form's result rows (inside `group_caps`, no `LIKE` error).
pub proof fn lemma_denotation(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps), likes_ok(sv, db, ps), group_caps(g2(), sel_rows(db, ps)),
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
        assert(k.len() == 2);
        let fr = full_row(g, xs, k);
        assert(agg_outs(g, xs, k).len() == 1);
        assert(fr.len() == 3);
        lemma_select_identity(fr, g.outs);
    }
    assert(res =~= full);
}

} // verus!
