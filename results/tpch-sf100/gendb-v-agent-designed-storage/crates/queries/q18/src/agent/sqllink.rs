//! The relational link of Q18: the FROM product `customer x orders x lineitem` of a database bound to the parts,
//! projected on the eight columns the statement reads (`q18_cols`), is the product of the model's rows (`jrow`);
//! sums over it are triple index sums over the model (`lemma_sum_xs`). With the normal form `q18_g` (WHERE, group
//! key and SUM argument of `link::query::QuerySpec`; the WHERE's IN subquery is `qspec::big`), a group accumulator
//! is a sum over the (customer, order) pairs whose key is the group's, times the order's lineitem sum
//! (`lemma_acc`); under the orders and customer primary keys only the order the key names and its customer
//! contribute (`lemma_collapse`), so the groups are exactly the good orders of `qspec` (`lemma_groups_link`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::{abs, pow10};
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::product_rows;
use crate::link::query::*;
use crate::link::join::{sum_of, shift, lemma_sum_of_product, lemma_sum_of_ext, lemma_proj_product,
    lemma_acc_sum_of, count_term, sum_term, abs_term};
use crate::link::expr::{ival, i128_max};
use crate::bridge::relation::{is_concat, lemma_product_rows_elems};
use crate::stores::liruns::interface::common::colfmt as ff;
use super::common::isum::*;
use super::model::*;
use super::qspec::*;
use super::rels::*;
use super::sqlrow::*;

verus! {

// ------------------------------------------------------------------------------------------------ the FROM rows

/// Positions read in the joined row: c_custkey, c_name | o_orderkey, o_custkey, o_totalprice, o_orderdate |
/// l_orderkey, l_quantity.
pub open spec fn q18_cols() -> Seq<nat> {
    seq![0nat, 1, 8, 9, 11, 12, 17, 21]
}

pub open spec fn from_rows(db: Database) -> Seq<Row> {
    product_rows(product_rows(db.tables[2], db.tables[1]), db.tables[0])
}

/// The projected FROM rows.
pub open spec fn q18_xs(db: Database) -> Seq<Row> {
    proj_all(from_rows(db), q18_cols())
}

/// A joined model row: customer row `c`, orders position `q`, lineitem row `j` (8 columns).
pub open spec fn jrow(m: M, c: int, q: int, j: int) -> Row {
    crow(m, c) + orow(m, q) + lrow(m, j)
}

pub proof fn lemma_from_eval(db: Database)
    requires db.tables.len() == 8,
    ensures eval_query(db, Seq::empty(), q18_from()) == Ok::<Relation, SqlError>(from_rows(db)),
{
    let e = Seq::<Val>::empty();
    let t2 = Query::Table(2);
    let t1 = Query::Table(1);
    let t0 = Query::Table(0);
    assert(eval_query(db, e, t2) == Ok::<Relation, SqlError>(db.tables[2]));
    assert(eval_query(db, e, t1) == Ok::<Relation, SqlError>(db.tables[1]));
    assert(eval_query(db, e, t0) == Ok::<Relation, SqlError>(db.tables[0]));
    let p21 = Query::Product { left: Box::new(t2), right: Box::new(t1) };
    assert(eval_query(db, e, p21) == Ok::<Relation, SqlError>(product_rows(db.tables[2], db.tables[1])));
    assert(q18_from() == Query::Product { left: Box::new(p21), right: Box::new(t0) });
}

/// The projected FROM rows are the product of the projected tables.
pub proof fn lemma_xs_product(db: Database)
    requires db_ok(db),
    ensures q18_xs(db) == product_rows(product_rows(crel(db), orel(db)), lrel(db)),
{
    lemma_widths(db);
    let (t2, t1, t0) = (db.tables[2], db.tables[1], db.tables[0]);
    let ca = ccols() + shift(ocols(), 8);
    lemma_proj_product(t2, t1, ccols(), ocols(), 8, 9);
    let a = product_rows(t2, t1);
    lemma_product_rows_elems(t2, t1);
    assert forall|i: int| 0 <= i < a.len() implies (#[trigger] a[i]).len() == 17 by {
        assert(is_concat(a[i], t2, t1));
        let (x, y) = choose|x: int, y: int| 0 <= x < t2.len() && 0 <= y < t1.len() && a[i] == #[trigger] t2[x] + #[trigger] t1[y];
    }
    assert forall|k: int| 0 <= k < ca.len() implies #[trigger] ca[k] < 17 by {}
    lemma_proj_product(a, t0, ca, lcols(), 17, 16);
    assert(ca + shift(lcols(), 17) =~= q18_cols());
}

/// A FROM row: one row of each table, read through the model.
pub proof fn lemma_from_row(db: Database, m: M, i: int) -> (r: (int, int, int))
    requires
        db_ok(db),
        rel_ok(m, db),
        0 <= i < from_rows(db).len(),
    ensures ({
        let (c, q, j) = r;
        let env = from_rows(db)[i];
        &&& 0 <= c < m.c_n && 0 <= q < m.o_n && 0 <= j < m.l_n
        &&& env.len() == 33
        &&& env[0] == Val::Int(ckey(m, c))
        &&& env[1] == Val::Text(cname(m, c))
        &&& env[8] == Val::Int(okey(m, q))
        &&& env[9] == Val::Int(ocust(m, q))
        &&& env[11] == (Val::Num { coeff: otp(m, q), scale: 2 })
        &&& env[12] == Val::Date(odate(m, q))
        &&& env[17] == Val::Int(lkey(m, j))
        &&& env[21] == (Val::Num { coeff: lqty(m, j), scale: 2 })
        &&& proj(env, q18_cols()) == jrow(m, c, q, j)
    }),
{
    lemma_widths(db);
    let (t2, t1, t0) = (db.tables[2], db.tables[1], db.tables[0]);
    let a = product_rows(t2, t1);
    lemma_product_rows_elems(a, t0);
    let env = from_rows(db)[i];
    assert(is_concat(env, a, t0));
    let (ai, l) = choose|x: int, y: int| 0 <= x < a.len() && 0 <= y < t0.len() && env == #[trigger] a[x] + #[trigger] t0[y];
    lemma_product_rows_elems(t2, t1);
    assert(is_concat(a[ai], t2, t1));
    let (c, b) = choose|x: int, y: int| 0 <= x < t2.len() && 0 <= y < t1.len() && a[ai] == #[trigger] t2[x] + #[trigger] t1[y];
    assert(ff::covered(m.o_map, b));
    let q = choose|q: int| 0 <= q < m.o_map.len() && m.o_map[q] == b;
    assert(ff::covered(m.l_map, l));
    let j = choose|j: int| 0 <= j < m.l_map.len() && m.l_map[j] == l;
    let (rc, ro, rl) = (t2[c], t1[b], t0[l]);
    assert(proj(rc, ccols()) == crow(m, c));
    assert(proj(ro, ocols()) == orow(m, q));
    assert(proj(rl, lcols()) == lrow(m, j));
    assert(proj(rc, ccols())[0] == rc[0] && proj(rc, ccols())[1] == rc[1]);
    assert(proj(ro, ocols())[0] == ro[0] && proj(ro, ocols())[1] == ro[1] && proj(ro, ocols())[2] == ro[3] && proj(ro, ocols())[3] == ro[4]);
    assert(proj(rl, lcols())[0] == rl[0] && proj(rl, lcols())[1] == rl[4]);
    assert(env == rc + ro + rl);
    assert(env[0] == rc[0] && env[1] == rc[1]);
    assert(env[8] == ro[0] && env[9] == ro[1] && env[11] == ro[3] && env[12] == ro[4]);
    assert(env[17] == rl[0] && env[21] == rl[4]);
    assert(proj(env, q18_cols()) =~= jrow(m, c, q, j));
    (c, q, j)
}

/// Inner sums of the triple sum.
pub open spec fn s_l(m: M, f: spec_fn(Row) -> int, a: Row) -> int {
    isum(m.l_n, |j: int| f(a + lrow(m, j)))
}

pub open spec fn s_ol(m: M, f: spec_fn(Row) -> int, x: Row) -> int {
    isum(m.o_n, |q: int| s_l(m, f, x + orow(m, q)))
}

/// A sum over the projected FROM rows is the triple index sum over the model.
pub proof fn lemma_sum_xs(db: Database, m: M, f: spec_fn(Row) -> int)
    requires db_ok(db), rel_ok(m, db),
    ensures sum_of(q18_xs(db), f) == isum(m.c_n, |c: int| s_ol(m, f, crow(m, c))),
{
    lemma_xs_product(db);
    let (cr, orr, lr) = (crel(db), orel(db), lrel(db));
    let a = product_rows(cr, orr);
    lemma_sum_of_product(a, lr, f);
    let h1 = |x: Row| sum_of(lr, |y: Row| f(x + y));
    let h2 = |x: Row| s_l(m, f, x);
    assert forall|i: int| 0 <= i < a.len() implies h1(#[trigger] a[i]) == h2(a[i]) by {
        let x = a[i];
        lemma_sum_l(db, m, |y: Row| f(x + y));
        lemma_isum_ext(m.l_n, |j: int| (|y: Row| f(x + y))(lrow(m, j)), |j: int| f(x + lrow(m, j)));
    }
    lemma_sum_of_ext(a, h1, h2);
    lemma_sum_of_product(cr, orr, h2);
    let h3 = |x: Row| sum_of(orr, |y: Row| h2(x + y));
    let h4 = |x: Row| s_ol(m, f, x);
    assert forall|i: int| 0 <= i < cr.len() implies h3(#[trigger] cr[i]) == h4(cr[i]) by {
        let x = cr[i];
        lemma_sum_o(db, m, |y: Row| h2(x + y));
        lemma_isum_ext(m.o_n, |q: int| (|y: Row| h2(x + y))(orow(m, q)), |q: int| s_l(m, f, x + orow(m, q)));
    }
    lemma_sum_of_ext(cr, h3, h4);
    lemma_sum_c(db, m, h4);
    lemma_isum_ext(m.c_n, |c: int| h4(crow(m, c)), |c: int| s_ol(m, f, crow(m, c)));
}

// ------------------------------------------------------------------------------------------------ the normal form

/// WHERE over the projected row: the IN subquery (`big` of o_orderkey), c_custkey = o_custkey, o_orderkey =
/// l_orderkey (two-valued: every read value is non-NULL and typed).
pub open spec fn q18_qual(m: M, p: QP) -> spec_fn(Row) -> bool {
    |x: Row| big(m, p, ival(x[2])) && ival(x[0]) == ival(x[3]) && ival(x[2]) == ival(x[6])
}

/// GROUP BY c_name, c_custkey, o_orderkey, o_orderdate, o_totalprice over the projected row.
pub open spec fn q18_key() -> spec_fn(Row) -> Row {
    |x: Row| seq![x[1], x[0], x[2], x[5], x[4]]
}

/// The SUM argument's coefficient (scale 2) over the projected row.
pub open spec fn q18_argf() -> spec_fn(int, Row) -> int {
    |j: int, x: Row| ival(x[7])
}

/// The GROUP BY row is the output row.
pub open spec fn q18_outs() -> Seq<nat> {
    seq![0nat, 1, 2, 3, 4, 5]
}

/// Q18 in the accumulator normal form of `link::query`.
pub open spec fn q18_g(m: M, p: QP) -> QuerySpec {
    QuerySpec { qual: q18_qual(m, p), key: q18_key(), arg: q18_argf(), aggs: seq![AggKind::Sum { scale: 2 }], outs: q18_outs(), grouped: true }
}

/// The group key of customer row `c` with the order at `q`.
pub open spec fn keyrow(m: M, c: int, q: int) -> Row {
    seq![Val::Text(cname(m, c)), Val::Int(ckey(m, c)), Val::Int(okey(m, q)), Val::Date(odate(m, q)), Val::Num { coeff: otp(m, q), scale: 2 }]
}

/// Customer row `c` and the order at `q` join, the order key is big and the pair's key is `k`.
pub open spec fn pair(m: M, p: QP, k: Row, c: int, q: int) -> bool {
    big(m, p, okey(m, q)) && ckey(m, c) == ocust(m, q) && keyrow(m, c, q) == k
}

/// On a joined model row the normal form's hit and argument read the model.
pub proof fn lemma_term(m: M, p: QP, k: Row, c: int, q: int, j: int)
    ensures
        hit(q18_g(m, p), jrow(m, c, q, j), k) == (pair(m, p, k, c, q) && lkey(m, j) == okey(m, q)),
        (q18_g(m, p).arg)(0, jrow(m, c, q, j)) == lqty(m, j),
        (q18_g(m, p).qual)(jrow(m, c, q, j)) == (big(m, p, okey(m, q)) && ckey(m, c) == ocust(m, q) && okey(m, q) == lkey(m, j)),
        (q18_g(m, p).key)(jrow(m, c, q, j)) == keyrow(m, c, q),
{
    let x = jrow(m, c, q, j);
    assert(x[0] == Val::Int(ckey(m, c)) && x[1] == Val::Text(cname(m, c)));
    assert(x[2] == Val::Int(okey(m, q)) && x[3] == Val::Int(ocust(m, q)));
    assert(x[4] == (Val::Num { coeff: otp(m, q), scale: 2 }) && x[5] == Val::Date(odate(m, q)));
    assert(x[6] == Val::Int(lkey(m, j)) && x[7] == (Val::Num { coeff: lqty(m, j), scale: 2 }));
    assert((q18_g(m, p).key)(x) =~= keyrow(m, c, q));
}

// ------------------------------------------------------------------------------------------------ factoring

/// The weight `w` summed over the lineitem rows of the order at `q`.
pub open spec fn lw(m: M, q: int, w: spec_fn(int) -> int) -> int {
    isum(m.l_n, |j: int| if lkey(m, j) == okey(m, q) { w(j) } else { 0int })
}

/// The term of the triple sum for a lineitem weight `w`.
pub open spec fn tw(m: M, p: QP, k: Row, w: spec_fn(int) -> int, c: int, q: int, j: int) -> int {
    if pair(m, p, k, c, q) && lkey(m, j) == okey(m, q) { w(j) } else { 0 }
}

/// Inner sums of the factorization (named, so that they can be quantifier triggers).
pub open spec fn t_j(m: M, p: QP, k: Row, w: spec_fn(int) -> int, c: int, q: int) -> int {
    isum(m.l_n, |j: int| tw(m, p, k, w, c, q, j))
}

pub open spec fn t_qj(m: M, p: QP, k: Row, w: spec_fn(int) -> int, c: int) -> int {
    isum(m.o_n, |q: int| t_j(m, p, k, w, c, q))
}

pub open spec fn a_cq(m: M, p: QP, k: Row, w: spec_fn(int) -> int, c: int, q: int) -> int {
    if pair(m, p, k, c, q) { lw(m, q, w) } else { 0int }
}

pub open spec fn a_q(m: M, p: QP, k: Row, w: spec_fn(int) -> int, c: int) -> int {
    isum(m.o_n, |q: int| a_cq(m, p, k, w, c, q))
}

/// The order position a group key names.
pub open spec fn qk(m: M, k: Row) -> int {
    opos(m, ival(k[2]))
}

/// The value of a group accumulator: the named order's lineitem sum, when its customer and key pair up.
pub open spec fn total(m: M, p: QP, k: Row, w: spec_fn(int) -> int) -> int {
    let q0 = qk(m, k);
    let c0 = cpos(m, ocust(m, q0));
    if 0 <= q0 < m.o_n && 0 <= c0 < m.c_n && pair(m, p, k, c0, q0) { lw(m, q0, w) } else { 0 }
}

/// The triple sum over pairs: per (customer, order) the order's lineitem sum.
proof fn lemma_factor(m: M, p: QP, k: Row, w: spec_fn(int) -> int)
    ensures isum(m.c_n, |c: int| t_qj(m, p, k, w, c)) == isum(m.c_n, |c: int| a_q(m, p, k, w, c)),
{
    assert forall|c: int| 0 <= c < m.c_n implies #[trigger] t_qj(m, p, k, w, c) == a_q(m, p, k, w, c) by {
        assert forall|q: int| 0 <= q < m.o_n implies #[trigger] t_j(m, p, k, w, c, q) == a_cq(m, p, k, w, c, q) by {
            if pair(m, p, k, c, q) {
                lemma_isum_ext(m.l_n, |j: int| tw(m, p, k, w, c, q, j), |j: int| if lkey(m, j) == okey(m, q) { w(j) } else { 0int });
            } else {
                lemma_isum_zero(m.l_n, |j: int| tw(m, p, k, w, c, q, j));
            }
        }
        lemma_isum_ext(m.o_n, |q: int| t_j(m, p, k, w, c, q), |q: int| a_cq(m, p, k, w, c, q));
    }
    lemma_isum_ext(m.c_n, |c: int| t_qj(m, p, k, w, c), |c: int| a_q(m, p, k, w, c));
}

/// Under the primary keys only the order the key names and its customer contribute.
pub proof fn lemma_collapse(m: M, p: QP, k: Row, w: spec_fn(int) -> int)
    requires model_ok(m),
    ensures isum(m.c_n, |c: int| a_q(m, p, k, w, c)) == total(m, p, k, w),
{
    let q0 = qk(m, k);
    let c0 = cpos(m, ocust(m, q0));
    // over orders: only q0
    assert forall|c: int| 0 <= c < m.c_n implies #[trigger] a_q(m, p, k, w, c)
        == (if 0 <= q0 < m.o_n { a_cq(m, p, k, w, c, q0) } else { 0int }) by {
        let f = |q: int| a_cq(m, p, k, w, c, q);
        assert forall|q: int| 0 <= q < m.o_n && q != q0 implies #[trigger] f(q) == 0 by {
            if pair(m, p, k, c, q) {
                assert(keyrow(m, c, q)[2] == Val::Int(okey(m, q)));
                assert(ival(k[2]) == okey(m, q));
                crate::agent::facts::lemma_opos(m, okey(m, q));
            }
        }
        lemma_isum_single(m.o_n, f, q0);
    }
    let g = |c: int| if 0 <= q0 < m.o_n { a_cq(m, p, k, w, c, q0) } else { 0int };
    lemma_isum_ext(m.c_n, |c: int| a_q(m, p, k, w, c), g);
    // over customers: only the customer of the order
    if 0 <= q0 < m.o_n {
        lemma_ccnt(m, ocust(m, q0));
        assert forall|c: int| 0 <= c < m.c_n && c != c0 implies #[trigger] g(c) == 0 by {
            if pair(m, p, k, c, q0) {
                assert(ckey(m, c) == ocust(m, q0));
            }
        }
        lemma_isum_single(m.c_n, g, c0);
    } else {
        lemma_isum_zero(m.c_n, g);
    }
}

pub open spec fn w_one() -> spec_fn(int) -> int { |j: int| 1int }
pub open spec fn w_qty(m: M) -> spec_fn(int) -> int { |j: int| lqty(m, j) }
pub open spec fn w_abs(m: M) -> spec_fn(int) -> int { |j: int| abs(lqty(m, j)) }

/// The lineitem sums of an order are the per-key sums of its key.
pub proof fn lemma_lw(m: M, q: int)
    ensures
        lw(m, q, w_one()) == kcnt(m, okey(m, q)),
        lw(m, q, w_qty(m)) == ksum(m, okey(m, q)),
        lw(m, q, w_abs(m)) == kabs(m, okey(m, q)),
{
    let k = okey(m, q);
    lemma_isum_ext(m.l_n, |j: int| if lkey(m, j) == okey(m, q) { w_one()(j) } else { 0int }, kcnt_f(m, k));
    lemma_isum_ext(m.l_n, |j: int| if lkey(m, j) == okey(m, q) { w_qty(m)(j) } else { 0int }, ksum_f(m, k));
    lemma_isum_ext(m.l_n, |j: int| if lkey(m, j) == okey(m, q) { w_abs(m)(j) } else { 0int }, kabs_f(m, k));
}

/// A normal-form term over the triple sum, for weight `w`.
proof fn lemma_acc_one(db: Database, m: M, p: QP, k: Row, f: spec_fn(Row) -> int, w: spec_fn(int) -> int)
    requires
        db_ok(db), rel_ok(m, db), model_ok(m),
        forall|c: int, q: int, j: int| #[trigger] f(jrow(m, c, q, j)) == tw(m, p, k, w, c, q, j),
    ensures sum_of(q18_xs(db), f) == total(m, p, k, w),
{
    lemma_sum_xs(db, m, f);
    assert forall|c: int| 0 <= c < m.c_n implies #[trigger] s_ol(m, f, crow(m, c)) == t_qj(m, p, k, w, c) by {
        assert forall|q: int| 0 <= q < m.o_n implies #[trigger] s_l(m, f, crow(m, c) + orow(m, q)) == t_j(m, p, k, w, c, q) by {
            assert forall|j: int| 0 <= j < m.l_n implies #[trigger] f(crow(m, c) + orow(m, q) + lrow(m, j)) == tw(m, p, k, w, c, q, j) by {
                assert(f(jrow(m, c, q, j)) == tw(m, p, k, w, c, q, j));
            }
            lemma_isum_ext(m.l_n, |j: int| f(crow(m, c) + orow(m, q) + lrow(m, j)), |j: int| tw(m, p, k, w, c, q, j));
        }
        lemma_isum_ext(m.o_n, |q: int| s_l(m, f, crow(m, c) + orow(m, q)), |q: int| t_j(m, p, k, w, c, q));
    }
    lemma_isum_ext(m.c_n, |c: int| s_ol(m, f, crow(m, c)), |c: int| t_qj(m, p, k, w, c));
    lemma_factor(m, p, k, w);
    lemma_collapse(m, p, k, w);
}

/// The group accumulators of the statement.
pub proof fn lemma_acc(db: Database, m: M, p: QP, k: Row)
    requires db_ok(db), rel_ok(m, db), model_ok(m),
    ensures
        gcount(q18_g(m, p), q18_xs(db), k) == total(m, p, k, w_one()),
        gsum(q18_g(m, p), q18_xs(db), k, 0) == total(m, p, k, w_qty(m)),
        gabs(q18_g(m, p), q18_xs(db), k, 0) == total(m, p, k, w_abs(m)),
{
    let g = q18_g(m, p);
    let xs = q18_xs(db);
    lemma_acc_sum_of(g, xs, k, 0);
    assert forall|c: int, q: int, j: int| #[trigger] count_term(g, k)(jrow(m, c, q, j)) == tw(m, p, k, w_one(), c, q, j) by {
        lemma_term(m, p, k, c, q, j);
    }
    lemma_acc_one(db, m, p, k, count_term(g, k), w_one());
    assert forall|c: int, q: int, j: int| #[trigger] sum_term(g, k, 0)(jrow(m, c, q, j)) == tw(m, p, k, w_qty(m), c, q, j) by {
        lemma_term(m, p, k, c, q, j);
    }
    lemma_acc_one(db, m, p, k, sum_term(g, k, 0), w_qty(m));
    assert forall|c: int, q: int, j: int| #[trigger] abs_term(g, k, 0)(jrow(m, c, q, j)) == tw(m, p, k, w_abs(m), c, q, j) by {
        lemma_term(m, p, k, c, q, j);
    }
    lemma_acc_one(db, m, p, k, abs_term(g, k, 0), w_abs(m));
}

// ------------------------------------------------------------------------------------------------ the groups

/// The group key of a good order.
pub open spec fn keyq(m: M, q: int) -> Row {
    keyrow(m, cpos(m, ocust(m, q)), q)
}

/// A sum of `n` terms each at most `b`.
proof fn lemma_isum_le(n: int, f: spec_fn(int) -> int, b: int)
    requires n >= 0, forall|i: int| 0 <= i < n ==> #[trigger] f(i) <= b,
    ensures isum(n, f) <= n * b,
    decreases n,
{
    if n > 0 {
        lemma_isum_le(n - 1, f, b);
        assert((n - 1) * b + b == n * b) by (nonlinear_arith);
    }
}

/// Every order's absolute quantity sum is at most `l_n * 10^15`, inside `i128`.
proof fn lemma_kabs_bound(m: M, k: int)
    requires model_ok(m),
    ensures 0 <= kabs(m, k) <= i128_max(),
{
    assert(pow10(15) == 1000000000000000) by (compute);
    let b = 1000000000000000int;
    assert forall|j: int| 0 <= j < m.l_n implies #[trigger] kabs_f(m, k)(j) <= b && kabs_f(m, k)(j) >= 0 by {
        assert(in_i64(lkey(m, j)));
        assert(-pow10(15) < lqty(m, j) < pow10(15));
    }
    lemma_isum_le(m.l_n, kabs_f(m, k), b);
    lemma_isum_nonneg(0, m.l_n, kabs_f(m, k));
    assert(m.l_n * b <= 18446744073709551615 * 1000000000000000) by (nonlinear_arith)
        requires m.l_n <= 18446744073709551615, b == 1000000000000000;
}

/// The statement's groups are the good orders: a key has a qualifying row exactly when it is a good order's key,
/// whose accumulators are its lineitem count and quantity sum; every group's absolute mass fits `i128`.
pub proof fn lemma_groups_link(db: Database, m: M, p: QP)
    requires db_ok(db), rel_ok(m, db), model_ok(m),
    ensures
        forall|k: Row| #[trigger] gcount(q18_g(m, p), q18_xs(db), k) > 0 <==> (0 <= qk(m, k) < m.o_n && good(m, p, qk(m, k)) && keyq(m, qk(m, k)) == k),
        forall|q: int| 0 <= q < m.o_n && #[trigger] good(m, p, q) ==> {
            &&& qk(m, keyq(m, q)) == q
            &&& gcount(q18_g(m, p), q18_xs(db), keyq(m, q)) == kcnt(m, okey(m, q))
            &&& gsum(q18_g(m, p), q18_xs(db), keyq(m, q), 0) == ksum(m, okey(m, q))
        },
        forall|k: Row| #[trigger] gabs(q18_g(m, p), q18_xs(db), k, 0) <= i128_max(),
{
    let g = q18_g(m, p);
    let xs = q18_xs(db);
    assert forall|k: Row| #[trigger] gcount(g, xs, k) > 0 <==> (0 <= qk(m, k) < m.o_n && good(m, p, qk(m, k)) && keyq(m, qk(m, k)) == k) by {
        lemma_acc(db, m, p, k);
        let q0 = qk(m, k);
        let c0 = cpos(m, ocust(m, q0));
        if 0 <= q0 < m.o_n {
            lemma_lw(m, q0);
            lemma_ccnt(m, ocust(m, q0));
            if 0 <= c0 < m.c_n && pair(m, p, k, c0, q0) {
                assert(ccnt(m, ocust(m, q0)) > 0);
            }
            if good(m, p, q0) && keyq(m, q0) == k {
                assert(pair(m, p, k, c0, q0));
            }
        }
    }
    assert forall|q: int| 0 <= q < m.o_n && #[trigger] good(m, p, q) implies {
        &&& qk(m, keyq(m, q)) == q
        &&& gcount(g, xs, keyq(m, q)) == kcnt(m, okey(m, q))
        &&& gsum(g, xs, keyq(m, q), 0) == ksum(m, okey(m, q))
    } by {
        let k = keyq(m, q);
        crate::agent::facts::lemma_opos(m, okey(m, q));
        assert(k[2] == Val::Int(okey(m, q)));
        assert(qk(m, k) == q);
        lemma_acc(db, m, p, k);
        lemma_lw(m, q);
        lemma_ccnt(m, ocust(m, q));
        assert(pair(m, p, k, cpos(m, ocust(m, q)), q));
    }
    assert forall|k: Row| #[trigger] gabs(g, xs, k, 0) <= i128_max() by {
        lemma_acc(db, m, p, k);
        let q0 = qk(m, k);
        if 0 <= q0 < m.o_n {
            lemma_lw(m, q0);
            lemma_kabs_bound(m, okey(m, q0));
        }
    }
}

} // verus!
