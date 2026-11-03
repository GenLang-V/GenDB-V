//! The relational link of Q3: the FROM product `customer x orders x lineitem` of a database bound to the parts,
//! projected on the ten columns the statement reads (`q3_cols`), is the product of the model's rows (`jrow`); sums over
//! it are triple index sums over the model (`lemma_sum_xs`). With the normal form `q3_g` (WHERE, group key and SUM
//! argument of `link::query::QuerySpec`), the group accumulators factor per order (`lemma_acc`), and under the orders
//! and customer primary keys the groups are exactly the good orders of `qspec` (`lemma_groups_link`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::types::*;
use crate::spec::typing::{db_wf, row_in_table};
use crate::spec::numeric::{abs, pow10};
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::product_rows;
use crate::schema::schema_spec;
use crate::link::query::*;
use crate::link::join::{sum_of, shift, lemma_sum_of_product, lemma_sum_of_ext, lemma_sum_of_perm, lemma_proj_product,
    lemma_acc_sum_of, count_term, sum_term, abs_term};
use crate::link::source::lemma_proj_all_index;
use crate::link::expr::{ival, tval, i128_max};
use crate::bridge::relation::{is_concat, lemma_product_rows_elems};
use crate::stores::facts::interface::common::colfmt as ff;
use super::common::isum::*;
use super::model::*;
use super::qspec::*;
use super::sqlrow::*;

verus! {

// ------------------------------------------------------------------------------------------------ the FROM rows

/// Positions read in the joined row: c_custkey, c_mktsegment | o_orderkey, o_custkey, o_orderdate, o_shippriority |
/// l_orderkey, l_extendedprice, l_discount, l_shipdate.
pub open spec fn q3_cols() -> Seq<nat> {
    seq![0nat, 6, 8, 9, 12, 15, 17, 22, 23, 27]
}

pub open spec fn from_rows(db: Database) -> Seq<Row> {
    product_rows(product_rows(db.tables[2], db.tables[1]), db.tables[0])
}

pub open spec fn crel(db: Database) -> Seq<Row> { proj_all(db.tables[2], ccols()) }
pub open spec fn orel(db: Database) -> Seq<Row> { proj_all(db.tables[1], ocols()) }
pub open spec fn lrel(db: Database) -> Seq<Row> { proj_all(db.tables[0], lcols()) }

/// The projected FROM rows.
pub open spec fn q3_xs(db: Database) -> Seq<Row> {
    proj_all(from_rows(db), q3_cols())
}

/// A joined model row: customer row `c`, orders position `q`, lineitem row `j`.
pub open spec fn jrow(m: M, c: int, q: int, j: int) -> Row {
    crow(m, c) + orow(m, q) + lrow(m, j)
}

/// The database facts the link needs.
pub open spec fn db_ok(db: Database) -> bool {
    db.schema == schema_spec() && db_wf(db)
}

pub proof fn lemma_from_eval(db: Database)
    requires db.tables.len() == 8,
    ensures eval_query(db, Seq::empty(), q3_from()) == Ok::<Relation, SqlError>(from_rows(db)),
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
    assert(q3_from() == Query::Product { left: Box::new(p21), right: Box::new(t0) });
}

/// Row widths of the three tables.
pub proof fn lemma_widths(db: Database)
    requires db_ok(db),
    ensures
        db.tables.len() == 8,
        forall|i: int| 0 <= i < db.tables[2].len() ==> (#[trigger] db.tables[2][i]).len() == 8,
        forall|i: int| 0 <= i < db.tables[1].len() ==> (#[trigger] db.tables[1][i]).len() == 9,
        forall|i: int| 0 <= i < db.tables[0].len() ==> (#[trigger] db.tables[0][i]).len() == 16,
{
    crate::stores::facts::declaration::lemma_declared_schema();
    assert(schema_spec()[2].columns.len() == 8) by (compute);
    assert forall|i: int| 0 <= i < db.tables[2].len() implies (#[trigger] db.tables[2][i]).len() == 8 by {
        assert(row_in_table(db.tables[2][i], db.schema[2]));
    }
    assert forall|i: int| 0 <= i < db.tables[1].len() implies (#[trigger] db.tables[1][i]).len() == 9 by {
        assert(row_in_table(db.tables[1][i], db.schema[1]));
    }
    assert forall|i: int| 0 <= i < db.tables[0].len() implies (#[trigger] db.tables[0][i]).len() == 16 by {
        assert(row_in_table(db.tables[0][i], db.schema[0]));
    }
}

/// The projected FROM rows are the product of the projected tables.
pub proof fn lemma_xs_product(db: Database)
    requires db_ok(db),
    ensures q3_xs(db) == product_rows(product_rows(crel(db), orel(db)), lrel(db)),
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
    assert(ca + shift(lcols(), 17) =~= q3_cols());
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
        &&& env[6] == Val::Text(segtext(m, c))
        &&& env[8] == Val::Int(okey(m, q))
        &&& env[9] == Val::Int(ocust(m, q))
        &&& env[12] == Val::Date(odate(m, q))
        &&& env[15] == Val::Int(osp(m, q))
        &&& env[17] == Val::Int(lkey(m, j))
        &&& env[22] == (Val::Num { coeff: lprice(m, j), scale: 2 })
        &&& env[23] == (Val::Num { coeff: ldisc(m, j), scale: 2 })
        &&& env[27] == Val::Date(lship(m, j))
        &&& proj(env, q3_cols()) == jrow(m, c, q, j)
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
    assert(proj(rc, ccols())[0] == rc[0] && proj(rc, ccols())[1] == rc[6]);
    assert(proj(ro, ocols())[0] == ro[0] && proj(ro, ocols())[1] == ro[1] && proj(ro, ocols())[2] == ro[4] && proj(ro, ocols())[3] == ro[7]);
    assert(proj(rl, lcols())[0] == rl[0] && proj(rl, lcols())[1] == rl[5] && proj(rl, lcols())[2] == rl[6] && proj(rl, lcols())[3] == rl[10]);
    assert(env == rc + ro + rl);
    assert(env[0] == rc[0] && env[6] == rc[6]);
    assert(env[8] == ro[0] && env[9] == ro[1] && env[12] == ro[4] && env[15] == ro[7]);
    assert(env[17] == rl[0] && env[22] == rl[5] && env[23] == rl[6] && env[27] == rl[10]);
    assert(proj(env, q3_cols()) =~= jrow(m, c, q, j));
    (c, q, j)
}

// ------------------------------------------------------------------------------------------------ sums by table

/// A sum over the lineitem relation is a sum over the model's stored rows (a permutation of it).
pub proof fn lemma_sum_l(db: Database, m: M, h: spec_fn(Row) -> int)
    requires rel_ok(m, db),
    ensures sum_of(lrel(db), h) == isum(m.l_n, |j: int| h(lrow(m, j))),
{
    let t = db.tables[0];
    let lr = lrel(db);
    lemma_proj_all_index(t, lcols());
    let st = ff::stored_rows(lr, m.l_map);
    assert(st =~= Seq::new(m.l_n as nat, |j: int| lrow(m, j))) by {
        assert forall|j: int| 0 <= j < m.l_n implies #[trigger] st[j] == lrow(m, j) by {
            assert(0 <= m.l_map[j] < m.l_n);
        }
    }
    ff::lemma_stored_rows_multiset(lr, m.l_map);
    lemma_sum_of_perm(st, lr, h);
    lemma_sum_of_seq(m.l_n, |j: int| lrow(m, j), h);
    lemma_isum_ext(m.l_n, |i: int| h((|j: int| lrow(m, j))(i)), |j: int| h(lrow(m, j)));
}

/// A sum over the orders relation is a sum over the model's stored positions.
pub proof fn lemma_sum_o(db: Database, m: M, h: spec_fn(Row) -> int)
    requires rel_ok(m, db),
    ensures sum_of(orel(db), h) == isum(m.o_n, |q: int| h(orow(m, q))),
{
    let t = db.tables[1];
    let orr = orel(db);
    lemma_proj_all_index(t, ocols());
    let st = ff::stored_rows(orr, m.o_map);
    assert(st =~= Seq::new(m.o_n as nat, |q: int| orow(m, q))) by {
        assert forall|q: int| 0 <= q < m.o_n implies #[trigger] st[q] == orow(m, q) by {
            assert(0 <= m.o_map[q] < m.o_n);
        }
    }
    ff::lemma_stored_rows_multiset(orr, m.o_map);
    lemma_sum_of_perm(st, orr, h);
    lemma_sum_of_seq(m.o_n, |q: int| orow(m, q), h);
    lemma_isum_ext(m.o_n, |i: int| h((|q: int| orow(m, q))(i)), |q: int| h(orow(m, q)));
}

/// A sum over the customer relation (canonical order) is a sum over the model's rows.
pub proof fn lemma_sum_c(db: Database, m: M, h: spec_fn(Row) -> int)
    requires rel_ok(m, db),
    ensures sum_of(crel(db), h) == isum(m.c_n, |c: int| h(crow(m, c))),
{
    let t = db.tables[2];
    lemma_proj_all_index(t, ccols());
    assert(crel(db) =~= Seq::new(m.c_n as nat, |c: int| crow(m, c)));
    lemma_sum_of_seq(m.c_n, |c: int| crow(m, c), h);
    lemma_isum_ext(m.c_n, |i: int| h((|c: int| crow(m, c))(i)), |c: int| h(crow(m, c)));
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
    ensures sum_of(q3_xs(db), f) == isum(m.c_n, |c: int| s_ol(m, f, crow(m, c))),
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

/// WHERE over the projected row (two-valued: every read value is non-NULL and typed).
pub open spec fn q3_qual(p: QP) -> spec_fn(Row) -> bool {
    |x: Row| tval(x[1]) == p.seg && ival(x[0]) == ival(x[3]) && ival(x[6]) == ival(x[2]) && ival(x[4]) < p.day && ival(x[9]) > p.day
}

/// GROUP BY l_orderkey, o_orderdate, o_shippriority over the projected row.
pub open spec fn q3_key() -> spec_fn(Row) -> Row {
    |x: Row| seq![x[6], x[4], x[5]]
}

/// The SUM argument's coefficient (scale 4) over the projected row.
pub open spec fn q3_argf() -> spec_fn(int, Row) -> int {
    |j: int, x: Row| ival(x[7]) * (100 - ival(x[8]))
}

/// Q3 in the accumulator normal form of `link::query`.
pub open spec fn q3_g(p: QP) -> QuerySpec {
    QuerySpec { qual: q3_qual(p), key: q3_key(), arg: q3_argf(), aggs: seq![AggKind::Sum { scale: 4 }], outs: q3_outs(), grouped: true }
}

/// The group key of the order at `q`.
pub open spec fn keyq(m: M, q: int) -> Row {
    seq![Val::Int(okey(m, q)), Val::Date(odate(m, q)), Val::Int(osp(m, q))]
}

/// The order at `q` is dated before `$2` and its key is `k`.
pub open spec fn om(m: M, p: QP, q: int, k: Row) -> bool {
    odate(m, q) < p.day && keyq(m, q) == k
}

/// On a joined model row the normal form's hit and argument read the model.
pub proof fn lemma_term(m: M, p: QP, k: Row, c: int, q: int, j: int)
    ensures
        hit(q3_g(p), jrow(m, c, q, j), k) == (cmatch(m, p, c, ocust(m, q)) && om(m, p, q, k) && lhit(m, p, q, j)),
        (q3_g(p).arg)(0, jrow(m, c, q, j)) == larg(m, j),
        (q3_g(p).qual)(jrow(m, c, q, j)) == (cmatch(m, p, c, ocust(m, q)) && odate(m, q) < p.day && lhit(m, p, q, j)),
        (q3_g(p).key)(jrow(m, c, q, j)) == seq![Val::Int(lkey(m, j)), Val::Date(odate(m, q)), Val::Int(osp(m, q))],
{
    let x = jrow(m, c, q, j);
    assert(x[0] == Val::Int(ckey(m, c)) && x[1] == Val::Text(segtext(m, c)));
    assert(x[2] == Val::Int(okey(m, q)) && x[3] == Val::Int(ocust(m, q)) && x[4] == Val::Date(odate(m, q)) && x[5] == Val::Int(osp(m, q)));
    assert(x[6] == Val::Int(lkey(m, j)) && x[7] == (Val::Num { coeff: lprice(m, j), scale: 2 }));
    assert(x[8] == (Val::Num { coeff: ldisc(m, j), scale: 2 }) && x[9] == Val::Date(lship(m, j)));
    assert((q3_g(p).key)(x) =~= seq![Val::Int(lkey(m, j)), Val::Date(odate(m, q)), Val::Int(osp(m, q))]);
    if lkey(m, j) == okey(m, q) {
        assert((q3_g(p).key)(x) =~= keyq(m, q));
    } else {
        assert((q3_g(p).key)(x)[0] != keyq(m, q)[0]);
    }
}

// ------------------------------------------------------------------------------------------------ factoring per order

/// The term of the triple sum for a lineitem weight `w`.
pub open spec fn tw(m: M, p: QP, k: Row, w: spec_fn(int) -> int, c: int, q: int, j: int) -> int {
    if cmatch(m, p, c, ocust(m, q)) && om(m, p, q, k) && lhit(m, p, q, j) { w(j) } else { 0 }
}

/// The weight summed over the shipped-later lineitems of the order at `q`.
pub open spec fn lw(m: M, p: QP, q: int, w: spec_fn(int) -> int) -> int {
    isum(m.l_n, |j: int| if lhit(m, p, q, j) { w(j) } else { 0int })
}

/// The per-order form of a group accumulator.
pub open spec fn per_order(m: M, p: QP, k: Row, w: spec_fn(int) -> int) -> int {
    isum(m.o_n, |q: int| if om(m, p, q, k) { ccnt(m, p, ocust(m, q)) * lw(m, p, q, w) } else { 0int })
}

/// Inner sums of the factorization (named, so that they can be quantifier triggers).
pub open spec fn t_j(m: M, p: QP, k: Row, w: spec_fn(int) -> int, c: int, q: int) -> int {
    isum(m.l_n, |j: int| tw(m, p, k, w, c, q, j))
}

pub open spec fn t_qj(m: M, p: QP, k: Row, w: spec_fn(int) -> int, c: int) -> int {
    isum(m.o_n, |q: int| t_j(m, p, k, w, c, q))
}

pub open spec fn a_cq(m: M, p: QP, k: Row, w: spec_fn(int) -> int, c: int, q: int) -> int {
    if cmatch(m, p, c, ocust(m, q)) && om(m, p, q, k) { lw(m, p, q, w) } else { 0int }
}

pub open spec fn a_q(m: M, p: QP, k: Row, w: spec_fn(int) -> int, c: int) -> int {
    isum(m.o_n, |q: int| a_cq(m, p, k, w, c, q))
}

pub open spec fn a_c(m: M, p: QP, k: Row, w: spec_fn(int) -> int, q: int) -> int {
    isum(m.c_n, |c: int| a_cq(m, p, k, w, c, q))
}

/// The triple sum factors per order: customers count, lineitems sum.
pub proof fn lemma_factor(m: M, p: QP, k: Row, w: spec_fn(int) -> int)
    ensures
        isum(m.c_n, |c: int| t_qj(m, p, k, w, c)) == per_order(m, p, k, w),
{
    // the lineitem sum
    assert forall|c: int| 0 <= c < m.c_n implies #[trigger] t_qj(m, p, k, w, c) == a_q(m, p, k, w, c) by {
        assert forall|q: int| 0 <= q < m.o_n implies #[trigger] t_j(m, p, k, w, c, q) == a_cq(m, p, k, w, c, q) by {
            if cmatch(m, p, c, ocust(m, q)) && om(m, p, q, k) {
                lemma_isum_ext(m.l_n, |j: int| tw(m, p, k, w, c, q, j), |j: int| if lhit(m, p, q, j) { w(j) } else { 0int });
            } else {
                lemma_isum_zero(m.l_n, |j: int| tw(m, p, k, w, c, q, j));
            }
        }
        lemma_isum_ext(m.o_n, |q: int| t_j(m, p, k, w, c, q), |q: int| a_cq(m, p, k, w, c, q));
    }
    lemma_isum_ext(m.c_n, |c: int| t_qj(m, p, k, w, c), |c: int| a_q(m, p, k, w, c));
    // exchange customers and orders
    let h = |c: int, q: int| a_cq(m, p, k, w, c, q);
    lemma_isum_swap(m.c_n, m.o_n, h);
    assert forall|c: int| 0 <= c < m.c_n implies #[trigger] a_q(m, p, k, w, c) == isum(m.o_n, |q: int| h(c, q)) by {
        lemma_isum_ext(m.o_n, |q: int| h(c, q), |q: int| a_cq(m, p, k, w, c, q));
    }
    lemma_isum_ext(m.c_n, |c: int| isum(m.o_n, |q: int| h(c, q)), |c: int| a_q(m, p, k, w, c));
    assert forall|q: int| 0 <= q < m.o_n implies #[trigger] a_c(m, p, k, w, q) == isum(m.c_n, |c: int| h(c, q)) by {
        lemma_isum_ext(m.c_n, |c: int| h(c, q), |c: int| a_cq(m, p, k, w, c, q));
    }
    lemma_isum_ext(m.o_n, |q: int| isum(m.c_n, |c: int| h(c, q)), |q: int| a_c(m, p, k, w, q));
    // the customer count
    assert forall|q: int| 0 <= q < m.o_n implies #[trigger] a_c(m, p, k, w, q)
        == (if om(m, p, q, k) { ccnt(m, p, ocust(m, q)) * lw(m, p, q, w) } else { 0int }) by {
        if om(m, p, q, k) {
            let l = lw(m, p, q, w);
            lemma_isum_scale(m.c_n, cmatch_f(m, p, ocust(m, q)), l);
            lemma_isum_ext(m.c_n, |c: int| a_cq(m, p, k, w, c, q), |c: int| l * cmatch_f(m, p, ocust(m, q))(c));
            assert(l * ccnt(m, p, ocust(m, q)) == ccnt(m, p, ocust(m, q)) * l) by (nonlinear_arith);
        } else {
            lemma_isum_zero(m.c_n, |c: int| a_cq(m, p, k, w, c, q));
        }
    }
    lemma_isum_ext(m.o_n, |q: int| a_c(m, p, k, w, q),
        |q: int| if om(m, p, q, k) { ccnt(m, p, ocust(m, q)) * lw(m, p, q, w) } else { 0int });
}

pub open spec fn w_one() -> spec_fn(int) -> int { |j: int| 1int }
pub open spec fn w_arg(m: M) -> spec_fn(int) -> int { |j: int| larg(m, j) }
pub open spec fn w_abs(m: M) -> spec_fn(int) -> int { |j: int| abs(larg(m, j)) }

pub proof fn lemma_lw(m: M, p: QP, q: int)
    ensures
        lw(m, p, q, w_one()) == lcnt(m, p, q),
        lw(m, p, q, w_arg(m)) == lsum(m, p, q),
        lw(m, p, q, w_abs(m)) == labs(m, p, q),
{
    lemma_isum_ext(m.l_n, |j: int| if lhit(m, p, q, j) { w_one()(j) } else { 0int }, lcnt_f(m, p, q));
    lemma_isum_ext(m.l_n, |j: int| if lhit(m, p, q, j) { w_arg(m)(j) } else { 0int }, lsum_f(m, p, q));
    lemma_isum_ext(m.l_n, |j: int| if lhit(m, p, q, j) { w_abs(m)(j) } else { 0int }, labs_f(m, p, q));
}

/// A normal-form term over the triple sum, for weight `w`.
proof fn lemma_acc_one(db: Database, m: M, p: QP, k: Row, f: spec_fn(Row) -> int, w: spec_fn(int) -> int)
    requires
        db_ok(db), rel_ok(m, db),
        forall|c: int, q: int, j: int| #[trigger] f(jrow(m, c, q, j)) == tw(m, p, k, w, c, q, j),
    ensures sum_of(q3_xs(db), f) == per_order(m, p, k, w),
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
}

/// The group accumulators of the statement, per order.
pub proof fn lemma_acc(db: Database, m: M, p: QP, k: Row)
    requires db_ok(db), rel_ok(m, db),
    ensures
        gcount(q3_g(p), q3_xs(db), k) == per_order(m, p, k, w_one()),
        gsum(q3_g(p), q3_xs(db), k, 0) == per_order(m, p, k, w_arg(m)),
        gabs(q3_g(p), q3_xs(db), k, 0) == per_order(m, p, k, w_abs(m)),
{
    let g = q3_g(p);
    let xs = q3_xs(db);
    lemma_acc_sum_of(g, xs, k, 0);
    assert forall|c: int, q: int, j: int| #[trigger] count_term(g, k)(jrow(m, c, q, j)) == tw(m, p, k, w_one(), c, q, j) by {
        lemma_term(m, p, k, c, q, j);
    }
    lemma_acc_one(db, m, p, k, count_term(g, k), w_one());
    assert forall|c: int, q: int, j: int| #[trigger] sum_term(g, k, 0)(jrow(m, c, q, j)) == tw(m, p, k, w_arg(m), c, q, j) by {
        lemma_term(m, p, k, c, q, j);
    }
    lemma_acc_one(db, m, p, k, sum_term(g, k, 0), w_arg(m));
    assert forall|c: int, q: int, j: int| #[trigger] abs_term(g, k, 0)(jrow(m, c, q, j)) == tw(m, p, k, w_abs(m), c, q, j) by {
        lemma_term(m, p, k, c, q, j);
    }
    lemma_acc_one(db, m, p, k, abs_term(g, k, 0), w_abs(m));
}

// ------------------------------------------------------------------------------------------------ primary keys

/// The order position a group key names.
pub open spec fn qk(m: M, k: Row) -> int {
    opos(m, ival(k[0]))
}

/// Under the orders primary key only the order the key names contributes.
pub proof fn lemma_collapse(m: M, p: QP, k: Row, w: spec_fn(int) -> int)
    requires model_ok(m),
    ensures
        per_order(m, p, k, w) == if 0 <= qk(m, k) < m.o_n && om(m, p, qk(m, k), k) {
            ccnt(m, p, ocust(m, qk(m, k))) * lw(m, p, qk(m, k), w)
        } else { 0 },
{
    let q0 = qk(m, k);
    let f = |q: int| if om(m, p, q, k) { ccnt(m, p, ocust(m, q)) * lw(m, p, q, w) } else { 0int };
    assert forall|q: int| 0 <= q < m.o_n && q != q0 implies #[trigger] f(q) == 0 by {
        if om(m, p, q, k) {
            assert(k[0] == Val::Int(okey(m, q)));
            crate::agent::facts::lemma_opos(m, okey(m, q));
            assert(ival(k[0]) == okey(m, q));
        }
    }
    lemma_isum_single(m.o_n, f, q0);
}

/// Under the customer primary key a customer key has at most one row (with the segment or not).
pub proof fn lemma_ccnt(m: M, p: QP, ck: int)
    requires model_ok(m),
    ensures 0 <= ccnt(m, p, ck) <= 1,
{
    let f = cmatch_f(m, p, ck);
    if exists|c: int| 0 <= c < m.c_n && ckey(m, c) == ck {
        let c0 = choose|c: int| 0 <= c < m.c_n && ckey(m, c) == ck;
        assert forall|c: int| 0 <= c < m.c_n && c != c0 implies #[trigger] f(c) == 0 by {
            assert(ckey(m, c) != ckey(m, c0));
        }
        lemma_isum_single(m.c_n, f, c0);
    } else {
        assert forall|c: int| 0 <= c < m.c_n implies #[trigger] f(c) == 0 by {}
        lemma_isum_zero(m.c_n, f);
    }
}

/// Without a counted lineitem the order's absolute sum is zero.
pub proof fn lemma_lcnt_zero(m: M, p: QP, q: int)
    requires lcnt(m, p, q) <= 0,
    ensures labs(m, p, q) == 0, lsum(m, p, q) == 0,
{
    assert forall|j: int| 0 <= j < m.l_n implies !lhit(m, p, q, j) by {
        if lhit(m, p, q, j) {
            assert forall|t: int| 0 <= t < m.l_n implies #[trigger] lcnt_f(m, p, q)(t) >= 0 by {}
            lemma_isum_ge_term(m.l_n, lcnt_f(m, p, q), j);
        }
    }
    lemma_isum_zero(m.l_n, labs_f(m, p, q));
    lemma_isum_zero(m.l_n, lsum_f(m, p, q));
}

/// The statement's groups are the good orders: a key has a qualifying row exactly when it is a good order's key,
/// whose accumulators are its lineitem count and sums; every group's absolute mass is bounded under `caps_ok`.
pub proof fn lemma_groups_link(db: Database, m: M, p: QP)
    requires db_ok(db), rel_ok(m, db), model_ok(m),
    ensures
        forall|k: Row| #[trigger] gcount(q3_g(p), q3_xs(db), k) > 0 <==> (0 <= qk(m, k) < m.o_n && good(m, p, qk(m, k)) && keyq(m, qk(m, k)) == k),
        forall|q: int| 0 <= q < m.o_n && #[trigger] good(m, p, q) ==> {
            &&& qk(m, keyq(m, q)) == q
            &&& gcount(q3_g(p), q3_xs(db), keyq(m, q)) == lcnt(m, p, q)
            &&& gsum(q3_g(p), q3_xs(db), keyq(m, q), 0) == lsum(m, p, q)
            &&& gabs(q3_g(p), q3_xs(db), keyq(m, q), 0) == labs(m, p, q)
        },
        caps_ok(m, p) ==> forall|k: Row| #[trigger] gabs(q3_g(p), q3_xs(db), k, 0) <= i128_max(),
{
    let g = q3_g(p);
    let xs = q3_xs(db);
    assert forall|k: Row| #[trigger] gcount(g, xs, k) > 0 <==> (0 <= qk(m, k) < m.o_n && good(m, p, qk(m, k)) && keyq(m, qk(m, k)) == k) by {
        lemma_acc(db, m, p, k);
        lemma_collapse(m, p, k, w_one());
        let q0 = qk(m, k);
        if 0 <= q0 < m.o_n {
            lemma_lw(m, p, q0);
            lemma_ccnt(m, p, ocust(m, q0));
            assert(lcnt(m, p, q0) >= 0) by {
                assert forall|t: int| 0 <= t < m.l_n implies #[trigger] lcnt_f(m, p, q0)(t) >= 0 by {}
                lemma_isum_nonneg(0, m.l_n, lcnt_f(m, p, q0));
            }
            let (cc, lc) = (ccnt(m, p, ocust(m, q0)), lcnt(m, p, q0));
            assert(cc * lc > 0 <==> (cc > 0 && lc > 0)) by (nonlinear_arith) requires 0 <= cc <= 1, lc >= 0;
        }
    }
    assert forall|q: int| 0 <= q < m.o_n && #[trigger] good(m, p, q) implies {
        &&& qk(m, keyq(m, q)) == q
        &&& gcount(g, xs, keyq(m, q)) == lcnt(m, p, q)
        &&& gsum(g, xs, keyq(m, q), 0) == lsum(m, p, q)
        &&& gabs(g, xs, keyq(m, q), 0) == labs(m, p, q)
    } by {
        let k = keyq(m, q);
        crate::agent::facts::lemma_opos(m, okey(m, q));
        assert(ival(k[0]) == okey(m, q));
        assert(qk(m, k) == q);
        lemma_acc(db, m, p, k);
        lemma_collapse(m, p, k, w_one());
        lemma_collapse(m, p, k, w_arg(m));
        lemma_collapse(m, p, k, w_abs(m));
        lemma_lw(m, p, q);
        lemma_ccnt(m, p, ocust(m, q));
        assert(ccnt(m, p, ocust(m, q)) == 1);
    }
    if caps_ok(m, p) {
        assert forall|k: Row| #[trigger] gabs(g, xs, k, 0) <= i128_max() by {
            lemma_acc(db, m, p, k);
            lemma_collapse(m, p, k, w_abs(m));
            let q0 = qk(m, k);
            if 0 <= q0 < m.o_n && om(m, p, q0, k) {
                lemma_lw(m, p, q0);
                lemma_ccnt(m, p, ocust(m, q0));
                let cc = ccnt(m, p, ocust(m, q0));
                if cc == 0 {
                    assert(cc * labs(m, p, q0) == 0);
                } else if lcnt(m, p, q0) <= 0 {
                    lemma_lcnt_zero(m, p, q0);
                } else {
                    assert(good(m, p, q0));
                    assert(labs(m, p, q0) <= i128_max());
                }
            }
        }
    }
}

} // verus!
