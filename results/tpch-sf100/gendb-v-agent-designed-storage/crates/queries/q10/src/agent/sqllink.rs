//! The relational link of Q10: the FROM product `customer x orders x lineitem x nation` of a database bound to the
//! parts, projected on the sixteen columns the statement reads (`q10_cols`), is the product of the model's rows
//! (`jrow`); sums over it are four nested index sums over the model (`lemma_sum_xs`). With the normal form `q10_g`
//! (WHERE, group key and SUM argument of `link::query::QuerySpec`), the group accumulators factor per customer
//! (`lemma_acc`): a nation count times the customer's orders' lineitem sums; under the customer and nation primary
//! keys the groups are exactly the good customers of `qspec` (`lemma_groups_link`).
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
use super::phase1::lemma_lcnt_zero;

verus! {

// ------------------------------------------------------------------------------------------------ the FROM rows

/// Positions read in the joined row: customer 0, 1, 2, 3, 4, 5, 7 | orders 8, 9, 12 | lineitem 17, 22, 23, 25 |
/// nation 33, 34.
pub open spec fn q10_cols() -> Seq<nat> {
    seq![0nat, 1, 2, 3, 4, 5, 7, 8, 9, 12, 17, 22, 23, 25, 33, 34]
}

pub open spec fn from_rows(db: Database) -> Seq<Row> {
    product_rows(product_rows(product_rows(db.tables[2], db.tables[1]), db.tables[0]), db.tables[6])
}

pub open spec fn crel(db: Database) -> Seq<Row> { proj_all(db.tables[2], ccols()) }
pub open spec fn orel(db: Database) -> Seq<Row> { proj_all(db.tables[1], ocols()) }
pub open spec fn lrel(db: Database) -> Seq<Row> { proj_all(db.tables[0], lcols()) }
pub open spec fn nrel(db: Database) -> Seq<Row> { proj_all(db.tables[6], ncols()) }

/// The projected FROM rows.
pub open spec fn q10_xs(db: Database) -> Seq<Row> {
    proj_all(from_rows(db), q10_cols())
}

/// A joined model row: customer row `c`, orders position `q`, lineitem row `j`, nation row `n`.
pub open spec fn jrow(m: M, c: int, q: int, j: int, n: int) -> Row {
    crow(m, c) + orow(m, q) + lrow(m, j) + nrow(m, n)
}

/// The database facts the link needs.
pub open spec fn db_ok(db: Database) -> bool {
    db.schema == schema_spec() && db_wf(db)
}

pub proof fn lemma_from_eval(db: Database)
    requires db.tables.len() == 8,
    ensures eval_query(db, Seq::empty(), q10_from()) == Ok::<Relation, SqlError>(from_rows(db)),
{
    let e = Seq::<Val>::empty();
    let t2 = Query::Table(2);
    let t1 = Query::Table(1);
    let t0 = Query::Table(0);
    let t6 = Query::Table(6);
    assert(eval_query(db, e, t2) == Ok::<Relation, SqlError>(db.tables[2]));
    assert(eval_query(db, e, t1) == Ok::<Relation, SqlError>(db.tables[1]));
    assert(eval_query(db, e, t0) == Ok::<Relation, SqlError>(db.tables[0]));
    assert(eval_query(db, e, t6) == Ok::<Relation, SqlError>(db.tables[6]));
    let p21 = Query::Product { left: Box::new(t2), right: Box::new(t1) };
    assert(eval_query(db, e, p21) == Ok::<Relation, SqlError>(product_rows(db.tables[2], db.tables[1])));
    let p210 = Query::Product { left: Box::new(p21), right: Box::new(t0) };
    assert(eval_query(db, e, p210) == Ok::<Relation, SqlError>(product_rows(product_rows(db.tables[2], db.tables[1]), db.tables[0])));
    assert(q10_from() == Query::Product { left: Box::new(p210), right: Box::new(t6) });
}

/// Row widths of the four tables.
pub proof fn lemma_widths(db: Database)
    requires db_ok(db),
    ensures
        db.tables.len() == 8,
        forall|i: int| 0 <= i < db.tables[2].len() ==> (#[trigger] db.tables[2][i]).len() == 8,
        forall|i: int| 0 <= i < db.tables[1].len() ==> (#[trigger] db.tables[1][i]).len() == 9,
        forall|i: int| 0 <= i < db.tables[0].len() ==> (#[trigger] db.tables[0][i]).len() == 16,
        forall|i: int| 0 <= i < db.tables[6].len() ==> (#[trigger] db.tables[6][i]).len() == 4,
{
    crate::stores::facts::declaration::lemma_declared_schema();
    crate::stores::custpart::declaration::lemma_declared_schema();
    crate::stores::suppliers::declaration::lemma_declared_schema();
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
    assert forall|i: int| 0 <= i < db.tables[6].len() implies (#[trigger] db.tables[6][i]).len() == 4 by {
        assert(row_in_table(db.tables[6][i], db.schema[6]));
    }
}

/// The projected FROM rows are the product of the projected tables.
pub proof fn lemma_xs_product(db: Database)
    requires db_ok(db),
    ensures q10_xs(db) == product_rows(product_rows(product_rows(crel(db), orel(db)), lrel(db)), nrel(db)),
{
    lemma_widths(db);
    let (t2, t1, t0, t6) = (db.tables[2], db.tables[1], db.tables[0], db.tables[6]);
    // customer x orders
    let ca1 = ccols() + shift(ocols(), 8);
    lemma_proj_product(t2, t1, ccols(), ocols(), 8, 9);
    let a1 = product_rows(t2, t1);
    lemma_product_rows_elems(t2, t1);
    assert forall|i: int| 0 <= i < a1.len() implies (#[trigger] a1[i]).len() == 17 by {
        assert(is_concat(a1[i], t2, t1));
        let (x, y) = choose|x: int, y: int| 0 <= x < t2.len() && 0 <= y < t1.len() && a1[i] == #[trigger] t2[x] + #[trigger] t1[y];
    }
    assert forall|k: int| 0 <= k < ca1.len() implies #[trigger] ca1[k] < 17 by {}
    // x lineitem
    let ca2 = ca1 + shift(lcols(), 17);
    lemma_proj_product(a1, t0, ca1, lcols(), 17, 16);
    let a2 = product_rows(a1, t0);
    lemma_product_rows_elems(a1, t0);
    assert forall|i: int| 0 <= i < a2.len() implies (#[trigger] a2[i]).len() == 33 by {
        assert(is_concat(a2[i], a1, t0));
        let (x, y) = choose|x: int, y: int| 0 <= x < a1.len() && 0 <= y < t0.len() && a2[i] == #[trigger] a1[x] + #[trigger] t0[y];
    }
    assert forall|k: int| 0 <= k < ca2.len() implies #[trigger] ca2[k] < 33 by {}
    // x nation
    lemma_proj_product(a2, t6, ca2, ncols(), 33, 4);
    assert(ca2 + shift(ncols(), 33) =~= q10_cols());
}

/// A FROM row: one row of each table, read through the model.
pub proof fn lemma_from_row(db: Database, m: M, i: int) -> (r: (int, int, int, int))
    requires
        db_ok(db),
        rel_ok(m, db),
        0 <= i < from_rows(db).len(),
    ensures ({
        let (c, q, j, n) = r;
        let env = from_rows(db)[i];
        &&& 0 <= c < m.c_n && 0 <= q < m.o_n && 0 <= j < m.l_n && 0 <= n < m.n_n
        &&& env.len() == 37
        &&& env[0] == Val::Int(ckey(m, c))
        &&& env[1] == Val::Text(cname(m, c))
        &&& env[2] == Val::Text(caddr(m, c))
        &&& env[3] == Val::Int(cnat(m, c))
        &&& env[4] == Val::Text(cphone(m, c))
        &&& env[5] == (Val::Num { coeff: cbal(m, c), scale: 2 })
        &&& env[7] == Val::Text(ccmt(m, c))
        &&& env[8] == Val::Int(okey(m, q))
        &&& env[9] == Val::Int(ocust(m, q))
        &&& env[12] == Val::Date(odate(m, q))
        &&& env[17] == Val::Int(lkey(m, j))
        &&& env[22] == (Val::Num { coeff: lprice(m, j), scale: 2 })
        &&& env[23] == (Val::Num { coeff: ldisc(m, j), scale: 2 })
        &&& env[25] == Val::Text(lflag(m, j))
        &&& env[33] == Val::Int(nkey(m, n))
        &&& env[34] == Val::Text(nname(m, n))
        &&& proj(env, q10_cols()) == jrow(m, c, q, j, n)
    }),
{
    lemma_widths(db);
    let (t2, t1, t0, t6) = (db.tables[2], db.tables[1], db.tables[0], db.tables[6]);
    let a1 = product_rows(t2, t1);
    let a2 = product_rows(a1, t0);
    lemma_product_rows_elems(a2, t6);
    let env = from_rows(db)[i];
    assert(is_concat(env, a2, t6));
    let (a2i, n) = choose|x: int, y: int| 0 <= x < a2.len() && 0 <= y < t6.len() && env == #[trigger] a2[x] + #[trigger] t6[y];
    lemma_product_rows_elems(a1, t0);
    assert(is_concat(a2[a2i], a1, t0));
    let (a1i, l) = choose|x: int, y: int| 0 <= x < a1.len() && 0 <= y < t0.len() && a2[a2i] == #[trigger] a1[x] + #[trigger] t0[y];
    lemma_product_rows_elems(t2, t1);
    assert(is_concat(a1[a1i], t2, t1));
    let (c, b) = choose|x: int, y: int| 0 <= x < t2.len() && 0 <= y < t1.len() && a1[a1i] == #[trigger] t2[x] + #[trigger] t1[y];
    assert(ff::covered(m.o_map, b));
    let q = choose|q: int| 0 <= q < m.o_map.len() && m.o_map[q] == b;
    assert(ff::covered(m.l_map, l));
    let j = choose|j: int| 0 <= j < m.l_map.len() && m.l_map[j] == l;
    let (rc, ro, rl, rn) = (t2[c], t1[b], t0[l], t6[n]);
    assert(proj(rc, ccols()) == crow(m, c));
    assert(proj(ro, ocols()) == orow(m, q));
    assert(proj(rl, lcols()) == lrow(m, j));
    assert(proj(rn, ncols()) == nrow(m, n));
    assert(proj(rc, ccols())[0] == rc[0] && proj(rc, ccols())[1] == rc[1] && proj(rc, ccols())[2] == rc[2]);
    assert(proj(rc, ccols())[3] == rc[3] && proj(rc, ccols())[4] == rc[4] && proj(rc, ccols())[5] == rc[5]);
    assert(proj(rc, ccols())[6] == rc[7]);
    assert(proj(ro, ocols())[0] == ro[0] && proj(ro, ocols())[1] == ro[1] && proj(ro, ocols())[2] == ro[4]);
    assert(proj(rl, lcols())[0] == rl[0] && proj(rl, lcols())[1] == rl[5] && proj(rl, lcols())[2] == rl[6] && proj(rl, lcols())[3] == rl[8]);
    assert(proj(rn, ncols())[0] == rn[0] && proj(rn, ncols())[1] == rn[1]);
    assert(env == rc + ro + rl + rn);
    assert(env[0] == rc[0] && env[1] == rc[1] && env[2] == rc[2] && env[3] == rc[3] && env[4] == rc[4] && env[5] == rc[5] && env[7] == rc[7]);
    assert(env[8] == ro[0] && env[9] == ro[1] && env[12] == ro[4]);
    assert(env[17] == rl[0] && env[22] == rl[5] && env[23] == rl[6] && env[25] == rl[8]);
    assert(env[33] == rn[0] && env[34] == rn[1]);
    assert(proj(env, q10_cols()) =~= jrow(m, c, q, j, n));
    (c, q, j, n)
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

/// A sum over the nation relation (canonical order) is a sum over the model's rows.
pub proof fn lemma_sum_n(db: Database, m: M, h: spec_fn(Row) -> int)
    requires rel_ok(m, db),
    ensures sum_of(nrel(db), h) == isum(m.n_n, |n: int| h(nrow(m, n))),
{
    let t = db.tables[6];
    lemma_proj_all_index(t, ncols());
    assert(nrel(db) =~= Seq::new(m.n_n as nat, |n: int| nrow(m, n)));
    lemma_sum_of_seq(m.n_n, |n: int| nrow(m, n), h);
    lemma_isum_ext(m.n_n, |i: int| h((|n: int| nrow(m, n))(i)), |n: int| h(nrow(m, n)));
}

/// Inner sums of the quadruple sum.
pub open spec fn s_n(m: M, f: spec_fn(Row) -> int, a: Row) -> int {
    isum(m.n_n, |n: int| f(a + nrow(m, n)))
}

pub open spec fn s_ln(m: M, f: spec_fn(Row) -> int, a: Row) -> int {
    isum(m.l_n, |j: int| s_n(m, f, a + lrow(m, j)))
}

pub open spec fn s_oln(m: M, f: spec_fn(Row) -> int, a: Row) -> int {
    isum(m.o_n, |q: int| s_ln(m, f, a + orow(m, q)))
}

/// A sum over the projected FROM rows is the quadruple index sum over the model.
pub proof fn lemma_sum_xs(db: Database, m: M, f: spec_fn(Row) -> int)
    requires db_ok(db), rel_ok(m, db),
    ensures sum_of(q10_xs(db), f) == isum(m.c_n, |c: int| s_oln(m, f, crow(m, c))),
{
    lemma_xs_product(db);
    let (cr, orr, lr, nr) = (crel(db), orel(db), lrel(db), nrel(db));
    let a = product_rows(cr, orr);
    let b = product_rows(a, lr);
    // nation level
    lemma_sum_of_product(b, nr, f);
    let h1 = |x: Row| sum_of(nr, |y: Row| f(x + y));
    let h2 = |x: Row| s_n(m, f, x);
    assert forall|i: int| 0 <= i < b.len() implies h1(#[trigger] b[i]) == h2(b[i]) by {
        let x = b[i];
        lemma_sum_n(db, m, |y: Row| f(x + y));
        lemma_isum_ext(m.n_n, |n: int| (|y: Row| f(x + y))(nrow(m, n)), |n: int| f(x + nrow(m, n)));
    }
    lemma_sum_of_ext(b, h1, h2);
    // lineitem level
    lemma_sum_of_product(a, lr, h2);
    let h3 = |x: Row| sum_of(lr, |y: Row| h2(x + y));
    let h4 = |x: Row| s_ln(m, f, x);
    assert forall|i: int| 0 <= i < a.len() implies h3(#[trigger] a[i]) == h4(a[i]) by {
        let x = a[i];
        lemma_sum_l(db, m, |y: Row| h2(x + y));
        lemma_isum_ext(m.l_n, |j: int| (|y: Row| h2(x + y))(lrow(m, j)), |j: int| s_n(m, f, x + lrow(m, j)));
    }
    lemma_sum_of_ext(a, h3, h4);
    // orders level
    lemma_sum_of_product(cr, orr, h4);
    let h5 = |x: Row| sum_of(orr, |y: Row| h4(x + y));
    let h6 = |x: Row| s_oln(m, f, x);
    assert forall|i: int| 0 <= i < cr.len() implies h5(#[trigger] cr[i]) == h6(cr[i]) by {
        let x = cr[i];
        lemma_sum_o(db, m, |y: Row| h4(x + y));
        lemma_isum_ext(m.o_n, |q: int| (|y: Row| h4(x + y))(orow(m, q)), |q: int| s_ln(m, f, x + orow(m, q)));
    }
    lemma_sum_of_ext(cr, h5, h6);
    // customer level
    lemma_sum_c(db, m, h6);
    lemma_isum_ext(m.c_n, |c: int| h6(crow(m, c)), |c: int| s_oln(m, f, crow(m, c)));
}

// ------------------------------------------------------------------------------------------------ the normal form

/// WHERE over the projected row (two-valued: every read value is non-NULL and typed).
pub open spec fn q10_qual(p: QP) -> spec_fn(Row) -> bool {
    |x: Row| ival(x[0]) == ival(x[8]) && ival(x[10]) == ival(x[7]) && p.lo <= ival(x[9]) && ival(x[9]) <= p.hi
        && tval(x[13]) == r_text() && ival(x[3]) == ival(x[14])
}

/// GROUP BY c_custkey, c_name, c_acctbal, c_phone, n_name, c_address, c_comment over the projected row.
pub open spec fn q10_key() -> spec_fn(Row) -> Row {
    |x: Row| seq![x[0], x[1], x[5], x[4], x[15], x[2], x[6]]
}

/// The SUM argument's coefficient (scale 4) over the projected row.
pub open spec fn q10_argf() -> spec_fn(int, Row) -> int {
    |j: int, x: Row| ival(x[11]) * (100 - ival(x[12]))
}

/// Q10 in the accumulator normal form of `link::query`.
pub open spec fn q10_g(p: QP) -> QuerySpec {
    QuerySpec { qual: q10_qual(p), key: q10_key(), arg: q10_argf(), aggs: seq![AggKind::Sum { scale: 4 }], outs: q10_outs(), grouped: true }
}

/// The group key of customer row `c` with nation row `n`.
pub open spec fn keyc(m: M, c: int, n: int) -> Row {
    seq![Val::Int(ckey(m, c)), Val::Text(cname(m, c)), Val::Num { coeff: cbal(m, c), scale: 2 }, Val::Text(cphone(m, c)),
        Val::Text(nname(m, n)), Val::Text(caddr(m, c)), Val::Text(ccmt(m, c))]
}

/// The group key of customer row `c` (with its nation).
pub open spec fn keyq(m: M, c: int) -> Row {
    keyc(m, c, npos(m, cnat(m, c)))
}

/// Customer row `c` with nation row `n` has the key `k`.
pub open spec fn cm(m: M, c: int, n: int, k: Row) -> bool {
    cnat(m, c) == nkey(m, n) && keyc(m, c, n) == k
}

/// On a joined model row the normal form's hit and argument read the model.
pub proof fn lemma_term(m: M, p: QP, k: Row, c: int, q: int, j: int, n: int)
    ensures
        hit(q10_g(p), jrow(m, c, q, j, n), k) == (cm(m, c, n, k) && ohit(m, p, c, q) && lhit(m, q, j)),
        (q10_g(p).arg)(0, jrow(m, c, q, j, n)) == larg(m, j),
        (q10_g(p).qual)(jrow(m, c, q, j, n)) == (cnat(m, c) == nkey(m, n) && ohit(m, p, c, q) && lhit(m, q, j)),
        (q10_g(p).key)(jrow(m, c, q, j, n)) == keyc(m, c, n),
{
    let x = jrow(m, c, q, j, n);
    assert(x[0] == Val::Int(ckey(m, c)) && x[1] == Val::Text(cname(m, c)) && x[2] == Val::Text(caddr(m, c)));
    assert(x[3] == Val::Int(cnat(m, c)) && x[4] == Val::Text(cphone(m, c)));
    assert(x[5] == (Val::Num { coeff: cbal(m, c), scale: 2 }) && x[6] == Val::Text(ccmt(m, c)));
    assert(x[7] == Val::Int(okey(m, q)) && x[8] == Val::Int(ocust(m, q)) && x[9] == Val::Date(odate(m, q)));
    assert(x[10] == Val::Int(lkey(m, j)) && x[11] == (Val::Num { coeff: lprice(m, j), scale: 2 }));
    assert(x[12] == (Val::Num { coeff: ldisc(m, j), scale: 2 }) && x[13] == Val::Text(lflag(m, j)));
    assert(x[14] == Val::Int(nkey(m, n)) && x[15] == Val::Text(nname(m, n)));
    assert((q10_g(p).key)(x) =~= keyc(m, c, n));
}

// ------------------------------------------------------------------------------------------------ factoring per customer

/// The term of the quadruple sum for a lineitem weight `w`.
pub open spec fn tw(m: M, p: QP, k: Row, w: spec_fn(int) -> int, c: int, q: int, j: int, n: int) -> int {
    if cm(m, c, n, k) && ohit(m, p, c, q) && lhit(m, q, j) { w(j) } else { 0 }
}

/// The weight summed over the returned lineitems of the order at `q`.
pub open spec fn lw(m: M, q: int, w: spec_fn(int) -> int) -> int {
    isum(m.l_n, |j: int| if lhit(m, q, j) { w(j) } else { 0int })
}

/// The weight summed over customer `c`'s orders in the window.
pub open spec fn cw(m: M, p: QP, c: int, w: spec_fn(int) -> int) -> int {
    isum(m.o_n, |q: int| if ohit(m, p, c, q) { lw(m, q, w) } else { 0int })
}

pub open spec fn cm_f(m: M, c: int, k: Row) -> spec_fn(int) -> int {
    |n: int| if cm(m, c, n, k) { 1int } else { 0int }
}

/// Number of nation rows with customer `c`'s nation key giving the key `k` (0 or 1 under the primary keys).
pub open spec fn ncnt(m: M, c: int, k: Row) -> int {
    isum(m.n_n, cm_f(m, c, k))
}

/// The per-customer form of a group accumulator.
pub open spec fn per_cust(m: M, p: QP, k: Row, w: spec_fn(int) -> int) -> int {
    isum(m.c_n, |c: int| ncnt(m, c, k) * cw(m, p, c, w))
}

/// Inner sums of the factorization (named, so that they can be quantifier triggers).
pub open spec fn t_n(m: M, p: QP, k: Row, w: spec_fn(int) -> int, c: int, q: int, j: int) -> int {
    isum(m.n_n, |n: int| tw(m, p, k, w, c, q, j, n))
}

pub open spec fn t_jn(m: M, p: QP, k: Row, w: spec_fn(int) -> int, c: int, q: int) -> int {
    isum(m.l_n, |j: int| t_n(m, p, k, w, c, q, j))
}

pub open spec fn t_qjn(m: M, p: QP, k: Row, w: spec_fn(int) -> int, c: int) -> int {
    isum(m.o_n, |q: int| t_jn(m, p, k, w, c, q))
}

/// The nation sum: the nation count times the weight.
proof fn lemma_factor_n(m: M, p: QP, k: Row, w: spec_fn(int) -> int, c: int, q: int, j: int)
    ensures t_n(m, p, k, w, c, q, j) == if ohit(m, p, c, q) && lhit(m, q, j) { w(j) * ncnt(m, c, k) } else { 0int },
{
    if ohit(m, p, c, q) && lhit(m, q, j) {
        lemma_isum_scale(m.n_n, cm_f(m, c, k), w(j));
        lemma_isum_ext(m.n_n, |n: int| tw(m, p, k, w, c, q, j, n), |n: int| w(j) * cm_f(m, c, k)(n));
    } else {
        lemma_isum_zero(m.n_n, |n: int| tw(m, p, k, w, c, q, j, n));
    }
}

/// The lineitem sum: the nation count times the order's weight.
proof fn lemma_factor_jn(m: M, p: QP, k: Row, w: spec_fn(int) -> int, c: int, q: int)
    ensures t_jn(m, p, k, w, c, q) == if ohit(m, p, c, q) { ncnt(m, c, k) * lw(m, q, w) } else { 0int },
{
    let nc = ncnt(m, c, k);
    let lf = |j: int| if lhit(m, q, j) { w(j) } else { 0int };
    assert forall|j: int| 0 <= j < m.l_n implies #[trigger] t_n(m, p, k, w, c, q, j)
        == (if ohit(m, p, c, q) { nc * lf(j) } else { 0int }) by {
        lemma_factor_n(m, p, k, w, c, q, j);
        if ohit(m, p, c, q) && lhit(m, q, j) {
            assert(w(j) * nc == nc * w(j)) by (nonlinear_arith);
        }
    }
    if ohit(m, p, c, q) {
        lemma_isum_scale(m.l_n, lf, nc);
        lemma_isum_ext(m.l_n, |j: int| t_n(m, p, k, w, c, q, j), |j: int| nc * lf(j));
        lemma_isum_ext(m.l_n, lf, |j: int| if lhit(m, q, j) { w(j) } else { 0int });
    } else {
        lemma_isum_zero(m.l_n, |j: int| t_n(m, p, k, w, c, q, j));
    }
}

/// The orders sum: the nation count times the customer's weight.
proof fn lemma_factor_qjn(m: M, p: QP, k: Row, w: spec_fn(int) -> int, c: int)
    ensures t_qjn(m, p, k, w, c) == ncnt(m, c, k) * cw(m, p, c, w),
{
    let nc = ncnt(m, c, k);
    let of = |q: int| if ohit(m, p, c, q) { lw(m, q, w) } else { 0int };
    assert forall|q: int| 0 <= q < m.o_n implies #[trigger] t_jn(m, p, k, w, c, q) == nc * of(q) by {
        lemma_factor_jn(m, p, k, w, c, q);
    }
    lemma_isum_scale(m.o_n, of, nc);
    lemma_isum_ext(m.o_n, |q: int| t_jn(m, p, k, w, c, q), |q: int| nc * of(q));
    lemma_isum_ext(m.o_n, of, |q: int| if ohit(m, p, c, q) { lw(m, q, w) } else { 0int });
}

pub open spec fn w_one() -> spec_fn(int) -> int { |j: int| 1int }
pub open spec fn w_arg(m: M) -> spec_fn(int) -> int { |j: int| larg(m, j) }
pub open spec fn w_abs(m: M) -> spec_fn(int) -> int { |j: int| abs(larg(m, j)) }

/// The weights' customer sums are the customer's count, revenue and absolute revenue.
pub proof fn lemma_cw(m: M, p: QP, c: int)
    ensures
        cw(m, p, c, w_one()) == ccnt(m, p, c),
        cw(m, p, c, w_arg(m)) == csum(m, p, c),
        cw(m, p, c, w_abs(m)) == cabs(m, p, c),
{
    assert forall|q: int| 0 <= q < m.o_n implies
        (if ohit(m, p, c, q) { lw(m, q, w_one()) } else { 0int }) == #[trigger] ccnt_f(m, p, c)(q) by {
        lemma_isum_ext(m.l_n, |j: int| if lhit(m, q, j) { w_one()(j) } else { 0int }, lcnt_f(m, q));
    }
    assert forall|q: int| 0 <= q < m.o_n implies
        (if ohit(m, p, c, q) { lw(m, q, w_arg(m)) } else { 0int }) == #[trigger] csum_f(m, p, c)(q) by {
        lemma_isum_ext(m.l_n, |j: int| if lhit(m, q, j) { w_arg(m)(j) } else { 0int }, lsum_f(m, q));
    }
    assert forall|q: int| 0 <= q < m.o_n implies
        (if ohit(m, p, c, q) { lw(m, q, w_abs(m)) } else { 0int }) == #[trigger] cabs_f(m, p, c)(q) by {
        lemma_isum_ext(m.l_n, |j: int| if lhit(m, q, j) { w_abs(m)(j) } else { 0int }, labs_f(m, q));
    }
    lemma_isum_ext(m.o_n, |q: int| if ohit(m, p, c, q) { lw(m, q, w_one()) } else { 0int }, ccnt_f(m, p, c));
    lemma_isum_ext(m.o_n, |q: int| if ohit(m, p, c, q) { lw(m, q, w_arg(m)) } else { 0int }, csum_f(m, p, c));
    lemma_isum_ext(m.o_n, |q: int| if ohit(m, p, c, q) { lw(m, q, w_abs(m)) } else { 0int }, cabs_f(m, p, c));
}

/// A normal-form term over the quadruple sum, for weight `w`.
proof fn lemma_acc_one(db: Database, m: M, p: QP, k: Row, f: spec_fn(Row) -> int, w: spec_fn(int) -> int)
    requires
        db_ok(db), rel_ok(m, db),
        forall|c: int, q: int, j: int, n: int| #[trigger] f(jrow(m, c, q, j, n)) == tw(m, p, k, w, c, q, j, n),
    ensures sum_of(q10_xs(db), f) == per_cust(m, p, k, w),
{
    lemma_sum_xs(db, m, f);
    assert forall|c: int| 0 <= c < m.c_n implies #[trigger] s_oln(m, f, crow(m, c)) == ncnt(m, c, k) * cw(m, p, c, w) by {
        assert forall|q: int| 0 <= q < m.o_n implies #[trigger] s_ln(m, f, crow(m, c) + orow(m, q)) == t_jn(m, p, k, w, c, q) by {
            assert forall|j: int| 0 <= j < m.l_n implies #[trigger] s_n(m, f, crow(m, c) + orow(m, q) + lrow(m, j)) == t_n(m, p, k, w, c, q, j) by {
                assert forall|n: int| 0 <= n < m.n_n implies #[trigger] f(crow(m, c) + orow(m, q) + lrow(m, j) + nrow(m, n)) == tw(m, p, k, w, c, q, j, n) by {
                    assert(f(jrow(m, c, q, j, n)) == tw(m, p, k, w, c, q, j, n));
                }
                lemma_isum_ext(m.n_n, |n: int| f(crow(m, c) + orow(m, q) + lrow(m, j) + nrow(m, n)), |n: int| tw(m, p, k, w, c, q, j, n));
            }
            lemma_isum_ext(m.l_n, |j: int| s_n(m, f, crow(m, c) + orow(m, q) + lrow(m, j)), |j: int| t_n(m, p, k, w, c, q, j));
        }
        lemma_isum_ext(m.o_n, |q: int| s_ln(m, f, crow(m, c) + orow(m, q)), |q: int| t_jn(m, p, k, w, c, q));
        lemma_factor_qjn(m, p, k, w, c);
    }
    lemma_isum_ext(m.c_n, |c: int| s_oln(m, f, crow(m, c)), |c: int| ncnt(m, c, k) * cw(m, p, c, w));
}

/// The group accumulators of the statement, per customer.
pub proof fn lemma_acc(db: Database, m: M, p: QP, k: Row)
    requires db_ok(db), rel_ok(m, db),
    ensures
        gcount(q10_g(p), q10_xs(db), k) == per_cust(m, p, k, w_one()),
        gsum(q10_g(p), q10_xs(db), k, 0) == per_cust(m, p, k, w_arg(m)),
        gabs(q10_g(p), q10_xs(db), k, 0) == per_cust(m, p, k, w_abs(m)),
{
    let g = q10_g(p);
    let xs = q10_xs(db);
    lemma_acc_sum_of(g, xs, k, 0);
    assert forall|c: int, q: int, j: int, n: int| #[trigger] count_term(g, k)(jrow(m, c, q, j, n)) == tw(m, p, k, w_one(), c, q, j, n) by {
        lemma_term(m, p, k, c, q, j, n);
    }
    lemma_acc_one(db, m, p, k, count_term(g, k), w_one());
    assert forall|c: int, q: int, j: int, n: int| #[trigger] sum_term(g, k, 0)(jrow(m, c, q, j, n)) == tw(m, p, k, w_arg(m), c, q, j, n) by {
        lemma_term(m, p, k, c, q, j, n);
    }
    lemma_acc_one(db, m, p, k, sum_term(g, k, 0), w_arg(m));
    assert forall|c: int, q: int, j: int, n: int| #[trigger] abs_term(g, k, 0)(jrow(m, c, q, j, n)) == tw(m, p, k, w_abs(m), c, q, j, n) by {
        lemma_term(m, p, k, c, q, j, n);
    }
    lemma_acc_one(db, m, p, k, abs_term(g, k, 0), w_abs(m));
}

// ------------------------------------------------------------------------------------------------ primary keys

/// The customer row a group key names.
pub open spec fn ck_of(m: M, k: Row) -> int {
    cpos(m, ival(k[0]))
}

/// Under the nation primary key, customer `c` has at most one nation row giving the key `k`: its nation's, when that
/// gives `k`.
pub proof fn lemma_ncnt(m: M, c: int, k: Row)
    requires model_ok(m),
    ensures ncnt(m, c, k) == if npos(m, cnat(m, c)) < m.n_n && keyc(m, c, npos(m, cnat(m, c))) == k { 1int } else { 0int },
{
    let n0 = npos(m, cnat(m, c));
    crate::agent::facts::lemma_npos(m, cnat(m, c));
    let f = cm_f(m, c, k);
    assert forall|n: int| 0 <= n < m.n_n && n != n0 implies #[trigger] f(n) == 0 by {
        assert(nkey(m, n) != cnat(m, c));
    }
    lemma_isum_single(m.n_n, f, n0);
}

/// Under the customer primary key only the customer the key names contributes.
pub proof fn lemma_collapse(m: M, p: QP, k: Row, w: spec_fn(int) -> int)
    requires model_ok(m),
    ensures
        per_cust(m, p, k, w) == if 0 <= ck_of(m, k) < m.c_n { ncnt(m, ck_of(m, k), k) * cw(m, p, ck_of(m, k), w) } else { 0 },
{
    let c0 = ck_of(m, k);
    let f = |c: int| ncnt(m, c, k) * cw(m, p, c, w);
    assert forall|c: int| 0 <= c < m.c_n && c != c0 implies #[trigger] f(c) == 0 by {
        lemma_ncnt(m, c, k);
        if ncnt(m, c, k) != 0 {
            assert(keyc(m, c, npos(m, cnat(m, c))) == k);
            assert(k[0] == Val::Int(ckey(m, c)));
            crate::agent::facts::lemma_cpos(m, ckey(m, c));
            assert(ival(k[0]) == ckey(m, c));
        }
    }
    lemma_isum_single(m.c_n, f, c0);
}

/// Count of a customer's lineitems is nonnegative.
proof fn lemma_ccnt_nonneg(m: M, p: QP, c: int)
    requires model_ok(m),
    ensures ccnt(m, p, c) >= 0,
{
    assert forall|q: int| 0 <= q < m.o_n implies #[trigger] ccnt_f(m, p, c)(q) >= 0 by {
        crate::agent::phase1::lemma_labs_lsum(m, q);
    }
    lemma_isum_nonneg(0, m.o_n, ccnt_f(m, p, c));
}

/// Without a counted lineitem the customer's sums are zero.
proof fn lemma_ccnt_zero(m: M, p: QP, c: int)
    requires model_ok(m), ccnt(m, p, c) <= 0,
    ensures cabs(m, p, c) == 0,
{
    assert forall|q: int| 0 <= q < m.o_n implies #[trigger] cabs_f(m, p, c)(q) == 0 by {
        if ohit(m, p, c, q) {
            crate::agent::phase1::lemma_labs_lsum(m, q);
            if lcnt(m, q) > 0 {
                assert forall|t: int| 0 <= t < m.o_n implies #[trigger] ccnt_f(m, p, c)(t) >= 0 by {
                    crate::agent::phase1::lemma_labs_lsum(m, t);
                }
                lemma_isum_ge_term(m.o_n, ccnt_f(m, p, c), q);
            } else {
                lemma_lcnt_zero(m, q);
            }
        }
    }
    lemma_isum_zero(m.o_n, cabs_f(m, p, c));
}

/// The statement's groups are the good customers: a key has a qualifying row exactly when it is a good customer's
/// key, whose accumulators are its lineitem count and sums; every group's absolute mass is bounded under `caps_ok`.
pub proof fn lemma_groups_link(db: Database, m: M, p: QP)
    requires db_ok(db), rel_ok(m, db), model_ok(m),
    ensures
        forall|k: Row| #[trigger] gcount(q10_g(p), q10_xs(db), k) > 0 <==> (0 <= ck_of(m, k) < m.c_n && good(m, p, ck_of(m, k)) && keyq(m, ck_of(m, k)) == k),
        forall|c: int| 0 <= c < m.c_n && #[trigger] good(m, p, c) ==> {
            &&& ck_of(m, keyq(m, c)) == c
            &&& gcount(q10_g(p), q10_xs(db), keyq(m, c)) == ccnt(m, p, c)
            &&& gsum(q10_g(p), q10_xs(db), keyq(m, c), 0) == csum(m, p, c)
            &&& gabs(q10_g(p), q10_xs(db), keyq(m, c), 0) == cabs(m, p, c)
        },
        caps_ok(m, p) ==> forall|k: Row| #[trigger] gabs(q10_g(p), q10_xs(db), k, 0) <= i128_max(),
{
    let g = q10_g(p);
    let xs = q10_xs(db);
    assert forall|k: Row| #[trigger] gcount(g, xs, k) > 0 <==> (0 <= ck_of(m, k) < m.c_n && good(m, p, ck_of(m, k)) && keyq(m, ck_of(m, k)) == k) by {
        lemma_acc(db, m, p, k);
        lemma_collapse(m, p, k, w_one());
        let c0 = ck_of(m, k);
        if 0 <= c0 < m.c_n {
            lemma_cw(m, p, c0);
            lemma_ncnt(m, c0, k);
            lemma_ccnt_nonneg(m, p, c0);
            let (nc, cc) = (ncnt(m, c0, k), ccnt(m, p, c0));
            assert(nc * cc > 0 <==> (nc > 0 && cc > 0)) by (nonlinear_arith) requires 0 <= nc <= 1, cc >= 0;
        }
    }
    assert forall|c: int| 0 <= c < m.c_n && #[trigger] good(m, p, c) implies {
        &&& ck_of(m, keyq(m, c)) == c
        &&& gcount(g, xs, keyq(m, c)) == ccnt(m, p, c)
        &&& gsum(g, xs, keyq(m, c), 0) == csum(m, p, c)
        &&& gabs(g, xs, keyq(m, c), 0) == cabs(m, p, c)
    } by {
        let k = keyq(m, c);
        crate::agent::facts::lemma_cpos(m, ckey(m, c));
        assert(ival(k[0]) == ckey(m, c));
        assert(ck_of(m, k) == c);
        lemma_acc(db, m, p, k);
        lemma_collapse(m, p, k, w_one());
        lemma_collapse(m, p, k, w_arg(m));
        lemma_collapse(m, p, k, w_abs(m));
        lemma_cw(m, p, c);
        lemma_ncnt(m, c, k);
        assert(ncnt(m, c, k) == 1);
    }
    if caps_ok(m, p) {
        assert forall|k: Row| #[trigger] gabs(g, xs, k, 0) <= i128_max() by {
            lemma_acc(db, m, p, k);
            lemma_collapse(m, p, k, w_abs(m));
            let c0 = ck_of(m, k);
            if 0 <= c0 < m.c_n {
                lemma_cw(m, p, c0);
                lemma_ncnt(m, c0, k);
                let nc = ncnt(m, c0, k);
                if nc == 0 {
                    assert(nc * cabs(m, p, c0) == 0);
                } else if ccnt(m, p, c0) <= 0 {
                    lemma_ccnt_zero(m, p, c0);
                } else {
                    assert(good(m, p, c0));
                    assert(cabs(m, p, c0) <= i128_max());
                }
            }
        }
    }
}

} // verus!
