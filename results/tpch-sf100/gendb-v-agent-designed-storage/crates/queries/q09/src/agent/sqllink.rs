//! The relational link of Q9, part 1: the FROM product `part x supplier x lineitem x partsupp x orders x nation` of
//! a database bound to the parts, projected on the 17 columns the statement reads (`q9_cols`), is the product of the
//! model's rows (`jrow`, `lemma_xs_product`); every FROM row reads a model row (`lemma_from_row`); and a sum over the
//! projected FROM rows is a six-fold index sum over the model (`lemma_sum_xs`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::types::*;
use crate::spec::typing::{db_wf, row_in_table};
use crate::spec::numeric::pow10;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::product_rows;
use crate::schema::schema_spec;
use crate::link::query::*;
use crate::link::join::{sum_of, shift, lemma_sum_of_product, lemma_sum_of_ext, lemma_sum_of_perm, lemma_proj_product};
use crate::link::source::lemma_proj_all_index;
use crate::link::expr::ival;
use crate::bridge::relation::{is_concat, lemma_product_rows_elems};
use crate::stores::facts::interface::common::colfmt as ff;
use super::common::isum::*;
use super::model::*;
use super::sqlrow::*;

verus! {

// ------------------------------------------------------------------------------------------------ the FROM rows

/// The FROM product in canonical order.
pub open spec fn from_rows(db: Database) -> Seq<Row> {
    product_rows(product_rows(product_rows(product_rows(product_rows(db.tables[3], db.tables[5]), db.tables[0]),
        db.tables[4]), db.tables[1]), db.tables[6])
}

pub open spec fn prel(db: Database) -> Seq<Row> { proj_all(db.tables[3], pcols()) }
pub open spec fn srel(db: Database) -> Seq<Row> { proj_all(db.tables[5], scols()) }
pub open spec fn lrel(db: Database) -> Seq<Row> { proj_all(db.tables[0], lcols()) }
pub open spec fn trel(db: Database) -> Seq<Row> { proj_all(db.tables[4], tcols()) }
pub open spec fn orel(db: Database) -> Seq<Row> { proj_all(db.tables[1], ocols()) }
pub open spec fn nrel(db: Database) -> Seq<Row> { proj_all(db.tables[6], ncols()) }

/// The projected FROM rows.
pub open spec fn xs_of(db: Database) -> Seq<Row> {
    proj_all(from_rows(db), q9_cols())
}

/// A joined model row: part row `c`, supplier row `s`, lineitem row `j`, partsupp row `t`, orders position `q`,
/// nation row `n`.
pub open spec fn jrow(m: M, c: int, s: int, j: int, t: int, q: int, n: int) -> Row {
    prow(m, c) + srow(m, s) + lrow(m, j) + trow(m, t) + orow(m, q) + nrow(m, n)
}

/// The database facts the link needs.
pub open spec fn db_ok(db: Database) -> bool {
    db.schema == schema_spec() && db_wf(db)
}

pub proof fn lemma_from_eval(db: Database)
    requires db.tables.len() == 8,
    ensures eval_query(db, Seq::empty(), q9_from()) == Ok::<Relation, SqlError>(from_rows(db)),
{
    let e = Seq::<Val>::empty();
    assert(eval_query(db, e, Query::Table(3)) == Ok::<Relation, SqlError>(db.tables[3]));
    assert(eval_query(db, e, Query::Table(5)) == Ok::<Relation, SqlError>(db.tables[5]));
    assert(eval_query(db, e, Query::Table(0)) == Ok::<Relation, SqlError>(db.tables[0]));
    assert(eval_query(db, e, Query::Table(4)) == Ok::<Relation, SqlError>(db.tables[4]));
    assert(eval_query(db, e, Query::Table(1)) == Ok::<Relation, SqlError>(db.tables[1]));
    assert(eval_query(db, e, Query::Table(6)) == Ok::<Relation, SqlError>(db.tables[6]));
    let p1 = Query::Product { left: Box::new(Query::Table(3)), right: Box::new(Query::Table(5)) };
    assert(eval_query(db, e, p1) == Ok::<Relation, SqlError>(product_rows(db.tables[3], db.tables[5])));
    let p2 = Query::Product { left: Box::new(p1), right: Box::new(Query::Table(0)) };
    assert(eval_query(db, e, p2) == Ok::<Relation, SqlError>(product_rows(product_rows(db.tables[3], db.tables[5]), db.tables[0])));
    let p3 = Query::Product { left: Box::new(p2), right: Box::new(Query::Table(4)) };
    assert(eval_query(db, e, p3) == Ok::<Relation, SqlError>(product_rows(product_rows(product_rows(db.tables[3], db.tables[5]), db.tables[0]), db.tables[4])));
    let p4 = Query::Product { left: Box::new(p3), right: Box::new(Query::Table(1)) };
    assert(eval_query(db, e, p4) == Ok::<Relation, SqlError>(product_rows(product_rows(product_rows(product_rows(db.tables[3], db.tables[5]), db.tables[0]), db.tables[4]), db.tables[1])));
    assert(q9_from() == Query::Product { left: Box::new(p4), right: Box::new(Query::Table(6)) });
}

/// Row widths of the six tables.
pub proof fn lemma_widths(db: Database)
    requires db_ok(db),
    ensures
        db.tables.len() == 8,
        forall|i: int| 0 <= i < db.tables[3].len() ==> (#[trigger] db.tables[3][i]).len() == 9,
        forall|i: int| 0 <= i < db.tables[5].len() ==> (#[trigger] db.tables[5][i]).len() == 7,
        forall|i: int| 0 <= i < db.tables[0].len() ==> (#[trigger] db.tables[0][i]).len() == 16,
        forall|i: int| 0 <= i < db.tables[4].len() ==> (#[trigger] db.tables[4][i]).len() == 5,
        forall|i: int| 0 <= i < db.tables[1].len() ==> (#[trigger] db.tables[1][i]).len() == 9,
        forall|i: int| 0 <= i < db.tables[6].len() ==> (#[trigger] db.tables[6][i]).len() == 4,
{
    crate::stores::facts::declaration::lemma_declared_schema();
    crate::stores::custpart::declaration::lemma_declared_schema();
    crate::stores::suppliers::declaration::lemma_declared_schema();
    assert(schema_spec()[0].columns.len() == 16) by (compute);
    assert(schema_spec()[1].columns.len() == 9) by (compute);
    assert forall|i: int| 0 <= i < db.tables[3].len() implies (#[trigger] db.tables[3][i]).len() == 9 by {
        assert(row_in_table(db.tables[3][i], db.schema[3]));
    }
    assert forall|i: int| 0 <= i < db.tables[5].len() implies (#[trigger] db.tables[5][i]).len() == 7 by {
        assert(row_in_table(db.tables[5][i], db.schema[5]));
    }
    assert forall|i: int| 0 <= i < db.tables[0].len() implies (#[trigger] db.tables[0][i]).len() == 16 by {
        assert(row_in_table(db.tables[0][i], db.schema[0]));
    }
    assert forall|i: int| 0 <= i < db.tables[4].len() implies (#[trigger] db.tables[4][i]).len() == 5 by {
        assert(row_in_table(db.tables[4][i], db.schema[4]));
    }
    assert forall|i: int| 0 <= i < db.tables[1].len() implies (#[trigger] db.tables[1][i]).len() == 9 by {
        assert(row_in_table(db.tables[1][i], db.schema[1]));
    }
    assert forall|i: int| 0 <= i < db.tables[6].len() implies (#[trigger] db.tables[6][i]).len() == 4 by {
        assert(row_in_table(db.tables[6][i], db.schema[6]));
    }
}

/// Rows of a product of relations of widths `wa` and `wb` have width `wa + wb`.
proof fn lemma_product_width(a: Seq<Row>, b: Seq<Row>, wa: nat, wb: nat)
    requires
        forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i]).len() == wa,
        forall|i: int| 0 <= i < b.len() ==> (#[trigger] b[i]).len() == wb,
    ensures forall|i: int| 0 <= i < product_rows(a, b).len() ==> (#[trigger] product_rows(a, b)[i]).len() == wa + wb,
{
    lemma_product_rows_elems(a, b);
    let pr = product_rows(a, b);
    assert forall|i: int| 0 <= i < pr.len() implies (#[trigger] pr[i]).len() == wa + wb by {
        assert(is_concat(pr[i], a, b));
        let (x, y) = choose|x: int, y: int| 0 <= x < a.len() && 0 <= y < b.len() && pr[i] == #[trigger] a[x] + #[trigger] b[y];
    }
}

/// One step of the projected product: the projection of `a x b` on `ca ++ shift(cb, wa)`.
proof fn lemma_proj_step(a: Seq<Row>, b: Seq<Row>, ca: Seq<nat>, cb: Seq<nat>, wa: nat, wb: nat)
    requires
        forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i]).len() == wa,
        forall|i: int| 0 <= i < b.len() ==> (#[trigger] b[i]).len() == wb,
        forall|k: int| 0 <= k < ca.len() ==> #[trigger] ca[k] < wa,
        forall|k: int| 0 <= k < cb.len() ==> #[trigger] cb[k] < wb,
    ensures
        proj_all(product_rows(a, b), ca + shift(cb, wa)) == product_rows(proj_all(a, ca), proj_all(b, cb)),
        forall|i: int| 0 <= i < product_rows(a, b).len() ==> (#[trigger] product_rows(a, b)[i]).len() == wa + wb,
        forall|k: int| 0 <= k < (ca + shift(cb, wa)).len() ==> #[trigger] (ca + shift(cb, wa))[k] < wa + wb,
{
    lemma_proj_product(a, b, ca, cb, wa, wb);
    lemma_product_width(a, b, wa, wb);
    let cs = ca + shift(cb, wa);
    assert forall|k: int| 0 <= k < cs.len() implies #[trigger] cs[k] < wa + wb by {
        if k >= ca.len() {
            assert(cs[k] == cb[k - ca.len()] + wa);
        }
    }
}

/// The projected FROM rows are the product of the projected tables.
pub proof fn lemma_xs_product(db: Database)
    requires db_ok(db),
    ensures
        xs_of(db) == product_rows(product_rows(product_rows(product_rows(product_rows(prel(db), srel(db)), lrel(db)),
            trel(db)), orel(db)), nrel(db)),
        forall|i: int| 0 <= i < from_rows(db).len() ==> (#[trigger] from_rows(db)[i]).len() == 50,
{
    lemma_widths(db);
    let (t3, t5, t0, t4, t1, t6) = (db.tables[3], db.tables[5], db.tables[0], db.tables[4], db.tables[1], db.tables[6]);
    assert forall|k: int| 0 <= k < pcols().len() implies #[trigger] pcols()[k] < 9 by {}
    assert forall|k: int| 0 <= k < scols().len() implies #[trigger] scols()[k] < 7 by {}
    assert forall|k: int| 0 <= k < lcols().len() implies #[trigger] lcols()[k] < 16 by {}
    assert forall|k: int| 0 <= k < tcols().len() implies #[trigger] tcols()[k] < 5 by {}
    assert forall|k: int| 0 <= k < ocols().len() implies #[trigger] ocols()[k] < 9 by {}
    assert forall|k: int| 0 <= k < ncols().len() implies #[trigger] ncols()[k] < 4 by {}
    lemma_proj_step(t3, t5, pcols(), scols(), 9, 7);
    let a1 = product_rows(t3, t5);
    let c1 = pcols() + shift(scols(), 9);
    lemma_proj_step(a1, t0, c1, lcols(), 16, 16);
    let a2 = product_rows(a1, t0);
    let c2 = c1 + shift(lcols(), 16);
    lemma_proj_step(a2, t4, c2, tcols(), 32, 5);
    let a3 = product_rows(a2, t4);
    let c3 = c2 + shift(tcols(), 32);
    lemma_proj_step(a3, t1, c3, ocols(), 37, 9);
    let a4 = product_rows(a3, t1);
    let c4 = c3 + shift(ocols(), 37);
    lemma_proj_step(a4, t6, c4, ncols(), 46, 4);
    assert(c4 + shift(ncols(), 46) =~= q9_cols());
}

/// A FROM row: one row of each table, read through the model.
pub proof fn lemma_from_row(db: Database, m: M, i: int) -> (r: (int, int, int, int, int, int))
    requires
        db_ok(db),
        rel_ok(m, db),
        0 <= i < from_rows(db).len(),
    ensures ({
        let (c, s, j, t, q, n) = r;
        &&& 0 <= c < m.p_n && 0 <= s < m.s_n && 0 <= j < m.l_n && 0 <= t < m.t_n && 0 <= q < m.o_n && 0 <= n < m.n_n
        &&& env_reads(from_rows(db)[i], jrow(m, c, s, j, t, q, n))
    }),
{
    lemma_widths(db);
    lemma_xs_product(db);
    let (t3, t5, t0, t4, t1, t6) = (db.tables[3], db.tables[5], db.tables[0], db.tables[4], db.tables[1], db.tables[6]);
    let a1 = product_rows(t3, t5);
    let a2 = product_rows(a1, t0);
    let a3 = product_rows(a2, t4);
    let a4 = product_rows(a3, t1);
    let env = from_rows(db)[i];
    lemma_product_rows_elems(a4, t6);
    assert(is_concat(env, a4, t6));
    let (i4, ni) = choose|x: int, y: int| 0 <= x < a4.len() && 0 <= y < t6.len() && env == #[trigger] a4[x] + #[trigger] t6[y];
    lemma_product_rows_elems(a3, t1);
    assert(is_concat(a4[i4], a3, t1));
    let (i3, oi) = choose|x: int, y: int| 0 <= x < a3.len() && 0 <= y < t1.len() && a4[i4] == #[trigger] a3[x] + #[trigger] t1[y];
    lemma_product_rows_elems(a2, t4);
    assert(is_concat(a3[i3], a2, t4));
    let (i2, ti) = choose|x: int, y: int| 0 <= x < a2.len() && 0 <= y < t4.len() && a3[i3] == #[trigger] a2[x] + #[trigger] t4[y];
    lemma_product_rows_elems(a1, t0);
    assert(is_concat(a2[i2], a1, t0));
    let (i1, li) = choose|x: int, y: int| 0 <= x < a1.len() && 0 <= y < t0.len() && a2[i2] == #[trigger] a1[x] + #[trigger] t0[y];
    lemma_product_rows_elems(t3, t5);
    assert(is_concat(a1[i1], t3, t5));
    let (c, s) = choose|x: int, y: int| 0 <= x < t3.len() && 0 <= y < t5.len() && a1[i1] == #[trigger] t3[x] + #[trigger] t5[y];
    assert(ff::covered(m.l_map, li));
    let j = choose|j: int| 0 <= j < m.l_map.len() && m.l_map[j] == li;
    assert(ff::covered(m.o_map, oi));
    let q = choose|q: int| 0 <= q < m.o_map.len() && m.o_map[q] == oi;
    let (rp, rs, rl, rt, ro, rn) = (t3[c], t5[s], t0[li], t4[ti], t1[oi], t6[ni]);
    assert(proj(rp, pcols()) == prow(m, c));
    assert(proj(rs, scols()) == srow(m, s));
    assert(proj(rl, lcols()) == lrow(m, j));
    assert(proj(rt, tcols()) == trow(m, ti));
    assert(proj(ro, ocols()) == orow(m, q));
    assert(proj(rn, ncols()) == nrow(m, ni));
    assert(env == rp + rs + rl + rt + ro + rn);
    let x = jrow(m, c, s, j, ti, q, ni);
    assert(proj(env, q9_cols()) =~= x) by {
        assert(proj(rp, pcols())[0] == rp[0] && proj(rp, pcols())[1] == rp[1]);
        assert(proj(rs, scols())[0] == rs[0] && proj(rs, scols())[1] == rs[3]);
        assert(proj(rl, lcols())[0] == rl[0] && proj(rl, lcols())[1] == rl[1] && proj(rl, lcols())[2] == rl[2]);
        assert(proj(rl, lcols())[3] == rl[4] && proj(rl, lcols())[4] == rl[5] && proj(rl, lcols())[5] == rl[6]);
        assert(proj(rt, tcols())[0] == rt[0] && proj(rt, tcols())[1] == rt[1] && proj(rt, tcols())[2] == rt[3]);
        assert(proj(ro, ocols())[0] == ro[0] && proj(ro, ocols())[1] == ro[4]);
        assert(proj(rn, ncols())[0] == rn[0] && proj(rn, ncols())[1] == rn[1]);
    }
    (c, s, j, ti, q, ni)
}

/// A joined model row of in-range indices has the declared types.
pub proof fn lemma_jrow_typed(m: M, c: int, s: int, j: int, t: int, q: int, n: int)
    requires
        model_ok(m),
        0 <= c < m.p_n && 0 <= s < m.s_n && 0 <= j < m.l_n && 0 <= t < m.t_n && 0 <= q < m.o_n && 0 <= n < m.n_n,
    ensures ({
        let x = jrow(m, c, s, j, t, q, n);
        &&& xrow_typed(x)
        &&& x[0] == Val::Int(pkey(m, c)) && x[1] == Val::Text(pname(m, c))
        &&& x[2] == Val::Int(skey(m, s)) && x[3] == Val::Int(snk(m, s))
        &&& x[4] == Val::Int(lok(m, j)) && x[5] == Val::Int(lpk(m, j)) && x[6] == Val::Int(lsk(m, j))
        &&& x[7] == (Val::Num { coeff: lqty(m, j), scale: 2 }) && x[8] == (Val::Num { coeff: lprice(m, j), scale: 2 })
        &&& x[9] == (Val::Num { coeff: ldisc(m, j), scale: 2 })
        &&& x[10] == Val::Int(tpk(m, t)) && x[11] == Val::Int(tsk(m, t)) && x[12] == (Val::Num { coeff: tcost(m, t), scale: 2 })
        &&& x[13] == Val::Int(okey(m, q)) && x[14] == Val::Date(odate(m, q))
        &&& x[15] == Val::Int(nkey(m, n)) && x[16] == Val::Text(nname(m, n))
    }),
{
    super::lookups::lemma_lvals(m, j);
    super::lookups::lemma_tvals(m, t);
    super::lookups::lemma_ovals(m, q);
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

/// Sums over the canonical-order relations are sums over the model's rows.
pub proof fn lemma_sum_p(db: Database, m: M, h: spec_fn(Row) -> int)
    requires rel_ok(m, db),
    ensures sum_of(prel(db), h) == isum(m.p_n, |c: int| h(prow(m, c))),
{
    lemma_proj_all_index(db.tables[3], pcols());
    assert(prel(db) =~= Seq::new(m.p_n as nat, |c: int| prow(m, c)));
    lemma_sum_of_seq(m.p_n, |c: int| prow(m, c), h);
    lemma_isum_ext(m.p_n, |i: int| h((|c: int| prow(m, c))(i)), |c: int| h(prow(m, c)));
}

pub proof fn lemma_sum_s(db: Database, m: M, h: spec_fn(Row) -> int)
    requires rel_ok(m, db),
    ensures sum_of(srel(db), h) == isum(m.s_n, |s: int| h(srow(m, s))),
{
    lemma_proj_all_index(db.tables[5], scols());
    assert(srel(db) =~= Seq::new(m.s_n as nat, |s: int| srow(m, s)));
    lemma_sum_of_seq(m.s_n, |s: int| srow(m, s), h);
    lemma_isum_ext(m.s_n, |i: int| h((|s: int| srow(m, s))(i)), |s: int| h(srow(m, s)));
}

pub proof fn lemma_sum_t(db: Database, m: M, h: spec_fn(Row) -> int)
    requires rel_ok(m, db),
    ensures sum_of(trel(db), h) == isum(m.t_n, |t: int| h(trow(m, t))),
{
    lemma_proj_all_index(db.tables[4], tcols());
    assert(trel(db) =~= Seq::new(m.t_n as nat, |t: int| trow(m, t)));
    lemma_sum_of_seq(m.t_n, |t: int| trow(m, t), h);
    lemma_isum_ext(m.t_n, |i: int| h((|t: int| trow(m, t))(i)), |t: int| h(trow(m, t)));
}

pub proof fn lemma_sum_n(db: Database, m: M, h: spec_fn(Row) -> int)
    requires rel_ok(m, db),
    ensures sum_of(nrel(db), h) == isum(m.n_n, |n: int| h(nrow(m, n))),
{
    lemma_proj_all_index(db.tables[6], ncols());
    assert(nrel(db) =~= Seq::new(m.n_n as nat, |n: int| nrow(m, n)));
    lemma_sum_of_seq(m.n_n, |n: int| nrow(m, n), h);
    lemma_isum_ext(m.n_n, |i: int| h((|n: int| nrow(m, n))(i)), |n: int| h(nrow(m, n)));
}

// ------------------------------------------------------------------------------------------------ nested sums

/// The nested index sums of `f` over the joined model rows, innermost (nation) first.
pub open spec fn s6(m: M, f: spec_fn(Row) -> int, x: Row) -> int { isum(m.n_n, |n: int| f(x + nrow(m, n))) }
pub open spec fn s5(m: M, f: spec_fn(Row) -> int, x: Row) -> int { isum(m.o_n, |q: int| s6(m, f, x + orow(m, q))) }
pub open spec fn s4(m: M, f: spec_fn(Row) -> int, x: Row) -> int { isum(m.t_n, |t: int| s5(m, f, x + trow(m, t))) }
pub open spec fn s3(m: M, f: spec_fn(Row) -> int, x: Row) -> int { isum(m.l_n, |j: int| s4(m, f, x + lrow(m, j))) }
pub open spec fn s2(m: M, f: spec_fn(Row) -> int, x: Row) -> int { isum(m.s_n, |s: int| s3(m, f, x + srow(m, s))) }

/// One product level: the sum over `a x b` of `f` is the sum over `a` of the inner model sum `inner`.
proof fn lemma_level(a: Seq<Row>, b: Seq<Row>, f: spec_fn(Row) -> int, inner: spec_fn(Row) -> int)
    requires forall|x: Row| #[trigger] inner(x) == sum_of(b, |y: Row| f(x + y)),
    ensures sum_of(product_rows(a, b), f) == sum_of(a, inner),
{
    lemma_sum_of_product(a, b, f);
    let h1 = |x: Row| sum_of(b, |y: Row| f(x + y));
    assert forall|i: int| 0 <= i < a.len() implies h1(#[trigger] a[i]) == inner(a[i]) by {}
    lemma_sum_of_ext(a, h1, inner);
}

/// A sum over the projected FROM rows is the six-fold index sum over the model.
pub proof fn lemma_sum_xs(db: Database, m: M, f: spec_fn(Row) -> int)
    requires db_ok(db), rel_ok(m, db),
    ensures sum_of(xs_of(db), f) == isum(m.p_n, |c: int| s2(m, f, prow(m, c))),
{
    lemma_xs_product(db);
    let (pr, sr, lr, tr, orr, nr) = (prel(db), srel(db), lrel(db), trel(db), orel(db), nrel(db));
    let a1 = product_rows(pr, sr);
    let a2 = product_rows(a1, lr);
    let a3 = product_rows(a2, tr);
    let a4 = product_rows(a3, orr);
    // nation
    let i6 = |x: Row| s6(m, f, x);
    assert forall|x: Row| #[trigger] i6(x) == sum_of(nr, |y: Row| f(x + y)) by {
        lemma_sum_n(db, m, |y: Row| f(x + y));
        lemma_isum_ext(m.n_n, |n: int| (|y: Row| f(x + y))(nrow(m, n)), |n: int| f(x + nrow(m, n)));
    }
    lemma_level(a4, nr, f, i6);
    // orders
    let i5 = |x: Row| s5(m, f, x);
    assert forall|x: Row| #[trigger] i5(x) == sum_of(orr, |y: Row| i6(x + y)) by {
        lemma_sum_o(db, m, |y: Row| i6(x + y));
        lemma_isum_ext(m.o_n, |q: int| (|y: Row| i6(x + y))(orow(m, q)), |q: int| s6(m, f, x + orow(m, q)));
    }
    lemma_level(a3, orr, i6, i5);
    // partsupp
    let i4 = |x: Row| s4(m, f, x);
    assert forall|x: Row| #[trigger] i4(x) == sum_of(tr, |y: Row| i5(x + y)) by {
        lemma_sum_t(db, m, |y: Row| i5(x + y));
        lemma_isum_ext(m.t_n, |t: int| (|y: Row| i5(x + y))(trow(m, t)), |t: int| s5(m, f, x + trow(m, t)));
    }
    lemma_level(a2, tr, i5, i4);
    // lineitem
    let i3 = |x: Row| s3(m, f, x);
    assert forall|x: Row| #[trigger] i3(x) == sum_of(lr, |y: Row| i4(x + y)) by {
        lemma_sum_l(db, m, |y: Row| i4(x + y));
        lemma_isum_ext(m.l_n, |j: int| (|y: Row| i4(x + y))(lrow(m, j)), |j: int| s4(m, f, x + lrow(m, j)));
    }
    lemma_level(a1, lr, i4, i3);
    // supplier
    let i2 = |x: Row| s2(m, f, x);
    assert forall|x: Row| #[trigger] i2(x) == sum_of(sr, |y: Row| i3(x + y)) by {
        lemma_sum_s(db, m, |y: Row| i3(x + y));
        lemma_isum_ext(m.s_n, |s: int| (|y: Row| i3(x + y))(srow(m, s)), |s: int| s3(m, f, x + srow(m, s)));
    }
    lemma_level(pr, sr, i3, i2);
    // part
    lemma_sum_p(db, m, i2);
    lemma_isum_ext(m.p_n, |c: int| i2(prow(m, c)), |c: int| s2(m, f, prow(m, c)));
}

} // verus!
