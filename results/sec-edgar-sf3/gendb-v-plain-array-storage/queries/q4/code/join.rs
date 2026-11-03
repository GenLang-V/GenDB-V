//! The FROM and WHERE of the statement as relations: on a database whose tables are the stored rows (`db_ok`), the
//! WHERE node evaluates to `st4(nrows)` (`lemma_eval_where_node`), the product of num with sub, tag and pre kept
//! by the three join conditions and the WHERE, each a `keep` of the condition's `True` rows (no condition is ever
//! an error: every row of every product is a concatenation of table rows, `shape*`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::bridge::collect::lemma_collect_all;
use crate::bridge::relation::{is_concat, lemma_product_rows_elems};
use crate::exec::relational::domain::lemma_collect_pointwise;
use crate::link::join::*;
use crate::agent::cols::*;
use crate::agent::sem::*;

verus! {

pub open spec fn nrows(c: Ctx) -> Seq<Row> { Seq::new(c.n as nat, |i: int| nrow(c, i)) }
pub open spec fn srows(c: Ctx) -> Seq<Row> { Seq::new(c.m as nat, |s: int| srow(c, s)) }
pub open spec fn trows(c: Ctx) -> Seq<Row> { Seq::new(c.nt as nat, |k: int| trow(c, k)) }
pub open spec fn prows(c: Ctx) -> Seq<Row> { Seq::new(c.npre as nat, |l: int| prow(c, l)) }

/// The rows on which `pred` is `True`.
pub open spec fn holds(db: Database, pred: Pred) -> spec_fn(Row) -> bool {
    |x: Row| eval_pred(db, x, pred) == Ok::<Truth, SqlError>(Truth::True)
}

pub open spec fn st1(db: Database, c: Ctx, a: Seq<Row>) -> Seq<Row> {
    keep(product_rows(a, srows(c)), holds(db, p_ns()))
}

pub open spec fn st2(db: Database, c: Ctx, a: Seq<Row>) -> Seq<Row> {
    keep(product_rows(st1(db, c, a), trows(c)), holds(db, p_nt()))
}

pub open spec fn st3(db: Database, c: Ctx, a: Seq<Row>) -> Seq<Row> {
    keep(product_rows(st2(db, c, a), prows(c)), holds(db, p_np()))
}

pub open spec fn st4(db: Database, c: Ctx, ps: Seq<Literal>, a: Seq<Row>) -> Seq<Row> {
    keep(st3(db, c, a), holds(db, p_where(ps)))
}

/// The tables of a database with `db_ok`.
pub proof fn lemma_tables(db: Database, c: Ctx)
    requires db_ok(db, c),
    ensures
        db.tables[1] == nrows(c), db.tables[0] == srows(c), db.tables[2] == trows(c), db.tables[3] == prows(c),
{
    assert(db.tables[1] =~= nrows(c));
    assert(db.tables[0] =~= srows(c));
    assert(db.tables[2] =~= trows(c));
    assert(db.tables[3] =~= prows(c));
}

// ------------------------------------------------------------------------------------------------ shapes

pub open spec fn shape1(c: Ctx, x: Row) -> bool {
    exists|i: int, s: int| 0 <= i < c.n && 0 <= s < c.m && x == #[trigger] ns_row(c, i, s)
}

pub open spec fn shape2(c: Ctx, x: Row) -> bool {
    exists|i: int, s: int, k: int| 0 <= i < c.n && 0 <= s < c.m && 0 <= k < c.nt && x == #[trigger] nst_row(c, i, s, k)
}

pub open spec fn shape3(c: Ctx, x: Row) -> bool {
    exists|i: int, s: int, k: int, l: int| 0 <= i < c.n && 0 <= s < c.m && 0 <= k < c.nt && 0 <= l < c.npre
        && x == #[trigger] full_row(c, i, s, k, l)
}

/// Every row of `nrows x srows` is a num row joined with a sub row.
proof fn lemma_shape1(c: Ctx, a: Seq<Row>)
    requires 0 <= c.m, forall|q: int| 0 <= q < a.len() ==> exists|i: int| 0 <= i < c.n && #[trigger] a[q] == nrow(c, i),
    ensures forall|q: int| 0 <= q < product_rows(a, srows(c)).len() ==> shape1(c, #[trigger] product_rows(a, srows(c))[q]),
{
    lemma_product_rows_elems(a, srows(c));
    assert forall|q: int| 0 <= q < product_rows(a, srows(c)).len() implies shape1(c, #[trigger] product_rows(a, srows(c))[q]) by {
        let x = product_rows(a, srows(c))[q];
        assert(is_concat(x, a, srows(c)));
        let (u, v) = choose|u: int, v: int| 0 <= u < a.len() && 0 <= v < srows(c).len() && x == #[trigger] a[u] + #[trigger] srows(c)[v];
        let i = choose|i: int| 0 <= i < c.n && #[trigger] a[u] == nrow(c, i);
        assert(srows(c)[v] == srow(c, v));
        assert(x == ns_row(c, i, v));
    }
}

/// Rows of a `keep` are rows of its input.
proof fn lemma_kept<P>(rows: Seq<Row>, f: spec_fn(Row) -> bool, shape: spec_fn(Row) -> bool)
    requires forall|q: int| 0 <= q < rows.len() ==> shape(#[trigger] rows[q]),
    ensures forall|q: int| 0 <= q < keep(rows, f).len() ==> shape(#[trigger] keep(rows, f)[q]),
{
    lemma_keep_members(rows, f);
    assert forall|q: int| 0 <= q < keep(rows, f).len() implies shape(#[trigger] keep(rows, f)[q]) by {
        let w = choose|w: int| 0 <= w < rows.len() && rows[w] == keep(rows, f)[q];
    }
}

proof fn lemma_shape2(c: Ctx, a: Seq<Row>)
    requires 0 <= c.nt, forall|q: int| 0 <= q < a.len() ==> shape1(c, #[trigger] a[q]),
    ensures forall|q: int| 0 <= q < product_rows(a, trows(c)).len() ==> shape2(c, #[trigger] product_rows(a, trows(c))[q]),
{
    lemma_product_rows_elems(a, trows(c));
    assert forall|q: int| 0 <= q < product_rows(a, trows(c)).len() implies shape2(c, #[trigger] product_rows(a, trows(c))[q]) by {
        let x = product_rows(a, trows(c))[q];
        assert(is_concat(x, a, trows(c)));
        let (u, v) = choose|u: int, v: int| 0 <= u < a.len() && 0 <= v < trows(c).len() && x == #[trigger] a[u] + #[trigger] trows(c)[v];
        assert(shape1(c, a[u]));
        let (i, s) = choose|i: int, s: int| 0 <= i < c.n && 0 <= s < c.m && a[u] == #[trigger] ns_row(c, i, s);
        assert(trows(c)[v] == trow(c, v));
        assert(x == nst_row(c, i, s, v));
    }
}

proof fn lemma_shape3(c: Ctx, a: Seq<Row>)
    requires 0 <= c.npre, forall|q: int| 0 <= q < a.len() ==> shape2(c, #[trigger] a[q]),
    ensures forall|q: int| 0 <= q < product_rows(a, prows(c)).len() ==> shape3(c, #[trigger] product_rows(a, prows(c))[q]),
{
    lemma_product_rows_elems(a, prows(c));
    assert forall|q: int| 0 <= q < product_rows(a, prows(c)).len() implies shape3(c, #[trigger] product_rows(a, prows(c))[q]) by {
        let x = product_rows(a, prows(c))[q];
        assert(is_concat(x, a, prows(c)));
        let (u, v) = choose|u: int, v: int| 0 <= u < a.len() && 0 <= v < prows(c).len() && x == #[trigger] a[u] + #[trigger] prows(c)[v];
        assert(shape2(c, a[u]));
        let (i, s, k) = choose|i: int, s: int, k: int| 0 <= i < c.n && 0 <= s < c.m && 0 <= k < c.nt && a[u] == #[trigger] nst_row(c, i, s, k);
        assert(prows(c)[v] == prow(c, v));
        assert(x == full_row(c, i, s, k, v));
    }
}

// ------------------------------------------------------------------------------------------------ filters

/// SQL WHERE keeps the rows whose truth value is `True`.
proof fn lemma_keep_true_is(rows: Seq<Row>, truths: Seq<Truth>, f: spec_fn(Row) -> bool)
    requires
        truths.len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] truths[i] is True) == f(rows[i]),
    ensures keep_true(rows, truths) == keep(rows, f),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let (ri, ti) = (rows.drop_last(), truths.drop_last());
        assert forall|i: int| 0 <= i < ri.len() implies (#[trigger] ti[i] is True) == f(ri[i]) by {
            assert(ti[i] == truths[i] && ri[i] == rows[i]);
        }
        lemma_keep_true_is(ri, ti, f);
        assert((truths[rows.len() - 1] is True) == f(rows[rows.len() - 1]));
    }
}

/// A WHERE whose condition is never an error on its input rows keeps the rows on which it is `True`.
pub proof fn lemma_filter(db: Database, src: Query, rows: Seq<Row>, pred: Pred)
    requires
        eval_query(db, Seq::empty(), src) == Ok::<Relation, SqlError>(rows),
        forall|q: int| 0 <= q < rows.len() ==> #[trigger] eval_pred(db, rows[q], pred) is Ok,
    ensures
        eval_query(db, Seq::empty(), Query::Filter { pred, input: Box::new(src) }) == Ok::<Relation, SqlError>(keep(rows, holds(db, pred))),
{
    let ctx = Seq::<Val>::empty();
    let truths = Seq::new(rows.len(), |i: int| eval_pred(db, rows[i], pred)->Ok_0);
    let prs = Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred));
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        assert(ctx + rows[i] =~= rows[i]);
    }
    lemma_collect_all(prs, truths);
    lemma_collect_pointwise::<Truth>();
    assert(collect(Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred))) == Ok::<Seq<Truth>, SqlError>(truths));
    assert forall|i: int| 0 <= i < rows.len() implies (#[trigger] truths[i] is True) == holds(db, pred)(rows[i]) by {}
    lemma_keep_true_is(rows, truths, holds(db, pred));
}

// ------------------------------------------------------------------------------------------------ the FROM tree

/// The WHERE node evaluates to `st4(nrows)`; every row of every stage has its shape.
#[verifier::spinoff_prover]
pub proof fn lemma_eval_where_node(db: Database, c: Ctx, ps: Seq<Literal>)
    requires db_ok(db, c), lits_ok(c, ps),
    ensures
        eval_query(db, Seq::empty(), q_where(ps)) == Ok::<Relation, SqlError>(st4(db, c, ps, nrows(c))),
        forall|q: int| 0 <= q < st4(db, c, ps, nrows(c)).len() ==> shape3(c, #[trigger] st4(db, c, ps, nrows(c))[q]),
{
    lemma_tables(db, c);
    let n = nrows(c);
    let e = Seq::<Val>::empty();
    // num x sub, then n.adsh = s.adsh.
    let r1 = product_rows(n, srows(c));
    assert(eval_query(db, e, Query::Table(1)) == Ok::<Relation, SqlError>(n));
    assert(eval_query(db, e, Query::Table(0)) == Ok::<Relation, SqlError>(srows(c)));
    assert(eval_query(db, e, Query::Table(2)) == Ok::<Relation, SqlError>(trows(c)));
    assert(eval_query(db, e, Query::Table(3)) == Ok::<Relation, SqlError>(prows(c)));
    assert(eval_query(db, e, Query::Product { left: Box::new(Query::Table(1)), right: Box::new(Query::Table(0)) })
        == Ok::<Relation, SqlError>(r1));
    assert forall|q: int| 0 <= q < n.len() implies exists|i: int| 0 <= i < c.n && #[trigger] n[q] == nrow(c, i) by {
        assert(n[q] == nrow(c, q));
    }
    lemma_shape1(c, n);
    assert forall|q: int| 0 <= q < r1.len() implies #[trigger] eval_pred(db, r1[q], p_ns()) is Ok by {
        assert(shape1(c, r1[q]));
        let (i, s) = choose|i: int, s: int| 0 <= i < c.n && 0 <= s < c.m && r1[q] == #[trigger] ns_row(c, i, s);
        lemma_eval_ns(db, c, i, s);
    }
    lemma_filter(db, Query::Product { left: Box::new(Query::Table(1)), right: Box::new(Query::Table(0)) }, r1, p_ns());
    let k1 = st1(db, c, n);
    lemma_kept::<()>(r1, holds(db, p_ns()), |x: Row| shape1(c, x));
    // x tag, then the tag condition.
    let r2 = product_rows(k1, trows(c));
    assert(eval_query(db, e, Query::Product { left: Box::new(q_ns()), right: Box::new(Query::Table(2)) }) == Ok::<Relation, SqlError>(r2));
    lemma_shape2(c, k1);
    assert forall|q: int| 0 <= q < r2.len() implies #[trigger] eval_pred(db, r2[q], p_nt()) is Ok by {
        assert(shape2(c, r2[q]));
        let (i, s, k) = choose|i: int, s: int, k: int| 0 <= i < c.n && 0 <= s < c.m && 0 <= k < c.nt && r2[q] == #[trigger] nst_row(c, i, s, k);
        lemma_eval_nt(db, c, i, s, k);
    }
    lemma_filter(db, Query::Product { left: Box::new(q_ns()), right: Box::new(Query::Table(2)) }, r2, p_nt());
    let k2 = st2(db, c, n);
    lemma_kept::<()>(r2, holds(db, p_nt()), |x: Row| shape2(c, x));
    // x pre, then the pre condition.
    let r3 = product_rows(k2, prows(c));
    assert(eval_query(db, e, Query::Product { left: Box::new(q_nst()), right: Box::new(Query::Table(3)) }) == Ok::<Relation, SqlError>(r3));
    lemma_shape3(c, k2);
    assert forall|q: int| 0 <= q < r3.len() implies #[trigger] eval_pred(db, r3[q], p_np()) is Ok by {
        assert(shape3(c, r3[q]));
        let (i, s, k, l) = choose|i: int, s: int, k: int, l: int| 0 <= i < c.n && 0 <= s < c.m && 0 <= k < c.nt && 0 <= l < c.npre
            && r3[q] == #[trigger] full_row(c, i, s, k, l);
        lemma_eval_np(db, c, i, s, k, l);
    }
    lemma_filter(db, Query::Product { left: Box::new(q_nst()), right: Box::new(Query::Table(3)) }, r3, p_np());
    let k3 = st3(db, c, n);
    lemma_kept::<()>(r3, holds(db, p_np()), |x: Row| shape3(c, x));
    // The WHERE.
    assert forall|q: int| 0 <= q < k3.len() implies #[trigger] eval_pred(db, k3[q], p_where(ps)) is Ok by {
        assert(shape3(c, k3[q]));
        let (i, s, k, l) = choose|i: int, s: int, k: int, l: int| 0 <= i < c.n && 0 <= s < c.m && 0 <= k < c.nt && 0 <= l < c.npre
            && k3[q] == #[trigger] full_row(c, i, s, k, l);
        lemma_eval_where(db, c, ps, i, s, k, l);
    }
    lemma_filter(db, q_nstp(), k3, p_where(ps));
    lemma_kept::<()>(k3, holds(db, p_where(ps)), |x: Row| shape3(c, x));
}

} // verus!
