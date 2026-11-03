//! L5 join rules over a product (engine toolkit; nothing here names a query, a table or a column).
//!
//! SQL writes an inner join as a condition over a product (`Filter(Product(l, r), p)`); the denotation evaluates
//! `p` on every pair, in left-major order, and returns the first error (hazard H1). A join plan skips pairs, so
//! every rule here needs the condition to be *total* on the pairs: it never errs (`ops::pred_keeps`). Then:
//! - conjunctions split (`lemma_and_keeps`): each conjunct is its own two-valued filter;
//! - an equality between a left and a right column is a hash join probing the right input with each left row
//!   (`lemma_equi_keeps`, `lemma_equi_join_rows`, `lemma_equi_join`; buckets by SQL equality `eq_bucket`, by
//!   structural equality for exact types `lemma_eq_bucket_exact`);
//! - a conjunct that reads one input only is pushed below the join and evaluated on that input's rows alone,
//!   rewritten through `left_map`/`right_map` (`lemma_left_keeps`, `lemma_right_keeps`, `lemma_push_conjuncts`);
//! - a reordered join tree: when the canonical rows are, as a bag, a view through a `ColMap` of the physical rows
//!   (`colmap`: swap for commutation, side by side for products, association needs no map), the canonical filter is
//!   the view of the physical filter by the rewritten condition (`lemma_filter_reordered`, `ctx_map`).
//!
//! Every condition named here is SQLSpec's own (`eval_pred`); the rewrites are `engine_link::remap`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::bridge::relation::{is_concat, lemma_product_rows_elems};
use crate::bridge::equality::{same_exact_type, lemma_val_not_distinct_structural};
use crate::link::join::{keep, left_of, right_of, shift, lemma_keep_ext, lemma_keep_all, lemma_keep_keep, lemma_keep_members, lemma_product_keep};
use crate::link::expr::lemma_expr_col;
use crate::engine_link::bag::{flat_by, lemma_flat_by_ext, lemma_bag_contains, lemma_keep_bag};
use crate::engine_link::ops::*;
use crate::engine_link::congruence::{join_block, lemma_keep_product};
use crate::engine_link::decorrelate::lemma_pred_and_keeps;
use crate::engine_link::locality::*;
use crate::engine_link::colmap::*;
use crate::engine_link::remap::*;

verus! {

// ------------------------------------------------------------------------------------- rows of a product

/// Row `k` of a product of left rows of width `wa`: its left part is a left row, its right part a right row.
pub proof fn lemma_product_row(a: Seq<Row>, b: Seq<Row>, wa: nat, k: int) -> (ij: (int, int))
    requires width_of(a, wa), 0 <= k < product_rows(a, b).len(),
    ensures
        0 <= ij.0 < a.len(),
        0 <= ij.1 < b.len(),
        product_rows(a, b)[k] == a[ij.0] + b[ij.1],
        left_of(product_rows(a, b)[k], wa) == a[ij.0],
        right_of(product_rows(a, b)[k], wa) == b[ij.1],
{
    lemma_product_rows_elems(a, b);
    let z = product_rows(a, b)[k];
    assert(is_concat(z, a, b));
    let (i, j) = choose|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && z == #[trigger] a[i] + #[trigger] b[j];
    assert(a[i].len() == wa);
    assert(left_of(z, wa) =~= a[i]);
    assert(right_of(z, wa) =~= b[j]);
    (i, j)
}

// ------------------------------------------------------------------------------------- conjunctions

/// Both conditions hold.
pub open spec fn both(f: spec_fn(Row) -> bool, h: spec_fn(Row) -> bool) -> spec_fn(Row) -> bool {
    |z: Row| f(z) && h(z)
}

/// A conjunction of two total conditions is total and keeps the rows both keep (strict AND is harmless when
/// neither side errs).
pub proof fn lemma_and_keeps(db: Database, ctx: Row, rows: Seq<Row>, p: Pred, q: Pred, f: spec_fn(Row) -> bool, h: spec_fn(Row) -> bool)
    requires pred_keeps(db, ctx, rows, p, f), pred_keeps(db, ctx, rows, q, h),
    ensures pred_keeps(db, ctx, rows, Pred::And(Box::new(p), Box::new(q)), both(f, h)),
{
    assert forall|i: int| 0 <= i < rows.len() implies {
        &&& #[trigger] eval_pred(db, ctx + rows[i], Pred::And(Box::new(p), Box::new(q))) is Ok
        &&& (eval_pred(db, ctx + rows[i], Pred::And(Box::new(p), Box::new(q)))->Ok_0 is True) == both(f, h)(rows[i])
    } by {
        assert(eval_pred(db, ctx + rows[i], p) is Ok && eval_pred(db, ctx + rows[i], q) is Ok);
        lemma_pred_and_keeps(db, ctx + rows[i], p, q);
    }
}

// ------------------------------------------------------------------------------------- equi conjuncts

/// SQL equality of two values: both non-NULL and equal in value (`compare` is `None` for NULL).
pub open spec fn key_eq(u: Val, v: Val) -> bool {
    compare(u, v) == Some(0int)
}

/// The condition `left column i = right column j` over a product of left rows of width `wa` (context of length
/// `c`).
pub open spec fn equi_pred(c: nat, wa: nat, i: nat, j: nat) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(c + i), b: Expr::Col(c + wa + j) }
}

/// The joined rows `equi_pred` keeps.
pub open spec fn equi_keeps(wa: nat, i: nat, j: nat) -> spec_fn(Row) -> bool {
    |z: Row| key_eq(z[i as int], z[(wa + j) as int])
}

/// The equality never errs on a pair: one key is NULL (`Unknown`), or both are of comparable families.
pub open spec fn keys_comparable(a: Seq<Row>, b: Seq<Row>, i: nat, j: nat) -> bool {
    forall|k: int, l: int| 0 <= k < a.len() && 0 <= l < b.len() ==>
        #[trigger] a[k][i as int] is Null || #[trigger] b[l][j as int] is Null || compare(a[k][i as int], b[l][j as int]) is Some
}

/// The rows whose column `j` is SQL-equal to `v` keep this.
pub open spec fn bucket_keeps(j: nat, v: Val) -> spec_fn(Row) -> bool {
    |y: Row| key_eq(v, y[j as int])
}

/// The rows of `b` whose column `j` is SQL-equal to `v`, in order (one hash bucket).
pub open spec fn eq_bucket(b: Seq<Row>, j: nat, v: Val) -> Seq<Row> {
    keep(b, bucket_keeps(j, v))
}

/// A left row joined to its bucket of right rows.
pub open spec fn equi_block(b: Seq<Row>, i: nat, j: nat) -> spec_fn(Row) -> Seq<Row> {
    |x: Row| eq_bucket(b, j, x[i as int]).map_values(|y: Row| x + y)
}

/// The equi-join of `a` (column `i`) and `b` (column `j`): left row by left row, its bucket (the order in which a
/// hash join probing the right input emits its rows).
pub open spec fn equi_join(a: Seq<Row>, b: Seq<Row>, i: nat, j: nat) -> Seq<Row> {
    flat_by(a, equi_block(b, i, j))
}

/// Every right row has column `j`.
pub open spec fn has_col(b: Seq<Row>, j: nat) -> bool {
    forall|l: int| 0 <= l < b.len() ==> j < (#[trigger] b[l]).len()
}

/// The equality conjunct is total on the product and keeps exactly the pairs with SQL-equal keys.
pub proof fn lemma_equi_keeps(db: Database, ctx: Row, a: Seq<Row>, b: Seq<Row>, wa: nat, i: nat, j: nat)
    requires width_of(a, wa), i < wa, has_col(b, j), keys_comparable(a, b, i, j),
    ensures pred_keeps(db, ctx, product_rows(a, b), equi_pred(ctx.len(), wa, i, j), equi_keeps(wa, i, j)),
{
    let p = product_rows(a, b);
    let pred = equi_pred(ctx.len(), wa, i, j);
    assert forall|k: int| 0 <= k < p.len() implies {
        &&& #[trigger] eval_pred(db, ctx + p[k], pred) is Ok
        &&& (eval_pred(db, ctx + p[k], pred)->Ok_0 is True) == equi_keeps(wa, i, j)(p[k])
    } by {
        let (ka, lb) = lemma_product_row(a, b, wa, k);
        let (x, y) = (a[ka], b[lb]);
        let env = ctx + p[k];
        assert(x.len() == wa && j < y.len());
        assert(env[(ctx.len() + i) as int] == x[i as int]);
        assert(env[(ctx.len() + wa + j) as int] == y[j as int]);
        assert(p[k][i as int] == x[i as int] && p[k][(wa + j) as int] == y[j as int]);
        lemma_expr_col(db, env, ctx.len() + i);
        lemma_expr_col(db, env, ctx.len() + wa + j);
        assert(x[i as int] is Null || y[j as int] is Null || compare(x[i as int], y[j as int]) is Some);
    }
}

/// The kept pairs of a product, as a hash join: left row by left row, its bucket.
pub proof fn lemma_equi_join_rows(a: Seq<Row>, b: Seq<Row>, wa: nat, i: nat, j: nat)
    requires width_of(a, wa), i < wa, has_col(b, j),
    ensures keep(product_rows(a, b), equi_keeps(wa, i, j)) == equi_join(a, b, i, j),
{
    let f = equi_keeps(wa, i, j);
    lemma_keep_product(a, b, f);
    assert forall|k: int| 0 <= k < a.len() implies #[trigger] join_block(b, f)(a[k]) == equi_block(b, i, j)(a[k]) by {
        let x = a[k];
        assert forall|l: int| 0 <= l < b.len() implies #[trigger] f(x + b[l]) == bucket_keeps(j, x[i as int])(b[l]) by {
            assert((x + b[l])[i as int] == x[i as int]);
            assert((x + b[l])[(wa + j) as int] == b[l][j as int]);
        }
        lemma_keep_ext(b, |y: Row| f(x + y), bucket_keeps(j, x[i as int]));
        let kept = eq_bucket(b, j, x[i as int]);
        assert(kept.map_values(|y: Row| x + y) =~= equi_block(b, i, j)(x));
    }
    lemma_flat_by_ext(a, join_block(b, f), equi_block(b, i, j));
}

/// L5, equi-join: a total equality between a left and a right column over the product is the hash join.
pub proof fn lemma_equi_join(db: Database, ctx: Row, a: Seq<Row>, b: Seq<Row>, wa: nat, i: nat, j: nat)
    requires width_of(a, wa), i < wa, has_col(b, j), keys_comparable(a, b, i, j),
    ensures filter_op(db, ctx, product_rows(a, b), equi_pred(ctx.len(), wa, i, j)) == Ok::<Relation, SqlError>(equi_join(a, b, i, j)),
{
    lemma_equi_keeps(db, ctx, a, b, wa, i, j);
    lemma_filter_keeps(db, ctx, product_rows(a, b), equi_pred(ctx.len(), wa, i, j), equi_keeps(wa, i, j));
    lemma_equi_join_rows(a, b, wa, i, j);
}

/// For a non-NULL probe value of the same exact type as every right key (for example int8 keys), the bucket is
/// the right rows whose key is that very value (a hash or array index on the stored value).
pub proof fn lemma_eq_bucket_exact(b: Seq<Row>, j: nat, v: Val)
    requires !(v is Null), forall|l: int| 0 <= l < b.len() ==> same_exact_type(v, #[trigger] b[l][j as int]),
    ensures eq_bucket(b, j, v) == keep(b, |y: Row| y[j as int] == v),
{
    assert forall|l: int| 0 <= l < b.len() implies #[trigger] bucket_keeps(j, v)(b[l]) == (b[l][j as int] == v) by {
        let w = b[l][j as int];
        lemma_val_not_distinct_structural(v, w);
        if w is Null {
            assert(compare(v, w) is None);
        }
    }
    lemma_keep_ext(b, bucket_keeps(j, v), |y: Row| y[j as int] == v);
}

// ------------------------------------------------------------------------------------- one-input conjuncts

/// The column map of a conjunct that reads the context and the left input only (context of length `c`, inputs
/// of widths `wa` and `wb`): it is evaluated on `ctx + left row` (the right input's positions are absent).
pub open spec fn left_map(c: nat, wa: nat, wb: nat) -> ColMap {
    Seq::new(c + wa + wb, |k: int| if k < c + wa { k as nat } else { (c + wa) as nat })
}

/// The column map of a conjunct that reads the context and the right input only: it is evaluated on
/// `ctx + right row` (the left input's positions are absent).
pub open spec fn right_map(c: nat, wa: nat, wb: nat) -> ColMap {
    Seq::new(c + wa + wb, |k: int| if k < c { k as nat } else if k < c + wa { (c + wb) as nat } else { (k - wa) as nat })
}

/// The joined environment against the left row's environment.
pub proof fn lemma_left_env(ctx: Row, x: Row, y: Row)
    ensures env_mapped(ctx + (x + y), ctx + x, left_map(ctx.len(), x.len(), y.len()), ctx.len() + x.len()),
{
    let (c, m, n) = (ctx.len(), left_map(ctx.len(), x.len(), y.len()), ctx.len() + x.len());
    let (canon, phys) = (ctx + (x + y), ctx + x);
    assert forall|i: int| 0 <= i < canon.len() && col_read_ok(i as nat, remap_reads(m, n))
        implies #[trigger] canon[i] == phys[remap_col(m, n, i as nat) as int] by {
        assert(m[i] < n);
        assert(i < c + x.len());
        assert(remap_col(m, n, i as nat) == i);
        if i >= c {
            assert((x + y)[i - c] == x[i - c]);
        }
    }
}

/// The joined environment against the right row's environment.
pub proof fn lemma_right_env(ctx: Row, x: Row, y: Row)
    ensures env_mapped(ctx + (x + y), ctx + y, right_map(ctx.len(), x.len(), y.len()), ctx.len() + y.len()),
{
    let (c, m, n) = (ctx.len(), right_map(ctx.len(), x.len(), y.len()), ctx.len() + y.len());
    let (canon, phys) = (ctx + (x + y), ctx + y);
    assert forall|i: int| 0 <= i < canon.len() && col_read_ok(i as nat, remap_reads(m, n))
        implies #[trigger] canon[i] == phys[remap_col(m, n, i as nat) as int] by {
        assert(m[i] < n);
        if i < c {
            assert(remap_col(m, n, i as nat) == i);
        } else {
            assert(i >= c + x.len());
            assert(remap_col(m, n, i as nat) == i - x.len());
            assert((x + y)[i - c] == y[i - c - x.len()]);
        }
    }
}

/// A condition `p` holds (is `True`) in `ctx + row`.
pub open spec fn side_keeps(db: Database, ctx: Row, p: Pred) -> spec_fn(Row) -> bool {
    |r: Row| eval_pred(db, ctx + r, p) == Ok::<Truth, SqlError>(Truth::True)
}

/// A condition on joined rows that is `f` of their left part.
pub open spec fn on_left(f: spec_fn(Row) -> bool, wa: nat) -> spec_fn(Row) -> bool {
    |z: Row| f(left_of(z, wa))
}

/// A condition on joined rows that is `f` of their right part.
pub open spec fn on_right(f: spec_fn(Row) -> bool, wa: nat) -> spec_fn(Row) -> bool {
    |z: Row| f(right_of(z, wa))
}

/// The left conjunct `p`, rewritten for the left rows alone.
pub open spec fn left_pred(p: Pred, c: nat, wa: nat, wb: nat) -> Pred {
    remap_pred(p, left_map(c, wa, wb), c + wa)
}

/// The right conjunct `q`, rewritten for the right rows alone.
pub open spec fn right_pred(q: Pred, c: nat, wa: nat, wb: nat) -> Pred {
    remap_pred(q, right_map(c, wa, wb), c + wb)
}

/// A conjunct `p` reads only the context and the left input, and its rewrite never errs on a left row.
pub open spec fn left_conjunct(db: Database, ctx: Row, a: Seq<Row>, p: Pred, wa: nat, wb: nat) -> bool {
    &&& pred_reads(p, remap_reads(left_map(ctx.len(), wa, wb), ctx.len() + wa))
    &&& forall|k: int| 0 <= k < a.len() ==> #[trigger] eval_pred(db, ctx + a[k], left_pred(p, ctx.len(), wa, wb)) is Ok
}

/// A conjunct `q` reads only the context and the right input, and its rewrite never errs on a right row.
pub open spec fn right_conjunct(db: Database, ctx: Row, b: Seq<Row>, q: Pred, wa: nat, wb: nat) -> bool {
    &&& pred_reads(q, remap_reads(right_map(ctx.len(), wa, wb), ctx.len() + wb))
    &&& forall|l: int| 0 <= l < b.len() ==> #[trigger] eval_pred(db, ctx + b[l], right_pred(q, ctx.len(), wa, wb)) is Ok
}

/// Pushdown, left: a left conjunct over the product is the left rows' own filter by its rewrite.
pub proof fn lemma_left_keeps(db: Database, ctx: Row, a: Seq<Row>, b: Seq<Row>, wa: nat, wb: nat, p: Pred)
    requires width_of(a, wa), width_of(b, wb), left_conjunct(db, ctx, a, p, wa, wb),
    ensures pred_keeps(db, ctx, product_rows(a, b), p, on_left(side_keeps(db, ctx, left_pred(p, ctx.len(), wa, wb)), wa)),
{
    let rows = product_rows(a, b);
    let pl = left_pred(p, ctx.len(), wa, wb);
    assert forall|k: int| 0 <= k < rows.len() implies {
        &&& #[trigger] eval_pred(db, ctx + rows[k], p) is Ok
        &&& (eval_pred(db, ctx + rows[k], p)->Ok_0 is True) == on_left(side_keeps(db, ctx, pl), wa)(rows[k])
    } by {
        let (ka, lb) = lemma_product_row(a, b, wa, k);
        let (x, y) = (a[ka], b[lb]);
        lemma_left_env(ctx, x, y);
        lemma_pred_remap(db, ctx + (x + y), ctx + x, p, left_map(ctx.len(), wa, wb), ctx.len() + wa);
        assert(eval_pred(db, ctx + x, pl) is Ok);
    }
}

/// Pushdown, right: a right conjunct over the product is the right rows' own filter by its rewrite.
pub proof fn lemma_right_keeps(db: Database, ctx: Row, a: Seq<Row>, b: Seq<Row>, wa: nat, wb: nat, q: Pred)
    requires width_of(a, wa), width_of(b, wb), right_conjunct(db, ctx, b, q, wa, wb),
    ensures pred_keeps(db, ctx, product_rows(a, b), q, on_right(side_keeps(db, ctx, right_pred(q, ctx.len(), wa, wb)), wa)),
{
    let rows = product_rows(a, b);
    let qr = right_pred(q, ctx.len(), wa, wb);
    assert forall|k: int| 0 <= k < rows.len() implies {
        &&& #[trigger] eval_pred(db, ctx + rows[k], q) is Ok
        &&& (eval_pred(db, ctx + rows[k], q)->Ok_0 is True) == on_right(side_keeps(db, ctx, qr), wa)(rows[k])
    } by {
        let (ka, lb) = lemma_product_row(a, b, wa, k);
        let (x, y) = (a[ka], b[lb]);
        lemma_right_env(ctx, x, y);
        lemma_pred_remap(db, ctx + (x + y), ctx + y, q, right_map(ctx.len(), wa, wb), ctx.len() + wb);
        assert(eval_pred(db, ctx + y, qr) is Ok);
    }
}

/// L5 pushdown: `WHERE p AND q` over a product, `p` reading the left input and `q` the right one (each total on its
/// input's rows), is the product of the two inputs filtered on their own.
pub proof fn lemma_push_conjuncts(db: Database, ctx: Row, a: Seq<Row>, b: Seq<Row>, wa: nat, wb: nat, p: Pred, q: Pred)
    requires width_of(a, wa), width_of(b, wb), left_conjunct(db, ctx, a, p, wa, wb), right_conjunct(db, ctx, b, q, wa, wb),
    ensures
        filter_op(db, ctx, product_rows(a, b), Pred::And(Box::new(p), Box::new(q))) == Ok::<Relation, SqlError>(product_rows(
            keep(a, side_keeps(db, ctx, left_pred(p, ctx.len(), wa, wb))),
            keep(b, side_keeps(db, ctx, right_pred(q, ctx.len(), wa, wb))),
        )),
{
    let rows = product_rows(a, b);
    let (fl, fr) = (side_keeps(db, ctx, left_pred(p, ctx.len(), wa, wb)), side_keeps(db, ctx, right_pred(q, ctx.len(), wa, wb)));
    lemma_left_keeps(db, ctx, a, b, wa, wb, p);
    lemma_right_keeps(db, ctx, a, b, wa, wb, q);
    lemma_and_keeps(db, ctx, rows, p, q, on_left(fl, wa), on_right(fr, wa));
    let f = both(on_left(fl, wa), on_right(fr, wa));
    lemma_filter_keeps(db, ctx, rows, Pred::And(Box::new(p), Box::new(q)), f);
    lemma_product_keep(a, b, fl, fr, wa);
    lemma_keep_ext(rows, |x: Row| fl(left_of(x, wa)) && fr(right_of(x, wa)), f);
}

/// L5, hash join with a pushed-down right filter: `WHERE left.i = right.j AND q`, `q` a right conjunct, is the
/// equi-join of the left rows with the right rows filtered on their own (the probe side filtered before the join).
pub proof fn lemma_equi_join_right_filter(db: Database, ctx: Row, a: Seq<Row>, b: Seq<Row>, wa: nat, wb: nat, i: nat, j: nat, q: Pred)
    requires
        width_of(a, wa), width_of(b, wb), i < wa, j < wb,
        keys_comparable(a, b, i, j),
        right_conjunct(db, ctx, b, q, wa, wb),
    ensures
        filter_op(db, ctx, product_rows(a, b), Pred::And(Box::new(equi_pred(ctx.len(), wa, i, j)), Box::new(q)))
            == Ok::<Relation, SqlError>(equi_join(a, keep(b, side_keeps(db, ctx, right_pred(q, ctx.len(), wa, wb))), i, j)),
{
    let rows = product_rows(a, b);
    let fr = side_keeps(db, ctx, right_pred(q, ctx.len(), wa, wb));
    let (fe, fq) = (equi_keeps(wa, i, j), on_right(fr, wa));
    let kb = keep(b, fr);
    assert(has_col(b, j));
    lemma_equi_keeps(db, ctx, a, b, wa, i, j);
    lemma_right_keeps(db, ctx, a, b, wa, wb, q);
    lemma_and_keeps(db, ctx, rows, equi_pred(ctx.len(), wa, i, j), q, fe, fq);
    lemma_filter_keeps(db, ctx, rows, Pred::And(Box::new(equi_pred(ctx.len(), wa, i, j)), Box::new(q)), both(fe, fq));
    // keep(rows, fe && fq) = keep(keep(rows, fq), fe) = keep(product(a, keep(b, fr)), fe)
    lemma_keep_keep(rows, fq, fe);
    lemma_keep_ext(rows, |z: Row| fq(z) && fe(z), both(fe, fq));
    lemma_keep_all(a, |x: Row| true);
    lemma_product_keep(a, b, |x: Row| true, fr, wa);
    lemma_keep_ext(rows, |x: Row| (|x: Row| true)(left_of(x, wa)) && fr(right_of(x, wa)), fq);
    // the right rows kept still have column j
    assert(has_col(kb, j)) by {
        lemma_keep_members(b, fr);
        assert forall|l: int| 0 <= l < kb.len() implies j < (#[trigger] kb[l]).len() by {
            assert(b.contains(kb[l]));
        }
    }
    lemma_equi_join_rows(a, kb, wa, i, j);
}

// ------------------------------------------------------------------------------------- reordered inputs

/// The environment view of a column map: the context unchanged, the row through `m`.
pub open spec fn ctx_map(c: nat, m: ColMap) -> ColMap {
    id_map(c) + shift(m, c)
}

/// The canonical environment `ctx + map_row(m, y)` against the physical one `ctx + y`; every position is mapped.
pub proof fn lemma_ctx_env(ctx: Row, m: ColMap, y: Row)
    requires map_into(m, y.len()),
    ensures
        env_mapped(ctx + map_row(m, y), ctx + y, ctx_map(ctx.len(), m), ctx.len() + y.len()),
        reads_all(remap_reads(ctx_map(ctx.len(), m), ctx.len() + y.len())),
{
    let (c, mm, n) = (ctx.len(), ctx_map(ctx.len(), m), ctx.len() + y.len());
    let (canon, phys) = (ctx + map_row(m, y), ctx + y);
    assert forall|i: int| 0 <= i < mm.len() implies #[trigger] mm[i] < n by {
        if i >= c {
            assert(mm[i] == m[i - c] + c);
        }
    }
    assert forall|i: int| 0 <= i < canon.len() && col_read_ok(i as nat, remap_reads(mm, n))
        implies #[trigger] canon[i] == phys[remap_col(mm, n, i as nat) as int] by {
        if i >= c {
            assert(mm[i] == m[i - c] + c);
            assert(canon[i] == y[m[i - c] as int]);
        }
    }
    assert forall|i: nat| #[trigger] col_read_ok(i, remap_reads(mm, n)) by {
        if i < mm.len() {
            assert(mm[i as int] < n);
        }
    }
}

/// L5 reordering: canonical rows `s` that are, as a bag, the view through `m` of physical rows `ys` (width `w`),
/// filtered by `p`, are, as a bag, the view of `ys` filtered by `p` rewritten through `ctx_map` (when the rewrite
/// never errs on a physical row). With `colmap::lemma_product_swap` this is join commutation; with
/// `lemma_product_map` and `link::join::lemma_product_assoc`, any reordering of a join tree.
pub proof fn lemma_filter_reordered(db: Database, ctx: Row, s: Seq<Row>, ys: Seq<Row>, m: ColMap, w: nat, p: Pred)
    requires
        s.to_multiset() == map_rows(m, ys).to_multiset(),
        width_of(ys, w),
        map_into(m, w),
        forall|k: int| 0 <= k < ys.len() ==> #[trigger] eval_pred(db, ctx + ys[k], remap_pred(p, ctx_map(ctx.len(), m), ctx.len() + w)) is Ok,
    ensures
        filter_op(db, ctx, s, p) is Ok,
        filter_op(db, ctx, s, p)->Ok_0.to_multiset()
            == map_rows(m, keep(ys, side_keeps(db, ctx, remap_pred(p, ctx_map(ctx.len(), m), ctx.len() + w)))).to_multiset(),
{
    let pm = remap_pred(p, ctx_map(ctx.len(), m), ctx.len() + w);
    let g = side_keeps(db, ctx, p);
    let canon = map_rows(m, ys);
    // `p` on a canonical row is the rewrite on the physical row it views
    assert forall|k: int| 0 <= k < ys.len() implies #[trigger] eval_pred(db, ctx + canon[k], p) == eval_pred(db, ctx + ys[k], pm) by {
        lemma_ctx_env(ctx, m, ys[k]);
        lemma_pred_reads_all(p, remap_reads(ctx_map(ctx.len(), m), ctx.len() + w));
        lemma_pred_remap(db, ctx + map_row(m, ys[k]), ctx + ys[k], p, ctx_map(ctx.len(), m), ctx.len() + w);
    }
    assert(pred_keeps(db, ctx, s, p, g)) by {
        assert forall|i: int| 0 <= i < s.len() implies {
            &&& #[trigger] eval_pred(db, ctx + s[i], p) is Ok
            &&& (eval_pred(db, ctx + s[i], p)->Ok_0 is True) == g(s[i])
        } by {
            let k = lemma_bag_contains(canon, s, i);
            assert(eval_pred(db, ctx + canon[k], p) == eval_pred(db, ctx + ys[k], pm));
        }
    }
    lemma_filter_keeps(db, ctx, s, p, g);
    lemma_keep_bag(s, canon, g);
    lemma_keep_through_map(m, ys, g);
    assert forall|k: int| 0 <= k < ys.len() implies #[trigger] g(map_row(m, ys[k])) == side_keeps(db, ctx, pm)(ys[k]) by {
        assert(canon[k] == map_row(m, ys[k]));
    }
    lemma_keep_ext(ys, |y: Row| g(map_row(m, y)), side_keeps(db, ctx, pm));
}

} // verus!
