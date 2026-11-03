//! GROUP BY link for `SUM` of int4 arguments (for example `SUM(CASE WHEN .. THEN 1 ELSE 0 END)`): the
//! `link::query::QuerySpec` normal form with integer argument values (`iargs`), whose group output is the exact sum
//! as an int8 (`ifull_row`); when some group's sum leaves int8 the GROUP BY is error 22003 (`lemma_igroup_err`).
//!
//! `link::query::lemma_group_query` covers COUNT(*) and numeric SUM/AVG only; this module adds the int4 SUM with the
//! same premises (per-row agreement of the condition, keys and arguments; exact keys) and the same proof plan:
//! the qualifying keys' `distinct_rows` is `gkeys`, each group's members are the argument rows of its qualifying
//! rows (`imembers`), and each SUM over its members is `int_result(int8, gsum)`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::int::*;
use crate::spec::scalar::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::equality::*;
use crate::link::query::*;
use crate::bridge::collect::{lemma_collect_all, lemma_collect_first_err};
use crate::exec::relational::domain::lemma_collect_pointwise;

verus! {

/// Integer argument values of a projected row: aggregate `j`'s argument is the integer `(g.arg)(j, x)`.
pub open spec fn iargs(g: QuerySpec, x: Row) -> Row {
    Seq::new(g.aggs.len(), |j: int| Val::Int((g.arg)(j, x)))
}

/// Every aggregate is a SUM of an int4 argument.
pub open spec fn iaggs_match(aggs: Seq<Agg>, g: QuerySpec) -> bool {
    &&& aggs.len() == g.aggs.len()
    &&& forall|j: int| 0 <= j < aggs.len() ==> (#[trigger] aggs[j]) is Sum && aggs[j]->Sum_kind == NumKind::Int4
}

/// Per-row agreement of the aggregate arguments with `iargs`, on qualifying rows.
pub open spec fn iargs_agree(db: Database, rows: Seq<Row>, cols: Seq<nat>, aggs: Seq<Agg>, g: QuerySpec) -> bool {
    forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], cols)) ==>
        agg_args(db, rows[i], aggs) == Ok::<Row, SqlError>(iargs(g, proj(rows[i], cols)))
}

/// Every group sum lies in int8.
pub open spec fn isum_caps(g: QuerySpec, xs: Seq<Row>) -> bool {
    forall|k: Row, j: int| 0 <= j < g.aggs.len() ==> int_in_range(IntKind::Int8, #[trigger] gsum(g, xs, k, j))
}

/// The SUM values of group `k`.
pub open spec fn isum_outs(g: QuerySpec, xs: Seq<Row>, k: Row) -> Row {
    Seq::new(g.aggs.len(), |j: int| Val::Int(gsum(g, xs, k, j)))
}

/// `key ++ sums` of group `k` (the GROUP BY operator's row).
pub open spec fn ifull_row(g: QuerySpec, xs: Seq<Row>, k: Row) -> Row {
    k + isum_outs(g, xs, k)
}

/// Integer argument rows of the qualifying rows of group `k`, in order.
pub open spec fn imembers(g: QuerySpec, xs: Seq<Row>, k: Row) -> Seq<Row>
    decreases xs.len(),
{
    if xs.len() == 0 {
        Seq::empty()
    } else if hit(g, xs.last(), k) {
        imembers(g, xs.drop_last(), k).push(iargs(g, xs.last()))
    } else {
        imembers(g, xs.drop_last(), k)
    }
}

/// Per kept row: its key tuple and integer arguments (the GROUP BY's prepared sequence).
pub proof fn lemma_iprepared(db: Database, rows: Seq<Row>, kept: Seq<Row>, cols: Seq<nat>, keys: Seq<Expr>, aggs: Seq<Agg>,
    g: QuerySpec)
    requires
        keys_agree(db, rows, cols, keys, g),
        iargs_agree(db, rows, cols, aggs, g),
        forall|i: int| 0 <= i < kept.len() ==> rows.contains(#[trigger] kept[i]) && (g.qual)(proj(kept[i], cols)),
    ensures
        collect(Seq::new(kept.len(), |i: int|
            match eval_exprs(db, Seq::<Val>::empty() + kept[i], keys) {
                Err(err) => Err(err),
                Ok(k) => match agg_args(db, Seq::<Val>::empty() + kept[i], aggs) {
                    Err(err) => Err(err),
                    Ok(a) => Ok((k, a)),
                },
            }))
            == Ok::<Seq<(Row, Row)>, SqlError>(Seq::new(kept.len(), |i: int| ((g.key)(proj(kept[i], cols)), iargs(g, proj(kept[i], cols))))),
{
    hide(eval_exprs);
    hide(agg_args);
    let ctx = Seq::<Val>::empty();
    let prep = Seq::new(kept.len(), |i: int| ((g.key)(proj(kept[i], cols)), iargs(g, proj(kept[i], cols))));
    let pre = Seq::new(kept.len(), |i: int|
        match eval_exprs(db, ctx + kept[i], keys) {
            Err(err) => Err(err),
            Ok(k) => match agg_args(db, ctx + kept[i], aggs) {
                Err(err) => Err(err),
                Ok(a) => Ok((k, a)),
            },
        });
    assert forall|i: int| 0 <= i < pre.len() implies #[trigger] pre[i] == Ok::<(Row, Row), SqlError>(prep[i]) by {
        assert(ctx + kept[i] =~= kept[i]);
        assert(rows.contains(kept[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
        assert((g.qual)(proj(rows[m], cols)));
        assert(eval_exprs(db, rows[m], keys) == Ok::<Row, SqlError>((g.key)(proj(rows[m], cols))));
        assert(agg_args(db, rows[m], aggs) == Ok::<Row, SqlError>(iargs(g, proj(rows[m], cols))));
    }
    lemma_collect_all(pre, prep);
}

/// `group_members` of the prepared (key, args) sequences is `imembers` (exact keys, `k` from the pool).
pub proof fn lemma_igroup_members(g: QuerySpec, xs: Seq<Row>, k: Row, pool: Seq<Row>)
    requires
        forall|a: Row, b: Row| pool.contains(a) && pool.contains(b) ==> (#[trigger] row_not_distinct(a, b) <==> a == b),
        forall|i: int| 0 <= i < qkeys(g, xs).len() ==> pool.contains(#[trigger] qkeys(g, xs)[i]),
        pool.contains(k),
    ensures
        group_members(qkeys(g, xs), qrows(g, xs).map_values(|x: Row| iargs(g, x)), k) == imembers(g, xs, k),
    decreases xs.len(),
{
    let args = |x: Row| iargs(g, x);
    if xs.len() > 0 {
        let xi = xs.drop_last();
        let x = xs.last();
        let qk = qkeys(g, xs);
        let qki = qkeys(g, xi);
        let qa = qrows(g, xs).map_values(args);
        let qai = qrows(g, xi).map_values(args);
        if (g.qual)(x) {
            assert(qk =~= qki.push((g.key)(x)));
            assert(qa =~= qai.push(iargs(g, x)));
            assert forall|i: int| 0 <= i < qki.len() implies pool.contains(#[trigger] qki[i]) by {
                assert(qk[i] == qki[i]);
            }
            lemma_igroup_members(g, xi, k, pool);
            assert(qk.drop_last() =~= qki);
            assert(qa.drop_last() =~= qai);
            assert(pool.contains(qk[qk.len() - 1]));
            assert(row_not_distinct((g.key)(x), k) <==> (g.key)(x) == k);
        } else {
            assert(qk =~= qki);
            assert(qa =~= qai);
            lemma_igroup_members(g, xi, k, pool);
        }
    } else {
        assert(qkeys(g, xs) =~= Seq::<Row>::empty());
    }
}

/// Column `j` of a group's members: `gcount` integers summing to `gsum`.
pub proof fn lemma_imembers_col(g: QuerySpec, xs: Seq<Row>, k: Row, j: int)
    requires 0 <= j < g.aggs.len(),
    ensures ({
        let vs = column(imembers(g, xs, k), j);
        &&& vs.len() == gcount(g, xs, k)
        &&& all_of_kind(NumKind::Int4, vs)
        &&& count_non_null(vs) == gcount(g, xs, k)
        &&& int_sum(vs) == gsum(g, xs, k, j)
    }),
    decreases xs.len(),
{
    let vs = column(imembers(g, xs, k), j);
    if xs.len() > 0 {
        let xi = xs.drop_last();
        let x = xs.last();
        lemma_imembers_col(g, xi, k, j);
        let vsi = column(imembers(g, xi, k), j);
        if hit(g, x, k) {
            assert(vs =~= vsi.push(iargs(g, x)[j]));
            assert(vs.drop_last() =~= vsi);
        } else {
            assert(vs =~= vsi);
        }
    } else {
        assert(vs =~= Seq::<Val>::empty());
    }
}

/// SUM `j` of a non-empty group: `int_result(int8, gsum)`.
pub proof fn lemma_isum_value(g: QuerySpec, aggs: Seq<Agg>, xs: Seq<Row>, k: Row, j: int)
    requires
        iaggs_match(aggs, g),
        0 <= j < g.aggs.len(),
        gcount(g, xs, k) > 0,
    ensures agg_value(aggs[j], column(imembers(g, xs, k), j)) == int_result(IntKind::Int8, gsum(g, xs, k, j)),
{
    lemma_imembers_col(g, xs, k, j);
    assert(aggs[j] is Sum && aggs[j]->Sum_kind == NumKind::Int4);
}

/// The aggregate row of a non-empty group whose sums all fit int8.
pub proof fn lemma_iagg_row(g: QuerySpec, aggs: Seq<Agg>, xs: Seq<Row>, k: Row)
    requires
        iaggs_match(aggs, g),
        gcount(g, xs, k) > 0,
        forall|j: int| 0 <= j < g.aggs.len() ==> int_in_range(IntKind::Int8, #[trigger] gsum(g, xs, k, j)),
    ensures agg_row(aggs, imembers(g, xs, k)) == Ok::<Row, SqlError>(isum_outs(g, xs, k)),
{
    let m = imembers(g, xs, k);
    let rs = Seq::new(aggs.len(), |j: int| agg_value(aggs[j], column(m, j)));
    let outs = isum_outs(g, xs, k);
    assert forall|j: int| 0 <= j < rs.len() implies #[trigger] rs[j] == Ok::<Val, SqlError>(outs[j]) by {
        lemma_isum_value(g, aggs, xs, k, j);
    }
    lemma_collect_all(rs, outs);
}

/// The aggregate row of a non-empty group is its sums or error 22003.
pub proof fn lemma_iagg_row_or_err(g: QuerySpec, aggs: Seq<Agg>, xs: Seq<Row>, k: Row)
    requires
        iaggs_match(aggs, g),
        gcount(g, xs, k) > 0,
    ensures
        agg_row(aggs, imembers(g, xs, k)) is Ok
            || agg_row(aggs, imembers(g, xs, k)) == Err::<Row, SqlError>(SqlError::NumericValueOutOfRange),
        (exists|j: int| 0 <= j < g.aggs.len() && !int_in_range(IntKind::Int8, #[trigger] gsum(g, xs, k, j)))
            ==> agg_row(aggs, imembers(g, xs, k)) == Err::<Row, SqlError>(SqlError::NumericValueOutOfRange),
{
    let m = imembers(g, xs, k);
    let rs = Seq::new(aggs.len(), |j: int| agg_value(aggs[j], column(m, j)));
    assert forall|j: int| 0 <= j < rs.len() implies #[trigger] rs[j] is Ok
        || rs[j] == Err::<Val, SqlError>(SqlError::NumericValueOutOfRange) by {
        lemma_isum_value(g, aggs, xs, k, j);
    }
    if exists|j: int| 0 <= j < rs.len() && #[trigger] rs[j] is Err {
        let j0 = choose|j: int| 0 <= j < rs.len() && #[trigger] rs[j] is Err;
        crate::link::capacity::lemma_collect_uniform_err(rs, SqlError::NumericValueOutOfRange, j0);
    } else {
        crate::bridge::collect::lemma_collect_ok(rs);
    }
    if exists|j: int| 0 <= j < g.aggs.len() && !int_in_range(IntKind::Int8, #[trigger] gsum(g, xs, k, j)) {
        let j1 = choose|j: int| 0 <= j < g.aggs.len() && !int_in_range(IntKind::Int8, #[trigger] gsum(g, xs, k, j));
        lemma_isum_value(g, aggs, xs, k, j1);
        crate::link::capacity::lemma_collect_uniform_err(rs, SqlError::NumericValueOutOfRange, j1);
    }
}

/// GROUP BY over the qualifying rows' (key, integer arguments): `key ++ sums` of every group, first-occurrence order.
pub proof fn lemma_igroups(g: QuerySpec, aggs: Seq<Agg>, xs: Seq<Row>)
    requires
        iaggs_match(aggs, g),
        keys_exact(g, xs),
        isum_caps(g, xs),
    ensures
        group_rows(aggs, qkeys(g, xs), qrows(g, xs).map_values(|x: Row| iargs(g, x)))
            == Ok::<Seq<Row>, SqlError>(gkeys(g, xs).map_values(|k: Row| ifull_row(g, xs, k))),
{
    let ks = qkeys(g, xs);
    let avs = qrows(g, xs).map_values(|x: Row| iargs(g, x));
    let pool = key_pool(g, xs);
    lemma_pool_exact(g, xs);
    assert forall|i: int| 0 <= i < qkeys(g, xs).len() implies pool.contains(#[trigger] qkeys(g, xs)[i]) by {
        assert(pool[i] == qkeys(g, xs)[i]);
    }
    lemma_distinct_gkeys(g, xs, pool);
    let ds = gkeys(g, xs);
    lemma_gkeys(g, xs);
    let grs = Seq::new(ds.len(), |gi: int|
        match agg_row(aggs, group_members(ks, avs, ds[gi])) {
            Ok(a) => Ok(ds[gi] + a),
            Err(e) => Err(e),
        });
    let full = ds.map_values(|k: Row| ifull_row(g, xs, k));
    assert forall|gi: int| 0 <= gi < grs.len() implies #[trigger] grs[gi] == Ok::<Row, SqlError>(full[gi]) by {
        let k = ds[gi];
        assert(pool.contains(k));
        lemma_igroup_members(g, xs, k, pool);
        assert(ds.contains(k));
        lemma_gkeys_witness(g, xs, k);
        let w = choose|w: int| 0 <= w < xs.len() && #[trigger] hit(g, xs[w], k);
        lemma_count_pos(g, xs, k, w);
        lemma_iagg_row(g, aggs, xs, k);
    }
    lemma_collect_all(grs, full);
}

/// A qualifying row of group `k` makes its count positive.
pub proof fn lemma_count_pos(g: QuerySpec, xs: Seq<Row>, k: Row, w: int)
    requires 0 <= w < xs.len(), hit(g, xs[w], k),
    ensures gcount(g, xs, k) > 0,
    decreases xs.len(),
{
    let xi = xs.drop_last();
    if w < xs.len() - 1 {
        assert(xi[w] == xs[w]);
        lemma_count_pos(g, xi, k, w);
    }
}

/// GROUP BY where some non-empty group `k0` has a sum outside int8: error 22003 (every group's sums are either
/// exact or that error).
pub proof fn lemma_igroups_err(g: QuerySpec, aggs: Seq<Agg>, xs: Seq<Row>, k0: Row, j0: int)
    requires
        iaggs_match(aggs, g),
        keys_exact(g, xs),
        gcount(g, xs, k0) > 0,
        0 <= j0 < g.aggs.len(),
        !int_in_range(IntKind::Int8, gsum(g, xs, k0, j0)),
    ensures
        group_rows(aggs, qkeys(g, xs), qrows(g, xs).map_values(|x: Row| iargs(g, x)))
            == Err::<Seq<Row>, SqlError>(SqlError::NumericValueOutOfRange),
{
    let e = SqlError::NumericValueOutOfRange;
    let ks = qkeys(g, xs);
    let avs = qrows(g, xs).map_values(|x: Row| iargs(g, x));
    let pool = key_pool(g, xs);
    lemma_pool_exact(g, xs);
    assert forall|i: int| 0 <= i < qkeys(g, xs).len() implies pool.contains(#[trigger] qkeys(g, xs)[i]) by {
        assert(pool[i] == qkeys(g, xs)[i]);
    }
    lemma_distinct_gkeys(g, xs, pool);
    let ds = gkeys(g, xs);
    lemma_gkeys(g, xs);
    let grs = Seq::new(ds.len(), |gi: int|
        match agg_row(aggs, group_members(ks, avs, ds[gi])) {
            Ok(a) => Ok(ds[gi] + a),
            Err(err) => Err(err),
        });
    assert forall|gi: int| 0 <= gi < grs.len() implies #[trigger] grs[gi] is Ok || grs[gi] == Err::<Row, SqlError>(e) by {
        let k = ds[gi];
        assert(pool.contains(k));
        lemma_igroup_members(g, xs, k, pool);
        assert(ds.contains(k));
        lemma_gkeys_witness(g, xs, k);
        let w = choose|w: int| 0 <= w < xs.len() && #[trigger] hit(g, xs[w], k);
        lemma_count_pos(g, xs, k, w);
        lemma_iagg_row_or_err(g, aggs, xs, k);
    }
    lemma_count_witness(g, xs, k0);
    let w0 = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], k0);
    assert(ds.contains(k0));
    let g0 = choose|gi: int| 0 <= gi < ds.len() && ds[gi] == k0;
    assert(grs[g0] == Err::<Row, SqlError>(e)) by {
        assert(pool.contains(k0));
        lemma_igroup_members(g, xs, k0, pool);
        lemma_iagg_row_or_err(g, aggs, xs, k0);
    }
    crate::link::capacity::lemma_collect_uniform_err(grs, e, g0);
}

/// The body is the GROUP BY of the qualifying rows' (key, integer arguments) sequence.
pub proof fn lemma_igroup_unfold(db: Database, rows: Seq<Row>, cols: Seq<nat>, input: Query, keys: Seq<Expr>,
    aggs: Seq<Agg>, g: QuerySpec)
    requires
        eval_query(db, Seq::empty(), input) == Ok::<Relation, SqlError>(keep_true(rows, qual_truths(g, proj_all(rows, cols)))),
        keys_agree(db, rows, cols, keys, g),
        iargs_agree(db, rows, cols, aggs, g),
    ensures ({
        let xs = proj_all(rows, cols);
        eval_query(db, Seq::empty(), Query::GroupBy { keys, aggs, input: Box::new(input) })
            == group_rows(aggs, qkeys(g, xs), qrows(g, xs).map_values(|x: Row| iargs(g, x)))
    }),
{
    hide(eval_pred);
    hide(eval_exprs);
    hide(agg_args);
    hide(group_rows);
    let xs = proj_all(rows, cols);
    let kept = keep_true(rows, qual_truths(g, xs));
    let q = qrows(g, xs);
    lemma_kept_rows(g, rows, cols);
    lemma_iprepared(db, rows, kept, cols, keys, aggs, g);
    let prep = Seq::new(kept.len(), |i: int| ((g.key)(proj(kept[i], cols)), iargs(g, proj(kept[i], cols))));
    assert(prep.map_values(|p: (Row, Row)| p.0) =~= qkeys(g, xs));
    assert(prep.map_values(|p: (Row, Row)| p.1) =~= q.map_values(|x: Row| iargs(g, x)));
    lemma_groupby_unfold(db, input, keys, aggs, kept, prep);
}

/// The grouped link for int4 SUMs: under per-row agreement, exact keys and int8 group sums, a GROUP BY over an
/// input that evaluates to the qualifying rows of `rows` is `key ++ sums` of every group, first-occurrence order.
pub proof fn lemma_igroup_query(db: Database, rows: Seq<Row>, cols: Seq<nat>, input: Query, keys: Seq<Expr>,
    aggs: Seq<Agg>, g: QuerySpec)
    requires
        eval_query(db, Seq::empty(), input) == Ok::<Relation, SqlError>(keep_true(rows, qual_truths(g, proj_all(rows, cols)))),
        keys_agree(db, rows, cols, keys, g),
        iargs_agree(db, rows, cols, aggs, g),
        iaggs_match(aggs, g),
        keys_exact(g, proj_all(rows, cols)),
        isum_caps(g, proj_all(rows, cols)),
    ensures ({
        let xs = proj_all(rows, cols);
        eval_query(db, Seq::empty(), Query::GroupBy { keys, aggs, input: Box::new(input) })
            == Ok::<Relation, SqlError>(gkeys(g, xs).map_values(|k: Row| ifull_row(g, xs, k)))
    }),
{
    lemma_igroup_unfold(db, rows, cols, input, keys, aggs, g);
    lemma_igroups(g, aggs, proj_all(rows, cols));
}

/// The grouped link when some non-empty group's sum leaves int8: the GROUP BY is error 22003.
pub proof fn lemma_igroup_err(db: Database, rows: Seq<Row>, cols: Seq<nat>, input: Query, keys: Seq<Expr>,
    aggs: Seq<Agg>, g: QuerySpec, k0: Row, j0: int)
    requires
        eval_query(db, Seq::empty(), input) == Ok::<Relation, SqlError>(keep_true(rows, qual_truths(g, proj_all(rows, cols)))),
        keys_agree(db, rows, cols, keys, g),
        iargs_agree(db, rows, cols, aggs, g),
        iaggs_match(aggs, g),
        keys_exact(g, proj_all(rows, cols)),
        gcount(g, proj_all(rows, cols), k0) > 0,
        0 <= j0 < g.aggs.len(),
        !int_in_range(IntKind::Int8, gsum(g, proj_all(rows, cols), k0, j0)),
    ensures
        eval_query(db, Seq::empty(), Query::GroupBy { keys, aggs, input: Box::new(input) })
            == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange),
{
    lemma_igroup_unfold(db, rows, cols, input, keys, aggs, g);
    lemma_igroups_err(g, aggs, proj_all(rows, cols), k0, j0);
}

} // verus!
