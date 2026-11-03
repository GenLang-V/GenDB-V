//! GROUP BY with integer `SUM(<int4 expression>)` aggregates over the accumulator normal form of `link::query`:
//! links the VERUS_SQL denotation of a `GroupBy` node to `gkeys` / `gsum` when every per-row argument is an int4
//! value (for example a `CASE .. THEN 1 ELSE 0 END` indicator), and states the SQL error of a sum beyond int8.
//!
//! `link::query::lemma_group_query` covers numeric SUM/AVG and COUNT(*); a SUM over int4 arguments differs in its
//! argument values (`Val::Int`, `int_args`), its result (`int_result(Int8, int_sum)`: an int8 value or the error 22003)
//! and its output row (`int_full_row`: the key, then each group's exact `gsum` as an int8 value). The normal form's
//! `aggs` kinds are not read here (only `g.aggs.len()` and `g.arg`). Proof structure as in `link::query`: on exact keys
//! the denotation's groups are `gkeys`, each group's members are the int argument rows of its qualifying rows
//! (`int_members`), and every member column is a sequence of int4 values whose `int_sum` is the group's `gsum`.
use vstd::prelude::*;
use crate::spec::limits::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::order::*;
use crate::spec::equality::*;
use crate::bridge::collect::lemma_collect_all;
use crate::exec::relational::domain::{lemma_collect_pointwise, lemma_group_input_unfold};
use crate::link::query::*;
use crate::link::capacity::lemma_group_by_err;

verus! {

/// Argument values of one projected row: aggregate `j`'s argument is the int4 value `g.arg(j, x)`.
pub open spec fn int_args(g: QuerySpec, x: Row) -> Row {
    Seq::new(g.aggs.len(), |j: int| Val::Int((g.arg)(j, x)))
}

/// Per-row agreement of the aggregate arguments with the normal form, on qualifying rows.
pub open spec fn int_args_agree(db: Database, rows: Seq<Row>, cols: Seq<nat>, aggs: Seq<Agg>, g: QuerySpec) -> bool {
    forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], cols)) ==>
        agg_args(db, rows[i], aggs) == Ok::<Row, SqlError>(int_args(g, proj(rows[i], cols)))
}

/// Every aggregate is a SUM over int4 arguments, one per normal-form aggregate.
pub open spec fn int4_sums(aggs: Seq<Agg>, g: QuerySpec) -> bool {
    &&& aggs.len() == g.aggs.len()
    &&& forall|j: int| 0 <= j < aggs.len() ==> (#[trigger] aggs[j]) is Sum && aggs[j]->Sum_kind == NumKind::Int4
}

/// Every group's sums are int8 values.
pub open spec fn int_caps(g: QuerySpec, xs: Seq<Row>) -> bool {
    forall|k: Row, j: int| 0 <= j < g.aggs.len() ==> int_in_range(IntKind::Int8, #[trigger] gsum(g, xs, k, j))
}

/// The int argument rows of the qualifying rows of group `k` (the GROUP BY members), in order.
pub open spec fn int_members(g: QuerySpec, xs: Seq<Row>, k: Row) -> Seq<Row>
    decreases xs.len(),
{
    if xs.len() == 0 {
        Seq::empty()
    } else if hit(g, xs.last(), k) {
        int_members(g, xs.drop_last(), k).push(int_args(g, xs.last()))
    } else {
        int_members(g, xs.drop_last(), k)
    }
}

/// The aggregate values of group `k`: each SUM as an int8 value.
pub open spec fn int_outs(g: QuerySpec, xs: Seq<Row>, k: Row) -> Row {
    Seq::new(g.aggs.len(), |j: int| Val::Int(gsum(g, xs, k, j)))
}

/// `key ++ sums` of group `k` (the GROUP BY row).
pub open spec fn int_full_row(g: QuerySpec, xs: Seq<Row>, k: Row) -> Row {
    k + int_outs(g, xs, k)
}

/// The GROUP BY's rows: one per group, first-occurrence order.
pub open spec fn int_result_rows(g: QuerySpec, xs: Seq<Row>) -> Seq<Row> {
    gkeys(g, xs).map_values(|k: Row| int_full_row(g, xs, k))
}

/// `group_members` of the prepared (key, args) sequences is `int_members` (exact keys, `k` from the pool).
pub proof fn lemma_int_group_members(g: QuerySpec, xs: Seq<Row>, k: Row, pool: Seq<Row>)
    requires
        forall|a: Row, b: Row| pool.contains(a) && pool.contains(b) ==> (#[trigger] row_not_distinct(a, b) <==> a == b),
        forall|i: int| 0 <= i < qkeys(g, xs).len() ==> pool.contains(#[trigger] qkeys(g, xs)[i]),
        pool.contains(k),
    ensures
        group_members(qkeys(g, xs), qrows(g, xs).map_values(|x: Row| int_args(g, x)), k) == int_members(g, xs, k),
    decreases xs.len(),
{
    let args = |x: Row| int_args(g, x);
    if xs.len() > 0 {
        let xi = xs.drop_last();
        let x = xs.last();
        let qk = qkeys(g, xs);
        let qki = qkeys(g, xi);
        let qa = qrows(g, xs).map_values(args);
        let qai = qrows(g, xi).map_values(args);
        if (g.qual)(x) {
            assert(qk =~= qki.push((g.key)(x)));
            assert(qa =~= qai.push(int_args(g, x)));
            assert forall|i: int| 0 <= i < qki.len() implies pool.contains(#[trigger] qki[i]) by {
                assert(qk[i] == qki[i]);
            }
            lemma_int_group_members(g, xi, k, pool);
            assert(qk.drop_last() =~= qki);
            assert(qa.drop_last() =~= qai);
            assert(pool.contains(qk[qk.len() - 1]));
            assert(row_not_distinct((g.key)(x), k) <==> (g.key)(x) == k);
        } else {
            assert(qk =~= qki);
            assert(qa =~= qai);
            lemma_int_group_members(g, xi, k, pool);
        }
    } else {
        assert(qkeys(g, xs) =~= Seq::<Row>::empty());
    }
}

/// Column `j` of the members: one int4 value per qualifying row of the group, summing to `gsum`.
pub proof fn lemma_int_members_col(g: QuerySpec, xs: Seq<Row>, k: Row, j: int)
    requires 0 <= j < g.aggs.len(),
    ensures ({
        let vs = column(int_members(g, xs, k), j);
        &&& vs.len() == gcount(g, xs, k)
        &&& all_of_kind(NumKind::Int4, vs)
        &&& count_non_null(vs) == gcount(g, xs, k)
        &&& int_sum(vs) == gsum(g, xs, k, j)
    }),
    decreases xs.len(),
{
    let vs = column(int_members(g, xs, k), j);
    if xs.len() > 0 {
        let xi = xs.drop_last();
        let x = xs.last();
        lemma_int_members_col(g, xi, k, j);
        let vsi = column(int_members(g, xi, k), j);
        if hit(g, x, k) {
            assert(vs =~= vsi.push(int_args(g, x)[j]));
            assert(vs.drop_last() =~= vsi);
            assert(int_args(g, x)[j] == Val::Int((g.arg)(j, x)));
        } else {
            assert(vs =~= vsi);
        }
    } else {
        assert(vs =~= Seq::<Val>::empty());
    }
}

/// One group's aggregate row: every SUM is its exact `gsum`, an int8 value.
pub proof fn lemma_int_agg_row(g: QuerySpec, aggs: Seq<Agg>, xs: Seq<Row>, k: Row)
    requires
        int4_sums(aggs, g),
        int_caps(g, xs),
        gcount(g, xs, k) > 0,
    ensures agg_row(aggs, int_members(g, xs, k)) == Ok::<Row, SqlError>(int_outs(g, xs, k)),
{
    let m = int_members(g, xs, k);
    let rs = Seq::new(aggs.len(), |j: int| agg_value(aggs[j], column(m, j)));
    let outs = int_outs(g, xs, k);
    assert forall|j: int| 0 <= j < rs.len() implies #[trigger] rs[j] == Ok::<Val, SqlError>(outs[j]) by {
        lemma_int_members_col(g, xs, k, j);
        assert(int_in_range(IntKind::Int8, gsum(g, xs, k, j)));
    }
    lemma_collect_all(rs, outs);
}

/// The value of one SUM over a group's members: an int8 value or the error 22003.
pub proof fn lemma_int_agg_value(g: QuerySpec, aggs: Seq<Agg>, xs: Seq<Row>, k: Row, j: int)
    requires
        int4_sums(aggs, g),
        0 <= j < aggs.len(),
        gcount(g, xs, k) > 0,
    ensures
        agg_value(aggs[j], column(int_members(g, xs, k), j)) == int_result(IntKind::Int8, gsum(g, xs, k, j)),
{
    lemma_int_members_col(g, xs, k, j);
}

/// GROUP BY over the qualifying rows' (key, int arguments): the row of every group, first-occurrence order.
pub proof fn lemma_int_groups(g: QuerySpec, aggs: Seq<Agg>, xs: Seq<Row>)
    requires
        int4_sums(aggs, g),
        keys_exact(g, xs),
        int_caps(g, xs),
    ensures
        group_rows(aggs, qkeys(g, xs), qrows(g, xs).map_values(|x: Row| int_args(g, x)))
            == Ok::<Seq<Row>, SqlError>(int_result_rows(g, xs)),
{
    let ks = qkeys(g, xs);
    let avs = qrows(g, xs).map_values(|x: Row| int_args(g, x));
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
    let full = int_result_rows(g, xs);
    assert forall|gi: int| 0 <= gi < grs.len() implies #[trigger] grs[gi] == Ok::<Row, SqlError>(full[gi]) by {
        let k = ds[gi];
        assert(pool.contains(k));
        lemma_int_group_members(g, xs, k, pool);
        assert(ds.contains(k));
        lemma_int_agg_row(g, aggs, xs, k);
    }
    lemma_collect_all(grs, full);
}

/// Per kept row: its key tuple and int aggregate arguments (the GROUP BY's prepared sequence).
pub proof fn lemma_int_prepared(db: Database, rows: Seq<Row>, kept: Seq<Row>, cols: Seq<nat>, keys: Seq<Expr>, aggs: Seq<Agg>, g: QuerySpec)
    requires
        keys_agree(db, rows, cols, keys, g),
        int_args_agree(db, rows, cols, aggs, g),
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
            == Ok::<Seq<(Row, Row)>, SqlError>(Seq::new(kept.len(), |i: int| ((g.key)(proj(kept[i], cols)), int_args(g, proj(kept[i], cols))))),
{
    hide(eval_exprs);
    hide(agg_args);
    let ctx = Seq::<Val>::empty();
    let prep = Seq::new(kept.len(), |i: int| ((g.key)(proj(kept[i], cols)), int_args(g, proj(kept[i], cols))));
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
        assert(agg_args(db, rows[m], aggs) == Ok::<Row, SqlError>(int_args(g, proj(rows[m], cols))));
    }
    lemma_collect_all(pre, prep);
}

/// The grouped link: under per-row agreement, exact keys and int8 sums, a GROUP BY over an input that evaluates to
/// the qualifying rows of `rows` is the row of every group key, in first-occurrence order.
pub proof fn lemma_int_group_query(db: Database, rows: Seq<Row>, cols: Seq<nat>, input: Query, keys: Seq<Expr>, aggs: Seq<Agg>, g: QuerySpec)
    requires
        eval_query(db, Seq::empty(), input) == Ok::<Relation, SqlError>(keep_true(rows, qual_truths(g, proj_all(rows, cols)))),
        keys_agree(db, rows, cols, keys, g),
        int_args_agree(db, rows, cols, aggs, g),
        int4_sums(aggs, g),
        keys_exact(g, proj_all(rows, cols)),
        int_caps(g, proj_all(rows, cols)),
    ensures
        eval_query(db, Seq::empty(), Query::GroupBy { keys, aggs, input: Box::new(input) })
            == Ok::<Relation, SqlError>(int_result_rows(g, proj_all(rows, cols))),
{
    hide(eval_pred);
    hide(eval_exprs);
    hide(agg_args);
    hide(group_rows);
    let xs = proj_all(rows, cols);
    let kept = keep_true(rows, qual_truths(g, xs));
    let q = qrows(g, xs);
    lemma_kept_rows(g, rows, cols);
    lemma_int_prepared(db, rows, kept, cols, keys, aggs, g);
    let prep = Seq::new(kept.len(), |i: int| ((g.key)(proj(kept[i], cols)), int_args(g, proj(kept[i], cols))));
    assert(prep.map_values(|p: (Row, Row)| p.0) =~= qkeys(g, xs));
    assert(prep.map_values(|p: (Row, Row)| p.1) =~= q.map_values(|x: Row| int_args(g, x)));
    lemma_int_groups(g, aggs, xs);
    lemma_groupby_unfold(db, input, keys, aggs, kept, prep);
}

/// A group whose sum `j` leaves int8: the GROUP BY is the error 22003 (every other SUM is a value or the same
/// error, so the group order does not matter).
pub proof fn lemma_int_group_err(db: Database, rows: Seq<Row>, cols: Seq<nat>, input: Query, keys: Seq<Expr>, aggs: Seq<Agg>,
    g: QuerySpec, k: Row, j: int)
    requires
        eval_query(db, Seq::empty(), input) == Ok::<Relation, SqlError>(keep_true(rows, qual_truths(g, proj_all(rows, cols)))),
        keys_agree(db, rows, cols, keys, g),
        int_args_agree(db, rows, cols, aggs, g),
        int4_sums(aggs, g),
        keys_exact(g, proj_all(rows, cols)),
        gcount(g, proj_all(rows, cols), k) > 0,
        0 <= j < aggs.len(),
        !int_in_range(IntKind::Int8, gsum(g, proj_all(rows, cols), k, j)),
    ensures
        eval_query(db, Seq::empty(), Query::GroupBy { keys, aggs, input: Box::new(input) })
            == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange),
{
    hide(eval_query);
    hide(eval_exprs);
    hide(agg_args);
    hide(group_input);
    let xs = proj_all(rows, cols);
    let kept = keep_true(rows, qual_truths(g, xs));
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| int_args(g, x));
    let ctx = Seq::<Val>::empty();
    let e = SqlError::NumericValueOutOfRange;
    lemma_kept_rows(g, rows, cols);
    assert(proj_all(kept, cols).len() == kept.len());
    assert forall|i: int| 0 <= i < kept.len() implies #[trigger] group_input(db, ctx + kept[i], keys, aggs)
        == Ok::<(Row, Row), SqlError>((ks[i], args[i])) by {
        assert(ctx + kept[i] =~= kept[i]);
        assert(rows.contains(kept[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
        assert((g.qual)(proj(rows[m], cols)));
        lemma_group_input_unfold(db, kept[i], keys, aggs);
        assert(proj(kept[i], cols) == qrows(g, xs)[i]);
    }
    let pool = key_pool(g, xs);
    lemma_pool_exact(g, xs);
    assert forall|i: int| 0 <= i < qkeys(g, xs).len() implies pool.contains(#[trigger] qkeys(g, xs)[i]) by {
        assert(pool[i] == qkeys(g, xs)[i]);
    }
    lemma_distinct_gkeys(g, xs, pool);
    lemma_gkeys(g, xs);
    let ds = distinct_rows(ks);
    assert(ds.contains(k));
    let gi = choose|gi: int| 0 <= gi < ds.len() && ds[gi] == k;
    assert forall|h: int, jj: int| 0 <= h < ds.len() && 0 <= jj < aggs.len() implies
        #[trigger] agg_value(aggs[jj], column(group_members(ks, args, ds[h]), jj)) is Ok
            || agg_value(aggs[jj], column(group_members(ks, args, ds[h]), jj)) == Err::<Val, SqlError>(e) by {
        assert(ds.contains(ds[h]));
        assert(pool.contains(ds[h]));
        lemma_int_group_members(g, xs, ds[h], pool);
        lemma_int_agg_value(g, aggs, xs, ds[h], jj);
    }
    lemma_int_group_members(g, xs, k, pool);
    lemma_int_agg_value(g, aggs, xs, k, j);
    assert(group_members(ks, args, ds[gi]) == int_members(g, xs, k));
    assert(eval_query(db, ctx, input) == Ok::<Relation, SqlError>(kept));
    lemma_group_by_err(db, ctx, keys, aggs, Box::new(input), kept, ks, args, e, gi, j);
}

/// An output with the distinct group keys `ks` (exactly the non-empty groups) and their rows `full`, sorted by the
/// ORDER BY keys: an allowed output of a statement whose body is the GROUP BY (no OFFSET or LIMIT).
pub proof fn lemma_int_ordered(db: Database, oq: OrderedQuery, g: QuerySpec, xs: Seq<Row>, ks: Seq<Row>, full: Seq<Row>)
    requires
        denote_body(db, oq) == Ok::<Relation, SqlError>(int_result_rows(g, xs)),
        oq.offset == 0,
        oq.limit is None,
        ks.no_duplicates(),
        forall|k: Row| #[trigger] ks.contains(k) <==> gcount(g, xs, k) > 0,
        full.len() == ks.len(),
        forall|i: int| 0 <= i < full.len() ==> #[trigger] full[i] == int_full_row(g, xs, ks[i]),
        sorted_by(oq.keys, full),
    ensures ordered_ok(db, oq, Ok::<Relation, SqlError>(full)),
{
    lemma_gkeys(g, xs);
    lemma_nodup_same_multiset(ks, gkeys(g, xs));
    let f = |k: Row| int_full_row(g, xs, k);
    lemma_map_multiset(ks, gkeys(g, xs), f);
    assert(full =~= ks.map_values(f));
    lemma_slice_all(full);
    assert(full.to_multiset() == int_result_rows(g, xs).to_multiset());
    assert(slice_rows(full, oq.offset, oq.limit) == full);
}

} // verus!
