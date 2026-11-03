//! The outer GROUP BY (`outer_q`: c_count, COUNT(*)) over the inner rows `[c_custkey_i, ccnt(i)]`, and the
//! statement's allowed outputs.
//!
//! In the accumulator normal form of `link::query` (`qspec`: every row qualifies, key `[row[1]]`, one COUNT(*)), the
//! outer GROUP BY is `result_rows(qspec(), inner_rows)` (`lemma_outer_ok`): one row `[c, gcount(c)]` per distinct
//! c_count `c`, where `gcount(c)` is the number of customer rows with c_count `c` (`lemma_gcount_ccnt`). A list of
//! distinct key rows covering exactly those `c`, with their full rows sorted by custdist DESC, c_count DESC, is an
//! allowed output of the statement (`lemma_answer`). A custdist beyond bigint is 22003 (`lemma_outer_overflow`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::equality::*;
use crate::spec::order::*;
use crate::spec::scalar::*;
use crate::spec::int::*;
use crate::spec::limits::*;
use crate::link::expr::*;
use crate::link::query::*;
use crate::link::capacity::lemma_group_by_err;
use crate::bridge::collect::*;
use crate::query::{param_typed, query_spec_at};
use super::sql::*;
use super::group::*;

verus! {

/// The outer GROUP BY in normal form: every row qualifies, its key is `[c_count]`, one COUNT(*).
pub open spec fn qspec() -> QuerySpec {
    QuerySpec {
        qual: |x: Row| true,
        key: |x: Row| seq![x[1]],
        arg: |j: int, x: Row| 0int,
        aggs: seq![AggKind::Count],
        outs: seq![0nat, 1nat],
        grouped: true,
    }
}

/// The columns of the inner rows.
pub open spec fn icols() -> Seq<nat> {
    seq![0nat, 1nat]
}

/// The inner rows are their own projection on both columns.
proof fn lemma_proj_inner(db: Database, ps: Seq<Literal>)
    ensures proj_all(inner_rows(db, ps), icols()) == inner_rows(db, ps),
{
    let rows = inner_rows(db, ps);
    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] proj_all(rows, icols())[i] == rows[i] by {
        assert(proj(rows[i], icols()) =~= rows[i]);
    }
    assert(proj_all(rows, icols()) =~= rows);
}

/// The number of customer rows among the first `m` with c_count `c`.
pub open spec fn cnt_ccnt(db: Database, ps: Seq<Literal>, c: int, m: int) -> nat
    decreases m,
{
    if m <= 0 { 0 } else { cnt_ccnt(db, ps, c, m - 1) + if ccnt(db, ps, m - 1) as int == c { 1nat } else { 0nat } }
}

/// The normal form's group count of key `[c]` counts the customer rows with c_count `c`.
pub proof fn lemma_gcount_ccnt(db: Database, ps: Seq<Literal>, c: int, m: int)
    requires 0 <= m <= ctab(db).len(),
    ensures gcount(qspec(), inner_rows(db, ps).take(m), krow(c)) == cnt_ccnt(db, ps, c, m),
    decreases m,
{
    if m > 0 {
        let rows = inner_rows(db, ps).take(m);
        assert(rows.drop_last() =~= inner_rows(db, ps).take(m - 1));
        lemma_gcount_ccnt(db, ps, c, m - 1);
        let x = rows.last();
        assert(x == seq![ctab(db)[m - 1][0], Val::Int(ccnt(db, ps, m - 1) as int)]);
        assert(((qspec().key)(x) == krow(c)) == (ccnt(db, ps, m - 1) as int == c)) by {
            if (qspec().key)(x) == krow(c) {
                assert((qspec().key)(x)[0] == krow(c)[0]);
            }
            if ccnt(db, ps, m - 1) as int == c {
                assert((qspec().key)(x) =~= krow(c));
            }
        }
    }
}

/// A group count never exceeds the number of rows.
proof fn lemma_gcount_le(g: QuerySpec, rows: Seq<Row>, k: Row)
    ensures gcount(g, rows, k) <= rows.len(),
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_gcount_le(g, rows.drop_last(), k);
    }
}

/// The key of every inner row evaluates to the normal form's key.
proof fn lemma_keys_agree(db: Database, ps: Seq<Literal>)
    ensures keys_agree(db, inner_rows(db, ps), icols(), seq![Expr::Col(1)], qspec()),
{
    hide(eval_exprs);
    let rows = inner_rows(db, ps);
    let g = qspec();
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], icols())) implies
        eval_exprs(db, rows[i], seq![Expr::Col(1)]) == Ok::<Row, SqlError>((g.key)(proj(rows[i], icols()))) by {
        assert(proj(rows[i], icols()) =~= rows[i]);
        lemma_eval_col1(db, rows[i]);
    }
}

/// `[Col(1)]` on a two-column row.
proof fn lemma_eval_col1(db: Database, x: Row)
    requires x.len() == 2,
    ensures eval_exprs(db, x, seq![Expr::Col(1)]) == Ok::<Row, SqlError>(seq![x[1]]),
{
    let ks = seq![Expr::Col(1)];
    lemma_expr_col(db, x, 1);
    lemma_expr_results_index(db, x, ks);
    lemma_collect_all(expr_results(db, x, ks), seq![x[1]]);
}

/// COUNT(*)'s argument row on any row.
proof fn lemma_count_star_args(db: Database, x: Row)
    ensures agg_args(db, x, seq![Agg::CountStar]) == Ok::<Row, SqlError>(seq![Val::Null]),
{
    let ags = seq![Agg::CountStar];
    lemma_agg_arg_results_index(db, x, ags);
    lemma_collect_all(agg_arg_results(db, x, ags), seq![Val::Null]);
}

/// The argument rows of every inner row agree with the normal form's.
proof fn lemma_args_agree(db: Database, ps: Seq<Literal>)
    ensures args_agree(db, inner_rows(db, ps), icols(), seq![Agg::CountStar], qspec()),
{
    hide(agg_args);
    let rows = inner_rows(db, ps);
    let g = qspec();
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], icols())) implies
        agg_args(db, rows[i], seq![Agg::CountStar]) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[i], icols()))) by {
        lemma_count_star_args(db, rows[i]);
        assert(arg_vals(g, proj(rows[i], icols())) =~= seq![Val::Null]);
    }
}

/// On the inner rows, key equality is SQL "not distinct" (integer keys).
proof fn lemma_keys_exact(db: Database, ps: Seq<Literal>)
    ensures keys_exact(qspec(), proj_all(inner_rows(db, ps), icols())),
{
    let rows = inner_rows(db, ps);
    let g = qspec();
    lemma_proj_inner(db, ps);
    assert forall|a: int, b: int| 0 <= a < rows.len() && 0 <= b < rows.len() && (g.qual)(rows[a]) && (g.qual)(rows[b]) implies
        (row_not_distinct(#[trigger] (g.key)(rows[a]), #[trigger] (g.key)(rows[b])) <==> (g.key)(rows[a]) == (g.key)(rows[b])) by {
        let (x, y) = (ccnt(db, ps, a) as int, ccnt(db, ps, b) as int);
        assert((g.key)(rows[a]) =~= krow(x));
        assert((g.key)(rows[b]) =~= krow(y));
        lemma_krow_nd(x, y);
        if krow(x) == krow(y) {
            assert(krow(x)[0] == krow(y)[0]);
        }
    }
}

/// The normal form's COUNT(*) never leaves bigint when no group has more than `int8_max()` rows.
proof fn lemma_caps(db: Database, ps: Seq<Literal>)
    requires forall|k: Row| #[trigger] gcount(qspec(), inner_rows(db, ps), k) <= int8_max(),
    ensures group_caps(qspec(), proj_all(inner_rows(db, ps), icols())),
{
    let rows = inner_rows(db, ps);
    let g = qspec();
    lemma_proj_inner(db, ps);
    assert forall|k: Row, j: int| #![trigger gcount(g, rows, k), g.aggs[j]] 0 <= j < g.aggs.len() && g.aggs[j] is Count
        implies gcount(g, rows, k) <= int8_max() by {
    }
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies #[trigger] gabs(g, rows, k, j) <= crate::link::expr::i128_max() by {
        assert(g.aggs[0] is Count);
    }
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && g.aggs[j] is Avg implies
        crate::spec::fns::div::num_div_fits(#[trigger] gsum(g, rows, k, j), g.aggs[j]->Avg_scale, gcount(g, rows, k) as int, 0) by {
        assert(g.aggs[0] is Count);
    }
}

/// A one-column key's full row has two columns, so selecting both is the full row.
proof fn lemma_select_full(rows: Seq<Row>, k: Row)
    requires k.len() == 1,
    ensures out_row(qspec(), rows, k) == full_row(qspec(), rows, k),
{
    hide(gcount);
    let fr = full_row(qspec(), rows, k);
    assert(agg_outs(qspec(), rows, k).len() == 1);
    assert(fr.len() == 2);
    assert(select(fr, qspec().outs) =~= fr);
}

/// The keys of the normal form are one-column rows.
proof fn lemma_gkeys_width(db: Database, ps: Seq<Literal>)
    ensures forall|i: int| 0 <= i < gkeys(qspec(), inner_rows(db, ps)).len() ==> (#[trigger] gkeys(qspec(), inner_rows(db, ps))[i]).len() == 1,
{
    let rows = inner_rows(db, ps);
    let g = qspec();
    assert forall|i: int| 0 <= i < gkeys(g, rows).len() implies (#[trigger] gkeys(g, rows)[i]).len() == 1 by {
        let k = gkeys(g, rows)[i];
        lemma_gkeys_witness(g, rows, k);
        let m = choose|m: int| 0 <= m < rows.len() && #[trigger] hit(g, rows[m], k);
        assert((g.key)(rows[m]) == k);
    }
}

/// With every c_count and custdist in bigint, the outer GROUP BY is the normal form's result rows.
pub proof fn lemma_outer_ok(db: Database, ps: Seq<Literal>)
    requires
        db_facts(db),
        param_typed(ps),
        !(ctab(db).len() > 0 && some_err(db, ps)),
        forall|i: int| 0 <= i < ctab(db).len() ==> #[trigger] ccnt(db, ps, i) <= int8_max(),
        forall|k: Row| #[trigger] gcount(qspec(), inner_rows(db, ps), k) <= int8_max(),
    ensures
        eval_query(db, Seq::empty(), outer_q(ps)) == Ok::<Relation, SqlError>(result_rows(qspec(), inner_rows(db, ps))),
{
    let rows = inner_rows(db, ps);
    let g = qspec();
    lemma_inner_ok(db, ps);
    lemma_proj_inner(db, ps);
    lemma_table_rows(db, inner_q(ps), rows, icols(), g);
    lemma_keys_agree(db, ps);
    lemma_args_agree(db, ps);
    assert(aggs_match(seq![Agg::CountStar], g)) by {
        assert(agg_matches(seq![Agg::CountStar][0], g.aggs[0]));
    }
    lemma_keys_exact(db, ps);
    lemma_caps(db, ps);
    lemma_group_query(db, rows, icols(), inner_q(ps), seq![Expr::Col(1)], seq![Agg::CountStar], g);
    let ks = gkeys(g, rows);
    let fa = ks.map_values(|k: Row| full_row(g, rows, k));
    let fb = ks.map_values(|k: Row| out_row(g, rows, k));
    lemma_gkeys_width(db, ps);
    assert forall|i: int| 0 <= i < ks.len() implies #[trigger] fa[i] == fb[i] by {
        lemma_select_full(rows, ks[i]);
    }
    assert(fa =~= fb);
}

/// A sorted list of output rows built from distinct key rows covering exactly the groups is an allowed output.
pub proof fn lemma_answer(db: Database, ps: Seq<Literal>, ks: Seq<Row>, full: Seq<Row>)
    requires
        eval_query(db, Seq::empty(), outer_q(ps)) == Ok::<Relation, SqlError>(result_rows(qspec(), inner_rows(db, ps))),
        ks.no_duplicates(),
        forall|i: int| 0 <= i < ks.len() ==> (#[trigger] ks[i]).len() == 1,
        forall|k: Row| #[trigger] ks.contains(k) <==> gcount(qspec(), inner_rows(db, ps), k) > 0,
        full.len() == ks.len(),
        forall|i: int| 0 <= i < full.len() ==> #[trigger] full[i] == full_row(qspec(), inner_rows(db, ps), ks[i]),
        sorted_by(order_keys(), full),
    ensures
        ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(full)),
{
    let g = qspec();
    let rows = inner_rows(db, ps);
    lemma_statement(ps);
    let oq = query_spec_at(ps);
    assert forall|i: int| 0 <= i < full.len() implies #[trigger] full[i] == out_row(g, rows, ks[i]) by {
        lemma_select_full(rows, ks[i]);
    }
    lemma_result_from_keys(g, order_keys(), 0, None, rows, ks, full);
    lemma_slice_all(full);
    lemma_ordered_link(db, oq, g, rows, full);
}

/// The full row of group `[c]`: `[c, gcount(c)]`.
pub proof fn lemma_full_row(db: Database, ps: Seq<Literal>, c: int)
    ensures full_row(qspec(), inner_rows(db, ps), krow(c))
        == seq![Val::Int(c), Val::Int(gcount(qspec(), inner_rows(db, ps), krow(c)) as int)],
{
    let g = qspec();
    let rows = inner_rows(db, ps);
    assert(agg_outs(g, rows, krow(c)) =~= seq![Val::Int(gcount(g, rows, krow(c)) as int)]);
    assert(full_row(g, rows, krow(c)) =~= seq![Val::Int(c), Val::Int(gcount(g, rows, krow(c)) as int)]);
}

/// Every row qualifies: `qrows` of the normal form is its input.
proof fn lemma_qrows_all(xs: Seq<Row>)
    ensures qrows(qspec(), xs) == xs,
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_qrows_all(xs.drop_last());
        assert(xs.drop_last().push(xs.last()) =~= xs);
    } else {
        assert(qrows(qspec(), xs) =~= xs);
    }
}

/// The outer GROUP BY's per-row inputs: key `[c_count]`, COUNT(*)'s argument row `[NULL]`.
proof fn lemma_outer_inputs(db: Database, ps: Seq<Literal>)
    ensures ({
        let rows = inner_rows(db, ps);
        let g = qspec();
        let ks = qkeys(g, rows);
        let args = qrows(g, rows).map_values(|x: Row| arg_vals(g, x));
        &&& ks.len() == rows.len() && args.len() == rows.len()
        &&& forall|i: int| 0 <= i < rows.len() ==> #[trigger] group_input(db, Seq::<Val>::empty() + rows[i], seq![Expr::Col(1)], seq![Agg::CountStar])
                == Ok::<(Row, Row), SqlError>((ks[i], args[i]))
    }),
{
    hide(eval_exprs);
    hide(agg_args);
    let rows = inner_rows(db, ps);
    let g = qspec();
    lemma_qrows_all(rows);
    let ks = qkeys(g, rows);
    let args = qrows(g, rows).map_values(|x: Row| arg_vals(g, x));
    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] group_input(db, Seq::<Val>::empty() + rows[i], seq![Expr::Col(1)], seq![Agg::CountStar])
        == Ok::<(Row, Row), SqlError>((ks[i], args[i])) by {
        let env = Seq::<Val>::empty() + rows[i];
        assert(env =~= rows[i]);
        lemma_eval_col1(db, rows[i]);
        lemma_count_star_args(db, rows[i]);
        assert(ks[i] == (g.key)(rows[i]));
        assert(args[i] =~= seq![Val::Null]);
    }
}

/// The group of `[c]` among the outer GROUP BY's distinct keys, and its COUNT(*) value.
proof fn lemma_outer_group(db: Database, ps: Seq<Literal>, c: int) -> (gi: int)
    requires
        db_facts(db),
        gcount(qspec(), inner_rows(db, ps), krow(c)) > 0,
    ensures ({
        let rows = inner_rows(db, ps);
        let g = qspec();
        let ks = qkeys(g, rows);
        let args = qrows(g, rows).map_values(|x: Row| arg_vals(g, x));
        let ds = distinct_rows(ks);
        &&& 0 <= gi < ds.len()
        &&& ds[gi] == krow(c)
        &&& column(group_members(ks, args, ds[gi]), 0).len() == gcount(g, rows, krow(c))
    }),
{
    let rows = inner_rows(db, ps);
    let g = qspec();
    let ks = qkeys(g, rows);
    lemma_keys_exact(db, ps);
    lemma_proj_inner(db, ps);
    lemma_pool_exact(g, rows);
    let pool = key_pool(g, rows);
    lemma_distinct_gkeys(g, rows, pool);
    lemma_gkeys(g, rows);
    let ds = distinct_rows(ks);
    assert(ds.contains(krow(c)));
    let gi = choose|gi: int| 0 <= gi < ds.len() && ds[gi] == krow(c);
    lemma_group_members(g, rows, krow(c), pool);
    lemma_members_col(g, rows, krow(c), 0);
    gi
}

/// A custdist beyond bigint: the outer GROUP BY raises 22003.
pub proof fn lemma_outer_overflow(db: Database, ps: Seq<Literal>, c: int)
    requires
        db_facts(db),
        param_typed(ps),
        !(ctab(db).len() > 0 && some_err(db, ps)),
        forall|i: int| 0 <= i < ctab(db).len() ==> #[trigger] ccnt(db, ps, i) <= int8_max(),
        gcount(qspec(), inner_rows(db, ps), krow(c)) > int8_max(),
    ensures
        eval_query(db, Seq::empty(), outer_q(ps)) == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange),
{
    hide(gcount);
    let rows = inner_rows(db, ps);
    let g = qspec();
    lemma_inner_ok(db, ps);
    let ks = qkeys(g, rows);
    let args = qrows(g, rows).map_values(|x: Row| arg_vals(g, x));
    let keys = seq![Expr::Col(1)];
    let aggs = seq![Agg::CountStar];
    lemma_outer_inputs(db, ps);
    let gi = lemma_outer_group(db, ps, c);
    let ds = distinct_rows(ks);
    let vs = column(group_members(ks, args, ds[gi]), 0);
    crate::link::capacity::lemma_count_value(Agg::CountStar, vs);
    assert forall|h: int, k: int| 0 <= h < ds.len() && 0 <= k < aggs.len() implies
        #[trigger] agg_value(aggs[k], column(group_members(ks, args, ds[h]), k)) is Ok
            || agg_value(aggs[k], column(group_members(ks, args, ds[h]), k)) == Err::<Val, SqlError>(SqlError::NumericValueOutOfRange) by {
        crate::link::capacity::lemma_count_value(Agg::CountStar, column(group_members(ks, args, ds[h]), k));
    }
    lemma_group_by_err(db, Seq::empty(), keys, aggs, Box::new(inner_q(ps)), rows, ks, args, SqlError::NumericValueOutOfRange, gi, 0);
}

} // verus!
