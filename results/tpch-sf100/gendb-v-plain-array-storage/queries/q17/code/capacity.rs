//! The capacity outcome of a selected key whose AVG division leaves its executable domain (`num_div_fits` fails):
//! the WHERE condition of the joined row of the first lineitem row and that key's part row evaluates the
//! subquery, whose aggregate is outside its domain (`lemma_sub_capacity`); no condition errs, so the canonical
//! evaluation reaches that row, and the filter, the aggregate and the body are outside the capacity domain
//! (`lemma_body_capacity`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::fns::div::*;
use crate::spec::aggs::avg::*;
use crate::exec::domain::*;
use crate::exec::relational::domain::*;
use crate::gendb_entry::stores::StoresView;
use crate::link::join::{keep, lemma_keep_members, lemma_product_index};
use crate::link::capacity::{lemma_filter_capacity, lemma_first_input, lemma_aggregate_capacity, aggs_ok_inside};
use crate::agent::tables::*;
use crate::agent::ast::*;
use crate::agent::sub::*;
use crate::agent::joined::*;
use crate::agent::keys::*;
use crate::agent::common::selection::*;
use crate::stores::flat_lineitem::interface as li;

verus! {

/// The AVG arguments of the kept inner rows of key `k`, row by row.
proof fn lemma_cap_args(db: Database, sv: StoresView, x: Row, k: int)
    requires tables_of(sv, db), x.len() == 25,
    ensures ({
        let ks = keep(line_rows(sv), kf(k));
        forall|i: int| 0 <= i < ks.len() ==> #[trigger] agg_args(db, x + ks[i], sub_aggs()) == Ok::<Row, SqlError>(sub_args(ks)[i])
    }),
{
    hide(agg_args);
    let rows = line_rows(sv);
    let ks = keep(rows, kf(k));
    lemma_keep_members(rows, kf(k));
    assert forall|i: int| 0 <= i < ks.len() implies #[trigger] agg_args(db, x + ks[i], sub_aggs()) == Ok::<Row, SqlError>(sub_args(ks)[i]) by {
        assert(rows.contains(ks[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == ks[i];
        assert(rows[m] == li::row_at(sv.flat_lineitem, m));
        lemma_sub_arg_row(db, x, ks[i]);
    }
}

/// The AVG of key `k`'s rows is outside its domain, and the aggregate row's only aggregate is that one.
proof fn lemma_cap_value(sv: StoresView, k: int)
    requires model_ok(sv), kcnt(sv, k) > 0, !num_div_fits(ksum(sv, k), 2, kcnt(sv, k), 0),
    ensures ({
        let args = sub_args(keep(line_rows(sv), kf(k)));
        &&& !fits_agg_value(sub_aggs()[0], column(args, 0))
        &&& aggs_ok_inside(sub_aggs(), args)
        &&& sub_aggs().len() == 1
    }),
{
    lemma_kept_totals(sv, k);
    let ks = keep(line_rows(sv), kf(k));
    let aggs = sub_aggs();
    let args = sub_args(ks);
    let col = column(args, 0);
    assert(col =~= qty_col(ks));
    lemma_qty_col(ks);
    assert(avg_sum(NumKind::Numeric, col) == (ksum(sv, k), 2nat));
    assert(!fits_avg(NumKind::Numeric, col));
    assert(aggs[0] == Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(29) });
    assert(!fits_agg_value(aggs[0], col));
    assert(aggs_ok_inside(aggs, args)) by {
        assert forall|j: int| 0 <= j < aggs.len() && #[trigger] fits_agg_value(aggs[j], column(args, j))
            implies agg_value(aggs[j], column(args, j)) is Ok by {
            assert(j == 0);
        }
    }
}

/// The subquery of a key `k` with rows whose AVG division leaves its domain is outside the capacity domain, in
/// every context `x` holding `k` as its part key.
pub proof fn lemma_sub_capacity(db: Database, sv: StoresView, x: Row, k: int)
    requires
        tables_of(sv, db), model_ok(sv), sizes_ok(sv), x.len() == 25, x[16] == Val::Int(k),
        kcnt(sv, k) > 0, !num_div_fits(ksum(sv, k), 2, kcnt(sv, k), 0),
    ensures !fits_query(db, x, sub_q()),
{
    hide(eval_query);
    hide(fits_query);
    hide(agg_args);
    hide(fits_agg_value);
    hide(aggs_ok_inside);
    lemma_sub_filter(db, sv, x, k);
    lemma_kept_totals(sv, k);
    let ks = keep(line_rows(sv), kf(k));
    let args = sub_args(ks);
    lemma_cap_args(db, sv, x, k);
    lemma_cap_value(sv, k);
    assert(args.len() == ks.len());
    lemma_aggregate_capacity(db, x, sub_aggs(), Box::new(sub_filter()), ks, args, 0);
    lemma_first_input(db, x, sub_q());
}

/// The WHERE condition on the joined row `x` of lineitem row `l` and part row `a` is outside its domain when the
/// subquery of `a`'s key is.
proof fn lemma_pred_capacity(db: Database, sv: StoresView, ps: Seq<Literal>, l: int, a: int)
    requires
        tables_of(sv, db), model_ok(sv), sizes_ok(sv), params_text(ps), 0 <= l < n_l(sv), 0 <= a < n_p(sv),
        !fits_query(db, row2(sv, l, a), sub_q()),
    ensures !fits_pred(db, row2(sv, l, a), q_pred(ps)),
{
    let x = row2(sv, l, a);
    lemma_row2(sv, l, a);
    lemma_part_pred_row2(db, sv, ps, l, a);
    assert(eval_expr(db, x, Expr::Col(4)) is Ok);
    assert(!fits_expr(db, x, Expr::Subquery(Box::new(sub_q()))));
    assert(!fits_pred(db, x, lt_pred()));
}

/// A selected key with rows whose AVG division leaves its executable domain: the body is outside the capacity
/// domain.
pub proof fn lemma_body_capacity(db: Database, sv: StoresView, ps: Seq<Literal>, keys: Seq<i64>, srows: Seq<int>, s: int)
    requires
        tables_of(sv, db), model_ok(sv), sizes_ok(sv), params_text(ps),
        keys_ok(keys, srows, sv, ps), 0 <= s < keys.len(),
        kcnt(sv, keys[s] as int) > 0,
        !num_div_fits(ksum(sv, keys[s] as int), 2, kcnt(sv, keys[s] as int), 0),
    ensures !fits_query(db, Seq::empty(), q_body(ps)),
{
    let k = keys[s] as int;
    lemma_range_filter_members(0, n_p(sv) as int, selr(sv, ps));
    let a = srows[s];
    assert(0 <= a < n_p(sv));
    assert(keys[s] == p_key(sv)[a]);
    // some lineitem row exists: the key has rows
    if n_l(sv) == 0 {
        assert(kcnt(sv, k) == range_sum(0, 0, kcnt_term(sv, k)));
    }
    let l = 0int;
    let x = row2(sv, l, a);
    lemma_row2(sv, l, a);
    lemma_sub_capacity(db, sv, x, k);
    lemma_pred_capacity(db, sv, ps, l, a);
    // the joined row is row `0 * n_p + a` of the product
    let rows = jrows(sv);
    lemma_product_index(line_rows(sv), part_rows(sv));
    assert(rows[0 * n_p(sv) + a] == line_rows(sv)[0] + part_rows(sv)[a]);
    assert(0 * n_p(sv) + a == a);
    let ctx = Seq::<Val>::empty();
    assert(ctx + rows[a] =~= x);
    lemma_eval_from(sv, db);
    assert forall|i: int| 0 <= i < rows.len() && #[trigger] fits_pred(db, ctx + rows[i], q_pred(ps))
        implies eval_pred(db, ctx + rows[i], q_pred(ps)) is Ok by {
        assert(ctx + rows[i] =~= rows[i]);
        lemma_jrows_elem(sv, i);
        let (l2, a2) = choose|l2: int, a2: int| 0 <= l2 < n_l(sv) && 0 <= a2 < n_p(sv) && rows[i] == #[trigger] row2(sv, l2, a2);
        lemma_pred_row2(db, sv, ps, l2, a2);
    }
    lemma_jrows_len(sv);
    lemma_filter_capacity(db, ctx, q_pred(ps), Box::new(q_from()), rows, a);
    lemma_first_input(db, ctx, q_agg(ps));
    lemma_first_input(db, ctx, q_body(ps));
}

} // verus!
