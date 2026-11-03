//! The two outcomes other than rows: a group count beyond int8 makes the statement's meaning the SQL error 22003
//! (`lemma_count_error`); an AVG division outside the executable domain puts the database outside the capacity
//! domain (`lemma_avg_capacity`, every count inside int8). Both go through the link toolkit's GROUP BY lemmas
//! (`link::capacity`) over the kept rows, whose groups and members `agent::sql` describes.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::order::*;
use crate::spec::int::*;
use crate::spec::limits::*;
use crate::spec::numeric::*;
use crate::spec::aggs::avg::*;
use crate::spec::fns::div::*;
use crate::exec::relational::domain::*;
use crate::spec::equality::*;
use crate::link::query::{qrows, qkeys, gkeys, qual_truths, proj_all};
use crate::link::capacity::{lemma_group_by_err, lemma_group_by_capacity, aggs_ok_inside, lemma_avg_inside_ok};
use crate::query::query_spec;
use crate::agent::cols::*;
use crate::agent::spec::*;
use crate::agent::sql::*;

verus! {

/// The GROUP BY's input rows, keys, arguments and groups (`ds`), each group's members being `mm`.
pub proof fn lemma_group_setup(c: Cols, db: Database, t: Seq<Row>)
    requires corr(c, t), 3 < db.tables.len(), db.tables[3] == t,
    ensures ({
        let kept = qrows(gq(), t);
        let ks = qkeys(gq(), t);
        let args = kept.map_values(|r: Row| myargs(r));
        let ds = distinct_rows(ks);
        &&& eval_query(db, Seq::empty(), q_input()) == Ok::<Relation, SqlError>(kept)
        &&& ks.len() == kept.len() && args.len() == kept.len()
        &&& forall|i: int| 0 <= i < kept.len() ==> #[trigger] group_input(db, Seq::<Val>::empty() + kept[i], q_keys(), q_aggs())
            == Ok::<(Row, Row), SqlError>((ks[i], args[i]))
        &&& ds == gkeys(gq(), t)
        &&& forall|h: int| 0 <= h < ds.len() ==> #[trigger] group_members(ks, args, ds[h]) == mm(t, ds[h], t.len() as int)
        &&& forall|h: int| 0 <= h < ds.len() ==> cnt_r(t, #[trigger] ds[h], 0, t.len() as int) > 0
    }),
{
    lemma_keys_typed(c, t);
    lemma_filter(db, t);
    lemma_kept(t);
    lemma_groups_keys(t);
    let kept = qrows(gq(), t);
    let ks = qkeys(gq(), t);
    let args = kept.map_values(|r: Row| myargs(r));
    let ds = distinct_rows(ks);
    assert forall|i: int| 0 <= i < kept.len() implies #[trigger] group_input(db, Seq::<Val>::empty() + kept[i], q_keys(), q_aggs())
        == Ok::<(Row, Row), SqlError>((ks[i], args[i])) by {
        assert(Seq::<Val>::empty() + kept[i] =~= kept[i]);
        lemma_row_exprs(db, kept[i]);
    }
    let n = t.len() as int;
    assert(t.subrange(0, n) =~= t);
    assert forall|h: int| 0 <= h < ds.len() implies #[trigger] group_members(ks, args, ds[h]) == mm(t, ds[h], n) by {
        assert(kpool(t).contains(ds[h]));
        lemma_members(t, ds[h], n);
    }
    assert forall|h: int| 0 <= h < ds.len() implies cnt_r(t, #[trigger] ds[h], 0, n) > 0 by {
        assert(ds.contains(ds[h]));
    }
}

/// The three aggregate values of a group with rows, as functions of its count, sum and distinct values.
pub proof fn lemma_agg_values(c: Cols, t: Seq<Row>, k: Row)
    requires corr(c, t), cnt_r(t, k, 0, t.len() as int) > 0,
    ensures ({
        let n = t.len() as int;
        let m = mm(t, k, n);
        let cnt = cnt_r(t, k, 0, n) as int;
        &&& agg_value(q_aggs()[0], column(m, 0)) == int_result(IntKind::Int8, cnt)
        &&& agg_value(q_aggs()[1], column(m, 1)) == int_result(IntKind::Int8, aset_r(t, k, 0, n).len() as int)
        &&& aset_r(t, k, 0, n).len() <= cnt
        &&& agg_value(q_aggs()[2], column(m, 2)) == num_div(sum_r(t, k, 0, n), 0, cnt, 0)
        &&& all_of_kind(NumKind::Int4, column(m, 2))
        &&& count_non_null(column(m, 2)) == cnt
        &&& avg_sum(NumKind::Int4, column(m, 2)) == (sum_r(t, k, 0, n), 0nat)
    }),
{
    let n = t.len() as int;
    let m = mm(t, k, n);
    lemma_mm(c, t, k, n);
    lemma_aset_finite(t, k, 0, n);
    let d = distinct_vals(column(m, 1));
    let a = aset_r(t, k, 0, n);
    d.unique_seq_to_set();
    assert(d.to_set() =~= a);
    assert(agg_value(Agg::Count(Expr::Col(0)), d) == int_result(IntKind::Int8, count_non_null(d) as int));
}

/// A group count beyond int8: the statement's meaning is the SQL error 22003.
pub proof fn lemma_count_error(c: Cols, db: Database, t: Seq<Row>, k: Row)
    requires
        corr(c, t), 3 < db.tables.len(), db.tables[3] == t,
        gkeys(gq(), t).contains(k), cnt_r(t, k, 0, t.len() as int) > int8_max(),
    ensures
        denote_body(db, query_spec()) == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange),
{
    let n = t.len() as int;
    let e = SqlError::NumericValueOutOfRange;
    lemma_group_setup(c, db, t);
    lemma_query_shape();
    let kept = qrows(gq(), t);
    let ks = qkeys(gq(), t);
    let args = kept.map_values(|r: Row| myargs(r));
    let ds = distinct_rows(ks);
    let aggs = q_aggs();
    let g = choose|g: int| 0 <= g < ds.len() && ds[g] == k;
    assert(group_members(ks, args, ds[g]) == mm(t, k, n));
    lemma_agg_values(c, t, k);
    assert forall|h: int, j: int| 0 <= h < ds.len() && 0 <= j < aggs.len()
        implies #[trigger] agg_value(aggs[j], column(group_members(ks, args, ds[h]), j)) is Ok
            || agg_value(aggs[j], column(group_members(ks, args, ds[h]), j)) == Err::<Val, SqlError>(e) by {
        let kh = ds[h];
        assert(group_members(ks, args, ds[h]) == mm(t, kh, n));
        assert(cnt_r(t, kh, 0, n) > 0);
        lemma_agg_values(c, t, kh);
    }
    lemma_group_by_err(db, Seq::empty(), q_keys(), aggs, Box::new(q_input()), kept, ks, args, e, g, 0);
}

/// Every count inside int8 and one group's AVG division outside the executable domain: the database is outside
/// the capacity domain.
pub proof fn lemma_avg_capacity(c: Cols, db: Database, t: Seq<Row>, k: Row)
    requires
        corr(c, t), 3 < db.tables.len(), db.tables[3] == t,
        forall|k2: Row| #[trigger] gkeys(gq(), t).contains(k2) ==> cnt_r(t, k2, 0, t.len() as int) <= int8_max(),
        gkeys(gq(), t).contains(k),
        !num_div_fits(sum_r(t, k, 0, t.len() as int), 0, cnt_r(t, k, 0, t.len() as int) as int, 0),
    ensures
        !fits_query(db, Seq::empty(), query_spec().body),
{
    let n = t.len() as int;
    lemma_group_setup(c, db, t);
    lemma_query_shape();
    let kept = qrows(gq(), t);
    let ks = qkeys(gq(), t);
    let args = kept.map_values(|r: Row| myargs(r));
    let ds = distinct_rows(ks);
    let aggs = q_aggs();
    let g = choose|g: int| 0 <= g < ds.len() && ds[g] == k;
    assert(group_members(ks, args, ds[g]) == mm(t, k, n));
    lemma_agg_values(c, t, k);
    assert(!fits_agg_value(aggs[2], column(mm(t, k, n), 2)));
    assert forall|h: int| 0 <= h < ds.len() implies #[trigger] aggs_ok_inside(aggs, group_members(ks, args, ds[h])) by {
        let kh = ds[h];
        let m = mm(t, kh, n);
        assert(group_members(ks, args, ds[h]) == m);
        assert(ds.contains(kh));
        lemma_agg_values(c, t, kh);
        assert forall|j: int| 0 <= j < aggs.len() && #[trigger] fits_agg_value(aggs[j], column(m, j))
            implies agg_value(aggs[j], column(m, j)) is Ok by {
            if j == 2 {
                lemma_avg_inside_ok(NumKind::Int4, Expr::Col(2), column(m, 2));
            }
        }
    }
    lemma_group_by_capacity(db, Seq::empty(), q_keys(), aggs, Box::new(q_input()), kept, ks, args, g, 2);
}

} // verus!
