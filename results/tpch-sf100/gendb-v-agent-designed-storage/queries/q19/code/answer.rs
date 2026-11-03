//! The statement's outcomes from the stored totals, for every database bound to the parts.
//!
//! The statement is `Aggregate [SUM(v)] (Filter pred (Product lineitem part))`. Over the kept rows, the SUM's
//! argument column holds the value of every kept row at scale 4 (`col_of`): its exact sum, count and absolute mass
//! are the sum, count and mass accumulators (`lemma_col`, `joinsum::lemma_sum_chain`). So the one result row is
//! `[Num(tot sum, 4)]`, or `[NULL]` when no row is kept (`lemma_agg_value`); a mass beyond `i128::MAX` is outside
//! the capacity domain (`lemma_agg_cap`); with some `$q + 10` outside int4 the statement is the error 22003 on a
//! non-empty product (`lemma_agg_err`) and `[NULL]` on an empty one (`lemma_agg_empty`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::numeric::*;
use crate::spec::scalar::NumKind;
use crate::gendb_entry::layout::PartView;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::order::*;
use crate::exec::value::*;
use crate::exec::relational::domain::*;
use crate::gendb_entry::{Answer, bound_db, outcome_ok, capacity_domain};
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::runtime::QueryError;
use crate::link::expr::lemma_align_same;
use crate::link::join::{sum_of, keep, lemma_keep_members, lemma_product_index};
use crate::link::query::{view_rows, lemma_aggregate_unfold};
use crate::link::capacity::{lemma_sum_inside_ok, aggs_ok_inside, lemma_aggregate_capacity, lemma_first_input};
use crate::link::outcome::{lemma_outcome_rows, lemma_outcome_err};
use crate::bridge::collect::lemma_collect_all;
use crate::query::{param_domain, query_spec_at};
use super::model::*;
use super::terms::*;
use super::kernel::*;
use super::sqlrow::*;
use super::joinsum::*;
use super::bind::*;

verus! {

// ------------------------------------------------------------------------------------------------ the SUM column

/// The SUM's argument column over the kept rows.
pub open spec fn col_of(ks: Seq<Row>) -> Seq<Val> {
    ks.map_values(|x: Row| xv(x))
}

/// The argument rows of the kept rows.
pub open spec fn args_of(ks: Seq<Row>) -> Seq<Row> {
    ks.map_values(|x: Row| seq![xv(x)])
}

/// Every row satisfies the condition.
pub open spec fn all_q(ks: Seq<Row>, ps: Seq<Literal>) -> bool {
    forall|i: int| 0 <= i < ks.len() ==> qx(ps)(#[trigger] ks[i])
}

/// The column of numerics at scale 4: its exact sum and mass are the sum and mass accumulators over the rows.
pub proof fn lemma_col(ks: Seq<Row>, ps: Seq<Literal>)
    requires all_q(ks, ps),
    ensures
        all_of_kind(NumKind::Numeric, col_of(ks)),
        count_non_null(col_of(ks)) == ks.len(),
        num_sum(col_of(ks)) == (sum_of(ks, tx(ps, 1)), if ks.len() > 0 { 4nat } else { 0nat }),
        num_max_scale(col_of(ks)) == if ks.len() > 0 { 4nat } else { 0nat },
        num_mass_at(col_of(ks), 4) == sum_of(ks, tx(ps, 2)),
    decreases ks.len(),
{
    let vs = col_of(ks);
    if ks.len() > 0 {
        let d = ks.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies qx(ps)(#[trigger] d[i]) by {
            assert(d[i] == ks[i]);
        }
        lemma_col(d, ps);
        assert(vs.drop_last() =~= col_of(d));
        let x = ks.last();
        assert(qx(ps)(ks[ks.len() - 1]));
        let c = wv(zx(x));
        assert(vs.last() == Val::Num { coeff: c, scale: 4 });
        assert(tx(ps, 1)(x) == c);
        assert(tx(ps, 2)(x) == abs(c));
        assert(pow10(0) == 1) by (compute);
        lemma_align_same(c, 4);
        let s = num_sum(col_of(d));
        if d.len() == 0 {
            assert(s == (0int, 0nat));
            assert(pow10(4) == 10000) by (compute);
            crate::link::expr::lemma_align_by(0, 0, 4, 10000);
        } else {
            lemma_align_same(s.0, 4);
        }
    }
}

/// The columns of the argument rows.
pub proof fn lemma_columns(ks: Seq<Row>)
    ensures
        column(args_of(ks), 0) == col_of(ks),
        args_of(ks).len() == ks.len(),
{
    assert(column(args_of(ks), 0) =~= col_of(ks));
}

/// The argument row of one product row.
proof fn lemma_kept_arg(db: Database, x: Row)
    requires rows_typed(db), prod_of(db).contains(x),
    ensures agg_args(db, Seq::<Val>::empty() + x, seq![sum_agg()]) == Ok::<Row, SqlError>(seq![xv(x)]),
{
    hide(agg_args);
    hide(xrow_typed);
    hide(prod_of);
    lemma_prod_typed(db);
    assert(Seq::<Val>::empty() + x =~= x);
    let pr = prod_of(db);
    let m = choose|m: int| 0 <= m < pr.len() && pr[m] == x;
    assert(xrow_typed(pr[m]));
    lemma_row_arg(db, x);
}

/// The kept rows' argument rows, collected.
pub proof fn lemma_kept_args(db: Database, ks: Seq<Row>)
    requires
        rows_typed(db),
        forall|i: int| 0 <= i < ks.len() ==> prod_of(db).contains(#[trigger] ks[i]),
    ensures
        collect(Seq::new(ks.len(), |i: int| agg_args(db, Seq::<Val>::empty() + ks[i], seq![sum_agg()]))) == Ok::<Seq<Row>, SqlError>(args_of(ks)),
        forall|i: int| 0 <= i < ks.len() ==> #[trigger] agg_args(db, Seq::<Val>::empty() + ks[i], seq![sum_agg()]) == Ok::<Row, SqlError>(args_of(ks)[i]),
{
    hide(agg_args);
    hide(prod_of);
    hide(rows_typed);
    let rs = Seq::new(ks.len(), |i: int| agg_args(db, Seq::<Val>::empty() + ks[i], seq![sum_agg()]));
    assert forall|i: int| 0 <= i < ks.len() implies #[trigger] agg_args(db, Seq::<Val>::empty() + ks[i], seq![sum_agg()]) == Ok::<Row, SqlError>(args_of(ks)[i]) by {
        lemma_kept_arg(db, ks[i]);
    }
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(args_of(ks)[i]) by {}
    lemma_collect_all(rs, args_of(ks));
}

// ------------------------------------------------------------------------------------------------ the totals

/// The result value of the totals: the sum at scale 4, or NULL when no row is kept.
pub open spec fn tot_val(fp: Seq<PartView>, cp: Seq<PartView>, ps: Seq<Literal>) -> Val {
    if tot(fp, cp, ps, 0, 0, n_pa(cp)) > 0 { Val::Num { coeff: tot(fp, cp, ps, 1, 0, n_pa(cp)), scale: 4 } } else { Val::Null }
}

/// No `$q + 10` leaves int4.
pub open spec fn no_ovf(ps: Seq<Literal>) -> bool {
    !ovf(ps, 0) && !ovf(ps, 1) && !ovf(ps, 2)
}

/// The kept rows and their columns' accumulators.
proof fn lemma_kept(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps), no_ovf(ps),
    ensures ({
        let ks = kept_of(db, ps);
        let (fp, cp) = (sv.facts, sv.custpart);
        &&& rows_typed(db)
        &&& eval_query(db, Seq::empty(), filter_q(ps)) == Ok::<Relation, SqlError>(ks)
        &&& all_q(ks, ps)
        &&& forall|i: int| 0 <= i < ks.len() ==> prod_of(db).contains(#[trigger] ks[i])
        &&& ks.len() == tot(fp, cp, ps, 0, 0, n_pa(cp))
        &&& sum_of(ks, tx(ps, 1)) == tot(fp, cp, ps, 1, 0, n_pa(cp))
        &&& sum_of(ks, tx(ps, 2)) == tot(fp, cp, ps, 2, 0, n_pa(cp))
    }),
{
    lemma_rows_typed(db);
    lemma_eval_filter_q(db, ps);
    let ks = kept_of(db, ps);
    lemma_keep_members(prod_of(db), qx(ps));
    lemma_kept_count(sv, db, ps);
    lemma_sum_chain(sv, db, ps, 1);
    lemma_sum_chain(sv, db, ps, 2);
}

/// The statement's body with the mass inside `i128`: the one row of the totals' value.
pub proof fn lemma_agg_value(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires
        bound_db(sv, db),
        param_domain(ps),
        no_ovf(ps),
        tot(sv.facts, sv.custpart, ps, 2, 0, n_pa(sv.custpart)) <= i128::MAX,
    ensures
        eval_query(db, Seq::empty(), agg_q(ps)) == Ok::<Relation, SqlError>(seq![seq![tot_val(sv.facts, sv.custpart, ps)]]),
{
    hide(eval_query);
    let ks = kept_of(db, ps);
    lemma_kept(sv, db, ps);
    lemma_kept_args(db, ks);
    lemma_col(ks, ps);
    lemma_columns(ks);
    let aggs = seq![sum_agg()];
    lemma_aggregate_unfold(db, filter_q(ps), aggs, ks, args_of(ks));
    let vs = col_of(ks);
    assert(fits_agg_value(sum_agg(), vs));
    lemma_sum_inside_ok(NumKind::Numeric, val_expr(), vs);
    let v = tot_val(sv.facts, sv.custpart, ps);
    assert(agg_value(sum_agg(), vs) == Ok::<Val, SqlError>(v));
    let rs = Seq::new(aggs.len(), |j: int| agg_value(aggs[j], column(args_of(ks), j)));
    assert forall|j: int| 0 <= j < rs.len() implies #[trigger] rs[j] == Ok::<Val, SqlError>(seq![v][j]) by {
        assert(aggs[0] == sum_agg());
    }
    lemma_collect_all(rs, seq![v]);
    assert(agg_row(aggs, args_of(ks)) == Ok::<Row, SqlError>(seq![v]));
}

/// The mass beyond `i128::MAX`: the body is outside the capacity domain.
pub proof fn lemma_agg_cap(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires
        bound_db(sv, db),
        param_domain(ps),
        no_ovf(ps),
        tot(sv.facts, sv.custpart, ps, 2, 0, n_pa(sv.custpart)) > i128::MAX,
    ensures
        !fits_query(db, Seq::empty(), agg_q(ps)),
{
    hide(eval_query);
    hide(fits_query);
    let ctx = Seq::<Val>::empty();
    let ks = kept_of(db, ps);
    lemma_kept(sv, db, ps);
    lemma_kept_args(db, ks);
    lemma_col(ks, ps);
    lemma_columns(ks);
    let aggs = seq![sum_agg()];
    assert(ks.len() > 0) by {
        if ks.len() == 0 {
            assert(sum_of(ks, tx(ps, 2)) == 0);
        }
    }
    let vs = col_of(ks);
    assert(aggs[0] == sum_agg());
    assert(!fits_agg_value(aggs[0], column(args_of(ks), 0)));
    assert(aggs_ok_inside(aggs, args_of(ks)));
    lemma_aggregate_capacity(db, ctx, aggs, Box::new(filter_q(ps)), ks, args_of(ks), 0);
}

/// Some `$q + 10` outside int4 on a non-empty product: the body is the error 22003.
pub proof fn lemma_agg_err(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires
        bound_db(sv, db),
        param_domain(ps),
        !no_ovf(ps),
        n_li(sv.facts) > 0,
        n_pa(sv.custpart) > 0,
    ensures
        eval_query(db, Seq::empty(), agg_q(ps)) == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange),
{
    hide(eval_query);
    lemma_rows_typed(db);
    lemma_li_link(sv, db);
    lemma_pa_link(sv, db);
    let pr = prod_of(db);
    lemma_product_index(db.tables[0], db.tables[3]);
    assert(pr.len() > 0) by (nonlinear_arith)
        requires pr.len() == db.tables[0].len() * db.tables[3].len(), db.tables[0].len() > 0, db.tables[3].len() > 0;
    lemma_eval_filter_err(db, ps);
    lemma_first_input(db, Seq::empty(), agg_q(ps));
}

/// An empty product: the body is the row `[NULL]`.
pub proof fn lemma_agg_empty(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires
        bound_db(sv, db),
        n_li(sv.facts) == 0 || n_pa(sv.custpart) == 0,
    ensures
        eval_query(db, Seq::empty(), agg_q(ps)) == Ok::<Relation, SqlError>(seq![seq![Val::Null]]),
{
    hide(eval_query);
    hide(agg_args);
    lemma_rows_typed(db);
    lemma_li_link(sv, db);
    lemma_pa_link(sv, db);
    let pr = prod_of(db);
    lemma_product_index(db.tables[0], db.tables[3]);
    assert(pr.len() == 0) by (nonlinear_arith)
        requires pr.len() == db.tables[0].len() * db.tables[3].len(), db.tables[0].len() == 0 || db.tables[3].len() == 0;
    lemma_eval_filter_empty(db, ps);
    let ks = Seq::<Row>::empty();
    let aggs = seq![sum_agg()];
    assert(Seq::new(ks.len(), |i: int| agg_args(db, Seq::<Val>::empty() + ks[i], aggs)) =~= Seq::<Result<Row, SqlError>>::empty());
    lemma_aggregate_unfold(db, filter_q(ps), aggs, ks, Seq::<Row>::empty());
    let row = seq![Val::Null];
    let rs = Seq::new(1, |j: int| agg_value(aggs[j], column(Seq::<Row>::empty(), j)));
    assert forall|j: int| 0 <= j < rs.len() implies #[trigger] rs[j] == Ok::<Val, SqlError>(row[j]) by {
        assert(column(Seq::<Row>::empty(), j) =~= Seq::<Val>::empty());
    }
    lemma_collect_all(rs, row);
}

// ------------------------------------------------------------------------------------------------ the answers

pub proof fn lemma_answer_err(sv: StoresView, ps: Seq<Literal>)
    requires
        param_domain(ps),
        !no_ovf(ps),
        n_li(sv.facts) > 0,
        n_pa(sv.custpart) > 0,
    ensures forall|db: Database| #[trigger] bound_db(sv, db) ==> outcome_ok(db, query_spec_at(ps),
        Ok::<Answer, QueryError>(Answer::SqlError(SqlError::NumericValueOutOfRange))),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps),
        Ok::<Answer, QueryError>(Answer::SqlError(SqlError::NumericValueOutOfRange))) by {
        lemma_ast(ps);
        lemma_agg_err(sv, db, ps);
        lemma_outcome_err(db, query_spec_at(ps), SqlError::NumericValueOutOfRange);
    }
}

pub proof fn lemma_answer_empty(sv: StoresView, ps: Seq<Literal>, rows: Vec<Vec<EVal>>)
    requires
        n_li(sv.facts) == 0 || n_pa(sv.custpart) == 0,
        view_rows(rows@) == seq![seq![Val::Null]],
    ensures forall|db: Database| #[trigger] bound_db(sv, db) ==> outcome_ok(db, query_spec_at(ps),
        Ok::<Answer, QueryError>(Answer::Rows(rows))),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps),
        Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
        lemma_ast(ps);
        lemma_agg_empty(sv, db, ps);
        lemma_outcome_rows(db, query_spec_at(ps), seq![seq![Val::Null]]);
    }
}

pub proof fn lemma_answer_cap(sv: StoresView, ps: Seq<Literal>)
    requires
        param_domain(ps),
        no_ovf(ps),
        tot(sv.facts, sv.custpart, ps, 2, 0, n_pa(sv.custpart)) > mmax(),
    ensures forall|db: Database| #[trigger] bound_db(sv, db) ==> outcome_ok(db, query_spec_at(ps),
        Ok::<Answer, QueryError>(Answer::Capacity)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps),
        Ok::<Answer, QueryError>(Answer::Capacity)) by {
        lemma_ast(ps);
        lemma_agg_cap(sv, db, ps);
    }
}

pub proof fn lemma_answer_rows(sv: StoresView, ps: Seq<Literal>, acc: Acc, rows: Vec<Vec<EVal>>)
    requires
        param_domain(ps),
        no_ovf(ps),
        acc_ok(acc, sv.facts, sv.custpart, ps, 0, n_pa(sv.custpart)),
        acc_small(acc),
        view_rows(rows@) == seq![seq![if acc.any { Val::Num { coeff: acc.sum as int, scale: 4 } } else { Val::Null }]],
    ensures forall|db: Database| #[trigger] bound_db(sv, db) ==> outcome_ok(db, query_spec_at(ps),
        Ok::<Answer, QueryError>(Answer::Rows(rows))),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps),
        Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
        lemma_ast(ps);
        lemma_agg_value(sv, db, ps);
        assert(tot_val(sv.facts, sv.custpart, ps) == (if acc.any { Val::Num { coeff: acc.sum as int, scale: 4 } } else { Val::Null }));
        lemma_outcome_rows(db, query_spec_at(ps), seq![seq![tot_val(sv.facts, sv.custpart, ps)]]);
    }
}

} // verus!
