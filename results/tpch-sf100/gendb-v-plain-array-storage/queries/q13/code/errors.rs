//! The statement's SQL errors, in the canonical evaluation order:
//! - a `LIKE` that raises (22025, a dangling escape reached) while there is a customer: the LEFT JOIN's error
//!   (`lemma_like_error`);
//! - otherwise a `c_count` beyond int8: the inner GROUP BY's error 22003 (`lemma_count_error`);
//! - otherwise a `custdist` beyond int8: the outer GROUP BY's error 22003 (`lemma_custdist_error`).
//! Each propagates through the operators above it (`link::capacity::lemma_first_input`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::order::*;
use crate::spec::equality::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::query::{query_spec_at, param_domain};
use crate::bridge::collect::*;
use crate::link::query::*;
use crate::link::capacity::{lemma_first_input, lemma_collect_uniform_err, lemma_group_by_err};
use crate::agent::tables::*;
use crate::agent::normal::*;
use crate::agent::denote::*;
use crate::agent::inner::*;
use crate::agent::answer::*;

verus! {

/// An error of the inner GROUP BY is the statement's.
proof fn lemma_inner_err_up(db: Database, ps: Seq<Literal>, e: SqlError)
    requires eval_query(db, Seq::empty(), q_inner(ps)) == Err::<Relation, SqlError>(e),
    ensures denote_body(db, query_spec_at(ps)) == Err::<Relation, SqlError>(e),
{
    lemma_query_shape(ps);
    lemma_first_input(db, Seq::empty(), q_outer(ps));
}

/// A raising `LIKE` with a customer: the statement's meaning is 22025.
pub proof fn lemma_like_error(sv: StoresView, db: Database, ps: Seq<Literal>, j0: int)
    requires bound_db(sv, db), param_domain(ps), n_c(sv) > 0, 0 <= j0 < n_o(sv), like_j(sv, pat_of(ps), j0) is Err,
    ensures denote_body(db, query_spec_at(ps)) == Err::<Relation, SqlError>(SqlError::InvalidEscapeSequence),
{
    lemma_join_err(sv, db, ps, j0);
    lemma_first_input(db, Seq::empty(), q_inner(ps));
    lemma_inner_err_up(db, ps, SqlError::InvalidEscapeSequence);
}

/// A `c_count` beyond int8 (no `LIKE` raising): the statement's meaning is 22003.
pub proof fn lemma_count_error(sv: StoresView, db: Database, ps: Seq<Literal>, i0: int)
    requires
        bound_db(sv, db), param_domain(ps), likes_ok(sv, pat_of(ps)),
        0 <= i0 < n_c(sv), ccnt(sv, pat_of(ps), i0) > i64::MAX,
    ensures denote_body(db, query_spec_at(ps)) == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange),
{
    let pat = pat_of(ps);
    let e = SqlError::NumericValueOutOfRange;
    lemma_inner(sv, db, ps);
    let irs = inner_results(sv, pat);
    assert forall|i: int| 0 <= i < irs.len() implies #[trigger] irs[i] is Ok || irs[i] == Err::<Row, SqlError>(e) by {}
    assert(irs[i0] == Err::<Row, SqlError>(e));
    lemma_collect_uniform_err(irs, e, i0);
    lemma_inner_err_up(db, ps, e);
}

/// Every inner row qualifies: the qualifying rows are all rows.
proof fn lemma_qrows_all(xs: Seq<Row>)
    ensures qrows(g2(), xs) == xs,
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_qrows_all(xs.drop_last());
        assert(xs.drop_last().push(xs.last()) =~= xs);
    }
}

/// The outer GROUP BY's per-row inputs over the inner rows: key `[c_count]`, argument NULL.
proof fn lemma_outer_inputs(db: Database, xs: Seq<Row>)
    requires forall|i: int| 0 <= i < xs.len() ==> (#[trigger] xs[i]).len() == 2,
    ensures ({
        let ks = qkeys(g2(), xs);
        let args = qrows(g2(), xs).map_values(|x: Row| arg_vals(g2(), x));
        &&& ks.len() == xs.len() && args.len() == xs.len()
        &&& forall|i: int| 0 <= i < xs.len() ==> #[trigger] group_input(db, Seq::<Val>::empty() + xs[i], q_outer_keys(), q_outer_aggs())
                == Ok::<(Row, Row), SqlError>((ks[i], args[i]))
    }),
{
    let g = g2();
    let ctx = Seq::<Val>::empty();
    lemma_qrows_all(xs);
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] group_input(db, ctx + xs[i], q_outer_keys(), q_outer_aggs())
        == Ok::<(Row, Row), SqlError>((ks[i], args[i])) by {
        assert(ctx + xs[i] =~= xs[i]);
        crate::link::query::lemma_eval_cols(db, xs[i], seq![1nat]);
        assert(col_exprs(seq![1nat]) =~= q_outer_keys());
        assert(select(xs[i], seq![1nat]) =~= seq![xs[i][1]]);
        lemma_agg_arg_results_index(db, xs[i], q_outer_aggs());
        lemma_collect_all(agg_arg_results(db, xs[i], q_outer_aggs()), seq![Val::Null]);
        assert(args[i] =~= seq![Val::Null]);
    }
}

/// The group `[v]` of the outer GROUP BY is one of its groups, with `hcount(v)` members.
proof fn lemma_outer_group(sv: StoresView, pat: Seq<u8>, v: int) -> (gi: int)
    requires hcount(sv, pat, v, n_c(sv)) > 0,
    ensures ({
        let xs = r1(sv, pat);
        let ks = qkeys(g2(), xs);
        let args = qrows(g2(), xs).map_values(|x: Row| arg_vals(g2(), x));
        &&& 0 <= gi < distinct_rows(ks).len()
        &&& column(group_members(ks, args, distinct_rows(ks)[gi]), 0).len() == hcount(sv, pat, v, n_c(sv))
    }),
{
    let g = g2();
    let xs = r1(sv, pat);
    let ks = qkeys(g, xs);
    let pool = key_pool(g, xs);
    lemma_r1_exact(sv, pat);
    lemma_pool_exact(g, xs);
    assert forall|i: int| 0 <= i < ks.len() implies pool.contains(#[trigger] ks[i]) by {
        assert(pool[i] == ks[i]);
    }
    lemma_distinct_gkeys(g, xs, pool);
    let k = seq![Val::Int(v)];
    assert(xs.subrange(0, n_c(sv)) =~= xs);
    lemma_gcount(sv, pat, v, n_c(sv));
    lemma_gkeys(g, xs);
    assert(gkeys(g, xs).contains(k));
    let gi = choose|gi: int| 0 <= gi < gkeys(g, xs).len() && gkeys(g, xs)[gi] == k;
    lemma_gkeys_witness(g, xs, k);
    let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], k);
    lemma_qrows_all(xs);
    assert(pool.contains(k)) by { assert(pool[m] == ks[m]); assert(ks[m] == (g.key)(xs[m])); }
    lemma_group_members(g, xs, k, pool);
    lemma_members_col(g, xs, k, 0);
    gi
}

/// A `custdist` beyond int8 (no earlier error): the statement's meaning is 22003.
pub proof fn lemma_custdist_error(sv: StoresView, db: Database, ps: Seq<Literal>, v: int)
    requires
        bound_db(sv, db), param_domain(ps), n_c(sv) == 0 || likes_ok(sv, pat_of(ps)),
        forall|i: int| 0 <= i < n_c(sv) ==> #[trigger] ccnt(sv, pat_of(ps), i) <= i64::MAX,
        hcount(sv, pat_of(ps), v, n_c(sv)) > i64::MAX,
    ensures denote_body(db, query_spec_at(ps)) == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange),
{
    let pat = pat_of(ps);
    let e = SqlError::NumericValueOutOfRange;
    let g = g2();
    let xs = r1(sv, pat);
    lemma_inner_ok(sv, db, ps);
    lemma_outer_inputs(db, xs);
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    let gi = lemma_outer_group(sv, pat, v);
    assert(q_outer_aggs()[0] == Agg::CountStar);
    assert(q_outer_aggs().len() == 1);
    lemma_group_by_err(db, Seq::empty(), q_outer_keys(), q_outer_aggs(), Box::new(q_inner(ps)), xs, ks, args, e, gi, 0);
    lemma_query_shape(ps);
}

/// The outer GROUP BY's keys over the inner rows are exact.
proof fn lemma_r1_exact(sv: StoresView, pat: Seq<u8>)
    ensures keys_exact(g2(), r1(sv, pat)),
{
    let g = g2();
    let xs = r1(sv, pat);
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        crate::agent::common::groups::lemma_int_keys(ccnt(sv, pat, a) as int, ccnt(sv, pat, b) as int);
        assert((g.key)(xs[a]) == seq![Val::Int(ccnt(sv, pat, a) as int)]);
        assert((g.key)(xs[b]) == seq![Val::Int(ccnt(sv, pat, b) as int)]);
        if seq![Val::Int(ccnt(sv, pat, a) as int)] == seq![Val::Int(ccnt(sv, pat, b) as int)] {
            assert(seq![Val::Int(ccnt(sv, pat, a) as int)][0] == seq![Val::Int(ccnt(sv, pat, b) as int)][0]);
        }
    }
}

} // verus!
