//! The statement's body over a bound database, stated with the per-lineitem totals `t = line::tot(sv, ps, 0, n_l)`:
//! - every `$k + 10` inside int4: the one aggregate row `grow(t)` inside the SUM capacity, outside the capacity
//!   domain beyond it (`lemma_body_rows`);
//! - an empty product: one NULL, whatever the parameters (`lemma_body_empty`);
//! - some `$k + 10` past int4 on a non-empty product: `NumericValueOutOfRange` (`lemma_body_err`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::numeric::*;
use crate::exec::relational::domain::{fits_query, lemma_eval_aggregate};
use crate::gendb_entry::stores::StoresView;
use crate::link::join::{keep, sum_of, lemma_sum_of_ext};
use crate::link::expr::i128_max;
use crate::query::param_domain;
use crate::agent::tables::*;
use crate::agent::line::*;
use crate::agent::ast::*;
use crate::agent::bind::adds_ok;
use crate::agent::joined::*;
use crate::agent::agg::*;

verus! {

/// Every kept row has the shape the argument reads.
proof fn lemma_kept_shape(sv: StoresView, ps: Seq<Literal>)
    requires domains_ok(sv),
    ensures all_jshape(keep(jrows(sv), jq(ps))),
{
    let k = keep(jrows(sv), jq(ps));
    lemma_kept_rows(sv, ps);
    assert forall|i: int| 0 <= i < k.len() implies jshape(#[trigger] k[i]) by {
        let (l, a) = choose|l: int, a: int| 0 <= l < n_l(sv) && 0 <= a < n_p(sv) && k[i] == #[trigger] row2(sv, l, a);
        lemma_row2_shape(sv, l, a);
    }
}

/// The number of rows is the sum of 1 over them.
proof fn lemma_sum_one(ks: Seq<Row>, f: spec_fn(Row) -> int)
    requires forall|i: int| 0 <= i < ks.len() ==> f(#[trigger] ks[i]) == 1,
    ensures sum_of(ks, f) == ks.len(),
    decreases ks.len(),
{
    if ks.len() > 0 {
        let ki = ks.drop_last();
        assert forall|i: int| 0 <= i < ki.len() implies f(#[trigger] ki[i]) == 1 by { assert(ki[i] == ks[i]); }
        lemma_sum_one(ki, f);
        assert(f(ks[ks.len() - 1]) == 1);
    }
}

/// The sums over the kept rows are the per-lineitem totals.
pub proof fn lemma_kept_tot(sv: StoresView, ps: Seq<Literal>)
    requires model_ok(sv),
    ensures ksums(keep(jrows(sv), jq(ps))) == tot(sv, ps, 0, n_l(sv) as int),
{
    let k = keep(jrows(sv), jq(ps));
    lemma_kept_rows(sv, ps);
    lemma_kept_sums(sv, ps);
    assert forall|i: int| 0 <= i < k.len() implies (jt_cnt(ps))(#[trigger] k[i]) == 1 by {}
    lemma_sum_one(k, jt_cnt(ps));
    assert forall|i: int| 0 <= i < k.len() implies (kt_all())(#[trigger] k[i]) == (jt_all(ps))(k[i]) by {}
    lemma_sum_of_ext(k, kt_all(), jt_all(ps));
    assert forall|i: int| 0 <= i < k.len() implies (kt_abs())(#[trigger] k[i]) == (jt_abs(ps))(k[i]) by {}
    lemma_sum_of_ext(k, kt_abs(), jt_abs(ps));
}

/// The body over a bound database when every `$k + 10` stays inside int4.
pub proof fn lemma_body_rows(db: Database, sv: StoresView, ps: Seq<Literal>)
    requires tables_of(sv, db), model_ok(sv), param_domain(ps), adds_ok(ps),
    ensures ({
        let t = tot(sv, ps, 0, n_l(sv) as int);
        &&& t.a_all <= i128_max() ==> eval_query(db, Seq::empty(), q_body(ps)) == Ok::<Relation, SqlError>(seq![grow(t)])
        &&& t.a_all > i128_max() ==> !fits_query(db, Seq::empty(), q_body(ps))
    }),
{
    crate::agent::joined::lemma_eval_filter(db, sv, ps);
    lemma_kept_shape(sv, ps);
    lemma_kept_tot(sv, ps);
    let ks = keep(jrows(sv), jq(ps));
    if ksums(ks).a_all <= i128_max() {
        lemma_eval_agg(db, ps, ks);
    } else {
        lemma_agg_capacity(db, ps, ks);
    }
}

/// An empty product: the body is one NULL, whatever the parameters.
pub proof fn lemma_body_empty(db: Database, sv: StoresView, ps: Seq<Literal>)
    requires tables_of(sv, db), model_ok(sv), jrows(sv).len() == 0,
    ensures eval_query(db, Seq::empty(), q_body(ps)) == Ok::<Relation, SqlError>(seq![seq![Val::Null]]),
{
    lemma_eval_filter_empty(db, sv, ps);
    let k = keep(jrows(sv), jq(ps));
    assert(k =~= Seq::<Row>::empty());
    assert(all_jshape(k));
    lemma_cols(k);
    lemma_eval_agg(db, ps, k);
}

/// Some `$k + 10` past int4 on a non-empty product: the body is that error.
pub proof fn lemma_body_err(db: Database, sv: StoresView, ps: Seq<Literal>)
    requires tables_of(sv, db), model_ok(sv), param_domain(ps), !adds_ok(ps), jrows(sv).len() > 0,
    ensures eval_query(db, Seq::empty(), q_body(ps)) == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange),
{
    let ctx = Seq::<Val>::empty();
    lemma_filter_err(db, sv, ps);
    lemma_eval_aggregate(db, ctx, q_aggs(), Box::new(q_filter(ps)));
}

} // verus!
