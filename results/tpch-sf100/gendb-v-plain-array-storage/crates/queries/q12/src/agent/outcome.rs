//! The fixed claim for each outcome of `query`, over every database bound to the stored parts.
//!
//! The parts determine the projected FROM relation of every bound database (`lemma_bound`: it is
//! `xs_of(sv) = product_rows(po_rows(sv), pl_rows(sv))`), so the outcome decided from the parts is the statement's:
//! the rows (`lemma_rows_all`), the error 22003 of a sum beyond int8 (`lemma_sum_err_all`), or the error of
//! `$3 + 1 year` on a non-empty FROM (`lemma_hi_err_all`). `lemma_slot_groups` turns the scan's slot counts
//! (`scan::acc_ok`) into the normal form's group accumulators.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::ast::*;
use crate::spec::eval::lit_val;
use crate::spec::order::*;
use crate::spec::typing::*;
use crate::spec::relation::product_rows;
use crate::spec::datetime::*;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::stores::StoresView;
use crate::query::{param_domain, param_typed, query_spec_at};
use crate::link::query::*;
use crate::link::join::{lemma_proj_product, lemma_product_index, shift};
use crate::agent::common::selection::*;
use crate::agent::common::int_groups::*;
use crate::agent::tables::*;
use crate::agent::normal::*;
use crate::agent::body::*;
use crate::agent::sums::*;
use crate::agent::scan::*;

verus! {

/// The projected FROM relation of every bound database.
pub open spec fn xs_of(sv: StoresView) -> Seq<Row> {
    product_rows(po_rows(sv), pl_rows(sv))
}

/// The one-text group key of ship mode `m`.
pub open spec fn gk(m: Seq<u8>) -> Row {
    seq![Val::Text(m)]
}

/// The parameter literals: two texts and a date whose day number is `pd_of(ps)`.
pub proof fn lemma_params(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures
        params_ok(ps, pd_of(ps)),
        ps[2] is Date,
        1 <= ps[2]->Date_m <= 12,
        1 <= ps[2]->Date_d <= 31,
        -730119 <= pd_of(ps) <= 2921939,
{
    assert(date_from_civil(1, 1, 1) == -730119) by (compute);
    assert(date_from_civil(9999, 12, 31) == 2921939) by (compute);
    let p = ps[2];
    assert(days_in_month(p->Date_y, p->Date_m) <= 31);
}

/// A bound database: its tables have the kinds the statement reads, its projected FROM relation is `xs_of(sv)`,
/// and the statement is the AST of `agent::normal`.
pub proof fn lemma_bound(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps),
    ensures
        body_hyps(db, ps, pd_of(ps)),
        proj_all(from_rows(db), j_cols()) == xs_of(sv),
        from_rows(db).len() == n_o(sv) * n_l(sv),
        query_spec_at(ps).body == ast_body(ps),
        query_spec_at(ps).keys == ast_order_keys(),
        query_spec_at(ps).limit is None,
        query_spec_at(ps).offset == 0,
{
    lemma_params(ps);
    lemma_query_shape(ps);
    lemma_tables(sv, db);
    let (t0, t1) = (db.tables[0], db.tables[1]);
    assert forall|j: int| 0 <= j < t1.len() implies o_row_ok(#[trigger] t1[j]) by {
        lemma_orders_row(sv, db, j);
    }
    assert forall|i: int| 0 <= i < t0.len() implies l_row_ok(#[trigger] t0[i]) by {
        lemma_lineitem_row(sv, db, i);
    }
    assert(j_cols() =~= o_cols() + shift(l_cols(), 9));
    lemma_proj_product(t1, t0, o_cols(), l_cols(), 9, 16);
    lemma_product_index(t1, t0);
}

// ------------------------------------------------------------------------------------------------ slot counts

/// A range sum of zeros.
proof fn lemma_range_sum_zero(lo: int, hi: int, f: spec_fn(int) -> int)
    requires forall|i: int| lo <= i < hi ==> #[trigger] f(i) == 0,
    ensures range_sum(lo, hi, f) == 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_range_sum_zero(lo, hi - 1, f);
    }
}

/// The scan's slot terms are the group terms of `sums`: slot 0 is `$1`'s group, slot 1 is `$2`'s when it differs
/// and empty otherwise.
pub proof fn lemma_slot_terms(sv: StoresView, q: Probe, n: int)
    requires probe_ok(q),
    ensures
        rs(sv, q, 0, n, t_n(sv, q, 0)) == range_sum(0, n, cnt_term(sv, q.dlo as int, q.dhi as int, q.p1@)),
        rs(sv, q, 0, n, t_h(sv, q, 0)) == range_sum(0, n, hi_term(sv, q.dlo as int, q.dhi as int, q.p1@)),
        q.two ==> rs(sv, q, 0, n, t_n(sv, q, 1)) == range_sum(0, n, cnt_term(sv, q.dlo as int, q.dhi as int, q.p2@)),
        q.two ==> rs(sv, q, 0, n, t_h(sv, q, 1)) == range_sum(0, n, hi_term(sv, q.dlo as int, q.dhi as int, q.p2@)),
        !q.two ==> rs(sv, q, 0, n, t_n(sv, q, 1)) == 0,
        !q.two ==> rs(sv, q, 0, n, t_h(sv, q, 1)) == 0,
{
    let (dlo, dhi) = (q.dlo as int, q.dhi as int);
    let p = p_qual(sv, q);
    let (gn0, gh0, gn1, gh1) = (guard(p, t_n(sv, q, 0)), guard(p, t_h(sv, q, 0)), guard(p, t_n(sv, q, 1)), guard(p, t_h(sv, q, 1)));
    assert forall|i: int| 0 <= i < n implies #[trigger] gn0(i) == cnt_term(sv, dlo, dhi, q.p1@)(i) by {}
    assert forall|i: int| 0 <= i < n implies #[trigger] gh0(i) == hi_term(sv, dlo, dhi, q.p1@)(i) by {}
    lemma_range_sum_ext(0, n, gn0, cnt_term(sv, dlo, dhi, q.p1@));
    lemma_range_sum_ext(0, n, gh0, hi_term(sv, dlo, dhi, q.p1@));
    if q.two {
        assert forall|i: int| 0 <= i < n implies #[trigger] gn1(i) == cnt_term(sv, dlo, dhi, q.p2@)(i) by {}
        assert forall|i: int| 0 <= i < n implies #[trigger] gh1(i) == hi_term(sv, dlo, dhi, q.p2@)(i) by {}
        lemma_range_sum_ext(0, n, gn1, cnt_term(sv, dlo, dhi, q.p2@));
        lemma_range_sum_ext(0, n, gh1, hi_term(sv, dlo, dhi, q.p2@));
    } else {
        assert forall|i: int| 0 <= i < n implies #[trigger] gn1(i) == 0 by {}
        assert forall|i: int| 0 <= i < n implies #[trigger] gh1(i) == 0 by {}
        lemma_range_sum_zero(0, n, gn1);
        lemma_range_sum_zero(0, n, gh1);
    }
}

/// What the call established before deciding the outcome: the parameters, the probe and window, the stored
/// columns' facts, and the upper bound `t1` (the one of `$3 + 1 year` when FROM is not empty).
pub open spec fn call_facts(sv: StoresView, ps: Seq<Literal>, q: Probe, t1: int) -> bool {
    &&& param_domain(ps)
    &&& q.p1@ == p1_of(ps) && q.p2@ == p2_of(ps)
    &&& probe_ok(q)
    &&& sums_hyps(sv, q.dlo as int, q.dhi as int, pd_of(ps), t1)
    &&& (n_o(sv) > 0 && n_l(sv) > 0 ==> hi_res(pd_of(ps)) == Ok::<int, SqlError>(t1))
}

/// The normal form of the call.
pub open spec fn g_call(ps: Seq<Literal>, t1: int) -> QuerySpec {
    g_at(ps, pd_of(ps), t1)
}

/// The group of ship mode `m` (one of the two parameters) has count `n` and high count `h`: its accumulators.
pub open spec fn group_is(ps: Seq<Literal>, t1: int, sv: StoresView, m: Seq<u8>, n: int, h: int) -> bool {
    &&& gcount(g_call(ps, t1), xs_of(sv), gk(m)) == n
    &&& gsum(g_call(ps, t1), xs_of(sv), gk(m), 0) == h
    &&& gsum(g_call(ps, t1), xs_of(sv), gk(m), 1) == n - h
    &&& 0 <= h <= n
}

/// The scan's counts of all rows are the group accumulators of `$1` and (when it differs) `$2`.
pub proof fn lemma_slot_groups(sv: StoresView, ps: Seq<Literal>, q: Probe, t1: int, acc: Counts)
    requires call_facts(sv, ps, q, t1), acc_ok(acc, sv, q, 0, n_l(sv)),
    ensures
        group_is(ps, t1, sv, q.p1@, acc.n0 as int, acc.h0 as int),
        q.two ==> group_is(ps, t1, sv, q.p2@, acc.n1 as int, acc.h1 as int),
{
    let (dlo, dhi, pd) = (q.dlo as int, q.dhi as int, pd_of(ps));
    let n = n_l(sv);
    lemma_slot_terms(sv, q, n);
    lemma_group_sums(sv, p1_of(ps), p2_of(ps), dlo, dhi, pd, t1, q.p1@);
    lemma_lo_count(sv, dlo, dhi, q.p1@, 0, n);
    assert forall|i: int| 0 <= #[trigger] lo_term(sv, dlo, dhi, q.p1@)(i) <= 1 by {}
    lemma_range_sum_01(lo_term(sv, dlo, dhi, q.p1@), 0, n);
    assert forall|i: int| 0 <= #[trigger] hi_term(sv, dlo, dhi, q.p1@)(i) <= 1 by {}
    lemma_range_sum_01(hi_term(sv, dlo, dhi, q.p1@), 0, n);
    if q.two {
        lemma_group_sums(sv, p1_of(ps), p2_of(ps), dlo, dhi, pd, t1, q.p2@);
        lemma_lo_count(sv, dlo, dhi, q.p2@, 0, n);
        assert forall|i: int| 0 <= #[trigger] lo_term(sv, dlo, dhi, q.p2@)(i) <= 1 by {}
        lemma_range_sum_01(lo_term(sv, dlo, dhi, q.p2@), 0, n);
        assert forall|i: int| 0 <= #[trigger] hi_term(sv, dlo, dhi, q.p2@)(i) <= 1 by {}
        lemma_range_sum_01(hi_term(sv, dlo, dhi, q.p2@), 0, n);
    }
}

/// Keys other than the parameters' have no rows.
pub proof fn lemma_other_groups(sv: StoresView, ps: Seq<Literal>, q: Probe, t1: int, k: Row)
    requires call_facts(sv, ps, q, t1), k != gk(q.p1@), k != gk(q.p2@),
    ensures
        gcount(g_call(ps, t1), xs_of(sv), k) == 0,
        gsum(g_call(ps, t1), xs_of(sv), k, 0) == 0,
        gsum(g_call(ps, t1), xs_of(sv), k, 1) == 0,
{
    lemma_other_key(sv, p1_of(ps), p2_of(ps), q.dlo as int, q.dhi as int, pd_of(ps), t1, k);
    lemma_zero_count(g_call(ps, t1), xs_of(sv), k, 0);
    lemma_zero_count(g_call(ps, t1), xs_of(sv), k, 1);
}

// ------------------------------------------------------------------------------------------------ the outcomes

/// Rows: the group rows `full` of the distinct keys `ks` (exactly the non-empty groups), sorted by ship mode, are an
/// allowed output for every bound database.
pub proof fn lemma_rows_all(sv: StoresView, ps: Seq<Literal>, q: Probe, t1: int, ks: Seq<Row>, full: Seq<Row>)
    requires
        call_facts(sv, ps, q, t1),
        int_caps(g_call(ps, t1), xs_of(sv)),
        ks.no_duplicates(),
        forall|k: Row| #[trigger] ks.contains(k) <==> gcount(g_call(ps, t1), xs_of(sv), k) > 0,
        full.len() == ks.len(),
        forall|i: int| 0 <= i < full.len() ==> #[trigger] full[i] == int_full_row(g_call(ps, t1), xs_of(sv), ks[i]),
        sorted_by(ast_order_keys(), full),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(full)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(full)) by {
        let pd = pd_of(ps);
        lemma_bound(sv, db, ps);
        if from_rows(db).len() > 0 {
            assert(n_o(sv) > 0 && n_l(sv) > 0) by (nonlinear_arith)
                requires from_rows(db).len() == n_o(sv) * n_l(sv), from_rows(db).len() > 0, n_o(sv) >= 0, n_l(sv) >= 0;
        }
        lemma_body_ok(db, ps, pd, t1);
        lemma_int_ordered(db, query_spec_at(ps), g_call(ps, t1), xs_of(sv), ks, full);
    }
}

/// A group whose sum `j` leaves int8: every bound database's meaning is the error 22003.
pub proof fn lemma_sum_err_all(sv: StoresView, ps: Seq<Literal>, q: Probe, t1: int, k: Row, j: int)
    requires
        call_facts(sv, ps, q, t1),
        gcount(g_call(ps, t1), xs_of(sv), k) > 0,
        0 <= j < 2,
        !int_in_range(IntKind::Int8, gsum(g_call(ps, t1), xs_of(sv), k, j)),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==>
            ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange)) by {
        let pd = pd_of(ps);
        lemma_bound(sv, db, ps);
        if from_rows(db).len() > 0 {
            assert(n_o(sv) > 0 && n_l(sv) > 0) by (nonlinear_arith)
                requires from_rows(db).len() == n_o(sv) * n_l(sv), from_rows(db).len() > 0, n_o(sv) >= 0, n_l(sv) >= 0;
        }
        lemma_body_sum_err(db, ps, pd, t1, k, j);
    }
}

/// `$3 + 1 year` fails on a non-empty FROM: every bound database's meaning is that error.
pub proof fn lemma_hi_err_all(sv: StoresView, ps: Seq<Literal>, e: SqlError)
    requires
        param_domain(ps),
        n_o(sv) > 0, n_l(sv) > 0,
        hi_res(pd_of(ps)) == Err::<int, SqlError>(e),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(e)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(e)) by {
        lemma_bound(sv, db, ps);
        assert(from_rows(db).len() > 0) by (nonlinear_arith)
            requires from_rows(db).len() == n_o(sv) * n_l(sv), n_o(sv) > 0, n_l(sv) > 0;
        lemma_body_hi_err(db, ps, pd_of(ps), e);
    }
}

} // verus!
