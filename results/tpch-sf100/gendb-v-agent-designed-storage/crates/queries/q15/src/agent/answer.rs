//! The statement's allowed outputs from what the plans compute: the largest group sum `M` (`is_max`, or no group
//! at all) and, per supplier row, whether its key is a group of sum `M` (`res_rows`). The rows `res_rows` of the
//! supplier rows are the body (`lemma_res_body`), so their sort by `s_suppkey` is an allowed output
//! (`lemma_rows_ok`). All of it is stated over any row order of the lineitem rows: the accumulators of a permutation
//! agree (`lemma_acc_perm`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::spec::typing::db_wf;
use crate::spec::aggs::minmax::extremum;
use crate::query::{param_typed, query_spec_at, lemma_query_wf_at};
use crate::schema::schema_spec;
use crate::link::query::*;
use crate::link::expr::{ival, i128_max};
use crate::link::join::{lemma_acc_sum_of, lemma_sum_of_perm, count_term, sum_term, abs_term};
use crate::bridge::order::lemma_denote_top_ok;
use super::window::*;
use super::sql::*;
use super::group::*;
use super::body::*;

verus! {

// ------------------------------------------------------------------------------------------------ the result

/// `M` is the largest group sum: some group has it, no group exceeds it.
pub open spec fn is_max(g: QuerySpec, xs: Seq<Row>, m: int) -> bool {
    &&& exists|k: Row| gcount(g, xs, k) > 0 && #[trigger] gsum(g, xs, k, 0) == m
    &&& forall|k: Row| #[trigger] gcount(g, xs, k) > 0 ==> gsum(g, xs, k, 0) <= m
}

/// No group at all.
pub open spec fn no_groups(g: QuerySpec, xs: Seq<Row>) -> bool {
    forall|k: Row| #[trigger] gcount(g, xs, k) == 0
}

/// Supplier row `s`'s key is a group of sum `m`.
pub open spec fn hit_m(g: QuerySpec, xs: Seq<Row>, m: int, s: Row) -> bool {
    gcount(g, xs, seq![s[0]]) > 0 && gsum(g, xs, seq![s[0]], 0) == m
}

/// The result rows: per supplier row, in order, its output row when its key is a group of sum `m`.
pub open spec fn res_rows(ss: Seq<Row>, g: QuerySpec, xs: Seq<Row>, m: int) -> Seq<Row>
    decreases ss.len(),
{
    if ss.len() == 0 {
        Seq::empty()
    } else {
        res_rows(ss.drop_last(), g, xs, m)
            + if hit_m(g, xs, m, ss.last()) { seq![res_row(ss.last(), Val::Num { coeff: m, scale: 4 })] } else { Seq::<Row>::empty() }
    }
}

/// The MAX of the group sums is `M`.
pub proof fn lemma_max_val(g: QuerySpec, xs: Seq<Row>, m: int)
    requires is_max(g, xs, m),
    ensures max_val(g, xs) == (Val::Num { coeff: m, scale: 4 }),
{
    let vs = gvals(g, xs);
    let ks = gkeys(g, xs);
    lemma_gkeys(g, xs);
    assert forall|i: int| 0 <= i < vs.len() implies (#[trigger] vs[i]) is Num && vs[i]->scale == 4 by {}
    lemma_max_num(vs, 4);
    let kw = choose|k: Row| gcount(g, xs, k) > 0 && #[trigger] gsum(g, xs, k, 0) == m;
    assert(ks.contains(kw));
    let iw = choose|i: int| 0 <= i < ks.len() && ks[i] == kw;
    assert(vs[iw]->coeff == m);
    let r = max_val(g, xs);
    let im = choose|i: int| 0 <= i < vs.len() && vs[i] == r;
    assert(ks.contains(ks[im]));
    assert(gcount(g, xs, ks[im]) > 0);
    assert(r->coeff == gsum(g, xs, ks[im], 0));
}

/// With `M` the largest group sum, the body's rows are `res_rows`.
pub proof fn lemma_body_res(ss: Seq<Row>, g: QuerySpec, xs: Seq<Row>, m: int)
    requires is_max(g, xs, m),
    ensures body_rows(ss, g, xs, max_val(g, xs)) == res_rows(ss, g, xs, m),
    decreases ss.len(),
{
    lemma_max_val(g, xs, m);
    if ss.len() > 0 {
        lemma_body_res(ss.drop_last(), g, xs, m);
        let s = ss.last();
        assert(hitk(g, xs, max_val(g, xs), s) == hit_m(g, xs, m, s));
    }
}

/// Without a group, the body has no row, and neither has `res_rows`.
pub proof fn lemma_body_none(ss: Seq<Row>, g: QuerySpec, xs: Seq<Row>, mv: Val, m: int)
    requires no_groups(g, xs),
    ensures
        body_rows(ss, g, xs, mv) == Seq::<Row>::empty(),
        res_rows(ss, g, xs, m) == Seq::<Row>::empty(),
    decreases ss.len(),
{
    if ss.len() > 0 {
        lemma_body_none(ss.drop_last(), g, xs, mv, m);
        let s = ss.last();
        assert(gcount(g, xs, seq![s[0]]) == 0);
        assert(Seq::<Row>::empty() + Seq::<Row>::empty() =~= Seq::<Row>::empty());
    }
}

// ------------------------------------------------------------------------------------------------ permutations

/// The accumulators of a permutation agree.
pub proof fn lemma_acc_perm(g: QuerySpec, a: Seq<Row>, b: Seq<Row>, k: Row)
    requires a.to_multiset() == b.to_multiset(),
    ensures
        gcount(g, a, k) == gcount(g, b, k),
        gsum(g, a, k, 0) == gsum(g, b, k, 0),
        gabs(g, a, k, 0) == gabs(g, b, k, 0),
{
    lemma_acc_sum_of(g, a, k, 0);
    lemma_acc_sum_of(g, b, k, 0);
    lemma_sum_of_perm(a, b, count_term(g, k));
    lemma_sum_of_perm(a, b, sum_term(g, k, 0));
    lemma_sum_of_perm(a, b, abs_term(g, k, 0));
}

/// `is_max`, `no_groups` and `res_rows` carry over to a permutation.
pub proof fn lemma_res_perm(ss: Seq<Row>, g: QuerySpec, a: Seq<Row>, b: Seq<Row>, m: int)
    requires a.to_multiset() == b.to_multiset(),
    ensures
        is_max(g, a, m) ==> is_max(g, b, m),
        no_groups(g, a) ==> no_groups(g, b),
        res_rows(ss, g, a, m) == res_rows(ss, g, b, m),
    decreases ss.len(),
{
    if is_max(g, a, m) {
        let kw = choose|k: Row| gcount(g, a, k) > 0 && #[trigger] gsum(g, a, k, 0) == m;
        lemma_acc_perm(g, a, b, kw);
        assert forall|k: Row| #[trigger] gcount(g, b, k) > 0 implies gsum(g, b, k, 0) <= m by {
            lemma_acc_perm(g, a, b, k);
        }
    }
    if no_groups(g, a) {
        assert forall|k: Row| #[trigger] gcount(g, b, k) == 0 by {
            lemma_acc_perm(g, a, b, k);
        }
    }
    if ss.len() > 0 {
        lemma_res_perm(ss.drop_last(), g, a, b, m);
        lemma_acc_perm(g, a, b, seq![ss.last()[0]]);
    }
}

/// Group caps carry over to a permutation.
pub proof fn lemma_caps_perm(lo: int, hi: int, a: Seq<Row>, b: Seq<Row>)
    requires a.to_multiset() == b.to_multiset(), group_caps(qg(lo, hi), a),
    ensures group_caps(qg(lo, hi), b),
{
    let g = qg(lo, hi);
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies #[trigger] gabs(g, b, k, j) <= i128_max() by {
        lemma_acc_perm(g, a, b, k);
        lemma_gabs_j(lo, hi, a, k, j);
        lemma_gabs_j(lo, hi, b, k, j);
    }
}

/// `gabs` of aggregate `j` of `qg` does not depend on `j` (one argument for every aggregate).
pub proof fn lemma_gabs_j(lo: int, hi: int, xs: Seq<Row>, k: Row, j: int)
    ensures gabs(qg(lo, hi), xs, k, j) == gabs(qg(lo, hi), xs, k, 0),
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_gabs_j(lo, hi, xs.drop_last(), k, j);
    }
}

/// Group caps from a bound `b` on every qualifying row's argument: each group's absolute mass is at most
/// `xs.len() * b`.
pub proof fn lemma_caps_bound(lo: int, hi: int, xs: Seq<Row>, b: int)
    requires
        b >= 0,
        xs.len() * b <= i128_max(),
        forall|j: int| 0 <= j < xs.len() && qual_of(lo, hi, #[trigger] xs[j]) ==> abs(rev_of(xs[j])) <= b,
    ensures group_caps(qg(lo, hi), xs),
{
    let g = qg(lo, hi);
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies #[trigger] gabs(g, xs, k, j) <= i128_max() by {
        lemma_gabs_j(lo, hi, xs, k, j);
        lemma_abs_le(lo, hi, xs, k, b);
        assert(gabs(g, xs, k, 0) <= xs.len() * b);
    }
}

/// The absolute mass of a group is at most `xs.len() * b`.
proof fn lemma_abs_le(lo: int, hi: int, xs: Seq<Row>, k: Row, b: int)
    requires
        b >= 0,
        forall|j: int| 0 <= j < xs.len() && qual_of(lo, hi, #[trigger] xs[j]) ==> abs(rev_of(xs[j])) <= b,
    ensures gabs(qg(lo, hi), xs, k, 0) <= xs.len() * b,
    decreases xs.len(),
{
    if xs.len() > 0 {
        let xi = xs.drop_last();
        assert forall|j: int| 0 <= j < xi.len() && qual_of(lo, hi, #[trigger] xi[j]) implies abs(rev_of(xi[j])) <= b by {
            assert(xi[j] == xs[j]);
        }
        lemma_abs_le(lo, hi, xi, k, b);
        assert(xs[xs.len() - 1] == xs.last());
        assert(xi.len() * b + b == xs.len() * b) by (nonlinear_arith) requires xi.len() + 1 == xs.len();
    }
}

// ------------------------------------------------------------------------------------------------ outcomes

/// The body is `res_rows` of the supplier rows (inside the SUM capacity condition).
pub proof fn lemma_res_body(db: Database, ps: Seq<Literal>, hi: int, m: int)
    requires
        db.schema == schema_spec(), db_wf(db),
        param_typed(ps),
        hi_ok(lo_of(ps), hi),
        group_caps(qg(lo_of(ps), hi), xd(db)),
        is_max(qg(lo_of(ps), hi), xd(db), m) || no_groups(qg(lo_of(ps), hi), xd(db)),
    ensures
        denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(res_rows(db.tables[5], qg(lo_of(ps), hi), xd(db), m)),
{
    let g = qg(lo_of(ps), hi);
    lemma_body(db, ps, hi);
    lemma_shape(ps);
    if is_max(g, xd(db), m) {
        lemma_body_res(db.tables[5], g, xd(db), m);
    } else {
        lemma_body_none(db.tables[5], g, xd(db), max_val(g, xd(db)), m);
    }
}

/// The sort by `s_suppkey` of the body's rows is an allowed output.
pub proof fn lemma_rows_ok(db: Database, ps: Seq<Literal>, rows: Seq<Row>)
    requires
        db.schema == schema_spec(), db_wf(db),
        param_typed(ps),
        denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(rows),
    ensures
        ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(sort_rows(order_keys(), rows))),
{
    let oq = query_spec_at(ps);
    lemma_query_wf_at(ps);
    lemma_shape(ps);
    lemma_denote_top_ok(db, oq);
    lemma_slice_all(sort_rows(oq.keys, rows));
}

} // verus!
