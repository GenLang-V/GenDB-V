//! The outer GROUP BY (`c_count`, `COUNT(*)`) and the answer rows.
//!
//! The outer GROUP BY over the inner rows `r1` (`(c_custkey, c_count)` per customer) is the toolkit's grouped normal
//! form `g2` (every row qualifies, key `c_count`, one COUNT): its group of `[c_count = v]` has `hcount(v)` rows
//! (`lemma_gcount`), and the statement's body is `result_rows(g2, r1)` (`lemma_outer`). The answer is built from a
//! histogram `hist` (`hist[v] = hcount(v)`, every `c_count` below its length, `hist_facts`): one row
//! `(v, hist[v])` per non-empty count, inserted in `custdist DESC, c_count DESC` order (`answer_rows`), which
//! `lemma_answer` proves an allowed output of the statement.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::equality::*;
use crate::spec::order::*;
use crate::spec::limits::*;
use crate::exec::value::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::query::{query_spec_at, param_domain};
use crate::bridge::collect::*;
use crate::link::query::*;
use crate::link::outcome::{lemma_view_rows_push, lemma_view_rows};
use crate::link::expr::lemma_compare_int;
use crate::agent::common::groups::lemma_int_keys;
use crate::agent::tables::*;
use crate::agent::normal::*;
use crate::agent::denote::*;
use crate::agent::inner::*;

verus! {

// ------------------------------------------------------------------------------------------------ the outer GROUP BY

/// The outer GROUP BY as a grouped normal form over the inner rows.
pub open spec fn g2() -> QuerySpec {
    QuerySpec {
        qual: |r: Row| true,
        key: |r: Row| seq![r[1]],
        arg: |j: int, r: Row| 0int,
        aggs: seq![AggKind::Count],
        outs: seq![0nat, 1nat],
        grouped: true,
    }
}

/// The inner rows' columns (both).
pub open spec fn r1_cols() -> Seq<nat> { seq![0nat, 1nat] }

/// The inner GROUP BY is its rows when no `c_count` leaves int8.
pub proof fn lemma_inner_ok(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires
        bound_db(sv, db), param_domain(ps), n_c(sv) == 0 || likes_ok(sv, pat_of(ps)),
        forall|i: int| 0 <= i < n_c(sv) ==> #[trigger] ccnt(sv, pat_of(ps), i) <= i64::MAX,
    ensures eval_query(db, Seq::empty(), q_inner(ps)) == Ok::<Relation, SqlError>(r1(sv, pat_of(ps))),
{
    let pat = pat_of(ps);
    lemma_inner(sv, db, ps);
    let irs = inner_results(sv, pat);
    let rows = r1(sv, pat);
    assert forall|i: int| 0 <= i < irs.len() implies #[trigger] irs[i] == Ok::<Row, SqlError>(rows[i]) by {
        assert(int_in_range(IntKind::Int8, ccnt(sv, pat, i) as int));
    }
    lemma_collect_all(irs, rows);
}

/// Projecting the inner rows on both columns keeps them.
proof fn lemma_r1_proj(sv: StoresView, pat: Seq<u8>)
    ensures proj_all(r1(sv, pat), r1_cols()) == r1(sv, pat),
{
    let rows = r1(sv, pat);
    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] proj_all(rows, r1_cols())[i] == rows[i] by {
        assert(proj(rows[i], r1_cols()) =~= rows[i]);
    }
    assert(proj_all(rows, r1_cols()) =~= rows);
}

/// The group of `[v]` over the inner rows of the customers below `n` has `hcount(v, n)` rows; a non-empty group's
/// key is some customer's `[c_count]`.
pub proof fn lemma_gcount(sv: StoresView, pat: Seq<u8>, v: int, n: int)
    requires 0 <= n <= n_c(sv),
    ensures gcount(g2(), r1(sv, pat).subrange(0, n), seq![Val::Int(v)]) == hcount(sv, pat, v, n),
    decreases n,
{
    if n > 0 {
        let rows = r1(sv, pat).subrange(0, n);
        assert(rows.drop_last() =~= r1(sv, pat).subrange(0, n - 1));
        lemma_gcount(sv, pat, v, n - 1);
        let last = rows.last();
        assert(last == seq![Val::Int(cck(sv)[n - 1] as int), Val::Int(ccnt(sv, pat, n - 1) as int)]);
        assert((g2().key)(last) == seq![Val::Int(ccnt(sv, pat, n - 1) as int)]);
        assert((seq![Val::Int(ccnt(sv, pat, n - 1) as int)] == seq![Val::Int(v)]) == (ccnt(sv, pat, n - 1) == v)) by {
            if seq![Val::Int(ccnt(sv, pat, n - 1) as int)] == seq![Val::Int(v)] {
                assert(seq![Val::Int(ccnt(sv, pat, n - 1) as int)][0] == seq![Val::Int(v)][0]);
            }
        }
    } else {
        assert(r1(sv, pat).subrange(0, 0).len() == 0);
    }
}

/// A non-empty group of the inner rows has a customer's `[c_count]` as key.
pub proof fn lemma_gcount_witness(sv: StoresView, pat: Seq<u8>, k: Row)
    requires gcount(g2(), r1(sv, pat), k) > 0,
    ensures exists|i: int| 0 <= i < n_c(sv) && k == seq![Val::Int(#[trigger] ccnt(sv, pat, i) as int)],
{
    let rows = r1(sv, pat);
    lemma_count_witness(g2(), rows, k);
    let m = choose|m: int| 0 <= m < rows.len() && #[trigger] hit(g2(), rows[m], k);
    assert(k == seq![rows[m][1]]);
}

/// The outer GROUP BY's domain: every group count fits int8.
pub open spec fn outer_caps(sv: StoresView, pat: Seq<u8>) -> bool {
    group_caps(g2(), r1(sv, pat))
}

/// The outer GROUP BY's key and COUNT(*) argument agree with `g2` on every inner row.
proof fn lemma_outer_agree(sv: StoresView, db: Database, pat: Seq<u8>)
    ensures
        keys_agree(db, r1(sv, pat), r1_cols(), q_outer_keys(), g2()),
        args_agree(db, r1(sv, pat), r1_cols(), q_outer_aggs(), g2()),
        aggs_match(q_outer_aggs(), g2()),
{
    let rows = r1(sv, pat);
    let cols = r1_cols();
    let g = g2();
    lemma_r1_proj(sv, pat);
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], cols)) implies
        eval_exprs(db, rows[i], q_outer_keys()) == Ok::<Row, SqlError>((g.key)(proj(rows[i], cols))) by {
        lemma_eval_cols(db, rows[i], seq![1nat]);
        assert(col_exprs(seq![1nat]) =~= q_outer_keys());
        assert(select(rows[i], seq![1nat]) =~= seq![rows[i][1]]);
        assert(proj(rows[i], cols) == proj_all(rows, cols)[i]);
    }
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], cols)) implies
        agg_args(db, rows[i], q_outer_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[i], cols))) by {
        lemma_agg_arg_results_index(db, rows[i], q_outer_aggs());
        assert(arg_vals(g, proj(rows[i], cols)) =~= seq![Val::Null]);
        lemma_collect_all(agg_arg_results(db, rows[i], q_outer_aggs()), seq![Val::Null]);
    }
}

/// The outer GROUP BY's keys (`[c_count]`) are exact.
proof fn lemma_outer_exact(sv: StoresView, pat: Seq<u8>)
    ensures keys_exact(g2(), proj_all(r1(sv, pat), r1_cols())),
{
    let g = g2();
    lemma_r1_proj(sv, pat);
    let xs = r1(sv, pat);
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        lemma_int_keys(ccnt(sv, pat, a) as int, ccnt(sv, pat, b) as int);
        assert((g.key)(xs[a]) == seq![Val::Int(ccnt(sv, pat, a) as int)]);
        assert((g.key)(xs[b]) == seq![Val::Int(ccnt(sv, pat, b) as int)]);
        if seq![Val::Int(ccnt(sv, pat, a) as int)] == seq![Val::Int(ccnt(sv, pat, b) as int)] {
            assert(seq![Val::Int(ccnt(sv, pat, a) as int)][0] == seq![Val::Int(ccnt(sv, pat, b) as int)][0]);
        }
    }
}

/// The full rows of the groups are the output rows (`outs` selects both columns).
proof fn lemma_outer_rows(sv: StoresView, pat: Seq<u8>)
    ensures ({
        let xs = proj_all(r1(sv, pat), r1_cols());
        gkeys(g2(), xs).map_values(|k: Row| full_row(g2(), xs, k)) == result_rows(g2(), r1(sv, pat))
    }),
{
    let g = g2();
    lemma_r1_proj(sv, pat);
    let xs = r1(sv, pat);
    let ks = gkeys(g, xs);
    assert forall|t: int| 0 <= t < ks.len() implies #[trigger] select(full_row(g, xs, ks[t]), g.outs) == full_row(g, xs, ks[t]) by {
        lemma_gkeys_witness(g, xs, ks[t]);
        let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], ks[t]);
        assert(ks[t].len() == 1);
        assert(select(full_row(g, xs, ks[t]), g.outs) =~= full_row(g, xs, ks[t]));
    }
    assert(ks.map_values(|k: Row| full_row(g, xs, k)) =~= result_rows(g, xs));
}

/// The statement's body is the outer normal form's rows over the inner rows.
pub proof fn lemma_outer(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires
        bound_db(sv, db), param_domain(ps), n_c(sv) == 0 || likes_ok(sv, pat_of(ps)),
        forall|i: int| 0 <= i < n_c(sv) ==> #[trigger] ccnt(sv, pat_of(ps), i) <= i64::MAX,
        outer_caps(sv, pat_of(ps)),
    ensures denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(result_rows(g2(), r1(sv, pat_of(ps)))),
{
    let pat = pat_of(ps);
    let rows = r1(sv, pat);
    let g = g2();
    lemma_query_shape(ps);
    lemma_inner_ok(sv, db, ps);
    lemma_r1_proj(sv, pat);
    lemma_keep_all(rows, qual_truths(g, proj_all(rows, r1_cols())));
    lemma_outer_agree(sv, db, pat);
    lemma_outer_exact(sv, pat);
    lemma_group_query(db, rows, r1_cols(), q_inner(ps), q_outer_keys(), q_outer_aggs(), g);
    lemma_outer_rows(sv, pat);
}

// ------------------------------------------------------------------------------------------------ the answer rows

/// The histogram's facts: `hist[v]` customers have `c_count == v`, every `c_count` is below its length, and every
/// entry fits int8.
pub open spec fn hist_facts(sv: StoresView, pat: Seq<u8>, hist: Seq<u64>) -> bool {
    &&& forall|v: int| 0 <= v < hist.len() ==> #[trigger] hist[v] as int == hcount(sv, pat, v, n_c(sv))
    &&& forall|i: int| 0 <= i < n_c(sv) ==> #[trigger] ccnt(sv, pat, i) < hist.len()
    &&& forall|v: int| 0 <= v < hist.len() ==> #[trigger] hist[v] <= i64::MAX
    &&& hist.len() <= i64::MAX as int + 1
}

/// `(count, customers)` pairs: `a` comes before `b` in `custdist DESC, c_count DESC` order.
pub open spec fn before(a: (u64, u64), b: (u64, u64)) -> bool {
    a.1 > b.1 || (a.1 == b.1 && a.0 > b.0)
}

/// A pair's answer row.
pub open spec fn pair_row(p: (u64, u64)) -> Row { seq![Val::Int(p.0 as int), Val::Int(p.1 as int)] }

/// The pairs list: sorted, one per non-empty count below `upto`, each with its histogram entry.
pub open spec fn pairs_ok(hist: Seq<u64>, ps: Seq<(u64, u64)>, upto: int) -> bool {
    &&& forall|a: int, b: int| 0 <= a < b < ps.len() ==> before(#[trigger] ps[a], #[trigger] ps[b])
    &&& forall|t: int| 0 <= t < ps.len() ==> (#[trigger] ps[t]).0 < upto && ps[t].1 == hist[ps[t].0 as int] && ps[t].1 > 0
    &&& forall|w: int| 0 <= w < upto && hist[w] > 0 ==> exists|t: int| 0 <= t < ps.len() && (#[trigger] ps[t]).0 == w
}

/// Inserting a pair with a new count at its place keeps the list sorted.
pub proof fn lemma_insert_sorted(ps: Seq<(u64, u64)>, x: (u64, u64), t: int)
    requires
        0 <= t <= ps.len(),
        forall|a: int, b: int| 0 <= a < b < ps.len() ==> before(#[trigger] ps[a], #[trigger] ps[b]),
        forall|s: int| 0 <= s < ps.len() ==> (#[trigger] ps[s]).0 != x.0,
        forall|s: int| 0 <= s < t ==> !before(x, #[trigger] ps[s]),
        t < ps.len() ==> before(x, ps[t]),
    ensures forall|a: int, b: int| 0 <= a < b < ps.insert(t, x).len() ==> before(#[trigger] ps.insert(t, x)[a], #[trigger] ps.insert(t, x)[b]),
{
    let q = ps.insert(t, x);
    assert forall|a: int, b: int| 0 <= a < b < q.len() implies before(#[trigger] q[a], #[trigger] q[b]) by {
        if b < t {
            assert(q[a] == ps[a] && q[b] == ps[b]);
        } else if b == t {
            assert(q[b] == x && q[a] == ps[a]);
            assert(!before(x, ps[a]));
        } else if a == t {
            assert(q[a] == x && q[b] == ps[b - 1]);
            if b - 1 > t { assert(before(ps[t], ps[b - 1])); }
        } else if a < t {
            assert(q[a] == ps[a] && q[b] == ps[b - 1]);
        } else {
            assert(q[a] == ps[a - 1] && q[b] == ps[b - 1]);
        }
    }
}

/// Inserting the pair of count `v` (not listed yet, `hist[v] > 0`) at its place.
fn insert_pair(ps: &mut Vec<(u64, u64)>, hist: &Vec<u64>, v: usize)
    requires v < hist@.len() <= u64::MAX, hist@[v as int] > 0, pairs_ok(hist@, old(ps)@, v as int),
    ensures pairs_ok(hist@, final(ps)@, v + 1),
{
    let h = hist[v];
    let x = (v as u64, h);
    let mut t: usize = 0;
    while t < ps.len() && !(h > ps[t].1 || (h == ps[t].1 && (v as u64) > ps[t].0))
        invariant
            t <= ps@.len(), pairs_ok(hist@, ps@, v as int), x == (v as u64, h), ps@ == old(ps)@,
            forall|s: int| 0 <= s < t ==> !before(x, #[trigger] ps@[s]),
        decreases ps@.len() - t,
    {
        t = t + 1;
    }
    let ghost p0 = ps@;
    proof {
        assert forall|s: int| 0 <= s < p0.len() implies (#[trigger] p0[s]).0 != x.0 by {}
        lemma_insert_sorted(p0, x, t as int);
    }
    ps.insert(t, x);
    proof {
        let q = ps@;
        assert(q == p0.insert(t as int, x));
        assert forall|s: int| 0 <= s < q.len() implies (#[trigger] q[s]).0 < v + 1 && q[s].1 == hist@[q[s].0 as int] && q[s].1 > 0 by {
            if s < t { assert(q[s] == p0[s]); } else if s > t { assert(q[s] == p0[s - 1]); }
        }
        assert forall|w: int| 0 <= w < v + 1 && hist@[w] > 0 implies exists|s: int| 0 <= s < q.len() && (#[trigger] q[s]).0 == w by {
            if w == v {
                assert(q[t as int].0 == w);
            } else {
                let s = choose|s: int| 0 <= s < p0.len() && (#[trigger] p0[s]).0 == w;
                if s < t { assert(q[s] == p0[s]); } else { assert(q[s + 1] == p0[s]); }
            }
        }
    }
}

/// The pairs of the non-empty counts of `hist`, sorted by `custdist DESC, c_count DESC`.
pub fn sorted_pairs(hist: &Vec<u64>) -> (ps: Vec<(u64, u64)>)
    requires hist@.len() <= u64::MAX,
    ensures pairs_ok(hist@, ps@, hist@.len() as int),
{
    let n = hist.len();
    let mut ps: Vec<(u64, u64)> = Vec::new();
    let mut v: usize = 0;
    while v < n
        invariant v <= n, n == hist@.len(), n <= u64::MAX, pairs_ok(hist@, ps@, v as int),
        decreases n - v,
    {
        if hist[v] > 0 {
            insert_pair(&mut ps, hist, v);
        } else {
            proof {
                assert forall|w: int| 0 <= w < v + 1 && hist@[w] > 0 implies exists|s: int| 0 <= s < ps@.len() && (#[trigger] ps@[s]).0 == w by {
                    assert(w < v);
                }
            }
        }
        v = v + 1;
    }
    ps
}

/// The answer rows of sorted pairs.
pub fn rows_of_pairs(ps: &Vec<(u64, u64)>) -> (rows: Vec<Vec<EVal>>)
    requires forall|t: int| 0 <= t < ps@.len() ==> (#[trigger] ps@[t]).0 <= i64::MAX && ps@[t].1 <= i64::MAX,
    ensures
        rows@.len() == ps@.len(),
        forall|t: int| 0 <= t < ps@.len() ==> #[trigger] view_rows(rows@)[t] == pair_row(ps@[t]),
{
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let mut k: usize = 0;
    while k < ps.len()
        invariant
            k <= ps@.len(), rows@.len() == k,
            forall|t: int| 0 <= t < ps@.len() ==> (#[trigger] ps@[t]).0 <= i64::MAX && ps@[t].1 <= i64::MAX,
            forall|t: int| 0 <= t < k ==> #[trigger] view_rows(rows@)[t] == pair_row(ps@[t]),
        decreases ps@.len() - k,
    {
        let (cv, h) = ps[k];
        let mut row: Vec<EVal> = Vec::new();
        row.push(EVal::Int(cv as i64));
        row.push(EVal::Int(h as i64));
        let ghost r0 = rows@;
        rows.push(row);
        proof {
            assert(view_row(row@) =~= pair_row(ps@[k as int]));
            lemma_view_rows_push(r0, row);
            assert forall|t: int| 0 <= t < k + 1 implies #[trigger] view_rows(rows@)[t] == pair_row(ps@[t]) by {
                if t < k { assert(view_rows(rows@)[t] == view_rows(r0)[t]); }
            }
        }
        k = k + 1;
    }
    rows
}

/// The order of two answer rows: `a` before `b` gives a negative comparison.
proof fn lemma_keys_cmp(a: (u64, u64), b: (u64, u64))
    requires before(a, b),
    ensures keys_cmp(q_order(), pair_row(a), pair_row(b)) < 0,
{
    let keys = q_order();
    let (ra, rb) = (pair_row(a), pair_row(b));
    lemma_compare_int(a.1 as int, b.1 as int);
    lemma_compare_int(a.0 as int, b.0 as int);
    let k0 = keys[0];
    let k1 = keys[1];
    assert(key_cmp(k0, ra, rb) == -sign(a.1 as int - b.1 as int));
    assert(key_cmp(k1, ra, rb) == -sign(a.0 as int - b.0 as int));
    let rest = keys.drop_first();
    assert(rest =~= seq![k1]);
    assert(rest.drop_first() =~= Seq::<OrderKey>::empty());
    assert(keys_cmp(rest.drop_first(), ra, rb) == 0);
    assert(keys_cmp(rest, ra, rb) == if key_cmp(k1, ra, rb) != 0 { key_cmp(k1, ra, rb) } else { 0 });
    assert(keys_cmp(keys, ra, rb) == if key_cmp(k0, ra, rb) != 0 { key_cmp(k0, ra, rb) } else { keys_cmp(rest, ra, rb) });
}

/// Sorted pairs give rows sorted by `custdist DESC, c_count DESC`.
proof fn lemma_rows_sorted(ps: Seq<(u64, u64)>, full: Seq<Row>)
    requires
        full.len() == ps.len(),
        forall|t: int| 0 <= t < ps.len() ==> #[trigger] full[t] == pair_row(ps[t]),
        forall|a: int, b: int| 0 <= a < b < ps.len() ==> before(#[trigger] ps[a], #[trigger] ps[b]),
    ensures sorted_by(q_order(), full),
{
    assert forall|i: int, j: int| 0 <= i < j < full.len() implies keys_cmp(q_order(), #[trigger] full[i], #[trigger] full[j]) <= 0 by {
        lemma_keys_cmp(ps[i], ps[j]);
    }
}

/// Some pair has count `v`.
pub open spec fn has_count(ps: Seq<(u64, u64)>, v: int) -> bool {
    exists|t: int| 0 <= t < ps.len() && (#[trigger] ps[t]).0 as int == v
}

/// Sorted pairs `(c_count, custdist)`: every pair is a non-empty count of the customers with its number of customers,
/// every customer's count has a pair, both fit int8.
pub open spec fn pairs_facts(sv: StoresView, pat: Seq<u8>, ps: Seq<(u64, u64)>) -> bool {
    &&& forall|a: int, b: int| 0 <= a < b < ps.len() ==> before(#[trigger] ps[a], #[trigger] ps[b])
    &&& forall|t: int| 0 <= t < ps.len() ==> (#[trigger] ps[t]).1 as int == hcount(sv, pat, ps[t].0 as int, n_c(sv))
            && ps[t].1 > 0 && ps[t].0 <= i64::MAX && ps[t].1 <= i64::MAX
    &&& forall|i: int| 0 <= i < n_c(sv) ==> has_count(ps, #[trigger] ccnt(sv, pat, i) as int)
}

/// The sorted pairs of a histogram have the pairs' facts.
proof fn lemma_hist_pairs(sv: StoresView, pat: Seq<u8>, hist: Seq<u64>, ps: Seq<(u64, u64)>)
    requires hist_facts(sv, pat, hist), pairs_ok(hist, ps, hist.len() as int),
    ensures pairs_facts(sv, pat, ps),
{
    assert forall|i: int| 0 <= i < n_c(sv) implies has_count(ps, #[trigger] ccnt(sv, pat, i) as int) by {
        let v = ccnt(sv, pat, i) as int;
        assert(v < hist.len());
        lemma_hcount_pos(sv, pat, i, n_c(sv));
        assert(hist[v] > 0);
        let t = choose|t: int| 0 <= t < ps.len() && (#[trigger] ps[t]).0 == v;
        assert(ps[t].0 as int == v);
    }
}

/// A customer below `n` makes the count of its `c_count` positive.
pub proof fn lemma_hcount_pos(sv: StoresView, pat: Seq<u8>, i: int, n: int)
    requires 0 <= i < n,
    ensures hcount(sv, pat, ccnt(sv, pat, i) as int, n) > 0,
    decreases n,
{
    if i < n - 1 {
        lemma_hcount_pos(sv, pat, i, n - 1);
    }
}

/// The answer rows built from sorted pairs are an allowed output of the statement.
pub proof fn lemma_answer(sv: StoresView, db: Database, ps: Seq<Literal>, pairs: Seq<(u64, u64)>, full: Seq<Row>)
    requires
        bound_db(sv, db), param_domain(ps), n_c(sv) == 0 || likes_ok(sv, pat_of(ps)),
        pairs_facts(sv, pat_of(ps), pairs),
        full.len() == pairs.len(),
        forall|t: int| 0 <= t < pairs.len() ==> #[trigger] full[t] == pair_row(pairs[t]),
    ensures ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(full)),
{
    let pat = pat_of(ps);
    let rows = r1(sv, pat);
    let g = g2();
    assert(rows.subrange(0, n_c(sv)) =~= rows);
    // every c_count is some pair's count, so within int8
    assert forall|i: int| 0 <= i < n_c(sv) implies #[trigger] ccnt(sv, pat, i) <= i64::MAX by {
        assert(has_count(pairs, ccnt(sv, pat, i) as int));
        let t = choose|t: int| 0 <= t < pairs.len() && (#[trigger] pairs[t]).0 as int == ccnt(sv, pat, i);
    }
    // the groups: [v] has hcount(v) rows
    assert forall|k: Row, j: int| #![trigger gcount(g, rows, k), g.aggs[j]] 0 <= j < g.aggs.len() && g.aggs[j] is Count
        implies gcount(g, rows, k) <= int8_max() by {
        if gcount(g, rows, k) > 0 {
            lemma_gcount_witness(sv, pat, k);
            let i = choose|i: int| 0 <= i < n_c(sv) && k == seq![Val::Int(#[trigger] ccnt(sv, pat, i) as int)];
            let v = ccnt(sv, pat, i) as int;
            lemma_gcount(sv, pat, v, n_c(sv));
            assert(has_count(pairs, ccnt(sv, pat, i) as int));
            let t = choose|t: int| 0 <= t < pairs.len() && (#[trigger] pairs[t]).0 as int == ccnt(sv, pat, i);
        }
    }
    assert(outer_caps(sv, pat)) by {
        assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies #[trigger] gabs(g, rows, k, j) <= crate::link::expr::i128_max() by {}
        assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && g.aggs[j] is Avg implies
            crate::spec::fns::div::num_div_fits(#[trigger] gsum(g, rows, k, j), g.aggs[j]->Avg_scale, gcount(g, rows, k) as int, 0) by {}
    }
    lemma_outer(sv, db, ps);
    // the keys of the answer rows are exactly the non-empty groups
    let ks = pairs.map_values(|p: (u64, u64)| seq![Val::Int(p.0 as int)]);
    assert(ks.no_duplicates()) by {
        assert forall|a: int, b: int| 0 <= a < ks.len() && 0 <= b < ks.len() && a != b implies ks[a] != ks[b] by {
            let (x, y) = if a < b { (a, b) } else { (b, a) };
            assert(before(pairs[x], pairs[y]));
            if ks[a] == ks[b] { assert(ks[a][0] == ks[b][0]); }
        }
    }
    assert forall|k: Row| #[trigger] ks.contains(k) <==> gcount(g, rows, k) > 0 by {
        if ks.contains(k) {
            let t = choose|t: int| 0 <= t < ks.len() && ks[t] == k;
            let v = pairs[t].0 as int;
            lemma_gcount(sv, pat, v, n_c(sv));
        }
        if gcount(g, rows, k) > 0 {
            lemma_gcount_witness(sv, pat, k);
            let i = choose|i: int| 0 <= i < n_c(sv) && k == seq![Val::Int(#[trigger] ccnt(sv, pat, i) as int)];
            assert(has_count(pairs, ccnt(sv, pat, i) as int));
            let t = choose|t: int| 0 <= t < pairs.len() && (#[trigger] pairs[t]).0 as int == ccnt(sv, pat, i);
            assert(ks[t] == k);
        }
    }
    assert forall|t: int| 0 <= t < full.len() implies #[trigger] full[t] == out_row(g, rows, ks[t]) by {
        let v = pairs[t].0 as int;
        lemma_gcount(sv, pat, v, n_c(sv));
        assert(out_row(g, rows, ks[t]) =~= pair_row(pairs[t]));
    }
    lemma_rows_sorted(pairs, full);
    lemma_result_from_keys(g, q_order(), 0, None, rows, ks, full);
    lemma_slice_all(full);
    lemma_query_shape(ps);
    lemma_ordered_link(db, query_spec_at(ps), g, rows, full);
}

/// The answer rows of sorted pairs: an allowed output of the statement for every database bound to the parts.
pub fn finish_pairs(pairs: &Vec<(u64, u64)>, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (rows: Vec<Vec<EVal>>)
    requires
        param_domain(ps), n_c(sv) == 0 || likes_ok(sv, pat_of(ps)), pairs_facts(sv, pat_of(ps), pairs@),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(view_rows(rows@))),
{
    let rows = rows_of_pairs(pairs);
    proof {
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies
            ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(view_rows(rows@))) by {
            lemma_view_rows(rows@);
            lemma_answer(sv, db, ps, pairs@, view_rows(rows@));
        }
    }
    rows
}

/// The answer rows of a histogram: an allowed output of the statement for every database bound to the parts.
pub fn finish_rows(hist: &Vec<u64>, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (rows: Vec<Vec<EVal>>)
    requires
        param_domain(ps), n_c(sv) == 0 || likes_ok(sv, pat_of(ps)), hist_facts(sv, pat_of(ps), hist@),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(view_rows(rows@))),
{
    let pairs = sorted_pairs(hist);
    proof { lemma_hist_pairs(sv, pat_of(ps), hist@, pairs@); }
    finish_pairs(&pairs, Ghost(sv), Ghost(ps))
}

} // verus!
