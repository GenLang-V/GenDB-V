//! The answers are allowed outcomes for every database bound to the stored parts.
//! - the scans' accumulators are the normal forms' (`lemma_count_a`: pass A is `g2`'s count and sum; `lemma_count_b`:
//!   pass B per first slot `k` is `gc`'s count and sum of the group `[ptext(k)]`; every group with a row is such a
//!   slot, `lemma_group_slot`);
//! - rows (`lemma_answer_rows`), error 22003 (`lemma_answer_overflow`) and `Capacity` (`lemma_answer_capacity`).
use vstd::prelude::*;
use crate::gendb_entry::{Answer, answer_meets, bound_db, outcome_ok};
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::runtime::QueryError;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::spec::scalar::*;
use crate::spec::text::lex_cmp;
use crate::spec::limits::*;
use crate::spec::fns::div::num_div_fits;
use crate::query::{param_domain, query_spec_at};
use crate::exec::value::*;
use crate::link::query::*;
use crate::link::expr::i128_max;
use super::common::sub2::*;
use super::model::*;
use super::scan::{post_b, lemma_gid_range};
use super::output::*;
use super::sql::*;
use super::group::*;
use super::errs::*;
use super::bind::*;

verus! {

// ------------------------------------------------------------------------------------------------ pass A

/// Pass A over the first `m` rows is `g2`'s count and sum over them.
pub proof fn lemma_count_a(v: Cv, db: Database, m: int)
    requires rows_match(v, db), 0 <= m <= v.n,
    ensures
        cnta(v, 0, m) == gcount(g2(v.ps), ctab(db).subrange(0, m), Seq::empty()),
        suma(v, 0, m) == gsum(g2(v.ps), ctab(db).subrange(0, m), Seq::empty(), 0),
    decreases m,
{
    let rows = ctab(db).subrange(0, m);
    if m == 0 {
        assert(rows =~= Seq::<Row>::empty());
    } else {
        lemma_count_a(v, db, m - 1);
        assert(rows.drop_last() =~= ctab(db).subrange(0, m - 1));
        assert(rows.last() == ctab(db)[m - 1]);
        assert(row_match(v, db, m - 1));
        assert(qa(v, m - 1) == sq(v.ps, ctab(db)[m - 1]));
    }
}

/// Pass A over all rows.
pub proof fn lemma_count_a_all(v: Cv, db: Database)
    requires rows_match(v, db),
    ensures
        cnta(v, 0, v.n) == gcount(g2(v.ps), ctab(db), Seq::empty()),
        suma(v, 0, v.n) == gsum(g2(v.ps), ctab(db), Seq::empty(), 0),
{
    lemma_count_a(v, db, v.n);
    assert(ctab(db).subrange(0, v.n) =~= ctab(db));
}

// ------------------------------------------------------------------------------------------------ pass B

/// One-column text keys are equal exactly when their texts are.
proof fn lemma_key_eq(a: Seq<u8>, b: Seq<u8>)
    ensures (seq![Val::Text(a)] == seq![Val::Text(b)]) == (a == b),
{
    if seq![Val::Text(a)] == seq![Val::Text(b)] {
        assert(seq![Val::Text(a)][0] == seq![Val::Text(b)][0]);
    }
}

/// Row `i` is a result row of group `k` exactly when it hits `gc`'s group `[ptext(k)]` (`k` a first slot).
proof fn lemma_hit_b(v: Cv, db: Database, avg: Val, k: int, i: int)
    requires rows_match(v, db), 0 <= i < v.n, 0 <= k < 7, first_occ(v.ps, k),
    ensures
        (qb(v, avg, i) && rgid(v, i) == k) == hit(gc(db, v.ps, avg), ctab(db)[i], seq![Val::Text(ptext(v.ps, k))]),
        racct(v, i) == cacct(ctab(db)[i]),
{
    let ps = v.ps;
    let r = ctab(db)[i];
    assert(row_match(v, db, i));
    let t = code(r);
    assert(rgid(v, i) == gid(ps, t));
    lemma_key_eq(t, ptext(ps, k));
    lemma_gid_range(ps, 0, t);
    if gid(ps, t) == k {
        assert(ptext(ps, k) == t);
    }
    if t == ptext(ps, k) {
        assert(gid(ps, t) == k);
    }
}

/// Pass B over the first `m` rows, group `k`, is `gc`'s count and sum of the group `[ptext(k)]`.
pub proof fn lemma_count_b(v: Cv, db: Database, avg: Val, k: int, m: int)
    requires rows_match(v, db), 0 <= m <= v.n, 0 <= k < 7, first_occ(v.ps, k),
    ensures
        cntb(v, avg, k, 0, m) == gcount(gc(db, v.ps, avg), ctab(db).subrange(0, m), seq![Val::Text(ptext(v.ps, k))]),
        sumb(v, avg, k, 0, m) == gsum(gc(db, v.ps, avg), ctab(db).subrange(0, m), seq![Val::Text(ptext(v.ps, k))], 1),
    decreases m,
{
    let rows = ctab(db).subrange(0, m);
    if m == 0 {
        assert(rows =~= Seq::<Row>::empty());
    } else {
        lemma_count_b(v, db, avg, k, m - 1);
        assert(rows.drop_last() =~= ctab(db).subrange(0, m - 1));
        assert(rows.last() == ctab(db)[m - 1]);
        lemma_hit_b(v, db, avg, k, m - 1);
    }
}

/// Pass B over all rows.
pub proof fn lemma_count_b_all(v: Cv, db: Database, avg: Val, k: int)
    requires rows_match(v, db), 0 <= k < 7, first_occ(v.ps, k),
    ensures
        cntb(v, avg, k, 0, v.n) == gcount(gc(db, v.ps, avg), ctab(db), seq![Val::Text(ptext(v.ps, k))]),
        sumb(v, avg, k, 0, v.n) == gsum(gc(db, v.ps, avg), ctab(db), seq![Val::Text(ptext(v.ps, k))], 1),
{
    lemma_count_b(v, db, avg, k, v.n);
    assert(ctab(db).subrange(0, v.n) =~= ctab(db));
}

/// A group of pass B with a row is a first slot.
pub proof fn lemma_cntb_first(v: Cv, avg: Val, k: int, lo: int, hi: int)
    requires cntb(v, avg, k, lo, hi) > 0,
    ensures 0 <= k < 7, first_occ(v.ps, k),
    decreases hi - lo,
{
    if hi > lo {
        if qb(v, avg, hi - 1) && rgid(v, hi - 1) == k {
            let t = sub2(rtext(v, hi - 1));
            lemma_gid_range(v.ps, 0, t);
            assert(ptext(v.ps, k) == t);
        } else {
            lemma_cntb_first(v, avg, k, lo, hi - 1);
        }
    }
}

/// Every group of `gc` with a row is the code of a first slot.
pub proof fn lemma_group_slot(db: Database, ps: Seq<Literal>, avg: Val, rows: Seq<Row>, kk: Row) -> (k: int)
    requires gcount(gc(db, ps, avg), rows, kk) > 0,
    ensures 0 <= k < 7, first_occ(ps, k), kk == seq![Val::Text(ptext(ps, k))],
{
    let g = gc(db, ps, avg);
    lemma_count_witness(g, rows, kk);
    let m = choose|m: int| 0 <= m < rows.len() && #[trigger] hit(g, rows[m], kk);
    let t = code(rows[m]);
    assert(mq(db, ps, avg, rows[m]));
    let k = gid(ps, t);
    lemma_gid_range(ps, 0, t);
    assert(ptext(ps, k) == t);
    k
}

// ------------------------------------------------------------------------------------------------ the subquery's domain

/// `g2` has the one (empty) key: every other key has no rows.
proof fn lemma_g2_other_key(ps: Seq<Literal>, rows: Seq<Row>, k: Row)
    requires k != Seq::<Val>::empty(),
    ensures gcount(g2(ps), rows, k) == 0,
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_g2_other_key(ps, rows.drop_last(), k);
    }
}

/// `group_caps` of the subquery: the absolute sums fit `i128`, and the AVG division is executable.
pub proof fn lemma_g2_caps(db: Database, ps: Seq<Literal>)
    requires
        db_ok(db),
        ctab(db).len() < 0x1_0000_0000_0000_0000,
        gcount(g2(ps), ctab(db), Seq::empty()) > 0 ==>
            num_div_fits(gsum(g2(ps), ctab(db), Seq::empty(), 0), 2, gcount(g2(ps), ctab(db), Seq::empty()) as int, 0),
    ensures group_caps(g2(ps), ctab(db)),
{
    let g = g2(ps);
    let rows = ctab(db);
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies #[trigger] gabs(g, rows, k, j) <= i128_max() by {
        assert forall|i: int| 0 <= i < rows.len() implies -acct_bound() < #[trigger] (g.arg)(j, rows[i]) < acct_bound() by {
            assert(crow_ok(rows[i]));
        }
        lemma_gabs_bound(g, rows, k, j);
        let n = rows.len() as int;
        assert(n * acct_bound() <= 0x1_0000_0000_0000_0000 * acct_bound()) by (nonlinear_arith)
            requires 0 <= n <= 0x1_0000_0000_0000_0000;
    }
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && g.aggs[j] is Avg implies
        num_div_fits(#[trigger] gsum(g, rows, k, j), g.aggs[j]->Avg_scale, gcount(g, rows, k) as int, 0) by {
        assert(j == 0);
        if k != Seq::<Val>::empty() {
            lemma_g2_other_key(ps, rows, k);
        }
    }
}

// ------------------------------------------------------------------------------------------------ answers

/// What the query knows for every bound database: the views describe it, and the subquery's value is `avg`.
pub open spec fn db_facts(v: Cv, avg: Val, db: Database) -> bool {
    &&& rows_match(v, db)
    &&& group_caps(g2(v.ps), ctab(db))
    &&& avg_val(db, v.ps) == avg
    &&& ctab(db).len() < 0x1_0000_0000_0000_0000
}

/// The keys of the output groups.
pub open spec fn okeys(ps: Seq<Literal>, ord: Seq<usize>) -> Seq<Row> {
    ord.map_values(|k: usize| seq![Val::Text(ptext(ps, k as int))])
}

/// An element of the group order is a first slot with a result row.
proof fn lemma_ord_mem(ps: Seq<Literal>, cnts: Seq<u64>, ord: Seq<usize>, i: int)
    requires order_ok(ps, cnts, ord), cnts.len() == 7, 0 <= i < ord.len(),
    ensures ord[i] < 7, first_occ(ps, ord[i] as int), cnts[ord[i] as int] > 0,
{
    let k = ord[i] as int;
    assert(ord[i] < 7);
    assert(ord.contains(ord[i]));
    assert(k as usize == ord[i]);
    assert(0 <= k < 7);
    let c = cnts[k];
    assert(ord.contains(k as usize) <==> first_occ(ps, k) && c > 0);
}

/// The ORDER BY comparison of two output rows is the bytewise order of their codes.
proof fn lemma_orow_cmp(ps: Seq<Literal>, a: int, c1: int, s1: int, b: int, c2: int, s2: int)
    ensures keys_cmp(order_keys(), orow(ps, a, c1, s1), orow(ps, b, c2, s2)) == lex_cmp(ptext(ps, a), ptext(ps, b)),
{
    let (r1, r2) = (orow(ps, a, c1, s1), orow(ps, b, c2, s2));
    let keys = order_keys();
    let ok = keys[0];
    assert(ok.col == 0 && !ok.desc);
    assert(r1.len() == 3 && r2.len() == 3);
    assert(r1[0] == Val::Text(ptext(ps, a)));
    assert(r2[0] == Val::Text(ptext(ps, b)));
    assert(compare(r1[0], r2[0]) == Some(lex_cmp(ptext(ps, a), ptext(ps, b))));
    assert(key_cmp(ok, r1, r2) == lex_cmp(ptext(ps, a), ptext(ps, b)));
    assert(keys.drop_first() =~= Seq::<OrderKey>::empty());
    assert(keys_cmp(Seq::<OrderKey>::empty(), r1, r2) == 0);
    assert(keys_cmp(keys, r1, r2) == key_cmp(ok, r1, r2));
}

/// The facts of the exec results the answer lemmas read.
pub open spec fn exec_ok(v: Cv, avg: Val, cnts: Seq<u64>, sums: Seq<i128>, ord: Seq<usize>) -> bool {
    &&& ps_ok(v.ps)
    &&& avg is Null || avg is Num
    &&& post_b(v, avg, 0, v.n, cnts, sums)
    &&& forall|k: int| 0 <= k < 7 ==> #[trigger] cnts[k] <= i64::MAX
    &&& order_ok(v.ps, cnts, ord)
}

/// Every group count of `gc` fits int8.
proof fn lemma_counts_fit(v: Cv, avg: Val, db: Database, cnts: Seq<u64>, sums: Seq<i128>, ord: Seq<usize>)
    requires db_facts(v, avg, db), exec_ok(v, avg, cnts, sums, ord),
    ensures forall|kk: Row| #[trigger] gcount(gc(db, v.ps, avg), ctab(db), kk) <= int8_max(),
{
    let (ps, rows, g) = (v.ps, ctab(db), gc(db, v.ps, avg));
    assert forall|kk: Row| #[trigger] gcount(g, rows, kk) <= int8_max() by {
        if gcount(g, rows, kk) > 0 {
            let k = lemma_group_slot(db, ps, avg, rows, kk);
            lemma_count_b_all(v, db, avg, k);
            assert(cnts[k] == cntb(v, avg, k, 0, v.n));
        }
    }
}

/// The output keys are distinct and are exactly the groups with rows.
proof fn lemma_okeys(v: Cv, avg: Val, db: Database, cnts: Seq<u64>, sums: Seq<i128>, ord: Seq<usize>)
    requires db_facts(v, avg, db), exec_ok(v, avg, cnts, sums, ord),
    ensures
        okeys(v.ps, ord).no_duplicates(),
        forall|kk: Row| #[trigger] okeys(v.ps, ord).contains(kk) <==> gcount(gc(db, v.ps, avg), ctab(db), kk) > 0,
{
    let (ps, rows, g) = (v.ps, ctab(db), gc(db, v.ps, avg));
    let ks = okeys(ps, ord);
    assert forall|i: int, j: int| 0 <= i < ks.len() && 0 <= j < ks.len() && i != j implies ks[i] != ks[j] by {
        let (a, b) = (ord[i] as int, ord[j] as int);
        lemma_ord_mem(ps, cnts, ord, i);
        lemma_ord_mem(ps, cnts, ord, j);
        lemma_key_eq(ptext(ps, a), ptext(ps, b));
        if ptext(ps, a) == ptext(ps, b) {
            assert(a == b);
        }
    }
    assert forall|kk: Row| #[trigger] ks.contains(kk) <==> gcount(g, rows, kk) > 0 by {
        if ks.contains(kk) {
            let i = choose|i: int| 0 <= i < ks.len() && ks[i] == kk;
            let k = ord[i] as int;
            lemma_ord_mem(ps, cnts, ord, i);
            lemma_count_b_all(v, db, avg, k);
        }
        if gcount(g, rows, kk) > 0 {
            let k = lemma_group_slot(db, ps, avg, rows, kk);
            lemma_count_b_all(v, db, avg, k);
            assert(cnts[k] > 0);
            assert(ord.contains(k as usize) <==> first_occ(ps, k) && cnts[k] > 0);
            let i = choose|i: int| 0 <= i < ord.len() && ord[i] == k as usize;
            assert(ks[i] == kk);
        }
    }
}

/// Each output row is its group's normal-form row.
proof fn lemma_out_rows(v: Cv, avg: Val, db: Database, cnts: Seq<u64>, sums: Seq<i128>, ord: Seq<usize>, out: Seq<Row>)
    requires
        db_facts(v, avg, db), exec_ok(v, avg, cnts, sums, ord),
        out == ord.map_values(|k: usize| orow(v.ps, k as int, cnts[k as int] as int, sums[k as int] as int)),
    ensures
        out.len() == okeys(v.ps, ord).len(),
        forall|i: int| 0 <= i < out.len() ==> #[trigger] out[i] == out_row(gc(db, v.ps, avg), ctab(db), okeys(v.ps, ord)[i]),
{
    let (ps, rows, g) = (v.ps, ctab(db), gc(db, v.ps, avg));
    let ks = okeys(ps, ord);
    assert forall|i: int| 0 <= i < out.len() implies #[trigger] out[i] == out_row(g, rows, ks[i]) by {
        lemma_out_row(v, avg, db, cnts, sums, ord, out, i);
    }
}

/// Output row `i` is its group's normal-form row.
proof fn lemma_out_row(v: Cv, avg: Val, db: Database, cnts: Seq<u64>, sums: Seq<i128>, ord: Seq<usize>, out: Seq<Row>, i: int)
    requires
        db_facts(v, avg, db), exec_ok(v, avg, cnts, sums, ord),
        out == ord.map_values(|k: usize| orow(v.ps, k as int, cnts[k as int] as int, sums[k as int] as int)),
        0 <= i < out.len(),
    ensures out[i] == out_row(gc(db, v.ps, avg), ctab(db), okeys(v.ps, ord)[i]),
{
    let (ps, rows, g) = (v.ps, ctab(db), gc(db, v.ps, avg));
    let k = ord[i] as int;
    lemma_ord_mem(ps, cnts, ord, i);
    lemma_count_b_all(v, db, avg, k);
    let kk = okeys(ps, ord)[i];
    assert(kk == seq![Val::Text(ptext(ps, k))]);
    assert(cnts[k] == gcount(g, rows, kk));
    assert(sums[k] == gsum(g, rows, kk, 1));
    let f = full_row(g, rows, kk);
    assert(f.len() == 3);
    lemma_select_identity(f, g.outs);
    assert(out[i] == orow(ps, k, cnts[k] as int, sums[k] as int));
    assert(out[i] =~= f);
}

/// The output rows are in ORDER BY order.
proof fn lemma_out_sorted(ps: Seq<Literal>, cnts: Seq<u64>, sums: Seq<i128>, ord: Seq<usize>, out: Seq<Row>)
    requires
        order_ok(ps, cnts, ord),
        out == ord.map_values(|k: usize| orow(ps, k as int, cnts[k as int] as int, sums[k as int] as int)),
    ensures sorted_by(order_keys(), out),
{
    assert forall|i: int, j: int| 0 <= i < j < out.len() implies keys_cmp(order_keys(), #[trigger] out[i], #[trigger] out[j]) <= 0 by {
        let (a, b) = (ord[i] as int, ord[j] as int);
        assert(lex_cmp(ptext(ps, a), ptext(ps, b)) <= 0);
        lemma_orow_cmp(ps, a, cnts[a] as int, sums[a] as int, b, cnts[b] as int, sums[b] as int);
    }
}

/// The output rows are an allowed outcome on one bound database.
proof fn lemma_answer_db(v: Cv, avg: Val, db: Database, cnts: Seq<u64>, sums: Seq<i128>, ord: Seq<usize>, out: Seq<Row>)
    requires
        db_facts(v, avg, db), exec_ok(v, avg, cnts, sums, ord),
        out == ord.map_values(|k: usize| orow(v.ps, k as int, cnts[k as int] as int, sums[k as int] as int)),
    ensures ordered_ok(db, query_spec_at(v.ps), Ok::<Relation, SqlError>(out)),
{
    let (ps, rows, g) = (v.ps, ctab(db), gc(db, v.ps, avg));
    lemma_counts_fit(v, avg, db, cnts, sums, ord);
    lemma_body(db, ps);
    lemma_okeys(v, avg, db, cnts, sums, ord);
    lemma_out_rows(v, avg, db, cnts, sums, ord, out);
    lemma_out_sorted(ps, cnts, sums, ord, out);
    lemma_result_from_keys(g, order_keys(), 0, None, rows, okeys(ps, ord), out);
    lemma_slice_all(out);
    lemma_statement(ps);
    lemma_ordered_link(db, query_spec_at(ps), g, rows, out);
}

/// The result rows are an allowed outcome on every bound database.
pub proof fn lemma_answer_rows(sv: StoresView, v: Cv, avg: Val, cnts: Seq<u64>, sums: Seq<i128>, ord: Seq<usize>,
    r: Result<Answer, QueryError>)
    requires
        forall|db: Database| #[trigger] bound_db(sv, db) ==> db_facts(v, avg, db),
        exec_ok(v, avg, cnts, sums, ord),
        r matches Ok(Answer::Rows(rows)) && view_rows(rows@)
            == ord.map_values(|k: usize| orow(v.ps, k as int, cnts[k as int] as int, sums[k as int] as int)),
    ensures answer_meets(sv, v.ps, r),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(v.ps), r) by {
        let rows = r->Ok_0->Rows_0;
        lemma_answer_db(v, avg, db, cnts, sums, ord, view_rows(rows@));
    }
}

/// With no subquery row the average is NULL and no row qualifies: the empty answer.
pub proof fn lemma_answer_empty(sv: StoresView, v: Cv, r: Result<Answer, QueryError>)
    requires
        forall|db: Database| #[trigger] bound_db(sv, db) ==> db_facts(v, Val::Null, db),
        ps_ok(v.ps),
        r matches Ok(Answer::Rows(rows)) && rows@.len() == 0,
    ensures answer_meets(sv, v.ps, r),
{
    let cnts = Seq::new(7, |k: int| 0u64);
    let sums = Seq::new(7, |k: int| 0i128);
    let ord = Seq::<usize>::empty();
    assert forall|k: int| 0 <= k < 7 implies #[trigger] cnts[k] == cntb(v, Val::Null, k, 0, v.n)
        && sums[k] == sumb(v, Val::Null, k, 0, v.n) by {
        lemma_cntb_null(v, k, 0, v.n);
    }
    assert(order_ok(v.ps, cnts, ord));
    assert(exec_ok(v, Val::Null, cnts, sums, ord));
    let rows = r->Ok_0->Rows_0;
    assert(view_rows(rows@) =~= ord.map_values(|k: usize| orow(v.ps, k as int, cnts[k as int] as int, sums[k as int] as int)));
    lemma_answer_rows(sv, v, Val::Null, cnts, sums, ord, r);
}

/// Against a NULL average no row is a result row.
proof fn lemma_cntb_null(v: Cv, k: int, lo: int, hi: int)
    ensures cntb(v, Val::Null, k, lo, hi) == 0, sumb(v, Val::Null, k, lo, hi) == 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_cntb_null(v, k, lo, hi - 1);
    }
}

/// A group count beyond int8: error 22003 on every bound database.
pub proof fn lemma_answer_overflow(sv: StoresView, v: Cv, avg: Val, cnts: Seq<u64>, sums: Seq<i128>, k: int)
    requires
        forall|db: Database| #[trigger] bound_db(sv, db) ==> db_facts(v, avg, db),
        ps_ok(v.ps),
        avg is Null || avg is Num,
        post_b(v, avg, 0, v.n, cnts, sums),
        0 <= k < 7,
        cnts[k] > i64::MAX,
    ensures answer_meets(sv, v.ps, Ok::<Answer, QueryError>(Answer::SqlError(SqlError::NumericValueOutOfRange))),
{
    let ps = v.ps;
    assert(cnts[k] == cntb(v, avg, k, 0, v.n));
    lemma_cntb_first(v, avg, k, 0, v.n);
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::SqlError(SqlError::NumericValueOutOfRange))) by {
        lemma_count_b_all(v, db, avg, k);
        lemma_body_count_err(db, ps, seq![Val::Text(ptext(ps, k))]);
    }
}

/// An AVG division outside the executable domain: `Capacity` on every bound database.
pub proof fn lemma_answer_capacity(sv: StoresView, v: Cv, sum: int, cnt: int)
    requires
        forall|db: Database| #[trigger] bound_db(sv, db) ==> rows_match(v, db),
        ps_ok(v.ps),
        sum == suma(v, 0, v.n),
        cnt == cnta(v, 0, v.n),
        cnt > 0,
        !num_div_fits(sum, 2, cnt, 0),
    ensures answer_meets(sv, v.ps, Ok::<Answer, QueryError>(Answer::Capacity)),
{
    let ps = v.ps;
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity)) by {
        lemma_count_a_all(v, db);
        lemma_body_capacity(db, ps);
    }
}

} // verus!
