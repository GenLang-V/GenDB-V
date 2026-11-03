//! The answer from the per-key accumulators of the scan ("entries", one per non-empty group, in dictionary
//! order): SQL error 22003 when some count exceeds int8, `Capacity` when some SUM/AVG mass exceeds `i128` or some
//! AVG division leaves its domain, otherwise the result rows (already in ORDER BY order, since both dictionaries
//! are sorted bytewise). Every outcome is proved for every database bound to the stored parts.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::spec::limits::*;
use crate::spec::numeric::abs;
use crate::spec::fns::div::num_div_fits;
use crate::spec::typing::db_wf;
use crate::spec::text::lex_cmp;
use crate::exec::value::*;
use crate::link::query::*;
use crate::link::expr::i128_max;
use crate::gendb_entry::layout::PartView;
use crate::stores::facts::interface::*;
use crate::stores::facts::interface::common::colfmt::*;
use crate::schema::schema_spec;
use crate::query::*;
use super::spec::*;
use super::model::*;
use super::rows::*;
use super::common::group_outcomes::{agg_over, kind_scale};
use crate::gendb_entry::{Answer, outcome_ok};
use crate::gendb_entry::runtime::QueryError;

verus! {

// ------------------------------------------------------------------------------------------------ entries

/// The accumulators of one non-empty group: its dictionary indices, count, the five sums and, per sum, whether
/// its absolute mass exceeds `i128` (then the sum is not kept).
pub struct Entry {
    pub a: usize,
    pub b: usize,
    pub cnt: u64,
    pub s0: i128,
    pub s1: i128,
    pub s2: i128,
    pub s3: i128,
    pub s4: i128,
    pub o0: bool,
    pub o1: bool,
    pub o2: bool,
    pub o3: bool,
    pub o4: bool,
}

pub open spec fn esum(e: Entry, w: int) -> int {
    if w == 0 { e.s0 as int } else if w == 1 { e.s1 as int } else if w == 2 { e.s2 as int } else if w == 3 { e.s3 as int } else { e.s4 as int }
}

pub open spec fn eover(e: Entry, w: int) -> bool {
    if w == 0 { e.o0 } else if w == 1 { e.o1 } else if w == 2 { e.o2 } else if w == 3 { e.o3 } else { e.o4 }
}

/// The entry holds the key sums of its group over all `n` stored rows.
pub open spec fn entry_vals(e: Entry, m: Model, p: int) -> bool {
    &&& e.cnt as int == ksum(m, p, e.a as int, e.b as int, 5, 0, m.n)
    &&& forall|w: int| 0 <= w < 5 ==> #[trigger] eover(e, w) == (kabs(m, p, e.a as int, e.b as int, w, 0, m.n) > i128_max())
    &&& forall|w: int| 0 <= w < 5 && !eover(e, w) ==> #[trigger] esum(e, w) == ksum(m, p, e.a as int, e.b as int, w, 0, m.n)
}

/// Entry `k1` precedes entry `k2` in dictionary order.
pub open spec fn key_lt(e1: Entry, e2: Entry) -> bool {
    e1.a < e2.a || (e1.a == e2.a && e1.b < e2.b)
}

/// The entries are the non-empty groups, each once, in dictionary order.
pub open spec fn entries_ok(es: Seq<Entry>, m: Model, p: int) -> bool {
    &&& forall|k: int| 0 <= k < es.len() ==> {
            &&& #[trigger] es[k].a < m.nrf && es[k].b < m.nls && es[k].cnt > 0
            &&& entry_vals(es[k], m, p)
        }
    &&& forall|k1: int, k2: int| 0 <= k1 < k2 < es.len() ==> #[trigger] key_lt(es[k1], es[k2])
    &&& forall|a: int, b: int| 0 <= a < m.nrf && 0 <= b < m.nls && #[trigger] ksum(m, p, a, b, 5, 0, m.n) > 0
            ==> exists|k: int| 0 <= k < es.len() && es[k].a == a && es[k].b == b
}

/// The stored relations of every database bound to the parts: the lineitem parts `tp` represent them.
pub open spec fn dbs_ok(dbs: spec_fn(Database) -> bool, tp: Seq<PartView>) -> bool {
    forall|db: Database| #[trigger] dbs(db) ==> db.schema == schema_spec() && db_wf(db) && lineitem_ok(tp, lineitem_rel(db))
}

/// The normal form's accumulators of every key over the stored relation of one database.
pub proof fn lemma_db_keys(db: Database, tp: Seq<PartView>, p: int)
    requires
        db.schema == schema_spec(), db_wf(db), lineitem_ok(tp, lineitem_rel(db)),
        u64s(tp[LI_LINESTATUS_DICT_OFFS as int]).len() >= 2,
    ensures
        model_wf(tp_model(tp)),
        tp_shape(tp),
        tp_model(tp).n == lineitem_rel(db).len(),
        forall|a: int, b: int| 0 <= a < tp_model(tp).nrf && 0 <= b < tp_model(tp).nls ==>
            #[trigger] gcount(q1_spec(p), lineitem_rel(db), dkey(tp, a, b)) == ksum(tp_model(tp), p, a, b, 5, 0, tp_model(tp).n),
        forall|a: int, b: int, jj: int| 0 <= a < tp_model(tp).nrf && 0 <= b < tp_model(tp).nls && 0 <= jj < 7 ==>
            #[trigger] gsum(q1_spec(p), lineitem_rel(db), dkey(tp, a, b), jj) == ksum(tp_model(tp), p, a, b, wmap(jj), 0, tp_model(tp).n),
        forall|a: int, b: int, jj: int| 0 <= a < tp_model(tp).nrf && 0 <= b < tp_model(tp).nls && 0 <= jj < 7 ==>
            #[trigger] gabs(q1_spec(p), lineitem_rel(db), dkey(tp, a, b), jj) == kabs(tp_model(tp), p, a, b, wmap(jj), 0, tp_model(tp).n),
        forall|k: Row| (forall|a: int, b: int| 0 <= a < tp_model(tp).nrf && 0 <= b < tp_model(tp).nls ==> #[trigger] dkey(tp, a, b) != k)
            ==> #[trigger] gcount(q1_spec(p), lineitem_rel(db), k) == 0,
{
    let m = tp_model(tp);
    let g = q1_spec(p);
    let rel = lineitem_rel(db);
    let srows = lineitem_rows(tp, rel);
    lemma_tp_model(tp, rel);
    lemma_full_range(srows);
    assert forall|a: int, b: int| 0 <= a < m.nrf && 0 <= b < m.nls implies
        #[trigger] gcount(g, rel, dkey(tp, a, b)) == ksum(m, p, a, b, 5, 0, m.n) by {
        lemma_perm_acc(tp, rel, p, dkey(tp, a, b), 0);
        lemma_acc_ksum(tp, srows, p, a, b, 0, m.n);
    }
    assert forall|a: int, b: int, jj: int| 0 <= a < m.nrf && 0 <= b < m.nls && 0 <= jj < 7 implies
        #[trigger] gsum(g, rel, dkey(tp, a, b), jj) == ksum(m, p, a, b, wmap(jj), 0, m.n) by {
        lemma_perm_acc(tp, rel, p, dkey(tp, a, b), jj);
        lemma_acc_ksum(tp, srows, p, a, b, jj, m.n);
    }
    assert forall|a: int, b: int, jj: int| 0 <= a < m.nrf && 0 <= b < m.nls && 0 <= jj < 7 implies
        #[trigger] gabs(g, rel, dkey(tp, a, b), jj) == kabs(m, p, a, b, wmap(jj), 0, m.n) by {
        lemma_perm_acc(tp, rel, p, dkey(tp, a, b), jj);
        lemma_acc_ksum(tp, srows, p, a, b, jj, m.n);
    }
    assert forall|k: Row| (forall|a: int, b: int| 0 <= a < m.nrf && 0 <= b < m.nls ==> #[trigger] dkey(tp, a, b) != k)
        implies #[trigger] gcount(g, rel, k) == 0 by {
        lemma_perm_acc(tp, rel, p, k, 0);
        lemma_other_key(tp, srows, p, k, m.n);
    }
}

// ------------------------------------------------------------------------------------------------ outcomes

/// The parts' facts every outcome lemma takes about one database.
pub open spec fn db_ok(db: Database, tp: Seq<PartView>) -> bool {
    &&& db.schema == schema_spec() && db_wf(db) && lineitem_ok(tp, lineitem_rel(db))
    &&& u64s(tp[LI_LINESTATUS_DICT_OFFS as int]).len() >= 2
}

/// An entry with a count beyond int8: the statement is the SQL error 22003.
pub proof fn lemma_fin_err(db: Database, tp: Seq<PartView>, ps: Seq<Literal>, es: Seq<Entry>, k: int)
    requires
        db_ok(db, tp), param_domain(ps), entries_ok(es, tp_model(tp), param_day(ps)),
        0 <= k < es.len(), es[k].cnt > int8_max(),
    ensures denote_body(db, query_spec_at(ps)) == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange),
{
    let p = param_day(ps);
    lemma_db_keys(db, tp, p);
    let e = es[k];
    assert(gcount(q1_spec(p), lineitem_rel(db), dkey(tp, e.a as int, e.b as int)) == e.cnt);
    lemma_body_count_err(db, ps, dkey(tp, e.a as int, e.b as int));
}

/// The groups of a key: a key with a qualifying row is the `dkey` of some entry.
pub proof fn lemma_key_entry(db: Database, tp: Seq<PartView>, p: int, es: Seq<Entry>, k: Row)
    requires db_ok(db, tp), entries_ok(es, tp_model(tp), p), gcount(q1_spec(p), lineitem_rel(db), k) > 0,
    ensures exists|i: int| 0 <= i < es.len() && dkey(tp, es[i].a as int, es[i].b as int) == k,
{
    let m = tp_model(tp);
    lemma_db_keys(db, tp, p);
    if forall|a: int, b: int| 0 <= a < m.nrf && 0 <= b < m.nls ==> #[trigger] dkey(tp, a, b) != k {
        assert(gcount(q1_spec(p), lineitem_rel(db), k) == 0);
    } else {
        let (a, b) = choose|a: int, b: int| 0 <= a < m.nrf && 0 <= b < m.nls && #[trigger] dkey(tp, a, b) == k;
        assert(ksum(m, p, a, b, 5, 0, m.n) > 0);
        let i = choose|i: int| 0 <= i < es.len() && es[i].a == a && es[i].b == b;
        assert(dkey(tp, es[i].a as int, es[i].b as int) == k);
    }
}

/// The accumulators of an entry's key are the entry's (where its sums are kept).
pub proof fn lemma_entry_acc(db: Database, tp: Seq<PartView>, p: int, es: Seq<Entry>, i: int, jj: int)
    requires db_ok(db, tp), entries_ok(es, tp_model(tp), p), 0 <= i < es.len(), 0 <= jj < 7,
    ensures ({
        let e = es[i];
        let k = dkey(tp, e.a as int, e.b as int);
        let g = q1_spec(p);
        let rel = lineitem_rel(db);
        &&& gcount(g, rel, k) == e.cnt
        &&& eover(e, wmap(jj)) == (gabs(g, rel, k, jj) > i128_max())
        &&& !eover(e, wmap(jj)) ==> gsum(g, rel, k, jj) == esum(e, wmap(jj))
    }),
{
    lemma_db_keys(db, tp, p);
    let e = es[i];
    assert(entry_vals(e, tp_model(tp), p));
    assert(0 <= wmap(jj) < 5);
}

/// Every entry's count within int8: every group's count is.
pub proof fn lemma_all_counts(db: Database, tp: Seq<PartView>, p: int, es: Seq<Entry>)
    requires
        db_ok(db, tp), entries_ok(es, tp_model(tp), p),
        forall|i: int| 0 <= i < es.len() ==> (#[trigger] es[i]).cnt <= int8_max(),
    ensures forall|k: Row| #[trigger] gcount(q1_spec(p), lineitem_rel(db), k) <= int8_max(),
{
    assert forall|k: Row| #[trigger] gcount(q1_spec(p), lineitem_rel(db), k) <= int8_max() by {
        if gcount(q1_spec(p), lineitem_rel(db), k) > 0 {
            lemma_key_entry(db, tp, p, es, k);
            let i = choose|i: int| 0 <= i < es.len() && dkey(tp, es[i].a as int, es[i].b as int) == k;
            lemma_entry_acc(db, tp, p, es, i, 0);
        }
    }
}

/// Counts within int8 and an entry's aggregate `jj < 7` violating its capacity condition (its mass beyond
/// `i128`, or for AVG its division outside the domain): the database is outside the capacity domain.
pub proof fn lemma_fin_cap(db: Database, tp: Seq<PartView>, ps: Seq<Literal>, es: Seq<Entry>, i: int, jj: int)
    requires
        db_ok(db, tp), param_domain(ps), entries_ok(es, tp_model(tp), param_day(ps)),
        forall|i2: int| 0 <= i2 < es.len() ==> (#[trigger] es[i2]).cnt <= int8_max(),
        0 <= i < es.len(), 0 <= jj < 7,
        eover(es[i], wmap(jj)) || (4 <= jj <= 6 && !num_div_fits(esum(es[i], wmap(jj)), 2, es[i].cnt as int, 0)),
    ensures !crate::gendb_entry::capacity_domain(db, query_spec_at(ps)),
{
    let p = param_day(ps);
    let e = es[i];
    let k = dkey(tp, e.a as int, e.b as int);
    let g = q1_spec(p);
    lemma_all_counts(db, tp, p, es);
    lemma_entry_acc(db, tp, p, es, i, jj);
    assert(e.cnt > 0);
    if !eover(e, wmap(jj)) {
        assert(g.aggs[jj] is Avg && kind_scale(g.aggs[jj]) == 2);
    }
    assert(agg_over(g, lineitem_rel(db), k, jj));
    lemma_body_capacity(db, ps, k, jj);
}

/// Entries that passed every check: counts within int8, no mass beyond `i128`, AVG divisions inside the domain.
pub open spec fn entries_fit(es: Seq<Entry>) -> bool {
    forall|i: int| 0 <= i < es.len() ==> {
        &&& (#[trigger] es[i]).cnt <= int8_max()
        &&& !es[i].o0 && !es[i].o1 && !es[i].o2 && !es[i].o3 && !es[i].o4
        &&& num_div_fits(es[i].s0 as int, 2, es[i].cnt as int, 0)
        &&& num_div_fits(es[i].s1 as int, 2, es[i].cnt as int, 0)
        &&& num_div_fits(es[i].s4 as int, 2, es[i].cnt as int, 0)
    }
}

/// Entries that fit: the groups are inside `group_caps`.
pub proof fn lemma_fin_caps(db: Database, tp: Seq<PartView>, p: int, es: Seq<Entry>)
    requires db_ok(db, tp), entries_ok(es, tp_model(tp), p), entries_fit(es),
    ensures group_caps(q1_spec(p), lineitem_rel(db)),
{
    let g = q1_spec(p);
    let rel = lineitem_rel(db);
    lemma_all_counts(db, tp, p, es);
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies #[trigger] gabs(g, rel, k, j) <= i128_max() by {
        if gcount(g, rel, k) > 0 {
            lemma_key_entry(db, tp, p, es, k);
            let i = choose|i: int| 0 <= i < es.len() && dkey(tp, es[i].a as int, es[i].b as int) == k;
            assert(j < 7);
            lemma_entry_acc(db, tp, p, es, i, j);
        } else {
            lemma_zero_count(g, rel, k, j);
        }
    }
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && g.aggs[j] is Avg implies
        num_div_fits(#[trigger] gsum(g, rel, k, j), g.aggs[j]->Avg_scale, gcount(g, rel, k) as int, 0) by {
        if gcount(g, rel, k) > 0 {
            lemma_key_entry(db, tp, p, es, k);
            let i = choose|i: int| 0 <= i < es.len() && dkey(tp, es[i].a as int, es[i].b as int) == k;
            assert(4 <= j <= 6);
            lemma_entry_acc(db, tp, p, es, i, j);
        }
    }
}

// ------------------------------------------------------------------------------------------------ result rows

/// The output row of an entry: its key texts, then SUM, SUM, SUM, SUM, AVG, AVG, AVG, COUNT.
pub open spec fn entry_row(tp: Seq<PartView>, e: Entry) -> Row {
    let c = e.cnt as nat;
    dkey(tp, e.a as int, e.b as int) + seq![
        agg_out(AggKind::Sum { scale: 2 }, c, e.s0 as int), agg_out(AggKind::Sum { scale: 2 }, c, e.s1 as int),
        agg_out(AggKind::Sum { scale: 4 }, c, e.s2 as int), agg_out(AggKind::Sum { scale: 6 }, c, e.s3 as int),
        agg_out(AggKind::Avg { scale: 2 }, c, e.s0 as int), agg_out(AggKind::Avg { scale: 2 }, c, e.s1 as int),
        agg_out(AggKind::Avg { scale: 2 }, c, e.s4 as int), agg_out(AggKind::Count, c, 0)]
}

/// A fitting entry's row is the normal form's output row of its key.
pub proof fn lemma_entry_row(db: Database, tp: Seq<PartView>, p: int, es: Seq<Entry>, i: int)
    requires db_ok(db, tp), entries_ok(es, tp_model(tp), p), entries_fit(es), 0 <= i < es.len(),
    ensures entry_row(tp, es[i]) == out_row(q1_spec(p), lineitem_rel(db), dkey(tp, es[i].a as int, es[i].b as int)),
{
    let g = q1_spec(p);
    let rel = lineitem_rel(db);
    let e = es[i];
    let k = dkey(tp, e.a as int, e.b as int);
    let ao = agg_outs(g, rel, k);
    lemma_entry_acc(db, tp, p, es, i, 0);
    lemma_entry_acc(db, tp, p, es, i, 1);
    lemma_entry_acc(db, tp, p, es, i, 2);
    lemma_entry_acc(db, tp, p, es, i, 3);
    lemma_entry_acc(db, tp, p, es, i, 4);
    lemma_entry_acc(db, tp, p, es, i, 5);
    lemma_entry_acc(db, tp, p, es, i, 6);
    let tail = entry_row(tp, e).subrange(2, 10);
    assert(ao.len() == 8);
    assert(ao[0] == tail[0]);
    assert(ao[1] == tail[1]);
    assert(ao[2] == tail[2]);
    assert(ao[3] == tail[3]);
    assert(ao[4] == tail[4]);
    assert(ao[5] == tail[5]);
    assert(ao[6] == tail[6]);
    assert(ao[7] == tail[7]);
    assert(ao =~= tail);
    let f = full_row(g, rel, k);
    assert(f =~= entry_row(tp, e));
    assert forall|m: int| 0 <= m < g.outs.len() implies #[trigger] g.outs[m] == m by {}
    lemma_select_identity(f, g.outs);
}

/// The ORDER BY of the statement on two rows with text keys: the first key column, then the second.
pub proof fn lemma_keys_cmp(r1: Row, r2: Row)
    requires r1.len() >= 2, r2.len() >= 2, r1[0] is Text, r1[1] is Text, r2[0] is Text, r2[1] is Text,
    ensures ({
        let c0 = lex_cmp(r1[0]->Text_0, r2[0]->Text_0);
        let c1 = lex_cmp(r1[1]->Text_0, r2[1]->Text_0);
        keys_cmp(q1_order_keys(), r1, r2) == if c0 != 0 { c0 } else { c1 }
    }),
{
    let ks = q1_order_keys();
    let k0 = OrderKey { col: 0, desc: false, nulls_first: false };
    let k1 = OrderKey { col: 1, desc: false, nulls_first: false };
    let t1 = ks.drop_first();
    let t2 = t1.drop_first();
    assert(ks[0] == k0);
    assert(t1 =~= seq![k1]);
    assert(t1[0] == k1);
    assert(t2 =~= Seq::<OrderKey>::empty());
    let c0 = lex_cmp(r1[0]->Text_0, r2[0]->Text_0);
    let c1 = lex_cmp(r1[1]->Text_0, r2[1]->Text_0);
    assert(key_cmp(k0, r1, r2) == c0);
    assert(key_cmp(k1, r1, r2) == c1);
    assert(keys_cmp(t2, r1, r2) == 0);
    assert(keys_cmp(t1, r1, r2) == (if c1 != 0 { c1 } else { keys_cmp(t2, r1, r2) }));
    assert(keys_cmp(ks, r1, r2) == (if c0 != 0 { c0 } else { keys_cmp(t1, r1, r2) }));
}

/// Two entries in dictionary order: their rows are in ORDER BY order.
pub proof fn lemma_pair_sorted(tp: Seq<PartView>, e1: Entry, e2: Entry)
    requires
        tp_shape(tp), model_wf(tp_model(tp)), key_lt(e1, e2),
        e1.a < tp_model(tp).nrf, e2.a < tp_model(tp).nrf, e1.b < tp_model(tp).nls, e2.b < tp_model(tp).nls,
    ensures keys_cmp(q1_order_keys(), entry_row(tp, e1), entry_row(tp, e2)) <= 0,
{
    let m = tp_model(tp);
    let (r1, r2) = (entry_row(tp, e1), entry_row(tp, e2));
    let (ro, rb, lo, lb) = (u64s(tp[LI_RETURNFLAG_DICT_OFFS as int]), u8s(tp[LI_RETURNFLAG_DICT_BYTES as int]),
        u64s(tp[LI_LINESTATUS_DICT_OFFS as int]), u8s(tp[LI_LINESTATUS_DICT_BYTES as int]));
    let (x1, x2) = (rf_text(tp, e1.a as int), rf_text(tp, e2.a as int));
    let (y1, y2) = (ls_text(tp, e1.b as int), ls_text(tp, e2.b as int));
    assert(r1[0] == Val::Text(x1) && r2[0] == Val::Text(x2));
    assert(r1[1] == Val::Text(y1) && r2[1] == Val::Text(y2));
    lemma_keys_cmp(r1, r2);
    if e1.a < e2.a {
        lemma_dict_order(ro, rb, m.nrf, e1.a as int, e2.a as int);
    } else {
        crate::bridge::equality::lemma_lex_cmp_zero(x1, x2);
        lemma_dict_order(lo, lb, m.nls, e1.b as int, e2.b as int);
    }
}

/// The entries' rows are sorted by the statement's ORDER BY (dictionary order is bytewise text order).
pub proof fn lemma_rows_sorted(tp: Seq<PartView>, p: int, es: Seq<Entry>)
    requires tp_shape(tp), model_wf(tp_model(tp)), entries_ok(es, tp_model(tp), p),
    ensures sorted_by(q1_order_keys(), es.map_values(|e: Entry| entry_row(tp, e))),
{
    let rows = es.map_values(|e: Entry| entry_row(tp, e));
    assert forall|i: int, j: int| 0 <= i < j < rows.len() implies keys_cmp(q1_order_keys(), #[trigger] rows[i], #[trigger] rows[j]) <= 0 by {
        assert(key_lt(es[i], es[j]));
        assert(es[i].a < tp_model(tp).nrf && es[j].a < tp_model(tp).nrf);
        lemma_pair_sorted(tp, es[i], es[j]);
    }
}

/// The keys of the entries: duplicate free, and exactly the keys of the non-empty groups.
pub proof fn lemma_entry_keys(db: Database, tp: Seq<PartView>, p: int, es: Seq<Entry>)
    requires db_ok(db, tp), entries_ok(es, tp_model(tp), p),
    ensures ({
        let ks = es.map_values(|e: Entry| dkey(tp, e.a as int, e.b as int));
        &&& ks.no_duplicates()
        &&& forall|k: Row| #[trigger] ks.contains(k) <==> gcount(q1_spec(p), lineitem_rel(db), k) > 0
    }),
{
    let m = tp_model(tp);
    let ks = es.map_values(|e: Entry| dkey(tp, e.a as int, e.b as int));
    lemma_db_keys(db, tp, p);
    assert forall|i: int, j: int| 0 <= i < ks.len() && 0 <= j < ks.len() && i != j implies ks[i] != ks[j] by {
        let (lo, hi) = if i < j { (i, j) } else { (j, i) };
        assert(key_lt(es[lo], es[hi]));
        lemma_dkey_eq(tp, es[i].a as int, es[i].b as int, es[j].a as int, es[j].b as int);
    }
    assert forall|k: Row| #[trigger] ks.contains(k) <==> gcount(q1_spec(p), lineitem_rel(db), k) > 0 by {
        if ks.contains(k) {
            let i = choose|i: int| 0 <= i < ks.len() && ks[i] == k;
            lemma_entry_acc(db, tp, p, es, i, 0);
        }
        if gcount(q1_spec(p), lineitem_rel(db), k) > 0 {
            lemma_key_entry(db, tp, p, es, k);
            let i = choose|i: int| 0 <= i < es.len() && dkey(tp, es[i].a as int, es[i].b as int) == k;
            assert(ks[i] == k);
        }
    }
}

/// Fitting entries: their rows, in order, are an allowed output of the statement.
pub proof fn lemma_fin_rows(db: Database, tp: Seq<PartView>, ps: Seq<Literal>, es: Seq<Entry>, out: Seq<Row>)
    requires
        db_ok(db, tp), param_domain(ps), entries_ok(es, tp_model(tp), param_day(ps)), entries_fit(es),
        out == es.map_values(|e: Entry| entry_row(tp, e)),
    ensures ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    let p = param_day(ps);
    let g = q1_spec(p);
    let rel = lineitem_rel(db);
    let ks = es.map_values(|e: Entry| dkey(tp, e.a as int, e.b as int));
    lemma_db_keys(db, tp, p);
    lemma_fin_caps(db, tp, p, es);
    lemma_body_rows(db, ps);
    lemma_entry_keys(db, tp, p, es);
    lemma_rows_sorted(tp, p, es);
    assert forall|i: int| 0 <= i < out.len() implies #[trigger] out[i] == out_row(g, rel, ks[i]) by {
        lemma_entry_row(db, tp, p, es, i);
    }
    lemma_query_shape(ps);
    lemma_result_from_keys(g, q1_order_keys(), 0, None, rel, ks, out);
    lemma_slice_all(out);
    lemma_ordered_link(db, query_spec_at(ps), g, rel, out);
}

// ------------------------------------------------------------------------------------------------ the answer

/// The bytes of dictionary entry `i`.
fn dict_entry(offs: &[u64], bytes: &[u8], i: usize) -> (r: Vec<u8>)
    requires i + 1 < offs@.len(), text_range_ok(offs@, bytes@, i as int),
    ensures r@ == text_of(offs@, bytes@, i as int),
{
    let blen = bytes.len();
    let lo64 = offs[i];
    let hi64 = offs[i + 1];
    assert(lo64 <= hi64 && hi64 <= blen);
    let lo = lo64 as usize;
    let hi = hi64 as usize;
    let mut v: Vec<u8> = Vec::new();
    let mut k = lo;
    while k < hi
        invariant lo <= k <= hi, hi <= bytes@.len(), lo == offs@[i as int], hi == offs@[i + 1],
            v@ == bytes@.subrange(lo as int, k as int),
        decreases hi - k,
    {
        v.push(bytes[k]);
        k = k + 1;
        proof {
            assert(v@ =~= bytes@.subrange(lo as int, k as int));
        }
    }
    v
}

/// The facts `finish_answer` takes: the parameter, the entries of the scan, the parts' dictionaries and the
/// databases bound to the parts.
pub open spec fn finish_pre(es: Seq<Entry>, rf_offs: Seq<u64>, rf_bytes: Seq<u8>, ls_offs: Seq<u64>, ls_bytes: Seq<u8>,
    tp: Seq<PartView>, ps: Seq<Literal>, dbs: spec_fn(Database) -> bool) -> bool
{
    &&& param_domain(ps)
    &&& tp_shape(tp) && model_wf(tp_model(tp)) && u64s(tp[LI_LINESTATUS_DICT_OFFS as int]).len() >= 2
    &&& entries_ok(es, tp_model(tp), param_day(ps))
    &&& rf_offs == u64s(tp[LI_RETURNFLAG_DICT_OFFS as int]) && rf_bytes == u8s(tp[LI_RETURNFLAG_DICT_BYTES as int])
    &&& ls_offs == u64s(tp[LI_LINESTATUS_DICT_OFFS as int]) && ls_bytes == u8s(tp[LI_LINESTATUS_DICT_BYTES as int])
    &&& forall|db: Database| #[trigger] dbs(db) ==> db_ok(db, tp)
}

/// The outcome of the SQL error for every admitted database.
proof fn lemma_out_err(tp: Seq<PartView>, ps: Seq<Literal>, es: Seq<Entry>, dbs: spec_fn(Database) -> bool, k: int)
    requires
        param_domain(ps), entries_ok(es, tp_model(tp), param_day(ps)),
        forall|db: Database| #[trigger] dbs(db) ==> db_ok(db, tp),
        0 <= k < es.len(), es[k].cnt > int8_max(),
    ensures forall|db: Database| #[trigger] dbs(db) ==> outcome_ok(db, query_spec_at(ps),
        Ok::<Answer, QueryError>(Answer::SqlError(SqlError::NumericValueOutOfRange))),
{
    assert forall|db: Database| #[trigger] dbs(db) implies outcome_ok(db, query_spec_at(ps),
        Ok::<Answer, QueryError>(Answer::SqlError(SqlError::NumericValueOutOfRange))) by {
        lemma_fin_err(db, tp, ps, es, k);
    }
}

/// The outcome `Capacity` for every admitted database.
proof fn lemma_out_cap(tp: Seq<PartView>, ps: Seq<Literal>, es: Seq<Entry>, dbs: spec_fn(Database) -> bool, i: int, jj: int)
    requires
        param_domain(ps), entries_ok(es, tp_model(tp), param_day(ps)),
        forall|db: Database| #[trigger] dbs(db) ==> db_ok(db, tp),
        forall|i2: int| 0 <= i2 < es.len() ==> (#[trigger] es[i2]).cnt <= int8_max(),
        0 <= i < es.len(), 0 <= jj < 7,
        eover(es[i], wmap(jj)) || (4 <= jj <= 6 && !num_div_fits(esum(es[i], wmap(jj)), 2, es[i].cnt as int, 0)),
    ensures forall|db: Database| #[trigger] dbs(db) ==> outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity)),
{
    assert forall|db: Database| #[trigger] dbs(db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity)) by {
        lemma_fin_cap(db, tp, ps, es, i, jj);
    }
}

/// The outcome of the rows for every admitted database.
proof fn lemma_out_rows(tp: Seq<PartView>, ps: Seq<Literal>, es: Seq<Entry>, dbs: spec_fn(Database) -> bool, rows: Vec<Vec<EVal>>)
    requires
        param_domain(ps), entries_ok(es, tp_model(tp), param_day(ps)), entries_fit(es),
        forall|db: Database| #[trigger] dbs(db) ==> db_ok(db, tp),
        view_rows(rows@) == es.map_values(|e: Entry| entry_row(tp, e)),
    ensures forall|db: Database| #[trigger] dbs(db) ==> outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(rows))),
{
    assert forall|db: Database| #[trigger] dbs(db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
        lemma_fin_rows(db, tp, ps, es, view_rows(rows@));
    }
}

/// One entry fits: no mass beyond `i128` and its AVG divisions inside the domain.
pub open spec fn entry_fits(e: Entry) -> bool {
    &&& !e.o0 && !e.o1 && !e.o2 && !e.o3 && !e.o4
    &&& num_div_fits(e.s0 as int, 2, e.cnt as int, 0)
    &&& num_div_fits(e.s1 as int, 2, e.cnt as int, 0)
    &&& num_div_fits(e.s4 as int, 2, e.cnt as int, 0)
}

/// The AVG values of a fitting entry, or the aggregate `jj` that violates its capacity condition.
fn entry_avgs(e: &Entry) -> (r: Result<(EVal, EVal, EVal), usize>)
    ensures
        r matches Ok(v) ==> entry_fits(*e)
            && v.0@ == agg_out(AggKind::Avg { scale: 2 }, e.cnt as nat, e.s0 as int)
            && v.1@ == agg_out(AggKind::Avg { scale: 2 }, e.cnt as nat, e.s1 as int)
            && v.2@ == agg_out(AggKind::Avg { scale: 2 }, e.cnt as nat, e.s4 as int),
        r matches Err(jj) ==> jj < 7 && (eover(*e, wmap(jj as int))
            || (4 <= jj <= 6 && !num_div_fits(esum(*e, wmap(jj as int)), 2, e.cnt as int, 0))),
{
    if e.o0 { return Err(0); }
    if e.o1 { return Err(1); }
    if e.o2 { return Err(2); }
    if e.o3 { return Err(3); }
    if e.o4 { return Err(6); }
    let a0 = exec_avg_finalize(e.s0, 2, e.cnt);
    let a1 = exec_avg_finalize(e.s1, 2, e.cnt);
    let a4 = exec_avg_finalize(e.s4, 2, e.cnt);
    match (a0, a1, a4) {
        (Ok(v0), Ok(v1), Ok(v4)) => Ok((v0, v1, v4)),
        (Err(_), _, _) => Err(4),
        (_, Err(_), _) => Err(5),
        _ => Err(6),
    }
}

/// The result row of a fitting entry.
fn entry_row_exec(e: &Entry, v0: EVal, v1: EVal, v4: EVal, rf_offs: &[u64], rf_bytes: &[u8], ls_offs: &[u64], ls_bytes: &[u8],
    Ghost(tp): Ghost<Seq<PartView>>) -> (row: Vec<EVal>)
    requires
        tp_shape(tp), e.a < tp_model(tp).nrf, e.b < tp_model(tp).nls, e.cnt <= int8_max(),
        rf_offs@ == u64s(tp[LI_RETURNFLAG_DICT_OFFS as int]) && rf_bytes@ == u8s(tp[LI_RETURNFLAG_DICT_BYTES as int]),
        ls_offs@ == u64s(tp[LI_LINESTATUS_DICT_OFFS as int]) && ls_bytes@ == u8s(tp[LI_LINESTATUS_DICT_BYTES as int]),
        v0@ == agg_out(AggKind::Avg { scale: 2 }, e.cnt as nat, e.s0 as int),
        v1@ == agg_out(AggKind::Avg { scale: 2 }, e.cnt as nat, e.s1 as int),
        v4@ == agg_out(AggKind::Avg { scale: 2 }, e.cnt as nat, e.s4 as int),
    ensures view_row(row@) == entry_row(tp, *e),
{
    proof {
        assert(text_range_ok(rf_offs@, rf_bytes@, e.a as int));
        assert(text_range_ok(ls_offs@, ls_bytes@, e.b as int));
    }
    let mut row: Vec<EVal> = Vec::new();
    row.push(EVal::Text(dict_entry(rf_offs, rf_bytes, e.a)));
    row.push(EVal::Text(dict_entry(ls_offs, ls_bytes, e.b)));
    row.push(exec_sum_out(e.s0, 2, e.cnt));
    row.push(exec_sum_out(e.s1, 2, e.cnt));
    row.push(exec_sum_out(e.s2, 4, e.cnt));
    row.push(exec_sum_out(e.s3, 6, e.cnt));
    row.push(v0);
    row.push(v1);
    row.push(v4);
    row.push(exec_count_out(e.cnt));
    proof {
        assert(view_row(row@) =~= entry_row(tp, *e));
    }
    row
}

/// One more fitting entry and its row.
proof fn lemma_rows_step(tp: Seq<PartView>, es: Seq<Entry>, k: int, old_rows: Seq<Row>, row: Row)
    requires
        0 <= k < es.len(), entries_fit(es.subrange(0, k)), entry_fits(es[k]), es[k].cnt <= int8_max(),
        old_rows == es.subrange(0, k).map_values(|e: Entry| entry_row(tp, e)), row == entry_row(tp, es[k]),
    ensures
        entries_fit(es.subrange(0, k + 1)),
        old_rows.push(row) == es.subrange(0, k + 1).map_values(|e: Entry| entry_row(tp, e)),
{
    let es1 = es.subrange(0, k + 1);
    assert(es1 =~= es.subrange(0, k).push(es[k]));
    assert(old_rows.push(row) =~= es1.map_values(|e: Entry| entry_row(tp, e)));
    assert forall|i: int| 0 <= i < es1.len() implies {
        &&& (#[trigger] es1[i]).cnt <= int8_max()
        &&& !es1[i].o0 && !es1[i].o1 && !es1[i].o2 && !es1[i].o3 && !es1[i].o4
        &&& num_div_fits(es1[i].s0 as int, 2, es1[i].cnt as int, 0)
        &&& num_div_fits(es1[i].s1 as int, 2, es1[i].cnt as int, 0)
        &&& num_div_fits(es1[i].s4 as int, 2, es1[i].cnt as int, 0)
    } by {
        if i < k {
            assert(es1[i] == es.subrange(0, k)[i]);
        }
    }
}

/// The answer from the entries: the SQL error, `Capacity`, or the rows, each proved for every database `dbs`
/// admits.
pub fn finish_answer(es: &Vec<Entry>, rf_offs: &[u64], rf_bytes: &[u8], ls_offs: &[u64], ls_bytes: &[u8],
    Ghost(tp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(dbs): Ghost<spec_fn(Database) -> bool>)
    -> (r: Result<Answer, QueryError>)
    requires finish_pre(es@, rf_offs@, rf_bytes@, ls_offs@, ls_bytes@, tp, ps, dbs),
    ensures forall|db: Database| #[trigger] dbs(db) ==> outcome_ok(db, query_spec_at(ps), r),
{
    // a count beyond int8: the SQL error 22003
    let mut k: usize = 0;
    while k < es.len()
        invariant
            finish_pre(es@, rf_offs@, rf_bytes@, ls_offs@, ls_bytes@, tp, ps, dbs),
            k <= es@.len(),
            forall|i: int| 0 <= i < k ==> (#[trigger] es@[i]).cnt <= int8_max(),
        decreases es@.len() - k,
    {
        if es[k].cnt > 0x7fff_ffff_ffff_ffff {
            proof {
                lemma_out_err(tp, ps, es@, dbs, k as int);
            }
            return Ok(Answer::SqlError(SqlError::NumericValueOutOfRange));
        }
        k = k + 1;
    }
    // capacity checks and the rows
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let mut k: usize = 0;
    while k < es.len()
        invariant
            finish_pre(es@, rf_offs@, rf_bytes@, ls_offs@, ls_bytes@, tp, ps, dbs),
            k <= es@.len(),
            forall|i: int| 0 <= i < es@.len() ==> (#[trigger] es@[i]).cnt <= int8_max(),
            entries_fit(es@.subrange(0, k as int)),
            view_rows(rows@) == es@.subrange(0, k as int).map_values(|e: Entry| entry_row(tp, e)),
        decreases es@.len() - k,
    {
        let e = &es[k];
        match entry_avgs(e) {
            Err(jj) => {
                proof {
                    lemma_out_cap(tp, ps, es@, dbs, k as int, jj as int);
                }
                return Ok(Answer::Capacity);
            },
            Ok((v0, v1, v4)) => {
                proof {
                    assert(es@[k as int].a < tp_model(tp).nrf && es@[k as int].b < tp_model(tp).nls);
                }
                let row = entry_row_exec(e, v0, v1, v4, rf_offs, rf_bytes, ls_offs, ls_bytes, Ghost(tp));
                let ghost old_rows = view_rows(rows@);
                rows.push(row);
                proof {
                    assert(view_rows(rows@) =~= old_rows.push(view_row(row@)));
                    lemma_rows_step(tp, es@, k as int, old_rows, view_row(row@));
                }
            },
        }
        k = k + 1;
    }
    proof {
        assert(es@.subrange(0, es@.len() as int) =~= es@);
        lemma_out_rows(tp, ps, es@, dbs, rows);
    }
    Ok(Answer::Rows(rows))
}

} // verus!
