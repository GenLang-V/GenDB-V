//! The answer: from the groups of the scan's entries to an allowed output of the statement (`ordered_ok`).
//!
//! For every database bound to the parts, the GROUP BY of the statement has one group per pair code present among
//! the entries, with the entries' count and sum (`model`, `stored`, `acc`). The candidates (groups with count > 10,
//! sorted by count, largest first) are therefore a sorted permutation of the HAVING rows, and their first 100 rows are
//! an allowed output.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::order::*;
use crate::spec::scalar::*;
use crate::spec::numeric::sign;
use crate::spec::typing::db_wf;
use crate::gendb_entry::layout::PartView;
use crate::schema::schema_spec;
use crate::query::{query_spec_at, param_domain};
use crate::stores::num_tvg::interface as N;
use crate::stores::pre::interface as P;
use crate::link::query::{gcount, gsum, gabs, gkeys, full_row, agg_outs, group_caps, proj, proj_all,
    lemma_gkeys, lemma_nodup_same_multiset, lemma_map_multiset, lemma_abs_bound};
use crate::link::join::{keep, lemma_keep_map, lemma_keep_members};
use crate::exec::value::{EVal, view_row};
use super::common::groupby::{Entry, Group, groups_ok, pcount, psum, pabs};
use super::common::sort::{CountDescOrder, SortOrder, sort_range};
use super::scan::ScanInput;
use super::model::*;
use super::stored::*;
use super::acc::*;

verus! {

// ------------------------------------------------------------------------------------- the database's rows

/// A projection on all `n` positions of an `n`-column row is the row.
proof fn lemma_proj_all_ident(rows: Seq<Row>, cols: Seq<nat>)
    requires
        forall|k: int| 0 <= k < cols.len() ==> #[trigger] cols[k] == k,
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] rows[i]).len() == cols.len(),
    ensures proj_all(rows, cols) == rows,
{
    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] proj_all(rows, cols)[i] == rows[i] by {
        assert(proj(rows[i], cols) =~= rows[i]);
    }
    assert(proj_all(rows, cols) =~= rows);
}

/// Rows of table `t` have the table's arity.
proof fn lemma_row_len(db: Database, t: int, i: int)
    requires db_wf(db), 0 <= t < db.tables.len(), 0 <= i < db.tables[t].len(),
    ensures db.tables[t][i].len() == db.schema[t].columns.len(),
{
    assert(crate::spec::typing::row_in_table(db.tables[t][i], db.schema[t]));
}

/// Table arities and the table count of the schema.
proof fn lemma_schema_facts(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures
        db.tables.len() == 4,
        db.schema[1].columns.len() == 9,
        db.schema[3].columns.len() == 10,
        query_arity(db.schema, Query::Table(3)) == 10,
{
    crate::stores::num_tvg::declaration::lemma_declared_schema();
    crate::stores::pre::declaration::lemma_declared_schema();
}

/// The num and pre relations of a well-formed database of the schema: the stored relations are the tables, with
/// the shapes `nums_ok` / `pres_ok`.
pub proof fn lemma_db_rows(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures
        db.tables.len() == 4,
        crate::stores::num_tvg::declaration::stored_relations(db)[0] == db.tables[1],
        crate::stores::pre::declaration::stored_relations(db)[0] == db.tables[3],
        nums_ok(db.tables[1]),
        pres_ok(db.tables[3]),
        query_arity(db.schema, Query::Table(3)) == 10,
{
    hide(schema_spec);
    hide(db_wf);
    lemma_schema_facts(db);
    let l = db.tables[1];
    let r = db.tables[3];
    let ncols = crate::stores::num_tvg::declaration::stored_cols_t0();
    let pcols = crate::stores::pre::declaration::stored_cols_t0();
    assert forall|i: int| 0 <= i < l.len() implies (#[trigger] l[i]).len() == ncols.len() by {
        lemma_row_len(db, 1, i);
    }
    assert forall|i: int| 0 <= i < r.len() implies (#[trigger] r[i]).len() == pcols.len() by {
        lemma_row_len(db, 3, i);
    }
    lemma_proj_all_ident(l, ncols);
    lemma_proj_all_ident(r, pcols);
    crate::stores::num_tvg::declaration::lemma_stored_relations(db);
    crate::stores::pre::declaration::lemma_stored_relations(db);
    lemma_rows_shape(crate::stores::num_tvg::declaration::stored_relations(db)[0],
        crate::stores::pre::declaration::stored_relations(db)[0]);
}

/// Row shapes from the stored columns' declared types.
proof fn lemma_rows_shape(l: Seq<Row>, r: Seq<Row>)
    requires
        crate::link::source::rows_in_columns(l, crate::stores::num_tvg::declaration::stored_columns_t0()),
        crate::link::source::rows_in_columns(r, crate::stores::pre::declaration::stored_columns_t0()),
    ensures nums_ok(l), pres_ok(r),
{
    let ncs = crate::stores::num_tvg::declaration::stored_columns_t0();
    let pcs = crate::stores::pre::declaration::stored_columns_t0();
    assert forall|i: int| 0 <= i < l.len() implies num_row_ok(#[trigger] l[i]) by {
        let x = l[i];
        assert(x.len() == ncs.len());
        assert(crate::spec::typing::value_in_column(x[0], ncs[0]));
        assert(crate::spec::typing::value_in_column(x[1], ncs[1]));
        assert(crate::spec::typing::value_in_column(x[2], ncs[2]));
        assert(crate::spec::typing::value_in_column(x[3], ncs[3]));
        assert(crate::spec::typing::value_in_column(x[5], ncs[5]));
        assert(crate::spec::typing::value_in_column(x[7], ncs[7]));
    }
    assert forall|j: int| 0 <= j < r.len() implies pre_row_ok(#[trigger] r[j]) by {
        let y = r[j];
        assert(y.len() == pcs.len());
        assert(crate::spec::typing::value_in_column(y[0], pcs[0]));
        assert(crate::spec::typing::value_in_column(y[6], pcs[6]));
        assert(crate::spec::typing::value_in_column(y[7], pcs[7]));
    }
}

// ------------------------------------------------------------------------------------------------ the output

/// The output row of candidate group `c`: tag, version, count, sum.
pub open spec fn cand_row(np: Seq<PartView>, c: Group) -> Row {
    seq![Val::Text(ntag_str(np, c.key as int)), Val::Text(nver_str(np, c.key as int)), Val::Int(c.count as int),
        Val::Num { coeff: c.sum as int, scale: 4 }]
}

/// The candidates: exactly the groups with count > 10, distinct keys, sorted by count (largest first).
#[verifier::opaque]
pub open spec fn cands_ok(gs: Seq<Group>, cs: Seq<Group>) -> bool {
    &&& forall|a: int, b: int| 0 <= a < b < cs.len() ==> #[trigger] cs[a].key != #[trigger] cs[b].key
    &&& forall|a: int, b: int| 0 <= a < b < cs.len() ==> #[trigger] cs[a].count >= #[trigger] cs[b].count
    &&& forall|c: int| 0 <= c < cs.len() ==> gs.contains(#[trigger] cs[c])
    &&& forall|c: int| 0 <= c < cs.len() ==> #[trigger] cs[c].count > 10
    &&& forall|g: int| 0 <= g < gs.len() && #[trigger] gs[g].count > 10 ==> cs.contains(gs[g])
}

/// The premises gathered by the query: the entries of the uom runs, their groups and the candidates.
pub open spec fn answer_premises(np: Seq<PartView>, pp: Seq<PartView>, inp: ScanInput, ps: Seq<Literal>, r0: int, r1: int,
    es: Seq<Entry>, gs: Seq<Group>, cs: Seq<Group>) -> bool {
    &&& inp_matches(inp, np, pp, ps) && inp.wf()
    &&& N::num_layout_ok(np) && P::pre_layout_ok(pp)
    &&& 0 <= r0 <= r1 <= inp.runs
    &&& forall|r: int| 0 <= r < inp.runs ==> (#[trigger] N::run_uom_of(np, r) == ukey(ps)) == (r0 <= r < r1)
    &&& es == inp.run_ents(r0, r1)
    &&& groups_ok(es, gs)
    &&& cands_ok(gs, cs)
    &&& inp.n <= 0x7fff_ffff_ffff_ffff
}

/// Keys of the entries: valid pair codes; group key and pair code correspond one to one.
proof fn lemma_group_keys(np: Seq<PartView>, pp: Seq<PartView>, inp: ScanInput, ps: Seq<Literal>, r0: int, r1: int,
    es: Seq<Entry>, gs: Seq<Group>, cs: Seq<Group>)
    requires answer_premises(np, pp, inp, ps, r0, r1, es, gs, cs),
    ensures
        forall|m: int| 0 <= m < es.len() ==> (#[trigger] es[m]).key < N::pair_count(np),
        forall|g: int| 0 <= g < gs.len() ==> (#[trigger] gs[g]).key < N::pair_count(np),
        es.len() <= inp.n,
{
    super::scan::lemma_run_ents_facts(inp, r0, r1);
    assert(inp.run_start@[r1] <= inp.run_start@[inp.runs as int]);
    assert forall|g: int| 0 <= g < gs.len() implies (#[trigger] gs[g]).key < N::pair_count(np) by {
        let p = gs[g].key;
        assert(gs[g].count > 0);
        assert(pcount(es, p) > 0);
        if !(exists|m: int| 0 <= m < es.len() && (#[trigger] es[m]).key == p) {
            lemma_pcount_zero(es, p);
        }
        let m = choose|m: int| 0 <= m < es.len() && (#[trigger] es[m]).key == p;
    }
}

proof fn lemma_pcount_zero(es: Seq<Entry>, p: u64)
    requires forall|m: int| 0 <= m < es.len() ==> (#[trigger] es[m]).key != p,
    ensures pcount(es, p) == 0,
    decreases es.len(),
{
    if es.len() > 0 {
        let ei = es.drop_last();
        assert forall|m: int| 0 <= m < ei.len() implies (#[trigger] ei[m]).key != p by {
            assert(ei[m] == es[m]);
        }
        lemma_pcount_zero(ei, p);
        assert(es.last() == es[es.len() - 1]);
    }
}

/// The GROUP BY accumulators of key `k` of the statement over a bound database are the entries'.
proof fn lemma_acc_db(db: Database, np: Seq<PartView>, pp: Seq<PartView>, inp: ScanInput, ps: Seq<Literal>, r0: int,
    r1: int, es: Seq<Entry>, k: Row)
    requires
        db.schema == schema_spec(), db_wf(db),
        N::represents(np, crate::stores::num_tvg::declaration::stored_relations(db)),
        P::represents(pp, crate::stores::pre::declaration::stored_relations(db)),
        inp_matches(inp, np, pp, ps), inp.wf(),
        0 <= r0 <= r1 <= inp.runs,
        forall|r: int| 0 <= r < inp.runs ==> (#[trigger] N::run_uom_of(np, r) == ukey(ps)) == (r0 <= r < r1),
        es == inp.run_ents(r0, r1),
    ensures ({
        let (l, r) = (db.tables[1], db.tables[3]);
        let g = lj_spec(ps);
        let xs = lj_rows(l, r);
        &&& gcount(g, xs, k) == ecount(np, es, k)
        &&& gsum(g, xs, k, 1) == esum(np, es, k)
        &&& gabs(g, xs, k, 1) == eabs(np, es, k)
    }),
{
    lemma_db_rows(db);
    let rn = crate::stores::num_tvg::declaration::stored_relations(db);
    let rp = crate::stores::pre::declaration::stored_relations(db);
    lemma_acc_all(np, pp, rn, rp, inp, ps, r0, r1, es, k);
    lemma_lj_acc(ps, db.tables[1], db.tables[3], k, 1);
}

/// The statement's GROUP BY accumulators are the entries'.
#[verifier::opaque]
pub open spec fn acc_link(np: Seq<PartView>, ps: Seq<Literal>, l: Seq<Row>, r: Seq<Row>, es: Seq<Entry>) -> bool {
    forall|k: Row| #![trigger gcount(lj_spec(ps), lj_rows(l, r), k)]
        gcount(lj_spec(ps), lj_rows(l, r), k) == ecount(np, es, k)
        && gsum(lj_spec(ps), lj_rows(l, r), k, 1) == esum(np, es, k)
        && gabs(lj_spec(ps), lj_rows(l, r), k, 1) == eabs(np, es, k)
}

/// Every group key with entries is the key of one of the groups, with its accumulators.
#[verifier::opaque]
pub open spec fn key_groups(np: Seq<PartView>, es: Seq<Entry>, gs: Seq<Group>) -> bool {
    forall|k: Row| #[trigger] ecount(np, es, k) > 0 ==> exists|gi: int| 0 <= gi < gs.len()
        && keyp(np, gs[gi].key as int) == k && ecount(np, es, k) == gs[gi].count && esum(np, es, k) == gs[gi].sum
        && eabs(np, es, k) == pabs(es, gs[gi].key)
}

proof fn lemma_acc_link(db: Database, np: Seq<PartView>, pp: Seq<PartView>, inp: ScanInput, ps: Seq<Literal>, r0: int,
    r1: int, es: Seq<Entry>)
    requires
        db.schema == schema_spec(), db_wf(db),
        N::represents(np, crate::stores::num_tvg::declaration::stored_relations(db)),
        P::represents(pp, crate::stores::pre::declaration::stored_relations(db)),
        inp_matches(inp, np, pp, ps), inp.wf(),
        0 <= r0 <= r1 <= inp.runs,
        forall|r: int| 0 <= r < inp.runs ==> (#[trigger] N::run_uom_of(np, r) == ukey(ps)) == (r0 <= r < r1),
        es == inp.run_ents(r0, r1),
    ensures acc_link(np, ps, db.tables[1], db.tables[3], es),
{
    reveal(acc_link);
    assert forall|k: Row| #![trigger gcount(lj_spec(ps), lj_rows(db.tables[1], db.tables[3]), k)]
        gcount(lj_spec(ps), lj_rows(db.tables[1], db.tables[3]), k) == ecount(np, es, k)
        && gsum(lj_spec(ps), lj_rows(db.tables[1], db.tables[3]), k, 1) == esum(np, es, k)
        && gabs(lj_spec(ps), lj_rows(db.tables[1], db.tables[3]), k, 1) == eabs(np, es, k) by {
        lemma_acc_db(db, np, pp, inp, ps, r0, r1, es, k);
    }
}

proof fn lemma_key_groups(np: Seq<PartView>, es: Seq<Entry>, gs: Seq<Group>)
    requires
        N::num_layout_ok(np), groups_ok(es, gs),
        forall|m: int| 0 <= m < es.len() ==> (#[trigger] es[m]).key < N::pair_count(np),
    ensures key_groups(np, es, gs),
{
    reveal(key_groups);
    assert forall|k: Row| #[trigger] ecount(np, es, k) > 0 implies exists|gi: int| 0 <= gi < gs.len()
        && keyp(np, gs[gi].key as int) == k && ecount(np, es, k) == gs[gi].count && esum(np, es, k) == gs[gi].sum
        && eabs(np, es, k) == pabs(es, gs[gi].key) by {
        lemma_ecount_witness(np, es, k);
        let m = choose|m: int| 0 <= m < es.len() && keyp(np, (#[trigger] es[m]).key as int) == k;
        let p = es[m].key;
        lemma_e_to_p(np, es, p);
        assert(pcount(es, p) > 0);
        let gi = choose|gi: int| 0 <= gi < gs.len() && gs[gi].key == p;
        assert(gs[gi].count as int == pcount(es, p));
    }
}

/// The groups are inside the arithmetic domain of the GROUP BY.
proof fn lemma_caps(np: Seq<PartView>, ps: Seq<Literal>, l: Seq<Row>, r: Seq<Row>, es: Seq<Entry>, gs: Seq<Group>)
    requires
        acc_link(np, ps, l, r, es), key_groups(np, es, gs), groups_ok(es, gs),
        es.len() <= 0x7fff_ffff_ffff_ffff,
    ensures group_caps(lj_spec(ps), lj_rows(l, r)),
{
    reveal(acc_link);
    reveal(key_groups);
    let g = lj_spec(ps);
    let xs = lj_rows(l, r);
    assert forall|k: Row, j: int| #![trigger gcount(g, xs, k), g.aggs[j]] 0 <= j < g.aggs.len() && g.aggs[j] is Count
        implies gcount(g, xs, k) <= crate::spec::limits::int8_max() by {
        lemma_ecount_le(np, es, k);
    }
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count)
        implies #[trigger] gabs(g, xs, k, j) <= crate::link::expr::i128_max() by {
        assert(j == 1);
        assert(gcount(g, xs, k) == ecount(np, es, k));
        if ecount(np, es, k) > 0 {
            let gi = choose|gi: int| 0 <= gi < gs.len()
                && keyp(np, gs[gi].key as int) == k && ecount(np, es, k) == gs[gi].count && esum(np, es, k) == gs[gi].sum
                && eabs(np, es, k) == pabs(es, gs[gi].key);
            assert(pabs(es, gs[gi].key) <= i128::MAX);
        } else {
            lemma_ecount_zero_abs(np, es, k);
        }
    }
}

/// The statement's answer: the first 100 candidate rows are an allowed output.
pub proof fn lemma_answer(db: Database, np: Seq<PartView>, pp: Seq<PartView>, inp: ScanInput, ps: Seq<Literal>, r0: int,
    r1: int, es: Seq<Entry>, gs: Seq<Group>, cs: Seq<Group>, out: Seq<Row>)
    requires
        db.schema == schema_spec(), db_wf(db), param_domain(ps),
        N::represents(np, crate::stores::num_tvg::declaration::stored_relations(db)),
        P::represents(pp, crate::stores::pre::declaration::stored_relations(db)),
        answer_premises(np, pp, inp, ps, r0, r1, es, gs, cs),
        out.len() == if cs.len() < 100 { cs.len() } else { 100 },
        forall|i: int| 0 <= i < out.len() ==> #[trigger] out[i] == cand_row(np, cs[i]),
    ensures ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    lemma_db_rows(db);
    lemma_group_keys(np, pp, inp, ps, r0, r1, es, gs, cs);
    let (l, r) = (db.tables[1], db.tables[3]);
    lemma_acc_link(db, np, pp, inp, ps, r0, r1, es);
    lemma_key_groups(np, es, gs);
    lemma_caps(np, ps, l, r, es, gs);
    lemma_body(db, ps, l, r);
    lemma_statement(ps);
    lemma_output(db, np, ps, l, r, es, gs, cs, out);
}

/// No entries of key `k`: its absolute sum is 0.
proof fn lemma_ecount_zero_abs(np: Seq<PartView>, es: Seq<Entry>, k: Row)
    requires ecount(np, es, k) == 0,
    ensures eabs(np, es, k) == 0, esum(np, es, k) == 0,
    decreases es.len(),
{
    if es.len() > 0 {
        lemma_ecount_zero_abs(np, es.drop_last(), k);
    }
}

/// The group key of every candidate.
pub open spec fn cand_keys(np: Seq<PartView>, cs: Seq<Group>) -> Seq<Row> {
    cs.map_values(|c: Group| keyp(np, c.key as int))
}

/// What a candidate is: a group with count > 10, i.e. the count and sum of its pair code's entries.
proof fn lemma_cand_facts(np: Seq<PartView>, es: Seq<Entry>, gs: Seq<Group>, cs: Seq<Group>, c: int)
    requires
        groups_ok(es, gs), cands_ok(gs, cs), 0 <= c < cs.len(),
        forall|g: int| 0 <= g < gs.len() ==> (#[trigger] gs[g]).key < N::pair_count(np),
    ensures
        cs[c].count as int == pcount(es, cs[c].key), cs[c].sum as int == psum(es, cs[c].key), cs[c].count > 10,
        cs[c].key < N::pair_count(np),
{
    reveal(cands_ok);
    assert(gs.contains(cs[c]));
    let gi = choose|gi: int| 0 <= gi < gs.len() && gs[gi] == cs[c];
    assert(gs[gi].count as int == pcount(es, gs[gi].key));
}

/// A group with count > 10 is a candidate.
proof fn lemma_group_is_cand(gs: Seq<Group>, cs: Seq<Group>, gi: int)
    requires cands_ok(gs, cs), 0 <= gi < gs.len(), gs[gi].count > 10,
    ensures exists|c: int| 0 <= c < cs.len() && cs[c] == gs[gi],
{
    reveal(cands_ok);
    assert(cs.contains(gs[gi]));
}

/// A candidate's full GROUP BY row is its output row.
proof fn lemma_cand_full(np: Seq<PartView>, ps: Seq<Literal>, l: Seq<Row>, r: Seq<Row>, es: Seq<Entry>, c: Group)
    requires
        N::num_layout_ok(np), acc_link(np, ps, l, r, es),
        forall|m: int| 0 <= m < es.len() ==> (#[trigger] es[m]).key < N::pair_count(np),
        c.count as int == pcount(es, c.key), c.sum as int == psum(es, c.key), c.count > 10, c.key < N::pair_count(np),
    ensures
        full_row(lj_spec(ps), lj_rows(l, r), keyp(np, c.key as int)) == cand_row(np, c),
        gcount(lj_spec(ps), lj_rows(l, r), keyp(np, c.key as int)) == c.count,
{
    hide(gcount);
    hide(gsum);
    hide(gabs);
    hide(lj_rows);
    hide(ecount);
    hide(esum);
    hide(eabs);
    reveal(acc_link);
    let g = lj_spec(ps);
    let xs = lj_rows(l, r);
    lemma_e_to_p(np, es, c.key);
    let k = keyp(np, c.key as int);
    assert(gcount(g, xs, k) == ecount(np, es, k));
    assert(gsum(g, xs, k, 1) == esum(np, es, k));
    assert(agg_outs(g, xs, k) =~= seq![Val::Int(c.count as int), Val::Num { coeff: c.sum as int, scale: 4 }]);
    assert(full_row(g, xs, k) =~= cand_row(np, c));
}

/// The candidates' keys are the HAVING keys of the statement's groups.
proof fn lemma_keys_equiv(np: Seq<PartView>, ps: Seq<Literal>, l: Seq<Row>, r: Seq<Row>, es: Seq<Entry>, gs: Seq<Group>,
    cs: Seq<Group>, k: Row)
    requires
        N::num_layout_ok(np), acc_link(np, ps, l, r, es), key_groups(np, es, gs), groups_ok(es, gs), cands_ok(gs, cs),
        forall|g: int| 0 <= g < gs.len() ==> (#[trigger] gs[g]).key < N::pair_count(np),
        forall|m: int| 0 <= m < es.len() ==> (#[trigger] es[m]).key < N::pair_count(np),
    ensures
        cand_keys(np, cs).contains(k) <==> gcount(lj_spec(ps), lj_rows(l, r), k) > 10,
{
    hide(gcount);
    hide(gsum);
    hide(gabs);
    hide(lj_rows);
    hide(ecount);
    hide(esum);
    hide(eabs);
    hide(groups_ok);
    let g = lj_spec(ps);
    let xs = lj_rows(l, r);
    let ks = cand_keys(np, cs);
    if ks.contains(k) {
        let c = choose|c: int| 0 <= c < ks.len() && ks[c] == k;
        lemma_cand_facts(np, es, gs, cs, c);
        lemma_cand_full(np, ps, l, r, es, cs[c]);
    }
    if gcount(g, xs, k) > 10 {
        reveal(acc_link);
        reveal(key_groups);
        assert(gcount(g, xs, k) == ecount(np, es, k));
        assert(ecount(np, es, k) > 0);
        let gi = choose|gi: int| 0 <= gi < gs.len()
            && keyp(np, gs[gi].key as int) == k && ecount(np, es, k) == gs[gi].count && esum(np, es, k) == gs[gi].sum
            && eabs(np, es, k) == pabs(es, gs[gi].key);
        assert(gs[gi].count > 10);
        lemma_group_is_cand(gs, cs, gi);
        let c = choose|c: int| 0 <= c < cs.len() && cs[c] == gs[gi];
        assert(ks[c] == k);
    }
}

/// Distinct candidates have distinct keys.
proof fn lemma_cand_keys_nodup(np: Seq<PartView>, gs: Seq<Group>, cs: Seq<Group>)
    requires
        N::num_layout_ok(np), cands_ok(gs, cs),
        forall|g: int| 0 <= g < gs.len() ==> (#[trigger] gs[g]).key < N::pair_count(np),
    ensures cand_keys(np, cs).no_duplicates(),
{
    reveal(cands_ok);
    let ks = cand_keys(np, cs);
    assert forall|a: int, b: int| 0 <= a < ks.len() && 0 <= b < ks.len() && a != b implies ks[a] != ks[b] by {
        assert(gs.contains(cs[a]) && gs.contains(cs[b]));
        let ga = choose|gi: int| 0 <= gi < gs.len() && gs[gi] == cs[a];
        let gb = choose|gi: int| 0 <= gi < gs.len() && gs[gi] == cs[b];
        if ks[a] == ks[b] {
            assert(ntag_str(np, cs[a].key as int) == ks[a][0]->Text_0);
            assert(ntag_str(np, cs[b].key as int) == ks[b][0]->Text_0);
            assert(nver_str(np, cs[a].key as int) == ks[a][1]->Text_0);
            assert(nver_str(np, cs[b].key as int) == ks[b][1]->Text_0);
            lemma_npair_inj(np, cs[a].key as int, cs[b].key as int);
            if a < b {
                assert(cs[a].key != cs[b].key);
            } else {
                assert(cs[b].key != cs[a].key);
            }
        }
    }
}

proof fn lemma_cands_count_sorted(gs: Seq<Group>, cs: Seq<Group>)
    requires cands_ok(gs, cs),
    ensures forall|a: int, b: int| 0 <= a < b < cs.len() ==> #[trigger] cs[a].count >= #[trigger] cs[b].count,
{
    reveal(cands_ok);
}

/// The candidates' rows, sorted by count (largest first), are sorted by the ORDER BY key.
proof fn lemma_cands_sorted(np: Seq<PartView>, cs: Seq<Group>, p: Seq<Row>)
    requires
        forall|a: int, b: int| 0 <= a < b < cs.len() ==> #[trigger] cs[a].count >= #[trigger] cs[b].count,
        p.len() == cs.len(),
        forall|c: int| 0 <= c < cs.len() ==> #[trigger] p[c] == cand_row(np, cs[c]),
    ensures sorted_by(seq![OrderKey { col: 2, desc: true, nulls_first: true }], p),
{
    let keys = seq![OrderKey { col: 2, desc: true, nulls_first: true }];
    assert forall|i: int, j: int| 0 <= i < j < p.len() implies keys_cmp(keys, #[trigger] p[i], #[trigger] p[j]) <= 0 by {
        let (ci, cj) = (cs[i].count as int, cs[j].count as int);
        assert(p[i].len() == 4 && p[j].len() == 4);
        assert(p[i][2] == Val::Int(ci));
        assert(p[j][2] == Val::Int(cj));
        crate::link::expr::lemma_compare_int(ci, cj);
        assert(ci >= cj);
        assert(sign(ci - cj) >= 0);
        assert(key_cmp(keys[0], p[i], p[j]) == -sign(ci - cj));
        assert(keys.drop_first() =~= Seq::<OrderKey>::empty());
        assert(keys_cmp(keys.drop_first(), p[i], p[j]) == 0);
    }
}

/// From the body's rows to the output.
proof fn lemma_output(db: Database, np: Seq<PartView>, ps: Seq<Literal>, l: Seq<Row>, r: Seq<Row>, es: Seq<Entry>,
    gs: Seq<Group>, cs: Seq<Group>, out: Seq<Row>)
    requires
        eval_query(db, Seq::empty(), body_query(ps)) == Ok::<Relation, SqlError>(keep(gb_rows(ps, l, r), |row: Row| having_ok(row))),
        query_spec_at(ps).body == body_query(ps),
        query_spec_at(ps).keys == seq![OrderKey { col: 2, desc: true, nulls_first: true }],
        query_spec_at(ps).limit == Some(100nat),
        query_spec_at(ps).offset == 0,
        N::num_layout_ok(np),
        groups_ok(es, gs), cands_ok(gs, cs), acc_link(np, ps, l, r, es), key_groups(np, es, gs),
        forall|g: int| 0 <= g < gs.len() ==> (#[trigger] gs[g]).key < N::pair_count(np),
        forall|m: int| 0 <= m < es.len() ==> (#[trigger] es[m]).key < N::pair_count(np),
        out.len() == if cs.len() < 100 { cs.len() } else { 100 },
        forall|i: int| 0 <= i < out.len() ==> #[trigger] out[i] == cand_row(np, cs[i]),
    ensures ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    hide(eval_query);
    hide(gcount);
    hide(gsum);
    hide(gabs);
    hide(lj_rows);
    hide(ecount);
    hide(esum);
    hide(eabs);
    hide(gkeys);
    hide(groups_ok);
    let g = lj_spec(ps);
    let xs = lj_rows(l, r);
    let f = |k: Row| full_row(g, xs, k);
    let hv = |k: Row| having_ok(f(k));
    let gk = gkeys(g, xs);
    let h = keep(gk, hv);
    let ks = cand_keys(np, cs);
    let p = ks.map_values(f);
    assert forall|c: int| 0 <= c < cs.len() implies #[trigger] p[c] == cand_row(np, cs[c]) by {
        lemma_cand_facts(np, es, gs, cs, c);
        lemma_cand_full(np, ps, l, r, es, cs[c]);
    }
    lemma_gkeys(g, xs);
    lemma_keep_members(gk, hv);
    assert forall|k: Row| #[trigger] ks.contains(k) <==> h.contains(k) by {
        lemma_keys_equiv(np, ps, l, r, es, gs, cs, k);
        if ks.contains(k) {
            assert(gcount(g, xs, k) > 10);
            assert(gk.contains(k));
            lemma_group_row_count(ps, l, r, k);
            lemma_keep_contains(gk, hv, k);
        }
        if h.contains(k) {
            let i = choose|i: int| 0 <= i < h.len() && h[i] == k;
            assert(gk.contains(h[i]) && hv(h[i]));
            assert(gcount(g, xs, k) > 0);
            lemma_group_row_count(ps, l, r, k);
        }
    }
    lemma_cand_keys_nodup(np, gs, cs);
    lemma_cands_count_sorted(gs, cs);
    lemma_keep_nodup(gk, hv);
    lemma_nodup_same_multiset(ks, h);
    lemma_map_multiset(ks, h, f);
    let hav = |row: Row| having_ok(row);
    lemma_keep_map(gk, f, hav);
    crate::link::join::lemma_keep_ext(gk, |y: Row| hav(f(y)), hv);
    assert(gb_rows(ps, l, r) =~= gk.map_values(f));
    assert(keep(gk.map_values(f), hav) == h.map_values(f));
    assert(keep(gb_rows(ps, l, r), hav) == h.map_values(f));
    lemma_cands_sorted(np, cs, p);
    assert(slice_rows(p, 0, Some(100nat)) =~= out);
    assert(p.to_multiset() == keep(gb_rows(ps, l, r), |row: Row| having_ok(row)).to_multiset());
}

/// A group of the statement with rows: its key has 2 columns and its row's count is at position 2.
proof fn lemma_group_row_count(ps: Seq<Literal>, l: Seq<Row>, r: Seq<Row>, k: Row)
    requires gcount(lj_spec(ps), lj_rows(l, r), k) > 0,
    ensures full_row(lj_spec(ps), lj_rows(l, r), k)[2] == Val::Int(gcount(lj_spec(ps), lj_rows(l, r), k) as int),
{
    let g = lj_spec(ps);
    let xs = lj_rows(l, r);
    crate::link::query::lemma_count_witness(g, xs, k);
    let m = choose|m: int| 0 <= m < xs.len() && #[trigger] crate::link::query::hit(g, xs[m], k);
    assert(k == key2(xs[m]));
    assert(agg_outs(g, xs, k)[0] == Val::Int(gcount(g, xs, k) as int));
}

/// `keep` keeps every row satisfying the condition.
proof fn lemma_keep_contains(rows: Seq<Row>, f: spec_fn(Row) -> bool, x: Row)
    requires rows.contains(x), f(x),
    ensures keep(rows, f).contains(x),
    decreases rows.len(),
{
    if rows.last() == x {
        assert(keep(rows, f).last() == x);
        assert(keep(rows, f)[keep(rows, f).len() - 1] == x);
    } else {
        let i = choose|i: int| 0 <= i < rows.len() && rows[i] == x;
        assert(rows.drop_last()[i] == x);
        lemma_keep_contains(rows.drop_last(), f, x);
        let kk = keep(rows.drop_last(), f);
        let j = choose|j: int| 0 <= j < kk.len() && kk[j] == x;
        if f(rows.last()) {
            assert(keep(rows, f)[j] == x);
        }
    }
}

/// `keep` of a duplicate-free sequence is duplicate-free.
proof fn lemma_keep_nodup(rows: Seq<Row>, f: spec_fn(Row) -> bool)
    requires rows.no_duplicates(),
    ensures keep(rows, f).no_duplicates(),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        assert(ri.no_duplicates()) by {
            assert forall|a: int, b: int| 0 <= a < ri.len() && 0 <= b < ri.len() && a != b implies ri[a] != ri[b] by {
                assert(ri[a] == rows[a] && ri[b] == rows[b]);
            }
        }
        lemma_keep_nodup(ri, f);
        lemma_keep_members(ri, f);
        let k = keep(rows, f);
        let ki = keep(ri, f);
        if f(rows.last()) {
            assert forall|a: int, b: int| 0 <= a < k.len() && 0 <= b < k.len() && a != b implies k[a] != k[b] by {
                if a == ki.len() || b == ki.len() {
                    let o = if a == ki.len() { b } else { a };
                    assert(ri.contains(ki[o]));
                    let m = choose|m: int| 0 <= m < ri.len() && ri[m] == ki[o];
                    assert(rows[m] != rows[rows.len() - 1]);
                } else {
                    assert(k[a] == ki[a] && k[b] == ki[b]);
                }
            }
        }
    }
}


// ------------------------------------------------------------------------------------------ the candidates (exec)


/// The groups with count > 10, sorted by count (largest first): sort all groups by count, keep the prefix with
/// count > 10.
pub fn select_cands(gs: &Vec<Group>) -> (cs: Vec<Group>)
    requires forall|a: int, b: int| 0 <= a < b < gs@.len() ==> #[trigger] gs@[a].key < #[trigger] gs@[b].key,
    ensures cands_ok(gs@, cs@),
{
    let n = gs.len();
    let mut v = gs.clone();
    let mut tmp = gs.clone();
    let o = CountDescOrder {};
    let ghost g0 = gs@;
    proof {
        assert(v@ =~= g0) by {
            assert forall|q: int| 0 <= q < v@.len() implies v@[q] == g0[q] by {}
        }
        assert(v@.subrange(0, n as int) =~= v@);
        assert forall|q: int| 0 <= q < v@.subrange(0, n as int).len() implies o.ok(#[trigger] v@.subrange(0, n as int)[q]) by {}
    }
    sort_range(&o, &mut v, &mut tmp, 0, n);
    proof {
        assert(v@.subrange(0, n as int) =~= v@);
        assert(g0.subrange(0, n as int) =~= g0);
        assert forall|a: int, b: int| 0 <= a < b < v@.len() implies #[trigger] v@[a].count >= #[trigger] v@[b].count by {
            assert(o.le(v@[a], v@[b]));
        }
    }
    // the prefix with count > 10
    let mut m: usize = 0;
    while m < n && v[m].count > 10
        invariant n == v@.len(), m <= n, forall|q: int| 0 <= q < m ==> #[trigger] v@[q].count > 10,
        decreases n - m,
    {
        m = m + 1;
    }
    let ghost vv = v@;
    v.truncate(m);
    proof {
        lemma_cands_prefix(g0, vv, m as int);
    }
    v
}

/// Sequences with one multiset have the same elements.
proof fn lemma_same_elems(v: Seq<Group>, gs: Seq<Group>)
    requires v.to_multiset() == gs.to_multiset(),
    ensures forall|x: Group| #[trigger] v.contains(x) <==> gs.contains(x),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    v.to_multiset_ensures();
    gs.to_multiset_ensures();
    assert forall|x: Group| #[trigger] v.contains(x) <==> gs.contains(x) by {
        let (cv, cg) = (v.to_multiset().count(x), gs.to_multiset().count(x));
        assert(cv == cg);
        assert(v.contains(x) <==> cv > 0);
        assert(gs.contains(x) <==> cg > 0);
    }
}

/// Groups with strictly increasing keys are distinct, and so is any permutation of them.
proof fn lemma_perm_nodup(v: Seq<Group>, gs: Seq<Group>)
    requires
        forall|a: int, b: int| 0 <= a < b < gs.len() ==> #[trigger] gs[a].key < #[trigger] gs[b].key,
        v.to_multiset() == gs.to_multiset(),
    ensures v.no_duplicates(),
{
    assert(gs.no_duplicates()) by {
        assert forall|a: int, b: int| 0 <= a < gs.len() && 0 <= b < gs.len() && a != b implies gs[a] != gs[b] by {
            if a < b {
                assert(gs[a].key < gs[b].key);
            } else {
                assert(gs[b].key < gs[a].key);
            }
        }
    }
    gs.lemma_multiset_has_no_duplicates();
    assert forall|x: Group| v.to_multiset().contains(x) implies v.to_multiset().count(x) == 1 by {
        assert(gs.to_multiset().contains(x));
    }
    v.lemma_multiset_has_no_duplicates_conv();
}

/// Distinct groups of `gs` (strictly increasing keys) have distinct keys.
proof fn lemma_distinct_keys(v: Seq<Group>, gs: Seq<Group>, a: int, b: int)
    requires
        forall|a: int, b: int| 0 <= a < b < gs.len() ==> #[trigger] gs[a].key < #[trigger] gs[b].key,
        gs.contains(v[a]), gs.contains(v[b]), v[a] != v[b], 0 <= a < v.len(), 0 <= b < v.len(),
    ensures v[a].key != v[b].key,
{
    let ga = choose|g: int| 0 <= g < gs.len() && gs[g] == v[a];
    let gb = choose|g: int| 0 <= g < gs.len() && gs[g] == v[b];
    if ga < gb {
        assert(gs[ga].key < gs[gb].key);
    } else if gb < ga {
        assert(gs[gb].key < gs[ga].key);
    }
}

/// The count-sorted groups' prefix with count > 10 is the candidate list.
proof fn lemma_cands_prefix(gs: Seq<Group>, v: Seq<Group>, m: int)
    requires
        forall|a: int, b: int| 0 <= a < b < gs.len() ==> #[trigger] gs[a].key < #[trigger] gs[b].key,
        v.to_multiset() == gs.to_multiset(),
        forall|a: int, b: int| 0 <= a < b < v.len() ==> #[trigger] v[a].count >= #[trigger] v[b].count,
        0 <= m <= v.len(),
        forall|q: int| 0 <= q < m ==> #[trigger] v[q].count > 10,
        m < v.len() ==> v[m].count <= 10,
    ensures cands_ok(gs, v.subrange(0, m)),
{
    reveal(cands_ok);
    let cs = v.subrange(0, m);
    lemma_same_elems(v, gs);
    lemma_perm_nodup(v, gs);
    assert forall|a: int, b: int| 0 <= a < b < cs.len() implies #[trigger] cs[a].key != #[trigger] cs[b].key by {
        assert(v.contains(v[a]) && v.contains(v[b]));
        lemma_distinct_keys(v, gs, a, b);
    }
    assert forall|a: int, b: int| 0 <= a < b < cs.len() implies #[trigger] cs[a].count >= #[trigger] cs[b].count by {
        assert(v[a].count >= v[b].count);
    }
    assert forall|c: int| 0 <= c < cs.len() implies gs.contains(#[trigger] cs[c]) by {
        assert(v.contains(v[c]));
    }
    assert forall|c: int| 0 <= c < cs.len() implies #[trigger] cs[c].count > 10 by {
        assert(v[c].count > 10);
    }
    assert forall|g: int| 0 <= g < gs.len() && #[trigger] gs[g].count > 10 implies cs.contains(gs[g]) by {
        assert(gs.contains(gs[g]));
        assert(v.contains(gs[g]));
        let q = choose|q: int| 0 <= q < v.len() && v[q] == gs[g];
        if q > m {
            assert(v[m].count >= v[q].count);
        }
        assert(cs[q] == gs[g]);
    }
}

/// `pcount` is at most the number of entries.
proof fn lemma_pcount_le(es: Seq<Entry>, p: u64)
    ensures pcount(es, p) <= es.len(),
    decreases es.len(),
{
    if es.len() > 0 {
        lemma_pcount_le(es.drop_last(), p);
    }
}

/// Candidates have valid pair codes and counts that fit `i64`.
pub proof fn lemma_cands_bounds(np: Seq<PartView>, pp: Seq<PartView>, inp: ScanInput, ps: Seq<Literal>, r0: int, r1: int,
    es: Seq<Entry>, gs: Seq<Group>, cs: Seq<Group>)
    requires answer_premises(np, pp, inp, ps, r0, r1, es, gs, cs),
    ensures forall|c: int| 0 <= c < cs.len() ==> (#[trigger] cs[c]).key < N::pair_count(np) && cs[c].count <= 0x7fff_ffff_ffff_ffff,
{
    lemma_group_keys(np, pp, inp, ps, r0, r1, es, gs, cs);
    assert forall|c: int| 0 <= c < cs.len() implies (#[trigger] cs[c]).key < N::pair_count(np) && cs[c].count <= 0x7fff_ffff_ffff_ffff by {
        lemma_cand_facts(np, es, gs, cs, c);
        lemma_pcount_le(es, cs[c].key);
    }
}

/// A key with a positive absolute sum is the key of an entry.
proof fn lemma_pabs_witness(es: Seq<Entry>, p: u64)
    requires pabs(es, p) > 0,
    ensures exists|m: int| 0 <= m < es.len() && (#[trigger] es[m]).key == p,
    decreases es.len(),
{
    if es.len() > 0 {
        if es.last().key == p {
            assert(es[es.len() - 1].key == p);
        } else {
            lemma_pabs_witness(es.drop_last(), p);
            let m = choose|m: int| 0 <= m < es.drop_last().len() && (#[trigger] es.drop_last()[m]).key == p;
            assert(es[m] == es.drop_last()[m]);
        }
    }
}

/// The capacity answer: an entry key whose absolute sum exceeds `i128::MAX` puts the statement outside its
/// capacity domain, for every database bound to the parts.
pub proof fn lemma_capacity_answer(db: Database, np: Seq<PartView>, pp: Seq<PartView>, inp: ScanInput, ps: Seq<Literal>,
    r0: int, r1: int, es: Seq<Entry>, p: u64)
    requires
        db.schema == schema_spec(), db_wf(db), param_domain(ps),
        N::represents(np, crate::stores::num_tvg::declaration::stored_relations(db)),
        P::represents(pp, crate::stores::pre::declaration::stored_relations(db)),
        inp_matches(inp, np, pp, ps), inp.wf(),
        N::num_layout_ok(np), P::pre_layout_ok(pp),
        0 <= r0 <= r1 <= inp.runs,
        forall|r: int| 0 <= r < inp.runs ==> (#[trigger] N::run_uom_of(np, r) == ukey(ps)) == (r0 <= r < r1),
        es == inp.run_ents(r0, r1),
        inp.n <= 0x7fff_ffff_ffff_ffff,
        pabs(es, p) > i128::MAX,
    ensures !crate::gendb_entry::capacity_domain(db, query_spec_at(ps)),
{
    lemma_db_rows(db);
    let (l, r) = (db.tables[1], db.tables[3]);
    super::scan::lemma_run_ents_facts(inp, r0, r1);
    assert(inp.run_start@[r1] <= inp.run_start@[inp.runs as int]);
    lemma_acc_link(db, np, pp, inp, ps, r0, r1, es);
    lemma_pabs_witness(es, p);
    let m = choose|m: int| 0 <= m < es.len() && (#[trigger] es[m]).key == p;
    assert(p < N::pair_count(np));
    lemma_e_to_p(np, es, p);
    let k = keyp(np, p as int);
    reveal(acc_link);
    assert(gcount(lj_spec(ps), lj_rows(l, r), k) == ecount(np, es, k));
    assert(gabs(lj_spec(ps), lj_rows(l, r), k, 1) == eabs(np, es, k));
    assert forall|k2: Row| #[trigger] gcount(lj_spec(ps), lj_rows(l, r), k2) <= crate::spec::limits::int8_max() by {
        lemma_ecount_le(np, es, k2);
    }
    super::capacity::lemma_capacity(db, ps, l, r, k);
    lemma_statement(ps);
}

} // verus!
