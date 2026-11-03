//! The Q21 statement's outcome on a database bound to the parts. Its body (`GroupBy` over the filtered FROM
//! product) evaluates to the normal form's rows when every group count fits int8 (`lemma_body`), and to error 22003
//! when one does not (`lemma_body_count_err`: COUNT beyond int8). A group's count is the sum of the slot counts with
//! its name (`world::lemma_gcount_slots`), so the normal form's rows are exactly the rows `[s_name, gtot(t)]` of the
//! name groups `gs` lists (`lemma_rr_rows`), and a top 100 of those rows under the ORDER BY keys is an allowed
//! output of the statement (`lemma_q21_ordered`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::order::*;
use crate::spec::limits::int8_max;
use crate::spec::relation::*;
use crate::query::query_spec_at;
use crate::link::query::*;
use crate::link::outcome::{lemma_outcome_sorted, lemma_outcome_err};
use crate::bridge::collect::*;
use crate::bridge::order::{keys_ok, key_ok};
use super::common::isum::*;
use super::common::topk::*;
use super::model::*;
use super::side::*;
use super::kernel::counts_ok;
use super::cand::*;
use super::groups::*;
use super::sqlrow::*;
use super::sqllink::*;
use super::typed::*;
use super::bind::db_ok;
use super::world::*;

verus! {

// ------------------------------------------------------------------------------------------------ the body

/// The GROUP BY rows of the normal form (`key ++ COUNT` of every group, first-occurrence order).
pub open spec fn fullrows(g: QuerySpec, xs: Seq<Row>) -> Seq<Row> {
    gkeys(g, xs).map_values(|k: Row| full_row(g, xs, k))
}

/// Every group key of the normal form is one value (`[s_name]`).
proof fn lemma_gk_len(db: Database, nm: Seq<u8>, k: Row)
    requires gkeys(q21_g(db, nm), q21_xs(db)).contains(k),
    ensures k.len() == 1,
{
    let g = q21_g(db, nm);
    let xs = q21_xs(db);
    lemma_gkeys_witness(g, xs, k);
    let t = choose|t: int| 0 <= t < xs.len() && #[trigger] hit(g, xs[t], k);
    assert((g.key)(xs[t]) == k);
}

/// The GROUP BY rows are the result rows (the SELECT list is the GROUP BY row).
proof fn lemma_full_is_result(db: Database, nm: Seq<u8>)
    ensures fullrows(q21_g(db, nm), q21_xs(db)) == result_rows(q21_g(db, nm), q21_xs(db)),
{
    let g = q21_g(db, nm);
    let xs = q21_xs(db);
    let gk = gkeys(g, xs);
    assert forall|i: int| 0 <= i < gk.len() implies #[trigger] full_row(g, xs, gk[i]) == out_row(g, xs, gk[i]) by {
        let k = gk[i];
        assert(gk.contains(k));
        lemma_gk_len(db, nm, k);
        assert(agg_outs(g, xs, k).len() == 1);
        lemma_select_identity(full_row(g, xs, k), g.outs);
    }
    assert(fullrows(g, xs) =~= result_rows(g, xs));
}

/// The statement's body evaluates to the normal form's rows when every group count fits int8.
pub proof fn lemma_body(db: Database, ps: Seq<Literal>, nm: Seq<u8>)
    requires
        db_ok(db),
        ps.len() >= 1,
        ps[0] == Literal::Text(nm),
        forall|k: Row| #[trigger] gcount(q21_g(db, nm), q21_xs(db), k) <= int8_max(),
    ensures
        denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(result_rows(q21_g(db, nm), q21_xs(db))),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_exprs);
    hide(agg_args);
    hide(gkeys);
    let g = q21_g(db, nm);
    let rows = from_rows(db);
    let xs = q21_xs(db);
    lemma_tables_typed(db);
    lemma_q21_shape(ps);
    lemma_from_eval(db);
    lemma_pred_agrees(db, ps, nm);
    lemma_filter_rows(db, q21_from(), rows, q21_cols(), q21_pred(ps), g);
    lemma_keys_args_agree(db, nm);
    lemma_keys_exact(db, nm);
    assert(group_caps(g, xs)) by {
        assert forall|k: Row, j: int| #![trigger gcount(g, xs, k), g.aggs[j]] 0 <= j < g.aggs.len() && g.aggs[j] is Count implies gcount(g, xs, k) <= int8_max() by {}
    }
    lemma_group_query(db, rows, q21_cols(), q21_filter(ps), q21_gkeys(), q21_aggs(), g);
    lemma_full_is_result(db, nm);
}

/// The body is the GROUP BY of the qualifying rows' (key, COUNT argument) sequence.
proof fn lemma_body_groups(db: Database, ps: Seq<Literal>, nm: Seq<u8>)
    requires
        db_ok(db),
        ps.len() >= 1,
        ps[0] == Literal::Text(nm),
    ensures ({
        let g = q21_g(db, nm);
        let xs = q21_xs(db);
        &&& keys_exact(g, xs)
        &&& denote_body(db, query_spec_at(ps)) == group_rows(q21_aggs(), qkeys(g, xs), qrows(g, xs).map_values(|x: Row| arg_vals(g, x)))
    }),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_expr);
    hide(eval_exprs);
    hide(agg_args);
    hide(group_rows);
    let g = q21_g(db, nm);
    let rows = from_rows(db);
    let cols = q21_cols();
    let keys = q21_gkeys();
    let aggs = q21_aggs();
    lemma_tables_typed(db);
    lemma_q21_shape(ps);
    lemma_from_eval(db);
    lemma_pred_agrees(db, ps, nm);
    lemma_filter_rows(db, q21_from(), rows, cols, q21_pred(ps), g);
    lemma_keys_args_agree(db, nm);
    lemma_keys_exact(db, nm);
    let xs = proj_all(rows, cols);
    let kept = keep_true(rows, qual_truths(g, xs));
    let q = qrows(g, xs);
    lemma_kept_rows(g, rows, cols);
    lemma_prepared(db, rows, kept, cols, keys, aggs, g);
    let prep = Seq::new(kept.len(), |i: int| ((g.key)(proj(kept[i], cols)), arg_vals(g, proj(kept[i], cols))));
    assert(prep.map_values(|p: (Row, Row)| p.0) =~= qkeys(g, xs));
    assert(prep.map_values(|p: (Row, Row)| p.1) =~= q.map_values(|x: Row| arg_vals(g, x)));
    lemma_groupby_unfold(db, q21_filter(ps), keys, aggs, kept, prep);
}

/// GROUP BY with COUNT(*): when some group's count is beyond int8, the outcome is error 22003 (every group's COUNT
/// either succeeds or fails with that error, so the first failure is it).
proof fn lemma_groups_count_err(g: QuerySpec, xs: Seq<Row>, k0: Row)
    requires
        g.aggs == seq![AggKind::Count],
        keys_exact(g, xs),
        gcount(g, xs, k0) > int8_max(),
    ensures
        group_rows(seq![Agg::CountStar], qkeys(g, xs), qrows(g, xs).map_values(|x: Row| arg_vals(g, x)))
            == Err::<Seq<Row>, SqlError>(SqlError::NumericValueOutOfRange),
{
    let aggs = seq![Agg::CountStar];
    let e = SqlError::NumericValueOutOfRange;
    let ks = qkeys(g, xs);
    let avs = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    let pool = key_pool(g, xs);
    lemma_pool_exact(g, xs);
    assert forall|i: int| 0 <= i < qkeys(g, xs).len() implies pool.contains(#[trigger] qkeys(g, xs)[i]) by {
        assert(pool[i] == qkeys(g, xs)[i]);
    }
    lemma_distinct_gkeys(g, xs, pool);
    let ds = gkeys(g, xs);
    lemma_gkeys(g, xs);
    let grs = Seq::new(ds.len(), |gi: int|
        match agg_row(aggs, group_members(ks, avs, ds[gi])) {
            Ok(a) => Ok(ds[gi] + a),
            Err(err) => Err(err),
        });
    assert forall|gi: int| 0 <= gi < grs.len() implies #[trigger] grs[gi] is Ok || grs[gi] == Err::<Row, SqlError>(e) by {
        let ms = group_members(ks, avs, ds[gi]);
        crate::link::capacity::lemma_count_value(Agg::CountStar, column(ms, 0));
        let vr = Seq::new(aggs.len(), |j: int| agg_value(aggs[j], column(ms, j)));
        assert(vr =~= seq![agg_value(Agg::CountStar, column(ms, 0))]);
        if agg_value(Agg::CountStar, column(ms, 0)) is Ok {
            lemma_collect_all(vr, seq![agg_value(Agg::CountStar, column(ms, 0))->Ok_0]);
        } else {
            lemma_collect_first_err(vr, 0);
        }
    }
    assert(ds.contains(k0));
    let g0 = choose|gi: int| 0 <= gi < ds.len() && ds[gi] == k0;
    assert(grs[g0] == Err::<Row, SqlError>(e)) by {
        assert(pool.contains(k0));
        lemma_group_members(g, xs, k0, pool);
        let ms = group_members(ks, avs, k0);
        lemma_members_col(g, xs, k0, 0);
        crate::link::capacity::lemma_count_value(Agg::CountStar, column(ms, 0));
        let vr = Seq::new(aggs.len(), |j: int| agg_value(aggs[j], column(ms, j)));
        assert(vr =~= seq![agg_value(Agg::CountStar, column(ms, 0))]);
        lemma_collect_first_err(vr, 0);
    }
    crate::link::capacity::lemma_collect_uniform_err(grs, e, g0);
}

/// A group count beyond int8 makes the statement's outcome error 22003.
pub proof fn lemma_body_count_err(db: Database, ps: Seq<Literal>, nm: Seq<u8>, k0: Row)
    requires
        db_ok(db),
        ps.len() >= 1,
        ps[0] == Literal::Text(nm),
        gcount(q21_g(db, nm), q21_xs(db), k0) > int8_max(),
    ensures
        ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange)),
{
    lemma_body_groups(db, ps, nm);
    lemma_groups_count_err(q21_g(db, nm), q21_xs(db), k0);
    lemma_outcome_err(db, query_spec_at(ps), SqlError::NumericValueOutOfRange);
}

// ------------------------------------------------------------------------------------------------ the groups

/// Every slot has a first slot of its name at or before it.
pub proof fn lemma_first_exists(sc: SCols, srows: Seq<usize>, t: int)
    requires 0 <= t,
    ensures exists|u: int| 0 <= u <= t && first(sc, srows, u) && slot_name(sc, srows, u) == slot_name(sc, srows, t),
    decreases t,
{
    if !first(sc, srows, t) {
        let v = choose|v: int| 0 <= v < t && #[trigger] slot_name(sc, srows, v) == slot_name(sc, srows, t);
        lemma_first_exists(sc, srows, v);
        let u = choose|u: int| 0 <= u <= v && first(sc, srows, u) && slot_name(sc, srows, u) == slot_name(sc, srows, v);
        assert(0 <= u <= t && first(sc, srows, u) && slot_name(sc, srows, u) == slot_name(sc, srows, t));
    } else {
        assert(0 <= t <= t && first(sc, srows, t) && slot_name(sc, srows, t) == slot_name(sc, srows, t));
    }
}

/// The slot facts every bound database shares.
pub open spec fn slots_res(c: Cols, sc: SCols, f: int, nm: Seq<u8>, nks: Seq<i64>, nwit: Seq<int>, srows: Seq<usize>,
    skeys: Seq<i64>, tot: Seq<usize>) -> bool {
    &&& nks_ok(sc, nm, nks, nwit)
    &&& slots_ok(sc, nks, srows, skeys)
    &&& counts_ok(c, f, skeys, tot, 0, c.n_l as int)
    &&& tot.len() == srows.len()
}

/// A group with a nonzero count is a slot name's, and its count is the slot name group's `gtot` at the name's first
/// slot.
pub proof fn lemma_group_slot(db: Database, fparts: Seq<PartView>, sparts: Seq<PartView>, c: Cols, sc: SCols,
    doffs: Seq<u64>, dbytes: Seq<u8>, f: int, nm: Seq<u8>, nks: Seq<i64>, nwit: Seq<int>, srows: Seq<usize>,
    skeys: Seq<i64>, tot: Seq<usize>, k: Row)
    requires
        world_ok(db, fparts, sparts, c, sc, doffs, dbytes, f),
        slots_res(c, sc, f, nm, nks, nwit, srows, skeys, tot),
        gcount(q21_g(db, nm), q21_xs(db), k) > 0,
    ensures
        exists|t: int| 0 <= t < srows.len() && first(sc, srows, t) && k == seq![Val::Text(slot_name(sc, srows, t))]
            && gcount(q21_g(db, nm), q21_xs(db), k) == gtot(sc, srows, tot, t),
{
    lemma_gcount_slots(db, fparts, sparts, c, sc, doffs, dbytes, f, nm, nks, nwit, srows, skeys, tot, k);
    let tt = tterm(sc, srows, tot, k);
    if forall|t: int| 0 <= t < srows.len() ==> #[trigger] tt(t) == 0 {
        lemma_isum_zero(srows.len() as int, tt);
    }
    let t1 = choose|t: int| !(0 <= t < srows.len() ==> #[trigger] tt(t) == 0);
    assert(k == seq![Val::Text(slot_name(sc, srows, t1))]);
    lemma_first_exists(sc, srows, t1);
    let u = choose|u: int| 0 <= u <= t1 && first(sc, srows, u) && slot_name(sc, srows, u) == slot_name(sc, srows, t1);
    lemma_tterm_gtot(sc, srows, tot, u);
    assert(k == seq![Val::Text(slot_name(sc, srows, u))]);
}

/// The listed groups' counts are their slots' name groups' counts.
pub proof fn lemma_slot_group(db: Database, fparts: Seq<PartView>, sparts: Seq<PartView>, c: Cols, sc: SCols,
    doffs: Seq<u64>, dbytes: Seq<u8>, f: int, nm: Seq<u8>, nks: Seq<i64>, nwit: Seq<int>, srows: Seq<usize>,
    skeys: Seq<i64>, tot: Seq<usize>, t: int)
    requires
        world_ok(db, fparts, sparts, c, sc, doffs, dbytes, f),
        slots_res(c, sc, f, nm, nks, nwit, srows, skeys, tot),
        0 <= t < srows.len(),
    ensures
        gcount(q21_g(db, nm), q21_xs(db), seq![Val::Text(slot_name(sc, srows, t))]) == gtot(sc, srows, tot, t),
{
    let k = seq![Val::Text(slot_name(sc, srows, t))];
    lemma_gcount_slots(db, fparts, sparts, c, sc, doffs, dbytes, f, nm, nks, nwit, srows, skeys, tot, k);
    lemma_tterm_gtot(sc, srows, tot, t);
}

/// Every group count fits int8 when the listed groups' do.
pub proof fn lemma_caps(db: Database, fparts: Seq<PartView>, sparts: Seq<PartView>, c: Cols, sc: SCols,
    doffs: Seq<u64>, dbytes: Seq<u8>, f: int, nm: Seq<u8>, nks: Seq<i64>, nwit: Seq<int>, srows: Seq<usize>,
    skeys: Seq<i64>, tot: Seq<usize>, gs: Seq<Cand>)
    requires
        world_ok(db, fparts, sparts, c, sc, doffs, dbytes, f),
        slots_res(c, sc, f, nm, nks, nwit, srows, skeys, tot),
        gs_ok(sc, srows, tot, gs),
    ensures
        forall|k: Row| #[trigger] gcount(q21_g(db, nm), q21_xs(db), k) <= int8_max(),
{
    assert forall|k: Row| #[trigger] gcount(q21_g(db, nm), q21_xs(db), k) <= int8_max() by {
        if gcount(q21_g(db, nm), q21_xs(db), k) > 0 {
            lemma_group_slot(db, fparts, sparts, c, sc, doffs, dbytes, f, nm, nks, nwit, srows, skeys, tot, k);
            let t = choose|t: int| 0 <= t < srows.len() && first(sc, srows, t) && k == seq![Val::Text(slot_name(sc, srows, t))]
                && gcount(q21_g(db, nm), q21_xs(db), k) == gtot(sc, srows, tot, t);
            let i = choose|i: int| 0 <= i < gs.len() && (#[trigger] gs[i]).t == t;
        }
    }
}

// ------------------------------------------------------------------------------------------------ the rows

/// The candidate rows of the first `n` listed groups.
pub open spec fn all_rows(sc: SCols, srows: Seq<usize>, gs: Seq<Cand>, n: int) -> Seq<Row> {
    cands_view(sc, srows, gs, n)
}

/// The listed groups' rows are distinct (different first slots have different names) and their ORDER BY keys are in
/// their families.
pub proof fn lemma_all_wf(sc: SCols, srows: Seq<usize>, tot: Seq<usize>, gs: Seq<Cand>, n: int)
    requires gs_ok(sc, srows, tot, gs), 0 <= n <= gs.len(),
    ensures rel_wf(q21_keys(), q21_fams(), all_rows(sc, srows, gs, n)),
{
    let s = all_rows(sc, srows, gs, n);
    assert forall|a: int, b: int| 0 <= a < s.len() && 0 <= b < s.len() && a != b implies s[a] != s[b] by {
        let (ta, tb) = (gs[a].t as int, gs[b].t as int);
        if a < b {
            assert(ta < tb);
            assert(first(sc, srows, tb));
            assert(slot_name(sc, srows, ta) != slot_name(sc, srows, tb));
        } else {
            assert(tb < ta);
            assert(first(sc, srows, ta));
            assert(slot_name(sc, srows, tb) != slot_name(sc, srows, ta));
        }
        assert(s[a][0] != s[b][0]);
    }
    assert forall|i: int| 0 <= i < s.len() implies keys_ok(q21_keys(), q21_fams(), #[trigger] s[i]) by {
        lemma_cand_cmp(sc, srows, gs[i], gs[i]);
    }
}

/// The normal form's rows are the listed groups' rows, without duplicates.
pub proof fn lemma_rr_rows(db: Database, fparts: Seq<PartView>, sparts: Seq<PartView>, c: Cols, sc: SCols,
    doffs: Seq<u64>, dbytes: Seq<u8>, f: int, nm: Seq<u8>, nks: Seq<i64>, nwit: Seq<int>, srows: Seq<usize>,
    skeys: Seq<i64>, tot: Seq<usize>, gs: Seq<Cand>)
    requires
        world_ok(db, fparts, sparts, c, sc, doffs, dbytes, f),
        slots_res(c, sc, f, nm, nks, nwit, srows, skeys, tot),
        gs_ok(sc, srows, tot, gs),
    ensures
        result_rows(q21_g(db, nm), q21_xs(db)).no_duplicates(),
        forall|r: Row| #[trigger] result_rows(q21_g(db, nm), q21_xs(db)).contains(r)
            <==> all_rows(sc, srows, gs, gs.len() as int).contains(r),
{
    let g = q21_g(db, nm);
    let xs = q21_xs(db);
    let gk = gkeys(g, xs);
    let rr = result_rows(g, xs);
    let al = all_rows(sc, srows, gs, gs.len() as int);
    lemma_gkeys(g, xs);
    assert forall|i: int| 0 <= i < gk.len() implies #[trigger] rr[i] == seq![gk[i][0], Val::Int(gcount(g, xs, gk[i]) as int)] by {
        let k = gk[i];
        assert(gk.contains(k));
        lemma_gk_len(db, nm, k);
        assert(agg_outs(g, xs, k) =~= seq![Val::Int(gcount(g, xs, k) as int)]);
        lemma_select_identity(full_row(g, xs, k), g.outs);
        assert(full_row(g, xs, k) =~= seq![k[0], Val::Int(gcount(g, xs, k) as int)]);
    }
    assert forall|r: Row| #[trigger] rr.contains(r) <==> al.contains(r) by {
        if rr.contains(r) {
            let i = choose|i: int| 0 <= i < rr.len() && rr[i] == r;
            let k = gk[i];
            assert(gk.contains(k));
            lemma_group_slot(db, fparts, sparts, c, sc, doffs, dbytes, f, nm, nks, nwit, srows, skeys, tot, k);
            let t = choose|t: int| 0 <= t < srows.len() && first(sc, srows, t) && k == seq![Val::Text(slot_name(sc, srows, t))]
                && gcount(g, xs, k) == gtot(sc, srows, tot, t);
            let j = choose|j: int| 0 <= j < gs.len() && (#[trigger] gs[j]).t == t;
            assert(al[j] == cand_row(sc, srows, gs[j]));
            assert(al[j] =~= r);
        }
        if al.contains(r) {
            let j = choose|j: int| 0 <= j < al.len() && al[j] == r;
            let t = gs[j].t as int;
            let k = seq![Val::Text(slot_name(sc, srows, t))];
            lemma_slot_group(db, fparts, sparts, c, sc, doffs, dbytes, f, nm, nks, nwit, srows, skeys, tot, t);
            assert(gk.contains(k));
            let i = choose|i: int| 0 <= i < gk.len() && gk[i] == k;
            assert(rr[i] =~= r);
        }
    }
    assert forall|a: int, b: int| 0 <= a < rr.len() && 0 <= b < rr.len() && a != b implies rr[a] != rr[b] by {
        let (ka, kb) = (gk[a], gk[b]);
        assert(gk.contains(ka) && gk.contains(kb));
        lemma_gk_len(db, nm, ka);
        lemma_gk_len(db, nm, kb);
        if rr[a] == rr[b] {
            assert(ka =~= kb);
        }
    }
}

/// A top 100 of the listed groups' rows is an allowed output of the statement on every such database.
pub proof fn lemma_q21_ordered(db: Database, fparts: Seq<PartView>, sparts: Seq<PartView>, c: Cols, sc: SCols,
    doffs: Seq<u64>, dbytes: Seq<u8>, f: int, ps: Seq<Literal>, nm: Seq<u8>, nks: Seq<i64>, nwit: Seq<int>,
    srows: Seq<usize>, skeys: Seq<i64>, tot: Seq<usize>, gs: Seq<Cand>, out: Seq<Row>)
    requires
        world_ok(db, fparts, sparts, c, sc, doffs, dbytes, f),
        slots_res(c, sc, f, nm, nks, nwit, srows, skeys, tot),
        gs_ok(sc, srows, tot, gs),
        ps.len() >= 1,
        ps[0] == Literal::Text(nm),
        topk_ok(q21_keys(), q21_fams(), 100, out, all_rows(sc, srows, gs, gs.len() as int)),
    ensures ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    let all = all_rows(sc, srows, gs, gs.len() as int);
    lemma_caps(db, fparts, sparts, c, sc, doffs, dbytes, f, nm, nks, nwit, srows, skeys, tot, gs);
    lemma_body(db, ps, nm);
    lemma_rr_rows(db, fparts, sparts, c, sc, doffs, dbytes, f, nm, nks, nwit, srows, skeys, tot, gs);
    lemma_all_wf(sc, srows, tot, gs, gs.len() as int);
    lemma_topk_ordered(q21_keys(), q21_fams(), 100, out, all);
    let pp = out + sort_rows(q21_keys(), rest_of(all, out));
    let rr = result_rows(q21_g(db, nm), q21_xs(db));
    lemma_nodup_same_multiset(rr, all);
    lemma_q21_shape(ps);
    lemma_outcome_sorted(db, query_spec_at(ps), rr, pp);
}

/// A listed group's count beyond int8 is the statement's error 22003 on every such database.
pub proof fn lemma_q21_count_err(db: Database, fparts: Seq<PartView>, sparts: Seq<PartView>, c: Cols, sc: SCols,
    doffs: Seq<u64>, dbytes: Seq<u8>, f: int, ps: Seq<Literal>, nm: Seq<u8>, nks: Seq<i64>, nwit: Seq<int>,
    srows: Seq<usize>, skeys: Seq<i64>, tot: Seq<usize>, t: int)
    requires
        world_ok(db, fparts, sparts, c, sc, doffs, dbytes, f),
        slots_res(c, sc, f, nm, nks, nwit, srows, skeys, tot),
        0 <= t < srows.len(),
        gtot(sc, srows, tot, t) > i64::MAX,
        ps.len() >= 1,
        ps[0] == Literal::Text(nm),
    ensures ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange)),
{
    lemma_slot_group(db, fparts, sparts, c, sc, doffs, dbytes, f, nm, nks, nwit, srows, skeys, tot, t);
    lemma_body_count_err(db, ps, nm, seq![Val::Text(slot_name(sc, srows, t))]);
}

} // verus!
