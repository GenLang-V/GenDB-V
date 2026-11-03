//! The statement's meaning on a database whose tables are the stored rows, given the fold over all contribution
//! records: the body (HAVING over the GroupBy) is the rows of the groups of `order` with at least two distinct
//! ciks (`lemma_body`); the first 500 sorted candidates are an allowed output (`lemma_answer`); and a group whose
//! sum left `i128`, or whose average is outside the division domain, puts the database outside the capacity domain
//! (`lemma_capacity`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::relation::*;
use crate::spec::order::*;
use crate::spec::scalar::*;
use crate::spec::aggs::avg::*;
use crate::spec::fns::div::*;
use crate::spec::equality::*;
use crate::bridge::order::*;
use crate::exec::relational::domain::*;
use crate::link::join::keep;
use crate::link::outcome::lemma_outcome_sorted;
use crate::agent::common::distinct::*;
use crate::agent::cols::*;
use crate::agent::ents::*;
use crate::agent::groups::*;
use crate::agent::fold::*;
use crate::agent::sem::*;
use crate::agent::join::*;
use crate::agent::decomp::*;
use crate::agent::group::*;
use crate::agent::topk::*;

verus! {

/// The facts about one call that every bound database shares: the context, the entries, the records (all
/// contributions) and the fold over them (hidden; `lemma_run_facts`).
#[verifier::opaque]
pub open spec fn run_ok(c: Ctx, ps: Seq<Literal>, ents: Seq<(usize, usize, usize)>, recs: Seq<Rec>, gr: &Groups,
    order: Seq<usize>, seen: Seq<bool>, cnt: Seq<usize>, sum: Seq<i128>, ovf: Seq<bool>, dcnt: Seq<usize>, pseen: Seq<bool>) -> bool
{
    &&& ctx_ok(c) && lits_ok(c, ps) && ents_ok(c, ents) && groups_ok(c, ents, gr)
    &&& c.n < usize::MAX && ents.len() < usize::MAX
    &&& recs == crate::agent::scan::contrib(c, ents, 0, c.n)
    &&& fold_inv(c, ents, gr, recs, order, seen, cnt, sum, ovf, dcnt, pseen)
    &&& forall|g: int| 0 <= g < seen.len() && #[trigger] seen[g] ==> cnt[g] > 0
}

/// The plain facts of a run: vector lengths, group ids in range, representatives, bounded distinct counts.
pub proof fn lemma_run_facts(c: Ctx, ps: Seq<Literal>, ents: Seq<(usize, usize, usize)>, recs: Seq<Rec>, gr: &Groups,
    order: Seq<usize>, seen: Seq<bool>, cnt: Seq<usize>, sum: Seq<i128>, ovf: Seq<bool>, dcnt: Seq<usize>, pseen: Seq<bool>)
    requires run_ok(c, ps, ents, recs, gr, order, seen, cnt, sum, ovf, dcnt, pseen),
    ensures
        ctx_ok(c), lits_ok(c, ps), reps_ok(c, gr.reps@),
        cnt.len() == gr.reps@.len() && sum.len() == gr.reps@.len() && ovf.len() == gr.reps@.len() && dcnt.len() == gr.reps@.len(),
        forall|x: int| 0 <= x < order.len() ==> (#[trigger] order[x] as int) < gr.reps@.len(),
        forall|g: int| 0 <= g < gr.reps@.len() ==> #[trigger] dcnt[g] <= 0x1_0000_0000,
{
    reveal(run_ok);
    assert(recs_ok(ents, recs)) by {
        crate::agent::group::lemma_contrib_mem(c, ents, 0, c.n);
        assert forall|q: int| 0 <= q < recs.len() implies ((#[trigger] recs[q]).1 as int) < ents.len() by {}
    }
    assert forall|g: int| 0 <= g < gr.reps@.len() implies #[trigger] dcnt[g] <= 0x1_0000_0000 by {
        crate::agent::group::lemma_dcnt_bound(c, ents, gr, recs, cnt, sum, ovf, g);
    }
}

/// The having condition of a group.
pub open spec fn having(dcnt: Seq<usize>) -> spec_fn(usize) -> bool {
    |g: usize| dcnt[g as int] >= 2
}

/// `filt` over functions that agree on the ids.
proof fn lemma_filt_ext(ids: Seq<usize>, f: spec_fn(usize) -> bool, h: spec_fn(usize) -> bool)
    requires forall|t: int| 0 <= t < ids.len() ==> f(#[trigger] ids[t]) == h(ids[t]),
    ensures filt(ids, f) == filt(ids, h),
    decreases ids.len(),
{
    if ids.len() > 0 {
        let d = ids.drop_last();
        assert forall|t: int| 0 <= t < d.len() implies f(#[trigger] d[t]) == h(d[t]) by {
            assert(d[t] == ids[t]);
        }
        lemma_filt_ext(d, f, h);
        assert(ids[ids.len() - 1] == ids.last());
    }
}

/// The where/group stages of a bound database (shared by the answer and the capacity proofs).
proof fn lemma_stages(db: Database, c: Ctx, ps: Seq<Literal>, ents: Seq<(usize, usize, usize)>, recs: Seq<Rec>)
    requires db_ok(db, c), lits_ok(c, ps), ents_ok(c, ents), c.n < usize::MAX, ents.len() < usize::MAX,
        recs == crate::agent::scan::contrib(c, ents, 0, c.n),
    ensures
        eval_query(db, Seq::empty(), q_where(ps)) == Ok::<Relation, SqlError>(rec_rows(c, ents, recs)),
        recs_facts(c, ents, recs),
{
    lemma_eval_where_node(db, c, ps);
    lemma_where_rows(db, c, ps, ents);
    lemma_contrib_mem(c, ents, 0, c.n);
}

/// The body: the GroupBy rows of the groups with at least two distinct ciks, in group order.
pub proof fn lemma_body(db: Database, c: Ctx, ps: Seq<Literal>, ents: Seq<(usize, usize, usize)>, recs: Seq<Rec>, gr: &Groups,
    order: Seq<usize>, seen: Seq<bool>, cnt: Seq<usize>, sum: Seq<i128>, ovf: Seq<bool>, dcnt: Seq<usize>, pseen: Seq<bool>)
    requires
        db_ok(db, c), run_ok(c, ps, ents, recs, gr, order, seen, cnt, sum, ovf, dcnt, pseen),
        forall|x: int| 0 <= x < order.len() ==> !ovf[#[trigger] order[x] as int]
            && num_div_fits(sum[order[x] as int] as int, 4, cnt[order[x] as int] as int, 0),
    ensures
        eval_query(db, Seq::empty(), q_body(ps))
            == Ok::<Relation, SqlError>(grows(c, gr.reps@, sum, cnt, dcnt, filt(order, having(dcnt)))),
{
    reveal(run_ok);
    lemma_stages(db, c, ps, ents, recs);
    lemma_group_node(db, c, ps, ents, recs, gr, order, seen, cnt, sum, ovf, dcnt, pseen);
    let m = |g: usize| g_row(c, gr.reps@, sum, cnt, dcnt, g as int);
    let rows = order.map_values(m);
    assert forall|q: int| 0 <= q < rows.len() implies #[trigger] eval_pred(db, rows[q], p_having()) is Ok
        && (eval_pred(db, rows[q], p_having()) == Ok::<Truth, SqlError>(Truth::True)) == (dcnt[order[q] as int] >= 2) by {
        lemma_g_row_sum(c, gr.reps@, sum, cnt, dcnt, order[q] as int);
        lemma_int_lit(db, rows[q], CmpOp::Ge, 3, 2);
    }
    lemma_filter(db, q_group(ps), rows, p_having());
    lemma_keep_ids(order, m, holds(db, p_having()));
    assert forall|t: int| 0 <= t < order.len() implies (|g: usize| holds(db, p_having())(m(g)))(#[trigger] order[t])
        == having(dcnt)(order[t]) by {
        assert(rows[t] == m(order[t]));
    }
    lemma_filt_ext(order, |g: usize| holds(db, p_having())(m(g)), having(dcnt));
}

/// The candidates at threshold `t` and the rows below it.
pub open spec fn cand_at(dcnt: Seq<usize>, sum: Seq<i128>, t: int) -> spec_fn(usize) -> bool {
    |g: usize| having(dcnt)(g) && sum[g as int] >= t
}

pub open spec fn rest_at(dcnt: Seq<usize>, sum: Seq<i128>, t: int) -> spec_fn(usize) -> bool {
    |g: usize| having(dcnt)(g) && !(sum[g as int] >= t)
}

/// A row of a stable sort is a row of its input.
proof fn lemma_sorted_member(keys: Seq<OrderKey>, v: Seq<Row>, i: int)
    requires 0 <= i < sort_rows(keys, v).len(), sort_rows(keys, v).to_multiset() == v.to_multiset(),
    ensures v.contains(sort_rows(keys, v)[i]),
{
    let s = sort_rows(keys, v);
    s.to_multiset_ensures();
    v.to_multiset_ensures();
    assert(s.contains(s[i]));
    assert(s.to_multiset().count(s[i]) > 0);
    assert(v.to_multiset().count(s[i]) > 0);
}

/// The first `min(500, |cand|)` sorted candidates are an allowed output, when there are at least 500 candidates or
/// the threshold is the smallest `i128`.
pub proof fn lemma_answer(db: Database, c: Ctx, ps: Seq<Literal>, reps: Seq<(usize, usize)>, order: Seq<usize>,
    sum: Seq<i128>, cnt: Seq<usize>, dcnt: Seq<usize>, t: int, out: Seq<Row>)
    requires
        eval_query(db, Seq::empty(), q_body(ps)) == Ok::<Relation, SqlError>(grows(c, reps, sum, cnt, dcnt, filt(order, having(dcnt)))),
        filt(order, cand_at(dcnt, sum, t)).len() >= 500 || t == i128::MIN,
        forall|x: int| 0 <= x < order.len() ==> (#[trigger] order[x] as int) < sum.len(),
        out == sort_rows(order_keys(), grows(c, reps, sum, cnt, dcnt, filt(order, cand_at(dcnt, sum, t)))).take(
            if filt(order, cand_at(dcnt, sum, t)).len() < 500 { filt(order, cand_at(dcnt, sum, t)).len() as int } else { 500 }),
    ensures ordered_ok(db, crate::query::query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    lemma_query_shape(ps);
    let oq = crate::query::query_spec_at(ps);
    let keys = order_keys();
    let fams = row_fams();
    let cand = filt(order, cand_at(dcnt, sum, t));
    let rest = filt(order, rest_at(dcnt, sum, t));
    let vc = grows(c, reps, sum, cnt, dcnt, cand);
    let vr = grows(c, reps, sum, cnt, dcnt, rest);
    let vh = grows(c, reps, sum, cnt, dcnt, filt(order, having(dcnt)));
    assert(all_keys_ok(keys, fams, vc)) by {
        assert forall|i: int| 0 <= i < vc.len() implies keys_ok(keys, fams, #[trigger] vc[i]) by {
            lemma_g_row_sum(c, reps, sum, cnt, dcnt, cand[i] as int);
            lemma_row_keys_ok(vc[i], sum[cand[i] as int] as int);
        }
    }
    assert(all_keys_ok(keys, fams, vr)) by {
        assert forall|i: int| 0 <= i < vr.len() implies keys_ok(keys, fams, #[trigger] vr[i]) by {
            lemma_g_row_sum(c, reps, sum, cnt, dcnt, rest[i] as int);
            lemma_row_keys_ok(vr[i], sum[rest[i] as int] as int);
        }
    }
    lemma_sort_rows(keys, fams, vc);
    lemma_sort_rows(keys, fams, vr);
    let sc = sort_rows(keys, vc);
    let sr = sort_rows(keys, vr);
    lemma_filt_mem(order, cand_at(dcnt, sum, t));
    lemma_filt_mem(order, rest_at(dcnt, sum, t));
    // Every candidate row has a sum of at least `t`, every rest row less: the candidates sort first.
    assert forall|i: int, j: int| 0 <= i < sc.len() && 0 <= j < sr.len() implies keys_cmp(keys, #[trigger] sc[i], #[trigger] sr[j]) <= 0 by {
        lemma_sorted_member(keys, vc, i);
        lemma_sorted_member(keys, vr, j);
        let a = choose|a: int| 0 <= a < vc.len() && vc[a] == sc[i];
        let b = choose|b: int| 0 <= b < vr.len() && vr[b] == sr[j];
        lemma_g_row_sum(c, reps, sum, cnt, dcnt, cand[a] as int);
        lemma_g_row_sum(c, reps, sum, cnt, dcnt, rest[b] as int);
        assert(sum[cand[a] as int] >= t);
        assert(!(sum[rest[b] as int] >= t));
        lemma_keys_cmp_sum(sc[i], sr[j], sum[cand[a] as int] as int, sum[rest[b] as int] as int);
    }
    lemma_sorted_concat(keys, sc, sr);
    let p = sc + sr;
    // The two parts together are the HAVING rows.
    lemma_filt_partition(order, having(dcnt), |g: usize| sum[g as int] >= t, |g: usize| g_row(c, reps, sum, cnt, dcnt, g as int));
    assert(filt(order, |g: usize| having(dcnt)(g) && (|g: usize| sum[g as int] >= t)(g)) == cand) by {
        lemma_filt_ext(order, |g: usize| having(dcnt)(g) && (|g: usize| sum[g as int] >= t)(g), cand_at(dcnt, sum, t));
    }
    assert(filt(order, |g: usize| having(dcnt)(g) && !(|g: usize| sum[g as int] >= t)(g)) == rest) by {
        lemma_filt_ext(order, |g: usize| having(dcnt)(g) && !(|g: usize| sum[g as int] >= t)(g), rest_at(dcnt, sum, t));
    }
    vstd::seq_lib::lemma_multiset_commutative(sc, sr);
    assert(p.to_multiset() == vh.to_multiset());
    lemma_outcome_sorted(db, oq, vh, p);
    // The first 500 rows of `p` are the first sorted candidates.
    if t == i128::MIN {
        assert(rest.len() == 0) by {
            if rest.len() > 0 {
                assert(!(sum[rest[0] as int] >= i128::MIN));
            }
        }
        assert(sr.len() == 0) by {
            sr.to_multiset_ensures();
            vr.to_multiset_ensures();
        }
        assert(p =~= sc);
    }
    assert(sc.len() == vc.len()) by {
        sc.to_multiset_ensures();
        vc.to_multiset_ensures();
    }
    assert(slice_rows(p, 0, Some(500nat)) =~= out);
}

// ------------------------------------------------------------------------------------------------ capacity

/// A group's members: `[cik, value, value]` rows; the sum and average columns are scale-4 numerics.
proof fn lemma_member_cols(c: Ctx, ents: Seq<(usize, usize, usize)>, gr: &Groups, recs: Seq<Rec>,
    cnt: Seq<usize>, sum: Seq<i128>, ovf: Seq<bool>, g: int)
    requires groups_ok(c, ents, gr), recs_ok(ents, recs), acc_inv(c, ents, gr, recs, cnt, sum, ovf), 0 <= g < gr.reps@.len(),
    ensures ({
        let m = members(c, ents, gr.reps@, recs, g);
        &&& all_num(column(m, 1), 4) && all_num(column(m, 2), 4)
        &&& all_of_kind(NumKind::Numeric, column(m, 1)) && all_of_kind(NumKind::Numeric, column(m, 2))
        &&& count_non_null(column(m, 2)) == m.len()
    }),
{
    let m = members(c, ents, gr.reps@, recs, g);
    lemma_members_cols(c, ents, gr, recs, g);
    lemma_num_kind(column(m, 1));
}

/// Every group's aggregates succeed inside their capacity conditions.
proof fn lemma_ok_inside(c: Ctx, ents: Seq<(usize, usize, usize)>, gr: &Groups, recs: Seq<Rec>,
    cnt: Seq<usize>, sum: Seq<i128>, ovf: Seq<bool>, g: int)
    requires groups_ok(c, ents, gr), recs_ok(ents, recs), acc_inv(c, ents, gr, recs, cnt, sum, ovf), 0 <= g < gr.reps@.len(),
    ensures crate::link::capacity::aggs_ok_inside(g_aggs(), members(c, ents, gr.reps@, recs, g)),
{
    let m = members(c, ents, gr.reps@, recs, g);
    let aggs = g_aggs();
    lemma_member_cols(c, ents, gr, recs, cnt, sum, ovf, g);
    lemma_dcnt_bound(c, ents, gr, recs, cnt, sum, ovf, g);
    assert forall|j: int| 0 <= j < aggs.len() && #[trigger] fits_agg_value(aggs[j], column(m, j))
        implies agg_value(aggs[j], column(m, j)) is Ok by {
        if j == 0 {
            assert(agg_value(aggs[0], column(m, 0)) == agg_value(Agg::Count(Expr::Col(10)), distinct_vals(column(m, 0))));
            assert(int_in_range(IntKind::Int8, distinct_vals(column(m, 0)).len() as int));
        } else if j == 1 {
            crate::link::capacity::lemma_sum_inside_ok(NumKind::Numeric, Expr::Col(7), column(m, 1));
        } else {
            crate::link::capacity::lemma_avg_inside_ok(NumKind::Numeric, Expr::Col(7), column(m, 2));
        }
    }
}

/// A group of `order` whose sum left `i128` or whose average is outside the division domain: the database is
/// outside the capacity domain.
pub proof fn lemma_capacity(db: Database, c: Ctx, ps: Seq<Literal>, ents: Seq<(usize, usize, usize)>, recs: Seq<Rec>, gr: &Groups,
    order: Seq<usize>, seen: Seq<bool>, cnt: Seq<usize>, sum: Seq<i128>, ovf: Seq<bool>, dcnt: Seq<usize>, pseen: Seq<bool>, x: int)
    requires
        db_ok(db, c), run_ok(c, ps, ents, recs, gr, order, seen, cnt, sum, ovf, dcnt, pseen),
        0 <= x < order.len(),
        ovf[order[x] as int] || !num_div_fits(sum[order[x] as int] as int, 4, cnt[order[x] as int] as int, 0),
    ensures !crate::gendb_entry::capacity_domain(db, crate::query::query_spec_at(ps)),
{
    reveal(run_ok);
    lemma_query_shape(ps);
    lemma_stages(db, c, ps, ents, recs);
    assert(recs_ok(ents, recs)) by {
        assert forall|q: int| 0 <= q < recs.len() implies ((#[trigger] recs[q]).1 as int) < ents.len() by {}
    }
    lemma_group_inputs(db, c, ps, ents, recs);
    let ks = keys_of(c, ents, recs);
    let args = args_of(c, ents, recs);
    let rows = rec_rows(c, ents, recs);
    let d = distinct_rows(ks);
    let g = order[x] as int;
    assert(d == order.map_values(|g: usize| grow_row(c, gr.reps@, g as int)));
    assert(d[x] == grow_row(c, gr.reps@, g));
    let m = members(c, ents, gr.reps@, recs, g);
    assert(group_members(ks, args, d[x]) == m);
    assert(order.contains(order[x]));
    assert(seen[g]);
    lemma_member_cols(c, ents, gr, recs, cnt, sum, ovf, g);
    assert forall|h: int| 0 <= h < d.len() implies #[trigger] crate::link::capacity::aggs_ok_inside(g_aggs(), group_members(ks, args, d[h])) by {
        assert(d[h] == grow_row(c, gr.reps@, order[h] as int));
        lemma_ok_inside(c, ents, gr, recs, cnt, sum, ovf, order[h] as int);
    }
    let c1 = column(m, 1);
    crate::link::capacity::lemma_num_mass_uniform(c1, 4);
    assert(c1.len() == m.len());
    assert(c1[0] is Num);
    if ovf[g] {
        // SUM: the absolute mass is beyond `i128`.
        assert(sum_mass(NumKind::Numeric, c1) == num_mass_at(c1, 4));
        assert(!fits_agg_value(g_aggs()[1], column(group_members(ks, args, d[x]), 1)));
        crate::link::capacity::lemma_group_by_capacity(db, Seq::empty(), g_keys(), g_aggs(), Box::new(q_where(ps)),
            rows, ks, args, x, 1);
    } else {
        // AVG: the division is outside its domain.
        let c2 = column(m, 2);
        lemma_members_cols(c, ents, gr, recs, g);
        assert(num_sum(c2) == (sum[g] as int, 4nat));
        assert(avg_sum(NumKind::Numeric, c2) == (sum[g] as int, 4nat));
        assert(!fits_avg(NumKind::Numeric, c2));
        assert(!fits_agg_value(g_aggs()[2], column(group_members(ks, args, d[x]), 2)));
        crate::link::capacity::lemma_group_by_capacity(db, Seq::empty(), g_keys(), g_aggs(), Box::new(q_where(ps)),
            rows, ks, args, x, 2);
    }
    crate::link::capacity::lemma_first_input(db, Seq::empty(), q_body(ps));
}

} // verus!
