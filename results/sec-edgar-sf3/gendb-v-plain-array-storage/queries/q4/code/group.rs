//! The GroupBy node over the WHERE rows (the joined rows of the contribution records, `decomp`): its prepared
//! keys and arguments are the records' `krow`/`arow` (`lemma_group_inputs`), its groups are the fold's `order`,
//! and each group's aggregate row is `[COUNT(DISTINCT cik), SUM(value), AVG(value)]` from the fold's counters
//! (`lemma_agg_values`) when the group's sum stayed in `i128` and its average is inside the division domain.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::scalar::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::relation::*;
use crate::spec::equality::*;
use crate::spec::aggs::avg::*;
use crate::spec::fns::div::*;
use crate::bridge::collect::lemma_collect_all;
use crate::exec::relational::domain::lemma_collect_pointwise;
use crate::link::query::{avg_of, lemma_avg_ok, lemma_groupby_unfold};
use crate::link::expr::lemma_expr_col;
use crate::agent::common::chains::NONE;
use crate::agent::common::distinct::*;
use crate::agent::cols::*;
use crate::agent::nf::*;
use crate::agent::ents::*;
use crate::agent::groups::*;
use crate::agent::scan::*;
use crate::agent::fold::*;
use crate::agent::sem::*;
use crate::agent::join::*;
use crate::agent::decomp::*;

verus! {

/// The aggregate row of a group with exact sum `sum` over `cnt` rows and `dcnt` distinct ciks.
pub open spec fn gval(sum: int, cnt: nat, dcnt: int) -> Row {
    seq![Val::Int(dcnt), Val::Num { coeff: sum, scale: 4 }, avg_of(sum, 4, cnt)]
}

/// The GroupBy output row of group `g`.
pub open spec fn g_row(c: Ctx, reps: Seq<(usize, usize)>, sum: Seq<i128>, cnt: Seq<usize>, dcnt: Seq<usize>, g: int) -> Row {
    grow_row(c, reps, g) + gval(sum[g] as int, cnt[g] as nat, dcnt[g] as int)
}

// ------------------------------------------------------------------------------------------------ records

/// The records of rows `lo..hi`: num rows of the range, entries, matches, values.
pub proof fn lemma_contrib_mem(c: Ctx, ents: Seq<(usize, usize, usize)>, lo: int, hi: int)
    requires 0 <= lo, hi < usize::MAX, ents.len() < usize::MAX,
    ensures forall|q: int| 0 <= q < contrib(c, ents, lo, hi).len() ==> {
        let r = #[trigger] contrib(c, ents, lo, hi)[q];
        &&& lo <= r.0 < hi && (r.1 as int) < ents.len() && ent_match(c, ents, r.0 as int, r.1 as int)
        &&& r.2 == n_val_s(c)[r.0 as int]
    },
    decreases hi - lo,
{
    if hi > lo {
        lemma_contrib_mem(c, ents, lo, hi - 1);
        lemma_recs_mem(c, ents, hi - 1, ents.len() as int);
        let a = contrib(c, ents, lo, hi - 1);
        let b = row_out(c, ents, hi - 1);
        assert forall|q: int| 0 <= q < contrib(c, ents, lo, hi).len() implies {
            let r = #[trigger] contrib(c, ents, lo, hi)[q];
            &&& lo <= r.0 < hi && (r.1 as int) < ents.len() && ent_match(c, ents, r.0 as int, r.1 as int)
            &&& r.2 == n_val_s(c)[r.0 as int]
        } by {
            if q < a.len() {
                assert(contrib(c, ents, lo, hi)[q] == a[q]);
            } else {
                assert(contrib(c, ents, lo, hi)[q] == b[q - a.len()]);
            }
        }
    }
}

/// The record facts of the whole contribution list.
pub open spec fn recs_facts(c: Ctx, ents: Seq<(usize, usize, usize)>, recs: Seq<Rec>) -> bool {
    forall|q: int| 0 <= q < recs.len() ==> {
        let r = #[trigger] recs[q];
        &&& 0 <= r.0 < c.n && (r.1 as int) < ents.len() && ent_match(c, ents, r.0 as int, r.1 as int)
        &&& r.2 == n_val_s(c)[r.0 as int]
    }
}

/// The GROUP BY keys on a row whose cells 12, 36, 41 are `kv`.
proof fn lemma_keys_env(db: Database, x: Row, kv: Row)
    requires x.len() == 48, kv.len() == 3, x[12] == kv[0], x[36] == kv[1], x[41] == kv[2],
    ensures eval_exprs(db, x, g_keys()) == Ok::<Row, SqlError>(kv),
{
    let ks = g_keys();
    let kr = expr_results(db, x, ks);
    lemma_expr_results_index(db, x, ks);
    lemma_expr_col(db, x, 12);
    lemma_expr_col(db, x, 36);
    lemma_expr_col(db, x, 41);
    assert forall|t: int| 0 <= t < kr.len() implies #[trigger] kr[t] == Ok::<Val, SqlError>(kv[t]) by {
        if t == 0 {} else if t == 1 {} else {}
    }
    lemma_collect_all(kr, kv);
}

/// The aggregate arguments on a row whose cells 10 and 7 are `av[0]` and `av[1] == av[2]`.
proof fn lemma_args_env(db: Database, x: Row, av: Row)
    requires x.len() == 48, av.len() == 3, x[10] == av[0], x[7] == av[1], av[2] == av[1],
    ensures agg_args(db, x, g_aggs()) == Ok::<Row, SqlError>(av),
{
    let ag = g_aggs();
    let ar = agg_arg_results(db, x, ag);
    lemma_agg_arg_results_index(db, x, ag);
    lemma_expr_col(db, x, 10);
    lemma_expr_col(db, x, 7);
    assert forall|t: int| 0 <= t < ar.len() implies #[trigger] ar[t] == Ok::<Val, SqlError>(av[t]) by {
        if t == 0 {
            assert(agg_arg(db, x, ag[0]) == agg_arg(db, x, Agg::Count(Expr::Col(10))));
        } else if t == 1 {} else {}
    }
    lemma_collect_all(ar, av);
}

/// The GroupBy input of one record's joined row: its key row and argument row.
pub proof fn lemma_group_input(db: Database, c: Ctx, ents: Seq<(usize, usize, usize)>, r: Rec)
    requires
        ents_ok(c, ents), 0 <= r.0 < c.n, (r.1 as int) < ents.len(), r.2 == n_val_s(c)[r.0 as int],
    ensures group_input(db, rec_row(c, ents, r), g_keys(), g_aggs()) == Ok::<(Row, Row), SqlError>((krow(c, ents, r), arow(c, ents, r))),
{
    hide(eval_exprs);
    hide(agg_args);
    let e = r.1 as int;
    lemma_ent_rows(c, ents, e);
    let (l, j, k) = ents[e];
    let x = rec_row(c, ents, r);
    lemma_full_cells(c, r.0 as int, j as int, k as int, l as int);
    lemma_keys_env(db, x, krow(c, ents, r));
    lemma_args_env(db, x, arow(c, ents, r));
}

/// The GroupBy node over the joined rows of `recs` is `group_rows` of their key and argument rows.
pub proof fn lemma_group_inputs(db: Database, c: Ctx, ps: Seq<Literal>, ents: Seq<(usize, usize, usize)>, recs: Seq<Rec>)
    requires
        ents_ok(c, ents), recs_facts(c, ents, recs),
        eval_query(db, Seq::empty(), q_where(ps)) == Ok::<Relation, SqlError>(rec_rows(c, ents, recs)),
    ensures
        eval_query(db, Seq::empty(), q_group(ps)) == group_rows(g_aggs(), keys_of(c, ents, recs), args_of(c, ents, recs)),
        forall|q: int| 0 <= q < recs.len() ==> #[trigger] group_input(db, Seq::<Val>::empty() + rec_rows(c, ents, recs)[q], g_keys(), g_aggs())
            == Ok::<(Row, Row), SqlError>((keys_of(c, ents, recs)[q], args_of(c, ents, recs)[q])),
{
    let kept = rec_rows(c, ents, recs);
    let e = Seq::<Val>::empty();
    let prep = Seq::new(recs.len(), |q: int| (krow(c, ents, recs[q]), arow(c, ents, recs[q])));
    let pre = Seq::new(kept.len(), |i: int|
        match eval_exprs(db, e + kept[i], g_keys()) {
            Err(err) => Err(err),
            Ok(k) => match agg_args(db, e + kept[i], g_aggs()) {
                Err(err) => Err(err),
                Ok(a) => Ok((k, a)),
            },
        });
    assert forall|q: int| 0 <= q < pre.len() implies #[trigger] pre[q] == Ok::<(Row, Row), SqlError>(prep[q]) by {
        assert(e + kept[q] =~= kept[q]);
        lemma_group_input(db, c, ents, recs[q]);
    }
    lemma_collect_all(pre, prep);
    lemma_groupby_unfold(db, q_where(ps), g_keys(), g_aggs(), kept, prep);
    assert(prep.map_values(|p: (Row, Row)| p.0) =~= keys_of(c, ents, recs));
    assert(prep.map_values(|p: (Row, Row)| p.1) =~= args_of(c, ents, recs));
    assert forall|q: int| 0 <= q < recs.len() implies #[trigger] group_input(db, e + kept[q], g_keys(), g_aggs())
        == Ok::<(Row, Row), SqlError>((keys_of(c, ents, recs)[q], args_of(c, ents, recs)[q])) by {
        assert(e + kept[q] =~= kept[q]);
        lemma_group_input(db, c, ents, recs[q]);
    }
}

// ------------------------------------------------------------------------------------------------ aggregate values

/// The AVG column of a group's members is its SUM column.
pub proof fn lemma_members_cols(c: Ctx, ents: Seq<(usize, usize, usize)>, gr: &Groups, p: Seq<Rec>, g: int)
    requires groups_ok(c, ents, gr), recs_ok(ents, p), 0 <= g < gr.reps@.len(),
    ensures column(members(c, ents, gr.reps@, p, g), 2) == column(members(c, ents, gr.reps@, p, g), 1),
    decreases p.len(),
{
    if p.len() > 0 {
        let pi = p.drop_last();
        assert(pi.push(p.last()) =~= p);
        assert(p[p.len() - 1] == p.last());
        assert forall|q: int| 0 <= q < pi.len() implies ((#[trigger] pi[q]).1 as int) < ents.len() by {
            assert(pi[q] == p[q]);
        }
        lemma_members_cols(c, ents, gr, pi, g);
        lemma_members_push(c, ents, gr, pi, p.last(), g);
        let m = members(c, ents, gr.reps@, pi, g);
        let a = arow(c, ents, p.last());
        lemma_column_push(m, a, 1);
        lemma_column_push(m, a, 2);
    } else {
        assert(keys_of(c, ents, p) =~= Seq::<Row>::empty());
        assert(column(members(c, ents, gr.reps@, p, g), 2) =~= column(members(c, ents, gr.reps@, p, g), 1));
    }
}

/// Numerics of scale 4 are of the numeric family; non-NULL values count as their number.
pub proof fn lemma_num_kind(vs: Seq<Val>)
    requires all_num(vs, 4),
    ensures all_of_kind(NumKind::Numeric, vs), count_non_null(vs) == vs.len(),
    decreases vs.len(),
{
    if vs.len() > 0 {
        let d = vs.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies (#[trigger] d[i] is Num) && d[i]->Num_scale == 4 by {
            assert(d[i] == vs[i]);
        }
        lemma_num_kind(d);
        assert(vs[vs.len() - 1] == vs.last());
    }
}

pub proof fn lemma_int_count(vs: Seq<Val>)
    requires all_int(vs),
    ensures count_non_null(vs) == vs.len(),
    decreases vs.len(),
{
    if vs.len() > 0 {
        let d = vs.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies #[trigger] d[i] is Int by {
            assert(d[i] == vs[i]);
        }
        lemma_int_count(d);
        assert(vs[vs.len() - 1] == vs.last());
    }
}

/// The distinct ciks of a group are 32-bit integers: at most `2^32` of them.
pub proof fn lemma_dcnt_bound(c: Ctx, ents: Seq<(usize, usize, usize)>, gr: &Groups, p: Seq<Rec>, cnt: Seq<usize>,
    sum: Seq<i128>, ovf: Seq<bool>, g: int)
    requires groups_ok(c, ents, gr), recs_ok(ents, p), acc_inv(c, ents, gr, p, cnt, sum, ovf), 0 <= g < gr.reps@.len(),
    ensures
        distinct_vals(column(members(c, ents, gr.reps@, p, g), 0)).len() <= 0x1_0000_0000,
        all_int(distinct_vals(column(members(c, ents, gr.reps@, p, g), 0))),
        count_non_null(distinct_vals(column(members(c, ents, gr.reps@, p, g), 0)))
            == distinct_vals(column(members(c, ents, gr.reps@, p, g), 0)).len(),
{
    let vs = column(members(c, ents, gr.reps@, p, g), 0);
    assert(all_int(vs));
    assert forall|i: int| 0 <= i < vs.len() implies -0x8000_0000 <= (#[trigger] vs[i])->Int_0 < 0x8000_0000 by {
        let x = vs[i]->Int_0;
        assert(vs[i] == Val::Int(x));
        assert(vs.contains(Val::Int(x)));
        let q = choose|q: int| 0 <= q < p.len() && gr.gid@[p[q].1 as int] == g && s_cik(c, ents[p[q].1 as int].1 as int) == x;
    }
    lemma_distinct_bound(vs);
    lemma_distinct_ints(vs);
    lemma_int_count(distinct_vals(vs));
}

/// The aggregate row of a group whose sum stayed in `i128` and whose average is inside the division domain.
pub proof fn lemma_agg_values(c: Ctx, ents: Seq<(usize, usize, usize)>, gr: &Groups, p: Seq<Rec>, cnt: Seq<usize>,
    sum: Seq<i128>, ovf: Seq<bool>, dcnt: Seq<usize>, pseen: Seq<bool>, g: int)
    requires
        groups_ok(c, ents, gr), recs_ok(ents, p), acc_inv(c, ents, gr, p, cnt, sum, ovf), dist_inv(c, ents, gr, p, dcnt, pseen),
        0 <= g < gr.reps@.len(), !ovf[g], cnt[g] > 0, num_div_fits(sum[g] as int, 4, cnt[g] as int, 0),
    ensures
        agg_row(g_aggs(), members(c, ents, gr.reps@, p, g)) == Ok::<Row, SqlError>(gval(sum[g] as int, cnt[g] as nat, dcnt[g] as int)),
{
    let m = members(c, ents, gr.reps@, p, g);
    let aggs = g_aggs();
    let (c0, c1, c2) = (column(m, 0), column(m, 1), column(m, 2));
    let gv = gval(sum[g] as int, cnt[g] as nat, dcnt[g] as int);
    lemma_dcnt_bound(c, ents, gr, p, cnt, sum, ovf, g);
    lemma_members_cols(c, ents, gr, p, g);
    assert(all_num(c1, 4));
    lemma_num_kind(c1);
    let s = sum[g] as int;
    let n = cnt[g] as int;
    assert(num_sum(c1) == (s, 4nat));
    lemma_num_in_range_small(s, 4);
    lemma_avg_ok(s, 4, n);
    let rs = Seq::new(aggs.len(), |j: int| agg_value(aggs[j], column(m, j)));
    assert forall|j: int| 0 <= j < rs.len() implies #[trigger] rs[j] == Ok::<Val, SqlError>(gv[j]) by {
        if j == 0 {
            assert(agg_value(aggs[0], c0) == agg_value(Agg::Count(Expr::Col(10)), distinct_vals(c0)));
            assert(int_in_range(IntKind::Int8, dcnt[g] as int));
        } else if j == 1 {
        } else {
            assert(avg_sum(NumKind::Numeric, c2) == (s, 4nat));
        }
    }
    lemma_collect_all(rs, gv);
}

/// The GroupBy node: one row per group of `order`, `key ++ aggregates`.
pub proof fn lemma_group_node(db: Database, c: Ctx, ps: Seq<Literal>, ents: Seq<(usize, usize, usize)>, recs: Seq<Rec>, gr: &Groups,
    order: Seq<usize>, seen: Seq<bool>, cnt: Seq<usize>, sum: Seq<i128>, ovf: Seq<bool>, dcnt: Seq<usize>, pseen: Seq<bool>)
    requires
        ents_ok(c, ents), recs_facts(c, ents, recs), groups_ok(c, ents, gr),
        eval_query(db, Seq::empty(), q_where(ps)) == Ok::<Relation, SqlError>(rec_rows(c, ents, recs)),
        fold_inv(c, ents, gr, recs, order, seen, cnt, sum, ovf, dcnt, pseen),
        forall|g: int| 0 <= g < seen.len() && #[trigger] seen[g] ==> cnt[g] > 0,
        forall|x: int| 0 <= x < order.len() ==> !ovf[#[trigger] order[x] as int]
            && num_div_fits(sum[order[x] as int] as int, 4, cnt[order[x] as int] as int, 0),
    ensures
        eval_query(db, Seq::empty(), q_group(ps))
            == Ok::<Relation, SqlError>(order.map_values(|g: usize| g_row(c, gr.reps@, sum, cnt, dcnt, g as int))),
{
    assert(recs_ok(ents, recs)) by {
        assert forall|q: int| 0 <= q < recs.len() implies ((#[trigger] recs[q]).1 as int) < ents.len() by {}
    }
    lemma_group_inputs(db, c, ps, ents, recs);
    let ks = keys_of(c, ents, recs);
    let args = args_of(c, ents, recs);
    let d = distinct_rows(ks);
    assert(d == order.map_values(|g: usize| grow_row(c, gr.reps@, g as int)));
    let out = order.map_values(|g: usize| g_row(c, gr.reps@, sum, cnt, dcnt, g as int));
    let rs = Seq::new(d.len(), |x: int|
        match agg_row(g_aggs(), group_members(ks, args, d[x])) {
            Ok(a) => Ok(d[x] + a),
            Err(e) => Err(e),
        });
    assert forall|x: int| 0 <= x < rs.len() implies #[trigger] rs[x] == Ok::<Row, SqlError>(out[x]) by {
        let g = order[x] as int;
        assert(order.contains(order[x]));
        assert(seen[g]);
        assert(d[x] == grow_row(c, gr.reps@, g));
        lemma_agg_values(c, ents, gr, recs, cnt, sum, ovf, dcnt, pseen, g);
    }
    lemma_collect_all(rs, out);
}

} // verus!
