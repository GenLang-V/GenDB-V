//! Aggregation queries over evaluated input rows: `Aggregate` (no GROUP BY: exactly one row over all input rows)
//! and `GroupBy`. Both first evaluate, per input row in order, the aggregate arguments (`exec_agg_args`; GROUP BY
//! also the key tuple), then compute the aggregate values of each group with `exec::relational::aggregate`.
//!
//! GROUP BY forms one group per class of not-distinct keys (`spec::equality`: NULL groups with NULL, numerics by
//! value), in first-occurrence order, represented by its first key; per group, the aggregates run over its members
//! in input order. Materialized and quadratic in the number of groups — a reference evaluator, not an optimized one.
//!
//! The argument and key evaluation is part of the `exec_expr`/`exec_query` recursion (measures in
//! `exec::relational::eval`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::equality::*;
use crate::exec::value::*;
use crate::exec::ast::*;
use crate::exec::domain::*;
use crate::exec::expr::*;
use crate::exec::equality::*;
use crate::exec::relational::schema::*;
use crate::exec::relational::rows::*;
use crate::exec::relational::domain::*;
use crate::exec::relational::aggregate::*;
use crate::exec::relational::ops::*;
use crate::bridge::relation::*;

verus! {

// ------------------------------------------------------------------ aggregate arguments of one input row

/// Argument value of one aggregate in one input row.
pub fn exec_agg_arg(db: &EDatabase, env: &ERow, a: &EAgg) -> (r: Outcome<EVal>)
    requires db_ts_ok(db@), row_ts_ok(view_row(env@)),
    ensures
        match r {
            Ok(res) => fits_agg_arg(db@, view_row(env@), view_agg(*a))
                && view_result(res) == agg_arg(db@, view_row(env@), view_agg(*a))
                && (res matches Ok(v) ==> val_ts_ok(v@)),
            Err(_) => !fits_agg_arg(db@, view_row(env@), view_agg(*a)),
        },
    decreases a,
{
    match a {
        EAgg::CountStar => Ok(Ok(EVal::Null)),
        EAgg::Count(e) | EAgg::Min(e) | EAgg::Max(e) => exec_expr(db, env, e),
        EAgg::Sum { arg, .. } | EAgg::Avg { arg, .. } => exec_expr(db, env, arg),
        EAgg::DistinctAgg(inner) => exec_agg_arg(db, env, inner),
    }
}

/// Argument values of the aggregates in one input row (`CountStar` has none: NULL stands in).
pub fn exec_agg_args(db: &EDatabase, env: &ERow, aggs: &Vec<EAgg>) -> (r: Outcome<ERow>)
    requires db_ts_ok(db@), row_ts_ok(view_row(env@)),
    ensures
        match r {
            Ok(res) => fits_agg_args(db@, view_row(env@), view_aggs(aggs@))
                && match res {
                    Ok(vs) => agg_args(db@, view_row(env@), view_aggs(aggs@)) == Ok::<Row, SqlError>(view_row(vs@))
                        && vs.len() == aggs.len() && row_ts_ok(view_row(vs@)),
                    Err(e) => agg_args(db@, view_row(env@), view_aggs(aggs@)) == Err::<Row, SqlError>(e),
                },
            Err(_) => !fits_agg_args(db@, view_row(env@), view_aggs(aggs@)),
        },
    decreases aggs, 1nat,
{
    hide(view_agg);
    hide(view_aggs);
    hide(view_expr);
    hide(agg_arg);
    hide(fits_agg_arg);
    hide(agg_args);
    hide(fits_agg_args);
    hide(agg_arg_results);
    hide(agg_arg_fs);
    let ghost genv = view_row(env@);
    let ghost ga = view_aggs(aggs@);
    let ghost rs = agg_arg_results(db@, genv, ga);
    let ghost fs = agg_arg_fs(db@, genv, ga);
    proof {
        lemma_agg_args(db@, genv, ga);
        lemma_view_aggs_index(aggs@);
        lemma_agg_arg_results_index(db@, genv, ga);
        lemma_agg_arg_fs_index(db@, genv, ga);
    }
    let mut out: ERow = Vec::new();
    let mut j: usize = 0;
    while j < aggs.len()
        invariant
            j <= aggs.len(), genv == view_row(env@), ga == view_aggs(aggs@), ga.len() == aggs.len(),
            rs == agg_arg_results(db@, genv, ga), fs == agg_arg_fs(db@, genv, ga),
            agg_args(db@, genv, ga) == collect(rs), fits_agg_args(db@, genv, ga) == fits_each(rs, fs),
            row_ts_ok(genv), db_ts_ok(db@),
            out.len() == j,
            forall|k: int| 0 <= k < j ==> #[trigger] rs[k] == Ok::<Val, SqlError>(view_row(out@)[k]),
            rs.len() == aggs.len(), fs.len() == aggs.len(),
            ok_before(rs, j as int), fits_before(fs, j as int),
            row_ts_ok(view_row(out@)),
        decreases aggs.len() - j,
    {
        proof {
            lemma_view_aggs_index(aggs@);
            lemma_agg_arg_results_index(db@, genv, ga);
            lemma_agg_arg_fs_index(db@, genv, ga);
            assert(ga[j as int] == view_agg(aggs@[j as int]));
        }
        match exec_agg_arg(db, env, &aggs[j]) {
            Err(cap) => {
                proof { lemma_each_capacity(rs, fs, j as int); }
                return Err(cap);
            },
            Ok(Err(e)) => {
                proof { lemma_each_err(rs, fs, j as int); }
                return Ok(Err(e));
            },
            Ok(Ok(v)) => {
                let ghost prev = view_row(out@);
                out.push(v);
                proof { assert(view_row(out@) =~= prev.push(v@)); }
            },
        }
        j = j + 1;
    }
    proof { lemma_each_done(rs, fs, view_row(out@)); }
    Ok(Ok(out))
}

// ------------------------------------------------------------------ Aggregate (no GROUP BY)

/// Aggregation without GROUP BY over evaluated input rows: exactly one row.
pub fn exec_aggregate(db: &EDatabase, ctx: &ERow, aggs: &Vec<EAgg>, rows: &Vec<ERow>) -> (r: Outcome<Vec<ERow>>)
    requires
        db_ts_ok(db@),
        row_ts_ok(view_row(ctx@)),
        rows_ts_ok(view_rows(rows@)),
    ensures
        ({
            let gc = view_row(ctx@);
            let g = view_rows(rows@);
            let ga = view_aggs(aggs@);
            let fits = fits_each(agg_args_results(db@, gc, g, ga), agg_args_fs(db@, gc, g, ga))
                && match collect(agg_args_results(db@, gc, g, ga)) {
                    Err(_) => true,
                    Ok(args) => fits_agg_row(ga, args),
                };
            let spec = match collect(agg_args_results(db@, gc, g, ga)) {
                Err(e) => Err(e),
                Ok(args) => match agg_row(ga, args) {
                    Err(e) => Err(e),
                    Ok(row) => Ok(seq![row]),
                },
            };
            match r {
                Ok(res) => fits && rel_outcome_ok(res, spec),
                Err(_) => !fits,
            }
        }),
    decreases aggs, 2nat,
{
    hide(view_agg);
    hide(view_expr);
    hide(agg_args);
    hide(fits_agg_args);
    hide(agg_args_fs);
    hide(agg_row);
    hide(fits_agg_row);
    let ghost gc = view_row(ctx@);
    let ghost g = view_rows(rows@);
    let ghost ga = view_aggs(aggs@);
    let ghost rs = agg_args_results(db@, gc, g, ga);
    let ghost fs = agg_args_fs(db@, gc, g, ga);
    proof { lemma_agg_args_fs_index(db@, gc, g, ga); }
    let mut args: Vec<ERow> = Vec::new();
    let mut i: usize = 0;
    while i < rows.len()
        invariant
            i <= rows.len(), g.len() == rows.len(),
            gc == view_row(ctx@), g == view_rows(rows@), ga == view_aggs(aggs@),
            rs == agg_args_results(db@, gc, g, ga), fs == agg_args_fs(db@, gc, g, ga),
            row_ts_ok(gc), rows_ts_ok(g), db_ts_ok(db@),
            args.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] rs[k] == Ok::<Row, SqlError>(view_rows(args@)[k]),
            forall|k: int| 0 <= k < i ==> (#[trigger] args@[k]).len() == aggs.len(),
            rows_ts_ok(view_rows(args@)),
            fs.len() == rows.len(),
            ok_before(rs, i as int), fits_before(fs, i as int),
        decreases rows.len() - i,
    {
        let env = concat_rows(ctx, &rows[i]);
        proof {
            lemma_agg_args_fs_index(db@, gc, g, ga);
            assert(g[i as int] == view_row(rows@[i as int]@));
            lemma_row_ts_ok_concat(gc, g[i as int]);
        }
        match exec_agg_args(db, &env, aggs) {
            Err(cap) => {
                proof { lemma_each_capacity(rs, fs, i as int); }
                return Err(cap);
            },
            Ok(Err(e)) => {
                proof { lemma_each_err(rs, fs, i as int); }
                return Ok(Err(e));
            },
            Ok(Ok(vs)) => {
                let ghost prev = view_rows(args@);
                args.push(vs);
                proof {
                    assert(view_rows(args@) =~= prev.push(view_row(vs@)));
                    assert forall|k: int| 0 <= k < view_rows(args@).len() implies row_ts_ok(#[trigger] view_rows(args@)[k]) by {
                        if k < prev.len() { assert(view_rows(args@)[k] == prev[k]); }
                    }
                }
            },
        }
        i = i + 1;
    }
    proof { lemma_each_done(rs, fs, view_rows(args@)); }
    match exec_agg_row(aggs, &args) {
        Err(cap) => Err(cap),
        Ok(Err(e)) => Ok(Err(e)),
        Ok(Ok(row)) => {
            let ghost grow = view_row(row@);
            let out = vec![row];
            proof {
                assert(view_rows(out@) =~= seq![grow]);
            }
            Ok(Ok(out))
        },
    }
}

// ------------------------------------------------------------------ GroupBy

/// Keys and aggregates of a `GroupBy` node (spec view).
pub open spec fn group_by_parts(q: EQuery) -> (Seq<Expr>, Seq<Agg>) {
    match q {
        EQuery::GroupBy { keys, aggs, .. } => (view_exprs(keys@), view_aggs(aggs@)),
        _ => (Seq::empty(), Seq::empty()),
    }
}

/// `GROUP BY keys` with `aggs` (of the `GroupBy` node `q`) over evaluated input rows: evaluates each input row's
/// key tuple and aggregate arguments, then forms the groups (`group_rows_exec`). Takes the node so that its
/// termination measure covers both the keys and the aggregates.
pub fn exec_group_by(db: &EDatabase, ctx: &ERow, q: &EQuery, rows: &Vec<ERow>) -> (r: Outcome<Vec<ERow>>)
    requires
        q is GroupBy,
        db_ts_ok(db@),
        row_ts_ok(view_row(ctx@)),
        rows_ts_ok(view_rows(rows@)),
    ensures
        ({
            let gc = view_row(ctx@);
            let g = view_rows(rows@);
            let gks = group_by_parts(*q).0;
            let ga = group_by_parts(*q).1;
            let fits = fits_each(group_input_results(db@, gc, g, gks, ga), group_input_fs(db@, gc, g, gks, ga))
                && match collect(group_input_results(db@, gc, g, gks, ga)) {
                    Err(_) => true,
                    Ok(prepared) => fits_groups(ga, prepared.map_values(|p: (Row, Row)| p.0),
                        prepared.map_values(|p: (Row, Row)| p.1)),
                };
            let spec = match collect(group_input_results(db@, gc, g, gks, ga)) {
                Err(e) => Err(e),
                Ok(prepared) => collect(group_results(ga, prepared.map_values(|p: (Row, Row)| p.0),
                    prepared.map_values(|p: (Row, Row)| p.1))),
            };
            match r {
                Ok(res) => fits && rel_outcome_ok(res, spec),
                Err(_) => !fits,
            }
        }),
    decreases q, 1nat,
{
    hide(view_agg);
    hide(view_expr);
    hide(view_aggs);
    hide(view_exprs);
    hide(eval_exprs);
    hide(fits_exprs);
    hide(agg_args);
    hide(fits_agg_args);
    hide(group_input);
    hide(fits_group_input);
    match q {
        EQuery::GroupBy { keys, aggs, .. } => {
            let ghost gc = view_row(ctx@);
            let ghost g = view_rows(rows@);
            let ghost gks = view_exprs(keys@);
            let ghost ga = view_aggs(aggs@);
            let ghost rs = group_input_results(db@, gc, g, gks, ga);
            let ghost fs = group_input_fs(db@, gc, g, gks, ga);
            let ghost mut prep: Seq<(Row, Row)> = Seq::empty();
            // Per input row i: its key tuple `key_rows[i]` and its aggregate arguments `arg_rows[i]`.
            let mut key_rows: Vec<ERow> = Vec::new();
            let mut arg_rows: Vec<ERow> = Vec::new();
            let mut i: usize = 0;
            #[verifier::loop_isolation(false)]
            while i < rows.len()
                invariant
                    i <= rows.len(), g.len() == rows.len(),
                    gc == view_row(ctx@), g == view_rows(rows@), gks == view_exprs(keys@), ga == view_aggs(aggs@),
                    rs == group_input_results(db@, gc, g, gks, ga), fs == group_input_fs(db@, gc, g, gks, ga),
                    row_ts_ok(gc), rows_ts_ok(g), db_ts_ok(db@),
                    key_rows.len() == i, arg_rows.len() == i, prep.len() == i,
                    forall|k: int| 0 <= k < i ==> #[trigger] rs[k] == Ok::<(Row, Row), SqlError>(prep[k]),
                    forall|k: int| 0 <= k < i ==> #[trigger] prep[k] == (view_rows(key_rows@)[k], view_rows(arg_rows@)[k]),
                    forall|k: int| 0 <= k < i ==> (#[trigger] arg_rows@[k]).len() == aggs.len(),
                    ok_before(rs, i as int), fits_before(fs, i as int),
                    rows_ts_ok(view_rows(key_rows@)),
                    rows_ts_ok(view_rows(arg_rows@)),
                decreases rows.len() - i,
            {
                let env = concat_rows(ctx, &rows[i]);
                let ghost genv = gc + g[i as int];
                proof {
                    assert(g[i as int] == view_row(rows@[i as int]@));
                    lemma_row_ts_ok_concat(gc, g[i as int]);
                    lemma_group_input_results(db@, gc, g, gks, ga, i as int);
                    lemma_group_input_unfold(db@, genv, gks, ga);
                    assert(fs[i as int] == fits_group_input(db@, genv, gks, ga));
                }
                let k = match exec_exprs(db, &env, keys) {
                    Err(cap) => {
                        proof { lemma_each_capacity(rs, fs, i as int); }
                        return Err(cap);
                    },
                    Ok(Err(e)) => {
                        proof { lemma_each_err(rs, fs, i as int); }
                        return Ok(Err(e));
                    },
                    Ok(Ok(k)) => k,
                };
                let a = match exec_agg_args(db, &env, aggs) {
                    Err(cap) => {
                        proof { lemma_each_capacity(rs, fs, i as int); }
                        return Err(cap);
                    },
                    Ok(Err(e)) => {
                        proof { lemma_each_err(rs, fs, i as int); }
                        return Ok(Err(e));
                    },
                    Ok(Ok(a)) => a,
                };
                let ghost pk = view_rows(key_rows@);
                let ghost pa = view_rows(arg_rows@);
                proof { prep = prep.push((view_row(k@), view_row(a@))); }
                key_rows.push(k);
                arg_rows.push(a);
                proof {
                    assert(view_rows(key_rows@) =~= pk.push(prep[i as int].0));
                    assert(view_rows(arg_rows@) =~= pa.push(prep[i as int].1));
                    assert forall|j: int| 0 <= j < view_rows(arg_rows@).len() implies row_ts_ok(#[trigger] view_rows(arg_rows@)[j]) by {
                        if j < pa.len() { assert(view_rows(arg_rows@)[j] == pa[j]); }
                    }
                }
                i = i + 1;
            }
            proof {
                lemma_each_done(rs, fs, prep);
                assert(prep.map_values(|p: (Row, Row)| p.0) =~= view_rows(key_rows@));
                assert(prep.map_values(|p: (Row, Row)| p.1) =~= view_rows(arg_rows@));
            }
            group_rows_exec(aggs, &key_rows, &arg_rows)
        },
        _ => unreached(),
    }
}

/// `spec::relation::group_rows` over the prepared input rows: per distinct key `d[g]` (first-occurrence order),
/// the row `d[g] ++ aggregates(members)`.
fn group_rows_exec(aggs: &Vec<EAgg>, key_rows: &Vec<ERow>, arg_rows: &Vec<ERow>) -> (r: Outcome<Vec<ERow>>)
    requires
        key_rows.len() == arg_rows.len(),
        forall|i: int| 0 <= i < arg_rows.len() ==> (#[trigger] arg_rows@[i]).len() == aggs.len(),
        rows_ts_ok(view_rows(key_rows@)),
        rows_ts_ok(view_rows(arg_rows@)),
    ensures
        ({
            let ga = view_aggs(aggs@);
            let gk = view_rows(key_rows@);
            let gv = view_rows(arg_rows@);
            match r {
                Ok(res) => fits_groups(ga, gk, gv) && rel_outcome_ok(res, collect(group_results(ga, gk, gv))),
                Err(_) => !fits_groups(ga, gk, gv),
            }
        }),
{
    hide(agg_row);
    hide(fits_agg_row);
    let ghost ga = view_aggs(aggs@);
    let ghost gk = view_rows(key_rows@);
    let ghost gv = view_rows(arg_rows@);
    let ghost rs = group_results(ga, gk, gv);
    let ghost fs = groups_fs(ga, gk, gv);
    let d = distinct_rows_exec(key_rows);
    let ghost gd = view_rows(d@);
    let mut out: Vec<ERow> = Vec::new();
    let mut g: usize = 0;
    while g < d.len()
        invariant
            g <= d.len(), key_rows.len() == arg_rows.len(),
            ga == view_aggs(aggs@), gk == view_rows(key_rows@), gv == view_rows(arg_rows@), gd == view_rows(d@),
            gd == distinct_rows(gk), rows_ts_ok(gd), rows_ts_ok(gv),
            forall|i: int| 0 <= i < arg_rows.len() ==> (#[trigger] arg_rows@[i]).len() == aggs.len(),
            rs == group_results(ga, gk, gv), fs == groups_fs(ga, gk, gv),
            rs.len() == d.len(), fs.len() == d.len(),
            out.len() == g,
            forall|k: int| 0 <= k < g ==> #[trigger] rs[k] == Ok::<Row, SqlError>(view_rows(out@)[k]),
            ok_before(rs, g as int), fits_before(fs, g as int),
            rows_ts_ok(view_rows(out@)),
        decreases d.len() - g,
    {
        let members = group_members_exec(key_rows, arg_rows, &d[g], aggs.len());
        proof {
            assert(gd[g as int] == view_row(d@[g as int]@));
            assert(fs[g as int] == fits_agg_row(ga, group_members(gk, gv, gd[g as int])));
            // Members are argument rows, so they keep the timestamp invariant.
            let gm = view_rows(members@);
            lemma_group_members_sub(gk, gv, gd[g as int]);
            assert forall|m: int| 0 <= m < gm.len() implies row_ts_ok(#[trigger] gm[m]) by {
                let i = choose|i: int| 0 <= i < gv.len() && gv[i] == gm[m];
            }
        }
        match exec_agg_row(aggs, &members) {
            Err(cap) => {
                proof { lemma_each_capacity(rs, fs, g as int); }
                return Err(cap);
            },
            Ok(Err(e)) => {
                proof { lemma_each_err(rs, fs, g as int); }
                return Ok(Err(e));
            },
            Ok(Ok(a)) => {
                let ghost prev = view_rows(out@);
                let row = concat_rows(&d[g], &a);
                proof { lemma_row_ts_ok_concat(gd[g as int], view_row(a@)); }
                out.push(row);
                proof { assert(view_rows(out@) =~= prev.push(gd[g as int] + view_row(a@))); }
            },
        }
        g = g + 1;
    }
    proof { lemma_each_done(rs, fs, view_rows(out@)); }
    Ok(Ok(out))
}

/// `spec::relation::group_members`: the argument rows of the input rows whose key tuple is not distinct from
/// `key`, in input order (`n`: the number of aggregates, the width of every argument row).
fn group_members_exec(key_rows: &Vec<ERow>, arg_rows: &Vec<ERow>, key: &ERow, n: usize) -> (out: Vec<ERow>)
    requires
        key_rows.len() == arg_rows.len(),
        forall|i: int| 0 <= i < arg_rows.len() ==> (#[trigger] arg_rows@[i]).len() == n,
    ensures
        view_rows(out@) == group_members(view_rows(key_rows@), view_rows(arg_rows@), view_row(key@)),
        forall|i: int| 0 <= i < out.len() ==> (#[trigger] out@[i]).len() == n,
{
    let ghost gk = view_rows(key_rows@);
    let ghost ga = view_rows(arg_rows@);
    let ghost k = view_row(key@);
    let mut out: Vec<ERow> = Vec::new();
    let mut i: usize = 0;
    while i < key_rows.len()
        invariant
            i <= key_rows.len(), key_rows.len() == arg_rows.len(),
            gk == view_rows(key_rows@), ga == view_rows(arg_rows@), k == view_row(key@),
            forall|j: int| 0 <= j < arg_rows.len() ==> (#[trigger] arg_rows@[j]).len() == n,
            view_rows(out@) == group_members(gk.take(i as int), ga.take(i as int), k),
            forall|j: int| 0 <= j < out.len() ==> (#[trigger] out@[j]).len() == n,
        decreases key_rows.len() - i,
    {
        proof {
            let tk = gk.take(i as int + 1);
            let ta = ga.take(i as int + 1);
            assert(tk.drop_last() =~= gk.take(i as int));
            assert(ta.drop_last() =~= ga.take(i as int));
            assert(tk.last() == view_row(key_rows@[i as int]@));
            assert(ta.last() == view_row(arg_rows@[i as int]@));
        }
        if row_not_distinct_exec(&key_rows[i], key) {
            let ghost prev = view_rows(out@);
            let r = clone_row(&arg_rows[i]);
            out.push(r);
            proof { assert(view_rows(out@) =~= prev.push(ga[i as int])); }
        }
        i = i + 1;
    }
    proof {
        assert(gk.take(key_rows.len() as int) =~= gk);
        assert(ga.take(key_rows.len() as int) =~= ga);
    }
    out
}

} // verus!
