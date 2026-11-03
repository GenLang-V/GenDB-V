//! Row operators of the query constructors `Table`, `Filter`, `Project`, `Product` and `LeftJoin`, each over its
//! already evaluated input rows, plus the outcome contract every row-producing operator shares (`rel_outcome_ok`)
//! and the static arity that sizes LEFT JOIN padding. The aggregating constructors are in
//! `exec::relational::group`; the dispatch over constructors is `exec::relational::eval::exec_query`.
//!
//! `exec_filter`, `exec_project`, `exec_left_join_row` and `exec_left_join` evaluate expressions or conditions per
//! row, so they are part of the `exec_expr`/`exec_query` recursion (measures in `exec::relational::eval`).
//! Every per-row loop evaluates left to right and stops at the first SQL error or `Capacity`, so it proves its
//! result against the named per-row outcome and domain sequences of `exec::relational::domain` (`fits_each`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::exec::value::*;
use crate::exec::ast::*;
use crate::exec::domain::*;
use crate::exec::expr::*;
use crate::exec::relational::schema::*;
use crate::exec::relational::rows::*;
use crate::exec::relational::domain::*;
use crate::exec::relational::eval::*;

verus! {

pub open spec fn view_rel(r: Result<Vec<ERow>, SqlError>) -> Result<Relation, SqlError> {
    match r {
        Ok(rows) => Ok(view_rows(rows@)),
        Err(e) => Err(e),
    }
}

/// Outcome postcondition shared by the row-producing operators: the result is `spec` and, when it is a
/// relation, its rows satisfy the timestamp representation invariant.
pub open spec fn rel_outcome_ok(res: Result<Vec<ERow>, SqlError>, spec: Result<Relation, SqlError>) -> bool {
    view_rel(res) == spec && (res matches Ok(rows) ==> rows_ts_ok(view_rows(rows@)))
}

/// `Query::Table(t)`: a copy of the stored rows (`TypeError` for an unknown table, which typing excludes).
pub fn exec_table(db: &EDatabase, t: usize) -> (r: Result<Vec<ERow>, SqlError>)
    requires db_ts_ok(db@),
    ensures rel_outcome_ok(r, eval_query(db@, seq![], Query::Table(t as nat))),
{
    if t < db.tables.len() {
        let rows = clone_rows(&db.tables[t]);
        proof {
            assert(db@.tables[t as int] == view_rows(db.tables@[t as int]@));
            assert(rows_ts_ok(db@.tables[t as int]));
        }
        Ok(rows)
    } else {
        Err(SqlError::TypeError)
    }
}

/// `WHERE pred` over evaluated input rows (keep the rows whose condition is `True`).
pub fn exec_filter(db: &EDatabase, ctx: &ERow, pred: &EPred, rows: &Vec<ERow>) -> (r: Outcome<Vec<ERow>>)
    requires
        db_ts_ok(db@),
        row_ts_ok(view_row(ctx@)),
        rows_ts_ok(view_rows(rows@)),
    ensures
        ({
            let rs = filter_results(db@, view_row(ctx@), view_rows(rows@), view_pred(*pred));
            match r {
                Ok(res) => filter_fits(db@, view_row(ctx@), view_rows(rows@), view_pred(*pred))
                    && rel_outcome_ok(res, match collect(rs) {
                        Err(e) => Err(e),
                        Ok(truths) => Ok(keep_true(view_rows(rows@), truths)),
                    }),
                Err(_) => !filter_fits(db@, view_row(ctx@), view_rows(rows@), view_pred(*pred)),
            }
        }),
    decreases pred, 2nat,
{
    hide(eval_pred);
    hide(fits_pred);
    let ghost gc = view_row(ctx@);
    let ghost g = view_rows(rows@);
    let ghost gp = view_pred(*pred);
    let ghost rs = filter_results(db@, gc, g, gp);
    let ghost fs = filter_fs(db@, gc, g, gp);
    let ghost mut ts: Seq<Truth> = Seq::empty();
    proof { lemma_filter_fits_each(db@, gc, g, gp); }
    let mut out: Vec<ERow> = Vec::new();
    let mut i: usize = 0;
    while i < rows.len()
        invariant
            i <= rows.len(), g.len() == rows.len(),
            db_ts_ok(db@),
            gc == view_row(ctx@), g == view_rows(rows@), gp == view_pred(*pred),
            rs == filter_results(db@, gc, g, gp), fs == filter_fs(db@, gc, g, gp),
            fits_each(rs, fs) == filter_fits(db@, gc, g, gp),
            row_ts_ok(gc), rows_ts_ok(g),
            ts.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] rs[k] == Ok::<Truth, SqlError>(ts[k]),
            ok_before(rs, i as int), fits_before(fs, i as int),
            view_rows(out@) == keep_true(g.take(i as int), ts),
            rows_ts_ok(view_rows(out@)),
        decreases rows.len() - i,
    {
        let env = concat_rows(ctx, &rows[i]);
        proof {
            assert(g[i as int] == view_row(rows@[i as int]@));
            lemma_row_ts_ok_concat(gc, g[i as int]);
        }
        match exec_pred(db, &env, pred) {
            Err(cap) => {
                proof { lemma_each_capacity(rs, fs, i as int); }
                return Err(cap);
            },
            Ok(Err(e)) => {
                proof { lemma_each_err(rs, fs, i as int); }
                return Ok(Err(e));
            },
            Ok(Ok(t)) => {
                let ghost prev = view_rows(out@);
                let ghost pts = ts;
                proof {
                    ts = ts.push(t);
                    let tr = g.take(i as int + 1);
                    assert(tr.drop_last() =~= g.take(i as int));
                    assert(ts.drop_last() =~= pts);
                    assert(keep_true(tr, ts) == if t is True { prev.push(g[i as int]) } else { prev });
                }
                if matches!(t, Truth::True) {
                    let row = clone_row(&rows[i]);
                    out.push(row);
                    proof { assert(view_rows(out@) =~= prev.push(g[i as int])); }
                }
            },
        }
        i = i + 1;
    }
    proof {
        lemma_each_done(rs, fs, ts);
        assert(g.take(rows.len() as int) =~= g);
    }
    Ok(Ok(out))
}

/// `SELECT exprs` over evaluated input rows.
pub fn exec_project(db: &EDatabase, ctx: &ERow, exprs: &Vec<EExpr>, rows: &Vec<ERow>) -> (r: Outcome<Vec<ERow>>)
    requires
        db_ts_ok(db@),
        row_ts_ok(view_row(ctx@)),
        rows_ts_ok(view_rows(rows@)),
    ensures
        match r {
            Ok(res) => fits_each(project_results(db@, view_row(ctx@), view_rows(rows@), view_exprs(exprs@)),
                    project_fs(db@, view_row(ctx@), view_rows(rows@), view_exprs(exprs@)))
                && rel_outcome_ok(res, collect(project_results(db@, view_row(ctx@), view_rows(rows@), view_exprs(exprs@)))),
            Err(_) => !fits_each(project_results(db@, view_row(ctx@), view_rows(rows@), view_exprs(exprs@)),
                project_fs(db@, view_row(ctx@), view_rows(rows@), view_exprs(exprs@))),
        },
    decreases exprs, 2nat,
{
    hide(view_expr);
    hide(view_exprs);
    hide(eval_exprs);
    hide(fits_exprs);
    hide(project_fs);
    let ghost gc = view_row(ctx@);
    let ghost g = view_rows(rows@);
    let ghost ge = view_exprs(exprs@);
    let ghost rs = project_results(db@, gc, g, ge);
    let ghost fs = project_fs(db@, gc, g, ge);
    proof { lemma_project_fs_index(db@, gc, g, ge); }
    let mut out: Vec<ERow> = Vec::new();
    let mut i: usize = 0;
    while i < rows.len()
        invariant
            i <= rows.len(), g.len() == rows.len(),
            gc == view_row(ctx@), g == view_rows(rows@), ge == view_exprs(exprs@),
            rs == project_results(db@, gc, g, ge), fs == project_fs(db@, gc, g, ge),
            row_ts_ok(gc), rows_ts_ok(g), db_ts_ok(db@),
            out.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] rs[k] == Ok::<Row, SqlError>(view_rows(out@)[k]),
            fs.len() == rows.len(),
            ok_before(rs, i as int), fits_before(fs, i as int),
            rows_ts_ok(view_rows(out@)),
        decreases rows.len() - i,
    {
        let env = concat_rows(ctx, &rows[i]);
        proof {
            lemma_project_fs_index(db@, gc, g, ge);
            assert(g[i as int] == view_row(rows@[i as int]@));
            lemma_row_ts_ok_concat(gc, g[i as int]);
        }
        match exec_exprs(db, &env, exprs) {
            Err(cap) => {
                proof { lemma_each_capacity(rs, fs, i as int); }
                return Err(cap);
            },
            Ok(Err(e)) => {
                proof { lemma_each_err(rs, fs, i as int); }
                return Ok(Err(e));
            },
            Ok(Ok(vs)) => {
                let ghost prev = view_rows(out@);
                out.push(vs);
                proof { assert(view_rows(out@) =~= prev.push(view_row(vs@))); }
            },
        }
        i = i + 1;
    }
    proof { lemma_each_done(rs, fs, view_rows(out@)); }
    Ok(Ok(out))
}

/// `spec::relation::product_rows`: the left-major cross product.
pub fn product_rows_exec(left: &Vec<ERow>, right: &Vec<ERow>) -> (out: Vec<ERow>)
    requires rows_ts_ok(view_rows(left@)), rows_ts_ok(view_rows(right@)),
    ensures
        view_rows(out@) == product_rows(view_rows(left@), view_rows(right@)),
        rows_ts_ok(view_rows(out@)),
{
    let ghost gl = view_rows(left@);
    let ghost gr = view_rows(right@);
    let mut out: Vec<ERow> = Vec::new();
    let mut i: usize = 0;
    while i < left.len()
        invariant
            i <= left.len(), gl == view_rows(left@), gr == view_rows(right@),
            rows_ts_ok(gl), rows_ts_ok(gr),
            view_rows(out@) == product_rows(gl.take(i as int), gr),
            rows_ts_ok(view_rows(out@)),
        decreases left.len() - i,
    {
        let ghost base = view_rows(out@);
        let ghost li = gl[i as int];
        proof { assert(li == view_row(left@[i as int]@)); }
        let mut j: usize = 0;
        while j < right.len()
            invariant
                i < left.len(), j <= right.len(), gl == view_rows(left@), gr == view_rows(right@),
                li == gl[i as int], li == view_row(left@[i as int]@),
                rows_ts_ok(gl), rows_ts_ok(gr),
                view_rows(out@) == base + pairs_with(li, gr.take(j as int)),
                rows_ts_ok(view_rows(out@)),
            decreases right.len() - j,
        {
            let ghost prev = view_rows(out@);
            let row = concat_rows(&left[i], &right[j]);
            proof {
                assert(gr[j as int] == view_row(right@[j as int]@));
                lemma_row_ts_ok_concat(li, gr[j as int]);
            }
            out.push(row);
            proof {
                assert(view_rows(out@) =~= prev.push(li + gr[j as int]));
                assert(pairs_with(li, gr.take(j as int + 1)) =~= pairs_with(li, gr.take(j as int)).push(li + gr[j as int]));
                assert(view_rows(out@) =~= base + pairs_with(li, gr.take(j as int + 1)));
            }
            j = j + 1;
        }
        proof {
            let t = gl.take(i as int + 1);
            assert(t.drop_last() =~= gl.take(i as int));
            assert(t.last() == li);
            assert(gr.take(gr.len() as int) =~= gr);
            assert(product_rows(t, gr) =~= base + pairs_with(li, gr));
        }
        i = i + 1;
    }
    proof { assert(gl.take(left.len() as int) =~= gl); }
    out
}

/// The LEFT JOIN rows of one left row (the matches, or one NULL-padded row of `right_arity` NULLs):
/// `spec::relation::left_join_one`.
pub fn exec_left_join_row(db: &EDatabase, ctx: &ERow, left_row: &ERow, on: &EPred, right: &Vec<ERow>, right_arity: usize)
    -> (r: Outcome<Vec<ERow>>)
    requires
        db_ts_ok(db@),
        row_ts_ok(view_row(ctx@)),
        row_ts_ok(view_row(left_row@)),
        rows_ts_ok(view_rows(right@)),
    ensures
        ({
            let env = view_row(ctx@) + view_row(left_row@);
            let rs = join_results(db@, env, view_rows(right@), view_pred(*on));
            match r {
                Ok(res) => join_row_fits(db@, env, view_rows(right@), view_pred(*on)) && match res {
                    Ok(out) => collect(rs) is Ok
                        && view_rows(out@) == left_join_one(view_row(left_row@), view_rows(right@), collect(rs)->Ok_0,
                            right_arity as nat)
                        && rows_ts_ok(view_rows(out@)),
                    Err(e) => collect(rs) == Err::<Seq<Truth>, SqlError>(e),
                },
                Err(_) => !join_row_fits(db@, env, view_rows(right@), view_pred(*on)),
            }
        }),
    decreases on, 2nat,
{
    hide(eval_pred);
    hide(fits_pred);
    let ghost gl = view_row(left_row@);
    let ghost genv = view_row(ctx@) + gl;
    let ghost gr = view_rows(right@);
    let ghost gon = view_pred(*on);
    let ghost rs = join_results(db@, genv, gr, gon);
    let ghost fs = join_fs(db@, genv, gr, gon);
    let ghost mut ts: Seq<Truth> = Seq::empty();
    proof {
        lemma_join_row_fits_each(db@, genv, gr, gon);
        lemma_row_ts_ok_concat(view_row(ctx@), gl);
    }
    let env = concat_rows(ctx, left_row);
    let mut matched: Vec<ERow> = Vec::new();
    let mut j: usize = 0;
    while j < right.len()
        invariant
            j <= right.len(), gr.len() == right.len(),
            db_ts_ok(db@),
            gl == view_row(left_row@), genv == view_row(env@), genv == view_row(ctx@) + gl,
            gr == view_rows(right@), gon == view_pred(*on),
            rs == join_results(db@, genv, gr, gon), fs == join_fs(db@, genv, gr, gon),
            fits_each(rs, fs) == join_row_fits(db@, genv, gr, gon),
            row_ts_ok(genv), row_ts_ok(gl), rows_ts_ok(gr),
            ts.len() == j,
            forall|k: int| 0 <= k < j ==> #[trigger] rs[k] == Ok::<Truth, SqlError>(ts[k]),
            ok_before(rs, j as int), fits_before(fs, j as int),
            view_rows(matched@) == pairs_with(gl, keep_true(gr.take(j as int), ts)),
            rows_ts_ok(view_rows(matched@)),
        decreases right.len() - j,
    {
        let env_j = concat_rows(&env, &right[j]);
        proof {
            assert(gr[j as int] == view_row(right@[j as int]@));
            lemma_row_ts_ok_concat(genv, gr[j as int]);
        }
        match exec_pred(db, &env_j, on) {
            Err(cap) => {
                proof { lemma_each_capacity(rs, fs, j as int); }
                return Err(cap);
            },
            Ok(Err(e)) => {
                proof { lemma_each_err(rs, fs, j as int); }
                return Ok(Err(e));
            },
            Ok(Ok(t)) => {
                let ghost prev_kt = keep_true(gr.take(j as int), ts);
                let ghost prev = view_rows(matched@);
                proof {
                    let pts = ts;
                    ts = ts.push(t);
                    let tr = gr.take(j as int + 1);
                    assert(tr.drop_last() =~= gr.take(j as int));
                    assert(ts.drop_last() =~= pts);
                    assert(keep_true(tr, ts) == if t is True { prev_kt.push(gr[j as int]) } else { prev_kt });
                }
                if matches!(t, Truth::True) {
                    let row = concat_rows(left_row, &right[j]);
                    proof { lemma_row_ts_ok_concat(gl, gr[j as int]); }
                    matched.push(row);
                    proof {
                        assert(view_rows(matched@) =~= prev.push(gl + gr[j as int]));
                        assert(pairs_with(gl, prev_kt.push(gr[j as int])) =~= pairs_with(gl, prev_kt).push(gl + gr[j as int]));
                    }
                }
            },
        }
        j = j + 1;
    }
    proof {
        lemma_each_done(rs, fs, ts);
        assert(gr.take(right.len() as int) =~= gr);
    }
    let ghost m = keep_true(gr, ts);
    if matched.len() == 0 {
        let pad = null_row_exec(right_arity);
        let row = concat_rows(left_row, &pad);
        proof { lemma_row_ts_ok_concat(gl, view_row(pad@)); }
        let out = vec![row];
        proof {
            assert(pairs_with(gl, m).len() == m.len());
            assert(view_rows(out@) =~= seq![gl + null_row(right_arity as nat)]);
        }
        Ok(Ok(out))
    } else {
        proof {
            assert(pairs_with(gl, m).len() == m.len());
            assert(pairs_with(gl, m) =~= m.map_values(|r: Row| gl + r));
        }
        Ok(Ok(matched))
    }
}

/// `left LEFT JOIN right ON on` over evaluated inputs; unmatched left rows are padded with `right_arity` NULLs.
pub fn exec_left_join(db: &EDatabase, ctx: &ERow, on: &EPred, left: &Vec<ERow>, right: &Vec<ERow>, right_arity: usize)
    -> (r: Outcome<Vec<ERow>>)
    requires
        db_ts_ok(db@),
        row_ts_ok(view_row(ctx@)),
        rows_ts_ok(view_rows(left@)),
        rows_ts_ok(view_rows(right@)),
    ensures
        ({
            let rs = left_join_results(db@, view_row(ctx@), view_rows(left@), view_rows(right@), view_pred(*on));
            match r {
                Ok(res) => left_join_fits(db@, view_row(ctx@), view_rows(left@), view_rows(right@), view_pred(*on))
                    && rel_outcome_ok(res, match collect(rs) {
                        Err(e) => Err(e),
                        Ok(truths) => Ok(left_join_rows(view_rows(left@), view_rows(right@), truths, right_arity as nat)),
                    }),
                Err(_) => !left_join_fits(db@, view_row(ctx@), view_rows(left@), view_rows(right@), view_pred(*on)),
            }
        }),
    decreases on, 3nat,
{
    hide(eval_pred);
    hide(fits_pred);
    hide(join_row_fits);
    hide(left_join_one);
    let ghost gc = view_row(ctx@);
    let ghost gl = view_rows(left@);
    let ghost gr = view_rows(right@);
    let ghost gon = view_pred(*on);
    let ghost rs = left_join_results(db@, gc, gl, gr, gon);
    let ghost fs = left_join_fs(db@, gc, gl, gr, gon);
    let ghost mut tss: Seq<Seq<Truth>> = Seq::empty();
    proof {
        lemma_left_join_fs(db@, gc, gl, gr, gon);
        lemma_collect_pointwise::<Truth>();
    }
    let mut out: Vec<ERow> = Vec::new();
    let mut i: usize = 0;
    while i < left.len()
        invariant
            i <= left.len(), gl.len() == left.len(),
            db_ts_ok(db@),
            gc == view_row(ctx@), gl == view_rows(left@), gr == view_rows(right@), gon == view_pred(*on),
            rs == left_join_results(db@, gc, gl, gr, gon), fs == left_join_fs(db@, gc, gl, gr, gon),
            fits_each(rs, fs) == left_join_fits(db@, gc, gl, gr, gon),
            forall|rs1: Seq<Result<Truth, SqlError>>, rs2: Seq<Result<Truth, SqlError>>|
                rs1.len() == rs2.len() && (forall|j: int| 0 <= j < rs1.len() ==> rs1[j] == rs2[j])
                ==> #[trigger] collect(rs1) == #[trigger] collect(rs2),
            row_ts_ok(gc), rows_ts_ok(gl), rows_ts_ok(gr),
            tss.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] rs[k] == Ok::<Seq<Truth>, SqlError>(tss[k]),
            ok_before(rs, i as int), fits_before(fs, i as int),
            view_rows(out@) == left_join_rows(gl.take(i as int), gr, tss, right_arity as nat),
            rows_ts_ok(view_rows(out@)),
        decreases left.len() - i,
    {
        proof {
            assert(gl[i as int] == view_row(left@[i as int]@));
            let env = gc + gl[i as int];
            assert(rs[i as int] == collect(join_results(db@, env, gr, gon)));
            assert(fs[i as int] == join_row_fits(db@, env, gr, gon));
        }
        match exec_left_join_row(db, ctx, &left[i], on, right, right_arity) {
            Err(cap) => {
                proof { lemma_each_capacity(rs, fs, i as int); }
                return Err(cap);
            },
            Ok(Err(e)) => {
                proof { lemma_each_err(rs, fs, i as int); }
                return Ok(Err(e));
            },
            Ok(Ok(rows_i)) => {
                let ghost prev = view_rows(out@);
                let ghost ts_i = collect(join_results(db@, gc + gl[i as int], gr, gon))->Ok_0;
                proof {
                    let pts = tss;
                    tss = tss.push(ts_i);
                    let tl = gl.take(i as int + 1);
                    assert(tl.drop_last() =~= gl.take(i as int));
                    assert(tss.drop_last() =~= pts);
                    assert(left_join_rows(tl, gr, tss, right_arity as nat)
                        == prev + left_join_one(gl[i as int], gr, ts_i, right_arity as nat));
                }
                append_rows(&mut out, rows_i);
                proof {
                    assert forall|k: int| 0 <= k < view_rows(out@).len() implies row_ts_ok(#[trigger] view_rows(out@)[k]) by {
                        if k < prev.len() {
                            assert(view_rows(out@)[k] == prev[k]);
                        } else {
                            assert(view_rows(out@)[k] == view_rows(rows_i@)[k - prev.len()]);
                        }
                    }
                }
            },
        }
        i = i + 1;
    }
    proof {
        lemma_each_done(rs, fs, tss);
        assert(gl.take(left.len() as int) =~= gl);
    }
    Ok(Ok(out))
}

/// `spec::eval::query_arity` (static column count; the LEFT JOIN padding width), or `None` when it exceeds `usize`.
pub fn query_arity_exec(schema: &Vec<ETableSchema>, q: &EQuery) -> (r: Option<usize>)
    ensures
        match r {
            Some(n) => n as nat == query_arity(view_schema(schema@), view_query(*q)),
            None => query_arity(view_schema(schema@), view_query(*q)) > usize::MAX,
        },
    decreases q,
{
    match q {
        EQuery::Table(t) => {
            if *t < schema.len() {
                proof { assert(view_schema(schema@)[*t as int] == view_table_schema(schema@[*t as int])); }
                Some(schema[*t].columns.len())
            } else {
                Some(0)
            }
        },
        EQuery::Filter { pred, input } => query_arity_exec(schema, input),
        EQuery::Project { exprs, input } => {
            proof { assert(view_exprs(exprs@).len() == exprs.len()); }
            Some(exprs.len())
        },
        EQuery::Product { left, right } | EQuery::LeftJoin { left, right, .. } => {
            let a = query_arity_exec(schema, left)?;
            let b = query_arity_exec(schema, right)?;
            a.checked_add(b)
        },
        EQuery::Aggregate { aggs, input } => {
            proof { assert(view_aggs(aggs@).len() == aggs.len()); }
            Some(aggs.len())
        },
        EQuery::GroupBy { keys, aggs, input } => {
            proof {
                assert(view_aggs(aggs@).len() == aggs.len());
                assert(view_exprs(keys@).len() == keys.len());
            }
            keys.len().checked_add(aggs.len())
        },
        EQuery::Distinct(input) => query_arity_exec(schema, input),
    }
}

} // verus!
