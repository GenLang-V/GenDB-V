//! `revenue0` in normal form and its value in any outer context.
//!
//! The normal form (`qg(lo, hi)`, a `link::query::QuerySpec`) reads lineitem projected on
//! `[l_suppkey, l_extendedprice, l_discount, l_shipdate]` (`cols4`): a row qualifies when `lo <= l_shipdate <= hi`,
//! its group key is `[l_suppkey]` and its SUM argument the coefficient `price * (100 - discount)` at scale 4.
//!
//! `lemma_rev_group` evaluates `revenue0` in an outer context of any length (the GROUP BY link of `link::query`,
//! restated with a context): one row `[key, SUM]` per group key in first-occurrence order. `lemma_max_q` evaluates
//! `SELECT MAX(total_revenue) FROM revenue0` in a product row's context: one row holding the largest group sum (NULL
//! without a group).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::types::*;
use crate::spec::typing::*;
use crate::spec::aggs::minmax::{extremum, extremum_step};
use crate::query::param_typed;
use crate::schema::schema_spec;
use crate::link::query::*;
use crate::link::expr::{ival, i128_max};
use crate::bridge::collect::{lemma_collect_all, lemma_collect_pointwise};
use crate::bridge::equality::same_exact_type;
use crate::spec::equality::row_not_distinct;
use crate::stores::lisupp::declaration::lemma_declared_schema;
use super::window::*;
use super::sql::*;

verus! {

// ------------------------------------------------------------------------------------------------ normal form

/// Table positions of the four columns `revenue0` reads: l_suppkey, l_extendedprice, l_discount, l_shipdate.
pub open spec fn cols4() -> Seq<nat> {
    seq![2nat, 5, 6, 10]
}

/// A row of the four columns.
pub open spec fn li_row(k: int, p: int, d: int, s: int) -> Row {
    seq![Val::Int(k), Val::Num { coeff: p, scale: 2 }, Val::Num { coeff: d, scale: 2 }, Val::Date(s)]
}

/// The WHERE condition on a four-column row: `lo <= l_shipdate <= hi`.
pub open spec fn qual_of(lo: int, hi: int, x: Row) -> bool {
    lo <= ival(x[3]) && ival(x[3]) <= hi
}

/// The SUM argument's coefficient (scale 4) on a four-column row.
pub open spec fn rev_of(x: Row) -> int {
    ival(x[1]) * (100 - ival(x[2]))
}

/// The group key of a four-column row.
pub open spec fn key_of(x: Row) -> Row {
    seq![x[0]]
}

/// `revenue0` in normal form for the window `[lo, hi]`.
pub open spec fn qg(lo: int, hi: int) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| qual_of(lo, hi, x),
        key: |x: Row| key_of(x),
        arg: |j: int, x: Row| rev_of(x),
        aggs: seq![AggKind::Sum { scale: 4 }],
        outs: seq![0nat, 1nat],
        grouped: true,
    }
}

/// The lineitem rows of a database projected on the four columns.
pub open spec fn xd(db: Database) -> Seq<Row> {
    proj_all(db.tables[0], cols4())
}

/// The GROUP BY rows of `revenue0`: `[key, SUM]` per group key, first-occurrence order.
pub open spec fn grows(g: QuerySpec, xs: Seq<Row>) -> Seq<Row> {
    gkeys(g, xs).map_values(|k: Row| full_row(g, xs, k))
}

/// `10^15`: the exclusive bound of a numeric(15, 2) coefficient.
pub open spec fn p15() -> int {
    1_000_000_000_000_000
}

/// A numeric(15, 2) value.
pub open spec fn num2(v: Val) -> bool {
    v == Val::Num { coeff: ival(v), scale: 2 } && -p15() < ival(v) < p15()
}

/// The typing facts the condition, key and argument need of a lineitem row.
pub open spec fn row_typed(r: Row) -> bool {
    &&& r.len() == 16
    &&& r[2] == Val::Int(ival(r[2]))
    &&& num2(r[5])
    &&& num2(r[6])
    &&& r[10] == Val::Date(ival(r[10]))
}

/// The lineitem rows of a database of the schema are typed.
pub proof fn lemma_rows_typed(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures
        db.tables.len() == 8,
        forall|i: int| 0 <= i < db.tables[0].len() ==> row_typed(#[trigger] db.tables[0][i]),
{
    lemma_declared_schema();
    assert(pow10(15) == p15()) by (compute);
    let num = Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false };
    assert(schema_spec()[0].columns[2] == Column { ty: SqlType::Int8, nullable: false }) by (compute);
    assert(schema_spec()[0].columns[5] == num) by (compute);
    assert(schema_spec()[0].columns[6] == num) by (compute);
    assert(schema_spec()[0].columns[10] == Column { ty: SqlType::Date, nullable: false }) by (compute);
    assert forall|i: int| 0 <= i < db.tables[0].len() implies row_typed(#[trigger] db.tables[0][i]) by {
        let r = db.tables[0][i];
        assert(row_in_table(r, db.schema[0]));
        assert(value_in_column(r[2], Column { ty: SqlType::Int8, nullable: false }));
        assert(value_in_column(r[5], num));
        assert(value_in_column(r[6], num));
        assert(value_in_column(r[10], Column { ty: SqlType::Date, nullable: false }));
    }
}

/// The four columns of a row.
pub proof fn lemma_proj4(r: Row)
    requires r.len() == 16,
    ensures
        proj(r, cols4()).len() == 4,
        proj(r, cols4())[0] == r[2],
        proj(r, cols4())[1] == r[5],
        proj(r, cols4())[2] == r[6],
        proj(r, cols4())[3] == r[10],
{
}

/// The normal form's argument values of a row: `[rev_of(x)]` at scale 4.
pub proof fn lemma_arg_vals(lo: int, hi: int, x: Row)
    ensures arg_vals(qg(lo, hi), x) == seq![Val::Num { coeff: rev_of(x), scale: 4 }],
{
    let g = qg(lo, hi);
    assert(arg_vals(g, x) =~= seq![Val::Num { coeff: rev_of(x), scale: 4 }]);
}

// ------------------------------------------------------------------------------------------------ per-row agreement

/// The context `ctx` followed by a row holds the row's columns at `ctx.len() ..`.
pub proof fn lemma_env(ctx: Row, r: Row, c: int)
    requires 0 <= c < r.len(),
    ensures (ctx + r).len() == ctx.len() + r.len(), (ctx + r)[ctx.len() + c] == r[c],
{
}

/// The WHERE condition of `revenue0` in context `ctx` agrees with the normal form on every lineitem row.
pub proof fn lemma_pred_agrees_ctx(db: Database, ctx: Row, ps: Seq<Literal>, hi: int)
    requires
        db.schema == schema_spec(), db_wf(db),
        param_typed(ps),
        hi_ok(lo_of(ps), hi),
    ensures
        forall|i: int| 0 <= i < db.tables[0].len() ==>
            eval_pred(db, ctx + #[trigger] db.tables[0][i], p_date(ctx.len(), ps))
                == Ok::<Truth, SqlError>(truth_of((qg(lo_of(ps), hi).qual)(proj(db.tables[0][i], cols4())))),
{
    lemma_rows_typed(db);
    let o = ctx.len();
    assert forall|i: int| 0 <= i < db.tables[0].len() implies
        eval_pred(db, ctx + #[trigger] db.tables[0][i], p_date(o, ps))
            == Ok::<Truth, SqlError>(truth_of((qg(lo_of(ps), hi).qual)(proj(db.tables[0][i], cols4())))) by {
        let r = db.tables[0][i];
        assert(row_typed(r));
        lemma_env(ctx, r, 10);
        lemma_proj4(r);
        lemma_pred_row(db, ctx + r, o, ps, hi, ival(r[10]));
    }
}

/// The filter of `revenue0` in context `ctx`: the rows whose projection qualifies.
pub proof fn lemma_rev_filter(db: Database, ctx: Row, ps: Seq<Literal>, hi: int)
    requires
        db.schema == schema_spec(), db_wf(db),
        param_typed(ps),
        hi_ok(lo_of(ps), hi),
    ensures ({
        let g = qg(lo_of(ps), hi);
        let rows = db.tables[0];
        eval_query(db, ctx, rev_filter(ctx.len(), ps))
            == Ok::<Relation, SqlError>(keep_true(rows, qual_truths(g, proj_all(rows, cols4()))))
    }),
{
    let g = qg(lo_of(ps), hi);
    let rows = db.tables[0];
    let o = ctx.len();
    let xs = proj_all(rows, cols4());
    let truths = qual_truths(g, xs);
    lemma_rows_typed(db);
    lemma_pred_agrees_ctx(db, ctx, ps, hi);
    let prs = Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], p_date(o, ps)));
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        assert(xs[i] == proj(rows[i], cols4()));
        assert(eval_pred(db, ctx + rows[i], p_date(o, ps)) == Ok::<Truth, SqlError>(truth_of((g.qual)(proj(rows[i], cols4())))));
    }
    lemma_collect_all(prs, truths);
    lemma_collect_pointwise::<Truth>();
    assert(eval_query(db, ctx, Query::Table(0)) == Ok::<Relation, SqlError>(rows));
}

/// Per kept row of `revenue0`'s filter: its key and argument row (the GROUP BY's prepared sequence, context `ctx`).
pub proof fn lemma_prepared_ctx(db: Database, ctx: Row, ps: Seq<Literal>, hi: int, kept: Seq<Row>)
    requires
        db.schema == schema_spec(), db_wf(db),
        forall|i: int| 0 <= i < kept.len() ==> db.tables[0].contains(#[trigger] kept[i]),
    ensures ({
        let g = qg(lo_of(ps), hi);
        let o = ctx.len();
        collect(Seq::new(kept.len(), |i: int|
            match eval_exprs(db, ctx + kept[i], rev_keys(o)) {
                Err(err) => Err(err),
                Ok(k) => match agg_args(db, ctx + kept[i], rev_aggs(o)) {
                    Err(err) => Err(err),
                    Ok(a) => Ok((k, a)),
                },
            }))
            == Ok::<Seq<(Row, Row)>, SqlError>(Seq::new(kept.len(), |i: int| ((g.key)(proj(kept[i], cols4())), arg_vals(g, proj(kept[i], cols4())))))
    }),
{
    hide(eval_exprs);
    hide(agg_args);
    let g = qg(lo_of(ps), hi);
    let o = ctx.len();
    lemma_rows_typed(db);
    let prep = Seq::new(kept.len(), |i: int| ((g.key)(proj(kept[i], cols4())), arg_vals(g, proj(kept[i], cols4()))));
    let pre = Seq::new(kept.len(), |i: int|
        match eval_exprs(db, ctx + kept[i], rev_keys(o)) {
            Err(err) => Err(err),
            Ok(k) => match agg_args(db, ctx + kept[i], rev_aggs(o)) {
                Err(err) => Err(err),
                Ok(a) => Ok((k, a)),
            },
        });
    assert forall|i: int| 0 <= i < pre.len() implies #[trigger] pre[i] == Ok::<(Row, Row), SqlError>(prep[i]) by {
        let r = kept[i];
        let m = choose|m: int| 0 <= m < db.tables[0].len() && db.tables[0][m] == r;
        assert(row_typed(db.tables[0][m]));
        let env = ctx + r;
        lemma_env(ctx, r, 2);
        lemma_env(ctx, r, 5);
        lemma_env(ctx, r, 6);
        lemma_proj4(r);
        lemma_keys_row(db, env, o);
        lemma_args_row(db, env, o, ival(r[5]), ival(r[6]));
        let x = proj(r, cols4());
        lemma_arg_vals(lo_of(ps), hi, x);
        assert((g.key)(x) =~= seq![env[(o + 2) as int]]);
    }
    lemma_collect_all(pre, prep);
}

/// One step of the GROUP BY denotation in context `ctx`.
pub proof fn lemma_groupby_unfold_ctx(db: Database, ctx: Row, input: Query, keys: Seq<Expr>, aggs: Seq<Agg>, kept: Seq<Row>,
    prep: Seq<(Row, Row)>)
    requires
        eval_query(db, ctx, input) == Ok::<Relation, SqlError>(kept),
        collect(Seq::new(kept.len(), |i: int|
            match eval_exprs(db, ctx + kept[i], keys) {
                Err(err) => Err(err),
                Ok(k) => match agg_args(db, ctx + kept[i], aggs) {
                    Err(err) => Err(err),
                    Ok(a) => Ok((k, a)),
                },
            })) == Ok::<Seq<(Row, Row)>, SqlError>(prep),
    ensures
        eval_query(db, ctx, Query::GroupBy { keys, aggs, input: Box::new(input) })
            == group_rows(aggs, prep.map_values(|p: (Row, Row)| p.0), prep.map_values(|p: (Row, Row)| p.1)),
{
    lemma_collect_pointwise::<(Row, Row)>();
}

/// The aggregate list matches the normal form.
pub proof fn lemma_aggs_match(o: nat, lo: int, hi: int)
    ensures aggs_match(rev_aggs(o), qg(lo, hi)),
{
    assert(agg_matches(rev_aggs(o)[0], qg(lo, hi).aggs[0]));
}

/// On the normal form's keys (one bigint), SQL "not distinct" is equality.
pub proof fn lemma_keys_exact(db: Database, lo: int, hi: int)
    requires db.schema == schema_spec(), db_wf(db),
    ensures keys_exact(qg(lo, hi), xd(db)),
{
    let g = qg(lo, hi);
    let xs = xd(db);
    lemma_rows_typed(db);
    lemma_proj_all_len(db.tables[0]);
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        let ra = db.tables[0][a];
        let rb = db.tables[0][b];
        assert(row_typed(ra) && row_typed(rb));
        assert(xs[a] == proj(ra, cols4()));
        assert(xs[b] == proj(rb, cols4()));
        lemma_proj4(ra);
        lemma_proj4(rb);
        let ka = (g.key)(xs[a]);
        let kb = (g.key)(xs[b]);
        assert(ka[0] == ra[2] && kb[0] == rb[2]);
        assert(same_exact_type(ka[0], kb[0]));
        lemma_row_exact(ka, kb);
    }
}

/// `proj_all` keeps the length and projects each row.
pub proof fn lemma_proj_all_len(rows: Seq<Row>)
    ensures
        proj_all(rows, cols4()).len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> #[trigger] proj_all(rows, cols4())[i] == proj(rows[i], cols4()),
{
    crate::link::source::lemma_proj_all_index(rows, cols4());
}

/// `revenue0` in any outer context: one row `[key, SUM]` per group key, in first-occurrence order, inside the SUM
/// capacity condition (`group_caps`).
pub proof fn lemma_rev_group(db: Database, ctx: Row, ps: Seq<Literal>, hi: int)
    requires
        db.schema == schema_spec(), db_wf(db),
        param_typed(ps),
        hi_ok(lo_of(ps), hi),
        group_caps(qg(lo_of(ps), hi), xd(db)),
    ensures
        eval_query(db, ctx, rev_group(ctx.len(), ps)) == Ok::<Relation, SqlError>(grows(qg(lo_of(ps), hi), xd(db))),
{
    hide(eval_pred);
    hide(eval_exprs);
    hide(agg_args);
    hide(group_rows);
    let g = qg(lo_of(ps), hi);
    let rows = db.tables[0];
    let xs = xd(db);
    let o = ctx.len();
    let kept = keep_true(rows, qual_truths(g, xs));
    lemma_rev_filter(db, ctx, ps, hi);
    lemma_kept_rows(g, rows, cols4());
    lemma_prepared_ctx(db, ctx, ps, hi, kept);
    let prep = Seq::new(kept.len(), |i: int| ((g.key)(proj(kept[i], cols4())), arg_vals(g, proj(kept[i], cols4()))));
    let q = qrows(g, xs);
    assert(prep.map_values(|p: (Row, Row)| p.0) =~= qkeys(g, xs));
    assert(prep.map_values(|p: (Row, Row)| p.1) =~= q.map_values(|x: Row| arg_vals(g, x)));
    lemma_aggs_match(o, lo_of(ps), hi);
    lemma_keys_exact(db, lo_of(ps), hi);
    lemma_groups(g, rev_aggs(o), xs);
    lemma_groupby_unfold_ctx(db, ctx, rev_filter(o, ps), rev_keys(o), rev_aggs(o), kept, prep);
}

// ------------------------------------------------------------------------------------------------ MAX

/// The SUM column of the GROUP BY rows.
pub open spec fn gvals(g: QuerySpec, xs: Seq<Row>) -> Seq<Val> {
    gkeys(g, xs).map_values(|k: Row| Val::Num { coeff: gsum(g, xs, k, 0), scale: 4 })
}

/// MAX over numerics of one scale `s`: NULL on no value, else one of the values, at least every value.
pub proof fn lemma_max_num(vs: Seq<Val>, s: nat)
    requires forall|i: int| 0 <= i < vs.len() ==> (#[trigger] vs[i]) is Num && vs[i]->scale == s,
    ensures
        extremum(true, vs) is Ok,
        vs.len() == 0 ==> extremum(true, vs) == Ok::<Val, SqlError>(Val::Null),
        vs.len() > 0 ==> ({
            let r = extremum(true, vs)->Ok_0;
            &&& r is Num && r->scale == s
            &&& exists|i: int| 0 <= i < vs.len() && vs[i] == r
            &&& forall|i: int| 0 <= i < vs.len() ==> (#[trigger] vs[i])->coeff <= r->coeff
        }),
    decreases vs.len(),
{
    if vs.len() > 0 {
        let d = vs.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies (#[trigger] d[i]) is Num && d[i]->scale == s by {
            assert(d[i] == vs[i]);
        }
        lemma_max_num(d, s);
        let v = vs.last();
        let acc = extremum(true, d)->Ok_0;
        assert(vs[vs.len() - 1] == v);
        if d.len() == 0 {
            assert(extremum(true, vs) == extremum_step(true, Val::Null, v));
            assert(vs[0] == v);
        } else {
            let (cv, ca) = (v->coeff, acc->coeff);
            crate::link::expr::lemma_compare_num(cv, s, ca, s);
            crate::link::expr::lemma_align_same(cv, s);
            crate::link::expr::lemma_align_same(ca, s);
            assert(compare(v, acc) == Some(sign(cv - ca)));
            let r = extremum(true, vs)->Ok_0;
            let i0 = choose|i: int| 0 <= i < d.len() && d[i] == acc;
            assert(vs[i0] == acc);
            if cv > ca {
                assert(r == v);
            } else {
                assert(r == acc);
            }
            assert forall|i: int| 0 <= i < vs.len() implies (#[trigger] vs[i])->coeff <= r->coeff by {
                if i < d.len() {
                    assert(vs[i] == d[i]);
                }
            }
        }
    }
}

/// The GROUP BY rows are `[key, Num(sum, 4)]` with a one-value key, and their SUM column is `gvals`.
pub proof fn lemma_grows(g: QuerySpec, xs: Seq<Row>, lo: int, hi: int)
    requires g == qg(lo, hi),
    ensures
        grows(g, xs).len() == gkeys(g, xs).len(),
        forall|i: int| 0 <= i < grows(g, xs).len() ==> (#[trigger] grows(g, xs)[i]).len() == 2
            && grows(g, xs)[i][0] == gkeys(g, xs)[i][0]
            && grows(g, xs)[i][1] == gvals(g, xs)[i]
            && gkeys(g, xs)[i] == seq![gkeys(g, xs)[i][0]],
{
    let ks = gkeys(g, xs);
    lemma_gkeys(g, xs);
    assert forall|i: int| 0 <= i < grows(g, xs).len() implies (#[trigger] grows(g, xs)[i]).len() == 2
        && grows(g, xs)[i][0] == ks[i][0]
        && grows(g, xs)[i][1] == gvals(g, xs)[i]
        && ks[i] == seq![ks[i][0]] by {
        let k = ks[i];
        assert(ks.contains(k));
        lemma_gkeys_witness(g, xs, k);
        let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], k);
        assert(k == key_of(xs[m]));
        assert(k =~= seq![k[0]]);
        let outs = agg_outs(g, xs, k);
        assert(outs =~= seq![Val::Num { coeff: gsum(g, xs, k, 0), scale: 4 }]);
        assert(full_row(g, xs, k) =~= seq![k[0], Val::Num { coeff: gsum(g, xs, k, 0), scale: 4 }]);
    }
}

/// The MAX argument on a GROUP BY row in a product row's context: its SUM column.
proof fn lemma_max_arg(db: Database, ctx: Row, gr: Row, v: Val)
    requires ctx.len() == 9, gr.len() == 2, gr[1] == v,
    ensures agg_args(db, ctx + gr, max_aggs()) == Ok::<Row, SqlError>(seq![v]),
{
    let env = ctx + gr;
    lemma_env(ctx, gr, 1);
    let rs = agg_arg_results(db, env, max_aggs());
    lemma_agg_arg_results_index(db, env, max_aggs());
    assert(rs[0] == eval_expr(db, env, Expr::Col(10)));
    assert(rs[0] == Ok::<Val, SqlError>(v));
    assert(rs.drop_last().len() == 0);
    assert(collect(rs.drop_last()) == Ok::<Seq<Val>, SqlError>(Seq::empty()));
    assert(Seq::<Val>::empty().push(v) =~= seq![v]);
}

/// One step of the Aggregate denotation in context `ctx`.
proof fn lemma_aggregate_unfold_ctx(db: Database, ctx: Row, input: Query, aggs: Seq<Agg>, kept: Seq<Row>, args: Seq<Row>)
    requires
        eval_query(db, ctx, input) == Ok::<Relation, SqlError>(kept),
        collect(Seq::new(kept.len(), |i: int| agg_args(db, ctx + kept[i], aggs))) == Ok::<Seq<Row>, SqlError>(args),
    ensures
        eval_query(db, ctx, Query::Aggregate { aggs, input: Box::new(input) })
            == match agg_row(aggs, args) {
                Err(err) => Err(err),
                Ok(row) => Ok::<Relation, SqlError>(seq![row]),
            },
{
    lemma_collect_pointwise::<Row>();
}

/// The MAX aggregate row over one-value argument rows.
proof fn lemma_max_row(args: Seq<Row>, vs: Seq<Val>, mv: Val)
    requires
        args.len() == vs.len(),
        forall|i: int| 0 <= i < args.len() ==> #[trigger] args[i] == seq![vs[i]],
        extremum(true, vs) == Ok::<Val, SqlError>(mv),
    ensures agg_row(max_aggs(), args) == Ok::<Row, SqlError>(seq![mv]),
{
    assert(column(args, 0) =~= vs);
    let ars = Seq::new(max_aggs().len(), |j: int| agg_value(max_aggs()[j], column(args, j)));
    assert(ars[0] == Ok::<Val, SqlError>(mv));
    lemma_collect_all(ars, seq![mv]);
}

/// `SELECT MAX(total_revenue) FROM revenue0` in a product row's context: one row with the MAX of the group sums.
pub proof fn lemma_max_q(db: Database, ctx: Row, ps: Seq<Literal>, hi: int)
    requires
        db.schema == schema_spec(), db_wf(db),
        param_typed(ps),
        hi_ok(lo_of(ps), hi),
        group_caps(qg(lo_of(ps), hi), xd(db)),
        ctx.len() == 9,
    ensures ({
        let g = qg(lo_of(ps), hi);
        &&& extremum(true, gvals(g, xd(db))) is Ok
        &&& eval_query(db, ctx, max_q(ps)) == Ok::<Relation, SqlError>(seq![seq![extremum(true, gvals(g, xd(db)))->Ok_0]])
    }),
{
    hide(agg_args);
    hide(eval_query);
    hide(agg_row);
    let g = qg(lo_of(ps), hi);
    let xs = xd(db);
    let gr = grows(g, xs);
    let vs = gvals(g, xs);
    lemma_rev_group(db, ctx, ps, hi);
    lemma_grows(g, xs, lo_of(ps), hi);
    assert forall|i: int| 0 <= i < vs.len() implies (#[trigger] vs[i]) is Num && vs[i]->scale == 4 by {}
    lemma_max_num(vs, 4);
    let mv = extremum(true, vs)->Ok_0;
    let args = Seq::new(gr.len(), |i: int| seq![vs[i]]);
    let pre = Seq::new(gr.len(), |i: int| agg_args(db, ctx + gr[i], max_aggs()));
    assert forall|i: int| 0 <= i < pre.len() implies #[trigger] pre[i] == Ok::<Row, SqlError>(args[i]) by {
        lemma_max_arg(db, ctx, gr[i], vs[i]);
    }
    lemma_collect_all(pre, args);
    lemma_max_row(args, vs, mv);
    lemma_aggregate_unfold_ctx(db, ctx, rev_group(9, ps), max_aggs(), gr, args);
}

} // verus!
