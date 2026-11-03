//! L2, locality and context independence (engine toolkit; nothing here names a query, a table or a column).
//!
//! A node reads the database only through its base tables and the environment only through its column
//! references. `*_reads(x, r)` says which: every column reference (at any depth, nested subqueries included) is a
//! position `>= r.n` or a context position `i < r.n` with `(r.ctx)(i)`, and every base table `t` has
//! `(r.tables)(t)`. Positions are absolute: every environment of a nested evaluation extends the outer context,
//! so `r.n` is usually the length of the context a node is evaluated in, and positions `>= r.n` are the rows the
//! node itself produces.
//!
//! `lemma_query_local` (and the expression, condition and aggregate forms): two databases of one schema that agree
//! on the tables read (`db_agree`), and two environments of one length that agree on the positions read
//! (`env_agree`), give the same outcome and the same capacity domain (`fits_*`). Corollary
//! `lemma_query_ctx_free`: a node that reads no context position below `n` has one value in every context of
//! length `n` (an uncorrelated subquery can be evaluated once; decorrelation, `engine_link::decorrelate`, uses
//! this).
//!
//! The proof follows the denotation's mutual recursion (measures: expressions `(e, 0)`, lists `(es, 1)`,
//! conditions `(p, 0)`, aggregates `(a, 0)` and `(aggs, 1)`, queries `(q, 2)` dispatching to one lemma per
//! constructor at `(q, 1)`); each step unfolds one node through the named per-row sequences of
//! `exec::relational::domain`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::exec::domain::*;
use crate::exec::relational::domain::*;
use crate::bridge::collect::*;

verus! {

// ------------------------------------------------------------------------------------- what a node reads

/// What a node may read: context positions below `n` only where `ctx` holds (every position from `n` on), and
/// base tables where `tables` holds.
pub struct Reads {
    pub n: nat,
    pub ctx: spec_fn(nat) -> bool,
    pub tables: spec_fn(nat) -> bool,
}

/// Reads nothing of the context below `n`, and any table.
pub open spec fn ctx_free(n: nat) -> Reads {
    Reads { n, ctx: |i: nat| false, tables: |t: nat| true }
}

pub open spec fn col_read_ok(i: nat, r: Reads) -> bool {
    i >= r.n || (r.ctx)(i)
}

pub open spec fn expr_reads(e: Expr, r: Reads) -> bool
    decreases e, 0nat,
{
    match e {
        Expr::Col(i) => col_read_ok(i, r),
        Expr::Lit(_) => true,
        Expr::Neg { kind, arg } => expr_reads(*arg, r),
        Expr::Arith { op, kind, a, b } => expr_reads(*a, r) && expr_reads(*b, r),
        Expr::Cast { cast, arg } => expr_reads(*arg, r),
        Expr::AddInterval { arg, months, days, micros } => expr_reads(*arg, r),
        Expr::Call { f, args } => exprs_reads(args, r),
        Expr::If { cond, then_e, else_e } => pred_reads(*cond, r) && expr_reads(*then_e, r) && expr_reads(*else_e, r),
        Expr::Subquery(q) => query_reads(*q, r),
    }
}

pub open spec fn exprs_reads(es: Seq<Expr>, r: Reads) -> bool
    decreases es, 1nat,
{
    es.len() == 0 || (exprs_reads(es.drop_last(), r) && expr_reads(es.last(), r))
}

pub open spec fn pred_reads(p: Pred, r: Reads) -> bool
    decreases p,
{
    match p {
        Pred::Cmp { op, a, b } => expr_reads(a, r) && expr_reads(b, r),
        Pred::And(a, b) => pred_reads(*a, r) && pred_reads(*b, r),
        Pred::Or(a, b) => pred_reads(*a, r) && pred_reads(*b, r),
        Pred::Not(a) => pred_reads(*a, r),
        Pred::IsNull(e) => expr_reads(e, r),
        Pred::OfBool(e) => expr_reads(e, r),
        Pred::Exists(q) => query_reads(*q, r),
        Pred::AnyCmp { op, e, q } => expr_reads(e, r) && query_reads(*q, r),
    }
}

pub open spec fn agg_reads(a: Agg, r: Reads) -> bool
    decreases a, 0nat,
{
    match a {
        Agg::CountStar => true,
        Agg::Count(e) => expr_reads(e, r),
        Agg::Sum { kind, arg } => expr_reads(arg, r),
        Agg::Min(e) => expr_reads(e, r),
        Agg::Max(e) => expr_reads(e, r),
        Agg::Avg { kind, arg } => expr_reads(arg, r),
        Agg::DistinctAgg(inner) => agg_reads(*inner, r),
    }
}

pub open spec fn aggs_reads(aggs: Seq<Agg>, r: Reads) -> bool
    decreases aggs, 1nat,
{
    aggs.len() == 0 || (aggs_reads(aggs.drop_last(), r) && agg_reads(aggs.last(), r))
}

pub open spec fn query_reads(q: Query, r: Reads) -> bool
    decreases q,
{
    match q {
        Query::Table(t) => (r.tables)(t),
        Query::Filter { pred, input } => pred_reads(pred, r) && query_reads(*input, r),
        Query::Project { exprs, input } => exprs_reads(exprs, r) && query_reads(*input, r),
        Query::Product { left, right } => query_reads(*left, r) && query_reads(*right, r),
        Query::LeftJoin { left, right, on } => query_reads(*left, r) && query_reads(*right, r) && pred_reads(on, r),
        Query::Aggregate { aggs, input } => aggs_reads(aggs, r) && query_reads(*input, r),
        Query::GroupBy { keys, aggs, input } => exprs_reads(keys, r) && aggs_reads(aggs, r) && query_reads(*input, r),
        Query::Distinct(input) => query_reads(*input, r),
    }
}

/// Element view of `exprs_reads`.
pub proof fn lemma_exprs_reads_index(es: Seq<Expr>, r: Reads, i: int)
    requires exprs_reads(es, r), 0 <= i < es.len(),
    ensures expr_reads(es[i], r),
    decreases es.len(),
{
    if i < es.len() - 1 {
        lemma_exprs_reads_index(es.drop_last(), r, i);
        assert(es.drop_last()[i] == es[i]);
    }
}

/// Element view of `aggs_reads`.
pub proof fn lemma_aggs_reads_index(aggs: Seq<Agg>, r: Reads, j: int)
    requires aggs_reads(aggs, r), 0 <= j < aggs.len(),
    ensures agg_reads(aggs[j], r),
    decreases aggs.len(),
{
    if j < aggs.len() - 1 {
        lemma_aggs_reads_index(aggs.drop_last(), r, j);
        assert(aggs.drop_last()[j] == aggs[j]);
    }
}

// ------------------------------------------------------------------------------------- agreement

/// Environments of one length that agree on every position a node with `r` may read.
pub open spec fn env_agree(x: Row, y: Row, r: Reads) -> bool {
    &&& x.len() == y.len()
    &&& forall|i: int| 0 <= i < x.len() && col_read_ok(i as nat, r) ==> #[trigger] x[i] == y[i]
}

/// Databases of one schema and table count that agree on every table a node with `r` may read.
pub open spec fn db_agree(a: Database, b: Database, r: Reads) -> bool {
    &&& a.schema == b.schema
    &&& a.tables.len() == b.tables.len()
    &&& forall|t: int| 0 <= t < a.tables.len() && (r.tables)(t as nat) ==> #[trigger] a.tables[t] == b.tables[t]
}

/// Agreement survives appending the same row (the environment of a row, or of a joined pair).
pub proof fn lemma_env_agree_push(x: Row, y: Row, row: Row, r: Reads)
    requires env_agree(x, y, r),
    ensures env_agree(x + row, y + row, r),
{
    assert forall|i: int| 0 <= i < (x + row).len() && col_read_ok(i as nat, r) implies #[trigger] (x + row)[i] == (y + row)[i] by {
        if i < x.len() {
            assert(x[i] == y[i]);
        }
    }
}

// ------------------------------------------------------------------------------------- the locality theorem

/// L2 for expressions: agreeing databases and environments give the same value and the same domain.
pub proof fn lemma_expr_local(a: Database, b: Database, x: Row, y: Row, e: Expr, r: Reads)
    requires db_agree(a, b, r), env_agree(x, y, r), expr_reads(e, r),
    ensures eval_expr(a, x, e) == eval_expr(b, y, e), fits_expr(a, x, e) == fits_expr(b, y, e),
    decreases e, 0nat,
{
    match e {
        Expr::Col(i) => {
            if i < x.len() {
                assert(x[i as int] == y[i as int]);
            }
        },
        Expr::Lit(_) => {},
        Expr::Neg { kind, arg } => lemma_expr_local(a, b, x, y, *arg, r),
        Expr::Arith { op, kind, a: ea, b: eb } => {
            lemma_expr_local(a, b, x, y, *ea, r);
            lemma_expr_local(a, b, x, y, *eb, r);
        },
        Expr::Cast { cast, arg } => lemma_expr_local(a, b, x, y, *arg, r),
        Expr::AddInterval { arg, months, days, micros } => lemma_expr_local(a, b, x, y, *arg, r),
        Expr::Call { f, args } => lemma_exprs_local(a, b, x, y, args, r),
        Expr::If { cond, then_e, else_e } => {
            lemma_pred_local(a, b, x, y, *cond, r);
            lemma_expr_local(a, b, x, y, *then_e, r);
            lemma_expr_local(a, b, x, y, *else_e, r);
        },
        Expr::Subquery(q) => lemma_query_local(a, b, x, y, *q, r),
    }
}

/// L2 for expression lists (SELECT lists, GROUP BY keys, function arguments).
pub proof fn lemma_exprs_local(a: Database, b: Database, x: Row, y: Row, es: Seq<Expr>, r: Reads)
    requires db_agree(a, b, r), env_agree(x, y, r), exprs_reads(es, r),
    ensures eval_exprs(a, x, es) == eval_exprs(b, y, es), fits_exprs(a, x, es) == fits_exprs(b, y, es),
    decreases es, 1nat,
{
    let (ra, rb) = (expr_results(a, x, es), expr_results(b, y, es));
    assert forall|i: int| 0 <= i < es.len() implies #[trigger] ra[i] == rb[i] by {
        lemma_exprs_reads_index(es, r, i);
        lemma_expr_local(a, b, x, y, es[i], r);
    }
    assert(ra =~= rb);
    if es.len() > 0 {
        lemma_exprs_local(a, b, x, y, es.drop_last(), r);
        lemma_expr_local(a, b, x, y, es.last(), r);
    }
}

/// L2 for conditions.
pub proof fn lemma_pred_local(a: Database, b: Database, x: Row, y: Row, p: Pred, r: Reads)
    requires db_agree(a, b, r), env_agree(x, y, r), pred_reads(p, r),
    ensures eval_pred(a, x, p) == eval_pred(b, y, p), fits_pred(a, x, p) == fits_pred(b, y, p),
    decreases p, 0nat,
{
    match p {
        Pred::Cmp { op, a: ea, b: eb } => {
            lemma_expr_local(a, b, x, y, ea, r);
            lemma_expr_local(a, b, x, y, eb, r);
        },
        Pred::And(pa, pb) => {
            lemma_pred_local(a, b, x, y, *pa, r);
            lemma_pred_local(a, b, x, y, *pb, r);
        },
        Pred::Or(pa, pb) => {
            lemma_pred_local(a, b, x, y, *pa, r);
            lemma_pred_local(a, b, x, y, *pb, r);
        },
        Pred::Not(pa) => lemma_pred_local(a, b, x, y, *pa, r),
        Pred::IsNull(e) => lemma_expr_local(a, b, x, y, e, r),
        Pred::OfBool(e) => lemma_expr_local(a, b, x, y, e, r),
        Pred::Exists(q) => lemma_query_local(a, b, x, y, *q, r),
        Pred::AnyCmp { op, e, q } => {
            lemma_expr_local(a, b, x, y, e, r);
            lemma_query_local(a, b, x, y, *q, r);
        },
    }
}

/// L2 for one aggregate's argument.
pub proof fn lemma_agg_local(a: Database, b: Database, x: Row, y: Row, g: Agg, r: Reads)
    requires db_agree(a, b, r), env_agree(x, y, r), agg_reads(g, r),
    ensures agg_arg(a, x, g) == agg_arg(b, y, g), fits_agg_arg(a, x, g) == fits_agg_arg(b, y, g),
    decreases g, 0nat,
{
    match g {
        Agg::CountStar => {},
        Agg::Count(e) => lemma_expr_local(a, b, x, y, e, r),
        Agg::Sum { kind, arg } => lemma_expr_local(a, b, x, y, arg, r),
        Agg::Min(e) => lemma_expr_local(a, b, x, y, e, r),
        Agg::Max(e) => lemma_expr_local(a, b, x, y, e, r),
        Agg::Avg { kind, arg } => lemma_expr_local(a, b, x, y, arg, r),
        Agg::DistinctAgg(inner) => lemma_agg_local(a, b, x, y, *inner, r),
    }
}

/// L2 for the arguments of a list of aggregates.
pub proof fn lemma_aggs_local(a: Database, b: Database, x: Row, y: Row, aggs: Seq<Agg>, r: Reads)
    requires db_agree(a, b, r), env_agree(x, y, r), aggs_reads(aggs, r),
    ensures
        agg_args(a, x, aggs) == agg_args(b, y, aggs),
        fits_agg_args(a, x, aggs) == fits_agg_args(b, y, aggs),
    decreases aggs, 1nat,
{
    let (ra, rb) = (agg_arg_results(a, x, aggs), agg_arg_results(b, y, aggs));
    let (fa, fb) = (agg_arg_fs(a, x, aggs), agg_arg_fs(b, y, aggs));
    assert forall|j: int| 0 <= j < aggs.len() implies #[trigger] ra[j] == rb[j] && fa[j] == fb[j] by {
        lemma_aggs_reads_index(aggs, r, j);
        lemma_agg_local(a, b, x, y, aggs[j], r);
    }
    assert(ra =~= rb);
    assert(fa =~= fb);
    lemma_agg_args(a, x, aggs);
    lemma_agg_args(b, y, aggs);
}

/// L2. A query reading only the agreed tables and positions has the same outcome and the same capacity domain.
pub proof fn lemma_query_local(a: Database, b: Database, x: Row, y: Row, q: Query, r: Reads)
    requires db_agree(a, b, r), env_agree(x, y, r), query_reads(q, r),
    ensures eval_query(a, x, q) == eval_query(b, y, q), fits_query(a, x, q) == fits_query(b, y, q),
    decreases q, 2nat,
{
    hide(eval_query);
    hide(fits_query);
    match q {
        Query::Table(_) => lemma_table_local(a, b, x, y, q, r),
        Query::Product { .. } => lemma_product_local(a, b, x, y, q, r),
        Query::Distinct(_) => lemma_distinct_local(a, b, x, y, q, r),
        Query::Filter { .. } => lemma_filter_local(a, b, x, y, q, r),
        Query::Project { .. } => lemma_project_local(a, b, x, y, q, r),
        Query::LeftJoin { .. } => lemma_left_join_local(a, b, x, y, q, r),
        Query::Aggregate { .. } => lemma_aggregate_local(a, b, x, y, q, r),
        Query::GroupBy { .. } => lemma_group_by_local(a, b, x, y, q, r),
    }
}

proof fn lemma_table_local(a: Database, b: Database, x: Row, y: Row, q: Query, r: Reads)
    requires q is Table, db_agree(a, b, r), env_agree(x, y, r), query_reads(q, r),
    ensures eval_query(a, x, q) == eval_query(b, y, q), fits_query(a, x, q) == fits_query(b, y, q),
    decreases q, 1nat,
{
    if let Query::Table(t) = q {
        if t < a.tables.len() {
            assert(a.tables[t as int] == b.tables[t as int]);
        }
    }
}

proof fn lemma_product_local(a: Database, b: Database, x: Row, y: Row, q: Query, r: Reads)
    requires q is Product, db_agree(a, b, r), env_agree(x, y, r), query_reads(q, r),
    ensures eval_query(a, x, q) == eval_query(b, y, q), fits_query(a, x, q) == fits_query(b, y, q),
    decreases q, 1nat,
{
    if let Query::Product { left, right } = q {
        lemma_query_local(a, b, x, y, *left, r);
        lemma_query_local(a, b, x, y, *right, r);
    }
}

proof fn lemma_distinct_local(a: Database, b: Database, x: Row, y: Row, q: Query, r: Reads)
    requires q is Distinct, db_agree(a, b, r), env_agree(x, y, r), query_reads(q, r),
    ensures eval_query(a, x, q) == eval_query(b, y, q), fits_query(a, x, q) == fits_query(b, y, q),
    decreases q, 1nat,
{
    if let Query::Distinct(input) = q {
        lemma_query_local(a, b, x, y, *input, r);
    }
}

/// The `Project` case of `fits_query`, unfolded once.
pub proof fn lemma_fits_project_unfold(db: Database, ctx: Row, exprs: Seq<Expr>, input: Box<Query>)
    ensures
        fits_query(db, ctx, Query::Project { exprs, input }) == (fits_query(db, ctx, *input)
            && match eval_query(db, ctx, *input) {
                Err(_) => true,
                Ok(rows) => fits_each(project_results(db, ctx, rows, exprs), project_fs(db, ctx, rows, exprs)),
            }),
{
    hide(eval_query);
}

/// The `Aggregate` case of `fits_query`, unfolded once.
pub proof fn lemma_fits_aggregate_unfold(db: Database, ctx: Row, aggs: Seq<Agg>, input: Box<Query>)
    ensures
        fits_query(db, ctx, Query::Aggregate { aggs, input }) == (fits_query(db, ctx, *input)
            && match eval_query(db, ctx, *input) {
                Err(_) => true,
                Ok(rows) => fits_each(agg_args_results(db, ctx, rows, aggs), agg_args_fs(db, ctx, rows, aggs))
                    && match collect(agg_args_results(db, ctx, rows, aggs)) {
                        Err(_) => true,
                        Ok(args) => fits_agg_row(aggs, args),
                    },
            }),
{
    hide(eval_query);
}

proof fn lemma_filter_local(a: Database, b: Database, x: Row, y: Row, q: Query, r: Reads)
    requires q is Filter, db_agree(a, b, r), env_agree(x, y, r), query_reads(q, r),
    ensures eval_query(a, x, q) == eval_query(b, y, q), fits_query(a, x, q) == fits_query(b, y, q),
    decreases q, 1nat,
{
    hide(eval_query);
    hide(fits_query);
    hide(eval_pred);
    hide(fits_pred);
    if let Query::Filter { pred, input } = q {
        lemma_query_local(a, b, x, y, *input, r);
        lemma_eval_filter(a, x, pred, input);
        lemma_eval_filter(b, y, pred, input);
        lemma_fits_filter(a, x, pred, input);
        lemma_fits_filter(b, y, pred, input);
        if let Ok(rows) = eval_query(a, x, *input) {
            assert forall|i: int|
                #![trigger eval_pred(a, x + rows[i], pred)] #![trigger fits_pred(a, x + rows[i], pred)]
                0 <= i < rows.len() implies
                eval_pred(a, x + rows[i], pred) == eval_pred(b, y + rows[i], pred)
                && fits_pred(a, x + rows[i], pred) == fits_pred(b, y + rows[i], pred) by {
                lemma_env_agree_push(x, y, rows[i], r);
                lemma_pred_local(a, b, x + rows[i], y + rows[i], pred, r);
            }
            let (ra, rb) = (filter_results(a, x, rows, pred), filter_results(b, y, rows, pred));
            assert(ra =~= rb);
            assert(filter_fits(a, x, rows, pred) == filter_fits(b, y, rows, pred)) by {
                if filter_fits(a, x, rows, pred) {
                    assert forall|i: int| 0 <= i < rows.len() && ok_before(rb, i)
                        implies #[trigger] fits_pred(b, y + rows[i], pred) by {
                        assert(fits_pred(a, x + rows[i], pred));
                    }
                }
                if filter_fits(b, y, rows, pred) {
                    assert forall|i: int| 0 <= i < rows.len() && ok_before(ra, i)
                        implies #[trigger] fits_pred(a, x + rows[i], pred) by {
                        assert(fits_pred(b, y + rows[i], pred));
                    }
                }
            }
        }
    }
}

proof fn lemma_project_local(a: Database, b: Database, x: Row, y: Row, q: Query, r: Reads)
    requires q is Project, db_agree(a, b, r), env_agree(x, y, r), query_reads(q, r),
    ensures eval_query(a, x, q) == eval_query(b, y, q), fits_query(a, x, q) == fits_query(b, y, q),
    decreases q, 1nat,
{
    hide(eval_query);
    hide(fits_query);
    hide(eval_exprs);
    hide(fits_exprs);
    if let Query::Project { exprs, input } = q {
        lemma_query_local(a, b, x, y, *input, r);
        lemma_eval_project(a, x, exprs, input);
        lemma_eval_project(b, y, exprs, input);
        lemma_fits_project_unfold(a, x, exprs, input);
        lemma_fits_project_unfold(b, y, exprs, input);
        if let Ok(rows) = eval_query(a, x, *input) {
            assert forall|i: int|
                #![trigger eval_exprs(a, x + rows[i], exprs)] #![trigger fits_exprs(a, x + rows[i], exprs)]
                0 <= i < rows.len() implies
                eval_exprs(a, x + rows[i], exprs) == eval_exprs(b, y + rows[i], exprs)
                && fits_exprs(a, x + rows[i], exprs) == fits_exprs(b, y + rows[i], exprs) by {
                lemma_env_agree_push(x, y, rows[i], r);
                lemma_exprs_local(a, b, x + rows[i], y + rows[i], exprs, r);
            }
            assert(project_results(a, x, rows, exprs) =~= project_results(b, y, rows, exprs));
            lemma_project_fs_index(a, x, rows, exprs);
            lemma_project_fs_index(b, y, rows, exprs);
            assert(project_fs(a, x, rows, exprs) =~= project_fs(b, y, rows, exprs));
        }
    }
}

proof fn lemma_left_join_local(a: Database, b: Database, x: Row, y: Row, q: Query, r: Reads)
    requires q is LeftJoin, db_agree(a, b, r), env_agree(x, y, r), query_reads(q, r),
    ensures eval_query(a, x, q) == eval_query(b, y, q), fits_query(a, x, q) == fits_query(b, y, q),
    decreases q, 1nat,
{
    hide(eval_query);
    hide(fits_query);
    hide(eval_pred);
    hide(fits_pred);
    if let Query::LeftJoin { left, right, on } = q {
        lemma_query_local(a, b, x, y, *left, r);
        lemma_query_local(a, b, x, y, *right, r);
        lemma_eval_left_join(a, x, left, right, on);
        lemma_eval_left_join(b, y, left, right, on);
        lemma_fits_left_join(a, x, left, right, on);
        lemma_fits_left_join(b, y, left, right, on);
        if let (Ok(l), Ok(rr)) = (eval_query(a, x, *left), eval_query(a, x, *right)) {
            assert forall|i: int|
                #![trigger join_results(a, x + l[i], rr, on)] #![trigger join_row_fits(a, x + l[i], rr, on)]
                0 <= i < l.len() implies
                join_results(a, x + l[i], rr, on) == join_results(b, y + l[i], rr, on)
                && join_row_fits(a, x + l[i], rr, on) == join_row_fits(b, y + l[i], rr, on) by {
                lemma_join_row_local(a, b, x + l[i], y + l[i], rr, on, r);
            }
            let (la, lb) = (left_join_results(a, x, l, rr, on), left_join_results(b, y, l, rr, on));
            lemma_collect_pointwise::<Truth>();
            assert forall|i: int| 0 <= i < l.len() implies #[trigger] la[i] == lb[i] by {
                let ja = join_results(a, x + l[i], rr, on);
                let inner_a = Seq::new(rr.len(), |j: int| eval_pred(a, x + l[i] + rr[j], on));
                let inner_b = Seq::new(rr.len(), |j: int| eval_pred(b, y + l[i] + rr[j], on));
                assert(inner_a =~= ja);
                assert(inner_b =~= join_results(b, y + l[i], rr, on));
            }
            assert(la =~= lb);
            assert(left_join_fits(a, x, l, rr, on) == left_join_fits(b, y, l, rr, on)) by {
                if left_join_fits(a, x, l, rr, on) {
                    assert forall|i: int| 0 <= i < l.len() && ok_before(lb, i)
                        implies #[trigger] join_row_fits(b, y + l[i], rr, on) by {
                        assert(join_row_fits(a, x + l[i], rr, on));
                    }
                }
                if left_join_fits(b, y, l, rr, on) {
                    assert forall|i: int| 0 <= i < l.len() && ok_before(la, i)
                        implies #[trigger] join_row_fits(a, x + l[i], rr, on) by {
                        assert(join_row_fits(b, y + l[i], rr, on));
                    }
                }
            }
        }
    }
}

/// One left row of a LEFT JOIN: the ON conditions against every right row agree, and so do their domains.
proof fn lemma_join_row_local(a: Database, b: Database, x: Row, y: Row, rr: Seq<Row>, on: Pred, r: Reads)
    requires db_agree(a, b, r), env_agree(x, y, r), pred_reads(on, r),
    ensures
        join_results(a, x, rr, on) == join_results(b, y, rr, on),
        join_row_fits(a, x, rr, on) == join_row_fits(b, y, rr, on),
    decreases on, 1nat,
{
    hide(eval_pred);
    hide(fits_pred);
    assert forall|j: int|
        #![trigger eval_pred(a, x + rr[j], on)] #![trigger fits_pred(a, x + rr[j], on)]
        0 <= j < rr.len() implies
        eval_pred(a, x + rr[j], on) == eval_pred(b, y + rr[j], on)
        && fits_pred(a, x + rr[j], on) == fits_pred(b, y + rr[j], on) by {
        lemma_env_agree_push(x, y, rr[j], r);
        lemma_pred_local(a, b, x + rr[j], y + rr[j], on, r);
    }
    let (ja, jb) = (join_results(a, x, rr, on), join_results(b, y, rr, on));
    assert(ja =~= jb);
    if join_row_fits(a, x, rr, on) {
        assert forall|j: int| 0 <= j < rr.len() && ok_before(jb, j) implies #[trigger] fits_pred(b, y + rr[j], on) by {
            assert(fits_pred(a, x + rr[j], on));
        }
    }
    if join_row_fits(b, y, rr, on) {
        assert forall|j: int| 0 <= j < rr.len() && ok_before(ja, j) implies #[trigger] fits_pred(a, x + rr[j], on) by {
            assert(fits_pred(b, y + rr[j], on));
        }
    }
}

proof fn lemma_aggregate_local(a: Database, b: Database, x: Row, y: Row, q: Query, r: Reads)
    requires q is Aggregate, db_agree(a, b, r), env_agree(x, y, r), query_reads(q, r),
    ensures eval_query(a, x, q) == eval_query(b, y, q), fits_query(a, x, q) == fits_query(b, y, q),
    decreases q, 1nat,
{
    hide(eval_query);
    hide(fits_query);
    hide(agg_args);
    hide(fits_agg_args);
    if let Query::Aggregate { aggs, input } = q {
        lemma_query_local(a, b, x, y, *input, r);
        lemma_eval_aggregate(a, x, aggs, input);
        lemma_eval_aggregate(b, y, aggs, input);
        lemma_fits_aggregate_unfold(a, x, aggs, input);
        lemma_fits_aggregate_unfold(b, y, aggs, input);
        if let Ok(rows) = eval_query(a, x, *input) {
            assert forall|i: int|
                #![trigger agg_args(a, x + rows[i], aggs)] #![trigger fits_agg_args(a, x + rows[i], aggs)]
                0 <= i < rows.len() implies
                agg_args(a, x + rows[i], aggs) == agg_args(b, y + rows[i], aggs)
                && fits_agg_args(a, x + rows[i], aggs) == fits_agg_args(b, y + rows[i], aggs) by {
                lemma_env_agree_push(x, y, rows[i], r);
                lemma_aggs_local(a, b, x + rows[i], y + rows[i], aggs, r);
            }
            assert(agg_args_results(a, x, rows, aggs) =~= agg_args_results(b, y, rows, aggs));
            lemma_agg_args_fs_index(a, x, rows, aggs);
            lemma_agg_args_fs_index(b, y, rows, aggs);
            assert(agg_args_fs(a, x, rows, aggs) =~= agg_args_fs(b, y, rows, aggs));
        }
    }
}

proof fn lemma_group_by_local(a: Database, b: Database, x: Row, y: Row, q: Query, r: Reads)
    requires q is GroupBy, db_agree(a, b, r), env_agree(x, y, r), query_reads(q, r),
    ensures eval_query(a, x, q) == eval_query(b, y, q), fits_query(a, x, q) == fits_query(b, y, q),
    decreases q, 1nat,
{
    hide(eval_query);
    hide(fits_query);
    hide(eval_exprs);
    hide(fits_exprs);
    hide(agg_args);
    hide(fits_agg_args);
    if let Query::GroupBy { keys, aggs, input } = q {
        lemma_query_local(a, b, x, y, *input, r);
        lemma_eval_group_by(a, x, keys, aggs, input);
        lemma_eval_group_by(b, y, keys, aggs, input);
        lemma_fits_group_by(a, x, keys, aggs, input);
        lemma_fits_group_by(b, y, keys, aggs, input);
        if let Ok(rows) = eval_query(a, x, *input) {
            assert forall|i: int|
                #![trigger eval_exprs(a, x + rows[i], keys)] #![trigger fits_exprs(a, x + rows[i], keys)]
                #![trigger agg_args(a, x + rows[i], aggs)] #![trigger fits_agg_args(a, x + rows[i], aggs)]
                0 <= i < rows.len() implies
                eval_exprs(a, x + rows[i], keys) == eval_exprs(b, y + rows[i], keys)
                && fits_exprs(a, x + rows[i], keys) == fits_exprs(b, y + rows[i], keys)
                && agg_args(a, x + rows[i], aggs) == agg_args(b, y + rows[i], aggs)
                && fits_agg_args(a, x + rows[i], aggs) == fits_agg_args(b, y + rows[i], aggs) by {
                lemma_env_agree_push(x, y, rows[i], r);
                lemma_exprs_local(a, b, x + rows[i], y + rows[i], keys, r);
                lemma_aggs_local(a, b, x + rows[i], y + rows[i], aggs, r);
            }
            assert(group_input_results(a, x, rows, keys, aggs) =~= group_input_results(b, y, rows, keys, aggs));
            assert(group_input_fs(a, x, rows, keys, aggs) =~= group_input_fs(b, y, rows, keys, aggs));
        }
    }
}

// ------------------------------------------------------------------------------------- corollaries

/// A query that reads no context position below `n` has the same outcome and domain in every context of length
/// `n` (and the same database).
pub proof fn lemma_query_ctx_free(db: Database, c1: Row, c2: Row, q: Query)
    requires c1.len() == c2.len(), query_reads(q, ctx_free(c1.len())),
    ensures eval_query(db, c1, q) == eval_query(db, c2, q), fits_query(db, c1, q) == fits_query(db, c2, q),
{
    let r = ctx_free(c1.len());
    assert(env_agree(c1, c2, r));
    lemma_query_local(db, db, c1, c2, q, r);
}

/// The same for an expression (an uncorrelated scalar subquery is the case `Expr::Subquery(q)`).
pub proof fn lemma_expr_ctx_free(db: Database, e1: Row, e2: Row, n: nat, e: Expr)
    requires e1.len() == e2.len(), n == e1.len(), expr_reads(e, ctx_free(n)),
    ensures eval_expr(db, e1, e) == eval_expr(db, e2, e), fits_expr(db, e1, e) == fits_expr(db, e2, e),
{
    let r = ctx_free(n);
    assert(env_agree(e1, e2, r));
    lemma_expr_local(db, db, e1, e2, e, r);
}

} // verus!
