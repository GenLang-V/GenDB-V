//! L5 column references through a column map: evaluate a canonical node on physical rows (engine toolkit; nothing
//! here names a query, a table or a column).
//!
//! A canonical environment `x` (outer context, then the canonical row) and a physical environment `y` are related
//! by a `ColMap` `m` and the physical prefix length `n` (`env_mapped`): every canonical position `i < |m|` that the
//! node reads is the physical position `m[i] < n`, and every position from `|m|` on (the rows nested evaluation
//! appends) is the physical position `i - |m| + n`. Entries `m[i] >= n` mark canonical positions that are not in
//! the physical environment (pruned columns); a node may not read them (`remap_reads`, a `locality::Reads`).
//!
//! `remap_expr(e, m, n)` (and the condition, aggregate, list and query forms) rewrites every column reference `i`,
//! at any depth, nested subqueries included, to `remap_col(m, n, i)`. Positions are absolute, so one rewrite serves
//! every nesting level. `lemma_query_remap`: the rewritten node on the physical environment has the canonical
//! node's outcome and capacity domain (`fits_*`). Uses: a join condition over a reordered join tree, a conjunct
//! pushed below a join and evaluated on one input's rows (`engine_link::joins`), expressions over pruned rows.
//!
//! The proof follows the denotation's mutual recursion like `engine_link::locality` (measures: expressions
//! `(e, 0)`, lists `(es, 1)`, conditions `(p, 0)`, aggregates `(a, 0)` and `(aggs, 1)`, queries `(q, 2)`
//! dispatching to one lemma per constructor at `(q, 1)`). The rewrite keeps every aggregate's kind, so aggregate
//! values and GROUP BY results over equal argument rows are equal (`lemma_agg_row_remap`), and every query's arity
//! (`lemma_remap_arity`, the LEFT JOIN padding width).
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::equality::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::exec::domain::*;
use crate::exec::relational::domain::*;
use crate::bridge::collect::*;
use crate::engine_link::colmap::ColMap;
use crate::engine_link::locality::*;

verus! {

// ------------------------------------------------------------------------------------- environments

/// The physical position of canonical position `i`: `m[i]` below `|m|`, the nested rows shifted after.
pub open spec fn remap_col(m: ColMap, n: nat, i: nat) -> nat {
    if i < m.len() { m[i as int] } else { (i - m.len() + n) as nat }
}

/// What a node evaluated through `m` may read: canonical positions below `|m|` that are physical (`m[i] < n`),
/// every nested position, any table.
pub open spec fn remap_reads(m: ColMap, n: nat) -> Reads {
    Reads { n: m.len(), ctx: |i: nat| m[i as int] < n, tables: |t: nat| true }
}

/// Canonical environment `x` and physical environment `y` (physical prefix of length `n`) agree through `m` on
/// every position a node with `remap_reads(m, n)` may read; their nested parts have one length.
pub open spec fn env_mapped(x: Row, y: Row, m: ColMap, n: nat) -> bool {
    &&& m.len() <= x.len()
    &&& n <= y.len()
    &&& x.len() - m.len() == y.len() - n
    &&& forall|i: int| 0 <= i < x.len() && col_read_ok(i as nat, remap_reads(m, n))
        ==> #[trigger] x[i] == y[remap_col(m, n, i as nat) as int]
}

/// The mapped positions lie inside the physical environment.
pub proof fn lemma_env_mapped_bound(x: Row, y: Row, m: ColMap, n: nat, i: nat)
    requires env_mapped(x, y, m, n), i < x.len(), col_read_ok(i, remap_reads(m, n)),
    ensures remap_col(m, n, i) < y.len(),
{
}

/// The relation survives appending the same row to both environments (a nested row, or a joined pair).
pub proof fn lemma_env_mapped_push(x: Row, y: Row, row: Row, m: ColMap, n: nat)
    requires env_mapped(x, y, m, n),
    ensures env_mapped(x + row, y + row, m, n),
{
    let r = remap_reads(m, n);
    assert forall|i: int| 0 <= i < (x + row).len() && col_read_ok(i as nat, r)
        implies #[trigger] (x + row)[i] == (y + row)[remap_col(m, n, i as nat) as int] by {
        if i < x.len() {
            assert(x[i] == y[remap_col(m, n, i as nat) as int]);
        } else {
            assert(remap_col(m, n, i as nat) == i - x.len() + y.len());
        }
    }
}

/// Table `t` may be read.
pub open spec fn table_ok(t: nat, r: Reads) -> bool {
    (r.tables)(t)
}

/// Every position and every table may be read (a column map without absent entries).
pub open spec fn reads_all(r: Reads) -> bool {
    &&& forall|i: nat| #[trigger] col_read_ok(i, r)
    &&& forall|t: nat| #[trigger] table_ok(t, r)
}

pub proof fn lemma_expr_reads_all(e: Expr, r: Reads)
    requires reads_all(r),
    ensures expr_reads(e, r),
    decreases e, 0nat,
{
    match e {
        Expr::Col(i) => assert(col_read_ok(i, r)),
        Expr::Lit(_) => {},
        Expr::Neg { kind, arg } => lemma_expr_reads_all(*arg, r),
        Expr::Arith { op, kind, a, b } => {
            lemma_expr_reads_all(*a, r);
            lemma_expr_reads_all(*b, r);
        },
        Expr::Cast { cast, arg } => lemma_expr_reads_all(*arg, r),
        Expr::AddInterval { arg, months, days, micros } => lemma_expr_reads_all(*arg, r),
        Expr::Call { f, args } => lemma_exprs_reads_all(args, r),
        Expr::If { cond, then_e, else_e } => {
            lemma_pred_reads_all(*cond, r);
            lemma_expr_reads_all(*then_e, r);
            lemma_expr_reads_all(*else_e, r);
        },
        Expr::Subquery(q) => lemma_query_reads_all(*q, r),
    }
}

pub proof fn lemma_exprs_reads_all(es: Seq<Expr>, r: Reads)
    requires reads_all(r),
    ensures exprs_reads(es, r),
    decreases es, 1nat,
{
    if es.len() > 0 {
        lemma_exprs_reads_all(es.drop_last(), r);
        lemma_expr_reads_all(es.last(), r);
    }
}

/// Every condition reads only what `r` allows when `r` allows everything.
pub proof fn lemma_pred_reads_all(p: Pred, r: Reads)
    requires reads_all(r),
    ensures pred_reads(p, r),
    decreases p, 0nat,
{
    match p {
        Pred::Cmp { op, a, b } => {
            lemma_expr_reads_all(a, r);
            lemma_expr_reads_all(b, r);
        },
        Pred::And(a, b) => {
            lemma_pred_reads_all(*a, r);
            lemma_pred_reads_all(*b, r);
        },
        Pred::Or(a, b) => {
            lemma_pred_reads_all(*a, r);
            lemma_pred_reads_all(*b, r);
        },
        Pred::Not(a) => lemma_pred_reads_all(*a, r),
        Pred::IsNull(e) => lemma_expr_reads_all(e, r),
        Pred::OfBool(e) => lemma_expr_reads_all(e, r),
        Pred::Exists(q) => lemma_query_reads_all(*q, r),
        Pred::AnyCmp { op, e, q } => {
            lemma_expr_reads_all(e, r);
            lemma_query_reads_all(*q, r);
        },
    }
}

pub proof fn lemma_agg_reads_all(a: Agg, r: Reads)
    requires reads_all(r),
    ensures agg_reads(a, r),
    decreases a, 0nat,
{
    match a {
        Agg::CountStar => {},
        Agg::Count(e) => lemma_expr_reads_all(e, r),
        Agg::Sum { kind, arg } => lemma_expr_reads_all(arg, r),
        Agg::Min(e) => lemma_expr_reads_all(e, r),
        Agg::Max(e) => lemma_expr_reads_all(e, r),
        Agg::Avg { kind, arg } => lemma_expr_reads_all(arg, r),
        Agg::DistinctAgg(inner) => lemma_agg_reads_all(*inner, r),
    }
}

pub proof fn lemma_aggs_reads_all(aggs: Seq<Agg>, r: Reads)
    requires reads_all(r),
    ensures aggs_reads(aggs, r),
    decreases aggs, 1nat,
{
    if aggs.len() > 0 {
        lemma_aggs_reads_all(aggs.drop_last(), r);
        lemma_agg_reads_all(aggs.last(), r);
    }
}

/// Every query reads only what `r` allows when `r` allows everything.
pub proof fn lemma_query_reads_all(q: Query, r: Reads)
    requires reads_all(r),
    ensures query_reads(q, r),
    decreases q, 2nat,
{
    match q {
        Query::Table(t) => assert(table_ok(t, r)),
        Query::Filter { pred, input } => {
            lemma_pred_reads_all(pred, r);
            lemma_query_reads_all(*input, r);
        },
        Query::Project { exprs, input } => {
            lemma_exprs_reads_all(exprs, r);
            lemma_query_reads_all(*input, r);
        },
        Query::Product { left, right } => {
            lemma_query_reads_all(*left, r);
            lemma_query_reads_all(*right, r);
        },
        Query::LeftJoin { left, right, on } => {
            lemma_query_reads_all(*left, r);
            lemma_query_reads_all(*right, r);
            lemma_pred_reads_all(on, r);
        },
        Query::Aggregate { aggs, input } => {
            lemma_aggs_reads_all(aggs, r);
            lemma_query_reads_all(*input, r);
        },
        Query::GroupBy { keys, aggs, input } => {
            lemma_exprs_reads_all(keys, r);
            lemma_aggs_reads_all(aggs, r);
            lemma_query_reads_all(*input, r);
        },
        Query::Distinct(input) => lemma_query_reads_all(*input, r),
    }
}

// ------------------------------------------------------------------------------------- the rewrite

pub open spec fn remap_expr(e: Expr, m: ColMap, n: nat) -> Expr
    decreases e, 0nat,
{
    match e {
        Expr::Col(i) => Expr::Col(remap_col(m, n, i)),
        Expr::Lit(l) => Expr::Lit(l),
        Expr::Neg { kind, arg } => Expr::Neg { kind, arg: Box::new(remap_expr(*arg, m, n)) },
        Expr::Arith { op, kind, a, b } =>
            Expr::Arith { op, kind, a: Box::new(remap_expr(*a, m, n)), b: Box::new(remap_expr(*b, m, n)) },
        Expr::Cast { cast, arg } => Expr::Cast { cast, arg: Box::new(remap_expr(*arg, m, n)) },
        Expr::AddInterval { arg, months, days, micros } =>
            Expr::AddInterval { arg: Box::new(remap_expr(*arg, m, n)), months, days, micros },
        Expr::Call { f, args } => Expr::Call { f, args: remap_exprs(args, m, n) },
        Expr::If { cond, then_e, else_e } => Expr::If {
            cond: Box::new(remap_pred(*cond, m, n)),
            then_e: Box::new(remap_expr(*then_e, m, n)),
            else_e: Box::new(remap_expr(*else_e, m, n)),
        },
        Expr::Subquery(q) => Expr::Subquery(Box::new(remap_query(*q, m, n))),
    }
}

pub open spec fn remap_exprs(es: Seq<Expr>, m: ColMap, n: nat) -> Seq<Expr>
    decreases es, 1nat,
{
    if es.len() == 0 { Seq::empty() } else { remap_exprs(es.drop_last(), m, n).push(remap_expr(es.last(), m, n)) }
}

pub open spec fn remap_pred(p: Pred, m: ColMap, n: nat) -> Pred
    decreases p,
{
    match p {
        Pred::Cmp { op, a, b } => Pred::Cmp { op, a: remap_expr(a, m, n), b: remap_expr(b, m, n) },
        Pred::And(a, b) => Pred::And(Box::new(remap_pred(*a, m, n)), Box::new(remap_pred(*b, m, n))),
        Pred::Or(a, b) => Pred::Or(Box::new(remap_pred(*a, m, n)), Box::new(remap_pred(*b, m, n))),
        Pred::Not(a) => Pred::Not(Box::new(remap_pred(*a, m, n))),
        Pred::IsNull(e) => Pred::IsNull(remap_expr(e, m, n)),
        Pred::OfBool(e) => Pred::OfBool(remap_expr(e, m, n)),
        Pred::Exists(q) => Pred::Exists(Box::new(remap_query(*q, m, n))),
        Pred::AnyCmp { op, e, q } => Pred::AnyCmp { op, e: remap_expr(e, m, n), q: Box::new(remap_query(*q, m, n)) },
    }
}

pub open spec fn remap_agg(a: Agg, m: ColMap, n: nat) -> Agg
    decreases a, 0nat,
{
    match a {
        Agg::CountStar => Agg::CountStar,
        Agg::Count(e) => Agg::Count(remap_expr(e, m, n)),
        Agg::Sum { kind, arg } => Agg::Sum { kind, arg: remap_expr(arg, m, n) },
        Agg::Min(e) => Agg::Min(remap_expr(e, m, n)),
        Agg::Max(e) => Agg::Max(remap_expr(e, m, n)),
        Agg::Avg { kind, arg } => Agg::Avg { kind, arg: remap_expr(arg, m, n) },
        Agg::DistinctAgg(inner) => Agg::DistinctAgg(Box::new(remap_agg(*inner, m, n))),
    }
}

pub open spec fn remap_aggs(aggs: Seq<Agg>, m: ColMap, n: nat) -> Seq<Agg>
    decreases aggs, 1nat,
{
    if aggs.len() == 0 { Seq::empty() } else { remap_aggs(aggs.drop_last(), m, n).push(remap_agg(aggs.last(), m, n)) }
}

pub open spec fn remap_query(q: Query, m: ColMap, n: nat) -> Query
    decreases q,
{
    match q {
        Query::Table(t) => Query::Table(t),
        Query::Filter { pred, input } => Query::Filter { pred: remap_pred(pred, m, n), input: Box::new(remap_query(*input, m, n)) },
        Query::Project { exprs, input } => Query::Project { exprs: remap_exprs(exprs, m, n), input: Box::new(remap_query(*input, m, n)) },
        Query::Product { left, right } =>
            Query::Product { left: Box::new(remap_query(*left, m, n)), right: Box::new(remap_query(*right, m, n)) },
        Query::LeftJoin { left, right, on } => Query::LeftJoin {
            left: Box::new(remap_query(*left, m, n)),
            right: Box::new(remap_query(*right, m, n)),
            on: remap_pred(on, m, n),
        },
        Query::Aggregate { aggs, input } => Query::Aggregate { aggs: remap_aggs(aggs, m, n), input: Box::new(remap_query(*input, m, n)) },
        Query::GroupBy { keys, aggs, input } => Query::GroupBy {
            keys: remap_exprs(keys, m, n),
            aggs: remap_aggs(aggs, m, n),
            input: Box::new(remap_query(*input, m, n)),
        },
        Query::Distinct(input) => Query::Distinct(Box::new(remap_query(*input, m, n))),
    }
}

/// Element view of `remap_exprs`.
pub proof fn lemma_remap_exprs_index(es: Seq<Expr>, m: ColMap, n: nat)
    ensures
        remap_exprs(es, m, n).len() == es.len(),
        forall|i: int| 0 <= i < es.len() ==> #[trigger] remap_exprs(es, m, n)[i] == remap_expr(es[i], m, n),
    decreases es.len(),
{
    if es.len() > 0 {
        lemma_remap_exprs_index(es.drop_last(), m, n);
        assert forall|i: int| 0 <= i < es.len() implies #[trigger] remap_exprs(es, m, n)[i] == remap_expr(es[i], m, n) by {
            if i < es.len() - 1 {
                assert(es.drop_last()[i] == es[i]);
            }
        }
    }
}

/// Element view of `remap_aggs`.
pub proof fn lemma_remap_aggs_index(aggs: Seq<Agg>, m: ColMap, n: nat)
    ensures
        remap_aggs(aggs, m, n).len() == aggs.len(),
        forall|j: int| 0 <= j < aggs.len() ==> #[trigger] remap_aggs(aggs, m, n)[j] == remap_agg(aggs[j], m, n),
    decreases aggs.len(),
{
    if aggs.len() > 0 {
        lemma_remap_aggs_index(aggs.drop_last(), m, n);
        assert forall|j: int| 0 <= j < aggs.len() implies #[trigger] remap_aggs(aggs, m, n)[j] == remap_agg(aggs[j], m, n) by {
            if j < aggs.len() - 1 {
                assert(aggs.drop_last()[j] == aggs[j]);
            }
        }
    }
}

/// The rewrite keeps every query's arity (and so the LEFT JOIN padding width).
pub proof fn lemma_remap_arity(schema: Schema, q: Query, m: ColMap, n: nat)
    ensures query_arity(schema, remap_query(q, m, n)) == query_arity(schema, q),
    decreases q,
{
    match q {
        Query::Table(_) => {},
        Query::Filter { pred, input } => lemma_remap_arity(schema, *input, m, n),
        Query::Project { exprs, input } => lemma_remap_exprs_index(exprs, m, n),
        Query::Product { left, right } => {
            lemma_remap_arity(schema, *left, m, n);
            lemma_remap_arity(schema, *right, m, n);
        },
        Query::LeftJoin { left, right, on } => {
            lemma_remap_arity(schema, *left, m, n);
            lemma_remap_arity(schema, *right, m, n);
        },
        Query::Aggregate { aggs, input } => lemma_remap_aggs_index(aggs, m, n),
        Query::GroupBy { keys, aggs, input } => {
            lemma_remap_exprs_index(keys, m, n);
            lemma_remap_aggs_index(aggs, m, n);
        },
        Query::Distinct(input) => lemma_remap_arity(schema, *input, m, n),
    }
}

// ------------------------------------------------------------------------------------- aggregate values

/// The rewrite keeps an aggregate's kind: equal argument values give the same value and domain.
pub proof fn lemma_agg_value_remap(a: Agg, m: ColMap, n: nat, vs: Seq<Val>)
    ensures
        agg_value(remap_agg(a, m, n), vs) == agg_value(a, vs),
        fits_agg_value(remap_agg(a, m, n), vs) == fits_agg_value(a, vs),
    decreases a,
{
    if let Agg::DistinctAgg(inner) = a {
        lemma_agg_value_remap(*inner, m, n, distinct_vals(vs));
    }
}

/// The aggregate row and its domain over any argument rows are those of the rewritten list.
pub proof fn lemma_agg_row_remap(aggs: Seq<Agg>, m: ColMap, n: nat, args: Seq<Row>)
    ensures
        agg_row(remap_aggs(aggs, m, n), args) == agg_row(aggs, args),
        fits_agg_row(remap_aggs(aggs, m, n), args) == fits_agg_row(aggs, args),
{
    let ra = remap_aggs(aggs, m, n);
    lemma_remap_aggs_index(aggs, m, n);
    let (va, vb) = (agg_value_results(ra, args), agg_value_results(aggs, args));
    let (fa, fb) = (agg_value_fs(ra, args), agg_value_fs(aggs, args));
    assert forall|j: int| #![trigger va[j]] #![trigger fa[j]] 0 <= j < aggs.len() implies va[j] == vb[j] && fa[j] == fb[j] by {
        lemma_agg_value_remap(aggs[j], m, n, column(args, j));
    }
    assert(va =~= vb);
    assert(fa =~= fb);
    lemma_agg_row(ra, args);
    lemma_agg_row(aggs, args);
}

/// The groups of a GROUP BY (values and domain) over any keys and arguments are those of the rewritten list.
pub proof fn lemma_groups_remap(aggs: Seq<Agg>, m: ColMap, n: nat, keys: Seq<Row>, args: Seq<Row>)
    ensures
        group_results(remap_aggs(aggs, m, n), keys, args) == group_results(aggs, keys, args),
        groups_fs(remap_aggs(aggs, m, n), keys, args) == groups_fs(aggs, keys, args),
{
    hide(agg_row);
    hide(fits_agg_row);
    let ra = remap_aggs(aggs, m, n);
    let ks = distinct_rows(keys);
    let (ga, gb) = (group_results(ra, keys, args), group_results(aggs, keys, args));
    let (fa, fb) = (groups_fs(ra, keys, args), groups_fs(aggs, keys, args));
    assert forall|g: int| #![trigger ga[g]] #![trigger fa[g]] 0 <= g < ks.len() implies ga[g] == gb[g] && fa[g] == fb[g] by {
        lemma_agg_row_remap(aggs, m, n, group_members(keys, args, ks[g]));
    }
    assert(ga =~= gb);
    assert(fa =~= fb);
}

// ------------------------------------------------------------------------------------- the remap theorem

/// Expressions: the rewritten expression on the physical environment has the value and domain of the canonical one.
pub proof fn lemma_expr_remap(db: Database, x: Row, y: Row, e: Expr, m: ColMap, n: nat)
    requires env_mapped(x, y, m, n), expr_reads(e, remap_reads(m, n)),
    ensures
        eval_expr(db, x, e) == eval_expr(db, y, remap_expr(e, m, n)),
        fits_expr(db, x, e) == fits_expr(db, y, remap_expr(e, m, n)),
    decreases e, 0nat,
{
    match e {
        Expr::Col(i) => {
            if i < x.len() {
                assert(x[i as int] == y[remap_col(m, n, i) as int]);
            } else {
                assert(remap_col(m, n, i) >= y.len());
            }
        },
        Expr::Lit(_) => {},
        Expr::Neg { kind, arg } => lemma_expr_remap(db, x, y, *arg, m, n),
        Expr::Arith { op, kind, a, b } => {
            lemma_expr_remap(db, x, y, *a, m, n);
            lemma_expr_remap(db, x, y, *b, m, n);
        },
        Expr::Cast { cast, arg } => lemma_expr_remap(db, x, y, *arg, m, n),
        Expr::AddInterval { arg, months, days, micros } => lemma_expr_remap(db, x, y, *arg, m, n),
        Expr::Call { f, args } => lemma_exprs_remap(db, x, y, args, m, n),
        Expr::If { cond, then_e, else_e } => {
            lemma_pred_remap(db, x, y, *cond, m, n);
            lemma_expr_remap(db, x, y, *then_e, m, n);
            lemma_expr_remap(db, x, y, *else_e, m, n);
        },
        Expr::Subquery(q) => lemma_query_remap(db, x, y, *q, m, n),
    }
}

/// Expression lists (SELECT lists, GROUP BY keys, function arguments).
pub proof fn lemma_exprs_remap(db: Database, x: Row, y: Row, es: Seq<Expr>, m: ColMap, n: nat)
    requires env_mapped(x, y, m, n), exprs_reads(es, remap_reads(m, n)),
    ensures
        eval_exprs(db, x, es) == eval_exprs(db, y, remap_exprs(es, m, n)),
        fits_exprs(db, x, es) == fits_exprs(db, y, remap_exprs(es, m, n)),
    decreases es, 1nat,
{
    let res = remap_exprs(es, m, n);
    lemma_remap_exprs_index(es, m, n);
    let (ra, rb) = (expr_results(db, x, es), expr_results(db, y, res));
    assert forall|i: int| 0 <= i < es.len() implies #[trigger] ra[i] == rb[i] by {
        lemma_exprs_reads_index(es, remap_reads(m, n), i);
        lemma_expr_remap(db, x, y, es[i], m, n);
    }
    assert(ra =~= rb);
    if es.len() > 0 {
        assert(res.drop_last() =~= remap_exprs(es.drop_last(), m, n));
        assert(res.last() == remap_expr(es.last(), m, n));
        lemma_exprs_remap(db, x, y, es.drop_last(), m, n);
        lemma_expr_remap(db, x, y, es.last(), m, n);
    }
}

/// Conditions.
pub proof fn lemma_pred_remap(db: Database, x: Row, y: Row, p: Pred, m: ColMap, n: nat)
    requires env_mapped(x, y, m, n), pred_reads(p, remap_reads(m, n)),
    ensures
        eval_pred(db, x, p) == eval_pred(db, y, remap_pred(p, m, n)),
        fits_pred(db, x, p) == fits_pred(db, y, remap_pred(p, m, n)),
    decreases p, 0nat,
{
    match p {
        Pred::Cmp { op, a, b } => {
            lemma_expr_remap(db, x, y, a, m, n);
            lemma_expr_remap(db, x, y, b, m, n);
        },
        Pred::And(a, b) => {
            lemma_pred_remap(db, x, y, *a, m, n);
            lemma_pred_remap(db, x, y, *b, m, n);
        },
        Pred::Or(a, b) => {
            lemma_pred_remap(db, x, y, *a, m, n);
            lemma_pred_remap(db, x, y, *b, m, n);
        },
        Pred::Not(a) => lemma_pred_remap(db, x, y, *a, m, n),
        Pred::IsNull(e) => lemma_expr_remap(db, x, y, e, m, n),
        Pred::OfBool(e) => lemma_expr_remap(db, x, y, e, m, n),
        Pred::Exists(q) => lemma_query_remap(db, x, y, *q, m, n),
        Pred::AnyCmp { op, e, q } => {
            lemma_expr_remap(db, x, y, e, m, n);
            lemma_query_remap(db, x, y, *q, m, n);
        },
    }
}

/// One aggregate's argument.
pub proof fn lemma_agg_remap(db: Database, x: Row, y: Row, a: Agg, m: ColMap, n: nat)
    requires env_mapped(x, y, m, n), agg_reads(a, remap_reads(m, n)),
    ensures
        agg_arg(db, x, a) == agg_arg(db, y, remap_agg(a, m, n)),
        fits_agg_arg(db, x, a) == fits_agg_arg(db, y, remap_agg(a, m, n)),
    decreases a, 0nat,
{
    match a {
        Agg::CountStar => {},
        Agg::Count(e) => lemma_expr_remap(db, x, y, e, m, n),
        Agg::Sum { kind, arg } => lemma_expr_remap(db, x, y, arg, m, n),
        Agg::Min(e) => lemma_expr_remap(db, x, y, e, m, n),
        Agg::Max(e) => lemma_expr_remap(db, x, y, e, m, n),
        Agg::Avg { kind, arg } => lemma_expr_remap(db, x, y, arg, m, n),
        Agg::DistinctAgg(inner) => lemma_agg_remap(db, x, y, *inner, m, n),
    }
}

/// The arguments of a list of aggregates.
pub proof fn lemma_aggs_remap(db: Database, x: Row, y: Row, aggs: Seq<Agg>, m: ColMap, n: nat)
    requires env_mapped(x, y, m, n), aggs_reads(aggs, remap_reads(m, n)),
    ensures
        agg_args(db, x, aggs) == agg_args(db, y, remap_aggs(aggs, m, n)),
        fits_agg_args(db, x, aggs) == fits_agg_args(db, y, remap_aggs(aggs, m, n)),
    decreases aggs, 2nat,
{
    lemma_agg_arg_results_remap(db, x, y, aggs, m, n);
    lemma_agg_args(db, x, aggs);
    lemma_agg_args(db, y, remap_aggs(aggs, m, n));
}

/// The per-aggregate argument outcomes and domains of one row, rewritten.
proof fn lemma_agg_arg_results_remap(db: Database, x: Row, y: Row, aggs: Seq<Agg>, m: ColMap, n: nat)
    requires env_mapped(x, y, m, n), aggs_reads(aggs, remap_reads(m, n)),
    ensures
        agg_arg_results(db, x, aggs) == agg_arg_results(db, y, remap_aggs(aggs, m, n)),
        agg_arg_fs(db, x, aggs) == agg_arg_fs(db, y, remap_aggs(aggs, m, n)),
    decreases aggs, 1nat,
{
    hide(agg_arg_results);
    hide(agg_arg_fs);
    hide(agg_arg);
    hide(fits_agg_arg);
    hide(remap_aggs);
    hide(remap_agg);
    let ra = remap_aggs(aggs, m, n);
    lemma_remap_aggs_index(aggs, m, n);
    lemma_agg_arg_results_index(db, x, aggs);
    lemma_agg_arg_results_index(db, y, ra);
    lemma_agg_arg_fs_index(db, x, aggs);
    lemma_agg_arg_fs_index(db, y, ra);
    let (sa, sb) = (agg_arg_results(db, x, aggs), agg_arg_results(db, y, ra));
    let (fa, fb) = (agg_arg_fs(db, x, aggs), agg_arg_fs(db, y, ra));
    assert forall|j: int| #![trigger sa[j]] #![trigger fa[j]] 0 <= j < aggs.len() implies sa[j] == sb[j] && fa[j] == fb[j] by {
        lemma_aggs_reads_index(aggs, remap_reads(m, n), j);
        lemma_agg_remap(db, x, y, aggs[j], m, n);
    }
    assert(sa =~= sb);
    assert(fa =~= fb);
}

/// L5 remap. A query reading only mapped positions has, rewritten and on the physical environment, the canonical
/// query's outcome and capacity domain.
pub proof fn lemma_query_remap(db: Database, x: Row, y: Row, q: Query, m: ColMap, n: nat)
    requires env_mapped(x, y, m, n), query_reads(q, remap_reads(m, n)),
    ensures
        eval_query(db, x, q) == eval_query(db, y, remap_query(q, m, n)),
        fits_query(db, x, q) == fits_query(db, y, remap_query(q, m, n)),
    decreases q, 2nat,
{
    hide(eval_query);
    hide(fits_query);
    match q {
        Query::Table(_) => lemma_table_remap(db, x, y, q, m, n),
        Query::Product { .. } => lemma_product_remap(db, x, y, q, m, n),
        Query::Distinct(_) => lemma_distinct_remap(db, x, y, q, m, n),
        Query::Filter { .. } => lemma_filter_remap(db, x, y, q, m, n),
        Query::Project { .. } => lemma_project_remap(db, x, y, q, m, n),
        Query::LeftJoin { .. } => lemma_left_join_remap(db, x, y, q, m, n),
        Query::Aggregate { .. } => lemma_aggregate_remap(db, x, y, q, m, n),
        Query::GroupBy { .. } => lemma_group_by_remap(db, x, y, q, m, n),
    }
}

proof fn lemma_table_remap(db: Database, x: Row, y: Row, q: Query, m: ColMap, n: nat)
    requires q is Table,
    ensures
        eval_query(db, x, q) == eval_query(db, y, remap_query(q, m, n)),
        fits_query(db, x, q) == fits_query(db, y, remap_query(q, m, n)),
    decreases q, 1nat,
{
}

proof fn lemma_product_remap(db: Database, x: Row, y: Row, q: Query, m: ColMap, n: nat)
    requires q is Product, env_mapped(x, y, m, n), query_reads(q, remap_reads(m, n)),
    ensures
        eval_query(db, x, q) == eval_query(db, y, remap_query(q, m, n)),
        fits_query(db, x, q) == fits_query(db, y, remap_query(q, m, n)),
    decreases q, 1nat,
{
    if let Query::Product { left, right } = q {
        lemma_query_remap(db, x, y, *left, m, n);
        lemma_query_remap(db, x, y, *right, m, n);
    }
}

proof fn lemma_distinct_remap(db: Database, x: Row, y: Row, q: Query, m: ColMap, n: nat)
    requires q is Distinct, env_mapped(x, y, m, n), query_reads(q, remap_reads(m, n)),
    ensures
        eval_query(db, x, q) == eval_query(db, y, remap_query(q, m, n)),
        fits_query(db, x, q) == fits_query(db, y, remap_query(q, m, n)),
    decreases q, 1nat,
{
    if let Query::Distinct(input) = q {
        lemma_query_remap(db, x, y, *input, m, n);
    }
}

proof fn lemma_filter_remap(db: Database, x: Row, y: Row, q: Query, m: ColMap, n: nat)
    requires q is Filter, env_mapped(x, y, m, n), query_reads(q, remap_reads(m, n)),
    ensures
        eval_query(db, x, q) == eval_query(db, y, remap_query(q, m, n)),
        fits_query(db, x, q) == fits_query(db, y, remap_query(q, m, n)),
    decreases q, 1nat,
{
    hide(eval_query);
    hide(fits_query);
    hide(eval_pred);
    hide(fits_pred);
    if let Query::Filter { pred, input } = q {
        let (rp, ri) = (remap_pred(pred, m, n), Box::new(remap_query(*input, m, n)));
        assert(remap_query(q, m, n) == Query::Filter { pred: rp, input: ri });
        lemma_query_remap(db, x, y, *input, m, n);
        lemma_eval_filter(db, x, pred, input);
        lemma_eval_filter(db, y, rp, ri);
        lemma_fits_filter(db, x, pred, input);
        lemma_fits_filter(db, y, rp, ri);
        if let Ok(rows) = eval_query(db, x, *input) {
            assert forall|i: int|
                #![trigger eval_pred(db, x + rows[i], pred)] #![trigger fits_pred(db, x + rows[i], pred)]
                0 <= i < rows.len() implies
                eval_pred(db, x + rows[i], pred) == eval_pred(db, y + rows[i], rp)
                && fits_pred(db, x + rows[i], pred) == fits_pred(db, y + rows[i], rp) by {
                lemma_env_mapped_push(x, y, rows[i], m, n);
                lemma_pred_remap(db, x + rows[i], y + rows[i], pred, m, n);
            }
            let (ra, rb) = (filter_results(db, x, rows, pred), filter_results(db, y, rows, rp));
            assert(ra =~= rb);
            assert(filter_fits(db, x, rows, pred) == filter_fits(db, y, rows, rp)) by {
                if filter_fits(db, x, rows, pred) {
                    assert forall|i: int| 0 <= i < rows.len() && ok_before(rb, i)
                        implies #[trigger] fits_pred(db, y + rows[i], rp) by {
                        assert(fits_pred(db, x + rows[i], pred));
                    }
                }
                if filter_fits(db, y, rows, rp) {
                    assert forall|i: int| 0 <= i < rows.len() && ok_before(ra, i)
                        implies #[trigger] fits_pred(db, x + rows[i], pred) by {
                        assert(fits_pred(db, y + rows[i], rp));
                    }
                }
            }
        }
    }
}

proof fn lemma_project_remap(db: Database, x: Row, y: Row, q: Query, m: ColMap, n: nat)
    requires q is Project, env_mapped(x, y, m, n), query_reads(q, remap_reads(m, n)),
    ensures
        eval_query(db, x, q) == eval_query(db, y, remap_query(q, m, n)),
        fits_query(db, x, q) == fits_query(db, y, remap_query(q, m, n)),
    decreases q, 1nat,
{
    hide(eval_query);
    hide(fits_query);
    hide(eval_exprs);
    hide(fits_exprs);
    if let Query::Project { exprs, input } = q {
        let (re, ri) = (remap_exprs(exprs, m, n), Box::new(remap_query(*input, m, n)));
        assert(remap_query(q, m, n) == Query::Project { exprs: re, input: ri });
        lemma_query_remap(db, x, y, *input, m, n);
        lemma_eval_project(db, x, exprs, input);
        lemma_eval_project(db, y, re, ri);
        lemma_fits_project_unfold(db, x, exprs, input);
        lemma_fits_project_unfold(db, y, re, ri);
        if let Ok(rows) = eval_query(db, x, *input) {
            assert forall|i: int|
                #![trigger eval_exprs(db, x + rows[i], exprs)] #![trigger fits_exprs(db, x + rows[i], exprs)]
                0 <= i < rows.len() implies
                eval_exprs(db, x + rows[i], exprs) == eval_exprs(db, y + rows[i], re)
                && fits_exprs(db, x + rows[i], exprs) == fits_exprs(db, y + rows[i], re) by {
                lemma_env_mapped_push(x, y, rows[i], m, n);
                lemma_exprs_remap(db, x + rows[i], y + rows[i], exprs, m, n);
            }
            assert(project_results(db, x, rows, exprs) =~= project_results(db, y, rows, re));
            lemma_project_fs_index(db, x, rows, exprs);
            lemma_project_fs_index(db, y, rows, re);
            assert(project_fs(db, x, rows, exprs) =~= project_fs(db, y, rows, re));
        }
    }
}

proof fn lemma_left_join_remap(db: Database, x: Row, y: Row, q: Query, m: ColMap, n: nat)
    requires q is LeftJoin, env_mapped(x, y, m, n), query_reads(q, remap_reads(m, n)),
    ensures
        eval_query(db, x, q) == eval_query(db, y, remap_query(q, m, n)),
        fits_query(db, x, q) == fits_query(db, y, remap_query(q, m, n)),
    decreases q, 1nat,
{
    hide(eval_query);
    hide(fits_query);
    hide(eval_pred);
    hide(fits_pred);
    if let Query::LeftJoin { left, right, on } = q {
        let (rl, rr, ro) = (Box::new(remap_query(*left, m, n)), Box::new(remap_query(*right, m, n)), remap_pred(on, m, n));
        assert(remap_query(q, m, n) == Query::LeftJoin { left: rl, right: rr, on: ro });
        lemma_query_remap(db, x, y, *left, m, n);
        lemma_query_remap(db, x, y, *right, m, n);
        lemma_remap_arity(db.schema, *right, m, n);
        lemma_eval_left_join(db, x, left, right, on);
        lemma_eval_left_join(db, y, rl, rr, ro);
        lemma_fits_left_join(db, x, left, right, on);
        lemma_fits_left_join(db, y, rl, rr, ro);
        if let (Ok(l), Ok(r)) = (eval_query(db, x, *left), eval_query(db, x, *right)) {
            assert forall|i: int|
                #![trigger join_results(db, x + l[i], r, on)] #![trigger join_row_fits(db, x + l[i], r, on)]
                0 <= i < l.len() implies
                join_results(db, x + l[i], r, on) == join_results(db, y + l[i], r, ro)
                && join_row_fits(db, x + l[i], r, on) == join_row_fits(db, y + l[i], r, ro) by {
                lemma_env_mapped_push(x, y, l[i], m, n);
                lemma_join_row_remap(db, x + l[i], y + l[i], r, on, m, n);
            }
            let (la, lb) = (left_join_results(db, x, l, r, on), left_join_results(db, y, l, r, ro));
            lemma_collect_pointwise::<Truth>();
            assert forall|i: int| 0 <= i < l.len() implies #[trigger] la[i] == lb[i] by {
                let inner_a = Seq::new(r.len(), |j: int| eval_pred(db, x + l[i] + r[j], on));
                let inner_b = Seq::new(r.len(), |j: int| eval_pred(db, y + l[i] + r[j], ro));
                assert(inner_a =~= join_results(db, x + l[i], r, on));
                assert(inner_b =~= join_results(db, y + l[i], r, ro));
            }
            assert(la =~= lb);
            assert(left_join_fits(db, x, l, r, on) == left_join_fits(db, y, l, r, ro)) by {
                if left_join_fits(db, x, l, r, on) {
                    assert forall|i: int| 0 <= i < l.len() && ok_before(lb, i)
                        implies #[trigger] join_row_fits(db, y + l[i], r, ro) by {
                        assert(join_row_fits(db, x + l[i], r, on));
                    }
                }
                if left_join_fits(db, y, l, r, ro) {
                    assert forall|i: int| 0 <= i < l.len() && ok_before(la, i)
                        implies #[trigger] join_row_fits(db, x + l[i], r, on) by {
                        assert(join_row_fits(db, y + l[i], r, ro));
                    }
                }
            }
        }
    }
}

/// One left row of a LEFT JOIN: the ON conditions against every right row agree, and so do their domains.
proof fn lemma_join_row_remap(db: Database, x: Row, y: Row, rr: Seq<Row>, on: Pred, m: ColMap, n: nat)
    requires env_mapped(x, y, m, n), pred_reads(on, remap_reads(m, n)),
    ensures
        join_results(db, x, rr, on) == join_results(db, y, rr, remap_pred(on, m, n)),
        join_row_fits(db, x, rr, on) == join_row_fits(db, y, rr, remap_pred(on, m, n)),
    decreases on, 1nat,
{
    hide(eval_pred);
    hide(fits_pred);
    let ro = remap_pred(on, m, n);
    assert forall|j: int|
        #![trigger eval_pred(db, x + rr[j], on)] #![trigger fits_pred(db, x + rr[j], on)]
        0 <= j < rr.len() implies
        eval_pred(db, x + rr[j], on) == eval_pred(db, y + rr[j], ro)
        && fits_pred(db, x + rr[j], on) == fits_pred(db, y + rr[j], ro) by {
        lemma_env_mapped_push(x, y, rr[j], m, n);
        lemma_pred_remap(db, x + rr[j], y + rr[j], on, m, n);
    }
    let (ja, jb) = (join_results(db, x, rr, on), join_results(db, y, rr, ro));
    assert(ja =~= jb);
    if join_row_fits(db, x, rr, on) {
        assert forall|j: int| 0 <= j < rr.len() && ok_before(jb, j) implies #[trigger] fits_pred(db, y + rr[j], ro) by {
            assert(fits_pred(db, x + rr[j], on));
        }
    }
    if join_row_fits(db, y, rr, ro) {
        assert forall|j: int| 0 <= j < rr.len() && ok_before(ja, j) implies #[trigger] fits_pred(db, x + rr[j], on) by {
            assert(fits_pred(db, y + rr[j], ro));
        }
    }
}

proof fn lemma_aggregate_remap(db: Database, x: Row, y: Row, q: Query, m: ColMap, n: nat)
    requires q is Aggregate, env_mapped(x, y, m, n), query_reads(q, remap_reads(m, n)),
    ensures
        eval_query(db, x, q) == eval_query(db, y, remap_query(q, m, n)),
        fits_query(db, x, q) == fits_query(db, y, remap_query(q, m, n)),
    decreases q, 1nat,
{
    hide(eval_query);
    hide(fits_query);
    hide(agg_args);
    hide(fits_agg_args);
    if let Query::Aggregate { aggs, input } = q {
        let (ra, ri) = (remap_aggs(aggs, m, n), Box::new(remap_query(*input, m, n)));
        assert(remap_query(q, m, n) == Query::Aggregate { aggs: ra, input: ri });
        lemma_query_remap(db, x, y, *input, m, n);
        lemma_eval_aggregate(db, x, aggs, input);
        lemma_eval_aggregate(db, y, ra, ri);
        lemma_fits_aggregate_unfold(db, x, aggs, input);
        lemma_fits_aggregate_unfold(db, y, ra, ri);
        if let Ok(rows) = eval_query(db, x, *input) {
            assert forall|i: int|
                #![trigger agg_args(db, x + rows[i], aggs)] #![trigger fits_agg_args(db, x + rows[i], aggs)]
                0 <= i < rows.len() implies
                agg_args(db, x + rows[i], aggs) == agg_args(db, y + rows[i], ra)
                && fits_agg_args(db, x + rows[i], aggs) == fits_agg_args(db, y + rows[i], ra) by {
                lemma_env_mapped_push(x, y, rows[i], m, n);
                lemma_aggs_remap(db, x + rows[i], y + rows[i], aggs, m, n);
            }
            assert(agg_args_results(db, x, rows, aggs) =~= agg_args_results(db, y, rows, ra));
            lemma_agg_args_fs_index(db, x, rows, aggs);
            lemma_agg_args_fs_index(db, y, rows, ra);
            assert(agg_args_fs(db, x, rows, aggs) =~= agg_args_fs(db, y, rows, ra));
            if let Ok(args) = collect(agg_args_results(db, x, rows, aggs)) {
                lemma_agg_row_remap(aggs, m, n, args);
            }
        }
    }
}

proof fn lemma_group_by_remap(db: Database, x: Row, y: Row, q: Query, m: ColMap, n: nat)
    requires q is GroupBy, env_mapped(x, y, m, n), query_reads(q, remap_reads(m, n)),
    ensures
        eval_query(db, x, q) == eval_query(db, y, remap_query(q, m, n)),
        fits_query(db, x, q) == fits_query(db, y, remap_query(q, m, n)),
    decreases q, 1nat,
{
    hide(eval_query);
    hide(fits_query);
    hide(eval_exprs);
    hide(fits_exprs);
    hide(agg_args);
    hide(fits_agg_args);
    if let Query::GroupBy { keys, aggs, input } = q {
        let (rk, ra, ri) = (remap_exprs(keys, m, n), remap_aggs(aggs, m, n), Box::new(remap_query(*input, m, n)));
        assert(remap_query(q, m, n) == Query::GroupBy { keys: rk, aggs: ra, input: ri });
        lemma_query_remap(db, x, y, *input, m, n);
        lemma_eval_group_by(db, x, keys, aggs, input);
        lemma_eval_group_by(db, y, rk, ra, ri);
        lemma_fits_group_by(db, x, keys, aggs, input);
        lemma_fits_group_by(db, y, rk, ra, ri);
        if let Ok(rows) = eval_query(db, x, *input) {
            assert forall|i: int|
                #![trigger eval_exprs(db, x + rows[i], keys)] #![trigger fits_exprs(db, x + rows[i], keys)]
                #![trigger agg_args(db, x + rows[i], aggs)] #![trigger fits_agg_args(db, x + rows[i], aggs)]
                0 <= i < rows.len() implies
                eval_exprs(db, x + rows[i], keys) == eval_exprs(db, y + rows[i], rk)
                && fits_exprs(db, x + rows[i], keys) == fits_exprs(db, y + rows[i], rk)
                && agg_args(db, x + rows[i], aggs) == agg_args(db, y + rows[i], ra)
                && fits_agg_args(db, x + rows[i], aggs) == fits_agg_args(db, y + rows[i], ra) by {
                lemma_env_mapped_push(x, y, rows[i], m, n);
                lemma_exprs_remap(db, x + rows[i], y + rows[i], keys, m, n);
                lemma_aggs_remap(db, x + rows[i], y + rows[i], aggs, m, n);
            }
            assert(group_input_results(db, x, rows, keys, aggs) =~= group_input_results(db, y, rows, rk, ra));
            assert(group_input_fs(db, x, rows, keys, aggs) =~= group_input_fs(db, y, rows, rk, ra));
            if let Ok(prepared) = collect(group_input_results(db, x, rows, keys, aggs)) {
                lemma_groups_remap(aggs, m, n, prepared.map_values(|p: (Row, Row)| p.0), prepared.map_values(|p: (Row, Row)| p.1));
            }
        }
    }
}

} // verus!
