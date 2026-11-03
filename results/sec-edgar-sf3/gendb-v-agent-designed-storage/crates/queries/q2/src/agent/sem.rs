//! The SQL meaning of the statement as a count. For a database whose `num` rows (table 1) and `sub` rows (table 0)
//! have the stored shapes (`shapes_ok`), the body evaluates without error and the multiplicity of every output row
//! `t` is `body_count`: the number of pairs (num row `n`, sub row `s`) with `n.adsh = s.adsh`, `s.fy = $2`,
//! `n.uom = $1`, `n.value` the largest value of its `(adsh, tag)` group among the rows of unit `$1`, and
//! `(s.name, n.tag, n.value) = t`. The proof follows the plan tree: the num x sub product filtered on adsh, the
//! GROUP BY (one row per `(adsh, tag)` key of unit `$1`, with the group's MAX), their product, the two filters and
//! the projection; then the count is a triple sum over num, sub and the groups, where exactly one group matches.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::numeric::*;
use crate::spec::ast::*;
use crate::spec::int::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::equality::*;
use crate::spec::aggs::minmax::*;
use crate::spec::order::denote_body;
use crate::link::join::*;
use crate::link::expr::*;
use crate::bridge::collect::lemma_collect_all;
use crate::bridge::equality::*;
use crate::bridge::relation::{is_concat, lemma_product_rows_elems};
use crate::query::{query_spec_at, param_domain};
use crate::agent::common::rel::*;

verus! {

broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms};

// ------------------------------------------------------------------ the plan tree

pub open spec fn p29() -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) }
}

pub open spec fn q_ns() -> Query {
    Query::Product { left: Box::new(Query::Table(1)), right: Box::new(Query::Table(0)) }
}

pub open spec fn q_f29() -> Query {
    Query::Filter { pred: p29(), input: Box::new(q_ns()) }
}

pub open spec fn p45(ps: Seq<Literal>) -> Pred {
    Pred::And(
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(5), b: Expr::Lit(ps[0]) }),
        Box::new(Pred::Not(Box::new(Pred::IsNull(Expr::Col(7))))),
    )
}

pub open spec fn q_f45(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: p45(ps), input: Box::new(Query::Table(1)) }
}

pub open spec fn grp_keys() -> Seq<Expr> {
    seq![Expr::Col(0), Expr::Col(1)]
}

pub open spec fn grp_aggs() -> Seq<Agg> {
    seq![Agg::Max(Expr::Col(7))]
}

pub open spec fn q_grp(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: grp_keys(), aggs: grp_aggs(), input: Box::new(q_f45(ps)) }
}

pub open spec fn q_prod(ps: Seq<Literal>) -> Query {
    Query::Product { left: Box::new(q_f29()), right: Box::new(q_grp(ps)) }
}

pub open spec fn p26() -> Pred {
    Pred::And(
        Box::new(Pred::And(
            Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(29) }),
            Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(1), b: Expr::Col(30) }),
        )),
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(7), b: Expr::Col(31) }),
    )
}

pub open spec fn q_f26(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: p26(), input: Box::new(q_prod(ps)) }
}

pub open spec fn p15(ps: Seq<Literal>) -> Pred {
    Pred::And(
        Box::new(Pred::And(
            Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(5), b: Expr::Lit(ps[0]) }),
            Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(19), b: Expr::Lit(ps[1]) }),
        )),
        Box::new(Pred::Not(Box::new(Pred::IsNull(Expr::Col(7))))),
    )
}

pub open spec fn q_f15(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: p15(ps), input: Box::new(q_f26(ps)) }
}

pub open spec fn out_exprs() -> Seq<Expr> {
    seq![Expr::Col(11), Expr::Col(1), Expr::Col(7)]
}

pub open spec fn q_body(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: out_exprs(), input: Box::new(q_f15(ps)) }
}

/// The statement's body is the plan tree above.
pub proof fn lemma_body_tree(ps: Seq<Literal>)
    ensures query_spec_at(ps).body == q_body(ps),
{
}

// ------------------------------------------------------------------ parameters and row shapes

pub open spec fn uom_of(ps: Seq<Literal>) -> Seq<u8> {
    match ps[0] { Literal::Text(b) => b, _ => Seq::empty() }
}

pub open spec fn fy_of(ps: Seq<Literal>) -> int {
    match ps[1] { Literal::Int { v, .. } => v, _ => 0 }
}

/// A `num` row: 9 values; adsh, tag, uom texts; value a numeric at scale 4.
pub open spec fn num_shape(n: Row) -> bool {
    &&& n.len() == 9
    &&& n[0] is Text && n[1] is Text && n[5] is Text
    &&& n[7] is Num && n[7]->Num_scale == 4
}

/// A `sub` row: 20 values; adsh, name texts; fy NULL or an integer.
pub open spec fn sub_shape(s: Row) -> bool {
    &&& s.len() == 20
    &&& s[0] is Text && s[2] is Text
    &&& (s[10] is Null || s[10] is Int)
}

pub open spec fn shapes_ok(db: Database) -> bool {
    &&& db.tables.len() >= 2
    &&& forall|i: int| 0 <= i < db.tables[1].len() ==> num_shape(#[trigger] db.tables[1][i])
    &&& forall|i: int| 0 <= i < db.tables[0].len() ==> sub_shape(#[trigger] db.tables[0][i])
}

// ------------------------------------------------------------------ the normal form

/// `m` is a row of unit `u` in group `(a, t)`.
pub open spec fn in_grp(m: Row, u: Seq<u8>, a: Val, t: Val) -> bool {
    m[5] == Val::Text(u) && m[0] == a && m[1] == t
}

/// `n`'s value is the largest of its group among the rows of unit `u`.
pub open spec fn is_gmax(nums: Seq<Row>, u: Seq<u8>, n: Row) -> bool {
    forall|k: int| 0 <= k < nums.len() && in_grp(#[trigger] nums[k], u, n[0], n[1]) ==> ival(nums[k][7]) <= ival(n[7])
}

/// `n` is of unit `u` and holds its group's MAX.
pub open spec fn qual(nums: Seq<Row>, u: Seq<u8>, n: Row) -> bool {
    n[5] == Val::Text(u) && is_gmax(nums, u, n)
}

pub open spec fn out_row(n: Row, s: Row) -> Row {
    seq![s[2], n[1], n[7]]
}

/// The pair `(n, s)` gives output row `t`.
pub open spec fn pair_hit(nums: Seq<Row>, u: Seq<u8>, y: int, t: Row, n: Row, s: Row) -> int {
    if qual(nums, u, n) && n[0] == s[0] && s[10] == Val::Int(y) && out_row(n, s) == t { 1 } else { 0 }
}

pub open spec fn sub_hits(nums: Seq<Row>, subs: Seq<Row>, u: Seq<u8>, y: int, t: Row) -> spec_fn(Row) -> int {
    |n: Row| sum_of(subs, |s: Row| pair_hit(nums, u, y, t, n, s))
}

/// Multiplicity of `t` in the body.
pub open spec fn body_count(nums: Seq<Row>, subs: Seq<Row>, u: Seq<u8>, y: int, t: Row) -> int {
    sum_of(nums, sub_hits(nums, subs, u, y, t))
}

// ------------------------------------------------------------------ filters

/// SQL filter with three-valued truths: the rows whose truth is `True` are `keep` of a condition that holds exactly
/// when the truth is `True`.
pub proof fn lemma_keep_true_iff(rows: Seq<Row>, truths: Seq<Truth>, f: spec_fn(Row) -> bool)
    requires
        truths.len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] truths[i] is True) == f(rows[i]),
    ensures keep_true(rows, truths) == keep(rows, f),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let (ri, ti) = (rows.drop_last(), truths.drop_last());
        assert forall|i: int| 0 <= i < ri.len() implies (#[trigger] ti[i] is True) == f(ri[i]) by {
            assert(ti[i] == truths[i] && ri[i] == rows[i]);
        }
        lemma_keep_true_iff(ri, ti, f);
        assert((truths[rows.len() - 1] is True) == f(rows[rows.len() - 1]));
    }
}

/// `lemma_eval_filter` for a condition that may be `Unknown`: it evaluates without error on every row, and to `True`
/// exactly when `h` holds.
pub proof fn lemma_eval_filter3(db: Database, src: Query, rows: Seq<Row>, f: spec_fn(Row) -> bool, pred: Pred,
    h: spec_fn(Row) -> bool, fh: spec_fn(Row) -> bool)
    requires
        eval_query(db, Seq::empty(), src) == Ok::<Relation, SqlError>(keep(rows, f)),
        forall|i: int| 0 <= i < rows.len() && f(#[trigger] rows[i]) ==>
            eval_pred(db, rows[i], pred) is Ok && (eval_pred(db, rows[i], pred)->Ok_0 is True) == h(rows[i]),
        forall|i: int| 0 <= i < rows.len() ==> fh(#[trigger] rows[i]) == (f(rows[i]) && h(rows[i])),
    ensures
        eval_query(db, Seq::empty(), Query::Filter { pred, input: Box::new(src) }) == Ok::<Relation, SqlError>(keep(rows, fh)),
{
    let kept = keep(rows, f);
    let ctx = Seq::<Val>::empty();
    lemma_keep_members(rows, f);
    let truths = Seq::new(kept.len(), |i: int| eval_pred(db, kept[i], pred)->Ok_0);
    let prs = Seq::new(kept.len(), |i: int| eval_pred(db, ctx + kept[i], pred));
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        assert(ctx + kept[i] =~= kept[i]);
        assert(rows.contains(kept[i]) && f(kept[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
        assert(f(rows[m]));
    }
    lemma_collect_all(prs, truths);
    crate::bridge::collect::lemma_collect_pointwise::<Truth>();
    assert(collect(Seq::new(kept.len(), |i: int| eval_pred(db, ctx + kept[i], pred))) == Ok::<Seq<Truth>, SqlError>(truths));
    assert forall|i: int| 0 <= i < kept.len() implies (#[trigger] truths[i] is True) == h(kept[i]) by {
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
        assert(f(rows[m]));
    }
    lemma_keep_true_iff(kept, truths, h);
    lemma_keep_keep(rows, f, h);
    lemma_keep_ext(rows, |x: Row| f(x) && h(x), fh);
}

pub open spec fn always() -> spec_fn(Row) -> bool {
    |x: Row| true
}

/// A base table is its rows.
pub proof fn lemma_table(db: Database, t: nat)
    requires t < db.tables.len(),
    ensures eval_query(db, Seq::empty(), Query::Table(t)) == Ok::<Relation, SqlError>(keep(db.tables[t as int], always())),
{
    lemma_eval_table(db, t, always());
}

/// Every row of `num x sub` is a num row followed by a sub row.
pub open spec fn ns_shape(x: Row) -> bool {
    exists|n: Row, s: Row| num_shape(n) && sub_shape(s) && x == n + s
}

pub open spec fn f29() -> spec_fn(Row) -> bool {
    |x: Row| x[0] == x[9]
}

/// The product `num x sub` filtered on `n.adsh = s.adsh`.
pub proof fn lemma_eval_f29(db: Database)
    requires shapes_ok(db),
    ensures
        eval_query(db, Seq::empty(), q_f29()) == Ok::<Relation, SqlError>(keep(product_rows(db.tables[1], db.tables[0]), f29())),
        forall|k: int| 0 <= k < product_rows(db.tables[1], db.tables[0]).len()
            ==> ns_shape(#[trigger] product_rows(db.tables[1], db.tables[0])[k]),
{
    let (nums, subs) = (db.tables[1], db.tables[0]);
    let ns = product_rows(nums, subs);
    lemma_table(db, 1);
    lemma_table(db, 0);
    lemma_keep_all(nums, always());
    lemma_keep_all(subs, always());
    lemma_product_rows_elems(nums, subs);
    assert forall|k: int| 0 <= k < ns.len() implies ns_shape(#[trigger] ns[k]) by {
        assert(is_concat(ns[k], nums, subs));
        let (i, j) = choose|i: int, j: int| 0 <= i < nums.len() && 0 <= j < subs.len() && ns[k] == #[trigger] nums[i] + #[trigger] subs[j];
        assert(num_shape(nums[i]) && sub_shape(subs[j]));
    }
    assert(eval_query(db, Seq::empty(), q_ns()) == Ok::<Relation, SqlError>(ns));
    lemma_keep_all(ns, always());
    assert forall|k: int| 0 <= k < ns.len() && always()(#[trigger] ns[k]) implies
        eval_pred(db, ns[k], p29()) == Ok::<Truth, SqlError>(truth_of(f29()(ns[k]))) by {
        let x = ns[k];
        assert(ns_shape(x));
        let (n, s) = choose|n: Row, s: Row| num_shape(n) && sub_shape(s) && x == n + s;
        assert(x[0] == n[0] && x[9] == s[0]);
        lemma_expr_col(db, x, 0);
        lemma_expr_col(db, x, 9);
        lemma_pred_text_cmp(db, x, CmpOp::Eq, Expr::Col(0), Expr::Col(9), tval(x[0]), tval(x[9]));
    }
    lemma_eval_filter(db, q_ns(), ns, always(), p29(), f29(), f29());
}

pub open spec fn fu(u: Seq<u8>) -> spec_fn(Row) -> bool {
    |n: Row| n[5] == Val::Text(u)
}

/// The rows of unit `$1` (`value` is never NULL).
pub proof fn lemma_eval_f45(db: Database, ps: Seq<Literal>)
    requires shapes_ok(db), param_domain(ps),
    ensures eval_query(db, Seq::empty(), q_f45(ps)) == Ok::<Relation, SqlError>(keep(db.tables[1], fu(uom_of(ps)))),
{
    let nums = db.tables[1];
    let u = uom_of(ps);
    lemma_table(db, 1);
    assert(ps[0] == Literal::Text(u));
    assert forall|i: int| 0 <= i < nums.len() && always()(#[trigger] nums[i]) implies
        eval_pred(db, nums[i], p45(ps)) == Ok::<Truth, SqlError>(truth_of(fu(u)(nums[i]))) by {
        let n = nums[i];
        assert(num_shape(n));
        lemma_expr_col(db, n, 5);
        lemma_expr_col(db, n, 7);
        lemma_expr_text(db, n, u);
        lemma_pred_text_cmp(db, n, CmpOp::Eq, Expr::Col(5), Expr::Lit(ps[0]), tval(n[5]), u);
        let nn = Pred::IsNull(Expr::Col(7));
        assert(eval_pred(db, n, nn) == Ok::<Truth, SqlError>(truth_of(false)));
        lemma_pred_not(db, n, nn, false);
        lemma_pred_and(db, n, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(5), b: Expr::Lit(ps[0]) },
            Pred::Not(Box::new(nn)), tval(n[5]) == u, true);
    }
    lemma_eval_filter(db, Query::Table(1), nums, always(), p45(ps), fu(u), fu(u));
}

// ------------------------------------------------------------------ GROUP BY (adsh, tag), MAX(value)

pub open spec fn key_of(r: Row) -> Row {
    seq![r[0], r[1]]
}

pub open spec fn arg_of(r: Row) -> Row {
    seq![r[7]]
}

/// The per-row (key, argument) pairs of the group input.
pub proof fn lemma_group_prepared(db: Database, f: Seq<Row>)
    requires forall|i: int| 0 <= i < f.len() ==> num_shape(#[trigger] f[i]),
    ensures
        collect(Seq::new(f.len(), |i: int|
            match eval_exprs(db, Seq::<Val>::empty() + f[i], grp_keys()) {
                Err(err) => Err(err),
                Ok(k) => match agg_args(db, Seq::<Val>::empty() + f[i], grp_aggs()) {
                    Err(err) => Err(err),
                    Ok(a) => Ok((k, a)),
                },
            })) == Ok::<Seq<(Row, Row)>, SqlError>(Seq::new(f.len(), |i: int| (key_of(f[i]), arg_of(f[i])))),
{
    let ctx = Seq::<Val>::empty();
    let rs = Seq::new(f.len(), |i: int|
        match eval_exprs(db, ctx + f[i], grp_keys()) {
            Err(err) => Err(err),
            Ok(k) => match agg_args(db, ctx + f[i], grp_aggs()) {
                Err(err) => Err(err),
                Ok(a) => Ok((k, a)),
            },
        });
    let vs = Seq::new(f.len(), |i: int| (key_of(f[i]), arg_of(f[i])));
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<(Row, Row), SqlError>(vs[i]) by {
        let r = f[i];
        assert(ctx + r =~= r);
        assert(num_shape(r));
        lemma_group_row(db, r);
    }
    lemma_collect_all(rs, vs);
}

/// One group input row: key `(adsh, tag)`, argument `value`.
proof fn lemma_group_row(db: Database, r: Row)
    requires num_shape(r),
    ensures
        eval_exprs(db, r, grp_keys()) == Ok::<Row, SqlError>(key_of(r)),
        agg_args(db, r, grp_aggs()) == Ok::<Row, SqlError>(arg_of(r)),
{
    let ks = grp_keys();
    lemma_eval_exprs_step(db, r, ks);
    assert(ks.drop_last() =~= seq![Expr::Col(0)]);
    lemma_eval_exprs_step(db, r, ks.drop_last());
    assert(ks.drop_last().drop_last() =~= Seq::<Expr>::empty());
    lemma_eval_exprs_empty(db, r);
    assert(Seq::<Val>::empty().push(r[0]).push(r[1]) =~= key_of(r));
    let ags = grp_aggs();
    lemma_agg_arg_results_index(db, r, ags);
    lemma_collect_all(agg_arg_results(db, r, ags), arg_of(r));
}

/// The facts the rest of the proof needs about the GROUP BY result `g`.
#[verifier::opaque]
pub open spec fn group_ok(nums: Seq<Row>, u: Seq<u8>, g: Seq<Row>) -> bool {
    // Every group row: its key, and its MAX: at least every value of the group and attained by one.
    &&& forall|i: int| 0 <= i < g.len() ==> grp_row_ok(nums, u, #[trigger] g[i])
    // Keys are distinct.
    &&& forall|i: int, j: int| 0 <= i < j < g.len() ==> key_of(#[trigger] g[i]) != key_of(#[trigger] g[j])
    // Every row of unit `u` has its group.
    &&& forall|k: int| 0 <= k < nums.len() && (#[trigger] nums[k])[5] == Val::Text(u)
        ==> exists|i: int| 0 <= i < g.len() && key_of(#[trigger] g[i]) == key_of(nums[k])
}

#[verifier::opaque]
pub open spec fn grp_row_ok(nums: Seq<Row>, u: Seq<u8>, r: Row) -> bool {
    &&& r.len() == 3
    &&& r[0] is Text && r[1] is Text
    &&& r[2] is Num && r[2]->Num_scale == 4
    &&& forall|k: int| 0 <= k < nums.len() && in_grp(#[trigger] nums[k], u, r[0], r[1]) ==> ival(nums[k][7]) <= ival(r[2])
    &&& exists|k: int| 0 <= k < nums.len() && in_grp(#[trigger] nums[k], u, r[0], r[1]) && ival(nums[k][7]) == ival(r[2])
}

/// The GROUP BY evaluates to rows with `group_ok`.
pub proof fn lemma_eval_grp(db: Database, ps: Seq<Literal>)
    requires shapes_ok(db), param_domain(ps),
    ensures
        eval_query(db, Seq::empty(), q_grp(ps)) is Ok,
        group_ok(db.tables[1], uom_of(ps), eval_query(db, Seq::empty(), q_grp(ps))->Ok_0),
{
    let nums = db.tables[1];
    let u = uom_of(ps);
    lemma_eval_f45(db, ps);
    let f = keep(nums, fu(u));
    lemma_keep_members(nums, fu(u));
    assert forall|i: int| 0 <= i < f.len() implies num_shape(#[trigger] f[i]) && f[i][5] == Val::Text(u) by {
        assert(nums.contains(f[i]));
        let k = choose|k: int| 0 <= k < nums.len() && nums[k] == f[i];
        assert(num_shape(nums[k]));
        assert(fu(u)(f[i]));
    }
    lemma_grp_unfold(db, ps, f);
    assert(group_input_ok(nums, u, f, grp_keys_of(f), grp_args_of(f)));
    lemma_group_rows(nums, u, f, grp_keys_of(f), grp_args_of(f));
}

pub open spec fn grp_keys_of(f: Seq<Row>) -> Seq<Row> {
    Seq::new(f.len(), |i: int| key_of(f[i]))
}

pub open spec fn grp_args_of(f: Seq<Row>) -> Seq<Row> {
    Seq::new(f.len(), |i: int| arg_of(f[i]))
}

/// One step of the GROUP BY denotation over its evaluated input `f`.
proof fn lemma_grp_unfold(db: Database, ps: Seq<Literal>, f: Seq<Row>)
    requires
        eval_query(db, Seq::empty(), q_f45(ps)) == Ok::<Relation, SqlError>(f),
        forall|i: int| 0 <= i < f.len() ==> num_shape(#[trigger] f[i]),
    ensures eval_query(db, Seq::empty(), q_grp(ps)) == group_rows(grp_aggs(), grp_keys_of(f), grp_args_of(f)),
{
    hide(eval_exprs);
    hide(agg_args);
    hide(group_rows);
    lemma_group_prepared(db, f);
    let prepared = Seq::new(f.len(), |i: int| (key_of(f[i]), arg_of(f[i])));
    crate::link::query::lemma_groupby_unfold(db, q_f45(ps), grp_keys(), grp_aggs(), f, prepared);
    assert(prepared.map_values(|p: (Row, Row)| p.0) =~= grp_keys_of(f));
    assert(prepared.map_values(|p: (Row, Row)| p.1) =~= grp_args_of(f));
}

/// The GROUP BY output rows: per distinct key, the key followed by the group's MAX.
pub open spec fn grp_out(keys: Seq<Row>, args: Seq<Row>) -> Seq<Row> {
    let ks = distinct_rows(keys);
    Seq::new(ks.len(), |g: int| ks[g] + seq![max_value(column(group_members(keys, args, ks[g]), 0))->Ok_0])
}

pub open spec fn group_input_ok(nums: Seq<Row>, u: Seq<u8>, f: Seq<Row>, keys: Seq<Row>, args: Seq<Row>) -> bool {
    &&& f == keep(nums, fu(u))
    &&& forall|i: int| 0 <= i < f.len() ==> num_shape(#[trigger] f[i]) && f[i][5] == Val::Text(u)
    &&& keys == Seq::new(f.len(), |i: int| key_of(f[i]))
    &&& args == Seq::new(f.len(), |i: int| arg_of(f[i]))
}

/// `group_rows` over the rows `f` of unit `u` (keys and arguments per row).
proof fn lemma_group_rows(nums: Seq<Row>, u: Seq<u8>, f: Seq<Row>, keys: Seq<Row>, args: Seq<Row>)
    requires group_input_ok(nums, u, f, keys, args),
    ensures
        group_rows(grp_aggs(), keys, args) is Ok,
        group_ok(nums, u, group_rows(grp_aggs(), keys, args)->Ok_0),
{
    lemma_group_out(nums, u, f, keys, args);
    lemma_group_distinct(nums, u, f, keys, args);
    lemma_group_cover(nums, u, f, keys, args);
    reveal(group_ok);
}

/// Distinct keys of the group input are two texts, each the key of some input row.
proof fn lemma_group_keys(nums: Seq<Row>, u: Seq<u8>, f: Seq<Row>, keys: Seq<Row>, args: Seq<Row>, g: int)
    requires group_input_ok(nums, u, f, keys, args), 0 <= g < distinct_rows(keys).len(),
    ensures
        distinct_rows(keys)[g].len() == 2, distinct_rows(keys)[g][0] is Text, distinct_rows(keys)[g][1] is Text,
        exists|i: int| 0 <= i < keys.len() && keys[i] == distinct_rows(keys)[g],
{
    lemma_distinct_rows_sub(keys);
    let k = distinct_rows(keys)[g];
    assert(keys.contains(k));
    let i = choose|i: int| 0 <= i < keys.len() && keys[i] == k;
    assert(num_shape(f[i]));
}

proof fn lemma_group_out(nums: Seq<Row>, u: Seq<u8>, f: Seq<Row>, keys: Seq<Row>, args: Seq<Row>)
    requires group_input_ok(nums, u, f, keys, args),
    ensures
        group_rows(grp_aggs(), keys, args) == Ok::<Seq<Row>, SqlError>(grp_out(keys, args)),
        forall|g: int| 0 <= g < grp_out(keys, args).len() ==> grp_row_ok(nums, u, #[trigger] grp_out(keys, args)[g]),
{
    hide(agg_row);
    let ks = distinct_rows(keys);
    let out = grp_out(keys, args);
    let rs = Seq::new(ks.len(), |g: int| match agg_row(grp_aggs(), group_members(keys, args, ks[g])) {
        Ok(a) => Ok(ks[g] + a),
        Err(e) => Err(e),
    });
    assert forall|g: int| 0 <= g < rs.len() implies #[trigger] rs[g] == Ok::<Row, SqlError>(out[g]) by {
        lemma_group_keys(nums, u, f, keys, args, g);
        lemma_one_group(nums, u, f, keys, args, ks[g]);
    }
    assert forall|g: int| 0 <= g < out.len() implies grp_row_ok(nums, u, #[trigger] out[g]) by {
        lemma_group_keys(nums, u, f, keys, args, g);
        lemma_one_group(nums, u, f, keys, args, ks[g]);
    }
    lemma_collect_all(rs, out);
    crate::bridge::collect::lemma_collect_pointwise::<Row>();
    assert(group_rows(grp_aggs(), keys, args) == collect(rs));
}

proof fn lemma_group_distinct(nums: Seq<Row>, u: Seq<u8>, f: Seq<Row>, keys: Seq<Row>, args: Seq<Row>)
    requires group_input_ok(nums, u, f, keys, args),
    ensures forall|i: int, j: int| 0 <= i < j < grp_out(keys, args).len()
        ==> key_of(#[trigger] grp_out(keys, args)[i]) != key_of(#[trigger] grp_out(keys, args)[j]),
{
    hide(row_not_distinct);
    let ks = distinct_rows(keys);
    let out = grp_out(keys, args);
    assert forall|i: int, j: int| 0 <= i < j < out.len() implies key_of(#[trigger] out[i]) != key_of(#[trigger] out[j]) by {
        lemma_group_keys(nums, u, f, keys, args, i);
        lemma_group_keys(nums, u, f, keys, args, j);
        assert(key_of(out[i]) =~= ks[i]);
        assert(key_of(out[j]) =~= ks[j]);
        lemma_distinct_pair(keys, i, j);
        lemma_not_distinct_text2(ks[i], ks[j]);
    }
}

proof fn lemma_group_cover(nums: Seq<Row>, u: Seq<u8>, f: Seq<Row>, keys: Seq<Row>, args: Seq<Row>)
    requires group_input_ok(nums, u, f, keys, args),
    ensures forall|k: int| 0 <= k < nums.len() && (#[trigger] nums[k])[5] == Val::Text(u)
        ==> exists|i: int| 0 <= i < grp_out(keys, args).len() && key_of(#[trigger] grp_out(keys, args)[i]) == key_of(nums[k]),
{
    hide(row_not_distinct);
    let ks = distinct_rows(keys);
    let out = grp_out(keys, args);
    assert forall|k: int| 0 <= k < nums.len() && (#[trigger] nums[k])[5] == Val::Text(u)
        implies exists|i: int| 0 <= i < out.len() && key_of(#[trigger] out[i]) == key_of(nums[k]) by {
        lemma_keep_complete(nums, fu(u), k);
        let i = choose|i: int| 0 <= i < f.len() && f[i] == nums[k];
        assert(keys[i] == key_of(nums[k]));
        assert(num_shape(f[i]));
        lemma_distinct_cover(keys, i);
        let g = choose|g: int| 0 <= g < ks.len() && row_not_distinct(#[trigger] ks[g], keys[i]);
        lemma_group_keys(nums, u, f, keys, args, g);
        lemma_not_distinct_text2(ks[g], keys[i]);
        assert(key_of(out[g]) =~= ks[g]);
    }
}

/// One group with key `k` (a key of some row): its MAX is a numeric at scale 4, at least every value of the group
/// and attained by one of them.
proof fn lemma_one_group(nums: Seq<Row>, u: Seq<u8>, f: Seq<Row>, keys: Seq<Row>, args: Seq<Row>, k: Row)
    requires
        f == keep(nums, fu(u)),
        forall|i: int| 0 <= i < f.len() ==> num_shape(#[trigger] f[i]) && f[i][5] == Val::Text(u),
        keys == Seq::new(f.len(), |i: int| key_of(f[i])),
        args == Seq::new(f.len(), |i: int| arg_of(f[i])),
        exists|i: int| 0 <= i < keys.len() && keys[i] == k,
    ensures
        agg_row(grp_aggs(), group_members(keys, args, k))
            == Ok::<Row, SqlError>(seq![max_value(column(group_members(keys, args, k), 0))->Ok_0]),
        grp_row_ok(nums, u, k + seq![max_value(column(group_members(keys, args, k), 0))->Ok_0]),
{
    reveal(grp_row_ok);
    let gm = group_members(keys, args, k);
    lemma_group_members(keys, args, k);
    let vs = column(gm, 0);
    let i0 = choose|i: int| 0 <= i < keys.len() && keys[i] == k;
    assert(num_shape(f[i0]));
    lemma_row_not_distinct_refl(k);
    assert(row_not_distinct(keys[i0], k));
    let m0 = choose|m: int| 0 <= m < gm.len() && gm[m] == args[i0];
    // Each member value is the value of a row of `f` whose key is `k`.
    assert forall|m: int| 0 <= m < vs.len() implies exists|i: int| 0 <= i < f.len() && key_of(f[i]) == k
        && #[trigger] vs[m] == f[i][7] by {
        assert(member_from(keys, args, k, gm[m]));
        let i = choose|i: int| 0 <= i < keys.len() && row_not_distinct(keys[i], k) && gm[m] == #[trigger] args[i];
        assert(num_shape(f[i]));
        lemma_not_distinct_text2(keys[i], k);
        assert(vs[m] == gm[m][0]);
    }
    assert(all_num_at(vs, 4)) by {
        assert forall|m: int| 0 <= m < vs.len() implies (#[trigger] vs[m] is Num && vs[m]->Num_scale == 4) by {
            let i = choose|i: int| 0 <= i < f.len() && key_of(f[i]) == k && #[trigger] vs[m] == f[i][7];
            assert(num_shape(f[i]));
        }
    }
    assert(vs[m0] == f[i0][7]);
    lemma_max_num(vs, 4);
    let mx = Val::Num { coeff: max_coeff(vs), scale: 4 };
    let r = k + seq![mx];
    assert(agg_row(grp_aggs(), gm) == collect(Seq::new(1, |j: int| agg_value(grp_aggs()[j], column(gm, j)))));
    lemma_collect_all(Seq::new(1, |j: int| agg_value(grp_aggs()[j], column(gm, j))), seq![mx]);
    assert(r[0] == k[0] && r[1] == k[1] && r[2] == mx);
    lemma_keep_members(nums, fu(u));
    // At least every value of the group.
    assert forall|q: int| 0 <= q < nums.len() && in_grp(#[trigger] nums[q], u, r[0], r[1]) implies ival(nums[q][7]) <= ival(r[2]) by {
        lemma_keep_complete(nums, fu(u), q);
        let i = choose|i: int| 0 <= i < f.len() && f[i] == nums[q];
        assert(keys[i] == key_of(f[i]));
        assert(key_of(f[i]) =~= k);
        assert(row_not_distinct(keys[i], k));
        let m = choose|m: int| 0 <= m < gm.len() && gm[m] == args[i];
        assert(vs[m] == gm[m][0]);
    }
    // Attained by a row of the group.
    let w = choose|m: int| 0 <= m < vs.len() && ival(vs[m]) == max_coeff(vs);
    let i = choose|i: int| 0 <= i < f.len() && key_of(f[i]) == k && #[trigger] vs[w] == f[i][7];
    assert(nums.contains(f[i]));
    let q = choose|q: int| 0 <= q < nums.len() && nums[q] == f[i];
    assert(key_of(f[i])[0] == f[i][0] && key_of(f[i])[1] == f[i][1]);
    assert(in_grp(nums[q], u, r[0], r[1]));
}

// ------------------------------------------------------------------ product with the groups, filters, projection

/// A group row's shape.
pub open spec fn g_shape(g: Row) -> bool {
    &&& g.len() == 3
    &&& g[0] is Text && g[1] is Text
    &&& g[2] is Num && g[2]->Num_scale == 4
}

/// The positions of a joined row `n ++ s ++ g` that the plan reads.
pub proof fn lemma_joined_index(n: Row, s: Row, g: Row)
    requires num_shape(n), sub_shape(s), g_shape(g),
    ensures ({
        let x = n + s + g;
        &&& x.len() == 32
        &&& x[0] == n[0] && x[1] == n[1] && x[5] == n[5] && x[7] == n[7]
        &&& x[9] == s[0] && x[11] == s[2] && x[19] == s[10]
        &&& x[29] == g[0] && x[30] == g[1] && x[31] == g[2]
    }),
{
    let a = n + s;
    assert(a[0] == n[0] && a[1] == n[1] && a[5] == n[5] && a[7] == n[7]);
    assert(a[9] == s[0] && a[11] == s[2] && a[19] == s[10]);
}

/// Every row of `(num x sub) x groups` is a num row, a sub row and a group row.
pub open spec fn pg_shape(x: Row) -> bool {
    exists|n: Row, s: Row, g: Row| num_shape(n) && sub_shape(s) && g_shape(g) && x == n + s + g
}

pub open spec fn h26() -> spec_fn(Row) -> bool {
    |x: Row| x[0] == x[29] && x[1] == x[30] && ival(x[7]) == ival(x[31])
}

pub open spec fn f26c() -> spec_fn(Row) -> bool {
    |x: Row| x[0] == x[9] && (x[0] == x[29] && x[1] == x[30] && ival(x[7]) == ival(x[31]))
}

pub open spec fn h15(u: Seq<u8>, y: int) -> spec_fn(Row) -> bool {
    |x: Row| x[5] == Val::Text(u) && x[19] == Val::Int(y)
}

pub open spec fn fall(u: Seq<u8>, y: int) -> spec_fn(Row) -> bool {
    |x: Row| (x[0] == x[9] && (x[0] == x[29] && x[1] == x[30] && ival(x[7]) == ival(x[31])))
        && (x[5] == Val::Text(u) && x[19] == Val::Int(y))
}

pub open spec fn proj3() -> spec_fn(Row) -> Row {
    |x: Row| seq![x[11], x[1], x[7]]
}

/// Text equality of two text values of a row.
proof fn lemma_text_eq(db: Database, x: Row, i: nat, j: nat)
    requires i < x.len(), j < x.len(), x[i as int] is Text, x[j as int] is Text,
    ensures eval_pred(db, x, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(i), b: Expr::Col(j) })
        == Ok::<Truth, SqlError>(truth_of(x[i as int] == x[j as int])),
{
    lemma_expr_col(db, x, i);
    lemma_expr_col(db, x, j);
    lemma_pred_text_cmp(db, x, CmpOp::Eq, Expr::Col(i), Expr::Col(j), tval(x[i as int]), tval(x[j as int]));
}

/// The join condition on `n.value = m.max_value` and the group keys.
proof fn lemma_pred26(db: Database, n: Row, s: Row, g: Row)
    requires num_shape(n), sub_shape(s), g_shape(g),
    ensures eval_pred(db, n + s + g, p26()) == Ok::<Truth, SqlError>(truth_of(h26()(n + s + g))),
{
    let x = n + s + g;
    lemma_joined_index(n, s, g);
    lemma_text_eq(db, x, 0, 29);
    lemma_text_eq(db, x, 1, 30);
    let (c1, c2) = (x[7]->Num_coeff, x[31]->Num_coeff);
    lemma_expr_col(db, x, 7);
    lemma_expr_col(db, x, 31);
    crate::link::expr::lemma_compare_num(c1, 4, c2, 4);
    lemma_align_same(c1, 4);
    lemma_align_same(c2, 4);
    assert(max_nat(4, 4) == 4);
    lemma_pred_cmp(db, x, CmpOp::Eq, Expr::Col(7), Expr::Col(31), x[7], x[31], c1, c2);
    let a1 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(29) };
    let a2 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(1), b: Expr::Col(30) };
    let a3 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(7), b: Expr::Col(31) };
    lemma_pred_and(db, x, a1, a2, x[0] == x[29], x[1] == x[30]);
    lemma_pred_and(db, x, Pred::And(Box::new(a1), Box::new(a2)), a3, x[0] == x[29] && x[1] == x[30], c1 == c2);
}

/// Kleene AND of two evaluated conditions.
proof fn lemma_and_ok(db: Database, x: Row, a: Pred, b: Pred, ta: Truth, tb: Truth)
    requires eval_pred(db, x, a) == Ok::<Truth, SqlError>(ta), eval_pred(db, x, b) == Ok::<Truth, SqlError>(tb),
    ensures eval_pred(db, x, Pred::And(Box::new(a), Box::new(b))) == Ok::<Truth, SqlError>(truth_and(ta, tb)),
{
}

/// `s.fy = $2` on a row whose fiscal year is NULL or an integer.
proof fn lemma_pred_fy(db: Database, ps: Seq<Literal>, x: Row)
    requires x.len() == 32, x[19] is Null || x[19] is Int, param_domain(ps),
    ensures ({
        let c19 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(19), b: Expr::Lit(ps[1]) };
        &&& eval_pred(db, x, c19) is Ok
        &&& (eval_pred(db, x, c19)->Ok_0 is True) == (x[19] == Val::Int(fy_of(ps)))
        &&& !(eval_pred(db, x, c19)->Ok_0 is False) || (x[19] is Int)
        &&& x[19] is Int ==> eval_pred(db, x, c19) == Ok::<Truth, SqlError>(truth_of(x[19] == Val::Int(fy_of(ps))))
        &&& x[19] is Null ==> eval_pred(db, x, c19) == Ok::<Truth, SqlError>(Truth::Unknown)
    }),
{
    let y = fy_of(ps);
    assert(ps[1] == Literal::Int { v: y, kind: IntKind::Int4 });
    lemma_expr_col(db, x, 19);
    assert(eval_expr(db, x, Expr::Lit(ps[1])) == Ok::<Val, SqlError>(Val::Int(y)));
    if x[19] is Int {
        crate::link::expr::lemma_compare_int(x[19]->Int_0, y);
        lemma_pred_cmp(db, x, CmpOp::Eq, Expr::Col(19), Expr::Lit(ps[1]), x[19], Val::Int(y), x[19]->Int_0, y);
    }
}

/// `n.uom = $1 AND s.fy = $2 AND n.value IS NOT NULL`: `True` exactly when the unit and the fiscal year match
/// (a NULL fiscal year gives `Unknown`).
proof fn lemma_pred15(db: Database, ps: Seq<Literal>, n: Row, s: Row, g: Row)
    requires num_shape(n), sub_shape(s), g_shape(g), param_domain(ps),
    ensures
        eval_pred(db, n + s + g, p15(ps)) is Ok,
        (eval_pred(db, n + s + g, p15(ps))->Ok_0 is True) == h15(uom_of(ps), fy_of(ps))(n + s + g),
{
    hide(eval_pred);
    let x = n + s + g;
    let (u, y) = (uom_of(ps), fy_of(ps));
    lemma_joined_index(n, s, g);
    assert(ps[0] == Literal::Text(u));
    lemma_expr_col(db, x, 5);
    lemma_expr_text(db, x, u);
    let c5 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(5), b: Expr::Lit(ps[0]) };
    let c19 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(19), b: Expr::Lit(ps[1]) };
    let nn = Pred::IsNull(Expr::Col(7));
    lemma_pred_text_cmp(db, x, CmpOp::Eq, Expr::Col(5), Expr::Lit(ps[0]), tval(x[5]), u);
    lemma_pred_fy(db, ps, x);
    let t5 = truth_of(tval(x[5]) == u);
    let t19 = eval_pred(db, x, c19)->Ok_0;
    lemma_is_null_false(db, x);
    lemma_pred_not(db, x, nn, false);
    lemma_and_ok(db, x, c5, c19, t5, t19);
    lemma_and_ok(db, x, Pred::And(Box::new(c5), Box::new(c19)), Pred::Not(Box::new(nn)), truth_and(t5, t19), truth_of(true));
    assert(p15(ps) == Pred::And(Box::new(Pred::And(Box::new(c5), Box::new(c19))), Box::new(Pred::Not(Box::new(nn)))));
}

proof fn lemma_is_null_false(db: Database, x: Row)
    requires x.len() == 32, x[7] is Num,
    ensures eval_pred(db, x, Pred::IsNull(Expr::Col(7))) == Ok::<Truth, SqlError>(truth_of(false)),
{
    lemma_expr_col(db, x, 7);
}

/// The groups' shape.
pub proof fn lemma_group_shapes(nums: Seq<Row>, u: Seq<u8>, g: Seq<Row>)
    requires group_ok(nums, u, g),
    ensures forall|i: int| 0 <= i < g.len() ==> g_shape(#[trigger] g[i]),
{
    reveal(group_ok);
    assert forall|i: int| 0 <= i < g.len() implies g_shape(#[trigger] g[i]) by {
        assert(grp_row_ok(nums, u, g[i]));
        reveal(grp_row_ok);
    }
}

/// The rows of `(num x sub) x groups` are joined rows.
pub proof fn lemma_pg_shapes(nums: Seq<Row>, subs: Seq<Row>, g: Seq<Row>)
    requires
        forall|i: int| 0 <= i < nums.len() ==> num_shape(#[trigger] nums[i]),
        forall|i: int| 0 <= i < subs.len() ==> sub_shape(#[trigger] subs[i]),
        forall|i: int| 0 <= i < g.len() ==> g_shape(#[trigger] g[i]),
    ensures
        forall|k: int| 0 <= k < product_rows(product_rows(nums, subs), g).len()
            ==> pg_shape(#[trigger] product_rows(product_rows(nums, subs), g)[k]),
{
    let ns = product_rows(nums, subs);
    let pg = product_rows(ns, g);
    lemma_product_rows_elems(nums, subs);
    lemma_product_rows_elems(ns, g);
    assert forall|k: int| 0 <= k < pg.len() implies pg_shape(#[trigger] pg[k]) by {
        assert(is_concat(pg[k], ns, g));
        let (a, b) = choose|a: int, b: int| 0 <= a < ns.len() && 0 <= b < g.len() && pg[k] == #[trigger] ns[a] + #[trigger] g[b];
        assert(is_concat(ns[a], nums, subs));
        let (i, j) = choose|i: int, j: int| 0 <= i < nums.len() && 0 <= j < subs.len() && ns[a] == #[trigger] nums[i] + #[trigger] subs[j];
        assert(num_shape(nums[i]) && sub_shape(subs[j]) && g_shape(g[b]));
    }
}

/// The body evaluates to the joined rows kept by the whole condition, projected on `(s.name, n.tag, n.value)`.
pub proof fn lemma_eval_body(db: Database, ps: Seq<Literal>)
    requires shapes_ok(db), param_domain(ps),
    ensures ({
        let g = eval_query(db, Seq::empty(), q_grp(ps))->Ok_0;
        let pg = product_rows(product_rows(db.tables[1], db.tables[0]), g);
        &&& eval_query(db, Seq::empty(), q_grp(ps)) is Ok
        &&& group_ok(db.tables[1], uom_of(ps), g)
        &&& denote_body(db, query_spec_at(ps))
            == Ok::<Relation, SqlError>(keep(pg, fall(uom_of(ps), fy_of(ps))).map_values(proj3()))
    }),
{
    let (nums, subs) = (db.tables[1], db.tables[0]);
    let (u, y) = (uom_of(ps), fy_of(ps));
    lemma_eval_f29(db);
    lemma_eval_grp(db, ps);
    let g = eval_query(db, Seq::empty(), q_grp(ps))->Ok_0;
    lemma_group_shapes(nums, u, g);
    let ns = product_rows(nums, subs);
    let pg = product_rows(ns, g);
    lemma_pg_shapes(nums, subs, g);
    // Product with the groups.
    lemma_keep_all(g, always());
    assert forall|i: int| 0 <= i < ns.len() implies (#[trigger] ns[i]).len() == 29 by {
        assert(ns_shape(ns[i]));
    }
    assert forall|k: int| 0 <= k < pg.len() implies #[trigger] f29()(pg[k])
        == (f29()(left_of(pg[k], 29)) && always()(right_of(pg[k], 29))) by {
        assert(pg_shape(pg[k]));
        let (n, s, gg) = choose|n: Row, s: Row, gg: Row| num_shape(n) && sub_shape(s) && g_shape(gg) && pg[k] == n + s + gg;
        lemma_joined_index(n, s, gg);
    }
    lemma_eval_product(db, q_f29(), q_grp(ps), ns, f29(), 29, g, always(), pg, f29());
    // n.adsh = m.adsh AND n.tag = m.tag AND n.value = m.max_value.
    assert forall|k: int| 0 <= k < pg.len() && f29()(#[trigger] pg[k]) implies
        eval_pred(db, pg[k], p26()) == Ok::<Truth, SqlError>(truth_of(h26()(pg[k]))) by {
        assert(pg_shape(pg[k]));
        let (n, s, gg) = choose|n: Row, s: Row, gg: Row| num_shape(n) && sub_shape(s) && g_shape(gg) && pg[k] == n + s + gg;
        lemma_pred26(db, n, s, gg);
    }
    lemma_eval_filter(db, q_prod(ps), pg, f29(), p26(), h26(), f26c());
    // WHERE n.uom = $1 AND s.fy = $2 AND n.value IS NOT NULL.
    assert forall|k: int| 0 <= k < pg.len() && f26c()(#[trigger] pg[k]) implies
        eval_pred(db, pg[k], p15(ps)) is Ok && (eval_pred(db, pg[k], p15(ps))->Ok_0 is True) == h15(u, y)(pg[k]) by {
        assert(pg_shape(pg[k]));
        let (n, s, gg) = choose|n: Row, s: Row, gg: Row| num_shape(n) && sub_shape(s) && g_shape(gg) && pg[k] == n + s + gg;
        lemma_pred15(db, ps, n, s, gg);
    }
    lemma_eval_filter3(db, q_f26(ps), pg, f26c(), p15(ps), h15(u, y), fall(u, y));
    // SELECT s.name, n.tag, n.value.
    lemma_eval_project(db, ps, pg, fall(u, y));
    lemma_body_tree(ps);
}

/// The projection of the kept joined rows.
proof fn lemma_eval_project(db: Database, ps: Seq<Literal>, pg: Seq<Row>, f: spec_fn(Row) -> bool)
    requires
        eval_query(db, Seq::empty(), q_f15(ps)) == Ok::<Relation, SqlError>(keep(pg, f)),
        forall|k: int| 0 <= k < pg.len() ==> pg_shape(#[trigger] pg[k]),
    ensures eval_query(db, Seq::empty(), q_body(ps)) == Ok::<Relation, SqlError>(keep(pg, f).map_values(proj3())),
{
    let kept = keep(pg, f);
    lemma_keep_members(pg, f);
    let outs = seq![11nat, 1nat, 7nat];
    assert forall|i: int| 0 <= i < kept.len() implies (#[trigger] kept[i]).len() == 32 by {
        assert(pg.contains(kept[i]));
        let k = choose|k: int| 0 <= k < pg.len() && pg[k] == kept[i];
        assert(pg_shape(pg[k]));
        let (n, s, gg) = choose|n: Row, s: Row, gg: Row| num_shape(n) && sub_shape(s) && g_shape(gg) && pg[k] == n + s + gg;
        lemma_joined_index(n, s, gg);
    }
    crate::link::query::lemma_project_cols(db, q_f15(ps), kept, outs, 32);
    assert(crate::link::query::col_exprs(outs) =~= out_exprs());
    assert(kept.map_values(|r: Row| crate::link::query::select(r, outs)) =~= kept.map_values(proj3())) by {
        assert forall|i: int| 0 <= i < kept.len() implies crate::link::query::select(kept[i], outs) == proj3()(kept[i]) by {
            assert(crate::link::query::select(kept[i], outs) =~= proj3()(kept[i]));
        }
    }
}

// ------------------------------------------------------------------ the count

/// For one num row `n` (a row of `nums`) and one sub row `s`, exactly one group can match, and it matches exactly
/// when `n` holds its group's MAX: the sum over the groups is `pair_hit`.
pub proof fn lemma_groups_sum(nums: Seq<Row>, u: Seq<u8>, y: int, t: Row, g: Seq<Row>, n: Row, s: Row, kn: int)
    requires
        group_ok(nums, u, g),
        forall|i: int| 0 <= i < g.len() ==> g_shape(#[trigger] g[i]),
        0 <= kn < nums.len(), nums[kn] == n,
        num_shape(n), sub_shape(s),
    ensures sum_of(g, |b: Row| hit(fall(u, y), proj3(), t)((n + s) + b)) == pair_hit(nums, u, y, t, n, s),
{
    let k = |b: Row| hit(fall(u, y), proj3(), t)((n + s) + b);
    let c = n[0] == s[0] && n[5] == Val::Text(u) && s[10] == Val::Int(y) && out_row(n, s) == t;
    // Each group's term.
    assert forall|j: int| 0 <= j < g.len() implies #[trigger] k(g[j]) == (if c && g[j][0] == n[0] && g[j][1] == n[1]
        && ival(n[7]) == ival(g[j][2]) { 1int } else { 0int }) by {
        lemma_joined_index(n, s, g[j]);
        assert(proj3()((n + s) + g[j]) =~= out_row(n, s));
    }
    if !c {
        lemma_sum_of_zero(g, k);
    } else {
        reveal(group_ok);
        assert(nums[kn][5] == Val::Text(u));
        let i = choose|i: int| 0 <= i < g.len() && key_of(#[trigger] g[i]) == key_of(nums[kn]);
        assert(g[i][0] == key_of(g[i])[0] && g[i][1] == key_of(g[i])[1]);
        assert forall|j: int| 0 <= j < g.len() && j != i implies k(#[trigger] g[j]) == 0 by {
            if g[j][0] == n[0] && g[j][1] == n[1] {
                assert(key_of(g[j]) =~= key_of(g[i]));
                if j < i {
                    assert(key_of(g[j]) != key_of(g[i]));
                } else {
                    assert(key_of(g[i]) != key_of(g[j]));
                }
            }
        }
        lemma_sum_of_single(g, k, i);
        let r = g[i];
        assert(grp_row_ok(nums, u, r));
        reveal(grp_row_ok);
        assert(in_grp(nums[kn], u, r[0], r[1]));
        let w = choose|q: int| 0 <= q < nums.len() && in_grp(#[trigger] nums[q], u, r[0], r[1]) && ival(nums[q][7]) == ival(r[2]);
        if ival(n[7]) == ival(r[2]) {
            assert forall|q: int| 0 <= q < nums.len() && in_grp(#[trigger] nums[q], u, n[0], n[1]) implies ival(nums[q][7]) <= ival(n[7]) by {
                assert(in_grp(nums[q], u, r[0], r[1]));
            }
            assert(is_gmax(nums, u, n));
        } else {
            if is_gmax(nums, u, n) {
                assert(in_grp(nums[w], u, n[0], n[1]));
                assert(ival(nums[w][7]) <= ival(n[7]));
                assert(ival(nums[kn][7]) <= ival(r[2]));
            }
        }
    }
}

/// The multiplicity of every row `t` in the body is `body_count`.
pub proof fn lemma_body_count(db: Database, ps: Seq<Literal>, t: Row)
    requires shapes_ok(db), param_domain(ps),
    ensures ({
        let g = eval_query(db, Seq::empty(), q_grp(ps))->Ok_0;
        let pg = product_rows(product_rows(db.tables[1], db.tables[0]), g);
        keep(pg, fall(uom_of(ps), fy_of(ps))).map_values(proj3()).to_multiset().count(t)
            == body_count(db.tables[1], db.tables[0], uom_of(ps), fy_of(ps), t)
    }),
{
    let (nums, subs) = (db.tables[1], db.tables[0]);
    let (u, y) = (uom_of(ps), fy_of(ps));
    lemma_eval_grp(db, ps);
    let g = eval_query(db, Seq::empty(), q_grp(ps))->Ok_0;
    lemma_group_shapes(nums, u, g);
    let ns = product_rows(nums, subs);
    let pg = product_rows(ns, g);
    let h = hit(fall(u, y), proj3(), t);
    lemma_count_keep_map(pg, fall(u, y), proj3(), t);
    lemma_sum_of_product(ns, g, h);
    let f2 = |a: Row| sum_of(g, |b: Row| h(a + b));
    lemma_sum_of_product(nums, subs, f2);
    let outer = |n: Row| sum_of(subs, |s: Row| f2(n + s));
    assert forall|i: int| 0 <= i < nums.len() implies #[trigger] outer(nums[i]) == sub_hits(nums, subs, u, y, t)(nums[i]) by {
        let n = nums[i];
        assert(num_shape(n));
        assert forall|j: int| 0 <= j < subs.len() implies #[trigger] f2(n + subs[j]) == pair_hit(nums, u, y, t, n, subs[j]) by {
            assert(sub_shape(subs[j]));
            lemma_groups_sum(nums, u, y, t, g, n, subs[j], i);
        }
        lemma_sum_of_ext(subs, |s: Row| f2(n + s), |s: Row| pair_hit(nums, u, y, t, n, s));
    }
    lemma_sum_of_ext(nums, outer, sub_hits(nums, subs, u, y, t));
}

/// The SQL meaning: the body has no error, and every row's multiplicity is `body_count`.
pub proof fn lemma_body(db: Database, ps: Seq<Literal>)
    requires shapes_ok(db), param_domain(ps),
    ensures
        denote_body(db, query_spec_at(ps)) is Ok,
        forall|t: Row| #[trigger] denote_body(db, query_spec_at(ps))->Ok_0.to_multiset().count(t)
            == body_count(db.tables[1], db.tables[0], uom_of(ps), fy_of(ps), t),
{
    lemma_eval_body(db, ps);
    assert forall|t: Row| #[trigger] denote_body(db, query_spec_at(ps))->Ok_0.to_multiset().count(t)
        == body_count(db.tables[1], db.tables[0], uom_of(ps), fy_of(ps), t) by {
        lemma_body_count(db, ps, t);
    }
}

} // verus!
