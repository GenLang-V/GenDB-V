//! Normal form of the statement over the source relations `N = num` (table 1) and `S = sub` (table 0).
//!
//! The FROM/WHERE of the outer query and of the subquery both evaluate (under a context of any length) to the
//! joined rows `x = n ++ s` of `product_rows(N, S)` kept by `fq`: `n.adsh = s.adsh`, `n.uom = $1`, `s.fy = $2`
//! (`n.value` is never NULL). A group accumulator over those rows (the toolkit's `gsum`/`gabs`/`gcount` with a key
//! that depends on the `sub` row only) is a sum over the `sub` rows `s` with `fy = $2` and that key of the per-filing
//! sum `fsum(s, w) = sum of w(n) over the num rows n with n.adsh = s.adsh and n.uom = $1` (`lemma_dec`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::types::*;
use crate::spec::typing::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::text::lex_cmp;
use crate::schema::schema_spec;
use crate::link::query::{QuerySpec, AggKind, hit, gsum, gabs, gcount};
use crate::link::join::{keep, sum_of, lemma_keep_keep, lemma_keep_ext, lemma_keep_members, lemma_sum_of_product_swap,
    lemma_sum_of_ext, lemma_sum_of_zero, lemma_acc_sum_of, sum_term, abs_term, count_term};
use crate::bridge::collect::{lemma_collect_all, lemma_collect_pointwise};
use crate::bridge::relation::{is_concat, lemma_product_rows_elems};
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::agent::ast::*;

verus! {

// ------------------------------------------------------------------------------------------- parameters and rows

/// The binding of the statement: `$1` text `p0`, `$2` integer `p1`.
pub open spec fn lits(p0: Seq<u8>, p1: int) -> Seq<Literal> {
    seq![Literal::Text(p0), Literal::Int { v: p1, kind: IntKind::Int4 }]
}

/// The coefficient of a numeric value (0 otherwise).
pub open spec fn coeff(v: Val) -> int {
    match v {
        Val::Num { coeff, .. } => coeff,
        _ => 0,
    }
}

/// A `num` row: 9 columns, `adsh` and `uom` text, `value` a numeric(28, 4).
pub open spec fn num_row_ok(n: Row) -> bool {
    &&& n.len() == 9
    &&& n[0] is Text
    &&& n[5] is Text
    &&& n[7] is Num
    &&& n[7]->Num_scale == 4
    &&& abs(coeff(n[7])) < pow10(28)
}

/// A `sub` row: 20 columns, `adsh` text, `cik` integer, `name` text, `fy` integer or NULL.
pub open spec fn sub_row_ok(s: Row) -> bool {
    &&& s.len() == 20
    &&& s[0] is Text
    &&& s[1] is Int
    &&& s[2] is Text
    &&& (s[10] is Null || s[10] is Int)
}

pub open spec fn num_rel(db: Database) -> Seq<Row> {
    db.tables[1]
}

pub open spec fn sub_rel(db: Database) -> Seq<Row> {
    db.tables[0]
}

/// The joined rows `num x sub` (left-major).
pub open spec fn joined(db: Database) -> Seq<Row> {
    product_rows(num_rel(db), sub_rel(db))
}

/// Every row of `num` and `sub` has its declared shape.
pub open spec fn rows_ok(db: Database) -> bool {
    &&& db.tables.len() == 4
    &&& forall|i: int| 0 <= i < num_rel(db).len() ==> num_row_ok(#[trigger] num_rel(db)[i])
    &&& forall|i: int| 0 <= i < sub_rel(db).len() ==> sub_row_ok(#[trigger] sub_rel(db)[i])
}

/// The declared columns give the row shapes.
pub proof fn lemma_rows_ok(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures rows_ok(db),
{
    crate::stores::num::declaration::lemma_declared_schema();
    crate::stores::sub_fy::declaration::lemma_declared_schema();
    let tn = schema_spec()[1];
    let ts = schema_spec()[0];
    let cn = crate::stores::num::declaration::stored_cols_t0();
    let cs = crate::stores::sub_fy::declaration::stored_cols_t0();
    assert(crate::link::source::proj_columns(tn, cn)[0] == tn.columns[0]);
    assert(crate::link::source::proj_columns(tn, cn)[5] == tn.columns[5]);
    assert(crate::link::source::proj_columns(tn, cn)[7] == tn.columns[7]);
    assert(crate::link::source::proj_columns(ts, cs)[0] == ts.columns[0]);
    assert(crate::link::source::proj_columns(ts, cs)[1] == ts.columns[1]);
    assert(crate::link::source::proj_columns(ts, cs)[2] == ts.columns[2]);
    assert(crate::link::source::proj_columns(ts, cs)[10] == ts.columns[10]);
    assert forall|i: int| 0 <= i < num_rel(db).len() implies num_row_ok(#[trigger] num_rel(db)[i]) by {
        let n = num_rel(db)[i];
        assert(row_in_table(n, tn));
        assert(value_in_column(n[0], tn.columns[0]));
        assert(value_in_column(n[5], tn.columns[5]));
        assert(value_in_column(n[7], tn.columns[7]));
    }
    assert forall|i: int| 0 <= i < sub_rel(db).len() implies sub_row_ok(#[trigger] sub_rel(db)[i]) by {
        let s = sub_rel(db)[i];
        assert(row_in_table(s, ts));
        assert(value_in_column(s[0], ts.columns[0]));
        assert(value_in_column(s[1], ts.columns[1]));
        assert(value_in_column(s[2], ts.columns[2]));
        assert(value_in_column(s[10], ts.columns[10]));
    }
}

// ------------------------------------------------------------------------------------------- the qualifying rows

/// `n.adsh = s.adsh AND n.uom = $1 AND s.fy = $2` on a joined row.
pub open spec fn fq(p0: Seq<u8>, p1: int, x: Row) -> bool {
    x[0] == x[9] && x[5] == Val::Text(p0) && x[19] == Val::Int(p1)
}

pub open spec fn fq_fn(p0: Seq<u8>, p1: int) -> spec_fn(Row) -> bool {
    |x: Row| fq(p0, p1, x)
}

/// The join condition alone.
pub open spec fn fj(x: Row) -> bool {
    x[0] == x[9]
}

/// The WHERE conditions after the join.
pub open spec fn fw(p0: Seq<u8>, p1: int, x: Row) -> bool {
    x[5] == Val::Text(p0) && x[19] == Val::Int(p1)
}

/// A joined row of well-shaped rows: positions of `num` first, then `sub`.
pub open spec fn joined_row_ok(x: Row) -> bool {
    exists|n: Row, s: Row| num_row_ok(n) && sub_row_ok(s) && x == n + s
}

pub proof fn lemma_joined_rows_ok(db: Database)
    requires rows_ok(db),
    ensures forall|k: int| 0 <= k < joined(db).len() ==> joined_row_ok(#[trigger] joined(db)[k]),
{
    lemma_product_rows_elems(num_rel(db), sub_rel(db));
    assert forall|k: int| 0 <= k < joined(db).len() implies joined_row_ok(#[trigger] joined(db)[k]) by {
        assert(is_concat(joined(db)[k], num_rel(db), sub_rel(db)));
        let (i, j) = choose|i: int, j: int| 0 <= i < num_rel(db).len() && 0 <= j < sub_rel(db).len()
            && joined(db)[k] == #[trigger] num_rel(db)[i] + #[trigger] sub_rel(db)[j];
        assert(num_row_ok(num_rel(db)[i]) && sub_row_ok(sub_rel(db)[j]));
    }
}

/// Positions of a joined row `n ++ s`.
pub proof fn lemma_concat_at(n: Row, s: Row)
    requires n.len() == 9,
    ensures
        forall|i: int| 0 <= i < 9 ==> #[trigger] (n + s)[i] == n[i],
        forall|i: int| 0 <= i < s.len() ==> #[trigger] (n + s)[9 + i] == s[i],
        (n + s).len() == 9 + s.len(),
{
}

// ------------------------------------------------------------------------------------- the FROM/WHERE evaluation

/// `keep_true` over truths whose `True` cases are exactly `f`.
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
        assert(truths.last() == truths[rows.len() - 1]);
    }
}

/// A WHERE under context `ctx` whose condition evaluates on every input row to a truth that is `True` exactly when
/// `h` holds keeps `keep(rows, h)`.
pub proof fn lemma_filter_iff(db: Database, ctx: Row, pred: Pred, input: Query, rows: Seq<Row>, h: spec_fn(Row) -> bool)
    requires
        eval_query(db, ctx, input) == Ok::<Relation, SqlError>(rows),
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] eval_pred(db, ctx + rows[i], pred)) is Ok,
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] eval_pred(db, ctx + rows[i], pred))->Ok_0 is True == h(rows[i]),
    ensures
        eval_query(db, ctx, Query::Filter { pred, input: Box::new(input) }) == Ok::<Relation, SqlError>(keep(rows, h)),
{
    let prs = Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred));
    let truths = Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred)->Ok_0);
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        assert(eval_pred(db, ctx + rows[i], pred) is Ok);
    }
    lemma_collect_all(prs, truths);
    lemma_collect_pointwise::<Truth>();
    assert forall|i: int| 0 <= i < rows.len() implies (#[trigger] truths[i] is True) == h(rows[i]) by {
        assert(eval_pred(db, ctx + rows[i], pred)->Ok_0 is True == h(rows[i]));
    }
    lemma_keep_true_iff(rows, truths, h);
}

/// `num x sub` under any context.
pub proof fn lemma_eval_product(db: Database, ctx: Row)
    requires db.tables.len() == 4,
    ensures eval_query(db, ctx, q_product()) == Ok::<Relation, SqlError>(joined(db)),
{
    assert(eval_query(db, ctx, Query::Table(1)) == Ok::<Relation, SqlError>(db.tables[1]));
    assert(eval_query(db, ctx, Query::Table(0)) == Ok::<Relation, SqlError>(db.tables[0]));
}

/// The join condition on one joined row.
pub proof fn lemma_pred_join_row(db: Database, ctx: Row, x: Row)
    requires joined_row_ok(x),
    ensures eval_pred(db, ctx + x, pred_join(ctx.len())) == Ok::<Truth, SqlError>(truth_of(fj(x))),
{
    let (n, s) = choose|n: Row, s: Row| num_row_ok(n) && sub_row_ok(s) && x == n + s;
    lemma_concat_at(n, s);
    let c = ctx.len() as int;
    let env = ctx + x;
    assert(env[c + 0] == x[0]);
    assert(env[c + 9] == x[9]);
    assert(x[9] == s[0]);
    let (a, b) = (x[0]->Text_0, x[9]->Text_0);
    lemma_lex_cmp_zero(a, b);
    assert(eval_expr(db, env, Expr::Col(ctx.len() + 0)) == Ok::<Val, SqlError>(x[0]));
    assert(eval_expr(db, env, Expr::Col(ctx.len() + 9)) == Ok::<Val, SqlError>(x[9]));
    assert(cmp_truth(CmpOp::Eq, x[0], x[9]) == Ok::<Truth, SqlError>(truth_of(fj(x))));
}

/// `col = 'text'` on a text value.
proof fn lemma_cmp_text(db: Database, env: Row, i: nat, lit: Literal, p0: Seq<u8>)
    requires i < env.len(), env[i as int] is Text, lit == Literal::Text(p0),
    ensures
        eval_pred(db, env, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(i), b: Expr::Lit(lit) })
            == Ok::<Truth, SqlError>(truth_of(env[i as int] == Val::Text(p0))),
{
    lemma_lex_cmp_zero(env[i as int]->Text_0, p0);
    assert(eval_expr(db, env, Expr::Col(i)) == Ok::<Val, SqlError>(env[i as int]));
    assert(eval_expr(db, env, Expr::Lit(lit)) == Ok::<Val, SqlError>(Val::Text(p0)));
}

/// `col = integer` on an integer or NULL value: `Unknown` for NULL.
proof fn lemma_cmp_int(db: Database, env: Row, i: nat, lit: Literal, p1: int)
    requires
        i < env.len(), env[i as int] is Int || env[i as int] is Null,
        lit == (Literal::Int { v: p1, kind: IntKind::Int4 }), int_in_range(IntKind::Int4, p1),
    ensures
        eval_pred(db, env, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(i), b: Expr::Lit(lit) }) is Ok,
        eval_pred(db, env, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(i), b: Expr::Lit(lit) })->Ok_0 is True
            == (env[i as int] == Val::Int(p1)),
{
    assert(eval_expr(db, env, Expr::Col(i)) == Ok::<Val, SqlError>(env[i as int]));
    assert(eval_expr(db, env, Expr::Lit(lit)) == Ok::<Val, SqlError>(Val::Int(p1)));
}

/// `NOT (col IS NULL)` on a non-NULL value.
proof fn lemma_not_null(db: Database, env: Row, i: nat)
    requires i < env.len(), !(env[i as int] is Null),
    ensures eval_pred(db, env, Pred::Not(Box::new(Pred::IsNull(Expr::Col(i))))) == Ok::<Truth, SqlError>(Truth::True),
{
    assert(eval_expr(db, env, Expr::Col(i)) == Ok::<Val, SqlError>(env[i as int]));
    assert(eval_pred(db, env, Pred::IsNull(Expr::Col(i))) == Ok::<Truth, SqlError>(Truth::False));
}

/// `a AND b` of two evaluated conditions.
proof fn lemma_and(db: Database, env: Row, a: Pred, b: Pred)
    requires eval_pred(db, env, a) is Ok, eval_pred(db, env, b) is Ok,
    ensures
        eval_pred(db, env, Pred::And(Box::new(a), Box::new(b)))
            == Ok::<Truth, SqlError>(truth_and(eval_pred(db, env, a)->Ok_0, eval_pred(db, env, b)->Ok_0)),
{
}

/// The WHERE conditions on one joined row: `True` exactly when `fw` holds (`fy` NULL gives `Unknown`).
pub proof fn lemma_pred_where_row(db: Database, p0: Seq<u8>, p1: int, ctx: Row, x: Row)
    requires joined_row_ok(x), int_in_range(IntKind::Int4, p1),
    ensures
        eval_pred(db, ctx + x, pred_where(lits(p0, p1), ctx.len())) is Ok,
        eval_pred(db, ctx + x, pred_where(lits(p0, p1), ctx.len()))->Ok_0 is True == fw(p0, p1, x),
{
    let (n, s) = choose|n: Row, s: Row| num_row_ok(n) && sub_row_ok(s) && x == n + s;
    lemma_concat_at(n, s);
    let c = ctx.len();
    let env = ctx + x;
    let ps = lits(p0, p1);
    assert(env[c as int + 5] == x[5]);
    assert(env[c as int + 19] == x[19]);
    assert(env[c as int + 7] == x[7]);
    assert(x[19] == s[10]);
    assert(ps[0] == Literal::Text(p0));
    assert(ps[1] == Literal::Int { v: p1, kind: IntKind::Int4 });
    let pa = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(c + 5), b: Expr::Lit(ps[0]) };
    let pb = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(c + 19), b: Expr::Lit(ps[1]) };
    let pn = Pred::Not(Box::new(Pred::IsNull(Expr::Col(c + 7))));
    lemma_cmp_text(db, env, c + 5, ps[0], p0);
    lemma_cmp_int(db, env, c + 19, ps[1], p1);
    lemma_not_null(db, env, c + 7);
    lemma_and(db, env, pa, pb);
    let pab = Pred::And(Box::new(pa), Box::new(pb));
    lemma_and(db, env, pab, pn);
    assert(pred_where(ps, c) == Pred::And(Box::new(pab), Box::new(pn)));
}

/// The FROM/WHERE (join, then the conditions) under a context of any length: the joined rows kept by `fq`.
pub proof fn lemma_eval_where(db: Database, p0: Seq<u8>, p1: int, ctx: Row)
    requires rows_ok(db), int_in_range(IntKind::Int4, p1),
    ensures
        eval_query(db, ctx, q_where(lits(p0, p1), ctx.len())) == Ok::<Relation, SqlError>(keep(joined(db), fq_fn(p0, p1))),
{
    let c = ctx.len();
    let rows = joined(db);
    lemma_joined_rows_ok(db);
    lemma_eval_product(db, ctx);
    assert forall|i: int| 0 <= i < rows.len() implies (#[trigger] eval_pred(db, ctx + rows[i], pred_join(c))) is Ok by {
        lemma_pred_join_row(db, ctx, rows[i]);
    }
    assert forall|i: int| 0 <= i < rows.len() implies (#[trigger] eval_pred(db, ctx + rows[i], pred_join(c)))->Ok_0 is True
        == (|x: Row| fj(x))(rows[i]) by {
        lemma_pred_join_row(db, ctx, rows[i]);
    }
    lemma_filter_iff(db, ctx, pred_join(c), q_product(), rows, |x: Row| fj(x));
    let k1 = keep(rows, |x: Row| fj(x));
    lemma_keep_members(rows, |x: Row| fj(x));
    assert forall|i: int| 0 <= i < k1.len() implies joined_row_ok(#[trigger] k1[i]) by {
        assert(rows.contains(k1[i]));
    }
    let ps = lits(p0, p1);
    assert forall|i: int| 0 <= i < k1.len() implies (#[trigger] eval_pred(db, ctx + k1[i], pred_where(ps, c))) is Ok by {
        lemma_pred_where_row(db, p0, p1, ctx, k1[i]);
    }
    assert forall|i: int| 0 <= i < k1.len() implies (#[trigger] eval_pred(db, ctx + k1[i], pred_where(ps, c)))->Ok_0 is True
        == (|x: Row| fw(p0, p1, x))(k1[i]) by {
        lemma_pred_where_row(db, p0, p1, ctx, k1[i]);
    }
    lemma_filter_iff(db, ctx, pred_where(ps, c), q_join(c), k1, |x: Row| fw(p0, p1, x));
    lemma_keep_keep(rows, |x: Row| fj(x), |x: Row| fw(p0, p1, x));
    lemma_keep_ext(rows, |x: Row| (|x: Row| fj(x))(x) && (|x: Row| fw(p0, p1, x))(x), fq_fn(p0, p1));
}

// ------------------------------------------------------------------------------------------- group accumulators

/// The outer query's grouping: key `(name, cik)`, `SUM(value)` at scale 4.
pub open spec fn g_top(p0: Seq<u8>, p1: int) -> QuerySpec {
    QuerySpec {
        qual: fq_fn(p0, p1),
        key: |x: Row| seq![x[11], x[10]],
        arg: |j: int, x: Row| coeff(x[7]),
        aggs: seq![AggKind::Sum { scale: 4 }],
        outs: seq![0nat, 1, 2],
        grouped: true,
    }
}

/// The subquery's grouping: key `(cik)`, `SUM(value)` at scale 4.
pub open spec fn g_cik(p0: Seq<u8>, p1: int) -> QuerySpec {
    QuerySpec {
        qual: fq_fn(p0, p1),
        key: |x: Row| seq![x[10]],
        arg: |j: int, x: Row| coeff(x[7]),
        aggs: seq![AggKind::Sum { scale: 4 }],
        outs: seq![0nat, 1],
        grouped: true,
    }
}

/// Group keys as functions of the `sub` row.
pub open spec fn key_top_s(s: Row) -> Row {
    seq![s[2], s[1]]
}

pub open spec fn key_cik_s(s: Row) -> Row {
    seq![s[1]]
}

/// `s.fy = $2`.
pub open spec fn sq(p1: int, s: Row) -> bool {
    s[10] == Val::Int(p1)
}

/// `n.adsh = s.adsh AND n.uom = $1`.
pub open spec fn nmatch(p0: Seq<u8>, n: Row, s: Row) -> bool {
    n[0] == s[0] && n[5] == Val::Text(p0)
}

/// Per-row weights of a `num` row: its value coefficient, its absolute value, one.
pub open spec fn w_val() -> spec_fn(Row) -> int {
    |n: Row| coeff(n[7])
}

pub open spec fn w_abs() -> spec_fn(Row) -> int {
    |n: Row| abs(coeff(n[7]))
}

pub open spec fn w_one() -> spec_fn(Row) -> int {
    |n: Row| 1int
}

/// The per-filing sum: `w` over the `num` rows of filing `s` with unit `$1`.
pub open spec fn fsum(p0: Seq<u8>, nrel: Seq<Row>, s: Row, w: spec_fn(Row) -> int) -> int {
    sum_of(nrel, |n: Row| if nmatch(p0, n, s) { w(n) } else { 0int })
}

/// Term of a `sub` row in `by_sub`.
pub open spec fn sub_term(p1: int, p0: Seq<u8>, nrel: Seq<Row>, ks: spec_fn(Row) -> Row, k: Row,
    w: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |s: Row| if sq(p1, s) && ks(s) == k { fsum(p0, nrel, s, w) } else { 0int }
}

/// A group accumulator over the qualifying joined rows, as a sum over `sub` rows of the per-filing sums.
pub open spec fn by_sub(p1: int, p0: Seq<u8>, nrel: Seq<Row>, srel: Seq<Row>, ks: spec_fn(Row) -> Row, k: Row,
    w: spec_fn(Row) -> int) -> int {
    sum_of(srel, sub_term(p1, p0, nrel, ks, k, w))
}

/// Decomposition: a per-row term over the joined rows that is `w(n)` on qualifying rows of key `k` (the key a
/// function `ks` of the `sub` part) and 0 elsewhere sums to `by_sub`.
pub proof fn lemma_dec(db: Database, p0: Seq<u8>, p1: int, kx: spec_fn(Row) -> Row, ks: spec_fn(Row) -> Row, k: Row,
    w: spec_fn(Row) -> int, t: spec_fn(Row) -> int)
    requires
        rows_ok(db),
        forall|n: Row, s: Row| num_row_ok(n) && sub_row_ok(s) ==> #[trigger] kx(n + s) == ks(s),
        forall|n: Row, s: Row| num_row_ok(n) && sub_row_ok(s) ==>
            #[trigger] t(n + s) == if fq(p0, p1, n + s) && kx(n + s) == k { w(n) } else { 0int },
    ensures
        sum_of(joined(db), t) == by_sub(p1, p0, num_rel(db), sub_rel(db), ks, k, w),
{
    let (nr, sr) = (num_rel(db), sub_rel(db));
    lemma_sum_of_product_swap(nr, sr, t);
    let inner = |y: Row| sum_of(nr, |x: Row| t(x + y));
    let target = sub_term(p1, p0, nr, ks, k, w);
    assert forall|j: int| 0 <= j < sr.len() implies inner(#[trigger] sr[j]) == target(sr[j]) by {
        let s = sr[j];
        assert(sub_row_ok(s));
        let tx = |x: Row| t(x + s);
        let mx = |n: Row| if nmatch(p0, n, s) { w(n) } else { 0int };
        if sq(p1, s) && ks(s) == k {
            assert forall|i: int| 0 <= i < nr.len() implies tx(#[trigger] nr[i]) == mx(nr[i]) by {
                let n = nr[i];
                assert(num_row_ok(n));
                lemma_concat_at(n, s);
                assert((n + s)[9int] == s[0]);
                assert((n + s)[19int] == s[10]);
            }
            lemma_sum_of_ext(nr, tx, mx);
        } else {
            assert forall|i: int| 0 <= i < nr.len() implies tx(#[trigger] nr[i]) == 0 by {
                let n = nr[i];
                assert(num_row_ok(n));
                lemma_concat_at(n, s);
                assert((n + s)[19int] == s[10]);
            }
            lemma_sum_of_zero(nr, tx);
        }
    }
    crate::link::join::lemma_sum_of_ext(sr, inner, target);
    assert(sum_of(joined(db), t) == sum_of(sr, inner));
    assert(sum_of(sr, inner) == sum_of(sr, target));
    assert(by_sub(p1, p0, nr, sr, ks, k, w) == sum_of(sr, target));
}

/// The outer grouping's key is the `sub` row's `(name, cik)`.
pub proof fn lemma_top_key(p0: Seq<u8>, p1: int)
    ensures forall|n: Row, s: Row| num_row_ok(n) && sub_row_ok(s) ==> #[trigger] (g_top(p0, p1).key)(n + s) == key_top_s(s),
{
    assert forall|n: Row, s: Row| num_row_ok(n) && sub_row_ok(s) implies #[trigger] (g_top(p0, p1).key)(n + s) == key_top_s(s) by {
        lemma_concat_at(n, s);
        assert((n + s)[11int] == s[2]);
        assert((n + s)[10int] == s[1]);
        assert((g_top(p0, p1).key)(n + s) =~= key_top_s(s));
    }
}

/// The subquery's grouping key is the `sub` row's `(cik)`.
pub proof fn lemma_cik_key(p0: Seq<u8>, p1: int)
    ensures forall|n: Row, s: Row| num_row_ok(n) && sub_row_ok(s) ==> #[trigger] (g_cik(p0, p1).key)(n + s) == key_cik_s(s),
{
    assert forall|n: Row, s: Row| num_row_ok(n) && sub_row_ok(s) implies #[trigger] (g_cik(p0, p1).key)(n + s) == key_cik_s(s) by {
        lemma_concat_at(n, s);
        assert((n + s)[10int] == s[1]);
        assert((g_cik(p0, p1).key)(n + s) =~= key_cik_s(s));
    }
}

/// `gsum`, `gabs` and `gcount` of a grouping whose key depends on the `sub` row, as sums over `sub` rows.
pub proof fn lemma_acc_by_sub(db: Database, p0: Seq<u8>, p1: int, g: QuerySpec, ks: spec_fn(Row) -> Row, k: Row)
    requires
        rows_ok(db),
        g.qual == fq_fn(p0, p1),
        g.arg == (|j: int, x: Row| coeff(x[7])),
        forall|n: Row, s: Row| num_row_ok(n) && sub_row_ok(s) ==> #[trigger] (g.key)(n + s) == ks(s),
    ensures
        gsum(g, joined(db), k, 0) == by_sub(p1, p0, num_rel(db), sub_rel(db), ks, k, w_val()),
        gabs(g, joined(db), k, 0) == by_sub(p1, p0, num_rel(db), sub_rel(db), ks, k, w_abs()),
        gcount(g, joined(db), k) == by_sub(p1, p0, num_rel(db), sub_rel(db), ks, k, w_one()),
{
    let x = joined(db);
    lemma_acc_sum_of(g, x, k, 0);
    assert forall|n: Row, s: Row| num_row_ok(n) && sub_row_ok(s) implies
        #[trigger] sum_term(g, k, 0)(n + s) == if fq(p0, p1, n + s) && (g.key)(n + s) == k { w_val()(n) } else { 0int } by {
        lemma_concat_at(n, s);
        assert((n + s)[7] == n[7]);
    }
    lemma_dec(db, p0, p1, g.key, ks, k, w_val(), sum_term(g, k, 0));
    assert forall|n: Row, s: Row| num_row_ok(n) && sub_row_ok(s) implies
        #[trigger] abs_term(g, k, 0)(n + s) == if fq(p0, p1, n + s) && (g.key)(n + s) == k { w_abs()(n) } else { 0int } by {
        lemma_concat_at(n, s);
        assert((n + s)[7] == n[7]);
    }
    lemma_dec(db, p0, p1, g.key, ks, k, w_abs(), abs_term(g, k, 0));
    assert forall|n: Row, s: Row| num_row_ok(n) && sub_row_ok(s) implies
        #[trigger] count_term(g, k)(n + s) == if fq(p0, p1, n + s) && (g.key)(n + s) == k { w_one()(n) } else { 0int } by {
    }
    lemma_dec(db, p0, p1, g.key, ks, k, w_one(), count_term(g, k));
}

} // verus!
