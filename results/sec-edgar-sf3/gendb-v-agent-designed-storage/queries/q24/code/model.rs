//! The statement's meaning in a normal form over the `num` and `pre` tables.
//!
//! The SQL body is `HAVING(GROUP BY(WHERE(num LEFT JOIN pre)))`. A joined row is a num row (positions 0..9)
//! followed by a pre row (positions 9..19) or ten NULLs. `p.adsh IS NULL` keeps exactly the NULL-padded rows of num
//! rows without a matching pre row (a matched pre row has a non-NULL adsh), so the WHERE + GROUP BY accumulators over
//! the joined rows (`lj_spec`) equal those of the anti-join over the num rows (`num_spec`): per group key
//! (tag, version), the number and the value sum of the num rows that pass the num conditions and have no pre row with
//! the same (adsh, tag, version). `lemma_body` states the whole body: the HAVING rows of the groups in
//! first-occurrence order.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::int::*;
use crate::spec::numeric::abs;
use crate::spec::equality::row_not_distinct;
use crate::link::query::{QuerySpec, AggKind, hit, gcount, gsum, gabs, gkeys, full_row, agg_outs, lemma_append,
    lemma_one_row, lemma_push, lemma_gkeys_witness};
use crate::link::join::{keep, lemma_keep_true_keep};
use crate::link::expr::{lemma_pred_text_cmp, lemma_pred_cmp, lemma_pred_and, lemma_pred_not, lemma_compare_int, int_cmp,
    text_cmp};
use crate::link::query::{proj, proj_all, select, col_exprs, lemma_eval_cols, pred_agrees, keys_agree, args_agree,
    aggs_match, keys_exact, group_caps, arg_vals, lemma_group_query, lemma_filter_rows, qual_truths, lemma_row_exact};
use crate::bridge::collect::lemma_collect_all;
use crate::bridge::relation::{lemma_left_join_rows_elems, is_concat, is_padded};
use crate::exec::relational::domain::{lemma_eval_filter, lemma_eval_left_join, left_join_results, filter_results};
use crate::spec::order::denote_body;
use crate::query::{query_spec_at, param_domain};

verus! {

// ------------------------------------------------------------------------------------------------- parameters

/// `$1` (uom), `$2` and `$3` (ddate bounds) of a binding.
pub open spec fn ukey(ps: Seq<Literal>) -> Seq<u8> {
    match ps[0] {
        Literal::Text(b) => b,
        _ => Seq::empty(),
    }
}

pub open spec fn dlo(ps: Seq<Literal>) -> int {
    match ps[1] {
        Literal::Int { v, .. } => v,
        _ => 0,
    }
}

pub open spec fn dhi(ps: Seq<Literal>) -> int {
    match ps[2] {
        Literal::Int { v, .. } => v,
        _ => 0,
    }
}

// ------------------------------------------------------------------------------------------ row conditions

/// An integer value inside `[lo, hi]`.
pub open spec fn date_in(v: Val, lo: int, hi: int) -> bool {
    match v {
        Val::Int(d) => lo <= d && d <= hi,
        _ => false,
    }
}

/// The WHERE conditions on the num columns: `uom = $1`, `ddate BETWEEN $2 AND $3`, `value IS NOT NULL`.
pub open spec fn num_where(ps: Seq<Literal>, x: Row) -> bool {
    &&& x[5] == Val::Text(ukey(ps))
    &&& date_in(x[3], dlo(ps), dhi(ps))
    &&& !(x[7] is Null)
}

/// Pre row `y` matches num row `x` on (adsh, tag, version).
pub open spec fn pre_matches(x: Row, y: Row) -> bool {
    &&& y[0] == x[0]
    &&& y[6] == x[1]
    &&& y[7] == x[2]
}

/// Some pre row matches `x`.
pub open spec fn has_pre(pre: Seq<Row>, x: Row) -> bool {
    exists|j: int| 0 <= j < pre.len() && pre_matches(x, #[trigger] pre[j])
}

/// The group key (tag, version).
pub open spec fn key2(x: Row) -> Row {
    seq![x[1], x[2]]
}

/// The SUM argument: the coefficient of `value` (scale 4).
pub open spec fn coeff7(j: int, x: Row) -> int {
    match x[7] {
        Val::Num { coeff, .. } => coeff,
        _ => 0,
    }
}

pub open spec fn aggs_nf() -> Seq<AggKind> {
    seq![AggKind::Count, AggKind::Sum { scale: 4 }]
}

pub open spec fn outs_nf() -> Seq<nat> {
    seq![0nat, 1, 2, 3]
}

/// WHERE + GROUP BY over the joined rows.
pub open spec fn lj_spec(ps: Seq<Literal>) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| num_where(ps, x) && x[9] is Null,
        key: |x: Row| key2(x),
        arg: |j: int, x: Row| coeff7(j, x),
        aggs: aggs_nf(),
        outs: outs_nf(),
        grouped: true,
    }
}

/// The anti-join over the num rows.
pub open spec fn num_spec(ps: Seq<Literal>, pre: Seq<Row>) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| num_where(ps, x) && !has_pre(pre, x),
        key: |x: Row| key2(x),
        arg: |j: int, x: Row| coeff7(j, x),
        aggs: aggs_nf(),
        outs: outs_nf(),
        grouped: true,
    }
}

// --------------------------------------------------------------------------------------------- the left join

/// The ON condition's truth for every (num row, pre row).
pub open spec fn on_truths(l: Seq<Row>, r: Seq<Row>) -> Seq<Seq<Truth>> {
    Seq::new(l.len(), |i: int| Seq::new(r.len(), |j: int| truth_of(pre_matches(l[i], r[j]))))
}

/// The ON truths of one num row.
pub open spec fn on_row(x: Row, r: Seq<Row>) -> Seq<Truth> {
    Seq::new(r.len(), |j: int| truth_of(pre_matches(x, r[j])))
}

/// The joined rows `num LEFT JOIN pre`.
pub open spec fn lj_rows(l: Seq<Row>, r: Seq<Row>) -> Seq<Row> {
    left_join_rows(l, r, on_truths(l, r), 10)
}

/// Shape of a num row: 9 columns, the read ones non-NULL of their types.
pub open spec fn num_row_ok(x: Row) -> bool {
    &&& x.len() == 9
    &&& x[0] is Text && x[1] is Text && x[2] is Text
    &&& x[3] is Int
    &&& x[5] is Text
    &&& x[7] is Num && x[7]->Num_scale == 4
}

/// Shape of a pre row: 10 columns, adsh, tag and version non-NULL text.
pub open spec fn pre_row_ok(y: Row) -> bool {
    &&& y.len() == 10
    &&& y[0] is Text && y[6] is Text && y[7] is Text
}

pub open spec fn nums_ok(l: Seq<Row>) -> bool {
    forall|i: int| 0 <= i < l.len() ==> num_row_ok(#[trigger] l[i])
}

pub open spec fn pres_ok(r: Seq<Row>) -> bool {
    forall|j: int| 0 <= j < r.len() ==> pre_row_ok(#[trigger] r[j])
}

/// `keep_true` of the ON truths of `x` is empty exactly when no pre row matches.
proof fn lemma_matched_empty(x: Row, r: Seq<Row>)
    ensures (keep_true(r, on_row(x, r)).len() == 0) == !has_pre(r, x),
{
    let f = |y: Row| pre_matches(x, y);
    crate::link::join::lemma_keep_true_keep(r, on_row(x, r), f);
    crate::link::join::lemma_keep_members(r, f);
    if has_pre(r, x) {
        let j = choose|j: int| 0 <= j < r.len() && pre_matches(x, #[trigger] r[j]);
        lemma_keep_nonempty(r, f, j);
    } else if keep(r, f).len() > 0 {
        let y = keep(r, f)[0];
        assert(r.contains(y) && f(y));
        let j = choose|j: int| 0 <= j < r.len() && r[j] == y;
        assert(pre_matches(x, r[j]));
    }
}

/// A row satisfying the condition makes `keep` non-empty.
proof fn lemma_keep_nonempty(rows: Seq<Row>, f: spec_fn(Row) -> bool, j: int)
    requires 0 <= j < rows.len(), f(rows[j]),
    ensures keep(rows, f).len() > 0,
    decreases rows.len(),
{
    if j == rows.len() - 1 {
        assert(rows.last() == rows[j]);
    } else {
        lemma_keep_nonempty(rows.drop_last(), f, j);
    }
}

/// Accumulators of a sequence on which no row hits are zero.
proof fn lemma_no_hits(g: QuerySpec, rows: Seq<Row>, k: Row, j: int)
    requires forall|m: int| 0 <= m < rows.len() ==> !hit(g, #[trigger] rows[m], k),
    ensures gcount(g, rows, k) == 0, gsum(g, rows, k, j) == 0, gabs(g, rows, k, j) == 0,
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        assert forall|m: int| 0 <= m < ri.len() implies !hit(g, #[trigger] ri[m], k) by {
            assert(ri[m] == rows[m]);
        }
        lemma_no_hits(g, ri, k, j);
        assert(!hit(g, rows[rows.len() - 1], k));
    }
}

/// The joined rows of one num row contribute what that num row contributes to the anti-join.
proof fn lemma_join_one(ps: Seq<Literal>, x: Row, r: Seq<Row>, k: Row, j: int)
    requires num_row_ok(x), pres_ok(r),
    ensures ({
        let one = left_join_one(x, r, on_row(x, r), 10);
        let (g, h) = (lj_spec(ps), num_spec(ps, r));
        &&& gcount(g, one, k) == if hit(h, x, k) { 1nat } else { 0nat }
        &&& gsum(g, one, k, j) == if hit(h, x, k) { (h.arg)(j, x) } else { 0 }
        &&& gabs(g, one, k, j) == if hit(h, x, k) { abs((h.arg)(j, x)) } else { 0 }
    }),
{
    let (g, h) = (lj_spec(ps), num_spec(ps, r));
    let t = on_row(x, r);
    let matched = keep_true(r, t);
    lemma_matched_empty(x, r);
    if matched.len() == 0 {
        let w = x + null_row(10);
        assert(left_join_one(x, r, t, 10) == seq![w]);
        lemma_one_row(g, w, k, j);
        assert(w[1] == x[1] && w[2] == x[2] && w[3] == x[3] && w[5] == x[5] && w[7] == x[7]);
        assert(w[9] == Val::Null);
        assert(key2(w) =~= key2(x));
    } else {
        let one = left_join_one(x, r, t, 10);
        assert(one == matched.map_values(|y: Row| x + y));
        crate::bridge::relation::lemma_keep_true_sub(r, t);
        assert forall|m: int| 0 <= m < one.len() implies !hit(g, #[trigger] one[m], k) by {
            assert(one[m] == x + matched[m]);
            assert(r.contains(matched[m]));
            let jj = choose|jj: int| 0 <= jj < r.len() && r[jj] == matched[m];
            assert(pre_row_ok(r[jj]));
            assert((x + matched[m])[9] == matched[m][0]);
        }
        lemma_no_hits(g, one, k, j);
    }
}

/// WHERE + GROUP BY accumulators over `num LEFT JOIN pre` are those of the anti-join over num.
pub proof fn lemma_lj_acc(ps: Seq<Literal>, l: Seq<Row>, r: Seq<Row>, k: Row, j: int)
    requires nums_ok(l), pres_ok(r),
    ensures
        gcount(lj_spec(ps), lj_rows(l, r), k) == gcount(num_spec(ps, r), l, k),
        gsum(lj_spec(ps), lj_rows(l, r), k, j) == gsum(num_spec(ps, r), l, k, j),
        gabs(lj_spec(ps), lj_rows(l, r), k, j) == gabs(num_spec(ps, r), l, k, j),
    decreases l.len(),
{
    let (g, h) = (lj_spec(ps), num_spec(ps, r));
    if l.len() > 0 {
        let li = l.drop_last();
        let x = l.last();
        assert forall|i: int| 0 <= i < li.len() implies num_row_ok(#[trigger] li[i]) by {
            assert(li[i] == l[i]);
        }
        lemma_lj_acc(ps, li, r, k, j);
        assert(on_truths(l, r).drop_last() =~= on_truths(li, r));
        assert(on_truths(l, r).last() =~= on_row(x, r));
        assert(lj_rows(l, r) == lj_rows(li, r) + left_join_one(x, r, on_row(x, r), 10));
        lemma_append(g, lj_rows(li, r), left_join_one(x, r, on_row(x, r), 10), k, j);
        assert(num_row_ok(l[l.len() - 1]));
        lemma_join_one(ps, x, r, k, j);
        assert(l == li.push(x));
        lemma_push(h, li, x, k, j);
    } else {
        assert(lj_rows(l, r).len() == 0);
    }
}


// ----------------------------------------------------------------------------------------------- the AST

pub open spec fn where_pred(ps: Seq<Literal>) -> Pred {
    Pred::And(
        Box::new(Pred::And(
            Box::new(Pred::And(
                Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(5), b: Expr::Lit(ps[0]) }),
                Box::new(Pred::And(
                    Box::new(Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(3), b: Expr::Lit(ps[1]) }),
                    Box::new(Pred::Cmp { op: CmpOp::Le, a: Expr::Col(3), b: Expr::Lit(ps[2]) }),
                )),
            )),
            Box::new(Pred::Not(Box::new(Pred::IsNull(Expr::Col(7))))),
        )),
        Box::new(Pred::IsNull(Expr::Col(9))),
    )
}

pub open spec fn on_pred() -> Pred {
    Pred::And(
        Box::new(Pred::And(
            Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(1), b: Expr::Col(15) }),
            Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(2), b: Expr::Col(16) }),
        )),
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) }),
    )
}

pub open spec fn having_pred() -> Pred {
    Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(2), b: Expr::Lit(Literal::Int { v: 10, kind: IntKind::Int4 }) }
}

pub open spec fn lj_query() -> Query {
    Query::LeftJoin { left: Box::new(Query::Table(1)), right: Box::new(Query::Table(3)), on: on_pred() }
}

pub open spec fn where_query(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: where_pred(ps), input: Box::new(lj_query()) }
}

pub open spec fn gb_keys() -> Seq<Expr> {
    seq![Expr::Col(1), Expr::Col(2)]
}

pub open spec fn gb_aggs() -> Seq<Agg> {
    seq![Agg::CountStar, Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(7) }]
}

pub open spec fn gb_query(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: gb_keys(), aggs: gb_aggs(), input: Box::new(where_query(ps)) }
}

pub open spec fn body_query(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: having_pred(), input: Box::new(gb_query(ps)) }
}

/// The statement is the AST above, ordered by `cnt DESC`, LIMIT 100.
pub proof fn lemma_statement(ps: Seq<Literal>)
    ensures
        query_spec_at(ps).body == body_query(ps),
        query_spec_at(ps).keys == seq![OrderKey { col: 2, desc: true, nulls_first: true }],
        query_spec_at(ps).limit == Some(100nat),
        query_spec_at(ps).offset == 0,
{
    assert(gb_keys() =~= seq![Expr::Col(1), Expr::Col(2)]);
}

// ----------------------------------------------------------------------------------- per-row evaluations

/// The ON condition on `x ++ y` is `pre_matches(x, y)`.
proof fn lemma_on_eval(db: Database, x: Row, y: Row)
    requires num_row_ok(x), pre_row_ok(y),
    ensures eval_pred(db, Seq::<Val>::empty() + x + y, on_pred()) == Ok::<Truth, SqlError>(truth_of(pre_matches(x, y))),
{
    let env = Seq::<Val>::empty() + x + y;
    assert(env.len() == 19);
    assert(env[1] == x[1] && env[2] == x[2] && env[0] == x[0]);
    assert(env[15] == y[6] && env[16] == y[7] && env[9] == y[0]);
    let (a1, a2, a0) = (x[1]->Text_0, x[2]->Text_0, x[0]->Text_0);
    let (b6, b7, b0) = (y[6]->Text_0, y[7]->Text_0, y[0]->Text_0);
    lemma_pred_text_cmp(db, env, CmpOp::Eq, Expr::Col(1), Expr::Col(15), a1, b6);
    lemma_pred_text_cmp(db, env, CmpOp::Eq, Expr::Col(2), Expr::Col(16), a2, b7);
    lemma_pred_text_cmp(db, env, CmpOp::Eq, Expr::Col(0), Expr::Col(9), a0, b0);
    let p1 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(1), b: Expr::Col(15) };
    let p2 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(2), b: Expr::Col(16) };
    let p3 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) };
    lemma_pred_and(db, env, p1, p2, a1 == b6, a2 == b7);
    lemma_pred_and(db, env, Pred::And(Box::new(p1), Box::new(p2)), p3, a1 == b6 && a2 == b7, a0 == b0);
}

/// Evaluating `num LEFT JOIN pre` gives `lj_rows`.
proof fn lemma_lj_eval(db: Database, l: Seq<Row>, r: Seq<Row>)
    requires
        db.tables.len() == 4,
        db.tables[1] == l,
        db.tables[3] == r,
        nums_ok(l), pres_ok(r),
        query_arity(db.schema, Query::Table(3)) == 10,
    ensures eval_query(db, Seq::empty(), lj_query()) == Ok::<Relation, SqlError>(lj_rows(l, r)),
{
    let ctx = Seq::<Val>::empty();
    lemma_eval_left_join(db, ctx, Box::new(Query::Table(1)), Box::new(Query::Table(3)), on_pred());
    let lr = left_join_results(db, ctx, l, r, on_pred());
    let tr = on_truths(l, r);
    assert forall|i: int| 0 <= i < lr.len() implies #[trigger] lr[i] == Ok::<Seq<Truth>, SqlError>(tr[i]) by {
        let inner = Seq::new(r.len(), |j: int| eval_pred(db, ctx + l[i] + r[j], on_pred()));
        assert forall|j: int| 0 <= j < inner.len() implies #[trigger] inner[j] == Ok::<Truth, SqlError>(tr[i][j]) by {
            assert(num_row_ok(l[i]) && pre_row_ok(r[j]));
            lemma_on_eval(db, l[i], r[j]);
        }
        lemma_collect_all(inner, tr[i]);
    }
    lemma_collect_all(lr, tr);
}

/// `x ++ y` (or `x ++ NULLs`) of a joined row: its num part is `x`, position 9 is `y[0]` (or NULL).
pub open spec fn joined_ok(z: Row) -> bool {
    &&& z.len() == 19
    &&& num_row_ok(z.subrange(0, 9))
    &&& (z[9] is Null || z[9] is Text)
}

/// Every joined row has the shape `joined_ok`.
proof fn lemma_lj_shape(l: Seq<Row>, r: Seq<Row>)
    requires nums_ok(l), pres_ok(r),
    ensures forall|m: int| 0 <= m < lj_rows(l, r).len() ==> joined_ok(#[trigger] lj_rows(l, r)[m]),
{
    lemma_left_join_rows_elems(l, r, on_truths(l, r), 10);
    let s = lj_rows(l, r);
    assert forall|m: int| 0 <= m < s.len() implies joined_ok(#[trigger] s[m]) by {
        if is_concat(s[m], l, r) {
            let (i, j) = choose|i: int, j: int| 0 <= i < l.len() && 0 <= j < r.len() && s[m] == #[trigger] l[i] + #[trigger] r[j];
            assert(num_row_ok(l[i]) && pre_row_ok(r[j]));
            assert(s[m].subrange(0, 9) =~= l[i]);
        } else {
            let i = choose|i: int| 0 <= i < l.len() && s[m] == #[trigger] l[i] + null_row(10);
            assert(num_row_ok(l[i]));
            assert(s[m].subrange(0, 9) =~= l[i]);
        }
    }
}

/// `IS NULL` of a column is two-valued.
proof fn lemma_isnull_eval(db: Database, z: Row, i: nat)
    requires i < z.len(),
    ensures eval_pred(db, z, Pred::IsNull(Expr::Col(i))) == Ok::<Truth, SqlError>(truth_of(z[i as int] is Null)),
{
    crate::link::expr::lemma_expr_col(db, z, i);
}

/// The parameter literals evaluate to their values.
proof fn lemma_params_lit(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures
        ps[0] == Literal::Text(ukey(ps)),
        ps[1] == (Literal::Int { v: dlo(ps), kind: IntKind::Int4 }),
        ps[2] == (Literal::Int { v: dhi(ps), kind: IntKind::Int4 }),
        lit_val(ps[1]) == Ok::<Val, SqlError>(Val::Int(dlo(ps))),
        lit_val(ps[2]) == Ok::<Val, SqlError>(Val::Int(dhi(ps))),
{
}

/// `ddate BETWEEN $2 AND $3` on a joined row.
proof fn lemma_date_eval(db: Database, ps: Seq<Literal>, z: Row)
    requires z.len() == 19, z[3] is Int, param_domain(ps),
    ensures ({
        let cge = Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(3), b: Expr::Lit(ps[1]) };
        let cle = Pred::Cmp { op: CmpOp::Le, a: Expr::Col(3), b: Expr::Lit(ps[2]) };
        eval_pred(db, z, Pred::And(Box::new(cge), Box::new(cle)))
            == Ok::<Truth, SqlError>(truth_of(date_in(z[3], dlo(ps), dhi(ps))))
    }),
{
    hide(eval_pred);
    lemma_params_lit(ps);
    let d = z[3]->Int_0;
    let (lo, hi) = (dlo(ps), dhi(ps));
    let cge = Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(3), b: Expr::Lit(ps[1]) };
    let cle = Pred::Cmp { op: CmpOp::Le, a: Expr::Col(3), b: Expr::Lit(ps[2]) };
    lemma_compare_int(d, lo);
    lemma_compare_int(d, hi);
    lemma_pred_cmp(db, z, CmpOp::Ge, Expr::Col(3), Expr::Lit(ps[1]), Val::Int(d), Val::Int(lo), d, lo);
    lemma_pred_cmp(db, z, CmpOp::Le, Expr::Col(3), Expr::Lit(ps[2]), Val::Int(d), Val::Int(hi), d, hi);
    lemma_pred_and(db, z, cge, cle, d >= lo, d <= hi);
}

/// The WHERE condition on a joined row is `lj_spec`'s qualification.
proof fn lemma_where_eval(db: Database, ps: Seq<Literal>, z: Row)
    requires joined_ok(z), param_domain(ps),
    ensures eval_pred(db, z, where_pred(ps)) == Ok::<Truth, SqlError>(truth_of((lj_spec(ps).qual)(z))),
{
    hide(eval_pred);
    let x = z.subrange(0, 9);
    assert(z[5] == x[5] && z[3] == x[3] && z[7] == x[7]);
    lemma_params_lit(ps);
    let u = ukey(ps);
    let s5 = z[5]->Text_0;
    let c5 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(5), b: Expr::Lit(ps[0]) };
    let cge = Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(3), b: Expr::Lit(ps[1]) };
    let cle = Pred::Cmp { op: CmpOp::Le, a: Expr::Col(3), b: Expr::Lit(ps[2]) };
    let cdate = Pred::And(Box::new(cge), Box::new(cle));
    let n7 = Pred::Not(Box::new(Pred::IsNull(Expr::Col(7))));
    let n9 = Pred::IsNull(Expr::Col(9));
    let din = date_in(z[3], dlo(ps), dhi(ps));
    lemma_pred_text_cmp(db, z, CmpOp::Eq, Expr::Col(5), Expr::Lit(ps[0]), s5, u);
    lemma_date_eval(db, ps, z);
    lemma_pred_and(db, z, c5, cdate, s5 == u, din);
    lemma_isnull_eval(db, z, 7);
    lemma_pred_not(db, z, Pred::IsNull(Expr::Col(7)), false);
    let c3 = Pred::And(Box::new(c5), Box::new(cdate));
    lemma_pred_and(db, z, c3, n7, s5 == u && din, true);
    lemma_isnull_eval(db, z, 9);
    let c4 = Pred::And(Box::new(c3), Box::new(n7));
    lemma_pred_and(db, z, c4, n9, s5 == u && din && true, z[9] is Null);
    assert((z[5] == Val::Text(u)) == (s5 == u));
    assert(where_pred(ps) == Pred::And(Box::new(c4), Box::new(n9)));
}


// ------------------------------------------------------------------------------------ GROUP BY and HAVING

pub open spec fn ident19() -> Seq<nat> {
    Seq::new(19, |i: int| i as nat)
}

proof fn lemma_proj_ident(z: Row)
    requires z.len() == 19,
    ensures proj(z, ident19()) == z,
{
    assert(proj(z, ident19()) =~= z);
}

proof fn lemma_proj_all_ident(rows: Seq<Row>)
    requires forall|m: int| 0 <= m < rows.len() ==> (#[trigger] rows[m]).len() == 19,
    ensures proj_all(rows, ident19()) == rows,
{
    assert forall|m: int| 0 <= m < rows.len() implies #[trigger] proj_all(rows, ident19())[m] == rows[m] by {
        lemma_proj_ident(rows[m]);
    }
    assert(proj_all(rows, ident19()) =~= rows);
}

/// HAVING `COUNT(*) > 10` on a GROUP BY row (count at position 2).
pub open spec fn having_ok(r: Row) -> bool {
    match r[2] {
        Val::Int(c) => c > 10,
        _ => false,
    }
}

/// The GROUP BY rows of the statement, in first-occurrence order.
pub open spec fn gb_rows(ps: Seq<Literal>, l: Seq<Row>, r: Seq<Row>) -> Seq<Row> {
    let xs = lj_rows(l, r);
    gkeys(lj_spec(ps), xs).map_values(|k: Row| full_row(lj_spec(ps), xs, k))
}

/// The aggregate arguments of a joined row.
proof fn lemma_args_eval(db: Database, ps: Seq<Literal>, z: Row)
    requires joined_ok(z),
    ensures agg_args(db, z, gb_aggs()) == Ok::<Row, SqlError>(arg_vals(lj_spec(ps), z)),
{
    hide(eval_expr);
    let g = lj_spec(ps);
    let aggs = gb_aggs();
    let rs = agg_arg_results(db, z, aggs);
    let vs = arg_vals(g, z);
    assert(z[7] == z.subrange(0, 9)[7]);
    let c = z[7]->Num_coeff;
    assert(z[7] == Val::Num { coeff: c, scale: 4 });
    crate::link::expr::lemma_expr_col(db, z, 7);
    assert(agg_arg(db, z, aggs[0]) == Ok::<Val, SqlError>(Val::Null));
    assert(agg_arg(db, z, aggs[1]) == eval_expr(db, z, Expr::Col(7)));
    assert(rs.len() == 2 && vs.len() == 2);
    assert(rs[0] == agg_arg(db, z, aggs[0]));
    assert(rs[1] == agg_arg(db, z, aggs[1]));
    assert(vs[0] == Val::Null);
    assert(vs[1] == Val::Num { coeff: c, scale: 4 });
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Val, SqlError>(vs[i]) by {
        if i == 0 {
        } else {
            assert(i == 1);
        }
    }
    lemma_collect_all(rs, vs);
}

/// The key expressions of a joined row.
proof fn lemma_keys_eval(db: Database, z: Row)
    requires z.len() == 19,
    ensures eval_exprs(db, z, gb_keys()) == Ok::<Row, SqlError>(key2(z)),
{
    let idxs = seq![1nat, 2nat];
    lemma_eval_cols(db, z, idxs);
    assert(col_exprs(idxs) =~= gb_keys());
    assert(select(z, idxs) =~= key2(z));
}

/// HAVING over the GROUP BY rows.
proof fn lemma_having_eval(db: Database, ps: Seq<Literal>, l: Seq<Row>, r: Seq<Row>)
    requires eval_query(db, Seq::empty(), gb_query(ps)) == Ok::<Relation, SqlError>(gb_rows(ps, l, r)),
    ensures
        eval_query(db, Seq::empty(), body_query(ps))
            == Ok::<Relation, SqlError>(keep(gb_rows(ps, l, r), |row: Row| having_ok(row))),
{
    let ctx = Seq::<Val>::empty();
    let g = lj_spec(ps);
    let xs = lj_rows(l, r);
    let rows = gb_rows(ps, l, r);
    lemma_eval_filter(db, ctx, having_pred(), Box::new(gb_query(ps)));
    let rs = filter_results(db, ctx, rows, having_pred());
    let ts = Seq::new(rows.len(), |i: int| truth_of(having_ok(rows[i])));
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Truth, SqlError>(ts[i]) by {
        let k = gkeys(g, xs)[i];
        assert(gkeys(g, xs).contains(k));
        lemma_gkeys_witness(g, xs, k);
        let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], k);
        assert(k == key2(xs[m]));
        let row = rows[i];
        assert(row == full_row(g, xs, k));
        assert(agg_outs(g, xs, k)[0] == Val::Int(gcount(g, xs, k) as int));
        assert(row[2] == Val::Int(gcount(g, xs, k) as int));
        assert(ctx + row =~= row);
        let c = gcount(g, xs, k) as int;
        lemma_compare_int(c, 10);
        crate::link::expr::lemma_expr_col(db, row, 2);
        lemma_pred_cmp(db, row, CmpOp::Gt, Expr::Col(2), Expr::Lit(Literal::Int { v: 10, kind: IntKind::Int4 }),
            Val::Int(c), Val::Int(10), c, 10);
    }
    lemma_collect_all(rs, ts);
    lemma_keep_true_keep(rows, ts, |row: Row| having_ok(row));
}

/// Every joined row is `joined_ok`, 19 wide, and projects to itself.
proof fn lemma_xs_shape(l: Seq<Row>, r: Seq<Row>)
    requires nums_ok(l), pres_ok(r),
    ensures
        forall|m: int| 0 <= m < lj_rows(l, r).len() ==> joined_ok(#[trigger] lj_rows(l, r)[m]),
        proj_all(lj_rows(l, r), ident19()) == lj_rows(l, r),
{
    let xs = lj_rows(l, r);
    lemma_lj_shape(l, r);
    assert forall|m: int| 0 <= m < xs.len() implies (#[trigger] xs[m]).len() == 19 by {
        assert(joined_ok(xs[m]));
    }
    lemma_proj_all_ident(xs);
}

proof fn lemma_pred_agrees(db: Database, ps: Seq<Literal>, xs: Seq<Row>)
    requires param_domain(ps), forall|m: int| 0 <= m < xs.len() ==> joined_ok(#[trigger] xs[m]),
    ensures pred_agrees(db, xs, ident19(), where_pred(ps), lj_spec(ps)),
{
    let g = lj_spec(ps);
    assert forall|i: int| 0 <= i < xs.len() implies
        eval_pred(db, #[trigger] xs[i], where_pred(ps)) == Ok::<Truth, SqlError>(truth_of((g.qual)(proj(xs[i], ident19())))) by {
        lemma_proj_ident(xs[i]);
        lemma_where_eval(db, ps, xs[i]);
    }
}

proof fn lemma_keys_agree(db: Database, ps: Seq<Literal>, xs: Seq<Row>)
    requires forall|m: int| 0 <= m < xs.len() ==> joined_ok(#[trigger] xs[m]),
    ensures keys_agree(db, xs, ident19(), gb_keys(), lj_spec(ps)),
{
    let g = lj_spec(ps);
    assert forall|i: int| 0 <= i < xs.len() && (g.qual)(proj(#[trigger] xs[i], ident19())) implies
        eval_exprs(db, xs[i], gb_keys()) == Ok::<Row, SqlError>((g.key)(proj(xs[i], ident19()))) by {
        lemma_proj_ident(xs[i]);
        lemma_keys_eval(db, xs[i]);
    }
}

proof fn lemma_args_agree(db: Database, ps: Seq<Literal>, xs: Seq<Row>)
    requires forall|m: int| 0 <= m < xs.len() ==> joined_ok(#[trigger] xs[m]),
    ensures args_agree(db, xs, ident19(), gb_aggs(), lj_spec(ps)),
{
    let g = lj_spec(ps);
    assert forall|i: int| 0 <= i < xs.len() && (g.qual)(proj(#[trigger] xs[i], ident19())) implies
        agg_args(db, xs[i], gb_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(xs[i], ident19()))) by {
        lemma_proj_ident(xs[i]);
        lemma_args_eval(db, ps, xs[i]);
    }
}

proof fn lemma_keys_exact(ps: Seq<Literal>, ys: Seq<Row>)
    requires forall|m: int| 0 <= m < ys.len() ==> joined_ok(#[trigger] ys[m]),
    ensures keys_exact(lj_spec(ps), ys),
{
    let g = lj_spec(ps);
    assert forall|a: int, b: int| 0 <= a < ys.len() && 0 <= b < ys.len() && (g.qual)(ys[a]) && (g.qual)(ys[b]) implies
        (row_not_distinct(#[trigger] (g.key)(ys[a]), #[trigger] (g.key)(ys[b])) <==> (g.key)(ys[a]) == (g.key)(ys[b])) by {
        assert(joined_ok(ys[a]) && joined_ok(ys[b]));
        let (ka, kb) = (key2(ys[a]), key2(ys[b]));
        assert(ys[a][1] == ys[a].subrange(0, 9)[1] && ys[a][2] == ys[a].subrange(0, 9)[2]);
        assert(ys[b][1] == ys[b].subrange(0, 9)[1] && ys[b][2] == ys[b].subrange(0, 9)[2]);
        assert forall|i: int| 0 <= i < ka.len() implies crate::bridge::equality::same_exact_type(#[trigger] ka[i], kb[i]) by {}
        lemma_row_exact(ka, kb);
    }
}

/// The body of the statement: the HAVING rows of the groups (first-occurrence order), inside `group_caps`.
pub proof fn lemma_body(db: Database, ps: Seq<Literal>, l: Seq<Row>, r: Seq<Row>)
    requires
        db.tables.len() == 4,
        db.tables[1] == l,
        db.tables[3] == r,
        nums_ok(l),
        pres_ok(r),
        query_arity(db.schema, Query::Table(3)) == 10,
        param_domain(ps),
        group_caps(lj_spec(ps), lj_rows(l, r)),
    ensures
        eval_query(db, Seq::empty(), body_query(ps))
            == Ok::<Relation, SqlError>(keep(gb_rows(ps, l, r), |row: Row| having_ok(row))),
{
    hide(eval_pred);
    hide(eval_exprs);
    hide(agg_args);
    let g = lj_spec(ps);
    let xs = lj_rows(l, r);
    let cols = ident19();
    lemma_lj_eval(db, l, r);
    lemma_xs_shape(l, r);
    lemma_pred_agrees(db, ps, xs);
    lemma_filter_rows(db, lj_query(), xs, cols, where_pred(ps), g);
    lemma_keys_agree(db, ps, xs);
    lemma_args_agree(db, ps, xs);
    assert(aggs_match(gb_aggs(), g));
    lemma_keys_exact(ps, xs);
    lemma_group_query(db, xs, cols, where_query(ps), gb_keys(), gb_aggs(), g);
    assert(eval_query(db, Seq::empty(), gb_query(ps)) == Ok::<Relation, SqlError>(gb_rows(ps, l, r)));
    lemma_having_eval(db, ps, l, r);
}

/// The WHERE rows and the per-row agreements of the GROUP BY (shared by the result and the capacity proofs).
pub proof fn lemma_where_facts(db: Database, ps: Seq<Literal>, l: Seq<Row>, r: Seq<Row>)
    requires
        db.tables.len() == 4,
        db.tables[1] == l,
        db.tables[3] == r,
        nums_ok(l),
        pres_ok(r),
        query_arity(db.schema, Query::Table(3)) == 10,
        param_domain(ps),
    ensures ({
        let g = lj_spec(ps);
        let xs = lj_rows(l, r);
        &&& eval_query(db, Seq::empty(), where_query(ps))
            == Ok::<Relation, SqlError>(keep_true(xs, qual_truths(g, proj_all(xs, ident19()))))
        &&& keys_agree(db, xs, ident19(), gb_keys(), g)
        &&& args_agree(db, xs, ident19(), gb_aggs(), g)
        &&& keys_exact(g, proj_all(xs, ident19()))
        &&& aggs_match(gb_aggs(), g)
        &&& proj_all(xs, ident19()) == xs
    }),
{
    hide(eval_pred);
    hide(eval_exprs);
    hide(agg_args);
    let g = lj_spec(ps);
    let xs = lj_rows(l, r);
    let cols = ident19();
    lemma_lj_eval(db, l, r);
    lemma_xs_shape(l, r);
    lemma_pred_agrees(db, ps, xs);
    lemma_filter_rows(db, lj_query(), xs, cols, where_pred(ps), g);
    lemma_keys_agree(db, ps, xs);
    lemma_args_agree(db, ps, xs);
    lemma_keys_exact(ps, xs);
}

} // verus!
