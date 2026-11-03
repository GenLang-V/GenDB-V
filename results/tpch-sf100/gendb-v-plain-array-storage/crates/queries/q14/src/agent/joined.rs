//! FROM and WHERE over the joined rows `jrows(sv) = lineitem x part` (left-major, `row2(l, a)` = lineitem row `l`
//! then part row `a`; 25 values).
//!
//! - `bounds_ok(ps, w, t1)`: the window `w` (stored days) is the statement's: `w.lo` is `$1` and `t1` the timestamp
//!   `$1 + INTERVAL '1' MONTH`, whose first day not before it is `w.hi`.
//! - On every joined row the WHERE condition evaluates without error to `jq(w)` (`lemma_pred_row2`): the keys are
//!   equal and the ship date is inside the window; so the filter is `keep(jrows, jq(w))` (`lemma_eval_filter`).
//!   When `$1 + INTERVAL '1' MONTH` fails, the condition fails with that error on every joined row
//!   (`lemma_pred_err`), and the filter is that error when the product is not empty (`lemma_filter_err`).
//! - Sums over the kept rows of the joined-row terms `jt_*` are the per-lineitem totals `line::tot`
//!   (`lemma_kept_sums`): the part key column is duplicate-free, so each lineitem row meets at most one part row
//!   (`common::sum_pick`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::datetime::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::source_check::date32_val;
use crate::link::join::{keep, sum_of, lemma_keep_true_keep, lemma_keep_members, lemma_sum_of_keep, lemma_sum_of_ext};
use crate::link::expr::{ival, tval, lemma_pred_cmp, lemma_pred_and, lemma_compare_date, lemma_compare_int};
use crate::bridge::relation::{is_concat, lemma_product_rows_elems};
use crate::bridge::collect::{lemma_collect_all, lemma_collect_pointwise};
use crate::exec::relational::domain::filter_results;
use crate::link::capacity::lemma_filter_err as lemma_filter_err_uniform;
use crate::query::param_domain;
use crate::agent::tables::*;
use crate::agent::line::*;
use crate::agent::ast::*;
use crate::agent::common::selection::*;
use crate::agent::common::sum_pick::*;
use crate::agent::common::like_prefix::starts_with_chars;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_part::interface as pi;

verus! {

// ------------------------------------------------------------------------------------------------ joined rows

/// The FROM relation.
pub open spec fn jrows(sv: StoresView) -> Seq<Row> { product_rows(line_rows(sv), part_rows(sv)) }

/// The joined row of lineitem row `l` and part row `a`.
pub open spec fn row2(sv: StoresView, l: int, a: int) -> Row { line_rows(sv)[l] + part_rows(sv)[a] }

/// The values of a joined row at the positions the statement reads.
pub proof fn lemma_row2(sv: StoresView, l: int, a: int)
    requires 0 <= l < n_l(sv), 0 <= a < n_p(sv),
    ensures ({
        let x = row2(sv, l, a);
        &&& x.len() == 25
        &&& x[1] == Val::Int(l_pkey(sv)[l] as int)
        &&& x[5] == (Val::Num { coeff: l_price(sv)[l] as int, scale: 2 })
        &&& x[6] == (Val::Num { coeff: l_disc(sv)[l] as int, scale: 2 })
        &&& x[10] == date32_val(l_ship(sv)[l])
        &&& x[16] == Val::Int(p_key(sv)[a] as int)
        &&& x[20] == Val::Text(p_type(sv, a))
    }),
{
    let lr = line_rows(sv)[l];
    let pr = part_rows(sv)[a];
    assert(lr == li::row_at(sv.flat_lineitem, l));
    assert(pr == pi::row_at(sv.flat_part, a));
    let x = lr + pr;
    assert(x[1] == lr[1] && x[5] == lr[5] && x[6] == lr[6] && x[10] == lr[10]);
    assert(x[16] == pr[0] && x[20] == pr[4]);
}

/// Every joined row is `row2(l, a)` for a lineitem row `l` and a part row `a`.
pub proof fn lemma_jrows_elem(sv: StoresView, k: int)
    requires 0 <= k < jrows(sv).len(),
    ensures exists|l: int, a: int| 0 <= l < n_l(sv) && 0 <= a < n_p(sv) && jrows(sv)[k] == #[trigger] row2(sv, l, a),
{
    lemma_product_rows_elems(line_rows(sv), part_rows(sv));
    assert(is_concat(jrows(sv)[k], line_rows(sv), part_rows(sv)));
    let (l, a) = choose|i: int, j: int| 0 <= i < line_rows(sv).len() && 0 <= j < part_rows(sv).len()
        && jrows(sv)[k] == #[trigger] line_rows(sv)[i] + #[trigger] part_rows(sv)[j];
    assert(jrows(sv)[k] == row2(sv, l, a));
}

/// The product has a row exactly when both tables do.
pub proof fn lemma_jrows_len(sv: StoresView)
    ensures jrows(sv).len() == n_l(sv) * n_p(sv), (jrows(sv).len() == 0) == (n_l(sv) == 0 || n_p(sv) == 0),
{
    lemma_product_rows_elems(line_rows(sv), part_rows(sv));
    let (x, y) = (n_l(sv) as int, n_p(sv) as int);
    assert((x * y == 0) == (x == 0 || y == 0)) by (nonlinear_arith) requires x >= 0, y >= 0;
}

/// FROM evaluates to the joined rows.
pub proof fn lemma_eval_from(sv: StoresView, db: Database)
    requires tables_of(sv, db),
    ensures eval_query(db, Seq::empty(), q_from()) == Ok::<Relation, SqlError>(jrows(sv)),
{
    let e = Seq::<Val>::empty();
    assert(eval_query(db, e, Query::Table(0)) == Ok::<Relation, SqlError>(line_rows(sv)));
    assert(eval_query(db, e, Query::Table(3)) == Ok::<Relation, SqlError>(part_rows(sv)));
}

// ------------------------------------------------------------------------------------------------ the window

/// `$1 + INTERVAL '1' MONTH` at the day `pd` (days since 2000-01-01): the timestamp of `date_to_ts` and
/// `ts_add_interval`, or their error.
pub open spec fn month_end_val(pd: int) -> Result<Val, SqlError> {
    match date_to_ts(pd) {
        Err(e) => Err(e),
        Ok(t0) => match ts_add_interval(t0, 1, 0, 0) {
            Ok(t) => Ok(Val::Ts(t)),
            Err(e) => Err(e),
        },
    }
}

/// The evaluator's value of `$1 + INTERVAL '1' MONTH` (it reads no column).
pub proof fn lemma_month_end_eval(db: Database, env: Row, p0: Literal, pd: int)
    requires lit_val(p0) == Ok::<Val, SqlError>(Val::Date(pd)),
    ensures eval_expr(db, env, month_end(p0)) == month_end_val(pd),
{
    hide(lit_val);
    hide(date_to_ts);
    hide(ts_add_interval);
    let cst = Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(Expr::Lit(p0)) };
    assert(eval_expr(db, env, Expr::Lit(p0)) == Ok::<Val, SqlError>(Val::Date(pd)));
    assert(eval_expr(db, env, cst) == cast(CastOp::DateToTimestamp, Val::Date(pd)));
}

/// The window `w` and the timestamp `t1` are the statement's at the parameters `ps`.
pub open spec fn bounds_ok(ps: Seq<Literal>, w: Win, t1: int) -> bool {
    &&& ps.len() == 1
    &&& lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(w.lo - 10957))
    &&& month_end_val(w.lo - 10957) == Ok::<Val, SqlError>(Val::Ts(t1))
    &&& (w.hi - 10957 - 1) * usecs_per_day() < t1
    &&& t1 <= (w.hi - 10957) * usecs_per_day()
}

/// A date value inside the window (`w` in stored days, the value in days since 2000-01-01).
pub open spec fn date_in(w: Win, v: Val) -> bool {
    match v { Val::Date(d) => w.lo - 10957 <= d && d < w.hi - 10957, _ => false }
}

/// The WHERE condition as a function of a joined row (two-valued: every operand is a non-NULL value).
pub open spec fn jq(w: Win) -> spec_fn(Row) -> bool {
    |x: Row| x[1] == x[16] && date_in(w, x[10])
}

/// On a joined row of the database, the condition is the key match and the window.
pub proof fn lemma_jq_row2(sv: StoresView, w: Win, l: int, a: int)
    requires 0 <= l < n_l(sv), 0 <= a < n_p(sv),
    ensures (jq(w))(row2(sv, l, a)) == (p_key(sv)[a] == l_pkey(sv)[l] && in_win(sv, w, l)),
{
    lemma_row2(sv, l, a);
}

/// The WHERE condition on a joined row.
pub proof fn lemma_pred_row2(db: Database, sv: StoresView, ps: Seq<Literal>, w: Win, t1: int, l: int, a: int)
    requires bounds_ok(ps, w, t1), 0 <= l < n_l(sv), 0 <= a < n_p(sv),
    ensures eval_pred(db, row2(sv, l, a), q_pred(ps)) == Ok::<Truth, SqlError>(truth_of((jq(w))(row2(sv, l, a)))),
{
    let x = row2(sv, l, a);
    lemma_row2(sv, l, a);
    let pk = l_pkey(sv)[l] as int;
    let key = p_key(sv)[a] as int;
    let d = l_ship(sv)[l] as int - 10957;
    let plo = w.lo - 10957;
    let phi = w.hi - 10957;
    let u = usecs_per_day();
    // l_partkey = p_partkey
    assert(eval_expr(db, x, Expr::Col(1)) == Ok::<Val, SqlError>(x[1]));
    assert(eval_expr(db, x, Expr::Col(16)) == Ok::<Val, SqlError>(x[16]));
    lemma_compare_int(pk, key);
    lemma_pred_cmp(db, x, CmpOp::Eq, Expr::Col(1), Expr::Col(16), x[1], x[16], pk, key);
    // l_shipdate >= $1
    assert(eval_expr(db, x, Expr::Col(10)) == Ok::<Val, SqlError>(Val::Date(d)));
    assert(eval_expr(db, x, Expr::Lit(ps[0])) == Ok::<Val, SqlError>(Val::Date(plo)));
    lemma_compare_date(d, plo);
    lemma_pred_cmp(db, x, CmpOp::Ge, Expr::Col(10), Expr::Lit(ps[0]), Val::Date(d), Val::Date(plo), d, plo);
    // l_shipdate < $1 + INTERVAL '1' MONTH: `d * u < t1` exactly when `d < phi`, as `t1` lies in `((phi - 1) * u, phi * u]`
    lemma_month_end_eval(db, x, ps[0], plo);
    assert(compare(Val::Date(d), Val::Ts(t1)) == Some(sign(d * u - t1)));
    lemma_pred_cmp(db, x, CmpOp::Lt, Expr::Col(10), month_end(ps[0]), Val::Date(d), Val::Ts(t1), d * u, t1);
    assert((d * u < t1) == (d < phi)) by (nonlinear_arith)
        requires u == 86_400_000_000, (phi - 1) * u < t1, t1 <= phi * u;
    lemma_pred_and(db, x, key_pred(), lo_pred(ps[0]), pk == key, d >= plo);
    lemma_pred_and(db, x, and(key_pred(), lo_pred(ps[0])), hi_pred(ps[0]), pk == key && d >= plo, d < phi);
    assert((x[1] == x[16]) == (pk == key));
}

/// The filter keeps exactly the joined rows satisfying `jq(w)`.
pub proof fn lemma_eval_filter(db: Database, sv: StoresView, ps: Seq<Literal>, w: Win, t1: int)
    requires tables_of(sv, db), bounds_ok(ps, w, t1),
    ensures eval_query(db, Seq::empty(), q_filter(ps)) == Ok::<Relation, SqlError>(keep(jrows(sv), jq(w))),
{
    lemma_eval_from(sv, db);
    let rows = jrows(sv);
    let ctx = Seq::<Val>::empty();
    let pred = q_pred(ps);
    let f = jq(w);
    let truths = Seq::new(rows.len(), |i: int| truth_of(f(rows[i])));
    let prs = Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred));
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        assert(ctx + rows[i] =~= rows[i]);
        lemma_jrows_elem(sv, i);
        let (l, a) = choose|l: int, a: int| 0 <= l < n_l(sv) && 0 <= a < n_p(sv) && rows[i] == #[trigger] row2(sv, l, a);
        lemma_pred_row2(db, sv, ps, w, t1, l, a);
    }
    lemma_collect_all(prs, truths);
    lemma_collect_pointwise::<Truth>();
    assert(collect(Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred))) == Ok::<Seq<Truth>, SqlError>(truths));
    lemma_keep_true_keep(rows, truths, f);
}

/// An empty product: the filter keeps nothing, whatever the condition.
pub proof fn lemma_eval_filter_empty(db: Database, sv: StoresView, ps: Seq<Literal>, w: Win)
    requires tables_of(sv, db), jrows(sv).len() == 0,
    ensures eval_query(db, Seq::empty(), q_filter(ps)) == Ok::<Relation, SqlError>(keep(jrows(sv), jq(w))),
{
    lemma_eval_from(sv, db);
    let rows = jrows(sv);
    let ctx = Seq::<Val>::empty();
    let pred = q_pred(ps);
    assert(Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred)) =~= Seq::<Result<Truth, SqlError>>::empty());
    assert(keep(rows, jq(w)) =~= Seq::<Row>::empty());
    assert(keep_true(rows, Seq::<Truth>::empty()) =~= Seq::<Row>::empty());
}

/// On a joined row, the WHERE condition fails with the error of `$1 + INTERVAL '1' MONTH`.
pub proof fn lemma_pred_err(db: Database, sv: StoresView, ps: Seq<Literal>, pd: int, e: SqlError, l: int, a: int)
    requires
        ps.len() == 1,
        lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(pd)),
        month_end_val(pd) == Err::<Val, SqlError>(e),
        0 <= l < n_l(sv), 0 <= a < n_p(sv),
    ensures eval_pred(db, row2(sv, l, a), q_pred(ps)) == Err::<Truth, SqlError>(e),
{
    let x = row2(sv, l, a);
    lemma_row2(sv, l, a);
    let pk = l_pkey(sv)[l] as int;
    let key = p_key(sv)[a] as int;
    let d = l_ship(sv)[l] as int - 10957;
    assert(eval_expr(db, x, Expr::Col(1)) == Ok::<Val, SqlError>(x[1]));
    assert(eval_expr(db, x, Expr::Col(16)) == Ok::<Val, SqlError>(x[16]));
    lemma_compare_int(pk, key);
    lemma_pred_cmp(db, x, CmpOp::Eq, Expr::Col(1), Expr::Col(16), x[1], x[16], pk, key);
    assert(eval_expr(db, x, Expr::Col(10)) == Ok::<Val, SqlError>(Val::Date(d)));
    assert(eval_expr(db, x, Expr::Lit(ps[0])) == Ok::<Val, SqlError>(Val::Date(pd)));
    lemma_compare_date(d, pd);
    lemma_pred_cmp(db, x, CmpOp::Ge, Expr::Col(10), Expr::Lit(ps[0]), Val::Date(d), Val::Date(pd), d, pd);
    lemma_pred_and(db, x, key_pred(), lo_pred(ps[0]), pk == key, d >= pd);
    lemma_month_end_eval(db, x, ps[0], pd);
    assert(eval_pred(db, x, hi_pred(ps[0])) == Err::<Truth, SqlError>(e));
}

/// A failing `$1 + INTERVAL '1' MONTH` on a non-empty product: the filter is that error.
pub proof fn lemma_filter_err(db: Database, sv: StoresView, ps: Seq<Literal>, pd: int, e: SqlError)
    requires
        tables_of(sv, db),
        ps.len() == 1,
        lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(pd)),
        month_end_val(pd) == Err::<Val, SqlError>(e),
        jrows(sv).len() > 0,
    ensures eval_query(db, Seq::empty(), q_filter(ps)) == Err::<Relation, SqlError>(e),
{
    let ctx = Seq::<Val>::empty();
    let rows = jrows(sv);
    let pred = q_pred(ps);
    lemma_eval_from(sv, db);
    assert forall|k: int| 0 <= k < rows.len() implies #[trigger] eval_pred(db, ctx + rows[k], pred) == Err::<Truth, SqlError>(e) by {
        assert(ctx + rows[k] =~= rows[k]);
        lemma_jrows_elem(sv, k);
        let (l, a) = choose|l: int, a: int| 0 <= l < n_l(sv) && 0 <= a < n_p(sv) && rows[k] == #[trigger] row2(sv, l, a);
        lemma_pred_err(db, sv, ps, pd, e, l, a);
    }
    assert(eval_pred(db, ctx + rows[0], pred) == Err::<Truth, SqlError>(e));
    lemma_filter_err_uniform(db, ctx, pred, Box::new(q_from()), rows, e, 0);
}

// ------------------------------------------------------------------------------------------------ sums

/// `l_extendedprice * (1 - l_discount)` of a joined row (scale-4 coefficient).
pub open spec fn jvol(x: Row) -> int { ival(x[5]) * (100 - ival(x[6])) }

/// The joined row's part type starts with the characters `PROMO`.
pub open spec fn jpromo(x: Row) -> bool { starts_with_chars(tval(x[20]), promo_lit()) }

/// Joined-row terms of the six totals (zero off the condition).
pub open spec fn jt_cnt(w: Win) -> spec_fn(Row) -> int { |x: Row| if (jq(w))(x) { 1int } else { 0int } }
pub open spec fn jt_all(w: Win) -> spec_fn(Row) -> int { |x: Row| if (jq(w))(x) { jvol(x) } else { 0int } }
pub open spec fn jt_abs(w: Win) -> spec_fn(Row) -> int { |x: Row| if (jq(w))(x) { abs(jvol(x)) } else { 0int } }
pub open spec fn jt_npr(w: Win) -> spec_fn(Row) -> int { |x: Row| if (jq(w))(x) && jpromo(x) { 1int } else { 0int } }
pub open spec fn jt_pr(w: Win) -> spec_fn(Row) -> int { |x: Row| if (jq(w))(x) && jpromo(x) { jvol(x) } else { 0int } }
pub open spec fn jt_apr(w: Win) -> spec_fn(Row) -> int { |x: Row| if (jq(w))(x) && jpromo(x) { abs(jvol(x)) } else { 0int } }

/// The sum over a sequence built by `Seq::new` is the range sum of the terms of its elements.
pub proof fn lemma_sum_of_new(n: nat, g: spec_fn(int) -> Row, h: spec_fn(Row) -> int)
    ensures sum_of(Seq::new(n, g), h) == range_sum(0, n as int, |i: int| h(g(i))),
    decreases n,
{
    if n > 0 {
        let s = Seq::new(n, g);
        lemma_sum_of_new((n - 1) as nat, g, h);
        assert(s.drop_last() =~= Seq::new((n - 1) as nat, g));
    } else {
        assert(Seq::new(n, g) =~= Seq::<Row>::empty());
    }
}

/// A sum over the joined rows whose terms vanish off the key match is the range sum of the term at each lineitem
/// row's part row (0 for a lineitem row without a part).
pub proof fn lemma_jsum(sv: StoresView, h: spec_fn(Row) -> int, f: spec_fn(int) -> int)
    requires
        keys_unique(p_key(sv)),
        forall|l: int, a: int| 0 <= l < n_l(sv) && 0 <= a < n_p(sv) && h(#[trigger] row2(sv, l, a)) != 0
            ==> p_key(sv)[a] == l_pkey(sv)[l],
        forall|l: int| 0 <= l < n_l(sv) ==> #[trigger] f(l) == if has_part(sv, l) { h(row2(sv, l, part_of(sv, l))) } else { 0 },
    ensures sum_of(jrows(sv), h) == range_sum(0, n_l(sv) as int, f),
{
    let lr = line_rows(sv);
    let pr = part_rows(sv);
    assert(col_unique(pr, 0)) by {
        assert forall|p: int, q: int| 0 <= p < pr.len() && 0 <= q < pr.len() && #[trigger] pr[p][0] == #[trigger] pr[q][0] implies p == q by {
            assert(pr[p] == pi::row_at(sv.flat_part, p));
            assert(pr[q] == pi::row_at(sv.flat_part, q));
        }
    }
    assert forall|p: int, q: int| 0 <= p < lr.len() && 0 <= q < pr.len() && h(#[trigger] lr[p] + #[trigger] pr[q]) != 0
        implies pr[q][0] == lr[p][1] by {
        assert(lr[p] + pr[q] == row2(sv, p, q));
        lemma_row2(sv, p, q);
        assert((lr[p] + pr[q])[1] == lr[p][1] && (lr[p] + pr[q])[16] == pr[q][0]);
    }
    lemma_sum_product_right(lr, pr, h, 1, 0);
    let phi = |x: Row| at_pick(pr, 0, x[1], |y: Row| h(x + y));
    let g = |i: int| li::row_at(sv.flat_lineitem, i);
    assert(lr == Seq::new(n_l(sv), g));
    lemma_sum_of_new(n_l(sv), g, phi);
    let gl = |i: int| phi(g(i));
    assert forall|l: int| 0 <= l < n_l(sv) implies #[trigger] gl(l) == f(l) by {
        let x = lr[l];
        assert(g(l) == x);
        let hx = |y: Row| h(x + y);
        let v = Val::Int(l_pkey(sv)[l] as int);
        assert(x == li::row_at(sv.flat_lineitem, l));
        assert(x[1] == v);
        assert(gl(l) == at_pick(pr, 0, v, hx));
        lemma_pick(pr, 0, v);
        if has_part(sv, l) {
            lemma_part_of(sv, l);
            let a0 = part_of(sv, l);
            assert(pr[a0] == pi::row_at(sv.flat_part, a0));
            assert(pr[a0][0] == v);
            assert(has_pick(pr, 0, v));
            assert(pick(pr, 0, v) == a0);
            assert(hx(pr[a0]) == h(row2(sv, l, a0)));
        } else {
            assert(!has_pick(pr, 0, v)) by {
                if has_pick(pr, 0, v) {
                    let q = choose|q: int| 0 <= q < pr.len() && #[trigger] pr[q][0] == v;
                    assert(pr[q] == pi::row_at(sv.flat_part, q));
                    assert(p_key(sv)[q] == l_pkey(sv)[l]);
                }
            }
        }
    }
    lemma_range_sum_ext(0, n_l(sv) as int, gl, f);
}

/// The joined row of a lineitem row and its part row: the condition is the window, the volume and the promotion
/// are the lineitem row's.
pub proof fn lemma_row2_part(sv: StoresView, w: Win, l: int)
    requires keys_unique(p_key(sv)), 0 <= l < n_l(sv), has_part(sv, l),
    ensures ({
        let x = row2(sv, l, part_of(sv, l));
        &&& (jq(w))(x) == in_win(sv, w, l)
        &&& jvol(x) == vol(sv, l)
        &&& jpromo(x) == promo(sv, part_of(sv, l))
    }),
{
    lemma_part_of(sv, l);
    let a = part_of(sv, l);
    lemma_row2(sv, l, a);
    lemma_jq_row2(sv, w, l, a);
}

/// A joined-row term vanishing off the condition sums, over the kept rows, to the range sum of `f`.
proof fn lemma_term(sv: StoresView, w: Win, jt: spec_fn(Row) -> int, f: spec_fn(int) -> int)
    requires
        keys_unique(p_key(sv)),
        forall|x: Row| !(#[trigger] (jq(w))(x)) ==> jt(x) == 0,
        forall|l: int| 0 <= l < n_l(sv) ==> #[trigger] f(l) == if has_part(sv, l) { jt(row2(sv, l, part_of(sv, l))) } else { 0 },
    ensures sum_of(keep(jrows(sv), jq(w)), jt) == range_sum(0, n_l(sv) as int, f),
{
    let rows = jrows(sv);
    assert forall|i: int| 0 <= i < rows.len() && !(jq(w))(#[trigger] rows[i]) implies jt(rows[i]) == 0 by {}
    lemma_sum_of_keep(rows, jq(w), jt);
    assert forall|l: int, a: int| 0 <= l < n_l(sv) && 0 <= a < n_p(sv) && jt(#[trigger] row2(sv, l, a)) != 0
        implies p_key(sv)[a] == l_pkey(sv)[l] by {
        lemma_jq_row2(sv, w, l, a);
    }
    lemma_jsum(sv, jt, f);
}

/// The sums of the six joined-row terms over the kept rows are the per-lineitem totals.
pub proof fn lemma_kept_sums(sv: StoresView, w: Win)
    requires keys_unique(p_key(sv)),
    ensures ({
        let k = keep(jrows(sv), jq(w));
        let t = tot(sv, w, 0, n_l(sv) as int);
        &&& sum_of(k, jt_cnt(w)) == t.cnt
        &&& sum_of(k, jt_all(w)) == t.s_all
        &&& sum_of(k, jt_abs(w)) == t.a_all
        &&& sum_of(k, jt_npr(w)) == t.n_pr
        &&& sum_of(k, jt_pr(w)) == t.s_pr
        &&& sum_of(k, jt_apr(w)) == t.a_pr
    }),
{
    assert forall|l: int| 0 <= l < n_l(sv) && has_part(sv, l) implies {
        let x = row2(sv, l, part_of(sv, l));
        &&& (jq(w))(x) == in_win(sv, w, l)
        &&& jvol(x) == vol(sv, l)
        &&& jpromo(x) == promo(sv, part_of(sv, l))
    } by {
        lemma_row2_part(sv, w, l);
    }
    lemma_term(sv, w, jt_cnt(w), f_cnt(sv, w));
    lemma_term(sv, w, jt_all(w), f_all(sv, w));
    lemma_term(sv, w, jt_abs(w), f_abs(sv, w));
    lemma_term(sv, w, jt_npr(w), f_npr(sv, w));
    lemma_term(sv, w, jt_pr(w), f_pr(sv, w));
    lemma_term(sv, w, jt_apr(w), f_apr(sv, w));
}

/// Every kept row is the joined row of a lineitem row and a part row, and satisfies the condition.
pub proof fn lemma_kept_rows(sv: StoresView, w: Win)
    ensures
        forall|i: int| 0 <= i < keep(jrows(sv), jq(w)).len() ==> (jq(w))(#[trigger] keep(jrows(sv), jq(w))[i])
            && exists|l: int, a: int| 0 <= l < n_l(sv) && 0 <= a < n_p(sv) && keep(jrows(sv), jq(w))[i] == #[trigger] row2(sv, l, a),
{
    let rows = jrows(sv);
    let k = keep(rows, jq(w));
    lemma_keep_members(rows, jq(w));
    assert forall|i: int| 0 <= i < k.len() implies (jq(w))(#[trigger] k[i])
        && exists|l: int, a: int| 0 <= l < n_l(sv) && 0 <= a < n_p(sv) && k[i] == #[trigger] row2(sv, l, a) by {
        assert(rows.contains(k[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == k[i];
        lemma_jrows_elem(sv, m);
    }
}

} // verus!
