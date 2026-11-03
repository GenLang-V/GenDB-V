//! FROM and WHERE over the joined rows `jrows(sv) = lineitem x part` (left-major, `row2(l, a)` = lineitem row `l`
//! then part row `a`; 25 values).
//!
//! - The parameters are texts `pb(ps)` (`$1`, the brand) and `pc(ps)` (`$2`, the container).
//! - On every joined row the WHERE condition evaluates without error to `jq(x)` (`lemma_pred_row2`): the keys are
//!   equal, the part's brand and container are the parameters, and the quantity is below the subquery's value
//!   `sub::sub_val` of the part key (`below`). When the keys are equal the part key has a lineitem row, so the
//!   subquery is not NULL and the comparison is two-valued; otherwise the conjunction is false whatever it is.
//!   So the filter is `keep(jrows, jq)` (`lemma_eval_filter`).
//! - Sums over the kept rows of joined-row terms are range sums over the lineitem rows of the term at each row's
//!   part row (`lemma_jsum`): the part key column is duplicate-free, so each lineitem row meets at most one part
//!   row (`common::sum_pick`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::gendb_entry::stores::StoresView;
use crate::link::join::{keep, sum_of, lemma_keep_true_keep, lemma_keep_members, lemma_sum_of_keep, lemma_sum_of_ext};
use crate::link::expr::{ival, lemma_pred_cmp, lemma_pred_and, lemma_pred_text_cmp, lemma_compare_int, lemma_compare_num};
use crate::bridge::relation::{is_concat, lemma_product_rows_elems};
use crate::bridge::collect::{lemma_collect_all, lemma_collect_pointwise};
use crate::agent::tables::*;
use crate::agent::ast::*;
use crate::agent::sub::*;
use crate::agent::common::selection::*;
use crate::agent::common::sum_pick::*;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_part::interface as pi;

verus! {

// ------------------------------------------------------------------------------------------------ parameters

/// The bytes of a text literal (empty for another literal).
pub open spec fn lit_bytes(l: Literal) -> Seq<u8> {
    match l { Literal::Text(b) => b, _ => Seq::empty() }
}

/// `$1` (the brand) and `$2` (the container).
pub open spec fn pb(ps: Seq<Literal>) -> Seq<u8> { lit_bytes(ps[0]) }
pub open spec fn pc(ps: Seq<Literal>) -> Seq<u8> { lit_bytes(ps[1]) }

/// Both parameters are text literals.
pub open spec fn params_text(ps: Seq<Literal>) -> bool {
    &&& ps.len() == 2
    &&& ps[0] is Text
    &&& ps[1] is Text
}

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
        &&& x[4] == (Val::Num { coeff: l_qty(sv)[l] as int, scale: 2 })
        &&& x[5] == (Val::Num { coeff: l_price(sv)[l] as int, scale: 2 })
        &&& x[16] == Val::Int(p_key(sv)[a] as int)
        &&& x[19] == Val::Text(p_brand(sv, a))
        &&& x[22] == Val::Text(p_cont(sv, a))
    }),
{
    let lr = line_rows(sv)[l];
    let pr = part_rows(sv)[a];
    assert(lr == li::row_at(sv.flat_lineitem, l));
    assert(pr == pi::row_at(sv.flat_part, a));
    let x = lr + pr;
    assert(x[1] == lr[1] && x[4] == lr[4] && x[5] == lr[5]);
    assert(x[16] == pr[0] && x[19] == pr[3] && x[22] == pr[6]);
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

// ------------------------------------------------------------------------------------------------ the condition

/// `q < v` for a quantity coefficient `q` (scale 2) and the subquery's value `v`; false for NULL.
pub open spec fn below_val(q: int, v: Val) -> bool {
    match v { Val::Num { coeff, scale } => num_cmp(q, 2, coeff, scale) < 0, _ => false }
}

/// The quantity coefficient `q` is below the subquery's value for part key `k`.
pub open spec fn below(sv: StoresView, q: int, k: int) -> bool { below_val(q, sub_val(sv, k)) }

/// The WHERE condition as a function of a joined row (two-valued on every joined row of the database).
pub open spec fn jq(sv: StoresView, ps: Seq<Literal>) -> spec_fn(Row) -> bool {
    |x: Row| x[16] == x[1] && x[19] == Val::Text(pb(ps)) && x[22] == Val::Text(pc(ps)) && below(sv, ival(x[4]), ival(x[16]))
}

/// A lineitem row's part key has at least that row.
pub proof fn lemma_kcnt_pos(sv: StoresView, l: int)
    requires 0 <= l < n_l(sv),
    ensures kcnt(sv, l_pkey(sv)[l] as int) >= 1,
{
    let k = l_pkey(sv)[l] as int;
    let f = kcnt_term(sv, k);
    assert forall|r: int| 0 <= r < n_l(sv) implies #[trigger] f(r) >= 0 by {}
    lemma_range_sum_split(0, l, n_l(sv) as int, f);
    lemma_range_sum_split(l, l + 1, n_l(sv) as int, f);
    lemma_range_sum_nonneg(0, l, f);
    lemma_range_sum_nonneg(l + 1, n_l(sv) as int, f);
    assert(range_sum(l, l, f) == 0);
    assert(range_sum(l, l + 1, f) == f(l));
}

/// Adjacent ranges add.
pub proof fn lemma_range_sum_split(lo: int, mid: int, hi: int, f: spec_fn(int) -> int)
    requires lo <= mid <= hi,
    ensures range_sum(lo, hi, f) == range_sum(lo, mid, f) + range_sum(mid, hi, f),
    decreases hi - mid,
{
    if hi > mid {
        lemma_range_sum_split(lo, mid, hi - 1, f);
    }
}

/// Kleene AND whose first operand is two-valued and whose second is two-valued wherever the first holds.
pub proof fn lemma_pred_and_guarded(db: Database, env: Row, a: Pred, b: Pred, x: bool, y: bool)
    requires
        eval_pred(db, env, a) == Ok::<Truth, SqlError>(truth_of(x)),
        eval_pred(db, env, b) is Ok,
        x ==> eval_pred(db, env, b) == Ok::<Truth, SqlError>(truth_of(y)),
    ensures
        eval_pred(db, env, Pred::And(Box::new(a), Box::new(b))) == Ok::<Truth, SqlError>(truth_of(x && y)),
{
}

/// The first three conjuncts on a joined row: the keys and the part's brand and container.
pub proof fn lemma_part_pred_row2(db: Database, sv: StoresView, ps: Seq<Literal>, l: int, a: int)
    requires params_text(ps), 0 <= l < n_l(sv), 0 <= a < n_p(sv),
    ensures ({
        let x = row2(sv, l, a);
        eval_pred(db, x, part_pred(ps)) == Ok::<Truth, SqlError>(truth_of(
            x[16] == x[1] && x[19] == Val::Text(pb(ps)) && x[22] == Val::Text(pc(ps))))
    }),
{
    let x = row2(sv, l, a);
    lemma_row2(sv, l, a);
    let lk = l_pkey(sv)[l] as int;
    let pk = p_key(sv)[a] as int;
    // p_partkey = l_partkey
    assert(eval_expr(db, x, Expr::Col(16)) == Ok::<Val, SqlError>(x[16]));
    assert(eval_expr(db, x, Expr::Col(1)) == Ok::<Val, SqlError>(x[1]));
    lemma_compare_int(pk, lk);
    lemma_pred_cmp(db, x, CmpOp::Eq, Expr::Col(16), Expr::Col(1), x[16], x[1], pk, lk);
    // p_brand = $1, p_container = $2
    assert(eval_expr(db, x, Expr::Col(19)) == Ok::<Val, SqlError>(Val::Text(p_brand(sv, a))));
    assert(eval_expr(db, x, Expr::Lit(ps[0])) == Ok::<Val, SqlError>(Val::Text(pb(ps))));
    lemma_pred_text_cmp(db, x, CmpOp::Eq, Expr::Col(19), Expr::Lit(ps[0]), p_brand(sv, a), pb(ps));
    assert(eval_expr(db, x, Expr::Col(22)) == Ok::<Val, SqlError>(Val::Text(p_cont(sv, a))));
    assert(eval_expr(db, x, Expr::Lit(ps[1])) == Ok::<Val, SqlError>(Val::Text(pc(ps))));
    lemma_pred_text_cmp(db, x, CmpOp::Eq, Expr::Col(22), Expr::Lit(ps[1]), p_cont(sv, a), pc(ps));
    lemma_pred_and(db, x, key_pred(), brand_pred(ps[0]), pk == lk, p_brand(sv, a) == pb(ps));
    lemma_pred_and(db, x, and(key_pred(), brand_pred(ps[0])), cont_pred(ps[1]), pk == lk && p_brand(sv, a) == pb(ps),
        p_cont(sv, a) == pc(ps));
}

/// `l_quantity < (subquery)` on a joined row: always a truth value, two-valued when the part key has rows.
pub proof fn lemma_lt_row2(db: Database, sv: StoresView, l: int, a: int)
    requires tables_of(sv, db), model_ok(sv), sizes_ok(sv), 0 <= l < n_l(sv), 0 <= a < n_p(sv),
    ensures ({
        let x = row2(sv, l, a);
        let k = p_key(sv)[a] as int;
        &&& eval_pred(db, x, lt_pred()) is Ok
        &&& kcnt(sv, k) > 0 ==> eval_pred(db, x, lt_pred()) == Ok::<Truth, SqlError>(truth_of(below(sv, l_qty(sv)[l] as int, k)))
    }),
{
    let x = row2(sv, l, a);
    lemma_row2(sv, l, a);
    let k = p_key(sv)[a] as int;
    let q = l_qty(sv)[l] as int;
    lemma_sub_value(db, sv, x, k);
    assert(eval_expr(db, x, Expr::Col(4)) == Ok::<Val, SqlError>(Val::Num { coeff: q, scale: 2 }));
    let v = sub_val(sv, k);
    if kcnt(sv, k) > 0 {
        let c = 2 * avg_coeff(sv, k);
        let s = avg_scale(sv, k) + 1;
        assert(v == Val::Num { coeff: c, scale: s });
        lemma_compare_num(q, 2, c, s);
        assert(compare(Val::Num { coeff: q, scale: 2 }, v) == Some(num_cmp(q, 2, c, s)));
    }
}

/// The WHERE condition on a joined row.
pub proof fn lemma_pred_row2(db: Database, sv: StoresView, ps: Seq<Literal>, l: int, a: int)
    requires tables_of(sv, db), model_ok(sv), sizes_ok(sv), params_text(ps), 0 <= l < n_l(sv), 0 <= a < n_p(sv),
    ensures eval_pred(db, row2(sv, l, a), q_pred(ps)) == Ok::<Truth, SqlError>(truth_of((jq(sv, ps))(row2(sv, l, a)))),
{
    let x = row2(sv, l, a);
    lemma_row2(sv, l, a);
    let k = p_key(sv)[a] as int;
    let part = x[16] == x[1] && x[19] == Val::Text(pb(ps)) && x[22] == Val::Text(pc(ps));
    lemma_part_pred_row2(db, sv, ps, l, a);
    lemma_lt_row2(db, sv, l, a);
    if part {
        // the keys are equal, so the part key has the row `l`
        assert(k == l_pkey(sv)[l] as int);
        lemma_kcnt_pos(sv, l);
    }
    lemma_pred_and_guarded(db, x, part_pred(ps), lt_pred(), part, below(sv, l_qty(sv)[l] as int, k));
    assert(ival(x[4]) == l_qty(sv)[l] as int);
    assert(ival(x[16]) == k);
}

/// The filter keeps exactly the joined rows satisfying `jq`.
pub proof fn lemma_eval_filter(db: Database, sv: StoresView, ps: Seq<Literal>)
    requires tables_of(sv, db), model_ok(sv), sizes_ok(sv), params_text(ps),
    ensures eval_query(db, Seq::empty(), q_filter(ps)) == Ok::<Relation, SqlError>(keep(jrows(sv), jq(sv, ps))),
{
    lemma_eval_from(sv, db);
    let rows = jrows(sv);
    let ctx = Seq::<Val>::empty();
    let pred = q_pred(ps);
    let f = jq(sv, ps);
    let truths = Seq::new(rows.len(), |i: int| truth_of(f(rows[i])));
    let prs = Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred));
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        assert(ctx + rows[i] =~= rows[i]);
        lemma_jrows_elem(sv, i);
        let (l, a) = choose|l: int, a: int| 0 <= l < n_l(sv) && 0 <= a < n_p(sv) && rows[i] == #[trigger] row2(sv, l, a);
        lemma_pred_row2(db, sv, ps, l, a);
    }
    lemma_collect_all(prs, truths);
    lemma_collect_pointwise::<Truth>();
    assert(collect(Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred))) == Ok::<Seq<Truth>, SqlError>(truths));
    lemma_keep_true_keep(rows, truths, f);
}

// ------------------------------------------------------------------------------------------------ per lineitem

/// Part row `a` is selected: its brand and container are the parameters.
pub open spec fn sel(sv: StoresView, ps: Seq<Literal>, a: int) -> bool {
    p_brand(sv, a) == pb(ps) && p_cont(sv, a) == pc(ps)
}

/// Some part row has row `l`'s part key.
pub open spec fn has_part(sv: StoresView, l: int) -> bool {
    exists|a: int| 0 <= a < n_p(sv) && #[trigger] p_key(sv)[a] == l_pkey(sv)[l]
}

/// The part row of row `l` (unique when it exists, `lemma_part_of`).
pub open spec fn part_of(sv: StoresView, l: int) -> int {
    choose|a: int| 0 <= a < n_p(sv) && #[trigger] p_key(sv)[a] == l_pkey(sv)[l]
}

/// Row `l` joins a selected part.
pub open spec fn insel(sv: StoresView, ps: Seq<Literal>, l: int) -> bool {
    has_part(sv, l) && sel(sv, ps, part_of(sv, l))
}

/// Row `l` qualifies: it joins a selected part and its quantity is below the subquery's value.
pub open spec fn qual(sv: StoresView, ps: Seq<Literal>, l: int) -> bool {
    insel(sv, ps, l) && below(sv, l_qty(sv)[l] as int, l_pkey(sv)[l] as int)
}

/// The per-row terms of the result: qualifying rows, and their price coefficients (scale 2).
pub open spec fn f_cnt(sv: StoresView, ps: Seq<Literal>) -> spec_fn(int) -> int {
    |l: int| if qual(sv, ps, l) { 1int } else { 0int }
}
pub open spec fn f_price(sv: StoresView, ps: Seq<Literal>) -> spec_fn(int) -> int {
    |l: int| if qual(sv, ps, l) { l_price(sv)[l] as int } else { 0int }
}

/// The part row of a row with a part holds its key, and it is the only one.
pub proof fn lemma_part_of(sv: StoresView, l: int)
    requires keys_unique(p_key(sv)), has_part(sv, l),
    ensures
        0 <= part_of(sv, l) < n_p(sv),
        p_key(sv)[part_of(sv, l)] == l_pkey(sv)[l],
        forall|a: int| 0 <= a < n_p(sv) && #[trigger] p_key(sv)[a] == l_pkey(sv)[l] ==> a == part_of(sv, l),
{
    let a0 = part_of(sv, l);
    assert forall|a: int| 0 <= a < n_p(sv) && #[trigger] p_key(sv)[a] == l_pkey(sv)[l] implies a == a0 by {
        if a != a0 {
            assert(p_key(sv)[a] == p_key(sv)[a0]);
        }
    }
}

/// A part row holding row `l`'s key is its part row.
pub proof fn lemma_part_is(sv: StoresView, l: int, a: int)
    requires keys_unique(p_key(sv)), 0 <= a < n_p(sv), p_key(sv)[a] == l_pkey(sv)[l],
    ensures has_part(sv, l), part_of(sv, l) == a,
{
    assert(has_part(sv, l));
    lemma_part_of(sv, l);
}

/// The joined row of a lineitem row and its part row satisfies the condition exactly when the row qualifies.
pub proof fn lemma_row2_part(sv: StoresView, ps: Seq<Literal>, l: int)
    requires keys_unique(p_key(sv)), 0 <= l < n_l(sv), has_part(sv, l),
    ensures (jq(sv, ps))(row2(sv, l, part_of(sv, l))) == qual(sv, ps, l),
{
    lemma_part_of(sv, l);
    lemma_row2(sv, l, part_of(sv, l));
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

/// Joined-row terms of the result (zero off the condition).
pub open spec fn jt_cnt(sv: StoresView, ps: Seq<Literal>) -> spec_fn(Row) -> int {
    |x: Row| if (jq(sv, ps))(x) { 1int } else { 0int }
}
pub open spec fn jt_price(sv: StoresView, ps: Seq<Literal>) -> spec_fn(Row) -> int {
    |x: Row| if (jq(sv, ps))(x) { ival(x[5]) } else { 0int }
}

/// A joined-row term vanishing off the condition sums, over the kept rows, to the range sum of `f`.
proof fn lemma_term(sv: StoresView, ps: Seq<Literal>, jt: spec_fn(Row) -> int, f: spec_fn(int) -> int)
    requires
        keys_unique(p_key(sv)),
        forall|x: Row| !(#[trigger] (jq(sv, ps))(x)) ==> jt(x) == 0,
        forall|l: int| 0 <= l < n_l(sv) ==> #[trigger] f(l) == if has_part(sv, l) { jt(row2(sv, l, part_of(sv, l))) } else { 0 },
    ensures sum_of(keep(jrows(sv), jq(sv, ps)), jt) == range_sum(0, n_l(sv) as int, f),
{
    let rows = jrows(sv);
    assert forall|i: int| 0 <= i < rows.len() && !(jq(sv, ps))(#[trigger] rows[i]) implies jt(rows[i]) == 0 by {}
    lemma_sum_of_keep(rows, jq(sv, ps), jt);
    assert forall|l: int, a: int| 0 <= l < n_l(sv) && 0 <= a < n_p(sv) && jt(#[trigger] row2(sv, l, a)) != 0
        implies p_key(sv)[a] == l_pkey(sv)[l] by {
        let x = row2(sv, l, a);
        lemma_row2(sv, l, a);
        if !(jq(sv, ps))(x) {
            assert(jt(x) == 0);
        }
        assert(x[16] == x[1]);
    }
    lemma_jsum(sv, jt, f);
}

/// The sums of the joined-row terms over the kept rows are the per-lineitem totals.
pub proof fn lemma_kept_sums(sv: StoresView, ps: Seq<Literal>)
    requires keys_unique(p_key(sv)),
    ensures ({
        let k = keep(jrows(sv), jq(sv, ps));
        &&& sum_of(k, jt_cnt(sv, ps)) == range_sum(0, n_l(sv) as int, f_cnt(sv, ps))
        &&& sum_of(k, jt_price(sv, ps)) == range_sum(0, n_l(sv) as int, f_price(sv, ps))
    }),
{
    assert forall|l: int| 0 <= l < n_l(sv) && has_part(sv, l) implies {
        let x = row2(sv, l, part_of(sv, l));
        &&& (jq(sv, ps))(x) == qual(sv, ps, l)
        &&& ival(x[5]) == l_price(sv)[l] as int
    } by {
        lemma_row2_part(sv, ps, l);
        lemma_part_of(sv, l);
        lemma_row2(sv, l, part_of(sv, l));
    }
    lemma_term(sv, ps, jt_cnt(sv, ps), f_cnt(sv, ps));
    lemma_term(sv, ps, jt_price(sv, ps), f_price(sv, ps));
}

/// A joined row of the database that satisfies the condition.
pub open spec fn kept_ok(sv: StoresView, ps: Seq<Literal>, x: Row) -> bool {
    &&& (jq(sv, ps))(x)
    &&& exists|l: int, a: int| 0 <= l < n_l(sv) && 0 <= a < n_p(sv) && x == #[trigger] row2(sv, l, a)
}

/// Every kept row is the joined row of a lineitem row and a part row, and satisfies the condition.
pub proof fn lemma_kept_rows(sv: StoresView, ps: Seq<Literal>)
    ensures
        forall|i: int| 0 <= i < keep(jrows(sv), jq(sv, ps)).len() ==> kept_ok(sv, ps, #[trigger] keep(jrows(sv), jq(sv, ps))[i]),
{
    let rows = jrows(sv);
    let k = keep(rows, jq(sv, ps));
    lemma_keep_members(rows, jq(sv, ps));
    assert forall|i: int| 0 <= i < k.len() implies kept_ok(sv, ps, #[trigger] k[i]) by {
        assert(rows.contains(k[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == k[i];
        lemma_jrows_elem(sv, m);
    }
}

} // verus!
