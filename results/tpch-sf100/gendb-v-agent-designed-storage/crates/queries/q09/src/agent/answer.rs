//! The Q9 statement's meaning on a database bound to the parts. When LIKE raises on no FROM row
//! (`no_like_err`), the WHERE keeps the FROM rows whose read columns qualify (`lemma_filter_eval`), the derived
//! table is their `sel_row`s (`lemma_project_eval_all`), and the GROUP BY (`g2`: key `(nation, o_year)`, SUM of the
//! amount at scale 4) has one row per key with a joining lineitem row; its count, sum and absolute sum are the
//! model's lineitem sums `kcnt`, `ksum`, `kabs` (`lemma_accs`). Inside the SUM capacity condition (`caps_ok`) the
//! body is those rows (`lemma_q9_denote`), so a duplicate-free sequence of exactly the rows `krow(k)` of the keys
//! with `kcnt(k) > 0`, sorted by nation, o_year DESC, is an allowed output (`lemma_q9_ordered`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::order::*;
use crate::spec::relation::{keep_true, collect};
use crate::spec::equality::row_not_distinct;
use crate::query::{query_spec_at, param_domain};
use crate::link::query::*;
use crate::link::join::{sum_of, keep, sum_term, count_term, abs_term, lemma_acc_sum_of, lemma_sum_of_map, lemma_sum_of_keep,
    lemma_sum_of_ext, lemma_keep_true_keep, lemma_keep_members};
use crate::link::source::lemma_proj_all_index;
use crate::link::outcome::lemma_outcome_sorted;
use crate::link::expr::{ival, i128_max};
use crate::bridge::equality::same_exact_type;
use crate::bridge::collect::lemma_collect_all;
use super::common::isum::*;
use super::model::*;
use super::qspec::*;
use super::sqlrow::*;
use super::sqllink::*;
use super::sqlsum::*;

verus! {

// ------------------------------------------------------------------------------------------------ the groups in model terms

pub open spec fn kcnt_f(m: M, p: QP, k: Row) -> spec_fn(int) -> int {
    |j: int| if jok(m, p, j) && jkey(m, j) == k { 1int } else { 0int }
}

pub open spec fn ksum_f(m: M, p: QP, k: Row) -> spec_fn(int) -> int {
    |j: int| if jok(m, p, j) && jkey(m, j) == k { jamt(m, j) } else { 0int }
}

pub open spec fn kabs_f(m: M, p: QP, k: Row) -> spec_fn(int) -> int {
    |j: int| if jok(m, p, j) && jkey(m, j) == k { abs(jamt(m, j)) } else { 0int }
}

/// The joining lineitem rows of group key `k`: their number, the sum and the absolute sum of their amounts.
pub open spec fn kcnt(m: M, p: QP, k: Row) -> int { isum(m.l_n, kcnt_f(m, p, k)) }
pub open spec fn ksum(m: M, p: QP, k: Row) -> int { isum(m.l_n, ksum_f(m, p, k)) }
pub open spec fn kabs(m: M, p: QP, k: Row) -> int { isum(m.l_n, kabs_f(m, p, k)) }

/// The result row of group key `k`.
pub open spec fn krow(m: M, p: QP, k: Row) -> Row {
    k + seq![Val::Num { coeff: ksum(m, p, k), scale: 4 }]
}

/// Every group's absolute amount mass is inside `i128` (the SUM capacity condition).
pub open spec fn caps_ok(m: M, p: QP) -> bool {
    forall|k: Row| #[trigger] kabs(m, p, k) <= i128_max()
}

/// LIKE raises on no FROM row: on no part name, or the FROM product is empty.
pub open spec fn no_like_err(m: M, p: QP) -> bool {
    like_total(m, p) || m.p_n == 0 || m.s_n == 0 || m.l_n == 0 || m.t_n == 0 || m.o_n == 0 || m.n_n == 0
}

/// The facts of a database bound to the parts, at one binding.
pub open spec fn bound_ok(db: Database, m: M, ps: Seq<Literal>) -> bool {
    &&& db_ok(db)
    &&& rel_ok(m, db)
    &&& model_ok(m)
    &&& param_domain(ps)
}

// ------------------------------------------------------------------------------------------------ WHERE and SELECT

/// The WHERE in normal form (only its condition is used).
pub open spec fn g1(p: QP) -> QuerySpec {
    QuerySpec { qual: |x: Row| qual_x(p, x), key: |x: Row| Seq::<Val>::empty(), arg: |j: int, x: Row| 0int,
        aggs: Seq::empty(), outs: Seq::empty(), grouped: false }
}

/// The FROM rows the WHERE keeps.
pub open spec fn kept_rows(db: Database, p: QP) -> Seq<Row> {
    keep(from_rows(db), |r: Row| qual_x(p, proj(r, q9_cols())))
}

/// The derived table.
pub open spec fn prows(db: Database, p: QP) -> Seq<Row> {
    kept_rows(db, p).map_values(|r: Row| sel_row(proj(r, q9_cols())))
}

/// Every FROM row reads a typed joined model row whose LIKE does not raise.
proof fn lemma_row_facts(db: Database, m: M, ps: Seq<Literal>, i: int)
    requires bound_ok(db, m, ps), no_like_err(m, qp_of(ps)), 0 <= i < from_rows(db).len(),
    ensures
        env_reads(from_rows(db)[i], proj(from_rows(db)[i], q9_cols())),
        xrow_typed(proj(from_rows(db)[i], q9_cols())),
        like_x(qp_of(ps), proj(from_rows(db)[i], q9_cols())) is Ok,
{
    let (c, s, j, t, q, n) = lemma_from_row(db, m, i);
    lemma_jrow_typed(m, c, s, j, t, q, n);
    let x = jrow(m, c, s, j, t, q, n);
    assert(like_x(qp_of(ps), x) == plike(m, qp_of(ps), c));
}

/// The WHERE keeps the FROM rows whose read columns qualify.
pub proof fn lemma_filter_eval(db: Database, m: M, ps: Seq<Literal>)
    requires bound_ok(db, m, ps), no_like_err(m, qp_of(ps)),
    ensures eval_query(db, Seq::empty(), q9_filter(ps)) == Ok::<Relation, SqlError>(kept_rows(db, qp_of(ps))),
{
    let p = qp_of(ps);
    let rows = from_rows(db);
    let cols = q9_cols();
    lemma_widths(db);
    lemma_from_eval(db);
    assert forall|i: int| 0 <= i < rows.len() implies
        eval_pred(db, #[trigger] rows[i], q9_pred(ps)) == Ok::<Truth, SqlError>(truth_of((g1(p).qual)(proj(rows[i], cols)))) by {
        lemma_row_facts(db, m, ps, i);
        lemma_pred_eval(db, rows[i], proj(rows[i], cols), ps);
    }
    lemma_filter_rows(db, q9_from(), rows, cols, q9_pred(ps), g1(p));
    let xs = proj_all(rows, cols);
    let truths = qual_truths(g1(p), xs);
    lemma_proj_all_index(rows, cols);
    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] truths[i] == truth_of((|r: Row| qual_x(p, proj(r, cols)))(rows[i])) by {}
    lemma_keep_true_keep(rows, truths, |r: Row| qual_x(p, proj(r, cols)));
}

/// The SELECT list over the kept rows.
pub proof fn lemma_project_eval_all(db: Database, m: M, ps: Seq<Literal>)
    requires bound_ok(db, m, ps), no_like_err(m, qp_of(ps)),
    ensures eval_query(db, Seq::empty(), q9_project(ps)) == Ok::<Relation, SqlError>(prows(db, qp_of(ps))),
{
    let p = qp_of(ps);
    let rows = from_rows(db);
    let cols = q9_cols();
    let kept = kept_rows(db, p);
    lemma_filter_eval(db, m, ps);
    lemma_keep_members(rows, |r: Row| qual_x(p, proj(r, cols)));
    let ctx = Seq::<Val>::empty();
    let rs = Seq::new(kept.len(), |i: int| eval_exprs(db, ctx + kept[i], q9_exprs()));
    let vs = prows(db, p);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(vs[i]) by {
        assert(ctx + kept[i] =~= kept[i]);
        assert(rows.contains(kept[i]));
        let t = choose|t: int| 0 <= t < rows.len() && rows[t] == kept[i];
        lemma_row_facts(db, m, ps, t);
        lemma_project_eval(db, rows[t], proj(rows[t], cols));
    }
    lemma_collect_all(rs, vs);
    crate::exec::relational::domain::lemma_collect_pointwise::<Row>();
}

// ------------------------------------------------------------------------------------------------ GROUP BY

/// The GROUP BY in normal form over the derived table.
pub open spec fn g2() -> QuerySpec {
    QuerySpec { qual: |y: Row| true, key: |y: Row| seq![y[0], y[1]], arg: |j: int, y: Row| ival(y[2]),
        aggs: seq![AggKind::Sum { scale: 4 }], outs: seq![0nat, 1, 2], grouped: true }
}

pub open spec fn cols3() -> Seq<nat> {
    seq![0nat, 1, 2]
}

/// A derived-table row is its own projection on its three columns.
proof fn lemma_proj3(y: Row)
    requires y.len() == 3,
    ensures proj(y, cols3()) == y,
{
    assert(proj(y, cols3()) =~= y);
}

/// The derived table's rows: three columns, a text key, a year numeric of scale 0, an amount of scale 4.
pub proof fn lemma_prows_shape(db: Database, m: M, ps: Seq<Literal>)
    requires bound_ok(db, m, ps), no_like_err(m, qp_of(ps)),
    ensures
        forall|i: int| 0 <= i < prows(db, qp_of(ps)).len() ==> {
            let y = #[trigger] prows(db, qp_of(ps))[i];
            &&& y.len() == 3 && y[0] is Text
            &&& y[1] matches Val::Num { coeff, scale } && scale == 0
            &&& y[2] matches Val::Num { coeff, scale } && scale == 4
        },
        proj_all(prows(db, qp_of(ps)), cols3()) == prows(db, qp_of(ps)),
{
    let p = qp_of(ps);
    let rows = from_rows(db);
    let cols = q9_cols();
    let kept = kept_rows(db, p);
    let pr = prows(db, p);
    lemma_keep_members(rows, |r: Row| qual_x(p, proj(r, cols)));
    assert forall|i: int| 0 <= i < pr.len() implies {
        let y = #[trigger] pr[i];
        &&& y.len() == 3 && y[0] is Text
        &&& y[1] matches Val::Num { coeff, scale } && scale == 0
        &&& y[2] matches Val::Num { coeff, scale } && scale == 4
    } by {
        assert(rows.contains(kept[i]));
        let t = choose|t: int| 0 <= t < rows.len() && rows[t] == kept[i];
        lemma_row_facts(db, m, ps, t);
    }
    lemma_proj_all_index(pr, cols3());
    assert forall|i: int| 0 <= i < pr.len() implies #[trigger] proj_all(pr, cols3())[i] == pr[i] by {
        lemma_proj3(pr[i]);
    }
    assert(proj_all(pr, cols3()) =~= pr);
}

/// A sum over the derived table is a sum over the projected FROM rows that qualify.
proof fn lemma_sum_prows(db: Database, m: M, ps: Seq<Literal>, f: spec_fn(Row) -> int)
    requires bound_ok(db, m, ps), no_like_err(m, qp_of(ps)),
    ensures sum_of(prows(db, qp_of(ps)), f)
        == sum_of(xs_of(db), |x: Row| if qual_x(qp_of(ps), x) { f(sel_row(x)) } else { 0int }),
{
    let p = qp_of(ps);
    let rows = from_rows(db);
    let cols = q9_cols();
    let c = |r: Row| qual_x(p, proj(r, cols));
    let kept = keep(rows, c);
    lemma_sum_of_map(kept, |r: Row| sel_row(proj(r, cols)), f);
    let h = |r: Row| if c(r) { f(sel_row(proj(r, cols))) } else { 0int };
    lemma_sum_of_keep(rows, c, h);
    lemma_keep_members(rows, c);
    assert forall|i: int| 0 <= i < kept.len() implies (|r: Row| f((|r: Row| sel_row(proj(r, cols)))(r)))(#[trigger] kept[i]) == h(kept[i]) by {}
    lemma_sum_of_ext(kept, |r: Row| f((|r: Row| sel_row(proj(r, cols)))(r)), h);
    lemma_sum_of_map(rows, |r: Row| proj(r, cols), |x: Row| if qual_x(p, x) { f(sel_row(x)) } else { 0int });
    assert(xs_of(db) == rows.map_values(|r: Row| proj(r, cols)));
    assert forall|i: int| 0 <= i < rows.len() implies
        (|r: Row| (|x: Row| if qual_x(p, x) { f(sel_row(x)) } else { 0int })((|r: Row| proj(r, cols))(r)))(#[trigger] rows[i]) == h(rows[i]) by {}
    lemma_sum_of_ext(rows, |r: Row| (|x: Row| if qual_x(p, x) { f(sel_row(x)) } else { 0int })((|r: Row| proj(r, cols))(r)), h);
}

/// The weights: one, the amount, its absolute value.
pub open spec fn w_one() -> spec_fn(Row) -> int { |x: Row| 1int }
pub open spec fn w_amt() -> spec_fn(Row) -> int { |x: Row| amt_x(x) }
pub open spec fn w_abs() -> spec_fn(Row) -> int { |x: Row| abs(amt_x(x)) }

/// The collapsed terms are the model's group terms.
proof fn lemma_jterms(m: M, p: QP, k: Row)
    requires model_ok(m),
    ensures
        isum(m.l_n, jterm(m, p, k, w_one())) == kcnt(m, p, k),
        isum(m.l_n, jterm(m, p, k, w_amt())) == ksum(m, p, k),
        isum(m.l_n, jterm(m, p, k, w_abs())) == kabs(m, p, k),
{
    assert forall|j: int| 0 <= j < m.l_n implies #[trigger] jterm(m, p, k, w_amt())(j) == ksum_f(m, p, k)(j) by {
        if jok(m, p, j) {
            super::lookups::lemma_ppos(m, lpk(m, j), 0);
            super::lookups::lemma_spos(m, lsk(m, j), 0);
            super::lookups::lemma_tpos(m, lpk(m, j), lsk(m, j), 0);
            super::lookups::lemma_opos(m, lok(m, j), 0);
            lemma_jrow_typed(m, lc(m, j), ls(m, j), j, lt(m, j), lq(m, j), jn(m, j));
        }
    }
    assert forall|j: int| 0 <= j < m.l_n implies #[trigger] jterm(m, p, k, w_abs())(j) == kabs_f(m, p, k)(j) by {
        if jok(m, p, j) {
            super::lookups::lemma_ppos(m, lpk(m, j), 0);
            super::lookups::lemma_spos(m, lsk(m, j), 0);
            super::lookups::lemma_tpos(m, lpk(m, j), lsk(m, j), 0);
            super::lookups::lemma_opos(m, lok(m, j), 0);
            lemma_jrow_typed(m, lc(m, j), ls(m, j), j, lt(m, j), lq(m, j), jn(m, j));
        }
    }
    assert forall|j: int| 0 <= j < m.l_n implies #[trigger] jterm(m, p, k, w_one())(j) == kcnt_f(m, p, k)(j) by {}
    lemma_isum_ext(m.l_n, jterm(m, p, k, w_one()), kcnt_f(m, p, k));
    lemma_isum_ext(m.l_n, jterm(m, p, k, w_amt()), ksum_f(m, p, k));
    lemma_isum_ext(m.l_n, jterm(m, p, k, w_abs()), kabs_f(m, p, k));
}

/// The count accumulator of key `k` is the collapsed count over the lineitem rows.
proof fn lemma_acc_cnt(db: Database, m: M, ps: Seq<Literal>, k: Row)
    requires bound_ok(db, m, ps), no_like_err(m, qp_of(ps)),
    ensures sum_of(prows(db, qp_of(ps)), count_term(g2(), k)) == isum(m.l_n, jterm(m, qp_of(ps), k, w_one())),
{
    let p = qp_of(ps);
    let xs = xs_of(db);
    lemma_sum_prows(db, m, ps, count_term(g2(), k));
    lemma_proj_all_index(from_rows(db), q9_cols());
    assert forall|i: int| 0 <= i < xs.len() implies (|x: Row| if qual_x(p, x) { count_term(g2(), k)(sel_row(x)) } else { 0int })(#[trigger] xs[i]) == gterm(p, k, w_one())(xs[i]) by {
        assert(seq![sel_row(xs[i])[0], sel_row(xs[i])[1]] =~= keyx(xs[i]));
    }
    lemma_sum_of_ext(xs, |x: Row| if qual_x(p, x) { count_term(g2(), k)(sel_row(x)) } else { 0int }, gterm(p, k, w_one()));
    lemma_sum_xs(db, m, gterm(p, k, w_one()));
    lemma_collapse(m, p, k, w_one());
}

/// The sum accumulator of key `k` is the collapsed sum over the lineitem rows.
proof fn lemma_acc_sum(db: Database, m: M, ps: Seq<Literal>, k: Row)
    requires bound_ok(db, m, ps), no_like_err(m, qp_of(ps)),
    ensures sum_of(prows(db, qp_of(ps)), sum_term(g2(), k, 0)) == isum(m.l_n, jterm(m, qp_of(ps), k, w_amt())),
{
    let p = qp_of(ps);
    let xs = xs_of(db);
    lemma_sum_prows(db, m, ps, sum_term(g2(), k, 0));
    lemma_proj_all_index(from_rows(db), q9_cols());
    assert forall|i: int| 0 <= i < xs.len() implies (|x: Row| if qual_x(p, x) { sum_term(g2(), k, 0)(sel_row(x)) } else { 0int })(#[trigger] xs[i]) == gterm(p, k, w_amt())(xs[i]) by {
        assert(seq![sel_row(xs[i])[0], sel_row(xs[i])[1]] =~= keyx(xs[i]));
    }
    lemma_sum_of_ext(xs, |x: Row| if qual_x(p, x) { sum_term(g2(), k, 0)(sel_row(x)) } else { 0int }, gterm(p, k, w_amt()));
    lemma_sum_xs(db, m, gterm(p, k, w_amt()));
    lemma_collapse(m, p, k, w_amt());
}

/// The absolute accumulator of key `k` is the collapsed absolute sum over the lineitem rows.
proof fn lemma_acc_abs(db: Database, m: M, ps: Seq<Literal>, k: Row)
    requires bound_ok(db, m, ps), no_like_err(m, qp_of(ps)),
    ensures sum_of(prows(db, qp_of(ps)), abs_term(g2(), k, 0)) == isum(m.l_n, jterm(m, qp_of(ps), k, w_abs())),
{
    let p = qp_of(ps);
    let xs = xs_of(db);
    lemma_sum_prows(db, m, ps, abs_term(g2(), k, 0));
    lemma_proj_all_index(from_rows(db), q9_cols());
    assert forall|i: int| 0 <= i < xs.len() implies (|x: Row| if qual_x(p, x) { abs_term(g2(), k, 0)(sel_row(x)) } else { 0int })(#[trigger] xs[i]) == gterm(p, k, w_abs())(xs[i]) by {
        assert(seq![sel_row(xs[i])[0], sel_row(xs[i])[1]] =~= keyx(xs[i]));
    }
    lemma_sum_of_ext(xs, |x: Row| if qual_x(p, x) { abs_term(g2(), k, 0)(sel_row(x)) } else { 0int }, gterm(p, k, w_abs()));
    lemma_sum_xs(db, m, gterm(p, k, w_abs()));
    lemma_collapse(m, p, k, w_abs());
}

/// The group accumulators of the derived table are the model's lineitem sums.
pub proof fn lemma_accs(db: Database, m: M, ps: Seq<Literal>, k: Row)
    requires bound_ok(db, m, ps), no_like_err(m, qp_of(ps)),
    ensures
        gcount(g2(), prows(db, qp_of(ps)), k) == kcnt(m, qp_of(ps), k),
        gsum(g2(), prows(db, qp_of(ps)), k, 0) == ksum(m, qp_of(ps), k),
        gabs(g2(), prows(db, qp_of(ps)), k, 0) == kabs(m, qp_of(ps), k),
{
    let p = qp_of(ps);
    let pr = prows(db, p);
    lemma_acc_sum_of(g2(), pr, k, 0);
    lemma_acc_cnt(db, m, ps, k);
    lemma_acc_sum(db, m, ps, k);
    lemma_acc_abs(db, m, ps, k);
    lemma_jterms(m, p, k);
}

// ------------------------------------------------------------------------------------------------ the body and the output

/// The SUM argument list on a derived-table row is its amount.
proof fn lemma_args_one(db: Database, y: Row)
    requires y.len() == 3, y[2] matches Val::Num { coeff, scale } && scale == 4,
    ensures agg_args(db, y, q9_aggs()) == Ok::<Row, SqlError>(seq![y[2]]),
{
    let rs = agg_arg_results(db, y, q9_aggs());
    lemma_agg_arg_results_index(db, y, q9_aggs());
    assert(rs[0] == agg_arg(db, y, q9_aggs()[0]));
    assert(rs.len() == 1);
    assert(rs.drop_last().len() == 0);
    assert(collect(rs.drop_last()) == Ok::<Seq<Val>, SqlError>(Seq::empty()));
    assert(rs.last() == Ok::<Val, SqlError>(y[2]));
    assert(Seq::<Val>::empty().push(y[2]) =~= seq![y[2]]);
}

/// The GROUP BY rows of the derived table (first-occurrence order of the keys).
pub open spec fn q9_rows(db: Database, p: QP) -> Seq<Row> {
    gkeys(g2(), prows(db, p)).map_values(|k: Row| full_row(g2(), prows(db, p), k))
}

/// Rows of the derived table's shape.
pub open spec fn shaped(pr: Seq<Row>) -> bool {
    forall|i: int| 0 <= i < pr.len() ==> {
        let y = #[trigger] pr[i];
        &&& y.len() == 3 && y[0] is Text
        &&& y[1] matches Val::Num { coeff, scale } && scale == 0
        &&& y[2] matches Val::Num { coeff, scale } && scale == 4
    }
}

pub proof fn lemma_g2_keys(db: Database, pr: Seq<Row>)
    requires shaped(pr),
    ensures keys_agree(db, pr, cols3(), q9_gkeys(), g2()),
{
    let g = g2();
    assert forall|i: int| 0 <= i < pr.len() && (g.qual)(proj(#[trigger] pr[i], cols3())) implies
        eval_exprs(db, pr[i], q9_gkeys()) == Ok::<Row, SqlError>((g.key)(proj(pr[i], cols3()))) by {
        lemma_proj3(pr[i]);
        assert(q9_gkeys() =~= col_exprs(seq![0nat, 1]));
        lemma_eval_cols(db, pr[i], seq![0nat, 1]);
        assert(select(pr[i], seq![0nat, 1]) =~= seq![pr[i][0], pr[i][1]]);
    }
}

pub proof fn lemma_g2_args(db: Database, pr: Seq<Row>)
    requires shaped(pr),
    ensures args_agree(db, pr, cols3(), q9_aggs(), g2()), aggs_match(q9_aggs(), g2()),
{
    hide(agg_args);
    let g = g2();
    assert forall|i: int| 0 <= i < pr.len() && (g.qual)(proj(#[trigger] pr[i], cols3())) implies
        agg_args(db, pr[i], q9_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(pr[i], cols3()))) by {
        lemma_proj3(pr[i]);
        lemma_args_one(db, pr[i]);
        assert(arg_vals(g, pr[i]) =~= seq![pr[i][2]]);
    }
}

pub proof fn lemma_g2_exact(pr: Seq<Row>)
    requires shaped(pr),
    ensures keys_exact(g2(), pr),
{
    let g = g2();
    assert forall|a: int, b: int| 0 <= a < pr.len() && 0 <= b < pr.len() && (g.qual)(pr[a]) && (g.qual)(pr[b]) implies
        (row_not_distinct(#[trigger] (g.key)(pr[a]), #[trigger] (g.key)(pr[b])) <==> (g.key)(pr[a]) == (g.key)(pr[b])) by {
        let (ka, kb) = ((g.key)(pr[a]), (g.key)(pr[b]));
        assert(ka.len() == 2 && kb.len() == 2);
        assert forall|t: int| 0 <= t < ka.len() implies same_exact_type(#[trigger] ka[t], kb[t]) by {
            assert(t == 0 || t == 1);
        }
        lemma_row_exact(ka, kb);
    }
}

proof fn lemma_g2_caps(db: Database, m: M, ps: Seq<Literal>)
    requires bound_ok(db, m, ps), no_like_err(m, qp_of(ps)), caps_ok(m, qp_of(ps)),
    ensures group_caps(g2(), prows(db, qp_of(ps))),
{
    let g = g2();
    let p = qp_of(ps);
    let xs = prows(db, p);
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies #[trigger] gabs(g, xs, k, j) <= i128_max() by {
        assert(j == 0);
        lemma_accs(db, m, ps, k);
    }
}

/// Inside the SUM capacity condition the GROUP BY is one row per key of the derived table.
pub proof fn lemma_group_eval(db: Database, m: M, ps: Seq<Literal>)
    requires bound_ok(db, m, ps), no_like_err(m, qp_of(ps)), caps_ok(m, qp_of(ps)),
    ensures eval_query(db, Seq::empty(), q9_body(ps)) == Ok::<Relation, SqlError>(q9_rows(db, qp_of(ps))),
{
    let p = qp_of(ps);
    let pr = prows(db, p);
    let g = g2();
    lemma_project_eval_all(db, m, ps);
    lemma_prows_shape(db, m, ps);
    assert(shaped(pr));
    lemma_table_rows(db, q9_project(ps), pr, cols3(), g);
    lemma_g2_keys(db, pr);
    lemma_g2_args(db, pr);
    lemma_g2_exact(pr);
    lemma_g2_caps(db, m, ps);
    lemma_group_query(db, pr, cols3(), q9_project(ps), q9_gkeys(), q9_aggs(), g);
}

/// The rows of the GROUP BY are exactly the rows `krow(k)` of the keys with a joining lineitem row, without
/// duplicates.
pub proof fn lemma_q9_rows(db: Database, m: M, ps: Seq<Literal>)
    requires bound_ok(db, m, ps), no_like_err(m, qp_of(ps)),
    ensures
        q9_rows(db, qp_of(ps)).no_duplicates(),
        forall|r: Row| #[trigger] q9_rows(db, qp_of(ps)).contains(r) <==>
            exists|k: Row| kcnt(m, qp_of(ps), k) > 0 && r == krow(m, qp_of(ps), k),
{
    let p = qp_of(ps);
    let pr = prows(db, p);
    let g = g2();
    let gk = gkeys(g, pr);
    let rr = q9_rows(db, p);
    lemma_gkeys(g, pr);
    // a key's row is its krow
    assert forall|k: Row| gk.contains(k) implies #[trigger] full_row(g, pr, k) == krow(m, p, k) by {
        lemma_accs(db, m, ps, k);
        assert(agg_outs(g, pr, k) =~= seq![Val::Num { coeff: ksum(m, p, k), scale: 4 }]);
    }
    assert forall|r: Row| #[trigger] rr.contains(r) <==> exists|k: Row| kcnt(m, p, k) > 0 && r == krow(m, p, k) by {
        if rr.contains(r) {
            let i = choose|i: int| 0 <= i < rr.len() && rr[i] == r;
            let k = gk[i];
            assert(gk.contains(k));
            lemma_accs(db, m, ps, k);
            assert(kcnt(m, p, k) > 0 && r == krow(m, p, k));
        }
        if exists|k: Row| kcnt(m, p, k) > 0 && r == krow(m, p, k) {
            let k = choose|k: Row| kcnt(m, p, k) > 0 && r == krow(m, p, k);
            lemma_accs(db, m, ps, k);
            assert(gk.contains(k));
            let i = choose|i: int| 0 <= i < gk.len() && gk[i] == k;
            assert(rr[i] == r);
        }
    }
    assert forall|a: int, b: int| 0 <= a < rr.len() && 0 <= b < rr.len() && a != b implies rr[a] != rr[b] by {
        let (ka, kb) = (gk[a], gk[b]);
        assert(gk.contains(ka) && gk.contains(kb));
        assert(gk[a] != gk[b]);
        if rr[a] == rr[b] {
            assert(rr[a] == krow(m, p, ka) && rr[b] == krow(m, p, kb));
            lemma_gk_len(db, m, ps, ka);
            lemma_gk_len(db, m, ps, kb);
            assert(krow(m, p, ka).subrange(0, 2) =~= ka);
            assert(krow(m, p, kb).subrange(0, 2) =~= kb);
        }
    }
}

/// Every key of the derived table has two columns.
proof fn lemma_gk_len(db: Database, m: M, ps: Seq<Literal>, k: Row)
    requires bound_ok(db, m, ps), no_like_err(m, qp_of(ps)), gkeys(g2(), prows(db, qp_of(ps))).contains(k),
    ensures k.len() == 2,
{
    let pr = prows(db, qp_of(ps));
    lemma_gkeys_witness(g2(), pr, k);
    let t = choose|t: int| 0 <= t < pr.len() && #[trigger] hit(g2(), pr[t], k);
    assert((g2().key)(pr[t]) == k);
}

/// A duplicate-free sequence of exactly the group rows, sorted by nation, o_year DESC, is an allowed output.
pub proof fn lemma_q9_ordered(db: Database, m: M, ps: Seq<Literal>, out: Seq<Row>)
    requires
        bound_ok(db, m, ps), no_like_err(m, qp_of(ps)), caps_ok(m, qp_of(ps)),
        out.no_duplicates(),
        sorted_by(q9_keys(), out),
        forall|r: Row| #[trigger] out.contains(r) <==> exists|k: Row| kcnt(m, qp_of(ps), k) > 0 && r == krow(m, qp_of(ps), k),
    ensures ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    let p = qp_of(ps);
    lemma_q9_shape(ps);
    lemma_group_eval(db, m, ps);
    lemma_q9_rows(db, m, ps);
    let rr = q9_rows(db, p);
    assert forall|r: Row| out.contains(r) <==> rr.contains(r) by {}
    lemma_nodup_same_multiset(out, rr);
    lemma_outcome_sorted(db, query_spec_at(ps), rr, out);
    lemma_slice_all(out);
}

} // verus!
