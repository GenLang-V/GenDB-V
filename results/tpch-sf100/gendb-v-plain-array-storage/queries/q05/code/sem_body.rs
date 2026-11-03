//! The statement body (`GROUP BY n_name` over the WHERE over the six-way FROM) in the accumulator normal form of
//! `link::query` (`q5_spec`): its rows inside `group_caps` (`lemma_body_ok`), `Capacity` when a group's SUM mass
//! leaves `i128` (`lemma_body_capacity`), the empty result of an empty FROM (`lemma_body_empty`), and the error of
//! the timestamp bound when the FROM has a row (`lemma_body_err`).
//!
//! The normal form reads the FROM rows themselves (the projection `cols47` is the identity): the group key is
//! `[n_name]` (position 41) and the SUM argument is the coefficient of `l_extendedprice * (1 - l_discount)` at
//! scale 4, `ival(x[22]) * (100 - ival(x[23]))`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::equality::*;
use crate::exec::relational::domain::*;
use crate::link::query::*;
use crate::link::expr::{ival, i128_max, lemma_expr_col};
use crate::link::capacity::*;
use crate::bridge::collect::lemma_collect_all;
use crate::bridge::equality::same_exact_type;
use crate::gendb_entry::stores::StoresView;
use crate::agent::model::*;
use crate::agent::sem_ast::*;
use crate::agent::sem_from::*;
use crate::agent::sem_pred::*;

verus! {

// ------------------------------------------------------------------------------------------------ the normal form

/// Coefficient of `l_extendedprice * (1 - l_discount)` (scale 4) on a FROM row.
pub open spec fn rev_of(x: Row) -> int {
    ival(x[22]) * (100 - ival(x[23]))
}

/// GROUP BY key `[n_name]` of a FROM row.
pub open spec fn q5_key(x: Row) -> Row {
    seq![x[41]]
}

pub open spec fn q5_aggs() -> Seq<AggKind> {
    seq![AggKind::Sum { scale: 4 }]
}

/// Output columns: the key, then the SUM (`key ++ aggregates` unchanged).
pub open spec fn q5_outs() -> Seq<nat> {
    seq![0nat, 1nat]
}

/// The normal form of Q5 for `$1 = rp`, `$2 = pd` and the timestamp bound `t`.
pub open spec fn q5_spec(rp: Seq<u8>, pd: int, t: int) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| q5_qual(rp, pd, t, x),
        key: |x: Row| q5_key(x),
        arg: |j: int, x: Row| rev_of(x),
        aggs: q5_aggs(),
        outs: q5_outs(),
        grouped: true,
    }
}

/// The identity projection of a FROM row (47 positions).
pub open spec fn cols47() -> Seq<nat> {
    Seq::new(47, |k: int| k as nat)
}

/// A numeric(15,2) value of a well-formed database.
pub open spec fn num15_2(v: Val) -> bool {
    v is Num && v->Num_scale == 2 && -coeff_bound() < v->Num_coeff < coeff_bound()
}

/// A FROM row as the normal form reads it.
pub open spec fn row_ok(x: Row) -> bool {
    &&& x.len() == 47
    &&& num15_2(x[22])
    &&& num15_2(x[23])
    &&& x[41] is Text
}

// ------------------------------------------------------------------------------------------------ FROM rows

/// Every FROM row is well formed and is its own projection.
pub proof fn lemma_rows_ok(sv: StoresView)
    requires stores_wf(sv), vals_ok(sv),
    ensures
        forall|k: int| 0 <= k < from6(sv).len() ==> row_ok(#[trigger] from6(sv)[k]),
        proj_all(from6(sv), cols47()) == from6(sv),
{
    let rows = from6(sv);
    assert forall|k: int| 0 <= k < rows.len() implies row_ok(#[trigger] rows[k]) by {
        assert(rows.contains(rows[k]));
        lemma_from6_contains(sv, rows[k]);
        let (i, j, c, d, e, f) = choose|i: int, j: int, c: int, d: int, e: int, f: int|
            in6(sv, i, j, c, d, e, f) && rows[k] == #[trigger] row6(sv, i, j, c, d, e, f);
        lemma_row6(sv, i, j, c, d, e, f);
        assert(abs(l_ext(sv)[c] as int) < coeff_bound() && abs(l_disc(sv)[c] as int) < coeff_bound());
    }
    assert forall|k: int| 0 <= k < rows.len() implies #[trigger] proj_all(rows, cols47())[k] == rows[k] by {
        assert(row_ok(rows[k]));
        assert(proj(rows[k], cols47()) =~= rows[k]);
    }
    assert(proj_all(rows, cols47()) =~= rows);
}

/// Every FROM row is the `row6` of some index tuple in range.
pub proof fn lemma_row_is_row6(sv: StoresView, k: int) -> (t: (int, int, int, int, int, int))
    requires stores_wf(sv), 0 <= k < from6(sv).len(),
    ensures in6(sv, t.0, t.1, t.2, t.3, t.4, t.5), from6(sv)[k] == row6(sv, t.0, t.1, t.2, t.3, t.4, t.5),
{
    let rows = from6(sv);
    assert(rows.contains(rows[k]));
    lemma_from6_contains(sv, rows[k]);
    choose|i: int, j: int, c: int, d: int, e: int, f: int| in6(sv, i, j, c, d, e, f) && rows[k] == #[trigger] row6(sv, i, j, c, d, e, f)
}

// ------------------------------------------------------------------------------------------------ WHERE

/// With the timestamp bound `t`, the WHERE agrees with the normal form on every FROM row.
pub proof fn lemma_pred_agrees(db: Database, sv: StoresView, ps: Seq<Literal>, rp: Seq<u8>, pd: int, t: int)
    requires stores_wf(sv), vals_ok(sv), params_are(ps, rp, pd), hi_res(pd) == Ok::<int, SqlError>(t),
    ensures pred_agrees(db, from6(sv), cols47(), where_pred(ps), q5_spec(rp, pd, t)),
{
    let rows = from6(sv);
    let g = q5_spec(rp, pd, t);
    lemma_rows_ok(sv);
    assert forall|k: int| 0 <= k < rows.len() implies
        eval_pred(db, #[trigger] rows[k], where_pred(ps)) == Ok::<Truth, SqlError>(truth_of((g.qual)(proj(rows[k], cols47())))) by {
        let tu = lemma_row_is_row6(sv, k);
        lemma_where_row(db, sv, ps, rp, pd, tu.0, tu.1, tu.2, tu.3, tu.4, tu.5);
        assert(proj_all(rows, cols47())[k] == proj(rows[k], cols47()));
    }
}

/// The WHERE of the body keeps the FROM rows the normal form qualifies.
pub proof fn lemma_input(db: Database, sv: StoresView, ps: Seq<Literal>, rp: Seq<u8>, pd: int, t: int)
    requires
        tables_of(sv, db), stores_wf(sv), vals_ok(sv), params_are(ps, rp, pd),
        hi_res(pd) == Ok::<int, SqlError>(t) || from6(sv).len() == 0,
    ensures
        eval_query(db, Seq::empty(), filtered(ps))
            == Ok::<Relation, SqlError>(keep_true(from6(sv), qual_truths(q5_spec(rp, pd, t), proj_all(from6(sv), cols47())))),
{
    lemma_eval_from6(db, sv);
    let g = q5_spec(rp, pd, t);
    if hi_res(pd) == Ok::<int, SqlError>(t) {
        lemma_pred_agrees(db, sv, ps, rp, pd, t);
    }
    assert(pred_agrees(db, from6(sv), cols47(), where_pred(ps), g));
    lemma_filter_rows(db, from_q(), from6(sv), cols47(), where_pred(ps), g);
}

// ------------------------------------------------------------------------------------------------ keys, arguments

/// `pow10` at the small exponents the per-row arithmetic uses.
pub proof fn lemma_pow10_small()
    ensures
        pow10(0) == 1,
        pow10(1) == 10,
        pow10(2) == 100,
        pow10(15) == 1_000_000_000_000_000,
        pow10(16) == 10_000_000_000_000_000,
{
    assert(pow10(0) == 1) by (compute);
    assert(pow10(1) == 10) by (compute);
    assert(pow10(2) == 100) by (compute);
    assert(pow10(15) == 1_000_000_000_000_000) by (compute);
    assert(pow10(16) == 10_000_000_000_000_000) by (compute);
}

/// `1::numeric` is `Num { 1, 0 }`.
pub proof fn lemma_eval_one(db: Database, env: Row)
    ensures eval_expr(db, env, e_one()) == Ok::<Val, SqlError>(Val::Num { coeff: 1, scale: 0 }),
{
    let l = Literal::Int { v: 1, kind: IntKind::Int4 };
    assert(int_in_range(IntKind::Int4, 1));
    assert(lit_val(l) == Ok::<Val, SqlError>(Val::Int(1)));
    assert(eval_expr(db, env, Expr::Lit(l)) == Ok::<Val, SqlError>(Val::Int(1)));
    assert(cast(CastOp::IntToNumeric, Val::Int(1)) == Ok::<Val, SqlError>(Val::Num { coeff: 1, scale: 0 }));
}

/// `l_extendedprice * (1 - l_discount)` on a well-formed FROM row.
pub proof fn lemma_eval_rev(db: Database, x: Row)
    requires row_ok(x),
    ensures
        eval_expr(db, x, e_rev()) == Ok::<Val, SqlError>(Val::Num { coeff: rev_of(x), scale: 4 }),
        abs(rev_of(x)) < pow10(31),
{
    lemma_pow10_small();
    lemma_eval_one(db, x);
    let e = x[22]->Num_coeff;
    let dc = x[23]->Num_coeff;
    lemma_expr_col(db, x, 22);
    lemma_expr_col(db, x, 23);
    assert(max_nat(0, 2) == 2);
    lemma_node_add(db, x, ArithOp::Sub, e_one(), Expr::Col(23), 1, 0, 1, dc, 2, 15, 2, 100, 1, 16);
    let sub = Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(e_one()), b: Box::new(Expr::Col(23)) };
    assert(eval_expr(db, x, sub) == Ok::<Val, SqlError>(Val::Num { coeff: 100 - dc, scale: 2 }));
    lemma_node_mul(db, x, Expr::Col(22), sub, e, 2, 15, 100 - dc, 2, 16);
}

/// The aggregate arguments on one well-formed row are the normal form's argument values.
pub proof fn lemma_args_row(db: Database, x: Row, g: QuerySpec)
    requires row_ok(x), g.aggs == q5_aggs(), forall|j: int, y: Row| #[trigger] (g.arg)(j, y) == rev_of(y),
    ensures agg_args(db, x, ast_aggs()) == Ok::<Row, SqlError>(arg_vals(g, x)),
{
    let aggs = ast_aggs();
    lemma_agg_arg_results_index(db, x, aggs);
    lemma_agg_arg_sum(db, x, NumKind::Numeric, e_rev());
    lemma_eval_rev(db, x);
    let rs = agg_arg_results(db, x, aggs);
    let vals = arg_vals(g, x);
    assert(vals.len() == 1);
    assert(vals[0] == Val::Num { coeff: rev_of(x), scale: 4 });
    assert(rs[0] == Ok::<Val, SqlError>(vals[0]));
    lemma_collect_all(rs, vals);
    lemma_agg_args(db, x, aggs);
}

/// The key expression on one row is the normal form's key.
pub proof fn lemma_keys_row(db: Database, x: Row)
    requires row_ok(x),
    ensures eval_exprs(db, x, ast_keys()) == Ok::<Row, SqlError>(q5_key(x)),
{
    assert(ast_keys() =~= col_exprs(seq![41nat]));
    lemma_eval_cols(db, x, seq![41nat]);
    assert(select(x, seq![41nat]) =~= q5_key(x));
}

/// Per-row agreement of the keys and the aggregate arguments on every FROM row.
pub proof fn lemma_agree(db: Database, sv: StoresView, rp: Seq<u8>, pd: int, t: int)
    requires stores_wf(sv), vals_ok(sv),
    ensures
        keys_agree(db, from6(sv), cols47(), ast_keys(), q5_spec(rp, pd, t)),
        args_agree(db, from6(sv), cols47(), ast_aggs(), q5_spec(rp, pd, t)),
{
    hide(eval_exprs);
    hide(agg_args);
    let g = q5_spec(rp, pd, t);
    let rows = from6(sv);
    lemma_rows_ok(sv);
    assert forall|k: int| 0 <= k < rows.len() && (g.qual)(proj(#[trigger] rows[k], cols47())) implies
        eval_exprs(db, rows[k], ast_keys()) == Ok::<Row, SqlError>((g.key)(proj(rows[k], cols47()))) by {
        assert(proj_all(rows, cols47())[k] == proj(rows[k], cols47()));
        lemma_keys_row(db, rows[k]);
    }
    assert forall|k: int| 0 <= k < rows.len() && (g.qual)(proj(#[trigger] rows[k], cols47())) implies
        agg_args(db, rows[k], ast_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[k], cols47()))) by {
        assert(proj_all(rows, cols47())[k] == proj(rows[k], cols47()));
        lemma_args_row(db, rows[k], g);
    }
}

/// The aggregate list matches the normal form's kinds.
pub proof fn lemma_aggs_match(rp: Seq<u8>, pd: int, t: int)
    ensures aggs_match(ast_aggs(), q5_spec(rp, pd, t)),
{
    let g = q5_spec(rp, pd, t);
    assert forall|j: int| 0 <= j < ast_aggs().len() implies agg_matches(#[trigger] ast_aggs()[j], g.aggs[j]) by {
        assert(j == 0);
    }
}

/// On the FROM rows, SQL "not distinct" of the keys is structural equality (text keys).
pub proof fn lemma_keys_exact(sv: StoresView, rp: Seq<u8>, pd: int, t: int)
    requires stores_wf(sv), vals_ok(sv),
    ensures keys_exact(q5_spec(rp, pd, t), from6(sv)),
{
    let g = q5_spec(rp, pd, t);
    let xs = from6(sv);
    lemma_rows_ok(sv);
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        let ka = (g.key)(xs[a]);
        let kb = (g.key)(xs[b]);
        assert(row_ok(xs[a]) && row_ok(xs[b]));
        assert forall|i: int| 0 <= i < ka.len() implies same_exact_type(#[trigger] ka[i], kb[i]) by {
            assert(i == 0);
        }
        lemma_row_exact(ka, kb);
    }
}

// ------------------------------------------------------------------------------------------------ the body

/// Inside `group_caps`, the body is the normal form's result rows.
pub proof fn lemma_body_ok(db: Database, sv: StoresView, ps: Seq<Literal>, rp: Seq<u8>, pd: int, t: int)
    requires
        tables_of(sv, db), stores_wf(sv), vals_ok(sv), params_are(ps, rp, pd),
        hi_res(pd) == Ok::<int, SqlError>(t) || from6(sv).len() == 0,
        group_caps(q5_spec(rp, pd, t), from6(sv)),
    ensures eval_query(db, Seq::empty(), body(ps)) == Ok::<Relation, SqlError>(result_rows(q5_spec(rp, pd, t), from6(sv))),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_exprs);
    hide(agg_args);
    let g = q5_spec(rp, pd, t);
    let cols = cols47();
    let xs = from6(sv);
    lemma_rows_ok(sv);
    lemma_input(db, sv, ps, rp, pd, t);
    lemma_agree(db, sv, rp, pd, t);
    lemma_aggs_match(rp, pd, t);
    lemma_keys_exact(sv, rp, pd, t);
    lemma_group_query(db, xs, cols, filtered(ps), ast_keys(), ast_aggs(), g);
    let ks = gkeys(g, xs);
    let fulls = ks.map_values(|k: Row| full_row(g, xs, k));
    let outs = ks.map_values(|k: Row| out_row(g, xs, k));
    assert forall|i: int| 0 <= i < ks.len() implies #[trigger] fulls[i] == outs[i] by {
        let k = ks[i];
        assert(ks.contains(k));
        lemma_gkeys_witness(g, xs, k);
        let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], k);
        assert(k == q5_key(xs[m]));
        assert(k.len() == 1);
        lemma_select_identity(full_row(g, xs, k), q5_outs());
    }
    assert(fulls =~= outs);
    assert(body(ps) == Query::GroupBy { keys: ast_keys(), aggs: ast_aggs(), input: Box::new(filtered(ps)) });
}

/// An empty FROM makes the body's value the empty relation (whatever the timestamp bound).
pub proof fn lemma_body_empty(db: Database, sv: StoresView, ps: Seq<Literal>, rp: Seq<u8>, pd: int)
    requires tables_of(sv, db), stores_wf(sv), vals_ok(sv), params_are(ps, rp, pd), from6(sv).len() == 0,
    ensures eval_query(db, Seq::empty(), body(ps)) == Ok::<Relation, SqlError>(Seq::<Row>::empty()),
{
    let g = q5_spec(rp, pd, 0);
    lemma_caps_empty(g);
    assert(from6(sv) =~= Seq::<Row>::empty());
    lemma_body_ok(db, sv, ps, rp, pd, 0);
    assert(gkeys(g, from6(sv)) =~= Seq::<Row>::empty());
    assert(result_rows(g, from6(sv)) =~= Seq::<Row>::empty());
}

/// Without the timestamp bound, a non-empty FROM makes the body's value that bound's error.
pub proof fn lemma_body_err(db: Database, sv: StoresView, ps: Seq<Literal>, rp: Seq<u8>, pd: int, e: SqlError)
    requires
        tables_of(sv, db), stores_wf(sv), params_are(ps, rp, pd),
        hi_res(pd) == Err::<int, SqlError>(e),
        from6(sv).len() > 0,
    ensures eval_query(db, Seq::empty(), body(ps)) == Err::<Relation, SqlError>(e),
{
    hide(eval_pred);
    let ctx = Seq::<Val>::empty();
    let rows = from6(sv);
    lemma_eval_from6(db, sv);
    assert forall|k: int| 0 <= k < rows.len() implies #[trigger] eval_pred(db, ctx + rows[k], where_pred(ps)) is Ok
        || eval_pred(db, ctx + rows[k], where_pred(ps)) == Err::<Truth, SqlError>(e) by {
        let tu = lemma_row_is_row6(sv, k);
        assert(ctx + rows[k] =~= rows[k]);
        lemma_where_row(db, sv, ps, rp, pd, tu.0, tu.1, tu.2, tu.3, tu.4, tu.5);
    }
    let tu = lemma_row_is_row6(sv, 0);
    assert(ctx + rows[0] =~= rows[0]);
    lemma_where_row(db, sv, ps, rp, pd, tu.0, tu.1, tu.2, tu.3, tu.4, tu.5);
    lemma_filter_err(db, ctx, where_pred(ps), Box::new(from_q()), rows, e, 0);
    lemma_first_input(db, ctx, body(ps));
}

// ------------------------------------------------------------------------------------------------ capacity

/// The GROUP BY's prepared inputs and groups in normal-form terms: the keys and argument rows of the kept rows are
/// `qkeys` and the qualifying rows' `arg_vals`; their distinct keys are `gkeys`; every group's members are `members`.
pub proof fn lemma_groups_setup(db: Database, sv: StoresView, ps: Seq<Literal>, rp: Seq<u8>, pd: int, t: int)
    requires
        tables_of(sv, db), stores_wf(sv), vals_ok(sv), params_are(ps, rp, pd),
        hi_res(pd) == Ok::<int, SqlError>(t),
    ensures ({
        let g = q5_spec(rp, pd, t);
        let xs = from6(sv);
        let kept = keep_true(xs, qual_truths(g, xs));
        let ks = qkeys(g, xs);
        let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
        &&& eval_query(db, Seq::empty(), filtered(ps)) == Ok::<Relation, SqlError>(kept)
        &&& ks.len() == kept.len()
        &&& args.len() == kept.len()
        &&& forall|i: int| 0 <= i < kept.len() ==> #[trigger] group_input(db, Seq::<Val>::empty() + kept[i], ast_keys(), ast_aggs())
                == Ok::<(Row, Row), SqlError>((ks[i], args[i]))
        &&& distinct_rows(ks) == gkeys(g, xs)
        &&& forall|k: Row| #[trigger] gkeys(g, xs).contains(k) ==> group_members(ks, args, k) == members(g, xs, k)
    }),
{
    hide(eval_query);
    hide(eval_exprs);
    hide(agg_args);
    hide(group_input);
    let g = q5_spec(rp, pd, t);
    let cols = cols47();
    let xs = from6(sv);
    lemma_rows_ok(sv);
    lemma_input(db, sv, ps, rp, pd, t);
    lemma_kept_rows(g, xs, cols);
    let kept = keep_true(xs, qual_truths(g, xs));
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    assert(proj_all(kept, cols).len() == kept.len());
    assert forall|i: int| 0 <= i < kept.len() implies #[trigger] group_input(db, Seq::<Val>::empty() + kept[i], ast_keys(), ast_aggs())
        == Ok::<(Row, Row), SqlError>((ks[i], args[i])) by {
        assert(Seq::<Val>::empty() + kept[i] =~= kept[i]);
        assert(xs.contains(kept[i]));
        let m = choose|m: int| 0 <= m < xs.len() && xs[m] == kept[i];
        assert(row_ok(xs[m]));
        lemma_keys_row(db, kept[i]);
        lemma_args_row(db, kept[i], g);
        lemma_group_input_unfold(db, kept[i], ast_keys(), ast_aggs());
        assert(proj(kept[i], cols) == qrows(g, xs)[i]);
        assert(proj(kept[i], cols) =~= kept[i]);
    }
    lemma_keys_exact(sv, rp, pd, t);
    let pool = key_pool(g, xs);
    lemma_pool_exact(g, xs);
    assert forall|i: int| 0 <= i < qkeys(g, xs).len() implies pool.contains(#[trigger] qkeys(g, xs)[i]) by {
        assert(pool[i] == qkeys(g, xs)[i]);
    }
    lemma_distinct_gkeys(g, xs, pool);
    assert forall|k: Row| #[trigger] gkeys(g, xs).contains(k) implies group_members(ks, args, k) == members(g, xs, k) by {
        let i = choose|i: int| 0 <= i < gkeys(g, xs).len() && gkeys(g, xs)[i] == k;
        assert(pool.contains(gkeys(g, xs)[i]));
        lemma_group_members(g, xs, k, pool);
    }
}

/// The members of a group: their SUM argument column is numeric at scale 4, with absolute mass `gabs`.
proof fn lemma_members_mass(g: QuerySpec, xs: Seq<Row>, k: Row)
    requires g.aggs == q5_aggs(),
    ensures ({
        let vs = column(members(g, xs, k), 0);
        &&& forall|i: int| 0 <= i < vs.len() ==> (#[trigger] vs[i] matches Val::Num { coeff, scale: s } ==> s == 4)
        &&& forall|i: int| 0 <= i < vs.len() ==> #[trigger] vs[i] is Num
        &&& num_mass_at(vs, 4) == gabs(g, xs, k, 0)
    }),
    decreases xs.len(),
{
    let vs = column(members(g, xs, k), 0);
    if xs.len() > 0 {
        let xi = xs.drop_last();
        let x = xs.last();
        lemma_members_mass(g, xi, k);
        let vsi = column(members(g, xi, k), 0);
        if hit(g, x, k) {
            assert(vs =~= vsi.push(arg_vals(g, x)[0]));
            assert(vs.drop_last() =~= vsi);
            assert(arg_vals(g, x)[0] == Val::Num { coeff: (g.arg)(0, x), scale: 4 });
            assert((4 - 4) as nat == 0nat);
            assert(pow10(0) == 1);
            assert(abs((g.arg)(0, x)) * pow10(0) == abs((g.arg)(0, x)));
        } else {
            assert(vs =~= vsi);
        }
    } else {
        assert(vs =~= Seq::<Val>::empty());
    }
}

/// The SUM capacity condition of a non-empty group's argument column is its `gabs` bound.
proof fn lemma_members_mass_fits(g: QuerySpec, xs: Seq<Row>, k: Row)
    requires g.aggs == q5_aggs(), gcount(g, xs, k) > 0,
    ensures sum_mass_fits(NumKind::Numeric, column(members(g, xs, k), 0)) == (gabs(g, xs, k, 0) <= i128_max()),
{
    let vs = column(members(g, xs, k), 0);
    lemma_members_mass(g, xs, k);
    lemma_members_col(g, xs, k, 0);
    lemma_num_mass_uniform(vs, 4);
    assert(vs.len() > 0);
    assert(vs[0] is Num);
    assert(num_max_scale(vs) == 4);
}

/// Inside its capacity condition the SUM of every group succeeds.
proof fn lemma_aggs_ok_inside(g: QuerySpec, xs: Seq<Row>, k: Row)
    requires g.aggs == q5_aggs(),
    ensures aggs_ok_inside(ast_aggs(), members(g, xs, k)),
{
    let m = members(g, xs, k);
    let aggs = ast_aggs();
    assert forall|j: int| 0 <= j < aggs.len() && #[trigger] fits_agg_value(aggs[j], column(m, j))
        implies agg_value(aggs[j], column(m, j)) is Ok by {
        assert(j == 0);
        lemma_members_col(g, xs, k, 0);
        lemma_sum_inside_ok(NumKind::Numeric, e_rev(), column(m, 0));
    }
}

/// A group whose SUM mass leaves `i128` puts the statement outside the capacity domain.
pub proof fn lemma_body_capacity(db: Database, sv: StoresView, ps: Seq<Literal>, rp: Seq<u8>, pd: int, t: int, k: Row)
    requires
        tables_of(sv, db), stores_wf(sv), vals_ok(sv), params_are(ps, rp, pd),
        hi_res(pd) == Ok::<int, SqlError>(t),
        gcount(q5_spec(rp, pd, t), from6(sv), k) > 0,
        gabs(q5_spec(rp, pd, t), from6(sv), k, 0) > i128_max(),
    ensures !fits_query(db, Seq::empty(), body(ps)),
{
    hide(eval_query);
    hide(group_input);
    let g = q5_spec(rp, pd, t);
    let xs = from6(sv);
    let kept = keep_true(xs, qual_truths(g, xs));
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    let ctx = Seq::<Val>::empty();
    lemma_groups_setup(db, sv, ps, rp, pd, t);
    lemma_gkeys(g, xs);
    let ds = distinct_rows(ks);
    assert(ds.contains(k));
    let gi = choose|gi: int| 0 <= gi < ds.len() && ds[gi] == k;
    assert forall|h: int| 0 <= h < ds.len() implies #[trigger] aggs_ok_inside(ast_aggs(), group_members(ks, args, ds[h])) by {
        assert(ds.contains(ds[h]));
        lemma_aggs_ok_inside(g, xs, ds[h]);
    }
    let vs = column(members(g, xs, k), 0);
    lemma_members_col(g, xs, k, 0);
    lemma_members_mass_fits(g, xs, k);
    assert(!fits_agg_value(ast_aggs()[0], vs));
    assert(group_members(ks, args, ds[gi]) == members(g, xs, k));
    lemma_group_by_capacity(db, ctx, ast_keys(), ast_aggs(), Box::new(filtered(ps)), kept, ks, args, gi, 0);
    assert(body(ps) == Query::GroupBy { keys: ast_keys(), aggs: ast_aggs(), input: Box::new(filtered(ps)) });
}

} // verus!
