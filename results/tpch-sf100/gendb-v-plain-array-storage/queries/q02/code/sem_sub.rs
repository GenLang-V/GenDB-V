//! The correlated subquery `SELECT MIN(ps_supplycost) FROM partsupp, supplier, nation, region WHERE p_partkey =
//! ps_partkey AND ..` evaluated in an outer row whose part key is `k`: its value is NULL when no partsupp row
//! offers `k` from a supplier of the region (`model::sub_ok`), otherwise the numeric (scale 2) of the least such
//! supply cost (`lemma_sub_value`). The comparison `ps_supplycost = (subquery)` with the outer row's cost `w` is
//! true exactly when `w` is that least cost (`lemma_cost_eq_min`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::aggs::minmax::*;
use crate::spec::text::lex_cmp;
use crate::link::join::keep;
use crate::link::expr::{lemma_pred_cmp, lemma_pred_text_cmp, lemma_pred_and, lemma_compare_int, int_cmp, text_cmp};
use crate::bridge::collect::{lemma_collect_all, lemma_collect_pointwise};
use crate::gendb_entry::stores::StoresView;
use crate::agent::model::*;
use crate::agent::sem_ast::*;
use crate::agent::common::relations::*;
use crate::stores::flat_partsupp::interface as psi;
use crate::stores::flat_supplier::interface as si;
use crate::stores::flat_nation::interface as ni;
use crate::stores::flat_region::interface as ri;

verus! {

/// The parameter literals of a binding: `$1` integer `v`, `$2` text `pat`, `$3` text `rp`.
pub open spec fn lits(v: int, pat: Seq<u8>, rp: Seq<u8>) -> Seq<Literal> {
    seq![Literal::Int { v, kind: IntKind::Int4 }, Literal::Text(pat), Literal::Text(rp)]
}

/// A row of the subquery's FROM: partsupp row `c`, supplier `b`, nation `d`, region `e`.
pub open spec fn row4(sv: StoresView, c: int, b: int, d: int, e: int) -> Row {
    ps_rows(sv)[c] + supp_rows(sv)[b] + nat_rows(sv)[d] + reg_rows(sv)[e]
}

pub open spec fn in4(sv: StoresView, c: int, b: int, d: int, e: int) -> bool {
    0 <= c < ps_n(sv) && 0 <= b < supp_n(sv) && 0 <= d < nat_n(sv) && 0 <= e < reg_n(sv)
}

/// The subquery's FROM relation (left-deep product).
pub open spec fn from4(sv: StoresView) -> Seq<Row> {
    product_rows(product_rows(product_rows(ps_rows(sv), supp_rows(sv)), nat_rows(sv)), reg_rows(sv))
}

/// The subquery's WHERE on its row `y`, for the outer part key `k`.
pub open spec fn sub_keep(k: int, rp: Seq<u8>) -> spec_fn(Row) -> bool {
    |y: Row| y[0] == Val::Int(k) && y[5] == y[1] && y[8] == y[12] && y[14] == y[16] && y[17] == Val::Text(rp)
}

/// The subquery's kept rows and its MIN argument values.
pub open spec fn sub_rows(sv: StoresView, k: int, rp: Seq<u8>) -> Seq<Row> {
    keep(from4(sv), sub_keep(k, rp))
}

pub open spec fn sub_vals(sv: StoresView, k: int, rp: Seq<u8>) -> Seq<Val> {
    sub_rows(sv, k, rp).map_values(|z: Row| z[3])
}

/// The value of the subquery for part key `k`.
pub open spec fn sub_value(sv: StoresView, k: int, rp: Seq<u8>) -> Val {
    if sub_vals(sv, k, rp).len() == 0 { Val::Null } else { Val::Num { coeff: min_coeff(sub_vals(sv, k, rp)), scale: 2 } }
}

/// `w` is the least supply cost of the subquery rows for `k` (and some row has it).
pub open spec fn is_min_cost(sv: StoresView, rp: Seq<u8>, k: int, w: int) -> bool {
    &&& exists|c: int| 0 <= c < ps_n(sv) && #[trigger] sub_ok(sv, rp, k, c) && ps_costs(sv)[c] == w
    &&& min_ok(sv, rp, k, w)
}

// ------------------------------------------------------------------------------------------ rows

/// The values of a subquery FROM row that the query reads.
pub proof fn lemma_row4(sv: StoresView, c: int, b: int, d: int, e: int)
    requires stores_wf(sv), in4(sv, c, b, d, e),
    ensures
        row4(sv, c, b, d, e).len() == 19,
        row4(sv, c, b, d, e)[0] == Val::Int(ps_pkeys(sv)[c] as int),
        row4(sv, c, b, d, e)[1] == Val::Int(ps_skeys(sv)[c] as int),
        row4(sv, c, b, d, e)[3] == (Val::Num { coeff: ps_costs(sv)[c] as int, scale: 2 }),
        row4(sv, c, b, d, e)[5] == Val::Int(s_keys(sv)[b] as int),
        row4(sv, c, b, d, e)[8] == Val::Int(s_nks(sv)[b] as int),
        row4(sv, c, b, d, e)[12] == Val::Int(n_keys(sv)[d] as int),
        row4(sv, c, b, d, e)[14] == Val::Int(n_rks(sv)[d] as int),
        row4(sv, c, b, d, e)[16] == Val::Int(r_keys(sv)[e] as int),
        row4(sv, c, b, d, e)[17] == Val::Text(r_name(sv, e)),
{
    let p = ps_rows(sv)[c];
    let s = supp_rows(sv)[b];
    let n = nat_rows(sv)[d];
    let r = reg_rows(sv)[e];
    assert(p == psi::row_at(sv.flat_partsupp, c));
    assert(s == si::row_at(sv.flat_supplier, b));
    assert(n == ni::row_at(sv.flat_nation, d));
    assert(r == ri::row_at(sv.flat_region, e));
    assert(p.len() == 5 && s.len() == 7 && n.len() == 4 && r.len() == 3);
    let y = row4(sv, c, b, d, e);
    assert(y[0] == p[0] && y[1] == p[1] && y[3] == p[3]);
    assert(y[5] == s[0] && y[8] == s[3]);
    assert(y[12] == n[0] && y[14] == n[2]);
    assert(y[16] == r[0] && y[17] == r[1]);
}

/// The rows of the subquery's FROM are exactly the `row4` of index tuples in range.
pub proof fn lemma_from4_contains(sv: StoresView, y: Row)
    requires stores_wf(sv),
    ensures from4(sv).contains(y) <==> exists|c: int, b: int, d: int, e: int| in4(sv, c, b, d, e) && y == #[trigger] row4(sv, c, b, d, e),
{
    let (ps, s, n, r) = (ps_rows(sv), supp_rows(sv), nat_rows(sv), reg_rows(sv));
    let l1 = product_rows(ps, s);
    let l2 = product_rows(l1, n);
    lemma_product_contains(l2, r, y);
    if from4(sv).contains(y) {
        let (i, e) = choose|i: int, e: int| 0 <= i < l2.len() && 0 <= e < r.len() && y == #[trigger] l2[i] + #[trigger] r[e];
        assert(l2.contains(l2[i]));
        lemma_product_contains(l1, n, l2[i]);
        let (j, d) = choose|j: int, d: int| 0 <= j < l1.len() && 0 <= d < n.len() && l2[i] == #[trigger] l1[j] + #[trigger] n[d];
        assert(l1.contains(l1[j]));
        lemma_product_contains(ps, s, l1[j]);
        let (c, b) = choose|c: int, b: int| 0 <= c < ps.len() && 0 <= b < s.len() && l1[j] == #[trigger] ps[c] + #[trigger] s[b];
        assert(y == row4(sv, c, b, d, e));
    }
    if exists|c: int, b: int, d: int, e: int| in4(sv, c, b, d, e) && y == #[trigger] row4(sv, c, b, d, e) {
        let (c, b, d, e) = choose|c: int, b: int, d: int, e: int| in4(sv, c, b, d, e) && y == #[trigger] row4(sv, c, b, d, e);
        lemma_product_contains(ps, s, ps[c] + s[b]);
        let x1 = ps[c] + s[b];
        lemma_product_contains(l1, n, x1 + n[d]);
        assert(l1.contains(x1));
        let i1 = choose|i: int| 0 <= i < l1.len() && l1[i] == x1;
        assert(l2.contains(l1[i1] + n[d]));
        let x2 = x1 + n[d];
        let i2 = choose|i: int| 0 <= i < l2.len() && l2[i] == x2;
        assert(y == l2[i2] + r[e]);
    }
}

// ------------------------------------------------------------------------------------------ evaluation

/// `FROM partsupp, supplier, nation, region` evaluates to `from4` (in any context).
pub proof fn lemma_eval_from4(db: Database, sv: StoresView, ctx: Row)
    requires tables_of(sv, db),
    ensures eval_query(db, ctx, sub_from()) == Ok::<Relation, SqlError>(from4(sv)),
{
    assert(eval_query(db, ctx, Query::Table(4)) == Ok::<Relation, SqlError>(ps_rows(sv)));
    assert(eval_query(db, ctx, Query::Table(5)) == Ok::<Relation, SqlError>(supp_rows(sv)));
    assert(eval_query(db, ctx, Query::Table(6)) == Ok::<Relation, SqlError>(nat_rows(sv)));
    assert(eval_query(db, ctx, Query::Table(7)) == Ok::<Relation, SqlError>(reg_rows(sv)));
    let q1 = prod(Query::Table(4), Query::Table(5));
    let q2 = prod(q1, Query::Table(6));
    assert(eval_query(db, ctx, q1) == Ok::<Relation, SqlError>(product_rows(ps_rows(sv), supp_rows(sv))));
    assert(eval_query(db, ctx, q2) == Ok::<Relation, SqlError>(product_rows(product_rows(ps_rows(sv), supp_rows(sv)), nat_rows(sv))));
}

/// Equality of two integer columns of the environment.
proof fn lemma_eq_int_cols(db: Database, env: Row, i: nat, j: nat, x: int, y: int)
    requires i < env.len(), j < env.len(), env[i as int] == Val::Int(x), env[j as int] == Val::Int(y),
    ensures eval_pred(db, env, eq_cols(i, j)) == Ok::<Truth, SqlError>(truth_of(x == y)),
{
    lemma_compare_int(x, y);
    lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(i), Expr::Col(j), Val::Int(x), Val::Int(y), x, y);
}

/// Equality of a text column with a text literal.
proof fn lemma_eq_text_lit(db: Database, env: Row, i: nat, a: Seq<u8>, b: Seq<u8>)
    requires i < env.len(), env[i as int] == Val::Text(a),
    ensures eval_pred(db, env, eq_lit(i, Literal::Text(b))) == Ok::<Truth, SqlError>(truth_of(a == b)),
{
    lemma_pred_text_cmp(db, env, CmpOp::Eq, Expr::Col(i), Expr::Lit(Literal::Text(b)), a, b);
}

/// The subquery's WHERE on outer row `x` (part key `k`) and FROM row `y`.
pub proof fn lemma_sub_filter_row(db: Database, sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>, x: Row, k: int,
    c: int, b: int, d: int, e: int)
    requires
        stores_wf(sv),
        in4(sv, c, b, d, e),
        x.len() == 28,
        x[0] == Val::Int(k),
    ensures
        eval_pred(db, x + row4(sv, c, b, d, e), sub_filters(lits(v, pat, rp)))
            == Ok::<Truth, SqlError>(truth_of((sub_keep(k, rp))(row4(sv, c, b, d, e)))),
{
    let y = row4(sv, c, b, d, e);
    lemma_row4(sv, c, b, d, e);
    let env = x + y;
    let ps = lits(v, pat, rp);
    assert(env.len() == 47);
    assert(env[0] == x[0]);
    assert(env[28] == y[0] && env[29] == y[1] && env[33] == y[5] && env[36] == y[8]);
    assert(env[40] == y[12] && env[42] == y[14] && env[44] == y[16] && env[45] == y[17]);
    let (pk, sk, snk, nk, nrk, rk) = (ps_pkeys(sv)[c] as int, ps_skeys(sv)[c] as int, s_nks(sv)[b] as int,
        n_keys(sv)[d] as int, n_rks(sv)[d] as int, r_keys(sv)[e] as int);
    let suppk = s_keys(sv)[b] as int;
    lemma_eq_int_cols(db, env, 0, 28, k, pk);
    lemma_eq_int_cols(db, env, 33, 29, suppk, sk);
    lemma_eq_int_cols(db, env, 36, 40, snk, nk);
    lemma_eq_int_cols(db, env, 42, 44, nrk, rk);
    assert(ps[2] == Literal::Text(rp));
    lemma_eq_text_lit(db, env, 45, r_name(sv, e), rp);
    let p1 = and(eq_cols(0, 28), eq_cols(33, 29));
    let p2 = and(p1, eq_cols(36, 40));
    let p3 = and(p2, eq_cols(42, 44));
    lemma_pred_and(db, env, eq_cols(0, 28), eq_cols(33, 29), k == pk, suppk == sk);
    lemma_pred_and(db, env, p1, eq_cols(36, 40), k == pk && suppk == sk, snk == nk);
    lemma_pred_and(db, env, p2, eq_cols(42, 44), k == pk && suppk == sk && snk == nk, nrk == rk);
    lemma_pred_and(db, env, p3, eq_lit(45, ps[2]), k == pk && suppk == sk && snk == nk && nrk == rk, r_name(sv, e) == rp);
}

/// The subquery's WHERE over its FROM, in outer row `x` (part key `k`): the kept rows `sub_rows`.
pub proof fn lemma_sub_filter(db: Database, sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>, x: Row, k: int)
    requires
        tables_of(sv, db),
        stores_wf(sv),
        x.len() == 28,
        x[0] == Val::Int(k),
    ensures
        eval_query(db, x, Query::Filter { pred: sub_filters(lits(v, pat, rp)), input: Box::new(sub_from()) })
            == Ok::<Relation, SqlError>(sub_rows(sv, k, rp)),
{
    let rows = from4(sv);
    let f = sub_keep(k, rp);
    let pred = sub_filters(lits(v, pat, rp));
    lemma_eval_from4(db, sv, x);
    let rs = Seq::new(rows.len(), |i: int| eval_pred(db, x + rows[i], pred));
    let truths = Seq::new(rows.len(), |i: int| truth_of(f(rows[i])));
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        assert(rows.contains(rows[i]));
        lemma_from4_contains(sv, rows[i]);
        let (c, b, d, e) = choose|c: int, b: int, d: int, e: int| in4(sv, c, b, d, e) && rows[i] == #[trigger] row4(sv, c, b, d, e);
        lemma_sub_filter_row(db, sv, v, pat, rp, x, k, c, b, d, e);
    }
    lemma_collect_all(rs, truths);
    lemma_collect_pointwise::<Truth>();
    assert forall|i: int| 0 <= i < rows.len() implies (#[trigger] truths[i] is True) == f(rows[i]) by {}
    lemma_keep_true_is_true(rows, truths, f);
}

/// The values of the subquery's MIN argument are numerics of scale 2.
pub proof fn lemma_sub_vals_num(sv: StoresView, k: int, rp: Seq<u8>)
    requires stores_wf(sv),
    ensures all_num(sub_vals(sv, k, rp), 2),
{
    let kept = sub_rows(sv, k, rp);
    let vals = sub_vals(sv, k, rp);
    assert forall|i: int| 0 <= i < vals.len() implies (#[trigger] vals[i]) is Num && vals[i]->Num_scale == 2 by {
        assert(kept.contains(kept[i]));
        lemma_keep_contains(from4(sv), sub_keep(k, rp), kept[i]);
        lemma_from4_contains(sv, kept[i]);
        let (c, b, d, e) = choose|c: int, b: int, d: int, e: int| in4(sv, c, b, d, e) && kept[i] == #[trigger] row4(sv, c, b, d, e);
        lemma_row4(sv, c, b, d, e);
    }
}

/// The subquery in outer row `x` (part key `k`) is one row holding `sub_value`.
pub proof fn lemma_sub_query(db: Database, sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>, x: Row, k: int)
    requires
        tables_of(sv, db),
        stores_wf(sv),
        x.len() == 28,
        x[0] == Val::Int(k),
    ensures
        eval_query(db, x, sub_query(lits(v, pat, rp))) == Ok::<Relation, SqlError>(seq![seq![sub_value(sv, k, rp)]]),
{
    let kept = sub_rows(sv, k, rp);
    let aggs = sub_aggs();
    lemma_sub_filter(db, sv, v, pat, rp, x, k);
    // Each kept row's MIN argument: position 31 of `x ++ z` is `z[3]`.
    let rs = Seq::new(kept.len(), |i: int| agg_args(db, x + kept[i], aggs));
    let args = Seq::new(kept.len(), |i: int| seq![kept[i][3]]);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(args[i]) by {
        let env = x + kept[i];
        assert(kept.contains(kept[i]));
        lemma_keep_contains(from4(sv), sub_keep(k, rp), kept[i]);
        lemma_from4_contains(sv, kept[i]);
        let (c, b, d, e) = choose|c: int, b: int, d: int, e: int| in4(sv, c, b, d, e) && kept[i] == #[trigger] row4(sv, c, b, d, e);
        lemma_row4(sv, c, b, d, e);
        assert(env[31] == kept[i][3]);
        let ars = agg_arg_results(db, env, aggs);
        assert(ars.len() == 1);
        assert(ars[0] == agg_arg(db, env, aggs[0]));
        assert(ars[0] == Ok::<Val, SqlError>(kept[i][3]));
        lemma_collect_all(ars, seq![kept[i][3]]);
    }
    lemma_collect_all(rs, args);
    lemma_collect_pointwise::<Row>();
    // MIN over the column of arguments.
    let vals = sub_vals(sv, k, rp);
    assert(column(args, 0) =~= vals);
    lemma_sub_vals_num(sv, k, rp);
    lemma_min_num(vals, 2);
    let mv = sub_value(sv, k, rp);
    assert(min_value(vals) == Ok::<Val, SqlError>(mv));
    let vrs = Seq::new(aggs.len(), |j: int| agg_value(aggs[j], column(args, j)));
    assert(vrs.len() == 1);
    assert(vrs[0] == agg_value(Agg::Min(Expr::Col(31)), column(args, 0)));
    assert(vrs[0] == Ok::<Val, SqlError>(mv));
    lemma_collect_all(vrs, seq![mv]);
    assert(agg_row(aggs, args) == Ok::<Row, SqlError>(seq![mv]));
    assert(eval_query(db, x, Query::Filter { pred: sub_filters(lits(v, pat, rp)), input: Box::new(sub_from()) })
        == Ok::<Relation, SqlError>(kept));
}

// ------------------------------------------------------------------------------------------ the subquery's value

/// The subquery's rows for `k` are the `row4` tuples of partsupp rows offering `k` from a supplier of the region.
proof fn lemma_sub_rows_contains(sv: StoresView, rp: Seq<u8>, k: int, z: Row)
    requires stores_wf(sv),
    ensures
        sub_rows(sv, k, rp).contains(z) <==> exists|c: int, b: int, d: int, e: int| in4(sv, c, b, d, e)
            && z == #[trigger] row4(sv, c, b, d, e) && ps_pkeys(sv)[c] == k && s_keys(sv)[b] == ps_skeys(sv)[c]
            && n_keys(sv)[d] == s_nks(sv)[b] && n_rks(sv)[d] == r_keys(sv)[e] && r_name(sv, e) == rp,
{
    lemma_keep_contains(from4(sv), sub_keep(k, rp), z);
    lemma_from4_contains(sv, z);
    if sub_rows(sv, k, rp).contains(z) {
        let (c, b, d, e) = choose|c: int, b: int, d: int, e: int| in4(sv, c, b, d, e) && z == #[trigger] row4(sv, c, b, d, e);
        lemma_row4(sv, c, b, d, e);
    }
    if exists|c: int, b: int, d: int, e: int| in4(sv, c, b, d, e)
            && z == #[trigger] row4(sv, c, b, d, e) && ps_pkeys(sv)[c] == k && s_keys(sv)[b] == ps_skeys(sv)[c]
            && n_keys(sv)[d] == s_nks(sv)[b] && n_rks(sv)[d] == r_keys(sv)[e] && r_name(sv, e) == rp {
        let (c, b, d, e) = choose|c: int, b: int, d: int, e: int| in4(sv, c, b, d, e)
            && z == #[trigger] row4(sv, c, b, d, e) && ps_pkeys(sv)[c] == k && s_keys(sv)[b] == ps_skeys(sv)[c]
            && n_keys(sv)[d] == s_nks(sv)[b] && n_rks(sv)[d] == r_keys(sv)[e] && r_name(sv, e) == rp;
        lemma_row4(sv, c, b, d, e);
    }
}

/// The numeric `val` has the supply cost of a subquery row for `k`.
pub open spec fn cost_of_sub_row(sv: StoresView, rp: Seq<u8>, k: int, val: Val) -> bool {
    exists|c: int| 0 <= c < ps_n(sv) && #[trigger] sub_ok(sv, rp, k, c) && coeff_of(val) == ps_costs(sv)[c]
}

/// The MIN argument values are exactly the supply costs of the subquery rows (`sub_ok`).
proof fn lemma_sub_vals_costs(sv: StoresView, rp: Seq<u8>, k: int)
    requires stores_wf(sv),
    ensures
        forall|i: int| 0 <= i < sub_vals(sv, k, rp).len() ==> cost_of_sub_row(sv, rp, k, #[trigger] sub_vals(sv, k, rp)[i]),
        forall|c: int| 0 <= c < ps_n(sv) && #[trigger] sub_ok(sv, rp, k, c) ==> exists|i: int| 0 <= i < sub_vals(sv, k, rp).len()
            && coeff_of(sub_vals(sv, k, rp)[i]) == ps_costs(sv)[c],
{
    let kept = sub_rows(sv, k, rp);
    let vals = sub_vals(sv, k, rp);
    assert forall|i: int| 0 <= i < vals.len() implies cost_of_sub_row(sv, rp, k, #[trigger] vals[i]) by {
        assert(kept.contains(kept[i]));
        lemma_sub_rows_contains(sv, rp, k, kept[i]);
        let (c, b, d, e) = choose|c: int, b: int, d: int, e: int| in4(sv, c, b, d, e)
            && kept[i] == #[trigger] row4(sv, c, b, d, e) && ps_pkeys(sv)[c] == k && s_keys(sv)[b] == ps_skeys(sv)[c]
            && n_keys(sv)[d] == s_nks(sv)[b] && n_rks(sv)[d] == r_keys(sv)[e] && r_name(sv, e) == rp;
        lemma_row4(sv, c, b, d, e);
        assert(supp_in_reg(sv, rp, b));
        assert(sub_ok(sv, rp, k, c));
        assert(vals[i] == kept[i][3]);
    }
    assert forall|c: int| 0 <= c < ps_n(sv) && #[trigger] sub_ok(sv, rp, k, c) implies exists|i: int| 0 <= i < vals.len()
        && coeff_of(vals[i]) == ps_costs(sv)[c] by {
        let b = choose|b: int| 0 <= b < supp_n(sv) && #[trigger] s_keys(sv)[b] == ps_skeys(sv)[c] && supp_in_reg(sv, rp, b);
        let (d, e) = choose|d: int, e: int| 0 <= d < nat_n(sv) && 0 <= e < reg_n(sv)
            && #[trigger] n_keys(sv)[d] == s_nks(sv)[b] && n_rks(sv)[d] == #[trigger] r_keys(sv)[e] && r_name(sv, e) == rp;
        let z = row4(sv, c, b, d, e);
        lemma_sub_rows_contains(sv, rp, k, z);
        let i = choose|i: int| 0 <= i < kept.len() && kept[i] == z;
        lemma_row4(sv, c, b, d, e);
        assert(vals[i] == z[3]);
    }
}

/// The subquery's value: NULL without a subquery row, otherwise the least supply cost (scale 2).
pub proof fn lemma_sub_value(sv: StoresView, rp: Seq<u8>, k: int)
    requires stores_wf(sv),
    ensures
        (sub_value(sv, k, rp) is Null) <==> !exists|c: int| 0 <= c < ps_n(sv) && #[trigger] sub_ok(sv, rp, k, c),
        !(sub_value(sv, k, rp) is Null) ==> sub_value(sv, k, rp) is Num && sub_value(sv, k, rp)->Num_scale == 2
            && is_min_cost(sv, rp, k, sub_value(sv, k, rp)->Num_coeff),
{
    let vals = sub_vals(sv, k, rp);
    lemma_sub_vals_num(sv, k, rp);
    lemma_min_num(vals, 2);
    lemma_sub_vals_costs(sv, rp, k);
    if vals.len() > 0 {
        let m = min_coeff(vals);
        let i = choose|i: int| 0 <= i < vals.len() && coeff_of(vals[i]) == m;
        assert(cost_of_sub_row(sv, rp, k, vals[i]));
        let c = choose|c: int| 0 <= c < ps_n(sv) && #[trigger] sub_ok(sv, rp, k, c) && coeff_of(vals[i]) == ps_costs(sv)[c];
        assert(sub_ok(sv, rp, k, c));
        assert forall|c2: int| 0 <= c2 < ps_n(sv) && #[trigger] sub_ok(sv, rp, k, c2) implies m <= ps_costs(sv)[c2] by {
            let i2 = choose|i2: int| 0 <= i2 < vals.len() && coeff_of(vals[i2]) == ps_costs(sv)[c2];
            assert(m <= coeff_of(vals[i2]));
        }
    } else {
        if exists|c: int| 0 <= c < ps_n(sv) && #[trigger] sub_ok(sv, rp, k, c) {
            let c = choose|c: int| 0 <= c < ps_n(sv) && #[trigger] sub_ok(sv, rp, k, c);
            assert(exists|i: int| 0 <= i < vals.len() && coeff_of(vals[i]) == ps_costs(sv)[c]);
        }
    }
}

/// `ps_supplycost = (subquery)` in outer row `x` with part key `k` and supply cost `w` (scale 2): true exactly when
/// `w` is the least supply cost of the subquery rows for `k`.
pub proof fn lemma_cost_eq_min(db: Database, sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>, x: Row, k: int, w: int)
    requires
        tables_of(sv, db),
        stores_wf(sv),
        x.len() == 28,
        x[0] == Val::Int(k),
        x[19] == (Val::Num { coeff: w, scale: 2 }),
    ensures
        eval_pred(db, x, cost_eq_min(lits(v, pat, rp))) is Ok,
        (eval_pred(db, x, cost_eq_min(lits(v, pat, rp)))->Ok_0 is True) == is_min_cost(sv, rp, k, w),
{
    let q = sub_query(lits(v, pat, rp));
    lemma_sub_query(db, sv, v, pat, rp, x, k);
    let sv_val = sub_value(sv, k, rp);
    assert(eval_expr(db, x, Expr::Subquery(Box::new(q))) == Ok::<Val, SqlError>(sv_val));
    assert(eval_expr(db, x, Expr::Col(19)) == Ok::<Val, SqlError>(x[19]));
    lemma_sub_value(sv, rp, k);
    if !(sv_val is Null) {
        let m = sv_val->Num_coeff;
        crate::link::expr::lemma_compare_num(w, 2, m, 2);
        crate::link::expr::lemma_align_same(w, 2);
        crate::link::expr::lemma_align_same(m, 2);
        assert(max_nat(2, 2) == 2);
        if is_min_cost(sv, rp, k, w) {
            let c = choose|c: int| 0 <= c < ps_n(sv) && #[trigger] sub_ok(sv, rp, k, c) && ps_costs(sv)[c] == w;
            let c2 = choose|c2: int| 0 <= c2 < ps_n(sv) && #[trigger] sub_ok(sv, rp, k, c2) && ps_costs(sv)[c2] == m;
            assert(m <= w);
            assert(w <= m);
        }
    } else {
        if is_min_cost(sv, rp, k, w) {
            let c = choose|c: int| 0 <= c < ps_n(sv) && #[trigger] sub_ok(sv, rp, k, c) && ps_costs(sv)[c] == w;
        }
    }
}

} // verus!
