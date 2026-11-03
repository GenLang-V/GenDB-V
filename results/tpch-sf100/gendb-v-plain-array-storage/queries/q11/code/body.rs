//! The statement body over one bound database (`sem::body`): the GROUP BY rows (`lemma_group_rows`), the HAVING
//! subquery's value under the context of a group row (`lemma_sub_value`), the HAVING condition on a group row
//! (`lemma_having`) and the body's rows (`lemma_body_rows`): the full rows `(ps_partkey, value)` of the groups whose
//! value, written at scale 12, exceeds `total * $2` (`hv`).
//!
//! Domains: the GROUP BY needs every group's absolute mass inside `i128` (`group_caps(gq(p), ..)`), the subquery the
//! total absolute mass (`group_caps(sq(p), ..)`); the product `total * $2` is always inside PostgreSQL's numeric
//! format. When some qualifying row exists, the subquery's value is the numeric `total * $2` at scale 12.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::order::*;
use crate::spec::equality::row_not_distinct;
use crate::exec::relational::domain::{lemma_eval_filter, lemma_eval_aggregate, lemma_eval_project, filter_results,
    agg_args_results, project_results};
use crate::bridge::collect::lemma_collect_all;
use crate::link::expr::{ival, lemma_compare_num, lemma_align_same, i128_max};
use crate::link::query::*;
use crate::link::join::{keep, lemma_keep_true_keep};
use crate::gendb_entry::stores::StoresView;
use crate::agent::model::*;
use crate::agent::sem::*;
use crate::agent::normal::*;

verus! {

// ------------------------------------------------------------------------------------------ FROM and WHERE

/// The positions `0..16` (projection of a FROM row onto itself).
pub open spec fn cols16() -> Seq<nat> {
    Seq::new(16, |k: int| k as nat)
}

/// Every FROM row has 16 values; projecting the FROM relation on `cols16` keeps it.
pub proof fn lemma_from_wf(sv: StoresView)
    requires stores_wf(sv),
    ensures
        forall|m: int| 0 <= m < from_rows(sv).len() ==> (#[trigger] from_rows(sv)[m]).len() == 16,
        proj_all(from_rows(sv), cols16()) == from_rows(sv),
{
    let r = from_rows(sv);
    assert forall|m: int| 0 <= m < r.len() implies (#[trigger] r[m]).len() == 16 by {
        let (a, b, d) = lemma_from_elem(sv, m);
        lemma_row3(sv, a, b, d);
    }
    assert forall|m: int| 0 <= m < r.len() implies #[trigger] proj_all(r, cols16())[m] == r[m] by {
        assert(proj(r[m], cols16()) =~= r[m]);
    }
    assert(proj_all(r, cols16()) =~= r);
}

/// The WHERE truth values of the FROM rows.
pub open spec fn truths(sv: StoresView, p: Seq<u8>) -> Seq<Truth> {
    qual_truths(gq(p), from_rows(sv))
}

/// The FROM rows the WHERE keeps.
pub open spec fn kept(sv: StoresView, p: Seq<u8>) -> Seq<Row> {
    keep_true(from_rows(sv), truths(sv, p))
}

/// The WHERE at offset `|ctx|` over the FROM relation keeps `kept` (any context, for both query blocks).
pub proof fn lemma_filter_eval(db: Database, sv: StoresView, p: Seq<u8>, ctx: Row)
    requires tables_of(sv, db), stores_wf(sv), bounds_ok(sv),
    ensures eval_query(db, ctx, filtered(ctx.len(), Literal::Text(p))) == Ok::<Relation, SqlError>(kept(sv, p)),
{
    let r = from_rows(sv);
    let pred = where_pred(ctx.len(), Literal::Text(p));
    lemma_eval_from(db, sv, ctx);
    lemma_eval_filter(db, ctx, pred, Box::new(from3()));
    let rs = filter_results(db, ctx, r, pred);
    let ts = truths(sv, p);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Truth, SqlError>(ts[i]) by {
        let (a, b, d) = lemma_from_elem(sv, i);
        lemma_row_eval(db, sv, p, ctx, a, b, d);
        lemma_qualx_row3(sv, p, a, b, d);
    }
    lemma_collect_all(rs, ts);
}

/// The kept rows: FROM rows that satisfy the WHERE, position by position the normal form's `qrows`.
pub proof fn lemma_kept(sv: StoresView, p: Seq<u8>)
    requires stores_wf(sv),
    ensures
        kept(sv, p) == qrows(gq(p), from_rows(sv)),
        kept(sv, p) == qrows(sq(p), from_rows(sv)),
        forall|i: int| 0 <= i < kept(sv, p).len() ==>
            from_rows(sv).contains(#[trigger] kept(sv, p)[i]) && qualx(p, kept(sv, p)[i]),
{
    let r = from_rows(sv);
    lemma_from_wf(sv);
    lemma_kept_rows(gq(p), r, cols16());
    let k = kept(sv, p);
    assert forall|i: int| 0 <= i < k.len() implies #[trigger] proj(k[i], cols16()) == k[i] by {
        let m = choose|m: int| 0 <= m < r.len() && r[m] == k[i];
        assert(proj(k[i], cols16()) =~= k[i]);
    }
    assert(proj_all(k, cols16()) =~= k);
    lemma_qrows_same(gq(p), sq(p), r);
}

/// Normal forms with the same qualification have the same qualifying rows.
proof fn lemma_qrows_same(g: QuerySpec, h: QuerySpec, xs: Seq<Row>)
    requires forall|x: Row| #[trigger] (g.qual)(x) == (h.qual)(x),
    ensures qrows(g, xs) == qrows(h, xs),
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_qrows_same(g, h, xs.drop_last());
    }
}

/// A kept row is a FROM row `row3(a, b, d)` whose rows satisfy the WHERE condition.
pub proof fn lemma_kept_row(sv: StoresView, p: Seq<u8>, x: Row) -> (abd: (int, int, int))
    requires stores_wf(sv), from_rows(sv).contains(x), qualx(p, x),
    ensures
        0 <= abd.0 < ps_n(sv), 0 <= abd.1 < supp_n(sv), 0 <= abd.2 < nat_n(sv),
        x == row3(sv, abd.0, abd.1, abd.2),
        qual3(sv, p, abd.0, abd.1, abd.2),
{
    let m = choose|m: int| 0 <= m < from_rows(sv).len() && from_rows(sv)[m] == x;
    let (a, b, d) = lemma_from_elem(sv, m);
    lemma_qualx_row3(sv, p, a, b, d);
    (a, b, d)
}

// ------------------------------------------------------------------------------------------ per-row agreement

/// A one-aggregate argument list.
pub proof fn lemma_agg_args_one(db: Database, env: Row, a: Agg, v: Val)
    requires agg_arg(db, env, a) == Ok::<Val, SqlError>(v),
    ensures agg_args(db, env, seq![a]) == Ok::<Row, SqlError>(seq![v]),
{
    let rs = agg_arg_results(db, env, seq![a]);
    assert(rs[0] == agg_arg(db, env, seq![a][0]));
    lemma_collect_all(rs, seq![v]);
}

/// The SUM argument of a FROM row at offset `|pre|` is the normal form's argument.
pub proof fn lemma_arg_row(db: Database, sv: StoresView, p: Seq<u8>, pre: Row, x: Row)
    requires stores_wf(sv), bounds_ok(sv), from_rows(sv).contains(x),
    ensures
        agg_args(db, pre + x, seq![sum_agg(pre.len())]) == Ok::<Row, SqlError>(arg_vals(gq(p), x)),
        arg_vals(gq(p), x) == arg_vals(sq(p), x),
        eval_exprs(db, pre + x, seq![Expr::Col(pre.len())]) == Ok::<Row, SqlError>(seq![x[0]]),
{
    let m = choose|m: int| 0 <= m < from_rows(sv).len() && from_rows(sv)[m] == x;
    let (a, b, d) = lemma_from_elem(sv, m);
    lemma_row3(sv, a, b, d);
    lemma_row_eval(db, sv, p, pre, a, b, d);
    let v = Val::Num { coeff: val(sv, a), scale: 2 };
    lemma_agg_arg_sum(db, pre + x, NumKind::Numeric, arg_expr(pre.len()));
    lemma_agg_args_one(db, pre + x, sum_agg(pre.len()), v);
    assert(ival(x[3]) * ival(x[2]) == val(sv, a));
    assert(arg_vals(gq(p), x) =~= seq![v]);
    assert(arg_vals(sq(p), x) =~= seq![v]);
    // the group key
    let env = pre + x;
    let es = seq![Expr::Col(pre.len())];
    lemma_eval_exprs_step(db, env, es);
    assert(es.drop_last() =~= Seq::<Expr>::empty());
    lemma_eval_exprs_empty(db, env);
    assert(Seq::<Val>::empty().push(x[0]) =~= seq![x[0]]);
}

// ------------------------------------------------------------------------------------------ GROUP BY

/// Every group's absolute mass is at most the total absolute mass.
pub proof fn lemma_gabs_le_total(p: Seq<u8>, xs: Seq<Row>, k: Row)
    ensures gabs(gq(p), xs, k, 0) <= gabs(sq(p), xs, Seq::<Val>::empty(), 0),
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_gabs_le_total(p, xs.drop_last(), k);
    }
}

/// The total absolute mass bounds every group: `group_caps` of both blocks.
pub proof fn lemma_caps(p: Seq<u8>, xs: Seq<Row>)
    requires gabs(sq(p), xs, Seq::<Val>::empty(), 0) <= i128_max(),
    ensures group_caps(gq(p), xs), group_caps(sq(p), xs),
{
    assert forall|k: Row, j: int| 0 <= j < gq(p).aggs.len() && !(gq(p).aggs[j] is Count)
        implies #[trigger] gabs(gq(p), xs, k, j) <= i128_max() by {
        lemma_gabs_le_total(p, xs, k);
    }
    assert forall|k: Row, j: int| 0 <= j < sq(p).aggs.len() && !(sq(p).aggs[j] is Count)
        implies #[trigger] gabs(sq(p), xs, k, j) <= i128_max() by {
        if k != Seq::<Val>::empty() {
            lemma_gabs_zero_key(p, xs, k);
        }
    }
}

/// The scalar block has no group other than the empty key.
proof fn lemma_gabs_zero_key(p: Seq<u8>, xs: Seq<Row>, k: Row)
    requires k != Seq::<Val>::empty(),
    ensures gabs(sq(p), xs, k, 0) == 0,
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_gabs_zero_key(p, xs.drop_last(), k);
    }
}

/// The keys of the grouped block are exact (one integer each).
proof fn lemma_keys_exact(sv: StoresView, p: Seq<u8>)
    requires stores_wf(sv),
    ensures keys_exact(gq(p), from_rows(sv)),
{
    let r = from_rows(sv);
    assert forall|a: int, b: int| 0 <= a < r.len() && 0 <= b < r.len() && (gq(p).qual)(r[a]) && (gq(p).qual)(r[b])
        implies (row_not_distinct(#[trigger] (gq(p).key)(r[a]), #[trigger] (gq(p).key)(r[b])) <==> (gq(p).key)(r[a]) == (gq(p).key)(r[b])) by {
        let (a1, b1, d1) = lemma_from_elem(sv, a);
        let (a2, b2, d2) = lemma_from_elem(sv, b);
        lemma_row3(sv, a1, b1, d1);
        lemma_row3(sv, a2, b2, d2);
        lemma_row_exact((gq(p).key)(r[a]), (gq(p).key)(r[b]));
    }
}

/// The GROUP BY rows: one full row per group key, in first-occurrence order.
pub proof fn lemma_group_rows(db: Database, sv: StoresView, p: Seq<u8>)
    requires tables_of(sv, db), stores_wf(sv), bounds_ok(sv), group_caps(gq(p), from_rows(sv)),
    ensures
        eval_query(db, Seq::empty(), grouped(Literal::Text(p)))
            == Ok::<Relation, SqlError>(gkeys(gq(p), from_rows(sv)).map_values(|k: Row| full_row(gq(p), from_rows(sv), k))),
{
    let r = from_rows(sv);
    let g = gq(p);
    let e = Seq::<Val>::empty();
    lemma_from_wf(sv);
    lemma_filter_eval(db, sv, p, e);
    assert(e.len() == 0);
    assert forall|i: int| 0 <= i < r.len() && (g.qual)(proj(#[trigger] r[i], cols16()))
        implies eval_exprs(db, r[i], seq![Expr::Col(0)]) == Ok::<Row, SqlError>((g.key)(proj(r[i], cols16()))) by {
        assert(r.contains(r[i]));
        lemma_arg_row(db, sv, p, e, r[i]);
        assert(e + r[i] =~= r[i]);
    }
    assert forall|i: int| 0 <= i < r.len() && (g.qual)(proj(#[trigger] r[i], cols16()))
        implies agg_args(db, r[i], seq![sum_agg(0)]) == Ok::<Row, SqlError>(arg_vals(g, proj(r[i], cols16()))) by {
        assert(r.contains(r[i]));
        lemma_arg_row(db, sv, p, e, r[i]);
        assert(e + r[i] =~= r[i]);
    }
    lemma_keys_exact(sv, p);
    lemma_group_query(db, r, cols16(), filtered(0, Literal::Text(p)), seq![Expr::Col(0)], seq![sum_agg(0)], g);
}

// ------------------------------------------------------------------------------------------ the HAVING subquery

/// The literal `$2` is the numeric `c2` at scale 10.
pub proof fn lemma_lit2(db: Database, env: Row, c2: int)
    requires -100000000000000000000000000000000000000 < c2 < 100000000000000000000000000000000000000,
    ensures eval_expr(db, env, Expr::Lit(Literal::Num { coeff: c2, scale: 10 })) == Ok::<Val, SqlError>(Val::Num { coeff: c2, scale: 10 }),
{
    lemma_num_in_range_small(c2, 10);
    assert(10 <= crate::spec::limits::numeric_dscale_max());
}

/// `|t| <= i128::MAX`, `|c2| < 10^38`: the product is inside PostgreSQL's numeric format at scale 12.
pub proof fn lemma_scaled_in_range(t: int, c2: int)
    requires
        -i128_max() <= t <= i128_max(),
        -100000000000000000000000000000000000000 < c2 < 100000000000000000000000000000000000000,
    ensures num_in_range(t * c2, 12),
{
    let b: int = 0x8000_0000_0000_0000_0000_0000_0000_0000;
    assert(abs(t) <= b);
    assert(abs(c2) <= b);
    assert(abs(t * c2) == abs(t) * abs(c2)) by (nonlinear_arith);
    assert(abs(t) * abs(c2) <= b * b) by (nonlinear_arith) requires 0 <= abs(t) <= b, 0 <= abs(c2) <= b;
    assert(b * b < pow10(77)) by (compute);
    lemma_decimal_digits_bound(abs(t * c2), 77);
}

/// The subquery's aggregate row: `SUM` over the kept rows (`total` at scale 2) when some row qualifies.
pub open spec fn total_val(sv: StoresView, p: Seq<u8>) -> Val {
    agg_out(AggKind::Sum { scale: 2 }, gcount(sq(p), from_rows(sv), Seq::empty()), gsum(sq(p), from_rows(sv), Seq::empty(), 0))
}

/// The subquery's aggregate under any context `r` of two values (a group row).
pub proof fn lemma_sub_agg(db: Database, sv: StoresView, p: Seq<u8>, r: Row)
    requires
        tables_of(sv, db), stores_wf(sv), bounds_ok(sv), r.len() == 2,
        group_caps(sq(p), from_rows(sv)),
    ensures eval_query(db, r, sub_agg(Literal::Text(p))) == Ok::<Relation, SqlError>(seq![seq![total_val(sv, p)]]),
{
    let xs = from_rows(sv);
    let g = sq(p);
    let k = kept(sv, p);
    let aggs = seq![sum_agg(2)];
    lemma_filter_eval(db, sv, p, r);
    lemma_kept(sv, p);
    lemma_eval_aggregate(db, r, aggs, Box::new(filtered(2, Literal::Text(p))));
    let rs = agg_args_results(db, r, k, aggs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(args[i]) by {
        lemma_arg_row(db, sv, p, r, k[i]);
    }
    lemma_collect_all(rs, args);
    lemma_scalar_members(g, xs);
    lemma_agg_row(g, aggs, xs, Seq::empty());
    assert(agg_outs(g, xs, Seq::empty()) =~= seq![total_val(sv, p)]);
}

/// `SUM(..) * $2` of the subquery: the numeric `total * c2` at scale 12 when some row qualifies.
pub proof fn lemma_sub_value(db: Database, sv: StoresView, p: Seq<u8>, c2: int, r: Row)
    requires
        tables_of(sv, db), stores_wf(sv), bounds_ok(sv), r.len() == 2,
        group_caps(sq(p), from_rows(sv)),
        gcount(sq(p), from_rows(sv), Seq::empty()) > 0,
        -100000000000000000000000000000000000000 < c2 < 100000000000000000000000000000000000000,
    ensures ({
        let ps = params_of(p, c2);
        let t = gsum(sq(p), from_rows(sv), Seq::empty(), 0);
        eval_query(db, r, sub_query(ps)) == Ok::<Relation, SqlError>(seq![seq![Val::Num { coeff: t * c2, scale: 12 }]])
    }),
{
    let ps = params_of(p, c2);
    let xs = from_rows(sv);
    let t = gsum(sq(p), xs, Seq::empty(), 0);
    lemma_sub_agg(db, sv, p, r);
    let v = total_val(sv, p);
    assert(v == Val::Num { coeff: t, scale: 2 });
    let arows = seq![seq![v]];
    let exprs = seq![scaled(ps[1])];
    lemma_eval_project(db, r, exprs, Box::new(sub_agg(ps[0])));
    let prs = project_results(db, r, arows, exprs);
    let env = r + arows[0];
    assert(env.len() == 3 && env[2] == v);
    // `t * c2` is inside the numeric format
    lemma_abs_le_mass(p, xs);
    lemma_scaled_in_range(t, c2);
    lemma_lit2(db, env, c2);
    assert(eval_expr(db, env, Expr::Col(2)) == Ok::<Val, SqlError>(v));
    let w = Val::Num { coeff: t * c2, scale: 12 };
    assert(eval_expr(db, env, scaled(ps[1])) == Ok::<Val, SqlError>(w));
    lemma_eval_exprs_step(db, env, exprs);
    assert(exprs.drop_last() =~= Seq::<Expr>::empty());
    lemma_eval_exprs_empty(db, env);
    assert(Seq::<Val>::empty().push(w) =~= seq![w]);
    assert(prs[0] == eval_exprs(db, r + arows[0], exprs));
    lemma_collect_all(prs, seq![seq![w]]);
}

/// The total's coefficient is at most its absolute mass, so inside `i128` under `group_caps`.
pub proof fn lemma_abs_le_mass(p: Seq<u8>, xs: Seq<Row>)
    requires group_caps(sq(p), xs),
    ensures -i128_max() <= gsum(sq(p), xs, Seq::empty(), 0) <= i128_max(),
{
    lemma_abs_bound(sq(p), xs, Seq::empty(), 0);
    assert(gabs(sq(p), xs, Seq::empty(), 0) <= i128_max());
}

// ------------------------------------------------------------------------------------------ HAVING and the body

/// HAVING on a group row of value `s` (scale 2): `s`, written at scale 12, exceeds `t * c2`.
pub open spec fn hv(t: int, c2: int) -> spec_fn(Row) -> bool {
    |row: Row| ival(row[1]) * 10_000_000_000 > t * c2
}

/// The HAVING condition on a group row `(Int(k), Num { s, 2 })`.
pub proof fn lemma_having(db: Database, sv: StoresView, p: Seq<u8>, c2: int, row: Row)
    requires
        tables_of(sv, db), stores_wf(sv), bounds_ok(sv),
        group_caps(sq(p), from_rows(sv)),
        gcount(sq(p), from_rows(sv), Seq::empty()) > 0,
        -100000000000000000000000000000000000000 < c2 < 100000000000000000000000000000000000000,
        row.len() == 2,
        row[1] is Num, row[1]->Num_scale == 2,
    ensures ({
        let ps = params_of(p, c2);
        let t = gsum(sq(p), from_rows(sv), Seq::empty(), 0);
        eval_pred(db, Seq::<Val>::empty() + row, having(ps)) == Ok::<Truth, SqlError>(truth_of((hv(t, c2))(row)))
    }),
{
    let ps = params_of(p, c2);
    let t = gsum(sq(p), from_rows(sv), Seq::empty(), 0);
    let env = Seq::<Val>::empty() + row;
    assert(env =~= row);
    lemma_sub_value(db, sv, p, c2, env);
    let w = Val::Num { coeff: t * c2, scale: 12 };
    assert(subquery_value(seq![seq![w]]) == Ok::<Val, SqlError>(w));
    assert(eval_expr(db, env, Expr::Subquery(Box::new(sub_query(ps)))) == Ok::<Val, SqlError>(w));
    assert(eval_expr(db, env, Expr::Col(1)) == Ok::<Val, SqlError>(row[1]));
    let s = ival(row[1]);
    lemma_compare_num(s, 2, t * c2, 12);
    assert(max_nat(2, 12) == 12);
    assert(pow10(10) == 10_000_000_000) by (compute);
    assert((12 - 2) as nat == 10);
    assert(align(s, 2, 12) == s * 10_000_000_000);
    lemma_align_same(t * c2, 12);
}

/// The groups' full rows.
pub open spec fn group_rows_of(sv: StoresView, p: Seq<u8>) -> Seq<Row> {
    gkeys(gq(p), from_rows(sv)).map_values(|k: Row| full_row(gq(p), from_rows(sv), k))
}

/// A group key's full row is `(Int(k), Num { gsum, 2 })`.
pub proof fn lemma_group_row(sv: StoresView, p: Seq<u8>, k: Row)
    requires stores_wf(sv), gkeys(gq(p), from_rows(sv)).contains(k),
    ensures
        exists|pk: int| k == kr(pk),
        full_row(gq(p), from_rows(sv), k).len() == 2,
        full_row(gq(p), from_rows(sv), k)[0] == k[0],
        full_row(gq(p), from_rows(sv), k)[1] == (Val::Num { coeff: gsum(gq(p), from_rows(sv), k, 0), scale: 2 }),
{
    let xs = from_rows(sv);
    lemma_gkeys_witness(gq(p), xs, k);
    let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(gq(p), xs[m], k);
    let (a, b, d) = lemma_from_elem(sv, m);
    lemma_row3(sv, a, b, d);
    assert(k == kr(ps_pkeys(sv)[a] as int));
    let f = full_row(gq(p), xs, k);
    assert(f == k + agg_outs(gq(p), xs, k));
}

/// The body's rows: the group rows HAVING keeps.
pub proof fn lemma_body_rows(db: Database, sv: StoresView, p: Seq<u8>, c2: int)
    requires
        tables_of(sv, db), stores_wf(sv), bounds_ok(sv),
        group_caps(gq(p), from_rows(sv)),
        group_caps(sq(p), from_rows(sv)),
        -100000000000000000000000000000000000000 < c2 < 100000000000000000000000000000000000000,
    ensures ({
        let ps = params_of(p, c2);
        let t = gsum(sq(p), from_rows(sv), Seq::empty(), 0);
        eval_query(db, Seq::empty(), body(ps)) == Ok::<Relation, SqlError>(keep(group_rows_of(sv, p), hv(t, c2)))
    }),
{
    let ps = params_of(p, c2);
    let xs = from_rows(sv);
    let t = gsum(sq(p), xs, Seq::empty(), 0);
    let gr = group_rows_of(sv, p);
    let e = Seq::<Val>::empty();
    lemma_group_rows(db, sv, p);
    lemma_eval_filter(db, e, having(ps), Box::new(grouped(ps[0])));
    let rs = filter_results(db, e, gr, having(ps));
    let ts = Seq::new(gr.len(), |i: int| truth_of((hv(t, c2))(gr[i])));
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Truth, SqlError>(ts[i]) by {
        let k = gkeys(gq(p), xs)[i];
        assert(gkeys(gq(p), xs).contains(k));
        lemma_group_row(sv, p, k);
        lemma_gkeys_witness(gq(p), xs, k);
        lemma_count_le(p, xs, k);
        lemma_having(db, sv, p, c2, gr[i]);
    }
    lemma_collect_all(rs, ts);
    lemma_keep_true_keep(gr, ts, hv(t, c2));
}

/// A group with a qualifying row makes the scalar block's count positive.
pub proof fn lemma_count_le(p: Seq<u8>, xs: Seq<Row>, k: Row)
    ensures gcount(gq(p), xs, k) <= gcount(sq(p), xs, Seq::<Val>::empty()),
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_count_le(p, xs.drop_last(), k);
    }
}

} // verus!
