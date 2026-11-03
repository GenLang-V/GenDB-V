//! The Q18 statement's meaning on a database bound to the parts: its body (`GroupBy` over the filtered FROM
//! product) evaluates to the normal form's rows, which are exactly the good orders' rows `gseq` (`lemma_q18_denote`;
//! every group's SUM fits, so there is no capacity case), so a top 100 of `gseq` under the ORDER BY keys is an
//! allowed output of the statement (`lemma_q18_ordered`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::order::*;
use crate::query::{query_spec_at, param_domain};
use crate::link::query::*;
use crate::link::source::lemma_proj_all_index;
use crate::link::outcome::lemma_outcome_sorted;
use crate::bridge::equality::same_exact_type;
use crate::spec::equality::row_not_distinct;
use crate::bridge::order::{keys_ok, key_ok};
use super::common::topk::*;
use super::model::*;
use super::qspec::*;
use super::rels::*;
use super::subq::sub_ok;
use super::sqlrow::*;
use super::sqllink::*;

verus! {

/// The facts of a database bound to the parts, at one binding.
pub open spec fn bound_ok(db: Database, m: M, ps: Seq<Literal>) -> bool {
    &&& db_ok(db)
    &&& rel_ok(m, db)
    &&& model_ok(m)
    &&& param_domain(ps)
}

/// The WHERE of the statement agrees with the normal form on every FROM row.
pub proof fn lemma_pred_agrees(db: Database, m: M, ps: Seq<Literal>)
    requires bound_ok(db, m, ps),
    ensures pred_agrees(db, from_rows(db), q18_cols(), q18_pred(ps), q18_g(m, qp_of(ps))),
{
    let p = qp_of(ps);
    let rows = from_rows(db);
    assert(sub_ok(db, m));
    assert forall|i: int| 0 <= i < rows.len() implies
        eval_pred(db, #[trigger] rows[i], q18_pred(ps)) == Ok::<Truth, SqlError>(truth_of((q18_g(m, p).qual)(proj(rows[i], q18_cols())))) by {
        let (c, q, j) = lemma_from_row(db, m, i);
        lemma_pred_eval(db, m, ps, rows[i], ckey(m, c), okey(m, q), ocust(m, q), lkey(m, j));
        lemma_term(m, p, Seq::empty(), c, q, j);
    }
}

/// The group key and the SUM argument agree with the normal form on every FROM row.
pub proof fn lemma_keys_args_agree(db: Database, m: M, ps: Seq<Literal>)
    requires bound_ok(db, m, ps),
    ensures
        keys_agree(db, from_rows(db), q18_cols(), q18_gkeys(), q18_g(m, qp_of(ps))),
        args_agree(db, from_rows(db), q18_cols(), q18_aggs(), q18_g(m, qp_of(ps))),
{
    let p = qp_of(ps);
    let g = q18_g(m, p);
    let rows = from_rows(db);
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], q18_cols())) implies
        eval_exprs(db, rows[i], q18_gkeys()) == Ok::<Row, SqlError>((g.key)(proj(rows[i], q18_cols()))) by {
        let (c, q, j) = lemma_from_row(db, m, i);
        lemma_keys_eval(db, rows[i]);
        lemma_term(m, p, Seq::empty(), c, q, j);
        assert(seq![rows[i][1], rows[i][0], rows[i][8], rows[i][12], rows[i][11]] =~= keyrow(m, c, q));
    }
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], q18_cols())) implies
        agg_args(db, rows[i], q18_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[i], q18_cols()))) by {
        let (c, q, j) = lemma_from_row(db, m, i);
        lemma_args_eval(db, rows[i]);
        lemma_term(m, p, Seq::empty(), c, q, j);
        assert(arg_vals(g, proj(rows[i], q18_cols())) =~= seq![Val::Num { coeff: lqty(m, j), scale: 2 }]);
    }
}

/// Group keys of all rows have one exact type per position.
pub proof fn lemma_keys_exact(db: Database, m: M, ps: Seq<Literal>)
    requires bound_ok(db, m, ps),
    ensures keys_exact(q18_g(m, qp_of(ps)), q18_xs(db)),
{
    let p = qp_of(ps);
    let g = q18_g(m, p);
    let rows = from_rows(db);
    let xs = q18_xs(db);
    lemma_proj_all_index(rows, q18_cols());
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        let (ca, qa, ja) = lemma_from_row(db, m, a);
        let (cb, qb, jb) = lemma_from_row(db, m, b);
        lemma_term(m, p, Seq::empty(), ca, qa, ja);
        lemma_term(m, p, Seq::empty(), cb, qb, jb);
        let (ka, kb) = ((g.key)(xs[a]), (g.key)(xs[b]));
        assert forall|t: int| 0 <= t < ka.len() implies same_exact_type(#[trigger] ka[t], kb[t]) by {}
        lemma_row_exact(ka, kb);
    }
}

/// The GROUP BY rows of the normal form (`key ++ aggregates` of every group, first-occurrence order).
pub open spec fn fullrows(g: QuerySpec, xs: Seq<Row>) -> Seq<Row> {
    gkeys(g, xs).map_values(|k: Row| full_row(g, xs, k))
}

/// Every group key of the normal form has five columns.
proof fn lemma_gk_len(db: Database, m: M, p: QP, k: Row)
    requires db_ok(db), rel_ok(m, db), gkeys(q18_g(m, p), q18_xs(db)).contains(k),
    ensures k.len() == 5,
{
    let g = q18_g(m, p);
    let xs = q18_xs(db);
    lemma_gkeys_witness(g, xs, k);
    let t = choose|t: int| 0 <= t < xs.len() && #[trigger] hit(g, xs[t], k);
    assert((g.key)(xs[t]) == k);
}

/// The GROUP BY rows are the result rows (the SELECT list is the GROUP BY row).
proof fn lemma_full_is_result(db: Database, m: M, p: QP)
    requires db_ok(db), rel_ok(m, db),
    ensures fullrows(q18_g(m, p), q18_xs(db)) == result_rows(q18_g(m, p), q18_xs(db)),
{
    let g = q18_g(m, p);
    let xs = q18_xs(db);
    let gk = gkeys(g, xs);
    assert forall|i: int| 0 <= i < gk.len() implies #[trigger] full_row(g, xs, gk[i]) == out_row(g, xs, gk[i]) by {
        let k = gk[i];
        assert(gk.contains(k));
        lemma_gk_len(db, m, p, k);
        assert(agg_outs(g, xs, k).len() == 1);
        lemma_select_identity(full_row(g, xs, k), q18_outs());
    }
    assert(fullrows(g, xs) =~= result_rows(g, xs));
}

/// The statement's body evaluates to the normal form's rows.
proof fn lemma_q18_eval(db: Database, m: M, ps: Seq<Literal>)
    requires bound_ok(db, m, ps),
    ensures denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(result_rows(q18_g(m, qp_of(ps)), q18_xs(db))),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_exprs);
    hide(agg_args);
    hide(group_caps);
    hide(gkeys);
    let p = qp_of(ps);
    let g = q18_g(m, p);
    let rows = from_rows(db);
    let xs = q18_xs(db);
    lemma_q18_shape(ps);
    lemma_widths(db);
    lemma_from_eval(db);
    lemma_pred_agrees(db, m, ps);
    lemma_filter_rows(db, q18_from(), rows, q18_cols(), q18_pred(ps), g);
    lemma_keys_args_agree(db, m, ps);
    lemma_keys_exact(db, m, ps);
    lemma_groups_link(db, m, p);
    reveal(group_caps);
    assert(group_caps(g, xs));
    assert(aggs_match(q18_aggs(), g)) by {
        assert(agg_matches(q18_aggs()[0], g.aggs[0]));
    }
    lemma_group_query(db, rows, q18_cols(), q18_filter(ps), q18_gkeys(), q18_aggs(), g);
    lemma_full_is_result(db, m, p);
}

/// The output row of a good order's group is its `grow`.
proof fn lemma_out_row(db: Database, m: M, p: QP, q: int)
    requires db_ok(db), rel_ok(m, db), model_ok(m), 0 <= q < m.o_n, good(m, p, q),
    ensures out_row(q18_g(m, p), q18_xs(db), keyq(m, q)) == grow(m, p, q),
{
    lemma_groups_link(db, m, p);
    let g = q18_g(m, p);
    let xs = q18_xs(db);
    let k = keyq(m, q);
    lemma_ccnt(m, ocust(m, q));
    crate::agent::facts::lemma_opos(m, okey(m, q));
    assert(gcount(g, xs, k) == kcnt(m, okey(m, q)));
    assert(agg_outs(g, xs, k) =~= seq![Val::Num { coeff: ksum(m, okey(m, q)), scale: 2 }]);
    lemma_select_identity(full_row(g, xs, k), q18_outs());
    assert(out_row(g, xs, k) =~= grow(m, p, q));
}

/// The normal form's rows are the good orders' rows, without duplicates.
proof fn lemma_rr_rows(db: Database, m: M, p: QP)
    requires db_ok(db), rel_ok(m, db), model_ok(m),
    ensures
        result_rows(q18_g(m, p), q18_xs(db)).no_duplicates(),
        forall|r: Row| #[trigger] result_rows(q18_g(m, p), q18_xs(db)).contains(r) <==> gseq(m, p, 0, m.o_n).contains(r),
{
    let g = q18_g(m, p);
    let xs = q18_xs(db);
    let gk = gkeys(g, xs);
    let rr = result_rows(g, xs);
    lemma_gkeys(g, xs);
    lemma_groups_link(db, m, p);
    lemma_gseq_contains(m, p, 0, m.o_n);
    assert forall|r: Row| #[trigger] rr.contains(r) <==> gseq(m, p, 0, m.o_n).contains(r) by {
        if rr.contains(r) {
            let i = choose|i: int| 0 <= i < rr.len() && rr[i] == r;
            let k = gk[i];
            assert(gk.contains(k));
            let q = qk(m, k);
            assert(good(m, p, q) && keyq(m, q) == k);
            lemma_out_row(db, m, p, q);
        }
        if gseq(m, p, 0, m.o_n).contains(r) {
            let q = choose|q: int| 0 <= q < m.o_n && good(m, p, q) && r == grow(m, p, q);
            let k = keyq(m, q);
            assert(gcount(g, xs, k) > 0);
            assert(gk.contains(k));
            let i = choose|i: int| 0 <= i < gk.len() && gk[i] == k;
            lemma_out_row(db, m, p, q);
            assert(rr[i] == r);
        }
    }
    assert forall|a: int, b: int| 0 <= a < rr.len() && 0 <= b < rr.len() && a != b implies rr[a] != rr[b] by {
        let (ka, kb) = (gk[a], gk[b]);
        assert(gk.contains(ka) && gk.contains(kb));
        lemma_gk_len(db, m, p, ka);
        lemma_gk_len(db, m, p, kb);
        if rr[a] == rr[b] {
            lemma_select_identity(full_row(g, xs, ka), q18_outs());
            lemma_select_identity(full_row(g, xs, kb), q18_outs());
            assert(rr[a][0] == ka[0] && rr[a][1] == ka[1] && rr[a][2] == ka[2] && rr[a][3] == ka[3] && rr[a][4] == ka[4]);
            assert(rr[b][0] == kb[0] && rr[b][1] == kb[1] && rr[b][2] == kb[2] && rr[b][3] == kb[3] && rr[b][4] == kb[4]);
            assert(ka =~= kb);
        }
    }
}

/// The good orders' rows are distinct and their ORDER BY keys are in their families.
pub proof fn lemma_gseq_wf(m: M, p: QP, lo: int, hi: int)
    requires model_ok(m), 0 <= lo, hi <= m.o_n,
    ensures rel_wf(q18_keys(), q18_fams(), gseq(m, p, lo, hi)),
{
    lemma_gseq_nodup(m, p, lo, hi);
    lemma_gseq_contains(m, p, lo, hi);
    let s = gseq(m, p, lo, hi);
    assert forall|i: int| 0 <= i < s.len() implies keys_ok(q18_keys(), q18_fams(), #[trigger] s[i]) by {
        assert(s.contains(s[i]));
        let q = choose|q: int| lo <= q < hi && good(m, p, q) && s[i] == grow(m, p, q);
        assert forall|t: int| 0 <= t < q18_keys().len() implies #[trigger] key_ok(q18_keys()[t], q18_fams()[t], s[i]) by {}
    }
}

/// A top 100 of the good orders' rows is an allowed output of the statement.
pub proof fn lemma_q18_ordered(db: Database, m: M, ps: Seq<Literal>, out: Seq<Row>)
    requires
        bound_ok(db, m, ps),
        topk_ok(q18_keys(), q18_fams(), 100, out, gseq(m, qp_of(ps), 0, m.o_n)),
    ensures ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    let p = qp_of(ps);
    let all = gseq(m, p, 0, m.o_n);
    lemma_q18_eval(db, m, ps);
    lemma_rr_rows(db, m, p);
    lemma_gseq_wf(m, p, 0, m.o_n);
    lemma_topk_ordered(q18_keys(), q18_fams(), 100, out, all);
    let pp = out + sort_rows(q18_keys(), rest_of(all, out));
    let rr = result_rows(q18_g(m, p), q18_xs(db));
    lemma_nodup_same_multiset(rr, all);
    lemma_q18_shape(ps);
    lemma_outcome_sorted(db, query_spec_at(ps), rr, pp);
}

} // verus!
