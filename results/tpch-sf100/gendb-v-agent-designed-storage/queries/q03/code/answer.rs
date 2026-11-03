//! The Q3 statement's meaning on a database bound to the parts: its body (`Project` over `GroupBy` over the
//! filtered FROM product) evaluates to the normal form's rows, which are exactly the good orders' rows `gseq`
//! (`lemma_q3_denote`, inside the SUM capacity condition `caps_ok`), so a top 10 of `gseq` under the ORDER BY keys is
//! an allowed output of the statement (`lemma_q3_ordered`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::order::*;
use crate::spec::relation::keep_true;
use crate::query::{query_spec_at, param_domain};
use crate::link::query::*;
use crate::link::source::lemma_proj_all_index;
use crate::link::outcome::lemma_outcome_sorted;
use crate::link::expr::{ival, i128_max};
use crate::bridge::equality::same_exact_type;
use crate::spec::equality::row_not_distinct;
use crate::bridge::order::{keys_ok, key_ok, all_keys_ok};
use crate::bridge::typing::val_family;
use super::common::topk::*;
use super::model::*;
use super::qspec::*;
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
    ensures pred_agrees(db, from_rows(db), q3_cols(), q3_pred(ps), q3_g(qp_of(ps))),
{
    let p = qp_of(ps);
    let rows = from_rows(db);
    assert forall|i: int| 0 <= i < rows.len() implies
        eval_pred(db, #[trigger] rows[i], q3_pred(ps)) == Ok::<Truth, SqlError>(truth_of((q3_g(p).qual)(proj(rows[i], q3_cols())))) by {
        let (c, q, j) = lemma_from_row(db, m, i);
        lemma_pred_eval(db, rows[i], ps, ckey(m, c), segtext(m, c), okey(m, q), ocust(m, q), odate(m, q), lkey(m, j), lship(m, j));
        lemma_term(m, p, Seq::empty(), c, q, j);
    }
}

/// The group key and the SUM argument agree with the normal form on every FROM row.
pub proof fn lemma_keys_args_agree(db: Database, m: M, ps: Seq<Literal>)
    requires bound_ok(db, m, ps),
    ensures
        keys_agree(db, from_rows(db), q3_cols(), q3_gkeys(), q3_g(qp_of(ps))),
        args_agree(db, from_rows(db), q3_cols(), q3_aggs(), q3_g(qp_of(ps))),
{
    let p = qp_of(ps);
    let g = q3_g(p);
    let rows = from_rows(db);
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], q3_cols())) implies
        eval_exprs(db, rows[i], q3_gkeys()) == Ok::<Row, SqlError>((g.key)(proj(rows[i], q3_cols()))) by {
        let (c, q, j) = lemma_from_row(db, m, i);
        lemma_keys_eval(db, rows[i], odate(m, q), osp(m, q), lkey(m, j));
        lemma_term(m, p, Seq::empty(), c, q, j);
    }
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], q3_cols())) implies
        agg_args(db, rows[i], q3_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[i], q3_cols()))) by {
        let (c, q, j) = lemma_from_row(db, m, i);
        lemma_args_eval(db, rows[i], lprice(m, j), ldisc(m, j));
        lemma_term(m, p, Seq::empty(), c, q, j);
        assert(arg_vals(g, proj(rows[i], q3_cols())) =~= seq![Val::Num { coeff: larg(m, j), scale: 4 }]);
    }
}

/// Group keys of qualifying rows have one exact type per position.
pub proof fn lemma_keys_exact(db: Database, m: M, ps: Seq<Literal>)
    requires bound_ok(db, m, ps),
    ensures keys_exact(q3_g(qp_of(ps)), q3_xs(db)),
{
    let p = qp_of(ps);
    let g = q3_g(p);
    let rows = from_rows(db);
    let xs = q3_xs(db);
    lemma_proj_all_index(rows, q3_cols());
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

/// Every group key has three columns, every GROUP BY row four.
proof fn lemma_group_widths(db: Database, m: M, ps: Seq<Literal>)
    requires bound_ok(db, m, ps),
    ensures ({
        let g = q3_g(qp_of(ps));
        let xs = q3_xs(db);
        forall|i: int| 0 <= i < fullrows(g, xs).len() ==> (#[trigger] fullrows(g, xs)[i]).len() == 4
    }),
{
    let g = q3_g(qp_of(ps));
    let xs = q3_xs(db);
    let gk = gkeys(g, xs);
    assert forall|i: int| 0 <= i < fullrows(g, xs).len() implies (#[trigger] fullrows(g, xs)[i]).len() == 4 by {
        let k = gk[i];
        assert(gk.contains(k));
        lemma_gkeys_witness(g, xs, k);
        let t = choose|t: int| 0 <= t < xs.len() && #[trigger] hit(g, xs[t], k);
        assert((g.key)(xs[t]) == k);
        assert(k.len() == 3);
        assert(agg_outs(g, xs, k).len() == 1);
    }
}

/// The output row of a good order's group is its `grow`.
proof fn lemma_out_row(db: Database, m: M, p: QP, q: int)
    requires db_ok(db), rel_ok(m, db), model_ok(m), 0 <= q < m.o_n, good(m, p, q),
    ensures out_row(q3_g(p), q3_xs(db), keyq(m, q)) == grow(m, p, q),
{
    lemma_groups_link(db, m, p);
    let g = q3_g(p);
    let xs = q3_xs(db);
    let k = keyq(m, q);
    assert(gcount(g, xs, k) == lcnt(m, p, q));
    assert(agg_outs(g, xs, k) =~= seq![Val::Num { coeff: lsum(m, p, q), scale: 4 }]);
    assert(out_row(g, xs, k) =~= grow(m, p, q));
}

/// The normal form's groups are inside the SUM capacity condition.
proof fn lemma_group_caps(db: Database, m: M, p: QP)
    requires db_ok(db), rel_ok(m, db), model_ok(m), caps_ok(m, p),
    ensures group_caps(q3_g(p), q3_xs(db)), aggs_match(q3_aggs(), q3_g(p)),
{
    lemma_groups_link(db, m, p);
}

/// The statement's body evaluates to the normal form's rows.
proof fn lemma_q3_eval(db: Database, m: M, ps: Seq<Literal>)
    requires bound_ok(db, m, ps), caps_ok(m, qp_of(ps)),
    ensures denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(result_rows(q3_g(qp_of(ps)), q3_xs(db))),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_exprs);
    hide(agg_args);
    hide(group_caps);
    hide(gkeys);
    let p = qp_of(ps);
    let g = q3_g(p);
    let rows = from_rows(db);
    let xs = q3_xs(db);
    lemma_q3_shape(ps);
    lemma_widths(db);
    lemma_from_eval(db);
    lemma_pred_agrees(db, m, ps);
    lemma_filter_rows(db, q3_from(), rows, q3_cols(), q3_pred(ps), g);
    lemma_keys_args_agree(db, m, ps);
    lemma_keys_exact(db, m, ps);
    lemma_group_caps(db, m, p);
    lemma_group_query(db, rows, q3_cols(), q3_filter(ps), q3_gkeys(), q3_aggs(), g);
    let fr = fullrows(g, xs);
    lemma_group_widths(db, m, ps);
    lemma_project_cols(db, q3_group(ps), fr, q3_outs(), 4);
    assert(fr.map_values(|r: Row| select(r, q3_outs())) =~= result_rows(g, xs));
}

/// Every group key of the normal form has three columns.
proof fn lemma_gk_len(db: Database, m: M, p: QP, k: Row)
    requires gkeys(q3_g(p), q3_xs(db)).contains(k),
    ensures k.len() == 3,
{
    let g = q3_g(p);
    let xs = q3_xs(db);
    lemma_gkeys_witness(g, xs, k);
    let t = choose|t: int| 0 <= t < xs.len() && #[trigger] hit(g, xs[t], k);
    assert((g.key)(xs[t]) == k);
}

/// The normal form's rows are the good orders' rows, without duplicates.
proof fn lemma_rr_rows(db: Database, m: M, p: QP)
    requires db_ok(db), rel_ok(m, db), model_ok(m),
    ensures
        result_rows(q3_g(p), q3_xs(db)).no_duplicates(),
        forall|r: Row| #[trigger] result_rows(q3_g(p), q3_xs(db)).contains(r) <==> gseq(m, p, 0, m.o_n).contains(r),
{
    let g = q3_g(p);
    let xs = q3_xs(db);
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
            assert(rr[a][0] == ka[0] && rr[a][2] == ka[1] && rr[a][3] == ka[2]);
            assert(rr[b][0] == kb[0] && rr[b][2] == kb[1] && rr[b][3] == kb[2]);
            assert(ka =~= kb);
        }
    }
}

/// The statement's body is the normal form's rows, which are the good orders' rows.
pub proof fn lemma_q3_denote(db: Database, m: M, ps: Seq<Literal>)
    requires bound_ok(db, m, ps), caps_ok(m, qp_of(ps)),
    ensures
        denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(result_rows(q3_g(qp_of(ps)), q3_xs(db))),
        result_rows(q3_g(qp_of(ps)), q3_xs(db)).no_duplicates(),
        forall|r: Row| #[trigger] result_rows(q3_g(qp_of(ps)), q3_xs(db)).contains(r) <==> gseq(m, qp_of(ps), 0, m.o_n).contains(r),
{
    lemma_q3_eval(db, m, ps);
    lemma_rr_rows(db, m, qp_of(ps));
}

/// The good orders' rows are distinct and their ORDER BY keys are in their families.
pub proof fn lemma_gseq_wf(m: M, p: QP)
    requires model_ok(m),
    ensures rel_wf(q3_keys(), q3_fams(), gseq(m, p, 0, m.o_n)),
{
    lemma_gseq_nodup(m, p, 0, m.o_n);
    lemma_gseq_contains(m, p, 0, m.o_n);
    let s = gseq(m, p, 0, m.o_n);
    assert forall|i: int| 0 <= i < s.len() implies keys_ok(q3_keys(), q3_fams(), #[trigger] s[i]) by {
        assert(s.contains(s[i]));
        let q = choose|q: int| 0 <= q < m.o_n && good(m, p, q) && s[i] == grow(m, p, q);
        assert forall|t: int| 0 <= t < q3_keys().len() implies #[trigger] key_ok(q3_keys()[t], q3_fams()[t], s[i]) by {}
    }
}

/// A top 10 of the good orders' rows is an allowed output of the statement.
pub proof fn lemma_q3_ordered(db: Database, m: M, ps: Seq<Literal>, out: Seq<Row>)
    requires
        bound_ok(db, m, ps),
        caps_ok(m, qp_of(ps)),
        topk_ok(q3_keys(), q3_fams(), 10, out, gseq(m, qp_of(ps), 0, m.o_n)),
    ensures ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    let p = qp_of(ps);
    let all = gseq(m, p, 0, m.o_n);
    lemma_q3_denote(db, m, ps);
    lemma_gseq_wf(m, p);
    lemma_topk_ordered(q3_keys(), q3_fams(), 10, out, all);
    let pp = out + sort_rows(q3_keys(), rest_of(all, out));
    let rr = result_rows(q3_g(p), q3_xs(db));
    lemma_nodup_same_multiset(rr, all);
    lemma_q3_shape(ps);
    lemma_outcome_sorted(db, query_spec_at(ps), rr, pp);
}

} // verus!
