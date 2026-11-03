//! The Q10 statement's meaning on a database bound to the parts: its body (`Project` over `GroupBy` over the
//! filtered FROM product) evaluates to the normal form's rows, which are exactly the good customers' rows `gseq`
//! (`lemma_q10_denote`, inside the SUM capacity condition `caps_ok`), so a top 20 of `gseq` under the ORDER BY key is
//! an allowed output of the statement (`lemma_q10_ordered`). When `$1 + 3 months` fails and the FROM product has a
//! row, the statement's meaning is that error (`lemma_q10_date_err`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::order::*;
use crate::spec::relation::{keep_true, product_rows};
use crate::query::{query_spec_at, param_domain};
use crate::link::query::*;
use crate::link::source::lemma_proj_all_index;
use crate::link::outcome::lemma_outcome_sorted;
use crate::link::expr::{ival, i128_max};
use crate::bridge::equality::same_exact_type;
use crate::spec::equality::row_not_distinct;
use crate::bridge::order::{keys_ok, key_ok, all_keys_ok};
use super::common::topk::*;
use super::model::*;
use super::qspec::*;
use super::window::*;
use super::sqlrow::*;
use super::sqllink::*;
use super::cand::lemma_cand_cmp;

verus! {

/// The facts of a database bound to the parts, at one binding and window.
pub open spec fn bound_ok(db: Database, m: M, ps: Seq<Literal>, p: QP) -> bool {
    &&& db_ok(db)
    &&& rel_ok(m, db)
    &&& model_ok(m)
    &&& param_domain(ps)
    &&& p.lo == lo_of(ps)
    &&& from_rows(db).len() > 0 ==> hi_ok(lo_of(ps), p.hi)
}

/// The WHERE of the statement agrees with the normal form on every FROM row.
pub proof fn lemma_pred_agrees(db: Database, m: M, ps: Seq<Literal>, p: QP)
    requires bound_ok(db, m, ps, p),
    ensures pred_agrees(db, from_rows(db), q10_cols(), q10_pred(ps), q10_g(p)),
{
    let rows = from_rows(db);
    assert forall|i: int| 0 <= i < rows.len() implies
        eval_pred(db, #[trigger] rows[i], q10_pred(ps)) == Ok::<Truth, SqlError>(truth_of((q10_g(p).qual)(proj(rows[i], q10_cols())))) by {
        let (c, q, j, n) = lemma_from_row(db, m, i);
        lemma_pred_eval(db, rows[i], ps, p.hi, ckey(m, c), cnat(m, c), okey(m, q), ocust(m, q), odate(m, q), lkey(m, j),
            lflag(m, j), nkey(m, n));
        lemma_term(m, p, Seq::empty(), c, q, j, n);
    }
}

/// The group key and the SUM argument agree with the normal form on every FROM row.
pub proof fn lemma_keys_args_agree(db: Database, m: M, ps: Seq<Literal>, p: QP)
    requires bound_ok(db, m, ps, p),
    ensures
        keys_agree(db, from_rows(db), q10_cols(), q10_gkeys(), q10_g(p)),
        args_agree(db, from_rows(db), q10_cols(), q10_aggs(), q10_g(p)),
{
    let g = q10_g(p);
    let rows = from_rows(db);
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], q10_cols())) implies
        eval_exprs(db, rows[i], q10_gkeys()) == Ok::<Row, SqlError>((g.key)(proj(rows[i], q10_cols()))) by {
        let (c, q, j, n) = lemma_from_row(db, m, i);
        lemma_keys_eval(db, rows[i]);
        lemma_term(m, p, Seq::empty(), c, q, j, n);
        let env = rows[i];
        assert(seq![env[0], env[1], env[5], env[4], env[34], env[2], env[7]] =~= keyc(m, c, n));
    }
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], q10_cols())) implies
        agg_args(db, rows[i], q10_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[i], q10_cols()))) by {
        let (c, q, j, n) = lemma_from_row(db, m, i);
        assert(in_i64(lkey(m, j)));
        lemma_args_eval(db, rows[i], lprice(m, j), ldisc(m, j));
        lemma_term(m, p, Seq::empty(), c, q, j, n);
        assert(arg_vals(g, proj(rows[i], q10_cols())) =~= seq![Val::Num { coeff: larg(m, j), scale: 4 }]);
    }
}

/// Group keys of qualifying rows have one exact type per position.
pub proof fn lemma_keys_exact(db: Database, m: M, ps: Seq<Literal>, p: QP)
    requires bound_ok(db, m, ps, p),
    ensures keys_exact(q10_g(p), q10_xs(db)),
{
    let g = q10_g(p);
    let rows = from_rows(db);
    let xs = q10_xs(db);
    lemma_proj_all_index(rows, q10_cols());
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        let (ca, qa, ja, na) = lemma_from_row(db, m, a);
        let (cb, qb, jb, nb) = lemma_from_row(db, m, b);
        lemma_term(m, p, Seq::empty(), ca, qa, ja, na);
        lemma_term(m, p, Seq::empty(), cb, qb, jb, nb);
        let (ka, kb) = ((g.key)(xs[a]), (g.key)(xs[b]));
        assert forall|t: int| 0 <= t < ka.len() implies same_exact_type(#[trigger] ka[t], kb[t]) by {}
        lemma_row_exact(ka, kb);
    }
}

/// The GROUP BY rows of the normal form (`key ++ aggregates` of every group, first-occurrence order).
pub open spec fn fullrows(g: QuerySpec, xs: Seq<Row>) -> Seq<Row> {
    gkeys(g, xs).map_values(|k: Row| full_row(g, xs, k))
}

/// Every group key has seven columns, every GROUP BY row eight.
proof fn lemma_group_widths(db: Database, m: M, ps: Seq<Literal>, p: QP)
    requires bound_ok(db, m, ps, p),
    ensures ({
        let g = q10_g(p);
        let xs = q10_xs(db);
        forall|i: int| 0 <= i < fullrows(g, xs).len() ==> (#[trigger] fullrows(g, xs)[i]).len() == 8
    }),
{
    let g = q10_g(p);
    let xs = q10_xs(db);
    let gk = gkeys(g, xs);
    assert forall|i: int| 0 <= i < fullrows(g, xs).len() implies (#[trigger] fullrows(g, xs)[i]).len() == 8 by {
        let k = gk[i];
        assert(gk.contains(k));
        lemma_gkeys_witness(g, xs, k);
        let t = choose|t: int| 0 <= t < xs.len() && #[trigger] hit(g, xs[t], k);
        assert((g.key)(xs[t]) == k);
        assert(k.len() == 7);
        assert(agg_outs(g, xs, k).len() == 1);
    }
}

/// The output row of a good customer's group is its `grow`.
proof fn lemma_out_row(db: Database, m: M, p: QP, c: int)
    requires db_ok(db), rel_ok(m, db), model_ok(m), 0 <= c < m.c_n, good(m, p, c),
    ensures out_row(q10_g(p), q10_xs(db), keyq(m, c)) == grow(m, p, c),
{
    lemma_groups_link(db, m, p);
    let g = q10_g(p);
    let xs = q10_xs(db);
    let k = keyq(m, c);
    assert(gcount(g, xs, k) == ccnt(m, p, c));
    assert(agg_outs(g, xs, k) =~= seq![Val::Num { coeff: csum(m, p, c), scale: 4 }]);
    assert(out_row(g, xs, k) =~= grow(m, p, c));
}

/// The normal form's groups are inside the SUM capacity condition.
proof fn lemma_group_caps(db: Database, m: M, p: QP)
    requires db_ok(db), rel_ok(m, db), model_ok(m), caps_ok(m, p),
    ensures group_caps(q10_g(p), q10_xs(db)), aggs_match(q10_aggs(), q10_g(p)),
{
    lemma_groups_link(db, m, p);
}

/// The statement's body evaluates to the normal form's rows.
proof fn lemma_q10_eval(db: Database, m: M, ps: Seq<Literal>, p: QP)
    requires bound_ok(db, m, ps, p), caps_ok(m, p),
    ensures denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(result_rows(q10_g(p), q10_xs(db))),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_exprs);
    hide(agg_args);
    hide(group_caps);
    hide(gkeys);
    let g = q10_g(p);
    let rows = from_rows(db);
    let xs = q10_xs(db);
    lemma_q10_shape(ps);
    lemma_widths(db);
    lemma_from_eval(db);
    lemma_pred_agrees(db, m, ps, p);
    lemma_filter_rows(db, q10_from(), rows, q10_cols(), q10_pred(ps), g);
    lemma_keys_args_agree(db, m, ps, p);
    lemma_keys_exact(db, m, ps, p);
    lemma_group_caps(db, m, p);
    lemma_group_query(db, rows, q10_cols(), q10_filter(ps), q10_gkeys(), q10_aggs(), g);
    let fr = fullrows(g, xs);
    lemma_group_widths(db, m, ps, p);
    lemma_project_cols(db, q10_group(ps), fr, q10_outs(), 8);
    assert(fr.map_values(|r: Row| select(r, q10_outs())) =~= result_rows(g, xs));
}

/// Every group key of the normal form has seven columns.
proof fn lemma_gk_len(db: Database, m: M, p: QP, k: Row)
    requires gkeys(q10_g(p), q10_xs(db)).contains(k),
    ensures k.len() == 7,
{
    let g = q10_g(p);
    let xs = q10_xs(db);
    lemma_gkeys_witness(g, xs, k);
    let t = choose|t: int| 0 <= t < xs.len() && #[trigger] hit(g, xs[t], k);
    assert((g.key)(xs[t]) == k);
}

/// The normal form's rows are the good customers' rows, without duplicates.
proof fn lemma_rr_rows(db: Database, m: M, p: QP)
    requires db_ok(db), rel_ok(m, db), model_ok(m),
    ensures
        result_rows(q10_g(p), q10_xs(db)).no_duplicates(),
        forall|r: Row| #[trigger] result_rows(q10_g(p), q10_xs(db)).contains(r) <==> gseq(m, p, 0, m.c_n).contains(r),
{
    let g = q10_g(p);
    let xs = q10_xs(db);
    let gk = gkeys(g, xs);
    let rr = result_rows(g, xs);
    lemma_gkeys(g, xs);
    lemma_groups_link(db, m, p);
    lemma_gseq_contains(m, p, 0, m.c_n);
    assert forall|r: Row| #[trigger] rr.contains(r) <==> gseq(m, p, 0, m.c_n).contains(r) by {
        if rr.contains(r) {
            let i = choose|i: int| 0 <= i < rr.len() && rr[i] == r;
            let k = gk[i];
            assert(gk.contains(k));
            let c = ck_of(m, k);
            assert(good(m, p, c) && keyq(m, c) == k);
            lemma_out_row(db, m, p, c);
        }
        if gseq(m, p, 0, m.c_n).contains(r) {
            let c = choose|c: int| 0 <= c < m.c_n && good(m, p, c) && r == grow(m, p, c);
            let k = keyq(m, c);
            assert(gcount(g, xs, k) > 0);
            assert(gk.contains(k));
            let i = choose|i: int| 0 <= i < gk.len() && gk[i] == k;
            lemma_out_row(db, m, p, c);
            assert(rr[i] == r);
        }
    }
    assert forall|a: int, b: int| 0 <= a < rr.len() && 0 <= b < rr.len() && a != b implies rr[a] != rr[b] by {
        let (ka, kb) = (gk[a], gk[b]);
        assert(gk.contains(ka) && gk.contains(kb));
        lemma_gk_len(db, m, p, ka);
        lemma_gk_len(db, m, p, kb);
        if rr[a] == rr[b] {
            assert(rr[a][0] == ka[0] && rr[a][1] == ka[1] && rr[a][3] == ka[2] && rr[a][6] == ka[3]);
            assert(rr[a][4] == ka[4] && rr[a][5] == ka[5] && rr[a][7] == ka[6]);
            assert(rr[b][0] == kb[0] && rr[b][1] == kb[1] && rr[b][3] == kb[2] && rr[b][6] == kb[3]);
            assert(rr[b][4] == kb[4] && rr[b][5] == kb[5] && rr[b][7] == kb[6]);
            assert(ka =~= kb);
        }
    }
}

/// The statement's body is the normal form's rows, which are the good customers' rows.
pub proof fn lemma_q10_denote(db: Database, m: M, ps: Seq<Literal>, p: QP)
    requires bound_ok(db, m, ps, p), caps_ok(m, p),
    ensures
        denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(result_rows(q10_g(p), q10_xs(db))),
        result_rows(q10_g(p), q10_xs(db)).no_duplicates(),
        forall|r: Row| #[trigger] result_rows(q10_g(p), q10_xs(db)).contains(r) <==> gseq(m, p, 0, m.c_n).contains(r),
{
    lemma_q10_eval(db, m, ps, p);
    lemma_rr_rows(db, m, p);
}

/// The good customers' rows are distinct and their ORDER BY keys are in their families.
pub proof fn lemma_gseq_wf(m: M, p: QP)
    requires model_ok(m),
    ensures rel_wf(q10_keys(), q10_fams(), gseq(m, p, 0, m.c_n)),
{
    crate::agent::phase2::lemma_gseq_wf_range(m, p, 0, m.c_n);
}

/// A top 20 of the good customers' rows is an allowed output of the statement.
pub proof fn lemma_q10_ordered(db: Database, m: M, ps: Seq<Literal>, p: QP, out: Seq<Row>)
    requires
        bound_ok(db, m, ps, p),
        caps_ok(m, p),
        topk_ok(q10_keys(), q10_fams(), 20, out, gseq(m, p, 0, m.c_n)),
    ensures ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    let all = gseq(m, p, 0, m.c_n);
    lemma_q10_denote(db, m, ps, p);
    lemma_gseq_wf(m, p);
    lemma_topk_ordered(q10_keys(), q10_fams(), 20, out, all);
    let pp = out + sort_rows(q10_keys(), rest_of(all, out));
    let rr = result_rows(q10_g(p), q10_xs(db));
    lemma_nodup_same_multiset(rr, all);
    lemma_q10_shape(ps);
    lemma_outcome_sorted(db, query_spec_at(ps), rr, pp);
}

// ------------------------------------------------------------------------------------------------ the date error

proof fn lemma_groupby_err_input(db: Database, keys: Seq<Expr>, aggs: Seq<Agg>, input: Query, e: SqlError)
    requires eval_query(db, Seq::empty(), input) == Err::<Relation, SqlError>(e),
    ensures eval_query(db, Seq::empty(), Query::GroupBy { keys, aggs, input: Box::new(input) }) == Err::<Relation, SqlError>(e),
{
}

proof fn lemma_project_err_input(db: Database, exprs: Seq<Expr>, input: Query, e: SqlError)
    requires eval_query(db, Seq::empty(), input) == Err::<Relation, SqlError>(e),
    ensures eval_query(db, Seq::empty(), Query::Project { exprs, input: Box::new(input) }) == Err::<Relation, SqlError>(e),
{
}

/// When `$1 + 3 months` fails and the FROM product has a row, the statement's meaning is that error.
pub proof fn lemma_q10_date_err(db: Database, m: M, ps: Seq<Literal>)
    requires
        db_ok(db), rel_ok(m, db), model_ok(m), param_domain(ps),
        from_rows(db).len() > 0,
        hi_value(lo_of(ps)) is Err,
    ensures
        ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(hi_value(lo_of(ps))->Err_0)),
{
    hide(eval_query);
    hide(eval_pred);
    let e = hi_value(lo_of(ps))->Err_0;
    let rows = from_rows(db);
    lemma_q10_shape(ps);
    lemma_widths(db);
    lemma_from_eval(db);
    assert forall|k: int| 0 <= k < rows.len() implies #[trigger] eval_pred(db, Seq::<Val>::empty() + rows[k], q10_pred(ps)) is Ok
        || eval_pred(db, Seq::<Val>::empty() + rows[k], q10_pred(ps)) == Err::<Truth, SqlError>(e) by {
        assert(Seq::<Val>::empty() + rows[k] =~= rows[k]);
        let (c, q, j, n) = lemma_from_row(db, m, k);
        lemma_pred_err(db, rows[k], ps, ckey(m, c), okey(m, q), ocust(m, q), odate(m, q), lkey(m, j));
    }
    assert(Seq::<Val>::empty() + rows[0] =~= rows[0]);
    let (c, q, j, n) = lemma_from_row(db, m, 0);
    lemma_pred_err(db, rows[0], ps, ckey(m, c), okey(m, q), ocust(m, q), odate(m, q), lkey(m, j));
    crate::link::capacity::lemma_filter_err(db, Seq::empty(), q10_pred(ps), Box::new(q10_from()), rows, e, 0);
    lemma_groupby_err_input(db, q10_gkeys(), q10_aggs(), q10_filter(ps), e);
    lemma_project_err_input(db, col_exprs(q10_outs()), q10_group(ps), e);
}

} // verus!
