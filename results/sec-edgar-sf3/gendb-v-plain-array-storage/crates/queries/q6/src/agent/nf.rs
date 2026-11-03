//! The statement's GROUP BY in the toolkit's accumulator normal form (`link::query::QuerySpec`) over the joined
//! rows `num x sub x pre` (`sem::jrows`, all 39 columns): condition `sem::qual_of`, key `[s.name, p.stmt, n.tag,
//! p.plabel]`, aggregates `SUM(n.value)` (scale 4) and `COUNT(*)`, output columns `key ++ aggregates`.
//!
//! `lemma_body` states the body's denotation: the normal form's result rows, under its arithmetic domain
//! (`group_caps`). `lemma_gsums` reduces the normal form's accumulators over the joined rows to `ctx::gacc`, the
//! per-`pre`-row form the implementation computes: for each `pre` row the matching `sub` row is unique (the key of
//! `sub`), so the triple sum over `num x sub x pre` collapses to a sum over `pre` of `ctx::acc`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::order::*;
use crate::spec::numeric::abs;
use crate::spec::scalar::NumKind;
use crate::spec::equality::row_not_distinct;
use crate::bridge::collect::lemma_collect_all;
use crate::bridge::equality::same_exact_type;
use crate::link::query::*;
use crate::link::join::*;
use crate::agent::ctx::*;
use crate::agent::sem::*;

verus! {

/// The normal form of the statement's GROUP BY.
pub open spec fn qs(c: Ctx) -> QuerySpec {
    QuerySpec {
        qual: qual_of(c),
        key: |x: Row| seq![x[11], x[32], x[1], x[37]],
        arg: |j: int, x: Row| if j == 0 { x[7]->Num_coeff } else { 0int },
        aggs: seq![AggKind::Sum { scale: 4 }, AggKind::Count],
        outs: seq![0nat, 1, 2, 3, 4, 5],
        grouped: true,
    }
}

/// All 39 columns of a joined row.
pub open spec fn id_cols() -> Seq<nat> {
    Seq::new(39, |i: int| i as nat)
}

pub proof fn lemma_proj_id(db: Database, c: Ctx)
    requires db_ok(db, c),
    ensures proj_all(jrows(db), id_cols()) == jrows(db),
{
    let jr = jrows(db);
    assert forall|r: int| 0 <= r < jr.len() implies proj(#[trigger] jr[r], id_cols()) == jr[r] by {
        assert(jr.contains(jr[r]));
        let (i, s, k) = lemma_jrow_of(db, c, jr[r]);
        lemma_jcells(c, i, s, k);
        assert(proj(jr[r], id_cols()) =~= jr[r]);
    }
    assert(proj_all(jr, id_cols()) =~= jr);
}

/// The key of a joined row.
pub proof fn lemma_row_key(c: Ctx, i: int, s: int, k: int)
    ensures ((qs(c)).key)(jrow(c, i, s, k)) == seq![Val::Text(s_name(c, s)), (if p_stmtv_s(c)[k] == 0 { Val::Null } else { Val::Text(p_stmt(c, k)) }), Val::Text(n_tag(c, i)), p_plabel_val(c, k)],
{
    lemma_jcells(c, i, s, k);
    let x = jrow(c, i, s, k);
    assert(((qs(c)).key)(x) =~= seq![Val::Text(s_name(c, s)), (if p_stmtv_s(c)[k] == 0 { Val::Null } else { Val::Text(p_stmt(c, k)) }), Val::Text(n_tag(c, i)), p_plabel_val(c, k)]);
}

/// The GROUP BY keys of a 39-column row evaluate to its normal-form key.
pub proof fn lemma_env_keys(db: Database, c: Ctx, x: Row)
    requires x.len() == 39,
    ensures eval_exprs(db, x, g_keys()) == Ok::<Row, SqlError>(((qs(c)).key)(x)),
{
    let idxs = seq![11nat, 32, 1, 37];
    assert(g_keys() =~= col_exprs(idxs));
    lemma_eval_cols(db, x, idxs);
    assert(select(x, idxs) =~= ((qs(c)).key)(x));
}

/// The per-aggregate argument outcomes of a row: its column 7, then NULL for `COUNT(*)`.
proof fn lemma_arg_results(db: Database, x: Row)
    requires x.len() == 39,
    ensures agg_arg_results(db, x, g_aggs()) == seq![Ok::<Val, SqlError>(x[7]), Ok::<Val, SqlError>(Val::Null)],
{
    hide(eval_expr);
    hide(agg_arg);
    lemma_agg_arg_results_index(db, x, g_aggs());
    lemma_agg_arg_sum(db, x, NumKind::Numeric, Expr::Col(7));
    lemma_agg_arg_count(db, x);
    crate::link::expr::lemma_expr_col(db, x, 7);
    assert(agg_arg_results(db, x, g_aggs()) =~= seq![Ok::<Val, SqlError>(x[7]), Ok::<Val, SqlError>(Val::Null)]);
}

/// The normal-form arguments of a row whose column 7 is the numeric `v` at scale 4.
proof fn lemma_arg_vals(c: Ctx, x: Row, v: int)
    requires x[7] == (Val::Num { coeff: v, scale: 4 }),
    ensures arg_vals(qs(c), x) == seq![Val::Num { coeff: v, scale: 4 }, Val::Null],
{
    assert(arg_vals(qs(c), x) =~= seq![Val::Num { coeff: v, scale: 4 }, Val::Null]);
}

/// Two successful outcomes collect to their two values.
proof fn lemma_collect_two(a: Val, b: Val)
    ensures collect(seq![Ok::<Val, SqlError>(a), Ok::<Val, SqlError>(b)]) == Ok::<Seq<Val>, SqlError>(seq![a, b]),
{
    let rs = seq![Ok::<Val, SqlError>(a), Ok::<Val, SqlError>(b)];
    let vs = seq![a, b];
    assert forall|j: int| 0 <= j < rs.len() implies #[trigger] rs[j] == Ok::<Val, SqlError>(vs[j]) by {}
    lemma_collect_all(rs, vs);
}

/// The aggregate arguments of a row whose column 7 is a numeric at scale 4.
pub proof fn lemma_env_args(db: Database, c: Ctx, x: Row, v: int)
    requires x.len() == 39, x[7] == (Val::Num { coeff: v, scale: 4 }),
    ensures agg_args(db, x, g_aggs()) == Ok::<Row, SqlError>(arg_vals(qs(c), x)),
{
    lemma_arg_results(db, x);
    lemma_arg_vals(c, x, v);
    lemma_collect_two(x[7], Val::Null);
}

/// Keys and arguments of a joined row.
pub proof fn lemma_row_agrees(db: Database, c: Ctx, i: int, s: int, k: int)
    ensures
        eval_exprs(db, jrow(c, i, s, k), g_keys()) == Ok::<Row, SqlError>(((qs(c)).key)(jrow(c, i, s, k))),
        agg_args(db, jrow(c, i, s, k), g_aggs()) == Ok::<Row, SqlError>(arg_vals(qs(c), jrow(c, i, s, k))),
{
    lemma_jcells(c, i, s, k);
    lemma_env_keys(db, c, jrow(c, i, s, k));
    lemma_env_args(db, c, jrow(c, i, s, k), n_val(c, i));
}

/// On the qualifying joined rows SQL "not distinct" of keys is structural equality.
pub proof fn lemma_keys_exact(db: Database, c: Ctx)
    requires db_ok(db, c),
    ensures keys_exact(qs(c), jrows(db)),
{
    let g = qs(c);
    let xs = jrows(db);
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        assert(xs.contains(xs[a]) && xs.contains(xs[b]));
        let (i1, s1, k1) = lemma_jrow_of(db, c, xs[a]);
        let (i2, s2, k2) = lemma_jrow_of(db, c, xs[b]);
        lemma_row_key(c, i1, s1, k1);
        lemma_row_key(c, i2, s2, k2);
        let ka = (g.key)(xs[a]);
        let kb = (g.key)(xs[b]);
        assert forall|t: int| 0 <= t < ka.len() implies same_exact_type(#[trigger] ka[t], kb[t]) by {}
        lemma_row_exact(ka, kb);
    }
}

/// The body of the statement is the normal form's result rows (inside its arithmetic domain).
#[verifier::spinoff_prover]
pub proof fn lemma_body(db: Database, c: Ctx, ps: Seq<Literal>)
    requires db_ok(db, c), lits_ok(c, ps), group_caps(qs(c), jrows(db)),
    ensures eval_query(db, Seq::empty(), q_body(ps[0], ps[1], ps[2])) == Ok::<Relation, SqlError>(result_rows(qs(c), jrows(db))),
{
    hide(eval_query);
    hide(eval_exprs);
    hide(agg_args);
    let g = qs(c);
    let jr = jrows(db);
    let cols = id_cols();
    lemma_input(db, c, ps);
    lemma_proj_id(db, c);
    let xs = proj_all(jr, cols);
    assert(xs == jr);
    let truths = qual_truths(g, xs);
    lemma_keep_true_keep(jr, truths, g.qual);
    assert forall|r: int| 0 <= r < jr.len() && (g.qual)(proj(#[trigger] jr[r], cols)) implies
        eval_exprs(db, jr[r], g_keys()) == Ok::<Row, SqlError>((g.key)(proj(jr[r], cols)))
        && agg_args(db, jr[r], g_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(jr[r], cols))) by {
        assert(xs[r] == proj(jr[r], cols));
        assert(jr.contains(jr[r]));
        let (i, s, k) = lemma_jrow_of(db, c, jr[r]);
        lemma_row_agrees(db, c, i, s, k);
    }
    assert(keys_agree(db, jr, cols, g_keys(), g));
    assert(args_agree(db, jr, cols, g_aggs(), g));
    assert(aggs_match(g_aggs(), g));
    lemma_keys_exact(db, c);
    lemma_group_query(db, jr, cols, q_input(ps[0], ps[1], ps[2]), g_keys(), g_aggs(), g);
    // `outs` selects every column of `key ++ aggregates`.
    let gk = gkeys(g, jr);
    assert forall|t: int| 0 <= t < gk.len() implies out_row(g, jr, #[trigger] gk[t]) == full_row(g, jr, gk[t]) by {
        let kk = gk[t];
        lemma_gkeys(g, jr);
        assert(gk.contains(kk));
        lemma_gkeys_witness(g, jr, kk);
        let r = choose|r: int| 0 <= r < jr.len() && #[trigger] hit(g, jr[r], kk);
        assert(jr.contains(jr[r]));
        let (i, s, k) = lemma_jrow_of(db, c, jr[r]);
        lemma_row_key(c, i, s, k);
        assert(kk.len() == 4);
        let fr = full_row(g, jr, kk);
        assert(fr.len() == 6);
        lemma_select_identity(fr, g.outs);
    }
    assert(gk.map_values(|k: Row| out_row(g, jr, k)) =~= gk.map_values(|k: Row| full_row(g, jr, k)));
}

} // verus!
