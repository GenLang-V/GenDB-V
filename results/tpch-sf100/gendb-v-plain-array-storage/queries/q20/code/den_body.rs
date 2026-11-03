//! The statement's body `SELECT s_name, s_address FROM supplier, nation WHERE ..` over one database:
//!
//! - FROM is the supplier-major product of the supplier and nation rows; row `i * n_n + j` is supplier `i` followed
//!   by nation `j` (`lemma_product_row`);
//! - the WHERE on such a row is `out_f` (`lemma_out_pred`) when no `LIKE` raises or partsupp is empty, so the body is
//!   `out_rows` (`lemma_body_rows`);
//! - when some `LIKE` raises and supplier, nation and partsupp are non-empty, the first outer row already raises
//!   22025 and the body is that error (`lemma_body_err`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::gendb_entry::stores::StoresView;
use crate::query::param_domain;
use crate::exec::relational::domain::*;
use crate::link::join::{keep, lemma_keep_true_keep, lemma_keep_members, lemma_product_index};
use crate::link::expr::{ival, lemma_pred_cmp, lemma_compare_int, lemma_pred_and, lemma_pred_text_cmp, text_cmp,
    lemma_text_cmp_holds, lemma_lex_cmp_zero};
use crate::link::capacity::{lemma_filter_err, lemma_first_input};
use crate::bridge::collect::lemma_collect_all;
use crate::stores::flat_supplier::interface as si;
use crate::stores::flat_nation::interface as ni;
use crate::agent::tables::*;
use crate::agent::ast::*;
use crate::agent::params::*;
use crate::agent::normal::*;
use crate::agent::den_li::*;
use crate::agent::den_ps::*;

verus! {

/// Row `k` of a product is `a[k / |b|] ++ b[k % |b|]`.
pub proof fn lemma_product_row(a: Seq<Row>, b: Seq<Row>, k: int)
    requires 0 <= k < product_rows(a, b).len(),
    ensures
        product_rows(a, b).len() == a.len() * b.len(),
        b.len() > 0,
        0 <= k / (b.len() as int) < a.len(),
        0 <= k % (b.len() as int) < b.len(),
        product_rows(a, b)[k] == a[k / (b.len() as int)] + b[k % (b.len() as int)],
{
    lemma_product_index(a, b);
    let nb = b.len() as int;
    if nb == 0 {
        assert(a.len() * b.len() == 0) by (nonlinear_arith) requires nb == 0, b.len() == nb;
    }
    let i = k / nb;
    let j = k % nb;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(k, nb);
    assert(0 <= j < nb);
    assert(0 <= i) by (nonlinear_arith) requires k >= 0, nb > 0, i == k / nb;
    assert(i < a.len()) by (nonlinear_arith) requires k < a.len() * nb, nb > 0, k == nb * i + j, 0 <= j;
    assert(k == i * nb + j) by (nonlinear_arith) requires k == nb * i + j;
}

/// Supplier row `i` followed by nation row `j`, as the evaluator sees it.
pub proof fn lemma_joined_row(sv: StoresView, i: int, j: int)
    requires stores_wf(sv), 0 <= i < n_s(sv), 0 <= j < n_n(sv),
    ensures ({
        let x = supp_rows(sv)[i] + nat_rows(sv)[j];
        &&& x.len() == 11
        &&& x[0] == Val::Int(sk(sv)[i] as int)
        &&& x[1] == Val::Text(sname(sv, i))
        &&& x[2] == Val::Text(saddr(sv, i))
        &&& x[3] == Val::Int(snk(sv)[i] as int)
        &&& x[7] == Val::Int(nk(sv)[j] as int)
        &&& x[8] == Val::Text(nname(sv, j))
    }),
{
    let (s, n) = (supp_rows(sv)[i], nat_rows(sv)[j]);
    assert(s == si::row_at(sv.flat_supplier, i));
    assert(n == ni::row_at(sv.flat_nation, j));
    let x = s + n;
    assert(x[7] == n[0] && x[8] == n[1]);
}

/// The outer WHERE on supplier row `i` followed by nation row `j` (when no `LIKE` raises or partsupp is empty).
pub proof fn lemma_out_pred(db: Database, sv: StoresView, ps: Seq<Literal>, lo: int, hi: int, i: int, j: int)
    requires
        tables_of(sv, db), model_ok(sv), sizes_ok(sv), param_domain(ps), win_ok(ps, lo, hi),
        likes_ok(sv, ps) || n_ps(sv) == 0, 0 <= i < n_s(sv), 0 <= j < n_n(sv),
    ensures ({
        let x = supp_rows(sv)[i] + nat_rows(sv)[j];
        eval_pred(db, x, out_pred(ps)) == Ok::<Truth, SqlError>(truth_of(out_f(sv, ps, lo, hi)(x)))
    }),
{
    hide(eval_query);
    let x = supp_rows(sv)[i] + nat_rows(sv)[j];
    lemma_joined_row(sv, i, j);
    lemma_param(ps);
    let v = sk(sv)[i] as int;
    lemma_in_supp_pred(db, sv, ps, lo, hi, x, v);
    let (s3, n7) = (snk(sv)[i] as int, nk(sv)[j] as int);
    assert(eval_expr(db, x, Expr::Col(3)) == Ok::<Val, SqlError>(Val::Int(s3)));
    assert(eval_expr(db, x, Expr::Col(7)) == Ok::<Val, SqlError>(Val::Int(n7)));
    lemma_compare_int(s3, n7);
    lemma_pred_cmp(db, x, CmpOp::Eq, Expr::Col(3), Expr::Col(7), Val::Int(s3), Val::Int(n7), s3, n7);
    let name = nname(sv, j);
    let want = nat_of(ps);
    assert(eval_expr(db, x, Expr::Col(8)) == Ok::<Val, SqlError>(Val::Text(name)));
    assert(eval_expr(db, x, Expr::Lit(ps[2])) == Ok::<Val, SqlError>(Val::Text(want)));
    lemma_pred_text_cmp(db, x, CmpOp::Eq, Expr::Col(8), Expr::Lit(ps[2]), name, want);
    lemma_text_cmp_holds(CmpOp::Eq, name, want);
    lemma_lex_cmp_zero(name, want);
    assert(text_cmp(CmpOp::Eq, name, want) == (name == want));
    lemma_pred_and(db, x, out_in_pred(ps), out_nat_pred(), in_supp(sv, ps, lo, hi, v), s3 == n7);
    lemma_pred_and(db, x, and(out_in_pred(ps), out_nat_pred()), out_name_pred(ps[2]), in_supp(sv, ps, lo, hi, v) && s3 == n7, name == want);
    assert(ival(x[0]) == v);
    assert((x[3] == x[7]) == (s3 == n7));
    assert((x[8] == Val::Text(want)) == (name == want));
}

/// `s_name, s_address` of a joined row.
proof fn lemma_out_exprs(db: Database, x: Row)
    requires x.len() == 11,
    ensures eval_exprs(db, x, out_exprs()) == Ok::<Row, SqlError>(out_proj(x)),
{
    let es = out_exprs();
    let er = expr_results(db, x, es);
    lemma_expr_results_index(db, x, es);
    assert(er[0] == Ok::<Val, SqlError>(x[1]));
    assert(er[1] == Ok::<Val, SqlError>(x[2]));
    lemma_collect_all(er, seq![x[1], x[2]]);
}

/// Every kept joined row has 11 values.
proof fn lemma_kept_lens(sv: StoresView, f: spec_fn(Row) -> bool)
    requires stores_wf(sv),
    ensures forall|t: int| 0 <= t < keep(product_rows(supp_rows(sv), nat_rows(sv)), f).len()
        ==> (#[trigger] keep(product_rows(supp_rows(sv), nat_rows(sv)), f)[t]).len() == 11,
{
    let rows = product_rows(supp_rows(sv), nat_rows(sv));
    let kept = keep(rows, f);
    lemma_keep_members(rows, f);
    assert forall|t: int| 0 <= t < kept.len() implies (#[trigger] kept[t]).len() == 11 by {
        assert(rows.contains(kept[t]));
        let k = choose|k: int| 0 <= k < rows.len() && rows[k] == kept[t];
        lemma_product_row(supp_rows(sv), nat_rows(sv), k);
        let nb = n_n(sv) as int;
        lemma_joined_row(sv, k / nb, k % nb);
    }
}

/// The outer WHERE when no `LIKE` raises, or partsupp, supplier or nation is empty: the rows of `out_f`.
proof fn lemma_out_filter(db: Database, sv: StoresView, ps: Seq<Literal>, lo: int, hi: int)
    requires
        tables_of(sv, db), model_ok(sv), sizes_ok(sv), param_domain(ps), win_ok(ps, lo, hi),
        likes_ok(sv, ps) || n_ps(sv) == 0 || n_s(sv) == 0 || n_n(sv) == 0,
    ensures eval_query(db, Seq::empty(), out_filter(ps))
        == Ok::<Relation, SqlError>(keep(product_rows(supp_rows(sv), nat_rows(sv)), out_f(sv, ps, lo, hi))),
{
    hide(eval_query);
    hide(eval_pred);
    let ctx = Seq::<Val>::empty();
    let rows = product_rows(supp_rows(sv), nat_rows(sv));
    let f = out_f(sv, ps, lo, hi);
    let pred = out_pred(ps);
    lemma_from(db, sv);
    lemma_eval_filter(db, ctx, pred, Box::new(out_from()));
    let prs = filter_results(db, ctx, rows, pred);
    let truths = Seq::new(rows.len(), |k: int| truth_of(f(rows[k])));
    assert forall|k: int| 0 <= k < prs.len() implies #[trigger] prs[k] == Ok::<Truth, SqlError>(truths[k]) by {
        lemma_product_row(supp_rows(sv), nat_rows(sv), k);
        let nb = n_n(sv) as int;
        let (i, j) = (k / nb, k % nb);
        assert(ctx + rows[k] =~= rows[k]);
        lemma_out_pred(db, sv, ps, lo, hi, i, j);
    }
    lemma_collect_all(prs, truths);
    lemma_keep_true_keep(rows, truths, f);
}

/// The body when no `LIKE` raises, or partsupp, supplier or nation is empty: `out_rows`.
pub proof fn lemma_body_rows(db: Database, sv: StoresView, ps: Seq<Literal>, lo: int, hi: int)
    requires
        tables_of(sv, db), model_ok(sv), sizes_ok(sv), param_domain(ps), win_ok(ps, lo, hi),
        likes_ok(sv, ps) || n_ps(sv) == 0 || n_s(sv) == 0 || n_n(sv) == 0,
    ensures eval_query(db, Seq::empty(), q_body(ps)) == Ok::<Relation, SqlError>(out_rows(sv, ps, lo, hi)),
{
    hide(eval_query);
    hide(eval_pred);
    hide(supp_rows);
    hide(nat_rows);
    hide(product_rows);
    hide(eval_exprs);
    let ctx = Seq::<Val>::empty();
    let rows = product_rows(supp_rows(sv), nat_rows(sv));
    let f = out_f(sv, ps, lo, hi);
    let kept = keep(rows, f);
    lemma_out_filter(db, sv, ps, lo, hi);
    // the projection `s_name, s_address`
    let es = out_exprs();
    lemma_eval_project(db, ctx, es, Box::new(out_filter(ps)));
    let pr = project_results(db, ctx, kept, es);
    let out = out_rows(sv, ps, lo, hi);
    lemma_kept_lens(sv, f);
    assert forall|t: int| 0 <= t < pr.len() implies #[trigger] pr[t] == Ok::<Row, SqlError>(out[t]) by {
        let x = kept[t];
        assert(ctx + x =~= x);
        lemma_out_exprs(db, x);
        assert(out[t] == out_proj(x));
    }
    lemma_collect_all(pr, out);
}

/// FROM is the product of the supplier and nation rows.
proof fn lemma_from(db: Database, sv: StoresView)
    requires tables_of(sv, db),
    ensures eval_query(db, Seq::empty(), out_from()) == Ok::<Relation, SqlError>(product_rows(supp_rows(sv), nat_rows(sv))),
{
    let ctx = Seq::<Val>::empty();
    assert(eval_query(db, ctx, Query::Table(5)) == Ok::<Relation, SqlError>(supp_rows(sv)));
    assert(eval_query(db, ctx, Query::Table(6)) == Ok::<Relation, SqlError>(nat_rows(sv)));
}

/// Some `LIKE` raises and supplier, nation and partsupp are non-empty: the body is the error 22025.
pub proof fn lemma_body_err(db: Database, sv: StoresView, ps: Seq<Literal>)
    requires
        tables_of(sv, db), stores_wf(sv), param_domain(ps),
        !likes_ok(sv, ps), n_ps(sv) > 0, n_s(sv) > 0, n_n(sv) > 0,
    ensures eval_query(db, Seq::empty(), q_body(ps)) == Err::<Relation, SqlError>(SqlError::InvalidEscapeSequence),
{
    hide(eval_query);
    let e = SqlError::InvalidEscapeSequence;
    let ctx = Seq::<Val>::empty();
    let rows = product_rows(supp_rows(sv), nat_rows(sv));
    let pred = out_pred(ps);
    lemma_from(db, sv);
    lemma_product_index(supp_rows(sv), nat_rows(sv));
    assert(rows.len() > 0) by (nonlinear_arith)
        requires rows.len() == n_s(sv) * n_n(sv), n_s(sv) > 0, n_n(sv) > 0;
    assert forall|k: int| 0 <= k < rows.len() implies #[trigger] eval_pred(db, ctx + rows[k], pred) == Err::<Truth, SqlError>(e) by {
        lemma_product_row(supp_rows(sv), nat_rows(sv), k);
        let nb = n_n(sv) as int;
        lemma_joined_row(sv, k / nb, k % nb);
        assert(ctx + rows[k] =~= rows[k]);
        lemma_in_supp_pred_err(db, sv, ps, rows[k]);
        assert(eval_pred(db, rows[k], and(out_in_pred(ps), out_nat_pred())) == Err::<Truth, SqlError>(e));
    }
    lemma_filter_err(db, ctx, pred, Box::new(out_from()), rows, e, 0);
    lemma_first_input(db, ctx, q_body(ps));
}

/// Without supplier, nation or partsupp rows the body has no rows.
pub proof fn lemma_out_rows_empty(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int)
    requires stores_wf(sv), n_ps(sv) == 0 || n_s(sv) == 0 || n_n(sv) == 0,
    ensures out_rows(sv, ps, lo, hi) == Seq::<Row>::empty(),
{
    let rows = product_rows(supp_rows(sv), nat_rows(sv));
    let f = out_f(sv, ps, lo, hi);
    lemma_product_index(supp_rows(sv), nat_rows(sv));
    if n_s(sv) == 0 || n_n(sv) == 0 {
        assert(rows.len() == 0) by (nonlinear_arith)
            requires rows.len() == n_s(sv) * n_n(sv), n_s(sv) == 0 || n_n(sv) == 0;
        crate::link::join::lemma_keep_none(rows, f);
    } else {
        assert forall|k: int| 0 <= k < rows.len() implies !f(#[trigger] rows[k]) by {
            let x = rows[k];
            if in_supp(sv, ps, lo, hi, ival(x[0])) {
                let q = choose|q: int| 0 <= q < n_ps(sv) && #[trigger] ps_ok(sv, ps, lo, hi, q) && pssk(sv)[q] as int == ival(x[0]);
                assert(false);
            }
        }
        crate::link::join::lemma_keep_none(rows, f);
    }
    assert(Seq::<Row>::empty().map_values(|x: Row| out_proj(x)) =~= Seq::<Row>::empty());
}

} // verus!
