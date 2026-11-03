//! The statement's body `SELECT o_year, sum0 / sum1 FROM <groups>` and its allowed outputs, stated with the scan's
//! per-year totals `tot_y(y)` (`line::tot` over all lineitem rows) for the two possible years.
//!
//! The groups are the years with a qualifying row (`present`), each group's row is `[year, sum0, sum1]`, and the
//! output row divides the sums (`div_of`, PostgreSQL's numeric division with its value-dependent scale). The
//! outcomes, over every bound database:
//! - every group's volume mass fits and every division succeeds: the rows, ordered by year (`lemma_body_rows`);
//! - some group's volume mass leaves `i128`: outside the capacity domain (`lemma_body_group_cap`);
//! - every failing division fails with one SQL error `e`: that error (`lemma_body_err`);
//! - some division leaves its executable domain and every division inside it succeeds: outside the capacity
//!   domain (`lemma_body_cap`);
//! - otherwise the first group in the GROUP BY's order decides (`lemma_body_first`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::order::*;
use crate::spec::fns::*;
use crate::spec::fns::div::*;
use crate::exec::domain::*;
use crate::exec::relational::domain::*;
use crate::query::{param_domain, query_spec_at};
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::capacity_domain;
use crate::link::query::{lemma_nodup_same_multiset, lemma_map_multiset};
use crate::link::expr::i128_max;
use crate::link::capacity::{lemma_fits_each_violation, lemma_collect_uniform_err};
use crate::bridge::collect::lemma_collect_all;
use crate::agent::tables::*;
use crate::agent::line::*;
use crate::agent::ast::*;
use crate::agent::pred::*;
use crate::agent::bag::*;
use crate::agent::group::*;
use crate::agent::groupby::*;

verus! {

// ------------------------------------------------------------------------------------------------ one output row

/// `sum0 / sum1` of a group with totals `t`.
pub open spec fn div_of(t: Tot) -> Result<Val, SqlError> { num_div(t.s_then, s0_of(t), t.s_all, 4) }

/// The division is inside its executable domain.
pub open spec fn div_fits_of(t: Tot) -> bool { num_div_fits(t.s_then, s0_of(t), t.s_all, 4) }

/// The division call `Col(1) / Col(2)`.
pub open spec fn div_call() -> Expr {
    Expr::Call { f: ScalarFn::DivNumeric, args: seq![Expr::Col(1), Expr::Col(2)] }
}

/// A two-element list of columns.
proof fn lemma_cols2(db: Database, g: Row)
    requires g.len() == 3,
    ensures eval_exprs(db, g, seq![Expr::Col(1), Expr::Col(2)]) == Ok::<Row, SqlError>(seq![g[1], g[2]]),
{
    let es = seq![Expr::Col(1), Expr::Col(2)];
    lemma_eval_col(db, g, 1);
    lemma_eval_col(db, g, 2);
    let rs = expr_results(db, g, es);
    lemma_expr_results_index(db, g, es);
    let vs = seq![g[1], g[2]];
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Val, SqlError>(vs[i]) by {
        if i == 0 {} else { assert(i == 1); }
    }
    lemma_collect_all(rs, vs);
}

/// One evaluation step of a call over evaluated arguments.
proof fn lemma_eval_call(db: Database, g: Row, f: ScalarFn, args: Seq<Expr>, vs: Seq<Val>)
    requires eval_exprs(db, g, args) == Ok::<Row, SqlError>(vs),
    ensures eval_expr(db, g, Expr::Call { f, args }) == apply_fn(f, vs),
{
}

/// One domain step of a call over evaluated arguments.
proof fn lemma_fits_call(db: Database, g: Row, f: ScalarFn, args: Seq<Expr>, vs: Seq<Val>)
    requires eval_exprs(db, g, args) == Ok::<Row, SqlError>(vs), fits_exprs(db, g, args),
    ensures fits_expr(db, g, Expr::Call { f, args }) == fits_fn(f, vs),
{
}

/// A column is inside the domain.
proof fn lemma_fits_col(db: Database, g: Row, k: nat)
    ensures fits_expr(db, g, Expr::Col(k)),
{
}

/// Columns are always inside the domain.
proof fn lemma_fits_cols2(db: Database, g: Row)
    ensures fits_exprs(db, g, seq![Expr::Col(1), Expr::Col(2)]),
{
    hide(eval_exprs);
    let es = seq![Expr::Col(1), Expr::Col(2)];
    lemma_fits_exprs_unfold(db, g, es);
    lemma_fits_exprs_unfold(db, g, es.drop_last());
    assert(es.drop_last().drop_last() =~= Seq::<Expr>::empty());
    assert(es.drop_last().last() == Expr::Col(1));
    assert(es.last() == Expr::Col(2));
    lemma_fits_col(db, g, 1);
    lemma_fits_col(db, g, 2);
}

/// The division on a group row.
proof fn lemma_div_call(db: Database, g: Row, c0: int, s0: nat, c1: int, s1: nat)
    requires g.len() == 3, g[1] == (Val::Num { coeff: c0, scale: s0 }), g[2] == (Val::Num { coeff: c1, scale: s1 }),
    ensures
        eval_expr(db, g, div_call()) == num_div(c0, s0, c1, s1),
        fits_expr(db, g, div_call()) == num_div_fits(c0, s0, c1, s1),
{
    hide(eval_expr);
    hide(fits_expr);
    let args = seq![Expr::Col(1), Expr::Col(2)];
    let vs = seq![g[1], g[2]];
    lemma_cols2(db, g);
    lemma_fits_cols2(db, g);
    lemma_eval_call(db, g, ScalarFn::DivNumeric, args, vs);
    lemma_fits_call(db, g, ScalarFn::DivNumeric, args, vs);
    assert(apply_fn(ScalarFn::DivNumeric, vs) == num_div(c0, s0, c1, s1));
    assert(fits_fn(ScalarFn::DivNumeric, vs) == num_div_fits(c0, s0, c1, s1));
}

/// The output expressions on a group row: the year and the quotient, or the quotient's error.
proof fn lemma_outer_value(db: Database, g: Row, c0: int, s0: nat, c1: int, s1: nat)
    requires g.len() == 3, g[1] == (Val::Num { coeff: c0, scale: s0 }), g[2] == (Val::Num { coeff: c1, scale: s1 }),
    ensures
        eval_exprs(db, g, outer_exprs()) == match num_div(c0, s0, c1, s1) {
            Ok(v) => Ok::<Row, SqlError>(seq![g[0], v]),
            Err(e) => Err(e),
        },
{
    hide(eval_expr);
    hide(fits_expr);
    let es = outer_exprs();
    let first = seq![Expr::Col(0)];
    assert(es.drop_last() =~= first);
    assert(es.last() == div_call());
    lemma_eval_col(db, g, 0);
    lemma_expr_list1(db, g, Expr::Col(0), g[0]);
    lemma_div_call(db, g, c0, s0, c1, s1);
    lemma_eval_exprs_step(db, g, es);
    if let Ok(v) = num_div(c0, s0, c1, s1) {
        assert(seq![g[0]].push(v) =~= seq![g[0], v]);
    }
}

/// The domain of the output expressions on a group row is the division's.
proof fn lemma_outer_fits(db: Database, g: Row, c0: int, s0: nat, c1: int, s1: nat)
    requires g.len() == 3, g[1] == (Val::Num { coeff: c0, scale: s0 }), g[2] == (Val::Num { coeff: c1, scale: s1 }),
    ensures fits_exprs(db, g, outer_exprs()) == num_div_fits(c0, s0, c1, s1),
{
    hide(eval_expr);
    hide(fits_expr);
    hide(eval_exprs);
    let es = outer_exprs();
    let first = seq![Expr::Col(0)];
    assert(es.drop_last() =~= first);
    assert(es.last() == div_call());
    assert(first.drop_last() =~= Seq::<Expr>::empty());
    assert(first.last() == Expr::Col(0));
    lemma_eval_col(db, g, 0);
    lemma_expr_list1(db, g, Expr::Col(0), g[0]);
    lemma_eval_exprs_empty(db, g);
    lemma_div_call(db, g, c0, s0, c1, s1);
    lemma_fits_col(db, g, 0);
    lemma_fits_exprs_unfold(db, g, es);
    lemma_fits_exprs_unfold(db, g, first);
    assert(fits_exprs(db, g, Seq::<Expr>::empty()));
}

/// The output expressions on a group row, and their domain.
pub proof fn lemma_outer_eval(db: Database, g: Row, c0: int, s0: nat, c1: int, s1: nat)
    requires g.len() == 3, g[1] == (Val::Num { coeff: c0, scale: s0 }), g[2] == (Val::Num { coeff: c1, scale: s1 }),
    ensures
        eval_exprs(db, g, outer_exprs()) == match num_div(c0, s0, c1, s1) {
            Ok(v) => Ok::<Row, SqlError>(seq![g[0], v]),
            Err(e) => Err(e),
        },
        fits_exprs(db, g, outer_exprs()) == num_div_fits(c0, s0, c1, s1),
{
    lemma_outer_value(db, g, c0, s0, c1, s1);
    lemma_outer_fits(db, g, c0, s0, c1, s1);
}

// ------------------------------------------------------------------------------------------------ the groups

/// The scan's totals of year `y` over all lineitem rows.
pub open spec fn tot_y(sv: StoresView, ps: Seq<Literal>, y: int) -> Tot { tot(sv, ps, y, 0, n_l(sv) as int) }

/// Year `y` has a group.
pub open spec fn present(sv: StoresView, ps: Seq<Literal>, y: int) -> bool { tot_y(sv, ps, y).cnt > 0 }

/// Both years' volume masses fit `i128`.
pub open spec fn masses_fit(sv: StoresView, ps: Seq<Literal>) -> bool {
    tot_y(sv, ps, 1995).a_all <= i128_max() && tot_y(sv, ps, 1996).a_all <= i128_max()
}

/// The group keys are year keys of the two years, each with the scan's totals.
pub proof fn lemma_group_keys(sv: StoresView, ps: Seq<Literal>, i: int)
    requires model_ok(sv), 0 <= i < dkeys(zrows(sv, ps)).len(),
    ensures ({
        let k = dkeys(zrows(sv, ps))[i];
        let y = k[0]->Num_coeff;
        &&& (y == 1995 || y == 1996)
        &&& k == ykey(y)
        &&& gsums(ps, zrows(sv, ps), k) == tot_y(sv, ps, y)
        &&& present(sv, ps, y)
    }),
{
    let zs = zrows(sv, ps);
    lemma_zrows_shape(sv, ps);
    lemma_dkeys(zs);
    let k = dkeys(zs)[i];
    assert(zks(zs).contains(k));
    lemma_key_shape(zs, k);
    lemma_group_sums(sv, ps, k[0]->Num_coeff);
    lemma_dkey_count(ps, zs, i);
}

/// A present year has a group.
pub proof fn lemma_present_key(sv: StoresView, ps: Seq<Literal>, y: int)
    requires model_ok(sv), present(sv, ps, y),
    ensures dkeys(zrows(sv, ps)).contains(ykey(y)),
{
    let zs = zrows(sv, ps);
    lemma_zrows_shape(sv, ps);
    lemma_dkeys(zs);
    lemma_group_sums(sv, ps, y);
    lemma_gcount(ps, zs, ykey(y));
}

/// Inside the masses, the groups fit.
proof fn lemma_groups_fit(sv: StoresView, ps: Seq<Literal>)
    requires model_ok(sv), masses_fit(sv, ps),
    ensures groups_fit(ps, zrows(sv, ps)),
{
    let zs = zrows(sv, ps);
    assert forall|i: int| 0 <= i < dkeys(zs).len() implies #[trigger] gsums(ps, zs, dkeys(zs)[i]).a_all <= i128_max() by {
        lemma_group_keys(sv, ps, i);
    }
}

/// The group row of group `i`.
proof fn lemma_grow(sv: StoresView, ps: Seq<Literal>, i: int)
    requires model_ok(sv), 0 <= i < dkeys(zrows(sv, ps)).len(),
    ensures ({
        let zs = zrows(sv, ps);
        let k = dkeys(zs)[i];
        let y = k[0]->Num_coeff;
        let t = tot_y(sv, ps, y);
        let g = grow(ps, zs, k);
        &&& g.len() == 3
        &&& g[0] == Val::Num { coeff: y, scale: 0 }
        &&& g[1] == Val::Num { coeff: t.s_then, scale: s0_of(t) }
        &&& g[2] == Val::Num { coeff: t.s_all, scale: 4 }
    }),
{
    lemma_group_keys(sv, ps, i);
}

/// The outcome of the output row of group `i`, and its domain.
proof fn lemma_group_out(db: Database, sv: StoresView, ps: Seq<Literal>, i: int)
    requires model_ok(sv), 0 <= i < dkeys(zrows(sv, ps)).len(),
    ensures ({
        let zs = zrows(sv, ps);
        let k = dkeys(zs)[i];
        let y = k[0]->Num_coeff;
        let t = tot_y(sv, ps, y);
        let g = grow(ps, zs, k);
        &&& eval_exprs(db, g, outer_exprs()) == match div_of(t) {
                Ok(v) => Ok::<Row, SqlError>(seq![Val::Num { coeff: y, scale: 0 }, v]),
                Err(e) => Err(e),
            }
        &&& fits_exprs(db, g, outer_exprs()) == div_fits_of(t)
    }),
{
    lemma_grow(sv, ps, i);
    let zs = zrows(sv, ps);
    let k = dkeys(zs)[i];
    let t = tot_y(sv, ps, k[0]->Num_coeff);
    lemma_outer_eval(db, grow(ps, zs, k), t.s_then, s0_of(t), t.s_all, 4);
}

/// The group rows inside the masses.
pub open spec fn grows_of(sv: StoresView, ps: Seq<Literal>) -> Seq<Row> {
    dkeys(zrows(sv, ps)).map_values(|k: Row| grow(ps, zrows(sv, ps), k))
}

/// The body over the group rows: the output row of every group, first error in group order.
proof fn lemma_body_eval(db: Database, sv: StoresView, ps: Seq<Literal>)
    requires tables_of(sv, db), param_domain(ps), model_ok(sv), masses_fit(sv, ps),
    ensures
        eval_query(db, Seq::empty(), q8_group(ps)) == Ok::<Relation, SqlError>(grows_of(sv, ps)),
        eval_query(db, Seq::empty(), q8_body(ps)) == collect(project_results(db, Seq::empty(), grows_of(sv, ps), outer_exprs())),
        fits_query(db, Seq::empty(), q8_body(ps)) == (fits_query(db, Seq::empty(), q8_group(ps))
            && fits_each(project_results(db, Seq::empty(), grows_of(sv, ps), outer_exprs()),
                project_fs(db, Seq::empty(), grows_of(sv, ps), outer_exprs()))),
{
    lemma_groups_fit(sv, ps);
    lemma_group_rows(db, sv, ps);
    lemma_eval_project(db, Seq::empty(), outer_exprs(), Box::new(q8_group(ps)));
}

/// The per-group outcome and domain sequences of the body.
proof fn lemma_body_seqs(db: Database, sv: StoresView, ps: Seq<Literal>)
    requires model_ok(sv),
    ensures ({
        let gs = grows_of(sv, ps);
        let rs = project_results(db, Seq::empty(), gs, outer_exprs());
        let fs = project_fs(db, Seq::empty(), gs, outer_exprs());
        let zs = zrows(sv, ps);
        &&& rs.len() == dkeys(zs).len() && fs.len() == dkeys(zs).len()
        &&& forall|i: int| 0 <= i < rs.len() ==> #[trigger] rs[i] == match div_of(tot_y(sv, ps, dkeys(zs)[i][0]->Num_coeff)) {
                Ok(v) => Ok::<Row, SqlError>(seq![Val::Num { coeff: dkeys(zs)[i][0]->Num_coeff, scale: 0 }, v]),
                Err(e) => Err(e),
            }
        &&& forall|i: int| 0 <= i < fs.len() ==> #[trigger] fs[i] == div_fits_of(tot_y(sv, ps, dkeys(zs)[i][0]->Num_coeff))
    }),
{
    let gs = grows_of(sv, ps);
    let ctx = Seq::<Val>::empty();
    let rs = project_results(db, ctx, gs, outer_exprs());
    let fs = project_fs(db, ctx, gs, outer_exprs());
    lemma_project_fs_index(db, ctx, gs, outer_exprs());
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == match div_of(tot_y(sv, ps, dkeys(zrows(sv, ps))[i][0]->Num_coeff)) {
            Ok(v) => Ok::<Row, SqlError>(seq![Val::Num { coeff: dkeys(zrows(sv, ps))[i][0]->Num_coeff, scale: 0 }, v]),
            Err(e) => Err(e),
        } by {
        assert(ctx + gs[i] =~= gs[i]);
        lemma_group_out(db, sv, ps, i);
    }
    assert forall|i: int| 0 <= i < fs.len() implies #[trigger] fs[i] == div_fits_of(tot_y(sv, ps, dkeys(zrows(sv, ps))[i][0]->Num_coeff)) by {
        assert(ctx + gs[i] =~= gs[i]);
        lemma_group_out(db, sv, ps, i);
    }
}

// ------------------------------------------------------------------------------------------------ outcomes

/// The output row of year `y` with quotient `v`.
pub open spec fn out_row(y: int, v: Val) -> Row { seq![Val::Num { coeff: y, scale: 0 }, v] }

/// The output: the present years' rows, 1995 first.
pub open spec fn out_rows(b95: bool, v95: Val, b96: bool, v96: Val) -> Seq<Row> {
    (if b95 { seq![out_row(1995, v95)] } else { Seq::empty() }) + (if b96 { seq![out_row(1996, v96)] } else { Seq::empty() })
}

/// The present years' keys, 1995 first.
pub open spec fn out_keys(b95: bool, b96: bool) -> Seq<Row> {
    (if b95 { seq![ykey(1995)] } else { Seq::empty() }) + (if b96 { seq![ykey(1996)] } else { Seq::empty() })
}

/// The output row of a group key with the two quotients.
pub open spec fn vof(v95: Val, v96: Val, k: Row) -> Row {
    if k == ykey(1995) { out_row(1995, v95) } else { out_row(1996, v96) }
}

/// Every division succeeds: the body is the output row of every group, in group order.
proof fn lemma_body_value(db: Database, sv: StoresView, ps: Seq<Literal>, v95: Val, v96: Val)
    requires
        tables_of(sv, db), param_domain(ps), model_ok(sv), masses_fit(sv, ps),
        present(sv, ps, 1995) ==> div_of(tot_y(sv, ps, 1995)) == Ok::<Val, SqlError>(v95),
        present(sv, ps, 1996) ==> div_of(tot_y(sv, ps, 1996)) == Ok::<Val, SqlError>(v96),
    ensures
        eval_query(db, Seq::empty(), q8_body(ps))
            == Ok::<Relation, SqlError>(dkeys(zrows(sv, ps)).map_values(|k: Row| vof(v95, v96, k))),
{
    let zs = zrows(sv, ps);
    let dk = dkeys(zs);
    lemma_body_eval(db, sv, ps);
    lemma_body_seqs(db, sv, ps);
    let gs = grows_of(sv, ps);
    let rs = project_results(db, Seq::empty(), gs, outer_exprs());
    let rows = dk.map_values(|k: Row| vof(v95, v96, k));
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(rows[i]) by {
        lemma_group_keys(sv, ps, i);
        assert(ykey(1995) != ykey(1996)) by { assert(ykey(1995)[0] != ykey(1996)[0]); }
    }
    lemma_collect_all(rs, rows);
}

/// The groups are the present years' keys, as a bag.
proof fn lemma_dkeys_bag(sv: StoresView, ps: Seq<Literal>)
    requires model_ok(sv),
    ensures dkeys(zrows(sv, ps)).to_multiset() == out_keys(present(sv, ps, 1995), present(sv, ps, 1996)).to_multiset(),
{
    let zs = zrows(sv, ps);
    let dk = dkeys(zs);
    let ks = out_keys(present(sv, ps, 1995), present(sv, ps, 1996));
    lemma_zrows_shape(sv, ps);
    lemma_dkeys(zs);
    assert(ykey(1995) != ykey(1996)) by { assert(ykey(1995)[0] != ykey(1996)[0]); }
    assert(ks.no_duplicates());
    assert forall|k: Row| dk.contains(k) <==> ks.contains(k) by {
        if dk.contains(k) {
            let i = choose|i: int| 0 <= i < dk.len() && dk[i] == k;
            lemma_group_keys(sv, ps, i);
            if k == ykey(1995) { assert(ks[0] == k); } else { assert(ks[ks.len() - 1] == k); }
        }
        if ks.contains(k) {
            if k == ykey(1995) { lemma_present_key(sv, ps, 1995); } else { lemma_present_key(sv, ps, 1996); }
        }
    }
    lemma_nodup_same_multiset(dk, ks);
}

/// The output rows are sorted by year.
proof fn lemma_out_sorted(b95: bool, v95: Val, b96: bool, v96: Val)
    ensures sorted_by(q8_order(), out_rows(b95, v95, b96, v96)),
{
    let p = out_rows(b95, v95, b96, v96);
    assert forall|i: int, j: int| 0 <= i < j < p.len() implies keys_cmp(q8_order(), #[trigger] p[i], #[trigger] p[j]) <= 0 by {
        assert(b95 && b96 && i == 0 && j == 1);
        assert(p[0] == out_row(1995, v95) && p[1] == out_row(1996, v96));
        assert(p[0][0] == Val::Num { coeff: 1995, scale: 0 } && p[1][0] == Val::Num { coeff: 1996, scale: 0 });
        crate::link::expr::lemma_compare_num(1995, 0, 1996, 0);
        assert(pow10(0) == 1);
        assert(compare(p[0][0], p[1][0]) == Some(-1int));
        assert(key_cmp(q8_order()[0], p[0], p[1]) == -1);
    }
}

/// Every division succeeds: the present years' rows in year order are an allowed output.
pub proof fn lemma_body_rows(db: Database, sv: StoresView, ps: Seq<Literal>, v95: Val, v96: Val)
    requires
        tables_of(sv, db), param_domain(ps), model_ok(sv), masses_fit(sv, ps),
        present(sv, ps, 1995) ==> div_of(tot_y(sv, ps, 1995)) == Ok::<Val, SqlError>(v95),
        present(sv, ps, 1996) ==> div_of(tot_y(sv, ps, 1996)) == Ok::<Val, SqlError>(v96),
    ensures
        ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out_rows(present(sv, ps, 1995), v95, present(sv, ps, 1996), v96))),
{
    let (b95, b96) = (present(sv, ps, 1995), present(sv, ps, 1996));
    let f = |k: Row| vof(v95, v96, k);
    lemma_query_shape(ps);
    lemma_body_value(db, sv, ps, v95, v96);
    lemma_dkeys_bag(sv, ps);
    let dk = dkeys(zrows(sv, ps));
    let ks = out_keys(b95, b96);
    lemma_map_multiset(dk, ks, f);
    let p = out_rows(b95, v95, b96, v96);
    assert(ks.map_values(f) =~= p) by {
        assert(ykey(1995) != ykey(1996)) by { assert(ykey(1995)[0] != ykey(1996)[0]); }
    }
    lemma_out_sorted(b95, v95, b96, v96);
    assert(slice_rows(p, 0, None) =~= p);
    let oq = query_spec_at(ps);
    let rows = dk.map_values(f);
    assert(denote_body(db, oq) == Ok::<Relation, SqlError>(rows));
    assert(oq.keys == q8_order() && oq.offset == 0 && oq.limit == None::<nat>);
    assert(p.to_multiset() == rows.to_multiset());
    assert(sorted_by(oq.keys, p));
    assert(Ok::<Relation, SqlError>(p) == Ok::<Relation, SqlError>(slice_rows(p, oq.offset, oq.limit)));
}

/// Some year's volume mass leaves `i128`: outside the capacity domain.
pub proof fn lemma_body_group_cap(db: Database, sv: StoresView, ps: Seq<Literal>, y: int)
    requires
        tables_of(sv, db), param_domain(ps), model_ok(sv),
        tot_y(sv, ps, y).a_all > i128_max(),
    ensures !capacity_domain(db, query_spec_at(ps)),
{
    lemma_query_shape(ps);
    lemma_tot_bounds(sv, ps, y, 0, n_l(sv) as int);
    lemma_present_key(sv, ps, y);
    let zs = zrows(sv, ps);
    let g = choose|g: int| 0 <= g < dkeys(zs).len() && dkeys(zs)[g] == ykey(y);
    lemma_group_keys(sv, ps, g);
    lemma_group_capacity(db, sv, ps, g);
}

/// Every failing division fails with `e` (and some does): the body's error is `e`.
pub proof fn lemma_body_err(db: Database, sv: StoresView, ps: Seq<Literal>, y: int, e: SqlError)
    requires
        tables_of(sv, db), param_domain(ps), model_ok(sv), masses_fit(sv, ps),
        present(sv, ps, y), div_of(tot_y(sv, ps, y)) == Err::<Val, SqlError>(e),
        present(sv, ps, 1995) ==> div_of(tot_y(sv, ps, 1995)) is Ok || div_of(tot_y(sv, ps, 1995)) == Err::<Val, SqlError>(e),
        present(sv, ps, 1996) ==> div_of(tot_y(sv, ps, 1996)) is Ok || div_of(tot_y(sv, ps, 1996)) == Err::<Val, SqlError>(e),
    ensures ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(e)),
{
    lemma_query_shape(ps);
    lemma_body_eval(db, sv, ps);
    lemma_body_seqs(db, sv, ps);
    let zs = zrows(sv, ps);
    let gs = grows_of(sv, ps);
    let rs = project_results(db, Seq::empty(), gs, outer_exprs());
    lemma_present_key(sv, ps, y);
    let g = choose|g: int| 0 <= g < dkeys(zs).len() && dkeys(zs)[g] == ykey(y);
    lemma_group_keys(sv, ps, g);
    assert forall|k: int| 0 <= k < rs.len() implies #[trigger] rs[k] is Ok || rs[k] == Err::<Row, SqlError>(e) by {
        lemma_group_keys(sv, ps, k);
    }
    lemma_collect_uniform_err(rs, e, g);
}

/// Some division leaves its executable domain and every division inside its domain succeeds: outside the
/// capacity domain.
pub proof fn lemma_body_cap(db: Database, sv: StoresView, ps: Seq<Literal>, y: int)
    requires
        tables_of(sv, db), param_domain(ps), model_ok(sv), masses_fit(sv, ps),
        present(sv, ps, y), !div_fits_of(tot_y(sv, ps, y)),
        present(sv, ps, 1995) && div_fits_of(tot_y(sv, ps, 1995)) ==> div_of(tot_y(sv, ps, 1995)) is Ok,
        present(sv, ps, 1996) && div_fits_of(tot_y(sv, ps, 1996)) ==> div_of(tot_y(sv, ps, 1996)) is Ok,
    ensures !capacity_domain(db, query_spec_at(ps)),
{
    lemma_query_shape(ps);
    lemma_body_eval(db, sv, ps);
    lemma_body_seqs(db, sv, ps);
    let zs = zrows(sv, ps);
    let gs = grows_of(sv, ps);
    let rs = project_results(db, Seq::empty(), gs, outer_exprs());
    let fs = project_fs(db, Seq::empty(), gs, outer_exprs());
    lemma_present_key(sv, ps, y);
    let g = choose|g: int| 0 <= g < dkeys(zs).len() && dkeys(zs)[g] == ykey(y);
    lemma_group_keys(sv, ps, g);
    assert forall|k: int| 0 <= k < fs.len() && #[trigger] fs[k] implies rs[k] is Ok by {
        lemma_group_keys(sv, ps, k);
    }
    lemma_fits_each_violation(rs, fs, g);
}

/// The first group in the GROUP BY's order decides: its division's error (inside its domain) is the body's
/// error, and its leaving the domain puts the body outside the capacity domain.
pub proof fn lemma_body_first(db: Database, sv: StoresView, ps: Seq<Literal>, y: int)
    requires
        tables_of(sv, db), param_domain(ps), model_ok(sv), masses_fit(sv, ps),
        dkeys(zrows(sv, ps)).len() > 0, dkeys(zrows(sv, ps))[0] == ykey(y),
    ensures
        div_fits_of(tot_y(sv, ps, y)) && div_of(tot_y(sv, ps, y)) is Err
            ==> ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(div_of(tot_y(sv, ps, y))->Err_0)),
        !div_fits_of(tot_y(sv, ps, y)) ==> !capacity_domain(db, query_spec_at(ps)),
{
    lemma_query_shape(ps);
    lemma_body_eval(db, sv, ps);
    lemma_body_seqs(db, sv, ps);
    let gs = grows_of(sv, ps);
    let rs = project_results(db, Seq::empty(), gs, outer_exprs());
    let fs = project_fs(db, Seq::empty(), gs, outer_exprs());
    lemma_group_keys(sv, ps, 0);
    assert(ykey(y)[0]->Num_coeff == y);
    if div_fits_of(tot_y(sv, ps, y)) && div_of(tot_y(sv, ps, y)) is Err {
        lemma_each_err(rs, fs, 0);
    }
    if !div_fits_of(tot_y(sv, ps, y)) {
        lemma_each_capacity(rs, fs, 0);
    }
}

} // verus!
