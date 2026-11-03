//! The statement body on a database of the schema: the rows of `supplier x revenue0` whose supplier key is the
//! group key and whose SUM is the MAX of all group sums, projected on `s_suppkey, s_name, s_address, s_phone,
//! total_revenue`, in supplier order (`lemma_body`: `body_rows`). The group keys are distinct, so each supplier
//! row meets at most one group (`lemma_keep_unique`).
//!
//! The other outcomes: `$1 + 3 months` outside the timestamp range is the statement's error when lineitem has a
//! row (`lemma_body_err`) and gives no row otherwise (`lemma_body_empty`); a group whose SUM has absolute mass
//! above `i128::MAX` puts the statement outside its capacity domain (`lemma_body_capacity`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::types::*;
use crate::spec::typing::*;
use crate::spec::equality::distinct_rows;
use crate::spec::aggs::minmax::extremum;
use crate::exec::relational::domain::*;
use crate::query::{param_typed, query_spec_at};
use crate::schema::schema_spec;
use crate::link::query::*;
use crate::link::join::{keep, lemma_keep_append, lemma_keep_map, lemma_keep_ext, lemma_keep_members,
    lemma_product_index, lemma_eval_product, lemma_eval_table};
use crate::link::join::lemma_keep_all as lemma_keep_every;
use crate::link::join::lemma_eval_filter as lemma_eval_where;
use crate::link::expr::{ival, i128_max, lemma_pred_cmp, lemma_pred_and, lemma_compare_num, lemma_align_same, lemma_expr_col};
use crate::link::capacity::{lemma_group_by_capacity, aggs_ok_inside, lemma_sum_inside_ok, lemma_num_mass_uniform,
    lemma_first_input, lemma_second_input, lemma_filter_err};
use crate::bridge::collect::{lemma_collect_all, lemma_collect_pointwise};
use crate::gendb_entry::capacity_domain;
use super::window::*;
use super::sql::*;
use super::group::*;

verus! {

// ------------------------------------------------------------------------------------------------ supplier rows

/// A supplier row of the schema: seven columns, a bigint key.
pub open spec fn supp_typed(s: Row) -> bool {
    &&& s.len() == 7
    &&& s[0] == Val::Int(ival(s[0]))
    &&& crate::spec::limits::int8_min() <= ival(s[0]) <= crate::spec::limits::int8_max()
}

/// The supplier rows of a database of the schema are typed.
pub proof fn lemma_supp_typed(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures
        db.tables.len() == 8,
        forall|i: int| 0 <= i < db.tables[5].len() ==> supp_typed(#[trigger] db.tables[5][i]),
{
    crate::stores::suppliers::declaration::lemma_declared_schema();
    assert(schema_spec()[5].columns.len() == 7) by (compute);
    assert(schema_spec()[5].columns[0] == Column { ty: SqlType::Int8, nullable: false }) by (compute);
    assert forall|i: int| 0 <= i < db.tables[5].len() implies supp_typed(#[trigger] db.tables[5][i]) by {
        let s = db.tables[5][i];
        assert(row_in_table(s, db.schema[5]));
        assert(value_in_column(s[0], Column { ty: SqlType::Int8, nullable: false }));
    }
}

// ------------------------------------------------------------------------------------------------ the result rows

/// The output row of supplier row `s` with revenue `mv`.
pub open spec fn res_row(s: Row, mv: Val) -> Row {
    seq![s[0], s[1], s[2], s[4], mv]
}

/// Supplier row `s` meets a group whose SUM is `mv`.
pub open spec fn hitk(g: QuerySpec, xs: Seq<Row>, mv: Val, s: Row) -> bool {
    &&& gcount(g, xs, seq![s[0]]) > 0
    &&& (Val::Num { coeff: gsum(g, xs, seq![s[0]], 0), scale: 4 }) == mv
}

/// The body's rows: per supplier row, in order, its output row when it meets a group of SUM `mv`.
pub open spec fn body_rows(ss: Seq<Row>, g: QuerySpec, xs: Seq<Row>, mv: Val) -> Seq<Row>
    decreases ss.len(),
{
    if ss.len() == 0 {
        Seq::empty()
    } else {
        body_rows(ss.drop_last(), g, xs, mv) + if hitk(g, xs, mv, ss.last()) { seq![res_row(ss.last(), mv)] } else { Seq::<Row>::empty() }
    }
}

/// The MAX of the group sums (NULL without a group).
pub open spec fn max_val(g: QuerySpec, xs: Seq<Row>) -> Val {
    extremum(true, gvals(g, xs))->Ok_0
}

// ------------------------------------------------------------------------------------------------ keep of one key

/// The condition of the outer WHERE on a product row: equal keys and the SUM equal to `mv`.
pub open spec fn outer_h(mv: Val) -> spec_fn(Row) -> bool {
    |y: Row| y[0] == y[7] && y[8] == mv
}

/// The condition on a GROUP BY row `r` for supplier key `a`.
pub open spec fn grp_h(a: Val, mv: Val) -> spec_fn(Row) -> bool {
    |r: Row| r[0] == a && r[1] == mv
}

/// Two-column rows with distinct first columns: at most one row has first column `a`, so the rows with first
/// column `a` and second `mv` are `[[a, mv]]` when there is one, else none.
pub proof fn lemma_keep_unique(rs: Seq<Row>, a: Val, mv: Val)
    requires
        forall|i: int| 0 <= i < rs.len() ==> (#[trigger] rs[i]).len() == 2,
        forall|i: int, j: int| 0 <= i < j < rs.len() ==> (#[trigger] rs[i])[0] != (#[trigger] rs[j])[0],
    ensures
        keep(rs, grp_h(a, mv)) == if exists|i: int| 0 <= i < rs.len() && #[trigger] rs[i][0] == a && rs[i][1] == mv {
            seq![seq![a, mv]]
        } else {
            Seq::<Row>::empty()
        },
    decreases rs.len(),
{
    let h = grp_h(a, mv);
    if rs.len() > 0 {
        let ri = rs.drop_last();
        let x = rs.last();
        assert forall|i: int| 0 <= i < ri.len() implies (#[trigger] ri[i]).len() == 2 by { assert(ri[i] == rs[i]); }
        assert forall|i: int, j: int| 0 <= i < j < ri.len() implies (#[trigger] ri[i])[0] != (#[trigger] ri[j])[0] by {
            assert(ri[i] == rs[i] && ri[j] == rs[j]);
        }
        lemma_keep_unique(ri, a, mv);
        assert(rs[rs.len() - 1] == x);
        let ex_i = exists|i: int| 0 <= i < ri.len() && #[trigger] ri[i][0] == a && ri[i][1] == mv;
        if h(x) {
            assert(x =~= seq![a, mv]);
            if ex_i {
                let i = choose|i: int| 0 <= i < ri.len() && #[trigger] ri[i][0] == a && ri[i][1] == mv;
                assert(rs[i] == ri[i]);
                assert(rs[i][0] != rs[rs.len() - 1][0]);
            }
            assert(keep(ri, h) =~= Seq::<Row>::empty());
            assert(keep(rs, h) =~= seq![seq![a, mv]]);
        } else {
            if exists|i: int| 0 <= i < rs.len() && #[trigger] rs[i][0] == a && rs[i][1] == mv {
                let i = choose|i: int| 0 <= i < rs.len() && #[trigger] rs[i][0] == a && rs[i][1] == mv;
                assert(i < ri.len());
                assert(ri[i] == rs[i]);
            }
            if ex_i {
                let i = choose|i: int| 0 <= i < ri.len() && #[trigger] ri[i][0] == a && ri[i][1] == mv;
                assert(rs[i] == ri[i]);
            }
        }
    } else {
        assert(keep(rs, h) =~= Seq::<Row>::empty());
    }
}

/// The GROUP BY rows have distinct keys, and a supplier key meets one with SUM `mv` exactly when `hitk`.
pub proof fn lemma_grows_hit(db: Database, ps: Seq<Literal>, hi: int, s: Row, mv: Val)
    requires
        db.schema == schema_spec(), db_wf(db),
        supp_typed(s),
    ensures ({
        let g = qg(lo_of(ps), hi);
        let gr = grows(g, xd(db));
        &&& forall|i: int| 0 <= i < gr.len() ==> (#[trigger] gr[i]).len() == 2
        &&& forall|i: int, j: int| 0 <= i < j < gr.len() ==> (#[trigger] gr[i])[0] != (#[trigger] gr[j])[0]
        &&& (exists|i: int| 0 <= i < gr.len() && #[trigger] gr[i][0] == s[0] && gr[i][1] == mv) == hitk(g, xd(db), mv, s)
    }),
{
    let g = qg(lo_of(ps), hi);
    let xs = xd(db);
    let gr = grows(g, xs);
    let ks = gkeys(g, xs);
    lemma_grows(g, xs, lo_of(ps), hi);
    lemma_gkeys(g, xs);
    assert forall|i: int, j: int| 0 <= i < j < gr.len() implies (#[trigger] gr[i])[0] != (#[trigger] gr[j])[0] by {
        assert(gr[i].len() == 2 && gr[i][0] == ks[i][0] && ks[i] == seq![ks[i][0]]);
        assert(gr[j].len() == 2 && gr[j][0] == ks[j][0] && ks[j] == seq![ks[j][0]]);
        assert(ks[i] != ks[j]);
    }
    let k = seq![s[0]];
    if exists|i: int| 0 <= i < gr.len() && #[trigger] gr[i][0] == s[0] && gr[i][1] == mv {
        let i = choose|i: int| 0 <= i < gr.len() && #[trigger] gr[i][0] == s[0] && gr[i][1] == mv;
        assert(gr[i].len() == 2 && gr[i][0] == ks[i][0] && ks[i] == seq![ks[i][0]] && gr[i][1] == gvals(g, xs)[i]);
        assert(ks[i] =~= k);
        assert(ks.contains(k));
        assert(gvals(g, xs)[i] == Val::Num { coeff: gsum(g, xs, k, 0), scale: 4 });
    }
    if hitk(g, xs, mv, s) {
        assert(ks.contains(k));
        let i = choose|i: int| 0 <= i < ks.len() && ks[i] == k;
        assert(gr[i].len() == 2 && gr[i][0] == ks[i][0] && gr[i][1] == gvals(g, xs)[i]);
        assert(gvals(g, xs)[i] == Val::Num { coeff: gsum(g, xs, k, 0), scale: 4 });
    }
}

// ------------------------------------------------------------------------------------------------ the outer WHERE

/// The outer WHERE on a product row `s ++ r` (a supplier row and a GROUP BY row): `s_suppkey = supplier_no` and
/// `total_revenue = MAX`.
pub proof fn lemma_outer_truth(db: Database, ps: Seq<Literal>, hi: int, s: Row, r: Row)
    requires
        db.schema == schema_spec(), db_wf(db),
        param_typed(ps),
        hi_ok(lo_of(ps), hi),
        group_caps(qg(lo_of(ps), hi), xd(db)),
        supp_typed(s),
        grows(qg(lo_of(ps), hi), xd(db)).contains(r),
    ensures
        eval_pred(db, s + r, outer_pred(ps)) == Ok::<Truth, SqlError>(truth_of(outer_h(max_val(qg(lo_of(ps), hi), xd(db)))(s + r))),
{
    hide(eval_query);
    let g = qg(lo_of(ps), hi);
    let xs = xd(db);
    let gr = grows(g, xs);
    let vs = gvals(g, xs);
    let y = s + r;
    lemma_grows(g, xs, lo_of(ps), hi);
    let j = choose|j: int| 0 <= j < gr.len() && gr[j] == r;
    let k = gkeys(g, xs)[j];
    lemma_gkeys(g, xs);
    assert(gkeys(g, xs).contains(k));
    lemma_gkeys_witness(g, xs, k);
    let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], k);
    lemma_rows_typed(db);
    lemma_proj_all_len(db.tables[0]);
    lemma_proj4(db.tables[0][m]);
    assert(k == key_of(xs[m]));
    assert(r[0] == k[0] && k[0] == db.tables[0][m][2]);
    let b = ival(r[0]);
    let a = ival(s[0]);
    assert(y.len() == 9);
    assert(y[0] == s[0] && y[7] == r[0] && y[8] == r[1]);
    lemma_key_pred(db, y, a, b);
    // the subquery
    lemma_max_q(db, y, ps, hi);
    lemma_max_num(vs, 4);
    let mv = max_val(g, xs);
    assert(vs.len() > 0);
    let c = gsum(g, xs, k, 0);
    assert(r[1] == vs[j] && vs[j] == Val::Num { coeff: c, scale: 4 });
    let mc = mv->coeff;
    assert(mv == Val::Num { coeff: mc, scale: 4 });
    assert(eval_expr(db, y, Expr::Subquery(Box::new(max_q(ps)))) == Ok::<Val, SqlError>(mv)) by {
        reveal(eval_query);
    }
    lemma_expr_col(db, y, 8);
    lemma_compare_num(c, 4, mc, 4);
    lemma_align_same(c, 4);
    lemma_align_same(mc, 4);
    lemma_pred_cmp(db, y, CmpOp::Eq, Expr::Col(8), Expr::Subquery(Box::new(max_q(ps))), Val::Num { coeff: c, scale: 4 }, mv, c, mc);
    lemma_pred_and(db, y, p_key(), p_max(ps), a == b, c == mc);
}

// ------------------------------------------------------------------------------------------------ the body

/// The product `s ++ G`, kept by the outer WHERE, projected: `[res_row(s, mv)]` when `s` meets a group of SUM
/// `mv`, else nothing.
proof fn lemma_block(db: Database, ps: Seq<Literal>, hi: int, s: Row)
    requires
        db.schema == schema_spec(), db_wf(db),
        supp_typed(s),
    ensures ({
        let g = qg(lo_of(ps), hi);
        let gr = grows(g, xd(db));
        let mv = max_val(g, xd(db));
        keep(gr.map_values(|r: Row| s + r), outer_h(mv)).map_values(|y: Row| select(y, out_cols()))
            == if hitk(g, xd(db), mv, s) { seq![res_row(s, mv)] } else { Seq::<Row>::empty() }
    }),
{
    let g = qg(lo_of(ps), hi);
    let xs = xd(db);
    let gr = grows(g, xs);
    let mv = max_val(g, xs);
    let m = |r: Row| s + r;
    let f = outer_h(mv);
    lemma_keep_map(gr, m, f);
    lemma_grows_hit(db, ps, hi, s, mv);
    assert forall|i: int| 0 <= i < gr.len() implies (|y: Row| f(m(y)))(#[trigger] gr[i]) == grp_h(s[0], mv)(gr[i]) by {
        let y = s + gr[i];
        assert(y[0] == s[0] && y[7] == gr[i][0] && y[8] == gr[i][1]);
    }
    lemma_keep_ext(gr, |y: Row| f(m(y)), grp_h(s[0], mv));
    lemma_keep_unique(gr, s[0], mv);
    if hitk(g, xs, mv, s) {
        let one = seq![seq![s[0], mv]];
        assert(one.map_values(m) =~= seq![s + seq![s[0], mv]]);
        let y = s + seq![s[0], mv];
        assert(select(y, out_cols()) =~= res_row(s, mv));
        assert(seq![y].map_values(|y: Row| select(y, out_cols())) =~= seq![res_row(s, mv)]);
    } else {
        assert(Seq::<Row>::empty().map_values(m) =~= Seq::<Row>::empty());
        assert(Seq::<Row>::empty().map_values(|y: Row| select(y, out_cols())) =~= Seq::<Row>::empty());
    }
}

/// The product of supplier rows and the GROUP BY rows, kept by the outer WHERE and projected, is `body_rows`.
proof fn lemma_kept_product(db: Database, ps: Seq<Literal>, hi: int, ss: Seq<Row>)
    requires
        db.schema == schema_spec(), db_wf(db),
        forall|i: int| 0 <= i < ss.len() ==> supp_typed(#[trigger] ss[i]),
    ensures ({
        let g = qg(lo_of(ps), hi);
        let gr = grows(g, xd(db));
        let mv = max_val(g, xd(db));
        keep(product_rows(ss, gr), outer_h(mv)).map_values(|y: Row| select(y, out_cols())) == body_rows(ss, g, xd(db), mv)
    }),
    decreases ss.len(),
{
    let g = qg(lo_of(ps), hi);
    let xs = xd(db);
    let gr = grows(g, xs);
    let mv = max_val(g, xs);
    let f = outer_h(mv);
    let sel = |y: Row| select(y, out_cols());
    if ss.len() == 0 {
        assert(product_rows(ss, gr) =~= Seq::<Row>::empty());
        assert(keep(product_rows(ss, gr), f).map_values(sel) =~= Seq::<Row>::empty());
    } else {
        let si = ss.drop_last();
        let s = ss.last();
        assert forall|i: int| 0 <= i < si.len() implies supp_typed(#[trigger] si[i]) by { assert(si[i] == ss[i]); }
        lemma_kept_product(db, ps, hi, si);
        assert(ss[ss.len() - 1] == s);
        let block = gr.map_values(|r: Row| s + r);
        assert(product_rows(ss, gr) == product_rows(si, gr) + block);
        lemma_keep_append(product_rows(si, gr), block, f);
        lemma_block(db, ps, hi, s);
        let a = keep(product_rows(si, gr), f);
        let b = keep(block, f);
        assert((a + b).map_values(sel) =~= a.map_values(sel) + b.map_values(sel));
    }
}

/// FROM supplier, revenue0: the product of the supplier rows and the GROUP BY rows.
proof fn lemma_prod_eval(db: Database, ps: Seq<Literal>, hi: int)
    requires
        db.schema == schema_spec(), db_wf(db),
        param_typed(ps),
        hi_ok(lo_of(ps), hi),
        group_caps(qg(lo_of(ps), hi), xd(db)),
    ensures
        eval_query(db, Seq::empty(), prod_q(ps))
            == Ok::<Relation, SqlError>(product_rows(db.tables[5], grows(qg(lo_of(ps), hi), xd(db)))),
{
    lemma_supp_typed(db);
    lemma_rev_group(db, Seq::empty(), ps, hi);
    assert(eval_query(db, Seq::empty(), Query::Table(5)) == Ok::<Relation, SqlError>(db.tables[5]));
}

/// Row `m` of a product is a left row followed by a right row.
proof fn lemma_product_at(a: Seq<Row>, b: Seq<Row>, m: int) -> (ij: (int, int))
    requires 0 <= m < product_rows(a, b).len(),
    ensures
        0 <= ij.0 < a.len(), 0 <= ij.1 < b.len(),
        product_rows(a, b)[m] == a[ij.0] + b[ij.1],
{
    lemma_product_index(a, b);
    let nb = b.len() as int;
    assert(nb > 0) by {
        if nb == 0 {
            assert(a.len() * b.len() == 0) by (nonlinear_arith) requires nb == 0, b.len() == nb;
        }
    }
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m, nb);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(m, nb);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(m, nb);
    let i = m / nb;
    let j = m % nb;
    assert(nb * i == i * nb) by (nonlinear_arith);
    assert(i < a.len()) by (nonlinear_arith) requires i * nb + j == m, m < a.len() * nb, 0 <= j < nb, 0 <= i;
    assert(product_rows(a, b)[i * nb + j] == a[i] + b[j]);
    (i, j)
}

/// The outer WHERE on every product row.
proof fn lemma_where_truths(db: Database, ps: Seq<Literal>, hi: int)
    requires
        db.schema == schema_spec(), db_wf(db),
        param_typed(ps),
        hi_ok(lo_of(ps), hi),
        group_caps(qg(lo_of(ps), hi), xd(db)),
    ensures ({
        let g = qg(lo_of(ps), hi);
        let pr = product_rows(db.tables[5], grows(g, xd(db)));
        forall|i: int| 0 <= i < pr.len() ==> #[trigger] eval_pred(db, Seq::<Val>::empty() + pr[i], outer_pred(ps))
            == Ok::<Truth, SqlError>(truth_of(outer_h(max_val(g, xd(db)))(pr[i])))
    }),
{
    let g = qg(lo_of(ps), hi);
    let gr = grows(g, xd(db));
    let ss = db.tables[5];
    let pr = product_rows(ss, gr);
    lemma_supp_typed(db);
    assert forall|i: int| 0 <= i < pr.len() implies #[trigger] eval_pred(db, Seq::<Val>::empty() + pr[i], outer_pred(ps))
        == Ok::<Truth, SqlError>(truth_of(outer_h(max_val(g, xd(db)))(pr[i]))) by {
        let (a, b) = lemma_product_at(ss, gr, i);
        assert(Seq::<Val>::empty() + pr[i] =~= pr[i]);
        assert(gr.contains(gr[b]));
        assert(supp_typed(ss[a]));
        lemma_outer_truth(db, ps, hi, ss[a], gr[b]);
    }
}

/// One step of the WHERE denotation over an evaluated input and its collected truths.
proof fn lemma_filter_unfold(db: Database, ctx: Row, pred: Pred, input: Query, rows: Seq<Row>, truths: Seq<Truth>)
    requires
        eval_query(db, ctx, input) == Ok::<Relation, SqlError>(rows),
        collect(Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred))) == Ok::<Seq<Truth>, SqlError>(truths),
    ensures
        eval_query(db, ctx, Query::Filter { pred, input: Box::new(input) }) == Ok::<Relation, SqlError>(keep_true(rows, truths)),
{
    lemma_collect_pointwise::<Truth>();
}

/// The outer WHERE keeps the product rows of `outer_h`.
proof fn lemma_filt_eval(db: Database, ps: Seq<Literal>, hi: int)
    requires
        db.schema == schema_spec(), db_wf(db),
        param_typed(ps),
        hi_ok(lo_of(ps), hi),
        group_caps(qg(lo_of(ps), hi), xd(db)),
    ensures ({
        let g = qg(lo_of(ps), hi);
        let pr = product_rows(db.tables[5], grows(g, xd(db)));
        eval_query(db, Seq::empty(), filt_q(ps)) == Ok::<Relation, SqlError>(keep(pr, outer_h(max_val(g, xd(db)))))
    }),
{
    hide(eval_pred);
    hide(eval_query);
    let g = qg(lo_of(ps), hi);
    let pr = product_rows(db.tables[5], grows(g, xd(db)));
    let f = outer_h(max_val(g, xd(db)));
    let ctx = Seq::<Val>::empty();
    let pred = outer_pred(ps);
    lemma_prod_eval(db, ps, hi);
    lemma_where_truths(db, ps, hi);
    let truths = Seq::new(pr.len(), |i: int| truth_of(f(pr[i])));
    let prs = Seq::new(pr.len(), |i: int| eval_pred(db, ctx + pr[i], pred));
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Truth, SqlError>(truths[i]) by {}
    lemma_collect_all(prs, truths);
    lemma_collect_pointwise::<Truth>();
    assert(collect(Seq::new(pr.len(), |i: int| eval_pred(db, ctx + pr[i], pred))) == Ok::<Seq<Truth>, SqlError>(truths));
    lemma_filter_unfold(db, ctx, pred, prod_q(ps), pr, truths);
    crate::link::join::lemma_keep_true_keep(pr, truths, f);
}

/// The rows the outer WHERE keeps have nine columns.
proof fn lemma_kept_width(db: Database, ps: Seq<Literal>, hi: int)
    requires db.schema == schema_spec(), db_wf(db),
    ensures ({
        let g = qg(lo_of(ps), hi);
        let kept = keep(product_rows(db.tables[5], grows(g, xd(db))), outer_h(max_val(g, xd(db))));
        forall|i: int| 0 <= i < kept.len() ==> (#[trigger] kept[i]).len() == 9
    }),
{
    let g = qg(lo_of(ps), hi);
    let gr = grows(g, xd(db));
    let ss = db.tables[5];
    let pr = product_rows(ss, gr);
    let kept = keep(pr, outer_h(max_val(g, xd(db))));
    lemma_supp_typed(db);
    lemma_grows(g, xd(db), lo_of(ps), hi);
    lemma_keep_members(pr, outer_h(max_val(g, xd(db))));
    assert forall|i: int| 0 <= i < kept.len() implies (#[trigger] kept[i]).len() == 9 by {
        assert(pr.contains(kept[i]));
        let m = choose|m: int| 0 <= m < pr.len() && pr[m] == kept[i];
        let (a, b) = lemma_product_at(ss, gr, m);
        assert(supp_typed(ss[a]));
        assert(gr[b].len() == 2);
    }
}

/// The statement body: `body_rows` of the supplier rows, inside the SUM capacity condition.
pub proof fn lemma_body(db: Database, ps: Seq<Literal>, hi: int)
    requires
        db.schema == schema_spec(), db_wf(db),
        param_typed(ps),
        hi_ok(lo_of(ps), hi),
        group_caps(qg(lo_of(ps), hi), xd(db)),
    ensures
        eval_query(db, Seq::empty(), body_q(ps))
            == Ok::<Relation, SqlError>(body_rows(db.tables[5], qg(lo_of(ps), hi), xd(db), max_val(qg(lo_of(ps), hi), xd(db)))),
{
    hide(eval_query);
    let g = qg(lo_of(ps), hi);
    let kept = keep(product_rows(db.tables[5], grows(g, xd(db))), outer_h(max_val(g, xd(db))));
    lemma_filt_eval(db, ps, hi);
    lemma_kept_width(db, ps, hi);
    lemma_supp_typed(db);
    assert forall|m: int| 0 <= m < out_cols().len() implies #[trigger] out_cols()[m] < 9 by {}
    lemma_project_cols(db, filt_q(ps), kept, out_cols(), 9);
    lemma_kept_product(db, ps, hi, db.tables[5]);
}

// ------------------------------------------------------------------------------------------------ other outcomes

/// A WHERE over no row keeps no row.
proof fn lemma_filter_none(db: Database, ctx: Row, pred: Pred, input: Query)
    requires eval_query(db, ctx, input) == Ok::<Relation, SqlError>(Seq::<Row>::empty()),
    ensures eval_query(db, ctx, Query::Filter { pred, input: Box::new(input) }) == Ok::<Relation, SqlError>(Seq::<Row>::empty()),
{
    let rows = Seq::<Row>::empty();
    assert(collect(Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred))) == Ok::<Seq<Truth>, SqlError>(Seq::empty()));
    assert(keep_true(rows, Seq::<Truth>::empty()) =~= rows);
}

/// A SELECT over no row has no row.
proof fn lemma_project_none(db: Database, ctx: Row, exprs: Seq<Expr>, input: Query)
    requires eval_query(db, ctx, input) == Ok::<Relation, SqlError>(Seq::<Row>::empty()),
    ensures eval_query(db, ctx, Query::Project { exprs, input: Box::new(input) }) == Ok::<Relation, SqlError>(Seq::<Row>::empty()),
{
    let rows = Seq::<Row>::empty();
    assert(collect(Seq::new(rows.len(), |i: int| eval_exprs(db, ctx + rows[i], exprs))) == Ok::<Seq<Row>, SqlError>(Seq::empty()));
}

/// A GROUP BY over no row has no group.
proof fn lemma_group_none(db: Database, ctx: Row, keys: Seq<Expr>, aggs: Seq<Agg>, input: Query)
    requires eval_query(db, ctx, input) == Ok::<Relation, SqlError>(Seq::<Row>::empty()),
    ensures eval_query(db, ctx, Query::GroupBy { keys, aggs, input: Box::new(input) }) == Ok::<Relation, SqlError>(Seq::<Row>::empty()),
{
    let rows = Seq::<Row>::empty();
    let prep = Seq::<(Row, Row)>::empty();
    assert(collect(Seq::new(rows.len(), |i: int|
        match eval_exprs(db, ctx + rows[i], keys) {
            Err(err) => Err(err),
            Ok(k) => match agg_args(db, ctx + rows[i], aggs) {
                Err(err) => Err(err),
                Ok(a) => Ok((k, a)),
            },
        })) == Ok::<Seq<(Row, Row)>, SqlError>(prep));
    lemma_groupby_unfold_ctx(db, ctx, input, keys, aggs, rows, prep);
    let ks = prep.map_values(|p: (Row, Row)| p.0);
    let args = prep.map_values(|p: (Row, Row)| p.1);
    assert(ks =~= Seq::<Row>::empty());
    assert(distinct_rows(ks).len() == 0);
    assert(collect(Seq::new(distinct_rows(ks).len(), |gi: int|
        match agg_row(aggs, group_members(ks, args, distinct_rows(ks)[gi])) {
            Ok(a) => Ok(distinct_rows(ks)[gi] + a),
            Err(e) => Err(e),
        })) == Ok::<Seq<Row>, SqlError>(Seq::empty()));
}

/// The product of any rows with no rows is empty.
proof fn lemma_product_empty(a: Seq<Row>)
    ensures product_rows(a, Seq::<Row>::empty()) == Seq::<Row>::empty(),
    decreases a.len(),
{
    if a.len() > 0 {
        lemma_product_empty(a.drop_last());
        assert(Seq::<Row>::empty().map_values(|r: Row| a.last() + r) =~= Seq::<Row>::empty());
        assert(Seq::<Row>::empty() + Seq::<Row>::empty() =~= Seq::<Row>::empty());
    }
}

/// With no lineitem row, `revenue0` is empty in any context (whatever `$1 + 3 months` evaluates to).
pub proof fn lemma_rev_group_empty(db: Database, ctx: Row, ps: Seq<Literal>)
    requires db.tables.len() > 0, db.tables[0].len() == 0,
    ensures eval_query(db, ctx, rev_group(ctx.len(), ps)) == Ok::<Relation, SqlError>(Seq::<Row>::empty()),
{
    let o = ctx.len();
    assert(db.tables[0] =~= Seq::<Row>::empty());
    assert(eval_query(db, ctx, Query::Table(0)) == Ok::<Relation, SqlError>(Seq::<Row>::empty()));
    lemma_filter_none(db, ctx, p_date(o, ps), Query::Table(0));
    lemma_group_none(db, ctx, rev_keys(o), rev_aggs(o), rev_filter(o, ps));
}

/// With no lineitem row the body has no row.
pub proof fn lemma_body_empty(db: Database, ps: Seq<Literal>)
    requires db.tables.len() > 5, db.tables[0].len() == 0,
    ensures eval_query(db, Seq::empty(), body_q(ps)) == Ok::<Relation, SqlError>(Seq::<Row>::empty()),
{
    let ctx = Seq::<Val>::empty();
    lemma_rev_group_empty(db, ctx, ps);
    lemma_product_empty(db.tables[5]);
    assert(eval_query(db, ctx, Query::Table(5)) == Ok::<Relation, SqlError>(db.tables[5]));
    assert(eval_query(db, ctx, prod_q(ps)) == Ok::<Relation, SqlError>(Seq::<Row>::empty()));
    lemma_filter_none(db, ctx, outer_pred(ps), prod_q(ps));
    lemma_project_none(db, ctx, col_exprs(out_cols()), filt_q(ps));
}

/// `$1 + 3 months` outside the timestamp range with a lineitem row: the body is that error.
pub proof fn lemma_body_err(db: Database, ps: Seq<Literal>)
    requires
        db.schema == schema_spec(), db_wf(db),
        param_typed(ps),
        hi_value(lo_of(ps)) is Err,
        db.tables[0].len() > 0,
    ensures
        eval_query(db, Seq::empty(), body_q(ps)) == Err::<Relation, SqlError>(hi_value(lo_of(ps))->Err_0),
{
    hide(eval_pred);
    let e = hi_value(lo_of(ps))->Err_0;
    let ctx = Seq::<Val>::empty();
    let rows = db.tables[0];
    lemma_rows_typed(db);
    assert(eval_query(db, ctx, Query::Table(0)) == Ok::<Relation, SqlError>(rows));
    assert forall|k: int| 0 <= k < rows.len() implies #[trigger] eval_pred(db, ctx + rows[k], p_date(0, ps)) == Err::<Truth, SqlError>(e) by {
        assert(ctx + rows[k] =~= rows[k]);
        assert(row_typed(rows[k]));
        lemma_pred_err_row(db, rows[k], 0, ps, ival(rows[k][10]));
    }
    lemma_filter_err(db, ctx, p_date(0, ps), Box::new(Query::Table(0)), rows, e, 0);
    lemma_first_input(db, ctx, rev_group(0, ps));
    assert(eval_query(db, ctx, Query::Table(5)) == Ok::<Relation, SqlError>(db.tables[5]));
    lemma_second_input(db, ctx, prod_q(ps), db.tables[5]);
    lemma_first_input(db, ctx, filt_q(ps));
    lemma_first_input(db, ctx, body_q(ps));
}

/// The absolute mass of a group's SUM arguments (all at scale 4) is its `gabs`.
proof fn lemma_members_mass(lo: int, hi: int, xs: Seq<Row>, k: Row)
    ensures ({
        let g = qg(lo, hi);
        &&& num_mass_at(column(members(g, xs, k), 0), 4) == gabs(g, xs, k, 0)
        &&& forall|i: int| 0 <= i < column(members(g, xs, k), 0).len() ==>
            (#[trigger] column(members(g, xs, k), 0)[i]) is Num && column(members(g, xs, k), 0)[i]->Num_scale == 4
    }),
    decreases xs.len(),
{
    let g = qg(lo, hi);
    let vs = column(members(g, xs, k), 0);
    if xs.len() > 0 {
        let xi = xs.drop_last();
        let x = xs.last();
        lemma_members_mass(lo, hi, xi, k);
        let vi = column(members(g, xi, k), 0);
        if hit(g, x, k) {
            assert(members(g, xs, k) == members(g, xi, k).push(arg_vals(g, x)));
            assert(vs =~= vi.push(arg_vals(g, x)[0]));
            assert(arg_vals(g, x)[0] == (Val::Num { coeff: (g.arg)(0, x), scale: 4 }));
            assert(vs.drop_last() =~= vi);
            assert(pow10(0) == 1);
            assert(abs((g.arg)(0, x)) * pow10((4 - 4) as nat) == abs((g.arg)(0, x)));
            assert forall|i: int| 0 <= i < vs.len() implies (#[trigger] vs[i]) is Num && vs[i]->Num_scale == 4 by {
                if i < vi.len() {
                    assert(vs[i] == vi[i]);
                }
            }
        } else {
            assert(members(g, xs, k) == members(g, xi, k));
        }
    } else {
        assert(vs.len() == 0);
    }
}

/// Over the members of every group: SUM succeeds inside its capacity condition; over the members of a group of
/// mass above `i128::MAX`, it is outside.
proof fn lemma_members_caps(o: nat, lo: int, hi: int, xs: Seq<Row>, k: Row)
    ensures
        aggs_ok_inside(rev_aggs(o), members(qg(lo, hi), xs, k)),
        gcount(qg(lo, hi), xs, k) > 0 && gabs(qg(lo, hi), xs, k, 0) > i128_max() ==>
            !fits_agg_value(rev_aggs(o)[0], column(members(qg(lo, hi), xs, k), 0)),
{
    let g = qg(lo, hi);
    let mem = members(g, xs, k);
    let vs = column(mem, 0);
    lemma_members_col(g, xs, k, 0);
    assert(all_of_kind(NumKind::Numeric, vs));
    assert forall|j: int| 0 <= j < rev_aggs(o).len() && #[trigger] fits_agg_value(rev_aggs(o)[j], column(mem, j))
        implies agg_value(rev_aggs(o)[j], column(mem, j)) is Ok by {
        lemma_sum_inside_ok(NumKind::Numeric, rev_arg(o), vs);
    }
    if gcount(g, xs, k) > 0 && gabs(g, xs, k, 0) > i128_max() {
        lemma_members_mass(lo, hi, xs, k);
        assert forall|i: int| 0 <= i < vs.len() implies (#[trigger] vs[i] matches Val::Num { coeff, scale } ==> scale == 4) by {}
        lemma_num_mass_uniform(vs, 4);
        lemma_count_members(g, xs, k);
        assert(vs.len() > 0);
        assert(vs[0] is Num);
        assert(num_max_scale(vs) == 4);
        assert(sum_mass(NumKind::Numeric, vs) > i128::MAX as int);
    }
}

/// A group's members are one per qualifying row of the group.
proof fn lemma_count_members(g: QuerySpec, xs: Seq<Row>, k: Row)
    ensures members(g, xs, k).len() == gcount(g, xs, k),
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_count_members(g, xs.drop_last(), k);
    }
}

/// The kept rows' GROUP BY inputs at the top level: key and argument row per kept row.
proof fn lemma_group_inputs(db: Database, ps: Seq<Literal>, hi: int)
    requires
        db.schema == schema_spec(), db_wf(db),
        param_typed(ps),
        hi_ok(lo_of(ps), hi),
    ensures ({
        let g = qg(lo_of(ps), hi);
        let xs = xd(db);
        let kept = keep_true(db.tables[0], qual_truths(g, xs));
        let ks = qkeys(g, xs);
        let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
        &&& eval_query(db, Seq::empty(), rev_filter(0, ps)) == Ok::<Relation, SqlError>(kept)
        &&& ks.len() == kept.len() && args.len() == kept.len()
        &&& forall|i: int| 0 <= i < kept.len() ==> #[trigger] group_input(db, Seq::<Val>::empty() + kept[i], rev_keys(0), rev_aggs(0))
                == Ok::<(Row, Row), SqlError>((ks[i], args[i]))
    }),
{
    hide(eval_pred);
    hide(eval_exprs);
    hide(agg_args);
    let g = qg(lo_of(ps), hi);
    let rows = db.tables[0];
    let cols = cols4();
    let xs = xd(db);
    let ctx = Seq::<Val>::empty();
    lemma_rev_filter(db, ctx, ps, hi);
    let kept = keep_true(rows, qual_truths(g, xs));
    lemma_kept_rows(g, rows, cols);
    lemma_prepared_ctx(db, ctx, ps, hi, kept);
    let qr = qrows(g, xs);
    let ks = qkeys(g, xs);
    let args = qr.map_values(|x: Row| arg_vals(g, x));
    assert(proj_all(kept, cols) == qr);
    assert(kept.len() == qr.len());
    let pre = Seq::new(kept.len(), |i: int|
        match eval_exprs(db, ctx + kept[i], rev_keys(0)) {
            Err(err) => Err(err),
            Ok(kk) => match agg_args(db, ctx + kept[i], rev_aggs(0)) {
                Err(err) => Err(err),
                Ok(a) => Ok((kk, a)),
            },
        });
    let prep = Seq::new(kept.len(), |i: int| ((g.key)(proj(kept[i], cols)), arg_vals(g, proj(kept[i], cols))));
    crate::bridge::collect::lemma_collect_ok(pre);
    assert forall|i: int| 0 <= i < kept.len() implies #[trigger] group_input(db, ctx + kept[i], rev_keys(0), rev_aggs(0))
        == Ok::<(Row, Row), SqlError>((ks[i], args[i])) by {
        assert(pre[i] is Ok);
        assert(collect(pre)->Ok_0[i] == prep[i]);
        assert(proj(kept[i], cols) == qr[i]);
    }
}

/// A group of `revenue0` whose SUM has absolute mass above `i128::MAX` puts `revenue0` outside its capacity domain.
proof fn lemma_group_capacity(db: Database, ps: Seq<Literal>, hi: int, k: Row)
    requires
        db.schema == schema_spec(), db_wf(db),
        param_typed(ps),
        hi_ok(lo_of(ps), hi),
        gcount(qg(lo_of(ps), hi), xd(db), k) > 0,
        gabs(qg(lo_of(ps), hi), xd(db), k, 0) > i128_max(),
    ensures !fits_query(db, Seq::empty(), rev_group(0, ps)),
{
    let g = qg(lo_of(ps), hi);
    let xs = xd(db);
    let ctx = Seq::<Val>::empty();
    let kept = keep_true(db.tables[0], qual_truths(g, xs));
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    lemma_group_inputs(db, ps, hi);
    lemma_keys_exact(db, lo_of(ps), hi);
    lemma_pool_exact(g, xs);
    let pool = key_pool(g, xs);
    lemma_distinct_gkeys(g, xs, pool);
    lemma_gkeys(g, xs);
    let gk = gkeys(g, xs);
    assert(gk.contains(k));
    let gi = choose|gi: int| 0 <= gi < gk.len() && gk[gi] == k;
    assert(pool.contains(gk[gi]));
    lemma_group_members(g, xs, k, pool);
    lemma_members_caps(0, lo_of(ps), hi, xs, k);
    assert forall|h: int| 0 <= h < distinct_rows(ks).len() implies #[trigger] aggs_ok_inside(rev_aggs(0), group_members(ks, args, distinct_rows(ks)[h])) by {
        assert(pool.contains(gk[h]));
        lemma_group_members(g, xs, gk[h], pool);
        lemma_members_caps(0, lo_of(ps), hi, xs, gk[h]);
    }
    lemma_group_by_capacity(db, ctx, rev_keys(0), rev_aggs(0), Box::new(rev_filter(0, ps)), kept, ks, args, gi, 0);
}

/// A group of `revenue0` whose SUM has absolute mass above `i128::MAX` puts the statement outside its capacity
/// domain.
pub proof fn lemma_body_capacity(db: Database, ps: Seq<Literal>, hi: int, k: Row)
    requires
        db.schema == schema_spec(), db_wf(db),
        param_typed(ps),
        hi_ok(lo_of(ps), hi),
        gcount(qg(lo_of(ps), hi), xd(db), k) > 0,
        gabs(qg(lo_of(ps), hi), xd(db), k, 0) > i128_max(),
    ensures !capacity_domain(db, query_spec_at(ps)),
{
    hide(eval_query);
    hide(fits_query);
    let ctx = Seq::<Val>::empty();
    lemma_group_capacity(db, ps, hi, k);
    lemma_table5(db, ctx);
    lemma_second_input(db, ctx, prod_q(ps), db.tables[5]);
    lemma_first_input(db, ctx, filt_q(ps));
    lemma_first_input(db, ctx, body_q(ps));
    lemma_shape(ps);
}

/// The supplier table evaluates to its rows.
proof fn lemma_table5(db: Database, ctx: Row)
    requires db.tables.len() > 5,
    ensures eval_query(db, ctx, Query::Table(5)) == Ok::<Relation, SqlError>(db.tables[5]),
{
}

} // verus!
