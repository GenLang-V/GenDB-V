//! The statement's relations in the Q2 normal form (`q2spec`).
//!
//! FROM lists: `prod5` (part, supplier, partsupp, nation, region) and `inner_rows` (partsupp, supplier, nation,
//! region); their rows are `x5` / `y4` concatenations of one row per table. The subquery's value for a partkey is
//! `sub_val` (`lemma_eval_sub`): NULL when no partsupp row of the key has a supplier in region `$3`, else the
//! least such supply cost (`lemma_sub_val`). The outer WHERE keeps the rows satisfying `q_row`
//! (`lemma_eval_filter_ok`), the body projects them (`lemma_eval_body_ok`), and their bag is that of the
//! candidates' output rows (`lemma_body_multiset`). A failing LIKE makes the body the first part row's error
//! (`lemma_eval_filter_err`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::aggs::minmax::{extremum, min_value};
use crate::link::join::{keep, lemma_keep_true_keep, lemma_keep_members, lemma_product_index, lemma_product_assoc};
use crate::link::query::{proj, proj_all};
use crate::bridge::collect::{lemma_collect_all, lemma_collect_first_err, lemma_collect_ok, lemma_collect_pointwise};
use super::common::relops::*;
use super::q2spec::*;
use super::sqlq::*;
use super::tables::*;

verus! {

// ------------------------------------------------------------------------------------------------ tables

/// The statement's five tables in a database.
pub open spec fn tabs_of(db: Database) -> Tabs {
    Tabs { p: db.tables[3], s: db.tables[5], ps: db.tables[4], n: db.tables[6], r: db.tables[7] }
}

pub open spec fn p_typed(r: Row) -> bool {
    r.len() == 9 && r[0] is Int && r[2] is Text && r[4] is Text && r[5] is Int
}

pub open spec fn s_typed(r: Row) -> bool {
    &&& r.len() == 7
    &&& r[0] is Int && r[1] is Text && r[2] is Text && r[3] is Int && r[4] is Text && r[6] is Text
    &&& r[5] is Num && r[5]->scale == 2
}

pub open spec fn ps_typed(r: Row) -> bool {
    r.len() == 5 && r[0] is Int && r[1] is Int && r[3] is Num && r[3]->scale == 2
}

pub open spec fn n_typed(r: Row) -> bool {
    r.len() == 4 && r[0] is Int && r[1] is Text && r[2] is Int
}

pub open spec fn r_typed(r: Row) -> bool {
    r.len() == 3 && r[0] is Int && r[1] is Text
}

/// The value shapes of every row the statement reads.
pub open spec fn tabs_typed(t: Tabs) -> bool {
    &&& forall|i: int| 0 <= i < t.p.len() ==> #[trigger] p_typed(t.p[i])
    &&& forall|i: int| 0 <= i < t.s.len() ==> #[trigger] s_typed(t.s[i])
    &&& forall|i: int| 0 <= i < t.ps.len() ==> #[trigger] ps_typed(t.ps[i])
    &&& forall|i: int| 0 <= i < t.n.len() ==> #[trigger] n_typed(t.n[i])
    &&& forall|i: int| 0 <= i < t.r.len() ==> #[trigger] r_typed(t.r[i])
}

pub proof fn lemma_tabs_typed(c: Cols, t: Tabs)
    requires cols_ok(c, t),
    ensures tabs_typed(t),
{
    assert forall|i: int| 0 <= i < t.p.len() implies #[trigger] p_typed(t.p[i]) by { assert(part_row_ok(c.p, t.p[i], i)); }
    assert forall|i: int| 0 <= i < t.s.len() implies #[trigger] s_typed(t.s[i]) by { assert(supp_row_ok(c.s, t.s[i], i)); }
    assert forall|i: int| 0 <= i < t.ps.len() implies #[trigger] ps_typed(t.ps[i]) by { assert(ps_row_ok(c.ps, t.ps[i], i)); }
    assert forall|i: int| 0 <= i < t.n.len() implies #[trigger] n_typed(t.n[i]) by { assert(nat_row_ok(c.n, t.n[i], i)); }
    assert forall|i: int| 0 <= i < t.r.len() implies #[trigger] r_typed(t.r[i]) by { assert(reg_row_ok(c.r, t.r[i], i)); }
}

/// Every table's rows are distinct (primary keys).
pub open spec fn tabs_nodup(t: Tabs) -> bool {
    &&& t.p.no_duplicates()
    &&& t.s.no_duplicates()
    &&& t.ps.no_duplicates()
    &&& t.n.no_duplicates()
    &&& t.r.no_duplicates()
}

// ------------------------------------------------------------------------------------------------ FROM lists

pub open spec fn inner_rows(t: Tabs) -> Seq<Row> {
    product_rows(product_rows(product_rows(t.ps, t.s), t.n), t.r)
}

pub open spec fn prod5(t: Tabs) -> Seq<Row> {
    product_rows(product_rows(product_rows(product_rows(t.p, t.s), t.ps), t.n), t.r)
}

pub open spec fn y4(t: Tabs, k: int, j: int, n: int, r: int) -> Row {
    t.ps[k] + t.s[j] + t.n[n] + t.r[r]
}

pub open spec fn x5(t: Tabs, i: int, j: int, k: int, n: int, r: int) -> Row {
    t.p[i] + t.s[j] + t.ps[k] + t.n[n] + t.r[r]
}

pub open spec fn y4_idx(t: Tabs, k: int, j: int, n: int, r: int) -> bool {
    0 <= k < t.ps.len() && 0 <= j < t.s.len() && 0 <= n < t.n.len() && 0 <= r < t.r.len()
}

pub open spec fn x5_idx(t: Tabs, i: int, j: int, k: int, n: int, r: int) -> bool {
    0 <= i < t.p.len() && y4_idx(t, k, j, n, r)
}

pub proof fn lemma_inner_has(t: Tabs, k: int, j: int, n: int, r: int)
    requires y4_idx(t, k, j, n, r),
    ensures inner_rows(t).contains(y4(t, k, j, n, r)),
{
    let a = product_rows(t.ps, t.s);
    let b = product_rows(a, t.n);
    lemma_product_has(t.ps, t.s, k, j);
    let fa = choose|f: int| 0 <= f < a.len() && a[f] == t.ps[k] + t.s[j];
    lemma_product_has(a, t.n, fa, n);
    let fb = choose|f: int| 0 <= f < b.len() && b[f] == a[fa] + t.n[n];
    lemma_product_has(b, t.r, fb, r);
}

pub proof fn lemma_inner_split(t: Tabs, y: Row)
    requires inner_rows(t).contains(y),
    ensures exists|k: int, j: int, n: int, r: int| #[trigger] y4_idx(t, k, j, n, r) && y == y4(t, k, j, n, r),
{
    let a = product_rows(t.ps, t.s);
    let b = product_rows(a, t.n);
    lemma_product_split(b, t.r, y);
    let (fb, r) = choose|fb: int, r: int| 0 <= fb < b.len() && 0 <= r < t.r.len() && y == #[trigger] b[fb] + #[trigger] t.r[r];
    assert(b.contains(b[fb]));
    lemma_product_split(a, t.n, b[fb]);
    let (fa, n) = choose|fa: int, n: int| 0 <= fa < a.len() && 0 <= n < t.n.len() && b[fb] == #[trigger] a[fa] + #[trigger] t.n[n];
    assert(a.contains(a[fa]));
    lemma_product_split(t.ps, t.s, a[fa]);
    let (k, j) = choose|k: int, j: int| 0 <= k < t.ps.len() && 0 <= j < t.s.len() && a[fa] == #[trigger] t.ps[k] + #[trigger] t.s[j];
    assert(y4_idx(t, k, j, n, r) && y == y4(t, k, j, n, r));
}

pub proof fn lemma_prod5_has(t: Tabs, i: int, j: int, k: int, n: int, r: int)
    requires x5_idx(t, i, j, k, n, r),
    ensures prod5(t).contains(x5(t, i, j, k, n, r)),
{
    let a = product_rows(t.p, t.s);
    let b = product_rows(a, t.ps);
    let c = product_rows(b, t.n);
    lemma_product_has(t.p, t.s, i, j);
    let fa = choose|f: int| 0 <= f < a.len() && a[f] == t.p[i] + t.s[j];
    lemma_product_has(a, t.ps, fa, k);
    let fb = choose|f: int| 0 <= f < b.len() && b[f] == a[fa] + t.ps[k];
    lemma_product_has(b, t.n, fb, n);
    let fc = choose|f: int| 0 <= f < c.len() && c[f] == b[fb] + t.n[n];
    lemma_product_has(c, t.r, fc, r);
}

pub proof fn lemma_prod5_split(t: Tabs, x: Row)
    requires prod5(t).contains(x),
    ensures exists|i: int, j: int, k: int, n: int, r: int| #[trigger] x5_idx(t, i, j, k, n, r) && x == x5(t, i, j, k, n, r),
{
    let a = product_rows(t.p, t.s);
    let b = product_rows(a, t.ps);
    let c = product_rows(b, t.n);
    lemma_product_split(c, t.r, x);
    let (fc, r) = choose|fc: int, r: int| 0 <= fc < c.len() && 0 <= r < t.r.len() && x == #[trigger] c[fc] + #[trigger] t.r[r];
    assert(c.contains(c[fc]));
    lemma_product_split(b, t.n, c[fc]);
    let (fb, n) = choose|fb: int, n: int| 0 <= fb < b.len() && 0 <= n < t.n.len() && c[fc] == #[trigger] b[fb] + #[trigger] t.n[n];
    assert(b.contains(b[fb]));
    lemma_product_split(a, t.ps, b[fb]);
    let (fa, k) = choose|fa: int, k: int| 0 <= fa < a.len() && 0 <= k < t.ps.len() && b[fb] == #[trigger] a[fa] + #[trigger] t.ps[k];
    assert(a.contains(a[fa]));
    lemma_product_split(t.p, t.s, a[fa]);
    let (i, j) = choose|i: int, j: int| 0 <= i < t.p.len() && 0 <= j < t.s.len() && a[fa] == #[trigger] t.p[i] + #[trigger] t.s[j];
    assert(x5_idx(t, i, j, k, n, r) && x == x5(t, i, j, k, n, r));
}

/// The columns of an inner row.
pub proof fn lemma_y4(t: Tabs, k: int, j: int, n: int, r: int)
    requires tabs_typed(t), y4_idx(t, k, j, n, r),
    ensures ({
        let y = y4(t, k, j, n, r);
        &&& yrow_ok(y)
        &&& y[0] == t.ps[k][0] && y[1] == t.ps[k][1] && y[3] == t.ps[k][3]
        &&& y[5] == t.s[j][0] && y[8] == t.s[j][3]
        &&& y[12] == t.n[n][0] && y[14] == t.n[n][2]
        &&& y[16] == t.r[r][0] && y[17] == t.r[r][1]
    }),
{
    assert(ps_typed(t.ps[k]) && s_typed(t.s[j]) && n_typed(t.n[n]) && r_typed(t.r[r]));
}

/// The columns of an outer row.
pub proof fn lemma_x5(t: Tabs, i: int, j: int, k: int, n: int, r: int)
    requires tabs_typed(t), x5_idx(t, i, j, k, n, r),
    ensures ({
        let x = x5(t, i, j, k, n, r);
        &&& xrow_ok(x)
        &&& x[0] == t.p[i][0] && x[2] == t.p[i][2] && x[4] == t.p[i][4] && x[5] == t.p[i][5]
        &&& x[9] == t.s[j][0] && x[10] == t.s[j][1] && x[11] == t.s[j][2] && x[12] == t.s[j][3]
        &&& x[13] == t.s[j][4] && x[14] == t.s[j][5] && x[15] == t.s[j][6]
        &&& x[16] == t.ps[k][0] && x[17] == t.ps[k][1] && x[19] == t.ps[k][3]
        &&& x[21] == t.n[n][0] && x[22] == t.n[n][1] && x[23] == t.n[n][2]
        &&& x[25] == t.r[r][0] && x[26] == t.r[r][1]
    }),
{
    assert(p_typed(t.p[i]) && s_typed(t.s[j]) && ps_typed(t.ps[k]) && n_typed(t.n[n]) && r_typed(t.r[r]));
}

// ------------------------------------------------------------------------------------------------ subquery

pub open spec fn gq_f(pkv: Val, rname: Seq<u8>) -> spec_fn(Row) -> bool {
    |y: Row| gq(pkv, rname, y)
}

/// The supply costs (column 3) of inner rows.
pub open spec fn cost_vals(rows: Seq<Row>) -> Seq<Val> {
    rows.map_values(|y: Row| y[3])
}

/// The subquery's value for partkey value `pkv`: MIN of the supply costs of its inner rows.
pub open spec fn sub_val(t: Tabs, m: Prm, pkv: Val) -> Val {
    extremum(false, cost_vals(keep(inner_rows(t), gq_f(pkv, m.rname))))->Ok_0
}

/// The inner condition on an inner row `y4(k, j, n, r)`.
pub proof fn lemma_gq_y4(t: Tabs, m: Prm, pkv: Val, k: int, j: int, n: int, r: int)
    requires tabs_typed(t), y4_idx(t, k, j, n, r),
    ensures gq(pkv, m.rname, y4(t, k, j, n, r)) == (t.ps[k][0] == pkv && smatch(t, k, j) && nmatch(t, j, n) && rmatch(t, m, n, r)),
{
    lemma_y4(t, k, j, n, r);
}

/// The subquery's value: NULL without a qualifying partsupp row, else the least qualifying supply cost.
pub proof fn lemma_sub_val(t: Tabs, m: Prm, pkv: Val)
    requires tabs_typed(t),
    ensures
        sub_val(t, m, pkv) is Null || (sub_val(t, m, pkv) is Num && sub_val(t, m, pkv)->scale == 2),
        extremum(false, cost_vals(keep(inner_rows(t), gq_f(pkv, m.rname)))) is Ok,
        (forall|k: int| !#[trigger] qual(t, m, pkv, k)) ==> sub_val(t, m, pkv) == Val::Null,
        (exists|k: int| #[trigger] qual(t, m, pkv, k)) ==> {
            &&& sub_val(t, m, pkv) is Num
            &&& exists|k0: int| #[trigger] qual(t, m, pkv, k0) && sub_val(t, m, pkv) == (Val::Num { coeff: cost(t, k0), scale: 2 })
            &&& forall|k: int| #[trigger] qual(t, m, pkv, k) ==> sub_val(t, m, pkv)->coeff <= cost(t, k)
        },
{
    let rows = inner_rows(t);
    let f = gq_f(pkv, m.rname);
    let kept = keep(rows, f);
    let vs = cost_vals(kept);
    lemma_keep_members(rows, f);
    // Every kept row is a qualifying partsupp row's inner row; its cost value is that row's supply cost.
    assert forall|x: int| #![trigger vs[x]] 0 <= x < vs.len() implies exists|k: int| #[trigger] qual(t, m, pkv, k) && vs[x] == (Val::Num { coeff: cost(t, k), scale: 2 }) by {
        assert(rows.contains(kept[x]) && f(kept[x]));
        lemma_inner_split(t, kept[x]);
        let (k, j, n, r) = choose|k: int, j: int, n: int, r: int| #[trigger] y4_idx(t, k, j, n, r) && kept[x] == y4(t, k, j, n, r);
        lemma_y4(t, k, j, n, r);
        lemma_gq_y4(t, m, pkv, k, j, n, r);
        assert(ps_typed(t.ps[k]));
        assert(qual(t, m, pkv, k));
    }
    assert forall|x: int| 0 <= x < vs.len() implies (#[trigger] vs[x]) is Num && vs[x]->scale == 2 by {
        let k = choose|k: int| #[trigger] qual(t, m, pkv, k) && vs[x] == (Val::Num { coeff: cost(t, k), scale: 2 });
    }
    lemma_min_num(vs, 2);
    let sv = sub_val(t, m, pkv);
    if exists|k: int| #[trigger] qual(t, m, pkv, k) {
        let k1 = choose|k: int| #[trigger] qual(t, m, pkv, k);
        let (j1, n1, r1) = choose|j: int, n: int, r: int| #![trigger smatch(t, k1, j), nmatch(t, j, n), rmatch(t, m, n, r)]
            smatch(t, k1, j) && nmatch(t, j, n) && rmatch(t, m, n, r);
        lemma_inner_has(t, k1, j1, n1, r1);
        lemma_gq_y4(t, m, pkv, k1, j1, n1, r1);
        lemma_keep_has(rows, f, y4(t, k1, j1, n1, r1));
        assert(vs.len() > 0);
        let x0 = choose|x: int| 0 <= x < vs.len() && vs[x] == sv;
        let k0 = choose|k: int| #[trigger] qual(t, m, pkv, k) && vs[x0] == (Val::Num { coeff: cost(t, k), scale: 2 });
        assert forall|k: int| #[trigger] qual(t, m, pkv, k) implies sv->coeff <= cost(t, k) by {
            let (j, n, r) = choose|j: int, n: int, r: int| #![trigger smatch(t, k, j), nmatch(t, j, n), rmatch(t, m, n, r)]
                smatch(t, k, j) && nmatch(t, j, n) && rmatch(t, m, n, r);
            lemma_inner_has(t, k, j, n, r);
            lemma_gq_y4(t, m, pkv, k, j, n, r);
            lemma_y4(t, k, j, n, r);
            lemma_keep_has(rows, f, y4(t, k, j, n, r));
            let x = choose|x: int| 0 <= x < kept.len() && kept[x] == y4(t, k, j, n, r);
            assert(vs[x] == t.ps[k][3]);
            assert(ps_typed(t.ps[k]));
        }
    } else {
        if vs.len() > 0 {
            assert(vs[0] == vs[0]);
            let k = choose|k: int| #[trigger] qual(t, m, pkv, k) && vs[0] == (Val::Num { coeff: cost(t, k), scale: 2 });
            assert(qual(t, m, pkv, k));
        }
        assert(vs.len() == 0);
    }
}

/// The inner FROM list evaluates to `inner_rows` (in any context).
pub proof fn lemma_eval_inner_from(db: Database, ctx: Row)
    requires db.tables.len() == 8,
    ensures eval_query(db, ctx, inner_from()) == Ok::<Relation, SqlError>(inner_rows(tabs_of(db))),
{
    let q45 = Query::Product { left: Box::new(Query::Table(4)), right: Box::new(Query::Table(5)) };
    let q456 = Query::Product { left: Box::new(q45), right: Box::new(Query::Table(6)) };
    assert(eval_query(db, ctx, Query::Table(4)) == Ok::<Relation, SqlError>(db.tables[4]));
    assert(eval_query(db, ctx, Query::Table(5)) == Ok::<Relation, SqlError>(db.tables[5]));
    assert(eval_query(db, ctx, Query::Table(6)) == Ok::<Relation, SqlError>(db.tables[6]));
    assert(eval_query(db, ctx, Query::Table(7)) == Ok::<Relation, SqlError>(db.tables[7]));
    assert(eval_query(db, ctx, q45) == Ok::<Relation, SqlError>(product_rows(db.tables[4], db.tables[5])));
    assert(eval_query(db, ctx, q456) == Ok::<Relation, SqlError>(product_rows(product_rows(db.tables[4], db.tables[5]), db.tables[6])));
}

/// The subquery's WHERE keeps the inner rows satisfying `gq` for the outer row's partkey.
pub proof fn lemma_eval_inner_filter(db: Database, ps: Seq<Literal>, x: Row)
    requires
        db.tables.len() == 8,
        tabs_typed(tabs_of(db)),
        params_ok(ps),
        x.len() == 28, x[0] is Int,
    ensures
        eval_query(db, x, Query::Filter { pred: inner_pred(ps), input: Box::new(inner_from()) })
            == Ok::<Relation, SqlError>(keep(inner_rows(tabs_of(db)), gq_f(x[0], prm_of(ps).rname))),
{
    let t = tabs_of(db);
    let m = prm_of(ps);
    let rows = inner_rows(t);
    let f = gq_f(x[0], m.rname);
    lemma_eval_inner_from(db, x);
    let rs = Seq::new(rows.len(), |i: int| eval_pred(db, x + rows[i], inner_pred(ps)));
    let tv = Seq::new(rows.len(), |i: int| truth_of(f(rows[i])));
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Truth, SqlError>(tv[i]) by {
        assert(rows.contains(rows[i]));
        lemma_inner_split(t, rows[i]);
        let (k, j, n, r) = choose|k: int, j: int, n: int, r: int| #[trigger] y4_idx(t, k, j, n, r) && rows[i] == y4(t, k, j, n, r);
        lemma_y4(t, k, j, n, r);
        lemma_inner_pred(db, ps, x, rows[i]);
    }
    lemma_collect_all(rs, tv);
    lemma_collect_pointwise::<Truth>();
    lemma_keep_true_keep(rows, tv, f);
}

/// The subquery's aggregate over the kept inner rows `kept`: one row holding their MIN supply cost.
pub proof fn lemma_eval_min(db: Database, ps: Seq<Literal>, x: Row, kept: Seq<Row>)
    requires
        x.len() == 28,
        forall|i: int| 0 <= i < kept.len() ==> (#[trigger] kept[i]).len() == 19,
        extremum(false, cost_vals(kept)) is Ok,
    ensures ({
        let aggs = seq![Agg::Min(Expr::Col(31))];
        let ars = Seq::new(kept.len(), |i: int| agg_args(db, x + kept[i], aggs));
        &&& collect(ars) == Ok::<Seq<Row>, SqlError>(Seq::new(kept.len(), |i: int| seq![kept[i][3]]))
        &&& agg_row(aggs, Seq::new(kept.len(), |i: int| seq![kept[i][3]]))
            == Ok::<Row, SqlError>(seq![extremum(false, cost_vals(kept))->Ok_0])
    }),
{
    let aggs = seq![Agg::Min(Expr::Col(31))];
    let ars = Seq::new(kept.len(), |i: int| agg_args(db, x + kept[i], aggs));
    let avs = Seq::new(kept.len(), |i: int| seq![kept[i][3]]);
    assert forall|i: int| 0 <= i < ars.len() implies #[trigger] ars[i] == Ok::<Row, SqlError>(avs[i]) by {
        let env = x + kept[i];
        assert(env[31] == kept[i][3]);
        let one = agg_arg_results(db, env, aggs);
        lemma_agg_arg_results_index(db, env, aggs);
        assert(one[0] == Ok::<Val, SqlError>(env[31]));
        lemma_collect_all(one, seq![env[31]]);
    }
    lemma_collect_all(ars, avs);
    assert(column(avs, 0) =~= cost_vals(kept));
    let sv = extremum(false, cost_vals(kept))->Ok_0;
    let vals = Seq::new(aggs.len(), |j: int| agg_value(aggs[j], column(avs, j)));
    assert(vals[0] == min_value(cost_vals(kept)));
    lemma_collect_all(vals, seq![sv]);
}

/// The subquery evaluates to `sub_val` of the outer row's partkey.
pub proof fn lemma_eval_sub(db: Database, ps: Seq<Literal>, x: Row)
    requires
        db.tables.len() == 8,
        tabs_typed(tabs_of(db)),
        params_ok(ps),
        x.len() == 28, x[0] is Int,
    ensures
        eval_expr(db, x, Expr::Subquery(Box::new(sub_q(ps)))) == Ok::<Val, SqlError>(sub_val(tabs_of(db), prm_of(ps), x[0])),
{
    let t = tabs_of(db);
    let m = prm_of(ps);
    let rows = inner_rows(t);
    let f = gq_f(x[0], m.rname);
    let kept = keep(rows, f);
    lemma_eval_inner_filter(db, ps, x);
    lemma_keep_members(rows, f);
    assert forall|i: int| 0 <= i < kept.len() implies (#[trigger] kept[i]).len() == 19 by {
        assert(rows.contains(kept[i]));
        lemma_inner_split(t, kept[i]);
        let (k, j, n, r) = choose|k: int, j: int, n: int, r: int| #[trigger] y4_idx(t, k, j, n, r) && kept[i] == y4(t, k, j, n, r);
        lemma_y4(t, k, j, n, r);
    }
    lemma_sub_val(t, m, x[0]);
    lemma_eval_min(db, ps, x, kept);
    lemma_collect_pointwise::<Row>();
    let sv = sub_val(t, m, x[0]);
    assert(eval_query(db, x, sub_q(ps)) == Ok::<Relation, SqlError>(seq![seq![sv]]));
}

// ------------------------------------------------------------------------------------------------ outer WHERE

/// The outer WHERE in normal form (on rows whose LIKE does not fail).
pub open spec fn q_row(t: Tabs, m: Prm, x: Row) -> bool {
    pre_q(m, x) && x[19] == sub_val(t, m, x[0])
}

pub open spec fn q_f(t: Tabs, m: Prm) -> spec_fn(Row) -> bool {
    |x: Row| q_row(t, m, x)
}

/// No part row's `p_type LIKE $2` fails.
pub open spec fn like_all_ok(t: Tabs, m: Prm) -> bool {
    forall|i: int| 0 <= i < t.p.len() ==> #[trigger] like_res(t.p[i][4], m.pat) is Ok
}

/// The outer FROM list evaluates to `prod5` (in any context).
pub proof fn lemma_eval_from(db: Database, ctx: Row)
    requires db.tables.len() == 8,
    ensures eval_query(db, ctx, outer_from()) == Ok::<Relation, SqlError>(prod5(tabs_of(db))),
{
    let q35 = Query::Product { left: Box::new(Query::Table(3)), right: Box::new(Query::Table(5)) };
    let q354 = Query::Product { left: Box::new(q35), right: Box::new(Query::Table(4)) };
    let q3546 = Query::Product { left: Box::new(q354), right: Box::new(Query::Table(6)) };
    assert(eval_query(db, ctx, Query::Table(3)) == Ok::<Relation, SqlError>(db.tables[3]));
    assert(eval_query(db, ctx, Query::Table(4)) == Ok::<Relation, SqlError>(db.tables[4]));
    assert(eval_query(db, ctx, Query::Table(5)) == Ok::<Relation, SqlError>(db.tables[5]));
    assert(eval_query(db, ctx, Query::Table(6)) == Ok::<Relation, SqlError>(db.tables[6]));
    assert(eval_query(db, ctx, Query::Table(7)) == Ok::<Relation, SqlError>(db.tables[7]));
    assert(eval_query(db, ctx, q35) == Ok::<Relation, SqlError>(product_rows(db.tables[3], db.tables[5])));
    assert(eval_query(db, ctx, q354) == Ok::<Relation, SqlError>(product_rows(product_rows(db.tables[3], db.tables[5]), db.tables[4])));
    assert(eval_query(db, ctx, q3546) == Ok::<Relation, SqlError>(
        product_rows(product_rows(product_rows(db.tables[3], db.tables[5]), db.tables[4]), db.tables[6])));
}

/// The outer WHERE on one row of the FROM list: the row's LIKE error, or a truth `True` exactly under `q_row`.
pub proof fn lemma_outer_row(db: Database, ps: Seq<Literal>, x: Row)
    requires
        db.tables.len() == 8,
        tabs_typed(tabs_of(db)),
        params_ok(ps),
        prod5(tabs_of(db)).contains(x),
    ensures
        xrow_ok(x),
        exists|i: int| 0 <= i < tabs_of(db).p.len() && #[trigger] tabs_of(db).p[i][4] == x[4],
        like_res(x[4], prm_of(ps).pat) matches Err(e) ==> eval_pred(db, x, outer_pred(ps)) == Err::<Truth, SqlError>(e),
        like_res(x[4], prm_of(ps).pat) is Ok ==> eval_pred(db, x, outer_pred(ps)) is Ok
            && (eval_pred(db, x, outer_pred(ps))->Ok_0 == Truth::True) == q_row(tabs_of(db), prm_of(ps), x),
{
    let t = tabs_of(db);
    lemma_prod5_split(t, x);
    let (i, j, k, n, r) = choose|i: int, j: int, k: int, n: int, r: int| #[trigger] x5_idx(t, i, j, k, n, r) && x == x5(t, i, j, k, n, r);
    lemma_x5(t, i, j, k, n, r);
    lemma_eval_sub(db, ps, x);
    lemma_sub_val(t, prm_of(ps), x[0]);
    lemma_outer_pred(db, ps, x, sub_val(t, prm_of(ps), x[0]));
}

/// Without a failing LIKE (or without rows) the outer WHERE keeps exactly the `q_row` rows.
pub proof fn lemma_eval_filter_ok(db: Database, ps: Seq<Literal>)
    requires
        db.tables.len() == 8,
        tabs_typed(tabs_of(db)),
        params_ok(ps),
        like_all_ok(tabs_of(db), prm_of(ps)) || prod5(tabs_of(db)).len() == 0,
    ensures
        eval_query(db, Seq::empty(), q_filter(ps)) == Ok::<Relation, SqlError>(keep(prod5(tabs_of(db)), q_f(tabs_of(db), prm_of(ps)))),
{
    let t = tabs_of(db);
    let m = prm_of(ps);
    let rows = prod5(t);
    lemma_eval_from(db, Seq::empty());
    let rs = Seq::new(rows.len(), |i: int| eval_pred(db, Seq::<Val>::empty() + rows[i], outer_pred(ps)));
    let tv = Seq::new(rows.len(), |i: int| eval_pred(db, rows[i], outer_pred(ps))->Ok_0);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Truth, SqlError>(tv[i]) by {
        assert(Seq::<Val>::empty() + rows[i] =~= rows[i]);
        assert(rows.contains(rows[i]));
        lemma_outer_row(db, ps, rows[i]);
        let i2 = choose|i2: int| 0 <= i2 < t.p.len() && #[trigger] t.p[i2][4] == rows[i][4];
        assert(like_res(t.p[i2][4], m.pat) is Ok);
    }
    lemma_collect_all(rs, tv);
    lemma_collect_pointwise::<Truth>();
    assert forall|i: int| 0 <= i < rows.len() implies (#[trigger] tv[i] is True) == q_f(t, m)(rows[i]) by {
        assert(Seq::<Val>::empty() + rows[i] =~= rows[i]);
        assert(rows.contains(rows[i]));
        lemma_outer_row(db, ps, rows[i]);
        let i2 = choose|i2: int| 0 <= i2 < t.p.len() && #[trigger] t.p[i2][4] == rows[i][4];
        assert(like_res(t.p[i2][4], m.pat) is Ok);
    }
    lemma_keep_true_iff(rows, tv, q_f(t, m));
}

/// Rows of a product of relations with fixed row widths have the summed width.
pub proof fn lemma_product_width(a: Seq<Row>, b: Seq<Row>, wa: nat, wb: nat)
    requires
        forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i]).len() == wa,
        forall|i: int| 0 <= i < b.len() ==> (#[trigger] b[i]).len() == wb,
    ensures forall|f: int| 0 <= f < product_rows(a, b).len() ==> (#[trigger] product_rows(a, b)[f]).len() == wa + wb,
{
    lemma_product_index(a, b);
    assert forall|f: int| 0 <= f < product_rows(a, b).len() implies (#[trigger] product_rows(a, b)[f]).len() == wa + wb by {
        lemma_product_at(a, b, f);
    }
}

/// Every row of the FROM list has 28 values.
pub proof fn lemma_prod5_width(t: Tabs)
    requires tabs_typed(t),
    ensures forall|f: int| 0 <= f < prod5(t).len() ==> (#[trigger] prod5(t)[f]).len() == 28,
{
    let a = product_rows(t.p, t.s);
    let b = product_rows(a, t.ps);
    let c = product_rows(b, t.n);
    assert forall|i: int| 0 <= i < t.p.len() implies (#[trigger] t.p[i]).len() == 9 by { assert(p_typed(t.p[i])); }
    assert forall|i: int| 0 <= i < t.s.len() implies (#[trigger] t.s[i]).len() == 7 by { assert(s_typed(t.s[i])); }
    assert forall|i: int| 0 <= i < t.ps.len() implies (#[trigger] t.ps[i]).len() == 5 by { assert(ps_typed(t.ps[i])); }
    assert forall|i: int| 0 <= i < t.n.len() implies (#[trigger] t.n[i]).len() == 4 by { assert(n_typed(t.n[i])); }
    assert forall|i: int| 0 <= i < t.r.len() implies (#[trigger] t.r[i]).len() == 3 by { assert(r_typed(t.r[i])); }
    lemma_product_width(t.p, t.s, 9, 7);
    lemma_product_width(a, t.ps, 16, 5);
    lemma_product_width(b, t.n, 21, 4);
    lemma_product_width(c, t.r, 25, 3);
}

/// The SELECT list on one row of 28 values.
pub proof fn lemma_project_row(db: Database, x: Row)
    requires x.len() == 28,
    ensures eval_exprs(db, Seq::<Val>::empty() + x, out_exprs()) == Ok::<Row, SqlError>(proj(x, out_cols())),
{
    let es = out_exprs();
    let cols = out_cols();
    assert(Seq::<Val>::empty() + x =~= x);
    let ers = expr_results(db, x, es);
    lemma_expr_results_index(db, x, es);
    assert forall|q: int| 0 <= q < ers.len() implies #[trigger] ers[q] == Ok::<Val, SqlError>(proj(x, cols)[q]) by {
        assert(es[q] == Expr::Col(cols[q]));
    }
    lemma_collect_all(ers, proj(x, cols));
}

/// The body's rows: the SELECT list of the kept rows.
pub proof fn lemma_eval_body_ok(db: Database, ps: Seq<Literal>)
    requires
        db.tables.len() == 8,
        tabs_typed(tabs_of(db)),
        params_ok(ps),
        like_all_ok(tabs_of(db), prm_of(ps)) || prod5(tabs_of(db)).len() == 0,
    ensures
        eval_query(db, Seq::empty(), q_body(ps))
            == Ok::<Relation, SqlError>(proj_all(keep(prod5(tabs_of(db)), q_f(tabs_of(db), prm_of(ps))), out_cols())),
{
    let t = tabs_of(db);
    let m = prm_of(ps);
    let kept = keep(prod5(t), q_f(t, m));
    lemma_eval_filter_ok(db, ps);
    lemma_keep_members(prod5(t), q_f(t, m));
    lemma_prod5_width(t);
    let rs = Seq::new(kept.len(), |i: int| eval_exprs(db, Seq::<Val>::empty() + kept[i], out_exprs()));
    let vs = proj_all(kept, out_cols());
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(vs[i]) by {
        assert(prod5(t).contains(kept[i]));
        let f = choose|f: int| 0 <= f < prod5(t).len() && prod5(t)[f] == kept[i];
        lemma_project_row(db, kept[i]);
    }
    lemma_collect_all(rs, vs);
    lemma_collect_pointwise::<Row>();
}

/// The FROM list in part-major form: `part x (supplier x partsupp x nation x region)`.
pub open spec fn rest_rows(t: Tabs) -> Seq<Row> {
    product_rows(product_rows(product_rows(t.s, t.ps), t.n), t.r)
}

pub proof fn lemma_part_major(t: Tabs)
    ensures
        prod5(t) == product_rows(t.p, rest_rows(t)),
        prod5(t).len() == t.p.len() * rest_rows(t).len(),
        (t.s.len() > 0 && t.ps.len() > 0 && t.n.len() > 0 && t.r.len() > 0) ==> rest_rows(t).len() > 0,
{
    lemma_product_assoc(t.p, t.s, t.ps);
    lemma_product_assoc(t.p, product_rows(t.s, t.ps), t.n);
    lemma_product_assoc(t.p, product_rows(product_rows(t.s, t.ps), t.n), t.r);
    lemma_product_index(t.p, rest_rows(t));
    lemma_product_index(t.s, t.ps);
    lemma_product_index(product_rows(t.s, t.ps), t.n);
    lemma_product_index(product_rows(product_rows(t.s, t.ps), t.n), t.r);
    if t.s.len() > 0 && t.ps.len() > 0 && t.n.len() > 0 && t.r.len() > 0 {
        assert(t.s.len() * t.ps.len() > 0) by (nonlinear_arith) requires t.s.len() > 0, t.ps.len() > 0;
        assert(t.s.len() * t.ps.len() * t.n.len() > 0) by (nonlinear_arith) requires t.s.len() * t.ps.len() > 0, t.n.len() > 0;
        assert(t.s.len() * t.ps.len() * t.n.len() * t.r.len() > 0) by (nonlinear_arith)
            requires t.s.len() * t.ps.len() * t.n.len() > 0, t.r.len() > 0;
    }
}

/// Row `f` of the FROM list holds part row `f / |rest|`'s p_type.
pub proof fn lemma_part_major_row(t: Tabs, f: int)
    requires tabs_typed(t), 0 <= f < prod5(t).len(),
    ensures
        rest_rows(t).len() > 0,
        0 <= f / (rest_rows(t).len() as int) < t.p.len(),
        prod5(t)[f][4] == t.p[f / (rest_rows(t).len() as int)][4],
{
    lemma_part_major(t);
    lemma_product_at(t.p, rest_rows(t), f);
    assert(p_typed(t.p[f / (rest_rows(t).len() as int)]));
}

/// The outer WHERE of row `f` of the FROM list, through its part row.
proof fn lemma_err_row(db: Database, ps: Seq<Literal>, f: int)
    requires
        db.tables.len() == 8,
        tabs_typed(tabs_of(db)),
        params_ok(ps),
        0 <= f < prod5(tabs_of(db)).len(),
    ensures ({
        let t = tabs_of(db);
        let a = f / (rest_rows(t).len() as int);
        let x = Seq::<Val>::empty() + prod5(t)[f];
        &&& 0 <= a < t.p.len()
        &&& like_res(t.p[a][4], prm_of(ps).pat) matches Err(e) ==> eval_pred(db, x, outer_pred(ps)) == Err::<Truth, SqlError>(e)
        &&& like_res(t.p[a][4], prm_of(ps).pat) is Ok ==> eval_pred(db, x, outer_pred(ps)) is Ok
    }),
{
    let t = tabs_of(db);
    let x = prod5(t)[f];
    assert(Seq::<Val>::empty() + x =~= x);
    lemma_part_major_row(t, f);
    assert(prod5(t).contains(x));
    lemma_outer_row(db, ps, x);
}

/// A failing LIKE on part row `i0` (and on no earlier part row) makes the WHERE fail with its error, when every
/// other table has rows.
pub proof fn lemma_eval_filter_err(db: Database, ps: Seq<Literal>, i0: int, e: SqlError)
    requires
        db.tables.len() == 8,
        tabs_typed(tabs_of(db)),
        params_ok(ps),
        0 <= i0 < tabs_of(db).p.len(),
        like_res(tabs_of(db).p[i0][4], prm_of(ps).pat) == Err::<Val, SqlError>(e),
        forall|i: int| 0 <= i < i0 ==> #[trigger] like_res(tabs_of(db).p[i][4], prm_of(ps).pat) is Ok,
        tabs_of(db).s.len() > 0, tabs_of(db).ps.len() > 0, tabs_of(db).n.len() > 0, tabs_of(db).r.len() > 0,
    ensures
        eval_query(db, Seq::empty(), q_filter(ps)) == Err::<Relation, SqlError>(e),
        eval_query(db, Seq::empty(), q_body(ps)) == Err::<Relation, SqlError>(e),
{
    let t = tabs_of(db);
    let rows = prod5(t);
    lemma_eval_from(db, Seq::empty());
    lemma_part_major(t);
    let nr = rest_rows(t).len() as int;
    let f0 = i0 * nr;
    assert(0 <= f0 < rows.len()) by (nonlinear_arith) requires 0 <= i0 < t.p.len(), nr > 0, rows.len() == t.p.len() * nr, f0 == i0 * nr;
    assert(f0 / nr == i0) by {
        vstd::arithmetic::div_mod::lemma_div_multiples_vanish(i0, nr);
        assert(nr * i0 == f0) by (nonlinear_arith) requires f0 == i0 * nr;
    }
    let rs = Seq::new(rows.len(), |f: int| eval_pred(db, Seq::<Val>::empty() + rows[f], outer_pred(ps)));
    assert forall|f: int| 0 <= f < f0 implies #[trigger] rs[f] is Ok by {
        lemma_err_row(db, ps, f);
        vstd::arithmetic::div_mod::lemma_div_is_ordered(f, f0, nr);
        assert(f / nr <= i0);
        if f / nr == i0 {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(f, nr);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(f, nr);
            assert(nr * (f / nr) == f0) by (nonlinear_arith) requires f / nr == i0, f0 == i0 * nr;
        }
    }
    lemma_err_row(db, ps, f0);
    lemma_collect_first_err(rs, f0);
    lemma_collect_pointwise::<Truth>();
}

// ------------------------------------------------------------------------------------------------ normal form

/// The outer WHERE on `x5(i, j, k, n, r)` in index form.
pub proof fn lemma_q_row_x5(t: Tabs, m: Prm, i: int, j: int, k: int, n: int, r: int)
    requires tabs_typed(t), x5_idx(t, i, j, k, n, r),
    ensures
        q_row(t, m, x5(t, i, j, k, n, r)) == (part_sel(t, m, i) && t.ps[k][0] == t.p[i][0] && smatch(t, k, j)
            && nmatch(t, j, n) && rmatch(t, m, n, r) && is_min(t, m, t.p[i][0], k)),
{
    let x = x5(t, i, j, k, n, r);
    lemma_x5(t, i, j, k, n, r);
    let pkv = t.p[i][0];
    lemma_sub_val(t, m, pkv);
    assert(ps_typed(t.ps[k]));
    let pre = part_sel(t, m, i) && t.ps[k][0] == pkv && smatch(t, k, j) && nmatch(t, j, n) && rmatch(t, m, n, r);
    assert(pre_q(m, x) == pre);
    if pre {
        assert(qual(t, m, pkv, k));
        let sv = sub_val(t, m, pkv);
        let k0 = choose|k0: int| #[trigger] qual(t, m, pkv, k0) && sv == (Val::Num { coeff: cost(t, k0), scale: 2 });
        assert(x[19] == (Val::Num { coeff: cost(t, k), scale: 2 }));
        if x[19] == sv {
            assert forall|k2: int| #[trigger] qual(t, m, pkv, k2) implies cost(t, k) <= cost(t, k2) by {}
            assert(is_min(t, m, pkv, k));
        }
        if is_min(t, m, pkv, k) {
            assert(cost(t, k) <= cost(t, k0));
            assert(sv->coeff <= cost(t, k));
        }
    }
}

/// The region row of nation `n` named `$3` (unique by the primary key).
pub open spec fn reg_of(t: Tabs, m: Prm, n: int) -> int {
    choose|r: int| rmatch(t, m, n, r)
}

/// The FROM row of a candidate.
pub open spec fn full_row(t: Tabs, m: Prm, c: Cand) -> Row {
    x5(t, c.part as int, c.supp as int, c.ps as int, c.nation as int, reg_of(t, m, c.nation as int))
}

/// The output row of a candidate.
pub open spec fn out_row_spec(t: Tabs, m: Prm, c: Cand) -> Row {
    proj(full_row(t, m, c), out_cols())
}

/// Its values: s_acctbal, s_name, n_name, p_partkey, p_mfgr, s_address, s_phone, s_comment.
pub proof fn lemma_out_row(t: Tabs, m: Prm, c: Cand)
    requires tabs_typed(t), cand_ok(t, m, c),
    ensures out_row_spec(t, m, c) == seq![
        t.s[c.supp as int][5], t.s[c.supp as int][1], t.n[c.nation as int][1], t.p[c.part as int][0],
        t.p[c.part as int][2], t.s[c.supp as int][2], t.s[c.supp as int][4], t.s[c.supp as int][6]],
{
    let r = reg_of(t, m, c.nation as int);
    assert(rmatch(t, m, c.nation as int, r));
    lemma_x5(t, c.part as int, c.supp as int, c.ps as int, c.nation as int, r);
    assert(out_row_spec(t, m, c) =~= seq![
        t.s[c.supp as int][5], t.s[c.supp as int][1], t.n[c.nation as int][1], t.p[c.part as int][0],
        t.p[c.part as int][2], t.s[c.supp as int][2], t.s[c.supp as int][4], t.s[c.supp as int][6]]);
}

/// The FROM list has no duplicate rows.
pub proof fn lemma_prod5_nodup(t: Tabs)
    requires tabs_typed(t), tabs_nodup(t),
    ensures prod5(t).no_duplicates(),
{
    let a = product_rows(t.p, t.s);
    let b = product_rows(a, t.ps);
    let c = product_rows(b, t.n);
    assert forall|i: int| 0 <= i < t.p.len() implies (#[trigger] t.p[i]).len() == 9 by { assert(p_typed(t.p[i])); }
    assert forall|i: int| 0 <= i < t.s.len() implies (#[trigger] t.s[i]).len() == 7 by { assert(s_typed(t.s[i])); }
    assert forall|i: int| 0 <= i < t.ps.len() implies (#[trigger] t.ps[i]).len() == 5 by { assert(ps_typed(t.ps[i])); }
    assert forall|i: int| 0 <= i < t.n.len() implies (#[trigger] t.n[i]).len() == 4 by { assert(n_typed(t.n[i])); }
    lemma_product_width(t.p, t.s, 9, 7);
    lemma_product_width(a, t.ps, 16, 5);
    lemma_product_width(b, t.n, 21, 4);
    lemma_product_nodup(t.p, t.s, 9);
    lemma_product_nodup(a, t.ps, 16);
    lemma_product_nodup(b, t.n, 21);
    lemma_product_nodup(c, t.r, 25);
}

/// Distinct candidates have distinct FROM rows.
proof fn lemma_full_distinct(t: Tabs, m: Prm, c1: Cand, c2: Cand)
    requires tabs_typed(t), tabs_nodup(t), cand_ok(t, m, c1), cand_ok(t, m, c2), pair_ne(c1, c2),
    ensures full_row(t, m, c1) != full_row(t, m, c2),
{
    let (r1, r2) = (reg_of(t, m, c1.nation as int), reg_of(t, m, c2.nation as int));
    assert(rmatch(t, m, c1.nation as int, r1) && rmatch(t, m, c2.nation as int, r2));
    let (x1, x2) = (full_row(t, m, c1), full_row(t, m, c2));
    lemma_x5(t, c1.part as int, c1.supp as int, c1.ps as int, c1.nation as int, r1);
    lemma_x5(t, c2.part as int, c2.supp as int, c2.ps as int, c2.nation as int, r2);
    assert(p_typed(t.p[c1.part as int]) && p_typed(t.p[c2.part as int]));
    assert(s_typed(t.s[c1.supp as int]) && s_typed(t.s[c2.supp as int]));
    assert(ps_typed(t.ps[c1.ps as int]) && ps_typed(t.ps[c2.ps as int]));
    if x1 == x2 {
        if c1.part != c2.part {
            assert(x1.subrange(0, 9) =~= t.p[c1.part as int]);
            assert(x2.subrange(0, 9) =~= t.p[c2.part as int]);
        } else {
            assert(x1.subrange(16, 21) =~= t.ps[c1.ps as int]);
            assert(x2.subrange(16, 21) =~= t.ps[c2.ps as int]);
        }
    }
}

/// The body's bag is the bag of the candidates' output rows.
pub proof fn lemma_body_multiset(t: Tabs, m: Prm, cs: Seq<Cand>)
    requires tabs_typed(t), tabs_nodup(t), keys_unique(t), cands_ok(t, m, cs),
    ensures
        proj_all(keep(prod5(t), q_f(t, m)), out_cols()).to_multiset()
            == cs.map_values(|c: Cand| out_row_spec(t, m, c)).to_multiset(),
{
    let kept = keep(prod5(t), q_f(t, m));
    let fr = cs.map_values(|c: Cand| full_row(t, m, c));
    lemma_prod5_nodup(t);
    lemma_keep_nodup(prod5(t), q_f(t, m));
    lemma_keep_members(prod5(t), q_f(t, m));
    assert(fr.no_duplicates()) by {
        assert forall|x: int, y: int| 0 <= x < fr.len() && 0 <= y < fr.len() && x != y implies fr[x] != fr[y] by {
            assert(cand_ok(t, m, cs[x]) && cand_ok(t, m, cs[y]));
            assert(pair_ne(cs[x], cs[y]));
            lemma_full_distinct(t, m, cs[x], cs[y]);
        }
    }
    assert forall|z: Row| kept.contains(z) implies fr.contains(z) by {
        let w = choose|w: int| 0 <= w < kept.len() && kept[w] == z;
        assert(prod5(t).contains(z) && q_row(t, m, z));
        lemma_prod5_split(t, z);
        let (i, j, k, n, r) = choose|i: int, j: int, k: int, n: int, r: int| #[trigger] x5_idx(t, i, j, k, n, r) && z == x5(t, i, j, k, n, r);
        lemma_q_row_x5(t, m, i, j, k, n, r);
        assert(has_pair(cs, i, k));
        let x = choose|x: int| 0 <= x < cs.len() && #[trigger] cs[x].part == i && cs[x].ps == k;
        let c = cs[x];
        assert(cand_ok(t, m, c));
        assert(t.s[c.supp as int][0] == t.s[j][0]);
        assert(c.supp == j);
        assert(t.n[c.nation as int][0] == t.n[n][0]);
        assert(c.nation == n);
        let rr = reg_of(t, m, n);
        assert(rmatch(t, m, n, rr));
        assert(t.r[rr][0] == t.r[r][0]);
        assert(rr == r);
        assert(fr[x] == z);
    }
    assert forall|z: Row| fr.contains(z) implies kept.contains(z) by {
        let x = choose|x: int| 0 <= x < fr.len() && fr[x] == z;
        let c = cs[x];
        assert(cand_ok(t, m, c));
        let rr = reg_of(t, m, c.nation as int);
        assert(rmatch(t, m, c.nation as int, rr));
        assert(qual(t, m, t.p[c.part as int][0], c.ps as int));
        lemma_prod5_has(t, c.part as int, c.supp as int, c.ps as int, c.nation as int, rr);
        lemma_q_row_x5(t, m, c.part as int, c.supp as int, c.ps as int, c.nation as int, rr);
        lemma_keep_has(prod5(t), q_f(t, m), z);
    }
    crate::link::query::lemma_nodup_same_multiset(kept, fr);
    crate::link::query::lemma_map_multiset(kept, fr, |x: Row| proj(x, out_cols()));
    assert(fr.map_values(|x: Row| proj(x, out_cols())) =~= cs.map_values(|c: Cand| out_row_spec(t, m, c)));
    assert(kept.map_values(|x: Row| proj(x, out_cols())) =~= proj_all(kept, out_cols()));
}

} // verus!
