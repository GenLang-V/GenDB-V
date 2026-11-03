//! The capacity case of the general path: when the AVG of some part key `k` (over at least one lineitem row) is
//! outside the executable division domain (`num_div_fits`), the statement is outside the capacity domain. The
//! WHERE condition evaluates the subquery for every row of `lineitem x part` (AND is strict), and for a joined row
//! of a lineitem row of key `k` with the part row the subquery's aggregate leaves its domain (`lemma_cap`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::numeric::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::fns::div::*;
use crate::spec::aggs::avg::*;
use crate::link::join::*;
use crate::link::query::{proj, proj_all};
use crate::link::expr::{ival, tval};
use crate::link::capacity::{aggs_ok_inside, lemma_aggregate_capacity, lemma_first_input, lemma_filter_capacity};
use crate::link::source::lemma_proj_all_index;
use crate::exec::relational::domain::{fits_query, fits_pred, fits_agg_value};
use crate::exec::domain::fits_expr;
use crate::exec::aggs::avg::fits_avg_value;
use crate::query::*;
use super::vals::*;
use super::typed::*;
use super::sqlsub::*;
use super::sqlmain::*;

verus! {

/// A positive count of key `k` has a witness row.
proof fn lemma_cnt_witness(rows: Seq<Row>, k: int) -> (i: int)
    requires sum_of(rows, t1(k)) > 0,
    ensures 0 <= i < rows.len(), is_key(rows[i], k),
{
    if forall|i: int| 0 <= i < rows.len() ==> !is_key(#[trigger] rows[i], k) {
        assert forall|i: int| 0 <= i < rows.len() implies t1(k)(#[trigger] rows[i]) == 0 by {}
        lemma_sum_of_zero(rows, t1(k));
        assert(false);
        0
    } else {
        choose|i: int| 0 <= i < rows.len() && is_key(#[trigger] rows[i], k)
    }
}

/// The subquery under `x` (p_partkey `k`) is outside its domain when its AVG is.
proof fn lemma_sub_cap(db: Database, x: Row, k: int)
    requires
        tables_ok(db),
        x.len() == 25,
        x[16] == Val::Int(k),
        qcnt(ys_of(db), k) >= 1,
        !num_div_fits(qsum(ys_of(db), k), 2, qcnt(ys_of(db), k), 0),
    ensures !fits_expr(db, x, sub_expr()),
{
    let ks = keep(db.tables[0], lkey(k));
    lemma_sub_filter(db, x, k);
    lemma_sub_sums(db, k);
    assert forall|i: int| 0 <= i < ks.len() implies (#[trigger] ks[i]).len() == 16 && num2(ks[i][4]) by {
        assert(num2(ks[i][4]) && ks[i].len() == 16);
    }
    lemma_sub_args(db, x, ks);
    assert forall|i: int| 0 <= i < ks.len() implies #[trigger] agg_args(db, x + ks[i], seq![avg_agg()]) == Ok::<Row, SqlError>(qty_args(ks)[i]) by {
        lemma_sub_arg_row(db, x, ks, i);
    }
    lemma_qty_sum(ks);
    let args = qty_args(ks);
    let vs = column(args, 0);
    assert(vs == qty_vals(ks));
    assert(num_sum(vs) == (qsum(ys_of(db), k), 2nat));
    assert(!fits_avg(NumKind::Numeric, vs));
    assert(!fits_agg_value(avg_agg(), vs));
    assert(aggs_ok_inside(seq![avg_agg()], args)) by {
        assert forall|j: int| 0 <= j < seq![avg_agg()].len() && #[trigger] fits_agg_value(seq![avg_agg()][j], column(args, j))
            implies agg_value(seq![avg_agg()][j], column(args, j)) is Ok by {
            assert(j == 0);
        }
    }
    lemma_aggregate_capacity(db, x, seq![avg_agg()], Box::new(sub_filter()), ks, args, 0);
    lemma_first_input(db, x, sub_q());
}

/// A conjunction whose left side evaluates without error and whose right side is outside its domain.
proof fn lemma_and_cap(db: Database, x: Row, a: Pred, b: Pred)
    requires eval_pred(db, x, a) is Ok, !fits_pred(db, x, b),
    ensures !fits_pred(db, x, Pred::And(Box::new(a), Box::new(b))),
{
}

/// A comparison of a column with an expression outside its domain.
proof fn lemma_cmp_cap(db: Database, x: Row, op: CmpOp, i: nat, e: Expr)
    requires i < x.len(), !fits_expr(db, x, e),
    ensures !fits_pred(db, x, Pred::Cmp { op, a: Expr::Col(i), b: e }),
{
    assert(eval_expr(db, x, Expr::Col(i)) is Ok);
    assert(fits_expr(db, x, Expr::Col(i)));
}

/// The first three conjuncts evaluate without error.
proof fn lemma_a123_ok(db: Database, ps: Seq<Literal>, x: Row, l: Row, p: Row)
    requires param_domain(ps), lrow_ok(l), prow_ok(p), x == l + p,
    ensures eval_pred(db, x, Pred::And(Box::new(Pred::And(Box::new(pred_pk()), Box::new(pred_brand(ps)))), Box::new(pred_cont(ps)))) is Ok,
{
    assert(x[16] == p[0] && x[1] == l[1] && x[19] == p[3] && x[22] == p[6]);
    lemma_int_eq(db, x, 16, 1, ival(p[0]), ival(l[1]));
    lemma_text_eq(db, x, 19, ps[0], tval(p[3]), ptext(ps[0]));
    lemma_text_eq(db, x, 22, ps[1], tval(p[6]), ptext(ps[1]));
    let a12 = Pred::And(Box::new(pred_pk()), Box::new(pred_brand(ps)));
    assert(eval_pred(db, x, pred_pk()) is Ok);
    assert(eval_pred(db, x, pred_brand(ps)) is Ok);
    assert(eval_pred(db, x, a12) is Ok);
    assert(eval_pred(db, x, pred_cont(ps)) is Ok);
}

/// The WHERE condition under such a joined row is outside its domain.
proof fn lemma_pred_cap(db: Database, ps: Seq<Literal>, l: Row, p: Row)
    requires
        tables_ok(db),
        param_domain(ps),
        lrow_ok(l),
        prow_ok(p),
        qcnt(ys_of(db), ival(p[0])) >= 1,
        !num_div_fits(qsum(ys_of(db), ival(p[0])), 2, qcnt(ys_of(db), ival(p[0])), 0),
    ensures !fits_pred(db, l + p, pred_q(ps)),
{
    let x = l + p;
    let k = ival(p[0]);
    assert(x.len() == 25);
    assert(x[16] == p[0]);
    lemma_sub_cap(db, x, k);
    lemma_cmp_cap(db, x, CmpOp::Lt, 4, sub_expr());
    lemma_a123_ok(db, ps, x, l, p);
    lemma_and_cap(db, x, Pred::And(Box::new(Pred::And(Box::new(pred_pk()), Box::new(pred_brand(ps)))), Box::new(pred_cont(ps))), pred_lt());
}

/// Some part row `j` whose key `k` has lineitem rows and an AVG outside the executable division domain: the
/// statement is outside the capacity domain.
pub proof fn lemma_cap(db: Database, ps: Seq<Literal>, j: int)
    requires
        tables_ok(db),
        db.tables[0].len() <= 0xffff_ffff_ffff_ffff,
        param_domain(ps),
        0 <= j < db.tables[3].len(),
        qcnt(ys_of(db), ival(db.tables[3][j][0])) >= 1,
        !num_div_fits(qsum(ys_of(db), ival(db.tables[3][j][0])), 2, qcnt(ys_of(db), ival(db.tables[3][j][0])), 0),
    ensures !fits_query(db, Seq::empty(), query_spec_at(ps).body),
{
    let (l, p) = (db.tables[0], db.tables[3]);
    let k = ival(p[j][0]);
    let ys = ys_of(db);
    lemma_value_rows(db);
    let i = lemma_cnt_witness(ys, k);
    assert(ys[i] == proj(l[i], lcols()));
    assert(lrow_ok(l[i]) && prow_ok(p[j]));
    lemma_pred_cap(db, ps, l[i], p[j]);
    let pr = prod_of(db);
    let np = p.len() as int;
    lemma_product_index(l, p);
    let m = i * np + j;
    assert(0 <= m < pr.len()) by (nonlinear_arith)
        requires m == i * np + j, 0 <= i < l.len(), 0 <= j < np, pr.len() == l.len() * np;
    assert(pr[m] == l[i] + p[j]);
    let ctx = Seq::<Val>::empty();
    assert(ctx + pr[m] =~= pr[m]);
    assert(eval_query(db, ctx, Query::Table(0)) == Ok::<Relation, SqlError>(l));
    assert(eval_query(db, ctx, Query::Table(3)) == Ok::<Relation, SqlError>(p));
    assert(eval_query(db, ctx, product_q()) == Ok::<Relation, SqlError>(pr));
    assert forall|q: int| 0 <= q < pr.len() && #[trigger] fits_pred(db, ctx + pr[q], pred_q(ps))
        implies eval_pred(db, ctx + pr[q], pred_q(ps)) is Ok by {
        lemma_prod_at(db, q);
        let (lq, pq) = (l[q / np], p[q % np]);
        assert(ctx + pr[q] =~= lq + pq);
        lemma_row_pred(db, ps, lq, pq);
    }
    lemma_filter_capacity(db, ctx, pred_q(ps), Box::new(product_q()), pr, m);
    lemma_first_input(db, ctx, agg_q(ps));
    lemma_ast(ps);
    lemma_first_input(db, ctx, query_spec_at(ps).body);
}

} // verus!
