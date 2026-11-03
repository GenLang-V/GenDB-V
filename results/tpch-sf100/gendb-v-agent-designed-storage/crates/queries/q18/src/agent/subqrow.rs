//! One lineitem row of the IN subquery's GROUP BY input (`subq::lemma_sub_prep`): its key `l_orderkey` and its
//! SUM argument `l_quantity` under a 33-column outer environment. A module of its own so that its solver context
//! holds only what this step needs.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::IntKind;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::{collect, keep_true, group_rows};
use crate::bridge::collect::{lemma_collect_all, lemma_collect_pointwise};
use crate::query::param_domain;
use crate::link::query::*;
use crate::link::join::{sum_of, lemma_acc_sum_of, count_term, sum_term};
use crate::link::source::lemma_proj_all_index;
use crate::exec::relational::domain::{filter_results, project_results, group_input_results, group_results,
    lemma_eval_filter, lemma_eval_project, lemma_eval_group_by};
use crate::link::expr::{ival, i128_max, lemma_expr_col, lemma_compare_num, lemma_compare_int, lemma_pred_cmp,
    lemma_align_same, lemma_align_by};
use super::common::isum::*;
use super::model::*;
use super::qspec::*;
use super::rels::*;
use super::subq::{sub_aggs, sub_g, lemma_sub_args, lemma_one_col};

verus! {

/// One lineitem row of `lemma_sub_prep`.
pub proof fn lemma_sub_prep_at(db: Database, m: M, ctx: Row, i: int)
    requires super::subq::sub_ok(db, m), ctx.len() == 33, 0 <= i < db.tables[0].len(),
    ensures ({
        let t0 = db.tables[0];
        let xs = lrel(db);
        group_input_results(db, ctx, t0, seq![Expr::Col(33)], sub_aggs())[i]
            == Ok::<(Row, Row), SqlError>(((sub_g().key)(xs[i]), arg_vals(sub_g(), xs[i])))
    }),
{
    let t0 = db.tables[0];
    let g = sub_g();
    let xs = lrel(db);
    lemma_widths(db);
    lemma_proj_all_index(t0, lcols());
    let j = lemma_lrow_at(db, m, i);
    let env = ctx + t0[i];
    assert(t0[i].len() == 16);
    assert(env[33] == t0[i][0] && env[37] == t0[i][4]);
    lemma_one_col(db, env, 33);
    lemma_expr_col(db, env, 37);
    lemma_sub_args(db, env, t0[i][4]);
    assert(xs[i] == lrow(m, j));
    assert((g.key)(xs[i]) =~= seq![t0[i][0]]);
    assert(arg_vals(g, xs[i]) =~= seq![t0[i][4]]);
}

} // verus!
