//! Executable `spec::aggs::avg`: the exact sum with the SUM evaluators of `exec::relational::aggregate` (the SUM
//! capacity condition: absolute mass at most `i128::MAX`, `sum_mass_fits`; integer sums of a vector always meet
//! it), then `exec::fns::div::num_div_exec` by the count of non-NULL values. `Capacity` exactly outside
//! `fits_avg_value`.
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::numeric::*;
use crate::spec::relation::*;
use crate::spec::aggs::avg::*;
use crate::exec::value::*;
use crate::exec::domain::*;
use crate::exec::fns::div::*;
use crate::exec::relational::domain::*;
use crate::exec::relational::aggregate::*;

verus! {

/// Executable domain of `avg_value`: the SUM mass condition (`sum_mass_fits`, every kind) and the division
/// (`spec::aggs::avg::fits_avg`). Used by `exec::relational::domain::fits_agg_value`.
pub open spec fn fits_avg_value(kind: NumKind, vs: Seq<Val>) -> bool {
    &&& all_of_kind(kind, vs) ==> sum_mass_fits(kind, vs)
    &&& fits_avg(kind, vs)
}

/// `spec::aggs::avg::avg_value`: NULL for no non-NULL values, otherwise the sum divided by their count as
/// numeric division (so int4/int8 AVG is numeric).
pub fn exec_avg(kind: NumKind, vs: &Vec<EVal>) -> (r: Outcome<EVal>)
    ensures
        match r {
            Ok(res) => fits_avg_value(kind, view_row(vs@)) && view_result(res) == avg_value(kind, view_row(vs@))
                && (res matches Ok(v) ==> val_ts_ok(v@)),
            Err(_) => !fits_avg_value(kind, view_row(vs@)),
        },
{
    let ghost g = view_row(vs@);
    if !all_of_kind_exec(kind, vs) {
        return Ok(Err(SqlError::TypeError));
    }
    // The exact sum as a decimal `c·10^-s` (integer sums have scale 0).
    let (c, s) = match kind {
        NumKind::Numeric => match num_sum_exec(vs) {
            Ok(p) => p,
            Err(cap) => return Err(cap),
        },
        _ => (int_sum_exec(vs), 0u32),
    };
    assert((c as int, s as nat) == avg_sum(kind, g));
    let n = count_non_null_exec(vs);
    if n == 0 {
        return Ok(Ok(EVal::Null));
    }
    proof {
        lemma_num_in_range_small(c as int, s as nat);
    }
    num_div_exec(c, s, n as i128, 0)
}

/// `spec::aggs::avg::avg_ty`: AVG of int4, int8 or numeric is nullable numeric at display scale 1000.
pub fn avg_ty_exec(kind: NumKind, t: ColTy) -> (r: Option<ColTy>)
    ensures r == avg_ty(kind, t),
{
    let ok = match (kind, t.ty) {
        (NumKind::Int4, ScalarTy::Int4) => true,
        (NumKind::Int8, ScalarTy::Int8) => true,
        (NumKind::Numeric, ScalarTy::Numeric { .. }) => true,
        _ => false,
    };
    if ok { Some(ColTy { ty: ScalarTy::Numeric { scale: 1000 }, nullable: true }) } else { None }
}

} // verus!
