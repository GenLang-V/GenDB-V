//! The WHERE bounds from the parameters (`param_bounds`): `$1` as a stored-date bound, the first day not before
//! the timestamp `$1 + INTERVAL '1' YEAR` (computed by the verified timestamp arithmetic of `exec::datetime`, so a
//! failing step is that step's SQL error), `$2 -/+ 0.01` and `100 * $3` as scale-2 coefficients.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::{lit_val, eval_expr};
use crate::spec::datetime::*;
use crate::gendb_params::Params;
use crate::query::param_domain;
use crate::exec::datetime::*;
use crate::agent::normal::*;
use crate::agent::body::*;
use crate::agent::kernel::*;
use crate::agent::outcome::lemma_param;

verus! {

/// Day number (since 2000-01-01) of the date parameter `$1`.
pub open spec fn param_day(ps: Seq<Literal>) -> int {
    date_from_civil(ps[0]->Date_y, ps[0]->Date_m, ps[0]->Date_d)
}

/// The bounds, or the SQL error of `$1 + INTERVAL '1' YEAR`.
pub enum ParamBounds {
    Bounds { b: Bounds, t1: i64 },
    Error(SqlError),
}

/// A valid date converts to a valid timestamp; adding the interval gives a valid timestamp.
pub proof fn lemma_ts_valid(pd: int, t0: int, t1: int)
    ensures
        date_to_ts(pd) == Ok::<int, SqlError>(t0) ==> ts_valid(t0),
        ts_add_interval(t0, 12, 0, 0) == Ok::<int, SqlError>(t1) ==> ts_valid(t1),
{
    hide(ts_add_months);
}

/// Computes the WHERE bounds of the parameters.
pub fn param_bounds(params: &Params) -> (r: ParamBounds)
    requires param_domain(params@),
    ensures
        lit_val(params@[0]) == Ok::<Val, SqlError>(Val::Date(param_day(params@))),
        r matches ParamBounds::Bounds { b, t1 } ==> bounds_ok(params@, qb_of(b), t1 as int) && bounds_wf(b),
        r matches ParamBounds::Error(e) ==> year_end_val(param_day(params@)) == Err::<Val, SqlError>(e),
{
    let ghost ps = params@;
    proof {
        lemma_param(ps);
    }
    let pd = date_from_civil_exec(params.p0.y as i64, params.p0.m as i64, params.p0.d as i64);
    let t0 = match date_to_ts_exec(pd as i32) {
        Ok(t) => t,
        Err(e) => return ParamBounds::Error(e),
    };
    proof {
        lemma_ts_valid(pd as int, t0 as int, 0);
    }
    let t1 = match ts_add_interval_exec(t0, 12, 0, 0) {
        Ok(t) => t,
        Err(e) => return ParamBounds::Error(e),
    };
    proof {
        lemma_ts_valid(pd as int, t0 as int, t1 as int);
        assert(year_end_val(pd as int) == Ok::<Val, SqlError>(Val::Ts(t1 as int)));
    }
    // The first day whose midnight is not before `t1`: `phi - 1 = floor((t1 - 1) / USECS_PER_DAY)`.
    let (q, rem) = floor_divmod(t1 - 1, 86_400_000_000i64);
    let phi = q + 1;
    proof {
        assert(-2451547 <= phi <= 106751992) by (nonlinear_arith)
            requires q * 86_400_000_000 + rem == t1 - 1, 0 <= rem < 86_400_000_000,
                -211813488000000000 <= t1 < 9223371331200000000, phi == q + 1;
    }
    let b = make_bounds((pd + 10957) as i32, (phi + 10957) as i32, params.p1 - 1, params.p1 + 1, params.p2 as i128 * 100);
    proof {
        let qb = qb_of(b);
        assert(qb.plo == pd as int);
        assert(qb.phi == phi as int);
        assert forall|db: Database, env: Row| #[trigger] eval_expr(db, env, e_year_end(ps[0])) == Ok::<Val, SqlError>(Val::Ts(t1 as int)) by {
            lemma_year_end_eval(db, env, ps[0], pd as int);
        }
        assert(year_end_is(ps[0], t1 as int)) by {
            reveal(year_end_is);
        }
        assert((qb.phi - 1) * usecs_per_day() < t1 as int);
        assert(t1 as int <= qb.phi * usecs_per_day());
    }
    ParamBounds::Bounds { b, t1 }
}

} // verus!
