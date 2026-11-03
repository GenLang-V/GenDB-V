//! The shipdate window from the parameter (`param_bounds`): `$1` as a stored-date bound and the first day not before
//! the timestamp `$1 + INTERVAL '3' MONTH`, computed by the verified timestamp arithmetic of `exec::datetime` (so a
//! failing step is that step's SQL error, `q_end_val`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::{lit_val, eval_expr};
use crate::spec::scalar::{cast, CastOp};
use crate::spec::datetime::*;
use crate::gendb_params::Params;
use crate::query::param_domain;
use crate::exec::datetime::*;
use crate::agent::normal::*;

verus! {

/// The window `[lo, hi)` on stored days (days since 1970-01-01).
#[derive(Clone, Copy)]
pub struct DayWindow {
    pub lo: i32,
    pub hi: i32,
}

/// The window in the normal form's days (since 2000-01-01).
pub open spec fn qb_of(w: DayWindow) -> QBounds {
    QBounds { plo: w.lo as int - 10957, phi: w.hi as int - 10957 }
}

/// Day number (since 2000-01-01) of the date parameter `$1`.
pub open spec fn param_day(ps: Seq<Literal>) -> int {
    date_from_civil(ps[0]->Date_y, ps[0]->Date_m, ps[0]->Date_d)
}

/// `$1 + INTERVAL '3' MONTH` at the day `pd`: the timestamp of `date_to_ts` and `ts_add_interval`, or their error.
pub open spec fn q_end_val(pd: int) -> Result<Val, SqlError> {
    match date_to_ts(pd) {
        Err(e) => Err(e),
        Ok(t0) => match ts_add_interval(t0, 3, 0, 0) {
            Ok(t) => Ok(Val::Ts(t)),
            Err(e) => Err(e),
        },
    }
}

/// The window, or the SQL error of `$1 + INTERVAL '3' MONTH`.
pub enum ParamBounds {
    Window { w: DayWindow, t1: i64 },
    Error(SqlError),
}

/// The parameter literal `$1` is a valid date with its day number inside the declared range.
pub proof fn lemma_param(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures ({
        let p = ps[0];
        &&& ps.len() == 1
        &&& p is Date
        &&& 1 <= p->Date_m <= 12
        &&& 1 <= p->Date_d <= 31
        &&& lit_val(p) == Ok::<Val, SqlError>(Val::Date(date_from_civil(p->Date_y, p->Date_m, p->Date_d)))
        &&& -730119 <= date_from_civil(p->Date_y, p->Date_m, p->Date_d) <= 2921939
    }),
{
    assert(date_from_civil(1, 1, 1) == -730119) by (compute);
    assert(date_from_civil(9999, 12, 31) == 2921939) by (compute);
    let p = ps[0];
    assert(days_in_month(p->Date_y, p->Date_m) <= 31);
}

/// The evaluator's value of `$1 + INTERVAL '3' MONTH` (it reads no column).
pub proof fn lemma_q_end_eval(db: Database, env: Row, p0: Literal, pd: int)
    requires lit_val(p0) == Ok::<Val, SqlError>(Val::Date(pd)),
    ensures eval_expr(db, env, e_q_end(p0)) == q_end_val(pd),
{
    hide(lit_val);
    hide(date_to_ts);
    hide(ts_add_interval);
    let cst = Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(Expr::Lit(p0)) };
    assert(eval_expr(db, env, Expr::Lit(p0)) == Ok::<Val, SqlError>(Val::Date(pd)));
    assert(eval_expr(db, env, cst) == cast(CastOp::DateToTimestamp, Val::Date(pd)));
}

/// A valid date converts to a valid timestamp; adding the interval gives a valid timestamp.
pub proof fn lemma_ts_valid(pd: int, t0: int, t1: int)
    ensures
        date_to_ts(pd) == Ok::<int, SqlError>(t0) ==> ts_valid(t0),
        ts_add_interval(t0, 3, 0, 0) == Ok::<int, SqlError>(t1) ==> ts_valid(t1),
{
    hide(ts_add_months);
}

/// Computes the window of the parameter.
pub fn param_bounds(params: &Params) -> (r: ParamBounds)
    requires param_domain(params@),
    ensures
        lit_val(params@[0]) == Ok::<Val, SqlError>(Val::Date(param_day(params@))),
        r matches ParamBounds::Window { w, t1 } ==> bounds_ok(params@, qb_of(w), t1 as int),
        r matches ParamBounds::Error(e) ==> q_end_val(param_day(params@)) == Err::<Val, SqlError>(e),
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
    let t1 = match ts_add_interval_exec(t0, 3, 0, 0) {
        Ok(t) => t,
        Err(e) => return ParamBounds::Error(e),
    };
    proof {
        lemma_ts_valid(pd as int, t0 as int, t1 as int);
        assert(q_end_val(pd as int) == Ok::<Val, SqlError>(Val::Ts(t1 as int)));
    }
    // The first day whose midnight is not before `t1`: `phi - 1 = floor((t1 - 1) / USECS_PER_DAY)`.
    let (q, rem) = floor_divmod(t1 - 1, 86_400_000_000i64);
    let phi = q + 1;
    proof {
        assert(-2451547 <= phi <= 106751992) by (nonlinear_arith)
            requires q * 86_400_000_000 + rem == t1 - 1, 0 <= rem < 86_400_000_000,
                -211813488000000000 <= t1 < 9223371331200000000, phi == q + 1;
    }
    let w = DayWindow { lo: (pd + 10957) as i32, hi: (phi + 10957) as i32 };
    proof {
        let qb = qb_of(w);
        assert(qb.plo == pd as int);
        assert(qb.phi == phi as int);
        assert forall|db: Database, env: Row| #[trigger] eval_expr(db, env, e_q_end(ps[0])) == Ok::<Val, SqlError>(Val::Ts(t1 as int)) by {
            lemma_q_end_eval(db, env, ps[0], pd as int);
        }
        assert(q_end_is(ps[0], t1 as int)) by {
            reveal(q_end_is);
        }
        assert((qb.phi - 1) * usecs_per_day() < t1 as int);
        assert(t1 as int <= qb.phi * usecs_per_day());
    }
    ParamBounds::Window { w, t1 }
}

} // verus!
