//! The ship window from the parameter (`param_window`): `$1` as a stored day, and the first day not before the
//! timestamp `$1 + INTERVAL '1' MONTH` (computed by the verified timestamp arithmetic of `exec::datetime`, so a
//! failing step is that step's SQL error). The scan tests the window with one unsigned comparison per row
//! (`Window::base`, `Window::span`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::lit_val;
use crate::spec::datetime::*;
use crate::gendb_params::Params;
use crate::query::param_domain;
use crate::exec::datetime::*;
use crate::agent::line::Win;
use crate::agent::joined::{bounds_ok, month_end_val};

verus! {

/// Day number (since 2000-01-01) of the date parameter `$1`.
pub open spec fn param_day(ps: Seq<Literal>) -> int {
    date_from_civil(ps[0]->Date_y, ps[0]->Date_m, ps[0]->Date_d)
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
        &&& lit_val(p) == Ok::<Val, SqlError>(Val::Date(param_day(ps)))
        &&& -730119 <= param_day(ps) <= 2921939
    }),
{
    assert(date_from_civil(1, 1, 1) == -730119) by (compute);
    assert(date_from_civil(9999, 12, 31) == 2921939) by (compute);
    let p = ps[0];
    assert(days_in_month(p->Date_y, p->Date_m) <= 31);
}

/// The ship window in stored days, `lo <= l_shipdate < hi`, with the precomputed fields of the one-comparison test
/// `(d + 2^31) - base < span` (wrapping, on `u32`), and the timestamp `$1 + INTERVAL '1' MONTH`.
#[derive(Clone, Copy)]
pub struct Window {
    pub lo: i32,
    pub hi: i32,
    pub base: u32,
    pub span: u32,
    pub t1: i64,
}

/// The window as the normal form's `Win`.
pub open spec fn win_of(x: Window) -> Win { Win { lo: x.lo as int, hi: x.hi as int } }

/// The precomputed test fields agree with the window.
pub open spec fn window_wf(x: Window) -> bool {
    &&& x.base as int == x.lo as int + 0x8000_0000
    &&& x.span as int == if x.hi > x.lo { x.hi as int - x.lo as int } else { 0 }
}

/// A valid date converts to a valid timestamp; adding the interval gives a valid timestamp.
proof fn lemma_ts_valid(pd: int, t0: int, t1: int)
    ensures
        date_to_ts(pd) == Ok::<int, SqlError>(t0) ==> ts_valid(t0),
        ts_add_interval(t0, 1, 0, 0) == Ok::<int, SqlError>(t1) ==> ts_valid(t1),
{
    hide(ts_add_months);
}

/// The window of the parameter, or the SQL error of `$1 + INTERVAL '1' MONTH`.
pub fn param_window(params: &Params) -> (r: Result<Window, SqlError>)
    requires param_domain(params@),
    ensures
        lit_val(params@[0]) == Ok::<Val, SqlError>(Val::Date(param_day(params@))),
        r matches Ok(x) ==> window_wf(x) && bounds_ok(params@, win_of(x), x.t1 as int),
        r matches Err(e) ==> month_end_val(param_day(params@)) == Err::<Val, SqlError>(e),
{
    let ghost ps = params@;
    proof {
        lemma_param(ps);
    }
    let pd = date_from_civil_exec(params.p0.y as i64, params.p0.m as i64, params.p0.d as i64);
    let t0 = match date_to_ts_exec(pd as i32) {
        Ok(t) => t,
        Err(e) => return Err(e),
    };
    proof {
        lemma_ts_valid(pd as int, t0 as int, 0);
    }
    let t1 = match ts_add_interval_exec(t0, 1, 0, 0) {
        Ok(t) => t,
        Err(e) => return Err(e),
    };
    proof {
        lemma_ts_valid(pd as int, t0 as int, t1 as int);
        assert(month_end_val(pd as int) == Ok::<Val, SqlError>(Val::Ts(t1 as int)));
    }
    // The first day whose midnight is not before `t1`: `phi - 1 = floor((t1 - 1) / USECS_PER_DAY)`.
    let (q, rem) = floor_divmod(t1 - 1, 86_400_000_000i64);
    let phi = q + 1;
    proof {
        assert(-2451547 <= phi <= 106751992) by (nonlinear_arith)
            requires q * 86_400_000_000 + rem == t1 - 1, 0 <= rem < 86_400_000_000,
                -211813488000000000 <= t1 < 9223371331200000000, phi == q + 1;
    }
    let lo = (pd + 10957) as i32;
    let hi = (phi + 10957) as i32;
    let base = (lo as i64 + 0x8000_0000i64) as u32;
    let span: u32 = if hi > lo { (hi as i64 - lo as i64) as u32 } else { 0 };
    let x = Window { lo, hi, base, span, t1 };
    proof {
        let w = win_of(x);
        assert(w.lo - 10957 == pd as int);
        assert(w.hi - 10957 == phi as int);
        assert((phi - 1) * usecs_per_day() < t1 as int) by (nonlinear_arith)
            requires q * 86_400_000_000 + rem == t1 - 1, 0 <= rem < 86_400_000_000, phi == q + 1,
                usecs_per_day() == 86_400_000_000;
        assert(t1 as int <= phi * usecs_per_day()) by (nonlinear_arith)
            requires q * 86_400_000_000 + rem == t1 - 1, 0 <= rem < 86_400_000_000, phi == q + 1,
                usecs_per_day() == 86_400_000_000;
    }
    Ok(x)
}

/// The one-comparison window test of a stored day.
pub open spec fn in_window(x: Window, d: i32) -> bool { x.lo <= d && d < x.hi }

/// `(d + 2^31) - base < span` (wrapping) is the window test.
#[inline(always)]
pub fn day_in(x: &Window, d: i32) -> (b: bool)
    requires window_wf(*x),
    ensures b == in_window(*x, d),
    no_unwind
{
    let biased = (d as i64 + 0x8000_0000i64) as u32;
    biased.wrapping_sub(x.base) < x.span
}

} // verus!
