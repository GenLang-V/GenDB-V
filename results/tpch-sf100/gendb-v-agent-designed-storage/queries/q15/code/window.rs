//! The date window of the binding: `$1` in days (`lo_of`) and `$1 + INTERVAL '3' MONTH` as a timestamp
//! (`hi_value`, PostgreSQL `timestamp_pl_interval`, which may fail with 22008); `l_shipdate < t` for a date and a
//! timestamp `t` is `l_shipdate <= hi` with `hi` the last day before `t` (`hi_ok`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::eval::lit_val;
use crate::spec::datetime::*;
use crate::query::param_typed;
use crate::gendb_params::Params;
use crate::exec::datetime::{date_from_civil_exec, date_to_ts_exec, ts_add_interval_exec, floor_divmod};

verus! {

/// `$1` as a day number.
pub open spec fn lo_of(ps: Seq<Literal>) -> int {
    match ps[0] {
        Literal::Date { y, m, d } => date_from_civil(y, m, d),
        _ => 0,
    }
}

/// The value of `$1 + 3 months` from `$1`'s day number.
pub open spec fn hi_value(lo: int) -> Result<int, SqlError> {
    match date_to_ts(lo) {
        Err(e) => Err(e),
        Ok(t) => ts_add_interval(t, 3, 0, 0),
    }
}

/// `hi` is the last day before the timestamp `$1 + 3 months`.
pub open spec fn hi_ok(lo: int, hi: int) -> bool {
    &&& hi_value(lo) is Ok
    &&& hi == (hi_value(lo)->Ok_0 - 1) / usecs_per_day()
}

/// `$1` is a valid date literal: it evaluates to its day number.
pub proof fn lemma_lit(ps: Seq<Literal>)
    requires param_typed(ps),
    ensures
        ps[0] is Date,
        lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(lo_of(ps))),
        date_valid(lo_of(ps)),
{
}

/// The date window: `$1` in days, and the last day before `$1 + 3 months` (or the error computing that timestamp).
pub fn date_window(params: &Params) -> (r: (i64, Result<i64, SqlError>))
    requires param_typed(params@),
    ensures
        r.0 as int == lo_of(params@),
        match r.1 {
            Ok(h) => hi_ok(lo_of(params@), h as int),
            Err(e) => hi_value(lo_of(params@)) == Err::<int, SqlError>(e),
        },
{
    let ghost ps = params@;
    proof {
        lemma_lit(ps);
        assert(days_in_month(params.p0.y as int, params.p0.m as int) <= 31);
    }
    let lo = date_from_civil_exec(params.p0.y as i64, params.p0.m as i64, params.p0.d as i64);
    let t0 = match date_to_ts_exec(lo as i32) {
        Ok(t) => t,
        Err(e) => return (lo, Err(e)),
    };
    let t1 = match ts_add_interval_exec(t0, 3, 0, 0) {
        Ok(t) => t,
        Err(e) => return (lo, Err(e)),
    };
    let (q, _) = floor_divmod(t1 - 1, 86_400_000_000i64);
    (lo, Ok(q))
}

} // verus!
