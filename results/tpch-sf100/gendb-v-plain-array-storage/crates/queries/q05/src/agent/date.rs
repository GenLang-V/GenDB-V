//! The year of `$2` as a half-open range of stored order dates (days since 1970-01-01): `[dlo, dhi)` holds exactly
//! the dates `od` with `$2 <= od < $2 + INTERVAL '1' YEAR` (`date_in`), or the SQL error of computing the
//! timestamp bound (`hi_res`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::datetime::*;
use crate::gendb_abi::CivilDate;
use crate::exec::datetime::{date_from_civil_exec, date_to_ts_exec, ts_add_interval_exec, floor_divmod};
use crate::agent::sem_pred::*;

verus! {

/// `d * u < t` exactly when `d` is below the ceiling of `t / u` (`t = q * u + r`, `0 <= r < u`).
pub proof fn lemma_ceil_div(d: int, t: int, q: int, r: int, u: int)
    requires u > 0, t == q * u + r, 0 <= r < u,
    ensures (d * u < t) == (d < if r == 0 { q } else { q + 1 }),
{
    if r == 0 {
        if d < q {
            assert(d * u <= (q - 1) * u) by (nonlinear_arith) requires d <= q - 1, u > 0;
            assert((q - 1) * u == q * u - u) by (nonlinear_arith);
        } else {
            assert(d * u >= q * u) by (nonlinear_arith) requires d >= q, u > 0;
        }
    } else {
        if d <= q {
            assert(d * u <= q * u) by (nonlinear_arith) requires d <= q, u > 0;
        } else {
            assert(d * u >= (q + 1) * u) by (nonlinear_arith) requires d >= q + 1, u > 0;
            assert((q + 1) * u == q * u + u) by (nonlinear_arith);
        }
    }
}

/// The stored-date range of the year starting at `$2` (the day `pd`), or the timestamp bound's error.
pub fn date_bounds(p: &CivilDate, Ghost(pd): Ghost<int>) -> (r: Result<(i32, i32), SqlError>)
    requires
        pd == date_from_civil(p.y as int, p.m as int, p.d as int),
        1 <= p.m <= 12, 1 <= p.d <= 31,
        -730119 <= pd <= 2921939,
    ensures
        r matches Ok((lo, hi)) ==> hi_res(pd) is Ok
            && forall|od: i32| #[trigger] date_in(od, pd, hi_res(pd)->Ok_0) == (lo <= od < hi),
        r matches Err(e) ==> hi_res(pd) == Err::<int, SqlError>(e),
{
    let pdx = date_from_civil_exec(p.y as i64, p.m as i64, p.d as i64);
    let t0 = match date_to_ts_exec(pdx as i32) {
        Ok(t) => t,
        Err(e) => return Err(e),
    };
    let t1 = match ts_add_interval_exec(t0, 12, 0, 0) {
        Ok(t) => t,
        Err(e) => return Err(e),
    };
    assert(hi_res(pd) == Ok::<int, SqlError>(t1 as int));
    assert(ts_valid(t1 as int)) by {
        let r1 = if 12int != 0 { ts_add_months(t0 as int, 12) } else { Ok::<int, SqlError>(t0 as int) };
        assert(ts_add_interval(t0 as int, 12, 0, 0) == match r1 {
            Err(e) => Err::<int, SqlError>(e),
            Ok(x) => ts_result(x + 0),
        });
    }
    let (q, rem) = floor_divmod(t1, 86_400_000_000);
    assert(-211813488000000000 <= t1 < 9223371331200000000);
    assert(-2451545 <= q <= 106751991) by (nonlinear_arith)
        requires q * 86_400_000_000 + rem == t1, 0 <= rem < 86_400_000_000, -211813488000000000 <= t1 < 9223371331200000000;
    let hi_day = if rem == 0 { q } else { q + 1 };
    let dlo = (pdx + 10957) as i32;
    let dhi = (hi_day + 10957) as i32;
    proof {
        let t = t1 as int;
        assert forall|od: i32| #[trigger] date_in(od, pd, t) == (dlo <= od < dhi) by {
            let dd = od as int - 10957;
            lemma_ceil_div(dd, t, q as int, rem as int, usecs_per_day());
            assert(date_in(od, pd, t) == (dd >= pd && dd * usecs_per_day() < t));
        }
    }
    Ok((dlo, dhi))
}

} // verus!
