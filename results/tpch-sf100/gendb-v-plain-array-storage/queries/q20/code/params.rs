//! The parameters of the statement as executable values: the date window `[lo, hi)` of the lineitem subquery in
//! stored days (since 1970-01-01), the `LIKE` pattern `$1` and the nation name `$3`.
//!
//! `$2 + INTERVAL '1' YEAR` never fails inside the declared domain (`lemma_year_end_ok`): a date of years 1..9999
//! moved by twelve months stays far inside PostgreSQL's timestamp range. The bounds are crude (they do not use that
//! `civil_from_date` inverts `date_from_civil`), only linear facts of the calendar formulas.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::scalar::*;
use crate::spec::datetime::*;
use crate::spec::numeric::sign;
use crate::gendb_params::Params;
use crate::query::param_domain;
use crate::exec::datetime::*;
use crate::link::expr::{lemma_compare_date, lemma_pred_cmp, lemma_pred_and};
use crate::agent::ast::*;

verus! {

/// Microseconds per day (`usecs_per_day()` as a literal, so products stay linear for the solver).
pub open spec fn upd() -> int { 86_400_000_000 }

/// Day number (since 2000-01-01) of `$2`.
pub open spec fn param_day(ps: Seq<Literal>) -> int {
    date_from_civil(ps[1]->Date_y, ps[1]->Date_m, ps[1]->Date_d)
}

/// The pattern `$1` and the nation name `$3` (their bytes).
pub open spec fn pat_of(ps: Seq<Literal>) -> Seq<u8> { ps[0]->Text_0 }
pub open spec fn nat_of(ps: Seq<Literal>) -> Seq<u8> { ps[2]->Text_0 }

/// The parameter literal `$2` is a valid date with its day number inside the declared range; `$1`, `$3` are text.
pub proof fn lemma_param(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures ({
        let p = ps[1];
        &&& p is Date
        &&& 1 <= p->Date_m <= 12
        &&& 1 <= p->Date_d <= 31
        &&& lit_val(p) == Ok::<Val, SqlError>(Val::Date(param_day(ps)))
        &&& -730119 <= param_day(ps) <= 2921939
        &&& ps[0] == Literal::Text(pat_of(ps))
        &&& ps[2] == Literal::Text(nat_of(ps))
    }),
{
    assert(date_from_civil(1, 1, 1) == -730119) by (compute);
    assert(date_from_civil(9999, 12, 31) == 2921939) by (compute);
    let p = ps[1];
    assert(days_in_month(p->Date_y, p->Date_m) <= 31);
}

// ------------------------------------------------------------------------------------------ calendar bounds

/// Crude bounds of the civil date of a day count `z` (since 1970-01-01) of years 1..9999: the year in `[0, 10001]`,
/// the day of month in `[1, 31]`, the month within a few thousand.
proof fn lemma_civil_bounds(z: int)
    requires -719162 <= z <= 2932896,
    ensures ({
        let c = civil_from_unix_days(z);
        &&& 0 <= c.0 <= 10001
        &&& -5000 <= c.1 <= 5000
        &&& 1 <= c.2 <= 31
    }),
{
    let z1 = z + 719468;
    let era = z1 / 146097;
    let doe = z1 - era * 146097;
    assert(0 <= era <= 24);
    assert(0 <= doe < 146097);
    let n = doe - doe / 1460 + doe / 36524 - doe / 146096;
    assert(0 <= n <= 146100);
    let yoe = n / 365;
    assert(0 <= yoe <= 400);
    let y = yoe + era * 400;
    assert(0 <= y <= 10000);
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    assert(-146200 <= doy <= 146097);
    let mp = (5 * doy + 2) / 153;
    assert(153 * mp <= 5 * doy + 2 < 153 * mp + 153);
    assert(-4800 <= mp <= 4800);
    let q = (153 * mp + 2) / 5;
    assert(5 * q <= 153 * mp + 2 < 5 * q + 5);
    let d = doy - q + 1;
    assert(1 <= d <= 31);
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    assert(civil_from_unix_days(z) == (if m <= 2 { y + 1 } else { y }, m, d));
}

/// Crude bounds of the day number of a civil date of years in `[-1000, 11000]`.
proof fn lemma_from_civil_bounds(y: int, m: int, d: int)
    requires -1000 <= y <= 11000, 1 <= m <= 12, 1 <= d <= 31,
    ensures -1200000 <= date_from_civil(y, m, d) <= 3300000,
{
    let y1 = if m <= 2 { y - 1 } else { y };
    let era = y1 / 400;
    let yoe = y1 - era * 400;
    assert(-3 <= era <= 27);
    assert(0 <= yoe < 400);
    let mp = if m > 2 { m - 3 } else { m + 9 };
    let doy = (153 * mp + 2) / 5 + d - 1;
    assert(0 <= doy <= 400);
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    assert(0 <= doe <= 146500);
}

/// `$2 + INTERVAL '1' YEAR` of a day number of years 1..9999 succeeds: `date_to_ts` and the month step stay in the
/// timestamp range.
pub proof fn lemma_year_end_ok(pd: int)
    requires -730119 <= pd <= 2921939,
    ensures
        date_to_ts(pd) == Ok::<int, SqlError>(pd * upd()),
        ts_add_interval(pd * upd(), 12, 0, 0) is Ok,
{
    let u = upd();
    assert(usecs_per_day() == u);
    let t = pd * u;
    assert(ts_valid(t));
    // the day and the time of day of a midnight timestamp
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(t, u, pd, 0);
    assert(t / u == pd && t % u == 0);
    let ymd = civil_from_date(pd);
    lemma_civil_bounds(pd + 10957);
    let total = ymd.0 * 12 + (ymd.1 - 1) + 12;
    let y2 = total / 12;
    let m2 = total % 12 + 1;
    assert(-1000 <= y2 <= 11000);
    assert(1 <= m2 <= 12);
    let dim = days_in_month(y2, m2);
    assert(28 <= dim <= 31);
    let d2 = if ymd.2 <= dim { ymd.2 } else { dim };
    lemma_from_civil_bounds(y2, m2, d2);
    let nd = date_from_civil(y2, m2, d2);
    assert(ts_valid(nd * u + 0));
    assert(ts_add_months(t, 12) == ts_result(nd * u + 0));
    assert(ts_add_months(t, 12) is Ok);
}

// ------------------------------------------------------------------------------------------ the date window

/// `$2 + INTERVAL '1' YEAR` evaluates to the timestamp `t1` (it reads no column).
#[verifier::opaque]
pub open spec fn year_end_is(p1: Literal, t1: int) -> bool {
    forall|db: Database, env: Row| #[trigger] eval_expr(db, env, year_end(p1)) == Ok::<Val, SqlError>(Val::Ts(t1))
}

/// The stored-day window `[lo, hi)` is the one of `$2`: `lo` is `$2` (stored days), and `hi` the first stored day
/// whose midnight is not before the timestamp `$2 + INTERVAL '1' YEAR`.
pub open spec fn win_ok(ps: Seq<Literal>, lo: int, hi: int) -> bool {
    &&& lit_val(ps[1]) == Ok::<Val, SqlError>(Val::Date(lo - 10957))
    &&& exists|t1: int| #[trigger] year_end_is(ps[1], t1) && (hi - 10957 - 1) * upd() < t1 && t1 <= (hi - 10957) * upd()
}

/// The evaluator's value of `$2 + INTERVAL '1' YEAR`.
proof fn lemma_year_end_eval(db: Database, env: Row, p1: Literal, pd: int)
    requires lit_val(p1) == Ok::<Val, SqlError>(Val::Date(pd)),
    ensures eval_expr(db, env, year_end(p1)) == match date_to_ts(pd) {
        Err(e) => Err(e),
        Ok(t0) => match ts_add_interval(t0, 12, 0, 0) {
            Ok(t) => Ok(Val::Ts(t)),
            Err(e) => Err(e),
        },
    },
{
    hide(lit_val);
    hide(date_to_ts);
    hide(ts_add_interval);
    let cst = Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(Expr::Lit(p1)) };
    assert(eval_expr(db, env, Expr::Lit(p1)) == Ok::<Val, SqlError>(Val::Date(pd)));
    assert(eval_expr(db, env, cst) == cast(CastOp::DateToTimestamp, Val::Date(pd)));
}

/// The window's two conditions on a lineitem shipdate `x` (stored days) at position 26 of the environment.
pub proof fn lemma_li_date_preds(db: Database, env: Row, ps: Seq<Literal>, lo: int, hi: int, x: int)
    requires win_ok(ps, lo, hi), env.len() > 26, env[26] == Val::Date(x - 10957),
    ensures
        eval_pred(db, env, li_ge_pred(ps[1])) == Ok::<Truth, SqlError>(truth_of(lo <= x)),
        eval_pred(db, env, li_lt_pred(ps[1])) == Ok::<Truth, SqlError>(truth_of(x < hi)),
{
    let u = upd();
    let d = x - 10957;
    let t1 = choose|t1: int| #[trigger] year_end_is(ps[1], t1) && (hi - 10957 - 1) * upd() < t1 && t1 <= (hi - 10957) * upd();
    assert(eval_expr(db, env, Expr::Col(26)) == Ok::<Val, SqlError>(env[26]));
    assert(eval_expr(db, env, Expr::Lit(ps[1])) == Ok::<Val, SqlError>(Val::Date(lo - 10957)));
    lemma_compare_date(d, lo - 10957);
    lemma_pred_cmp(db, env, CmpOp::Ge, Expr::Col(26), Expr::Lit(ps[1]), env[26], Val::Date(lo - 10957), d, lo - 10957);
    assert(eval_expr(db, env, year_end(ps[1])) == Ok::<Val, SqlError>(Val::Ts(t1))) by {
        reveal(year_end_is);
    }
    assert(usecs_per_day() == u);
    assert(compare(Val::Date(d), Val::Ts(t1)) == Some(sign(d * u - t1)));
    lemma_pred_cmp(db, env, CmpOp::Lt, Expr::Col(26), year_end(ps[1]), env[26], Val::Ts(t1), d * u, t1);
    // `d * u < t1` exactly when `d < hi - 10957`: `t1` lies in `((hi - 10957 - 1) * u, (hi - 10957) * u]`.
    assert((d * u < t1) == (x < hi)) by (nonlinear_arith)
        requires u == 86_400_000_000, (hi - 10957 - 1) * u < t1, t1 <= (hi - 10957) * u, d == x - 10957;
}

/// Computes the stored-day window `[lo, hi)` of `$2`.
pub fn date_window(params: &Params) -> (r: (i32, i32))
    requires param_domain(params@),
    ensures win_ok(params@, r.0 as int, r.1 as int),
{
    let ghost ps = params@;
    proof {
        lemma_param(ps);
    }
    let pd = date_from_civil_exec(params.p1.y as i64, params.p1.m as i64, params.p1.d as i64);
    proof {
        lemma_year_end_ok(pd as int);
    }
    let t0 = match date_to_ts_exec(pd as i32) {
        Ok(t) => t,
        Err(_) => {
            proof { assert(false); }
            0
        },
    };
    assert(t0 as int == pd * upd());
    assert(ts_valid(t0 as int));
    let t1 = match ts_add_interval_exec(t0, 12, 0, 0) {
        Ok(t) => t,
        Err(_) => {
            proof { assert(false); }
            0
        },
    };
    proof {
        assert(ts_add_interval(t0 as int, 12, 0, 0) == Ok::<int, SqlError>(t1 as int));
    }
    // The first day whose midnight is not before `t1`: `phi - 1 = floor((t1 - 1) / USECS_PER_DAY)`.
    let (q, rem) = floor_divmod(t1 - 1, 86_400_000_000i64);
    let phi = q + 1;
    proof {
        assert(ts_valid(t1 as int)) by {
            assert(ts_add_interval(t0 as int, 12, 0, 0) == Ok::<int, SqlError>(t1 as int));
        }
        assert(-2451547 <= phi <= 106751992) by (nonlinear_arith)
            requires q * 86_400_000_000 + rem == t1 - 1, 0 <= rem < 86_400_000_000,
                -211813488000000000 <= t1 < 9223371331200000000, phi == q + 1;
        assert((phi - 1) * upd() < t1 && t1 <= phi * upd()) by (nonlinear_arith)
            requires q * 86_400_000_000 + rem == t1 - 1, 0 <= rem < 86_400_000_000, phi == q + 1;
    }
    let lo = (pd + 10957) as i32;
    let hi = (phi + 10957) as i32;
    proof {
        assert forall|db: Database, env: Row| #[trigger] eval_expr(db, env, year_end(ps[1])) == Ok::<Val, SqlError>(Val::Ts(t1 as int)) by {
            lemma_year_end_eval(db, env, ps[1], pd as int);
        }
        assert(year_end_is(ps[1], t1 as int)) by {
            reveal(year_end_is);
        }
        assert((hi - 10957 - 1) * upd() < t1 && t1 <= (hi - 10957) * upd());
    }
    (lo, hi)
}

} // verus!
