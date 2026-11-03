//! `EXTRACT(YEAR | MONTH | DAY FROM x)` for `x` a date or timestamp (`Expr::Call` with `ExtractYear`,
//! `ExtractMonth`, `ExtractDay`, one argument). PostgreSQL 18 `extract_date` /
//! `extract_timestamp`: the result is `numeric` with scale 0 (since PostgreSQL 14); NULL gives NULL. The civil
//! date is the existing proleptic Gregorian conversion `spec::datetime::civil_from_date` (astronomical years);
//! a timestamp's date is its day `floor(t / USECS_PER_DAY)` (PostgreSQL `timestamp2tm`), so the time of day does
//! not matter. YEAR has no year 0: an astronomical year `y <= 0` is reported as `y - 1` (1 BC is -1), which a
//! PostgreSQL 18 fixture confirmed on both types. Other fields are
//! refused by the frontend.
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::datetime::*;

verus! {

/// The requested field of a civil date `(y, m, d)`.
pub open spec fn extract_field(f: ScalarFn, ymd: (int, int, int)) -> int {
    match f {
        ScalarFn::ExtractYear => if ymd.0 > 0 { ymd.0 } else { ymd.0 - 1 },
        ScalarFn::ExtractMonth => ymd.1,
        _ => ymd.2,
    }
}

/// `date` or `timestamp` -> numeric scale 0.
pub open spec fn type_extract(f: ScalarFn, args: Seq<ColTy>) -> Option<ColTy> {
    if args.len() == 1 && (args[0].ty is Date || args[0].ty is Timestamp) {
        Some(ColTy { ty: ScalarTy::Numeric { scale: 0 }, nullable: args[0].nullable })
    } else {
        None
    }
}

/// Value of `EXTRACT` (strict: NULL gives NULL).
pub open spec fn apply_extract(f: ScalarFn, args: Seq<Val>) -> Result<Val, SqlError> {
    if args.len() != 1 {
        Err(SqlError::TypeError)
    } else {
        match args[0] {
            Val::Null => Ok(Val::Null),
            Val::Date(d) => Ok(Val::Num { coeff: extract_field(f, civil_from_date(d)), scale: 0 }),
            Val::Ts(t) => Ok(Val::Num { coeff: extract_field(f, civil_from_date(t / usecs_per_day())), scale: 0 }),
            _ => Err(SqlError::TypeError),
        }
    }
}

/// EXTRACT never needs `Capacity` (dates are `i32` days; timestamps are valid, `exec::domain::val_ts_ok`).
pub open spec fn fits_extract(f: ScalarFn, args: Seq<Val>) -> bool {
    true
}

} // verus!
