//! Executable `spec::fns::extract`: `EXTRACT(YEAR | MONTH | DAY FROM x)` of a date or timestamp, on the verified
//! civil conversion `exec::datetime::civil_from_date_exec`. Never `Capacity`.
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::fns::extract::*;
use crate::exec::value::*;
use crate::exec::domain::*;
use crate::exec::datetime::*;

verus! {

/// `spec::fns::extract::extract_field`: the requested field of a civil date (YEAR has no year 0).
fn extract_field_exec(f: ScalarFn, ymd: (i64, i64, i64)) -> (r: i128)
    requires -0x1000_0000 <= ymd.0 <= 0x1000_0000,
    ensures r as int == extract_field(f, (ymd.0 as int, ymd.1 as int, ymd.2 as int)),
{
    match f {
        ScalarFn::ExtractYear => if ymd.0 > 0 { ymd.0 as i128 } else { ymd.0 as i128 - 1 },
        ScalarFn::ExtractMonth => ymd.1 as i128,
        _ => ymd.2 as i128,
    }
}

/// `spec::fns::extract::apply_extract`: the field as numeric scale 0; a timestamp's date is its day.
pub fn exec_extract(f: ScalarFn, args: &Vec<EVal>) -> (r: Outcome<EVal>)
    requires row_ts_ok(view_row(args@)),
    ensures
        match r {
            Ok(res) => fits_extract(f, view_row(args@)) && view_result(res) == apply_extract(f, view_row(args@))
                && (res matches Ok(v) ==> val_ts_ok(v@)),
            Err(_) => !fits_extract(f, view_row(args@)),
        },
{
    if args.len() != 1 {
        return Ok(Err(SqlError::TypeError));
    }
    let ghost vs = view_row(args@);
    assert(vs[0] == args@[0]@);
    match &args[0] {
        EVal::Null => Ok(Ok(EVal::Null)),
        EVal::Date(d) => {
            let ymd = civil_from_date_exec(*d as i64);
            Ok(Ok(EVal::Num { coeff: extract_field_exec(f, ymd), scale: 0 }))
        },
        EVal::Ts(t) => {
            assert(val_ts_ok(vs[0]));
            let (day, _time_of_day) = ts_day_and_time_exec(*t);
            let ymd = civil_from_date_exec(day);
            Ok(Ok(EVal::Num { coeff: extract_field_exec(f, ymd), scale: 0 }))
        },
        _ => Ok(Err(SqlError::TypeError)),
    }
}

/// `spec::fns::extract::type_extract`: a date or timestamp gives numeric scale 0.
pub fn type_extract_exec(f: ScalarFn, args: &Vec<ColTy>) -> (r: Option<ColTy>)
    ensures r == type_extract(f, args@),
{
    if args.len() == 1 {
        match args[0].ty {
            ScalarTy::Date | ScalarTy::Timestamp =>
                Some(ColTy { ty: ScalarTy::Numeric { scale: 0 }, nullable: args[0].nullable }),
            _ => None,
        }
    } else {
        None
    }
}

} // verus!
