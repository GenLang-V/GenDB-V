//! Executable scalar functions (`spec::fns`): `exec_fn` (value, with `Capacity` exactly outside `fits_fn`) and
//! `type_fn_exec` (the checker's typing rule). Both dispatch on the function family to one module per feature,
//! mirroring `spec::fns`: `div` (integer and numeric division), `like`, `substring`, `extract`, `pad`
//! (`bpchar` blank padding). Each feature module has `exec_<feature>` (value) and `type_<feature>_exec` (type).
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::ast::*;
use crate::spec::fns::*;
use crate::exec::value::*;
use crate::exec::domain::*;

pub mod div;
pub mod like;
pub mod substring;
pub mod extract;
pub mod pad;

verus! {

/// `spec::fns::apply_fn` on evaluated arguments (the arguments satisfy the timestamp invariant).
pub fn exec_fn(f: ScalarFn, args: &Vec<EVal>) -> (r: Outcome<EVal>)
    requires row_ts_ok(view_row(args@)),
    ensures
        match r {
            Ok(res) => fits_fn(f, view_row(args@)) && view_result(res) == apply_fn(f, view_row(args@))
                && (res matches Ok(v) ==> val_ts_ok(v@)),
            Err(_) => !fits_fn(f, view_row(args@)),
        },
{
    match f {
        ScalarFn::DivInt4 | ScalarFn::DivInt8 | ScalarFn::DivNumeric => div::exec_div(f, args),
        ScalarFn::Like => like::exec_like(f, args),
        ScalarFn::Substring2 | ScalarFn::Substring3 => substring::exec_substring(f, args),
        ScalarFn::ExtractYear | ScalarFn::ExtractMonth | ScalarFn::ExtractDay => extract::exec_extract(f, args),
        ScalarFn::PadBpchar => pad::exec_pad(f, args),
    }
}

/// `spec::fns::type_fn`.
pub fn type_fn_exec(f: ScalarFn, args: &Vec<ColTy>) -> (r: Option<ColTy>)
    ensures r == type_fn(f, args@),
{
    match f {
        ScalarFn::DivInt4 | ScalarFn::DivInt8 | ScalarFn::DivNumeric => div::type_div_exec(f, args),
        ScalarFn::Like => like::type_like_exec(f, args),
        ScalarFn::Substring2 | ScalarFn::Substring3 => substring::type_substring_exec(f, args),
        ScalarFn::ExtractYear | ScalarFn::ExtractMonth | ScalarFn::ExtractDay => extract::type_extract_exec(f, args),
        ScalarFn::PadBpchar => pad::type_pad_exec(f, args),
    }
}

} // verus!
