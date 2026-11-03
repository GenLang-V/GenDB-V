//! Leaf scalar functions of `Expr::Call` (`spec::ast::ScalarFn`): typing, value and executable domain, dispatched
//! to one module per feature. `spec::eval` evaluates the arguments left to right (first error wins) and applies
//! `apply_fn`; `spec::typing` types the arguments and applies `type_fn`; `exec::relational::domain` requires
//! `fits_fn` of the argument values. These dispatchers are final; the per-feature modules own the rules.
//! - `div`:       DivInt4, DivInt8, DivNumeric
//! - `like`:      Like
//! - `substring`: Substring2, Substring3
//! - `extract`:   ExtractYear, ExtractMonth, ExtractDay
//! - `pad`:       PadBpchar
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::ast::*;

pub mod div;
pub mod like;
pub mod substring;
pub mod extract;
pub mod pad;

verus! {

/// Result type of `f` over arguments of types `args`; `None` = ill-typed.
pub open spec fn type_fn(f: ScalarFn, args: Seq<ColTy>) -> Option<ColTy> {
    match f {
        ScalarFn::DivInt4 | ScalarFn::DivInt8 | ScalarFn::DivNumeric => div::type_div(f, args),
        ScalarFn::Like => like::type_like(f, args),
        ScalarFn::Substring2 | ScalarFn::Substring3 => substring::type_substring(f, args),
        ScalarFn::ExtractYear | ScalarFn::ExtractMonth | ScalarFn::ExtractDay => extract::type_extract(f, args),
        ScalarFn::PadBpchar => pad::type_pad(f, args),
    }
}

/// Value of `f` on evaluated arguments.
pub open spec fn apply_fn(f: ScalarFn, args: Seq<Val>) -> Result<Val, SqlError> {
    match f {
        ScalarFn::DivInt4 | ScalarFn::DivInt8 | ScalarFn::DivNumeric => div::apply_div(f, args),
        ScalarFn::Like => like::apply_like(f, args),
        ScalarFn::Substring2 | ScalarFn::Substring3 => substring::apply_substring(f, args),
        ScalarFn::ExtractYear | ScalarFn::ExtractMonth | ScalarFn::ExtractDay => extract::apply_extract(f, args),
        ScalarFn::PadBpchar => pad::apply_pad(f, args),
    }
}

/// Executable domain of `apply_fn` (the intermediates it computes fit the machine representation).
pub open spec fn fits_fn(f: ScalarFn, args: Seq<Val>) -> bool {
    match f {
        ScalarFn::DivInt4 | ScalarFn::DivInt8 | ScalarFn::DivNumeric => div::fits_div(f, args),
        ScalarFn::Like => like::fits_like(f, args),
        ScalarFn::Substring2 | ScalarFn::Substring3 => substring::fits_substring(f, args),
        ScalarFn::ExtractYear | ScalarFn::ExtractMonth | ScalarFn::ExtractDay => extract::fits_extract(f, args),
        ScalarFn::PadBpchar => pad::fits_pad(f, args),
    }
}

} // verus!
