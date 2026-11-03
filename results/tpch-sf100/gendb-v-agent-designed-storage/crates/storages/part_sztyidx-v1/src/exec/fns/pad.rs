//! Executable `spec::fns::pad`: `PadBpchar(s, n)`, the blank-padded `char(n)` subject of a LIKE (`s` followed by
//! spaces up to `n` characters). Never `Capacity`.
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::chars::*;
use crate::spec::fns::pad::*;
use crate::exec::value::*;
use crate::exec::domain::*;
use crate::exec::chars::*;

verus! {

/// `b` followed by spaces up to `n` characters (none when `b` already has `n` or more).
fn pad_exec(b: &Vec<u8>, n: i64) -> (r: Vec<u8>)
    ensures r@ == b@ + spaces(n - chars(b@).len()),
{
    let char_count = chars_exec(b).len();
    let missing: i128 = n as i128 - char_count as i128;
    let mut out = b.clone();
    let mut added: i128 = 0;
    while added < missing
        invariant
            0 <= added,
            missing >= 0 ==> added <= missing,
            missing <= 0 ==> added == 0,
            out@ == b@ + spaces(added as int),
        decreases missing - added,
    {
        out.push(0x20u8);
        proof {
            assert(spaces(added as int + 1) =~= spaces(added as int).push(0x20u8));
            assert(out@ =~= b@ + spaces(added as int + 1));
        }
        added = added + 1;
    }
    proof {
        if missing > 0 {
            assert(added == missing);
        } else {
            assert(added == 0);
            assert(spaces(missing as int) =~= spaces(0));
        }
    }
    out
}

/// `spec::fns::pad::apply_pad` on `[s, n]`.
pub fn exec_pad(f: ScalarFn, args: &Vec<EVal>) -> (r: Outcome<EVal>)
    requires row_ts_ok(view_row(args@)),
    ensures
        match r {
            Ok(res) => fits_pad(f, view_row(args@)) && view_result(res) == apply_pad(f, view_row(args@))
                && (res matches Ok(v) ==> val_ts_ok(v@)),
            Err(_) => !fits_pad(f, view_row(args@)),
        },
{
    if args.len() != 2 {
        return Ok(Err(SqlError::TypeError));
    }
    let ghost vs = view_row(args@);
    assert(vs[0] == args@[0]@ && vs[1] == args@[1]@);
    match (&args[0], &args[1]) {
        (EVal::Null, _) | (_, EVal::Null) => Ok(Ok(EVal::Null)),
        (EVal::Text(b), EVal::Int(n)) => Ok(Ok(EVal::Text(pad_exec(b, *n)))),
        _ => Ok(Err(SqlError::TypeError)),
    }
}

/// `spec::fns::pad::type_pad`: `(text, int4) -> text`.
pub fn type_pad_exec(f: ScalarFn, args: &Vec<ColTy>) -> (r: Option<ColTy>)
    ensures r == type_pad(f, args@),
{
    if args.len() == 2 {
        match (args[0].ty, args[1].ty) {
            (ScalarTy::Text, ScalarTy::Int4) =>
                Some(ColTy { ty: ScalarTy::Text, nullable: args[0].nullable || args[1].nullable }),
            _ => None,
        }
    } else {
        None
    }
}

} // verus!
