//! Executable `spec::fns::substring`: `SUBSTRING(s FROM start [FOR len])` over characters. Positions are
//! compared in `i128` from the `i64` operands, so every int4 (indeed int8) start and length is exact; never
//! `Capacity`.
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::chars::*;
use crate::spec::fns::substring::*;
use crate::exec::value::*;
use crate::exec::domain::*;
use crate::exec::chars::*;

verus! {

/// `char_range(chars(b), start, end)`: the characters at 1-based positions `max(start, 1) <= p < end`
/// (`end = None`: to the end of the string).
fn char_range_exec(b: &Vec<u8>, start: i64, end: Option<i64>) -> (r: Vec<u8>)
    ensures
        r@ == char_range(chars(b@), start as int, match end { Some(e) => Some(e as int), None => None }),
{
    let cs = chars_exec(b);
    let n = cs.len();
    let s = start as i128;
    // 0-based character bounds `lo..hi`, clamped to the string.
    let lo: usize = if s < 1 { 0 } else if s - 1 > n as i128 { n } else { (s - 1) as usize };
    let hi: usize = match end {
        None => n,
        Some(e) => {
            let e = e as i128;
            if e - 1 < lo as i128 { lo } else if e - 1 > n as i128 { n } else { (e - 1) as usize }
        },
    };
    concat_range_exec(&cs, lo, hi)
}

/// `spec::fns::substring::apply_substring` on `[s, start]` or `[s, start, len]`.
pub fn exec_substring(f: ScalarFn, args: &Vec<EVal>) -> (r: Outcome<EVal>)
    requires row_ts_ok(view_row(args@)),
    ensures
        match r {
            Ok(res) => fits_substring(f, view_row(args@)) && view_result(res) == apply_substring(f, view_row(args@))
                && (res matches Ok(v) ==> val_ts_ok(v@)),
            Err(_) => !fits_substring(f, view_row(args@)),
        },
{
    let ghost vs = view_row(args@);
    let arity: usize = match f { ScalarFn::Substring3 => 3, _ => 2 };
    if args.len() != arity {
        return Ok(Err(SqlError::TypeError));
    }
    let mut k: usize = 0;
    while k < args.len()
        invariant
            k <= args.len(),
            args.len() == arity,
            arity as nat == substring_arity(f),
            vs == view_row(args@),
            vs.len() == args.len(),
            forall|m: int| 0 <= m < k ==> !(#[trigger] vs[m] is Null),
        decreases args.len() - k,
    {
        if let EVal::Null = &args[k] {
            assert(vs[k as int] is Null);
            assert(exists|m: int| 0 <= m < vs.len() && #[trigger] vs[m] is Null);
            assert(apply_substring(f, vs) == Ok::<Val, SqlError>(Val::Null));
            return Ok(Ok(EVal::Null));
        }
        assert(!(vs[k as int] is Null));
        k = k + 1;
    }
    assert(!(exists|m: int| 0 <= m < vs.len() && #[trigger] vs[m] is Null));
    assert(vs[0] == args@[0]@ && vs[1] == args@[1]@);
    match f {
        ScalarFn::Substring3 => {
            assert(vs[2] == args@[2]@);
            match (&args[0], &args[1], &args[2]) {
                (EVal::Text(b), EVal::Int(start), EVal::Int(len)) => {
                    if *len < 0 {
                        Ok(Err(SqlError::SubstringError))
                    } else {
                        // `start + len` past int4 means "to the end" (`spec::fns::substring::substring_end`).
                        let end = if *start as i128 + *len as i128 > i32::MAX as i128 { None } else { Some(*start + *len) };
                        let r = char_range_exec(b, *start, end);
                        assert(substring_end(*start as int, *len as int)
                            == match end { Some(e) => Some(e as int), None => None::<int> });
                        assert(apply_substring(f, vs) == substring_value(f, vs));
                        Ok(Ok(EVal::Text(r)))
                    }
                },
                _ => Ok(Err(SqlError::TypeError)),
            }
        },
        _ => {
            match (&args[0], &args[1]) {
                (EVal::Text(b), EVal::Int(start)) => Ok(Ok(EVal::Text(char_range_exec(b, *start, None)))),
                _ => Ok(Err(SqlError::TypeError)),
            }
        },
    }
}

/// `spec::fns::substring::type_substring`: `substring(text, int4 [, int4]) -> text`.
pub fn type_substring_exec(f: ScalarFn, args: &Vec<ColTy>) -> (r: Option<ColTy>)
    ensures r == type_substring(f, args@),
{
    let arity: usize = match f { ScalarFn::Substring3 => 3, _ => 2 };
    if args.len() != arity {
        return None;
    }
    let ok0 = match args[0].ty { ScalarTy::Text => true, _ => false };
    let ok1 = match args[1].ty { ScalarTy::Int4 => true, _ => false };
    let ok2 = args.len() == 2 || match args[2].ty { ScalarTy::Int4 => true, _ => false };
    if ok0 && ok1 && ok2 {
        Some(ColTy {
            ty: ScalarTy::Text,
            nullable: args[0].nullable || args[1].nullable || (args.len() == 3 && args[2].nullable),
        })
    } else {
        None
    }
}

} // verus!
