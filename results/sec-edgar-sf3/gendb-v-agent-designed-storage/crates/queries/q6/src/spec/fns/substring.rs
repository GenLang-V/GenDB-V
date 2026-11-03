//! `SUBSTRING(s FROM start [FOR len])` (`Expr::Call` with `Substring3` `[s, start, len]` or `Substring2`
//! `[s, start]`). PostgreSQL 18 `text_substring` (varlena.c), over characters (`spec::chars`):
//! - strict: any NULL argument gives NULL (before the length check);
//! - `len < 0` is 22011 "negative substring length not allowed";
//! - the result is the characters at 1-based positions `p` with `max(start, 1) <= p < start + len`; when
//!   `start + len` overflows int4, PostgreSQL takes the rest of the string (so does `Substring2`);
//! - a start past the end, or an end at or before position 1, gives the empty string.
//! A `char(n)` argument reaches `SUBSTRING` through PostgreSQL's implicit `bpchar -> text` cast, which strips
//! trailing blanks: the identity on stored (canonical) `char(n)` values, so the frontend passes it unchanged.
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::limits::*;
use crate::spec::chars::*;

verus! {

/// Exclusive 1-based end position: `start + len`, or `None` ("to the end") when it overflows int4.
pub open spec fn substring_end(start: int, len: int) -> Option<int> {
    if start + len > int4_max() { None } else { Some(start + len) }
}

/// The characters `cs` at 1-based positions `max(start, 1) <= p < end` (`end = None`: to the end).
pub open spec fn char_range(cs: Seq<Seq<u8>>, start: int, end: Option<int>) -> Seq<u8> {
    let n = cs.len() as int;
    let lo = if start < 1 { 0 } else if start - 1 > n { n } else { start - 1 };
    let hi = match end {
        None => n,
        Some(e) => if e - 1 < lo { lo } else if e - 1 > n { n } else { e - 1 },
    };
    concat(cs.subrange(lo, hi))
}

/// Value of `SUBSTRING` on non-NULL arguments of the right arity.
pub open spec fn substring_value(f: ScalarFn, args: Seq<Val>) -> Result<Val, SqlError> {
    match f {
        ScalarFn::Substring3 => match (args[0], args[1], args[2]) {
            (Val::Text(b), Val::Int(start), Val::Int(len)) =>
                if len < 0 {
                    Err(SqlError::SubstringError)
                } else {
                    Ok(Val::Text(char_range(chars(b), start, substring_end(start, len))))
                },
            _ => Err(SqlError::TypeError),
        },
        _ => match (args[0], args[1]) {
            (Val::Text(b), Val::Int(start)) => Ok(Val::Text(char_range(chars(b), start, None))),
            _ => Err(SqlError::TypeError),
        },
    }
}

/// Number of arguments: 3 for `Substring3`, 2 for `Substring2`.
pub open spec fn substring_arity(f: ScalarFn) -> nat {
    match f { ScalarFn::Substring3 => 3, _ => 2 }
}

/// `substring(text, int4 [, int4]) -> text` (PostgreSQL has no int8 or numeric variant).
pub open spec fn type_substring(f: ScalarFn, args: Seq<ColTy>) -> Option<ColTy> {
    if args.len() == substring_arity(f) && args[0].ty is Text && args[1].ty is Int4
        && (args.len() == 2 || args[2].ty is Int4) {
        Some(ColTy {
            ty: ScalarTy::Text,
            nullable: args[0].nullable || args[1].nullable || (args.len() == 3 && args[2].nullable),
        })
    } else {
        None
    }
}

/// Value of `SUBSTRING` on its evaluated arguments (strict: any NULL gives NULL).
pub open spec fn apply_substring(f: ScalarFn, args: Seq<Val>) -> Result<Val, SqlError> {
    if args.len() != substring_arity(f) {
        Err(SqlError::TypeError)
    } else if exists|k: int| 0 <= k < args.len() && #[trigger] args[k] is Null {
        Ok(Val::Null)
    } else {
        substring_value(f, args)
    }
}

/// SUBSTRING never needs `Capacity`.
pub open spec fn fits_substring(f: ScalarFn, args: Seq<Val>) -> bool {
    true
}

} // verus!
