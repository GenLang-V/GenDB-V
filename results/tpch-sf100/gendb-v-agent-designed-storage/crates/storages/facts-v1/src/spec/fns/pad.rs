//! `char(n)` blank padding (`Expr::Call` with `PadBpchar`, arguments `[s, n]`).
//!
//! GenDB stores `char(n)` values canonically, without trailing blanks (`spec::typing::value_in_column`), and
//! the implicit `bpchar -> text` cast of PostgreSQL strips them, so most operations see the canonical value. The
//! exception is PostgreSQL's `bpcharlike`/`bpcharnlike` (`char(n) [NOT] LIKE text`), which match the stored,
//! blank-padded value: `'ab'::char(4) LIKE 'ab'` is false and `LIKE 'ab__'` true (confirmed by a PostgreSQL 18
//! fixture). The frontend therefore passes a `char(n)` LIKE subject through
//! `PadBpchar(s, n)`: `s` followed by spaces up to `n` characters (`spec::chars`). Strict (NULL gives NULL).
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::chars::*;

verus! {

/// `k` spaces (none when `k <= 0`).
pub open spec fn spaces(k: int) -> Seq<u8> {
    Seq::new(if k > 0 { k as nat } else { 0 }, |i: int| 0x20u8)
}

/// `[text, int4] -> text`.
pub open spec fn type_pad(f: ScalarFn, args: Seq<ColTy>) -> Option<ColTy> {
    if args.len() == 2 && args[0].ty is Text && args[1].ty is Int4 {
        Some(ColTy { ty: ScalarTy::Text, nullable: args[0].nullable || args[1].nullable })
    } else {
        None
    }
}

/// `s` followed by spaces up to `n` characters (strict: NULL gives NULL).
pub open spec fn apply_pad(f: ScalarFn, args: Seq<Val>) -> Result<Val, SqlError> {
    if args.len() != 2 {
        Err(SqlError::TypeError)
    } else if args[0] is Null || args[1] is Null {
        Ok(Val::Null)
    } else {
        match (args[0], args[1]) {
            (Val::Text(b), Val::Int(n)) => Ok(Val::Text(b + spaces(n - chars(b).len()))),
            _ => Err(SqlError::TypeError),
        }
    }
}

/// Padding never needs `Capacity`.
pub open spec fn fits_pad(f: ScalarFn, args: Seq<Val>) -> bool {
    true
}

} // verus!
