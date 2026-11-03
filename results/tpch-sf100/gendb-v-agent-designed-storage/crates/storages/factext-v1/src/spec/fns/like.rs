//! `s LIKE p ESCAPE e` (`Expr::Call` with `Like`, arguments `[s, p, e]`).
//!
//! PostgreSQL 18 evaluates `s LIKE p ESCAPE e` as `s ~~ like_escape(p, e)` (`s LIKE p` without ESCAPE is the same
//! with the escape `\`, which the frontend supplies). Every step below is PostgreSQL's, over characters
//! (`spec::chars`; C collation, so a literal character matches only the identical bytes):
//! 1. `like_escape` is strict: a NULL pattern or escape gives NULL. An escape of more than one character is
//!    22025 "invalid escape string" (not 22019). This happens before the strict `~~` looks at the subject, so a
//!    NULL subject with an invalid escape still raises 22025.
//! 2. A NULL subject gives NULL.
//! 3. The pattern is read into tokens (`like_tokens`): the escape character followed by any character is that
//!    character literally (the escape takes precedence over `%` and `_`); `%` is any sequence; `_` is one
//!    character; an empty escape disables escaping; an escape as the last character is a dangling escape.
//! 4. The tokens are run by PostgreSQL's matcher `MatchText` (`like_match.c`), `like_mt` below, which is
//!    standard matching with an early exit (`LIKE_ABORT`). It raises 22025 "LIKE pattern must not end with
//!    escape character" only when the search actually reaches a dangling escape with text left (or directly
//!    after a `%` run); otherwise such a pattern gives false. `bridge::fns::like::lemma_like_mt_std` proves that
//!    whenever the matcher returns, its answer is the standard meaning `like_std` (where a dangling escape
//!    matches nothing), and that a pattern without a dangling escape never raises.
//! The frontend passes a `char(n)` subject through `PadBpchar` (PostgreSQL's `bpcharlike` sees the blank-padded
//! value) and a `char(n)` pattern or escape unchanged (PostgreSQL's implicit `bpchar -> text` cast strips the
//! padding, and stored `char(n)` values are canonical, i.e. already stripped).
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::chars::*;

verus! {

/// One pattern token.
pub enum LikeTok {
    /// A character matched literally (bytewise).
    Lit(Seq<u8>),
    /// `_`: exactly one character.
    One,
    /// `%`: any sequence of characters.
    Any,
    /// An escape character with nothing after it (only ever the last token).
    Dangling,
}

/// `MatchText`'s three outcomes (`LIKE_TRUE`, `LIKE_FALSE`, `LIKE_ABORT`); the operator is true only on `Match`.
pub enum LikeRes {
    Match,
    NoMatch,
    /// No match here nor at any later text position (PostgreSQL's early exit).
    Abort,
}

/// The pattern characters `%` and `_`.
pub open spec fn pct() -> Seq<u8> { seq![0x25u8] }
pub open spec fn underscore() -> Seq<u8> { seq![0x5Fu8] }

/// Tokens of the pattern characters `pc[k..]` with escape character `esc` (`None`: no escaping).
pub open spec fn like_tokens(pc: Seq<Seq<u8>>, esc: Option<Seq<u8>>, k: int) -> Seq<LikeTok>
    decreases pc.len() - k,
{
    if k < 0 || k >= pc.len() {
        Seq::empty()
    } else if esc == Some(pc[k]) {
        if k + 1 >= pc.len() {
            seq![LikeTok::Dangling]
        } else {
            seq![LikeTok::Lit(pc[k + 1])] + like_tokens(pc, esc, k + 2)
        }
    } else if pc[k] == pct() {
        seq![LikeTok::Any] + like_tokens(pc, esc, k + 1)
    } else if pc[k] == underscore() {
        seq![LikeTok::One] + like_tokens(pc, esc, k + 1)
    } else {
        seq![LikeTok::Lit(pc[k])] + like_tokens(pc, esc, k + 1)
    }
}

/// `MatchText(t[i..], p[j..])`: the main loop (literal and `_` steps; `%` hands over to `like_any`).
pub open spec fn like_mt(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int, j: int) -> Result<LikeRes, SqlError>
    decreases p.len() - j, 0int, t.len() - i,
{
    if 0 <= i < t.len() && 0 <= j < p.len() {
        match p[j] {
            LikeTok::Dangling => Err(SqlError::InvalidEscapeSequence),
            LikeTok::Lit(c) => if t[i] == c { like_mt(t, p, i + 1, j + 1) } else { Ok(LikeRes::NoMatch) },
            LikeTok::One => like_mt(t, p, i + 1, j + 1),
            LikeTok::Any => like_any(t, p, i, j + 1),
        }
    } else if 0 <= i < t.len() {
        // End of pattern, text left.
        Ok(LikeRes::NoMatch)
    } else {
        // End of text: match iff only `%`s are left.
        like_end(p, j)
    }
}

/// After a `%` (the tokens before `j` are consumed): skip further `%`s and `_`s (each `_` takes one character;
/// running out of text is `Abort`), then a trailing run matches, a dangling escape raises, and a literal starts
/// the scan for a position where the rest matches.
pub open spec fn like_any(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int, j: int) -> Result<LikeRes, SqlError>
    decreases p.len() - j, 2int, t.len() - i,
{
    if 0 <= j < p.len() {
        match p[j] {
            LikeTok::Any => like_any(t, p, i, j + 1),
            LikeTok::One => if 0 <= i < t.len() { like_any(t, p, i + 1, j + 1) } else { Ok(LikeRes::Abort) },
            LikeTok::Dangling => Err(SqlError::InvalidEscapeSequence),
            LikeTok::Lit(_) => like_scan(t, p, i, j),
        }
    } else {
        Ok(LikeRes::Match)
    }
}

/// The scan: the first position `k' >= k` where `MatchText(t[k'..], p[j..])` is not `NoMatch` decides; the end
/// of the text is `Abort`.
pub open spec fn like_scan(t: Seq<Seq<u8>>, p: Seq<LikeTok>, k: int, j: int) -> Result<LikeRes, SqlError>
    decreases p.len() - j, 1int, t.len() - k,
{
    if 0 <= k < t.len() {
        match like_mt(t, p, k, j) {
            Ok(LikeRes::NoMatch) => like_scan(t, p, k + 1, j),
            r => r,
        }
    } else {
        Ok(LikeRes::Abort)
    }
}

/// End of text: `Match` iff every remaining token is `%`, else `Abort`.
pub open spec fn like_end(p: Seq<LikeTok>, j: int) -> Result<LikeRes, SqlError>
    decreases p.len() - j,
{
    if 0 <= j < p.len() {
        match p[j] {
            LikeTok::Any => like_end(p, j + 1),
            _ => Ok(LikeRes::Abort),
        }
    } else {
        Ok(LikeRes::Match)
    }
}

/// The standard meaning of LIKE matching (SQL: `t[i..]` is a concatenation matching the tokens `p[j..]` one by
/// one), which a dangling escape never matches. Not used by the evaluation; `bridge::fns::like` proves that the
/// matcher agrees with it.
pub open spec fn like_std(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int, j: int) -> bool
    decreases (t.len() - i) + (p.len() - j),
{
    if i < 0 || i > t.len() || j < 0 {
        false
    } else if j >= p.len() {
        i == t.len()
    } else {
        match p[j] {
            LikeTok::Lit(c) => i < t.len() && t[i] == c && like_std(t, p, i + 1, j + 1),
            LikeTok::One => i < t.len() && like_std(t, p, i + 1, j + 1),
            LikeTok::Any => like_std(t, p, i, j + 1) || (i < t.len() && like_std(t, p, i + 1, j)),
            LikeTok::Dangling => false,
        }
    }
}

/// The escape character of an escape string of at most one character.
pub open spec fn escape_of(ec: Seq<Seq<u8>>) -> Option<Seq<u8>> {
    if ec.len() == 0 { None } else { Some(ec[0]) }
}

/// `s LIKE p ESCAPE e` on values (see the module comment for the order of the checks).
pub open spec fn like_value(s: Val, p: Val, e: Val) -> Result<Val, SqlError> {
    if p is Null || e is Null {
        Ok(Val::Null)
    } else {
        match (p, e) {
            (Val::Text(pb), Val::Text(eb)) => {
                let ec = chars(eb);
                if ec.len() > 1 {
                    Err(SqlError::InvalidEscapeSequence)
                } else {
                    match s {
                        Val::Null => Ok(Val::Null),
                        Val::Text(sb) => match like_mt(chars(sb), like_tokens(chars(pb), escape_of(ec), 0), 0, 0) {
                            Ok(r) => Ok(Val::Bool(r is Match)),
                            Err(err) => Err(err),
                        },
                        _ => Err(SqlError::TypeError),
                    }
                }
            },
            _ => Err(SqlError::TypeError),
        }
    }
}

/// `[text, text, text] -> bool` (`text`, `varchar` and `char(n)` are the one static type `Text`).
pub open spec fn type_like(f: ScalarFn, args: Seq<ColTy>) -> Option<ColTy> {
    if args.len() == 3 && args[0].ty is Text && args[1].ty is Text && args[2].ty is Text {
        Some(ColTy { ty: ScalarTy::Bool, nullable: args[0].nullable || args[1].nullable || args[2].nullable })
    } else {
        None
    }
}

/// Value of `LIKE` on its evaluated arguments `[s, p, e]`.
pub open spec fn apply_like(f: ScalarFn, args: Seq<Val>) -> Result<Val, SqlError> {
    if args.len() == 3 { like_value(args[0], args[1], args[2]) } else { Err(SqlError::TypeError) }
}

/// LIKE never needs `Capacity`.
pub open spec fn fits_like(f: ScalarFn, args: Seq<Val>) -> bool {
    true
}

} // verus!
