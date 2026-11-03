//! Executable `spec::fns::like`: the same tokenizer and PostgreSQL's `MatchText` search over executable
//! characters. The literal and `_` steps and the `%`-run skipping are loops; recursion happens only from the scan
//! after a `%` into the rest of the pattern (depth at most the number of `%` runs). Never `Capacity`.
//!
//! Matcher functions mirror the spec ones: `like_mt_exec` (match tokens `p[j..]` against characters `t[i..]`),
//! `like_any_exec` (after a `%`), `like_scan_exec` (try each start position for the rest of the pattern) and
//! `like_end_exec` (text exhausted: only `%` tokens may remain).
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::chars::*;
use crate::spec::fns::like::*;
use crate::exec::value::*;
use crate::exec::domain::*;
use crate::exec::chars::*;

verus! {

/// The wildcard bytes `%` (any run of characters) and `_` (one character), `spec::fns::like::{pct, underscore}`.
const PERCENT: u8 = 0x25;
const UNDERSCORE: u8 = 0x5F;

/// A pattern token (`spec::fns::like::LikeTok`): a literal character, `_`, `%`, or an escape character at the end
/// of the pattern (an error when reached).
pub enum ETok {
    Lit(Vec<u8>),
    One,
    Any,
    Dangling,
}

pub open spec fn view_tok(t: ETok) -> LikeTok {
    match t {
        ETok::Lit(c) => LikeTok::Lit(c@),
        ETok::One => LikeTok::One,
        ETok::Any => LikeTok::Any,
        ETok::Dangling => LikeTok::Dangling,
    }
}

pub open spec fn view_toks(ts: Seq<ETok>) -> Seq<LikeTok> {
    ts.map_values(|t: ETok| view_tok(t))
}

/// The character `c` is the single byte `b`.
fn is_byte_char(c: &Vec<u8>, b: u8) -> (r: bool)
    ensures r == (c@ == seq![b]),
{
    if c.len() == 1 && c[0] == b {
        assert(c@ =~= seq![b]);
        true
    } else {
        false
    }
}

/// `spec::fns::like::like_tokens(pc, esc, 0)`.
pub fn like_tokens_exec(pc: &Vec<Vec<u8>>, esc: &Option<Vec<u8>>) -> (r: Vec<ETok>)
    ensures
        view_toks(r@) == like_tokens(view_chars(pc@), match esc { Some(e) => Some(e@), None => None }, 0),
{
    let ghost cs = view_chars(pc@);
    let ghost es = match esc { Some(e) => Some(e@), None => None::<Seq<u8>> };
    let mut out: Vec<ETok> = Vec::new();
    let mut k: usize = 0;
    assert(view_toks(out@) + like_tokens(cs, es, 0) =~= like_tokens(cs, es, 0));
    while k < pc.len()
        invariant
            k <= pc.len(),
            cs == view_chars(pc@),
            es == match esc { Some(e) => Some(e@), None => None::<Seq<u8>> },
            view_toks(out@) + like_tokens(cs, es, k as int) == like_tokens(cs, es, 0),
        decreases pc.len() - k,
    {
        let c = &pc[k];
        assert(cs[k as int] == c@);
        let is_esc = match esc {
            Some(e) => bytes_eq(e, c),
            None => false,
        };
        assert(is_esc == (es == Some(cs[k as int])));
        let ghost old_out = out@;
        let tok: ETok;
        let next: usize;
        if is_esc {
            if k + 1 >= pc.len() {
                tok = ETok::Dangling;
                next = pc.len();
            } else {
                tok = ETok::Lit(pc[k + 1].clone());
                assert(cs[k + 1] == pc@[k + 1]@);
                next = k + 2;
            }
        } else if is_byte_char(c, PERCENT) {
            tok = ETok::Any;
            next = k + 1;
        } else if is_byte_char(c, UNDERSCORE) {
            tok = ETok::One;
            next = k + 1;
        } else {
            tok = ETok::Lit(c.clone());
            next = k + 1;
        }
        proof {
            assert(like_tokens(cs, es, k as int) =~= seq![view_tok(tok)] + like_tokens(cs, es, next as int)) by {
                if is_esc && k + 1 >= pc.len() {
                    assert(like_tokens(cs, es, next as int) =~= Seq::<LikeTok>::empty());
                }
            }
        }
        out.push(tok);
        proof {
            assert(view_toks(out@) =~= view_toks(old_out).push(view_tok(tok)));
            assert(view_toks(out@) + like_tokens(cs, es, next as int)
                =~= view_toks(old_out) + (seq![view_tok(tok)] + like_tokens(cs, es, next as int)));
        }
        k = next;
    }
    assert(like_tokens(cs, es, k as int) =~= Seq::<LikeTok>::empty());
    assert(view_toks(out@) =~= view_toks(out@) + like_tokens(cs, es, k as int));
    out
}

/// `like_mt(t, p, i0, j0)`.
pub fn like_mt_exec(t: &Vec<Vec<u8>>, p: &Vec<ETok>, i0: usize, j0: usize) -> (r: Result<LikeRes, SqlError>)
    requires i0 <= t.len(), j0 <= p.len(),
    ensures r == like_mt(view_chars(t@), view_toks(p@), i0 as int, j0 as int),
    decreases p.len() - j0, 0int, t.len() - i0,
{
    let ghost tv = view_chars(t@);
    let ghost pv = view_toks(p@);
    let mut i = i0;
    let mut j = j0;
    loop
        invariant
            i0 <= i <= t.len(),
            j0 <= j <= p.len(),
            tv == view_chars(t@),
            pv == view_toks(p@),
            like_mt(tv, pv, i as int, j as int) == like_mt(tv, pv, i0 as int, j0 as int),
        decreases p.len() - j,
    {
        if i < t.len() && j < p.len() {
            assert(tv[i as int] == t@[i as int]@);
            assert(pv[j as int] == view_tok(p@[j as int]));
            match &p[j] {
                ETok::Dangling => {
                    return Err(SqlError::InvalidEscapeSequence);
                },
                ETok::Lit(c) => {
                    if bytes_eq(&t[i], c) {
                        i = i + 1;
                        j = j + 1;
                    } else {
                        return Ok(LikeRes::NoMatch);
                    }
                },
                ETok::One => {
                    i = i + 1;
                    j = j + 1;
                },
                ETok::Any => {
                    return like_any_exec(t, p, i, j + 1);
                },
            }
        } else if i < t.len() {
            return Ok(LikeRes::NoMatch);
        } else {
            return like_end_exec(p, j);
        }
    }
}

/// `like_any(t, p, i0, j0)`.
pub fn like_any_exec(t: &Vec<Vec<u8>>, p: &Vec<ETok>, i0: usize, j0: usize) -> (r: Result<LikeRes, SqlError>)
    requires i0 <= t.len(), j0 <= p.len(),
    ensures r == like_any(view_chars(t@), view_toks(p@), i0 as int, j0 as int),
    decreases p.len() - j0, 2int, t.len() - i0,
{
    let ghost tv = view_chars(t@);
    let ghost pv = view_toks(p@);
    let mut i = i0;
    let mut j = j0;
    loop
        invariant
            i0 <= i <= t.len(),
            j0 <= j <= p.len(),
            tv == view_chars(t@),
            pv == view_toks(p@),
            like_any(tv, pv, i as int, j as int) == like_any(tv, pv, i0 as int, j0 as int),
        decreases p.len() - j,
    {
        if j < p.len() {
            assert(pv[j as int] == view_tok(p@[j as int]));
            match &p[j] {
                ETok::Any => {
                    j = j + 1;
                },
                ETok::One => {
                    if i < t.len() {
                        i = i + 1;
                        j = j + 1;
                    } else {
                        return Ok(LikeRes::Abort);
                    }
                },
                ETok::Dangling => {
                    return Err(SqlError::InvalidEscapeSequence);
                },
                ETok::Lit(_) => {
                    return like_scan_exec(t, p, i, j);
                },
            }
        } else {
            return Ok(LikeRes::Match);
        }
    }
}

/// `like_scan(t, p, k0, j)`.
pub fn like_scan_exec(t: &Vec<Vec<u8>>, p: &Vec<ETok>, k0: usize, j: usize) -> (r: Result<LikeRes, SqlError>)
    requires k0 <= t.len(), j <= p.len(),
    ensures r == like_scan(view_chars(t@), view_toks(p@), k0 as int, j as int),
    decreases p.len() - j, 1int, t.len() - k0,
{
    let ghost tv = view_chars(t@);
    let ghost pv = view_toks(p@);
    let mut k = k0;
    while k < t.len()
        invariant
            k0 <= k <= t.len(),
            j <= p.len(),
            tv == view_chars(t@),
            pv == view_toks(p@),
            like_scan(tv, pv, k as int, j as int) == like_scan(tv, pv, k0 as int, j as int),
        decreases t.len() - k,
    {
        let r = like_mt_exec(t, p, k, j);
        match r {
            Ok(LikeRes::NoMatch) => {
                k = k + 1;
            },
            _ => {
                return r;
            },
        }
    }
    Ok(LikeRes::Abort)
}

/// `like_end(p, j0)`.
pub fn like_end_exec(p: &Vec<ETok>, j0: usize) -> (r: Result<LikeRes, SqlError>)
    requires j0 <= p.len(),
    ensures r == like_end(view_toks(p@), j0 as int),
{
    let ghost pv = view_toks(p@);
    let mut j = j0;
    while j < p.len()
        invariant
            j0 <= j <= p.len(),
            pv == view_toks(p@),
            like_end(pv, j as int) == like_end(pv, j0 as int),
        decreases p.len() - j,
    {
        assert(pv[j as int] == view_tok(p@[j as int]));
        match &p[j] {
            ETok::Any => {
                j = j + 1;
            },
            _ => {
                return Ok(LikeRes::Abort);
            },
        }
    }
    Ok(LikeRes::Match)
}

/// `spec::fns::like::like_value`: `s LIKE p ESCAPE e` (an escape of more than one character is 22025).
pub fn like_value_exec(s: &EVal, p: &EVal, e: &EVal) -> (r: Result<EVal, SqlError>)
    ensures view_result(r) == like_value(s@, p@, e@),
{
    match (p, e) {
        (EVal::Text(pb), EVal::Text(eb)) => {
            let ec = chars_exec(eb);
            if ec.len() > 1 {
                return Err(SqlError::InvalidEscapeSequence);
            }
            match s {
                EVal::Null => Ok(EVal::Null),
                EVal::Text(sb) => {
                    let tc = chars_exec(sb);
                    let pc = chars_exec(pb);
                    let esc: Option<Vec<u8>> = if ec.len() == 0 { None } else { Some(ec[0].clone()) };
                    proof {
                        let ecv = chars(eb@);
                        assert(ecv == view_chars(ec@));
                        if ec.len() > 0 {
                            assert(ecv[0] == ec@[0]@);
                        }
                        assert(escape_of(ecv) == match esc { Some(x) => Some(x@), None => None::<Seq<u8>> });
                    }
                    let toks = like_tokens_exec(&pc, &esc);
                    match like_mt_exec(&tc, &toks, 0, 0) {
                        Ok(m) => Ok(EVal::Bool(match m { LikeRes::Match => true, _ => false })),
                        Err(err) => Err(err),
                    }
                },
                _ => Err(SqlError::TypeError),
            }
        },
        (EVal::Null, _) | (_, EVal::Null) => Ok(EVal::Null),
        _ => Err(SqlError::TypeError),
    }
}

/// `spec::fns::like::apply_like` on `[s, p, e]`.
pub fn exec_like(f: ScalarFn, args: &Vec<EVal>) -> (r: Outcome<EVal>)
    requires row_ts_ok(view_row(args@)),
    ensures
        match r {
            Ok(res) => fits_like(f, view_row(args@)) && view_result(res) == apply_like(f, view_row(args@))
                && (res matches Ok(v) ==> val_ts_ok(v@)),
            Err(_) => !fits_like(f, view_row(args@)),
        },
{
    if args.len() != 3 {
        return Ok(Err(SqlError::TypeError));
    }
    let res = like_value_exec(&args[0], &args[1], &args[2]);
    proof {
        let vs = view_row(args@);
        assert(vs[0] == args@[0]@ && vs[1] == args@[1]@ && vs[2] == args@[2]@);
    }
    Ok(res)
}

/// `spec::fns::like::type_like`: three text arguments give a boolean.
pub fn type_like_exec(f: ScalarFn, args: &Vec<ColTy>) -> (r: Option<ColTy>)
    ensures r == type_like(f, args@),
{
    if args.len() == 3 {
        match (args[0].ty, args[1].ty, args[2].ty) {
            (ScalarTy::Text, ScalarTy::Text, ScalarTy::Text) => Some(ColTy {
                ty: ScalarTy::Bool,
                nullable: args[0].nullable || args[1].nullable || args[2].nullable,
            }),
            _ => None,
        }
    } else {
        None
    }
}

} // verus!
