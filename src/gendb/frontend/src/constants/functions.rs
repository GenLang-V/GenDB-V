//! The leaf scalar functions of `Expr::Call` on evaluated arguments: a transcription of `spec::fns::apply_fn` and its
//! modules `div`, `like`, `substring`, `extract` and `pad` (only numeric division can leave the executable domain,
//! `num_div_fits`).

use super::eval::{civil_from_date, int_result, NumKind, Outcome, SqlError, Stop, Val, INT4_MAX, USECS_PER_DAY};

/// `apply_fn`: the value of `f` on its arguments.
pub(super) fn apply_fn(f: &str, args: &[Val]) -> Outcome<Val> {
    match (f, args) {
        ("DivInt4" | "DivInt8" | "DivNumeric", [a, b]) => div(f, a, b),
        ("Like", [s, p, e]) => like(s, p, e),
        ("Substring2" | "Substring3", _) => substring(f, args),
        ("ExtractYear" | "ExtractMonth" | "ExtractDay", [x]) => extract(f, x),
        ("PadBpchar", [s, n]) => pad(s, n),
        _ => Err(Stop::Undecided),
    }
}

// ---------------------------------------------------------------- division (`spec::fns::div`)

/// `apply_div` (strict): integer division truncates toward zero after the zero check (22012), then the range check
/// (`MIN / -1` is 22003); numeric division is `num_div`.
fn div(f: &str, a: &Val, b: &Val) -> Outcome<Val> {
    match (a, b) {
        (Val::Null, _) | (_, Val::Null) => Ok(Val::Null),
        (Val::Int(x), Val::Int(y)) if f != "DivNumeric" => {
            if *y == 0 {
                return Err(Stop::Sql(SqlError::DivisionByZero));
            }
            // Rust's integer `/` truncates toward zero, as C's (`trunc_div`).
            int_result(if f == "DivInt4" { NumKind::Int4 } else { NumKind::Int8 }, i128::from(*x) / i128::from(*y))
        }
        (Val::Num { coeff: c1, scale: s1 }, Val::Num { coeff: c2, scale: s2 }) if f == "DivNumeric" => num_div(*c1, *s1, *c2, *s2),
        _ => Err(Stop::Undecided),
    }
}

/// Number of decimal digits of `n` (0 has none).
fn decimal_digits(mut n: u128) -> i64 {
    let mut digits = 0;
    while n > 0 {
        n /= 10;
        digits += 1;
    }
    digits
}

/// `nbase_weight`: the base-10000 weight of the leading nonzero digit of `coeff·10^-scale` (0 for zero).
fn nbase_weight(coeff: i128, scale: u32) -> i64 {
    if coeff == 0 { 0 } else { (decimal_digits(coeff.unsigned_abs()) - 1 - i64::from(scale)).div_euclid(4) }
}

/// `nbase_first_digit`: the leading nonzero base-10000 digit of `coeff·10^-scale` (0 for zero). With `t` in
/// `[1 - digits, 4 - digits]` the shift never leaves `u128`.
fn nbase_first_digit(coeff: i128, scale: u32) -> u128 {
    if coeff == 0 {
        return 0;
    }
    let t = -i64::from(scale) - 4 * nbase_weight(coeff, scale);
    let magnitude = coeff.unsigned_abs();
    if t >= 0 { magnitude * 10u128.pow(t as u32) } else { magnitude / 10u128.pow((-t) as u32) }
}

/// `div_scale`: PostgreSQL's `select_div_scale`.
fn div_scale(c1: i128, s1: u32, c2: i128, s2: u32) -> u32 {
    let qw0 = nbase_weight(c1, s1) - nbase_weight(c2, s2);
    let qweight = if nbase_first_digit(c1, s1) <= nbase_first_digit(c2, s2) { qw0 - 1 } else { qw0 };
    (16 - 4 * qweight).max(i64::from(s1)).max(i64::from(s2)).max(0).min(1000) as u32
}

/// `m·10^k` in `u128`, `Capacity` when it does not fit (`num_div_fits`).
fn scaled(m: u128, k: i64) -> Outcome<u128> {
    u32::try_from(k).ok().and_then(|k| 10u128.checked_pow(k)).and_then(|p| m.checked_mul(p)).ok_or(Stop::Capacity)
}

/// `num_div` within `num_div_fits`: 22012 for a zero divisor, otherwise the quotient at scale `div_scale`, rounded half
/// away from zero, from the scaled dividend `|c1|·10^k` (`k >= 0`) or scaled divisor `|c2|·10^-k` (`k < 0`),
/// `k = scale + s2 - s1`; both and the result coefficient must fit (`u128`, `i128`).
pub(super) fn num_div(c1: i128, s1: u32, c2: i128, s2: u32) -> Outcome<Val> {
    if c2 == 0 {
        return Err(Stop::Sql(SqlError::DivisionByZero));
    }
    let scale = div_scale(c1, s1, c2, s2);
    if c1 == 0 {
        return Ok(Val::Num { coeff: 0, scale });
    }
    let k = i64::from(scale) + i64::from(s2) - i64::from(s1);
    let (n, d) = if k >= 0 { (scaled(c1.unsigned_abs(), k)?, c2.unsigned_abs()) } else { (c1.unsigned_abs(), scaled(c2.unsigned_abs(), -k)?) };
    // `div_round`: floor((2n + d) / 2d), i.e. one more than `n / d` exactly when the remainder is at least half of `d`.
    let remainder = n % d;
    let quotient = n / d + u128::from(remainder >= d - remainder);
    let coeff = if (c1 < 0) != (c2 < 0) { 0i128.checked_sub_unsigned(quotient) } else { i128::try_from(quotient).ok() };
    Ok(Val::Num { coeff: coeff.ok_or(Stop::Capacity)?, scale })
}

// ---------------------------------------------------------------- characters and LIKE (`spec::chars`, `spec::fns::like`)

/// `chars`: a character is a byte that is not a UTF-8 continuation byte, with the continuation bytes after it; a
/// leading continuation byte is a character of its own.
pub(super) fn chars(b: &[u8]) -> Vec<&[u8]> {
    let is_cont = |x: u8| (0x80..0xC0).contains(&x);
    let starts: Vec<usize> = (0..b.len()).filter(|&i| i == 0 || !is_cont(b[i])).collect();
    starts.iter().enumerate().map(|(k, &s)| &b[s..starts.get(k + 1).copied().unwrap_or(b.len())]).collect()
}

/// Step 1 of `like_value`, PostgreSQL's `like_escape(p, e)`: it does not look at the subject. A NULL pattern or escape
/// passes (the result is NULL); an escape string of more than one character is 22025.
pub(super) fn like_escape(p: &Val, e: &Val) -> Outcome<()> {
    match (p, e) {
        (Val::Null, _) | (_, Val::Null) => Ok(()),
        (Val::Text(_), Val::Text(escape)) if chars(escape).len() > 1 => Err(Stop::Sql(SqlError::InvalidEscapeSequence)),
        (Val::Text(_), Val::Text(_)) => Ok(()),
        _ => Err(Stop::Undecided),
    }
}

/// `like_value`: `like_escape`, then a NULL subject gives NULL, then PostgreSQL's matcher.
fn like(s: &Val, p: &Val, e: &Val) -> Outcome<Val> {
    like_escape(p, e)?;
    match (s, p, e) {
        (_, Val::Null, _) | (_, _, Val::Null) | (Val::Null, Val::Text(_), Val::Text(_)) => Ok(Val::Null),
        (Val::Text(subject), Val::Text(pattern), Val::Text(escape)) => {
            let tokens = like_tokens(&chars(pattern), chars(escape).first().copied());
            Ok(Val::Bool(like_match(&chars(subject), &tokens)? == LikeRes::Match))
        }
        _ => Err(Stop::Undecided),
    }
}

/// `LikeTok`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Tok<'a> {
    Lit(&'a [u8]),
    One,
    Any,
    Dangling,
}

/// `LikeRes`: `MatchText`'s outcomes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LikeRes {
    Match,
    NoMatch,
    Abort,
}

/// `like_tokens`: the escape character followed by any character is that character literally; `%` any sequence; `_`
/// one character; an escape as the last character is dangling.
fn like_tokens<'a>(pc: &[&'a [u8]], escape: Option<&[u8]>) -> Vec<Tok<'a>> {
    let mut tokens = Vec::with_capacity(pc.len());
    let mut k = 0;
    while k < pc.len() {
        if Some(pc[k]) == escape {
            match pc.get(k + 1) {
                Some(c) => tokens.push(Tok::Lit(c)),
                None => tokens.push(Tok::Dangling),
            }
            k += 2;
        } else {
            tokens.push(match pc[k] {
                b"%" => Tok::Any,
                b"_" => Tok::One,
                c => Tok::Lit(c),
            });
            k += 1;
        }
    }
    tokens
}

/// A `like_mt` run up to its first `%`: an outcome, or the positions after the `%` where `like_any` continues.
enum Segment {
    Done(LikeRes),
    AfterAny { i: usize, j: usize },
}

/// `like_mt(t, p, i, j)` up to the first `%` token (literal and `_` steps, then the end-of-pattern / end-of-text rules,
/// `like_end`).
fn segment(t: &[&[u8]], p: &[Tok<'_>], mut i: usize, mut j: usize) -> Outcome<Segment> {
    loop {
        match (t.get(i), p.get(j)) {
            (Some(_), Some(Tok::Dangling)) => return Err(Stop::Sql(SqlError::InvalidEscapeSequence)),
            (Some(c), Some(Tok::Lit(l))) if c != l => return Ok(Segment::Done(LikeRes::NoMatch)),
            (Some(_), Some(Tok::Lit(_) | Tok::One)) => (i, j) = (i + 1, j + 1),
            (Some(_), Some(Tok::Any)) => return Ok(Segment::AfterAny { i, j: j + 1 }),
            (Some(_), None) => return Ok(Segment::Done(LikeRes::NoMatch)),
            // End of text: a match exactly when only `%`s are left.
            (None, _) => {
                let rest_any = p[j..].iter().all(|tok| *tok == Tok::Any);
                return Ok(Segment::Done(if rest_any { LikeRes::Match } else { LikeRes::Abort }));
            }
        }
    }
}

/// PostgreSQL's matcher `like_mt(t, p, 0, 0)`, without recursion. After a `%` (`like_any`), further `%`s and `_`s are
/// skipped; the end of the pattern matches, a dangling escape raises, and a literal starts the scan (`like_scan`): the
/// first text position whose run is not `NoMatch` decides, and a run that reaches the next `%` is final for the scan,
/// because `like_any` never answers `NoMatch`.
fn like_match(t: &[&[u8]], p: &[Tok<'_>]) -> Outcome<LikeRes> {
    let mut run = segment(t, p, 0, 0)?;
    loop {
        let (mut i, mut j) = match run {
            Segment::Done(result) => return Ok(result),
            Segment::AfterAny { i, j } => (i, j),
        };
        // `like_any`.
        loop {
            match p.get(j) {
                None => return Ok(LikeRes::Match),
                Some(Tok::Any) => j += 1,
                Some(Tok::One) if i < t.len() => (i, j) = (i + 1, j + 1),
                Some(Tok::One) => return Ok(LikeRes::Abort),
                Some(Tok::Dangling) => return Err(Stop::Sql(SqlError::InvalidEscapeSequence)),
                Some(Tok::Lit(_)) => break,
            }
        }
        // `like_scan` from text position `i`.
        run = Segment::Done(LikeRes::Abort);
        for k in i..t.len() {
            match segment(t, p, k, j)? {
                Segment::Done(LikeRes::NoMatch) => continue,
                decided => {
                    run = decided;
                    break;
                }
            }
        }
    }
}

// ---------------------------------------------------------------- SUBSTRING, EXTRACT, char(n) padding

/// `apply_substring` (strict, then 22011 for a negative length): the characters at 1-based positions
/// `max(start, 1) <= p < start + len`, to the end when `start + len` overflows int4 or without a length.
fn substring(f: &str, args: &[Val]) -> Outcome<Val> {
    if args.len() != if f == "Substring3" { 3 } else { 2 } {
        return Err(Stop::Undecided);
    }
    if args.contains(&Val::Null) {
        return Ok(Val::Null);
    }
    let (b, start, end) = match args {
        [Val::Text(b), Val::Int(start), Val::Int(len)] => {
            if *len < 0 {
                return Err(Stop::Sql(SqlError::SubstringError));
            }
            let end = i128::from(*start) + i128::from(*len);
            (b, i128::from(*start), (end <= INT4_MAX).then_some(end))
        }
        [Val::Text(b), Val::Int(start)] => (b, i128::from(*start), None),
        _ => return Err(Stop::Undecided),
    };
    // `char_range`.
    let cs = chars(b);
    let n = cs.len() as i128;
    let lo = (start - 1).clamp(0, n);
    let hi = end.map_or(n, |e| (e - 1).clamp(lo, n));
    Ok(Val::Text(cs[lo as usize..hi as usize].concat()))
}

/// `apply_extract`: the field of the civil date (a timestamp's day is `floor(t / USECS_PER_DAY)`) as numeric scale 0;
/// YEAR has no year 0 (1 BC is -1).
fn extract(f: &str, x: &Val) -> Outcome<Val> {
    let day = match x {
        Val::Null => return Ok(Val::Null),
        Val::Date(d) => i128::from(*d),
        Val::Ts(t) => i128::from(*t).div_euclid(USECS_PER_DAY),
        _ => return Err(Stop::Undecided),
    };
    let (y, m, d) = civil_from_date(day);
    let field = match f {
        "ExtractYear" if y > 0 => y,
        "ExtractYear" => y - 1,
        "ExtractMonth" => m,
        _ => d,
    };
    Ok(Val::Num { coeff: field, scale: 0 })
}

/// `apply_pad`: the text followed by spaces up to `n` characters (strict).
fn pad(s: &Val, n: &Val) -> Outcome<Val> {
    match (s, n) {
        (Val::Null, _) | (_, Val::Null) => Ok(Val::Null),
        (Val::Text(b), Val::Int(n)) => {
            let missing = (*n - chars(b).len() as i64).max(0) as usize;
            Ok(Val::Text([b.as_slice(), &vec![b' '; missing]].concat()))
        }
        _ => Err(Stop::Undecided),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn num(coeff: i128, scale: u32) -> Val {
        Val::Num { coeff, scale }
    }

    fn text(s: &str) -> Val {
        Val::Text(s.as_bytes().to_vec())
    }

    /// PostgreSQL 18's quotients and scales (`select_div_scale`, half away from zero), as probed.
    #[test]
    fn numeric_division_scales() {
        let third = 33333333333333333333;
        assert_eq!(num_div(1, 0, 3, 0), Ok(num(third, 20)));
        assert_eq!(num_div(2, 0, 3, 0), Ok(num(66666666666666666667, 20)));
        assert_eq!(num_div(-2, 0, 3, 0), Ok(num(-66666666666666666667, 20)));
        assert_eq!(num_div(50, 1, 2, 0), Ok(num(25000000000000000, 16)));
        assert_eq!(num_div(10000, 0, 3, 0), Ok(num(33333333333333333333, 16)));
        assert_eq!(num_div(1, 0, 10000, 0), Ok(num(100000000000000000000, 24)));
        assert_eq!(num_div(0, 0, 3, 0), Ok(num(0, 20)));
        assert_eq!(num_div(15000, 0, 10000, 0), Ok(num(150000000000000000000, 20)));
        // 0.5 / 10^21 is 5·10^-22 at scale 40 in SQLSpec, but its scaled dividend 5·10^39 leaves `u128`: `Capacity`.
        assert_eq!(div_scale(5, 1, 1000000000000000000000, 0), 40);
        assert_eq!(num_div(5, 1, 1000000000000000000000, 0), Err(Stop::Capacity));
        assert_eq!(num_div(1, 0, 0, 2), Err(Stop::Sql(SqlError::DivisionByZero)));
        assert_eq!(num_div(i128::MAX, 0, 1, 30), Err(Stop::Capacity));
        assert_eq!(div("DivInt4", &Val::Int(-7), &Val::Int(2)), Ok(Val::Int(-3)));
        assert_eq!(div("DivInt4", &Val::Int(-2147483648), &Val::Int(-1)), Err(Stop::Sql(SqlError::NumericValueOutOfRange)));
        assert_eq!(div("DivInt8", &Val::Int(0), &Val::Int(0)), Err(Stop::Sql(SqlError::DivisionByZero)));
    }

    /// LIKE: the escape check precedes the NULL subject; a dangling escape raises only when the matcher reaches it.
    #[test]
    fn like_follows_postgresql_order() {
        let invalid = Err(Stop::Sql(SqlError::InvalidEscapeSequence));
        assert_eq!(like(&text("a"), &text("a"), &text("xy")), invalid);
        assert_eq!(like(&Val::Null, &text("a"), &text("xy")), invalid);
        assert_eq!(like(&text("a"), &Val::Null, &text("xy")), Ok(Val::Null));
        assert_eq!(like(&text("ab"), &text("a\\"), &text("\\")), invalid);
        assert_eq!(like(&text("a"), &text("a\\"), &text("\\")), Ok(Val::Bool(false)));
        assert_eq!(like(&text("b"), &text("a\\"), &text("\\")), Ok(Val::Bool(false)));
        assert_eq!(like(&text("a%"), &text("a\\%"), &text("\\")), Ok(Val::Bool(true)));
        assert_eq!(like(&text("a\\b"), &text("a\\b"), &text("")), Ok(Val::Bool(true)));
        assert_eq!(like(&text("PROMO BRUSHED"), &text("PROMO%"), &text("\\")), Ok(Val::Bool(true)));
        assert_eq!(like(&text("special packages requests"), &text("%special%requests%"), &text("\\")), Ok(Val::Bool(true)));
        assert_eq!(like(&text("abc"), &text("%b_"), &text("\\")), Ok(Val::Bool(true)));
        assert_eq!(like(&text("abc"), &text("%x%"), &text("\\")), Ok(Val::Bool(false)));
        assert_eq!(like(&text("ä"), &text("_"), &text("\\")), Ok(Val::Bool(true)));
        assert_eq!(pad(&text("ab"), &Val::Int(4)), Ok(text("ab  ")));
    }

    /// SUBSTRING positions before 1, overflow of `start + len` and the negative length; EXTRACT of 1 BC.
    #[test]
    fn substring_and_extract() {
        assert_eq!(substring("Substring3", &[text("abcdef"), Val::Int(-1), Val::Int(3)]), Ok(text("a")));
        assert_eq!(substring("Substring2", &[text("abcdef"), Val::Int(0)]), Ok(text("abcdef")));
        assert_eq!(substring("Substring3", &[text("abcdef"), Val::Int(2), Val::Int(2147483647)]), Ok(text("bcdef")));
        assert_eq!(substring("Substring3", &[text("abc"), Val::Int(1), Val::Int(-1)]), Err(Stop::Sql(SqlError::SubstringError)));
        assert_eq!(substring("Substring3", &[Val::Null, Val::Int(1), Val::Int(-1)]), Ok(Val::Null));
        assert_eq!(substring("Substring3", &[text("abc"), Val::Int(7), Val::Int(2)]), Ok(text("")));
        let first_day = -730119; // 0001-01-01
        assert_eq!(extract("ExtractYear", &Val::Date(first_day - 1)), Ok(num(-1, 0)));
        assert_eq!(extract("ExtractDay", &Val::Ts((first_day - 1) * 86_400_000_000 + 5)), Ok(num(31, 0)));
    }
}
