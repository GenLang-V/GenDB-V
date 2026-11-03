//! `s LIKE p` on raw bytes inside worker tasks, and the trigram prefilter.
//!
//! - Token codes: the pattern tokens (`spec::fns::like::LikeTok`) as `u16` codes a worker can read without
//!   allocation (`code_ok`): a one-byte literal character is its byte, `_`, `%` and a dangling escape are
//!   `TOK_ONE`, `TOK_ANY`, `TOK_DANGLING`, a literal of several bytes is `TOK_WIDE`.
//! - The matcher `mt_b` / `any_b` / `scan_b` / `end_b` is PostgreSQL's `MatchText` (`like_mt` and friends) over the
//!   characters of an ASCII text, which are its single bytes (`lemma_ascii_chars`); it mirrors the spec functions
//!   step for step (loops for literal steps and `%` runs, recursion only from a scan into the rest).
//! - The prefilter: every three consecutive one-byte literal tokens of the pattern must occur as three consecutive
//!   bytes of any text the pattern matches, so their `trisig` bits (`need_of`) are set in the text's signature
//!   (`lemma_need_in_sig`); a row whose signature misses one of them does not match (`lemma_reject`).
//! - `lemma_like_err`: the only error the matcher raises is 22025 (`InvalidEscapeSequence`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::chars::*;
use crate::spec::fns::like::*;
use crate::bridge::fns::like::{no_dangling, lemma_like_mt_std};
use crate::exec::fns::like::{ETok, view_tok, view_toks};
use crate::stores::factext_trislice::interface::trisig::*;

verus! {

/// Code of `_`.
pub const TOK_ONE: u16 = 256;
/// Code of `%`.
pub const TOK_ANY: u16 = 257;
/// Code of a dangling escape.
pub const TOK_DANGLING: u16 = 258;
/// Code of a literal character of more than one byte.
pub const TOK_WIDE: u16 = 259;

/// Every byte is ASCII (below 0x80).
pub open spec fn is_ascii(t: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < t.len() ==> #[trigger] t[i] < 0x80u8
}

/// The single bytes of `t` as characters.
pub open spec fn byte_chars(t: Seq<u8>) -> Seq<Seq<u8>> {
    Seq::new(t.len(), |i: int| seq![t[i]])
}

/// The characters of an ASCII text are its bytes.
pub proof fn lemma_ascii_chars(t: Seq<u8>)
    requires is_ascii(t),
    ensures chars(t) == byte_chars(t),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(chars(t) =~= byte_chars(t));
    } else {
        let d = t.drop_last();
        assert(is_ascii(d)) by {
            assert forall|i: int| 0 <= i < d.len() implies #[trigger] d[i] < 0x80u8 by {
                assert(d[i] == t[i]);
            }
        }
        lemma_ascii_chars(d);
        assert(t[t.len() - 1] < 0x80u8);
        assert(!is_cont(t.last()));
        assert(byte_chars(t) =~= byte_chars(d).push(seq![t.last()]));
    }
}

/// Code `code` stands for token `tok`.
pub open spec fn code_ok(code: u16, tok: LikeTok) -> bool {
    match tok {
        LikeTok::Lit(c) => if c.len() == 1 { code == c[0] as u16 } else { code == TOK_WIDE },
        LikeTok::One => code == TOK_ONE,
        LikeTok::Any => code == TOK_ANY,
        LikeTok::Dangling => code == TOK_DANGLING,
    }
}

/// The codes stand for the tokens, one for one.
pub open spec fn codes_ok(codes: Seq<u16>, toks: Seq<LikeTok>) -> bool {
    &&& codes.len() == toks.len()
    &&& forall|j: int| 0 <= j < codes.len() ==> #[trigger] code_ok(codes[j], toks[j])
}

/// The codes of the tokens (calling thread).
pub fn token_codes(toks: &Vec<ETok>) -> (codes: Vec<u16>)
    ensures codes_ok(codes@, view_toks(toks@)),
{
    let mut codes: Vec<u16> = Vec::new();
    let mut j: usize = 0;
    while j < toks.len()
        invariant
            j <= toks.len(),
            codes@.len() == j,
            forall|q: int| 0 <= q < j ==> #[trigger] code_ok(codes@[q], view_toks(toks@)[q]),
        decreases toks.len() - j,
    {
        let code: u16 = match &toks[j] {
            ETok::Lit(c) => if c.len() == 1 { c[0] as u16 } else { TOK_WIDE },
            ETok::One => TOK_ONE,
            ETok::Any => TOK_ANY,
            ETok::Dangling => TOK_DANGLING,
        };
        assert(view_toks(toks@)[j as int] == view_tok(toks@[j as int]));
        codes.push(code);
        j = j + 1;
    }
    codes
}

/// No code is a dangling escape (calling thread).
pub fn has_dangling(codes: &Vec<u16>) -> (r: bool)
    ensures r == exists|j: int| 0 <= j < codes@.len() && #[trigger] codes@[j] == TOK_DANGLING,
{
    let mut j: usize = 0;
    while j < codes.len()
        invariant
            j <= codes.len(),
            forall|q: int| 0 <= q < j ==> #[trigger] codes@[q] != TOK_DANGLING,
        decreases codes.len() - j,
    {
        if codes[j] == TOK_DANGLING {
            return true;
        }
        j = j + 1;
    }
    false
}

/// Without a dangling code the tokens have no dangling escape.
pub proof fn lemma_no_dangling(codes: Seq<u16>, toks: Seq<LikeTok>)
    requires
        codes_ok(codes, toks),
        forall|j: int| 0 <= j < codes.len() ==> #[trigger] codes[j] != TOK_DANGLING,
    ensures no_dangling(toks),
{
    assert forall|k: int| 0 <= k < toks.len() implies !(#[trigger] toks[k] is Dangling) by {
        assert(code_ok(codes[k], toks[k]));
        assert(codes[k] != TOK_DANGLING);
    }
}

// ------------------------------------------------------------------------------------------------ the matcher

/// The characters of the ASCII text `bytes[lo..hi]`.
pub open spec fn tview(bytes: Seq<u8>, lo: int, hi: int) -> Seq<Seq<u8>> {
    byte_chars(bytes.subrange(lo, hi))
}

/// A one-byte character equals a token character exactly when it is that one byte.
proof fn lemma_char_eq(x: u8, c: Seq<u8>)
    ensures (seq![x] == c) == (c.len() == 1 && c[0] == x),
{
    if c.len() == 1 && c[0] == x {
        assert(seq![x] =~= c);
    }
}

/// The literal token `codes[j]` matches the text byte `x`.
fn lit_matches(code: u16, x: u8, Ghost(tok): Ghost<LikeTok>) -> (r: bool)
    requires code_ok(code, tok), tok is Lit,
    ensures r == (seq![x] == tok->Lit_0),
    no_unwind
{
    proof { lemma_char_eq(x, tok->Lit_0); }
    code < 256 && code as u8 == x
}

/// `like_mt(tview(bytes, lo, hi), p, i0, j0)`.
pub fn mt_b(bytes: &[u8], lo: usize, hi: usize, codes: &Vec<u16>, Ghost(p): Ghost<Seq<LikeTok>>, i0: usize, j0: usize)
    -> (r: Result<LikeRes, SqlError>)
    requires
        lo <= hi <= bytes@.len(),
        codes_ok(codes@, p),
        i0 <= hi - lo,
        j0 <= codes@.len(),
    ensures r == like_mt(tview(bytes@, lo as int, hi as int), p, i0 as int, j0 as int),
    decreases codes@.len() - j0, 0int, hi - lo - i0,
    no_unwind
{
    let ghost tv = tview(bytes@, lo as int, hi as int);
    let n = hi - lo;
    let m = codes.len();
    let mut i = i0;
    let mut j = j0;
    loop
        invariant
            lo <= hi <= bytes@.len(),
            n == hi - lo,
            m == codes@.len(),
            codes_ok(codes@, p),
            tv == tview(bytes@, lo as int, hi as int),
            i0 <= i <= n,
            j0 <= j <= m,
            like_mt(tv, p, i as int, j as int) == like_mt(tv, p, i0 as int, j0 as int),
        decreases m - j,
    {
        if i < n && j < m {
            let code = codes[j];
            assert(code_ok(code, p[j as int]));
            assert(tv[i as int] == seq![bytes@[lo + i]]);
            if code == TOK_DANGLING {
                return Err(SqlError::InvalidEscapeSequence);
            } else if code == TOK_ONE {
                i = i + 1;
                j = j + 1;
            } else if code == TOK_ANY {
                return any_b(bytes, lo, hi, codes, Ghost(p), i, j + 1);
            } else {
                if lit_matches(code, bytes[lo + i], Ghost(p[j as int])) {
                    i = i + 1;
                    j = j + 1;
                } else {
                    return Ok(LikeRes::NoMatch);
                }
            }
        } else if i < n {
            return Ok(LikeRes::NoMatch);
        } else {
            return end_b(codes, Ghost(p), j);
        }
    }
}

/// `like_any(tview(bytes, lo, hi), p, i0, j0)`.
pub fn any_b(bytes: &[u8], lo: usize, hi: usize, codes: &Vec<u16>, Ghost(p): Ghost<Seq<LikeTok>>, i0: usize, j0: usize)
    -> (r: Result<LikeRes, SqlError>)
    requires
        lo <= hi <= bytes@.len(),
        codes_ok(codes@, p),
        i0 <= hi - lo,
        j0 <= codes@.len(),
    ensures r == like_any(tview(bytes@, lo as int, hi as int), p, i0 as int, j0 as int),
    decreases codes@.len() - j0, 2int, hi - lo - i0,
    no_unwind
{
    let ghost tv = tview(bytes@, lo as int, hi as int);
    let n = hi - lo;
    let m = codes.len();
    let mut i = i0;
    let mut j = j0;
    loop
        invariant
            lo <= hi <= bytes@.len(),
            n == hi - lo,
            m == codes@.len(),
            codes_ok(codes@, p),
            tv == tview(bytes@, lo as int, hi as int),
            i0 <= i <= n,
            j0 <= j <= m,
            like_any(tv, p, i as int, j as int) == like_any(tv, p, i0 as int, j0 as int),
        decreases m - j,
    {
        if j < m {
            let code = codes[j];
            assert(code_ok(code, p[j as int]));
            if code == TOK_ANY {
                j = j + 1;
            } else if code == TOK_ONE {
                if i < n {
                    i = i + 1;
                    j = j + 1;
                } else {
                    return Ok(LikeRes::Abort);
                }
            } else if code == TOK_DANGLING {
                return Err(SqlError::InvalidEscapeSequence);
            } else {
                return scan_b(bytes, lo, hi, codes, Ghost(p), i, j);
            }
        } else {
            return Ok(LikeRes::Match);
        }
    }
}

/// `like_scan(tview(bytes, lo, hi), p, k0, j)`.
pub fn scan_b(bytes: &[u8], lo: usize, hi: usize, codes: &Vec<u16>, Ghost(p): Ghost<Seq<LikeTok>>, k0: usize, j: usize)
    -> (r: Result<LikeRes, SqlError>)
    requires
        lo <= hi <= bytes@.len(),
        codes_ok(codes@, p),
        k0 <= hi - lo,
        j <= codes@.len(),
    ensures r == like_scan(tview(bytes@, lo as int, hi as int), p, k0 as int, j as int),
    decreases codes@.len() - j, 1int, hi - lo - k0,
    no_unwind
{
    let ghost tv = tview(bytes@, lo as int, hi as int);
    let n = hi - lo;
    // A one-byte literal first token: positions holding another byte answer `NoMatch` at once.
    let first: u16 = if j < codes.len() { codes[j] } else { TOK_WIDE };
    let mut k = k0;
    while k < n
        invariant
            lo <= hi <= bytes@.len(),
            n == hi - lo,
            codes_ok(codes@, p),
            tv == tview(bytes@, lo as int, hi as int),
            k0 <= k <= n,
            j <= codes@.len(),
            j < codes@.len() ==> first == codes@[j as int],
            j >= codes@.len() ==> first == TOK_WIDE,
            like_scan(tv, p, k as int, j as int) == like_scan(tv, p, k0 as int, j as int),
        decreases n - k,
    {
        if first < 256 && bytes[lo + k] != first as u8 {
            proof {
                assert(j < codes@.len());
                assert(code_ok(codes@[j as int], p[j as int]));
                assert(p[j as int] is Lit);
                lemma_char_eq(bytes@[lo + k], p[j as int]->Lit_0);
                assert(tv[k as int] == seq![bytes@[lo + k]]);
                assert(like_mt(tv, p, k as int, j as int) == Ok::<LikeRes, SqlError>(LikeRes::NoMatch));
            }
            k = k + 1;
        } else {
            let r = mt_b(bytes, lo, hi, codes, Ghost(p), k, j);
            match r {
                Ok(LikeRes::NoMatch) => {
                    k = k + 1;
                },
                _ => {
                    return r;
                },
            }
        }
    }
    Ok(LikeRes::Abort)
}

/// `like_end(p, j0)`.
pub fn end_b(codes: &Vec<u16>, Ghost(p): Ghost<Seq<LikeTok>>, j0: usize) -> (r: Result<LikeRes, SqlError>)
    requires
        codes_ok(codes@, p),
        j0 <= codes@.len(),
    ensures r == like_end(p, j0 as int),
    no_unwind
{
    let m = codes.len();
    let mut j = j0;
    while j < m
        invariant
            m == codes@.len(),
            codes_ok(codes@, p),
            j0 <= j <= m,
            like_end(p, j as int) == like_end(p, j0 as int),
        decreases m - j,
    {
        assert(code_ok(codes@[j as int], p[j as int]));
        if codes[j] == TOK_ANY {
            j = j + 1;
        } else {
            return Ok(LikeRes::Abort);
        }
    }
    Ok(LikeRes::Match)
}

/// OR of the bytes `t[0 .. k]`.
pub open spec fn or_upto(t: Seq<u8>, k: int) -> u8
    decreases k,
{
    if k <= 0 { 0u8 } else { or_upto(t, k - 1) | t[k - 1] }
}

/// An OR is below 0x80 exactly when both operands are.
proof fn lemma_or_ascii(x: u8, y: u8)
    ensures ((x | y) < 0x80u8) == (x < 0x80u8 && y < 0x80u8),
{
    assert(((x | y) < 0x80u8) == (x < 0x80u8 && y < 0x80u8)) by (bit_vector);
}

/// The OR of a prefix is below 0x80 exactly when every byte of it is.
proof fn lemma_or_upto(t: Seq<u8>, k: int)
    requires 0 <= k <= t.len(),
    ensures (or_upto(t, k) < 0x80u8) == (forall|i: int| 0 <= i < k ==> #[trigger] t[i] < 0x80u8),
    decreases k,
{
    if k > 0 {
        lemma_or_upto(t, k - 1);
        lemma_or_ascii(or_upto(t, k - 1), t[k - 1]);
    }
}

/// `bytes[lo..hi]` is ASCII (an OR over the bytes, no early exit, so the loop vectorizes).
pub fn ascii_range(bytes: &[u8], lo: usize, hi: usize) -> (r: bool)
    requires lo <= hi <= bytes@.len(),
    ensures r == is_ascii(bytes@.subrange(lo as int, hi as int)),
    no_unwind
{
    let ghost t = bytes@.subrange(lo as int, hi as int);
    let mut acc: u8 = 0;
    let mut k = lo;
    while k < hi
        invariant
            lo <= k <= hi <= bytes@.len(),
            t == bytes@.subrange(lo as int, hi as int),
            acc == or_upto(t, k - lo),
        decreases hi - k,
    {
        assert(t[k - lo] == bytes@[k as int]);
        acc = acc | bytes[k];
        k = k + 1;
    }
    proof {
        lemma_or_upto(t, t.len() as int);
    }
    acc < 0x80u8
}

// ------------------------------------------------------------------------------------------------ errors

/// The matcher raises only 22025.
pub proof fn lemma_mt_err(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int, j: int)
    ensures like_mt(t, p, i, j) is Err ==> like_mt(t, p, i, j) == Err::<LikeRes, SqlError>(SqlError::InvalidEscapeSequence),
    decreases p.len() - j, 0int, t.len() - i,
{
    if 0 <= i < t.len() && 0 <= j < p.len() {
        match p[j] {
            LikeTok::Lit(c) => { if t[i] == c { lemma_mt_err(t, p, i + 1, j + 1); } },
            LikeTok::One => { lemma_mt_err(t, p, i + 1, j + 1); },
            LikeTok::Any => { lemma_any_err(t, p, i, j + 1); },
            LikeTok::Dangling => {},
        }
    } else if 0 <= i < t.len() {
    } else {
        lemma_end_ok(p, j);
    }
}

/// `like_any` raises only 22025.
pub proof fn lemma_any_err(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int, j: int)
    ensures like_any(t, p, i, j) is Err ==> like_any(t, p, i, j) == Err::<LikeRes, SqlError>(SqlError::InvalidEscapeSequence),
    decreases p.len() - j, 2int, t.len() - i,
{
    if 0 <= j < p.len() {
        match p[j] {
            LikeTok::Any => { lemma_any_err(t, p, i, j + 1); },
            LikeTok::One => { if 0 <= i < t.len() { lemma_any_err(t, p, i + 1, j + 1); } },
            LikeTok::Dangling => {},
            LikeTok::Lit(_) => { lemma_scan_err(t, p, i, j); },
        }
    }
}

/// `like_scan` raises only 22025.
pub proof fn lemma_scan_err(t: Seq<Seq<u8>>, p: Seq<LikeTok>, k: int, j: int)
    ensures like_scan(t, p, k, j) is Err ==> like_scan(t, p, k, j) == Err::<LikeRes, SqlError>(SqlError::InvalidEscapeSequence),
    decreases p.len() - j, 1int, t.len() - k,
{
    if 0 <= k < t.len() {
        lemma_mt_err(t, p, k, j);
        if like_mt(t, p, k, j) == Ok::<LikeRes, SqlError>(LikeRes::NoMatch) {
            lemma_scan_err(t, p, k + 1, j);
        }
    }
}

/// `like_end` never raises.
pub proof fn lemma_end_ok(p: Seq<LikeTok>, j: int)
    ensures like_end(p, j) is Ok,
    decreases p.len() - j,
{
    if 0 <= j < p.len() {
        if p[j] is Any {
            lemma_end_ok(p, j + 1);
        }
    }
}

// ------------------------------------------------------------------------------------------------ prefilter

/// Codes `j, j + 1, j + 2` are one-byte literals.
pub open spec fn tri_at(codes: Seq<u16>, j: int) -> bool {
    codes[j] < 256 && codes[j + 1] < 256 && codes[j + 2] < 256
}

/// Word `w` of the signature bit of the one-byte literal trigram at `j` (0 when there is none).
pub open spec fn tri_need(codes: Seq<u16>, j: int, w: int) -> u64 {
    if tri_at(codes, j) { tri_bit(codes[j] as u8, codes[j + 1] as u8, codes[j + 2] as u8, w) } else { 0u64 }
}

/// Word `w` of the OR of the bits of the literal trigrams starting before `j`.
pub open spec fn need_upto(codes: Seq<u16>, j: int, w: int) -> u64
    decreases j,
{
    if j <= 0 { 0u64 } else { need_upto(codes, j - 1, w) | tri_need(codes, j - 1, w) }
}

/// Word `w` of the signature bits every text the pattern matches has.
pub open spec fn need_of(codes: Seq<u16>, w: int) -> u64 {
    if codes.len() >= 3 { need_upto(codes, codes.len() - 2, w) } else { 0u64 }
}

/// Both words of `need_of(codes)`.
pub fn need_mask(codes: &Vec<u16>) -> (m: (u64, u64))
    ensures m.0 == need_of(codes@, 0), m.1 == need_of(codes@, 1),
{
    let len = codes.len();
    if len < 3 {
        return (0, 0);
    }
    let cnt = len - 2;
    let mut acc0: u64 = 0;
    let mut acc1: u64 = 0;
    let mut j: usize = 0;
    while j < cnt
        invariant
            len == codes@.len(),
            len >= 3,
            cnt == len - 2,
            j <= cnt,
            acc0 == need_upto(codes@, j as int, 0),
            acc1 == need_upto(codes@, j as int, 1),
        decreases cnt - j,
    {
        let (a, b, c) = (codes[j], codes[j + 1], codes[j + 2]);
        let (b0, b1): (u64, u64) = if a < 256 && b < 256 && c < 256 { tri_bits_exec(a as u8, b as u8, c as u8) } else { (0, 0) };
        acc0 = acc0 | b0;
        acc1 = acc1 | b1;
        j = j + 1;
    }
    (acc0, acc1)
}

/// A matching suffix `t[i..]` of the tokens `p[j0..]` (`j0 <= j`) contains the three one-character literals
/// `p[j], p[j + 1], p[j + 2]` as consecutive characters.
proof fn lemma_std_tri(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int, j0: int, j: int)
    requires
        like_std(t, p, i, j0),
        0 <= j0 <= j,
        j + 2 < p.len(),
        p[j] is Lit, p[j + 1] is Lit, p[j + 2] is Lit,
    ensures
        exists|q: int| 0 <= q && q + 2 < t.len() && #[trigger] t[q] == p[j]->Lit_0 && t[q + 1] == p[j + 1]->Lit_0
            && t[q + 2] == p[j + 2]->Lit_0,
    decreases (t.len() - i) + (p.len() - j0),
{
    if j0 == j {
        assert(like_std(t, p, i + 1, j + 1));
        assert(like_std(t, p, i + 2, j + 2));
        assert(t[i] == p[j]->Lit_0);
    } else {
        match p[j0] {
            LikeTok::Lit(_) => { lemma_std_tri(t, p, i + 1, j0 + 1, j); },
            LikeTok::One => { lemma_std_tri(t, p, i + 1, j0 + 1, j); },
            LikeTok::Any => {
                if like_std(t, p, i, j0 + 1) {
                    lemma_std_tri(t, p, i, j0 + 1, j);
                } else {
                    lemma_std_tri(t, p, i + 1, j0, j);
                }
            },
            LikeTok::Dangling => {},
        }
    }
}

/// `concat` of a concatenation.
proof fn lemma_concat_append(a: Seq<Seq<u8>>, b: Seq<Seq<u8>>)
    ensures concat(a + b) == concat(a) + concat(b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(concat(a) + concat(b) =~= concat(a));
    } else {
        lemma_concat_append(a, b.drop_last());
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
        assert(concat(a) + concat(b) =~= concat(a) + concat(b.drop_last()) + b.last());
    }
}

/// Three consecutive one-byte characters of a text are three consecutive bytes of it.
proof fn lemma_chars_tri(text: Seq<u8>, q: int, x: u8, y: u8, z: u8)
    requires
        0 <= q,
        q + 2 < chars(text).len(),
        chars(text)[q] == seq![x],
        chars(text)[q + 1] == seq![y],
        chars(text)[q + 2] == seq![z],
    ensures
        exists|pos: int| 0 <= pos && pos + 2 < text.len() && #[trigger] text[pos] == x && text[pos + 1] == y && text[pos + 2] == z,
{
    let cs = chars(text);
    lemma_concat_chars(text);
    let pre = cs.subrange(0, q);
    let mid = cs.subrange(q, q + 3);
    let post = cs.subrange(q + 3, cs.len() as int);
    assert(cs =~= pre + mid + post);
    lemma_concat_append(pre + mid, post);
    lemma_concat_append(pre, mid);
    assert(mid =~= seq![seq![x], seq![y], seq![z]]);
    assert(concat(mid) =~= seq![x, y, z]) by {
        let m1 = mid.drop_last();
        let m2 = m1.drop_last();
        let m3 = m2.drop_last();
        assert(m3 =~= Seq::<Seq<u8>>::empty());
        assert(concat(m3) =~= Seq::<u8>::empty());
        assert(m2.last() == seq![x]);
        assert(m1.last() == seq![y]);
        assert(mid.last() == seq![z]);
        assert(concat(m2) == concat(m3) + m2.last());
        assert(concat(m2) =~= seq![x]);
        assert(concat(m1) == concat(m2) + m1.last());
        assert(concat(m1) =~= seq![x, y]);
        assert(concat(mid) == concat(m1) + mid.last());
    }
    let pos = concat(pre).len() as int;
    assert(text == concat(pre) + concat(mid) + concat(post));
    assert(text[pos] == x);
    assert(text[pos + 1] == y);
    assert(text[pos + 2] == z);
}

/// AND-ing with a mask keeps the union of two kept masks.
proof fn lemma_and_or(s: u64, a: u64, b: u64)
    requires s & a == a, s & b == b,
    ensures s & (a | b) == (a | b),
{
    assert((s & a == a && s & b == b) ==> (s & (a | b) == (a | b))) by (bit_vector);
}

/// Every text a token sequence (with codes `codes`) matches has the needed signature bits (both words).
pub proof fn lemma_need_in_sig(text: Seq<u8>, codes: Seq<u16>, p: Seq<LikeTok>, w: int)
    requires
        codes_ok(codes, p),
        like_std(chars(text), p, 0, 0),
    ensures
        sig_of(text, w) & need_of(codes, w) == need_of(codes, w),
{
    let s = sig_of(text, w);
    if codes.len() >= 3 {
        lemma_need_upto(text, codes, p, codes.len() - 2, w);
    } else {
        assert(s & 0u64 == 0u64) by (bit_vector);
    }
}

/// The prefix form of `lemma_need_in_sig`.
proof fn lemma_need_upto(text: Seq<u8>, codes: Seq<u16>, p: Seq<LikeTok>, j: int, w: int)
    requires
        codes_ok(codes, p),
        like_std(chars(text), p, 0, 0),
        0 <= j <= codes.len() - 2,
    ensures
        sig_of(text, w) & need_upto(codes, j, w) == need_upto(codes, j, w),
    decreases j,
{
    let s = sig_of(text, w);
    if j <= 0 {
        assert(s & 0u64 == 0u64) by (bit_vector);
    } else {
        lemma_need_upto(text, codes, p, j - 1, w);
        let k = j - 1;
        if tri_at(codes, k) {
            assert(code_ok(codes[k], p[k]));
            assert(code_ok(codes[k + 1], p[k + 1]));
            assert(code_ok(codes[k + 2], p[k + 2]));
            let (x, y, z) = (codes[k] as u8, codes[k + 1] as u8, codes[k + 2] as u8);
            assert(p[k] is Lit && p[k + 1] is Lit && p[k + 2] is Lit);
            lemma_char_eq(x, p[k]->Lit_0);
            lemma_char_eq(y, p[k + 1]->Lit_0);
            lemma_char_eq(z, p[k + 2]->Lit_0);
            let t = chars(text);
            lemma_std_tri(t, p, 0, 0, k);
            let q = choose|q: int| 0 <= q && q + 2 < t.len() && #[trigger] t[q] == p[k]->Lit_0 && t[q + 1] == p[k + 1]->Lit_0
                && t[q + 2] == p[k + 2]->Lit_0;
            lemma_chars_tri(text, q, x, y, z);
            let pos = choose|pos: int| 0 <= pos && pos + 2 < text.len() && #[trigger] text[pos] == x && text[pos + 1] == y
                && text[pos + 2] == z;
            lemma_sig_has(text, pos, w);
            lemma_and_or(s, need_upto(codes, k, w), tri_need(codes, k, w));
        } else {
            assert(s & 0u64 == 0u64) by (bit_vector);
            lemma_and_or(s, need_upto(codes, k, w), 0u64);
        }
    }
}

/// The text's signature misses a needed bit in word 0 or 1.
pub open spec fn rejects(s0: u64, s1: u64, n0: u64, n1: u64) -> bool {
    s0 & n0 != n0 || s1 & n1 != n1
}

/// A row whose signature misses a needed bit does not match (without dangling escapes the matcher returns).
pub proof fn lemma_reject(text: Seq<u8>, codes: Seq<u16>, p: Seq<LikeTok>)
    requires
        codes_ok(codes, p),
        no_dangling(p),
        rejects(sig_of(text, 0), sig_of(text, 1), need_of(codes, 0), need_of(codes, 1)),
    ensures
        like_mt(chars(text), p, 0, 0) is Ok,
        like_mt(chars(text), p, 0, 0) != Ok::<LikeRes, SqlError>(LikeRes::Match),
{
    lemma_like_mt_std(chars(text), p);
    if like_std(chars(text), p, 0, 0) {
        lemma_need_in_sig(text, codes, p, 0);
        lemma_need_in_sig(text, codes, p, 1);
    }
}

} // verus!
