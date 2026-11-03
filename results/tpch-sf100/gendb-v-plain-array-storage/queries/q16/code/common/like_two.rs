//! `LIKE` with the default backslash escape: on an ASCII pattern without backslash the value is a boolean (never an
//! error) given by standard matching over the pattern's characters (`lemma_like_plain`); and `s LIKE '%<a>%<b>%'`
//! on an ASCII text `s`, for non-empty ASCII literals `a`, `b` without `%`, `_` and backslash, is the byte test
//! "`a` occurs in `s`, and `b` occurs after the end of that occurrence" (`lemma_like_two`), with an executable
//! search for it (`has_two_exec`, `no_unwind`) that looks for `b` only after the first occurrence of `a`.
//!
//! Token view: every character of such a pattern is one byte, `%` becomes `Any`, `_` `One`, every other byte a
//! literal (`plain_tok`); the matcher never meets a dangling escape, so it is standard matching
//! (`bridge::fns::like::lemma_like_mt_std`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::chars::*;
use crate::spec::fns::like::*;
use crate::bridge::fns::like::{no_dangling, std_from, lemma_like_mt_std, lemma_std_any};

verus! {

// ------------------------------------------------------------------------------------------------ bytes

/// Every byte is ASCII (below 0x80): each is a character of its own.
pub open spec fn ascii(b: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < b.len() ==> #[trigger] b[i] < 0x80u8
}

/// `lit` occurs in `s` at byte `i`.
pub open spec fn sub_at(s: Seq<u8>, lit: Seq<u8>, i: int) -> bool {
    0 <= i && i + lit.len() <= s.len() && s.subrange(i, i + lit.len()) == lit
}

/// `lit` occurs in `s`.
pub open spec fn has_sub(s: Seq<u8>, lit: Seq<u8>) -> bool {
    exists|i: int| #[trigger] sub_at(s, lit, i)
}

/// `a` occurs in `s` at some byte `i` and `b` occurs in what follows that occurrence.
pub open spec fn has_two(s: Seq<u8>, a: Seq<u8>, b: Seq<u8>) -> bool {
    exists|i: int| #[trigger] sub_at(s, a, i) && has_sub(s.subrange(i + a.len(), s.len() as int), b)
}

/// A literal byte of a pattern: ASCII, and neither `%`, `_` nor backslash.
pub open spec fn lit_byte(c: u8) -> bool {
    c < 0x80u8 && c != 0x25u8 && c != 0x5Fu8 && c != 0x5Cu8
}

/// `%`, `m1 >= 1` literal bytes, `%`, `m2 >= 1` literal bytes, `%`.
pub open spec fn two_pattern(pat: Seq<u8>, m1: int, m2: int) -> bool {
    &&& m1 >= 1 && m2 >= 1
    &&& pat.len() == m1 + m2 + 3
    &&& pat[0] == 0x25u8 && pat[m1 + 1] == 0x25u8 && pat[m1 + m2 + 2] == 0x25u8
    &&& forall|i: int| 1 <= i <= m1 ==> #[trigger] lit_byte(pat[i])
    &&& forall|i: int| m1 + 2 <= i <= m1 + m2 + 1 ==> #[trigger] lit_byte(pat[i])
}

/// The two literals of a two-segment pattern.
pub open spec fn two_lit1(pat: Seq<u8>, m1: int) -> Seq<u8> { pat.subrange(1, m1 + 1) }
pub open spec fn two_lit2(pat: Seq<u8>, m1: int, m2: int) -> Seq<u8> { pat.subrange(m1 + 2, m1 + m2 + 2) }

/// An ASCII pattern without backslash.
pub open spec fn plain_pattern(pat: Seq<u8>) -> bool {
    ascii(pat) && forall|i: int| 0 <= i < pat.len() ==> #[trigger] pat[i] != 0x5Cu8
}

// ------------------------------------------------------------------------------------------------ characters

/// The characters of ASCII bytes are the single bytes.
pub proof fn lemma_chars_ascii(b: Seq<u8>)
    requires ascii(b),
    ensures chars(b) == Seq::new(b.len(), |i: int| seq![b[i]]),
    decreases b.len(),
{
    if b.len() > 0 {
        let d = b.drop_last();
        assert(ascii(d)) by {
            assert forall|i: int| 0 <= i < d.len() implies #[trigger] d[i] < 0x80u8 by { assert(d[i] == b[i]); }
        }
        lemma_chars_ascii(d);
        assert(b[b.len() - 1] < 0x80u8);
        assert(!is_cont(b.last()));
        assert(chars(b) =~= Seq::new(b.len(), |i: int| seq![b[i]]));
    } else {
        assert(chars(b) =~= Seq::new(b.len(), |i: int| seq![b[i]]));
    }
}

/// The escape character: a backslash.
pub open spec fn backslash_char() -> Seq<u8> { seq![0x5Cu8] }

/// The escape string `'\'` is the one character backslash.
pub proof fn lemma_escape_backslash()
    ensures chars(seq![92u8]) == seq![backslash_char()], escape_of(chars(seq![92u8])) == Some(backslash_char()),
{
    let bs = seq![92u8];
    assert(ascii(bs)) by { assert forall|i: int| 0 <= i < bs.len() implies #[trigger] bs[i] < 0x80u8 by {} }
    lemma_chars_ascii(bs);
    assert(chars(bs) =~= seq![backslash_char()]);
}

// ------------------------------------------------------------------------------------------------ tokens

/// The token of one character of a pattern without escapes.
pub open spec fn plain_tok(c: Seq<u8>) -> LikeTok {
    if c == pct() { LikeTok::Any } else if c == underscore() { LikeTok::One } else { LikeTok::Lit(c) }
}

/// Without a backslash character from `k` on, every character is its own token.
pub proof fn lemma_tokens_plain(pc: Seq<Seq<u8>>, k: int)
    requires
        0 <= k <= pc.len(),
        forall|i: int| k <= i < pc.len() ==> #[trigger] pc[i] != backslash_char(),
    ensures
        like_tokens(pc, Some(backslash_char()), k) == Seq::new((pc.len() - k) as nat, |j: int| plain_tok(pc[k + j])),
    decreases pc.len() - k,
{
    let esc = Some(backslash_char());
    if k < pc.len() {
        lemma_tokens_plain(pc, k + 1);
        assert(pc[k] != backslash_char());
        assert(like_tokens(pc, esc, k) =~= Seq::new((pc.len() - k) as nat, |j: int| plain_tok(pc[k + j])));
    } else {
        assert(like_tokens(pc, esc, k) =~= Seq::new((pc.len() - k) as nat, |j: int| plain_tok(pc[k + j])));
    }
}

/// The tokens of a plain pattern: one per byte, none dangling.
pub proof fn lemma_plain_tokens(pat: Seq<u8>)
    requires plain_pattern(pat),
    ensures ({
        let toks = like_tokens(chars(pat), Some(backslash_char()), 0);
        &&& toks == Seq::new(pat.len(), |j: int| plain_tok(seq![pat[j]]))
        &&& no_dangling(toks)
    }),
{
    lemma_chars_ascii(pat);
    let pc = chars(pat);
    assert forall|i: int| 0 <= i < pc.len() implies #[trigger] pc[i] != backslash_char() by {
        assert(pc[i] == seq![pat[i]]);
        if pc[i] == backslash_char() { assert(pc[i][0] == 0x5Cu8); }
    }
    lemma_tokens_plain(pc, 0);
    let toks = like_tokens(pc, Some(backslash_char()), 0);
    assert(toks =~= Seq::new(pat.len(), |j: int| plain_tok(seq![pat[j]])));
}

/// `s LIKE pat` (escape backslash) for a plain pattern: never an error, the standard meaning over characters.
pub proof fn lemma_like_plain(s: Seq<u8>, pat: Seq<u8>)
    requires plain_pattern(pat),
    ensures
        like_value(Val::Text(s), Val::Text(pat), Val::Text(seq![92u8]))
            == Ok::<Val, SqlError>(Val::Bool(like_std(chars(s), like_tokens(chars(pat), Some(backslash_char()), 0), 0, 0))),
{
    lemma_escape_backslash();
    lemma_plain_tokens(pat);
    let toks = like_tokens(chars(pat), Some(backslash_char()), 0);
    lemma_like_mt_std(chars(s), toks);
}

/// `s LIKE p` with the backslash escape is a boolean or the matcher's error (for any text and pattern).
pub proof fn lemma_like_shape(s: Seq<u8>, p: Seq<u8>)
    ensures ({
        let r = like_value(Val::Text(s), Val::Text(p), Val::Text(seq![92u8]));
        let m = like_mt(chars(s), like_tokens(chars(p), Some(backslash_char()), 0), 0, 0);
        &&& m is Ok ==> r == Ok::<Val, SqlError>(Val::Bool(m->Ok_0 is Match))
        &&& m is Err ==> r == Err::<Val, SqlError>(m->Err_0)
    }),
{
    lemma_escape_backslash();
}

// ------------------------------------------------------------------------------------------------ standard matching

/// A run of literal tokens `j..e` from text position `i`: the next `e - j` characters are those literals, and the
/// rest matches from token `e`.
pub proof fn lemma_std_run(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int, j: int, e: int)
    requires
        0 <= i <= t.len(), 0 <= j <= e <= p.len(),
        forall|q: int| j <= q < e ==> (#[trigger] p[q]) is Lit,
    ensures
        like_std(t, p, i, j) == (i + (e - j) <= t.len()
            && (forall|q: int| j <= q < e ==> #[trigger] t[i - j + q] == p[q]->Lit_0)
            && like_std(t, p, i + (e - j), e)),
    decreases e - j,
{
    if j < e {
        assert(p[j] is Lit);
        if i < t.len() {
            lemma_std_run(t, p, i + 1, j + 1, e);
            if like_std(t, p, i, j) {
                assert(t[i] == p[j]->Lit_0);
                assert forall|q: int| j <= q < e implies #[trigger] t[i - j + q] == p[q]->Lit_0 by {
                    if q > j {
                        assert(t[(i + 1) - (j + 1) + q] == p[q]->Lit_0);
                    }
                }
            }
            if i + (e - j) <= t.len() && (forall|q: int| j <= q < e ==> #[trigger] t[i - j + q] == p[q]->Lit_0)
                && like_std(t, p, i + (e - j), e) {
                assert(t[i - j + j] == p[j]->Lit_0);
                assert forall|q: int| j + 1 <= q < e implies #[trigger] t[(i + 1) - (j + 1) + q] == p[q]->Lit_0 by {
                    assert(t[i - j + q] == p[q]->Lit_0);
                }
            }
        }
    }
}

/// A final `%` matches every rest of the text.
pub proof fn lemma_std_last_any(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int)
    requires 0 <= i <= t.len(), p.len() >= 1, p[p.len() - 1] is Any,
    ensures like_std(t, p, i, p.len() - 1),
{
    lemma_std_any(t, p, i, p.len() - 1);
    assert(like_std(t, p, t.len() as int, p.len() as int));
    assert(std_from(t, p, i, p.len() as int));
}

/// The literal tokens `j..j + m` occur at character `k` of `t`.
pub open spec fn toks_at(t: Seq<Seq<u8>>, p: Seq<LikeTok>, j: int, m: int, k: int) -> bool {
    0 <= k && k + m <= t.len() && forall|q: int| j <= q < j + m ==> #[trigger] t[k - j + q] == p[q]->Lit_0
}

/// Tokens `%`, `m1` literals, `%`, `m2` literals, `%`: the text matches exactly when the first literals occur at
/// some character `k0` and the second ones at some character `k2 >= k0 + m1`.
pub proof fn lemma_std_two(t: Seq<Seq<u8>>, p: Seq<LikeTok>, m1: int, m2: int)
    requires
        m1 >= 1, m2 >= 1, p.len() == m1 + m2 + 3,
        p[0] is Any, p[m1 + 1] is Any, p[m1 + m2 + 2] is Any,
        forall|q: int| 1 <= q <= m1 ==> (#[trigger] p[q]) is Lit,
        forall|q: int| m1 + 2 <= q <= m1 + m2 + 1 ==> (#[trigger] p[q]) is Lit,
    ensures
        like_std(t, p, 0, 0) == exists|k0: int, k2: int| #[trigger] toks_at(t, p, 1, m1, k0) && k0 + m1 <= k2
            && #[trigger] toks_at(t, p, m1 + 2, m2, k2),
{
    let n = t.len() as int;
    lemma_std_any(t, p, 0, 0);
    if like_std(t, p, 0, 0) {
        let k0 = choose|k0: int| 0 <= k0 <= n && #[trigger] like_std(t, p, k0, 1);
        lemma_std_run(t, p, k0, 1, m1 + 1);
        let k1 = k0 + m1;
        lemma_std_any(t, p, k1, m1 + 1);
        let k2 = choose|k2: int| k1 <= k2 <= n && #[trigger] like_std(t, p, k2, m1 + 2);
        lemma_std_run(t, p, k2, m1 + 2, m1 + m2 + 2);
        assert(toks_at(t, p, 1, m1, k0));
        assert(toks_at(t, p, m1 + 2, m2, k2));
    }
    if exists|k0: int, k2: int| #[trigger] toks_at(t, p, 1, m1, k0) && k0 + m1 <= k2 && #[trigger] toks_at(t, p, m1 + 2, m2, k2) {
        let (k0, k2) = choose|k0: int, k2: int| #[trigger] toks_at(t, p, 1, m1, k0) && k0 + m1 <= k2
            && #[trigger] toks_at(t, p, m1 + 2, m2, k2);
        lemma_std_last_any(t, p, k2 + m2);
        lemma_std_run(t, p, k2, m1 + 2, m1 + m2 + 2);
        assert(like_std(t, p, k2, m1 + 2));
        lemma_std_any(t, p, k0 + m1, m1 + 1);
        assert(std_from(t, p, k0 + m1, m1 + 2));
        assert(like_std(t, p, k0 + m1, m1 + 1));
        lemma_std_run(t, p, k0, 1, m1 + 1);
        assert(like_std(t, p, k0, 1));
        assert(std_from(t, p, 0, 1));
    }
}

// ------------------------------------------------------------------------------------------------ the theorem

/// Literal characters at character `k` of an ASCII text are the literal bytes at byte `k`.
proof fn lemma_toks_bytes(s: Seq<u8>, pat: Seq<u8>, toks: Seq<LikeTok>, j: int, m: int, k: int)
    requires
        ascii(s),
        chars(s) == Seq::new(s.len(), |i: int| seq![s[i]]),
        0 <= j, j + m <= pat.len(), m >= 0, toks.len() == pat.len(),
        forall|q: int| j <= q < j + m ==> (#[trigger] toks[q]) == LikeTok::Lit(seq![pat[q]]),
    ensures toks_at(chars(s), toks, j, m, k) == sub_at(s, pat.subrange(j, j + m), k),
{
    let t = chars(s);
    let lit = pat.subrange(j, j + m);
    if toks_at(t, toks, j, m, k) {
        assert(s.subrange(k, k + m) =~= lit) by {
            assert forall|x: int| 0 <= x < m implies s.subrange(k, k + m)[x] == lit[x] by {
                let q = j + x;
                assert(t[k - j + q] == toks[q]->Lit_0);
                assert(t[k + x] == seq![s[k + x]]);
                assert(seq![s[k + x]][0] == seq![pat[q]][0]);
            }
        }
    }
    if sub_at(s, lit, k) {
        assert forall|q: int| j <= q < j + m implies #[trigger] t[k - j + q] == toks[q]->Lit_0 by {
            assert(t[k - j + q] == seq![s[k - j + q]]);
            assert(s.subrange(k, k + m)[q - j] == lit[q - j]);
        }
    }
}

/// `s LIKE pat` for a two-segment pattern and an ASCII text is the two-occurrence byte test.
pub proof fn lemma_like_two(s: Seq<u8>, pat: Seq<u8>, m1: int, m2: int)
    requires ascii(s), two_pattern(pat, m1, m2),
    ensures
        like_value(Val::Text(s), Val::Text(pat), Val::Text(seq![92u8]))
            == Ok::<Val, SqlError>(Val::Bool(has_two(s, two_lit1(pat, m1), two_lit2(pat, m1, m2)))),
{
    assert(plain_pattern(pat)) by {
        assert forall|i: int| 0 <= i < pat.len() implies #[trigger] pat[i] < 0x80u8 && pat[i] != 0x5Cu8 by {
            if 1 <= i <= m1 { assert(lit_byte(pat[i])); }
            else if m1 + 2 <= i <= m1 + m2 + 1 { assert(lit_byte(pat[i])); }
        }
    }
    lemma_like_plain(s, pat);
    lemma_plain_tokens(pat);
    let toks = like_tokens(chars(pat), Some(backslash_char()), 0);
    let t = chars(s);
    lemma_chars_ascii(s);
    assert forall|q: int| 0 <= q < pat.len() && #[trigger] pat[q] != 0x25u8 && lit_byte(pat[q])
        implies toks[q] == LikeTok::Lit(seq![pat[q]]) by {
        assert(toks[q] == plain_tok(seq![pat[q]]));
        if seq![pat[q]] == pct() { assert(seq![pat[q]][0] == 0x25u8); }
        if seq![pat[q]] == underscore() { assert(seq![pat[q]][0] == 0x5Fu8); }
    }
    assert forall|q: int| (q == 0 || q == m1 + 1 || q == m1 + m2 + 2) implies (#[trigger] toks[q]) is Any by {
        assert(toks[q] == plain_tok(seq![pat[q]]));
        assert(seq![pat[q]] =~= pct());
    }
    assert forall|q: int| 1 <= q <= m1 implies (#[trigger] toks[q]) == LikeTok::Lit(seq![pat[q]]) by {
        assert(lit_byte(pat[q]));
    }
    assert forall|q: int| m1 + 2 <= q <= m1 + m2 + 1 implies (#[trigger] toks[q]) == LikeTok::Lit(seq![pat[q]]) by {
        assert(lit_byte(pat[q]));
    }
    assert(toks[0] is Any && toks[m1 + 1] is Any && toks[m1 + m2 + 2] is Any);
    lemma_std_two(t, toks, m1, m2);
    let a = two_lit1(pat, m1);
    let b = two_lit2(pat, m1, m2);
    assert(a.len() == m1 && b.len() == m2);
    if like_std(t, toks, 0, 0) {
        let (k0, k2) = choose|k0: int, k2: int| #[trigger] toks_at(t, toks, 1, m1, k0) && k0 + m1 <= k2
            && #[trigger] toks_at(t, toks, m1 + 2, m2, k2);
        lemma_toks_bytes(s, pat, toks, 1, m1, k0);
        lemma_toks_bytes(s, pat, toks, m1 + 2, m2, k2);
        let rest = s.subrange(k0 + m1, s.len() as int);
        assert(rest.subrange(k2 - k0 - m1, k2 - k0 - m1 + m2) =~= s.subrange(k2, k2 + m2));
        assert(sub_at(rest, b, k2 - k0 - m1));
        assert(sub_at(s, a, k0));
        assert(has_two(s, a, b));
    }
    if has_two(s, a, b) {
        let k0 = choose|i: int| #[trigger] sub_at(s, a, i) && has_sub(s.subrange(i + a.len(), s.len() as int), b);
        let rest = s.subrange(k0 + m1, s.len() as int);
        let x = choose|x: int| #[trigger] sub_at(rest, b, x);
        let k2 = k0 + m1 + x;
        assert(rest.subrange(x, x + m2) =~= s.subrange(k2, k2 + m2));
        assert(sub_at(s, b, k2));
        lemma_toks_bytes(s, pat, toks, 1, m1, k0);
        lemma_toks_bytes(s, pat, toks, m1 + 2, m2, k2);
        assert(toks_at(t, toks, m1 + 2, m2, k2));
    }
}

// ------------------------------------------------------------------------------------------------ search

/// The first byte position of `lit` (`m >= 1` bytes) in `bytes[lo..hi]`, relative to `lo`, or `usize::MAX` when
/// it does not occur: a scan for the first byte, then a comparison.
pub fn find_sub(bytes: &[u8], lo: usize, hi: usize, lit: &Vec<u8>, m: usize) -> (r: usize)
    requires lo <= hi <= bytes@.len(), m == lit@.len(), m >= 1,
    ensures ({
        let s = bytes@.subrange(lo as int, hi as int);
        &&& r < usize::MAX ==> r + m <= hi - lo && sub_at(s, lit@, r as int)
            && forall|k: int| 0 <= k < r ==> !#[trigger] sub_at(s, lit@, k)
        &&& r == usize::MAX ==> forall|k: int| !#[trigger] sub_at(s, lit@, k)
    }),
    no_unwind
{
    let ghost s = bytes@.subrange(lo as int, hi as int);
    if hi - lo < m {
        proof {
            assert forall|k: int| !#[trigger] sub_at(s, lit@, k) by {}
        }
        return usize::MAX;
    }
    let last = hi - m;
    let p0 = lit[0];
    let mut i = lo;
    while i <= last
        invariant
            lo <= i <= last + 1, last + m == hi, hi <= bytes@.len(), m == lit@.len(), m >= 1, p0 == lit@[0],
            s == bytes@.subrange(lo as int, hi as int),
            forall|k: int| 0 <= k < i - lo ==> !#[trigger] sub_at(s, lit@, k),
        decreases last + 1 - i,
    {
        if bytes[i] == p0 {
            let mut k: usize = 1;
            while k < m && bytes[i + k] == lit[k]
                invariant
                    1 <= k <= m, i + m <= hi, hi <= bytes@.len(), m == lit@.len(), p0 == lit@[0], bytes@[i as int] == p0,
                    forall|j: int| 0 <= j < k ==> bytes@[i + j] == #[trigger] lit@[j],
                decreases m - k,
            {
                k = k + 1;
            }
            if k == m {
                proof {
                    assert(s.subrange(i - lo, i - lo + m) =~= lit@) by {
                        assert forall|j: int| 0 <= j < m implies s.subrange(i - lo, i - lo + m)[j] == lit@[j] by {
                            assert(s[i - lo + j] == bytes@[i + j]);
                        }
                    }
                }
                return i - lo;
            }
            proof {
                assert(!sub_at(s, lit@, i - lo)) by {
                    if sub_at(s, lit@, i - lo) {
                        assert(s.subrange(i - lo, i - lo + m)[k as int] == lit@[k as int]);
                        assert(s[i - lo + k] == bytes@[i + k]);
                    }
                }
            }
        } else {
            proof {
                assert(!sub_at(s, lit@, i - lo)) by {
                    if sub_at(s, lit@, i - lo) {
                        assert(s.subrange(i - lo, i - lo + m)[0] == lit@[0]);
                        assert(s[i - lo] == bytes@[i as int]);
                    }
                }
            }
        }
        i = i + 1;
    }
    proof {
        assert forall|k: int| !#[trigger] sub_at(s, lit@, k) by {
            if sub_at(s, lit@, k) {
                assert(k < i - lo);
            }
        }
    }
    usize::MAX
}

/// Whether `a` (`m1 >= 1` bytes) occurs in `bytes[lo..hi]` with `b` (`m2 >= 1` bytes) occurring after it
/// (`has_two`): `b` is searched only after the first occurrence of `a` (any later pair of occurrences gives one
/// after the first `a` too).
pub fn has_two_exec(bytes: &[u8], lo: usize, hi: usize, a: &Vec<u8>, m1: usize, b: &Vec<u8>, m2: usize) -> (r: bool)
    requires lo <= hi <= bytes@.len(), m1 == a@.len(), m2 == b@.len(), m1 >= 1, m2 >= 1,
    ensures r == has_two(bytes@.subrange(lo as int, hi as int), a@, b@),
    no_unwind
{
    let ghost s = bytes@.subrange(lo as int, hi as int);
    let i = find_sub(bytes, lo, hi, a, m1);
    if i == usize::MAX {
        proof {
            assert(!has_two(s, a@, b@)) by {
                if has_two(s, a@, b@) {
                    let k = choose|k: int| #[trigger] sub_at(s, a@, k) && has_sub(s.subrange(k + a@.len(), s.len() as int), b@);
                }
            }
        }
        return false;
    }
    let start = lo + i + m1;
    let j = find_sub(bytes, start, hi, b, m2);
    proof {
        let rest = s.subrange(i + m1, s.len() as int);
        assert(rest =~= bytes@.subrange(start as int, hi as int));
        if has_two(s, a@, b@) {
            let k = choose|k: int| #[trigger] sub_at(s, a@, k) && has_sub(s.subrange(k + a@.len(), s.len() as int), b@);
            assert(i <= k);
            let rk = s.subrange(k + m1, s.len() as int);
            let x = choose|x: int| #[trigger] sub_at(rk, b@, x);
            let y = (k - i) + x;
            assert(rk.subrange(x, x + b@.len()) =~= rest.subrange(y, y + b@.len()));
            assert(sub_at(rest, b@, y));
        }
    }
    if j < usize::MAX {
        proof {
            let rest = s.subrange(i + m1, s.len() as int);
            assert(sub_at(rest, b@, j as int));
            assert(sub_at(s, a@, i as int));
        }
        true
    } else {
        false
    }
}

/// Whether every byte of `bytes[lo..hi]` is ASCII (the OR of the bytes is below 0x80).
pub fn ascii_exec(bytes: &[u8], lo: usize, hi: usize) -> (r: bool)
    requires lo <= hi <= bytes@.len(),
    ensures r == ascii(bytes@.subrange(lo as int, hi as int)),
    no_unwind
{
    let mut acc: u8 = 0;
    let mut i = lo;
    while i < hi
        invariant
            lo <= i <= hi, hi <= bytes@.len(),
            acc < 0x80u8 <==> forall|k: int| lo <= k < i ==> #[trigger] bytes@[k] < 0x80u8,
        decreases hi - i,
    {
        let b = bytes[i];
        proof {
            assert((acc | b) < 0x80u8 <==> (acc < 0x80u8 && b < 0x80u8)) by (bit_vector);
        }
        acc = acc | b;
        i = i + 1;
    }
    proof {
        let s = bytes@.subrange(lo as int, hi as int);
        assert(ascii(s) <==> forall|k: int| lo <= k < hi ==> #[trigger] bytes@[k] < 0x80u8) by {
            if ascii(s) {
                assert forall|k: int| lo <= k < hi implies #[trigger] bytes@[k] < 0x80u8 by { assert(s[k - lo] == bytes@[k]); }
            }
            if forall|k: int| lo <= k < hi ==> #[trigger] bytes@[k] < 0x80u8 {
                assert forall|i: int| 0 <= i < s.len() implies #[trigger] s[i] < 0x80u8 by { assert(bytes@[lo + i] < 0x80u8); }
            }
        }
    }
    acc < 0x80u8
}

} // verus!
