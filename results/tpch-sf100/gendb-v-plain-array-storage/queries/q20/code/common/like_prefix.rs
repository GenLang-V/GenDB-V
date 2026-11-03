//! `s LIKE 'lit%'` (escape backslash) as a byte test: for a pattern of at least one ASCII byte that is neither `%`,
//! `_` nor backslash, followed by one `%` (`prefix_pattern`), the value is `true` exactly when `s` starts with the
//! bytes of `lit` and the byte after them, if any, is not a UTF-8 continuation byte (`prefix_match`,
//! `lemma_like_prefix`); it never raises. `prefix_match_at` decides it on a byte range (`no_unwind`, for workers).
//!
//! Why the byte after the prefix matters: LIKE matches characters (`spec::chars`), and a continuation byte after
//! the prefix would belong to the prefix's last character, which then is not the single ASCII character of `lit`.
//! Proof: the pattern's characters are its bytes, its tokens are one literal per byte of `lit` then `%`, the matcher
//! is standard matching (`bridge::fns::like::lemma_like_mt_std`), and the characters of `s` begin with the bytes of
//! `lit` exactly under `prefix_match` (`lemma_chars_append`, `lemma_char_starts`, `lemma_concat_chars`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::chars::*;
use crate::spec::fns::like::*;
use crate::bridge::fns::like::{no_dangling, lemma_like_mt_std};

verus! {

// ------------------------------------------------------------------------------------------------ the test

/// `lit%`: at least one ASCII byte that is neither `%`, `_` nor backslash, then one `%`.
pub open spec fn prefix_pattern(pat: Seq<u8>) -> bool {
    &&& pat.len() >= 2
    &&& pat[pat.len() - 1] == 0x25u8
    &&& forall|i: int| 0 <= i < pat.len() - 1 ==> #[trigger] pat[i] < 0x80u8 && pat[i] != 0x25u8 && pat[i] != 0x5Fu8 && pat[i] != 0x5Cu8
}

/// The literal of a prefix pattern.
pub open spec fn prefix_lit(pat: Seq<u8>) -> Seq<u8> { pat.subrange(0, pat.len() - 1) }

/// `s` begins with `lit`, and the byte after it (if any) is not a continuation byte.
pub open spec fn prefix_match(s: Seq<u8>, lit: Seq<u8>) -> bool {
    &&& s.len() >= lit.len()
    &&& s.subrange(0, lit.len() as int) == lit
    &&& (s.len() == lit.len() || !is_cont(s[lit.len() as int]))
}

/// The backslash escape string.
pub open spec fn backslash() -> Seq<u8> { seq![0x5Cu8] }

// ------------------------------------------------------------------------------------------------ characters

/// A non-empty text has a character.
proof fn lemma_chars_len(b: Seq<u8>)
    ensures b.len() > 0 ==> chars(b).len() > 0,
{
}

/// The characters of an ASCII text are its bytes.
proof fn lemma_chars_ascii(b: Seq<u8>)
    requires forall|i: int| 0 <= i < b.len() ==> #[trigger] b[i] < 0x80u8,
    ensures chars(b) == Seq::new(b.len(), |i: int| seq![b[i]]),
    decreases b.len(),
{
    if b.len() > 0 {
        let d = b.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies #[trigger] d[i] < 0x80u8 by { assert(d[i] == b[i]); }
        lemma_chars_ascii(d);
        assert(!is_cont(b.last()));
        assert(chars(b) =~= Seq::new(b.len(), |i: int| seq![b[i]]));
    } else {
        assert(chars(b) =~= Seq::new(b.len(), |i: int| seq![b[i]]));
    }
}

/// Text that starts with a non-continuation byte begins a new character: the characters of `a + b` are those of
/// `a` followed by those of `b`.
proof fn lemma_chars_append(a: Seq<u8>, b: Seq<u8>)
    requires b.len() == 0 || !is_cont(b[0]),
    ensures chars(a + b) == chars(a) + chars(b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(chars(a) + chars(b) =~= chars(a));
    } else {
        let d = b.drop_last();
        let x = b.last();
        assert((a + b).drop_last() =~= a + d);
        assert((a + b).last() == x);
        if d.len() == 0 {
            assert(a + d =~= a);
            assert(b =~= seq![x]);
            assert(chars(d) =~= Seq::<Seq<u8>>::empty());
            assert(chars(b) =~= seq![seq![x]]);
            assert(chars(a + b) =~= chars(a) + chars(b));
        } else {
            assert(d[0] == b[0]);
            lemma_chars_append(a, d);
            lemma_chars_len(d);
            let cs = chars(d);
            let ca = chars(a);
            assert((ca + cs).len() > 0);
            if is_cont(x) {
                assert((ca + cs).last() == cs.last());
                assert((ca + cs).drop_last() =~= ca + cs.drop_last());
                assert(chars(a + b) =~= chars(a) + chars(b));
            } else {
                assert(chars(a + b) =~= chars(a) + chars(b));
            }
        }
    }
}

/// Every character after the first starts with a non-continuation byte.
proof fn lemma_char_starts(b: Seq<u8>)
    ensures
        forall|k: int| 0 <= k < chars(b).len() ==> #[trigger] chars(b)[k].len() > 0,
        forall|k: int| 1 <= k < chars(b).len() ==> !is_cont(#[trigger] chars(b)[k][0]),
    decreases b.len(),
{
    lemma_chars_nonempty(b);
    if b.len() > 0 {
        let d = b.drop_last();
        lemma_char_starts(d);
        let cs = chars(d);
        let x = b.last();
        let r = chars(b);
        if is_cont(x) && cs.len() > 0 {
            assert forall|k: int| 1 <= k < r.len() implies !is_cont(#[trigger] r[k][0]) by {
                if k < r.len() - 1 {
                    assert(r[k] == cs[k]);
                } else {
                    assert(r[k] == cs.last().push(x));
                    assert(cs.last() == cs[cs.len() - 1]);
                    assert(r[k][0] == cs[k][0]);
                }
            }
        } else {
            assert forall|k: int| 1 <= k < r.len() implies !is_cont(#[trigger] r[k][0]) by {
                if k < r.len() - 1 {
                    assert(r[k] == cs[k]);
                } else {
                    assert(r[k] == seq![x]);
                }
            }
        }
    }
}

/// Concatenation distributes over appended character lists.
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
        assert(concat(a + b) =~= concat(a) + concat(b));
    }
}

/// Characters that are the single bytes of `lit` spell `lit`.
proof fn lemma_concat_singles(t: Seq<Seq<u8>>, lit: Seq<u8>)
    requires t.len() == lit.len(), forall|j: int| 0 <= j < t.len() ==> #[trigger] t[j] == seq![lit[j]],
    ensures concat(t) == lit,
    decreases t.len(),
{
    if t.len() > 0 {
        let d = t.drop_last();
        let dl = lit.drop_last();
        assert forall|j: int| 0 <= j < d.len() implies #[trigger] d[j] == seq![dl[j]] by {
            assert(d[j] == t[j]);
        }
        lemma_concat_singles(d, dl);
        assert(t.last() == t[t.len() - 1]);
        assert(concat(t) =~= lit);
    } else {
        assert(concat(t) =~= lit);
    }
}

// ------------------------------------------------------------------------------------------------ tokens and matching

/// The tokens of `lit%`: one literal per byte of `lit`, then `%`.
pub open spec fn prefix_toks(lit: Seq<u8>) -> Seq<LikeTok> {
    Seq::new(lit.len(), |i: int| LikeTok::Lit(seq![lit[i]])).push(LikeTok::Any)
}

/// The tokens of a prefix pattern from position `i` on.
proof fn lemma_tokens_from(pat: Seq<u8>, i: int)
    requires prefix_pattern(pat), 0 <= i < pat.len(),
    ensures ({
        let pc = Seq::new(pat.len(), |m: int| seq![pat[m]]);
        let lit = prefix_lit(pat);
        like_tokens(pc, Some(backslash()), i) == prefix_toks(lit).subrange(i, pat.len() as int)
    }),
    decreases pat.len() - i,
{
    let pc = Seq::new(pat.len(), |m: int| seq![pat[m]]);
    let lit = prefix_lit(pat);
    let toks = prefix_toks(lit);
    let n = pat.len() as int;
    if i == n - 1 {
        assert(pc[i] == seq![0x25u8]);
        assert(pc[i] != backslash()) by { assert(pc[i][0] != backslash()[0]); }
        assert(pc[i] == pct());
        assert(like_tokens(pc, Some(backslash()), i + 1) =~= Seq::<LikeTok>::empty());
        assert(like_tokens(pc, Some(backslash()), i) =~= seq![LikeTok::Any]);
        assert(toks.subrange(i, n) =~= seq![LikeTok::Any]);
    } else {
        lemma_tokens_from(pat, i + 1);
        let c = pat[i];
        assert(c < 0x80u8 && c != 0x25u8 && c != 0x5Fu8 && c != 0x5Cu8);
        assert(pc[i] == seq![c]);
        assert(pc[i] != backslash()) by { assert(pc[i][0] != backslash()[0]); }
        assert(pc[i] != pct()) by { assert(pc[i][0] != pct()[0]); }
        assert(pc[i] != underscore()) by { assert(pc[i][0] != underscore()[0]); }
        assert(lit[i] == c);
        assert(like_tokens(pc, Some(backslash()), i) =~= seq![LikeTok::Lit(pc[i])] + like_tokens(pc, Some(backslash()), i + 1));
        assert(toks.subrange(i, n) =~= seq![LikeTok::Lit(seq![c])] + toks.subrange(i + 1, n));
    }
}

/// Standard matching of `lit%` from token `j` (at text position `i == j`): the next characters are those of `lit`.
proof fn lemma_std_prefix(t: Seq<Seq<u8>>, lit: Seq<u8>, j: int)
    requires 0 <= j <= lit.len(),
    ensures like_std(t, prefix_toks(lit), j, j) == (t.len() >= lit.len()
        && forall|m: int| j <= m < lit.len() ==> #[trigger] t[m] == seq![lit[m]]),
    decreases lit.len() - j,
{
    let p = prefix_toks(lit);
    let k = lit.len() as int;
    if j == k {
        lemma_std_any_rest(t, p, j);
    } else {
        lemma_std_prefix(t, lit, j + 1);
        assert(p[j] == LikeTok::Lit(seq![lit[j]]));
        if like_std(t, p, j, j) {
            assert(j < t.len() && t[j] == seq![lit[j]]);
        }
    }
}

/// The final `%` matches every rest of the text.
proof fn lemma_std_any_rest(t: Seq<Seq<u8>>, p: Seq<LikeTok>, j: int)
    requires 0 <= j, j == p.len() - 1, p[j] is Any,
    ensures like_std(t, p, j, j) == (j <= t.len()),
{
    if j <= t.len() {
        lemma_std_any_from(t, p, j, j);
    }
}

/// The final `%` (token `j`, the last) matches the text from any position `i <= |t|`.
proof fn lemma_std_any_from(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int, j: int)
    requires 0 <= j <= i <= t.len(), j == p.len() - 1, p[j] is Any,
    ensures like_std(t, p, i, j),
    decreases t.len() - i,
{
    if i < t.len() {
        lemma_std_any_from(t, p, i + 1, j);
    } else {
        assert(like_std(t, p, i, j + 1));
    }
}

/// The characters of `s` begin with the bytes of `lit` (as single characters) exactly under `prefix_match`.
proof fn lemma_chars_prefix(s: Seq<u8>, lit: Seq<u8>)
    requires lit.len() >= 1, forall|i: int| 0 <= i < lit.len() ==> #[trigger] lit[i] < 0x80u8,
    ensures (chars(s).len() >= lit.len() && forall|m: int| 0 <= m < lit.len() ==> #[trigger] chars(s)[m] == seq![lit[m]])
        == prefix_match(s, lit),
{
    let k = lit.len() as int;
    let t = chars(s);
    if prefix_match(s, lit) {
        let rest = s.subrange(k, s.len() as int);
        assert(s =~= lit + rest);
        lemma_chars_append(lit, rest);
        lemma_chars_ascii(lit);
        assert forall|m: int| 0 <= m < k implies #[trigger] t[m] == seq![lit[m]] by {
            assert(t[m] == chars(lit)[m]);
        }
    }
    if t.len() >= k && forall|m: int| 0 <= m < k ==> #[trigger] t[m] == seq![lit[m]] {
        lemma_concat_chars(s);
        let a = t.subrange(0, k);
        let b = t.subrange(k, t.len() as int);
        assert(t =~= a + b);
        lemma_concat_append(a, b);
        lemma_concat_singles(a, lit);
        assert(s == lit + concat(b));
        assert(s.subrange(0, k) =~= lit);
        if s.len() > k {
            lemma_char_starts(s);
            assert(b.len() > 0) by {
                if b.len() == 0 {
                    assert(concat(b) =~= Seq::<u8>::empty());
                }
            }
            let c0 = b[0];
            assert(c0 == t[k]);
            assert(c0.len() > 0);
            assert(b =~= seq![c0] + b.subrange(1, b.len() as int));
            lemma_concat_append(seq![c0], b.subrange(1, b.len() as int));
            assert(concat(seq![c0]) =~= c0) by {
                let one = seq![c0];
                assert(one.drop_last() =~= Seq::<Seq<u8>>::empty());
                assert(concat(one.drop_last()) =~= Seq::<u8>::empty());
                assert(one.last() == c0);
                assert(concat(one) == concat(one.drop_last()) + one.last());
                assert(Seq::<u8>::empty() + c0 =~= c0);
            }
            assert(s[k] == concat(b)[0]);
            assert(concat(b)[0] == c0[0]);
            assert(!is_cont(t[k][0]));
        }
    }
}

/// `s LIKE 'lit%'` is `prefix_match(s, lit)`, and never raises.
pub proof fn lemma_like_prefix(s: Seq<u8>, pat: Seq<u8>)
    requires prefix_pattern(pat),
    ensures like_value(Val::Text(s), Val::Text(pat), Val::Text(backslash())) == Ok::<Val, SqlError>(Val::Bool(prefix_match(s, prefix_lit(pat)))),
{
    let lit = prefix_lit(pat);
    let k = lit.len() as int;
    // the characters of the pattern and of the escape
    assert forall|i: int| 0 <= i < pat.len() implies #[trigger] pat[i] < 0x80u8 by {
        if i < pat.len() - 1 {} else {}
    }
    lemma_chars_ascii(pat);
    let pc = Seq::new(pat.len(), |m: int| seq![pat[m]]);
    lemma_chars_ascii(backslash());
    assert(chars(backslash()) =~= seq![seq![0x5Cu8]]);
    assert(escape_of(chars(backslash())) == Some(backslash()));
    // the tokens
    lemma_tokens_from(pat, 0);
    let toks = prefix_toks(lit);
    assert(toks.subrange(0, pat.len() as int) =~= toks);
    assert(like_tokens(chars(pat), escape_of(chars(backslash())), 0) == toks);
    assert(no_dangling(toks)) by {
        assert forall|m: int| 0 <= m < toks.len() implies !(#[trigger] toks[m] is Dangling) by {
            if m < k {} else {}
        }
    }
    // the matcher is standard matching
    let t = chars(s);
    lemma_like_mt_std(t, toks);
    lemma_std_prefix(t, lit, 0);
    assert forall|i: int| 0 <= i < lit.len() implies #[trigger] lit[i] < 0x80u8 by {}
    lemma_chars_prefix(s, lit);
}

// ------------------------------------------------------------------------------------------------ executable

/// Whether `pat` is a prefix pattern.
pub fn prefix_pattern_exec(pat: &[u8]) -> (r: bool)
    ensures r == prefix_pattern(pat@),
{
    let n = pat.len();
    if n < 2 || pat[n - 1] != 0x25u8 {
        return false;
    }
    let mut i: usize = 0;
    while i < n - 1
        invariant
            n == pat@.len(), n >= 2, i <= n - 1,
            forall|j: int| 0 <= j < i ==> #[trigger] pat@[j] < 0x80u8 && pat@[j] != 0x25u8 && pat@[j] != 0x5Fu8 && pat@[j] != 0x5Cu8,
        decreases n - 1 - i,
    {
        let c = pat[i];
        if c >= 0x80u8 || c == 0x25u8 || c == 0x5Fu8 || c == 0x5Cu8 {
            return false;
        }
        i = i + 1;
    }
    true
}

/// `prefix_match` on the bytes `[s, e)` of `bytes` (`no_unwind`): the first `lit` bytes, then the next byte.
pub fn prefix_match_at(bytes: &[u8], blen: usize, s: usize, e: usize, lit: &Vec<u8>, k: usize) -> (r: bool)
    requires s <= e <= blen, blen == bytes@.len(), k == lit@.len(),
    ensures r == prefix_match(bytes@.subrange(s as int, e as int), lit@),
    no_unwind
{
    let ghost v = bytes@.subrange(s as int, e as int);
    if e - s < k {
        return false;
    }
    let mut j: usize = 0;
    while j < k
        invariant
            s <= e <= blen, blen == bytes@.len(), k == lit@.len(), j <= k, e - s >= k,
            v == bytes@.subrange(s as int, e as int),
            forall|m: int| 0 <= m < j ==> #[trigger] v[m] == lit@[m],
        decreases k - j,
    {
        if bytes[s + j] != lit[j] {
            proof {
                assert(v[j as int] == bytes@[s + j]);
                assert(v.subrange(0, k as int)[j as int] != lit@[j as int]);
            }
            return false;
        }
        j = j + 1;
    }
    proof {
        assert(v.subrange(0, k as int) =~= lit@);
    }
    if e - s == k {
        true
    } else {
        let b = bytes[s + k];
        proof { assert(v[k as int] == b); }
        !(0x80u8 <= b && b < 0xC0u8)
    }
}

} // verus!
