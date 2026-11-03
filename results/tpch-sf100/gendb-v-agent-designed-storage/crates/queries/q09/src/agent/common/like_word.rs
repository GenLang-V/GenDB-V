//! `s LIKE '%w%' ESCAPE '\'` for a plain word `w` (non-empty ASCII without `%`, `_`, `\`) on an ASCII text `s`: the
//! value is `true` exactly when `w` occurs in `s` as a byte substring, and it never raises (`lemma_like_word`).
//! On ASCII text every byte is one character (`lemma_chars_ascii`), the pattern's tokens are `%`, the word's
//! literals, `%` (`lemma_word_tokens`), and standard LIKE matching of those tokens is substring search
//! (`lemma_std_word`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::chars::*;
use crate::spec::fns::like::*;
use crate::bridge::fns::like::{no_dangling, std_from, lemma_like_mt_std, lemma_std_any};

verus! {

/// Every byte is ASCII.
pub open spec fn all_ascii(s: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] < 0x80
}

/// `w` occurs in `s` at byte position `i`.
pub open spec fn occurs_at(s: Seq<u8>, w: Seq<u8>, i: int) -> bool {
    0 <= i && i + w.len() <= s.len() && s.subrange(i, i + w.len()) == w
}

/// `w` is a byte substring of `s`.
pub open spec fn contains(s: Seq<u8>, w: Seq<u8>) -> bool {
    exists|i: int| #[trigger] occurs_at(s, w, i)
}

/// A non-empty ASCII word without the LIKE metacharacters `%`, `_` and the escape `\`.
pub open spec fn plain_word(w: Seq<u8>) -> bool {
    &&& w.len() >= 1
    &&& forall|i: int| 0 <= i < w.len() ==> #[trigger] w[i] < 0x80 && w[i] != 0x25 && w[i] != 0x5F && w[i] != 0x5C
}

/// The pattern `%w%`.
pub open spec fn word_pattern(w: Seq<u8>) -> Seq<u8> {
    seq![0x25u8] + w + seq![0x25u8]
}

/// One character per byte.
pub open spec fn singles(s: Seq<u8>) -> Seq<Seq<u8>> {
    Seq::new(s.len(), |i: int| seq![s[i]])
}

/// On ASCII text every byte is a character.
pub proof fn lemma_chars_ascii(s: Seq<u8>)
    requires all_ascii(s),
    ensures chars(s) == singles(s),
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        assert(all_ascii(d)) by {
            assert forall|i: int| 0 <= i < d.len() implies #[trigger] d[i] < 0x80 by { assert(d[i] == s[i]); }
        }
        lemma_chars_ascii(d);
        assert(s.last() == s[s.len() - 1]);
        assert(!is_cont(s.last()));
        assert(chars(s) == chars(d).push(seq![s.last()]));
        assert(singles(d).push(seq![s.last()]) =~= singles(s));
    } else {
        assert(chars(s) =~= singles(s));
    }
}

/// The tokens of `%w%`: `%`, one literal per byte of `w`, `%`.
pub open spec fn word_tokens(w: Seq<u8>) -> Seq<LikeTok> {
    seq![LikeTok::Any] + Seq::new(w.len(), |i: int| LikeTok::Lit(seq![w[i]])) + seq![LikeTok::Any]
}

/// The tokens of `%w%` from position `k` on (escape `\`).
proof fn lemma_word_tokens_from(w: Seq<u8>, k: int)
    requires plain_word(w), 0 <= k <= w.len() + 2,
    ensures
        like_tokens(singles(word_pattern(w)), Some(seq![0x5Cu8]), k)
            == word_tokens(w).subrange(k, w.len() + 2int),
    decreases w.len() + 2 - k,
{
    let pat = word_pattern(w);
    let pc = singles(pat);
    let n = w.len() + 2int;
    let toks = word_tokens(w);
    assert(pat.len() == n);
    assert(pc.len() == n);
    if k >= n {
        assert(toks.subrange(k, n) =~= Seq::<LikeTok>::empty());
    } else {
        lemma_word_tokens_from(w, k + 1);
        assert(pc[k] == seq![pat[k]]);
        let b = pat[k];
        if k == 0 || k == n - 1 {
            assert(b == 0x25u8);
            assert(pc[k] =~= pct());
            assert(Some(seq![0x5Cu8]) != Some(pc[k]));
            assert(toks[k] == LikeTok::Any);
        } else {
            assert(b == w[k - 1]);
            assert(b != 0x25u8 && b != 0x5Fu8 && b != 0x5Cu8);
            assert(pc[k] != pct()) by { assert(pc[k][0] != pct()[0]); }
            assert(pc[k] != underscore()) by { assert(pc[k][0] != underscore()[0]); }
            assert(Some(seq![0x5Cu8]) != Some(pc[k])) by { assert(seq![0x5Cu8][0] != pc[k][0]); }
            assert(toks[k] == LikeTok::Lit(seq![w[k - 1]]));
        }
        assert(seq![toks[k]] + toks.subrange(k + 1, n) =~= toks.subrange(k, n));
    }
}

pub proof fn lemma_word_tokens(w: Seq<u8>)
    requires plain_word(w),
    ensures
        like_tokens(chars(word_pattern(w)), escape_of(chars(seq![0x5Cu8])), 0) == word_tokens(w),
        no_dangling(word_tokens(w)),
        chars(seq![0x5Cu8]).len() == 1,
{
    let pat = word_pattern(w);
    assert(all_ascii(pat)) by {
        assert forall|i: int| 0 <= i < pat.len() implies #[trigger] pat[i] < 0x80 by {
            if 0 < i < pat.len() - 1 { assert(pat[i] == w[i - 1]); }
        }
    }
    lemma_chars_ascii(pat);
    let e = seq![0x5Cu8];
    assert(all_ascii(e));
    lemma_chars_ascii(e);
    assert(chars(e) =~= seq![seq![0x5Cu8]]);
    lemma_word_tokens_from(w, 0);
    assert(word_tokens(w).subrange(0, w.len() + 2int) =~= word_tokens(w));
    let toks = word_tokens(w);
    assert forall|m: int| 0 <= m < toks.len() implies !(#[trigger] toks[m] is Dangling) by {}
}

/// The literal run of the word tokens from token `j` (1 ..= |w| + 1) at text position `k`: standard matching
/// holds exactly when the rest of the word occurs at `k` (the closing `%` then matches the rest of the text).
proof fn lemma_std_lits(s: Seq<u8>, w: Seq<u8>, k: int, j: int)
    requires plain_word(w), 0 <= k <= s.len(), 1 <= j <= w.len() + 1,
    ensures
        like_std(singles(s), word_tokens(w), k, j)
            == (k + (w.len() + 1 - j) <= s.len() && s.subrange(k, k + (w.len() + 1 - j)) == w.subrange(j - 1, w.len() as int)),
    decreases w.len() + 1 - j,
{
    let t = singles(s);
    let p = word_tokens(w);
    let m = w.len() as int;
    if j == m + 1 {
        // the closing %: some suffix matches the empty rest
        lemma_std_any(t, p, k, j);
        assert(like_std(t, p, s.len() as int, j + 1));
        assert(std_from(t, p, k, j + 1));
        assert(s.subrange(k, k) =~= w.subrange(m, m));
    } else {
        assert(p[j] == LikeTok::Lit(seq![w[j - 1]]));
        if k < s.len() {
            lemma_std_lits(s, w, k + 1, j + 1);
            assert(t[k] == seq![s[k]]);
            assert((t[k] == seq![w[j - 1]]) == (s[k] == w[j - 1])) by {
                if t[k] == seq![w[j - 1]] { assert(t[k][0] == seq![w[j - 1]][0]); }
            }
            let rest = m + 1 - j;
            if s[k] == w[j - 1] && k + rest <= s.len() && s.subrange(k + 1, k + rest) == w.subrange(j, m) {
                assert(s.subrange(k, k + rest) =~= seq![s[k]] + s.subrange(k + 1, k + rest));
                assert(w.subrange(j - 1, m) =~= seq![w[j - 1]] + w.subrange(j, m));
            }
            if k + rest <= s.len() && s.subrange(k, k + rest) == w.subrange(j - 1, m) {
                assert(s.subrange(k, k + rest)[0] == s[k]);
                assert(w.subrange(j - 1, m)[0] == w[j - 1]);
                assert(s.subrange(k + 1, k + rest) =~= s.subrange(k, k + rest).subrange(1, rest));
                assert(w.subrange(j, m) =~= w.subrange(j - 1, m).subrange(1, rest));
            }
        } else {
            assert(m + 1 - j >= 1);
        }
    }
}

/// Standard matching of `%w%` on a text of single-byte characters is substring search.
proof fn lemma_std_word(s: Seq<u8>, w: Seq<u8>)
    requires plain_word(w),
    ensures like_std(singles(s), word_tokens(w), 0, 0) == contains(s, w),
{
    let t = singles(s);
    let p = word_tokens(w);
    lemma_std_any(t, p, 0, 0);
    if contains(s, w) {
        let i = choose|i: int| #[trigger] occurs_at(s, w, i);
        lemma_std_lits(s, w, i, 1);
        assert(w.subrange(0, w.len() as int) =~= w);
        assert(like_std(t, p, i, 1));
    }
    if std_from(t, p, 0, 1) {
        let k = choose|k: int| 0 <= k <= t.len() && #[trigger] like_std(t, p, k, 1);
        lemma_std_lits(s, w, k, 1);
        assert(w.subrange(0, w.len() as int) =~= w);
        assert(occurs_at(s, w, k));
    }
}

/// `s LIKE '%w%' ESCAPE '\'` on ASCII text is the substring test, without error.
pub proof fn lemma_like_word(s: Seq<u8>, w: Seq<u8>)
    requires plain_word(w), all_ascii(s),
    ensures
        like_value(Val::Text(s), Val::Text(word_pattern(w)), Val::Text(seq![0x5Cu8]))
            == Ok::<Val, SqlError>(Val::Bool(contains(s, w))),
{
    lemma_word_tokens(w);
    lemma_chars_ascii(s);
    let t = chars(s);
    let p = word_tokens(w);
    lemma_like_mt_std(t, p);
    lemma_std_word(s, w);
}

} // verus!
