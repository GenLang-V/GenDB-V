//! `s LIKE '%<lit>'` (escape backslash) is the byte-suffix test `s ends with <lit>` when `<lit>` is ASCII without
//! `%`, `_` and backslash (`lemma_like_suffix`): the pattern's tokens are `%` then one literal character per byte, the
//! matcher (which never fails without a dangling escape) is standard matching, a run of literal tokens at the end
//! matches exactly the last characters, and ASCII characters at the end of a text are its last bytes.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::chars::*;
use crate::spec::fns::like::*;
use crate::bridge::fns::like::{no_dangling, std_from, lemma_like_mt_std, lemma_std_any};

verus! {

/// `t` ends with `s`.
pub open spec fn ends_with(t: Seq<u8>, s: Seq<u8>) -> bool {
    t.len() >= s.len() && t.subrange(t.len() - s.len(), t.len() as int) == s
}

/// Every byte is ASCII (below 0x80): each is a character of its own.
pub open spec fn ascii(b: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < b.len() ==> #[trigger] b[i] < 0x80u8
}

/// `%` followed by ASCII bytes that are neither `%`, `_` nor backslash.
pub open spec fn suffix_pattern(pat: Seq<u8>) -> bool {
    &&& pat.len() >= 1
    &&& pat[0] == 0x25u8
    &&& forall|i: int| 1 <= i < pat.len() ==> #[trigger] pat[i] < 0x80u8 && pat[i] != 0x25u8 && pat[i] != 0x5Fu8 && pat[i] != 0x5Cu8
}

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

/// The literal tokens of the pattern characters `pc[k..]`, one per character.
pub open spec fn lit_toks(pc: Seq<Seq<u8>>, k: int) -> Seq<LikeTok> {
    Seq::new((pc.len() - k) as nat, |j: int| LikeTok::Lit(pc[k + j]))
}

/// Characters that are neither the escape, `%` nor `_` tokenize as literals.
proof fn lemma_tokens_lits(pc: Seq<Seq<u8>>, k: int)
    requires
        1 <= k <= pc.len(),
        forall|i: int| 1 <= i < pc.len() ==> #[trigger] pc[i] != backslash_char() && pc[i] != pct() && pc[i] != underscore(),
    ensures like_tokens(pc, Some(backslash_char()), k) == lit_toks(pc, k),
    decreases pc.len() - k,
{
    if k < pc.len() {
        lemma_tokens_lits(pc, k + 1);
        assert(pc[k] != backslash_char() && pc[k] != pct() && pc[k] != underscore());
        assert(like_tokens(pc, Some(backslash_char()), k) =~= lit_toks(pc, k));
    } else {
        assert(like_tokens(pc, Some(backslash_char()), k) =~= lit_toks(pc, k));
    }
}

/// The escape character: a backslash.
pub open spec fn backslash_char() -> Seq<u8> {
    seq![0x5Cu8]
}

/// The character of literal token `k`.
pub open spec fn tok_lit(p: Seq<LikeTok>, k: int) -> Seq<u8> {
    p[k]->Lit_0
}

/// The text from `i` is exactly the characters of the literal tokens from `j`.
pub open spec fn rest_is_lits(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int, j: int) -> bool {
    t.len() - i == p.len() - j && forall|k: int| j <= k < p.len() ==> #[trigger] tok_lit(p, k) == t[i - j + k]
}

/// Literal tokens from `j` on match the text from `i` exactly when the rest of the text is those characters.
proof fn lemma_std_lits(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int, j: int)
    requires
        0 <= i <= t.len(),
        1 <= j <= p.len(),
        forall|q: int| 1 <= q < p.len() ==> (#[trigger] p[q]) is Lit,
    ensures like_std(t, p, i, j) == rest_is_lits(t, p, i, j),
    decreases p.len() - j,
{
    if j < p.len() {
        assert(p[j] is Lit);
        if i < t.len() {
            lemma_std_lits(t, p, i + 1, j + 1);
            if like_std(t, p, i, j) {
                assert forall|k: int| j <= k < p.len() implies #[trigger] tok_lit(p, k) == t[i - j + k] by {
                    if k > j {
                        assert(tok_lit(p, k) == t[(i + 1) - (j + 1) + k]);
                    }
                }
            }
            if rest_is_lits(t, p, i, j) {
                assert(tok_lit(p, j) == t[i - j + j]);
                assert forall|k: int| j + 1 <= k < p.len() implies #[trigger] tok_lit(p, k) == t[(i + 1) - (j + 1) + k] by {
                    assert(tok_lit(p, k) == t[i - j + k]);
                }
            }
        } else {
            if rest_is_lits(t, p, i, j) {
                assert(false);
            }
        }
    }
}

/// The last characters of `cs` are the ASCII bytes of `lit`, one per character.
pub open spec fn suffix_chars(cs: Seq<Seq<u8>>, lit: Seq<u8>) -> bool {
    cs.len() >= lit.len()
        && forall|k: int| cs.len() - lit.len() <= k < cs.len() ==> #[trigger] cs[k] == seq![lit[k - (cs.len() - lit.len())]]
}

/// The last characters of a text are the ASCII bytes `lit` exactly when the text ends with `lit`.
proof fn lemma_suffix_chars(s: Seq<u8>, lit: Seq<u8>)
    requires ascii(lit),
    ensures suffix_chars(chars(s), lit) == ends_with(s, lit),
    decreases lit.len(),
{
    let m = lit.len() as int;
    let cs = chars(s);
    if m == 0 {
        assert(s.subrange(s.len() as int, s.len() as int) =~= lit);
    } else if s.len() == 0 {
        assert(cs.len() == 0);
    } else {
        let s1 = s.drop_last();
        let l1 = lit.drop_last();
        assert(ascii(l1)) by {
            assert forall|i: int| 0 <= i < l1.len() implies #[trigger] l1[i] < 0x80u8 by { assert(l1[i] == lit[i]); }
        }
        lemma_suffix_chars(s1, l1);
        let c1 = chars(s1);
        let l = lit[m - 1];
        assert(l < 0x80u8);
        lemma_chars_nonempty(s1);
        // The text ends with `lit` iff its last byte is `l` and the rest ends with `l1`.
        assert(ends_with(s, lit) == (s.last() == l && ends_with(s1, l1))) by {
            if ends_with(s, lit) {
                assert(s.subrange(s.len() - m, s.len() as int)[m - 1] == s.last());
                assert(s1.subrange(s1.len() - (m - 1), s1.len() as int) =~= s.subrange(s.len() - m, s.len() as int).drop_last());
            }
            if s.last() == l && ends_with(s1, l1) {
                assert(s.subrange(s.len() - m, s.len() as int) =~= s1.subrange(s1.len() - (m - 1), s1.len() as int).push(s.last()));
                assert(l1.push(l) =~= lit);
            }
        }
        if is_cont(s.last()) && c1.len() > 0 {
            // The last character has at least two bytes, so it is not an ASCII byte; nor is the last byte `l`.
            assert(cs.last() == c1.last().push(s.last()));
            assert(c1[c1.len() - 1].len() > 0);
            if suffix_chars(cs, lit) {
                assert(cs[cs.len() - 1] == seq![lit[m - 1]]);
                assert(cs[cs.len() - 1].len() == 1);
            }
            assert(s.last() >= 0x80u8);
        } else {
            assert(cs == c1.push(seq![s.last()]));
            assert(suffix_chars(cs, lit) == (s.last() == l && suffix_chars(c1, l1))) by {
                if suffix_chars(cs, lit) {
                    assert(cs[cs.len() - 1] == seq![lit[m - 1]]);
                    assert(seq![s.last()][0] == l);
                    assert forall|k: int| c1.len() - l1.len() <= k < c1.len() implies #[trigger] c1[k] == seq![l1[k - (c1.len() - l1.len())]] by {
                        assert(cs[k] == seq![lit[k - (cs.len() - m)]]);
                        assert(l1[k - (c1.len() - l1.len())] == lit[k - (cs.len() - m)]);
                    }
                }
                if s.last() == l && suffix_chars(c1, l1) {
                    assert forall|k: int| cs.len() - m <= k < cs.len() implies #[trigger] cs[k] == seq![lit[k - (cs.len() - m)]] by {
                        if k < cs.len() - 1 {
                            assert(c1[k] == seq![l1[k - (c1.len() - l1.len())]]);
                            assert(l1[k - (c1.len() - l1.len())] == lit[k - (cs.len() - m)]);
                        } else {
                            assert(cs[cs.len() - 1] == seq![s.last()]);
                        }
                    }
                }
            }
        }
    }
}

/// `s LIKE pat` for a suffix pattern is the byte-suffix test.
pub proof fn lemma_like_suffix(s: Seq<u8>, pat: Seq<u8>)
    requires suffix_pattern(pat),
    ensures
        like_value(Val::Text(s), Val::Text(pat), Val::Text(seq![92u8]))
            == Ok::<Val, SqlError>(Val::Bool(ends_with(s, pat.subrange(1, pat.len() as int)))),
{
    let lit = pat.subrange(1, pat.len() as int);
    let m = lit.len() as int;
    // The escape string is the one character backslash.
    let bs = seq![92u8];
    assert(ascii(bs)) by { assert forall|i: int| 0 <= i < bs.len() implies #[trigger] bs[i] < 0x80u8 by {} }
    lemma_chars_ascii(bs);
    let ec = chars(bs);
    assert(ec =~= seq![backslash_char()]);
    assert(escape_of(ec) == Some(backslash_char()));
    // The pattern's characters and tokens.
    assert(ascii(pat)) by {
        assert forall|i: int| 0 <= i < pat.len() implies #[trigger] pat[i] < 0x80u8 by { if i > 0 { assert(pat[i] < 0x80u8); } }
    }
    lemma_chars_ascii(pat);
    let pc = chars(pat);
    assert(pc[0] == pct()) by { assert(pc[0] =~= seq![0x25u8]); }
    assert forall|i: int| 1 <= i < pc.len() implies #[trigger] pc[i] != backslash_char() && pc[i] != pct() && pc[i] != underscore() by {
        assert(pc[i] == seq![pat[i]]);
        assert(pat[i] != 0x5Cu8 && pat[i] != 0x25u8 && pat[i] != 0x5Fu8);
        if pc[i] == backslash_char() { assert(pc[i][0] == 0x5Cu8); }
        if pc[i] == pct() { assert(pc[i][0] == 0x25u8); }
        if pc[i] == underscore() { assert(pc[i][0] == 0x5Fu8); }
    }
    lemma_tokens_lits(pc, 1);
    let toks = like_tokens(pc, Some(backslash_char()), 0);
    assert(pc[0] != backslash_char()) by { assert(pc[0][0] == 0x25u8); }
    assert(toks == seq![LikeTok::Any] + lit_toks(pc, 1));
    assert(toks.len() == m + 1);
    assert(toks[0] == LikeTok::Any);
    assert forall|q: int| 1 <= q < toks.len() implies (#[trigger] toks[q]) is Lit && toks[q]->Lit_0 == seq![lit[q - 1]] by {
        assert(toks[q] == LikeTok::Lit(pc[q]));
        assert(pc[q] == seq![pat[q]]);
        assert(lit[q - 1] == pat[q]);
    }
    assert(no_dangling(toks)) by {
        assert forall|k: int| 0 <= k < toks.len() implies !(#[trigger] toks[k] is Dangling) by {}
    }
    // The matcher is standard matching: `%` then the literals at the end.
    let t = chars(s);
    lemma_like_mt_std(t, toks);
    lemma_std_any(t, toks, 0, 0);
    let k0 = t.len() - m;
    assert(like_std(t, toks, 0, 0) == suffix_chars(t, lit)) by {
        if like_std(t, toks, 0, 0) {
            assert(std_from(t, toks, 0, 1));
            let k = choose|k: int| 0 <= k <= t.len() && #[trigger] like_std(t, toks, k, 1);
            lemma_std_lits(t, toks, k, 1);
            assert(k == k0);
            assert forall|i: int| t.len() - m <= i < t.len() implies #[trigger] t[i] == seq![lit[i - (t.len() - m)]] by {
                let q = i - k0 + 1;
                assert(tok_lit(toks, q) == t[k - 1 + q]);
                assert(toks[q]->Lit_0 == seq![lit[q - 1]]);
            }
        }
        if suffix_chars(t, lit) {
            lemma_std_lits(t, toks, k0, 1);
            assert forall|q: int| 1 <= q < toks.len() implies #[trigger] tok_lit(toks, q) == t[k0 - 1 + q] by {
                assert(t[k0 - 1 + q] == seq![lit[(k0 - 1 + q) - (t.len() - m)]]);
                assert(toks[q]->Lit_0 == seq![lit[q - 1]]);
            }
            assert(like_std(t, toks, k0, 1));
            assert(std_from(t, toks, 0, 1));
        }
    }
    assert(ascii(lit)) by {
        assert forall|i: int| 0 <= i < lit.len() implies #[trigger] lit[i] < 0x80u8 by { assert(lit[i] == pat[i + 1]); }
    }
    lemma_suffix_chars(s, lit);
}

} // verus!
