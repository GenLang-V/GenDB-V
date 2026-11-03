//! `s LIKE '<lit>%'` (escape backslash) on any text `s` is the byte test "`s` starts with `lit`, followed by the end
//! of `s` or by a byte that is not a UTF-8 continuation byte" (`starts_with_chars`), when `<lit>` is non-empty ASCII
//! without `%`, `_` and backslash (`lemma_like_prefix`); `starts_with_exec` decides it on a byte range (`no_unwind`,
//! usable in worker tasks).
//!
//! The pattern's tokens are one literal character per byte of `lit`, then `%`; the matcher (which never fails without
//! a dangling escape) is standard matching (`bridge::fns::like::lemma_like_mt_std`), so `s` matches exactly when its
//! first characters (`spec::chars`) are the bytes of `lit`, one byte each. Characters of `s` split where a
//! non-continuation byte starts (`lemma_chars_append`), and every character after the first starts with a
//! non-continuation byte (`lemma_chars_lead`): so the first characters are `lit`'s bytes exactly when the bytes are,
//! and the next byte (if any) starts a new character.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::chars::*;
use crate::spec::fns::like::*;
use crate::bridge::fns::like::{no_dangling, std_from, lemma_like_mt_std, lemma_std_any};

verus! {

// ------------------------------------------------------------------------------------------------ the byte test

/// Every byte is ASCII (below 0x80): each is a character of its own.
pub open spec fn ascii(b: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < b.len() ==> #[trigger] b[i] < 0x80u8
}

/// `s` starts with the bytes of `lit`, followed by its end or by a byte that starts a new character.
pub open spec fn starts_with_chars(s: Seq<u8>, lit: Seq<u8>) -> bool {
    &&& lit.len() <= s.len()
    &&& s.subrange(0, lit.len() as int) == lit
    &&& (s.len() == lit.len() || !is_cont(s[lit.len() as int]))
}

/// Non-empty ASCII bytes that are neither `%`, `_` nor backslash, then `%`.
pub open spec fn prefix_pattern(pat: Seq<u8>) -> bool {
    &&& pat.len() >= 2
    &&& pat[pat.len() - 1] == 0x25u8
    &&& forall|i: int| 0 <= i < pat.len() - 1 ==> #[trigger] pat[i] < 0x80u8 && pat[i] != 0x25u8 && pat[i] != 0x5Fu8 && pat[i] != 0x5Cu8
}

/// The literal before the final `%` of a prefix pattern.
pub open spec fn prefix_lit(pat: Seq<u8>) -> Seq<u8> { pat.subrange(0, pat.len() - 1) }

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

/// A non-empty text has a character.
proof fn lemma_chars_len(b: Seq<u8>)
    ensures b.len() > 0 ==> chars(b).len() > 0,
{
}

/// Characters split where a byte that is not a continuation byte starts.
pub proof fn lemma_chars_append(a: Seq<u8>, b: Seq<u8>)
    requires b.len() == 0 || !is_cont(b[0]),
    ensures chars(a + b) == chars(a) + chars(b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(chars(b) =~= Seq::<Seq<u8>>::empty());
        assert(chars(a) + chars(b) =~= chars(a));
    } else {
        let bi = b.drop_last();
        let x = b.last();
        assert((a + b).drop_last() =~= a + bi);
        assert((a + b).last() == x);
        if bi.len() > 0 {
            assert(bi[0] == b[0]);
        }
        lemma_chars_append(a, bi);
        let ca = chars(a);
        let cb = chars(bi);
        if bi.len() == 0 {
            assert(x == b[0]);
            assert(!is_cont(x));
            assert(chars(bi) =~= Seq::<Seq<u8>>::empty());
            assert(ca + cb =~= ca);
            assert(chars(b) =~= seq![seq![x]]);
            assert(chars(a + b) =~= ca.push(seq![x]));
            assert(ca + chars(b) =~= ca.push(seq![x]));
        } else {
            lemma_chars_len(bi);
            assert(cb.len() > 0);
            let ab = ca + cb;
            if is_cont(x) {
                assert(ab.drop_last() =~= ca + cb.drop_last());
                assert(ab.last() == cb.last());
                assert(chars(a + b) == ab.drop_last().push(ab.last().push(x)));
                assert(chars(b) == cb.drop_last().push(cb.last().push(x)));
                assert(ab.drop_last().push(ab.last().push(x)) =~= ca + cb.drop_last().push(cb.last().push(x)));
            } else {
                assert(chars(a + b) == ab.push(seq![x]));
                assert(chars(b) == cb.push(seq![x]));
                assert(ab.push(seq![x]) =~= ca + cb.push(seq![x]));
            }
        }
    }
}

/// Every character after the first starts with a byte that is not a continuation byte, and every character is
/// non-empty.
pub proof fn lemma_chars_lead(b: Seq<u8>)
    ensures
        forall|k: int| 0 <= k < chars(b).len() ==> (#[trigger] chars(b)[k]).len() > 0,
        forall|k: int| 1 <= k < chars(b).len() ==> !is_cont(#[trigger] chars(b)[k][0]),
    decreases b.len(),
{
    lemma_chars_nonempty(b);
    if b.len() > 0 {
        let cs = chars(b.drop_last());
        lemma_chars_lead(b.drop_last());
        let x = b.last();
        if is_cont(x) && cs.len() > 0 {
            let r = cs.drop_last().push(cs.last().push(x));
            assert(chars(b) == r);
            assert forall|k: int| 1 <= k < r.len() implies !is_cont(#[trigger] r[k][0]) by {
                if k < r.len() - 1 {
                    assert(r[k] == cs[k]);
                } else {
                    assert(r[k] == cs[k].push(x));
                    assert(cs[k].len() > 0);
                    assert(r[k][0] == cs[k][0]);
                }
            }
        } else {
            let r = cs.push(seq![x]);
            assert(chars(b) == r);
            assert forall|k: int| 1 <= k < r.len() implies !is_cont(#[trigger] r[k][0]) by {
                if k < r.len() - 1 {
                    assert(r[k] == cs[k]);
                } else {
                    assert(cs.len() > 0);
                    assert(!is_cont(x));
                    assert(r[k] == seq![x]);
                }
            }
        }
    }
}

/// Concatenation of characters distributes over appending.
pub proof fn lemma_concat_append(a: Seq<Seq<u8>>, b: Seq<Seq<u8>>)
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
        assert(concat(a) + (concat(b.drop_last()) + b.last()) =~= (concat(a) + concat(b.drop_last())) + b.last());
    }
}

/// Single-byte characters spell their bytes.
pub proof fn lemma_concat_singles(lit: Seq<u8>)
    ensures concat(Seq::new(lit.len(), |i: int| seq![lit[i]])) == lit,
    decreases lit.len(),
{
    if lit.len() > 0 {
        let d = lit.drop_last();
        lemma_concat_singles(d);
        let cs = Seq::new(lit.len(), |i: int| seq![lit[i]]);
        assert(cs.drop_last() =~= Seq::new(d.len(), |i: int| seq![d[i]]));
        assert(d + seq![lit.last()] =~= lit);
    } else {
        assert(Seq::new(lit.len(), |i: int| seq![lit[i]]) =~= Seq::<Seq<u8>>::empty());
        assert(lit =~= Seq::<u8>::empty());
    }
}

/// The first `lit.len()` characters of `s` are the single bytes of the ASCII `lit` exactly when `s` starts with the
/// characters of `lit`.
pub proof fn lemma_first_chars(s: Seq<u8>, lit: Seq<u8>)
    requires ascii(lit), lit.len() >= 1,
    ensures
        (lit.len() <= chars(s).len() && forall|q: int| 0 <= q < lit.len() ==> #[trigger] chars(s)[q] == seq![lit[q]])
            == starts_with_chars(s, lit),
{
    let m = lit.len() as int;
    let t = chars(s);
    let singles = Seq::new(lit.len(), |i: int| seq![lit[i]]);
    lemma_chars_ascii(lit);
    if starts_with_chars(s, lit) {
        let rest = s.subrange(m, s.len() as int);
        assert(s =~= lit + rest);
        if rest.len() > 0 {
            assert(rest[0] == s[m]);
        }
        lemma_chars_append(lit, rest);
        assert(t == chars(lit) + chars(rest));
        assert forall|q: int| 0 <= q < m implies #[trigger] t[q] == seq![lit[q]] by {
            assert(t[q] == chars(lit)[q]);
        }
    }
    if m <= t.len() && forall|q: int| 0 <= q < m ==> #[trigger] t[q] == seq![lit[q]] {
        lemma_concat_chars(s);
        let head = t.take(m);
        let tail = t.skip(m);
        assert(t =~= head + tail);
        assert(head =~= singles) by {
            assert forall|q: int| 0 <= q < m implies head[q] == singles[q] by {
                assert(head[q] == t[q]);
            }
        }
        lemma_concat_append(head, tail);
        lemma_concat_singles(lit);
        assert(s == lit + concat(tail));
        assert(s.subrange(0, m) =~= lit);
        if s.len() > m {
            assert(concat(tail).len() > 0);
            assert(tail.len() > 0) by {
                if tail.len() == 0 { assert(concat(tail) =~= Seq::<u8>::empty()); }
            }
            lemma_chars_lead(s);
            assert(t[m].len() > 0);
            assert(!is_cont(t[m][0]));
            let tl = tail.drop_first();
            assert(tail =~= seq![t[m]] + tl);
            lemma_concat_append(seq![t[m]], tl);
            assert(concat(seq![t[m]]) =~= t[m]) by {
                assert(seq![t[m]].drop_last() =~= Seq::<Seq<u8>>::empty());
                assert(concat(Seq::<Seq<u8>>::empty()) =~= Seq::<u8>::empty());
            }
            assert(concat(tail)[0] == t[m][0]);
            assert(s[m] == concat(tail)[0]);
        }
    }
}

// ------------------------------------------------------------------------------------------------ tokens

/// Token `q` of a prefix pattern of `m` literal characters: the literal character, then `%` at `m`.
pub open spec fn ptok(pc: Seq<Seq<u8>>, m: int, q: int) -> LikeTok {
    if q == m { LikeTok::Any } else { LikeTok::Lit(pc[q]) }
}

/// The escape character: a backslash.
pub open spec fn backslash_char() -> Seq<u8> { seq![0x5Cu8] }

/// The tokens of a prefix pattern's characters from `k` (`0 <= k <= m + 1`).
proof fn lemma_tokens_from(pc: Seq<Seq<u8>>, m: int, k: int)
    requires
        pc.len() == m + 1, m >= 1, 0 <= k <= m + 1,
        pc[m] == pct(),
        forall|i: int| 0 <= i < m ==> #[trigger] pc[i] != backslash_char() && pc[i] != pct() && pc[i] != underscore(),
    ensures
        like_tokens(pc, Some(backslash_char()), k) == Seq::new((m + 1 - k) as nat, |j: int| ptok(pc, m, k + j)),
    decreases m + 1 - k,
{
    let esc = Some(backslash_char());
    if k < m + 1 {
        lemma_tokens_from(pc, m, k + 1);
        if k == m {
            assert(pc[k] != backslash_char()) by { assert(pc[k][0] == 0x25u8); }
        } else {
            assert(pc[k] != backslash_char() && pc[k] != pct() && pc[k] != underscore());
        }
        assert(like_tokens(pc, esc, k) =~= Seq::new((m + 1 - k) as nat, |j: int| ptok(pc, m, k + j)));
    } else {
        assert(like_tokens(pc, esc, k) =~= Seq::new((m + 1 - k) as nat, |j: int| ptok(pc, m, k + j)));
    }
}

// ------------------------------------------------------------------------------------------------ standard matching

/// The text from `i` matches the literal tokens `j..m` and the final `%` exactly when the next `m - j` characters
/// are those literals.
proof fn lemma_std_lits(t: Seq<Seq<u8>>, p: Seq<LikeTok>, m: int, i: int, j: int)
    requires
        p.len() == m + 1, m >= 1, 0 <= j <= m, 0 <= i <= t.len(),
        p[m] is Any,
        forall|q: int| 0 <= q < m ==> (#[trigger] p[q]) is Lit,
    ensures
        like_std(t, p, i, j) == (i + (m - j) <= t.len()
            && forall|q: int| j <= q < m ==> #[trigger] t[i - j + q] == p[q]->Lit_0),
    decreases m - j,
{
    if j == m {
        lemma_std_any(t, p, i, m);
        assert(like_std(t, p, t.len() as int, m + 1));
        assert(std_from(t, p, i, m + 1));
    } else {
        assert(p[j] is Lit);
        if i < t.len() {
            lemma_std_lits(t, p, m, i + 1, j + 1);
            if like_std(t, p, i, j) {
                assert forall|q: int| j <= q < m implies #[trigger] t[i - j + q] == p[q]->Lit_0 by {
                    if q > j {
                        assert(t[(i + 1) - (j + 1) + q] == p[q]->Lit_0);
                    }
                }
            }
            if i + (m - j) <= t.len() && forall|q: int| j <= q < m ==> #[trigger] t[i - j + q] == p[q]->Lit_0 {
                assert(t[i - j + j] == p[j]->Lit_0);
                assert forall|q: int| j + 1 <= q < m implies #[trigger] t[(i + 1) - (j + 1) + q] == p[q]->Lit_0 by {
                    assert(t[i - j + q] == p[q]->Lit_0);
                }
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------ the theorem

/// `s LIKE pat` for a prefix pattern is the byte test `starts_with_chars`.
pub proof fn lemma_like_prefix(s: Seq<u8>, pat: Seq<u8>)
    requires prefix_pattern(pat),
    ensures
        like_value(Val::Text(s), Val::Text(pat), Val::Text(seq![92u8]))
            == Ok::<Val, SqlError>(Val::Bool(starts_with_chars(s, prefix_lit(pat)))),
{
    let lit = prefix_lit(pat);
    let m = lit.len() as int;
    // the escape string is the one character backslash
    let bs = seq![92u8];
    assert(ascii(bs)) by { assert forall|i: int| 0 <= i < bs.len() implies #[trigger] bs[i] < 0x80u8 by {} }
    lemma_chars_ascii(bs);
    let ec = chars(bs);
    assert(ec =~= seq![backslash_char()]);
    assert(escape_of(ec) == Some(backslash_char()));
    // the pattern's characters and tokens
    assert(ascii(pat)) by {
        assert forall|i: int| 0 <= i < pat.len() implies #[trigger] pat[i] < 0x80u8 by {
            if i < pat.len() - 1 { assert(pat[i] < 0x80u8); }
        }
    }
    lemma_chars_ascii(pat);
    let pc = chars(pat);
    assert(pc.len() == m + 1);
    assert(pc[m] == pct()) by { assert(pc[m] =~= seq![0x25u8]); }
    assert forall|i: int| 0 <= i < m implies #[trigger] pc[i] != backslash_char() && pc[i] != pct() && pc[i] != underscore() by {
        assert(pc[i] == seq![pat[i]]);
        assert(pat[i] != 0x5Cu8 && pat[i] != 0x25u8 && pat[i] != 0x5Fu8);
        if pc[i] == backslash_char() { assert(pc[i][0] == 0x5Cu8); }
        if pc[i] == pct() { assert(pc[i][0] == 0x25u8); }
        if pc[i] == underscore() { assert(pc[i][0] == 0x5Fu8); }
    }
    lemma_tokens_from(pc, m, 0);
    let toks = like_tokens(pc, Some(backslash_char()), 0);
    assert(toks =~= Seq::new((m + 1) as nat, |q: int| ptok(pc, m, q)));
    assert forall|q: int| 0 <= q < m implies (#[trigger] toks[q]) is Lit && toks[q]->Lit_0 == seq![lit[q]] by {
        assert(toks[q] == ptok(pc, m, q));
        assert(pc[q] == seq![pat[q]]);
        assert(lit[q] == pat[q]);
    }
    assert(no_dangling(toks)) by {
        assert forall|k: int| 0 <= k < toks.len() implies !(#[trigger] toks[k] is Dangling) by {
            assert(toks[k] == ptok(pc, m, k));
        }
    }
    assert(toks[m] is Any) by { assert(toks[m] == ptok(pc, m, m)); }
    // the matcher is standard matching: the literals, then `%`
    let t = chars(s);
    lemma_like_mt_std(t, toks);
    lemma_std_lits(t, toks, m, 0, 0);
    // the first characters are the literal bytes exactly when the bytes start with them
    assert(ascii(lit)) by {
        assert forall|i: int| 0 <= i < lit.len() implies #[trigger] lit[i] < 0x80u8 by { assert(lit[i] == pat[i]); }
    }
    lemma_first_chars(s, lit);
    assert(like_std(t, toks, 0, 0) == starts_with_chars(s, lit)) by {
        if like_std(t, toks, 0, 0) {
            assert forall|q: int| 0 <= q < m implies #[trigger] t[q] == seq![lit[q]] by {
                assert(t[0 - 0 + q] == toks[q]->Lit_0);
            }
        }
        if starts_with_chars(s, lit) {
            assert forall|q: int| 0 <= q < m implies #[trigger] t[0 - 0 + q] == toks[q]->Lit_0 by {
                assert(t[q] == seq![lit[q]]);
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------ the executable test

/// Whether `bytes[lo..hi]` starts with the characters of `lit` (`m` bytes, `m >= 1`).
pub fn starts_with_exec(bytes: &[u8], lo: usize, hi: usize, lit: &[u8], m: usize) -> (r: bool)
    requires lo <= hi <= bytes@.len(), m == lit@.len(), m >= 1,
    ensures r == starts_with_chars(bytes@.subrange(lo as int, hi as int), lit@),
    no_unwind
{
    let ghost s = bytes@.subrange(lo as int, hi as int);
    if hi - lo < m {
        return false;
    }
    let mut k: usize = 0;
    while k < m
        invariant
            lo <= hi <= bytes@.len(), m == lit@.len(), m <= hi - lo, k <= m,
            s == bytes@.subrange(lo as int, hi as int),
            forall|x: int| 0 <= x < k ==> #[trigger] s[x] == lit@[x],
        decreases m - k,
    {
        if bytes[lo + k] != lit[k] {
            assert(s[k as int] == bytes@[lo + k]);
            assert(s.subrange(0, m as int)[k as int] != lit@[k as int]);
            return false;
        }
        assert(s[k as int] == bytes@[lo + k]);
        k = k + 1;
    }
    assert(s.subrange(0, m as int) =~= lit@);
    if hi - lo == m {
        return true;
    }
    let b = bytes[lo + m];
    assert(s[m as int] == b);
    !(0x80u8 <= b && b < 0xC0u8)
}

} // verus!
