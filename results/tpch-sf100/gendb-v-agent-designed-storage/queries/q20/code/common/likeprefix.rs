//! LIKE with a literal prefix pattern, and bytewise intervals: (1) the LIKE matcher raises only 22025
//! (`lemma_like_value_err`); (2) for a pattern `P%` whose `P` is ASCII without `%`, `_` and the escape `\`,
//! `t LIKE P%` is exactly `prefix_cond(t, P)`: `t` starts with the bytes of `P` and the byte after them (if any) does
//! not continue `P`'s last character (`lemma_prefix_like`); (3) the texts that start with `q ++ [x]` for some
//! byte `x` in `[a, b)` are exactly the texts in the bytewise interval `[q ++ [a], q ++ [b])` (`lemma_lex_interval`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::chars::*;
use crate::spec::text::lex_cmp;
use crate::spec::fns::like::*;

verus! {

// ------------------------------------------------------------------------------------------------ errors

/// `like_mt` raises only 22025.
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

/// `chars` of the one-byte escape `\` is one character.
pub proof fn lemma_chars_backslash()
    ensures chars(seq![92u8]) == seq![seq![92u8]],
{
    let b = seq![92u8];
    assert(b.drop_last() =~= Seq::<u8>::empty());
    assert(chars(Seq::<u8>::empty()) =~= Seq::<Seq<u8>>::empty());
    assert(!is_cont(92u8));
    assert(Seq::<Seq<u8>>::empty().push(seq![92u8]) =~= seq![seq![92u8]]);
}

/// `t LIKE pat ESCAPE '\'` on texts: a boolean, or the error 22025.
pub proof fn lemma_like_value_err(t: Seq<u8>, pat: Seq<u8>)
    ensures ({
        let r = like_value(Val::Text(t), Val::Text(pat), Val::Text(seq![92u8]));
        &&& r is Ok ==> r->Ok_0 is Bool
        &&& r is Err ==> r == Err::<Val, SqlError>(SqlError::InvalidEscapeSequence)
        &&& r == match like_mt(chars(t), like_tokens(chars(pat), Some(seq![92u8]), 0), 0, 0) {
                Ok(m) => Ok::<Val, SqlError>(Val::Bool(m is Match)),
                Err(e) => Err::<Val, SqlError>(e),
            }
    }),
{
    lemma_chars_backslash();
    let ec = chars(seq![92u8]);
    assert(ec.len() == 1);
    assert(escape_of(ec) == Some(seq![92u8]));
    lemma_mt_err(chars(t), like_tokens(chars(pat), Some(seq![92u8]), 0), 0, 0);
}

// ------------------------------------------------------------------------------------------------ characters

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

/// Splitting at a byte that starts a character (or at the end): the characters of the two parts.
pub proof fn lemma_chars_split(t: Seq<u8>, m: int)
    requires 0 <= m <= t.len(), m == t.len() || !is_cont(t[m]),
    ensures chars(t) == chars(t.subrange(0, m)) + chars(t.subrange(m, t.len() as int)),
    decreases t.len(),
{
    let a = t.subrange(0, m);
    if t.len() == m {
        assert(t.subrange(m, t.len() as int) =~= Seq::<u8>::empty());
        assert(a =~= t);
        assert(chars(Seq::<u8>::empty()) =~= Seq::<Seq<u8>>::empty());
        assert(chars(t) + Seq::<Seq<u8>>::empty() =~= chars(t));
    } else {
        let d = t.drop_last();
        let b = t.last();
        if m < d.len() {
            assert(d[m] == t[m]);
        }
        lemma_chars_split(d, m);
        assert(d.subrange(0, m) =~= a);
        let r = t.subrange(m, t.len() as int);
        let rd = d.subrange(m, d.len() as int);
        assert(r.drop_last() =~= rd);
        assert(r.last() == b);
        let cs = chars(d);
        let cr = chars(rd);
        assert(cs == chars(a) + cr);
        if d.len() == m {
            assert(rd =~= Seq::<u8>::empty());
            assert(cr =~= Seq::<Seq<u8>>::empty());
            assert(b == t[m]);
            assert(!is_cont(b));
            assert(chars(r) == cr.push(seq![b]));
            assert(chars(t) == cs.push(seq![b]));
            assert(cs.push(seq![b]) =~= chars(a) + cr.push(seq![b]));
        } else {
            assert(rd.len() > 0);
            crate::agent::common::likeprefix::lemma_chars_len_pos(rd);
            assert(cr.len() > 0);
            assert(cs.len() > 0);
            assert(cs.last() == cr.last());
            if is_cont(b) {
                assert(chars(r) == cr.drop_last().push(cr.last().push(b)));
                assert(chars(t) == cs.drop_last().push(cs.last().push(b)));
                assert(cs.drop_last() =~= chars(a) + cr.drop_last());
                assert(cs.drop_last().push(cs.last().push(b)) =~= chars(a) + cr.drop_last().push(cr.last().push(b)));
            } else {
                assert(chars(r) == cr.push(seq![b]));
                assert(chars(t) == cs.push(seq![b]));
                assert(cs.push(seq![b]) =~= chars(a) + cr.push(seq![b]));
            }
        }
    }
}

/// A non-empty text has a character.
pub proof fn lemma_chars_len_pos(t: Seq<u8>)
    requires t.len() > 0,
    ensures chars(t).len() > 0,
{
    let cs = chars(t.drop_last());
    if is_cont(t.last()) && cs.len() > 0 {
        assert(chars(t).len() == cs.len());
    } else {
        assert(chars(t).len() == cs.len() + 1);
    }
}

/// Every character after the first starts with a byte that is not a continuation byte.
pub proof fn lemma_chars_heads(t: Seq<u8>)
    ensures forall|k: int| 1 <= k < chars(t).len() ==> !is_cont(#[trigger] chars(t)[k][0]),
    decreases t.len(),
{
    if t.len() > 0 {
        let d = t.drop_last();
        let b = t.last();
        lemma_chars_heads(d);
        lemma_chars_nonempty(d);
        let cs = chars(d);
        let ct = chars(t);
        assert forall|k: int| 1 <= k < ct.len() implies !is_cont(#[trigger] ct[k][0]) by {
            if is_cont(b) && cs.len() > 0 {
                if k < cs.len() - 1 {
                    assert(ct[k] == cs[k]);
                } else {
                    assert(ct[k] == cs.last().push(b));
                    assert(cs.last().len() > 0);
                    assert(ct[k][0] == cs[k][0]);
                }
            } else {
                if k < cs.len() {
                    assert(ct[k] == cs[k]);
                } else {
                    assert(ct[k] == seq![b]);
                    assert(cs.len() > 0);
                }
            }
        }
    }
}

/// `concat` of a prefix of characters, one more character.
pub proof fn lemma_concat_take(cs: Seq<Seq<u8>>, k: int)
    requires 0 <= k < cs.len(),
    ensures concat(cs.subrange(0, k + 1)) == concat(cs.subrange(0, k)) + cs[k],
{
    let s = cs.subrange(0, k + 1);
    assert(s.drop_last() =~= cs.subrange(0, k));
    assert(s.last() == cs[k]);
}

/// `concat` splits at any character index.
pub proof fn lemma_concat_split(cs: Seq<Seq<u8>>, k: int)
    requires 0 <= k <= cs.len(),
    ensures concat(cs) == concat(cs.subrange(0, k)) + concat(cs.subrange(k, cs.len() as int)),
    decreases cs.len(),
{
    if k == cs.len() {
        assert(cs.subrange(0, k) =~= cs);
        assert(cs.subrange(k, cs.len() as int) =~= Seq::<Seq<u8>>::empty());
        assert(concat(cs) + Seq::<u8>::empty() =~= concat(cs));
    } else {
        let d = cs.drop_last();
        lemma_concat_split(d, k);
        assert(d.subrange(0, k) =~= cs.subrange(0, k));
        let r = cs.subrange(k, cs.len() as int);
        assert(r.drop_last() =~= d.subrange(k, d.len() as int));
        assert(r.last() == cs.last());
        assert(concat(r) == concat(d.subrange(k, d.len() as int)) + cs.last());
        assert(concat(cs) == concat(d) + cs.last());
    }
}

/// Single-byte characters concatenate to their bytes.
pub proof fn lemma_concat_bytes(cs: Seq<Seq<u8>>, p: Seq<u8>)
    requires cs.len() == p.len(), forall|j: int| 0 <= j < p.len() ==> #[trigger] cs[j] == seq![p[j]],
    ensures concat(cs) == p,
    decreases cs.len(),
{
    if cs.len() > 0 {
        let d = cs.drop_last();
        lemma_concat_bytes(d, p.drop_last());
        assert(cs.last() == seq![p.last()]);
        assert(p.drop_last() + seq![p.last()] =~= p);
    } else {
        assert(p =~= Seq::<u8>::empty());
    }
}

// ------------------------------------------------------------------------------------------------ prefix patterns

/// `P` can open a prefix pattern `P%`: ASCII, without `%`, `_` and the escape `\`.
pub open spec fn plain_prefix(p: Seq<u8>) -> bool {
    forall|j: int| 0 <= j < p.len() ==> #[trigger] p[j] < 0x80u8 && p[j] != 0x25u8 && p[j] != 0x5Fu8 && p[j] != 0x5Cu8
}

/// `t` starts with the bytes of `p`, and the byte after them (if any) starts a character.
pub open spec fn prefix_cond(t: Seq<u8>, p: Seq<u8>) -> bool {
    &&& t.len() >= p.len()
    &&& t.subrange(0, p.len() as int) == p
    &&& (p.len() == 0 || t.len() == p.len() || !is_cont(t[p.len() as int]))
}

/// The tokens of the pattern `p ++ [%]` (escape `\`) from character `k`: literals, then `%`.
pub open spec fn prefix_toks(p: Seq<u8>) -> Seq<LikeTok> {
    Seq::new(p.len() + 1, |j: int| if j < p.len() { LikeTok::Lit(seq![p[j]]) } else { LikeTok::Any })
}

/// The tokens of `p ++ [%]` from character `k`.
proof fn lemma_prefix_tokens(p: Seq<u8>, k: int)
    requires plain_prefix(p), 0 <= k <= p.len(),
    ensures like_tokens(byte_chars(p.push(0x25u8)), Some(seq![92u8]), k) == prefix_toks(p).subrange(k, p.len() as int + 1),
    decreases p.len() - k,
{
    let pc = byte_chars(p.push(0x25u8));
    let esc = Some(seq![92u8]);
    if k == p.len() {
        assert(pc[k] == seq![0x25u8]);
        assert(seq![0x25u8] != seq![92u8]) by { assert(seq![0x25u8][0] != seq![92u8][0]); }
        assert(pc[k] == pct());
        assert(like_tokens(pc, esc, k + 1) =~= Seq::<LikeTok>::empty());
        assert(seq![LikeTok::Any] + Seq::<LikeTok>::empty() =~= prefix_toks(p).subrange(k, p.len() as int + 1));
    } else {
        lemma_prefix_tokens(p, k + 1);
        assert(pc[k] == seq![p[k]]);
        assert(p[k] != 92u8 && p[k] != 0x25u8 && p[k] != 0x5Fu8);
        assert(seq![p[k]] != seq![92u8]) by { assert(seq![p[k]][0] != seq![92u8][0]); }
        assert(seq![p[k]] != pct()) by { assert(seq![p[k]][0] != pct()[0]); }
        assert(seq![p[k]] != underscore()) by { assert(seq![p[k]][0] != underscore()[0]); }
        assert(seq![LikeTok::Lit(seq![p[k]])] + prefix_toks(p).subrange(k + 1, p.len() as int + 1)
            =~= prefix_toks(p).subrange(k, p.len() as int + 1));
    }
}

/// The matcher on the prefix tokens from position `i` (`i <= t.len()`): a match exactly when the next characters are
/// `p[i..]`.
proof fn lemma_prefix_mt(t: Seq<Seq<u8>>, p: Seq<u8>, i: int)
    requires 0 <= i <= p.len(), i <= t.len(),
    ensures
        like_mt(t, prefix_toks(p), i, i) is Ok,
        (like_mt(t, prefix_toks(p), i, i) == Ok::<LikeRes, SqlError>(LikeRes::Match))
            == (t.len() >= p.len() && forall|j: int| i <= j < p.len() ==> #[trigger] t[j] == seq![p[j]]),
    decreases p.len() - i,
{
    let toks = prefix_toks(p);
    let rhs = t.len() >= p.len() && forall|j: int| i <= j < p.len() ==> #[trigger] t[j] == seq![p[j]];
    if i < p.len() {
        assert(toks[i] == LikeTok::Lit(seq![p[i]]));
        if i < t.len() {
            if t[i] == seq![p[i]] {
                lemma_prefix_mt(t, p, i + 1);
                assert(like_mt(t, toks, i, i) == like_mt(t, toks, i + 1, i + 1));
                let rhs1 = t.len() >= p.len() && forall|j: int| i + 1 <= j < p.len() ==> #[trigger] t[j] == seq![p[j]];
                if rhs1 {
                    assert forall|j: int| i <= j < p.len() implies #[trigger] t[j] == seq![p[j]] by {
                        if j > i {
                            assert(i + 1 <= j < p.len());
                        }
                    }
                }
                if rhs {
                    assert forall|j: int| i + 1 <= j < p.len() implies #[trigger] t[j] == seq![p[j]] by {
                        assert(i <= j < p.len());
                    }
                }
                assert(rhs == rhs1);
            } else {
                assert(like_mt(t, toks, i, i) == Ok::<LikeRes, SqlError>(LikeRes::NoMatch));
                if rhs {
                    assert(t[i] == seq![p[i]]);
                }
            }
        } else {
            assert(like_mt(t, toks, i, i) == like_end(toks, i));
            assert(like_end(toks, i) == Ok::<LikeRes, SqlError>(LikeRes::Abort));
            assert(!rhs);
        }
    } else {
        assert(toks[i] == LikeTok::Any);
        if i < t.len() {
            assert(like_any(t, toks, i, i + 1) == Ok::<LikeRes, SqlError>(LikeRes::Match));
            assert(like_mt(t, toks, i, i) == like_any(t, toks, i, i + 1));
        } else {
            assert(like_end(toks, i + 1) == Ok::<LikeRes, SqlError>(LikeRes::Match));
            assert(like_end(toks, i) == like_end(toks, i + 1));
            assert(like_mt(t, toks, i, i) == like_end(toks, i));
        }
        assert(rhs);
    }
}

/// The characters of `t` start with the bytes of `p` (one character each) exactly under `prefix_cond`.
proof fn lemma_prefix_chars(t: Seq<u8>, p: Seq<u8>)
    requires is_ascii(p), p.len() >= 1,
    ensures
        (chars(t).len() >= p.len() && forall|j: int| 0 <= j < p.len() ==> #[trigger] chars(t)[j] == seq![p[j]])
            == prefix_cond(t, p),
{
    let m = p.len() as int;
    let cs = chars(t);
    if chars(t).len() >= p.len() && forall|j: int| 0 <= j < p.len() ==> #[trigger] chars(t)[j] == seq![p[j]] {
        lemma_concat_chars(t);
        lemma_concat_split(cs, m);
        let pre = cs.subrange(0, m);
        assert forall|j: int| 0 <= j < m implies #[trigger] pre[j] == seq![p[j]] by {
            assert(pre[j] == cs[j]);
        }
        lemma_concat_bytes(pre, p);
        assert(t =~= p + concat(cs.subrange(m, cs.len() as int)));
        assert(t.subrange(0, m) =~= p);
        if t.len() > m {
            if cs.len() == m {
                assert(cs.subrange(m, cs.len() as int) =~= Seq::<Seq<u8>>::empty());
                assert(concat(Seq::<Seq<u8>>::empty()) == Seq::<u8>::empty());
                assert(false);
            }
            lemma_chars_heads(t);
            lemma_chars_nonempty(t);
            let rest = cs.subrange(m, cs.len() as int);
            lemma_concat_split(rest, 1);
            let one = rest.subrange(0, 1);
            assert(one.drop_last() =~= Seq::<Seq<u8>>::empty());
            assert(concat(one) == concat(Seq::<Seq<u8>>::empty()) + one.last());
            assert(concat(Seq::<Seq<u8>>::empty()) == Seq::<u8>::empty());
            assert(one.last() == cs[m]);
            assert(cs[m].len() > 0);
            assert(t[m] == cs[m][0]);
            assert(!is_cont(cs[m][0]));
        }
    }
    if prefix_cond(t, p) {
        lemma_chars_split(t, m);
        let a = t.subrange(0, m);
        assert(a == p);
        lemma_ascii_chars(p);
        assert forall|j: int| 0 <= j < p.len() implies #[trigger] chars(t)[j] == seq![p[j]] by {
            assert(chars(t)[j] == chars(a)[j]);
        }
    }
}

/// `t LIKE p% ESCAPE '\'` for a plain prefix `p` (at least one byte) is `prefix_cond(t, p)`, never an error.
pub proof fn lemma_prefix_like(t: Seq<u8>, p: Seq<u8>)
    requires plain_prefix(p), p.len() >= 1,
    ensures like_value(Val::Text(t), Val::Text(p.push(0x25u8)), Val::Text(seq![92u8]))
        == Ok::<Val, SqlError>(Val::Bool(prefix_cond(t, p))),
{
    let pat = p.push(0x25u8);
    assert(is_ascii(pat)) by {
        assert forall|i: int| 0 <= i < pat.len() implies #[trigger] pat[i] < 0x80u8 by {
            if i < p.len() { assert(pat[i] == p[i]); }
        }
    }
    assert(is_ascii(p)) by {
        assert forall|i: int| 0 <= i < p.len() implies #[trigger] p[i] < 0x80u8 by {}
    }
    lemma_ascii_chars(pat);
    lemma_prefix_tokens(p, 0);
    assert(prefix_toks(p).subrange(0, p.len() as int + 1) =~= prefix_toks(p));
    lemma_like_value_err(t, pat);
    lemma_prefix_mt(chars(t), p, 0);
    lemma_prefix_chars(t, p);
}

// ------------------------------------------------------------------------------------------------ intervals

/// The texts in `[q ++ [a], q ++ [b])` (bytewise, `a < b`) are those starting with `q` followed by a byte in `[a, b)`.
pub proof fn lemma_lex_interval(q: Seq<u8>, a: u8, b: u8, t: Seq<u8>)
    requires a < b,
    ensures
        (lex_cmp(q.push(a), t) <= 0 && lex_cmp(t, q.push(b)) < 0)
            == (t.len() > q.len() && t.subrange(0, q.len() as int) == q && a <= t[q.len() as int] < b),
    decreases q.len(),
{
    let qa = q.push(a);
    let qb = q.push(b);
    let rhs = t.len() > q.len() && t.subrange(0, q.len() as int) == q && a <= t[q.len() as int] < b;
    if t.len() == 0 {
        assert(lex_cmp(qa, t) == 1);
        assert(!rhs);
    } else if q.len() == 0 {
        assert(qa[0] == a && qb[0] == b);
        assert(qa.drop_first() =~= Seq::<u8>::empty());
        assert(qb.drop_first() =~= Seq::<u8>::empty());
        assert(t.subrange(0, 0) =~= q);
        let t1 = t.drop_first();
        if a == t[0] {
            assert(lex_cmp(qa, t) == lex_cmp(Seq::<u8>::empty(), t1));
            assert(lex_cmp(Seq::<u8>::empty(), t1) <= 0);
        }
        if t[0] == b {
            assert(lex_cmp(t, qb) == lex_cmp(t1, Seq::<u8>::empty()));
            assert(lex_cmp(t1, Seq::<u8>::empty()) >= 0);
        }
        assert((lex_cmp(qa, t) <= 0) == (a <= t[0]));
        assert((lex_cmp(t, qb) < 0) == (t[0] < b));
    } else {
        let q1 = q.drop_first();
        let t1 = t.drop_first();
        assert(qa.drop_first() =~= q1.push(a));
        assert(qb.drop_first() =~= q1.push(b));
        assert(qa[0] == q[0] && qb[0] == q[0]);
        if t[0] == q[0] {
            lemma_lex_interval(q1, a, b, t1);
            assert(lex_cmp(qa, t) == lex_cmp(q1.push(a), t1));
            assert(lex_cmp(t, qb) == lex_cmp(t1, q1.push(b)));
            let rhs1 = t1.len() > q1.len() && t1.subrange(0, q1.len() as int) == q1 && a <= t1[q1.len() as int] < b;
            if rhs1 {
                assert forall|k: int| 0 <= k < q.len() implies #[trigger] t.subrange(0, q.len() as int)[k] == q[k] by {
                    if k > 0 {
                        assert(t[k] == t1[k - 1]);
                        assert(t1.subrange(0, q1.len() as int)[k - 1] == q1[k - 1]);
                    }
                }
                assert(t.subrange(0, q.len() as int) =~= q);
                assert(t[q.len() as int] == t1[q1.len() as int]);
            }
            if rhs {
                assert forall|k: int| 0 <= k < q1.len() implies #[trigger] t1.subrange(0, q1.len() as int)[k] == q1[k] by {
                    assert(t.subrange(0, q.len() as int)[k + 1] == q[k + 1]);
                }
                assert(t1.subrange(0, q1.len() as int) =~= q1);
                assert(t[q.len() as int] == t1[q1.len() as int]);
            }
            assert(rhs == rhs1);
        } else {
            if rhs {
                assert(t.subrange(0, q.len() as int)[0] == q[0]);
            }
            if q[0] < t[0] {
                assert(lex_cmp(t, qb) == 1);
            } else {
                assert(lex_cmp(qa, t) == 1);
            }
        }
    }
}

} // verus!
