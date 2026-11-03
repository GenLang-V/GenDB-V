//! A text matching the LIKE pattern `%w1%w2%` (ASCII words without `%`, `_` or the escape) spells `w1` and, after it,
//! `w2` in its bytes: the byte-level necessary condition of a substring LIKE (`lemma_two_words`), so a byte search
//! that finds no such occurrence proves the LIKE false.
//!
//! Steps: an ASCII pattern's characters are its bytes (`lemma_chars_ascii`) and its tokens are `%` -> Any, `_` -> One,
//! other bytes literal (`lemma_tokens_ascii`); the standard matcher's meaning (`like_std`, which
//! `bridge::fns::like::lemma_like_mt_std` ties to the matcher) consumes a run of literal tokens as consecutive
//! one-byte characters (`lemma_std_lits`); and a one-byte character at character index `k` is the byte at
//! `pos(t, k)`, the length of the characters before it (`lemma_char_byte`).
use vstd::prelude::*;
use crate::spec::chars::*;
use crate::spec::value::SqlError;
use crate::spec::fns::like::*;
use crate::bridge::fns::like::{lemma_std_any, std_from, no_dangling};

verus! {

/// Every byte is ASCII (below 0x80, so no UTF-8 continuation byte).
pub open spec fn ascii(b: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < b.len() ==> (#[trigger] b[i]) < 0x80u8
}

/// The characters of ASCII bytes are the bytes one by one.
pub proof fn lemma_chars_ascii(b: Seq<u8>)
    requires ascii(b),
    ensures chars(b) == b.map_values(|x: u8| seq![x]),
    decreases b.len(),
{
    if b.len() > 0 {
        let d = b.drop_last();
        assert(ascii(d)) by {
            assert forall|i: int| 0 <= i < d.len() implies (#[trigger] d[i]) < 0x80u8 by { assert(d[i] == b[i]); }
        }
        lemma_chars_ascii(d);
        assert(!is_cont(b.last()));
        assert(b.map_values(|x: u8| seq![x]) =~= d.map_values(|x: u8| seq![x]).push(seq![b.last()]));
    }
}

/// The token of one pattern byte (no escaping).
pub open spec fn tok_of(c: u8) -> LikeTok {
    if c == 0x25u8 { LikeTok::Any } else if c == 0x5Fu8 { LikeTok::One } else { LikeTok::Lit(seq![c]) }
}

/// The tokens of an ASCII pattern without the escape byte: one token per byte.
pub proof fn lemma_tokens_ascii(pat: Seq<u8>, e: u8, k: int)
    requires
        ascii(pat),
        forall|i: int| 0 <= i < pat.len() ==> #[trigger] pat[i] != e,
        0 <= k <= pat.len(),
    ensures
        like_tokens(chars(pat), Some(seq![e]), k) == pat.subrange(k, pat.len() as int).map_values(|c: u8| tok_of(c)),
    decreases pat.len() - k,
{
    lemma_chars_ascii(pat);
    let pc = chars(pat);
    let ts = like_tokens(pc, Some(seq![e]), k);
    let want = pat.subrange(k, pat.len() as int).map_values(|c: u8| tok_of(c));
    if k < pat.len() {
        lemma_tokens_ascii(pat, e, k + 1);
        let rest = like_tokens(pc, Some(seq![e]), k + 1);
        assert(pc[k] == seq![pat[k]]);
        assert(seq![pat[k]] != seq![e]) by {
            assert(seq![pat[k]][0] != seq![e][0]);
        }
        assert(pct() == seq![0x25u8]);
        assert(underscore() == seq![0x5Fu8]);
        if pat[k] == 0x25u8 {
            assert(pc[k] == pct());
        } else {
            assert(pc[k] != pct()) by {
                assert(pc[k][0] != pct()[0]);
            }
            if pat[k] == 0x5Fu8 {
                assert(pc[k] == underscore());
            } else {
                assert(pc[k] != underscore()) by {
                    assert(pc[k][0] != underscore()[0]);
                }
            }
        }
        assert(ts == seq![tok_of(pat[k])] + rest);
        assert(want =~= seq![tok_of(pat[k])] + pat.subrange(k + 1, pat.len() as int).map_values(|c: u8| tok_of(c)));
    } else {
        assert(want =~= Seq::<LikeTok>::empty());
    }
}

/// A run of literal tokens `p[j .. j + |w|]` for the bytes of `w` consumes `|w|` one-byte characters.
pub proof fn lemma_std_lits(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int, j: int, w: Seq<u8>)
    requires
        0 <= j, j + w.len() <= p.len(),
        forall|m: int| 0 <= m < w.len() ==> #[trigger] p[j + m] == LikeTok::Lit(seq![w[m]]),
        like_std(t, p, i, j),
    ensures
        0 <= i, i + w.len() <= t.len(),
        forall|m: int| 0 <= m < w.len() ==> #[trigger] t[i + m] == seq![w[m]],
        like_std(t, p, i + w.len(), j + w.len()),
    decreases w.len(),
{
    if w.len() > 0 {
        assert(p[j + 0] == LikeTok::Lit(seq![w[0]]));
        assert(t[i] == seq![w[0]]);
        let w2 = w.drop_first();
        assert forall|m: int| 0 <= m < w2.len() implies #[trigger] p[(j + 1) + m] == LikeTok::Lit(seq![w2[m]]) by {
            assert(p[j + (m + 1)] == LikeTok::Lit(seq![w[m + 1]]));
        }
        lemma_std_lits(t, p, i + 1, j + 1, w2);
        assert forall|m: int| 0 <= m < w.len() implies #[trigger] t[i + m] == seq![w[m]] by {
            if m > 0 {
                assert(t[(i + 1) + (m - 1)] == seq![w2[m - 1]]);
            }
        }
    }
}

/// Byte position of character `k`: the length of the characters before it.
pub open spec fn pos(t: Seq<Seq<u8>>, k: int) -> int {
    concat(t.subrange(0, k)).len() as int
}

/// Concatenation distributes over appending.
pub proof fn lemma_concat_add(a: Seq<Seq<u8>>, b: Seq<Seq<u8>>)
    ensures concat(a + b) == concat(a) + concat(b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(concat(b) =~= Seq::<u8>::empty());
        assert(concat(a) + concat(b) =~= concat(a));
    } else {
        lemma_concat_add(a, b.drop_last());
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
        assert(concat(a) + concat(b) =~= concat(a) + concat(b.drop_last()) + b.last());
    }
}

/// Character `k` of `t` sits at byte `pos(t, k)` of `concat(t)`, and the next character starts after it.
pub proof fn lemma_char_byte(t: Seq<Seq<u8>>, k: int)
    requires 0 <= k < t.len(),
    ensures
        pos(t, k + 1) == pos(t, k) + t[k].len(),
        pos(t, k) + t[k].len() <= concat(t).len(),
        forall|q: int| 0 <= q < t[k].len() ==> #[trigger] concat(t)[pos(t, k) + q] == t[k][q],
{
    let pre = t.subrange(0, k);
    let rest = t.subrange(k + 1, t.len() as int);
    assert(t.subrange(0, k + 1) =~= pre.push(t[k]));
    assert(concat(pre.push(t[k])) == concat(pre) + t[k]) by {
        assert(pre.push(t[k]).drop_last() =~= pre);
    }
    assert(t =~= pre.push(t[k]) + rest);
    lemma_concat_add(pre.push(t[k]), rest);
    let whole = concat(pre) + t[k] + concat(rest);
    assert(concat(t) == whole);
    assert forall|q: int| 0 <= q < t[k].len() implies #[trigger] concat(t)[pos(t, k) + q] == t[k][q] by {
        assert(whole[concat(pre).len() + q] == t[k][q]);
    }
}

/// Character positions are nondecreasing.
pub proof fn lemma_pos_mono(t: Seq<Seq<u8>>, a: int, b: int)
    requires 0 <= a <= b <= t.len(),
    ensures pos(t, a) <= pos(t, b),
    decreases b - a,
{
    if a < b {
        lemma_pos_mono(t, a, b - 1);
        lemma_char_byte(t, b - 1);
    }
}

/// A run of one-byte characters `t[i .. i + |w|]` spelling `w` is the bytes of `w` at `pos(t, i)`.
pub proof fn lemma_run_bytes(t: Seq<Seq<u8>>, i: int, w: Seq<u8>)
    requires
        0 <= i, i + w.len() <= t.len(),
        forall|m: int| 0 <= m < w.len() ==> #[trigger] t[i + m] == seq![w[m]],
    ensures
        pos(t, i + w.len()) == pos(t, i) + w.len(),
        forall|m: int| 0 <= m < w.len() ==> #[trigger] concat(t)[pos(t, i) + m] == w[m],
    decreases w.len(),
{
    if w.len() > 0 {
        let w2 = w.drop_last();
        assert forall|m: int| 0 <= m < w2.len() implies #[trigger] t[i + m] == seq![w2[m]] by {
            assert(t[i + m] == seq![w[m]]);
        }
        lemma_run_bytes(t, i, w2);
        let k = i + w2.len();
        assert(t[k] == seq![w[w2.len() as int]]);
        lemma_char_byte(t, k);
        assert(concat(t)[pos(t, k) + 0] == t[k][0]);
        assert forall|m: int| 0 <= m < w.len() implies #[trigger] concat(t)[pos(t, i) + m] == w[m] by {
            if m < w2.len() {
                assert(concat(t)[pos(t, i) + m] == w2[m]);
            }
        }
    }
}

/// `w` occurs in `b` at byte `p`.
pub open spec fn occurs_at(b: Seq<u8>, w: Seq<u8>, p: int) -> bool {
    0 <= p && p + w.len() <= b.len() && forall|m: int| 0 <= m < w.len() ==> #[trigger] b[p + m] == w[m]
}

/// The pattern `%w1%w2%`.
pub open spec fn two_words(w1: Seq<u8>, w2: Seq<u8>) -> Seq<u8> {
    seq![0x25u8] + w1 + seq![0x25u8] + w2 + seq![0x25u8]
}

/// A word of the pattern: ASCII, without `%`, `_` or the escape byte.
pub open spec fn word_ok(w: Seq<u8>, e: u8) -> bool {
    &&& ascii(w)
    &&& forall|i: int| 0 <= i < w.len() ==> #[trigger] w[i] != 0x25u8 && w[i] != 0x5Fu8 && w[i] != e
}

/// A text whose characters match `%w1%w2%` holds `w1` at some byte and `w2` at a later byte.
pub proof fn lemma_two_words(b: Seq<u8>, w1: Seq<u8>, w2: Seq<u8>, e: u8)
    requires
        word_ok(w1, e), word_ok(w2, e),
        e < 0x80u8, e != 0x25u8,
        like_mt(chars(b), like_tokens(chars(two_words(w1, w2)), Some(seq![e]), 0), 0, 0) == Ok::<LikeRes, SqlError>(LikeRes::Match),
    ensures
        exists|p1: int, p2: int| p1 + w1.len() <= p2 && #[trigger] occurs_at(b, w1, p1) && #[trigger] occurs_at(b, w2, p2),
{
    let pat = two_words(w1, w2);
    let (n1, n2) = (w1.len() as int, w2.len() as int);
    assert(pat.len() == n1 + n2 + 3);
    assert forall|i: int| 0 <= i < pat.len() implies (#[trigger] pat[i]) < 0x80u8 && pat[i] != e by {
        if 1 <= i < 1 + n1 {
            assert(pat[i] == w1[i - 1]);
        } else if 2 + n1 <= i < 2 + n1 + n2 {
            assert(pat[i] == w2[i - 2 - n1]);
        }
    }
    lemma_tokens_ascii(pat, e, 0);
    let p = like_tokens(chars(pat), Some(seq![e]), 0);
    assert(p == pat.subrange(0, pat.len() as int).map_values(|c: u8| tok_of(c)));
    assert(pat.subrange(0, pat.len() as int) =~= pat);
    let t = chars(b);
    crate::bridge::fns::like::lemma_like_mt_std(t, p);
    assert(like_std(t, p, 0, 0));
    // The tokens: `%`, w1's literals, `%`, w2's literals, `%`.
    assert(p[0] == LikeTok::Any);
    assert forall|m: int| 0 <= m < n1 implies #[trigger] p[1 + m] == LikeTok::Lit(seq![w1[m]]) by {
        assert(pat[1 + m] == w1[m]);
    }
    assert(pat[1 + n1] == 0x25u8);
    assert(p[1 + n1] == LikeTok::Any);
    assert forall|m: int| 0 <= m < n2 implies #[trigger] p[(2 + n1) + m] == LikeTok::Lit(seq![w2[m]]) by {
        assert(pat[(2 + n1) + m] == w2[m]);
    }
    // First `%`: some start i1 of w1's run.
    lemma_std_any(t, p, 0, 0);
    let i1 = choose|k: int| 0 <= k <= t.len() && #[trigger] like_std(t, p, k, 1);
    lemma_std_lits(t, p, i1, 1, w1);
    // Second `%`: some start i2 >= i1 + |w1| of w2's run.
    lemma_std_any(t, p, i1 + n1, 1 + n1);
    let i2 = choose|k: int| i1 + n1 <= k <= t.len() && #[trigger] like_std(t, p, k, 2 + n1);
    lemma_std_lits(t, p, i2, 2 + n1, w2);
    // Bytes.
    lemma_concat_chars(b);
    lemma_run_bytes(t, i1, w1);
    lemma_run_bytes(t, i2, w2);
    lemma_pos_mono(t, i1 + n1, i2);
    lemma_pos_mono(t, i2 + n2, t.len() as int);
    assert(t.subrange(0, t.len() as int) =~= t);
    let (p1, p2) = (pos(t, i1), pos(t, i2));
    lemma_pos_nonneg(t, i1);
    assert(occurs_at(b, w1, p1));
    assert(occurs_at(b, w2, p2));
}


// ------------------------------------------------------------------------------------------------ exactness

/// A nonempty text has characters, each nonempty; every character after the first starts with a byte that is no
/// continuation byte.
pub proof fn lemma_chars_heads(b: Seq<u8>)
    ensures
        b.len() > 0 ==> chars(b).len() > 0,
        forall|k: int| 0 <= k < chars(b).len() ==> (#[trigger] chars(b)[k]).len() > 0,
        forall|k: int| 1 <= k < chars(b).len() ==> !is_cont(#[trigger] chars(b)[k][0]),
    decreases b.len(),
{
    if b.len() > 0 {
        let d = b.drop_last();
        lemma_chars_heads(d);
        let cs = chars(d);
        let x = b.last();
        if is_cont(x) && cs.len() > 0 {
            let r = cs.drop_last().push(cs.last().push(x));
            assert(chars(b) == r);
            assert forall|k: int| 0 <= k < r.len() implies (#[trigger] r[k]).len() > 0 by {
                if k < r.len() - 1 { assert(r[k] == cs[k]); }
            }
            assert forall|k: int| 1 <= k < r.len() implies !is_cont(#[trigger] r[k][0]) by {
                if k < r.len() - 1 {
                    assert(r[k] == cs[k]);
                } else {
                    assert(r[k] == cs.last().push(x));
                    assert(cs.last().len() > 0);
                    assert(r[k][0] == cs[k][0]);
                }
            }
        } else {
            let r = cs.push(seq![x]);
            assert(chars(b) == r);
            assert forall|k: int| 0 <= k < r.len() implies (#[trigger] r[k]).len() > 0 by {
                if k < r.len() - 1 { assert(r[k] == cs[k]); }
            }
            assert forall|k: int| 1 <= k < r.len() implies !is_cont(#[trigger] r[k][0]) by {
                if k < r.len() - 1 { assert(r[k] == cs[k]); }
            }
        }
    }
}

/// Characters split where a byte that is no continuation byte starts the second part.
pub proof fn lemma_chars_split(u: Seq<u8>, v: Seq<u8>)
    requires v.len() > 0, !is_cont(v[0]),
    ensures chars(u + v) == chars(u) + chars(v),
    decreases v.len(),
{
    if v.len() == 1 {
        assert((u + v).drop_last() =~= u);
        assert((u + v).last() == v[0]);
        assert(v.drop_last() =~= Seq::<u8>::empty());
        assert(chars(v) == chars(Seq::<u8>::empty()).push(seq![v[0]]));
        assert(chars(v) =~= seq![seq![v[0]]]);
        assert(chars(u + v) =~= chars(u) + chars(v));
    } else {
        let v2 = v.drop_last();
        let x = v.last();
        lemma_chars_split(u, v2);
        lemma_chars_heads(v2);
        assert((u + v).drop_last() =~= u + v2);
        assert((u + v).last() == x);
        assert(v.drop_last() == v2);
        let cs = chars(u + v2);
        assert(cs == chars(u) + chars(v2));
        assert(cs.len() > 0);
        if is_cont(x) {
            assert(chars(u + v) == cs.drop_last().push(cs.last().push(x)));
            assert(chars(v) == chars(v2).drop_last().push(chars(v2).last().push(x)));
            assert(cs.last() == chars(v2).last());
            assert(chars(u + v) =~= chars(u) + chars(v));
        } else {
            assert(chars(u + v) == cs.push(seq![x]));
            assert(chars(v) == chars(v2).push(seq![x]));
            assert(chars(u + v) =~= chars(u) + chars(v));
        }
    }
}

/// A run of literal tokens is consumed by the same one-byte characters (the converse of `lemma_std_lits`).
pub proof fn lemma_std_lits_rev(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int, j: int, w: Seq<u8>)
    requires
        0 <= i, i + w.len() <= t.len(),
        0 <= j, j + w.len() <= p.len(),
        forall|m: int| 0 <= m < w.len() ==> #[trigger] p[j + m] == LikeTok::Lit(seq![w[m]]),
        forall|m: int| 0 <= m < w.len() ==> #[trigger] t[i + m] == seq![w[m]],
        like_std(t, p, i + w.len(), j + w.len()),
    ensures like_std(t, p, i, j),
    decreases w.len(),
{
    if w.len() > 0 {
        let w2 = w.drop_first();
        assert forall|m: int| 0 <= m < w2.len() implies #[trigger] p[(j + 1) + m] == LikeTok::Lit(seq![w2[m]]) by {
            assert(p[j + (m + 1)] == LikeTok::Lit(seq![w[m + 1]]));
        }
        assert forall|m: int| 0 <= m < w2.len() implies #[trigger] t[(i + 1) + m] == seq![w2[m]] by {
            assert(t[i + (m + 1)] == seq![w[m + 1]]);
        }
        lemma_std_lits_rev(t, p, i + 1, j + 1, w2);
        assert(p[j + 0] == LikeTok::Lit(seq![w[0]]));
        assert(t[i + 0] == seq![w[0]]);
    }
}

/// `w` occurs at byte `p` and the byte after it, if any, is no continuation byte (so `w` ends a character).
pub open spec fn proper_at(b: Seq<u8>, w: Seq<u8>, p: int) -> bool {
    &&& occurs_at(b, w, p)
    &&& (p + w.len() == b.len() || !is_cont(b[p + w.len()]))
}

/// `w1` and, after it, `w2`, each ending a character.
pub open spec fn proper_two(b: Seq<u8>, w1: Seq<u8>, w2: Seq<u8>) -> bool {
    exists|p1: int, p2: int| p1 + w1.len() <= p2 && #[trigger] proper_at(b, w1, p1) && #[trigger] proper_at(b, w2, p2)
}

/// The tokens of `%w1%w2%`.
proof fn lemma_two_tokens(w1: Seq<u8>, w2: Seq<u8>, e: u8)
    requires word_ok(w1, e), word_ok(w2, e), e < 0x80u8, e != 0x25u8,
    ensures ({
        let p = like_tokens(chars(two_words(w1, w2)), Some(seq![e]), 0);
        let (n1, n2) = (w1.len() as int, w2.len() as int);
        &&& p.len() == n1 + n2 + 3
        &&& no_dangling(p)
        &&& p[0] == LikeTok::Any
        &&& forall|m: int| 0 <= m < n1 ==> #[trigger] p[1 + m] == LikeTok::Lit(seq![w1[m]])
        &&& p[1 + n1] == LikeTok::Any
        &&& forall|m: int| 0 <= m < n2 ==> #[trigger] p[(2 + n1) + m] == LikeTok::Lit(seq![w2[m]])
        &&& p[2 + n1 + n2] == LikeTok::Any
    }),
{
    let pat = two_words(w1, w2);
    let (n1, n2) = (w1.len() as int, w2.len() as int);
    assert(pat.len() == n1 + n2 + 3);
    assert forall|i: int| 0 <= i < pat.len() implies (#[trigger] pat[i]) < 0x80u8 && pat[i] != e by {
        if 1 <= i < 1 + n1 {
            assert(pat[i] == w1[i - 1]);
        } else if 2 + n1 <= i < 2 + n1 + n2 {
            assert(pat[i] == w2[i - 2 - n1]);
        }
    }
    lemma_tokens_ascii(pat, e, 0);
    let p = like_tokens(chars(pat), Some(seq![e]), 0);
    assert(pat.subrange(0, pat.len() as int) =~= pat);
    assert(p == pat.map_values(|c: u8| tok_of(c)));
    assert forall|m: int| 0 <= m < n1 implies #[trigger] p[1 + m] == LikeTok::Lit(seq![w1[m]]) by {
        assert(pat[1 + m] == w1[m]);
    }
    assert(pat[1 + n1] == 0x25u8);
    assert forall|m: int| 0 <= m < n2 implies #[trigger] p[(2 + n1) + m] == LikeTok::Lit(seq![w2[m]]) by {
        assert(pat[(2 + n1) + m] == w2[m]);
    }
    assert(pat[2 + n1 + n2] == 0x25u8);
    assert forall|k: int| 0 <= k < p.len() implies !(#[trigger] p[k] is Dangling) by {
        assert(p[k] == tok_of(pat[k]));
    }
}

/// The one-byte characters of an ASCII word.
proof fn lemma_word_chars(w: Seq<u8>, e: u8)
    requires word_ok(w, e),
    ensures
        chars(w).len() == w.len(),
        forall|m: int| 0 <= m < w.len() ==> #[trigger] chars(w)[m] == seq![w[m]],
{
    lemma_chars_ascii(w);
}

/// A text with `w1` and, after it, `w2`, each ending a character, matches `%w1%w2%`.
pub proof fn lemma_two_words_back(b: Seq<u8>, w1: Seq<u8>, w2: Seq<u8>, e: u8)
    requires
        word_ok(w1, e), word_ok(w2, e), w1.len() > 0, w2.len() > 0,
        e < 0x80u8, e != 0x25u8,
        proper_two(b, w1, w2),
    ensures
        like_mt(chars(b), like_tokens(chars(two_words(w1, w2)), Some(seq![e]), 0), 0, 0) == Ok::<LikeRes, SqlError>(LikeRes::Match),
{
    let (n1, n2) = (w1.len() as int, w2.len() as int);
    let (p1, p2) = choose|p1: int, p2: int| p1 + w1.len() <= p2 && #[trigger] proper_at(b, w1, p1) && #[trigger] proper_at(b, w2, p2);
    let ba = b.subrange(0, p1);
    let bb = b.subrange(p1 + n1, p2);
    let bc = b.subrange(p2 + n2, b.len() as int);
    let r2 = w2 + bc;
    let r1 = bb + r2;
    let r0 = w1 + r1;
    assert(b =~= ba + r0) by {
        assert((ba + r0).len() == b.len());
        assert forall|k: int| 0 <= k < b.len() implies #[trigger] (ba + r0)[k] == b[k] by {
            if k < p1 {
            } else if k < p1 + n1 {
                assert(b[p1 + (k - p1)] == w1[k - p1]);
                assert((ba + r0)[k] == r0[k - p1]);
            } else if k < p2 {
                assert((ba + r0)[k] == r0[k - p1]);
                assert(r0[k - p1] == r1[k - p1 - n1]);
                assert(r1[k - p1 - n1] == bb[k - p1 - n1]);
            } else if k < p2 + n2 {
                assert(b[p2 + (k - p2)] == w2[k - p2]);
                assert((ba + r0)[k] == r0[k - p1]);
                assert(r0[k - p1] == r1[k - p1 - n1]);
                assert(r1[k - p1 - n1] == r2[k - p2]);
            } else {
                assert((ba + r0)[k] == r0[k - p1]);
                assert(r0[k - p1] == r1[k - p1 - n1]);
                assert(r1[k - p1 - n1] == r2[k - p2]);
                assert(r2[k - p2] == bc[k - p2 - n2]);
            }
        }
    }
    assert(w1[0] < 0x80u8);
    assert(w2[0] < 0x80u8);
    // chars(b) = chars(ba) + chars(w1) + chars(bb) + chars(w2) + chars(bc).
    lemma_chars_split(ba, r0);
    assert(r1.len() > 0 && r1[0] == b[p1 + n1]);
    lemma_chars_split(w1, r1);
    if bb.len() > 0 {
        lemma_chars_split(bb, r2);
    } else {
        assert(r1 =~= r2);
        assert(chars(bb) =~= Seq::<Seq<u8>>::empty());
        assert(chars(r1) =~= chars(bb) + chars(r2));
    }
    if bc.len() > 0 {
        assert(bc[0] == b[p2 + n2]);
        lemma_chars_split(w2, bc);
    } else {
        assert(r2 =~= w2);
        assert(chars(bc) =~= Seq::<Seq<u8>>::empty());
        assert(chars(r2) =~= chars(w2) + chars(bc));
    }
    lemma_word_chars(w1, e);
    lemma_word_chars(w2, e);
    let (ta, tb, tc) = (chars(ba), chars(bb), chars(bc));
    let t = chars(b);
    assert(t =~= ta + chars(w1) + tb + chars(w2) + tc);
    let (i1, i2) = (ta.len() as int, ta.len() + n1 + tb.len());
    assert forall|m: int| 0 <= m < n1 implies #[trigger] t[i1 + m] == seq![w1[m]] by {
        assert(t[i1 + m] == chars(w1)[m]);
    }
    assert forall|m: int| 0 <= m < n2 implies #[trigger] t[i2 + m] == seq![w2[m]] by {
        assert(t[i2 + m] == chars(w2)[m]);
    }
    lemma_two_tokens(w1, w2, e);
    let p = like_tokens(chars(two_words(w1, w2)), Some(seq![e]), 0);
    // The last `%` takes the rest.
    assert(like_std(t, p, t.len() as int, 3 + n1 + n2));
    lemma_std_any(t, p, i2 + n2, 2 + n1 + n2);
    assert(like_std(t, p, i2 + n2, 2 + n1 + n2));
    lemma_std_lits_rev(t, p, i2, 2 + n1, w2);
    lemma_std_any(t, p, i1 + n1, 1 + n1);
    assert(like_std(t, p, i1 + n1, 1 + n1));
    lemma_std_lits_rev(t, p, i1, 1, w1);
    lemma_std_any(t, p, 0, 0);
    assert(like_std(t, p, 0, 0));
    crate::bridge::fns::like::lemma_like_mt_std(t, p);
}

/// A text matching `%w1%w2%` has `w1` and, after it, `w2`, each ending a character.
pub proof fn lemma_two_words_fwd(b: Seq<u8>, w1: Seq<u8>, w2: Seq<u8>, e: u8)
    requires
        word_ok(w1, e), word_ok(w2, e), w1.len() > 0, w2.len() > 0,
        e < 0x80u8, e != 0x25u8,
        like_mt(chars(b), like_tokens(chars(two_words(w1, w2)), Some(seq![e]), 0), 0, 0) == Ok::<LikeRes, SqlError>(LikeRes::Match),
    ensures proper_two(b, w1, w2),
{
    let (n1, n2) = (w1.len() as int, w2.len() as int);
    lemma_two_tokens(w1, w2, e);
    let p = like_tokens(chars(two_words(w1, w2)), Some(seq![e]), 0);
    let t = chars(b);
    crate::bridge::fns::like::lemma_like_mt_std(t, p);
    assert(like_std(t, p, 0, 0));
    lemma_std_any(t, p, 0, 0);
    let i1 = choose|k: int| 0 <= k <= t.len() && #[trigger] like_std(t, p, k, 1);
    lemma_std_lits(t, p, i1, 1, w1);
    lemma_std_any(t, p, i1 + n1, 1 + n1);
    let i2 = choose|k: int| i1 + n1 <= k <= t.len() && #[trigger] like_std(t, p, k, 2 + n1);
    lemma_std_lits(t, p, i2, 2 + n1, w2);
    lemma_concat_chars(b);
    lemma_chars_heads(b);
    lemma_run_bytes(t, i1, w1);
    lemma_run_bytes(t, i2, w2);
    lemma_pos_mono(t, i1 + n1, i2);
    lemma_pos_mono(t, i2 + n2, t.len() as int);
    assert(t.subrange(0, t.len() as int) =~= t);
    let (p1, p2) = (pos(t, i1), pos(t, i2));
    lemma_pos_nonneg(t, i1);
    assert(occurs_at(b, w1, p1));
    assert(occurs_at(b, w2, p2));
    // The byte after each word starts the next character.
    assert(i1 + n1 < t.len());
    lemma_char_byte(t, i1 + n1);
    assert(b[pos(t, i1 + n1) + 0] == t[i1 + n1][0]);
    assert(proper_at(b, w1, p1));
    if i2 + n2 < t.len() {
        lemma_char_byte(t, i2 + n2);
        assert(b[pos(t, i2 + n2) + 0] == t[i2 + n2][0]);
    }
    assert(proper_at(b, w2, p2));
}

proof fn lemma_pos_nonneg(t: Seq<Seq<u8>>, k: int)
    ensures pos(t, k) >= 0,
{
}

} // verus!
