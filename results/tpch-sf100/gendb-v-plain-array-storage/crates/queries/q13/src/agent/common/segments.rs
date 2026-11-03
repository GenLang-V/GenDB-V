//! `s LIKE '%<s1>%<s2>%...%<sk>%'` (escape backslash) on an ASCII text `s` is "the segments occur in order without
//! overlap" (`match_from`, greedy-decidable), when every segment is non-empty ASCII without `%`, `_` and backslash
//! (`lemma_like_segments`); the pattern parser (`parse_segments`) and the greedy executable matcher
//! (`match_segments`, `no_unwind`, usable in worker tasks).
//!
//! Proof outline: the pattern's characters are its bytes, and since it holds no escape character its tokens are one
//! per byte (`%` is `Any`, any other byte a literal); the matcher never fails without a dangling escape and means
//! standard matching (`bridge::fns::like::lemma_like_mt_std`); standard matching reads a token suffix independently
//! of the tokens before it (`lemma_std_suffix`); a `%` followed by a literal run means "the run occurs at or after
//! the position" (`lemma_std_lits`, `lemma_std_segments`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::chars::*;
use crate::spec::fns::like::*;
use crate::bridge::fns::like::{no_dangling, std_from, lemma_like_mt_std, lemma_std_any};
use crate::agent::common::find::{occ, no_occ, Prefix, prefix_ok, prefix_of, find_first};

verus! {

// ------------------------------------------------------------------------------------------------ bytes and segments

/// Every byte is ASCII (below 0x80): each is a character of its own.
pub open spec fn ascii(b: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < b.len() ==> #[trigger] b[i] < 0x80u8
}

/// `lit` occurs in `s` at byte `i`.
pub open spec fn sub_at(s: Seq<u8>, lit: Seq<u8>, i: int) -> bool {
    0 <= i && i + lit.len() <= s.len() && s.subrange(i, i + lit.len()) == lit
}

/// A byte a segment may hold: ASCII, not `%`, `_` or backslash.
pub open spec fn seg_byte_ok(c: u8) -> bool {
    c < 0x80u8 && c != 0x25u8 && c != 0x5Fu8 && c != 0x5Cu8
}

/// One segment: non-empty, every byte allowed.
pub open spec fn seg_ok(s: Seq<u8>) -> bool {
    s.len() >= 1 && forall|i: int| 0 <= i < s.len() ==> #[trigger] seg_byte_ok(s[i])
}

/// Every segment is allowed.
pub open spec fn segs_ok(ss: Seq<Seq<u8>>) -> bool {
    forall|k: int| 0 <= k < ss.len() ==> #[trigger] seg_ok(ss[k])
}

/// `s1 % s2 % ... sk %`: the pattern after its first `%`.
pub open spec fn tail_pattern(ss: Seq<Seq<u8>>) -> Seq<u8>
    decreases ss.len(),
{
    if ss.len() == 0 { Seq::empty() } else { ss[0] + seq![0x25u8] + tail_pattern(ss.drop_first()) }
}

/// The pattern `%s1%s2%...%sk%`.
pub open spec fn seg_pattern(ss: Seq<Seq<u8>>) -> Seq<u8> {
    seq![0x25u8] + tail_pattern(ss)
}

/// The segments `ss` occur in `t` in order, without overlap, the first at or after byte `i`.
pub open spec fn match_from(t: Seq<u8>, ss: Seq<Seq<u8>>, i: int) -> bool
    decreases ss.len(),
{
    if ss.len() == 0 {
        true
    } else {
        exists|q: int| i <= q && #[trigger] sub_at(t, ss[0], q) && match_from(t, ss.drop_first(), q + ss[0].len())
    }
}

/// The value of `t LIKE pat` (escape backslash).
pub open spec fn like_of(t: Seq<u8>, pat: Seq<u8>) -> Result<Val, SqlError> {
    like_value(Val::Text(t), Val::Text(pat), Val::Text(seq![0x5Cu8]))
}

// ------------------------------------------------------------------------------------------------ greedy matching

/// A later start position is a stronger requirement.
pub proof fn lemma_match_mono(t: Seq<u8>, ss: Seq<Seq<u8>>, i: int, i2: int)
    requires i <= i2, match_from(t, ss, i2),
    ensures match_from(t, ss, i),
{
    if ss.len() > 0 {
        let q = choose|q: int| i2 <= q && #[trigger] sub_at(t, ss[0], q) && match_from(t, ss.drop_first(), q + ss[0].len());
        assert(i <= q && sub_at(t, ss[0], q) && match_from(t, ss.drop_first(), q + ss[0].len()));
    }
}

/// No occurrence of the first segment starts in `[i, i2)`: starting at `i` or at `i2` is the same.
pub proof fn lemma_match_skip(t: Seq<u8>, ss: Seq<Seq<u8>>, i: int, i2: int)
    requires ss.len() > 0, i <= i2, forall|q: int| i <= q < i2 ==> !#[trigger] sub_at(t, ss[0], q),
    ensures match_from(t, ss, i) == match_from(t, ss, i2),
{
    if match_from(t, ss, i) {
        let q = choose|q: int| i <= q && #[trigger] sub_at(t, ss[0], q) && match_from(t, ss.drop_first(), q + ss[0].len());
        assert(q >= i2);
        assert(i2 <= q && sub_at(t, ss[0], q) && match_from(t, ss.drop_first(), q + ss[0].len()));
    }
    if match_from(t, ss, i2) {
        lemma_match_mono(t, ss, i, i2);
    }
}

/// The first segment occurs at `q`: matching from `q` is matching the rest after it (greedy step).
pub proof fn lemma_match_at(t: Seq<u8>, ss: Seq<Seq<u8>>, q: int)
    requires ss.len() > 0, sub_at(t, ss[0], q),
    ensures match_from(t, ss, q) == match_from(t, ss.drop_first(), q + ss[0].len()),
{
    if match_from(t, ss, q) {
        let q2 = choose|q2: int| q <= q2 && #[trigger] sub_at(t, ss[0], q2) && match_from(t, ss.drop_first(), q2 + ss[0].len());
        lemma_match_mono(t, ss.drop_first(), q + ss[0].len(), q2 + ss[0].len());
    }
}

/// No occurrence of the first segment at or after `i`: no match.
pub proof fn lemma_match_none(t: Seq<u8>, ss: Seq<Seq<u8>>, i: int)
    requires ss.len() > 0, forall|q: int| i <= q ==> !#[trigger] sub_at(t, ss[0], q),
    ensures !match_from(t, ss, i),
{
}

/// An occurrence inside the row `bytes[a..b)` in absolute positions is an occurrence in the row's value.
pub proof fn lemma_occ_row(bytes: Seq<u8>, lit: Seq<u8>, a: int, b: int, q: int)
    requires 0 <= a <= q, a <= b <= bytes.len(),
    ensures occ(bytes, lit, q, b) == sub_at(bytes.subrange(a, b), lit, q - a),
{
    let t = bytes.subrange(a, b);
    let j = q - a;
    if occ(bytes, lit, q, b) {
        assert(t.subrange(j, j + lit.len()) =~= lit) by {
            assert forall|k: int| 0 <= k < lit.len() implies t.subrange(j, j + lit.len())[k] == lit[k] by {
                assert(bytes[q + k] == lit[k]);
            }
        }
    }
    if sub_at(t, lit, j) {
        assert forall|k: int| 0 <= k < lit.len() implies #[trigger] bytes[q + k] == lit[k] by {
            assert(t.subrange(j, j + lit.len())[k] == lit[k]);
        }
    }
}

// ------------------------------------------------------------------------------------------------ the matcher

/// The executable segments: bytes, lengths and prefix patterns, one per segment, and their view.
pub struct Segs {
    pub bytes: Vec<Vec<u8>>,
    pub lens: Vec<usize>,
    pub pfs: Vec<Prefix>,
}

/// The executable segments hold `ss` (non-empty list of allowed segments).
pub open spec fn segs_view_ok(s: &Segs, ss: Seq<Seq<u8>>) -> bool {
    &&& ss.len() >= 1
    &&& segs_ok(ss)
    &&& s.bytes@.len() == ss.len() && s.lens@.len() == ss.len() && s.pfs@.len() == ss.len()
    &&& forall|k: int| #![trigger s.bytes@[k]] 0 <= k < ss.len() ==> {
        &&& s.bytes@[k]@ == ss[k]
        &&& s.lens@[k] as int == ss[k].len()
        &&& prefix_ok(s.pfs@[k], ss[k])
    }
}

/// Whether the segments occur in order in the row `bytes[a..to)`, the first at or after `from` (greedy: each
/// segment at its first occurrence after the previous one).
pub fn match_segments(bytes: &[u8], nbytes: usize, from: usize, to: usize, s: &Segs, Ghost(a): Ghost<int>,
    Ghost(ss): Ghost<Seq<Seq<u8>>>) -> (r: bool)
    requires 0 <= a <= from <= to <= nbytes, nbytes == bytes@.len(), segs_view_ok(s, ss),
    ensures r == match_from(bytes@.subrange(a, to as int), ss, from - a),
    no_unwind
{
    let ghost t = bytes@.subrange(a, to as int);
    let n = s.bytes.len();
    let mut k: usize = 0;
    let mut pos: usize = from;
    assert(ss.subrange(0, ss.len() as int) =~= ss);
    while k < n
        invariant
            0 <= a <= from <= pos <= to <= nbytes, nbytes == bytes@.len(), segs_view_ok(s, ss), n == ss.len(),
            k <= n, t == bytes@.subrange(a, to as int),
            match_from(t, ss, from - a) == match_from(t, ss.subrange(k as int, n as int), pos - a),
        decreases n - k,
    {
        let lit = &s.bytes[k];
        let m = s.lens[k];
        let ghost rest = ss.subrange(k as int, n as int);
        assert(rest[0] == ss[k as int]);
        assert(rest.drop_first() =~= ss.subrange(k + 1, n as int));
        assert(seg_ok(ss[k as int]));
        assert(s.lens@[k as int] as int == ss[k as int].len() && s.bytes@[k as int]@ == ss[k as int]);
        match find_first(bytes, nbytes, pos, to, lit, m, &s.pfs[k]) {
            Some(q) => {
                proof {
                    assert forall|q2: int| pos - a <= q2 < q - a implies !#[trigger] sub_at(t, rest[0], q2) by {
                        lemma_occ_row(bytes@, rest[0], a, to as int, q2 + a);
                        assert(!occ(bytes@, rest[0], q2 + a, to as int));
                    }
                    lemma_match_skip(t, rest, pos - a, q - a);
                    lemma_occ_row(bytes@, rest[0], a, to as int, q as int);
                    lemma_match_at(t, rest, q - a);
                }
                pos = q + m;
            },
            None => {
                proof {
                    assert forall|q2: int| pos - a <= q2 implies !#[trigger] sub_at(t, rest[0], q2) by {
                        if q2 + a < to {
                            lemma_occ_row(bytes@, rest[0], a, to as int, q2 + a);
                            assert(!occ(bytes@, rest[0], q2 + a, to as int));
                        }
                    }
                    lemma_match_none(t, rest, pos - a);
                }
                return false;
            },
        }
        k = k + 1;
    }
    proof {
        assert(ss.subrange(n as int, n as int).len() == 0);
    }
    true
}

// ------------------------------------------------------------------------------------------------ the pattern

/// Appending a segment appends it and a `%` to the tail pattern.
pub proof fn lemma_tail_push(ss: Seq<Seq<u8>>, s: Seq<u8>)
    ensures tail_pattern(ss.push(s)) == tail_pattern(ss) + s + seq![0x25u8],
    decreases ss.len(),
{
    if ss.len() == 0 {
        let e = Seq::<Seq<u8>>::empty();
        assert(ss.push(s).drop_first() =~= e);
        assert(tail_pattern(e) == Seq::<u8>::empty());
        assert(tail_pattern(ss) == Seq::<u8>::empty());
        assert(ss.push(s)[0] == s);
        assert(tail_pattern(ss.push(s)) == s + seq![0x25u8] + tail_pattern(e));
        assert(tail_pattern(ss.push(s)) =~= tail_pattern(ss) + s + seq![0x25u8]);
    } else {
        lemma_tail_push(ss.drop_first(), s);
        assert(ss.push(s).drop_first() =~= ss.drop_first().push(s));
        assert(ss.push(s)[0] == ss[0]);
        assert(tail_pattern(ss.push(s)) =~= tail_pattern(ss) + s + seq![0x25u8]);
    }
}

/// The parser's view: `segs_ok(ss)`, and every executable field agrees.
pub fn parse_segments(pat: &[u8]) -> (r: Option<(Segs, Ghost<Seq<Seq<u8>>>)>)
    ensures
        r matches Some((s, ss)) ==> segs_view_ok(&s, ss@) && seg_pattern(ss@) == pat@,
{
    let n = pat.len();
    if n < 3 || pat[0] != 0x25u8 || pat[n - 1] != 0x25u8 {
        return None;
    }
    let mut bytes: Vec<Vec<u8>> = Vec::new();
    let mut lens: Vec<usize> = Vec::new();
    let mut pfs: Vec<Prefix> = Vec::new();
    let ghost mut ss: Seq<Seq<u8>> = Seq::empty();
    let mut cur: Vec<u8> = Vec::new();
    let mut i: usize = 1;
    assert(pat@.subrange(0, 1) =~= seq![0x25u8] + tail_pattern(ss) + cur@);
    while i < n
        invariant
            1 <= i <= n, n == pat@.len(), n >= 3, pat@[0] == 0x25u8,
            pat@.subrange(0, i as int) == seq![0x25u8] + tail_pattern(ss) + cur@,
            segs_ok(ss),
            forall|t: int| 0 <= t < cur@.len() ==> #[trigger] seg_byte_ok(cur@[t]),
            bytes@.len() == ss.len() && lens@.len() == ss.len() && pfs@.len() == ss.len(),
            forall|k: int| #![trigger bytes@[k]] 0 <= k < ss.len() ==> {
                &&& bytes@[k]@ == ss[k]
                &&& lens@[k] as int == ss[k].len()
                &&& prefix_ok(pfs@[k], ss[k])
            },
            i == n ==> cur@.len() == 0,
        decreases n - i,
    {
        let c = pat[i];
        if c == 0x25u8 {
            if cur.len() == 0 {
                return None;
            }
            let m = cur.len();
            let pf = prefix_of(&cur, m);
            let ghost seg = cur@;
            let ghost (b0, l0, p0, ss0) = (bytes@, lens@, pfs@, ss);
            proof {
                lemma_tail_push(ss, seg);
                assert(pat@.subrange(0, i + 1) =~= pat@.subrange(0, i as int).push(0x25u8));
                assert(seq![0x25u8] + tail_pattern(ss.push(seg)) =~= (seq![0x25u8] + tail_pattern(ss) + seg).push(0x25u8));
                ss = ss.push(seg);
                assert(seg_ok(seg));
                assert forall|k: int| 0 <= k < ss.len() implies #[trigger] seg_ok(ss[k]) by {
                    if k < ss.len() - 1 { assert(ss[k] == ss.drop_last()[k]); }
                }
            }
            bytes.push(cur);
            lens.push(m);
            pfs.push(pf);
            cur = Vec::new();
            proof {
                assert(seq![0x25u8] + tail_pattern(ss) + cur@ =~= seq![0x25u8] + tail_pattern(ss));
                assert forall|k: int| #![trigger bytes@[k]] 0 <= k < ss.len() implies {
                    &&& bytes@[k]@ == ss[k]
                    &&& lens@[k] as int == ss[k].len()
                    &&& prefix_ok(pfs@[k], ss[k])
                } by {
                    if k < ss0.len() {
                        assert(bytes@[k] == b0[k] && lens@[k] == l0[k] && pfs@[k] == p0[k] && ss[k] == ss0[k]);
                    } else {
                        assert(bytes@[k]@ == seg && lens@[k] == m && pfs@[k] == pf && ss[k] == seg);
                    }
                }
            }
        } else {
            if !(c < 0x80u8 && c != 0x5Fu8 && c != 0x5Cu8) {
                return None;
            }
            if i == n - 1 {
                return None;
            }
            proof {
                assert(pat@.subrange(0, i + 1) =~= pat@.subrange(0, i as int).push(c));
            }
            let ghost (b0, l0, p0) = (bytes@, lens@, pfs@);
            cur.push(c);
            proof {
                assert(seq![0x25u8] + tail_pattern(ss) + cur@ =~= (seq![0x25u8] + tail_pattern(ss) + cur@.drop_last()).push(c));
                assert(bytes@ == b0 && lens@ == l0 && pfs@ == p0);
                assert forall|k: int| #![trigger bytes@[k]] 0 <= k < ss.len() implies {
                    &&& bytes@[k]@ == ss[k]
                    &&& lens@[k] as int == ss[k].len()
                    &&& prefix_ok(pfs@[k], ss[k])
                } by {
                    assert(b0[k]@ == ss[k]);
                }
            }
        }
        i = i + 1;
    }
    if bytes.len() == 0 {
        return None;
    }
    proof {
        assert(pat@.subrange(0, n as int) =~= pat@);
        assert(seq![0x25u8] + tail_pattern(ss) + cur@ =~= seg_pattern(ss));
    }
    Some((Segs { bytes, lens, pfs }, Ghost(ss)))
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

// ------------------------------------------------------------------------------------------------ tokens

/// The token of one pattern byte when the pattern has no escape character in it.
pub open spec fn tok_of(c: u8) -> LikeTok {
    if c == 0x25u8 { LikeTok::Any } else if c == 0x5Fu8 { LikeTok::One } else { LikeTok::Lit(seq![c]) }
}

/// The tokens of pattern bytes `p` (no escape character in them): one per byte.
pub open spec fn toks(p: Seq<u8>) -> Seq<LikeTok> {
    Seq::new(p.len(), |k: int| tok_of(p[k]))
}

/// Without the escape character, the tokens of the characters from `k` are one per byte.
proof fn lemma_tokens_plain(p: Seq<u8>, k: int)
    requires
        0 <= k <= p.len(),
        forall|i: int| 0 <= i < p.len() ==> #[trigger] p[i] < 0x80u8 && p[i] != 0x5Cu8,
    ensures like_tokens(Seq::new(p.len(), |i: int| seq![p[i]]), Some(seq![0x5Cu8]), k) == toks(p).subrange(k, p.len() as int),
    decreases p.len() - k,
{
    let pc = Seq::new(p.len(), |i: int| seq![p[i]]);
    if k < p.len() {
        lemma_tokens_plain(p, k + 1);
        assert(pc[k] != seq![0x5Cu8]) by {
            if pc[k] == seq![0x5Cu8] { assert(pc[k][0] == p[k]); }
        }
        if p[k] == 0x25u8 {
            assert(pc[k] == seq![0x25u8]);
            assert(pc[k] == pct());
        } else if p[k] == 0x5Fu8 {
            assert(pc[k] == underscore());
        } else {
            assert(pc[k] != pct()) by { if pc[k] == pct() { assert(pc[k][0] == p[k]); } }
            assert(pc[k] != underscore()) by { if pc[k] == underscore() { assert(pc[k][0] == p[k]); } }
        }
        assert(like_tokens(pc, Some(seq![0x5Cu8]), k) =~= toks(p).subrange(k, p.len() as int));
    } else {
        assert(like_tokens(pc, Some(seq![0x5Cu8]), k) =~= toks(p).subrange(k, p.len() as int));
    }
}

/// Standard matching reads only the tokens from `j` on.
pub proof fn lemma_std_suffix(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int, j: int)
    requires 0 <= j <= p.len(),
    ensures like_std(t, p, i, j) == like_std(t, p.subrange(j, p.len() as int), i, 0),
    decreases (t.len() - i) + (p.len() - j), 0int,
{
    let q = p.subrange(j, p.len() as int);
    if i < 0 || i > t.len() {
    } else if j >= p.len() {
    } else {
        assert(q[0] == p[j]);
        assert(q.subrange(1, q.len() as int) =~= p.subrange(j + 1, p.len() as int));
        match p[j] {
            LikeTok::Lit(c) => {
                if i < t.len() {
                    lemma_std_suffix(t, p, i + 1, j + 1);
                    lemma_std_suffix(t, q, i + 1, 1);
                }
            },
            LikeTok::One => {
                if i < t.len() {
                    lemma_std_suffix(t, p, i + 1, j + 1);
                    lemma_std_suffix(t, q, i + 1, 1);
                }
            },
            LikeTok::Any => {
                lemma_std_suffix(t, p, i, j + 1);
                lemma_std_suffix(t, q, i, 1);
                if i < t.len() {
                    lemma_std_suffix(t, p, i + 1, j);
                }
            },
            LikeTok::Dangling => {},
        }
    }
}

/// A literal run (the tokens of segment `s`) followed by `x`: the segment occurs at `i` and `x` matches after it.
proof fn lemma_std_lits(tb: Seq<u8>, s: Seq<u8>, x: Seq<LikeTok>, i: int)
    requires
        0 <= i <= tb.len(),
        forall|k: int| 0 <= k < s.len() ==> #[trigger] seg_byte_ok(s[k]),
    ensures
        like_std(Seq::new(tb.len(), |k: int| seq![tb[k]]), toks(s) + x, i, 0)
            == (sub_at(tb, s, i) && like_std(Seq::new(tb.len(), |k: int| seq![tb[k]]), x, i + s.len(), 0)),
    decreases s.len(),
{
    let t = Seq::new(tb.len(), |k: int| seq![tb[k]]);
    let p = toks(s) + x;
    if s.len() == 0 {
        assert(p =~= x);
        assert(tb.subrange(i, i) =~= s);
    } else {
        let s2 = s.drop_first();
        assert forall|k: int| 0 <= k < s2.len() implies #[trigger] seg_byte_ok(s2[k]) by { assert(s2[k] == s[k + 1]); }
        assert(p[0] == tok_of(s[0]));
        assert(seg_byte_ok(s[0]));
        assert(p[0] == LikeTok::Lit(seq![s[0]]));
        assert(p.subrange(1, p.len() as int) =~= toks(s2) + x);
        if i < tb.len() {
            lemma_std_suffix(t, p, i + 1, 1);
            lemma_std_lits(tb, s2, x, i + 1);
            assert((t[i] == seq![s[0]]) == (tb[i] == s[0])) by {
                if t[i] == seq![s[0]] { assert(t[i][0] == tb[i]); }
            }
            if sub_at(tb, s, i) {
                assert(tb.subrange(i, i + s.len())[0] == s[0]);
                assert(tb.subrange(i + 1, i + 1 + s2.len()) =~= tb.subrange(i, i + s.len()).drop_first());
            }
            if tb[i] == s[0] && sub_at(tb, s2, i + 1) {
                assert(tb.subrange(i, i + s.len()) =~= seq![s[0]] + tb.subrange(i + 1, i + 1 + s2.len()));
                assert(seq![s[0]] + s2 =~= s);
            }
        }
    }
}

/// The tokens of `%` followed by the tail pattern.
proof fn lemma_toks_any(ss: Seq<Seq<u8>>)
    ensures toks(seg_pattern(ss)) == seq![LikeTok::Any] + toks(tail_pattern(ss)),
{
    assert(toks(seg_pattern(ss)) =~= seq![LikeTok::Any] + toks(tail_pattern(ss)));
}

/// The tokens of the tail pattern: the first segment's literals, `%`, the rest.
proof fn lemma_toks_tail(ss: Seq<Seq<u8>>)
    requires ss.len() > 0,
    ensures toks(tail_pattern(ss)) == toks(ss[0]) + (seq![LikeTok::Any] + toks(tail_pattern(ss.drop_first()))),
{
    let a = ss[0];
    let b = tail_pattern(ss.drop_first());
    assert(tail_pattern(ss) == a + seq![0x25u8] + b);
    assert(toks(a + seq![0x25u8] + b) =~= toks(a) + (seq![LikeTok::Any] + toks(b)));
}

/// `%` then the segments: standard matching from text position `i` is matching the segments from byte `i`.
proof fn lemma_std_segments(tb: Seq<u8>, ss: Seq<Seq<u8>>, i: int)
    requires 0 <= i <= tb.len(), segs_ok(ss),
    ensures
        like_std(Seq::new(tb.len(), |k: int| seq![tb[k]]), seq![LikeTok::Any] + toks(tail_pattern(ss)), i, 0)
            == match_from(tb, ss, i),
    decreases ss.len(), tb.len() - i,
{
    let t = Seq::new(tb.len(), |k: int| seq![tb[k]]);
    let p = seq![LikeTok::Any] + toks(tail_pattern(ss));
    lemma_std_any(t, p, i, 0);
    assert(p.subrange(1, p.len() as int) =~= toks(tail_pattern(ss)));
    if ss.len() == 0 {
        assert(tail_pattern(ss) =~= Seq::<u8>::empty());
        assert(p.len() == 1);
        assert(like_std(t, p, t.len() as int, 1));
    } else {
        let s0 = ss[0];
        let rest = ss.drop_first();
        let x = seq![LikeTok::Any] + toks(tail_pattern(rest));
        assert(segs_ok(rest)) by {
            assert forall|k: int| 0 <= k < rest.len() implies #[trigger] seg_ok(rest[k]) by { assert(rest[k] == ss[k + 1]); }
        }
        assert(seg_ok(s0));
        lemma_toks_tail(ss);
        // std_from(t, p, i, 1): some k in [i, |t|] where the tail tokens match from k
        if match_from(tb, ss, i) {
            let q = choose|q: int| i <= q && #[trigger] sub_at(tb, s0, q) && match_from(tb, rest, q + s0.len());
            lemma_std_suffix(t, p, q, 1);
            lemma_std_lits(tb, s0, x, q);
            lemma_std_segments(tb, rest, q + s0.len());
            assert(like_std(t, p, q, 1));
            assert(i <= q <= t.len());
        }
        if std_from(t, p, i, 1) {
            let q = choose|q: int| i <= q <= t.len() && #[trigger] like_std(t, p, q, 1);
            lemma_std_suffix(t, p, q, 1);
            lemma_std_lits(tb, s0, x, q);
            if sub_at(tb, s0, q) {
                lemma_std_segments(tb, rest, q + s0.len());
                assert(sub_at(tb, ss[0], q) && match_from(tb, ss.drop_first(), q + ss[0].len()));
            }
        }
    }
}

/// `t LIKE '%s1%...%sk%'` on ASCII `t` with allowed segments: true exactly when the segments occur in order.
pub proof fn lemma_like_segments(t: Seq<u8>, ss: Seq<Seq<u8>>)
    requires ascii(t), segs_ok(ss),
    ensures like_of(t, seg_pattern(ss)) == Ok::<Val, SqlError>(Val::Bool(match_from(t, ss, 0))),
{
    let pat = seg_pattern(ss);
    let e = seq![0x5Cu8];
    // the escape string is one character
    assert(e.drop_last() =~= Seq::<u8>::empty());
    assert(chars(e.drop_last()) == Seq::<Seq<u8>>::empty());
    assert(!is_cont(e.last()));
    assert(chars(e) =~= seq![seq![0x5Cu8]]);
    assert(escape_of(chars(e)) == Some(seq![0x5Cu8]));
    // the pattern's bytes are ASCII without backslash
    assert forall|i: int| 0 <= i < pat.len() implies #[trigger] pat[i] < 0x80u8 && pat[i] != 0x5Cu8 && pat[i] != 0x5Fu8 by {
        lemma_pattern_bytes(ss, i);
    }
    assert(ascii(pat));
    lemma_chars_ascii(t);
    lemma_chars_ascii(pat);
    let tc = Seq::new(t.len(), |k: int| seq![t[k]]);
    let pc = Seq::new(pat.len(), |k: int| seq![pat[k]]);
    lemma_tokens_plain(pat, 0);
    assert(toks(pat).subrange(0, pat.len() as int) =~= toks(pat));
    let tk = toks(pat);
    assert(no_dangling(tk)) by {
        assert forall|k: int| 0 <= k < tk.len() implies !(#[trigger] tk[k] is Dangling) by {}
    }
    lemma_like_mt_std(tc, tk);
    lemma_toks_any(ss);
    lemma_std_segments(t, ss, 0);
}

/// Every byte of a segment pattern is ASCII, and none is `_` or backslash.
proof fn lemma_pattern_bytes(ss: Seq<Seq<u8>>, i: int)
    requires segs_ok(ss), 0 <= i < seg_pattern(ss).len(),
    ensures seg_pattern(ss)[i] < 0x80u8 && seg_pattern(ss)[i] != 0x5Cu8 && seg_pattern(ss)[i] != 0x5Fu8,
{
    if i > 0 {
        lemma_tail_bytes(ss, i - 1);
    }
}

/// Every byte of a tail pattern is ASCII, and none is `_` or backslash.
proof fn lemma_tail_bytes(ss: Seq<Seq<u8>>, i: int)
    requires segs_ok(ss), 0 <= i < tail_pattern(ss).len(),
    ensures tail_pattern(ss)[i] < 0x80u8 && tail_pattern(ss)[i] != 0x5Cu8 && tail_pattern(ss)[i] != 0x5Fu8,
    decreases ss.len(),
{
    if ss.len() > 0 {
        let a = ss[0];
        let rest = ss.drop_first();
        assert(seg_ok(a));
        assert(segs_ok(rest)) by {
            assert forall|k: int| 0 <= k < rest.len() implies #[trigger] seg_ok(rest[k]) by { assert(rest[k] == ss[k + 1]); }
        }
        let tp = tail_pattern(ss);
        assert(tp == a + seq![0x25u8] + tail_pattern(rest));
        if i < a.len() {
            assert(tp[i] == a[i]);
            assert(seg_byte_ok(a[i]));
        } else if i == a.len() {
            assert(tp[i] == 0x25u8);
        } else {
            assert(tp[i] == tail_pattern(rest)[i - a.len() - 1]);
            lemma_tail_bytes(rest, i - a.len() - 1);
        }
    }
}

} // verus!
