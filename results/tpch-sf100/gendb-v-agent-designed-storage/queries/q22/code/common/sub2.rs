//! `SUBSTRING(s FROM 1 FOR 2)` at the byte level: the bytes of `s` before the start of its third character
//! (`spec::chars`: a character is a non-continuation byte and the continuation bytes after it; a leading
//! continuation byte starts a character of its own), with an allocation-free `no_unwind` reader of that end.
//!
//! `sub2_end(b)` is the end of the second character: with `p1 = next_start(b, 1)` (start of the second character,
//! or `b.len()`), the start of the third character `next_start(b, p1 + 1)`, or `b.len()` when there is none.
//! `lemma_sub2` proves `char_range(chars(b), 1, substring_end(1, 2)) == b[0 .. sub2_end(b)]`; the proof splits the
//! characters at character starts (`lemma_chars_split`) and reads a lone character (`lemma_chars_one`).
use vstd::prelude::*;
use crate::spec::chars::*;
use crate::spec::fns::substring::{char_range, substring_end};

verus! {

/// The first position `p >= from` holding a non-continuation byte, or `b.len()`.
pub open spec fn next_start(b: Seq<u8>, from: int) -> int
    decreases b.len() - from,
{
    if from >= b.len() {
        b.len() as int
    } else if !is_cont(b[from]) {
        from
    } else {
        next_start(b, from + 1)
    }
}

/// End of the first two characters of `b` (exclusive byte position).
pub open spec fn sub2_end(b: Seq<u8>) -> int {
    if b.len() == 0 {
        0
    } else {
        let p1 = next_start(b, 1);
        if p1 >= b.len() { b.len() as int } else { next_start(b, p1 + 1) }
    }
}

/// `SUBSTRING(b FROM 1 FOR 2)` as bytes.
pub open spec fn sub2(b: Seq<u8>) -> Seq<u8> {
    b.subrange(0, sub2_end(b))
}

/// `next_start` lies in `[from, len]`, skips only continuation bytes, and stops at a non-continuation byte.
pub proof fn lemma_next_start(b: Seq<u8>, from: int)
    requires 0 <= from,
    ensures
        from <= next_start(b, from) || (from > b.len() && next_start(b, from) == b.len()),
        next_start(b, from) <= b.len(),
        forall|j: int| from <= j < next_start(b, from) ==> #[trigger] is_cont(b[j]),
        next_start(b, from) < b.len() ==> !is_cont(b[next_start(b, from)]),
    decreases b.len() - from,
{
    if from < b.len() && is_cont(b[from]) {
        lemma_next_start(b, from + 1);
    }
}

/// The characters of `b` split at a character start `k` (or at the end).
pub proof fn lemma_chars_split(b: Seq<u8>, k: int)
    requires
        0 <= k <= b.len(),
        k == b.len() || !is_cont(b[k]),
    ensures chars(b) == chars(b.subrange(0, k)) + chars(b.subrange(k, b.len() as int)),
    decreases b.len(),
{
    if b.len() == k {
        assert(b.subrange(0, k) =~= b);
        assert(b.subrange(k, b.len() as int) =~= Seq::<u8>::empty());
        assert(chars(Seq::<u8>::empty()) =~= Seq::<Seq<u8>>::empty());
        assert(chars(b) + Seq::<Seq<u8>>::empty() =~= chars(b));
    } else {
        let bi = b.drop_last();
        if k < bi.len() {
            assert(bi[k] == b[k]);
        }
        lemma_chars_split(bi, k);
        let a = chars(b.subrange(0, k));
        assert(bi.subrange(0, k) =~= b.subrange(0, k));
        let t = b.subrange(k, b.len() as int);
        let ti = bi.subrange(k, bi.len() as int);
        assert(t.drop_last() =~= ti);
        assert(t.last() == b.last());
        let cs = chars(bi);
        let ct = chars(ti);
        assert(cs == a + ct);
        if is_cont(b.last()) && cs.len() > 0 {
            // The last byte continues the last character; that character lies in the tail (the tail is not
            // empty: its first byte, `b[k]`, is not a continuation byte, and `b.last()` is).
            assert(ct.len() > 0) by {
                if ti.len() == 0 {
                    assert(b.len() == k + 1);
                    assert(b.last() == b[k]);
                }
                assert(ti.len() > 0);
                assert(ti.drop_last().push(ti.last()) =~= ti);
                lemma_chars_nonempty_len(ti);
            }
            assert(chars(t) == ct.drop_last().push(ct.last().push(b.last())));
            assert(cs.drop_last() =~= a + ct.drop_last());
            assert(cs.last() == ct.last());
            assert(chars(b) == cs.drop_last().push(cs.last().push(b.last())));
            assert(chars(b) =~= a + chars(t));
        } else {
            if is_cont(b.last()) {
                assert(cs.len() == 0);
                assert(ct.len() == 0);
            }
            assert(!(is_cont(t.last()) && ct.len() > 0)) by {
                if is_cont(t.last()) {
                    assert(cs.len() == 0);
                    assert(ct.len() == 0);
                }
            }
            assert(chars(t) == ct.push(seq![b.last()]));
            assert(chars(b) == cs.push(seq![b.last()]));
            assert(chars(b) =~= a + chars(t));
        }
    }
}

/// A non-empty text has at least one character.
pub proof fn lemma_chars_nonempty_len(b: Seq<u8>)
    requires b.len() > 0,
    ensures chars(b).len() > 0,
{
    let cs = chars(b.drop_last());
    if is_cont(b.last()) && cs.len() > 0 {
        assert(chars(b).len() == cs.len());
    } else {
        assert(chars(b).len() == cs.len() + 1);
    }
}

/// A first byte followed only by continuation bytes is one character.
pub proof fn lemma_chars_one(c: Seq<u8>)
    requires
        c.len() >= 1,
        forall|j: int| 1 <= j < c.len() ==> #[trigger] is_cont(c[j]),
    ensures chars(c) == seq![c],
    decreases c.len(),
{
    let ci = c.drop_last();
    if c.len() == 1 {
        assert(ci =~= Seq::<u8>::empty());
        assert(chars(ci) =~= Seq::<Seq<u8>>::empty());
        assert(seq![c.last()] =~= c);
        assert(chars(c) =~= seq![c]);
    } else {
        assert forall|j: int| 1 <= j < ci.len() implies #[trigger] is_cont(ci[j]) by {
            assert(ci[j] == c[j]);
        }
        lemma_chars_one(ci);
        assert(is_cont(c[c.len() - 1]));
        assert(ci.push(c.last()) =~= c);
        assert(chars(c) =~= seq![c]);
    }
}

/// Two-character concatenation.
proof fn lemma_concat_two(x: Seq<u8>, y: Seq<u8>)
    ensures concat(seq![x, y]) == x + y,
{
    let s = seq![x, y];
    assert(s.drop_last() =~= seq![x]);
    lemma_concat_one(x);
    assert(s.last() == y);
}

/// One-character concatenation.
proof fn lemma_concat_one(x: Seq<u8>)
    ensures concat(seq![x]) == x,
{
    let e = Seq::<Seq<u8>>::empty();
    assert(seq![x].drop_last() =~= e);
    assert(concat(e) == Seq::<u8>::empty());
    assert(concat(seq![x]) == concat(e) + x);
    assert(Seq::<u8>::empty() + x =~= x);
}

/// `SUBSTRING(b FROM 1 FOR 2)` is the byte prefix `b[0 .. sub2_end(b)]`.
pub proof fn lemma_sub2(b: Seq<u8>)
    ensures
        0 <= sub2_end(b) <= b.len(),
        char_range(chars(b), 1, substring_end(1, 2)) == sub2(b),
{
    let n = b.len() as int;
    assert(substring_end(1, 2) == Some(3int));
    if n == 0 {
        assert(chars(b) =~= Seq::<Seq<u8>>::empty());
        assert(chars(b).subrange(0, 0) =~= Seq::<Seq<u8>>::empty());
        assert(sub2(b) =~= Seq::<u8>::empty());
    } else {
        lemma_next_start(b, 1);
        let p1 = next_start(b, 1);
        lemma_chars_split(b, p1);
        let first = b.subrange(0, p1);
        assert forall|j: int| 1 <= j < first.len() implies #[trigger] is_cont(first[j]) by {
            assert(first[j] == b[j]);
        }
        lemma_chars_one(first);
        let rest = b.subrange(p1, n);
        if p1 >= n {
            assert(rest =~= Seq::<u8>::empty());
            assert(chars(rest) =~= Seq::<Seq<u8>>::empty());
            assert(chars(b) =~= seq![first]);
            assert(first =~= b);
            assert(chars(b).subrange(0, 1) =~= seq![b]);
            lemma_concat_one(b);
            assert(sub2(b) =~= b);
        } else {
            lemma_next_start(b, p1 + 1);
            let p2 = next_start(b, p1 + 1);
            let k = p2 - p1;
            if p2 < n {
                assert(rest[k] == b[p2]);
            }
            lemma_chars_split(rest, k);
            let second = rest.subrange(0, k);
            assert(second =~= b.subrange(p1, p2));
            assert forall|j: int| 1 <= j < second.len() implies #[trigger] is_cont(second[j]) by {
                assert(second[j] == b[p1 + j]);
            }
            lemma_chars_one(second);
            let tail = chars(rest.subrange(k, rest.len() as int));
            assert(chars(b) =~= seq![first, second] + tail);
            assert(chars(b).subrange(0, 2) =~= seq![first, second]);
            lemma_concat_two(first, second);
            assert(first + second =~= b.subrange(0, p2));
        }
    }
}

/// Whether byte `x` is a UTF-8 continuation byte.
pub fn is_cont_exec(x: u8) -> (r: bool)
    ensures r == is_cont(x),
    no_unwind
{
    0x80u8 <= x && x < 0xC0u8
}

/// `sub2_end` of the text `bytes[s .. e]`, relative to `s`.
pub fn sub2_end_exec(bytes: &[u8], s: usize, e: usize) -> (r: usize)
    requires s <= e <= bytes@.len(),
    ensures r == sub2_end(bytes@.subrange(s as int, e as int)),
    no_unwind
{
    let ghost b = bytes@.subrange(s as int, e as int);
    let n = e - s;
    if n == 0 {
        return 0;
    }
    let mut p1: usize = 1;
    while p1 < n && is_cont_exec(bytes[s + p1])
        invariant
            1 <= p1 <= n,
            n == b.len(),
            s + n == e,
            e <= bytes@.len(),
            s + n <= bytes@.len(),
            b == bytes@.subrange(s as int, e as int),
            next_start(b, p1 as int) == next_start(b, 1),
        decreases n - p1,
    {
        assert(b[p1 as int] == bytes@[s + p1]);
        p1 = p1 + 1;
    }
    proof {
        if p1 < n {
            assert(b[p1 as int] == bytes@[s + p1]);
        }
    }
    if p1 >= n {
        return n;
    }
    let mut p2: usize = p1 + 1;
    while p2 < n && is_cont_exec(bytes[s + p2])
        invariant
            p1 < p2 <= n,
            n == b.len(),
            s + n == e,
            e <= bytes@.len(),
            s + n <= bytes@.len(),
            b == bytes@.subrange(s as int, e as int),
            next_start(b, p2 as int) == next_start(b, p1 + 1),
            p1 == next_start(b, 1),
        decreases n - p2,
    {
        assert(b[p2 as int] == bytes@[s + p2]);
        p2 = p2 + 1;
    }
    proof {
        if p2 < n {
            assert(b[p2 as int] == bytes@[s + p2]);
        }
    }
    p2
}

} // verus!
