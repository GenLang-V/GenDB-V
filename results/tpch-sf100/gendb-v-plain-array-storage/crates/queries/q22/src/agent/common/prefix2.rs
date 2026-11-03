//! `SUBSTRING(s FROM 1 FOR 2)` (the first two characters of a text) on texts that start with two ASCII bytes:
//! when the byte after them is absent or starts a character, the result is exactly those two bytes
//! (`lemma_prefix2_ascii`). The character segmentation `spec::chars::chars` splits at every character start
//! (`lemma_chars_split`).
use vstd::prelude::*;
use crate::spec::chars::*;
use crate::spec::fns::substring::*;

verus! {

/// The value of `SUBSTRING(b FROM 1 FOR 2)` on a non-NULL text `b` (`spec::fns::substring::substring_value`).
/// Opaque: callers reveal it only where the character segmentation is needed.
#[verifier::opaque]
pub open spec fn prefix2(b: Seq<u8>) -> Seq<u8> {
    char_range(chars(b), 1, substring_end(1, 2))
}

/// A non-empty text has a character.
pub proof fn lemma_chars_nonempty_len(b: Seq<u8>)
    requires b.len() > 0,
    ensures chars(b).len() > 0,
{
}

/// Position `k` starts a character of `b` (or is its end): the characters of `b` are those of `b[..k]` followed
/// by those of `b[k..]`.
pub proof fn lemma_chars_split(b: Seq<u8>, k: int)
    requires 0 < k <= b.len(), k == b.len() || !is_cont(b[k]),
    ensures chars(b) == chars(b.subrange(0, k)) + chars(b.subrange(k, b.len() as int)),
    decreases b.len() - k,
{
    let n = b.len() as int;
    if k == n {
        assert(b.subrange(0, k) =~= b);
        assert(b.subrange(k, n) =~= Seq::<u8>::empty());
        assert(chars(b.subrange(k, n)) =~= Seq::<Seq<u8>>::empty());
        assert(chars(b) + Seq::<Seq<u8>>::empty() =~= chars(b));
    } else {
        let bd = b.drop_last();
        let x = b.last();
        if k < n - 1 {
            assert(bd[k] == b[k]);
        }
        lemma_chars_split(bd, k);
        let a = chars(b.subrange(0, k));
        let tail = b.subrange(k, n);
        let tail_d = bd.subrange(k, n - 1);
        assert(bd.subrange(0, k) =~= b.subrange(0, k));
        assert(tail.drop_last() =~= tail_d);
        assert(tail.last() == x);
        let bb = chars(tail_d);
        assert(chars(bd) == a + bb);
        // one step of `chars` on `b` and on its tail
        assert(chars(b) == if is_cont(x) && chars(bd).len() > 0 {
            chars(bd).drop_last().push(chars(bd).last().push(x))
        } else {
            chars(bd).push(seq![x])
        });
        assert(chars(tail) == if is_cont(x) && bb.len() > 0 {
            bb.drop_last().push(bb.last().push(x))
        } else {
            bb.push(seq![x])
        });
        if bb.len() == 0 {
            // the tail before `x` is empty: `x` is `b[k]`, a character start
            if tail_d.len() > 0 {
                lemma_chars_nonempty_len(tail_d);
            }
            assert(k == n - 1);
            assert(x == b[k]);
            assert(!is_cont(x));
            assert(chars(b) == (a + bb).push(seq![x]));
            assert((a + bb).push(seq![x]) =~= a + bb.push(seq![x]));
        } else if is_cont(x) {
            assert((a + bb).drop_last().push((a + bb).last().push(x)) =~= a + bb.drop_last().push(bb.last().push(x)));
        } else {
            assert((a + bb).push(seq![x]) =~= a + bb.push(seq![x]));
        }
    }
}

/// Two ASCII bytes are two one-byte characters.
pub proof fn lemma_chars_two_ascii(b0: u8, b1: u8)
    requires b0 < 0x80, b1 < 0x80,
    ensures chars(seq![b0, b1]) == seq![seq![b0], seq![b1]],
{
    let s = seq![b0, b1];
    let s0 = s.drop_last();
    assert(s0 =~= seq![b0]);
    let e = Seq::<u8>::empty();
    assert(seq![b0].drop_last() =~= e);
    assert(chars(e).len() == 0);
    assert(seq![b0].last() == b0);
    assert(chars(seq![b0]) == chars(e).push(seq![b0]));
    assert(chars(seq![b0]) =~= seq![seq![b0]]);
    assert(!is_cont(b1));
    assert(s.last() == b1);
    assert(chars(s) =~= seq![seq![b0], seq![b1]]);
}

/// The first two characters of a text starting with two ASCII bytes, followed by the end or a character start,
/// are those two bytes.
pub proof fn lemma_prefix2_ascii(b: Seq<u8>)
    requires
        b.len() >= 2,
        b[0] < 0x80,
        b[1] < 0x80,
        b.len() == 2 || !is_cont(b[2]),
    ensures prefix2(b) == b.subrange(0, 2),
{
    reveal(prefix2);
    let n = b.len() as int;
    lemma_chars_split(b, 2);
    let head = b.subrange(0, 2);
    assert(head =~= seq![b[0], b[1]]);
    lemma_chars_two_ascii(b[0], b[1]);
    let cs = chars(b);
    let hc = seq![seq![b[0]], seq![b[1]]];
    assert(cs == hc + chars(b.subrange(2, n)));
    assert(cs.len() >= 2);
    assert(substring_end(1, 2) == Some(3int)) by {
        assert(crate::spec::limits::int4_max() == 2147483647);
    }
    assert(cs.subrange(0, 2) =~= hc);
    assert(hc.drop_last() =~= seq![seq![b[0]]]);
    let ce = Seq::<Seq<u8>>::empty();
    assert(seq![seq![b[0]]].drop_last() =~= ce);
    assert(concat(ce).len() == 0);
    assert(concat(seq![seq![b[0]]]) == concat(ce) + seq![b[0]]);
    assert(concat(seq![seq![b[0]]]) =~= seq![b[0]]);
    assert(concat(hc) =~= seq![b[0], b[1]]);
}

} // verus!
