//! Characters of text values (used by LIKE, SUBSTRING and char(n) padding).
//!
//! Text values are bytes. A character is a byte that is not a UTF-8 continuation byte (`10xxxxxx`) followed by
//! the continuation bytes after it. On well-formed UTF-8 (the decoder premise for stored text, deviation D4 of
//! the VERUS_SQL_COVERAGE design, and true of every literal the frontend emits) this is the code-point
//! segmentation PostgreSQL's UTF-8 routines use (`pg_utf_mblen` of the lead byte), and the number of characters
//! is `spec::typing::utf8_chars`. The definition is total on every byte sequence (a leading continuation byte
//! starts a character of its own), so no premise is needed for the semantics to be defined.
use vstd::prelude::*;

verus! {

/// A UTF-8 continuation byte (`10xxxxxx`).
pub open spec fn is_cont(b: u8) -> bool {
    0x80u8 <= b && b < 0xC0u8
}

/// The characters of `b`, in order.
pub open spec fn chars(b: Seq<u8>) -> Seq<Seq<u8>>
    decreases b.len(),
{
    if b.len() == 0 {
        Seq::empty()
    } else {
        let cs = chars(b.drop_last());
        if is_cont(b.last()) && cs.len() > 0 {
            cs.drop_last().push(cs.last().push(b.last()))
        } else {
            cs.push(seq![b.last()])
        }
    }
}

/// Concatenation of characters (the text they spell).
pub open spec fn concat(cs: Seq<Seq<u8>>) -> Seq<u8>
    decreases cs.len(),
{
    if cs.len() == 0 { Seq::empty() } else { concat(cs.drop_last()) + cs.last() }
}

/// The characters of `b` spell `b`.
pub proof fn lemma_concat_chars(b: Seq<u8>)
    ensures concat(chars(b)) == b,
    decreases b.len(),
{
    if b.len() > 0 {
        let cs = chars(b.drop_last());
        lemma_concat_chars(b.drop_last());
        if is_cont(b.last()) && cs.len() > 0 {
            let r = cs.drop_last().push(cs.last().push(b.last()));
            assert(r.drop_last() =~= cs.drop_last());
            assert(cs.drop_last().push(cs.last()) =~= cs);
            assert(concat(cs) == concat(cs.drop_last()) + cs.last());
            assert(concat(r) =~= concat(cs) + seq![b.last()]);
        } else {
            let r = cs.push(seq![b.last()]);
            assert(r.drop_last() =~= cs);
        }
        assert(b.drop_last().push(b.last()) =~= b);
    }
}

/// Every character is non-empty.
pub proof fn lemma_chars_nonempty(b: Seq<u8>)
    ensures forall|k: int| 0 <= k < chars(b).len() ==> #[trigger] chars(b)[k].len() > 0,
    decreases b.len(),
{
    if b.len() > 0 {
        let cs = chars(b.drop_last());
        lemma_chars_nonempty(b.drop_last());
        if is_cont(b.last()) && cs.len() > 0 {
            let r = cs.drop_last().push(cs.last().push(b.last()));
            assert forall|k: int| 0 <= k < r.len() implies #[trigger] r[k].len() > 0 by {
                if k < r.len() - 1 { assert(r[k] == cs[k]); }
            }
        } else {
            let r = cs.push(seq![b.last()]);
            assert forall|k: int| 0 <= k < r.len() implies #[trigger] r[k].len() > 0 by {
                if k < r.len() - 1 { assert(r[k] == cs[k]); }
            }
        }
    }
}

} // verus!
