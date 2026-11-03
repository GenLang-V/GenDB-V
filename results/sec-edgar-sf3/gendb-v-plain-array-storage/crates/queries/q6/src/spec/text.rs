//! Text semantics: byte strings in `C` collation (for UTF-8, byte order is code-point order).
use vstd::prelude::*;

verus! {

/// Lexicographic byte comparison: -1, 0 or 1.
pub open spec fn lex_cmp(a: Seq<u8>, b: Seq<u8>) -> int
    decreases a.len(),
{
    if a.len() == 0 {
        if b.len() == 0 { 0 } else { -1 }
    } else if b.len() == 0 {
        1
    } else if a[0] < b[0] {
        -1
    } else if a[0] > b[0] {
        1
    } else {
        lex_cmp(a.drop_first(), b.drop_first())
    }
}

} // verus!
