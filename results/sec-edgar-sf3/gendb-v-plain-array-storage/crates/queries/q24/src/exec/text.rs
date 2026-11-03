//! Executable text comparison (`spec::text`): byte-wise order, PostgreSQL's `C` collation.
use vstd::prelude::*;
use crate::spec::text::*;

verus! {

/// `spec::text::lex_cmp`: `-1`, `0` or `1` by the first differing byte, a proper prefix ordering first.
pub fn lex_cmp_exec(a: &Vec<u8>, b: &Vec<u8>) -> (r: i8)
    ensures r as int == lex_cmp(a@, b@),
{
    let mut i: usize = 0;
    assert(a@.subrange(0, a@.len() as int) =~= a@);
    assert(b@.subrange(0, b@.len() as int) =~= b@);
    while i < a.len() && i < b.len()
        invariant
            i <= a.len(),
            i <= b.len(),
            lex_cmp(a@.subrange(i as int, a@.len() as int), b@.subrange(i as int, b@.len() as int)) == lex_cmp(a@, b@),
        decreases a.len() - i,
    {
        let ghost sa = a@.subrange(i as int, a@.len() as int);
        let ghost sb = b@.subrange(i as int, b@.len() as int);
        if a[i] < b[i] {
            return -1;
        } else if a[i] > b[i] {
            return 1;
        }
        assert(sa.drop_first() =~= a@.subrange(i + 1, a@.len() as int));
        assert(sb.drop_first() =~= b@.subrange(i + 1, b@.len() as int));
        i = i + 1;
    }
    if i < a.len() { 1 } else if i < b.len() { -1 } else { 0 }
}

} // verus!
