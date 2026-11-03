//! Byte equality of one value of a stored text column (offsets and bytes parts) with a byte string.
use vstd::prelude::*;
use crate::link::query::{text_at, text_wf, TextView};

verus! {

/// The text column of the offsets `offs` and bytes `bytes`.
pub open spec fn tview(offs: Seq<i64>, bytes: Seq<u8>) -> TextView {
    TextView { offsets: offs, bytes }
}

/// Value `i` of the column (`n` rows, `nb` bytes) equals `pat` (`plen` bytes), byte for byte.
pub fn text_eq_at(offs: &[i64], bytes: &[u8], nb: usize, i: usize, pat: &[u8], plen: usize, Ghost(n): Ghost<int>) -> (b: bool)
    requires
        text_wf(tview(offs@, bytes@), n),
        i < n,
        nb == bytes@.len(),
        plen == pat@.len(),
    ensures b == (text_at(tview(offs@, bytes@), i as int) == pat@),
    no_unwind
{
    let ghost t = tview(offs@, bytes@);
    assert(0 <= t.offsets[i as int] <= t.offsets[i + 1] <= t.bytes.len());
    let a = offs[i] as usize;
    let e = offs[i + 1] as usize;
    if e - a != plen {
        assert(text_at(t, i as int).len() != pat@.len());
        return false;
    }
    let mut k: usize = 0;
    while k < plen
        invariant
            k <= plen, plen == pat@.len(), a + plen == e, e <= nb, nb == bytes@.len(),
            a == t.offsets[i as int], e == t.offsets[i + 1], t == tview(offs@, bytes@),
            text_at(t, i as int) == bytes@.subrange(a as int, e as int),
            forall|x: int| 0 <= x < k ==> bytes@[a + x] == pat@[x],
        decreases plen - k,
    {
        if bytes[a + k] != pat[k] {
            assert(text_at(t, i as int)[k as int] == bytes@[a + k]);
            return false;
        }
        k = k + 1;
    }
    assert(text_at(t, i as int) =~= pat@);
    true
}

} // verus!
