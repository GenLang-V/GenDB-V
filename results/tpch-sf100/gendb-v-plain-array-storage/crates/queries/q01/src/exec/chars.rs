//! Executable `spec::chars`: UTF-8 character segmentation, concatenation of a character range and byte-string
//! equality. Never `Capacity`.
use vstd::prelude::*;
use crate::spec::chars::*;

verus! {

/// The spec view of executable characters.
pub open spec fn view_chars(cs: Seq<Vec<u8>>) -> Seq<Seq<u8>> {
    cs.map_values(|c: Vec<u8>| c@)
}

/// `spec::chars::chars`: the characters of `b` (a continuation byte `0x80..0xC0` extends the previous
/// character; any other byte, or a leading continuation byte,
/// starts a new one).
pub fn chars_exec(b: &Vec<u8>) -> (r: Vec<Vec<u8>>)
    ensures view_chars(r@) == chars(b@),
{
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 0;
    assert(b@.take(0) =~= Seq::<u8>::empty());
    assert(view_chars(out@) =~= Seq::<Seq<u8>>::empty());
    while i < b.len()
        invariant
            i <= b.len(),
            view_chars(out@) == chars(b@.take(i as int)),
        decreases b.len() - i,
    {
        let x = b[i];
        let ghost pre = b@.take(i as int);
        let ghost cur = b@.take(i as int + 1);
        assert(cur.drop_last() =~= pre);
        assert(cur.last() == x);
        let ghost cs = chars(pre);
        if 0x80u8 <= x && x < 0xC0u8 && out.len() > 0 {
            let ghost old_out = out@;
            match out.pop() {
                Some(mut last) => {
                    let ghost lastv = last@;
                    last.push(x);
                    out.push(last);
                    proof {
                        assert(old_out.drop_last() == out@.drop_last());
                        assert(view_chars(out@) =~= cs.drop_last().push(cs.last().push(x))) by {
                            assert(view_chars(old_out)[old_out.len() - 1] == lastv);
                            assert forall|k: int| 0 <= k < out@.len() implies
                                #[trigger] view_chars(out@)[k] == cs.drop_last().push(cs.last().push(x))[k] by {
                                if k < out@.len() - 1 {
                                    assert(out@[k] == old_out[k]);
                                }
                            }
                        }
                    }
                },
                None => {},
            }
        } else {
            let mut c: Vec<u8> = Vec::new();
            c.push(x);
            let ghost old_out = out@;
            out.push(c);
            proof {
                assert(c@ =~= seq![x]);
                assert(view_chars(out@) =~= cs.push(seq![x])) by {
                    assert forall|k: int| 0 <= k < out@.len() implies
                        #[trigger] view_chars(out@)[k] == cs.push(seq![x])[k] by {
                        if k < old_out.len() {
                            assert(out@[k] == old_out[k]);
                        }
                    }
                }
            }
        }
        i = i + 1;
    }
    assert(b@.take(b.len() as int) =~= b@);
    out
}

/// `spec::chars::concat(cs[lo..hi])`: the bytes of the characters `lo..hi`.
pub fn concat_range_exec(cs: &Vec<Vec<u8>>, lo: usize, hi: usize) -> (r: Vec<u8>)
    requires lo <= hi <= cs.len(),
    ensures r@ == concat(view_chars(cs@).subrange(lo as int, hi as int)),
{
    let mut out: Vec<u8> = Vec::new();
    let mut k: usize = lo;
    assert(view_chars(cs@).subrange(lo as int, lo as int) =~= Seq::<Seq<u8>>::empty());
    while k < hi
        invariant
            lo <= k <= hi <= cs.len(),
            out@ == concat(view_chars(cs@).subrange(lo as int, k as int)),
        decreases hi - k,
    {
        let c = &cs[k];
        let ghost before = out@;
        let mut m: usize = 0;
        while m < c.len()
            invariant
                m <= c.len(),
                out@ == before + c@.take(m as int),
            decreases c.len() - m,
        {
            out.push(c[m]);
            proof {
                assert(c@.take(m as int + 1) =~= c@.take(m as int).push(c@[m as int]));
                assert(out@ =~= before + c@.take(m as int + 1));
            }
            m = m + 1;
        }
        proof {
            assert(c@.take(c@.len() as int) =~= c@);
            let s = view_chars(cs@).subrange(lo as int, k as int + 1);
            assert(s.drop_last() =~= view_chars(cs@).subrange(lo as int, k as int));
            assert(s.last() == c@);
        }
        k = k + 1;
    }
    out
}

/// Byte-string equality.
pub fn bytes_eq(a: &Vec<u8>, b: &Vec<u8>) -> (r: bool)
    ensures r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            a@.take(i as int) == b@.take(i as int),
        decreases a.len() - i,
    {
        if a[i] != b[i] {
            assert(a@[i as int] != b@[i as int]);
            return false;
        }
        assert(a@.take(i as int + 1) =~= a@.take(i as int).push(a@[i as int]));
        assert(b@.take(i as int + 1) =~= b@.take(i as int).push(b@[i as int]));
        i = i + 1;
    }
    assert(a@.take(a.len() as int) =~= a@);
    assert(b@.take(b.len() as int) =~= b@);
    true
}

} // verus!
