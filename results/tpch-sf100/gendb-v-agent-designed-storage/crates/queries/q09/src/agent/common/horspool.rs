//! Byte substring search with the Horspool skip: the word `w = pat[wl .. wl + wn]` occurs in `y[a .. e]` exactly when
//! `find_horspool` says so. At each alignment the byte under the word's last position decides the skip
//! (`shift_ok`: no byte of `w[0 .. wn - 1]` after position `wn - 1 - sh[b]` equals `b`), so the skipped alignments
//! cannot match; `shift_table` builds the table of a word of at most 255 bytes.
use vstd::prelude::*;
use super::like_word::{occurs_at, contains};

verus! {

/// The skip of byte `b` is between 1 and `wn`, and `b` does not occur in `w` strictly between position
/// `wn - 1 - sh[b]` and the last position.
pub open spec fn shift_ok(sh: Seq<u8>, w: Seq<u8>) -> bool {
    &&& sh.len() == 256
    &&& forall|b: int| 0 <= b < 256 ==> 1 <= #[trigger] sh[b] <= w.len()
    &&& forall|b: int, i: int| #![trigger w[i], sh[b]] 0 <= b < 256 && w.len() - 1 - sh[b] < i < w.len() - 1 ==> w[i] != b as u8
}

/// The skip table of the word `pat[wl .. wl + wn]` (`1 <= wn <= 255`).
pub fn shift_table(pat: &[u8], wl: usize, wn: usize) -> (sh: Vec<u8>)
    requires 1 <= wn <= 255, wl + wn <= pat@.len() <= usize::MAX,
    ensures shift_ok(sh@, pat@.subrange(wl as int, wl + wn)),
{
    let ghost w = pat@.subrange(wl as int, wl + wn);
    let mut sh: Vec<u8> = vec![wn as u8; 256];
    proof {
        assert forall|b: int| 0 <= b < 256 implies #[trigger] sh@[b] == wn as u8 by {
            assert(vstd::pervasive::cloned(wn as u8, sh@[b]));
        }
    }
    let mut idx: usize = 0;
    while idx + 1 < wn
        invariant
            1 <= wn <= 255, wl + wn <= pat@.len() <= usize::MAX, w == pat@.subrange(wl as int, wl + wn),
            sh@.len() == 256, idx < wn,
            forall|b: int| 0 <= b < 256 ==> 1 <= #[trigger] sh@[b] <= wn,
            forall|b: int, i: int| #![trigger w[i], sh@[b]] 0 <= b < 256 && wn - 1 - sh@[b] < i < idx ==> w[i] != b as u8,
        decreases wn - idx,
    {
        let c = pat[wl + idx];
        let ghost s0 = sh@;
        sh.set(c as usize, (wn - 1 - idx) as u8);
        proof {
            assert(w[idx as int] == c);
            assert forall|b: int, i: int| #![trigger w[i], sh@[b]] 0 <= b < 256 && wn - 1 - sh@[b] < i < idx + 1 implies w[i] != b as u8 by {
                if b == c as int {
                    assert(sh@[b] == wn - 1 - idx);
                } else {
                    assert(sh@[b] == s0[b]);
                    if i == idx {
                        assert(w[i] == c);
                        assert(c != b as u8);
                    }
                }
            }
        }
        idx = idx + 1;
    }
    sh
}

/// No alignment between `i + 1` and `i + sh[b] - 1` matches when the byte under the word's last position at
/// alignment `i` is `b`.
proof fn lemma_skip(s: Seq<u8>, w: Seq<u8>, sh: Seq<u8>, i: int, x: int)
    requires
        shift_ok(sh, w), w.len() >= 1,
        0 <= i, i + w.len() <= s.len(),
        i < x < i + sh[s[i + w.len() - 1] as int],
    ensures !occurs_at(s, w, x),
{
    let b = s[i + w.len() - 1];
    let k = i + w.len() - 1 - x;
    if occurs_at(s, w, x) {
        assert(0 <= k < w.len() - 1);
        assert(s.subrange(x, x + w.len())[k] == w[k]);
        assert(s[x + k] == w[k]);
        assert(w.len() - 1 - sh[b as int] < k);
        assert(w[k] != b);
    }
}

/// Does `y[a .. e]` contain `w = pat[wl .. wl + wn]`? (Horspool skips over the alignments)
pub fn find_horspool(y: &[u8], a: usize, e: usize, pat: &[u8], wl: usize, wn: usize, sh: &Vec<u8>) -> (r: bool)
    requires
        a <= e <= y@.len(),
        wl + wn <= pat@.len() <= usize::MAX,
        wn >= 1,
        shift_ok(sh@, pat@.subrange(wl as int, wl + wn)),
    ensures r == contains(y@.subrange(a as int, e as int), pat@.subrange(wl as int, wl + wn)),
    no_unwind
{
    let ghost s = y@.subrange(a as int, e as int);
    let ghost w = pat@.subrange(wl as int, wl + wn);
    if e - a < wn {
        proof {
            assert forall|x: int| !#[trigger] occurs_at(s, w, x) by {}
        }
        return false;
    }
    let last = e - wn;
    let wlast = pat[wl + wn - 1];
    let mut i = a;
    while i <= last
        invariant
            a <= i, last + wn == e, e <= y@.len(),
            wl + wn <= pat@.len() <= usize::MAX,
            wn >= 1,
            s == y@.subrange(a as int, e as int),
            w == pat@.subrange(wl as int, wl + wn),
            wlast == pat@[wl + wn - 1],
            shift_ok(sh@, w),
            forall|x: int| 0 <= x < i - a ==> !#[trigger] occurs_at(s, w, x),
        decreases e - i,
    {
        let cend = y[i + wn - 1];
        if cend == wlast {
            let mut k: usize = 0;
            while k + 1 < wn && y[i + k] == pat[wl + k]
                invariant
                    a <= i <= last, last + wn == e, e <= y@.len(),
                    wl + wn <= pat@.len() <= usize::MAX,
                    k < wn,
                    forall|x: int| 0 <= x < k ==> #[trigger] y@[i + x] == pat@[wl + x],
                decreases wn - k,
            {
                k = k + 1;
            }
            if k + 1 == wn {
                proof {
                    assert(s.subrange(i - a, i - a + wn) =~= w) by {
                        assert forall|x: int| 0 <= x < wn implies s.subrange(i - a, i - a + wn)[x] == w[x] by {
                            if x < k { assert(y@[i + x] == pat@[wl + x]); }
                        }
                    }
                    assert(occurs_at(s, w, i - a));
                }
                return true;
            } else {
                proof {
                    assert(!occurs_at(s, w, i - a)) by {
                        if occurs_at(s, w, i - a) {
                            assert(s.subrange(i - a, i - a + wn)[k as int] == w[k as int]);
                        }
                    }
                }
            }
        } else {
            proof {
                assert(!occurs_at(s, w, i - a)) by {
                    if occurs_at(s, w, i - a) {
                        assert(s.subrange(i - a, i - a + wn)[wn - 1] == w[wn - 1]);
                    }
                }
            }
        }
        let step = sh[cend as usize] as usize;
        proof {
            assert(s[i - a + wn - 1] == cend);
            assert forall|x: int| 0 <= x < i - a + step implies !#[trigger] occurs_at(s, w, x) by {
                if x > i - a {
                    lemma_skip(s, w, sh@, i - a, x);
                }
            }
        }
        i = i + step;
    }
    proof {
        assert forall|x: int| !#[trigger] occurs_at(s, w, x) by {
            if occurs_at(s, w, x) {
                assert(x < i - a);
            }
        }
    }
    false
}

} // verus!
