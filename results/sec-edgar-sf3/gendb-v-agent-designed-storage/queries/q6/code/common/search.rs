//! Searches over sorted data (no allocation, `no_unwind`, usable in worker bodies): the lower bound of a key in a
//! nondecreasing `u64` slice, plainly or galloping forward from a start position known to be below the key; and the
//! lower bound of a byte string among strictly increasing dictionary values (`text_entry` of a text list), directly
//! by position or through a list of dictionary codes, galloping forward from a start position.
use vstd::prelude::*;
use crate::spec::text::lex_cmp;
use crate::stores::num::interface::common::text::{compare_bytes, text_entry, text_entry_of, text_parts_wf,
    lemma_lex_cmp_lt_trans};
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::bridge::order::lemma_lex_cmp_antisym;

verus! {

/// `s` is nondecreasing on `[lo, hi)`.
pub open spec fn sorted_on(s: Seq<u64>, lo: int, hi: int) -> bool {
    forall|a: int, b: int| lo <= a <= b < hi ==> #[trigger] s[a] <= #[trigger] s[b]
}

/// `r` is the lower bound of `key` in `s[lo..hi)`.
pub open spec fn is_lb(s: Seq<u64>, lo: int, hi: int, key: u64, r: int) -> bool {
    &&& lo <= r <= hi
    &&& forall|i: int| lo <= i < r ==> #[trigger] s[i] < key
    &&& forall|i: int| r <= i < hi ==> #[trigger] s[i] >= key
}

/// First position `i` of `[lo, hi)` with `s[i] >= key` (`hi` if none).
pub fn lower_bound(s: &[u64], lo: usize, hi: usize, key: u64) -> (r: usize)
    requires lo <= hi <= s@.len(), sorted_on(s@, lo as int, hi as int),
    ensures is_lb(s@, lo as int, hi as int, key, r as int),
    no_unwind
{
    let mut a = lo;
    let mut b = hi;
    while a < b
        invariant
            lo <= a <= b <= hi <= s@.len(),
            sorted_on(s@, lo as int, hi as int),
            forall|i: int| lo <= i < a ==> #[trigger] s@[i] < key,
            forall|i: int| b <= i < hi ==> #[trigger] s@[i] >= key,
        decreases b - a,
    {
        let mid = a + (b - a) / 2;
        if s[mid] < key {
            a = mid + 1;
        } else {
            b = mid;
        }
    }
    a
}

/// The lower bound of `key` in `s[lo..hi)`, galloping forward from `lo` (fast when it is near `lo`).
pub fn gallop_u64(s: &[u64], lo: usize, hi: usize, key: u64) -> (r: usize)
    requires lo <= hi <= s@.len(), sorted_on(s@, lo as int, hi as int),
    ensures is_lb(s@, lo as int, hi as int, key, r as int),
    no_unwind
{
    let mut a = lo;
    let mut step: usize = 1;
    while a < hi
        invariant
            lo <= a <= hi <= s@.len(),
            sorted_on(s@, lo as int, hi as int),
            forall|i: int| lo <= i < a ==> #[trigger] s@[i] < key,
            step >= 1,
        decreases hi - a,
    {
        if s[a] >= key {
            return a;
        }
        let b = if hi - a > step { a + step } else { hi };
        if b < hi && s[b] < key {
            a = b + 1;
            if step <= hi / 2 {
                step = step * 2;
            }
        } else {
            let r = lower_bound(s, a + 1, b, key);
            proof {
                assert forall|i: int| b <= i < hi implies #[trigger] s@[i] >= key by {
                    assert(s@[b as int] <= s@[i]);
                }
            }
            return r;
        }
    }
    a
}

// ------------------------------------------------------------------------------------------------ dictionaries

/// Value `k` of the dictionary.
pub open spec fn dict_at(off: Seq<u64>, bytes: Seq<u8>, k: int) -> Seq<u8> {
    text_entry(off, bytes, k)
}

/// Value at position `d` of a code list: the dictionary value of code `codes[d]`.
pub open spec fn coded_at(codes: Seq<u64>, off: Seq<u64>, bytes: Seq<u8>, d: int) -> Seq<u8> {
    text_entry(off, bytes, codes[d] as int)
}

/// The values at positions `[lo, hi)` of a code list are dictionary values and strictly increase.
pub open spec fn coded_sorted(codes: Seq<u64>, off: Seq<u64>, bytes: Seq<u8>, count: int, lo: int, hi: int) -> bool {
    &&& text_parts_wf(off, bytes, count)
    &&& 0 <= lo <= hi <= codes.len()
    &&& forall|d: int| lo <= d < hi ==> #[trigger] codes[d] < count
    &&& forall|a: int, b: int| lo <= a < b < hi
        ==> lex_cmp(#[trigger] coded_at(codes, off, bytes, a), #[trigger] coded_at(codes, off, bytes, b)) < 0
}

/// `r` is the lower bound of `key` among positions `[lo, hi)` of the code list, `found` whether it holds `key`.
pub open spec fn is_coded_lb(codes: Seq<u64>, off: Seq<u64>, bytes: Seq<u8>, lo: int, hi: int, key: Seq<u8>, r: int,
    found: bool) -> bool {
    &&& lo <= r <= hi
    &&& forall|d: int| lo <= d < r ==> lex_cmp(#[trigger] coded_at(codes, off, bytes, d), key) < 0
    &&& forall|d: int| r <= d < hi ==> lex_cmp(#[trigger] coded_at(codes, off, bytes, d), key) >= 0
    &&& found == (r < hi && coded_at(codes, off, bytes, r) == key)
    &&& !found ==> forall|d: int| lo <= d < hi ==> #[trigger] coded_at(codes, off, bytes, d) != key
}

/// Value at position `d` of the code list.
fn coded_value<'a>(codes: &[u64], off: &'a [u64], bytes: &'a [u8], count: usize, d: usize) -> (r: (&'a [u8], usize))
    requires d < codes@.len(), codes@[d as int] < count, text_parts_wf(off@, bytes@, count as int),
    ensures r.0@ == coded_at(codes@, off@, bytes@, d as int), r.1 == r.0@.len(),
    no_unwind
{
    text_entry_of(off, bytes, count, codes[d] as usize)
}

/// Lower bound of `key` among positions `[lo, hi)` of a sorted code list (binary search).
fn coded_lb(codes: &[u64], off: &[u64], bytes: &[u8], count: usize, lo: usize, hi: usize, key: &[u8], key_len: usize)
    -> (r: usize)
    requires coded_sorted(codes@, off@, bytes@, count as int, lo as int, hi as int), key_len == key@.len(),
    ensures
        lo <= r <= hi,
        forall|d: int| lo <= d < r ==> lex_cmp(#[trigger] coded_at(codes@, off@, bytes@, d), key@) < 0,
        forall|d: int| r <= d < hi ==> lex_cmp(#[trigger] coded_at(codes@, off@, bytes@, d), key@) >= 0,
    no_unwind
{
    let mut a = lo;
    let mut b = hi;
    while a < b
        invariant
            lo <= a <= b <= hi,
            coded_sorted(codes@, off@, bytes@, count as int, lo as int, hi as int),
            key_len == key@.len(),
            forall|d: int| lo <= d < a ==> lex_cmp(#[trigger] coded_at(codes@, off@, bytes@, d), key@) < 0,
            forall|d: int| b <= d < hi ==> lex_cmp(#[trigger] coded_at(codes@, off@, bytes@, d), key@) >= 0,
        decreases b - a,
    {
        let mid = a + (b - a) / 2;
        let (e, el) = coded_value(codes, off, bytes, count, mid);
        let c = compare_bytes(e, el, key, key_len);
        if c < 0 {
            proof {
                assert forall|d: int| lo <= d < mid + 1 implies lex_cmp(#[trigger] coded_at(codes@, off@, bytes@, d), key@) < 0 by {
                    if d < mid {
                        lemma_lex_cmp_lt_trans(coded_at(codes@, off@, bytes@, d), coded_at(codes@, off@, bytes@, mid as int), key@);
                    }
                }
            }
            a = mid + 1;
        } else {
            proof {
                assert forall|d: int| mid <= d < hi implies lex_cmp(#[trigger] coded_at(codes@, off@, bytes@, d), key@) >= 0 by {
                    if d > mid {
                        let (x, y) = (coded_at(codes@, off@, bytes@, mid as int), coded_at(codes@, off@, bytes@, d));
                        lemma_lex_cmp_antisym(x, y);
                        lemma_lex_cmp_antisym(key@, x);
                        lemma_lex_cmp_antisym(key@, y);
                        lemma_lex_cmp_zero(key@, x);
                        if lex_cmp(key@, x) < 0 {
                            lemma_lex_cmp_lt_trans(key@, x, y);
                        }
                    }
                }
            }
            b = mid;
        }
    }
    a
}

/// Lower bound of `key` among positions `[lo, hi)` of a sorted code list, galloping forward from `lo`, and whether
/// it holds `key`.
pub fn gallop_coded(codes: &[u64], off: &[u64], bytes: &[u8], count: usize, lo: usize, hi: usize, key: &[u8],
    key_len: usize) -> (r: (usize, bool))
    requires coded_sorted(codes@, off@, bytes@, count as int, lo as int, hi as int), key_len == key@.len(),
    ensures is_coded_lb(codes@, off@, bytes@, lo as int, hi as int, key@, r.0 as int, r.1),
    no_unwind
{
    let mut a = lo;
    let mut b = hi;
    let mut step: usize = 1;
    let mut done = false;
    while a < hi && !done
        invariant
            lo <= a <= b <= hi,
            !done ==> b == hi,
            coded_sorted(codes@, off@, bytes@, count as int, lo as int, hi as int),
            key_len == key@.len(),
            forall|d: int| lo <= d < a ==> lex_cmp(#[trigger] coded_at(codes@, off@, bytes@, d), key@) < 0,
            b < hi ==> lex_cmp(coded_at(codes@, off@, bytes@, b as int), key@) >= 0,
            step >= 1,
        decreases (hi - a) as int + if done { 0int } else { 1int },
    {
        let probe = if hi - a > step { a + step } else { hi };
        if probe < hi {
            let (e, el) = coded_value(codes, off, bytes, count, probe);
            if compare_bytes(e, el, key, key_len) < 0 {
                proof {
                    assert forall|d: int| lo <= d < probe + 1 implies lex_cmp(#[trigger] coded_at(codes@, off@, bytes@, d), key@) < 0 by {
                        if d < probe {
                            lemma_lex_cmp_lt_trans(coded_at(codes@, off@, bytes@, d), coded_at(codes@, off@, bytes@, probe as int), key@);
                        }
                    }
                }
                a = probe + 1;
                if step <= hi / 2 {
                    step = step * 2;
                }
            } else {
                b = probe;
                done = true;
            }
        } else {
            done = true;
        }
    }
    proof {
        assert forall|x: int, y: int| a <= x < y < b implies
            lex_cmp(#[trigger] coded_at(codes@, off@, bytes@, x), #[trigger] coded_at(codes@, off@, bytes@, y)) < 0 by {}
        assert forall|d: int| a <= d < b implies #[trigger] codes@[d] < count by {}
    }
    let r = coded_lb(codes, off, bytes, count, a, b, key, key_len);
    proof {
        assert forall|d: int| b <= d < hi implies lex_cmp(#[trigger] coded_at(codes@, off@, bytes@, d), key@) >= 0 by {
            if d > b {
                let (x, y) = (coded_at(codes@, off@, bytes@, b as int), coded_at(codes@, off@, bytes@, d));
                lemma_lex_cmp_antisym(x, y);
                lemma_lex_cmp_antisym(key@, x);
                lemma_lex_cmp_antisym(key@, y);
                lemma_lex_cmp_zero(key@, x);
                if lex_cmp(key@, x) < 0 {
                    lemma_lex_cmp_lt_trans(key@, x, y);
                }
            }
        }
    }
    let found = if r < hi {
        let (e, el) = coded_value(codes, off, bytes, count, r);
        let c = compare_bytes(e, el, key, key_len);
        proof { lemma_lex_cmp_zero(e@, key@); }
        c == 0
    } else {
        false
    };
    proof {
        if !found {
            assert forall|d: int| lo <= d < hi implies #[trigger] coded_at(codes@, off@, bytes@, d) != key@ by {
                lemma_lex_cmp_zero(coded_at(codes@, off@, bytes@, d), key@);
                if d > r && r < hi {
                    let (x, y) = (coded_at(codes@, off@, bytes@, r as int), coded_at(codes@, off@, bytes@, d));
                    lemma_lex_cmp_antisym(x, key@);
                    lemma_lex_cmp_zero(x, key@);
                    lemma_lex_cmp_antisym(key@, x);
                    lemma_lex_cmp_lt_trans(key@, x, y);
                }
            }
        }
    }
    (r, found)
}

/// The dictionary values `[lo, hi)` strictly increase.
pub open spec fn dict_sorted(off: Seq<u64>, bytes: Seq<u8>, count: int, lo: int, hi: int) -> bool {
    &&& text_parts_wf(off, bytes, count)
    &&& 0 <= lo <= hi <= count
    &&& forall|a: int, b: int| lo <= a < b < hi ==> lex_cmp(#[trigger] dict_at(off, bytes, a), #[trigger] dict_at(off, bytes, b)) < 0
}

/// `r` is the lower bound of `key` among values `[lo, hi)`, `found` whether it is `key`.
pub open spec fn is_dict_lb(off: Seq<u64>, bytes: Seq<u8>, lo: int, hi: int, key: Seq<u8>, r: int, found: bool) -> bool {
    &&& lo <= r <= hi
    &&& forall|d: int| lo <= d < r ==> lex_cmp(#[trigger] dict_at(off, bytes, d), key) < 0
    &&& forall|d: int| r <= d < hi ==> lex_cmp(#[trigger] dict_at(off, bytes, d), key) >= 0
    &&& found == (r < hi && dict_at(off, bytes, r) == key)
    &&& !found ==> forall|d: int| lo <= d < hi ==> #[trigger] dict_at(off, bytes, d) != key
}

/// Value `d` of the dictionary.
fn dict_value<'a>(off: &'a [u64], bytes: &'a [u8], count: usize, d: usize) -> (r: (&'a [u8], usize))
    requires d < count, text_parts_wf(off@, bytes@, count as int),
    ensures r.0@ == dict_at(off@, bytes@, d as int), r.1 == r.0@.len(),
    no_unwind
{
    text_entry_of(off, bytes, count, d)
}

/// Lower bound of `key` among values `[lo, hi)` of a sorted dictionary (binary search).
fn dict_lb(off: &[u64], bytes: &[u8], count: usize, lo: usize, hi: usize, key: &[u8], key_len: usize)
    -> (r: usize)
    requires dict_sorted(off@, bytes@, count as int, lo as int, hi as int), key_len == key@.len(),
    ensures
        lo <= r <= hi,
        forall|d: int| lo <= d < r ==> lex_cmp(#[trigger] dict_at(off@, bytes@, d), key@) < 0,
        forall|d: int| r <= d < hi ==> lex_cmp(#[trigger] dict_at(off@, bytes@, d), key@) >= 0,
    no_unwind
{
    let mut a = lo;
    let mut b = hi;
    while a < b
        invariant
            lo <= a <= b <= hi,
            dict_sorted(off@, bytes@, count as int, lo as int, hi as int),
            key_len == key@.len(),
            forall|d: int| lo <= d < a ==> lex_cmp(#[trigger] dict_at(off@, bytes@, d), key@) < 0,
            forall|d: int| b <= d < hi ==> lex_cmp(#[trigger] dict_at(off@, bytes@, d), key@) >= 0,
        decreases b - a,
    {
        let mid = a + (b - a) / 2;
        let (e, el) = dict_value(off, bytes, count, mid);
        let c = compare_bytes(e, el, key, key_len);
        if c < 0 {
            proof {
                assert forall|d: int| lo <= d < mid + 1 implies lex_cmp(#[trigger] dict_at(off@, bytes@, d), key@) < 0 by {
                    if d < mid {
                        lemma_lex_cmp_lt_trans(dict_at(off@, bytes@, d), dict_at(off@, bytes@, mid as int), key@);
                    }
                }
            }
            a = mid + 1;
        } else {
            proof {
                assert forall|d: int| mid <= d < hi implies lex_cmp(#[trigger] dict_at(off@, bytes@, d), key@) >= 0 by {
                    if d > mid {
                        let (x, y) = (dict_at(off@, bytes@, mid as int), dict_at(off@, bytes@, d));
                        lemma_lex_cmp_antisym(x, y);
                        lemma_lex_cmp_antisym(key@, x);
                        lemma_lex_cmp_antisym(key@, y);
                        lemma_lex_cmp_zero(key@, x);
                        if lex_cmp(key@, x) < 0 {
                            lemma_lex_cmp_lt_trans(key@, x, y);
                        }
                    }
                }
            }
            b = mid;
        }
    }
    a
}

/// Lower bound of `key` among values `[lo, hi)` of a sorted dictionary, galloping forward from `lo`, and whether
/// it holds `key`.
pub fn gallop_dict(off: &[u64], bytes: &[u8], count: usize, lo: usize, hi: usize, key: &[u8],
    key_len: usize) -> (r: (usize, bool))
    requires dict_sorted(off@, bytes@, count as int, lo as int, hi as int), key_len == key@.len(),
    ensures is_dict_lb(off@, bytes@, lo as int, hi as int, key@, r.0 as int, r.1),
    no_unwind
{
    let mut a = lo;
    let mut b = hi;
    let mut step: usize = 1;
    let mut done = false;
    while a < hi && !done
        invariant
            lo <= a <= b <= hi,
            !done ==> b == hi,
            dict_sorted(off@, bytes@, count as int, lo as int, hi as int),
            key_len == key@.len(),
            forall|d: int| lo <= d < a ==> lex_cmp(#[trigger] dict_at(off@, bytes@, d), key@) < 0,
            b < hi ==> lex_cmp(dict_at(off@, bytes@, b as int), key@) >= 0,
            step >= 1,
        decreases (hi - a) as int + if done { 0int } else { 1int },
    {
        let probe = if hi - a > step { a + step } else { hi };
        if probe < hi {
            let (e, el) = dict_value(off, bytes, count, probe);
            if compare_bytes(e, el, key, key_len) < 0 {
                proof {
                    assert forall|d: int| lo <= d < probe + 1 implies lex_cmp(#[trigger] dict_at(off@, bytes@, d), key@) < 0 by {
                        if d < probe {
                            lemma_lex_cmp_lt_trans(dict_at(off@, bytes@, d), dict_at(off@, bytes@, probe as int), key@);
                        }
                    }
                }
                a = probe + 1;
                if step <= hi / 2 {
                    step = step * 2;
                }
            } else {
                b = probe;
                done = true;
            }
        } else {
            done = true;
        }
    }
    proof {
        assert forall|x: int, y: int| a <= x < y < b implies
            lex_cmp(#[trigger] dict_at(off@, bytes@, x), #[trigger] dict_at(off@, bytes@, y)) < 0 by {}
    }
    let r = dict_lb(off, bytes, count, a, b, key, key_len);
    proof {
        assert forall|d: int| b <= d < hi implies lex_cmp(#[trigger] dict_at(off@, bytes@, d), key@) >= 0 by {
            if d > b {
                let (x, y) = (dict_at(off@, bytes@, b as int), dict_at(off@, bytes@, d));
                lemma_lex_cmp_antisym(x, y);
                lemma_lex_cmp_antisym(key@, x);
                lemma_lex_cmp_antisym(key@, y);
                lemma_lex_cmp_zero(key@, x);
                if lex_cmp(key@, x) < 0 {
                    lemma_lex_cmp_lt_trans(key@, x, y);
                }
            }
        }
    }
    let found = if r < hi {
        let (e, el) = dict_value(off, bytes, count, r);
        let c = compare_bytes(e, el, key, key_len);
        proof { lemma_lex_cmp_zero(e@, key@); }
        c == 0
    } else {
        false
    };
    proof {
        if !found {
            assert forall|d: int| lo <= d < hi implies #[trigger] dict_at(off@, bytes@, d) != key@ by {
                lemma_lex_cmp_zero(dict_at(off@, bytes@, d), key@);
                if d > r && r < hi {
                    let (x, y) = (dict_at(off@, bytes@, r as int), dict_at(off@, bytes@, d));
                    lemma_lex_cmp_antisym(x, key@);
                    lemma_lex_cmp_zero(x, key@);
                    lemma_lex_cmp_antisym(key@, x);
                    lemma_lex_cmp_lt_trans(key@, x, y);
                }
            }
        }
    }
    (r, found)
}


/// A position of `key` among `s[0..n)` by binary search, or `None`. A found position always holds `key`; when
/// `s[0..n)` is sorted, `None` means that `key` is absent (otherwise it may be present elsewhere).
pub fn find_key(s: &Vec<u64>, n: usize, key: u64) -> (r: Option<usize>)
    requires n <= s@.len(),
    ensures r matches Some(i) ==> i < n && s@[i as int] == key,
    no_unwind
{
    let mut lo: usize = 0;
    let mut hi: usize = n;
    while lo < hi
        invariant lo <= hi <= n, n <= s@.len(),
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        let x = s[mid];
        if x == key {
            return Some(mid);
        }
        if x < key {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    None
}

} // verus!
