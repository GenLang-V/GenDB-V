//! Text values stored as two parts: `U64` offsets (`count + 1` entries, nondecreasing) and `U8` bytes; value `k` is
//! `bytes[offsets[k] .. offsets[k + 1]]`. A sorted dictionary is such a list whose values strictly increase in byte
//! order (`lex_cmp`, SQL text order in the C collation), so equal codes mean equal values and code order is value
//! order. Readers here work on slices (usable in worker bodies) and on stored parts.
use vstd::prelude::*;
use crate::spec::text::lex_cmp;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::StoredParts;
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::bridge::order::lemma_lex_cmp_antisym;

verus! {

/// Bytes of value `k`.
pub open spec fn text_entry(off: Seq<u64>, bytes: Seq<u8>, k: int) -> Seq<u8> {
    bytes.subrange(off[k] as int, off[k + 1] as int)
}

/// `count` values: `count + 1` nondecreasing offsets, the last within `bytes`; value `k` is the byte range
/// `[off[k], off[k + 1])`.
pub open spec fn text_parts_wf(off: Seq<u64>, bytes: Seq<u8>, count: int) -> bool {
    &&& count >= 0
    &&& off.len() == count + 1
    &&& off[count] <= bytes.len()
    &&& forall|a: int, b: int| 0 <= a <= b <= count ==> #[trigger] off[a] <= #[trigger] off[b]
}

/// Value `k` is a byte range inside `bytes`.
pub proof fn lemma_text_entry_range(off: Seq<u64>, bytes: Seq<u8>, count: int, k: int)
    requires text_parts_wf(off, bytes, count), 0 <= k < count,
    ensures off[k] <= off[k + 1] <= bytes.len(), text_entry(off, bytes, k).len() == off[k + 1] - off[k],
{
    assert(off[k] <= off[k + 1]);
    assert(off[k + 1] <= off[count]);
}

/// The values strictly increase in byte order (a sorted dictionary: distinct values, code order = value order).
pub open spec fn text_strictly_sorted(off: Seq<u64>, bytes: Seq<u8>, count: int) -> bool {
    forall|a: int, b: int| 0 <= a < b < count
        ==> lex_cmp(#[trigger] text_entry(off, bytes, a), #[trigger] text_entry(off, bytes, b)) < 0
}

/// In a sorted dictionary, codes are equal exactly when their values are, and code order is byte order.
pub proof fn lemma_dict_codes(off: Seq<u64>, bytes: Seq<u8>, count: int, a: int, b: int)
    requires text_strictly_sorted(off, bytes, count), 0 <= a < count, 0 <= b < count,
    ensures
        (text_entry(off, bytes, a) == text_entry(off, bytes, b)) == (a == b),
        (lex_cmp(text_entry(off, bytes, a), text_entry(off, bytes, b)) < 0) == (a < b),
        (lex_cmp(text_entry(off, bytes, a), text_entry(off, bytes, b)) == 0) == (a == b),
{
    let (x, y) = (text_entry(off, bytes, a), text_entry(off, bytes, b));
    lemma_lex_cmp_zero(x, y);
    lemma_lex_cmp_antisym(x, y);
    if b < a {
        assert(lex_cmp(y, x) < 0);
    }
}

/// The offsets and bytes of two parts.
pub open spec fn u64_part(p: PartView) -> Seq<u64> {
    match p {
        PartView::U64(s) => s,
        _ => Seq::empty(),
    }
}

pub open spec fn u8_part(p: PartView) -> Seq<u8> {
    match p {
        PartView::U8(s) => s,
        _ => Seq::empty(),
    }
}

/// `[lo, hi)` of a slice, `no_unwind`.
pub fn subslice<T>(s: &[T], lo: usize, hi: usize) -> (r: &[T])
    requires lo <= hi <= s@.len(),
    ensures r@ == s@.subrange(lo as int, hi as int),
    no_unwind
{
    let (_, tail) = s.split_at(lo);
    let (mid, _) = tail.split_at(hi - lo);
    assert(mid@ =~= s@.subrange(lo as int, hi as int));
    mid
}

/// Bytes of value `k` of a text list held as slices, with its length; `no_unwind`.
pub fn text_entry_of<'a>(off: &'a [u64], bytes: &'a [u8], count: usize, k: usize) -> (r: (&'a [u8], usize))
    requires text_parts_wf(off@, bytes@, count as int), k < count,
    ensures r.0@ == text_entry(off@, bytes@, k as int), r.1 == r.0@.len(),
    no_unwind
{
    proof { lemma_text_entry_range(off@, bytes@, count as int, k as int); }
    let lo = off[k];
    let hi = off[k + 1];
    assert(hi <= bytes.len());
    let s = subslice(bytes, lo as usize, hi as usize);
    (s, (hi - lo) as usize)
}

/// Byte order of two slices (`lex_cmp`), lengths passed in; `no_unwind`.
pub fn compare_bytes(x: &[u8], xn: usize, y: &[u8], yn: usize) -> (r: i8)
    requires xn == x@.len(), yn == y@.len(),
    ensures r as int == lex_cmp(x@, y@),
    no_unwind
{
    let mut i: usize = 0;
    assert(x@.subrange(0, xn as int) =~= x@);
    assert(y@.subrange(0, yn as int) =~= y@);
    while i < xn && i < yn
        invariant
            xn == x@.len(), yn == y@.len(), i <= xn, i <= yn,
            lex_cmp(x@.subrange(i as int, xn as int), y@.subrange(i as int, yn as int)) == lex_cmp(x@, y@),
        decreases xn - i,
    {
        let ghost sx = x@.subrange(i as int, xn as int);
        let ghost sy = y@.subrange(i as int, yn as int);
        if x[i] < y[i] {
            return -1;
        } else if x[i] > y[i] {
            return 1;
        }
        assert(sx.drop_first() =~= x@.subrange(i + 1, xn as int));
        assert(sy.drop_first() =~= y@.subrange(i + 1, yn as int));
        i = i + 1;
    }
    if i < xn { 1 } else if i < yn { -1 } else { 0 }
}

/// Every value below position `mid + 1` sorts before `key`, when value `mid` does.
proof fn lemma_search_below(off: Seq<u64>, bytes: Seq<u8>, count: int, key: Seq<u8>, mid: int)
    requires
        text_strictly_sorted(off, bytes, count),
        0 <= mid < count,
        lex_cmp(text_entry(off, bytes, mid), key) < 0,
    ensures
        forall|k: int| 0 <= k <= mid ==> lex_cmp(#[trigger] text_entry(off, bytes, k), key) < 0,
{
    assert forall|k: int| 0 <= k <= mid implies lex_cmp(#[trigger] text_entry(off, bytes, k), key) < 0 by {
        if k < mid {
            lemma_lex_cmp_lt_trans(text_entry(off, bytes, k), text_entry(off, bytes, mid), key);
        }
    }
}

/// Every value from position `mid` on sorts after `key`, when value `mid` does.
proof fn lemma_search_above(off: Seq<u64>, bytes: Seq<u8>, count: int, key: Seq<u8>, mid: int)
    requires
        text_strictly_sorted(off, bytes, count),
        0 <= mid < count,
        lex_cmp(text_entry(off, bytes, mid), key) > 0,
    ensures
        forall|k: int| mid <= k < count ==> lex_cmp(#[trigger] text_entry(off, bytes, k), key) > 0,
{
    assert forall|k: int| mid <= k < count implies lex_cmp(#[trigger] text_entry(off, bytes, k), key) > 0 by {
        if k > mid {
            let (e, f) = (text_entry(off, bytes, mid), text_entry(off, bytes, k));
            lemma_lex_cmp_antisym(e, f);
            lemma_lex_cmp_antisym(key, e);
            lemma_lex_cmp_antisym(key, f);
            lemma_lex_cmp_lt_trans(key, e, f);
        }
    }
}

/// Binary search of `key` in a sorted dictionary held as slices: `Some(k)` exactly when value `k` is `key`
/// (sound and complete); `no_unwind`.
pub fn find_text(off: &[u64], bytes: &[u8], count: usize, key: &[u8], key_len: usize) -> (r: Option<usize>)
    requires
        text_parts_wf(off@, bytes@, count as int),
        text_strictly_sorted(off@, bytes@, count as int),
        key_len == key@.len(),
    ensures
        r matches Some(k) ==> k < count && text_entry(off@, bytes@, k as int) == key@,
        r is None ==> forall|k: int| 0 <= k < count ==> text_entry(off@, bytes@, k) != key@,
    no_unwind
{
    let mut lo: usize = 0;
    let mut hi: usize = count;
    while lo < hi
        invariant
            lo <= hi <= count,
            text_parts_wf(off@, bytes@, count as int),
            text_strictly_sorted(off@, bytes@, count as int),
            key_len == key@.len(),
            forall|k: int| 0 <= k < lo ==> lex_cmp(#[trigger] text_entry(off@, bytes@, k), key@) < 0,
            forall|k: int| hi <= k < count ==> lex_cmp(#[trigger] text_entry(off@, bytes@, k), key@) > 0,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        let (e, en) = text_entry_of(off, bytes, count, mid);
        let c = compare_bytes(e, en, key, key_len);
        if c == 0 {
            proof { lemma_lex_cmp_zero(e@, key@); }
            return Some(mid);
        } else if c < 0 {
            proof { lemma_search_below(off@, bytes@, count as int, key@, mid as int); }
            lo = mid + 1;
        } else {
            proof { lemma_search_above(off@, bytes@, count as int, key@, mid as int); }
            hi = mid;
        }
    }
    proof {
        assert forall|k: int| 0 <= k < count implies text_entry(off@, bytes@, k) != key@ by {
            lemma_lex_cmp_zero(text_entry(off@, bytes@, k), key@);
        }
    }
    None
}

/// Strict byte order is transitive.
pub proof fn lemma_lex_cmp_lt_trans(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>)
    requires lex_cmp(a, b) < 0, lex_cmp(b, c) < 0,
    ensures lex_cmp(a, c) < 0,
{
    crate::bridge::order::lemma_lex_cmp_trans(a, b, c);
    lemma_lex_cmp_zero(a, c);
    if a == c {
        lemma_lex_cmp_antisym(b, c);
    }
}

/// Bytes of value `k` of the text list stored in parts `p_off` (U64 offsets) and `p_bytes` (U8 bytes): two extent
/// requests (offsets `[k, k + 2)`, then the value's bytes).
pub fn read_text_entry(st: &mut StoredParts, p_off: usize, p_bytes: usize, count: usize, k: usize) -> (r: &'static [u8])
    requires
        p_off < old(st)@.len(), p_bytes < old(st)@.len(),
        old(st)@[p_off as int] is U64, old(st)@[p_bytes as int] is U8,
        text_parts_wf(u64_part(old(st)@[p_off as int]), u8_part(old(st)@[p_bytes as int]), count as int),
        k < count < usize::MAX,
    ensures
        final(st)@ == old(st)@,
        r@ == text_entry(u64_part(old(st)@[p_off as int]), u8_part(old(st)@[p_bytes as int]), k as int),
{
    let ghost off = u64_part(st@[p_off as int]);
    let ghost bytes = u8_part(st@[p_bytes as int]);
    proof { lemma_text_entry_range(off, bytes, count as int, k as int); }
    let pair = st.extent_u64(p_off, k, k + 2);
    let lo = pair[0];
    let hi = pair[1];
    assert(lo == off[k as int] && hi == off[k + 1]);
    let nbytes = st.part_len(p_bytes);
    assert(hi <= nbytes);
    st.extent_u8(p_bytes, lo as usize, hi as usize)
}

/// Binary search of `key` in the sorted dictionary stored in parts `p_off` (U64 offsets) and `p_bytes` (U8 bytes):
/// `Some(k)` exactly when value `k` is `key` (sound and complete). Reads both parts whole (two extent requests).
pub fn find_in_stored_dict(st: &mut StoredParts, p_off: usize, p_bytes: usize, count: usize, key: &[u8]) -> (r: Option<usize>)
    requires
        p_off < old(st)@.len(), p_bytes < old(st)@.len(),
        old(st)@[p_off as int] is U64, old(st)@[p_bytes as int] is U8,
        text_parts_wf(u64_part(old(st)@[p_off as int]), u8_part(old(st)@[p_bytes as int]), count as int),
        text_strictly_sorted(u64_part(old(st)@[p_off as int]), u8_part(old(st)@[p_bytes as int]), count as int),
        count < usize::MAX,
    ensures
        final(st)@ == old(st)@,
        r matches Some(k) ==> k < count
            && text_entry(u64_part(old(st)@[p_off as int]), u8_part(old(st)@[p_bytes as int]), k as int) == key@,
        r is None ==> forall|k: int| 0 <= k < count
            ==> text_entry(u64_part(old(st)@[p_off as int]), u8_part(old(st)@[p_bytes as int]), k) != key@,
{
    let ghost off_v = u64_part(st@[p_off as int]);
    let ghost bytes_v = u8_part(st@[p_bytes as int]);
    let off = st.extent_u64(p_off, 0, count + 1);
    let nb = st.part_len(p_bytes);
    let bytes = st.extent_u8(p_bytes, 0, nb);
    proof {
        assert(off@ =~= off_v);
        assert(bytes@ =~= bytes_v);
    }
    let key_len = key.len();
    find_text(off, bytes, count, key, key_len)
}

} // verus!
