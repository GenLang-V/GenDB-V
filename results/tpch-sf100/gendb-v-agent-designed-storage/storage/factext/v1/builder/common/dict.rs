//! Sorted text dictionaries: `build_dict` collects the distinct values of a text column into a dictionary whose
//! entries are strictly increasing in bytewise order (`lex_cmp`) and that holds every value of the column;
//! `dict_search` finds a value's entry by binary search (`no_unwind`, usable in worker tasks).
//! The dictionary is flat: entry `x` is `bytes[offs[x] .. offs[x + 1]]` (`colfmt::text_of`).
use vstd::prelude::*;
use crate::spec::text::lex_cmp;
use crate::link::query::{text_at, text_wf, TextCol};
use crate::gendb_entry::work::text_bytes;
use crate::builder::iface::common::colfmt::*;

verus! {

/// A flat dictionary: `offs.len() - 1` entries.
pub struct Dict {
    pub offs: Vec<u64>,
    pub bytes: Vec<u8>,
}

/// Number of entries.
pub open spec fn dict_k(d: Dict) -> int {
    d.offs@.len() - 1
}

/// Well-formed and strictly sorted.
pub open spec fn dict_wf(d: Dict) -> bool {
    &&& d.offs@.len() >= 1
    &&& text_parts_wf(d.offs@, d.bytes@, dict_k(d))
    &&& dict_sorted(d.offs@, d.bytes@, dict_k(d))
}

/// Entry `x` of the dictionary.
pub open spec fn dict_entry(d: Dict, x: int) -> Seq<u8> {
    text_of(d.offs@, d.bytes@, x)
}

/// Some entry holds `t`.
pub open spec fn dict_has(d: Dict, t: Seq<u8>) -> bool {
    exists|x: int| 0 <= x < dict_k(d) && dict_entry(d, x) == t
}

/// The entry holding `t` (unique in a sorted dictionary).
pub open spec fn dict_index_of(d: Dict, t: Seq<u8>) -> int {
    choose|x: int| 0 <= x < dict_k(d) && dict_entry(d, x) == t
}

/// The index `dict_index_of` names holds `t`, and it is the only one.
pub proof fn lemma_dict_index_of(d: Dict, t: Seq<u8>, x: int)
    requires
        dict_wf(d),
        0 <= x < dict_k(d),
        dict_entry(d, x) == t,
    ensures
        dict_index_of(d, t) == x,
{
    let y = dict_index_of(d, t);
    if y != x {
        lemma_dict_distinct(d.offs@, d.bytes@, dict_k(d), x, y);
    }
}

/// Byte strings of a sequence of entries, in order.
pub open spec fn ents_view(ents: Seq<Vec<u8>>) -> Seq<Seq<u8>> {
    ents.map_values(|v: Vec<u8>| v@)
}

/// Some entry is `t`.
pub open spec fn in_ents(ents: Seq<Vec<u8>>, t: Seq<u8>) -> bool {
    exists|x: int| 0 <= x < ents.len() && ents[x]@ == t
}

/// Strictly increasing in bytewise order (adjacent entries).
pub open spec fn strictly_sorted(s: Seq<Seq<u8>>) -> bool {
    forall|a: int| 0 <= a < s.len() - 1 ==> #[trigger] lex_cmp(s[a], s[a + 1]) < 0
}

proof fn lemma_sorted_order(s: Seq<Seq<u8>>, a: int, b: int)
    requires
        strictly_sorted(s),
        0 <= a < b < s.len(),
    ensures
        lex_cmp(s[a], s[b]) < 0,
    decreases b - a,
{
    assert(lex_cmp(s[b - 1], s[(b - 1) + 1]) < 0);
    if b > a + 1 {
        lemma_sorted_order(s, a, b - 1);
        crate::bridge::order::lemma_lex_cmp_trans(s[a], s[b - 1], s[b]);
        if lex_cmp(s[a], s[b]) == 0 {
            crate::bridge::equality::lemma_lex_cmp_zero(s[a], s[b]);
            crate::bridge::order::lemma_lex_cmp_antisym(s[b - 1], s[b]);
        }
    }
}

proof fn lemma_lex_step(x: Seq<u8>, y: Seq<u8>, i: int)
    requires
        0 <= i < x.len(),
        i < y.len(),
        x[i] == y[i],
    ensures
        lex_cmp(x.subrange(i, x.len() as int), y.subrange(i, y.len() as int))
            == lex_cmp(x.subrange(i + 1, x.len() as int), y.subrange(i + 1, y.len() as int)),
{
    let sx = x.subrange(i, x.len() as int);
    let sy = y.subrange(i, y.len() as int);
    assert(sx.drop_first() =~= x.subrange(i + 1, x.len() as int));
    assert(sy.drop_first() =~= y.subrange(i + 1, y.len() as int));
}

/// Bytewise comparison of `x[xlo .. xhi]` with `y` (`ylen` bytes): `lex_cmp`, `no_unwind`.
pub fn cmp_window(x: &Vec<u8>, xlo: usize, xhi: usize, y: &[u8], ylen: usize) -> (r: i8)
    requires
        xlo <= xhi <= x@.len(),
        ylen == y@.len(),
    ensures
        r as int == lex_cmp(x@.subrange(xlo as int, xhi as int), y@),
    no_unwind
{
    let ghost xs = x@.subrange(xlo as int, xhi as int);
    let xlen = xhi - xlo;
    let mut i: usize = 0;
    assert(xs.subrange(0, xs.len() as int) =~= xs);
    assert(y@.subrange(0, y@.len() as int) =~= y@);
    while i < xlen && i < ylen
        invariant
            xlo <= xhi <= x@.len(),
            xlen == xhi - xlo,
            ylen == y@.len(),
            xs == x@.subrange(xlo as int, xhi as int),
            i <= xlen,
            i <= ylen,
            lex_cmp(xs.subrange(i as int, xs.len() as int), y@.subrange(i as int, y@.len() as int)) == lex_cmp(xs, y@),
        decreases xlen - i,
    {
        let a = x[xlo + i];
        let b = y[i];
        assert(a == xs[i as int]);
        let ghost sx = xs.subrange(i as int, xs.len() as int);
        let ghost sy = y@.subrange(i as int, y@.len() as int);
        if a < b {
            assert(sx[0] == a && sy[0] == b);
            return -1;
        } else if a > b {
            assert(sx[0] == a && sy[0] == b);
            return 1;
        }
        proof {
            lemma_lex_step(xs, y@, i as int);
        }
        i = i + 1;
    }
    let ghost sx = xs.subrange(i as int, xs.len() as int);
    let ghost sy = y@.subrange(i as int, y@.len() as int);
    if i < xlen {
        assert(sy.len() == 0 && sx.len() > 0);
        1
    } else if i < ylen {
        assert(sx.len() == 0 && sy.len() > 0);
        -1
    } else {
        assert(sx.len() == 0 && sy.len() == 0);
        0
    }
}

/// Binary search of `a` (`alen` bytes) among strictly sorted entries: `Ok(x)` with `ents[x] == a`, or `Err(p)`
/// with every entry before `p` smaller and every entry from `p` on larger.
fn ents_search(ents: &Vec<Vec<u8>>, a: &[u8], alen: usize) -> (r: Result<usize, usize>)
    requires
        strictly_sorted(ents_view(ents@)),
        alen == a@.len(),
    ensures
        r matches Ok(x) ==> x < ents@.len() && ents@[x as int]@ == a@,
        r matches Err(p) ==> p <= ents@.len()
            && (forall|y: int| 0 <= y < p ==> lex_cmp(#[trigger] ents@[y]@, a@) < 0)
            && (forall|y: int| p <= y < ents@.len() ==> lex_cmp(#[trigger] ents@[y]@, a@) > 0),
{
    let ghost s = ents_view(ents@);
    let mut lo: usize = 0;
    let mut hi: usize = ents.len();
    while lo < hi
        invariant
            s == ents_view(ents@),
            strictly_sorted(s),
            alen == a@.len(),
            lo <= hi <= ents@.len(),
            forall|y: int| 0 <= y < lo ==> lex_cmp(#[trigger] ents@[y]@, a@) < 0,
            forall|y: int| hi <= y < ents@.len() ==> lex_cmp(#[trigger] ents@[y]@, a@) > 0,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        let e = &ents[mid];
        let c = cmp_window(e, 0, e.len(), a, alen);
        proof {
            assert(e@.subrange(0, e@.len() as int) =~= e@);
            assert(s[mid as int] == e@);
        }
        if c == 0 {
            proof {
                crate::bridge::equality::lemma_lex_cmp_zero(e@, a@);
            }
            return Ok(mid);
        } else if c < 0 {
            proof {
                assert forall|y: int| 0 <= y < mid + 1 implies lex_cmp(#[trigger] ents@[y]@, a@) < 0 by {
                    if y < mid {
                        lemma_sorted_order(s, y, mid as int);
                        assert(s[y] == ents@[y]@);
                        crate::bridge::order::lemma_lex_cmp_trans(s[y], s[mid as int], a@);
                        if lex_cmp(s[y], a@) == 0 {
                            crate::bridge::equality::lemma_lex_cmp_zero(s[y], a@);
                            crate::bridge::order::lemma_lex_cmp_antisym(s[y], s[mid as int]);
                        }
                    }
                }
            }
            lo = mid + 1;
        } else {
            proof {
                assert forall|y: int| mid <= y < ents@.len() implies lex_cmp(#[trigger] ents@[y]@, a@) > 0 by {
                    if y > mid {
                        lemma_sorted_order(s, mid as int, y);
                        assert(s[y] == ents@[y]@);
                        crate::bridge::order::lemma_lex_cmp_antisym(s[mid as int], s[y]);
                        crate::bridge::order::lemma_lex_cmp_antisym(s[mid as int], a@);
                        crate::bridge::order::lemma_lex_cmp_antisym(s[y], a@);
                        crate::bridge::order::lemma_lex_cmp_trans(a@, s[mid as int], s[y]);
                        if lex_cmp(s[y], a@) == 0 {
                            crate::bridge::equality::lemma_lex_cmp_zero(s[y], a@);
                            crate::bridge::equality::lemma_lex_cmp_zero(a@, s[y]);
                        }
                    }
                }
            }
            hi = mid;
        }
    }
    Err(lo)
}

/// Copies `a` (`alen` bytes) into a new vector.
fn copy_bytes(a: &[u8], alen: usize) -> (v: Vec<u8>)
    requires alen == a@.len(),
    ensures v@ == a@,
{
    let mut v: Vec<u8> = Vec::with_capacity(alen);
    let mut i: usize = 0;
    while i < alen
        invariant
            alen == a@.len(),
            i <= alen,
            v@ == a@.subrange(0, i as int),
        decreases alen - i,
    {
        v.push(a[i]);
        i = i + 1;
        proof {
            assert(v@ =~= a@.subrange(0, i as int));
        }
    }
    proof {
        assert(a@.subrange(0, alen as int) =~= a@);
    }
    v
}

/// The distinct values of text column `t` (`n` rows) as a strictly sorted dictionary holding every value.
pub fn build_dict(t: &TextCol, n: usize) -> (d: Dict)
    requires
        crate::builder::common::colsrc::twf(t@, n as int),
    ensures
        dict_wf(d),
        forall|i: int| 0 <= i < n ==> #[trigger] dict_has(d, text_at(t@, i)),
{
    proof {
        reveal(crate::builder::common::colsrc::twf);
    }
    let mut ents: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            text_wf(t@, n as int),
            i <= n,
            strictly_sorted(ents_view(ents@)),
            forall|r: int| 0 <= r < i ==> in_ents(ents@, #[trigger] text_at(t@, r)),
        decreases n - i,
    {
        assert(0 <= t.offsets@[i as int] <= t.offsets@[i + 1] <= t.bytes@.len());
        let a = text_bytes(t, i);
        let alen = a.len();
        let ghost old_ents = ents@;
        match ents_search(&ents, a, alen) {
            Ok(_x) => {},
            Err(p) => {
                let v = copy_bytes(a, alen);
                ents.insert(p, v);
                proof {
                    old_ents.insert_ensures(p as int, v);
                    let s = ents_view(ents@);
                    assert forall|q: int| 0 <= q < s.len() - 1 implies #[trigger] lex_cmp(s[q], s[q + 1]) < 0 by {
                        if q + 1 < p {
                            assert(s[q] == old_ents[q]@ && s[q + 1] == old_ents[q + 1]@);
                            assert(lex_cmp(ents_view(old_ents)[q], ents_view(old_ents)[q + 1]) < 0);
                        } else if q + 1 == p {
                            assert(s[q] == old_ents[q]@ && s[q + 1] == a@);
                        } else if q == p {
                            assert(s[q] == a@ && s[q + 1] == old_ents[q]@);
                            crate::bridge::order::lemma_lex_cmp_antisym(old_ents[q]@, a@);
                        } else {
                            assert(s[q] == old_ents[q - 1]@ && s[q + 1] == old_ents[q]@);
                            assert(lex_cmp(ents_view(old_ents)[q - 1], ents_view(old_ents)[(q - 1) + 1]) < 0);
                        }
                    }
                    assert forall|r: int| 0 <= r < i implies in_ents(ents@, #[trigger] text_at(t@, r)) by {
                        assert(in_ents(old_ents, text_at(t@, r)));
                        let x = choose|x: int| 0 <= x < old_ents.len() && old_ents[x]@ == text_at(t@, r);
                        if x < p {
                            assert(ents@[x]@ == text_at(t@, r));
                        } else {
                            assert(ents@[x + 1]@ == text_at(t@, r));
                        }
                    }
                    assert(ents@[p as int]@ == text_at(t@, i as int));
                }
            },
        }
        proof {
            assert(in_ents(ents@, text_at(t@, i as int)));
        }
        i = i + 1;
    }
    let d = flatten(&ents);
    proof {
        assert forall|i: int| 0 <= i < n implies #[trigger] dict_has(d, text_at(t@, i)) by {
            assert(in_ents(ents@, text_at(t@, i)));
            let x = choose|x: int| 0 <= x < ents@.len() && ents@[x]@ == text_at(t@, i);
            assert(dict_entry(d, x) == ents@[x]@);
        }
    }
    d
}

/// The entries as a flat dictionary (same entries, same order).
fn flatten(ents: &Vec<Vec<u8>>) -> (d: Dict)
    requires
        strictly_sorted(ents_view(ents@)),
    ensures
        dict_wf(d),
        dict_k(d) == ents@.len(),
        forall|x: int| 0 <= x < ents@.len() ==> #[trigger] dict_entry(d, x) == ents@[x]@,
{
    let mut offs: Vec<u64> = Vec::new();
    let mut bytes: Vec<u8> = Vec::new();
    offs.push(0);
    let mut x: usize = 0;
    while x < ents.len()
        invariant
            x <= ents@.len(),
            offs@.len() == x + 1,
            offs@[x as int] == bytes@.len(),
            text_parts_wf(offs@, bytes@, x as int),
            forall|y: int| 0 <= y < x ==> #[trigger] text_of(offs@, bytes@, y) == ents@[y]@,
        decreases ents@.len() - x,
    {
        let e = &ents[x];
        let ghost before = bytes@;
        let mut i: usize = 0;
        while i < e.len()
            invariant
                i <= e@.len(),
                bytes@ == before + e@.subrange(0, i as int),
            decreases e@.len() - i,
        {
            bytes.push(e[i]);
            i = i + 1;
            proof {
                assert(bytes@ =~= before + e@.subrange(0, i as int));
            }
        }
        let ghost old_offs = offs@;
        offs.push(bytes.len() as u64);
        proof {
            assert(e@.subrange(0, e@.len() as int) =~= e@);
            assert forall|y: int| 0 <= y < x + 1 implies #[trigger] text_of(offs@, bytes@, y) == ents@[y]@ by {
                if y < x {
                    assert(offs@[y] == old_offs[y] && offs@[y + 1] == old_offs[y + 1]);
                    assert(text_of(old_offs, before, y) == ents@[y]@);
                    assert(text_range_ok(old_offs, before, y));
                    assert(bytes@.subrange(offs@[y] as int, offs@[y + 1] as int) =~= before.subrange(offs@[y] as int, offs@[y + 1] as int));
                } else {
                    assert(bytes@.subrange(offs@[y] as int, offs@[y + 1] as int) =~= e@);
                }
            }
            assert forall|j: int| 0 <= j < x + 1 implies #[trigger] text_range_ok(offs@, bytes@, j) by {
                if j < x {
                    assert(text_range_ok(old_offs, before, j));
                }
            }
        }
        x = x + 1;
    }
    let d = Dict { offs, bytes };
    proof {
        let s = ents_view(ents@);
        assert forall|a: int| 0 <= a < dict_k(d) - 1 implies #[trigger] lex_cmp(text_of(d.offs@, d.bytes@, a), text_of(d.offs@, d.bytes@, a + 1)) < 0 by {
            assert(s[a] == ents@[a]@ && s[a + 1] == ents@[a + 1]@);
        }
    }
    d
}

proof fn lemma_search_below(d: Dict, a: Seq<u8>, mid: int, target: int)
    requires
        dict_wf(d),
        0 <= mid < dict_k(d),
        0 <= target < dict_k(d),
        dict_entry(d, target) == a,
        lex_cmp(dict_entry(d, mid), a) < 0,
    ensures
        target > mid,
{
    if target < mid {
        lemma_dict_order(d.offs@, d.bytes@, dict_k(d), target, mid);
        crate::bridge::order::lemma_lex_cmp_antisym(dict_entry(d, target), dict_entry(d, mid));
    } else if target == mid {
        crate::bridge::equality::lemma_lex_cmp_zero(dict_entry(d, mid), a);
    }
}

proof fn lemma_search_above(d: Dict, a: Seq<u8>, mid: int, target: int)
    requires
        dict_wf(d),
        0 <= mid < dict_k(d),
        0 <= target < dict_k(d),
        dict_entry(d, target) == a,
        lex_cmp(dict_entry(d, mid), a) > 0,
    ensures
        target < mid,
{
    if target > mid {
        lemma_dict_order(d.offs@, d.bytes@, dict_k(d), mid, target);
    } else if target == mid {
        crate::bridge::equality::lemma_lex_cmp_zero(dict_entry(d, mid), a);
    }
}

/// The entry holding `a` (`alen` bytes), by binary search, `no_unwind`.
pub fn dict_search(d: &Dict, a: &[u8], alen: usize) -> (x: usize)
    requires
        dict_wf(*d),
        dict_has(*d, a@),
        alen == a@.len(),
    ensures
        x < dict_k(*d),
        dict_entry(*d, x as int) == a@,
        x == dict_index_of(*d, a@),
    no_unwind
{
    let ghost k = dict_k(*d);
    let ghost target = choose|x: int| 0 <= x < dict_k(*d) && dict_entry(*d, x) == a@;
    let blen = d.bytes.len();
    let mut lo: usize = 0;
    let mut hi: usize = d.offs.len() - 1;
    while lo < hi
        invariant
            dict_wf(*d),
            k == dict_k(*d),
            blen == d.bytes@.len(),
            alen == a@.len(),
            0 <= target < k,
            dict_entry(*d, target) == a@,
            lo <= target < hi <= k,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        assert(text_range_ok(d.offs@, d.bytes@, mid as int));
        let c = cmp_window(&d.bytes, d.offs[mid] as usize, d.offs[mid + 1] as usize, a, alen);
        if c == 0 {
            proof {
                crate::bridge::equality::lemma_lex_cmp_zero(dict_entry(*d, mid as int), a@);
                lemma_dict_index_of(*d, a@, mid as int);
            }
            return mid;
        } else if c < 0 {
            proof {
                lemma_search_below(*d, a@, mid as int, target);
            }
            lo = mid + 1;
        } else {
            proof {
                lemma_search_above(*d, a@, mid as int, target);
            }
            hi = mid;
        }
    }
    proof {
        assert(false);
    }
    0
}

} // verus!
