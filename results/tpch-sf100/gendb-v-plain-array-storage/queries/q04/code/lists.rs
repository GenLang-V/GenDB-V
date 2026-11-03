//! Lists of `orders` rows (row indices) and their counts per priority.
//!
//! `win_list(a, b)`: the rows of `[a, b)` in the date window, in row order; `q_list(a, b)`: the qualifying rows (in the
//! window and with a late `lineitem` row). `cnt_list(s, kb)`: how many rows of the list `s` have priority `kb`.
//! `key_filter(s, ks)`: the rows of `s` whose priority is in the set `ks` (used to merge group tables).
use vstd::prelude::*;
use crate::agent::cols::*;

verus! {

/// The date window on stored days: `dlo <= o_orderdate < dhi` (days since 1970-01-01).
#[derive(Clone, Copy)]
pub struct Win {
    pub dlo: i64,
    pub dhi: i64,
}

pub open spec fn in_win(o: OCols, w: Win, i: int) -> bool {
    w.dlo <= o.odate@[i] as int && (o.odate@[i] as int) < w.dhi
}

/// Order row `i` qualifies: in the window, and its key has a late `lineitem` row.
pub open spec fn qual_row(l: LCols, o: OCols, w: Win, i: int) -> bool {
    in_win(o, w, i) && has(l, o.okey@[i] as int)
}

/// The rows of `[a, b)` in the window, in row order.
pub open spec fn win_list(o: OCols, w: Win, a: int, b: int) -> Seq<usize>
    decreases b - a,
{
    if b <= a {
        Seq::empty()
    } else {
        let d = win_list(o, w, a, b - 1);
        if in_win(o, w, b - 1) { d.push((b - 1) as usize) } else { d }
    }
}

/// The qualifying rows of `[a, b)`, in row order.
pub open spec fn q_list(l: LCols, o: OCols, w: Win, a: int, b: int) -> Seq<usize>
    decreases b - a,
{
    if b <= a {
        Seq::empty()
    } else {
        let d = q_list(l, o, w, a, b - 1);
        if qual_row(l, o, w, b - 1) { d.push((b - 1) as usize) } else { d }
    }
}

/// The rows of `s` whose key has a late `lineitem` row.
pub open spec fn has_filter(l: LCols, o: OCols, s: Seq<usize>) -> Seq<usize>
    decreases s.len(),
{
    if s.len() == 0 {
        s
    } else {
        let d = has_filter(l, o, s.drop_last());
        if has(l, o.okey@[s.last() as int] as int) { d.push(s.last()) } else { d }
    }
}

/// The number of rows of `s` with priority `kb`.
pub open spec fn cnt_list(o: OCols, s: Seq<usize>, kb: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        cnt_list(o, s.drop_last(), kb) + if prio(o, s.last() as int) == kb { 1nat } else { 0nat }
    }
}

/// The rows of `s` whose priority is in `ks`.
pub open spec fn key_filter(o: OCols, s: Seq<usize>, ks: spec_fn(Seq<u8>) -> bool) -> Seq<usize>
    decreases s.len(),
{
    if s.len() == 0 {
        s
    } else {
        let d = key_filter(o, s.drop_last(), ks);
        if ks(prio(o, s.last() as int)) { d.push(s.last()) } else { d }
    }
}

/// Elements of `s` lie in `[a, b)`.
pub open spec fn within(s: Seq<usize>, a: int, b: int) -> bool {
    forall|m: int| 0 <= m < s.len() ==> a <= #[trigger] s[m] < b
}

/// One more row at the end of a window list.
pub proof fn lemma_win_list_step(o: OCols, w: Win, a: int, b: int)
    requires a <= b,
    ensures win_list(o, w, a, b + 1) == if in_win(o, w, b) { win_list(o, w, a, b).push(b as usize) } else { win_list(o, w, a, b) },
{
}

/// Window lists: rows in `[a, b)`, at most `b - a` of them, all in the window.
pub proof fn lemma_win_list(o: OCols, w: Win, a: int, b: int)
    requires 0 <= a <= b <= usize::MAX,
    ensures
        within(win_list(o, w, a, b), a, b),
        win_list(o, w, a, b).len() <= b - a,
        forall|m: int| 0 <= m < win_list(o, w, a, b).len() ==> in_win(o, w, #[trigger] win_list(o, w, a, b)[m] as int),
    decreases b - a,
{
    if a < b {
        lemma_win_list(o, w, a, b - 1);
        let d = win_list(o, w, a, b - 1);
        let s = win_list(o, w, a, b);
        assert forall|m: int| 0 <= m < s.len() implies a <= #[trigger] s[m] < b && in_win(o, w, s[m] as int) by {
            if m < d.len() {
                assert(s[m] == d[m]);
            } else {
                assert(s[m] == (b - 1) as usize);
            }
        }
    }
}

/// Qualifying lists: rows in `[a, b)`, at most `b - a` of them, all qualifying.
pub proof fn lemma_q_list(l: LCols, o: OCols, w: Win, a: int, b: int)
    requires 0 <= a <= b <= usize::MAX,
    ensures
        within(q_list(l, o, w, a, b), a, b),
        q_list(l, o, w, a, b).len() <= b - a,
        forall|m: int| 0 <= m < q_list(l, o, w, a, b).len() ==> qual_row(l, o, w, #[trigger] q_list(l, o, w, a, b)[m] as int),
    decreases b - a,
{
    if a < b {
        lemma_q_list(l, o, w, a, b - 1);
        let d = q_list(l, o, w, a, b - 1);
        let s = q_list(l, o, w, a, b);
        assert forall|m: int| 0 <= m < s.len() implies a <= #[trigger] s[m] < b && qual_row(l, o, w, s[m] as int) by {
            if m < d.len() {
                assert(s[m] == d[m]);
            } else {
                assert(s[m] == (b - 1) as usize);
            }
        }
    }
}

/// Keeping the rows of a window list whose key has a late row gives the qualifying list.
pub proof fn lemma_q_list_filter(l: LCols, o: OCols, w: Win, a: int, b: int)
    requires 0 <= a <= b <= usize::MAX,
    ensures has_filter(l, o, win_list(o, w, a, b)) == q_list(l, o, w, a, b),
    decreases b - a,
{
    if a < b {
        lemma_q_list_filter(l, o, w, a, b - 1);
        let d = win_list(o, w, a, b - 1);
        if in_win(o, w, b - 1) {
            lemma_has_filter_push(l, o, d, (b - 1) as usize);
            assert(o.okey@[((b - 1) as usize) as int] == o.okey@[b - 1]);
        }
    } else {
        assert(win_list(o, w, a, b) == Seq::<usize>::empty());
    }
}

/// `has_filter` of a list with one more element.
pub proof fn lemma_has_filter_push(l: LCols, o: OCols, s: Seq<usize>, r: usize)
    ensures has_filter(l, o, s.push(r)) == if has(l, o.okey@[r as int] as int) { has_filter(l, o, s).push(r) } else { has_filter(l, o, s) },
{
    assert(s.push(r).drop_last() =~= s);
}

/// Qualifying lists of adjacent ranges concatenate.
pub proof fn lemma_q_list_split(l: LCols, o: OCols, w: Win, a: int, b: int, c: int)
    requires a <= b <= c,
    ensures q_list(l, o, w, a, c) == q_list(l, o, w, a, b) + q_list(l, o, w, b, c),
    decreases c - b,
{
    if b < c {
        lemma_q_list_split(l, o, w, a, b, c - 1);
        let x = q_list(l, o, w, a, b);
        let y = q_list(l, o, w, b, c - 1);
        if qual_row(l, o, w, c - 1) {
            assert((x + y).push((c - 1) as usize) =~= x + y.push((c - 1) as usize));
        }
    } else {
        assert(q_list(l, o, w, b, c) =~= Seq::<usize>::empty());
        assert(q_list(l, o, w, a, b) + Seq::<usize>::empty() =~= q_list(l, o, w, a, b));
    }
}

/// Counts add over concatenation.
pub proof fn lemma_cnt_append(o: OCols, s: Seq<usize>, t: Seq<usize>, kb: Seq<u8>)
    ensures cnt_list(o, s + t, kb) == cnt_list(o, s, kb) + cnt_list(o, t, kb),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(s + t =~= s);
    } else {
        lemma_cnt_append(o, s, t.drop_last(), kb);
        assert((s + t).drop_last() =~= s + t.drop_last());
        assert((s + t).last() == t.last());
    }
}

/// One more element.
pub proof fn lemma_cnt_push(o: OCols, s: Seq<usize>, r: usize, kb: Seq<u8>)
    ensures cnt_list(o, s.push(r), kb) == cnt_list(o, s, kb) + if prio(o, r as int) == kb { 1nat } else { 0nat },
{
    assert(s.push(r).drop_last() =~= s);
}

/// A count is at most the length of the list.
pub proof fn lemma_cnt_le(o: OCols, s: Seq<usize>, kb: Seq<u8>)
    ensures cnt_list(o, s, kb) <= s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_cnt_le(o, s.drop_last(), kb);
    }
}

/// A positive count has a witness row.
pub proof fn lemma_cnt_witness(o: OCols, s: Seq<usize>, kb: Seq<u8>)
    requires cnt_list(o, s, kb) > 0,
    ensures exists|m: int| 0 <= m < s.len() && prio(o, #[trigger] s[m] as int) == kb,
    decreases s.len(),
{
    if prio(o, s.last() as int) == kb {
        assert(prio(o, s[s.len() - 1] as int) == kb);
    } else {
        lemma_cnt_witness(o, s.drop_last(), kb);
        let m = choose|m: int| 0 <= m < s.drop_last().len() && prio(o, #[trigger] s.drop_last()[m] as int) == kb;
        assert(s[m] == s.drop_last()[m]);
    }
}

/// A row of the list with priority `kb` gives a positive count.
pub proof fn lemma_cnt_pos(o: OCols, s: Seq<usize>, m: int, kb: Seq<u8>)
    requires 0 <= m < s.len(), prio(o, s[m] as int) == kb,
    ensures cnt_list(o, s, kb) > 0,
    decreases s.len(),
{
    if m < s.len() - 1 {
        assert(s.drop_last()[m] == s[m]);
        lemma_cnt_pos(o, s.drop_last(), m, kb);
    }
}

/// The count of a key filter: the full count for keys of the set, zero otherwise.
pub proof fn lemma_cnt_key_filter(o: OCols, s: Seq<usize>, ks: spec_fn(Seq<u8>) -> bool, kb: Seq<u8>)
    ensures cnt_list(o, key_filter(o, s, ks), kb) == if ks(kb) { cnt_list(o, s, kb) } else { 0 },
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_cnt_key_filter(o, s.drop_last(), ks, kb);
        let d = key_filter(o, s.drop_last(), ks);
        if ks(prio(o, s.last() as int)) {
            lemma_cnt_push(o, d, s.last(), kb);
        }
    }
}

/// Membership in a key filter.
pub proof fn lemma_key_filter_contains(o: OCols, s: Seq<usize>, ks: spec_fn(Seq<u8>) -> bool, r: usize)
    ensures key_filter(o, s, ks).contains(r) == (s.contains(r) && ks(prio(o, r as int))),
    decreases s.len(),
{
    if s.len() > 0 {
        let d = key_filter(o, s.drop_last(), ks);
        lemma_key_filter_contains(o, s.drop_last(), ks, r);
        let f = key_filter(o, s, ks);
        if f.contains(r) {
            let m = choose|m: int| 0 <= m < f.len() && f[m] == r;
            if ks(prio(o, s.last() as int)) && m == d.len() {
                assert(s[s.len() - 1] == r);
            } else {
                assert(d[m] == r);
                let x = choose|x: int| 0 <= x < s.drop_last().len() && s.drop_last()[x] == r;
                assert(s[x] == r);
            }
        }
        if s.contains(r) && ks(prio(o, r as int)) {
            let m = choose|m: int| 0 <= m < s.len() && s[m] == r;
            if m == s.len() - 1 {
                assert(f[d.len() as int] == r);
            } else {
                assert(s.drop_last()[m] == r);
                let x = choose|x: int| 0 <= x < d.len() && d[x] == r;
                assert(f[x] == r);
            }
        }
    } else {
        assert(!key_filter(o, s, ks).contains(r));
    }
}

/// A key filter that keeps every key of the list is the list.
pub proof fn lemma_key_filter_all(o: OCols, s: Seq<usize>, ks: spec_fn(Seq<u8>) -> bool)
    requires forall|m: int| 0 <= m < s.len() ==> ks(prio(o, #[trigger] s[m] as int)),
    ensures key_filter(o, s, ks) == s,
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        assert forall|m: int| 0 <= m < d.len() implies ks(prio(o, #[trigger] d[m] as int)) by {
            assert(d[m] == s[m]);
        }
        lemma_key_filter_all(o, d, ks);
        assert(ks(prio(o, s[s.len() - 1] as int)));
        assert(d.push(s.last()) =~= s);
    }
}

/// The empty key set keeps nothing.
pub proof fn lemma_key_filter_none(o: OCols, s: Seq<usize>)
    ensures key_filter(o, s, |kb: Seq<u8>| false) == Seq::<usize>::empty(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_key_filter_none(o, s.drop_last());
    }
}

} // verus!
