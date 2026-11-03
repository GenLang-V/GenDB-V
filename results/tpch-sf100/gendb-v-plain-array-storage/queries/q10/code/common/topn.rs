//! A top-N selection of candidates by value, descending: a fixed-capacity buffer kept sorted by sorted insertion
//! (`Top`, `top_offer`), and the merge law of top-N lists of disjoint candidate sets (`lemma_top_merge`).
//!
//! Candidates are distinct ids (`int`) offered one at a time with their values `vf(id)`; after the ids `s` have been
//! offered, the buffer holds a top-N of `s` (`top_of`): `min(N, |s|)` distinct ids of `s`, values not increasing,
//! and no other id of `s` with a larger value than the last one. Ties at the boundary may go either way.
use vstd::prelude::*;
use vstd::set_lib::{lemma_len_subset, lemma_subset_equality};

verus! {

// ------------------------------------------------------------------------------------------------ specifications

/// `sel` is a top-`cap` of the distinct candidates `s` by `vf`.
pub open spec fn top_of(sel: Seq<int>, s: Seq<int>, vf: spec_fn(int) -> int, cap: int) -> bool {
    &&& sel.no_duplicates()
    &&& forall|i: int| 0 <= i < sel.len() ==> s.contains(#[trigger] sel[i])
    &&& sel.len() == if s.len() <= cap { s.len() as int } else { cap }
    &&& forall|i: int, j: int| 0 <= i < j < sel.len() ==> vf(#[trigger] sel[i]) >= vf(#[trigger] sel[j])
    &&& sel.len() > 0 ==> forall|x: int| #[trigger] s.contains(x) && !sel.contains(x) ==> vf(x) <= vf(sel.last())
}

/// The buffer: `rows[0..k)` with their values `vals[0..k)`, capacity `cap`.
pub struct Top {
    pub rows: Vec<usize>,
    pub vals: Vec<i128>,
    pub k: usize,
    pub cap: usize,
}

/// The selected ids of the buffer.
pub open spec fn tsel(t: Top) -> Seq<int> {
    Seq::new(t.k as nat, |i: int| t.rows@[i] as int)
}

/// The buffer holds a top-`cap` of the offered distinct candidates `s`, with their values.
pub open spec fn top_inv(t: Top, s: Seq<int>, vf: spec_fn(int) -> int) -> bool {
    &&& 1 <= t.cap && t.rows@.len() == t.cap && t.vals@.len() == t.cap && t.k <= t.cap
    &&& forall|i: int| 0 <= i < t.k ==> #[trigger] t.vals@[i] as int == vf(t.rows@[i] as int)
    &&& s.no_duplicates()
    &&& top_of(tsel(t), s, vf, t.cap as int)
}

// ------------------------------------------------------------------------------------------------ the buffer

/// An empty buffer of capacity `cap` (calling thread: allocates).
pub fn top_new(cap: usize, Ghost(vf): Ghost<spec_fn(int) -> int>) -> (t: Top)
    requires cap >= 1,
    ensures top_inv(t, Seq::empty(), vf), t.cap == cap,
{
    let t = Top { rows: vec![0usize; cap], vals: vec![0i128; cap], k: 0, cap };
    proof {
        assert(tsel(t) =~= Seq::<int>::empty());
    }
    t
}

/// The sequence with `x` inserted at position `pos`.
proof fn lemma_insert_props(base: Seq<int>, pos: int, x: int)
    requires 0 <= pos <= base.len(),
    ensures
        base.insert(pos, x).len() == base.len() + 1,
        forall|i: int| 0 <= i < pos ==> #[trigger] base.insert(pos, x)[i] == base[i],
        base.insert(pos, x)[pos] == x,
        forall|i: int| pos < i <= base.len() ==> #[trigger] base.insert(pos, x)[i] == base[i - 1],
{
}

/// Offering a candidate that does not enter a full buffer keeps it a top-`cap` list.
proof fn lemma_offer_skip(sel: Seq<int>, s: Seq<int>, vf: spec_fn(int) -> int, cap: int, x: int)
    requires
        top_of(sel, s, vf, cap), s.no_duplicates(), !s.contains(x), 1 <= cap, sel.len() == cap,
        vf(x) <= vf(sel[cap - 1]),
    ensures top_of(sel, s.push(x), vf, cap), s.push(x).no_duplicates(),
{
    let s2 = s.push(x);
    assert forall|i: int| 0 <= i < sel.len() implies s2.contains(#[trigger] sel[i]) by {
        assert(s.contains(sel[i]));
        let j = choose|j: int| 0 <= j < s.len() && s[j] == sel[i];
        assert(s2[j] == sel[i]);
    }
    assert forall|y: int| #[trigger] s2.contains(y) && !sel.contains(y) implies vf(y) <= vf(sel.last()) by {
        if y != x {
            let j = choose|j: int| 0 <= j < s2.len() && s2[j] == y;
            assert(s[j] == y);
            assert(s.contains(y));
        }
    }
    assert forall|a: int, b: int| 0 <= a < s2.len() && 0 <= b < s2.len() && a != b implies s2[a] != s2[b] by {
        if a == s.len() { assert(s.contains(s2[b])); } else if b == s.len() { assert(s.contains(s2[a])); }
    }
}

/// The ids kept below `pos` are not below `v`, those from `pos` on are below it (the list is sorted).
proof fn lemma_pos_split(sel: Seq<int>, vf: spec_fn(int) -> int, v: int, kk: int, pos: int)
    requires
        0 <= pos <= kk <= sel.len(),
        forall|i: int, j: int| 0 <= i < j < sel.len() ==> vf(#[trigger] sel[i]) >= vf(#[trigger] sel[j]),
        forall|j: int| 0 <= j < pos ==> vf(#[trigger] sel[j]) >= v,
        pos < kk ==> vf(sel[pos]) < v,
    ensures forall|j: int| pos <= j < kk ==> vf(#[trigger] sel[j]) < v,
{
    assert forall|j: int| pos <= j < kk implies vf(#[trigger] sel[j]) < v by {
        if j > pos { assert(vf(sel[pos]) >= vf(sel[j])); }
    }
}

/// The inserted list: `ns[j]` is `sel[j]` below `pos`, `x` at `pos`, `sel[j - 1]` above.
pub open spec fn ins_at(sel: Seq<int>, kk: int, pos: int, x: int) -> Seq<int> { sel.subrange(0, kk).insert(pos, x) }

proof fn lemma_ins_index(sel: Seq<int>, kk: int, pos: int, x: int)
    requires 0 <= pos <= kk <= sel.len(),
    ensures
        ins_at(sel, kk, pos, x).len() == kk + 1,
        forall|j: int| 0 <= j < pos ==> #[trigger] ins_at(sel, kk, pos, x)[j] == sel[j],
        ins_at(sel, kk, pos, x)[pos] == x,
        forall|j: int| pos < j <= kk ==> #[trigger] ins_at(sel, kk, pos, x)[j] == sel[j - 1],
{
    lemma_insert_props(sel.subrange(0, kk), pos, x);
}

proof fn lemma_ins_nodup(sel: Seq<int>, s: Seq<int>, x: int, kk: int, pos: int)
    requires sel.no_duplicates(), !s.contains(x), forall|i: int| 0 <= i < sel.len() ==> s.contains(#[trigger] sel[i]),
        0 <= pos <= kk <= sel.len(),
    ensures ins_at(sel, kk, pos, x).no_duplicates(),
{
    let ns = ins_at(sel, kk, pos, x);
    lemma_ins_index(sel, kk, pos, x);
    assert forall|a: int, b: int| 0 <= a < ns.len() && 0 <= b < ns.len() && a != b implies ns[a] != ns[b] by {
        let aa = if a < pos { a } else { a - 1 };
        let bb = if b < pos { b } else { b - 1 };
        if a == pos {
            assert(ns[b] == sel[bb]);
            assert(s.contains(sel[bb]));
        } else if b == pos {
            assert(ns[a] == sel[aa]);
            assert(s.contains(sel[aa]));
        } else {
            assert(ns[a] == sel[aa] && ns[b] == sel[bb]);
        }
    }
}

proof fn lemma_ins_in(sel: Seq<int>, s: Seq<int>, x: int, kk: int, pos: int)
    requires forall|i: int| 0 <= i < sel.len() ==> s.contains(#[trigger] sel[i]), 0 <= pos <= kk <= sel.len(),
    ensures forall|j: int| 0 <= j < kk + 1 ==> s.push(x).contains(#[trigger] ins_at(sel, kk, pos, x)[j]),
{
    let ns = ins_at(sel, kk, pos, x);
    let s2 = s.push(x);
    lemma_ins_index(sel, kk, pos, x);
    assert forall|j: int| 0 <= j < kk + 1 implies s2.contains(#[trigger] ns[j]) by {
        if j == pos {
            assert(s2[s.len() as int] == x);
        } else {
            let jj = if j < pos { j } else { j - 1 };
            assert(ns[j] == sel[jj]);
            assert(s.contains(sel[jj]));
            let q = choose|q: int| 0 <= q < s.len() && s[q] == sel[jj];
            assert(s2[q] == sel[jj]);
        }
    }
}

proof fn lemma_ins_sorted(sel: Seq<int>, vf: spec_fn(int) -> int, x: int, kk: int, pos: int)
    requires
        0 <= pos <= kk <= sel.len(),
        forall|i: int, j: int| 0 <= i < j < sel.len() ==> vf(#[trigger] sel[i]) >= vf(#[trigger] sel[j]),
        forall|j: int| 0 <= j < pos ==> vf(#[trigger] sel[j]) >= vf(x),
        forall|j: int| pos <= j < kk ==> vf(#[trigger] sel[j]) < vf(x),
    ensures forall|a: int, b: int| 0 <= a < b < kk + 1 ==> vf(#[trigger] ins_at(sel, kk, pos, x)[a]) >= vf(#[trigger] ins_at(sel, kk, pos, x)[b]),
{
    let ns = ins_at(sel, kk, pos, x);
    lemma_ins_index(sel, kk, pos, x);
    assert forall|a: int, b: int| 0 <= a < b < kk + 1 implies vf(#[trigger] ns[a]) >= vf(#[trigger] ns[b]) by {
        if a == pos {
            assert(ns[b] == sel[b - 1]);
        } else if b == pos {
            assert(ns[a] == sel[a]);
        } else {
            let aa = if a < pos { a } else { a - 1 };
            let bb = if b < pos { b } else { b - 1 };
            assert(ns[a] == sel[aa] && ns[b] == sel[bb]);
        }
    }
}

/// Inserting a candidate at its sorted place among the kept ids (all, or all but the last of a full buffer) gives a
/// top-`cap` list of the offered ids.
proof fn lemma_insert_top(sel: Seq<int>, s: Seq<int>, vf: spec_fn(int) -> int, cap: int, x: int, kk: int, pos: int)
    requires
        top_of(sel, s, vf, cap), s.no_duplicates(), !s.contains(x), 1 <= cap,
        kk == if sel.len() < cap { sel.len() as int } else { cap - 1 },
        sel.len() == cap ==> vf(x) > vf(sel[cap - 1]),
        0 <= pos <= kk,
        forall|j: int| 0 <= j < pos ==> vf(#[trigger] sel[j]) >= vf(x),
        forall|j: int| pos <= j < kk ==> vf(#[trigger] sel[j]) < vf(x),
    ensures
        top_of(ins_at(sel, kk, pos, x), s.push(x), vf, cap),
        s.push(x).no_duplicates(),
{
    let s2 = s.push(x);
    let ns = ins_at(sel, kk, pos, x);
    lemma_ins_index(sel, kk, pos, x);
    lemma_ins_nodup(sel, s, x, kk, pos);
    lemma_ins_in(sel, s, x, kk, pos);
    lemma_ins_sorted(sel, vf, x, kk, pos);
    if sel.len() < cap {
        lemma_sel_all(sel, s);
    }
    assert forall|y: int| #[trigger] s2.contains(y) && !ns.contains(y) implies vf(y) <= vf(ns.last()) by {
        if y == x {
            assert(ns[pos] == y);
        } else {
            let q = choose|q: int| 0 <= q < s2.len() && s2[q] == y;
            assert(s[q] == y);
            assert(s.contains(y));
            if sel.len() < cap {
                assert(sel.contains(y));
                let jy = choose|jy: int| 0 <= jy < sel.len() && sel[jy] == y;
                let jn = if jy < pos { jy } else { jy + 1 };
                assert(ns[jn] == y);
            } else {
                // full buffer: y is the dropped last id or was already below it
                let last_old = sel[cap - 1];
                assert(vf(y) <= vf(last_old)) by {
                    if sel.contains(y) {
                        let jy = choose|jy: int| 0 <= jy < sel.len() && sel[jy] == y;
                        if jy < kk {
                            let jn = if jy < pos { jy } else { jy + 1 };
                            assert(ns[jn] == y);
                        }
                    } else {
                        assert(sel.last() == last_old);
                    }
                }
                if pos < kk {
                    assert(ns.last() == sel[kk - 1]);
                    assert(vf(sel[kk - 1]) >= vf(sel[kk]));
                } else {
                    assert(ns.last() == x);
                }
            }
        }
    }
    assert forall|a: int, b: int| 0 <= a < s2.len() && 0 <= b < s2.len() && a != b implies s2[a] != s2[b] by {
        if a == s.len() { assert(s.contains(s2[b])); } else if b == s.len() { assert(s.contains(s2[a])); }
    }
}

/// A top list shorter than the capacity holds every offered id.
proof fn lemma_sel_all(sel: Seq<int>, s: Seq<int>)
    requires sel.no_duplicates(), s.no_duplicates(), sel.len() == s.len(),
        forall|i: int| 0 <= i < sel.len() ==> s.contains(#[trigger] sel[i]),
    ensures forall|y: int| #[trigger] s.contains(y) ==> sel.contains(y),
{
    lemma_sub_len(sel, s);
}

/// Offers candidate `x` with value `v` (= `vf(x)`, not offered before).
pub fn top_offer(t: &mut Top, x: usize, v: i128, Ghost(s): Ghost<Seq<int>>, Ghost(vf): Ghost<spec_fn(int) -> int>)
    requires top_inv(*old(t), s, vf), vf(x as int) == v, !s.contains(x as int),
    ensures
        top_inv(*final(t), s.push(x as int), vf), final(t).cap == old(t).cap,
        old(t).k == old(t).cap ==> final(t).k == final(t).cap && final(t).vals@[final(t).cap - 1] >= old(t).vals@[old(t).cap - 1],
    no_unwind
{
    let ghost old_sel = tsel(*t);
    let cap = t.cap;
    let k = t.k;
    assert(t.rows@.len() == cap && t.vals@.len() == cap);
    if k == cap && v <= t.vals[k - 1] {
        proof {
            lemma_offer_skip(old_sel, s, vf, cap as int, x as int);
        }
        return;
    }
    // kept: the first `kk` selected ids (all of them, or all but the last when the buffer is full)
    let kk = if k < cap { k } else { cap - 1 };
    // pos: the number of kept ids with a value at least v
    let mut pos: usize = 0;
    while pos < kk && t.vals[pos] >= v
        invariant
            pos <= kk < cap, t.rows@.len() == cap, t.vals@.len() == cap, kk <= t.k,
            forall|i: int| 0 <= i < pos ==> t.vals@[i] >= v,
        decreases kk - pos,
    {
        pos = pos + 1;
    }
    let ghost rows0 = t.rows@;
    let ghost vals0 = t.vals@;
    proof {
        assert forall|j: int| 0 <= j < pos implies vf(#[trigger] old_sel[j]) >= v by {
            assert(vals0[j] as int == vf(rows0[j] as int));
        }
        if pos < kk {
            assert(vals0[pos as int] as int == vf(rows0[pos as int] as int));
        }
        lemma_pos_split(old_sel, vf, v as int, kk as int, pos as int);
    }
    // shift the kept ids at pos.. up by one
    let mut i: usize = kk;
    while i > pos
        invariant
            pos <= i <= kk < cap, t.rows@.len() == cap, t.vals@.len() == cap, t.k == k, t.cap == cap,
            forall|j: int| 0 <= j < i ==> #[trigger] t.rows@[j] == rows0[j],
            forall|j: int| 0 <= j < i ==> #[trigger] t.vals@[j] == vals0[j],
            forall|j: int| i < j <= kk ==> #[trigger] t.rows@[j] == rows0[j - 1],
            forall|j: int| i < j <= kk ==> #[trigger] t.vals@[j] == vals0[j - 1],
        decreases i,
    {
        let r = t.rows[i - 1];
        let w = t.vals[i - 1];
        t.rows[i] = r;
        t.vals[i] = w;
        i = i - 1;
    }
    t.rows[pos] = x;
    t.vals[pos] = v;
    if k < cap {
        t.k = k + 1;
    }
    proof {
        let ins = ins_at(old_sel, kk as int, pos as int, x as int);
        lemma_ins_index(old_sel, kk as int, pos as int, x as int);
        assert(tsel(*t) =~= ins) by {
            assert forall|j: int| 0 <= j < ins.len() implies tsel(*t)[j] == ins[j] by {
                if j < pos { assert(t.rows@[j] == rows0[j]); } else if j > pos { assert(t.rows@[j] == rows0[j - 1]); }
            }
        }
        assert forall|j: int| 0 <= j < t.k implies #[trigger] t.vals@[j] as int == vf(t.rows@[j] as int) by {
            if j > pos as int { assert(vals0[j - 1] as int == vf(rows0[j - 1] as int)); }
            if j < pos as int { assert(vals0[j] as int == vf(rows0[j] as int)); }
        }
        if k == cap {
            assert(vals0[k - 1] as int == vf(rows0[k - 1] as int));
            if pos < kk {
                assert(t.vals@[cap - 1] == vals0[cap - 2]);
                assert(vals0[cap - 2] as int == vf(rows0[cap - 2] as int));
                assert(vf(old_sel[cap - 2]) >= vf(old_sel[cap - 1]));
            }
        }
        lemma_insert_top(old_sel, s, vf, cap as int, x as int, kk as int, pos as int);
    }
}

// ------------------------------------------------------------------------------------------------ merging

/// A sub-sequence without duplicates of a sequence without duplicates is no longer; equal lengths make them hold
/// the same ids.
pub proof fn lemma_sub_len(a: Seq<int>, b: Seq<int>)
    requires a.no_duplicates(), b.no_duplicates(), forall|i: int| 0 <= i < a.len() ==> b.contains(#[trigger] a[i]),
    ensures
        a.len() <= b.len(),
        a.len() == b.len() ==> forall|x: int| #[trigger] b.contains(x) ==> a.contains(x),
{
    assert(a.to_set().subset_of(b.to_set())) by {
        assert forall|z: int| a.to_set().contains(z) implies b.to_set().contains(z) by {
            let q = choose|q: int| 0 <= q < a.len() && a[q] == z;
        }
    }
    a.unique_seq_to_set();
    b.unique_seq_to_set();
    lemma_len_subset(a.to_set(), b.to_set());
    if a.len() == b.len() {
        lemma_subset_equality(a.to_set(), b.to_set());
        assert forall|x: int| #[trigger] b.contains(x) implies a.contains(x) by {
            assert(b.to_set().contains(x));
        }
    }
}

/// Merging: `sel` is a top-`cap` of `c`, every id of `c` lies in `g`, and for each id `y` of `g` outside `c` there
/// is a top-`cap` list `l` (inside `c`) of a part of `g` holding `y` and `cap` ids not below it. Then `sel` is a
/// top-`cap` of `g`, given that `c` holds all of `g` when `g` has fewer than `cap` ids outside the parts' lists.
pub proof fn lemma_top_merge(sel: Seq<int>, c: Seq<int>, g: Seq<int>, vf: spec_fn(int) -> int, cap: int)
    requires
        cap >= 1,
        c.no_duplicates(), g.no_duplicates(),
        top_of(sel, c, vf, cap),
        forall|y: int| #[trigger] c.contains(y) ==> g.contains(y),
        // an id of g outside c is dominated by cap ids of c
        forall|y: int| #[trigger] g.contains(y) && !c.contains(y) ==> exists|l: Seq<int>| #[trigger] dominated(l, y, c, vf, cap),
    ensures
        top_of(sel, g, vf, cap),
{
    // sizes
    assert forall|i: int| 0 <= i < c.len() implies g.contains(#[trigger] c[i]) by {
        assert(c.contains(c[i]));
    }
    lemma_sub_len(c, g);
    if c.len() < g.len() {
        // some id of g is outside c: its dominating list puts cap ids into c
        assert(exists|y: int| #[trigger] g.contains(y) && !c.contains(y)) by {
            if forall|y: int| #[trigger] g.contains(y) ==> c.contains(y) {
                assert forall|i: int| 0 <= i < g.len() implies c.contains(#[trigger] g[i]) by {
                    assert(g.contains(g[i]));
                }
                lemma_sub_len(g, c);
            }
        }
        let y = choose|y: int| #[trigger] g.contains(y) && !c.contains(y);
        let l = choose|l: Seq<int>| #[trigger] dominated(l, y, c, vf, cap);
        lemma_sub_len(l, c);
        assert(sel.len() == cap);
    }
    assert forall|i: int| 0 <= i < sel.len() implies g.contains(#[trigger] sel[i]) by {
        assert(c.contains(sel[i]));
    }
    if sel.len() > 0 {
        assert forall|y: int| #[trigger] g.contains(y) && !sel.contains(y) implies vf(y) <= vf(sel.last()) by {
            if !c.contains(y) && vf(y) > vf(sel.last()) {
                let l = choose|l: Seq<int>| #[trigger] dominated(l, y, c, vf, cap);
                // every id of l is above the last selected one, so it is selected
                assert forall|i: int| 0 <= i < l.len() implies sel.contains(#[trigger] l[i]) by {
                    assert(vf(l[i]) >= vf(y));
                    assert(c.contains(l[i]));
                }
                lemma_sub_len(l, c);
                assert(sel.len() == cap);
                lemma_sub_len(l, sel);
                // so sel holds exactly l's ids, and its last one is not below y
                assert(sel.contains(sel.last()));
                assert(l.contains(sel.last()));
                let j = choose|j: int| 0 <= j < l.len() && l[j] == sel.last();
                assert(vf(l[j]) >= vf(y));
            }
        }
    }
}

/// `l` holds `cap` distinct ids of `c`, none below `y`.
pub open spec fn dominated(l: Seq<int>, y: int, c: Seq<int>, vf: spec_fn(int) -> int, cap: int) -> bool {
    &&& l.no_duplicates()
    &&& l.len() == cap
    &&& forall|i: int| 0 <= i < l.len() ==> c.contains(#[trigger] l[i]) && vf(l[i]) >= vf(y)
}

/// A full top-`cap` list of a part dominates every id of the part it does not hold.
pub proof fn lemma_dominated(sel: Seq<int>, part: Seq<int>, c: Seq<int>, y: int, vf: spec_fn(int) -> int, cap: int)
    requires
        top_of(sel, part, vf, cap), part.contains(y), !sel.contains(y),
        forall|i: int| 0 <= i < sel.len() ==> c.contains(#[trigger] sel[i]),
        part.no_duplicates(),
    ensures dominated(sel, y, c, vf, cap),
{
    lemma_sub_len(sel, part);
    if sel.len() < cap {
        assert(sel.len() == part.len());
        assert(sel.contains(y));
    }
    assert forall|i: int| 0 <= i < sel.len() implies c.contains(#[trigger] sel[i]) && vf(sel[i]) >= vf(y) by {
        assert(vf(y) <= vf(sel.last()));
        if i < sel.len() - 1 { assert(vf(sel[i]) >= vf(sel[sel.len() - 1])); }
    }
}

} // verus!
