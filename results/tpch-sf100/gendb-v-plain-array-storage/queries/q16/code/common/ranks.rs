//! Ranks of distinct values: the rank of value `i` is the number of values below it (`rank_of`, by byte order for
//! texts, numerically for integers). Distinct values have distinct ranks below their number, and a smaller value has
//! a smaller rank (`lemma_rank_order`), so comparing ranks compares values. Ranks are counted by a double loop
//! (meant for small value lists such as dictionary keys).
use vstd::prelude::*;
use vstd::set_lib::set_int_range;
use crate::spec::text::lex_cmp;
use crate::bridge::order::{lemma_lex_cmp_antisym, lemma_lex_cmp_trans};
use crate::bridge::equality::lemma_lex_cmp_zero;

verus! {

/// Byte order on two texts as a strict "less than".
pub open spec fn text_lt(a: Seq<u8>, b: Seq<u8>) -> bool { lex_cmp(a, b) < 0 }

/// The positions of the texts below text `i`.
pub open spec fn below_texts(keys: Seq<Seq<u8>>, i: int) -> Set<int> {
    set_int_range(0, keys.len() as int).filter(|j: int| text_lt(keys[j], keys[i]))
}

/// The positions of the integers below integer `i`.
pub open spec fn below_ints(vs: Seq<i64>, i: int) -> Set<int> {
    set_int_range(0, vs.len() as int).filter(|j: int| vs[j] < vs[i])
}

/// Distinct texts / integers.
pub open spec fn distinct_texts(keys: Seq<Seq<u8>>) -> bool {
    forall|i: int, j: int| 0 <= i < keys.len() && 0 <= j < keys.len() && i != j ==> keys[i] != keys[j]
}

pub open spec fn distinct_ints(vs: Seq<i64>) -> bool {
    forall|i: int, j: int| 0 <= i < vs.len() && 0 <= j < vs.len() && i != j ==> vs[i] != vs[j]
}

/// `lex_cmp` after a common prefix of `i` bytes.
proof fn lemma_lex_cmp_skip(a: Seq<u8>, b: Seq<u8>, i: int)
    requires 0 <= i <= a.len(), i <= b.len(), forall|k: int| 0 <= k < i ==> a[k] == b[k],
    ensures lex_cmp(a, b) == lex_cmp(a.subrange(i, a.len() as int), b.subrange(i, b.len() as int)),
    decreases i,
{
    if i > 0 {
        let (ta, tb) = (a.drop_first(), b.drop_first());
        assert forall|k: int| 0 <= k < i - 1 implies ta[k] == tb[k] by {
            assert(ta[k] == a[k + 1] && tb[k] == b[k + 1]);
        }
        lemma_lex_cmp_skip(ta, tb, i - 1);
        assert(ta.subrange(i - 1, ta.len() as int) =~= a.subrange(i, a.len() as int));
        assert(tb.subrange(i - 1, tb.len() as int) =~= b.subrange(i, b.len() as int));
        assert(a.len() > 0 && b.len() > 0 && a[0] == b[0]);
    } else {
        assert(a.subrange(0, a.len() as int) =~= a);
        assert(b.subrange(0, b.len() as int) =~= b);
    }
}

/// `lex_cmp` of `a[alo..ahi]` and `b[blo..bhi]`.
pub fn lex_cmp_exec(a: &Vec<u8>, alo: usize, ahi: usize, b: &Vec<u8>, blo: usize, bhi: usize) -> (r: i8)
    requires alo <= ahi <= a@.len(), blo <= bhi <= b@.len(),
    ensures r as int == lex_cmp(a@.subrange(alo as int, ahi as int), b@.subrange(blo as int, bhi as int)),
{
    let ghost sa = a@.subrange(alo as int, ahi as int);
    let ghost sb = b@.subrange(blo as int, bhi as int);
    let na = ahi - alo;
    let nb = bhi - blo;
    let mut i: usize = 0;
    while i < na && i < nb
        invariant
            na == sa.len(), nb == sb.len(), i <= na, i <= nb, alo <= ahi <= a@.len(), blo <= bhi <= b@.len(),
            na == ahi - alo, nb == bhi - blo,
            sa == a@.subrange(alo as int, ahi as int), sb == b@.subrange(blo as int, bhi as int),
            forall|k: int| 0 <= k < i ==> sa[k] == sb[k],
        decreases na - i,
    {
        let x = a[alo + i];
        let y = b[blo + i];
        proof { assert(sa[i as int] == x && sb[i as int] == y); }
        if x != y {
            proof {
                lemma_lex_cmp_skip(sa, sb, i as int);
                let (ra, rb) = (sa.subrange(i as int, na as int), sb.subrange(i as int, nb as int));
                assert(ra[0] == x && rb[0] == y);
            }
            return if x < y { -1 } else { 1 };
        }
        i = i + 1;
    }
    proof {
        lemma_lex_cmp_skip(sa, sb, i as int);
        let (ra, rb) = (sa.subrange(i as int, na as int), sb.subrange(i as int, nb as int));
        assert(ra.len() == 0 || rb.len() == 0);
    }
    if na < nb { -1 } else if na > nb { 1 } else { 0 }
}

/// A strictly smaller text has strictly fewer texts below it, and distinct texts differ in rank.
pub proof fn lemma_text_rank_order(keys: Seq<Seq<u8>>, i: int, j: int)
    requires distinct_texts(keys), 0 <= i < keys.len(), 0 <= j < keys.len(), text_lt(keys[i], keys[j]),
    ensures below_texts(keys, i).len() < below_texts(keys, j).len(),
{
    let (si, sj) = (below_texts(keys, i), below_texts(keys, j));
    vstd::set_lib::lemma_int_range(0, keys.len() as int);
    assert(si.subset_of(sj.remove(i))) by {
        assert forall|z: int| si.contains(z) implies sj.remove(i).contains(z) by {
            assert(text_lt(keys[z], keys[i]));
            lemma_lex_cmp_trans(keys[z], keys[i], keys[j]);
            lemma_lex_cmp_zero(keys[z], keys[j]);
            if keys[z] == keys[j] {
                lemma_lex_cmp_antisym(keys[i], keys[j]);
            }
            if z == i {
                lemma_lex_cmp_zero(keys[i], keys[i]);
            }
        }
    }
    assert(sj.contains(i));
    vstd::set_lib::lemma_len_subset(si, sj.remove(i));
}

/// Distinct texts have distinct ranks; ranks lie below the number of texts.
pub proof fn lemma_text_ranks(keys: Seq<Seq<u8>>, i: int, j: int)
    requires distinct_texts(keys), 0 <= i < keys.len(), 0 <= j < keys.len(),
    ensures
        below_texts(keys, i).len() < keys.len(),
        i != j ==> below_texts(keys, i).len() != below_texts(keys, j).len(),
        (below_texts(keys, i).len() < below_texts(keys, j).len()) == text_lt(keys[i], keys[j]),
{
    vstd::set_lib::lemma_int_range(0, keys.len() as int);
    let si = below_texts(keys, i);
    assert(si.subset_of(set_int_range(0, keys.len() as int).remove(i))) by {
        assert forall|z: int| si.contains(z) implies set_int_range(0, keys.len() as int).remove(i).contains(z) by {
            if z == i { lemma_lex_cmp_zero(keys[i], keys[i]); }
        }
    }
    vstd::set_lib::lemma_len_subset(si, set_int_range(0, keys.len() as int).remove(i));
    lemma_lex_cmp_antisym(keys[i], keys[j]);
    lemma_lex_cmp_zero(keys[i], keys[j]);
    if i != j {
        if text_lt(keys[i], keys[j]) { lemma_text_rank_order(keys, i, j); } else { lemma_text_rank_order(keys, j, i); }
    } else {
        lemma_lex_cmp_zero(keys[i], keys[i]);
    }
}

/// A smaller integer has fewer integers below it.
pub proof fn lemma_int_rank_order(vs: Seq<i64>, i: int, j: int)
    requires 0 <= i < vs.len(), 0 <= j < vs.len(), vs[i] < vs[j],
    ensures below_ints(vs, i).len() < below_ints(vs, j).len(),
{
    let (si, sj) = (below_ints(vs, i), below_ints(vs, j));
    vstd::set_lib::lemma_int_range(0, vs.len() as int);
    assert(si.subset_of(sj.remove(i)));
    assert(sj.contains(i));
    vstd::set_lib::lemma_len_subset(si, sj.remove(i));
}

/// Distinct integers have distinct ranks below their number, ordered as the integers.
pub proof fn lemma_int_ranks(vs: Seq<i64>, i: int, j: int)
    requires distinct_ints(vs), 0 <= i < vs.len(), 0 <= j < vs.len(),
    ensures
        below_ints(vs, i).len() < vs.len(),
        i != j ==> below_ints(vs, i).len() != below_ints(vs, j).len(),
        (below_ints(vs, i).len() < below_ints(vs, j).len()) == (vs[i] < vs[j]),
{
    vstd::set_lib::lemma_int_range(0, vs.len() as int);
    let si = below_ints(vs, i);
    assert(si.subset_of(set_int_range(0, vs.len() as int).remove(i)));
    vstd::set_lib::lemma_len_subset(si, set_int_range(0, vs.len() as int).remove(i));
    if i != j {
        if vs[i] < vs[j] { lemma_int_rank_order(vs, i, j); } else { lemma_int_rank_order(vs, j, i); }
    }
}

/// The ranks of byte strings held in `bytes` (key `i` at `bytes[off[i] .. off[i + 1]]`).
pub fn text_ranks(bytes: &Vec<u8>, off: &Vec<usize>, Ghost(keys): Ghost<Seq<Seq<u8>>>) -> (r: Vec<usize>)
    requires
        off@.len() == keys.len() + 1,
        forall|i: int| 0 <= i < keys.len() ==> off@[i] <= #[trigger] off@[i + 1] <= bytes@.len()
            && bytes@.subrange(off@[i] as int, off@[i + 1] as int) == keys[i],
    ensures r@.len() == keys.len(), forall|i: int| 0 <= i < keys.len() ==> #[trigger] r@[i] == below_texts(keys, i).len(),
{
    let n = off.len() - 1;
    let mut r: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == keys.len(), off@.len() == n + 1, i <= n, r@.len() == i,
            forall|x: int| 0 <= x < n ==> off@[x] <= #[trigger] off@[x + 1] <= bytes@.len()
                && bytes@.subrange(off@[x] as int, off@[x + 1] as int) == keys[x],
            forall|x: int| 0 <= x < i ==> #[trigger] r@[x] == below_texts(keys, x).len(),
        decreases n - i,
    {
        let mut c: usize = 0;
        let mut j: usize = 0;
        proof {
            assert(off@[i as int] <= off@[i + 1]);
            assert(set_int_range(0, 0).filter(|z: int| text_lt(keys[z], keys[i as int])) =~= Set::<int>::empty()) by {
                vstd::set_lib::lemma_int_range(0, 0);
            }
        }
        while j < n
            invariant
                n == keys.len(), off@.len() == n + 1, i < n, j <= n,
                forall|x: int| 0 <= x < n ==> off@[x] <= #[trigger] off@[x + 1] <= bytes@.len()
                    && bytes@.subrange(off@[x] as int, off@[x + 1] as int) == keys[x],
                c == set_int_range(0, j as int).filter(|z: int| text_lt(keys[z], keys[i as int])).len(),
                c <= j,
            decreases n - j,
        {
            proof { assert(off@[j as int] <= off@[j + 1]); }
            let lt = lex_cmp_exec(bytes, off[j], off[j + 1], bytes, off[i], off[i + 1]) < 0;
            proof {
                vstd::set_lib::lemma_int_range(0, j as int);
                vstd::set_lib::lemma_int_range(0, j + 1);
                let f = |z: int| text_lt(keys[z], keys[i as int]);
                let s0 = set_int_range(0, j as int).filter(f);
                let s1 = set_int_range(0, j + 1).filter(f);
                if lt {
                    assert(s1 =~= s0.insert(j as int));
                    assert(!s0.contains(j as int));
                } else {
                    assert(s1 =~= s0);
                }
            }
            if lt {
                c = c + 1;
            }
            j = j + 1;
        }
        r.push(c);
        proof {
            assert(set_int_range(0, n as int).filter(|z: int| text_lt(keys[z], keys[i as int])) == below_texts(keys, i as int));
        }
        i = i + 1;
    }
    r
}

/// The ranks of integers.
pub fn int_ranks(vs: &Vec<i64>) -> (r: Vec<usize>)
    ensures r@.len() == vs@.len(), forall|i: int| 0 <= i < vs@.len() ==> #[trigger] r@[i] == below_ints(vs@, i).len(),
{
    let n = vs.len();
    let mut r: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant n == vs@.len(), i <= n, r@.len() == i,
            forall|x: int| 0 <= x < i ==> #[trigger] r@[x] == below_ints(vs@, x).len(),
        decreases n - i,
    {
        let mut c: usize = 0;
        let mut j: usize = 0;
        proof {
            vstd::set_lib::lemma_int_range(0, 0);
            assert(set_int_range(0, 0).filter(|z: int| vs@[z] < vs@[i as int]) =~= Set::<int>::empty());
        }
        while j < n
            invariant n == vs@.len(), i < n, j <= n, c <= j,
                c == set_int_range(0, j as int).filter(|z: int| vs@[z] < vs@[i as int]).len(),
            decreases n - j,
        {
            let lt = vs[j] < vs[i];
            proof {
                vstd::set_lib::lemma_int_range(0, j as int);
                vstd::set_lib::lemma_int_range(0, j + 1);
                let f = |z: int| vs@[z] < vs@[i as int];
                let s0 = set_int_range(0, j as int).filter(f);
                let s1 = set_int_range(0, j + 1).filter(f);
                if lt {
                    assert(s1 =~= s0.insert(j as int));
                    assert(!s0.contains(j as int));
                } else {
                    assert(s1 =~= s0);
                }
            }
            if lt { c = c + 1; }
            j = j + 1;
        }
        r.push(c);
        i = i + 1;
    }
    r
}

} // verus!
