//! Top-k selection under ORDER BY keys (`spec::order::keys_cmp`), for relations of distinct rows. `topk_ok(buf, all)`:
//! `buf` holds the first `min(k, |all|)` rows of `all` in key order, sorted (ties in any order). Laws: the empty
//! case, inserting one more row at its sorted position (truncated to `k`), skipping a row not below the k-th, and
//! absorbing the top-k of a disjoint relation (partition and merge). `lemma_topk_ordered` turns `topk_ok` into the
//! `ORDER BY .. LIMIT k` outcome form of `spec::order::ordered_ok`: a sorted permutation of `all` whose first `k`
//! rows are `buf`.
use vstd::prelude::*;
use crate::spec::value::Row;
use crate::spec::ast::OrderKey;
use crate::spec::order::{keys_cmp, sorted_by, slice_rows, sort_rows};
use crate::bridge::order::{keys_ok, all_keys_ok, lemma_keys_cmp_trans, lemma_keys_cmp_antisym, lemma_sort_rows};

verus! {

pub open spec fn min_nat(a: nat, b: nat) -> nat { if a <= b { a } else { b } }

/// `buf` is the top `k` of `all` (distinct rows) under `keys`.
pub open spec fn topk_ok(keys: Seq<OrderKey>, fams: Seq<int>, k: nat, buf: Seq<Row>, all: Seq<Row>) -> bool {
    &&& sorted_by(keys, buf)
    &&& buf.no_duplicates()
    &&& all_keys_ok(keys, fams, buf)
    &&& forall|i: int| 0 <= i < buf.len() ==> all.contains(#[trigger] buf[i])
    &&& buf.len() == min_nat(k, all.len())
    &&& buf.len() > 0 ==> forall|x: Row| #[trigger] all.contains(x) && !buf.contains(x) ==> keys_cmp(keys, buf.last(), x) <= 0
}

/// A relation of distinct rows whose keys are in their families.
pub open spec fn rel_wf(keys: Seq<OrderKey>, fams: Seq<int>, all: Seq<Row>) -> bool {
    all.no_duplicates() && all_keys_ok(keys, fams, all)
}

/// A duplicate-free sequence inside another is not longer; of equal length, it holds every row of the other.
pub proof fn lemma_nodup_sub(a: Seq<Row>, b: Seq<Row>)
    requires
        a.no_duplicates(),
        b.no_duplicates(),
        forall|i: int| 0 <= i < a.len() ==> b.contains(#[trigger] a[i]),
    ensures
        a.len() <= b.len(),
        a.len() == b.len() ==> forall|x: Row| #[trigger] b.contains(x) ==> a.contains(x),
{
    a.unique_seq_to_set();
    b.unique_seq_to_set();
    assert(a.to_set().subset_of(b.to_set())) by {
        assert forall|x: Row| a.to_set().contains(x) implies b.to_set().contains(x) by {
            let i = choose|i: int| 0 <= i < a.len() && a[i] == x;
            assert(b.contains(a[i]));
        }
    }
    vstd::set_lib::lemma_len_subset(a.to_set(), b.to_set());
    if a.len() == b.len() {
        vstd::set_lib::lemma_subset_equality(a.to_set(), b.to_set());
        assert forall|x: Row| #[trigger] b.contains(x) implies a.contains(x) by {
            assert(b.to_set().contains(x));
            assert(a.to_set().contains(x));
        }
    }
}

/// The empty relation's top k is empty.
pub proof fn lemma_topk_empty(keys: Seq<OrderKey>, fams: Seq<int>, k: nat)
    ensures topk_ok(keys, fams, k, Seq::empty(), Seq::empty()),
{
}

/// A sorted sequence: every row is not above its last row.
pub proof fn lemma_sorted_last(keys: Seq<OrderKey>, s: Seq<Row>, i: int)
    requires sorted_by(keys, s), 0 <= i < s.len(),
    ensures keys_cmp(keys, s[i], s.last()) <= 0 || i == s.len() - 1,
{
    if i < s.len() - 1 {
        assert(keys_cmp(keys, s[i], s[s.len() - 1]) <= 0);
    }
}

/// `r` inserted at `pos` (after the rows not above it), truncated to `k`.
pub open spec fn ins_at(buf: Seq<Row>, pos: int, r: Row, k: nat) -> Seq<Row> {
    let full = buf.subrange(0, pos).push(r) + buf.subrange(pos, buf.len() as int);
    if full.len() > k { full.subrange(0, k as int) } else { full }
}

/// `pos` is the sorted position of `r` in `buf`: the rows before it are not above `r`, the rows from it are above.
pub open spec fn ins_pos(keys: Seq<OrderKey>, buf: Seq<Row>, pos: int, r: Row) -> bool {
    &&& 0 <= pos <= buf.len()
    &&& forall|i: int| 0 <= i < pos ==> keys_cmp(keys, #[trigger] buf[i], r) <= 0
    &&& forall|i: int| pos <= i < buf.len() ==> keys_cmp(keys, #[trigger] buf[i], r) > 0
}

proof fn lemma_ins_at_index(buf: Seq<Row>, pos: int, r: Row, k: nat, i: int)
    requires 0 <= pos <= buf.len(), 0 <= i,
    ensures
        i < ins_at(buf, pos, r, k).len() ==>
            ins_at(buf, pos, r, k)[i] == if i < pos { buf[i] } else if i == pos { r } else { buf[i - 1] },
        ins_at(buf, pos, r, k).len() == min_nat(k, buf.len() + 1),
{
}

/// Membership in a sequence with one more row.
pub proof fn lemma_push_contains(all: Seq<Row>, r: Row)
    ensures
        all.push(r).contains(r),
        forall|x: Row| #[trigger] all.contains(x) ==> all.push(r).contains(x),
        forall|x: Row| #[trigger] all.push(r).contains(x) ==> all.contains(x) || x == r,
        all.push(r).no_duplicates() ==> all.no_duplicates() && !all.contains(r),
{
    assert(all.push(r)[all.len() as int] == r);
    assert forall|x: Row| #[trigger] all.contains(x) implies all.push(r).contains(x) by {
        let i = choose|i: int| 0 <= i < all.len() && all[i] == x;
        assert(all.push(r)[i] == x);
    }
    assert forall|x: Row| #[trigger] all.push(r).contains(x) implies all.contains(x) || x == r by {
        let i = choose|i: int| 0 <= i < all.len() + 1 && all.push(r)[i] == x;
        if i < all.len() {
            assert(all[i] == x);
        }
    }
    if all.push(r).no_duplicates() {
        assert forall|i: int, j: int| 0 <= i < all.len() && 0 <= j < all.len() && i != j implies all[i] != all[j] by {
            assert(all.push(r)[i] == all[i] && all.push(r)[j] == all[j]);
        }
        if all.contains(r) {
            let i = choose|i: int| 0 <= i < all.len() && all[i] == r;
            assert(all.push(r)[i] == all.push(r)[all.len() as int]);
        }
    }
}

/// The inserted sequence is sorted.
proof fn lemma_ins_sorted(keys: Seq<OrderKey>, fams: Seq<int>, k: nat, buf: Seq<Row>, r: Row, pos: int)
    requires
        sorted_by(keys, buf),
        all_keys_ok(keys, fams, buf),
        keys_ok(keys, fams, r),
        ins_pos(keys, buf, pos, r),
    ensures
        sorted_by(keys, ins_at(buf, pos, r, k)),
{
    let nb = ins_at(buf, pos, r, k);
    assert forall|i: int, j: int| 0 <= i < j < nb.len() implies keys_cmp(keys, #[trigger] nb[i], #[trigger] nb[j]) <= 0 by {
        lemma_ins_at_index(buf, pos, r, k, i);
        lemma_ins_at_index(buf, pos, r, k, j);
        if j < pos {
            assert(keys_cmp(keys, buf[i], buf[j]) <= 0);
        } else if j == pos {
            assert(keys_cmp(keys, buf[i], r) <= 0);
        } else if i < pos {
            assert(keys_ok(keys, fams, buf[i]));
            assert(keys_ok(keys, fams, buf[j - 1]));
            assert(keys_cmp(keys, buf[i], r) <= 0);
            assert(keys_cmp(keys, buf[j - 1], r) > 0);
            lemma_keys_cmp_antisym(keys, fams, buf[j - 1], r);
            lemma_keys_cmp_trans(keys, fams, buf[i], r, buf[j - 1]);
        } else if i == pos {
            assert(keys_ok(keys, fams, buf[j - 1]));
            assert(keys_cmp(keys, buf[j - 1], r) > 0);
            lemma_keys_cmp_antisym(keys, fams, buf[j - 1], r);
        } else {
            assert(keys_cmp(keys, buf[i - 1], buf[j - 1]) <= 0);
        }
    }
}

/// The inserted sequence: its rows are `r` and rows of `buf`, distinct, with their keys in their families.
proof fn lemma_ins_rows(keys: Seq<OrderKey>, fams: Seq<int>, k: nat, buf: Seq<Row>, r: Row, pos: int)
    requires
        buf.no_duplicates(),
        all_keys_ok(keys, fams, buf),
        keys_ok(keys, fams, r),
        !buf.contains(r),
        0 <= pos <= buf.len(),
    ensures
        ins_at(buf, pos, r, k).no_duplicates(),
        all_keys_ok(keys, fams, ins_at(buf, pos, r, k)),
        forall|i: int| 0 <= i < ins_at(buf, pos, r, k).len() ==> #[trigger] ins_at(buf, pos, r, k)[i] == r
            || buf.contains(ins_at(buf, pos, r, k)[i]),
        k >= 1 ==> ins_at(buf, pos, r, k).contains(r) || pos >= k,
        forall|bi: int| 0 <= bi < buf.len() && bi + 1 < k ==> #[trigger] ins_at(buf, pos, r, k).contains(buf[bi]),
        ins_at(buf, pos, r, k).len() == min_nat(k, buf.len() + 1),
{
    let nb = ins_at(buf, pos, r, k);
    lemma_ins_at_index(buf, pos, r, k, 0);
    assert forall|i: int| 0 <= i < nb.len() implies #[trigger] nb[i] == r || buf.contains(nb[i]) by {
        lemma_ins_at_index(buf, pos, r, k, i);
        if i < pos {
            assert(buf.contains(buf[i]));
        } else if i > pos {
            assert(buf.contains(buf[i - 1]));
        }
    }
    assert forall|i: int| 0 <= i < nb.len() implies keys_ok(keys, fams, #[trigger] nb[i]) by {
        lemma_ins_at_index(buf, pos, r, k, i);
    }
    assert forall|i: int, j: int| 0 <= i < nb.len() && 0 <= j < nb.len() && i != j implies nb[i] != nb[j] by {
        lemma_ins_at_index(buf, pos, r, k, i);
        lemma_ins_at_index(buf, pos, r, k, j);
        if i == pos {
            assert(buf.contains(nb[j]));
        } else if j == pos {
            assert(buf.contains(nb[i]));
        }
    }
    if k >= 1 && pos < k {
        lemma_ins_at_index(buf, pos, r, k, pos);
    }
    assert forall|bi: int| 0 <= bi < buf.len() && bi + 1 < k implies #[trigger] nb.contains(buf[bi]) by {
        if bi < pos {
            lemma_ins_at_index(buf, pos, r, k, bi);
        } else {
            lemma_ins_at_index(buf, pos, r, k, bi + 1);
        }
    }
}

/// Inserting a new row at its sorted position keeps the top k (when it enters the buffer).
pub proof fn lemma_topk_insert(keys: Seq<OrderKey>, fams: Seq<int>, k: nat, buf: Seq<Row>, all: Seq<Row>, r: Row, pos: int)
    requires
        topk_ok(keys, fams, k, buf, all),
        rel_wf(keys, fams, all.push(r)),
        k >= 1,
        ins_pos(keys, buf, pos, r),
        buf.len() < k || pos < buf.len(),
    ensures
        topk_ok(keys, fams, k, ins_at(buf, pos, r, k), all.push(r)),
{
    let nb = ins_at(buf, pos, r, k);
    let al = all.push(r);
    lemma_push_contains(all, r);
    assert(keys_ok(keys, fams, r)) by { assert(al[all.len() as int] == r); }
    assert forall|i: int| 0 <= i < all.len() implies keys_ok(keys, fams, #[trigger] all[i]) by {
        assert(al[i] == all[i]);
    }
    assert(!buf.contains(r)) by {
        if buf.contains(r) {
            let i = choose|i: int| 0 <= i < buf.len() && buf[i] == r;
            assert(all.contains(buf[i]));
        }
    }
    lemma_ins_sorted(keys, fams, k, buf, r, pos);
    lemma_ins_rows(keys, fams, k, buf, r, pos);
    assert forall|i: int| 0 <= i < nb.len() implies al.contains(#[trigger] nb[i]) by {
        if nb[i] != r {
            let bi = choose|bi: int| 0 <= bi < buf.len() && buf[bi] == nb[i];
            assert(all.contains(buf[bi]));
        }
    }
    lemma_nodup_sub(buf, all);
    if buf.len() < k {
        assert(buf.len() == all.len());
    }
    if nb.len() > 0 {
        assert forall|x: Row| #[trigger] al.contains(x) && !nb.contains(x) implies keys_cmp(keys, nb.last(), x) <= 0 by {
            lemma_topk_insert_threshold(keys, fams, k, buf, all, r, pos, x);
        }
    }
}

/// The threshold of the inserted buffer: a row of `all.push(r)` left out is not above its last row.
proof fn lemma_topk_insert_threshold(keys: Seq<OrderKey>, fams: Seq<int>, k: nat, buf: Seq<Row>, all: Seq<Row>, r: Row, pos: int, x: Row)
    requires
        topk_ok(keys, fams, k, buf, all),
        rel_wf(keys, fams, all.push(r)),
        k >= 1,
        ins_pos(keys, buf, pos, r),
        buf.len() < k || pos < buf.len(),
        all.push(r).contains(x),
        !ins_at(buf, pos, r, k).contains(x),
        ins_at(buf, pos, r, k).len() > 0,
    ensures
        keys_cmp(keys, ins_at(buf, pos, r, k).last(), x) <= 0,
{
    let nb = ins_at(buf, pos, r, k);
    let al = all.push(r);
    lemma_push_contains(all, r);
    assert(keys_ok(keys, fams, r)) by { assert(al[all.len() as int] == r); }
    assert(!buf.contains(r)) by {
        if buf.contains(r) {
            let i = choose|i: int| 0 <= i < buf.len() && buf[i] == r;
            assert(all.contains(buf[i]));
        }
    }
    assert(forall|i: int| 0 <= i < buf.len() ==> keys_ok(keys, fams, #[trigger] buf[i]));
    lemma_ins_rows(keys, fams, k, buf, r, pos);
    lemma_nodup_sub(buf, all);
    assert(x != r);
    assert(all.contains(x));
    let xi = choose|xi: int| 0 <= xi < all.len() && all[xi] == x;
    assert(keys_ok(keys, fams, x)) by { assert(al[xi] == x); }
    if buf.len() < k {
        // every row of `all` is in `buf`, hence in `nb`
        assert(buf.len() == all.len());
        assert(buf.contains(x));
        let bi = choose|bi: int| 0 <= bi < buf.len() && buf[bi] == x;
        assert(nb.contains(buf[bi]));
    } else {
        // full: `buf.last()` dropped out; `nb.last()` is not above it
        assert(buf.len() == k);
        let bl = buf.last();
        let nl = nb.last();
        lemma_ins_at_index(buf, pos, r, k, k - 1);
        assert(keys_ok(keys, fams, bl)) by { assert(bl == buf[buf.len() - 1]); }
        assert(keys_cmp(keys, nl, bl) <= 0) by {
            if pos == k - 1 {
                assert(nl == r);
                assert(keys_cmp(keys, buf[k - 1], r) > 0);
                lemma_keys_cmp_antisym(keys, fams, buf[k - 1], r);
            } else {
                assert(nl == buf[k - 2]);
                assert(keys_cmp(keys, buf[k - 2], buf[k - 1]) <= 0);
            }
        }
        assert(keys_ok(keys, fams, nl)) by { assert(nl == nb[nb.len() - 1]); }
        if x != bl {
            assert(!buf.contains(x)) by {
                if buf.contains(x) {
                    let bi = choose|bi: int| 0 <= bi < buf.len() && buf[bi] == x;
                    assert(bi != k - 1);
                    assert(nb.contains(buf[bi]));
                }
            }
            assert(keys_cmp(keys, bl, x) <= 0);
            lemma_keys_cmp_trans(keys, fams, nl, bl, x);
        }
    }
}

/// A row not below the k-th of a full buffer leaves the top k unchanged.
pub proof fn lemma_topk_skip(keys: Seq<OrderKey>, fams: Seq<int>, k: nat, buf: Seq<Row>, all: Seq<Row>, r: Row)
    requires
        topk_ok(keys, fams, k, buf, all),
        rel_wf(keys, fams, all.push(r)),
        k >= 1,
        buf.len() == k,
        keys_cmp(keys, buf.last(), r) <= 0,
    ensures
        topk_ok(keys, fams, k, buf, all.push(r)),
{
    let al = all.push(r);
    assert(al[all.len() as int] == r);
    lemma_push_contains(all, r);
    assert forall|i: int| 0 <= i < buf.len() implies al.contains(#[trigger] buf[i]) by {
        assert(all.contains(buf[i]));
        let j = choose|j: int| 0 <= j < all.len() && all[j] == buf[i];
        assert(al[j] == buf[i]);
    }
    assert forall|x: Row| #[trigger] al.contains(x) && !buf.contains(x) implies keys_cmp(keys, buf.last(), x) <= 0 by {
        if x != r {
            let i = choose|i: int| 0 <= i < al.len() && al[i] == x;
            assert(all[i] == x);
            assert(all.contains(x));
        }
    }
    lemma_nodup_sub(buf, all);
}

/// In an absorb step: the last row of the merged buffer is not above the last row of a full partial top k `l`
/// (otherwise every row of `l` would be in `buf`, so `buf` would be `l`).
proof fn lemma_absorb_last(keys: Seq<OrderKey>, fams: Seq<int>, k: nat, buf: Seq<Row>, a: Seq<Row>, l: Seq<Row>)
    requires
        k >= 1,
        topk_ok(keys, fams, k, buf, a + l),
        sorted_by(keys, l),
        l.no_duplicates(),
        all_keys_ok(keys, fams, l),
        l.len() == k,
        buf.len() > 0,
    ensures
        keys_cmp(keys, buf.last(), l.last()) <= 0,
{
    let al = a + l;
    let ll = l.last();
    assert(keys_ok(keys, fams, ll)) by { assert(ll == l[l.len() - 1]); }
    assert(keys_ok(keys, fams, buf.last())) by { assert(buf.last() == buf[buf.len() - 1]); }
    if keys_cmp(keys, buf.last(), ll) > 0 {
        assert forall|j: int| 0 <= j < l.len() implies buf.contains(#[trigger] l[j]) by {
            assert(keys_ok(keys, fams, l[j]));
            if !buf.contains(l[j]) {
                assert(al[a.len() + j] == l[j]);
                assert(al.contains(l[j]));
                assert(keys_cmp(keys, buf.last(), l[j]) <= 0);
                if j < l.len() - 1 {
                    assert(keys_cmp(keys, l[j], l[l.len() - 1]) <= 0);
                    lemma_keys_cmp_trans(keys, fams, buf.last(), l[j], ll);
                }
            }
        }
        lemma_nodup_sub(l, buf);
        assert(buf.contains(buf.last())) by { assert(buf[buf.len() - 1] == buf.last()); }
        let li = choose|li: int| 0 <= li < l.len() && l[li] == buf.last();
        if li < l.len() - 1 {
            assert(keys_cmp(keys, l[li], l[l.len() - 1]) <= 0);
        }
        lemma_keys_cmp_antisym(keys, fams, buf.last(), ll);
    }
}

/// Absorbing the top k `l` of a relation `b` disjoint from `a`: the top k of `a ++ l` is the top k of `a ++ b`.
pub proof fn lemma_topk_absorb(keys: Seq<OrderKey>, fams: Seq<int>, k: nat, buf: Seq<Row>, a: Seq<Row>, l: Seq<Row>, b: Seq<Row>)
    requires
        k >= 1,
        topk_ok(keys, fams, k, buf, a + l),
        topk_ok(keys, fams, k, l, b),
        rel_wf(keys, fams, a + b),
        rel_wf(keys, fams, b),
    ensures
        topk_ok(keys, fams, k, buf, a + b),
{
    let al = a + l;
    let ab = a + b;
    assert forall|i: int| 0 <= i < buf.len() implies ab.contains(#[trigger] buf[i]) by {
        assert(al.contains(buf[i]));
        let j = choose|j: int| 0 <= j < al.len() && al[j] == buf[i];
        if j < a.len() {
            assert(ab[j] == buf[i]);
        } else {
            assert(l[j - a.len()] == buf[i]);
            assert(b.contains(l[j - a.len()]));
            let jb = choose|jb: int| 0 <= jb < b.len() && b[jb] == buf[i];
            assert(ab[a.len() + jb] == buf[i]);
        }
    }
    lemma_nodup_sub(l, b);
    assert(buf.len() == min_nat(k, ab.len()));
    if buf.len() > 0 {
        assert forall|x: Row| #[trigger] ab.contains(x) && !buf.contains(x) implies keys_cmp(keys, buf.last(), x) <= 0 by {
            let i = choose|i: int| 0 <= i < ab.len() && ab[i] == x;
            assert(keys_ok(keys, fams, x)) by { assert(ab[i] == x); }
            if i < a.len() {
                assert(al[i] == x);
                assert(al.contains(x));
            } else if l.contains(x) {
                let li = choose|li: int| 0 <= li < l.len() && l[li] == x;
                assert(al[a.len() + li] == x);
                assert(al.contains(x));
            } else {
                // x lies in b but not in its top k: l is full and l.last() <= x
                assert(b[i - a.len()] == x);
                assert(b.contains(x));
                assert(l.len() == k) by {
                    if l.len() < k {
                        assert(l.len() == b.len());
                    }
                }
                let ll = l.last();
                assert(keys_cmp(keys, ll, x) <= 0);
                assert(keys_ok(keys, fams, ll)) by { assert(ll == l[l.len() - 1]); }
                assert(keys_ok(keys, fams, buf.last())) by { assert(buf.last() == buf[buf.len() - 1]); }
                lemma_absorb_last(keys, fams, k, buf, a, l);
                lemma_keys_cmp_trans(keys, fams, buf.last(), ll, x);
            }
        }
    }
}

/// The rows of `all` not in `out`, in order.
pub open spec fn rest_of(all: Seq<Row>, out: Seq<Row>) -> Seq<Row>
    decreases all.len(),
{
    if all.len() == 0 {
        Seq::empty()
    } else {
        let r = rest_of(all.drop_last(), out);
        if out.contains(all.last()) { r } else { r.push(all.last()) }
    }
}

/// `rest_of` holds exactly the rows of `all` outside `out`, without duplicates when `all` has none.
pub proof fn lemma_rest_of(all: Seq<Row>, out: Seq<Row>)
    ensures
        forall|x: Row| #[trigger] rest_of(all, out).contains(x) <==> (all.contains(x) && !out.contains(x)),
        all.no_duplicates() ==> rest_of(all, out).no_duplicates(),
    decreases all.len(),
{
    if all.len() > 0 {
        let ai = all.drop_last();
        lemma_rest_of(ai, out);
        let r = rest_of(ai, out);
        let x0 = all.last();
        assert(all =~= ai.push(x0));
        assert forall|x: Row| #[trigger] rest_of(all, out).contains(x) <==> (all.contains(x) && !out.contains(x)) by {
            if all.contains(x) && x != x0 {
                let i = choose|i: int| 0 <= i < all.len() && all[i] == x;
                assert(i < ai.len());
                assert(ai[i] == x);
            }
            if ai.contains(x) {
                let i = choose|i: int| 0 <= i < ai.len() && ai[i] == x;
                assert(all[i] == x);
            }
            if !out.contains(x0) {
                assert(rest_of(all, out) == r.push(x0));
                if r.push(x0).contains(x) && x != x0 {
                    let i = choose|i: int| 0 <= i < r.len() + 1 && r.push(x0)[i] == x;
                    assert(r[i] == x);
                }
                if r.contains(x) {
                    let i = choose|i: int| 0 <= i < r.len() && r[i] == x;
                    assert(r.push(x0)[i] == x);
                }
                assert(r.push(x0)[r.len() as int] == x0);
            }
        }
        if all.no_duplicates() && !out.contains(x0) {
            assert(!ai.contains(x0)) by {
                if ai.contains(x0) {
                    let i = choose|i: int| 0 <= i < ai.len() && ai[i] == x0;
                    assert(all[i] == all[all.len() - 1]);
                }
            }
            assert(!r.contains(x0));
            assert forall|i: int, j: int| 0 <= i < r.len() + 1 && 0 <= j < r.len() + 1 && i != j implies r.push(x0)[i] != r.push(x0)[j] by {
                if i == r.len() { assert(r.contains(r[j])); } else if j == r.len() { assert(r.contains(r[i])); }
            }
        }
        if all.no_duplicates() {
            assert(ai.no_duplicates());
        }
    }
}

/// The top k as an `ORDER BY .. LIMIT k` outcome: a sorted permutation of `all` whose first `k` rows are `out`.
pub proof fn lemma_topk_ordered(keys: Seq<OrderKey>, fams: Seq<int>, k: nat, out: Seq<Row>, all: Seq<Row>)
    requires
        topk_ok(keys, fams, k, out, all),
        rel_wf(keys, fams, all),
    ensures ({
        let p = out + sort_rows(keys, rest_of(all, out));
        &&& p.to_multiset() == all.to_multiset()
        &&& sorted_by(keys, p)
        &&& slice_rows(p, 0, Some(k)) == out
    }),
{
    let rest = rest_of(all, out);
    let sr = sort_rows(keys, rest);
    let p = out + sr;
    lemma_rest_of(all, out);
    assert(all_keys_ok(keys, fams, rest)) by {
        assert forall|i: int| 0 <= i < rest.len() implies keys_ok(keys, fams, #[trigger] rest[i]) by {
            assert(rest.contains(rest[i]));
            let j = choose|j: int| 0 <= j < all.len() && all[j] == rest[i];
        }
    }
    lemma_sort_rows(keys, fams, rest);
    // sr is a permutation of rest: the same rows, no duplicates
    sr.to_multiset_ensures();
    rest.to_multiset_ensures();
    assert forall|x: Row| #[trigger] sr.contains(x) <==> rest.contains(x) by {
        assert(sr.to_multiset().count(x) == rest.to_multiset().count(x));
    }
    rest.lemma_multiset_has_no_duplicates();
    sr.lemma_multiset_has_no_duplicates_conv();
    // p: duplicate-free, the same rows as all
    assert forall|i: int, j: int| 0 <= i < out.len() && 0 <= j < sr.len() implies out[i] != sr[j] by {
        assert(sr.contains(sr[j]));
        assert(rest.contains(sr[j]));
        assert(out.contains(out[i]));
    }
    vstd::seq_lib::lemma_no_dup_in_concat(out, sr);
    assert forall|x: Row| #[trigger] p.contains(x) <==> all.contains(x) by {
        if p.contains(x) {
            let i = choose|i: int| 0 <= i < p.len() && p[i] == x;
            if i < out.len() {
                assert(out[i] == x);
            } else {
                assert(sr[i - out.len()] == x);
                assert(sr.contains(x));
            }
        }
        if all.contains(x) {
            if out.contains(x) {
                let i = choose|i: int| 0 <= i < out.len() && out[i] == x;
                assert(p[i] == x);
            } else {
                assert(rest.contains(x));
                assert(sr.contains(x));
                let i = choose|i: int| 0 <= i < sr.len() && sr[i] == x;
                assert(p[out.len() + i] == x);
            }
        }
    }
    crate::link::query::lemma_nodup_same_multiset(p, all);
    // sorted: out sorted, sr sorted, every row of out not above every row of sr
    assert forall|i: int, j: int| 0 <= i < j < p.len() implies keys_cmp(keys, #[trigger] p[i], #[trigger] p[j]) <= 0 by {
        if j < out.len() {
            assert(p[i] == out[i] && p[j] == out[j]);
        } else if i >= out.len() {
            assert(p[i] == sr[i - out.len()] && p[j] == sr[j - out.len()]);
        } else {
            let x = sr[j - out.len()];
            assert(p[j] == x);
            assert(sr.contains(x));
            assert(rest.contains(x));
            assert(out.len() > 0);
            assert(keys_cmp(keys, out.last(), x) <= 0);
            assert(keys_ok(keys, fams, x)) by {
                let t = choose|t: int| 0 <= t < sr.len() && sr[t] == x;
            }
            assert(keys_ok(keys, fams, out[i]));
            assert(keys_ok(keys, fams, out.last())) by { assert(out.last() == out[out.len() - 1]); }
            if i < out.len() - 1 {
                assert(keys_cmp(keys, out[i], out[out.len() - 1]) <= 0);
                lemma_keys_cmp_trans(keys, fams, out[i], out.last(), x);
            }
        }
    }
    // the first k rows are out
    lemma_nodup_sub(out, all);
    if out.len() < k {
        assert(out.len() == all.len());
        assert(rest.len() == 0) by {
            if rest.len() > 0 {
                assert(rest.contains(rest[0]));
            }
        }
        assert(sr.len() == 0) by {
            if sr.len() > 0 {
                assert(sr.contains(sr[0]));
            }
        }
        assert(p =~= out);
        assert(slice_rows(p, 0, Some(k)) =~= out);
    } else {
        assert(out.len() == k);
        assert(slice_rows(p, 0, Some(k)) =~= out);
    }
}

} // verus!
