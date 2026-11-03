//! GROUP BY over exact keys: when SQL "not distinct" is structural equality on every key of the input
//! (`exact_keys`), the denotation's groups (`distinct_rows`) are the distinct keys in first-occurrence order
//! (`dk`) and each group's members (`group_members`) are the argument rows of the input rows with that key (`mem`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::equality::*;
use crate::spec::relation::*;

verus! {

/// Distinct keys in first-occurrence order (structural equality).
pub open spec fn dk(keys: Seq<Row>) -> Seq<Row>
    decreases keys.len(),
{
    if keys.len() == 0 {
        Seq::empty()
    } else {
        let d = dk(keys.drop_last());
        if d.contains(keys.last()) { d } else { d.push(keys.last()) }
    }
}

/// Argument rows of the input rows whose key is `k` (structurally), in input order.
pub open spec fn mem(keys: Seq<Row>, args: Seq<Row>, k: Row) -> Seq<Row>
    decreases keys.len(),
{
    if keys.len() == 0 || args.len() == 0 {
        Seq::empty()
    } else {
        let m = mem(keys.drop_last(), args.drop_last(), k);
        if keys.last() == k { m.push(args.last()) } else { m }
    }
}

/// SQL "not distinct" is structural equality on every pair of keys.
pub open spec fn exact_keys(keys: Seq<Row>) -> bool {
    forall|a: Row, b: Row| keys.contains(a) && keys.contains(b) ==> (#[trigger] row_not_distinct(a, b) <==> a == b)
}

/// `dk` has no duplicates and exactly the keys' values.
pub proof fn lemma_dk(keys: Seq<Row>)
    ensures
        dk(keys).no_duplicates(),
        forall|x: Row| #![trigger dk(keys).contains(x)] #![trigger keys.contains(x)] dk(keys).contains(x) <==> keys.contains(x),
    decreases keys.len(),
{
    if keys.len() > 0 {
        let ki = keys.drop_last();
        lemma_dk(ki);
        let d = dk(ki);
        assert forall|x: Row| #![trigger dk(keys).contains(x)] #![trigger keys.contains(x)] dk(keys).contains(x) <==> keys.contains(x) by {
            if ki.contains(x) {
                let i = choose|i: int| 0 <= i < ki.len() && ki[i] == x;
                assert(keys[i] == x);
            }
            if keys.contains(x) {
                let i = choose|i: int| 0 <= i < keys.len() && keys[i] == x;
                if i < ki.len() {
                    assert(ki[i] == x);
                } else {
                    assert(x == keys.last());
                }
            }
            if !d.contains(keys.last()) {
                let e = d.push(keys.last());
                if e.contains(x) {
                    let i = choose|i: int| 0 <= i < e.len() && e[i] == x;
                    if i < d.len() {
                        assert(d[i] == x);
                    }
                }
                if d.contains(x) {
                    let i = choose|i: int| 0 <= i < d.len() && d[i] == x;
                    assert(e[i] == x);
                }
                assert(e[d.len() as int] == keys.last());
            }
        }
        if !d.contains(keys.last()) {
            let e = d.push(keys.last());
            assert forall|i: int, j: int| 0 <= i < e.len() && 0 <= j < e.len() && i != j implies e[i] != e[j] by {
                if i < d.len() && j < d.len() {
                    assert(e[i] == d[i] && e[j] == d[j]);
                } else if i < d.len() {
                    assert(e[i] == d[i]);
                    assert(d.contains(d[i]));
                } else if j < d.len() {
                    assert(e[j] == d[j]);
                    assert(d.contains(d[j]));
                }
            }
        }
    }
}

/// `has_not_distinct` over a sequence drawn from an exact pool is `contains`.
proof fn lemma_has_nd(d: Seq<Row>, k: Row, keys: Seq<Row>)
    requires
        exact_keys(keys),
        forall|i: int| 0 <= i < d.len() ==> keys.contains(#[trigger] d[i]),
        keys.contains(k),
    ensures has_not_distinct(d, k) <==> d.contains(k),
    decreases d.len(),
{
    if d.len() > 0 {
        let di = d.drop_last();
        assert forall|i: int| 0 <= i < di.len() implies keys.contains(#[trigger] di[i]) by {
            assert(di[i] == d[i]);
        }
        lemma_has_nd(di, k, keys);
        assert(keys.contains(d[d.len() - 1]));
        assert(row_not_distinct(d.last(), k) <==> d.last() == k);
        if di.contains(k) {
            let i = choose|i: int| 0 <= i < di.len() && di[i] == k;
            assert(d[i] == k);
        }
        if d.contains(k) && d.last() != k {
            let i = choose|i: int| 0 <= i < d.len() && d[i] == k;
            assert(di[i] == k);
        }
    }
}

/// Exact keys: the denotation's groups are `dk`.
pub proof fn lemma_distinct_rows_dk(keys: Seq<Row>)
    requires exact_keys(keys),
    ensures distinct_rows(keys) == dk(keys),
    decreases keys.len(),
{
    if keys.len() > 0 {
        let ki = keys.drop_last();
        assert(exact_keys(ki)) by {
            assert forall|a: Row, b: Row| ki.contains(a) && ki.contains(b) implies (#[trigger] row_not_distinct(a, b) <==> a == b) by {
                let i = choose|i: int| 0 <= i < ki.len() && ki[i] == a;
                let j = choose|j: int| 0 <= j < ki.len() && ki[j] == b;
                assert(keys[i] == a && keys[j] == b);
            }
        }
        lemma_distinct_rows_dk(ki);
        lemma_dk(ki);
        let d = dk(ki);
        assert forall|i: int| 0 <= i < d.len() implies keys.contains(#[trigger] d[i]) by {
            assert(d.contains(d[i]));
            let m = choose|m: int| 0 <= m < ki.len() && ki[m] == d[i];
            assert(keys[m] == d[i]);
        }
        assert(keys[keys.len() - 1] == keys.last());
        lemma_has_nd(d, keys.last(), keys);
    }
}

/// Exact keys: the denotation's members of a key of the input are `mem`.
pub proof fn lemma_group_members_mem(keys: Seq<Row>, args: Seq<Row>, k: Row)
    requires exact_keys(keys), keys.contains(k), keys.len() == args.len(),
    ensures group_members(keys, args, k) == mem(keys, args, k),
    decreases keys.len(),
{
    if keys.len() > 0 {
        let (ki, ai) = (keys.drop_last(), args.drop_last());
        assert(keys[keys.len() - 1] == keys.last());
        assert(row_not_distinct(keys.last(), k) <==> keys.last() == k);
        if ki.contains(k) {
            assert(exact_keys(ki)) by {
                assert forall|a: Row, b: Row| ki.contains(a) && ki.contains(b) implies (#[trigger] row_not_distinct(a, b) <==> a == b) by {
                    let i = choose|i: int| 0 <= i < ki.len() && ki[i] == a;
                    let j = choose|j: int| 0 <= j < ki.len() && ki[j] == b;
                    assert(keys[i] == a && keys[j] == b);
                }
            }
            lemma_group_members_mem(ki, ai, k);
        } else {
            // `k` is only the last key: no earlier member on either side.
            assert forall|i: int| 0 <= i < ki.len() implies !row_not_distinct(#[trigger] ki[i], k) || ki[i] == k by {
                assert(keys[i] == ki[i]);
                assert(keys.contains(ki[i]));
            }
            lemma_group_members_absent(ki, ai, k);
            lemma_mem_absent(ki, ai, k);
        }
    }
}

/// No key not distinct from `k`: no members.
proof fn lemma_group_members_absent(keys: Seq<Row>, args: Seq<Row>, k: Row)
    requires forall|i: int| 0 <= i < keys.len() ==> !row_not_distinct(#[trigger] keys[i], k) || keys[i] == k,
        !keys.contains(k),
    ensures group_members(keys, args, k) == Seq::<Row>::empty(),
    decreases keys.len(),
{
    if keys.len() > 0 && args.len() > 0 {
        let ki = keys.drop_last();
        assert forall|i: int| 0 <= i < ki.len() implies !row_not_distinct(#[trigger] ki[i], k) || ki[i] == k by {
            assert(ki[i] == keys[i]);
        }
        if ki.contains(k) {
            let i = choose|i: int| 0 <= i < ki.len() && ki[i] == k;
            assert(keys[i] == k);
        }
        lemma_group_members_absent(ki, args.drop_last(), k);
        assert(keys[keys.len() - 1] == keys.last());
        assert(keys.last() != k);
    }
}

/// `k` not among the keys: no `mem` members.
pub proof fn lemma_mem_absent(keys: Seq<Row>, args: Seq<Row>, k: Row)
    requires !keys.contains(k),
    ensures mem(keys, args, k) == Seq::<Row>::empty(),
    decreases keys.len(),
{
    if keys.len() > 0 && args.len() > 0 {
        let ki = keys.drop_last();
        if ki.contains(k) {
            let i = choose|i: int| 0 <= i < ki.len() && ki[i] == k;
            assert(keys[i] == k);
        }
        lemma_mem_absent(ki, args.drop_last(), k);
        assert(keys[keys.len() - 1] == keys.last());
    }
}

} // verus!
