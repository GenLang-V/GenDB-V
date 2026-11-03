//! GROUP BY over an input made of blocks with one key each: when the input's key rows are block after block, every
//! row of block `i` equal to `k_i` and the `k_i` pairwise distinct (SQL "not distinct"), the groups
//! (`distinct_rows`) are the `k_i` in block order and the members of group `k_i` are block `i`'s argument rows
//! (`group_members`). Stated for one more block at the end (`lemma_distinct_append_block`,
//! `lemma_members_append`, `lemma_members_all`, `lemma_members_none`), so a proof over a left-recursive
//! relation (a LEFT JOIN, one block per left row) can follow its recursion.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::equality::*;
use crate::spec::relation::group_members;
use crate::bridge::equality::*;

verus! {

/// Every row of `b` is `k`.
pub open spec fn all_rows(b: Seq<Row>, k: Row) -> bool {
    forall|t: int| 0 <= t < b.len() ==> #[trigger] b[t] == k
}

/// `distinct_rows` of `a` followed by a non-empty block of copies of a key `k` that is not-distinct from no group
/// of `a`: the groups of `a`, then `k`.
pub proof fn lemma_distinct_append_block(a: Seq<Row>, b: Seq<Row>, k: Row)
    requires b.len() > 0, all_rows(b, k), !has_not_distinct(distinct_rows(a), k),
    ensures distinct_rows(a + b) == distinct_rows(a).push(k),
    decreases b.len(),
{
    let bi = b.drop_last();
    assert((a + b).drop_last() =~= a + bi);
    assert((a + b).last() == k);
    if bi.len() == 0 {
        assert(a + bi =~= a);
    } else {
        assert(all_rows(bi, k)) by {
            assert forall|t: int| 0 <= t < bi.len() implies #[trigger] bi[t] == k by { assert(bi[t] == b[t]); }
        }
        lemma_distinct_append_block(a, bi, k);
        let d = distinct_rows(a).push(k);
        lemma_row_not_distinct_refl(k);
        assert(d.last() == k);
        assert(has_not_distinct(d, k));
    }
}

/// `has_not_distinct` holds exactly when some row is not distinct from `k`.
pub proof fn lemma_has_not_distinct(d: Seq<Row>, k: Row)
    ensures has_not_distinct(d, k) <==> exists|t: int| 0 <= t < d.len() && row_not_distinct(#[trigger] d[t], k),
    decreases d.len(),
{
    if d.len() > 0 {
        lemma_has_not_distinct(d.drop_last(), k);
        if has_not_distinct(d.drop_last(), k) {
            let t = choose|t: int| 0 <= t < d.drop_last().len() && row_not_distinct(#[trigger] d.drop_last()[t], k);
            assert(d[t] == d.drop_last()[t]);
        }
        if exists|t: int| 0 <= t < d.len() && row_not_distinct(#[trigger] d[t], k) {
            let t = choose|t: int| 0 <= t < d.len() && row_not_distinct(#[trigger] d[t], k);
            if t < d.len() - 1 {
                assert(d.drop_last()[t] == d[t]);
            }
        }
    }
}

/// The members of a group over concatenated inputs are the members over each part.
pub proof fn lemma_members_append(ka: Seq<Row>, aa: Seq<Row>, kb: Seq<Row>, ab: Seq<Row>, k: Row)
    requires ka.len() == aa.len(), kb.len() == ab.len(),
    ensures group_members(ka + kb, aa + ab, k) == group_members(ka, aa, k) + group_members(kb, ab, k),
    decreases kb.len(),
{
    if kb.len() == 0 {
        assert(ka + kb =~= ka);
        assert(aa + ab =~= aa);
        assert(group_members(kb, ab, k) == Seq::<Row>::empty());
        assert(group_members(ka, aa, k) + Seq::<Row>::empty() =~= group_members(ka, aa, k));
    } else {
        let (kbi, abi) = (kb.drop_last(), ab.drop_last());
        lemma_members_append(ka, aa, kbi, abi, k);
        assert((ka + kb).drop_last() =~= ka + kbi);
        assert((aa + ab).drop_last() =~= aa + abi);
        assert((ka + kb).last() == kb.last());
        assert((aa + ab).last() == ab.last());
        let gi = group_members(ka, aa, k) + group_members(kbi, abi, k);
        if row_not_distinct(kb.last(), k) {
            assert(gi.push(ab.last()) =~= group_members(ka, aa, k) + group_members(kbi, abi, k).push(ab.last()));
        }
    }
}

/// Every key of the part is not-distinct from `k`: every argument row is a member.
pub proof fn lemma_members_all(kb: Seq<Row>, ab: Seq<Row>, k: Row)
    requires kb.len() == ab.len(), forall|t: int| 0 <= t < kb.len() ==> row_not_distinct(#[trigger] kb[t], k),
    ensures group_members(kb, ab, k) == ab,
    decreases kb.len(),
{
    if kb.len() == 0 {
        assert(ab =~= Seq::<Row>::empty());
    } else {
        let (kbi, abi) = (kb.drop_last(), ab.drop_last());
        assert forall|t: int| 0 <= t < kbi.len() implies row_not_distinct(#[trigger] kbi[t], k) by { assert(kbi[t] == kb[t]); }
        lemma_members_all(kbi, abi, k);
        assert(kb.last() == kb[kb.len() - 1]);
        assert(abi.push(ab.last()) =~= ab);
    }
}

/// No key of the part is not-distinct from `k`: no member.
pub proof fn lemma_members_none(kb: Seq<Row>, ab: Seq<Row>, k: Row)
    requires kb.len() == ab.len(), forall|t: int| 0 <= t < kb.len() ==> !row_not_distinct(#[trigger] kb[t], k),
    ensures group_members(kb, ab, k) == Seq::<Row>::empty(),
    decreases kb.len(),
{
    if kb.len() > 0 {
        let (kbi, abi) = (kb.drop_last(), ab.drop_last());
        assert forall|t: int| 0 <= t < kbi.len() implies !row_not_distinct(#[trigger] kbi[t], k) by { assert(kbi[t] == kb[t]); }
        lemma_members_none(kbi, abi, k);
        assert(kb.last() == kb[kb.len() - 1]);
    }
}

/// One-integer key rows are not-distinct exactly when equal.
pub proof fn lemma_int_keys(a: int, b: int)
    ensures row_not_distinct(seq![Val::Int(a)], seq![Val::Int(b)]) == (a == b),
{
    let (ra, rb) = (seq![Val::Int(a)], seq![Val::Int(b)]);
    if a == b {
        lemma_row_not_distinct_refl(ra);
    } else {
        assert(!val_not_distinct(ra[0], rb[0]));
    }
}

} // verus!
