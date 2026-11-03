//! Concatenation of a sequence of vectors (`vflat`), e.g. the per-task outputs of a parallel stage kept in task order
//! instead of being copied into one vector, with the facts needed to walk it by a (vector, index) cursor.
use vstd::prelude::*;

verus! {

/// The vectors' elements, in order.
pub open spec fn vflat<T>(bs: Seq<Vec<T>>) -> Seq<T>
    decreases bs.len(),
{
    if bs.len() == 0 { Seq::empty() } else { vflat(bs.drop_last()) + bs.last()@ }
}

/// Appending a vector appends its elements.
pub proof fn lemma_vflat_push<T>(bs: Seq<Vec<T>>, v: Vec<T>)
    ensures vflat(bs.push(v)) == vflat(bs) + v@,
{
    assert(bs.push(v).drop_last() =~= bs);
}

/// One more vector of the prefix: `vflat(bs[..i+1]) == vflat(bs[..i]) + bs[i]`.
pub proof fn lemma_vflat_take<T>(bs: Seq<Vec<T>>, i: int)
    requires 0 <= i < bs.len(),
    ensures vflat(bs.take(i + 1)) == vflat(bs.take(i)) + bs[i]@,
{
    assert(bs.take(i + 1).drop_last() =~= bs.take(i));
}

/// The flattening of a prefix is a prefix of the flattening.
pub proof fn lemma_vflat_prefix<T>(bs: Seq<Vec<T>>, i: int)
    requires 0 <= i <= bs.len(),
    ensures
        vflat(bs.take(i)).len() <= vflat(bs).len(),
        forall|k: int| 0 <= k < vflat(bs.take(i)).len() ==> #[trigger] vflat(bs.take(i))[k] == vflat(bs)[k],
    decreases bs.len() - i,
{
    if i == bs.len() {
        assert(bs.take(i) =~= bs);
    } else {
        lemma_vflat_prefix(bs, i + 1);
        lemma_vflat_take(bs, i);
        assert forall|k: int| 0 <= k < vflat(bs.take(i)).len() implies #[trigger] vflat(bs.take(i))[k] == vflat(bs)[k] by {
            assert(vflat(bs.take(i + 1))[k] == vflat(bs.take(i))[k]);
        }
    }
}

/// Element `j` of vector `i` sits at `|vflat(bs[..i])| + j`.
pub proof fn lemma_vflat_index<T>(bs: Seq<Vec<T>>, i: int, j: int)
    requires 0 <= i < bs.len(), 0 <= j < bs[i]@.len(),
    ensures
        vflat(bs.take(i)).len() + j < vflat(bs).len(),
        vflat(bs)[vflat(bs.take(i)).len() + j] == bs[i]@[j],
{
    lemma_vflat_take(bs, i);
    lemma_vflat_prefix(bs, i + 1);
    let k = vflat(bs.take(i)).len() + j;
    assert(vflat(bs.take(i + 1))[k] == bs[i]@[j]);
}

/// The whole sequence is its full prefix.
pub proof fn lemma_vflat_all<T>(bs: Seq<Vec<T>>)
    ensures vflat(bs.take(bs.len() as int)) == vflat(bs),
{
    assert(bs.take(bs.len() as int) =~= bs);
}

} // verus!
