//! Co-clustering of lineitem with orders in storage `facts`. When the cluster flag (part `FACTS_CLUSTER`, U64 `[1]`)
//! is set, the stored lineitem rows never go back in the stored order of their orders: `order_pos` of each row's
//! l_orderkey (the first stored orders row with that o_orderkey, or the number of orders rows when there is none)
//! is nondecreasing along the stored lineitem rows (`clustered`). Nothing cross-table is stored: the flag is one
//! bit about the order the builder chose, which it checked at build time. Under the declared primary key of
//! orders, `order_pos` is the position of the one matching orders row (`lemma_order_pos_at`), so the lineitem rows
//! of a stored range of orders rows form a contiguous stored range, which a query finds by binary search over
//! lineitem rows, computing `order_pos` with the orders key index (`keyidx::key_find`).
use vstd::prelude::*;
use crate::spec::value::{Row, Val};

verus! {

/// The first stored orders row at or after `i` whose column 0 (o_orderkey) is `k`, or `orows.len()` if none.
pub open spec fn first_key_from(orows: Seq<Row>, k: Val, i: int) -> int
    decreases orows.len() - i,
{
    if i < 0 || i >= orows.len() {
        orows.len() as int
    } else if orows[i][0] == k {
        i
    } else {
        first_key_from(orows, k, i + 1)
    }
}

/// The stored position of the orders row of a lineitem key `k`: the first stored orders row with o_orderkey `k`,
/// or `orows.len()` when no orders row has it.
pub open spec fn order_pos(orows: Seq<Row>, k: Val) -> int {
    first_key_from(orows, k, 0)
}

/// Stored lineitem row `j` comes no later, in orders order, than row `j + 1`.
pub open spec fn cluster_step(lrows: Seq<Row>, orows: Seq<Row>, j: int) -> bool {
    order_pos(orows, lrows[j][0]) <= order_pos(orows, lrows[j + 1][0])
}

/// The stored lineitem rows follow the stored orders order (by their l_orderkey, column 0).
pub open spec fn clustered(lrows: Seq<Row>, orows: Seq<Row>) -> bool {
    forall|j: int| 0 <= j < lrows.len() - 1 ==> #[trigger] cluster_step(lrows, orows, j)
}

/// `order_pos` is nondecreasing between any two stored lineitem rows of a clustered order.
pub proof fn lemma_clustered_le(lrows: Seq<Row>, orows: Seq<Row>, a: int, b: int)
    requires
        clustered(lrows, orows),
        0 <= a <= b < lrows.len(),
    ensures
        order_pos(orows, lrows[a][0]) <= order_pos(orows, lrows[b][0]),
    decreases b - a,
{
    if a < b {
        lemma_clustered_le(lrows, orows, a, b - 1);
        assert(cluster_step(lrows, orows, b - 1));
    }
}

proof fn lemma_first_key_from(orows: Seq<Row>, k: Val, i: int, p: int)
    requires
        0 <= i <= p <= orows.len(),
        p < orows.len() ==> orows[p][0] == k,
        forall|q: int| i <= q < p ==> #[trigger] orows[q][0] != k,
    ensures
        first_key_from(orows, k, i) == p,
    decreases p - i,
{
    if i < p {
        lemma_first_key_from(orows, k, i + 1, p);
    }
}

/// When stored orders row `p` is the only one with key `k` (as under the primary key of orders), `order_pos` is `p`;
/// when no row has key `k`, it is `orows.len()`.
pub proof fn lemma_order_pos_at(orows: Seq<Row>, k: Val, p: int)
    requires
        0 <= p <= orows.len(),
        p < orows.len() ==> orows[p][0] == k,
        forall|q: int| 0 <= q < orows.len() && q != p ==> #[trigger] orows[q][0] != k,
    ensures
        order_pos(orows, k) == p,
{
    lemma_first_key_from(orows, k, 0, p);
}

/// `order_pos` lies in `[0, orows.len()]`.
pub proof fn lemma_order_pos_bound(orows: Seq<Row>, k: Val)
    ensures
        0 <= order_pos(orows, k) <= orows.len(),
{
    lemma_first_key_from_bound(orows, k, 0);
}

proof fn lemma_first_key_from_bound(orows: Seq<Row>, k: Val, i: int)
    requires 0 <= i,
    ensures i <= first_key_from(orows, k, i) <= orows.len() || (i > orows.len() && first_key_from(orows, k, i) == orows.len()),
        0 <= first_key_from(orows, k, i) <= orows.len(),
    decreases orows.len() - i,
{
    if i < orows.len() && orows[i][0] != k {
        lemma_first_key_from_bound(orows, k, i + 1);
    }
}

} // verus!
