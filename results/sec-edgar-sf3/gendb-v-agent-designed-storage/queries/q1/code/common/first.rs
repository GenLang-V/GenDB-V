//! First-occurrence order of the group keys of the link toolkit's normal form (`link::query::gkeys`): the keys of
//! a prefix of the rows are a prefix of the keys, so a key with a qualifying row at position `ja`, where another
//! key has none at or before `ja`, comes first. This locates the first failing group of a GROUP BY without
//! materializing the canonical group order.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::link::query::*;

verus! {

/// A qualifying row of group `k` at position `j` makes the group's count positive.
pub proof fn lemma_count_pos(g: QuerySpec, rows: Seq<Row>, k: Row, j: int)
    requires 0 <= j < rows.len(), hit(g, rows[j], k),
    ensures gcount(g, rows, k) > 0,
    decreases rows.len(),
{
    if j < rows.len() - 1 {
        let init = rows.drop_last();
        assert(init[j] == rows[j]);
        lemma_count_pos(g, init, k, j);
    }
}

/// No qualifying row of group `k`: its count is 0.
pub proof fn lemma_count_zero(g: QuerySpec, rows: Seq<Row>, k: Row)
    requires forall|j: int| 0 <= j < rows.len() ==> !hit(g, #[trigger] rows[j], k),
    ensures gcount(g, rows, k) == 0,
    decreases rows.len(),
{
    if rows.len() > 0 {
        let init = rows.drop_last();
        assert forall|j: int| 0 <= j < init.len() implies !hit(g, #[trigger] init[j], k) by {
            assert(init[j] == rows[j]);
        }
        lemma_count_zero(g, init, k);
        assert(!hit(g, rows[rows.len() - 1], k));
    }
}

/// The group keys of the first `m` rows are a prefix of the group keys.
pub proof fn lemma_gkeys_prefix(g: QuerySpec, rows: Seq<Row>, m: int)
    requires 0 <= m <= rows.len(),
    ensures
        gkeys(g, rows.take(m)).len() <= gkeys(g, rows).len(),
        gkeys(g, rows.take(m)) == gkeys(g, rows).take(gkeys(g, rows.take(m)).len() as int),
    decreases rows.len(),
{
    if m < rows.len() {
        let init = rows.drop_last();
        assert(rows.take(m) =~= init.take(m));
        lemma_gkeys_prefix(g, init, m);
        let a = gkeys(g, init.take(m));
        let b = gkeys(g, init);
        let c = gkeys(g, rows);
        assert(b.take(a.len() as int) == a);
        assert(c == b || c == b.push((g.key)(rows.last())));
        assert(c.take(a.len() as int) =~= b.take(a.len() as int));
    } else {
        assert(rows.take(m) =~= rows);
        assert(gkeys(g, rows).take(gkeys(g, rows).len() as int) =~= gkeys(g, rows));
    }
}

/// Key `a` has a qualifying row at `ja` and key `b` none at or before `ja`: `a` comes before `b` in `gkeys`.
pub proof fn lemma_gkeys_order(g: QuerySpec, rows: Seq<Row>, a: Row, b: Row, ja: int, ia: int, ib: int)
    requires
        0 <= ja < rows.len(),
        hit(g, rows[ja], a),
        forall|j: int| 0 <= j <= ja ==> !hit(g, #[trigger] rows[j], b),
        0 <= ia < gkeys(g, rows).len(), gkeys(g, rows)[ia] == a,
        0 <= ib < gkeys(g, rows).len(), gkeys(g, rows)[ib] == b,
    ensures ia < ib,
{
    let pre = rows.take(ja + 1);
    let ks = gkeys(g, rows);
    let pk = gkeys(g, pre);
    assert(pre[ja] == rows[ja]);
    lemma_count_pos(g, pre, a, ja);
    assert forall|j: int| 0 <= j < pre.len() implies !hit(g, #[trigger] pre[j], b) by {
        assert(pre[j] == rows[j]);
    }
    lemma_count_zero(g, pre, b);
    lemma_gkeys(g, pre);
    lemma_gkeys(g, rows);
    lemma_gkeys_prefix(g, rows, ja + 1);
    assert(pk.contains(a));
    let ia2 = choose|i: int| 0 <= i < pk.len() && pk[i] == a;
    assert(ks[ia2] == a);
    assert(ia2 == ia);
    if ib < pk.len() {
        assert(pk[ib] == b);
        assert(pk.contains(b));
    }
}

} // verus!
