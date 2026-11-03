//! Co-clustering of the scan model: under the storage's co-clustering flag, the stored orders row (`opos`) of the
//! stored lines' order keys never decreases (`clus_ok`), from `facts`' `cluster::clustered` over its stored rows.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::*;
use crate::spec::typing::*;
use crate::stores::facts::interface::*;
use crate::stores::facts::interface::common::colfmt::*;
use super::model::*;
use super::bind::*;

verus! {

// ------------------------------------------------------------------------------------------------ co-clustering

/// The order key of stored lineitem row `j` (column 0 of the stored rows the cluster flag talks about).
proof fn lemma_lrow_key(db: Database, p: Seq<PartView>, c: Cols, j: int)
    requires li_core(db, p, c), li_from_parts(c, p), 0 <= j < c.n_l,
    ensures
        lineitem_rows(ltp(p), lrel(db)).len() == c.n_l,
        lineitem_rows(ltp(p), lrel(db))[j][0] == Val::Int(lkey(c, j)),
{
    let t = ltp(p);
    let n = c.n_l as int;
    let sb = u64s(t[LI_LAYOUT as int])[1] as int;
    let gp = t[LI_GROUPS as int];
    let rows = lineitem_rows(t, lrel(db));
    assert(rows.len() == n);
    lemma_for_col(gp, n, sb, c.bs_l as int, t[LI_ORDERKEY_BASE as int], t[LI_ORDERKEY_CODES as int], j);
    assert(rows[j][0] == Val::Int(for_at(u64s(gp), t[LI_ORDERKEY_BASE as int], t[LI_ORDERKEY_CODES as int], j)));
}

/// The order key of stored orders row `q`.
proof fn lemma_orow_key(db: Database, p: Seq<PartView>, c: Cols, q: int)
    requires ord_core(db, p, c), ord_from_parts(c, p), 0 <= q < c.n_o,
    ensures
        orders_rows(otp(p), orel(db)).len() == c.n_o,
        orders_rows(otp(p), orel(db))[q][0] == Val::Int(okey(c, q)),
{
    let t = otp(p);
    let n = c.n_o as int;
    let sb = u64s(t[OR_LAYOUT as int])[1] as int;
    let gp = t[OR_GROUPS as int];
    let rows = orders_rows(t, orel(db));
    assert(rows.len() == n);
    lemma_for_col(gp, n, sb, c.bs_o as int, t[OR_ORDERKEY_BASE as int], t[OR_ORDERKEY_CODES as int], q);
    assert(rows[q][0] == Val::Int(for_at(u64s(gp), t[OR_ORDERKEY_BASE as int], t[OR_ORDERKEY_CODES as int], q)));
}

/// The storage's `order_pos` of an integer key is the model's `opos`.
proof fn lemma_order_pos(db: Database, p: Seq<PartView>, c: Cols, k: int)
    requires ord_core(db, p, c), ord_from_parts(c, p), keys_ok(c),
    ensures cluster::order_pos(orders_rows(otp(p), orel(db)), Val::Int(k)) == opos(c, k),
{
    reveal(opos);
    let orows = orders_rows(otp(p), orel(db));
    let n = c.n_o as int;
    assert(orows.len() == n) by {
        if n > 0 { lemma_orow_key(db, p, c, 0); } else { assert(orows.len() == n); }
    }
    let at = opos(c, k);
    if has_o(c, k) {
        let w = orow(c, k);
        assert(0 <= w < n && okey(c, w) == k);
        lemma_orow_key(db, p, c, w);
        assert forall|q: int| 0 <= q < n && q != w implies #[trigger] orows[q][0] != Val::Int(k) by {
            lemma_orow_key(db, p, c, q);
        }
        cluster::lemma_order_pos_at(orows, Val::Int(k), w);
    } else {
        assert forall|q: int| 0 <= q < n && q != n implies #[trigger] orows[q][0] != Val::Int(k) by {
            lemma_orow_key(db, p, c, q);
        }
        cluster::lemma_order_pos_at(orows, Val::Int(k), n);
    }
}

/// With the co-clustering flag set, the model is co-clustered (`clus_ok`).
pub proof fn lemma_clus(db: Database, p: Seq<PartView>, c: Cols)
    requires
        db.schema == crate::schema::schema_spec(), db_wf(db),
        represents(p, crate::stores::facts::declaration::stored_relations(db)),
        li_from_parts(c, p), ord_from_parts(c, p), keys_ok(c),
        p[FACTS_CLUSTER as int] is U64, u64s(p[FACTS_CLUSTER as int]).len() == 1,
        u64s(p[FACTS_CLUSTER as int])[0] == 1,
    ensures clus_ok(c),
{
    reveal(clus_ok);
    lemma_li_core(db, p, c);
    lemma_ord_core(db, p, c);
    let rels = crate::stores::facts::declaration::stored_relations(db);
    let lrows = lineitem_rows(ltp(p), lrel(db));
    let orows = orders_rows(otp(p), orel(db));
    assert(cluster::clustered(lrows, orows));
    assert forall|j: int| 0 <= j < c.n_l - 1 implies #[trigger] opos(c, lkey(c, j)) <= opos(c, lkey(c, j + 1)) by {
        lemma_lrow_key(db, p, c, j);
        lemma_lrow_key(db, p, c, j + 1);
        assert(cluster::cluster_step(lrows, orows, j));
        lemma_order_pos(db, p, c, lkey(c, j));
        lemma_order_pos(db, p, c, lkey(c, j + 1));
    }
}

} // verus!
