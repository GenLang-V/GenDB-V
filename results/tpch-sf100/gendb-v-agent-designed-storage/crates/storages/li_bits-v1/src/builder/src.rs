//! What the builder reads from storage `facts`: the shapes of the lineitem parts it indexes (row groups,
//! frame-of-reference codes and bases of l_discount, l_quantity and l_shipdate), from facts' `represents`.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::part_len;
use crate::gendb_entry::sources::StoresView;
use crate::gendb_entry::sources_bound;
use crate::spec::value::{Database, Row};
use crate::stores::facts::interface as F;
use crate::stores::facts::interface::common::colfmt as FC;
use crate::stores::facts::declaration as FD;
use crate::stores::li_bits::declaration as D;
use crate::stores::li_bits::interface::{gsv, n_rows};

verus! {

/// An I64 base part with one entry per row group.
pub open spec fn base_ok(fp: Seq<PartView>, k: int) -> bool {
    fp[k] is I64 && FC::i64s(fp[k]).len() == gsv(fp).len() - 1
}

/// The shapes the builder relies on.
pub open spec fn src_ok(fp: Seq<PartView>) -> bool {
    let n = n_rows(fp);
    &&& fp.len() == F::FACTS_PARTS
    &&& fp[F::LI_GROUPS as int] is U64
    &&& FC::groups_wf(gsv(fp), n)
    &&& fp[F::LI_SHIPDATE_CODES as int] is U16
    &&& fp[F::LI_DISCOUNT_CODES as int] is U8 && part_len(fp[F::LI_DISCOUNT_CODES as int]) == n
    &&& fp[F::LI_QUANTITY_CODES as int] is U16 && part_len(fp[F::LI_QUANTITY_CODES as int]) == n
    &&& base_ok(fp, F::LI_SHIPDATE_BASE as int)
    &&& base_ok(fp, F::LI_DISCOUNT_BASE as int)
    &&& base_ok(fp, F::LI_QUANTITY_BASE as int)
}

/// The facts of facts' `represents` about the lineitem parts the builder reads.
proof fn lemma_li_parts(fp: Seq<PartView>, rels: Seq<Seq<Row>>)
    requires F::represents(fp, rels),
    ensures ({
        let tp = fp.subrange(F::LINEITEM_FIRST as int, (F::LINEITEM_FIRST + F::LI_PARTS) as int);
        let n = rels[0].len() as int;
        let srows = F::lineitem_rows(tp, rels[0]);
        &&& fp.len() == F::FACTS_PARTS
        &&& F::table_layout_ok(tp, n)
        &&& tp[F::LI_QUANTITY_CODES as int] is U16
        &&& FC::num_col_at(tp, F::LI_GROUPS as int, F::LI_QUANTITY_CODES as int, F::LI_QUANTITY_BASE as int, srows, 4, 2)
        &&& tp[F::LI_DISCOUNT_CODES as int] is U8
        &&& FC::num_col_at(tp, F::LI_GROUPS as int, F::LI_DISCOUNT_CODES as int, F::LI_DISCOUNT_BASE as int, srows, 6, 2)
        &&& tp[F::LI_SHIPDATE_CODES as int] is U16
        &&& FC::date_col_at(tp, F::LI_GROUPS as int, F::LI_SHIPDATE_CODES as int, F::LI_SHIPDATE_BASE as int, srows, 10)
    }),
{
}

/// The shapes, from facts' `represents`.
proof fn lemma_shapes(fp: Seq<PartView>, rels: Seq<Seq<Row>>)
    requires F::represents(fp, rels),
    ensures src_ok(fp),
{
    hide(F::represents);
    lemma_li_parts(fp, rels);
    let tp = fp.subrange(F::LINEITEM_FIRST as int, (F::LINEITEM_FIRST + F::LI_PARTS) as int);
    let n = rels[0].len() as int;
    assert forall|k: int| 0 <= k < 48 implies #[trigger] tp[k] == fp[k] by {}
    let bs = FC::u64s(tp[F::LI_LAYOUT as int])[1] as int;
    FC::lemma_uniform_groups(tp[F::LI_GROUPS as int], n, bs);
    assert(gsv(fp) == FC::gs_at(tp, F::LI_GROUPS as int));
    assert(tp[F::LI_SHIPDATE_CODES as int] == fp[F::LI_SHIPDATE_CODES as int]);
    assert(n_rows(fp) == n);
    assert(tp[F::LI_SHIPDATE_BASE as int] == fp[F::LI_SHIPDATE_BASE as int]);
    assert(tp[F::LI_DISCOUNT_BASE as int] == fp[F::LI_DISCOUNT_BASE as int]);
    assert(tp[F::LI_QUANTITY_BASE as int] == fp[F::LI_QUANTITY_BASE as int]);
    assert(tp[F::LI_DISCOUNT_CODES as int] == fp[F::LI_DISCOUNT_CODES as int]);
    assert(tp[F::LI_QUANTITY_CODES as int] == fp[F::LI_QUANTITY_CODES as int]);
}

/// For a database bound to `facts`: facts represents this storage's relations, and the shapes hold.
pub proof fn lemma_src(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures
        D::stored_relations(db) == FD::stored_relations(db),
        F::represents(sv.facts, D::stored_relations(db)),
        src_ok(sv.facts),
{
    hide(F::represents);
    let rels = FD::stored_relations(db);
    assert(D::stored_relations(db) =~= rels);
    assert(F::represents(sv.facts, rels));
    lemma_shapes(sv.facts, rels);
}

} // verus!
