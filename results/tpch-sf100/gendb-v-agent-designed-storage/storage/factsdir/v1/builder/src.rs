//! What the builder reads from storage `facts`, stated over the source parts `fp` with this storage's definitions:
//! the shapes of the parts it requests, the l_partkey key index as the directory scan needs it (`idx_src_ok`, under
//! kind 2) and the o_orderkey column (`okey_src_ok`). Derived from facts' `represents` for a bound database
//! (`lemma_src`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::sources::StoresView;
use crate::gendb_entry::sources_bound;
use crate::gendb_entry::stored::part_len;
use crate::gendb_entry::storage::stored_relations;
use crate::spec::value::{Database, Row};
use crate::stores::facts::interface as F;
use crate::stores::facts::interface::common::colfmt as FC;
use crate::stores::facts::interface::common::keyidx as FK;
use crate::stores::facts::declaration as FD;
use crate::stores::factsdir::interface as M;
use crate::stores::factsdir::interface::common::colfmt::{u32s, u64s, i64s};
use crate::stores::factsdir::interface::dirs::*;
use super::pdir::{idx_src_ok, idx_sorted_at};
use super::odir::okey_src_ok;

verus! {

/// Lineitem rows of the source (its layout part).
pub open spec fn li_rows_of(fp: Seq<PartView>) -> int {
    u64s(fp[M::LI_LAYOUT as int])[0] as int
}

/// Orders rows of the source (its layout part).
pub open spec fn or_rows_of(fp: Seq<PartView>) -> int {
    u64s(fp[(M::ORDERS_FIRST + M::OR_LAYOUT) as int])[0] as int
}

/// The source facts the build reads.
pub open spec fn src_facts(fp: Seq<PartView>) -> bool {
    let nl = li_rows_of(fp);
    let no = or_rows_of(fp);
    &&& fp.len() == M::FACTS_PARTS
    &&& fp[M::LI_LAYOUT as int] is U64 && u64s(fp[M::LI_LAYOUT as int]).len() == 2
    &&& fp[M::LI_PARTKEY_CODES as int] is U32 && part_len(fp[M::LI_PARTKEY_CODES as int]) == nl
    &&& fp[M::LI_PARTKEY_BASE as int] is I64
    &&& fp[M::LI_KEYIDX_CODES as int] is U32 && fp[M::LI_KEYIDX_BASE as int] is U64
    &&& fp[M::LI_KEYIDX_KIND as int] is U64 && u64s(fp[M::LI_KEYIDX_KIND as int]).len() == 1
    &&& u64s(fp[M::LI_KEYIDX_KIND as int])[0] == 2 ==> part_len(fp[M::LI_KEYIDX_CODES as int]) == nl && idx_src_ok(fp, nl)
    &&& fp[(M::ORDERS_FIRST + M::OR_LAYOUT) as int] is U64 && u64s(fp[(M::ORDERS_FIRST + M::OR_LAYOUT) as int]).len() == 2
    &&& fp[(M::ORDERS_FIRST + M::OR_ORDERKEY_CODES) as int] is U32
    &&& part_len(fp[(M::ORDERS_FIRST + M::OR_ORDERKEY_CODES) as int]) == no
    &&& fp[(M::ORDERS_FIRST + M::OR_ORDERKEY_BASE) as int] is I64
    &&& okey_src_ok(fp, no)
}

/// The lineitem parts of facts.
pub open spec fn li_tp(fp: Seq<PartView>) -> Seq<PartView> {
    fp.subrange(F::LINEITEM_FIRST as int, (F::LINEITEM_FIRST + F::LI_PARTS) as int)
}

/// The orders parts of facts.
pub open spec fn or_tp(fp: Seq<PartView>) -> Seq<PartView> {
    fp.subrange(F::ORDERS_FIRST as int, (F::ORDERS_FIRST + F::OR_PARTS) as int)
}

/// One base per block: the bases cover the rows.
proof fn lemma_bases_cover(tp: Seq<PartView>, n: int, cp: int, bp: int)
    requires
        FC::groups_part_ok(tp[1], n, FC::u64s(tp[0])[1] as int),
        FC::for_shape(FC::gs_at(tp, 1), tp[bp], tp[cp], n),
    ensures
        part_len(tp[bp]) * (FC::u64s(tp[0])[1] as int) >= n,
        FC::u64s(tp[0])[1] as int >= 1,
{
    let bs = FC::u64s(tp[0])[1] as int;
    FC::lemma_uniform_groups(tp[1], n, bs);
    FC::lemma_nblocks(n, bs);
}

/// The lineitem facts the build reads.
proof fn lemma_src_li(fp: Seq<PartView>, rel: Seq<Row>)
    requires
        fp.len() == M::FACTS_PARTS,
        F::lineitem_ok(li_tp(fp), rel),
    ensures
        li_rows_of(fp) == rel.len(),
        fp[M::LI_LAYOUT as int] is U64 && u64s(fp[M::LI_LAYOUT as int]).len() == 2,
        fp[M::LI_PARTKEY_CODES as int] is U32 && part_len(fp[M::LI_PARTKEY_CODES as int]) == rel.len(),
        fp[M::LI_PARTKEY_BASE as int] is I64,
        fp[M::LI_KEYIDX_CODES as int] is U32 && fp[M::LI_KEYIDX_BASE as int] is U64,
        fp[M::LI_KEYIDX_KIND as int] is U64 && u64s(fp[M::LI_KEYIDX_KIND as int]).len() == 1,
        u64s(fp[M::LI_KEYIDX_KIND as int])[0] == 2 ==> part_len(fp[M::LI_KEYIDX_CODES as int]) == rel.len()
            && idx_src_ok(fp, rel.len() as int),
{
    let tp = li_tp(fp);
    let n = rel.len() as int;
    assert forall|k: int| 0 <= k < 48 implies #[trigger] tp[k] == fp[k] by {}
    let bs = FC::u64s(tp[0])[1] as int;
    assert(F::table_layout_ok(tp, n));
    let srows = F::lineitem_rows(tp, rel);
    assert(F::lineitem_cols_ok(tp, srows));
    assert(srows.len() == n);
    assert(FC::int_col_at(tp, 1, 6, 7, srows, 1));
    lemma_bases_cover(tp, n, 6, 7);
    let kind = FC::u64s(tp[47])[0];
    let (kc, kb, ic, ib) = (FC::u32s(tp[6]), FC::i64s(tp[7]), FC::u32s(tp[45]), FC::u64s(tp[46]));
    assert(FK::keyidx_ok(kc, kb, ic, ib, bs, kind, n));
    if kind == 2 {
        let im = FK::idx_map(ic, ib, bs, n);
        assert(FC::is_perm(im, n));
        assert forall|p: int| 0 <= p < n implies 0 <= #[trigger] pdir_irow(fp, p) < n by {
            assert(im[p] == FK::fidx(ic, ib, bs, p));
        }
        assert forall|p: int| 0 <= p < n - 1 implies #[trigger] idx_sorted_at(fp, p) by {
            assert(FK::sorted_at(kc, kb, ic, ib, bs, kind, p));
        }
    }
}

/// The orders facts the build reads.
proof fn lemma_src_or(fp: Seq<PartView>, rel: Seq<Row>)
    requires
        fp.len() == M::FACTS_PARTS,
        F::orders_ok(or_tp(fp), rel),
    ensures
        or_rows_of(fp) == rel.len(),
        fp[(M::ORDERS_FIRST + M::OR_LAYOUT) as int] is U64 && u64s(fp[(M::ORDERS_FIRST + M::OR_LAYOUT) as int]).len() == 2,
        fp[(M::ORDERS_FIRST + M::OR_ORDERKEY_CODES) as int] is U32,
        part_len(fp[(M::ORDERS_FIRST + M::OR_ORDERKEY_CODES) as int]) == rel.len(),
        fp[(M::ORDERS_FIRST + M::OR_ORDERKEY_BASE) as int] is I64,
        okey_src_ok(fp, rel.len() as int),
{
    let tp = or_tp(fp);
    let n = rel.len() as int;
    assert forall|k: int| 0 <= k < 26 implies #[trigger] tp[k] == fp[48 + k] by {}
    assert(F::table_layout_ok(tp, n));
    let srows = F::orders_rows(tp, rel);
    assert(F::orders_cols_ok(tp, srows));
    assert(srows.len() == n);
    assert(FC::int_col_at(tp, 1, 4, 5, srows, 0));
    lemma_bases_cover(tp, n, 4, 5);
}

/// For a database bound to `facts`, its parts meet `src_facts`, with the row counts of the stored relations.
pub proof fn lemma_src(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures
        src_facts(sv.facts),
        li_rows_of(sv.facts) == stored_relations(db)[0].len(),
        or_rows_of(sv.facts) == stored_relations(db)[1].len(),
        stored_relations(db) == FD::stored_relations(db),
{
    let fp = sv.facts;
    let frels = FD::stored_relations(db);
    assert(F::represents(fp, frels));
    assert(stored_relations(db) =~= frels);
    lemma_src_li(fp, frels[0]);
    lemma_src_or(fp, frels[1]);
}

} // verus!
