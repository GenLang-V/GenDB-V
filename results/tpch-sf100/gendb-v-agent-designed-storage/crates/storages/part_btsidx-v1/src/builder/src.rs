//! What the builder reads from storage `custpart` (part, canonical row order), stated with this storage's interface
//! definitions over the source parts `cp`: for a database bound to the source, the layout and the shapes of the
//! p_partkey, p_brand, p_type and p_size columns, the values of every row, and p_size inside `i64` (`src_ok`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::sources::StoresView;
use crate::gendb_entry::sources_bound;
use crate::spec::value::{Database, Row, Val};
use crate::spec::int::{int_in_range, IntKind};
use crate::link::source::lemma_proj_all_index;
use crate::stores::custpart::interface as C;
use crate::stores::custpart::interface::common::colfmt as CF;
use crate::stores::custpart::interface::common::read as CR;
use crate::stores::custpart::declaration as CD;
use crate::stores::part_btsidx::declaration as D;
use crate::stores::part_btsidx::interface::*;

verus! {

/// Layout and column shapes over the source parts (as `pa_shape`, without the part count of this storage).
pub open spec fn base_ok(cp: Seq<PartView>, n: int) -> bool {
    let bs = bsize(cp);
    &&& cp.len() == CUSTPART_PARTS
    &&& cp[PA_LAYOUT as int] is U64 && u64s(cp[PA_LAYOUT as int]).len() == 2
    &&& n_rows(cp) == n
    &&& bs >= 1
    &&& cp[PA_PARTKEY_CODES as int] is U32 && cp[PA_PARTKEY_BASE as int] is I64
    &&& for_len_ok(u32s(cp[PA_PARTKEY_CODES as int]).len() as int, i64s(cp[PA_PARTKEY_BASE as int]).len() as int, n, bs)
    &&& cp[PA_SIZE_CODES as int] is U8 && cp[PA_SIZE_BASE as int] is I64
    &&& for_len_ok(u8s(cp[PA_SIZE_CODES as int]).len() as int, i64s(cp[PA_SIZE_BASE as int]).len() as int, n, bs)
    &&& cp[PA_BRAND_CODES as int] is U8 && cp[PA_BRAND_BASE as int] is U64
    &&& for_len_ok(u8s(cp[PA_BRAND_CODES as int]).len() as int, u64s(cp[PA_BRAND_BASE as int]).len() as int, n, bs)
    &&& cp[PA_TYPE_CODES as int] is U8 && cp[PA_TYPE_BASE as int] is U64
    &&& for_len_ok(u8s(cp[PA_TYPE_CODES as int]).len() as int, u64s(cp[PA_TYPE_BASE as int]).len() as int, n, bs)
    &&& cp[PA_BRAND_DOFFS as int] is U64 && cp[PA_BRAND_DBYTES as int] is U8
    &&& dict_ok(b_offs(cp), b_bytes(cp))
    &&& cp[PA_TYPE_DOFFS as int] is U64 && cp[PA_TYPE_DBYTES as int] is U8
    &&& dict_ok(t_offs(cp), t_bytes(cp))
    &&& forall|r: int| 0 <= r < n ==> i64::MIN <= #[trigger] size_at(cp, r) <= i64::MAX
}

/// Everything the builder uses about the source parts `cp` and this storage's relation `rel`.
pub open spec fn src_ok(cp: Seq<PartView>, rel: Seq<Row>) -> bool {
    &&& base_ok(cp, rel.len() as int)
    &&& rows_ok(cp, rel)
}

/// The part parts of custpart.
pub open spec fn pa_tp(cp: Seq<PartView>) -> Seq<PartView> {
    cp.subrange(C::PART_FIRST as int, (C::PART_FIRST + C::PA_PARTS) as int)
}

/// The conjuncts of custpart's `represents` about part that the builder reads.
pub open spec fn pa_conj(cp: Seq<PartView>, crel: Seq<Row>) -> bool {
    let tp = pa_tp(cp);
    &&& cp.len() == CUSTPART_PARTS
    &&& C::table_layout_ok(tp, crel.len() as int)
    &&& tp[C::PA_PARTKEY_CODES as int] is U32
    &&& CF::int_col_at(tp, C::PA_GROUPS as int, C::PA_PARTKEY_CODES as int, C::PA_PARTKEY_BASE as int, crel, 0)
    &&& tp[C::PA_BRAND_CODES as int] is U8
    &&& CF::dict_col_at(tp, C::PA_GROUPS as int, C::PA_BRAND_CODES as int, C::PA_BRAND_BASE as int, C::PA_BRAND_DICT_OFFS as int, C::PA_BRAND_DICT_BYTES as int, crel, 3)
    &&& tp[C::PA_SIZE_CODES as int] is U8
    &&& CF::int_col_at(tp, C::PA_GROUPS as int, C::PA_SIZE_CODES as int, C::PA_SIZE_BASE as int, crel, 5)
    &&& tp[C::PA_TYPE_CODES as int] is U8
    &&& CF::dict_col_at(tp, C::PA_GROUPS as int, C::PA_TYPE_CODES as int, C::PA_TYPE_BASE as int, C::PA_TYPE_DICT_OFFS as int, C::PA_TYPE_DICT_BYTES as int, crel, 4)
}

/// custpart's `represents` gives `pa_conj` (conjuncts only).
proof fn lemma_pa_conj(cp: Seq<PartView>, crels: Seq<Seq<Row>>)
    requires C::represents(cp, crels),
    ensures pa_conj(cp, crels[1]),
{
    let tp = pa_tp(cp);
    assert(C::part_ok(tp, crels[1]));
}

/// The part parts are parts 21 .. 50 of custpart.
proof fn lemma_tp(cp: Seq<PartView>)
    requires cp.len() == CUSTPART_PARTS,
    ensures forall|k: int| 0 <= k < 29 ==> #[trigger] pa_tp(cp)[k] == cp[21 + k],
{
}

/// The groups part of the part table (uniform groups of `bsize` rows).
pub open spec fn groups_ok(cp: Seq<PartView>, n: int) -> bool {
    CF::groups_part_ok(cp[22], n, bsize(cp))
}

/// A dictionary of `colfmt` (well-formed text parts) is a dictionary of this interface.
proof fn lemma_dict(o: Seq<u64>, y: Seq<u8>)
    requires o.len() >= 1, CF::text_parts_wf(o, y, o.len() - 1),
    ensures dict_ok(o, y),
{
    assert forall|i: int| 0 <= i < o.len() - 1 implies #[trigger] dict_range_ok(o, y, i) by {
        assert(CF::text_range_ok(o, y, i));
    }
}

/// Layout and column shapes.
proof fn lemma_src_shape(cp: Seq<PartView>, crel: Seq<Row>)
    requires pa_conj(cp, crel),
    ensures ({
        let n = crel.len() as int;
        let bs = bsize(cp);
        &&& cp[PA_LAYOUT as int] is U64 && u64s(cp[PA_LAYOUT as int]).len() == 2
        &&& n_rows(cp) == n
        &&& bs >= 1
        &&& cp[PA_PARTKEY_CODES as int] is U32 && cp[PA_PARTKEY_BASE as int] is I64
        &&& for_len_ok(u32s(cp[PA_PARTKEY_CODES as int]).len() as int, i64s(cp[PA_PARTKEY_BASE as int]).len() as int, n, bs)
        &&& cp[PA_SIZE_CODES as int] is U8 && cp[PA_SIZE_BASE as int] is I64
        &&& for_len_ok(u8s(cp[PA_SIZE_CODES as int]).len() as int, i64s(cp[PA_SIZE_BASE as int]).len() as int, n, bs)
        &&& cp[PA_BRAND_CODES as int] is U8 && cp[PA_BRAND_BASE as int] is U64
        &&& for_len_ok(u8s(cp[PA_BRAND_CODES as int]).len() as int, u64s(cp[PA_BRAND_BASE as int]).len() as int, n, bs)
        &&& cp[PA_TYPE_CODES as int] is U8 && cp[PA_TYPE_BASE as int] is U64
        &&& for_len_ok(u8s(cp[PA_TYPE_CODES as int]).len() as int, u64s(cp[PA_TYPE_BASE as int]).len() as int, n, bs)
        &&& cp[PA_BRAND_DOFFS as int] is U64 && cp[PA_BRAND_DBYTES as int] is U8
        &&& dict_ok(b_offs(cp), b_bytes(cp))
        &&& cp[PA_TYPE_DOFFS as int] is U64 && cp[PA_TYPE_DBYTES as int] is U8
        &&& dict_ok(t_offs(cp), t_bytes(cp))
        &&& groups_ok(cp, n)
    }),
{
    hide(CF::int_col);
    hide(CF::dict_col);
    let tp = pa_tp(cp);
    lemma_tp(cp);
    let n = crel.len() as int;
    let gp = tp[C::PA_GROUPS as int];
    let bs = bsize(cp);
    assert(tp[C::PA_LAYOUT as int] == cp[PA_LAYOUT as int]);
    assert(CF::groups_part_ok(gp, n, bs));
    CF::lemma_uniform_groups(gp, n, bs);
    CF::lemma_nblocks(n, bs);
    assert(tp[C::PA_PARTKEY_BASE as int] == cp[PA_PARTKEY_BASE as int]);
    assert(tp[C::PA_PARTKEY_CODES as int] == cp[PA_PARTKEY_CODES as int]);
    assert(tp[C::PA_SIZE_BASE as int] == cp[PA_SIZE_BASE as int]);
    assert(tp[C::PA_SIZE_CODES as int] == cp[PA_SIZE_CODES as int]);
    assert(tp[C::PA_BRAND_BASE as int] == cp[PA_BRAND_BASE as int]);
    assert(tp[C::PA_BRAND_CODES as int] == cp[PA_BRAND_CODES as int]);
    assert(tp[C::PA_TYPE_BASE as int] == cp[PA_TYPE_BASE as int]);
    assert(tp[C::PA_TYPE_CODES as int] == cp[PA_TYPE_CODES as int]);
    assert(tp[C::PA_BRAND_DICT_OFFS as int] == cp[PA_BRAND_DOFFS as int]);
    assert(tp[C::PA_BRAND_DICT_BYTES as int] == cp[PA_BRAND_DBYTES as int]);
    assert(tp[C::PA_TYPE_DICT_OFFS as int] == cp[PA_TYPE_DOFFS as int]);
    assert(tp[C::PA_TYPE_DICT_BYTES as int] == cp[PA_TYPE_DBYTES as int]);
    assert(CF::for_i64_shape(tp, C::PA_GROUPS as int, C::PA_PARTKEY_CODES as int, C::PA_PARTKEY_BASE as int, n));
    assert(CF::for_i64_shape(tp, C::PA_GROUPS as int, C::PA_SIZE_CODES as int, C::PA_SIZE_BASE as int, n));
    assert(CF::for_u64_shape(tp, C::PA_GROUPS as int, C::PA_BRAND_CODES as int, C::PA_BRAND_BASE as int, n));
    assert(CF::for_u64_shape(tp, C::PA_GROUPS as int, C::PA_TYPE_CODES as int, C::PA_TYPE_BASE as int, n));
    lemma_dict(b_offs(cp), b_bytes(cp));
    lemma_dict(t_offs(cp), t_bytes(cp));
}

/// The values of every row, and p_size inside `i64`.
proof fn lemma_src_rows(cp: Seq<PartView>, crel: Seq<Row>, rel: Seq<Row>, t3: Seq<Row>)
    requires
        pa_conj(cp, crel),
        crel == crate::link::query::proj_all(t3, CD::stored_cols_t1()),
        rel == crate::link::query::proj_all(t3, D::stored_cols_t0()),
        crate::link::source::rows_in_columns(rel, D::stored_columns_t0()),
    ensures
        rows_ok(cp, rel),
        forall|r: int| 0 <= r < rel.len() ==> i64::MIN <= #[trigger] size_at(cp, r) <= i64::MAX,
{
    let tp = pa_tp(cp);
    lemma_tp(cp);
    lemma_proj_all_index(t3, CD::stored_cols_t1());
    lemma_proj_all_index(t3, D::stored_cols_t0());
    let n = crel.len() as int;
    let gp = tp[C::PA_GROUPS as int];
    let gs = CF::u64s(gp);
    let bs = bsize(cp);
    assert(tp[C::PA_LAYOUT as int] == cp[PA_LAYOUT as int]);
    assert(CF::groups_part_ok(gp, n, bs));
    let (kb, kc) = (tp[C::PA_PARTKEY_BASE as int], tp[C::PA_PARTKEY_CODES as int]);
    let (zb, zc) = (tp[C::PA_SIZE_BASE as int], tp[C::PA_SIZE_CODES as int]);
    let (bb, bc) = (tp[C::PA_BRAND_BASE as int], tp[C::PA_BRAND_CODES as int]);
    let (ob, oc) = (tp[C::PA_TYPE_BASE as int], tp[C::PA_TYPE_CODES as int]);
    assert(kb == cp[PA_PARTKEY_BASE as int] && kc == cp[PA_PARTKEY_CODES as int]);
    assert(zb == cp[PA_SIZE_BASE as int] && zc == cp[PA_SIZE_CODES as int]);
    assert(bb == cp[PA_BRAND_BASE as int] && bc == cp[PA_BRAND_CODES as int]);
    assert(ob == cp[PA_TYPE_BASE as int] && oc == cp[PA_TYPE_CODES as int]);
    let (bo, by) = (CF::u64s(tp[C::PA_BRAND_DICT_OFFS as int]), CF::u8s(tp[C::PA_BRAND_DICT_BYTES as int]));
    let (co, cy) = (CF::u64s(tp[C::PA_TYPE_DICT_OFFS as int]), CF::u8s(tp[C::PA_TYPE_DICT_BYTES as int]));
    assert(bo == b_offs(cp) && by == b_bytes(cp));
    assert(co == t_offs(cp) && cy == t_bytes(cp));
    assert(CF::int_col(crel, 0, gs, kb, kc));
    assert(CF::dict_col(crel, 3, gs, bb, bc, bo, by));
    assert(CF::int_col(crel, 5, gs, zb, zc));
    assert(CF::dict_col(crel, 4, gs, ob, oc, co, cy));
    assert forall|r: int| 0 <= r < rel.len() implies #[trigger] rel[r] == row_at(cp, r) && dict_idx_ok(cp, r)
        && i64::MIN <= size_at(cp, r) <= i64::MAX by {
        CR::lemma_for_row(gp, n, bs, kb, kc, r);
        CR::lemma_for_row(gp, n, bs, zb, zc, r);
        CR::lemma_for_row(gp, n, bs, bb, bc, r);
        CR::lemma_for_row(gp, n, bs, ob, oc, r);
        assert(crel[r][0] == Val::Int(pkey_at(cp, r)));
        assert(CF::for_at(gs, bb, bc, r) == bi_at(cp, r));
        assert(CF::for_at(gs, ob, oc, r) == ti_at(cp, r));
        assert(crel[r][3] == Val::Text(b_text(cp, bi_at(cp, r))));
        assert(crel[r][5] == Val::Int(size_at(cp, r)));
        assert(crel[r][4] == Val::Text(t_text(cp, ti_at(cp, r))));
        assert(rel[r][0] == t3[r][0] && crel[r][0] == t3[r][0]);
        assert(rel[r][1] == t3[r][3] && crel[r][3] == t3[r][3]);
        assert(rel[r][2] == t3[r][4] && crel[r][4] == t3[r][4]);
        assert(rel[r][3] == t3[r][5] && crel[r][5] == t3[r][5]);
        assert(rel[r].len() == 4);
        assert(rel[r] =~= row_at(cp, r));
        assert(crate::spec::typing::value_in_column(rel[r][3], D::stored_columns_t0()[3]));
    }
    assert forall|r: int| 0 <= r < rel.len() implies #[trigger] dict_idx_ok(cp, r) by {
        assert(rel[r] == row_at(cp, r));
    }
    assert forall|r: int| 0 <= r < rel.len() implies i64::MIN <= #[trigger] size_at(cp, r) <= i64::MAX by {
        assert(rel[r] == row_at(cp, r));
    }
}

/// For a database bound to `custpart`, its parts and this storage's relation meet `src_ok`.
pub proof fn lemma_src(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures src_ok(sv.custpart, D::stored_relations(db)[0]), groups_ok(sv.custpart, D::stored_relations(db)[0].len() as int),
{
    hide(pa_conj);
    let cp = sv.custpart;
    let crels = CD::stored_relations(db);
    assert(C::represents(cp, crels));
    lemma_pa_conj(cp, crels);
    let t3 = db.tables[3];
    let rel = D::stored_relations(db)[0];
    D::lemma_stored_relations(db);
    lemma_proj_all_index(t3, CD::stored_cols_t1());
    lemma_proj_all_index(t3, D::stored_cols_t0());
    assert(rel.len() == crels[1].len());
    lemma_src_shape(cp, crels[1]);
    lemma_src_rows(cp, crels[1], rel, t3);
}

} // verus!
