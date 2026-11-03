//! What the builder reads from storage `custpart` (part, canonical row order), stated with this storage's interface
//! definitions over the source parts `cp`: for a database bound to the source, the layout, the p_partkey and p_name
//! column shapes, and the values of every row (`src_ok`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::sources::StoresView;
use crate::gendb_entry::sources_bound;
use crate::gendb_entry::stored::part_len;
use crate::spec::value::{Database, Row, Val};
use crate::link::source::lemma_proj_all_index;
use crate::stores::custpart::interface as C;
use crate::stores::custpart::interface::common::colfmt as CF;
use crate::stores::custpart::interface::common::read as CR;
use crate::stores::custpart::declaration as CD;
use crate::stores::part_nameidx::declaration as D;
use crate::stores::part_nameidx::interface::*;

verus! {

/// Everything the builder uses about the source parts `cp` and this storage's relation `rel`.
pub open spec fn src_ok(cp: Seq<PartView>, rel: Seq<Row>) -> bool {
    let n = rel.len() as int;
    &&& cp.len() == CUSTPART_PARTS
    &&& cp[PA_LAYOUT as int] is U64 && u64s(cp[PA_LAYOUT as int]).len() == 2
    &&& n_rows(cp) == n
    &&& bsize(cp) >= 1
    &&& cp[PA_PARTKEY_CODES as int] is U32 && u32s(cp[PA_PARTKEY_CODES as int]).len() == n
    &&& cp[PA_PARTKEY_BASE as int] is I64 && i64s(cp[PA_PARTKEY_BASE as int]).len() * bsize(cp) >= n
    &&& cp[PA_NAME_OFFS as int] is U64 && name_offs(cp).len() == n + 1
    &&& cp[PA_NAME_BYTES as int] is U8
    &&& forall|r: int| 0 <= r < n ==> #[trigger] name_range_ok(cp, r)
    &&& rows_ok(cp, rel)
}

/// The conjuncts of custpart's `represents` about part that the builder reads.
pub open spec fn pa_conj(cp: Seq<PartView>, crel: Seq<Row>) -> bool {
    let tp = cp.subrange(C::PART_FIRST as int, (C::PART_FIRST + C::PA_PARTS) as int);
    &&& cp.len() == CUSTPART_PARTS
    &&& C::table_layout_ok(tp, crel.len() as int)
    &&& CF::int_col_at(tp, C::PA_GROUPS as int, C::PA_PARTKEY_CODES as int, C::PA_PARTKEY_BASE as int, crel, 0)
    &&& tp[C::PA_PARTKEY_CODES as int] is U32
    &&& CF::text_col_at(tp, C::PA_NAME_OFFS as int, C::PA_NAME_BYTES as int, crel, 1)
}

/// custpart's `represents` gives `pa_conj` (conjuncts only).
proof fn lemma_pa_conj(cp: Seq<PartView>, crels: Seq<Seq<Row>>)
    requires C::represents(cp, crels),
    ensures pa_conj(cp, crels[1]),
{
    let tp = cp.subrange(C::PART_FIRST as int, (C::PART_FIRST + C::PA_PARTS) as int);
    assert(C::part_ok(tp, crels[1]));
}

/// The part parts are parts 21 .. 50 of custpart.
proof fn lemma_tp(cp: Seq<PartView>)
    requires cp.len() == CUSTPART_PARTS,
    ensures forall|k: int| 0 <= k < 29 ==> #[trigger] cp.subrange(21, 50)[k] == cp[21 + k],
{
}

/// Layout and column shapes.
proof fn lemma_src_shape(cp: Seq<PartView>, crel: Seq<Row>)
    requires pa_conj(cp, crel),
    ensures ({
        let n = crel.len() as int;
        &&& cp[PA_LAYOUT as int] is U64 && u64s(cp[PA_LAYOUT as int]).len() == 2
        &&& n_rows(cp) == n
        &&& bsize(cp) >= 1
        &&& cp[PA_PARTKEY_CODES as int] is U32 && u32s(cp[PA_PARTKEY_CODES as int]).len() == n
        &&& cp[PA_PARTKEY_BASE as int] is I64 && i64s(cp[PA_PARTKEY_BASE as int]).len() * bsize(cp) >= n
        &&& cp[PA_NAME_OFFS as int] is U64 && name_offs(cp).len() == n + 1
        &&& cp[PA_NAME_BYTES as int] is U8
        &&& forall|r: int| 0 <= r < n ==> #[trigger] name_range_ok(cp, r)
        &&& FC_groups(cp, n)
    }),
{
    hide(CF::int_col);
    hide(CF::text_col);
    let tp = cp.subrange(C::PART_FIRST as int, (C::PART_FIRST + C::PA_PARTS) as int);
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
    assert(tp[C::PA_NAME_OFFS as int] == cp[PA_NAME_OFFS as int]);
    assert(tp[C::PA_NAME_BYTES as int] == cp[PA_NAME_BYTES as int]);
    assert(part_len(tp[C::PA_PARTKEY_BASE as int]) == CF::u64s(gp).len() - 1);
    let (o, y) = (CF::u64s(tp[C::PA_NAME_OFFS as int]), CF::u8s(tp[C::PA_NAME_BYTES as int]));
    assert forall|r: int| 0 <= r < n implies #[trigger] name_range_ok(cp, r) by {
        assert(CF::text_range_ok(o, y, r));
    }
}

/// The groups part of the part table (uniform groups of `bsize` rows).
pub open spec fn FC_groups(cp: Seq<PartView>, n: int) -> bool {
    CF::groups_part_ok(cp[22], n, bsize(cp))
}

/// The values of every row.
proof fn lemma_src_rows(cp: Seq<PartView>, crel: Seq<Row>, rel: Seq<Row>, t3: Seq<Row>)
    requires
        pa_conj(cp, crel),
        crel == crate::link::query::proj_all(t3, CD::stored_cols_t1()),
        rel == crate::link::query::proj_all(t3, D::stored_cols_t0()),
    ensures rows_ok(cp, rel),
{
    let tp = cp.subrange(C::PART_FIRST as int, (C::PART_FIRST + C::PA_PARTS) as int);
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
    assert(kb == cp[PA_PARTKEY_BASE as int] && kc == cp[PA_PARTKEY_CODES as int]);
    let (o, y) = (CF::u64s(tp[C::PA_NAME_OFFS as int]), CF::u8s(tp[C::PA_NAME_BYTES as int]));
    assert(o == name_offs(cp) && y == name_bytes(cp));
    assert(CF::int_col(crel, 0, gs, kb, kc));
    assert(CF::text_col(crel, 1, o, y));
    assert forall|r: int| 0 <= r < rel.len() implies #[trigger] rel[r] == pa_row(pkey_at(cp, r), name_at(cp, r)) by {
        CR::lemma_for_row(gp, n, bs, kb, kc, r);
        assert(crel[r][0] == Val::Int(CF::for_at(gs, kb, kc, r)));
        assert(crel[r][1] == Val::Text(CF::text_of(o, y, r)));
        assert(rel[r][0] == t3[r][0] && crel[r][0] == t3[r][0]);
        assert(rel[r][1] == t3[r][1] && crel[r][1] == t3[r][1]);
        assert(rel[r] =~= pa_row(pkey_at(cp, r), name_at(cp, r)));
    }
}

/// For a database bound to `custpart`, its parts and this storage's relation meet `src_ok`.
pub proof fn lemma_src(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures src_ok(sv.custpart, D::stored_relations(db)[0]),
{
    hide(pa_conj);
    let cp = sv.custpart;
    let crels = CD::stored_relations(db);
    assert(C::represents(cp, crels));
    lemma_pa_conj(cp, crels);
    let t3 = db.tables[3];
    let rel = D::stored_relations(db)[0];
    lemma_proj_all_index(t3, CD::stored_cols_t1());
    lemma_proj_all_index(t3, D::stored_cols_t0());
    assert(rel.len() == crels[1].len());
    lemma_src_shape(cp, crels[1]);
    lemma_src_rows(cp, crels[1], rel, t3);
}

} // verus!
