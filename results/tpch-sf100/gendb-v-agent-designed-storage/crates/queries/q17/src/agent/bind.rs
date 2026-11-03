//! The stored parts as value rows, for a database bound to them (`gendb_entry::bound_db`).
//!
//! - lineitem (storage `li_pkqty`): stored row `s` gives the value row `srow(lp, s)`; in stored order (`srows`)
//!   and in the order of the (l_partkey, l_quantity) index (`irows`, position `p` holds stored row `irow(p)`) they are
//!   permutations of the database's lineitem value rows (`lemma_li_link`);
//! - part (storage `custpart`, canonical order): stored row `j` gives `zrow(cp, j)` (p_partkey, and p_brand,
//!   p_container as dictionary entries); in order they are the database's part value rows (`lemma_pa_link`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::typing::db_wf;
use crate::link::query::{proj, proj_all};
use crate::link::expr::ival;
use crate::link::source::lemma_proj_all_index;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::part_len;
use crate::gendb_entry::stores::{StoresView, stored_ok};
use crate::stores::li_pkqty::interface as LI;
use crate::stores::li_pkqty::declaration as LD;
use crate::stores::custpart::interface as CPI;
use crate::stores::custpart::interface::common::colfmt as CF;
use crate::stores::custpart::interface::common::read as CR;
use crate::stores::custpart::declaration as CD;
use super::vals::*;
use super::typed::*;

verus! {

// ------------------------------------------------------------------------------------------------ lineitem

/// Number of stored lineitem rows.
pub open spec fn n_li(lp: Seq<PartView>) -> int {
    LI::n_rows(lp)
}

/// The value row of stored lineitem row `s`.
pub open spec fn srow(lp: Seq<PartView>, s: int) -> Row {
    yrow(LI::key_at(lp, s), LI::qty_at(lp, s), LI::price_at(lp, s))
}

/// The value rows in stored order.
pub open spec fn srows(lp: Seq<PartView>) -> Seq<Row> {
    Seq::new(n_li(lp) as nat, |s: int| srow(lp, s))
}

/// The value rows in the order of the l_partkey key index.
pub open spec fn irows(lp: Seq<PartView>) -> Seq<Row> {
    Seq::new(n_li(lp) as nat, |p: int| srow(lp, LI::irow(lp, p)))
}

/// What the scan relies on about the lineitem parts: the shapes, the directory, typed values.
pub open spec fn li_facts(lp: Seq<PartView>) -> bool {
    let n = n_li(lp);
    &&& 0 <= n <= u64::MAX
    &&& LI::li_shape(lp, n)
    &&& LI::idx_ok(lp, n)
    &&& forall|s: int| 0 <= s < n ==> y_ok(#[trigger] srow(lp, s))
}

/// The row map as a sequence.
pub open spec fn rmap(lp: Seq<PartView>) -> Seq<int> {
    Seq::new(n_li(lp) as nat, |s: int| LI::map_at(lp, s))
}

/// The key index as a sequence.
pub open spec fn imap(lp: Seq<PartView>) -> Seq<int> {
    Seq::new(n_li(lp) as nat, |p: int| LI::irow(lp, p))
}

/// The stored lineitem value rows are the relation's rows under the row map.
proof fn lemma_srows_map(lp: Seq<PartView>, rel: Seq<Row>)
    requires LI::represents(lp, seq![rel]),
    ensures
        CF::is_perm(rmap(lp), rel.len() as int),
        srows(lp) == CF::stored_rows(rel, rmap(lp)),
{
    let n = rel.len() as int;
    let rels = seq![rel];
    assert(rels[0] == rel);
    assert(LI::row_map_ok(lp, n));
    assert(LI::rows_ok(lp, rel));
    let m = rmap(lp);
    assert forall|i: int| 0 <= i < n implies #[trigger] CF::covered(m, i) by {
        assert(LI::mapped(lp, n, i));
        let s = choose|s: int| 0 <= s < n && #[trigger] LI::map_at(lp, s) == i;
        assert(m[s] == i);
    }
    assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b implies #[trigger] m[a] != #[trigger] m[b] by {
        assert(m[a] == LI::map_at(lp, a) && m[b] == LI::map_at(lp, b));
    }
    assert forall|s: int| 0 <= s < n implies 0 <= #[trigger] m[s] < n by {
        assert(m[s] == LI::map_at(lp, s));
    }
    assert forall|s: int| 0 <= s < n implies #[trigger] srows(lp)[s] == CF::stored_rows(rel, m)[s] by {
        assert(rel[LI::map_at(lp, s)] == LI::li_row(LI::key_at(lp, s), LI::qty_at(lp, s), LI::price_at(lp, s)));
    }
    assert(srows(lp) =~= CF::stored_rows(rel, m));
}

/// In index mode, the index-ordered value rows are the stored ones under the composite index.
proof fn lemma_irows_map(lp: Seq<PartView>, n: int)
    requires
        LI::idx_ok(lp, n),
        LI::has_idx(lp),
        n == n_li(lp),
        n >= 0,
    ensures
        CF::is_perm(imap(lp), n),
        irows(lp) == CF::stored_rows(srows(lp), imap(lp)),
{
    let m = imap(lp);
    assert forall|i: int| 0 <= i < n implies #[trigger] CF::covered(m, i) by {
        assert(LI::indexed(lp, n, i));
        let p = choose|p: int| 0 <= p < n && #[trigger] LI::irow(lp, p) == i;
        assert(m[p] == i);
    }
    assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b implies #[trigger] m[a] != #[trigger] m[b] by {
        assert(m[a] == LI::irow(lp, a) && m[b] == LI::irow(lp, b));
    }
    assert forall|p: int| 0 <= p < n implies 0 <= #[trigger] m[p] < n by {
        assert(m[p] == LI::irow(lp, p));
    }
    assert(irows(lp) =~= CF::stored_rows(srows(lp), m));
}

/// For a bound database: the lineitem facts, and both orders of the stored value rows are permutations of the
/// database's lineitem value rows.
pub proof fn lemma_li_link(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        li_facts(sv.li_pkqty),
        n_li(sv.li_pkqty) == db.tables[0].len(),
        srows(sv.li_pkqty).to_multiset() == ys_of(db).to_multiset(),
        LI::has_idx(sv.li_pkqty) ==> irows(sv.li_pkqty).to_multiset() == ys_of(db).to_multiset(),
        tables_ok(db),
{
    let lp = sv.li_pkqty;
    lemma_tables_ok(db);
    lemma_value_rows(db);
    assert(stored_ok(sv, db));
    let rels = LD::stored_relations(db);
    assert(LI::represents(lp, rels));
    assert(LD::stored_cols_t0() =~= lcols());
    let rel = rels[0];
    assert(rel == ys_of(db));
    assert(rels =~= seq![rel]);
    let n = rel.len() as int;
    assert(LI::li_shape(lp, n));
    assert(n_li(lp) == n);
    assert(n_li(lp) <= u64::MAX);
    lemma_srows_map(lp, rel);
    CF::lemma_stored_rows_multiset(rel, rmap(lp));
    assert forall|s: int| 0 <= s < n implies y_ok(#[trigger] srow(lp, s)) by {
        let m = rmap(lp);
        assert(srows(lp)[s] == rel[m[s]]);
        assert(0 <= m[s] < n);
        assert(y_ok(ys_of(db)[m[s]]));
    }
    if LI::has_idx(lp) {
        lemma_irows_map(lp, n);
        CF::lemma_stored_rows_multiset(srows(lp), imap(lp));
    }
}

// ------------------------------------------------------------------------------------------------ part

/// Index of part `k` of table part in the custpart parts.
pub open spec fn pp(k: usize) -> int {
    (CPI::PART_FIRST + k) as int
}

/// Number of stored part rows.
pub open spec fn n_pa(cp: Seq<PartView>) -> int {
    CF::u64s(cp[pp(CPI::PA_LAYOUT)])[0] as int
}

/// Rows per block of the part columns.
pub open spec fn pa_bs(cp: Seq<PartView>) -> int {
    CF::u64s(cp[pp(CPI::PA_LAYOUT)])[1] as int
}

/// p_partkey of stored part row `j`.
pub open spec fn pkey_at(cp: Seq<PartView>, j: int) -> int {
    CF::i64s(cp[pp(CPI::PA_PARTKEY_BASE)])[j / pa_bs(cp)] + CF::u32s(cp[pp(CPI::PA_PARTKEY_CODES)])[j]
}

/// Dictionary index of the p_brand of stored part row `j`.
pub open spec fn bidx_at(cp: Seq<PartView>, j: int) -> int {
    CF::u64s(cp[pp(CPI::PA_BRAND_BASE)])[j / pa_bs(cp)] + CF::u8s(cp[pp(CPI::PA_BRAND_CODES)])[j]
}

/// Dictionary index of the p_container of stored part row `j`.
pub open spec fn cidx_at(cp: Seq<PartView>, j: int) -> int {
    CF::u64s(cp[pp(CPI::PA_CONTAINER_BASE)])[j / pa_bs(cp)] + CF::u8s(cp[pp(CPI::PA_CONTAINER_CODES)])[j]
}

pub open spec fn bd_o(cp: Seq<PartView>) -> Seq<u64> {
    CF::u64s(cp[pp(CPI::PA_BRAND_DICT_OFFS)])
}

pub open spec fn bd_y(cp: Seq<PartView>) -> Seq<u8> {
    CF::u8s(cp[pp(CPI::PA_BRAND_DICT_BYTES)])
}

/// Number of p_brand dictionary entries.
pub open spec fn n_bd(cp: Seq<PartView>) -> int {
    bd_o(cp).len() - 1
}

pub open spec fn cd_o(cp: Seq<PartView>) -> Seq<u64> {
    CF::u64s(cp[pp(CPI::PA_CONTAINER_DICT_OFFS)])
}

pub open spec fn cd_y(cp: Seq<PartView>) -> Seq<u8> {
    CF::u8s(cp[pp(CPI::PA_CONTAINER_DICT_BYTES)])
}

/// Number of p_container dictionary entries.
pub open spec fn n_cd(cp: Seq<PartView>) -> int {
    cd_o(cp).len() - 1
}

/// The value row of stored part row `j`.
pub open spec fn zrow(cp: Seq<PartView>, j: int) -> Row {
    seq![
        Val::Int(pkey_at(cp, j)),
        Val::Text(CF::text_of(bd_o(cp), bd_y(cp), bidx_at(cp, j))),
        Val::Text(CF::text_of(cd_o(cp), cd_y(cp), cidx_at(cp, j))),
    ]
}

/// The part value rows in stored (canonical) order.
pub open spec fn zrows(cp: Seq<PartView>) -> Seq<Row> {
    Seq::new(n_pa(cp) as nat, |j: int| zrow(cp, j))
}

/// What the scan relies on about the part parts.
pub open spec fn pa_facts(cp: Seq<PartView>) -> bool {
    let n = n_pa(cp);
    let bs = pa_bs(cp);
    &&& cp.len() == CPI::CUSTPART_PARTS
    &&& cp[pp(CPI::PA_LAYOUT)] is U64 && CF::u64s(cp[pp(CPI::PA_LAYOUT)]).len() == 2
    &&& 0 <= n
    &&& bs >= 1
    &&& n + bs <= u64::MAX
    &&& cp[pp(CPI::PA_PARTKEY_CODES)] is U32 && cp[pp(CPI::PA_PARTKEY_BASE)] is I64
    &&& LI::for_len_ok(CF::u32s(cp[pp(CPI::PA_PARTKEY_CODES)]).len() as int, CF::i64s(cp[pp(CPI::PA_PARTKEY_BASE)]).len() as int, n, bs)
    &&& cp[pp(CPI::PA_BRAND_CODES)] is U8 && cp[pp(CPI::PA_BRAND_BASE)] is U64
    &&& LI::for_len_ok(CF::u8s(cp[pp(CPI::PA_BRAND_CODES)]).len() as int, CF::u64s(cp[pp(CPI::PA_BRAND_BASE)]).len() as int, n, bs)
    &&& cp[pp(CPI::PA_CONTAINER_CODES)] is U8 && cp[pp(CPI::PA_CONTAINER_BASE)] is U64
    &&& LI::for_len_ok(CF::u8s(cp[pp(CPI::PA_CONTAINER_CODES)]).len() as int, CF::u64s(cp[pp(CPI::PA_CONTAINER_BASE)]).len() as int, n, bs)
    &&& cp[pp(CPI::PA_BRAND_DICT_OFFS)] is U64 && cp[pp(CPI::PA_BRAND_DICT_BYTES)] is U8
    &&& bd_o(cp).len() >= 1
    &&& CF::text_parts_wf(bd_o(cp), bd_y(cp), n_bd(cp))
    &&& CF::dict_sorted(bd_o(cp), bd_y(cp), n_bd(cp))
    &&& cp[pp(CPI::PA_CONTAINER_DICT_OFFS)] is U64 && cp[pp(CPI::PA_CONTAINER_DICT_BYTES)] is U8
    &&& cd_o(cp).len() >= 1
    &&& CF::text_parts_wf(cd_o(cp), cd_y(cp), n_cd(cp))
    &&& CF::dict_sorted(cd_o(cp), cd_y(cp), n_cd(cp))
    &&& forall|j: int| 0 <= j < n ==> {
        &&& 0 <= #[trigger] bidx_at(cp, j) < n_bd(cp)
        &&& 0 <= cidx_at(cp, j) < n_cd(cp)
        &&& i64::MIN <= pkey_at(cp, j) <= i64::MAX
    }
}

/// The parts of table part in storage custpart.
pub open spec fn pa_tp(cp: Seq<PartView>) -> Seq<PartView> {
    cp.subrange(CPI::PART_FIRST as int, (CPI::PART_FIRST + CPI::PA_PARTS) as int)
}

/// The conjuncts of `part_ok` the scan reads.
proof fn lemma_part_conj(cp: Seq<PartView>, rel: Seq<Row>)
    requires
        cp.len() == CPI::CUSTPART_PARTS,
        CPI::part_ok(pa_tp(cp), rel),
    ensures ({
        let tp = pa_tp(cp);
        &&& CPI::table_layout_ok(tp, rel.len() as int)
        &&& tp[CPI::PA_PARTKEY_CODES as int] is U32
        &&& CF::int_col_at(tp, CPI::PA_GROUPS as int, CPI::PA_PARTKEY_CODES as int, CPI::PA_PARTKEY_BASE as int, rel, 0)
        &&& tp[CPI::PA_BRAND_CODES as int] is U8
        &&& CF::dict_col_at(tp, CPI::PA_GROUPS as int, CPI::PA_BRAND_CODES as int, CPI::PA_BRAND_BASE as int,
                CPI::PA_BRAND_DICT_OFFS as int, CPI::PA_BRAND_DICT_BYTES as int, rel, 3)
        &&& tp[CPI::PA_CONTAINER_CODES as int] is U8
        &&& CF::dict_col_at(tp, CPI::PA_GROUPS as int, CPI::PA_CONTAINER_CODES as int, CPI::PA_CONTAINER_BASE as int,
                CPI::PA_CONTAINER_DICT_OFFS as int, CPI::PA_CONTAINER_DICT_BYTES as int, rel, 6)
    }),
{
}

/// The part parts in the custpart parts.
proof fn lemma_pa_tp(cp: Seq<PartView>)
    requires cp.len() == CPI::CUSTPART_PARTS,
    ensures forall|k: int| 0 <= k < CPI::PA_PARTS ==> #[trigger] pa_tp(cp)[k] == cp[pp(k as usize)],
{
}

/// The shapes of the part columns the scan reads.
proof fn lemma_part_shapes(cp: Seq<PartView>, rel: Seq<Row>)
    requires
        cp.len() == CPI::CUSTPART_PARTS,
        CPI::part_ok(pa_tp(cp), rel),
    ensures
        n_pa(cp) == rel.len(),
        cp[pp(CPI::PA_LAYOUT)] is U64 && CF::u64s(cp[pp(CPI::PA_LAYOUT)]).len() == 2,
        pa_bs(cp) >= 1,
        n_pa(cp) + pa_bs(cp) <= u64::MAX,
        CF::groups_part_ok(cp[pp(CPI::PA_GROUPS)], n_pa(cp), pa_bs(cp)),
        cp[pp(CPI::PA_PARTKEY_CODES)] is U32 && cp[pp(CPI::PA_PARTKEY_BASE)] is I64,
        LI::for_len_ok(CF::u32s(cp[pp(CPI::PA_PARTKEY_CODES)]).len() as int, CF::i64s(cp[pp(CPI::PA_PARTKEY_BASE)]).len() as int, n_pa(cp), pa_bs(cp)),
        cp[pp(CPI::PA_BRAND_CODES)] is U8 && cp[pp(CPI::PA_BRAND_BASE)] is U64,
        LI::for_len_ok(CF::u8s(cp[pp(CPI::PA_BRAND_CODES)]).len() as int, CF::u64s(cp[pp(CPI::PA_BRAND_BASE)]).len() as int, n_pa(cp), pa_bs(cp)),
        cp[pp(CPI::PA_CONTAINER_CODES)] is U8 && cp[pp(CPI::PA_CONTAINER_BASE)] is U64,
        LI::for_len_ok(CF::u8s(cp[pp(CPI::PA_CONTAINER_CODES)]).len() as int, CF::u64s(cp[pp(CPI::PA_CONTAINER_BASE)]).len() as int, n_pa(cp), pa_bs(cp)),
        cp[pp(CPI::PA_BRAND_DICT_OFFS)] is U64 && cp[pp(CPI::PA_BRAND_DICT_BYTES)] is U8,
        bd_o(cp).len() >= 1,
        CF::text_parts_wf(bd_o(cp), bd_y(cp), n_bd(cp)),
        CF::dict_sorted(bd_o(cp), bd_y(cp), n_bd(cp)),
        cp[pp(CPI::PA_CONTAINER_DICT_OFFS)] is U64 && cp[pp(CPI::PA_CONTAINER_DICT_BYTES)] is U8,
        cd_o(cp).len() >= 1,
        CF::text_parts_wf(cd_o(cp), cd_y(cp), n_cd(cp)),
        CF::dict_sorted(cd_o(cp), cd_y(cp), n_cd(cp)),
{
    hide(CF::int_col);
    hide(CF::dict_col);
    lemma_part_conj(cp, rel);
    let tp = pa_tp(cp);
    lemma_pa_tp(cp);
    let n = rel.len() as int;
    let gp = tp[CPI::PA_GROUPS as int];
    let bs = CF::u64s(tp[CPI::PA_LAYOUT as int])[1] as int;
    assert(tp[CPI::PA_LAYOUT as int] == cp[pp(CPI::PA_LAYOUT)]);
    assert(tp[CPI::PA_GROUPS as int] == cp[pp(CPI::PA_GROUPS)]);
    assert(bs == pa_bs(cp));
    assert(CF::groups_part_ok(gp, n, bs));
    CF::lemma_uniform_groups(gp, n, bs);
    CF::lemma_nblocks(n, bs);
    assert(tp[CPI::PA_PARTKEY_CODES as int] == cp[pp(CPI::PA_PARTKEY_CODES)]);
    assert(tp[CPI::PA_PARTKEY_BASE as int] == cp[pp(CPI::PA_PARTKEY_BASE)]);
    assert(tp[CPI::PA_BRAND_CODES as int] == cp[pp(CPI::PA_BRAND_CODES)]);
    assert(tp[CPI::PA_BRAND_BASE as int] == cp[pp(CPI::PA_BRAND_BASE)]);
    assert(tp[CPI::PA_CONTAINER_CODES as int] == cp[pp(CPI::PA_CONTAINER_CODES)]);
    assert(tp[CPI::PA_CONTAINER_BASE as int] == cp[pp(CPI::PA_CONTAINER_BASE)]);
    assert(tp[CPI::PA_BRAND_DICT_OFFS as int] == cp[pp(CPI::PA_BRAND_DICT_OFFS)]);
    assert(tp[CPI::PA_BRAND_DICT_BYTES as int] == cp[pp(CPI::PA_BRAND_DICT_BYTES)]);
    assert(tp[CPI::PA_CONTAINER_DICT_OFFS as int] == cp[pp(CPI::PA_CONTAINER_DICT_OFFS)]);
    assert(tp[CPI::PA_CONTAINER_DICT_BYTES as int] == cp[pp(CPI::PA_CONTAINER_DICT_BYTES)]);
}

/// The part values of stored row `j`.
proof fn lemma_part_row(cp: Seq<PartView>, rel: Seq<Row>, j: int)
    requires
        cp.len() == CPI::CUSTPART_PARTS,
        CPI::part_ok(pa_tp(cp), rel),
        0 <= j < rel.len(),
    ensures
        0 <= bidx_at(cp, j) < n_bd(cp),
        0 <= cidx_at(cp, j) < n_cd(cp),
        rel[j][0] == Val::Int(pkey_at(cp, j)),
        rel[j][3] == Val::Text(CF::text_of(bd_o(cp), bd_y(cp), bidx_at(cp, j))),
        rel[j][6] == Val::Text(CF::text_of(cd_o(cp), cd_y(cp), cidx_at(cp, j))),
{
    lemma_part_conj(cp, rel);
    lemma_part_shapes(cp, rel);
    let tp = pa_tp(cp);
    lemma_pa_tp(cp);
    let n = rel.len() as int;
    let gp = cp[pp(CPI::PA_GROUPS)];
    let bs = pa_bs(cp);
    let gs = CF::u64s(gp);
    let (kc, kb) = (cp[pp(CPI::PA_PARTKEY_CODES)], cp[pp(CPI::PA_PARTKEY_BASE)]);
    let (bc, bb) = (cp[pp(CPI::PA_BRAND_CODES)], cp[pp(CPI::PA_BRAND_BASE)]);
    let (cc, cb) = (cp[pp(CPI::PA_CONTAINER_CODES)], cp[pp(CPI::PA_CONTAINER_BASE)]);
    assert(tp[CPI::PA_GROUPS as int] == gp);
    assert(tp[CPI::PA_PARTKEY_CODES as int] == kc && tp[CPI::PA_PARTKEY_BASE as int] == kb);
    assert(tp[CPI::PA_BRAND_CODES as int] == bc && tp[CPI::PA_BRAND_BASE as int] == bb);
    assert(tp[CPI::PA_CONTAINER_CODES as int] == cc && tp[CPI::PA_CONTAINER_BASE as int] == cb);
    assert(tp[CPI::PA_BRAND_DICT_OFFS as int] == cp[pp(CPI::PA_BRAND_DICT_OFFS)]);
    assert(tp[CPI::PA_BRAND_DICT_BYTES as int] == cp[pp(CPI::PA_BRAND_DICT_BYTES)]);
    assert(tp[CPI::PA_CONTAINER_DICT_OFFS as int] == cp[pp(CPI::PA_CONTAINER_DICT_OFFS)]);
    assert(tp[CPI::PA_CONTAINER_DICT_BYTES as int] == cp[pp(CPI::PA_CONTAINER_DICT_BYTES)]);
    CR::lemma_for_row(gp, n, bs, kb, kc, j);
    CR::lemma_for_row(gp, n, bs, bb, bc, j);
    CR::lemma_for_row(gp, n, bs, cb, cc, j);
    assert(CF::for_at(gs, kb, kc, j) == pkey_at(cp, j));
    assert(CF::for_at(gs, bb, bc, j) == bidx_at(cp, j));
    assert(CF::for_at(gs, cb, cc, j) == cidx_at(cp, j));
    assert(CF::int_col(rel, 0, gs, kb, kc));
    assert(CF::dict_col(rel, 3, gs, bb, bc, bd_o(cp), bd_y(cp)));
    assert(CF::dict_col(rel, 6, gs, cb, cc, cd_o(cp), cd_y(cp)));
}

/// For a bound database: the part facts, and the stored part value rows are the database's part value rows.
pub proof fn lemma_pa_link(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        pa_facts(sv.custpart),
        n_pa(sv.custpart) == db.tables[3].len(),
        zrows(sv.custpart) == zs_of(db),
{
    hide(CPI::customer_ok);
    hide(CPI::part_ok);
    let cp = sv.custpart;
    lemma_tables_ok(db);
    lemma_value_rows(db);
    let p = db.tables[3];
    let rels = CD::stored_relations(db);
    CD::lemma_declared_schema();
    assert(stored_ok(sv, db));
    assert(CPI::represents(cp, rels));
    lemma_proj_all_index(p, CD::stored_cols_t1());
    assert forall|j: int| 0 <= j < p.len() implies #[trigger] rels[1][j] == p[j] by {
        assert(prow_ok(p[j]));
        assert(proj(p[j], CD::stored_cols_t1()) =~= p[j]);
    }
    assert(rels[1] =~= p);
    assert(CPI::part_ok(pa_tp(cp), p));
    lemma_part_shapes(cp, p);
    let n = p.len() as int;
    assert forall|j: int| 0 <= j < n implies #[trigger] zrows(cp)[j] == zs_of(db)[j]
        && 0 <= bidx_at(cp, j) < n_bd(cp) && 0 <= cidx_at(cp, j) < n_cd(cp)
        && i64::MIN <= pkey_at(cp, j) <= i64::MAX by {
        lemma_part_row(cp, p, j);
        assert(prow_ok(p[j]));
        assert(zs_of(db)[j] == proj(p[j], pcols()));
        assert(proj(p[j], pcols()) =~= zrow(cp, j));
    }
    assert(zrows(cp) =~= zs_of(db));
    assert forall|j: int| 0 <= j < n implies {
        &&& 0 <= #[trigger] bidx_at(cp, j) < n_bd(cp)
        &&& 0 <= cidx_at(cp, j) < n_cd(cp)
        &&& i64::MIN <= pkey_at(cp, j) <= i64::MAX
    } by {
        assert(zrows(cp)[j] == zs_of(db)[j]);
    }
}

} // verus!
