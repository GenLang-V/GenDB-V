//! The stored columns the query reads and what every database bound to the parts gives about them.
//!
//! `Li` holds the lineitem columns of storage `lisupp` as whole-part slices: frame-of-reference codes per stored
//! row with one base per block of `bs` rows (so row `j`'s value is `base[j / bs] + code[j]`), the l_shipdate zone
//! maxima per block, and the l_suppkey key index (`ic`/`ib`/`kind`, `keyidx`). `xs_of(c)` are the stored rows
//! decoded to `[l_suppkey, l_extendedprice, l_discount, l_shipdate]` (`group::li_row`), in stored order; for every
//! bound database they are a permutation of the lineitem rows projected on those columns (`lemma_li_db`).
//!
//! `Su` holds the supplier columns of storage `suppliers` (canonical row order): the key (FOR codes) and the name,
//! address and phone texts; stored row `j` is supplier row `j` of every bound database (`lemma_su_db`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::typing::db_wf;
use crate::schema::schema_spec;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::{StoredParts, part_len};
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::link::query::{proj, proj_all};
use crate::link::expr::ival;
use crate::link::source::lemma_proj_all_index;
use crate::stores::lisupp::interface as li;
use crate::stores::lisupp::interface::common::colfmt as lc;
use crate::stores::lisupp::interface::common::keyidx as lk;
use crate::stores::suppliers::interface as si;
use crate::stores::suppliers::interface::common::colfmt as sc;
use super::group::*;

verus! {

// ------------------------------------------------------------------------------------------------ lineitem

/// The lineitem columns of `lisupp` as whole-part slices, with their lengths.
#[derive(Clone, Copy)]
pub struct Li {
    pub ship: &'static [u16],
    pub ship_base: &'static [i64],
    pub ship_zmax: &'static [i64],
    pub supp: &'static [u32],
    pub supp_base: &'static [i64],
    pub price: &'static [u32],
    pub price_base: &'static [i64],
    pub disc: &'static [u8],
    pub disc_base: &'static [i64],
    pub ic: &'static [u32],
    pub ib: &'static [u64],
    pub kind: u64,
    /// Stored rows.
    pub n: usize,
    /// Rows per block.
    pub bs: u64,
    /// Blocks (one base per block).
    pub nb: usize,
}

pub open spec fn supp_v(c: Li, j: int) -> int { c.supp_base@[j / c.bs as int] + c.supp@[j] }
pub open spec fn price_v(c: Li, j: int) -> int { c.price_base@[j / c.bs as int] + c.price@[j] }
pub open spec fn disc_v(c: Li, j: int) -> int { c.disc_base@[j / c.bs as int] + c.disc@[j] }
pub open spec fn ship_v(c: Li, j: int) -> int { c.ship_base@[j / c.bs as int] + c.ship@[j] }

/// The stored lineitem rows, decoded.
pub open spec fn xs_of(c: Li) -> Seq<Row> {
    Seq::new(c.n as nat, |j: int| li_row(supp_v(c, j), price_v(c, j), disc_v(c, j), ship_v(c, j)))
}

/// The shape of the slices: `n` codes each, one base (and zone maximum) per block of `bs` rows.
pub open spec fn li_shape(c: Li) -> bool {
    &&& c.bs >= 1
    &&& c.nb as int == lc::nblocks_of(c.n as int, c.bs as int)
    &&& c.nb * c.bs >= c.n
    &&& c.nb == 0 || (c.nb - 1) * c.bs < c.n
    &&& c.n + c.bs <= u64::MAX
    &&& c.ship@.len() == c.n && c.supp@.len() == c.n && c.price@.len() == c.n && c.disc@.len() == c.n
    &&& c.ship_base@.len() == c.nb && c.ship_zmax@.len() == c.nb && c.supp_base@.len() == c.nb
    &&& c.price_base@.len() == c.nb && c.disc_base@.len() == c.nb
}

/// The slices are the parts of `lisupp`.
pub open spec fn li_link(c: Li, parts: Seq<PartView>) -> bool {
    &&& parts.len() == li::LISUPP_PARTS
    &&& parts[li::LI_LAYOUT as int] is U64
    &&& lc::u64s(parts[li::LI_LAYOUT as int]).len() == 2
    &&& c.n as int == lc::u64s(parts[li::LI_LAYOUT as int])[0]
    &&& c.bs as int == lc::u64s(parts[li::LI_LAYOUT as int])[1]
    &&& c.nb as int == part_len(parts[li::LI_SHIPDATE_BASE as int])
    &&& parts[li::LI_SHIPDATE_CODES as int] == PartView::U16(c.ship@)
    &&& parts[li::LI_SHIPDATE_BASE as int] == PartView::I64(c.ship_base@)
    &&& parts[li::LI_SHIPDATE_ZMAX as int] == PartView::I64(c.ship_zmax@)
    &&& parts[li::LI_SUPPKEY_CODES as int] == PartView::U32(c.supp@)
    &&& parts[li::LI_SUPPKEY_BASE as int] == PartView::I64(c.supp_base@)
    &&& parts[li::LI_EXTENDEDPRICE_CODES as int] == PartView::U32(c.price@)
    &&& parts[li::LI_EXTENDEDPRICE_BASE as int] == PartView::I64(c.price_base@)
    &&& parts[li::LI_DISCOUNT_CODES as int] == PartView::U8(c.disc@)
    &&& parts[li::LI_DISCOUNT_BASE as int] == PartView::I64(c.disc_base@)
    &&& parts[li::SX_CODES as int] == PartView::U32(c.ic@)
    &&& parts[li::SX_BASES as int] == PartView::U64(c.ib@)
    &&& parts[li::SX_KIND as int] is U64
    &&& lc::u64s(parts[li::SX_KIND as int]).len() == 1
    &&& c.kind == lc::u64s(parts[li::SX_KIND as int])[0]
}

/// What `represents` states of the inherited lineitem parts.
pub proof fn lemma_li_ok(parts: Seq<PartView>, rels: Seq<Seq<Row>>)
    requires li::represents(parts, rels),
    ensures
        li::li_ok(parts.subrange(0, li::LI_PARTS as int), rels[0]),
        li::index_ok(parts, rels[0].len() as int),
        parts.len() == li::LISUPP_PARTS,
{
}

/// The part kinds and lengths the loader needs, from `represents`.
pub proof fn lemma_li_parts(parts: Seq<PartView>, rels: Seq<Seq<Row>>)
    requires li::represents(parts, rels),
    ensures ({
        let n = rels[0].len() as int;
        let bs = lc::u64s(parts[0])[1] as int;
        let nb = lc::nblocks_of(n, bs);
        &&& parts.len() == li::LISUPP_PARTS
        &&& parts[li::LI_LAYOUT as int] is U64 && lc::u64s(parts[li::LI_LAYOUT as int]).len() == 2
        &&& lc::u64s(parts[li::LI_LAYOUT as int])[0] == n
        &&& bs >= 1 && n + bs <= u64::MAX
        &&& nb * bs >= n && (nb == 0 || (nb - 1) * bs < n) && nb >= 0
        &&& parts[li::LI_SHIPDATE_CODES as int] is U16 && part_len(parts[li::LI_SHIPDATE_CODES as int]) == n
        &&& parts[li::LI_SUPPKEY_CODES as int] is U32 && part_len(parts[li::LI_SUPPKEY_CODES as int]) == n
        &&& parts[li::LI_EXTENDEDPRICE_CODES as int] is U32 && part_len(parts[li::LI_EXTENDEDPRICE_CODES as int]) == n
        &&& parts[li::LI_DISCOUNT_CODES as int] is U8 && part_len(parts[li::LI_DISCOUNT_CODES as int]) == n
        &&& parts[li::LI_SHIPDATE_BASE as int] is I64 && part_len(parts[li::LI_SHIPDATE_BASE as int]) == nb
        &&& parts[li::LI_SHIPDATE_ZMAX as int] is I64 && part_len(parts[li::LI_SHIPDATE_ZMAX as int]) == nb
        &&& parts[li::LI_SUPPKEY_BASE as int] is I64 && part_len(parts[li::LI_SUPPKEY_BASE as int]) == nb
        &&& parts[li::LI_EXTENDEDPRICE_BASE as int] is I64 && part_len(parts[li::LI_EXTENDEDPRICE_BASE as int]) == nb
        &&& parts[li::LI_DISCOUNT_BASE as int] is I64 && part_len(parts[li::LI_DISCOUNT_BASE as int]) == nb
        &&& parts[li::SX_CODES as int] is U32 && parts[li::SX_BASES as int] is U64
        &&& parts[li::SX_KIND as int] is U64 && lc::u64s(parts[li::SX_KIND as int]).len() == 1
    }),
{
    lemma_li_ok(parts, rels);
    let tp = parts.subrange(0, li::LI_PARTS as int);
    let n = rels[0].len() as int;
    let bs = lc::u64s(parts[0])[1] as int;
    assert forall|k: int| 0 <= k < li::LI_PARTS implies #[trigger] tp[k] == parts[k] by {}
    let srows = li::li_rows(tp, rels[0]);
    assert(srows.len() == n);
    lc::lemma_uniform_groups(tp[1], n, bs);
    lc::lemma_nblocks(n, bs);
}

/// The shape of the slices, from `represents`.
pub proof fn lemma_li_shape(c: Li, parts: Seq<PartView>, rels: Seq<Seq<Row>>)
    requires
        li::represents(parts, rels),
        li_link(c, parts),
    ensures
        li_shape(c),
        c.n == rels[0].len(),
        lk::keyidx_ok(c.supp@, c.supp_base@, c.ic@, c.ib@, c.bs as int, c.kind, c.n as int),
{
    lemma_li_parts(parts, rels);
    lemma_li_ok(parts, rels);
    assert(li::index_ok(parts, rels[0].len() as int));
}

/// Row `j`'s decoded values are its stored row's columns, and its shipdate lies under its block's zone maximum.
pub proof fn lemma_li_row(c: Li, parts: Seq<PartView>, rels: Seq<Seq<Row>>, j: int)
    requires
        li::represents(parts, rels),
        li_link(c, parts),
        0 <= j < c.n,
    ensures ({
        let tp = parts.subrange(0, li::LI_PARTS as int);
        let srows = li::li_rows(tp, rels[0]);
        &&& srows.len() == c.n
        &&& xs_of(c)[j] =~= srows[j]
        &&& 0 <= j / (c.bs as int) < c.nb
        &&& ship_v(c, j) <= c.ship_zmax@[j / c.bs as int]
    }),
{
    hide(li::represents);
    lemma_li_shape(c, parts, rels);
    reveal(li::represents);
    lemma_li_ok(parts, rels);
    let tp = parts.subrange(0, li::LI_PARTS as int);
    let n = c.n as int;
    let bs = c.bs as int;
    let srows = li::li_rows(tp, rels[0]);
    assert forall|k: int| 0 <= k < li::LI_PARTS implies #[trigger] tp[k] == parts[k] by {}
    let gp = tp[1];
    let gs = lc::u64s(gp);
    assert(srows.len() == n);
    crate::stores::lisupp::interface::common::read::lemma_div_lt(j, bs, c.nb as int);
    crate::stores::lisupp::interface::common::read::lemma_for_row(gp, n, bs, tp[9], tp[8], j);
    crate::stores::lisupp::interface::common::read::lemma_for_row(gp, n, bs, tp[15], tp[14], j);
    crate::stores::lisupp::interface::common::read::lemma_for_row(gp, n, bs, tp[17], tp[16], j);
    crate::stores::lisupp::interface::common::read::lemma_for_row(gp, n, bs, tp[29], tp[28], j);
    assert(li::li_cols_ok(tp, srows));
    assert(srows[j][0] == Val::Int(lc::for_at(gs, tp[9], tp[8], j)));
    assert(srows[j][1] == (Val::Num { coeff: lc::for_at(gs, tp[15], tp[14], j), scale: 2 }));
    assert(srows[j][2] == (Val::Num { coeff: lc::for_at(gs, tp[17], tp[16], j), scale: 2 }));
    assert(srows[j][3] == Val::Date(lc::for_at(gs, tp[29], tp[28], j)));
    let m = li::li_map(tp, n);
    assert(lc::is_perm(m, n));
    assert(0 <= m[j] < n);
    assert(srows[j] == rels[0][m[j]]);
    assert(srows[j].len() == 4);
    assert(lc::in_group(gs, j / bs, j));
}

/// Every stored row's decoded values are its stored row's columns, and the shipdate lies under its block's zone
/// maximum.
pub proof fn lemma_li_rows(c: Li, parts: Seq<PartView>, rels: Seq<Seq<Row>>)
    requires
        li::represents(parts, rels),
        li_link(c, parts),
    ensures ({
        let tp = parts.subrange(0, li::LI_PARTS as int);
        let srows = li::li_rows(tp, rels[0]);
        &&& li_shape(c)
        &&& c.n == rels[0].len()
        &&& srows.len() == c.n
        &&& forall|j: int| 0 <= j < c.n ==> #[trigger] xs_of(c)[j] =~= srows[j]
        &&& forall|j: int| 0 <= j < c.n ==> #[trigger] ship_v(c, j) <= c.ship_zmax@[j / c.bs as int]
        &&& lk::keyidx_ok(c.supp@, c.supp_base@, c.ic@, c.ib@, c.bs as int, c.kind, c.n as int)
    }),
{
    hide(li::represents);
    hide(li::li_rows);
    hide(xs_of);
    lemma_li_shape(c, parts, rels);
    lemma_srows_len(parts, rels);
    let tp = parts.subrange(0, li::LI_PARTS as int);
    let srows = li::li_rows(tp, rels[0]);
    assert forall|j: int| 0 <= j < c.n implies #[trigger] xs_of(c)[j] =~= srows[j] by {
        lemma_li_row(c, parts, rels, j);
    }
    assert forall|j: int| 0 <= j < c.n implies #[trigger] ship_v(c, j) <= c.ship_zmax@[j / c.bs as int] by {
        lemma_li_row(c, parts, rels, j);
    }
    lemma_srows_len(parts, rels);
}

/// The stored rows are as many as the relation's rows.
proof fn lemma_srows_len(parts: Seq<PartView>, rels: Seq<Seq<Row>>)
    requires li::represents(parts, rels),
    ensures
        rels.len() == 1,
        li::li_rows(parts.subrange(0, li::LI_PARTS as int), rels[0]).len() == rels[0].len(),
{
}

/// For every bound database: the stored rows are a permutation of its lineitem rows projected on the four columns,
/// with numeric(15, 2) price and discount.
pub proof fn lemma_li_db(c: Li, sv: StoresView, db: Database)
    requires
        bound_db(sv, db),
        li_link(c, sv.lisupp),
    ensures
        li_shape(c),
        c.n == db.tables[0].len(),
        xs_of(c).to_multiset() == xd(db).to_multiset(),
        xs_of(c).len() == xd(db).len(),
        forall|j: int| 0 <= j < c.n ==> #[trigger] ship_v(c, j) <= c.ship_zmax@[j / c.bs as int],
        forall|j: int| 0 <= j < c.n ==> -p15() < #[trigger] price_v(c, j) < p15() && -p15() < disc_v(c, j) < p15(),
        lk::keyidx_ok(c.supp@, c.supp_base@, c.ic@, c.ib@, c.bs as int, c.kind, c.n as int),
{
    let parts = sv.lisupp;
    let rels = crate::stores::lisupp::declaration::stored_relations(db);
    assert(li::represents(parts, rels));
    lemma_li_rows(c, parts, rels);
    lemma_li_ok(parts, rels);
    let tp = parts.subrange(0, li::LI_PARTS as int);
    let srows = li::li_rows(tp, rels[0]);
    let n = c.n as int;
    let m = li::li_map(tp, n);
    let xdb = xd(db);
    assert(rels[0] == xdb);
    lemma_proj_all_len(db.tables[0]);
    assert(lc::is_perm(m, n));
    assert(srows == lc::stored_rows(xdb, m));
    let xs = xs_of(c);
    assert(xs =~= srows);
    lc::lemma_stored_rows_multiset(xdb, m);
    lemma_rows_typed(db);
    assert forall|j: int| 0 <= j < n implies -p15() < #[trigger] price_v(c, j) < p15() && -p15() < disc_v(c, j) < p15() by {
        let i = m[j];
        assert(0 <= i < n);
        assert(srows[j] == xdb[i]);
        assert(xdb[i] == proj(db.tables[0][i], cols4()));
        assert(row_typed(db.tables[0][i]));
        lemma_proj4(db.tables[0][i]);
        assert(xs[j] == srows[j]);
        assert(xs[j][1] == (Val::Num { coeff: price_v(c, j), scale: 2 }));
        assert(xs[j][2] == (Val::Num { coeff: disc_v(c, j), scale: 2 }));
    }
}

/// Reads the lineitem columns of `lisupp` (whole parts).
pub fn load_li(st: &mut StoredParts, Ghost(rels): Ghost<Seq<Seq<Row>>>) -> (c: Li)
    requires li::represents(old(st)@, rels),
    ensures
        final(st)@ == old(st)@,
        li_link(c, old(st)@),
{
    let ghost parts = st@;
    proof {
        lemma_li_parts(parts, rels);
    }
    let lay = st.extent_u64(li::LI_LAYOUT, 0, 2);
    let n = st.part_len(li::LI_SHIPDATE_CODES);
    let nb = st.part_len(li::LI_SHIPDATE_BASE);
    let bs64 = lay[1];
    proof {
        assert(lay@ =~= lc::u64s(parts[li::LI_LAYOUT as int]));
        assert(bs64 as int + n as int <= u64::MAX);
    }
    let bs: u64 = bs64;
    let ship = st.extent_u16(li::LI_SHIPDATE_CODES, 0, n);
    let ship_base = st.extent_i64(li::LI_SHIPDATE_BASE, 0, nb);
    let ship_zmax = st.extent_i64(li::LI_SHIPDATE_ZMAX, 0, nb);
    let supp = st.extent_u32(li::LI_SUPPKEY_CODES, 0, n);
    let supp_base = st.extent_i64(li::LI_SUPPKEY_BASE, 0, nb);
    let price = st.extent_u32(li::LI_EXTENDEDPRICE_CODES, 0, n);
    let price_base = st.extent_i64(li::LI_EXTENDEDPRICE_BASE, 0, nb);
    let disc = st.extent_u8(li::LI_DISCOUNT_CODES, 0, n);
    let disc_base = st.extent_i64(li::LI_DISCOUNT_BASE, 0, nb);
    let nic = st.part_len(li::SX_CODES);
    let nib = st.part_len(li::SX_BASES);
    let ic = st.extent_u32(li::SX_CODES, 0, nic);
    let ib = st.extent_u64(li::SX_BASES, 0, nib);
    let kv = st.extent_u64(li::SX_KIND, 0, 1);
    let kind = kv[0];
    let c = Li { ship, ship_base, ship_zmax, supp, supp_base, price, price_base, disc, disc_base, ic, ib, kind, n, bs, nb };
    proof {
        assert(bs as int == bs64 as int);
        assert(ship@ =~= parts[li::LI_SHIPDATE_CODES as int]->U16_0);
        assert(ship_base@ =~= lc::i64s(parts[li::LI_SHIPDATE_BASE as int]));
        assert(ship_zmax@ =~= lc::i64s(parts[li::LI_SHIPDATE_ZMAX as int]));
        assert(supp@ =~= lc::u32s(parts[li::LI_SUPPKEY_CODES as int]));
        assert(supp_base@ =~= lc::i64s(parts[li::LI_SUPPKEY_BASE as int]));
        assert(price@ =~= lc::u32s(parts[li::LI_EXTENDEDPRICE_CODES as int]));
        assert(price_base@ =~= lc::i64s(parts[li::LI_EXTENDEDPRICE_BASE as int]));
        assert(disc@ =~= lc::u8s(parts[li::LI_DISCOUNT_CODES as int]));
        assert(disc_base@ =~= lc::i64s(parts[li::LI_DISCOUNT_BASE as int]));
        assert(ic@ =~= lc::u32s(parts[li::SX_CODES as int]));
        assert(ib@ =~= lc::u64s(parts[li::SX_BASES as int]));
        assert(kv@ =~= lc::u64s(parts[li::SX_KIND as int]));
    }
    c
}

// ------------------------------------------------------------------------------------------------ supplier

/// The supplier columns of `suppliers` as whole-part slices.
#[derive(Clone, Copy)]
pub struct Su {
    pub key: &'static [u32],
    pub key_base: &'static [i64],
    pub name_o: &'static [u64],
    pub name_y: &'static [u8],
    pub addr_o: &'static [u64],
    pub addr_y: &'static [u8],
    pub phone_o: &'static [u64],
    pub phone_y: &'static [u8],
    /// Supplier rows.
    pub ns: usize,
    /// Rows per block.
    pub bs: u64,
    /// Key index kind of s_suppkey (1: the rows are sorted by key).
    pub kind: u64,
}

pub open spec fn skey_v(s: Su, j: int) -> int { s.key_base@[j / s.bs as int] + s.key@[j] }

/// The slices are the supplier parts of `suppliers`.
pub open spec fn su_link(s: Su, parts: Seq<PartView>) -> bool {
    let f = si::SUPPLIER_FIRST as int;
    &&& parts.len() == si::SUPPLIERS_PARTS
    &&& parts[f + si::SU_LAYOUT as int] is U64
    &&& sc::u64s(parts[f + si::SU_LAYOUT as int]).len() == 2
    &&& s.ns as int == sc::u64s(parts[f + si::SU_LAYOUT as int])[0]
    &&& s.bs as int == sc::u64s(parts[f + si::SU_LAYOUT as int])[1]
    &&& parts[f + si::SU_SUPPKEY_CODES as int] == PartView::U32(s.key@)
    &&& parts[f + si::SU_SUPPKEY_BASE as int] == PartView::I64(s.key_base@)
    &&& parts[f + si::SU_NAME_OFFS as int] == PartView::U64(s.name_o@)
    &&& parts[f + si::SU_NAME_BYTES as int] == PartView::U8(s.name_y@)
    &&& parts[f + si::SU_ADDRESS_OFFS as int] == PartView::U64(s.addr_o@)
    &&& parts[f + si::SU_ADDRESS_BYTES as int] == PartView::U8(s.addr_y@)
    &&& parts[f + si::SU_PHONE_OFFS as int] == PartView::U64(s.phone_o@)
    &&& parts[f + si::SU_PHONE_BYTES as int] == PartView::U8(s.phone_y@)
    &&& parts[f + si::SU_KEYIDX_KIND as int] is U64
    &&& sc::u64s(parts[f + si::SU_KEYIDX_KIND as int]).len() == 1
    &&& s.kind == sc::u64s(parts[f + si::SU_KEYIDX_KIND as int])[0]
}

/// The shape of the supplier slices and their text ranges.
pub open spec fn su_shape(s: Su) -> bool {
    &&& s.bs >= 1
    &&& s.key@.len() == s.ns
    &&& s.key_base@.len() * s.bs >= s.ns
    &&& s.name_o@.len() == s.ns + 1 && s.addr_o@.len() == s.ns + 1 && s.phone_o@.len() == s.ns + 1
    &&& forall|j: int| 0 <= j < s.ns ==> #[trigger] sc::text_range_ok(s.name_o@, s.name_y@, j)
            && sc::text_range_ok(s.addr_o@, s.addr_y@, j) && sc::text_range_ok(s.phone_o@, s.phone_y@, j)
}

/// The output columns of supplier row `j`.
pub open spec fn su_row_ok(s: Su, r: Row, j: int) -> bool {
    &&& r.len() == 7
    &&& r[0] == Val::Int(skey_v(s, j))
    &&& r[1] == Val::Text(sc::text_of(s.name_o@, s.name_y@, j))
    &&& r[2] == Val::Text(sc::text_of(s.addr_o@, s.addr_y@, j))
    &&& r[4] == Val::Text(sc::text_of(s.phone_o@, s.phone_y@, j))
}

/// The part kinds and lengths the loader needs, from `represents`.
pub proof fn lemma_su_parts(parts: Seq<PartView>, rels: Seq<Seq<Row>>)
    requires si::represents(parts, rels),
    ensures ({
        let f = si::SUPPLIER_FIRST as int;
        let ns = rels[1].len() as int;
        let bs = sc::u64s(parts[f])[1] as int;
        &&& parts.len() == si::SUPPLIERS_PARTS
        &&& parts[f + si::SU_LAYOUT as int] is U64 && sc::u64s(parts[f + si::SU_LAYOUT as int]).len() == 2
        &&& sc::u64s(parts[f + si::SU_LAYOUT as int])[0] == ns
        &&& bs >= 1 && ns + bs <= u64::MAX
        &&& parts[f + si::SU_SUPPKEY_CODES as int] is U32 && part_len(parts[f + si::SU_SUPPKEY_CODES as int]) == ns
        &&& parts[f + si::SU_SUPPKEY_BASE as int] is I64 && part_len(parts[f + si::SU_SUPPKEY_BASE as int]) * bs >= ns
        &&& parts[f + si::SU_NAME_OFFS as int] is U64 && part_len(parts[f + si::SU_NAME_OFFS as int]) == ns + 1
        &&& parts[f + si::SU_NAME_BYTES as int] is U8
        &&& parts[f + si::SU_ADDRESS_OFFS as int] is U64 && part_len(parts[f + si::SU_ADDRESS_OFFS as int]) == ns + 1
        &&& parts[f + si::SU_ADDRESS_BYTES as int] is U8
        &&& parts[f + si::SU_PHONE_OFFS as int] is U64 && part_len(parts[f + si::SU_PHONE_OFFS as int]) == ns + 1
        &&& parts[f + si::SU_PHONE_BYTES as int] is U8
        &&& parts[f + si::SU_KEYIDX_KIND as int] is U64 && part_len(parts[f + si::SU_KEYIDX_KIND as int]) == 1
    }),
{
    let f = si::SUPPLIER_FIRST as int;
    let tp = parts.subrange(f, f + si::SU_PARTS as int);
    assert(si::supplier_ok(tp, rels[1]));
    assert forall|k: int| 0 <= k < si::SU_PARTS implies #[trigger] tp[k] == parts[f + k] by {}
    let ns = rels[1].len() as int;
    let bs = sc::u64s(tp[0])[1] as int;
    sc::lemma_uniform_groups(tp[1], ns, bs);
    sc::lemma_nblocks(ns, bs);
}

/// Every supplier row of a bound database is its stored row, with text ranges inside their byte parts.
pub proof fn lemma_su_db(s: Su, sv: StoresView, db: Database)
    requires
        bound_db(sv, db),
        su_link(s, sv.suppliers),
    ensures
        su_shape(s),
        s.ns == db.tables[5].len(),
        forall|j: int| 0 <= j < s.ns ==> su_row_ok(s, #[trigger] db.tables[5][j], j),
        crate::stores::suppliers::interface::common::keyidx::keyidx_ok(s.key@, s.key_base@, Seq::<u32>::empty(),
            Seq::<u64>::empty(), s.bs as int, s.kind, s.ns as int),
{
    let parts = sv.suppliers;
    let rels = crate::stores::suppliers::declaration::stored_relations(db);
    assert(si::represents(parts, rels));
    lemma_su_parts(parts, rels);
    let f = si::SUPPLIER_FIRST as int;
    let tp = parts.subrange(f, f + si::SU_PARTS as int);
    assert(si::supplier_ok(tp, rels[1]));
    assert forall|k: int| 0 <= k < si::SU_PARTS implies #[trigger] tp[k] == parts[f + k] by {}
    let rel = rels[1];
    let ns = s.ns as int;
    let bs = s.bs as int;
    let t5 = db.tables[5];
    crate::stores::suppliers::declaration::lemma_stored_relations(db);
    lemma_proj_all_index(t5, crate::stores::suppliers::declaration::stored_cols_t1());
    super::body::lemma_supp_typed(db);
    assert(rel.len() == ns);
    assert forall|j: int| 0 <= j < ns implies su_row_ok(s, #[trigger] t5[j], j) by {
        crate::stores::suppliers::interface::common::read::lemma_for_row(tp[1], ns, bs, tp[3], tp[2], j);
        assert(rel[j] == proj(t5[j], crate::stores::suppliers::declaration::stored_cols_t1()));
        assert(super::body::supp_typed(t5[j]));
        assert(rel[j][0] == t5[j][0] && rel[j][1] == t5[j][1] && rel[j][2] == t5[j][2] && rel[j][4] == t5[j][4]);
        assert(rel[j][0] == Val::Int(sc::for_at(sc::u64s(tp[1]), tp[3], tp[2], j)));
        assert(rel[j][1] == Val::Text(sc::text_of(s.name_o@, s.name_y@, j)));
        assert(rel[j][2] == Val::Text(sc::text_of(s.addr_o@, s.addr_y@, j)));
        assert(rel[j][4] == Val::Text(sc::text_of(s.phone_o@, s.phone_y@, j)));
    }
    assert forall|j: int| 0 <= j < ns implies #[trigger] sc::text_range_ok(s.name_o@, s.name_y@, j)
        && sc::text_range_ok(s.addr_o@, s.addr_y@, j) && sc::text_range_ok(s.phone_o@, s.phone_y@, j) by {
        assert(sc::text_parts_wf(s.name_o@, s.name_y@, ns));
        assert(sc::text_parts_wf(s.addr_o@, s.addr_y@, ns));
        assert(sc::text_parts_wf(s.phone_o@, s.phone_y@, ns));
    }
}

/// Reads the supplier columns of `suppliers` (whole parts).
pub fn load_su(st: &mut StoredParts, Ghost(rels): Ghost<Seq<Seq<Row>>>) -> (s: Su)
    requires si::represents(old(st)@, rels),
    ensures
        final(st)@ == old(st)@,
        su_link(s, old(st)@),
{
    let ghost parts = st@;
    proof {
        lemma_su_parts(parts, rels);
    }
    let f = si::SUPPLIER_FIRST;
    let lay = st.extent_u64(f + si::SU_LAYOUT, 0, 2);
    let ns = st.part_len(f + si::SU_SUPPKEY_CODES);
    let nkb = st.part_len(f + si::SU_SUPPKEY_BASE);
    let bs64 = lay[1];
    proof {
        assert(lay@ =~= sc::u64s(parts[f + si::SU_LAYOUT as int]));
    }
    let bs: u64 = bs64;
    let key = st.extent_u32(f + si::SU_SUPPKEY_CODES, 0, ns);
    let key_base = st.extent_i64(f + si::SU_SUPPKEY_BASE, 0, nkb);
    let nl = st.part_len(f + si::SU_NAME_BYTES);
    let nol = st.part_len(f + si::SU_NAME_OFFS);
    let name_o = st.extent_u64(f + si::SU_NAME_OFFS, 0, nol);
    let name_y = st.extent_u8(f + si::SU_NAME_BYTES, 0, nl);
    let al = st.part_len(f + si::SU_ADDRESS_BYTES);
    let aol = st.part_len(f + si::SU_ADDRESS_OFFS);
    let addr_o = st.extent_u64(f + si::SU_ADDRESS_OFFS, 0, aol);
    let addr_y = st.extent_u8(f + si::SU_ADDRESS_BYTES, 0, al);
    let pl = st.part_len(f + si::SU_PHONE_BYTES);
    let pol = st.part_len(f + si::SU_PHONE_OFFS);
    let phone_o = st.extent_u64(f + si::SU_PHONE_OFFS, 0, pol);
    let phone_y = st.extent_u8(f + si::SU_PHONE_BYTES, 0, pl);
    let kd = st.extent_u64(f + si::SU_KEYIDX_KIND, 0, 1);
    let kind = kd[0];
    proof {
        assert(kd@ =~= sc::u64s(parts[f + si::SU_KEYIDX_KIND as int]));
    }
    let s = Su { key, key_base, name_o, name_y, addr_o, addr_y, phone_o, phone_y, ns, bs, kind };
    proof {
        assert(bs as int == bs64 as int);
        assert(key@ =~= sc::u32s(parts[f + si::SU_SUPPKEY_CODES as int]));
        assert(key_base@ =~= sc::i64s(parts[f + si::SU_SUPPKEY_BASE as int]));
        assert(name_o@ =~= sc::u64s(parts[f + si::SU_NAME_OFFS as int]));
        assert(name_y@ =~= sc::u8s(parts[f + si::SU_NAME_BYTES as int]));
        assert(addr_o@ =~= sc::u64s(parts[f + si::SU_ADDRESS_OFFS as int]));
        assert(addr_y@ =~= sc::u8s(parts[f + si::SU_ADDRESS_BYTES as int]));
        assert(phone_o@ =~= sc::u64s(parts[f + si::SU_PHONE_OFFS as int]));
        assert(phone_y@ =~= sc::u8s(parts[f + si::SU_PHONE_BYTES as int]));
    }
    s
}

} // verus!
