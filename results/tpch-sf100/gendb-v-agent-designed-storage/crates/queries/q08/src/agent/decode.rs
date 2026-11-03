//! Binding of the stored parts to the column model: the slices a scan reads (`cols_from`) decode, for every database
//! bound to the parts, to the database's lineitem, orders, customer and supplier rows (`lemma_li`, `lemma_or`,
//! `lemma_cu`, `lemma_su`), which gives the model's shape facts (`lemma_cols`: `model::cols_ok`) and, with the
//! part filter and the nation statuses (`filters`), the decoded model `bind::dmodel` (`filters::lemma_dmodel`).
//!
//! Block sizes: a table's layout stores its block size `bs` as a `u64`; the scan uses `bs` when `bs <= n` (so it
//! fits `usize`) and otherwise `n` (one block); both give every row the same group (`bs_ok`, `lemma_bs_div`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::spec::value::*;
use crate::link::query::{proj, proj_all};
use crate::stores::factsdir::interface as fi;
use crate::stores::custpart::interface as ci;
use crate::stores::suppliers::interface as si;
use crate::stores::factsdir::interface::common::colfmt as fc;
use crate::stores::custpart::interface::common::colfmt as cc;
use crate::stores::suppliers::interface::common::colfmt as sc;
use crate::stores::factsdir::interface::common::keyidx as fk;
use crate::stores::custpart::interface::common::keyidx as ck;
use crate::stores::suppliers::interface::common::keyidx as sk;
use crate::stores::factsdir::declaration as fd;
use crate::stores::custpart::declaration as cd;
use crate::stores::suppliers::declaration as sd;
use super::sql::*;
use super::join::{key0, join_ok, lemma_keys};
use super::model::*;
use super::bind::*;

verus! {

// ------------------------------------------------------------------------------------------------ block sizes

/// `e` is the scan's block size for a table of `n` rows stored in blocks of `bs`.
pub open spec fn bs_ok(e: int, bs: int, n: int) -> bool {
    &&& e >= 1
    &&& bs <= n ==> e == bs
    &&& bs > n ==> e == (if n >= 1 { n } else { 1 })
}

pub proof fn lemma_bs_div(e: int, bs: int, n: int, j: int)
    requires bs >= 1, bs_ok(e, bs, n), 0 <= j < n,
    ensures j / e == j / bs,
{
    if bs > n {
        vstd::arithmetic::div_mod::lemma_basic_div(j, e);
        vstd::arithmetic::div_mod::lemma_basic_div(j, bs);
    }
}

/// The groups of `bs` rows cover the rows in blocks of `e`.
pub proof fn lemma_bs_len(e: int, bs: int, n: int)
    requires bs >= 1, n >= 0, bs_ok(e, bs, n),
    ensures ((n + bs - 1) / bs) * e >= n, (n + bs - 1) / bs >= 0,
{
    fc::lemma_nblocks(n, bs);
    let q = (n + bs - 1) / bs;
    assert(q == fc::nblocks_of(n, bs));
    if bs <= n {
        assert(q * e >= n) by (nonlinear_arith) requires q * bs >= n, e == bs;
    } else if n >= 1 {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(n + bs - 1, bs, 1, n - 1);
        assert(q == 1 && e == n);
        assert(q * e >= n) by (nonlinear_arith) requires q == 1, e == n;
    } else {
        assert(q * e >= n) by (nonlinear_arith) requires q >= 0, e >= 1, n == 0;
    }
}

proof fn lemma_rebs_f(kc: Seq<u32>, kb: Seq<i64>, ic: Seq<u32>, ib: Seq<u64>, bs: int, e: int, kind: u64, n: int)
    requires
        fk::keyidx_ok(kc, kb, ic, ib, bs, kind, n), bs_ok(e, bs, n),
        kb.len() * e >= n, kind == 2 ==> ib.len() * e >= n,
    ensures fk::keyidx_ok(kc, kb, ic, ib, e, kind, n),
{
    assert forall|j: int| 0 <= j < n implies #[trigger] fk::fkey(kc, kb, e, j) == fk::fkey(kc, kb, bs, j) by {
        lemma_bs_div(e, bs, n, j);
    }
    assert forall|j: int| 0 <= j < n implies #[trigger] fk::fidx(ic, ib, e, j) == fk::fidx(ic, ib, bs, j) by {
        lemma_bs_div(e, bs, n, j);
    }
    if kind == 2 {
        assert(fk::idx_map(ic, ib, e, n) =~= fk::idx_map(ic, ib, bs, n));
    }
    if kind >= 1 {
        assert forall|r: int| 0 <= r < n - 1 implies #[trigger] fk::sorted_at(kc, kb, ic, ib, e, kind, r) by {
            assert(fk::sorted_at(kc, kb, ic, ib, bs, kind, r));
            fk::lemma_irow_bound(kc, kb, ic, ib, bs, kind, n, r);
            fk::lemma_irow_bound(kc, kb, ic, ib, bs, kind, n, r + 1);
            assert(fk::irow(kind, ic, ib, e, r) == fk::irow(kind, ic, ib, bs, r));
            assert(fk::irow(kind, ic, ib, e, r + 1) == fk::irow(kind, ic, ib, bs, r + 1));
        }
    }
}

proof fn lemma_rebs_c(kc: Seq<u32>, kb: Seq<i64>, bs: int, e: int, kind: u64, n: int)
    requires
        ck::keyidx_ok(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), bs, kind, n), bs_ok(e, bs, n), kb.len() * e >= n,
    ensures ck::keyidx_ok(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), e, kind, n),
{
    let (ic, ib) = (Seq::<u32>::empty(), Seq::<u64>::empty());
    assert forall|j: int| 0 <= j < n implies #[trigger] ck::fkey(kc, kb, e, j) == ck::fkey(kc, kb, bs, j) by {
        lemma_bs_div(e, bs, n, j);
    }
    if kind >= 1 {
        assert forall|r: int| 0 <= r < n - 1 implies #[trigger] ck::sorted_at(kc, kb, ic, ib, e, kind, r) by {
            assert(ck::sorted_at(kc, kb, ic, ib, bs, kind, r));
            if kind == 2 {
                assert(ib.len() * bs >= n);
                assert(false) by (nonlinear_arith) requires ib.len() == 0, ib.len() * bs >= n, n >= 2;
            }
        }
    }
}

proof fn lemma_rebs_s(kc: Seq<u32>, kb: Seq<i64>, bs: int, e: int, kind: u64, n: int)
    requires
        sk::keyidx_ok(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), bs, kind, n), bs_ok(e, bs, n), kb.len() * e >= n,
    ensures sk::keyidx_ok(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), e, kind, n),
{
    let (ic, ib) = (Seq::<u32>::empty(), Seq::<u64>::empty());
    assert forall|j: int| 0 <= j < n implies #[trigger] sk::fkey(kc, kb, e, j) == sk::fkey(kc, kb, bs, j) by {
        lemma_bs_div(e, bs, n, j);
    }
    if kind >= 1 {
        assert forall|r: int| 0 <= r < n - 1 implies #[trigger] sk::sorted_at(kc, kb, ic, ib, e, kind, r) by {
            assert(sk::sorted_at(kc, kb, ic, ib, bs, kind, r));
            if kind == 2 {
                assert(ib.len() * bs >= n);
                assert(false) by (nonlinear_arith) requires ib.len() == 0, ib.len() * bs >= n, n >= 2;
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------ table parts

pub open spec fn li_tp(sv: StoresView) -> Seq<PartView> {
    sv.factsdir.subrange(fi::LINEITEM_FIRST as int, (fi::LINEITEM_FIRST + fi::LI_PARTS) as int)
}

pub open spec fn or_tp(sv: StoresView) -> Seq<PartView> {
    sv.factsdir.subrange(fi::ORDERS_FIRST as int, (fi::ORDERS_FIRST + fi::OR_PARTS) as int)
}

/// The inherited parts of storage `facts` inside storage `factsdir`, for a bound database: lineitem, orders and the
/// clustering flag as facts states them (`base_represents` over the first 75 parts).
pub proof fn lemma_fparts(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        sv.factsdir.len() == crate::stores::factsdir::interface::dirs::FACTSDIR_PARTS,
        fi::lineitem_ok(li_tp(sv), fd::stored_relations(db)[0]),
        fi::orders_ok(or_tp(sv), fd::stored_relations(db)[1]),
        sv.factsdir[fi::FACTS_CLUSTER as int] is U64, fc::u64s(sv.factsdir[fi::FACTS_CLUSTER as int]).len() == 1,
        fc::u64s(sv.factsdir[fi::FACTS_CLUSTER as int])[0] == 1 ==> fi::cluster::clustered(
            fi::lineitem_rows(li_tp(sv), fd::stored_relations(db)[0]), fi::orders_rows(or_tp(sv), fd::stored_relations(db)[1])),
{
    let p = sv.factsdir;
    let bp = fi::base_parts(p);
    let rels = fd::stored_relations(db);
    assert(fi::represents(p, rels));
    assert(fi::base_represents(bp, rels));
    assert(bp.subrange(fi::LINEITEM_FIRST as int, (fi::LINEITEM_FIRST + fi::LI_PARTS) as int) =~= li_tp(sv));
    assert(bp.subrange(fi::ORDERS_FIRST as int, (fi::ORDERS_FIRST + fi::OR_PARTS) as int) =~= or_tp(sv));
    assert(bp[fi::FACTS_CLUSTER as int] == p[fi::FACTS_CLUSTER as int]);
}

pub open spec fn cu_tp(sv: StoresView) -> Seq<PartView> {
    sv.custpart.subrange(ci::CUSTOMER_FIRST as int, (ci::CUSTOMER_FIRST + ci::CU_PARTS) as int)
}

pub open spec fn pa_tp(sv: StoresView) -> Seq<PartView> {
    sv.custpart.subrange(ci::PART_FIRST as int, (ci::PART_FIRST + ci::PA_PARTS) as int)
}

pub open spec fn su_tp(sv: StoresView) -> Seq<PartView> {
    sv.suppliers.subrange(si::SUPPLIER_FIRST as int, (si::SUPPLIER_FIRST + si::SU_PARTS) as int)
}

pub open spec fn na_tp(sv: StoresView) -> Seq<PartView> {
    sv.suppliers.subrange(si::NATION_FIRST as int, (si::NATION_FIRST + si::NA_PARTS) as int)
}

pub open spec fn re_tp(sv: StoresView) -> Seq<PartView> {
    sv.suppliers.subrange(si::REGION_FIRST as int, (si::REGION_FIRST + si::RE_PARTS) as int)
}

/// The stored lineitem rows and the stored-to-canonical map of orders.
pub open spec fn lrows_of(sv: StoresView, db: Database) -> Seq<Row> {
    fi::lineitem_rows(li_tp(sv), fd::stored_relations(db)[0])
}

pub open spec fn orows_of(sv: StoresView, db: Database) -> Seq<Row> {
    fi::orders_rows(or_tp(sv), fd::stored_relations(db)[1])
}

pub open spec fn omap_of(sv: StoresView, n: int) -> Seq<int> {
    fi::orders_map(or_tp(sv), n)
}

/// The scan's slices are the parts' values.
pub open spec fn cols_from(sv: StoresView, c: Cols) -> bool {
    let l = li_tp(sv);
    let o = or_tp(sv);
    let cu = cu_tp(sv);
    let su = su_tp(sv);
    &&& c.n_l == fc::u64s(l[fi::LI_LAYOUT as int])[0] && bs_ok(c.bs_l as int, fc::u64s(l[fi::LI_LAYOUT as int])[1] as int, c.n_l as int)
    &&& c.lk_c@ == fc::u32s(l[fi::LI_ORDERKEY_CODES as int]) && c.lk_b@ == fc::i64s(l[fi::LI_ORDERKEY_BASE as int])
    &&& c.lp_c@ == fc::u32s(l[fi::LI_PARTKEY_CODES as int]) && c.lp_b@ == fc::i64s(l[fi::LI_PARTKEY_BASE as int])
    &&& c.ls_c@ == fc::u32s(l[fi::LI_SUPPKEY_CODES as int]) && c.ls_b@ == fc::i64s(l[fi::LI_SUPPKEY_BASE as int])
    &&& c.le_c@ == fc::u32s(l[fi::LI_EXTENDEDPRICE_CODES as int]) && c.le_b@ == fc::i64s(l[fi::LI_EXTENDEDPRICE_BASE as int])
    &&& c.ld_c@ == fc::u8s(l[fi::LI_DISCOUNT_CODES as int]) && c.ld_b@ == fc::i64s(l[fi::LI_DISCOUNT_BASE as int])
    &&& c.n_o == fc::u64s(o[fi::OR_LAYOUT as int])[0] && bs_ok(c.bs_o as int, fc::u64s(o[fi::OR_LAYOUT as int])[1] as int, c.n_o as int)
    &&& c.ok_c@ == fc::u32s(o[fi::OR_ORDERKEY_CODES as int]) && c.ok_b@ == fc::i64s(o[fi::OR_ORDERKEY_BASE as int])
    &&& c.oc_c@ == fc::u32s(o[fi::OR_CUSTKEY_CODES as int]) && c.oc_b@ == fc::i64s(o[fi::OR_CUSTKEY_BASE as int])
    &&& c.od_c@ == o[fi::OR_ORDERDATE_CODES as int]->U16_0 && c.od_b@ == fc::i64s(o[fi::OR_ORDERDATE_BASE as int])
    &&& c.oi_c@ == fc::u32s(o[fi::OR_KEYIDX_CODES as int]) && c.oi_b@ == fc::u64s(o[fi::OR_KEYIDX_BASE as int])
    &&& c.oi_kind == fc::u64s(o[fi::OR_KEYIDX_KIND as int])[0]
    &&& c.n_c == cc::u64s(cu[ci::CU_LAYOUT as int])[0] && bs_ok(c.bs_c as int, cc::u64s(cu[ci::CU_LAYOUT as int])[1] as int, c.n_c as int)
    &&& c.ck_c@ == cc::u32s(cu[ci::CU_CUSTKEY_CODES as int]) && c.ck_b@ == cc::i64s(cu[ci::CU_CUSTKEY_BASE as int])
    &&& c.cn_c@ == cc::u8s(cu[ci::CU_NATIONKEY_CODES as int]) && c.cn_b@ == cc::i64s(cu[ci::CU_NATIONKEY_BASE as int])
    &&& c.c_kind == cc::u64s(cu[ci::CU_KEYIDX_KIND as int])[0]
    &&& c.n_s == sc::u64s(su[si::SU_LAYOUT as int])[0] && bs_ok(c.bs_s as int, sc::u64s(su[si::SU_LAYOUT as int])[1] as int, c.n_s as int)
    &&& c.sk_c@ == sc::u32s(su[si::SU_SUPPKEY_CODES as int]) && c.sk_b@ == sc::i64s(su[si::SU_SUPPKEY_BASE as int])
    &&& c.sn_c@ == sc::u8s(su[si::SU_NATIONKEY_CODES as int]) && c.sn_b@ == sc::i64s(su[si::SU_NATIONKEY_BASE as int])
    &&& c.s_kind == sc::u64s(su[si::SU_KEYIDX_KIND as int])[0]
    &&& c.lo == d95() && c.hi == d96e() && c.d96 == d96()
    &&& c.e32@ == Seq::<u32>::empty() && c.e64@ == Seq::<u64>::empty()
}

// ------------------------------------------------------------------------------------------------ FOR values

/// A FOR value of a facts table with the scan's block size.
pub proof fn lemma_ffor(tp: Seq<PartView>, n: int, e: int, bp: int, cp: int, j: int)
    requires
        tp.len() >= 2, fc::groups_part_ok(tp[1], n, fc::u64s(tp[0])[1] as int),
        bs_ok(e, fc::u64s(tp[0])[1] as int, n), 0 <= j < n,
    ensures fc::for_at(fc::gs_at(tp, 1), tp[bp], tp[cp], j) == fc::base_at(tp[bp], j / e) + fc::code_at(tp[cp], j),
{
    let bs = fc::u64s(tp[0])[1] as int;
    fi::common::read::lemma_for_row(tp[1], n, bs, tp[bp], tp[cp], j);
    lemma_bs_div(e, bs, n, j);
}

pub proof fn lemma_cfor(tp: Seq<PartView>, n: int, e: int, bp: int, cp: int, j: int)
    requires
        tp.len() >= 2, cc::groups_part_ok(tp[1], n, cc::u64s(tp[0])[1] as int),
        bs_ok(e, cc::u64s(tp[0])[1] as int, n), 0 <= j < n,
    ensures cc::for_at(cc::gs_at(tp, 1), tp[bp], tp[cp], j) == cc::base_at(tp[bp], j / e) + cc::code_at(tp[cp], j),
{
    let bs = cc::u64s(tp[0])[1] as int;
    ci::common::read::lemma_for_row(tp[1], n, bs, tp[bp], tp[cp], j);
    lemma_bs_div(e, bs, n, j);
}

pub proof fn lemma_sfor(tp: Seq<PartView>, n: int, e: int, bp: int, cp: int, j: int)
    requires
        tp.len() >= 2, sc::groups_part_ok(tp[1], n, sc::u64s(tp[0])[1] as int),
        bs_ok(e, sc::u64s(tp[0])[1] as int, n), 0 <= j < n,
    ensures sc::for_at(sc::gs_at(tp, 1), tp[bp], tp[cp], j) == sc::base_at(tp[bp], j / e) + sc::code_at(tp[cp], j),
{
    let bs = sc::u64s(tp[0])[1] as int;
    si::common::read::lemma_for_row(tp[1], n, bs, tp[bp], tp[cp], j);
    lemma_bs_div(e, bs, n, j);
}

/// Base part lengths cover the rows in the scan's blocks.
pub proof fn lemma_fbases(tp: Seq<PartView>, n: int, e: int, bp: int)
    requires
        tp.len() >= 2, fc::groups_part_ok(tp[1], n, fc::u64s(tp[0])[1] as int),
        bs_ok(e, fc::u64s(tp[0])[1] as int, n),
        crate::gendb_entry::stored::part_len(tp[bp]) == fc::gs_at(tp, 1).len() - 1,
    ensures crate::gendb_entry::stored::part_len(tp[bp]) * e >= n,
{
    let bs = fc::u64s(tp[0])[1] as int;
    fc::lemma_uniform_groups(tp[1], n, bs);
    lemma_bs_len(e, bs, n);
}

pub proof fn lemma_cbases(tp: Seq<PartView>, n: int, e: int, bp: int)
    requires
        tp.len() >= 2, cc::groups_part_ok(tp[1], n, cc::u64s(tp[0])[1] as int),
        bs_ok(e, cc::u64s(tp[0])[1] as int, n),
        crate::gendb_entry::stored::part_len(tp[bp]) == cc::gs_at(tp, 1).len() - 1,
    ensures crate::gendb_entry::stored::part_len(tp[bp]) * e >= n,
{
    let bs = cc::u64s(tp[0])[1] as int;
    cc::lemma_uniform_groups(tp[1], n, bs);
    lemma_bs_len(e, bs, n);
}

pub proof fn lemma_sbases(tp: Seq<PartView>, n: int, e: int, bp: int)
    requires
        tp.len() >= 2, sc::groups_part_ok(tp[1], n, sc::u64s(tp[0])[1] as int),
        bs_ok(e, sc::u64s(tp[0])[1] as int, n),
        crate::gendb_entry::stored::part_len(tp[bp]) == sc::gs_at(tp, 1).len() - 1,
    ensures crate::gendb_entry::stored::part_len(tp[bp]) * e >= n,
{
    let bs = sc::u64s(tp[0])[1] as int;
    sc::lemma_uniform_groups(tp[1], n, bs);
    lemma_bs_len(e, bs, n);
}

// ------------------------------------------------------------------------------------------------ lineitem

/// Shapes of the lineitem slices.
pub open spec fn li_shape(c: Cols) -> bool {
    &&& c.bs_l >= 1
    &&& c.lk_c@.len() == c.n_l && c.lp_c@.len() == c.n_l && c.ls_c@.len() == c.n_l
    &&& c.le_c@.len() == c.n_l && c.ld_c@.len() == c.n_l
    &&& c.lp_b@.len() == c.lk_b@.len() && c.ls_b@.len() == c.lk_b@.len()
    &&& c.le_b@.len() == c.lk_b@.len() && c.ld_b@.len() == c.lk_b@.len()
    &&& c.lk_b@.len() * c.bs_l >= c.n_l
}

pub proof fn lemma_li(sv: StoresView, db: Database, c: Cols)
    requires bound_db(sv, db), cols_from(sv, c),
    ensures
        li_shape(c),
        lrows_of(sv, db).len() == c.n_l,
        lrows_of(sv, db).to_multiset() == proj_all(db.tables[0], fd::stored_cols_t0()).to_multiset(),
        forall|j: int| 0 <= j < c.n_l ==> lrow_ok(c, #[trigger] lrows_of(sv, db)[j], j),
        forall|j: int| 0 <= j < c.n_l ==> in_i64(#[trigger] lk(c, j)) && in_i64(lp(c, j)) && in_i64(ls(c, j)),
        forall|j: int| 0 <= j < c.n_l ==> coeff15(#[trigger] le(c, j)) && coeff15(ld(c, j)),
{
    let tp = li_tp(sv);
    let rels = fd::stored_relations(db);
    let rel = rels[0];
    lemma_fparts(sv, db);
    assert(fi::lineitem_ok(tp, rel));
    let n = rel.len() as int;
    let lmap = fi::lineitem_map(tp, n);
    let rows = lrows_of(sv, db);
    assert(fc::is_perm(lmap, n));
    fc::lemma_stored_rows_multiset(rel, lmap);
    assert(fi::lineitem_cols_ok(tp, rows));
    let e = c.bs_l as int;
    let bs = fc::u64s(tp[0])[1] as int;
    assert(c.n_l == n);
    lemma_fbases(tp, n, e, fi::LI_ORDERKEY_BASE as int);
    let cols = fd::stored_cols_t0();
    crate::link::source::lemma_proj_all_index(db.tables[0], cols);
    lemma_tables_typed(db);
    assert forall|j: int| #![trigger rows[j]] #![trigger lk(c, j)] #![trigger le(c, j)]
        0 <= j < c.n_l implies lrow_ok(c, rows[j], j) && in_i64(lk(c, j)) && in_i64(lp(c, j))
        && in_i64(ls(c, j)) && coeff15(le(c, j)) && coeff15(ld(c, j)) by {
        lemma_ffor(tp, n, e, fi::LI_ORDERKEY_BASE as int, fi::LI_ORDERKEY_CODES as int, j);
        lemma_ffor(tp, n, e, fi::LI_PARTKEY_BASE as int, fi::LI_PARTKEY_CODES as int, j);
        lemma_ffor(tp, n, e, fi::LI_SUPPKEY_BASE as int, fi::LI_SUPPKEY_CODES as int, j);
        lemma_ffor(tp, n, e, fi::LI_EXTENDEDPRICE_BASE as int, fi::LI_EXTENDEDPRICE_CODES as int, j);
        lemma_ffor(tp, n, e, fi::LI_DISCOUNT_BASE as int, fi::LI_DISCOUNT_CODES as int, j);
        let i = lmap[j];
        assert(0 <= i < n);
        assert(rows[j] == rel[i]);
        let r = db.tables[0][i];
        assert(li_typed(r));
        assert(rel[i][0] == r[0] && rel[i][1] == r[1] && rel[i][2] == r[2] && rel[i][5] == r[5] && rel[i][6] == r[6]);
        assert(crate::spec::numeric::pow10(15) == 1_000_000_000_000_000) by (compute_only);
    }
}

// ------------------------------------------------------------------------------------------------ orders

pub open spec fn or_shape(c: Cols) -> bool {
    &&& c.bs_o >= 1
    &&& c.ok_c@.len() == c.n_o && c.oc_c@.len() == c.n_o && c.od_c@.len() == c.n_o
    &&& c.oc_b@.len() == c.ok_b@.len() && c.od_b@.len() == c.ok_b@.len()
    &&& c.ok_b@.len() * c.bs_o >= c.n_o
    &&& fk::keyidx_ok(c.ok_c@, c.ok_b@, c.oi_c@, c.oi_b@, c.bs_o as int, c.oi_kind, c.n_o as int)
}

pub proof fn lemma_or(sv: StoresView, db: Database, c: Cols)
    requires bound_db(sv, db), cols_from(sv, c),
    ensures
        or_shape(c),
        orders_ok(db, c, omap_of(sv, c.n_o as int)),
        orows_of(sv, db).len() == c.n_o,
        forall|p: int| 0 <= p < c.n_o ==> (#[trigger] orows_of(sv, db)[p])[0] == Val::Int(okey(c, p)),
        forall|p: int| 0 <= p < c.n_o ==> in_i64(#[trigger] okey(c, p)) && in_i64(oc(c, p)) && in_i64(od(c, p)),
        forall|a: int, b: int| 0 <= a < c.n_o && 0 <= b < c.n_o && a != b ==> #[trigger] okey(c, a) != #[trigger] okey(c, b),
{
    let tp = or_tp(sv);
    let rel = fd::stored_relations(db)[1];
    lemma_fparts(sv, db);
    assert(fi::orders_ok(tp, rel));
    lemma_tables_typed(db);
    lemma_keys(db);
    lemma_or_rows(tp, rel, db, c);
    lemma_or_idx(tp, rel, c);
}

proof fn lemma_or_rows(tp: Seq<PartView>, rel: Seq<Row>, db: Database, c: Cols)
    requires
        fi::orders_ok(tp, rel),
        rel == fd::stored_relations(db)[1],
        tables_typed(db), key0(db.tables[1]),
        c.n_o == fc::u64s(tp[fi::OR_LAYOUT as int])[0], bs_ok(c.bs_o as int, fc::u64s(tp[fi::OR_LAYOUT as int])[1] as int, c.n_o as int),
        c.ok_c@ == fc::u32s(tp[fi::OR_ORDERKEY_CODES as int]) && c.ok_b@ == fc::i64s(tp[fi::OR_ORDERKEY_BASE as int]),
        c.oc_c@ == fc::u32s(tp[fi::OR_CUSTKEY_CODES as int]) && c.oc_b@ == fc::i64s(tp[fi::OR_CUSTKEY_BASE as int]),
        c.od_c@ == tp[fi::OR_ORDERDATE_CODES as int]->U16_0 && c.od_b@ == fc::i64s(tp[fi::OR_ORDERDATE_BASE as int]),
    ensures
        orders_ok(db, c, fi::orders_map(tp, c.n_o as int)),
        fi::orders_rows(tp, rel).len() == c.n_o,
        forall|p: int| 0 <= p < c.n_o ==> (#[trigger] fi::orders_rows(tp, rel)[p])[0] == Val::Int(okey(c, p)),
        forall|p: int| 0 <= p < c.n_o ==> in_i64(#[trigger] okey(c, p)) && in_i64(oc(c, p)) && in_i64(od(c, p)),
        forall|a: int, b: int| 0 <= a < c.n_o && 0 <= b < c.n_o && a != b ==> #[trigger] okey(c, a) != #[trigger] okey(c, b),
{
    let n = rel.len() as int;
    let omap = fi::orders_map(tp, n);
    let rows = fi::orders_rows(tp, rel);
    assert(fc::is_perm(omap, n));
    assert(fi::orders_cols_ok(tp, rows));
    let e = c.bs_o as int;
    let cols = fd::stored_cols_t1();
    crate::link::source::lemma_proj_all_index(db.tables[1], cols);
    let t = db.tables[1];
    assert forall|p: int| #![trigger omap[p]] #![trigger okey(c, p)] #![trigger rows[p]]
        0 <= p < c.n_o implies 0 <= omap[p] < c.n_o && orow_ok(c, t[omap[p]], p)
        && rows[p][0] == Val::Int(okey(c, p)) && in_i64(okey(c, p)) && in_i64(oc(c, p)) && in_i64(od(c, p)) by {
        lemma_ffor(tp, n, e, fi::OR_ORDERKEY_BASE as int, fi::OR_ORDERKEY_CODES as int, p);
        lemma_ffor(tp, n, e, fi::OR_CUSTKEY_BASE as int, fi::OR_CUSTKEY_CODES as int, p);
        lemma_ffor(tp, n, e, fi::OR_ORDERDATE_BASE as int, fi::OR_ORDERDATE_CODES as int, p);
        let i = omap[p];
        assert(rows[p] == rel[i]);
        assert(cols[4] == 4);
        assert(rel[i][0] == t[i][0] && rel[i][1] == t[i][1] && rel[i][4] == t[i][4]);
        assert(or_typed(t[i]));
    }
    assert forall|i: int| 0 <= i < c.n_o implies #[trigger] ocovered(omap, i) by {
        assert(fc::covered(omap, i));
    }
    assert forall|a: int, b: int| 0 <= a < c.n_o && 0 <= b < c.n_o && a != b implies #[trigger] okey(c, a) != #[trigger] okey(c, b) by {
        assert(orow_ok(c, t[omap[a]], a) && orow_ok(c, t[omap[b]], b));
        if okey(c, a) == okey(c, b) {
            assert(t[omap[a]][0] == t[omap[b]][0]);
            assert(omap[a] == omap[b]);
        }
    }
}

proof fn lemma_or_idx(tp: Seq<PartView>, rel: Seq<Row>, c: Cols)
    requires
        fi::orders_ok(tp, rel),
        c.n_o == fc::u64s(tp[fi::OR_LAYOUT as int])[0], bs_ok(c.bs_o as int, fc::u64s(tp[fi::OR_LAYOUT as int])[1] as int, c.n_o as int),
        c.ok_c@ == fc::u32s(tp[fi::OR_ORDERKEY_CODES as int]) && c.ok_b@ == fc::i64s(tp[fi::OR_ORDERKEY_BASE as int]),
        c.oc_c@ == fc::u32s(tp[fi::OR_CUSTKEY_CODES as int]) && c.oc_b@ == fc::i64s(tp[fi::OR_CUSTKEY_BASE as int]),
        c.od_c@ == tp[fi::OR_ORDERDATE_CODES as int]->U16_0 && c.od_b@ == fc::i64s(tp[fi::OR_ORDERDATE_BASE as int]),
        c.oi_c@ == fc::u32s(tp[fi::OR_KEYIDX_CODES as int]) && c.oi_b@ == fc::u64s(tp[fi::OR_KEYIDX_BASE as int]),
        c.oi_kind == fc::u64s(tp[fi::OR_KEYIDX_KIND as int])[0],
    ensures or_shape(c),
{
    let n = rel.len() as int;
    let rows = fi::orders_rows(tp, rel);
    assert(fi::orders_cols_ok(tp, rows));
    let e = c.bs_o as int;
    let bs = fc::u64s(tp[0])[1] as int;
    lemma_fbases(tp, n, e, fi::OR_ORDERKEY_BASE as int);
    let kc = fc::u32s(tp[fi::OR_ORDERKEY_CODES as int]);
    let kb = fc::i64s(tp[fi::OR_ORDERKEY_BASE as int]);
    let ic = fc::u32s(tp[fi::OR_KEYIDX_CODES as int]);
    let ib = fc::u64s(tp[fi::OR_KEYIDX_BASE as int]);
    let kind = fc::u64s(tp[fi::OR_KEYIDX_KIND as int])[0];
    lemma_keyidx_len(kc, kb, ic, ib, bs, e, kind, n, kb.len() as int);
    lemma_rebs_f(kc, kb, ic, ib, bs, e, kind, n);
}

/// The index's base part has the key base part's group count, so it covers the rows in the scan's blocks.
proof fn lemma_keyidx_len(kc: Seq<u32>, kb: Seq<i64>, ic: Seq<u32>, ib: Seq<u64>, bs: int, e: int, kind: u64, n: int, m: int)
    requires
        fk::keyidx_ok(kc, kb, ic, ib, bs, kind, n), bs_ok(e, bs, n), m == kb.len(), m * e >= n,
    ensures kind == 2 ==> ib.len() * e >= n,
{
    if kind == 2 && n > 0 {
        // ib.len() * bs >= n: with one block (bs > n), ib has an entry, so ib.len() * n >= n.
        if bs <= n {
        } else {
            assert(ib.len() >= 1) by (nonlinear_arith) requires ib.len() * bs >= n, n > 0, ib.len() >= 0;
            assert(ib.len() * e >= n) by (nonlinear_arith) requires ib.len() >= 1, e == n, n > 0;
        }
    }
}

// ------------------------------------------------------------------------------------------------ customer, supplier

pub open spec fn cu_shape(c: Cols) -> bool {
    &&& c.bs_c >= 1
    &&& c.ck_c@.len() == c.n_c && c.cn_c@.len() == c.n_c && c.cn_b@.len() == c.ck_b@.len()
    &&& c.ck_b@.len() * c.bs_c >= c.n_c
    &&& ck::keyidx_ok(c.ck_c@, c.ck_b@, Seq::<u32>::empty(), Seq::<u64>::empty(), c.bs_c as int, c.c_kind, c.n_c as int)
}

pub proof fn lemma_cu(sv: StoresView, db: Database, c: Cols)
    requires bound_db(sv, db), cols_from(sv, c),
    ensures
        cu_shape(c),
        cust_ok(db, c),
        forall|i: int| 0 <= i < c.n_c ==> in_i64(#[trigger] ck(c, i)) && in_i64(cn(c, i)),
        forall|a: int, b: int| 0 <= a < c.n_c && 0 <= b < c.n_c && a != b ==> #[trigger] ck(c, a) != #[trigger] ck(c, b),
{
    let tp = cu_tp(sv);
    let rel = cd::stored_relations(db)[0];
    assert(ci::customer_ok(tp, rel));
    let n = rel.len() as int;
    let e = c.bs_c as int;
    let bs = cc::u64s(tp[0])[1] as int;
    lemma_cbases(tp, n, e, ci::CU_CUSTKEY_BASE as int);
    let cols = cd::stored_cols_t0();
    crate::link::source::lemma_proj_all_index(db.tables[2], cols);
    lemma_tables_typed(db);
    lemma_keys(db);
    let t = db.tables[2];
    assert forall|i: int| #![trigger t[i]] #![trigger ck(c, i)] 0 <= i < c.n_c implies t[i][0] == Val::Int(ck(c, i))
        && t[i][3] == Val::Int(cn(c, i)) && in_i64(ck(c, i)) && in_i64(cn(c, i)) by {
        lemma_cfor(tp, n, e, ci::CU_CUSTKEY_BASE as int, ci::CU_CUSTKEY_CODES as int, i);
        lemma_cfor(tp, n, e, ci::CU_NATIONKEY_BASE as int, ci::CU_NATIONKEY_CODES as int, i);
        assert(rel[i][0] == t[i][0] && rel[i][3] == t[i][3]);
        assert(cu_typed(t[i]));
    }
    assert forall|a: int, b: int| 0 <= a < c.n_c && 0 <= b < c.n_c && a != b implies #[trigger] ck(c, a) != #[trigger] ck(c, b) by {
        assert(t[a][0] == Val::Int(ck(c, a)) && t[b][0] == Val::Int(ck(c, b)));
    }
    lemma_rebs_c(c.ck_c@, c.ck_b@, bs, e, c.c_kind, n);
}

pub open spec fn su_shape(c: Cols) -> bool {
    &&& c.bs_s >= 1
    &&& c.sk_c@.len() == c.n_s && c.sn_c@.len() == c.n_s && c.sn_b@.len() == c.sk_b@.len()
    &&& c.sk_b@.len() * c.bs_s >= c.n_s
    &&& sk::keyidx_ok(c.sk_c@, c.sk_b@, Seq::<u32>::empty(), Seq::<u64>::empty(), c.bs_s as int, c.s_kind, c.n_s as int)
}

pub proof fn lemma_su(sv: StoresView, db: Database, c: Cols)
    requires bound_db(sv, db), cols_from(sv, c),
    ensures
        su_shape(c),
        supp_ok(db, c),
        forall|i: int| 0 <= i < c.n_s ==> in_i64(#[trigger] sk(c, i)) && in_i64(sn(c, i)),
        forall|a: int, b: int| 0 <= a < c.n_s && 0 <= b < c.n_s && a != b ==> #[trigger] sk(c, a) != #[trigger] sk(c, b),
{
    let tp = su_tp(sv);
    let rel = sd::stored_relations(db)[1];
    assert(si::supplier_ok(tp, rel));
    let n = rel.len() as int;
    let e = c.bs_s as int;
    let bs = sc::u64s(tp[0])[1] as int;
    lemma_sbases(tp, n, e, si::SU_SUPPKEY_BASE as int);
    let cols = sd::stored_cols_t1();
    crate::link::source::lemma_proj_all_index(db.tables[5], cols);
    lemma_tables_typed(db);
    lemma_keys(db);
    let t = db.tables[5];
    assert forall|i: int| #![trigger t[i]] #![trigger sk(c, i)] 0 <= i < c.n_s implies t[i][0] == Val::Int(sk(c, i))
        && t[i][3] == Val::Int(sn(c, i)) && in_i64(sk(c, i)) && in_i64(sn(c, i)) by {
        lemma_sfor(tp, n, e, si::SU_SUPPKEY_BASE as int, si::SU_SUPPKEY_CODES as int, i);
        lemma_sfor(tp, n, e, si::SU_NATIONKEY_BASE as int, si::SU_NATIONKEY_CODES as int, i);
        assert(rel[i][0] == t[i][0] && rel[i][3] == t[i][3]);
        assert(su_typed(t[i]));
    }
    assert forall|a: int, b: int| 0 <= a < c.n_s && 0 <= b < c.n_s && a != b implies #[trigger] sk(c, a) != #[trigger] sk(c, b) by {
        assert(t[a][0] == Val::Int(sk(c, a)) && t[b][0] == Val::Int(sk(c, b)));
    }
    lemma_rebs_s(c.sk_c@, c.sk_b@, bs, e, c.s_kind, n);
}

// ------------------------------------------------------------------------------------------------ the column model

/// The slices of a bound database satisfy the column model's facts.
pub proof fn lemma_cols(sv: StoresView, db: Database, c: Cols)
    requires bound_db(sv, db), cols_from(sv, c),
    ensures cols_ok(c),
{
    lemma_li(sv, db, c);
    lemma_or(sv, db, c);
    lemma_cu(sv, db, c);
    lemma_su(sv, db, c);
}

/// The co-clustering flag: the stored lineitem rows follow the stored orders.
pub open spec fn cluster_flag(sv: StoresView) -> u64 {
    fc::u64s(sv.factsdir[fi::FACTS_CLUSTER as int])[0]
}

pub proof fn lemma_clustered(sv: StoresView, db: Database, c: Cols)
    requires bound_db(sv, db), cols_from(sv, c), cluster_flag(sv) == 1,
    ensures lines_clustered(c),
{
    lemma_li(sv, db, c);
    lemma_or(sv, db, c);
    let lrows = lrows_of(sv, db);
    let orows = orows_of(sv, db);
    lemma_fparts(sv, db);
    assert(fi::cluster::clustered(lrows, orows));
    assert forall|k: int| #[trigger] rpos(c, k) == fi::cluster::order_pos(orows, Val::Int(k)) by {
        lemma_rpos(c, k);
        let p = rpos(c, k);
        assert forall|q: int| 0 <= q < orows.len() && q != p implies #[trigger] orows[q][0] != Val::Int(k) by {
            assert(orows[q][0] == Val::Int(okey(c, q)));
            if p < c.n_o {
                assert(okey(c, q) != okey(c, p));
            }
        }
        fi::cluster::lemma_order_pos_at(orows, Val::Int(k), p);
    }
    assert forall|j: int| 0 <= j < c.n_l - 1 implies #[trigger] lstep(c, j) by {
        assert(fi::cluster::cluster_step(lrows, orows, j));
        assert(lrow_ok(c, lrows[j], j) && lrow_ok(c, lrows[j + 1], j + 1));
        assert(rpos(c, lk(c, j)) == fi::cluster::order_pos(orows, Val::Int(lk(c, j))));
        assert(rpos(c, lk(c, j + 1)) == fi::cluster::order_pos(orows, Val::Int(lk(c, j + 1))));
    }
}

} // verus!
