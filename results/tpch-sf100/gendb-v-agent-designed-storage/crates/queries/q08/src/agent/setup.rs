//! Setup of the Q8 scan on the calling thread: whole-part reads, the column model's slices (`load_cols`), the part
//! filter (`build_pfilter`: the keys of the parts of type `$3` as bitmaps) and the nation statuses (`build_ntab`).
//! Each result is tied to the stored parts (`decode::cols_from`, `filters::pf_from`, `filters::ntab_from`) and has
//! the facts the scan kernel needs (`model::cols_ok` via `decode::lemma_cols`, `kernel::pf_ok`, `kernel::ntab_ok`).
use vstd::prelude::*;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::stored::StoredParts;
use crate::gendb_entry::bound_db;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::stores::factsdir::interface as fi;
use crate::stores::custpart::interface as ci;
use crate::stores::suppliers::interface as si;
use crate::stores::factsdir::interface::common::colfmt as fc;
use crate::stores::custpart::interface::common::colfmt as cc;
use crate::stores::suppliers::interface::common::colfmt as sc;
use crate::stores::factsdir::declaration as fd;
use crate::stores::custpart::declaration as cd;
use crate::stores::suppliers::declaration as sd;
use super::sql::*;
use super::model::*;
use super::kernel::*;
use super::bind::*;
use super::decode::*;
use super::filters::*;

verus! {

// ------------------------------------------------------------------------------------------------ whole parts

pub fn whole_u8(st: &mut StoredParts, p: usize) -> (r: &'static [u8])
    requires p < old(st)@.len(), old(st)@[p as int] is U8,
    ensures final(st)@ == old(st)@, r@ == old(st)@[p as int]->U8_0,
{
    let n = st.part_len(p);
    let r = st.extent_u8(p, 0, n);
    proof { assert(r@ =~= old(st)@[p as int]->U8_0); }
    r
}

pub fn whole_u16(st: &mut StoredParts, p: usize) -> (r: &'static [u16])
    requires p < old(st)@.len(), old(st)@[p as int] is U16,
    ensures final(st)@ == old(st)@, r@ == old(st)@[p as int]->U16_0,
{
    let n = st.part_len(p);
    let r = st.extent_u16(p, 0, n);
    proof { assert(r@ =~= old(st)@[p as int]->U16_0); }
    r
}

pub fn whole_u32(st: &mut StoredParts, p: usize) -> (r: &'static [u32])
    requires p < old(st)@.len(), old(st)@[p as int] is U32,
    ensures final(st)@ == old(st)@, r@ == old(st)@[p as int]->U32_0,
{
    let n = st.part_len(p);
    let r = st.extent_u32(p, 0, n);
    proof { assert(r@ =~= old(st)@[p as int]->U32_0); }
    r
}

pub fn whole_u64(st: &mut StoredParts, p: usize) -> (r: &'static [u64])
    requires p < old(st)@.len(), old(st)@[p as int] is U64,
    ensures final(st)@ == old(st)@, r@ == old(st)@[p as int]->U64_0,
{
    let n = st.part_len(p);
    let r = st.extent_u64(p, 0, n);
    proof { assert(r@ =~= old(st)@[p as int]->U64_0); }
    r
}

pub fn whole_i64(st: &mut StoredParts, p: usize) -> (r: &'static [i64])
    requires p < old(st)@.len(), old(st)@[p as int] is I64,
    ensures final(st)@ == old(st)@, r@ == old(st)@[p as int]->I64_0,
{
    let n = st.part_len(p);
    let r = st.extent_i64(p, 0, n);
    proof { assert(r@ =~= old(st)@[p as int]->I64_0); }
    r
}

/// The first value of a U64 part (a kind or flag).
pub fn first_u64(st: &mut StoredParts, p: usize) -> (r: u64)
    requires p < old(st)@.len(), old(st)@[p as int] is U64, old(st)@[p as int]->U64_0.len() >= 1,
    ensures final(st)@ == old(st)@, r == old(st)@[p as int]->U64_0[0],
{
    let s = st.extent_u64(p, 0, 1);
    s[0]
}

/// The scan's block size for a table of `n` rows whose layout part is `lay` (`decode::bs_ok`).
pub fn block_rows(st: &mut StoredParts, lay: usize, n: usize) -> (e: usize)
    requires
        lay < old(st)@.len(), old(st)@[lay as int] is U64, old(st)@[lay as int]->U64_0.len() == 2,
        old(st)@[lay as int]->U64_0[1] >= 1,
    ensures final(st)@ == old(st)@, bs_ok(e as int, old(st)@[lay as int]->U64_0[1] as int, n as int),
{
    let l = st.extent_u64(lay, 0, 2);
    let b = l[1];
    if b <= n as u64 { b as usize } else if n >= 1 { n } else { 1 }
}

// ------------------------------------------------------------------------------------------------ the column model

/// The parts of every table the scan reads, of a bound database.
pub proof fn lemma_tables(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        fi::lineitem_ok(li_tp(sv), fd::stored_relations(db)[0]),
        fi::orders_ok(or_tp(sv), fd::stored_relations(db)[1]),
        ci::customer_ok(cu_tp(sv), cd::stored_relations(db)[0]),
        ci::part_ok(pa_tp(sv), cd::stored_relations(db)[1]),
        si::supplier_ok(su_tp(sv), sd::stored_relations(db)[1]),
        si::nation_ok(na_tp(sv), sd::stored_relations(db)[2]),
        si::region_ok(re_tp(sv), sd::stored_relations(db)[3]),
        sv.factsdir.len() == crate::stores::factsdir::interface::dirs::FACTSDIR_PARTS, sv.custpart.len() == ci::CUSTPART_PARTS, sv.suppliers.len() == si::SUPPLIERS_PARTS,
        sv.factsdir[fi::FACTS_CLUSTER as int] is U64, fc::u64s(sv.factsdir[fi::FACTS_CLUSTER as int]).len() == 1,
{
    lemma_fparts(sv, db);
}

/// The lineitem and orders slices.
fn load_facts(st: &mut StoredParts, Ghost(sv): Ghost<StoresView>, Ghost(db): Ghost<Database>) -> (r: (usize, usize,
    &'static [u32], &'static [i64], &'static [u32], &'static [i64], &'static [u32], &'static [i64],
    &'static [u32], &'static [i64], &'static [u8], &'static [i64],
    usize, usize, &'static [u32], &'static [i64], &'static [u32], &'static [i64], &'static [u16], &'static [i64],
    &'static [u32], &'static [u64], u64))
    requires old(st)@ == sv.factsdir, bound_db(sv, db),
    ensures
        final(st)@ == old(st)@,
        ({
            let l = li_tp(sv);
            let o = or_tp(sv);
            &&& r.0 == fc::u64s(l[fi::LI_LAYOUT as int])[0] && bs_ok(r.1 as int, fc::u64s(l[fi::LI_LAYOUT as int])[1] as int, r.0 as int)
            &&& r.2@ == fc::u32s(l[fi::LI_ORDERKEY_CODES as int]) && r.3@ == fc::i64s(l[fi::LI_ORDERKEY_BASE as int])
            &&& r.4@ == fc::u32s(l[fi::LI_PARTKEY_CODES as int]) && r.5@ == fc::i64s(l[fi::LI_PARTKEY_BASE as int])
            &&& r.6@ == fc::u32s(l[fi::LI_SUPPKEY_CODES as int]) && r.7@ == fc::i64s(l[fi::LI_SUPPKEY_BASE as int])
            &&& r.8@ == fc::u32s(l[fi::LI_EXTENDEDPRICE_CODES as int]) && r.9@ == fc::i64s(l[fi::LI_EXTENDEDPRICE_BASE as int])
            &&& r.10@ == fc::u8s(l[fi::LI_DISCOUNT_CODES as int]) && r.11@ == fc::i64s(l[fi::LI_DISCOUNT_BASE as int])
            &&& r.12 == fc::u64s(o[fi::OR_LAYOUT as int])[0] && bs_ok(r.13 as int, fc::u64s(o[fi::OR_LAYOUT as int])[1] as int, r.12 as int)
            &&& r.14@ == fc::u32s(o[fi::OR_ORDERKEY_CODES as int]) && r.15@ == fc::i64s(o[fi::OR_ORDERKEY_BASE as int])
            &&& r.16@ == fc::u32s(o[fi::OR_CUSTKEY_CODES as int]) && r.17@ == fc::i64s(o[fi::OR_CUSTKEY_BASE as int])
            &&& r.18@ == o[fi::OR_ORDERDATE_CODES as int]->U16_0 && r.19@ == fc::i64s(o[fi::OR_ORDERDATE_BASE as int])
            &&& r.20@ == fc::u32s(o[fi::OR_KEYIDX_CODES as int]) && r.21@ == fc::u64s(o[fi::OR_KEYIDX_BASE as int])
            &&& r.22 == fc::u64s(o[fi::OR_KEYIDX_KIND as int])[0]
        }),
{
    proof {
        lemma_tables(sv, db);
        let rels = fd::stored_relations(db);
        let lrows = fi::lineitem_rows(li_tp(sv), rels[0]);
        let orows = fi::orders_rows(or_tp(sv), rels[1]);
        assert(fi::lineitem_cols_ok(li_tp(sv), lrows));
        assert(fi::orders_cols_ok(or_tp(sv), orows));
    }
    let lf = fi::LINEITEM_FIRST;
    let of = fi::ORDERS_FIRST;
    let n_l = st.part_len(lf + fi::LI_ORDERKEY_CODES);
    let bs_l = block_rows(st, lf + fi::LI_LAYOUT, n_l);
    let lk_c = whole_u32(st, lf + fi::LI_ORDERKEY_CODES);
    let lk_b = whole_i64(st, lf + fi::LI_ORDERKEY_BASE);
    let lp_c = whole_u32(st, lf + fi::LI_PARTKEY_CODES);
    let lp_b = whole_i64(st, lf + fi::LI_PARTKEY_BASE);
    let ls_c = whole_u32(st, lf + fi::LI_SUPPKEY_CODES);
    let ls_b = whole_i64(st, lf + fi::LI_SUPPKEY_BASE);
    let le_c = whole_u32(st, lf + fi::LI_EXTENDEDPRICE_CODES);
    let le_b = whole_i64(st, lf + fi::LI_EXTENDEDPRICE_BASE);
    let ld_c = whole_u8(st, lf + fi::LI_DISCOUNT_CODES);
    let ld_b = whole_i64(st, lf + fi::LI_DISCOUNT_BASE);
    let n_o = st.part_len(of + fi::OR_ORDERKEY_CODES);
    let bs_o = block_rows(st, of + fi::OR_LAYOUT, n_o);
    let ok_c = whole_u32(st, of + fi::OR_ORDERKEY_CODES);
    let ok_b = whole_i64(st, of + fi::OR_ORDERKEY_BASE);
    let oc_c = whole_u32(st, of + fi::OR_CUSTKEY_CODES);
    let oc_b = whole_i64(st, of + fi::OR_CUSTKEY_BASE);
    let od_c = whole_u16(st, of + fi::OR_ORDERDATE_CODES);
    let od_b = whole_i64(st, of + fi::OR_ORDERDATE_BASE);
    let oi_c = whole_u32(st, of + fi::OR_KEYIDX_CODES);
    let oi_b = whole_u64(st, of + fi::OR_KEYIDX_BASE);
    let oi_kind = first_u64(st, of + fi::OR_KEYIDX_KIND);
    (n_l, bs_l, lk_c, lk_b, lp_c, lp_b, ls_c, ls_b, le_c, le_b, ld_c, ld_b, n_o, bs_o, ok_c, ok_b, oc_c, oc_b, od_c, od_b,
        oi_c, oi_b, oi_kind)
}

/// A key-lookup hint: the key of the first row (lookups probe `key - first` first), or 0.
fn first_key(kc: &'static [u32], kb: &'static [i64]) -> i64 {
    if kc.len() > 0 && kb.len() > 0 {
        let v: i128 = kb[0] as i128 + kc[0] as i128;
        if i64::MIN as i128 <= v && v <= i64::MAX as i128 { v as i64 } else { 0 }
    } else {
        0
    }
}

/// The column model's slices, read whole on the calling thread.
pub fn load_cols(stores: &mut Stores, Ghost(db): Ghost<Database>) -> (c: Cols)
    requires bound_db(old(stores)@, db),
    ensures final(stores)@ == old(stores)@, cols_from(old(stores)@, c), cols_ok(c),
{
    let ghost sv = stores@;
    proof { lemma_tables(sv, db); }
    let (n_l, bs_l, lk_c, lk_b, lp_c, lp_b, ls_c, ls_b, le_c, le_b, ld_c, ld_b, n_o, bs_o, ok_c, ok_b, oc_c, oc_b, od_c, od_b,
        oi_c, oi_b, oi_kind) = load_facts(&mut stores.factsdir, Ghost(sv), Ghost(db));
    proof {
        let rels = cd::stored_relations(db);
        assert(ci::customer_ok(cu_tp(sv), rels[0]));
        let srels = sd::stored_relations(db);
        assert(si::supplier_ok(su_tp(sv), srels[1]));
    }
    let cf = ci::CUSTOMER_FIRST;
    let cp = &mut stores.custpart;
    let n_c = cp.part_len(cf + ci::CU_CUSTKEY_CODES);
    let bs_c = block_rows(cp, cf + ci::CU_LAYOUT, n_c);
    let ck_c = whole_u32(cp, cf + ci::CU_CUSTKEY_CODES);
    let ck_b = whole_i64(cp, cf + ci::CU_CUSTKEY_BASE);
    let cn_c = whole_u8(cp, cf + ci::CU_NATIONKEY_CODES);
    let cn_b = whole_i64(cp, cf + ci::CU_NATIONKEY_BASE);
    let c_kind = first_u64(cp, cf + ci::CU_KEYIDX_KIND);
    let sf = si::SUPPLIER_FIRST;
    let sp = &mut stores.suppliers;
    let n_s = sp.part_len(sf + si::SU_SUPPKEY_CODES);
    let bs_s = block_rows(sp, sf + si::SU_LAYOUT, n_s);
    let sk_c = whole_u32(sp, sf + si::SU_SUPPKEY_CODES);
    let sk_b = whole_i64(sp, sf + si::SU_SUPPKEY_BASE);
    let sn_c = whole_u8(sp, sf + si::SU_NATIONKEY_CODES);
    let sn_b = whole_i64(sp, sf + si::SU_NATIONKEY_BASE);
    let s_kind = first_u64(sp, sf + si::SU_KEYIDX_KIND);
    let e32: &'static [u32] = sk_c.split_at(0).0;
    let e64: &'static [u64] = oi_b.split_at(0).0;
    proof {
        assert(e32@ =~= Seq::<u32>::empty());
        assert(e64@ =~= Seq::<u64>::empty());
    }
    let c = Cols {
        n_l, bs_l, lk_c, lk_b, lp_c, lp_b, ls_c, ls_b, le_c, le_b, ld_c, ld_b,
        n_o, bs_o, ok_c, ok_b, oc_c, oc_b, od_c, od_b, oi_c, oi_b, oi_kind,
        n_c, bs_c, ck_c, ck_b, cn_c, cn_b, c_kind, c_first: first_key(ck_c, ck_b),
        n_s, bs_s, sk_c, sk_b, sn_c, sn_b, s_kind, s_first: first_key(sk_c, sk_b),
        lo: -1826, hi: -1096, d96: -1461, e32, e64,
    };
    proof {
        assert(cols_from(sv, c));
        lemma_cols(sv, db, c);
    }
    c
}

} // verus!
