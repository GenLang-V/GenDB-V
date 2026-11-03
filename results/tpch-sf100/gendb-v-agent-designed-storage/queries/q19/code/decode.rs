//! Decoding one stored row: under uniform groups of `bs` rows, the value of row `s` of a frame-of-reference column
//! is `base[s / bs] + code[s]` (`lemma_li_decode`, `lemma_pa_decode`), and the key index's key at a position is the
//! l_partkey of the stored row there (`lemma_ikey`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::part_len;
use crate::stores::facts::interface::*;
use crate::stores::facts::interface::common::colfmt::*;
use crate::stores::facts::interface::common::keyidx::{keyidx_ok, irow, fkey, lemma_irow_bound, lemma_fkey_for_at};
use crate::stores::facts::interface::common::read::{lemma_for_row, lemma_div_lt};
use crate::stores::custpart::interface as cpi;
use crate::stores::custpart::interface::common::colfmt as cpc;
use crate::stores::custpart::interface::common::read as cpr;
use super::model::*;

verus! {

/// Number of lineitem groups.
pub open spec fn li_ng(fp: Seq<PartView>) -> int {
    li_gs(fp).len() - 1
}

/// The values of stored lineitem row `s` from its group `s / bs` and its codes.
pub proof fn lemma_li_decode(fp: Seq<PartView>, s: int)
    requires li_shape(fp), 0 <= s < n_li(fp),
    ensures ({
        let g = s / li_bs(fp);
        &&& 0 <= g < li_ng(fp)
        &&& li_ng(fp) == nblocks_of(n_li(fp), li_bs(fp))
        &&& lpk_at(fp, s) == pk_b(fp)[g] + pk_c(fp)[s]
        &&& qty_at(fp, s) == i64s(fp[LI_QUANTITY_BASE as int])[g] + u16s_of(fp[LI_QUANTITY_CODES as int])[s]
        &&& price_at(fp, s) == i64s(fp[LI_EXTENDEDPRICE_BASE as int])[g] + u32s(fp[LI_EXTENDEDPRICE_CODES as int])[s]
        &&& disc_at(fp, s) == i64s(fp[LI_DISCOUNT_BASE as int])[g] + u8s(fp[LI_DISCOUNT_CODES as int])[s]
        &&& sidx_at(fp, s) == u64s(fp[LI_SHIPINSTRUCT_BASE as int])[g] + u8s(fp[LI_SHIPINSTRUCT_CODES as int])[s]
        &&& midx_at(fp, s) == u64s(fp[LI_SHIPMODE_BASE as int])[g] + u8s(fp[LI_SHIPMODE_CODES as int])[s]
        &&& s < u16s_of(fp[LI_QUANTITY_CODES as int]).len()
        &&& s < pk_c(fp).len()
        &&& s < u32s(fp[LI_EXTENDEDPRICE_CODES as int]).len()
        &&& s < u8s(fp[LI_DISCOUNT_CODES as int]).len()
        &&& s < u8s(fp[LI_SHIPINSTRUCT_CODES as int]).len()
        &&& s < u8s(fp[LI_SHIPMODE_CODES as int]).len()
    }),
{
    let n = n_li(fp);
    let bs = li_bs(fp);
    let gp = fp[LI_GROUPS as int];
    lemma_uniform_groups(gp, n, bs);
    lemma_nblocks(n, bs);
    lemma_div_lt(s, bs, nblocks_of(n, bs));
    lemma_for_row(gp, n, bs, fp[LI_PARTKEY_BASE as int], fp[LI_PARTKEY_CODES as int], s);
    lemma_for_row(gp, n, bs, fp[LI_QUANTITY_BASE as int], fp[LI_QUANTITY_CODES as int], s);
    lemma_for_row(gp, n, bs, fp[LI_EXTENDEDPRICE_BASE as int], fp[LI_EXTENDEDPRICE_CODES as int], s);
    lemma_for_row(gp, n, bs, fp[LI_DISCOUNT_BASE as int], fp[LI_DISCOUNT_CODES as int], s);
    lemma_for_row(gp, n, bs, fp[LI_SHIPINSTRUCT_BASE as int], fp[LI_SHIPINSTRUCT_CODES as int], s);
    lemma_for_row(gp, n, bs, fp[LI_SHIPMODE_BASE as int], fp[LI_SHIPMODE_CODES as int], s);
}

/// The key index: positions map to stored rows, and the key at a position is that row's l_partkey.
pub proof fn lemma_ikey(fp: Seq<PartView>, p: int)
    requires li_shape(fp), 0 <= p < n_li(fp),
    ensures
        0 <= irow_at(fp, p) < n_li(fp),
        ikey_at(fp, p) == lpk_at(fp, irow_at(fp, p)),
        kx_kind(fp) == 2 ==> 0 <= p / li_bs(fp) < kx_b(fp).len() && p < kx_c(fp).len()
            && irow_at(fp, p) == kx_b(fp)[p / li_bs(fp)] + kx_c(fp)[p],
        kx_kind(fp) != 2 ==> irow_at(fp, p) == p,
{
    let n = n_li(fp);
    let bs = li_bs(fp);
    lemma_irow_bound(pk_c(fp), pk_b(fp), kx_c(fp), kx_b(fp), bs, kx_kind(fp), n, p);
    lemma_fkey_for_at(fp[LI_GROUPS as int], n, bs, fp[LI_PARTKEY_BASE as int], fp[LI_PARTKEY_CODES as int], irow_at(fp, p));
    if kx_kind(fp) == 2 {
        assert(kx_b(fp).len() * bs >= n);
        lemma_div_lt(p, bs, kx_b(fp).len() as int);
    }
}

/// Number of part groups.
pub open spec fn pa_ng(cp: Seq<PartView>) -> int {
    pa_gs(cp).len() - 1
}

/// The values of stored part row `j` from its group `j / bs` and its codes.
pub proof fn lemma_pa_decode(cp: Seq<PartView>, j: int)
    requires pa_shape(cp), 0 <= j < n_pa(cp),
    ensures ({
        let g = j / pa_bs(cp);
        &&& 0 <= g < pa_ng(cp)
        &&& pkey_at(cp, j) == cpc::i64s(cp[pp(cpi::PA_PARTKEY_BASE)])[g] + cpc::u32s(cp[pp(cpi::PA_PARTKEY_CODES)])[j]
        &&& bidx_at(cp, j) == cpc::u64s(cp[pp(cpi::PA_BRAND_BASE)])[g] + cpc::u8s(cp[pp(cpi::PA_BRAND_CODES)])[j]
        &&& size_at(cp, j) == cpc::i64s(cp[pp(cpi::PA_SIZE_BASE)])[g] + cpc::u8s(cp[pp(cpi::PA_SIZE_CODES)])[j]
        &&& cidx_at(cp, j) == cpc::u64s(cp[pp(cpi::PA_CONTAINER_BASE)])[g] + cpc::u8s(cp[pp(cpi::PA_CONTAINER_CODES)])[j]
        &&& j < cpc::u32s(cp[pp(cpi::PA_PARTKEY_CODES)]).len()
    }),
{
    let n = n_pa(cp);
    let bs = pa_bs(cp);
    let gp = cp[pp(cpi::PA_GROUPS)];
    cpc::lemma_uniform_groups(gp, n, bs);
    cpc::lemma_nblocks(n, bs);
    cpr::lemma_div_lt(j, bs, cpc::nblocks_of(n, bs));
    cpr::lemma_for_row(gp, n, bs, cp[pp(cpi::PA_PARTKEY_BASE)], cp[pp(cpi::PA_PARTKEY_CODES)], j);
    cpr::lemma_for_row(gp, n, bs, cp[pp(cpi::PA_BRAND_BASE)], cp[pp(cpi::PA_BRAND_CODES)], j);
    cpr::lemma_for_row(gp, n, bs, cp[pp(cpi::PA_SIZE_BASE)], cp[pp(cpi::PA_SIZE_CODES)], j);
    cpr::lemma_for_row(gp, n, bs, cp[pp(cpi::PA_CONTAINER_BASE)], cp[pp(cpi::PA_CONTAINER_CODES)], j);
}

/// Row `j` lies in block `g` (`g * bs <= j < (g + 1) * bs`): its block is `j / bs`.
pub proof fn lemma_block(j: int, g: int, bs: int)
    requires bs >= 1, g >= 0, g * bs <= j < (g + 1) * bs,
    ensures j / bs == g,
{
    assert((g + 1) * bs == g * bs + bs) by (nonlinear_arith);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(j, bs, g, j - g * bs);
}

} // verus!
