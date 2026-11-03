//! Reading the parts on the calling thread: every column the query reads as a whole-part extent (`whole_*`), the
//! bound parameter (`$1` as the coefficient `100 * $1` at scale 2), and the `Cols` handle of the kernels with its
//! `cols_ok` proof.
use vstd::prelude::*;
use crate::gendb_entry::stored::StoredParts;
use crate::gendb_entry::stores::Stores;
use crate::gendb_params::Params;
use crate::query::param_domain;
use super::model::*;
use super::facts::kinds_ok;
use super::qspec::*;
use super::kernel::*;

verus! {

fn whole_u8(sp: &mut StoredParts, i: usize) -> (r: &'static [u8])
    requires i < old(sp)@.len(), old(sp)@[i as int] is U8,
    ensures final(sp)@ == old(sp)@, r@ == pv_u8(old(sp)@[i as int]),
{
    let n = sp.part_len(i);
    let r = sp.extent_u8(i, 0, n);
    proof { assert(r@ =~= pv_u8(old(sp)@[i as int])); }
    r
}

fn whole_u16(sp: &mut StoredParts, i: usize) -> (r: &'static [u16])
    requires i < old(sp)@.len(), old(sp)@[i as int] is U16,
    ensures final(sp)@ == old(sp)@, r@ == pv_u16(old(sp)@[i as int]),
{
    let n = sp.part_len(i);
    let r = sp.extent_u16(i, 0, n);
    proof { assert(r@ =~= pv_u16(old(sp)@[i as int])); }
    r
}

fn whole_u32(sp: &mut StoredParts, i: usize) -> (r: &'static [u32])
    requires i < old(sp)@.len(), old(sp)@[i as int] is U32,
    ensures final(sp)@ == old(sp)@, r@ == pv_u32(old(sp)@[i as int]),
{
    let n = sp.part_len(i);
    let r = sp.extent_u32(i, 0, n);
    proof { assert(r@ =~= pv_u32(old(sp)@[i as int])); }
    r
}

fn whole_u64(sp: &mut StoredParts, i: usize) -> (r: &'static [u64])
    requires i < old(sp)@.len(), old(sp)@[i as int] is U64,
    ensures final(sp)@ == old(sp)@, r@ == pv_u64(old(sp)@[i as int]),
{
    let n = sp.part_len(i);
    let r = sp.extent_u64(i, 0, n);
    proof { assert(r@ =~= pv_u64(old(sp)@[i as int])); }
    r
}

fn whole_i64(sp: &mut StoredParts, i: usize) -> (r: &'static [i64])
    requires i < old(sp)@.len(), old(sp)@[i as int] is I64,
    ensures final(sp)@ == old(sp)@, r@ == pv_i64(old(sp)@[i as int]),
{
    let n = sp.part_len(i);
    let r = sp.extent_i64(i, 0, n);
    proof { assert(r@ =~= pv_i64(old(sp)@[i as int])); }
    r
}

/// The column handle of the query.
pub fn load(stores: &mut Stores, params: &Params, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (c: Cols)
    requires
        kinds_ok(old(stores)@),
        model_ok(m),
        m == model_of(old(stores)@),
        p == qp_of(params@),
        param_domain(params@),
    ensures
        final(stores)@ == old(stores)@,
        cols_ok(c, m, p),
        rcols_ok(c, m),
        lcols_ok(c, m),
{
    // `$1` (an int4) as a coefficient at scale 2
    let thr: i128 = 100 * (params.p0 as i128);
    // customer
    let c_layout = whole_u64(&mut stores.custpart, C_LAYOUT);
    let c_key_c = whole_u32(&mut stores.custpart, C_KEY_C);
    let c_key_b = whole_i64(&mut stores.custpart, C_KEY_B);
    let c_name_o = whole_u64(&mut stores.custpart, C_NAME_O);
    let c_name_y = whole_u8(&mut stores.custpart, C_NAME_Y);
    let c_kind = whole_u64(&mut stores.custpart, C_IDX_KIND)[0];
    let e32 = stores.custpart.extent_u32(C_KEY_C, 0, 0);
    let e64 = stores.custpart.extent_u64(C_IDX_KIND, 0, 0);
    let c_bs = c_layout[1];
    let cidx_ok = c_bs <= usize::MAX as u64;
    let c_bsz: usize = if cidx_ok { c_bs as usize } else { 1 };
    // lineitem
    let l_layout = whole_u64(&mut stores.liruns, F_L_LAYOUT);
    let l_key_c = whole_u32(&mut stores.liruns, F_L_KEY_C);
    let l_key_b = whole_i64(&mut stores.liruns, F_L_KEY_B);
    let l_qty_c = whole_u16(&mut stores.liruns, F_L_QTY_C);
    let l_qty_b = whole_i64(&mut stores.liruns, F_L_QTY_B);
    // orders
    let o_layout = whole_u64(&mut stores.liruns, F_O_LAYOUT);
    let o_key_c = whole_u32(&mut stores.liruns, F_O_KEY_C);
    let o_key_b = whole_i64(&mut stores.liruns, F_O_KEY_B);
    let o_cust_c = whole_u32(&mut stores.liruns, F_O_CUST_C);
    let o_cust_b = whole_i64(&mut stores.liruns, F_O_CUST_B);
    let o_tp_c = whole_u32(&mut stores.liruns, F_O_TP_C);
    let o_tp_b = whole_i64(&mut stores.liruns, F_O_TP_B);
    let o_date_c = whole_u16(&mut stores.liruns, F_O_DATE_C);
    let o_date_b = whole_i64(&mut stores.liruns, F_O_DATE_B);
    let o_ic = whole_u32(&mut stores.liruns, F_O_IDX_C);
    let o_ib = whole_u64(&mut stores.liruns, F_O_IDX_B);
    let o_kind = whole_u64(&mut stores.liruns, F_O_IDX_KIND)[0];
    let cluster = whole_u64(&mut stores.liruns, F_CLUSTER)[0];
    // runs and the l_quantity zone map
    let r_meta = whole_u64(&mut stores.liruns, F_R_META);
    let r_lens = whole_u8(&mut stores.liruns, F_R_LENS);
    let r_starts = whole_u64(&mut stores.liruns, F_R_STARTS);
    let qz = whole_i64(&mut stores.liruns, F_QZ);
    let lg_meta = whole_u64(&mut stores.liruns, F_LG_META);
    let lg_runs = whole_u32(&mut stores.liruns, F_LG_RUNS);
    let lg_starts = whole_u32(&mut stores.liruns, F_LG_STARTS);
    let o_bs = o_layout[1];
    let idx_ok = o_bs <= usize::MAX as u64;
    let o_bsz: usize = if idx_ok { o_bs as usize } else { 1 };
    let c = Cols {
        l_key_c, l_key_b, l_qty_c, l_qty_b,
        l_bs: l_layout[1], l_n: l_key_c.len(), l_nb: l_key_b.len(),
        o_key_c, o_key_b, o_cust_c, o_cust_b, o_tp_c, o_tp_b, o_date_c, o_date_b, o_ic, o_ib, o_kind,
        o_bs, o_bsz, idx_ok, o_n: o_key_c.len(), o_nb: o_key_b.len(),
        c_key_c, c_key_b, c_name_o, c_name_y, c_bs, c_bsz, cidx_ok, c_n: c_key_c.len(), c_nb: c_key_b.len(), c_kind,
        e32, e64, thr, cluster,
        r_lens, r_starts, qz, r_mode: r_meta[0], r_stride: r_meta[1], r_n: r_lens.len(), r_sn: r_starts.len(),
        qz_n: qz.len(),
        lg_mode: lg_meta[0], lg_max: lg_meta[1], lg_n: lg_meta[2], lg_runs, lg_starts,
        lg_rn: lg_runs.len(),
    };
    proof {
        assert(e32@ =~= Seq::<u32>::empty());
        assert(e64@ =~= Seq::<u64>::empty());
    }
    c
}

} // verus!
