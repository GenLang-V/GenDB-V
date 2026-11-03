//! Reading the parts on the calling thread: every column the query reads as a whole-part extent (`whole_*`), the
//! bound parameters (`$2` as days, `$1` as the market segment dictionary entry), the density of customer keys
//! (`dense_keys`: sorted distinct keys from 1 to n, so customer row `c` has key `c + 1` and a key is looked up by
//! position), the segment as one U8 code when the code groups share a base (`seg_code`), and the `Cols` handle of
//! the kernels with its `cols_ok` proof.
use vstd::prelude::*;
use crate::gendb_entry::stored::StoredParts;
use crate::gendb_entry::stores::Stores;
use crate::gendb_params::Params;
use crate::exec::datetime::date_from_civil_exec;
use crate::query::param_domain;
use crate::stores::custpart::interface::common::colfmt as cf;
use crate::stores::custpart::interface::common::read::dict_find;
use crate::stores::custpart::interface::common::keyidx as ck;
use super::model::*;
use super::facts::kinds_ok;
use super::qspec::*;
use super::sqlrow::lemma_params;
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

/// Sorted (key index kind 1) distinct customer keys grow by at least one per row.
proof fn lemma_keys_gap(m: M, a: int, b: int)
    requires model_ok(m), m.c_kind == 1, 0 <= a <= b < m.c_n,
    ensures ckey(m, b) - ckey(m, a) >= b - a,
    decreases b - a,
{
    if a < b {
        lemma_keys_gap(m, a, b - 1);
        assert(ck::sorted_at(m.c_key_c, m.c_key_b, Seq::<u32>::empty(), Seq::<u64>::empty(), m.c_bs, m.c_kind, b - 1));
        assert(ckey(m, b - 1) != ckey(m, b));
    }
}

/// Sorted distinct keys from 1 to `n` are the row positions plus one.
proof fn lemma_dense(m: M)
    requires model_ok(m), m.c_kind == 1, m.c_n > 0, ckey(m, 0) == 1, ckey(m, m.c_n - 1) == m.c_n,
    ensures forall|i: int| 0 <= i < m.c_n ==> #[trigger] ckey(m, i) == i + 1,
{
    assert forall|i: int| 0 <= i < m.c_n implies #[trigger] ckey(m, i) == i + 1 by {
        lemma_keys_gap(m, 0, i);
        lemma_keys_gap(m, i, m.c_n - 1);
    }
}

/// Customer row `c` has key `c + 1` for every row: decided from the sort flag and the first and last keys.
pub fn dense_keys(key_c: &[u32], key_b: &[i64], kind: u64, bs: u64, n: usize, Ghost(m): Ghost<M>) -> (r: bool)
    requires
        model_ok(m),
        key_c@ == m.c_key_c,
        key_b@ == m.c_key_b,
        kind == m.c_kind,
        bs as int == m.c_bs,
        n == m.c_n,
    ensures r ==> forall|i: int| 0 <= i < m.c_n ==> #[trigger] ckey(m, i) == i + 1,
{
    if kind != 1 || n == 0 {
        return false;
    }
    proof {
        lemma_div_in(0, m.c_bs, 0);
        lemma_block_bound(0, m.c_bs, m.c_n, m.c_nb);
        lemma_block_bound(m.c_n - 1, m.c_bs, m.c_n, m.c_nb);
    }
    let k0 = key_b[0] as i128 + key_c[0] as i128;
    let kl = key_b[(((n - 1) as u64) / bs) as usize] as i128 + key_c[n - 1] as i128;
    if k0 == 1 && kl == n as i128 {
        proof { lemma_dense(m); }
        true
    } else {
        false
    }
}

/// The segment entry `seg` as a U8 code when every customer group has the same base (`Some(code)`): then a row has
/// the segment exactly when its code is `code`.
pub fn seg_code(seg_c: &[u8], seg_b: &[u64], n: usize, nb: usize, seg: u64, Ghost(m): Ghost<M>) -> (r: Option<u8>)
    requires
        model_ok(m),
        seg_c@ == m.c_seg_c,
        seg_b@ == m.c_seg_b,
        n == m.c_n,
        nb == m.c_nb,
    ensures
        r matches Some(code) ==> forall|i: int| 0 <= i < m.c_n ==> (#[trigger] m.c_seg_c[i] == code) == (cseg(m, i) == seg as int),
{
    if nb == 0 {
        return None;
    }
    let b0 = seg_b[0];
    let mut uni = true;
    let mut g: usize = 0;
    while g < nb
        invariant
            model_ok(m),
            seg_b@ == m.c_seg_b, nb == m.c_nb, nb > 0, b0 == m.c_seg_b[0],
            g <= nb,
            uni ==> forall|k: int| 0 <= k < g ==> #[trigger] m.c_seg_b[k] == b0,
        decreases nb - g,
    {
        if seg_b[g] != b0 {
            uni = false;
        }
        g = g + 1;
    }
    if uni && seg >= b0 && seg - b0 < 256 {
        let code = (seg - b0) as u8;
        proof {
            assert forall|i: int| 0 <= i < m.c_n implies (#[trigger] m.c_seg_c[i] == code) == (cseg(m, i) == seg as int) by {
                lemma_block_bound(i, m.c_bs, m.c_n, m.c_nb);
                assert(m.c_seg_b[i / m.c_bs] == b0);
            }
        }
        Some(code)
    } else {
        None
    }
}

/// The column handle of the query, or `None` when no dictionary entry is `$1` (then no customer has the segment).
pub fn load(stores: &mut Stores, params: &Params, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: Option<Cols>)
    requires
        kinds_ok(old(stores)@),
        model_ok(m),
        m == model_of(old(stores)@),
        p == qp_of(params@),
        param_domain(params@),
    ensures
        final(stores)@ == old(stores)@,
        r matches Some(c) ==> cols_ok(c, m, p),
        r is None ==> forall|i: int| 0 <= i < m.c_n ==> #[trigger] segtext(m, i) != p.seg,
{
    let ghost sv = stores@;
    proof { lemma_params(params@); }
    let day = date_from_civil_exec(params.p1.y as i64, params.p1.m as i64, params.p1.d as i64);
    // the market segment's dictionary entry
    let d_off = whole_u64(&mut stores.custpart, C_DICT_OFF);
    let d_bytes = whole_u8(&mut stores.custpart, C_DICT_BYTES);
    let dn = d_off.len();
    let seg = match dict_find(d_off, d_bytes, dn - 1, params.p0, params.p0.len()) {
        Some(s) => s as u64,
        None => {
            proof {
                assert forall|i: int| 0 <= i < m.c_n implies #[trigger] segtext(m, i) != p.seg by {
                    assert(in_i64(ckey(m, i)));
                }
            }
            return None;
        },
    };
    // customer
    let c_layout = whole_u64(&mut stores.custpart, C_LAYOUT);
    let c_key_c = whole_u32(&mut stores.custpart, C_KEY_C);
    let c_key_b = whole_i64(&mut stores.custpart, C_KEY_B);
    let c_seg_c = whole_u8(&mut stores.custpart, C_SEG_C);
    let c_seg_b = whole_u64(&mut stores.custpart, C_SEG_B);
    let c_kind = whole_u64(&mut stores.custpart, C_IDX_KIND)[0];
    let e32 = stores.custpart.extent_u32(C_KEY_C, 0, 0);
    let e64 = stores.custpart.extent_u64(C_SEG_B, 0, 0);
    let c_bs = c_layout[1];
    let c_n = c_key_c.len();
    let c_nb = c_key_b.len();
    let c_dense = dense_keys(c_key_c, c_key_b, c_kind, c_bs, c_n, Ghost(m));
    let (segc, seg_fast) = match seg_code(c_seg_c, c_seg_b, c_n, c_nb, seg, Ghost(m)) {
        Some(code) => (code, c_dense),
        None => (0u8, false),
    };
    // lineitem
    let l_layout = whole_u64(&mut stores.li_okruns, F_L_LAYOUT);
    let l_key_c = whole_u32(&mut stores.li_okruns, F_L_KEY_C);
    let l_key_b = whole_i64(&mut stores.li_okruns, F_L_KEY_B);
    let l_price_c = whole_u32(&mut stores.li_okruns, F_L_PRICE_C);
    let l_price_b = whole_i64(&mut stores.li_okruns, F_L_PRICE_B);
    let l_disc_c = whole_u8(&mut stores.li_okruns, F_L_DISC_C);
    let l_disc_b = whole_i64(&mut stores.li_okruns, F_L_DISC_B);
    let l_ship_c = whole_u16(&mut stores.li_okruns, F_L_SHIP_C);
    let l_ship_b = whole_i64(&mut stores.li_okruns, F_L_SHIP_B);
    let l_ship_z = whole_i64(&mut stores.li_okruns, F_L_SHIP_Z);
    let l_st = whole_u32(&mut stores.li_okruns, R_STARTS);
    // orders
    let o_layout = whole_u64(&mut stores.li_okruns, F_O_LAYOUT);
    let o_key_c = whole_u32(&mut stores.li_okruns, F_O_KEY_C);
    let o_key_b = whole_i64(&mut stores.li_okruns, F_O_KEY_B);
    let o_cust_c = whole_u32(&mut stores.li_okruns, F_O_CUST_C);
    let o_cust_b = whole_i64(&mut stores.li_okruns, F_O_CUST_B);
    let o_date_c = whole_u16(&mut stores.li_okruns, F_O_DATE_C);
    let o_date_b = whole_i64(&mut stores.li_okruns, F_O_DATE_B);
    let o_sp_c = whole_u8(&mut stores.li_okruns, F_O_SP_C);
    let o_sp_b = whole_i64(&mut stores.li_okruns, F_O_SP_B);
    let o_ic = whole_u32(&mut stores.li_okruns, F_O_IDX_C);
    let o_ib = whole_u64(&mut stores.li_okruns, F_O_IDX_B);
    let o_kind = whole_u64(&mut stores.li_okruns, F_O_IDX_KIND)[0];
    let cluster = whole_u64(&mut stores.li_okruns, F_CLUSTER)[0];
    let o_bs = o_layout[1];
    let idx_ok = o_bs <= usize::MAX as u64;
    let o_bsz: usize = if idx_ok { o_bs as usize } else { 1 };
    let c = Cols {
        l_key_c, l_key_b, l_price_c, l_price_b, l_disc_c, l_disc_b, l_ship_c, l_ship_b, l_ship_z, l_st, l_nst: l_st.len(),
        l_bs: l_layout[1], l_n: l_key_c.len(), l_nb: l_key_b.len(),
        o_key_c, o_key_b, o_cust_c, o_cust_b, o_date_c, o_date_b, o_sp_c, o_sp_b, o_ic, o_ib, o_kind,
        o_bs, o_bsz, idx_ok, o_n: o_key_c.len(), o_nb: o_key_b.len(),
        c_key_c, c_key_b, c_seg_c, c_seg_b, c_bs, c_n, c_kind, c_dense, segc, seg_fast, e32, e64,
        seg, day, cluster,
    };
    proof {
        assert(e32@ =~= Seq::<u32>::empty());
        assert(e64@ =~= Seq::<u64>::empty());
    }
    Some(c)
}

} // verus!
