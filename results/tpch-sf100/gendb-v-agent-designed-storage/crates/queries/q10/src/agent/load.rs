//! Reading the parts on the calling thread: every column the kernels read as a whole-part extent (`whole_*`), the
//! l_returnflag dictionary entry of `'R'` (`dict_find`), the density of customer keys in O(1) (`dense_ok`: the
//! keys are sorted by the key index flag and distinct by the primary key, so first key 1 and last key `c_n` make
//! row `c` hold key `c + 1`), and the `Cols` handle of the kernels with its `cols_ok` proof. `Txt` holds the
//! columns of the output rows (customer text and numbers, nation names).
use vstd::prelude::*;
use crate::gendb_entry::stored::StoredParts;
use crate::gendb_entry::stores::Stores;
use crate::stores::facts::interface::common::colfmt as ff;
use crate::stores::facts::interface::common::read::dict_find;
use crate::stores::custpart::interface::common::keyidx as ck;
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

/// Strictly increasing keys between two rows: the key grows by at least the row distance.
proof fn lemma_key_gap(m: M, a: int, b: int)
    requires
        model_ok(m),
        m.c_kind == 1,
        0 <= a <= b < m.c_n,
    ensures ckey(m, b) - ckey(m, a) >= b - a,
    decreases b - a,
{
    if a < b {
        lemma_key_gap(m, a, b - 1);
        let r = b - 1;
        assert(ck::sorted_at(m.c_key_c, m.c_key_b, Seq::<u32>::empty(), Seq::<u64>::empty(), m.c_bs, m.c_kind, r));
        assert(ck::fkey(m.c_key_c, m.c_key_b, m.c_bs, r) == ckey(m, r));
        assert(ck::fkey(m.c_key_c, m.c_key_b, m.c_bs, r + 1) == ckey(m, r + 1));
        assert(ckey(m, r) != ckey(m, r + 1));
    }
}

/// With sorted distinct keys, first key 1 and last key `c_n`, row `c` holds key `c + 1`.
proof fn lemma_dense(m: M)
    requires
        model_ok(m),
        m.c_kind == 1,
        m.c_n > 0,
        ckey(m, 0) == 1,
        ckey(m, m.c_n - 1) == m.c_n,
    ensures forall|i: int| 0 <= i < m.c_n ==> #[trigger] ckey(m, i) == i + 1,
{
    assert forall|i: int| 0 <= i < m.c_n implies #[trigger] ckey(m, i) == i + 1 by {
        lemma_key_gap(m, 0, i);
        lemma_key_gap(m, i, m.c_n - 1);
    }
}

/// The customer keys are `1 ..= c_n` in row order (checked in O(1) from the sort flag and the primary key).
fn dense_ok(key_c: &[u32], key_b: &[i64], bs: u64, n: usize, kind: u64, Ghost(m): Ghost<M>) -> (r: bool)
    requires
        model_ok(m),
        key_c@ == m.c_key_c,
        key_b@ == m.c_key_b,
        bs as int == m.c_bs,
        n == m.c_n,
        kind == m.c_kind,
    ensures r ==> forall|i: int| 0 <= i < m.c_n ==> #[trigger] ckey(m, i) == i + 1,
{
    if kind != 1 || n == 0 {
        return false;
    }
    proof {
        lemma_block_bound(0, m.c_bs, m.c_n, m.c_nb);
        lemma_block_bound(n - 1, m.c_bs, m.c_n, m.c_nb);
        assert(in_i64(ckey(m, 0)));
        assert(in_i64(ckey(m, n - 1)));
    }
    let first = key_b[(0u64 / bs) as usize] as i128 + key_c[0] as i128;
    let last = key_b[(((n - 1) as u64) / bs) as usize] as i128 + key_c[n - 1] as i128;
    if first == 1 && last == n as i128 {
        proof { lemma_dense(m); }
        true
    } else {
        false
    }
}

/// The `Cols` handle of the kernels for the date window `[lo, hi]`.
pub fn load(stores: &mut Stores, lo: i64, hi: i64, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: Cols)
    requires
        kinds_ok(old(stores)@),
        model_ok(m),
        m == model_of(old(stores)@),
        p.lo == lo && p.hi == hi,
    ensures
        final(stores)@ == old(stores)@,
        cols_ok(r, m, p),
{
    // the l_returnflag dictionary entry of 'R'
    let rf_off = whole_u64(&mut stores.facts, F_L_RF_OFF);
    let rf_bytes = whole_u8(&mut stores.facts, F_L_RF_BYTES);
    let dn = rf_off.len();
    let r_txt: Vec<u8> = vec![82u8];
    proof {
        assert(r_txt@ =~= r_text());
    }
    let found = dict_find(rf_off, rf_bytes, dn - 1, r_txt.as_slice(), 1);
    let rf: u64 = match found {
        Some(s) => s as u64,
        None => (dn - 1) as u64,
    };
    proof {
        assert forall|j: int| 0 <= j < m.l_n implies (#[trigger] lflag(m, j) == r_text()) == (lrf(m, j) == rf as int) by {
            assert(in_i64(lkey(m, j)));
            match found {
                Some(s) => {
                    if lrf(m, j) != s as int {
                        ff::lemma_dict_distinct(m.rf_off, m.rf_bytes, rf_n(m), lrf(m, j), s as int);
                    }
                },
                None => {},
            }
        }
    }
    // lineitem
    let l_layout = whole_u64(&mut stores.facts, F_L_LAYOUT);
    let l_key_c = whole_u32(&mut stores.facts, F_L_KEY_C);
    let l_key_b = whole_i64(&mut stores.facts, F_L_KEY_B);
    let l_price_c = whole_u32(&mut stores.facts, F_L_PRICE_C);
    let l_price_b = whole_i64(&mut stores.facts, F_L_PRICE_B);
    let l_disc_c = whole_u8(&mut stores.facts, F_L_DISC_C);
    let l_disc_b = whole_i64(&mut stores.facts, F_L_DISC_B);
    let l_rf_c = whole_u8(&mut stores.facts, F_L_RF_C);
    let l_rf_b = whole_u64(&mut stores.facts, F_L_RF_B);
    // orders
    let o_layout = whole_u64(&mut stores.facts, F_O_LAYOUT);
    let o_key_c = whole_u32(&mut stores.facts, F_O_KEY_C);
    let o_key_b = whole_i64(&mut stores.facts, F_O_KEY_B);
    let o_cust_c = whole_u32(&mut stores.facts, F_O_CUST_C);
    let o_cust_b = whole_i64(&mut stores.facts, F_O_CUST_B);
    let o_date_c = whole_u16(&mut stores.facts, F_O_DATE_C);
    let o_date_b = whole_i64(&mut stores.facts, F_O_DATE_B);
    let o_date_z = whole_i64(&mut stores.facts, F_O_DATE_Z);
    let o_ic = whole_u32(&mut stores.facts, F_O_IDX_C);
    let o_ib = whole_u64(&mut stores.facts, F_O_IDX_B);
    let o_kind = whole_u64(&mut stores.facts, F_O_IDX_KIND)[0];
    let cluster = whole_u64(&mut stores.facts, F_CLUSTER)[0];
    let o_bs = o_layout[1];
    let idx_ok = o_bs <= usize::MAX as u64;
    let o_bsz: usize = if idx_ok { o_bs as usize } else { 1 };
    // customer
    let c_layout = whole_u64(&mut stores.custpart, C_LAYOUT);
    let c_key_c = whole_u32(&mut stores.custpart, C_KEY_C);
    let c_key_b = whole_i64(&mut stores.custpart, C_KEY_B);
    let c_nat_c = whole_u8(&mut stores.custpart, C_NAT_C);
    let c_nat_b = whole_i64(&mut stores.custpart, C_NAT_B);
    let c_kind = whole_u64(&mut stores.custpart, C_IDX_KIND)[0];
    let e32 = stores.custpart.extent_u32(C_KEY_C, 0, 0);
    let e64 = stores.custpart.extent_u64(C_LAYOUT, 0, 0);
    let c_bs = c_layout[1];
    let c_bsz_ok = c_bs <= usize::MAX as u64;
    let c_bsz: usize = if c_bsz_ok { c_bs as usize } else { 1 };
    let c_n = c_key_c.len();
    let c_dense = dense_ok(c_key_c, c_key_b, c_bs, c_n, c_kind, Ghost(m));
    // nation
    let n_layout = whole_u64(&mut stores.suppliers, N_LAYOUT);
    let n_key_c = whole_u8(&mut stores.suppliers, N_KEY_C);
    let n_key_b = whole_i64(&mut stores.suppliers, N_KEY_B);
    let c = Cols {
        l_key_c, l_key_b, l_price_c, l_price_b, l_disc_c, l_disc_b, l_rf_c, l_rf_b,
        l_bs: l_layout[1], l_n: l_key_c.len(), l_nb: l_key_b.len(),
        o_key_c, o_key_b, o_cust_c, o_cust_b, o_date_c, o_date_b, o_date_z, o_ic, o_ib, o_kind,
        o_bs, o_bsz, idx_ok, o_n: o_key_c.len(), o_nb: o_key_b.len(),
        c_key_c, c_key_b, c_nat_c, c_nat_b, c_bs, c_bsz, c_bsz_ok, c_n, c_nb: c_key_b.len(), c_kind, c_dense, e32, e64,
        n_key_c, n_key_b, n_bs: n_layout[1], n_n: n_key_c.len(),
        rf, lo, hi, cluster,
    };
    proof {
        assert(e32@ =~= Seq::<u32>::empty());
        assert(e64@ =~= Seq::<u64>::empty());
    }
    c
}

/// The columns of the output rows: customer key, name, address, phone, account balance, comment, nation key, and
/// the nation keys and names.
pub struct Txt {
    pub c_key_c: &'static [u32],
    pub c_key_b: &'static [i64],
    pub c_name_o: &'static [u64],
    pub c_name_y: &'static [u8],
    pub c_addr_o: &'static [u64],
    pub c_addr_y: &'static [u8],
    pub c_phone_o: &'static [u64],
    pub c_phone_y: &'static [u8],
    pub c_bal_c: &'static [u32],
    pub c_bal_b: &'static [i64],
    pub c_cmt_o: &'static [u64],
    pub c_cmt_y: &'static [u8],
    pub c_bs: u64,
    pub n_name_o: &'static [u64],
    pub n_name_y: &'static [u8],
}

pub open spec fn txt_ok(t: Txt, m: M) -> bool {
    &&& t.c_key_c@ == m.c_key_c && t.c_key_b@ == m.c_key_b
    &&& t.c_name_o@ == m.c_name_o && t.c_name_y@ == m.c_name_y
    &&& t.c_addr_o@ == m.c_addr_o && t.c_addr_y@ == m.c_addr_y
    &&& t.c_phone_o@ == m.c_phone_o && t.c_phone_y@ == m.c_phone_y
    &&& t.c_bal_c@ == m.c_bal_c && t.c_bal_b@ == m.c_bal_b
    &&& t.c_cmt_o@ == m.c_cmt_o && t.c_cmt_y@ == m.c_cmt_y
    &&& t.c_bs as int == m.c_bs
    &&& t.n_name_o@ == m.n_name_o && t.n_name_y@ == m.n_name_y
}

/// The output columns.
pub fn load_txt(stores: &mut Stores, Ghost(m): Ghost<M>) -> (r: Txt)
    requires
        kinds_ok(old(stores)@),
        model_ok(m),
        m == model_of(old(stores)@),
    ensures
        final(stores)@ == old(stores)@,
        txt_ok(r, m),
{
    let c_layout = whole_u64(&mut stores.custpart, C_LAYOUT);
    Txt {
        c_key_c: whole_u32(&mut stores.custpart, C_KEY_C),
        c_key_b: whole_i64(&mut stores.custpart, C_KEY_B),
        c_name_o: whole_u64(&mut stores.custpart, C_NAME_O),
        c_name_y: whole_u8(&mut stores.custpart, C_NAME_Y),
        c_addr_o: whole_u64(&mut stores.custpart, C_ADDR_O),
        c_addr_y: whole_u8(&mut stores.custpart, C_ADDR_Y),
        c_phone_o: whole_u64(&mut stores.custpart, C_PHONE_O),
        c_phone_y: whole_u8(&mut stores.custpart, C_PHONE_Y),
        c_bal_c: whole_u32(&mut stores.custpart, C_BAL_C),
        c_bal_b: whole_i64(&mut stores.custpart, C_BAL_B),
        c_cmt_o: whole_u64(&mut stores.custpart, C_CMT_O),
        c_cmt_y: whole_u8(&mut stores.custpart, C_CMT_Y),
        c_bs: c_layout[1],
        n_name_o: whole_u64(&mut stores.suppliers, N_NAME_O),
        n_name_y: whole_u8(&mut stores.suppliers, N_NAME_Y),
    }
}

} // verus!
