//! The column slices of the model (`Cols`, `cols_ok`) and their reading on the calling thread: every part the
//! query reads is one whole-part extent request (`load`). Slice lengths are fields because slice `len` may unwind
//! in worker bodies.
use vstd::prelude::*;
use crate::gendb_entry::stored::StoredParts;
use crate::gendb_entry::stores::Stores;
use super::model::*;

verus! {

/// The column slices of the model, with the row counts and block sizes.
#[derive(Clone, Copy)]
pub struct Cols {
    pub l_ok_c: &'static [u32],
    pub l_ok_b: &'static [i64],
    pub l_pk_c: &'static [u32],
    pub l_pk_b: &'static [i64],
    pub l_sk_c: &'static [u32],
    pub l_sk_b: &'static [i64],
    pub l_qty_c: &'static [u16],
    pub l_qty_b: &'static [i64],
    pub l_price_c: &'static [u32],
    pub l_price_b: &'static [i64],
    pub l_disc_c: &'static [u8],
    pub l_disc_b: &'static [i64],
    pub l_ic: &'static [u32],
    pub l_ib: &'static [u64],
    pub l_kind: u64,
    pub dir: &'static [u32],
    pub kb: i64,
    pub l_bs: u64,
    pub l_n: usize,
    pub o_key_c: &'static [u32],
    pub o_key_b: &'static [i64],
    pub o_date_c: &'static [u16],
    pub o_date_b: &'static [i64],
    pub o_date_z: &'static [i64],
    pub o_ic: &'static [u32],
    pub o_ib: &'static [u64],
    pub o_kind: u64,
    pub cluster: u64,
    pub o_bs: u64,
    pub o_bsz: usize,
    pub o_bsz_ok: bool,
    pub o_n: usize,
    pub p_key_c: &'static [u32],
    pub p_key_b: &'static [i64],
    pub p_name_o: &'static [u64],
    pub p_name_y: &'static [u8],
    pub py_n: usize,
    pub p_kind: u64,
    pub p_sig: &'static [u64],
    pub p_bs: u64,
    pub p_n: usize,
    pub t_pk_c: &'static [u32],
    pub t_pk_b: &'static [i64],
    pub t_sk_c: &'static [u32],
    pub t_sk_b: &'static [i64],
    pub t_cost_c: &'static [u32],
    pub t_cost_b: &'static [i64],
    pub t_kind: u64,
    pub t_bs: u64,
    pub t_n: usize,
    pub s_key_c: &'static [u32],
    pub s_key_b: &'static [i64],
    pub s_nk_c: &'static [u8],
    pub s_nk_b: &'static [i64],
    pub s_kind: u64,
    pub s_bs: u64,
    pub s_n: usize,
    pub n_key_c: &'static [u8],
    pub n_key_b: &'static [i64],
    pub n_name_o: &'static [u64],
    pub n_name_y: &'static [u8],
    pub n_bs: u64,
    pub n_n: usize,
    pub e32: &'static [u32],
    pub e64: &'static [u64],
}

/// The slices are the model's parts.
pub open spec fn cols_ok(c: Cols, m: M) -> bool {
    &&& c.l_ok_c@ == m.l_ok_c && c.l_ok_b@ == m.l_ok_b
    &&& c.l_pk_c@ == m.l_pk_c && c.l_pk_b@ == m.l_pk_b
    &&& c.l_sk_c@ == m.l_sk_c && c.l_sk_b@ == m.l_sk_b
    &&& c.l_qty_c@ == m.l_qty_c && c.l_qty_b@ == m.l_qty_b
    &&& c.l_price_c@ == m.l_price_c && c.l_price_b@ == m.l_price_b
    &&& c.l_disc_c@ == m.l_disc_c && c.l_disc_b@ == m.l_disc_b
    &&& c.l_ic@ == m.l_ic && c.l_ib@ == m.l_ib && c.l_kind == m.l_kind
    &&& c.dir@ == m.dir && c.kb as int == m.kb
    &&& c.l_bs as int == m.l_bs && c.l_n == m.l_n
    &&& c.o_key_c@ == m.o_key_c && c.o_key_b@ == m.o_key_b
    &&& c.o_date_c@ == m.o_date_c && c.o_date_b@ == m.o_date_b && c.o_date_z@ == m.o_date_z && c.cluster == m.cluster
    &&& c.o_ic@ == m.o_ic && c.o_ib@ == m.o_ib && c.o_kind == m.o_kind
    &&& c.o_bs as int == m.o_bs && c.o_n == m.o_n
    &&& c.o_bsz_ok ==> c.o_bsz as int == m.o_bs
    &&& c.p_key_c@ == m.p_key_c && c.p_key_b@ == m.p_key_b
    &&& c.p_name_o@ == m.p_name_o && c.p_name_y@ == m.p_name_y && c.p_name_y@.len() <= usize::MAX && c.py_n == c.p_name_y@.len()
    &&& c.p_kind == m.p_kind && c.p_bs as int == m.p_bs && c.p_n == m.p_n
    &&& c.t_pk_c@ == m.t_pk_c && c.t_pk_b@ == m.t_pk_b
    &&& c.t_sk_c@ == m.t_sk_c && c.t_sk_b@ == m.t_sk_b
    &&& c.t_cost_c@ == m.t_cost_c && c.t_cost_b@ == m.t_cost_b
    &&& c.t_kind == m.t_kind && c.t_bs as int == m.t_bs && c.t_n == m.t_n
    &&& c.s_key_c@ == m.s_key_c && c.s_key_b@ == m.s_key_b
    &&& c.s_nk_c@ == m.s_nk_c && c.s_nk_b@ == m.s_nk_b
    &&& c.s_kind == m.s_kind && c.s_bs as int == m.s_bs && c.s_n == m.s_n
    &&& c.n_key_c@ == m.n_key_c && c.n_key_b@ == m.n_key_b
    &&& c.n_name_o@ == m.n_name_o && c.n_name_y@ == m.n_name_y && c.n_name_y@.len() <= usize::MAX
    &&& c.n_bs as int == m.n_bs && c.n_n == m.n_n
    &&& c.e32@ == Seq::<u32>::empty() && c.e64@ == Seq::<u64>::empty()
}

/// Kinds and lengths of the parts the query reads (what the extent reads require).
pub open spec fn kinds_ok(sv: crate::gendb_entry::stores::StoresView) -> bool {
    let f = fx(sv);
    let c = sv.custpart;
    let s = sv.suppliers;
    &&& sv.factspk.len() == 77
    &&& f.len() == 75
    &&& f[F_L_IDX_C as int] is U32 && f[F_L_IDX_B as int] is U64
    &&& f[F_L_IDX_KIND as int] is U64 && pv_u64(f[F_L_IDX_KIND as int]).len() == 1
    &&& sv.factspk[K_DIR_BASE as int] is I64 && pv_i64(sv.factspk[K_DIR_BASE as int]).len() == 1
    &&& sv.factspk[K_DIR_POS as int] is U32
    &&& f[F_L_LAYOUT as int] is U64 && pv_u64(f[F_L_LAYOUT as int]).len() == 2
    &&& f[F_L_OK_C as int] is U32 && f[F_L_OK_B as int] is I64
    &&& f[F_L_PK_C as int] is U32 && f[F_L_PK_B as int] is I64
    &&& f[F_L_SK_C as int] is U32 && f[F_L_SK_B as int] is I64
    &&& f[F_L_QTY_C as int] is U16 && f[F_L_QTY_B as int] is I64
    &&& f[F_L_PRICE_C as int] is U32 && f[F_L_PRICE_B as int] is I64
    &&& f[F_L_DISC_C as int] is U8 && f[F_L_DISC_B as int] is I64
    &&& f[F_O_LAYOUT as int] is U64 && pv_u64(f[F_O_LAYOUT as int]).len() == 2
    &&& f[F_O_KEY_C as int] is U32 && f[F_O_KEY_B as int] is I64
    &&& f[F_O_DATE_C as int] is U16 && f[F_O_DATE_B as int] is I64 && f[F_O_DATE_Z as int] is I64
    &&& f[F_CLUSTER as int] is U64 && pv_u64(f[F_CLUSTER as int]).len() == 1
    &&& f[F_O_IDX_C as int] is U32 && f[F_O_IDX_B as int] is U64
    &&& f[F_O_IDX_KIND as int] is U64 && pv_u64(f[F_O_IDX_KIND as int]).len() == 1
    &&& c.len() == 50
    &&& c[C_P_LAYOUT as int] is U64 && pv_u64(c[C_P_LAYOUT as int]).len() == 2
    &&& c[C_P_KEY_C as int] is U32 && c[C_P_KEY_B as int] is I64
    &&& c[C_P_NAME_O as int] is U64 && c[C_P_NAME_Y as int] is U8
    &&& c[C_P_KIND as int] is U64 && pv_u64(c[C_P_KIND as int]).len() == 1
    &&& sv.partsig.len() == 51 && sv.partsig[G_SIG as int] is U64
    &&& s.len() == 48
    &&& s[S_PS_LAYOUT as int] is U64 && pv_u64(s[S_PS_LAYOUT as int]).len() == 2
    &&& s[S_PS_PK_C as int] is U32 && s[S_PS_PK_B as int] is I64
    &&& s[S_PS_SK_C as int] is U32 && s[S_PS_SK_B as int] is I64
    &&& s[S_PS_COST_C as int] is U32 && s[S_PS_COST_B as int] is I64
    &&& s[S_PS_KIND as int] is U64 && pv_u64(s[S_PS_KIND as int]).len() == 1
    &&& s[S_S_LAYOUT as int] is U64 && pv_u64(s[S_S_LAYOUT as int]).len() == 2
    &&& s[S_S_KEY_C as int] is U32 && s[S_S_KEY_B as int] is I64
    &&& s[S_S_NK_C as int] is U8 && s[S_S_NK_B as int] is I64
    &&& s[S_S_KIND as int] is U64 && pv_u64(s[S_S_KIND as int]).len() == 1
    &&& s[S_N_LAYOUT as int] is U64 && pv_u64(s[S_N_LAYOUT as int]).len() == 2
    &&& s[S_N_KEY_C as int] is U8 && s[S_N_KEY_B as int] is I64
    &&& s[S_N_NAME_O as int] is U64 && s[S_N_NAME_Y as int] is U8
}

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

/// The two values of a layout part: rows and block rows.
fn layout(sp: &mut StoredParts, i: usize) -> (r: (u64, u64))
    requires i < old(sp)@.len(), old(sp)@[i as int] is U64, pv_u64(old(sp)@[i as int]).len() == 2,
    ensures final(sp)@ == old(sp)@, r.0 == pv_u64(old(sp)@[i as int])[0], r.1 == pv_u64(old(sp)@[i as int])[1],
{
    let v = sp.extent_u64(i, 0, 2);
    (v[0], v[1])
}

/// The value of a one-entry U64 part.
fn flag(sp: &mut StoredParts, i: usize) -> (r: u64)
    requires i < old(sp)@.len(), old(sp)@[i as int] is U64, pv_u64(old(sp)@[i as int]).len() == 1,
    ensures final(sp)@ == old(sp)@, r == pv_u64(old(sp)@[i as int])[0],
{
    let v = sp.extent_u64(i, 0, 1);
    v[0]
}

/// Every part the query reads, as whole extents (row counts are the code slices' lengths).
pub fn load(stores: &mut Stores, Ghost(m): Ghost<M>) -> (c: Cols)
    requires
        kinds_ok(old(stores)@),
        m == model_of(old(stores)@),
        model_ok(m),
    ensures
        final(stores)@ == old(stores)@,
        cols_ok(c, m),
        c.p_sig@ == sigs_of(old(stores)@),
{
    let (_, l_bs) = layout(&mut stores.factspk, F_L_LAYOUT);
    let (_, o_bs) = layout(&mut stores.factspk, F_O_LAYOUT);
    let (_, p_bs) = layout(&mut stores.custpart, C_P_LAYOUT);
    let (_, t_bs) = layout(&mut stores.suppliers, S_PS_LAYOUT);
    let (_, s_bs) = layout(&mut stores.suppliers, S_S_LAYOUT);
    let (_, n_bs) = layout(&mut stores.suppliers, S_N_LAYOUT);
    let e32: &'static [u32] = stores.factspk.extent_u32(F_O_IDX_C, 0, 0);
    let e64: &'static [u64] = stores.factspk.extent_u64(F_O_IDX_B, 0, 0);
    proof {
        assert(e32@ =~= Seq::<u32>::empty());
        assert(e64@ =~= Seq::<u64>::empty());
    }
    let l_pk_c = whole_u32(&mut stores.factspk, F_L_PK_C);
    let o_key_c = whole_u32(&mut stores.factspk, F_O_KEY_C);
    let p_key_c = whole_u32(&mut stores.custpart, C_P_KEY_C);
    let t_pk_c = whole_u32(&mut stores.suppliers, S_PS_PK_C);
    let s_key_c = whole_u32(&mut stores.suppliers, S_S_KEY_C);
    let n_key_c = whole_u8(&mut stores.suppliers, S_N_KEY_C);
    let p_name_y = whole_u8(&mut stores.custpart, C_P_NAME_Y);
    let n_name_y = whole_u8(&mut stores.suppliers, S_N_NAME_Y);
    let _p_name_len = p_name_y.len();
    let _n_name_len = n_name_y.len();
    let o_bsz_ok = o_bs <= usize::MAX as u64;
    let o_bsz: usize = if o_bsz_ok { o_bs as usize } else { 1 };
    let c = Cols {
        l_ok_c: whole_u32(&mut stores.factspk, F_L_OK_C),
        l_ok_b: whole_i64(&mut stores.factspk, F_L_OK_B),
        l_pk_c,
        l_pk_b: whole_i64(&mut stores.factspk, F_L_PK_B),
        l_sk_c: whole_u32(&mut stores.factspk, F_L_SK_C),
        l_sk_b: whole_i64(&mut stores.factspk, F_L_SK_B),
        l_qty_c: whole_u16(&mut stores.factspk, F_L_QTY_C),
        l_qty_b: whole_i64(&mut stores.factspk, F_L_QTY_B),
        l_price_c: whole_u32(&mut stores.factspk, F_L_PRICE_C),
        l_price_b: whole_i64(&mut stores.factspk, F_L_PRICE_B),
        l_disc_c: whole_u8(&mut stores.factspk, F_L_DISC_C),
        l_disc_b: whole_i64(&mut stores.factspk, F_L_DISC_B),
        l_ic: whole_u32(&mut stores.factspk, F_L_IDX_C),
        l_ib: whole_u64(&mut stores.factspk, F_L_IDX_B),
        l_kind: flag(&mut stores.factspk, F_L_IDX_KIND),
        dir: whole_u32(&mut stores.factspk, K_DIR_POS),
        kb: stores.factspk.extent_i64(K_DIR_BASE, 0, 1)[0],
        l_bs,
        l_n: l_pk_c.len(),
        o_key_c,
        o_key_b: whole_i64(&mut stores.factspk, F_O_KEY_B),
        o_date_c: whole_u16(&mut stores.factspk, F_O_DATE_C),
        o_date_b: whole_i64(&mut stores.factspk, F_O_DATE_B),
        o_date_z: whole_i64(&mut stores.factspk, F_O_DATE_Z),
        o_ic: whole_u32(&mut stores.factspk, F_O_IDX_C),
        o_ib: whole_u64(&mut stores.factspk, F_O_IDX_B),
        o_kind: flag(&mut stores.factspk, F_O_IDX_KIND),
        cluster: flag(&mut stores.factspk, F_CLUSTER),
        o_bs,
        o_bsz,
        o_bsz_ok,
        o_n: o_key_c.len(),
        p_key_c,
        p_key_b: whole_i64(&mut stores.custpart, C_P_KEY_B),
        p_name_o: whole_u64(&mut stores.custpart, C_P_NAME_O),
        p_name_y,
        py_n: _p_name_len,
        p_kind: flag(&mut stores.custpart, C_P_KIND),
        p_sig: whole_u64(&mut stores.partsig, G_SIG),
        p_bs,
        p_n: p_key_c.len(),
        t_pk_c,
        t_pk_b: whole_i64(&mut stores.suppliers, S_PS_PK_B),
        t_sk_c: whole_u32(&mut stores.suppliers, S_PS_SK_C),
        t_sk_b: whole_i64(&mut stores.suppliers, S_PS_SK_B),
        t_cost_c: whole_u32(&mut stores.suppliers, S_PS_COST_C),
        t_cost_b: whole_i64(&mut stores.suppliers, S_PS_COST_B),
        t_kind: flag(&mut stores.suppliers, S_PS_KIND),
        t_bs,
        t_n: t_pk_c.len(),
        s_key_c,
        s_key_b: whole_i64(&mut stores.suppliers, S_S_KEY_B),
        s_nk_c: whole_u8(&mut stores.suppliers, S_S_NK_C),
        s_nk_b: whole_i64(&mut stores.suppliers, S_S_NK_B),
        s_kind: flag(&mut stores.suppliers, S_S_KIND),
        s_bs,
        s_n: s_key_c.len(),
        n_key_c,
        n_key_b: whole_i64(&mut stores.suppliers, S_N_KEY_B),
        n_name_o: whole_u64(&mut stores.suppliers, S_N_NAME_O),
        n_name_y,
        n_bs,
        n_n: n_key_c.len(),
        e32,
        e64,
    };
    c
}

} // verus!
