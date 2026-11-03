//! Part-level model of the columns Q9 reads. `M` is the view of the parts of the three storage uses: `facts`
//! (lineitem and orders, each stored through a row map), `custpart` (part, canonical order; with `partsig`'s p_name
//! trigram signatures) and `suppliers`
//! (partsupp, supplier and nation, canonical order). Integer, numeric and date values are frame-of-reference
//! decoded: `base[row / block] + code[row]` (numerics as coefficients of scale 2, dates as days since 2000-01-01);
//! text values (p_name, n_name) are byte ranges of an offsets part and a bytes part.
//!
//! The join of the statement is described per stored lineitem row `j` (`jok`): its part, supplier, partsupp row,
//! order and its supplier's nation are the rows holding the matching keys (`ppos`, `spos`, `tpos`, `opos`, `npos`;
//! unique under the declared primary keys), and its contribution to the group (nation row, year) is
//! `amt(j) = l_extendedprice * (100 - l_discount) - ps_supplycost * l_quantity` at scale 4.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stores::StoresView;
use crate::spec::value::*;
use crate::spec::numeric::pow10;
use crate::spec::datetime::{date_valid, civil_from_date};
use crate::link::query::proj;
use crate::stores::facts::interface as fi;
use crate::stores::custpart::interface as ci;
use crate::stores::suppliers::interface as si;
use crate::stores::partsig::interface as gi;

verus! {

// ------------------------------------------------------------------------------------------------ part views

pub open spec fn pv_u8(p: PartView) -> Seq<u8> {
    match p { PartView::U8(s) => s, _ => Seq::empty() }
}

pub open spec fn pv_u16(p: PartView) -> Seq<u16> {
    match p { PartView::U16(s) => s, _ => Seq::empty() }
}

pub open spec fn pv_u32(p: PartView) -> Seq<u32> {
    match p { PartView::U32(s) => s, _ => Seq::empty() }
}

pub open spec fn pv_u64(p: PartView) -> Seq<u64> {
    match p { PartView::U64(s) => s, _ => Seq::empty() }
}

pub open spec fn pv_i64(p: PartView) -> Seq<i64> {
    match p { PartView::I64(s) => s, _ => Seq::empty() }
}

// ------------------------------------------------------------------------------------------------ part indexes

// storage `facts`: lineitem parts at 0.., orders parts at 48..
pub const F_L_LAYOUT: usize = 0;
pub const F_L_OK_C: usize = 4;
pub const F_L_OK_B: usize = 5;
pub const F_L_PK_C: usize = 6;
pub const F_L_PK_B: usize = 7;
pub const F_L_SK_C: usize = 8;
pub const F_L_SK_B: usize = 9;
pub const F_L_QTY_C: usize = 12;
pub const F_L_QTY_B: usize = 13;
pub const F_L_PRICE_C: usize = 14;
pub const F_L_PRICE_B: usize = 15;
pub const F_L_DISC_C: usize = 16;
pub const F_L_DISC_B: usize = 17;
pub const F_O_LAYOUT: usize = 48;
pub const F_O_KEY_C: usize = 52;
pub const F_O_KEY_B: usize = 53;
pub const F_O_DATE_C: usize = 62;
pub const F_O_DATE_B: usize = 63;
pub const F_O_DATE_Z: usize = 64;
pub const F_O_IDX_C: usize = 71;
pub const F_O_IDX_B: usize = 72;
pub const F_O_IDX_KIND: usize = 73;
pub const F_CLUSTER: usize = 74;
pub const F_L_IDX_C: usize = 45;
pub const F_L_IDX_B: usize = 46;
pub const F_L_IDX_KIND: usize = 47;
// storage `factspk`: facts' 75 parts, then the l_partkey directory
pub const K_DIR_BASE: usize = 75;
pub const K_DIR_POS: usize = 76;
// storage `custpart`: part parts at 21..
pub const C_P_LAYOUT: usize = 21;
pub const C_P_KEY_C: usize = 23;
pub const C_P_KEY_B: usize = 24;
pub const C_P_NAME_O: usize = 25;
pub const C_P_NAME_Y: usize = 26;
pub const C_P_KIND: usize = 49;
// storage `partsig`: custpart's 50 parts, then the p_name trigram signatures
pub const G_SIG: usize = 50;
// storage `suppliers`: partsupp parts at 0.., supplier at 13.., nation at 30..
pub const S_PS_LAYOUT: usize = 0;
pub const S_PS_PK_C: usize = 2;
pub const S_PS_PK_B: usize = 3;
pub const S_PS_SK_C: usize = 4;
pub const S_PS_SK_B: usize = 5;
pub const S_PS_COST_C: usize = 8;
pub const S_PS_COST_B: usize = 9;
pub const S_PS_KIND: usize = 12;
pub const S_S_LAYOUT: usize = 13;
pub const S_S_KEY_C: usize = 15;
pub const S_S_KEY_B: usize = 16;
pub const S_S_NK_C: usize = 21;
pub const S_S_NK_B: usize = 22;
pub const S_S_KIND: usize = 29;
pub const S_N_LAYOUT: usize = 30;
pub const S_N_KEY_C: usize = 32;
pub const S_N_KEY_B: usize = 33;
pub const S_N_NAME_O: usize = 34;
pub const S_N_NAME_Y: usize = 35;

// ------------------------------------------------------------------------------------------------ the model

/// The parts this query reads, as sequences (`l_*` lineitem, `o_*` orders, `p_*` part, `t_*` partsupp, `s_*`
/// supplier, `n_*` nation; `*_c` codes, `*_b` group bases, `*_bs` block rows, `*_nb` groups, `l_map`/`o_map`
/// stored row -> canonical row, `*_kind` key index kinds).
pub struct M {
    pub l_n: int,
    pub l_bs: int,
    pub l_nb: int,
    pub l_map: Seq<int>,
    pub l_ok_c: Seq<u32>,
    pub l_ok_b: Seq<i64>,
    pub l_pk_c: Seq<u32>,
    pub l_pk_b: Seq<i64>,
    pub l_sk_c: Seq<u32>,
    pub l_sk_b: Seq<i64>,
    pub l_qty_c: Seq<u16>,
    pub l_qty_b: Seq<i64>,
    pub l_price_c: Seq<u32>,
    pub l_price_b: Seq<i64>,
    pub l_disc_c: Seq<u8>,
    pub l_disc_b: Seq<i64>,
    pub l_ic: Seq<u32>,
    pub l_ib: Seq<u64>,
    pub l_kind: u64,
    pub dir: Seq<u32>,
    pub kb: int,
    pub o_n: int,
    pub o_bs: int,
    pub o_nb: int,
    pub o_map: Seq<int>,
    pub o_key_c: Seq<u32>,
    pub o_key_b: Seq<i64>,
    pub o_date_c: Seq<u16>,
    pub o_date_b: Seq<i64>,
    pub o_date_z: Seq<i64>,
    pub o_ic: Seq<u32>,
    pub o_ib: Seq<u64>,
    pub o_kind: u64,
    pub cluster: u64,
    pub p_n: int,
    pub p_bs: int,
    pub p_nb: int,
    pub p_key_c: Seq<u32>,
    pub p_key_b: Seq<i64>,
    pub p_name_o: Seq<u64>,
    pub p_name_y: Seq<u8>,
    pub p_kind: u64,
    pub t_n: int,
    pub t_bs: int,
    pub t_nb: int,
    pub t_pk_c: Seq<u32>,
    pub t_pk_b: Seq<i64>,
    pub t_sk_c: Seq<u32>,
    pub t_sk_b: Seq<i64>,
    pub t_cost_c: Seq<u32>,
    pub t_cost_b: Seq<i64>,
    pub t_kind: u64,
    pub s_n: int,
    pub s_bs: int,
    pub s_nb: int,
    pub s_key_c: Seq<u32>,
    pub s_key_b: Seq<i64>,
    pub s_nk_c: Seq<u8>,
    pub s_nk_b: Seq<i64>,
    pub s_kind: u64,
    pub n_n: int,
    pub n_bs: int,
    pub n_nb: int,
    pub n_key_c: Seq<u8>,
    pub n_key_b: Seq<i64>,
    pub n_name_o: Seq<u64>,
    pub n_name_y: Seq<u8>,
}

/// The facts parts inside storage `factspk` (its first 75 parts).
pub open spec fn fx(sv: StoresView) -> Seq<PartView> {
    sv.factspk.subrange(0, 75)
}

/// The model of the parts of the three storage uses.
pub open spec fn model_of(sv: StoresView) -> M {
    let f = fx(sv);
    let c = sv.custpart;
    let s = sv.suppliers;
    let l_n = pv_u64(f[F_L_LAYOUT as int])[0] as int;
    let o_n = pv_u64(f[F_O_LAYOUT as int])[0] as int;
    M {
        l_n,
        l_bs: pv_u64(f[F_L_LAYOUT as int])[1] as int,
        l_nb: pv_i64(f[F_L_OK_B as int]).len() as int,
        l_map: fi::lineitem_map(f.subrange(0, 48), l_n),
        l_ok_c: pv_u32(f[F_L_OK_C as int]),
        l_ok_b: pv_i64(f[F_L_OK_B as int]),
        l_pk_c: pv_u32(f[F_L_PK_C as int]),
        l_pk_b: pv_i64(f[F_L_PK_B as int]),
        l_sk_c: pv_u32(f[F_L_SK_C as int]),
        l_sk_b: pv_i64(f[F_L_SK_B as int]),
        l_qty_c: pv_u16(f[F_L_QTY_C as int]),
        l_qty_b: pv_i64(f[F_L_QTY_B as int]),
        l_price_c: pv_u32(f[F_L_PRICE_C as int]),
        l_price_b: pv_i64(f[F_L_PRICE_B as int]),
        l_disc_c: pv_u8(f[F_L_DISC_C as int]),
        l_disc_b: pv_i64(f[F_L_DISC_B as int]),
        l_ic: pv_u32(f[F_L_IDX_C as int]),
        l_ib: pv_u64(f[F_L_IDX_B as int]),
        l_kind: pv_u64(f[F_L_IDX_KIND as int])[0],
        dir: pv_u32(sv.factspk[K_DIR_POS as int]),
        kb: pv_i64(sv.factspk[K_DIR_BASE as int])[0] as int,
        o_n,
        o_bs: pv_u64(f[F_O_LAYOUT as int])[1] as int,
        o_nb: pv_i64(f[F_O_KEY_B as int]).len() as int,
        o_map: fi::orders_map(f.subrange(48, 74), o_n),
        o_key_c: pv_u32(f[F_O_KEY_C as int]),
        o_key_b: pv_i64(f[F_O_KEY_B as int]),
        o_date_c: pv_u16(f[F_O_DATE_C as int]),
        o_date_b: pv_i64(f[F_O_DATE_B as int]),
        o_date_z: pv_i64(f[F_O_DATE_Z as int]),
        o_ic: pv_u32(f[F_O_IDX_C as int]),
        o_ib: pv_u64(f[F_O_IDX_B as int]),
        o_kind: pv_u64(f[F_O_IDX_KIND as int])[0],
        cluster: pv_u64(f[F_CLUSTER as int])[0],
        p_n: pv_u64(c[C_P_LAYOUT as int])[0] as int,
        p_bs: pv_u64(c[C_P_LAYOUT as int])[1] as int,
        p_nb: pv_i64(c[C_P_KEY_B as int]).len() as int,
        p_key_c: pv_u32(c[C_P_KEY_C as int]),
        p_key_b: pv_i64(c[C_P_KEY_B as int]),
        p_name_o: pv_u64(c[C_P_NAME_O as int]),
        p_name_y: pv_u8(c[C_P_NAME_Y as int]),
        p_kind: pv_u64(c[C_P_KIND as int])[0],
        t_n: pv_u64(s[S_PS_LAYOUT as int])[0] as int,
        t_bs: pv_u64(s[S_PS_LAYOUT as int])[1] as int,
        t_nb: pv_i64(s[S_PS_PK_B as int]).len() as int,
        t_pk_c: pv_u32(s[S_PS_PK_C as int]),
        t_pk_b: pv_i64(s[S_PS_PK_B as int]),
        t_sk_c: pv_u32(s[S_PS_SK_C as int]),
        t_sk_b: pv_i64(s[S_PS_SK_B as int]),
        t_cost_c: pv_u32(s[S_PS_COST_C as int]),
        t_cost_b: pv_i64(s[S_PS_COST_B as int]),
        t_kind: pv_u64(s[S_PS_KIND as int])[0],
        s_n: pv_u64(s[S_S_LAYOUT as int])[0] as int,
        s_bs: pv_u64(s[S_S_LAYOUT as int])[1] as int,
        s_nb: pv_i64(s[S_S_KEY_B as int]).len() as int,
        s_key_c: pv_u32(s[S_S_KEY_C as int]),
        s_key_b: pv_i64(s[S_S_KEY_B as int]),
        s_nk_c: pv_u8(s[S_S_NK_C as int]),
        s_nk_b: pv_i64(s[S_S_NK_B as int]),
        s_kind: pv_u64(s[S_S_KIND as int])[0],
        n_n: pv_u64(s[S_N_LAYOUT as int])[0] as int,
        n_bs: pv_u64(s[S_N_LAYOUT as int])[1] as int,
        n_nb: pv_i64(s[S_N_KEY_B as int]).len() as int,
        n_key_c: pv_u8(s[S_N_KEY_C as int]),
        n_key_b: pv_i64(s[S_N_KEY_B as int]),
        n_name_o: pv_u64(s[S_N_NAME_O as int]),
        n_name_y: pv_u8(s[S_N_NAME_Y as int]),
    }
}

// ------------------------------------------------------------------------------------------------ decoded values

pub open spec fn lok(m: M, j: int) -> int { m.l_ok_b[j / m.l_bs] as int + m.l_ok_c[j] as int }
pub open spec fn lpk(m: M, j: int) -> int { m.l_pk_b[j / m.l_bs] as int + m.l_pk_c[j] as int }
pub open spec fn lsk(m: M, j: int) -> int { m.l_sk_b[j / m.l_bs] as int + m.l_sk_c[j] as int }
pub open spec fn lqty(m: M, j: int) -> int { m.l_qty_b[j / m.l_bs] as int + m.l_qty_c[j] as int }
pub open spec fn lprice(m: M, j: int) -> int { m.l_price_b[j / m.l_bs] as int + m.l_price_c[j] as int }
pub open spec fn ldisc(m: M, j: int) -> int { m.l_disc_b[j / m.l_bs] as int + m.l_disc_c[j] as int }
pub open spec fn okey(m: M, q: int) -> int { m.o_key_b[q / m.o_bs] as int + m.o_key_c[q] as int }
pub open spec fn odate(m: M, q: int) -> int { m.o_date_b[q / m.o_bs] as int + m.o_date_c[q] as int }
pub open spec fn pkey(m: M, c: int) -> int { m.p_key_b[c / m.p_bs] as int + m.p_key_c[c] as int }
pub open spec fn pname(m: M, c: int) -> Seq<u8> { m.p_name_y.subrange(m.p_name_o[c] as int, m.p_name_o[c + 1] as int) }
pub open spec fn tpk(m: M, t: int) -> int { m.t_pk_b[t / m.t_bs] as int + m.t_pk_c[t] as int }
pub open spec fn tsk(m: M, t: int) -> int { m.t_sk_b[t / m.t_bs] as int + m.t_sk_c[t] as int }
pub open spec fn tcost(m: M, t: int) -> int { m.t_cost_b[t / m.t_bs] as int + m.t_cost_c[t] as int }
pub open spec fn skey(m: M, s: int) -> int { m.s_key_b[s / m.s_bs] as int + m.s_key_c[s] as int }
pub open spec fn snk(m: M, s: int) -> int { m.s_nk_b[s / m.s_bs] as int + m.s_nk_c[s] as int }
pub open spec fn nkey(m: M, n: int) -> int { m.n_key_b[n / m.n_bs] as int + m.n_key_c[n] as int }
pub open spec fn nname(m: M, n: int) -> Seq<u8> { m.n_name_y.subrange(m.n_name_o[n] as int, m.n_name_o[n + 1] as int) }

// ------------------------------------------------------------------------------------------------ key positions

/// The stored orders position with `o_orderkey == k` (the chosen one; unique under the primary key), or `o_n`.
pub open spec fn opos(m: M, k: int) -> int {
    if exists|q: int| 0 <= q < m.o_n && #[trigger] okey(m, q) == k {
        choose|q: int| 0 <= q < m.o_n && #[trigger] okey(m, q) == k
    } else {
        m.o_n
    }
}

/// The part row with `p_partkey == k`, or `p_n`.
pub open spec fn ppos(m: M, k: int) -> int {
    if exists|c: int| 0 <= c < m.p_n && #[trigger] pkey(m, c) == k {
        choose|c: int| 0 <= c < m.p_n && #[trigger] pkey(m, c) == k
    } else {
        m.p_n
    }
}

/// The supplier row with `s_suppkey == k`, or `s_n`.
pub open spec fn spos(m: M, k: int) -> int {
    if exists|s: int| 0 <= s < m.s_n && #[trigger] skey(m, s) == k {
        choose|s: int| 0 <= s < m.s_n && #[trigger] skey(m, s) == k
    } else {
        m.s_n
    }
}

/// The nation row with `n_nationkey == k`, or `n_n`.
pub open spec fn npos(m: M, k: int) -> int {
    if exists|n: int| 0 <= n < m.n_n && #[trigger] nkey(m, n) == k {
        choose|n: int| 0 <= n < m.n_n && #[trigger] nkey(m, n) == k
    } else {
        m.n_n
    }
}

/// The partsupp row with `(ps_partkey, ps_suppkey) == (pk, sk)`, or `t_n`.
pub open spec fn tpos(m: M, pk: int, sk: int) -> int {
    if exists|t: int| 0 <= t < m.t_n && #[trigger] tpk(m, t) == pk && tsk(m, t) == sk {
        choose|t: int| 0 <= t < m.t_n && #[trigger] tpk(m, t) == pk && tsk(m, t) == sk
    } else {
        m.t_n
    }
}

// ------------------------------------------------------------------------------------------------ facts

pub open spec fn in_i64(x: int) -> bool { i64::MIN <= x <= i64::MAX }

/// A numeric(15,2) coefficient.
pub open spec fn num15(x: int) -> bool { -pow10(15) < x < pow10(15) }

/// Uniform frame-of-reference groups of `bs` rows over `n` rows (`nb` groups).
pub open spec fn frame_ok(n: int, bs: int, nb: int) -> bool {
    &&& 1 <= bs && 0 <= n && n + bs <= u64::MAX
    &&& nb * bs >= n && (nb > 0 ==> (nb - 1) * bs < n) && nb >= 0
}

/// Layout of the columns read: frames and part lengths.
pub open spec fn shapes_ok(m: M) -> bool {
    &&& frame_ok(m.l_n, m.l_bs, m.l_nb)
    &&& m.l_ok_c.len() == m.l_n && m.l_ok_b.len() == m.l_nb
    &&& m.l_pk_c.len() == m.l_n && m.l_pk_b.len() == m.l_nb
    &&& m.l_sk_c.len() == m.l_n && m.l_sk_b.len() == m.l_nb
    &&& m.l_qty_c.len() == m.l_n && m.l_qty_b.len() == m.l_nb
    &&& m.l_price_c.len() == m.l_n && m.l_price_b.len() == m.l_nb
    &&& m.l_disc_c.len() == m.l_n && m.l_disc_b.len() == m.l_nb
    &&& frame_ok(m.o_n, m.o_bs, m.o_nb)
    &&& m.o_key_c.len() == m.o_n && m.o_key_b.len() == m.o_nb
    &&& m.o_date_c.len() == m.o_n && m.o_date_b.len() == m.o_nb
    &&& frame_ok(m.p_n, m.p_bs, m.p_nb)
    &&& m.p_key_c.len() == m.p_n && m.p_key_b.len() == m.p_nb
    &&& ci::common::colfmt::text_parts_wf(m.p_name_o, m.p_name_y, m.p_n)
    &&& frame_ok(m.t_n, m.t_bs, m.t_nb)
    &&& m.t_pk_c.len() == m.t_n && m.t_pk_b.len() == m.t_nb
    &&& m.t_sk_c.len() == m.t_n && m.t_sk_b.len() == m.t_nb
    &&& m.t_cost_c.len() == m.t_n && m.t_cost_b.len() == m.t_nb
    &&& frame_ok(m.s_n, m.s_bs, m.s_nb)
    &&& m.s_key_c.len() == m.s_n && m.s_key_b.len() == m.s_nb
    &&& m.s_nk_c.len() == m.s_n && m.s_nk_b.len() == m.s_nb
    &&& frame_ok(m.n_n, m.n_bs, m.n_nb)
    &&& m.n_key_c.len() == m.n_n && m.n_key_b.len() == m.n_nb
    &&& si::common::colfmt::text_parts_wf(m.n_name_o, m.n_name_y, m.n_n)
}

/// Decoded values: machine ranges, the declared numeric precision, valid dates.
pub open spec fn values_ok(m: M) -> bool {
    &&& forall|j: int| 0 <= j < m.l_n ==> {
        &&& in_i64(#[trigger] lok(m, j)) && in_i64(lpk(m, j)) && in_i64(lsk(m, j))
        &&& num15(lqty(m, j)) && num15(lprice(m, j)) && num15(ldisc(m, j))
    }
    &&& forall|q: int| 0 <= q < m.o_n ==> in_i64(#[trigger] okey(m, q)) && date_valid(odate(m, q)) && in_i64(odate(m, q))
    &&& forall|c: int| 0 <= c < m.p_n ==> in_i64(#[trigger] pkey(m, c))
    &&& forall|t: int| 0 <= t < m.t_n ==> in_i64(#[trigger] tpk(m, t)) && in_i64(tsk(m, t)) && num15(tcost(m, t))
    &&& forall|s: int| 0 <= s < m.s_n ==> in_i64(#[trigger] skey(m, s)) && in_i64(snk(m, s))
    &&& forall|n: int| 0 <= n < m.n_n ==> in_i64(#[trigger] nkey(m, n))
}

/// The declared primary keys at the part level, and the key indexes the lookups use.
pub open spec fn keys_ok(m: M) -> bool {
    &&& forall|a: int, b: int| 0 <= a < m.o_n && 0 <= b < m.o_n && a != b ==> #[trigger] okey(m, a) != #[trigger] okey(m, b)
    &&& forall|a: int, b: int| 0 <= a < m.p_n && 0 <= b < m.p_n && a != b ==> #[trigger] pkey(m, a) != #[trigger] pkey(m, b)
    &&& forall|a: int, b: int| 0 <= a < m.s_n && 0 <= b < m.s_n && a != b ==> #[trigger] skey(m, a) != #[trigger] skey(m, b)
    &&& forall|a: int, b: int| 0 <= a < m.n_n && 0 <= b < m.n_n && a != b ==> #[trigger] nkey(m, a) != #[trigger] nkey(m, b)
    &&& forall|a: int, b: int| 0 <= a < m.t_n && 0 <= b < m.t_n && a != b ==>
            #[trigger] tpk(m, a) != #[trigger] tpk(m, b) || tsk(m, a) != tsk(m, b)
    &&& fi::common::keyidx::keyidx_ok(m.o_key_c, m.o_key_b, m.o_ic, m.o_ib, m.o_bs, m.o_kind, m.o_n)
    &&& ci::common::keyidx::keyidx_ok(m.p_key_c, m.p_key_b, Seq::<u32>::empty(), Seq::<u64>::empty(), m.p_bs, m.p_kind, m.p_n)
    &&& si::common::keyidx::keyidx_ok(m.t_pk_c, m.t_pk_b, Seq::<u32>::empty(), Seq::<u64>::empty(), m.t_bs, m.t_kind, m.t_n)
    &&& si::common::keyidx::keyidx_ok(m.s_key_c, m.s_key_b, Seq::<u32>::empty(), Seq::<u64>::empty(), m.s_bs, m.s_kind, m.s_n)
}

/// Orders facts: order dates are bounded by their group's zone maximum, and with the co-clustering flag the
/// lineitem rows follow the stored orders (the order position of `l_orderkey` never decreases).
pub open spec fn ofacts_ok(m: M) -> bool {
    &&& m.o_date_z.len() == m.o_nb
    &&& forall|q: int| 0 <= q < m.o_n ==> #[trigger] odate(m, q) <= m.o_date_z[q / m.o_bs]
    &&& m.cluster == 1 ==> forall|a: int, b: int| 0 <= a <= b < m.l_n ==>
            #[trigger] opos(m, lok(m, a)) <= #[trigger] opos(m, lok(m, b))
}

/// l_partkey at position `r` of the lineitem key index.
pub open spec fn lkey(m: M, r: int) -> int {
    lpk(m, fi::common::keyidx::irow(m.l_kind, m.l_ic, m.l_ib, m.l_bs, r))
}

/// Directory entry `i`: the first key-index position whose key is at least `kb + i` (or `l_n`).
pub open spec fn dentry(m: M, i: int) -> bool {
    let d = m.dir[i] as int;
    &&& d <= m.l_n
    &&& forall|r: int| 0 <= r < d ==> #[trigger] lkey(m, r) < m.kb + i
    &&& d < m.l_n ==> lkey(m, d) >= m.kb + i
}

/// The lineitem l_partkey key index and its directory (storage `factspk`).
pub open spec fn pdir_ok(m: M) -> bool {
    &&& fi::common::keyidx::keyidx_ok(m.l_pk_c, m.l_pk_b, m.l_ic, m.l_ib, m.l_bs, m.l_kind, m.l_n)
    &&& m.dir.len() >= 1
    &&& forall|i: int| 0 <= i < m.dir.len() ==> #[trigger] dentry(m, i)
}

/// The p_name trigram signatures `sig` (storage `partsig`): one per part row, covering the row's name, which is
/// ASCII unless the signature is all ones.
pub open spec fn psig_ok(sig: Seq<u64>, m: M) -> bool {
    &&& sig.len() == m.p_n
    &&& forall|c: int| 0 <= c < m.p_n ==> #[trigger] gi::sig_row_ok(pname(m, c), sig[c])
}

/// The signatures of storage `partsig`.
pub open spec fn sigs_of(sv: StoresView) -> Seq<u64> {
    pv_u64(sv.partsig[G_SIG as int])
}

/// Every fact of the model.
pub open spec fn model_ok(m: M) -> bool {
    &&& shapes_ok(m)
    &&& values_ok(m)
    &&& keys_ok(m)
}

// ------------------------------------------------------------------------------------------------ rows of a database

/// Columns read: lineitem l_orderkey, l_partkey, l_suppkey, l_quantity, l_extendedprice, l_discount; orders
/// o_orderkey, o_orderdate; part p_partkey, p_name; partsupp ps_partkey, ps_suppkey, ps_supplycost; supplier
/// s_suppkey, s_nationkey; nation n_nationkey, n_name.
pub open spec fn lcols() -> Seq<nat> { seq![0nat, 1, 2, 4, 5, 6] }
pub open spec fn ocols() -> Seq<nat> { seq![0nat, 4] }
pub open spec fn pcols() -> Seq<nat> { seq![0nat, 1] }
pub open spec fn tcols() -> Seq<nat> { seq![0nat, 1, 3] }
pub open spec fn scols() -> Seq<nat> { seq![0nat, 3] }
pub open spec fn ncols() -> Seq<nat> { seq![0nat, 1] }

pub open spec fn lrow(m: M, j: int) -> Row {
    seq![Val::Int(lok(m, j)), Val::Int(lpk(m, j)), Val::Int(lsk(m, j)), Val::Num { coeff: lqty(m, j), scale: 2 },
        Val::Num { coeff: lprice(m, j), scale: 2 }, Val::Num { coeff: ldisc(m, j), scale: 2 }]
}

pub open spec fn orow(m: M, q: int) -> Row {
    seq![Val::Int(okey(m, q)), Val::Date(odate(m, q))]
}

pub open spec fn prow(m: M, c: int) -> Row {
    seq![Val::Int(pkey(m, c)), Val::Text(pname(m, c))]
}

pub open spec fn trow(m: M, t: int) -> Row {
    seq![Val::Int(tpk(m, t)), Val::Int(tsk(m, t)), Val::Num { coeff: tcost(m, t), scale: 2 }]
}

pub open spec fn srow(m: M, s: int) -> Row {
    seq![Val::Int(skey(m, s)), Val::Int(snk(m, s))]
}

pub open spec fn nrow(m: M, n: int) -> Row {
    seq![Val::Int(nkey(m, n)), Val::Text(nname(m, n))]
}

/// The database's tables, read through the model: lineitem and orders through their row maps (bijections), the
/// other tables in canonical order.
pub open spec fn rel_ok(m: M, db: Database) -> bool {
    &&& db.tables.len() == 8
    &&& m.l_n == db.tables[0].len()
    &&& fi::common::colfmt::is_perm(m.l_map, m.l_n)
    &&& forall|j: int| 0 <= j < m.l_n ==> #[trigger] proj(db.tables[0][m.l_map[j]], lcols()) == lrow(m, j)
    &&& m.o_n == db.tables[1].len()
    &&& fi::common::colfmt::is_perm(m.o_map, m.o_n)
    &&& forall|q: int| 0 <= q < m.o_n ==> #[trigger] proj(db.tables[1][m.o_map[q]], ocols()) == orow(m, q)
    &&& m.p_n == db.tables[3].len()
    &&& forall|c: int| 0 <= c < m.p_n ==> #[trigger] proj(db.tables[3][c], pcols()) == prow(m, c)
    &&& m.t_n == db.tables[4].len()
    &&& forall|t: int| 0 <= t < m.t_n ==> #[trigger] proj(db.tables[4][t], tcols()) == trow(m, t)
    &&& m.s_n == db.tables[5].len()
    &&& forall|s: int| 0 <= s < m.s_n ==> #[trigger] proj(db.tables[5][s], scols()) == srow(m, s)
    &&& m.n_n == db.tables[6].len()
    &&& forall|n: int| 0 <= n < m.n_n ==> #[trigger] proj(db.tables[6][n], ncols()) == nrow(m, n)
}

} // verus!
