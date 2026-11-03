//! Part-level model of the columns Q3 reads. `M` is the view of the parts (storage `li_okruns`: the parts of storage
//! `facts`, lineitem and orders, orders stored by order date and lineitem co-clustered with them, then the start row
//! of every l_orderkey run of lineitem; storage `custpart`: customer in canonical order). Values are decoded as
//! frame-of-reference integers: `base[row / block] + code[row]` (numerics as coefficients of scale 2, dates as days
//! since 2000-01-01). The predicates here (`shapes_ok`, `values_ok`, `keys_ok`, `cluster_ok`, `runs_ok`, `rel_ok`)
//! are what every database bound to the parts gives (`facts::lemma_model`); the
//! kernels are proved against them, the SQL link (`bridge`) relates them to the statement's rows.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stores::StoresView;
use crate::spec::value::*;
use crate::spec::numeric::pow10;
use crate::spec::datetime::date_valid;
use crate::link::query::proj;
use crate::stores::facts::interface as fi;
use crate::stores::custpart::interface as ci;

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

// storage `facts` (lineitem parts first, then orders at 48, then the cluster flag)
pub const F_L_LAYOUT: usize = 0;
pub const F_L_KEY_C: usize = 4;
pub const F_L_KEY_B: usize = 5;
pub const F_L_PRICE_C: usize = 14;
pub const F_L_PRICE_B: usize = 15;
pub const F_L_DISC_C: usize = 16;
pub const F_L_DISC_B: usize = 17;
pub const F_L_SHIP_C: usize = 28;
pub const F_L_SHIP_B: usize = 29;
pub const F_L_SHIP_Z: usize = 30;
pub const F_O_LAYOUT: usize = 48;
pub const F_O_KEY_C: usize = 52;
pub const F_O_KEY_B: usize = 53;
pub const F_O_CUST_C: usize = 54;
pub const F_O_CUST_B: usize = 55;
pub const F_O_DATE_C: usize = 62;
pub const F_O_DATE_B: usize = 63;
pub const F_O_SP_C: usize = 69;
pub const F_O_SP_B: usize = 70;
pub const F_O_IDX_C: usize = 71;
pub const F_O_IDX_B: usize = 72;
pub const F_O_IDX_KIND: usize = 73;
pub const F_CLUSTER: usize = 74;
// storage `li_okruns`: facts' 75 parts, then the lineitem l_orderkey run starts
pub const R_STARTS: usize = 75;
// storage `custpart` (customer parts first)
pub const C_LAYOUT: usize = 0;
pub const C_KEY_C: usize = 2;
pub const C_KEY_B: usize = 3;
pub const C_SEG_C: usize = 14;
pub const C_SEG_B: usize = 15;
pub const C_DICT_OFF: usize = 16;
pub const C_DICT_BYTES: usize = 17;
pub const C_IDX_KIND: usize = 20;

// ------------------------------------------------------------------------------------------------ the model

/// The parts this query reads, as sequences (`l_*` lineitem, `o_*` orders, `c_*` customer; `*_c` codes, `*_b` group
/// bases, `*_bs` block rows, `*_nb` groups, `l_map`/`o_map` stored row -> canonical row).
pub struct M {
    pub l_n: int,
    pub l_bs: int,
    pub l_nb: int,
    pub l_map: Seq<int>,
    pub l_key_c: Seq<u32>,
    pub l_key_b: Seq<i64>,
    pub l_price_c: Seq<u32>,
    pub l_price_b: Seq<i64>,
    pub l_disc_c: Seq<u8>,
    pub l_disc_b: Seq<i64>,
    pub l_ship_c: Seq<u16>,
    pub l_ship_b: Seq<i64>,
    pub l_ship_z: Seq<i64>,
    pub o_n: int,
    pub o_bs: int,
    pub o_nb: int,
    pub o_map: Seq<int>,
    pub o_key_c: Seq<u32>,
    pub o_key_b: Seq<i64>,
    pub o_cust_c: Seq<u32>,
    pub o_cust_b: Seq<i64>,
    pub o_date_c: Seq<u16>,
    pub o_date_b: Seq<i64>,
    pub o_sp_c: Seq<u8>,
    pub o_sp_b: Seq<i64>,
    pub o_ic: Seq<u32>,
    pub o_ib: Seq<u64>,
    pub o_kind: u64,
    pub cluster: u64,
    pub l_st: Seq<u32>,
    pub c_n: int,
    pub c_bs: int,
    pub c_nb: int,
    pub c_key_c: Seq<u32>,
    pub c_key_b: Seq<i64>,
    pub c_seg_c: Seq<u8>,
    pub c_seg_b: Seq<u64>,
    pub d_off: Seq<u64>,
    pub d_bytes: Seq<u8>,
    pub c_kind: u64,
}

/// The facts parts as storage `li_okruns` keeps them (its first 75 parts).
pub open spec fn fparts(sv: StoresView) -> Seq<PartView> {
    sv.li_okruns.subrange(0, 75)
}

/// The model of the parts of the storage uses (`li_okruns` for lineitem and orders, `custpart` for customer).
pub open spec fn model_of(sv: StoresView) -> M {
    let f = fparts(sv);
    let c = sv.custpart;
    let l_n = pv_u64(f[F_L_LAYOUT as int])[0] as int;
    let o_n = pv_u64(f[F_O_LAYOUT as int])[0] as int;
    M {
        l_n,
        l_bs: pv_u64(f[F_L_LAYOUT as int])[1] as int,
        l_nb: pv_i64(f[F_L_KEY_B as int]).len() as int,
        l_map: fi::lineitem_map(f.subrange(0, 48), l_n),
        l_key_c: pv_u32(f[F_L_KEY_C as int]),
        l_key_b: pv_i64(f[F_L_KEY_B as int]),
        l_price_c: pv_u32(f[F_L_PRICE_C as int]),
        l_price_b: pv_i64(f[F_L_PRICE_B as int]),
        l_disc_c: pv_u8(f[F_L_DISC_C as int]),
        l_disc_b: pv_i64(f[F_L_DISC_B as int]),
        l_ship_c: pv_u16(f[F_L_SHIP_C as int]),
        l_ship_b: pv_i64(f[F_L_SHIP_B as int]),
        l_ship_z: pv_i64(f[F_L_SHIP_Z as int]),
        o_n,
        o_bs: pv_u64(f[F_O_LAYOUT as int])[1] as int,
        o_nb: pv_i64(f[F_O_KEY_B as int]).len() as int,
        o_map: fi::orders_map(f.subrange(48, 74), o_n),
        o_key_c: pv_u32(f[F_O_KEY_C as int]),
        o_key_b: pv_i64(f[F_O_KEY_B as int]),
        o_cust_c: pv_u32(f[F_O_CUST_C as int]),
        o_cust_b: pv_i64(f[F_O_CUST_B as int]),
        o_date_c: pv_u16(f[F_O_DATE_C as int]),
        o_date_b: pv_i64(f[F_O_DATE_B as int]),
        o_sp_c: pv_u8(f[F_O_SP_C as int]),
        o_sp_b: pv_i64(f[F_O_SP_B as int]),
        o_ic: pv_u32(f[F_O_IDX_C as int]),
        o_ib: pv_u64(f[F_O_IDX_B as int]),
        o_kind: pv_u64(f[F_O_IDX_KIND as int])[0],
        cluster: pv_u64(f[F_CLUSTER as int])[0],
        l_st: pv_u32(sv.li_okruns[R_STARTS as int]),
        c_n: pv_u64(c[C_LAYOUT as int])[0] as int,
        c_bs: pv_u64(c[C_LAYOUT as int])[1] as int,
        c_nb: pv_i64(c[C_KEY_B as int]).len() as int,
        c_key_c: pv_u32(c[C_KEY_C as int]),
        c_key_b: pv_i64(c[C_KEY_B as int]),
        c_seg_c: pv_u8(c[C_SEG_C as int]),
        c_seg_b: pv_u64(c[C_SEG_B as int]),
        d_off: pv_u64(c[C_DICT_OFF as int]),
        d_bytes: pv_u8(c[C_DICT_BYTES as int]),
        c_kind: pv_u64(c[C_IDX_KIND as int])[0],
    }
}

// ------------------------------------------------------------------------------------------------ decoded values

pub open spec fn lkey(m: M, j: int) -> int { m.l_key_b[j / m.l_bs] as int + m.l_key_c[j] as int }
pub open spec fn lprice(m: M, j: int) -> int { m.l_price_b[j / m.l_bs] as int + m.l_price_c[j] as int }
pub open spec fn ldisc(m: M, j: int) -> int { m.l_disc_b[j / m.l_bs] as int + m.l_disc_c[j] as int }
pub open spec fn lship(m: M, j: int) -> int { m.l_ship_b[j / m.l_bs] as int + m.l_ship_c[j] as int }
pub open spec fn okey(m: M, q: int) -> int { m.o_key_b[q / m.o_bs] as int + m.o_key_c[q] as int }
pub open spec fn ocust(m: M, q: int) -> int { m.o_cust_b[q / m.o_bs] as int + m.o_cust_c[q] as int }
pub open spec fn odate(m: M, q: int) -> int { m.o_date_b[q / m.o_bs] as int + m.o_date_c[q] as int }
pub open spec fn osp(m: M, q: int) -> int { m.o_sp_b[q / m.o_bs] as int + m.o_sp_c[q] as int }
pub open spec fn ckey(m: M, c: int) -> int { m.c_key_b[c / m.c_bs] as int + m.c_key_c[c] as int }
/// Dictionary entry index of the customer's market segment.
pub open spec fn cseg(m: M, c: int) -> int { m.c_seg_b[c / m.c_bs] as int + m.c_seg_c[c] as int }
/// Number of entries of the market segment dictionary.
pub open spec fn dict_n(m: M) -> int { m.d_off.len() - 1 }
/// The market segment text of customer row `c`.
pub open spec fn segtext(m: M, c: int) -> Seq<u8> { ci::common::colfmt::text_of(m.d_off, m.d_bytes, cseg(m, c)) }
/// Per-row argument coefficient of `SUM(l_extendedprice * (1 - l_discount))` at scale 4.
pub open spec fn larg(m: M, j: int) -> int { lprice(m, j) * (100 - ldisc(m, j)) }

/// The stored orders position whose `o_orderkey` is `k` (the first one; unique under the primary key), or `o_n`.
pub open spec fn opos(m: M, k: int) -> int {
    if exists|q: int| 0 <= q < m.o_n && #[trigger] okey(m, q) == k {
        choose|q: int| 0 <= q < m.o_n && #[trigger] okey(m, q) == k
    } else {
        m.o_n
    }
}

/// The order position of lineitem row `j`.
pub open spec fn lpos(m: M, j: int) -> int { opos(m, lkey(m, j)) }

// ------------------------------------------------------------------------------------------------ facts

pub open spec fn in_i64(x: int) -> bool { i64::MIN <= x <= i64::MAX }

/// Layout of the frame-of-reference columns: block rows, row and group counts, part lengths.
pub open spec fn shapes_ok(m: M) -> bool {
    &&& 1 <= m.l_bs && 0 <= m.l_n && m.l_n + m.l_bs <= u64::MAX
    &&& m.l_nb * m.l_bs >= m.l_n && (m.l_nb > 0 ==> (m.l_nb - 1) * m.l_bs < m.l_n) && m.l_nb >= 0
    &&& m.l_key_c.len() == m.l_n && m.l_key_b.len() == m.l_nb
    &&& m.l_price_c.len() == m.l_n && m.l_price_b.len() == m.l_nb
    &&& m.l_disc_c.len() == m.l_n && m.l_disc_b.len() == m.l_nb
    &&& m.l_ship_c.len() == m.l_n && m.l_ship_b.len() == m.l_nb && m.l_ship_z.len() == m.l_nb
    &&& 1 <= m.o_bs && 0 <= m.o_n && m.o_n + m.o_bs <= u64::MAX
    &&& m.o_nb * m.o_bs >= m.o_n && (m.o_nb > 0 ==> (m.o_nb - 1) * m.o_bs < m.o_n) && m.o_nb >= 0
    &&& m.o_key_c.len() == m.o_n && m.o_key_b.len() == m.o_nb
    &&& m.o_cust_c.len() == m.o_n && m.o_cust_b.len() == m.o_nb
    &&& m.o_date_c.len() == m.o_n && m.o_date_b.len() == m.o_nb
    &&& m.o_sp_c.len() == m.o_n && m.o_sp_b.len() == m.o_nb
    &&& 1 <= m.c_bs && 0 <= m.c_n && m.c_n + m.c_bs <= u64::MAX
    &&& m.c_nb * m.c_bs >= m.c_n && (m.c_nb > 0 ==> (m.c_nb - 1) * m.c_bs < m.c_n) && m.c_nb >= 0
    &&& m.c_key_c.len() == m.c_n && m.c_key_b.len() == m.c_nb
    &&& m.c_seg_c.len() == m.c_n && m.c_seg_b.len() == m.c_nb
    &&& m.d_off.len() >= 1
}

/// Decoded values: machine ranges, the declared numeric precision, valid dates, zone maxima, dictionary indexes.
pub open spec fn values_ok(m: M) -> bool {
    &&& forall|j: int| 0 <= j < m.l_n ==> {
        &&& in_i64(#[trigger] lkey(m, j))
        &&& -pow10(15) < lprice(m, j) < pow10(15)
        &&& -pow10(15) < ldisc(m, j) < pow10(15)
        &&& in_i64(lship(m, j)) && lship(m, j) <= m.l_ship_z[j / m.l_bs]
    }
    &&& forall|q: int| 0 <= q < m.o_n ==> {
        &&& in_i64(#[trigger] okey(m, q)) && in_i64(ocust(m, q)) && in_i64(osp(m, q))
        &&& date_valid(odate(m, q)) && in_i64(odate(m, q))
    }
    &&& forall|c: int| 0 <= c < m.c_n ==> in_i64(#[trigger] ckey(m, c)) && 0 <= cseg(m, c) < dict_n(m)
    &&& ci::common::colfmt::text_parts_wf(m.d_off, m.d_bytes, dict_n(m))
    &&& ci::common::colfmt::dict_sorted(m.d_off, m.d_bytes, dict_n(m))
}

/// The declared primary keys at the part level, and the key indexes of orders and customer.
pub open spec fn keys_ok(m: M) -> bool {
    &&& forall|a: int, b: int| 0 <= a < m.o_n && 0 <= b < m.o_n && a != b ==> #[trigger] okey(m, a) != #[trigger] okey(m, b)
    &&& forall|a: int, b: int| 0 <= a < m.c_n && 0 <= b < m.c_n && a != b ==> #[trigger] ckey(m, a) != #[trigger] ckey(m, b)
    &&& fi::common::keyidx::keyidx_ok(m.o_key_c, m.o_key_b, m.o_ic, m.o_ib, m.o_bs, m.o_kind, m.o_n)
    &&& ci::common::keyidx::keyidx_ok(m.c_key_c, m.c_key_b, Seq::<u32>::empty(), Seq::<u64>::empty(), m.c_bs, m.c_kind, m.c_n)
}

/// With the cluster flag set, the order position of the stored lineitem rows never decreases.
pub open spec fn cluster_ok(m: M) -> bool {
    m.cluster == 1 ==> forall|j: int| 0 <= j < m.l_n - 1 ==> #[trigger] lpos(m, j) <= lpos(m, j + 1)
}

/// Run `k` of the l_orderkey run starts: rows `[l_st[k], l_st[k + 1])`, nonempty, one key, another key after it.
pub open spec fn run_ok(m: M, k: int) -> bool {
    let a = m.l_st[k] as int;
    let b = m.l_st[k + 1] as int;
    &&& a < b <= m.l_n
    &&& forall|s: int| a <= s < b ==> #[trigger] lkey(m, s) == lkey(m, a)
    &&& b < m.l_n ==> lkey(m, b) != lkey(m, b - 1)
}

/// The run starts of storage `li_okruns`: the first is row 0, every run is correct.
pub open spec fn runs_ok(m: M) -> bool {
    &&& m.l_st.len() >= 1
    &&& m.l_st[0] == 0
    &&& forall|k: int| 0 <= k < m.l_st.len() - 1 ==> #[trigger] run_ok(m, k)
}

/// Every fact of the model.
pub open spec fn model_ok(m: M) -> bool {
    &&& shapes_ok(m)
    &&& values_ok(m)
    &&& keys_ok(m)
    &&& cluster_ok(m)
    &&& runs_ok(m)
}

// ------------------------------------------------------------------------------------------------ rows of a database

/// Lineitem columns read: l_orderkey, l_extendedprice, l_discount, l_shipdate.
pub open spec fn lcols() -> Seq<nat> { seq![0nat, 5, 6, 10] }
/// Orders columns read: o_orderkey, o_custkey, o_orderdate, o_shippriority.
pub open spec fn ocols() -> Seq<nat> { seq![0nat, 1, 4, 7] }
/// Customer columns read: c_custkey, c_mktsegment.
pub open spec fn ccols() -> Seq<nat> { seq![0nat, 6] }

pub open spec fn lrow(m: M, j: int) -> Row {
    seq![Val::Int(lkey(m, j)), Val::Num { coeff: lprice(m, j), scale: 2 }, Val::Num { coeff: ldisc(m, j), scale: 2 }, Val::Date(lship(m, j))]
}

pub open spec fn orow(m: M, q: int) -> Row {
    seq![Val::Int(okey(m, q)), Val::Int(ocust(m, q)), Val::Date(odate(m, q)), Val::Int(osp(m, q))]
}

pub open spec fn crow(m: M, c: int) -> Row {
    seq![Val::Int(ckey(m, c)), Val::Text(segtext(m, c))]
}

/// The database's tables, read through the model: lineitem and orders through their row maps (bijections),
/// customer in canonical order.
pub open spec fn rel_ok(m: M, db: Database) -> bool {
    &&& db.tables.len() == 8
    &&& m.l_n == db.tables[0].len()
    &&& fi::common::colfmt::is_perm(m.l_map, m.l_n)
    &&& forall|j: int| 0 <= j < m.l_n ==> #[trigger] proj(db.tables[0][m.l_map[j]], lcols()) == lrow(m, j)
    &&& m.o_n == db.tables[1].len()
    &&& fi::common::colfmt::is_perm(m.o_map, m.o_n)
    &&& forall|q: int| 0 <= q < m.o_n ==> #[trigger] proj(db.tables[1][m.o_map[q]], ocols()) == orow(m, q)
    &&& m.c_n == db.tables[2].len()
    &&& forall|c: int| 0 <= c < m.c_n ==> #[trigger] proj(db.tables[2][c], ccols()) == crow(m, c)
}

} // verus!
