//! Part-level model of the columns Q10 reads. `M` is the view of the parts of three storage uses: `facts`
//! (lineitem and orders, orders stored by order date with zone maps, lineitem co-clustered with them, each through
//! a row map stored row -> canonical row), `custpart` (customer in canonical order) and `suppliers` (nation in
//! canonical order). Integers, numerics (coefficients of scale 2) and dates (days since 2000-01-01) are decoded as
//! frame-of-reference values `base[row / block] + code[row]`; text as `text_of(offsets, bytes, row)`; l_returnflag
//! as a sorted dictionary entry. The predicates here (`shapes_ok`, `values_ok`, `keys_ok`, `cluster_ok`, `rel_ok`)
//! are what every database bound to the parts gives (`facts::lemma_model`); the kernels are proved against them
//! and the SQL link relates them to the statement's rows.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stores::StoresView;
use crate::spec::value::*;
use crate::spec::numeric::pow10;
use crate::spec::datetime::date_valid;
use crate::link::query::proj;
use crate::stores::facts::interface as fi;
use crate::stores::facts::interface::common::colfmt as ff;
use crate::stores::custpart::interface::common::colfmt as cf;
use crate::stores::suppliers::interface::common::colfmt as sf;

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

// storage `facts`: lineitem parts at 0, orders parts at 48, the cluster flag at 74
pub const F_L_LAYOUT: usize = 0;
pub const F_L_KEY_C: usize = 4;
pub const F_L_KEY_B: usize = 5;
pub const F_L_PRICE_C: usize = 14;
pub const F_L_PRICE_B: usize = 15;
pub const F_L_DISC_C: usize = 16;
pub const F_L_DISC_B: usize = 17;
pub const F_L_RF_C: usize = 20;
pub const F_L_RF_B: usize = 21;
pub const F_L_RF_OFF: usize = 22;
pub const F_L_RF_BYTES: usize = 23;
pub const F_O_LAYOUT: usize = 48;
pub const F_O_KEY_C: usize = 52;
pub const F_O_KEY_B: usize = 53;
pub const F_O_CUST_C: usize = 54;
pub const F_O_CUST_B: usize = 55;
pub const F_O_DATE_C: usize = 62;
pub const F_O_DATE_B: usize = 63;
pub const F_O_DATE_Z: usize = 64;
pub const F_O_IDX_C: usize = 71;
pub const F_O_IDX_B: usize = 72;
pub const F_O_IDX_KIND: usize = 73;
pub const F_CLUSTER: usize = 74;
// storage `custpart`: customer parts at 0
pub const C_LAYOUT: usize = 0;
pub const C_KEY_C: usize = 2;
pub const C_KEY_B: usize = 3;
pub const C_NAME_O: usize = 4;
pub const C_NAME_Y: usize = 5;
pub const C_ADDR_O: usize = 6;
pub const C_ADDR_Y: usize = 7;
pub const C_NAT_C: usize = 8;
pub const C_NAT_B: usize = 9;
pub const C_PHONE_O: usize = 10;
pub const C_PHONE_Y: usize = 11;
pub const C_BAL_C: usize = 12;
pub const C_BAL_B: usize = 13;
pub const C_CMT_O: usize = 18;
pub const C_CMT_Y: usize = 19;
pub const C_IDX_KIND: usize = 20;
// storage `suppliers`: nation parts at 30
pub const N_LAYOUT: usize = 30;
pub const N_KEY_C: usize = 32;
pub const N_KEY_B: usize = 33;
pub const N_NAME_O: usize = 34;
pub const N_NAME_Y: usize = 35;

// ------------------------------------------------------------------------------------------------ the model

/// The parts this query reads, as sequences (`l_*` lineitem, `o_*` orders, `c_*` customer, `n_*` nation; `*_c`
/// codes, `*_b` group bases, `*_bs` block rows, `*_nb` groups, `*_o`/`*_y` text offsets/bytes, `l_map`/`o_map`
/// stored row -> canonical row, `rf_*` the l_returnflag dictionary).
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
    pub l_rf_c: Seq<u8>,
    pub l_rf_b: Seq<u64>,
    pub rf_off: Seq<u64>,
    pub rf_bytes: Seq<u8>,
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
    pub o_date_z: Seq<i64>,
    pub o_ic: Seq<u32>,
    pub o_ib: Seq<u64>,
    pub o_kind: u64,
    pub cluster: u64,
    pub c_n: int,
    pub c_bs: int,
    pub c_nb: int,
    pub c_key_c: Seq<u32>,
    pub c_key_b: Seq<i64>,
    pub c_name_o: Seq<u64>,
    pub c_name_y: Seq<u8>,
    pub c_addr_o: Seq<u64>,
    pub c_addr_y: Seq<u8>,
    pub c_nat_c: Seq<u8>,
    pub c_nat_b: Seq<i64>,
    pub c_phone_o: Seq<u64>,
    pub c_phone_y: Seq<u8>,
    pub c_bal_c: Seq<u32>,
    pub c_bal_b: Seq<i64>,
    pub c_cmt_o: Seq<u64>,
    pub c_cmt_y: Seq<u8>,
    pub c_kind: u64,
    pub n_n: int,
    pub n_bs: int,
    pub n_nb: int,
    pub n_key_c: Seq<u8>,
    pub n_key_b: Seq<i64>,
    pub n_name_o: Seq<u64>,
    pub n_name_y: Seq<u8>,
}

/// The model of the parts of the three storage uses.
pub open spec fn model_of(sv: StoresView) -> M {
    let f = sv.facts;
    let c = sv.custpart;
    let s = sv.suppliers;
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
        l_rf_c: pv_u8(f[F_L_RF_C as int]),
        l_rf_b: pv_u64(f[F_L_RF_B as int]),
        rf_off: pv_u64(f[F_L_RF_OFF as int]),
        rf_bytes: pv_u8(f[F_L_RF_BYTES as int]),
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
        o_date_z: pv_i64(f[F_O_DATE_Z as int]),
        o_ic: pv_u32(f[F_O_IDX_C as int]),
        o_ib: pv_u64(f[F_O_IDX_B as int]),
        o_kind: pv_u64(f[F_O_IDX_KIND as int])[0],
        cluster: pv_u64(f[F_CLUSTER as int])[0],
        c_n: pv_u64(c[C_LAYOUT as int])[0] as int,
        c_bs: pv_u64(c[C_LAYOUT as int])[1] as int,
        c_nb: pv_i64(c[C_KEY_B as int]).len() as int,
        c_key_c: pv_u32(c[C_KEY_C as int]),
        c_key_b: pv_i64(c[C_KEY_B as int]),
        c_name_o: pv_u64(c[C_NAME_O as int]),
        c_name_y: pv_u8(c[C_NAME_Y as int]),
        c_addr_o: pv_u64(c[C_ADDR_O as int]),
        c_addr_y: pv_u8(c[C_ADDR_Y as int]),
        c_nat_c: pv_u8(c[C_NAT_C as int]),
        c_nat_b: pv_i64(c[C_NAT_B as int]),
        c_phone_o: pv_u64(c[C_PHONE_O as int]),
        c_phone_y: pv_u8(c[C_PHONE_Y as int]),
        c_bal_c: pv_u32(c[C_BAL_C as int]),
        c_bal_b: pv_i64(c[C_BAL_B as int]),
        c_cmt_o: pv_u64(c[C_CMT_O as int]),
        c_cmt_y: pv_u8(c[C_CMT_Y as int]),
        c_kind: pv_u64(c[C_IDX_KIND as int])[0],
        n_n: pv_u64(s[N_LAYOUT as int])[0] as int,
        n_bs: pv_u64(s[N_LAYOUT as int])[1] as int,
        n_nb: pv_i64(s[N_KEY_B as int]).len() as int,
        n_key_c: pv_u8(s[N_KEY_C as int]),
        n_key_b: pv_i64(s[N_KEY_B as int]),
        n_name_o: pv_u64(s[N_NAME_O as int]),
        n_name_y: pv_u8(s[N_NAME_Y as int]),
    }
}

// ------------------------------------------------------------------------------------------------ decoded values

pub open spec fn lkey(m: M, j: int) -> int { m.l_key_b[j / m.l_bs] as int + m.l_key_c[j] as int }
pub open spec fn lprice(m: M, j: int) -> int { m.l_price_b[j / m.l_bs] as int + m.l_price_c[j] as int }
pub open spec fn ldisc(m: M, j: int) -> int { m.l_disc_b[j / m.l_bs] as int + m.l_disc_c[j] as int }
/// Dictionary entry index of l_returnflag of lineitem row `j`.
pub open spec fn lrf(m: M, j: int) -> int { m.l_rf_b[j / m.l_bs] as int + m.l_rf_c[j] as int }
/// Number of entries of the l_returnflag dictionary.
pub open spec fn rf_n(m: M) -> int { m.rf_off.len() - 1 }
/// The l_returnflag text of lineitem row `j`.
pub open spec fn lflag(m: M, j: int) -> Seq<u8> { ff::text_of(m.rf_off, m.rf_bytes, lrf(m, j)) }
pub open spec fn okey(m: M, q: int) -> int { m.o_key_b[q / m.o_bs] as int + m.o_key_c[q] as int }
pub open spec fn ocust(m: M, q: int) -> int { m.o_cust_b[q / m.o_bs] as int + m.o_cust_c[q] as int }
pub open spec fn odate(m: M, q: int) -> int { m.o_date_b[q / m.o_bs] as int + m.o_date_c[q] as int }
pub open spec fn ckey(m: M, c: int) -> int { m.c_key_b[c / m.c_bs] as int + m.c_key_c[c] as int }
pub open spec fn cnat(m: M, c: int) -> int { m.c_nat_b[c / m.c_bs] as int + m.c_nat_c[c] as int }
pub open spec fn cbal(m: M, c: int) -> int { m.c_bal_b[c / m.c_bs] as int + m.c_bal_c[c] as int }
pub open spec fn cname(m: M, c: int) -> Seq<u8> { cf::text_of(m.c_name_o, m.c_name_y, c) }
pub open spec fn caddr(m: M, c: int) -> Seq<u8> { cf::text_of(m.c_addr_o, m.c_addr_y, c) }
pub open spec fn cphone(m: M, c: int) -> Seq<u8> { cf::text_of(m.c_phone_o, m.c_phone_y, c) }
pub open spec fn ccmt(m: M, c: int) -> Seq<u8> { cf::text_of(m.c_cmt_o, m.c_cmt_y, c) }
pub open spec fn nkey(m: M, n: int) -> int { m.n_key_b[n / m.n_bs] as int + m.n_key_c[n] as int }
pub open spec fn nname(m: M, n: int) -> Seq<u8> { sf::text_of(m.n_name_o, m.n_name_y, n) }
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

/// The customer row whose `c_custkey` is `k` (unique under the primary key), or `c_n`.
pub open spec fn cpos(m: M, k: int) -> int {
    if exists|c: int| 0 <= c < m.c_n && #[trigger] ckey(m, c) == k {
        choose|c: int| 0 <= c < m.c_n && #[trigger] ckey(m, c) == k
    } else {
        m.c_n
    }
}

/// The nation row whose `n_nationkey` is `k` (unique under the primary key), or `n_n`.
pub open spec fn npos(m: M, k: int) -> int {
    if exists|n: int| 0 <= n < m.n_n && #[trigger] nkey(m, n) == k {
        choose|n: int| 0 <= n < m.n_n && #[trigger] nkey(m, n) == k
    } else {
        m.n_n
    }
}

// ------------------------------------------------------------------------------------------------ facts

pub open spec fn in_i64(x: int) -> bool { i64::MIN <= x <= i64::MAX }

/// Uniform block layout of a table of `n` rows in blocks of `bs` rows, `nb` blocks.
pub open spec fn blocks_ok(n: int, bs: int, nb: int) -> bool {
    &&& 1 <= bs && 0 <= n && n + bs <= u64::MAX
    &&& nb * bs >= n && (nb > 0 ==> (nb - 1) * bs < n) && nb >= 0
}

/// Layout of the frame-of-reference columns: block rows, row and group counts, part lengths.
pub open spec fn shapes_ok(m: M) -> bool {
    &&& blocks_ok(m.l_n, m.l_bs, m.l_nb)
    &&& m.l_key_c.len() == m.l_n && m.l_key_b.len() == m.l_nb
    &&& m.l_price_c.len() == m.l_n && m.l_price_b.len() == m.l_nb
    &&& m.l_disc_c.len() == m.l_n && m.l_disc_b.len() == m.l_nb
    &&& m.l_rf_c.len() == m.l_n && m.l_rf_b.len() == m.l_nb
    &&& m.rf_off.len() >= 1
    &&& blocks_ok(m.o_n, m.o_bs, m.o_nb)
    &&& m.o_key_c.len() == m.o_n && m.o_key_b.len() == m.o_nb
    &&& m.o_cust_c.len() == m.o_n && m.o_cust_b.len() == m.o_nb
    &&& m.o_date_c.len() == m.o_n && m.o_date_b.len() == m.o_nb && m.o_date_z.len() == m.o_nb
    &&& blocks_ok(m.c_n, m.c_bs, m.c_nb)
    &&& m.c_key_c.len() == m.c_n && m.c_key_b.len() == m.c_nb
    &&& m.c_nat_c.len() == m.c_n && m.c_nat_b.len() == m.c_nb
    &&& m.c_bal_c.len() == m.c_n && m.c_bal_b.len() == m.c_nb
    &&& blocks_ok(m.n_n, m.n_bs, m.n_nb)
    &&& m.n_key_c.len() == m.n_n && m.n_key_b.len() == m.n_nb
}

/// Decoded values: machine ranges, the declared numeric precision, valid dates, zone maxima, text parts and the
/// sorted l_returnflag dictionary.
pub open spec fn values_ok(m: M) -> bool {
    &&& forall|j: int| 0 <= j < m.l_n ==> {
        &&& in_i64(#[trigger] lkey(m, j))
        &&& -pow10(15) < lprice(m, j) < pow10(15)
        &&& -pow10(15) < ldisc(m, j) < pow10(15)
        &&& 0 <= lrf(m, j) < rf_n(m)
    }
    &&& ff::text_parts_wf(m.rf_off, m.rf_bytes, rf_n(m))
    &&& ff::dict_sorted(m.rf_off, m.rf_bytes, rf_n(m))
    &&& forall|q: int| 0 <= q < m.o_n ==> {
        &&& in_i64(#[trigger] okey(m, q)) && in_i64(ocust(m, q))
        &&& date_valid(odate(m, q)) && in_i64(odate(m, q))
        &&& odate(m, q) <= m.o_date_z[q / m.o_bs]
    }
    &&& forall|c: int| 0 <= c < m.c_n ==> {
        &&& in_i64(#[trigger] ckey(m, c)) && in_i64(cnat(m, c))
        &&& -pow10(15) < cbal(m, c) < pow10(15)
    }
    &&& cf::text_parts_wf(m.c_name_o, m.c_name_y, m.c_n)
    &&& cf::text_parts_wf(m.c_addr_o, m.c_addr_y, m.c_n)
    &&& cf::text_parts_wf(m.c_phone_o, m.c_phone_y, m.c_n)
    &&& cf::text_parts_wf(m.c_cmt_o, m.c_cmt_y, m.c_n)
    &&& forall|n: int| 0 <= n < m.n_n ==> in_i64(#[trigger] nkey(m, n))
    &&& sf::text_parts_wf(m.n_name_o, m.n_name_y, m.n_n)
}

/// The declared primary keys at the part level, and the key indexes of orders and customer.
pub open spec fn keys_ok(m: M) -> bool {
    &&& forall|a: int, b: int| 0 <= a < m.o_n && 0 <= b < m.o_n && a != b ==> #[trigger] okey(m, a) != #[trigger] okey(m, b)
    &&& forall|a: int, b: int| 0 <= a < m.c_n && 0 <= b < m.c_n && a != b ==> #[trigger] ckey(m, a) != #[trigger] ckey(m, b)
    &&& forall|a: int, b: int| 0 <= a < m.n_n && 0 <= b < m.n_n && a != b ==> #[trigger] nkey(m, a) != #[trigger] nkey(m, b)
    &&& fi::common::keyidx::keyidx_ok(m.o_key_c, m.o_key_b, m.o_ic, m.o_ib, m.o_bs, m.o_kind, m.o_n)
    &&& crate::stores::custpart::interface::common::keyidx::keyidx_ok(m.c_key_c, m.c_key_b, Seq::<u32>::empty(),
            Seq::<u64>::empty(), m.c_bs, m.c_kind, m.c_n)
}

/// With the cluster flag set, the order position of the stored lineitem rows never decreases.
pub open spec fn cluster_ok(m: M) -> bool {
    m.cluster == 1 ==> forall|j: int| 0 <= j < m.l_n - 1 ==> #[trigger] lpos(m, j) <= lpos(m, j + 1)
}

/// Every fact of the model.
pub open spec fn model_ok(m: M) -> bool {
    &&& shapes_ok(m)
    &&& values_ok(m)
    &&& keys_ok(m)
    &&& cluster_ok(m)
}

// ------------------------------------------------------------------------------------------------ rows of a database

/// Lineitem columns read: l_orderkey, l_extendedprice, l_discount, l_returnflag.
pub open spec fn lcols() -> Seq<nat> { seq![0nat, 5, 6, 8] }
/// Orders columns read: o_orderkey, o_custkey, o_orderdate.
pub open spec fn ocols() -> Seq<nat> { seq![0nat, 1, 4] }
/// Customer columns read: c_custkey, c_name, c_address, c_nationkey, c_phone, c_acctbal, c_comment.
pub open spec fn ccols() -> Seq<nat> { seq![0nat, 1, 2, 3, 4, 5, 7] }
/// Nation columns read: n_nationkey, n_name.
pub open spec fn ncols() -> Seq<nat> { seq![0nat, 1] }

pub open spec fn lrow(m: M, j: int) -> Row {
    seq![Val::Int(lkey(m, j)), Val::Num { coeff: lprice(m, j), scale: 2 }, Val::Num { coeff: ldisc(m, j), scale: 2 },
        Val::Text(lflag(m, j))]
}

pub open spec fn orow(m: M, q: int) -> Row {
    seq![Val::Int(okey(m, q)), Val::Int(ocust(m, q)), Val::Date(odate(m, q))]
}

pub open spec fn crow(m: M, c: int) -> Row {
    seq![Val::Int(ckey(m, c)), Val::Text(cname(m, c)), Val::Text(caddr(m, c)), Val::Int(cnat(m, c)),
        Val::Text(cphone(m, c)), Val::Num { coeff: cbal(m, c), scale: 2 }, Val::Text(ccmt(m, c))]
}

pub open spec fn nrow(m: M, n: int) -> Row {
    seq![Val::Int(nkey(m, n)), Val::Text(nname(m, n))]
}

/// The database's tables, read through the model: lineitem and orders through their row maps (bijections),
/// customer and nation in canonical order.
pub open spec fn rel_ok(m: M, db: Database) -> bool {
    &&& db.tables.len() == 8
    &&& m.l_n == db.tables[0].len()
    &&& ff::is_perm(m.l_map, m.l_n)
    &&& forall|j: int| 0 <= j < m.l_n ==> #[trigger] proj(db.tables[0][m.l_map[j]], lcols()) == lrow(m, j)
    &&& m.o_n == db.tables[1].len()
    &&& ff::is_perm(m.o_map, m.o_n)
    &&& forall|q: int| 0 <= q < m.o_n ==> #[trigger] proj(db.tables[1][m.o_map[q]], ocols()) == orow(m, q)
    &&& m.c_n == db.tables[2].len()
    &&& forall|c: int| 0 <= c < m.c_n ==> #[trigger] proj(db.tables[2][c], ccols()) == crow(m, c)
    &&& m.n_n == db.tables[6].len()
    &&& forall|n: int| 0 <= n < m.n_n ==> #[trigger] proj(db.tables[6][n], ncols()) == nrow(m, n)
}

} // verus!
