//! Part-level model of the columns Q18 reads. `M` is the view of the parts (storage `liruns`: the lineitem and orders
//! parts of `facts`, orders stored by order date and lineitem co-clustered with them, plus the runs of equal
//! l_orderkey, the l_quantity zone map and the run permutation by length; storage `custpart`: customer in canonical order). Values are decoded as frame-of-reference integers: `base[row / block] + code[row]` (numerics as
//! coefficients of scale 2, dates as days since 2000-01-01); c_name is plain text (offsets + bytes). The predicates
//! here (`shapes_ok`, `values_ok`, `keys_ok`, `cluster_ok`, `rel_ok`) are what every database bound to the parts
//! gives (`facts::lemma_model`); the kernels are proved against them, the SQL link (`sqllink`) relates them to the
//! statement's rows.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stores::StoresView;
use crate::spec::value::*;
use crate::spec::numeric::pow10;
use crate::spec::datetime::date_valid;
use crate::link::query::proj;
use crate::stores::liruns::interface as fi;
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

// storage `liruns` (the parts of `facts`: lineitem parts first, then orders at 48, then the cluster flag; then the runs)
pub const F_L_LAYOUT: usize = 0;
pub const F_L_KEY_C: usize = 4;
pub const F_L_KEY_B: usize = 5;
pub const F_L_QTY_C: usize = 12;
pub const F_L_QTY_B: usize = 13;
pub const F_O_LAYOUT: usize = 48;
pub const F_O_KEY_C: usize = 52;
pub const F_O_KEY_B: usize = 53;
pub const F_O_CUST_C: usize = 54;
pub const F_O_CUST_B: usize = 55;
pub const F_O_TP_C: usize = 60;
pub const F_O_TP_B: usize = 61;
pub const F_O_DATE_C: usize = 62;
pub const F_O_DATE_B: usize = 63;
pub const F_O_IDX_C: usize = 71;
pub const F_O_IDX_B: usize = 72;
pub const F_O_IDX_KIND: usize = 73;
pub const F_CLUSTER: usize = 74;
pub const F_R_META: usize = 75;
pub const F_R_LENS: usize = 76;
pub const F_R_STARTS: usize = 77;
pub const F_QZ: usize = 78;
pub const F_LG_META: usize = 79;
pub const F_LG_RUNS: usize = 80;
pub const F_LG_STARTS: usize = 81;
// storage `custpart` (customer parts first)
pub const C_LAYOUT: usize = 0;
pub const C_KEY_C: usize = 2;
pub const C_KEY_B: usize = 3;
pub const C_NAME_O: usize = 4;
pub const C_NAME_Y: usize = 5;
pub const C_IDX_KIND: usize = 20;

// ------------------------------------------------------------------------------------------------ the model

/// The parts this query reads, as sequences (`l_*` lineitem, `o_*` orders, `c_*` customer; `*_c` codes, `*_b` group
/// bases, `*_bs` block rows, `*_nb` groups, `l_map`/`o_map` stored row -> canonical row; `c_name_o`/`c_name_y` the
/// offsets and bytes of c_name).
pub struct M {
    pub l_n: int,
    pub l_bs: int,
    pub l_nb: int,
    pub l_map: Seq<int>,
    pub l_key_c: Seq<u32>,
    pub l_key_b: Seq<i64>,
    pub l_qty_c: Seq<u16>,
    pub l_qty_b: Seq<i64>,
    pub o_n: int,
    pub o_bs: int,
    pub o_nb: int,
    pub o_map: Seq<int>,
    pub o_key_c: Seq<u32>,
    pub o_key_b: Seq<i64>,
    pub o_cust_c: Seq<u32>,
    pub o_cust_b: Seq<i64>,
    pub o_tp_c: Seq<u32>,
    pub o_tp_b: Seq<i64>,
    pub o_date_c: Seq<u16>,
    pub o_date_b: Seq<i64>,
    pub o_ic: Seq<u32>,
    pub o_ib: Seq<u64>,
    pub o_kind: u64,
    pub cluster: u64,
    pub r_mode: u64,
    pub r_stride: int,
    pub r_lens: Seq<u8>,
    pub r_starts: Seq<u64>,
    pub qz: Seq<i64>,
    pub lg_mode: u64,
    pub lg_max: int,
    pub lg_n: int,
    pub lg_runs: Seq<u32>,
    pub lg_starts: Seq<u32>,
    pub c_n: int,
    pub c_bs: int,
    pub c_nb: int,
    pub c_key_c: Seq<u32>,
    pub c_key_b: Seq<i64>,
    pub c_name_o: Seq<u64>,
    pub c_name_y: Seq<u8>,
    pub c_kind: u64,
}

/// The model of the parts of both storage uses.
pub open spec fn model_of(sv: StoresView) -> M {
    let f = sv.liruns;
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
        l_qty_c: pv_u16(f[F_L_QTY_C as int]),
        l_qty_b: pv_i64(f[F_L_QTY_B as int]),
        o_n,
        o_bs: pv_u64(f[F_O_LAYOUT as int])[1] as int,
        o_nb: pv_i64(f[F_O_KEY_B as int]).len() as int,
        o_map: fi::orders_map(f.subrange(48, 74), o_n),
        o_key_c: pv_u32(f[F_O_KEY_C as int]),
        o_key_b: pv_i64(f[F_O_KEY_B as int]),
        o_cust_c: pv_u32(f[F_O_CUST_C as int]),
        o_cust_b: pv_i64(f[F_O_CUST_B as int]),
        o_tp_c: pv_u32(f[F_O_TP_C as int]),
        o_tp_b: pv_i64(f[F_O_TP_B as int]),
        o_date_c: pv_u16(f[F_O_DATE_C as int]),
        o_date_b: pv_i64(f[F_O_DATE_B as int]),
        o_ic: pv_u32(f[F_O_IDX_C as int]),
        o_ib: pv_u64(f[F_O_IDX_B as int]),
        o_kind: pv_u64(f[F_O_IDX_KIND as int])[0],
        cluster: pv_u64(f[F_CLUSTER as int])[0],
        r_mode: pv_u64(f[F_R_META as int])[0],
        r_stride: pv_u64(f[F_R_META as int])[1] as int,
        r_lens: pv_u8(f[F_R_LENS as int]),
        r_starts: pv_u64(f[F_R_STARTS as int]),
        qz: pv_i64(f[F_QZ as int]),
        lg_mode: pv_u64(f[F_LG_META as int])[0],
        lg_max: pv_u64(f[F_LG_META as int])[1] as int,
        lg_n: pv_u64(f[F_LG_META as int])[2] as int,
        lg_runs: pv_u32(f[F_LG_RUNS as int]),
        lg_starts: pv_u32(f[F_LG_STARTS as int]),
        c_n: pv_u64(c[C_LAYOUT as int])[0] as int,
        c_bs: pv_u64(c[C_LAYOUT as int])[1] as int,
        c_nb: pv_i64(c[C_KEY_B as int]).len() as int,
        c_key_c: pv_u32(c[C_KEY_C as int]),
        c_key_b: pv_i64(c[C_KEY_B as int]),
        c_name_o: pv_u64(c[C_NAME_O as int]),
        c_name_y: pv_u8(c[C_NAME_Y as int]),
        c_kind: pv_u64(c[C_IDX_KIND as int])[0],
    }
}

// ------------------------------------------------------------------------------------------------ decoded values

pub open spec fn lkey(m: M, j: int) -> int { m.l_key_b[j / m.l_bs] as int + m.l_key_c[j] as int }
/// l_quantity coefficient (scale 2).
pub open spec fn lqty(m: M, j: int) -> int { m.l_qty_b[j / m.l_bs] as int + m.l_qty_c[j] as int }
pub open spec fn okey(m: M, q: int) -> int { m.o_key_b[q / m.o_bs] as int + m.o_key_c[q] as int }
pub open spec fn ocust(m: M, q: int) -> int { m.o_cust_b[q / m.o_bs] as int + m.o_cust_c[q] as int }
/// o_totalprice coefficient (scale 2).
pub open spec fn otp(m: M, q: int) -> int { m.o_tp_b[q / m.o_bs] as int + m.o_tp_c[q] as int }
pub open spec fn odate(m: M, q: int) -> int { m.o_date_b[q / m.o_bs] as int + m.o_date_c[q] as int }
pub open spec fn ckey(m: M, c: int) -> int { m.c_key_b[c / m.c_bs] as int + m.c_key_c[c] as int }
/// The c_name text of customer row `c`.
pub open spec fn cname(m: M, c: int) -> Seq<u8> { ci::common::colfmt::text_of(m.c_name_o, m.c_name_y, c) }

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
    &&& m.l_qty_c.len() == m.l_n && m.l_qty_b.len() == m.l_nb
    &&& 1 <= m.o_bs && 0 <= m.o_n && m.o_n + m.o_bs <= u64::MAX
    &&& m.o_nb * m.o_bs >= m.o_n && (m.o_nb > 0 ==> (m.o_nb - 1) * m.o_bs < m.o_n) && m.o_nb >= 0
    &&& m.o_key_c.len() == m.o_n && m.o_key_b.len() == m.o_nb
    &&& m.o_cust_c.len() == m.o_n && m.o_cust_b.len() == m.o_nb
    &&& m.o_tp_c.len() == m.o_n && m.o_tp_b.len() == m.o_nb
    &&& m.o_date_c.len() == m.o_n && m.o_date_b.len() == m.o_nb
    &&& 1 <= m.c_bs && 0 <= m.c_n && m.c_n + m.c_bs <= u64::MAX
    &&& m.c_nb * m.c_bs >= m.c_n && (m.c_nb > 0 ==> (m.c_nb - 1) * m.c_bs < m.c_n) && m.c_nb >= 0
    &&& m.c_key_c.len() == m.c_n && m.c_key_b.len() == m.c_nb
}

/// Decoded values: machine ranges, the declared numeric precision, valid dates, c_name byte ranges.
pub open spec fn values_ok(m: M) -> bool {
    &&& forall|j: int| 0 <= j < m.l_n ==> in_i64(#[trigger] lkey(m, j)) && -pow10(15) < lqty(m, j) < pow10(15)
    &&& forall|q: int| 0 <= q < m.o_n ==> {
        &&& in_i64(#[trigger] okey(m, q)) && in_i64(ocust(m, q))
        &&& -pow10(15) < otp(m, q) < pow10(15)
        &&& date_valid(odate(m, q)) && in_i64(odate(m, q))
    }
    &&& forall|c: int| 0 <= c < m.c_n ==> in_i64(#[trigger] ckey(m, c))
    &&& ci::common::colfmt::text_parts_wf(m.c_name_o, m.c_name_y, m.c_n)
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

/// Start row of run `r` (prefix sums of the run lengths).
pub open spec fn rs(m: M, r: int) -> int { fi::rstart(m.r_lens, r) }

/// Number of runs.
pub open spec fn nruns(m: M) -> int { m.r_lens.len() as int }

/// Every row of run `r` has the key of its first row.
pub open spec fn run_same_m(m: M, r: int) -> bool {
    forall|j: int| rs(m, r) <= j < rs(m, r + 1) ==> #[trigger] lkey(m, j) == lkey(m, rs(m, r))
}

/// The rows on both sides of the start of run `r` have different keys.
pub open spec fn run_cut_m(m: M, r: int) -> bool {
    lkey(m, rs(m, r) - 1) != lkey(m, rs(m, r))
}

/// The runs (mode 1): maximal runs of equal l_orderkey covering the lineitem rows, sampled starts, and the
/// l_quantity zone map. Opaque: revealed where a run, a sample or the zone map is read.
#[verifier::opaque]
pub open spec fn runs_ok(m: M) -> bool {
    m.r_mode == 1 ==> {
        &&& m.r_stride >= 1
        &&& rs(m, nruns(m)) == m.l_n
        &&& forall|r: int| 0 <= r < nruns(m) ==> #[trigger] m.r_lens[r] >= 1 && run_same_m(m, r)
        &&& forall|r: int| 0 < r < nruns(m) ==> #[trigger] run_cut_m(m, r)
        &&& forall|b: int| 0 <= b < m.r_starts.len() ==> #[trigger] fi::start_ok(m.r_lens, m.r_starts, m.r_stride, b)
        &&& m.qz.len() == m.l_nb
        &&& forall|j: int| 0 <= j < m.l_n ==> #[trigger] lqty(m, j) <= m.qz[j / m.l_bs]
    }
}

/// The run permutation by length (mode 1): no run is longer than `lg_max`, and the first `lg_n` entries are exactly
/// the runs of length `lg_max`, ascending, with their start rows. Opaque: read through the lemmas of `scan`.
#[verifier::opaque]
pub open spec fn long_ok(m: M) -> bool {
    m.lg_mode == 1 ==> {
        &&& m.r_mode == 1
        &&& m.lg_n <= m.lg_runs.len() && m.lg_n <= m.lg_starts.len()
        &&& forall|r: int| 0 <= r < nruns(m) ==> #[trigger] m.r_lens[r] <= m.lg_max
        &&& forall|i: int| 0 <= i < m.lg_n ==> #[trigger] fi::long_at(m.r_lens, m.lg_runs, m.lg_starts, m.lg_max, i)
        &&& forall|a: int, b: int| 0 <= a < b < m.lg_n ==> #[trigger] m.lg_runs[a] < #[trigger] m.lg_runs[b]
        &&& forall|r: int| 0 <= r < nruns(m) && m.r_lens[r] == m.lg_max ==> #[trigger] fi::long_listed(m.lg_runs, m.lg_n, r)
    }
}

/// Every fact of the model.
pub open spec fn model_ok(m: M) -> bool {
    &&& shapes_ok(m)
    &&& values_ok(m)
    &&& keys_ok(m)
    &&& cluster_ok(m)
}

// ------------------------------------------------------------------------------------------------ rows of a database

/// Lineitem columns read: l_orderkey, l_quantity.
pub open spec fn lcols() -> Seq<nat> { seq![0nat, 4] }
/// Orders columns read: o_orderkey, o_custkey, o_totalprice, o_orderdate.
pub open spec fn ocols() -> Seq<nat> { seq![0nat, 1, 3, 4] }
/// Customer columns read: c_custkey, c_name.
pub open spec fn ccols() -> Seq<nat> { seq![0nat, 1] }

pub open spec fn lrow(m: M, j: int) -> Row {
    seq![Val::Int(lkey(m, j)), Val::Num { coeff: lqty(m, j), scale: 2 }]
}

pub open spec fn orow(m: M, q: int) -> Row {
    seq![Val::Int(okey(m, q)), Val::Int(ocust(m, q)), Val::Num { coeff: otp(m, q), scale: 2 }, Val::Date(odate(m, q))]
}

pub open spec fn crow(m: M, c: int) -> Row {
    seq![Val::Int(ckey(m, c)), Val::Text(cname(m, c))]
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
