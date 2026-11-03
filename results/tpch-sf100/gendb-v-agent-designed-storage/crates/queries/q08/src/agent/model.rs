//! Column model of the Q8 scan: the decoded columns a scan task reads (frame-of-reference codes plus one base per
//! group of `bs_*` rows), and the scan's meaning per stored lineitem row (`lc`): its contribution (year, volume,
//! nation match) or none.
//!
//! - lineitem (storage `facts`, `n_l` stored rows): l_orderkey `lk`, l_partkey `lp`, l_suppkey `ls`,
//!   l_extendedprice `le`, l_discount `ld` (coefficients of scale 2);
//! - orders (storage `facts`, `n_o` stored rows, with a key index on o_orderkey): o_orderkey `okey`, o_custkey `oc`,
//!   o_orderdate `od` (days since 2000-01-01);
//! - customer and supplier (`custpart`, `suppliers`; key lookups `cfind` / `sfind`): c_custkey `ck`, c_nationkey `cn`,
//!   s_suppkey `sk`, s_nationkey `sn`;
//! - the part filter `pm(v)`: some part row has key `v` and type `$3` (a predicate; the scan reads it from bitmaps);
//! - nation statuses (`NStat`): per nation row its key, whether its region is named `$2` and whether its name is `$1`.
//!
//! `lc(m, j)` follows the joins: part filter, the order of the line (`rpos`: the first stored orders row with the
//! key), the order date window, the customer and its nation's region, the supplier and its nation.
use vstd::prelude::*;
use crate::spec::value::*;
use super::sql::year_of;
use super::join::LHit;

verus! {

/// Column slices of one scan (whole parts, requested on the calling thread).
pub struct Cols {
    pub n_l: usize,
    pub bs_l: usize,
    pub lk_c: &'static [u32],
    pub lk_b: &'static [i64],
    pub lp_c: &'static [u32],
    pub lp_b: &'static [i64],
    pub ls_c: &'static [u32],
    pub ls_b: &'static [i64],
    pub le_c: &'static [u32],
    pub le_b: &'static [i64],
    pub ld_c: &'static [u8],
    pub ld_b: &'static [i64],
    pub n_o: usize,
    pub bs_o: usize,
    pub ok_c: &'static [u32],
    pub ok_b: &'static [i64],
    pub oc_c: &'static [u32],
    pub oc_b: &'static [i64],
    pub od_c: &'static [u16],
    pub od_b: &'static [i64],
    pub oi_c: &'static [u32],
    pub oi_b: &'static [u64],
    pub oi_kind: u64,
    pub n_c: usize,
    pub bs_c: usize,
    pub ck_c: &'static [u32],
    pub ck_b: &'static [i64],
    pub cn_c: &'static [u8],
    pub cn_b: &'static [i64],
    pub c_kind: u64,
    pub c_first: i64,
    pub n_s: usize,
    pub bs_s: usize,
    pub sk_c: &'static [u32],
    pub sk_b: &'static [i64],
    pub sn_c: &'static [u8],
    pub sn_b: &'static [i64],
    pub s_kind: u64,
    pub s_first: i64,
    /// The order date window `[lo, hi]` (days) and the first day of 1996.
    pub lo: i64,
    pub hi: i64,
    pub d96: i64,
    /// Empty index slices (the customer and supplier key lookups take none).
    pub e32: &'static [u32],
    pub e64: &'static [u64],
}

impl Copy for Cols {}

impl Clone for Cols {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

// ------------------------------------------------------------------------------------------------ decoded columns

pub open spec fn lk(m: Cols, j: int) -> int { m.lk_b@[j / m.bs_l as int] + m.lk_c@[j] }
pub open spec fn lp(m: Cols, j: int) -> int { m.lp_b@[j / m.bs_l as int] + m.lp_c@[j] }
pub open spec fn ls(m: Cols, j: int) -> int { m.ls_b@[j / m.bs_l as int] + m.ls_c@[j] }
pub open spec fn le(m: Cols, j: int) -> int { m.le_b@[j / m.bs_l as int] + m.le_c@[j] }
pub open spec fn ld(m: Cols, j: int) -> int { m.ld_b@[j / m.bs_l as int] + m.ld_c@[j] }
pub open spec fn okey(m: Cols, p: int) -> int { m.ok_b@[p / m.bs_o as int] + m.ok_c@[p] }
pub open spec fn oc(m: Cols, p: int) -> int { m.oc_b@[p / m.bs_o as int] + m.oc_c@[p] }
pub open spec fn od(m: Cols, p: int) -> int { m.od_b@[p / m.bs_o as int] + m.od_c@[p] }
pub open spec fn ck(m: Cols, i: int) -> int { m.ck_b@[i / m.bs_c as int] + m.ck_c@[i] }
pub open spec fn cn(m: Cols, i: int) -> int { m.cn_b@[i / m.bs_c as int] + m.cn_c@[i] }
pub open spec fn sk(m: Cols, i: int) -> int { m.sk_b@[i / m.bs_s as int] + m.sk_c@[i] }
pub open spec fn sn(m: Cols, i: int) -> int { m.sn_b@[i / m.bs_s as int] + m.sn_c@[i] }

pub open spec fn in_i64(x: int) -> bool {
    i64::MIN <= x <= i64::MAX
}

/// `numeric(15,2)` coefficients: `|c| < 10^15`.
pub open spec fn coeff15(x: int) -> bool {
    -1_000_000_000_000_000 < x < 1_000_000_000_000_000
}

/// Shapes of the slices, decoded values in `i64`, keys distinct where the scan looks rows up by key.
pub open spec fn cols_ok(m: Cols) -> bool {
    &&& m.bs_l >= 1 && m.bs_o >= 1 && m.bs_c >= 1 && m.bs_s >= 1
    &&& m.lk_c@.len() == m.n_l && m.lp_c@.len() == m.n_l && m.ls_c@.len() == m.n_l
    &&& m.le_c@.len() == m.n_l && m.ld_c@.len() == m.n_l
    &&& m.lp_b@.len() == m.lk_b@.len() && m.ls_b@.len() == m.lk_b@.len()
    &&& m.le_b@.len() == m.lk_b@.len() && m.ld_b@.len() == m.lk_b@.len()
    &&& m.lk_b@.len() * m.bs_l >= m.n_l
    &&& m.ok_c@.len() == m.n_o && m.oc_c@.len() == m.n_o && m.od_c@.len() == m.n_o
    &&& m.oc_b@.len() == m.ok_b@.len() && m.od_b@.len() == m.ok_b@.len()
    &&& m.ok_b@.len() * m.bs_o >= m.n_o
    &&& m.ck_c@.len() == m.n_c && m.cn_c@.len() == m.n_c && m.cn_b@.len() == m.ck_b@.len()
    &&& m.ck_b@.len() * m.bs_c >= m.n_c
    &&& m.sk_c@.len() == m.n_s && m.sn_c@.len() == m.n_s && m.sn_b@.len() == m.sk_b@.len()
    &&& m.sk_b@.len() * m.bs_s >= m.n_s
    &&& crate::stores::factsdir::interface::common::keyidx::keyidx_ok(m.ok_c@, m.ok_b@, m.oi_c@, m.oi_b@,
            m.bs_o as int, m.oi_kind, m.n_o as int)
    &&& m.e32@ == Seq::<u32>::empty() && m.e64@ == Seq::<u64>::empty()
    &&& crate::stores::custpart::interface::common::keyidx::keyidx_ok(m.ck_c@, m.ck_b@, Seq::<u32>::empty(),
            Seq::<u64>::empty(), m.bs_c as int, m.c_kind, m.n_c as int)
    &&& crate::stores::suppliers::interface::common::keyidx::keyidx_ok(m.sk_c@, m.sk_b@, Seq::<u32>::empty(),
            Seq::<u64>::empty(), m.bs_s as int, m.s_kind, m.n_s as int)
    &&& forall|j: int| 0 <= j < m.n_l ==> in_i64(#[trigger] lk(m, j)) && in_i64(lp(m, j)) && in_i64(ls(m, j))
    &&& forall|j: int| 0 <= j < m.n_l ==> coeff15(#[trigger] le(m, j)) && coeff15(ld(m, j))
    &&& forall|p: int| 0 <= p < m.n_o ==> in_i64(#[trigger] okey(m, p)) && in_i64(oc(m, p)) && in_i64(od(m, p))
    &&& forall|i: int| 0 <= i < m.n_c ==> in_i64(#[trigger] ck(m, i)) && in_i64(cn(m, i))
    &&& forall|i: int| 0 <= i < m.n_s ==> in_i64(#[trigger] sk(m, i)) && in_i64(sn(m, i))
    &&& forall|a: int, b: int| 0 <= a < m.n_o && 0 <= b < m.n_o && a != b ==> #[trigger] okey(m, a) != #[trigger] okey(m, b)
    &&& forall|a: int, b: int| 0 <= a < m.n_c && 0 <= b < m.n_c && a != b ==> #[trigger] ck(m, a) != #[trigger] ck(m, b)
    &&& forall|a: int, b: int| 0 <= a < m.n_s && 0 <= b < m.n_s && a != b ==> #[trigger] sk(m, a) != #[trigger] sk(m, b)
    &&& m.lo == super::sql::d95() && m.hi == super::sql::d96e() && m.d96 == super::sql::d96()
}

// ------------------------------------------------------------------------------------------------ lookups

/// The first stored orders row at or after `i` with key `k`, or `n_o`.
pub open spec fn rpos_from(m: Cols, k: int, i: int) -> int
    decreases m.n_o - i,
{
    if i < 0 || i >= m.n_o {
        m.n_o as int
    } else if okey(m, i) == k {
        i
    } else {
        rpos_from(m, k, i + 1)
    }
}

/// The stored orders row of key `k`, or `n_o` when none has it.
pub open spec fn rpos(m: Cols, k: int) -> int {
    rpos_from(m, k, 0)
}

/// The customer row with key `k`, if any.
pub open spec fn cfind(m: Cols, k: int) -> Option<int> {
    if exists|i: int| 0 <= i < m.n_c && #[trigger] ck(m, i) == k {
        Some(choose|i: int| 0 <= i < m.n_c && #[trigger] ck(m, i) == k)
    } else {
        None
    }
}

/// The supplier row with key `k`, if any.
pub open spec fn sfind(m: Cols, k: int) -> Option<int> {
    if exists|i: int| 0 <= i < m.n_s && #[trigger] sk(m, i) == k {
        Some(choose|i: int| 0 <= i < m.n_s && #[trigger] sk(m, i) == k)
    } else {
        None
    }
}

/// Nation rows: key, region named `$2`, name `$1`.
pub struct NStat {
    pub keys: Seq<i64>,
    pub reg: Seq<bool>,
    pub name: Seq<bool>,
}

pub open spec fn nstat_wf(ns: NStat) -> bool {
    &&& ns.reg.len() == ns.keys.len() && ns.name.len() == ns.keys.len()
    &&& forall|a: int, b: int| 0 <= a < ns.keys.len() && 0 <= b < ns.keys.len() && a != b
        ==> #[trigger] ns.keys[a] != #[trigger] ns.keys[b]
}

/// The nation row with key `k`, if any.
pub open spec fn nfind(ns: NStat, k: int) -> Option<int> {
    if exists|i: int| 0 <= i < ns.keys.len() && #[trigger] ns.keys[i] == k {
        Some(choose|i: int| 0 <= i < ns.keys.len() && #[trigger] ns.keys[i] == k)
    } else {
        None
    }
}

/// Some nation row has key `k` and its region is named `$2`.
pub open spec fn nreg(ns: NStat, k: int) -> bool {
    match nfind(ns, k) {
        Some(i) => ns.reg[i],
        None => false,
    }
}

// ------------------------------------------------------------------------------------------------ the scan's meaning

/// Stored lineitem row `j`'s contribution (`pm`: the part filter).
pub open spec fn lc(m: Cols, pm: spec_fn(int) -> bool, ns: NStat, j: int) -> Option<LHit> {
    if !pm(lp(m, j)) {
        None
    } else {
        let p = rpos(m, lk(m, j));
        if p >= m.n_o {
            None
        } else {
            let d = od(m, p);
            if !(m.lo <= d <= m.hi) {
                None
            } else {
                match cfind(m, oc(m, p)) {
                    None => None,
                    Some(ci) => if !nreg(ns, cn(m, ci)) {
                        None
                    } else {
                        match sfind(m, ls(m, j)) {
                            None => None,
                            Some(si) => match nfind(ns, sn(m, si)) {
                                None => None,
                                Some(ni) => Some(LHit {
                                    year: year_of(d),
                                    vol: le(m, j) * (100 - ld(m, j)),
                                    hit: ns.name[ni],
                                }),
                            },
                        }
                    },
                }
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------ accumulators

/// Per-year counts, volume sums and absolute volume masses (`*0`: 1995, `*1`: 1996); `h*`: supplier nation `$1`.
pub struct AccS {
    pub c0: int,
    pub v0: int,
    pub hc0: int,
    pub hv0: int,
    pub m0: int,
    pub c1: int,
    pub v1: int,
    pub hc1: int,
    pub hv1: int,
    pub m1: int,
}

pub open spec fn acc_zero() -> AccS {
    AccS { c0: 0, v0: 0, hc0: 0, hv0: 0, m0: 0, c1: 0, v1: 0, hc1: 0, hv1: 0, m1: 0 }
}

pub open spec fn acc_add(a: AccS, b: AccS) -> AccS {
    AccS {
        c0: a.c0 + b.c0, v0: a.v0 + b.v0, hc0: a.hc0 + b.hc0, hv0: a.hv0 + b.hv0, m0: a.m0 + b.m0,
        c1: a.c1 + b.c1, v1: a.v1 + b.v1, hc1: a.hc1 + b.hc1, hv1: a.hv1 + b.hv1, m1: a.m1 + b.m1,
    }
}

pub open spec fn absv(x: int) -> int {
    if x >= 0 { x } else { -x }
}

/// One row's accumulator from its contribution (years other than 1995 and 1996 add nothing).
pub open spec fn acc_of(h: Option<LHit>) -> AccS {
    match h {
        None => acc_zero(),
        Some(v) => {
            let hc = if v.hit { 1int } else { 0int };
            let hv = if v.hit { v.vol } else { 0int };
            if v.year == 1995 {
                AccS { c0: 1, v0: v.vol, hc0: hc, hv0: hv, m0: absv(v.vol), c1: 0, v1: 0, hc1: 0, hv1: 0, m1: 0 }
            } else if v.year == 1996 {
                AccS { c0: 0, v0: 0, hc0: 0, hv0: 0, m0: 0, c1: 1, v1: v.vol, hc1: hc, hv1: hv, m1: absv(v.vol) }
            } else {
                acc_zero()
            }
        },
    }
}

/// The accumulator of stored lineitem rows `[a, b)`.
pub open spec fn acc_range(m: Cols, pm: spec_fn(int) -> bool, ns: NStat, a: int, b: int) -> AccS
    decreases b - a,
{
    if b <= a { acc_zero() } else { acc_add(acc_range(m, pm, ns, a, b - 1), acc_of(lc(m, pm, ns, b - 1))) }
}

pub proof fn lemma_acc_add_assoc(a: AccS, b: AccS, c: AccS)
    ensures acc_add(acc_add(a, b), c) == acc_add(a, acc_add(b, c)),
{
}

pub proof fn lemma_acc_add_zero(a: AccS)
    ensures acc_add(a, acc_zero()) == a, acc_add(acc_zero(), a) == a,
{
}

/// Adjacent ranges add.
pub proof fn lemma_acc_split(m: Cols, pm: spec_fn(int) -> bool, ns: NStat, a: int, b: int, c: int)
    requires a <= b <= c,
    ensures acc_range(m, pm, ns, a, c) == acc_add(acc_range(m, pm, ns, a, b), acc_range(m, pm, ns, b, c)),
    decreases c - b,
{
    if b < c {
        lemma_acc_split(m, pm, ns, a, b, c - 1);
        lemma_acc_add_assoc(acc_range(m, pm, ns, a, b), acc_range(m, pm, ns, b, c - 1), acc_of(lc(m, pm, ns, c - 1)));
    } else {
        lemma_acc_add_zero(acc_range(m, pm, ns, a, b));
    }
}

/// Rows without a contribution add nothing.
pub proof fn lemma_acc_none(m: Cols, pm: spec_fn(int) -> bool, ns: NStat, a: int, b: int)
    requires forall|j: int| a <= j < b ==> #[trigger] lc(m, pm, ns, j) is None,
    ensures acc_range(m, pm, ns, a, b) == acc_zero(),
    decreases b - a,
{
    if a < b {
        lemma_acc_none(m, pm, ns, a, b - 1);
    }
}

/// Masses never decrease along a range, and bound the counts and sums.
pub open spec fn acc_sane(s: AccS, n: int) -> bool {
    &&& 0 <= s.c0 <= n && 0 <= s.c1 <= n && 0 <= s.hc0 <= s.c0 && 0 <= s.hc1 <= s.c1
    &&& absv(s.v0) <= s.m0 && absv(s.hv0) <= s.m0 && absv(s.v1) <= s.m1 && absv(s.hv1) <= s.m1
}

pub proof fn lemma_acc_range_sane(m: Cols, pm: spec_fn(int) -> bool, ns: NStat, a: int, b: int)
    requires a <= b,
    ensures acc_sane(acc_range(m, pm, ns, a, b), b - a),
    decreases b - a,
{
    if a < b {
        lemma_acc_range_sane(m, pm, ns, a, b - 1);
    }
}

pub proof fn lemma_acc_mass_mono(m: Cols, pm: spec_fn(int) -> bool, ns: NStat, a: int, b: int, c: int)
    requires a <= b <= c,
    ensures
        acc_range(m, pm, ns, a, b).m0 <= acc_range(m, pm, ns, a, c).m0,
        acc_range(m, pm, ns, a, b).m1 <= acc_range(m, pm, ns, a, c).m1,
{
    lemma_acc_split(m, pm, ns, a, b, c);
    lemma_acc_range_sane(m, pm, ns, b, c);
}

// ------------------------------------------------------------------------------------------------ groups

/// Row `j` of group `g` (rows `g * bs .. g * bs + bs`) has `j / bs == g`.
pub proof fn lemma_div_group(j: int, bs: int, g: int)
    requires bs >= 1, g * bs <= j < g * bs + bs,
    ensures j / bs == g,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(j, bs, g, j - g * bs);
}

/// The group of row `j` and the rows left in it.
pub proof fn lemma_group_of_row(j: int, bs: int)
    requires j >= 0, bs >= 1,
    ensures
        (j / bs) * bs <= j,
        0 <= j / bs,
        j < (j / bs) * bs + bs,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, bs);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(j, bs);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(j, bs);
    assert(bs * (j / bs) == (j / bs) * bs) by (nonlinear_arith);
}

// ------------------------------------------------------------------------------------------------ order positions

proof fn lemma_rpos_from_bound(m: Cols, k: int, i: int)
    requires 0 <= i,
    ensures
        0 <= rpos_from(m, k, i) <= m.n_o,
        rpos_from(m, k, i) < m.n_o ==> okey(m, rpos_from(m, k, i)) == k && rpos_from(m, k, i) >= i,
        forall|q: int| i <= q < rpos_from(m, k, i) ==> #[trigger] okey(m, q) != k,
    decreases m.n_o - i,
{
    if i < m.n_o && okey(m, i) != k {
        lemma_rpos_from_bound(m, k, i + 1);
    }
}

proof fn lemma_rpos_from_at(m: Cols, k: int, i: int, p: int)
    requires
        0 <= i <= p <= m.n_o,
        p < m.n_o ==> okey(m, p) == k,
        forall|q: int| i <= q < p ==> #[trigger] okey(m, q) != k,
    ensures rpos_from(m, k, i) == p,
    decreases p - i,
{
    if i < p {
        lemma_rpos_from_at(m, k, i + 1, p);
    }
}

/// `rpos(k)` is the first stored orders row with key `k`, or `n_o`.
pub proof fn lemma_rpos(m: Cols, k: int)
    ensures
        0 <= rpos(m, k) <= m.n_o,
        rpos(m, k) < m.n_o ==> okey(m, rpos(m, k)) == k,
        forall|q: int| 0 <= q < rpos(m, k) ==> #[trigger] okey(m, q) != k,
{
    lemma_rpos_from_bound(m, k, 0);
}

/// A stored orders row holding key `k` with no earlier row holding it is `rpos(k)`; `n_o` when no row holds it.
pub proof fn lemma_rpos_at(m: Cols, k: int, p: int)
    requires
        0 <= p <= m.n_o,
        p < m.n_o ==> okey(m, p) == k,
        forall|q: int| 0 <= q < p ==> #[trigger] okey(m, q) != k,
    ensures rpos(m, k) == p,
{
    lemma_rpos_from_at(m, k, 0, p);
}

/// Stored lineitem row `j`'s order comes no later than row `j + 1`'s.
pub open spec fn lstep(m: Cols, j: int) -> bool {
    rpos(m, lk(m, j)) <= rpos(m, lk(m, j + 1))
}

/// The stored lineitem rows follow the stored orders order.
pub open spec fn lines_clustered(m: Cols) -> bool {
    forall|j: int| 0 <= j < m.n_l - 1 ==> #[trigger] lstep(m, j)
}

/// `rpos` of lineitem rows is nondecreasing between any two rows.
pub proof fn lemma_lines_le(m: Cols, a: int, b: int)
    requires lines_clustered(m), 0 <= a <= b < m.n_l,
    ensures rpos(m, lk(m, a)) <= rpos(m, lk(m, b)),
    decreases b - a,
{
    if a < b {
        lemma_lines_le(m, a, b - 1);
        assert(lstep(m, b - 1));
    }
}

} // verus!
