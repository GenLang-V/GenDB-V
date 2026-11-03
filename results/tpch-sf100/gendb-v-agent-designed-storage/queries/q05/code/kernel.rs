//! The Q5 scan kernel: one worker task walks a range of stored lineitem rows (stored order: grouped by the stored
//! position of their order) together with their orders, and accumulates, per group of the qualifying nations,
//! the count, the revenue `l_extendedprice * (1 - l_discount)` (scale 4) and its absolute value.
//!
//! - Fast path (`scan_fast`: clustered layout, dense customer and supplier keys, both `cmap` maps): per block of
//!   4096 orders, first every order's map value (`ov`: date window, customer `c_custkey = row + 1`, customer map),
//!   then each order's run of lineitem rows (`skip_run`: codes compared within a storage block); a dead order's run
//!   is skipped whole (`lemma_dead_run`), a live order's rows check the supplier map (`fast_line`).
//! - General path: clustered layout with a forward merge (`line_start` binary search, `p` never decreasing), or
//!   orders found through the key index; customers and suppliers by dense key, key index or scan.
//! - Live path (`live::scan_live`, chosen in `ScanTask::run` when the task's two end runs are aligned): see `live`.
//! Invariant: each accumulator equals the sum over the rows done so far of `q5spec::contrib` (`lsum`), or the
//! absolute sum already exceeds `i128::MAX` (overflow flag: the caller answers Capacity).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::datetime::*;
use crate::link::join::*;
use crate::link::expr::i128_max;
use crate::gendb_entry::parallel::WorkerTask;
use crate::stores::facts::interface::cluster::{clustered, order_pos, first_key_from, lemma_clustered_le, lemma_order_pos_at};
use crate::stores::facts::interface::common::keyidx as okx;
use crate::stores::custpart::interface::common::keyidx as ckx;
use crate::stores::suppliers::interface::common::keyidx as skx;
use crate::agent::q5spec::*;
use crate::agent::lookup::keys_unique;
use crate::agent::chain::*;
use crate::agent::common::forview::*;
use crate::agent::common::sums::*;
use crate::agent::cmap::*;
use std::sync::Arc;

verus! {

/// Read-only inputs shared by every task: column slices, sizes, block divisors, layout flags, the date window,
/// and the ghost relations they decode to.
#[derive(Clone, Copy)]
pub struct ScanCtx {
    /// lineitem: l_orderkey, l_suppkey, l_extendedprice (U32 codes), l_discount (U8 codes), with I64 bases
    pub lk_c: &'static [u32],
    pub lk_b: &'static [i64],
    pub ls_c: &'static [u32],
    pub ls_b: &'static [i64],
    pub le_c: &'static [u32],
    pub le_b: &'static [i64],
    pub ld_c: &'static [u8],
    pub ld_b: &'static [i64],
    /// orders: o_orderkey, o_custkey (U32), o_orderdate (U16), the o_orderkey key index (kind `okind`)
    pub ok_c: &'static [u32],
    pub ok_b: &'static [i64],
    pub oc_c: &'static [u32],
    pub oc_b: &'static [i64],
    pub od_c: &'static [u16],
    pub od_b: &'static [i64],
    pub oi_c: &'static [u32],
    pub oi_b: &'static [u64],
    pub okind: u64,
    /// customer: c_custkey (U32) with its key index kind, c_nationkey (U8)
    pub ck_c: &'static [u32],
    pub ck_b: &'static [i64],
    pub ckind: u64,
    pub cn_c: &'static [u8],
    pub cn_b: &'static [i64],
    /// supplier: s_suppkey (U32) with its key index kind, s_nationkey (U8)
    pub sk_c: &'static [u32],
    pub sk_b: &'static [i64],
    pub skind: u64,
    pub sn_c: &'static [u8],
    pub sn_b: &'static [i64],
    /// empty index parts (customer and supplier keys are sorted in place)
    pub e32: &'static [u32],
    pub e64: &'static [u64],
    /// li_okruns: the start row of every run of equal l_orderkey (`setup::runs_wf`) and their count
    pub st: &'static [u32],
    pub st_n: usize,
    pub n_l: usize,
    pub n_o: usize,
    pub n_c: usize,
    pub n_s: usize,
    pub ldiv: Div,
    pub odiv: Div,
    pub cdiv: Div,
    pub sdiv: Div,
    /// the block sizes of the orders, customer and supplier key columns are the storage's (key indexes usable)
    pub ok_exact: bool,
    pub ck_exact: bool,
    pub sk_exact: bool,
    /// lineitem rows follow their orders (checked flag of the storage)
    pub clustered: bool,
    /// c_custkey of stored row c is c + 1 (checked by the caller)
    pub cdense: bool,
    /// s_suppkey of stored row s is s + 1 (checked by the caller)
    pub sdense: bool,
    /// the date window `[lo_day, hi_day)` in days since 2000-01-01
    pub lo_day: i64,
    pub hi_day: i64,
    pub rs: Ghost<Rels>,
    pub prm: Ghost<Prm>,
    /// stored lineitem rows and stored orders rows (with their canonical orders row)
    pub lrows: Ghost<Seq<Row>>,
    pub orows: Ghost<Seq<Row>>,
    pub omap: Ghost<Seq<int>>,
    /// the qualifying-nation list's nation rows and the group names
    pub qrow: Ghost<Seq<int>>,
    pub gnames: Ghost<Seq<Seq<u8>>>,
}

impl ScanCtx {
    /// Stored lineitem row `j` decodes to its columns.
    pub open spec fn lrow_ok(&self, j: int) -> bool {
        let l = self.lrows@[j];
        let bs = self.ldiv.bs as int;
        &&& l.len() == 15
        &&& l[0] == Val::Int(fv32(self.lk_c@, self.lk_b@, bs, j))
        &&& l[2] == Val::Int(fv32(self.ls_c@, self.ls_b@, bs, j))
        &&& l[5] == (Val::Num { coeff: fv32(self.le_c@, self.le_b@, bs, j), scale: 2 })
        &&& l[6] == (Val::Num { coeff: fv8(self.ld_c@, self.ld_b@, bs, j), scale: 2 })
        &&& abs(fv32(self.le_c@, self.le_b@, bs, j)) < pow10(15)
        &&& abs(fv8(self.ld_c@, self.ld_b@, bs, j)) < pow10(15)
    }

    /// Stored orders row `p` is its canonical row and decodes to its columns.
    pub open spec fn orow_ok(&self, p: int) -> bool {
        let o = self.orows@[p];
        let bs = self.odiv.bs as int;
        &&& 0 <= self.omap@[p] < self.rs@.o.len()
        &&& o == self.rs@.o[self.omap@[p]]
        &&& o[0] == Val::Int(fv32(self.ok_c@, self.ok_b@, bs, p))
        &&& o[1] == Val::Int(fv32(self.oc_c@, self.oc_b@, bs, p))
        &&& o[4] == Val::Date(fv16(self.od_c@, self.od_b@, bs, p))
    }

    /// Canonical orders row `i` is some stored orders row.
    pub open spec fn o_covered(&self, i: int) -> bool {
        exists|p: int| 0 <= p < self.n_o && #[trigger] self.omap@[p] == i
    }

    /// Customer row `c` decodes to its key and nation key.
    pub open spec fn crow_ok(&self, c: int) -> bool {
        let bs = self.cdiv.bs as int;
        &&& self.rs@.c[c][0] == Val::Int(fv32(self.ck_c@, self.ck_b@, bs, c))
        &&& self.rs@.c[c][3] == Val::Int(fv8(self.cn_c@, self.cn_b@, bs, c))
    }

    /// Supplier row `s` decodes to its key and nation key.
    pub open spec fn srow_ok(&self, s: int) -> bool {
        let bs = self.sdiv.bs as int;
        &&& self.rs@.s[s][0] == Val::Int(fv32(self.sk_c@, self.sk_b@, bs, s))
        &&& self.rs@.s[s][3] == Val::Int(fv8(self.sn_c@, self.sn_b@, bs, s))
    }

    pub open spec fn wf(&self) -> bool {
        let rs = self.rs@;
        let prm = self.prm@;
        &&& self.ldiv.ok() && self.odiv.ok() && self.cdiv.ok() && self.sdiv.ok()
        &&& self.lrows@.len() == self.n_l && self.orows@.len() == self.n_o && self.omap@.len() == self.n_o
        &&& rs.c.len() == self.n_c && rs.s.len() == self.n_s
        &&& col32_ok(self.lk_c@, self.lk_b@, self.ldiv.bs as int, self.n_l as int)
        &&& col32_ok(self.ls_c@, self.ls_b@, self.ldiv.bs as int, self.n_l as int)
        &&& col32_ok(self.le_c@, self.le_b@, self.ldiv.bs as int, self.n_l as int)
        &&& col8_ok(self.ld_c@, self.ld_b@, self.ldiv.bs as int, self.n_l as int)
        &&& col32_ok(self.ok_c@, self.ok_b@, self.odiv.bs as int, self.n_o as int)
        &&& col32_ok(self.oc_c@, self.oc_b@, self.odiv.bs as int, self.n_o as int)
        &&& col16_ok(self.od_c@, self.od_b@, self.odiv.bs as int, self.n_o as int)
        &&& col32_ok(self.ck_c@, self.ck_b@, self.cdiv.bs as int, self.n_c as int)
        &&& col8_ok(self.cn_c@, self.cn_b@, self.cdiv.bs as int, self.n_c as int)
        &&& col32_ok(self.sk_c@, self.sk_b@, self.sdiv.bs as int, self.n_s as int)
        &&& col8_ok(self.sn_c@, self.sn_b@, self.sdiv.bs as int, self.n_s as int)
        &&& forall|j: int| 0 <= j < self.n_l ==> #[trigger] self.lrow_ok(j)
        &&& forall|p: int| 0 <= p < self.n_o ==> #[trigger] self.orow_ok(p)
        &&& forall|c: int| 0 <= c < self.n_c ==> #[trigger] self.crow_ok(c)
        &&& forall|s: int| 0 <= s < self.n_s ==> #[trigger] self.srow_ok(s)
        &&& forall|i: int| 0 <= i < rs.o.len() ==> #[trigger] self.o_covered(i)
        &&& self.ok_exact ==> okx::keyidx_ok(self.ok_c@, self.ok_b@, self.oi_c@, self.oi_b@, self.odiv.bs as int, self.okind, self.n_o as int)
        &&& self.ck_exact ==> ckx::keyidx_ok(self.ck_c@, self.ck_b@, self.e32@, self.e64@, self.cdiv.bs as int, self.ckind, self.n_c as int)
        &&& self.sk_exact ==> skx::keyidx_ok(self.sk_c@, self.sk_b@, self.e32@, self.e64@, self.sdiv.bs as int, self.skind, self.n_s as int)
        &&& self.cdense ==> forall|c: int| 0 <= c < self.n_c ==> #[trigger] fv32(self.ck_c@, self.ck_b@, self.cdiv.bs as int, c) == c + 1
        &&& self.sdense ==> forall|s: int| 0 <= s < self.n_s ==> #[trigger] fv32(self.sk_c@, self.sk_b@, self.sdiv.bs as int, s) == s + 1
        &&& self.clustered ==> clustered(self.lrows@, self.orows@)
        &&& crate::agent::setup::runs_wf(self.lrows@, self.st@)
        &&& self.st_n == self.st@.len()
        &&& keys_unique(self.orows@) && keys_unique(rs.o) && keys_unique(rs.c) && keys_unique(rs.s) && keys_unique(rs.n)
        &&& self.lo_day as int == prm.lo
        &&& self.hi_day as int * usecs_per_day() >= prm.hi
        &&& (self.hi_day as int - 1) * usecs_per_day() < prm.hi
    }

    /// The order position (first stored orders row of the key) of stored lineitem row `j`.
    pub open spec fn op(&self, j: int) -> int {
        order_pos(self.orows@, self.lrows@[j][0])
    }

    /// `r` splits the stored lineitem rows at orders position `p`: rows before `r` have earlier orders.
    pub open spec fn split_at(&self, p: int, r: int) -> bool {
        &&& 0 <= r <= self.n_l
        &&& forall|j: int| 0 <= j < self.n_l ==> (j < r <==> #[trigger] self.op(j) < p)
    }

    /// Sum over stored lineitem rows `[a, b)` of accumulator `m` of group `gi`.
    pub open spec fn lsum(&self, gi: int, m: int, a: int, b: int) -> int {
        sum_of(self.lrows@.subrange(a, b), contrib_fn(self.rs@, self.prm@, gkey(self.gnames@, gi), m))
    }

    /// The accumulators of group `gi` over rows `[a, b)`, or the overflow of its absolute sum.
    pub open spec fn acc_ok(&self, gi: int, a: int, b: int, cnt: usize, sum: i128, abs_: u128, ovf: bool) -> bool {
        if ovf {
            self.lsum(gi, 2, a, b) > i128_max()
        } else {
            &&& cnt as int == self.lsum(gi, 0, a, b)
            &&& sum as int == self.lsum(gi, 1, a, b)
            &&& abs_ as int == self.lsum(gi, 2, a, b)
            &&& abs_ as int <= i128_max()
            &&& -(abs_ as int) <= sum as int <= abs_ as int
            &&& cnt as int <= b - a
        }
    }
}

// ------------------------------------------------------------------------------------------- order positions

/// `first_key_from` finds a row holding the key, after rows that do not.
pub proof fn lemma_fkf(orows: Seq<Row>, k: Val, i: int)
    requires 0 <= i,
    ensures
        first_key_from(orows, k, i) < orows.len() ==> orows[first_key_from(orows, k, i)][0] == k,
        first_key_from(orows, k, i) <= orows.len(),
    decreases orows.len() - i,
{
    if i < orows.len() && orows[i][0] != k {
        lemma_fkf(orows, k, i + 1);
    }
}

/// The stored orders row with key `k`, or `None` when no stored orders row has it.
fn order_row(t: &ScanCtx, k: i64) -> (r: Option<usize>)
    requires t.wf(),
    ensures
        r matches Some(p) ==> p < t.n_o && t.orows@[p as int][0] == Val::Int(k as int),
        r is None ==> forall|p: int| 0 <= p < t.n_o ==> #[trigger] t.orows@[p][0] != Val::Int(k as int),
    no_unwind
{
    let r = if t.ok_exact {
        okx::key_find(t.ok_c, t.ok_b, t.oi_c, t.oi_b, t.odiv.bs, t.okind, t.n_o, k as i128)
    } else {
        scan32(t.ok_c, t.ok_b, t.odiv, t.n_o, k)
    };
    proof {
        match r {
            Some(p) => {
                assert(t.orow_ok(p as int));
                assert(okx::fkey(t.ok_c@, t.ok_b@, t.odiv.bs as int, p as int) == fv32(t.ok_c@, t.ok_b@, t.odiv.bs as int, p as int));
            },
            None => {
                assert forall|p: int| 0 <= p < t.n_o implies #[trigger] t.orows@[p][0] != Val::Int(k as int) by {
                    assert(t.orow_ok(p));
                    assert(okx::fkey(t.ok_c@, t.ok_b@, t.odiv.bs as int, p) == fv32(t.ok_c@, t.ok_b@, t.odiv.bs as int, p));
                }
            },
        }
    }
    r
}

/// `order_pos` of key `k` (the stored orders row holding it, or `n_o`).
fn order_position(t: &ScanCtx, k: i64) -> (r: usize)
    requires t.wf(),
    ensures r as int == order_pos(t.orows@, Val::Int(k as int)), r <= t.n_o,
    no_unwind
{
    match order_row(t, k) {
        Some(p) => {
            proof {
                assert forall|q: int| 0 <= q < t.orows@.len() && q != p implies #[trigger] t.orows@[q][0] != Val::Int(k as int) by {
                    if t.orows@[q][0] == Val::Int(k as int) {
                        assert(t.orows@[q][0] == t.orows@[p as int][0]);
                    }
                }
                lemma_order_pos_at(t.orows@, Val::Int(k as int), p as int);
            }
            p
        },
        None => {
            proof {
                lemma_order_pos_at(t.orows@, Val::Int(k as int), t.n_o as int);
            }
            t.n_o
        },
    }
}

/// The first stored lineitem row whose order lies at or after orders position `p` (binary search; the stored
/// lineitem rows follow their orders).
fn line_start(t: &ScanCtx, p: usize) -> (r: usize)
    requires t.wf(), t.clustered,
    ensures t.split_at(p as int, r as int),
    no_unwind
{
    let mut lo: usize = 0;
    let mut hi: usize = t.n_l;
    while lo < hi
        invariant
            t.wf(), t.clustered,
            lo <= hi <= t.n_l,
            forall|j: int| 0 <= j < lo ==> #[trigger] t.op(j) < p,
            forall|j: int| hi <= j < t.n_l ==> #[trigger] t.op(j) >= p,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        let k = get32(t.lk_c, t.lk_b, t.ldiv, t.n_l, mid);
        let q = order_position(t, k);
        proof {
            assert(t.lrow_ok(mid as int));
            assert(q as int == t.op(mid as int));
        }
        if q < p {
            proof {
                assert forall|j: int| 0 <= j < mid + 1 implies #[trigger] t.op(j) < p by {
                    lemma_clustered_le(t.lrows@, t.orows@, j, mid as int);
                }
            }
            lo = mid + 1;
        } else {
            proof {
                assert forall|j: int| mid <= j < t.n_l implies #[trigger] t.op(j) >= p by {
                    lemma_clustered_le(t.lrows@, t.orows@, mid as int, j);
                }
            }
            hi = mid;
        }
    }
    lo
}

// ------------------------------------------------------------------------------------------- dimension lookups

/// The customer row with key `ck`, or `None` when no customer row has it.
fn cust_row(t: &ScanCtx, ck: i64) -> (r: Option<usize>)
    requires t.wf(),
    ensures
        r matches Some(c) ==> c < t.n_c && t.rs@.c[c as int][0] == Val::Int(ck as int),
        r is None ==> forall|c: int| 0 <= c < t.n_c ==> #[trigger] t.rs@.c[c][0] != Val::Int(ck as int),
    no_unwind
{
    if t.cdense {
        if 1 <= ck && (ck as u64) <= (t.n_c as u64) {
            let c = (ck - 1) as usize;
            proof {
                assert(t.crow_ok(c as int));
            }
            Some(c)
        } else {
            proof {
                assert forall|c: int| 0 <= c < t.n_c implies #[trigger] t.rs@.c[c][0] != Val::Int(ck as int) by {
                    assert(t.crow_ok(c));
                }
            }
            None
        }
    } else {
        let r = if t.ck_exact {
            ckx::key_find(t.ck_c, t.ck_b, t.e32, t.e64, t.cdiv.bs, t.ckind, t.n_c, ck as i128)
        } else {
            scan32(t.ck_c, t.ck_b, t.cdiv, t.n_c, ck)
        };
        proof {
            match r {
                Some(c) => {
                    assert(t.crow_ok(c as int));
                    assert(ckx::fkey(t.ck_c@, t.ck_b@, t.cdiv.bs as int, c as int) == fv32(t.ck_c@, t.ck_b@, t.cdiv.bs as int, c as int));
                },
                None => {
                    assert forall|c: int| 0 <= c < t.n_c implies #[trigger] t.rs@.c[c][0] != Val::Int(ck as int) by {
                        assert(t.crow_ok(c));
                        assert(ckx::fkey(t.ck_c@, t.ck_b@, t.cdiv.bs as int, c) == fv32(t.ck_c@, t.ck_b@, t.cdiv.bs as int, c));
                    }
                },
            }
        }
        r
    }
}

/// The supplier row with key `sk`, or `None` when no supplier row has it.
fn supp_row(t: &ScanCtx, sk: i64) -> (r: Option<usize>)
    requires t.wf(),
    ensures
        r matches Some(s) ==> s < t.n_s && t.rs@.s[s as int][0] == Val::Int(sk as int),
        r is None ==> forall|s: int| 0 <= s < t.n_s ==> #[trigger] t.rs@.s[s][0] != Val::Int(sk as int),
    no_unwind
{
    if t.sdense {
        if 1 <= sk && (sk as u64) <= (t.n_s as u64) {
            let s = (sk - 1) as usize;
            proof {
                assert(t.srow_ok(s as int));
            }
            Some(s)
        } else {
            proof {
                assert forall|s: int| 0 <= s < t.n_s implies #[trigger] t.rs@.s[s][0] != Val::Int(sk as int) by {
                    assert(t.srow_ok(s));
                }
            }
            None
        }
    } else {
        let r = if t.sk_exact {
            skx::key_find(t.sk_c, t.sk_b, t.e32, t.e64, t.sdiv.bs, t.skind, t.n_s, sk as i128)
        } else {
            scan32(t.sk_c, t.sk_b, t.sdiv, t.n_s, sk)
        };
        proof {
            match r {
                Some(s) => {
                    assert(t.srow_ok(s as int));
                    assert(skx::fkey(t.sk_c@, t.sk_b@, t.sdiv.bs as int, s as int) == fv32(t.sk_c@, t.sk_b@, t.sdiv.bs as int, s as int));
                },
                None => {
                    assert forall|s: int| 0 <= s < t.n_s implies #[trigger] t.rs@.s[s][0] != Val::Int(sk as int) by {
                        assert(t.srow_ok(s));
                        assert(skx::fkey(t.sk_c@, t.sk_b@, t.sdiv.bs as int, s) == fv32(t.sk_c@, t.sk_b@, t.sdiv.bs as int, s));
                    }
                },
            }
        }
        r
    }
}

/// The first entry of the qualifying-nation list with key `cnk`.
pub fn qual_lookup(qkey: &Vec<i64>, cnk: i64) -> (r: Option<usize>)
    ensures
        r matches Some(q) ==> q < qkey@.len() && qkey@[q as int] == cnk,
        r is None ==> forall|q: int| 0 <= q < qkey@.len() ==> #[trigger] qkey@[q] != cnk,
    no_unwind
{
    let n = qkey.len();
    let mut q: usize = 0;
    while q < n
        invariant
            n == qkey@.len(),
            q <= n,
            forall|i: int| 0 <= i < q ==> #[trigger] qkey@[i] != cnk,
        decreases n - q,
    {
        if qkey[q] == cnk {
            return Some(q);
        }
        q = q + 1;
    }
    None
}

/// A date is inside the window exactly when it is in `[lo_day, hi_day)`.
proof fn lemma_window(t: &ScanCtx, o: Row, d: int)
    requires t.wf(), o[4] == Val::Date(d),
    ensures date_ok(o, t.prm@) == (t.lo_day <= d && d < t.hi_day),
{
    let u = usecs_per_day();
    let h = t.hi_day as int;
    assert(u > 0);
    if d < h {
        assert(d * u <= (h - 1) * u) by (nonlinear_arith) requires d <= h - 1, u > 0;
    } else {
        assert(d * u >= h * u) by (nonlinear_arith) requires d >= h, u > 0;
    }
}

/// The customer and supplier maps of a task, when it has them (`use_map`).
pub open spec fn map_ok(t: ScanCtx, qkey: Seq<i64>, ms: Seq<Vec<u64>>, cmd: Div, sms: Seq<Vec<u64>>, smd: Div, use_map: bool) -> bool {
    use_map ==> qkey.len() < 16 && cmd.ok() && smd.ok()
        && cmap_ok(ms, cmd.bs as int, qkey, t.cn_c@, t.cn_b@, t.cdiv.bs as int, t.n_c as int)
        && cmap_ok(sms, smd.bs as int, qkey, t.sn_c@, t.sn_b@, t.sdiv.bs as int, t.n_s as int)
}

/// Whether supplier row `s` is in nation `cnk` (through the supplier map when there is one: `cur_v` is the map
/// value of `cnk`).
fn same_nation(t: &ScanCtx, qkey: &Vec<i64>, ms: &Vec<Vec<u64>>, cmd: Div, sms: &Vec<Vec<u64>>, smd: Div, use_map: bool,
    s: usize, cnk: i64, cur_v: u64) -> (b: bool)
    requires
        t.wf(), s < t.n_s, map_ok(*t, qkey@, ms@, cmd, sms@, smd, use_map),
        use_map ==> cur_v != 0 && cur_v == qvl(qkey@, cnk as int),
    ensures b == (fv8(t.sn_c@, t.sn_b@, t.sdiv.bs as int, s as int) == cnk as int),
    no_unwind
{
    if use_map {
        proof {
            assert(cmap_has(sms@, smd.bs as int, s as int));
        }
        let sv = cmap_get(sms, smd, s);
        proof {
            let snk = fv8(t.sn_c@, t.sn_b@, t.sdiv.bs as int, s as int);
            assert(cmap_val(sms@, smd.bs as int, s as int) == qvl(qkey@, snk));
            lemma_qvl(qkey@, snk);
            lemma_qvl(qkey@, cnk as int);
        }
        sv == cur_v
    } else {
        let snk = get8(t.sn_c, t.sn_b, t.sdiv, t.n_s, s);
        snk == cnk
    }
}

/// The qualifying-list entry of customer row `c`'s nation key (through the map when there is one).
fn nation_entry(t: &ScanCtx, qkey: &Vec<i64>, ms: &Vec<Vec<u64>>, cmd: Div, sms: &Vec<Vec<u64>>, smd: Div, use_map: bool,
    c: usize) -> (r: Option<usize>)
    requires t.wf(), map_ok(*t, qkey@, ms@, cmd, sms@, smd, use_map), c < t.n_c,
    ensures
        use_map && r is Some ==> r->0 + 1 == qvl(qkey@, fv8(t.cn_c@, t.cn_b@, t.cdiv.bs as int, c as int)),
        r matches Some(q) ==> q < qkey@.len() && qkey@[q as int] as int == fv8(t.cn_c@, t.cn_b@, t.cdiv.bs as int, c as int),
        r is None ==> forall|q: int| 0 <= q < qkey@.len() ==> #[trigger] qkey@[q] as int != fv8(t.cn_c@, t.cn_b@, t.cdiv.bs as int, c as int),
    no_unwind
{
    if use_map {
        proof {
            assert(cmap_has(ms@, cmd.bs as int, c as int));
            lemma_qvl(qkey@, fv8(t.cn_c@, t.cn_b@, t.cdiv.bs as int, c as int));
        }
        let v = cmap_get(ms, cmd, c);
        if v == 0 { None } else { Some((v - 1) as usize) }
    } else {
        let cnk = get8(t.cn_c, t.cn_b, t.cdiv, t.n_c, c);
        qual_lookup(qkey, cnk)
    }
}

/// Whether stored orders row `p` is live (else its key is dead), its group, the customer's nation key and ghost
/// witnesses of the live chain.
fn eval_order(t: &ScanCtx, qkey: &Vec<i64>, qgrp: &Vec<usize>, ms: &Vec<Vec<u64>>, cmd: Div, sms: &Vec<Vec<u64>>, smd: Div,
    use_map: bool, p: usize) -> (r: (bool, usize, i64, Ghost<int>, Ghost<int>, Ghost<int>, u64))
    requires
        t.wf(),
        qlist_ok(t.rs@, t.prm@, qkey@, qgrp@, t.qrow@, t.gnames@),
        map_ok(*t, qkey@, ms@, cmd, sms@, smd, use_map),
        p < t.n_o,
    ensures
        !r.0 ==> key_dead(t.rs@, t.prm@, t.orows@[p as int][0]),
        r.0 ==> r.1 < t.gnames@.len()
            && order_live(t.rs@, t.prm@, qkey@, qgrp@, t.orows@[p as int][0], r.3@, r.4@, r.5@, r.2)
            && qgrp@[r.5@] == r.1,
        r.0 && use_map ==> r.6 != 0 && r.6 == qvl(qkey@, r.2 as int),
    no_unwind
{
    let ghost rs = t.rs@;
    let ghost prm = t.prm@;
    let ghost oi = t.omap@[p as int];
    proof {
        assert(t.orow_ok(p as int));
    }
    let d = get16(t.od_c, t.od_b, t.odiv, t.n_o, p);
    proof {
        lemma_window(t, rs.o[oi], d as int);
    }
    if t.lo_day <= d && d < t.hi_day {
        let ck = get32(t.oc_c, t.oc_b, t.odiv, t.n_o, p);
        match cust_row(t, ck) {
            Some(c) => {
                proof {
                    assert(t.crow_ok(c as int));
                }
                match nation_entry(t, qkey, ms, cmd, sms, smd, use_map, c) {
                    Some(qq) => {
                        let cnk = qkey[qq];
                        proof {
                            assert(qentry_ok(rs, prm, qkey@, qgrp@, t.qrow@, t.gnames@, qq as int));
                        }
                        let v: u64 = if use_map { qq as u64 + 1 } else { 0 };
                        (true, qgrp[qq], cnk, Ghost(oi), Ghost(c as int), Ghost(qq as int), v)
                    },
                    None => {
                        proof {
                            let fv = fv8(t.cn_c@, t.cn_b@, t.cdiv.bs as int, c as int);
                            assert(i64::MIN <= fv <= i64::MAX);
                            let cnk = fv as i64;
                            assert forall|q: int| 0 <= q < qkey@.len() implies #[trigger] qkey@[q] != cnk by {
                                assert(qkey@[q] as int != fv);
                            }
                            lemma_dead_nation(rs, prm, qkey@, qgrp@, t.qrow@, t.gnames@, oi, c as int, cnk);
                        }
                        (false, 0, 0, Ghost(0), Ghost(0), Ghost(0), 0)
                    },
                }
            },
            None => {
                proof {
                    lemma_dead_no_customer(rs, prm, oi);
                }
                (false, 0, 0, Ghost(0), Ghost(0), Ghost(0), 0)
            },
        }
    } else {
        proof {
            lemma_dead_window(rs, prm, oi);
        }
        (false, 0, 0, Ghost(0), Ghost(0), Ghost(0), 0)
    }
}

/// The group of an order key found through the key index (non-clustered layout): a missing order is dead.
fn eval_key(t: &ScanCtx, qkey: &Vec<i64>, qgrp: &Vec<usize>, ms: &Vec<Vec<u64>>, cmd: Div, sms: &Vec<Vec<u64>>, smd: Div,
    use_map: bool, k: i64) -> (r: (bool, usize, i64, Ghost<int>, Ghost<int>, Ghost<int>, u64))
    requires
        t.wf(),
        qlist_ok(t.rs@, t.prm@, qkey@, qgrp@, t.qrow@, t.gnames@),
        map_ok(*t, qkey@, ms@, cmd, sms@, smd, use_map),
    ensures
        !r.0 ==> key_dead(t.rs@, t.prm@, Val::Int(k as int)),
        r.0 ==> r.1 < t.gnames@.len()
            && order_live(t.rs@, t.prm@, qkey@, qgrp@, Val::Int(k as int), r.3@, r.4@, r.5@, r.2)
            && qgrp@[r.5@] == r.1,
        r.0 && use_map ==> r.6 != 0 && r.6 == qvl(qkey@, r.2 as int),
    no_unwind
{
    match order_row(t, k) {
        Some(p) => eval_order(t, qkey, qgrp, ms, cmd, sms, smd, use_map, p),
        None => {
            proof {
                let rs = t.rs@;
                assert forall|i: int| 0 <= i < rs.o.len() implies #[trigger] rs.o[i][0] != Val::Int(k as int) by {
                    assert(t.o_covered(i));
                    let p = choose|p: int| 0 <= p < t.n_o && #[trigger] t.omap@[p] == i;
                    assert(t.orow_ok(p));
                }
                lemma_dead_no_order(rs, t.prm@, Val::Int(k as int));
            }
            (false, 0, 0, Ghost(0), Ghost(0), Ghost(0), 0)
        },
    }
}

/// Whether stored lineitem row `j` of a live order (group `cur_q`, customer nation key `cnk`) has its supplier in
/// that nation: then its multiplicity is 1 in group `cur_q` and 0 elsewhere; otherwise 0 everywhere.
fn line_hit(t: &ScanCtx, qkey: &Vec<i64>, qgrp: &Vec<usize>, ms: &Vec<Vec<u64>>, cmd: Div, sms: &Vec<Vec<u64>>, smd: Div,
    use_map: bool, j: usize, cur_q: usize, cnk: i64, cur_v: u64, oi: Ghost<int>, ci: Ghost<int>, qq: Ghost<int>) -> (hit: bool)
    requires
        t.wf(),
        qlist_ok(t.rs@, t.prm@, qkey@, qgrp@, t.qrow@, t.gnames@),
        map_ok(*t, qkey@, ms@, cmd, sms@, smd, use_map),
        use_map ==> cur_v != 0 && cur_v == qvl(qkey@, cnk as int),
        j < t.n_l,
        cur_q < t.gnames@.len(),
        order_live(t.rs@, t.prm@, qkey@, qgrp@, t.lrows@[j as int][0], oi@, ci@, qq@, cnk),
        qgrp@[qq@] == cur_q,
    ensures
        forall|gi: int| 0 <= gi < t.gnames@.len() ==>
            #[trigger] line_mult(t.rs@, t.prm@, gkey(t.gnames@, gi), t.lrows@[j as int])
                == if hit && gi == cur_q { 1int } else { 0int },
    no_unwind
{
    let ghost rs = t.rs@;
    let ghost prm = t.prm@;
    let ghost gn = t.gnames@;
    let ghost l = t.lrows@[j as int];
    proof {
        assert(t.lrow_ok(j as int));
    }
    let sk = get32(t.ls_c, t.ls_b, t.ldiv, t.n_l, j);
    match supp_row(t, sk) {
        Some(s) => {
            proof {
                assert(t.srow_ok(s as int));
            }
            if same_nation(t, qkey, ms, cmd, sms, smd, use_map, s, cnk, cur_v) {
                proof {
                    assert forall|gi: int| 0 <= gi < gn.len() implies
                        #[trigger] line_mult(rs, prm, gkey(gn, gi), l) == if true && gi == cur_q { 1int } else { 0int } by {
                        lemma_line_hit(rs, prm, qkey@, qgrp@, t.qrow@, gn, l, oi@, ci@, qq@, cnk, s as int, gkey(gn, gi));
                        lemma_gkey_eq(gn, gi, cur_q as int);
                    }
                }
                true
            } else {
                proof {
                    assert(rs.s[s as int][0] == l[2] && rs.s[s as int][3] != Val::Int(cnk as int));
                    assert forall|gi: int| 0 <= gi < gn.len() implies
                        #[trigger] line_mult(rs, prm, gkey(gn, gi), l) == if false && gi == cur_q { 1int } else { 0int } by {
                        lemma_line_miss(rs, prm, qkey@, qgrp@, t.qrow@, gn, l, oi@, ci@, qq@, cnk, gkey(gn, gi));
                    }
                }
                false
            }
        },
        None => {
            proof {
                assert forall|gi: int| 0 <= gi < gn.len() implies
                    #[trigger] line_mult(rs, prm, gkey(gn, gi), l) == if false && gi == cur_q { 1int } else { 0int } by {
                    lemma_line_miss(rs, prm, qkey@, qgrp@, t.qrow@, gn, l, oi@, ci@, qq@, cnk, gkey(gn, gi));
                }
            }
            false
        },
    }
}

// ------------------------------------------------------------------------------------------- accumulation

/// One more row: every accumulator of group `gi` grows by the row's multiplicity times its weight.
pub proof fn lemma_acc_step(t: &ScanCtx, gi: int, a: int, j: int, dm: int)
    requires
        t.wf(), 0 <= a <= j < t.n_l,
        line_mult(t.rs@, t.prm@, gkey(t.gnames@, gi), t.lrows@[j]) == dm,
    ensures
        forall|m: int| #[trigger] t.lsum(gi, m, a, j + 1) == t.lsum(gi, m, a, j) + dm * wsel(m, t.lrows@[j]),
{
    assert forall|m: int| #[trigger] t.lsum(gi, m, a, j + 1) == t.lsum(gi, m, a, j) + dm * wsel(m, t.lrows@[j]) by {
        lemma_sum_range_step(t.lrows@, contrib_fn(t.rs@, t.prm@, gkey(t.gnames@, gi), m), a, j);
    }
}

/// The weights of stored lineitem row `j`: count 1, revenue `ep * (100 - dc)` and its absolute value.
pub proof fn lemma_weights(t: &ScanCtx, j: int, ep: int, dc: int)
    requires t.wf(), 0 <= j < t.n_l,
        ep == fv32(t.le_c@, t.le_b@, t.ldiv.bs as int, j),
        dc == fv8(t.ld_c@, t.ld_b@, t.ldiv.bs as int, j),
    ensures
        wsel(0, t.lrows@[j]) == 1,
        wsel(1, t.lrows@[j]) == ep * (100 - dc),
        wsel(2, t.lrows@[j]) == abs(ep * (100 - dc)),
        abs(ep) < pow10(15), abs(dc) < pow10(15),
{
    assert(t.lrow_ok(j));
}

/// The revenue of one row and its absolute value, exactly, in `i128`.
pub fn revenue(ep: i64, dc: i64) -> (r: (i128, u128))
    requires abs(ep as int) < pow10(15), abs(dc as int) < pow10(15),
    ensures
        r.0 as int == ep * (100 - dc),
        r.1 as int == abs(ep * (100 - dc)),
        r.1 as int <= 0x10000_0000_0000_0000_0000_0000_0000,
    no_unwind
{
    proof {
        assert(pow10(15) == 1000000000000000) by (compute);
    }
    let e = ep as i128;
    let o = 100i128 - dc as i128;
    proof {
        let (x, y) = (e as int, o as int);
        assert(-1000000000000000 < x < 1000000000000000);
        assert(-1000000000000000 + 100 < y < 1000000000000000 + 100);
        assert(-1000000000000100000000000000000 < x * y < 1000000000000100000000000000000) by (nonlinear_arith)
            requires -1000000000000000 < x < 1000000000000000, -999999999999900 < y < 1000000000000100;
    }
    let v = e * o;
    let a: u128 = if v < 0 { (-v) as u128 } else { v as u128 };
    (v, a)
}

// ------------------------------------------------------------------------------------------- fast path
// Clustered layout, dense customer and supplier keys and both maps: per block of orders, first the map value of
// every order (`ov`: independent loads), then the block's lineitem rows with a branch-free order advance and an
// unconditional supplier-map load (row 0 for rows of dead orders), so the random loads overlap.

/// The map value of stored orders row `p`: its customer's map value when the date is in the window and the
/// customer key is a row's (`c_custkey = row + 1`), else 0.
pub open spec fn ov(t: ScanCtx, ms: Seq<Vec<u64>>, cw: int, p: int) -> u64 {
    let bs = t.odiv.bs as int;
    let d = fv16(t.od_c@, t.od_b@, bs, p);
    let ck = fv32(t.oc_c@, t.oc_b@, bs, p);
    if t.lo_day <= d < t.hi_day && 1 <= ck <= t.n_c { cmap_val(ms, cw, ck - 1) } else { 0 }
}

/// `ov` of stored orders row `p`.
pub fn order_v(t: &ScanCtx, qkey: &Vec<i64>, ms: &Vec<Vec<u64>>, cmd: Div, sms: &Vec<Vec<u64>>, smd: Div, p: usize) -> (v: u64)
    requires t.wf(), map_ok(*t, qkey@, ms@, cmd, sms@, smd, true), t.n_c >= 1, p < t.n_o,
    ensures v == ov(*t, ms@, cmd.bs as int, p as int),
    no_unwind
{
    let d = get16(t.od_c, t.od_b, t.odiv, t.n_o, p);
    let ck = get32(t.oc_c, t.oc_b, t.odiv, t.n_o, p);
    let ok = t.lo_day <= d && d < t.hi_day && 1 <= ck && (ck as u64) <= (t.n_c as u64);
    let c: usize = if ok { (ck - 1) as usize } else { 0 };
    proof {
        assert(cmap_has(ms@, cmd.bs as int, c as int));
        assert(cmap_has(ms@, cmd.bs as int, 0));
        assert(cmap_val(ms@, cmd.bs as int, c as int) == qvl(qkey@, fv8(t.cn_c@, t.cn_b@, t.cdiv.bs as int, c as int)));
    }
    let cv = cmap_get(ms, cmd, c);
    if ok { cv } else { 0 }
}

/// What `ov` shows about an order: a dead key, or the live chain through its customer and entry `ov - 1`.
pub proof fn lemma_ov(t: ScanCtx, qkey: Seq<i64>, qgrp: Seq<usize>, ms: Seq<Vec<u64>>, cmd: Div, sms: Seq<Vec<u64>>, smd: Div, p: int)
    requires
        t.wf(), qlist_ok(t.rs@, t.prm@, qkey, qgrp, t.qrow@, t.gnames@),
        map_ok(t, qkey, ms, cmd, sms, smd, true), t.cdense, 0 <= p < t.n_o,
    ensures
        ov(t, ms, cmd.bs as int, p) == 0 ==> key_dead(t.rs@, t.prm@, t.orows@[p][0]),
        ov(t, ms, cmd.bs as int, p) != 0 ==> ({
            let v = ov(t, ms, cmd.bs as int, p);
            let qq = v - 1;
            let ci = fv32(t.oc_c@, t.oc_b@, t.odiv.bs as int, p) - 1;
            &&& 0 <= qq < qkey.len()
            &&& order_live(t.rs@, t.prm@, qkey, qgrp, t.orows@[p][0], t.omap@[p], ci, qq, qkey[qq])
            &&& qgrp[qq] < t.gnames@.len()
            &&& v == qvl(qkey, qkey[qq] as int)
        }),
{
    let rs = t.rs@;
    let prm = t.prm@;
    let oi = t.omap@[p];
    let bs = t.odiv.bs as int;
    let d = fv16(t.od_c@, t.od_b@, bs, p);
    let ck = fv32(t.oc_c@, t.oc_b@, bs, p);
    assert(t.orow_ok(p));
    lemma_window(&t, rs.o[oi], d);
    if !(t.lo_day <= d < t.hi_day) {
        lemma_dead_window(rs, prm, oi);
    } else if !(1 <= ck <= t.n_c) {
        assert forall|i: int| 0 <= i < rs.c.len() implies #[trigger] rs.c[i][0] != rs.o[oi][1] by {
            assert(t.crow_ok(i));
        }
        lemma_dead_no_customer(rs, prm, oi);
    } else {
        let c = ck - 1;
        assert(t.crow_ok(c));
        let cnk = fv8(t.cn_c@, t.cn_b@, t.cdiv.bs as int, c);
        assert(cmap_val(ms, cmd.bs as int, c) == qvl(qkey, cnk));
        lemma_qvl(qkey, cnk);
        let v = qvl(qkey, cnk);
        if v == 0 {
            assert(i64::MIN <= cnk <= i64::MAX);
            let ck8 = cnk as i64;
            assert forall|q: int| 0 <= q < qkey.len() implies #[trigger] qkey[q] != ck8 by {
                assert(qkey[q] as int != cnk);
            }
            lemma_dead_nation(rs, prm, qkey, qgrp, t.qrow@, t.gnames@, oi, c, ck8);
        } else {
            let qq = v - 1;
            assert(qentry_ok(rs, prm, qkey, qgrp, t.qrow@, t.gnames@, qq as int));
            assert(qkey[qq as int] as int == cnk);
        }
    }
}

/// Stored lineitem row `j` of stored orders row `p` (map value `v`): whether its supplier is in the customer's
/// nation, and the group.
pub fn fast_line(t: &ScanCtx, qkey: &Vec<i64>, qgrp: &Vec<usize>, ms: &Vec<Vec<u64>>, cmd: Div, sms: &Vec<Vec<u64>>, smd: Div,
    j: usize, p: usize, v: u64) -> (r: (bool, usize))
    requires
        t.wf(), qlist_ok(t.rs@, t.prm@, qkey@, qgrp@, t.qrow@, t.gnames@),
        map_ok(*t, qkey@, ms@, cmd, sms@, smd, true),
        t.cdense, t.sdense, t.n_s >= 1,
        j < t.n_l, p < t.n_o, t.lrows@[j as int][0] == t.orows@[p as int][0],
        v == ov(*t, ms@, cmd.bs as int, p as int),
    ensures
        r.0 ==> r.1 < t.gnames@.len(),
        forall|gi: int| 0 <= gi < t.gnames@.len() ==>
            #[trigger] line_mult(t.rs@, t.prm@, gkey(t.gnames@, gi), t.lrows@[j as int])
                == if r.0 && gi == r.1 { 1int } else { 0int },
    no_unwind
{
    let ghost rs = t.rs@;
    let ghost prm = t.prm@;
    let ghost gn = t.gnames@;
    let ghost l = t.lrows@[j as int];
    proof {
        assert(t.lrow_ok(j as int));
        lemma_ov(*t, qkey@, qgrp@, ms@, cmd, sms@, smd, p as int);
    }
    let sk = get32(t.ls_c, t.ls_b, t.ldiv, t.n_l, j);
    let live = v != 0;
    let sok = 1 <= sk && (sk as u64) <= (t.n_s as u64);
    let s0: usize = if live && sok { (sk - 1) as usize } else { 0 };
    proof {
        assert(cmap_has(sms@, smd.bs as int, s0 as int));
        assert(cmap_has(sms@, smd.bs as int, 0));
        assert(cmap_val(sms@, smd.bs as int, s0 as int) == qvl(qkey@, fv8(t.sn_c@, t.sn_b@, t.sdiv.bs as int, s0 as int)));
    }
    let s_in = live && sok;
    let s: usize = s0;
    let sv = cmap_get(sms, smd, s);
    if s_in && sv == v {
        let qq = (v - 1) as usize;
        let g = qgrp[qq];
        proof {
            let oi = t.omap@[p as int];
            let ci = fv32(t.oc_c@, t.oc_b@, t.odiv.bs as int, p as int) - 1;
            let cnk = qkey@[qq as int];
            let snk = fv8(t.sn_c@, t.sn_b@, t.sdiv.bs as int, s as int);
            assert(t.srow_ok(s as int));
            assert(cmap_val(sms@, smd.bs as int, s as int) == qvl(qkey@, snk));
            lemma_qvl(qkey@, snk);
            lemma_qvl(qkey@, cnk as int);
            assert(snk == cnk as int);
            assert forall|gi: int| 0 <= gi < gn.len() implies
                #[trigger] line_mult(rs, prm, gkey(gn, gi), l) == if true && gi == g { 1int } else { 0int } by {
                lemma_line_hit(rs, prm, qkey@, qgrp@, t.qrow@, gn, l, oi, ci, qq as int, cnk, s as int, gkey(gn, gi));
                lemma_gkey_eq(gn, gi, g as int);
            }
        }
        (true, g)
    } else {
        proof {
            if !live {
                assert forall|gi: int| 0 <= gi < gn.len() implies
                    #[trigger] line_mult(rs, prm, gkey(gn, gi), l) == if false && gi == 0 { 1int } else { 0int } by {
                    assert(line_mult(rs, prm, gkey(gn, gi), l) == 0);
                }
            } else {
                let qq = (v - 1) as int;
                let oi = t.omap@[p as int];
                let ci = fv32(t.oc_c@, t.oc_b@, t.odiv.bs as int, p as int) - 1;
                let cnk = qkey@[qq];
                if !sok {
                    assert forall|i: int| 0 <= i < rs.s.len() implies #[trigger] rs.s[i][0] != l[2] by {
                        assert(t.srow_ok(i));
                    }
                } else {
                    let snk = fv8(t.sn_c@, t.sn_b@, t.sdiv.bs as int, s0 as int);
                    assert(t.srow_ok(s0 as int));
                    assert(cmap_val(sms@, smd.bs as int, s0 as int) == qvl(qkey@, snk));
                    lemma_qvl(qkey@, snk);
                    lemma_qvl(qkey@, cnk as int);
                    assert(snk != cnk as int);
                    assert(rs.s[s0 as int][0] == l[2] && rs.s[s0 as int][3] != Val::Int(cnk as int));
                }
                assert forall|gi: int| 0 <= gi < gn.len() implies
                    #[trigger] line_mult(rs, prm, gkey(gn, gi), l) == if false && gi == 0 { 1int } else { 0int } by {
                    lemma_line_miss(rs, prm, qkey@, qgrp@, t.qrow@, gn, l, oi, ci, qq, cnk, gkey(gn, gi));
                }
            }
        }
        (false, 0)
    }
}

/// Add stored lineitem row `j` (multiplicity 1 in group `g` when `hit`, else 0 everywhere) to the accumulators.
pub fn acc_line(t: &ScanCtx, cnt: &mut Vec<usize>, sum: &mut Vec<i128>, abs: &mut Vec<u128>, ovf: &mut Vec<bool>,
    ja: usize, j: usize, hit: bool, g: usize)
    requires
        t.wf(), ja <= j < t.n_l,
        old(cnt)@.len() == t.gnames@.len() && old(sum)@.len() == t.gnames@.len()
            && old(abs)@.len() == t.gnames@.len() && old(ovf)@.len() == t.gnames@.len(),
        forall|gi: int| 0 <= gi < t.gnames@.len() ==>
            #[trigger] t.acc_ok(gi, ja as int, j as int, old(cnt)@[gi], old(sum)@[gi], old(abs)@[gi], old(ovf)@[gi]),
        hit ==> g < t.gnames@.len(),
        forall|gi: int| 0 <= gi < t.gnames@.len() ==>
            #[trigger] line_mult(t.rs@, t.prm@, gkey(t.gnames@, gi), t.lrows@[j as int]) == if hit && gi == g { 1int } else { 0int },
    ensures
        final(cnt)@.len() == t.gnames@.len() && final(sum)@.len() == t.gnames@.len()
            && final(abs)@.len() == t.gnames@.len() && final(ovf)@.len() == t.gnames@.len(),
        forall|gi: int| 0 <= gi < t.gnames@.len() ==>
            #[trigger] t.acc_ok(gi, ja as int, j as int + 1, final(cnt)@[gi], final(sum)@[gi], final(abs)@[gi], final(ovf)@[gi]),
    no_unwind
{
    let ghost rs = t.rs@;
    let ghost prm = t.prm@;
    let ghost gn = t.gnames@;
    let ghost ng = gn.len();
    let ghost l = t.lrows@[j as int];
    let ghost oc = cnt@;
    let ghost osu = sum@;
    let ghost oa = abs@;
    let ghost oo = ovf@;
    if hit {
        let ep = get32(t.le_c, t.le_b, t.ldiv, t.n_l, j);
        let dc = get8(t.ld_c, t.ld_b, t.ldiv, t.n_l, j);
        proof {
            lemma_weights(t, j as int, ep as int, dc as int);
        }
        let (v, a) = revenue(ep, dc);
        proof {
            assert(t.acc_ok(g as int, ja as int, j as int, oc[g as int], osu[g as int], oa[g as int], oo[g as int]));
        }
        if !ovf[g] {
            if abs[g] <= (i128::MAX as u128) - a {
                abs[g] = abs[g] + a;
                sum[g] = sum[g] + v;
                cnt[g] = cnt[g] + 1;
            } else {
                ovf[g] = true;
            }
        }
        proof {
            assert forall|gi: int| 0 <= gi < ng implies
                #[trigger] t.acc_ok(gi, ja as int, j as int + 1, cnt@[gi], sum@[gi], abs@[gi], ovf@[gi]) by {
                let dm = if gi == g { 1int } else { 0int };
                assert(line_mult(rs, prm, gkey(gn, gi), l) == dm);
                lemma_acc_step(t, gi, ja as int, j as int, dm);
                assert(t.lsum(gi, 0, ja as int, j as int + 1) == t.lsum(gi, 0, ja as int, j as int) + dm * wsel(0, l));
                assert(t.lsum(gi, 1, ja as int, j as int + 1) == t.lsum(gi, 1, ja as int, j as int) + dm * wsel(1, l));
                assert(t.lsum(gi, 2, ja as int, j as int + 1) == t.lsum(gi, 2, ja as int, j as int) + dm * wsel(2, l));
                assert(t.acc_ok(gi, ja as int, j as int, oc[gi], osu[gi], oa[gi], oo[gi]));
            }
        }
    } else {
        proof {
            assert forall|gi: int| 0 <= gi < ng implies
                #[trigger] t.acc_ok(gi, ja as int, j as int + 1, cnt@[gi], sum@[gi], abs@[gi], ovf@[gi]) by {
                assert(line_mult(rs, prm, gkey(gn, gi), l) == 0);
                lemma_acc_step(t, gi, ja as int, j as int, 0);
                assert(t.lsum(gi, 0, ja as int, j as int + 1) == t.lsum(gi, 0, ja as int, j as int));
                assert(t.lsum(gi, 1, ja as int, j as int + 1) == t.lsum(gi, 1, ja as int, j as int));
                assert(t.lsum(gi, 2, ja as int, j as int + 1) == t.lsum(gi, 2, ja as int, j as int));
                assert(t.acc_ok(gi, ja as int, j as int, oc[gi], osu[gi], oa[gi], oo[gi]));
            }
        }
    }
}

/// `y` is in block `blk` of size `bs`.
pub proof fn lemma_in_blk(y: int, bs: int, blk: int)
    requires bs >= 1, blk >= 0, blk * bs <= y < blk * bs + bs,
    ensures y / bs == blk,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(y, bs);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(y, bs);
    let q = y / bs;
    assert(bs * q == q * bs) by (nonlinear_arith);
    if q < blk {
        assert(q * bs + bs <= blk * bs) by (nonlinear_arith) requires q < blk, bs >= 1;
    }
    if q > blk {
        assert(q * bs >= blk * bs + bs) by (nonlinear_arith) requires q > blk, bs >= 1;
    }
}

/// The end of the run of stored lineitem rows from `j` (below `jb`) whose order key is `key`: within a block of
/// rows (one base) the codes are compared with `key - base`.
fn skip_run(t: &ScanCtx, j: usize, jb: usize, key: i64) -> (r: usize)
    requires t.wf(), j <= jb <= t.n_l,
    ensures
        j <= r <= jb,
        forall|x: int| j <= x < r ==> (#[trigger] t.lrows@[x])[0] == Val::Int(key as int),
        r < jb ==> t.lrows@[r as int][0] != Val::Int(key as int),
    no_unwind
{
    let bs = t.ldiv.bs;
    let mut x = j;
    let mut done = false;
    while x < jb && !done
        invariant
            t.wf(), j <= x <= jb <= t.n_l, bs == t.ldiv.bs,
            forall|y: int| j <= y < x ==> (#[trigger] t.lrows@[y])[0] == Val::Int(key as int),
            done ==> x < jb && t.lrows@[x as int][0] != Val::Int(key as int),
        decreases jb - x + (if done { 0int } else { 1int }),
    {
        let blk = div_of(t.ldiv, x);
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, bs as int);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(x as int, bs as int);
            assert(bs * blk == blk * bs) by (nonlinear_arith);
            lemma_block_index(x as int, bs as int, t.lk_b@.len() as int);
        }
        let off = x - blk * bs;
        let rem = bs - off;
        let bend = if rem < jb - x { x + rem } else { jb };
        let base = t.lk_b[blk];
        let kc = key as i128 - base as i128;
        if kc < 0 || kc > 0xffff_ffff {
            proof {
                assert(t.lrow_ok(x as int));
                assert(x as int / bs as int == blk);
            }
            done = true;
        } else {
            let k32 = kc as u32;
            let mut y = x;
            while y < bend && t.lk_c[y] == k32
                invariant
                    t.wf(), j <= x <= y <= bend <= jb <= t.n_l, bs == t.ldiv.bs, bs >= 1,
                    blk * bs <= x, bend <= blk * bs + bs, blk < t.lk_b@.len(),
                    base == t.lk_b@[blk as int], k32 as int == key as int - base as int,
                    forall|z: int| j <= z < y ==> (#[trigger] t.lrows@[z])[0] == Val::Int(key as int),
                decreases bend - y,
            {
                proof {
                    lemma_in_blk(y as int, bs as int, blk as int);
                    assert(t.lrow_ok(y as int));
                }
                y = y + 1;
            }
            if y < bend {
                proof {
                    lemma_in_blk(y as int, bs as int, blk as int);
                    assert(t.lrow_ok(y as int));
                }
                done = true;
            }
            x = y;
        }
    }
    x
}

/// Rows `[j0, j1)` of a dead order key leave every accumulator as it is.
proof fn lemma_dead_run(t: ScanCtx, ja: int, j0: int, j1: int, kv: Val,
    cnt: Seq<usize>, sum: Seq<i128>, abs: Seq<u128>, ovf: Seq<bool>)
    requires
        t.wf(), 0 <= ja <= j0 <= j1 <= t.n_l,
        forall|x: int| j0 <= x < j1 ==> (#[trigger] t.lrows@[x])[0] == kv,
        key_dead(t.rs@, t.prm@, kv),
        cnt.len() == t.gnames@.len() && sum.len() == t.gnames@.len() && abs.len() == t.gnames@.len() && ovf.len() == t.gnames@.len(),
        forall|gi: int| 0 <= gi < t.gnames@.len() ==> #[trigger] t.acc_ok(gi, ja, j0, cnt[gi], sum[gi], abs[gi], ovf[gi]),
    ensures
        forall|gi: int| 0 <= gi < t.gnames@.len() ==> #[trigger] t.acc_ok(gi, ja, j1, cnt[gi], sum[gi], abs[gi], ovf[gi]),
{
    assert forall|gi: int| 0 <= gi < t.gnames@.len() implies #[trigger] t.acc_ok(gi, ja, j1, cnt[gi], sum[gi], abs[gi], ovf[gi]) by {
        assert(t.acc_ok(gi, ja, j0, cnt[gi], sum[gi], abs[gi], ovf[gi]));
        assert forall|m: int| #[trigger] t.lsum(gi, m, ja, j1) == t.lsum(gi, m, ja, j0) by {
            let f = contrib_fn(t.rs@, t.prm@, gkey(t.gnames@, gi), m);
            assert forall|x: int| j0 <= x < j1 implies f(#[trigger] t.lrows@[x]) == 0 by {
                assert(t.lrows@[x][0] == kv);
                assert(line_mult(t.rs@, t.prm@, gkey(t.gnames@, gi), t.lrows@[x]) == 0);
            }
            lemma_sum_range_zero(t.lrows@, f, j0, j1);
            lemma_sum_range_split(t.lrows@, f, ja, j0, j1);
        }
        assert(t.lsum(gi, 0, ja, j1) == t.lsum(gi, 0, ja, j0));
        assert(t.lsum(gi, 1, ja, j1) == t.lsum(gi, 1, ja, j0));
        assert(t.lsum(gi, 2, ja, j1) == t.lsum(gi, 2, ja, j0));
    }
}

/// The task on the fast path.
fn scan_fast(task: ScanTask) -> (out: ScanOut)
    requires
        task.pre(),
        task.ctx.clustered, task.use_map, task.ctx.cdense, task.ctx.sdense,
        task.ctx.n_c >= 1, task.ctx.n_s >= 1, task.vbuf@.len() >= 1,
    ensures task.post(out),
    no_unwind
{
    let ghost task0 = task;
    let ScanTask { ctx, qkey, qgrp, cm, cmd, sm, smd, use_map, vbuf, lp, obuf, hb, hg, pa, pb, cnt, sum, abs, ovf } = task;
    let t = ctx;
    let ms: &Vec<Vec<u64>> = &*cm;
    let sms: &Vec<Vec<u64>> = &*sm;
    let ghost rs = t.rs@;
    let ghost prm = t.prm@;
    let ghost gn = t.gnames@;
    let ghost ng = gn.len();
    let mut cnt = cnt;
    let mut sum = sum;
    let mut abs = abs;
    let mut ovf = ovf;
    let mut vbuf = vbuf;
    let ob = vbuf.len();
    let ja = line_start(&t, pa);
    let jb = line_start(&t, pb);
    proof {
        if ja > jb {
            assert(t.split_at(pa as int, ja as int));
            assert(t.split_at(pb as int, jb as int));
            assert(t.op(jb as int) < pa);
            assert(t.op(jb as int) >= pb);
        }
        assert forall|gi: int| 0 <= gi < ng implies
            #[trigger] t.acc_ok(gi, ja as int, ja as int, cnt@[gi], sum@[gi], abs@[gi], ovf@[gi]) by {
            assert forall|m: int| #[trigger] t.lsum(gi, m, ja as int, ja as int) == 0 by {
                lemma_sum_range_empty(t.lrows@, contrib_fn(rs, prm, gkey(gn, gi), m), ja as int);
            }
        }
        if ja < jb {
            assert(t.split_at(pa as int, ja as int));
            assert(t.op(ja as int) >= pa);
        }
    }
    let mut j = ja;
    let mut qa = pa;
    while j < jb
        invariant
            t.wf(),
            qlist_ok(rs, prm, qkey@, qgrp@, t.qrow@, gn),
            map_ok(t, qkey@, ms@, cmd, sms@, smd, true),
            t.clustered, t.cdense, t.sdense, t.n_c >= 1, t.n_s >= 1,
            rs == t.rs@, prm == t.prm@, gn == t.gnames@, ng == gn.len(),
            ob == vbuf@.len(), ob >= 1,
            ja <= j <= jb <= t.n_l,
            t.split_at(pa as int, ja as int) && t.split_at(pb as int, jb as int),
            pb <= t.n_o, pa <= qa <= pb,
            j < jb ==> qa <= t.op(j as int),
            ng == cnt@.len() && ng == sum@.len() && ng == abs@.len() && ng == ovf@.len(),
            forall|gi: int| 0 <= gi < ng ==>
                #[trigger] t.acc_ok(gi, ja as int, j as int, cnt@[gi], sum@[gi], abs@[gi], ovf@[gi]),
        decreases pb - qa,
    {
        proof {
            assert(t.op(j as int) < pb);
        }
        let qb = if pb - qa < ob { pb } else { qa + ob };
        // the map values of the block's orders
        let mut i: usize = 0;
        while i < qb - qa
            invariant
                t.wf(), map_ok(t, qkey@, ms@, cmd, sms@, smd, true), t.n_c >= 1,
                qa < qb <= pb <= t.n_o, qb - qa <= ob, ob == vbuf@.len(),
                i <= qb - qa,
                forall|x: int| 0 <= x < i ==> #[trigger] vbuf@[x] as u64 == ov(t, ms@, cmd.bs as int, qa + x),
            decreases qb - qa - i,
        {
            let v = order_v(&t, &qkey, ms, cmd, sms, smd, qa + i);
            proof {
                lemma_cmap_val_small(ms@, cmd.bs as int, t, qa + i);
            }
            let ghost vb0 = vbuf@;
            vbuf[i] = v as u8;
            proof {
                assert forall|x: int| 0 <= x < i + 1 implies #[trigger] vbuf@[x] as u64 == ov(t, ms@, cmd.bs as int, qa + x) by {
                    if x < i {
                        assert(vbuf@[x] == vb0[x]);
                    }
                }
            }
            i = i + 1;
        }
        // the block's orders, each with its run of lineitem rows
        let mut p = qa;
        while p < qb && j < jb
            invariant
                t.wf(),
                qlist_ok(rs, prm, qkey@, qgrp@, t.qrow@, gn),
                map_ok(t, qkey@, ms@, cmd, sms@, smd, true),
                t.clustered, t.cdense, t.sdense, t.n_c >= 1, t.n_s >= 1,
                rs == t.rs@, prm == t.prm@, gn == t.gnames@, ng == gn.len(),
                ob == vbuf@.len(),
                ja <= j <= jb <= t.n_l,
                t.split_at(pa as int, ja as int) && t.split_at(pb as int, jb as int),
                pb <= t.n_o, pa <= qa <= p, p <= qb, qb <= pb, qb - qa <= ob,
                forall|x: int| 0 <= x < qb - qa ==> #[trigger] vbuf@[x] as u64 == ov(t, ms@, cmd.bs as int, qa + x),
                j < jb ==> p <= t.op(j as int),
                ng == cnt@.len() && ng == sum@.len() && ng == abs@.len() && ng == ovf@.len(),
                forall|gi: int| 0 <= gi < ng ==>
                    #[trigger] t.acc_ok(gi, ja as int, j as int, cnt@[gi], sum@[gi], abs@[gi], ovf@[gi]),
            decreases qb - p,
        {
            let key = get32(t.ok_c, t.ok_b, t.odiv, t.n_o, p);
            let v = vbuf[p - qa] as u64;
            let ghost kv = t.orows@[p as int][0];
            proof {
                assert(t.orow_ok(p as int));
                assert(kv == Val::Int(key as int));
                assert(vbuf@[(p - qa) as int] as u64 == ov(t, ms@, cmd.bs as int, qa + (p - qa)));
                lemma_ov(t, qkey@, qgrp@, ms@, cmd, sms@, smd, p as int);
            }
            let ghost j0 = j;
            let j2 = skip_run(&t, j, jb, key);
            if v == 0 {
                // a dead order: its rows take part in no group
                proof {
                    lemma_dead_run(t, ja as int, j0 as int, j2 as int, kv, cnt@, sum@, abs@, ovf@);
                }
                j = j2;
            } else {
                while j < j2
                    invariant
                        t.wf(),
                        qlist_ok(rs, prm, qkey@, qgrp@, t.qrow@, gn),
                        map_ok(t, qkey@, ms@, cmd, sms@, smd, true),
                        t.cdense, t.sdense, t.n_s >= 1,
                        rs == t.rs@, prm == t.prm@, gn == t.gnames@, ng == gn.len(),
                        ja <= j0 <= j <= j2 <= jb, jb <= t.n_l, p < t.n_o,
                        forall|x: int| j0 <= x < j2 ==> (#[trigger] t.lrows@[x])[0] == kv,
                        kv == t.orows@[p as int][0], kv == Val::Int(key as int),
                        v == ov(t, ms@, cmd.bs as int, p as int),
                        ng == cnt@.len() && ng == sum@.len() && ng == abs@.len() && ng == ovf@.len(),
                        forall|gi: int| 0 <= gi < ng ==>
                            #[trigger] t.acc_ok(gi, ja as int, j as int, cnt@[gi], sum@[gi], abs@[gi], ovf@[gi]),
                    decreases j2 - j,
                {
                    proof {
                        assert(t.lrows@[j as int][0] == kv);
                    }
                    let (hit, g) = fast_line(&t, &qkey, &qgrp, ms, cmd, sms, smd, j, p, v);
                    acc_line(&t, &mut cnt, &mut sum, &mut abs, &mut ovf, ja, j, hit, g);
                    j = j + 1;
                }
            }
            proof {
                // the next row (if any) belongs to a later order
                if j < jb {
                    let opj = t.op(j as int);
                    assert(t.lrow_ok(j as int));
                    lemma_fkf(t.orows@, t.lrows@[j as int][0], 0);
                    assert(t.split_at(pb as int, jb as int));
                    assert(opj < pb);
                    assert(t.lrows@[j as int][0] != kv);
                    assert(j == j2);
                    if j > j0 {
                        assert(t.lrows@[j as int - 1][0] == kv);
                        lemma_clustered_le(t.lrows@, t.orows@, j as int - 1, j as int);
                        assert forall|q: int| 0 <= q < t.orows@.len() && q != p implies #[trigger] t.orows@[q][0] != kv by {
                            if t.orows@[q][0] == kv {
                                assert(t.orows@[q][0] == t.orows@[p as int][0]);
                            }
                        }
                        lemma_order_pos_at(t.orows@, kv, p as int);
                        assert(t.op(j as int - 1) == p);
                    }
                    assert(p <= opj);
                    assert(t.orows@[opj][0] == t.lrows@[j as int][0]);
                    assert(opj != p);
                }
            }
            p = p + 1;
        }
        qa = qb;
    }
    ScanOut { ja, jb, cnt, sum, abs, ovf, touch: 0 }
}

/// A map value is below 16 (it fits a byte).
pub proof fn lemma_cmap_val_small(ms: Seq<Vec<u64>>, cw: int, t: ScanCtx, p: int)
    ensures ov(t, ms, cw, p) < 16,
{
    let bs = t.odiv.bs as int;
    let ck = fv32(t.oc_c@, t.oc_b@, bs, p);
    let c = ck - 1;
    lemma_nib_lt16(ms[(c / 16) / cw]@[(c / 16) % cw], (c % 16) as u64);
}

impl WorkerTask for ScanTask {
    type Output = ScanOut;

    open spec fn pre(&self) -> bool {
        let t = self.ctx;
        let ng = t.gnames@.len();
        &&& t.wf()
        &&& qlist_ok(t.rs@, t.prm@, self.qkey@, self.qgrp@, t.qrow@, t.gnames@)
        &&& map_ok(t, self.qkey@, (*self.cm)@, self.cmd, (*self.sm)@, self.smd, self.use_map)
        &&& ng == self.cnt@.len() && ng == self.sum@.len() && ng == self.abs@.len() && ng == self.ovf@.len()
        &&& forall|gi: int| 0 <= gi < ng ==> self.cnt@[gi] == 0 && self.sum@[gi] == 0 && self.abs@[gi] == 0 && !self.ovf@[gi]
        &&& self.pa <= self.pb
        &&& t.clustered ==> self.pb <= t.n_o
        &&& !t.clustered ==> self.pb <= t.n_l
    }

    open spec fn post(&self, out: ScanOut) -> bool {
        let t = self.ctx;
        let ng = t.gnames@.len();
        &&& out.ja <= out.jb <= t.n_l
        &&& t.clustered ==> t.split_at(self.pa as int, out.ja as int) && t.split_at(self.pb as int, out.jb as int)
        &&& !t.clustered ==> out.ja == self.pa && out.jb == self.pb
        &&& ng == out.cnt@.len() && ng == out.sum@.len() && ng == out.abs@.len() && ng == out.ovf@.len()
        &&& forall|gi: int| 0 <= gi < ng ==>
                #[trigger] t.acc_ok(gi, out.ja as int, out.jb as int, out.cnt@[gi], out.sum@[gi], out.abs@[gi], out.ovf@[gi])
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.pa as u64, self.pb as u64)
    }

    fn run(self) -> (out: ScanOut) {
        if self.ctx.clustered && self.use_map && self.ctx.cdense && self.ctx.sdense && self.ctx.n_c >= 1
            && self.ctx.n_s >= 1 && self.vbuf.len() >= 1 {
            if self.lp.len() == self.vbuf.len() && self.obuf.len() == self.vbuf.len()
                && self.hg.len() == self.hb.len() && self.cmd.p2 && self.smd.p2 && self.ctx.ldiv.p2
                && crate::agent::live::check_aligned(&self.ctx, self.pa)
                && crate::agent::live::check_aligned(&self.ctx, self.pb) {
                return crate::agent::live::scan_live(self);
            }
            return scan_fast(self);
        }
        let ScanTask { ctx, qkey, qgrp, cm, cmd, sm, smd, use_map, vbuf, lp, obuf, hb, hg, pa, pb, cnt, sum, abs, ovf } = self;
        let t = ctx;
        let ms: &Vec<Vec<u64>> = &*cm;
        let sms: &Vec<Vec<u64>> = &*sm;
        let ghost rs = t.rs@;
        let ghost prm = t.prm@;
        let ghost gn = t.gnames@;
        let ghost ng = gn.len();
        let mut cnt = cnt;
        let mut sum = sum;
        let mut abs = abs;
        let mut ovf = ovf;
        let ja = if t.clustered { line_start(&t, pa) } else { pa };
        let jb = if t.clustered { line_start(&t, pb) } else { pb };
        proof {
            if t.clustered && ja > jb {
                assert(t.split_at(pa as int, ja as int));
                assert(t.split_at(pb as int, jb as int));
                assert(t.op(jb as int) < pa);
                assert(t.op(jb as int) >= pb);
            }
            assert forall|gi: int| 0 <= gi < ng implies
                #[trigger] t.acc_ok(gi, ja as int, ja as int, cnt@[gi], sum@[gi], abs@[gi], ovf@[gi]) by {
                assert forall|m: int| #[trigger] t.lsum(gi, m, ja as int, ja as int) == 0 by {
                    lemma_sum_range_empty(t.lrows@, contrib_fn(rs, prm, gkey(gn, gi), m), ja as int);
                }
            }
        }
        let mut j = ja;
        let mut p = pa;
        let mut have = false;
        let mut cur_key: i64 = 0;
        let mut cur_live = false;
        let mut cur_q: usize = 0;
        let mut cur_cnk: i64 = 0;
        let mut cur_v: u64 = 0;
        let ghost mut oi: int = 0;
        let ghost mut ci: int = 0;
        let ghost mut qq: int = 0;
        while j < jb
            invariant
                t.wf(),
                qlist_ok(rs, prm, qkey@, qgrp@, t.qrow@, gn),
                map_ok(t, qkey@, ms@, cmd, sms@, smd, use_map),
                rs == t.rs@, prm == t.prm@, gn == t.gnames@, ng == gn.len(),
                ja <= j <= jb <= t.n_l,
                t.clustered ==> t.split_at(pa as int, ja as int) && t.split_at(pb as int, jb as int),
                t.clustered ==> pb <= t.n_o,
                !t.clustered ==> ja == pa && jb == pb,
                ng == cnt@.len() && ng == sum@.len() && ng == abs@.len() && ng == ovf@.len(),
                forall|gi: int| 0 <= gi < ng ==>
                    #[trigger] t.acc_ok(gi, ja as int, j as int, cnt@[gi], sum@[gi], abs@[gi], ovf@[gi]),
                t.clustered && j < jb ==> pa <= p <= t.op(j as int),
                t.clustered && have ==> p < t.n_o && t.orows@[p as int][0] == Val::Int(cur_key as int),
                have && !cur_live ==> key_dead(rs, prm, Val::Int(cur_key as int)),
                have && cur_live ==> cur_q < ng
                    && order_live(rs, prm, qkey@, qgrp@, Val::Int(cur_key as int), oi, ci, qq, cur_cnk)
                    && qgrp@[qq] == cur_q,
                have && cur_live && use_map ==> cur_v != 0 && cur_v == qvl(qkey@, cur_cnk as int),
            decreases jb - j,
        {
            let k = get32(t.lk_c, t.lk_b, t.ldiv, t.n_l, j);
            proof {
                assert(t.lrow_ok(j as int));
            }
            let ghost l = t.lrows@[j as int];
            if !have || k != cur_key {
                // locate the order of key k
                if t.clustered {
                    let ghost opj = t.op(j as int);
                    proof {
                        assert(t.split_at(pb as int, jb as int));
                        assert(opj < pb);
                        lemma_fkf(t.orows@, l[0], 0);
                        assert(t.orows@[opj][0] == Val::Int(k as int));
                    }
                    if have {
                        proof {
                            if p as int == opj {
                                assert(t.orows@[p as int][0] == Val::Int(cur_key as int));
                            }
                        }
                        p = p + 1;
                    }
                    while get32(t.ok_c, t.ok_b, t.odiv, t.n_o, p) != k
                        invariant
                            t.wf(),
                            pa <= p <= opj < pb <= t.n_o,
                            opj == t.op(j as int),
                            t.orows@[opj][0] == Val::Int(k as int),
                        decreases opj - p,
                    {
                        proof {
                            assert(t.orow_ok(p as int));
                            assert(t.orow_ok(opj));
                        }
                        p = p + 1;
                    }
                    proof {
                        assert(t.orow_ok(p as int));
                        assert(t.orows@[p as int][0] == Val::Int(k as int));
                        assert(t.orows@[p as int][0] == t.orows@[opj][0]);
                        assert(p as int == opj);
                    }
                    let (live, q, cnk, g_oi, g_ci, g_qq, v) = eval_order(&t, &qkey, &qgrp, ms, cmd, sms, smd, use_map, p);
                    cur_live = live;
                    cur_q = q;
                    cur_cnk = cnk;
                    cur_v = v;
                    proof {
                        oi = g_oi@;
                        ci = g_ci@;
                        qq = g_qq@;
                    }
                } else {
                    let (live, q, cnk, g_oi, g_ci, g_qq, v) = eval_key(&t, &qkey, &qgrp, ms, cmd, sms, smd, use_map, k);
                    cur_live = live;
                    cur_q = q;
                    cur_cnk = cnk;
                    cur_v = v;
                    proof {
                        oi = g_oi@;
                        ci = g_ci@;
                        qq = g_qq@;
                    }
                }
                have = true;
                cur_key = k;
            }
            // the row's contribution: 1 in group `cur_q` when the supplier is in the customer's nation
            let hit = if cur_live {
                line_hit(&t, &qkey, &qgrp, ms, cmd, sms, smd, use_map, j, cur_q, cur_cnk, cur_v, Ghost(oi), Ghost(ci), Ghost(qq))
            } else {
                proof {
                    assert forall|gi: int| 0 <= gi < ng implies
                        #[trigger] line_mult(rs, prm, gkey(gn, gi), l) == if false && gi == cur_q { 1int } else { 0int } by {
                        assert(line_mult(rs, prm, gkey(gn, gi), l) == 0);
                    }
                }
                false
            };
            let ghost oc = cnt@;
            let ghost osu = sum@;
            let ghost oa = abs@;
            let ghost oo = ovf@;
            if hit {
                let ep = get32(t.le_c, t.le_b, t.ldiv, t.n_l, j);
                let dc = get8(t.ld_c, t.ld_b, t.ldiv, t.n_l, j);
                proof {
                    lemma_weights(&t, j as int, ep as int, dc as int);
                }
                let (v, a) = revenue(ep, dc);
                let g = cur_q;
                proof {
                    assert(t.acc_ok(g as int, ja as int, j as int, oc[g as int], osu[g as int], oa[g as int], oo[g as int]));
                }
                if !ovf[g] {
                    if abs[g] <= (i128::MAX as u128) - a {
                        abs[g] = abs[g] + a;
                        sum[g] = sum[g] + v;
                        cnt[g] = cnt[g] + 1;
                    } else {
                        ovf[g] = true;
                    }
                }
                proof {
                    assert forall|gi: int| 0 <= gi < ng implies
                        #[trigger] t.acc_ok(gi, ja as int, j as int + 1, cnt@[gi], sum@[gi], abs@[gi], ovf@[gi]) by {
                        let dm = if gi == g { 1int } else { 0int };
                        assert(line_mult(rs, prm, gkey(gn, gi), l) == dm);
                        lemma_acc_step(&t, gi, ja as int, j as int, dm);
                        assert(t.lsum(gi, 0, ja as int, j as int + 1) == t.lsum(gi, 0, ja as int, j as int) + dm * wsel(0, l));
                        assert(t.lsum(gi, 1, ja as int, j as int + 1) == t.lsum(gi, 1, ja as int, j as int) + dm * wsel(1, l));
                        assert(t.lsum(gi, 2, ja as int, j as int + 1) == t.lsum(gi, 2, ja as int, j as int) + dm * wsel(2, l));
                        assert(t.acc_ok(gi, ja as int, j as int, oc[gi], osu[gi], oa[gi], oo[gi]));
                    }
                }
            } else {
                proof {
                    assert forall|gi: int| 0 <= gi < ng implies
                        #[trigger] t.acc_ok(gi, ja as int, j as int + 1, cnt@[gi], sum@[gi], abs@[gi], ovf@[gi]) by {
                        assert(line_mult(rs, prm, gkey(gn, gi), l) == 0);
                        lemma_acc_step(&t, gi, ja as int, j as int, 0);
                        assert(t.lsum(gi, 0, ja as int, j as int + 1) == t.lsum(gi, 0, ja as int, j as int));
                        assert(t.lsum(gi, 1, ja as int, j as int + 1) == t.lsum(gi, 1, ja as int, j as int));
                        assert(t.lsum(gi, 2, ja as int, j as int + 1) == t.lsum(gi, 2, ja as int, j as int));
                        assert(t.acc_ok(gi, ja as int, j as int, oc[gi], osu[gi], oa[gi], oo[gi]));
                    }
                }
            }
            proof {
                if t.clustered && j + 1 < jb {
                    lemma_clustered_le(t.lrows@, t.orows@, j as int, j as int + 1);
                    assert(t.split_at(pa as int, ja as int));
                    assert(t.op(j as int + 1) >= pa);
                    // the current order is the order of row j
                    assert(t.orows@[p as int][0] == l[0]);
                    assert forall|q: int| 0 <= q < t.orows@.len() && q != p implies #[trigger] t.orows@[q][0] != l[0] by {
                        if t.orows@[q][0] == l[0] {
                            assert(t.orows@[q][0] == t.orows@[p as int][0]);
                        }
                    }
                    lemma_order_pos_at(t.orows@, l[0], p as int);
                }
            }
            j = j + 1;
        }
        ScanOut { ja, jb, cnt, sum, abs, ovf, touch: 0 }
    }
}

/// One worker task: the shared context, its own copy of the qualifying list, its range and its accumulators.
pub struct ScanTask {
    pub ctx: ScanCtx,
    pub qkey: Vec<i64>,
    pub qgrp: Vec<usize>,
    /// the shared customer map (`cmap`), when `use_map`
    pub cm: Arc<Vec<Vec<u64>>>,
    pub cmd: Div,
    pub sm: Arc<Vec<Vec<u64>>>,
    pub smd: Div,
    pub use_map: bool,
    /// the fast path's per-block map values of orders; the live path's listed orders (same length)
    pub vbuf: Vec<u8>,
    pub lp: Vec<usize>,
    /// the live path's per-batch map values of orders (same length; `live::gather`)
    pub obuf: Vec<u8>,
    /// the live path's hit list: stored lineitem rows and their groups (same length; `hits`)
    pub hb: Vec<usize>,
    pub hg: Vec<usize>,
    pub pa: usize,
    pub pb: usize,
    pub cnt: Vec<usize>,
    pub sum: Vec<i128>,
    pub abs: Vec<u128>,
    pub ovf: Vec<bool>,
}

/// A task's lineitem range and accumulators.
pub struct ScanOut {
    pub ja: usize,
    pub jb: usize,
    pub cnt: Vec<usize>,
    pub sum: Vec<i128>,
    pub abs: Vec<u128>,
    pub ovf: Vec<bool>,
    /// xor of the codes the live path's touch pass read (kept so the reads are not removed)
    pub touch: u32,
}

} // verus!
