//! The index-driven Q8 kernel over storage `factsdir`. A task walks a range of l_partkey directory entries
//! `[e0, e1)` (entry `e` is part key `pkmin + e`) in batches of up to `G` passing entries (`batch_step`):
//! `collect` finds them with `next_pass` (part type codes scanned in 32-byte chunks, `common::chunk::has_u8`; dense
//! part keys: part row `key - pfirst`; no directory offsets read for failing parts), `gather` loads their position
//! ranges `offs[e] .. offs[e + 1]` and the stored row of each range's first position in lean loops (independent
//! cache misses overlap), and `walk_entry` buffers every position's stored lineitem row `s`, counting it only when
//! `s` lies in the order-date range `[la, lb)` (branch-free; rows outside contribute nothing, `run::bounds_ok`).
//! Full buffers of `BATCH` rows are processed by `flush` in 4 stages, each a lean gather loop of independent loads
//! then a filter/compact loop: the order (l_orderkey, then the o_orderkey directory), the order's date and
//! customer, the customer's region (dense customer keys), the supplier's nation, price and discount (dense supplier
//! keys).
//!
//! Every block size is a power of two (`shift_ok`), so group indices are shifts, not divisions.
//!
//! Proof: a task's accumulators are those of its key index positions (`idxspec::acc_idx`); the batch invariant is
//! `acc + acc_rows(buffer) == acc_idx(first position, current position)`; the entries a batch skips fail the filter
//! (`coll_ok`, `gap_fail`) and hold no contributing position (`lemma_entries_none`). The merged tasks cover every
//! position, and the key index is a bijection, so the total is the scan's `acc_range` over every stored row
//! (`lemma_idx_all`).
use vstd::prelude::*;
use vstd::arithmetic::power2::pow2;
use crate::gendb_entry::parallel::{WorkerTask, MAX_WORKERS};
use crate::gendb_entry::work::{filled, put};
use crate::stores::factsdir::interface::dirs::ODIR_NONE;
use crate::stores::factsdir::interface::common::colfmt::is_perm;
use super::sql::*;
use super::model::*;
use super::kernel::*;
use super::idxspec::*;
use super::run::{bounds_ok, acc_merge};
use super::common::chunk::{W8, has_u8};
use super::cbits::{cb_ok, cbit};
use std::sync::Arc;

verus! {

// ------------------------------------------------------------------------------------------------ directories

/// The directory slices: lineitem's l_partkey key index (`ic`, `ib`: position -> stored row), the l_partkey
/// directory (`pkmin`, `offs`), the o_orderkey directory (`okmin`, `orows`), the block-size shifts of lineitem,
/// orders, customer, supplier and part, and the first keys of the dense part, customer and supplier keys.
pub struct Dirs {
    pub ic: &'static [u32],
    pub ib: &'static [u64],
    pub pkmin: i64,
    pub offs: &'static [u32],
    pub okmin: i64,
    pub orows: &'static [u32],
    pub on: usize,
    pub sl: usize,
    pub so: usize,
    pub sc: usize,
    pub ss: usize,
    pub sp: usize,
    pub pfirst: i64,
    pub cfirst: i64,
    pub sfirst: i64,
}

impl Copy for Dirs {}

impl Clone for Dirs {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

/// `b` rows per block is `2^sh`.
pub open spec fn shift_ok(sh: usize, b: usize) -> bool {
    sh < 64 && pow2(sh as nat) == b
}

/// `x / b` as a shift.
#[inline(always)]
pub fn shr(x: usize, sh: usize, Ghost(b): Ghost<usize>) -> (r: usize)
    requires shift_ok(sh, b),
    ensures r == x / b,
    no_unwind
{
    proof {
        vstd::bits::lemma_u64_shr_is_div(x as u64, sh as u64);
    }
    ((x as u64) >> (sh as u64)) as usize
}

/// Position `p` lies in the directory entry of its stored row's part key.
pub open spec fn in_dent(c: Cols, d: Dirs, p: int) -> bool {
    let e = lp(c, drow(c, d, p)) - d.pkmin;
    &&& 0 <= e < d.offs@.len() - 1
    &&& d.offs@[e] <= p < d.offs@[e + 1]
}

/// Entry `e` of the o_orderkey directory is empty or names the stored orders row of key `okmin + e`.
pub open spec fn osound(c: Cols, d: Dirs, e: int) -> bool {
    let r = d.orows@[e];
    r == ODIR_NONE || (r < c.n_o && okey(c, r as int) == d.okmin + e)
}

/// The key of stored orders row `q` has a nonempty entry.
pub open spec fn ocomplete(c: Cols, d: Dirs, q: int) -> bool {
    let e = okey(c, q) - d.okmin;
    &&& 0 <= e < d.orows@.len()
    &&& d.orows@[e] != ODIR_NONE
}

/// What the kernel uses of the directories, the block sizes and the dense customer and supplier keys.
pub open spec fn dirs_ok(c: Cols, d: Dirs) -> bool {
    let n = c.n_l as int;
    let nk = d.offs@.len() - 1;
    &&& c.n_l < usize::MAX
    &&& d.ic@.len() == n && d.ib@.len() * c.bs_l >= n
    &&& is_perm(dmap(c, d), n)
    &&& d.offs@.len() >= 1 && d.offs@[0] == 0 && d.offs@[nk] == n
    &&& forall|e: int| 0 <= e < nk ==> #[trigger] d.offs@[e] <= d.offs@[e + 1]
    &&& forall|p: int| 0 <= p < n ==> #[trigger] in_dent(c, d, p)
    &&& c.n_o < ODIR_NONE
    &&& d.on == d.orows@.len()
    &&& forall|e: int| 0 <= e < d.orows@.len() ==> #[trigger] osound(c, d, e)
    &&& forall|q: int| 0 <= q < c.n_o ==> #[trigger] ocomplete(c, d, q)
    &&& shift_ok(d.sl, c.bs_l) && shift_ok(d.so, c.bs_o) && shift_ok(d.sc, c.bs_c) && shift_ok(d.ss, c.bs_s)
    &&& forall|i: int| 0 <= i < c.n_c ==> #[trigger] ck(c, i) == d.cfirst + i
    &&& forall|i: int| 0 <= i < c.n_s ==> #[trigger] sk(c, i) == d.sfirst + i
}

/// Dense part keys (part row `i` has key `pfirst + i`) with a power-of-two block size.
pub open spec fn pdense(f: PFilter, d: Dirs) -> bool {
    &&& shift_ok(d.sp, f.bs_p)
    &&& forall|i: int| 0 <= i < f.n_p ==> #[trigger] pkey(f, i) == d.pfirst + i
}

/// Offsets are nondecreasing over any span of entries.
pub proof fn lemma_offs_mono(c: Cols, d: Dirs, a: int, b: int)
    requires dirs_ok(c, d), 0 <= a <= b <= d.offs@.len() - 1,
    ensures d.offs@[a] <= d.offs@[b],
    decreases b - a,
{
    if a < b {
        lemma_offs_mono(c, d, a, b - 1);
        assert(d.offs@[b - 1] <= d.offs@[b]);
    }
}

/// The positions of entry `e` hold stored rows of part key `pkmin + e`.
pub proof fn lemma_entry_key(c: Cols, d: Dirs, e: int, p: int)
    requires dirs_ok(c, d), 0 <= e < d.offs@.len() - 1, d.offs@[e] <= p < d.offs@[e + 1],
    ensures
        p < c.n_l,
        lp(c, drow(c, d, p)) == d.pkmin + e,
{
    let nk = d.offs@.len() - 1;
    lemma_offs_mono(c, d, e + 1, nk);
    assert(in_dent(c, d, p));
    let f = lp(c, drow(c, d, p)) - d.pkmin;
    if f < e {
        lemma_offs_mono(c, d, f + 1, e);
    } else if f > e {
        lemma_offs_mono(c, d, e + 1, f);
    }
}

/// The stored row at a key index position is a stored row.
pub proof fn lemma_drow(c: Cols, d: Dirs, p: int)
    requires dirs_ok(c, d), 0 <= p < c.n_l,
    ensures 0 <= drow(c, d, p) < c.n_l, 0 <= p / (c.bs_l as int), p / (c.bs_l as int) < d.ib@.len(),
{
    assert(dmap(c, d)[p] == drow(c, d, p));
    lemma_div_below(p, c.bs_l as int, d.ib@.len() as int);
}

/// With dense part keys, the part filter is a type test of part row `v - pfirst`.
pub proof fn lemma_pm_dense(f: PFilter, d: Dirs, v: int)
    requires super::filters::pf_shape(f), pdense(f, d),
    ensures pmatch(f, v) == (f.has_t && 0 <= v - d.pfirst < f.n_p && ptype(f, v - d.pfirst) == f.t),
{
    if pmatch(f, v) {
        let r = choose|r: int| 0 <= r < f.n_p && #[trigger] pkey(f, r) == v && ptype(f, r) == f.t;
        assert(pkey(f, r) == d.pfirst + r);
    }
    if f.has_t && 0 <= v - d.pfirst < f.n_p && ptype(f, v - d.pfirst) == f.t {
        assert(pkey(f, v - d.pfirst) == v);
    }
}

// ------------------------------------------------------------------------------------------------ part scan

/// The first entry in `[e, e1)` whose part passes the type filter `$3`, or `e1`. Entry `x` is part row
/// `x - delta` (`delta = pfirst - pkmin`); entries outside the part rows fail. Within a part group of `bs_p` rows the
/// test is one byte compare against the group's code of `$3` (`t - base`), so the scan reads no directory offsets.
fn next_pass(f: &PFilter, d: &Dirs, e: usize, e1: usize) -> (r: usize)
    requires super::filters::pf_shape(*f), pdense(*f, *d), e <= e1,
    ensures
        e <= r <= e1,
        forall|x: int| e <= x < r ==> !#[trigger] pmatch(*f, d.pkmin + x),
        r < e1 ==> pmatch(*f, d.pkmin + r),
    no_unwind
{
    proof {
        assert forall|x: int| e <= x < e1 && !(f.has_t && 0 <= d.pkmin + x - d.pfirst < f.n_p
            && ptype(*f, d.pkmin + x - d.pfirst) == f.t) implies !#[trigger] pmatch(*f, d.pkmin + x) by {
            lemma_pm_dense(*f, *d, d.pkmin + x);
        }
    }
    if !f.has_t {
        return e1;
    }
    // Entries `[xlo, xhi)` are the part rows `[xlo - delta, xhi - delta)`.
    let delta: i128 = d.pfirst as i128 - d.pkmin as i128;
    let xlo: i128 = if (e as i128) < delta { delta } else { e as i128 };
    let xhi: i128 = if (e1 as i128) < f.n_p as i128 + delta { e1 as i128 } else { f.n_p as i128 + delta };
    if xlo >= xhi {
        return e1;
    }
    let i0: usize = (xlo - delta) as usize;
    let iend: usize = (xhi - delta) as usize;
    let bs = f.bs_p;
    let mut i: usize = i0;
    while i < iend
        invariant
            super::filters::pf_shape(*f), pdense(*f, *d), f.has_t, bs == f.bs_p,
            e <= xlo < xhi <= e1, delta == d.pfirst - d.pkmin, e < xlo ==> xlo == delta, xhi < e1 ==> xhi == f.n_p + delta,
            i0 == xlo - delta, iend == xhi - delta, 0 <= i0 <= i <= iend <= f.n_p,
            forall|j: int| i0 <= j < i ==> #[trigger] ptype(*f, j) != f.t,
        decreases iend - i,
    {
        let g = shr(i, d.sp, Ghost(bs));
        proof {
            lemma_div_below(i as int, bs as int, f.pk_b@.len() as int);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i as int, bs as int);
            vstd::arithmetic::div_mod::lemma_mod_bound(i as int, bs as int);
        }
        // `rem` = i mod bs; the group ends `bs - rem` rows later.
        let rem: usize = i - g * bs;
        let gend: usize = if bs - rem <= iend - i { i + (bs - rem) } else { iend };
        proof {
            assert forall|j: int| i <= j < gend implies #[trigger] (j / (bs as int)) == g by {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(j, bs as int, g as int, j - g * bs);
            }
        }
        let base = f.pt_b[g];
        if base <= f.t && f.t - base <= 255 {
            let tc: u8 = (f.t - base) as u8;
            // Skip whole chunks of `W8` codes without `tc` (a vectorizable test), then find the code one by one.
            while gend - i >= W8 && !has_u8(f.pt_c, i, tc)
                invariant
                    super::filters::pf_shape(*f), pdense(*f, *d), f.has_t, bs == f.bs_p,
                    e <= xlo < xhi <= e1, delta == d.pfirst - d.pkmin, e < xlo ==> xlo == delta, xhi < e1 ==> xhi == f.n_p + delta, i0 == xlo - delta, iend == xhi - delta,
                    i0 <= i <= gend <= iend <= f.n_p, base == f.pt_b@[g as int], tc == f.t - base,
                    forall|j: int| i <= j < gend ==> #[trigger] (j / (bs as int)) == g,
                    forall|j: int| i0 <= j < i ==> #[trigger] ptype(*f, j) != f.t,
                decreases gend - i,
            {
                proof {
                    assert forall|j: int| i0 <= j < i + W8 implies #[trigger] ptype(*f, j) != f.t by {
                        if j >= i {
                            assert(j / (bs as int) == g);
                            assert(f.pt_c@[j] != tc);
                        }
                    }
                }
                i = i + W8;
            }
            while i < gend && f.pt_c[i] != tc
                invariant
                    super::filters::pf_shape(*f), pdense(*f, *d), f.has_t, bs == f.bs_p,
                    e <= xlo < xhi <= e1, delta == d.pfirst - d.pkmin, e < xlo ==> xlo == delta, xhi < e1 ==> xhi == f.n_p + delta, i0 == xlo - delta, iend == xhi - delta,
                    i0 <= i <= gend <= iend <= f.n_p, base == f.pt_b@[g as int], tc == f.t - base,
                    forall|j: int| i <= j < gend ==> #[trigger] (j / (bs as int)) == g,
                    forall|j: int| i0 <= j < i ==> #[trigger] ptype(*f, j) != f.t,
                decreases gend - i,
            {
                i = i + 1;
            }
            if i < gend {
                proof {
                    assert(ptype(*f, i as int) == f.t);
                    lemma_pm_dense(*f, *d, d.pkmin + (i + delta));
                    assert forall|x: int| e <= x < i + delta implies !#[trigger] pmatch(*f, d.pkmin + x) by {
                        lemma_pm_dense(*f, *d, d.pkmin + x);
                        if xlo <= x {
                            assert(ptype(*f, x - delta) != f.t);
                        }
                    }
                }
                return (i as i128 + delta) as usize;
            }
        } else {
            proof {
                assert forall|j: int| i <= j < gend implies #[trigger] ptype(*f, j) != f.t by {
                    assert(j / (bs as int) == g);
                }
            }
            i = gend;
        }
    }
    proof {
        assert forall|x: int| e <= x < e1 implies !#[trigger] pmatch(*f, d.pkmin + x) by {
            lemma_pm_dense(*f, *d, d.pkmin + x);
            if xlo <= x < xhi {
                assert(ptype(*f, x - delta) != f.t);
            }
        }
    }
    e1
}

/// Entries `[e, x)` whose parts all fail the filter hold no contributing position.
proof fn lemma_entries_none(c: Cols, f: PFilter, nt: NTab, d: Dirs, e: int, x: int)
    requires
        dirs_ok(c, d), 0 <= e <= x <= d.offs@.len() - 1,
        forall|y: int| e <= y < x ==> !#[trigger] pmatch(f, d.pkmin + y),
    ensures
        forall|p: int| d.offs@[e] <= p < d.offs@[x] ==> #[trigger] gl(c, pm_of(f), nt_view(nt), d, p) is None,
{
    let nk = d.offs@.len() - 1;
    assert forall|p: int| d.offs@[e] <= p < d.offs@[x] implies #[trigger] gl(c, pm_of(f), nt_view(nt), d, p) is None by {
        lemma_offs_mono(c, d, x, nk);
        assert(in_dent(c, d, p));
        let y = lp(c, drow(c, d, p)) - d.pkmin;
        if y < e {
            lemma_offs_mono(c, d, y + 1, e);
        } else if y >= x {
            lemma_offs_mono(c, d, x, y);
        }
        assert(!pmatch(f, d.pkmin + y));
    }
}

// ------------------------------------------------------------------------------------------------ lookups

/// The stored orders row of lineitem key `k` (`rpos`), by the o_orderkey directory.
#[inline(always)]
fn order_of(c: &Cols, d: &Dirs, k: i64) -> (p: usize)
    requires cols_ok(*c), dirs_ok(*c, *d),
    ensures p == rpos(*c, k as int),
    no_unwind
{
    let ek: i128 = k as i128 - d.okmin as i128;
    if 0 <= ek && ek < d.on as i128 {
        let r = d.orows[ek as usize];
        if r != ODIR_NONE {
            proof {
                assert(osound(*c, *d, ek as int));
                assert forall|q: int| 0 <= q < r implies #[trigger] okey(*c, q) != k by {
                    if okey(*c, q) == k {
                        assert(okey(*c, q) == okey(*c, r as int));
                    }
                }
                lemma_rpos_at(*c, k as int, r as int);
            }
            return r as usize;
        }
    }
    proof {
        assert forall|q: int| 0 <= q < c.n_o implies #[trigger] okey(*c, q) != k by {
            assert(ocomplete(*c, *d, q));
        }
        lemma_rpos_at(*c, k as int, c.n_o as int);
    }
    c.n_o
}

/// The customer row of key `k` (dense keys), if any.
#[inline(always)]
fn cust_of(c: &Cols, d: &Dirs, k: i64) -> (r: Option<usize>)
    requires cols_ok(*c), dirs_ok(*c, *d),
    ensures
        r == match cfind(*c, k as int) { Some(i) => Some(i as usize), None => None::<usize> },
        r matches Some(i) ==> i < c.n_c,
    no_unwind
{
    let g: i128 = k as i128 - d.cfirst as i128;
    if 0 <= g && g < c.n_c as i128 {
        let i = g as usize;
        proof {
            assert(ck(*c, i as int) == k);
            let c2 = choose|j: int| 0 <= j < c.n_c && #[trigger] ck(*c, j) == k as int;
            assert(c2 == i);
        }
        Some(i)
    } else {
        proof {
            assert forall|j: int| 0 <= j < c.n_c implies #[trigger] ck(*c, j) != k by {}
        }
        None
    }
}

/// The supplier row of key `k` (dense keys), if any.
#[inline(always)]
fn supp_of(c: &Cols, d: &Dirs, k: i64) -> (r: Option<usize>)
    requires cols_ok(*c), dirs_ok(*c, *d),
    ensures
        r == match sfind(*c, k as int) { Some(i) => Some(i as usize), None => None::<usize> },
        r matches Some(i) ==> i < c.n_s,
    no_unwind
{
    let g: i128 = k as i128 - d.sfirst as i128;
    if 0 <= g && g < c.n_s as i128 {
        let i = g as usize;
        proof {
            assert(sk(*c, i as int) == k);
            let s2 = choose|j: int| 0 <= j < c.n_s && #[trigger] sk(*c, j) == k as int;
            assert(s2 == i);
        }
        Some(i)
    } else {
        proof {
            assert forall|j: int| 0 <= j < c.n_s implies #[trigger] sk(*c, j) != k by {}
        }
        None
    }
}

// ------------------------------------------------------------------------------------------------ batches

/// Rows per batch of the staged kernel.
pub const BATCH: usize = 512;

/// The per-task buffers of the staged kernel: lineitem rows, their orders rows, customer keys and order dates, and
/// the gathered values of the later stages (region flags; supplier keys, prices and discounts reuse `keys`, `eps`,
/// `dcs`).
pub struct Bufs {
    pub rows: Vec<usize>,
    pub ords: Vec<usize>,
    pub keys: Vec<i64>,
    pub days: Vec<i64>,
    pub flags: Vec<bool>,
    pub eps: Vec<i64>,
    pub dcs: Vec<i64>,
}

pub open spec fn bufs_ok(b: Bufs) -> bool {
    &&& b.rows@.len() == BATCH && b.ords@.len() == BATCH && b.keys@.len() == BATCH && b.days@.len() == BATCH
    &&& b.flags@.len() == BATCH && b.eps@.len() == BATCH && b.dcs@.len() == BATCH
}

/// Fresh buffers (calling thread).
pub fn bufs_new() -> (b: Bufs)
    ensures bufs_ok(b),
{
    Bufs {
        rows: filled(BATCH, 0usize),
        ords: filled(BATCH, 0usize),
        keys: filled(BATCH, 0i64),
        days: filled(BATCH, 0i64),
        flags: filled(BATCH, false),
        eps: filled(BATCH, 0i64),
        dcs: filled(BATCH, 0i64),
    }
}

/// Buffered row `q` is a stored row whose part passes the filter.
pub open spec fn row_in(c: Cols, pm: spec_fn(int) -> bool, rows: Seq<usize>, q: int) -> bool {
    rows[q] < c.n_l && pm(lp(c, rows[q] as int))
}

/// After the date stage: row `q`'s order exists, is in the date window, and its customer key and date are stored.
pub open spec fn kept2(c: Cols, pm: spec_fn(int) -> bool, rows: Seq<usize>, keys: Seq<i64>, days: Seq<i64>, q: int) -> bool {
    let s = rows[q] as int;
    let p = rpos(c, lk(c, s));
    &&& rows[q] < c.n_l && pm(lp(c, s))
    &&& p < c.n_o && keys[q] == oc(c, p) && days[q] == od(c, p) && c.lo <= days[q] <= c.hi
}

/// After the customer stage: also the customer exists and its nation is in region `$2`.
pub open spec fn kept3(c: Cols, pm: spec_fn(int) -> bool, ns: NStat, rows: Seq<usize>, days: Seq<i64>, q: int) -> bool {
    let s = rows[q] as int;
    let p = rpos(c, lk(c, s));
    &&& rows[q] < c.n_l && pm(lp(c, s))
    &&& p < c.n_o && days[q] == od(c, p) && c.lo <= days[q] <= c.hi
    &&& cfind(c, oc(c, p)) is Some
    &&& nreg(ns, cn(c, cfind(c, oc(c, p))->Some_0))
}

/// Stage 1: the stored orders row of each buffered line, in two loops (the l_orderkey of every line, then each
/// key's orders row) so the independent cache misses of each loop overlap.
fn stage_ords(c: &Cols, d: &Dirs, b: &mut Bufs, n: usize)
    requires
        cols_ok(*c), dirs_ok(*c, *d), bufs_ok(*old(b)), n <= BATCH,
        forall|q: int| 0 <= q < n ==> #[trigger] old(b).rows@[q] < c.n_l,
    ensures
        bufs_ok(*final(b)),
        final(b).rows@ == old(b).rows@, final(b).days@ == old(b).days@,
        forall|q: int| 0 <= q < n ==> #[trigger] final(b).ords@[q] == rpos(*c, lk(*c, final(b).rows@[q] as int)),
    no_unwind
{
    let mut i: usize = 0;
    while i < n
        invariant
            cols_ok(*c), dirs_ok(*c, *d), bufs_ok(*b), n <= BATCH, i <= n,
            b.rows@ == old(b).rows@, b.days@ == old(b).days@,
            forall|q: int| 0 <= q < n ==> #[trigger] b.rows@[q] < c.n_l,
            forall|q: int| 0 <= q < i ==> #[trigger] b.keys@[q] == lk(*c, b.rows@[q] as int),
        decreases n - i,
    {
        let s = b.rows[i];
        let g = shr(s, d.sl, Ghost(c.bs_l));
        proof {
            assert(b.rows@[i as int] < c.n_l);
            lemma_div_below(s as int, c.bs_l as int, c.lk_b@.len() as int);
            assert(in_i64(lk(*c, s as int)));
        }
        let lkey = c.lk_b[g] + c.lk_c[s] as i64;
        put(&mut b.keys, i, lkey);
        i = i + 1;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            cols_ok(*c), dirs_ok(*c, *d), bufs_ok(*b), n <= BATCH, i <= n,
            b.rows@ == old(b).rows@, b.days@ == old(b).days@,
            forall|q: int| 0 <= q < n ==> #[trigger] b.keys@[q] == lk(*c, b.rows@[q] as int),
            forall|q: int| 0 <= q < i ==> #[trigger] b.ords@[q] == rpos(*c, lk(*c, b.rows@[q] as int)),
        decreases n - i,
    {
        let p = order_of(c, d, b.keys[i]);
        put(&mut b.ords, i, p);
        i = i + 1;
    }
}

/// Stage 2: keep the lines whose order exists and lies in the date window, with its customer key and date
/// (compacted to the front, in order). The kept lines accumulate as the input lines. A lean first loop gathers each
/// order's date and customer key (independent cache misses overlap); the second compacts within the buffers.
fn stage_date(c: &Cols, d: &Dirs, b: &mut Bufs, n: usize, Ghost(pm): Ghost<spec_fn(int) -> bool>, Ghost(ns): Ghost<NStat>)
    -> (m: usize)
    requires
        cols_ok(*c), dirs_ok(*c, *d), bufs_ok(*old(b)), n <= BATCH,
        forall|q: int| 0 <= q < n ==> #[trigger] row_in(*c, pm, old(b).rows@, q),
        forall|q: int| 0 <= q < n ==> #[trigger] old(b).ords@[q] == rpos(*c, lk(*c, old(b).rows@[q] as int)),
    ensures
        bufs_ok(*final(b)), m <= n,
        acc_rows(*c, pm, ns, old(b).rows@, n as int) == acc_rows(*c, pm, ns, final(b).rows@, m as int),
        forall|q: int| 0 <= q < m ==> #[trigger] kept2(*c, pm, final(b).rows@, final(b).keys@, final(b).days@, q),
    no_unwind
{
    let ghost orig = b.rows@;
    let ghost ords = b.ords@;
    let mut i: usize = 0;
    while i < n
        invariant
            cols_ok(*c), dirs_ok(*c, *d), bufs_ok(*b), n <= BATCH, i <= n,
            orig == old(b).rows@, ords == old(b).ords@, b.rows@ == orig, b.ords@ == ords,
            forall|q: int| 0 <= q < i ==> #[trigger] ords[q] < c.n_o ==> b.days@[q] == od(*c, ords[q] as int)
                && b.keys@[q] == oc(*c, ords[q] as int),
        decreases n - i,
    {
        let p = b.ords[i];
        if p < c.n_o {
            let gp = shr(p, d.so, Ghost(c.bs_o));
            proof {
                lemma_div_below(p as int, c.bs_o as int, c.ok_b@.len() as int);
                assert(in_i64(okey(*c, p as int)));
                assert(in_i64(od(*c, p as int)) && in_i64(oc(*c, p as int)));
            }
            let day = c.od_b[gp] + c.od_c[p] as i64;
            let ckey = c.oc_b[gp] + c.oc_c[p] as i64;
            put(&mut b.days, i, day);
            put(&mut b.keys, i, ckey);
        }
        i = i + 1;
    }
    let ghost days0 = b.days@;
    let ghost keys0 = b.keys@;
    let mut m: usize = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            cols_ok(*c), dirs_ok(*c, *d), bufs_ok(*b), n <= BATCH, m <= i, i <= n,
            orig == old(b).rows@, ords == old(b).ords@, b.ords@ == ords,
            forall|q: int| 0 <= q < n ==> #[trigger] row_in(*c, pm, orig, q),
            forall|q: int| 0 <= q < n ==> #[trigger] ords[q] == rpos(*c, lk(*c, orig[q] as int)),
            forall|q: int| 0 <= q < n ==> #[trigger] ords[q] < c.n_o ==> days0[q] == od(*c, ords[q] as int)
                && keys0[q] == oc(*c, ords[q] as int),
            forall|q: int| i <= q < n ==> #[trigger] b.rows@[q] == orig[q],
            forall|q: int| i <= q < n ==> #[trigger] b.days@[q] == days0[q],
            forall|q: int| i <= q < n ==> #[trigger] b.keys@[q] == keys0[q],
            acc_rows(*c, pm, ns, orig, i as int) == acc_rows(*c, pm, ns, b.rows@, m as int),
            forall|q: int| 0 <= q < m ==> #[trigger] kept2(*c, pm, b.rows@, b.keys@, b.days@, q),
        decreases n - i,
    {
        let s = b.rows[i];
        let p = b.ords[i];
        let day = b.days[i];
        let ckey = b.keys[i];
        proof {
            assert(b.rows@[i as int] == orig[i as int]);
            assert(b.days@[i as int] == days0[i as int] && b.keys@[i as int] == keys0[i as int]);
            assert(row_in(*c, pm, orig, i as int));
            assert(ords[i as int] == rpos(*c, lk(*c, s as int)));
            lemma_acc_add_zero(acc_rows(*c, pm, ns, orig, i as int));
        }
        if p < c.n_o && c.lo <= day && day <= c.hi {
            let ghost (r0, k0, d0) = (b.rows@, b.keys@, b.days@);
            put(&mut b.keys, m, ckey);
            put(&mut b.days, m, day);
            put(&mut b.rows, m, s);
            proof {
                assert(ords[i as int] < c.n_o);
                lemma_rows_put(*c, pm, ns, r0, m as int, s);
                assert forall|q: int| 0 <= q < m + 1 implies #[trigger] kept2(*c, pm, b.rows@, b.keys@, b.days@, q) by {
                    if q < m {
                        assert(kept2(*c, pm, r0, k0, d0, q));
                    }
                }
            }
            m = m + 1;
        }
        i = i + 1;
    }
    m
}

/// Customer row `ci`'s nation is in region `$2` (false when the key has no customer).
pub open spec fn reg_of(c: Cols, ns: NStat, k: int) -> bool {
    cfind(c, k) is Some && nreg(ns, cn(c, cfind(c, k)->Some_0))
}

/// Stage 3: keep the lines whose customer exists and whose nation is in region `$2` (compacted again). A lean
/// first loop gathers each customer's region flag; the second compacts.
fn stage_cust(c: &Cols, nt: &NTab, d: &Dirs, b: &mut Bufs, n: usize, Ghost(pm): Ghost<spec_fn(int) -> bool>) -> (m: usize)
    requires
        cols_ok(*c), ntab_ok(*nt), cb_ok(*c, *nt), dirs_ok(*c, *d), bufs_ok(*old(b)), n <= BATCH,
        forall|q: int| 0 <= q < n ==> #[trigger] kept2(*c, pm, old(b).rows@, old(b).keys@, old(b).days@, q),
    ensures
        bufs_ok(*final(b)), m <= n,
        acc_rows(*c, pm, nt_view(*nt), old(b).rows@, n as int) == acc_rows(*c, pm, nt_view(*nt), final(b).rows@, m as int),
        forall|q: int| 0 <= q < m ==> #[trigger] kept3(*c, pm, nt_view(*nt), final(b).rows@, final(b).days@, q),
    no_unwind
{
    let ghost ns = nt_view(*nt);
    let ghost (orig, keys, days0) = (b.rows@, b.keys@, b.days@);
    let mut i: usize = 0;
    while i < n
        invariant
            cols_ok(*c), ntab_ok(*nt), cb_ok(*c, *nt), dirs_ok(*c, *d), bufs_ok(*b), n <= BATCH, i <= n,
            ns == nt_view(*nt),
            b.rows@ == orig, b.keys@ == keys, b.days@ == days0,
            forall|q: int| 0 <= q < i ==> #[trigger] b.flags@[q] == reg_of(*c, ns, keys[q] as int),
        decreases n - i,
    {
        let ckey = b.keys[i];
        let mut reg = false;
        match cust_of(c, d, ckey) {
            Some(ci) => {
                proof {
                    lemma_div_below(ci as int, c.bs_c as int, c.ck_b@.len() as int);
                    assert(in_i64(cn(*c, ci as int)));
                }
                if nt.cbits.len() > 0 {
                    // The region bitmap of the serial kernel (`cbits`): word `ci / 64`, bit `ci % 64`.
                    proof {
                        lemma_div_below(ci as int, 64, nt.cbits@.len() as int);
                        assert(cbit(nt.cbits@, ci as int) == nreg(ns, cn(*c, ci as int)));
                    }
                    reg = (nt.cbits[ci / 64] >> ((ci % 64) as u64)) & 1 == 1;
                } else {
                    let g = shr(ci, d.sc, Ghost(c.bs_c));
                    let cnat = c.cn_b[g] + c.cn_c[ci] as i64;
                    let (_, reg1, _) = nat_lookup(nt, cnat);
                    reg = reg1;
                }
            },
            None => {},
        }
        put(&mut b.flags, i, reg);
        i = i + 1;
    }
    let ghost flags = b.flags@;
    let mut m: usize = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            cols_ok(*c), ntab_ok(*nt), dirs_ok(*c, *d), bufs_ok(*b), n <= BATCH, m <= i, i <= n,
            ns == nt_view(*nt),
            orig == old(b).rows@, keys == old(b).keys@, days0 == old(b).days@, b.flags@ == flags,
            forall|q: int| 0 <= q < n ==> #[trigger] kept2(*c, pm, orig, keys, days0, q),
            forall|q: int| 0 <= q < n ==> #[trigger] flags[q] == reg_of(*c, ns, keys[q] as int),
            forall|q: int| i <= q < n ==> #[trigger] b.rows@[q] == orig[q],
            forall|q: int| i <= q < n ==> #[trigger] b.days@[q] == days0[q],
            acc_rows(*c, pm, ns, orig, i as int) == acc_rows(*c, pm, ns, b.rows@, m as int),
            forall|q: int| 0 <= q < m ==> #[trigger] kept3(*c, pm, ns, b.rows@, b.days@, q),
        decreases n - i,
    {
        let s = b.rows[i];
        let day = b.days[i];
        proof {
            assert(b.rows@[i as int] == orig[i as int] && b.days@[i as int] == days0[i as int]);
            assert(kept2(*c, pm, orig, keys, days0, i as int));
            assert(flags[i as int] == reg_of(*c, ns, keys[i as int] as int));
            lemma_acc_add_zero(acc_rows(*c, pm, ns, orig, i as int));
        }
        if b.flags[i] {
            let ghost (r0, d0) = (b.rows@, b.days@);
            put(&mut b.days, m, day);
            put(&mut b.rows, m, s);
            proof {
                lemma_rows_put(*c, pm, ns, r0, m as int, s);
                assert forall|q: int| 0 <= q < m + 1 implies #[trigger] kept3(*c, pm, ns, b.rows@, b.days@, q) by {
                    if q < m {
                        assert(kept3(*c, pm, ns, r0, d0, q));
                    }
                }
            }
            m = m + 1;
        }
        i = i + 1;
    }
    m
}

/// Stage 4: the supplier's nation and the volume of each kept line, added to `acc`. `false` when a year's mass
/// would pass `i128::MAX`. A lean first loop gathers each line's supplier key, price and discount.
fn stage_acc(c: &Cols, nt: &NTab, d: &Dirs, b: &mut Bufs, n: usize, acc: &mut Acc, Ghost(pm): Ghost<spec_fn(int) -> bool>,
    Ghost(k): Ghost<int>) -> (ok: bool)
    requires
        cols_ok(*c), ntab_ok(*nt), dirs_ok(*c, *d), bufs_ok(*old(b)), n <= BATCH,
        forall|q: int| 0 <= q < n ==> #[trigger] kept3(*c, pm, nt_view(*nt), old(b).rows@, old(b).days@, q),
        !old(acc).ovf, 0 <= k, acc_sane(acc_view(*old(acc)), k), k + n < usize::MAX,
    ensures
        bufs_ok(*final(b)), final(b).rows@ == old(b).rows@,
        !final(acc).ovf,
        ok ==> acc_view(*final(acc)) == acc_add(acc_view(*old(acc)), acc_rows(*c, pm, nt_view(*nt), old(b).rows@, n as int))
            && acc_sane(acc_view(*final(acc)), k + n),
        !ok ==> acc_add(acc_view(*old(acc)), acc_rows(*c, pm, nt_view(*nt), old(b).rows@, n as int)).m0 > i128::MAX
            || acc_add(acc_view(*old(acc)), acc_rows(*c, pm, nt_view(*nt), old(b).rows@, n as int)).m1 > i128::MAX,
    no_unwind
{
    let ghost ns = nt_view(*nt);
    let ghost a0 = acc_view(*acc);
    let ghost (rows, days) = (b.rows@, b.days@);
    let mut i: usize = 0;
    while i < n
        invariant
            cols_ok(*c), ntab_ok(*nt), dirs_ok(*c, *d), bufs_ok(*b), n <= BATCH, i <= n,
            ns == nt_view(*nt), b.rows@ == rows, b.days@ == days,
            forall|q: int| 0 <= q < n ==> #[trigger] kept3(*c, pm, ns, rows, days, q),
            forall|q: int| 0 <= q < i ==> #[trigger] b.keys@[q] == ls(*c, rows[q] as int)
                && b.eps@[q] == le(*c, rows[q] as int) && b.dcs@[q] == ld(*c, rows[q] as int),
        decreases n - i,
    {
        let s = b.rows[i];
        proof {
            assert(kept3(*c, pm, ns, rows, days, i as int));
            assert(s == rows[i as int]);
            assert(0 <= s < c.n_l);
            lemma_div_below(s as int, c.bs_l as int, c.lk_b@.len() as int);
            assert(in_i64(ls(*c, s as int)));
            assert(cols_ok(*c));
            assert(coeff15(le(*c, s as int)));
            assert(coeff15(ld(*c, s as int)));
        }
        let g = shr(s, d.sl, Ghost(c.bs_l));
        let skey = c.ls_b[g] + c.ls_c[s] as i64;
        let ep = c.le_b[g] + c.le_c[s] as i64;
        let dc = c.ld_b[g] + c.ld_c[s] as i64;
        let ghost (k0, e0, d0) = (b.keys@, b.eps@, b.dcs@);
        put(&mut b.keys, i, skey);
        put(&mut b.eps, i, ep);
        put(&mut b.dcs, i, dc);
        proof {
            assert forall|q: int| 0 <= q < i + 1 implies #[trigger] b.keys@[q] == ls(*c, rows[q] as int)
                && b.eps@[q] == le(*c, rows[q] as int) && b.dcs@[q] == ld(*c, rows[q] as int) by {
                if q < i {
                    assert(k0[q] == ls(*c, rows[q] as int));
                    assert(b.keys@[q] == k0[q] && b.eps@[q] == e0[q] && b.dcs@[q] == d0[q]);
                }
            }
        }
        i = i + 1;
    }
    proof {
        assert(forall|q: int| 0 <= q < n ==> #[trigger] b.keys@[q] == ls(*c, rows[q] as int)
            && b.eps@[q] == le(*c, rows[q] as int) && b.dcs@[q] == ld(*c, rows[q] as int));
        assert(forall|q: int| 0 <= q < n ==> #[trigger] kept3(*c, pm, ns, b.rows@, b.days@, q));
    }
    let mut i: usize = 0;
    while i < n
        invariant
            cols_ok(*c), ntab_ok(*nt), dirs_ok(*c, *d), bufs_ok(*b), n <= BATCH, i <= n,
            ns == nt_view(*nt), a0 == acc_view(*old(acc)), b.rows@ == rows, b.days@ == days,
            rows == old(b).rows@, days == old(b).days@,
            forall|q: int| 0 <= q < n ==> #[trigger] b.keys@[q] == ls(*c, rows[q] as int)
                && b.eps@[q] == le(*c, rows[q] as int) && b.dcs@[q] == ld(*c, rows[q] as int),
            forall|q: int| 0 <= q < n ==> #[trigger] kept3(*c, pm, ns, b.rows@, b.days@, q),
            !acc.ovf, 0 <= k, k + n < usize::MAX,
            acc_view(*acc) == acc_add(a0, acc_rows(*c, pm, ns, b.rows@, i as int)),
            acc_sane(acc_view(*acc), k + i),
        decreases n - i,
    {
        let s = b.rows[i];
        let day = b.days[i];
        let ghost before = acc_view(*acc);
        proof {
            assert(kept3(*c, pm, ns, b.rows@, b.days@, i as int));
            assert(b.keys@[i as int] == ls(*c, s as int));
            lemma_acc_add_assoc(a0, acc_rows(*c, pm, ns, b.rows@, i as int), acc_of(lc(*c, pm, ns, s as int)));
        }
        let skey = b.keys[i];
        let mut contrib: Option<(bool, i128, bool)> = None;
        match supp_of(c, d, skey) {
            Some(si) => {
                proof {
                    lemma_div_below(si as int, c.bs_s as int, c.sk_b@.len() as int);
                    assert(in_i64(sn(*c, si as int)));
                }
                let gs = shr(si, d.ss, Ghost(c.bs_s));
                let snat = c.sn_b[gs] + c.sn_c[si] as i64;
                let (ex2, _, name2) = nat_lookup(nt, snat);
                if ex2 {
                    proof {
                        assert(coeff15(le(*c, s as int)) && coeff15(ld(*c, s as int)));
                    }
                    let ep = b.eps[i];
                    let dc = b.dcs[i];
                    let f2 = 100 - dc as i128;
                    proof {
                        assert(-0x1_0000_0000_0000_0000_0000_0000_0000 < ep * f2 < 0x1_0000_0000_0000_0000_0000_0000_0000)
                            by (nonlinear_arith)
                            requires -1_000_000_000_000_000 < ep < 1_000_000_000_000_000,
                                -1_000_000_000_000_000 + 100 < f2 < 1_000_000_000_000_000 + 100;
                        lemma_years(day as int);
                        let ni = nfind(ns, snat as int)->Some_0;
                        assert(nname(ns, snat as int) == ns.name[ni]);
                    }
                    contrib = Some((day >= c.d96, ep as i128 * f2, name2));
                }
            },
            None => {},
        }
        proof {
            assert(hit_of(contrib) == lc(*c, pm, ns, s as int));
            assert(vol_ok(contrib));
        }
        let pushed = acc_push(acc, contrib, Ghost(k + i));
        if !pushed {
            proof {
                lemma_rows_mass_mono(*c, pm, ns, b.rows@, i + 1, n as int);
                lemma_rows_sane(*c, pm, ns, b.rows@, n as int);
            }
            return false;
        }
        proof {
            lemma_sane_wider(acc_view(*acc), k + i + 1, k + i + 1);
        }
        i = i + 1;
    }
    proof {
        lemma_sane_wider(acc_view(*acc), k + i, k + n);
    }
    true
}

/// The batch: stages 1 to 4 over the first `n` buffered rows, added to `acc`.
fn flush(c: &Cols, nt: &NTab, d: &Dirs, b: &mut Bufs, n: usize, acc: &mut Acc, Ghost(pm): Ghost<spec_fn(int) -> bool>,
    Ghost(k): Ghost<int>) -> (ok: bool)
    requires
        cols_ok(*c), ntab_ok(*nt), cb_ok(*c, *nt), dirs_ok(*c, *d), bufs_ok(*old(b)), n <= BATCH,
        forall|q: int| 0 <= q < n ==> #[trigger] row_in(*c, pm, old(b).rows@, q),
        !old(acc).ovf, 0 <= k, acc_sane(acc_view(*old(acc)), k), k + n < usize::MAX,
    ensures
        bufs_ok(*final(b)),
        !final(acc).ovf,
        ok ==> acc_view(*final(acc)) == acc_add(acc_view(*old(acc)), acc_rows(*c, pm, nt_view(*nt), old(b).rows@, n as int))
            && acc_sane(acc_view(*final(acc)), k + n),
        !ok ==> acc_add(acc_view(*old(acc)), acc_rows(*c, pm, nt_view(*nt), old(b).rows@, n as int)).m0 > i128::MAX
            || acc_add(acc_view(*old(acc)), acc_rows(*c, pm, nt_view(*nt), old(b).rows@, n as int)).m1 > i128::MAX,
    no_unwind
{
    let ghost ns = nt_view(*nt);
    proof {
        assert forall|q: int| 0 <= q < n implies #[trigger] b.rows@[q] < c.n_l by {
            assert(row_in(*c, pm, b.rows@, q));
        }
    }
    stage_ords(c, d, b, n);
    let m = stage_date(c, d, b, n, Ghost(pm), Ghost(ns));
    let m2 = stage_cust(c, nt, d, b, m, Ghost(pm));
    let ok = stage_acc(c, nt, d, b, m2, acc, Ghost(pm), Ghost(k));
    if ok {
        proof {
            lemma_sane_wider(acc_view(*acc), k + m2, k + n);
        }
    }
    ok
}

// ------------------------------------------------------------------------------------------------ one task

/// What a task over entries `[e0, e1)` needs.
pub open spec fn idx_pre(c: Cols, f: PFilter, nt: NTab, d: Dirs, e0: int, e1: int, la: int, lb: int) -> bool {
    &&& idx_pre0(c, f, nt, d, e0, e1, la, lb)
    &&& cb_ok(c, nt)
}

/// `idx_pre` without the customer region bitmap.
pub open spec fn idx_pre0(c: Cols, f: PFilter, nt: NTab, d: Dirs, e0: int, e1: int, la: int, lb: int) -> bool {
    &&& cols_ok(c)
    &&& super::filters::pf_shape(f)
    &&& pdense(f, d)
    &&& ntab_ok(nt)
    &&& dirs_ok(c, d)
    &&& 0 <= e0 <= e1 <= d.offs@.len() - 1
    &&& bounds_ok(c, f, nt, la, lb)
}

/// What a task over entries `[e0, e1)` returns: the accumulators of their key index positions.
pub open spec fn idx_post(c: Cols, f: PFilter, nt: NTab, d: Dirs, e0: int, e1: int, out: Acc) -> bool {
    let s = acc_idx(c, pm_of(f), nt_view(nt), d, d.offs@[e0] as int, d.offs@[e1] as int);
    &&& !out.ovf ==> acc_view(out) == s
    &&& out.ovf ==> s.m0 > i128::MAX || s.m1 > i128::MAX
}

/// The batch invariant at key index position `pos`: the accumulated rows plus the buffered rows are the positions
/// `[p0, pos)`; `k` rows were accumulated.
pub open spec fn batch_inv(c: Cols, f: PFilter, nt: NTab, d: Dirs, acc: Acc, rows: Seq<usize>, nb: int, p0: int, pos: int,
    k: int) -> bool {
    let pm = pm_of(f);
    let ns = nt_view(nt);
    &&& 0 <= nb <= BATCH
    &&& forall|q: int| 0 <= q < nb ==> #[trigger] row_in(c, pm, rows, q)
    &&& !acc.ovf
    &&& 0 <= k && k + nb <= pos - p0
    &&& acc_sane(acc_view(acc), k)
    &&& acc_add(acc_view(acc), acc_rows(c, pm, ns, rows, nb)) == acc_idx(c, pm, ns, d, p0, pos)
}

// ------------------------------------------------------------------------------------------------ entry batches

/// Passing directory entries per batch of a task's walk.
pub const G: usize = 32;

/// A batch of passing directory entries (`ents`), their position ranges `[los[j], his[j])` and the stored row of
/// each range's first position (`sf`), gathered in lean loops of independent loads before the walk.
pub struct Ents {
    pub ents: Vec<usize>,
    pub los: Vec<usize>,
    pub his: Vec<usize>,
    pub sf: Vec<usize>,
}

pub open spec fn ents_ok(en: Ents) -> bool {
    en.ents@.len() == G && en.los@.len() == G && en.his@.len() == G && en.sf@.len() == G
}

/// Fresh batch buffers (calling thread).
pub fn ents_new() -> (en: Ents)
    ensures ents_ok(en),
{
    Ents { ents: filled(G, 0usize), los: filled(G, 0usize), his: filled(G, 0usize), sf: filled(G, 0usize) }
}

/// The first entry of the gap before batch entry `j` (entries `[gap_lo(j), ents[j])` fail the filter).
pub open spec fn gap_lo(ents: Seq<usize>, e: int, j: int) -> int {
    if j <= 0 { e } else { ents[j - 1] + 1 }
}

/// Entry `z` (part key `pkmin + z`) fails the type filter.
pub open spec fn efail(f: PFilter, d: Dirs, z: int) -> bool {
    !pmatch(f, d.pkmin + z)
}

/// The entries of the gap before batch entry `j` fail the filter.
pub open spec fn gap_fail(f: PFilter, d: Dirs, ents: Seq<usize>, e: int, j: int) -> bool {
    forall|z: int| gap_lo(ents, e, j) <= z < ents[j] ==> #[trigger] efail(f, d, z)
}

/// `ents[0 .. ne)` are the passing entries of `[e, x)` in increasing order: every other entry there fails.
pub open spec fn coll_ok(f: PFilter, d: Dirs, ents: Seq<usize>, ne: int, e: int, x: int) -> bool {
    &&& 0 <= ne <= G && ents.len() == G
    &&& forall|j: int| 0 <= j < ne ==> gap_lo(ents, e, j) <= #[trigger] ents[j] < x && pmatch(f, d.pkmin + ents[j])
    &&& forall|j: int| 0 <= j < ne ==> #[trigger] gap_fail(f, d, ents, e, j)
    &&& gap_lo(ents, e, ne) <= x
    &&& forall|z: int| gap_lo(ents, e, ne) <= z < x ==> #[trigger] efail(f, d, z)
}

/// Collect up to `G` passing entries from `e` on (`next_pass`); `x` is where the next batch starts.
fn collect(f: &PFilter, d: &Dirs, e: usize, e1: usize, en: &mut Ents) -> (r: (usize, usize))
    requires super::filters::pf_shape(*f), pdense(*f, *d), e < e1, ents_ok(*old(en)),
    ensures
        ents_ok(*final(en)), e < r.1 <= e1,
        coll_ok(*f, *d, final(en).ents@, r.0 as int, e as int, r.1 as int),
    no_unwind
{
    let mut ne: usize = 0;
    let mut x: usize = e;
    let mut done = false;
    while !done && ne < G && x < e1
        invariant
            super::filters::pf_shape(*f), pdense(*f, *d), e < e1, ents_ok(*en),
            e <= x <= e1, done ==> x == e1, ne > 0 ==> x > e,
            coll_ok(*f, *d, en.ents@, ne as int, e as int, x as int),
            gap_lo(en.ents@, e as int, ne as int) == x || done,
        decreases G - ne + (e1 - x) + (if done { 0int } else { 1int }),
    {
        let y = next_pass(f, d, x, e1);
        if y == e1 {
            proof {
                assert forall|z: int| gap_lo(en.ents@, e as int, ne as int) <= z < e1 implies #[trigger] efail(*f, *d, z) by {
                    if z >= x {
                        assert(!pmatch(*f, d.pkmin + z));
                    }
                }
            }
            x = e1;
            done = true;
        } else {
            let ghost old_ents = en.ents@;
            put(&mut en.ents, ne, y);
            proof {
                assert forall|j: int| 0 <= j <= ne implies #[trigger] gap_lo(en.ents@, e as int, j) == gap_lo(old_ents, e as int, j) by {}
                assert forall|j: int| 0 <= j < ne + 1 implies gap_lo(en.ents@, e as int, j) <= #[trigger] en.ents@[j] < y + 1
                    && pmatch(*f, d.pkmin + en.ents@[j]) by {
                    if j < ne {
                        assert(en.ents@[j] == old_ents[j]);
                    }
                }
                assert forall|j: int| 0 <= j < ne + 1 implies #[trigger] gap_fail(*f, *d, en.ents@, e as int, j) by {
                    if j < ne {
                        assert(en.ents@[j] == old_ents[j]);
                        assert(gap_fail(*f, *d, old_ents, e as int, j));
                    } else {
                        assert forall|z: int| gap_lo(en.ents@, e as int, j) <= z < en.ents@[j] implies #[trigger] efail(*f, *d, z) by {
                            assert(!pmatch(*f, d.pkmin + z));
                        }
                    }
                }
            }
            ne = ne + 1;
            x = y + 1;
        }
    }
    (ne, x)
}

/// The position ranges of the batch's entries and the stored row of each range's first position (independent
/// loads: their cache misses overlap).
fn gather(c: &Cols, d: &Dirs, en: &mut Ents, ne: usize)
    requires
        cols_ok(*c), dirs_ok(*c, *d), ents_ok(*old(en)), ne <= G,
        forall|j: int| 0 <= j < ne ==> #[trigger] old(en).ents@[j] < d.offs@.len() - 1,
    ensures
        ents_ok(*final(en)), final(en).ents@ == old(en).ents@,
        forall|j: int| 0 <= j < ne ==> #[trigger] final(en).los@[j] == d.offs@[final(en).ents@[j] as int]
            && final(en).his@[j] == d.offs@[final(en).ents@[j] + 1]
            && (final(en).los@[j] < final(en).his@[j] ==> final(en).sf@[j] as int == drow(*c, *d, final(en).los@[j] as int)),
    no_unwind
{
    let ghost ents = en.ents@;
    let ghost nk = d.offs@.len() - 1;
    let mut j: usize = 0;
    while j < ne
        invariant
            cols_ok(*c), dirs_ok(*c, *d), ents_ok(*en), ne <= G, j <= ne, en.ents@ == ents, nk == d.offs@.len() - 1,
            forall|q: int| 0 <= q < ne ==> #[trigger] ents[q] < nk,
            forall|q: int| 0 <= q < j ==> #[trigger] en.los@[q] == d.offs@[ents[q] as int],
            forall|q: int| 0 <= q < j ==> #[trigger] en.his@[q] == d.offs@[ents[q] + 1],
        decreases ne - j,
    {
        let x = en.ents[j];
        proof {
            assert(ents[j as int] < nk);
        }
        let lo = d.offs[x] as usize;
        let hi = d.offs[x + 1] as usize;
        put(&mut en.los, j, lo);
        put(&mut en.his, j, hi);
        j = j + 1;
    }
    let ghost (los, his) = (en.los@, en.his@);
    let mut j: usize = 0;
    while j < ne
        invariant
            cols_ok(*c), dirs_ok(*c, *d), ents_ok(*en), ne <= G, j <= ne, en.ents@ == ents, nk == d.offs@.len() - 1,
            en.los@ == los, en.his@ == his,
            forall|q: int| 0 <= q < ne ==> #[trigger] ents[q] < nk,
            forall|q: int| 0 <= q < ne ==> #[trigger] los[q] == d.offs@[ents[q] as int],
            forall|q: int| 0 <= q < ne ==> #[trigger] his[q] == d.offs@[ents[q] + 1],
            forall|q: int| 0 <= q < j ==> (#[trigger] en.sf@[q] as int == drow(*c, *d, los[q] as int) || los[q] >= his[q]),
        decreases ne - j,
    {
        let lo = en.los[j];
        if lo < en.his[j] {
            proof {
                assert(los[j as int] == d.offs@[ents[j as int] as int]);
                assert(his[j as int] == d.offs@[ents[j as int] + 1]);
                lemma_offs_mono(*c, *d, ents[j as int] + 1, nk);
                lemma_drow(*c, *d, lo as int);
            }
            let g = shr(lo, d.sl, Ghost(c.bs_l));
            let s = (d.ib[g] + d.ic[lo] as u64) as usize;
            let ghost s0 = en.sf@;
            put(&mut en.sf, j, s);
            proof {
                assert forall|q: int| 0 <= q < j + 1 implies (#[trigger] en.sf@[q] as int == drow(*c, *d, los[q] as int) || los[q] >= his[q]) by {
                    if q < j {
                        assert(s0[q] as int == drow(*c, *d, los[q] as int) || los[q] >= his[q]);
                    }
                }
            }
        }
        j = j + 1;
    }
}

/// Walk the positions `[lo, hi)` of passing entry `ent`: buffer their rows, counting those in `[la, lb)`, and flush
/// full batches. `(false, _)` when a year's mass of the task's positions would pass `i128::MAX`.
fn walk_entry(c: &Cols, f: &PFilter, nt: &NTab, d: &Dirs, e0: usize, e1: usize, la: usize, lb: usize, b: &mut Bufs,
    acc: &mut Acc, nb: &mut usize, ent: usize, lo: usize, hi: usize, s_first: usize, Ghost(k0): Ghost<int>)
    -> (r: (bool, Ghost<int>))
    requires
        idx_pre(*c, *f, *nt, *d, e0 as int, e1 as int, la as int, lb as int),
        e0 <= ent < e1, lo == d.offs@[ent as int], hi == d.offs@[ent + 1],
        d.offs@[e0 as int] <= lo <= hi <= d.offs@[e1 as int],
        lo < hi ==> s_first as int == drow(*c, *d, lo as int),
        pmatch(*f, d.pkmin + ent),
        bufs_ok(*old(b)),
        batch_inv(*c, *f, *nt, *d, *old(acc), old(b).rows@, *old(nb) as int, d.offs@[e0 as int] as int, lo as int, k0),
    ensures
        bufs_ok(*final(b)),
        r.0 ==> batch_inv(*c, *f, *nt, *d, *final(acc), final(b).rows@, *final(nb) as int, d.offs@[e0 as int] as int,
            hi as int, r.1@),
        !r.0 ==> acc_idx(*c, pm_of(*f), nt_view(*nt), *d, d.offs@[e0 as int] as int, d.offs@[e1 as int] as int).m0 > i128::MAX
            || acc_idx(*c, pm_of(*f), nt_view(*nt), *d, d.offs@[e0 as int] as int, d.offs@[e1 as int] as int).m1 > i128::MAX,
    no_unwind
{
    let ghost pm = pm_of(*f);
    let ghost ns = nt_view(*nt);
    let ghost nk = d.offs@.len() - 1;
    let ghost p0 = d.offs@[e0 as int] as int;
    let ghost p1 = d.offs@[e1 as int] as int;
    let ghost mut k: int = k0;
    proof {
        lemma_offs_mono(*c, *d, e1 as int, nk);
    }
    let mut p = lo;
    while p < hi
        invariant
            idx_pre(*c, *f, *nt, *d, e0 as int, e1 as int, la as int, lb as int),
            pm == pm_of(*f), ns == nt_view(*nt), nk == d.offs@.len() - 1,
            p0 == d.offs@[e0 as int], p1 == d.offs@[e1 as int], p1 <= c.n_l,
            e0 <= ent < e1, lo == d.offs@[ent as int], hi == d.offs@[ent + 1], p0 <= lo <= hi <= p1,
            lo < hi ==> s_first as int == drow(*c, *d, lo as int),
            pm(d.pkmin + ent),
            bufs_ok(*b), lo <= p <= hi,
            batch_inv(*c, *f, *nt, *d, *acc, b.rows@, *nb as int, p0, p as int, k),
        decreases hi - p,
    {
        proof {
            lemma_entry_key(*c, *d, ent as int, p as int);
            lemma_drow(*c, *d, p as int);
        }
        let s = if p == lo {
            s_first
        } else {
            let g = shr(p, d.sl, Ghost(c.bs_l));
            (d.ib[g] + d.ic[p] as u64) as usize
        };
        proof {
            assert(s as int == drow(*c, *d, p as int));
            assert(gl(*c, pm, ns, *d, p as int) == lc(*c, pm, ns, s as int));
        }
        // Write the row into the next free slot always and count it only when it lies in `[la, lb)`: no branch on
        // the window test (rows outside the window contribute nothing, `bounds_ok`).
        if *nb == BATCH {
            let ok = flush(c, nt, d, b, *nb, acc, Ghost(pm), Ghost(k));
            if !ok {
                proof {
                    lemma_idx_mass_mono(*c, pm, ns, *d, p0, p as int, p1);
                }
                return (false, Ghost(k));
            }
            proof {
                k = k + *nb;
                lemma_acc_add_zero(acc_view(*acc));
            }
            *nb = 0;
        }
        let n0 = *nb;
        let ghost r0 = b.rows@;
        put(&mut b.rows, n0, s);
        let inw: usize = if la <= s && s < lb { 1 } else { 0 };
        proof {
            lemma_rows_put(*c, pm, ns, r0, n0 as int, s);
            if inw == 1 {
                lemma_acc_add_assoc(acc_view(*acc), acc_rows(*c, pm, ns, r0, n0 as int), acc_of(lc(*c, pm, ns, s as int)));
                assert forall|q: int| 0 <= q < n0 + 1 implies #[trigger] row_in(*c, pm, b.rows@, q) by {
                    if q < n0 {
                        assert(row_in(*c, pm, r0, q));
                    }
                }
            } else {
                assert(lc(*c, pm, ns, s as int) is None);
                lemma_acc_add_zero(acc_idx(*c, pm, ns, *d, p0, p as int));
                assert forall|q: int| 0 <= q < n0 implies #[trigger] row_in(*c, pm, b.rows@, q) by {
                    assert(row_in(*c, pm, r0, q));
                }
            }
        }
        *nb = n0 + inw;
        p = p + 1;
    }
    (true, Ghost(k))
}

/// Walk the batch `en.ents[0 .. ne)` of the passing entries of `[e, x)` (`coll_ok`, ranges and first rows gathered):
/// from the batch invariant at the first position of entry `e` to the one at the first position of entry `x`.
fn walk_batch(c: &Cols, f: &PFilter, nt: &NTab, d: &Dirs, e0: usize, e1: usize, la: usize, lb: usize, b: &mut Bufs,
    acc: &mut Acc, nb: &mut usize, en: &Ents, ne: usize, e: usize, x: usize, Ghost(k0): Ghost<int>)
    -> (r: (bool, Ghost<int>))
    requires
        idx_pre(*c, *f, *nt, *d, e0 as int, e1 as int, la as int, lb as int),
        bufs_ok(*old(b)), ents_ok(*en), e0 <= e < x <= e1,
        coll_ok(*f, *d, en.ents@, ne as int, e as int, x as int),
        forall|q: int| 0 <= q < ne ==> #[trigger] en.los@[q] == d.offs@[en.ents@[q] as int]
            && en.his@[q] == d.offs@[en.ents@[q] + 1]
            && (en.los@[q] < en.his@[q] ==> en.sf@[q] as int == drow(*c, *d, en.los@[q] as int)),
        batch_inv(*c, *f, *nt, *d, *old(acc), old(b).rows@, *old(nb) as int, d.offs@[e0 as int] as int,
            d.offs@[e as int] as int, k0),
    ensures
        bufs_ok(*final(b)),
        r.0 ==> batch_inv(*c, *f, *nt, *d, *final(acc), final(b).rows@, *final(nb) as int, d.offs@[e0 as int] as int,
            d.offs@[x as int] as int, r.1@),
        !r.0 ==> acc_idx(*c, pm_of(*f), nt_view(*nt), *d, d.offs@[e0 as int] as int, d.offs@[e1 as int] as int).m0 > i128::MAX
            || acc_idx(*c, pm_of(*f), nt_view(*nt), *d, d.offs@[e0 as int] as int, d.offs@[e1 as int] as int).m1 > i128::MAX,
    no_unwind
{
    let ghost pm = pm_of(*f);
    let ghost ns = nt_view(*nt);
    let ghost nk = d.offs@.len() - 1;
    let ghost p0 = d.offs@[e0 as int] as int;
    let ghost p1 = d.offs@[e1 as int] as int;
    let ghost ents = en.ents@;
    let ghost mut k: int = k0;
    proof {
        lemma_offs_mono(*c, *d, e0 as int, e1 as int);
        lemma_offs_mono(*c, *d, e1 as int, nk);
    }
    let mut j: usize = 0;
    let mut cur: usize = e;
    while j < ne
        invariant
            idx_pre(*c, *f, *nt, *d, e0 as int, e1 as int, la as int, lb as int),
            pm == pm_of(*f), ns == nt_view(*nt), nk == d.offs@.len() - 1,
            p0 == d.offs@[e0 as int], p1 == d.offs@[e1 as int], p0 <= p1 <= c.n_l,
            bufs_ok(*b), ents_ok(*en), e0 <= e < x <= e1, j <= ne, en.ents@ == ents,
            coll_ok(*f, *d, ents, ne as int, e as int, x as int),
            forall|q: int| 0 <= q < ne ==> #[trigger] en.los@[q] == d.offs@[ents[q] as int]
                && en.his@[q] == d.offs@[ents[q] + 1]
                && (en.los@[q] < en.his@[q] ==> en.sf@[q] as int == drow(*c, *d, en.los@[q] as int)),
            cur as int == gap_lo(ents, e as int, j as int), e <= cur <= x,
            batch_inv(*c, *f, *nt, *d, *acc, b.rows@, *nb as int, p0, d.offs@[cur as int] as int, k),
        decreases ne - j,
    {
        let ent = en.ents[j];
        proof {
            // The entries `[cur, ent)` fail the filter: their positions add nothing.
            assert(gap_lo(ents, e as int, j as int) <= ents[j as int] < x);
            assert(gap_fail(*f, *d, ents, e as int, j as int));
            assert forall|z: int| cur <= z < ent implies !#[trigger] pmatch(*f, d.pkmin + z) by {
                assert(efail(*f, *d, z));
            }
            lemma_offs_mono(*c, *d, cur as int, ent as int);
            lemma_offs_mono(*c, *d, ent as int, e1 as int);
            lemma_entries_none(*c, *f, *nt, *d, cur as int, ent as int);
            lemma_idx_none(*c, pm, ns, *d, d.offs@[cur as int] as int, d.offs@[ent as int] as int);
            lemma_idx_split(*c, pm, ns, *d, p0, d.offs@[cur as int] as int, d.offs@[ent as int] as int);
            lemma_acc_add_zero(acc_idx(*c, pm, ns, *d, p0, d.offs@[cur as int] as int));
            assert(pmatch(*f, d.pkmin + ents[j as int]));
            lemma_offs_mono(*c, *d, ent as int, ent + 1);
            lemma_offs_mono(*c, *d, ent + 1, e1 as int);
        }
        let lo = en.los[j];
        let hi = en.his[j];
        let s_first = en.sf[j];
        let (ok, Ghost(k2)) = walk_entry(c, f, nt, d, e0, e1, la, lb, b, acc, nb, ent, lo, hi, s_first,
            Ghost(k));
        if !ok {
            return (false, Ghost(k));
        }
        proof {
            k = k2;
        }
        cur = ent + 1;
        j = j + 1;
    }
    proof {
        // The entries `[cur, x)` after the batch fail the filter.
        assert forall|z: int| cur <= z < x implies !#[trigger] pmatch(*f, d.pkmin + z) by {
            assert(efail(*f, *d, z));
        }
        lemma_offs_mono(*c, *d, cur as int, x as int);
        lemma_offs_mono(*c, *d, x as int, e1 as int);
        lemma_entries_none(*c, *f, *nt, *d, cur as int, x as int);
        lemma_idx_none(*c, pm, ns, *d, d.offs@[cur as int] as int, d.offs@[x as int] as int);
        lemma_idx_split(*c, pm, ns, *d, p0, d.offs@[cur as int] as int, d.offs@[x as int] as int);
        lemma_acc_add_zero(acc_idx(*c, pm, ns, *d, p0, d.offs@[cur as int] as int));
    }
    (true, Ghost(k))
}

/// One batch of the walk from entry `e`: collect the next passing entries, gather their ranges, walk them; `x` is the
/// entry the next batch starts at.
fn batch_step(c: &Cols, f: &PFilter, nt: &NTab, d: &Dirs, e0: usize, e1: usize, la: usize, lb: usize, b: &mut Bufs,
    acc: &mut Acc, nb: &mut usize, en: &mut Ents, e: usize, Ghost(k0): Ghost<int>) -> (r: (bool, usize, Ghost<int>))
    requires
        idx_pre(*c, *f, *nt, *d, e0 as int, e1 as int, la as int, lb as int),
        bufs_ok(*old(b)), ents_ok(*old(en)), e0 <= e < e1,
        batch_inv(*c, *f, *nt, *d, *old(acc), old(b).rows@, *old(nb) as int, d.offs@[e0 as int] as int,
            d.offs@[e as int] as int, k0),
    ensures
        bufs_ok(*final(b)), ents_ok(*final(en)), e < r.1 <= e1,
        r.0 ==> batch_inv(*c, *f, *nt, *d, *final(acc), final(b).rows@, *final(nb) as int, d.offs@[e0 as int] as int,
            d.offs@[r.1 as int] as int, r.2@),
        !r.0 ==> acc_idx(*c, pm_of(*f), nt_view(*nt), *d, d.offs@[e0 as int] as int, d.offs@[e1 as int] as int).m0 > i128::MAX
            || acc_idx(*c, pm_of(*f), nt_view(*nt), *d, d.offs@[e0 as int] as int, d.offs@[e1 as int] as int).m1 > i128::MAX,
    no_unwind
{
    let ghost nk = d.offs@.len() - 1;
    let (ne, x) = collect(f, d, e, e1, en);
    let ghost ents = en.ents@;
    proof {
        assert forall|j: int| 0 <= j < ne implies #[trigger] ents[j] < nk by {
            assert(gap_lo(ents, e as int, j) <= ents[j] < x);
        }
    }
    gather(c, d, en, ne);
    let (ok, Ghost(k2)) = walk_batch(c, f, nt, d, e0, e1, la, lb, b, acc, nb, en, ne, e, x, Ghost(k0));
    (ok, x, Ghost(k2))
}

/// The accumulators of the lineitem rows of directory entries `[e0, e1)` (only rows in `[la, lb)` are counted).
/// Batches of up to `G` passing entries: collect them, gather their ranges and first rows, then walk their
/// positions; the skipped entries between them fail the filter and hold no contributing position.
fn idx_range(c: &Cols, f: &PFilter, nt: &NTab, d: &Dirs, e0: usize, e1: usize, la: usize, lb: usize, b: Bufs,
    en: Ents) -> (out: Acc)
    requires
        idx_pre(*c, *f, *nt, *d, e0 as int, e1 as int, la as int, lb as int),
        bufs_ok(b), ents_ok(en),
    ensures idx_post(*c, *f, *nt, *d, e0 as int, e1 as int, out),
    no_unwind
{
    let ghost pm = pm_of(*f);
    let ghost ns = nt_view(*nt);
    let ghost nk = d.offs@.len() - 1;
    let ghost p0 = d.offs@[e0 as int] as int;
    let ghost p1 = d.offs@[e1 as int] as int;
    let ghost mut k: int = 0;
    let mut b = b;
    let mut en = en;
    let mut acc = acc_new();
    let mut nb: usize = 0;
    let mut e = e0;
    proof {
        lemma_offs_mono(*c, *d, e0 as int, e1 as int);
        lemma_offs_mono(*c, *d, e1 as int, nk);
    }
    while e < e1
        invariant
            idx_pre(*c, *f, *nt, *d, e0 as int, e1 as int, la as int, lb as int),
            pm == pm_of(*f), ns == nt_view(*nt), nk == d.offs@.len() - 1,
            p0 == d.offs@[e0 as int], p1 == d.offs@[e1 as int], p0 <= p1 <= c.n_l,
            bufs_ok(b), ents_ok(en), e0 <= e <= e1,
            batch_inv(*c, *f, *nt, *d, acc, b.rows@, nb as int, p0, d.offs@[e as int] as int, k),
        decreases e1 - e,
    {
        let (ok, x, Ghost(k2)) = batch_step(c, f, nt, d, e0, e1, la, lb, &mut b, &mut acc, &mut nb, &mut en, e, Ghost(k));
        if !ok {
            acc.ovf = true;
            return acc;
        }
        proof {
            k = k2;
        }
        e = x;
    }
    let ok = flush(c, nt, d, &mut b, nb, &mut acc, Ghost(pm), Ghost(k));
    if !ok {
        acc.ovf = true;
    }
    acc
}

/// One index task: directory entries `[e0, e1)`, lineitem rows restricted to `[la, lb)`, with its buffers.
pub struct IdxTask {
    pub c: Cols,
    pub f: Arc<PFilter>,
    pub nt: Arc<NTab>,
    pub d: Dirs,
    pub e0: usize,
    pub e1: usize,
    pub la: usize,
    pub lb: usize,
    pub b: Bufs,
    pub en: Ents,
}

impl WorkerTask for IdxTask {
    type Output = Acc;

    open spec fn pre(&self) -> bool {
        &&& idx_pre(self.c, *self.f, *self.nt, self.d, self.e0 as int, self.e1 as int, self.la as int, self.lb as int)
        &&& bufs_ok(self.b)
        &&& ents_ok(self.en)
    }

    open spec fn post(&self, out: Acc) -> bool {
        idx_post(self.c, *self.f, *self.nt, self.d, self.e0 as int, self.e1 as int, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.e0 as u64, self.e1 as u64)
    }

    fn run(self) -> (out: Acc) {
        let f: &PFilter = &*self.f;
        let nt: &NTab = &*self.nt;
        idx_range(&self.c, f, nt, &self.d, self.e0, self.e1, self.la, self.lb, self.b, self.en)
    }
}

/// Task `t` of `ts` covers entries `[es[t], es[t + 1])`.
pub open spec fn itasks_ok(ts: Seq<IdxTask>, es: Seq<int>, c: Cols, f: PFilter, nt: NTab, d: Dirs) -> bool {
    &&& es.len() == ts.len() + 1
    &&& forall|t: int| 0 <= t < ts.len() ==> {
        &&& (#[trigger] ts[t]).c == c && *ts[t].f == f && *ts[t].nt == nt && ts[t].d == d
        &&& ts[t].e0 as int == es[t] && ts[t].e1 as int == es[t + 1]
        &&& ts[t].pre()
    }
}

/// At most `workers` tasks of about equal entry counts tiling the directory's entries.
/// Most worker tasks of one call (below the 64 logical CPUs of the host, measured: 60 tasks beat 64 at 64 workers).
pub const MAX_TASKS: usize = 60;

pub fn make_idx_tasks(c: Cols, f: Arc<PFilter>, nt: Arc<NTab>, d: Dirs, la: usize, lb: usize, workers: usize)
    -> (r: (Vec<IdxTask>, Ghost<Seq<int>>))
    requires
        idx_pre(c, *f, *nt, d, 0, d.offs@.len() - 1, la as int, lb as int),
        1 <= workers <= MAX_WORKERS,
    ensures
        1 <= r.0@.len() <= workers,
        itasks_ok(r.0@, r.1@, c, *f, *nt, d),
        r.1@[0] == 0, r.1@[r.0@.len() as int] == d.offs@.len() - 1,
{
    let nk = d.offs.len() - 1;
    // At most `MAX_TASKS` threads: with every logical CPU busy, the scheduler starts some worker milliseconds late.
    let w = if workers > MAX_TASKS { MAX_TASKS } else { workers };
    let count = if w < nk { w } else if nk >= 1 { nk } else { 1 };
    let chunk = nk / count;
    let mut tasks: Vec<IdxTask> = Vec::new();
    let ghost mut es: Seq<int> = seq![0int];
    let mut e0: usize = 0;
    let mut t: usize = 0;
    while t < count
        invariant
            idx_pre(c, *f, *nt, d, 0, d.offs@.len() - 1, la as int, lb as int),
            nk == d.offs@.len() - 1, 1 <= count <= workers, t <= count,
            tasks@.len() == t, es.len() == t + 1, es[0] == 0, es[t as int] == e0, e0 <= nk,
            t == count ==> e0 == nk,
            itasks_ok(tasks@, es, c, *f, *nt, d),
        decreases count - t,
    {
        let e1 = if t + 1 == count { nk } else if chunk < nk - e0 { e0 + chunk } else { nk };
        let ghost (old_tasks, old_es) = (tasks@, es);
        let task = IdxTask { c, f: f.clone(), nt: nt.clone(), d, e0, e1, la, lb, b: bufs_new(), en: ents_new() };
        proof {
            assert(task.pre());
        }
        tasks.push(task);
        proof {
            es = es.push(e1 as int);
            assert forall|k: int| 0 <= k < tasks@.len() implies {
                &&& (#[trigger] tasks@[k]).c == c && *tasks@[k].f == *f && *tasks@[k].nt == *nt && tasks@[k].d == d
                &&& tasks@[k].e0 as int == es[k] && tasks@[k].e1 as int == es[k + 1]
                &&& tasks@[k].pre()
            } by {
                if k < t {
                    assert(tasks@[k] == old_tasks[k]);
                    assert(es[k] == old_es[k] && es[k + 1] == old_es[k + 1]);
                }
            }
        }
        e0 = e1;
        t = t + 1;
    }
    (tasks, Ghost(es))
}

// ------------------------------------------------------------------------------------------------ merge

/// The merged task outputs: the accumulators of key index positions `[offs[es[0]], offs[es[n]])`; `ovf` when that
/// range's mass passes `i128::MAX`.
pub fn merge_idx(outs: &Vec<Acc>, Ghost(c): Ghost<Cols>, Ghost(f): Ghost<PFilter>, Ghost(nt): Ghost<NTab>,
    Ghost(d): Ghost<Dirs>, Ghost(es): Ghost<Seq<int>>) -> (r: Acc)
    requires
        dirs_ok(c, d),
        outs@.len() >= 1,
        es.len() == outs@.len() + 1,
        0 <= es[0],
        es[outs@.len() as int] <= d.offs@.len() - 1,
        forall|t: int| 0 <= t < outs@.len() ==> #[trigger] es[t] <= es[t + 1],
        forall|t: int| 0 <= t < outs@.len() ==> idx_post(c, f, nt, d, es[t], es[t + 1], #[trigger] outs@[t]),
    ensures ({
        let s = acc_idx(c, pm_of(f), nt_view(nt), d, d.offs@[es[0]] as int, d.offs@[es[outs@.len() as int]] as int);
        &&& !r.ovf ==> acc_view(r) == s
        &&& r.ovf ==> s.m0 > i128::MAX || s.m1 > i128::MAX
    }),
{
    let ghost pm = pm_of(f);
    let ghost ns = nt_view(nt);
    let n = outs.len();
    let ghost nk = d.offs@.len() - 1;
    let ghost bs: Seq<int> = Seq::new((n + 1) as nat, |t: int| d.offs@[es[t]] as int);
    proof {
        assert forall|t: int| 0 <= t <= n implies es[0] <= #[trigger] es[t] <= es[n as int] by {
            lemma_es_mono(es, n as int, 0, t);
            lemma_es_mono(es, n as int, t, n as int);
        }
        assert forall|t: int| 0 <= t < n implies #[trigger] bs[t] <= bs[t + 1] by {
            lemma_offs_mono(c, d, es[t], es[t + 1]);
        }
        assert forall|t: int| 0 <= t <= n implies bs[0] <= #[trigger] bs[t] <= bs[n as int] by {
            lemma_offs_mono(c, d, es[0], es[t]);
            lemma_offs_mono(c, d, es[t], es[n as int]);
        }
        lemma_offs_mono(c, d, es[n as int], nk);
    }
    let ghost end = bs[n as int];
    let mut tot = acc_new();
    let mut t: usize = 0;
    while t < n
        invariant
            dirs_ok(c, d), nk == d.offs@.len() - 1,
            n == outs@.len(), es.len() == n + 1,
            bs == Seq::new((n + 1) as nat, |t: int| d.offs@[es[t]] as int),
            end == bs[n as int], 0 <= bs[0], end <= c.n_l,
            forall|k: int| 0 <= k <= n ==> bs[0] <= #[trigger] bs[k] <= end,
            forall|k: int| 0 <= k < n ==> #[trigger] bs[k] <= bs[k + 1],
            forall|k: int| 0 <= k < n ==> idx_post(c, f, nt, d, es[k], es[k + 1], #[trigger] outs@[k]),
            pm == pm_of(f), ns == nt_view(nt),
            t <= n,
            !tot.ovf,
            acc_view(tot) == acc_idx(c, pm, ns, d, bs[0], bs[t as int]),
        decreases n - t,
    {
        let o = &outs[t];
        let ghost (a, b, e) = (bs[0], bs[t as int], bs[t + 1]);
        proof {
            assert(idx_post(c, f, nt, d, es[t as int], es[t + 1], outs@[t as int]));
            assert(bs[t as int] == d.offs@[es[t as int]] && bs[t + 1] == d.offs@[es[t + 1]]);
            lemma_idx_split(c, pm, ns, d, a, b, e);
            lemma_idx_sane(c, pm, ns, d, a, b);
            lemma_idx_sane(c, pm, ns, d, b, e);
            lemma_idx_mass_mono(c, pm, ns, d, a, e, end);
        }
        if o.ovf {
            proof {
                lemma_idx_sane(c, pm, ns, d, a, b);
                lemma_idx_mass_mono(c, pm, ns, d, b, e, end);
                lemma_idx_split(c, pm, ns, d, a, b, end);
                lemma_idx_split(c, pm, ns, d, b, e, end);
                lemma_idx_sane(c, pm, ns, d, e, end);
            }
            let mut r = acc_new();
            r.ovf = true;
            return r;
        }
        let ok = acc_merge(&mut tot, o, Ghost(b - a), Ghost(e - b));
        if !ok {
            proof {
                lemma_idx_mass_mono(c, pm, ns, d, a, e, end);
            }
            let mut r = acc_new();
            r.ovf = true;
            return r;
        }
        t = t + 1;
    }
    tot
}

/// Boundaries of a nondecreasing sequence are ordered.
proof fn lemma_es_mono(es: Seq<int>, n: int, a: int, b: int)
    requires
        es.len() == n + 1,
        forall|k: int| 0 <= k < n ==> #[trigger] es[k] <= es[k + 1],
        0 <= a <= b <= n,
    ensures es[a] <= es[b],
    decreases b - a,
{
    if a < b {
        lemma_es_mono(es, n, a, b - 1);
        assert(es[b - 1] <= es[b]);
    }
}

} // verus!
