//! The counts of the selected suppliers over all lineitem rows (`supplier_counts`).
//!
//! 1. The selected suppliers (`build_sup`): the nations named `$1` (`text_is`), per nation key the number of such
//!    nations (a table over keys `0..NKEYS` when every nation key is small, else a scan per supplier), and the
//!    supplier rows whose nation key has one, ascending (`SupMap::sel`); with dense supplier keys also the row map
//!    `cmap` for the scan's key lookup.
//! 2. The lineitem rows are split into at most `SCAN_TASKS` (24) ranges, fewer when `workers` is smaller (the scan
//!    is bound by memory, and more threads only contend), that start at a change of `l_orderkey`; one `scan::ScanTask` per range (or the calling thread alone for one range).
//! 3. When every task saw its keys in order and every range boundary is ordered, `l_orderkey` is sorted
//!    (`runs::lemma_pairs_join`), every task's counts are its range's counts, and they add up in range order.
//!    Otherwise the calling thread computes every count row by row from the definitions (`naive_counts`, slow).
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::{fork_join, Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::gendb_entry::stores::StoresView;
use crate::link::query::{text_at, text_wf, TextView};
use crate::agent::cols::*;
use crate::agent::nf::*;
use crate::agent::runs::*;
use crate::agent::scan::*;
use crate::agent::common::zeroed::*;
use crate::agent::common::bits64::*;

verus! {

/// Nation keys below this bound are counted in a table.
pub const NKEYS: usize = 1024;

// ------------------------------------------------------------------------------------------------ the parameter

/// Whether value `n` of a text column is the bytes `p`.
pub fn text_is(off: &[i64], bytes: &[u8], n: usize, p: &[u8], Ghost(t): Ghost<TextView>, Ghost(rows): Ghost<int>) -> (r: bool)
    requires off@ == t.offsets, bytes@ == t.bytes, text_wf(t, rows), n < rows,
    ensures r == (text_at(t, n as int) == p@),
{
    let a = off[n];
    let b = off[n + 1];
    let blen = bytes.len();
    proof {
        assert(0 <= t.offsets[n as int] <= t.offsets[n + 1] <= t.bytes.len());
    }
    let len = (b - a) as usize;
    if len != p.len() {
        return false;
    }
    let au = a as usize;
    let mut i: usize = 0;
    while i < len
        invariant
            off@ == t.offsets, bytes@ == t.bytes, text_wf(t, rows), n < rows,
            a == t.offsets[n as int], b == t.offsets[n + 1], au == a, len == b - a, len == p@.len(),
            0 <= a <= b <= bytes@.len(), blen == bytes@.len(),
            i <= len,
            forall|k: int| 0 <= k < i ==> bytes@[au + k] == p@[k],
        decreases len - i,
    {
        if bytes[au + i] != p[i] {
            proof { assert(text_at(t, n as int)[i as int] == bytes@[au + i]); }
            return false;
        }
        i = i + 1;
    }
    proof { assert(text_at(t, n as int) =~= p@); }
    true
}

// ------------------------------------------------------------------------------------------------ selected suppliers

/// `sel` lists exactly the supplier rows with a nation named `p`.
pub open spec fn sel_exact(m: SupMap, sv: StoresView, p: Seq<u8>) -> bool {
    &&& forall|ci: int| 0 <= ci < m.nsel ==> nw(sv, p, #[trigger] m.sel@[ci] as int) > 0
    &&& forall|s: int| 0 <= s < n_s(sv) && nw(sv, p, s) > 0 ==> exists|ci: int| 0 <= ci < m.nsel && #[trigger] m.sel@[ci] == s
}

/// Per nation row: whether its name is `p`.
fn nation_matches(c: &Cols, p: &[u8], Ghost(sv): Ghost<StoresView>) -> (nm: Vec<bool>)
    requires cols_ok(*c, sv),
    ensures nm@.len() == c.nn, forall|n: int| 0 <= n < c.nn ==> #[trigger] nm@[n] == (nname(sv, n) == p@),
{
    let mut nm: Vec<bool> = Vec::new();
    let mut n: usize = 0;
    while n < c.nn
        invariant cols_ok(*c, sv), n <= c.nn, nm@.len() == n,
            forall|k: int| 0 <= k < n ==> #[trigger] nm@[k] == (nname(sv, k) == p@),
        decreases c.nn - n,
    {
        let b = text_is(c.nnoff, c.nnb, n, p, Ghost(nname_col(sv)), Ghost(n_n(sv)));
        nm.push(b);
        n = n + 1;
    }
    nm
}

/// The number of nations named `p` with key `v`, by a scan of the nations.
fn ncount(c: &Cols, nm: &Vec<bool>, v: i64, Ghost(sv): Ghost<StoresView>, Ghost(p): Ghost<Seq<u8>>) -> (w: u64)
    requires cols_ok(*c, sv), nm@.len() == c.nn, forall|n: int| 0 <= n < c.nn ==> #[trigger] nm@[n] == (nname(sv, n) == p),
    ensures w as int == ncnt(sv, p, v as int, n_n(sv)),
{
    let mut w: u64 = 0;
    let mut n: usize = 0;
    while n < c.nn
        invariant cols_ok(*c, sv), nm@.len() == c.nn, forall|k: int| 0 <= k < c.nn ==> #[trigger] nm@[k] == (nname(sv, k) == p),
            n <= c.nn, w as int == ncnt(sv, p, v as int, n as int), w <= n,
        decreases c.nn - n,
    {
        if nm[n] && c.nkey[n] == v {
            w = w + 1;
        }
        n = n + 1;
    }
    w
}

/// The table of nation counts per small key, when every nation key is small (`r.0`).
fn nation_table(c: &Cols, nm: &Vec<bool>, Ghost(sv): Ghost<StoresView>, Ghost(p): Ghost<Seq<u8>>) -> (r: (bool, Vec<u64>))
    requires cols_ok(*c, sv), nm@.len() == c.nn, forall|n: int| 0 <= n < c.nn ==> #[trigger] nm@[n] == (nname(sv, n) == p),
    ensures
        r.1@.len() == NKEYS,
        r.0 ==> forall|v: int| 0 <= v < NKEYS ==> #[trigger] r.1@[v] as int == ncnt(sv, p, v, n_n(sv)),
        r.0 ==> forall|n: int| 0 <= n < n_n(sv) ==> 0 <= #[trigger] nkey(sv)[n] < NKEYS,
{
    let mut tab = zeros_u64(NKEYS);
    let mut small = true;
    let mut n: usize = 0;
    while n < c.nn
        invariant
            cols_ok(*c, sv), nm@.len() == c.nn, forall|k: int| 0 <= k < c.nn ==> #[trigger] nm@[k] == (nname(sv, k) == p),
            n <= c.nn, tab@.len() == NKEYS,
            small ==> forall|v: int| 0 <= v < NKEYS ==> #[trigger] tab@[v] as int == ncnt(sv, p, v, n as int),
            small ==> forall|v: int| 0 <= v < NKEYS ==> #[trigger] tab@[v] <= n,
            small ==> forall|k: int| 0 <= k < n ==> 0 <= #[trigger] nkey(sv)[k] < NKEYS,
        decreases c.nn - n,
    {
        let k = c.nkey[n];
        if k >= 0 && k < NKEYS as i64 {
            if nm[n] && small {
                let ku = k as usize;
                tab[ku] = tab[ku] + 1;
            }
        } else {
            small = false;
        }
        n = n + 1;
    }
    (small, tab)
}

/// The selected suppliers and the scan's key lookup.
pub fn build_sup(c: &Cols, p: &[u8], Ghost(sv): Ghost<StoresView>) -> (m: SupMap)
    requires cols_ok(*c, sv),
    ensures sup_ok(m, sv), sel_exact(m, sv, p@), m.skey == c.skey,
{
    let ghost pb = p@;
    let nm = nation_matches(c, p, Ghost(sv));
    let (small, tab) = nation_table(c, &nm, Ghost(sv), Ghost(pb));
    let mut sel: Vec<usize> = Vec::new();
    let mut s: usize = 0;
    while s < c.ns
        invariant
            cols_ok(*c, sv), nm@.len() == c.nn, forall|n: int| 0 <= n < c.nn ==> #[trigger] nm@[n] == (nname(sv, n) == pb),
            tab@.len() == NKEYS,
            small ==> forall|v: int| 0 <= v < NKEYS ==> #[trigger] tab@[v] as int == ncnt(sv, pb, v, n_n(sv)),
            small ==> forall|n: int| 0 <= n < n_n(sv) ==> 0 <= #[trigger] nkey(sv)[n] < NKEYS,
            s <= c.ns,
            sel_ok(sel@, s as int),
            forall|ci: int| 0 <= ci < sel@.len() ==> nw(sv, pb, #[trigger] sel@[ci] as int) > 0,
            forall|t: int| 0 <= t < s && nw(sv, pb, t) > 0 ==> exists|ci: int| 0 <= ci < sel@.len() && #[trigger] sel@[ci] == t,
        decreases c.ns - s,
    {
        let k = c.snk[s];
        let w: u64 = if small {
            if k >= 0 && k < NKEYS as i64 {
                tab[k as usize]
            } else {
                proof {
                    assert forall|n: int| 0 <= n < n_n(sv) implies !#[trigger] nhit(sv, pb, k as int, n) by {}
                    lemma_ncnt_le1(sv, pb, k as int, n_n(sv));
                }
                0
            }
        } else {
            ncount(c, &nm, k, Ghost(sv), Ghost(pb))
        };
        proof { assert(w as int == nw(sv, pb, s as int)); }
        let ghost sel0 = sel@;
        if w > 0 {
            sel.push(s);
            proof {
                assert forall|ci: int| 0 <= ci < sel@.len() implies nw(sv, pb, #[trigger] sel@[ci] as int) > 0 by {
                    if ci < sel0.len() { assert(sel@[ci] == sel0[ci]); }
                }
            }
        }
        proof {
            assert forall|t: int| 0 <= t < s + 1 && nw(sv, pb, t) > 0 implies exists|ci: int| 0 <= ci < sel@.len() && #[trigger] sel@[ci] == t by {
                if t < s {
                    let ci = choose|ci: int| 0 <= ci < sel0.len() && #[trigger] sel0[ci] == t;
                    assert(sel@[ci] == t);
                } else {
                    assert(sel@[sel0.len() as int] == t);
                }
            }
        }
        s = s + 1;
    }
    let nsel = sel.len();
    // dense supplier keys: `s_suppkey[s] == s_suppkey[0] + s`
    let base: i64 = if c.ns > 0 { c.skey[0] } else { 0 };
    let mut dense = nsel < u32::MAX as usize;
    let mut t: usize = 0;
    while t < c.ns && dense
        invariant
            cols_ok(*c, sv), t <= c.ns, c.ns > 0 ==> base == skey(sv)[0], nsel == sel@.len(),
            dense ==> nsel < u32::MAX,
            dense ==> forall|u: int| 0 <= u < t ==> #[trigger] skey(sv)[u] as int == base as int + u,
        decreases c.ns - t,
    {
        if c.skey[t] as i128 != base as i128 + t as i128 {
            dense = false;
        }
        t = t + 1;
    }
    let mut cmap: Vec<u32> = Vec::new();
    let mut nb: Vec<u64> = Vec::new();
    if dense {
        cmap = zeros_u32(c.ns);
        nb = zeros_u64(c.ns / 64 + 1);
        proof {
            assert forall|u: int| 0 <= u < c.ns implies #[trigger] nbit(nb@, u) == (cmap@[u] != 0) by {
                lemma_bit_zero((u % 64) as u64);
                assert(u / 64 < c.ns / 64 + 1) by (nonlinear_arith) requires 0 <= u < c.ns;
            }
        }
        let mut ci: usize = 0;
        while ci < nsel
            invariant
                cols_ok(*c, sv), nsel == sel@.len(), nsel < u32::MAX, sel_ok(sel@, c.ns as int), ci <= nsel, cmap@.len() == c.ns,
                forall|d: int| 0 <= d < ci ==> cmap@[#[trigger] sel@[d] as int] == d + 1,
                forall|u: int| 0 <= u < c.ns && #[trigger] cmap@[u] != 0 ==> cmap@[u] - 1 < ci && sel@[cmap@[u] - 1] == u,
                nb@.len() == c.ns / 64 + 1,
                forall|u: int| 0 <= u < c.ns ==> #[trigger] nbit(nb@, u) == (cmap@[u] != 0),
            decreases nsel - ci,
        {
            let ghost cm0 = cmap@;
            let ghost nb0 = nb@;
            let row = sel[ci];
            cmap[row] = (ci + 1) as u32;
            proof {
                assert(row / 64 < c.ns / 64 + 1) by (nonlinear_arith) requires row < c.ns;
            }
            let wd = nb[row / 64];
            nb[row / 64] = wd | (1u64 << ((row % 64) as u64));
            proof {
                assert forall|d: int| 0 <= d < ci + 1 implies cmap@[#[trigger] sel@[d] as int] == d + 1 by {
                    if d < ci {
                        assert(sel@[d] < sel@[ci as int]);
                    }
                }
                assert forall|u: int| 0 <= u < c.ns && #[trigger] cmap@[u] != 0 implies cmap@[u] - 1 < ci + 1 && sel@[cmap@[u] - 1] == u by {
                    if u != row as int {
                        assert(cmap@[u] == cm0[u]);
                    }
                }
                assert forall|u: int| 0 <= u < c.ns implies #[trigger] nbit(nb@, u) == (cmap@[u] != 0) by {
                    assert(nbit(nb0, u) == (cm0[u] != 0));
                    if u / 64 == row / 64 {
                        lemma_bit_or(wd, 1, (row % 64) as u64, (u % 64) as u64);
                        if u != row as int {
                            assert(u % 64 != row % 64);
                            assert(cmap@[u] == cm0[u]);
                        }
                    } else {
                        assert(u / 64 < c.ns / 64 + 1) by (nonlinear_arith) requires 0 <= u < c.ns;
                        assert(nb@[u / 64] == nb0[u / 64]);
                        if u != row as int {
                            assert(cmap@[u] == cm0[u]);
                        }
                    }
                }
            }
            ci = ci + 1;
        }
    }
    let tab = low_bit_table();
    let m = SupMap { dense, cmap, nb, tab, base, sel, skey: c.skey, ns: c.ns, nsel };
    proof {
        reveal(bitmap_ok);
    }
    proof {
        assert(m.sel@ == sel@);
    }
    m
}

// ------------------------------------------------------------------------------------------------ the general path

/// The EXISTS and the NOT EXISTS's subquery of lineitem row `i`, by a scan of every row.
fn others(c: &Cols, i: usize, Ghost(sv): Ghost<StoresView>) -> (r: (bool, bool))
    requires cols_ok(*c, sv), i < c.nl,
    ensures r.0 == ex2(sv, i as int), r.1 == ex3(sv, i as int),
{
    let mut e2 = false;
    let mut e3 = false;
    let mut j: usize = 0;
    while j < c.nl
        invariant
            cols_ok(*c, sv), i < c.nl, j <= c.nl,
            e2 == exists|t: int| 0 <= t < j && #[trigger] other_at(sv, i as int, t),
            e3 == exists|t: int| 0 <= t < j && #[trigger] other_at(sv, i as int, t) && late(sv, t),
        decreases c.nl - j,
    {
        if c.lk[j] == c.lk[i] && c.ls[j] != c.ls[i] {
            proof { assert(other_at(sv, i as int, j as int)); }
            e2 = true;
            if c.lr[j] > c.lc[j] {
                e3 = true;
            }
        }
        j = j + 1;
    }
    (e2, e3)
}

/// The counts computed from the definitions, row by row (any key order; quadratic, used only when `l_orderkey` is
/// not sorted).
pub fn naive_counts(c: &Cols, m: &SupMap, Ghost(sv): Ghost<StoresView>) -> (tot: Vec<u64>)
    requires cols_ok(*c, sv), sup_ok(*m, sv),
    ensures tot@.len() == m.nsel, forall|ci: int| 0 <= ci < m.nsel ==> #[trigger] tot@[ci] as int == ksum(sv, ckey(*m, ci), 0, n_l(sv)),
{
    let mut tot = zeros_u64(m.nsel);
    let mut i: usize = 0;
    while i < c.nl
        invariant
            cols_ok(*c, sv), sup_ok(*m, sv), i <= c.nl, tot@.len() == m.nsel,
            forall|ci: int| 0 <= ci < m.nsel ==> #[trigger] tot@[ci] as int == ksum(sv, ckey(*m, ci), 0, i as int),
            forall|ci: int| 0 <= ci < m.nsel ==> #[trigger] tot@[ci] <= i,
        decreases c.nl - i,
    {
        let ghost t0 = tot@;
        let mut hit: Option<usize> = None;
        if c.lr[i] > c.lc[i] {
            let (e2, e3) = others(c, i, Ghost(sv));
            if e2 && !e3 {
                match lookup(m, c.ls[i], Ghost(sv)) {
                    Some(ci) => {
                        let o = find_order(c.ok, c.no, c.lk[i], 0);
                        if o < c.no {
                            proof { lemma_ofs_found(sv, lk(sv)[i as int] as int, o as int); }
                            if status_f(c, o, Ghost(sv)) {
                                hit = Some(ci);
                            }
                        } else {
                            proof { lemma_ofs_none(sv, lk(sv)[i as int] as int); }
                        }
                    },
                    None => {},
                }
            }
        }
        if let Some(ci) = hit {
            tot[ci] = tot[ci] + 1;
        }
        proof {
            assert forall|ci: int| 0 <= ci < m.nsel implies #[trigger] tot@[ci] as int == ksum(sv, ckey(*m, ci), 0, i + 1) by {
                let v = ckey(*m, ci);
                assert(ksum(sv, v, 0, i + 1) == ksum(sv, v, 0, i as int) + lterm(sv, v, i as int));
                if lterm(sv, v, i as int) != 0 {
                    assert(ls(sv)[i as int] as int == v && lq(sv, i as int));
                }
                if let Some(c0) = hit {
                    if ci != c0 as int && v == ls(sv)[i as int] as int {
                        lemma_ckey_unique(*m, sv, ci, c0 as int);
                    }
                }
            }
        }
        i = i + 1;
    }
    tot
}

// ------------------------------------------------------------------------------------------------ the parallel path

/// The range bounds: ascending from 0 to `nl`, every inner bound at a key change.
pub open spec fn bounds_ok(sv: StoresView, lb: Seq<usize>, nt: int) -> bool {
    &&& lb.len() == nt + 1
    &&& lb[0] == 0
    &&& lb[nt] == n_l(sv)
    &&& forall|t: int| 0 <= t < nt ==> lb[t] <= #[trigger] lb[t + 1]
    &&& forall|t: int| 0 <= t <= nt ==> #[trigger] lb[t] <= n_l(sv)
    &&& forall|t: int| 0 <= t <= nt ==> (lb[t] == 0 || lb[t] == n_l(sv) || lk(sv)[lb[t] - 1] != lk(sv)[#[trigger] lb[t] as int])
}

/// `nt` ranges of about equal size starting at key changes.
fn make_bounds(c: &Cols, nt: usize, Ghost(sv): Ghost<StoresView>) -> (lb: Vec<usize>)
    requires cols_ok(*c, sv), 1 <= nt <= MAX_WORKERS,
    ensures bounds_ok(sv, lb@, nt as int),
{
    let nl = c.nl;
    let chunk = nl / nt;
    let mut lb: Vec<usize> = Vec::new();
    lb.push(0);
    let mut t: usize = 1;
    while t < nt
        invariant
            cols_ok(*c, sv), nl == c.nl, chunk == nl / nt, 1 <= nt <= MAX_WORKERS, 1 <= t <= nt, lb@.len() == t, lb@[0] == 0,
            forall|u: int| 0 <= u < t - 1 ==> lb@[u] <= #[trigger] lb@[u + 1],
            forall|u: int| 0 <= u < t ==> #[trigger] lb@[u] <= nl,
            forall|u: int| 0 <= u < t ==> (lb@[u] == 0 || lb@[u] == nl || lk(sv)[lb@[u] - 1] != lk(sv)[#[trigger] lb@[u] as int]),
        decreases nt - t,
    {
        let prev = lb[t - 1];
        let mut b: usize = if chunk <= nl / t {
            proof {
                assert(t * chunk <= t * (nl / t)) by (nonlinear_arith) requires 1 <= t, chunk <= nl / t;
                assert(t * (nl / t) <= nl) by (nonlinear_arith) requires 1 <= t;
            }
            t * chunk
        } else {
            nl
        };
        if b < prev {
            b = prev;
        }
        while b > 0 && b < nl && c.lk[b] == c.lk[b - 1]
            invariant cols_ok(*c, sv), nl == c.nl, prev <= b <= nl,
            decreases nl - b,
        {
            b = b + 1;
        }
        let ghost lb0 = lb@;
        lb.push(b);
        proof {
            assert forall|u: int| 0 <= u < t implies lb@[u] <= #[trigger] lb@[u + 1] by {
                if u < t - 1 { assert(lb@[u] == lb0[u] && lb@[u + 1] == lb0[u + 1]); }
            }
            assert forall|u: int| 0 <= u < t + 1 implies (lb@[u] == 0 || lb@[u] == nl || lk(sv)[lb@[u] - 1] != lk(sv)[#[trigger] lb@[u] as int]) by {
                if u < t { assert(lb@[u] == lb0[u]); }
            }
        }
        t = t + 1;
    }
    let ghost lb0 = lb@;
    lb.push(nl);
    proof {
        assert forall|u: int| 0 <= u < nt implies lb@[u] <= #[trigger] lb@[u + 1] by {
            if u < nt - 1 { assert(lb@[u] == lb0[u] && lb@[u + 1] == lb0[u + 1]); }
        }
        assert forall|u: int| 0 <= u <= nt implies (lb@[u] == 0 || lb@[u] == nl || lk(sv)[lb@[u] - 1] != lk(sv)[#[trigger] lb@[u] as int]) by {
            if u < nt { assert(lb@[u] == lb0[u]); }
        }
    }
    lb
}

/// The task facts the merge needs, per range `t`.
pub open spec fn task_ok(tk: ScanTask, c: Cols, m: SupMap, sv: StoresView, lb: Seq<usize>, t: int) -> bool {
    &&& tk.c == c
    &&& *tk.m == m
    &&& tk.lo == lb[t]
    &&& tk.hi == lb[t + 1]
    &&& tk.sv@ == sv
    &&& tk.pre()
}

/// One task per range.
fn make_tasks(c: &Cols, m: &Arc<SupMap>, lb: &Vec<usize>, nt: usize, Ghost(sv): Ghost<StoresView>) -> (tasks: Vec<ScanTask>)
    requires cols_ok(*c, sv), sup_ok(**m, sv), bounds_ok(sv, lb@, nt as int), 1 <= nt <= MAX_WORKERS,
    ensures tasks@.len() == nt, forall|t: int| 0 <= t < nt ==> task_ok(#[trigger] tasks@[t], *c, **m, sv, lb@, t),
{
    let mut tasks: Vec<ScanTask> = Vec::new();
    let mut t: usize = 0;
    while t < nt
        invariant
            cols_ok(*c, sv), sup_ok(**m, sv), bounds_ok(sv, lb@, nt as int), 1 <= nt <= MAX_WORKERS, t <= nt, tasks@.len() == t,
            forall|u: int| 0 <= u < t ==> task_ok(#[trigger] tasks@[u], *c, **m, sv, lb@, u),
        decreases nt - t,
    {
        let lo = lb[t];
        let hi = lb[t + 1];
        let cnt = zeros_u64(m.nsel);
        let task = ScanTask { c: *c, m: m.clone(), lo, hi, cur: 0, cnt, sv: Ghost(sv) };
        proof {
            assert(lb@[t as int] <= lb@[t + 1]);
            assert(scan_pre(*c, **m, lo as int, hi as int, sv));
        }
        let ghost tk0 = tasks@;
        tasks.push(task);
        proof {
            assert forall|u: int| 0 <= u < t + 1 implies task_ok(#[trigger] tasks@[u], *c, **m, sv, lb@, u) by {
                if u < t { assert(tasks@[u] == tk0[u]); }
            }
        }
        t = t + 1;
    }
    tasks
}

/// The most scan tasks of one call (see `supplier_counts`).
pub const SCAN_TASKS: usize = 24;

/// The counts of every selected supplier over all lineitem rows.
pub fn supplier_counts(c: &Cols, marc: &Arc<SupMap>, workers: usize, dispatch: &mut Dispatch, Ghost(sv): Ghost<StoresView>)
    -> (r: Result<Vec<u64>, WorkerFailure>)
    requires cols_ok(*c, sv), sup_ok(**marc, sv), 1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(tot) ==> tot@.len() == marc.nsel
            && forall|ci: int| 0 <= ci < marc.nsel ==> #[trigger] tot@[ci] as int == ksum(sv, ckey(**marc, ci), 0, n_l(sv)),
{
    let mr: &SupMap = &**marc;
    let nl = c.nl;
    // at most 24 ranges: the scan is bound by memory (the `l_suppkey` reads); measured at 64 workers, 24 tasks take
    // about 245 ms where 48 or 64 take 305-312 ms, and 16 tasks are no faster than 24
    let nt: usize = if nl < 1048576 { 1 } else if workers > SCAN_TASKS { SCAN_TASKS } else { workers };
    if nt == 1 {
        let mut cnt = zeros_u64(mr.nsel);
        let ok = scan_range(c, mr, 0, nl, &mut cnt, 0, Ghost(sv));
        if ok {
            return Ok(cnt);
        }
        return Ok(naive_counts(c, mr, Ghost(sv)));
    }
    let lb = make_bounds(c, nt, Ghost(sv));
    let tasks = make_tasks(c, marc, &lb, nt, Ghost(sv));
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(v) => v,
        Err(e) => return Err(e),
    };
    // every task in order and every boundary pair ordered: the keys are sorted
    let mut all_ok = true;
    let mut t: usize = 0;
    while t < nt
        invariant
            cols_ok(*c, sv), sup_ok(*mr, sv), bounds_ok(sv, lb@, nt as int), outs@.len() == nt, tv.len() == nt,
            forall|u: int| 0 <= u < nt ==> task_ok(#[trigger] tv[u], *c, *mr, sv, lb@, u),
            forall|u: int| 0 <= u < nt ==> #[trigger] tv[u].post(outs@[u]),
            t <= nt, nl == c.nl,
            all_ok ==> pairs_ok(sv, 0, lb@[t as int] as int),
            all_ok ==> forall|u: int| 0 <= u < t ==> (#[trigger] outs@[u]).sorted,
        decreases nt - t,
    {
        let lo = lb[t];
        let hi = lb[t + 1];
        proof {
            assert(task_ok(tv[t as int], *c, *mr, sv, lb@, t as int));
            assert(tv[t as int].post(outs@[t as int]));
        }
        let boundary_ok = lo == 0 || lo >= nl || c.lk[lo - 1] <= c.lk[lo];
        if all_ok && outs[t].sorted && boundary_ok {
            proof {
                assert(lb@[t as int] <= lb@[t + 1]);
                if lo < hi {
                    if lo > 0 { assert(pair_ok(sv, lo as int)); }
                    lemma_pairs_join(sv, 0, lo as int, hi as int);
                }
            }
        } else {
            all_ok = false;
        }
        t = t + 1;
    }
    if !all_ok {
        return Ok(naive_counts(c, mr, Ghost(sv)));
    }
    proof { assert(sorted(sv)); }
    // add the range counts in range order
    let nsel = mr.nsel;
    let mut tot = zeros_u64(nsel);
    let mut t: usize = 0;
    while t < nt
        invariant
            cols_ok(*c, sv), sup_ok(*mr, sv), nsel == mr.nsel, bounds_ok(sv, lb@, nt as int), outs@.len() == nt, tv.len() == nt,
            forall|u: int| 0 <= u < nt ==> task_ok(#[trigger] tv[u], *c, *mr, sv, lb@, u),
            forall|u: int| 0 <= u < nt ==> #[trigger] tv[u].post(outs@[u]),
            forall|u: int| 0 <= u < nt ==> (#[trigger] outs@[u]).sorted,
            sorted(sv), t <= nt, tot@.len() == nsel,
            forall|ci: int| 0 <= ci < nsel ==> #[trigger] tot@[ci] as int == ksum(sv, ckey(*mr, ci), 0, lb@[t as int] as int),
        decreases nt - t,
    {
        proof {
            assert(task_ok(tv[t as int], *c, *mr, sv, lb@, t as int));
            assert(tv[t as int].post(outs@[t as int]));
            assert(lb@[t as int] <= lb@[t + 1]);
        }
        let cnt_t = &outs[t].cnt;
        let ghost lo = lb@[t as int] as int;
        let ghost hi = lb@[t + 1] as int;
        let mut ci: usize = 0;
        while ci < nsel
            invariant
                cols_ok(*c, sv), sup_ok(*mr, sv), nsel == mr.nsel, cnt_t@.len() == nsel, tot@.len() == nsel,
                0 <= lo <= hi <= n_l(sv), ci <= nsel,
                forall|d: int| 0 <= d < nsel ==> #[trigger] cnt_t@[d] as int == ksum(sv, ckey(*mr, d), lo, hi),
                forall|d: int| 0 <= d < ci ==> #[trigger] tot@[d] as int == ksum(sv, ckey(*mr, d), 0, hi),
                forall|d: int| ci <= d < nsel ==> #[trigger] tot@[d] as int == ksum(sv, ckey(*mr, d), 0, lo),
            decreases nsel - ci,
        {
            proof {
                lemma_ksum_split(sv, ckey(*mr, ci as int), 0, lo, hi);
                lemma_ksum_le(sv, ckey(*mr, ci as int), 0, hi);
            }
            tot[ci] = tot[ci] + cnt_t[ci];
            ci = ci + 1;
        }
        t = t + 1;
    }
    Ok(tot)
}

} // verus!
