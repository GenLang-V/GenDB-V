//! The query's executable phases over the stored columns (`columns::Cols`), each with the model fact it
//! establishes:
//! - `nations_in_region`: which nation rows belong to a region named `$3`;
//! - `scan_parts_suppliers` (parallel): the qualifying part keys (fast `LIKE '%lit'` path) and the region flag of
//!   every supplier, plus whether supplier keys are dense;
//! - `general_part_keys` (serial): the qualifying part keys for any other pattern, with the exact first `LIKE`
//!   error;
//! - `scan_partsupp` (parallel): the hits (`sem_plan::hit`) in increasing row order with their fields.
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::spec::fns::like::like_value;
use crate::exec::value::*;
use crate::exec::fns::like::like_value_exec;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::agent::model::*;
use crate::agent::sem_ast::backslash;
use crate::agent::sem_outer::{like_res, part_ok, lemma_like_res};
use crate::agent::sem_plan::*;
use crate::agent::columns::*;
use crate::agent::scan_part::*;
use crate::agent::scan_partsupp::*;
use crate::agent::topk::text_slice;
use crate::agent::common::slot_buffer::SlotBuffer;
use crate::agent::common::key_set::{KeySet, BLOCK};
use crate::agent::common::like_suffix::{ends_with, suffix_pattern, lemma_like_suffix};

verus! {

// ------------------------------------------------------------------------------------------ small helpers

/// Byte equality of two slices.
pub fn bytes_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures r == (a@ == b@),
{
    let n = a.len();
    if n != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < n
        invariant n == a@.len(), n == b@.len(), i <= n, forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases n - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i = i + 1;
    }
    assert(a@ =~= b@);
    true
}

/// A copy of a byte slice.
pub fn to_vec(s: &[u8]) -> (v: Vec<u8>)
    ensures v@ == s@,
{
    let n = s.len();
    let mut v: Vec<u8> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant n == s@.len(), i <= n, v@ == s@.subrange(0, i as int),
        decreases n - i,
    {
        v.push(s[i]);
        i = i + 1;
        assert(v@ =~= s@.subrange(0, i as int));
    }
    assert(s@.subrange(0, n as int) =~= s@);
    v
}

// ------------------------------------------------------------------------------------------ nations of the region

/// Nation row `d` belongs to a region row named `rp`.
pub open spec fn nat_in_reg(sv: StoresView, rp: Seq<u8>, d: int) -> bool {
    exists|e: int| 0 <= e < reg_n(sv) && #[trigger] r_keys(sv)[e] == n_rks(sv)[d] && r_name(sv, e) == rp
}

/// For every nation row whether it belongs to a region named `rp`.
pub fn nations_in_region(c: &Cols, rp: &[u8], Ghost(sv): Ghost<StoresView>) -> (ok: Vec<bool>)
    requires cols_ok(*c, sv),
    ensures ok@.len() == nat_n(sv), forall|d: int| 0 <= d < nat_n(sv) ==> #[trigger] ok@[d] == nat_in_reg(sv, rp@, d),
{
    let mut ok: Vec<bool> = Vec::new();
    let mut d: usize = 0;
    while d < c.nn
        invariant
            cols_ok(*c, sv),
            d <= c.nn,
            ok@.len() == d,
            forall|x: int| 0 <= x < d ==> #[trigger] ok@[x] == nat_in_reg(sv, rp@, x),
        decreases c.nn - d,
    {
        let mut found = false;
        let mut e: usize = 0;
        while e < c.nr
            invariant
                cols_ok(*c, sv),
                d < c.nn,
                e <= c.nr,
                found == exists|x: int| 0 <= x < e && #[trigger] r_keys(sv)[x] == n_rks(sv)[d as int] && r_name(sv, x) == rp@,
            decreases c.nr - e,
        {
            let name = text_slice(c.r_name.off, c.r_name.bytes, c.r_name.n, c.r_name.blen, e);
            assert(name@ == r_name(sv, e as int));
            if c.r_keys[e] == c.n_rks[d] && bytes_eq(name, rp) {
                found = true;
            }
            e = e + 1;
        }
        ok.push(found);
        d = d + 1;
    }
    ok
}

/// The scans' supplier flags (`scan_part::supp_in_region` over the nation flags) are the model's region test.
pub proof fn lemma_supp_flags(sv: StoresView, rp: Seq<u8>, nat_ok: Seq<bool>, b: int)
    requires
        nat_ok.len() == nat_n(sv),
        forall|d: int| 0 <= d < nat_n(sv) ==> #[trigger] nat_ok[d] == nat_in_reg(sv, rp, d),
    ensures supp_in_region(s_nks(sv), n_keys(sv), nat_ok, b) == supp_in_reg(sv, rp, b),
{
    if supp_in_region(s_nks(sv), n_keys(sv), nat_ok, b) {
        let d = choose|d: int| 0 <= d < n_keys(sv).len() && n_keys(sv)[d] == s_nks(sv)[b] && #[trigger] nat_ok[d];
        assert(nat_in_reg(sv, rp, d));
        let e = choose|e: int| 0 <= e < reg_n(sv) && #[trigger] r_keys(sv)[e] == n_rks(sv)[d] && r_name(sv, e) == rp;
        assert(supp_in_reg(sv, rp, b));
    }
    if supp_in_reg(sv, rp, b) {
        let (d, e) = choose|d: int, e: int| 0 <= d < nat_n(sv) && 0 <= e < reg_n(sv)
            && #[trigger] n_keys(sv)[d] == s_nks(sv)[b] && n_rks(sv)[d] == #[trigger] r_keys(sv)[e] && r_name(sv, e) == rp;
        assert(nat_in_reg(sv, rp, d));
        assert(nat_ok[d]);
    }
}

// ------------------------------------------------------------------------------------------ qualifying part keys

/// `ks` holds exactly the keys of the qualifying parts.
pub open spec fn qkeys_ok(sv: StoresView, v: int, pat: Seq<u8>, ks: Seq<i64>) -> bool {
    forall|k: i64| (exists|j: int| 0 <= j < ks.len() && #[trigger] ks[j] == k) <==> qual_key(sv, v, pat, k as int)
}

/// `k` is the key of a qualifying part row below `end`.
pub open spec fn key_from_part(sv: StoresView, v: int, pat: Seq<u8>, k: i64, end: int) -> bool {
    exists|x: int| 0 <= x < end && #[trigger] p_keys(sv)[x] == k && part_ok(sv, v, pat, x)
}

/// `k` occurs in `ks`.
pub open spec fn in_keys(ks: Seq<i64>, k: i64) -> bool {
    exists|j: int| 0 <= j < ks.len() && ks[j] == k
}

/// No part row's `LIKE` fails.
pub open spec fn like_ok_all(sv: StoresView, pat: Seq<u8>) -> bool {
    forall|a: int| 0 <= a < part_n(sv) ==> #[trigger] like_res(p_type(sv, a), pat) is Ok
}

/// The keys of the qualifying parts, or the first part row whose `LIKE` fails (any pattern; one `LIKE` evaluation
/// per part row on the calling thread).
pub fn general_part_keys(c: &Cols, v: i64, pat: &[u8], Ghost(sv): Ghost<StoresView>) -> (r: Result<Vec<i64>, (usize, SqlError)>)
    requires cols_ok(*c, sv),
    ensures
        r matches Ok(ks) ==> like_ok_all(sv, pat@) && qkeys_ok(sv, v as int, pat@, ks@),
        r matches Err((a0, e)) ==> a0 < part_n(sv) && like_res(p_type(sv, a0 as int), pat@) == Err::<Val, SqlError>(e)
            && forall|a: int| 0 <= a < a0 ==> #[trigger] like_res(p_type(sv, a), pat@) is Ok,
{
    let pv = EVal::Text(to_vec(pat));
    let mut esc: Vec<u8> = Vec::new();
    esc.push(92u8);
    assert(esc@ =~= backslash());
    let ev = EVal::Text(esc);
    let mut ks: Vec<i64> = Vec::new();
    let mut a: usize = 0;
    while a < c.np
        invariant
            cols_ok(*c, sv),
            a <= c.np,
            pv@ == Val::Text(pat@),
            ev@ == Val::Text(backslash()),
            forall|x: int| 0 <= x < a ==> #[trigger] like_res(p_type(sv, x), pat@) is Ok,
            forall|j: int| 0 <= j < ks@.len() ==> key_from_part(sv, v as int, pat@, #[trigger] ks@[j], a as int),
            forall|x: int| 0 <= x < a && #[trigger] part_ok(sv, v as int, pat@, x) ==> in_keys(ks@, p_keys(sv)[x]),
        decreases c.np - a,
    {
        let t = text_slice(c.p_type.off, c.p_type.bytes, c.p_type.n, c.p_type.blen, a);
        assert(t@ == p_type(sv, a as int));
        let sv_t = EVal::Text(to_vec(t));
        let lr = like_value_exec(&sv_t, &pv, &ev);
        proof { lemma_like_res(p_type(sv, a as int), pat@); }
        match lr {
            Err(e) => {
                return Err((a, e));
            },
            Ok(val) => {
                let hit = match val { EVal::Bool(bv) => bv, _ => false };
                let ghost before = ks@;
                if hit && c.p_sizes[a] == v {
                    ks.push(c.p_keys[a]);
                    proof {
                        assert(part_ok(sv, v as int, pat@, a as int));
                        assert forall|j: int| 0 <= j < ks@.len() implies key_from_part(sv, v as int, pat@, #[trigger] ks@[j], a + 1) by {
                            if j < before.len() {
                                assert(ks@[j] == before[j]);
                                assert(key_from_part(sv, v as int, pat@, before[j], a as int));
                                let x = choose|x: int| 0 <= x < a && #[trigger] p_keys(sv)[x] == before[j] && part_ok(sv, v as int, pat@, x);
                            } else {
                                assert(p_keys(sv)[a as int] == ks@[j]);
                            }
                        }
                        assert forall|x: int| 0 <= x < a + 1 && #[trigger] part_ok(sv, v as int, pat@, x) implies in_keys(ks@, p_keys(sv)[x]) by {
                            if x < a {
                                let j = choose|j: int| 0 <= j < before.len() && before[j] == p_keys(sv)[x];
                                assert(ks@[j] == before[j]);
                            } else {
                                assert(ks@[before.len() as int] == p_keys(sv)[x]);
                            }
                        }
                    }
                } else {
                    proof {
                        assert(!part_ok(sv, v as int, pat@, a as int));
                    }
                }
            },
        }
        a = a + 1;
    }
    proof {
        assert forall|k: i64| (exists|j: int| 0 <= j < ks@.len() && #[trigger] ks@[j] == k) <==> qual_key(sv, v as int, pat@, k as int) by {
            if exists|j: int| 0 <= j < ks@.len() && #[trigger] ks@[j] == k {
                let j = choose|j: int| 0 <= j < ks@.len() && #[trigger] ks@[j] == k;
                assert(key_from_part(sv, v as int, pat@, ks@[j], c.np as int));
                let x = choose|x: int| 0 <= x < c.np && #[trigger] p_keys(sv)[x] == ks@[j] && part_ok(sv, v as int, pat@, x);
            }
            if qual_key(sv, v as int, pat@, k as int) {
                let x = choose|x: int| 0 <= x < part_n(sv) && #[trigger] p_keys(sv)[x] == k as int && part_ok(sv, v as int, pat@, x);
                assert(in_keys(ks@, p_keys(sv)[x]));
                let j = choose|j: int| 0 <= j < ks@.len() && ks@[j] == p_keys(sv)[x];
            }
        }
    }
    Ok(ks)
}

// ------------------------------------------------------------------------------------------ phase 1 (parallel)

/// The part scan over all part rows with the scans' parameters (`lo = 0`).
pub open spec fn global_part_scan(c: Cols, v: i64, suffix: &'static [u8]) -> PartScan {
    PartScan { sizes: c.p_sizes, keys: c.p_keys, toff: c.p_type.off, tbytes: c.p_type.bytes, tlen: c.p_type.blen, n: c.np,
        lo: 0, hi: c.np, target: v, suffix, slen: suffix@.len() as usize }
}

/// The part scan's condition is the model's part condition on the fast path.
pub proof fn lemma_part_hit_fast(c: Cols, sv: StoresView, v: i64, pat: Seq<u8>, suffix: &'static [u8], a: int)
    requires cols_ok(c, sv), suffix_pattern(pat), suffix@ == pat.subrange(1, pat.len() as int), 0 <= a < c.np,
    ensures
        global_part_scan(c, v, suffix).hit(a) == part_ok(sv, v as int, pat, a),
        like_res(p_type(sv, a), pat) is Ok,
{
    assert(text_row(c.p_type.off@, c.p_type.bytes@, a) == p_type(sv, a));
    lemma_like_suffix(p_type(sv, a), pat);
    assert(backslash() == seq![92u8]);
}

/// Result of phase 1: the qualifying part keys (fast path), the region flag of every supplier and whether supplier
/// keys are `s_keys[0] + b`.
pub struct Phase1 {
    pub qkeys: Vec<i64>,
    pub flags: Vec<bool>,
    pub dense: bool,
    pub nflag: usize,
}

pub open spec fn phase1_ok(c: Cols, sv: StoresView, v: i64, pat: Seq<u8>, rp: Seq<u8>, fast: bool, p: Phase1) -> bool {
    &&& p.flags@.len() == supp_n(sv)
    &&& forall|b: int| 0 <= b < supp_n(sv) ==> #[trigger] p.flags@[b] == supp_in_reg(sv, rp, b)
    &&& p.dense ==> forall|b: int| 0 <= b < supp_n(sv) ==> #[trigger] s_keys(sv)[b] == s_keys(sv)[0] + b
    &&& fast ==> qkeys_ok(sv, v as int, pat, p.qkeys@) && like_ok_all(sv, pat)
}

/// The part lane of the global part scan `g` over rows `r` with fresh buffers.
pub open spec fn part_lane_of(g: PartScan, l: PartLane, r: (usize, usize)) -> bool {
    l.pre() && l.scan == (PartScan { lo: r.0, hi: r.1, ..g })
}

/// Phase 1 tasks: task `i` holds part lanes `4i .. 4i + 3` of the chained part ranges `pr` and supplier range `sr[i]`.
pub open spec fn tasks1_ok(c: Cols, v: i64, suffix: &'static [u8], nat_arc: Arc<Vec<bool>>, sbase: i64, tasks: Seq<ScanTask1>,
    pr: Seq<(usize, usize)>, sr: Seq<(usize, usize)>) -> bool
{
    let g = global_part_scan(c, v, suffix);
    &&& pr.len() == 4 * tasks.len() && sr.len() == tasks.len()
    &&& forall|i: int| 0 <= i < tasks.len() ==> {
        let t = #[trigger] tasks[i];
        &&& t.pre()
        &&& part_lane_of(g, t.p0, pr[4 * i]) && part_lane_of(g, t.p1, pr[4 * i + 1])
        &&& part_lane_of(g, t.p2, pr[4 * i + 2]) && part_lane_of(g, t.p3, pr[4 * i + 3])
        &&& t.supp == (SuppScan { skeys: c.s_keys, snk: c.s_nks, ns: c.ns, slo: sr[i].0, shi: sr[i].1, base: sbase,
                nat_keys: c.n_keys, nn: c.nn, nat_ok: nat_arc })
    }
    &&& forall|j: int| 0 < j < pr.len() ==> #[trigger] pr[j].0 == pr[j - 1].1
    &&& forall|i: int| 0 < i < sr.len() ==> #[trigger] sr[i].0 == sr[i - 1].1
}

/// A fresh part lane over `[lo, hi)`.
fn make_part_lane(c: &Cols, Ghost(sv): Ghost<StoresView>, v: i64, suffix: &'static [u8], slen: usize, lo: usize, hi: usize) -> (l: PartLane)
    requires
        cols_ok(*c, sv),
        lo <= hi <= c.np,
        slen == suffix@.len(),
    ensures part_lane_of(global_part_scan(*c, v, suffix), l, (lo, hi)),
{
    let scan = PartScan { sizes: c.p_sizes, keys: c.p_keys, toff: c.p_type.off, tbytes: c.p_type.bytes, tlen: c.p_type.blen,
        n: c.np, lo, hi, target: v, suffix, slen };
    let batch = if hi > lo { vec![0usize; BATCH] } else { Vec::new() };
    PartLane { scan, out: SlotBuffer::new((hi - lo) / 128 + 64, 0i64), batch }
}

/// Append the keys of part lane `[lo, hi)` (rescanned with room for every row when incomplete) to `qkeys`.
fn append_part_lane(c: &Cols, v: i64, suffix: &'static [u8], slen: usize, lo: usize, hi: usize, o: PartLaneOut,
    qkeys: &mut Vec<i64>, Ghost(l): Ghost<PartLane>)
    requires
        slen == suffix@.len(),
        part_lane_of(global_part_scan(*c, v, suffix), l, (lo, hi)),
        part_lane_post(l, o),
        global_part_scan(*c, v, suffix).covers(lo as int, old(qkeys)@),
    ensures global_part_scan(*c, v, suffix).covers(hi as int, final(qkeys)@),
{
    let ghost g = global_part_scan(*c, v, suffix);
    let mut keys = if o.complete {
        o.keys.into_vec()
    } else {
        let ps = PartScan { sizes: c.p_sizes, keys: c.p_keys, toff: c.p_type.off, tbytes: c.p_type.bytes, tlen: c.p_type.blen,
            n: c.np, lo, hi, target: v, suffix, slen };
        assert(ps == l.scan);
        let (buf, done) = ps.run_scan(SlotBuffer::new(hi - lo, 0i64));
        assert(done);
        buf.into_vec()
    };
    proof {
        assert(l.scan.covers(hi as int, keys@));
        lemma_covers_concat(g, l.scan, lo as int, hi as int, qkeys@, keys@);
    }
    qkeys.append(&mut keys);
}

/// Scan the parts (fast path only) and the suppliers in parallel.
pub fn phase1(c: &Cols, Ghost(sv): Ghost<StoresView>, fast: bool, suffix: &'static [u8], v: i64, Ghost(pat): Ghost<Seq<u8>>,
    nat_ok: Vec<bool>, Ghost(rp): Ghost<Seq<u8>>, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<Phase1, WorkerFailure>)
    requires
        cols_ok(*c, sv),
        keys_unique(n_keys(sv)),
        1 <= workers <= MAX_WORKERS,
        c.np >= 1, c.ns >= 1,
        nat_ok@.len() == nat_n(sv),
        forall|d: int| 0 <= d < nat_n(sv) ==> #[trigger] nat_ok@[d] == nat_in_reg(sv, rp, d),
        fast ==> suffix_pattern(pat) && suffix@ == pat.subrange(1, pat.len() as int),
    ensures r matches Ok(p) ==> phase1_ok(*c, sv, v, pat, rp, fast, p),
{
    let nt = workers;
    let np_fast = if fast { c.np } else { 0 };
    let nl = 4 * nt;
    let pchunk = if np_fast / nl == 0 { 1 } else { np_fast / nl };
    let tchunk = if np_fast / nt == 0 { 1 } else { np_fast / nt };
    let schunk = if c.ns / nt == 0 { 1 } else { c.ns / nt };
    let nat_arc = Arc::new(nat_ok);
    let sbase = c.s_keys[0];
    let slen = suffix.len();
    let ghost g = global_part_scan(*c, v, suffix);
    let mut tasks: Vec<ScanTask1> = Vec::new();
    let mut pr: Vec<(usize, usize)> = Vec::new();
    let mut sr: Vec<(usize, usize)> = Vec::new();
    let mut plo: usize = 0;
    let mut slo: usize = 0;
    let mut t: usize = 0;
    while t < nt
        invariant
            cols_ok(*c, sv),
            nt == workers, 1 <= nt <= MAX_WORKERS,
            t <= nt,
            slen == suffix@.len(),
            np_fast == (if fast { c.np } else { 0 }),
            plo <= np_fast, slo <= c.ns,
            tasks@.len() == t,
            (*nat_arc)@ == nat_ok@,
            nat_ok@.len() == nat_n(sv),
            g == global_part_scan(*c, v, suffix),
            tasks1_ok(*c, v, suffix, nat_arc, sbase, tasks@, pr@, sr@),
            t == 0 ==> plo == 0 && slo == 0,
            t > 0 ==> pr@[4 * t - 1].1 == plo && sr@[t - 1].1 == slo,
            t > 0 ==> pr@[0].0 == 0 && sr@[0].0 == 0,
            t == nt && t > 0 ==> plo == np_fast && slo == c.ns,
            keys_unique(n_keys(sv)),
        decreases nt - t,
    {
        let last = t + 1 == nt;
        // Four lanes per task keep four memory streams in flight on one thread; with many tasks the scan is bound
        // by the memory bandwidth instead, so lane 0 takes the whole task range.
        let (h0, h1, h2, h3) = if nt < LANE_TASKS {
            let h0 = next_hi(plo, np_fast, pchunk, false);
            let h1 = next_hi(h0, np_fast, pchunk, false);
            let h2 = next_hi(h1, np_fast, pchunk, false);
            (h0, h1, h2, next_hi(h2, np_fast, pchunk, last))
        } else {
            let h0 = next_hi(plo, np_fast, tchunk, last);
            (h0, h0, h0, h0)
        };
        let shi = next_hi(slo, c.ns, schunk, last);
        let p0 = make_part_lane(c, Ghost(sv), v, suffix, slen, plo, h0);
        let p1 = make_part_lane(c, Ghost(sv), v, suffix, slen, h0, h1);
        let p2 = make_part_lane(c, Ghost(sv), v, suffix, slen, h1, h2);
        let p3 = make_part_lane(c, Ghost(sv), v, suffix, slen, h2, h3);
        let nat_c = nat_arc.clone();
        assert(nat_c == nat_arc);
        let supp = SuppScan { skeys: c.s_keys, snk: c.s_nks, ns: c.ns, slo, shi, base: sbase, nat_keys: c.n_keys, nn: c.nn,
            nat_ok: nat_c };
        let task = ScanTask1 { p0, p1, p2, p3, pass: PartPass::new(), supp, flags: vec![false; shi - slo] };
        let ghost before = tasks@;
        let ghost pr0 = pr@;
        let ghost sr0 = sr@;
        tasks.push(task);
        pr.push((plo, h0));
        pr.push((h0, h1));
        pr.push((h1, h2));
        pr.push((h2, h3));
        sr.push((slo, shi));
        proof {
            assert(task.supp.wf());
            assert(task.pre());
            assert forall|i: int| 0 <= i < tasks@.len() implies {
                let tk = #[trigger] tasks@[i];
                &&& tk.pre()
                &&& part_lane_of(g, tk.p0, pr@[4 * i]) && part_lane_of(g, tk.p1, pr@[4 * i + 1])
                &&& part_lane_of(g, tk.p2, pr@[4 * i + 2]) && part_lane_of(g, tk.p3, pr@[4 * i + 3])
                &&& tk.supp == (SuppScan { skeys: c.s_keys, snk: c.s_nks, ns: c.ns, slo: sr@[i].0, shi: sr@[i].1, base: sbase,
                    nat_keys: c.n_keys, nn: c.nn, nat_ok: nat_arc })
            } by {
                if i < t {
                    assert(tasks@[i] == before[i] && sr@[i] == sr0[i]);
                    assert(pr@[4 * i] == pr0[4 * i] && pr@[4 * i + 1] == pr0[4 * i + 1]);
                    assert(pr@[4 * i + 2] == pr0[4 * i + 2] && pr@[4 * i + 3] == pr0[4 * i + 3]);
                }
            }
            assert forall|j: int| 0 < j < pr@.len() implies #[trigger] pr@[j].0 == pr@[j - 1].1 by {
                if j < 4 * t { assert(pr@[j] == pr0[j] && pr@[j - 1] == pr0[j - 1]); }
            }
            assert forall|i: int| 0 < i < sr@.len() implies #[trigger] sr@[i].0 == sr@[i - 1].1 by {
                if i < t { assert(sr@[i] == sr0[i] && sr@[i - 1] == sr0[i - 1]); }
            }
        }
        plo = h3;
        slo = shi;
        t = t + 1;
    }
    let ghost tg = tasks@;
    let ghost mut tg_rest = tasks@;
    // A single task runs on the calling thread: no spawn, and the caller stays busy.
    let outs = if nt == 1 {
        let mut tasks = tasks;
        let only = tasks.pop().unwrap();
        assert(only == tg[0]);
        let o = only.run();
        let mut outs: Vec<ScanOut1> = Vec::new();
        outs.push(o);
        outs
    } else {
        match fork_join(dispatch, tasks) {
            Ok(o) => o,
            Err(e) => return Err(e),
        }
    };
    // Merge in task order.
    let mut outs = outs;
    let mut qkeys: Vec<i64> = Vec::with_capacity(np_fast / 128);
    let mut flags: Vec<bool> = Vec::with_capacity(c.ns);
    let mut dense = true;
    let mut nflag: usize = 0;
    let mut i: usize = 0;
    proof {
        assert(g.covers(0, Seq::<i64>::empty()));
    }
    while i < nt
        invariant
            cols_ok(*c, sv),
            nt == tg.len(), i <= nt, 1 <= nt,
            outs@.len() == nt - i,
            tg_rest == tg.subrange(i as int, nt as int),
            forall|j: int| 0 <= j < outs@.len() ==> #[trigger] tg_rest[j].post(outs@[j]),
            tasks1_ok(*c, v, suffix, nat_arc, sbase, tg, pr@, sr@),
            (*nat_arc)@ == nat_ok@,
            pr@[0].0 == 0 && sr@[0].0 == 0,
            pr@[4 * nt - 1].1 == np_fast && sr@[nt - 1].1 == c.ns,
            np_fast == (if fast { c.np } else { 0 }),
            g == global_part_scan(*c, v, suffix),
            slen == suffix@.len(),
            g.covers(if i == 0 { 0 } else { pr@[4 * i - 1].1 as int }, qkeys@),
            flags@.len() == (if i == 0 { 0 } else { sr@[i - 1].1 as int }),
            flags@.len() <= c.ns,
            nflag <= flags@.len(),
            forall|b: int| 0 <= b < flags@.len() ==> #[trigger] flags@[b] == supp_in_region(c.s_nks@, c.n_keys@, nat_ok@, b),
            dense ==> forall|b: int| 0 <= b < flags@.len() ==> #[trigger] c.s_keys@[b] == sbase + b,
            sbase == c.s_keys@[0],
        decreases nt - i,
    {
        let ghost outs0 = outs@;
        let o = outs.remove(0);
        let ghost task = tg[i as int];
        assert(tg_rest[0] == task);
        assert(task.post(o));
        proof {
            assert forall|j: int| 0 <= j < outs@.len() implies #[trigger] tg_rest.drop_first()[j].post(outs@[j]) by {
                assert(outs@[j] == outs0[j + 1]);
                assert(tg_rest.drop_first()[j] == tg_rest[j + 1]);
            }
            tg_rest = tg_rest.drop_first();
            assert(tg_rest =~= tg.subrange(i + 1, nt as int));
            if i > 0 { assert(pr@[4 * i].0 == pr@[4 * i - 1].1); }
            assert(pr@[4 * i + 1].0 == pr@[4 * i].1);
            assert(pr@[4 * i + 2].0 == pr@[4 * i + 1].1);
            assert(pr@[4 * i + 3].0 == pr@[4 * i + 2].1);
        }
        let ScanOut1 { o0, o1, o2, o3, flags: of, dense: od, nflag: onf } = o;
        // Part keys of the lanes.
        let r0 = pr[4 * i];
        let r1 = pr[4 * i + 1];
        let r2 = pr[4 * i + 2];
        let r3 = pr[4 * i + 3];
        append_part_lane(c, v, suffix, slen, r0.0, r0.1, o0, &mut qkeys, Ghost(task.p0));
        append_part_lane(c, v, suffix, slen, r1.0, r1.1, o1, &mut qkeys, Ghost(task.p1));
        append_part_lane(c, v, suffix, slen, r2.0, r2.1, o2, &mut qkeys, Ghost(task.p2));
        append_part_lane(c, v, suffix, slen, r3.0, r3.1, o3, &mut qkeys, Ghost(task.p3));
        // Supplier flags of the range.
        let ghost f0 = flags@;
        let mut f = of;
        let ghost fv = f@;
        proof {
            assert(task.supp.done(f@, od));
            assert(task.supp.slo == f0.len()) by { if i > 0 { assert(sr@[i as int].0 == sr@[i - 1].1); } }
        }
        if !od {
            dense = false;
        }
        nflag = nflag + onf;
        flags.append(&mut f);
        proof {
            let s = task.supp;
            assert forall|b: int| 0 <= b < flags@.len() implies #[trigger] flags@[b] == supp_in_region(c.s_nks@, c.n_keys@, nat_ok@, b) by {
                if b >= f0.len() {
                    assert(flags@[b] == fv[b - f0.len()]);
                    assert(fv[b - s.slo] == supp_in_region(s.snk@, s.nat_keys@, s.nat_ok@, b));
                } else {
                    assert(flags@[b] == f0[b]);
                }
            }
            if dense {
                assert forall|b: int| 0 <= b < flags@.len() implies #[trigger] c.s_keys@[b] == sbase + b by {
                    if b >= f0.len() {
                        assert(s.skeys@[b] == s.base + b);
                    } else {
                        assert(f0.len() > b);
                    }
                }
            }
        }
        i = i + 1;
    }
    proof {
        assert forall|b: int| 0 <= b < supp_n(sv) implies #[trigger] flags@[b] == supp_in_reg(sv, rp, b) by {
            lemma_supp_flags(sv, rp, nat_ok@, b);
        }
        if fast {
            assert(g.covers(c.np as int, qkeys@));
            assert forall|a: int| 0 <= a < part_n(sv) implies #[trigger] like_res(p_type(sv, a), pat) is Ok by {
                lemma_part_hit_fast(*c, sv, v, pat, suffix, a);
            }
            assert forall|k: i64| (exists|j: int| 0 <= j < qkeys@.len() && #[trigger] qkeys@[j] == k) <==> qual_key(sv, v as int, pat, k as int) by {
                if exists|j: int| 0 <= j < qkeys@.len() && #[trigger] qkeys@[j] == k {
                    let j = choose|j: int| 0 <= j < qkeys@.len() && #[trigger] qkeys@[j] == k;
                    assert(g.sourced(c.np as int, qkeys@[j]));
                    let x = choose|x: int| g.lo <= x < c.np && #[trigger] g.hit(x) && g.keys@[x] == qkeys@[j];
                    lemma_part_hit_fast(*c, sv, v, pat, suffix, x);
                    assert(p_keys(sv)[x] == k);
                }
                if qual_key(sv, v as int, pat, k as int) {
                    let x = choose|x: int| 0 <= x < part_n(sv) && #[trigger] p_keys(sv)[x] == k as int && part_ok(sv, v as int, pat, x);
                    lemma_part_hit_fast(*c, sv, v, pat, suffix, x);
                    assert(g.hit(x));
                    assert(listed(qkeys@, g.keys@[x]));
                }
            }
        }
    }
    Ok(Phase1 { qkeys, flags, dense, nflag })
}

// ------------------------------------------------------------------------------------------ phase 2 (parallel)

/// The partsupp scan over all partsupp rows (`lo = 0`).
pub open spec fn global_ps_scan(c: Cols, set: Arc<KeySet>, flags: Arc<Vec<bool>>, dense: bool, sbase: i64) -> PsScan {
    PsScan { pkeys: c.ps_pkeys, skeys: c.ps_skeys, costs: c.ps_costs, nps: c.nps, lo: 0, hi: c.nps, set,
        supp_keys: c.s_keys, supp_acct: c.s_accts, ns: c.ns, sbase, dense, flags }
}

/// The hits' fields, one vector per field.
pub struct HitVecs {
    pub c: Vec<usize>,
    pub b: Vec<usize>,
    pub pk: Vec<i64>,
    pub cost: Vec<i128>,
    pub acct: Vec<i128>,
}

pub open spec fn hv_seqs(h: HitVecs) -> HitSeqs {
    HitSeqs { c: h.c@, b: h.b@, pk: h.pk@, cost: h.cost@, acct: h.acct@ }
}

/// The lane of `g` over rows `[lo, hi)` with fresh buffers.
pub open spec fn lane_of(g: PsScan, l: PsLane, r: (usize, usize)) -> bool {
    l.pre() && l.scan == (PsScan { lo: r.0, hi: r.1, ..g })
}

/// Phase 2 tasks: task `i` holds lanes `4i .. 4i + 3` of the chained lane ranges `rg`.
pub open spec fn tasks2_ok(g: PsScan, tasks: Seq<PsScanTask>, rg: Seq<(usize, usize)>) -> bool {
    &&& rg.len() == 4 * tasks.len()
    &&& forall|i: int| 0 <= i < tasks.len() ==> {
        let t = #[trigger] tasks[i];
        &&& t.pre()
        &&& lane_of(g, t.l0, rg[4 * i]) && lane_of(g, t.l1, rg[4 * i + 1])
        &&& lane_of(g, t.l2, rg[4 * i + 2]) && lane_of(g, t.l3, rg[4 * i + 3])
    }
    &&& forall|j: int| 0 < j < rg.len() ==> #[trigger] rg[j].0 == rg[j - 1].1
}

/// Room for the hits of a lane of `rows` partsupp rows when about `per_mega` hits are expected per 2^20 rows:
/// 1.5 times the expectation plus 64 (a guess; a lane that runs out of room is rescanned).
fn lane_capacity(rows: usize, per_mega: u64) -> (c: usize)
    ensures c <= rows,
{
    let pm = if per_mega > 0x10_0000 { 0x10_0000u64 } else { per_mega };
    if rows > 0xFFFF_FFFF {
        return rows;
    }
    assert(rows * pm <= 0xFFFF_FFFF * 0x10_0000) by (nonlinear_arith) requires rows <= 0xFFFF_FFFF, pm <= 0x10_0000;
    let prod: u128 = rows as u128 * pm as u128;
    let e: u128 = prod / 0x10_0000u128;
    assert(e <= rows) by (nonlinear_arith) requires pm <= 0x10_0000, prod == rows * pm, e == prod / 0x10_0000;
    let c = e + e / 2 + 64;
    if c > rows as u128 { rows } else { c as usize }
}

/// Task counts from which each phase-2 task scans one lane only.
pub const LANE_TASKS: usize = 16;

/// The next lane range after `lo`: `chunk` rows, or the rest for the last lane.
fn next_hi(lo: usize, n: usize, chunk: usize, last: bool) -> (hi: usize)
    requires lo <= n,
    ensures lo <= hi <= n, last ==> hi == n,
{
    if last { n } else if n - lo > chunk { lo + chunk } else { n }
}

/// A fresh lane of `g` over `[lo, hi)` with a batch buffer of `bs` rows.
fn make_lane(c: &Cols, set: &Arc<KeySet>, flags: &Arc<Vec<bool>>, dense: bool, sbase: i64, lo: usize, hi: usize, est: u64,
    bs: usize, Ghost(g): Ghost<PsScan>) -> (l: PsLane)
    requires
        lo <= hi <= c.nps,
        g == global_ps_scan(*c, *set, *flags, dense, sbase),
        g.wf(),
    ensures lane_of(g, l, (lo, hi)), batch_ok(l.batch@, l.scan, bs as int),
{
    let set_c = set.clone();
    let flags_c = flags.clone();
    let scan = PsScan { pkeys: c.ps_pkeys, skeys: c.ps_skeys, costs: c.ps_costs, nps: c.nps, lo, hi, set: set_c,
        supp_keys: c.s_keys, supp_acct: c.s_accts, ns: c.ns, sbase, dense, flags: flags_c };
    let batch = if hi > lo { vec![0usize; bs] } else { Vec::new() };
    PsLane { scan, out: Hits::new(lane_capacity(hi - lo, est)), batch }
}

/// Append the hits of lane `[lo, hi)` (rescanned with room for every row when incomplete) to `h`.
fn append_lane(c: &Cols, set: &Arc<KeySet>, flags: &Arc<Vec<bool>>, dense: bool, sbase: i64, lo: usize, hi: usize,
    o: PsLaneOut, h: &mut HitVecs, Ghost(g): Ghost<PsScan>, Ghost(l): Ghost<PsLane>)
    requires
        g == global_ps_scan(*c, *set, *flags, dense, sbase),
        g.wf(),
        lane_of(g, l, (lo, hi)),
        lane_post(l, o),
        g.covers_seqs(lo as int, hv_seqs(*old(h))),
    ensures g.covers_seqs(hi as int, hv_seqs(*final(h))),
{
    let hits = if o.complete {
        o.hits
    } else {
        let scan = PsScan { pkeys: c.ps_pkeys, skeys: c.ps_skeys, costs: c.ps_costs, nps: c.nps, lo, hi,
            set: set.clone(), supp_keys: c.s_keys, supp_acct: c.s_accts, ns: c.ns, sbase, dense, flags: flags.clone() };
        assert(scan == l.scan);
        let (hh, done) = scan.run_scan(Hits::new(hi - lo));
        assert(done);
        hh
    };
    proof {
        assert(l.scan.covers(hi as int, hits));
        lemma_covers_seqs(l.scan, hi as int, hits);
        lemma_ps_concat(g, l.scan, lo as int, hi as int, hv_seqs(*h), hit_seqs(hits));
    }
    let ghost h0 = hv_seqs(*h);
    let Hits { c: hc, b: hb, pk: hk, cost: hco, acct: hac } = hits;
    let mut v1 = hc.into_vec();
    let mut v2 = hb.into_vec();
    let mut v3 = hk.into_vec();
    let mut v4 = hco.into_vec();
    let mut v5 = hac.into_vec();
    h.c.append(&mut v1);
    h.b.append(&mut v2);
    h.pk.append(&mut v3);
    h.cost.append(&mut v4);
    h.acct.append(&mut v5);
    proof {
        assert(hv_seqs(*h) == h0.concat(hit_seqs(hits)));
    }
}

/// Scan the partsupp rows in parallel: every hit with its fields, in row order.
pub fn phase2(c: &Cols, Ghost(sv): Ghost<StoresView>, set: Arc<KeySet>, flags: Arc<Vec<bool>>, dense: bool, est: u64,
    workers: usize, dispatch: &mut Dispatch) -> (r: Result<HitVecs, WorkerFailure>)
    requires
        cols_ok(*c, sv),
        1 <= workers <= MAX_WORKERS,
        c.nps >= 1, c.ns >= 1,
        set.wf(),
        flags@.len() == c.ns,
        keys_unique(s_keys(sv)),
        dense ==> forall|b: int| 0 <= b < c.ns ==> #[trigger] s_keys(sv)[b] == s_keys(sv)[0] + b,
    ensures r matches Ok(h) ==> global_ps_scan(*c, set, flags, dense, s_keys(sv)[0]).covers_seqs(c.nps as int, hv_seqs(h)),
{
    let nt = workers;
    let nl = 4 * nt;
    let chunk = if c.nps / nl == 0 { 1 } else { c.nps / nl };
    let tchunk = if c.nps / nt == 0 { 1 } else { c.nps / nt };
    let sbase = c.s_keys[0];
    // Batch rows: long batches when one task scans everything; short ones keep the per-task buffers small.
    let bs = if nt == 1 { PS_BATCH_SOLO } else { PS_BATCH };
    assert(0 < bs && bs % BLOCK == 0);
    let ghost g = global_ps_scan(*c, set, flags, dense, sbase);
    proof {
        assert(g.wf());
    }
    let mut tasks: Vec<PsScanTask> = Vec::new();
    let mut rg: Vec<(usize, usize)> = Vec::new();
    let mut lo: usize = 0;
    let mut t: usize = 0;
    while t < nt
        invariant
            cols_ok(*c, sv),
            nt == workers, 1 <= nt <= MAX_WORKERS,
            t <= nt,
            lo <= c.nps,
            tasks@.len() == t,
            g == global_ps_scan(*c, set, flags, dense, sbase),
            g.wf(),
            0 < bs, bs % BLOCK == 0,
            tasks2_ok(g, tasks@, rg@),
            t == 0 ==> lo == 0,
            t > 0 ==> rg@[4 * t - 1].1 == lo && rg@[0].0 == 0,
            t == nt && t > 0 ==> lo == c.nps,
        decreases nt - t,
    {
        let last = t + 1 == nt;
        // Four lanes per task keep four memory streams in flight on one thread; with many tasks the scan is bound
        // by the memory bandwidth instead, so lane 0 takes the whole task range.
        let (h0, h1, h2, h3) = if nt < LANE_TASKS {
            let h0 = next_hi(lo, c.nps, chunk, false);
            let h1 = next_hi(h0, c.nps, chunk, false);
            let h2 = next_hi(h1, c.nps, chunk, false);
            (h0, h1, h2, next_hi(h2, c.nps, chunk, last))
        } else {
            let h0 = next_hi(lo, c.nps, tchunk, last);
            (h0, h0, h0, h0)
        };
        let l0 = make_lane(c, &set, &flags, dense, sbase, lo, h0, est, bs, Ghost(g));
        let l1 = make_lane(c, &set, &flags, dense, sbase, h0, h1, est, bs, Ghost(g));
        let l2 = make_lane(c, &set, &flags, dense, sbase, h1, h2, est, bs, Ghost(g));
        let l3 = make_lane(c, &set, &flags, dense, sbase, h2, h3, est, bs, Ghost(g));
        let task = PsScanTask { l0, l1, l2, l3, pass: PassScratch::new(bs) };
        let ghost before = tasks@;
        let ghost rg0 = rg@;
        tasks.push(task);
        rg.push((lo, h0));
        rg.push((h0, h1));
        rg.push((h1, h2));
        rg.push((h2, h3));
        proof {
            assert(task.pre());
            assert forall|i: int| 0 <= i < tasks@.len() implies {
                let tk = #[trigger] tasks@[i];
                &&& tk.pre()
                &&& lane_of(g, tk.l0, rg@[4 * i]) && lane_of(g, tk.l1, rg@[4 * i + 1])
                &&& lane_of(g, tk.l2, rg@[4 * i + 2]) && lane_of(g, tk.l3, rg@[4 * i + 3])
            } by {
                if i < t {
                    assert(tasks@[i] == before[i]);
                    assert(rg@[4 * i] == rg0[4 * i] && rg@[4 * i + 1] == rg0[4 * i + 1]);
                    assert(rg@[4 * i + 2] == rg0[4 * i + 2] && rg@[4 * i + 3] == rg0[4 * i + 3]);
                }
            }
            assert forall|j: int| 0 < j < rg@.len() implies #[trigger] rg@[j].0 == rg@[j - 1].1 by {
                if j < 4 * t { assert(rg@[j] == rg0[j] && rg@[j - 1] == rg0[j - 1]); }
            }
        }
        lo = h3;
        t = t + 1;
    }
    let ghost tg = tasks@;
    // A single task runs on the calling thread: no spawn, and the caller stays busy.
    let outs = if nt == 1 {
        let mut tasks = tasks;
        let only = tasks.pop().unwrap();
        assert(only == tg[0]);
        let o = only.run();
        let mut outs: Vec<PsOut4> = Vec::new();
        outs.push(o);
        outs
    } else {
        match fork_join(dispatch, tasks) {
            Ok(o) => o,
            Err(e) => return Err(e),
        }
    };
    let mut outs = outs;
    // Room for the expected hits of all rows, so the appends below rarely reallocate.
    let cap = lane_capacity(c.nps, est);
    let mut h = HitVecs { c: Vec::with_capacity(cap), b: Vec::with_capacity(cap), pk: Vec::with_capacity(cap),
        cost: Vec::with_capacity(cap), acct: Vec::with_capacity(cap) };
    let mut i: usize = 0;
    proof {
        let hs = hv_seqs(h);
        assert(hs.c =~= Seq::<usize>::empty() && hs.b =~= Seq::<usize>::empty());
        assert(g.covers_seqs(0, hs));
    }
    let ghost mut tg_rest = tg;
    while i < nt
        invariant
            cols_ok(*c, sv),
            nt == tg.len(), i <= nt, 1 <= nt,
            outs@.len() == nt - i,
            tg_rest == tg.subrange(i as int, nt as int),
            forall|j: int| 0 <= j < outs@.len() ==> #[trigger] tg_rest[j].post(outs@[j]),
            g == global_ps_scan(*c, set, flags, dense, sbase),
            g.wf(),
            tasks2_ok(g, tg, rg@),
            rg@[0].0 == 0,
            rg@[4 * nt - 1].1 == c.nps,
            g.covers_seqs(if i == 0 { 0 } else { rg@[4 * i - 1].1 as int }, hv_seqs(h)),
        decreases nt - i,
    {
        let ghost outs0 = outs@;
        let o4 = outs.remove(0);
        let ghost task = tg[i as int];
        assert(tg_rest[0] == task);
        assert(task.post(o4));
        proof {
            assert forall|j: int| 0 <= j < outs@.len() implies #[trigger] tg_rest.drop_first()[j].post(outs@[j]) by {
                assert(outs@[j] == outs0[j + 1]);
                assert(tg_rest.drop_first()[j] == tg_rest[j + 1]);
            }
            tg_rest = tg_rest.drop_first();
            assert(tg_rest =~= tg.subrange(i + 1, nt as int));
            if i > 0 { assert(rg@[4 * i].0 == rg@[4 * i - 1].1); }
            assert(rg@[4 * i + 1].0 == rg@[4 * i].1);
            assert(rg@[4 * i + 2].0 == rg@[4 * i + 1].1);
            assert(rg@[4 * i + 3].0 == rg@[4 * i + 2].1);
        }
        let PsOut4 { o0, o1, o2, o3 } = o4;
        let r0 = rg[4 * i];
        let r1 = rg[4 * i + 1];
        let r2 = rg[4 * i + 2];
        let r3 = rg[4 * i + 3];
        append_lane(c, &set, &flags, dense, sbase, r0.0, r0.1, o0, &mut h, Ghost(g), Ghost(task.l0));
        append_lane(c, &set, &flags, dense, sbase, r1.0, r1.1, o1, &mut h, Ghost(g), Ghost(task.l1));
        append_lane(c, &set, &flags, dense, sbase, r2.0, r2.1, o2, &mut h, Ghost(g), Ghost(task.l2));
        append_lane(c, &set, &flags, dense, sbase, r3.0, r3.1, o3, &mut h, Ghost(g), Ghost(task.l3));
        i = i + 1;
    }
    Ok(h)
}

} // verus!
