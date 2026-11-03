//! One round of the plan: the groups of the brand dictionary indices `[b0, b1)`, the type dictionary indices
//! `[t0, t1)` and every size slot (local group `gid`, at most `2^18` of them).
//!
//! The round's lookup tables (`round_tables`) code the part rows of the window that pass the part conditions. The
//! counts of every local group come from the partitioned plan (`fast::fast_counts`) when it applies, else from the
//! general plan (`general_counts`): the pair tasks (`pair_phase`, waves of at most `workers` tasks over consecutive
//! part ranges, a task whose scratch was too small run again with room for every partsupp row) give every pair of the
//! round and, from the supplier ranges they also scan, the bitmap of the supplier rows the subquery excludes
//! (`excl_of`); the counting tasks (`count_phase`) count each local group's distinct supplier rows that the subquery
//! does not exclude. Either way a count is the size of the group's set `answer::pset`, which is the group's
//! COUNT(DISTINCT ps_suppkey) (`answer::lemma_group_card`); `collect` appends the groups with a pair in
//! (brand, type, size) order.
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::QueryError;
use super::tables::*;
use super::model::*;
use super::kernel::*;
use super::count::*;
use super::sqlq::{Prm, like_true};
use super::answer::*;
use super::output::{Grp, grp_lt, lex_sorted};
use super::split::*;
use super::bind::{keys_unique, fk_supp};
use super::supp::{cc_row, comm_ok, SuppTask, supp_out_ok};
use super::common::marks::{lemma_zero_holds, bit_at, holds, mark_new};
use super::sidx::SIdx;
use super::fast::fast_counts;
use super::prep::part_dense;

verus! {

/// Local groups of one round at most.
pub const ROUND_GROUPS: usize = 0x40000;

// ------------------------------------------------------------------------------------------------ specs

/// The per-entry inputs of every round: which brand entries differ from `$1`, which type entries match `$2`, and
/// the distinct sizes of the IN list in increasing order.
pub open spec fn inputs_ok(c: Cols, m: Prm, bok: Seq<bool>, tlike: Seq<bool>, sizes: Seq<i64>) -> bool {
    &&& bok.len() == c.p.brand_o@.len() - 1
    &&& forall|b: int| 0 <= b < bok.len() ==> #[trigger] bok[b] == (txt(c.p.brand_o@, c.p.brand_y@, b) != m.brand)
    &&& tlike.len() == c.p.type_o@.len() - 1
    &&& forall|e: int| 0 <= e < tlike.len()
        ==> #[trigger] tlike[e] == like_true(Val::Text(txt(c.p.type_o@, c.p.type_y@, e)), m.pat)
    &&& 1 <= sizes.len() <= 8
    &&& forall|a: int, b: int| 0 <= a < b < sizes.len() ==> #[trigger] sizes[a] < #[trigger] sizes[b]
    &&& forall|v: int| #[trigger] listed(sizes, v) <==> m.sizes.contains(v)
}

/// The facts every round reads: the column handles of the tables, unique keys, the foreign key, the dense supplier
/// keys, and the supplier rows the subquery excludes.
pub open spec fn world_ok(c: Cols, t: Tabs, m: Prm, sdense: bool, sfirst: i64) -> bool {
    &&& cols_ok(c, t)
    &&& keys_unique(t)
    &&& fk_supp(t)
    &&& sdense ==> forall|x: int| 0 <= x < c.s.n ==> #[trigger] skey(c.s, x) == sfirst + x
}

/// A round's window: nonempty, inside the dictionaries, at most `ROUND_GROUPS` local groups.
pub open spec fn win_ok(b0: int, b1: int, t0: int, t1: int, nb: int, nt: int, ns: int) -> bool {
    &&& 0 <= b0 < b1 <= nb
    &&& 0 <= t0 < t1 <= nt
    &&& 1 <= ns <= 8
    &&& (b1 - b0) * (t1 - t0) * ns <= 0x40000
}

pub open spec fn rnd(b0: usize, b1: usize, t0: usize, t1: usize, ns: usize) -> Rnd {
    Rnd { b0: b0 as int, b1: b1 as int, t0: t0 as int, t1: t1 as int, ns: ns as int }
}

/// COUNT(DISTINCT ps_suppkey) of the group of brand entry `b`, type entry `tt` and size slot `z`.
pub open spec fn kc(c: Cols, t: Tabs, m: Prm, sizes: Seq<i64>, b: int, tt: int, z: int) -> int {
    kv(t, m, key_bt(c, sizes, b, tt, z)).len() as int
}

/// A collected group: inside the dictionaries and the size list, with its group's count, positive and an int8.
pub open spec fn grp_ok(c: Cols, t: Tabs, m: Prm, sizes: Seq<i64>, e: Grp) -> bool {
    &&& e.b < c.p.brand_o@.len() - 1
    &&& e.t < c.p.type_o@.len() - 1
    &&& e.z < sizes.len()
    &&& e.cnt as int == kc(c, t, m, sizes, e.b as int, e.t as int, e.z as int)
    &&& 0 < e.cnt <= i64::MAX
}

pub open spec fn at(e: Grp, b: int, tt: int, z: int) -> bool {
    e.b == b && e.t == tt && e.z == z
}

// ------------------------------------------------------------------------------------------------ arithmetic

proof fn lemma_win(r: Rnd)
    requires win_ok(r.b0, r.b1, r.t0, r.t1, r.b1, r.t1, r.ns),
    ensures
        (r.t1 - r.t0) * r.ns <= rng(r),
        (r.b1 - r.b0) * ((r.t1 - r.t0) * r.ns) == rng(r),
        rng(r) <= 0x40000,
{
    let (bw, tw) = (r.b1 - r.b0, r.t1 - r.t0);
    assert(tw * r.ns <= bw * tw * r.ns) by (nonlinear_arith) requires bw >= 1, tw >= 1, r.ns >= 1;
    assert(bw * (tw * r.ns) == bw * tw * r.ns) by (nonlinear_arith);
}

/// `a1 * n + z1 < a2 * n + z2` with slots below `n`: `(a1, z1)` precedes `(a2, z2)`.
proof fn lemma_mix_lt(a1: int, z1: int, a2: int, z2: int, n: int)
    requires 0 <= z1 < n, 0 <= z2 < n, a1 * n + z1 < a2 * n + z2,
    ensures a1 < a2 || (a1 == a2 && z1 < z2),
{
    if a1 > a2 {
        assert(a1 * n >= a2 * n + n) by (nonlinear_arith) requires a1 >= a2 + 1, n >= 0;
    }
}

/// A smaller local group is a smaller (brand, type, slot).
pub proof fn lemma_gid_lt(r: Rnd, b1: int, t1: int, z1: int, b2: int, t2: int, z2: int)
    requires in_round(r, b1, t1, z1), in_round(r, b2, t2, z2), gid(r, b1, t1, z1) < gid(r, b2, t2, z2),
    ensures b1 < b2 || (b1 == b2 && (t1 < t2 || (t1 == t2 && z1 < z2))),
{
    let tw = r.t1 - r.t0;
    lemma_mix_lt((b1 - r.b0) * tw + (t1 - r.t0), z1, (b2 - r.b0) * tw + (t2 - r.t0), z2, r.ns);
    if (b1 - r.b0) * tw + (t1 - r.t0) < (b2 - r.b0) * tw + (t2 - r.t0) {
        lemma_mix_lt(b1 - r.b0, t1 - r.t0, b2 - r.b0, t2 - r.t0, tw);
    } else {
        lemma_gid_inj(r, b1, t1, 0, b2, t2, 0);
    }
}

/// Local group `g` of the round is `gid(b0 + bb, t0 + tt, z)` for `z = g % ns`, `tt = (g / ns) % tw` and
/// `bb = (g / ns) / tw`.
pub proof fn lemma_decode(r: Rnd, g: int)
    requires r.ns >= 1, r.t1 > r.t0, r.b1 > r.b0, 0 <= g < rng(r),
    ensures ({
        let tw = r.t1 - r.t0;
        let z = g % r.ns;
        let tt = (g / r.ns) % tw;
        let bb = (g / r.ns) / tw;
        &&& in_round(r, r.b0 + bb, r.t0 + tt, z)
        &&& gid(r, r.b0 + bb, r.t0 + tt, z) == g
    }),
{
    let tw = r.t1 - r.t0;
    let bw = r.b1 - r.b0;
    let z = g % r.ns;
    let bt = g / r.ns;
    let tt = bt % tw;
    let bb = bt / tw;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(g, r.ns);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(g, r.ns);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(g, r.ns);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(bt, tw);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(bt, tw);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(bt, tw);
    assert(g == bt * r.ns + z) by (nonlinear_arith) requires g == r.ns * bt + z;
    assert(bt == bb * tw + tt) by (nonlinear_arith) requires bt == tw * bb + tt;
    assert(bt < bw * tw) by {
        if bt >= bw * tw {
            assert(bt * r.ns >= bw * tw * r.ns) by (nonlinear_arith) requires bt >= bw * tw, r.ns >= 1;
        }
    }
    assert(bb < bw) by {
        if bb >= bw {
            assert(bb * tw >= bw * tw) by (nonlinear_arith) requires bb >= bw, tw >= 1;
        }
    }
}

// ------------------------------------------------------------------------------------------------ tables, env

/// The round's lookup tables.
pub fn round_tables(c: &Cols, bok: &Vec<bool>, tlike: &Vec<bool>, sizes: &Vec<i64>, b0: usize, b1: usize, t0: usize,
    t1: usize, Ghost(m): Ghost<Prm>) -> (q: QualTabs)
    requires
        inputs_ok(*c, m, bok@, tlike@, sizes@),
        win_ok(b0 as int, b1 as int, t0 as int, t1 as int, bok@.len() as int, tlike@.len() as int, sizes@.len() as int),
    ensures
        round_tabs(q, *c, m, rnd(b0, b1, t0, t1, sizes@.len() as usize)),
        q.sizes@ == sizes@,
{
    let nb = bok.len();
    let nt = tlike.len();
    let ns = sizes.len();
    let tw = t1 - t0;
    let ghost r = rnd(b0, b1, t0, t1, ns);
    proof {
        lemma_win(r);
    }
    let per_b = tw * ns;
    let mut bterm: Vec<u32> = Vec::new();
    let mut b: usize = 0;
    while b < nb
        invariant
            inputs_ok(*c, m, bok@, tlike@, sizes@),
            win_ok(b0 as int, b1 as int, t0 as int, t1 as int, nb as int, nt as int, ns as int),
            nb == bok@.len(), ns == sizes@.len(), tw == t1 - t0, per_b == tw * ns, r == rnd(b0, b1, t0, t1, ns),
            b <= nb, bterm@.len() == b,
            forall|x: int| 0 <= x < b ==> #[trigger] bterm@[x] as int == if b0 <= x < b1
                && txt(c.p.brand_o@, c.p.brand_y@, x) != m.brand { (x - b0) * (t1 - t0) * ns } else { NONE32 as int },
        decreases nb - b,
    {
        if b0 <= b && b < b1 && bok[b] {
            proof {
                lemma_gid_bound(r, b as int, t0 as int, 0);
                assert((b - b0) * (tw * ns) == (b - b0) * tw * ns) by (nonlinear_arith);
            }
            bterm.push(((b - b0) * per_b) as u32);
        } else {
            bterm.push(NONE32);
        }
        b = b + 1;
    }
    let mut tterm: Vec<u32> = Vec::new();
    let mut e: usize = 0;
    while e < nt
        invariant
            inputs_ok(*c, m, bok@, tlike@, sizes@),
            win_ok(b0 as int, b1 as int, t0 as int, t1 as int, nb as int, nt as int, ns as int),
            nt == tlike@.len(), ns == sizes@.len(), tw == t1 - t0, r == rnd(b0, b1, t0, t1, ns),
            e <= nt, tterm@.len() == e,
            forall|x: int| 0 <= x < e ==> #[trigger] tterm@[x] as int == if t0 <= x < t1
                && !like_true(Val::Text(txt(c.p.type_o@, c.p.type_y@, x)), m.pat) { (x - t0) * ns } else { NONE32 as int },
        decreases nt - e,
    {
        if t0 <= e && e < t1 && !tlike[e] {
            proof {
                lemma_gid_bound(r, b0 as int, e as int, 0);
            }
            tterm.push(((e - t0) * ns) as u32);
        } else {
            tterm.push(NONE32);
        }
        e = e + 1;
    }
    let mut szs: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < ns
        invariant ns == sizes@.len(), z <= ns, szs@ == sizes@.subrange(0, z as int),
        decreases ns - z,
    {
        szs.push(sizes[z]);
        z = z + 1;
        proof {
            assert(szs@ =~= sizes@.subrange(0, z as int));
        }
    }
    proof {
        assert(szs@ =~= sizes@);
    }
    QualTabs { bterm, tterm, sizes: szs }
}

/// The pair tasks' environment of a round.
fn make_env(c: &Cols, tabs: Arc<QualTabs>, sdense: bool, sfirst: i64, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>,
    Ghost(r): Ghost<Rnd>) -> (e: PairEnv)
    requires
        cols_ok(*c, t), keys_unique(t),
        round_tabs(*tabs, *c, m, r),
        sdense ==> forall|x: int| 0 <= x < c.s.n ==> #[trigger] skey(c.s, x) == sfirst + x,
    ensures env_ok(e, rng(r)), e.c == *c, e.tabs == tabs,
{
    let pn = c.p.n;
    let psn = c.ps.n;
    let ratio = if pn > 0 { psn / pn } else { 0 };
    let jmax = if ratio > 0 { psn / ratio } else { 0 };
    let ps_shift = pow2_shift(c.ps.bs);
    let nb = tabs.bterm.len();
    let nt = tabs.tterm.len();
    let ns = tabs.sizes.len();
    let tr: &QualTabs = &*tabs;
    proof {
        lemma_shape(*c, t);
        lemma_round_shape(*tr, *c, m, r);
        if ratio > 0 {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(psn as int, ratio as int);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(psn as int, ratio as int);
            assert(jmax * ratio <= psn) by (nonlinear_arith)
                requires psn == ratio * jmax + psn % ratio, psn % ratio >= 0;
        }
        assert forall|j1: int, j2: int| 0 <= j1 < c.p.n && 0 <= j2 < c.p.n
            && #[trigger] pkey(c.p, j1) == #[trigger] pkey(c.p, j2) implies j1 == j2 by {
            assert(part_row_ok(c.p, t.p[j1], j1));
            assert(part_row_ok(c.p, t.p[j2], j2));
            assert(t.p[j1][0] == t.p[j2][0]);
        }
        assert forall|r1: int, r2: int| 0 <= r1 < c.s.n && 0 <= r2 < c.s.n
            && #[trigger] skey(c.s, r1) == #[trigger] skey(c.s, r2) implies r1 == r2 by {
            assert(supp_row_ok(c.s, t.s[r1], r1));
            assert(supp_row_ok(c.s, t.s[r2], r2));
            assert(t.s[r1][0] == t.s[r2][0]);
        }
    }
    let (pfirst, pdense) = part_dense(&c.p, Ghost(c.e32@), Ghost(c.e64@));
    // psrun's key runs apply to the guess when their ratio is the guess's and divides the block size.
    let runs0 = c.ps.runs[0];
    let rper = if ratio > 0 && ratio <= 65536 && runs0 == ratio as i64 && 65536 % ratio == 0 { 65536 / ratio } else { 0 };
    proof {
        if rper > 0 {
            let (ri, pi) = (ratio as int, rper as int);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(65536, ri);
            assert(pi * ri == 65536) by (nonlinear_arith)
                requires 65536int == ri * (65536int / ri) + 65536int % ri, 65536int % ri == 0, pi == 65536int / ri;
        }
    }
    PairEnv { c: *c, ratio, jmax, ps_shift, sdense, sfirst, pdense, pfirst, tabs, nb, nt, ns, rper }
}

// ------------------------------------------------------------------------------------------------ pairs

/// Task `k` of the cuts `bnd`.
pub open spec fn task_at<S: SIdx>(e: PairEnv, ng: usize, bnd: Seq<usize>, k: int, tk: PairTask<S>) -> bool {
    &&& tk.pre()
    &&& *tk.env == e
    &&& tk.ng == ng
    &&& tk.lo == bnd[k]
    &&& tk.hi == bnd[k + 1]
}

/// Task `k`'s supplier rows are `[sb[k], sb[k + 1])`, with room for all of them.
pub open spec fn supp_at<S: SIdx>(s: SCols, sb: Seq<usize>, k: int, tk: PairTask<S>) -> bool {
    &&& tk.supp.s == s
    &&& tk.supp.lo == sb[k]
    &&& tk.supp.hi == sb[k + 1]
    &&& tk.supp.cap >= tk.supp.hi - tk.supp.lo
}

/// Output `k` lists exactly the matching supplier rows of `[sb[k], sb[k + 1])`.
pub open spec fn supp_done<S: SIdx>(s: SCols, sb: Seq<usize>, k: int, po: PairOut<S>) -> bool {
    po.supp.done && supp_out_ok(s, sb[k] as int, sb[k + 1] as int, po.supp)
}

/// Output `k` of the cuts `bnd`, when finished, has the pairs of its part rows.
pub open spec fn pair_done<S: SIdx>(e: PairEnv, ng: usize, bnd: Seq<usize>, k: int, po: PairOut<S>) -> bool {
    po.done ==> pairs_out(*e.tabs, e.c, bnd[k] as int, bnd[k + 1] as int, ng as int, po)
}

/// A pair task over part rows `[lo, hi)` with `cap` entries of scratch.
fn new_task<S: SIdx>(env: &Arc<PairEnv>, ng: usize, lo: usize, hi: usize, cap: usize, supp: SuppTask) -> (tk: PairTask<S>)
    requires env_ok(**env, ng as int), lo <= hi <= env.c.p.n, ng + 1 < usize::MAX, env.c.s.n as int <= S::lim(), supp.pre(),
    ensures tk.pre(), *tk.env == **env, tk.ng == ng, tk.lo == lo, tk.hi == hi, tk.cap == cap, tk.supp == supp,
{
    PairTask {
        env: env.clone(),
        ng,
        lo,
        hi,
        tmp_g: vec![0u32; cap],
        tmp_s: vec![S::zero(); cap],
        cap,
        btab: [0u32; 256],
        ttab: [0u32; 256],
        stab: [0u32; 256],
        out: vec![S::zero(); cap],
        offs: vec![0usize; ng + 1],
        supp,
    }
}

/// The supplier task of rows `[lo, hi)`, with room for all of them (at least 32 MiB: the allocator then maps fresh
/// zero pages).
pub fn supp_task(s: &SCols, lo: usize, hi: usize) -> (st: SuppTask)
    requires comm_ok(*s), lo <= hi <= s.n,
    ensures st.pre(), st.s == *s, st.lo == lo, st.hi == hi, st.cap >= hi - lo,
{
    let cap = if hi - lo > 0x40_0000 { hi - lo } else { 0x40_0000 };
    SuppTask { s: *s, lo, hi, cap, out: vec![0usize; cap] }
}

/// The bitmap of the supplier rows the subquery excludes, from the pair outputs' supplier lists.
fn excl_of<S: SIdx>(s: &SCols, all: &Vec<PairOut<S>>, sb: &Vec<usize>) -> (r: Vec<u64>)
    requires
        cuts(sb@, s.n as int), sb@.len() == all@.len() + 1,
        forall|k: int| 0 <= k < all@.len() ==> #[trigger] supp_done(*s, sb@, k, all@[k]),
    ensures
        s.n <= 64 * r@.len(),
        forall|j: int| 0 <= j < s.n ==> #[trigger] bit_at(r@, j) == cc_row(*s, j),
{
    let mut excl: Vec<u64> = vec![0u64; s.n / 64 + 1];
    proof {
        lemma_zero_holds(excl@);
        assert(s.n <= 64 * (s.n / 64 + 1)) by (nonlinear_arith)
            requires s.n == 64 * (s.n / 64) + s.n % 64, s.n % 64 < 64;
    }
    let ghost mut set: Set<int> = Set::empty();
    let nout = all.len();
    let mut t: usize = 0;
    while t < nout
        invariant
            nout == all@.len(),
            cuts(sb@, s.n as int), sb@.len() == all@.len() + 1,
            forall|k: int| 0 <= k < all@.len() ==> #[trigger] supp_done(*s, sb@, k, all@[k]),
            t <= nout,
            s.n <= 64 * excl@.len(),
            holds(excl@, set),
            forall|j: int| #[trigger] set.contains(j) ==> 0 <= j < s.n && cc_row(*s, j),
            forall|j: int| 0 <= j < sb@[t as int] && #[trigger] cc_row(*s, j) ==> set.contains(j),
        decreases nout - t,
    {
        let o = &all[t].supp;
        let lo = sb[t];
        let hi = sb[t + 1];
        proof {
            lemma_cuts_mono(sb@, s.n as int, t as int, t + 1);
            lemma_cuts_mono(sb@, s.n as int, t + 1, nout as int);
            assert(supp_done(*s, sb@, t as int, all@[t as int]));
        }
        let mut q: usize = 0;
        while q < o.len
            invariant
                *o == all@[t as int].supp,
                supp_out_ok(*s, lo as int, hi as int, *o),
                lo <= hi <= s.n,
                q <= o.len,
                s.n <= 64 * excl@.len(),
                holds(excl@, set),
                forall|j: int| #[trigger] set.contains(j) ==> 0 <= j < s.n && cc_row(*s, j),
                forall|j: int| 0 <= j < lo && #[trigger] cc_row(*s, j) ==> set.contains(j),
                forall|q2: int| 0 <= q2 < q ==> #[trigger] set.contains(o.rows@[q2] as int),
            decreases o.len - q,
        {
            let j = o.rows[q];
            assert(lo <= o.rows@[q as int] < hi && cc_row(*s, o.rows@[q as int] as int));
            let _ = mark_new(&mut excl, j, Ghost(set));
            proof {
                set = set.insert(j as int);
            }
            q = q + 1;
        }
        proof {
            assert forall|j: int| 0 <= j < hi && #[trigger] cc_row(*s, j) implies set.contains(j) by {
                if j >= lo {
                    let q2 = choose|q2: int| 0 <= q2 < o.len && o.rows@[q2] == j;
                    assert(set.contains(o.rows@[q2] as int));
                }
            }
        }
        t = t + 1;
    }
    proof {
        assert forall|j: int| 0 <= j < s.n implies #[trigger] bit_at(excl@, j) == cc_row(*s, j) by {
            if cc_row(*s, j) {
                assert(set.contains(j));
            }
        }
    }
    excl
}

/// Scratch entries of a pair task over `rows` part rows: twice the expected pairs, at least `2^23` (the allocator
/// then maps fresh zero pages instead of clearing them on the calling thread), at most the partsupp row count.
fn pair_cap(ratio: usize, rows: usize, psn: usize) -> usize {
    let mut want: usize = psn;
    if ratio < 0x10_0000 && (rows as u64) < 0x100_0000_0000u64 {
        proof {
            assert(2 * (ratio as u64 + 1) * (rows as u64) < 0x4000_0000_0000_0000) by (nonlinear_arith)
                requires ratio < 0x10_0000, (rows as u64) < 0x100_0000_0000u64;
        }
        let w: u64 = 2 * (ratio as u64 + 1) * (rows as u64);
        if w < psn as u64 {
            want = w as usize;
        }
    }
    if want < 0x80_0000 {
        want = if psn < 0x80_0000 { psn } else { 0x80_0000 };
    }
    want
}

pub proof fn lemma_cuts_mono(bnd: Seq<usize>, n: int, a: int, b: int)
    requires cuts(bnd, n), 0 <= a <= b < bnd.len(),
    ensures bnd[a] <= bnd[b],
    decreases b - a,
{
    if a < b {
        lemma_cuts_mono(bnd, n, a, b - 1);
    }
}

pub proof fn lemma_find(bnd: Seq<usize>, n: int, j: int, l: int)
    requires cuts(bnd, n), 0 <= l < bnd.len() - 1, bnd[l] <= j < n,
    ensures exists|k: int| l <= k < bnd.len() - 1 && bnd[k] <= j < #[trigger] bnd[k + 1],
    decreases bnd.len() - l,
{
    if j >= bnd[l + 1] {
        lemma_find(bnd, n, j, l + 1);
    } else {
        assert(bnd[l] <= j < bnd[l + 1]);
    }
}

pub open spec fn env_tabs(e: PairEnv) -> QualTabs {
    *e.tabs
}

/// The finished outputs of the cuts of `[0, p.n)` are well formed segments of supplier rows.
proof fn lemma_cover_ok<S: SIdx>(e: PairEnv, ng: usize, bnd: Seq<usize>, all: Seq<PairOut<S>>)
    requires
        cuts(bnd, e.c.p.n as int),
        all.len() == bnd.len() - 1,
        forall|k: int| 0 <= k < all.len() ==> (#[trigger] all[k]).done && pair_done(e, ng, bnd, k, all[k]),
    ensures
        outs_ok(all, ng as int, e.c.s.n as int),
{
    let q = env_tabs(e);
    let c = e.c;
    assert forall|t: int| 0 <= t < all.len() implies {
        &&& (#[trigger] all[t]).offs@.len() == ng + 1
        &&& all[t].offs@[0] == 0
        &&& all[t].offs@[ng as int] <= all[t].out@.len()
        &&& forall|g: int| 0 <= g < ng ==> #[trigger] all[t].offs@[g] <= all[t].offs@[g + 1]
        &&& forall|g: int, x: int| 0 <= g < ng && #[trigger] seg_has(all[t], g, x) ==> 0 <= x < c.s.n
    } by {
        assert(pair_done(e, ng, bnd, t, all[t]));
        assert forall|g: int, x: int| 0 <= g < ng && #[trigger] seg_has(all[t], g, x) implies 0 <= x < c.s.n by {
            assert(pair_in(q, c, bnd[t] as int, bnd[t + 1] as int, g, x));
            let (j, i) = choose|j: int, i: int| bnd[t] <= j < bnd[t + 1] && #[trigger] pair_at(q, c, j, i, g, x);
        }
    }
}

/// One output's pair is a pair of the round.
proof fn lemma_cover_to<S: SIdx>(e: PairEnv, ng: usize, bnd: Seq<usize>, all: Seq<PairOut<S>>, g: int, x: int)
    requires
        cuts(bnd, e.c.p.n as int),
        all.len() == bnd.len() - 1,
        forall|k: int| 0 <= k < all.len() ==> (#[trigger] all[k]).done && pair_done(e, ng, bnd, k, all[k]),
        0 <= g < ng,
        in_some(all, g, x),
    ensures pair_in(env_tabs(e), e.c, 0, e.c.p.n as int, g, x),
{
    let q = env_tabs(e);
    let c = e.c;
    let t = choose|t: int| 0 <= t < all.len() && #[trigger] seg_has(all[t], g, x);
    assert(pair_done(e, ng, bnd, t, all[t]));
    assert(pair_in(q, c, bnd[t] as int, bnd[t + 1] as int, g, x));
    let (j, i) = choose|j: int, i: int| bnd[t] <= j < bnd[t + 1] && #[trigger] pair_at(q, c, j, i, g, x);
    lemma_cuts_mono(bnd, c.p.n as int, t + 1, bnd.len() - 1);
    assert(pair_in(q, c, 0, c.p.n as int, g, x));
}

/// A pair of the round is in some output.
proof fn lemma_cover_from<S: SIdx>(e: PairEnv, ng: usize, bnd: Seq<usize>, all: Seq<PairOut<S>>, g: int, x: int)
    requires
        cuts(bnd, e.c.p.n as int),
        all.len() == bnd.len() - 1,
        forall|k: int| 0 <= k < all.len() ==> (#[trigger] all[k]).done && pair_done(e, ng, bnd, k, all[k]),
        0 <= g < ng,
        pair_in(env_tabs(e), e.c, 0, e.c.p.n as int, g, x),
    ensures in_some(all, g, x),
{
    let q = env_tabs(e);
    let c = e.c;
    let (j, i) = choose|j: int, i: int| 0 <= j < c.p.n && #[trigger] pair_at(q, c, j, i, g, x);
    lemma_find(bnd, c.p.n as int, j, 0);
    let k = choose|k: int| 0 <= k < bnd.len() - 1 && bnd[k] <= j < #[trigger] bnd[k + 1];
    assert(pair_done(e, ng, bnd, k, all[k]));
    assert(pair_in(q, c, bnd[k] as int, bnd[k + 1] as int, g, x));
    assert(seg_has(all[k], g, x));
}

/// The finished outputs of the cuts of `[0, p.n)` have, together, exactly the round's pairs.
proof fn lemma_cover<S: SIdx>(e: PairEnv, ng: usize, bnd: Seq<usize>, all: Seq<PairOut<S>>)
    requires
        cuts(bnd, e.c.p.n as int),
        all.len() == bnd.len() - 1,
        forall|k: int| 0 <= k < all.len() ==> (#[trigger] all[k]).done && pair_done(e, ng, bnd, k, all[k]),
    ensures
        outs_ok(all, ng as int, e.c.s.n as int),
        forall|g: int, x: int| 0 <= g < ng ==> (#[trigger] in_some(all, g, x) <==> pair_in(env_tabs(e), e.c, 0, e.c.p.n as int, g, x)),
{
    lemma_cover_ok(e, ng, bnd, all);
    assert forall|g: int, x: int| 0 <= g < ng implies (#[trigger] in_some(all, g, x)
        <==> pair_in(env_tabs(e), e.c, 0, e.c.p.n as int, g, x)) by {
        if in_some(all, g, x) {
            lemma_cover_to(e, ng, bnd, all, g, x);
        }
        if pair_in(env_tabs(e), e.c, 0, e.c.p.n as int, g, x) {
            lemma_cover_from(e, ng, bnd, all, g, x);
        }
    }
}

/// Every output of the cuts has its pairs (when finished) and its matching supplier rows.
pub open spec fn outs_done<S: SIdx>(e: PairEnv, ng: usize, bnd: Seq<usize>, sb: Seq<usize>, all: Seq<PairOut<S>>, nk: int) -> bool {
    forall|k: int| 0 <= k < nk ==> #[trigger] pair_done(e, ng, bnd, k, all[k]) && supp_done(e.c.s, sb, k, all[k])
}

/// Replacing output `k` by a finished one keeps `outs_done`.
proof fn lemma_outs_done_set<S: SIdx>(e: PairEnv, ng: usize, bnd: Seq<usize>, sb: Seq<usize>, all: Seq<PairOut<S>>, nk: int,
    k: int, o: PairOut<S>)
    requires
        outs_done(e, ng, bnd, sb, all, nk), all.len() == nk, 0 <= k < nk,
        pair_done(e, ng, bnd, k, o), supp_done(e.c.s, sb, k, o),
    ensures outs_done(e, ng, bnd, sb, all.update(k, o), nk),
{
    let a1 = all.update(k, o);
    assert forall|k2: int| 0 <= k2 < nk implies #[trigger] pair_done(e, ng, bnd, k2, a1[k2]) && supp_done(e.c.s, sb, k2, a1[k2]) by {
        if k2 != k {
            assert(a1[k2] == all[k2]);
            assert(pair_done(e, ng, bnd, k2, all[k2]));
        }
    }
}

/// Task `k` again, with room for every partsupp row.
fn redo<S: SIdx>(env: &Arc<PairEnv>, ng: usize, bnd: &Vec<usize>, sb: &Vec<usize>, k: usize) -> (o: PairOut<S>)
    requires
        env_ok(**env, ng as int), ng + 1 < usize::MAX, env.c.s.n as int <= S::lim(), comm_ok(env.c.s),
        cuts(bnd@, env.c.p.n as int), cuts(sb@, env.c.s.n as int), sb@.len() == bnd@.len(), k + 1 < bnd@.len(),
    ensures o.done, pair_done(**env, ng, bnd@, k as int, o), supp_done(env.c.s, sb@, k as int, o),
{
    proof {
        lemma_cuts_mono(bnd@, env.c.p.n as int, k as int, k + 1);
        lemma_cuts_mono(bnd@, env.c.p.n as int, k + 1, bnd@.len() - 1);
        lemma_cuts_mono(sb@, env.c.s.n as int, k as int, k + 1);
        lemma_cuts_mono(sb@, env.c.s.n as int, k + 1, sb@.len() - 1);
    }
    let _nb = bnd.len();
    let st = supp_task(&env.c.s, sb[k], sb[k + 1]);
    let tk = new_task(env, ng, bnd[k], bnd[k + 1], env.c.ps.n, st);
    let o = tk.run();
    proof {
        assert(tk.supp.post(o.supp));
    }
    o
}

/// Outputs `outs[i]` of tasks `k0 + i`, each with its pairs (when finished) and its matching supplier rows.
pub open spec fn outs_done_at<S: SIdx>(e: PairEnv, ng: usize, bnd: Seq<usize>, sb: Seq<usize>, outs: Seq<PairOut<S>>,
    k0: int) -> bool {
    forall|i: int| 0 <= i < outs.len() ==> #[trigger] pair_done(e, ng, bnd, k0 + i, outs[i]) && supp_done(e.c.s, sb, k0 + i, outs[i])
}

proof fn lemma_outs_append<S: SIdx>(e: PairEnv, ng: usize, bnd: Seq<usize>, sb: Seq<usize>, all: Seq<PairOut<S>>,
    outs: Seq<PairOut<S>>, k0: int)
    requires outs_done(e, ng, bnd, sb, all, k0), all.len() == k0, outs_done_at(e, ng, bnd, sb, outs, k0),
    ensures outs_done(e, ng, bnd, sb, all + outs, k0 + outs.len()),
{
    let a1 = all + outs;
    assert forall|k: int| 0 <= k < k0 + outs.len() implies #[trigger] pair_done(e, ng, bnd, k, a1[k]) && supp_done(e.c.s, sb, k, a1[k]) by {
        if k < k0 {
            assert(a1[k] == all[k]);
            assert(pair_done(e, ng, bnd, k, all[k]));
        } else {
            assert(a1[k] == outs[k - k0]);
            assert(pair_done(e, ng, bnd, k0 + (k - k0), outs[k - k0]));
        }
    }
}

/// One wave: the pair tasks `[k0, k1)` in one fork-join.
fn wave<S: SIdx>(env: &Arc<PairEnv>, ng: usize, bnd: &Vec<usize>, sb: &Vec<usize>, k0: usize, k1: usize,
    dispatch: &mut Dispatch) -> (r: Result<Vec<PairOut<S>>, QueryError>)
    requires
        env_ok(**env, ng as int), ng + 1 < usize::MAX, env.c.s.n as int <= S::lim(), comm_ok(env.c.s),
        cuts(bnd@, env.c.p.n as int), cuts(sb@, env.c.s.n as int), sb@.len() == bnd@.len(),
        k0 <= k1 < bnd@.len(), k1 - k0 <= MAX_WORKERS,
    ensures
        r matches Err(e) ==> e is WorkerFailed,
        r matches Ok(outs) ==> outs@.len() == k1 - k0 && outs_done_at(**env, ng, bnd@, sb@, outs@, k0 as int),
{
    let pn = env.c.p.n;
    let psn = env.c.ps.n;
    let sn = env.c.s.n;
    let ratio = env.ratio;
    let nk = bnd.len() - 1;
    let mut tasks: Vec<PairTask<S>> = Vec::new();
    let mut k = k0;
    while k < k1
        invariant
            env_ok(**env, ng as int), ng + 1 < usize::MAX, env.c.s.n as int <= S::lim(),
            cuts(bnd@, pn as int), nk == bnd@.len() - 1, pn == env.c.p.n, psn == env.c.ps.n,
            comm_ok(env.c.s), cuts(sb@, sn as int), sb@.len() == nk + 1, sn == env.c.s.n,
            k0 <= k <= k1 <= nk, k1 - k0 <= MAX_WORKERS,
            tasks@.len() == k - k0,
            forall|i: int| 0 <= i < tasks@.len() ==> #[trigger] task_at(**env, ng, bnd@, k0 + i, tasks@[i]),
            forall|i: int| 0 <= i < tasks@.len() ==> #[trigger] supp_at(env.c.s, sb@, k0 + i, tasks@[i]),
        decreases k1 - k,
    {
        let lo = bnd[k];
        let hi = bnd[k + 1];
        proof {
            lemma_cuts_mono(bnd@, pn as int, k as int, k + 1);
            lemma_cuts_mono(bnd@, pn as int, k + 1, nk as int);
            lemma_cuts_mono(sb@, sn as int, k as int, k + 1);
            lemma_cuts_mono(sb@, sn as int, k + 1, nk as int);
        }
        let st = supp_task(&env.c.s, sb[k], sb[k + 1]);
        let cap = pair_cap(ratio, hi - lo, psn);
        let tk = new_task(env, ng, lo, hi, cap, st);
        tasks.push(tk);
        proof {
            assert(task_at(**env, ng, bnd@, k as int, tasks@[k - k0]));
            assert(supp_at(env.c.s, sb@, k as int, tasks@[k - k0]));
        }
        k = k + 1;
    }
    let ghost ts = tasks@;
    proof {
        assert forall|i: int| 0 <= i < tasks@.len() implies #[trigger] tasks@[i].pre() by {
            assert(task_at(**env, ng, bnd@, k0 + i, tasks@[i]));
        }
    }
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => {
            return Err(QueryError::WorkerFailed(e));
        },
    };
    proof {
        assert forall|i: int| 0 <= i < outs@.len() implies #[trigger] pair_done(**env, ng, bnd@, k0 + i, outs@[i])
            && supp_done(env.c.s, sb@, k0 + i, outs@[i]) by {
            assert(task_at(**env, ng, bnd@, k0 + i, ts[i]));
            assert(supp_at(env.c.s, sb@, k0 + i, ts[i]));
            assert(ts[i].post(outs@[i]));
            assert(ts[i].supp.post(outs@[i].supp));
        }
    }
    Ok(outs)
}

/// Every pair of the round, grouped by local group, over the pair outputs.
fn pair_phase<S: SIdx>(env: &Arc<PairEnv>, ng: usize, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<(Vec<PairOut<S>>, Vec<u64>), QueryError>)
    requires
        env_ok(**env, ng as int), ng + 1 < usize::MAX, 1 <= workers <= MAX_WORKERS, env.c.s.n as int <= S::lim(),
        comm_ok(env.c.s),
    ensures
        r matches Err(e) ==> e is WorkerFailed,
        r matches Ok((all, ex)) ==> outs_ok(all@, ng as int, env.c.s.n as int)
            && (forall|g: int, x: int| 0 <= g < ng ==> (#[trigger] in_some(all@, g, x)
                <==> pair_in(*env.tabs, env.c, 0, env.c.p.n as int, g, x)))
            && env.c.s.n <= 64 * ex@.len()
            && forall|j: int| 0 <= j < env.c.s.n ==> #[trigger] bit_at(ex@, j) == cc_row(env.c.s, j),
{
    let pn = env.c.p.n;
    let psn = env.c.ps.n;
    let ratio = env.ratio;
    // About 1M part rows per task, at least one task per worker; whole part blocks.
    let want = pn / 0x10_0000 + 1;
    let ntask = if want > workers { want } else { workers };
    let b0 = split_range(pn, ntask, env.c.p.bs);
    let bnd = if b0.len() < 2 { pad_cuts(b0, pn, 2) } else { b0 };
    let nk = bnd.len() - 1;
    // Every task also decides a range of supplier rows for the subquery.
    let sn = env.c.s.n;
    let sb = pad_cuts(split_range(sn, nk, 1), sn, nk + 1);
    let er0: &PairEnv = &**env;
    let mut all: Vec<PairOut<S>> = Vec::new();
    let mut k0: usize = 0;
    while k0 < nk
        invariant
            env_ok(**env, ng as int), ng + 1 < usize::MAX, 1 <= workers <= MAX_WORKERS, env.c.s.n as int <= S::lim(),
            cuts(bnd@, pn as int), nk == bnd@.len() - 1, pn == env.c.p.n, psn == env.c.ps.n,
            comm_ok(env.c.s), cuts(sb@, sn as int), sb@.len() == nk + 1, sn == env.c.s.n,
            k0 <= nk, all@.len() == k0,
            outs_done(**env, ng, bnd@, sb@, all@, k0 as int),
            *er0 == **env,
        decreases nk - k0,
    {
        let k1 = if nk - k0 > workers { k0 + workers } else { nk };
        let outs = match wave(env, ng, &bnd, &sb, k0, k1, dispatch) {
            Ok(o) => o,
            Err(e) => {
                return Err(e);
            },
        };
        let ghost all0 = all@;
        let ghost ov = outs@;
        let mut outs = outs;
        all.append(&mut outs);
        proof {
            lemma_outs_append(*er0, ng, bnd@, sb@, all0, ov, k0 as int);
        }
        k0 = k1;
    }
    // A task whose scratch was too small runs again with room for every partsupp row.
    proof {
        assert(outs_done(**env, ng, bnd@, sb@, all@, nk as int));
    }
    let mut k: usize = 0;
    while k < nk
        invariant
            env_ok(**env, ng as int), ng + 1 < usize::MAX, env.c.s.n as int <= S::lim(),
            cuts(bnd@, pn as int), nk == bnd@.len() - 1, pn == env.c.p.n, psn == env.c.ps.n,
            k <= nk, all@.len() == nk,
            comm_ok(env.c.s), cuts(sb@, sn as int), sb@.len() == nk + 1, sn == env.c.s.n,
            outs_done(**env, ng, bnd@, sb@, all@, nk as int),
            forall|k2: int| 0 <= k2 < k ==> (#[trigger] all@[k2]).done,
            *er0 == **env,
        decreases nk - k,
    {
        if !all[k].done {
            let o = redo(env, ng, &bnd, &sb, k);
            let ghost a0 = all@;
            proof {
                lemma_outs_done_set(*er0, ng, bnd@, sb@, a0, nk as int, k as int, o);
            }
            all[k] = o;
            proof {
                assert(all@ == a0.update(k as int, o));
                assert forall|k2: int| 0 <= k2 < k + 1 implies (#[trigger] all@[k2]).done by {
                    if k2 < k { assert(all@[k2] == a0[k2]); }
                }
            }
        }
        k = k + 1;
    }
    proof {
        assert forall|k2: int| 0 <= k2 < all@.len() implies (#[trigger] all@[k2]).done && pair_done(**env, ng, bnd@, k2, all@[k2]) by {
            assert(outs_done(**env, ng, bnd@, sb@, all@, nk as int));
        }
        assert forall|k2: int| 0 <= k2 < all@.len() implies #[trigger] supp_done(env.c.s, sb@, k2, all@[k2]) by {
            assert(outs_done(**env, ng, bnd@, sb@, all@, nk as int));
        }
    }
    let er: &PairEnv = &**env;
    proof {
        lemma_cover(*er, ng, bnd@, all@);
    }
    let ex = excl_of(&env.c.s, &all, &sb);
    Ok((all, ex))
}

// ------------------------------------------------------------------------------------------------ counts

/// Every local group's number of distinct, not excluded supplier rows.
fn count_phase<S: SIdx>(outs: Arc<Vec<PairOut<S>>>, excl: &Arc<Vec<u64>>, ng: usize, sn: usize, workers: usize,
    dispatch: &mut Dispatch) -> (r: Result<Vec<u64>, QueryError>)
    requires
        outs_ok(outs@, ng as int, sn as int),
        sn <= 64 * excl@.len(),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Err(e) ==> e is WorkerFailed,
        r matches Ok(cs) ==> cs@.len() == ng
            && forall|g: int| 0 <= g < ng ==> #[trigger] cs@[g] as int == dset(outs@, excl@, sn as int, g).len(),
{
    let nct = if ng >= 64 { if workers > 16 { 16 } else { workers } } else { 1 };
    let gb = split_range(ng, nct, 1);
    let ntk = gb.len() - 1;
    let mut tasks: Vec<CountTask<S>> = Vec::new();
    let mut k: usize = 0;
    while k < ntk
        invariant
            outs_ok(outs@, ng as int, sn as int), sn <= 64 * excl@.len(),
            cuts(gb@, ng as int), ntk == gb@.len() - 1, ntk <= nct, nct <= MAX_WORKERS,
            k <= ntk, tasks@.len() == k,
            forall|i: int| 0 <= i < k ==> (#[trigger] tasks@[i]).pre() && tasks@[i].outs@ == outs@
                && tasks@[i].excl@ == excl@ && tasks@[i].sn == sn && tasks@[i].ng == ng
                && tasks@[i].g0 == gb@[i] && tasks@[i].g1 == gb@[i + 1],
        decreases ntk - k,
    {
        let g0 = gb[k];
        let g1 = gb[k + 1];
        proof {
            lemma_cuts_mono(gb@, ng as int, k + 1, ntk as int);
        }
        let marks = vec![0u64; sn / 64 + 1];
        proof {
            lemma_zero_holds(marks@);
            assert(sn <= 64 * (sn / 64 + 1)) by (nonlinear_arith)
                requires sn == 64 * (sn / 64) + sn % 64, sn % 64 < 64;
        }
        tasks.push(CountTask { outs: outs.clone(), excl: excl.clone(), sn, ng, g0, g1, marks, counts: vec![0u64; g1 - g0] });
        k = k + 1;
    }
    let ghost ts = tasks@;
    let couts = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => {
            return Err(QueryError::WorkerFailed(e));
        },
    };
    let mut cs: Vec<u64> = Vec::new();
    let mut k: usize = 0;
    while k < ntk
        invariant
            cuts(gb@, ng as int), ntk == gb@.len() - 1, couts@.len() == ntk, ts.len() == ntk,
            forall|i: int| 0 <= i < ntk ==> (#[trigger] ts[i]).post(couts@[i]) && ts[i].outs@ == outs@
                && ts[i].excl@ == excl@ && ts[i].sn == sn && ts[i].g0 == gb@[i] && ts[i].g1 == gb@[i + 1],
            k <= ntk, cs@.len() == gb@[k as int],
            forall|g: int| 0 <= g < cs@.len() ==> #[trigger] cs@[g] as int == dset(outs@, excl@, sn as int, g).len(),
        decreases ntk - k,
    {
        let g0 = gb[k];
        let g1 = gb[k + 1];
        let cv = &couts[k];
        proof {
            assert(ts[k as int].post(couts@[k as int]));
        }
        let mut g = g0;
        while g < g1
            invariant
                g0 <= g <= g1, cs@.len() == g, cv@.len() == g1 - g0,
                forall|h: int| g0 <= h < g1 ==> #[trigger] cv@[h - g0] as int == dset(outs@, excl@, sn as int, h).len(),
                forall|h: int| 0 <= h < cs@.len() ==> #[trigger] cs@[h] as int == dset(outs@, excl@, sn as int, h).len(),
            decreases g1 - g,
        {
            let x = cv[g - g0];
            cs.push(x);
            g = g + 1;
        }
        k = k + 1;
    }
    proof {
        lemma_cuts_mono(gb@, ng as int, 0, ntk as int);
    }
    Ok(cs)
}

// ------------------------------------------------------------------------------------------------ collect

/// The groups of the round with a pair, appended in local group order (which is (brand, type, slot) order).
fn collect(counts: &Vec<u64>, b0: usize, b1: usize, t0: usize, t1: usize, ns: usize, res: &mut Vec<Grp>,
    Ghost(c): Ghost<Cols>, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>, Ghost(sizes): Ghost<Seq<i64>>) -> (ok: bool)
    requires
        win_ok(b0 as int, b1 as int, t0 as int, t1 as int, c.p.brand_o@.len() - 1, c.p.type_o@.len() - 1, ns as int),
        ns == sizes.len(),
        counts@.len() == rng(rnd(b0, b1, t0, t1, ns)),
        forall|b: int, tt: int, z: int| #[trigger] in_round(rnd(b0, b1, t0, t1, ns), b, tt, z)
            ==> counts@[gid(rnd(b0, b1, t0, t1, ns), b, tt, z)] as int == kc(c, t, m, sizes, b, tt, z),
        lex_sorted(old(res)@),
        forall|k: int| 0 <= k < old(res)@.len() ==> grp_ok(c, t, m, sizes, #[trigger] old(res)@[k])
            && (old(res)@[k].b < b0 || (old(res)@[k].b == b0 && old(res)@[k].t < t0)),
    ensures
        !ok ==> exists|b: int, tt: int, z: int| b0 <= b < b1 && t0 <= tt < t1 && 0 <= z < ns
            && #[trigger] kc(c, t, m, sizes, b, tt, z) > i64::MAX,
        ok ==> {
            &&& final(res)@.len() >= old(res)@.len()
            &&& final(res)@.subrange(0, old(res)@.len() as int) == old(res)@
            &&& lex_sorted(final(res)@)
            &&& forall|k: int| 0 <= k < final(res)@.len() ==> grp_ok(c, t, m, sizes, #[trigger] final(res)@[k])
            &&& forall|k: int| old(res)@.len() <= k < final(res)@.len()
                ==> b0 <= (#[trigger] final(res)@[k]).b < b1 && t0 <= final(res)@[k].t < t1
            &&& forall|b: int, tt: int, z: int| b0 <= b < b1 && t0 <= tt < t1 && 0 <= z < ns
                && #[trigger] kc(c, t, m, sizes, b, tt, z) > 0
                ==> exists|k: int| old(res)@.len() <= k < final(res)@.len() && at(#[trigger] final(res)@[k], b, tt, z)
        },
{
    let ghost r = rnd(b0, b1, t0, t1, ns);
    let ghost n0 = res@.len();
    let ghost old_res = res@;
    let tw = t1 - t0;
    let ng = counts.len();
    let mut g: usize = 0;
    while g < ng
        invariant
            win_ok(b0 as int, b1 as int, t0 as int, t1 as int, c.p.brand_o@.len() - 1, c.p.type_o@.len() - 1, ns as int),
            r == rnd(b0, b1, t0, t1, ns), ns == sizes.len(), tw == t1 - t0,
            ng == counts@.len(), ng == rng(r),
            forall|b: int, tt: int, z: int| #[trigger] in_round(r, b, tt, z)
                ==> counts@[gid(r, b, tt, z)] as int == kc(c, t, m, sizes, b, tt, z),
            g <= ng,
            res@.len() >= n0, res@.subrange(0, n0 as int) == old_res,
            lex_sorted(res@),
            forall|k: int| 0 <= k < res@.len() ==> grp_ok(c, t, m, sizes, #[trigger] res@[k]),
            forall|k: int| 0 <= k < n0 ==> (#[trigger] res@[k]).b < b0 || (res@[k].b == b0 && res@[k].t < t0),
            forall|k: int| n0 <= k < res@.len() ==> in_round(r, (#[trigger] res@[k]).b as int, res@[k].t as int, res@[k].z as int)
                && gid(r, res@[k].b as int, res@[k].t as int, res@[k].z as int) < g,
            forall|b: int, tt: int, z: int| #[trigger] in_round(r, b, tt, z) && gid(r, b, tt, z) < g
                && kc(c, t, m, sizes, b, tt, z) > 0 ==> exists|k: int| n0 <= k < res@.len() && at(#[trigger] res@[k], b, tt, z),
        decreases ng - g,
    {
        let cnt = counts[g];
        if cnt > 0 {
            let z = g % ns;
            let bt = g / ns;
            let tt = bt % tw;
            let bb = bt / tw;
            proof {
                lemma_decode(r, g as int);
            }
            let ghost (bi, ti, zi) = ((b0 + bb) as int, (t0 + tt) as int, z as int);
            assert(in_round(r, bi, ti, zi));
            if cnt > 0x7FFF_FFFF_FFFF_FFFFu64 {
                proof {
                    assert(kc(c, t, m, sizes, bi, ti, zi) > i64::MAX);
                }
                return false;
            }
            let e = Grp { b: b0 + bb, t: t0 + tt, z, cnt };
            let ghost before = res@;
            proof {
                assert forall|k: int| 0 <= k < res@.len() implies #[trigger] grp_lt(res@[k], e) by {
                    if k >= n0 {
                        lemma_gid_lt(r, res@[k].b as int, res@[k].t as int, res@[k].z as int, bi, ti, zi);
                    }
                }
            }
            res.push(e);
            proof {
                assert forall|a: int, b: int| 0 <= a < b < res@.len() implies #[trigger] grp_lt(res@[a], res@[b])
                    && grp_lt(res@[a], res@[b]) by {
                    if b < before.len() {
                        assert(res@[a] == before[a] && res@[b] == before[b]);
                    } else {
                        assert(res@[a] == before[a]);
                    }
                }
                assert(res@.subrange(0, n0 as int) =~= old_res) by {
                    assert(before.subrange(0, n0 as int) == old_res);
                }
                assert forall|b: int, tt2: int, z2: int| #[trigger] in_round(r, b, tt2, z2) && gid(r, b, tt2, z2) < g + 1
                    && kc(c, t, m, sizes, b, tt2, z2) > 0 implies exists|k: int| n0 <= k < res@.len()
                    && at(#[trigger] res@[k], b, tt2, z2) by {
                    if gid(r, b, tt2, z2) == g {
                        lemma_gid_inj(r, b, tt2, z2, bi, ti, zi);
                        assert(at(res@[res@.len() - 1], b, tt2, z2));
                    } else {
                        let k = choose|k: int| n0 <= k < before.len() && at(#[trigger] before[k], b, tt2, z2);
                        assert(res@[k] == before[k]);
                    }
                }
            }
        } else {
            proof {
                assert forall|b: int, tt2: int, z2: int| #[trigger] in_round(r, b, tt2, z2) && gid(r, b, tt2, z2) < g + 1
                    && kc(c, t, m, sizes, b, tt2, z2) > 0 implies exists|k: int| n0 <= k < res@.len()
                    && at(#[trigger] res@[k], b, tt2, z2) by {
                    if gid(r, b, tt2, z2) == g {
                        assert(counts@[g as int] == 0);
                    }
                }
            }
        }
        g = g + 1;
    }
    proof {
        assert forall|b: int, tt: int, z: int| b0 <= b < b1 && t0 <= tt < t1 && 0 <= z < ns
            && #[trigger] kc(c, t, m, sizes, b, tt, z) > 0
            implies exists|k: int| n0 <= k < res@.len() && at(#[trigger] res@[k], b, tt, z) by {
            assert(in_round(r, b, tt, z));
            lemma_gid_bound(r, b, tt, z);
        }
        assert forall|k: int| n0 <= k < res@.len() implies b0 <= (#[trigger] res@[k]).b < b1 && t0 <= res@[k].t < t1 by {
            assert(in_round(r, res@[k].b as int, res@[k].t as int, res@[k].z as int));
        }
    }
    true
}

/// The general plan's counts (`pair_phase`, `count_phase`): every local group's count.
fn general_counts<S: SIdx>(env: &Arc<PairEnv>, ng: usize, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<Vec<u64>, QueryError>)
    requires
        env_ok(**env, ng as int), ng + 1 < usize::MAX, 1 <= workers <= MAX_WORKERS, env.c.s.n as int <= S::lim(),
        comm_ok(env.c.s),
    ensures
        r matches Err(e) ==> e is WorkerFailed,
        r matches Ok(cs) ==> cs@.len() == ng
            && forall|g: int| 0 <= g < ng ==> #[trigger] cs@[g] as int == pset(*env.tabs, env.c, g).len(),
{
    let (all, ex) = match pair_phase::<S>(env, ng, workers, dispatch) {
        Ok(a) => a,
        Err(e) => {
            return Err(e);
        },
    };
    let ghost av = all@;
    let ghost exv = ex@;
    let outs = Arc::new(all);
    let excl = Arc::new(ex);
    let counts = match count_phase(outs, &excl, ng, env.c.s.n, workers, dispatch) {
        Ok(cs) => cs,
        Err(e) => {
            return Err(e);
        },
    };
    proof {
        assert forall|g: int| 0 <= g < ng implies #[trigger] counts@[g] as int == pset(*env.tabs, env.c, g).len() by {
            let d = dset(av, exv, env.c.s.n as int, g);
            let ps = pset(*env.tabs, env.c, g);
            assert forall|x: int| #[trigger] d.contains(x) == ps.contains(x) by {
                assert(in_some(av, g, x) <==> pair_in(*env.tabs, env.c, 0, env.c.p.n as int, g, x));
            }
            assert(d =~= ps);
        }
    }
    Ok(counts)
}

// ------------------------------------------------------------------------------------------------ the round

/// One round: appends the groups of the window with a pair, in (brand, type, slot) order. `Ok(false)`: some group
/// of the window counts beyond int8 (the statement's error).
pub fn run_round<S: SIdx>(c: &Cols, bok: &Vec<bool>, tlike: &Vec<bool>, sizes: &Vec<i64>, b0: usize, b1: usize, t0: usize,
    t1: usize, sdense: bool, sfirst: i64, workers: usize, dispatch: &mut Dispatch,
    res: &mut Vec<Grp>, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>) -> (r: Result<bool, QueryError>)
    requires
        world_ok(*c, t, m, sdense, sfirst),
        inputs_ok(*c, m, bok@, tlike@, sizes@),
        c.s.n as int <= S::lim(),
        win_ok(b0 as int, b1 as int, t0 as int, t1 as int, bok@.len() as int, tlike@.len() as int, sizes@.len() as int),
        1 <= workers <= MAX_WORKERS,
        lex_sorted(old(res)@),
        forall|k: int| 0 <= k < old(res)@.len() ==> grp_ok(*c, t, m, sizes@, #[trigger] old(res)@[k])
            && (old(res)@[k].b < b0 || (old(res)@[k].b == b0 && old(res)@[k].t < t0)),
    ensures
        r matches Err(e) ==> e is WorkerFailed,
        r matches Ok(false) ==> exists|b: int, tt: int, z: int| b0 <= b < b1 && t0 <= tt < t1 && 0 <= z < sizes@.len()
            && #[trigger] kc(*c, t, m, sizes@, b, tt, z) > i64::MAX,
        r matches Ok(true) ==> {
            &&& final(res)@.len() >= old(res)@.len()
            &&& final(res)@.subrange(0, old(res)@.len() as int) == old(res)@
            &&& lex_sorted(final(res)@)
            &&& forall|k: int| 0 <= k < final(res)@.len() ==> grp_ok(*c, t, m, sizes@, #[trigger] final(res)@[k])
            &&& forall|k: int| old(res)@.len() <= k < final(res)@.len()
                ==> b0 <= (#[trigger] final(res)@[k]).b < b1 && t0 <= final(res)@[k].t < t1
            &&& forall|b: int, tt: int, z: int| b0 <= b < b1 && t0 <= tt < t1 && 0 <= z < sizes@.len()
                && #[trigger] kc(*c, t, m, sizes@, b, tt, z) > 0
                ==> exists|k: int| old(res)@.len() <= k < final(res)@.len() && at(#[trigger] final(res)@[k], b, tt, z)
        },
{
    let ns = sizes.len();
    let tw = t1 - t0;
    let ghost r = rnd(b0, b1, t0, t1, ns);
    proof {
        lemma_win(r);
    }
    let per_b = tw * ns;
    let ng = (b1 - b0) * per_b;
    let q = round_tables(c, bok, tlike, sizes, b0, b1, t0, t1, Ghost(m));
    let ghost qv = q;
    let tabs = Arc::new(q);
    let env = Arc::new(make_env(c, tabs, sdense, sfirst, Ghost(t), Ghost(m), Ghost(r)));
    // The partitioned plan when it applies, else the general plan.
    let counts = match fast_counts(&env, ng, workers, dispatch) {
        Ok(Some(cs)) => cs,
        Ok(None) => match general_counts::<S>(&env, ng, workers, dispatch) {
            Ok(cs) => cs,
            Err(e) => {
                return Err(e);
            },
        },
        Err(e) => {
            return Err(e);
        },
    };
    proof {
        assert forall|b: int, tt: int, z: int| #[trigger] in_round(r, b, tt, z)
            implies counts@[gid(r, b, tt, z)] as int == kc(*c, t, m, sizes@, b, tt, z) by {
            lemma_gid_bound(r, b, tt, z);
            lemma_group_card(*c, t, m, qv, r, b, tt, z);
        }
    }
    let ok = collect(&counts, b0, b1, t0, t1, ns, res, Ghost(*c), Ghost(t), Ghost(m), Ghost(sizes@));
    Ok(ok)
}

} // verus!
