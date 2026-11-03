//! The part pass: per part row, whether it passes the part conditions (`part_ok`: size among `$3..$10`, brand not
//! `$1`, type not matching `$2`) and its group id; and whether partsupp has the layout "`l` consecutive rows per part,
//! in part order" (`ps_partkey[l * a + i] = p_partkey[a]`).
//!
//! Group ids: the brand and type of a part get their ids in two dictionaries built before the pass
//! (`common::text_dict`), the size its position in the distinct sizes `szl`; the group id is
//! `(brand id * nt + type id) * nsz + size position` (`gid_of`), below `2^26`. The tests "brand is `$1`" and
//! "type matches `$2`" are made once per dictionary entry (`bskip`, `tskip`). A part of a listed size whose brand or
//! type is not in the dictionaries is a miss (the caller then takes another path).
//!
//! Output (one task per range `lo..hi` of part rows, `cap = hi - lo`): the qualifying rows of group bucket `b`
//! (`gid >> bshift`) as entries `gid << 32 | row` in region `b` of `buf`, positions `b * cap ..` (`boff[b]` of them).
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::model::*;
use crate::agent::cols::*;
use crate::agent::sem_sub::like_res;
use crate::agent::sem_row::*;
use crate::agent::common::text_dict::*;
use crate::agent::common::word_cache::WordCache;
use crate::agent::supp::{SuppTask, SuppOut, supp_post};

verus! {

/// Group ids are below this bound.
pub const GID_LIMIT: usize = 0x400_0000;

/// The position of key `x` in `keys` (distinct keys: the only one).
pub open spec fn key_index(keys: Seq<Seq<u8>>, x: Seq<u8>) -> int {
    choose|i: int| 0 <= i < keys.len() && keys[i] == x
}

/// The position of size `s` in `szl`.
pub open spec fn size_index(szl: Seq<i64>, s: i64) -> int {
    choose|j: int| 0 <= j < szl.len() && szl[j] == s
}

/// The group id of part row `a`.
pub open spec fn gid_of(kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, szl: Seq<i64>, sv: StoresView, a: int) -> int {
    (key_index(kb, p_brand(sv, a)) * kt.len() + key_index(kt, p_type(sv, a))) * szl.len() + size_index(szl, p_sizes(sv)[a])
}

/// The entry of part row `a` with group id `g`.
pub open spec fn entry(g: int, a: int) -> u64 {
    ((g as u64) << 32u64) | (a as u64)
}

/// The row and group id of an entry.
pub open spec fn entry_row(e: u64) -> int { (e & 0xFFFF_FFFFu64) as int }
pub open spec fn entry_gid(e: u64) -> int { (e >> 32u64) as int }

/// Packing and unpacking an entry.
pub proof fn lemma_entry(g: u64, a: u64)
    requires g < 0x1_0000_0000, a < 0x1_0000_0000,
    ensures entry_row(entry(g as int, a as int)) == a, entry_gid(entry(g as int, a as int)) == g,
{
    assert(((((g << 32u64) | a) & 0xFFFF_FFFFu64) == a) && (((g << 32u64) | a) >> 32u64 == g)) by (bit_vector)
        requires g < 0x1_0000_0000, a < 0x1_0000_0000;
}

/// The keys are distinct.
pub open spec fn distinct_keys(keys: Seq<Seq<u8>>) -> bool {
    forall|i: int, j: int| 0 <= i < j < keys.len() ==> keys[i] != keys[j]
}

/// The distinct sizes `szl` are exactly the values of `$3..$10`.
pub open spec fn sizes_ok(szl: Seq<i64>, ps: Seq<Literal>) -> bool {
    &&& 1 <= szl.len() <= 8
    &&& forall|i: int, j: int| 0 <= i < j < szl.len() ==> szl[i] != szl[j]
    &&& forall|s: int| size_match(ps, 8, s) <==> exists|j: int| 0 <= j < szl.len() && szl[j] == s
}

/// The dictionaries' per-entry tests.
pub open spec fn flags_ok(kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, bskip: Seq<bool>, tskip: Seq<bool>, ps: Seq<Literal>) -> bool {
    &&& bskip.len() == kb.len() && tskip.len() == kt.len()
    &&& forall|i: int| 0 <= i < kb.len() ==> #[trigger] bskip[i] == (kb[i] == brand_lit(ps))
    &&& forall|i: int| 0 <= i < kt.len() ==> #[trigger] tskip[i] == (like_res(kt[i], pat_lit(ps)) == Ok::<Val, SqlError>(Val::Bool(true)))
}

/// The bucket of a group id.
pub open spec fn bucket(g: int, bshift: int) -> int {
    (g as u64 >> (bshift as u64)) as int
}

/// The group-id parameters: `nb` buckets of `2^bshift` ids cover every id.
pub open spec fn buckets_ok(kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, szl: Seq<i64>, bshift: int, nb: int) -> bool {
    &&& kb.len() * kt.len() * szl.len() <= GID_LIMIT
    &&& 0 <= bshift < 32 && nb >= 1
    &&& forall|g: int| 0 <= g < kb.len() * kt.len() * szl.len() ==> #[trigger] bucket(g, bshift) < nb
}

/// Part row `a` has a listed size, but its brand or type is not a dictionary key.
pub open spec fn missed(kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, sv: StoresView, ps: Seq<Literal>, a: int) -> bool {
    size_match(ps, 8, p_sizes(sv)[a] as int) && (!kb.contains(p_brand(sv, a)) || !kt.contains(p_type(sv, a)))
}

/// Entry `e` belongs to region `b` of rows `lo..hi`.
pub open spec fn entry_ok(e: u64, b: int, lo: int, hi: int, kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, szl: Seq<i64>,
    bshift: int, sv: StoresView, ps: Seq<Literal>) -> bool {
    let a = entry_row(e);
    &&& lo <= a < hi
    &&& part_ok(sv, ps, a)
    &&& entry_gid(e) == gid_of(kb, kt, szl, sv, a)
    &&& bucket(entry_gid(e), bshift) == b
}

/// Region `b` holds exactly the entries of the qualifying rows of `lo..end` in bucket `b`.
pub open spec fn region_ok(buf: Seq<u64>, cap: int, cnt: int, b: int, lo: int, end: int, hi: int, kb: Seq<Seq<u8>>,
    kt: Seq<Seq<u8>>, szl: Seq<i64>, bshift: int, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& 0 <= cnt <= cap
    &&& forall|x: int| 0 <= x < cnt ==> entry_ok(#[trigger] buf[b * cap + x], b, lo, end, kb, kt, szl, bshift, sv, ps)
    &&& forall|a: int| lo <= a < end && #[trigger] part_ok(sv, ps, a) && bucket(gid_of(kb, kt, szl, sv, a), bshift) == b
        ==> exists|x: int| 0 <= x < cnt && #[trigger] buf[b * cap + x] == entry(gid_of(kb, kt, szl, sv, a), a)
}

/// Bit `s` of the size mask.
pub open spec fn mask_bit(smask: u64, s: int) -> bool {
    (smask >> (s as u64)) & 1u64 == 1u64
}

/// The size mask and slots at size `s` (`0 <= s < 64`): the bit says whether `s` is listed, the slot where.
pub open spec fn mask_at(smask: u64, sslot: Seq<u8>, szl: Seq<i64>, s: int) -> bool {
    &&& mask_bit(smask, s) <==> exists|j: int| 0 <= j < szl.len() && szl[j] == s
    &&& mask_bit(smask, s) ==> sslot[s] < szl.len() && szl[sslot[s] as int] == s
}

/// The size mask and slots describe the listed sizes in `0..64`.
pub open spec fn mask_ok(smask: u64, sslot: Seq<u8>, szl: Seq<i64>) -> bool {
    &&& sslot.len() == 64
    &&& forall|s: int| 0 <= s < 64 ==> #[trigger] mask_at(smask, sslot, szl, s)
}

/// The read-only inputs of one range of part rows.
pub struct PartCtx {
    pub lo: usize,
    pub hi: usize,
    pub c: Cols,
    pub l: usize,
    pub szl: Vec<i64>,
    pub smask: u64,
    pub sslot: Vec<u8>,
    pub bdict: Arc<TextDict>,
    pub tdict: Arc<TextDict>,
    pub bcache: Arc<WordCache>,
    pub tcache: Arc<WordCache>,
    pub bskip: Arc<Vec<bool>>,
    pub tskip: Arc<Vec<bool>>,
    pub bshift: u32,
    pub nb: usize,
    pub sv: Ghost<StoresView>,
    pub ps: Ghost<Seq<Literal>>,
}

/// One range of part rows: its inputs and its preallocated outputs.
pub struct PartTask {
    pub ctx: PartCtx,
    pub buf: Vec<u64>,
    pub boff: Vec<usize>,
    pub cand: Vec<u32>,
    pub sup: Option<SuppTask>,
}

/// A task's result.
pub struct PartOut {
    pub lo: usize,
    pub hi: usize,
    pub cap: usize,
    pub buf: Vec<u64>,
    pub boff: Vec<usize>,
    pub layout_ok: bool,
    pub misses: usize,
    pub sup: Option<SuppOut>,
}

/// The inputs are consistent.
pub open spec fn ctx_ok(t: PartCtx) -> bool {
    let (sv, ps) = (t.sv@, t.ps@);
    let (kb, kt) = (t.bdict.keys(), t.tdict.keys());
    &&& cols_ok(t.c, sv) && stores_wf(sv)
    &&& t.lo < t.hi <= t.c.np && t.c.np < 0x1_0000_0000
    &&& t.l >= 1 && t.c.nq == t.l * t.c.np
    &&& t.bdict.wf() && t.tdict.wf()
    &&& t.bcache.wf(kb) && t.tcache.wf(kt)
    &&& sizes_ok(t.szl@, ps)
    &&& mask_ok(t.smask, t.sslot@, t.szl@)
    &&& flags_ok(kb, kt, t.bskip@, t.tskip@, ps)
    &&& buckets_ok(kb, kt, t.szl@, t.bshift as int, t.nb as int)
}

/// What a task needs.
pub open spec fn part_pre(t: PartTask) -> bool {
    &&& ctx_ok(t.ctx)
    &&& t.boff@.len() == t.ctx.nb && forall|b: int| 0 <= b < t.ctx.nb ==> #[trigger] t.boff@[b] == 0
    &&& t.buf@.len() >= t.ctx.nb * (t.ctx.hi - t.ctx.lo)
    &&& t.cand@.len() >= t.ctx.hi - t.ctx.lo
}

/// The task saw the layout on its rows.
pub open spec fn post_layout(t: PartCtx, out: PartOut) -> bool {
    out.layout_ok ==> forall|a: int, i: int| t.lo <= a < t.hi && 0 <= i < t.l
        ==> #[trigger] ps_pkeys(t.sv@)[t.l * a + i] == p_keys(t.sv@)[a]
}

/// Without misses, every region holds exactly its entries.
pub open spec fn post_regions(t: PartCtx, out: PartOut) -> bool {
    out.misses == 0 ==> forall|b: int| 0 <= b < t.nb ==> #[trigger] region_ok(out.buf@, (t.hi - t.lo) as int, out.boff@[b] as int,
        b, t.lo as int, t.hi as int, t.hi as int, t.bdict.keys(), t.tdict.keys(), t.szl@, t.bshift as int, t.sv@, t.ps@)
}

/// Misses are real, and without misses no row of the range misses a dictionary.
pub open spec fn post_misses(t: PartCtx, out: PartOut) -> bool {
    &&& out.misses > 0 ==> exists|a: int| t.lo <= a < t.hi && #[trigger] missed(t.bdict.keys(), t.tdict.keys(), t.sv@, t.ps@, a)
    &&& out.misses == 0 ==> forall|a: int| t.lo <= a < t.hi ==> !#[trigger] missed(t.bdict.keys(), t.tdict.keys(), t.sv@, t.ps@, a)
}

/// What a task guarantees (its rows `lo..hi`).
pub open spec fn part_post(t: PartCtx, out: PartOut) -> bool {
    &&& out.lo == t.lo && out.hi == t.hi && out.cap == t.hi - t.lo
    &&& out.buf@.len() >= t.nb * (t.hi - t.lo) && out.boff@.len() == t.nb
    &&& post_layout(t, out)
    &&& post_regions(t, out)
    &&& post_misses(t, out)
}

/// The supplier sub-task's output, when there is one.
pub open spec fn sup_done(st: Option<SuppTask>, so: Option<SuppOut>) -> bool {
    match st {
        Some(t) => so matches Some(o) && supp_post(t.lo as int, t.hi as int, t.sv@, o),
        None => so is None,
    }
}

/// The position of `s` in the distinct sizes, or `szl.len()` when it is not listed.
pub fn size_pos(szl: &Vec<i64>, s: i64) -> (j: usize)
    requires szl@.len() <= 8,
    ensures
        j <= szl@.len(),
        j < szl@.len() ==> szl@[j as int] == s,
        j == szl@.len() ==> forall|k: int| 0 <= k < szl@.len() ==> szl@[k] != s,
    no_unwind
{
    let n = szl.len();
    let mut j: usize = n;
    let mut k: usize = 0;
    while k < n
        invariant
            n == szl@.len(), k <= n, j <= n,
            j < n ==> szl@[j as int] == s,
            j == n ==> forall|x: int| 0 <= x < k ==> szl@[x] != s,
        decreases n - k,
    {
        if szl[k] == s {
            j = k;
        }
        k = k + 1;
    }
    j
}

/// The position of a key among distinct keys is its `key_index`.
proof fn lemma_find_index(keys: Seq<Seq<u8>>, x: Seq<u8>, r: int)
    requires distinct_keys(keys), 0 <= r < keys.len(), keys[r] == x,
    ensures key_index(keys, x) == r, keys.contains(x),
{
    let i = key_index(keys, x);
    assert(0 <= i < keys.len() && keys[i] == x);
    if i != r {
        if i < r { assert(keys[i] != keys[r]); } else { assert(keys[r] != keys[i]); }
    }
}

/// The position of a listed size is its `size_index`.
proof fn lemma_size_index(szl: Seq<i64>, s: i64, j: int)
    requires 0 <= j < szl.len(), szl[j] == s, forall|i: int, k: int| 0 <= i < k < szl.len() ==> szl[i] != szl[k],
    ensures size_index(szl, s) == j,
{
    let i = size_index(szl, s);
    if i != j {
        if i < j { assert(szl[i] != szl[j]); } else { assert(szl[j] != szl[i]); }
    }
}

/// Bounds of a group id.
proof fn lemma_gid_bound(bid: int, tid: int, j: int, nbr: int, nt: int, ns: int)
    requires 0 <= bid < nbr, 0 <= tid < nt, 0 <= j < ns, nbr * nt * ns <= GID_LIMIT,
    ensures
        0 <= (bid * nt + tid) * ns + j < nbr * nt * ns, nbr * nt * ns <= GID_LIMIT,
        0 <= bid * nt <= bid * nt + tid < GID_LIMIT, (bid * nt + tid) * ns < GID_LIMIT,
{
    assert(0 <= (bid * nt + tid) * ns + j < nbr * nt * ns) by (nonlinear_arith)
        requires 0 <= bid < nbr, 0 <= tid < nt, 0 <= j < ns;
    assert(0 <= bid * nt) by (nonlinear_arith) requires 0 <= bid, 0 <= nt;
    assert(bid * nt + tid <= (bid * nt + tid) * ns) by (nonlinear_arith) requires 0 <= bid * nt + tid, ns >= 1;
}

/// Positions of distinct regions differ.
proof fn lemma_regions_disjoint(cap: int, b1: int, x1: int, b2: int, x2: int)
    requires cap >= 1, 0 <= x1 < cap, 0 <= x2 < cap, 0 <= b1, 0 <= b2, b1 != b2,
    ensures b1 * cap + x1 != b2 * cap + x2,
{
    if b1 < b2 {
        assert(b1 * cap + x1 < b2 * cap + x2) by (nonlinear_arith) requires b1 < b2, 0 <= x1 < cap, 0 <= x2, cap >= 1;
    } else {
        assert(b2 * cap + x2 < b1 * cap + x1) by (nonlinear_arith) requires b2 < b1, 0 <= x2 < cap, 0 <= x1, cap >= 1;
    }
}

/// A region position lies inside the buffer.
proof fn lemma_region_in(cap: int, b: int, x: int, nb: int)
    requires cap >= 1, 0 <= b < nb, 0 <= x < cap,
    ensures 0 <= b * cap + x < nb * cap,
{
    assert(0 <= b * cap + x < nb * cap) by (nonlinear_arith) requires cap >= 1, 0 <= b < nb, 0 <= x < cap;
}

/// The partsupp rows `l * a .. l * a + l` all have part key `p_partkey[a]`.
fn rows_match(c: &Cols, l: usize, a: usize, Ghost(sv): Ghost<StoresView>) -> (r: bool)
    requires cols_ok(*c, sv), a < c.np, l >= 1, c.nq == l * c.np,
    ensures r ==> forall|i: int| 0 <= i < l ==> #[trigger] ps_pkeys(sv)[l * a + i] == p_keys(sv)[a as int],
    no_unwind
{
    proof {
        assert(l * a + l <= l * c.np) by (nonlinear_arith) requires a < c.np, l >= 1;
    }
    let k = c.p_key[a];
    let base = l * a;
    let mut ok = true;
    let mut i: usize = 0;
    while i < l
        invariant
            cols_ok(*c, sv), a < c.np, base == l * a, base + l <= c.nq, i <= l, k == p_keys(sv)[a as int],
            ok ==> forall|j: int| 0 <= j < i ==> #[trigger] ps_pkeys(sv)[l * a + j] == p_keys(sv)[a as int],
        decreases l - i,
    {
        if c.ps_pk[base + i] != k {
            ok = false;
        }
        i = i + 1;
    }
    ok
}

/// Casting `i64` to `u64` is injective.
proof fn lemma_cast_inj(x: i64, y: i64)
    requires x as u64 == y as u64,
    ensures x == y,
{
    assert(x as u64 == y as u64 ==> x == y) by (bit_vector);
}

/// `ps_partkey[l * a + i] = p_partkey[a]` for every part row `a` of `lo..hi` and `i < l` (for `l = 4` a branch-free
/// pass that accumulates the differences).
pub fn layout_range(c: &Cols, l: usize, lo: usize, hi: usize, Ghost(sv): Ghost<StoresView>) -> (r: bool)
    requires cols_ok(*c, sv), lo <= hi <= c.np, l >= 1, c.nq == l * c.np,
    ensures r ==> forall|x: int, i: int| lo <= x < hi && 0 <= i < l ==> #[trigger] ps_pkeys(sv)[l * x + i] == p_keys(sv)[x],
    no_unwind
{
    if l == 4 {
        let mut bad: u64 = 0;
        let mut a = lo;
        while a < hi
            invariant
                cols_ok(*c, sv), lo <= a <= hi, hi <= c.np, l == 4, c.nq == l * c.np,
                bad == 0 ==> forall|x: int, i: int| lo <= x < a && 0 <= i < l ==> #[trigger] ps_pkeys(sv)[l * x + i] == p_keys(sv)[x],
            decreases hi - a,
        {
            proof {
                assert(4 * a + 4 <= 4 * c.np) by (nonlinear_arith) requires a < c.np;
            }
            let k = c.p_key[a];
            let b = 4 * a;
            let k0 = c.ps_pk[b];
            let k1 = c.ps_pk[b + 1];
            let k2 = c.ps_pk[b + 2];
            let k3 = c.ps_pk[b + 3];
            let ku = k as u64;
            let t = ((k0 as u64) ^ ku) | ((k1 as u64) ^ ku) | ((k2 as u64) ^ ku) | ((k3 as u64) ^ ku);
            let nb = bad | t;
            proof {
                let (u0, u1, u2, u3) = (k0 as u64, k1 as u64, k2 as u64, k3 as u64);
                assert(nb == 0u64 ==> bad == 0u64 && u0 == ku && u1 == ku && u2 == ku && u3 == ku) by (bit_vector)
                    requires nb == bad | t, t == (u0 ^ ku) | (u1 ^ ku) | (u2 ^ ku) | (u3 ^ ku);
                if nb == 0 {
                    lemma_cast_inj(k0, k);
                    lemma_cast_inj(k1, k);
                    lemma_cast_inj(k2, k);
                    lemma_cast_inj(k3, k);
                    assert forall|x: int, i: int| lo <= x < a + 1 && 0 <= i < l implies #[trigger] ps_pkeys(sv)[l * x + i] == p_keys(sv)[x] by {
                        if x == a {
                            if i == 0 {} else if i == 1 {} else if i == 2 {} else { assert(i == 3); }
                        }
                    }
                }
            }
            bad = nb;
            a = a + 1;
        }
        bad == 0
    } else {
        let mut a = lo;
        while a < hi
            invariant
                cols_ok(*c, sv), lo <= a <= hi, hi <= c.np, l >= 1, c.nq == l * c.np,
                forall|x: int, i: int| lo <= x < a && 0 <= i < l ==> #[trigger] ps_pkeys(sv)[l * x + i] == p_keys(sv)[x],
            decreases hi - a,
        {
            if !rows_match(c, l, a, Ghost(sv)) {
                return false;
            }
            a = a + 1;
        }
        true
    }
}

/// The first `nc` candidates are rows of `lo..end` with a listed size.
pub open spec fn cands_in(cand: Seq<u32>, nc: int, lo: int, end: int, sv: StoresView, ps: Seq<Literal>) -> bool {
    forall|k: int| 0 <= k < nc ==> lo <= #[trigger] cand[k] < end && size_match(ps, 8, p_sizes(sv)[cand[k] as int] as int)
}

/// The first `nc` candidates increase.
pub open spec fn cands_sorted(cand: Seq<u32>, nc: int) -> bool {
    forall|i: int, j: int| 0 <= i < j < nc ==> cand[i] < cand[j]
}

/// Every row of `lo..end` with a listed size is among the first `nc` candidates.
pub open spec fn cands_all(cand: Seq<u32>, nc: int, lo: int, end: int, sv: StoresView, ps: Seq<Literal>) -> bool {
    forall|x: int| lo <= x < end && #[trigger] size_match(ps, 8, p_sizes(sv)[x] as int) ==> exists|k: int| 0 <= k < nc && cand[k] == x
}

/// Whether part size `s` is listed (the mask for `0..64`, the list otherwise).
fn size_listed(t: &PartCtx, s: i64) -> (r: bool)
    requires ctx_ok(*t),
    ensures r == size_match(t.ps@, 8, s as int),
    no_unwind
{
    let ghost ps = t.ps@;
    if 0 <= s && s < 64 {
        proof {
            assert(mask_at(t.smask, t.sslot@, t.szl@, s as int));
            if size_match(ps, 8, s as int) {
                let x = choose|x: int| 0 <= x < t.szl@.len() && t.szl@[x] == s as int;
            }
        }
        (t.smask >> (s as u64)) & 1u64 == 1u64
    } else {
        let nsz = t.szl.len();
        let j = size_pos(&t.szl, s);
        proof {
            if j < nsz { assert(t.szl@[j as int] == s); }
            if size_match(ps, 8, s as int) {
                let x = choose|x: int| 0 <= x < t.szl@.len() && t.szl@[x] == s as int;
            }
        }
        j < nsz
    }
}

/// The rows of the task's range with a listed size, in order, as candidates `0..nc` (branch-free appends).
fn collect_cands(t: &PartCtx, cand: &mut Vec<u32>) -> (nc: usize)
    requires ctx_ok(*t), old(cand)@.len() >= t.hi - t.lo,
    ensures
        final(cand)@.len() == old(cand)@.len(), nc <= t.hi - t.lo,
        cands_in(final(cand)@, nc as int, t.lo as int, t.hi as int, t.sv@, t.ps@),
        cands_sorted(final(cand)@, nc as int),
        cands_all(final(cand)@, nc as int, t.lo as int, t.hi as int, t.sv@, t.ps@),
    no_unwind
{
    let ghost (sv, ps) = (t.sv@, t.ps@);
    let ghost len0 = cand@.len();
    let lo = t.lo;
    let hi = t.hi;
    let mut nc: usize = 0;
    let mut a = lo;
    while a < hi
        invariant
            ctx_ok(*t), lo == t.lo, hi == t.hi, sv == t.sv@, ps == t.ps@, lo <= a <= hi, nc <= a - lo,
            cand@.len() >= hi - lo, cand@.len() == len0,
            cands_in(cand@, nc as int, lo as int, a as int, sv, ps), cands_sorted(cand@, nc as int),
            cands_all(cand@, nc as int, lo as int, a as int, sv, ps),
        decreases hi - a,
    {
        let s = t.c.p_size[a];
        let pass = size_listed(t, s);
        let ghost c0 = cand@;
        cand[nc] = a as u32;
        proof {
            assert(a < 0x1_0000_0000);
            assert forall|k: int| 0 <= k < nc implies cand@[k] == c0[k] by {}
            if pass {
                assert forall|k: int| 0 <= k < nc + 1 implies lo <= #[trigger] cand@[k] < a + 1
                    && size_match(ps, 8, p_sizes(sv)[cand@[k] as int] as int) by {
                    if k < nc { assert(cand@[k] == c0[k]); }
                }
                assert forall|i: int, j: int| 0 <= i < j < nc + 1 implies cand@[i] < cand@[j] by {
                    assert(cand@[i] == c0[i]);
                    if j < nc { assert(cand@[j] == c0[j]); }
                }
                assert forall|x: int| lo <= x < a + 1 && #[trigger] size_match(ps, 8, p_sizes(sv)[x] as int)
                    implies exists|k: int| 0 <= k < nc + 1 && cand@[k] == x by {
                    if x < a {
                        let k = choose|k: int| 0 <= k < nc && c0[k] == x;
                        assert(cand@[k] == x);
                    } else {
                        assert(cand@[nc as int] == x);
                    }
                }
            } else {
                assert forall|k: int| 0 <= k < nc implies lo <= #[trigger] cand@[k] < a + 1
                    && size_match(ps, 8, p_sizes(sv)[cand@[k] as int] as int) by {
                    assert(cand@[k] == c0[k]);
                }
                assert forall|i: int, j: int| 0 <= i < j < nc implies cand@[i] < cand@[j] by {
                    assert(cand@[i] == c0[i] && cand@[j] == c0[j]);
                }
                assert forall|x: int| lo <= x < a + 1 && #[trigger] size_match(ps, 8, p_sizes(sv)[x] as int)
                    implies exists|k: int| 0 <= k < nc && cand@[k] == x by {
                    if x < a {
                        let k = choose|k: int| 0 <= k < nc && c0[k] == x;
                        assert(cand@[k] == x);
                    }
                }
            }
        }
        nc = nc + (if pass { 1usize } else { 0usize });
        a = a + 1;
    }
    nc
}

/// The rows between candidates (from `done`, just past candidate `kc - 1`, up to candidate `kc`, or to `hi` after
/// the last) have no listed size.
proof fn lemma_gap(cand: Seq<u32>, nc: int, kc: int, lo: int, hi: int, done: int, sv: StoresView, ps: Seq<Literal>)
    requires
        cands_in(cand, nc, lo, hi, sv, ps), cands_sorted(cand, nc), cands_all(cand, nc, lo, hi, sv, ps),
        0 <= kc <= nc, done == if kc == 0 { lo } else { cand[kc - 1] + 1 },
    ensures
        kc < nc ==> done <= cand[kc],
        forall|x: int| done <= x < (if kc < nc { cand[kc] as int } else { hi }) && lo <= x
            ==> !size_match(ps, 8, #[trigger] p_sizes(sv)[x] as int),
{
    if kc < nc && kc > 0 {
        assert(cand[kc - 1] < cand[kc]);
    }
    if kc < nc { assert(lo <= cand[kc]); }
    assert forall|x: int| done <= x < (if kc < nc { cand[kc] as int } else { hi }) && lo <= x
        implies !size_match(ps, 8, #[trigger] p_sizes(sv)[x] as int) by {
        if size_match(ps, 8, p_sizes(sv)[x] as int) {
            if kc < nc { assert(lo <= cand[kc] <= hi); }
            assert(x < hi) by { if kc < nc { assert(cand[kc] < hi); } }
            let k = choose|k: int| 0 <= k < nc && cand[k] == x;
            if k < kc {
                if k < kc - 1 { assert(cand[k] < cand[kc - 1]); }
            } else if k > kc {
                assert(cand[kc] < cand[k]);
            }
        }
    }
}

/// Regions after rows `x..y` that all fail the part conditions: unchanged contents, those rows covered.
proof fn lemma_regions_skip_range(buf: Seq<u64>, boff: Seq<usize>, cap: int, nb: int, lo: int, x: int, y: int, hi: int,
    kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, szl: Seq<i64>, bshift: int, sv: StoresView, ps: Seq<Literal>)
    requires
        boff.len() == nb, x <= y,
        forall|b: int| 0 <= b < nb ==> #[trigger] region_ok(buf, cap, boff[b] as int, b, lo, x, hi, kb, kt, szl, bshift, sv, ps),
        forall|r: int| x <= r < y ==> !#[trigger] part_ok(sv, ps, r),
    ensures
        forall|b: int| 0 <= b < nb ==> #[trigger] region_ok(buf, cap, boff[b] as int, b, lo, y, hi, kb, kt, szl, bshift, sv, ps),
{
    assert forall|b: int| 0 <= b < nb implies #[trigger] region_ok(buf, cap, boff[b] as int, b, lo, y, hi, kb, kt, szl, bshift, sv, ps) by {
        assert(region_ok(buf, cap, boff[b] as int, b, lo, x, hi, kb, kt, szl, bshift, sv, ps));
        let cnt = boff[b] as int;
        assert forall|z: int| 0 <= z < cnt implies entry_ok(#[trigger] buf[b * cap + z], b, lo, y, kb, kt, szl, bshift, sv, ps) by {
            assert(entry_ok(buf[b * cap + z], b, lo, x, kb, kt, szl, bshift, sv, ps));
        }
    }
}

/// The decision for one part row.
pub enum RowClass {
    /// The row does not pass the part conditions.
    Skip,
    /// A listed size, but the brand or the type is not a dictionary key.
    Miss,
    /// The row passes, with this group id and bucket.
    Emit(usize, usize),
}

/// Classify part row `a` (see `RowClass`).
fn classify(t: &PartCtx, a: usize) -> (r: RowClass)
    requires ctx_ok(*t), t.lo <= a < t.hi,
    ensures ({
        let (sv, ps) = (t.sv@, t.ps@);
        let (kb, kt) = (t.bdict.keys(), t.tdict.keys());
        match r {
            RowClass::Skip => !part_ok(sv, ps, a as int) && !missed(kb, kt, sv, ps, a as int),
            RowClass::Miss => missed(kb, kt, sv, ps, a as int),
            RowClass::Emit(g, b) => part_ok(sv, ps, a as int) && !missed(kb, kt, sv, ps, a as int) && g == gid_of(kb, kt, t.szl@, sv, a as int)
                && g < GID_LIMIT && b == bucket(g as int, t.bshift as int) && b < t.nb,
        }
    }),
    no_unwind
{
    let ghost (sv, ps) = (t.sv@, t.ps@);
    let ghost (kb, kt) = (t.bdict.keys(), t.tdict.keys());
    let c = t.c;
    let s = c.p_size[a];
    let nsz = t.szl.len();
    let j: usize;
    if 0 <= s && s < 64 {
        let bit = (t.smask >> (s as u64)) & 1u64;
        proof { assert(mask_at(t.smask, t.sslot@, t.szl@, s as int)); }
        if bit != 1u64 {
            proof {
                assert(!size_match(ps, 8, s as int)) by {
                    if size_match(ps, 8, s as int) {
                        let x = choose|x: int| 0 <= x < t.szl@.len() && t.szl@[x] == s as int;
                    }
                }
            }
            return RowClass::Skip;
        }
        j = t.sslot[s as usize] as usize;
    } else {
        j = size_pos(&t.szl, s);
        if j == nsz {
            proof {
                assert(!size_match(ps, 8, s as int)) by {
                    if size_match(ps, 8, s as int) {
                        let x = choose|x: int| 0 <= x < t.szl@.len() && t.szl@[x] == s as int;
                    }
                }
            }
            return RowClass::Skip;
        }
    }
    proof {
        assert(j < nsz && t.szl@[j as int] == s);
        assert(size_match(ps, 8, s as int));
    }
    let (bx, by) = trange(&c.brand, a, Ghost(c.np as int));
    let mut bid = t.bcache.lookup(c.brand.bytes, bx, by, Ghost(kb));
    if bid == ABSENT {
        bid = t.bdict.find(c.brand.bytes, bx, by);
    }
    let (tx, ty) = trange(&c.ptype, a, Ghost(c.np as int));
    let mut tid = t.tcache.lookup(c.ptype.bytes, tx, ty, Ghost(kt));
    if tid == ABSENT {
        tid = t.tdict.find(c.ptype.bytes, tx, ty);
    }
    proof {
        assert(c.brand.bytes@.subrange(bx as int, by as int) == p_brand(sv, a as int));
        assert(c.ptype.bytes@.subrange(tx as int, ty as int) == p_type(sv, a as int));
    }
    if bid == ABSENT || tid == ABSENT {
        proof {
            if bid == ABSENT {
                assert(!kb.contains(p_brand(sv, a as int))) by {
                    if kb.contains(p_brand(sv, a as int)) {
                        let x = choose|x: int| 0 <= x < kb.len() && kb[x] == p_brand(sv, a as int);
                        assert(t.bdict.key(x) != p_brand(sv, a as int));
                    }
                }
            } else {
                assert(!kt.contains(p_type(sv, a as int))) by {
                    if kt.contains(p_type(sv, a as int)) {
                        let x = choose|x: int| 0 <= x < kt.len() && kt[x] == p_type(sv, a as int);
                        assert(t.tdict.key(x) != p_type(sv, a as int));
                    }
                }
            }
        }
        return RowClass::Miss;
    }
    proof {
        t.bdict.lemma_keys_distinct();
        t.tdict.lemma_keys_distinct();
        assert(kb[bid as int] == p_brand(sv, a as int));
        assert(kt[tid as int] == p_type(sv, a as int));
        lemma_find_index(kb, p_brand(sv, a as int), bid as int);
        lemma_find_index(kt, p_type(sv, a as int), tid as int);
        assert(!missed(kb, kt, sv, ps, a as int));
        lemma_size_index(t.szl@, s, j as int);
        assert(t.bskip@[bid as int] == (kb[bid as int] == brand_lit(ps)));
        assert(t.tskip@[tid as int] == (like_res(kt[tid as int], pat_lit(ps)) == Ok::<Val, SqlError>(Val::Bool(true))));
    }
    if t.bskip[bid as usize] || t.tskip[tid as usize] {
        return RowClass::Skip;
    }
    let nt = t.tdict.count();
    proof {
        lemma_gid_bound(bid as int, tid as int, j as int, kb.len() as int, nt as int, nsz as int);
    }
    let g = (bid as usize * nt + tid as usize) * nsz + j;
    proof {
        assert(g == gid_of(kb, kt, t.szl@, sv, a as int));
        assert(bucket(g as int, t.bshift as int) < t.nb);
    }
    let b = ((g as u64) >> (t.bshift as u64)) as usize;
    RowClass::Emit(g, b)
}

/// Regions after a row that emits nothing: unchanged contents, one more row covered.
proof fn lemma_regions_skip(buf: Seq<u64>, boff: Seq<usize>, cap: int, nb: int, lo: int, a: int, hi: int, kb: Seq<Seq<u8>>,
    kt: Seq<Seq<u8>>, szl: Seq<i64>, bshift: int, sv: StoresView, ps: Seq<Literal>)
    requires
        boff.len() == nb,
        forall|b: int| 0 <= b < nb ==> #[trigger] region_ok(buf, cap, boff[b] as int, b, lo, a, hi, kb, kt, szl, bshift, sv, ps),
        !part_ok(sv, ps, a),
    ensures
        forall|b: int| 0 <= b < nb ==> #[trigger] region_ok(buf, cap, boff[b] as int, b, lo, a + 1, hi, kb, kt, szl, bshift, sv, ps),
{
    assert forall|b: int| 0 <= b < nb implies #[trigger] region_ok(buf, cap, boff[b] as int, b, lo, a + 1, hi, kb, kt, szl, bshift, sv, ps) by {
        assert(region_ok(buf, cap, boff[b] as int, b, lo, a, hi, kb, kt, szl, bshift, sv, ps));
        let cnt = boff[b] as int;
        assert forall|x: int| 0 <= x < cnt implies entry_ok(#[trigger] buf[b * cap + x], b, lo, a + 1, kb, kt, szl, bshift, sv, ps) by {
            assert(entry_ok(buf[b * cap + x], b, lo, a, kb, kt, szl, bshift, sv, ps));
        }
    }
}

/// Regions after row `a` emitted entry `e` at position `bw * cap + boff[bw]`.
proof fn lemma_regions_push(buf0: Seq<u64>, buf: Seq<u64>, boff0: Seq<usize>, boff: Seq<usize>, cap: int, nb: int,
    lo: int, a: int, hi: int, kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, szl: Seq<i64>, bshift: int, sv: StoresView,
    ps: Seq<Literal>, g: int, bw: int)
    requires
        boff0.len() == nb, boff.len() == nb, cap >= 1, 0 <= bw < nb, 0 <= lo <= a < hi, a < 0x1_0000_0000, 0 <= g < GID_LIMIT,
        part_ok(sv, ps, a), g == gid_of(kb, kt, szl, sv, a), bw == bucket(g, bshift),
        boff0[bw] < cap,
        buf0.len() == buf.len(), buf.len() >= nb * cap,
        buf == buf0.update(bw * cap + boff0[bw], entry(g, a)),
        boff[bw] == boff0[bw] + 1,
        forall|b: int| 0 <= b < nb && b != bw ==> boff[b] == boff0[b],
        forall|b: int| 0 <= b < nb ==> #[trigger] region_ok(buf0, cap, boff0[b] as int, b, lo, a, hi, kb, kt, szl, bshift, sv, ps),
    ensures
        forall|b: int| 0 <= b < nb ==> #[trigger] region_ok(buf, cap, boff[b] as int, b, lo, a + 1, hi, kb, kt, szl, bshift, sv, ps),
{
    lemma_entry(g as u64, a as u64);
    lemma_region_in(cap, bw, boff0[bw] as int, nb);
    assert forall|b: int| 0 <= b < nb implies #[trigger] region_ok(buf, cap, boff[b] as int, b, lo, a + 1, hi, kb, kt, szl, bshift, sv, ps) by {
        assert(region_ok(buf0, cap, boff0[b] as int, b, lo, a, hi, kb, kt, szl, bshift, sv, ps));
        let cnt = boff[b] as int;
        let cnt0 = boff0[b] as int;
        assert forall|x: int| 0 <= x < cnt implies entry_ok(#[trigger] buf[b * cap + x], b, lo, a + 1, kb, kt, szl, bshift, sv, ps) by {
            if x < cnt0 {
                if bw != b {
                    lemma_regions_disjoint(cap, b, x, bw, boff0[bw] as int);
                }
                lemma_region_in(cap, b, x, nb);
                assert(buf[b * cap + x] == buf0[b * cap + x]);
                assert(entry_ok(buf0[b * cap + x], b, lo, a, kb, kt, szl, bshift, sv, ps));
            } else {
                assert(b == bw && x == cnt0);
            }
        }
        assert forall|r: int| lo <= r < a + 1 && #[trigger] part_ok(sv, ps, r) && bucket(gid_of(kb, kt, szl, sv, r), bshift) == b
            implies exists|x: int| 0 <= x < cnt && #[trigger] buf[b * cap + x] == entry(gid_of(kb, kt, szl, sv, r), r) by {
            if r < a {
                let x = choose|x: int| 0 <= x < cnt0 && #[trigger] buf0[b * cap + x] == entry(gid_of(kb, kt, szl, sv, r), r);
                if bw != b {
                    lemma_regions_disjoint(cap, b, x, bw, boff0[bw] as int);
                } else {
                    assert(x != boff0[bw] as int);
                }
                lemma_region_in(cap, b, x, nb);
                assert(buf[b * cap + x] == buf0[b * cap + x]);
                assert(cnt0 <= cnt);
            } else {
                assert(r == a);
                assert(b == bw);
                assert(cnt == cnt0 + 1);
                assert(buf[bw * cap + boff0[bw]] == entry(g, a));
                assert(buf[b * cap + cnt0] == entry(gid_of(kb, kt, szl, sv, r), r));
                assert(0 <= cnt0 < cnt);
            }
        }
    }
}

impl WorkerTask for PartTask {
    type Output = PartOut;

    open spec fn pre(&self) -> bool {
        &&& part_pre(*self)
        &&& self.sup matches Some(st) ==> st.pre()
    }

    open spec fn post(&self, out: PartOut) -> bool {
        &&& part_post(self.ctx, out)
        &&& sup_done(self.sup, out.sup)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.ctx.lo as u64, self.ctx.hi as u64)
    }

    fn run(self) -> (out: PartOut) {
        let PartTask { ctx, mut buf, mut boff, mut cand, sup } = self;
        let ghost (sv, ps) = (ctx.sv@, ctx.ps@);
        let ghost (kb, kt) = (ctx.bdict.keys(), ctx.tdict.keys());
        let lo = ctx.lo;
        let hi = ctx.hi;
        let nb = ctx.nb;
        let cap = hi - lo;
        let layout_ok = layout_range(&ctx.c, ctx.l, lo, hi, Ghost(sv));
        let mut misses: usize = 0;
        let nc = collect_cands(&ctx, &mut cand);
        let mut kc: usize = 0;
        let ghost mut done: int = lo as int;
        proof {
            assert forall|b: int| 0 <= b < nb implies #[trigger] region_ok(buf@, cap as int, boff@[b] as int, b,
                lo as int, lo as int, hi as int, kb, kt, ctx.szl@, ctx.bshift as int, sv, ps) by {
                assert(boff@[b] == 0);
            }
        }
        while kc < nc
            invariant
                ctx_ok(ctx), ctx.lo == lo, ctx.hi == hi, ctx.nb == nb, ctx.sv@ == sv, ctx.ps@ == ps,
                kb == ctx.bdict.keys(), kt == ctx.tdict.keys(),
                cands_in(cand@, nc as int, lo as int, hi as int, sv, ps), cands_sorted(cand@, nc as int),
                cands_all(cand@, nc as int, lo as int, hi as int, sv, ps), nc <= cand@.len(),
                kc <= nc, done == if kc == 0 { lo as int } else { cand@[kc - 1] + 1 },
                cap == hi - lo, lo <= done <= hi, misses <= done - lo,
                buf@.len() >= nb * cap, boff@.len() == nb,
                forall|b: int| 0 <= b < nb ==> #[trigger] boff@[b] <= done - lo,
                layout_ok ==> forall|x: int, i: int| lo <= x < hi && 0 <= i < ctx.l ==> #[trigger] ps_pkeys(sv)[ctx.l * x + i] == p_keys(sv)[x],
                misses == 0 ==> forall|b: int| 0 <= b < nb ==> #[trigger] region_ok(buf@, cap as int, boff@[b] as int, b,
                    lo as int, done, hi as int, kb, kt, ctx.szl@, ctx.bshift as int, sv, ps),
                misses > 0 ==> exists|x: int| lo <= x < done && #[trigger] missed(kb, kt, sv, ps, x),
                misses == 0 ==> forall|x: int| lo <= x < done ==> !#[trigger] missed(kb, kt, sv, ps, x),
            decreases nc - kc,
        {
            let a = cand[kc] as usize;
            proof {
                lemma_gap(cand@, nc as int, kc as int, lo as int, hi as int, done, sv, ps);
                assert(lo <= a < hi);
                if misses == 0 {
                    lemma_regions_skip_range(buf@, boff@, cap as int, nb as int, lo as int, done, a as int, hi as int, kb, kt,
                        ctx.szl@, ctx.bshift as int, sv, ps);
                }
                assert forall|x: int| done <= x < a implies !#[trigger] missed(kb, kt, sv, ps, x) && !part_ok(sv, ps, x) by {
                    assert(!size_match(ps, 8, p_sizes(sv)[x] as int));
                }
            }
            let ghost misses0 = misses;
            match classify(&ctx, a) {
                RowClass::Skip => {
                    proof {
                        if misses == 0 {
                            lemma_regions_skip(buf@, boff@, cap as int, nb as int, lo as int, a as int, hi as int, kb, kt,
                                ctx.szl@, ctx.bshift as int, sv, ps);
                        }
                    }
                },
                RowClass::Miss => {
                    misses = misses + 1;
                },
                RowClass::Emit(g, b) => {
                    let p = boff[b];
                    let blen = buf.len();
                    proof {
                        assert(p <= a - lo);
                        lemma_region_in(cap as int, b as int, p as int, nb as int);
                        assert(b * cap + p < blen);
                        assert(b * cap <= b * cap + p);
                    }
                    let ghost buf0 = buf@;
                    let ghost boff0 = boff@;
                    buf[b * cap + p] = ((g as u64) << 32u64) | (a as u64);
                    boff[b] = p + 1;
                    proof {
                        if misses == 0 {
                            lemma_regions_push(buf0, buf@, boff0, boff@, cap as int, nb as int, lo as int, a as int, hi as int,
                                kb, kt, ctx.szl@, ctx.bshift as int, sv, ps, g as int, b as int);
                        }
                    }
                },
            }
            proof {
                if misses > 0 && misses0 > 0 {
                    let x = choose|x: int| lo <= x < done && #[trigger] missed(kb, kt, sv, ps, x);
                }
                assert forall|b: int| 0 <= b < nb implies #[trigger] boff@[b] <= a + 1 - lo by {}
                assert forall|x: int| lo <= x < a + 1 && misses == 0 implies !#[trigger] missed(kb, kt, sv, ps, x) by {
                    if x < done { } else if x < a { } else { }
                }
                done = a + 1;
            }
            kc = kc + 1;
        }
        proof {
            lemma_gap(cand@, nc as int, kc as int, lo as int, hi as int, done, sv, ps);
            if misses == 0 {
                lemma_regions_skip_range(buf@, boff@, cap as int, nb as int, lo as int, done, hi as int, hi as int, kb, kt,
                    ctx.szl@, ctx.bshift as int, sv, ps);
                assert forall|x: int| lo <= x < hi implies !#[trigger] missed(kb, kt, sv, ps, x) by {
                    if x >= done { assert(!size_match(ps, 8, p_sizes(sv)[x] as int)); }
                }
            }
            if misses > 0 {
                let x = choose|x: int| lo <= x < done && #[trigger] missed(kb, kt, sv, ps, x);
            }
        }
        let so = match sup {
            Some(st) => Some(st.run()),
            None => None,
        };
        PartOut { lo, hi, cap, buf, boff, layout_ok, misses, sup: so }
    }
}

} // verus!
