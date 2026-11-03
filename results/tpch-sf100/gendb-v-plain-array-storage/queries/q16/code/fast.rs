//! The fast path's preparations and passes on the calling thread: the prefix dictionaries and their flags
//! (`build_dicts`), the group-id buckets (`bucket_params`), the part pass (`run_parts`), the bit set of excluded
//! supplier keys (`excl_bits`) and the distinct-count pass with its flattened counts (`run_counts`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::query::param_domain;
use crate::exec::value::*;
use crate::exec::fns::like::like_value_exec;
use crate::gendb_params::Params;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{Dispatch, fork_join, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::agent::model::*;
use crate::agent::cols::*;
use crate::agent::sem_ast::backslash;
use crate::agent::sem_sub::like_res;
use crate::agent::sem_row::*;
use crate::agent::parts::*;
use crate::agent::supp::copy_bytes;
use crate::agent::prep::{big, big4};
use crate::agent::common::like_two::{plain_pattern, ascii};
use crate::agent::common::text_dict::*;
use crate::agent::common::word_cache::WordCache;
use crate::agent::common::split::*;
use crate::agent::common::bitset::*;
use crate::agent::sem_link::*;
use crate::agent::sem_sub::excluded;
use crate::agent::supp::{SuppResult, SuppOut, SuppTask, supp_result_ok, supp_post, supp_merge, make_supp_task, supp_pass, has_key};
use crate::agent::counts::*;
use crate::agent::common::key_group::*;
use crate::agent::output::{grow, tables_ok, present, orow, build_output};
use crate::agent::sem_result::*;
use crate::agent::common::ranks::{distinct_texts, distinct_ints};
use crate::agent::common::like_two::lemma_like_plain;
use crate::gendb_entry::results::{ResultColumns, columns_wf, columns_view};
use crate::gendb_entry::bound_db;
use crate::query::query_spec_at;
use crate::spec::order::ordered_ok;

verus! {

/// `p` is a plain pattern: ASCII without a backslash.
pub fn plain_exec(p: &[u8]) -> (r: bool)
    ensures r == plain_pattern(p@),
{
    let n = p.len();
    let mut i: usize = 0;
    while i < n
        invariant n == p@.len(), i <= n, forall|j: int| 0 <= j < i ==> #[trigger] p@[j] < 0x80u8 && p@[j] != 0x5Cu8,
        decreases n - i,
    {
        if p[i] >= 0x80u8 || p[i] == 0x5Cu8 {
            proof { assert(!(p@[i as int] < 0x80u8 && p@[i as int] != 0x5Cu8)); }
            return false;
        }
        i = i + 1;
    }
    proof {
        assert(ascii(p@));
    }
    true
}

// ------------------------------------------------------------------------------------------------ dictionaries

/// The dictionaries of the fast path and their flags.
pub struct Dicts {
    pub bd: TextDict,
    pub td: TextDict,
    pub bskip: Vec<bool>,
    pub tskip: Vec<bool>,
}

pub open spec fn dicts_ok(d: Dicts, ps: Seq<Literal>) -> bool {
    &&& d.bd.wf() && d.td.wf()
    &&& flags_ok(d.bd.keys(), d.td.keys(), d.bskip@, d.tskip@, ps)
}

/// Insert the values of rows `0..pre` of a text column (keys that do not fit are left out).
fn insert_prefix(d: &mut TextDict, t: &TextCol, n: usize, pre: usize)
    requires old(d).wf(), tcol_wf(*t, n as int), pre <= n,
    ensures final(d).wf(),
{
    let mut a: usize = 0;
    while a < pre
        invariant d.wf(), tcol_wf(*t, n as int), pre <= n, a <= pre,
        decreases pre - a,
    {
        let (x, y) = trange(t, a, Ghost(n as int));
        let _ = d.insert(t.bytes, x, y);
        a = a + 1;
    }
}

/// Per brand key: whether it is `$1`.
fn brand_flags(bd: &TextDict, p0: &[u8]) -> (f: Vec<bool>)
    requires bd.wf(),
    ensures f@.len() == bd.n(), forall|i: int| 0 <= i < bd.n() ==> #[trigger] f@[i] == (bd.keys()[i] == p0@),
{
    let n = bd.count();
    let plen = p0.len();
    let mut f: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant bd.wf(), n == bd.n(), plen == p0@.len(), i <= n, f@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] f@[j] == (bd.keys()[j] == p0@),
        decreases n - i,
    {
        let (x, y) = bd.key_range(i);
        let e = vec_bytes_eq_range(&bd.kbytes, x, y, p0, 0, plen);
        proof { assert(p0@.subrange(0, plen as int) =~= p0@); }
        f.push(e);
        i = i + 1;
    }
    f
}

/// Per type key: whether it matches `$2`.
fn type_flags(td: &TextDict, p1: &[u8]) -> (f: Vec<bool>)
    requires td.wf(),
    ensures f@.len() == td.n(),
        forall|i: int| 0 <= i < td.n() ==> #[trigger] f@[i] == (like_res(td.keys()[i], p1@) == Ok::<Val, SqlError>(Val::Bool(true))),
{
    let pat = EVal::Text(copy_bytes(p1, 0, p1.len()));
    let escv = vec![92u8];
    proof {
        assert(p1@.subrange(0, p1@.len() as int) =~= p1@);
        assert(escv@ =~= backslash());
    }
    let esc = EVal::Text(escv);
    let n = td.count();
    let mut f: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant td.wf(), n == td.n(), i <= n, f@.len() == i,
            pat@ == Val::Text(p1@), esc@ == Val::Text(backslash()),
            forall|j: int| 0 <= j < i ==> #[trigger] f@[j] == (like_res(td.keys()[j], p1@) == Ok::<Val, SqlError>(Val::Bool(true))),
        decreases n - i,
    {
        let (x, y) = td.key_range(i);
        let v = copy_bytes(td.kbytes.as_slice(), x, y);
        let s = EVal::Text(v);
        let r = like_value_exec(&s, &pat, &esc);
        let hit = match r { Ok(EVal::Bool(b)) => b, _ => false };
        proof {
            assert(s@ == Val::Text(td.keys()[i as int]));
            assert(hit == (like_res(td.keys()[i as int], p1@) == Ok::<Val, SqlError>(Val::Bool(true))));
        }
        f.push(hit);
        i = i + 1;
    }
    f
}

/// The dictionaries of the brands and types of the first part rows, with their flags.
pub fn build_dicts(c: &Cols, params: &Params, pre: usize, Ghost(sv): Ghost<StoresView>) -> (d: Dicts)
    requires cols_ok(*c, sv), param_domain(params@), pre <= c.np,
    ensures dicts_ok(d, params@),
{
    proof { lemma_params(params@); }
    let mut bd = TextDict::new(255);
    let mut td = TextDict::new(4095);
    insert_prefix(&mut bd, &c.brand, c.np, pre);
    insert_prefix(&mut td, &c.ptype, c.np, pre);
    let bskip = brand_flags(&bd, params.p0);
    let tskip = type_flags(&td, params.p1);
    Dicts { bd, td, bskip, tskip }
}

/// The word cache of a dictionary's keys.
pub fn build_cache(d: &TextDict) -> (c: WordCache)
    requires d.wf(),
    ensures c.wf(d.keys()),
{
    let mut c = WordCache::new(1023, Ghost(d.keys()));
    let n = d.count();
    let kb = d.kbytes.as_slice();
    let mut i: usize = 0;
    while i < n
        invariant d.wf(), n == d.n(), i <= n, c.wf(d.keys()), kb@ == d.kbytes@,
        decreases n - i,
    {
        let (x, y) = d.key_range(i);
        proof { assert(d.keys()[i as int] == kb@.subrange(x as int, y as int)); }
        c.insert(kb, x, y, i as u32, Ghost(d.keys()));
        i = i + 1;
    }
    c
}

// ------------------------------------------------------------------------------------------------ size mask

/// The size mask and slots of the distinct sizes `szl` (sizes outside `0..64` are not in the mask).
pub fn size_mask(szl: &Vec<i64>) -> (r: (u64, Vec<u8>))
    requires szl@.len() <= 8, forall|i: int, j: int| 0 <= i < j < szl@.len() ==> szl@[i] != szl@[j],
    ensures mask_ok(r.0, r.1@, szl@),
{
    let mut m: u64 = 0;
    let mut sl: Vec<u8> = vec![0u8; 64];
    proof {
        assert forall|s: int| 0 <= s < 64 implies !mask_bit(0u64, s) by {
            let su = s as u64;
            assert((0u64 >> su) & 1u64 == 0u64) by (bit_vector);
        }
    }
    let mut j: usize = 0;
    while j < szl.len()
        invariant
            szl@.len() <= 8, j <= szl@.len(), sl@.len() == 64,
            forall|i: int, k: int| 0 <= i < k < szl@.len() ==> szl@[i] != szl@[k],
            forall|s: int| 0 <= s < 64 ==> (#[trigger] mask_bit(m, s) <==> exists|x: int| 0 <= x < j && szl@[x] == s),
            forall|s: int| 0 <= s < 64 && #[trigger] mask_bit(m, s) ==> sl@[s] < j && szl@[sl@[s] as int] == s,
        decreases szl@.len() - j,
    {
        let v = szl[j];
        if 0 <= v && v < 64 {
            let ghost m0 = m;
            let ghost sl0 = sl@;
            m = m | (1u64 << (v as u64));
            sl.set(v as usize, j as u8);
            proof {
                assert forall|s: int| 0 <= s < 64 implies (#[trigger] mask_bit(m, s) <==> (mask_bit(m0, s) || s == v as int)) by {
                    let (su, vu) = (s as u64, v as u64);
                    assert(((m0 | (1u64 << vu)) >> su) & 1u64 == 1u64 <==> ((m0 >> su) & 1u64 == 1u64 || su == vu)) by (bit_vector)
                        requires su < 64, vu < 64;
                }
                assert(!mask_bit(m0, v as int)) by {
                    if mask_bit(m0, v as int) {
                        let x = choose|x: int| 0 <= x < j && szl@[x] == v as int;
                        assert(szl@[x] != szl@[j as int]);
                    }
                }
                assert forall|s: int| 0 <= s < 64 implies (#[trigger] mask_bit(m, s) <==> exists|x: int| 0 <= x < j + 1 && szl@[x] == s) by {
                    if mask_bit(m, s) && s != v as int {
                        let x = choose|x: int| 0 <= x < j && szl@[x] == s;
                    }
                    if exists|x: int| 0 <= x < j + 1 && szl@[x] == s {
                        let x = choose|x: int| 0 <= x < j + 1 && szl@[x] == s;
                        if x < j { assert(mask_bit(m0, s)); }
                    }
                }
                assert forall|s: int| 0 <= s < 64 && #[trigger] mask_bit(m, s) implies sl@[s] < j + 1 && szl@[sl@[s] as int] == s by {
                    if s != v as int {
                        assert(mask_bit(m0, s));
                        assert(sl@[s] == sl0[s]);
                    }
                }
            }
        } else {
            proof {
                assert forall|s: int| 0 <= s < 64 implies (#[trigger] mask_bit(m, s) <==> exists|x: int| 0 <= x < j + 1 && szl@[x] == s) by {
                    if exists|x: int| 0 <= x < j + 1 && szl@[x] == s {
                        let x = choose|x: int| 0 <= x < j + 1 && szl@[x] == s;
                        if x == j { assert(false); }
                    }
                }
            }
        }
        j = j + 1;
    }
    proof {
        assert forall|s: int| 0 <= s < 64 implies #[trigger] mask_at(m, sl@, szl@, s) by {
            assert(mask_bit(m, s) <==> exists|x: int| 0 <= x < szl@.len() && szl@[x] == s);
        }
    }
    (m, sl)
}

/// A copy of `v`.
pub fn copy_u8(v: &Vec<u8>) -> (r: Vec<u8>)
    ensures r@ == v@,
{
    let mut r: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v@.len(), r@ == v@.subrange(0, i as int),
        decreases v@.len() - i,
    {
        r.push(v[i]);
        i = i + 1;
        proof { assert(r@ =~= v@.subrange(0, i as int)); }
    }
    proof { assert(v@.subrange(0, v@.len() as int) =~= v@); }
    r
}

// ------------------------------------------------------------------------------------------------ buckets

/// The bucket of a group id is its id shifted right by `s`; a bucket's ids are `b << s ..` (`2^s` of them).
pub proof fn lemma_bucket_range(g: u64, b: u64, s: u64)
    requires s < 32, g < 0x1_0000_0000,
    ensures (g >> s) == b ==> (b << s) <= g && g - (b << s) < (1u64 << s),
{
    assert((g >> s) == b ==> (b << s) <= g && g - (b << s) < (1u64 << s)) by (bit_vector) requires s < 32, g < 0x1_0000_0000;
}

pub proof fn lemma_bucket_of(g: u64, b: u64, s: u64)
    requires s < 32, g < 0x1_0000_0000, b < 0x1_0000_0000, (b << s) <= g, g - (b << s) < (1u64 << s),
    ensures g >> s == b,
{
    assert(g >> s == b) by (bit_vector) requires s < 32, g < 0x1_0000_0000, b < 0x1_0000_0000, (b << s) <= g, g - (b << s) < (1u64 << s);
}

pub proof fn lemma_shift_mono(g1: u64, g2: u64, s: u64)
    requires s < 32, g1 <= g2,
    ensures g1 >> s <= g2 >> s,
{
    assert(g1 >> s <= g2 >> s) by (bit_vector) requires s < 32, g1 <= g2;
}

/// The shift `s` and number of buckets for `cg` group ids and `workers` workers: at most `workers` buckets.
pub fn bucket_params(cg: usize, workers: usize) -> (r: (u32, usize))
    requires 1 <= cg <= GID_LIMIT, 1 <= workers,
    ensures
        r.0 < 32, 1 <= r.1 <= workers,
        r.1 as int == ((cg - 1) as u64 >> r.0 as u64) + 1,
        forall|g: int| 0 <= g < cg ==> #[trigger] bucket(g, r.0 as int) < r.1,
{
    let top = (cg - 1) as u64;
    let mut s: u32 = 0;
    while s < 26 && (top >> (s as u64)) >= workers as u64
        invariant s <= 26, top < 0x400_0000,
        decreases 26 - s,
    {
        proof { lemma_shift_mono(0, top, s as u64); }
        s = s + 1;
    }
    proof {
        if s == 26 {
            assert(top >> 26u64 == 0) by (bit_vector) requires top < 0x400_0000;
        }
    }
    proof {
        let x = top >> (s as u64);
        assert(x <= top) by (bit_vector) requires x == top >> (s as u64), (s as u64) < 32;
    }
    let nb = ((top >> (s as u64)) + 1) as usize;
    proof {
        assert forall|g: int| 0 <= g < cg implies #[trigger] bucket(g, s as int) < nb by {
            lemma_shift_mono(g as u64, top, s as u64);
        }
    }
    (s, nb)
}

// ------------------------------------------------------------------------------------------------ part pass

/// The inputs shared by all part tasks.
pub open spec fn shared_ok(c: Cols, l: usize, szl: Seq<i64>, bd: TextDict, td: TextDict, bskip: Seq<bool>, tskip: Seq<bool>,
    bshift: u32, nbk: usize, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& cols_ok(c, sv) && stores_wf(sv)
    &&& c.np < 0x1_0000_0000 && c.np * 64 <= usize::MAX
    &&& l >= 1 && c.nq == l * c.np
    &&& bd.wf() && td.wf()
    &&& sizes_ok(szl, ps)
    &&& flags_ok(bd.keys(), td.keys(), bskip, tskip, ps)
    &&& buckets_ok(bd.keys(), td.keys(), szl, bshift as int, nbk as int)
    &&& 1 <= nbk <= 64
}

/// Task `t` has the shared inputs and range `rs[t]`.
pub open spec fn ctx_is(x: PartCtx, lo: usize, hi: usize, c: Cols, l: usize, szl: Seq<i64>, bd: TextDict, td: TextDict,
    bskip: Seq<bool>, tskip: Seq<bool>, bshift: u32, nbk: usize, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& x.lo == lo && x.hi == hi && x.c == c && x.l == l && x.szl@ == szl
    &&& *x.bdict == bd && *x.tdict == td && x.bskip@ == bskip && x.tskip@ == tskip
    &&& x.bshift == bshift && x.nb == nbk && x.sv@ == sv && x.ps@ == ps
}

/// A copy of `v`.
pub fn copy_i64(v: &Vec<i64>) -> (r: Vec<i64>)
    ensures r@ == v@,
{
    let mut r: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v@.len(), r@ == v@.subrange(0, i as int),
        decreases v@.len() - i,
    {
        r.push(v[i]);
        i = i + 1;
        proof { assert(r@ =~= v@.subrange(0, i as int)); }
    }
    proof { assert(v@.subrange(0, v@.len() as int) =~= v@); }
    r
}

/// A supplier output of rows `lo..hi`.
pub open spec fn sup_out_ok(so: Option<SuppOut>, lo: int, hi: int, sv: StoresView) -> bool {
    so matches Some(o) && supp_post(lo, hi, sv, o)
}

/// Part task `t` carries the supplier task of range `rss[t]` exactly when the passes are merged and `t < rss.len()`.
pub open spec fn sup_is(st: Option<SuppTask>, t: int, rss: Seq<(usize, usize)>, merged: bool, sv: StoresView) -> bool {
    if merged && t < rss.len() {
        st matches Some(x) && x.lo == rss[t].0 && x.hi == rss[t].1 && x.sv@ == sv
    } else {
        st is None
    }
}

/// The part tasks over the ranges `rs`.
fn part_tasks(c: &Cols, l: usize, szl: &Vec<i64>, smask: u64, sslot: &Vec<u8>, bd: &Arc<TextDict>, td: &Arc<TextDict>,
    bc: &Arc<WordCache>, tc: &Arc<WordCache>,
    bskip: &Arc<Vec<bool>>, tskip: &Arc<Vec<bool>>, bshift: u32, nbk: usize, rs: &Vec<(usize, usize)>,
    rss: &Vec<(usize, usize)>, merged: bool, Ghost(sv): Ghost<StoresView>,
    Ghost(ps): Ghost<Seq<Literal>>) -> (tasks: Vec<PartTask>)
    requires
        shared_ok(*c, l, szl@, **bd, **td, bskip@, tskip@, bshift, nbk, sv, ps), mask_ok(smask, sslot@, szl@),
        bc.wf(bd.keys()), tc.wf(td.keys()),
        covers(rs@, c.np as int), merged ==> covers(rss@, c.ns as int) && rss@.len() <= rs@.len(),
    ensures
        tasks@.len() == rs@.len(),
        forall|t: int| 0 <= t < tasks@.len() ==> #[trigger] tasks@[t].pre(),
        forall|t: int| 0 <= t < tasks@.len() ==> sup_is((#[trigger] tasks@[t]).sup, t, rss@, merged, sv),
        forall|t: int| 0 <= t < tasks@.len() ==> ctx_is((#[trigger] tasks@[t]).ctx, rs@[t].0, rs@[t].1, *c, l, szl@, **bd, **td,
            bskip@, tskip@, bshift, nbk, sv, ps),
{
    let mut tasks: Vec<PartTask> = Vec::new();
    let mut t: usize = 0;
    while t < rs.len()
        invariant
            shared_ok(*c, l, szl@, **bd, **td, bskip@, tskip@, bshift, nbk, sv, ps), covers(rs@, c.np as int),
            mask_ok(smask, sslot@, szl@), bc.wf(bd.keys()), tc.wf(td.keys()),
            t <= rs@.len(), tasks@.len() == t,
            forall|j: int| 0 <= j < t ==> #[trigger] tasks@[j].pre(),
            forall|j: int| 0 <= j < t ==> ctx_is((#[trigger] tasks@[j]).ctx, rs@[j].0, rs@[j].1, *c, l, szl@, **bd, **td,
                bskip@, tskip@, bshift, nbk, sv, ps),
            merged ==> covers(rss@, c.ns as int) && rss@.len() <= rs@.len(),
            forall|j: int| 0 <= j < t ==> sup_is((#[trigger] tasks@[j]).sup, j, rss@, merged, sv),
        decreases rs@.len() - t,
    {
        let (lo, hi) = rs[t];
        proof {
            lemma_in_bounds(rs@, c.np as int, t as int);
            assert(nbk * (hi - lo) <= 64 * c.np) by (nonlinear_arith) requires nbk <= 64, hi - lo <= c.np;
        }
        let ctx = PartCtx {
            lo, hi, c: *c, l, szl: copy_i64(szl), smask, sslot: copy_u8(sslot), bdict: bd.clone(), tdict: td.clone(), bcache: bc.clone(), tcache: tc.clone(), bskip: bskip.clone(), tskip: tskip.clone(),
            bshift, nb: nbk, sv: Ghost(sv), ps: Ghost(ps),
        };
        let n = nbk * (hi - lo);
        let buf: Vec<u64> = vec![0u64; big(n)];
        let boff: Vec<usize> = vec![0usize; nbk];
        proof {
            assert forall|b: int| 0 <= b < nbk implies #[trigger] boff@[b] == 0 by {}
        }
        let cand: Vec<u32> = vec![0u32; big4(hi - lo)];
        let sup = if merged && t < rss.len() {
            proof { lemma_in_bounds(rss@, c.ns as int, t as int); }
            let (slo, shi) = rss[t];
            Some(make_supp_task(c, slo, shi, Ghost(sv)))
        } else {
            None
        };
        let task = PartTask { ctx, buf, boff, cand, sup };
        proof {
            assert(ctx_ok(task.ctx));
        }
        tasks.push(task);
        proof {
            assert forall|j: int| 0 <= j < t + 1 implies #[trigger] tasks@[j].pre() by {
                if j == t { assert(tasks@[j] == task); }
            }
        }
        t = t + 1;
    }
    tasks
}

/// The part pass: its tasks' contexts and outputs.
pub fn run_parts(c: &Cols, l: usize, szl: &Vec<i64>, smask: u64, sslot: &Vec<u8>, bd: &Arc<TextDict>, td: &Arc<TextDict>,
    bc: &Arc<WordCache>, tc: &Arc<WordCache>,
    bskip: &Arc<Vec<bool>>, tskip: &Arc<Vec<bool>>, bshift: u32, nbk: usize, rs: &Vec<(usize, usize)>,
    rss: &Vec<(usize, usize)>, merged: bool, dispatch: &mut Dispatch,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: Result<(Vec<PartOut>, Ghost<Seq<PartCtx>>), WorkerFailure>)
    requires
        shared_ok(*c, l, szl@, **bd, **td, bskip@, tskip@, bshift, nbk, sv, ps), mask_ok(smask, sslot@, szl@),
        bc.wf(bd.keys()), tc.wf(td.keys()),
        covers(rs@, c.np as int), rs@.len() <= MAX_WORKERS, merged ==> covers(rss@, c.ns as int) && rss@.len() <= rs@.len(),
    ensures
        r matches Ok((outs, ctxs)) ==> outs@.len() == rs@.len() && ctxs@.len() == rs@.len()
            && (forall|t: int| 0 <= t < rs@.len() ==> #[trigger] part_post(ctxs@[t], outs@[t]))
            && (forall|t: int| 0 <= t < rs@.len() ==> ctx_is(#[trigger] ctxs@[t], rs@[t].0, rs@[t].1, *c, l, szl@, **bd, **td,
                bskip@, tskip@, bshift, nbk, sv, ps))
            && (merged ==> forall|t: int| 0 <= t < rss@.len() ==> sup_out_ok((#[trigger] outs@[t]).sup, rss@[t].0 as int, rss@[t].1 as int, sv)),
{
    let tasks = part_tasks(c, l, szl, smask, sslot, bd, td, bc, tc, bskip, tskip, bshift, nbk, rs, rss, merged, Ghost(sv), Ghost(ps));
    let ghost tv = tasks@;
    let ghost ctxs = Seq::new(tv.len(), |t: int| tv[t].ctx);
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    proof {
        assert forall|t: int| 0 <= t < rs@.len() implies #[trigger] part_post(ctxs[t], outs@[t]) by {
            assert(tv[t].post(outs@[t]));
        }
        assert forall|t: int| 0 <= t < rs@.len() implies ctx_is(#[trigger] ctxs[t], rs@[t].0, rs@[t].1, *c, l, szl@, **bd, **td,
            bskip@, tskip@, bshift, nbk, sv, ps) by {
            assert(ctx_is(tv[t].ctx, rs@[t].0, rs@[t].1, *c, l, szl@, **bd, **td, bskip@, tskip@, bshift, nbk, sv, ps));
        }
        if merged {
            assert forall|t: int| 0 <= t < rss@.len() implies sup_out_ok((#[trigger] outs@[t]).sup, rss@[t].0 as int, rss@[t].1 as int, sv) by {
                assert(tv[t].post(outs@[t]));
                assert(sup_is(tv[t].sup, t, rss@, merged, sv));
            }
        }
    }
    Ok((outs, Ghost(ctxs)))
}

/// The supplier pass's result from the merged part tasks' outputs.
fn supp_from_parts(c: &Cols, outs: &Vec<PartOut>, rss: &Vec<(usize, usize)>, Ghost(sv): Ghost<StoresView>) -> (r: SuppResult)
    requires
        cols_ok(*c, sv), covers(rss@, c.ns as int), rss@.len() <= outs@.len(),
        forall|t: int| 0 <= t < rss@.len() ==> sup_out_ok((#[trigger] outs@[t]).sup, rss@[t].0 as int, rss@[t].1 as int, sv),
    ensures supp_result_ok(r, sv),
{
    let mut souts: Vec<&SuppOut> = Vec::new();
    let mut t: usize = 0;
    while t < rss.len()
        invariant
            t <= rss@.len(), rss@.len() <= outs@.len(), souts@.len() == t,
            forall|x: int| 0 <= x < rss@.len() ==> sup_out_ok((#[trigger] outs@[x]).sup, rss@[x].0 as int, rss@[x].1 as int, sv),
            forall|j: int| 0 <= j < t ==> #[trigger] supp_post(rss@[j].0 as int, rss@[j].1 as int, sv, *souts@[j]),
        decreases rss@.len() - t,
    {
        proof { assert(sup_out_ok(outs@[t as int].sup, rss@[t as int].0 as int, rss@[t as int].1 as int, sv)); }
        match &outs[t].sup {
            Some(o) => { souts.push(o); },
            None => { proof { assert(false); } },
        }
        t = t + 1;
    }
    supp_merge(c, &souts, rss, Ghost(sv))
}

// ------------------------------------------------------------------------------------------------ checks

/// Every part task saw the layout and no dictionary miss.
pub fn parts_clean(outs: &Vec<PartOut>) -> (r: bool)
    ensures r == forall|t: int| 0 <= t < outs@.len() ==> (#[trigger] outs@[t]).layout_ok && outs@[t].misses == 0,
{
    let mut t: usize = 0;
    while t < outs.len()
        invariant t <= outs@.len(), forall|j: int| 0 <= j < t ==> (#[trigger] outs@[j]).layout_ok && outs@[j].misses == 0,
        decreases outs@.len() - t,
    {
        if !outs[t].layout_ok || outs[t].misses != 0 {
            return false;
        }
        t = t + 1;
    }
    true
}

/// The facts of a clean part pass over ranges `rs` covering the part rows.
pub open spec fn pass_ok(outs: Seq<PartOut>, ctxs: Seq<PartCtx>, rs: Seq<(usize, usize)>, c: Cols, l: usize, szl: Seq<i64>,
    bd: TextDict, td: TextDict, bskip: Seq<bool>, tskip: Seq<bool>, bshift: u32, nbk: usize, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& covers(rs, c.np as int) && outs.len() == rs.len() && ctxs.len() == rs.len()
    &&& forall|t: int| 0 <= t < rs.len() ==> #[trigger] part_post(ctxs[t], outs[t])
    &&& forall|t: int| 0 <= t < rs.len() ==> ctx_is(#[trigger] ctxs[t], rs[t].0, rs[t].1, c, l, szl, bd, td, bskip, tskip, bshift, nbk, sv, ps)
    &&& forall|t: int| 0 <= t < rs.len() ==> (#[trigger] outs[t]).layout_ok && outs[t].misses == 0
}

/// One clean part task: the layout and complete dictionaries on its rows.
proof fn lemma_task_clean(x: PartCtx, o: PartOut, a: int)
    requires part_post(x, o), o.layout_ok, o.misses == 0, x.lo <= a < x.hi,
    ensures
        forall|i: int| 0 <= i < x.l ==> #[trigger] ps_pkeys(x.sv@)[x.l * a + i] == p_keys(x.sv@)[a],
        !missed(x.bdict.keys(), x.tdict.keys(), x.sv@, x.ps@, a),
{
    assert(post_layout(x, o) && post_misses(x, o));
}

/// A clean pass shows the layout and complete dictionaries.
pub proof fn lemma_pass_layout(outs: Seq<PartOut>, ctxs: Seq<PartCtx>, rs: Seq<(usize, usize)>, c: Cols, l: usize, szl: Seq<i64>,
    bd: TextDict, td: TextDict, bskip: Seq<bool>, tskip: Seq<bool>, bshift: u32, nbk: usize, sv: StoresView, ps: Seq<Literal>)
    requires
        shared_ok(c, l, szl, bd, td, bskip, tskip, bshift, nbk, sv, ps),
        pass_ok(outs, ctxs, rs, c, l, szl, bd, td, bskip, tskip, bshift, nbk, sv, ps),
    ensures layout(sv, l as int), no_miss(bd.keys(), td.keys(), sv, ps),
{
    hide(part_post);
    assert forall|a: int, i: int| 0 <= a < part_n(sv) && 0 <= i < l implies #[trigger] ps_pkeys(sv)[l * a + i] == p_keys(sv)[a] by {
        lemma_covered(rs, c.np as int, a);
        let t = choose|t: int| 0 <= t < rs.len() && rs[t].0 <= a < #[trigger] rs[t].1;
        assert(ctx_is(ctxs[t], rs[t].0, rs[t].1, c, l, szl, bd, td, bskip, tskip, bshift, nbk, sv, ps));
        assert(part_post(ctxs[t], outs[t]));
        assert(outs[t].layout_ok && outs[t].misses == 0);
        lemma_task_clean(ctxs[t], outs[t], a);
        assert(ps_pkeys(ctxs[t].sv@)[ctxs[t].l * a + i] == p_keys(ctxs[t].sv@)[a]);
    }
    assert forall|a: int| 0 <= a < part_n(sv) implies !#[trigger] missed(bd.keys(), td.keys(), sv, ps, a) by {
        lemma_covered(rs, c.np as int, a);
        let t = choose|t: int| 0 <= t < rs.len() && rs[t].0 <= a < #[trigger] rs[t].1;
        assert(ctx_is(ctxs[t], rs[t].0, rs[t].1, c, l, szl, bd, td, bskip, tskip, bshift, nbk, sv, ps));
        assert(part_post(ctxs[t], outs[t]));
        assert(outs[t].layout_ok && outs[t].misses == 0);
        lemma_task_clean(ctxs[t], outs[t], a);
    }
}

// ------------------------------------------------------------------------------------------------ excluded keys

/// Bit `d` is set exactly for the offsets of the keys `ek[..n]`.
pub open spec fn bits_are(eb: Seq<u64>, ek: Seq<i64>, n: int, smin: int) -> bool {
    forall|d: int| #[trigger] in_bits(eb, d) ==> (bit_at(eb, d) <==> exists|x: int| 0 <= x < n && ek[x] - smin == d)
}

/// The bit set of the offsets `k - smin` of the keys `ek` (`nw` words).
pub fn excl_bits(ek: &Vec<i64>, smin: i64, nw: usize) -> (eb: Vec<u64>)
    requires forall|x: int| 0 <= x < ek@.len() ==> smin <= #[trigger] ek@[x] && (ek@[x] - smin) / 64 < nw,
    ensures eb@.len() == nw, bits_are(eb@, ek@, ek@.len() as int, smin as int),
{
    let mut eb: Vec<u64> = vec![0u64; nw];
    proof {
        assert forall|d: int| #[trigger] in_bits(eb@, d) implies (bit_at(eb@, d) <==> exists|x: int| 0 <= x < 0 && ek@[x] - smin == d) by {
            let w = eb@[d / 64];
            assert(w == 0u64);
            let sh = (d % 64) as u64;
            assert((w >> sh) & 1u64 == 0u64) by (bit_vector) requires w == 0u64;
        }
    }
    let mut i: usize = 0;
    while i < ek.len()
        invariant
            i <= ek@.len(), eb@.len() == nw,
            forall|x: int| 0 <= x < ek@.len() ==> smin <= #[trigger] ek@[x] && (ek@[x] - smin) / 64 < nw,
            bits_are(eb@, ek@, i as int, smin as int),
        decreases ek@.len() - i,
    {
        let k = ek[i];
        let o = (k as i128 - smin as i128) as u64;
        proof { assert(in_bits(eb@, o as int)); }
        let ghost e0 = eb@;
        let _ = test_set(&mut eb, o);
        proof {
            assert forall|d: int| #[trigger] in_bits(eb@, d) implies (bit_at(eb@, d) <==> exists|x: int| 0 <= x < i + 1 && ek@[x] - smin == d) by {
                assert(in_bits(e0, d));
                if d == o as int {
                    assert(ek@[i as int] - smin == d);
                } else {
                    assert(bit_at(eb@, d) == bit_at(e0, d));
                    if exists|x: int| 0 <= x < i + 1 && ek@[x] - smin == d {
                        let x = choose|x: int| 0 <= x < i + 1 && ek@[x] - smin == d;
                        assert(x != i);
                    }
                }
            }
        }
        i = i + 1;
    }
    eb
}

/// The bit set of the excluded keys is exact on the supplier keys of partsupp.
pub proof fn lemma_excl_ok(sv: StoresView, res: SuppResult, eb: Seq<u64>, nw: int)
    requires
        stores_wf(sv), keys_ok(sv), supp_result_ok(res, sv),
        nw == eb.len(), (res.smax - res.smin) / 64 < nw,
        bits_are(eb, res.ekeys@, res.ekeys@.len() as int, res.smin as int),
    ensures excl_ok(sv, res.smin as int, eb),
{
    let smin = res.smin as int;
    assert forall|c: int| 0 <= c < ps_n(sv) implies 0 <= #[trigger] ps_skeys(sv)[c] - smin && in_bits(eb, ps_skeys(sv)[c] - smin)
        && (bit_at(eb, ps_skeys(sv)[c] - smin) == excluded(sv, ps_skeys(sv)[c] as int)) by {
        let k = ps_skeys(sv)[c] as int;
        assert(is_supplier(sv, k));
        let b = choose|b: int| 0 <= b < supp_n(sv) && s_keys(sv)[b] == k;
        assert(res.smin <= s_keys(sv)[b] <= res.smax);
        let d = k - smin;
        assert(d / 64 <= (res.smax - res.smin) / 64) by {
            vstd::arithmetic::div_mod::lemma_div_is_ordered(d, res.smax - res.smin, 64);
        }
        assert(in_bits(eb, d));
        assert(has_key(res.ekeys@, k) == excluded(sv, k));
        if bit_at(eb, d) {
            let x = choose|x: int| 0 <= x < res.ekeys@.len() && res.ekeys@[x] - smin == d;
            assert(res.ekeys@[x] == k);
            assert(has_key(res.ekeys@, k));
        }
        if has_key(res.ekeys@, k) {
            let x = choose|x: int| 0 <= x < res.ekeys@.len() && res.ekeys@[x] == k;
            assert(res.ekeys@[x] - smin == d);
        }
    }
}

// ------------------------------------------------------------------------------------------------ gathered entries

/// An entry of the gathered entries of bucket `b` comes from some task's region.
pub proof fn lemma_gathered_index(outs: Seq<PartOut>, b: int, w: int, i: int)
    requires 0 <= w <= outs.len(), forall|x: int| 0 <= x < w ==> #[trigger] region_fits(outs[x], b),
        0 <= i < gathered(outs, b, w).len(),
    ensures exists|x: int, y: int| 0 <= x < w && 0 <= y < outs[x].boff@[b]
        && gathered(outs, b, w)[i] == #[trigger] outs[x].buf@[b * outs[x].cap + y],
    decreases w,
{
    let p = gathered(outs, b, w - 1);
    let o = outs[w - 1];
    assert(region_fits(o, b));
    assert(gathered(outs, b, w) == p + region_seq(o, b));
    if i < p.len() {
        lemma_gathered_index(outs, b, w - 1, i);
        let (x, y) = choose|x: int, y: int| 0 <= x < w - 1 && 0 <= y < outs[x].boff@[b]
            && p[i] == #[trigger] outs[x].buf@[b * outs[x].cap + y];
        assert(gathered(outs, b, w)[i] == outs[x].buf@[b * outs[x].cap + y]);
    } else {
        let y = i - p.len();
        assert(0 <= b * o.cap) by (nonlinear_arith) requires b >= 0, o.cap >= 0;
        assert(region_seq(o, b)[y] == o.buf@[b * o.cap + y]);
        assert(gathered(outs, b, w)[i] == outs[w - 1].buf@[b * outs[w - 1].cap + y]);
    }
}

/// Every region entry is among the gathered entries.
pub proof fn lemma_gathered_contains(outs: Seq<PartOut>, b: int, w: int, x: int, y: int)
    requires 0 <= w <= outs.len(), forall|z: int| 0 <= z < w ==> #[trigger] region_fits(outs[z], b),
        0 <= x < w, 0 <= y < outs[x].boff@[b],
    ensures gathered(outs, b, w).contains(outs[x].buf@[b * outs[x].cap + y]),
    decreases w,
{
    let p = gathered(outs, b, w - 1);
    let o = outs[w - 1];
    assert(region_fits(o, b));
    assert(gathered(outs, b, w) == p + region_seq(o, b));
    if x < w - 1 {
        lemma_gathered_contains(outs, b, w - 1, x, y);
        let i = choose|i: int| 0 <= i < p.len() && p[i] == outs[x].buf@[b * outs[x].cap + y];
        assert(gathered(outs, b, w)[i] == p[i]);
    } else {
        assert(0 <= b * o.cap) by (nonlinear_arith) requires b >= 0, o.cap >= 0;
        assert(region_seq(o, b)[y] == o.buf@[b * o.cap + y]);
        assert(gathered(outs, b, w)[p.len() + y] == o.buf@[b * o.cap + y]);
    }
}

/// The values of key `k` are the values of the entries with key `k`.
pub proof fn lemma_kvals_has(es: Seq<u64>, base: int, k: int, v: u32)
    ensures kvals(es, base, k).contains(v) <==> exists|i: int| 0 <= i < es.len() && ekey(es[i], base) == k && #[trigger] evalue(es[i]) == v,
    decreases es.len(),
{
    if es.len() > 0 {
        let d = es.drop_last();
        lemma_kvals_has(d, base, k, v);
        let kv = kvals(d, base, k);
        if kvals(es, base, k).contains(v) {
            if ekey(es.last(), base) == k && evalue(es.last()) == v {
                assert(evalue(es[es.len() - 1]) == v);
            } else {
                if ekey(es.last(), base) == k {
                    let j = choose|j: int| 0 <= j < kv.push(evalue(es.last())).len() && kv.push(evalue(es.last()))[j] == v;
                    assert(j < kv.len());
                    assert(kv.contains(v));
                }
                assert(kv.contains(v));
                let i = choose|i: int| 0 <= i < d.len() && ekey(d[i], base) == k && #[trigger] evalue(d[i]) == v;
                assert(es[i] == d[i]);
            }
        }
        if exists|i: int| 0 <= i < es.len() && ekey(es[i], base) == k && #[trigger] evalue(es[i]) == v {
            let i = choose|i: int| 0 <= i < es.len() && ekey(es[i], base) == k && #[trigger] evalue(es[i]) == v;
            if i == es.len() - 1 {
                assert(kvals(es, base, k) == kv.push(v));
                assert(kv.push(v)[kv.len() as int] == v);
            } else {
                assert(d[i] == es[i]);
                assert(kv.contains(v));
                let j = choose|j: int| 0 <= j < kv.len() && kv[j] == v;
                if ekey(es.last(), base) == k {
                    assert(kv.push(evalue(es.last()))[j] == v);
                }
            }
        }
    }
}

/// The value of an entry is its row; its key is its group id minus the base.
pub proof fn lemma_entry_parts(e: u64, base: int)
    ensures evalue(e) as int == entry_row(e), ekey(e, base) == entry_gid(e) - base, entry_row(e) < 0x1_0000_0000,
{
    assert((e & 0xFFFF_FFFFu64) <= 0xFFFF_FFFFu64) by (bit_vector);
}

// ------------------------------------------------------------------------------------------------ buckets of entries

/// One clean task's region of bucket `b`.
pub proof fn lemma_task_region(x: PartCtx, o: PartOut, b: int)
    requires part_post(x, o), o.misses == 0, 0 <= b < x.nb, x.lo < x.hi,
    ensures
        region_ok(o.buf@, (x.hi - x.lo) as int, o.boff@[b] as int, b, x.lo as int, x.hi as int, x.hi as int,
            x.bdict.keys(), x.tdict.keys(), x.szl@, x.bshift as int, x.sv@, x.ps@),
        region_fits(o, b),
{
    assert(post_regions(x, o));
    assert(region_ok(o.buf@, (x.hi - x.lo) as int, o.boff@[b] as int, b, x.lo as int, x.hi as int, x.hi as int,
            x.bdict.keys(), x.tdict.keys(), x.szl@, x.bshift as int, x.sv@, x.ps@));
    let cap = o.cap as int;
    assert(b * cap + cap <= x.nb * cap) by (nonlinear_arith) requires 0 <= b < x.nb, cap >= 0;
}

/// The clean pass's regions of bucket `b` fit, and their entries are entries of qualifying rows of bucket `b`.
pub proof fn lemma_bucket_entries(outs: Seq<PartOut>, ctxs: Seq<PartCtx>, rs: Seq<(usize, usize)>, c: Cols, l: usize, szl: Seq<i64>,
    bd: TextDict, td: TextDict, bskip: Seq<bool>, tskip: Seq<bool>, bshift: u32, nbk: usize, sv: StoresView, ps: Seq<Literal>, b: int)
    requires
        pass_ok(outs, ctxs, rs, c, l, szl, bd, td, bskip, tskip, bshift, nbk, sv, ps), 0 <= b < nbk,
    ensures
        forall|w: int| 0 <= w < outs.len() ==> #[trigger] region_fits(outs[w], b),
        forall|i: int| 0 <= i < gathered(outs, b, outs.len() as int).len() ==> #[trigger] entry_ok(gathered(outs, b, outs.len() as int)[i],
            b, 0, c.np as int, bd.keys(), td.keys(), szl, bshift as int, sv, ps),
{
    hide(part_post);
    assert forall|w: int| 0 <= w < outs.len() implies #[trigger] region_fits(outs[w], b) by {
        assert(ctx_is(ctxs[w], rs[w].0, rs[w].1, c, l, szl, bd, td, bskip, tskip, bshift, nbk, sv, ps));
        assert(part_post(ctxs[w], outs[w]) && outs[w].misses == 0);
        lemma_in_bounds(rs, c.np as int, w);
        lemma_task_region(ctxs[w], outs[w], b);
    }
    let g = gathered(outs, b, outs.len() as int);
    assert forall|i: int| 0 <= i < g.len() implies #[trigger] entry_ok(g[i], b, 0, c.np as int, bd.keys(), td.keys(), szl, bshift as int, sv, ps) by {
        lemma_gathered_index(outs, b, outs.len() as int, i);
        let (x, y) = choose|x: int, y: int| 0 <= x < outs.len() && 0 <= y < outs[x].boff@[b]
            && g[i] == #[trigger] outs[x].buf@[b * outs[x].cap + y];
        assert(ctx_is(ctxs[x], rs[x].0, rs[x].1, c, l, szl, bd, td, bskip, tskip, bshift, nbk, sv, ps));
        assert(part_post(ctxs[x], outs[x]) && outs[x].misses == 0);
        lemma_in_bounds(rs, c.np as int, x);
        lemma_task_region(ctxs[x], outs[x], b);
        let cap = (rs[x].1 - rs[x].0) as int;
        assert(outs[x].cap == cap) by { reveal(part_post); }
        assert(entry_ok(outs[x].buf@[b * cap + y], b, rs[x].0 as int, rs[x].1 as int, bd.keys(), td.keys(), szl, bshift as int, sv, ps));
    }
}

/// The facts of the fast path after a clean part pass.
pub open spec fn fast_pass(outs: Seq<PartOut>, ctxs: Seq<PartCtx>, rs: Seq<(usize, usize)>, c: Cols, l: usize, szl: Seq<i64>,
    bd: TextDict, td: TextDict, bskip: Seq<bool>, tskip: Seq<bool>, bshift: u32, nbk: usize, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& shared_ok(c, l, szl, bd, td, bskip, tskip, bshift, nbk, sv, ps)
    &&& pass_ok(outs, ctxs, rs, c, l, szl, bd, td, bskip, tskip, bshift, nbk, sv, ps)
    &&& fast_ok(sv, ps, bd.keys(), td.keys(), szl)
    &&& nbk as int == ((bd.keys().len() * td.keys().len() * szl.len() - 1) as u64 >> bshift as u64) + 1
}

/// The first group id of bucket `b`.
pub open spec fn glo_of(b: int, s: u32) -> int {
    ((b as u64) << (s as u64)) as int
}

/// The rows listed for group id `g` by the gathered entries of its bucket.
pub open spec fn grows(outs: Seq<PartOut>, s: u32, g: int) -> Seq<u32> {
    let b = bucket(g, s as int);
    kvals(gathered(outs, b, outs.len() as int), glo_of(b, s), g - glo_of(b, s))
}

/// The entries of bucket `b` have keys `0..ng` above its first id, and rows below `np`.
pub proof fn lemma_bucket_keys(outs: Seq<PartOut>, ctxs: Seq<PartCtx>, rs: Seq<(usize, usize)>, c: Cols, l: usize, szl: Seq<i64>,
    bd: TextDict, td: TextDict, bskip: Seq<bool>, tskip: Seq<bool>, bshift: u32, nbk: usize, sv: StoresView, ps: Seq<Literal>,
    b: int, ng: int)
    requires
        fast_pass(outs, ctxs, rs, c, l, szl, bd, td, bskip, tskip, bshift, nbk, sv, ps), 0 <= b < nbk,
        ng == if glo_of(b + 1, bshift) < bd.keys().len() * td.keys().len() * szl.len() { glo_of(b + 1, bshift) - glo_of(b, bshift) }
            else { bd.keys().len() * td.keys().len() * szl.len() - glo_of(b, bshift) },
    ensures
        keys_in(gathered(outs, b, outs.len() as int), glo_of(b, bshift), ng),
        forall|i: int| 0 <= i < gathered(outs, b, outs.len() as int).len() ==> #[trigger] evalue(gathered(outs, b, outs.len() as int)[i]) < c.np,
{
    let (kb, kt) = (bd.keys(), td.keys());
    let cg = kb.len() * kt.len() * szl.len();
    let g = gathered(outs, b, outs.len() as int);
    let glo = glo_of(b, bshift);
    lemma_bucket_entries(outs, ctxs, rs, c, l, szl, bd, td, bskip, tskip, bshift, nbk, sv, ps, b);
    assert forall|i: int| 0 <= i < g.len() implies 0 <= #[trigger] ekey(g[i], glo) < ng by {
        let e = g[i];
        assert(entry_ok(e, b, 0, c.np as int, kb, kt, szl, bshift as int, sv, ps));
        let a = entry_row(e);
        lemma_gid_row(sv, ps, kb, kt, szl, a);
        let gid = entry_gid(e);
        lemma_entry_parts(e, glo);
        assert(gid < 0x400_0000);
        lemma_bucket_range(gid as u64, b as u64, bshift as u64);
        let (bu, su) = (b as u64, bshift as u64);
        assert(((bu + 1) as u64) << su == (bu << su) + (1u64 << su)) by (bit_vector)
            requires su < 32, bu < 0x400_0000, (bu << su) < 0x400_0000;
    }
    assert forall|i: int| 0 <= i < g.len() implies #[trigger] evalue(g[i]) < c.np by {
        assert(entry_ok(g[i], b, 0, c.np as int, kb, kt, szl, bshift as int, sv, ps));
        lemma_entry_parts(g[i], glo);
    }
}

/// The rows listed for group id `g` are exactly its qualifying part rows.
pub proof fn lemma_group_rows(outs: Seq<PartOut>, ctxs: Seq<PartCtx>, rs: Seq<(usize, usize)>, c: Cols, l: usize, szl: Seq<i64>,
    bd: TextDict, td: TextDict, bskip: Seq<bool>, tskip: Seq<bool>, bshift: u32, nbk: usize, sv: StoresView, ps: Seq<Literal>, g: int)
    requires
        fast_pass(outs, ctxs, rs, c, l, szl, bd, td, bskip, tskip, bshift, nbk, sv, ps),
        0 <= g < bd.keys().len() * td.keys().len() * szl.len(),
    ensures group_rows_are(grows(outs, bshift, g), bd.keys(), td.keys(), szl, sv, ps, g),
{
    hide(part_post);
    let (kb, kt) = (bd.keys(), td.keys());
    let cg = kb.len() * kt.len() * szl.len();
    let b = bucket(g, bshift as int);
    let glo = glo_of(b, bshift);
    let w = outs.len() as int;
    let es = gathered(outs, b, w);
    let rows = grows(outs, bshift, g);
    let k = g - glo;
    assert(0 <= b < nbk);
    lemma_bucket_range(g as u64, b as u64, bshift as u64);
    lemma_bucket_entries(outs, ctxs, rs, c, l, szl, bd, td, bskip, tskip, bshift, nbk, sv, ps, b);
    assert forall|i: int| 0 <= i < rows.len() implies (#[trigger] rows[i]) < part_n(sv) by {
        assert(rows.contains(rows[i]));
        lemma_kvals_has(es, glo, k, rows[i]);
        let j = choose|j: int| 0 <= j < es.len() && ekey(es[j], glo) == k && #[trigger] evalue(es[j]) == rows[i];
        assert(entry_ok(es[j], b, 0, c.np as int, kb, kt, szl, bshift as int, sv, ps));
        lemma_entry_parts(es[j], glo);
    }
    assert forall|a: int| 0 <= a < part_n(sv) implies (#[trigger] rows.contains(a as u32)
        <==> part_ok(sv, ps, a) && gid_of(kb, kt, szl, sv, a) == g) by {
        lemma_kvals_has(es, glo, k, a as u32);
        if rows.contains(a as u32) {
            let j = choose|j: int| 0 <= j < es.len() && ekey(es[j], glo) == k && #[trigger] evalue(es[j]) == a as u32;
            assert(entry_ok(es[j], b, 0, c.np as int, kb, kt, szl, bshift as int, sv, ps));
            lemma_entry_parts(es[j], glo);
            assert(entry_row(es[j]) == a);
        }
        if part_ok(sv, ps, a) && gid_of(kb, kt, szl, sv, a) == g {
            lemma_covered(rs, c.np as int, a);
            let t = choose|t: int| 0 <= t < rs.len() && rs[t].0 <= a < #[trigger] rs[t].1;
            assert(ctx_is(ctxs[t], rs[t].0, rs[t].1, c, l, szl, bd, td, bskip, tskip, bshift, nbk, sv, ps));
            assert(part_post(ctxs[t], outs[t]) && outs[t].misses == 0);
            lemma_in_bounds(rs, c.np as int, t);
            lemma_task_region(ctxs[t], outs[t], b);
            let cap = (rs[t].1 - rs[t].0) as int;
            assert(outs[t].cap == cap) by { reveal(part_post); }
            assert(region_ok(outs[t].buf@, cap, outs[t].boff@[b] as int, b, rs[t].0 as int, rs[t].1 as int, rs[t].1 as int,
                kb, kt, szl, bshift as int, sv, ps));
            assert(bucket(gid_of(kb, kt, szl, sv, a), bshift as int) == b);
            let y = choose|y: int| 0 <= y < outs[t].boff@[b] && #[trigger] outs[t].buf@[b * cap + y] == entry(gid_of(kb, kt, szl, sv, a), a);
            lemma_gathered_contains(outs, b, w, t, y);
            let e = entry(g, a);
            assert(es.contains(e));
            let j = choose|j: int| 0 <= j < es.len() && es[j] == e;
            lemma_entry(g as u64, a as u64);
            lemma_entry_parts(e, glo);
            assert(evalue(es[j]) == a as u32);
        }
    }
}

// ------------------------------------------------------------------------------------------------ count pass

/// The number of group ids of bucket `b` (`cg` ids in all).
pub open spec fn ng_of(b: int, s: u32, cg: int) -> int {
    if glo_of(b + 1, s) < cg { glo_of(b + 1, s) - glo_of(b, s) } else { cg - glo_of(b, s) }
}

/// Bucket arithmetic: bucket `b` of `nbk` starts below `cg`; the next starts where it ends; the last ends at `cg`.
pub proof fn lemma_bucket_bounds(b: u64, s: u64, top: u64, nbk: u64)
    requires s < 32, top < 0x400_0000, nbk == (top >> s) + 1, b < nbk,
    ensures
        (b << s) <= top,
        ((b + 1) as u64) << s == (b << s) + (1u64 << s),
        b + 1 < nbk ==> (((b + 1) as u64) << s) <= top,
        b + 1 == nbk ==> top < (((b + 1) as u64) << s),
{
    assert((b << s) <= top) by (bit_vector) requires s < 32, top < 0x400_0000, b <= (top >> s);
    assert(((b + 1) as u64) << s == (b << s) + (1u64 << s)) by (bit_vector) requires s < 32, top < 0x400_0000, b <= (top >> s);
    if b + 1 < nbk {
        let b1 = (b + 1) as u64;
        assert((b1 << s) <= top) by (bit_vector) requires s < 32, top < 0x400_0000, b1 <= (top >> s);
    } else {
        let b1 = (b + 1) as u64;
        assert(top < (b1 << s)) by (bit_vector) requires s < 32, top < 0x400_0000, b1 == (top >> s) + 1;
    }
}

/// A copy of `v`.
pub fn copy_u64(v: &Vec<u64>) -> (r: Vec<u64>)
    ensures r@ == v@,
{
    let mut r: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v@.len(), r@ == v@.subrange(0, i as int),
        decreases v@.len() - i,
    {
        r.push(v[i]);
        i = i + 1;
        proof { assert(r@ =~= v@.subrange(0, i as int)); }
    }
    proof { assert(v@.subrange(0, v@.len() as int) =~= v@); }
    r
}

/// The number of gathered entries of bucket `b`.
fn gathered_len(outs: &Vec<PartOut>, b: usize, rs: &Vec<(usize, usize)>, Ghost(np): Ghost<int>) -> (m: usize)
    requires
        covers(rs@, np), outs@.len() == rs@.len(), np <= usize::MAX,
        forall|w: int| 0 <= w < outs@.len() ==> #[trigger] region_fits(outs@[w], b as int),
        forall|w: int| 0 <= w < outs@.len() ==> (#[trigger] outs@[w]).cap == rs@[w].1 - rs@[w].0,
    ensures m == gathered(outs@, b as int, outs@.len() as int).len(),
{
    let mut tot: usize = 0;
    let mut w: usize = 0;
    while w < outs.len()
        invariant
            covers(rs@, np), outs@.len() == rs@.len(), np <= usize::MAX, w <= outs@.len(),
            forall|x: int| 0 <= x < outs@.len() ==> #[trigger] region_fits(outs@[x], b as int),
            forall|x: int| 0 <= x < outs@.len() ==> (#[trigger] outs@[x]).cap == rs@[x].1 - rs@[x].0,
            tot == gathered(outs@, b as int, w as int).len(),
            w > 0 ==> tot <= rs@[w - 1].1, w == 0 ==> tot == 0,
        decreases outs@.len() - w,
    {
        proof {
            assert(region_fits(outs@[w as int], b as int));
            lemma_in_bounds(rs@, np, w as int);
            if w > 0 { assert(rs@[w - 1].1 == rs@[w as int].0); }
            assert(gathered(outs@, b as int, w + 1) == gathered(outs@, b as int, w as int) + region_seq(outs@[w as int], b as int));
        }
        tot = tot + outs[w].boff[b];
        w = w + 1;
    }
    tot
}

/// Count task `t` is bucket `b` over the clean pass `outs` and the bit set `eb`.
pub open spec fn cnt_is(t: CntTask, b: int, bshift: u32, cg: int, c: Cols, l: usize, smin: i64, outs: Seq<PartOut>, eb: Seq<u64>) -> bool {
    &&& t.b == b && t.glo as int == glo_of(b, bshift) && t.ng == ng_of(b, bshift, cg)
    &&& t.c == c && t.l == l && t.smin == smin && t.ins@ == outs && t.ebits@ == eb
}

/// The count tasks, one per bucket.
fn cnt_tasks(c: &Cols, l: usize, smin: i64, pouts: &Arc<Vec<PartOut>>, eb: &Arc<Vec<u64>>, cg: usize, bshift: u32, nbk: usize,
    rs: &Vec<(usize, usize)>, Ghost(ctxs): Ghost<Seq<PartCtx>>, Ghost(szl): Ghost<Seq<i64>>, Ghost(bd): Ghost<TextDict>,
    Ghost(td): Ghost<TextDict>, Ghost(bskip): Ghost<Seq<bool>>, Ghost(tskip): Ghost<Seq<bool>>, Ghost(sv): Ghost<StoresView>,
    Ghost(ps): Ghost<Seq<Literal>>) -> (tasks: Vec<CntTask>)
    requires
        fast_pass(pouts@, ctxs, rs@, *c, l, szl, bd, td, bskip, tskip, bshift, nbk, sv, ps),
        cg == bd.keys().len() * td.keys().len() * szl.len(), l <= 64,
        eb@.len() < 0x100_0000_0000_0000, excl_ok(sv, smin as int, eb@),
    ensures
        tasks@.len() == nbk,
        forall|b: int| 0 <= b < nbk ==> #[trigger] tasks@[b].pre(),
        forall|b: int| 0 <= b < nbk ==> cnt_is(#[trigger] tasks@[b], b, bshift, cg as int, *c, l, smin, pouts@, eb@),
{
    let ghost outs = pouts@;
    proof {
        let (x, y, z) = (bd.keys().len() as int, td.keys().len() as int, szl.len() as int);
        assert(x * y * z >= 1) by (nonlinear_arith) requires x >= 1, y >= 1, z >= 1;
    }
    let top = (cg - 1) as u64;
    let mut tasks: Vec<CntTask> = Vec::new();
    let mut b: usize = 0;
    while b < nbk
        invariant
            fast_pass(outs, ctxs, rs@, *c, l, szl, bd, td, bskip, tskip, bshift, nbk, sv, ps), outs == pouts@,
            cg == bd.keys().len() * td.keys().len() * szl.len(), l <= 64, top == cg - 1,
            eb@.len() < 0x100_0000_0000_0000, excl_ok(sv, smin as int, eb@),
            b <= nbk, tasks@.len() == b,
            forall|x: int| 0 <= x < b ==> #[trigger] tasks@[x].pre(),
            forall|x: int| 0 <= x < b ==> cnt_is(#[trigger] tasks@[x], x, bshift, cg as int, *c, l, smin, pouts@, eb@),
        decreases nbk - b,
    {
        proof {
            lemma_bucket_bounds(b as u64, bshift as u64, top, nbk as u64);
            lemma_bucket_entries(outs, ctxs, rs@, *c, l, szl, bd, td, bskip, tskip, bshift, nbk, sv, ps, b as int);
            assert forall|w: int| 0 <= w < outs.len() implies (#[trigger] outs[w]).cap == rs@[w].1 - rs@[w].0 by {
                assert(ctx_is(ctxs[w], rs@[w].0, rs@[w].1, *c, l, szl, bd, td, bskip, tskip, bshift, nbk, sv, ps));
                assert(part_post(ctxs[w], outs[w]));
            }
        }
        let glo = (b as u64) << (bshift as u64);
        let nxt = ((b + 1) as u64) << (bshift as u64);
        let ng = if nxt < cg as u64 { (nxt - glo) as usize } else { (cg as u64 - glo) as usize };
        proof {
            lemma_bucket_keys(outs, ctxs, rs@, *c, l, szl, bd, td, bskip, tskip, bshift, nbk, sv, ps, b as int, ng as int);
        }
        let m = gathered_len(pouts, b, rs, Ghost(c.np as int));
        let ent: Vec<u64> = vec![0u64; big(m)];
        let rows: Vec<u32> = vec![0u32; big4(m)];
        let ends: Vec<usize> = vec![0usize; ng + 1];
        let bits: Vec<u64> = vec![0u64; eb.len()];
        let scratch: Vec<i64> = vec![0i64; 256];
        let out: Vec<u64> = vec![0u64; ng];
        let t = CntTask {
            b, glo, ng, m, c: *c, l, smin, ins: pouts.clone(), ebits: eb.clone(), ent, ends, rows, bits, scratch, out, sv: Ghost(sv),
        };
        proof {
            assert forall|k: int| 0 <= k <= t.ng implies #[trigger] t.ends@[k] == 0 by {}
            assert forall|cc: int| 0 <= cc < t.c.nq implies 0 <= #[trigger] t.c.ps_sk@[cc] - t.smin && in_bits(t.ebits@, t.c.ps_sk@[cc] - t.smin) by {
                assert(0 <= ps_skeys(sv)[cc] - smin && in_bits(eb@, ps_skeys(sv)[cc] - smin));
            }
            assert(cnt_pre(t));
        }
        tasks.push(t);
        proof {
            assert forall|x: int| 0 <= x < b + 1 implies #[trigger] tasks@[x].pre() by {
                if x == b { assert(tasks@[x] == t); }
            }
        }
        b = b + 1;
    }
    tasks
}

/// The value expected for group id `g`: the number of distinct non-excluded supplier offsets of its rows.
pub open spec fn cval(sv: StoresView, l: usize, smin: i64, outs: Seq<PartOut>, bshift: u32, eb: Seq<u64>, g: int) -> nat {
    tset(ps_skeys(sv), l as int, smin as int, grows(outs, bshift, g), eb).len()
}

/// The count pass: the counts of all group ids, in id order.
pub fn run_counts(c: &Cols, l: usize, smin: i64, pouts: &Arc<Vec<PartOut>>, eb: &Arc<Vec<u64>>, cg: usize, bshift: u32, nbk: usize,
    rs: &Vec<(usize, usize)>, dispatch: &mut Dispatch, Ghost(ctxs): Ghost<Seq<PartCtx>>, Ghost(szl): Ghost<Seq<i64>>,
    Ghost(bd): Ghost<TextDict>, Ghost(td): Ghost<TextDict>, Ghost(bskip): Ghost<Seq<bool>>, Ghost(tskip): Ghost<Seq<bool>>,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Result<Vec<u64>, WorkerFailure>)
    requires
        fast_pass(pouts@, ctxs, rs@, *c, l, szl, bd, td, bskip, tskip, bshift, nbk, sv, ps),
        cg == bd.keys().len() * td.keys().len() * szl.len(), l <= 64, nbk <= MAX_WORKERS,
        eb@.len() < 0x100_0000_0000_0000, excl_ok(sv, smin as int, eb@),
    ensures
        r matches Ok(cnt) ==> cnt@.len() == cg
            && forall|g: int| 0 <= g < cg ==> #[trigger] cnt@[g] as int == cval(sv, l, smin, pouts@, bshift, eb@, g),
{
    proof {
        let (x, y, z) = (bd.keys().len() as int, td.keys().len() as int, szl.len() as int);
        assert(x * y * z >= 1) by (nonlinear_arith) requires x >= 1, y >= 1, z >= 1;
    }
    let tasks = cnt_tasks(c, l, smin, pouts, eb, cg, bshift, nbk, rs, Ghost(ctxs), Ghost(szl), Ghost(bd), Ghost(td),
        Ghost(bskip), Ghost(tskip), Ghost(sv), Ghost(ps));
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    let top = (cg - 1) as u64;
    let mut cnt: Vec<u64> = Vec::new();
    let mut b: usize = 0;
    proof {
        let su = bshift as u64;
        assert((0u64 << su) == 0u64) by (bit_vector) requires su < 32;
        assert(glo_of(0, bshift) == 0);
    }
    while b < nbk
        invariant
            fast_pass(pouts@, ctxs, rs@, *c, l, szl, bd, td, bskip, tskip, bshift, nbk, sv, ps),
            cg == bd.keys().len() * td.keys().len() * szl.len(), top == cg - 1, cg >= 1,
            outs@.len() == nbk, tv.len() == nbk, b <= nbk,
            forall|x: int| 0 <= x < nbk ==> #[trigger] tv[x].post(outs@[x]),
            forall|x: int| 0 <= x < nbk ==> cnt_is(#[trigger] tv[x], x, bshift, cg as int, *c, l, smin, pouts@, eb@),
            b < nbk ==> cnt@.len() == glo_of(b as int, bshift),
            b == nbk ==> cnt@.len() == cg,
            forall|g: int| 0 <= g < cnt@.len() ==> #[trigger] cnt@[g] as int == cval(sv, l, smin, pouts@, bshift, eb@, g),
        decreases nbk - b,
    {
        proof {
            lemma_bucket_bounds(b as u64, bshift as u64, top, nbk as u64);
            assert(tv[b as int].post(outs@[b as int]));
            assert(cnt_is(tv[b as int], b as int, bshift, cg as int, *c, l, smin, pouts@, eb@));
        }
        let glo = (b as u64) << (bshift as u64);
        let nxt = ((b + 1) as u64) << (bshift as u64);
        let ng = if nxt < cg as u64 { (nxt - glo) as usize } else { (cg as u64 - glo) as usize };
        let o = &outs[b];
        let mut k: usize = 0;
        while k < ng
            invariant
                cnt@.len() == glo + k, k <= ng, o@.len() == ng, glo < 0x400_0000, (glo + ng) <= cg, cg <= 0x400_0000,
                ng <= (1u64 << (bshift as u64)), bshift < 32, glo == (b as u64) << (bshift as u64), b < nbk, nbk <= 64,
                forall|kk: int| 0 <= kk < ng ==> #[trigger] o@[kk] == tset(c.ps_sk@, l as int, smin as int,
                    kvals(gathered(pouts@, b as int, pouts@.len() as int), glo as int, kk), eb@).len(),
                c.ps_sk@ == ps_skeys(sv),
                forall|g: int| 0 <= g < cnt@.len() ==> #[trigger] cnt@[g] as int == cval(sv, l, smin, pouts@, bshift, eb@, g),
            decreases ng - k,
        {
            let ghost g = (glo + k) as int;
            proof {
                lemma_bucket_of(g as u64, b as u64, bshift as u64);
                assert(bucket(g, bshift as int) == b);
                assert(glo_of(b as int, bshift) == glo);
            }
            cnt.push(o[k]);
            k = k + 1;
        }
        b = b + 1;
    }
    Ok(cnt)
}

// ------------------------------------------------------------------------------------------------ the fast path

/// The fast path's outcome: the answer columns, a fallback request (the data is outside the fast path's
/// assumptions), or a worker failure.
pub enum FastOut {
    Done(ResultColumns),
    Fallback,
    Failed(WorkerFailure),
}

/// No part type's `LIKE` fails under a plain pattern.
pub proof fn lemma_types_ok(sv: StoresView, ps: Seq<Literal>)
    requires plain_pattern(pat_lit(ps)),
    ensures forall|a: int| 0 <= a < part_n(sv) ==> #[trigger] type_res(sv, ps, a) is Ok,
{
    assert forall|a: int| 0 <= a < part_n(sv) implies #[trigger] type_res(sv, ps, a) is Ok by {
        lemma_like_plain(p_type(sv, a), pat_lit(ps));
    }
}

/// The counts are the statement's group counts.
proof fn lemma_counts(outs: Seq<PartOut>, ctxs: Seq<PartCtx>, rs: Seq<(usize, usize)>, c: Cols, l: usize, szl: Seq<i64>,
    bd: TextDict, td: TextDict, bskip: Seq<bool>, tskip: Seq<bool>, bshift: u32, nbk: usize, sv: StoresView, ps: Seq<Literal>,
    smin: i64, eb: Seq<u64>, cnt: Seq<u64>)
    requires
        fast_pass(outs, ctxs, rs, c, l, szl, bd, td, bskip, tskip, bshift, nbk, sv, ps),
        layout(sv, l as int), excl_ok(sv, smin as int, eb),
        cnt.len() == bd.keys().len() * td.keys().len() * szl.len(),
        forall|g: int| 0 <= g < cnt.len() ==> #[trigger] cnt[g] as int == cval(sv, l, smin, outs, bshift, eb, g),
    ensures
        forall|g: int| 0 <= g < cnt.len() ==> #[trigger] cnt[g] == gcount(sv, ps, grow(bd.keys(), td.keys(), szl, g))
            && (is_group(sv, ps, grow(bd.keys(), td.keys(), szl, g)) <==> cnt[g] > 0),
{
    assert forall|g: int| 0 <= g < cnt.len() implies #[trigger] cnt[g] == gcount(sv, ps, grow(bd.keys(), td.keys(), szl, g))
        && (is_group(sv, ps, grow(bd.keys(), td.keys(), szl, g)) <==> cnt[g] > 0) by {
        lemma_group_rows(outs, ctxs, rs, c, l, szl, bd, td, bskip, tskip, bshift, nbk, sv, ps, g);
        lemma_group_count(sv, ps, bd.keys(), td.keys(), szl, l as int, smin as int, eb, g, grows(outs, bshift, g));
        assert(cnt[g] as int == cval(sv, l, smin, outs, bshift, eb, g));
    }
}

/// Whether every count is below `2^32 - 1`.
fn counts_small(cnt: &Vec<u64>) -> (r: bool)
    ensures r == forall|g: int| 0 <= g < cnt@.len() ==> #[trigger] cnt@[g] < 0xFFFF_FFFF,
{
    let mut g: usize = 0;
    while g < cnt.len()
        invariant g <= cnt@.len(), forall|x: int| 0 <= x < g ==> #[trigger] cnt@[x] < 0xFFFF_FFFF,
        decreases cnt@.len() - g,
    {
        if cnt[g] >= 0xFFFF_FFFF {
            return false;
        }
        g = g + 1;
    }
    true
}

/// The keys of a dictionary are distinct texts.
proof fn lemma_dict_distinct(d: TextDict)
    requires d.wf(),
    ensures distinct_texts(d.keys()),
{
    d.lemma_keys_distinct();
    assert forall|i: int, j: int| 0 <= i < d.keys().len() && 0 <= j < d.keys().len() && i != j implies d.keys()[i] != d.keys()[j] by {
        if i > j { assert(d.keys()[j] != d.keys()[i]); }
    }
}

/// The fast path (see the module comments of `parts`, `counts` and `output`).
pub fn fast_answer(c: &Cols, params: &Params, szl: &Vec<i64>, workers: usize, dispatch: &mut Dispatch,
    Ghost(sv): Ghost<StoresView>) -> (r: FastOut)
    requires
        cols_ok(*c, sv), stores_wf(sv), keys_ok(sv), param_domain(params@), sizes_ok(szl@, params@),
        1 <= workers <= MAX_WORKERS, c.np >= 1, c.nq >= 1, c.ns >= 1, plain_pattern(pat_lit(params@)),
    ensures
        r matches FastOut::Done(cols) ==> columns_wf(cols) && forall|db: Database| #[trigger] bound_db(sv, db)
            ==> ordered_ok(db, query_spec_at(params@), Ok::<Relation, SqlError>(columns_view(cols))),
{
    let ghost ps = params@;
    proof { lemma_params(ps); }
    // The layout and sizes the fast path needs.
    if c.np as u64 >= 0x1_0000_0000u64 || c.np > usize::MAX / 64 {
        return FastOut::Fallback;
    }
    let l = c.nq / c.np;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(c.nq as int, c.np as int);
        vstd::arithmetic::div_mod::lemma_mod_bound(c.nq as int, c.np as int);
        assert(l * c.np <= c.nq) by (nonlinear_arith)
            requires c.nq == c.np * l + c.nq % c.np, 0 <= c.nq % c.np, l == c.nq / c.np;
    }
    if l == 0 || l > 64 || l * c.np != c.nq {
        return FastOut::Fallback;
    }
    proof {
        assert(c.np * 64 <= usize::MAX) by (nonlinear_arith) requires c.np <= usize::MAX / 64;
    }
    let pre = if c.np < 8192 { c.np } else { 8192 };
    let Dicts { bd, td, bskip, tskip } = build_dicts(c, params, pre, Ghost(sv));
    let nbr = bd.count();
    let nt = td.count();
    let ns = szl.len();
    if nbr == 0 || nt == 0 || nbr > GID_LIMIT || nt > GID_LIMIT {
        return FastOut::Fallback;
    }
    proof {
        assert((nbr as u64) * (nt as u64) <= 0x400_0000u64 * 0x400_0000u64) by (nonlinear_arith)
            requires nbr <= 0x400_0000, nt <= 0x400_0000;
        assert(ns <= 8);
    }
    let p2 = nbr as u64 * nt as u64;
    if p2 > GID_LIMIT as u64 {
        return FastOut::Fallback;
    }
    proof {
        assert(p2 * (ns as u64) <= 0x400_0000u64 * 8) by (nonlinear_arith) requires p2 <= 0x400_0000, ns <= 8;
    }
    let p3 = p2 * ns as u64;
    if p3 > GID_LIMIT as u64 {
        return FastOut::Fallback;
    }
    proof {
        assert(nbr * nt * ns == p3 as int && p3 >= 1) by (nonlinear_arith)
            requires p2 == nbr * nt, p3 == p2 * ns, nbr >= 1, nt >= 1, ns >= 1;
    }
    let cg = nbr * nt * ns;
    // At most 32 group buckets (count tasks): beyond that, spawning more threads costs the caller more than the
    // smaller buckets save.
    let (bshift, nbk) = bucket_params(cg, if workers > 32 { 32 } else { workers });
    let ghost (gbd, gtd) = (bd, td);
    proof {
        lemma_dict_distinct(bd);
        lemma_dict_distinct(td);
        assert(shared_ok(*c, l, szl@, bd, td, bskip@, tskip@, bshift, nbk, sv, ps));
    }
    let bc = Arc::new(build_cache(&bd));
    let tc = Arc::new(build_cache(&td));
    let bd = Arc::new(bd);
    let td = Arc::new(td);
    let bskip = Arc::new(bskip);
    let tskip = Arc::new(tskip);
    let (smask, sslot) = size_mask(szl);
    // Part ranges grow with the task index by up to 30% (the last task is spawned first).
    let rs = split_weighted(c.np, workers, 30);
    let rss = split_ranges(c.ns, workers);
    let merged = rss.len() <= rs.len();
    let (pouts, Ghost(ctxs)) = match run_parts(c, l, szl, smask, &sslot, &bd, &td, &bc, &tc, &bskip, &tskip, bshift, nbk, &rs,
        &rss, merged, dispatch, Ghost(sv), Ghost(ps)) {
        Ok(x) => x,
        Err(e) => return FastOut::Failed(e),
    };
    if !parts_clean(&pouts) {
        return FastOut::Fallback;
    }
    let supp = if merged {
        supp_from_parts(c, &pouts, &rss, Ghost(sv))
    } else {
        match supp_pass(c, Ghost(sv), workers, dispatch) {
            Ok(x) => x,
            Err(e) => return FastOut::Failed(e),
        }
    };
    proof {
        assert(pass_ok(pouts@, ctxs, rs@, *c, l, szl@, gbd, gtd, bskip@, tskip@, bshift, nbk, sv, ps));
        lemma_pass_layout(pouts@, ctxs, rs@, *c, l, szl@, gbd, gtd, bskip@, tskip@, bshift, nbk, sv, ps);
        assert(fast_ok(sv, ps, gbd.keys(), gtd.keys(), szl@));
        assert(fast_pass(pouts@, ctxs, rs@, *c, l, szl@, gbd, gtd, bskip@, tskip@, bshift, nbk, sv, ps));
    }
    // The bit set of the excluded supplier keys.
    let span = supp.smax as i128 - supp.smin as i128;
    if span < 0 || span >= 0x100_0000_0000 || span / 64 + 1 > usize::MAX as i128 {
        return FastOut::Fallback;
    }
    let nw = (span / 64 + 1) as usize;
    proof {
        assert forall|x: int| 0 <= x < supp.ekeys@.len() implies supp.smin <= #[trigger] supp.ekeys@[x] && (supp.ekeys@[x] - supp.smin) / 64 < nw by {
            assert(supp.smin <= supp.ekeys@[x] <= supp.smax);
            vstd::arithmetic::div_mod::lemma_div_is_ordered(supp.ekeys@[x] - supp.smin, span as int, 64);
        }
    }
    let eb = excl_bits(&supp.ekeys, supp.smin, nw);
    proof { lemma_excl_ok(sv, supp, eb@, nw as int); }
    let eb = Arc::new(eb);
    let pouts = Arc::new(pouts);
    let cnt = match run_counts(c, l, supp.smin, &pouts, &eb, cg, bshift, nbk, &rs, dispatch, Ghost(ctxs), Ghost(szl@), Ghost(gbd),
        Ghost(gtd), Ghost(bskip@), Ghost(tskip@), Ghost(sv), Ghost(ps)) {
        Ok(x) => x,
        Err(e) => return FastOut::Failed(e),
    };
    if !counts_small(&cnt) {
        return FastOut::Fallback;
    }
    let bl = bd.kbytes.len();
    let tl = td.kbytes.len();
    if bl > usize::MAX / cg || tl > usize::MAX / cg {
        return FastOut::Fallback;
    }
    proof {
        assert(cg * bl <= usize::MAX) by (nonlinear_arith) requires bl <= usize::MAX / cg, cg >= 1;
        assert(cg * tl <= usize::MAX) by (nonlinear_arith) requires tl <= usize::MAX / cg, cg >= 1;
        lemma_counts(pouts@, ctxs, rs@, *c, l, szl@, gbd, gtd, bskip@, tskip@, bshift, nbk, sv, ps, supp.smin, eb@, cnt@);
        assert(tables_ok(gbd.keys(), gtd.keys(), szl@, cnt@));
    }
    let cols = build_output(&bd, &td, szl, &cnt);
    proof {
        lemma_fast_rows(sv, ps, gbd.keys(), gtd.keys(), szl@, cnt@, columns_view(cols));
        lemma_types_ok(sv, ps);
        lemma_answer_rows(sv, ps, columns_view(cols));
    }
    FastOut::Done(cols)
}

} // verus!
