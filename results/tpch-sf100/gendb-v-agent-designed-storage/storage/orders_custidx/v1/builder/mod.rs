//! Builder of storage `orders_custidx` (a secondary index of orders on o_custkey) from storage `facts`.
//!
//! 1. `canonical_keys`: the o_custkey of every canonical orders row, from the stored rows of `facts` and their row
//!    map (stored row `s` is canonical row `map_at(s)`, a bijection, `src`).
//! 2. The key range `[lo, hi]`. A dense directory needs fewer than `u32::MAX` rows and a range of at most
//!    `4 n + 2^20` keys; otherwise the fallback mode stores the keys.
//! 3. Counting sort over `kmin = lo`: `count_keys` (rows per key), `prefix_offsets` (directory offsets: prefix sums of
//!    the counts), `scatter` (each row, in canonical order, into the next free slot of its key's range).
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::layout::{PartView, owned_parts_view};
use crate::gendb_entry::parallel::Dispatch;
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::gendb_entry::storage::{represents, stored_relations};
use crate::spec::value::{Database, Row, Val};
use crate::stores::orders_custidx::interface as I;
use crate::stores::facts::interface::common::colfmt as FC;

pub mod src;
pub mod count;
use src::*;
use count::*;

verus! {

/// The facts `canonical_keys` needs about the source columns (`src_ok` over slices).
pub open spec fn cols_ok(pc: Seq<u32>, pb: Seq<u64>, kc: Seq<u32>, kb: Seq<i64>, bsize: int, rel: Seq<Row>) -> bool {
    let n = rel.len() as int;
    &&& bsize >= 1
    &&& pc.len() == n && kc.len() == n
    &&& forall|s: int| 0 <= s < n ==> #[trigger] (s / bsize) < pb.len() && s / bsize < kb.len()
    &&& forall|s: int| 0 <= s < n ==> 0 <= #[trigger] map_at(pc, pb, bsize, s) < n
    &&& forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b ==>
            #[trigger] map_at(pc, pb, bsize, a) != #[trigger] map_at(pc, pb, bsize, b)
    &&& forall|r: int| 0 <= r < n ==> #[trigger] mapped(pc, pb, bsize, r)
    &&& forall|s: int| 0 <= s < n ==> {
            &&& i64::MIN <= #[trigger] key_at(kc, kb, bsize, s) <= i64::MAX
            &&& rel[map_at(pc, pb, bsize, s)][0] == Val::Int(key_at(kc, kb, bsize, s))
        }
}

/// The key of every canonical row: stored row `s` writes its key at its canonical row `map_at(s)`; the row map is
/// a bijection, so every canonical row is written exactly once.
fn canonical_keys(pc: &[u32], pb: &[u64], kc: &[u32], kb: &[i64], bsize: usize, n: usize, Ghost(rel): Ghost<Seq<Row>>)
    -> (keys: Vec<i64>)
    requires
        rel.len() == n,
        cols_ok(pc@, pb@, kc@, kb@, bsize as int, rel),
    ensures
        keys@.len() == n,
        forall|r: int| 0 <= r < n ==> #[trigger] rel[r][0] == Val::Int(keys@[r] as int),
{
    let ghost (pcv, pbv, kcv, kbv, b) = (pc@, pb@, kc@, kb@, bsize as int);
    let mut keys: Vec<i64> = vec![0i64; n];
    let mut s: usize = 0;
    while s < n
        invariant
            rel.len() == n,
            cols_ok(pcv, pbv, kcv, kbv, b, rel),
            pcv == pc@, pbv == pb@, kcv == kc@, kbv == kb@, b == bsize as int,
            s <= n,
            keys@.len() == n,
            forall|t: int| 0 <= t < s ==> #[trigger] keys@[map_at(pcv, pbv, b, t)] == key_at(kcv, kbv, b, t),
        decreases n - s,
    {
        let g = s / bsize;
        assert((s as int) / b < pbv.len() && (s as int) / b < kbv.len());
        assert(0 <= map_at(pcv, pbv, b, s as int) < n);
        let r = (pb[g] + pc[s] as u64) as usize;
        assert(i64::MIN <= key_at(kcv, kbv, b, s as int) <= i64::MAX);
        let key = kb[g] + kc[s] as i64;
        let ghost old_keys = keys@;
        keys[r] = key;
        proof {
            assert forall|t: int| 0 <= t < s + 1 implies #[trigger] keys@[map_at(pcv, pbv, b, t)] == key_at(kcv, kbv, b, t) by {
                if t < s {
                    assert(map_at(pcv, pbv, b, t) != map_at(pcv, pbv, b, s as int));
                    assert(keys@[map_at(pcv, pbv, b, t)] == old_keys[map_at(pcv, pbv, b, t)]);
                }
            }
        }
        s = s + 1;
    }
    proof {
        assert forall|r: int| 0 <= r < n implies #[trigger] rel[r][0] == Val::Int(keys@[r] as int) by {
            assert(mapped(pcv, pbv, b, r));
            let t = choose|t: int| 0 <= t < pcv.len() && #[trigger] map_at(pcv, pbv, b, t) == r;
            assert(keys@[map_at(pcv, pbv, b, t)] == key_at(kcv, kbv, b, t));
        }
    }
    keys
}

/// The smallest and largest key (`keys` non-empty).
fn key_range(keys: &Vec<i64>) -> (r: (i64, i64))
    requires keys@.len() > 0,
    ensures
        r.0 <= r.1,
        forall|i: int| 0 <= i < keys@.len() ==> r.0 <= #[trigger] keys@[i] <= r.1,
{
    let n = keys.len();
    let mut lo = keys[0];
    let mut hi = keys[0];
    let mut i: usize = 1;
    while i < n
        invariant
            n == keys@.len(),
            1 <= i <= n,
            lo <= hi,
            forall|q: int| 0 <= q < i ==> lo <= #[trigger] keys@[q] <= hi,
        decreases n - i,
    {
        let x = keys[i];
        if x < lo { lo = x; }
        if x > hi { hi = x; }
        i = i + 1;
    }
    (lo, hi)
}

/// Rows per key `kmin + e`, `e < k`.
fn count_keys(keys: &Vec<i64>, kmin: i64, k: usize) -> (cnt: Vec<u32>)
    requires
        keys@.len() < u32::MAX,
        forall|r: int| 0 <= r < keys@.len() ==> kmin <= #[trigger] keys@[r] < kmin + k,
    ensures
        cnt@.len() == k,
        forall|e: int| 0 <= e < k ==> #[trigger] cnt@[e] == cnt_int(keys@, kmin + e, keys@.len() as int),
        psum(cnt@, k as int) == keys@.len(),
{
    let n = keys.len();
    let mut cnt: Vec<u32> = vec![0u32; k];
    proof {
        lemma_psum_zero(cnt@, k as int);
    }
    let mut r: usize = 0;
    while r < n
        invariant
            n == keys@.len(),
            n < u32::MAX,
            forall|q: int| 0 <= q < n ==> kmin <= #[trigger] keys@[q] < kmin + k,
            r <= n,
            cnt@.len() == k,
            forall|e: int| 0 <= e < k ==> #[trigger] cnt@[e] == cnt_int(keys@, kmin + e, r as int),
            psum(cnt@, k as int) == r,
        decreases n - r,
    {
        let x = keys[r];
        assert(kmin <= x < kmin + k);
        let e = ((x as i128) - (kmin as i128)) as usize;
        proof {
            lemma_psum_elem(cnt@, e as int, k as int);
        }
        let c = cnt[e];
        let ghost old_cnt = cnt@;
        cnt[e] = c + 1;
        proof {
            lemma_psum_inc(old_cnt, e as int, k as int, (c + 1) as u32);
            assert(cnt@ == old_cnt.update(e as int, (c + 1) as u32));
            assert forall|f: int| 0 <= f < k implies #[trigger] cnt@[f] == cnt_int(keys@, kmin + f, r + 1) by {
                if f != e {
                    assert(keys@[r as int] != kmin + f);
                }
            }
        }
        r = r + 1;
    }
    cnt
}

/// Directory offsets: `offs[e] == psum(cnt, e)` for `e <= k`.
fn prefix_offsets(cnt: &Vec<u32>, k: usize, Ghost(n): Ghost<int>) -> (offs: Vec<u32>)
    requires
        k < usize::MAX,
        cnt@.len() == k,
        psum(cnt@, k as int) == n,
        n < u32::MAX,
    ensures
        offs@.len() == k + 1,
        forall|e: int| 0 <= e <= k ==> #[trigger] offs@[e] == psum(cnt@, e),
{
    let mut offs: Vec<u32> = Vec::with_capacity(k + 1);
    offs.push(0);
    let mut acc: u32 = 0;
    let mut e: usize = 0;
    while e < k
        invariant
            cnt@.len() == k,
            psum(cnt@, k as int) == n,
            n < u32::MAX,
            e <= k,
            offs@.len() == e + 1,
            acc as int == psum(cnt@, e as int),
            forall|f: int| 0 <= f <= e ==> #[trigger] offs@[f] == psum(cnt@, f),
        decreases k - e,
    {
        proof {
            lemma_psum_mono(cnt@, e as int + 1, k as int);
        }
        acc = acc + cnt[e];
        offs.push(acc);
        e = e + 1;
    }
    offs
}

/// Slot `j` lies in the filled part `[offs[e], cur[e])` of entry `e`.
pub open spec fn filled(offs: Seq<u32>, cur: Seq<u32>, e: int, j: int) -> bool {
    offs[e] <= j < cur[e]
}

/// Each row, in canonical order, into the next free slot of its key's range.
fn scatter(keys: &Vec<i64>, kmin: i64, k: usize, Ghost(cnt): Ghost<Seq<u32>>, offs: &Vec<u32>) -> (perm: Vec<u32>)
    requires
        keys@.len() < u32::MAX,
        forall|r: int| 0 <= r < keys@.len() ==> kmin <= #[trigger] keys@[r] < kmin + k,
        cnt.len() == k,
        forall|e: int| 0 <= e < k ==> #[trigger] cnt[e] == cnt_int(keys@, kmin + e, keys@.len() as int),
        psum(cnt, k as int) == keys@.len(),
        offs@.len() == k + 1,
        forall|e: int| 0 <= e <= k ==> #[trigger] offs@[e] == psum(cnt, e),
    ensures
        perm@.len() == keys@.len(),
        forall|e: int, j: int| 0 <= e < k && #[trigger] I::in_entry(offs@, e, j) ==>
            perm@[j] < keys@.len() && keys@[perm@[j] as int] == kmin + e,
        forall|r: int| 0 <= r < keys@.len() ==> #[trigger] I::listed(perm@, r),
{
    let n = keys.len();
    let mut cur: Vec<u32> = Vec::with_capacity(k);
    let mut e0: usize = 0;
    while e0 < k
        invariant
            e0 <= k,
            offs@.len() == k + 1,
            cur@.len() == e0,
            forall|f: int| 0 <= f < e0 ==> #[trigger] cur@[f] == offs@[f],
        decreases k - e0,
    {
        cur.push(offs[e0]);
        e0 = e0 + 1;
    }
    let mut perm: Vec<u32> = vec![0u32; n];
    let ghost mut pos: Seq<int> = Seq::empty();
    let mut r: usize = 0;
    while r < n
        invariant
            n == keys@.len(),
            n < u32::MAX,
            forall|q: int| 0 <= q < n ==> kmin <= #[trigger] keys@[q] < kmin + k,
            cnt.len() == k,
            forall|e: int| 0 <= e < k ==> #[trigger] cnt[e] == cnt_int(keys@, kmin + e, n as int),
            psum(cnt, k as int) == n,
            offs@.len() == k + 1,
            forall|e: int| 0 <= e <= k ==> #[trigger] offs@[e] == psum(cnt, e),
            r <= n,
            cur@.len() == k,
            perm@.len() == n,
            forall|e: int| 0 <= e < k ==> #[trigger] cur@[e] == offs@[e] + cnt_int(keys@, kmin + e, r as int),
            forall|e: int, j: int| 0 <= e < k && #[trigger] filled(offs@, cur@, e, j) ==>
                perm@[j] < r && keys@[perm@[j] as int] == kmin + e,
            pos.len() == r,
            forall|q: int| 0 <= q < r ==> {
                &&& #[trigger] filled(offs@, cur@, keys@[q] - kmin, pos[q])
                &&& perm@[pos[q]] == q
            },
        decreases n - r,
    {
        let x = keys[r];
        let e = ((x as i128) - (kmin as i128)) as usize;
        let ghost ei = e as int;
        proof {
            lemma_cnt_mono(keys@, kmin + ei, r as int + 1, n as int);
            lemma_psum_mono(cnt, ei + 1, k as int);
        }
        let w = cur[e];
        assert(w < offs@[ei + 1]);
        let ghost (old_perm, old_cur) = (perm@, cur@);
        perm[w as usize] = r as u32;
        cur[e] = w + 1;
        proof {
            // Entries other than `e` are disjoint from `[offs[e], offs[e + 1])`, which holds `w`.
            assert forall|f: int, j: int| 0 <= f < k && f != ei && #[trigger] filled(offs@, old_cur, f, j) implies j != w by {
                lemma_cnt_mono(keys@, kmin + f, r as int, n as int);
                if f < ei {
                    lemma_entries_ordered(cnt, f, ei);
                } else {
                    lemma_entries_ordered(cnt, ei, f);
                }
            }
            assert forall|f: int| 0 <= f < k implies #[trigger] cur@[f] == offs@[f] + cnt_int(keys@, kmin + f, r as int + 1) by {
                if f != ei {
                    assert(keys@[r as int] != kmin + f);
                }
            }
            assert forall|f: int, j: int| 0 <= f < k && #[trigger] filled(offs@, cur@, f, j) implies
                perm@[j] < r + 1 && keys@[perm@[j] as int] == kmin + f by {
                if f != ei {
                    assert(filled(offs@, old_cur, f, j));
                } else if j != w {
                    assert(filled(offs@, old_cur, f, j));
                }
            }
            let new_pos = pos.push(w as int);
            assert(offs@[ei] <= w);
            assert forall|q: int| 0 <= q < r + 1 implies {
                &&& #[trigger] filled(offs@, cur@, keys@[q] - kmin, new_pos[q])
                &&& perm@[new_pos[q]] == q
            } by {
                if q < r {
                    let f = keys@[q] - kmin;
                    assert(new_pos[q] == pos[q]);
                    assert(filled(offs@, old_cur, f, pos[q]));
                    assert(perm@[pos[q]] == old_perm[pos[q]]) by {
                        if f != ei {
                            assert(pos[q] != w);
                        } else {
                            assert(pos[q] < w);
                        }
                    }
                    assert(filled(offs@, cur@, f, pos[q]));
                } else {
                    assert(new_pos[q] == w);
                    assert(keys@[q] - kmin == ei);
                }
            }
            pos = new_pos;
        }
        r = r + 1;
    }
    proof {
        assert forall|e: int| 0 <= e < k implies #[trigger] cur@[e] == offs@[e + 1] by {
            assert(offs@[e + 1] == psum(cnt, e) + cnt[e]);
        }
        assert forall|e: int, j: int| 0 <= e < k && #[trigger] I::in_entry(offs@, e, j) implies
            perm@[j] < n && keys@[perm@[j] as int] == kmin + e by {
            assert(filled(offs@, cur@, e, j));
        }
        assert forall|q: int| 0 <= q < n implies #[trigger] I::listed(perm@, q) by {
            let f = keys@[q] - kmin;
            assert(filled(offs@, cur@, f, pos[q]));
            lemma_psum_mono(cnt, f + 1, k as int);
            assert(cur@[f] == offs@[f + 1]);
            assert(0 <= pos[q] < perm@.len());
        }
    }
    perm
}

/// The directory of `keys` over `kmin .. kmin + k` (all keys in range, fewer than `u32::MAX` rows).
fn build_directory(keys: &Vec<i64>, kmin: i64, k: usize, Ghost(rel): Ghost<Seq<Row>>) -> (r: (Vec<u32>, Vec<u32>))
    requires
        k < usize::MAX,
        keys@.len() < u32::MAX,
        rel.len() == keys@.len(),
        forall|q: int| 0 <= q < keys@.len() ==> kmin <= #[trigger] keys@[q] < kmin + k,
        forall|q: int| 0 <= q < rel.len() ==> #[trigger] rel[q][0] == Val::Int(keys@[q] as int),
    ensures
        r.0@.len() == k + 1,
        I::directory_ok(kmin as int, k as int, r.0@, r.1@, rel),
{
    let n = keys.len();
    let cnt = count_keys(keys, kmin, k);
    let offs = prefix_offsets(&cnt, k, Ghost(n as int));
    let perm = scatter(keys, kmin, k, Ghost(cnt@), &offs);
    proof {
        let (o, p) = (offs@, perm@);
        assert(o[0] == 0);
        assert forall|e: int| 0 <= e < k implies #[trigger] o[e] <= o[e + 1] by {
            assert(o[e + 1] == psum(cnt@, e) + cnt@[e]);
        }
        assert forall|e: int| 0 <= e < k implies #[trigger] o[e + 1] - o[e] == I::count_key(rel, kmin + e, n as int) by {
            assert(o[e + 1] == psum(cnt@, e) + cnt@[e]);
            lemma_cnt_rel(rel, keys@, kmin + e, n as int);
        }
        assert forall|e: int, j: int| 0 <= e < k && #[trigger] I::in_entry(o, e, j) implies
            p[j] < n && rel[p[j] as int][0] == Val::Int(kmin + e) by {
            assert(keys@[p[j] as int] == kmin + e);
        }
        assert forall|q: int| 0 <= q < n implies #[trigger] I::key_in_range(rel, kmin as int, k as int, q) by {
            assert(rel[q][0] == Val::Int(keys@[q] as int));
        }
    }
    (offs, perm)
}

/// Build the index parts `[META, OFFS, PERM, KEYS]`.
pub fn build(stores: &mut Stores, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        sources_ready(old(stores)@),
        1 <= workers <= crate::gendb_entry::parallel::MAX_WORKERS,
    ensures
        match r {
            Ok(p) => forall|db: Database| #[trigger] sources_bound(old(stores)@, db)
                ==> represents(storage_parts(old(stores)@, owned_parts_view(p@)), stored_relations(db)),
            Err(QueryError::WorkerFailed(_)) => true,
            Err(_) => false,
        },
{
    let ghost sv = stores@;
    let ghost db0 = choose|db: Database| #[trigger] sources_bound(sv, db);
    let ghost rel = stored_relations(db0)[0];
    proof {
        lemma_src(sv, db0);
        // Every database bound to the source has the same indexed relation (the parts determine it).
        assert forall|db: Database| #[trigger] sources_bound(sv, db) implies stored_relations(db)[0] == rel by {
            lemma_src(sv, db);
            lemma_same_rel(sv, db0, db);
        }
    }
    let n = stores.facts.part_len(P_PERM_CODES);
    let keys: Vec<i64> = if n == 0 {
        Vec::new()
    } else {
        let lay = stores.facts.extent_u64(P_LAYOUT, 0, 2);
        // Rows per group; any value above `n - 1` puts every row in group 0, as `n` does.
        let b64 = lay[1];
        let bsize: usize = if b64 <= n as u64 { b64 as usize } else { n };
        let nb = stores.facts.part_len(P_PERM_BASE);
        let nbk = stores.facts.part_len(P_CUST_BASE);
        let pc = stores.facts.extent_u32(P_PERM_CODES, 0, n);
        let pb = stores.facts.extent_u64(P_PERM_BASE, 0, nb);
        let kc = stores.facts.extent_u32(P_CUST_CODES, 0, n);
        let kb = stores.facts.extent_i64(P_CUST_BASE, 0, nbk);
        proof {
            assert(lay@ =~= FC::u64s(sv.facts[P_LAYOUT as int]));
            assert(pc@ =~= FC::u32s(sv.facts[P_PERM_CODES as int]));
            assert(pb@ =~= FC::u64s(sv.facts[P_PERM_BASE as int]));
            assert(kc@ =~= FC::u32s(sv.facts[P_CUST_CODES as int]));
            assert(kb@ =~= FC::i64s(sv.facts[P_CUST_BASE as int]));
            lemma_cols_ok(sv.facts, rel, bsize as int);
        }
        canonical_keys(pc, pb, kc, kb, bsize, n, Ghost(rel))
    };
    let mut out: Vec<OwnedPart> = Vec::new();
    let mut directory = false;
    let mut kmin: i64 = 0;
    let mut k: usize = 0;
    if n == 0 {
        directory = true;
    } else if n < 4294967295usize {
        let (lo, hi) = key_range(&keys);
        let width: i128 = hi as i128 - lo as i128 + 1;
        if width <= 4 * (n as i128) + 1048576 && width < usize::MAX as i128 {
            directory = true;
            kmin = lo;
            k = width as usize;
        }
    }
    if directory {
        let (offs, perm) = build_directory(&keys, kmin, k, Ghost(rel));
        let mut meta: Vec<i64> = Vec::new();
        meta.push(I::MODE_DIRECTORY);
        meta.push(kmin);
        let empty: Vec<i64> = Vec::new();
        let ghost (mv, ov, pv) = (meta@, offs@, perm@);
        out.push(OwnedPart::I64(meta));
        out.push(OwnedPart::U32(offs));
        out.push(OwnedPart::U32(perm));
        out.push(OwnedPart::I64(empty));
        proof {
            let built = owned_parts_view(out@);
            assert(built[0] == PartView::I64(mv));
            assert(built[1] == PartView::U32(ov));
            assert(built[2] == PartView::U32(pv));
            assert forall|db: Database| #[trigger] sources_bound(sv, db)
                implies represents(storage_parts(sv, built), stored_relations(db)) by {
                lemma_src(sv, db);
                assert(storage_parts(sv, built) =~= built);
                assert(I::idx_u32s(built[1]).len() - 1 == k);
            }
        }
    } else {
        let mut meta: Vec<i64> = Vec::new();
        meta.push(0);
        meta.push(0);
        let e1: Vec<u32> = Vec::new();
        let e2: Vec<u32> = Vec::new();
        let ghost (mv, kv) = (meta@, keys@);
        out.push(OwnedPart::I64(meta));
        out.push(OwnedPart::U32(e1));
        out.push(OwnedPart::U32(e2));
        out.push(OwnedPart::I64(keys));
        proof {
            let built = owned_parts_view(out@);
            assert(built[0] == PartView::I64(mv));
            assert(built[3] == PartView::I64(kv));
            assert forall|db: Database| #[trigger] sources_bound(sv, db)
                implies represents(storage_parts(sv, built), stored_relations(db)) by {
                lemma_src(sv, db);
                assert(storage_parts(sv, built) =~= built);
            }
        }
    }
    Ok(out)
}

/// `src_ok` gives `cols_ok` at an effective group size `bsize` that puts every row in the same group as the
/// stored one (`bsize` is the stored group size, or `n` when the stored one exceeds `n`).
proof fn lemma_cols_ok(p: Seq<PartView>, rel: Seq<Row>, bsize: int)
    requires
        src_ok(p, rel),
        rel.len() >= 1,
        bsize == (if FC::u64s(p[P_LAYOUT as int])[1] <= rel.len() { FC::u64s(p[P_LAYOUT as int])[1] as int } else { rel.len() as int }),
    ensures
        cols_ok(FC::u32s(p[P_PERM_CODES as int]), FC::u64s(p[P_PERM_BASE as int]), FC::u32s(p[P_CUST_CODES as int]),
            FC::i64s(p[P_CUST_BASE as int]), bsize, rel),
{
    let n = rel.len() as int;
    let b0 = FC::u64s(p[P_LAYOUT as int])[1] as int;
    let (pc, pb) = (FC::u32s(p[P_PERM_CODES as int]), FC::u64s(p[P_PERM_BASE as int]));
    let (kc, kb) = (FC::u32s(p[P_CUST_CODES as int]), FC::i64s(p[P_CUST_BASE as int]));
    assert forall|s: int| 0 <= s < n implies #[trigger] (s / bsize) == s / b0 by {
        if b0 > n {
            assert(s / bsize == 0) by (nonlinear_arith) requires 0 <= s < bsize;
            assert(s / b0 == 0) by (nonlinear_arith) requires 0 <= s < b0;
        }
    }
    assert forall|s: int| 0 <= s < n implies #[trigger] map_at(pc, pb, bsize, s) == map_at(pc, pb, b0, s)
        && key_at(kc, kb, bsize, s) == key_at(kc, kb, b0, s) by {
        assert(s / bsize == s / b0);
    }
    assert forall|s: int| 0 <= s < n implies #[trigger] (s / bsize) < pb.len() && s / bsize < kb.len() by {
        assert(s / bsize == s / b0);
        assert((s / b0) < pb.len() && s / b0 < kb.len());
    }
    assert forall|s: int| 0 <= s < n implies 0 <= #[trigger] map_at(pc, pb, bsize, s) < n by {
        assert(map_at(pc, pb, bsize, s) == map_at(pc, pb, b0, s));
    }
    assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b implies
        #[trigger] map_at(pc, pb, bsize, a) != #[trigger] map_at(pc, pb, bsize, b) by {
        assert(map_at(pc, pb, bsize, a) == map_at(pc, pb, b0, a));
        assert(map_at(pc, pb, bsize, b) == map_at(pc, pb, b0, b));
        assert(map_at(pc, pb, b0, a) != map_at(pc, pb, b0, b));
    }
    assert forall|r: int| 0 <= r < n implies #[trigger] mapped(pc, pb, bsize, r) by {
        assert(mapped(pc, pb, b0, r));
        let s = choose|s: int| 0 <= s < pc.len() && #[trigger] map_at(pc, pb, b0, s) == r;
        assert(map_at(pc, pb, bsize, s) == map_at(pc, pb, b0, s));
    }
    assert forall|s: int| 0 <= s < n implies {
        &&& i64::MIN <= #[trigger] key_at(kc, kb, bsize, s) <= i64::MAX
        &&& rel[map_at(pc, pb, bsize, s)][0] == Val::Int(key_at(kc, kb, bsize, s))
    } by {
        assert(map_at(pc, pb, bsize, s) == map_at(pc, pb, b0, s));
        assert(key_at(kc, kb, bsize, s) == key_at(kc, kb, b0, s));
        assert(i64::MIN <= key_at(kc, kb, b0, s) <= i64::MAX);
    }
}

/// Two databases bound to the same source parts have the same indexed relation: the row map and key columns of
/// `facts` determine every canonical row's key.
proof fn lemma_same_rel(sv: StoresView, a: Database, b: Database)
    requires
        src_ok(sv.facts, stored_relations(a)[0]),
        src_ok(sv.facts, stored_relations(b)[0]),
    ensures
        stored_relations(a)[0] == stored_relations(b)[0],
{
    let (ra, rb) = (stored_relations(a)[0], stored_relations(b)[0]);
    let p = sv.facts;
    let n = ra.len() as int;
    let bsize = FC::u64s(p[P_LAYOUT as int])[1] as int;
    let (pc, pb) = (FC::u32s(p[P_PERM_CODES as int]), FC::u64s(p[P_PERM_BASE as int]));
    let (kc, kb) = (FC::u32s(p[P_CUST_CODES as int]), FC::i64s(p[P_CUST_BASE as int]));
    assert(rb.len() == n);
    assert forall|r: int| 0 <= r < n implies ra[r] == rb[r] by {
        assert(mapped(pc, pb, bsize, r));
        let s = choose|s: int| 0 <= s < pc.len() && #[trigger] map_at(pc, pb, bsize, s) == r;
        assert(ra[map_at(pc, pb, bsize, s)][0] == Val::Int(key_at(kc, kb, bsize, s)));
        assert(rb[map_at(pc, pb, bsize, s)][0] == Val::Int(key_at(kc, kb, bsize, s)));
        assert(ra[r][0] == rb[r][0]);
        assert(ra[r] =~= rb[r]);
    }
    assert(ra =~= rb);
}

} // verus!
