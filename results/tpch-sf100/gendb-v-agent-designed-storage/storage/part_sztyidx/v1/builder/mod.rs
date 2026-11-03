//! Builder of storage `part_sztyidx` (a secondary composite index of part on (p_size, p_type)) from storage
//! `custpart`.
//!
//! 1. `row_cols`: the p_size and the p_type dictionary entry of every canonical part row (custpart keeps part in
//!    canonical row order; FOR codes, `src`). The index's key texts are a copy of custpart's p_type dictionary.
//! 2. The p_size range `[lo, hi]`. A dense directory needs fewer than `u32::MAX` rows and at most `4 n + 2^20`
//!    composite keys `(hi - lo + 1) * T`; otherwise the fallback mode stores the keys of every row.
//! 3. Composite keys `ck[r] = (p_size - lo) * T + entry` (`composite_keys`), then a counting sort over them:
//!    `count_keys` (rows per key), `prefix_offsets` (directory offsets: prefix sums of the counts), `scatter` (each
//!    row, in canonical order, into the next free slot of its key's range, so rows increase inside an entry and
//!    every row lands in exactly one slot).
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::layout::{PartView, owned_parts_view};
use crate::gendb_entry::parallel::Dispatch;
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::gendb_entry::storage::{represents, stored_relations};
use crate::spec::value::{Database, Row, Val};
use crate::stores::part_sztyidx::interface as I;
use crate::stores::part_sztyidx::interface::key_text;
use crate::stores::custpart::interface::common::colfmt as FC;

pub mod src;
pub mod count;
use src::*;
use count::*;

verus! {

/// The p_size and the p_type dictionary entry of every canonical row: `keys[r] = key_at(r)`, `tents[r] = tent_at(r)`.
fn row_cols(sc: &[u8], sb: &[i64], tc: &[u8], tb: &[u64], bsize: usize, n: usize, nt: usize,
    Ghost(rel): Ghost<Seq<Row>>, Ghost(doffs): Ghost<Seq<u64>>, Ghost(dbytes): Ghost<Seq<u8>>) -> (r: (Vec<i64>, Vec<u64>))
    requires
        rel.len() == n,
        bsize >= 1,
        sc@.len() == n,
        tc@.len() == n,
        nt == doffs.len() - 1,
        forall|q: int| 0 <= q < n ==> #[trigger] (q / bsize as int) < sb@.len() && (q / bsize as int) < tb@.len(),
        forall|q: int| 0 <= q < n ==> {
            &&& i64::MIN <= #[trigger] key_at(sc@, sb@, bsize as int, q) <= i64::MAX
            &&& rel[q][1] == Val::Int(key_at(sc@, sb@, bsize as int, q))
            &&& 0 <= tent_at(tc@, tb@, bsize as int, q) < doffs.len() - 1
            &&& rel[q][0] == Val::Text(key_text(doffs, dbytes, tent_at(tc@, tb@, bsize as int, q)))
        },
    ensures
        r.0@.len() == n,
        r.1@.len() == n,
        forall|q: int| 0 <= q < n ==> {
            &&& #[trigger] rel[q][1] == Val::Int(r.0@[q] as int)
            &&& r.1@[q] < nt
            &&& rel[q][0] == Val::Text(key_text(doffs, dbytes, r.1@[q] as int))
        },
{
    let mut keys: Vec<i64> = Vec::with_capacity(n);
    let mut tents: Vec<u64> = Vec::with_capacity(n);
    let mut r: usize = 0;
    while r < n
        invariant
            rel.len() == n,
            bsize >= 1,
            sc@.len() == n,
            tc@.len() == n,
            nt == doffs.len() - 1,
            forall|q: int| 0 <= q < n ==> #[trigger] (q / bsize as int) < sb@.len() && (q / bsize as int) < tb@.len(),
            forall|q: int| 0 <= q < n ==> {
                &&& i64::MIN <= #[trigger] key_at(sc@, sb@, bsize as int, q) <= i64::MAX
                &&& rel[q][1] == Val::Int(key_at(sc@, sb@, bsize as int, q))
                &&& 0 <= tent_at(tc@, tb@, bsize as int, q) < doffs.len() - 1
                &&& rel[q][0] == Val::Text(key_text(doffs, dbytes, tent_at(tc@, tb@, bsize as int, q)))
            },
            r <= n,
            keys@.len() == r,
            tents@.len() == r,
            forall|q: int| 0 <= q < r ==> {
                &&& #[trigger] rel[q][1] == Val::Int(keys@[q] as int)
                &&& tents@[q] < nt
                &&& rel[q][0] == Val::Text(key_text(doffs, dbytes, tents@[q] as int))
            },
        decreases n - r,
    {
        let g = r / bsize;
        assert((r as int) / (bsize as int) < sb@.len() && (r as int) / (bsize as int) < tb@.len());
        assert(i64::MIN <= key_at(sc@, sb@, bsize as int, r as int) <= i64::MAX);
        assert(0 <= tent_at(tc@, tb@, bsize as int, r as int) < doffs.len() - 1);
        let key = sb[g] + sc[r] as i64;
        let te = tb[g] + tc[r] as u64;
        keys.push(key);
        tents.push(te);
        r = r + 1;
    }
    (keys, tents)
}

/// Composite keys `ck[r] = (keys[r] - lo) * nt + tents[r]`, all below `kk = w * nt`.
fn composite_keys(keys: &Vec<i64>, tents: &Vec<u64>, lo: i64, w: usize, nt: usize, kk: usize) -> (ck: Vec<i64>)
    requires
        keys@.len() == tents@.len(),
        nt >= 1,
        kk == w * nt,
        kk <= i64::MAX,
        forall|q: int| 0 <= q < keys@.len() ==> lo <= #[trigger] keys@[q] < lo + w,
        forall|q: int| 0 <= q < keys@.len() ==> #[trigger] tents@[q] < nt,
    ensures
        ck@.len() == keys@.len(),
        forall|q: int| 0 <= q < keys@.len() ==> 0 <= #[trigger] ck@[q] < kk
            && ck@[q] == (keys@[q] - lo) * nt + tents@[q],
{
    let n = keys.len();
    let mut ck: Vec<i64> = Vec::with_capacity(n);
    let mut r: usize = 0;
    while r < n
        invariant
            n == keys@.len(),
            keys@.len() == tents@.len(),
            nt >= 1,
            kk == w * nt,
            kk <= i64::MAX,
            forall|q: int| 0 <= q < keys@.len() ==> lo <= #[trigger] keys@[q] < lo + w,
            forall|q: int| 0 <= q < keys@.len() ==> #[trigger] tents@[q] < nt,
            r <= n,
            ck@.len() == r,
            forall|q: int| 0 <= q < r ==> 0 <= #[trigger] ck@[q] < kk
                && ck@[q] == (keys@[q] - lo) * nt + tents@[q],
        decreases n - r,
    {
        let x = keys[r];
        let te = tents[r];
        assert(lo <= x < lo + w);
        assert(te < nt);
        let d: i128 = x as i128 - lo as i128;
        proof {
            assert(d * (nt as int) + (te as int) < kk) by (nonlinear_arith)
                requires 0 <= d < w, 0 <= te < nt, kk == w * nt;
            assert(d * (nt as int) >= 0) by (nonlinear_arith) requires 0 <= d, nt >= 1;
        }
        let v: i128 = d * (nt as i128) + te as i128;
        ck.push(v as i64);
        r = r + 1;
    }
    ck
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
        forall|e: int, j1: int, j2: int| 0 <= e < k && #[trigger] I::in_entry(offs@, e, j1)
            && #[trigger] I::in_entry(offs@, e, j2) && j1 < j2 ==> perm@[j1] < perm@[j2],
        forall|j1: int, j2: int| 0 <= j1 < keys@.len() && 0 <= j2 < keys@.len() && j1 != j2
            ==> #[trigger] perm@[j1] != #[trigger] perm@[j2],
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
            forall|e: int, j1: int, j2: int| 0 <= e < k && #[trigger] filled(offs@, cur@, e, j1)
                && #[trigger] filled(offs@, cur@, e, j2) && j1 < j2 ==> perm@[j1] < perm@[j2],
            pos.len() == r,
            forall|q: int| 0 <= q < r ==> {
                &&& #[trigger] filled(offs@, cur@, keys@[q] - kmin, pos[q])
                &&& perm@[pos[q]] == q
            },
            // Every filled slot is the slot of the row it holds (so no row is held twice).
            forall|e: int, j: int| 0 <= e < k && #[trigger] filled(offs@, cur@, e, j) ==> j < n && pos[perm@[j] as int] == j,
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
            // Rows increase inside an entry: the new slot `w` is the last filled one of entry `e` and holds `r`,
            // larger than every row written before.
            assert forall|f: int, j1: int, j2: int| 0 <= f < k && #[trigger] filled(offs@, cur@, f, j1)
                && #[trigger] filled(offs@, cur@, f, j2) && j1 < j2 implies perm@[j1] < perm@[j2] by {
                if f != ei {
                    assert(filled(offs@, old_cur, f, j1) && filled(offs@, old_cur, f, j2));
                    assert(j1 != w) by {
                        lemma_cnt_mono(keys@, kmin + f, r as int, n as int);
                        if f < ei { lemma_entries_ordered(cnt, f, ei); } else { lemma_entries_ordered(cnt, ei, f); }
                    }
                    assert(j2 != w) by {
                        lemma_cnt_mono(keys@, kmin + f, r as int, n as int);
                        if f < ei { lemma_entries_ordered(cnt, f, ei); } else { lemma_entries_ordered(cnt, ei, f); }
                    }
                } else if j2 != w {
                    assert(filled(offs@, old_cur, f, j1) && filled(offs@, old_cur, f, j2));
                } else {
                    assert(filled(offs@, old_cur, f, j1));
                    assert(old_perm[j1] < r);
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
            assert(offs@[ei + 1] <= n);
            assert forall|f: int, j: int| 0 <= f < k && #[trigger] filled(offs@, cur@, f, j) implies j < n && new_pos[perm@[j] as int] == j by {
                if j == w {
                    assert(perm@[j] == r);
                } else {
                    assert(filled(offs@, old_cur, f, j));
                    assert(j < n);
                    assert(perm@[j] == old_perm[j]);
                    assert(old_perm[j] < r);
                    assert(new_pos[old_perm[j] as int] == pos[old_perm[j] as int]);
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
        assert forall|e: int, j1: int, j2: int| 0 <= e < k && #[trigger] I::in_entry(offs@, e, j1)
            && #[trigger] I::in_entry(offs@, e, j2) && j1 < j2 implies perm@[j1] < perm@[j2] by {
            assert(filled(offs@, cur@, e, j1) && filled(offs@, cur@, e, j2));
        }
        assert forall|q: int| 0 <= q < n implies #[trigger] I::listed(perm@, q) by {
            let f = keys@[q] - kmin;
            assert(filled(offs@, cur@, f, pos[q]));
            lemma_psum_mono(cnt, f + 1, k as int);
            assert(cur@[f] == offs@[f + 1]);
            assert(0 <= pos[q] < perm@.len());
        }
        // Every slot is filled: it lies in some entry, and every entry is full.
        assert(offs@[0] == 0);
        assert(offs@[k as int] == n);
        assert forall|e: int| 0 <= e < k implies #[trigger] offs@[e] <= offs@[e + 1] by {
            assert(offs@[e + 1] == psum(cnt, e) + cnt[e]);
        }
        assert forall|j1: int, j2: int| 0 <= j1 < n && 0 <= j2 < n && j1 != j2
            implies #[trigger] perm@[j1] != #[trigger] perm@[j2] by {
            let e1 = I::lemma_find_entry(offs@, k as int, j1);
            let e2 = I::lemma_find_entry(offs@, k as int, j2);
            assert(filled(offs@, cur@, e1, j1));
            assert(filled(offs@, cur@, e2, j2));
        }
    }
    perm
}

/// The directory of the composite keys `ck` over `0 .. k` (fewer than `u32::MAX` rows).
fn build_directory(ck: &Vec<i64>, k: usize) -> (r: (Vec<u32>, Vec<u32>))
    requires
        k < usize::MAX,
        ck@.len() < u32::MAX,
        forall|q: int| 0 <= q < ck@.len() ==> 0 <= #[trigger] ck@[q] < k,
    ensures
        r.0@.len() == k + 1,
        r.0@[0] == 0,
        r.0@[k as int] == ck@.len(),
        forall|e: int| 0 <= e < k ==> #[trigger] r.0@[e] <= r.0@[e + 1],
        r.1@.len() == ck@.len(),
        forall|e: int, j: int| 0 <= e < k && #[trigger] I::in_entry(r.0@, e, j) ==>
            r.1@[j] < ck@.len() && ck@[r.1@[j] as int] == e,
        forall|q: int| 0 <= q < ck@.len() ==> #[trigger] I::listed(r.1@, q),
        forall|j1: int, j2: int| 0 <= j1 < ck@.len() && 0 <= j2 < ck@.len() && j1 != j2
            ==> #[trigger] r.1@[j1] != #[trigger] r.1@[j2],
        forall|e: int, j1: int, j2: int| 0 <= e < k && #[trigger] I::in_entry(r.0@, e, j1)
            && #[trigger] I::in_entry(r.0@, e, j2) && j1 < j2 ==> r.1@[j1] < r.1@[j2],
{
    let n = ck.len();
    let cnt = count_keys(ck, 0, k);
    let offs = prefix_offsets(&cnt, k, Ghost(n as int));
    let perm = scatter(ck, 0, k, Ghost(cnt@), &offs);
    proof {
        let o = offs@;
        assert(o[0] == 0);
        assert forall|e: int| 0 <= e < k implies #[trigger] o[e] <= o[e + 1] by {
            assert(o[e + 1] == psum(cnt@, e) + cnt@[e]);
        }
    }
    (offs, perm)
}

/// A copy of a U64 slice.
fn copy_u64s(s: &[u64]) -> (v: Vec<u64>)
    ensures v@ == s@,
{
    let n = s.len();
    let mut v: Vec<u64> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant n == s@.len(), i <= n, v@ == s@.subrange(0, i as int),
        decreases n - i,
    {
        v.push(s[i]);
        proof { assert(s@.subrange(0, i + 1) =~= s@.subrange(0, i as int).push(s@[i as int])); }
        i = i + 1;
    }
    proof { assert(s@.subrange(0, n as int) =~= s@); }
    v
}

/// A copy of a U8 slice.
fn copy_u8s(s: &[u8]) -> (v: Vec<u8>)
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
        proof { assert(s@.subrange(0, i + 1) =~= s@.subrange(0, i as int).push(s@[i as int])); }
        i = i + 1;
    }
    proof { assert(s@.subrange(0, n as int) =~= s@); }
    v
}

/// The facts of every canonical row the index is built from: its p_size `keys[q]` and p_type key text number
/// `tents[q] < nt`.
pub open spec fn rows_ok(keys: Seq<i64>, tents: Seq<u64>, nt: int, toffs: Seq<u64>, tbytes: Seq<u8>, rel: Seq<Row>) -> bool {
    &&& keys.len() == rel.len()
    &&& tents.len() == rel.len()
    &&& forall|q: int| 0 <= q < rel.len() ==> (#[trigger] rel[q]).len() == 2
    &&& forall|q: int| 0 <= q < rel.len() ==> {
            &&& #[trigger] rel[q][1] == Val::Int(keys[q] as int)
            &&& tents[q] < nt
            &&& rel[q][0] == Val::Text(key_text(toffs, tbytes, tents[q] as int))
        }
}

/// The directory over the composite keys `ck` of the rows is a directory of their (p_size, p_type) keys.
proof fn lemma_dir_ok(kmin: int, nt: int, kk: int, keys: Seq<i64>, tents: Seq<u64>, ck: Seq<i64>, toffs: Seq<u64>, tbytes: Seq<u8>,
    offs: Seq<u32>, perm: Seq<u32>, rel: Seq<Row>)
    requires
        rows_ok(keys, tents, nt, toffs, tbytes, rel),
        kk >= 0,
        kk == 0 || nt >= 1,
        ck.len() == rel.len(),
        forall|q: int| 0 <= q < rel.len() ==> #[trigger] ck[q] == (keys[q] - kmin) * nt + tents[q],
        offs.len() == kk + 1,
        offs[0] == 0,
        offs[kk] == rel.len(),
        forall|e: int| 0 <= e < kk ==> #[trigger] offs[e] <= offs[e + 1],
        perm.len() == rel.len(),
        forall|e: int, j: int| 0 <= e < kk && #[trigger] I::in_entry(offs, e, j) ==>
            perm[j] < rel.len() && ck[perm[j] as int] == e,
        forall|q: int| 0 <= q < rel.len() ==> #[trigger] I::listed(perm, q),
        forall|j1: int, j2: int| 0 <= j1 < rel.len() && 0 <= j2 < rel.len() && j1 != j2
            ==> #[trigger] perm[j1] != #[trigger] perm[j2],
        forall|e: int, j1: int, j2: int| 0 <= e < kk && #[trigger] I::in_entry(offs, e, j1)
            && #[trigger] I::in_entry(offs, e, j2) && j1 < j2 ==> perm[j1] < perm[j2],
    ensures
        I::directory_ok(kmin, nt, toffs, tbytes, offs, perm, rel),
{
    assert forall|e: int, j: int| 0 <= e < kk && #[trigger] I::in_entry(offs, e, j) implies
        perm[j] < rel.len() && I::has_key(rel[perm[j] as int], kmin, nt, toffs, tbytes, e) by {
        let q = perm[j] as int;
        assert(ck[q] == e);
        assert(rel[q][1] == Val::Int(keys[q] as int));
        lemma_entry_key(kmin, nt, keys[q] as int, tents[q] as int, e);
    }
    let n = rel.len() as int;
    let k = offs.len() - 1;
    assert(k == kk);
    assert(offs.len() >= 1);
    assert(k == 0 || nt >= 1);
    assert(offs[0] == 0);
    assert(offs[k] == n);
    assert(forall|e: int| 0 <= e < k ==> #[trigger] offs[e] <= offs[e + 1]);
    assert(perm.len() == n);
    assert(forall|r: int| 0 <= r < n ==> #[trigger] I::listed(perm, r));
    assert(forall|j1: int, j2: int| 0 <= j1 < n && 0 <= j2 < n && j1 != j2 ==> #[trigger] perm[j1] != #[trigger] perm[j2]);
    assert(forall|e: int, j1: int, j2: int| 0 <= e < k && #[trigger] I::in_entry(offs, e, j1) && #[trigger] I::in_entry(offs, e, j2)
            && j1 < j2 ==> perm[j1] < perm[j2]);
}

/// Composite key `e = (key - kmin) * nt + tent` (`tent < nt`) splits back into `key - kmin` and `tent`.
proof fn lemma_entry_key(kmin: int, nt: int, key: int, tent: int, e: int)
    requires 0 <= tent < nt, e == (key - kmin) * nt + tent,
    ensures e / nt == key - kmin, e % nt == tent,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(e, nt, key - kmin, tent);
}

/// The parts of a dense directory represent the rows.
proof fn lemma_dir_represents(built: Seq<PartView>, mv: Seq<i64>, ov: Seq<u32>, pv: Seq<u32>, tov: Seq<u64>, tbv: Seq<u8>, rel: Seq<Row>)
    requires
        built.len() == I::STYIDX_PARTS,
        built[0] == PartView::I64(mv),
        built[1] == PartView::U32(ov),
        built[2] == PartView::U32(pv),
        built[3] == PartView::U64(tov),
        built[4] == PartView::U8(tbv),
        built[5] is I64,
        built[6] is U64,
        mv.len() == 2,
        mv[0] == I::MODE_DIRECTORY,
        I::texts_ok(tov, tbv),
        forall|q: int| 0 <= q < rel.len() ==> (#[trigger] rel[q]).len() == 2,
        I::directory_ok(mv[1] as int, tov.len() - 1, tov, tbv, ov, pv, rel),
    ensures
        I::represents(built, seq![rel]),
{
    assert(seq![rel][0] == rel);
}

/// The parts of a dense directory over the composite keys `0 .. kk = w * nt` (p_sizes `kmin .. kmin + w`).
fn directory_parts(keys: Vec<i64>, tents: Vec<u64>, toffs: Vec<u64>, tbytes: Vec<u8>, nt: usize, kmin: i64, w: usize, kk: usize,
    Ghost(rel): Ghost<Seq<Row>>) -> (out: Vec<OwnedPart>)
    requires
        rows_ok(keys@, tents@, nt as int, toffs@, tbytes@, rel),
        I::texts_ok(toffs@, tbytes@),
        nt == toffs@.len() - 1,
        keys@.len() < u32::MAX,
        keys@.len() == 0 || (nt >= 1 && kk == w * nt && kk < usize::MAX && kk <= i64::MAX
            && forall|q: int| 0 <= q < keys@.len() ==> kmin <= #[trigger] keys@[q] < kmin + w),
        keys@.len() == 0 ==> kk == 0,
    ensures
        I::represents(owned_parts_view(out@), seq![rel]),
{
    let n = keys.len();
    let mut out: Vec<OwnedPart> = Vec::new();
    let ghost (tov, tbv) = (toffs@, tbytes@);
    proof {
        assert forall|q: int| 0 <= q < keys@.len() implies #[trigger] tents@[q] < nt by {
            assert(rel[q][1] == Val::Int(keys@[q] as int));
        }
    }
    let ck: Vec<i64> = if n == 0 { Vec::new() } else { composite_keys(&keys, &tents, kmin, w, nt, kk) };
    assert(ck@.len() == n);
    let (offs, perm) = build_directory(&ck, kk);
    let mut meta: Vec<i64> = Vec::new();
    meta.push(I::MODE_DIRECTORY);
    meta.push(kmin);
    let e1: Vec<i64> = Vec::new();
    let e2: Vec<u64> = Vec::new();
    let ghost (mv, ov, pv) = (meta@, offs@, perm@);
    proof {
        lemma_dir_ok(kmin as int, nt as int, kk as int, keys@, tents@, ck@, tov, tbv, ov, pv, rel);
    }
    out.push(OwnedPart::I64(meta));
    out.push(OwnedPart::U32(offs));
    out.push(OwnedPart::U32(perm));
    out.push(OwnedPart::U64(toffs));
    out.push(OwnedPart::U8(tbytes));
    out.push(OwnedPart::I64(e1));
    out.push(OwnedPart::U64(e2));
    proof {
        let built = owned_parts_view(out@);
        assert(built[0] == PartView::I64(mv));
        assert(built[1] == PartView::U32(ov));
        assert(built[2] == PartView::U32(pv));
        assert(built[3] == PartView::U64(tov));
        assert(built[4] == PartView::U8(tbv));
        lemma_dir_represents(built, mv, ov, pv, tov, tbv, rel);
    }
    out
}

/// The parts of the fallback mode: the keys of every row.
fn fallback_parts(keys: Vec<i64>, tents: Vec<u64>, toffs: Vec<u64>, tbytes: Vec<u8>, nt: usize, Ghost(rel): Ghost<Seq<Row>>)
    -> (out: Vec<OwnedPart>)
    requires
        rows_ok(keys@, tents@, nt as int, toffs@, tbytes@, rel),
        I::texts_ok(toffs@, tbytes@),
        nt == toffs@.len() - 1,
    ensures
        I::represents(owned_parts_view(out@), seq![rel]),
{
    let mut out: Vec<OwnedPart> = Vec::new();
    let ghost (tov, tbv) = (toffs@, tbytes@);
    let mut meta: Vec<i64> = Vec::new();
    meta.push(0);
    meta.push(0);
    let e1: Vec<u32> = Vec::new();
    let e2: Vec<u32> = Vec::new();
    let ghost (mv, kv, tv) = (meta@, keys@, tents@);
    out.push(OwnedPart::I64(meta));
    out.push(OwnedPart::U32(e1));
    out.push(OwnedPart::U32(e2));
    out.push(OwnedPart::U64(toffs));
    out.push(OwnedPart::U8(tbytes));
    out.push(OwnedPart::I64(keys));
    out.push(OwnedPart::U64(tents));
    proof {
        let built = owned_parts_view(out@);
        assert(built[0] == PartView::I64(mv));
        assert(built[3] == PartView::U64(tov));
        assert(built[4] == PartView::U8(tbv));
        assert(built[5] == PartView::I64(kv));
        assert(built[6] == PartView::U64(tv));
        assert(seq![rel][0] == rel);
    }
    out
}

/// The index parts `[META, OFFS, PERM, TOFFS, TBYTES, KEYS, TENT]` of the rows `rel`.
fn index_parts(keys: Vec<i64>, tents: Vec<u64>, toffs: Vec<u64>, tbytes: Vec<u8>, nt: usize, Ghost(rel): Ghost<Seq<Row>>)
    -> (out: Vec<OwnedPart>)
    requires
        rows_ok(keys@, tents@, nt as int, toffs@, tbytes@, rel),
        I::texts_ok(toffs@, tbytes@),
        nt == toffs@.len() - 1,
    ensures
        I::represents(owned_parts_view(out@), seq![rel]),
{
    let n = keys.len();
    let mut out: Vec<OwnedPart> = Vec::new();
    let mut directory = false;
    let mut kmin: i64 = 0;
    let mut kk: usize = 0;
    let mut w: usize = 0;
    if n == 0 {
        directory = true;
    } else if n < 4294967295usize && nt >= 1 {
        let (lo, hi) = key_range(&keys);
        let width: i128 = hi as i128 - lo as i128 + 1;
        let bound: i128 = 4 * (n as i128) + 1048576;
        if width <= bound && (nt as i128) <= bound {
            proof {
                assert(width * (nt as int) <= bound * bound) by (nonlinear_arith)
                    requires 1 <= width <= bound, 0 <= nt <= bound;
                assert(bound * bound <= 0x10000_0000_0000_0000_0000) by (nonlinear_arith)
                    requires 0 <= bound <= 0x4_0010_0000;
            }
            let kw: i128 = width * (nt as i128);
            if kw <= bound && width < usize::MAX as i128 && kw < usize::MAX as i128 {
                directory = true;
                kmin = lo;
                w = width as usize;
                assert(kw >= 0) by (nonlinear_arith) requires kw == width * (nt as int), width >= 1, nt >= 0;
                kk = kw as usize;
                assert(w == width && kk == kw);
            }
        }
    }
    if directory {
        directory_parts(keys, tents, toffs, tbytes, nt, kmin, w, kk, Ghost(rel))
    } else {
        fallback_parts(keys, tents, toffs, tbytes, nt, Ghost(rel))
    }
}

/// Build the index parts `[META, OFFS, PERM, TOFFS, TBYTES, KEYS, TENT]`.
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
        assert forall|db: Database| #[trigger] sources_bound(sv, db) implies stored_relations(db) == seq![rel] by {
            lemma_src(sv, db);
            lemma_same_rel(sv, db0, db);
            crate::stores::part_sztyidx::declaration::lemma_stored_relations(db);
            assert(stored_relations(db) =~= seq![rel]);
        }
    }
    let ghost p = sv.custpart;
    let ghost doffs_s = FC::u64s(p[P_TYPE_DOFFS as int]);
    let ghost dbytes_s = FC::u8s(p[P_TYPE_DBYTES as int]);
    // The key texts: custpart's p_type dictionary.
    let dl = stores.custpart.part_len(P_TYPE_DOFFS);
    let doffs = stores.custpart.extent_u64(P_TYPE_DOFFS, 0, dl);
    let bl = stores.custpart.part_len(P_TYPE_DBYTES);
    let dbytes = stores.custpart.extent_u8(P_TYPE_DBYTES, 0, bl);
    proof {
        assert(doffs@ =~= doffs_s);
        assert(dbytes@ =~= dbytes_s);
    }
    let nt: usize = dl - 1;
    let toffs = copy_u64s(doffs);
    let tbytes = copy_u8s(dbytes);
    let n = stores.custpart.part_len(P_SIZE_CODES);
    let (keys, tents): (Vec<i64>, Vec<u64>) = if n == 0 {
        (Vec::new(), Vec::new())
    } else {
        let lay = stores.custpart.extent_u64(P_LAYOUT, 0, 2);
        // Rows per group; any value above `n - 1` puts every row in group 0, as `n` does.
        let b64 = lay[1];
        let bsize: usize = if b64 <= n as u64 { b64 as usize } else { n };
        let nb = stores.custpart.part_len(P_SIZE_BASE);
        let sc = stores.custpart.extent_u8(P_SIZE_CODES, 0, n);
        let sb = stores.custpart.extent_i64(P_SIZE_BASE, 0, nb);
        let ntb = stores.custpart.part_len(P_TYPE_BASE);
        let tc = stores.custpart.extent_u8(P_TYPE_CODES, 0, n);
        let tb = stores.custpart.extent_u64(P_TYPE_BASE, 0, ntb);
        proof {
            assert(lay@ =~= FC::u64s(p[P_LAYOUT as int]));
            assert(sc@ =~= FC::u8s(p[P_SIZE_CODES as int]));
            assert(sb@ =~= FC::i64s(p[P_SIZE_BASE as int]));
            assert(tc@ =~= FC::u8s(p[P_TYPE_CODES as int]));
            assert(tb@ =~= FC::u64s(p[P_TYPE_BASE as int]));
            lemma_key_facts(p, rel, bsize as int);
        }
        row_cols(sc, sb, tc, tb, bsize, n, nt, Ghost(rel), Ghost(doffs_s), Ghost(dbytes_s))
    };
    proof {
        assert(rows_ok(keys@, tents@, nt as int, toffs@, tbytes@, rel)) by {
            assert forall|q: int| 0 <= q < rel.len() implies (#[trigger] rel[q]).len() == 2 by {}
        }
    }
    let out = index_parts(keys, tents, toffs, tbytes, nt, Ghost(rel));
    proof {
        let built = owned_parts_view(out@);
        assert forall|db: Database| #[trigger] sources_bound(sv, db)
            implies represents(storage_parts(sv, built), stored_relations(db)) by {
            assert(storage_parts(sv, built) =~= built);
            assert(stored_relations(db) == seq![rel]);
        }
    }
    Ok(out)
}

/// `src_ok` gives the facts `row_cols` needs at an effective group size `bsize` that puts every row in the same
/// group as the stored one (`bsize` is the stored group size, or `n` when the stored one exceeds `n`).
proof fn lemma_key_facts(p: Seq<PartView>, rel: Seq<Row>, bsize: int)
    requires
        src_ok(p, rel),
        rel.len() >= 1,
        bsize == (if FC::u64s(p[P_LAYOUT as int])[1] <= rel.len() { FC::u64s(p[P_LAYOUT as int])[1] as int } else { rel.len() as int }),
    ensures
        bsize >= 1,
        FC::u8s(p[P_SIZE_CODES as int]).len() == rel.len(),
        FC::u8s(p[P_TYPE_CODES as int]).len() == rel.len(),
        forall|r: int| 0 <= r < rel.len() ==> #[trigger] (r / bsize) < FC::i64s(p[P_SIZE_BASE as int]).len()
            && (r / bsize) < FC::u64s(p[P_TYPE_BASE as int]).len(),
        forall|r: int| 0 <= r < rel.len() ==> {
            &&& i64::MIN <= #[trigger] key_at(FC::u8s(p[P_SIZE_CODES as int]), FC::i64s(p[P_SIZE_BASE as int]), bsize, r) <= i64::MAX
            &&& rel[r][1] == Val::Int(key_at(FC::u8s(p[P_SIZE_CODES as int]), FC::i64s(p[P_SIZE_BASE as int]), bsize, r))
            &&& 0 <= tent_at(FC::u8s(p[P_TYPE_CODES as int]), FC::u64s(p[P_TYPE_BASE as int]), bsize, r) < FC::u64s(p[P_TYPE_DOFFS as int]).len() - 1
            &&& rel[r][0] == Val::Text(key_text(FC::u64s(p[P_TYPE_DOFFS as int]), FC::u8s(p[P_TYPE_DBYTES as int]),
                    tent_at(FC::u8s(p[P_TYPE_CODES as int]), FC::u64s(p[P_TYPE_BASE as int]), bsize, r)))
        },
{
    let n = rel.len() as int;
    let b0 = FC::u64s(p[P_LAYOUT as int])[1] as int;
    let (sc, sb) = (FC::u8s(p[P_SIZE_CODES as int]), FC::i64s(p[P_SIZE_BASE as int]));
    let (tc, tb) = (FC::u8s(p[P_TYPE_CODES as int]), FC::u64s(p[P_TYPE_BASE as int]));
    assert forall|r: int| 0 <= r < n implies #[trigger] (r / bsize) == r / b0 by {
        if b0 > n {
            assert(r / bsize == 0) by (nonlinear_arith) requires 0 <= r < bsize;
            assert(r / b0 == 0) by (nonlinear_arith) requires 0 <= r < b0;
        }
    }
    assert forall|r: int| 0 <= r < n implies #[trigger] (r / bsize) < sb.len() && (r / bsize) < tb.len() by {
        assert(r / bsize == r / b0);
        assert((r / b0) < sb.len() && (r / b0) < tb.len());
    }
    assert forall|r: int| 0 <= r < n implies {
        &&& i64::MIN <= #[trigger] key_at(sc, sb, bsize, r) <= i64::MAX
        &&& rel[r][1] == Val::Int(key_at(sc, sb, bsize, r))
        &&& 0 <= tent_at(tc, tb, bsize, r) < FC::u64s(p[P_TYPE_DOFFS as int]).len() - 1
        &&& rel[r][0] == Val::Text(key_text(FC::u64s(p[P_TYPE_DOFFS as int]), FC::u8s(p[P_TYPE_DBYTES as int]), tent_at(tc, tb, bsize, r)))
    } by {
        assert(r / bsize == r / b0);
        assert(key_at(sc, sb, bsize, r) == key_at(sc, sb, b0, r));
        assert(tent_at(tc, tb, bsize, r) == tent_at(tc, tb, b0, r));
        assert(i64::MIN <= key_at(sc, sb, b0, r) <= i64::MAX);
    }
}

/// Two databases bound to the same source parts have the same indexed relation: the p_size and p_type codes of
/// `custpart` determine every canonical row's keys.
proof fn lemma_same_rel(sv: StoresView, a: Database, b: Database)
    requires
        src_ok(sv.custpart, stored_relations(a)[0]),
        src_ok(sv.custpart, stored_relations(b)[0]),
    ensures
        stored_relations(a)[0] == stored_relations(b)[0],
{
    let (ra, rb) = (stored_relations(a)[0], stored_relations(b)[0]);
    let p = sv.custpart;
    let n = ra.len() as int;
    let bsize = FC::u64s(p[P_LAYOUT as int])[1] as int;
    let (sc, sb) = (FC::u8s(p[P_SIZE_CODES as int]), FC::i64s(p[P_SIZE_BASE as int]));
    assert(rb.len() == n);
    assert forall|r: int| 0 <= r < n implies ra[r] == rb[r] by {
        assert(i64::MIN <= key_at(sc, sb, bsize, r) <= i64::MAX);
        assert(ra[r][0] == rb[r][0]);
        assert(ra[r][1] == rb[r][1]);
        assert(ra[r].len() == 2 && rb[r].len() == 2);
        assert(ra[r] =~= rb[r]);
    }
    assert(ra =~= rb);
}

} // verus!
