//! Builder of storage `factspk`: one pass over facts' l_partkey key index (positions `0 .. n` in key order) fills
//! the directory `dir[i]` = first position whose key is at least `kb + i` (`kb` = the key at position 0), the row
//! count after the last key. The invariant does not need the index to be sorted; queries use its sortedness
//! (facts' `keyidx_ok`) to read the rows of one key as `[dir[i], dir[i + 1])`.
//! Fallback (no rows, more than `u32::MAX` rows, a key range beyond `MAX_KEYS`, or a non-`i64` smallest key): the
//! one-entry directory `[0]` with `kb = i64::MIN`, which satisfies the same relation.
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::layout::{PartView, owned_parts_view, owned_part_view};
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::{sources_ready, sources_bound, storage_parts};
use crate::spec::value::{Database, Row};
use crate::stores::facts::interface as fi;
use crate::stores::factspk::interface as pk;
use fi::common::colfmt::{u32s, u64s, i64s};
use fi::common::keyidx::{fkey, fidx, irow, keyidx_ok, idx_map};
use fi::common::colfmt::is_perm;

verus! {

/// Most directory entries (key range + 2).
pub const MAX_KEYS: usize = 0x4000_0000;

/// The l_partkey key index of facts' parts `f`, as `key_at` reads it.
pub open spec fn fkey_at(f: Seq<PartView>, r: int) -> int {
    pk::key_at(f, r)
}

/// What the builder needs of facts' lineitem parts (from `represents` of any bound database).
pub open spec fn src_ok(f: Seq<PartView>) -> bool {
    let n = pk::li_rows(f);
    let bs = pk::li_bsize(f);
    &&& f.len() == fi::FACTS_PARTS
    &&& f[fi::LI_LAYOUT as int] is U64 && u64s(f[fi::LI_LAYOUT as int]).len() == 2
    &&& f[fi::LI_PARTKEY_CODES as int] is U32 && f[fi::LI_PARTKEY_BASE as int] is I64
    &&& f[fi::LI_KEYIDX_CODES as int] is U32 && f[fi::LI_KEYIDX_BASE as int] is U64
    &&& f[fi::LI_KEYIDX_KIND as int] is U64 && u64s(f[fi::LI_KEYIDX_KIND as int]).len() == 1
    &&& keyidx_ok(u32s(f[fi::LI_PARTKEY_CODES as int]), i64s(f[fi::LI_PARTKEY_BASE as int]),
            u32s(f[fi::LI_KEYIDX_CODES as int]), u64s(f[fi::LI_KEYIDX_BASE as int]), bs,
            u64s(f[fi::LI_KEYIDX_KIND as int])[0], n)
}

/// A bound database gives `src_ok`.
proof fn lemma_src_ok(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures src_ok(sv.facts),
{
    let f = sv.facts;
    let rels = crate::stores::facts::declaration::stored_relations(db);
    assert(fi::represents(f, rels));
    let tp = f.subrange(fi::LINEITEM_FIRST as int, (fi::LINEITEM_FIRST + fi::LI_PARTS) as int);
    assert(fi::lineitem_ok(tp, rels[0]));
    assert(fi::LINEITEM_FIRST == 0);
    assert forall|k: int| 0 <= k < fi::LI_PARTS implies tp[k] == f[k] by {}
    assert(tp[fi::LI_LAYOUT as int] == f[fi::LI_LAYOUT as int]);
    assert(tp[fi::LI_PARTKEY_CODES as int] == f[fi::LI_PARTKEY_CODES as int]);
    assert(tp[fi::LI_PARTKEY_BASE as int] == f[fi::LI_PARTKEY_BASE as int]);
    assert(tp[fi::LI_KEYIDX_CODES as int] == f[fi::LI_KEYIDX_CODES as int]);
    assert(tp[fi::LI_KEYIDX_BASE as int] == f[fi::LI_KEYIDX_BASE as int]);
    assert(tp[fi::LI_KEYIDX_KIND as int] == f[fi::LI_KEYIDX_KIND as int]);
    let rows = fi::lineitem_rows(tp, rels[0]);
    assert(fi::lineitem_cols_ok(tp, rows));
    assert(rows.len() == rels[0].len());
    assert(u64s(tp[fi::LI_LAYOUT as int])[0] == rels[0].len());
}

/// The key at index position `r`, computed as `key_at` defines it.
fn key_exec(kc: &[u32], kb: &[i64], ic: &[u32], ib: &[u64], bs: usize, kind: u64, n: usize, r: usize, Ghost(f): Ghost<Seq<PartView>>)
    -> (k: i128)
    requires
        src_ok(f),
        kc@ == u32s(f[fi::LI_PARTKEY_CODES as int]), kb@ == i64s(f[fi::LI_PARTKEY_BASE as int]),
        ic@ == u32s(f[fi::LI_KEYIDX_CODES as int]), ib@ == u64s(f[fi::LI_KEYIDX_BASE as int]),
        bs as int == pk::li_bsize(f), kind == u64s(f[fi::LI_KEYIDX_KIND as int])[0], n as int == pk::li_rows(f),
        r < n,
    ensures
        k as int == fkey_at(f, r as int),
{
    proof {
        fi::common::keyidx::lemma_irow_bound(kc@, kb@, ic@, ib@, bs as int, kind, n as int, r as int);
        fi::common::read::lemma_div_lt(r as int, bs as int, kb@.len() as int);
        if kind == 2 {
            fi::common::read::lemma_div_lt(r as int, bs as int, ib@.len() as int);
            assert(idx_map(ic@, ib@, bs as int, n as int)[r as int] == fidx(ic@, ib@, bs as int, r as int));
        }
    }
    let j: usize = if kind == 2 { (ib[r / bs] as i128 + ic[r] as i128) as usize } else { r };
    proof {
        assert(j as int == irow(kind, ic@, ib@, bs as int, r as int));
        fi::common::read::lemma_div_lt(j as int, bs as int, kb@.len() as int);
    }
    kb[j / bs] as i128 + kc[j] as i128
}

/// Entries `[0, i)` of `dir` are directory entries over facts' parts `f` with origin `kb`.
pub open spec fn filled_ok(f: Seq<PartView>, dir: Seq<u32>, kb: int, i: int) -> bool {
    forall|x: int| 0 <= x < i ==> #[trigger] entry_ok(f, dir, kb, x)
}

/// `dir[x]` is the first position whose key is at least `kb + x`, or the row count.
pub open spec fn entry_ok(f: Seq<PartView>, dir: Seq<u32>, kb: int, x: int) -> bool {
    let d = dir[x] as int;
    &&& d <= pk::li_rows(f)
    &&& forall|r: int| 0 <= r < d ==> #[trigger] fkey_at(f, r) < kb + x
    &&& d < pk::li_rows(f) ==> fkey_at(f, d) >= kb + x
}

/// The directory over facts' parts `f`: `(kb, dir)` with every entry correct.
fn directory(stores: &mut Stores, Ghost(f): Ghost<Seq<PartView>>) -> (r: (i64, Vec<u32>))
    requires old(stores)@.facts == f, src_ok(f),
    ensures
        final(stores)@ == old(stores)@,
        r.1@.len() >= 1,
        filled_ok(f, r.1@, r.0 as int, r.1@.len() as int),
{
    let lay = stores.facts.extent_u64(fi::LI_LAYOUT, 0, 2);
    let n64 = lay[0];
    let bs64 = lay[1];
    proof {
        assert(lay@ =~= u64s(f[fi::LI_LAYOUT as int]));
    }
    let kind_v = stores.facts.extent_u64(fi::LI_KEYIDX_KIND, 0, 1);
    let kind = kind_v[0];
    let fb: (i64, Vec<u32>) = (i64::MIN, vec![0u32; 1]);
    proof {
        assert(fb.1@.len() == 1);
        assert(entry_ok(f, fb.1@, i64::MIN as int, 0)) by {
            assert(fb.1@[0] == 0) by { assert(vstd::pervasive::cloned(0u32, fb.1@[0])); }
            if 0 < pk::li_rows(f) {
                fi::common::keyidx::lemma_irow_bound(u32s(f[fi::LI_PARTKEY_CODES as int]), i64s(f[fi::LI_PARTKEY_BASE as int]),
                    u32s(f[fi::LI_KEYIDX_CODES as int]), u64s(f[fi::LI_KEYIDX_BASE as int]), pk::li_bsize(f),
                    kind, pk::li_rows(f), 0);
            }
        }
    }
    if n64 == 0 || n64 > 0xffff_ffff || bs64 == 0 || bs64 > 0xffff_ffff {
        return fb;
    }
    let n = n64 as usize;
    let bs = bs64 as usize;
    let kc = stores.facts.extent_u32(fi::LI_PARTKEY_CODES, 0, stores.facts.part_len(fi::LI_PARTKEY_CODES));
    let kb = stores.facts.extent_i64(fi::LI_PARTKEY_BASE, 0, stores.facts.part_len(fi::LI_PARTKEY_BASE));
    let ic = stores.facts.extent_u32(fi::LI_KEYIDX_CODES, 0, stores.facts.part_len(fi::LI_KEYIDX_CODES));
    let ib = stores.facts.extent_u64(fi::LI_KEYIDX_BASE, 0, stores.facts.part_len(fi::LI_KEYIDX_BASE));
    proof {
        assert(kc@ =~= u32s(f[fi::LI_PARTKEY_CODES as int]));
        assert(kb@ =~= i64s(f[fi::LI_PARTKEY_BASE as int]));
        assert(ic@ =~= u32s(f[fi::LI_KEYIDX_CODES as int]));
        assert(ib@ =~= u64s(f[fi::LI_KEYIDX_BASE as int]));
    }
    let kmin = key_exec(kc, kb, ic, ib, bs, kind, n, 0, Ghost(f));
    let kmax = key_exec(kc, kb, ic, ib, bs, kind, n, n - 1, Ghost(f));
    if kmin < i64::MIN as i128 || kmin > i64::MAX as i128 || kmax < kmin || kmax - kmin + 2 > MAX_KEYS as i128 {
        return fb;
    }
    let dlen = (kmax - kmin + 2) as usize;
    let k0 = kmin as i64;
    let mut dir: Vec<u32> = vec![0u32; dlen];
    let mut i: usize = 0;
    let mut r: usize = 0;
    while r < n
        invariant
            src_ok(f), n as int == pk::li_rows(f), n <= 0xffff_ffff,
            kc@ == u32s(f[fi::LI_PARTKEY_CODES as int]), kb@ == i64s(f[fi::LI_PARTKEY_BASE as int]),
            ic@ == u32s(f[fi::LI_KEYIDX_CODES as int]), ib@ == u64s(f[fi::LI_KEYIDX_BASE as int]),
            bs as int == pk::li_bsize(f), kind == u64s(f[fi::LI_KEYIDX_KIND as int])[0],
            dir@.len() == dlen, 1 <= dlen <= MAX_KEYS,
            r <= n, i <= dlen,
            filled_ok(f, dir@, k0 as int, i as int),
            // every key before `r` is below the next threshold
            i < dlen ==> forall|q: int| 0 <= q < r ==> #[trigger] fkey_at(f, q) < k0 + i,
        decreases n - r,
    {
        let k = key_exec(kc, kb, ic, ib, bs, kind, n, r, Ghost(f));
        while i < dlen && (k0 as i128) + (i as i128) <= k
            invariant
                src_ok(f), n as int == pk::li_rows(f), n <= 0xffff_ffff,
                dir@.len() == dlen, 1 <= dlen <= MAX_KEYS,
                r < n, i <= dlen,
                k as int == fkey_at(f, r as int),
                filled_ok(f, dir@, k0 as int, i as int),
                i < dlen ==> forall|q: int| 0 <= q < r ==> #[trigger] fkey_at(f, q) < k0 + i,
            decreases dlen - i,
        {
            let ghost d0 = dir@;
            dir.set(i, r as u32);
            proof {
                assert forall|x: int| 0 <= x < i + 1 implies #[trigger] entry_ok(f, dir@, k0 as int, x) by {
                    if x < i {
                        assert(entry_ok(f, d0, k0 as int, x));
                        assert(dir@[x] == d0[x]);
                    } else {
                        assert(dir@[x] == r as u32);
                    }
                }
                if i + 1 < dlen {
                    assert forall|q: int| 0 <= q < r implies #[trigger] fkey_at(f, q) < k0 + i + 1 by {}
                }
            }
            i = i + 1;
        }
        proof {
            if i < dlen {
                assert forall|q: int| 0 <= q < r + 1 implies #[trigger] fkey_at(f, q) < k0 + i by {
                    if q == r { assert(fkey_at(f, q) == k as int); }
                }
            }
        }
        r = r + 1;
    }
    while i < dlen
        invariant
            src_ok(f), n as int == pk::li_rows(f), n <= 0xffff_ffff,
            dir@.len() == dlen,
            r == n, i <= dlen,
            filled_ok(f, dir@, k0 as int, i as int),
            i < dlen ==> forall|q: int| 0 <= q < n ==> #[trigger] fkey_at(f, q) < k0 + i,
        decreases dlen - i,
    {
        let ghost d0 = dir@;
        dir.set(i, n as u32);
        proof {
            assert forall|x: int| 0 <= x < i + 1 implies #[trigger] entry_ok(f, dir@, k0 as int, x) by {
                if x < i {
                    assert(entry_ok(f, d0, k0 as int, x));
                    assert(dir@[x] == d0[x]);
                } else {
                    assert(dir@[x] == n as u32);
                }
            }
            if i + 1 < dlen {
                assert forall|q: int| 0 <= q < n implies #[trigger] fkey_at(f, q) < k0 + i + 1 by {}
            }
        }
        i = i + 1;
    }
    (k0, dir)
}

/// factspk's stored relations are facts' (the same declaration).
proof fn lemma_same_relations(db: Database)
    ensures crate::stores::factspk::declaration::stored_relations(db) == crate::stores::facts::declaration::stored_relations(db),
{
    assert(crate::stores::factspk::declaration::stored_cols_t0() =~= crate::stores::facts::declaration::stored_cols_t0());
    assert(crate::stores::factspk::declaration::stored_cols_t1() =~= crate::stores::facts::declaration::stored_cols_t1());
    assert(crate::stores::factspk::declaration::stored_relations(db) =~= crate::stores::facts::declaration::stored_relations(db));
}

/// The parts of facts followed by the directory parts satisfy `represents` for every bound database.
pub fn build(stores: &mut Stores, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        sources_ready(old(stores)@),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(p) ==> forall|db: Database| #[trigger] sources_bound(old(stores)@, db) ==>
            crate::gendb_entry::storage::represents(storage_parts(old(stores)@, owned_parts_view(p@)),
                crate::gendb_entry::storage::stored_relations(db)),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ghost sv = stores@;
    let ghost f = sv.facts;
    let ghost db0 = choose|db: Database| #[trigger] sources_bound(sv, db);
    proof { lemma_src_ok(sv, db0); }
    let (k0, dir) = directory(stores, Ghost(f));
    let ghost dv = dir@;
    let mut parts: Vec<OwnedPart> = Vec::new();
    let mut base: Vec<i64> = Vec::new();
    base.push(k0);
    parts.push(OwnedPart::I64(base));
    parts.push(OwnedPart::U32(dir));
    proof {
        let built = owned_parts_view(parts@);
        assert(built.len() == 2);
        assert(built[0] == owned_part_view(parts@[0]));
        assert(built[1] == owned_part_view(parts@[1]));
        let all = storage_parts(sv, built);
        assert(all == f + built);
        assert(all.len() == pk::FACTSPK_PARTS);
        assert(all.subrange(0, pk::FACTS_PARTS as int) =~= f);
        assert(all[pk::DIR_BASE as int] == built[0]);
        assert(all[pk::DIR_POS as int] == built[1]);
        assert(pk::dir_of(all) == dv);
        assert(pk::kb_of(all) == k0 as int);
        assert forall|r: int| #[trigger] pk::key_at(all, r) == fkey_at(f, r) by {
            assert(all[fi::LI_LAYOUT as int] == f[fi::LI_LAYOUT as int]);
            assert(all[fi::LI_PARTKEY_CODES as int] == f[fi::LI_PARTKEY_CODES as int]);
            assert(all[fi::LI_PARTKEY_BASE as int] == f[fi::LI_PARTKEY_BASE as int]);
            assert(all[fi::LI_KEYIDX_CODES as int] == f[fi::LI_KEYIDX_CODES as int]);
            assert(all[fi::LI_KEYIDX_BASE as int] == f[fi::LI_KEYIDX_BASE as int]);
            assert(all[fi::LI_KEYIDX_KIND as int] == f[fi::LI_KEYIDX_KIND as int]);
        }
        assert(pk::li_rows(all) == pk::li_rows(f)) by {
            assert(all[fi::LI_LAYOUT as int] == f[fi::LI_LAYOUT as int]);
        }
        assert forall|i: int| 0 <= i < pk::dir_of(all).len() implies #[trigger] pk::dir_entry_ok(all, i) by {
            assert(entry_ok(f, dv, k0 as int, i));
        }
        assert(pk::dir_ok(all));
        assert forall|db: Database| #[trigger] sources_bound(sv, db) implies
            pk::represents(all, crate::stores::factspk::declaration::stored_relations(db)) by {
            lemma_same_relations(db);
        }
    }
    Ok(parts)
}

} // verus!
