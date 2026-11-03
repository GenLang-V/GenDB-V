//! Builder of storage `li_partdir`: the 75 parts of `facts` are inherited unchanged; this builder adds the directory
//! header and offsets over the l_partkey key index of facts.
//!
//! Plan: when the key index has kind 2 (a bijection of the stored rows in nondecreasing key order) and the rows fit
//! U32 offsets, one scan along the index positions `p` reads each key `key_at(irow(p))` and appends, for every key
//! entry not yet started, the position `p` (`dir_scan`): entry `e` starts at the first position whose key is at
//! least `kmin + e`; the entries after the last key end at `n`. Otherwise the directory is absent (mode 0).
//!
//! Proof: `src::lemma_src` restates the source facts with this storage's definitions; the scan's invariant
//! (`scan_inv`) places every scanned position in the entry of its key; the inherited parts are the source's parts, so
//! every restated fact carries over (`lemma_same_prefix`).
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::layout::{PartView, owned_parts_view};
use crate::gendb_entry::parallel::Dispatch;
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::gendb_entry::storage::{represents, stored_relations};
use crate::gendb_entry::stored::part_len;
use crate::spec::value::{Database, Row};
use crate::stores::li_partdir::interface::*;
use crate::stores::li_partdir::declaration as D;

pub mod src;
use src::*;

verus! {

/// Largest key span (number of directory entries) the builder accepts beyond `2 n`.
pub const SPAN_SLACK: usize = 1_000_000;

/// `j < m * b` implies `j / b < m`.
proof fn lemma_div_lt(j: int, b: int, m: int)
    requires
        0 <= j < m * b,
        b >= 1,
    ensures
        0 <= j / b < m,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, b);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(j, b);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(j, b);
    assert(b * (j / b) == (j / b) * b) by (nonlinear_arith);
    assert(j / b < m) by (nonlinear_arith) requires (j / b) * b <= j, j < m * b, b >= 1;
}

/// Keys are nondecreasing along the index between any two positions.
proof fn lemma_sorted_le(fp: Seq<PartView>, n: int, a: int, b: int)
    requires
        index_ok(fp, n),
        0 <= a <= b < n,
    ensures
        key_at(fp, irow(fp, a)) <= key_at(fp, irow(fp, b)),
    decreases b - a,
{
    if a < b {
        lemma_sorted_le(fp, n, a, b - 1);
        assert(sorted_at(fp, b - 1));
    }
}

/// The slices of the scan are the source's index and key parts.
pub open spec fn slices_ok(fp: Seq<PartView>, n: int, bs: int, ic: Seq<u32>, ib: Seq<u64>, kc: Seq<u32>, kb: Seq<i64>) -> bool {
    &&& base_ok(fp, n)
    &&& index_ok(fp, n)
    &&& bs == bsize(fp)
    &&& ic == u32s(fp[LI_KEYIDX_CODES as int])
    &&& ib == u64s(fp[LI_KEYIDX_BASE as int])
    &&& kc == u32s(fp[LI_PARTKEY_CODES as int])
    &&& kb == i64s(fp[LI_PARTKEY_BASE as int])
}

/// The stored row at index position `p`.
fn irow_exec(ic: &[u32], ib: &[u64], bs: usize, n: usize, p: usize, Ghost(fp): Ghost<Seq<PartView>>) -> (s: usize)
    requires
        slices_ok(fp, n as int, bs as int, ic@, ib@, u32s(fp[LI_PARTKEY_CODES as int]), i64s(fp[LI_PARTKEY_BASE as int])),
        p < n,
    ensures
        s as int == irow(fp, p as int),
        s < n,
{
    proof {
        lemma_div_lt(p as int, bs as int, ib@.len() as int);
        assert(0 <= irow(fp, p as int) < n);
    }
    (ib[p / bs] + ic[p] as u64) as usize
}

/// The key of stored row `s`.
fn key_exec(kc: &[u32], kb: &[i64], bs: usize, n: usize, s: usize, Ghost(fp): Ghost<Seq<PartView>>) -> (k: i64)
    requires
        base_ok(fp, n as int),
        bs as int == bsize(fp),
        kc@ == u32s(fp[LI_PARTKEY_CODES as int]),
        kb@ == i64s(fp[LI_PARTKEY_BASE as int]),
        s < n,
    ensures
        k as int == key_at(fp, s as int),
{
    proof {
        lemma_div_lt(s as int, bs as int, kb@.len() as int);
        assert(i64::MIN <= key_at(fp, s as int) <= i64::MAX);
    }
    kb[s / bs] + kc[s] as i64
}

/// A directory over the `n` index positions (`kmin`, offsets `offs`): nondecreasing offsets at most `n`, every
/// position inside the entry of its key.
pub open spec fn dir_spec(fp: Seq<PartView>, n: int, kmin: int, offs: Seq<u32>) -> bool {
    &&& offs.len() >= 1
    &&& offs[offs.len() - 1] <= n
    &&& forall|e: int| 0 <= e < offs.len() - 1 ==> #[trigger] offs[e] <= offs[e + 1]
    &&& forall|p: int| 0 <= p < n ==> {
        let e = #[trigger] key_at(fp, irow(fp, p)) - kmin;
        &&& 0 <= e < offs.len() - 1
        &&& offs[e] <= p < offs[e + 1]
    }
}

/// The scan's invariant after positions `0 .. p` with `cur` entries started.
pub open spec fn scan_inv(fp: Seq<PartView>, n: int, kmin: int, offs: Seq<u32>, p: int, cur: int) -> bool {
    &&& offs.len() == cur
    &&& forall|e: int| 0 <= e < cur ==> #[trigger] offs[e] <= p
    &&& forall|e: int| 0 <= e < cur - 1 ==> #[trigger] offs[e] <= offs[e + 1]
    &&& forall|q: int| 0 <= q < p ==> {
        let e = #[trigger] key_at(fp, irow(fp, q)) - kmin;
        &&& 0 <= e < cur
        &&& offs[e] <= q
        &&& e + 1 < cur ==> q < offs[e + 1]
    }
}

/// The directory of the key index: `Some((kmin, offs))` with `dir_spec`, or `None` when the key span is too wide.
fn dir_scan(ic: &[u32], ib: &[u64], kc: &[u32], kb: &[i64], bs: usize, n: usize, Ghost(fp): Ghost<Seq<PartView>>)
    -> (r: Option<(i64, Vec<u32>)>)
    requires
        slices_ok(fp, n as int, bs as int, ic@, ib@, kc@, kb@),
        1 <= n <= u32::MAX,
    ensures
        r matches Some((kmin, offs)) ==> dir_spec(fp, n as int, kmin as int, offs@),
{
    let ghost ni = n as int;
    let s0 = irow_exec(ic, ib, bs, n, 0, Ghost(fp));
    let kmin = key_exec(kc, kb, bs, n, s0, Ghost(fp));
    let sl = irow_exec(ic, ib, bs, n, n - 1, Ghost(fp));
    let kmax = key_exec(kc, kb, bs, n, sl, Ghost(fp));
    proof {
        lemma_sorted_le(fp, ni, 0, ni - 1);
    }
    let span: i128 = kmax as i128 - kmin as i128 + 1;
    if span > 2 * (n as i128) + SPAN_SLACK as i128 || span > 0xffff_fffe {
        return None;
    }
    let nk = span as usize;
    let mut offs: Vec<u32> = Vec::new();
    let mut cur: usize = 0;
    let mut p: usize = 0;
    while p < n
        invariant
            slices_ok(fp, ni, bs as int, ic@, ib@, kc@, kb@),
            ni == n as int,
            1 <= n <= u32::MAX,
            kmin as int == key_at(fp, irow(fp, 0)),
            nk as int == key_at(fp, irow(fp, ni - 1)) - kmin + 1,
            p <= n,
            cur <= nk,
            p == 0 ==> cur == 0,
            p > 0 ==> cur as int == key_at(fp, irow(fp, p - 1)) - kmin + 1,
            scan_inv(fp, ni, kmin as int, offs@, p as int, cur as int),
        decreases n - p,
    {
        let s = irow_exec(ic, ib, bs, n, p, Ghost(fp));
        let k = key_exec(kc, kb, bs, n, s, Ghost(fp));
        proof {
            lemma_sorted_le(fp, ni, 0, p as int);
            lemma_sorted_le(fp, ni, p as int, ni - 1);
            if p > 0 {
                lemma_sorted_le(fp, ni, p - 1, p as int);
            }
        }
        let e = (k as i128 - kmin as i128) as usize;
        while cur <= e
            invariant
                slices_ok(fp, ni, bs as int, ic@, ib@, kc@, kb@),
                ni == n as int,
                1 <= n <= u32::MAX,
                p < n,
                e < nk,
                e as int == key_at(fp, irow(fp, p as int)) - kmin,
                cur <= e + 1,
                scan_inv(fp, ni, kmin as int, offs@, p as int, cur as int),
            decreases e + 1 - cur,
        {
            proof {
                let ghost o = offs@;
                lemma_push_entry_any(fp, ni, kmin as int, o, p as int, cur as int);
            }
            offs.push(p as u32);
            cur = cur + 1;
        }
        proof {
            let ghost o = offs@;
            lemma_step(fp, ni, kmin as int, o, p as int, cur as int);
        }
        p = p + 1;
    }
    while cur <= nk
        invariant
            ni == n as int,
            1 <= n <= u32::MAX,
            nk <= cur <= nk + 1,
            nk <= 0xffff_fffe,
            scan_inv(fp, ni, kmin as int, offs@, ni, cur as int),
        decreases nk + 1 - cur,
    {
        proof {
            let ghost o = offs@;
            lemma_push_end(fp, ni, kmin as int, o, cur as int);
        }
        offs.push(n as u32);
        cur = cur + 1;
    }
    proof {
        assert(offs@.len() == nk + 1);
        assert(offs@[nk as int] <= ni);
        assert forall|q: int| 0 <= q < ni implies {
            let e = #[trigger] key_at(fp, irow(fp, q)) - kmin;
            &&& 0 <= e < offs@.len() - 1
            &&& offs@[e] <= q < offs@[e + 1]
        } by {
            let e = key_at(fp, irow(fp, q)) - kmin;
            lemma_sorted_le(fp, ni, q, ni - 1);
            assert(scan_inv(fp, ni, kmin as int, offs@, ni, cur as int));
            assert(e + 1 < cur);
        }
    }
    Some((kmin, offs))
}

/// One more entry starting at `p` keeps the invariant (inner loop step).
proof fn lemma_push_entry_any(fp: Seq<PartView>, n: int, kmin: int, offs: Seq<u32>, p: int, cur: int)
    requires
        scan_inv(fp, n, kmin, offs, p, cur),
        0 <= p <= u32::MAX,
    ensures
        scan_inv(fp, n, kmin, offs.push(p as u32), p, cur + 1),
{
    let o2 = offs.push(p as u32);
    assert forall|e: int| 0 <= e < cur + 1 implies #[trigger] o2[e] <= p by {
        if e < cur {
            assert(o2[e] == offs[e]);
        }
    }
    assert forall|e: int| 0 <= e < cur implies #[trigger] o2[e] <= o2[e + 1] by {
        if e < cur - 1 {
            assert(offs[e] <= offs[e + 1]);
        } else {
            assert(offs[e] <= p);
        }
    }
    assert forall|q: int| 0 <= q < p implies {
        let e = #[trigger] key_at(fp, irow(fp, q)) - kmin;
        &&& 0 <= e < cur + 1
        &&& o2[e] <= q
        &&& e + 1 < cur + 1 ==> q < o2[e + 1]
    } by {
        let e = key_at(fp, irow(fp, q)) - kmin;
        assert(0 <= e < cur && offs[e] <= q);
        assert(o2[e] == offs[e]);
        if e + 1 < cur {
            assert(o2[e + 1] == offs[e + 1]);
        } else {
            assert(o2[e + 1] == p);
            assert(q < p);
        }
    }
}

/// After the entries up to the key of position `p` are started, position `p` is placed.
proof fn lemma_step(fp: Seq<PartView>, n: int, kmin: int, offs: Seq<u32>, p: int, cur: int)
    requires
        scan_inv(fp, n, kmin, offs, p, cur),
        0 <= p < n,
        cur == key_at(fp, irow(fp, p)) - kmin + 1,
        key_at(fp, irow(fp, p)) - kmin >= 0,
    ensures
        scan_inv(fp, n, kmin, offs, p + 1, cur),
{
    assert forall|e: int| 0 <= e < cur implies #[trigger] offs[e] <= p + 1 by {
        assert(offs[e] <= p);
    }
    assert forall|q: int| 0 <= q < p + 1 implies {
        let e = #[trigger] key_at(fp, irow(fp, q)) - kmin;
        &&& 0 <= e < cur
        &&& offs[e] <= q
        &&& e + 1 < cur ==> q < offs[e + 1]
    } by {
        if q == p {
            let e = key_at(fp, irow(fp, q)) - kmin;
            assert(e == cur - 1);
            assert(offs[e] <= p);
        }
    }
}

/// The entries after the last key end at `n`.
proof fn lemma_push_end(fp: Seq<PartView>, n: int, kmin: int, offs: Seq<u32>, cur: int)
    requires
        scan_inv(fp, n, kmin, offs, n, cur),
        0 <= n <= u32::MAX,
    ensures
        scan_inv(fp, n, kmin, offs.push(n as u32), n, cur + 1),
{
    lemma_push_entry_any(fp, n, kmin, offs, n, cur);
}

/// The parts of this storage agree with the source parts on every inherited part, so every restated value agrees.
proof fn lemma_same_prefix(fp: Seq<PartView>, parts: Seq<PartView>)
    requires
        fp.len() == FACTS_PARTS,
        parts.len() >= FACTS_PARTS,
        forall|k: int| 0 <= k < FACTS_PARTS ==> #[trigger] parts[k] == fp[k],
    ensures
        n_rows(parts) == n_rows(fp),
        bsize(parts) == bsize(fp),
        forall|s: int| #[trigger] map_at(parts, s) == map_at(fp, s),
        forall|s: int| #[trigger] key_at(parts, s) == key_at(fp, s),
        forall|s: int| #[trigger] qty_at(parts, s) == qty_at(fp, s),
        forall|s: int| #[trigger] price_at(parts, s) == price_at(fp, s),
        forall|p: int| #[trigger] irow(parts, p) == irow(fp, p),
        parts[LI_LAYOUT as int] == fp[LI_LAYOUT as int],
        parts[LI_PERM_CODES as int] == fp[LI_PERM_CODES as int],
        parts[LI_PERM_BASE as int] == fp[LI_PERM_BASE as int],
        parts[LI_PARTKEY_CODES as int] == fp[LI_PARTKEY_CODES as int],
        parts[LI_PARTKEY_BASE as int] == fp[LI_PARTKEY_BASE as int],
        parts[LI_QUANTITY_CODES as int] == fp[LI_QUANTITY_CODES as int],
        parts[LI_QUANTITY_BASE as int] == fp[LI_QUANTITY_BASE as int],
        parts[LI_EXTENDEDPRICE_CODES as int] == fp[LI_EXTENDEDPRICE_CODES as int],
        parts[LI_EXTENDEDPRICE_BASE as int] == fp[LI_EXTENDEDPRICE_BASE as int],
        parts[LI_KEYIDX_CODES as int] == fp[LI_KEYIDX_CODES as int],
        parts[LI_KEYIDX_BASE as int] == fp[LI_KEYIDX_BASE as int],
{
    assert(parts[LI_LAYOUT as int] == fp[LI_LAYOUT as int]);
    assert(parts[LI_PERM_CODES as int] == fp[LI_PERM_CODES as int]);
    assert(parts[LI_PERM_BASE as int] == fp[LI_PERM_BASE as int]);
    assert(parts[LI_PARTKEY_CODES as int] == fp[LI_PARTKEY_CODES as int]);
    assert(parts[LI_PARTKEY_BASE as int] == fp[LI_PARTKEY_BASE as int]);
    assert(parts[LI_QUANTITY_CODES as int] == fp[LI_QUANTITY_CODES as int]);
    assert(parts[LI_QUANTITY_BASE as int] == fp[LI_QUANTITY_BASE as int]);
    assert(parts[LI_EXTENDEDPRICE_CODES as int] == fp[LI_EXTENDEDPRICE_CODES as int]);
    assert(parts[LI_EXTENDEDPRICE_BASE as int] == fp[LI_EXTENDEDPRICE_BASE as int]);
    assert(parts[LI_KEYIDX_CODES as int] == fp[LI_KEYIDX_CODES as int]);
    assert(parts[LI_KEYIDX_BASE as int] == fp[LI_KEYIDX_BASE as int]);
}

/// The inherited facts of the source carry over to this storage's parts.
proof fn lemma_built_rows(fp: Seq<PartView>, parts: Seq<PartView>, rel: Seq<Row>)
    requires
        src_ok(fp, rel),
        parts.len() == LI_PARTDIR_PARTS,
        forall|k: int| 0 <= k < FACTS_PARTS ==> #[trigger] parts[k] == fp[k],
    ensures
        li_shape(parts, rel.len() as int),
        row_map_ok(parts, rel.len() as int),
        rows_ok(parts, rel),
{
    let n = rel.len() as int;
    lemma_same_prefix(fp, parts);
    assert(li_shape(parts, n));
    assert forall|r: int| 0 <= r < n implies #[trigger] mapped(parts, n, r) by {
        assert(mapped(fp, n, r));
        let s = choose|s: int| 0 <= s < n && #[trigger] map_at(fp, s) == r;
        assert(map_at(parts, s) == r);
    }
    assert forall|s: int| 0 <= s < n implies 0 <= #[trigger] map_at(parts, s) < n by {
        assert(map_at(parts, s) == map_at(fp, s));
    }
    assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b implies
        #[trigger] map_at(parts, a) != #[trigger] map_at(parts, b) by {
        assert(map_at(parts, a) == map_at(fp, a));
        assert(map_at(parts, b) == map_at(fp, b));
    }
    assert forall|s: int| 0 <= s < rel.len() implies
        rel[#[trigger] map_at(parts, s)] == li_row(key_at(parts, s), qty_at(parts, s), price_at(parts, s)) by {
        assert(rel[map_at(fp, s)] == li_row(key_at(fp, s), qty_at(fp, s), price_at(fp, s)));
    }
}

/// A present directory: the scan's directory over the source's key index.
proof fn lemma_dir_some(fp: Seq<PartView>, parts: Seq<PartView>, n: int, kmin: i64, offs: Seq<u32>)
    requires
        parts.len() == LI_PARTDIR_PARTS,
        forall|k: int| 0 <= k < FACTS_PARTS ==> #[trigger] parts[k] == fp[k],
        fp.len() == FACTS_PARTS,
        parts[DIR_META as int] == PartView::I64(seq![MODE_DIRECTORY, kmin]),
        parts[DIR_OFFS as int] == PartView::U32(offs),
        index_ok(fp, n),
        dir_spec(fp, n, kmin as int, offs),
    ensures
        dir_ok(parts, n),
{
    hide(dir_spec);
    hide(index_ok);
    lemma_same_prefix(fp, parts);
    assert(dir_meta(parts) == seq![MODE_DIRECTORY, kmin]);
    assert(has_dir(parts));
    assert(dir_offs(parts) == offs);
    assert(dir_kmin(parts) == kmin);
    assert forall|p: int| 0 <= p < n implies 0 <= #[trigger] irow(parts, p) < n by {
        reveal(index_ok);
        assert(irow(parts, p) == irow(fp, p));
    }
    assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b implies
        #[trigger] irow(parts, a) != #[trigger] irow(parts, b) by {
        reveal(index_ok);
        assert(irow(parts, a) == irow(fp, a));
        assert(irow(parts, b) == irow(fp, b));
    }
    assert(for_len_ok(u32s(parts[LI_KEYIDX_CODES as int]).len() as int, u64s(parts[LI_KEYIDX_BASE as int]).len() as int,
                n, bsize(parts))) by {
        reveal(index_ok);
    }
    assert(parts[LI_KEYIDX_CODES as int] is U32 && parts[LI_KEYIDX_BASE as int] is U64) by {
        reveal(index_ok);
    }
    assert forall|s: int| 0 <= s < n implies #[trigger] indexed(parts, n, s) by {
        reveal(index_ok);
        assert(indexed(fp, n, s));
        let p = choose|p: int| 0 <= p < n && #[trigger] irow(fp, p) == s;
        assert(irow(parts, p) == irow(fp, p));
    }
    assert forall|p: int| 0 <= p < n implies #[trigger] in_entry(parts, p) by {
        reveal(dir_spec);
        assert(irow(parts, p) == irow(fp, p));
        assert(key_at(parts, irow(parts, p)) == key_at(fp, irow(fp, p)));
    }
    assert(dir_offs(parts).len() >= 1 && dir_offs(parts)[dir_nkeys(parts)] <= n) by {
        reveal(dir_spec);
    }
    assert forall|e: int| 0 <= e < dir_nkeys(parts) implies #[trigger] dir_offs(parts)[e] <= dir_offs(parts)[e + 1] by {
        reveal(dir_spec);
        assert(offs[e] <= offs[e + 1]);
    }
}

/// The directory parts: absent, or the scan's directory over the source's key index.
proof fn lemma_built_dir(fp: Seq<PartView>, parts: Seq<PartView>, n: int, dir: Option<(i64, Seq<u32>)>)
    requires
        parts.len() == LI_PARTDIR_PARTS,
        forall|k: int| 0 <= k < FACTS_PARTS ==> #[trigger] parts[k] == fp[k],
        fp.len() == FACTS_PARTS,
        parts[DIR_META as int] == PartView::I64(match dir { Some((kmin, offs)) => seq![MODE_DIRECTORY, kmin], None => seq![0i64, 0i64] }),
        parts[DIR_OFFS as int] == PartView::U32(match dir { Some((kmin, offs)) => offs, None => seq![0u32] }),
        dir matches Some((kmin, offs)) ==> index_ok(fp, n) && dir_spec(fp, n, kmin as int, offs),
    ensures
        dir_ok(parts, n),
{
    match dir {
        Some((kmin, offs)) => {
            lemma_dir_some(fp, parts, n, kmin, offs);
        },
        None => {
            assert(dir_meta(parts) == seq![0i64, 0i64]);
            assert(!has_dir(parts));
        },
    }
}

/// The new storage's parts represent the stored relations of every database bound to the source.
proof fn lemma_built(sv: StoresView, db: Database, built: Seq<PartView>, dir: Option<(i64, Seq<u32>)>, n: int)
    requires
        sources_bound(sv, db),
        n == n_rows(sv.facts),
        built.len() == 2,
        built[0] == PartView::I64(match dir { Some((kmin, offs)) => seq![MODE_DIRECTORY, kmin], None => seq![0i64, 0i64] }),
        built[1] == PartView::U32(match dir { Some((kmin, offs)) => offs, None => seq![0u32] }),
        dir matches Some((kmin, offs)) ==> src::kind_of(sv.facts) == 2 && dir_spec(sv.facts, n, kmin as int, offs),
    ensures
        represents(storage_parts(sv, built), stored_relations(db)),
{
    let fp = sv.facts;
    let parts = storage_parts(sv, built);
    let rels = stored_relations(db);
    lemma_src(sv, db);
    D::lemma_stored_relations(db);
    let rel = rels[0];
    assert(parts.len() == LI_PARTDIR_PARTS);
    assert forall|k: int| 0 <= k < FACTS_PARTS implies #[trigger] parts[k] == fp[k] by {}
    assert(parts[DIR_META as int] == built[0]);
    assert(parts[DIR_OFFS as int] == built[1]);
    assert(rel.len() == n);
    lemma_built_rows(fp, parts, rel);
    lemma_built_dir(fp, parts, n, dir);
}

/// Build the directory parts (the inherited parts of `facts` come first, unchanged).
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
    let ghost fp = sv.facts;
    let ghost db0 = choose|db: Database| #[trigger] sources_bound(sv, db);
    proof {
        lemma_src(sv, db0);
    }
    let ghost n0 = n_rows(fp);
    let lay = stores.facts.extent_u64(LI_LAYOUT, 0, 2);
    let n = stores.facts.part_len(LI_PARTKEY_CODES);
    let bs64 = lay[1];
    let kv = stores.facts.extent_u64(src::LI_KEYIDX_KIND, 0, 1);
    proof {
        assert(n as int == n0);
        assert(bs64 as int == bsize(fp));
    }
    let dir: Option<(i64, Vec<u32>)> = if kv[0] == 2 && n >= 1 && n <= 0xffff_ffff && bs64 <= n as u64 {
        let bs = bs64 as usize;
        proof {
            assert(src::kind_of(fp) == 2);
            assert(index_ok(fp, n0));
        }
        let nib = stores.facts.part_len(LI_KEYIDX_BASE);
        let nkb = stores.facts.part_len(LI_PARTKEY_BASE);
        let ic = stores.facts.extent_u32(LI_KEYIDX_CODES, 0, n);
        let ib = stores.facts.extent_u64(LI_KEYIDX_BASE, 0, nib);
        let kc = stores.facts.extent_u32(LI_PARTKEY_CODES, 0, n);
        let kb = stores.facts.extent_i64(LI_PARTKEY_BASE, 0, nkb);
        proof {
            assert(ic@ =~= u32s(fp[LI_KEYIDX_CODES as int]));
            assert(ib@ =~= u64s(fp[LI_KEYIDX_BASE as int]));
            assert(kc@ =~= u32s(fp[LI_PARTKEY_CODES as int]));
            assert(kb@ =~= i64s(fp[LI_PARTKEY_BASE as int]));
        }
        dir_scan(ic, ib, kc, kb, bs, n, Ghost(fp))
    } else {
        None
    };
    let ghost gdir: Option<(i64, Seq<u32>)> = match &dir {
        Some((kmin, offs)) => Some((*kmin, offs@)),
        None => None,
    };
    let mut meta: Vec<i64> = Vec::new();
    let offs: Vec<u32> = match dir {
        Some((kmin, offs)) => {
            meta.push(MODE_DIRECTORY);
            meta.push(kmin);
            offs
        },
        None => {
            meta.push(0);
            meta.push(0);
            let mut z: Vec<u32> = Vec::new();
            z.push(0);
            z
        },
    };
    let ghost meta_v = meta@;
    let ghost offs_v = offs@;
    let mut out: Vec<OwnedPart> = Vec::new();
    out.push(OwnedPart::I64(meta));
    out.push(OwnedPart::U32(offs));
    proof {
        let built = owned_parts_view(out@);
        assert(built.len() == 2);
        assert(built[0] == PartView::I64(meta_v));
        assert(built[1] == PartView::U32(offs_v));
        match gdir {
            Some((kmin, o)) => {
                assert(meta_v =~= seq![MODE_DIRECTORY, kmin]);
            },
            None => {
                assert(meta_v =~= seq![0i64, 0i64]);
                assert(offs_v =~= seq![0u32]);
            },
        }
        assert forall|db: Database| #[trigger] sources_bound(sv, db)
            implies represents(storage_parts(sv, built), stored_relations(db)) by {
            lemma_built(sv, db, built, gdir, n0);
        }
    }
    Ok(out)
}

} // verus!
