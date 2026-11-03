//! Builder of storage `li_pkship`: the 75 parts of `facts` are inherited unchanged; this builder adds a composite
//! index of lineitem on `(l_partkey, l_shipinstruct, l_shipmode)`.
//!
//! Plan (when facts' l_partkey key index has kind 2, the rows fit U32 positions, the key span is small enough for a
//! dense directory and every l_shipinstruct / l_shipmode dictionary index is below 16):
//! 1. `dirscan::dir_scan`: the directory over facts' key index (entry `e` = positions of key `kmin + e`);
//! 2. `assemble::ship_check`: every dictionary index below 16, so the ship key `16 * si + sm` fits a byte;
//! 3. one worker task per run of entries (`task::IdxTask`): each position's stored row `s` and ship key `c` are
//!    packed as `c * 2^32 + s`, each entry's packed values are sorted ascending (`sort64::msort64`, so by ship
//!    key), then unpacked into the task's index rows and ship keys;
//! 4. the calling thread concatenates the tasks' outputs (`assemble::build_index`) and checks that the rows are a
//!    bijection (`check_perm`).
//! Otherwise (or when the check fails) the index is absent (mode 0).
//!
//! Proof: `src::lemma_src` restates the source facts with this storage's definitions; each task proves, for every
//! entry of its run, that the entry's positions hold rows of the entry's key with their ship keys, in ship key
//! order (`task::entry_out`), because sorting only moves elements that all satisfy that property; the concatenation
//! keeps it for all entries, which gives `in_entry`, `ship_key_ok` and `ship_sorted_at` for every position.
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::layout::{PartView, owned_parts_view};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::gendb_entry::storage::{represents, stored_relations};
use crate::spec::value::{Database, Row};
use crate::stores::li_pkship::interface::*;
use crate::stores::li_pkship::declaration as D;

pub mod src;
pub mod dirscan;
pub mod sort64;
pub mod perm;
pub mod task;
pub mod assemble;
use src::*;
use dirscan::*;
use task::*;
use assemble::*;
use perm::{check_perm, perm_view_ok, covered_u32};

verus! {

/// The parts of this storage agree with the source parts on every inherited part.
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
        forall|s: int| #[trigger] row_at(parts, s) == row_at(fp, s),
        forall|s: int| #[trigger] dict_idx_ok(parts, s) == dict_idx_ok(fp, s),
        forall|s: int| #[trigger] si_at(parts, s) == si_at(fp, s),
        forall|s: int| #[trigger] sm_at(parts, s) == sm_at(fp, s),
        forall|s: int| #[trigger] ship_of(parts, s) == ship_of(fp, s),
        parts[LI_LAYOUT as int] == fp[LI_LAYOUT as int],
        parts[LI_PERM_CODES as int] == fp[LI_PERM_CODES as int],
        parts[LI_PERM_BASE as int] == fp[LI_PERM_BASE as int],
        parts[LI_PARTKEY_CODES as int] == fp[LI_PARTKEY_CODES as int],
        parts[LI_PARTKEY_BASE as int] == fp[LI_PARTKEY_BASE as int],
        parts[LI_QUANTITY_CODES as int] == fp[LI_QUANTITY_CODES as int],
        parts[LI_QUANTITY_BASE as int] == fp[LI_QUANTITY_BASE as int],
        parts[LI_PRICE_CODES as int] == fp[LI_PRICE_CODES as int],
        parts[LI_PRICE_BASE as int] == fp[LI_PRICE_BASE as int],
        parts[LI_DISCOUNT_CODES as int] == fp[LI_DISCOUNT_CODES as int],
        parts[LI_DISCOUNT_BASE as int] == fp[LI_DISCOUNT_BASE as int],
        parts[LI_SI_CODES as int] == fp[LI_SI_CODES as int],
        parts[LI_SI_BASE as int] == fp[LI_SI_BASE as int],
        parts[LI_SI_DOFFS as int] == fp[LI_SI_DOFFS as int],
        parts[LI_SI_DBYTES as int] == fp[LI_SI_DBYTES as int],
        parts[LI_SM_CODES as int] == fp[LI_SM_CODES as int],
        parts[LI_SM_BASE as int] == fp[LI_SM_BASE as int],
        parts[LI_SM_DOFFS as int] == fp[LI_SM_DOFFS as int],
        parts[LI_SM_DBYTES as int] == fp[LI_SM_DBYTES as int],
{
    assert(parts[LI_LAYOUT as int] == fp[LI_LAYOUT as int]);
    assert(parts[LI_PERM_CODES as int] == fp[LI_PERM_CODES as int]);
    assert(parts[LI_PERM_BASE as int] == fp[LI_PERM_BASE as int]);
    assert(parts[LI_PARTKEY_CODES as int] == fp[LI_PARTKEY_CODES as int]);
    assert(parts[LI_PARTKEY_BASE as int] == fp[LI_PARTKEY_BASE as int]);
    assert(parts[LI_QUANTITY_CODES as int] == fp[LI_QUANTITY_CODES as int]);
    assert(parts[LI_QUANTITY_BASE as int] == fp[LI_QUANTITY_BASE as int]);
    assert(parts[LI_PRICE_CODES as int] == fp[LI_PRICE_CODES as int]);
    assert(parts[LI_PRICE_BASE as int] == fp[LI_PRICE_BASE as int]);
    assert(parts[LI_DISCOUNT_CODES as int] == fp[LI_DISCOUNT_CODES as int]);
    assert(parts[LI_DISCOUNT_BASE as int] == fp[LI_DISCOUNT_BASE as int]);
    assert(parts[LI_SI_CODES as int] == fp[LI_SI_CODES as int]);
    assert(parts[LI_SI_BASE as int] == fp[LI_SI_BASE as int]);
    assert(parts[LI_SI_DOFFS as int] == fp[LI_SI_DOFFS as int]);
    assert(parts[LI_SI_DBYTES as int] == fp[LI_SI_DBYTES as int]);
    assert(parts[LI_SM_CODES as int] == fp[LI_SM_CODES as int]);
    assert(parts[LI_SM_BASE as int] == fp[LI_SM_BASE as int]);
    assert(parts[LI_SM_DOFFS as int] == fp[LI_SM_DOFFS as int]);
    assert(parts[LI_SM_DBYTES as int] == fp[LI_SM_DBYTES as int]);
}

/// The inherited facts of the source carry over to this storage's parts.
proof fn lemma_built_rows(fp: Seq<PartView>, parts: Seq<PartView>, rel: Seq<Row>)
    requires
        src_ok(fp, rel),
        parts.len() == LI_PKSHIP_PARTS,
        forall|k: int| 0 <= k < FACTS_PARTS ==> #[trigger] parts[k] == fp[k],
    ensures
        li_shape(parts, rel.len() as int),
        row_map_ok(parts, rel.len() as int),
        rows_ok(parts, rel),
{
    let n = rel.len() as int;
    lemma_same_prefix(fp, parts);
    assert(si_offs(parts) == si_offs(fp) && si_bytes(parts) == si_bytes(fp));
    assert(sm_offs(parts) == sm_offs(fp) && sm_bytes(parts) == sm_bytes(fp));
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
    assert forall|s: int| 0 <= s < rel.len() implies rel[#[trigger] map_at(parts, s)] == row_at(parts, s) by {
        assert(rel[map_at(fp, s)] == row_at(fp, s));
    }
    assert forall|s: int| 0 <= s < rel.len() implies #[trigger] dict_idx_ok(parts, s) by {
        assert(dict_idx_ok(fp, s));
    }
}

/// Position `p` of entry `e`: its row has the entry's key and its ship key.
proof fn lemma_entry_at(fp: Seq<PartView>, n: int, kmin: int, offs: Seq<u32>, rows: Seq<u32>,
    ships: Seq<u8>, e: int, p: int)
    requires entry_out(fp, n, kmin, offs, 0, rows, ships, e), offs[e] <= p < offs[e + 1],
    ensures
        rows[p] < n,
        key_at(fp, rows[p] as int) == kmin + e,
        ships[p] == ship_of(fp, rows[p] as int),
        p + 1 < offs[e + 1] ==> ships[p] <= ships[p + 1],
{
    reveal(entry_out);
}

/// The index facts of position `p`.
proof fn lemma_idx_pos(fp: Seq<PartView>, parts: Seq<PartView>, n: int, kmin: i64, offs: Seq<u32>,
    rows: Seq<u32>, ships: Seq<u8>, p: int)
    requires
        forall|k: int| 0 <= k < FACTS_PARTS ==> #[trigger] parts[k] == fp[k],
        parts.len() == LI_PKSHIP_PARTS, fp.len() == FACTS_PARTS,
        idx_meta(parts) == seq![MODE_INDEX, kmin],
        idx_offs(parts) == offs, idx_rows(parts) == rows, idx_ship(parts) == ships,
        offs.len() >= 1, offs[0] == 0, offs[offs.len() - 1] == n,
        ents_mono(offs, offs.len() - 1),
        forall|e: int| 0 <= e < offs.len() - 1 ==> #[trigger] entry_out(fp, n, kmin as int, offs, 0, rows, ships, e),
        ships_in(fp, n),
        0 <= p < n,
    ensures
        in_entry(parts, p),
        ship_key_ok(parts, p),
        p + 1 < n ==> ship_sorted_at(parts, p),
{
    lemma_same_prefix(fp, parts);
    let nk = offs.len() - 1;
    let e = lemma_find_entry_m(offs, nk, p);
    lemma_entry_at(fp, n, kmin as int, offs, rows, ships, e, p);
    assert(key_at(parts, irow(parts, p)) == key_at(fp, rows[p] as int));
    reveal(ships_in);
    assert(0 <= si_at(fp, rows[p] as int) < 16 && 0 <= sm_at(fp, rows[p] as int) < 16);
    if p + 1 < n {
        let f = lemma_find_entry_m(offs, nk, p + 1);
        lemma_entry_at(fp, n, kmin as int, offs, rows, ships, f, p + 1);
        assert(key_at(parts, irow(parts, p + 1)) == key_at(fp, rows[p + 1] as int));
        if key_at(parts, irow(parts, p)) == key_at(parts, irow(parts, p + 1)) {
            assert(e == f);
        }
    }
}

/// A present index: the directory, the rows and the ship keys of `build_index`, checked a bijection.
proof fn lemma_idx_some(fp: Seq<PartView>, parts: Seq<PartView>, n: int, kmin: i64, offs: Seq<u32>,
    rows: Seq<u32>, ships: Seq<u8>)
    requires
        parts.len() == LI_PKSHIP_PARTS,
        forall|k: int| 0 <= k < FACTS_PARTS ==> #[trigger] parts[k] == fp[k],
        fp.len() == FACTS_PARTS,
        n >= 1,
        parts[IDX_META as int] == PartView::I64(seq![MODE_INDEX, kmin]),
        parts[IDX_OFFS as int] == PartView::U32(offs),
        parts[IDX_ROWS as int] == PartView::U32(rows),
        parts[IDX_SHIP as int] == PartView::U8(ships),
        dir_spec(fp, n, kmin as int, offs),
        rows.len() == n, ships.len() == n,
        perm_view_ok(rows, n),
        forall|e: int| 0 <= e < offs.len() - 1 ==> #[trigger] entry_out(fp, n, kmin as int, offs, 0, rows, ships, e),
        ships_in(fp, n),
    ensures
        idx_ok(parts, n),
{
    lemma_dir_ends(fp, n, kmin as int, offs);
    lemma_dir_mono(fp, n, kmin as int, offs);
    assert(idx_meta(parts) == seq![MODE_INDEX, kmin]);
    assert(has_idx(parts));
    assert(idx_offs(parts) == offs);
    assert(idx_rows(parts) == rows);
    assert(idx_ship(parts) == ships);
    assert forall|p: int| 0 <= p < n implies 0 <= #[trigger] irow(parts, p) < n by {
        assert(rows[p] < n);
    }
    assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b implies
        #[trigger] irow(parts, a) != #[trigger] irow(parts, b) by {
        assert(rows[a] != rows[b]);
    }
    assert forall|s: int| 0 <= s < n implies #[trigger] indexed(parts, n, s) by {
        assert(covered_u32(rows, s));
        let p = choose|p: int| 0 <= p < rows.len() && rows[p] == s;
        assert(irow(parts, p) == s);
    }
    assert forall|p: int| 0 <= p < n implies #[trigger] in_entry(parts, p) by {
        lemma_idx_pos(fp, parts, n, kmin, offs, rows, ships, p);
    }
    assert forall|p: int| 0 <= p < n implies #[trigger] ship_key_ok(parts, p) by {
        lemma_idx_pos(fp, parts, n, kmin, offs, rows, ships, p);
    }
    assert forall|p: int| 0 <= p < n - 1 implies #[trigger] ship_sorted_at(parts, p) by {
        lemma_idx_pos(fp, parts, n, kmin, offs, rows, ships, p);
    }
    assert forall|e: int| 0 <= e < idx_nkeys(parts) implies #[trigger] idx_offs(parts)[e] <= idx_offs(parts)[e + 1] by {
        lemma_ents_le(offs, offs.len() - 1, e, e + 1);
    }
}

/// The new storage's parts represent the stored relations of every database bound to the source.
proof fn lemma_built(sv: StoresView, db: Database, built: Seq<PartView>, idx: Option<(i64, Seq<u32>, Seq<u32>, Seq<u8>)>)
    requires
        sources_bound(sv, db),
        built.len() == 4,
        built[0] == PartView::I64(match idx { Some((kmin, o, r, d)) => seq![MODE_INDEX, kmin], None => seq![0i64, 0i64] }),
        built[1] == PartView::U32(match idx { Some((kmin, o, r, d)) => o, None => seq![0u32] }),
        built[2] == PartView::U32(match idx { Some((kmin, o, r, d)) => r, None => Seq::<u32>::empty() }),
        built[3] == PartView::U8(match idx { Some((kmin, o, r, d)) => d, None => Seq::<u8>::empty() }),
        idx matches Some((kmin, o, r, d)) ==> {
            let n = n_rows(sv.facts);
            &&& n >= 1
            &&& kind_of(sv.facts) == 2
            &&& dir_spec(sv.facts, n, kmin as int, o)
            &&& r.len() == n && d.len() == n
            &&& perm_view_ok(r, n)
            &&& forall|e: int| 0 <= e < o.len() - 1 ==> #[trigger] entry_out(sv.facts, n, kmin as int, o, 0, r, d, e)
            &&& ships_in(sv.facts, n)
        },
    ensures
        represents(storage_parts(sv, built), stored_relations(db)),
{
    let fp = sv.facts;
    let parts = storage_parts(sv, built);
    let rels = stored_relations(db);
    lemma_src(sv, db);
    D::lemma_stored_relations(db);
    let rel = rels[0];
    assert(parts.len() == LI_PKSHIP_PARTS);
    assert forall|k: int| 0 <= k < FACTS_PARTS implies #[trigger] parts[k] == fp[k] by {}
    assert(parts[IDX_META as int] == built[0]);
    assert(parts[IDX_OFFS as int] == built[1]);
    assert(parts[IDX_ROWS as int] == built[2]);
    assert(parts[IDX_SHIP as int] == built[3]);
    lemma_built_rows(fp, parts, rel);
    match idx {
        Some((kmin, o, r, d)) => {
            lemma_idx_some(fp, parts, rel.len() as int, kmin, o, r, d);
        },
        None => {
            assert(idx_meta(parts) == seq![0i64, 0i64]);
            assert(!has_idx(parts));
        },
    }
}

pub fn build(stores: &mut Stores, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        sources_ready(old(stores)@),
        1 <= workers <= MAX_WORKERS,
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
    let lay = stores.facts.extent_u64(LI_LAYOUT, 0, 2);
    let n = stores.facts.part_len(LI_PARTKEY_CODES);
    let bs64 = lay[1];
    let kv = stores.facts.extent_u64(LI_KEYIDX_KIND, 0, 1);
    proof {
        assert(n as int == n_rows(fp));
        assert(bs64 as int == bsize(fp));
    }
    let mut idx: Option<(i64, Vec<u32>, Vec<u32>, Vec<u8>)> = None;
    if kv[0] == 2 && n >= 1 && n <= 0xffff_ffff && bs64 <= n as u64 {
        let bs = bs64 as usize;
        proof {
            assert(kind_of(fp) == 2);
            assert(index_ok(fp, n as int));
        }
        let nib = stores.facts.part_len(LI_KEYIDX_BASE);
        let nkb = stores.facts.part_len(LI_PARTKEY_BASE);
        let nsb = stores.facts.part_len(LI_SI_BASE);
        let nmb = stores.facts.part_len(LI_SM_BASE);
        let ic = stores.facts.extent_u32(LI_KEYIDX_CODES, 0, n);
        let ib = stores.facts.extent_u64(LI_KEYIDX_BASE, 0, nib);
        let kc = stores.facts.extent_u32(LI_PARTKEY_CODES, 0, n);
        let kb = stores.facts.extent_i64(LI_PARTKEY_BASE, 0, nkb);
        let sc = stores.facts.extent_u8(LI_SI_CODES, 0, n);
        let sb = stores.facts.extent_u64(LI_SI_BASE, 0, nsb);
        let mc = stores.facts.extent_u8(LI_SM_CODES, 0, n);
        let mb = stores.facts.extent_u64(LI_SM_BASE, 0, nmb);
        proof {
            assert(ic@ =~= u32s(fp[LI_KEYIDX_CODES as int]));
            assert(ib@ =~= u64s(fp[LI_KEYIDX_BASE as int]));
            assert(kc@ =~= u32s(fp[LI_PARTKEY_CODES as int]));
            assert(kb@ =~= i64s(fp[LI_PARTKEY_BASE as int]));
            assert(sc@ =~= u8s(fp[LI_SI_CODES as int]));
            assert(sb@ =~= u64s(fp[LI_SI_BASE as int]));
            assert(mc@ =~= u8s(fp[LI_SM_CODES as int]));
            assert(mb@ =~= u64s(fp[LI_SM_BASE as int]));
        }
        proof {
            reveal(task_src);
            assert(task_src(fp, n as int, bs as int, ic@, ib@, sc@, sb@, mc@, mb@));
        }
        if ship_check(sc, sb, mc, mb, bs, n, Ghost(fp)) {
            match dir_scan(ic, ib, kc, kb, bs, n, Ghost(fp)) {
                Some((kmin, offs)) => {
                    match build_index(ic, ib, sc, sb, mc, mb, bs, n, kmin, &offs, workers, dispatch, Ghost(fp)) {
                        Ok((rows, ships)) => {
                            if check_perm(&rows) {
                                idx = Some((kmin, offs, rows, ships));
                            }
                        },
                        Err(e) => return Err(e),
                    }
                },
                None => {},
            }
        }
    }
    let ghost gidx: Option<(i64, Seq<u32>, Seq<u32>, Seq<u8>)> = match &idx {
        Some((kmin, o, r, d)) => Some((*kmin, o@, r@, d@)),
        None => None,
    };
    let mut meta: Vec<i64> = Vec::new();
    let (offs, rows, ships): (Vec<u32>, Vec<u32>, Vec<u8>) = match idx {
        Some((kmin, o, r, d)) => {
            meta.push(MODE_INDEX);
            meta.push(kmin);
            (o, r, d)
        },
        None => {
            meta.push(0);
            meta.push(0);
            let mut z: Vec<u32> = Vec::new();
            z.push(0);
            (z, Vec::new(), Vec::new())
        },
    };
    let ghost (mv, ov, rv, dv) = (meta@, offs@, rows@, ships@);
    let mut out: Vec<OwnedPart> = Vec::new();
    out.push(OwnedPart::I64(meta));
    out.push(OwnedPart::U32(offs));
    out.push(OwnedPart::U32(rows));
    out.push(OwnedPart::U8(ships));
    proof {
        let built = owned_parts_view(out@);
        assert(built.len() == 4);
        assert(built[0] == PartView::I64(mv));
        assert(built[1] == PartView::U32(ov));
        assert(built[2] == PartView::U32(rv));
        assert(built[3] == PartView::U8(dv));
        match gidx {
            Some((kmin, o, r, d)) => {
                assert(mv =~= seq![MODE_INDEX, kmin]);
            },
            None => {
                assert(mv =~= seq![0i64, 0i64]);
                assert(ov =~= seq![0u32]);
                assert(rv =~= Seq::<u32>::empty());
                assert(dv =~= Seq::<u8>::empty());
            },
        }
        assert forall|db: Database| #[trigger] sources_bound(sv, db) implies
            represents(storage_parts(sv, built), stored_relations(db)) by {
            lemma_built(sv, db, built, gidx);
        }
    }
    Ok(out)
}

} // verus!
