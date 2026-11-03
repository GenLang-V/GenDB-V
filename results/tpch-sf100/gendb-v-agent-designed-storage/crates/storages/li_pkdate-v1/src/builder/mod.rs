//! Builder of storage `li_pkdate`: the 75 parts of `facts` are inherited unchanged; this builder adds a composite
//! index of lineitem on `(l_partkey, l_shipdate)`.
//!
//! Plan (when facts' l_partkey key index has kind 2, the rows fit U32 positions, the key span is small enough for a
//! dense directory and the dates span at most 65536 days):
//! 1. `dirscan::dir_scan`: the directory over facts' key index (entry `e` = positions of key `kmin + e`);
//! 2. `assemble::date_range`: the smallest and largest l_shipdate (`dbase` = the smallest);
//! 3. one worker task per run of entries (`task::IdxTask`): each position's stored row `s` and date code `c` are
//!    packed as `c * 2^32 + s`, each entry's packed values are sorted ascending (`sort64::msort64`, so by date),
//!    then unpacked into the task's index rows and date codes;
//! 4. the calling thread concatenates the tasks' outputs (`assemble::build_index`) and checks that the rows are a
//!    bijection (`check_perm`).
//! Otherwise (or when the check fails) the index is absent (mode 0).
//!
//! Proof: `src::lemma_src` restates the source facts with this storage's definitions; each task proves, for every
//! entry of its run, that the entry's positions hold rows of the entry's key with their date codes, in date order
//! (`task::entry_out`), because sorting only moves elements that all satisfy that property; the concatenation keeps
//! it for all entries, which gives `in_entry`, `date_key_ok` and `date_sorted_at` for every position.
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::layout::{PartView, owned_parts_view};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::gendb_entry::storage::{represents, stored_relations};
use crate::spec::value::{Database, Row};
use crate::stores::li_pkdate::interface::*;
use crate::stores::li_pkdate::declaration as D;

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
        forall|s: int| #[trigger] supp_at(parts, s) == supp_at(fp, s),
        forall|s: int| #[trigger] qty_at(parts, s) == qty_at(fp, s),
        forall|s: int| #[trigger] date_at(parts, s) == date_at(fp, s),
        parts[LI_LAYOUT as int] == fp[LI_LAYOUT as int],
        parts[LI_PERM_CODES as int] == fp[LI_PERM_CODES as int],
        parts[LI_PERM_BASE as int] == fp[LI_PERM_BASE as int],
        parts[LI_PARTKEY_CODES as int] == fp[LI_PARTKEY_CODES as int],
        parts[LI_PARTKEY_BASE as int] == fp[LI_PARTKEY_BASE as int],
        parts[LI_SUPPKEY_CODES as int] == fp[LI_SUPPKEY_CODES as int],
        parts[LI_SUPPKEY_BASE as int] == fp[LI_SUPPKEY_BASE as int],
        parts[LI_QUANTITY_CODES as int] == fp[LI_QUANTITY_CODES as int],
        parts[LI_QUANTITY_BASE as int] == fp[LI_QUANTITY_BASE as int],
        parts[LI_SHIPDATE_CODES as int] == fp[LI_SHIPDATE_CODES as int],
        parts[LI_SHIPDATE_BASE as int] == fp[LI_SHIPDATE_BASE as int],
{
    assert(parts[LI_LAYOUT as int] == fp[LI_LAYOUT as int]);
    assert(parts[LI_PERM_CODES as int] == fp[LI_PERM_CODES as int]);
    assert(parts[LI_PERM_BASE as int] == fp[LI_PERM_BASE as int]);
    assert(parts[LI_PARTKEY_CODES as int] == fp[LI_PARTKEY_CODES as int]);
    assert(parts[LI_PARTKEY_BASE as int] == fp[LI_PARTKEY_BASE as int]);
    assert(parts[LI_SUPPKEY_CODES as int] == fp[LI_SUPPKEY_CODES as int]);
    assert(parts[LI_SUPPKEY_BASE as int] == fp[LI_SUPPKEY_BASE as int]);
    assert(parts[LI_QUANTITY_CODES as int] == fp[LI_QUANTITY_CODES as int]);
    assert(parts[LI_QUANTITY_BASE as int] == fp[LI_QUANTITY_BASE as int]);
    assert(parts[LI_SHIPDATE_CODES as int] == fp[LI_SHIPDATE_CODES as int]);
    assert(parts[LI_SHIPDATE_BASE as int] == fp[LI_SHIPDATE_BASE as int]);
}

/// The inherited facts of the source carry over to this storage's parts.
proof fn lemma_built_rows(fp: Seq<PartView>, parts: Seq<PartView>, rel: Seq<Row>)
    requires
        src_ok(fp, rel),
        parts.len() == LI_PKDATE_PARTS,
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
        rel[#[trigger] map_at(parts, s)] == li_row(key_at(parts, s), supp_at(parts, s), qty_at(parts, s), date_at(parts, s)) by {
        assert(rel[map_at(fp, s)] == li_row(key_at(fp, s), supp_at(fp, s), qty_at(fp, s), date_at(fp, s)));
    }
}

/// Position `p` of entry `e`: its row has the entry's key and its date code.
proof fn lemma_entry_at(fp: Seq<PartView>, n: int, kmin: int, dbase: int, offs: Seq<u32>, rows: Seq<u32>,
    dates: Seq<u16>, e: int, p: int)
    requires entry_out(fp, n, dbase, kmin, offs, 0, rows, dates, e), offs[e] <= p < offs[e + 1],
    ensures
        rows[p] < n,
        key_at(fp, rows[p] as int) == kmin + e,
        dbase + dates[p] == date_at(fp, rows[p] as int),
        p + 1 < offs[e + 1] ==> dates[p] <= dates[p + 1],
{
    reveal(entry_out);
}

/// The index facts of position `p`.
proof fn lemma_idx_pos(fp: Seq<PartView>, parts: Seq<PartView>, n: int, kmin: i64, dbase: i64, offs: Seq<u32>,
    rows: Seq<u32>, dates: Seq<u16>, p: int)
    requires
        forall|k: int| 0 <= k < FACTS_PARTS ==> #[trigger] parts[k] == fp[k],
        parts.len() == LI_PKDATE_PARTS, fp.len() == FACTS_PARTS,
        idx_meta(parts) == seq![MODE_INDEX, kmin, dbase],
        idx_offs(parts) == offs, idx_rows(parts) == rows, idx_dates(parts) == dates,
        offs.len() >= 1, offs[0] == 0, offs[offs.len() - 1] == n,
        ents_mono(offs, offs.len() - 1),
        forall|e: int| 0 <= e < offs.len() - 1 ==> #[trigger] entry_out(fp, n, dbase as int, kmin as int, offs, 0, rows, dates, e),
        0 <= p < n,
    ensures
        in_entry(parts, p),
        date_key_ok(parts, p),
        p + 1 < n ==> date_sorted_at(parts, p),
{
    lemma_same_prefix(fp, parts);
    let nk = offs.len() - 1;
    let e = lemma_find_entry_m(offs, nk, p);
    lemma_entry_at(fp, n, kmin as int, dbase as int, offs, rows, dates, e, p);
    assert(key_at(parts, irow(parts, p)) == key_at(fp, rows[p] as int));
    if p + 1 < n {
        let f = lemma_find_entry_m(offs, nk, p + 1);
        lemma_entry_at(fp, n, kmin as int, dbase as int, offs, rows, dates, f, p + 1);
        assert(key_at(parts, irow(parts, p + 1)) == key_at(fp, rows[p + 1] as int));
        if key_at(parts, irow(parts, p)) == key_at(parts, irow(parts, p + 1)) {
            assert(e == f);
        }
    }
}

/// A present index: the directory, the rows and the date codes of `build_index`, checked a bijection.
proof fn lemma_idx_some(fp: Seq<PartView>, parts: Seq<PartView>, n: int, kmin: i64, dbase: i64, offs: Seq<u32>,
    rows: Seq<u32>, dates: Seq<u16>)
    requires
        parts.len() == LI_PKDATE_PARTS,
        forall|k: int| 0 <= k < FACTS_PARTS ==> #[trigger] parts[k] == fp[k],
        fp.len() == FACTS_PARTS,
        n >= 1,
        parts[IDX_META as int] == PartView::I64(seq![MODE_INDEX, kmin, dbase]),
        parts[IDX_OFFS as int] == PartView::U32(offs),
        parts[IDX_ROWS as int] == PartView::U32(rows),
        parts[IDX_DATES as int] == PartView::U16(dates),
        dir_spec(fp, n, kmin as int, offs),
        rows.len() == n, dates.len() == n,
        perm_view_ok(rows, n),
        forall|e: int| 0 <= e < offs.len() - 1 ==> #[trigger] entry_out(fp, n, dbase as int, kmin as int, offs, 0, rows, dates, e),
    ensures
        idx_ok(parts, n),
{
    lemma_dir_ends(fp, n, kmin as int, offs);
    lemma_dir_mono(fp, n, kmin as int, offs);
    assert(idx_meta(parts) == seq![MODE_INDEX, kmin, dbase]);
    assert(has_idx(parts));
    assert(idx_offs(parts) == offs);
    assert(idx_rows(parts) == rows);
    assert(idx_dates(parts) == dates);
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
        lemma_idx_pos(fp, parts, n, kmin, dbase, offs, rows, dates, p);
    }
    assert forall|p: int| 0 <= p < n implies #[trigger] date_key_ok(parts, p) by {
        lemma_idx_pos(fp, parts, n, kmin, dbase, offs, rows, dates, p);
    }
    assert forall|p: int| 0 <= p < n - 1 implies #[trigger] date_sorted_at(parts, p) by {
        lemma_idx_pos(fp, parts, n, kmin, dbase, offs, rows, dates, p);
    }
    assert forall|e: int| 0 <= e < idx_nkeys(parts) implies #[trigger] idx_offs(parts)[e] <= idx_offs(parts)[e + 1] by {
        lemma_ents_le(offs, offs.len() - 1, e, e + 1);
    }
}

/// The new storage's parts represent the stored relations of every database bound to the source.
proof fn lemma_built(sv: StoresView, db: Database, built: Seq<PartView>, idx: Option<(i64, i64, Seq<u32>, Seq<u32>, Seq<u16>)>)
    requires
        sources_bound(sv, db),
        built.len() == 4,
        built[0] == PartView::I64(match idx { Some((kmin, dbase, o, r, d)) => seq![MODE_INDEX, kmin, dbase], None => seq![0i64, 0i64, 0i64] }),
        built[1] == PartView::U32(match idx { Some((kmin, dbase, o, r, d)) => o, None => seq![0u32] }),
        built[2] == PartView::U32(match idx { Some((kmin, dbase, o, r, d)) => r, None => Seq::<u32>::empty() }),
        built[3] == PartView::U16(match idx { Some((kmin, dbase, o, r, d)) => d, None => Seq::<u16>::empty() }),
        idx matches Some((kmin, dbase, o, r, d)) ==> {
            let n = n_rows(sv.facts);
            &&& n >= 1
            &&& kind_of(sv.facts) == 2
            &&& dir_spec(sv.facts, n, kmin as int, o)
            &&& r.len() == n && d.len() == n
            &&& perm_view_ok(r, n)
            &&& forall|e: int| 0 <= e < o.len() - 1 ==> #[trigger] entry_out(sv.facts, n, dbase as int, kmin as int, o, 0, r, d, e)
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
    assert(parts.len() == LI_PKDATE_PARTS);
    assert forall|k: int| 0 <= k < FACTS_PARTS implies #[trigger] parts[k] == fp[k] by {}
    assert(parts[IDX_META as int] == built[0]);
    assert(parts[IDX_OFFS as int] == built[1]);
    assert(parts[IDX_ROWS as int] == built[2]);
    assert(parts[IDX_DATES as int] == built[3]);
    lemma_built_rows(fp, parts, rel);
    match idx {
        Some((kmin, dbase, o, r, d)) => {
            lemma_idx_some(fp, parts, rel.len() as int, kmin, dbase, o, r, d);
        },
        None => {
            assert(idx_meta(parts) == seq![0i64, 0i64, 0i64]);
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
    let mut idx: Option<(i64, i64, Vec<u32>, Vec<u32>, Vec<u16>)> = None;
    if kv[0] == 2 && n >= 1 && n <= 0xffff_ffff && bs64 <= n as u64 {
        let bs = bs64 as usize;
        proof {
            assert(kind_of(fp) == 2);
            assert(index_ok(fp, n as int));
        }
        let nib = stores.facts.part_len(LI_KEYIDX_BASE);
        let nkb = stores.facts.part_len(LI_PARTKEY_BASE);
        let ndb = stores.facts.part_len(LI_SHIPDATE_BASE);
        let ic = stores.facts.extent_u32(LI_KEYIDX_CODES, 0, n);
        let ib = stores.facts.extent_u64(LI_KEYIDX_BASE, 0, nib);
        let kc = stores.facts.extent_u32(LI_PARTKEY_CODES, 0, n);
        let kb = stores.facts.extent_i64(LI_PARTKEY_BASE, 0, nkb);
        let dc = stores.facts.extent_u16(LI_SHIPDATE_CODES, 0, n);
        let db = stores.facts.extent_i64(LI_SHIPDATE_BASE, 0, ndb);
        proof {
            assert(ic@ =~= u32s(fp[LI_KEYIDX_CODES as int]));
            assert(ib@ =~= u64s(fp[LI_KEYIDX_BASE as int]));
            assert(kc@ =~= u32s(fp[LI_PARTKEY_CODES as int]));
            assert(kb@ =~= i64s(fp[LI_PARTKEY_BASE as int]));
            assert(dc@ =~= u16s(fp[LI_SHIPDATE_CODES as int]));
            assert(db@ =~= i64s(fp[LI_SHIPDATE_BASE as int]));
        }
        proof {
            reveal(task_src);
            assert(task_src(fp, n as int, bs as int, ic@, ib@, dc@, db@));
        }
        match dir_scan(ic, ib, kc, kb, bs, n, Ghost(fp)) {
            Some((kmin, offs)) => {
                let (dlo, dhi) = date_range(dc, db, bs, n, Ghost(fp));
                if dhi - dlo <= 0xffff {
                    proof {
                        lemma_dates_in(fp, n as int, dlo as int, dhi as int);
                    }
                    match build_index(ic, ib, dc, db, bs, n, kmin, dlo, &offs, workers, dispatch, Ghost(fp)) {
                        Ok((rows, dates)) => {
                            if check_perm(&rows) {
                                idx = Some((kmin, dlo, offs, rows, dates));
                            }
                        },
                        Err(e) => return Err(e),
                    }
                }
            },
            None => {},
        }
    }
    let ghost gidx: Option<(i64, i64, Seq<u32>, Seq<u32>, Seq<u16>)> = match &idx {
        Some((kmin, dbase, o, r, d)) => Some((*kmin, *dbase, o@, r@, d@)),
        None => None,
    };
    let mut meta: Vec<i64> = Vec::new();
    let (offs, rows, dates): (Vec<u32>, Vec<u32>, Vec<u16>) = match idx {
        Some((kmin, dbase, o, r, d)) => {
            meta.push(MODE_INDEX);
            meta.push(kmin);
            meta.push(dbase);
            (o, r, d)
        },
        None => {
            meta.push(0);
            meta.push(0);
            meta.push(0);
            let mut z: Vec<u32> = Vec::new();
            z.push(0);
            (z, Vec::new(), Vec::new())
        },
    };
    let ghost (mv, ov, rv, dv) = (meta@, offs@, rows@, dates@);
    let mut out: Vec<OwnedPart> = Vec::new();
    out.push(OwnedPart::I64(meta));
    out.push(OwnedPart::U32(offs));
    out.push(OwnedPart::U32(rows));
    out.push(OwnedPart::U16(dates));
    proof {
        let built = owned_parts_view(out@);
        assert(built.len() == 4);
        assert(built[0] == PartView::I64(mv));
        assert(built[1] == PartView::U32(ov));
        assert(built[2] == PartView::U32(rv));
        assert(built[3] == PartView::U16(dv));
        match gidx {
            Some((kmin, dbase, o, r, d)) => {
                assert(mv =~= seq![MODE_INDEX, kmin, dbase]);
            },
            None => {
                assert(mv =~= seq![0i64, 0i64, 0i64]);
                assert(ov =~= seq![0u32]);
                assert(rv =~= Seq::<u32>::empty());
                assert(dv =~= Seq::<u16>::empty());
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
