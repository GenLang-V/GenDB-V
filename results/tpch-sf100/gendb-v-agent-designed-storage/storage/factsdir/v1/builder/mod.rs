//! Builder of storage `factsdir`: the 75 parts of `facts` are inherited unchanged; this builder adds the l_partkey
//! directory over facts' l_partkey key index (`pdir::dir_scan`) and the o_orderkey directory of facts' orders rows
//! (`odir::odir_build`). Either directory is absent (mode 0) when the source does not allow it (no key index of kind
//! 2, too many rows for U32 entries, or too wide a key span).
//!
//! Proof: `same::lemma_base` restates facts' `represents` with this storage's copy of its definitions
//! (`base_represents`); `src` derives what the two scans read from it; the scans' postconditions give the
//! directories' contracts over the source parts, which are the inherited parts of this storage.
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::layout::{PartView, owned_parts_view};
use crate::gendb_entry::parallel::Dispatch;
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::gendb_entry::storage::{represents, stored_relations};
use crate::spec::value::{Database, Row};
use crate::stores::factsdir::interface as M;
use crate::stores::factsdir::interface::common::colfmt::{u32s, u64s, i64s};
use crate::stores::factsdir::interface::dirs::*;

pub mod pdir;
pub mod odir;
pub mod same;
pub mod src;

use pdir::{dir_scan, dir_spec, idx_src_ok};
use odir::{odir_build, odir_spec, okey_src_ok, odir_entry_ok, odir_found};

verus! {

/// The inherited parts of this storage are the source parts.
pub open spec fn prefix_ok(fp: Seq<PartView>, parts: Seq<PartView>) -> bool {
    &&& fp.len() == M::FACTS_PARTS
    &&& parts.len() == FACTSDIR_PARTS
    &&& forall|k: int| 0 <= k < M::FACTS_PARTS ==> #[trigger] parts[k] == fp[k]
}

/// The directory parts' values (mode 0 parts when a directory is absent).
pub open spec fn meta_of(d: Option<(i64, Seq<u32>)>) -> Seq<i64> {
    match d {
        Some((kmin, o)) => seq![MODE_DIRECTORY, kmin],
        None => seq![0i64, 0i64],
    }
}

pub open spec fn body_of(d: Option<(i64, Seq<u32>)>) -> Seq<u32> {
    match d {
        Some((kmin, o)) => o,
        None => seq![0u32],
    }
}

/// The l_partkey directory parts over the source's key index.
proof fn lemma_pdir_built(fp: Seq<PartView>, parts: Seq<PartView>, n: int, d: Option<(i64, Seq<u32>)>)
    requires
        prefix_ok(fp, parts),
        parts[PDIR_META as int] == PartView::I64(meta_of(d)),
        parts[PDIR_OFFS as int] == PartView::U32(body_of(d)),
        d matches Some((kmin, offs)) ==> dir_spec(fp, n, kmin as int, offs)
            && u64s(fp[M::LI_KEYIDX_KIND as int]).len() == 1 && u64s(fp[M::LI_KEYIDX_KIND as int])[0] == 2,
    ensures
        pdir_ok(parts, n),
{
    assert(parts[LI_LAYOUT_IDX as int] == fp[LI_LAYOUT_IDX as int]);
    assert(parts[M::LI_PARTKEY_CODES as int] == fp[M::LI_PARTKEY_CODES as int]);
    assert(parts[M::LI_PARTKEY_BASE as int] == fp[M::LI_PARTKEY_BASE as int]);
    assert(parts[M::LI_KEYIDX_CODES as int] == fp[M::LI_KEYIDX_CODES as int]);
    assert(parts[M::LI_KEYIDX_BASE as int] == fp[M::LI_KEYIDX_BASE as int]);
    assert(parts[M::LI_KEYIDX_KIND as int] == fp[M::LI_KEYIDX_KIND as int]);
    assert(pdir_meta(parts) == meta_of(d));
    match d {
        Some((kmin, offs)) => {
            assert(has_pdir(parts));
            assert(pdir_offs(parts) == offs);
            assert(pdir_kmin(parts) == kmin);
            assert forall|p: int| 0 <= p < n implies #[trigger] in_pentry(parts, p) by {
                assert(pdir_irow(parts, p) == pdir_irow(fp, p));
                assert(li_key(parts, pdir_irow(parts, p)) == li_key(fp, pdir_irow(fp, p)));
            }
            assert forall|e: int| 0 <= e < pdir_nkeys(parts) implies #[trigger] pdir_offs(parts)[e] <= pdir_offs(parts)[e + 1] by {
                assert(offs[e] <= offs[e + 1]);
            }
        },
        None => {
            assert(!has_pdir(parts));
        },
    }
}

/// The index of the lineitem layout part.
pub const LI_LAYOUT_IDX: usize = 0;

/// The o_orderkey directory parts over the source's orders rows.
proof fn lemma_odir_built(fp: Seq<PartView>, parts: Seq<PartView>, n: int, d: Option<(i64, Seq<u32>)>)
    requires
        prefix_ok(fp, parts),
        parts[ODIR_META as int] == PartView::I64(meta_of(d)),
        parts[ODIR_ROWS as int] == PartView::U32(body_of(d)),
        d matches Some((kmin, rows)) ==> odir_spec(fp, n, kmin as int, rows),
    ensures
        odir_ok(parts, n),
{
    assert(parts[(M::ORDERS_FIRST + M::OR_LAYOUT) as int] == fp[(M::ORDERS_FIRST + M::OR_LAYOUT) as int]);
    assert(parts[(M::ORDERS_FIRST + M::OR_ORDERKEY_CODES) as int] == fp[(M::ORDERS_FIRST + M::OR_ORDERKEY_CODES) as int]);
    assert(parts[(M::ORDERS_FIRST + M::OR_ORDERKEY_BASE) as int] == fp[(M::ORDERS_FIRST + M::OR_ORDERKEY_BASE) as int]);
    assert(odir_meta(parts) == meta_of(d));
    match d {
        Some((kmin, rows)) => {
            assert(has_odir(parts));
            assert(odir_rows(parts) == rows);
            assert(odir_kmin(parts) == kmin);
            assert forall|e: int| 0 <= e < odir_rows(parts).len() implies #[trigger] oentry_sound(parts, n, e) by {
                assert(odir_entry_ok(fp, n, kmin as int, rows, e));
                if rows[e] != ODIR_NONE {
                    assert(or_key(parts, rows[e] as int) == or_key(fp, rows[e] as int));
                }
            }
            assert forall|p: int| 0 <= p < n implies #[trigger] oentry_complete(parts, p) by {
                assert(odir_found(fp, kmin as int, rows, p));
                assert(or_key(parts, p) == or_key(fp, p));
            }
        },
        None => {
            assert(!has_odir(parts));
        },
    }
}

/// The new storage's parts represent the stored relations of every database bound to the source.
proof fn lemma_built(sv: StoresView, db: Database, built: Seq<PartView>, pd: Option<(i64, Seq<u32>)>,
    od: Option<(i64, Seq<u32>)>)
    requires
        sources_bound(sv, db),
        built.len() == 4,
        built[0] == PartView::I64(meta_of(pd)),
        built[1] == PartView::U32(body_of(pd)),
        built[2] == PartView::I64(meta_of(od)),
        built[3] == PartView::U32(body_of(od)),
        pd matches Some((kmin, offs)) ==> dir_spec(sv.facts, src::li_rows_of(sv.facts), kmin as int, offs)
            && u64s(sv.facts[M::LI_KEYIDX_KIND as int]).len() == 1 && u64s(sv.facts[M::LI_KEYIDX_KIND as int])[0] == 2,
        od matches Some((kmin, rows)) ==> odir_spec(sv.facts, src::or_rows_of(sv.facts), kmin as int, rows),
    ensures
        represents(storage_parts(sv, built), stored_relations(db)),
{
    let fp = sv.facts;
    let parts = storage_parts(sv, built);
    let rels = stored_relations(db);
    src::lemma_src(sv, db);
    assert(parts.len() == FACTSDIR_PARTS);
    assert forall|k: int| 0 <= k < M::FACTS_PARTS implies #[trigger] parts[k] == fp[k] by {}
    assert(prefix_ok(fp, parts));
    assert(M::base_parts(parts) =~= fp);
    same::lemma_base(sv, db);
    lemma_pdir_built(fp, parts, rels[0].len() as int, pd);
    lemma_odir_built(fp, parts, rels[1].len() as int, od);
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
        src::lemma_src(sv, db0);
    }
    // ---- the l_partkey directory
    let lay = stores.facts.extent_u64(M::LI_LAYOUT, 0, 2);
    let n = stores.facts.part_len(M::LI_PARTKEY_CODES);
    let bs64 = lay[1];
    let kv = stores.facts.extent_u64(M::LI_KEYIDX_KIND, 0, 1);
    let pd: Option<(i64, Vec<u32>)> = if kv[0] == 2 && n >= 1 && n <= 0xffff_ffff && bs64 <= n as u64 && bs64 >= 1 {
        let bs = bs64 as usize;
        proof {
            assert(idx_src_ok(fp, n as int));
        }
        let nib = stores.facts.part_len(M::LI_KEYIDX_BASE);
        let nkb = stores.facts.part_len(M::LI_PARTKEY_BASE);
        let ic = stores.facts.extent_u32(M::LI_KEYIDX_CODES, 0, n);
        let ib = stores.facts.extent_u64(M::LI_KEYIDX_BASE, 0, nib);
        let kc = stores.facts.extent_u32(M::LI_PARTKEY_CODES, 0, n);
        let kb = stores.facts.extent_i64(M::LI_PARTKEY_BASE, 0, nkb);
        proof {
            assert(ic@ =~= u32s(fp[M::LI_KEYIDX_CODES as int]));
            assert(ib@ =~= u64s(fp[M::LI_KEYIDX_BASE as int]));
            assert(kc@ =~= u32s(fp[M::LI_PARTKEY_CODES as int]));
            assert(kb@ =~= i64s(fp[M::LI_PARTKEY_BASE as int]));
        }
        dir_scan(ic, ib, kc, kb, bs, n, Ghost(fp))
    } else {
        None
    };
    // ---- the o_orderkey directory
    let olay = stores.facts.extent_u64(M::ORDERS_FIRST + M::OR_LAYOUT, 0, 2);
    let no = stores.facts.part_len(M::ORDERS_FIRST + M::OR_ORDERKEY_CODES);
    let obs64 = olay[1];
    let od: Option<(i64, Vec<u32>)> = if obs64 >= 1 && obs64 <= no as u64 {
        let obs = obs64 as usize;
        proof {
            assert(okey_src_ok(fp, no as int));
        }
        let nob = stores.facts.part_len(M::ORDERS_FIRST + M::OR_ORDERKEY_BASE);
        let oc = stores.facts.extent_u32(M::ORDERS_FIRST + M::OR_ORDERKEY_CODES, 0, no);
        let ob = stores.facts.extent_i64(M::ORDERS_FIRST + M::OR_ORDERKEY_BASE, 0, nob);
        proof {
            assert(oc@ =~= u32s(fp[(M::ORDERS_FIRST + M::OR_ORDERKEY_CODES) as int]));
            assert(ob@ =~= i64s(fp[(M::ORDERS_FIRST + M::OR_ORDERKEY_BASE) as int]));
        }
        odir_build(oc, ob, obs, no, Ghost(fp))
    } else {
        None
    };
    let ghost gpd: Option<(i64, Seq<u32>)> = match &pd {
        Some((kmin, offs)) => Some((*kmin, offs@)),
        None => None,
    };
    let ghost god: Option<(i64, Seq<u32>)> = match &od {
        Some((kmin, rows)) => Some((*kmin, rows@)),
        None => None,
    };
    let (pmeta, poffs) = dir_parts(pd);
    let (ometa, orows) = dir_parts(od);
    let ghost (pm_v, po_v, om_v, or_v) = (pmeta@, poffs@, ometa@, orows@);
    let mut out: Vec<OwnedPart> = Vec::new();
    out.push(OwnedPart::I64(pmeta));
    out.push(OwnedPart::U32(poffs));
    out.push(OwnedPart::I64(ometa));
    out.push(OwnedPart::U32(orows));
    proof {
        let built = owned_parts_view(out@);
        assert(built.len() == 4);
        assert(built[0] == PartView::I64(pm_v));
        assert(built[1] == PartView::U32(po_v));
        assert(built[2] == PartView::I64(om_v));
        assert(built[3] == PartView::U32(or_v));
        assert forall|db: Database| #[trigger] sources_bound(sv, db)
            implies represents(storage_parts(sv, built), stored_relations(db)) by {
            src::lemma_src(sv, db);
            lemma_built(sv, db, built, gpd, god);
        }
    }
    Ok(out)
}

/// The header and body parts of a directory (mode 0 parts when absent).
fn dir_parts(d: Option<(i64, Vec<u32>)>) -> (r: (Vec<i64>, Vec<u32>))
    ensures
        r.0@ == meta_of(match d { Some((k, v)) => Some((k, v@)), None => None }),
        r.1@ == body_of(match d { Some((k, v)) => Some((k, v@)), None => None }),
{
    let mut meta: Vec<i64> = Vec::new();
    match d {
        Some((kmin, body)) => {
            meta.push(MODE_DIRECTORY);
            meta.push(kmin);
            proof {
                assert(meta@ =~= seq![MODE_DIRECTORY, kmin]);
            }
            (meta, body)
        },
        None => {
            meta.push(0);
            meta.push(0);
            let mut z: Vec<u32> = Vec::new();
            z.push(0);
            proof {
                assert(meta@ =~= seq![0i64, 0i64]);
                assert(z@ =~= seq![0u32]);
            }
            (meta, z)
        },
    }
}

} // verus!
