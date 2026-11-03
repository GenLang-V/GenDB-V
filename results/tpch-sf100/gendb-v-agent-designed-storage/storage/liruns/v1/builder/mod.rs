//! Builder of storage `liruns`, derived from `facts` (which it extends: the 75 parts of `facts` come first,
//! unchanged).
//!
//! It reads the l_orderkey and l_quantity columns of the stored lineitem rows of `facts` (U32 / U16 codes, I64
//! bases over uniform blocks) and builds, in one pass each, the run directory of l_orderkey (`runs::build_runs`:
//! U8 run lengths and every 4096th run start) and the zone map of l_quantity (`zone::build_zone`). When a run is
//! longer than 255 rows or a maximum does not fit I64 the mode is 0 and nothing is stated about the new parts.
//!
//! Proof: for every database bound to `facts`, the inherited parts satisfy `inherited_ok` (`inherit`), and in mode
//! 1 the new parts satisfy `runs_ok` and `zone_ok`: this storage's `lkey_at` / `lqty_at` are the keys and values the
//! builder read (`lemma_new_parts`).
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::{sources_ready, sources_bound, storage_parts};
use crate::gendb_entry::layout::{PartView, owned_parts_view};
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::stored::part_len;
use crate::spec::value::*;
use crate::stores::liruns::interface::*;
use crate::stores::liruns::interface::common::colfmt::*;
use crate::stores::liruns::declaration::stored_relations;
use crate::stores::facts::interface as fi;
use crate::stores::facts::declaration as fd;

pub mod inherit;
pub mod runs;
pub mod zone;
pub mod long;

use inherit::*;
use runs::*;
use zone::*;
use long::*;

verus! {

/// Rows between two sampled run starts.
pub const STRIDE: usize = 4096;

/// The lineitem parts the builder reads: kinds and lengths (for every bound database).
pub open spec fn li_shape(f: Seq<PartView>) -> bool {
    let n = u64s(f[LI_LAYOUT as int])[0] as int;
    let bs = u64s(f[LI_LAYOUT as int])[1] as int;
    &&& f.len() == FACTS_PARTS
    &&& f[LI_LAYOUT as int] is U64 && u64s(f[LI_LAYOUT as int]).len() == 2
    &&& f[LI_ORDERKEY_CODES as int] is U32 && f[LI_ORDERKEY_BASE as int] is I64
    &&& f[LI_QUANTITY_CODES as int] is U16 && f[LI_QUANTITY_BASE as int] is I64
    &&& 1 <= bs && 0 <= n
    &&& u32s(f[LI_ORDERKEY_CODES as int]).len() == n
    &&& u16s(f[LI_QUANTITY_CODES as int]).len() == n
    &&& i64s(f[LI_ORDERKEY_BASE as int]).len() * bs >= n
    &&& i64s(f[LI_QUANTITY_BASE as int]).len() * bs >= n
}

/// The frame and the two lineitem columns' shapes.
proof fn lemma_li_shape(tp: Seq<PartView>, rel: Seq<Row>)
    requires lineitem_ok(tp, rel),
    ensures
        table_layout_ok(tp, rel.len() as int),
        tp[4] is U32 && for_i64_shape(tp, 1, 4, 5, rel.len() as int),
        tp[12] is U16 && for_i64_shape(tp, 1, 12, 13, rel.len() as int),
{
    let rows = lineitem_rows(tp, rel);
    assert(lineitem_cols_ok(tp, rows));
    assert(int_col_at(tp, 1, 4, 5, rows, 0));
    assert(num_col_at(tp, 1, 12, 13, rows, 1, 2));
    assert(rows.len() == rel.len());
}

/// The shape of the lineitem parts, and their row count is the database's.
proof fn lemma_shape(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures
        li_shape(sv.facts),
        u64s(sv.facts[LI_LAYOUT as int])[0] == stored_relations(db)[0].len(),
{
    lemma_facts_len(sv, db);
    lemma_li_ok(sv, db);
    let f = sv.facts;
    let tp = ftl(sv);
    let rel = stored_relations(db)[0];
    let n = rel.len() as int;
    assert(tp[0] == f[0] && tp[1] == f[1] && tp[4] == f[4] && tp[5] == f[5] && tp[12] == f[12] && tp[13] == f[13]);
    lemma_li_shape(tp, rel);
    let bs = u64s(tp[0])[1] as int;
    lemma_uniform_groups(tp[1], n, bs);
    lemma_nblocks(n, bs);
    assert(part_len(tp[5]) == i64s(tp[5]).len());
    assert(part_len(tp[13]) == i64s(tp[13]).len());
    assert(part_len(tp[4]) == u32s(tp[4]).len());
    assert(part_len(tp[12]) == u16s(tp[12]).len());
}

/// The new parts of a build.
fn new_parts(mode: u64, lens: Vec<u8>, starts: Vec<u64>, z: Vec<i64>, lmeta: Vec<u64>, lr: Vec<u32>, ls: Vec<u32>)
    -> (p: Vec<OwnedPart>)
    ensures
        owned_parts_view(p@) == seq![PartView::U64(seq![mode, STRIDE as u64]), PartView::U8(lens@), PartView::U64(starts@),
            PartView::I64(z@), PartView::U64(lmeta@), PartView::U32(lr@), PartView::U32(ls@)],
{
    let ghost (lv, sv, zv, mv, rv, tv) = (lens@, starts@, z@, lmeta@, lr@, ls@);
    let mut meta: Vec<u64> = Vec::new();
    meta.push(mode);
    meta.push(STRIDE as u64);
    let mut p: Vec<OwnedPart> = Vec::new();
    p.push(OwnedPart::U64(meta));
    p.push(OwnedPart::U8(lens));
    p.push(OwnedPart::U64(starts));
    p.push(OwnedPart::I64(z));
    p.push(OwnedPart::U64(lmeta));
    p.push(OwnedPart::U32(lr));
    p.push(OwnedPart::U32(ls));
    proof {
        assert(meta@ =~= seq![mode, STRIDE as u64]);
        assert(owned_parts_view(p@) =~= seq![PartView::U64(seq![mode, STRIDE as u64]), PartView::U8(lv), PartView::U64(sv),
            PartView::I64(zv), PartView::U64(mv), PartView::U32(rv), PartView::U32(tv)]);
    }
    p
}

/// In mode `MODE_LONG` the run permutation states the runs of the longest length of the run lengths.
proof fn lemma_long_parts(all: Seq<PartView>, mode: u64, lens: Seq<u8>, lmeta: Seq<u64>, lr: Seq<u32>, ls: Seq<u32>)
    requires
        all.len() == LIRUNS_PARTS,
        all[RUN_META as int] == PartView::U64(seq![mode, STRIDE as u64]),
        all[RUN_LENS as int] == PartView::U8(lens),
        all[LONG_META as int] == PartView::U64(lmeta),
        all[LONG_RUNS as int] == PartView::U32(lr),
        all[LONG_STARTS as int] == PartView::U32(ls),
        lmeta.len() == 3,
        lmeta[0] == MODE_LONG ==> mode == MODE_RUNS && long_built(lens, lr, ls, lmeta[1] as int, lmeta[2] as int),
    ensures
        long_ok(all),
{
    assert(run_lens(all) == lens);
    assert(long_meta(all) == lmeta);
    assert(long_runs(all) == lr);
    assert(long_starts(all) == ls);
    assert(run_meta(all) == seq![mode, STRIDE as u64]);
}

/// A run of the builder's keys is a run of this storage's `lkey_at`.
proof fn lemma_same_lkey(all: Seq<PartView>, kc: Seq<u32>, kb: Seq<i64>, bs: int, lens: Seq<u8>, r: int)
    requires
        rs_same(kc, kb, bs, lens, r),
        run_lens(all) == lens,
        forall|j: int| #[trigger] lkey_at(all, j) == fkey(kc, kb, bs, j),
    ensures run_same(all, r),
{
    reveal(rs_same);
    assert forall|j: int| rstart(lens, r) <= j < rstart(lens, r + 1) implies
        #[trigger] lkey_at(all, j) == lkey_at(all, rstart(lens, r)) by {
        assert(fkey(kc, kb, bs, j) == fkey(kc, kb, bs, rstart(lens, r)));
        assert(lkey_at(all, rstart(lens, r)) == fkey(kc, kb, bs, rstart(lens, r)));
    }
}

/// In mode 1 the new parts state the runs and the zone map of the keys and values the builder read.
proof fn lemma_new_parts(all: Seq<PartView>, f: Seq<PartView>, n: int, kc: Seq<u32>, kb: Seq<i64>, qc: Seq<u16>,
    qb: Seq<i64>, bs: int, mode: u64, lens: Seq<u8>, starts: Seq<u64>, z: Seq<i64>)
    requires
        all.len() == LIRUNS_PARTS,
        all.subrange(0, FACTS_PARTS as int) == f,
        li_shape(f),
        n == u64s(f[LI_LAYOUT as int])[0],
        bs == u64s(f[LI_LAYOUT as int])[1],
        kc == u32s(f[LI_ORDERKEY_CODES as int]), kb == i64s(f[LI_ORDERKEY_BASE as int]),
        qc == u16s(f[LI_QUANTITY_CODES as int]), qb == i64s(f[LI_QUANTITY_BASE as int]),
        all[RUN_META as int] == PartView::U64(seq![mode, STRIDE as u64]),
        all[RUN_LENS as int] == PartView::U8(lens),
        all[RUN_STARTS as int] == PartView::U64(starts),
        all[QTY_ZMAX as int] == PartView::I64(z),
        mode == MODE_RUNS ==> runs_built(kc, kb, bs, lens, starts, STRIDE as int) && rstart(lens, lens.len() as int) == n
            && zone_built(qc, qb, bs, n, z),
    ensures
        runs_ok(all, n),
        zone_ok(all, n),
{
    assert(all[LI_LAYOUT as int] == f[LI_LAYOUT as int]) by { assert(all.subrange(0, FACTS_PARTS as int)[0] == all[0]); }
    assert(all[LI_ORDERKEY_CODES as int] == f[LI_ORDERKEY_CODES as int]) by { assert(all.subrange(0, FACTS_PARTS as int)[4] == all[4]); }
    assert(all[LI_ORDERKEY_BASE as int] == f[LI_ORDERKEY_BASE as int]) by { assert(all.subrange(0, FACTS_PARTS as int)[5] == all[5]); }
    assert(all[LI_QUANTITY_CODES as int] == f[LI_QUANTITY_CODES as int]) by { assert(all.subrange(0, FACTS_PARTS as int)[12] == all[12]); }
    assert(all[LI_QUANTITY_BASE as int] == f[LI_QUANTITY_BASE as int]) by { assert(all.subrange(0, FACTS_PARTS as int)[13] == all[13]); }
    assert(li_bs(all) == bs);
    assert(run_lens(all) == lens);
    assert(run_starts(all) == starts);
    assert(run_meta(all) == seq![mode, STRIDE as u64]);
    assert(qty_zmax(all) == z);
    if mode == MODE_RUNS {
        reveal(runs_built);
        assert(run_meta(all)[0] == MODE_RUNS);
        assert(run_meta(all)[1] as int == STRIDE as int);
        assert(rstart(run_lens(all), run_lens(all).len() as int) == n);
        assert forall|j: int| #[trigger] lkey_at(all, j) == fkey(kc, kb, bs, j) by {
            reveal(fkey);
        }
        assert forall|r: int| 0 <= r < lens.len() implies #[trigger] lens[r] >= 1 && run_same(all, r) by {
            assert(lens[r] >= 1 && rs_same(kc, kb, bs, lens, r));
            lemma_same_lkey(all, kc, kb, bs, lens, r);
        }
        assert forall|r: int| 0 < r < lens.len() implies #[trigger] run_cut(all, r) by {
            assert(rs_cut(kc, kb, bs, lens, r));
            assert(lkey_at(all, rstart(lens, r) - 1) == fkey(kc, kb, bs, rstart(lens, r) - 1));
            assert(lkey_at(all, rstart(lens, r)) == fkey(kc, kb, bs, rstart(lens, r)));
        }
        assert forall|b: int| 0 <= b < run_starts(all).len() implies #[trigger] start_ok(lens, run_starts(all), run_meta(all)[1] as int, b) by {
            assert(start_ok(lens, starts, STRIDE as int, b));
        }
        assert forall|j: int| 0 <= j < n implies #[trigger] lqty_at(all, j) <= qty_zmax(all)[j / li_bs(all)] by {
            assert(fval(qc, qb, bs, j) <= z[j / bs]);
        }
        let stride = run_meta(all)[1] as int;
        assert(stride >= 1);
        assert(forall|r: int| 0 <= r < run_lens(all).len() ==> #[trigger] run_lens(all)[r] >= 1 && run_same(all, r));
        assert(forall|r: int| 0 < r < run_lens(all).len() ==> #[trigger] run_cut(all, r));
    }
}

pub fn build(stores: &mut Stores, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        sources_ready(old(stores)@),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(p) ==> forall|db: Database| #[trigger] sources_bound(old(stores)@, db) ==>
            represents(storage_parts(old(stores)@, owned_parts_view(p@)), stored_relations(db)),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ghost sv = stores@;
    let ghost db0 = choose|db: Database| #[trigger] sources_bound(sv, db);
    proof {
        lemma_shape(sv, db0);
    }
    let ghost fv = sv.facts;
    let f = &mut stores.facts;
    let lay = f.extent_u64(LI_LAYOUT, 0, 2);
    let n64 = lay[0];
    let bs64 = lay[1];
    let nk = f.part_len(LI_ORDERKEY_CODES);
    let nkb = f.part_len(LI_ORDERKEY_BASE);
    let nq = f.part_len(LI_QUANTITY_CODES);
    let nqb = f.part_len(LI_QUANTITY_BASE);
    let kc = f.extent_u32(LI_ORDERKEY_CODES, 0, nk);
    let kb = f.extent_i64(LI_ORDERKEY_BASE, 0, nkb);
    let qc = f.extent_u16(LI_QUANTITY_CODES, 0, nq);
    let qb = f.extent_i64(LI_QUANTITY_BASE, 0, nqb);
    proof {
        assert(lay@ =~= u64s(fv[LI_LAYOUT as int]));
        assert(kc@ =~= u32s(fv[LI_ORDERKEY_CODES as int]));
        assert(kb@ =~= i64s(fv[LI_ORDERKEY_BASE as int]));
        assert(qc@ =~= u16s(fv[LI_QUANTITY_CODES as int]));
        assert(qb@ =~= i64s(fv[LI_QUANTITY_BASE as int]));
    }
    let mut mode: u64 = 0;
    let mut lens: Vec<u8> = Vec::new();
    let mut starts: Vec<u64> = Vec::new();
    let mut z: Vec<i64> = Vec::new();
    let mut lmeta: Vec<u64> = vec![0, 0, 0];
    let mut lr: Vec<u32> = Vec::new();
    let mut ls: Vec<u32> = Vec::new();
    if bs64 <= usize::MAX as u64 {
        let bs = bs64 as usize;
        let n = nk;
        match build_runs(kc, kb, bs, n, STRIDE) {
            Some((l, s)) => {
                match build_zone(qc, qb, bs, n) {
                    Some(zz) => {
                        mode = MODE_RUNS;
                        if n as u64 <= u32::MAX as u64 && l.len() as u64 <= u32::MAX as u64 {
                            let (lmax, nlong, pr, ps) = build_long(&l);
                            lmeta = vec![MODE_LONG, lmax, nlong];
                            lr = pr;
                            ls = ps;
                        }
                        lens = l;
                        starts = s;
                        z = zz;
                    },
                    None => {},
                }
            },
            None => {},
        }
    }
    let ghost (lv, stv, zv, mv, rv, tv) = (lens@, starts@, z@, lmeta@, lr@, ls@);
    proof {
        assert(lmeta@.len() == 3);
    }
    let parts = new_parts(mode, lens, starts, z, lmeta, lr, ls);
    proof {
        let built = owned_parts_view(parts@);
        let all = storage_parts(sv, built);
        assert(all == sv.facts + built);
        assert(all.subrange(0, FACTS_PARTS as int) =~= sv.facts);
        assert(all[RUN_META as int] == built[0]);
        assert(all[RUN_LENS as int] == built[1]);
        assert(all[RUN_STARTS as int] == built[2]);
        assert(all[QTY_ZMAX as int] == built[3]);
        assert(all[LONG_META as int] == built[4]);
        assert(all[LONG_RUNS as int] == built[5]);
        assert(all[LONG_STARTS as int] == built[6]);
        assert forall|db: Database| #[trigger] sources_bound(sv, db) implies represents(all, stored_relations(db)) by {
            lemma_shape(sv, db);
            lemma_inherited(sv, db, all);
            lemma_new_parts(all, sv.facts, stored_relations(db)[0].len() as int, kc@, kb@, qc@, qb@, bs64 as int,
                mode, lv, stv, zv);
            lemma_long_parts(all, mode, lv, mv, rv, tv);
        }
    }
    Ok(parts)
}

} // verus!
