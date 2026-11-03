//! Builder of storage `num_tvg`: keeps the 27 parts of storage `num` (inherited, linked unchanged) and adds a group
//! index over num's stored order (`interface::index_ok`): `run_groups`, `group_start`, `group_key`.
//! One pass over the rows of each run: a new group starts at the run's first row and wherever the pair code `tv`
//! changes. Row positions and pair codes are stored as `U32`; when the row count or the pair count exceeds
//! `u32::MAX` the three parts are left empty (the first case of `index_ok`).
//! The proof: the loop invariants (`done_ok`) give the index facts; the inherited parts carry num's `represents` over
//! to num_tvg's (`lemma_represents`).
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::layout::{owned_parts_view, PartView};
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::spec::value::Database;
use crate::stores::num::interface as src;
use crate::stores::num_tvg::interface as dst;
use crate::stores::num::interface::common::runs::runs_partition_ok;

verus! {

/// The index facts of `index_ok` (second case) over sequences: `start` the `nr + 1` run starts, `tv` the pair codes.
pub open spec fn index_facts(start: Seq<u64>, tv: Seq<u64>, nr: int, np: int, rg: Seq<u64>, gs: Seq<u32>, gk: Seq<u32>) -> bool {
    let ng = gk.len() as int;
    &&& forall|g: int| 0 <= g < ng ==> (#[trigger] gk[g]) < np
    &&& rg.len() == nr + 1
    &&& gs.len() == ng + 1
    &&& forall|a: int, b: int| 0 <= a <= b <= nr ==> #[trigger] rg[a] <= #[trigger] rg[b]
    &&& rg[nr] == ng
    &&& forall|r: int| 0 <= r <= nr ==> #[trigger] gs[rg[r] as int] == start[r]
    &&& forall|a: int, b: int| 0 <= a <= b <= ng ==> #[trigger] gs[a] <= #[trigger] gs[b]
    &&& forall|g: int, i: int| 0 <= g < ng && gs[g] <= i < gs[g + 1] ==> #[trigger] tv[i] == #[trigger] gk[g] as u64
}

/// State of the pass before row `i` of run `r` (rows `[start[r], i)` of run `r` and all earlier runs done):
/// `rg` holds the first group of runs `0..=r` (`0..r` when `i` is the run's first row), every group but the last is
/// closed, the last group (if any) holds the rows from its start up to `i`.
pub open spec fn done_ok(start: Seq<u64>, tv: Seq<u64>, np: int, r: int, i: int, rg: Seq<u64>, gs: Seq<u32>, gk: Seq<u32>) -> bool {
    let ng = gk.len() as int;
    &&& forall|g: int| 0 <= g < ng ==> (#[trigger] gk[g]) < np
    &&& gs.len() == ng
    &&& forall|a: int, b: int| 0 <= a <= b < rg.len() ==> #[trigger] rg[a] <= #[trigger] rg[b]
    &&& forall|a: int| 0 <= a < rg.len() ==> #[trigger] rg[a] < ng && gs[rg[a] as int] == start[a]
    &&& forall|a: int, b: int| 0 <= a <= b < ng ==> #[trigger] gs[a] <= #[trigger] gs[b]
    &&& forall|g: int| 0 <= g < ng ==> #[trigger] gs[g] < i
    &&& forall|g: int, k: int| 0 <= g && g + 1 < ng && gs[g] <= k < gs[g + 1] ==> #[trigger] tv[k] == #[trigger] gk[g] as u64
    &&& ng > 0 ==> forall|k: int| gs[ng - 1] <= k < i ==> #[trigger] tv[k] == gk[ng - 1] as u64
}

/// Some database is bound to the source: num's layout holds.
proof fn lemma_source_layout(sv: StoresView)
    requires sources_ready(sv),
    ensures src::num_layout_ok(sv.num),
{
    let db = choose|db: Database| #[trigger] sources_bound(sv, db);
}

/// The group index of the rows `[0, n)` cut into `nr` nonempty runs by `start`, with pair codes `tv` below 2^32.
fn build_index(start: &[u64], tv: &[u64], nr: usize, n: usize, np: usize) -> (r: (Vec<u64>, Vec<u32>, Vec<u32>))
    requires
        runs_partition_ok(start@, nr as int, n as int),
        tv@.len() == n, n <= u32::MAX, np <= u32::MAX,
        forall|i: int| 0 <= i < n ==> #[trigger] tv@[i] < np,
    ensures index_facts(start@, tv@, nr as int, np as int, r.0@, r.1@, r.2@),
{
    let mut rg: Vec<u64> = Vec::with_capacity(start.len());
    let mut gs: Vec<u32> = Vec::new();
    let mut gk: Vec<u32> = Vec::new();
    let mut r: usize = 0;
    while r < nr
        invariant
            runs_partition_ok(start@, nr as int, n as int), tv@.len() == n, n <= u32::MAX, np <= u32::MAX,
            forall|i: int| 0 <= i < n ==> #[trigger] tv@[i] < np,
            r <= nr, rg@.len() == r,
            done_ok(start@, tv@, np as int, r as int, start@[r as int] as int, rg@, gs@, gk@),
        decreases nr - r,
    {
        let s = start[r] as usize;
        let e = start[r + 1] as usize;
        proof {
            assert(start@[r as int] < start@[r + 1]);
            assert(start@[r + 1] <= start@[nr as int]);
        }
        let ghost ng0 = gk@.len();
        rg.push(gk.len() as u64);
        let mut i: usize = s;
        while i < e
            invariant
                runs_partition_ok(start@, nr as int, n as int), tv@.len() == n, n <= u32::MAX, np <= u32::MAX,
                forall|i: int| 0 <= i < n ==> #[trigger] tv@[i] < np,
                r < nr, s == start@[r as int], e == start@[r + 1], s < e <= n,
                s <= i <= e, rg@.len() == r + 1, rg@[r as int] == ng0,
                i == s ==> gk@.len() == ng0,
                i > s ==> gk@.len() > ng0 && gs@[ng0 as int] == s && gk@[gk@.len() - 1] as u64 == tv@[i - 1],
                done_ok(start@, tv@, np as int, r as int, i as int, rg@.subrange(0, r as int), gs@, gk@),
                forall|a: int| 0 <= a < r ==> #[trigger] rg@[a] <= ng0,
            decreases e - i,
        {
            if i == s || tv[i] != tv[i - 1] {
                let ghost ogs = gs@;
                let ghost ogk = gk@;
                gs.push(i as u32);
                gk.push(tv[i] as u32);
                proof {
                    let ng = gk@.len() as int;
                    assert forall|a: int, b: int| 0 <= a <= b < ng implies #[trigger] gs@[a] <= #[trigger] gs@[b] by {
                        if b < ng - 1 {
                            assert(ogs[a] <= ogs[b]);
                        } else if a < ng - 1 {
                            assert(ogs[a] < i);
                        }
                    }
                    assert forall|g: int, k: int| 0 <= g && g + 1 < ng && gs@[g] <= k < gs@[g + 1]
                        implies #[trigger] tv@[k] == #[trigger] gk@[g] as u64 by {
                        if g + 1 < ng - 1 {
                            assert(ogs[g] == gs@[g] && ogs[g + 1] == gs@[g + 1] && ogk[g] == gk@[g]);
                        } else {
                            assert(g == ng - 2);
                            assert(ogs[ng - 2] == gs@[g]);
                        }
                    }
                }
            } else {
                proof {
                    assert(gk@[gk@.len() - 1] as u64 == tv@[i as int]);
                }
            }
            i = i + 1;
        }
        proof {
            let ng = gk@.len() as int;
            assert(rg@.subrange(0, r as int).push(ng0 as u64) =~= rg@);
            assert forall|a: int, b: int| 0 <= a <= b < rg@.len() implies #[trigger] rg@[a] <= #[trigger] rg@[b] by {
                if b < r {
                    assert(rg@.subrange(0, r as int)[a] <= rg@.subrange(0, r as int)[b]);
                }
            }
            assert forall|a: int| 0 <= a < rg@.len() implies #[trigger] rg@[a] < ng && gs@[rg@[a] as int] == start@[a] by {
                if a < r {
                    assert(rg@.subrange(0, r as int)[a] == rg@[a]);
                }
            }
        }
        r = r + 1;
    }
    let ng = gk.len();
    let ghost ogs = gs@;
    rg.push(ng as u64);
    gs.push(n as u32);
    proof {
        let ngi = ng as int;
        let rgv = rg@;
        let gsv = gs@;
        assert(gsv.len() == ngi + 1);
        assert forall|a: int, b: int| 0 <= a <= b <= nr implies #[trigger] rgv[a] <= #[trigger] rgv[b] by {
            if b < nr {
            } else if a < nr {
                assert(rgv[a] < ngi);
            }
        }
        assert forall|q: int| 0 <= q <= nr implies #[trigger] gsv[rgv[q] as int] == start@[q] by {
            if q < nr {
                assert(rgv[q] < ngi);
                assert(gsv[rgv[q] as int] == ogs[rgv[q] as int]);
            }
        }
        assert forall|a: int, b: int| 0 <= a <= b <= ngi implies #[trigger] gsv[a] <= #[trigger] gsv[b] by {
            if b < ngi {
                assert(ogs[a] <= ogs[b]);
            } else if a < ngi {
                assert(ogs[a] < start@[nr as int]);
            }
        }
        assert forall|g: int, i: int| 0 <= g < ngi && gsv[g] <= i < gsv[g + 1] implies #[trigger] tv@[i] == #[trigger] gk@[g] as u64 by {
            if g + 1 < ngi {
                assert(ogs[g] == gsv[g] && ogs[g + 1] == gsv[g + 1]);
            } else {
                assert(ogs[g] == gsv[g]);
            }
        }
    }
    (rg, gs, gk)
}

/// The inherited parts followed by the index parts represent num_tvg's relations of every database bound to num.
proof fn lemma_represents(sv: StoresView, db: Database, rg: Seq<u64>, gs: Seq<u32>, gk: Seq<u32>)
    requires
        sources_bound(sv, db),
        (rg.len() == 0 && gs.len() == 0 && gk.len() == 0)
            || index_facts(src::u64s(sv.num, src::P_RUN_START), src::u64s(sv.num, src::P_TV), src::run_count(sv.num),
                src::pair_count(sv.num), rg, gs, gk),
    ensures
        dst::represents(sv.num + seq![PartView::U64(rg), PartView::U32(gs), PartView::U32(gk)],
            crate::stores::num_tvg::declaration::stored_relations(db)),
{
    let sp = sv.num;
    let parts = sp + seq![PartView::U64(rg), PartView::U32(gs), PartView::U32(gk)];
    let rels = crate::stores::num::declaration::stored_relations(db);
    assert(crate::stores::num_tvg::declaration::stored_relations(db) == rels);
    assert(src::represents(sp, rels));
    assert(sp.len() == 27);
    assert forall|k: int| 0 <= k < 27 implies #[trigger] parts[k] == sp[k] by {}
    assert(parts[dst::P_RUN_GROUPS as int] == PartView::U64(rg));
    assert(parts[dst::P_GROUP_START as int] == PartView::U32(gs));
    assert(parts[dst::P_GROUP_KEY as int] == PartView::U32(gk));
    lemma_layout_carries(sp, parts, rg, gs, gk);
    let n = src::row_count(sp);
    let start = src::u64s(sp, src::P_RUN_START);
    assert forall|i: int| 0 <= i < n implies #[trigger] dst::stored_cols_ok(parts, dst::stored_row(parts, rels, i), i) by {
        assert(src::stored_cols_ok(sp, src::stored_row(sp, rels, i), i));
        assert(dst::stored_row(parts, rels, i) == src::stored_row(sp, rels, i));
    }
    assert forall|r: int, i: int| 0 <= r < dst::run_count(parts) && dst::u64s(parts, dst::P_RUN_START)[r] <= i < dst::u64s(parts, dst::P_RUN_START)[r + 1]
        implies #[trigger] dst::run_cols_ok(parts, dst::stored_row(parts, rels, i), r) by {
        assert(src::run_cols_ok(sp, src::stored_row(sp, rels, i), r));
        assert(dst::stored_row(parts, rels, i) == src::stored_row(sp, rels, i));
    }
    assert forall|j: int| 0 <= j < n implies #[trigger] dst::canon_cols_ok(parts, rels[0][j], j) by {
        assert(src::canon_cols_ok(sp, rels[0][j], j));
        assert(dst::sparse_at(parts, dst::P_COREG_ROWS, j) == src::sparse_at(sp, src::P_COREG_ROWS, j));
        assert(dst::sparse_at(parts, dst::P_FOOTNOTE_ROWS, j) == src::sparse_at(sp, src::P_FOOTNOTE_ROWS, j));
    }
}

/// num's layout facts on the inherited parts give num_tvg's (the definitions are copies), plus the index facts.
proof fn lemma_layout_carries(sp: Seq<PartView>, parts: Seq<PartView>, rg: Seq<u64>, gs: Seq<u32>, gk: Seq<u32>)
    requires
        src::num_layout_ok(sp),
        parts == sp + seq![PartView::U64(rg), PartView::U32(gs), PartView::U32(gk)],
        (rg.len() == 0 && gs.len() == 0 && gk.len() == 0)
            || index_facts(src::u64s(sp, src::P_RUN_START), src::u64s(sp, src::P_TV), src::run_count(sp),
                src::pair_count(sp), rg, gs, gk),
    ensures dst::num_layout_ok(parts),
{
    assert(sp.len() == 27);
    assert forall|k: int| 0 <= k < 27 implies #[trigger] parts[k] == sp[k] by {}
    let n = src::row_count(sp);
    let nr = src::run_count(sp);
    assert(dst::row_count(parts) == n);
    assert(dst::run_count(parts) == nr);
    assert(dst::u32s(parts, dst::P_GROUP_START) == gs);
    assert(dst::u32s(parts, dst::P_GROUP_KEY) == gk);
    assert(dst::u64s(parts, dst::P_RUN_GROUPS) == rg);
    assert(dst::index_ok(parts));
    // The text dictionaries, permutation, runs and sparse columns: same definitions over the same parts.
    let orig = src::u64s(sp, src::P_ORIG);
    assert(src::common::perm::ident(n as nat) =~= dst::common::perm::ident(n as nat));
    assert(dst::common::perm::is_permutation(orig, n as nat));
    assert(dst::dict_ok(parts, dst::P_UOM_OFF)) by { lemma_dict_carries(sp, parts, src::P_UOM_OFF); }
    assert(dst::dict_ok(parts, dst::P_ADSH_OFF)) by { lemma_dict_carries(sp, parts, src::P_ADSH_OFF); }
    assert(dst::dict_ok(parts, dst::P_TAG_OFF)) by { lemma_dict_carries(sp, parts, src::P_TAG_OFF); }
    assert(dst::dict_ok(parts, dst::P_VERSION_OFF)) by { lemma_dict_carries(sp, parts, src::P_VERSION_OFF); }
    assert(dst::sparse_ok(parts, dst::P_COREG_ROWS, n)) by { lemma_sparse_carries(sp, parts, src::P_COREG_ROWS, n); }
    assert(dst::sparse_ok(parts, dst::P_FOOTNOTE_ROWS, n)) by { lemma_sparse_carries(sp, parts, src::P_FOOTNOTE_ROWS, n); }
}

proof fn lemma_dict_carries(sp: Seq<PartView>, parts: Seq<PartView>, po: usize)
    requires
        src::dict_ok(sp, po), po + 1 < 27, sp.len() == 27, parts.len() >= 27,
        forall|k: int| 0 <= k < 27 ==> #[trigger] parts[k] == sp[k],
    ensures dst::dict_ok(parts, po),
{
    assert(parts[po as int] == sp[po as int]);
    assert(parts[po + 1] == sp[po + 1]);
    let off = src::common::text::u64_part(sp[po as int]);
    let bytes = src::common::text::u8_part(sp[po + 1]);
    let c = src::common::cols::text_count(sp, po as int);
    assert(dst::common::cols::text_count(parts, po as int) == c);
    assert forall|a: int, b: int| 0 <= a < b < c implies crate::spec::text::lex_cmp(
        #[trigger] dst::common::text::text_entry(off, bytes, a), #[trigger] dst::common::text::text_entry(off, bytes, b)) < 0 by {
        assert(crate::spec::text::lex_cmp(src::common::text::text_entry(off, bytes, a),
            src::common::text::text_entry(off, bytes, b)) < 0);
    }
}

proof fn lemma_sparse_carries(sp: Seq<PartView>, parts: Seq<PartView>, prows: usize, n: int)
    requires
        src::sparse_ok(sp, prows, n), prows + 2 < 27, sp.len() == 27, parts.len() >= 27,
        forall|k: int| 0 <= k < 27 ==> #[trigger] parts[k] == sp[k],
    ensures dst::sparse_ok(parts, prows, n),
{
    assert(parts[prows as int] == sp[prows as int]);
    assert(parts[prows + 1] == sp[prows + 1]);
    assert(parts[prows + 2] == sp[prows + 2]);
}

/// The source facts the builder reads: run starts, pair codes below the pair count, part types and lengths.
proof fn lemma_source_facts(sp: Seq<PartView>)
    requires src::num_layout_ok(sp),
    ensures
        sp.len() == 27,
        sp[src::P_ORIG as int] is U64, sp[src::P_RUN_UOM as int] is U64, sp[src::P_PAIR_TAG as int] is U64,
        sp[src::P_RUN_START as int] is U64, sp[src::P_TV as int] is U64,
        src::u64s(sp, src::P_RUN_START).len() == src::run_count(sp) + 1,
        src::u64s(sp, src::P_TV).len() == src::row_count(sp),
        runs_partition_ok(src::u64s(sp, src::P_RUN_START), src::run_count(sp), src::row_count(sp)),
        forall|i: int| 0 <= i < src::row_count(sp) ==> #[trigger] src::u64s(sp, src::P_TV)[i] < src::pair_count(sp),
{
}

/// Every database bound to num gets num_tvg's `represents` over the inherited parts and the index parts.
proof fn lemma_all_represent(sv: StoresView, parts: Seq<OwnedPart>, rg: Seq<u64>, gs: Seq<u32>, gk: Seq<u32>)
    requires
        sources_ready(sv),
        owned_parts_view(parts) == seq![PartView::U64(rg), PartView::U32(gs), PartView::U32(gk)],
        (rg.len() == 0 && gs.len() == 0 && gk.len() == 0)
            || index_facts(src::u64s(sv.num, src::P_RUN_START), src::u64s(sv.num, src::P_TV), src::run_count(sv.num),
                src::pair_count(sv.num), rg, gs, gk),
    ensures
        forall|db: Database| #[trigger] sources_bound(sv, db)
            ==> dst::represents(storage_parts(sv, owned_parts_view(parts)), crate::stores::num_tvg::declaration::stored_relations(db)),
{
    assert forall|db: Database| #[trigger] sources_bound(sv, db) implies dst::represents(
        storage_parts(sv, owned_parts_view(parts)), crate::stores::num_tvg::declaration::stored_relations(db)) by {
        lemma_represents(sv, db, rg, gs, gk);
    }
}

pub fn build(stores: &mut Stores, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        sources_ready(old(stores)@),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(p) ==> forall|db: Database| #[trigger] sources_bound(old(stores)@, db)
            ==> dst::represents(storage_parts(old(stores)@, owned_parts_view(p@)),
                crate::stores::num_tvg::declaration::stored_relations(db)),
        r matches Err(e) ==> e is WorkerFailed,
{
    hide(src::num_layout_ok);
    hide(src::represents);
    hide(dst::represents);
    let ghost sv = stores@;
    let ghost sp = sv.num;
    proof {
        lemma_source_layout(sv);
        lemma_source_facts(sp);
    }
    let n = stores.num.part_len(src::P_ORIG);
    let nr = stores.num.part_len(src::P_RUN_UOM);
    let ns = stores.num.part_len(src::P_RUN_START);
    let npairs = stores.num.part_len(src::P_PAIR_TAG);
    let (rg, gs, gk) = if n <= 0xffff_ffff && npairs <= 0xffff_ffff {
        let start = stores.num.extent_u64(src::P_RUN_START, 0, ns);
        let tv = stores.num.extent_u64(src::P_TV, 0, n);
        proof {
            assert(start@ =~= src::u64s(sp, src::P_RUN_START));
            assert(tv@ =~= src::u64s(sp, src::P_TV));
            assert forall|i: int| 0 <= i < n implies #[trigger] tv@[i] < npairs by {
                assert(tv@[i] < src::pair_count(sp));
            }
        }
        build_index(start, tv, nr, n, npairs)
    } else {
        (Vec::new(), Vec::new(), Vec::new())
    };
    let ghost (rgv, gsv, gkv) = (rg@, gs@, gk@);
    let mut parts: Vec<OwnedPart> = Vec::new();
    parts.push(OwnedPart::U64(rg));
    parts.push(OwnedPart::U32(gs));
    parts.push(OwnedPart::U32(gk));
    proof {
        assert(owned_parts_view(parts@) =~= seq![PartView::U64(rgv), PartView::U32(gsv), PartView::U32(gkv)]);
        lemma_all_represent(sv, parts@, rgv, gsv, gkv);
    }
    Ok(parts)
}

} // verus!
