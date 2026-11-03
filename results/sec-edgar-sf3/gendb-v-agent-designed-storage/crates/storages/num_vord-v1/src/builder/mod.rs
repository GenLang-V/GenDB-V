//! Builder of storage `num_vord`: keeps the 27 parts of storage `num` (inherited, linked unchanged) and adds
//! `vorder` (`interface::vorder_ok`): for every uom code `u`, the stored rows `[unit_row(u), unit_row(u + 1))`
//! sorted by value descending (ties by row), written at the same positions of `vorder`.
//! Per unit: one `VKey` (value, row) per row, sorted by the parallel merge sort, then the rows of the sorted keys.
//! The proof: the keys' rows are the unit's span (so the sorted rows have its multiset), and each sorted key is the
//! key of its own row (so the rows are ordered by value); units are disjoint ranges in increasing order, so writing
//! one leaves the earlier ones unchanged. The inherited parts carry num's `represents` over to num_vord's.
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::layout::{owned_parts_view, PartView};
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::spec::value::Database;
use crate::stores::num::interface as src;
use crate::stores::num_vord::interface as dst;
use crate::stores::num_vord::interface::common::perm::lemma_multiset_map;
use crate::stores::num::interface::common::runs::{runs_partition_ok, group_starts_ok};
pub mod common;
use common::sort::{par_sort, VKey, ValueDescOrder, SortOrder};

verus! {

broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms};

/// The value order of the rows `[lo, hi)` at positions `[lo, hi)` of `vo`: the span's multiset, values
/// nonincreasing.
pub open spec fn order_facts(value: Seq<i128>, vo: Seq<u64>, lo: int, hi: int) -> bool {
    &&& 0 <= lo <= hi <= vo.len()
    &&& vo.subrange(lo, hi).to_multiset() == dst::span(lo, hi).to_multiset()
    &&& forall|p: int, q: int| lo <= p < q < hi ==> #[trigger] value[vo[p] as int] >= #[trigger] value[vo[q] as int]
}

/// The first stored row of uom code `u` in the source parts.
pub open spec fn src_unit_row(sp: Seq<PartView>, u: int) -> int {
    src::u64s(sp, src::P_RUN_START)[src::u64s(sp, src::P_UOM_RUNS)[u] as int] as int
}

/// The value of the source parts' stored rows.
pub open spec fn src_value(sp: Seq<PartView>) -> Seq<i128> {
    src::common::cols::i128_part(sp[src::P_VALUE as int])
}

/// Every unit before `u` is ordered in `vo`.
pub open spec fn units_done(sp: Seq<PartView>, vo: Seq<u64>, u: int) -> bool {
    forall|w: int| 0 <= w < u ==> #[trigger] order_facts(src_value(sp), vo, src_unit_row(sp, w), src_unit_row(sp, w + 1))
}

/// The key of row `i`.
pub open spec fn vkey_of(value: Seq<i128>, i: int) -> VKey {
    VKey { v: value[i], row: i as u64 }
}

pub open spec fn key_row(e: VKey) -> u64 {
    e.row
}

/// Some database is bound to the source: num's layout holds.
proof fn lemma_source_layout(sv: StoresView)
    requires sources_ready(sv),
    ensures src::num_layout_ok(sv.num),
{
    let db = choose|db: Database| #[trigger] sources_bound(sv, db);
}

/// The source facts the builder reads.
proof fn lemma_source_facts(sp: Seq<PartView>)
    requires src::num_layout_ok(sp),
    ensures
        sp.len() == 27,
        sp[src::P_ORIG as int] is U64, sp[src::P_RUN_START as int] is U64, sp[src::P_UOM_RUNS as int] is U64,
        sp[src::P_UOM_OFF as int] is U64, sp[src::P_VALUE as int] is I128, sp[src::P_RUN_UOM as int] is U64,
        src::uom_count(sp) >= 0,
        src::u64s(sp, src::P_UOM_RUNS).len() == src::uom_count(sp) + 1,
        src_value(sp).len() == src::row_count(sp),
        runs_partition_ok(src::u64s(sp, src::P_RUN_START), src::run_count(sp), src::row_count(sp)),
        group_starts_ok(src::u64s(sp, src::P_UOM_RUNS), src::u64s(sp, src::P_RUN_UOM), src::uom_count(sp)),
{
}

/// Unit starts are nondecreasing and at most `n`.
proof fn lemma_unit_rows(sp: Seq<PartView>, a: int, b: int)
    requires src::num_layout_ok(sp), 0 <= a <= b <= src::uom_count(sp),
    ensures 0 <= src_unit_row(sp, a) <= src_unit_row(sp, b) <= src::row_count(sp),
{
    lemma_source_facts(sp);
    let g = src::u64s(sp, src::P_UOM_RUNS);
    let k0 = src::u64s(sp, src::P_RUN_UOM);
    let start = src::u64s(sp, src::P_RUN_START);
    let nr = src::run_count(sp);
    assert(g[a] <= k0.len() && g[b] <= k0.len());
    if g[b] < g[a] {
        let r = g[b] as int;
        assert(r < g[a] <==> k0[r] < a);
        assert(r < g[b] <==> k0[r] < b);
    }
    assert(g[a] <= g[b]);
    if g[a] < g[b] {
        assert(start[g[a] as int] < start[g[b] as int]);
    }
    if (g[b] as int) < nr {
        assert(start[g[b] as int] < start[nr]);
    }
    if 0 < g[a] {
        assert(start[0] < start[g[a] as int]);
    }
}

/// The rows `[lo, hi)` sorted by value descending (ties by row).
fn sort_unit(value: &[i128], lo: usize, hi: usize, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<u64>, QueryError>)
    requires lo <= hi <= value@.len(), 1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(rows) ==> rows@.len() == hi - lo
            && rows@.to_multiset() == dst::span(lo as int, hi as int).to_multiset()
            && forall|p: int, q: int| 0 <= p < q < rows@.len()
                ==> #[trigger] value@[rows@[p] as int] >= #[trigger] value@[rows@[q] as int],
        r matches Err(e) ==> e is WorkerFailed,
{
    let n = hi - lo;
    let mut keys: Vec<VKey> = Vec::with_capacity(n);
    let mut i = lo;
    while i < hi
        invariant
            lo <= i <= hi <= value@.len(), keys@.len() == i - lo,
            forall|k: int| 0 <= k < keys@.len() ==> #[trigger] keys@[k] == vkey_of(value@, lo + k),
        decreases hi - i,
    {
        keys.push(VKey { v: value[i], row: i as u64 });
        i = i + 1;
    }
    let ghost kv = keys@;
    let sorted = par_sort(ValueDescOrder {}, keys, workers, dispatch)?;
    let ghost s = sorted@;
    proof {
        assert(s.len() == s.to_multiset().len());
        assert(kv.len() == kv.to_multiset().len());
    }
    let mut rows: Vec<u64> = Vec::with_capacity(n);
    let mut q: usize = 0;
    while q < n
        invariant
            q <= n, sorted@.len() == n, s == sorted@,
            rows@ == s.subrange(0, q as int).map_values(|e: VKey| key_row(e)),
        decreases n - q,
    {
        rows.push(sorted[q].row);
        q = q + 1;
        proof {
            assert(rows@ =~= s.subrange(0, q as int).map_values(|e: VKey| key_row(e)));
        }
    }
    proof {
        let f = |e: VKey| key_row(e);
        assert(s.subrange(0, n as int) =~= s);
        lemma_multiset_map(s, kv, f);
        assert(kv.map_values(f) =~= dst::span(lo as int, hi as int));
        // Every sorted key is the key of its own row.
        assert forall|a: int| 0 <= a < n implies #[trigger] s[a] == vkey_of(value@, s[a].row as int) by {
            assert(s.to_multiset().count(s[a]) > 0);
            assert(kv.to_multiset().count(s[a]) > 0);
            assert(kv.contains(s[a]));
            let k = choose|k: int| 0 <= k < kv.len() && kv[k] == s[a];
            assert(kv[k] == vkey_of(value@, lo + k));
        }
        assert forall|p: int, q: int| 0 <= p < q < rows@.len()
            implies #[trigger] value@[rows@[p] as int] >= #[trigger] value@[rows@[q] as int] by {
            assert(ValueDescOrder {}.le(s[p], s[q]));
            assert(s[p] == vkey_of(value@, s[p].row as int));
            assert(s[q] == vkey_of(value@, s[q].row as int));
            assert(rows@[p] == s[p].row && rows@[q] == s[q].row);
        }
    }
    Ok(rows)
}

/// Writing below position `lo` is not done: an order of rows `[a, b)` with `b <= lo` survives writes at `lo` on.
proof fn lemma_order_kept(value: Seq<i128>, v1: Seq<u64>, v2: Seq<u64>, a: int, b: int, lo: int)
    requires
        order_facts(value, v1, a, b), b <= lo, v1.len() == v2.len(),
        forall|x: int| 0 <= x < lo ==> #[trigger] v2[x] == v1[x],
    ensures order_facts(value, v2, a, b),
{
    assert(v2.subrange(a, b) =~= v1.subrange(a, b));
    assert forall|p: int, q: int| a <= p < q < b implies #[trigger] value[v2[p] as int] >= #[trigger] value[v2[q] as int] by {
        assert(v2[p] == v1[p] && v2[q] == v1[q]);
    }
}

/// `rows` copied to positions `[lo, hi)`: the order facts of `[lo, hi)`.
proof fn lemma_order_written(value: Seq<i128>, vo: Seq<u64>, rows: Seq<u64>, lo: int, hi: int)
    requires
        0 <= lo <= hi <= vo.len(), rows.len() == hi - lo,
        forall|x: int| lo <= x < hi ==> #[trigger] vo[x] == rows[x - lo],
        rows.to_multiset() == dst::span(lo, hi).to_multiset(),
        forall|p: int, q: int| 0 <= p < q < rows.len() ==> #[trigger] value[rows[p] as int] >= #[trigger] value[rows[q] as int],
    ensures order_facts(value, vo, lo, hi),
{
    assert(vo.subrange(lo, hi) =~= rows);
    assert forall|p: int, q: int| lo <= p < q < hi implies #[trigger] value[vo[p] as int] >= #[trigger] value[vo[q] as int] by {
        assert(vo[p] == rows[p - lo] && vo[q] == rows[q - lo]);
        assert(value[rows[p - lo] as int] >= value[rows[q - lo] as int]);
    }
}

/// The value order of every unit (`vo` starts as `n` zeros).
fn build_order(start: &[u64], uom_runs: &[u64], value: &[i128], nu: usize, n: usize, workers: usize,
    dispatch: &mut Dispatch, Ghost(sp): Ghost<Seq<PartView>>) -> (r: Result<Vec<u64>, QueryError>)
    requires
        src::num_layout_ok(sp),
        start@ == src::u64s(sp, src::P_RUN_START),
        uom_runs@ == src::u64s(sp, src::P_UOM_RUNS),
        value@ == src_value(sp),
        nu == src::uom_count(sp), n == src::row_count(sp),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(vo) ==> vo@.len() == n && units_done(sp, vo@, nu as int),
        r matches Err(e) ==> e is WorkerFailed,
{
    proof { lemma_source_facts(sp); }
    let mut vo: Vec<u64> = crate::gendb_entry::work::filled(n, 0u64);
    let mut u: usize = 0;
    while u < nu
        invariant
            src::num_layout_ok(sp),
            start@ == src::u64s(sp, src::P_RUN_START),
            uom_runs@ == src::u64s(sp, src::P_UOM_RUNS),
            value@ == src_value(sp),
            nu == src::uom_count(sp), n == src::row_count(sp),
            uom_runs@.len() == nu + 1,
            start@.len() == src::run_count(sp) + 1,
            value@.len() == n,
            1 <= workers <= MAX_WORKERS,
            u <= nu, vo@.len() == n,
            units_done(sp, vo@, u as int),
        decreases nu - u,
    {
        proof {
            lemma_unit_rows(sp, u as int, u + 1);
            lemma_source_facts(sp);
            let g = src::u64s(sp, src::P_UOM_RUNS);
            assert(g[u as int] <= src::run_count(sp) && g[u + 1] <= src::run_count(sp));
        }
        let lo = start[uom_runs[u] as usize] as usize;
        let hi = start[uom_runs[u + 1] as usize] as usize;
        let rows = sort_unit(value, lo, hi, workers, dispatch)?;
        let ghost v0 = vo@;
        let mut k: usize = 0;
        while k < hi - lo
            invariant
                lo <= hi <= n, vo@.len() == n, rows@.len() == hi - lo, k <= hi - lo,
                forall|x: int| 0 <= x < n && !(lo <= x < lo + k) ==> #[trigger] vo@[x] == v0[x],
                forall|x: int| lo <= x < lo + k ==> #[trigger] vo@[x] == rows@[x - lo],
            decreases hi - lo - k,
        {
            vo.set(lo + k, rows[k]);
            k = k + 1;
        }
        proof {
            lemma_order_written(src_value(sp), vo@, rows@, lo as int, hi as int);
            assert forall|w: int| 0 <= w < u + 1 implies #[trigger] order_facts(src_value(sp), vo@, src_unit_row(sp, w),
                src_unit_row(sp, w + 1)) by {
                if w < u {
                    lemma_unit_rows(sp, w + 1, u as int);
                    lemma_unit_rows(sp, w, w + 1);
                    assert(order_facts(src_value(sp), v0, src_unit_row(sp, w), src_unit_row(sp, w + 1)));
                    lemma_order_kept(src_value(sp), v0, vo@, src_unit_row(sp, w), src_unit_row(sp, w + 1), lo as int);
                }
            }
        }
        u = u + 1;
    }
    Ok(vo)
}

/// The inherited parts followed by `vorder` represent num_vord's relations of every database bound to num.
proof fn lemma_represents(sv: StoresView, db: Database, vo: Seq<u64>)
    requires
        sources_bound(sv, db),
        vo.len() == src::row_count(sv.num),
        units_done(sv.num, vo, src::uom_count(sv.num)),
    ensures
        dst::represents(sv.num.push(PartView::U64(vo)), crate::stores::num_vord::declaration::stored_relations(db)),
{
    let sp = sv.num;
    let parts = sp.push(PartView::U64(vo));
    let rels = crate::stores::num::declaration::stored_relations(db);
    assert(crate::stores::num_vord::declaration::stored_relations(db) == rels);
    assert(src::represents(sp, rels));
    assert(sp.len() == 27);
    assert forall|k: int| 0 <= k < 27 implies #[trigger] parts[k] == sp[k] by {}
    lemma_layout_carries(sp, parts, vo);
    let n = src::row_count(sp);
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

/// num's layout facts on the inherited parts give num_vord's (the definitions are copies), plus the value order.
proof fn lemma_layout_carries(sp: Seq<PartView>, parts: Seq<PartView>, vo: Seq<u64>)
    requires
        src::num_layout_ok(sp),
        parts == sp.push(PartView::U64(vo)),
        vo.len() == src::row_count(sp),
        units_done(sp, vo, src::uom_count(sp)),
    ensures dst::num_layout_ok(parts),
{
    assert(sp.len() == 27);
    assert forall|k: int| 0 <= k < 27 implies #[trigger] parts[k] == sp[k] by {}
    let n = src::row_count(sp);
    assert(dst::row_count(parts) == n);
    assert(dst::run_count(parts) == src::run_count(sp));
    assert(dst::u64s(parts, dst::P_VORDER) == vo);
    assert forall|u: int| 0 <= u < dst::uom_count(parts) implies #[trigger] dst::unit_order_ok(parts, u) by {
        assert(dst::unit_row(parts, u) == src_unit_row(sp, u));
        assert(dst::unit_row(parts, u + 1) == src_unit_row(sp, u + 1));
        assert(order_facts(src_value(sp), vo, src_unit_row(sp, u), src_unit_row(sp, u + 1)));
    }
    assert(dst::vorder_ok(parts));
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

/// Every database bound to num gets num_vord's `represents` over the inherited parts and `vorder`.
proof fn lemma_all_represent(sv: StoresView, parts: Seq<OwnedPart>, vo: Seq<u64>)
    requires
        sources_ready(sv),
        owned_parts_view(parts) == seq![PartView::U64(vo)],
        vo.len() == src::row_count(sv.num),
        units_done(sv.num, vo, src::uom_count(sv.num)),
    ensures
        forall|db: Database| #[trigger] sources_bound(sv, db)
            ==> dst::represents(storage_parts(sv, owned_parts_view(parts)), crate::stores::num_vord::declaration::stored_relations(db)),
{
    assert forall|db: Database| #[trigger] sources_bound(sv, db) implies dst::represents(
        storage_parts(sv, owned_parts_view(parts)), crate::stores::num_vord::declaration::stored_relations(db)) by {
        lemma_represents(sv, db, vo);
        assert(storage_parts(sv, owned_parts_view(parts)) =~= sv.num.push(PartView::U64(vo)));
    }
}

pub fn build(stores: &mut Stores, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        sources_ready(old(stores)@),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(p) ==> forall|db: Database| #[trigger] sources_bound(old(stores)@, db)
            ==> dst::represents(storage_parts(old(stores)@, owned_parts_view(p@)),
                crate::stores::num_vord::declaration::stored_relations(db)),
        r matches Err(e) ==> e is WorkerFailed,
{
    hide(src::represents);
    hide(dst::represents);
    let ghost sv = stores@;
    let ghost sp = sv.num;
    proof {
        lemma_source_layout(sv);
        lemma_source_facts(sp);
    }
    let n = stores.num.part_len(src::P_ORIG);
    let nr1 = stores.num.part_len(src::P_RUN_START);
    let nu1 = stores.num.part_len(src::P_UOM_RUNS);
    let nu = stores.num.part_len(src::P_UOM_OFF) - 1;
    let start = stores.num.extent_u64(src::P_RUN_START, 0, nr1);
    let uom_runs = stores.num.extent_u64(src::P_UOM_RUNS, 0, nu1);
    let nv = stores.num.part_len(src::P_VALUE);
    let value = stores.num.extent_i128(src::P_VALUE, 0, nv);
    proof {
        assert(start@ =~= src::u64s(sp, src::P_RUN_START));
        assert(uom_runs@ =~= src::u64s(sp, src::P_UOM_RUNS));
        assert(value@ =~= src_value(sp));
    }
    let vo = build_order(start, uom_runs, value, nu, n, workers, dispatch, Ghost(sp))?;
    let ghost vov = vo@;
    let mut parts: Vec<OwnedPart> = Vec::new();
    parts.push(OwnedPart::U64(vo));
    proof {
        assert(owned_parts_view(parts@) =~= seq![PartView::U64(vov)]);
        lemma_all_represent(sv, parts@, vov);
    }
    Ok(parts)
}

} // verus!
