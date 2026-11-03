//! Builder of storage `num`: sorted dictionaries of uom, adsh, tag and version (parallel sorts of row ids by value),
//! a (tag, version) pair dictionary, then one parallel sort of the rows by (uom code, adsh code, pair code, row) that
//! fixes the stored order. From the sorted keys: the canonical row of each stored row (`orig`), the pair codes, the
//! (uom, adsh) runs and the uom directory; ddate and value gathered into stored order, per-run ddate bounds; qtrs,
//! coreg and footnote kept in canonical order (coreg and footnote sparse). Parts in `P_*` order.
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_source::*;
use crate::gendb_entry::parallel::Dispatch;
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::layout::{owned_parts_view, PartView};
use crate::link::query::{text_at, text_wf, TextView};
use crate::spec::value::{Row, Val};
use crate::stores::num::interface::*;
use crate::stores::num::interface::common::text::{text_entry, text_parts_wf, text_strictly_sorted, u64_part, u8_part};
use crate::stores::num::interface::common::cols::{i32_part, i128_part, text_col_ok, text_count};
use crate::stores::num::interface::common::perm::{is_permutation, lemma_permutation_facts};
use crate::stores::num::interface::common::runs::*;
pub mod common;
use common::sort::{TextOrder, SortOrder, Key4, KeyOrder, key4_le, sorted_by};
use common::dict::{build_text_dict, emit_text_list, lemma_emitted_sorted, dict_ids_ok, codes_ok, row_in};
use common::keys::{sort_row_keys, rows_of_keys, k2_of_keys, build_pair_dict, key_runs, group_starts, run_min_max,
    row_keys, key_rows, lemma_sorted_keys, runs_ok};
use common::gather::{gather, sparse_text};

verus! {

/// The text order of a delivered text column of `rows` rows.
fn text_order(c: &TextCol, rows: usize) -> (o: TextOrder)
    requires text_wf(c@, rows as int), rows < usize::MAX,
    ensures o.wf(), o.rows == rows, o.text() == c@,
{
    TextOrder { offsets: c.offsets, bytes: c.bytes, rows: rows as u64 }
}

/// A sorted dictionary of a NOT NULL text column: representative rows, per-row codes, and its text parts.
pub struct BuiltDict {
    pub ids: Vec<u64>,
    pub codes: Vec<u64>,
    pub off: Vec<u64>,
    pub bytes: Vec<u8>,
}

/// The facts a dictionary of column `o` gives.
spec fn built_dict_ok(o: TextOrder, d: BuiltDict) -> bool {
    &&& dict_ids_ok(o, d.ids@)
    &&& d.codes@.len() == o.rows
    &&& forall|i: int| 0 <= i < o.rows ==> (#[trigger] d.codes@[i]) < d.ids@.len()
        && o.value(d.ids@[d.codes@[i] as int]) == o.value(i as u64)
    &&& d.ids@.len() <= o.rows
    &&& d.off@.len() == d.ids@.len() + 1
    &&& text_parts_wf(d.off@, d.bytes@, d.ids@.len() as int)
    &&& text_strictly_sorted(d.off@, d.bytes@, d.ids@.len() as int)
    &&& forall|k: int| 0 <= k < d.ids@.len() ==> #[trigger] text_entry(d.off@, d.bytes@, k) == o.value(d.ids@[k])
}

/// Dictionary of a NOT NULL text column.
fn dictionary(o: TextOrder, any: &'static [u8], workers: usize, dispatch: &mut Dispatch) -> (r: Result<BuiltDict, QueryError>)
    requires o.wf(), 1 <= workers <= 64,
    ensures
        r matches Ok(d) ==> built_dict_ok(o, d),
        r matches Err(e) ==> e is WorkerFailed,
{
    let d = build_text_dict(o, any, false, workers, dispatch)?;
    let (off, bytes) = emit_text_list(&o, &d.ids);
    proof {
        lemma_emitted_sorted(o, d.ids@, off@, bytes@);
        assert forall|i: int| 0 <= i < o.rows implies (#[trigger] d.codes@[i]) < d.ids@.len()
            && o.value(d.ids@[d.codes@[i] as int]) == o.value(i as u64) by {
            assert(row_in(any@, false, i));
        }
    }
    Ok(BuiltDict { ids: d.ids, codes: d.codes, off, bytes })
}

pub fn build(src: &SourceRef, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires source_wf(src@), in_domain(tables(src@)), 1 <= workers <= 64,
    ensures
        r matches Ok(p) ==> represents(owned_parts_view(p@), tables(src@)),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ghost v = src@;
    let n = src.t0_f0.offsets.len() - 1;
    let adsh = text_order(&src.t0_f0, n);
    let tag = text_order(&src.t0_f1, n);
    let version = text_order(&src.t0_f2, n);
    let uom = text_order(&src.t0_f5, n);
    let uom_d = dictionary(uom, src.t0_v6, workers, dispatch)?;
    let adsh_d = dictionary(adsh, src.t0_v6, workers, dispatch)?;
    let tag_d = dictionary(tag, src.t0_v6, workers, dispatch)?;
    let version_d = dictionary(version, src.t0_v6, workers, dispatch)?;
    let pairs = build_pair_dict(&tag_d.codes, &version_d.codes, Ghost(tag_d.ids@.len() as int),
        Ghost(version_d.ids@.len() as int), workers, dispatch)?;
    let s = sort_row_keys(&uom_d.codes, &adsh_d.codes, &pairs.codes, workers, dispatch)?;
    proof {
        lemma_sorted_keys(s@, uom_d.codes@, adsh_d.codes@, pairs.codes@);
        lemma_permutation_facts(key_rows(s@), n as nat);
    }
    let orig = rows_of_keys(&s);
    let tv = k2_of_keys(&s);
    let runs = key_runs(&s);
    let uom_count = uom_d.ids.len() as u64;
    proof {
        lemma_run_keys_below(s@, runs.start@, runs.k0@, runs.k1@, uom_d.codes@, adsh_d.codes@, pairs.codes@,
            uom_d.ids@.len() as int, adsh_d.ids@.len() as int);
    }
    let uom_runs = group_starts(&runs.k0, uom_count);
    let ddate = gather(src.t0_f3, &orig);
    let value = gather(src.t0_f7, &orig);
    let (dmin, dmax) = run_min_max(&ddate, &runs.start);
    let qtrs = vstd::slice::slice_to_vec(src.t0_f4);
    let coreg = text_order(&src.t0_f6, n);
    let (coreg_rows, coreg_off, coreg_bytes) = sparse_text(&coreg, src.t0_v6);
    let footnote = text_order(&src.t0_f8, n);
    let (fn_rows, fn_off, fn_bytes) = sparse_text(&footnote, src.t0_v8);
    let ghost views = seq![
        PartView::U64(orig@), PartView::U64(runs.start@), PartView::U64(runs.k0@), PartView::U64(runs.k1@),
        PartView::U64(uom_runs@),
        PartView::U64(uom_d.off@), PartView::U8(uom_d.bytes@),
        PartView::U64(adsh_d.off@), PartView::U8(adsh_d.bytes@),
        PartView::U64(tv@), PartView::U64(pairs.first@), PartView::U64(pairs.second@),
        PartView::U64(tag_d.off@), PartView::U8(tag_d.bytes@),
        PartView::U64(version_d.off@), PartView::U8(version_d.bytes@),
        PartView::I32(ddate@), PartView::I128(value@), PartView::I32(dmin@), PartView::I32(dmax@),
        PartView::I32(qtrs@),
        PartView::U64(coreg_rows@), PartView::U64(coreg_off@), PartView::U8(coreg_bytes@),
        PartView::U64(fn_rows@), PartView::U64(fn_off@), PartView::U8(fn_bytes@)
    ];
    let ghost g_uom = uom_d;
    let ghost g_adsh = adsh_d;
    let ghost g_tag = tag_d;
    let ghost g_version = version_d;
    let ghost g_pairs = (pairs.first@, pairs.second@, pairs.codes@);
    let ghost g_runs = (runs.start@, runs.k0@, runs.k1@);
    let mut parts: Vec<OwnedPart> = Vec::new();
    parts.push(OwnedPart::U64(orig));
    parts.push(OwnedPart::U64(runs.start));
    parts.push(OwnedPart::U64(runs.k0));
    parts.push(OwnedPart::U64(runs.k1));
    parts.push(OwnedPart::U64(uom_runs));
    parts.push(OwnedPart::U64(uom_d.off));
    parts.push(OwnedPart::U8(uom_d.bytes));
    parts.push(OwnedPart::U64(adsh_d.off));
    parts.push(OwnedPart::U8(adsh_d.bytes));
    parts.push(OwnedPart::U64(tv));
    parts.push(OwnedPart::U64(pairs.first));
    parts.push(OwnedPart::U64(pairs.second));
    parts.push(OwnedPart::U64(tag_d.off));
    parts.push(OwnedPart::U8(tag_d.bytes));
    parts.push(OwnedPart::U64(version_d.off));
    parts.push(OwnedPart::U8(version_d.bytes));
    parts.push(OwnedPart::I32(ddate));
    parts.push(OwnedPart::I128(value));
    parts.push(OwnedPart::I32(dmin));
    parts.push(OwnedPart::I32(dmax));
    parts.push(OwnedPart::I32(qtrs));
    parts.push(OwnedPart::U64(coreg_rows));
    parts.push(OwnedPart::U64(coreg_off));
    parts.push(OwnedPart::U8(coreg_bytes));
    parts.push(OwnedPart::U64(fn_rows));
    parts.push(OwnedPart::U64(fn_off));
    parts.push(OwnedPart::U8(fn_bytes));
    proof {
        assert(owned_parts_view(parts@) =~= views);
        let b = NumBuild { v, pv: views, uom, adsh, tag, version, du: g_uom, da: g_adsh, dt: g_tag, dv: g_version,
            pf: g_pairs.0, ps: g_pairs.1, pc: g_pairs.2, s: s@, start: g_runs.0, k0: g_runs.1, k1: g_runs.2,
            coreg, footnote };
        assert(f_orders(b)) by { reveal(f_orders); }
        assert(f_dicts(b)) by { reveal(f_dicts); }
        assert(f_pairs(b)) by { reveal(f_pairs); }
        assert(f_keys(b)) by { reveal(f_keys); }
        assert(f_runs(b)) by { reveal(f_runs); }
        assert(f_parts(b)) by { reveal(f_parts); }
        assert(f_values(b)) by { reveal(f_values); }
        lemma_num_layout(b);
        lemma_num_rows(b);
    }
    Ok(parts)
}

/// Run keys are codes of the dictionaries, and `k0` never decreases across runs.
proof fn lemma_run_keys_below(s: Seq<Key4>, start: Seq<u64>, k0: Seq<u64>, k1: Seq<u64>,
    a: Seq<u64>, b: Seq<u64>, c: Seq<u64>, na: int, nb: int)
    requires
        runs_ok(s, start, k0, k1),
        forall|q: int| 0 <= q < s.len() ==> (#[trigger] s[q]).k3 < a.len() && s[q] == row_keys(a, b, c)[s[q].k3 as int],
        a.len() == b.len(), a.len() == c.len(),
        forall|j: int| 0 <= j < a.len() ==> #[trigger] a[j] < na && b[j] < nb,
    ensures
        forall|r: int| 0 <= r < k0.len() ==> #[trigger] k0[r] < na && k1[r] < nb,
        forall|p: int, q: int| 0 <= p < q < k0.len() ==> #[trigger] k0[p] <= #[trigger] k0[q],
{
    assert forall|r: int| 0 <= r < k0.len() implies #[trigger] k0[r] < na && k1[r] < nb by {
        let i = start[r] as int;
        assert(start[r] < start[r + 1]);
        lemma_start_le_len(start, k0.len() as int, s.len() as int, r + 1);
        assert(s[i].k0 == k0[r] && s[i].k1 == k1[r]);
        let j = s[i].k3 as int;
        assert(a[j] < na && b[j] < nb);
    }
    assert forall|p: int, q: int| 0 <= p < q < k0.len() implies #[trigger] k0[p] <= #[trigger] k0[q] by {
        assert(pair_lt(k0[p], k1[p], k0[q], k1[q]));
    }
}

/// Run starts stay within the rows.
proof fn lemma_start_le_len(start: Seq<u64>, nr: int, n: int, r: int)
    requires runs_partition_ok(start, nr, n), 0 <= r <= nr,
    ensures start[r] <= n,
{
    if r < nr {
        assert(start[r] < start[nr]);
    }
}

/// Everything the builder computed, as sequences (ghost).
pub struct NumBuild {
    pub v: SourceView,
    pub pv: Seq<PartView>,
    pub uom: TextOrder,
    pub adsh: TextOrder,
    pub tag: TextOrder,
    pub version: TextOrder,
    pub du: BuiltDict,
    pub da: BuiltDict,
    pub dt: BuiltDict,
    pub dv: BuiltDict,
    pub pf: Seq<u64>,
    pub ps: Seq<u64>,
    pub pc: Seq<u64>,
    pub s: Seq<Key4>,
    pub start: Seq<u64>,
    pub k0: Seq<u64>,
    pub k1: Seq<u64>,
    pub coreg: TextOrder,
    pub footnote: TextOrder,
}

/// Row count of the source.
spec fn nrows(b: NumBuild) -> int {
    source_rows_t0(b.v)
}

/// The text orders read the delivered columns.
#[verifier::opaque]
spec fn f_orders(b: NumBuild) -> bool {
    let n = nrows(b);
    &&& source_wf(b.v)
    &&& b.uom.text() == b.v.t0_f5 && b.adsh.text() == b.v.t0_f0 && b.tag.text() == b.v.t0_f1 && b.version.text() == b.v.t0_f2
    &&& b.coreg.text() == b.v.t0_f6 && b.footnote.text() == b.v.t0_f8
    &&& b.uom.rows == n && b.adsh.rows == n && b.tag.rows == n && b.version.rows == n && b.coreg.rows == n && b.footnote.rows == n
    &&& b.uom.wf() && b.adsh.wf() && b.tag.wf() && b.version.wf() && b.coreg.wf() && b.footnote.wf()
}

/// The four dictionaries.
#[verifier::opaque]
spec fn f_dicts(b: NumBuild) -> bool {
    &&& built_dict_ok(b.uom, b.du) && built_dict_ok(b.adsh, b.da) && built_dict_ok(b.tag, b.dt) && built_dict_ok(b.version, b.dv)
    &&& b.du.codes@.len() == nrows(b) && b.da.codes@.len() == nrows(b)
}

/// The pair dictionary and the rows' pair codes.
#[verifier::opaque]
spec fn f_pairs(b: NumBuild) -> bool {
    let n = nrows(b);
    &&& pairs_increasing(b.pf, b.ps) && b.pc.len() == n
    &&& forall|j: int| 0 <= j < n ==> (#[trigger] b.pc[j]) < b.pf.len() && b.pf[b.pc[j] as int] == b.dt.codes@[j]
        && b.ps[b.pc[j] as int] == b.dv.codes@[j]
    &&& forall|q: int| 0 <= q < b.pf.len() ==> #[trigger] b.pf[q] < b.dt.ids@.len() && b.ps[q] < b.dv.ids@.len()
}

/// The sorted row keys.
#[verifier::opaque]
spec fn f_keys(b: NumBuild) -> bool {
    let n = nrows(b);
    &&& sorted_by(KeyOrder {}, b.s)
    &&& b.s.len() == n
    &&& is_permutation(key_rows(b.s), n as nat)
    &&& forall|q: int| 0 <= q < b.s.len() ==> (#[trigger] b.s[q]).k3 < n
        && b.s[q] == row_keys(b.du.codes@, b.da.codes@, b.pc)[b.s[q].k3 as int]
}

/// The runs of the sorted keys.
#[verifier::opaque]
spec fn f_runs(b: NumBuild) -> bool {
    runs_ok(b.s, b.start, b.k0, b.k1)
}

/// The parts (except per-row values) as built.
#[verifier::opaque]
spec fn f_parts(b: NumBuild) -> bool {
    let pv = b.pv;
    let n = nrows(b);
    &&& pv.len() == PART_COUNT
    &&& pv[P_ORIG as int] == PartView::U64(key_rows(b.s))
    &&& pv[P_RUN_START as int] == PartView::U64(b.start)
    &&& pv[P_RUN_UOM as int] == PartView::U64(b.k0)
    &&& pv[P_RUN_ADSH as int] == PartView::U64(b.k1)
    &&& pv[P_UOM_RUNS as int] is U64 && group_starts_ok(u64_part(pv[P_UOM_RUNS as int]), b.k0, b.du.ids@.len() as int)
    &&& pv[P_UOM_OFF as int] == PartView::U64(b.du.off@) && pv[P_UOM_BYTES as int] == PartView::U8(b.du.bytes@)
    &&& pv[P_ADSH_OFF as int] == PartView::U64(b.da.off@) && pv[P_ADSH_BYTES as int] == PartView::U8(b.da.bytes@)
    &&& pv[P_TV as int] is U64 && u64_part(pv[P_TV as int]).len() == n
    &&& forall|i: int| 0 <= i < n ==> #[trigger] u64_part(pv[P_TV as int])[i] == b.s[i].k2
    &&& pv[P_PAIR_TAG as int] == PartView::U64(b.pf) && pv[P_PAIR_VERSION as int] == PartView::U64(b.ps)
    &&& pv[P_TAG_OFF as int] == PartView::U64(b.dt.off@) && pv[P_TAG_BYTES as int] == PartView::U8(b.dt.bytes@)
    &&& pv[P_VERSION_OFF as int] == PartView::U64(b.dv.off@) && pv[P_VERSION_BYTES as int] == PartView::U8(b.dv.bytes@)
}

/// The per-row values, run bounds and canonical columns as built.
#[verifier::opaque]
spec fn f_values(b: NumBuild) -> bool {
    let pv = b.pv;
    let n = nrows(b);
    let v = b.v;
    &&& pv.len() == PART_COUNT
    &&& pv[P_DDATE as int] is I32 && i32_part(pv[P_DDATE as int]).len() == n
    &&& forall|i: int| 0 <= i < n ==> #[trigger] i32_part(pv[P_DDATE as int])[i] == v.t0_f3[key_rows(b.s)[i] as int]
    &&& pv[P_VALUE as int] is I128 && i128_part(pv[P_VALUE as int]).len() == n
    &&& forall|i: int| 0 <= i < n ==> #[trigger] i128_part(pv[P_VALUE as int])[i] == v.t0_f7[key_rows(b.s)[i] as int]
    &&& pv[P_RUN_DDATE_MIN as int] is I32 && pv[P_RUN_DDATE_MAX as int] is I32
    &&& run_bounds_ok(i32_part(pv[P_DDATE as int]), b.start, i32_part(pv[P_RUN_DDATE_MIN as int]), i32_part(pv[P_RUN_DDATE_MAX as int]))
    &&& pv[P_QTRS as int] == PartView::I32(v.t0_f4)
    &&& sparse_built(pv, P_COREG_ROWS, b.coreg, v.t0_v6)
    &&& sparse_built(pv, P_FOOTNOTE_ROWS, b.footnote, v.t0_v8)
}

/// All the builder facts.
spec fn built(b: NumBuild) -> bool {
    f_orders(b) && f_dicts(b) && f_pairs(b) && f_keys(b) && f_runs(b) && f_parts(b) && f_values(b)
}

/// Parts `p`, `p + 1`, `p + 2` are the sparse form of nullable column `o` (validity `valid`).
spec fn sparse_built(pv: Seq<PartView>, p: usize, o: TextOrder, valid: Seq<u8>) -> bool {
    let rows = u64_part(pv[p as int]);
    let off = u64_part(pv[p + 1]);
    let bytes = u8_part(pv[p + 2]);
    &&& pv[p as int] is U64 && pv[p + 1] is U64 && pv[p + 2] is U8
    &&& valid.len() == o.rows
    &&& forall|a: int, b: int| 0 <= a < b < rows.len() ==> #[trigger] rows[a] < #[trigger] rows[b]
    &&& forall|k: int| 0 <= k < rows.len() ==> #[trigger] rows[k] < o.rows && valid[rows[k] as int] != 0
    &&& forall|i: int| 0 <= i < o.rows && valid[i] != 0 ==> rows.contains(i as u64)
    &&& text_parts_wf(off, bytes, rows.len() as int)
    &&& forall|k: int| 0 <= k < rows.len() ==> #[trigger] text_entry(off, bytes, k) == o.value(rows[k])
}

/// Layout facts: part count, types, sizes.
proof fn lemma_layout_shape(b: NumBuild)
    requires built(b),
    ensures
        b.pv.len() == PART_COUNT,
        b.pv[P_ORIG as int] is U64 && b.pv[P_RUN_START as int] is U64 && b.pv[P_RUN_UOM as int] is U64,
        b.pv[P_RUN_ADSH as int] is U64 && b.pv[P_UOM_RUNS as int] is U64 && b.pv[P_TV as int] is U64,
        b.pv[P_PAIR_TAG as int] is U64 && b.pv[P_PAIR_VERSION as int] is U64,
        b.pv[P_DDATE as int] is I32 && b.pv[P_VALUE as int] is I128 && b.pv[P_QTRS as int] is I32,
        b.pv[P_RUN_DDATE_MIN as int] is I32 && b.pv[P_RUN_DDATE_MAX as int] is I32,
        row_count(b.pv) == nrows(b),
        run_count(b.pv) == b.k0.len(),
        u64s(b.pv, P_RUN_START) == b.start,
        u64s(b.pv, P_RUN_UOM) == b.k0,
        u64s(b.pv, P_RUN_ADSH) == b.k1,
        uom_count(b.pv) == b.du.ids@.len(), adsh_count(b.pv) == b.da.ids@.len(),
        tag_count(b.pv) == b.dt.ids@.len(), version_count(b.pv) == b.dv.ids@.len(),
        pair_count(b.pv) == b.pf.len(),
        u64s(b.pv, P_PAIR_TAG) == b.pf, u64s(b.pv, P_PAIR_VERSION) == b.ps,
{
    reveal(f_parts);
    reveal(f_values);
    reveal(f_keys);
    reveal(f_dicts);
    reveal(f_pairs);
}

/// Layout facts: the permutation, runs and uom directory.
proof fn lemma_layout_runs(b: NumBuild)
    requires built(b),
    ensures
        is_permutation(u64s(b.pv, P_ORIG), row_count(b.pv) as nat),
        runs_partition_ok(b.start, b.k0.len() as int, nrows(b)),
        b.k1.len() == b.k0.len(),
        pairs_increasing(b.k0, b.k1),
        forall|r: int| 0 <= r < b.k0.len() ==> #[trigger] b.k0[r] < b.du.ids@.len() && b.k1[r] < b.da.ids@.len(),
        group_starts_ok(u64s(b.pv, P_UOM_RUNS), b.k0, b.du.ids@.len() as int),
{
    lemma_layout_shape(b);
    reveal(f_parts);
    reveal(f_keys);
    reveal(f_runs);
    reveal(f_dicts);
    reveal(f_pairs);
    assert(b.s.len() == nrows(b));
    assert forall|j: int| 0 <= j < b.du.codes@.len() implies #[trigger] b.du.codes@[j] < b.du.ids@.len()
        && b.da.codes@[j] < b.da.ids@.len() by {
        reveal(f_orders);
    }
    lemma_run_keys_below(b.s, b.start, b.k0, b.k1, b.du.codes@, b.da.codes@, b.pc, b.du.ids@.len() as int,
        b.da.ids@.len() as int);
}

/// Layout facts: dictionaries, pair list and pair codes.
proof fn lemma_layout_dicts(b: NumBuild)
    requires built(b),
    ensures
        dict_ok(b.pv, P_UOM_OFF), dict_ok(b.pv, P_ADSH_OFF), dict_ok(b.pv, P_TAG_OFF), dict_ok(b.pv, P_VERSION_OFF),
        u64s(b.pv, P_TV).len() == nrows(b),
        forall|i: int| 0 <= i < nrows(b) ==> #[trigger] u64s(b.pv, P_TV)[i] < b.pf.len(),
        pairs_increasing(b.pf, b.ps),
        forall|p: int| 0 <= p < b.pf.len() ==> #[trigger] b.pf[p] < b.dt.ids@.len() && b.ps[p] < b.dv.ids@.len(),
{
    reveal(f_parts);
    reveal(f_dicts);
    reveal(f_pairs);
    let n = nrows(b);
    let tv = u64_part(b.pv[P_TV as int]);
    assert forall|i: int| 0 <= i < n implies #[trigger] tv[i] < b.pf.len() by {
        reveal(f_keys);
        assert(b.s[i] == row_keys(b.du.codes@, b.da.codes@, b.pc)[b.s[i].k3 as int]);
    }
}

/// Every row of run `r` has the run's key.
proof fn lemma_run_member(s: Seq<Key4>, start: Seq<u64>, k0: Seq<u64>, k1: Seq<u64>, r: int, i: int)
    requires runs_ok(s, start, k0, k1), 0 <= r < k0.len(), start[r] <= i < start[r + 1],
    ensures s[i].k0 == k0[r] && s[i].k1 == k1[r],
{
}

/// Layout facts: pair codes never decrease inside a run.
proof fn lemma_layout_tv_order(b: NumBuild)
    requires built(b),
    ensures
        forall|r: int, i: int, j: int| #![trigger b.start[r], u64s(b.pv, P_TV)[i], u64s(b.pv, P_TV)[j]]
            0 <= r < b.k0.len() && b.start[r] <= i < j < b.start[r + 1] ==> u64s(b.pv, P_TV)[i] <= u64s(b.pv, P_TV)[j],
{
    reveal(f_parts);
    reveal(f_keys);
    reveal(f_runs);
    let n = nrows(b);
    let tv = u64_part(b.pv[P_TV as int]);
    let s = b.s;
    let start = b.start;
    let k0 = b.k0;
    let k1 = b.k1;
    assert forall|r: int, i: int, j: int| #![trigger start[r], tv[i], tv[j]] 0 <= r < k0.len() && start[r] <= i < j < start[r + 1]
        implies tv[i] <= tv[j] by {
        lemma_start_le_len(start, k0.len() as int, n, r + 1);
        lemma_run_member(s, start, k0, k1, r, i);
        lemma_run_member(s, start, k0, k1, r, j);
        assert(key4_le(s[i], s[j]));
    }
}

/// Layout facts: per-row values, run bounds and canonical columns.
proof fn lemma_layout_values(b: NumBuild)
    requires built(b),
    ensures
        i32_part(b.pv[P_DDATE as int]).len() == nrows(b),
        i128_part(b.pv[P_VALUE as int]).len() == nrows(b),
        run_bounds_ok(i32_part(b.pv[P_DDATE as int]), b.start, i32_part(b.pv[P_RUN_DDATE_MIN as int]),
            i32_part(b.pv[P_RUN_DDATE_MAX as int])),
        i32_part(b.pv[P_QTRS as int]).len() == nrows(b),
        sparse_ok(b.pv, P_COREG_ROWS, nrows(b)),
        sparse_ok(b.pv, P_FOOTNOTE_ROWS, nrows(b)),
{
    reveal(f_values);
    reveal(f_orders);
    lemma_sparse_ok(b.pv, P_COREG_ROWS, b.coreg, b.v.t0_v6);
    lemma_sparse_ok(b.pv, P_FOOTNOTE_ROWS, b.footnote, b.v.t0_v8);
}

/// The assembled parts satisfy the layout facts.
proof fn lemma_num_layout(b: NumBuild)
    requires built(b),
    ensures
        num_layout_ok(b.pv),
        row_count(b.pv) == nrows(b),
        run_count(b.pv) == b.k0.len(),
        u64s(b.pv, P_RUN_START) == b.start,
{
    lemma_layout_shape(b);
    lemma_layout_runs(b);
    lemma_layout_dicts(b);
    lemma_layout_tv_order(b);
    lemma_layout_values(b);
}

/// The sparse parts satisfy the layout's sparse facts.
proof fn lemma_sparse_ok(pv: Seq<PartView>, p: usize, o: TextOrder, valid: Seq<u8>)
    requires sparse_built(pv, p, o, valid), p + 2 < pv.len(),
    ensures sparse_ok(pv, p, o.rows as int),
{
}

/// The value of a sparse column at canonical row `j` is the column's value there.
proof fn lemma_sparse_value(pv: Seq<PartView>, p: usize, o: TextOrder, valid: Seq<u8>, j: int)
    requires sparse_built(pv, p, o, valid), p + 2 < pv.len(), 0 <= j < o.rows,
    ensures sparse_at(pv, p, j) == crate::gendb_source::or_null(valid[j], Val::Text(o.value(j as u64))),
{
    let rows = u64_part(pv[p as int]);
    if valid[j] != 0 {
        assert(rows.contains(j as u64));
        let k = choose|k: int| 0 <= k < rows.len() && rows[k] == j as u64;
        lemma_sparse_index(rows, o.rows as int, k);
        assert(text_entry(u64_part(pv[p + 1]), u8_part(pv[p + 2]), k) == o.value(rows[k]));
    } else {
        if sparse_has(rows, j) {
            let k = choose|k: int| 0 <= k < rows.len() && rows[k] == j;
            assert(valid[rows[k] as int] != 0);
        }
    }
}

/// Columns held per stored row.
proof fn lemma_stored_cols(b: NumBuild, i: int)
    requires built(b), 0 <= i < nrows(b),
    ensures stored_cols_ok(b.pv, stored_row(b.pv, tables(b.v), i), i),
{
    reveal(f_parts);
    reveal(f_keys);
    reveal(f_dicts);
    reveal(f_pairs);
    reveal(f_orders);
    reveal(f_values);
    let s = b.s;
    let pv = b.pv;
    let j = s[i].k3 as int;
    assert(key_rows(s)[i] == s[i].k3);
    assert(s[i] == row_keys(b.du.codes@, b.da.codes@, b.pc)[j]);
    let t = table_t0(b.v);
    assert(stored_row(pv, tables(b.v), i) == t[j]);
    assert(u64_part(pv[P_TV as int])[i] == b.pc[j]);
    assert(tag_of(pv, i) == text_entry(b.dt.off@, b.dt.bytes@, b.dt.codes@[j] as int));
    assert(tag_of(pv, i) == b.tag.value(j as u64));
    assert(version_of(pv, i) == text_entry(b.dv.off@, b.dv.bytes@, b.dv.codes@[j] as int));
    assert(version_of(pv, i) == b.version.value(j as u64));
}

/// Columns held per run.
proof fn lemma_run_cols(b: NumBuild, r: int, i: int)
    requires built(b), 0 <= r < b.k0.len(), b.start[r] <= i < b.start[r + 1],
    ensures run_cols_ok(b.pv, stored_row(b.pv, tables(b.v), i), r),
{
    reveal(f_parts);
    reveal(f_keys);
    reveal(f_runs);
    reveal(f_dicts);
    reveal(f_orders);
    let s = b.s;
    let pv = b.pv;
    lemma_start_le_len(b.start, b.k0.len() as int, s.len() as int, r + 1);
    let j = s[i].k3 as int;
    assert(key_rows(s)[i] == s[i].k3);
    assert(s[i] == row_keys(b.du.codes@, b.da.codes@, b.pc)[j]);
    assert(s[i].k0 == b.k0[r] && s[i].k1 == b.k1[r]);
    let t = table_t0(b.v);
    assert(stored_row(pv, tables(b.v), i) == t[j]);
    assert(run_uom_of(pv, r) == text_entry(b.du.off@, b.du.bytes@, b.du.codes@[j] as int));
    assert(run_uom_of(pv, r) == b.uom.value(j as u64));
    assert(run_adsh_of(pv, r) == text_entry(b.da.off@, b.da.bytes@, b.da.codes@[j] as int));
    assert(run_adsh_of(pv, r) == b.adsh.value(j as u64));
}

/// Columns held in canonical row order.
proof fn lemma_canon_cols(b: NumBuild, j: int)
    requires built(b), 0 <= j < nrows(b),
    ensures canon_cols_ok(b.pv, tables(b.v)[0][j], j),
{
    reveal(f_values);
    reveal(f_orders);
    lemma_sparse_value(b.pv, P_COREG_ROWS, b.coreg, b.v.t0_v6, j);
    lemma_sparse_value(b.pv, P_FOOTNOTE_ROWS, b.footnote, b.v.t0_v8, j);
}

/// Every row fact of `represents`.
proof fn lemma_num_rows(b: NumBuild)
    requires built(b),
    ensures represents(b.pv, tables(b.v)),
{
    lemma_num_layout(b);
    let n = nrows(b);
    let rels = tables(b.v);
    let pv = b.pv;
    let start = b.start;
    assert(rels.len() == 1 && rels[0].len() == n);
    assert forall|i: int| 0 <= i < n implies #[trigger] stored_cols_ok(pv, stored_row(pv, rels, i), i) by {
        lemma_stored_cols(b, i);
    }
    assert forall|r: int, i: int| 0 <= r < run_count(pv) && start[r] <= i < start[r + 1]
        implies #[trigger] run_cols_ok(pv, stored_row(pv, rels, i), r) by {
        lemma_run_cols(b, r, i);
    }
    assert forall|j: int| 0 <= j < n implies #[trigger] canon_cols_ok(pv, rels[0][j], j) by {
        lemma_canon_cols(b, j);
    }
}

} // verus!
