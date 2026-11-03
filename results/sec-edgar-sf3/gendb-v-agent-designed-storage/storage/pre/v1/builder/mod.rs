//! Builder of storage `pre`: sorted dictionaries of adsh, stmt, rfile, tag, version and plabel (parallel sorts of row
//! ids by value), a dictionary of distinct (stmt key, rfile code) groups (stmt key 0 for NULL), a (tag, version) pair
//! dictionary, then one parallel sort of the rows by (adsh code, group code, pair code, row) that fixes the stored
//! order. From the sorted keys: the canonical row of each stored row (`orig`), the pair codes, the (adsh, group)
//! sub-runs and the adsh directory; line and plabel (code, validity) gathered into stored order; report, inpth and
//! negating kept in canonical order. Parts in `P_*` order.
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_source::*;
use crate::gendb_entry::parallel::Dispatch;
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::layout::{owned_parts_view, PartView};
use crate::link::query::{text_at, text_wf, TextView};
use crate::spec::value::{Row, Val};
use crate::stores::pre::interface::*;
use crate::stores::pre::interface::common::text::{text_entry, text_parts_wf, text_strictly_sorted, u64_part, u8_part};
use crate::stores::pre::interface::common::cols::{i32_part, text_count, u64s, list_entry, sorted_list_ok, coded_text_at, coded_col_ok};
use crate::stores::pre::interface::common::perm::{is_permutation, lemma_permutation_facts};
use crate::stores::pre::interface::common::runs::*;
pub mod common;
use common::sort::{TextOrder, SortOrder, Key4, KeyOrder, key4_le, sorted_by};
use common::dict::{build_text_dict, emit_text_list, lemma_emitted_sorted, dict_ids_ok, codes_ok, row_in};
use common::keys::{sort_row_keys, rows_of_keys, k2_of_keys, build_pair_dict, key_runs, group_starts, row_keys, key_rows,
    lemma_sorted_keys, runs_ok};
use common::gather::{gather, gather_vec};

verus! {

/// The text order of a delivered text column of `rows` rows.
fn text_order(c: &TextCol, rows: usize) -> (o: TextOrder)
    requires text_wf(c@, rows as int), rows < usize::MAX,
    ensures o.wf(), o.rows == rows, o.text() == c@,
{
    TextOrder { offsets: c.offsets, bytes: c.bytes, rows: rows as u64 }
}

/// A sorted dictionary of a text column: representative rows, per-row codes, and its text parts.
pub struct BuiltDict {
    pub ids: Vec<u64>,
    pub codes: Vec<u64>,
    pub off: Vec<u64>,
    pub bytes: Vec<u8>,
}

/// The facts a dictionary of column `o` gives (NULL rows have no code).
spec fn built_dict_ok(o: TextOrder, valid: Seq<u8>, nullable: bool, d: BuiltDict) -> bool {
    &&& dict_ids_ok(o, d.ids@)
    &&& d.ids@.len() <= o.rows
    &&& d.codes@.len() == o.rows
    &&& forall|i: int| 0 <= i < o.rows && row_in(valid, nullable, i) ==> (#[trigger] d.codes@[i]) < d.ids@.len()
        && o.value(d.ids@[d.codes@[i] as int]) == o.value(i as u64)
    &&& d.off@.len() == d.ids@.len() + 1
    &&& text_parts_wf(d.off@, d.bytes@, d.ids@.len() as int)
    &&& text_strictly_sorted(d.off@, d.bytes@, d.ids@.len() as int)
    &&& forall|k: int| 0 <= k < d.ids@.len() ==> #[trigger] text_entry(d.off@, d.bytes@, k) == o.value(d.ids@[k])
}

/// Dictionary of a text column (of its non-NULL rows when `nullable`).
fn dictionary(o: TextOrder, valid: &'static [u8], nullable: bool, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<BuiltDict, QueryError>)
    requires o.wf(), nullable ==> valid@.len() == o.rows, 1 <= workers <= 64,
    ensures
        r matches Ok(d) ==> built_dict_ok(o, valid@, nullable, d),
        r matches Err(e) ==> e is WorkerFailed,
{
    let d = build_text_dict(o, valid, nullable, workers, dispatch)?;
    let (off, bytes) = emit_text_list(&o, &d.ids);
    proof {
        lemma_emitted_sorted(o, d.ids@, off@, bytes@);
    }
    Ok(BuiltDict { ids: d.ids, codes: d.codes, off, bytes })
}

/// The stmt key of each row: 0 for NULL, else its stmt code + 1.
spec fn stmt_key(valid: Seq<u8>, codes: Seq<u64>, j: int) -> u64 {
    if valid[j] == 0 { 0 } else { (codes[j] + 1) as u64 }
}

/// The stmt keys of all rows.
fn stmt_keys(valid: &'static [u8], codes: &Vec<u64>, count: u64) -> (r: Vec<u64>)
    requires
        valid@.len() == codes@.len(),
        forall|j: int| 0 <= j < codes@.len() && valid@[j] != 0 ==> #[trigger] codes@[j] < count,
    ensures
        r@.len() == codes@.len(),
        forall|j: int| 0 <= j < codes@.len() ==> #[trigger] r@[j] == stmt_key(valid@, codes@, j) && r@[j] <= count,
{
    let n = codes.len();
    let mut r: Vec<u64> = Vec::with_capacity(n);
    let mut j: usize = 0;
    while j < n
        invariant
            n == codes@.len(), valid@.len() == n, j <= n, r@.len() == j,
            forall|t: int| 0 <= t < n && valid@[t] != 0 ==> #[trigger] codes@[t] < count,
            forall|t: int| 0 <= t < j ==> #[trigger] r@[t] == stmt_key(valid@, codes@, t) && r@[t] <= count,
        decreases n - j,
    {
        if valid[j] == 0 {
            r.push(0);
        } else {
            r.push(codes[j] + 1);
        }
        j = j + 1;
    }
    r
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
    let stmt = text_order(&src.t0_f3, n);
    let rfile = text_order(&src.t0_f5, n);
    let tag = text_order(&src.t0_f6, n);
    let version = text_order(&src.t0_f7, n);
    let plabel = text_order(&src.t0_f8, n);
    let adsh_d = dictionary(adsh, src.t0_v3, false, workers, dispatch)?;
    let tag_d = dictionary(tag, src.t0_v3, false, workers, dispatch)?;
    let version_d = dictionary(version, src.t0_v3, false, workers, dispatch)?;
    let rfile_d = dictionary(rfile, src.t0_v3, false, workers, dispatch)?;
    let stmt_d = dictionary(stmt, src.t0_v3, true, workers, dispatch)?;
    let plabel_d = dictionary(plabel, src.t0_v8, true, workers, dispatch)?;
    proof {
        assert forall|j: int| 0 <= j < n implies #[trigger] tag_d.codes@[j] < tag_d.ids@.len()
            && version_d.codes@[j] < version_d.ids@.len() && rfile_d.codes@[j] < rfile_d.ids@.len()
            && adsh_d.codes@[j] < adsh_d.ids@.len() by {
            assert(row_in(src.t0_v3@, false, j));
        }
        assert forall|j: int| 0 <= j < n && src.t0_v3@[j] != 0 implies #[trigger] stmt_d.codes@[j] < stmt_d.ids@.len() by {
            assert(row_in(src.t0_v3@, true, j));
        }
    }
    let stmt_count = stmt_d.ids.len() as u64;
    let keys = stmt_keys(src.t0_v3, &stmt_d.codes, stmt_count);
    let groups = build_pair_dict(&keys, &rfile_d.codes, Ghost(stmt_count + 1), Ghost(rfile_d.ids@.len() as int),
        workers, dispatch)?;
    let pairs = build_pair_dict(&tag_d.codes, &version_d.codes, Ghost(tag_d.ids@.len() as int),
        Ghost(version_d.ids@.len() as int), workers, dispatch)?;
    let s = sort_row_keys(&adsh_d.codes, &groups.codes, &pairs.codes, workers, dispatch)?;
    proof {
        lemma_sorted_keys(s@, adsh_d.codes@, groups.codes@, pairs.codes@);
        lemma_permutation_facts(key_rows(s@), n as nat);
    }
    let orig = rows_of_keys(&s);
    let tv = k2_of_keys(&s);
    let runs = key_runs(&s);
    let adsh_count = adsh_d.ids.len() as u64;
    proof {
        lemma_run_keys_below(s@, runs.start@, runs.k0@, runs.k1@, adsh_d.codes@, groups.codes@, pairs.codes@,
            adsh_d.ids@.len() as int, groups.first@.len() as int);
        assert forall|k: int| 0 <= k < orig@.len() implies #[trigger] orig@[k] < n by {
            assert(key_rows(s@)[k] == s@[k].k3);
        }
    }
    let adsh_subs = group_starts(&runs.k0, adsh_count);
    let line = gather(src.t0_f2, &orig);
    let plabel_codes = gather_vec(&plabel_d.codes, &orig);
    let plabel_valid = gather(src.t0_v8, &orig);
    let report = vstd::slice::slice_to_vec(src.t0_f1);
    let inpth = vstd::slice::slice_to_vec(src.t0_f4);
    let negating = vstd::slice::slice_to_vec(src.t0_f9);
    let ghost views = seq![
        PartView::U64(orig@), PartView::U64(runs.start@), PartView::U64(runs.k0@), PartView::U64(runs.k1@),
        PartView::U64(adsh_subs@),
        PartView::U64(adsh_d.off@), PartView::U8(adsh_d.bytes@),
        PartView::U64(groups.first@), PartView::U64(groups.second@),
        PartView::U64(stmt_d.off@), PartView::U8(stmt_d.bytes@),
        PartView::U64(rfile_d.off@), PartView::U8(rfile_d.bytes@),
        PartView::U64(tv@), PartView::U64(pairs.first@), PartView::U64(pairs.second@),
        PartView::U64(tag_d.off@), PartView::U8(tag_d.bytes@),
        PartView::U64(version_d.off@), PartView::U8(version_d.bytes@),
        PartView::I32(line@),
        PartView::U64(plabel_codes@), PartView::U8(plabel_valid@), PartView::U64(plabel_d.off@), PartView::U8(plabel_d.bytes@),
        PartView::I32(report@), PartView::I32(inpth@), PartView::I32(negating@)
    ];
    let ghost g = (adsh_d, tag_d, version_d, stmt_d, rfile_d, plabel_d);
    let ghost g_groups = (groups.first@, groups.second@, groups.codes@, keys@);
    let ghost g_pairs = (pairs.first@, pairs.second@, pairs.codes@);
    let ghost g_runs = (runs.start@, runs.k0@, runs.k1@);
    let mut parts: Vec<OwnedPart> = Vec::new();
    parts.push(OwnedPart::U64(orig));
    parts.push(OwnedPart::U64(runs.start));
    parts.push(OwnedPart::U64(runs.k0));
    parts.push(OwnedPart::U64(runs.k1));
    parts.push(OwnedPart::U64(adsh_subs));
    parts.push(OwnedPart::U64(adsh_d.off));
    parts.push(OwnedPart::U8(adsh_d.bytes));
    parts.push(OwnedPart::U64(groups.first));
    parts.push(OwnedPart::U64(groups.second));
    parts.push(OwnedPart::U64(stmt_d.off));
    parts.push(OwnedPart::U8(stmt_d.bytes));
    parts.push(OwnedPart::U64(rfile_d.off));
    parts.push(OwnedPart::U8(rfile_d.bytes));
    parts.push(OwnedPart::U64(tv));
    parts.push(OwnedPart::U64(pairs.first));
    parts.push(OwnedPart::U64(pairs.second));
    parts.push(OwnedPart::U64(tag_d.off));
    parts.push(OwnedPart::U8(tag_d.bytes));
    parts.push(OwnedPart::U64(version_d.off));
    parts.push(OwnedPart::U8(version_d.bytes));
    parts.push(OwnedPart::I32(line));
    parts.push(OwnedPart::U64(plabel_codes));
    parts.push(OwnedPart::U8(plabel_valid));
    parts.push(OwnedPart::U64(plabel_d.off));
    parts.push(OwnedPart::U8(plabel_d.bytes));
    parts.push(OwnedPart::I32(report));
    parts.push(OwnedPart::I32(inpth));
    parts.push(OwnedPart::I32(negating));
    proof {
        assert(owned_parts_view(parts@) =~= views);
        let b = PreBuild { v, pv: views, adsh, tag, version, stmt, rfile, plabel,
            da: g.0, dt: g.1, dv: g.2, ds: g.3, dr: g.4, dp: g.5,
            gf: g_groups.0, gs: g_groups.1, gc: g_groups.2, keys: g_groups.3,
            pf: g_pairs.0, ps: g_pairs.1, pc: g_pairs.2, s: s@,
            start: g_runs.0, k0: g_runs.1, k1: g_runs.2 };
        assert(f_orders(b)) by { reveal(f_orders); }
        assert(f_dicts(b)) by { reveal(f_dicts); }
        assert(f_groups(b)) by { reveal(f_groups); }
        assert(f_pairs(b)) by { reveal(f_pairs); }
        assert(f_keys(b)) by { reveal(f_keys); }
        assert(f_runs(b)) by { reveal(f_runs); }
        assert(f_parts(b)) by { reveal(f_parts); }
        assert(f_values(b)) by { reveal(f_values); }
        lemma_pre_rows(b);
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
        lemma_start_le_len(start, k0.len() as int, s.len() as int, r + 1);
        lemma_run_member(s, start, k0, k1, r, i);
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

/// Every row of run `r` has the run's key.
proof fn lemma_run_member(s: Seq<Key4>, start: Seq<u64>, k0: Seq<u64>, k1: Seq<u64>, r: int, i: int)
    requires runs_ok(s, start, k0, k1), 0 <= r < k0.len(), start[r] <= i < start[r + 1],
    ensures s[i].k0 == k0[r] && s[i].k1 == k1[r],
{
}

/// Everything the builder computed, as sequences (ghost).
pub struct PreBuild {
    pub v: SourceView,
    pub pv: Seq<PartView>,
    pub adsh: TextOrder,
    pub tag: TextOrder,
    pub version: TextOrder,
    pub stmt: TextOrder,
    pub rfile: TextOrder,
    pub plabel: TextOrder,
    pub da: BuiltDict,
    pub dt: BuiltDict,
    pub dv: BuiltDict,
    pub ds: BuiltDict,
    pub dr: BuiltDict,
    pub dp: BuiltDict,
    pub gf: Seq<u64>,
    pub gs: Seq<u64>,
    pub gc: Seq<u64>,
    pub keys: Seq<u64>,
    pub pf: Seq<u64>,
    pub ps: Seq<u64>,
    pub pc: Seq<u64>,
    pub s: Seq<Key4>,
    pub start: Seq<u64>,
    pub k0: Seq<u64>,
    pub k1: Seq<u64>,
}

/// Row count of the source.
spec fn nrows(b: PreBuild) -> int {
    source_rows_t0(b.v)
}

/// The text orders read the delivered columns.
#[verifier::opaque]
spec fn f_orders(b: PreBuild) -> bool {
    let n = nrows(b);
    &&& source_wf(b.v)
    &&& b.adsh.text() == b.v.t0_f0 && b.stmt.text() == b.v.t0_f3 && b.rfile.text() == b.v.t0_f5
    &&& b.tag.text() == b.v.t0_f6 && b.version.text() == b.v.t0_f7 && b.plabel.text() == b.v.t0_f8
    &&& b.adsh.rows == n && b.stmt.rows == n && b.rfile.rows == n && b.tag.rows == n && b.version.rows == n && b.plabel.rows == n
    &&& b.adsh.wf() && b.stmt.wf() && b.rfile.wf() && b.tag.wf() && b.version.wf() && b.plabel.wf()
}

/// The six dictionaries.
#[verifier::opaque]
spec fn f_dicts(b: PreBuild) -> bool {
    &&& built_dict_ok(b.adsh, b.v.t0_v3, false, b.da)
    &&& built_dict_ok(b.tag, b.v.t0_v3, false, b.dt)
    &&& built_dict_ok(b.version, b.v.t0_v3, false, b.dv)
    &&& built_dict_ok(b.rfile, b.v.t0_v3, false, b.dr)
    &&& built_dict_ok(b.stmt, b.v.t0_v3, true, b.ds)
    &&& built_dict_ok(b.plabel, b.v.t0_v8, true, b.dp)
}

/// The group dictionary and the rows' group codes.
#[verifier::opaque]
spec fn f_groups(b: PreBuild) -> bool {
    let n = nrows(b);
    &&& b.keys.len() == n
    &&& forall|j: int| 0 <= j < n ==> #[trigger] b.keys[j] == stmt_key(b.v.t0_v3, b.ds.codes@, j)
    &&& pairs_increasing(b.gf, b.gs) && b.gc.len() == n
    &&& forall|j: int| 0 <= j < n ==> (#[trigger] b.gc[j]) < b.gf.len() && b.gf[b.gc[j] as int] == b.keys[j]
        && b.gs[b.gc[j] as int] == b.dr.codes@[j]
    &&& forall|q: int| 0 <= q < b.gf.len() ==> #[trigger] b.gf[q] < b.ds.ids@.len() + 1 && b.gs[q] < b.dr.ids@.len()
}

/// The pair dictionary and the rows' pair codes.
#[verifier::opaque]
spec fn f_pairs(b: PreBuild) -> bool {
    let n = nrows(b);
    &&& pairs_increasing(b.pf, b.ps) && b.pc.len() == n
    &&& forall|j: int| 0 <= j < n ==> (#[trigger] b.pc[j]) < b.pf.len() && b.pf[b.pc[j] as int] == b.dt.codes@[j]
        && b.ps[b.pc[j] as int] == b.dv.codes@[j]
    &&& forall|q: int| 0 <= q < b.pf.len() ==> #[trigger] b.pf[q] < b.dt.ids@.len() && b.ps[q] < b.dv.ids@.len()
}

/// The sorted row keys.
#[verifier::opaque]
spec fn f_keys(b: PreBuild) -> bool {
    let n = nrows(b);
    &&& sorted_by(KeyOrder {}, b.s)
    &&& b.s.len() == n
    &&& is_permutation(key_rows(b.s), n as nat)
    &&& forall|q: int| 0 <= q < b.s.len() ==> (#[trigger] b.s[q]).k3 < n
        && b.s[q] == row_keys(b.da.codes@, b.gc, b.pc)[b.s[q].k3 as int]
}

/// The sub-runs of the sorted keys.
#[verifier::opaque]
spec fn f_runs(b: PreBuild) -> bool {
    runs_ok(b.s, b.start, b.k0, b.k1)
}

/// The parts (except per-row values) as built.
#[verifier::opaque]
spec fn f_parts(b: PreBuild) -> bool {
    let pv = b.pv;
    let n = nrows(b);
    &&& pv.len() == PART_COUNT
    &&& pv[P_ORIG as int] == PartView::U64(key_rows(b.s))
    &&& pv[P_SUB_START as int] == PartView::U64(b.start)
    &&& pv[P_SUB_ADSH as int] == PartView::U64(b.k0)
    &&& pv[P_SUB_GROUP as int] == PartView::U64(b.k1)
    &&& pv[P_ADSH_SUBS as int] is U64 && group_starts_ok(u64_part(pv[P_ADSH_SUBS as int]), b.k0, b.da.ids@.len() as int)
    &&& pv[P_ADSH_OFF as int] == PartView::U64(b.da.off@) && pv[P_ADSH_BYTES as int] == PartView::U8(b.da.bytes@)
    &&& pv[P_GROUP_STMT as int] == PartView::U64(b.gf) && pv[P_GROUP_RFILE as int] == PartView::U64(b.gs)
    &&& pv[P_STMT_OFF as int] == PartView::U64(b.ds.off@) && pv[P_STMT_BYTES as int] == PartView::U8(b.ds.bytes@)
    &&& pv[P_RFILE_OFF as int] == PartView::U64(b.dr.off@) && pv[P_RFILE_BYTES as int] == PartView::U8(b.dr.bytes@)
    &&& pv[P_TV as int] is U64 && u64_part(pv[P_TV as int]).len() == n
    &&& forall|i: int| 0 <= i < n ==> #[trigger] u64_part(pv[P_TV as int])[i] == b.s[i].k2
    &&& pv[P_PAIR_TAG as int] == PartView::U64(b.pf) && pv[P_PAIR_VERSION as int] == PartView::U64(b.ps)
    &&& pv[P_TAG_OFF as int] == PartView::U64(b.dt.off@) && pv[P_TAG_BYTES as int] == PartView::U8(b.dt.bytes@)
    &&& pv[P_VERSION_OFF as int] == PartView::U64(b.dv.off@) && pv[P_VERSION_BYTES as int] == PartView::U8(b.dv.bytes@)
    &&& pv[P_PLABEL_OFF as int] == PartView::U64(b.dp.off@) && pv[P_PLABEL_BYTES as int] == PartView::U8(b.dp.bytes@)
}

/// The per-row columns in stored order and the canonical columns as built.
#[verifier::opaque]
spec fn f_values(b: PreBuild) -> bool {
    let pv = b.pv;
    let n = nrows(b);
    let v = b.v;
    let orig = key_rows(b.s);
    &&& pv.len() == PART_COUNT
    &&& pv[P_LINE as int] is I32 && i32_part(pv[P_LINE as int]).len() == n
    &&& forall|i: int| 0 <= i < n ==> #[trigger] i32_part(pv[P_LINE as int])[i] == v.t0_f2[orig[i] as int]
    &&& pv[P_PLABEL_CODES as int] is U64 && u64_part(pv[P_PLABEL_CODES as int]).len() == n
    &&& forall|i: int| 0 <= i < n ==> #[trigger] u64_part(pv[P_PLABEL_CODES as int])[i] == b.dp.codes@[orig[i] as int]
    &&& pv[P_PLABEL_VALID as int] is U8 && u8_part(pv[P_PLABEL_VALID as int]).len() == n
    &&& forall|i: int| 0 <= i < n ==> #[trigger] u8_part(pv[P_PLABEL_VALID as int])[i] == v.t0_v8[orig[i] as int]
    &&& pv[P_REPORT as int] == PartView::I32(v.t0_f1)
    &&& pv[P_INPTH as int] == PartView::I32(v.t0_f4)
    &&& pv[P_NEGATING as int] == PartView::I32(v.t0_f9)
}

/// All the builder facts.
spec fn built(b: PreBuild) -> bool {
    f_orders(b) && f_dicts(b) && f_groups(b) && f_pairs(b) && f_keys(b) && f_runs(b) && f_parts(b) && f_values(b)
}

/// Layout facts: part count, types, sizes.
proof fn lemma_layout_shape(b: PreBuild)
    requires built(b),
    ensures
        b.pv.len() == PART_COUNT,
        b.pv[P_ORIG as int] is U64 && b.pv[P_SUB_START as int] is U64 && b.pv[P_SUB_ADSH as int] is U64,
        b.pv[P_SUB_GROUP as int] is U64 && b.pv[P_ADSH_SUBS as int] is U64,
        b.pv[P_GROUP_STMT as int] is U64 && b.pv[P_GROUP_RFILE as int] is U64,
        b.pv[P_TV as int] is U64 && b.pv[P_PAIR_TAG as int] is U64 && b.pv[P_PAIR_VERSION as int] is U64,
        b.pv[P_LINE as int] is I32 && b.pv[P_REPORT as int] is I32 && b.pv[P_INPTH as int] is I32,
        b.pv[P_NEGATING as int] is I32,
        row_count(b.pv) == nrows(b),
        sub_count(b.pv) == b.k0.len(),
        b.k1.len() == b.k0.len(),
        u64s(b.pv, P_SUB_START) == b.start,
        u64s(b.pv, P_SUB_ADSH) == b.k0,
        u64s(b.pv, P_SUB_GROUP) == b.k1,
        adsh_count(b.pv) == b.da.ids@.len(),
        stmt_count(b.pv) == b.ds.ids@.len(), rfile_count(b.pv) == b.dr.ids@.len(),
        tag_count(b.pv) == b.dt.ids@.len(), version_count(b.pv) == b.dv.ids@.len(),
        group_count(b.pv) == b.gf.len(),
        pair_count(b.pv) == b.pf.len(),
        u64s(b.pv, P_GROUP_STMT) == b.gf, u64s(b.pv, P_GROUP_RFILE) == b.gs,
        u64s(b.pv, P_PAIR_TAG) == b.pf, u64s(b.pv, P_PAIR_VERSION) == b.ps,
{
    reveal(f_parts);
    reveal(f_values);
    reveal(f_keys);
    reveal(f_dicts);
    reveal(f_groups);
    reveal(f_pairs);
    reveal(f_runs);
}

/// Layout facts: the permutation, sub-runs and adsh directory.
proof fn lemma_layout_runs(b: PreBuild)
    requires built(b),
    ensures
        is_permutation(u64s(b.pv, P_ORIG), row_count(b.pv) as nat),
        runs_partition_ok(b.start, b.k0.len() as int, nrows(b)),
        pairs_increasing(b.k0, b.k1),
        forall|r: int| 0 <= r < b.k0.len() ==> #[trigger] b.k0[r] < b.da.ids@.len() && b.k1[r] < b.gf.len(),
        group_starts_ok(u64s(b.pv, P_ADSH_SUBS), b.k0, b.da.ids@.len() as int),
{
    lemma_layout_shape(b);
    reveal(f_parts);
    reveal(f_keys);
    reveal(f_runs);
    reveal(f_dicts);
    reveal(f_groups);
    reveal(f_orders);
    reveal(f_pairs);
    assert(b.s.len() == nrows(b));
    assert forall|j: int| 0 <= j < b.da.codes@.len() implies #[trigger] b.da.codes@[j] < b.da.ids@.len()
        && b.gc[j] < b.gf.len() by {
        reveal(f_orders);
        assert(row_in(b.v.t0_v3, false, j));
    }
    lemma_run_keys_below(b.s, b.start, b.k0, b.k1, b.da.codes@, b.gc, b.pc, b.da.ids@.len() as int, b.gf.len() as int);
}

/// Layout facts: dictionaries, group and pair lists and pair codes.
proof fn lemma_layout_dicts(b: PreBuild)
    requires built(b),
    ensures
        sorted_list_ok(b.pv, P_ADSH_OFF), sorted_list_ok(b.pv, P_STMT_OFF), sorted_list_ok(b.pv, P_RFILE_OFF),
        sorted_list_ok(b.pv, P_TAG_OFF), sorted_list_ok(b.pv, P_VERSION_OFF),
        pairs_increasing(b.gf, b.gs),
        forall|g: int| 0 <= g < b.gf.len() ==> #[trigger] b.gf[g] <= b.ds.ids@.len() && b.gs[g] < b.dr.ids@.len(),
        u64s(b.pv, P_TV).len() == nrows(b),
        forall|i: int| 0 <= i < nrows(b) ==> #[trigger] u64s(b.pv, P_TV)[i] < b.pf.len(),
        pairs_increasing(b.pf, b.ps),
        forall|p: int| 0 <= p < b.pf.len() ==> #[trigger] b.pf[p] < b.dt.ids@.len() && b.ps[p] < b.dv.ids@.len(),
{
    reveal(f_parts);
    reveal(f_dicts);
    reveal(f_groups);
    reveal(f_pairs);
    reveal(f_orders);
    let n = nrows(b);
    let tv = u64_part(b.pv[P_TV as int]);
    assert forall|i: int| 0 <= i < n implies #[trigger] tv[i] < b.pf.len() by {
        reveal(f_keys);
        assert(b.s[i] == row_keys(b.da.codes@, b.gc, b.pc)[b.s[i].k3 as int]);
    }
}

/// Layout facts: pair codes never decrease inside a sub-run.
proof fn lemma_layout_tv_order(b: PreBuild)
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

/// The plabel column gathered into stored order satisfies `coded_col_ok`, with the column's values.
proof fn lemma_plabel(b: PreBuild)
    requires built(b),
    ensures
        coded_col_ok(b.pv, P_PLABEL_CODES, P_PLABEL_VALID as int, P_PLABEL_OFF, nrows(b)),
        forall|i: int| 0 <= i < nrows(b) ==> #[trigger] coded_text_at(b.pv, P_PLABEL_CODES, P_PLABEL_VALID as int, P_PLABEL_OFF, i)
            == crate::gendb_source::or_null(b.v.t0_v8[key_rows(b.s)[i] as int], Val::Text(b.plabel.value(key_rows(b.s)[i]))),
{
    reveal(f_values);
    reveal(f_orders);
    reveal(f_dicts);
    reveal(f_parts);
    reveal(f_keys);
    let n = nrows(b);
    let pv = b.pv;
    let orig = key_rows(b.s);
    let d = b.dp;
    let (pc, pvalid, po) = (P_PLABEL_CODES, P_PLABEL_VALID as int, P_PLABEL_OFF);
    assert(text_count(pv, po as int) == d.ids@.len());
    assert forall|i: int| 0 <= i < n implies #[trigger] orig[i] < n by {
        assert(orig[i] == b.s[i].k3);
    }
    assert forall|i: int| 0 <= i < n && !(pvalid >= 0 && u8_part(pv[pvalid])[i] == 0)
        implies #[trigger] u64s(pv, pc)[i] < text_count(pv, po as int) by {
        let j = orig[i] as int;
        assert(row_in(b.v.t0_v8, true, j));
    }
    assert forall|i: int| 0 <= i < n implies #[trigger] coded_text_at(pv, pc, pvalid, po, i)
        == crate::gendb_source::or_null(b.v.t0_v8[orig[i] as int], Val::Text(b.plabel.value(orig[i]))) by {
        let j = orig[i] as int;
        if row_in(b.v.t0_v8, true, j) {
            assert(d.codes@[j] < d.ids@.len());
            assert(list_entry(pv, po, d.codes@[j] as int) == text_entry(d.off@, d.bytes@, d.codes@[j] as int));
        }
    }
}

/// Layout facts: per-row values and canonical columns.
proof fn lemma_layout_values(b: PreBuild)
    requires built(b),
    ensures
        i32_part(b.pv[P_LINE as int]).len() == nrows(b),
        coded_col_ok(b.pv, P_PLABEL_CODES, P_PLABEL_VALID as int, P_PLABEL_OFF, nrows(b)),
        i32_part(b.pv[P_REPORT as int]).len() == nrows(b),
        i32_part(b.pv[P_INPTH as int]).len() == nrows(b),
        i32_part(b.pv[P_NEGATING as int]).len() == nrows(b),
{
    lemma_plabel(b);
    reveal(f_values);
    reveal(f_orders);
}

/// The assembled parts satisfy the layout facts.
proof fn lemma_pre_layout(b: PreBuild)
    requires built(b),
    ensures
        pre_layout_ok(b.pv),
        row_count(b.pv) == nrows(b),
        sub_count(b.pv) == b.k0.len(),
        u64s(b.pv, P_SUB_START) == b.start,
{
    lemma_layout_shape(b);
    lemma_layout_runs(b);
    lemma_layout_dicts(b);
    lemma_layout_tv_order(b);
    lemma_layout_values(b);
}

/// Columns held per stored row.
proof fn lemma_stored_cols(b: PreBuild, i: int)
    requires built(b), 0 <= i < nrows(b),
    ensures stored_cols_ok(b.pv, stored_row(b.pv, tables(b.v), i), i),
{
    lemma_plabel(b);
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
    assert(s[i] == row_keys(b.da.codes@, b.gc, b.pc)[j]);
    let t = table_t0(b.v);
    assert(stored_row(pv, tables(b.v), i) == t[j]);
    assert(u64_part(pv[P_TV as int])[i] == b.pc[j]);
    assert(row_in(b.v.t0_v3, false, j));
    assert(tag_of(pv, i) == text_entry(b.dt.off@, b.dt.bytes@, b.dt.codes@[j] as int));
    assert(tag_of(pv, i) == b.tag.value(j as u64));
    assert(version_of(pv, i) == text_entry(b.dv.off@, b.dv.bytes@, b.dv.codes@[j] as int));
    assert(version_of(pv, i) == b.version.value(j as u64));
}

/// Columns held per sub-run.
proof fn lemma_sub_cols(b: PreBuild, r: int, i: int)
    requires built(b), 0 <= r < b.k0.len(), b.start[r] <= i < b.start[r + 1],
    ensures sub_cols_ok(b.pv, stored_row(b.pv, tables(b.v), i), r),
{
    reveal(f_parts);
    reveal(f_keys);
    reveal(f_runs);
    reveal(f_dicts);
    reveal(f_groups);
    reveal(f_orders);
    let s = b.s;
    let pv = b.pv;
    lemma_start_le_len(b.start, b.k0.len() as int, s.len() as int, r + 1);
    lemma_run_member(s, b.start, b.k0, b.k1, r, i);
    let j = s[i].k3 as int;
    assert(key_rows(s)[i] == s[i].k3);
    assert(s[i] == row_keys(b.da.codes@, b.gc, b.pc)[j]);
    let t = table_t0(b.v);
    assert(stored_row(pv, tables(b.v), i) == t[j]);
    assert(row_in(b.v.t0_v3, false, j));
    assert(sub_adsh_of(pv, r) == text_entry(b.da.off@, b.da.bytes@, b.da.codes@[j] as int));
    assert(sub_adsh_of(pv, r) == b.adsh.value(j as u64));
    let g = b.k1[r] as int;
    assert(g == b.gc[j]);
    assert(b.gf[g] == stmt_key(b.v.t0_v3, b.ds.codes@, j));
    assert(group_rfile_of(pv, g) == text_entry(b.dr.off@, b.dr.bytes@, b.dr.codes@[j] as int));
    assert(group_rfile_of(pv, g) == b.rfile.value(j as u64));
    if b.v.t0_v3[j] != 0 {
        assert(row_in(b.v.t0_v3, true, j));
        assert(b.ds.codes@[j] < b.ds.ids@.len());
        assert(group_stmt_of(pv, g) == Val::Text(text_entry(b.ds.off@, b.ds.bytes@, b.ds.codes@[j] as int)));
        assert(group_stmt_of(pv, g) == Val::Text(b.stmt.value(j as u64)));
    }
}

/// Columns held in canonical row order.
proof fn lemma_canon_cols(b: PreBuild, j: int)
    requires built(b), 0 <= j < nrows(b),
    ensures canon_cols_ok(b.pv, tables(b.v)[0][j], j),
{
    reveal(f_values);
    reveal(f_orders);
}

/// Every fact of `represents`.
proof fn lemma_pre_rows(b: PreBuild)
    requires built(b),
    ensures represents(b.pv, tables(b.v)),
{
    lemma_pre_layout(b);
    let n = nrows(b);
    let rels = tables(b.v);
    let pv = b.pv;
    let start = b.start;
    assert(rels.len() == 1 && rels[0].len() == n);
    assert forall|i: int| 0 <= i < n implies #[trigger] stored_cols_ok(pv, stored_row(pv, rels, i), i) by {
        lemma_stored_cols(b, i);
    }
    assert forall|r: int, i: int| 0 <= r < sub_count(pv) && start[r] <= i < start[r + 1]
        implies #[trigger] sub_cols_ok(pv, stored_row(pv, rels, i), r) by {
        lemma_sub_cols(b, r, i);
    }
    assert forall|j: int| 0 <= j < n implies #[trigger] canon_cols_ok(pv, rels[0][j], j) by {
        lemma_canon_cols(b, j);
    }
}

} // verus!
