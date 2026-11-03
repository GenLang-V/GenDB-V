//! Query: per (tag, version), the count and value sum of the `num` rows of uom `$1` with ddate in `[$2, $3]` that
//! have no `pre` row with the same (adsh, tag, version); groups with count > 10, largest 100 counts.
//!
//! Plan (storages `num` clustered by (uom, adsh, tag, version) and `pre` clustered by (adsh, group, tag, version)):
//! 1. the uom code of `$1` (binary search of the uom dictionary) gives the num runs `[r0, r1)` of that uom;
//! 2. code maps pre tag -> num tag and pre version -> num version (merges of the sorted dictionaries), then
//!    pre pair -> num pair (linear step / galloping search in the sorted num pair list), in parallel, kept as one
//!    chunk per task (`common::dictmap`, `pairmap`, `chunks`);
//! 3. the runs are scanned in parallel (`scan`, tasks balanced by the rows of zone-map-passing runs): per run (one
//!    filing) the images of its pre rows are set in a per-task bit set, then the rows with ddate in range whose pair
//!    code is not set are emitted as (pair code, value), and the bits are cleared;
//! 4. the entries are grouped by pair code (`common::groupby`), the groups with count > 10 sorted by count and the
//!    first 100 output (`answer::select_cands`).
//! Proof: `answer::lemma_answer` (from `model`, `stored`, `acc`) for every database bound to the parts. When the
//! absolute value sum of some group exceeds `i128::MAX` the answer is `Capacity` (`capacity`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::stored::StoredParts;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::{Answer, stores_ready, answer_meets, bound_db, outcome_ok};
use crate::gendb_params::Params;
use crate::query::{param_domain, query_spec_at};
use crate::exec::value::{EVal, view_row};
use crate::link::query::view_rows;
use crate::stores::num_tvg::interface as N;
use crate::stores::pre::interface as P;
use crate::stores::num_tvg::interface::common::text::{find_text, text_entry_of, lemma_dict_codes};

pub mod common;
pub mod model;
pub mod scan;
pub mod stored;
pub mod acc;
pub mod answer;
pub mod parts;
pub mod capacity;

use common::dictmap::{Dict, dict_map3, map_ok};
use common::pairmap::{Pairs, pair_map, pair_map32};
use common::chunks::{chunks_shape, chunks_seq};
use common::groupby::{Group, group_by};
use scan::{ScanInput, scan_runs, npm_view, npm_shape_ok};
use stored::{inp_matches, lemma_inp_wf, lemma_npm_ok, lemma_ndict_at, npm_ok, ndict_is, pdict_is, ntag_str, nver_str};
use answer::{answer_premises, cand_row, lemma_answer, lemma_cands_bounds, select_cands};
use parts::{read_u64, read_u32, read_i32, read_i128, num_dict, pre_dict, len_bound, len_bound_u64};
use model::{ukey, dlo, dhi};

verus! {

/// The num runs of uom `key`: `[r0, r1)`, empty when no stored uom equals `key`.
fn uom_range(st: &mut StoredParts, key: &'static [u8]) -> (r: (usize, usize))
    requires N::num_layout_ok(old(st)@),
    ensures
        final(st)@ == old(st)@,
        r.0 <= r.1 <= N::run_count(old(st)@),
        forall|q: int| 0 <= q < N::run_count(old(st)@) ==> (#[trigger] N::run_uom_of(old(st)@, q) == key@) == (r.0 <= q < r.1),
{
    let ghost np = st@;
    let nuom = num_dict(st, N::P_UOM_OFF);
    let uom_runs = read_u64(st, N::P_UOM_RUNS);
    let nruns = st.part_len(N::P_RUN_UOM);
    let key_len = key.len();
    let found = find_text(nuom.off, nuom.bytes, nuom.count, key, key_len);
    let r = match found {
        Some(u) => {
            proof {
                N::lemma_uom_runs(np, u as int);
                assert(uom_runs@[u + 1] <= nruns);
            }
            (uom_runs[u] as usize, uom_runs[u + 1] as usize)
        },
        None => (0usize, 0usize),
    };
    proof {
        assert forall|q: int| 0 <= q < N::run_count(np) implies (#[trigger] N::run_uom_of(np, q) == key@) == (r.0 <= q < r.1) by {
            let ur = N::u64s(np, N::P_RUN_UOM)[q] as int;
            assert(ur < nuom.count);
            lemma_ndict_at(nuom, np, N::P_UOM_OFF, ur);
            match found {
                Some(u) => {
                    lemma_dict_codes(nuom.off@, nuom.bytes@, nuom.count as int, ur, u as int);
                },
                None => {},
            }
        }
    }
    r
}

/// The adsh dictionaries of num and pre.
fn adsh_dicts(stn: &mut StoredParts, stp: &mut StoredParts) -> (r: (Dict, Dict))
    requires N::num_layout_ok(old(stn)@), P::pre_layout_ok(old(stp)@),
    ensures
        final(stn)@ == old(stn)@, final(stp)@ == old(stp)@,
        ndict_is(r.0, old(stn)@, N::P_ADSH_OFF), pdict_is(r.1, old(stp)@, P::P_ADSH_OFF), r.0.wf(), r.1.wf(),
{
    (num_dict(stn, N::P_ADSH_OFF), pre_dict(stp, P::P_ADSH_OFF))
}

/// Pre's pair list is strictly increasing in the terms of `pair_map` (the same definition in num_tvg's interface).
proof fn lemma_pre_pairs_increasing(pp: Seq<PartView>)
    requires P::pre_layout_ok(pp),
    ensures crate::stores::num_tvg::interface::common::runs::pairs_increasing(
        P::common::cols::u64s(pp, P::P_PAIR_TAG), P::common::cols::u64s(pp, P::P_PAIR_VERSION)),
{
    let a = P::common::cols::u64s(pp, P::P_PAIR_TAG);
    let b = P::common::cols::u64s(pp, P::P_PAIR_VERSION);
    assert(crate::stores::pre::interface::common::runs::pairs_increasing(a, b));
    assert forall|i: int, j: int| 0 <= i < j < a.len() implies
        crate::stores::num_tvg::interface::common::runs::pair_lt(#[trigger] a[i], b[i], #[trigger] a[j], b[j]) by {
        assert(crate::stores::pre::interface::common::runs::pair_lt(a[i], b[i], a[j], b[j]));
    }
}

/// The num pair -> pre pair map in its representation (`scan::npm_view`): one `u32` vector when `use32`, else
/// chunks of `size = 1 << shift` codes.
pub struct NpmRep {
    pub use32: bool,
    pub v32: Vec<u32>,
    pub cs: Vec<Vec<u64>>,
    pub shift: u64,
    pub size: u64,
}

/// The num adsh -> pre adsh map and the num pair -> pre pair map (`npm_ok`): the tag, version and adsh dictionary
/// maps in one parallel phase, then the pair map (`u32` entries when pre has fewer than `u32::MAX` pairs).
fn maps(stn: &mut StoredParts, stp: &mut StoredParts, nadsh: Dict, padsh: Dict, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<(Vec<u64>, NpmRep), QueryError>)
    requires
        N::num_layout_ok(old(stn)@), P::pre_layout_ok(old(stp)@), 1 <= workers <= MAX_WORKERS,
        nadsh.wf(), padsh.wf(),
    ensures
        final(stn)@ == old(stn)@, final(stp)@ == old(stp)@,
        r matches Ok((amap, m)) ==> map_ok(nadsh, padsh, amap@)
            && npm_shape_ok(m.use32, m.v32@, m.cs@, m.shift, m.size, N::pair_count(old(stn)@) as int)
            && npm_ok(old(stn)@, old(stp)@, npm_view(m.use32, m.v32@, m.cs@, m.size as int, N::pair_count(old(stn)@) as int)),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ghost np = stn@;
    let ghost pp = stp@;
    let ntag = num_dict(stn, N::P_TAG_OFF);
    let nver = num_dict(stn, N::P_VERSION_OFF);
    let npt = read_u64(stn, N::P_PAIR_TAG);
    let npv = read_u64(stn, N::P_PAIR_VERSION);
    let ptag = pre_dict(stp, P::P_TAG_OFF);
    let pver = pre_dict(stp, P::P_VERSION_OFF);
    let ppt = read_u64(stp, P::P_PAIR_TAG);
    let ppv = read_u64(stp, P::P_PAIR_VERSION);
    let (tm, vm, amap) = match dict_map3(ntag, ptag, nver, pver, nadsh, padsh, workers, dispatch) {
        Ok(m) => m,
        Err(e) => return Err(e),
    };
    let src = Pairs { first: npt, second: npv, count: len_bound_u64(npt) };
    let dst = Pairs { first: ppt, second: ppv, count: ppt.len() };
    let ghost tmv = tm@;
    let ghost vmv = vm@;
    proof {
        lemma_pre_pairs_increasing(pp);
        assert forall|p: int| 0 <= p < src.count implies (#[trigger] src.first@[p]) < tmv.len() && src.second@[p] < vmv.len() by {
            assert(N::u64s(np, N::P_PAIR_TAG)[p] < N::tag_count(np));
        }
    }
    if dst.count < 0xffff_ffff {
        let v32 = match pair_map32(src, dst, Arc::new(tm), Arc::new(vm), workers, dispatch) {
            Ok(m) => m,
            Err(e) => return Err(e),
        };
        let m = NpmRep { use32: true, v32, cs: Vec::new(), shift: 12, size: 4096 };
        proof {
            let v = npm_view(true, m.v32@, m.cs@, 4096, src.count as int);
            assert forall|p: int| 0 <= p < src.count implies
                common::pairmap::pair_entry_ok(src, dst, tmv, vmv, p, #[trigger] v[p]) by {
                assert(v[p] == m.v32@[p] as u64);
            }
            lemma_npm_ok(np, pp, ntag, nver, ptag, pver, tmv, vmv, src, dst, v);
        }
        return Ok((amap, m));
    }
    let (cs, shift, size) = match pair_map(src, dst, Arc::new(tm), Arc::new(vm), workers, dispatch) {
        Ok(m) => m,
        Err(e) => return Err(e),
    };
    let m = NpmRep { use32: false, v32: Vec::new(), cs, shift, size };
    proof {
        let v = chunks_seq(m.cs@, size as int, src.count as int);
        assert forall|p: int| 0 <= p < src.count implies
            common::pairmap::pair_entry_ok(src, dst, tmv, vmv, p, #[trigger] v[p]) by {
            assert(v[p] == common::chunks::chunk_at(m.cs@, size as int, p));
        }
        lemma_npm_ok(np, pp, ntag, nver, ptag, pver, tmv, vmv, src, dst, v);
        assert(npm_view(false, m.v32@, m.cs@, size as int, src.count as int) == v);
    }
    Ok((amap, m))
}

/// The scan's inputs: the stored parts, the parameters and the maps.
fn scan_input(stn: &mut StoredParts, stp: &mut StoredParts, nadsh: Dict, padsh: Dict, amap: Vec<u64>,
    m: NpmRep, params: &Params) -> (inp: ScanInput)
    requires
        N::num_layout_ok(old(stn)@), P::pre_layout_ok(old(stp)@),
        ndict_is(nadsh, old(stn)@, N::P_ADSH_OFF), pdict_is(padsh, old(stp)@, P::P_ADSH_OFF),
        nadsh.wf(), padsh.wf(),
        map_ok(nadsh, padsh, amap@),
        npm_shape_ok(m.use32, m.v32@, m.cs@, m.shift, m.size, N::pair_count(old(stn)@) as int),
        npm_ok(old(stn)@, old(stp)@, npm_view(m.use32, m.v32@, m.cs@, m.size as int, N::pair_count(old(stn)@) as int)),
        param_domain(params@),
    ensures
        final(stn)@ == old(stn)@, final(stp)@ == old(stp)@,
        inp_matches(inp, old(stn)@, old(stp)@, params@), inp.wf(), inp.n <= 0x7fff_ffff_ffff_ffff,
        inp.runs == N::run_count(old(stn)@),
{
    let ghost np = stn@;
    let ghost pp = stp@;
    let run_start = read_u64(stn, N::P_RUN_START);
    let run_adsh = read_u64(stn, N::P_RUN_ADSH);
    let run_dmin = read_i32(stn, N::P_RUN_DDATE_MIN);
    let run_dmax = read_i32(stn, N::P_RUN_DDATE_MAX);
    let tv = read_u64(stn, N::P_TV);
    let ddate = read_i32(stn, N::P_DDATE);
    let value = read_i128(stn, N::P_VALUE);
    let npairs = len_bound_u64(read_u64(stn, N::P_PAIR_TAG));
    let run_groups = read_u64(stn, N::P_RUN_GROUPS);
    let group_start = read_u32(stn, N::P_GROUP_START);
    let group_key = read_u32(stn, N::P_GROUP_KEY);
    let adsh_subs = read_u64(stp, P::P_ADSH_SUBS);
    let sub_start = read_u64(stp, P::P_SUB_START);
    let ptv = read_u64(stp, P::P_TV);
    let subs = stp.part_len(P::P_SUB_ADSH);
    let ppairs = len_bound_u64(read_u64(stp, P::P_PAIR_TAG));
    let n = len_bound(value);
    let nruns = run_adsh.len();
    let pn = ptv.len();
    let has_index = run_groups.len() == run_start.len();
    let ngroups = group_key.len();
    let nadsh_n = nadsh.count;
    let inp = ScanInput {
        run_start, run_adsh, run_dmin, run_dmax, tv, ddate, value, nadsh, padsh, adsh_subs, sub_start, ptv,
        amap: Arc::new(amap), use32: m.use32, npm32: Arc::new(m.v32), npm: Arc::new(m.cs), npm_shift: m.shift,
        npm_size: m.size,
        run_groups, group_start, group_key, has_index, ngroups,
        n, runs: nruns, pn, subs, npairs, ppairs, nadsh_n,
        dlo: params.p1 as i32, dhi: params.p2 as i32,
    };
    proof {
        assert(params@[1] == (Literal::Int { v: params.p1 as int, kind: crate::spec::int::IntKind::Int4 }));
        assert(inp.dlo == dlo(params@) && inp.dhi == dhi(params@));
        lemma_inp_wf(inp, np, pp, params@);
    }
    inp
}

/// The output row of candidate `c`: tag and version bytes, count, sum (scale 4).
fn cand_out(ntag: Dict, nver: Dict, npt: &'static [u64], npv: &'static [u64], c: Group) -> (row: Vec<EVal>)
    requires
        ntag.wf(), nver.wf(), c.key < npt@.len(), npt@.len() == npv@.len(),
        npt@[c.key as int] < ntag.count, npv@[c.key as int] < nver.count,
        c.count <= 0x7fff_ffff_ffff_ffff,
    ensures view_row(row@) == seq![Val::Text(ntag.at(npt@[c.key as int] as int)), Val::Text(nver.at(npv@[c.key as int] as int)),
        Val::Int(c.count as int), Val::Num { coeff: c.sum as int, scale: 4 }],
{
    let n = npt.len();
    let p = c.key as usize;
    let (tb, _tn) = text_entry_of(ntag.off, ntag.bytes, ntag.count, npt[p] as usize);
    let (vb, _vn) = text_entry_of(nver.off, nver.bytes, nver.count, npv[p] as usize);
    let mut row: Vec<EVal> = Vec::new();
    row.push(EVal::Text(vstd::slice::slice_to_vec(tb)));
    row.push(EVal::Text(vstd::slice::slice_to_vec(vb)));
    row.push(EVal::Int(c.count as i64));
    row.push(EVal::Num { coeff: c.sum, scale: 4 });
    proof {
        assert(view_row(row@) =~= seq![Val::Text(ntag.at(npt@[c.key as int] as int)), Val::Text(nver.at(npv@[c.key as int] as int)),
            Val::Int(c.count as int), Val::Num { coeff: c.sum as int, scale: 4 }]);
    }
    row
}

/// The output rows of the first `min(100, |cs|)` candidates.
fn output_rows(stn: &mut StoredParts, cs: &Vec<Group>) -> (rows: Vec<Vec<EVal>>)
    requires
        N::num_layout_ok(old(stn)@),
        forall|c: int| 0 <= c < cs@.len() ==> (#[trigger] cs@[c]).key < N::pair_count(old(stn)@)
            && cs@[c].count <= 0x7fff_ffff_ffff_ffff,
    ensures
        final(stn)@ == old(stn)@,
        rows@.len() == if cs@.len() < 100 { cs@.len() } else { 100 },
        forall|j: int| 0 <= j < rows@.len() ==> view_row((#[trigger] rows@[j])@) == cand_row(old(stn)@, cs@[j]),
{
    let ghost np = stn@;
    let ntag = num_dict(stn, N::P_TAG_OFF);
    let nver = num_dict(stn, N::P_VERSION_OFF);
    let npt = read_u64(stn, N::P_PAIR_TAG);
    let npv = read_u64(stn, N::P_PAIR_VERSION);
    let lim = if cs.len() < 100 { cs.len() } else { 100 };
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let mut i: usize = 0;
    while i < lim
        invariant
            N::num_layout_ok(np), stored::ndict_is(ntag, np, N::P_TAG_OFF), stored::ndict_is(nver, np, N::P_VERSION_OFF),
            ntag.wf(), nver.wf(), npt@ == N::u64s(np, N::P_PAIR_TAG), npv@ == N::u64s(np, N::P_PAIR_VERSION),
            forall|c: int| 0 <= c < cs@.len() ==> (#[trigger] cs@[c]).key < N::pair_count(np)
                && cs@[c].count <= 0x7fff_ffff_ffff_ffff,
            i <= lim <= cs@.len(), lim == if cs@.len() < 100 { cs@.len() } else { 100 },
            rows@.len() == i,
            forall|j: int| 0 <= j < i ==> view_row((#[trigger] rows@[j])@) == cand_row(np, cs@[j]),
        decreases lim - i,
    {
        let c = cs[i];
        proof {
            assert(c.key < N::pair_count(np));
            assert(npt@[c.key as int] < N::tag_count(np) && npv@[c.key as int] < N::version_count(np));
            lemma_ndict_at(ntag, np, N::P_TAG_OFF, npt@[c.key as int] as int);
            lemma_ndict_at(nver, np, N::P_VERSION_OFF, npv@[c.key as int] as int);
        }
        let row = cand_out(ntag, nver, npt, npv, c);
        rows.push(row);
        i = i + 1;
    }
    rows
}

proof fn lemma_groups_sorted(es: Seq<common::groupby::Entry>, gs: Seq<Group>)
    requires common::groupby::groups_ok(es, gs),
    ensures forall|a: int, b: int| 0 <= a < b < gs.len() ==> #[trigger] gs[a].key < #[trigger] gs[b].key,
{
}

/// Some database is bound to the parts: the layouts hold.
proof fn lemma_layouts(sv: crate::gendb_entry::stores::StoresView)
    requires stores_ready(sv),
    ensures N::num_layout_ok(sv.num_tvg), P::pre_layout_ok(sv.pre),
{
    let db0 = choose|db: Database| bound_db(sv, db);
    assert(bound_db(sv, db0));
}

/// The rows answer the statement for every database bound to the parts.
proof fn lemma_final(sv: crate::gendb_entry::stores::StoresView, ps: Seq<Literal>, iv: ScanInput, r0: int, r1: int,
    es: Seq<common::groupby::Entry>, gs: Seq<Group>, cs: Seq<Group>, rows: Vec<Vec<EVal>>)
    requires
        param_domain(ps),
        answer_premises(sv.num_tvg, sv.pre, iv, ps, r0, r1, es, gs, cs),
        rows@.len() == if cs.len() < 100 { cs.len() } else { 100 },
        forall|j: int| 0 <= j < rows@.len() ==> view_row((#[trigger] rows@[j])@) == cand_row(sv.num_tvg, cs[j]),
    ensures answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Rows(rows))),
{
    let out = view_rows(rows@);
    assert forall|i: int| 0 <= i < out.len() implies #[trigger] out[i] == cand_row(sv.num_tvg, cs[i]) by {
        assert(out[i] == view_row(rows@[i]@));
    }
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
        lemma_answer(db, sv.num_tvg, sv.pre, iv, ps, r0, r1, es, gs, cs, out);
    }
}

/// The capacity answer for every database bound to the parts.
proof fn lemma_capacity_final(sv: crate::gendb_entry::stores::StoresView, ps: Seq<Literal>, iv: ScanInput, r0: int, r1: int,
    es: Seq<common::groupby::Entry>, p: u64)
    requires
        param_domain(ps),
        stored::inp_matches(iv, sv.num_tvg, sv.pre, ps), iv.wf(),
        N::num_layout_ok(sv.num_tvg), P::pre_layout_ok(sv.pre),
        0 <= r0 <= r1 <= iv.runs,
        forall|r: int| 0 <= r < iv.runs ==> (#[trigger] N::run_uom_of(sv.num_tvg, r) == ukey(ps)) == (r0 <= r < r1),
        es == iv.run_ents(r0, r1),
        iv.n <= 0x7fff_ffff_ffff_ffff,
        common::groupby::pabs(es, p) > i128::MAX,
    ensures answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Capacity)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity)) by {
        answer::lemma_capacity_answer(db, sv.num_tvg, sv.pre, iv, ps, r0, r1, es, p);
    }
}

pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures answer_meets(old(stores)@, params@, r),
{
    hide(common::groupby::groups_ok);
    hide(stored::inp_matches);
    hide(ScanInput::wf);
    hide(ScanInput::run_ents);
    hide(N::num_layout_ok);
    hide(P::pre_layout_ok);
    hide(stored::npm_ok);
    hide(bound_db);
    let ghost sv = stores@;
    let ghost ps = params@;
    proof {
        lemma_layouts(sv);
    }
    let ghost np = sv.num_tvg;
    let ghost pp = sv.pre;
    let (r0, r1) = uom_range(&mut stores.num_tvg, params.p0);
    let (nadsh, padsh) = adsh_dicts(&mut stores.num_tvg, &mut stores.pre);
    let (amap, npm) = match maps(&mut stores.num_tvg, &mut stores.pre, nadsh, padsh, workers, dispatch) {
        Ok(m) => m,
        Err(e) => return Err(e),
    };
    let inp = scan_input(&mut stores.num_tvg, &mut stores.pre, nadsh, padsh, amap, npm, params);
    let ghost iv = inp;
    proof {
        assert(ps[0] == Literal::Text(params.p0@));
    }
    let es = match scan_runs(Arc::new(inp), r0, r1, workers, dispatch) {
        Ok(es) => es,
        Err(e) => return Err(e),
    };
    let ghost esv = es@;
    let gs = match group_by(es) {
        Ok(gs) => gs,
        Err(p) => {
            proof {
                lemma_capacity_final(sv, ps, iv, r0 as int, r1 as int, esv, p);
            }
            return Ok(Answer::Capacity);
        },
    };
    proof {
        lemma_groups_sorted(esv, gs@);
    }
    let cs = select_cands(&gs);
    proof {
        lemma_cands_bounds(np, pp, iv, ps, r0 as int, r1 as int, esv, gs@, cs@);
    }
    let rows = output_rows(&mut stores.num_tvg, &cs);
    proof {
        lemma_final(sv, ps, iv, r0 as int, r1 as int, esv, gs@, cs@, rows);
    }
    Ok(Answer::Rows(rows))
}

} // verus!
