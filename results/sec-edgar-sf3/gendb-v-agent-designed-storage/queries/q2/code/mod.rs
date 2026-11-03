// AUTHOR MODULE ROOT (crate::agent). You own every file under src/agent/.
//! Entry of the query: the top 100 (value DESC, name, tag) of the `num` rows of unit `$1` that hold the MAX value
//! of their (adsh, tag) group, with the name of their filing in `sub` when its fiscal year is `$2`.
//!
//! Plan. Storage `num_vord` is `num` (clustered in runs of equal (uom, adsh), rows of one tag adjacent in a run)
//! plus `vorder`, every unit's rows by value descending. The unit `$1` is one dictionary lookup, one run range and
//! one row range; one thread walks the unit's rows in value order (`walk`), keeps the candidates in a top-100
//! buffer and stops once no later row can enter it. No other thread: the walk visits a few hundred rows.
//! Proof chain: `sem` (the SQL body's bag is `body_count`), `vstored` (the candidates of the unit's positions in
//! value order have that bag), `walk` (the buffer is a top-100 split of them), `common::topk` (the final slice is
//! an allowed ORDER BY / LIMIT output).
use vstd::prelude::*;
pub mod common;
pub mod sem;
pub mod stored;
pub mod vstored;
pub mod kernel;
pub mod walk;

use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::order::*;
use crate::exec::value::{EVal, view_row};
use crate::link::query::view_rows;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db, outcome_ok};
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::work::filled;
use crate::gendb_params::Params;
use crate::query::{param_domain, query_spec_at};
use crate::gendb_entry::layout::PartView;
use crate::stores::num_vord::interface as numi;
use crate::stores::sub::interface as subi;
use crate::stores::num_vord::interface::common::text::{text_entry, text_entry_of, find_in_stored_dict, u64_part, u8_part};
use crate::stores::num_vord::interface::common::cols::{i32_part, i128_part};
use kernel::*;
use stored::*;
use vstored::*;
use walk::*;
use sem::*;
use common::topk::*;

verus! {

/// A copy of a byte slice.
fn copy_bytes(s: &[u8]) -> (v: Vec<u8>)
    ensures v@ == s@,
{
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant i <= s@.len(), v@ == s@.subrange(0, i as int),
        decreases s@.len() - i,
    {
        v.push(s[i]);
        i = i + 1;
        proof { assert(v@ =~= s@.subrange(0, i as int)); }
    }
    proof { assert(s@.subrange(0, s@.len() as int) =~= s@); }
    v
}

/// The whole `u64` part `p` (one extent request).
fn whole_u64(st: &mut crate::gendb_entry::stored::StoredParts, p: usize) -> (r: &'static [u64])
    requires p < old(st)@.len(), old(st)@[p as int] is U64,
    ensures final(st)@ == old(st)@, r@ == u64_part(old(st)@[p as int]),
{
    let n = st.part_len(p);
    let r = st.extent_u64(p, 0, n);
    proof { assert(r@ =~= u64_part(old(st)@[p as int])); }
    r
}

/// The whole `u8` part `p`.
fn whole_u8(st: &mut crate::gendb_entry::stored::StoredParts, p: usize) -> (r: &'static [u8])
    requires p < old(st)@.len(), old(st)@[p as int] is U8,
    ensures final(st)@ == old(st)@, r@ == u8_part(old(st)@[p as int]),
{
    let n = st.part_len(p);
    let r = st.extent_u8(p, 0, n);
    proof { assert(r@ =~= u8_part(old(st)@[p as int])); }
    r
}

/// The whole `i32` part `p`.
fn whole_i32(st: &mut crate::gendb_entry::stored::StoredParts, p: usize) -> (r: &'static [i32])
    requires p < old(st)@.len(), old(st)@[p as int] is I32,
    ensures final(st)@ == old(st)@, r@ == i32_part(old(st)@[p as int]),
{
    let n = st.part_len(p);
    let r = st.extent_i32(p, 0, n);
    proof { assert(r@ =~= i32_part(old(st)@[p as int])); }
    r
}

/// The whole `i128` part `p`.
fn whole_i128(st: &mut crate::gendb_entry::stored::StoredParts, p: usize) -> (r: &'static [i128])
    requires p < old(st)@.len(), old(st)@[p as int] is I128,
    ensures final(st)@ == old(st)@, r@ == i128_part(old(st)@[p as int]),
{
    let n = st.part_len(p);
    let r = st.extent_i128(p, 0, n);
    proof { assert(r@ =~= i128_part(old(st)@[p as int])); }
    r
}

/// Entries `u` and `u + 1` of the `u64` part `p`.
fn two_u64(st: &mut crate::gendb_entry::stored::StoredParts, p: usize, u: usize) -> (r: (u64, u64))
    requires p < old(st)@.len(), old(st)@[p as int] is U64, u + 2 <= u64_part(old(st)@[p as int]).len(),
    ensures final(st)@ == old(st)@, r.0 == u64_part(old(st)@[p as int])[u as int], r.1 == u64_part(old(st)@[p as int])[u + 1],
{
    let n = st.part_len(p);
    let e = st.extent_u64(p, u, u + 2);
    (e[0], e[1])
}

/// A top-100 split of a bag with the body's multiplicities answers the statement.
proof fn lemma_answer(db: Database, ps: Seq<Literal>, c: Seq<Row>, t: Seq<Row>, rest: Seq<Row>)
    requires
        shapes_ok(db), param_domain(ps),
        topk_ok(qkeys(), qfams(), TOPK as nat, c, t, rest),
        forall|x: Row| #[trigger] c.to_multiset().count(x) == body_count(db.tables[1], db.tables[0], uom_of(ps), fy_of(ps), x),
    ensures ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(t)),
{
    lemma_body(db, ps);
    let oq = query_spec_at(ps);
    let body = denote_body(db, oq)->Ok_0;
    assert(c.to_multiset() =~= body.to_multiset());
    lemma_topk_final(qkeys(), qfams(), TOPK as nat, c, t, rest);
    let p = t + sort_rows(qkeys(), rest);
    assert(oq.keys =~= qkeys());
    assert(oq.offset == 0 && oq.limit == Some(100nat));
    crate::link::outcome::lemma_outcome_sorted(db, oq, body, p);
}

/// The slices the walk reads, for unit code `uc`.
fn read_input(stores: &mut Stores, params: &Params, uc: usize) -> (w: WalkInput)
    requires
        kfacts(old(stores).num_vord@, old(stores).sub@),
        param_domain(params@),
        uc < numi::uom_count(old(stores).num_vord@),
        numi::dict_entry(old(stores).num_vord@, numi::P_UOM_OFF, uc as int) == params.p0@,
    ensures
        final(stores)@ == old(stores)@,
        win_ok(w),
        w.np@ == old(stores).num_vord@, w.sp@ == old(stores).sub@, w.u@ == params.p0@, w.p1 == params.p1,
        w.uc@ == uc as int,
{
    let ghost np = stores.num_vord@;
    let ghost sp = stores.sub@;
    proof {
        lemma_kf_parts(np, sp);
        lemma_kf_lens(np, sp);
        lemma_kf_uom(np, sp, uc as int);
        lemma_kf_sub(np, sp);
        lemma_kf_vorder(np, sp, uc as int);
    }
    let nruns = stores.num_vord.part_len(numi::P_RUN_ADSH);
    let (r0u, r1u) = two_u64(&mut stores.num_vord, numi::P_UOM_RUNS, uc);
    proof { assert(r0u <= r1u <= nruns); }
    let r0 = r0u as usize;
    let r1 = r1u as usize;
    let run_start = whole_u64(&mut stores.num_vord, numi::P_RUN_START);
    let nrows = stores.num_vord.part_len(numi::P_TV);
    proof {
        lemma_kf_unit_bounds(np, sp, uc as int);
        assert(run_start@[r0 as int] <= nrows && run_start@[r1 as int] <= nrows);
    }
    let lo = run_start[r0] as usize;
    let hi = run_start[r1] as usize;
    let w = WalkInput {
        p1: params.p1,
        fy: whole_i32(&mut stores.sub, subi::P_FY),
        fy_valid: whole_u8(&mut stores.sub, subi::P_FY_VALID),
        sub_adsh_off: whole_u64(&mut stores.sub, subi::P_ADSH_OFF),
        sub_adsh_bytes: whole_u8(&mut stores.sub, subi::P_ADSH_BYTES),
        sub_rows: stores.sub.part_len(subi::P_CIK),
        name_codes: whole_u64(&mut stores.sub, subi::P_NAME_CODES),
        adsh_order: whole_u64(&mut stores.sub, subi::P_ADSH_ORDER),
        adsh_off: whole_u64(&mut stores.num_vord, numi::P_ADSH_OFF),
        adsh_bytes: whole_u8(&mut stores.num_vord, numi::P_ADSH_BYTES),
        adsh_count: stores.num_vord.part_len(numi::P_ADSH_OFF) - 1,
        run_adsh: whole_u64(&mut stores.num_vord, numi::P_RUN_ADSH),
        run_start,
        tv: whole_u64(&mut stores.num_vord, numi::P_TV),
        pair_tag: whole_u64(&mut stores.num_vord, numi::P_PAIR_TAG),
        value: whole_i128(&mut stores.num_vord, numi::P_VALUE),
        vorder: whole_u64(&mut stores.num_vord, numi::P_VORDER),
        nrows,
        r0, r1, lo, hi,
        uc: Ghost(uc as int),
        np: Ghost(np), sp: Ghost(sp), u: Ghost(params.p0@),
    };
    proof {
        assert(kfacts(np, sp));
        assert(w.fy@ == i32_part(sp[subi::P_FY as int]));
        assert(w.sub_rows == subi::row_count(sp));
        assert(w.adsh_count == numi::adsh_count(np));
        assert(w.run_start@ == n_start(np));
        assert(w.value@ == n_value(np));
        assert(w.vorder@ == vord(np));
        assert(w.r0 == numi::u64s(np, numi::P_UOM_RUNS)[uc as int]);
        assert(w.r1 == numi::u64s(np, numi::P_UOM_RUNS)[uc + 1]);
        assert(w.lo == numi::unit_row(np, uc as int));
        assert(w.hi == numi::unit_row(np, uc + 1));
        assert(win_ok(w));
    }
    w
}

/// The answer rows of the buffer: name and tag bytes from their dictionaries, the value at scale 4.
fn answer_rows(stores: &mut Stores, cands: &Vec<Cand>, len: usize) -> (rows: Vec<Vec<EVal>>)
    requires
        kfacts(old(stores).num_vord@, old(stores).sub@),
        buf_ok(old(stores).num_vord@, old(stores).sub@, cands@, len as int),
    ensures
        final(stores)@ == old(stores)@,
        view_rows(rows@) == tview(old(stores).num_vord@, old(stores).sub@, cands@, len as int),
{
    let ghost np = stores.num_vord@;
    let ghost sp = stores.sub@;
    proof { lemma_kf_parts(np, sp); }
    let names = stores.sub.part_len(subi::P_NAME_DICT_OFF) - 1;
    let name_off = whole_u64(&mut stores.sub, subi::P_NAME_DICT_OFF);
    let name_bytes = whole_u8(&mut stores.sub, subi::P_NAME_DICT_BYTES);
    let tags = stores.num_vord.part_len(numi::P_TAG_OFF) - 1;
    let tag_off = whole_u64(&mut stores.num_vord, numi::P_TAG_OFF);
    let tag_bytes = whole_u8(&mut stores.num_vord, numi::P_TAG_BYTES);
    let ghost tt = tview(np, sp, cands@, len as int);
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            buf_ok(np, sp, cands@, len as int),
            tt == tview(np, sp, cands@, len as int),
            rows@.len() == i,
            forall|k: int| 0 <= k < i ==> view_row((#[trigger] rows@[k])@) == tt[k],
            name_off@ == u64_part(sp[subi::P_NAME_DICT_OFF as int]),
            name_bytes@ == u8_part(sp[subi::P_NAME_DICT_BYTES as int]),
            names == name_count(sp),
            tag_off@ == u64_part(np[numi::P_TAG_OFF as int]),
            tag_bytes@ == u8_part(np[numi::P_TAG_BYTES as int]),
            tags == numi::tag_count(np),
            crate::stores::num_vord::interface::common::text::text_parts_wf(name_off@, name_bytes@, names as int),
            crate::stores::num_vord::interface::common::text::text_parts_wf(tag_off@, tag_bytes@, tags as int),
        decreases len - i,
    {
        let c = cands[i];
        let (nm, _) = text_entry_of(name_off, name_bytes, names, c.name as usize);
        let (tg, _) = text_entry_of(tag_off, tag_bytes, tags, c.tag as usize);
        let mut row: Vec<EVal> = Vec::new();
        row.push(EVal::Text(copy_bytes(nm)));
        row.push(EVal::Text(copy_bytes(tg)));
        row.push(EVal::Num { coeff: c.value, scale: 4 });
        proof {
            assert(view_row(row@) =~= cview(np, sp, c));
        }
        rows.push(row);
        i = i + 1;
    }
    proof {
        assert(view_rows(rows@) =~= tt);
    }
    rows
}

pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    let ghost np = stores.num_vord@;
    let ghost sp = stores.sub@;
    let ghost ps = params@;
    let ghost u = params.p0@;
    let ghost y = params.p1 as int;
    proof {
        let db0 = choose|db: Database| bound_db(sv, db);
        lemma_bound_kfacts(sv, db0);
        lemma_kf_parts(np, sp);
        lemma_kf_dicts(np, sp);
        assert(uom_of(ps) == u && fy_of(ps) == y);
    }
    let uom_count = stores.num_vord.part_len(numi::P_UOM_OFF) - 1;
    let found = find_in_stored_dict(&mut stores.num_vord, numi::P_UOM_OFF, numi::P_UOM_BYTES, uom_count, params.p0);
    let mut cands: Vec<Cand> = filled(TOPK, Cand { value: 0, name: 0, tag: 0 });
    let (len, Ghost(all), Ghost(grest)) = match found {
        None => {
            proof {
                lemma_topk_empty(qkeys(), qfams(), TOPK as nat);
                assert(tview(np, sp, cands@, 0) =~= Seq::<Row>::empty());
            }
            (0, Ghost(Seq::<Row>::empty()), Ghost(Seq::<Row>::empty()))
        },
        Some(uc) => {
            let w = read_input(stores, params, uc);
            let (len, Ghost(rest)) = w.walk(&mut cands);
            (len, Ghost(v_emits(np, sp, u, y, numi::unit_row(np, uc as int), numi::unit_row(np, uc + 1))), Ghost(rest))
        },
    };
    let rows = answer_rows(stores, &cands, len);
    proof {
        let t = tview(np, sp, cands@, len as int);
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok(Answer::Rows(rows))) by {
            lemma_bound_parts(sv, db);
            lemma_rels(np, sp, db);
            assert forall|x: Row| #[trigger] all.to_multiset().count(x) == body_count(db.tables[1], db.tables[0], uom_of(ps), fy_of(ps), x) by {
                match found {
                    None => {
                        lemma_no_unit_count(np, sp, db, u, y, x);
                    },
                    Some(uc) => {
                        lemma_v_count(np, sp, db, u, y, x, uc as int);
                    },
                }
            }
            lemma_answer(db, ps, all, t, grest);
        }
    }
    Ok(Answer::Rows(rows))
}

} // verus!
