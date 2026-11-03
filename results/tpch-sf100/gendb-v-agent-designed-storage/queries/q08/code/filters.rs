//! Binding of the part filter and the nation statuses to the stored parts, and the whole decoded model.
//!
//! - `pf_from`: the part filter's slices are the part table's key and type columns, and `t` / `has_t` locate `$3`
//!   in the type dictionary; `lemma_pa` gives the filter's shape facts (`pf_shape`) and `bind::part_ok`.
//! - `ntab_from`: per nation row its key, whether its region (by key) is named `$2` and whether its name is `$1`;
//!   `lemma_na` gives `bind::nation_ok`.
//! - `lemma_dmodel`: with `decode::cols_from`, the decoded model `bind::dmodel` of every bound database.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::stores::custpart::interface as ci;
use crate::stores::suppliers::interface as si;
use crate::stores::custpart::interface::common::colfmt as cc;
use crate::stores::suppliers::interface::common::colfmt as sc;
use crate::stores::custpart::interface::common::keyidx as ck;
use crate::stores::custpart::declaration as cd;
use crate::stores::suppliers::declaration as sd;
use super::sql::*;
use super::join::{key0, find, lemma_find, join_ok, lemma_keys};
use super::model::*;
use super::kernel::*;
use super::bind::*;
use super::decode::*;

verus! {

// ------------------------------------------------------------------------------------------------ part filter

/// The type dictionary of part.
pub open spec fn tdict_offs(sv: StoresView) -> Seq<u64> {
    cc::u64s(pa_tp(sv)[ci::PA_TYPE_DICT_OFFS as int])
}

pub open spec fn tdict_bytes(sv: StoresView) -> Seq<u8> {
    cc::u8s(pa_tp(sv)[ci::PA_TYPE_DICT_BYTES as int])
}

/// The part filter's slices are the parts' values; `t` is the dictionary entry `$3` (`has_t`), or none is.
pub open spec fn pf_from(sv: StoresView, ps: Seq<Literal>, f: PFilter) -> bool {
    let p = pa_tp(sv);
    let doffs = tdict_offs(sv);
    let dbytes = tdict_bytes(sv);
    &&& f.n_p == cc::u64s(p[ci::PA_LAYOUT as int])[0]
    &&& bs_ok(f.bs_p as int, cc::u64s(p[ci::PA_LAYOUT as int])[1] as int, f.n_p as int)
    &&& f.pk_c@ == cc::u32s(p[ci::PA_PARTKEY_CODES as int]) && f.pk_b@ == cc::i64s(p[ci::PA_PARTKEY_BASE as int])
    &&& f.pt_c@ == cc::u8s(p[ci::PA_TYPE_CODES as int]) && f.pt_b@ == cc::u64s(p[ci::PA_TYPE_BASE as int])
    &&& f.p_kind == cc::u64s(p[ci::PA_KEYIDX_KIND as int])[0]
    &&& f.has_t ==> f.t + 1 < doffs.len() && cc::text_of(doffs, dbytes, f.t as int) == txt(ps[2])
    &&& !f.has_t ==> forall|x: int| 0 <= x < doffs.len() - 1 ==> #[trigger] cc::text_of(doffs, dbytes, x) != txt(ps[2])
    &&& f.e32@ == Seq::<u32>::empty() && f.e64@ == Seq::<u64>::empty()
}

/// The part filter's facts other than its bitmaps.
pub open spec fn pf_shape(f: PFilter) -> bool {
    &&& f.bs_p >= 1
    &&& f.pk_c@.len() == f.n_p && f.pt_c@.len() == f.n_p && f.pt_b@.len() == f.pk_b@.len()
    &&& f.pk_b@.len() * f.bs_p >= f.n_p
    &&& f.e32@ == Seq::<u32>::empty() && f.e64@ == Seq::<u64>::empty()
    &&& ck::keyidx_ok(f.pk_c@, f.pk_b@, Seq::<u32>::empty(), Seq::<u64>::empty(), f.bs_p as int, f.p_kind, f.n_p as int)
    &&& forall|i: int| 0 <= i < f.n_p ==> in_i64(#[trigger] pkey(f, i))
    &&& forall|a: int, b: int| 0 <= a < f.n_p && 0 <= b < f.n_p && a != b ==> #[trigger] pkey(f, a) != #[trigger] pkey(f, b)
}

proof fn lemma_rebs_p(kc: Seq<u32>, kb: Seq<i64>, bs: int, e: int, kind: u64, n: int)
    requires
        ck::keyidx_ok(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), bs, kind, n), bs_ok(e, bs, n), kb.len() * e >= n,
    ensures ck::keyidx_ok(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), e, kind, n),
{
    let (ic, ib) = (Seq::<u32>::empty(), Seq::<u64>::empty());
    assert forall|j: int| 0 <= j < n implies #[trigger] ck::fkey(kc, kb, e, j) == ck::fkey(kc, kb, bs, j) by {
        lemma_bs_div(e, bs, n, j);
    }
    if kind >= 1 {
        assert forall|r: int| 0 <= r < n - 1 implies #[trigger] ck::sorted_at(kc, kb, ic, ib, e, kind, r) by {
            assert(ck::sorted_at(kc, kb, ic, ib, bs, kind, r));
            if kind == 2 {
                assert(ib.len() * bs >= n);
                assert(false) by (nonlinear_arith) requires ib.len() == 0, ib.len() * bs >= n, n >= 2;
            }
        }
    }
}

/// The part rows of a bound database under the filter.
pub proof fn lemma_pa(sv: StoresView, db: Database, ps: Seq<Literal>, f: PFilter)
    requires bound_db(sv, db), pf_from(sv, ps, f),
    ensures pf_shape(f), part_ok(db, ps, f),
{
    let tp = pa_tp(sv);
    let rel = cd::stored_relations(db)[1];
    assert(ci::part_ok(tp, rel));
    let n = rel.len() as int;
    let e = f.bs_p as int;
    let bs = cc::u64s(tp[0])[1] as int;
    let doffs = tdict_offs(sv);
    let dbytes = tdict_bytes(sv);
    let k = doffs.len() - 1;
    assert(cc::dict_col_at(tp, ci::PA_GROUPS as int, ci::PA_TYPE_CODES as int, ci::PA_TYPE_BASE as int,
        ci::PA_TYPE_DICT_OFFS as int, ci::PA_TYPE_DICT_BYTES as int, rel, 4));
    lemma_pbases(tp, n, e);
    let cols = cd::stored_cols_t1();
    crate::link::source::lemma_proj_all_index(db.tables[3], cols);
    lemma_tables_typed(db);
    lemma_keys(db);
    let t = db.tables[3];
    assert forall|i: int| #![trigger t[i]] #![trigger pkey(f, i)] 0 <= i < f.n_p implies t[i][0] == Val::Int(pkey(f, i))
        && (t[i][4] == Val::Text(txt(ps[2]))) == (f.has_t && ptype(f, i) == f.t) && in_i64(pkey(f, i)) by {
        lemma_pfor(tp, n, e, ci::PA_PARTKEY_BASE as int, ci::PA_PARTKEY_CODES as int, i);
        lemma_pfor(tp, n, e, ci::PA_TYPE_BASE as int, ci::PA_TYPE_CODES as int, i);
        assert(rel[i][0] == t[i][0] && rel[i][4] == t[i][4]);
        assert(pa_typed(t[i]));
        let x = ptype(f, i);
        assert(0 <= x < k);
        assert(t[i][4] == Val::Text(cc::text_of(doffs, dbytes, x)));
        if f.has_t && x != f.t {
            cc::lemma_dict_distinct(doffs, dbytes, k, x, f.t as int);
        }
    }
    assert forall|a: int, b: int| 0 <= a < f.n_p && 0 <= b < f.n_p && a != b implies #[trigger] pkey(f, a) != #[trigger] pkey(f, b) by {
        assert(t[a][0] == Val::Int(pkey(f, a)) && t[b][0] == Val::Int(pkey(f, b)));
    }
    lemma_rebs_p(f.pk_c@, f.pk_b@, bs, e, f.p_kind, n);
}

pub proof fn lemma_pfor(tp: Seq<PartView>, n: int, e: int, bp: int, cp: int, j: int)
    requires
        tp.len() >= 2, cc::groups_part_ok(tp[1], n, cc::u64s(tp[0])[1] as int),
        bs_ok(e, cc::u64s(tp[0])[1] as int, n), 0 <= j < n,
    ensures cc::for_at(cc::gs_at(tp, 1), tp[bp], tp[cp], j) == cc::base_at(tp[bp], j / e) + cc::code_at(tp[cp], j),
{
    let bs = cc::u64s(tp[0])[1] as int;
    ci::common::read::lemma_for_row(tp[1], n, bs, tp[bp], tp[cp], j);
    lemma_bs_div(e, bs, n, j);
}

proof fn lemma_pbases(tp: Seq<PartView>, n: int, e: int)
    requires
        tp.len() >= 2, cc::groups_part_ok(tp[1], n, cc::u64s(tp[0])[1] as int),
        bs_ok(e, cc::u64s(tp[0])[1] as int, n),
        crate::gendb_entry::stored::part_len(tp[ci::PA_PARTKEY_BASE as int]) == cc::gs_at(tp, 1).len() - 1,
    ensures crate::gendb_entry::stored::part_len(tp[ci::PA_PARTKEY_BASE as int]) * e >= n,
{
    let bs = cc::u64s(tp[0])[1] as int;
    cc::lemma_uniform_groups(tp[1], n, bs);
    lemma_bs_len(e, bs, n);
}

// ------------------------------------------------------------------------------------------------ nation statuses

pub open spec fn nkey_at(sv: StoresView, i: int) -> int {
    let na = na_tp(sv);
    sc::for_at(sc::gs_at(na, 1), na[si::NA_NATIONKEY_BASE as int], na[si::NA_NATIONKEY_CODES as int], i)
}

pub open spec fn nrkey_at(sv: StoresView, i: int) -> int {
    let na = na_tp(sv);
    sc::for_at(sc::gs_at(na, 1), na[si::NA_REGIONKEY_BASE as int], na[si::NA_REGIONKEY_CODES as int], i)
}

pub open spec fn nname_at(sv: StoresView, i: int) -> Seq<u8> {
    let na = na_tp(sv);
    sc::text_of(sc::u64s(na[si::NA_NAME_OFFS as int]), sc::u8s(na[si::NA_NAME_BYTES as int]), i)
}

pub open spec fn rkey_at(sv: StoresView, r: int) -> int {
    let re = re_tp(sv);
    sc::for_at(sc::gs_at(re, 1), re[si::RE_REGIONKEY_BASE as int], re[si::RE_REGIONKEY_CODES as int], r)
}

pub open spec fn rname_at(sv: StoresView, r: int) -> Seq<u8> {
    let re = re_tp(sv);
    sc::text_of(sc::u64s(re[si::RE_NAME_OFFS as int]), sc::u8s(re[si::RE_NAME_BYTES as int]), r)
}

pub open spec fn n_nat(sv: StoresView) -> int {
    sc::u64s(na_tp(sv)[si::NA_LAYOUT as int])[0] as int
}

pub open spec fn n_reg(sv: StoresView) -> int {
    sc::u64s(re_tp(sv)[si::RE_LAYOUT as int])[0] as int
}

/// Some region row with key `k` is named `b`.
pub open spec fn reg_named(sv: StoresView, k: int, b: Seq<u8>) -> bool {
    exists|r: int| 0 <= r < n_reg(sv) && #[trigger] rkey_at(sv, r) == k && rname_at(sv, r) == b
}

/// The per-row nation statuses are the parts' values.
pub open spec fn ntab_from(sv: StoresView, ps: Seq<Literal>, nt: NTab) -> bool {
    &&& nt.keys@.len() == n_nat(sv) && nt.rreg@.len() == n_nat(sv) && nt.rname@.len() == n_nat(sv)
    &&& forall|i: int| 0 <= i < n_nat(sv) ==> {
        &&& #[trigger] nt.keys@[i] as int == nkey_at(sv, i)
        &&& nt.rname@[i] == (nname_at(sv, i) == txt(ps[0]))
        &&& nt.rreg@[i] == reg_named(sv, nrkey_at(sv, i), txt(ps[1]))
    }
}

/// The nation and region rows of a bound database.
pub proof fn lemma_nr_rows(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        db.tables[6].len() == n_nat(sv), db.tables[7].len() == n_reg(sv),
        forall|i: int| 0 <= i < n_nat(sv) ==> (#[trigger] db.tables[6][i])[0] == Val::Int(nkey_at(sv, i))
            && db.tables[6][i][1] == Val::Text(nname_at(sv, i)) && db.tables[6][i][2] == Val::Int(nrkey_at(sv, i))
            && in_i64(nkey_at(sv, i)) && in_i64(nrkey_at(sv, i)),
        forall|r: int| 0 <= r < n_reg(sv) ==> (#[trigger] db.tables[7][r])[0] == Val::Int(rkey_at(sv, r))
            && db.tables[7][r][1] == Val::Text(rname_at(sv, r)) && in_i64(rkey_at(sv, r)),
        forall|a: int, b: int| 0 <= a < n_nat(sv) && 0 <= b < n_nat(sv) && a != b ==> #[trigger] nkey_at(sv, a) != #[trigger] nkey_at(sv, b),
{
    let rels = sd::stored_relations(db);
    assert(si::nation_ok(na_tp(sv), rels[2]));
    assert(si::region_ok(re_tp(sv), rels[3]));
    crate::link::source::lemma_proj_all_index(db.tables[6], sd::stored_cols_t2());
    crate::link::source::lemma_proj_all_index(db.tables[7], sd::stored_cols_t3());
    lemma_tables_typed(db);
    lemma_keys(db);
    let tn = db.tables[6];
    let tr = db.tables[7];
    assert forall|i: int| 0 <= i < n_nat(sv) implies (#[trigger] tn[i])[0] == Val::Int(nkey_at(sv, i))
        && tn[i][1] == Val::Text(nname_at(sv, i)) && tn[i][2] == Val::Int(nrkey_at(sv, i))
        && in_i64(nkey_at(sv, i)) && in_i64(nrkey_at(sv, i)) by {
        assert(rels[2][i][0] == tn[i][0] && rels[2][i][1] == tn[i][1] && rels[2][i][2] == tn[i][2]);
        assert(na_typed(tn[i]));
    }
    assert forall|r: int| 0 <= r < n_reg(sv) implies (#[trigger] tr[r])[0] == Val::Int(rkey_at(sv, r))
        && tr[r][1] == Val::Text(rname_at(sv, r)) && in_i64(rkey_at(sv, r)) by {
        assert(rels[3][r][0] == tr[r][0] && rels[3][r][1] == tr[r][1]);
        assert(re_typed(tr[r]));
    }
    assert forall|a: int, b: int| 0 <= a < n_nat(sv) && 0 <= b < n_nat(sv) && a != b implies #[trigger] nkey_at(sv, a) != #[trigger] nkey_at(sv, b) by {
        assert(tn[a][0] == Val::Int(nkey_at(sv, a)) && tn[b][0] == Val::Int(nkey_at(sv, b)));
    }
}

/// The nation statuses of a bound database.
pub proof fn lemma_na(sv: StoresView, db: Database, ps: Seq<Literal>, nt: NTab)
    requires bound_db(sv, db), ntab_from(sv, ps, nt),
    ensures nation_ok(db, ps, nt_view(nt)),
{
    lemma_nr_rows(sv, db);
    lemma_keys(db);
    let ns = nt_view(nt);
    let tn = db.tables[6];
    let tr = db.tables[7];
    assert forall|i: int| 0 <= i < ns.keys.len() implies (#[trigger] tn[i])[0] == Val::Int(ns.keys[i] as int)
        && (tn[i][1] == Val::Text(txt(ps[0]))) == ns.name[i]
        && ns.reg[i] == nat_reg(db, ps, tn[i]) by {
        let k = nrkey_at(sv, i);
        assert(nt.keys@[i] as int == nkey_at(sv, i));
        assert(nt.rname@[i] == (nname_at(sv, i) == txt(ps[0])));
        assert(nt.rreg@[i] == reg_named(sv, k, txt(ps[1])));
        assert(tn[i][0] == Val::Int(nkey_at(sv, i)) && tn[i][1] == Val::Text(nname_at(sv, i)) && tn[i][2] == Val::Int(k));
        lemma_find(tr, Val::Int(k));
        if reg_named(sv, k, txt(ps[1])) {
            let r = choose|r: int| 0 <= r < n_reg(sv) && #[trigger] rkey_at(sv, r) == k && rname_at(sv, r) == txt(ps[1]);
            assert(tr[r][0] == Val::Int(k));
            assert(find(tr, Val::Int(k)) == Some(tr[r]));
        } else {
            if let Some(rr) = find(tr, Val::Int(k)) {
                let r = choose|r: int| 0 <= r < tr.len() && (#[trigger] tr[r])[0] == Val::Int(k);
                assert(find(tr, Val::Int(k)) == Some(tr[r]));
                assert(rkey_at(sv, r) == k);
                assert(tr[r][1] != Val::Text(txt(ps[1])));
            }
        }
        assert(ns.reg[i] == nat_reg(db, ps, tn[i]));
    }
    assert forall|a: int, b: int| 0 <= a < ns.keys.len() && 0 <= b < ns.keys.len() && a != b
        implies #[trigger] ns.keys[a] != #[trigger] ns.keys[b] by {
        assert(nkey_at(sv, a) != nkey_at(sv, b));
    }
}

// ------------------------------------------------------------------------------------------------ the whole model

/// Every database bound to the parts has the decoded model of the scan's structures.
pub proof fn lemma_dmodel(sv: StoresView, db: Database, ps: Seq<Literal>, c: Cols, f: PFilter, nt: NTab)
    requires bound_db(sv, db), cols_from(sv, c), pf_from(sv, ps, f), ntab_from(sv, ps, nt),
    ensures
        dmodel(db, ps, c, f, nt_view(nt), lrows_of(sv, db), omap_of(sv, c.n_o as int)),
        lrows_of(sv, db).to_multiset() == crate::link::query::proj_all(db.tables[0],
            crate::stores::factsdir::declaration::stored_cols_t0()).to_multiset(),
        db_ok(db),
{
    lemma_tables_typed(db);
    lemma_keys(db);
    lemma_li(sv, db, c);
    lemma_or(sv, db, c);
    lemma_cu(sv, db, c);
    lemma_su(sv, db, c);
    lemma_pa(sv, db, ps, f);
    lemma_na(sv, db, ps, nt);
}

} // verus!
