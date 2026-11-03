//! What the fast path needs of a bound database, in terms of the views (`Cv`) and the parts of
//! `cust_phoneidx` it reads (the country-code order `p` and its run starts `rs`):
//! - `corder_ok`: `p` is a bijection of the customer rows and every run holds rows of one group (its rows share
//!   `SUBSTRING(c_phone, 1, 2)` with the run's first row, `cust_phoneidx`'s `same_code_at`, and the group is a
//!   function of that code);
//! - `lemma_dense_keys`: with custpart's key index of kind 1 (rows sorted by c_custkey) and the PRIMARY KEY of
//!   customer, the keys strictly increase; when the last key is the first plus `n - 1` they are the first key plus
//!   the row (`common::dense`).
use vstd::prelude::*;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::*;
use crate::spec::constraints::key_of;
use crate::spec::equality::row_not_distinct;
use crate::gendb_constraints::{declared_db, declared_schema};
use crate::link::source::lemma_proj_all_index;
use crate::bridge::constraints::lemma_primary_key_identifies;
use crate::bridge::equality::lemma_row_not_distinct_refl;
use crate::stores::custpart::interface as CP;
use crate::stores::custpart::interface::common::colfmt as CPC;
use crate::stores::custpart::interface::common::keyidx as KI;
use crate::stores::cust_phoneidx::interface as PX;
use super::model::*;
use super::pmodel::*;
use super::sql::*;
use super::bind::*;
use super::common::perm::*;
use super::common::sub2::{sub2, lemma_sub2};
use super::common::dense::{strictly_increasing, lemma_dense};

verus! {

/// Number of runs of the order.
pub open spec fn nruns(rs: Seq<u64>) -> int {
    rs.len() - 1
}

/// The country-code order over the views: a bijection of the rows, cut into runs of one group each.
pub open spec fn corder_ok(v: Cv, p: Seq<u32>, rs: Seq<u64>) -> bool {
    &&& v.n >= 1
    &&& p.len() == v.n
    &&& is_bij(pmap(p), v.n)
    &&& rows_in(v, p, 0, v.n)
    &&& rs.len() >= 2
    &&& rs[0] == 0
    &&& rs[nruns(rs)] == v.n
    &&& forall|t: int| 0 <= t < nruns(rs) ==> #[trigger] rs[t] < rs[t + 1]
    &&& forall|t: int, j: int| 0 <= t < nruns(rs) && #[trigger] PX::in_run(rs, t, j) ==>
            rgid(v, p[j] as int) == rgid(v, p[rs[t] as int] as int)
}

/// The kinds of the parts the fast path requests.
pub open spec fn fast_shape(sv: StoresView) -> bool {
    let (pc, px) = (sv.custpart, sv.cust_phoneidx);
    &&& pc.len() == CP::CUSTPART_PARTS
    &&& pc[20] is U64 && CPC::u64s(pc[20]).len() == 1
    &&& px.len() == PX::PHONEIDX_PARTS
    &&& px[50] is U32 && px[51] is U64
}

/// The shapes, for a bound database.
pub proof fn lemma_fast_shape(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures fast_shape(sv),
{
    let p = sv.custpart;
    let rels = crate::stores::custpart::declaration::stored_relations(db);
    assert(CP::represents(p, rels));
    let tp = p.subrange(CP::CUSTOMER_FIRST as int, (CP::CUSTOMER_FIRST + CP::CU_PARTS) as int);
    assert(CP::customer_ok(tp, rels[0]));
    assert(tp[20] == p[20]);
    let px = sv.cust_phoneidx;
    assert(PX::represents(px, crate::stores::cust_phoneidx::declaration::stored_relations(db)));
}

/// Row `r`'s phone in `cust_phoneidx` is the views' phone.
proof fn lemma_phone(sv: StoresView, db: Database, v: Cv, r: int)
    requires
        bound_db(sv, db),
        rows_match(v, db),
        0 <= r < v.n,
    ensures
        PX::phone_at(sv.cust_phoneidx, r) == rtext(v, r),
{
    let px = sv.cust_phoneidx;
    let rels = crate::stores::cust_phoneidx::declaration::stored_relations(db);
    assert(PX::represents(px, rels));
    lemma_proj_all_index(db.tables[2], crate::stores::cust_phoneidx::declaration::stored_cols_t0());
    assert(rels[0][r] == PX::cu_row(PX::phone_at(px, r)));
    assert(rels[0][r][0] == db.tables[2][r][4]);
    assert(row_match(v, db, r));
}

/// The order's facts, for a bound database (the index is present).
pub proof fn lemma_order(sv: StoresView, db: Database, v: Cv)
    requires
        bound_db(sv, db),
        rows_match(v, db),
        v.n >= 1,
        PX::perm(sv.cust_phoneidx).len() == v.n,
    ensures
        corder_ok(v, PX::perm(sv.cust_phoneidx), PX::runs(sv.cust_phoneidx)),
{
    let px = sv.cust_phoneidx;
    let rels = crate::stores::cust_phoneidx::declaration::stored_relations(db);
    assert(PX::represents(px, rels));
    lemma_proj_all_index(db.tables[2], crate::stores::cust_phoneidx::declaration::stored_cols_t0());
    let n = v.n;
    assert(rels[0].len() == n);
    let (p, rs) = (PX::perm(px), PX::runs(px));
    assert(PX::index_ok(px, n));
    let m = nruns(rs);
    let pm = pmap(p);
    assert forall|j: int| 0 <= j < n implies 0 <= #[trigger] pm[j] < n by {
        assert(p[j] < n);
    }
    assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b implies #[trigger] pm[a] != #[trigger] pm[b] by {
        assert(p[a] != p[b]);
    }
    assert forall|i: int| 0 <= i < n implies #[trigger] covered(pm, i) by {
        assert(PX::listed(p, i));
        let j = choose|j: int| 0 <= j < p.len() && #[trigger] p[j] == i;
        assert(pm[j] == i);
    }
    assert(is_bij(pm, n));
    assert forall|j: int| 0 <= j < n implies #[trigger] p[j] < v.n by {}
    assert forall|t: int, j: int| 0 <= t < m && #[trigger] PX::in_run(rs, t, j) implies
        rgid(v, p[j] as int) == rgid(v, p[rs[t] as int] as int) by {
        assert(PX::same_code_at(px, t, j));
        PX::lemma_runs_mono(rs, m, t + 1, m);
        let (r1, r0) = (p[j] as int, p[rs[t] as int] as int);
        assert(r1 < n && r0 < n);
        lemma_phone(sv, db, v, r1);
        lemma_phone(sv, db, v, r0);
        lemma_sub2(rtext(v, r1));
        lemma_sub2(rtext(v, r0));
    }
}

/// c_custkey of row `r`.
pub open spec fn key_fn(v: Cv) -> spec_fn(int) -> int {
    |r: int| rkey(v, r)
}

/// Rows sorted by key (custpart's key index kind 1) with a PRIMARY KEY: keys strictly increase.
proof fn lemma_keys_increase(sv: StoresView, db: Database, v: Cv)
    requires
        bound_db(sv, db),
        views_of(sv, v),
        rows_match(v, db),
        CPC::u64s(sv.custpart[20])[0] == 1,
    ensures
        strictly_increasing(key_fn(v), v.n),
{
    let p = sv.custpart;
    let rels = crate::stores::custpart::declaration::stored_relations(db);
    assert(CP::represents(p, rels));
    let tp = p.subrange(CP::CUSTOMER_FIRST as int, (CP::CUSTOMER_FIRST + CP::CU_PARTS) as int);
    assert(CP::customer_ok(tp, rels[0]));
    assert(tp[0] == p[0] && tp[2] == p[2] && tp[3] == p[3] && tp[20] == p[20]);
    lemma_proj_all_index(db.tables[2], crate::stores::custpart::declaration::stored_cols_t0());
    let n = v.n;
    assert(rels[0].len() == n);
    let bsz = CPC::u64s(tp[CP::CU_LAYOUT as int])[1] as int;
    let (kc, kb) = (CPC::u32s(tp[2]), CPC::i64s(tp[3]));
    let e = Seq::<u32>::empty();
    let f = Seq::<u64>::empty();
    assert(KI::keyidx_ok(kc, kb, e, f, bsz, 1, n));
    let ddb = declared_db(db);
    crate::gendb_constraints::lemma_declared_schema();
    assert(declared_schema()[2].constraints[0] == (crate::spec::types::Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert(crate::schema::schema_spec().len() == 8) by (compute);
    assert forall|r: int| 0 <= r < n - 1 implies #[trigger] key_fn(v)(r) < key_fn(v)(r + 1) by {
        assert(KI::sorted_at(kc, kb, e, f, bsz, 1, r));
        assert(r / v.bs == r / bsz);
        assert((r + 1) / v.bs == (r + 1) / bsz);
        assert(rkey(v, r) <= rkey(v, r + 1));
        assert(row_match(v, db, r));
        assert(row_match(v, db, r + 1));
        if rkey(v, r) == rkey(v, r + 1) {
            let (a, b) = (ctab(db)[r], ctab(db)[r + 1]);
            assert(a[0] == b[0]);
            assert(key_of(a, seq![0nat]) =~= key_of(b, seq![0nat]));
            lemma_row_not_distinct_refl(key_of(a, seq![0nat]));
            assert(ddb.tables[2] == db.tables[2]);
            lemma_primary_key_identifies(ddb, 2, 0, seq![0nat], true, r, r + 1);
        }
    }
}

/// Dense keys: rows sorted by a PRIMARY KEY whose last value is the first plus `n - 1` have key `first + r`.
pub proof fn lemma_dense_keys(sv: StoresView, db: Database, v: Cv)
    requires
        bound_db(sv, db),
        views_of(sv, v),
        rows_match(v, db),
        v.n >= 1,
        CPC::u64s(sv.custpart[20])[0] == 1,
        rkey(v, v.n - 1) == rkey(v, 0) + v.n - 1,
    ensures
        forall|r: int| 0 <= r < v.n ==> #[trigger] rkey(v, r) == rkey(v, 0) + r,
{
    lemma_keys_increase(sv, db, v);
    lemma_dense(key_fn(v), v.n);
    assert forall|r: int| 0 <= r < v.n implies #[trigger] rkey(v, r) == rkey(v, 0) + r by {
        assert(key_fn(v)(r) == key_fn(v)(0) + r);
    }
}

} // verus!
