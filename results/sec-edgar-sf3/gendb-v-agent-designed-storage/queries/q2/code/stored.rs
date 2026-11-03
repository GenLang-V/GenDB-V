//! The query over the stored layouts. `num` is stored clustered by (uom, adsh, tag, version) in runs of equal
//! (uom, adsh) (`stores::num_vord::interface`); `sub` is stored in canonical order with `adsh_order`, its rows
//! sorted by adsh. Views of the parts (`n_start`, `n_value`, `tagc`, `fy_ok`, `seg_max`, `cand_row`), the database
//! bound to both storages (`parts_bound`, with the declared constraints), and the facts that relate stored rows to
//! the SQL rows: columns of a stored row (`lemma_srow`), runs and groups (`lemma_same_group`, `lemma_qual_seg`),
//! sums over stored positions (`lemma_stored_sum`), sub rows (`lemma_sub_row`) and sub's primary key (`lemma_sub_pk`).
use vstd::prelude::*;
use vstd::multiset::Multiset;
use crate::spec::value::*;
use crate::spec::typing::db_wf;
use crate::schema::schema_spec;
use crate::link::join::*;
use crate::link::query::{proj, proj_all};
use crate::link::expr::ival;
use crate::gendb_entry::layout::PartView;
use crate::stores::num_vord::interface as numi;
use crate::stores::sub::interface as subi;
use crate::stores::num_vord::declaration as numd;
use crate::stores::sub::declaration as subd;
use crate::stores::num_vord::interface::common::text::{text_entry, u64_part, u8_part, lemma_dict_codes};
use crate::stores::num_vord::interface::common::cols::{i32_part, i128_part};
use crate::stores::num_vord::interface::common::runs::*;
use crate::stores::num_vord::interface::common::perm::*;
use crate::agent::sem::*;
use crate::agent::common::rel::*;

verus! {

broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms, vstd::seq_lib::lemma_multiset_commutative};

// ------------------------------------------------------------------ views of the parts

pub open spec fn n_start(np: Seq<PartView>) -> Seq<u64> {
    numi::u64s(np, numi::P_RUN_START)
}

pub open spec fn n_value(np: Seq<PartView>) -> Seq<i128> {
    i128_part(np[numi::P_VALUE as int])
}

/// Tag code of stored row `i` (dictionary position of its tag).
pub open spec fn tagc(np: Seq<PartView>, i: int) -> int {
    numi::u64s(np, numi::P_PAIR_TAG)[numi::u64s(np, numi::P_TV)[i] as int] as int
}

pub open spec fn s_order(sp: Seq<PartView>) -> Seq<u64> {
    subi::adsh_order(sp)
}

/// Sub row `j` has fiscal year `y` (not NULL).
pub open spec fn fy_ok(sp: Seq<PartView>, y: int, j: int) -> bool {
    u8_part(sp[subi::P_FY_VALID as int])[j] != 0 && i32_part(sp[subi::P_FY as int])[j] as int == y
}

pub open spec fn name_code(sp: Seq<PartView>, j: int) -> int {
    u64_part(sp[subi::P_NAME_CODES as int])[j] as int
}

pub open spec fn name_text(sp: Seq<PartView>, code: int) -> Seq<u8> {
    crate::stores::sub::interface::common::text::text_entry(
        crate::stores::sub::interface::common::text::u64_part(sp[subi::P_NAME_DICT_OFF as int]),
        crate::stores::sub::interface::common::text::u8_part(sp[subi::P_NAME_DICT_BYTES as int]), code)
}

pub open spec fn tag_text(np: Seq<PartView>, code: int) -> Seq<u8> {
    numi::dict_entry(np, numi::P_TAG_OFF, code)
}

/// Run `r` holds the rows of unit `u` and filing `a`.
pub open spec fn is_key_run(np: Seq<PartView>, u: Seq<u8>, a: Seq<u8>, r: int) -> bool {
    0 <= r < numi::run_count(np) && numi::run_uom_of(np, r) == u && numi::run_adsh_of(np, r) == a
}

/// Stored row `i` of run `r` holds the largest value among the rows of run `r` with its tag.
pub open spec fn seg_max(np: Seq<PartView>, r: int, i: int) -> bool {
    forall|i2: int| n_start(np)[r] <= i2 < n_start(np)[r + 1] && #[trigger] tagc(np, i2) == tagc(np, i)
        ==> n_value(np)[i2] <= n_value(np)[i]
}

/// The output row of name code `nc`, tag code `tc` and value coefficient `v`.
pub open spec fn out_of(np: Seq<PartView>, sp: Seq<PartView>, nc: int, tc: int, v: int) -> Row {
    seq![Val::Text(name_text(sp, nc)), Val::Text(tag_text(np, tc)), Val::Num { coeff: v, scale: 4 }]
}

/// The output row of sub row `j` and stored num row `i`.
pub open spec fn cand_row(np: Seq<PartView>, sp: Seq<PartView>, j: int, i: int) -> Row {
    out_of(np, sp, name_code(sp, j), tagc(np, i), n_value(np)[i] as int)
}

/// `db` is bound to both storages.
#[verifier::opaque]
pub open spec fn parts_bound(np: Seq<PartView>, sp: Seq<PartView>, db: Database) -> bool {
    &&& db.schema == schema_spec()
    &&& db_wf(db)
    &&& numi::represents(np, numd::stored_relations(db))
    &&& subi::represents(sp, subd::stored_relations(db))
    &&& crate::spec::constraints::constraints_hold(crate::gendb_constraints::declared_db(db))
}

// ------------------------------------------------------------------ the stored relations are the tables

/// `num`'s stored relation is table 1 and `sub`'s is table 0 (every column is stored), and their rows have the
/// shapes `sem` needs.
pub proof fn lemma_rels(np: Seq<PartView>, sp: Seq<PartView>, db: Database)
    requires parts_bound(np, sp, db),
    ensures
        numd::stored_relations(db)[0] == db.tables[1],
        subd::stored_relations(db)[0] == db.tables[0],
        shapes_ok(db),
{
    reveal(parts_bound);
    numd::lemma_declared_schema();
    subd::lemma_declared_schema();
    let (nums, subs) = (db.tables[1], db.tables[0]);
    let nc = numd::stored_cols_t0();
    let sc = subd::stored_cols_t0();
    assert forall|k: int| 0 <= k < 9 implies #[trigger] nc[k] == k by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else if k == 4 {} else if k == 5 {}
        else if k == 6 {} else if k == 7 {} else {}
    }
    assert forall|k: int| 0 <= k < 20 implies #[trigger] sc[k] == k by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else if k == 4 {} else if k == 5 {}
        else if k == 6 {} else if k == 7 {} else if k == 8 {} else if k == 9 {} else if k == 10 {} else if k == 11 {}
        else if k == 12 {} else if k == 13 {} else if k == 14 {} else if k == 15 {} else if k == 16 {} else if k == 17 {}
        else if k == 18 {} else {}
    }
    assert(nc.len() == 9 && sc.len() == 20);
    assert forall|j: int| 0 <= j < nums.len() implies #[trigger] proj(nums[j], nc) == nums[j] by {
        assert(crate::spec::typing::row_in_table(db.tables[1][j], db.schema[1]));
        assert(proj(nums[j], nc) =~= nums[j]);
    }
    assert forall|j: int| 0 <= j < subs.len() implies #[trigger] proj(subs[j], sc) == subs[j] by {
        assert(crate::spec::typing::row_in_table(db.tables[0][j], db.schema[0]));
        assert(proj(subs[j], sc) =~= subs[j]);
    }
    assert(proj_all(nums, nc) =~= nums);
    assert(proj_all(subs, sc) =~= subs);
    // Shapes of num rows, from the run each row is stored in.
    let rels = numd::stored_relations(db);
    let orig = numi::u64s(np, numi::P_ORIG);
    let n = numi::row_count(np);
    lemma_permutation_facts(orig, n as nat);
    assert forall|j: int| 0 <= j < nums.len() implies num_shape(#[trigger] nums[j]) by {
        let i = position_of(orig, j);
        lemma_run_of(n_start(np), numi::run_count(np), n, i);
        let r = run_of(n_start(np), numi::run_count(np), i);
        assert(numi::stored_row(np, rels, i) == nums[j]);
        assert(numi::stored_cols_ok(np, numi::stored_row(np, rels, i), i));
        assert(numi::run_cols_ok(np, numi::stored_row(np, rels, i), r));
    }
    assert forall|j: int| 0 <= j < subs.len() implies sub_shape(#[trigger] subs[j]) by {
        assert(subi::sub_row_ok(sp, subd::stored_relations(db)[0][j], j));
    }
}

/// Canonical row of stored position `i`.
pub open spec fn srow(np: Seq<PartView>, db: Database, i: int) -> Row {
    db.tables[1][numi::u64s(np, numi::P_ORIG)[i] as int]
}

/// The columns of stored row `i` of run `r`.
pub proof fn lemma_srow(np: Seq<PartView>, sp: Seq<PartView>, db: Database, r: int, i: int)
    requires parts_bound(np, sp, db), 0 <= r < numi::run_count(np), n_start(np)[r] <= i < n_start(np)[r + 1],
    ensures
        srow(np, db, i)[0] == Val::Text(numi::run_adsh_of(np, r)),
        srow(np, db, i)[5] == Val::Text(numi::run_uom_of(np, r)),
        srow(np, db, i)[1] == Val::Text(numi::tag_of(np, i)),
        srow(np, db, i)[7] == (Val::Num { coeff: n_value(np)[i] as int, scale: 4 }),
        numi::tag_of(np, i) == tag_text(np, tagc(np, i)),
        0 <= i < numi::row_count(np),
        0 <= numi::u64s(np, numi::P_ORIG)[i] < db.tables[1].len(),
{
    reveal(parts_bound);
    lemma_rels(np, sp, db);
    let rels = numd::stored_relations(db);
    let n = numi::row_count(np);
    assert(n_start(np)[0] <= n_start(np)[r]);
    assert(n_start(np)[r + 1] <= n_start(np)[numi::run_count(np)]);
    lemma_permutation_facts(numi::u64s(np, numi::P_ORIG), n as nat);
    assert(numi::stored_cols_ok(np, numi::stored_row(np, rels, i), i));
    assert(numi::run_cols_ok(np, numi::stored_row(np, rels, i), r));
}

/// Runs with the same unit and filing are the same run.
pub proof fn lemma_run_unique(np: Seq<PartView>, sp: Seq<PartView>, db: Database, r: int, r2: int)
    requires
        parts_bound(np, sp, db),
        0 <= r < numi::run_count(np), 0 <= r2 < numi::run_count(np),
        numi::run_uom_of(np, r) == numi::run_uom_of(np, r2),
        numi::run_adsh_of(np, r) == numi::run_adsh_of(np, r2),
    ensures r == r2,
{
    reveal(parts_bound);
    let (ru, ra) = (numi::u64s(np, numi::P_RUN_UOM), numi::u64s(np, numi::P_RUN_ADSH));
    assert(ru[r] < numi::uom_count(np) && ra[r] < numi::adsh_count(np));
    assert(ru[r2] < numi::uom_count(np) && ra[r2] < numi::adsh_count(np));
    lemma_dict_codes(u64_part(np[numi::P_UOM_OFF as int]), u8_part(np[numi::P_UOM_OFF + 1]), numi::uom_count(np), ru[r] as int, ru[r2] as int);
    lemma_dict_codes(u64_part(np[numi::P_ADSH_OFF as int]), u8_part(np[numi::P_ADSH_OFF + 1]), numi::adsh_count(np), ra[r] as int, ra[r2] as int);
    if r < r2 {
        assert(pair_lt(ru[r], ra[r], ru[r2], ra[r2]));
    } else if r2 < r {
        assert(pair_lt(ru[r2], ra[r2], ru[r], ra[r]));
    }
}

/// Stored rows with the same unit, filing and tag as row `i` of run `r` are exactly the rows of run `r` with its
/// tag code.
pub proof fn lemma_same_group(np: Seq<PartView>, sp: Seq<PartView>, db: Database, r: int, i: int, i2: int)
    requires
        parts_bound(np, sp, db),
        0 <= r < numi::run_count(np), n_start(np)[r] <= i < n_start(np)[r + 1],
        0 <= i2 < numi::row_count(np),
    ensures
        (srow(np, db, i2)[5] == srow(np, db, i)[5] && srow(np, db, i2)[0] == srow(np, db, i)[0]
            && srow(np, db, i2)[1] == srow(np, db, i)[1])
        == (n_start(np)[r] <= i2 < n_start(np)[r + 1] && tagc(np, i2) == tagc(np, i)),
{
    reveal(parts_bound);
    let nr = numi::run_count(np);
    lemma_run_of(n_start(np), nr, numi::row_count(np), i2);
    let r2 = run_of(n_start(np), nr, i2);
    lemma_srow(np, sp, db, r, i);
    lemma_srow(np, sp, db, r2, i2);
    let (tv, pt) = (numi::u64s(np, numi::P_TV), numi::u64s(np, numi::P_PAIR_TAG));
    assert(tv[i] < numi::pair_count(np) && tv[i2] < numi::pair_count(np));
    assert(pt[tv[i] as int] < numi::tag_count(np) && pt[tv[i2] as int] < numi::tag_count(np));
    lemma_dict_codes(u64_part(np[numi::P_TAG_OFF as int]), u8_part(np[numi::P_TAG_OFF + 1]), numi::tag_count(np), tagc(np, i), tagc(np, i2));
    if srow(np, db, i2)[5] == srow(np, db, i)[5] && srow(np, db, i2)[0] == srow(np, db, i)[0] {
        lemma_run_unique(np, sp, db, r, r2);
    }
    if n_start(np)[r] <= i2 < n_start(np)[r + 1] {
        assert(in_run(n_start(np), r, i2));
    }
}

/// In a run of unit `u`, a row satisfies `sem::qual` exactly when it holds its tag's largest value in the run.
pub proof fn lemma_qual_seg(np: Seq<PartView>, sp: Seq<PartView>, db: Database, u: Seq<u8>, r: int, i: int)
    requires
        parts_bound(np, sp, db),
        0 <= r < numi::run_count(np), n_start(np)[r] <= i < n_start(np)[r + 1],
        numi::run_uom_of(np, r) == u,
    ensures qual(db.tables[1], u, srow(np, db, i)) == seg_max(np, r, i),
{
    reveal(parts_bound);
    let nums = db.tables[1];
    let orig = numi::u64s(np, numi::P_ORIG);
    let n = numi::row_count(np);
    lemma_rels(np, sp, db);
    lemma_permutation_facts(orig, n as nat);
    lemma_srow(np, sp, db, r, i);
    let x = srow(np, db, i);
    if seg_max(np, r, i) {
        assert forall|k: int| 0 <= k < nums.len() && in_grp(#[trigger] nums[k], u, x[0], x[1]) implies ival(nums[k][7]) <= ival(x[7]) by {
            let i2 = position_of(orig, k);
            assert(srow(np, db, i2) == nums[k]);
            lemma_same_group(np, sp, db, r, i, i2);
            lemma_run_of(n_start(np), numi::run_count(np), n, i2);
            lemma_srow(np, sp, db, run_of(n_start(np), numi::run_count(np), i2), i2);
            assert(tagc(np, i2) == tagc(np, i));
        }
    }
    if qual(nums, u, x) {
        assert forall|i2: int| n_start(np)[r] <= i2 < n_start(np)[r + 1] && #[trigger] tagc(np, i2) == tagc(np, i)
            implies n_value(np)[i2] <= n_value(np)[i] by {
            lemma_same_group(np, sp, db, r, i, i2);
            lemma_srow(np, sp, db, r, i2);
            let k = orig[i2] as int;
            assert(in_grp(nums[k], u, x[0], x[1]));
        }
    }
}


/// Layout facts for counting: the run partition and its bounds.
pub proof fn lemma_runs(np: Seq<PartView>, sp: Seq<PartView>, db: Database)
    requires parts_bound(np, sp, db),
    ensures
        runs_partition_ok(n_start(np), numi::run_count(np), numi::row_count(np)),
        forall|r: int| 0 <= r < numi::run_count(np) ==> 0 <= #[trigger] n_start(np)[r] <= n_start(np)[r + 1] <= numi::row_count(np),
{
    reveal(parts_bound);
    let st = n_start(np);
    let nr = numi::run_count(np);
    assert forall|r: int| 0 <= r < nr implies 0 <= #[trigger] st[r] <= st[r + 1] <= numi::row_count(np) by {
        assert(st[0] <= st[r]);
        assert(st[r + 1] <= st[nr]);
    }
}

/// The run of stored position `i`.
pub proof fn lemma_pos_run(np: Seq<PartView>, sp: Seq<PartView>, db: Database, i: int)
    requires parts_bound(np, sp, db), 0 <= i < numi::row_count(np),
    ensures ({
        let r = run_of(n_start(np), numi::run_count(np), i);
        0 <= r < numi::run_count(np) && n_start(np)[r] <= i < n_start(np)[r + 1]
    }),
{
    lemma_runs(np, sp, db);
    lemma_run_of(n_start(np), numi::run_count(np), numi::row_count(np), i);
}

/// A sum over the canonical num rows is the sum over the stored positions.
pub proof fn lemma_stored_sum(np: Seq<PartView>, sp: Seq<PartView>, db: Database, f: spec_fn(Row) -> int)
    requires parts_bound(np, sp, db),
    ensures sum_of(db.tables[1], f) == sum_idx(0, numi::row_count(np), |i: int| f(srow(np, db, i))),
{
    reveal(parts_bound);
    lemma_rels(np, sp, db);
    let rels = numd::stored_relations(db);
    let n = numi::row_count(np);
    numi::lemma_stored_rows_multiset(np, rels);
    let sg = |i: int| numi::stored_row(np, rels, i);
    lemma_sum_of_perm(db.tables[1], Seq::new(n as nat, sg), f);
    lemma_sum_of_new(n as nat, sg, f);
    lemma_sum_idx_ext(0, n, |i: int| f(sg(i)), |i: int| f(srow(np, db, i)));
}

/// The columns of sub row `j` that the query reads.
pub proof fn lemma_sub_row(np: Seq<PartView>, sp: Seq<PartView>, db: Database, y: int, j: int)
    requires parts_bound(np, sp, db), 0 <= j < db.tables[0].len(),
    ensures
        db.tables[0][j][0] == Val::Text(subi::adsh_bytes(sp, j)),
        db.tables[0][j][2] == Val::Text(name_text(sp, name_code(sp, j))),
        (db.tables[0][j][10] == Val::Int(y)) == fy_ok(sp, y, j),
{
    reveal(parts_bound);
    lemma_rels(np, sp, db);
    assert(subi::sub_row_ok(sp, subd::stored_relations(db)[0][j], j));
}

/// Two `sub` rows with the same adsh are the same row (the declared primary key of `sub`).
pub proof fn lemma_sub_pk(np: Seq<PartView>, sp: Seq<PartView>, db: Database, j1: int, j2: int)
    requires
        parts_bound(np, sp, db),
        0 <= j1 < db.tables[0].len(), 0 <= j2 < db.tables[0].len(),
        subi::adsh_bytes(sp, j1) == subi::adsh_bytes(sp, j2),
    ensures j1 == j2,
{
    lemma_sub_row(np, sp, db, 0, j1);
    lemma_sub_row(np, sp, db, 0, j2);
    reveal(parts_bound);
    let ddb = crate::gendb_constraints::declared_db(db);
    let cols = seq![0nat];
    assert(crate::gendb_constraints::declared_schema().len() == 4) by (compute);
    assert(crate::gendb_constraints::declared_schema()[0].constraints.len() == 1) by (compute);
    assert(crate::gendb_constraints::declared_schema()[0].constraints[0]
        == (crate::spec::types::Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true })) by (compute);
    let (k1, k2) = (crate::spec::constraints::key_of(db.tables[0][j1], cols), crate::spec::constraints::key_of(db.tables[0][j2], cols));
    assert(k1 =~= seq![db.tables[0][j1][0]]);
    assert(k2 =~= seq![db.tables[0][j2][0]]);
    crate::bridge::equality::lemma_lex_cmp_zero(subi::adsh_bytes(sp, j1), subi::adsh_bytes(sp, j2));
    assert(crate::spec::equality::val_not_distinct(k1[0], k2[0]));
    assert(crate::spec::equality::row_not_distinct(k1, k2));
    assert(ddb.tables == db.tables);
    crate::bridge::constraints::lemma_primary_key_identifies(ddb, 0, 0, cols, true, j1, j2);
}

/// `adsh_order` is a permutation of the sub rows.
pub proof fn lemma_sub_order(np: Seq<PartView>, sp: Seq<PartView>, db: Database)
    requires parts_bound(np, sp, db),
    ensures
        crate::stores::sub::interface::common::perm::is_permutation(s_order(sp), db.tables[0].len()),
{
    reveal(parts_bound);
    lemma_rels(np, sp, db);
}

/// A database bound to the stores is bound to both storages' parts.
pub proof fn lemma_bound_parts(sv: crate::gendb_entry::stores::StoresView, db: Database)
    requires crate::gendb_entry::bound_db(sv, db),
    ensures parts_bound(sv.num_vord, sv.sub, db),
{
    reveal(parts_bound);
}

/// The layouts of both storages hold.
pub proof fn lemma_bound_layouts(np: Seq<PartView>, sp: Seq<PartView>, db: Database)
    requires parts_bound(np, sp, db),
    ensures numi::num_layout_ok(np), subi::sub_layout_ok(sp), subi::row_count(sp) == db.tables[0].len(),
{
    reveal(parts_bound);
    lemma_rels(np, sp, db);
}

} // verus!
