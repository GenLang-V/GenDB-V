//! The three inner levels of the nested sum, each collapsed onto its stored layout:
//! - num (`lemma_num_level`): the num rows of one filing's adsh, one unit and one (tag, version) are the rows of one
//!   pair code inside one `(uom, adsh)` run;
//! - tag (`lemma_tag_level`): by the primary key (tag, version), at most one tag row matches a (tag, version);
//! - pre (`lemma_pre_level`): the pre rows of one adsh and one stmt are the rows of that adsh's sub-runs whose
//!   (stmt, rfile) group has that stmt.
//! The executable lookups are stated as byte-level facts (`num_found`, `tag_found`, `pre_found`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::typing::db_wf;
use crate::spec::constraints::*;
use crate::spec::types::Constraint;
use crate::schema::schema_spec;
use crate::gendb_constraints::{declared_db, declared_schema};
use crate::gendb_entry::layout::PartView;
use crate::link::query::{proj, proj_all};
use crate::link::join::sum_of;
use crate::bridge::equality::lemma_row_not_distinct_refl;
use crate::bridge::constraints::lemma_primary_key_identifies;
use crate::stores::num::interface as N;
use crate::stores::pre::interface as P;
use crate::stores::sub_sic::interface as S;
use crate::stores::tag_tv::interface as T;
use crate::stores::num::interface::common::runs::{run_of, lemma_run_of, in_run};
use crate::stores::num::interface::common::text::{text_entry, lemma_dict_codes};
use crate::agent::common::sums::*;
use crate::agent::group::num4;

verus! {

// ------------------------------------------------------------------------------------------------ stored relations

proof fn lemma_proj_ident(rows: Seq<Row>, cols: Seq<nat>, w: nat)
    requires
        cols.len() == w,
        forall|k: int| 0 <= k < w ==> #[trigger] cols[k] == k,
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] rows[i]).len() == w,
    ensures proj_all(rows, cols) == rows,
{
    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] proj_all(rows, cols)[i] == rows[i] by {
        assert(proj(rows[i], cols) =~= rows[i]);
    }
    assert(proj_all(rows, cols) =~= rows);
}

/// Each storage's stored relation is its table's rows.
pub proof fn lemma_rels(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures
        crate::stores::num::declaration::stored_relations(db) == seq![db.tables[1]],
        crate::stores::sub_sic::declaration::stored_relations(db) == seq![db.tables[0]],
        crate::stores::tag_tv::declaration::stored_relations(db) == seq![db.tables[2]],
        crate::stores::pre::declaration::stored_relations(db) == seq![db.tables[3]],
{
    crate::agent::sem::lemma_rows_typed(db);
    let s = schema_spec();
    assert forall|t: int, i: int| 0 <= t < 4 && 0 <= i < db.tables[t].len() implies (#[trigger] db.tables[t][i]).len() == s[t].columns.len() by {
        assert(crate::spec::typing::row_in_table(db.tables[t][i], s[t]));
    }
    assert(s[0].columns.len() == 20 && s[1].columns.len() == 9 && s[2].columns.len() == 9 && s[3].columns.len() == 10);
    let c1 = crate::stores::num::declaration::stored_cols_t0();
    let c0 = crate::stores::sub_sic::declaration::stored_cols_t0();
    let c2 = crate::stores::tag_tv::declaration::stored_cols_t0();
    let c3 = crate::stores::pre::declaration::stored_cols_t0();
    assert forall|k: int| 0 <= k < 9 implies #[trigger] c1[k] == k by {}
    assert forall|k: int| 0 <= k < 20 implies #[trigger] c0[k] == k by {}
    assert forall|k: int| 0 <= k < 9 implies #[trigger] c2[k] == k by {}
    assert forall|k: int| 0 <= k < 10 implies #[trigger] c3[k] == k by {}
    lemma_proj_ident(db.tables[1], c1, 9);
    lemma_proj_ident(db.tables[0], c0, 20);
    lemma_proj_ident(db.tables[2], c2, 9);
    lemma_proj_ident(db.tables[3], c3, 10);
}

// ------------------------------------------------------------------------------------------------ partitions

/// A run partition of `[0, start[runs])`: the sum over the positions is the sum over the runs.
pub proof fn lemma_rsum_runs(start: Seq<u64>, runs: int, k: int, h: spec_fn(int) -> int)
    requires 0 <= k <= runs, start.len() == runs + 1, start[0] == 0,
        forall|a: int, b: int| 0 <= a < b <= runs ==> #[trigger] start[a] < #[trigger] start[b],
    ensures rsum(0, start[k] as int, h) == rsum(0, k, |s: int| rsum(start[s] as int, start[s + 1] as int, h)),
    decreases k,
{
    if k > 0 {
        lemma_rsum_runs(start, runs, k - 1, h);
        lemma_rsum_split(0, start[k - 1] as int, start[k] as int, h);
    }
}

// ------------------------------------------------------------------------------------------------ num

/// Stored num row `i`.
pub open spec fn nrow(db: Database, num: Seq<PartView>, i: int) -> Row {
    db.tables[1][N::u64s(num, N::P_ORIG)[i] as int]
}

/// A num row of the filing's adsh, the unit `$1` and one (tag, version).
pub open spec fn nmatch(n: Row, b0: Seq<u8>, a: Seq<u8>, tg: Seq<u8>, vr: Seq<u8>) -> bool {
    n[0] == Val::Text(a) && n[1] == Val::Text(tg) && n[2] == Val::Text(vr) && n[5] == Val::Text(b0)
}

/// The num-level weight function.
pub open spec fn nfun(b0: Seq<u8>, a: Seq<u8>, tg: Seq<u8>, vr: Seq<u8>, phi: spec_fn(Val) -> int) -> spec_fn(Row) -> int {
    |n: Row| if nmatch(n, b0, a, tg, vr) { phi(n[7]) } else { 0 }
}

pub open spec fn uom_entry(num: Seq<PartView>, k: int) -> Seq<u8> { N::dict_entry(num, N::P_UOM_OFF, k) }

pub open spec fn ntag_entry(num: Seq<PartView>, c: int) -> Seq<u8> {
    N::dict_entry(num, N::P_TAG_OFF, N::u64s(num, N::P_PAIR_TAG)[c] as int)
}

pub open spec fn nver_entry(num: Seq<PartView>, c: int) -> Seq<u8> {
    N::dict_entry(num, N::P_VERSION_OFF, N::u64s(num, N::P_PAIR_VERSION)[c] as int)
}

/// The executable lookup of the filing's run: the uom code `u` of `$1` and the filing's `(uom, adsh)` run, `-1`
/// when absent.
pub open spec fn run_found(num: Seq<PartView>, b0: Seq<u8>, a: Seq<u8>, u: int, run: int) -> bool {
    &&& (run >= 0 ==> 0 <= u < N::uom_count(num) && uom_entry(num, u) == b0 && run < N::run_count(num)
            && N::u64s(num, N::P_RUN_UOM)[run] == u && N::run_adsh_of(num, run) == a)
    &&& (run < 0 ==> forall|r: int| 0 <= r < N::run_count(num) ==> !(#[trigger] N::run_uom_of(num, r) == b0 && N::run_adsh_of(num, r) == a))
}

/// The executable lookup of a (tag, version) among num's pairs: its pair code, `-1` when absent.
pub open spec fn pair_found(num: Seq<PartView>, tg: Seq<u8>, vr: Seq<u8>, nq: int) -> bool {
    &&& (nq >= 0 ==> nq < N::pair_count(num) && ntag_entry(num, nq) == tg && nver_entry(num, nq) == vr)
    &&& (nq < 0 ==> forall|c: int| 0 <= c < N::pair_count(num) ==> !(#[trigger] ntag_entry(num, c) == tg && nver_entry(num, c) == vr))
}

/// Both lookups of one (filing, pre row).
pub open spec fn num_found(num: Seq<PartView>, b0: Seq<u8>, a: Seq<u8>, tg: Seq<u8>, vr: Seq<u8>, u: int, run: int, nq: int) -> bool {
    run_found(num, b0, a, u, run) && pair_found(num, tg, vr, nq)
}

/// The weight of stored num row `i` when it has pair code `nq`.
pub open spec fn run_pair_term(num: Seq<PartView>, nq: int, phi: spec_fn(Val) -> int) -> spec_fn(int) -> int {
    |i: int| if N::u64s(num, N::P_TV)[i] == nq { phi(num4(crate::stores::num::interface::common::cols::i128_part(num[N::P_VALUE as int])[i] as int)) } else { 0 }
}

/// The weight of the matched stored num rows of one run and one pair code.
pub open spec fn run_pair_sum(num: Seq<PartView>, rs: int, re: int, nq: int, phi: spec_fn(Val) -> int) -> int {
    rsum(rs, re, run_pair_term(num, nq, phi))
}

/// The num-level weight of stored row `i`.
pub open spec fn nterm(db: Database, num: Seq<PartView>, b0: Seq<u8>, a: Seq<u8>, tg: Seq<u8>, vr: Seq<u8>, phi: spec_fn(Val) -> int, i: int) -> int {
    if nmatch(nrow(db, num, i), b0, a, tg, vr) { phi(nrow(db, num, i)[7]) } else { 0 }
}

pub open spec fn nvals(num: Seq<PartView>) -> Seq<i128> {
    crate::stores::num::interface::common::cols::i128_part(num[N::P_VALUE as int])
}

/// The column facts of stored num row `i`, by its run.
proof fn lemma_num_row(db: Database, num: Seq<PartView>, i: int)
    requires N::represents(num, seq![db.tables[1]]), 0 <= i < N::row_count(num),
    ensures ({
        let start = N::u64s(num, N::P_RUN_START);
        let r = run_of(start, N::run_count(num), i);
        &&& 0 <= r < N::run_count(num) && start[r] <= i < start[r + 1]
        &&& forall|r2: int| 0 <= r2 < N::run_count(num) && #[trigger] in_run(start, r2, i) ==> r2 == r
        &&& nrow(db, num, i)[0] == Val::Text(N::run_adsh_of(num, r))
        &&& nrow(db, num, i)[5] == Val::Text(N::run_uom_of(num, r))
        &&& nrow(db, num, i)[1] == Val::Text(N::tag_of(num, i))
        &&& nrow(db, num, i)[2] == Val::Text(N::version_of(num, i))
        &&& nrow(db, num, i)[7] == num4(nvals(num)[i] as int)
        &&& N::u64s(num, N::P_TV)[i] < N::pair_count(num)
    }),
{
    let rels = seq![db.tables[1]];
    let start = N::u64s(num, N::P_RUN_START);
    lemma_run_of(start, N::run_count(num), N::row_count(num), i);
    let r = run_of(start, N::run_count(num), i);
    assert(N::stored_cols_ok(num, N::stored_row(num, rels, i), i));
    assert(N::run_cols_ok(num, N::stored_row(num, rels, i), r));
}

/// Without a run or a pair code, no stored row matches.
proof fn lemma_num_none(db: Database, num: Seq<PartView>, b0: Seq<u8>, a: Seq<u8>, tg: Seq<u8>, vr: Seq<u8>,
    u: int, run: int, nq: int, phi: spec_fn(Val) -> int, i: int)
    requires
        N::represents(num, seq![db.tables[1]]), num_found(num, b0, a, tg, vr, u, run, nq),
        run < 0 || nq < 0, 0 <= i < N::row_count(num),
    ensures nterm(db, num, b0, a, tg, vr, phi, i) == 0,
{
    lemma_num_row(db, num, i);
    let r = run_of(N::u64s(num, N::P_RUN_START), N::run_count(num), i);
    if nmatch(nrow(db, num, i), b0, a, tg, vr) {
        if run < 0 {
            assert(N::run_uom_of(num, r) == b0 && N::run_adsh_of(num, r) == a);
        } else {
            let c = N::u64s(num, N::P_TV)[i] as int;
            assert(ntag_entry(num, c) == tg && nver_entry(num, c) == vr);
        }
    }
}

/// Outside the filing's run, no stored row matches (run keys are distinct, dictionary codes are distinct).
proof fn lemma_num_outside(db: Database, num: Seq<PartView>, b0: Seq<u8>, a: Seq<u8>, tg: Seq<u8>, vr: Seq<u8>,
    u: int, run: int, nq: int, phi: spec_fn(Val) -> int, i: int)
    requires
        N::represents(num, seq![db.tables[1]]), num_found(num, b0, a, tg, vr, u, run, nq),
        run >= 0, 0 <= i < N::row_count(num),
        !(N::u64s(num, N::P_RUN_START)[run] <= i < N::u64s(num, N::P_RUN_START)[run + 1]),
    ensures nterm(db, num, b0, a, tg, vr, phi, i) == 0,
{
    lemma_num_row(db, num, i);
    let start = N::u64s(num, N::P_RUN_START);
    let r = run_of(start, N::run_count(num), i);
    if nmatch(nrow(db, num, i), b0, a, tg, vr) {
        assert(r != run);
        let ru = N::u64s(num, N::P_RUN_UOM);
        let ra = N::u64s(num, N::P_RUN_ADSH);
        let ucount = N::uom_count(num);
        let acount = N::adsh_count(num);
        assert(ru[r] < ucount && ra[r] < acount && ru[run] < ucount && ra[run] < acount);
        lemma_dict_codes(crate::stores::num::interface::common::text::u64_part(num[N::P_UOM_OFF as int]),
            crate::stores::num::interface::common::text::u8_part(num[N::P_UOM_OFF + 1]), ucount, ru[r] as int, u);
        lemma_dict_codes(crate::stores::num::interface::common::text::u64_part(num[N::P_ADSH_OFF as int]),
            crate::stores::num::interface::common::text::u8_part(num[N::P_ADSH_OFF + 1]), acount, ra[r] as int, ra[run] as int);
        assert(ru[r] == ru[run] && ra[r] == ra[run]);
        if r < run {
            assert(crate::stores::num::interface::common::runs::pair_lt(ru[r], ra[r], ru[run], ra[run]));
        } else {
            assert(crate::stores::num::interface::common::runs::pair_lt(ru[run], ra[run], ru[r], ra[r]));
        }
    }
}

/// Inside the filing's run, a stored row matches exactly when it has the pre row's pair code.
proof fn lemma_num_inside(db: Database, num: Seq<PartView>, b0: Seq<u8>, a: Seq<u8>, tg: Seq<u8>, vr: Seq<u8>,
    u: int, run: int, nq: int, phi: spec_fn(Val) -> int, i: int)
    requires
        N::represents(num, seq![db.tables[1]]), num_found(num, b0, a, tg, vr, u, run, nq),
        run >= 0, nq >= 0,
        N::u64s(num, N::P_RUN_START)[run] <= i < N::u64s(num, N::P_RUN_START)[run + 1],
        i < N::row_count(num),
    ensures
        nterm(db, num, b0, a, tg, vr, phi, i)
            == if N::u64s(num, N::P_TV)[i] == nq { phi(num4(nvals(num)[i] as int)) } else { 0 },
{
    lemma_num_row(db, num, i);
    let start = N::u64s(num, N::P_RUN_START);
    let r = run_of(start, N::run_count(num), i);
    assert(in_run(start, run, i));
    assert(r == run);
    let tv = N::u64s(num, N::P_TV);
    let pt = N::u64s(num, N::P_PAIR_TAG);
    let pv = N::u64s(num, N::P_PAIR_VERSION);
    let tcount = N::tag_count(num);
    let vcount = N::version_count(num);
    let c = tv[i] as int;
    assert(pt[c] < tcount && pv[c] < vcount && pt[nq] < tcount && pv[nq] < vcount);
    lemma_dict_codes(crate::stores::num::interface::common::text::u64_part(num[N::P_TAG_OFF as int]),
        crate::stores::num::interface::common::text::u8_part(num[N::P_TAG_OFF + 1]), tcount, pt[c] as int, pt[nq] as int);
    lemma_dict_codes(crate::stores::num::interface::common::text::u64_part(num[N::P_VERSION_OFF as int]),
        crate::stores::num::interface::common::text::u8_part(num[N::P_VERSION_OFF + 1]), vcount, pv[c] as int, pv[nq] as int);
    if c != nq {
        if c < nq {
            assert(crate::stores::num::interface::common::runs::pair_lt(pt[c], pv[c], pt[nq], pv[nq]));
        } else {
            assert(crate::stores::num::interface::common::runs::pair_lt(pt[nq], pv[nq], pt[c], pv[c]));
        }
    }
}

/// Without the filing's run, no num row matches (any (tag, version)).
pub proof fn lemma_num_level_norun(db: Database, num: Seq<PartView>, b0: Seq<u8>, a: Seq<u8>, tg: Seq<u8>, vr: Seq<u8>,
    u: int, phi: spec_fn(Val) -> int)
    requires N::represents(num, seq![db.tables[1]]), run_found(num, b0, a, u, -1),
    ensures sum_of(db.tables[1], nfun(b0, a, tg, vr, phi)) == 0,
{
    let h = nfun(b0, a, tg, vr, phi);
    let orig = N::u64s(num, N::P_ORIG);
    assert forall|k: int| 0 <= k < db.tables[1].len() implies #[trigger] h(db.tables[1][k]) == 0 by {
        let nn = N::row_count(num);
        crate::stores::num::interface::common::perm::lemma_permutation_facts(orig, nn as nat);
        let i = crate::stores::num::interface::common::perm::position_of(orig, k);
        lemma_num_row(db, num, i);
        let r = run_of(N::u64s(num, N::P_RUN_START), N::run_count(num), i);
        assert(nrow(db, num, i) == db.tables[1][k]);
        if nmatch(nrow(db, num, i), b0, a, tg, vr) {
            assert(N::run_uom_of(num, r) == b0 && N::run_adsh_of(num, r) == a);
        }
    }
    crate::link::join::lemma_sum_of_zero(db.tables[1], h);
}

/// The num level: the matching num rows are the stored rows of the filing's run with the pre row's pair code.
pub proof fn lemma_num_level(db: Database, num: Seq<PartView>, b0: Seq<u8>, a: Seq<u8>, tg: Seq<u8>, vr: Seq<u8>,
    u: int, run: int, nq: int, phi: spec_fn(Val) -> int)
    requires
        N::represents(num, seq![db.tables[1]]),
        num_found(num, b0, a, tg, vr, u, run, nq),
    ensures
        sum_of(db.tables[1], nfun(b0, a, tg, vr, phi))
            == if run >= 0 && nq >= 0 {
                run_pair_sum(num, N::u64s(num, N::P_RUN_START)[run] as int, N::u64s(num, N::P_RUN_START)[run + 1] as int, nq, phi)
            } else { 0 },
{
    let rels = seq![db.tables[1]];
    let nn = N::row_count(num);
    let nr = N::run_count(num);
    let orig = N::u64s(num, N::P_ORIG);
    let start = N::u64s(num, N::P_RUN_START);
    let h = nfun(b0, a, tg, vr, phi);
    N::lemma_stored_rows_multiset(num, rels);
    assert(Seq::new(nn as nat, |i: int| N::stored_row(num, rels, i)) =~= Seq::new(db.tables[1].len(), |i: int| db.tables[1][orig[i] as int]));
    lemma_sum_of_permuted(db.tables[1], orig, h);
    let hh = |i: int| nterm(db, num, b0, a, tg, vr, phi, i);
    assert(db.tables[1].len() == nn);
    lemma_rsum_ext(0, nn, |i: int| h(db.tables[1][orig[i] as int]), hh);
    assert(sum_of(db.tables[1], h) == rsum(0, nn, hh));
    if run < 0 || nq < 0 {
        assert forall|i: int| 0 <= i < nn implies #[trigger] hh(i) == 0 by {
            lemma_num_none(db, num, b0, a, tg, vr, u, run, nq, phi, i);
        }
        lemma_rsum_zero(0, nn, hh);
        assert(sum_of(db.tables[1], h) == 0);
    } else {
        let (rs, re) = (start[run] as int, start[run + 1] as int);
        assert(start[0] == 0 && start[nr] == nn);
        assert(0 <= rs <= re <= nn) by {
            if run > 0 { assert(start[0] < start[run]); }
            if run + 1 < nr { assert(start[run + 1] < start[nr]); }
        }
        assert forall|i: int| 0 <= i < nn && !(rs <= i < re) implies #[trigger] hh(i) == 0 by {
            lemma_num_outside(db, num, b0, a, tg, vr, u, run, nq, phi, i);
        }
        let target = run_pair_term(num, nq, phi);
        assert forall|i: int| rs <= i < re implies #[trigger] hh(i) == target(i) by {
            lemma_num_inside(db, num, b0, a, tg, vr, u, run, nq, phi, i);
        }
        lemma_rsum_window(0, rs, re, nn, hh);
        lemma_rsum_ext(rs, re, hh, target);
        assert(sum_of(db.tables[1], h) == run_pair_sum(num, rs, re, nq, phi));
    }
}

// ------------------------------------------------------------------------------------------------ tag

/// A tag row of one (tag, version), not abstract.
pub open spec fn tmatch(t: Row, tg: Seq<u8>, vr: Seq<u8>) -> bool {
    t[0] == Val::Text(tg) && t[1] == Val::Text(vr) && t[3] == Val::Int(0)
}

/// The tag-level weight function.
pub open spec fn tfun(tg: Seq<u8>, vr: Seq<u8>, psi: spec_fn(Val) -> int) -> spec_fn(Row) -> int {
    |t: Row| if tmatch(t, tg, vr) { psi(t[7]) } else { 0 }
}

pub open spec fn ttag_entry(tagp: Seq<PartView>, r: int) -> Seq<u8> {
    crate::stores::tag_tv::interface::common::cols::list_entry(tagp, T::P_TAG_OFF, crate::stores::tag_tv::interface::common::cols::u64s(tagp, T::P_TAG_CODES)[r] as int)
}

pub open spec fn tver_entry(tagp: Seq<PartView>, r: int) -> Seq<u8> {
    crate::stores::tag_tv::interface::common::cols::list_entry(tagp, T::P_VERSION_OFF, crate::stores::tag_tv::interface::common::cols::u64s(tagp, T::P_VERSION_CODES)[r] as int)
}

/// The executable lookup of a (tag, version): its tag row, or `-1` when no row has it.
pub open spec fn tag_found(tagp: Seq<PartView>, tg: Seq<u8>, vr: Seq<u8>, tr: int) -> bool {
    &&& (tr >= 0 ==> tr < T::row_count(tagp) && ttag_entry(tagp, tr) == tg && tver_entry(tagp, tr) == vr)
    &&& (tr < 0 ==> forall|r: int| 0 <= r < T::row_count(tagp) ==> !(#[trigger] ttag_entry(tagp, r) == tg && tver_entry(tagp, r) == vr))
}

pub open spec fn tag_abstract(tagp: Seq<PartView>, r: int) -> int {
    crate::stores::tag_tv::interface::common::cols::i32_part(tagp[T::P_ABSTRACT as int])[r] as int
}

/// The tag level: by the primary key, the one tag row of the (tag, version) if it is not abstract.
pub proof fn lemma_tag_level(db: Database, tagp: Seq<PartView>, tg: Seq<u8>, vr: Seq<u8>, tr: int, psi: spec_fn(Val) -> int)
    requires
        db.schema == schema_spec(), db_wf(db), constraints_hold(declared_db(db)),
        T::represents(tagp, seq![db.tables[2]]),
        tag_found(tagp, tg, vr, tr),
    ensures
        sum_of(db.tables[2], tfun(tg, vr, psi))
            == if tr >= 0 && tag_abstract(tagp, tr) == 0 { psi(db.tables[2][tr][7]) } else { 0 },
{
    let tab = db.tables[2];
    let h = tfun(tg, vr, psi);
    lemma_sum_of_rsum(tab, h);
    let hh = |i: int| h(tab[i]);
    let n = tab.len() as int;
    assert forall|i: int| 0 <= i < n implies {
        &&& #[trigger] tab[i][0] == Val::Text(ttag_entry(tagp, i))
        &&& tab[i][1] == Val::Text(tver_entry(tagp, i))
        &&& tab[i][3] == Val::Int(tag_abstract(tagp, i))
    } by {
        assert(T::tag_row_ok(tagp, tab[i], i));
    }
    if tr < 0 {
        assert forall|i: int| 0 <= i < n implies #[trigger] hh(i) == 0 by {
            assert(tab[i][0] == Val::Text(ttag_entry(tagp, i)));
        }
        lemma_rsum_zero(0, n, hh);
    } else {
        let dd = declared_db(db);
        crate::gendb_constraints::lemma_declared_schema();
        let cols = seq![0nat, 1nat];
        assert(dd.schema[2].constraints[0] == (Constraint::Key { cols, primary: true, nulls_distinct: true }));
        assert forall|i: int| 0 <= i < n && i != tr implies #[trigger] hh(i) == 0 by {
            assert(tab[i][0] == Val::Text(ttag_entry(tagp, i)));
            assert(tab[tr][0] == Val::Text(ttag_entry(tagp, tr)));
            if tmatch(tab[i], tg, vr) {
                let ki = key_of(dd.tables[2][i], cols);
                let kt = key_of(dd.tables[2][tr], cols);
                assert(ki =~= kt);
                lemma_row_not_distinct_refl(ki);
                lemma_primary_key_identifies(dd, 2, 0, cols, true, i, tr);
            }
        }
        assert(tab[tr][0] == Val::Text(ttag_entry(tagp, tr)));
        lemma_rsum_single(0, n, hh, tr);
    }
}

// ------------------------------------------------------------------------------------------------ pre

/// Stored pre row `j`.
pub open spec fn prow(db: Database, pre: Seq<PartView>, j: int) -> Row {
    db.tables[3][crate::stores::pre::interface::common::cols::u64s(pre, P::P_ORIG)[j] as int]
}

/// A pre row of the filing's adsh with stmt `$2`.
pub open spec fn pmatch(p: Row, a: Seq<u8>, b1: Seq<u8>) -> bool {
    p[0] == Val::Text(a) && p[3] == Val::Text(b1)
}

/// The pre-level weight function.
pub open spec fn pfun(a: Seq<u8>, b1: Seq<u8>, y: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |p: Row| if pmatch(p, a, b1) { y(p) } else { 0 }
}

/// `y` of stored pre row `j`.
pub open spec fn yrow(db: Database, pre: Seq<PartView>, y: spec_fn(Row) -> int) -> spec_fn(int) -> int {
    |j: int| y(prow(db, pre, j))
}

pub open spec fn pre_u64s(pre: Seq<PartView>, k: usize) -> Seq<u64> { crate::stores::pre::interface::common::cols::u64s(pre, k) }

pub open spec fn padsh_entry(pre: Seq<PartView>, k: int) -> Seq<u8> {
    crate::stores::pre::interface::common::cols::list_entry(pre, P::P_ADSH_OFF, k)
}

pub open spec fn pstmt_entry(pre: Seq<PartView>, k: int) -> Seq<u8> {
    crate::stores::pre::interface::common::cols::list_entry(pre, P::P_STMT_OFF, k)
}

/// The executable lookups: the pre adsh code of the filing and the stmt code of `$2`, each `-1` when absent.
pub open spec fn pre_found(pre: Seq<PartView>, a: Seq<u8>, b1: Seq<u8>, pc: int, sc: int) -> bool {
    &&& (pc >= 0 ==> pc < P::adsh_count(pre) && padsh_entry(pre, pc) == a)
    &&& (pc < 0 ==> forall|k: int| 0 <= k < P::adsh_count(pre) ==> #[trigger] padsh_entry(pre, k) != a)
    &&& (sc >= 0 ==> sc < P::stmt_count(pre) && pstmt_entry(pre, sc) == b1)
    &&& (sc < 0 ==> forall|k: int| 0 <= k < P::stmt_count(pre) ==> #[trigger] pstmt_entry(pre, k) != b1)
}

/// The (stmt, rfile) group `g` has stmt `$2`.
pub open spec fn gq(pre: Seq<PartView>, sc: int, g: int) -> bool {
    sc >= 0 && pre_u64s(pre, P::P_GROUP_STMT)[g] == sc + 1
}

/// `y` summed over sub-run `s`'s stored rows when its group has stmt `$2`, else 0.
pub open spec fn sub_term(pre: Seq<PartView>, sc: int, y: spec_fn(int) -> int) -> spec_fn(int) -> int {
    |s: int| if gq(pre, sc, pre_u64s(pre, P::P_SUB_GROUP)[s] as int) {
        rsum(pre_u64s(pre, P::P_SUB_START)[s] as int, pre_u64s(pre, P::P_SUB_START)[s + 1] as int, y)
    } else { 0 }
}

/// Sum over the sub-runs `[s0, s1)` whose group has stmt `$2`, of `y` over each sub-run's stored rows.
pub open spec fn subs_sum(pre: Seq<PartView>, sc: int, s0: int, s1: int, y: spec_fn(int) -> int) -> int {
    rsum(s0, s1, sub_term(pre, sc, y))
}

/// The pre level: the filing's pre rows with stmt `$2` are the rows of its adsh's sub-runs of qualifying groups.
pub proof fn lemma_pre_level(db: Database, pre: Seq<PartView>, a: Seq<u8>, b1: Seq<u8>, pc: int, sc: int, y: spec_fn(Row) -> int)
    requires
        P::represents(pre, seq![db.tables[3]]),
        pre_found(pre, a, b1, pc, sc),
    ensures
        sum_of(db.tables[3], pfun(a, b1, y))
            == if pc >= 0 {
                subs_sum(pre, sc, pre_u64s(pre, P::P_ADSH_SUBS)[pc] as int, pre_u64s(pre, P::P_ADSH_SUBS)[pc + 1] as int,
                    yrow(db, pre, y))
            } else { 0 },
{
    let rels = seq![db.tables[3]];
    let n = P::row_count(pre);
    let ns = P::sub_count(pre);
    let orig = pre_u64s(pre, P::P_ORIG);
    let start = pre_u64s(pre, P::P_SUB_START);
    let sadsh = pre_u64s(pre, P::P_SUB_ADSH);
    let sgroup = pre_u64s(pre, P::P_SUB_GROUP);
    let gstmt = pre_u64s(pre, P::P_GROUP_STMT);
    let h = pfun(a, b1, y);
    P::lemma_stored_rows_multiset(pre, rels);
    assert(Seq::new(n as nat, |j: int| P::stored_row(pre, rels, j)) =~= Seq::new(db.tables[3].len(), |j: int| db.tables[3][orig[j] as int]));
    lemma_sum_of_permuted(db.tables[3], orig, h);
    let hh = |j: int| h(db.tables[3][orig[j] as int]);
    let yj = yrow(db, pre, y);
    // The value of row `j`: its sub-run decides adsh and stmt.
    let acount = P::adsh_count(pre);
    let scount = P::stmt_count(pre);
    let val = |s: int, j: int| if sadsh[s] == pc && gq(pre, sc, sgroup[s] as int) { yj(j) } else { 0 };
    assert forall|j: int| 0 <= j < n implies #[trigger] hh(j) == val(run_of(start, ns, j), j) by {
        lemma_run_of(start, ns, n, j);
        let s = run_of(start, ns, j);
        assert(P::sub_cols_ok(pre, P::stored_row(pre, rels, j), s));
        let p = prow(db, pre, j);
        assert(p == P::stored_row(pre, rels, j));
        let g = sgroup[s] as int;
        assert(sadsh[s] < acount && g < P::group_count(pre));
        assert(gstmt[g] <= scount);
        if pc >= 0 {
            crate::stores::pre::interface::common::text::lemma_dict_codes(crate::stores::pre::interface::common::text::u64_part(pre[P::P_ADSH_OFF as int]),
                crate::stores::pre::interface::common::text::u8_part(pre[P::P_ADSH_OFF + 1]), acount, sadsh[s] as int, pc);
        } else {
            assert(padsh_entry(pre, sadsh[s] as int) != a);
        }
        if gstmt[g] != 0 {
            let k = gstmt[g] - 1;
            if sc >= 0 {
                crate::stores::pre::interface::common::text::lemma_dict_codes(crate::stores::pre::interface::common::text::u64_part(pre[P::P_STMT_OFF as int]),
                    crate::stores::pre::interface::common::text::u8_part(pre[P::P_STMT_OFF + 1]), scount, k, sc);
            } else {
                assert(pstmt_entry(pre, k) != b1);
            }
        }
    }
    // Inside sub-run `s`, row `j`'s value is `val(s, j)`.
    assert forall|s: int, j: int| 0 <= s < ns && #[trigger] in_run(start, s, j) implies hh(j) == val(s, j) by {
        assert(start[s + 1] <= start[ns]) by { if s + 1 < ns { assert(start[s + 1] < start[ns]); } }
        lemma_run_of(start, ns, n, j);
    }
    // Rows by sub-runs.
    assert(start[0] == 0 && start[ns] == n);
    lemma_rsum_runs(start, ns, ns, hh);
    let per = |s: int| rsum(start[s] as int, start[s + 1] as int, hh);
    let qual_sub = sub_term(pre, sc, yj);
    if pc < 0 {
        assert forall|s: int| 0 <= s < ns implies #[trigger] per(s) == 0 by {
            assert forall|j: int| start[s] <= j < start[s + 1] implies #[trigger] hh(j) == 0 by { assert(in_run(start, s, j)); }
            lemma_rsum_zero(start[s] as int, start[s + 1] as int, hh);
        }
        lemma_rsum_zero(0, ns, per);
    } else {
        P::lemma_adsh_subs(pre, pc);
        let as0 = pre_u64s(pre, P::P_ADSH_SUBS)[pc] as int;
        let as1 = pre_u64s(pre, P::P_ADSH_SUBS)[pc + 1] as int;
        assert forall|s: int| 0 <= s < ns && !(as0 <= s < as1) implies #[trigger] per(s) == 0 by {
            assert(sadsh[s] != pc);
            assert forall|j: int| start[s] <= j < start[s + 1] implies #[trigger] hh(j) == 0 by { assert(in_run(start, s, j)); }
            lemma_rsum_zero(start[s] as int, start[s + 1] as int, hh);
        }
        lemma_rsum_window(0, as0, as1, ns, per);
        assert forall|s: int| as0 <= s < as1 implies #[trigger] per(s) == qual_sub(s) by {
            assert(sadsh[s] == pc);
            if gq(pre, sc, sgroup[s] as int) {
                assert forall|j: int| start[s] <= j < start[s + 1] implies #[trigger] hh(j) == yj(j) by { assert(in_run(start, s, j)); }
                lemma_rsum_ext(start[s] as int, start[s + 1] as int, hh, yj);
            } else {
                assert forall|j: int| start[s] <= j < start[s + 1] implies #[trigger] hh(j) == 0 by { assert(in_run(start, s, j)); }
                lemma_rsum_zero(start[s] as int, start[s + 1] as int, hh);
            }
        }
        lemma_rsum_ext(as0, as1, per, qual_sub);
    }
}

} // verus!
