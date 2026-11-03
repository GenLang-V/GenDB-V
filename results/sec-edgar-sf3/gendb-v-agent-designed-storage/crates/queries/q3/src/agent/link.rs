//! From the computed filings and groups to the SQL normal form, for every database bound to the storages.
//!
//! - per `sub` row `j`: its relation row's adsh, group keys and `fy` test are those the scan read (`lemma_sub_row`);
//!   its per-filing sums are its run's (`lemma_fsum_facts`);
//! - a group key of the computation (cik word, name code) names the SQL key `kspec` (name text, cik integer);
//! - the toolkit accumulators of a SQL key are range sums over `sub` rows of the qualifying rows' run sums
//!   (`lemma_acc`), and so are the sums over the scan's filings (`lemma_filt_total`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::gendb_entry::layout::PartView;
use crate::link::query::{QuerySpec, gsum, gabs, gcount, proj, proj_all};
use crate::link::join::sum_of;
use crate::stores::num::interface as num_if;
use crate::stores::sub_fy::interface as sub_if;
use crate::stores::sub_fy::interface::common::text::{text_entry, u8_part, u64_part};
use crate::stores::sub_fy::interface::common::cols::{text_count, i32_part};
use crate::stores::sub_fy::interface::common::perm::is_permutation;
use crate::agent::common::sort::Filing;
use crate::agent::common::sums::*;
use crate::agent::nf::*;
use crate::agent::numlink::*;
use crate::agent::scan::*;
use crate::agent::groups::{gkey, sum_f, mass_f};

verus! {

// ------------------------------------------------------------------------------------------------ the bound database

/// `db` is bound to the parts of the scan context: the shapes of the rows and both storages' relations.
pub open spec fn bound(db: Database, c: ScanCtx) -> bool {
    &&& rows_ok(db)
    &&& num_if::represents(c.np, crate::stores::num::declaration::stored_relations(db))
    &&& sub_if::represents(c.sp, crate::stores::sub_fy::declaration::stored_relations(db))
}

/// `$1` is the uom dictionary's value `u`.
pub open spec fn uom_is(c: ScanCtx, p0: Seq<u8>) -> bool {
    num_if::dict_entry(c.np, num_if::P_UOM_OFF, c.u) == p0
}

/// The stored relation of `sub` is the table itself.
pub proof fn lemma_sub_rel(db: Database)
    requires rows_ok(db),
    ensures crate::stores::sub_fy::declaration::stored_relations(db)[0] == sub_rel(db),
{
    let sr = sub_rel(db);
    let cols = crate::stores::sub_fy::declaration::stored_cols_t0();
    assert forall|i: int| 0 <= i < sr.len() implies #[trigger] proj_all(sr, cols)[i] == sr[i] by {
        assert(sub_row_ok(sr[i]));
        assert(proj(sr[i], cols) =~= sr[i]);
    }
    assert(proj_all(sr, cols) =~= sr);
}

// ------------------------------------------------------------------------------------------------ keys

/// The name dictionary of `sub`.
pub open spec fn name_count(sp: Seq<PartView>) -> int {
    text_count(sp, sub_if::P_NAME_DICT_OFF as int)
}

pub open spec fn name_entry(sp: Seq<PartView>, code: int) -> Seq<u8> {
    text_entry(u64_part(sp[sub_if::P_NAME_DICT_OFF as int]), u8_part(sp[sub_if::P_NAME_DICT_BYTES as int]), code)
}

/// The SQL group key named by a computed key: `(name, cik)` of the outer query, or `(cik)` of the subquery.
pub open spec fn kspec(sp: Seq<PartView>, k: (u64, u64), by_name: bool) -> Row {
    if by_name {
        seq![Val::Text(name_entry(sp, k.1 as int)), Val::Int(k.0 as int - 0x8000_0000)]
    } else {
        seq![Val::Int(k.0 as int - 0x8000_0000)]
    }
}

/// A computed key of a real filing: cik word below `2^32`, name code inside the dictionary.
pub open spec fn key_valid(sp: Seq<PartView>, k: (u64, u64), by_name: bool) -> bool {
    &&& k.0 < 0x1_0000_0000
    &&& by_name ==> 0 <= k.1 < name_count(sp)
}

/// The computed key of sub row `j`.
pub open spec fn ekey(c: ScanCtx, j: int, by_name: bool) -> (u64, u64) {
    (cik_word(c, j), if by_name { name_word(c, j) } else { 0 })
}

/// The SQL grouping and its key on `sub` rows.
pub open spec fn gsel(p0: Seq<u8>, p1: int, by_name: bool) -> QuerySpec {
    if by_name { g_top(p0, p1) } else { g_cik(p0, p1) }
}

pub open spec fn ksel(by_name: bool) -> spec_fn(Row) -> Row {
    if by_name { |s: Row| key_top_s(s) } else { |s: Row| key_cik_s(s) }
}

/// Distinct valid computed keys name distinct SQL keys.
pub proof fn lemma_kspec_inj(sp: Seq<PartView>, a: (u64, u64), b: (u64, u64), by_name: bool)
    requires sub_if::sub_layout_ok(sp), key_valid(sp, a, by_name), key_valid(sp, b, by_name),
        !by_name ==> a.1 == 0 && b.1 == 0,
    ensures (kspec(sp, a, by_name) == kspec(sp, b, by_name)) == (a == b),
{
    if kspec(sp, a, by_name) == kspec(sp, b, by_name) {
        if by_name {
            assert(kspec(sp, a, by_name)[0] == kspec(sp, b, by_name)[0]);
            assert(kspec(sp, a, by_name)[1] == kspec(sp, b, by_name)[1]);
            crate::stores::sub_fy::interface::common::text::lemma_dict_codes(u64_part(sp[sub_if::P_NAME_DICT_OFF as int]),
                u8_part(sp[sub_if::P_NAME_DICT_BYTES as int]), name_count(sp), a.1 as int, b.1 as int);
        } else {
            assert(kspec(sp, a, by_name)[0] == kspec(sp, b, by_name)[0]);
        }
    }
}

/// The relation row of sub row `j` holds what the scan read.
pub proof fn lemma_sub_row(db: Database, c: ScanCtx, j: int, by_name: bool)
    requires bound(db, c), ctx_ok(c), 0 <= j < n_sub(c),
    ensures
        j < sub_rel(db).len(),
        sub_rel(db)[j][0] == Val::Text(sub_if::adsh_bytes(c.sp, j)),
        ksel(by_name)(sub_rel(db)[j]) == kspec(c.sp, ekey(c, j, by_name), by_name),
        key_valid(c.sp, ekey(c, j, by_name), by_name),
        sq(c.p1, sub_rel(db)[j]) == fy_ok(c, j),
{
    lemma_sub_rel(db);
    let s = sub_rel(db)[j];
    assert(sub_if::sub_row_ok(c.sp, s, j));
    let cik = i32_part(c.sp[sub_if::P_CIK as int])[j];
    assert(s[1] == Val::Int(cik as int));
    assert(cik_word(c, j) as int == cik as int + 0x8000_0000);
    assert(u64_part(c.sp[sub_if::P_NAME_CODES as int])[j] < name_count(c.sp));
    if by_name {
        assert(ksel(by_name)(s) =~= kspec(c.sp, ekey(c, j, by_name), by_name));
    } else {
        assert(ksel(by_name)(s) =~= kspec(c.sp, ekey(c, j, by_name), by_name));
    }
}

// ------------------------------------------------------------------------------------------------ per-filing sums

/// The run's value, absolute mass and row count of a matched sub row (0 for an unmatched one).
pub open spec fn fval(c: ScanCtx, j: int, which: int) -> int {
    if !matched(c, j) {
        0
    } else if which == 0 {
        run_sum(c.np, the_run(c, j))
    } else if which == 1 {
        run_mass(c.np, the_run(c, j))
    } else {
        run_hi(c.np, the_run(c, j)) - run_lo(c.np, the_run(c, j))
    }
}

/// The weight of `nf` for `which`.
pub open spec fn wsel(which: int) -> spec_fn(Row) -> int {
    if which == 0 { w_val() } else if which == 1 { w_abs() } else { w_one() }
}

/// The per-filing sums of sub row `j` are its run's, or 0 without a run of `($1, adsh_j)`.
pub proof fn lemma_fsum_facts(db: Database, c: ScanCtx, p0: Seq<u8>, j: int, which: int)
    requires bound(db, c), ctx_ok(c), uom_is(c, p0), 0 <= j < n_sub(c), 0 <= which <= 2,
    ensures
        fsum(p0, num_rel(db), sub_rel(db)[j], wsel(which)) == fval(c, j, which),
        matched(c, j) ==> run_hi(c.np, the_run(c, j)) - run_lo(c.np, the_run(c, j)) > 0,
{
    let np = c.np;
    let a = sub_if::adsh_bytes(c.sp, j);
    lemma_sub_row(db, c, j, true);
    lemma_range(c);
    if matched(c, j) {
        let r = the_run(c, j);
        assert(run_match(c, j, r));
        assert(u64s_uom(np)[r] == c.u);
        assert(num_if::run_uom_of(np, r) == p0);
        lemma_fsum_run(db, np, p0, sub_rel(db)[j], a, r, wsel(which));
        lemma_run_weights(db, np, r);
    } else {
        assert forall|r: int| 0 <= r < num_if::run_count(np) implies !#[trigger] run_key_is(np, r, p0, a) by {
            if run_key_is(np, r, p0, a) {
                if c.r0 <= r < c.r1 {
                    assert(run_match(c, j, r));
                } else {
                    let ru = num_if::u64s(np, num_if::P_RUN_UOM);
                    assert(ru[r] < num_if::uom_count(np));
                    num_if::lemma_uom_runs(np, c.u);
                    assert(ru[r] != c.u);
                    crate::stores::num::interface::common::text::lemma_dict_codes(num_if::u64s(np, num_if::P_UOM_OFF),
                        crate::stores::num::interface::common::text::u8_part(np[num_if::P_UOM_BYTES as int]),
                        num_if::uom_count(np), ru[r] as int, c.u);
                }
            }
        }
        lemma_fsum_none(db, np, p0, sub_rel(db)[j], a, wsel(which));
    }
}

/// The run uom codes.
pub open spec fn u64s_uom(np: Seq<PartView>) -> Seq<u64> {
    num_if::u64s(np, num_if::P_RUN_UOM)
}

// ------------------------------------------------------------------------------------------------ accumulators

/// Term of sub row `j` in the accumulators of computed key `k`: the run value of a qualifying row with that key.
pub open spec fn tterm(c: ScanCtx, k: (u64, u64), by_name: bool, which: int) -> spec_fn(int) -> int {
    |j: int| if qualifies(c, j) && ekey(c, j, by_name) == k { fval(c, j, which) } else { 0int }
}

/// The toolkit accumulator of `which` (sum, absolute sum, count).
pub open spec fn acc(g: QuerySpec, xs: Seq<Row>, k: Row, which: int) -> int {
    if which == 0 { gsum(g, xs, k, 0) } else if which == 1 { gabs(g, xs, k, 0) } else { gcount(g, xs, k) as int }
}

/// The accumulators of the SQL key named by a computed key are range sums over the `sub` rows.
pub proof fn lemma_acc(db: Database, c: ScanCtx, p0: Seq<u8>, k: (u64, u64), by_name: bool, which: int)
    requires
        bound(db, c), ctx_ok(c), uom_is(c, p0), 0 <= which <= 2,
        key_valid(c.sp, k, by_name), !by_name ==> k.1 == 0,
    ensures
        acc(gsel(p0, c.p1, by_name), joined(db), kspec(c.sp, k, by_name), which)
            == rsum(0, n_sub(c), tterm(c, k, by_name, which)),
{
    let g = gsel(p0, c.p1, by_name);
    let ks = ksel(by_name);
    let kk = kspec(c.sp, k, by_name);
    let (nr, sr) = (num_rel(db), sub_rel(db));
    lemma_sub_rel(db);
    assert(sr.len() == n_sub(c));
    if by_name {
        lemma_top_key(p0, c.p1);
    } else {
        lemma_cik_key(p0, c.p1);
    }
    lemma_acc_by_sub(db, p0, c.p1, g, ks, kk);
    let st = sub_term(c.p1, p0, nr, ks, kk, wsel(which));
    lemma_sum_of_ssum(sr, st);
    lemma_ssum_index(sr, st);
    assert forall|j: int| 0 <= j < n_sub(c) implies st(#[trigger] sr[j]) == tterm(c, k, by_name, which)(j) by {
        lemma_sub_row(db, c, j, by_name);
        lemma_fsum_facts(db, c, p0, j, which);
        lemma_kspec_inj(c.sp, ekey(c, j, by_name), k, by_name);
    }
    lemma_rsum_ext(0, n_sub(c), |j: int| st(sr[j]), tterm(c, k, by_name, which));
}

// ------------------------------------------------------------------------------------------------ the scan's filings

/// Concatenated ranges of `filt`.
pub proof fn lemma_filt_append(c: ScanCtx, a: int, b: int, d: int)
    requires a <= b <= d,
    ensures filt(c, a, b) + filt(c, b, d) == filt(c, a, d),
    decreases d - b,
{
    if d == b {
        assert(filt(c, a, b) + filt(c, b, d) =~= filt(c, a, b));
    } else {
        lemma_filt_append(c, a, b, d - 1);
        lemma_filt_step(c, b, d - 1);
        lemma_filt_step(c, a, d - 1);
        let one = if qualifies(c, row_at(c, d - 1)) { seq![entry(c, row_at(c, d - 1))] } else { Seq::<Filing>::empty() };
        assert(filt(c, b, d) == filt(c, b, d - 1) + one);
        assert(filt(c, a, d) == filt(c, a, d - 1) + one);
        assert(filt(c, a, b) + (filt(c, b, d - 1) + one) =~= (filt(c, a, b) + filt(c, b, d - 1)) + one);
    }
}

/// Sums over `filt` are range sums over positions.
pub proof fn lemma_filt_ssum(c: ScanCtx, lo: int, hi: int, f: spec_fn(Filing) -> int)
    requires lo <= hi,
    ensures ssum(filt(c, lo, hi), f) == rsum(lo, hi, |p: int| if qualifies(c, row_at(c, p)) { f(entry(c, row_at(c, p))) } else { 0int }),
    decreases hi - lo,
{
    if hi > lo {
        lemma_filt_ssum(c, lo, hi - 1, f);
        lemma_filt_step(c, lo, hi - 1);
        let one = if qualifies(c, row_at(c, hi - 1)) { seq![entry(c, row_at(c, hi - 1))] } else { Seq::<Filing>::empty() };
        lemma_ssum_append(filt(c, lo, hi - 1), one, f);
        assert(ssum(Seq::<Filing>::empty(), f) == 0);
        if qualifies(c, row_at(c, hi - 1)) {
            assert(one.drop_last() =~= Seq::<Filing>::empty());
            assert(ssum(one, f) == ssum(one.drop_last(), f) + f(one.last()));
        } else {
            assert(ssum(one, f) == 0);
        }
    }
}

/// Elements of `filt` are entries of qualifying positions; entries of qualifying positions are in `filt`.
pub proof fn lemma_filt_members(c: ScanCtx, lo: int, hi: int)
    requires lo <= hi,
    ensures
        forall|e: Filing| #[trigger] filt(c, lo, hi).contains(e) ==>
            exists|p: int| lo <= p < hi && qualifies(c, row_at(c, p)) && #[trigger] entry(c, row_at(c, p)) == e,
        forall|p: int| lo <= p < hi && qualifies(c, row_at(c, p)) ==> #[trigger] filt(c, lo, hi).contains(entry(c, row_at(c, p))),
    decreases hi - lo,
{
    if hi > lo {
        lemma_filt_members(c, lo, hi - 1);
        lemma_filt_step(c, lo, hi - 1);
        let fi = filt(c, lo, hi - 1);
        let f = filt(c, lo, hi);
        assert forall|e: Filing| #[trigger] f.contains(e) implies
            exists|p: int| lo <= p < hi && qualifies(c, row_at(c, p)) && #[trigger] entry(c, row_at(c, p)) == e by {
            let i = choose|i: int| 0 <= i < f.len() && f[i] == e;
            if i < fi.len() {
                assert(fi[i] == e);
                assert(fi.contains(e));
            } else {
                assert(entry(c, row_at(c, hi - 1)) == e);
            }
        }
        assert forall|p: int| lo <= p < hi && qualifies(c, row_at(c, p)) implies #[trigger] f.contains(entry(c, row_at(c, p))) by {
            if p < hi - 1 {
                assert(fi.contains(entry(c, row_at(c, p))));
                let i = choose|i: int| 0 <= i < fi.len() && fi[i] == entry(c, row_at(c, p));
                assert(f[i] == fi[i]);
            } else {
                assert(f[fi.len() as int] == entry(c, row_at(c, p)));
            }
        }
    }
}

/// The entry of a qualifying, not big sub row carries its run's exact sum and mass.
pub proof fn lemma_entry_values(c: ScanCtx, j: int)
    requires qualifies(c, j), !big(c, j),
    ensures
        entry(c, j).sum as int == fval(c, j, 0),
        entry(c, j).mass as int == fval(c, j, 1),
        gkey(entry(c, j), true) == ekey(c, j, true),
        gkey(entry(c, j), false) == ekey(c, j, false),
{
    let r = the_run(c, j);
    let (lo, hi) = (run_lo(c.np, r), run_hi(c.np, r));
    assert forall|i: int| lo <= i < hi implies #[trigger] abs_term_at(c.np)(i) >= val_term(c.np)(i)
        && abs_term_at(c.np)(i) >= -val_term(c.np)(i) by {}
    lemma_rsum_abs(lo, hi, val_term(c.np), abs_term_at(c.np));
    assert forall|i: int| lo <= i < hi implies #[trigger] abs_term_at(c.np)(i) >= 0 by {}
    lemma_rsum_nonneg(lo, hi, abs_term_at(c.np));
}

/// A sum over the scan's filings of a key's terms is the range sum of the key's run values over `sub` rows.
pub proof fn lemma_filt_total(c: ScanCtx, k: (u64, u64), by_name: bool, which: int)
    requires
        ctx_ok(c), 0 <= which <= 1,
        none_big(c, 0, n_sub(c)),
    ensures ({
        let f = if which == 0 { sum_f(k, by_name) } else { mass_f(k, by_name) };
        ssum(filt(c, 0, n_sub(c)), f) == rsum(0, n_sub(c), tterm(c, k, by_name, which))
    }),
{
    let f = if which == 0 { sum_f(k, by_name) } else { mass_f(k, by_name) };
    let n = n_sub(c);
    lemma_filt_ssum(c, 0, n, f);
    let h = tterm(c, k, by_name, which);
    let byp = |p: int| if qualifies(c, row_at(c, p)) { f(entry(c, row_at(c, p))) } else { 0int };
    crate::stores::sub_fy::interface::common::perm::lemma_permutation_facts(sub_if::fy_order(c.sp), n as nat);
    assert forall|p: int| 0 <= p < n implies #[trigger] byp(p) == h(row_at(c, p) as u64 as int) by {
        let j = row_at(c, p);
        assert(0 <= j < n);
        assert(j as u64 as int == j);
        if qualifies(c, j) {
            assert(!big(c, row_at(c, p)));
            lemma_entry_values(c, j);
        }
    }
    lemma_rsum_ext(0, n, byp, |p: int| h(row_at(c, p) as u64 as int));
    let ao = sub_if::fy_order(c.sp);
    assert(ao.to_multiset() == positions(n as nat).to_multiset()) by {
        assert(positions(n as nat) =~= crate::stores::sub_fy::interface::common::perm::ident(n as nat));
    }
    lemma_rsum_permuted(ao, n as nat, h);
    lemma_rsum_ext(0, n, |p: int| h(row_at(c, p) as u64 as int), |t: int| h(ao[t] as int));
}

} // verus!
