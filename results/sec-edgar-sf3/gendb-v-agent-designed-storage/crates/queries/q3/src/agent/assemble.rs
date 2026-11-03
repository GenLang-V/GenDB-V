//! The computed groups are the SQL groups, for every database bound to the storages.
//!
//! `run_ok` collects what the computation established before grouping: the scan context, no big filing, and the
//! sorted list `l` of the scan's filings. A pass's groups (`groups_ok`) then have: sums and masses equal to the
//! toolkit accumulators of their SQL keys (`lemma_group_acc`), and the SQL group keys are exactly the computed
//! keys named by `kspec` (`lemma_keys_match`), without duplicates on either side (`lemma_keys_multiset`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::link::query::{QuerySpec, gsum, gabs, gcount, gkeys, hit, lemma_gkeys, lemma_nodup_same_multiset};
use crate::link::expr::i128_max;
use crate::stores::sub_fy::interface as sub_if;
use crate::stores::sub_fy::interface::common::text::u64_part;
use crate::stores::sub_fy::interface::common::cols::i32_part;
use crate::stores::sub_fy::interface::common::perm::{lemma_permutation_facts, position_of};
use crate::agent::common::sort::{Filing, FilingOrder, SortOrder, sorted_by, filing_le};
use crate::agent::common::sums::*;
use crate::agent::nf::*;
use crate::agent::scan::*;
use crate::agent::groups::*;
use crate::agent::link::*;
use crate::agent::eval::sum_caps;

verus! {

broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms};

/// What the computation established before grouping.
pub open spec fn run_ok(c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>) -> bool {
    &&& ctx_ok(c)
    &&& uom_is(c, p0)
    &&& none_big(c, 0, n_sub(c))
    &&& l.to_multiset() == filt(c, 0, n_sub(c)).to_multiset()
    &&& sorted_by(FilingOrder {}, l)
}

/// Two qualifying positions of the fiscal-year order have the same `fy`, so their entries are in `(cik, name)`
/// order.
pub proof fn lemma_entries_ordered(c: ScanCtx, p: int, q: int)
    requires ctx_ok(c), 0 <= p < q < n_sub(c), qualifies(c, row_at(c, p)), qualifies(c, row_at(c, q)),
    ensures filing_le(entry(c, row_at(c, p)), entry(c, row_at(c, q))),
{
    let ord = sub_if::fy_order(c.sp);
    lemma_permutation_facts(ord, n_sub(c) as nat);
    assert(sub_if::key_le(sub_if::row_key(c.sp, ord[p] as int), sub_if::row_key(c.sp, ord[q] as int)));
    assert(sub_if::fy_word(c.sp, row_at(c, p)) == sub_if::fy_word(c.sp, row_at(c, q)));
}

/// The scan's filings are sorted by `(cik, name)`: the fiscal-year order lists the rows of one `fy` by cik,
/// name code and row.
pub proof fn lemma_filt_sorted(c: ScanCtx, hi: int)
    requires ctx_ok(c), 0 <= hi <= n_sub(c),
    ensures sorted_by(FilingOrder {}, filt(c, 0, hi)),
    decreases hi,
{
    if hi > 0 {
        lemma_filt_sorted(c, hi - 1);
        lemma_filt_step(c, 0, hi - 1);
        let s = filt(c, 0, hi - 1);
        if qualifies(c, row_at(c, hi - 1)) {
            let x = entry(c, row_at(c, hi - 1));
            let t = s.push(x);
            assert(filt(c, 0, hi) =~= t);
            lemma_filt_members(c, 0, hi - 1);
            assert forall|i: int, j: int| 0 <= i < j < t.len() implies FilingOrder {}.le(#[trigger] t[i], #[trigger] t[j]) by {
                if j == s.len() {
                    assert(s.contains(s[i]));
                    let p = choose|p: int| 0 <= p < hi - 1 && qualifies(c, row_at(c, p)) && #[trigger] entry(c, row_at(c, p)) == s[i];
                    lemma_entries_ordered(c, p, hi - 1);
                } else {
                    assert(t[i] == s[i] && t[j] == s[j]);
                }
            }
        } else {
            assert(filt(c, 0, hi) =~= s);
        }
    }
}

/// The computed key of group `h`.
pub open spec fn hkey(g: Groups, h: int, by_name: bool) -> (u64, u64) {
    gk(g.cik@, g.name@, h, by_name)
}

/// The SQL keys of the computed groups.
pub open spec fn key_list(sp: Seq<crate::gendb_entry::layout::PartView>, g: Groups, by_name: bool) -> Seq<Row> {
    Seq::new(g.sum@.len(), |h: int| kspec(sp, hkey(g, h, by_name), by_name))
}

/// A filing of the sorted list is an entry of a qualifying sub row.
pub proof fn lemma_l_member(c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>, t: int)
    requires run_ok(c, p0, l), 0 <= t < l.len(),
    ensures exists|p: int| 0 <= p < n_sub(c) && qualifies(c, row_at(c, p)) && #[trigger] entry(c, row_at(c, p)) == l[t],
{
    assert(l.contains(l[t]));
    assert(l.to_multiset().count(l[t]) > 0);
    assert(filt(c, 0, n_sub(c)).contains(l[t]));
    lemma_filt_members(c, 0, n_sub(c));
}

/// The entry of a qualifying sub row is in the sorted list.
pub proof fn lemma_l_has(c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>, j: int)
    requires run_ok(c, p0, l), 0 <= j < n_sub(c), qualifies(c, j),
    ensures l.contains(entry(c, j)),
{
    let n = n_sub(c);
    lemma_permutation_facts(sub_if::fy_order(c.sp), n as nat);
    let p = position_of(sub_if::fy_order(c.sp), j);
    assert(row_at(c, p) == j);
    lemma_filt_members(c, 0, n);
    assert(filt(c, 0, n).contains(entry(c, j)));
    assert(filt(c, 0, n).to_multiset().count(entry(c, j)) > 0);
}

/// Each filing's sum is bounded by its mass, which fits `i128`.
pub proof fn lemma_filings_ok(c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>)
    requires run_ok(c, p0, l),
    ensures filings_ok(l),
{
    assert forall|t: int| 0 <= t < l.len() implies {
        &&& (#[trigger] l[t]).mass <= i128::MAX as u128
        &&& l[t].sum as int <= l[t].mass as int
        &&& -(l[t].sum as int) <= l[t].mass as int
    } by {
        lemma_l_member(c, p0, l, t);
        let p = choose|p: int| 0 <= p < n_sub(c) && qualifies(c, row_at(c, p)) && #[trigger] entry(c, row_at(c, p)) == l[t];
        let j = row_at(c, p);
        assert(!big(c, row_at(c, p)));
        lemma_entry_values(c, j);
        let r = the_run(c, j);
        assert forall|i: int| crate::agent::numlink::run_lo(c.np, r) <= i < crate::agent::numlink::run_hi(c.np, r)
            implies #[trigger] crate::agent::numlink::abs_term_at(c.np)(i) >= crate::agent::numlink::val_term(c.np)(i)
            && crate::agent::numlink::abs_term_at(c.np)(i) >= -crate::agent::numlink::val_term(c.np)(i) by {}
        lemma_rsum_abs(crate::agent::numlink::run_lo(c.np, r), crate::agent::numlink::run_hi(c.np, r),
            crate::agent::numlink::val_term(c.np), crate::agent::numlink::abs_term_at(c.np));
    }
}

/// The computed key of a qualifying sub row is valid.
pub proof fn lemma_ekey_valid(c: ScanCtx, j: int, by_name: bool)
    requires ctx_ok(c), 0 <= j < n_sub(c),
    ensures key_valid(c.sp, ekey(c, j, by_name), by_name), !by_name ==> ekey(c, j, by_name).1 == 0,
{
    assert(u64_part(c.sp[sub_if::P_NAME_CODES as int])[j] < name_count(c.sp));
    let cik = i32_part(c.sp[sub_if::P_CIK as int])[j];
    assert(cik_word(c, j) as int == cik as int + 0x8000_0000);
}

/// A group's key is the key of one of the list's filings, hence valid.
pub proof fn lemma_hkey_valid(c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>, g: Groups, by_name: bool, h: int)
    requires run_ok(c, p0, l), groups_ok(g, l, by_name), 0 <= h < g.sum@.len(),
    ensures
        key_valid(c.sp, hkey(g, h, by_name), by_name),
        !by_name ==> hkey(g, h, by_name).1 == 0,
        exists|j: int| 0 <= j < n_sub(c) && qualifies(c, j) && #[trigger] ekey(c, j, by_name) == hkey(g, h, by_name),
{
    reveal(gf_wit);
    let t = choose|i: int| 0 <= i < l.len() && gkey(#[trigger] l[i], by_name) == gk(g.cik@, g.name@, h, by_name);
    lemma_l_member(c, p0, l, t);
    let p = choose|p: int| 0 <= p < n_sub(c) && qualifies(c, row_at(c, p)) && #[trigger] entry(c, row_at(c, p)) == l[t];
    let j = row_at(c, p);
    lemma_permutation_facts(sub_if::fy_order(c.sp), n_sub(c) as nat);
    lemma_ekey_valid(c, j, by_name);
    assert(ekey(c, j, by_name) == hkey(g, h, by_name));
}

/// A group's sum and mass are the toolkit accumulators of its SQL key.
pub proof fn lemma_group_acc(db: Database, c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>, g: Groups, by_name: bool, h: int)
    requires bound(db, c), run_ok(c, p0, l), groups_ok(g, l, by_name), 0 <= h < g.sum@.len(),
    ensures
        g.sum@[h] as int == gsum(gsel(p0, c.p1, by_name), joined(db), kspec(c.sp, hkey(g, h, by_name), by_name), 0),
        g.mass@[h] as int == gabs(gsel(p0, c.p1, by_name), joined(db), kspec(c.sp, hkey(g, h, by_name), by_name), 0),
{
    reveal(gf_vals);
    let k = hkey(g, h, by_name);
    lemma_hkey_valid(c, p0, l, g, by_name, h);
    lemma_ssum_perm(l, filt(c, 0, n_sub(c)), sum_f(k, by_name));
    lemma_ssum_perm(l, filt(c, 0, n_sub(c)), mass_f(k, by_name));
    lemma_filt_total(c, k, by_name, 0);
    lemma_filt_total(c, k, by_name, 1);
    lemma_acc(db, c, p0, k, by_name, 0);
    lemma_acc(db, c, p0, k, by_name, 1);
}

/// A sum of nonnegative terms that is positive has a positive term.
proof fn lemma_rsum_pos(lo: int, hi: int, f: spec_fn(int) -> int) -> (i: int)
    requires rsum(lo, hi, f) != 0,
    ensures lo <= i < hi, f(i) != 0,
{
    if forall|i: int| lo <= i < hi ==> #[trigger] f(i) == 0 {
        lemma_rsum_zero(lo, hi, f);
        assert(false);
        lo
    } else {
        choose|i: int| lo <= i < hi && #[trigger] f(i) != 0
    }
}

/// The SQL group keys are exactly the SQL keys of the computed groups.
pub proof fn lemma_keys_match(db: Database, c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>, g: Groups, by_name: bool)
    requires bound(db, c), run_ok(c, p0, l), groups_ok(g, l, by_name),
    ensures forall|kk: Row| #[trigger] gkeys(gsel(p0, c.p1, by_name), joined(db)).contains(kk)
        <==> key_list(c.sp, g, by_name).contains(kk),
{
    let gq = gsel(p0, c.p1, by_name);
    let xs = joined(db);
    let n = n_sub(c);
    lemma_gkeys(gq, xs);
    assert forall|kk: Row| #[trigger] gkeys(gq, xs).contains(kk) <==> key_list(c.sp, g, by_name).contains(kk) by {
        if key_list(c.sp, g, by_name).contains(kk) {
            let h = choose|h: int| 0 <= h < g.sum@.len() && key_list(c.sp, g, by_name)[h] == kk;
            let k = hkey(g, h, by_name);
            lemma_hkey_valid(c, p0, l, g, by_name, h);
            let j = choose|j: int| 0 <= j < n_sub(c) && qualifies(c, j) && #[trigger] ekey(c, j, by_name) == k;
            lemma_acc(db, c, p0, k, by_name, 2);
            lemma_fsum_facts(db, c, p0, j, 2);
            let f = tterm(c, k, by_name, 2);
            assert forall|i: int| 0 <= i < n implies #[trigger] f(i) >= 0 by {
                if qualifies(c, i) && ekey(c, i, by_name) == k {
                    lemma_fsum_facts(db, c, p0, i, 2);
                }
            }
            lemma_rsum_nonneg(0, n, f);
            assert(f(j) > 0);
            assert(gcount(gq, xs, kk) > 0);
        }
        if gkeys(gq, xs).contains(kk) {
            assert(gcount(gq, xs, kk) > 0);
            let ks = ksel(by_name);
            if by_name {
                lemma_top_key(p0, c.p1);
            } else {
                lemma_cik_key(p0, c.p1);
            }
            lemma_acc_by_sub(db, p0, c.p1, gq, ks, kk);
            let (nr, sr) = (num_rel(db), sub_rel(db));
            lemma_sub_rel(db);
            let st = sub_term(c.p1, p0, nr, ks, kk, w_one());
            crate::agent::numlink::lemma_sum_of_ssum(sr, st);
            lemma_ssum_index(sr, st);
            let j = lemma_rsum_pos(0, sr.len() as int, |j: int| st(sr[j]));
            lemma_sub_row(db, c, j, by_name);
            lemma_fsum_facts(db, c, p0, j, 2);
            assert(qualifies(c, j));
            lemma_l_has(c, p0, l, j);
            let t = choose|t: int| 0 <= t < l.len() && l[t] == entry(c, j);
            reveal(gf_cover);
            let h = choose|h: int| 0 <= h < g.sum@.len() && #[trigger] gk(g.cik@, g.name@, h, by_name) == gkey(l[t], by_name);
            assert(gkey(entry(c, j), by_name) == ekey(c, j, by_name));
            assert(key_list(c.sp, g, by_name)[h] == kk);
        }
    }
}

/// Both key sequences are free of duplicates and have the same elements: the same multiset.
pub proof fn lemma_keys_multiset(db: Database, c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>, g: Groups, by_name: bool)
    requires bound(db, c), run_ok(c, p0, l), groups_ok(g, l, by_name),
    ensures
        gkeys(gsel(p0, c.p1, by_name), joined(db)).to_multiset() == key_list(c.sp, g, by_name).to_multiset(),
        gkeys(gsel(p0, c.p1, by_name), joined(db)).len() == g.sum@.len(),
{
    let kl = key_list(c.sp, g, by_name);
    lemma_keys_match(db, c, p0, l, g, by_name);
    lemma_gkeys(gsel(p0, c.p1, by_name), joined(db));
    reveal(gf_sorted);
    assert forall|a: int, b: int| 0 <= a < kl.len() && 0 <= b < kl.len() && a != b implies kl[a] != kl[b] by {
        lemma_hkey_valid(c, p0, l, g, by_name, a);
        lemma_hkey_valid(c, p0, l, g, by_name, b);
        lemma_kspec_inj(c.sp, hkey(g, a, by_name), hkey(g, b, by_name), by_name);
        if a < b {
            assert(key_lt(gk(g.cik@, g.name@, a, by_name), gk(g.cik@, g.name@, b, by_name)));
        } else {
            assert(key_lt(gk(g.cik@, g.name@, b, by_name), gk(g.cik@, g.name@, a, by_name)));
        }
    }
    assert(kl.no_duplicates());
    lemma_nodup_same_multiset(gkeys(gsel(p0, c.p1, by_name), joined(db)), kl);
    assert(gkeys(gsel(p0, c.p1, by_name), joined(db)).len() == gkeys(gsel(p0, c.p1, by_name), joined(db)).to_multiset().len());
    assert(kl.len() == kl.to_multiset().len());
}

/// Every SQL group of a computed pass has an exact sum inside `i128`.
pub proof fn lemma_sum_caps(db: Database, c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>, g: Groups, by_name: bool)
    requires bound(db, c), run_ok(c, p0, l), groups_ok(g, l, by_name),
    ensures sum_caps(gsel(p0, c.p1, by_name), joined(db)),
{
    lemma_keys_match(db, c, p0, l, g, by_name);
    assert forall|kk: Row| #[trigger] gkeys(gsel(p0, c.p1, by_name), joined(db)).contains(kk) implies
        -i128_max() <= gsum(gsel(p0, c.p1, by_name), joined(db), kk, 0) <= i128_max() by {
        let h = choose|h: int| 0 <= h < g.sum@.len() && key_list(c.sp, g, by_name)[h] == kk;
        lemma_group_acc(db, c, p0, l, g, by_name, h);
        reveal(gf_vals);
        assert(g.sum@[h] as int <= g.mass@[h] as int && -(g.sum@[h] as int) <= g.mass@[h] as int);
        assert(g.mass@[h] <= i128::MAX as u128);
    }
}

} // verus!
