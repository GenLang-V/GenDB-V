//! The plan's normal form: the statement's kept FROM rows are determined by their lineitem row.
//!
//! A lineitem row `c` is a *candidate* when some index tuple `(i, j, c, d, e, f)` satisfies the WHERE (`cand`);
//! the primary keys of orders, customer, supplier, nation and region make that tuple unique (`lemma_tuple_unique`),
//! so the kept rows are, as a bag, the candidates' rows (`lemma_kept_bag`). Hence each group accumulator of the
//! normal form over the FROM is a sum over lineitem rows (`lemma_group_sums`): row `c` adds its revenue
//! `l_extendedprice * (100 - l_discount)` (scale 4) to the group named by its nation, when it is a candidate.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::spec::relation::*;
use crate::link::join::*;
use crate::link::query::*;
use crate::gendb_entry::stores::StoresView;
use crate::agent::model::*;
use crate::agent::sem_from::*;
use crate::agent::sem_pred::*;
use crate::agent::sem_body::*;
use crate::agent::common::relations::*;

verus! {

/// Lineitem row `c` has a FROM row satisfying the WHERE.
pub open spec fn cand(sv: StoresView, rp: Seq<u8>, pd: int, t: int, c: int) -> bool {
    exists|i: int, j: int, d: int, e: int, f: int| #[trigger] in6(sv, i, j, c, d, e, f) && qual6(sv, rp, pd, t, i, j, c, d, e, f)
}

/// The FROM tuple of candidate `c`: customer, orders, supplier, nation and region rows.
pub open spec fn ctuple(sv: StoresView, rp: Seq<u8>, pd: int, t: int, c: int) -> (int, int, int, int, int) {
    choose|i: int, j: int, d: int, e: int, f: int| #[trigger] in6(sv, i, j, c, d, e, f) && qual6(sv, rp, pd, t, i, j, c, d, e, f)
}

/// The kept FROM row of candidate `c`.
pub open spec fn cand_row(sv: StoresView, rp: Seq<u8>, pd: int, t: int, c: int) -> Row {
    let u = ctuple(sv, rp, pd, t, c);
    row6(sv, u.0, u.1, c, u.2, u.3, u.4)
}

/// The nation row of candidate `c`.
pub open spec fn cnation(sv: StoresView, rp: Seq<u8>, pd: int, t: int, c: int) -> int {
    ctuple(sv, rp, pd, t, c).3
}

/// The revenue coefficient (scale 4) of lineitem row `c`.
pub open spec fn crev(sv: StoresView, c: int) -> int {
    l_ext(sv)[c] as int * (100 - l_disc(sv)[c] as int)
}

/// Contribution of lineitem row `c` to the group with key `k`: its revenue when it is a candidate whose nation's
/// name is the key.
pub open spec fn cterm(sv: StoresView, rp: Seq<u8>, pd: int, t: int, k: Row, c: int) -> int {
    if cand(sv, rp, pd, t, c) && seq![Val::Text(n_name(sv, cnation(sv, rp, pd, t, c)))] == k { crev(sv, c) } else { 0 }
}

/// Sums over the lineitem rows `[0, n)`: revenue, row count and absolute revenue of the group with key `k`.
pub open spec fn csum(sv: StoresView, rp: Seq<u8>, pd: int, t: int, k: Row, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else { csum(sv, rp, pd, t, k, n - 1) + cterm(sv, rp, pd, t, k, n - 1) }
}

pub open spec fn ccount(sv: StoresView, rp: Seq<u8>, pd: int, t: int, k: Row, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else {
        ccount(sv, rp, pd, t, k, n - 1)
            + if cand(sv, rp, pd, t, n - 1) && seq![Val::Text(n_name(sv, cnation(sv, rp, pd, t, n - 1)))] == k { 1int } else { 0int }
    }
}

pub open spec fn cabs(sv: StoresView, rp: Seq<u8>, pd: int, t: int, k: Row, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else { cabs(sv, rp, pd, t, k, n - 1) + abs(cterm(sv, rp, pd, t, k, n - 1)) }
}

// ------------------------------------------------------------------------------------------ candidates

/// A FROM tuple satisfying the WHERE is determined by its lineitem row (primary keys).
pub proof fn lemma_tuple_unique(sv: StoresView, rp: Seq<u8>, pd: int, t: int,
    i: int, j: int, c: int, d: int, e: int, f: int, i2: int, j2: int, d2: int, e2: int, f2: int)
    requires
        stores_wf(sv), keys_ok(sv),
        in6(sv, i, j, c, d, e, f), in6(sv, i2, j2, c, d2, e2, f2),
        qual6(sv, rp, pd, t, i, j, c, d, e, f),
        qual6(sv, rp, pd, t, i2, j2, c, d2, e2, f2),
    ensures i == i2, j == j2, d == d2, e == e2, f == f2,
{
    assert(o_ok(sv)[j] == o_ok(sv)[j2]);
    assert(s_sk(sv)[d] == s_sk(sv)[d2]);
    assert(c_ck(sv)[i] == c_ck(sv)[i2]);
    assert(n_nk(sv)[e] == n_nk(sv)[e2]);
    assert(r_rk(sv)[f] == r_rk(sv)[f2]);
}

/// A candidate's tuple satisfies the WHERE, and every satisfying tuple of `c` is that tuple.
pub proof fn lemma_ctuple(sv: StoresView, rp: Seq<u8>, pd: int, t: int, c: int)
    requires stores_wf(sv), keys_ok(sv), cand(sv, rp, pd, t, c),
    ensures
        ({ let u = ctuple(sv, rp, pd, t, c);
            in6(sv, u.0, u.1, c, u.2, u.3, u.4) && qual6(sv, rp, pd, t, u.0, u.1, c, u.2, u.3, u.4) }),
        forall|i: int, j: int, d: int, e: int, f: int| #[trigger] in6(sv, i, j, c, d, e, f) && qual6(sv, rp, pd, t, i, j, c, d, e, f)
            ==> ctuple(sv, rp, pd, t, c) == (i, j, d, e, f),
{
    let u = ctuple(sv, rp, pd, t, c);
    assert forall|i: int, j: int, d: int, e: int, f: int| #[trigger] in6(sv, i, j, c, d, e, f) && qual6(sv, rp, pd, t, i, j, c, d, e, f)
        implies ctuple(sv, rp, pd, t, c) == (i, j, d, e, f) by {
        lemma_tuple_unique(sv, rp, pd, t, u.0, u.1, c, u.2, u.3, u.4, i, j, d, e, f);
    }
}

/// The candidates' rows of lineitem rows `[0, n)`, in lineitem order.
pub open spec fn crows(sv: StoresView, rp: Seq<u8>, pd: int, t: int, n: int) -> Seq<Row>
    decreases n,
{
    if n <= 0 {
        Seq::empty()
    } else if cand(sv, rp, pd, t, n - 1) {
        crows(sv, rp, pd, t, n - 1).push(cand_row(sv, rp, pd, t, n - 1))
    } else {
        crows(sv, rp, pd, t, n - 1)
    }
}

/// The rows of `crows(n)` are the candidates' rows of `[0, n)`, pairwise different.
proof fn lemma_crows(sv: StoresView, rp: Seq<u8>, pd: int, t: int, n: int)
    requires stores_wf(sv), keys_ok(sv), 0 <= n <= nl(sv),
    ensures
        crows(sv, rp, pd, t, n).no_duplicates(),
        forall|x: Row| crows(sv, rp, pd, t, n).contains(x) <==>
            exists|c: int| 0 <= c < n && cand(sv, rp, pd, t, c) && x == #[trigger] cand_row(sv, rp, pd, t, c),
    decreases n,
{
    let s = crows(sv, rp, pd, t, n);
    if n > 0 {
        lemma_crows(sv, rp, pd, t, n - 1);
        let si = crows(sv, rp, pd, t, n - 1);
        if cand(sv, rp, pd, t, n - 1) {
            let x = cand_row(sv, rp, pd, t, n - 1);
            lemma_ctuple(sv, rp, pd, t, n - 1);
            let u = ctuple(sv, rp, pd, t, n - 1);
            lemma_row6(sv, u.0, u.1, n - 1, u.2, u.3, u.4);
            assert(!si.contains(x)) by {
                if si.contains(x) {
                    let c = choose|c: int| 0 <= c < n - 1 && cand(sv, rp, pd, t, c) && x == #[trigger] cand_row(sv, rp, pd, t, c);
                    lemma_ctuple(sv, rp, pd, t, c);
                    let w = ctuple(sv, rp, pd, t, c);
                    lemma_row6(sv, w.0, w.1, c, w.2, w.3, w.4);
                    assert(x[17] == cand_row(sv, rp, pd, t, c)[17] && x[20] == cand_row(sv, rp, pd, t, c)[20]);
                    assert(l_ok(sv)[c] == l_ok(sv)[n - 1] && l_ln(sv)[c] == l_ln(sv)[n - 1]);
                }
            }
            assert(s == si.push(x));
            assert(s.no_duplicates()) by {
                assert forall|a: int, b: int| 0 <= a < s.len() && 0 <= b < s.len() && a != b implies s[a] != s[b] by {
                    if a < si.len() && b < si.len() {
                        assert(s[a] == si[a] && s[b] == si[b]);
                    } else if a < si.len() {
                        assert(s[a] == si[a]);
                        assert(si.contains(si[a]));
                    } else {
                        assert(s[b] == si[b]);
                        assert(si.contains(si[b]));
                    }
                }
            }
            assert forall|y: Row| s.contains(y) <==>
                exists|c: int| 0 <= c < n && cand(sv, rp, pd, t, c) && y == #[trigger] cand_row(sv, rp, pd, t, c) by {
                if s.contains(y) {
                    let m = choose|m: int| 0 <= m < s.len() && s[m] == y;
                    if m < si.len() {
                        assert(si.contains(y));
                    } else {
                        assert(y == cand_row(sv, rp, pd, t, n - 1));
                    }
                }
                if exists|c: int| 0 <= c < n && cand(sv, rp, pd, t, c) && y == #[trigger] cand_row(sv, rp, pd, t, c) {
                    let c = choose|c: int| 0 <= c < n && cand(sv, rp, pd, t, c) && y == #[trigger] cand_row(sv, rp, pd, t, c);
                    if c < n - 1 {
                        assert(si.contains(y));
                        let m = choose|m: int| 0 <= m < si.len() && si[m] == y;
                        assert(s[m] == y);
                    } else {
                        assert(s[si.len() as int] == y);
                    }
                }
            }
        } else {
            assert(s == si);
            assert forall|y: Row| s.contains(y) <==>
                exists|c: int| 0 <= c < n && cand(sv, rp, pd, t, c) && y == #[trigger] cand_row(sv, rp, pd, t, c) by {
                if exists|c: int| 0 <= c < n && cand(sv, rp, pd, t, c) && y == #[trigger] cand_row(sv, rp, pd, t, c) {
                    let c = choose|c: int| 0 <= c < n && cand(sv, rp, pd, t, c) && y == #[trigger] cand_row(sv, rp, pd, t, c);
                    assert(c < n - 1);
                }
            }
        }
    } else {
        assert(s =~= Seq::<Row>::empty());
    }
}

/// The normal form's condition as a closure.
pub open spec fn qual_fn(rp: Seq<u8>, pd: int, t: int) -> spec_fn(Row) -> bool {
    q5_spec(rp, pd, t).qual
}

/// The kept rows are, as a bag, the candidates' rows.
pub proof fn lemma_kept_bag(sv: StoresView, rp: Seq<u8>, pd: int, t: int)
    requires stores_wf(sv), keys_ok(sv),
    ensures keep(from6(sv), qual_fn(rp, pd, t)).to_multiset() == crows(sv, rp, pd, t, nl(sv) as int).to_multiset(),
{
    let f = qual_fn(rp, pd, t);
    let kept = keep(from6(sv), f);
    let g = crows(sv, rp, pd, t, nl(sv) as int);
    lemma_from6_nodup(sv);
    lemma_keep_nodup(from6(sv), f);
    lemma_crows(sv, rp, pd, t, nl(sv) as int);
    assert forall|x: Row| kept.contains(x) <==> g.contains(x) by {
        lemma_keep_contains(from6(sv), f, x);
        lemma_from6_contains(sv, x);
        if kept.contains(x) {
            let (i, j, c, d, e, ff) = choose|i: int, j: int, c: int, d: int, e: int, ff: int|
                in6(sv, i, j, c, d, e, ff) && x == #[trigger] row6(sv, i, j, c, d, e, ff);
            lemma_qual_row6(sv, rp, pd, t, i, j, c, d, e, ff);
            assert(qual6(sv, rp, pd, t, i, j, c, d, e, ff));
            assert(cand(sv, rp, pd, t, c));
            lemma_ctuple(sv, rp, pd, t, c);
            assert(x == cand_row(sv, rp, pd, t, c));
        }
        if g.contains(x) {
            let c = choose|c: int| 0 <= c < nl(sv) && cand(sv, rp, pd, t, c) && x == #[trigger] cand_row(sv, rp, pd, t, c);
            lemma_ctuple(sv, rp, pd, t, c);
            let u = ctuple(sv, rp, pd, t, c);
            lemma_qual_row6(sv, rp, pd, t, u.0, u.1, c, u.2, u.3, u.4);
            assert(from6(sv).contains(x));
        }
    }
    lemma_nodup_same_multiset(kept, g);
}

// ------------------------------------------------------------------------------------------ group sums

/// On a candidate's row, the normal form's per-row terms are the candidate's.
proof fn lemma_cand_terms(sv: StoresView, rp: Seq<u8>, pd: int, t: int, k: Row, c: int)
    requires stores_wf(sv), keys_ok(sv), 0 <= c < nl(sv), cand(sv, rp, pd, t, c),
    ensures ({
        let g = q5_spec(rp, pd, t);
        let x = cand_row(sv, rp, pd, t, c);
        &&& (sum_term(g, k, 0))(x) == cterm(sv, rp, pd, t, k, c)
        &&& (count_term(g, k))(x) == (if seq![Val::Text(n_name(sv, cnation(sv, rp, pd, t, c)))] == k { 1int } else { 0int })
        &&& (abs_term(g, k, 0))(x) == abs(cterm(sv, rp, pd, t, k, c))
    }),
{
    lemma_ctuple(sv, rp, pd, t, c);
    let u = ctuple(sv, rp, pd, t, c);
    lemma_row6(sv, u.0, u.1, c, u.2, u.3, u.4);
    lemma_qual_row6(sv, rp, pd, t, u.0, u.1, c, u.2, u.3, u.4);
    let g = q5_spec(rp, pd, t);
    let x = cand_row(sv, rp, pd, t, c);
    assert((g.qual)(x));
    assert((g.key)(x) =~= seq![Val::Text(n_name(sv, cnation(sv, rp, pd, t, c)))]);
    assert(rev_of(x) == crev(sv, c));
}

/// The sums of the per-row terms over `crows(n)` are the lineitem sums over `[0, n)`.
proof fn lemma_crows_sums(sv: StoresView, rp: Seq<u8>, pd: int, t: int, k: Row, n: int)
    requires stores_wf(sv), keys_ok(sv), 0 <= n <= nl(sv),
    ensures
        sum_of(crows(sv, rp, pd, t, n), sum_term(q5_spec(rp, pd, t), k, 0)) == csum(sv, rp, pd, t, k, n),
        sum_of(crows(sv, rp, pd, t, n), count_term(q5_spec(rp, pd, t), k)) == ccount(sv, rp, pd, t, k, n),
        sum_of(crows(sv, rp, pd, t, n), abs_term(q5_spec(rp, pd, t), k, 0)) == cabs(sv, rp, pd, t, k, n),
    decreases n,
{
    if n > 0 {
        lemma_crows_sums(sv, rp, pd, t, k, n - 1);
        let si = crows(sv, rp, pd, t, n - 1);
        if cand(sv, rp, pd, t, n - 1) {
            let x = cand_row(sv, rp, pd, t, n - 1);
            lemma_cand_terms(sv, rp, pd, t, k, n - 1);
            assert(crows(sv, rp, pd, t, n).drop_last() =~= si);
        } else {
            assert(cterm(sv, rp, pd, t, k, n - 1) == 0);
        }
    }
}

/// The group accumulators of the normal form over the FROM are the lineitem sums.
pub proof fn lemma_group_sums(sv: StoresView, rp: Seq<u8>, pd: int, t: int, k: Row)
    requires stores_wf(sv), keys_ok(sv),
    ensures ({
        let g = q5_spec(rp, pd, t);
        let n = nl(sv) as int;
        &&& gsum(g, from6(sv), k, 0) == csum(sv, rp, pd, t, k, n)
        &&& gcount(g, from6(sv), k) as int == ccount(sv, rp, pd, t, k, n)
        &&& gabs(g, from6(sv), k, 0) == cabs(sv, rp, pd, t, k, n)
    }),
{
    let g = q5_spec(rp, pd, t);
    let xs = from6(sv);
    let n = nl(sv) as int;
    let q = qual_fn(rp, pd, t);
    let kept = keep(xs, q);
    let cr = crows(sv, rp, pd, t, n);
    lemma_acc_sum_of(g, xs, k, 0);
    lemma_kept_bag(sv, rp, pd, t);
    lemma_crows_sums(sv, rp, pd, t, k, n);
    let fs = sum_term(g, k, 0);
    let fc = count_term(g, k);
    let fa = abs_term(g, k, 0);
    assert forall|i: int| 0 <= i < xs.len() && !q(#[trigger] xs[i]) implies fs(xs[i]) == 0 && fc(xs[i]) == 0 && fa(xs[i]) == 0 by {}
    lemma_sum_of_keep(xs, q, fs);
    lemma_sum_of_keep(xs, q, fc);
    lemma_sum_of_keep(xs, q, fa);
    lemma_sum_of_perm(kept, cr, fs);
    lemma_sum_of_perm(kept, cr, fc);
    lemma_sum_of_perm(kept, cr, fa);
}

} // verus!
