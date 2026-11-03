//! Runs of equal order keys in `l_orderkey` and what one scan over a run knows about it.
//!
//! When `l_orderkey` is sorted (`sorted`: every adjacent pair ordered), a run `[a, b)` of one key that starts and
//! ends at key changes (`run_ok`) holds every row of that key (`lemma_run_complete`), so the EXISTS / NOT EXISTS of
//! a row of the run look only at the run. The scan keeps, for the prefix `[a, e)` of the current run, the number of
//! late rows, the supplier `ll` of a late row, and two flags (`st_ok`): `mb` (two late rows of different suppliers)
//! and `db` (two rows of different suppliers). One more row updates them (`lemma_step`), and a finished run's count
//! for any supplier key `v` is `nlate * ofs(key)` when the run has late rows, all of supplier `ll == v`, and two
//! suppliers, otherwise 0 (`lemma_run_contrib`).
use vstd::prelude::*;
use crate::gendb_entry::stores::StoresView;
use crate::agent::cols::*;
use crate::agent::nf::*;

verus! {

// ------------------------------------------------------------------------------------------------ order

/// The adjacent pair ending at row `t` is ordered.
pub open spec fn pair_ok(sv: StoresView, t: int) -> bool { lk(sv)[t - 1] <= lk(sv)[t] }

/// Every adjacent pair inside `[lo, hi)` is ordered.
pub open spec fn pairs_ok(sv: StoresView, lo: int, hi: int) -> bool {
    forall|t: int| lo < t < hi ==> #[trigger] pair_ok(sv, t)
}

/// `l_orderkey` is sorted.
pub open spec fn sorted(sv: StoresView) -> bool { pairs_ok(sv, 0, n_l(sv)) }

/// Sorted keys are monotone.
pub proof fn lemma_sorted_mono(sv: StoresView, x: int, y: int)
    requires sorted(sv), 0 <= x <= y < n_l(sv),
    ensures lk(sv)[x] <= lk(sv)[y],
    decreases y - x,
{
    if x < y {
        lemma_sorted_mono(sv, x, y - 1);
        assert(pair_ok(sv, y));
    }
}

/// Two adjacent ranges of ordered pairs whose boundary pair is ordered.
pub proof fn lemma_pairs_join(sv: StoresView, lo: int, mid: int, hi: int)
    requires pairs_ok(sv, lo, mid), pairs_ok(sv, mid, hi), lo < mid ==> pair_ok(sv, mid), lo <= mid <= hi,
    ensures pairs_ok(sv, lo, hi),
{
    assert forall|t: int| lo < t < hi implies #[trigger] pair_ok(sv, t) by {
        if t < mid {} else if t == mid {} else {}
    }
}

// ------------------------------------------------------------------------------------------------ runs

/// `[a, b)` is a run of one key that starts and ends at key changes.
pub open spec fn run_ok(sv: StoresView, a: int, b: int) -> bool {
    &&& 0 <= a < b <= n_l(sv)
    &&& forall|t: int| a <= t < b ==> #[trigger] lk(sv)[t] == lk(sv)[a]
    &&& (a == 0 || lk(sv)[a - 1] != lk(sv)[a])
    &&& (b == n_l(sv) || lk(sv)[b] != lk(sv)[a])
}

/// In sorted keys, such a run holds every row of its key.
pub proof fn lemma_run_complete(sv: StoresView, a: int, b: int, j: int)
    requires sorted(sv), run_ok(sv, a, b), 0 <= j < n_l(sv), lk(sv)[j] == lk(sv)[a],
    ensures a <= j < b,
{
    if j < a {
        lemma_sorted_mono(sv, j, a - 1);
        assert(pair_ok(sv, a));
    } else if j >= b {
        lemma_sorted_mono(sv, b, j);
        assert(pair_ok(sv, b));
        assert(lk(sv)[b - 1] == lk(sv)[a]);
    }
}

// ------------------------------------------------------------------------------------------------ run prefix state

/// Number of late rows in `[a, e)`.
pub open spec fn nlr(sv: StoresView, a: int, e: int) -> nat
    decreases e - a,
{
    if e <= a { 0 } else { nlr(sv, a, e - 1) + if late(sv, e - 1) { 1nat } else { 0nat } }
}

/// Every late row of `[a, e)` has supplier `v`.
pub open spec fn late_sup_all(sv: StoresView, a: int, e: int, v: int) -> bool {
    forall|t: int| a <= t < e && late(sv, t) ==> #[trigger] ls(sv)[t] as int == v
}

/// Two late rows of `[a, e)` have different suppliers.
pub open spec fn late_pair(sv: StoresView, a: int, e: int) -> bool {
    exists|t1: int, t2: int| a <= t1 < e && a <= t2 < e && late(sv, t1) && late(sv, t2)
        && #[trigger] ls(sv)[t1] != #[trigger] ls(sv)[t2]
}

/// Every row of `[a, e)` has row `a`'s supplier.
pub open spec fn sup_all(sv: StoresView, a: int, e: int) -> bool {
    forall|t: int| a <= t < e ==> #[trigger] ls(sv)[t] == ls(sv)[a]
}

/// Two rows of `[a, e)` have different suppliers.
pub open spec fn sup_pair(sv: StoresView, a: int, e: int) -> bool {
    exists|t1: int, t2: int| a <= t1 < e && a <= t2 < e && #[trigger] ls(sv)[t1] != #[trigger] ls(sv)[t2]
}

/// Some late row of `[a, e)` has supplier `v`.
pub open spec fn some_late_v(sv: StoresView, a: int, e: int, v: int) -> bool {
    exists|t: int| a <= t < e && late(sv, t) && #[trigger] ls(sv)[t] as int == v
}

/// What the scan knows about the run prefix `[a, e)`.
pub open spec fn st_ok(sv: StoresView, a: int, e: int, mb: bool, db: bool, ll: i64, nlate: u64) -> bool {
    &&& nlate as int == nlr(sv, a, e)
    &&& (nlate > 0 ==> some_late_v(sv, a, e, ll as int))
    &&& (!mb ==> late_sup_all(sv, a, e, ll as int))
    &&& (mb ==> late_pair(sv, a, e))
    &&& (!db ==> sup_all(sv, a, e))
    &&& (db ==> sup_pair(sv, a, e))
}

/// No late row in `[a, e)` exactly when the count is 0; the count is at most the length.
pub proof fn lemma_nlr(sv: StoresView, a: int, e: int)
    requires a <= e,
    ensures
        nlr(sv, a, e) <= e - a,
        nlr(sv, a, e) == 0 ==> forall|t: int| a <= t < e ==> !late(sv, t),
    decreases e - a,
{
    if e > a {
        lemma_nlr(sv, a, e - 1);
    }
}

/// The empty prefix.
pub proof fn lemma_st_empty(sv: StoresView, a: int, ll: i64)
    ensures st_ok(sv, a, a, false, false, ll, 0),
{
}

/// One more row `e` of the same run: the updated state (`multi`: a late row whose supplier differs from `ll` after
/// an earlier late row; `diff`: a supplier differing from the previous row's `ps`).
pub proof fn lemma_step(sv: StoresView, a: int, e: int, mb: bool, db: bool, ll: i64, nlate: u64, ps: i64)
    requires
        a <= e < n_l(sv), ls(sv).len() == n_l(sv), lc(sv).len() == n_l(sv), lr(sv).len() == n_l(sv),
        st_ok(sv, a, e, mb, db, ll, nlate),
        e > a ==> ps == ls(sv)[e - 1],
        e == a ==> ps == ls(sv)[a],
        nlate < u64::MAX,
    ensures ({
        let s = ls(sv)[e];
        let lt = late(sv, e);
        let multi = lt && nlate > 0 && s != ll;
        let diff = s != ps;
        st_ok(sv, a, e + 1, mb || multi, db || diff, if lt { s } else { ll }, (nlate + if lt { 1u64 } else { 0u64 }) as u64)
    }),
{
    let s = ls(sv)[e];
    let lt = late(sv, e);
    let multi = lt && nlate > 0 && s != ll;
    let diff = s != ps;
    let ll2 = if lt { s } else { ll };
    let mb2 = mb || multi;
    let db2 = db || diff;
    lemma_nlr(sv, a, e);
    // the late supplier
    if nlate > 0 || lt {
        if lt {
            assert(some_late_v(sv, a, e + 1, ll2 as int)) by { assert(ls(sv)[e] as int == ll2 as int); }
        } else {
            let t = choose|t: int| a <= t < e && late(sv, t) && #[trigger] ls(sv)[t] as int == ll as int;
            assert(some_late_v(sv, a, e + 1, ll2 as int)) by { assert(ls(sv)[t] as int == ll2 as int); }
        }
    }
    // all late rows share `ll2` unless `mb2`
    if !mb2 {
        assert forall|t: int| a <= t < e + 1 && late(sv, t) implies #[trigger] ls(sv)[t] as int == ll2 as int by {
            if t < e {
                assert(ls(sv)[t] as int == ll as int);
                if lt {
                    assert(nlate > 0);
                }
            }
        }
    }
    // a pair of late rows of different suppliers
    if mb2 {
        if !mb {
            let t = choose|t: int| a <= t < e && late(sv, t) && #[trigger] ls(sv)[t] as int == ll as int;
            assert(late_pair(sv, a, e + 1)) by { assert(ls(sv)[t] != ls(sv)[e]); }
        } else {
            let (t1, t2) = choose|t1: int, t2: int| a <= t1 < e && a <= t2 < e && late(sv, t1) && late(sv, t2)
                && #[trigger] ls(sv)[t1] != #[trigger] ls(sv)[t2];
            assert(late_pair(sv, a, e + 1)) by { assert(ls(sv)[t1] != ls(sv)[t2]); }
        }
    }
    // all rows share row `a`'s supplier unless `db2`
    if !db2 {
        assert forall|t: int| a <= t < e + 1 implies #[trigger] ls(sv)[t] == ls(sv)[a] by {
            if t == e && e > a {
                assert(ls(sv)[e - 1] == ls(sv)[a]);
            }
        }
    }
    if db2 {
        if !db {
            assert(e > a);
            assert(sup_pair(sv, a, e + 1)) by { assert(ls(sv)[e - 1] != ls(sv)[e]); }
        } else {
            let (t1, t2) = choose|t1: int, t2: int| a <= t1 < e && a <= t2 < e && #[trigger] ls(sv)[t1] != #[trigger] ls(sv)[t2];
            assert(sup_pair(sv, a, e + 1)) by { assert(ls(sv)[t1] != ls(sv)[t2]); }
        }
    }
}

// ------------------------------------------------------------------------------------------------ a finished run

/// The run has late rows, all of one supplier, and two suppliers: its waiting rows are its late rows.
pub open spec fn cand(nlate: u64, mb: bool, db: bool) -> bool { nlate > 0 && !mb && db }

/// Per row of a finished complete run: its contribution to supplier key `v`.
proof fn lemma_run_row(sv: StoresView, a: int, b: int, mb: bool, db: bool, ll: i64, nlate: u64, v: int, i: int)
    requires sorted(sv), run_ok(sv, a, b), st_ok(sv, a, b, mb, db, ll, nlate), a <= i < b,
        ls(sv).len() == n_l(sv),
    ensures lterm(sv, v, i) == if cand(nlate, mb, db) && v == ll as int && late(sv, i) { ofs(sv, lk(sv)[a] as int) } else { 0 },
{
    assert(lk(sv)[i] == lk(sv)[a]);
    lemma_nlr(sv, a, b);
    if late(sv, i) {
        if !(nlate > 0) {
            assert(!late(sv, i));
        } else if mb {
            // a late row of another supplier: NOT EXISTS fails
            let (t1, t2) = choose|t1: int, t2: int| a <= t1 < b && a <= t2 < b && late(sv, t1) && late(sv, t2)
                && #[trigger] ls(sv)[t1] != #[trigger] ls(sv)[t2];
            let t = if ls(sv)[t1] != ls(sv)[i] { t1 } else { t2 };
            assert(lk(sv)[t] == lk(sv)[a]);
            assert(other_at(sv, i, t));
            assert(ex3(sv, i));
        } else if !db {
            // one supplier only: EXISTS fails
            assert forall|j: int| 0 <= j < n_l(sv) implies !#[trigger] other_at(sv, i, j) by {
                if lk(sv)[j] == lk(sv)[i] {
                    lemma_run_complete(sv, a, b, j);
                    assert(ls(sv)[j] == ls(sv)[a]);
                    assert(ls(sv)[i] == ls(sv)[a]);
                }
            }
            assert(!ex2(sv, i));
        } else {
            // the candidate case: EXISTS holds, NOT EXISTS holds
            assert(ls(sv)[i] as int == ll as int);
            let (t1, t2) = choose|t1: int, t2: int| a <= t1 < b && a <= t2 < b && #[trigger] ls(sv)[t1] != #[trigger] ls(sv)[t2];
            let t = if ls(sv)[t1] != ls(sv)[i] { t1 } else { t2 };
            assert(lk(sv)[t] == lk(sv)[a]);
            assert(other_at(sv, i, t));
            assert(ex2(sv, i));
            assert forall|j: int| 0 <= j < n_l(sv) implies !(#[trigger] other_at(sv, i, j) && late(sv, j)) by {
                if lk(sv)[j] == lk(sv)[i] && late(sv, j) {
                    lemma_run_complete(sv, a, b, j);
                    assert(ls(sv)[j] as int == ll as int);
                }
            }
            assert(!ex3(sv, i));
        }
    }
}

/// `ksum` over `[a, e)` of a run whose rows contribute `w` when `c` holds and the row is late.
proof fn lemma_sum_late(sv: StoresView, a: int, b: int, e: int, mb: bool, db: bool, ll: i64, nlate: u64, v: int)
    requires sorted(sv), run_ok(sv, a, b), st_ok(sv, a, b, mb, db, ll, nlate), a <= e <= b, ls(sv).len() == n_l(sv),
    ensures ksum(sv, v, a, e) == if cand(nlate, mb, db) && v == ll as int { nlr(sv, a, e) * ofs(sv, lk(sv)[a] as int) } else { 0 },
    decreases e - a,
{
    if e > a {
        lemma_sum_late(sv, a, b, e - 1, mb, db, ll, nlate, v);
        lemma_run_row(sv, a, b, mb, db, ll, nlate, v, e - 1);
        let w = ofs(sv, lk(sv)[a] as int) as int;
        let x = nlr(sv, a, e - 1) as int;
        assert((x + 1) * w == x * w + w) by (nonlinear_arith);
    }
}

/// The count of a finished complete run for supplier key `v`.
pub proof fn lemma_run_contrib(sv: StoresView, a: int, b: int, mb: bool, db: bool, ll: i64, nlate: u64, v: int)
    requires sorted(sv), run_ok(sv, a, b), st_ok(sv, a, b, mb, db, ll, nlate), ls(sv).len() == n_l(sv),
    ensures ksum(sv, v, a, b) == if cand(nlate, mb, db) && v == ll as int { nlate * ofs(sv, lk(sv)[a] as int) } else { 0 },
{
    lemma_sum_late(sv, a, b, b, mb, db, ll, nlate, v);
}

} // verus!
