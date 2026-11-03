//! The per-slot totals of the recorded lineitem rows, as definitions and lemmas (`decide` computes them).
//!
//! Slot `s` of `n` slots sums the quantities (`acc_of`) and counts (`cnt_of`) of the recorded rows (`lrec`: in the
//! window, part key matching) whose key pair's first slot is `s`. For the first slot `c` of a key pair `(a, b)` with
//! a matching part key `a` these are exactly `lsum(a, b)` and `lcnt(a, b)` (`lemma_first_totals`): every lineitem
//! hit of `(a, b)` is recorded and counted at `c`, and nothing else is.
use vstd::prelude::*;
use crate::gendb_entry::stores::StoresView;
use crate::agent::tables::*;
use crate::agent::normal::*;
use crate::agent::slots::*;
use crate::agent::linepass::*;
use crate::agent::common::selection::*;

verus! {

/// The quantity / count term of row `l` for slot `s`: its quantity (1) when `s` is its pair's first slot.
pub open spec fn qterm(sv: StoresView, spk: Seq<i64>, ssk: Seq<i64>, n: int, s: int) -> spec_fn(int) -> int {
    |l: int| if first_slot(spk, ssk, n, lpk(sv)[l] as int, lsk(sv)[l] as int, s) { lqt(sv)[l] as int } else { 0int }
}
pub open spec fn cterm(sv: StoresView, spk: Seq<i64>, ssk: Seq<i64>, n: int, s: int) -> spec_fn(int) -> int {
    |l: int| if first_slot(spk, ssk, n, lpk(sv)[l] as int, lsk(sv)[l] as int, s) { 1int } else { 0int }
}

/// Slot `s`'s quantity sum and count over the recorded rows of `[0, hi)`.
pub open spec fn acc_of(sv: StoresView, dlo: int, dhi: int, keys: Seq<int>, spk: Seq<i64>, ssk: Seq<i64>, n: int, s: int, hi: int) -> int {
    range_sum(0, hi, guard(lrec(sv, dlo, dhi, keys), qterm(sv, spk, ssk, n, s)))
}
pub open spec fn cnt_of(sv: StoresView, dlo: int, dhi: int, keys: Seq<int>, spk: Seq<i64>, ssk: Seq<i64>, n: int, s: int, hi: int) -> int {
    range_sum(0, hi, guard(lrec(sv, dlo, dhi, keys), cterm(sv, spk, ssk, n, s)))
}

/// The largest quantity coefficient magnitude of numeric(15,2).
pub open spec fn qmax() -> int { 999_999_999_999_999 }

/// The totals of the first slot `c` of the pair `(a, b)`, `a` a matching key, are the pair's lineitem totals.
pub proof fn lemma_first_totals(sv: StoresView, dlo: int, dhi: int, keys: Seq<int>, spk: Seq<i64>, ssk: Seq<i64>, n: int,
    a: int, b: int, c: int)
    requires first_slot(spk, ssk, n, a, b, c), keys.contains(a),
    ensures
        acc_of(sv, dlo, dhi, keys, spk, ssk, n, c, n_l(sv) as int) == lsum(sv, dlo, dhi, a, b),
        cnt_of(sv, dlo, dhi, keys, spk, ssk, n, c, n_l(sv) as int) == lcnt(sv, dlo, dhi, a, b),
{
    let f = lrec(sv, dlo, dhi, keys);
    let ga = guard(f, qterm(sv, spk, ssk, n, c));
    let gc = guard(f, cterm(sv, spk, ssk, n, c));
    assert forall|l: int| 0 <= l < n_l(sv) implies #[trigger] ga(l) == lsum_term(sv, dlo, dhi, a, b)(l)
        && gc(l) == lcnt_term(sv, dlo, dhi, a, b)(l) by {
        let (x, y) = (lpk(sv)[l] as int, lsk(sv)[l] as int);
        if lhit(sv, dlo, dhi, a, b, l) {
            assert(f(l));
            assert(first_slot(spk, ssk, n, x, y, c));
        } else if first_slot(spk, ssk, n, x, y, c) {
            assert(x == a && y == b);
            assert(!in_win(sv, dlo, dhi, l));
        }
    }
    lemma_range_sum_ext(0, n_l(sv) as int, ga, lsum_term(sv, dlo, dhi, a, b));
    lemma_range_sum_ext(0, n_l(sv) as int, gc, lcnt_term(sv, dlo, dhi, a, b));
}

/// One record more: the term of its row for every slot (its first slot gains it, no other slot does).
pub proof fn lemma_record_terms(sv: StoresView, spk: Seq<i64>, ssk: Seq<i64>, n: int, l: int, s0: int, s: int)
    requires first_slot(spk, ssk, n, lpk(sv)[l] as int, lsk(sv)[l] as int, s0),
    ensures
        qterm(sv, spk, ssk, n, s)(l) == if s == s0 { lqt(sv)[l] as int } else { 0 },
        cterm(sv, spk, ssk, n, s)(l) == if s == s0 { 1int } else { 0 },
{
    if s != s0 && first_slot(spk, ssk, n, lpk(sv)[l] as int, lsk(sv)[l] as int, s) {
        lemma_first_unique(spk, ssk, n, lpk(sv)[l] as int, lsk(sv)[l] as int, s0, s);
    }
}

} // verus!
