//! Per-slot totals from the hit records: for slot `s` (key `keys[s]`), the quantity sum `sums[s]` and the row count
//! `cnts[s]` of the lineitem rows with that part key (`sub::ksum`, `sub::kcnt`). Every such row is a hit (its key is
//! listed), and the listed keys are distinct, so each hit adds to exactly its own slot.
//!
//! The hit records of the ranges, in range order, list the rows `range_filter(0, nl, inrow)` (`lemma_flat_ranges`).
use vstd::prelude::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::agent::tables::*;
use crate::agent::sub::*;
use crate::agent::keys::*;
use crate::agent::scan::*;
use crate::agent::parts::{split_at, lemma_split};
use crate::agent::common::selection::*;
use crate::agent::common::keyset::*;

verus! {

/// The bound of a quantity or price coefficient: `10^15 - 1`.
pub open spec fn coef_max() -> int { 999_999_999_999_999 }

/// The rows of the ranges `0..t` of `nt` even ranges, concatenated: the listed rows below the range boundary.
pub proof fn lemma_flat_step(nl: int, nt: int, t: int, p: spec_fn(int) -> bool)
    requires 0 <= nl, 1 <= nt, 0 <= t < nt,
    ensures
        range_filter(0, split_at(nl, nt, t), p) + range_filter(split_at(nl, nt, t), split_at(nl, nt, t + 1), p)
            == range_filter(0, split_at(nl, nt, t + 1), p),
{
    lemma_split(nl, nt, t);
    lemma_range_filter_concat(0, split_at(nl, nt, t), split_at(nl, nt, t + 1), p);
}

/// The sum of a list of rows below `nl` whose terms are bounded by `coef_max()` (in absolute value).
pub proof fn lemma_seq_sum_bound(xs: Seq<int>, f: spec_fn(int) -> int)
    requires forall|t: int| 0 <= t < xs.len() ==> -999_999_999_999_999 <= #[trigger] f(xs[t]) <= 999_999_999_999_999,
    ensures -999_999_999_999_999 * xs.len() <= seq_sum(xs, f) <= 999_999_999_999_999 * xs.len(),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let xi = xs.drop_last();
        assert forall|t: int| 0 <= t < xi.len() implies -999_999_999_999_999 <= #[trigger] f(xi[t]) <= 999_999_999_999_999 by {
            assert(xi[t] == xs[t]);
        }
        lemma_seq_sum_bound(xi, f);
        assert(f(xs.last()) == f(xs[xs.len() - 1]));
    }
}

/// The per-slot sums of every slot over the rows `xs`.
pub open spec fn sums_ok(sums: Seq<i128>, cnts: Seq<i128>, xs: Seq<int>, keys: Seq<i64>, sv: StoresView) -> bool {
    &&& sums.len() == keys.len() && cnts.len() == keys.len()
    &&& forall|s: int| 0 <= s < keys.len() ==> #[trigger] sums[s] as int == seq_sum(xs, kqty_term(sv, keys[s] as int))
            && cnts[s] as int == seq_sum(xs, kcnt_term(sv, keys[s] as int))
}

/// One more hit row `l` in slot `s0`: only that slot's sums grow.
proof fn lemma_sums_step(sums: Seq<i128>, cnts: Seq<i128>, xs: Seq<int>, keys: Seq<i64>, sv: StoresView, l: int, s0: int,
    sums2: Seq<i128>, cnts2: Seq<i128>)
    requires
        sums_ok(sums, cnts, xs, keys, sv),
        0 <= s0 < keys.len(), keys[s0] == l_pkey(sv)[l],
        forall|s: int, t: int| 0 <= s < keys.len() && 0 <= t < keys.len() && #[trigger] keys[s] == #[trigger] keys[t] ==> s == t,
        sums2 == sums.update(s0, (sums[s0] + l_qty(sv)[l]) as i128),
        cnts2 == cnts.update(s0, (cnts[s0] + 1) as i128),
        sums[s0] + l_qty(sv)[l] == (sums[s0] + l_qty(sv)[l]) as i128,
        cnts[s0] + 1 == (cnts[s0] + 1) as i128,
    ensures sums_ok(sums2, cnts2, xs.push(l), keys, sv),
{
    assert forall|s: int| 0 <= s < keys.len() implies #[trigger] sums2[s] as int == seq_sum(xs.push(l), kqty_term(sv, keys[s] as int))
        && cnts2[s] as int == seq_sum(xs.push(l), kcnt_term(sv, keys[s] as int)) by {
        lemma_seq_sum_push(xs, l, kqty_term(sv, keys[s] as int));
        lemma_seq_sum_push(xs, l, kcnt_term(sv, keys[s] as int));
        if s != s0 {
            assert(keys[s] != keys[s0]);
        }
    }
}

/// The per-slot quantity sums and row counts of every slot's key.
pub fn slot_sums(outs: &Vec<Hits>, nt: usize, ks: &KeySet, Ghost(sv): Ghost<StoresView>, Ghost(srows): Ghost<Seq<int>>,
    Ghost(ps): Ghost<Seq<Literal>>) -> (r: (Vec<i128>, Vec<i128>))
    requires
        1 <= nt, scan_ok(outs@, nt as int, ks.keys@, sv), keyset_wf(ks), keys_ok(ks.keys@, srows, sv, ps),
        keys_unique(p_key(sv)), domains_ok(sv), sizes_ok(sv),
    ensures
        r.0@.len() == ks.n && r.1@.len() == ks.n,
        forall|s: int| 0 <= s < ks.n ==> #[trigger] r.0@[s] as int == ksum(sv, ks.keys@[s] as int)
            && r.1@[s] as int == kcnt(sv, ks.keys@[s] as int),
{
    let ghost keys = ks.keys@;
    let ghost p = inrow(keys, sv);
    let ghost nl = n_l(sv) as int;
    proof { lemma_keys_distinct(keys, srows, sv, ps); }
    let n = ks.n;
    let mut sums: Vec<i128> = vec![0i128; n];
    let mut cnts: Vec<i128> = vec![0i128; n];
    proof {
        assert(sums_ok(sums@, cnts@, Seq::empty(), keys, sv)) by {
            assert forall|s: int| 0 <= s < keys.len() implies #[trigger] sums@[s] as int == seq_sum(Seq::<int>::empty(), kqty_term(sv, keys[s] as int))
                && cnts@[s] as int == seq_sum(Seq::<int>::empty(), kcnt_term(sv, keys[s] as int)) by {
                assert(vstd::pervasive::cloned(0i128, sums@[s]));
                assert(vstd::pervasive::cloned(0i128, cnts@[s]));
            }
        }
        lemma_split(nl, nt as int, 0);
        assert(range_filter(0, 0, p) =~= Seq::<int>::empty());
    }
    let mut t: usize = 0;
    while t < nt
        invariant
            1 <= nt, scan_ok(outs@, nt as int, keys, sv), keyset_wf(ks), keys == ks.keys@, n == ks.n,
            p == inrow(keys, sv), nl == n_l(sv), domains_ok(sv), sizes_ok(sv), t <= nt,
            forall|s: int, u: int| 0 <= s < keys.len() && 0 <= u < keys.len() && #[trigger] keys[s] == #[trigger] keys[u] ==> s == u,
            sums_ok(sums@, cnts@, range_filter(0, split_at(nl, nt as int, t as int), p), keys, sv),
        decreases nt - t,
    {
        proof { lemma_split(nl, nt as int, t as int); }
        let ghost x0 = range_filter(0, split_at(nl, nt as int, t as int), p);
        let ghost rt = range_filter(split_at(nl, nt as int, t as int), split_at(nl, nt as int, t + 1), p);
        let h = &outs[t];
        assert(hits_ok(h, rt, keys, sv));
        proof {
            lemma_flat_step(nl, nt as int, t as int, p);
            lemma_range_filter_members(0, split_at(nl, nt as int, t + 1), p);
            assert(x0 + rt == range_filter(0, split_at(nl, nt as int, t + 1), p));
        }
        let used = h.used;
        let mut j: usize = 0;
        while j < used
            invariant
                keys == ks.keys@, n == ks.n, used == h.used, j <= used, domains_ok(sv), sizes_ok(sv),
                hits_ok(h, rt, keys, sv),
                x0 + rt == range_filter(0, split_at(nl, nt as int, t + 1), p),
                0 <= split_at(nl, nt as int, t + 1) <= nl, nl == n_l(sv),
                (x0 + rt).len() <= nl,
                forall|s: int, u: int| 0 <= s < keys.len() && 0 <= u < keys.len() && #[trigger] keys[s] == #[trigger] keys[u] ==> s == u,
                sums_ok(sums@, cnts@, x0 + rt.take(j as int), keys, sv),
            decreases used - j,
        {
            let ghost xs = x0 + rt.take(j as int);
            let (s0, q, _pr) = h.recs[j];
            let ghost l = rt[j as int];
            proof {
                assert(rec_ok(h.recs@[j as int], l, keys, sv));
                assert(xs.len() < (x0 + rt).len());
                // the slot's sums so far are bounded by the rows so far
                let fq = kqty_term(sv, keys[s0 as int] as int);
                let fc = kcnt_term(sv, keys[s0 as int] as int);
                lemma_range_filter_members(0, split_at(nl, nt as int, t + 1), p);
                assert forall|u: int| 0 <= u < xs.len() implies -999_999_999_999_999 <= #[trigger] fq(xs[u]) <= 999_999_999_999_999 by {
                    assert(xs[u] == (x0 + rt)[u]);
                    let r = xs[u];
                    assert(0 <= r < nl);
                    assert(num15(l_qty(sv)[r]));
                }
                lemma_seq_sum_bound(xs, fq);
                assert forall|u: int| 0 <= u < xs.len() implies -999_999_999_999_999 <= #[trigger] fc(xs[u]) <= 999_999_999_999_999 by {}
                lemma_seq_sum_bound(xs, fc);
                lemma_sum_bound_small();
                let m = xs.len() + 1;
                assert(m <= nl);
                assert(nl <= usize::MAX as int);
                assert(usize::MAX as int <= 0xffff_ffff_ffff_ffff);
                assert(999_999_999_999_999 * m < sum_bound()) by (nonlinear_arith)
                    requires 0 <= m <= 0xffff_ffff_ffff_ffff;
                assert(num15(l_qty(sv)[l]));
            }
            let ghost sums0 = sums@;
            let ghost cnts0 = cnts@;
            let a = sums[s0];
            let b = cnts[s0];
            sums.set(s0, a + q as i128);
            cnts.set(s0, b + 1);
            proof {
                lemma_sums_step(sums0, cnts0, xs, keys, sv, l, s0 as int, sums@, cnts@);
                assert(rt.take(j + 1) =~= rt.take(j as int).push(l));
                assert(x0 + rt.take(j + 1) =~= xs.push(l));
            }
            j = j + 1;
        }
        proof {
            assert(rt.take(used as int) =~= rt);
        }
        t = t + 1;
    }
    proof {
        lemma_split(nl, nt as int, (nt - 1) as int);
        let xs = range_filter(0, nl, p);
        assert forall|s: int| 0 <= s < n implies #[trigger] sums@[s] as int == ksum(sv, keys[s] as int)
            && cnts@[s] as int == kcnt(sv, keys[s] as int) by {
            let k = keys[s] as int;
            lemma_sum_range_filter(0, nl, p, kqty_term(sv, k));
            lemma_sum_range_filter(0, nl, p, kcnt_term(sv, k));
            assert forall|l: int| 0 <= l < nl implies #[trigger] guard(p, kqty_term(sv, k))(l) == kqty_term(sv, k)(l) by {
                if !p(l) {
                    assert(l_pkey(sv)[l] != keys[s]);
                }
            }
            assert forall|l: int| 0 <= l < nl implies #[trigger] guard(p, kcnt_term(sv, k))(l) == kcnt_term(sv, k)(l) by {
                if !p(l) {
                    assert(l_pkey(sv)[l] != keys[s]);
                }
            }
            lemma_range_sum_ext(0, nl, guard(p, kqty_term(sv, k)), kqty_term(sv, k));
            lemma_range_sum_ext(0, nl, guard(p, kcnt_term(sv, k)), kcnt_term(sv, k));
        }
    }
    (sums, cnts)
}

} // verus!
