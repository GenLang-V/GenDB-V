//! Phase 2: one task per customer range `[clo, chi)` (the ranges of phase 1, whose exact group ids it reads).
//! The task first ORs, word by word, the phase-1 bit sets over its key window `[64 * w0, 64 * w1)` (`merged_ok`):
//! with customer keys `row + 1` (the usual layout) that window holds the keys of its rows. Then, per row of its
//! range whose code hits and whose balance exceeds the threshold, it decides whether some orders row has the row's
//! key (the merged window; the separate bit sets for a key outside the window; a scan of `o_custkey` for a key
//! outside every bit set) and counts and sums the rows without orders per group id (`out2_ok`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::ast::Literal;
use crate::gendb_entry::parallel::WorkerTask;
use crate::gendb_entry::stores::StoresView;
use crate::agent::common::bitset::*;
use crate::agent::common::rsum::*;
use crate::agent::common::split::*;
use crate::agent::tables::*;
use crate::agent::normal::*;
use crate::agent::cols::*;
use crate::agent::codes::*;
use crate::agent::phase1::*;

verus! {

/// Bit `b` of a word.
pub open spec fn wbit(x: u64, b: int) -> bool { (x >> (b as u64)) & 1u64 == 1u64 }

/// The phase-1 bit sets: set `s` marks the keys below `range` of the orders range `s` of `nsets` even ranges.
pub open spec fn sets_ok(sets: Seq<Vec<u64>>, sv: StoresView, nsets: int, range: int) -> bool {
    &&& 1 <= nsets
    &&& sets.len() == nsets
    &&& forall|s: int| 0 <= s < nsets ==>
            #[trigger] keys_ok(sets[s]@, sv, split(n_o(sv) as int, nsets, s), split(n_o(sv) as int, nsets, s + 1), range)
}

/// Some of the first `s_hi` bit sets has bit `b` of word `w`.
pub open spec fn any_word(sets: Seq<Vec<u64>>, s_hi: int, w: int, b: int) -> bool {
    exists|s: int| 0 <= s < s_hi && #[trigger] wbit(sets[s]@[w], b)
}

/// The merged window: word `w - w0` holds the OR of word `w` of the first `s_hi` sets.
pub open spec fn merged_ok(merged: Seq<u64>, sets: Seq<Vec<u64>>, s_hi: int, w0: int, w1: int) -> bool {
    &&& merged.len() == w1 - w0
    &&& forall|w: int, b: int| w0 <= w < w1 && 0 <= b < 64 ==> (#[trigger] wbit(merged[w - w0], b) == any_word(sets, s_hi, w, b))
}

/// Bits of an OR.
#[verifier::spinoff_prover]
pub proof fn lemma_or_bit(x: u64, y: u64, b: int)
    requires 0 <= b < 64,
    ensures wbit(x | y, b) == (wbit(x, b) || wbit(y, b)),
{
    let s = b as u64;
    assert((((x | y) >> s) & 1u64 == 1u64) == (((x >> s) & 1u64 == 1u64) || ((y >> s) & 1u64 == 1u64))) by (bit_vector)
        requires s < 64;
}

/// A key below `range` is held by some orders row exactly when some phase-1 set marks it.
#[verifier::spinoff_prover]
pub proof fn lemma_sets_key(sets: Seq<Vec<u64>>, sv: StoresView, nsets: int, range: int, k: int)
    requires sets_ok(sets, sv, nsets, range), 0 <= k < range,
    ensures (exists|s: int| 0 <= s < nsets && #[trigger] bit_at(sets[s]@, k)) == has_ord(sv, k),
{
    let n = n_o(sv) as int;
    if exists|s: int| 0 <= s < nsets && #[trigger] bit_at(sets[s]@, k) {
        let s = choose|s: int| 0 <= s < nsets && #[trigger] bit_at(sets[s]@, k);
        assert(keys_ok(sets[s]@, sv, split(n, nsets, s), split(n, nsets, s + 1), range));
        let j = choose|j: int| split(n, nsets, s) <= j < split(n, nsets, s + 1) && #[trigger] ock(sv)[j] as int == k;
        lemma_split(n, nsets, s + 1, nsets);
        lemma_split(n, nsets, 0, s);
    }
    if has_ord(sv, k) {
        let j = choose|j: int| 0 <= j < n_o(sv) && #[trigger] ock(sv)[j] as int == k;
        let s = lemma_split_find(n, nsets, j);
        assert(keys_ok(sets[s]@, sv, split(n, nsets, s), split(n, nsets, s + 1), range));
        assert(ord_in(sv, k, split(n, nsets, s), split(n, nsets, s + 1)));
        assert(bit_at(sets[s]@, k));
    }
}

/// Whether some orders row has key `k`, without the merged window: the bit sets for a key below `range`, else a
/// scan of `o_custkey`.
#[verifier::spinoff_prover]
fn ord_check(c: &Cols, sets: &Vec<Vec<u64>>, nsets: usize, range: u64, k: i64, Ghost(sv): Ghost<StoresView>) -> (r: bool)
    requires cols_ok(*c, sv), sets_ok(sets@, sv, nsets as int, range as int), range < u64::MAX,
    ensures r == has_ord(sv, k as int),
    no_unwind
{
    if k >= 0 && (k as u64) < range {
        proof { lemma_sets_key(sets@, sv, nsets as int, range as int, k as int); }
        let mut s: usize = 0;
        while s < nsets
            invariant
                s <= nsets, sets_ok(sets@, sv, nsets as int, range as int), 0 <= k < range,
                forall|s2: int| 0 <= s2 < s ==> !(#[trigger] bit_at(sets@[s2]@, k as int)),
            decreases nsets - s,
        {
            proof {
                assert(keys_ok(sets@[s as int]@, sv, split(n_o(sv) as int, nsets as int, s as int),
                    split(n_o(sv) as int, nsets as int, s + 1), range as int));
                assert((k as int) / 64 < nwords(range as int));
            }
            if test_bit(&sets[s], k as u64) {
                proof {
                    assert(bit_at(sets@[s as int]@, k as int));
                    lemma_sets_key(sets@, sv, nsets as int, range as int, k as int);
                }
                return true;
            }
            s = s + 1;
        }
        false
    } else {
        let mut j: usize = 0;
        while j < c.no
            invariant j <= c.no, cols_ok(*c, sv), forall|j2: int| 0 <= j2 < j ==> #[trigger] ock(sv)[j2] as int != k as int,
            decreases c.no - j,
        {
            if c.ock[j] == k {
                return true;
            }
            j = j + 1;
        }
        false
    }
}

/// ORs word `w` of every set into the merged window.
#[verifier::spinoff_prover]
fn merge_window(sets: &Vec<Vec<u64>>, nsets: usize, nw: usize, w0: usize, w1: usize, merged: &mut Vec<u64>)
    requires
        w0 <= w1 <= nw, nsets == sets@.len(),
        forall|s: int| 0 <= s < nsets ==> (#[trigger] sets@[s])@.len() == nw,
        old(merged)@.len() == w1 - w0,
        forall|w: int| 0 <= w < old(merged)@.len() ==> #[trigger] old(merged)@[w] == 0u64,
    ensures merged_ok(final(merged)@, sets@, nsets as int, w0 as int, w1 as int),
    no_unwind
{
    proof {
        assert forall|w: int, b: int| w0 <= w < w1 && 0 <= b < 64 implies
            (#[trigger] wbit(merged@[w - w0], b) == any_word(sets@, 0, w, b)) by {
            let bb = b as u64;
            assert(merged@[w - w0] == 0u64);
            assert((0u64 >> bb) & 1u64 == 0u64) by (bit_vector);
        }
    }
    let mut s: usize = 0;
    while s < nsets
        invariant
            s <= nsets, nsets == sets@.len(), w0 <= w1 <= nw,
            forall|s2: int| 0 <= s2 < nsets ==> (#[trigger] sets@[s2])@.len() == nw,
            merged_ok(merged@, sets@, s as int, w0 as int, w1 as int),
        decreases nsets - s,
    {
        let set = &sets[s];
        let mut w = w0;
        while w < w1
            invariant
                w0 <= w <= w1, w1 <= nw, s < nsets, nsets == sets@.len(), set@ == sets@[s as int]@, set@.len() == nw,
                merged@.len() == w1 - w0,
                forall|w2: int, b: int| w0 <= w2 < w && 0 <= b < 64 ==> (#[trigger] wbit(merged@[w2 - w0], b) == any_word(sets@, s + 1, w2, b)),
                forall|w2: int, b: int| w <= w2 < w1 && 0 <= b < 64 ==> (#[trigger] wbit(merged@[w2 - w0], b) == any_word(sets@, s as int, w2, b)),
            decreases w1 - w,
        {
            let ghost before = merged@;
            let x = merged[w - w0] | set[w];
            merged[w - w0] = x;
            proof {
                assert forall|w2: int, b: int| w0 <= w2 < w + 1 && 0 <= b < 64 implies
                    (#[trigger] wbit(merged@[w2 - w0], b) == any_word(sets@, s + 1, w2, b)) by {
                    if w2 == w {
                        lemma_or_bit(before[w - w0], set@[w as int], b);
                        assert(wbit(before[w - w0], b) == any_word(sets@, s as int, w2, b));
                        if any_word(sets@, s + 1, w2, b) && !wbit(set@[w as int], b) {
                            let s3 = choose|s3: int| 0 <= s3 < s + 1 && #[trigger] wbit(sets@[s3]@[w2], b);
                            assert(s3 < s);
                        }
                        if wbit(set@[w as int], b) {
                            assert(wbit(sets@[s as int]@[w2], b));
                        }
                    } else {
                        assert(merged@[w2 - w0] == before[w2 - w0]);
                    }
                }
                assert forall|w2: int, b: int| w + 1 <= w2 < w1 && 0 <= b < 64 implies
                    (#[trigger] wbit(merged@[w2 - w0], b) == any_word(sets@, s as int, w2, b)) by {
                    assert(merged@[w2 - w0] == before[w2 - w0]);
                }
            }
            w = w + 1;
        }
        s = s + 1;
    }
}

/// The per-group counts and balance sums of the qualifying rows of `[lo, hi)`, with their bounds.
pub open spec fn gparts_ok(cnts: Seq<u64>, sums: Seq<i128>, sv: StoresView, ps: Seq<Literal>, lo: int, hi: int) -> bool {
    &&& cnts.len() == 7 && sums.len() == 7
    &&& forall|g: int| 0 <= g < 7 ==> #[trigger] cnts[g] as int == range_sum(lo, hi, gcnt_term(sv, ps, g))
            && sums[g] as int == range_sum(lo, hi, gsum_term(sv, ps, g))
            && cnts[g] <= hi - lo
            && -999_999_999_999_999 * (cnts[g] as int) <= sums[g] as int <= 999_999_999_999_999 * (cnts[g] as int)
}

/// One phase-2 task.
pub struct Task2 {
    pub c: Cols,
    pub sv: Ghost<StoresView>,
    pub ps: Ghost<Seq<Literal>>,
    pub sets: Arc<Vec<Vec<u64>>>,
    pub nsets: usize,
    pub range: u64,
    pub nw: usize,
    pub codes_all: Arc<Vec<Vec<u8>>>,
    pub t: usize,
    pub clo: usize,
    pub chi: usize,
    pub thr: i128,
    pub w0: usize,
    pub w1: usize,
    pub merged: Vec<u64>,
    pub cnts: Vec<u64>,
    pub sums: Vec<i128>,
}

/// The output of a phase-2 task.
pub struct Out2 {
    pub cnts: Vec<u64>,
    pub sums: Vec<i128>,
}

/// Counts and sums the qualifying rows of `[clo, chi)` per group id.
#[verifier::spinoff_prover]
fn count_rows(c: &Cols, sets: &Vec<Vec<u64>>, nsets: usize, range: u64, codes: &Vec<u8>, clo: usize, chi: usize,
    threshold: i128, w0: usize, w1: usize, merged: &Vec<u64>, cnts: &mut Vec<u64>, sums: &mut Vec<i128>,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    requires
        cols_ok(*c, sv), sets_ok(sets@, sv, nsets as int, range as int), range < u64::MAX,
        forall|s: int| 0 <= s < nsets ==> (#[trigger] sets@[s])@.len() == nwords(range as int),
        codes_ok(codes@, sv, ps, clo as int, chi as int, true), clo <= chi <= c.nc,
        avg_n(sv, ps) > 0, threshold as int == thr(sv, ps),
        w0 <= w1 <= nwords(range as int),
        merged_ok(merged@, sets@, nsets as int, w0 as int, w1 as int),
        old(cnts)@ == Seq::new(7, |g: int| 0u64), old(sums)@ == Seq::new(7, |g: int| 0i128),
    ensures gparts_ok(final(cnts)@, final(sums)@, sv, ps, clo as int, chi as int),
    no_unwind
{
    let mut i = clo;
    while i < chi
        invariant
            clo <= i <= chi, chi <= c.nc, cols_ok(*c, sv), sets_ok(sets@, sv, nsets as int, range as int), range < u64::MAX,
            forall|s: int| 0 <= s < nsets ==> (#[trigger] sets@[s])@.len() == nwords(range as int),
            codes_ok(codes@, sv, ps, clo as int, chi as int, true),
            avg_n(sv, ps) > 0, threshold as int == thr(sv, ps),
            w0 <= w1 <= nwords(range as int),
            merged_ok(merged@, sets@, nsets as int, w0 as int, w1 as int),
            gparts_ok(cnts@, sums@, sv, ps, clo as int, i as int),
        decreases chi - i,
    {
        let g = codes[i - clo];
        let ghost (c0, s0) = (cnts@, sums@);
        proof {
            assert(codes@[i - clo] == gid(sv, ps, i as int));
            lemma_grp(ps, code_of(sv, i as int));
            assert(num15(bal(sv)[i as int]));
        }
        let mut qualifies = false;
        if g < NONE {
            let v = c.bal[i];
            if v > threshold {
                let k = c.cck[i];
                let ordered = if k >= 0 && (k as u64) < range && (k as u64) / 64 >= w0 as u64 && (k as u64) / 64 < w1 as u64 {
                    let ku = k as u64;
                    let wi = (ku / 64) as usize;
                    let b = ku % 64;
                    proof {
                        lemma_sets_key(sets@, sv, nsets as int, range as int, k as int);
                        assert(wi as int == (k as int) / 64 && b as int == (k as int) % 64);
                        assert(wbit(merged@[wi - w0], b as int) == any_word(sets@, nsets as int, wi as int, b as int));
                        assert forall|s: int| 0 <= s < nsets implies #[trigger] bit_at(sets@[s]@, k as int)
                            == wbit(sets@[s]@[wi as int], b as int) by {}
                        if any_word(sets@, nsets as int, wi as int, b as int) {
                            let s = choose|s: int| 0 <= s < nsets && #[trigger] wbit(sets@[s]@[wi as int], b as int);
                            assert(bit_at(sets@[s]@, k as int));
                        }
                        if exists|s: int| 0 <= s < nsets && #[trigger] bit_at(sets@[s]@, k as int) {
                            let s = choose|s: int| 0 <= s < nsets && #[trigger] bit_at(sets@[s]@, k as int);
                            assert(wbit(sets@[s]@[wi as int], b as int));
                        }
                    }
                    (merged[wi - w0] >> b) & 1u64 == 1u64
                } else {
                    ord_check(c, sets, nsets, range, k, Ghost(sv))
                };
                if !ordered {
                    let gi = g as usize;
                    proof {
                        assert(gparts_ok(cnts@, sums@, sv, ps, clo as int, i as int));
                        assert(cnts@[gi as int] <= i - clo);
                        let cg = cnts@[gi as int] as int;
                        let sg = sums@[gi as int] as int;
                        assert(sg + v as int <= 999_999_999_999_999 * (cg + 1)) by (nonlinear_arith)
                            requires sg <= 999_999_999_999_999 * cg, v < 1_000_000_000_000_000;
                        assert(sg + v as int >= -999_999_999_999_999 * (cg + 1)) by (nonlinear_arith)
                            requires sg >= -999_999_999_999_999 * cg, v > -1_000_000_000_000_000;
                        assert(999_999_999_999_999 * (cg + 1) < 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff)
                            by (nonlinear_arith) requires cg + 1 <= 0x2000_0000_0000_0000;
                    }
                    cnts[gi] = cnts[gi] + 1;
                    sums[gi] = sums[gi] + v;
                    qualifies = true;
                }
            }
        }
        proof {
            assert(qualifies == qual(sv, ps, i as int));
            assert forall|g2: int| 0 <= g2 < 7 implies #[trigger] cnts@[g2] as int == range_sum(clo as int, i + 1, gcnt_term(sv, ps, g2))
                && sums@[g2] as int == range_sum(clo as int, i + 1, gsum_term(sv, ps, g2))
                && cnts@[g2] <= i + 1 - clo
                && -999_999_999_999_999 * (cnts@[g2] as int) <= sums@[g2] as int <= 999_999_999_999_999 * (cnts@[g2] as int) by {
                lemma_range_sum_step(clo as int, i as int, gcnt_term(sv, ps, g2));
                lemma_range_sum_step(clo as int, i as int, gsum_term(sv, ps, g2));
                assert(c0[g2] as int == range_sum(clo as int, i as int, gcnt_term(sv, ps, g2)));
                if !(qualifies && g2 == g as int) {
                    assert(cnts@[g2] == c0[g2] && sums@[g2] == s0[g2]);
                }
            }
        }
        i = i + 1;
    }
}

impl WorkerTask for Task2 {
    type Output = Out2;

    open spec fn pre(&self) -> bool {
        &&& cols_ok(self.c, self.sv@)
        &&& sets_ok((*self.sets)@, self.sv@, self.nsets as int, self.range as int)
        &&& self.range < u64::MAX
        &&& self.nw as int == nwords(self.range as int)
        &&& forall|s: int| 0 <= s < self.nsets ==> (#[trigger] (*self.sets)@[s])@.len() == nwords(self.range as int)
        &&& self.t < (*self.codes_all)@.len()
        &&& codes_ok((*self.codes_all)@[self.t as int]@, self.sv@, self.ps@, self.clo as int, self.chi as int, true)
        &&& self.clo <= self.chi <= self.c.nc
        &&& avg_n(self.sv@, self.ps@) > 0
        &&& self.thr as int == thr(self.sv@, self.ps@)
        &&& self.w0 <= self.w1 <= nwords(self.range as int)
        &&& self.merged@.len() == self.w1 - self.w0
        &&& forall|w: int| 0 <= w < self.merged@.len() ==> #[trigger] self.merged@[w] == 0u64
        &&& self.cnts@ == Seq::new(7, |g: int| 0u64)
        &&& self.sums@ == Seq::new(7, |g: int| 0i128)
    }

    open spec fn post(&self, out: Out2) -> bool {
        gparts_ok(out.cnts@, out.sums@, self.sv@, self.ps@, self.clo as int, self.chi as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.clo as u64, self.chi as u64)
    }

    fn run(self) -> (out: Out2) {
        let Task2 { c, sv, ps, sets, nsets, range, nw, codes_all, t, clo, chi, thr, w0, w1, merged, cnts, sums } = self;
        let mut merged = merged;
        let mut cnts = cnts;
        let mut sums = sums;
        let sets_ref: &Vec<Vec<u64>> = &*sets;
        merge_window(sets_ref, nsets, nw, w0, w1, &mut merged);
        let codes: &Vec<u8> = &codes_all[t];
        count_rows(&c, sets_ref, nsets, range, codes, clo, chi, thr, w0, w1, &merged, &mut cnts, &mut sums, sv, ps);
        Out2 { cnts, sums }
    }
}

} // verus!
