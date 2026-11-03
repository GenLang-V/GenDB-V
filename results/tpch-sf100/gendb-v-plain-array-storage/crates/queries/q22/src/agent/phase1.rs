//! Phase 1: one task per worker. Task `t` (1) marks, in its own bit set of the customer keys `0..range`, every key
//! that its orders range `[olo, ohi)` holds (`keys_ok`), and (2) computes the group id of every customer row of its
//! customer range `[clo, chi)` with the fast test (`SLOW` where it cannot decide) together with the AVG
//! population's count and balance sum over the range, exact when no row was `SLOW` (`codes_ok`, `avg_part_ok`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::ast::Literal;
use crate::gendb_entry::parallel::WorkerTask;
use crate::gendb_entry::stores::StoresView;
use crate::agent::common::bitset::*;
use crate::agent::common::rsum::*;
use crate::agent::common::slice_marks::*;
use crate::agent::tables::*;
use crate::agent::normal::*;
use crate::agent::cols::*;
use crate::agent::codes::*;

verus! {

/// Some orders row of `[lo, hi)` has customer key `k`.
pub open spec fn ord_in(sv: StoresView, k: int, lo: int, hi: int) -> bool {
    exists|j: int| lo <= j < hi && #[trigger] ock(sv)[j] as int == k
}

/// Words of a bit set over the keys `0..range`.
pub open spec fn nwords(range: int) -> int { range / 64 + 1 }

/// The bit set marks exactly the keys below `range` that orders rows `[lo, hi)` hold.
pub open spec fn keys_ok(bits: Seq<u64>, sv: StoresView, lo: int, hi: int, range: int) -> bool {
    &&& bits.len() == nwords(range)
    &&& forall|k: int| 0 <= k < range ==> (#[trigger] bit_at(bits, k) == ord_in(sv, k, lo, hi))
}

/// Group ids of rows `[lo, hi)`, entry `r - lo` for row `r`: exact or `SLOW`, and exact everywhere when `exact`.
pub open spec fn codes_ok(codes: Seq<u8>, sv: StoresView, ps: Seq<Literal>, lo: int, hi: int, exact: bool) -> bool {
    &&& codes.len() == hi - lo
    &&& forall|r: int| lo <= r < hi ==> (#[trigger] codes[r - lo] == SLOW && !exact) || codes[r - lo] == gid(sv, ps, r)
}

/// Bounds of a partial AVG count and sum over `m` rows (every balance below `10^15`).
pub open spec fn avg_bounds(sum: int, cnt: int, m: int) -> bool {
    0 <= cnt <= m && 0 <= sum <= 999_999_999_999_999 * cnt
}

/// The AVG population's count and sum over rows `[lo, hi)`, when `exact`.
pub open spec fn avg_part_ok(sum: int, cnt: int, sv: StoresView, ps: Seq<Literal>, lo: int, hi: int, exact: bool) -> bool {
    &&& avg_bounds(sum, cnt, hi - lo)
    &&& exact ==> sum == range_sum(lo, hi, avg_sum_term(sv, ps)) && cnt == range_sum(lo, hi, avg_cnt_term(sv, ps))
}

/// A zero word has no bit set.
#[verifier::spinoff_prover]
pub proof fn lemma_zero_bits(words: Seq<u64>)
    requires forall|w: int| 0 <= w < words.len() ==> #[trigger] words[w] == 0u64,
    ensures forall|k: int| 0 <= k && k / 64 < words.len() ==> !(#[trigger] bit_at(words, k)),
{
    assert forall|k: int| 0 <= k && k / 64 < words.len() implies !(#[trigger] bit_at(words, k)) by {
        let s = (k % 64) as u64;
        assert(words[k / 64] == 0u64);
        assert((0u64 >> s) & 1u64 == 0u64) by (bit_vector);
    }
}

/// One phase-1 task.
pub struct Task1 {
    pub c: Cols,
    pub lut: Arc<Vec<u8>>,
    pub sv: Ghost<StoresView>,
    pub ps: Ghost<Seq<Literal>>,
    pub olo: usize,
    pub ohi: usize,
    pub range: u64,
    pub bits: Vec<u64>,
    pub clo: usize,
    pub chi: usize,
    pub codes: Vec<u8>,
    /// Scratch space of the chunked marking (`common::slice_marks`): `np` groups of `cap` slots, key slices of
    /// `2^shift` keys, chunks of `chunk` orders rows; `np == 0` marks key by key.
    pub buf: Vec<u32>,
    pub fill: Vec<usize>,
    pub shift: u64,
    pub np: usize,
    pub cap: usize,
    pub chunk: usize,
}

/// The output of a phase-1 task.
pub struct Out1 {
    pub bits: Vec<u64>,
    pub codes: Vec<u8>,
    pub sum: i128,
    pub cnt: u64,
    pub slow: u64,
}

/// What a phase-1 task's output says about its ranges.
pub open spec fn out1_ok(o: Out1, sv: StoresView, ps: Seq<Literal>, olo: int, ohi: int, range: int, clo: int, chi: int) -> bool {
    &&& keys_ok(o.bits@, sv, olo, ohi, range)
    &&& codes_ok(o.codes@, sv, ps, clo, chi, o.slow == 0)
    &&& avg_part_ok(o.sum as int, o.cnt as int, sv, ps, clo, chi, o.slow == 0)
}

/// Every key below `range` has its bit in a bit set of `nwords(range)` words.
#[verifier::spinoff_prover]
pub proof fn lemma_bits_cover(bits: Seq<u64>, range: int)
    requires bits.len() == nwords(range), range >= 0,
    ensures forall|k: int| 0 <= k < range ==> in_bits(bits, k),
{
    assert forall|k: int| 0 <= k < range implies in_bits(bits, k) by {
        vstd::arithmetic::div_mod::lemma_div_is_ordered(k, range, 64);
    }
}

/// The keys marked from the `o_custkey` slice are the keys of the orders rows.
#[verifier::spinoff_prover]
pub proof fn lemma_marks_keys(bits: Seq<u64>, sv: StoresView, lo: int, hi: int, range: int)
    requires marks_ok(bits, ock(sv), lo, hi, range), bits.len() == nwords(range),
    ensures keys_ok(bits, sv, lo, hi, range),
{
    assert forall|k: int| 0 <= k < range implies (#[trigger] bit_at(bits, k) == ord_in(sv, k, lo, hi)) by {
        if key_in(ock(sv), k, lo, hi) {
            let j = choose|j: int| lo <= j < hi && #[trigger] ock(sv)[j] as int == k;
            assert(ord_in(sv, k, lo, hi));
        }
        if ord_in(sv, k, lo, hi) {
            let j = choose|j: int| lo <= j < hi && #[trigger] ock(sv)[j] as int == k;
            assert(key_in(ock(sv), k, lo, hi));
        }
    }
}

/// Marks the keys of the orders range `[olo, ohi)` in a zero bit set.
#[verifier::spinoff_prover]
fn mark_keys(c: &Cols, olo: usize, ohi: usize, range: u64, bits: &mut Vec<u64>, Ghost(sv): Ghost<StoresView>)
    requires
        cols_ok(*c, sv), olo <= ohi <= c.no, range < u64::MAX,
        old(bits)@.len() == nwords(range as int),
        forall|w: int| 0 <= w < old(bits)@.len() ==> #[trigger] old(bits)@[w] == 0u64,
    ensures keys_ok(final(bits)@, sv, olo as int, ohi as int, range as int),
    no_unwind
{
    proof { lemma_zero_bits(bits@); }
    let mut j = olo;
    while j < ohi
        invariant
            olo <= j <= ohi, ohi <= c.no, cols_ok(*c, sv), range < u64::MAX,
            bits@.len() == nwords(range as int),
            forall|k: int| 0 <= k < range ==> (#[trigger] bit_at(bits@, k) == ord_in(sv, k, olo as int, j as int)),
        decreases ohi - j,
    {
        let k = c.ock[j];
        let ghost old_bits = bits@;
        if k >= 0 && (k as u64) < range {
            proof { assert((k as int) / 64 < nwords(range as int)); }
            test_set(bits, k as u64);
        }
        proof {
            assert forall|k2: int| 0 <= k2 < range implies (#[trigger] bit_at(bits@, k2) == ord_in(sv, k2, olo as int, j + 1)) by {
                assert(k2 / 64 < nwords(range as int));
                if ock(sv)[j as int] as int == k2 {
                    assert(ord_in(sv, k2, olo as int, j + 1));
                } else {
                    assert(bit_at(bits@, k2) == bit_at(old_bits, k2));
                    if ord_in(sv, k2, olo as int, j + 1) {
                        let jj = choose|jj: int| olo <= jj < j + 1 && #[trigger] ock(sv)[jj] as int == k2;
                        assert(jj < j);
                    }
                }
            }
        }
        j = j + 1;
    }
}

/// Group ids and AVG partials of the customer range `[clo, chi)`; returns `(sum, count, slow rows)`.
#[verifier::spinoff_prover]
fn scan_customers(c: &Cols, lut: &Vec<u8>, clo: usize, chi: usize, codes: &mut Vec<u8>,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: (i128, u64, u64))
    requires
        cols_ok(*c, sv), lut_ok(lut@, ps), clo <= chi <= c.nc, old(codes)@.len() == chi - clo,
    ensures
        codes_ok(final(codes)@, sv, ps, clo as int, chi as int, r.2 == 0),
        avg_part_ok(r.0 as int, r.1 as int, sv, ps, clo as int, chi as int, r.2 == 0),
    no_unwind
{
    let mut sum: i128 = 0;
    let mut cnt: u64 = 0;
    let mut slow: u64 = 0;
    let mut i = clo;
    while i < chi
        invariant
            clo <= i <= chi, chi <= c.nc, cols_ok(*c, sv), lut_ok(lut@, ps),
            codes@.len() == chi - clo,
            slow <= i - clo,
            forall|r: int| clo <= r < i ==> (#[trigger] codes@[r - clo] == SLOW && slow != 0) || codes@[r - clo] == gid(sv, ps, r),
            avg_part_ok(sum as int, cnt as int, sv, ps, clo as int, i as int, slow == 0),
        decreases chi - i,
    {
        let g = fast_code(c, lut, i, Ghost(sv), Ghost(ps));
        let ghost old_codes = codes@;
        codes[i - clo] = g;
        proof {
            lemma_grp(ps, code_of(sv, i as int));
            assert(num15(bal(sv)[i as int]));
        }
        if g < NONE {
            let v = c.bal[i];
            if v > 0 {
                proof {
                    assert(sum as int + v as int <= 999_999_999_999_999 * (cnt as int + 1)) by (nonlinear_arith)
                        requires sum as int <= 999_999_999_999_999 * (cnt as int), v < 1_000_000_000_000_000;
                    assert(999_999_999_999_999 * (cnt as int + 1) < 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff)
                        by (nonlinear_arith) requires cnt as int + 1 <= 0x2000_0000_0000_0000;
                }
                sum = sum + v;
                cnt = cnt + 1;
            }
        } else if g == SLOW {
            slow = slow + 1;
        }
        proof {
            if slow == 0 {
                lemma_range_sum_step(clo as int, i as int, avg_sum_term(sv, ps));
                lemma_range_sum_step(clo as int, i as int, avg_cnt_term(sv, ps));
            }
            assert forall|r: int| clo <= r < i + 1 implies (#[trigger] codes@[r - clo] == SLOW && slow != 0) || codes@[r - clo] == gid(sv, ps, r) by {
                if r < i {
                    assert(codes@[r - clo] == old_codes[r - clo]);
                }
            }
        }
        i = i + 1;
    }
    (sum, cnt, slow)
}

impl WorkerTask for Task1 {
    type Output = Out1;

    open spec fn pre(&self) -> bool {
        &&& cols_ok(self.c, self.sv@)
        &&& lut_ok((*self.lut)@, self.ps@)
        &&& self.olo <= self.ohi <= self.c.no
        &&& self.clo <= self.chi <= self.c.nc
        &&& self.range < u64::MAX
        &&& self.bits@.len() == nwords(self.range as int)
        &&& forall|w: int| 0 <= w < self.bits@.len() ==> #[trigger] self.bits@[w] == 0u64
        &&& self.codes@.len() == self.chi - self.clo
        &&& self.buf@.len() == self.np * self.cap
        &&& self.fill@.len() == self.np
        &&& self.shift < 64
        &&& 1 <= self.chunk
    }

    open spec fn post(&self, out: Out1) -> bool {
        out1_ok(out, self.sv@, self.ps@, self.olo as int, self.ohi as int, self.range as int, self.clo as int, self.chi as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.olo as u64, self.ohi as u64)
    }

    fn run(self) -> (out: Out1) {
        let Task1 { c, lut, sv, ps, olo, ohi, range, bits, clo, chi, codes, buf, fill, shift, np, cap, chunk } = self;
        let mut bits = bits;
        let mut codes = codes;
        let mut buf = buf;
        let mut fill = fill;
        if np > 0 && range <= 0x1_0000_0000 {
            proof { lemma_bits_cover(bits@, range as int); }
            mark_chunked(c.ock, olo, ohi, range, &mut bits, &mut buf, &mut fill, shift, np, cap, chunk);
            proof { lemma_marks_keys(bits@, sv@, olo as int, ohi as int, range as int); }
        } else {
            mark_keys(&c, olo, ohi, range, &mut bits, sv);
        }
        let (sum, cnt, slow) = scan_customers(&c, &*lut, clo, chi, &mut codes, sv, ps);
        Out1 { bits, codes, sum, cnt, slow }
    }
}

} // verus!
