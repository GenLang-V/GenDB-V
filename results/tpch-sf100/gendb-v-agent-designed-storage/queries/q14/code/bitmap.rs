//! The promotion flag of every stored part row as a bitmap, built per call.
//!
//! Bit `r % 64` of word `r / 64` is set exactly when part row `r`'s p_type is `LIKE 'PROMO%'` (`bits_ok`). The
//! bitmap (one bit per part, 2.5 MB at scale factor 100) stays in cache while the scan looks parts up at random,
//! where the p_type codes (one byte per part) would not. It is computed inside the call from the stored p_type
//! codes and the dictionary entries' LIKE results (`kernel::promo_ok`); nothing of it is stored.
//!
//! Words are built in parallel ranges (`BuildTask`, `build_words`) and concatenated on the calling thread.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::parallel::{Dispatch, fork_join, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use super::model::*;
use super::terms::*;
use super::kernel::*;

verus! {

// ------------------------------------------------------------------------------------------------ bits

/// Bit `b` of word `x`.
pub open spec fn bit(x: u64, b: int) -> bool {
    ((x >> (b as u64)) & 1u64) == 1u64
}

/// Number of words of a bitmap of `n` bits.
pub open spec fn nwords(n: int) -> int {
    (n + 63) / 64
}

/// `2^s` as an integer.
pub open spec fn p2(s: int) -> int {
    vstd::arithmetic::power2::pow2(s as nat) as int
}

/// The promotion bitmap of the stored part rows in blocks of `2^s` words: bit `r % 64` of word `x % 2^s` of block
/// `x / 2^s`, `x = r / 64`, is part row `r`'s promotion flag.
pub open spec fn bits_ok(blocks: Seq<Vec<u64>>, s: int, cp: Seq<PartView>) -> bool {
    &&& 0 <= s < 64
    &&& forall|r: int| 0 <= r < n_pa(cp) ==> {
        &&& #[trigger] bit_in(blocks, s, r) == promo_text(ptype_at(cp, r))
        &&& (r / 64) / p2(s) < blocks.len()
        &&& (r / 64) % p2(s) < blocks[(r / 64) / p2(s)]@.len()
    }
}

/// Bit `r` of a blocked bitmap.
pub open spec fn bit_in(blocks: Seq<Vec<u64>>, s: int, r: int) -> bool {
    bit(blocks[(r / 64) / p2(s)]@[(r / 64) % p2(s)], r % 64)
}

/// Setting bit `b` by `f` (0 or 1) keeps the other bits.
pub proof fn lemma_bit_or(x: u64, f: u64, b: u64, c: u64)
    requires f <= 1, b < 64, c < 64,
    ensures
        bit(x | (f << b), c as int) == if c == b { bit(x, c as int) || f == 1 } else { bit(x, c as int) },
{
    assert(((((x | (f << b)) >> c) & 1u64) == 1u64) == if c == b { (((x >> c) & 1u64) == 1u64) || f == 1u64 } else { ((x >> c) & 1u64) == 1u64 }) by (bit_vector)
        requires f <= 1, b < 64, c < 64;
}

/// Every bit of 0 is clear.
pub proof fn lemma_bit_zero(c: u64)
    requires c < 64,
    ensures (0u64 >> c) & 1u64 == 0u64,
{
    assert((0u64 >> c) & 1u64 == 0u64) by (bit_vector);
}

/// Word index and bit position of a row by shifts.
pub proof fn lemma_shift_div(r: u64)
    ensures r >> 6u64 == r / 64, r & 63u64 == r % 64,
{
    assert(r >> 6u64 == r / 64) by (bit_vector);
    assert(r & 63u64 == r % 64) by (bit_vector);
}

/// The bit of `x` at `b` is 0 or 1.
pub proof fn lemma_bit_01(x: u64, b: u64)
    ensures (x >> b) & 1u64 <= 1u64,
{
    assert((x >> b) & 1u64 <= 1u64) by (bit_vector);
}

// ------------------------------------------------------------------------------------------------ building

/// The 64 rows of word `x` lie in one part group of 65536 rows.
pub proof fn lemma_same_block(x: int, b: int)
    requires 0 <= x, 0 <= b < 64,
    ensures (64 * x + b) / 65536 == (64 * x) / 65536,
{
    let q = x / 1024;
    let rr = x % 1024;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, 1024);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(x, 1024);
    assert(64 * x + b == q * 65536 + (64 * rr + b)) by (nonlinear_arith)
        requires x == 1024 * q + rr;
    assert(64 * x == q * 65536 + 64 * rr) by (nonlinear_arith)
        requires x == 1024 * q + rr;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(64 * x + b, 65536, q, 64 * rr + b);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(64 * x, 65536, q, 64 * rr);
}

/// Word `x` of the bitmap: bits of the part rows `64 x .. 64 x + 63` (rows from `n` on clear).
pub open spec fn word_ok(w: u64, cp: Seq<PartView>, x: int) -> bool {
    forall|b: int| 0 <= b < 64 && 64 * x + b < n_pa(cp) ==> #[trigger] bit(w, b) == promo_text(ptype_at(cp, 64 * x + b))
}

/// Word `x` of the bitmap (part rows in uniform groups of 65536, so the 64 rows share their group's base);
/// `flags[e]` is 1 when p_type dictionary entry `e` is a promotion type, else 0.
pub fn build_word(p: &PaCols, flags: &Vec<u64>, x: usize, Ghost(cp): Ghost<Seq<PartView>>) -> (w: u64)
    requires
        look_ok(*p, cp),
        flags_ok(flags@, cp),
        64 * x < p.n,
    ensures
        word_ok(w, cp, x as int),
    no_unwind
{
    let r0 = 64 * x;
    proof {
        lemma_part_lookup(*p, cp, r0 as int);
    }
    let base = p.ty_base[r0 / 65536];
    let nb: usize = if p.n - r0 >= 64 { 64 } else { p.n - r0 };
    let nf = flags.len();
    let mut w: u64 = 0;
    let mut b: usize = 0;
    proof {
        assert forall|c: int| 0 <= c < 64 implies !#[trigger] bit(0u64, c) by {
            lemma_bit_zero(c as u64);
        }
    }
    while b < nb
        invariant
            look_ok(*p, cp),
            flags_ok(flags@, cp),
            nf == flags@.len(),
            r0 == 64 * x, r0 < p.n,
            r0 as int / 65536 < p.ty_base@.len(),
            base == p.ty_base@[r0 as int / 65536],
            nb <= 64, r0 + nb <= p.n,
            b <= nb,
            forall|c: int| 0 <= c < b ==> #[trigger] bit(w, c) == promo_text(ptype_at(cp, r0 + c)),
            forall|c: int| b <= c < 64 ==> !#[trigger] bit(w, c),
        decreases nb - b,
    {
        let r = r0 + b;
        proof {
            lemma_part_lookup(*p, cp, r as int);
            lemma_same_block(x as int, b as int);
            assert(tidx_at(cp, r as int) == base + p.ty@[r as int]);
        }
        let f = flags[(base + p.ty[r] as u64) as usize];
        proof {
            assert forall|c: int| 0 <= c < 64 implies #[trigger] bit(w | (f << (b as u64)), c)
                == if c == b { bit(w, c) || f == 1 } else { bit(w, c) } by {
                lemma_bit_or(w, f, b as u64, c as u64);
            }
        }
        let ghost w0 = w;
        w = w | (f << (b as u64));
        proof {
            assert(!bit(w0, b as int));
            assert(f == if promo_text(ptype_at(cp, r as int)) { 1u64 } else { 0u64 });
            assert(bit(w, b as int) == promo_text(ptype_at(cp, r0 + b)));
            assert forall|c: int| 0 <= c < b + 1 implies #[trigger] bit(w, c) == promo_text(ptype_at(cp, r0 + c)) by {
                if c < b {
                    assert(bit(w, c) == bit(w0, c));
                }
            }
            assert forall|c: int| b + 1 <= c < 64 implies !#[trigger] bit(w, c) by {
                assert(bit(w, c) == bit(w0, c));
            }
        }
        b = b + 1;
    }
    proof {
        assert forall|c: int| 0 <= c < 64 && 64 * x + c < n_pa(cp) implies #[trigger] bit(w, c) == promo_text(ptype_at(cp, 64 * x + c)) by {
            assert(r0 + c == 64 * x + c);
        }
    }
    w
}

/// `flags[e]` is 1 exactly when p_type dictionary entry `e` is a promotion type, else 0.
pub open spec fn flags_ok(flags: Seq<u64>, cp: Seq<PartView>) -> bool {
    &&& flags.len() == n_td(cp)
    &&& forall|e: int| 0 <= e < n_td(cp) ==> #[trigger] flags[e] == if promo_text(tdict(cp, e)) { 1u64 } else { 0u64 }
}

/// The promotion flags as words.
pub fn flag_words(promo: &Vec<bool>, Ghost(cp): Ghost<Seq<PartView>>) -> (r: Vec<u64>)
    requires promo_ok(promo@, cp),
    ensures flags_ok(r@, cp),
{
    let mut r: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < promo.len()
        invariant
            promo_ok(promo@, cp),
            i <= promo@.len(),
            r@.len() == i,
            forall|e: int| 0 <= e < i ==> #[trigger] r@[e] == if promo_text(tdict(cp, e)) { 1u64 } else { 0u64 },
        decreases promo@.len() - i,
    {
        r.push(if promo[i] { 1 } else { 0 });
        i = i + 1;
    }
    r
}

/// The words `x_lo .. x_lo + out.len()` of the bitmap, into `out`.
pub fn build_words(p: &PaCols, flags: &Vec<u64>, x_lo: usize, out: &mut Vec<u64>, Ghost(cp): Ghost<Seq<PartView>>)
    requires
        look_ok(*p, cp),
        flags_ok(flags@, cp),
        x_lo + old(out)@.len() <= nwords(p.n as int),
    ensures
        final(out)@.len() == old(out)@.len(),
        forall|i: int| 0 <= i < final(out)@.len() ==> #[trigger] word_ok(final(out)@[i], cp, x_lo + i),
    no_unwind
{
    let nw = out.len();
    let mut i: usize = 0;
    while i < nw
        invariant
            look_ok(*p, cp),
            flags_ok(flags@, cp),
            nw == out@.len(),
            x_lo + nw <= nwords(p.n as int),
            i <= nw,
            forall|k: int| 0 <= k < i ==> #[trigger] word_ok(out@[k], cp, x_lo + k),
        decreases nw - i,
    {
        let x = x_lo + i;
        proof {
            assert(64 * x < p.n) by (nonlinear_arith)
                requires x < nwords(p.n as int), nwords(p.n as int) == (p.n + 63) / 64;
        }
        let wv = build_word(p, flags, x, Ghost(cp));
        crate::gendb_entry::work::put(out, i, wv);
        i = i + 1;
    }
}

/// Word `x` lies in block `x / per` of the blocks `bl`, inside its length.
pub open spec fn in_block(bl: Seq<Vec<u64>>, per: int, x: int) -> bool {
    x / per < bl.len() && x % per < bl[x / per]@.len()
}

/// The blocks of `2^s` words built by the tasks are the bitmap.
pub proof fn lemma_bits_from_blocks(blocks: Seq<Vec<u64>>, s: int, ps: int, cp: Seq<PartView>)
    requires
        0 <= s < 64,
        ps == p2(s),
        forall|k: int, i: int| 0 <= k < blocks.len() && 0 <= i < blocks[k]@.len() ==> #[trigger] word_ok(blocks[k]@[i], cp, k * ps + i),
        forall|x: int| 0 <= x < nwords(n_pa(cp)) ==> #[trigger] in_block(blocks, ps, x),
    ensures
        bits_ok(blocks, s, cp),
{
    vstd::arithmetic::power2::lemma_pow2_pos(s as nat);
    assert forall|r: int| 0 <= r < n_pa(cp) implies #[trigger] bit_in(blocks, s, r) == promo_text(ptype_at(cp, r)) && {
        &&& (r / 64) / p2(s) < blocks.len()
        &&& (r / 64) % p2(s) < (blocks[(r / 64) / p2(s)])@.len()
    } by {
        let x = r / 64;
        let b = r % 64;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(r, 64);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(r, 64);
        assert(r == 64 * x + b && 0 <= b < 64);
        assert(0 <= x < nwords(n_pa(cp))) by (nonlinear_arith)
            requires x == r / 64, 0 <= r < n_pa(cp), nwords(n_pa(cp)) == (n_pa(cp) + 63) / 64, r == 64 * x + b, 0 <= b < 64;
        let k = x / ps;
        let i = x % ps;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, ps);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(x, ps);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(x, ps);
        assert(x == k * ps + i) by (nonlinear_arith) requires x == ps * k + i;
        assert(in_block(blocks, ps, x));
        assert(i < blocks[x / ps]@.len());
        assert(k < blocks.len());
        let wv = blocks[k]@[i];
        assert(word_ok(wv, cp, k * ps + i));
        assert(64 * (k * ps + i) + b == r);
        assert(bit(wv, b) == promo_text(ptype_at(cp, 64 * (k * ps + i) + b)));
    }
}

/// One worker's block of the bitmap: words `x_lo .. x_lo + out.len()`.
pub struct BuildTask {
    pub pa: PaCols,
    pub flags: Vec<u64>,
    pub x_lo: usize,
    pub out: Vec<u64>,
    pub cp: Ghost<Seq<PartView>>,
}

impl WorkerTask for BuildTask {
    type Output = Vec<u64>;

    open spec fn pre(&self) -> bool {
        &&& look_ok(self.pa, self.cp@)
        &&& flags_ok(self.flags@, self.cp@)
        &&& self.x_lo + self.out@.len() <= nwords(self.pa.n as int)
    }

    open spec fn post(&self, out: Vec<u64>) -> bool {
        &&& out@.len() == self.out@.len()
        &&& forall|i: int| 0 <= i < out@.len() ==> #[trigger] word_ok(out@[i], self.cp@, self.x_lo + i)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.x_lo as u64, self.x_lo as u64)
    }

    fn run(self) -> (r: Vec<u64>) {
        let mut out = self.out;
        build_words(&self.pa, &self.flags, self.x_lo, &mut out, self.cp);
        out
    }
}

/// Words of block `k` of `2^s` words of a bitmap of `nw` words: `k 2^s .. min((k + 1) 2^s, nw)`.
pub open spec fn blen(k: int, per: int, nw: int) -> int {
    if (k + 1) * per <= nw { per } else { nw - k * per }
}

/// Facts of the block partition: every word lies in its block, inside the block's length.
pub proof fn lemma_blocks_cover(nw: int, per: int, nb: int, x: int)
    requires
        per >= 1,
        nb == nw / per + 1,
        0 <= x < nw,
    ensures
        0 <= x / per < nb,
        (x / per) * per <= nw,
        0 <= x % per < blen(x / per, per, nw),
        x == (x / per) * per + x % per,
{
    let k = x / per;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, per);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(x, per);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(x, per);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(x, nw, per);
    assert(per * k == k * per) by (nonlinear_arith);
}

/// The promotion bitmap of the part rows in blocks of `2^s` words, one block per task, at most `workers` tasks.
pub fn build_bitmap(p: &PaCols, promo: &Vec<bool>, workers: usize, dispatch: &mut Dispatch,
    Ghost(cp): Ghost<Seq<PartView>>) -> (r: Result<(Vec<Vec<u64>>, u64), QueryError>)
    requires
        look_ok(*p, cp),
        promo_ok(promo@, cp),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok((v, s)) ==> bits_ok(v@, s as int, cp),
        r matches Err(e) ==> e is WorkerFailed,
{
    let nw = p.n / 64 + if p.n % 64 == 0 { 0 } else { 1 };
    proof {
        assert(nw == nwords(p.n as int)) by (nonlinear_arith)
            requires nw == p.n / 64 + if p.n % 64 == 0 { 0int } else { 1int }, p.n >= 0;
        assert(nw <= 0x400_0000_0000_0000) by (nonlinear_arith)
            requires nw <= p.n / 64 + 1, p.n <= 0xffff_ffff_ffff_ffff;
    }
    // The smallest block size 2^s (at least 2^10 words) giving at most `workers` blocks.
    let mut s: u64 = 10;
    while s < 62 && (nw as u64 >> s) >= workers as u64
        invariant 10 <= s <= 62,
        decreases 62 - s,
    {
        s = s + 1;
    }
    proof {
        vstd::bits::lemma_u64_shr_is_div(nw as u64, s);
        vstd::bits::lemma_u64_pow2_no_overflow(s as nat);
        vstd::bits::lemma_u64_shl_is_mul(1u64, s);
        vstd::arithmetic::power2::lemma_pow2_pos(s as nat);
        if s == 62 {
            vstd::arithmetic::power2::lemma2_to64_rest();
            assert(nw as int / p2(62) == 0) by (nonlinear_arith)
                requires 0 <= nw <= 0x400_0000_0000_0000, p2(62) == 0x4000_0000_0000_0000;
        }
    }
    let per: u64 = 1u64 << s;
    let nb = (nw as u64 >> s) as usize + 1;
    let ghost pi = per as int;
    proof {
        assert(per as int == p2(s as int));
        assert(nb as int == nw as int / pi + 1);
        assert(nb <= workers);
        assert((nw as int / pi) * pi <= nw) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(nw as int, pi);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(nw as int, pi);
            assert(pi * (nw as int / pi) == (nw as int / pi) * pi) by (nonlinear_arith);
        }
        assert(nb * pi <= nw + pi) by (nonlinear_arith)
            requires nb == nw as int / pi + 1, (nw as int / pi) * pi <= nw;
        assert(pi <= 0x4000_0000_0000_0000) by {
            vstd::arithmetic::power2::lemma2_to64_rest();
            if s < 62 {
                vstd::arithmetic::power2::lemma_pow2_strictly_increases(s as nat, 62);
            }
        }
    }
    let flags = flag_words(promo, Ghost(cp));
    let mut tasks: Vec<BuildTask> = Vec::new();
    let mut k: usize = 0;
    while k < nb
        invariant
            look_ok(*p, cp),
            flags_ok(flags@, cp),
            nw == nwords(p.n as int),
            nw <= 0x400_0000_0000_0000,
            pi == per as int, pi >= 1, pi <= 0x4000_0000_0000_0000,
            pi == p2(s as int), s < 64,
            nb == nw as int / pi + 1,
            nb * pi <= nw + pi,
            (nw as int / pi) * pi <= nw,
            k <= nb,
            tasks@.len() == k,
            forall|i: int| 0 <= i < k ==> (#[trigger] tasks@[i]).pre() && tasks@[i].cp@ == cp
                && tasks@[i].x_lo == i * pi && tasks@[i].out@.len() == blen(i, pi, nw as int),
        decreases nb - k,
    {
        proof {
            assert(k * pi <= (nw as int / pi) * pi) by (nonlinear_arith)
                requires k <= nw as int / pi, pi >= 1;
            assert((k + 1) * pi <= nb * pi) by (nonlinear_arith)
                requires k + 1 <= nb, pi >= 1;
        }
        proof {
            assert((k + 1) * pi == k * pi + pi) by (nonlinear_arith);
            assert(k * pi >= 0) by (nonlinear_arith) requires k >= 0, pi >= 1;
        }
        let lo = (k as u64 * per) as usize;
        let hi = if (k as u64 + 1) * per <= nw as u64 { ((k as u64 + 1) * per) as usize } else { nw };
        proof {
            assert(lo == k * pi);
            assert(lo <= hi);
            assert(hi - lo == blen(k as int, pi, nw as int));
            assert(hi <= nw);
        }
        let task = BuildTask { pa: *p, flags: copy_words(&flags), x_lo: lo, out: vec![0u64; hi - lo], cp: Ghost(cp) };
        tasks.push(task);
        k = k + 1;
    }
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    proof {
        let bl = outs@;
        let si = s as int;
        assert(pi == p2(si));
        assert forall|kk: int, i: int| 0 <= kk < bl.len() && 0 <= i < bl[kk]@.len() implies #[trigger] word_ok(bl[kk]@[i], cp, kk * pi + i) by {
            assert(tv[kk].post(outs@[kk]));
        }
        assert forall|x: int| 0 <= x < nwords(n_pa(cp)) implies #[trigger] in_block(bl, pi, x) by {
            lemma_blocks_cover(nw as int, pi, nb as int, x);
            assert(tv[x / pi].post(outs@[x / pi]));
        }
        lemma_bits_from_blocks(bl, si, pi, cp);
    }
    Ok((outs, s))
}

/// A copy of a word vector.
pub fn copy_words(v: &Vec<u64>) -> (r: Vec<u64>)
    ensures r@ == v@,
{
    let mut r: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v.len(), r@ == v@.subrange(0, i as int),
        decreases v.len() - i,
    {
        r.push(v[i]);
        proof {
            assert(v@.subrange(0, i + 1) =~= v@.subrange(0, i as int).push(v@[i as int]));
        }
        i = i + 1;
    }
    proof {
        assert(v@.subrange(0, v@.len() as int) =~= v@);
    }
    r
}

/// A copy of a flag vector.
pub fn copy_flags(v: &Vec<bool>) -> (r: Vec<bool>)
    ensures r@ == v@,
{
    let mut r: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v.len(), r@ == v@.subrange(0, i as int),
        decreases v.len() - i,
    {
        r.push(v[i]);
        proof {
            assert(v@.subrange(0, i + 1) =~= v@.subrange(0, i as int).push(v@[i as int]));
        }
        i = i + 1;
    }
    proof {
        assert(v@.subrange(0, v@.len() as int) =~= v@);
    }
    r
}

} // verus!
