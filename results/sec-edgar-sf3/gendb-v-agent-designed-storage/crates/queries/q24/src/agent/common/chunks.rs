//! `n` `u64` values kept as chunks of `size = 2^shift` values (chunk `c` holds values `[c * size, min((c + 1) *
//! size, n))`), so parallel tasks can each fill one chunk and readers look a value up by shift and mask, without
//! concatenating the chunks into one vector.
use vstd::prelude::*;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse};
use vstd::arithmetic::power2::pow2;
use vstd::bits::low_bits_mask;

verus! {

/// Length of chunk `c` of `n` values in chunks of `size`.
pub open spec fn chunk_len(size: int, n: int, c: int) -> int {
    if n - c * size < 0 { 0 } else if n - c * size < size { n - c * size } else { size }
}

/// `cs` holds `n` values in chunks of `size`.
pub open spec fn chunks_shape(cs: Seq<Vec<u64>>, size: int, n: int) -> bool {
    &&& size >= 1
    &&& n >= 0
    &&& n <= cs.len() * size
    &&& forall|c: int| 0 <= c < cs.len() ==> (#[trigger] cs[c])@.len() == chunk_len(size, n, c)
}

/// Value `q` of the chunked values.
pub open spec fn chunk_at(cs: Seq<Vec<u64>>, size: int, q: int) -> u64 {
    cs[q / size]@[q % size]
}

/// The chunked values as one sequence.
pub open spec fn chunks_seq(cs: Seq<Vec<u64>>, size: int, n: int) -> Seq<u64> {
    Seq::new(n as nat, |q: int| chunk_at(cs, size, q))
}

/// Position `c * size + r` (`0 <= r < size`) is offset `r` of chunk `c`.
pub proof fn lemma_chunk_pos(size: int, c: int, r: int)
    requires size >= 1, 0 <= r < size,
    ensures (c * size + r) / size == c, (c * size + r) % size == r,
{
    lemma_fundamental_div_mod_converse(c * size + r, size, c, r);
}

/// Value `q < n` lies in chunk `q / size` at offset `q % size`, both in bounds.
pub proof fn lemma_chunk_index(cs: Seq<Vec<u64>>, size: int, n: int, q: int)
    requires chunks_shape(cs, size, n), 0 <= q < n,
    ensures 0 <= q / size < cs.len(), 0 <= q % size < cs[q / size]@.len(),
{
    let c = q / size;
    let r = q % size;
    lemma_fundamental_div_mod(q, size);
    assert(0 <= r < size);
    assert(c >= 0) by (nonlinear_arith) requires q >= 0, size >= 1, c == q / size;
    assert(c < cs.len()) by (nonlinear_arith) requires q == size * c + r, r >= 0, q < n, n <= cs.len() * size, size >= 1;
    assert(n - c * size > r) by (nonlinear_arith) requires q == size * c + r, q < n;
}

/// `q >> shift` and `q & (size - 1)` are the chunk and the offset of `q` for `size == 1 << shift`.
pub proof fn lemma_shift_mask(q: u64, shift: u64, size: u64)
    requires shift < 64, size == 1u64 << shift,
    ensures q >> shift == q / size, q & sub(size, 1) == q % size, size >= 1,
{
    vstd::bits::lemma_u64_pow2_no_overflow(shift as nat);
    vstd::bits::lemma_u64_shl_is_mul(1u64, shift);
    assert(size == pow2(shift as nat));
    vstd::bits::lemma_u64_shr_is_div(q, shift);
    vstd::bits::lemma_u64_low_bits_mask_is_mod(q, shift as nat);
    assert(low_bits_mask(shift as nat) == pow2(shift as nat) - 1);
}

/// Value `q` of the chunked values (`size == 1 << shift`).
pub fn chunk_get(cs: &Vec<Vec<u64>>, shift: u64, size: u64, n: usize, q: usize) -> (v: u64)
    requires shift < 64, size == 1u64 << shift, chunks_shape(cs@, size as int, n as int), q < n,
    ensures v == chunk_at(cs@, size as int, q as int),
    no_unwind
{
    proof {
        lemma_shift_mask(q as u64, shift, size);
        lemma_chunk_index(cs@, size as int, n as int, q as int);
    }
    let c = ((q as u64) >> shift) as usize;
    let r = ((q as u64) & (size - 1)) as usize;
    cs[c][r]
}

} // verus!
