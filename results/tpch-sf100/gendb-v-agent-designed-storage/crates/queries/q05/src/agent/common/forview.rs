//! Decoded views of frame-of-reference (FOR) columns stored in uniform row blocks: the value of row `j` is the
//! base of its block `j / bs` plus its unsigned code (`fv32`, `fv16`, `fv8`). `col*_ok` states the shape (one code
//! per row, enough bases) and that every value fits `i64`; the `get*` readers decode one row without unwinding,
//! dividing by the block size with a shift when it is a power of two (`Div`).
use vstd::prelude::*;
use vstd::arithmetic::power2::pow2;

verus! {

/// A block size `bs` and, when `p2`, its base-2 logarithm `sh` (`bs == 2^sh`).
#[derive(Clone, Copy)]
pub struct Div {
    pub bs: usize,
    pub sh: usize,
    pub p2: bool,
}

impl Div {
    pub open spec fn ok(&self) -> bool {
        &&& self.bs >= 1
        &&& self.p2 ==> self.sh < 64 && self.bs as nat == pow2(self.sh as nat)
    }
}

/// `x / d.bs`, by a shift when the block size is a power of two.
pub fn div_of(d: Div, x: usize) -> (r: usize)
    requires d.ok(),
    ensures r == x / d.bs,
    no_unwind
{
    if d.p2 {
        let xx = x as u64;
        let ss = d.sh as u64;
        proof {
            vstd::bits::lemma_u64_shr_is_div(xx, ss);
        }
        let r = xx >> ss;
        proof {
            vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(x as int, 1, d.bs as int);
            assert(x as int / 1 == x as int);
        }
        r as usize
    } else {
        x / d.bs
    }
}

/// The `Div` of a block size: its shift when it is a power of two below `2^62`.
pub fn div_new(bs: usize) -> (d: Div)
    requires bs >= 1,
    ensures d.ok(), d.bs == bs,
{
    let mut sh: usize = 0;
    let mut p: u64 = 1;
    let b = bs as u64;
    proof {
        vstd::arithmetic::power2::lemma2_to64();
    }
    while p < b && sh < 62
        invariant
            sh <= 62,
            p as nat == pow2(sh as nat),
            1 <= p <= 0x4000_0000_0000_0000,
        decreases 62 - sh,
    {
        proof {
            vstd::arithmetic::power2::lemma_pow2_unfold((sh + 1) as nat);
            vstd::arithmetic::power2::lemma2_to64_rest();
            if sh < 61 {
                vstd::arithmetic::power2::lemma_pow2_strictly_increases(sh as nat, 61);
            }
            assert(p <= 0x2000_0000_0000_0000);
        }
        p = p * 2;
        sh = sh + 1;
    }
    Div { bs, sh, p2: p == b }
}

/// A `Div` for a layout block size `bs` over `n` rows that indexes every row's block exactly as `bs` does: `bs`
/// itself when it is at most `n` (`exact`), else `n` (every row is then in block 0 under both).
pub fn div_for(bs: u64, n: usize) -> (r: (Div, bool))
    requires bs >= 1,
    ensures
        r.0.ok(),
        r.1 ==> r.0.bs as int == bs as int,
        forall|j: int| 0 <= j < n ==> #[trigger] (j / (r.0.bs as int)) == j / (bs as int),
        n > 0 ==> r.0.bs <= n,
{
    if bs <= n as u64 {
        (div_new(bs as usize), true)
    } else {
        let b = if n == 0 { 1 } else { n };
        proof {
            assert forall|j: int| 0 <= j < n implies #[trigger] (j / (b as int)) == j / (bs as int) by {
                vstd::arithmetic::div_mod::lemma_basic_div(j, b as int);
                vstd::arithmetic::div_mod::lemma_basic_div(j, bs as int);
            }
        }
        (div_new(b), false)
    }
}

/// Two block sizes that index every row's block alike give the same U32 column.
pub proof fn lemma_col32_rebase(codes: Seq<u32>, bases: Seq<i64>, bs: int, bs2: int, n: int)
    requires
        col32_ok(codes, bases, bs, n), bs2 >= 1, n > 0 ==> bs2 <= n,
        forall|j: int| 0 <= j < n ==> #[trigger] (j / bs2) == j / bs,
    ensures
        col32_ok(codes, bases, bs2, n),
        forall|j: int| 0 <= j < n ==> #[trigger] fv32(codes, bases, bs2, j) == fv32(codes, bases, bs, j),
{
    assert forall|j: int| 0 <= j < n implies #[trigger] fv32(codes, bases, bs2, j) == fv32(codes, bases, bs, j) by {
        assert(j / bs2 == j / bs);
    }
    lemma_bases_rebase(bases.len() as int, bs, bs2, n);
}

/// Two block sizes that index every row's block alike give the same U16 column.
pub proof fn lemma_col16_rebase(codes: Seq<u16>, bases: Seq<i64>, bs: int, bs2: int, n: int)
    requires
        col16_ok(codes, bases, bs, n), bs2 >= 1, n > 0 ==> bs2 <= n,
        forall|j: int| 0 <= j < n ==> #[trigger] (j / bs2) == j / bs,
    ensures
        col16_ok(codes, bases, bs2, n),
        forall|j: int| 0 <= j < n ==> #[trigger] fv16(codes, bases, bs2, j) == fv16(codes, bases, bs, j),
{
    assert forall|j: int| 0 <= j < n implies #[trigger] fv16(codes, bases, bs2, j) == fv16(codes, bases, bs, j) by {
        assert(j / bs2 == j / bs);
    }
    lemma_bases_rebase(bases.len() as int, bs, bs2, n);
}

/// Two block sizes that index every row's block alike give the same U8 column.
pub proof fn lemma_col8_rebase(codes: Seq<u8>, bases: Seq<i64>, bs: int, bs2: int, n: int)
    requires
        col8_ok(codes, bases, bs, n), bs2 >= 1, n > 0 ==> bs2 <= n,
        forall|j: int| 0 <= j < n ==> #[trigger] (j / bs2) == j / bs,
    ensures
        col8_ok(codes, bases, bs2, n),
        forall|j: int| 0 <= j < n ==> #[trigger] fv8(codes, bases, bs2, j) == fv8(codes, bases, bs, j),
{
    assert forall|j: int| 0 <= j < n implies #[trigger] fv8(codes, bases, bs2, j) == fv8(codes, bases, bs, j) by {
        assert(j / bs2 == j / bs);
    }
    lemma_bases_rebase(bases.len() as int, bs, bs2, n);
}

/// Enough bases for `n` rows under `bs` are enough under `bs2` when both index the last row alike.
proof fn lemma_bases_rebase(m: int, bs: int, bs2: int, n: int)
    requires
        bs >= 1, bs2 >= 1, m >= 0, m * bs >= n, n > 0 ==> bs2 <= n,
        forall|j: int| 0 <= j < n ==> #[trigger] (j / bs2) == j / bs,
    ensures m * bs2 >= n,
{
    if n > 0 {
        let j = n - 1;
        assert(j / bs2 == j / bs);
        lemma_block_index(j, bs, m);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, bs2);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(j, bs2);
        assert(bs2 * (j / bs2) == (j / bs2) * bs2) by (nonlinear_arith);
        assert((j / bs2 + 1) * bs2 > j) by (nonlinear_arith)
            requires (j / bs2) * bs2 + j % bs2 == j, j % bs2 < bs2;
        assert(m * bs2 >= (j / bs2 + 1) * bs2) by (nonlinear_arith)
            requires m >= j / bs2 + 1, bs2 >= 1;
    }
}

/// The first row of a U32 FOR column holding `k`, by a linear scan; `None` when no row holds it.
pub fn scan32(codes: &[u32], bases: &[i64], d: Div, n: usize, k: i64) -> (r: Option<usize>)
    requires d.ok(), col32_ok(codes@, bases@, d.bs as int, n as int),
    ensures
        r matches Some(j) ==> j < n && fv32(codes@, bases@, d.bs as int, j as int) == k,
        r is None ==> forall|j: int| 0 <= j < n ==> #[trigger] fv32(codes@, bases@, d.bs as int, j) != k,
    no_unwind
{
    let mut j: usize = 0;
    while j < n
        invariant
            d.ok(), col32_ok(codes@, bases@, d.bs as int, n as int),
            j <= n,
            forall|i: int| 0 <= i < j ==> #[trigger] fv32(codes@, bases@, d.bs as int, i) != k,
        decreases n - j,
    {
        if get32(codes, bases, d, n, j) == k {
            return Some(j);
        }
        j = j + 1;
    }
    None
}

/// Value of row `j` of a FOR column with U32 codes and I64 bases.
pub open spec fn fv32(codes: Seq<u32>, bases: Seq<i64>, bs: int, j: int) -> int {
    bases[j / bs] as int + codes[j] as int
}

/// Value of row `j` of a FOR column with U16 codes and I64 bases.
pub open spec fn fv16(codes: Seq<u16>, bases: Seq<i64>, bs: int, j: int) -> int {
    bases[j / bs] as int + codes[j] as int
}

/// Value of row `j` of a FOR column with U8 codes and I64 bases.
pub open spec fn fv8(codes: Seq<u8>, bases: Seq<i64>, bs: int, j: int) -> int {
    bases[j / bs] as int + codes[j] as int
}

/// `n` rows of U32 codes over enough bases; every value fits `i64`.
pub open spec fn col32_ok(codes: Seq<u32>, bases: Seq<i64>, bs: int, n: int) -> bool {
    &&& bs >= 1
    &&& codes.len() == n
    &&& bases.len() * bs >= n
    &&& forall|j: int| 0 <= j < n ==> i64::MIN <= #[trigger] fv32(codes, bases, bs, j) <= i64::MAX
}

/// `n` rows of U16 codes over enough bases; every value fits `i64`.
pub open spec fn col16_ok(codes: Seq<u16>, bases: Seq<i64>, bs: int, n: int) -> bool {
    &&& bs >= 1
    &&& codes.len() == n
    &&& bases.len() * bs >= n
    &&& forall|j: int| 0 <= j < n ==> i64::MIN <= #[trigger] fv16(codes, bases, bs, j) <= i64::MAX
}

/// `n` rows of U8 codes over enough bases; every value fits `i64`.
pub open spec fn col8_ok(codes: Seq<u8>, bases: Seq<i64>, bs: int, n: int) -> bool {
    &&& bs >= 1
    &&& codes.len() == n
    &&& bases.len() * bs >= n
    &&& forall|j: int| 0 <= j < n ==> i64::MIN <= #[trigger] fv8(codes, bases, bs, j) <= i64::MAX
}

/// `j < m * b` implies `j / b < m`.
pub proof fn lemma_block_index(j: int, b: int, m: int)
    requires 0 <= j < m * b, b >= 1,
    ensures 0 <= j / b < m,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, b);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(j, b);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(j, b);
    assert(b * (j / b) == (j / b) * b) by (nonlinear_arith);
    assert(j / b < m) by (nonlinear_arith) requires (j / b) * b <= j, j < m * b, b >= 1;
}

/// Row `j` of a U32 FOR column.
pub fn get32(codes: &[u32], bases: &[i64], d: Div, n: usize, j: usize) -> (v: i64)
    requires d.ok(), col32_ok(codes@, bases@, d.bs as int, n as int), j < n,
    ensures v == fv32(codes@, bases@, d.bs as int, j as int),
    no_unwind
{
    let g = div_of(d, j);
    proof {
        lemma_block_index(j as int, d.bs as int, bases@.len() as int);
        assert(i64::MIN <= fv32(codes@, bases@, d.bs as int, j as int) <= i64::MAX);
    }
    bases[g] + codes[j] as i64
}

/// Row `j` of a U16 FOR column.
pub fn get16(codes: &[u16], bases: &[i64], d: Div, n: usize, j: usize) -> (v: i64)
    requires d.ok(), col16_ok(codes@, bases@, d.bs as int, n as int), j < n,
    ensures v == fv16(codes@, bases@, d.bs as int, j as int),
    no_unwind
{
    let g = div_of(d, j);
    proof {
        lemma_block_index(j as int, d.bs as int, bases@.len() as int);
        assert(i64::MIN <= fv16(codes@, bases@, d.bs as int, j as int) <= i64::MAX);
    }
    bases[g] + codes[j] as i64
}

/// Row `j` of a U8 FOR column.
pub fn get8(codes: &[u8], bases: &[i64], d: Div, n: usize, j: usize) -> (v: i64)
    requires d.ok(), col8_ok(codes@, bases@, d.bs as int, n as int), j < n,
    ensures v == fv8(codes@, bases@, d.bs as int, j as int),
    no_unwind
{
    let g = div_of(d, j);
    proof {
        lemma_block_index(j as int, d.bs as int, bases@.len() as int);
        assert(i64::MIN <= fv8(codes@, bases@, d.bs as int, j as int) <= i64::MAX);
    }
    bases[g] + codes[j] as i64
}

} // verus!
