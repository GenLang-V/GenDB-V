//! Readers over the column formats of `colfmt`, on slices obtained from `StoredParts` extents (so they can run in
//! worker tasks: every reader here is `no_unwind`). Row decoding of frame-of-reference columns (`for_get_*`, with
//! `lemma_for_row` relating it to `colfmt::for_at`), text values (`text_slice`), dictionary lookup by binary search
//! (`dict_find`, sound and complete on a sorted dictionary), and lookup of a row by an integer key (`find_key_u32`:
//! a caller's guess first, then a scan; sound and complete).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::text::lex_cmp;
use super::colfmt::*;

verus! {

/// The group of row `j` under uniform groups of `bsize` rows is `j / bsize`, so a FOR value is
/// `base[j / bsize] + code[j]`.
pub proof fn lemma_for_row(gp: PartView, n: int, bsize: int, base: PartView, codes: PartView, j: int)
    requires
        groups_part_ok(gp, n, bsize),
        0 <= j < n,
    ensures
        group_of(u64s(gp), j) == j / bsize,
        in_group(u64s(gp), j / bsize, j),
        for_at(u64s(gp), base, codes, j) == base_at(base, j / bsize) + code_at(codes, j),
{
    let g = j / bsize;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, bsize);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(j, bsize);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(j, bsize);
    assert(bsize * g == g * bsize) by (nonlinear_arith);
    assert((g + 1) * bsize == g * bsize + bsize) by (nonlinear_arith);
    lemma_uniform_groups(gp, n, bsize);
    lemma_uniform_in_group(gp, n, bsize, g, j);
    lemma_for_at(u64s(gp), n, base, codes, g, j);
}

/// Value of row `j` of a FOR column with U32 codes and I64 bases (uniform groups of `bsize` rows).
pub fn for_get_u32(codes: &[u32], bases: &[i64], bsize: usize, j: usize) -> (v: i64)
    requires
        bsize >= 1,
        j < codes@.len(),
        (j as int) / (bsize as int) < bases@.len(),
        i64::MIN <= bases@[(j as int) / (bsize as int)] + codes@[j as int] <= i64::MAX,
    ensures
        v == bases@[(j as int) / (bsize as int)] + codes@[j as int],
    no_unwind
{
    bases[j / bsize] + codes[j] as i64
}

/// Value of row `j` of a FOR column with U16 codes and I64 bases.
pub fn for_get_u16(codes: &[u16], bases: &[i64], bsize: usize, j: usize) -> (v: i64)
    requires
        bsize >= 1,
        j < codes@.len(),
        (j as int) / (bsize as int) < bases@.len(),
        i64::MIN <= bases@[(j as int) / (bsize as int)] + codes@[j as int] <= i64::MAX,
    ensures
        v == bases@[(j as int) / (bsize as int)] + codes@[j as int],
    no_unwind
{
    bases[j / bsize] + codes[j] as i64
}

/// Value of row `j` of a FOR column with U8 codes and I64 bases.
pub fn for_get_u8(codes: &[u8], bases: &[i64], bsize: usize, j: usize) -> (v: i64)
    requires
        bsize >= 1,
        j < codes@.len(),
        (j as int) / (bsize as int) < bases@.len(),
        i64::MIN <= bases@[(j as int) / (bsize as int)] + codes@[j as int] <= i64::MAX,
    ensures
        v == bases@[(j as int) / (bsize as int)] + codes@[j as int],
    no_unwind
{
    bases[j / bsize] + codes[j] as i64
}

/// The bytes of text value `j` (offsets and bytes slices of a text part pair or of a dictionary).
pub fn text_slice<'a>(offs: &[u64], bytes: &'a [u8], j: usize) -> (s: &'a [u8])
    requires
        j + 1 < offs@.len(),
        text_range_ok(offs@, bytes@, j as int),
    ensures
        s@ == text_of(offs@, bytes@, j as int),
    no_unwind
{
    let a = offs[j] as usize;
    let b = offs[j + 1] as usize;
    let (_, tail) = bytes.split_at(a);
    let (mid, _) = tail.split_at(b - a);
    proof {
        assert(mid@ =~= bytes@.subrange(a as int, b as int));
    }
    mid
}

proof fn lemma_lex_step(x: Seq<u8>, y: Seq<u8>, i: int)
    requires
        0 <= i < x.len(),
        i < y.len(),
        x[i] == y[i],
    ensures
        lex_cmp(x.subrange(i, x.len() as int), y.subrange(i, y.len() as int))
            == lex_cmp(x.subrange(i + 1, x.len() as int), y.subrange(i + 1, y.len() as int)),
{
    assert(x.subrange(i, x.len() as int).drop_first() =~= x.subrange(i + 1, x.len() as int));
    assert(y.subrange(i, y.len() as int).drop_first() =~= y.subrange(i + 1, y.len() as int));
}

/// Bytewise comparison (`lex_cmp`) of `x` (`xlen` bytes) with `y` (`ylen` bytes).
pub fn bytes_cmp(x: &[u8], xlen: usize, y: &[u8], ylen: usize) -> (r: i8)
    requires
        xlen == x@.len(),
        ylen == y@.len(),
    ensures
        r as int == lex_cmp(x@, y@),
    no_unwind
{
    let mut i: usize = 0;
    assert(x@.subrange(0, x@.len() as int) =~= x@);
    assert(y@.subrange(0, y@.len() as int) =~= y@);
    while i < xlen && i < ylen
        invariant
            xlen == x@.len(),
            ylen == y@.len(),
            i <= xlen,
            i <= ylen,
            lex_cmp(x@.subrange(i as int, x@.len() as int), y@.subrange(i as int, y@.len() as int)) == lex_cmp(x@, y@),
        decreases xlen - i,
    {
        let a = x[i];
        let b = y[i];
        if a < b {
            assert(x@.subrange(i as int, x@.len() as int)[0] == a);
            assert(y@.subrange(i as int, y@.len() as int)[0] == b);
            return -1;
        } else if a > b {
            assert(x@.subrange(i as int, x@.len() as int)[0] == a);
            assert(y@.subrange(i as int, y@.len() as int)[0] == b);
            return 1;
        }
        proof {
            lemma_lex_step(x@, y@, i as int);
        }
        i = i + 1;
    }
    let ghost sx = x@.subrange(i as int, x@.len() as int);
    let ghost sy = y@.subrange(i as int, y@.len() as int);
    if i < xlen {
        assert(sy.len() == 0 && sx.len() > 0);
        1
    } else if i < ylen {
        assert(sx.len() == 0 && sy.len() > 0);
        -1
    } else {
        assert(sx.len() == 0 && sy.len() == 0);
        0
    }
}

/// The entry of a sorted dictionary (`k` entries) holding `needle` (`nlen` bytes), if any: binary search.
pub fn dict_find(offs: &[u64], bytes: &[u8], k: usize, needle: &[u8], nlen: usize) -> (r: Option<usize>)
    requires
        offs@.len() == k + 1,
        text_parts_wf(offs@, bytes@, k as int),
        dict_sorted(offs@, bytes@, k as int),
        nlen == needle@.len(),
    ensures
        r matches Some(x) ==> x < k && text_of(offs@, bytes@, x as int) == needle@,
        r is None ==> forall|x: int| 0 <= x < k ==> text_of(offs@, bytes@, x) != needle@,
    no_unwind
{
    let mut lo: usize = 0;
    let mut hi: usize = k;
    while lo < hi
        invariant
            offs@.len() == k + 1,
            text_parts_wf(offs@, bytes@, k as int),
            dict_sorted(offs@, bytes@, k as int),
            nlen == needle@.len(),
            lo <= hi <= k,
            forall|x: int| 0 <= x < lo ==> lex_cmp(#[trigger] text_of(offs@, bytes@, x), needle@) < 0,
            forall|x: int| hi <= x < k ==> lex_cmp(#[trigger] text_of(offs@, bytes@, x), needle@) > 0,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        assert(text_range_ok(offs@, bytes@, mid as int));
        proof {
            vstd::slice::axiom_spec_len(bytes);
        }
        let e = text_slice(offs, bytes, mid);
        let elen = (offs[mid + 1] - offs[mid]) as usize;
        let c = bytes_cmp(e, elen, needle, nlen);
        let ghost em = text_of(offs@, bytes@, mid as int);
        if c == 0 {
            proof {
                crate::bridge::equality::lemma_lex_cmp_zero(em, needle@);
            }
            return Some(mid);
        } else if c < 0 {
            proof {
                assert forall|x: int| 0 <= x < mid + 1 implies lex_cmp(#[trigger] text_of(offs@, bytes@, x), needle@) < 0 by {
                    if x < mid {
                        lemma_dict_order(offs@, bytes@, k as int, x, mid as int);
                        let ex = text_of(offs@, bytes@, x);
                        crate::bridge::order::lemma_lex_cmp_trans(ex, em, needle@);
                        if lex_cmp(ex, needle@) == 0 {
                            crate::bridge::equality::lemma_lex_cmp_zero(ex, needle@);
                            crate::bridge::order::lemma_lex_cmp_antisym(ex, em);
                        }
                    }
                }
            }
            lo = mid + 1;
        } else {
            proof {
                assert forall|x: int| mid <= x < k implies lex_cmp(#[trigger] text_of(offs@, bytes@, x), needle@) > 0 by {
                    if x > mid {
                        lemma_dict_order(offs@, bytes@, k as int, mid as int, x);
                        let ex = text_of(offs@, bytes@, x);
                        crate::bridge::order::lemma_lex_cmp_antisym(em, ex);
                        crate::bridge::order::lemma_lex_cmp_antisym(em, needle@);
                        crate::bridge::order::lemma_lex_cmp_antisym(ex, needle@);
                        crate::bridge::order::lemma_lex_cmp_trans(needle@, em, ex);
                        if lex_cmp(ex, needle@) == 0 {
                            crate::bridge::equality::lemma_lex_cmp_zero(ex, needle@);
                            crate::bridge::equality::lemma_lex_cmp_zero(needle@, ex);
                        }
                    }
                }
            }
            hi = mid;
        }
    }
    proof {
        assert forall|x: int| 0 <= x < k implies text_of(offs@, bytes@, x) != needle@ by {
            crate::bridge::equality::lemma_lex_cmp_zero(text_of(offs@, bytes@, x), needle@);
        }
    }
    None
}

/// `j < m * b` implies `j / b < m`.
pub proof fn lemma_div_lt(j: int, b: int, m: int)
    requires
        0 <= j < m * b,
        b >= 1,
    ensures
        0 <= j / b < m,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, b);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(j, b);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(j, b);
    assert(b * (j / b) == (j / b) * b) by (nonlinear_arith);
    assert(j / b < m) by (nonlinear_arith) requires (j / b) * b <= j, j < m * b, b >= 1;
}

/// The decoded integer of row `j` of a FOR column with U32 codes and I64 bases (uniform groups of `bsize` rows).
pub open spec fn key_u32_at(codes: Seq<u32>, bases: Seq<i64>, bsize: int, j: int) -> int {
    bases[j / bsize] + codes[j]
}

/// A row whose FOR-coded U32/I64 key is `k`: the row `guess` if it has it, else the first such row by a scan.
/// `None` exactly when no row has key `k` (rows `0 .. n`).
pub fn find_key_u32(codes: &[u32], bases: &[i64], bsize: usize, n: usize, k: i64, guess: usize) -> (r: Option<usize>)
    requires
        bsize >= 1,
        n == codes@.len(),
        bases@.len() * bsize >= n,
        forall|j: int| 0 <= j < n ==> i64::MIN <= #[trigger] key_u32_at(codes@, bases@, bsize as int, j) <= i64::MAX,
    ensures
        r matches Some(j) ==> j < n && key_u32_at(codes@, bases@, bsize as int, j as int) == k,
        r is None ==> forall|j: int| 0 <= j < n ==> #[trigger] key_u32_at(codes@, bases@, bsize as int, j) != k,
    no_unwind
{
    if guess < n {
        proof {
            lemma_div_lt(guess as int, bsize as int, bases@.len() as int);
        }
        assert(i64::MIN <= key_u32_at(codes@, bases@, bsize as int, guess as int) <= i64::MAX);
        assert(key_u32_at(codes@, bases@, bsize as int, guess as int) == bases@[(guess as int) / (bsize as int)] + codes@[guess as int]);
        if for_get_u32(codes, bases, bsize, guess) == k {
            return Some(guess);
        }
    }
    let mut j: usize = 0;
    while j < n
        invariant
            bsize >= 1,
            n == codes@.len(),
            j <= n,
            bases@.len() * bsize >= n,
            forall|i: int| 0 <= i < n ==> i64::MIN <= #[trigger] key_u32_at(codes@, bases@, bsize as int, i) <= i64::MAX,
            forall|i: int| 0 <= i < j ==> #[trigger] key_u32_at(codes@, bases@, bsize as int, i) != k,
        decreases n - j,
    {
        proof {
            lemma_div_lt(j as int, bsize as int, bases@.len() as int);
        }
        assert(i64::MIN <= key_u32_at(codes@, bases@, bsize as int, j as int) <= i64::MAX);
        assert(key_u32_at(codes@, bases@, bsize as int, j as int) == bases@[(j as int) / (bsize as int)] + codes@[j as int]);
        if for_get_u32(codes, bases, bsize, j) == k {
            return Some(j);
        }
        j = j + 1;
    }
    None
}

} // verus!
