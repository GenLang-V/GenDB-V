//! The customer region bitmap of one call: bit `i` (word `i / 64`, bit `i % 64`) is "customer row `i`'s nation is
//! in region `$2`" (`nreg` of its c_nationkey). 15M customers make 1.9 MB of bits, which stay in the caches and the
//! TLB, where the c_nationkey codes (15 MB) do not; the serial index kernel tests a bit instead of reading the code.
//!
//! The build reads the customer nation codes 64 at a time. A word of 64 rows inside one customer group (`bs_c` a
//! multiple of 64) whose codes are all below 64 maps them through the group's region mask (bit `k`: nation key
//! `base + k` is in the region; `common::bitword::mask_word`, vector shifts); any other word (a partial last word,
//! a code of 64 or more, a base near `i64::MAX`, or a group size that is not a multiple of 64) looks each row's
//! nation up one by one.
use vstd::prelude::*;
use super::model::*;
use super::kernel::*;
use super::common::bitword::*;

verus! {

/// Customer bit `i` of the bitmap words `bits`.
pub open spec fn cbit(bits: Seq<u64>, i: int) -> bool {
    wbit(bits[i / 64], i % 64)
}

/// `bits` covers every customer row and bit `i` is customer row `i`'s region flag.
pub open spec fn cb_valid(c: Cols, ns: NStat, bits: Seq<u64>) -> bool {
    &&& bits.len() * 64 >= c.n_c
    &&& forall|i: int| 0 <= i < c.n_c ==> #[trigger] cbit(bits, i) == nreg(ns, cn(c, i))
}

/// The nation table's bitmap is empty (not built) or valid.
pub open spec fn cb_ok(c: Cols, nt: NTab) -> bool {
    nt.cbits@.len() > 0 ==> cb_valid(c, nt_view(nt), nt.cbits@)
}

/// The region mask of nation keys `[b, b + 64)`: bit `k` is `nreg` of key `b + k`.
fn region_mask(nt: &NTab, b: i64) -> (m: u64)
    requires ntab_ok(*nt), b <= i64::MAX - 64,
    ensures forall|k: int| 0 <= k < 64 ==> #[trigger] wbit(m, k) == nreg(nt_view(*nt), b + k),
{
    let mut m: u64 = 0;
    let mut k: u64 = 0;
    proof {
        lemma_zero_word();
    }
    while k < 64
        invariant
            ntab_ok(*nt), b <= i64::MAX - 64,
            k <= 64,
            k < 64 ==> (m >> k) == 0,
            forall|q: int| 0 <= q < k ==> #[trigger] wbit(m, q) == nreg(nt_view(*nt), b + q),
        decreases 64 - k,
    {
        let (_, reg, _) = nat_lookup(nt, b + k as i64);
        let f: u64 = if reg { 1 } else { 0 };
        let ghost m0 = m;
        m = push_bit(m, f, k);
        proof {
            assert forall|q: int| 0 <= q < k + 1 implies #[trigger] wbit(m, q) == nreg(nt_view(*nt), b + q) by {
                if q < k {
                    assert(wbit(m, q) == wbit(m0, q));
                }
            }
        }
        k = k + 1;
    }
    m
}

/// The word of customer rows `[i, i + len)`, each row's nation looked up.
fn word_slow(c: &Cols, nt: &NTab, i: usize, len: usize) -> (w: u64)
    requires cols_ok(*c), ntab_ok(*nt), 1 <= len <= 64, i + len <= c.n_c,
    ensures forall|j: int| 0 <= j < len ==> #[trigger] wbit(w, j) == nreg(nt_view(*nt), cn(*c, i + j)),
{
    let mut w: u64 = 0;
    let mut j: usize = 0;
    proof {
        lemma_zero_word();
    }
    while j < len
        invariant
            cols_ok(*c), ntab_ok(*nt), 1 <= len <= 64, i + len <= c.n_c,
            j <= len,
            j < 64 ==> (w >> (j as u64)) == 0,
            forall|q: int| 0 <= q < j ==> #[trigger] wbit(w, q) == nreg(nt_view(*nt), cn(*c, i + q)),
        decreases len - j,
    {
        let r = i + j;
        proof {
            lemma_div_below(r as int, c.bs_c as int, c.cn_b@.len() as int);
            assert(in_i64(ck(*c, r as int)) && in_i64(cn(*c, r as int)));
        }
        let key = c.cn_b[r / c.bs_c] + c.cn_c[r] as i64;
        let (_, reg, _) = nat_lookup(nt, key);
        let f: u64 = if reg { 1 } else { 0 };
        let ghost w0 = w;
        w = push_bit(w, f, j as u64);
        proof {
            assert forall|q: int| 0 <= q < j + 1 implies #[trigger] wbit(w, q) == nreg(nt_view(*nt), cn(*c, i + q)) by {
                if q < j {
                    assert(wbit(w, q) == wbit(w0, q));
                }
            }
        }
        j = j + 1;
    }
    w
}

/// The 64 rows of a word starting at a multiple of 64 lie in one group of `bs` rows when `bs` is a multiple of 64.
proof fn lemma_word_group(i: int, bs: int, j: int)
    requires i >= 0, i % 64 == 0, bs > 0, bs % 64 == 0, 0 <= j < 64,
    ensures (i + j) / bs == i / bs,
{
    let q = i / bs;
    let r = i % bs;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, bs);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(i, bs);
    let a = i / 64;
    let t = bs / 64;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, 64);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(bs, 64);
    assert(r == 64 * (a - t * q)) by (nonlinear_arith)
        requires i == 64 * a, bs == 64 * t, i == bs * q + r;
    assert(a - t * q < t) by (nonlinear_arith)
        requires r == 64 * (a - t * q), r < bs, bs == 64 * t;
    assert(r + 64 <= bs) by (nonlinear_arith)
        requires r == 64 * (a - t * q), a - t * q <= t - 1, bs == 64 * t;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(i + j, bs, q, r + j);
}

/// Bit `i` of a word list extended by `w` at index `wi` (`i` in `[64 wi, 64 wi + 64)`) is bit `i - 64 wi` of `w`;
/// bits of earlier rows are unchanged.
proof fn lemma_push_word(bits: Seq<u64>, w: u64, i: int)
    requires 0 <= i < bits.len() * 64 + 64,
    ensures
        i < bits.len() * 64 ==> cbit(bits.push(w), i) == cbit(bits, i),
        i >= bits.len() * 64 ==> cbit(bits.push(w), i) == wbit(w, i - bits.len() * 64),
{
    let wi = bits.len() as int;
    if i < wi * 64 {
        lemma_div_below(i, 64, wi);
    } else {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(i, 64, wi, i - wi * 64);
    }
}

/// The customer region bitmap (calling thread).
pub fn build_cbits(c: &Cols, nt: &NTab) -> (bits: Vec<u64>)
    requires cols_ok(*c), ntab_ok(*nt),
    ensures cb_valid(*c, nt_view(*nt), bits@),
{
    let ghost ns = nt_view(*nt);
    let n = c.n_c;
    let bs = c.bs_c;
    let grouped = bs % 64 == 0;
    let mut bits: Vec<u64> = Vec::with_capacity(n / 64 + 1);
    // The mask of group `mg` (`mg == usize::MAX`: none yet).
    let mut mg: usize = usize::MAX;
    let mut m: u64 = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            cols_ok(*c), ntab_ok(*nt), ns == nt_view(*nt), n == c.n_c, bs == c.bs_c, grouped == (bs % 64 == 0),
            i <= n,
            i == bits@.len() * 64 || (i == n && n <= bits@.len() * 64),
            mg != usize::MAX ==> mg < c.cn_b@.len() && c.cn_b@[mg as int] <= i64::MAX - 64
                && forall|k: int| 0 <= k < 64 ==> #[trigger] wbit(m, k) == nreg(ns, c.cn_b@[mg as int] + k),
            forall|q: int| 0 <= q < i ==> #[trigger] cbit(bits@, q) == nreg(ns, cn(*c, q)),
        decreases n - i,
    {
        let len: usize = if n - i >= 64 { 64 } else { n - i };
        let mut w: u64 = 0;
        let mut fast = false;
        if len == 64 && grouped {
            let g = i / bs;
            proof {
                lemma_div_below(i as int, bs as int, c.cn_b@.len() as int);
            }
            let b = c.cn_b[g];
            let chunk = vstd::slice::slice_subrange(c.cn_c, i, i + 64);
            proof {
                assert forall|j: int| 0 <= j < 64 implies #[trigger] chunk@[j] == c.cn_c@[i + j] by {}
            }
            if b <= i64::MAX - 64 && all_below64(chunk) {
                if mg != g {
                    m = region_mask(nt, b);
                    mg = g;
                }
                w = mask_word(chunk, m);
                fast = true;
                proof {
                    assert(i % 64 == 0) by {
                        vstd::arithmetic::div_mod::lemma_mod_multiples_basic(bits@.len() as int, 64);
                    }
                    assert forall|j: int| 0 <= j < 64 implies #[trigger] wbit(w, j) == nreg(ns, cn(*c, i + j)) by {
                        lemma_word_group(i as int, bs as int, j);
                        assert(chunk@[j] == c.cn_c@[i + j]);
                        assert(c.cn_c@[i + j] < 64);
                        assert(wbit(m, c.cn_c@[i + j] as int) == nreg(ns, b + c.cn_c@[i + j]));
                    }
                }
            }
        }
        if !fast {
            w = word_slow(c, nt, i, len);
        }
        let ghost b0 = bits@;
        bits.push(w);
        proof {
            assert(i == b0.len() * 64);
            assert forall|q: int| 0 <= q < i + len implies #[trigger] cbit(bits@, q) == nreg(ns, cn(*c, q)) by {
                lemma_push_word(b0, w, q);
                if q >= i {
                    assert(wbit(w, q - i) == nreg(ns, cn(*c, i + (q - i))));
                }
            }
        }
        i = i + len;
    }
    bits
}

} // verus!
