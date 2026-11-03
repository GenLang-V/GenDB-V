//! Building blocks of the lineitem scan (`agent::scan`), each `no_unwind` so a worker can call it.
//!
//! - `find_key`: the position of a key in a key column (binary search when the column happens to be sorted,
//!   checked; otherwise a linear scan), or none.
//! - `cust_bit`: whether some customer of a key has segment `$1`, from the per-customer-row segment bitmap when the
//!   `c_custkey` column is positional (`c_custkey[r] == base + r`).
//! - `block_masks`: for 64 lineitem rows, the bit mask of key changes (row `t` has another `l_orderkey` than the row
//!   before it) and of `l_shipdate > $2`.
//! - `block_orders`: walks the key changes of a block in order; the `u`-th change starts the next orders row
//!   (`j + count_below(changes, t + 1)` for row `t`); checks that this orders row has the lineitem's key, and
//!   collects the date toggles (bit `t` set where the order of row `t` and of row `t - 1` differ in
//!   `o_orderdate < $2`). The prefix XOR of the toggles is then the per-row flag `o_orderdate < $2` of the row's
//!   order (`lemma_order_flags`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::stores::StoresView;
use crate::agent::tables::*;
use crate::agent::normal_form::*;
use crate::agent::common::bits::*;
use crate::agent::common::tz::tz64;

verus! {

// ------------------------------------------------------------------------------------------------ key search

/// `Some(x)`: `keys[x] == k`; `None`: no position holds `k`.
pub fn find_key(keys: &'static [i64], n: usize, k: i64) -> (r: Option<usize>)
    requires keys@.len() == n,
    ensures
        r matches Some(x) ==> x < n && keys@[x as int] == k,
        r is None ==> forall|x: int| 0 <= x < n ==> keys@[x] != k,
    no_unwind
{
    // binary search for the first position with a key >= k (meaningful when the column is sorted)
    let mut a: usize = 0;
    let mut b: usize = n;
    while a < b
        invariant a <= b <= n, keys@.len() == n,
        decreases b - a,
    {
        let m = a + (b - a) / 2;
        if keys[m] < k { a = m + 1; } else { b = m; }
    }
    if a < n && keys[a] == k {
        return Some(a);
    }
    // not sorted around k: scan every position
    let mut x: usize = 0;
    while x < n
        invariant x <= n, keys@.len() == n, forall|y: int| 0 <= y < x ==> keys@[y] != k,
        decreases n - x,
    {
        if keys[x] == k {
            return Some(x);
        }
        x = x + 1;
    }
    None
}

// ------------------------------------------------------------------------------------------------ customers

/// The segment bitmap over customer rows, valid when `c_custkey` is positional: `c_custkey[r] == base + r` and bit
/// `r` is set exactly when customer row `r` has segment `seg`.
pub open spec fn cust_bits_ok(bits: Seq<u64>, sv: StoresView, seg: Seq<u8>, base: int, nc: int) -> bool {
    &&& nc == n_c(sv)
    &&& ck(sv).len() == nc
    &&& forall|r: int| 0 <= r < nc ==> #[trigger] ck(sv)[r] as int == base + r && r / 64 < bits.len()
    &&& forall|r: int| 0 <= r < nc ==> #[trigger] word_bit(bits, r) == (cseg(sv, r) == seg)
}

/// Some customer of key `key` has segment `seg` (`cust_ok`), read from the bitmap.
pub fn cust_bit(bits: &Vec<u64>, base: i64, nc: usize, key: i64, Ghost(sv): Ghost<StoresView>, Ghost(seg): Ghost<Seq<u8>>) -> (b: bool)
    requires cust_bits_ok(bits@, sv, seg, base as int, nc as int),
    ensures b == cust_ok(sv, seg, key as int),
    no_unwind
{
    let d: i128 = key as i128 - base as i128;
    if 0 <= d && d < nc as i128 {
        let r = d as usize;
        assert(ck(sv)[r as int] as int == base as int + r);
        assert((r as int) / 64 < bits@.len());
        let w = bits[r / 64];
        let b = (w >> ((r % 64) as u64)) & 1 == 1;
        proof {
            assert(word_bit(bits@, r as int) == b);
            if b {
                assert(cseg(sv, r as int) == seg);
            } else {
                if cust_ok(sv, seg, key as int) {
                    let r2 = choose|r2: int| 0 <= r2 < n_c(sv) && ck(sv)[r2] as int == key as int && #[trigger] cseg(sv, r2) == seg;
                    assert(ck(sv)[r2] as int == base as int + r2);
                }
            }
        }
        b
    } else {
        proof {
            if cust_ok(sv, seg, key as int) {
                let r2 = choose|r2: int| 0 <= r2 < n_c(sv) && ck(sv)[r2] as int == key as int && #[trigger] cseg(sv, r2) == seg;
                assert(ck(sv)[r2] as int == base as int + r2);
            }
        }
        false
    }
}

// ------------------------------------------------------------------------------------------------ blocks of 64 rows

/// Key of the row before row `t` of a block (`prev` before row 0).
pub open spec fn key_before(kb: Seq<i64>, prev: i64, t: int) -> i64 {
    if t == 0 { prev } else { kb[t - 1] }
}

/// Bit masks of a block: `cm` bit `t` = row `t` changes the key, `sm` bit `t` = row `t` ships after `dl`.
pub fn block_masks(kb: &[i64], sb: &[i32], prev: i64, dl: i32) -> (r: (u64, u64))
    requires kb@.len() == 64, sb@.len() == 64,
    ensures
        forall|t: u64| t < 64 ==> #[trigger] bit(r.0, t) == (kb@[t as int] != key_before(kb@, prev, t as int)),
        forall|t: u64| t < 64 ==> #[trigger] bit(r.1, t) == (sb@[t as int] > dl),
    no_unwind
{
    let mut cm: u64 = 0;
    let mut sm: u64 = 0;
    let mut p = prev;
    let mut t: usize = 0;
    proof {
        assert forall|u: u64| u < 64 implies !#[trigger] bit(0u64, u) by { lemma_bit_zero(u); }
    }
    while t < 64
        invariant
            t <= 64, kb@.len() == 64, sb@.len() == 64,
            p == key_before(kb@, prev, t as int),
            forall|u: u64| u < t ==> #[trigger] bit(cm, u) == (kb@[u as int] != key_before(kb@, prev, u as int)),
            forall|u: u64| u < t ==> #[trigger] bit(sm, u) == (sb@[u as int] > dl),
            forall|u: u64| t <= u < 64 ==> !#[trigger] bit(cm, u),
            forall|u: u64| t <= u < 64 ==> !#[trigger] bit(sm, u),
        decreases 64 - t,
    {
        let k = kb[t];
        let ch: u64 = if k != p { 1 } else { 0 };
        let sh: u64 = if sb[t] > dl { 1 } else { 0 };
        let ghost (cm0, sm0) = (cm, sm);
        cm = cm | (ch << (t as u64));
        sm = sm | (sh << (t as u64));
        proof {
            assert forall|u: u64| u < 64 implies #[trigger] bit(cm, u) == if u == t as u64 { ch == 1 } else { bit(cm0, u) } by {
                lemma_bit_set(cm0, ch, t as u64, u);
            }
            assert forall|u: u64| u < 64 implies #[trigger] bit(sm, u) == if u == t as u64 { sh == 1 } else { bit(sm0, u) } by {
                lemma_bit_set(sm0, sh, t as u64, u);
            }
        }
        p = k;
        t = t + 1;
    }
    (cm, sm)
}

/// The orders row of row `t` of a block whose row before it maps to `j`.
pub open spec fn blk_ord(j: int, cm: u64, t: int) -> int { j + count_below(cm, t + 1) }

/// Walk the key changes of a block (orders `j + 1, j + 2, ..`): check each new order's key, and collect the date
/// toggles. `None` when an orders row does not have the key (the scan then falls back).
pub fn block_orders(okey: &'static [i64], odate: &'static [i32], kb: &[i64], cm: u64, j: usize, dl: i32, table: &[u8; 64],
    Ghost(no): Ghost<int>) -> (r: Option<(u64, usize)>)
    requires kb@.len() == 64, okey@.len() == no, odate@.len() == no, j + 64 < no, no <= usize::MAX, table@.len() == 64,
    ensures
        r matches Some((tog, jj)) ==> {
            &&& jj == j + count_below(cm, 64)
            &&& forall|s: u64| s < 64 && #[trigger] bit(cm, s) ==> okey@[blk_ord(j as int, cm, s as int)] == kb@[s as int]
            &&& forall|u: u64| u < 64 ==> #[trigger] bit(tog, u) == (bit(cm, u)
                    && ((odate@[blk_ord(j as int, cm, u as int)] < dl) != (odate@[j + count_below(cm, u as int)] < dl)))
        },
    no_unwind
{
    let mut tog: u64 = 0;
    let mut c = cm;
    let mut jj = j;
    let mut dp: bool = odate[j] < dl;
    let ghost mut p: int = 0;
    proof {
        lemma_count_nonneg(cm, 0);
        assert forall|u: u64| u < 64 implies !#[trigger] bit(0u64, u) by { lemma_bit_zero(u); }
    }
    while c != 0
        invariant
            kb@.len() == 64, okey@.len() == no, odate@.len() == no, j + 64 < no, no <= usize::MAX, table@.len() == 64,
            0 <= p <= 64,
            forall|u: u64| u < 64 ==> #[trigger] bit(c, u) == (bit(cm, u) && u >= p),
            jj == j + count_below(cm, p),
            count_below(cm, p) <= p,
            dp == (odate@[jj as int] < dl),
            forall|s: u64| s < p && #[trigger] bit(cm, s) ==> okey@[blk_ord(j as int, cm, s as int)] == kb@[s as int],
            forall|u: u64| u < 64 ==> #[trigger] bit(tog, u) == (u < p && bit(cm, u)
                && ((odate@[blk_ord(j as int, cm, u as int)] < dl) != (odate@[j + count_below(cm, u as int)] < dl))),
        decreases 64 - p,
    {
        let s = tz64(c, table);
        proof {
            lemma_first_bit(c);
            assert(bit(c, s as u64));
            assert(s as int >= p);
            assert forall|u: u64| p <= u < s implies !#[trigger] bit(cm, u) by {
                assert(!bit(c, u));
            }
            lemma_count_flat(cm, p, s as int);
            lemma_count_step(cm, s as int);
            lemma_count_bounds(cm, s as int + 1, 64);
            lemma_count_nonneg(cm, s as int + 1);
        }
        let ghost c0 = c;
        c = c & (c - 1);
        proof {
            assert(c0 - 1 == sub(c0, 1));
            assert forall|u: u64| u < 64 implies #[trigger] bit(c, u) == (bit(cm, u) && u >= s + 1) by {
                lemma_clear_lowest(c0, s as u64, u);
            }
        }
        assert(jj + 1 == j + count_below(cm, s as int + 1));
        assert(count_below(cm, s as int + 1) <= 64);
        jj = jj + 1;
        let su = s as usize;
        if okey[jj] != kb[su] {
            return None;
        }
        let dk: bool = odate[jj] < dl;
        let x: u64 = if dk != dp { 1 } else { 0 };
        let ghost tog0 = tog;
        proof {
            assert(!bit(tog0, s as u64));
        }
        tog = tog | (x << (s as u64));
        proof {
            assert forall|u: u64| u < 64 implies #[trigger] bit(tog, u) == if u == s as u64 { x == 1 } else { bit(tog0, u) } by {
                lemma_bit_set(tog0, x, s as u64, u);
            }
            p = s as int + 1;
        }
        dp = dk;
    }
    proof {
        assert forall|u: u64| p <= u < 64 implies !#[trigger] bit(cm, u) by {
            assert(!bit(c, u)) by { lemma_bit_zero(u); }
        }
        lemma_count_flat(cm, p, 64);
    }
    Some((tog, jj))
}

/// The prefix XOR of the toggles, flipped by the date flag of order `j`, is the date flag of every row's order.
pub proof fn lemma_order_flags(odate: Seq<i32>, dl: i32, cm: u64, tog: u64, j: int, d0: u64)
    requires
        d0 <= 1, (d0 == 1) == (odate[j] < dl),
        0 <= j, j + 64 < odate.len(),
        forall|u: u64| u < 64 ==> #[trigger] bit(tog, u) == (bit(cm, u)
            && ((odate[blk_ord(j, cm, u as int)] < dl) != (odate[j + count_below(cm, u as int)] < dl))),
    ensures
        forall|u: u64| u < 64 ==> #[trigger] bit(prefix_xor(tog) ^ (0u64.wrapping_sub(d0)), u) == (odate[blk_ord(j, cm, u as int)] < dl),
{
    let o = prefix_xor(tog) ^ (0u64.wrapping_sub(d0));
    assert forall|u: u64| u < 64 implies #[trigger] bit(o, u) == (odate[blk_ord(j, cm, u as int)] < dl) by {
        lemma_order_flag_at(odate, dl, cm, tog, j, d0, u);
    }
}

/// Induction step of `lemma_order_flags`.
pub proof fn lemma_order_flag_at(odate: Seq<i32>, dl: i32, cm: u64, tog: u64, j: int, d0: u64, u: u64)
    requires
        d0 <= 1, (d0 == 1) == (odate[j] < dl), u < 64,
        0 <= j, j + 64 < odate.len(),
        forall|v: u64| v < 64 ==> #[trigger] bit(tog, v) == (bit(cm, v)
            && ((odate[blk_ord(j, cm, v as int)] < dl) != (odate[j + count_below(cm, v as int)] < dl))),
    ensures bit(prefix_xor(tog) ^ (0u64.wrapping_sub(d0)), u) == (odate[blk_ord(j, cm, u as int)] < dl),
    decreases u,
{
    lemma_bit_flip(prefix_xor(tog), d0, u);
    lemma_prefix_xor(tog, u);
    lemma_count_step(cm, u as int);
    lemma_count_bounds(cm, u as int, u as int + 1);
    lemma_count_nonneg(cm, u as int + 1);
    assert(bit(tog, u) == (bit(cm, u)
        && ((odate[blk_ord(j, cm, u as int)] < dl) != (odate[j + count_below(cm, u as int)] < dl))));
    if u > 0 {
        let w = (u - 1) as u64;
        lemma_order_flag_at(odate, dl, cm, tog, j, d0, w);
        lemma_bit_flip(prefix_xor(tog), d0, w);
        assert(blk_ord(j, cm, w as int) == j + count_below(cm, u as int));
    } else {
        assert(count_below(cm, 0) == 0);
    }
}

/// Every row of the block has the key of its order, when the row before the block has the key of order `j`.
pub proof fn lemma_block_keys(okey: Seq<i64>, kb: Seq<i64>, prev: i64, cm: u64, j: int, t: u64)
    requires
        kb.len() == 64, t < 64, 0 <= j, j + 64 < okey.len(),
        okey[j] == prev,
        forall|u: u64| u < 64 ==> #[trigger] bit(cm, u) == (kb[u as int] != key_before(kb, prev, u as int)),
        forall|s: u64| s < 64 && #[trigger] bit(cm, s) ==> okey[blk_ord(j, cm, s as int)] == kb[s as int],
    ensures okey[blk_ord(j, cm, t as int)] == kb[t as int],
    decreases t,
{
    lemma_count_step(cm, t as int);
    lemma_count_bounds(cm, t as int + 1, 64);
    lemma_count_nonneg(cm, t as int + 1);
    if !bit(cm, t) {
        if t > 0 {
            lemma_block_keys(okey, kb, prev, cm, j, (t - 1) as u64);
        } else {
            assert(count_below(cm, 0) == 0);
        }
    }
}

} // verus!
