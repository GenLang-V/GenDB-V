//! The set bits of a bit set (bit `x` is bit `x % 64` of `u64` word `x / 64`) as a strictly increasing list of
//! positions (`set_bits_list`): one `trailing_zeros` per set bit, zero words skipped. Turns a scatter of row numbers
//! into a sorted row list without a sort.
use vstd::prelude::*;
use vstd::std_specs::bits::{u64_trailing_zeros, axiom_u64_trailing_zeros};

verus! {

/// Bit `x` of the words `v`.
pub open spec fn wbit(v: Seq<u64>, x: int) -> bool {
    (v[x / 64] >> ((x % 64) as u64)) & 1u64 == 1u64
}

/// Clearing the lowest set bit `t` of `x` (`x & (x - 1)`) keeps every other bit.
proof fn lemma_clear_lowest(x: u64, t: u64, c: u64)
    requires x != 0, t < 64, c < 64, (x >> t) & 1u64 == 1u64, x << sub(64u64, t) == 0u64,
    ensures
        ((x & sub(x, 1u64)) >> c) & 1u64 == (if c == t { 0u64 } else { (x >> c) & 1u64 }),
        (x & sub(x, 1u64)) < x,
{
    assert(((x & sub(x, 1u64)) >> c) & 1u64 == (if c == t { 0u64 } else { (x >> c) & 1u64 })) by (bit_vector)
        requires x != 0, t < 64, c < 64, (x >> t) & 1u64 == 1u64, x << sub(64u64, t) == 0u64;
    assert((x & sub(x, 1u64)) < x) by (bit_vector)
        requires x != 0;
}

/// A clear word bit.
proof fn lemma_zero_word_bit(c: u64)
    requires c < 64,
    ensures (0u64 >> c) & 1u64 == 0u64,
{
    assert((0u64 >> c) & 1u64 == 0u64) by (bit_vector);
}

/// Position `w * 64 + c` is bit `c` of word `w`.
proof fn lemma_pos(w: int, c: int)
    requires 0 <= w, 0 <= c < 64,
    ensures (w * 64 + c) / 64 == w, (w * 64 + c) % 64 == c,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(w * 64 + c, 64, w, c);
}

/// The set bits below `n` of `g`, strictly increasing.
pub fn set_bits_list(g: &Vec<u64>, n: usize, cap: usize) -> (l: Vec<usize>)
    requires
        n <= g@.len() * 64,
        n + 64 <= usize::MAX,
    ensures
        forall|i: int| 0 <= i < l@.len() ==> (#[trigger] l@[i]) < n && wbit(g@, l@[i] as int),
        forall|i: int, j: int| 0 <= i < j < l@.len() ==> #[trigger] l@[i] < #[trigger] l@[j],
        forall|y: int| 0 <= y < n && #[trigger] wbit(g@, y) ==> exists|i: int| 0 <= i < l@.len() && l@[i] == y,
{
    broadcast use axiom_u64_trailing_zeros;
    let mut l: Vec<usize> = Vec::with_capacity(cap);
    let nw = n / 64 + 1;
    let mut w: usize = 0;
    while w < nw && w < g.len()
        invariant
            n <= g@.len() * 64, n + 64 <= usize::MAX, nw == n / 64 + 1,
            w <= nw, w <= g@.len(),
            forall|i: int| 0 <= i < l@.len() ==> (#[trigger] l@[i]) < n && (l@[i] as int) < w * 64 && wbit(g@, l@[i] as int),
            forall|i: int, j: int| 0 <= i < j < l@.len() ==> #[trigger] l@[i] < #[trigger] l@[j],
            forall|y: int| 0 <= y < n && y < w * 64 && #[trigger] wbit(g@, y) ==> exists|i: int| 0 <= i < l@.len() && l@[i] == y,
        decreases nw - w,
    {
        let gw = g[w];
        let mut x = gw;
        let ghost l_w = l@;
        while x != 0
            invariant
                n + 64 <= usize::MAX, w < nw, nw == n / 64 + 1, w < g@.len(), gw == g@[w as int],
                forall|c: u64| c < 64 && #[trigger] ((x >> c) & 1u64) == 1u64 ==> (gw >> c) & 1u64 == 1u64,
                l_w.len() <= l@.len(),
                forall|i: int| 0 <= i < l_w.len() ==> #[trigger] l@[i] == l_w[i],
                forall|i: int| 0 <= i < l_w.len() ==> (#[trigger] l_w[i] as int) < w * 64,
                forall|i: int| 0 <= i < l@.len() ==> (#[trigger] l@[i]) < n && wbit(g@, l@[i] as int),
                forall|i: int| l_w.len() <= i < l@.len() ==> w * 64 <= (#[trigger] l@[i]) < w * 64 + 64,
                forall|i: int, j: int| 0 <= i < j < l@.len() ==> #[trigger] l@[i] < #[trigger] l@[j],
                // every set bit of x lies above the last row listed
                forall|c: u64| c < 64 && #[trigger] ((x >> c) & 1u64) == 1u64 && l@.len() > 0 ==> l@.last() < w * 64 + c,
                // the cleared bits of g's word are listed (when below n)
                forall|c: u64| c < 64 && (w * 64 + c < n) && (gw >> c) & 1u64 == 1u64 && #[trigger] ((x >> c) & 1u64) == 0u64
                    ==> exists|i: int| l_w.len() <= i < l@.len() && l@[i] == w * 64 + c,
            decreases x,
        {
            let t = x.trailing_zeros() as u64;
            let ghost x0 = x;
            let ghost l0 = l@;
            proof {
                assert(t < 64);
                assert forall|c: u64| c < 64 implies ((x & sub(x, 1u64)) >> c) & 1u64 == (if c == t { 0u64 } else { (x >> c) & 1u64 }) by {
                    lemma_clear_lowest(x, t, c);
                }
                lemma_clear_lowest(x, t, 0);
                lemma_pos(w as int, t as int);
            }
            let y = w * 64 + t as usize;
            if y < n {
                l.push(y);
                proof {
                    assert(wbit(g@, y as int));
                    assert(l@[l@.len() - 1] == y);
                }
            }
            x = x & (x - 1);
            proof {
                assert forall|c: u64| c < 64 && #[trigger] ((x >> c) & 1u64) == 1u64 implies (gw >> c) & 1u64 == 1u64 by {
                    lemma_clear_lowest(x0, t, c);
                    assert((x0 >> c) & 1u64 == 1u64);
                }
                assert forall|i: int| 0 <= i < l_w.len() implies #[trigger] l@[i] == l_w[i] by {
                    assert(l@[i] == l0[i]);
                }
                assert forall|i: int| 0 <= i < l@.len() implies (#[trigger] l@[i]) < n && wbit(g@, l@[i] as int) by {
                    if i < l0.len() {
                        assert(l@[i] == l0[i]);
                    }
                }
                assert forall|i: int| l_w.len() <= i < l@.len() implies w * 64 <= (#[trigger] l@[i]) < w * 64 + 64 by {
                    if i < l0.len() {
                        assert(l@[i] == l0[i]);
                    }
                }
                assert forall|i: int, j: int| 0 <= i < j < l@.len() implies #[trigger] l@[i] < #[trigger] l@[j] by {
                    if j >= l0.len() {
                        assert(l@[i] == l0[i]);
                        assert(l0.len() > 0 ==> l0.last() < w * 64 + t);
                        assert(l0[i] <= l0.last());
                    } else {
                        assert(l@[i] == l0[i] && l@[j] == l0[j]);
                    }
                }
                assert forall|c: u64| c < 64 && #[trigger] ((x >> c) & 1u64) == 1u64 && l@.len() > 0 implies l@.last() < w * 64 + c by {
                    assert(c != t);
                    assert((x0 >> c) & 1u64 == 1u64);
                    if c < t {
                        assert((x0 >> c) & 1u64 == 0u64);
                    }
                    if l@.len() == l0.len() {
                        assert(l@.last() == l0.last());
                    }
                }
                assert forall|c: u64| c < 64 && (w * 64 + c < n) && (gw >> c) & 1u64 == 1u64 && #[trigger] ((x >> c) & 1u64) == 0u64
                    implies exists|i: int| l_w.len() <= i < l@.len() && l@[i] == w * 64 + c by {
                    if c == t {
                        assert(l@[l@.len() - 1] == w * 64 + c);
                    } else {
                        assert((x0 >> c) & 1u64 == 0u64);
                        let i = choose|i: int| l_w.len() <= i < l0.len() && l0[i] == w * 64 + c;
                        assert(l@[i] == l0[i]);
                    }
                }
            }
        }
        proof {
            assert forall|i: int| 0 <= i < l@.len() implies (#[trigger] l@[i]) < n && (l@[i] as int) < (w + 1) * 64
                && wbit(g@, l@[i] as int) by {
                if i < l_w.len() {
                    assert(l@[i] == l_w[i]);
                }
            }
            assert forall|y: int| 0 <= y < n && y < (w + 1) * 64 && #[trigger] wbit(g@, y)
                implies exists|i: int| 0 <= i < l@.len() && l@[i] == y by {
                if y < w * 64 {
                    let i = choose|i: int| 0 <= i < l_w.len() && l_w[i] == y;
                    assert(l@[i] == l_w[i]);
                } else {
                    let c = (y - w * 64) as u64;
                    lemma_pos(w as int, c as int);
                    assert(y == w * 64 + c);
                    lemma_zero_word_bit(c);
                    assert((gw >> c) & 1u64 == 1u64);
                    assert((x >> c) & 1u64 == 0u64);
                }
            }
        }
        w = w + 1;
    }
    proof {
        assert forall|y: int| 0 <= y < n && #[trigger] wbit(g@, y) implies exists|i: int| 0 <= i < l@.len() && l@[i] == y by {
            if w >= nw {
                assert(y < nw * 64) by {
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, 64);
                }
            } else {
                assert(w == g@.len());
            }
        }
    }
    l
}

} // verus!
