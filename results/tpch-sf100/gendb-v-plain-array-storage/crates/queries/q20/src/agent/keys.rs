//! The matching part keys as a bitmap over `[0, kmax)` (`KeyBits`), with a coarse bitmap (one bit per 8 keys, 1/8 of
//! the size, so it stays in a core's cache while lineitem streams) that rejects most other keys before the exact
//! bitmap is read. Built only when every key lies in `[0, KEY_LIMIT)` (`build_keybits`); the query takes its
//! general path otherwise.
use vstd::prelude::*;
use crate::agent::common::bitset::*;

verus! {

/// Keys at or above this bound are not put into a bitmap (2^31 bits = 256 MiB).
pub const KEY_LIMIT: i64 = 0x8000_0000;

/// A key list as integers.
pub open spec fn ints(s: Seq<i64>) -> Seq<int> { s.map_values(|k: i64| k as int) }

/// The bitmaps of a key set.
pub struct KeyBits {
    pub bits: Vec<u64>,
    pub nw: usize,
    pub coarse: Vec<u64>,
    pub ncw: usize,
    pub kmax: u64,
}

/// The bitmap holds exactly the keys, every one below `kmax == 64 * nw`; the coarse bitmap has bit `v / 8` of every
/// key `v`.
pub open spec fn kb_ok(kb: KeyBits, keys: Seq<int>) -> bool {
    &&& kb.bits@.len() == kb.nw && kb.coarse@.len() == kb.ncw
    &&& kb.kmax as int == 64 * kb.nw && kb.nw <= 0x0400_0000
    &&& forall|v: int| #[trigger] wbit(kb.bits@, v) == keys.contains(v)
    &&& forall|v: int| #[trigger] wbit(kb.bits@, v) ==> wbit(kb.coarse@, v / 8)
}

/// A zeroed vector of `n` words.
fn zero_words(n: usize) -> (v: Vec<u64>)
    ensures v@.len() == n, forall|u: int| !#[trigger] wbit(v@, u),
{
    let v = vec![0u64; n];
    proof {
        assert forall|u: int| !#[trigger] wbit(v@, u) by {
            if 0 <= u && u / 64 < n {
                assert(vstd::pervasive::cloned(0u64, v@[u / 64]));
                lemma_bit_zero((u % 64) as u64);
            }
        }
    }
    v
}

/// The bitmaps of `keys`, when every key lies in `[0, KEY_LIMIT)`.
pub fn build_keybits(keys: &Vec<i64>) -> (r: Option<KeyBits>)
    ensures r matches Some(kb) ==> kb_ok(kb, ints(keys@)),
{
    let ghost ks = ints(keys@);
    let n = keys.len();
    let mut maxk: i64 = 0;
    let mut x: usize = 0;
    while x < n
        invariant
            n == keys@.len(), x <= n, 0 <= maxk < KEY_LIMIT,
            forall|y: int| 0 <= y < x ==> 0 <= #[trigger] keys@[y] <= maxk,
        decreases n - x,
    {
        let v = keys[x];
        if v < 0 || v >= KEY_LIMIT {
            return None;
        }
        if v > maxk {
            maxk = v;
        }
        x = x + 1;
    }
    let nw = (maxk as usize) / 64 + 1;
    let ncw = nw / 8 + 1;
    let mut bits = zero_words(nw);
    let mut coarse = zero_words(ncw);
    let mut x: usize = 0;
    while x < n
        invariant
            n == keys@.len(), x <= n, 0 <= maxk < KEY_LIMIT, nw == (maxk as int) / 64 + 1, ncw == nw / 8 + 1,
            ks == ints(keys@),
            forall|y: int| 0 <= y < n ==> 0 <= #[trigger] keys@[y] <= maxk,
            bits@.len() == nw, coarse@.len() == ncw,
            forall|v: int| #[trigger] wbit(bits@, v) == ks.subrange(0, x as int).contains(v),
            forall|v: int| #[trigger] wbit(bits@, v) ==> wbit(coarse@, v / 8),
        decreases n - x,
    {
        let v = keys[x];
        let u = v as u64;
        proof {
            assert(0 <= v <= maxk);
            assert((u as int) / 64 < nw);
            lemma_word_pos(u);
        }
        let ghost before = bits@;
        let ghost cbefore = coarse@;
        wbit_set(&mut bits, u);
        let c = u >> 3u64;
        proof {
            assert(u >> 3u64 == u / 8) by (bit_vector);
            assert((c as int) / 64 < ncw);
        }
        wbit_set(&mut coarse, c);
        proof {
            let pre = ks.subrange(0, x as int);
            let post = ks.subrange(0, x as int + 1);
            assert(post =~= pre.push(v as int));
            assert(ks[x as int] == v as int);
            assert forall|w: int| #[trigger] wbit(bits@, w) == post.contains(w) by {
                if pre.contains(w) {
                    let t = choose|t: int| 0 <= t < pre.len() && pre[t] == w;
                    assert(post[t] == w);
                }
                if post.contains(w) && w != v as int {
                    let t = choose|t: int| 0 <= t < post.len() && post[t] == w;
                    assert(t < pre.len());
                    assert(pre[t] == w);
                }
                if w == v as int {
                    assert(post[x as int] == w);
                }
            }
            assert forall|w: int| #[trigger] wbit(bits@, w) implies wbit(coarse@, w / 8) by {
                if w != v as int {
                    assert(wbit(before, w));
                    assert(wbit(cbefore, w / 8));
                }
            }
        }
        x = x + 1;
    }
    proof {
        assert(ks.subrange(0, n as int) =~= ks);
    }
    Some(KeyBits { bits, nw, coarse, ncw, kmax: (nw as u64) * 64 })
}

/// `v` inside the key range, else 0 (a key outside the range is tested as key 0: the coarse test may then pass,
/// the exact test decides).
pub open spec fn clamp(kb: KeyBits, v: int) -> int { if 0 <= v < kb.kmax { v } else { 0 } }

/// `v` passes the coarse bitmap.
pub open spec fn coarse_hit(kb: KeyBits, v: int) -> bool { wbit(kb.coarse@, clamp(kb, v) / 8) }

/// Every key passes the coarse bitmap.
pub proof fn lemma_key_coarse(kb: KeyBits, keys: Seq<int>, v: int)
    requires kb_ok(kb, keys), keys.contains(v),
    ensures coarse_hit(kb, v),
{
    assert(wbit(kb.bits@, v));
    assert(clamp(kb, v) == v);
}

/// Whether `v` passes the coarse bitmap (`no_unwind`).
pub fn kb_coarse(kb: &KeyBits, v: i64) -> (r: bool)
    requires kb.coarse@.len() == kb.ncw, kb.kmax <= 0x1_0000_0000,
    ensures r == coarse_hit(*kb, v as int),
    no_unwind
{
    let u = if v >= 0 && (v as u64) < kb.kmax { v as u64 } else { 0 };
    assert(u as int == clamp(*kb, v as int));
    let c = u >> 3u64;
    proof { assert(u >> 3u64 == u / 8) by (bit_vector); }
    wbit_test(&kb.coarse, kb.ncw, c)
}

/// Whether `v` is one of the keys by the exact bitmap alone (`no_unwind`).
pub fn kb_exact(kb: &KeyBits, v: i64, Ghost(keys): Ghost<Seq<int>>) -> (r: bool)
    requires kb_ok(*kb, keys), 0 <= v,
    ensures r == keys.contains(v as int),
    no_unwind
{
    wbit_test(&kb.bits, kb.nw, v as u64)
}

/// Whether `v` is one of the keys (`no_unwind`): the coarse bit, then the exact bit.
pub fn kb_has(kb: &KeyBits, v: i64, Ghost(keys): Ghost<Seq<int>>) -> (r: bool)
    requires kb_ok(*kb, keys),
    ensures r == keys.contains(v as int),
    no_unwind
{
    if v < 0 {
        proof { assert(!wbit(kb.bits@, v as int)); }
        return false;
    }
    let u = v as u64;
    if u >= kb.kmax {
        proof { assert(!wbit(kb.bits@, v as int)); }
        return false;
    }
    let c = u >> 3u64;
    proof { assert(u >> 3u64 == u / 8) by (bit_vector); }
    if !wbit_test(&kb.coarse, kb.ncw, c) {
        proof { assert(!wbit(kb.bits@, v as int)); }
        return false;
    }
    wbit_test(&kb.bits, kb.nw, u)
}

} // verus!
