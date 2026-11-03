//! The suppliers of nation `$1` as count slots, and the map from a supplier key to its slot.
//!
//! Slot `t` is the `t`-th supplier row (in stored order) whose nation key is one of the nation keys named `$1`; its
//! key is `skeys[t]` (distinct under the supplier primary key). `slot_of(k)` finds the slot holding key `k`: through a
//! dense table over the slot keys' range (`slots[k - kmin]`, `NONE` where no slot has the key) when that range is
//! small, else by a scan of the slot keys. Both are `no_unwind`, for worker tasks.
use vstd::prelude::*;
use std::sync::Arc;

verus! {

/// No slot.
pub const NONE: u32 = 0xffff_ffff;

/// Largest key range of the dense table (entries).
pub const DENSE_MAX: usize = 1usize << 26;

/// The slot keys and their lookup table.
pub struct SuppMap {
    /// Number of slots.
    pub ns: usize,
    /// Key of each slot.
    pub skeys: Arc<Vec<i64>>,
    /// Whether the dense table is used.
    pub dense: bool,
    /// First key of the dense table's range.
    pub kmin: i64,
    /// Entries of the dense table (its key range `[kmin, kmin + range)`).
    pub range: usize,
    /// The dense table: the slot of key `kmin + v`, or `NONE`.
    pub slots: Arc<Vec<u32>>,
    /// One bit per dense-table entry: set exactly when the entry holds a slot (a small filter in front of it).
    pub bits: Arc<Vec<u64>>,
}

/// Bit `b` of word `w`.
pub open spec fn wbit(w: u64, b: u64) -> bool {
    (w >> b) & 1u64 == 1u64
}

/// Bit `v` of the bit words.
pub open spec fn bit_of(bits: Seq<u64>, v: int) -> bool {
    wbit(bits[v / 64], (v % 64) as u64)
}

proof fn lemma_wbit_set(w: u64, b: u64, c: u64)
    requires b < 64, c < 64,
    ensures wbit(w | (1u64 << b), c) == (c == b || wbit(w, c)),
{
    assert(((w | (1u64 << b)) >> c) & 1u64 == 1u64 <==> (c == b || (w >> c) & 1u64 == 1u64)) by (bit_vector)
        requires b < 64, c < 64;
}

proof fn lemma_wbit_zero(c: u64)
    requires c < 64,
    ensures !wbit(0u64, c),
{
    assert((0u64 >> c) & 1u64 != 1u64) by (bit_vector) requires c < 64;
}

/// The slot keys are distinct.
pub open spec fn keys_unique(ks: Seq<i64>) -> bool {
    forall|a: int, b: int| 0 <= a < ks.len() && 0 <= b < ks.len() && a != b ==> #[trigger] ks[a] != #[trigger] ks[b]
}

/// The dense table is right for the slot keys.
pub open spec fn dense_ok(ks: Seq<i64>, kmin: int, range: int, sl: Seq<u32>) -> bool {
    &&& sl.len() == range
    &&& forall|t: int| 0 <= t < ks.len() ==> kmin <= #[trigger] ks[t] < kmin + range
    &&& forall|t: int| 0 <= t < ks.len() ==> #[trigger] sl[ks[t] - kmin] == t
    &&& forall|v: int| 0 <= v < range && #[trigger] sl[v] != NONE ==> sl[v] < ks.len() && ks[sl[v] as int] == kmin + v
}

/// The map is well formed.
pub open spec fn smap_ok(m: SuppMap) -> bool {
    &&& m.skeys@.len() == m.ns
    &&& keys_unique(m.skeys@)
    &&& m.dense ==> m.ns < NONE
    &&& m.dense ==> dense_ok(m.skeys@, m.kmin as int, m.range as int, m.slots@)
    &&& m.dense ==> m.bits@.len() * 64 >= m.range
    &&& m.dense ==> forall|v: int| 0 <= v < m.range ==> #[trigger] bit_of(m.bits@, v) == (m.slots@[v] != NONE)
}

/// The slot of supplier key `k`, if any.
pub fn slot_of(m: &SuppMap, k: i64) -> (r: Option<usize>)
    requires smap_ok(*m),
    ensures
        r matches Some(t) ==> t < m.ns && m.skeys@[t as int] == k,
        r is None ==> forall|t: int| 0 <= t < m.ns ==> #[trigger] m.skeys@[t] != k,
    no_unwind
{
    if m.dense {
        if k >= m.kmin && (k as i128 - m.kmin as i128) < m.range as i128 {
            let v = (k as i128 - m.kmin as i128) as usize;
            proof {
                assert(v / 64 < m.bits@.len()) by (nonlinear_arith)
                    requires v < m.range, m.bits@.len() * 64 >= m.range;
            }
            let w = m.bits[v / 64];
            if (w >> ((v % 64) as u64)) & 1u64 == 0 {
                proof {
                    assert(!bit_of(m.bits@, v as int));
                    assert forall|t: int| 0 <= t < m.ns implies #[trigger] m.skeys@[t] != k by {
                        if m.skeys@[t] == k {
                            assert(m.slots@[m.skeys@[t] - m.kmin] == t);
                        }
                    }
                }
                return None;
            }
            let s = m.slots[v];
            if s != NONE {
                return Some(s as usize);
            }
            proof {
                assert forall|t: int| 0 <= t < m.ns implies #[trigger] m.skeys@[t] != k by {
                    if m.skeys@[t] == k {
                        assert(m.slots@[m.skeys@[t] - m.kmin] == t);
                    }
                }
            }
        }
        return None;
    }
    let ns = m.ns;
    let mut t: usize = 0;
    while t < ns
        invariant
            smap_ok(*m),
            ns == m.ns,
            t <= ns,
            forall|u: int| 0 <= u < t ==> #[trigger] m.skeys@[u] != k,
        decreases ns - t,
    {
        if m.skeys[t] == k {
            return Some(t);
        }
        t = t + 1;
    }
    None
}

/// The map over slot keys `ks` (distinct): the dense table when the key range has at most `DENSE_MAX` entries.
pub fn build_map(ks: Vec<i64>) -> (m: SuppMap)
    requires
        keys_unique(ks@),
    ensures
        smap_ok(m),
        m.skeys@ == ks@,
{
    let ns = ks.len();
    let mut kmin: i64 = 0;
    let mut kmax: i64 = 0;
    let mut t: usize = 0;
    while t < ns
        invariant
            ns == ks@.len(),
            t <= ns,
            kmin <= kmax,
            t > 0 ==> forall|u: int| 0 <= u < t ==> kmin <= #[trigger] ks@[u] <= kmax,
        decreases ns - t,
    {
        let k = ks[t];
        if t == 0 {
            kmin = k;
            kmax = k;
        } else {
            if k < kmin {
                kmin = k;
            }
            if k > kmax {
                kmax = k;
            }
        }
        t = t + 1;
    }
    let span = kmax as i128 - kmin as i128;
    if ns == 0 || ns >= NONE as usize || span >= DENSE_MAX as i128 {
        return SuppMap { ns, skeys: Arc::new(ks), dense: false, kmin: 0, range: 0, slots: Arc::new(Vec::new()),
            bits: Arc::new(Vec::new()) };
    }
    let range = (span + 1) as usize;
    let mut sl: Vec<u32> = super::common::fill::fill_u32(range, NONE);
    let nw = range / 64 + 1;
    let mut bits: Vec<u64> = super::common::fill::fill_u64(nw, 0u64);
    proof {
        assert forall|v: int| 0 <= v < range implies #[trigger] bit_of(bits@, v) == (sl@[v] != NONE) by {
            vstd::arithmetic::div_mod::lemma_div_pos_is_pos(v, 64);
            lemma_wbit_zero((v % 64) as u64);
            assert(v / 64 < nw) by (nonlinear_arith) requires 0 <= v < range, nw == range / 64 + 1;
        }
    }
    let mut t: usize = 0;
    while t < ns
        invariant
            ns == ks@.len(),
            ns < NONE,
            keys_unique(ks@),
            t <= ns,
            range == kmax - kmin + 1,
            sl@.len() == range,
            forall|u: int| 0 <= u < ns ==> kmin <= #[trigger] ks@[u] <= kmax,
            forall|u: int| 0 <= u < t ==> #[trigger] sl@[ks@[u] - kmin] == u,
            forall|v: int| 0 <= v < range && #[trigger] sl@[v] != NONE ==> sl@[v] < t && ks@[sl@[v] as int] == kmin + v,
            nw == range / 64 + 1,
            bits@.len() == nw,
            forall|v: int| 0 <= v < range ==> #[trigger] bit_of(bits@, v) == (sl@[v] != NONE),
        decreases ns - t,
    {
        let v = (ks[t] as i128 - kmin as i128) as usize;
        let ghost old_sl = sl@;
        let ghost old_bits = bits@;
        sl[v] = t as u32;
        proof {
            assert(v / 64 < nw) by (nonlinear_arith) requires v < range, nw == range / 64 + 1;
        }
        let wi = v / 64;
        let wb = (v % 64) as u64;
        let wv = bits[wi] | (1u64 << wb);
        bits[wi] = wv;
        proof {
            assert(sl@[v as int] == t as u32);
            assert forall|u: int| 0 <= u < range implies #[trigger] bit_of(bits@, u) == (sl@[u] != NONE) by {
                vstd::arithmetic::div_mod::lemma_div_pos_is_pos(u, 64);
                vstd::arithmetic::div_mod::lemma_mod_pos_bound(u, 64);
                assert(u / 64 < nw) by (nonlinear_arith) requires 0 <= u < range, nw == range / 64 + 1;
                let ub = (u % 64) as u64;
                if u / 64 == wi as int {
                    assert(bits@[u / 64] == old_bits[wi as int] | (1u64 << wb));
                    lemma_wbit_set(old_bits[wi as int], wb, ub);
                    if u == v as int {
                        assert(ub == wb);
                        assert(wbit(bits@[u / 64], ub));
                        assert(bit_of(bits@, u));
                        assert(sl@[u] != NONE);
                    } else {
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(u, 64);
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(v as int, 64);
                        assert(ub != wb);
                        assert(old_sl[u] == sl@[u]);
                        assert(bit_of(old_bits, u) == wbit(old_bits[wi as int], ub));
                        assert(bit_of(old_bits, u) == (old_sl[u] != NONE));
                        assert(bit_of(bits@, u) == wbit(bits@[u / 64], ub));
                    }
                } else {
                    assert(bits@[u / 64] == old_bits[u / 64]);
                    assert(u != v as int);
                    assert(old_sl[u] == sl@[u]);
                    assert(bit_of(old_bits, u) == (old_sl[u] != NONE));
                    assert(bit_of(bits@, u) == bit_of(old_bits, u));
                }
            }
        }
        t = t + 1;
    }
    let m = SuppMap { ns, skeys: Arc::new(ks), dense: true, kmin, range, slots: Arc::new(sl), bits: Arc::new(bits) };
    proof {
        assert forall|u: int| 0 <= u < ns implies m.kmin <= #[trigger] m.skeys@[u] < m.kmin + m.range by {
            assert(kmin <= ks@[u] <= kmax);
        }
    }
    m
}

} // verus!
