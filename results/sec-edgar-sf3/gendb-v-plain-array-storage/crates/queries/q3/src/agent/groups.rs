//! The groups `(name, cik)` of the ranks with rows (calling thread): ranks in order; a new key opens a group
//! (first-occurrence order, `gks`), every rank's total is added to its group (`psum`). The same pass counts the
//! distinct ciks (`dciks`) and the total of all ranks (`tsum`).
//!
//! Lookup structure: linear probing without wrap-around over the groups, home slot from the cik alone, so every
//! group of one cik lies in the occupied run from that cik's home: a probe for `(name, cik)` that meets an empty
//! slot has seen every group of that cik (it finds the key, or learns whether the cik is new).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::link::query::{text_wf, text_at, TextView};
use crate::agent::common::bytes::*;
use crate::agent::common::wide::*;
use crate::agent::keys::{pow2i, home, lemma_home_bound, occupied, lemma_occupied_range, lemma_occupied_update,
    lemma_occupied_zero, lemma_occupied_nonneg};

verus! {

/// The sub columns of the group key.
#[derive(Clone, Copy)]
pub struct KeyCols {
    pub name_off: &'static [i64],
    pub name_bytes: &'static [u8],
    pub cik: &'static [i32],
    pub n: usize,
    pub bytes_len: usize,
}

impl KeyCols {
    pub open spec fn text(&self) -> TextView {
        TextView { offsets: self.name_off@, bytes: self.name_bytes@ }
    }

    pub open spec fn name(&self, j: int) -> Seq<u8> {
        text_at(self.text(), j)
    }

    pub open spec fn cik(&self, j: int) -> int {
        self.cik@[j] as int
    }

    /// The outer group key `(name, cik)` of sub row `j`.
    pub open spec fn okey(&self, j: int) -> Row {
        seq![Val::Text(self.name(j)), Val::Int(self.cik(j))]
    }

    #[verifier::opaque]
    pub open spec fn wf(&self) -> bool {
        &&& text_wf(self.text(), self.n as int)
        &&& self.cik@.len() == self.n
        &&& self.bytes_len == self.name_bytes@.len()
    }
}

/// Row `j`'s name bytes are a range of the bytes; the cik column has a value per row.
pub proof fn lemma_kc_row(kc: &KeyCols, j: int)
    requires kc.wf(), 0 <= j < kc.n,
    ensures
        0 <= kc.name_off@[j] <= kc.name_off@[j + 1] <= kc.name_bytes@.len(),
        kc.name_off@.len() == kc.n + 1, kc.cik@.len() == kc.n, kc.bytes_len == kc.name_bytes@.len(),
{
    reveal(KeyCols::wf);
    assert(0 <= kc.text().offsets[j] <= kc.text().offsets[j + 1] <= kc.text().bytes.len());
}

/// The inputs of the grouping: rank -> sub row, the totals and whether the rank has rows.
pub open spec fn ranks_wf(kc: &KeyCols, qr: Seq<usize>, tot: Seq<Wide>, seen: Seq<bool>) -> bool {
    &&& tot.len() == qr.len() && seen.len() == qr.len()
    &&& qr.len() < 0x1_0000_0000_0000_0000
    &&& forall|id: int| 0 <= id < qr.len() ==> #[trigger] qr[id] < kc.n
    &&& forall|id: int| 0 <= id < qr.len() ==> -rank_limit() <= #[trigger] wval(tot[id]) <= rank_limit()
}

/// The bound of one rank's total (`2^158`).
pub open spec fn rank_limit() -> int {
    0x4000_0000int * two128()
}

/// The group keys of the ranks below `m` with rows, first-occurrence order.
pub open spec fn gks(kc: &KeyCols, qr: Seq<usize>, seen: Seq<bool>, m: int) -> Seq<Row>
    decreases m,
{
    if m <= 0 {
        Seq::empty()
    } else {
        let d = gks(kc, qr, seen, m - 1);
        let k = kc.okey(qr[m - 1] as int);
        if seen[m - 1] && !d.contains(k) { d.push(k) } else { d }
    }
}

/// The distinct ciks of those ranks.
pub open spec fn dciks(kc: &KeyCols, qr: Seq<usize>, seen: Seq<bool>, m: int) -> Seq<int>
    decreases m,
{
    if m <= 0 {
        Seq::empty()
    } else {
        let d = dciks(kc, qr, seen, m - 1);
        let c = kc.cik(qr[m - 1] as int);
        if seen[m - 1] && !d.contains(c) { d.push(c) } else { d }
    }
}

/// The sum of the totals of the ranks below `m` with rows and key `k`.
pub open spec fn psum(kc: &KeyCols, qr: Seq<usize>, tot: Seq<Wide>, seen: Seq<bool>, k: Row, m: int) -> int
    decreases m,
{
    if m <= 0 {
        0
    } else {
        psum(kc, qr, tot, seen, k, m - 1) + if seen[m - 1] && kc.okey(qr[m - 1] as int) == k { wval(tot[m - 1]) } else { 0 }
    }
}

/// The sum of the totals of the ranks below `m` with rows.
pub open spec fn tsum(qr: Seq<usize>, tot: Seq<Wide>, seen: Seq<bool>, m: int) -> int
    decreases m,
{
    if m <= 0 { 0 } else { tsum(qr, tot, seen, m - 1) + if seen[m - 1] { wval(tot[m - 1]) } else { 0 } }
}

pub proof fn lemma_psum_bound(kc: &KeyCols, qr: Seq<usize>, tot: Seq<Wide>, seen: Seq<bool>, k: Row, m: int)
    requires ranks_wf(kc, qr, tot, seen), 0 <= m <= qr.len(),
    ensures
        -(m * rank_limit()) <= psum(kc, qr, tot, seen, k, m) <= m * rank_limit(),
        -(m * rank_limit()) <= tsum(qr, tot, seen, m) <= m * rank_limit(),
    decreases m,
{
    if m > 0 {
        lemma_psum_bound(kc, qr, tot, seen, k, m - 1);
        let b = rank_limit();
        assert(-b <= wval(tot[m - 1]) <= b);
        assert(m * b == (m - 1) * b + b) by (nonlinear_arith);
        assert(psum(kc, qr, tot, seen, k, m) == psum(kc, qr, tot, seen, k, m - 1)
            + if seen[m - 1] && kc.okey(qr[m - 1] as int) == k { wval(tot[m - 1]) } else { 0 });
        assert(tsum(qr, tot, seen, m) == tsum(qr, tot, seen, m - 1) + if seen[m - 1] { wval(tot[m - 1]) } else { 0 });
    }
}

/// Totals over fewer than 2^31 ranks stay in `Wide`'s exact range.
pub proof fn lemma_sums_in_range(kc: &KeyCols, qr: Seq<usize>, tot: Seq<Wide>, seen: Seq<bool>, k: Row, m: int)
    requires ranks_wf(kc, qr, tot, seen), 0 <= m <= qr.len(),
    ensures
        -wide_limit() <= psum(kc, qr, tot, seen, k, m) <= wide_limit(),
        -wide_limit() <= tsum(qr, tot, seen, m) <= wide_limit(),
{
    lemma_psum_bound(kc, qr, tot, seen, k, m);
    let b = rank_limit();
    assert(m * b <= 0x1_0000_0000_0000_0000 * b) by (nonlinear_arith) requires 0 <= m <= 0x1_0000_0000_0000_0000int, b >= 0;
    assert(0x1_0000_0000_0000_0000 * b <= wide_limit());
}

// ------------------------------------------------------------------------------------------------ the group table

/// The hash of a cik.
pub open spec fn cik_hash(c: i32) -> u64 {
    ((c as u32) as u64 | 0x1_0000_0000u64).wrapping_mul(0x9E37_79B9_7F4A_7C15u64)
}

pub struct Groups {
    pub bits: u64,
    pub nslots: usize,
    /// Slot -> group + 1 (0: empty).
    pub slots: Vec<u32>,
    /// Group -> its cik, its first sub row, its sum.
    pub cik: Vec<i32>,
    pub rep: Vec<usize>,
    pub sum: Vec<Wide>,
    /// Number of distinct ciks, total of all ranks.
    pub ncik: usize,
    pub total: Wide,
}

/// Occupied slot `s`: a group with its home at or before `s`, every slot in between occupied.
pub open spec fn gslot_ok(g: &Groups, s: int) -> bool {
    let i = g.slots@[s] as int - 1;
    &&& 0 <= i < g.rep@.len()
    &&& home(cik_hash(g.cik@[i]), g.bits) <= s
    &&& forall|t: int| home(cik_hash(g.cik@[i]), g.bits) <= t < s ==> #[trigger] g.slots@[t] != 0
}

pub open spec fn gstored(g: &Groups, i: int) -> bool {
    exists|s: int| 0 <= s < g.nslots && #[trigger] g.slots@[s] != 0 && g.slots@[s] as int - 1 == i
}

/// The table's shape and probing invariant.
#[verifier::opaque]
pub open spec fn table_inv(g: &Groups) -> bool {
    &&& 1 <= g.bits <= 30
    &&& g.nslots == g.slots@.len()
    &&& g.nslots < usize::MAX
    &&& g.cik@.len() == g.rep@.len() && g.sum@.len() == g.rep@.len()
    &&& pow2i(g.bits as nat) + g.rep@.len() < g.nslots
    &&& forall|s: int| 0 <= s < g.nslots && #[trigger] g.slots@[s] != 0 ==> gslot_ok(g, s)
    &&& forall|i: int| 0 <= i < g.rep@.len() ==> #[trigger] gstored(g, i)
    &&& occupied_u32(g.slots@, g.nslots as int) == g.rep@.len()
}

/// Number of occupied slots among the first `m`.
pub open spec fn occupied_u32(t: Seq<u32>, m: int) -> int
    decreases m,
{
    if m <= 0 { 0 } else { occupied_u32(t, m - 1) + if t[m - 1] != 0 { 1int } else { 0int } }
}

/// The groups of the ranks below `m`.
#[verifier::opaque]
pub open spec fn groups_ok(g: &Groups, kc: &KeyCols, qr: Seq<usize>, tot: Seq<Wide>, seen: Seq<bool>, m: int) -> bool {
    let ks = gks(kc, qr, seen, m);
    &&& g.rep@.len() == ks.len()
    &&& g.rep@.len() <= m
    &&& forall|i: int| 0 <= i < ks.len() ==> #[trigger] g.rep@[i] < kc.n
    &&& forall|i: int| 0 <= i < ks.len() ==> kc.okey(#[trigger] g.rep@[i] as int) == ks[i]
    &&& forall|i: int| 0 <= i < ks.len() ==> #[trigger] g.cik@[i] as int == kc.cik(g.rep@[i] as int)
    &&& forall|i: int| 0 <= i < ks.len() ==> #[trigger] wval(g.sum@[i]) == psum(kc, qr, tot, seen, ks[i], m)
    &&& g.ncik == dciks(kc, qr, seen, m).len()
    &&& wval(g.total) == tsum(qr, tot, seen, m)
}

// ------------------------------------------------------------------------------------------------- list lemmas

/// `gks` holds exactly the keys of the ranks with rows, once each.
pub proof fn lemma_gks(kc: &KeyCols, qr: Seq<usize>, seen: Seq<bool>, m: int)
    requires 0 <= m <= qr.len(), m <= seen.len(),
    ensures
        gks(kc, qr, seen, m).no_duplicates(),
        gks(kc, qr, seen, m).len() <= m,
        forall|k: Row| gks(kc, qr, seen, m).contains(k) <==>
            exists|id: int| 0 <= id < m && seen[id] && #[trigger] kc.okey(qr[id] as int) == k,
    decreases m,
{
    if m > 0 {
        lemma_gks(kc, qr, seen, m - 1);
        let d = gks(kc, qr, seen, m - 1);
        let k0 = kc.okey(qr[m - 1] as int);
        assert forall|k: Row| gks(kc, qr, seen, m).contains(k) <==>
            exists|id: int| 0 <= id < m && seen[id] && #[trigger] kc.okey(qr[id] as int) == k by {
            if gks(kc, qr, seen, m).contains(k) {
                if d.contains(k) {
                    let id = choose|id: int| 0 <= id < m - 1 && seen[id] && #[trigger] kc.okey(qr[id] as int) == k;
                    assert(0 <= id < m && seen[id] && kc.okey(qr[id] as int) == k);
                } else {
                    assert(seen[m - 1] && !d.contains(k0));
                    assert(gks(kc, qr, seen, m) == d.push(k0));
                    let t = choose|t: int| 0 <= t < d.push(k0).len() && d.push(k0)[t] == k;
                    if t < d.len() {
                        assert(d[t] == k);
                    }
                    assert(k == k0);
                }
            }
            if exists|id: int| 0 <= id < m && seen[id] && #[trigger] kc.okey(qr[id] as int) == k {
                let id = choose|id: int| 0 <= id < m && seen[id] && #[trigger] kc.okey(qr[id] as int) == k;
                if id < m - 1 {
                    assert(d.contains(k));
                    if seen[m - 1] && !d.contains(k0) {
                        let t = choose|t: int| 0 <= t < d.len() && d[t] == k;
                        assert(gks(kc, qr, seen, m)[t] == k);
                    }
                } else {
                    if !d.contains(k0) {
                        assert(gks(kc, qr, seen, m)[d.len() as int] == k0);
                    }
                }
            }
        }
        if seen[m - 1] && !d.contains(k0) {
            assert forall|a: int, b: int| 0 <= a < b < d.push(k0).len() implies d.push(k0)[a] != d.push(k0)[b] by {
                if b == d.len() {
                    assert(d.contains(d[a]));
                }
            }
        }
    }
}

/// `dciks` holds exactly the ciks of the ranks with rows, once each.
pub proof fn lemma_dciks(kc: &KeyCols, qr: Seq<usize>, seen: Seq<bool>, m: int)
    requires 0 <= m <= qr.len(), m <= seen.len(),
    ensures
        forall|c: int| dciks(kc, qr, seen, m).contains(c) <==>
            exists|id: int| 0 <= id < m && seen[id] && #[trigger] kc.cik(qr[id] as int) == c,
    decreases m,
{
    if m > 0 {
        lemma_dciks(kc, qr, seen, m - 1);
        let d = dciks(kc, qr, seen, m - 1);
        let c0 = kc.cik(qr[m - 1] as int);
        assert forall|c: int| dciks(kc, qr, seen, m).contains(c) <==>
            exists|id: int| 0 <= id < m && seen[id] && #[trigger] kc.cik(qr[id] as int) == c by {
            if dciks(kc, qr, seen, m).contains(c) {
                if d.contains(c) {
                    let id = choose|id: int| 0 <= id < m - 1 && seen[id] && #[trigger] kc.cik(qr[id] as int) == c;
                    assert(0 <= id < m && seen[id] && kc.cik(qr[id] as int) == c);
                } else {
                    assert(dciks(kc, qr, seen, m) == d.push(c0));
                    let t = choose|t: int| 0 <= t < d.push(c0).len() && d.push(c0)[t] == c;
                    if t < d.len() {
                        assert(d[t] == c);
                    }
                    assert(c == c0);
                }
            }
            if exists|id: int| 0 <= id < m && seen[id] && #[trigger] kc.cik(qr[id] as int) == c {
                let id = choose|id: int| 0 <= id < m && seen[id] && #[trigger] kc.cik(qr[id] as int) == c;
                if id < m - 1 {
                    assert(d.contains(c));
                    if seen[m - 1] && !d.contains(c0) {
                        let t = choose|t: int| 0 <= t < d.len() && d[t] == c;
                        assert(dciks(kc, qr, seen, m)[t] == c);
                    }
                } else {
                    if !d.contains(c0) {
                        assert(dciks(kc, qr, seen, m)[d.len() as int] == c0);
                    }
                }
            }
        }
    }
}

/// A key without a rank (with rows) below `m` has sum 0.
pub proof fn lemma_psum_absent(kc: &KeyCols, qr: Seq<usize>, tot: Seq<Wide>, seen: Seq<bool>, k: Row, m: int)
    requires 0 <= m <= qr.len(), m <= seen.len(), forall|id: int| 0 <= id < m && seen[id] ==> #[trigger] kc.okey(qr[id] as int) != k,
    ensures psum(kc, qr, tot, seen, k, m) == 0,
    decreases m,
{
    if m > 0 {
        lemma_psum_absent(kc, qr, tot, seen, k, m - 1);
    }
}

// ------------------------------------------------------------------------------------------------- table lemmas

proof fn lemma_occ_u32_same(a: Seq<u32>, b: Seq<u32>, m: int)
    requires 0 <= m <= a.len(), m <= b.len(), forall|t: int| 0 <= t < m ==> #[trigger] a[t] == b[t],
    ensures occupied_u32(a, m) == occupied_u32(b, m),
    decreases m,
{
    if m > 0 {
        lemma_occ_u32_same(a, b, m - 1);
    }
}

proof fn lemma_occ_u32_update(t: Seq<u32>, m: int, s: int, v: u32)
    requires 0 <= s < m <= t.len(), t[s] == 0, v != 0,
    ensures occupied_u32(t.update(s, v), m) == occupied_u32(t, m) + 1,
    decreases m,
{
    if m - 1 > s {
        lemma_occ_u32_update(t, m - 1, s, v);
    } else {
        lemma_occ_u32_same(t, t.update(s, v), s);
    }
}

proof fn lemma_occ_u32_nonneg(t: Seq<u32>, m: int)
    ensures occupied_u32(t, m) >= 0,
    decreases m,
{
    if m > 0 {
        lemma_occ_u32_nonneg(t, m - 1);
    }
}

proof fn lemma_occ_u32_range(t: Seq<u32>, m: int, a: int, b: int)
    requires 0 <= a <= b <= m <= t.len(), forall|u: int| a <= u < b ==> #[trigger] t[u] != 0,
    ensures occupied_u32(t, m) >= b - a,
    decreases m,
{
    if a == b {
        lemma_occ_u32_nonneg(t, m);
    } else if m > b {
        lemma_occ_u32_range(t, m - 1, a, b);
    } else {
        lemma_occ_u32_range(t, m - 1, a, b - 1);
        assert(t[m - 1] != 0);
    }
}

proof fn lemma_occ_u32_zero(t: Seq<u32>, m: int)
    requires 0 <= m <= t.len(), forall|u: int| 0 <= u < m ==> #[trigger] t[u] == 0,
    ensures occupied_u32(t, m) == 0,
    decreases m,
{
    if m > 0 {
        lemma_occ_u32_zero(t, m - 1);
    }
}

pub proof fn lemma_table_shape(g: &Groups)
    requires table_inv(g),
    ensures
        1 <= g.bits <= 30, g.nslots == g.slots@.len(), g.nslots < usize::MAX,
        g.cik@.len() == g.rep@.len(), g.sum@.len() == g.rep@.len(),
        pow2i(g.bits as nat) + g.rep@.len() < g.nslots,
        occupied_u32(g.slots@, g.nslots as int) == g.rep@.len(),
{
    reveal(table_inv);
}

pub proof fn lemma_table_slot(g: &Groups, s: int)
    requires table_inv(g), 0 <= s < g.nslots, g.slots@[s] != 0,
    ensures gslot_ok(g, s),
{
    reveal(table_inv);
}

pub proof fn lemma_table_stored(g: &Groups, i: int)
    requires table_inv(g), 0 <= i < g.rep@.len(),
    ensures gstored(g, i),
{
    reveal(table_inv);
}

/// A probe that met the empty slot `s` from the home of cik `c`: no group of cik `c` beyond the slots seen.
pub proof fn lemma_table_absent(g: &Groups, c: i32, s: int)
    requires
        table_inv(g),
        home(cik_hash(c), g.bits) <= s < g.nslots, g.slots@[s] == 0,
        forall|t: int| home(cik_hash(c), g.bits) <= t < s ==> #[trigger] g.slots@[t] != 0,
    ensures
        forall|i: int| 0 <= i < g.rep@.len() && g.cik@[i] == c ==>
            exists|t: int| home(cik_hash(c), g.bits) <= t < s && #[trigger] g.slots@[t] as int - 1 == i,
{
    assert forall|i: int| 0 <= i < g.rep@.len() && g.cik@[i] == c implies
        exists|t: int| home(cik_hash(c), g.bits) <= t < s && #[trigger] g.slots@[t] as int - 1 == i by {
        lemma_table_stored(g, i);
        let t = choose|t: int| 0 <= t < g.nslots && #[trigger] g.slots@[t] != 0 && g.slots@[t] as int - 1 == i;
        lemma_table_slot(g, t);
        if t > s {
            assert(g.slots@[s] != 0);
        }
        assert(home(cik_hash(c), g.bits) <= t);
    }
}

/// An empty table.
pub proof fn lemma_table_init(g: &Groups)
    requires
        1 <= g.bits <= 30, g.nslots == g.slots@.len(), g.nslots < usize::MAX,
        g.rep@.len() == 0, g.cik@.len() == 0, g.sum@.len() == 0,
        pow2i(g.bits as nat) < g.nslots,
        forall|s: int| 0 <= s < g.slots@.len() ==> #[trigger] g.slots@[s] == 0,
    ensures table_inv(g),
{
    reveal(table_inv);
    lemma_occ_u32_zero(g.slots@, g.nslots as int);
}

/// A new group at the empty slot `s` reached from its cik's home.
pub proof fn lemma_table_insert(g0: &Groups, g1: &Groups, s: int, c: i32)
    requires
        table_inv(g0),
        home(cik_hash(c), g0.bits) <= s < g0.nslots, g0.slots@[s] == 0,
        forall|t: int| home(cik_hash(c), g0.bits) <= t < s ==> #[trigger] g0.slots@[t] != 0,
        g0.rep@.len() + 1 < 0xffff_ffff,
        g1.bits == g0.bits, g1.nslots == g0.nslots,
        g1.slots@ == g0.slots@.update(s, (g0.rep@.len() + 1) as u32),
        g1.cik@ == g0.cik@.push(c), g1.rep@.len() == g0.rep@.len() + 1, g1.sum@.len() == g0.sum@.len() + 1,
        pow2i(g1.bits as nat) + g1.rep@.len() < g1.nslots,
    ensures table_inv(g1),
{
    reveal(table_inv);
    let ng = g0.rep@.len() as int;
    lemma_occ_u32_update(g0.slots@, g0.nslots as int, s, (ng + 1) as u32);
    assert forall|t: int| 0 <= t < g1.nslots && #[trigger] g1.slots@[t] != 0 implies gslot_ok(g1, t) by {
        if t != s {
            assert(g1.slots@[t] == g0.slots@[t]);
            assert(gslot_ok(g0, t));
            let i = g0.slots@[t] as int - 1;
            assert(g1.cik@[i] == g0.cik@[i]);
            assert forall|u: int| home(cik_hash(g1.cik@[i]), g1.bits) <= u < t implies #[trigger] g1.slots@[u] != 0 by {
                if u != s {
                    assert(g1.slots@[u] == g0.slots@[u]);
                }
            }
        } else {
            assert(g1.slots@[t] as int - 1 == ng);
            assert(g1.cik@[ng] == c);
            assert forall|u: int| home(cik_hash(c), g1.bits) <= u < t implies #[trigger] g1.slots@[u] != 0 by {
                assert(g1.slots@[u] == g0.slots@[u]);
            }
        }
    }
    assert forall|i: int| 0 <= i < g1.rep@.len() implies #[trigger] gstored(g1, i) by {
        if i == ng {
            assert(g1.slots@[s] != 0 && g1.slots@[s] as int - 1 == i);
        } else {
            assert(gstored(g0, i));
            let t = choose|t: int| 0 <= t < g0.nslots && #[trigger] g0.slots@[t] != 0 && g0.slots@[t] as int - 1 == i;
            assert(t != s);
            assert(g1.slots@[t] == g0.slots@[t]);
        }
    }
}

// ------------------------------------------------------------------------------------------------ probe and build

/// The group of slot `t`.
pub open spec fn slot_group(g: &Groups, t: int) -> int {
    g.slots@[t] as int - 1
}

/// The key of group `i`.
pub open spec fn group_key(g: &Groups, kc: &KeyCols, i: int) -> Row {
    kc.okey(g.rep@[i] as int)
}

/// Every group's first sub row is a sub row, and its cik is that row's.
pub open spec fn groups_cols(g: &Groups, kc: &KeyCols) -> bool {
    &&& forall|i: int| 0 <= i < g.rep@.len() ==> #[trigger] g.rep@[i] < kc.n
    &&& forall|i: int| 0 <= i < g.rep@.len() ==> #[trigger] g.cik@[i] as int == kc.cik(g.rep@[i] as int)
}

/// Where the key `(x, c)` (the key of sub row `j`; `x` its name, `xn` bytes) is: its group, or none (then `s` is the
/// empty slot reached from the cik's home and `cik_seen` tells whether some group has cik `c`).
pub fn probe_group(g: &Groups, kc: &KeyCols, j: usize, x: &'static [u8], xn: usize, c: i32) -> (r: (usize, usize, bool))
    requires
        table_inv(g), kc.wf(), j < kc.n, c as int == kc.cik(j as int), x@ == kc.name(j as int), xn == x@.len(),
        groups_cols(g, kc),
    ensures
        r.0 != usize::MAX ==> r.0 < g.rep@.len() && group_key(g, kc, r.0 as int) == kc.okey(j as int),
        r.0 == usize::MAX ==> {
            &&& forall|i: int| 0 <= i < g.rep@.len() ==> #[trigger] group_key(g, kc, i) != kc.okey(j as int)
            &&& home(cik_hash(c), g.bits) <= r.1 < g.nslots && g.slots@[r.1 as int] == 0
            &&& forall|t: int| home(cik_hash(c), g.bits) <= t < r.1 ==> #[trigger] g.slots@[t] != 0
            &&& r.2 == exists|i: int| 0 <= i < g.rep@.len() && #[trigger] g.cik@[i] == c
        },
{
    proof {
        lemma_table_shape(g);
        reveal(KeyCols::wf);
    }
    let bits = g.bits;
    let h = ((c as u32) as u64 | 0x1_0000_0000u64).wrapping_mul(0x9E37_79B9_7F4A_7C15u64);
    proof {
        lemma_home_bound(h, bits);
    }
    let mut s = (h >> (64 - bits)) as usize;
    let ghost hm = s as int;
    let mut cik_seen = false;
    let nslots = g.nslots;
    while s < nslots
        invariant
            table_inv(g), kc.wf(), j < kc.n, c as int == kc.cik(j as int), x@ == kc.name(j as int), xn == x@.len(),
            groups_cols(g, kc),
            nslots == g.nslots, nslots == g.slots@.len(), g.cik@.len() == g.rep@.len(), bits == g.bits,
            hm == home(cik_hash(c), bits), hm <= s <= nslots,
            forall|t: int| hm <= t < s ==> #[trigger] g.slots@[t] != 0 && group_key(g, kc, slot_group(g, t)) != kc.okey(j as int),
            cik_seen ==> exists|t: int| hm <= t < s && #[trigger] g.cik@[slot_group(g, t)] == c,
            !cik_seen ==> forall|t: int| hm <= t < s ==> #[trigger] g.cik@[slot_group(g, t)] != c,
        decreases nslots - s,
    {
        let slot = g.slots[s];
        if slot == 0 {
            proof {
                lemma_probe_group_absent(g, kc, j, c, s as int, cik_seen);
            }
            return (usize::MAX, s, cik_seen);
        }
        proof {
            lemma_table_slot(g, s as int);
        }
        let i = (slot - 1) as usize;
        assert(slot_group(g, s as int) == i as int);
        if g.cik[i] == c {
            let rj = g.rep[i];
            proof {
                lemma_kc_row(kc, rj as int);
            }
            let ra = kc.name_off[rj] as usize;
            let rb = kc.name_off[rj + 1] as usize;
            if rb - ra == xn && eq_n(sub_bytes(kc.name_bytes, ra, rb), x, xn) {
                proof {
                    assert(kc.okey(rj as int) =~= kc.okey(j as int));
                }
                return (i, s, true);
            }
            proof {
                assert(kc.okey(rj as int)[0] != kc.okey(j as int)[0]);
            }
            cik_seen = true;
        } else {
            proof {
                assert(kc.okey(g.rep@[i as int] as int)[1] != kc.okey(j as int)[1]);
            }
        }
        s = s + 1;
    }
    proof {
        // Unreachable: the table has an empty slot after every home.
        lemma_occ_u32_range(g.slots@, nslots as int, hm, nslots as int);
    }
    (usize::MAX, s, cik_seen)
}

/// The probe met an empty slot: no group has the key, and `cik_seen` is whether some group has the cik.
proof fn lemma_probe_group_absent(g: &Groups, kc: &KeyCols, j: usize, c: i32, s: int, cik_seen: bool)
    requires
        table_inv(g), groups_cols(g, kc), c as int == kc.cik(j as int),
        home(cik_hash(c), g.bits) <= s < g.nslots, g.slots@[s] == 0,
        forall|t: int| home(cik_hash(c), g.bits) <= t < s ==> #[trigger] g.slots@[t] != 0 && group_key(g, kc, slot_group(g, t)) != kc.okey(j as int),
        cik_seen ==> exists|t: int| home(cik_hash(c), g.bits) <= t < s && #[trigger] g.cik@[slot_group(g, t)] == c,
        !cik_seen ==> forall|t: int| home(cik_hash(c), g.bits) <= t < s ==> #[trigger] g.cik@[slot_group(g, t)] != c,
    ensures
        forall|i: int| 0 <= i < g.rep@.len() ==> #[trigger] group_key(g, kc, i) != kc.okey(j as int),
        cik_seen == exists|i: int| 0 <= i < g.rep@.len() && #[trigger] g.cik@[i] == c,
{
    let hm = home(cik_hash(c), g.bits);
    lemma_table_absent(g, c, s);
    assert forall|i: int| 0 <= i < g.rep@.len() implies #[trigger] group_key(g, kc, i) != kc.okey(j as int) by {
        if group_key(g, kc, i) == kc.okey(j as int) {
            assert(group_key(g, kc, i)[1] == kc.okey(j as int)[1]);
            assert(g.cik@[i] == c);
            let t = choose|t: int| hm <= t < s && #[trigger] g.slots@[t] as int - 1 == i;
            assert(slot_group(g, t) == i);
        }
    }
    if exists|i: int| 0 <= i < g.rep@.len() && #[trigger] g.cik@[i] == c {
        let i = choose|i: int| 0 <= i < g.rep@.len() && #[trigger] g.cik@[i] == c;
        let t = choose|t: int| hm <= t < s && #[trigger] g.slots@[t] as int - 1 == i;
        assert(slot_group(g, t) == i);
        assert(g.cik@[slot_group(g, t)] == c);
    }
    if cik_seen {
        let t = choose|t: int| hm <= t < s && #[trigger] g.cik@[slot_group(g, t)] == c;
        lemma_table_slot(g, t);
        assert(0 <= slot_group(g, t) < g.rep@.len());
    }
}

/// A cik among the groups' keys of the ranks below `m` is one of their distinct ciks, and back.
pub proof fn lemma_cik_in_groups(g: &Groups, kc: &KeyCols, qr: Seq<usize>, tot: Seq<Wide>, seen: Seq<bool>, m: int, c: i32)
    requires groups_ok(g, kc, qr, tot, seen, m), groups_cols(g, kc), 0 <= m <= qr.len(), m <= seen.len(),
    ensures
        dciks(kc, qr, seen, m).contains(c as int) == exists|i: int| 0 <= i < g.rep@.len() && #[trigger] g.cik@[i] == c,
{
    reveal(groups_ok);
    lemma_gks(kc, qr, seen, m);
    lemma_dciks(kc, qr, seen, m);
    let ks = gks(kc, qr, seen, m);
    if dciks(kc, qr, seen, m).contains(c as int) {
        let id = choose|id: int| 0 <= id < m && seen[id] && #[trigger] kc.cik(qr[id] as int) == c as int;
        let k = kc.okey(qr[id] as int);
        assert(ks.contains(k));
        let i = choose|i: int| 0 <= i < ks.len() && ks[i] == k;
        assert(kc.okey(g.rep@[i] as int) == k);
        assert(kc.okey(g.rep@[i] as int)[1] == k[1]);
        assert(g.cik@[i] == c);
    }
    if exists|i: int| 0 <= i < g.rep@.len() && #[trigger] g.cik@[i] == c {
        let i = choose|i: int| 0 <= i < g.rep@.len() && #[trigger] g.cik@[i] == c;
        assert(ks.contains(ks[i]));
        let id = choose|id: int| 0 <= id < m && seen[id] && #[trigger] kc.okey(qr[id] as int) == ks[i];
        assert(kc.okey(g.rep@[i] as int) == ks[i]);
        assert(kc.okey(qr[id] as int)[1] == ks[i][1]);
        assert(kc.cik(qr[id] as int) == c as int);
    }
}

/// The groups of every rank.
pub fn build_groups(kc: &KeyCols, qr: &Vec<usize>, tot: &Vec<Wide>, seen: &Vec<bool>, bits: u64) -> (g: Groups)
    requires
        kc.wf(), ranks_wf(kc, qr@, tot@, seen@), qr@.len() < 0xffff_fff0,
        1 <= bits <= 30, pow2i(bits as nat) + qr@.len() + 1 < usize::MAX,
    ensures
        groups_ok(&g, kc, qr@, tot@, seen@, qr@.len() as int),
        groups_cols(&g, kc),
        g.sum@.len() == g.rep@.len(),
{
    let nq = qr.len();
    proof {
        vstd::bits::lemma_usize_pow2_no_overflow(bits as nat);
        vstd::bits::lemma_usize_shl_is_mul(1, bits as usize);
    }
    let nslots = (1usize << (bits as usize)) + nq + 1;
    let mut g = Groups {
        bits,
        nslots,
        slots: vec![0u32; nslots],
        cik: Vec::new(),
        rep: Vec::new(),
        sum: Vec::new(),
        ncik: 0,
        total: wide_zero(),
    };
    proof {
        assert forall|s: int| 0 <= s < g.slots@.len() implies #[trigger] g.slots@[s] == 0 by {
            assert(cloned(0u32, g.slots@[s]));
        }
        lemma_table_init(&g);
        assert(gks(kc, qr@, seen@, 0) =~= Seq::<Row>::empty());
        reveal(groups_ok);
    }
    let mut id: usize = 0;
    while id < nq
        invariant
            kc.wf(), ranks_wf(kc, qr@, tot@, seen@), nq == qr@.len(), id <= nq, nq < 0xffff_fff0,
            1 <= bits <= 30, g.bits == bits, g.nslots == nslots, nslots == pow2i(bits as nat) + nq + 1,
            table_inv(&g), groups_cols(&g, kc), g.ncik <= g.rep@.len(),
            groups_ok(&g, kc, qr@, tot@, seen@, id as int),
        decreases nq - id,
    {
        let ghost g0 = g;
        let ghost ks = gks(kc, qr@, seen@, id as int);
        proof {
            lemma_table_shape(&g);
            lemma_gks(kc, qr@, seen@, id as int);
            lemma_sums_in_range(kc, qr@, tot@, seen@, Seq::empty(), id as int);
            lemma_groups_facts(&g, kc, qr@, tot@, seen@, id as int);
        }
        if seen[id] {
            let j = qr[id];
            proof {
                lemma_kc_row(kc, j as int);
            }
            let c = kc.cik[j];
            let a = kc.name_off[j] as usize;
            let b = kc.name_off[j + 1] as usize;
            let x = sub_bytes(kc.name_bytes, a, b);
            let ghost k = kc.okey(j as int);
            let (found, s, cik_seen) = probe_group(&g, kc, j, x, b - a, c);
            if found != usize::MAX {
                proof {
                    lemma_sums_in_range(kc, qr@, tot@, seen@, ks[found as int], id as int);
                    assert(ks[found as int] == k);
                    assert(ks.contains(k));
                    lemma_cik_in_groups(&g0, kc, qr@, tot@, seen@, id as int, c);
                    assert(g0.cik@[found as int] == c);
                }
                add_to_group(&mut g, found, tot[id]);
                proof {
                    lemma_found_step(&g0, &g, kc, qr@, tot@, seen@, id as int, found as int);
                }
            } else {
                proof {
                    lemma_cik_in_groups(&g0, kc, qr@, tot@, seen@, id as int, c);
                    assert(!ks.contains(k)) by {
                        if ks.contains(k) {
                            let i = choose|i: int| 0 <= i < ks.len() && ks[i] == k;
                            assert(group_key(&g0, kc, i) == k);
                        }
                    }
                    assert(g.rep@.len() < nq);
                }
                new_group(&mut g, s, j, c, tot[id], !cik_seen);
                proof {
                    lemma_new_step(&g0, &g, kc, qr@, tot@, seen@, id as int, cik_seen);
                }
            }
        } else {
            proof {
                lemma_skip_step(&g, kc, qr@, tot@, seen@, id as int);
            }
        }
        id = id + 1;
    }
    proof {
        lemma_table_shape(&g);
    }
    g
}

/// Add `w` to group `i` and to the total.
fn add_to_group(g: &mut Groups, i: usize, w: Wide)
    requires
        table_inv(old(g)), i < old(g).rep@.len(),
        -wide_limit() <= wval(old(g).sum@[i as int]) <= wide_limit(), -wide_limit() <= wval(w) <= wide_limit(),
        -wide_limit() <= wval(old(g).total) <= wide_limit(),
    ensures
        table_inv(final(g)),
        final(g).rep@ == old(g).rep@, final(g).cik@ == old(g).cik@, final(g).ncik == old(g).ncik,
        final(g).bits == old(g).bits, final(g).nslots == old(g).nslots, final(g).slots@ == old(g).slots@,
        final(g).sum@ == old(g).sum@.update(i as int, final(g).sum@[i as int]),
        wval(final(g).sum@[i as int]) == wval(old(g).sum@[i as int]) + wval(w),
        wval(final(g).total) == wval(old(g).total) + wval(w),
{
    proof {
        lemma_table_shape(g);
    }
    let x = wide_add(g.sum[i], w);
    g.sum.set(i, x);
    g.total = wide_add(g.total, w);
    proof {
        reveal(table_inv);
        assert forall|s: int| 0 <= s < g.nslots && #[trigger] g.slots@[s] != 0 implies gslot_ok(g, s) by {
            assert(gslot_ok(old(g), s));
        }
        assert forall|i2: int| 0 <= i2 < g.rep@.len() implies #[trigger] gstored(g, i2) by {
            assert(gstored(old(g), i2));
        }
    }
}

/// A new group of sub row `j` (cik `c`) with sum `w`, at the empty slot `s` reached from the cik's home.
fn new_group(g: &mut Groups, s: usize, j: usize, c: i32, w: Wide, cik_new: bool)
    requires
        table_inv(old(g)),
        home(cik_hash(c), old(g).bits) <= s < old(g).nslots, old(g).slots@[s as int] == 0,
        forall|t: int| home(cik_hash(c), old(g).bits) <= t < s ==> #[trigger] old(g).slots@[t] != 0,
        old(g).rep@.len() + 1 < 0xffff_ffff,
        pow2i(old(g).bits as nat) + old(g).rep@.len() + 1 < old(g).nslots,
        old(g).ncik < usize::MAX,
        -wide_limit() <= wval(w) <= wide_limit(), -wide_limit() <= wval(old(g).total) <= wide_limit(),
    ensures
        table_inv(final(g)),
        final(g).rep@ == old(g).rep@.push(j), final(g).cik@ == old(g).cik@.push(c),
        final(g).ncik as int == if cik_new { old(g).ncik as int + 1 } else { old(g).ncik as int },
        final(g).bits == old(g).bits, final(g).nslots == old(g).nslots,
        final(g).sum@.len() == old(g).sum@.len() + 1,
        forall|i: int| 0 <= i < old(g).sum@.len() ==> #[trigger] final(g).sum@[i] == old(g).sum@[i],
        wval(final(g).sum@[old(g).sum@.len() as int]) == wval(w),
        wval(final(g).total) == wval(old(g).total) + wval(w),
{
    let ghost g0 = *old(g);
    proof {
        lemma_table_shape(g);
    }
    let ng = g.rep.len();
    if cik_new {
        g.ncik = g.ncik + 1;
    }
    g.rep.push(j);
    g.cik.push(c);
    g.sum.push(w);
    g.slots.set(s, (ng + 1) as u32);
    g.total = wide_add(g.total, w);
    proof {
        lemma_table_insert(&g0, g, s as int, c);
    }
}

/// What the loop reads of `groups_ok`.
pub proof fn lemma_groups_facts(g: &Groups, kc: &KeyCols, qr: Seq<usize>, tot: Seq<Wide>, seen: Seq<bool>, m: int)
    requires groups_ok(g, kc, qr, tot, seen, m),
    ensures
        g.rep@.len() == gks(kc, qr, seen, m).len(), g.rep@.len() <= m,
        forall|i: int| 0 <= i < g.rep@.len() ==> #[trigger] group_key(g, kc, i) == gks(kc, qr, seen, m)[i],
        forall|i: int| 0 <= i < g.rep@.len() ==> #[trigger] wval(g.sum@[i]) == psum(kc, qr, tot, seen, gks(kc, qr, seen, m)[i], m),
        g.ncik == dciks(kc, qr, seen, m).len(),
        wval(g.total) == tsum(qr, tot, seen, m),
{
    reveal(groups_ok);
}

/// A rank without rows changes nothing.
pub proof fn lemma_skip_step(g: &Groups, kc: &KeyCols, qr: Seq<usize>, tot: Seq<Wide>, seen: Seq<bool>, m: int)
    requires groups_ok(g, kc, qr, tot, seen, m), 0 <= m < qr.len(), seen.len() == qr.len(), !seen[m],
    ensures groups_ok(g, kc, qr, tot, seen, m + 1),
{
    reveal(groups_ok);
    let ks = gks(kc, qr, seen, m);
    assert(gks(kc, qr, seen, m + 1) == ks);
    assert(dciks(kc, qr, seen, m + 1) == dciks(kc, qr, seen, m));
    assert forall|i: int| 0 <= i < ks.len() implies #[trigger] wval(g.sum@[i]) == psum(kc, qr, tot, seen, ks[i], m + 1) by {}
}

/// A rank (with rows) whose key has group `found`: that group's sum grows by the rank's total.
pub proof fn lemma_found_step(g0: &Groups, g1: &Groups, kc: &KeyCols, qr: Seq<usize>, tot: Seq<Wide>, seen: Seq<bool>, m: int,
    found: int)
    requires
        groups_ok(g0, kc, qr, tot, seen, m), groups_cols(g0, kc), 0 <= m < qr.len(), ranks_wf(kc, qr, tot, seen),
        seen[m], 0 <= found < g0.rep@.len(), gks(kc, qr, seen, m)[found] == kc.okey(qr[m] as int),
        dciks(kc, qr, seen, m).contains(kc.cik(qr[m] as int)),
        g1.rep@ == g0.rep@, g1.cik@ == g0.cik@, g1.ncik == g0.ncik,
        g1.sum@ == g0.sum@.update(found, g1.sum@[found]),
        wval(g1.sum@[found]) == wval(g0.sum@[found]) + wval(tot[m]),
        wval(g1.total) == wval(g0.total) + wval(tot[m]),
    ensures groups_ok(g1, kc, qr, tot, seen, m + 1), groups_cols(g1, kc),
{
    reveal(groups_ok);
    let ks = gks(kc, qr, seen, m);
    let k = kc.okey(qr[m] as int);
    lemma_gks(kc, qr, seen, m);
    assert(ks.contains(k));
    assert(gks(kc, qr, seen, m + 1) == ks);
    assert(dciks(kc, qr, seen, m + 1) == dciks(kc, qr, seen, m));
    assert forall|i: int| 0 <= i < ks.len() implies #[trigger] wval(g1.sum@[i]) == psum(kc, qr, tot, seen, ks[i], m + 1) by {
        if i != found {
            assert(ks[i] != ks[found]);
            assert(g1.sum@[i] == g0.sum@[i]);
        }
    }
}

/// A rank (with rows) with a new key: a new group with the rank's total; one more distinct cik when it is new.
pub proof fn lemma_new_step(g0: &Groups, g1: &Groups, kc: &KeyCols, qr: Seq<usize>, tot: Seq<Wide>, seen: Seq<bool>, m: int,
    cik_seen: bool)
    requires
        groups_ok(g0, kc, qr, tot, seen, m), groups_cols(g0, kc), 0 <= m < qr.len(), ranks_wf(kc, qr, tot, seen),
        seen[m], !gks(kc, qr, seen, m).contains(kc.okey(qr[m] as int)),
        dciks(kc, qr, seen, m).contains(kc.cik(qr[m] as int)) == cik_seen,
        g0.sum@.len() == g0.rep@.len(), g0.cik@.len() == g0.rep@.len(),
        g1.rep@ == g0.rep@.push(qr[m]), g1.cik@ == g0.cik@.push(kc.cik@[qr[m] as int]),
        g1.ncik as int == if cik_seen { g0.ncik as int } else { g0.ncik as int + 1 },
        g1.sum@.len() == g0.sum@.len() + 1,
        forall|i: int| 0 <= i < g0.sum@.len() ==> #[trigger] g1.sum@[i] == g0.sum@[i],
        wval(g1.sum@[g0.sum@.len() as int]) == wval(tot[m]),
        wval(g1.total) == wval(g0.total) + wval(tot[m]),
    ensures groups_ok(g1, kc, qr, tot, seen, m + 1), groups_cols(g1, kc),
{
    reveal(groups_ok);
    let ks = gks(kc, qr, seen, m);
    let k = kc.okey(qr[m] as int);
    lemma_gks(kc, qr, seen, m);
    assert(gks(kc, qr, seen, m + 1) == ks.push(k));
    let ng = ks.len() as int;
    assert(g0.sum@.len() == ng);
    lemma_psum_absent(kc, qr, tot, seen, k, m);
    assert forall|i: int| 0 <= i < ng + 1 implies #[trigger] wval(g1.sum@[i]) == psum(kc, qr, tot, seen, ks.push(k)[i], m + 1) by {
        if i < ng {
            assert(ks.push(k)[i] == ks[i]);
            assert(ks[i] != k);
        } else {
            assert(ks.push(k)[i] == k);
        }
    }
    assert forall|i: int| 0 <= i < ng + 1 implies kc.okey(#[trigger] g1.rep@[i] as int) == ks.push(k)[i] by {
        if i < ng {
            assert(g1.rep@[i] == g0.rep@[i]);
        }
    }
    assert forall|i: int| 0 <= i < ng + 1 implies #[trigger] g1.cik@[i] as int == kc.cik(g1.rep@[i] as int) by {
        if i < ng {
            assert(g1.rep@[i] == g0.rep@[i] && g1.cik@[i] == g0.cik@[i]);
        }
    }
    assert forall|i: int| 0 <= i < ng + 1 implies #[trigger] g1.rep@[i] < kc.n by {
        if i < ng {
            assert(g1.rep@[i] == g0.rep@[i]);
        }
    }
}

} // verus!
