//! The qualifying-row bitmap of partsupp, built from the ps_suppkey index of storage `ps_suppidx` (a dense directory
//! over the supplier keys whose entry `e` lists exactly the partsupp rows with ps_suppkey `kmin + e`, `six::directory_ok`).
//!
//! `row_bitmap` visits the flag of every supplier key (`supp::flags_ok`) and, for each qualifying key, sets the bits
//! of the rows its directory entry lists: bit `r % 64` of word `r / 64` is set exactly when row `r` qualifies
//! (`bm_ok`). One thread does about 40K directory lookups and 3.2M bit sets per nation instead of a flag lookup for
//! each of the 80M rows; the scan then reads its chunk masks from the bitmap (`scan::chunk_mask_bm`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::gendb_entry::stored::StoredParts;
use crate::stores::ps_suppidx::interface as six;
use super::tables::Tabs;
use super::nf::*;
use super::rows::*;
use super::supp::flags_ok;
use super::common::lowbit::bit_at;

verus! {

/// Bit `r` of a row bitmap: bit `r % 64` of word `r / 64`.
pub open spec fn bm_bit(bm: Seq<u64>, r: int) -> bool {
    bit_at(bm[r / 64], r % 64)
}

/// The bitmap flags exactly the qualifying partsupp rows `0 .. n` (`n / 64 + 1` words).
pub open spec fn bm_ok(bm: Seq<u64>, n: int, t: Tabs, name: Seq<u8>) -> bool {
    &&& bm.len() == n / 64 + 1
    &&& forall|r: int| 0 <= r < n ==> #[trigger] bm_bit(bm, r) == rowq(t, name, r)
}

/// The relation the index describes: the ps_suppkey column of partsupp (one-column rows, canonical order).
pub open spec fn supp_rel(t: Tabs) -> Seq<Row> {
    Seq::new(t.ps.len(), |r: int| seq![t.ps[r][1]])
}

/// Handles of the index in dense directory mode (`ok`; otherwise unused).
#[derive(Clone, Copy)]
pub struct SuppIdx {
    pub ok: bool,
    pub kmin: i64,
    pub offs: &'static [u32],
    pub perm: &'static [u32],
}

pub open spec fn idx_ok(ix: SuppIdx, t: Tabs) -> bool {
    ix.ok ==> ix.offs@.len() >= 1 && six::directory_ok(ix.kmin as int, ix.offs@.len() - 1, ix.offs@, ix.perm@, supp_rel(t))
}

/// Opens the index parts (directory mode only).
pub fn open_index(sp: &mut StoredParts, Ghost(t): Ghost<Tabs>) -> (ix: SuppIdx)
    requires
        exists|rels: Seq<Seq<Row>>| #[trigger] six::represents(old(sp)@, rels) && rels[0] == supp_rel(t),
    ensures
        final(sp)@ == old(sp)@,
        idx_ok(ix, t),
{
    let ghost rels = choose|rels: Seq<Seq<Row>>| #[trigger] six::represents(sp@, rels) && rels[0] == supp_rel(t);
    let meta = sp.extent_i64(six::META, 0, 2);
    proof { assert(meta@ =~= six::idx_i64s(sp@[six::META as int])); }
    if meta[0] != six::MODE_DIRECTORY {
        let none = sp.extent_u32(six::OFFS, 0, 0);
        return SuppIdx { ok: false, kmin: 0, offs: none, perm: none };
    }
    let lo = sp.part_len(six::OFFS);
    let lp = sp.part_len(six::PERM);
    let offs = sp.extent_u32(six::OFFS, 0, lo);
    let perm = sp.extent_u32(six::PERM, 0, lp);
    proof {
        assert(offs@ =~= six::idx_u32s(sp@[six::OFFS as int]));
        assert(perm@ =~= six::idx_u32s(sp@[six::PERM as int]));
    }
    SuppIdx { ok: true, kmin: meta[1], offs, perm }
}

/// Directory offsets are nondecreasing over any span.
proof fn lemma_offs_mono(offs: Seq<u32>, k: int, a: int, b: int)
    requires
        offs.len() == k + 1,
        forall|e: int| 0 <= e < k ==> #[trigger] offs[e] <= offs[e + 1],
        0 <= a <= b <= k,
    ensures offs[a] <= offs[b],
    decreases b - a,
{
    if a < b {
        lemma_offs_mono(offs, k, a + 1, b);
        assert(offs[a] <= offs[a + 1]);
    }
}

/// Setting bit `s` of a word sets it and keeps every other bit.
proof fn lemma_set_bit(m: u64, s: u64, i: u64)
    requires s < 64, i < 64,
    ensures
        i == s ==> ((m | (1u64 << s)) >> i) & 1u64 == 1u64,
        i != s ==> ((m | (1u64 << s)) >> i) & 1u64 == (m >> i) & 1u64,
{
    assert(i == s ==> ((m | (1u64 << s)) >> i) & 1u64 == 1u64) by (bit_vector) requires s < 64, i < 64;
    assert(i != s ==> ((m | (1u64 << s)) >> i) & 1u64 == (m >> i) & 1u64) by (bit_vector) requires s < 64, i < 64;
}

/// No bit of zero is set.
proof fn lemma_zero_bit(i: u64)
    requires i < 64,
    ensures (0u64 >> i) & 1u64 == 0u64,
{
    assert((0u64 >> i) & 1u64 == 0u64) by (bit_vector);
}

/// The ps_suppkey of row `r` (an integer under the index: `key_in_range`).
pub open spec fn skey(t: Tabs, r: int) -> int {
    t.ps[r][1]->Int_0
}

/// Row `r` sits at some position `j0 .. j` of the permutation.
pub open spec fn seen(perm: Seq<u32>, j0: int, j: int, r: int) -> bool {
    exists|jj: int| j0 <= jj < j && perm[jj] == r
}

/// The bitmap after the supplier keys below `lim`: exactly the qualifying rows whose key is below `lim`.
pub open spec fn bm_inv(bm: Seq<u64>, n: int, t: Tabs, name: Seq<u8>, lim: int) -> bool {
    &&& bm.len() == n / 64 + 1
    &&& forall|r: int| 0 <= r < n ==> #[trigger] bm_bit(bm, r) == (rowq(t, name, r) && skey(t, r) < lim)
}

/// Under the directory, every row's key is an integer of the directory's range.
proof fn lemma_row_key(ix: SuppIdx, t: Tabs, r: int)
    requires ix.ok, idx_ok(ix, t), 0 <= r < t.ps.len(),
    ensures
        t.ps[r][1] == Val::Int(skey(t, r)),
        ix.kmin <= skey(t, r) < ix.kmin + ix.offs@.len() - 1,
{
    let rel = supp_rel(t);
    assert(rel[r] == seq![t.ps[r][1]]);
    assert(six::key_in_range(rel, ix.kmin as int, ix.offs@.len() - 1, r));
}

/// The rows listed by directory entry `e` are exactly the rows whose key is `kmin + e`.
proof fn lemma_entry_rows(ix: SuppIdx, t: Tabs, e: int, r: int)
    requires ix.ok, idx_ok(ix, t), 0 <= e < ix.offs@.len() - 1, 0 <= r < t.ps.len(),
    ensures
        t.ps[r][1] == Val::Int(skey(t, r)),
        seen(ix.perm@, ix.offs@[e] as int, ix.offs@[e + 1] as int, r) == (skey(t, r) == ix.kmin + e),
{
    let rel = supp_rel(t);
    let k = ix.offs@.len() - 1;
    lemma_row_key(ix, t, r);
    if seen(ix.perm@, ix.offs@[e] as int, ix.offs@[e + 1] as int, r) {
        let jj = choose|jj: int| ix.offs@[e] <= jj < ix.offs@[e + 1] && ix.perm@[jj] == r;
        assert(six::in_entry(ix.offs@, e, jj));
        assert(rel[r] == seq![t.ps[r][1]]);
    }
    if skey(t, r) == ix.kmin + e {
        assert(six::listed(ix.perm@, r));
        let j = choose|j: int| 0 <= j < ix.perm@.len() && ix.perm@[j] == r;
        let e2 = six::lemma_find_entry(ix.offs@, k, j);
        assert(rel[ix.perm@[j] as int][0] == Val::Int(ix.kmin + e2));
        assert(rel[r] == seq![t.ps[r][1]]);
        assert(e2 == e);
        assert(ix.offs@[e] <= j < ix.offs@[e + 1]);
    }
}

/// Sets the bits of the rows `perm[j0 .. j1]` (directory entry `e`, key `v = kmin + e`, which qualifies).
fn mark_entry(bm: &mut Vec<u64>, ix: &SuppIdx, e: usize, Ghost(v): Ghost<int>, n: usize, Ghost(t): Ghost<Tabs>,
    Ghost(name): Ghost<Seq<u8>>)
    requires
        ix.ok, idx_ok(*ix, t), t.ps.len() == n,
        e + 1 < ix.offs@.len(), v == ix.kmin + e,
        sq(t, name, Val::Int(v)),
        bm_inv(old(bm)@, n as int, t, name, v),
    ensures
        bm_inv(final(bm)@, n as int, t, name, v + 1),
{
    let ghost k = ix.offs@.len() - 1;
    let ghost rel = supp_rel(t);
    let j0 = ix.offs[e] as usize;
    let j1 = ix.offs[e + 1] as usize;
    proof {
        lemma_offs_mono(ix.offs@, k, e as int + 1, k);
    }
    let mut j = j0;
    while j < j1
        invariant
            ix.ok, idx_ok(*ix, t), t.ps.len() == n, rel == supp_rel(t), k == ix.offs@.len() - 1,
            e + 1 < ix.offs@.len(), v == ix.kmin + e,
            j0 == ix.offs@[e as int], j1 == ix.offs@[e + 1], j0 <= j <= j1, j1 <= n,
            bm@.len() == n / 64 + 1,
            forall|r: int| 0 <= r < n ==> #[trigger] bm_bit(bm@, r)
                == ((rowq(t, name, r) && skey(t, r) < v) || seen(ix.perm@, j0 as int, j as int, r)),
        decreases j1 - j,
    {
        assert(six::in_entry(ix.offs@, e as int, j as int));
        let r = ix.perm[j] as usize;
        let q = r / 64;
        let s = (r % 64) as u64;
        let w = bm[q];
        let ghost b0 = bm@;
        crate::gendb_entry::work::put(bm, q, w | (1u64 << s));
        proof {
            assert forall|x: int| 0 <= x < n implies #[trigger] bm_bit(bm@, x)
                == ((rowq(t, name, x) && skey(t, x) < v) || seen(ix.perm@, j0 as int, j + 1, x)) by {
                assert(bm_bit(b0, x) == ((rowq(t, name, x) && skey(t, x) < v) || seen(ix.perm@, j0 as int, j as int, x)));
                if x == r {
                    lemma_set_bit(w, s, s);
                    assert(ix.perm@[j as int] == x);
                } else {
                    if x / 64 == q {
                        lemma_set_bit(w, s, (x % 64) as u64);
                    } else {
                        assert(bm@[x / 64] == b0[x / 64]);
                    }
                    if seen(ix.perm@, j0 as int, j + 1, x) {
                        let jj = choose|jj: int| j0 <= jj < j + 1 && ix.perm@[jj] == x;
                        assert(jj != j);
                    }
                }
            }
        }
        j = j + 1;
    }
    proof {
        assert forall|x: int| 0 <= x < n implies #[trigger] bm_bit(bm@, x) == (rowq(t, name, x) && skey(t, x) < v + 1) by {
            lemma_entry_rows(*ix, t, e as int, x);
        }
    }
}

/// The qualifying-row bitmap of the `n` partsupp rows: for every flagged supplier key in the directory, mark the
/// rows of its entry.
pub fn row_bitmap(ix: &SuppIdx, fl: &Vec<u8>, smin: i64, range: usize, n: usize, Ghost(t): Ghost<Tabs>,
    Ghost(name): Ghost<Seq<u8>>) -> (bm: Vec<u64>)
    requires
        ix.ok, idx_ok(*ix, t), t.ps.len() == n,
        flags_ok(t, name, fl@, smin as int, range as int),
    ensures
        bm_ok(bm@, n as int, t, name),
{
    let nw = n / 64 + 1;
    let mut bm: Vec<u64> = vec![0u64; nw];
    let ghost k = ix.offs@.len() - 1;
    let nk = ix.offs.len() - 1;
    proof {
        assert forall|r: int| 0 <= r < n implies #[trigger] bm_bit(bm@, r) == (rowq(t, name, r) && skey(t, r) < smin) by {
            lemma_zero_bit((r % 64) as u64);
            if rowq(t, name, r) {
                lemma_row_key(*ix, t, r);
                assert(sq(t, name, Val::Int(skey(t, r))));
            }
        }
    }
    let mut i: usize = 0;
    while i < range
        invariant
            ix.ok, idx_ok(*ix, t), t.ps.len() == n, k == ix.offs@.len() - 1, nk == k,
            flags_ok(t, name, fl@, smin as int, range as int),
            i <= range,
            bm_inv(bm@, n as int, t, name, smin + i),
        decreases range - i,
    {
        let ghost v = smin + i;
        if fl[i] != 0 {
            let e: i128 = smin as i128 + i as i128 - ix.kmin as i128;
            if 0 <= e && e < nk as i128 {
                mark_entry(&mut bm, ix, e as usize, Ghost(v), n, Ghost(t), Ghost(name));
            } else {
                // No row has a key outside the directory's range.
                proof {
                    assert forall|r: int| 0 <= r < n implies #[trigger] bm_bit(bm@, r) == (rowq(t, name, r) && skey(t, r) < v + 1) by {
                        lemma_row_key(*ix, t, r);
                    }
                }
            }
        } else {
            // The key does not qualify.
            proof {
                assert(!sq(t, name, Val::Int(v)));
                assert forall|r: int| 0 <= r < n implies #[trigger] bm_bit(bm@, r) == (rowq(t, name, r) && skey(t, r) < v + 1) by {
                    lemma_row_key(*ix, t, r);
                }
            }
        }
        i = i + 1;
    }
    proof {
        assert forall|r: int| 0 <= r < n implies #[trigger] bm_bit(bm@, r) == rowq(t, name, r) by {
            lemma_row_key(*ix, t, r);
            if rowq(t, name, r) {
                assert(sq(t, name, Val::Int(skey(t, r))));
            }
        }
    }
    bm
}

} // verus!
