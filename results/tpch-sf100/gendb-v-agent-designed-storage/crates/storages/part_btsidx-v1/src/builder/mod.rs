//! Builder of storage `part_btsidx`: the 50 parts of `custpart` are inherited unchanged; this builder adds a composite
//! index of part on `(p_brand, p_type, p_size)`.
//!
//! Plan (when the rows fit U32 positions and the key space `nb * nt * ns` is at most `MAX_KEYS`):
//! 1. `size_range`: the smallest and largest p_size (`smin`, `ns = smax - smin + 1`);
//! 2. `pack_rows`: each row `r` packed as `comp(r) * 2^32 + r` with `comp(r) = (brand * nt + type) * ns +
//!    (size - smin)`;
//! 3. `sort64::msort64` sorts the packed values (so by composite key);
//! 4. `unpack`: the index rows (`perm`) and their keys; `build_dir`: entry `e` starts at the first position whose
//!    key is at least `e`;
//! 5. `check_perm`: the rows are a bijection (checked at run time).
//! Otherwise the index is absent (mode 0).
//!
//! Proof: every packed value satisfies `good` (row in range, key = the row's composite key below `nk`); the sort
//! keeps that for each element and makes the keys nondecreasing, so the directory scan puts every position in the
//! entry of its row's key (`dir_ok`).
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::layout::{PartView, owned_parts_view};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::gendb_entry::storage::{represents, stored_relations};
use crate::spec::value::{Database, Row};
use crate::stores::part_btsidx::interface::*;
use crate::stores::part_btsidx::declaration as D;

pub mod src;
pub mod sort64;
pub mod perm;
use src::*;
use sort64::*;
use perm::{check_perm, perm_view_ok, covered_u32};

verus! {

/// Largest number of directory entries the builder accepts.
pub const MAX_KEYS: u64 = 0x400_0000;

/// `2^32`: packed values are `key * 2^32 + row`.
pub open spec fn p32() -> int {
    0x1_0000_0000
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

/// The composite key of row `r` for `nt` types and the size range `smin .. smin + ns`.
pub open spec fn compk(cp: Seq<PartView>, nc: int, ns: int, smin: int, r: int) -> int {
    (bi_at(cp, r) * nc + ti_at(cp, r)) * ns + (size_at(cp, r) - smin)
}

/// The composite key of in-range indices is below `nb * nc * ns`.
proof fn lemma_comp_bound(b: int, c: int, t: int, nb: int, nc: int, ns: int)
    requires 0 <= b < nb, 0 <= c < nc, 0 <= t < ns,
    ensures 0 <= (b * nc + c) * ns + t < nb * nc * ns, 0 <= b * nc + c < nb * nc,
{
    assert(b * nc + c < nb * nc) by (nonlinear_arith) requires 0 <= b < nb, 0 <= c < nc;
    assert(0 <= b * nc) by (nonlinear_arith) requires 0 <= b, 0 <= nc;
    let g = b * nc + c;
    assert(g * ns + t < (nb * nc) * ns) by (nonlinear_arith) requires 0 <= g < nb * nc, 0 <= t < ns;
    assert(0 <= g * ns) by (nonlinear_arith) requires 0 <= g, 0 <= ns;
    assert((nb * nc) * ns == nb * nc * ns) by (nonlinear_arith);
}

/// Packed value `x`: a row below `n` and its composite key below `nk`.
#[verifier::opaque]
pub open spec fn good(cp: Seq<PartView>, n: int, nc: int, ns: int, smin: int, nk: int, x: u64) -> bool {
    let r = x as int % p32();
    let k = x as int / p32();
    &&& r < n
    &&& k < nk
    &&& k == compk(cp, nc, ns, smin, r)
}

/// The smallest and largest p_size of the `n >= 1` rows.
fn size_range(zc: &[u8], zb: &[i64], bs: usize, n: usize, Ghost(cp): Ghost<Seq<PartView>>) -> (r: (i64, i64))
    requires
        base_ok(cp, n as int), n >= 1,
        bs as int == bsize(cp),
        zc@ == u8s(cp[PA_SIZE_CODES as int]),
        zb@ == i64s(cp[PA_SIZE_BASE as int]),
    ensures
        forall|s: int| 0 <= s < n ==> r.0 <= #[trigger] size_at(cp, s) <= r.1,
        r.0 <= r.1,
{
    proof {
        lemma_div_lt(0, bs as int, zb@.len() as int);
        assert(i64::MIN <= size_at(cp, 0) <= i64::MAX);
    }
    let d0 = zb[0] + zc[0] as i64;
    let mut lo = d0;
    let mut hi = d0;
    let mut s: usize = 1;
    while s < n
        invariant
            base_ok(cp, n as int), n >= 1, bs as int == bsize(cp),
            zc@ == u8s(cp[PA_SIZE_CODES as int]), zb@ == i64s(cp[PA_SIZE_BASE as int]),
            1 <= s <= n,
            lo <= hi,
            forall|t: int| 0 <= t < s ==> lo <= #[trigger] size_at(cp, t) <= hi,
        decreases n - s,
    {
        proof {
            lemma_div_lt(s as int, bs as int, zb@.len() as int);
            assert(i64::MIN <= size_at(cp, s as int) <= i64::MAX);
        }
        let d = zb[s / bs] + zc[s] as i64;
        if d < lo { lo = d; }
        if d > hi { hi = d; }
        s = s + 1;
    }
    (lo, hi)
}

/// The slices of the packing step and the facts they carry.
pub open spec fn pack_src(cp: Seq<PartView>, rel: Seq<Row>, n: int, bs: int, zc: Seq<u8>, zb: Seq<i64>, bc: Seq<u8>,
    bb: Seq<u64>, oc: Seq<u8>, ob: Seq<u64>) -> bool
{
    &&& src_ok(cp, rel)
    &&& rel.len() == n
    &&& bs == bsize(cp)
    &&& zc == u8s(cp[PA_SIZE_CODES as int]) && zb == i64s(cp[PA_SIZE_BASE as int])
    &&& bc == u8s(cp[PA_BRAND_CODES as int]) && bb == u64s(cp[PA_BRAND_BASE as int])
    &&& oc == u8s(cp[PA_TYPE_CODES as int]) && ob == u64s(cp[PA_TYPE_BASE as int])
}

/// Every row packed with its composite key.
fn pack_rows(zc: &[u8], zb: &[i64], bc: &[u8], bb: &[u64], oc: &[u8], ob: &[u64], bs: usize, n: usize,
    nc: u64, ns: u64, smin: i64, nk: u64, Ghost(cp): Ghost<Seq<PartView>>, Ghost(rel): Ghost<Seq<Row>>)
    -> (packed: Vec<u64>)
    requires
        pack_src(cp, rel, n as int, bs as int, zc@, zb@, bc@, bb@, oc@, ob@),
        1 <= n <= 0xffff_ffff,
        nc as int == n_types(cp),
        n_brands(cp) <= 0x1_0000, n_types(cp) <= 0x1_0000,
        nk as int == n_brands(cp) * n_types(cp) * ns,
        nk <= MAX_KEYS,
        forall|s: int| 0 <= s < n ==> smin <= #[trigger] size_at(cp, s) < smin + ns,
    ensures
        packed@.len() == n,
        forall|x: int| 0 <= x < n ==> #[trigger] good(cp, n as int, nc as int, ns as int, smin as int, nk as int, packed@[x]),
        forall|x: int| 0 <= x < n ==> (#[trigger] packed@[x]) as int % p32() == x,
{
    let mut packed: Vec<u64> = Vec::with_capacity(n);
    let mut r: usize = 0;
    while r < n
        invariant
            pack_src(cp, rel, n as int, bs as int, zc@, zb@, bc@, bb@, oc@, ob@),
            1 <= n <= 0xffff_ffff,
            nc as int == n_types(cp),
            n_brands(cp) <= 0x1_0000, n_types(cp) <= 0x1_0000,
            nk as int == n_brands(cp) * n_types(cp) * ns,
            nk <= MAX_KEYS,
            forall|s: int| 0 <= s < n ==> smin <= #[trigger] size_at(cp, s) < smin + ns,
            r <= n,
            packed@.len() == r,
            forall|x: int| 0 <= x < r ==> #[trigger] good(cp, n as int, nc as int, ns as int, smin as int, nk as int, packed@[x]),
            forall|x: int| 0 <= x < r ==> (#[trigger] packed@[x]) as int % p32() == x,
        decreases n - r,
    {
        proof {
            lemma_div_lt(r as int, bs as int, zb@.len() as int);
            lemma_div_lt(r as int, bs as int, bb@.len() as int);
            lemma_div_lt(r as int, bs as int, ob@.len() as int);
            assert(dict_idx_ok(cp, r as int));
            assert(i64::MIN <= size_at(cp, r as int) <= i64::MAX);
            assert(smin <= size_at(cp, r as int) < smin + ns);
            lemma_comp_bound(bi_at(cp, r as int), ti_at(cp, r as int), size_at(cp, r as int) - smin,
                n_brands(cp), n_types(cp), ns as int);
        }
        let g = r / bs;
        proof {
            assert(g as int == r as int / bsize(cp));
            assert(bi_at(cp, r as int) == bb@[g as int] + bc@[r as int]);
            assert(ti_at(cp, r as int) == ob@[g as int] + oc@[r as int]);
            assert(size_at(cp, r as int) == zb@[g as int] + zc@[r as int]);
        }
        let bi = bb[g] + bc[r] as u64;
        let ci = ob[g] + oc[r] as u64;
        let sz = zb[g] + zc[r] as i64;
        let t = (sz - smin) as u64;
        proof {
            let (bv, cv, tv) = (bi as int, ci as int, t as int);
            assert(bv * nc <= 0x1_0000 * 0x1_0000) by (nonlinear_arith) requires 0 <= bv <= 0x1_0000, 0 <= nc <= 0x1_0000;
            assert((bv * nc + cv) * ns + tv == compk(cp, nc as int, ns as int, smin as int, r as int));
        }
        let key = (bi * nc + ci) * ns + t;
        proof {
            assert(key as int == compk(cp, nc as int, ns as int, smin as int, r as int));
            assert(key < nk);
        }
        let value = key * 0x1_0000_0000 + r as u64;
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(value as int, p32(), key as int, r as int);
            reveal(good);
            assert(good(cp, n as int, nc as int, ns as int, smin as int, nk as int, value));
        }
        packed.push(value);
        r = r + 1;
    }
    packed
}

/// The index rows and keys of the sorted packed values.
fn unpack(packed: &Vec<u64>, n: usize) -> (r: (Vec<u32>, Vec<u32>))
    requires packed@.len() == n, forall|x: int| 0 <= x < n ==> (#[trigger] packed@[x]) as int / p32() < MAX_KEYS,
    ensures
        r.0@.len() == n, r.1@.len() == n,
        forall|x: int| 0 <= x < n ==> (#[trigger] r.0@[x]) as int == packed@[x] as int % p32(),
        forall|x: int| 0 <= x < n ==> (#[trigger] r.1@[x]) as int == packed@[x] as int / p32(),
{
    let mut rows: Vec<u32> = Vec::with_capacity(n);
    let mut keys: Vec<u32> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            packed@.len() == n, forall|x: int| 0 <= x < n ==> (#[trigger] packed@[x]) as int / p32() < MAX_KEYS,
            i <= n, rows@.len() == i, keys@.len() == i,
            forall|x: int| 0 <= x < i ==> (#[trigger] rows@[x]) as int == packed@[x] as int % p32(),
            forall|x: int| 0 <= x < i ==> (#[trigger] keys@[x]) as int == packed@[x] as int / p32(),
        decreases n - i,
    {
        let x = packed[i];
        assert(x as int / p32() < MAX_KEYS);
        rows.push((x % 0x1_0000_0000) as u32);
        keys.push((x / 0x1_0000_0000) as u32);
        i = i + 1;
    }
    (rows, keys)
}

/// The keys never decrease.
pub open spec fn keys_sorted(keys: Seq<u32>) -> bool {
    forall|a: int, b: int| 0 <= a <= b < keys.len() ==> #[trigger] keys[a] <= #[trigger] keys[b]
}

/// Offset `j` of the directory: the first position whose key is at least `j`.
pub open spec fn first_at_least(keys: Seq<u32>, j: int, o: int) -> bool {
    &&& 0 <= o <= keys.len()
    &&& forall|i: int| 0 <= i < o ==> #[trigger] keys[i] < j
    &&& o < keys.len() ==> keys[o] >= j
}

/// The directory over the sorted keys (all below `nk`): `offs[j]` is the first position whose key is at least `j`.
fn build_dir(keys: &Vec<u32>, nk: usize) -> (offs: Vec<u32>)
    requires
        keys_sorted(keys@),
        keys@.len() <= u32::MAX,
        nk < usize::MAX,
    ensures
        offs@.len() == nk + 1,
        forall|j: int| 0 <= j <= nk ==> #[trigger] first_at_least(keys@, j, offs@[j] as int),
{
    let n = keys.len();
    let mut offs: Vec<u32> = Vec::with_capacity(nk + 1);
    let mut p: usize = 0;
    let mut j: usize = 0;
    while j <= nk
        invariant
            keys_sorted(keys@), n == keys@.len(), n <= u32::MAX, nk < usize::MAX,
            j <= nk + 1,
            offs@.len() == j,
            p <= n,
            j > 0 ==> p == offs@[j - 1],
            forall|i: int| 0 <= i < p ==> #[trigger] keys@[i] < j,
            forall|jj: int| 0 <= jj < j ==> #[trigger] first_at_least(keys@, jj, offs@[jj] as int),
        decreases nk + 1 - j,
    {
        while p < n && (keys[p] as usize) < j
            invariant
                keys_sorted(keys@), n == keys@.len(), p <= n,
                forall|i: int| 0 <= i < p ==> #[trigger] keys@[i] < j,
            decreases n - p,
        {
            p = p + 1;
        }
        let ghost o0 = offs@;
        offs.push(p as u32);
        proof {
            assert(first_at_least(keys@, j as int, p as int));
            assert forall|jj: int| 0 <= jj < j + 1 implies #[trigger] first_at_least(keys@, jj, offs@[jj] as int) by {
                if jj < j {
                    assert(offs@[jj] == o0[jj]);
                }
            }
            assert forall|i: int| 0 <= i < p implies #[trigger] keys@[i] < j + 1 by {}
        }
        j = j + 1;
    }
    offs
}

/// Under `first_at_least`, the offsets never decrease, and a position lies in the entry of its key.
proof fn lemma_dir_facts(keys: Seq<u32>, offs: Seq<u32>, nk: int, p: int)
    requires
        keys_sorted(keys),
        offs.len() == nk + 1,
        forall|j: int| 0 <= j <= nk ==> #[trigger] first_at_least(keys, j, offs[j] as int),
        0 <= p < keys.len(),
        keys[p] < nk,
    ensures
        offs[keys[p] as int] <= p < offs[keys[p] + 1],
{
    let k = keys[p] as int;
    assert(first_at_least(keys, k, offs[k] as int));
    assert(first_at_least(keys, k + 1, offs[k + 1] as int));
    if p < offs[k] {
        assert(keys[p] < k);
    }
    if p >= offs[k + 1] {
        let o = offs[k + 1] as int;
        assert(o < keys.len());
        assert(keys[o] >= k + 1);
        assert(keys[o] <= keys[p]);
    }
}

/// Offsets never decrease.
proof fn lemma_dir_mono(keys: Seq<u32>, offs: Seq<u32>, nk: int, e: int)
    requires
        keys_sorted(keys),
        offs.len() == nk + 1,
        forall|j: int| 0 <= j <= nk ==> #[trigger] first_at_least(keys, j, offs[j] as int),
        0 <= e < nk,
    ensures
        offs[e] <= offs[e + 1],
{
    assert(first_at_least(keys, e, offs[e] as int));
    assert(first_at_least(keys, e + 1, offs[e + 1] as int));
    if offs[e + 1] < offs[e] {
        let o = offs[e + 1] as int;
        assert(keys[o] < e);
        assert(keys[o] >= e + 1);
    }
}

/// The new storage's parts represent the stored relations of every database bound to the source.
proof fn lemma_built(sv: StoresView, db: Database, built: Seq<PartView>, idx: Option<(i64, i64, Seq<u32>, Seq<u32>, Seq<u32>)>)
    requires
        sources_bound(sv, db),
        built.len() == 3,
        built[0] == PartView::I64(match idx { Some((smin, ns, o, r, k)) => seq![MODE_INDEX, smin, ns], None => seq![0i64, 0i64, 0i64] }),
        built[1] == PartView::U32(match idx { Some((smin, ns, o, r, k)) => o, None => seq![0u32] }),
        built[2] == PartView::U32(match idx { Some((smin, ns, o, r, k)) => r, None => Seq::<u32>::empty() }),
        idx matches Some((smin, ns, o, r, k)) ==> {
            let cp = sv.custpart;
            let n = n_rows(cp);
            let nk = n_brands(cp) * n_types(cp) * ns;
            &&& ns >= 1
            &&& o.len() == nk + 1
            &&& r.len() == n && k.len() == n
            &&& perm_view_ok(r, n)
            &&& keys_sorted(k)
            &&& forall|j: int| 0 <= j <= nk ==> #[trigger] first_at_least(k, j, o[j] as int)
            &&& forall|p: int| 0 <= p < n ==> #[trigger] k[p] < nk && k[p] == compk(cp, n_types(cp), ns as int, smin as int, r[p] as int)
            &&& forall|s: int| 0 <= s < n ==> smin <= #[trigger] size_at(cp, s) < smin + ns
        },
    ensures
        represents(storage_parts(sv, built), stored_relations(db)),
{
    let cp = sv.custpart;
    let parts = storage_parts(sv, built);
    let rels = stored_relations(db);
    lemma_src(sv, db);
    D::lemma_stored_relations(db);
    let rel = rels[0];
    let n = rel.len() as int;
    assert(parts.len() == PART_BTS_PARTS);
    assert forall|k: int| 0 <= k < CUSTPART_PARTS implies #[trigger] parts[k] == cp[k] by {}
    assert(parts[IDX_META as int] == built[0]);
    assert(parts[IDX_OFFS as int] == built[1]);
    assert(parts[IDX_PERM as int] == built[2]);
    assert(parts[PA_LAYOUT as int] == cp[PA_LAYOUT as int]);
    assert(parts[PA_PARTKEY_CODES as int] == cp[PA_PARTKEY_CODES as int]);
    assert(parts[PA_PARTKEY_BASE as int] == cp[PA_PARTKEY_BASE as int]);
    assert(parts[PA_SIZE_CODES as int] == cp[PA_SIZE_CODES as int]);
    assert(parts[PA_SIZE_BASE as int] == cp[PA_SIZE_BASE as int]);
    assert(parts[PA_BRAND_CODES as int] == cp[PA_BRAND_CODES as int]);
    assert(parts[PA_BRAND_BASE as int] == cp[PA_BRAND_BASE as int]);
    assert(parts[PA_BRAND_DOFFS as int] == cp[PA_BRAND_DOFFS as int]);
    assert(parts[PA_BRAND_DBYTES as int] == cp[PA_BRAND_DBYTES as int]);
    assert(parts[PA_TYPE_CODES as int] == cp[PA_TYPE_CODES as int]);
    assert(parts[PA_TYPE_BASE as int] == cp[PA_TYPE_BASE as int]);
    assert(parts[PA_TYPE_DOFFS as int] == cp[PA_TYPE_DOFFS as int]);
    assert(parts[PA_TYPE_DBYTES as int] == cp[PA_TYPE_DBYTES as int]);
    assert(pa_shape(parts, n));
    assert forall|r: int| #[trigger] row_at(parts, r) == row_at(cp, r) by {}
    assert forall|r: int| #[trigger] dict_idx_ok(parts, r) == dict_idx_ok(cp, r) by {}
    assert forall|r: int| 0 <= r < n implies #[trigger] rel[r] == row_at(parts, r) by {
        assert(rel[r] == row_at(cp, r));
    }
    assert forall|r: int| 0 <= r < n implies #[trigger] dict_idx_ok(parts, r) by {
        assert(dict_idx_ok(cp, r));
    }
    assert(rows_ok(parts, rel));
    match idx {
        Some((smin, ns, o, r, k)) => {
            let nk = n_brands(cp) * n_types(cp) * ns;
            assert(idx_meta(parts) == seq![MODE_INDEX, smin, ns]);
            assert(has_idx(parts));
            assert(idx_offs(parts) == o);
            assert(idx_perm(parts) == r);
            assert(idx_smin(parts) == smin && idx_ns(parts) == ns);
            assert(n_brands(parts) == n_brands(cp) && n_types(parts) == n_types(cp));
            assert(idx_nkeys(parts) == nk);
            assert forall|p: int| 0 <= p < n implies 0 <= #[trigger] prow(parts, p) < n by {
                assert(r[p] < n);
            }
            assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b implies
                #[trigger] prow(parts, a) != #[trigger] prow(parts, b) by {
                assert(r[a] != r[b]);
            }
            assert forall|s: int| 0 <= s < n implies #[trigger] listed(parts, n, s) by {
                assert(covered_u32(r, s));
                let p = choose|p: int| 0 <= p < r.len() && r[p] == s;
                assert(prow(parts, p) == s);
            }
            assert forall|s: int| 0 <= s < n implies #[trigger] size_in(parts, s) by {
                assert(smin <= size_at(cp, s) < smin + ns);
            }
            assert forall|p: int| 0 <= p < n implies #[trigger] in_entry(parts, p) by {
                assert(k[p] < nk && k[p] == compk(cp, n_types(cp), ns as int, smin as int, r[p] as int));
                assert(comp_at(parts, prow(parts, p)) == k[p]);
                lemma_dir_facts(k, o, nk, p);
            }
            assert forall|e: int| 0 <= e < idx_nkeys(parts) implies #[trigger] idx_offs(parts)[e] <= idx_offs(parts)[e + 1] by {
                lemma_dir_mono(k, o, nk, e);
            }
            assert(first_at_least(k, nk, o[nk] as int));
            assert(idx_ok(parts, n));
        },
        None => {
            assert(idx_meta(parts) == seq![0i64, 0i64, 0i64]);
            assert(!has_idx(parts));
        },
    }
}

/// The packed values sorted ascending have nondecreasing keys; each still holds its row and key.
proof fn lemma_sorted_keys(cp: Seq<PartView>, n: int, nc: int, ns: int, smin: int, nk: int, packed: Seq<u64>,
    rows: Seq<u32>, keys: Seq<u32>)
    requires
        packed.len() == n, rows.len() == n, keys.len() == n,
        sorted64(seg64(packed, 0, n)),
        forall|x: int| 0 <= x < n ==> #[trigger] good(cp, n, nc, ns, smin, nk, packed[x]),
        forall|x: int| 0 <= x < n ==> (#[trigger] rows[x]) as int == packed[x] as int % p32(),
        forall|x: int| 0 <= x < n ==> (#[trigger] keys[x]) as int == packed[x] as int / p32(),
    ensures
        keys_sorted(keys),
        forall|p: int| 0 <= p < n ==> #[trigger] keys[p] < nk && keys[p] == compk(cp, nc, ns, smin, rows[p] as int),
{
    reveal(good);
    assert forall|a: int, b: int| 0 <= a <= b < keys.len() implies #[trigger] keys[a] <= #[trigger] keys[b] by {
        if a < b {
            assert(seg64(packed, 0, n)[a] == packed[a] && seg64(packed, 0, n)[b] == packed[b]);
            vstd::arithmetic::div_mod::lemma_div_is_ordered(packed[a] as int, packed[b] as int, p32());
        }
    }
    assert forall|p: int| 0 <= p < n implies #[trigger] keys[p] < nk && keys[p] == compk(cp, nc, ns, smin, rows[p] as int) by {
        assert(good(cp, n, nc, ns, smin, nk, packed[p]));
    }
}

pub fn build(stores: &mut Stores, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        sources_ready(old(stores)@),
        1 <= workers <= MAX_WORKERS,
    ensures
        match r {
            Ok(p) => forall|db: Database| #[trigger] sources_bound(old(stores)@, db)
                ==> represents(storage_parts(old(stores)@, owned_parts_view(p@)), stored_relations(db)),
            Err(QueryError::WorkerFailed(_)) => true,
            Err(_) => false,
        },
{
    let ghost sv = stores@;
    let ghost cp = sv.custpart;
    let ghost db0 = choose|db: Database| #[trigger] sources_bound(sv, db);
    let ghost rel0 = D::stored_relations(db0)[0];
    proof {
        lemma_src(sv, db0);
    }
    let lay = stores.custpart.extent_u64(PA_LAYOUT, 0, 2);
    let n = stores.custpart.part_len(PA_PARTKEY_CODES);
    let bs64 = lay[1];
    let nbo = stores.custpart.part_len(PA_BRAND_DOFFS);
    let nco = stores.custpart.part_len(PA_TYPE_DOFFS);
    proof {
        assert(n as int == n_rows(cp));
        assert(bs64 as int == bsize(cp));
        assert(nbo as int == b_offs(cp).len());
        assert(nco as int == t_offs(cp).len());
    }
    let mut idx: Option<(i64, i64, Vec<u32>, Vec<u32>, Vec<u32>)> = None;
    if n >= 1 && n <= 0xffff_ffff && bs64 <= n as u64 && nbo <= 0x1_0000 && nco <= 0x1_0000 {
        let bs = bs64 as usize;
        let nb = (nbo - 1) as u64;
        let nc = (nco - 1) as u64;
        let nzb = stores.custpart.part_len(PA_SIZE_BASE);
        let nbb = stores.custpart.part_len(PA_BRAND_BASE);
        let nob = stores.custpart.part_len(PA_TYPE_BASE);
        let zc = stores.custpart.extent_u8(PA_SIZE_CODES, 0, n);
        let zb = stores.custpart.extent_i64(PA_SIZE_BASE, 0, nzb);
        let bc = stores.custpart.extent_u8(PA_BRAND_CODES, 0, n);
        let bb = stores.custpart.extent_u64(PA_BRAND_BASE, 0, nbb);
        let oc = stores.custpart.extent_u8(PA_TYPE_CODES, 0, n);
        let ob = stores.custpart.extent_u64(PA_TYPE_BASE, 0, nob);
        proof {
            assert(zc@ =~= u8s(cp[PA_SIZE_CODES as int]));
            assert(zb@ =~= i64s(cp[PA_SIZE_BASE as int]));
            assert(bc@ =~= u8s(cp[PA_BRAND_CODES as int]));
            assert(bb@ =~= u64s(cp[PA_BRAND_BASE as int]));
            assert(oc@ =~= u8s(cp[PA_TYPE_CODES as int]));
            assert(ob@ =~= u64s(cp[PA_TYPE_BASE as int]));
            assert(pack_src(cp, rel0, n as int, bs as int, zc@, zb@, bc@, bb@, oc@, ob@));
        }
        let (smin, smax) = size_range(zc, zb, bs, n, Ghost(cp));
        if (smax as i128) - (smin as i128) < 0x10_0000 {
            let ns = (smax - smin + 1) as u64;
            proof {
                assert(nb * nc <= 0x1_0000 * 0x1_0000) by (nonlinear_arith) requires nb <= 0x1_0000, nc <= 0x1_0000;
            }
            let nbc = nb * nc;
            proof {
                assert(ns <= 0x10_0000);
                if nbc <= MAX_KEYS {
                    assert(nbc * ns <= MAX_KEYS * 0x10_0000) by (nonlinear_arith) requires nbc <= MAX_KEYS, ns <= 0x10_0000;
                }
            }
            if nbc <= MAX_KEYS && nbc * ns <= MAX_KEYS {
                let nk = nbc * ns;
                proof {
                    assert(nk as int == n_brands(cp) * n_types(cp) * ns) by (nonlinear_arith)
                        requires nk == nbc * ns, nbc == nb * nc, nb as int == n_brands(cp), nc as int == n_types(cp);
                }
                let mut packed = pack_rows(zc, zb, bc, bb, oc, ob, bs, n, nc, ns, smin, nk, Ghost(cp), Ghost(rel0));
                let mut tmp: Vec<u64> = vec![0u64; n];
                let ghost pr = |x: u64| good(cp, n as int, nc as int, ns as int, smin as int, nk as int, x);
                proof {
                    assert forall|x: int| 0 <= x < n implies #[trigger] pr(packed@[x]) by {}
                }
                msort64(&mut packed, &mut tmp, 0, n, Ghost(pr));
                proof {
                    reveal(good);
                    assert forall|x: int| 0 <= x < n implies (#[trigger] packed@[x]) as int / p32() < MAX_KEYS by {
                        assert(pr(packed@[x]));
                    }
                }
                let (rows, keys) = unpack(&packed, n);
                proof {
                    assert forall|x: int| 0 <= x < n implies #[trigger] good(cp, n as int, nc as int, ns as int, smin as int, nk as int, packed@[x]) by {
                        assert(pr(packed@[x]));
                    }
                    lemma_sorted_keys(cp, n as int, nc as int, ns as int, smin as int, nk as int, packed@, rows@, keys@);
                }
                let offs = build_dir(&keys, nk as usize);
                if check_perm(&rows) {
                    idx = Some((smin, ns as i64, offs, rows, keys));
                }
            }
        }
    }
    let ghost gidx: Option<(i64, i64, Seq<u32>, Seq<u32>, Seq<u32>)> = match &idx {
        Some((smin, ns, o, r, k)) => Some((*smin, *ns, o@, r@, k@)),
        None => None,
    };
    let mut meta: Vec<i64> = Vec::new();
    let (offs, rows): (Vec<u32>, Vec<u32>) = match idx {
        Some((smin, ns, o, r, k)) => {
            meta.push(MODE_INDEX);
            meta.push(smin);
            meta.push(ns);
            (o, r)
        },
        None => {
            meta.push(0);
            meta.push(0);
            meta.push(0);
            let mut z: Vec<u32> = Vec::new();
            z.push(0);
            (z, Vec::new())
        },
    };
    let ghost (mv, ov, rv) = (meta@, offs@, rows@);
    let mut out: Vec<OwnedPart> = Vec::new();
    out.push(OwnedPart::I64(meta));
    out.push(OwnedPart::U32(offs));
    out.push(OwnedPart::U32(rows));
    proof {
        let built = owned_parts_view(out@);
        assert(built.len() == 3);
        assert(built[0] == PartView::I64(mv));
        assert(built[1] == PartView::U32(ov));
        assert(built[2] == PartView::U32(rv));
        match gidx {
            Some((smin, ns, o, r, k)) => {
                assert(mv =~= seq![MODE_INDEX, smin, ns]);
            },
            None => {
                assert(mv =~= seq![0i64, 0i64, 0i64]);
                assert(ov =~= seq![0u32]);
                assert(rv =~= Seq::<u32>::empty());
            },
        }
        assert forall|db: Database| #[trigger] sources_bound(sv, db) implies
            represents(storage_parts(sv, built), stored_relations(db)) by {
            lemma_built(sv, db, built, gidx);
        }
    }
    Ok(out)
}

} // verus!
