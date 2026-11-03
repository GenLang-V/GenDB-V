//! The part pass: the keys and branch codes of the part rows satisfying some branch (`PartTask`, one task per range
//! of 64-row words). A task writes, for each such row of its range in order, the row's `p_partkey` and its branch code
//! (bit `k` for branch `k`) into key and code buffers allocated by the caller (one entry per 64 rows, plus 64; TPC-H
//! has ~0.24% qualifying rows); `plist_ok` states the list: every listed key has its code, and every qualifying row of
//! the range has its key listed. A task whose buffers could overflow stops and reports `full`; the caller then lists
//! the keys on its own thread (`serial_keys`).
//!
//! Per 64-row word (`part_word`): the size and brand masks, then, for the rare rows still possible, the container
//! (`cont_bit`). When every brand parameter has 8 bytes and the word's 64 brands are 8 bytes each stored back to back
//! (TPC-H's `Brand#MN`), the masks come from `fast_pre_word`: the 512 brand bytes are compared word by word with the
//! parameters, branch-free; otherwise `pre_word` tests the brand of each row whose size is in range.
use vstd::prelude::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{fork_join, Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::spec::ast::Literal;
use crate::agent::tables::*;
use crate::agent::line::*;
use crate::agent::cols::*;
use crate::agent::bind::*;
use crate::agent::common::bits::*;
use crate::agent::common::text_eq::*;
use crate::agent::common::tz::{tz64, tz_table_array};
use crate::agent::keymap::*;

verus! {

/// Number of 64-row words of `n` rows.
pub open spec fn nwords(n: int) -> int { n / 64 + if n % 64 != 0 { 1int } else { 0int } }

// ------------------------------------------------------------------------------------------------ one row

/// The container literals of branch `k`, padded to 24 bytes, with their lengths.
fn cont_lits(k: usize) -> (r: ([u8; 24], usize, [u8; 24], usize, [u8; 24], usize, [u8; 24], usize))
    requires k < 3,
    ensures
        r.1 <= 24 && r.3 <= 24 && r.5 <= 24 && r.7 <= 24,
        lit_of(r.0, r.1) == cont_lit(k as int, 0), lit_of(r.2, r.3) == cont_lit(k as int, 1),
        lit_of(r.4, r.5) == cont_lit(k as int, 2), lit_of(r.6, r.7) == cont_lit(k as int, 3),
    no_unwind
{
    let r = if k == 0 {
        ([83, 77, 32, 67, 65, 83, 69, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 7,
         [83, 77, 32, 66, 79, 88, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 6,
         [83, 77, 32, 80, 65, 67, 75, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 7,
         [83, 77, 32, 80, 75, 71, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 6)
    } else if k == 1 {
        ([77, 69, 68, 32, 66, 65, 71, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 7,
         [77, 69, 68, 32, 66, 79, 88, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 7,
         [77, 69, 68, 32, 80, 75, 71, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 7,
         [77, 69, 68, 32, 80, 65, 67, 75, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 8)
    } else {
        ([76, 71, 32, 67, 65, 83, 69, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 7,
         [76, 71, 32, 66, 79, 88, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 6,
         [76, 71, 32, 80, 65, 67, 75, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 7,
         [76, 71, 32, 80, 75, 71, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 6)
    };
    proof {
        assert(lit_of(r.0, r.1) =~= cont_lit(k as int, 0));
        assert(lit_of(r.2, r.3) =~= cont_lit(k as int, 1));
        assert(lit_of(r.4, r.5) =~= cont_lit(k as int, 2));
        assert(lit_of(r.6, r.7) =~= cont_lit(k as int, 3));
    }
    r
}

/// Part row `r`'s container is one of branch `k`'s.
fn cont_in(c: &PartCols, r: usize, k: usize, Ghost(sv): Ghost<StoresView>) -> (b: bool)
    requires part_cols_ok(*c, sv), r < c.np, k < 3,
    ensures b == cont_ok(k as int, p_cont(sv, r as int)),
    no_unwind
{
    let o = c.cont.offs;
    let by = c.cont.bytes;
    let ghost n = c.np as int;
    let (l0, n0, l1, n1, l2, n2, l3, n3) = cont_lits(k);
    text_is_lit(o, by, r, &l0, n0, Ghost(n)) || text_is_lit(o, by, r, &l1, n1, Ghost(n))
        || text_is_lit(o, by, r, &l2, n2, Ghost(n)) || text_is_lit(o, by, r, &l3, n3, Ghost(n))
}

/// Branch `k`'s size and brand conditions on part row `r` (the container is checked separately).
pub open spec fn pre_cond(sv: StoresView, ps: Seq<Literal>, k: int, r: int) -> bool {
    p_brand(sv, r) == pb(ps, k) && 1 <= p_size(sv)[r] <= size_hi(k)
}

/// Branch `k`'s size range on part row `r`.
pub open spec fn size_ok(sv: StoresView, k: int, r: int) -> bool { 1 <= p_size(sv)[r] <= size_hi(k) }

/// The brand of part row `r` against the three brand parameters (one word comparison each when the stored brand
/// has 8 bytes).
#[inline(always)]
fn brand_eq(c: &PartCols, x: &Bind, r: usize, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (m: (bool, bool, bool))
    requires part_cols_ok(*c, sv), bind_ok(*x, ps), r < c.np,
    ensures
        m.0 == (p_brand(sv, r as int) == pb(ps, 0)),
        m.1 == (p_brand(sv, r as int) == pb(ps, 1)),
        m.2 == (p_brand(sv, r as int) == pb(ps, 2)),
    no_unwind
{
    let ghost n = c.np as int;
    let bo = c.brand.offs;
    let bb = c.brand.bytes;
    proof {
        assert(0 <= bo@[r as int] <= bo@[r + 1] <= bb@.len());
        assert(vstd::slice::spec_slice_len(bb) as int == bb@.len());
    }
    let s = bo[r] as usize;
    let e = bo[r + 1] as usize;
    let ghost br = bb@.subrange(s as int, e as int);
    if e - s == 8 {
        // one word comparison per branch (a parameter of another length never equals 8 bytes)
        let v = load8(bb, s);
        proof {
            if x.e0 { lemma_pack8_eq(br, pb(ps, 0)); }
            if x.e1 { lemma_pack8_eq(br, pb(ps, 1)); }
            if x.e2 { lemma_pack8_eq(br, pb(ps, 2)); }
        }
        (x.e0 && v == x.k0, x.e1 && v == x.k1, x.e2 && v == x.k2)
    } else {
        (text_is(bo, bb, r, x.b0, x.n0, Ghost(n)), text_is(bo, bb, r, x.b1, x.n1, Ghost(n)),
            text_is(bo, bb, r, x.b2, x.n2, Ghost(n)))
    }
}

/// The size ranges of the rows `lo .. hi` (at most 64) as three masks (straight-line over a full word).
fn size_word(c: &PartCols, lo: usize, hi: usize, Ghost(sv): Ghost<StoresView>) -> (r: (u64, u64, u64))
    requires part_cols_ok(*c, sv), lo < hi <= c.np, hi - lo <= 64,
    ensures
        forall|u: u64| u < 64 ==> #[trigger] bit(r.0, u) == (lo + u < hi && size_ok(sv, 0, lo + u)),
        forall|u: u64| u < 64 ==> #[trigger] bit(r.1, u) == (lo + u < hi && size_ok(sv, 1, lo + u)),
        forall|u: u64| u < 64 ==> #[trigger] bit(r.2, u) == (lo + u < hi && size_ok(sv, 2, lo + u)),
    no_unwind
{
    let mut z0: u64 = 0;
    let mut z1: u64 = 0;
    let mut z2: u64 = 0;
    proof {
        assert forall|u: u64| u < 64 implies !#[trigger] bit(0u64, u) by { lemma_bit_zero(u); }
    }
    let (_, tail) = c.size.split_at(lo);
    let n = hi - lo;
    let mut u: usize = 0;
    while u < n
        invariant
            part_cols_ok(*c, sv), lo < hi <= c.np, n == hi - lo, n <= 64, u <= n,
            tail@ == c.size@.subrange(lo as int, c.size@.len() as int),
            forall|v: u64| v < 64 ==> #[trigger] bit(z0, v) == (v < u && size_ok(sv, 0, lo + v)),
            forall|v: u64| v < 64 ==> #[trigger] bit(z1, v) == (v < u && size_ok(sv, 1, lo + v)),
            forall|v: u64| v < 64 ==> #[trigger] bit(z2, v) == (v < u && size_ok(sv, 2, lo + v)),
        decreases n - u,
    {
        let sz = tail[u];
        proof { assert(sz == p_size(sv)[lo + u]); }
        let x0: u64 = if 1 <= sz && sz <= 5 { 1 } else { 0 };
        let x1: u64 = if 1 <= sz && sz <= 10 { 1 } else { 0 };
        let x2: u64 = if 1 <= sz && sz <= 15 { 1 } else { 0 };
        let t = u as u64;
        let ghost (o0, o1, o2) = (z0, z1, z2);
        z0 = z0 | (x0 << t);
        z1 = z1 | (x1 << t);
        z2 = z2 | (x2 << t);
        proof {
            assert forall|v: u64| v < 64 implies #[trigger] bit(z0, v) == (v < u + 1 && size_ok(sv, 0, lo + v)) by {
                lemma_bit_set(o0, x0, t, v);
            }
            assert forall|v: u64| v < 64 implies #[trigger] bit(z1, v) == (v < u + 1 && size_ok(sv, 1, lo + v)) by {
                lemma_bit_set(o1, x1, t, v);
            }
            assert forall|v: u64| v < 64 implies #[trigger] bit(z2, v) == (v < u + 1 && size_ok(sv, 2, lo + v)) by {
                lemma_bit_set(o2, x2, t, v);
            }
        }
        u = u + 1;
    }
    (z0, z1, z2)
}

/// Flags in {0, 1}: their `&` is 1 exactly when both are.
proof fn lemma_and01(a: u64, b: u64)
    requires a == 0 || a == 1, b == 0 || b == 1,
    ensures (a & b) == (if a == 1 && b == 1 { 1u64 } else { 0u64 }),
{
    assert((a == 0u64 || a == 1u64) && (b == 0u64 || b == 1u64) ==> (a & b) == (if a == 1u64 && b == 1u64 { 1u64 } else { 0u64 }))
        by (bit_vector);
}

/// The brand of row `lo + u` is the word at `8 u` of the 512 bytes `ch` that start at the brand offset of row `lo`,
/// when the row's offsets are `8 u` and `8 u + 8` past that offset.
proof fn lemma_chunk_brand(c: PartCols, sv: StoresView, lo: int, u: int, base: int, ch: Seq<u8>)
    requires
        part_cols_ok(c, sv), 0 <= lo, lo + 64 <= c.np, 0 <= u < 64,
        base == c.brand.offs@[lo], ch == c.brand.bytes@.subrange(base, base + 512), base + 512 <= c.brand.bytes@.len(),
        c.brand.offs@[lo + u] - base == 8 * u, c.brand.offs@[lo + u + 1] - c.brand.offs@[lo + u] == 8,
    ensures p_brand(sv, lo + u) == ch.subrange(8 * u, 8 * u + 8),
{
    let s = c.brand.offs@[lo + u] as int;
    assert(p_brand(sv, lo + u) == c.brand.bytes@.subrange(s, s + 8));
    assert(c.brand.bytes@.subrange(s, s + 8) =~= ch.subrange(8 * u, 8 * u + 8));
}

/// The size and brand masks of the full word `lo .. lo + 64` when every brand parameter has 8 bytes and the word's
/// brands are 8 bytes each, stored back to back (`None` otherwise): the 64 brands are then the 512 bytes from the
/// word's first offset, compared word by word with the parameters, without a branch per row.
fn fast_pre_word(c: &PartCols, x: &Bind, lo: usize, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: Option<(u64, u64, u64)>)
    requires part_cols_ok(*c, sv), bind_ok(*x, ps), lo + 64 <= c.np, x.e0, x.e1, x.e2,
    ensures
        r matches Some((m0, m1, m2)) ==> {
            &&& forall|u: u64| u < 64 ==> #[trigger] bit(m0, u) == pre_cond(sv, ps, 0, lo + u)
            &&& forall|u: u64| u < 64 ==> #[trigger] bit(m1, u) == pre_cond(sv, ps, 1, lo + u)
            &&& forall|u: u64| u < 64 ==> #[trigger] bit(m2, u) == pre_cond(sv, ps, 2, lo + u)
        },
    no_unwind
{
    let (_, st) = c.size.split_at(lo);
    let (sz, _) = st.split_at(64);
    let (_, ot) = c.brand.offs.split_at(lo);
    let (o, _) = ot.split_at(65);
    proof {
        assert(o@[0] == c.brand.offs@[lo as int]);
        assert(0 <= c.brand.offs@[lo as int]);
    }
    let base = o[0];
    let (_, bt) = match c.brand.bytes.split_at_checked(base as usize) { Some(p) => p, None => { return None; } };
    let (ch, _) = match bt.split_at_checked(512) { Some(p) => p, None => { return None; } };
    proof {
        assert(ch@ =~= c.brand.bytes@.subrange(base as int, base + 512));
    }
    let (k0, k1, k2) = (x.k0, x.k1, x.k2);
    let mut m0: u64 = 0;
    let mut m1: u64 = 0;
    let mut m2: u64 = 0;
    let mut bad: u64 = 0;
    proof {
        assert forall|u: u64| u < 64 implies !#[trigger] bit(0u64, u) by { lemma_bit_zero(u); }
    }
    let mut u: usize = 0;
    while u < 64
        invariant
            part_cols_ok(*c, sv), bind_ok(*x, ps), lo + 64 <= c.np, x.e0, x.e1, x.e2,
            k0 == x.k0, k1 == x.k1, k2 == x.k2, u <= 64,
            sz@ == c.size@.subrange(lo as int, lo + 64), o@ == c.brand.offs@.subrange(lo as int, lo + 65),
            base == c.brand.offs@[lo as int], ch@ == c.brand.bytes@.subrange(base as int, base + 512),
            base + 512 <= c.brand.bytes@.len(),
            bad == 0 ==> forall|v: u64| v < 64 ==> #[trigger] bit(m0, v) == (v < u && pre_cond(sv, ps, 0, lo + v)),
            bad == 0 ==> forall|v: u64| v < 64 ==> #[trigger] bit(m1, v) == (v < u && pre_cond(sv, ps, 1, lo + v)),
            bad == 0 ==> forall|v: u64| v < 64 ==> #[trigger] bit(m2, v) == (v < u && pre_cond(sv, ps, 2, lo + v)),
        decreases 64 - u,
    {
        let ghost r = lo + u;
        proof {
            assert(o@[u as int] == c.brand.offs@[r] && o@[u + 1] == c.brand.offs@[r + 1]);
            assert(0 <= c.brand.offs@[r] <= c.brand.offs@[r + 1]);
            assert(sz@[u as int] == p_size(sv)[r]);
        }
        let s = o[u];
        let e = o[u + 1];
        // the row's brand is the chunk's word `u`
        let off: u64 = if s - base == 8 * u as i64 && e - s == 8 { 0 } else { 1 };
        let v = load8(ch, 8 * u);
        let z = sz[u];
        let s0: u64 = if 1 <= z && z <= 5 { 1 } else { 0 };
        let s1: u64 = if 1 <= z && z <= 10 { 1 } else { 0 };
        let s2: u64 = if 1 <= z && z <= 15 { 1 } else { 0 };
        let e0: u64 = if v == k0 { 1 } else { 0 };
        let e1: u64 = if v == k1 { 1 } else { 0 };
        let e2: u64 = if v == k2 { 1 } else { 0 };
        let b0 = s0 & e0;
        let b1 = s1 & e1;
        let b2 = s2 & e2;
        let ghost bad0 = bad;
        bad = bad | off;
        proof {
            lemma_and01(s0, e0);
            lemma_and01(s1, e1);
            lemma_and01(s2, e2);
            assert((bad0 | off) == 0u64 ==> bad0 == 0u64 && off == 0u64) by (bit_vector);
            if bad == 0 {
                lemma_chunk_brand(*c, sv, lo as int, u as int, base as int, ch@);
                assert(v == pack8_spec(p_brand(sv, r)));
                lemma_pack8_eq(p_brand(sv, r), pb(ps, 0));
                lemma_pack8_eq(p_brand(sv, r), pb(ps, 1));
                lemma_pack8_eq(p_brand(sv, r), pb(ps, 2));
                assert forall|w: u64| w < 64 implies #[trigger] bit(m0 | (b0 << (u as u64)), w) == (w < u + 1 && pre_cond(sv, ps, 0, lo + w)) by {
                    lemma_bit_set(m0, b0, u as u64, w);
                }
                assert forall|w: u64| w < 64 implies #[trigger] bit(m1 | (b1 << (u as u64)), w) == (w < u + 1 && pre_cond(sv, ps, 1, lo + w)) by {
                    lemma_bit_set(m1, b1, u as u64, w);
                }
                assert forall|w: u64| w < 64 implies #[trigger] bit(m2 | (b2 << (u as u64)), w) == (w < u + 1 && pre_cond(sv, ps, 2, lo + w)) by {
                    lemma_bit_set(m2, b2, u as u64, w);
                }
            }
        }
        m0 = m0 | (b0 << (u as u64));
        m1 = m1 | (b1 << (u as u64));
        m2 = m2 | (b2 << (u as u64));
        u = u + 1;
    }
    if bad != 0 {
        return None;
    }
    Some((m0, m1, m2))
}

/// The brand mask word `mk` of branch `k` holds, below bit `q`, the rows of `zk` whose brand is the branch's.
pub open spec fn brand_ok(mk: u64, zk: u64, k: int, lo: int, q: int, sv: StoresView, ps: Seq<Literal>) -> bool {
    forall|u: u64| u < 64 ==> #[trigger] bit(mk, u) == (u < q && bit(zk, u) && p_brand(sv, lo + u) == pb(ps, k))
}

/// One step of the brand test: row `lo + t` (brand equal to branch `k`'s parameter: `ek`), for branch `k`.
fn brand_bit(mk: u64, zk: u64, t: u64, ek: bool, Ghost(k): Ghost<int>, Ghost(lo): Ghost<int>, Ghost(q): Ghost<int>,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: u64)
    requires
        t < 64, q <= t, ek == (p_brand(sv, lo + t) == pb(ps, k)),
        brand_ok(mk, zk, k, lo, q, sv, ps),
        forall|u: u64| q <= u < t ==> !#[trigger] bit(zk, u),
    ensures brand_ok(r, zk, k, lo, t + 1, sv, ps),
    no_unwind
{
    let x: u64 = if (zk >> t) & 1u64 == 1u64 && ek { 1 } else { 0 };
    let r = mk | (x << t);
    proof {
        assert(!bit(mk, t));
        assert forall|u: u64| u < 64 implies #[trigger] bit(r, u) == (u < t + 1 && bit(zk, u) && p_brand(sv, lo + u) == pb(ps, k)) by {
            lemma_bit_set(mk, x, t, u);
        }
    }
    r
}

/// The size and brand masks of the rows `lo .. hi`: the brand is read only for the rows with a size bit.
fn pre_word(c: &PartCols, x: &Bind, table: &[u8; 64], lo: usize, hi: usize, Ghost(sv): Ghost<StoresView>,
    Ghost(ps): Ghost<Seq<Literal>>) -> (r: (u64, u64, u64))
    requires part_cols_ok(*c, sv), bind_ok(*x, ps), lo < hi <= c.np, hi - lo <= 64, table@.len() == 64,
    ensures
        forall|u: u64| u < 64 ==> #[trigger] bit(r.0, u) == (lo + u < hi && pre_cond(sv, ps, 0, lo + u)),
        forall|u: u64| u < 64 ==> #[trigger] bit(r.1, u) == (lo + u < hi && pre_cond(sv, ps, 1, lo + u)),
        forall|u: u64| u < 64 ==> #[trigger] bit(r.2, u) == (lo + u < hi && pre_cond(sv, ps, 2, lo + u)),
    no_unwind
{
    let (z0, z1, z2) = size_word(c, lo, hi, Ghost(sv));
    // every size range is inside branch 2's: `z2` covers `z0` and `z1`
    let mut todo = z2;
    let mut m0: u64 = 0;
    let mut m1: u64 = 0;
    let mut m2: u64 = 0;
    let ghost mut q: int = 0;
    proof {
        assert forall|u: u64| u < 64 implies !#[trigger] bit(0u64, u) by { lemma_bit_zero(u); }
    }
    while todo != 0
        invariant
            part_cols_ok(*c, sv), bind_ok(*x, ps), lo < hi <= c.np, hi - lo <= 64, table@.len() == 64,
            0 <= q <= 64,
            forall|u: u64| u < 64 ==> #[trigger] bit(z0, u) == (lo + u < hi && size_ok(sv, 0, lo + u)),
            forall|u: u64| u < 64 ==> #[trigger] bit(z1, u) == (lo + u < hi && size_ok(sv, 1, lo + u)),
            forall|u: u64| u < 64 ==> #[trigger] bit(z2, u) == (lo + u < hi && size_ok(sv, 2, lo + u)),
            forall|u: u64| u < 64 ==> #[trigger] bit(todo, u) == (q <= u && bit(z2, u)),
            brand_ok(m0, z0, 0, lo as int, q, sv, ps), brand_ok(m1, z1, 1, lo as int, q, sv, ps),
            brand_ok(m2, z2, 2, lo as int, q, sv, ps),
        decreases 64 - q,
    {
        proof { lemma_first_bit(todo); }
        let t = tz64(todo, table) as u64;
        let ghost todo0 = todo;
        proof {
            assert(bit(todo, t));
            assert forall|u: u64| q <= u < t implies !#[trigger] bit(z2, u) by { assert(!bit(todo, u)); }
            assert forall|u: u64| q <= u < t implies !#[trigger] bit(z1, u) by { assert(!bit(todo, u)); assert(!bit(z2, u)); }
            assert forall|u: u64| q <= u < t implies !#[trigger] bit(z0, u) by { assert(!bit(todo, u)); assert(!bit(z2, u)); }
        }
        todo = todo & (todo - 1);
        proof {
            assert(todo0 - 1 == sub(todo0, 1));
            assert forall|u: u64| u < 64 implies #[trigger] bit(todo, u) == (t + 1 <= u && bit(z2, u)) by {
                lemma_clear_lowest(todo0, t, u);
            }
            assert(lo + t < hi);
        }
        let (e0, e1, e2) = brand_eq(c, x, lo + t as usize, Ghost(sv), Ghost(ps));
        m0 = brand_bit(m0, z0, t, e0, Ghost(0), Ghost(lo as int), Ghost(q), Ghost(sv), Ghost(ps));
        m1 = brand_bit(m1, z1, t, e1, Ghost(1), Ghost(lo as int), Ghost(q), Ghost(sv), Ghost(ps));
        m2 = brand_bit(m2, z2, t, e2, Ghost(2), Ghost(lo as int), Ghost(q), Ghost(sv), Ghost(ps));
        proof { q = t + 1; }
    }
    proof {
        assert forall|u: u64| u < 64 && q <= u implies !#[trigger] bit(z2, u) by { lemma_bit_zero(u); assert(!bit(todo, u)); }
        assert forall|u: u64| u < 64 && q <= u implies !#[trigger] bit(z1, u) by { lemma_bit_zero(u); assert(!bit(todo, u)); assert(!bit(z2, u)); }
        assert forall|u: u64| u < 64 && q <= u implies !#[trigger] bit(z0, u) by { lemma_bit_zero(u); assert(!bit(todo, u)); assert(!bit(z2, u)); }
        assert forall|u: u64| u < 64 implies #[trigger] bit(m0, u) == (lo + u < hi && pre_cond(sv, ps, 0, lo + u)) by {
            assert(bit(m0, u) == (u < q && bit(z0, u) && p_brand(sv, lo + u) == pb(ps, 0)));
            if q <= u { assert(!bit(z0, u)); }
        }
        assert forall|u: u64| u < 64 implies #[trigger] bit(m1, u) == (lo + u < hi && pre_cond(sv, ps, 1, lo + u)) by {
            assert(bit(m1, u) == (u < q && bit(z1, u) && p_brand(sv, lo + u) == pb(ps, 1)));
            if q <= u { assert(!bit(z1, u)); }
        }
        assert forall|u: u64| u < 64 implies #[trigger] bit(m2, u) == (lo + u < hi && pre_cond(sv, ps, 2, lo + u)) by {
            assert(bit(m2, u) == (u < q && bit(z2, u) && p_brand(sv, lo + u) == pb(ps, 2)));
            if q <= u { assert(!bit(z2, u)); }
        }
    }
    (m0, m1, m2)
}

/// The three branch words of the rows `64 w .. min(64 w + 64, np)` (bits past the last row clear): the size and
/// brand masks (`pre_word`), then the container of the rows still possible.
fn part_word(c: &PartCols, x: &Bind, table: &[u8; 64], w: usize, fast: bool, Ghost(sv): Ghost<StoresView>,
    Ghost(ps): Ghost<Seq<Literal>>) -> (r: (u64, u64, u64))
    requires
        part_cols_ok(*c, sv), bind_ok(*x, ps), 64 * w < c.np, table@.len() == 64,
        fast ==> x.e0 && x.e1 && x.e2,
    ensures
        forall|u: u64| u < 64 ==> #[trigger] bit(r.0, u) == (64 * w + u < n_p(sv) && pcond(sv, ps, 0, 64 * w + u)),
        forall|u: u64| u < 64 ==> #[trigger] bit(r.1, u) == (64 * w + u < n_p(sv) && pcond(sv, ps, 1, 64 * w + u)),
        forall|u: u64| u < 64 ==> #[trigger] bit(r.2, u) == (64 * w + u < n_p(sv) && pcond(sv, ps, 2, 64 * w + u)),
    no_unwind
{
    let lo = 64 * w;
    let hi = if c.np - lo > 64 { lo + 64 } else { c.np };
    let fw = if fast && c.np - lo >= 64 { fast_pre_word(c, x, lo, Ghost(sv), Ghost(ps)) } else { None };
    let (m0, m1, m2) = match fw {
        Some(m) => m,
        None => pre_word(c, x, table, lo, hi, Ghost(sv), Ghost(ps)),
    };
    // phase 2: the container of the rows with a size and brand bit, lowest bit first
    let mut todo = m0 | m1 | m2;
    let mut r0: u64 = 0;
    let mut r1: u64 = 0;
    let mut r2: u64 = 0;
    let ghost mut q: int = 0;
    proof {
        assert forall|u: u64| u < 64 implies #[trigger] bit(todo, u) == (bit(m0, u) || bit(m1, u) || bit(m2, u)) by {
            lemma_bit_or3(m0, m1, m2, u);
        }
        assert forall|u: u64| u < 64 implies !#[trigger] bit(0u64, u) by { lemma_bit_zero(u); }
    }
    while todo != 0
        invariant
            part_cols_ok(*c, sv), lo == 64 * w, lo <= hi <= c.np, hi <= lo + 64, table@.len() == 64,
            0 <= q <= 64,
            forall|u: u64| u < 64 ==> #[trigger] bit(m0, u) == (lo + u < hi && pre_cond(sv, ps, 0, lo + u)),
            forall|u: u64| u < 64 ==> #[trigger] bit(m1, u) == (lo + u < hi && pre_cond(sv, ps, 1, lo + u)),
            forall|u: u64| u < 64 ==> #[trigger] bit(m2, u) == (lo + u < hi && pre_cond(sv, ps, 2, lo + u)),
            forall|u: u64| u < 64 ==> #[trigger] bit(todo, u) == (q <= u && (bit(m0, u) || bit(m1, u) || bit(m2, u))),
            res_ok(r0, m0, 0, lo as int, q, sv), res_ok(r1, m1, 1, lo as int, q, sv), res_ok(r2, m2, 2, lo as int, q, sv),
        decreases 64 - q,
    {
        proof { lemma_first_bit(todo); }
        let t = tz64(todo, table) as u64;
        let ghost todo0 = todo;
        proof {
            assert(bit(todo, t));
            assert forall|u: u64| q <= u < t implies !#[trigger] bit(m0, u) by { assert(!bit(todo, u)); }
            assert forall|u: u64| q <= u < t implies !#[trigger] bit(m1, u) by { assert(!bit(todo, u)); }
            assert forall|u: u64| q <= u < t implies !#[trigger] bit(m2, u) by { assert(!bit(todo, u)); }
        }
        todo = todo & (todo - 1);
        proof {
            assert(todo0 - 1 == sub(todo0, 1));
            assert forall|u: u64| u < 64 implies #[trigger] bit(todo, u) == (t + 1 <= u && (bit(m0, u) || bit(m1, u) || bit(m2, u))) by {
                lemma_clear_lowest(todo0, t, u);
            }
        }
        r0 = cont_bit(c, 0, lo, t, m0, r0, Ghost(q), Ghost(sv));
        r1 = cont_bit(c, 1, lo, t, m1, r1, Ghost(q), Ghost(sv));
        r2 = cont_bit(c, 2, lo, t, m2, r2, Ghost(q), Ghost(sv));
        proof { q = t + 1; }
    }
    proof {
        assert(hi == n_p(sv) || (hi == lo + 64 && lo + 64 <= n_p(sv)));
        assert forall|u: u64| u < 64 && q <= u implies !#[trigger] bit(m0, u) by { lemma_bit_zero(u); assert(!bit(todo, u)); }
        assert forall|u: u64| u < 64 && q <= u implies !#[trigger] bit(m1, u) by { lemma_bit_zero(u); assert(!bit(todo, u)); }
        assert forall|u: u64| u < 64 && q <= u implies !#[trigger] bit(m2, u) by { lemma_bit_zero(u); assert(!bit(todo, u)); }
        assert forall|u: u64| u < 64 implies #[trigger] bit(r0, u) == (64 * w + u < n_p(sv) && pcond(sv, ps, 0, 64 * w + u)) by {
            assert(bit(r0, u) == (u < q && bit(m0, u) && cont_ok(0, p_cont(sv, lo + u))));
            assert(bit(m0, u) == (lo + u < hi && pre_cond(sv, ps, 0, lo + u)));
            if q <= u { assert(!bit(m0, u)); }
        }
        assert forall|u: u64| u < 64 implies #[trigger] bit(r1, u) == (64 * w + u < n_p(sv) && pcond(sv, ps, 1, 64 * w + u)) by {
            assert(bit(r1, u) == (u < q && bit(m1, u) && cont_ok(1, p_cont(sv, lo + u))));
            assert(bit(m1, u) == (lo + u < hi && pre_cond(sv, ps, 1, lo + u)));
            if q <= u { assert(!bit(m1, u)); }
        }
        assert forall|u: u64| u < 64 implies #[trigger] bit(r2, u) == (64 * w + u < n_p(sv) && pcond(sv, ps, 2, 64 * w + u)) by {
            assert(bit(r2, u) == (u < q && bit(m2, u) && cont_ok(2, p_cont(sv, lo + u))));
            assert(bit(m2, u) == (lo + u < hi && pre_cond(sv, ps, 2, lo + u)));
            if q <= u { assert(!bit(m2, u)); }
        }
    }
    (r0, r1, r2)
}

/// The result word `rk` of branch `k` holds, below bit `q`, the rows of `mk` whose container is one of the branch's.
pub open spec fn res_ok(rk: u64, mk: u64, k: int, lo: int, q: int, sv: StoresView) -> bool {
    forall|u: u64| u < 64 ==> #[trigger] bit(rk, u) == (u < q && bit(mk, u) && cont_ok(k, p_cont(sv, lo + u)))
}

/// One step of the container test: row `lo + t`, the next row with a size and brand bit, for branch `k`.
fn cont_bit(c: &PartCols, k: usize, lo: usize, t: u64, mk: u64, rk: u64, Ghost(q): Ghost<int>, Ghost(sv): Ghost<StoresView>)
    -> (r: u64)
    requires
        part_cols_ok(*c, sv), k < 3, t < 64, q <= t, bit(mk, t) ==> lo + t < c.np,
        res_ok(rk, mk, k as int, lo as int, q, sv),
        forall|u: u64| q <= u < t ==> !#[trigger] bit(mk, u),
    ensures res_ok(r, mk, k as int, lo as int, t + 1, sv),
    no_unwind
{
    let x: u64 = if (mk >> t) & 1u64 == 1u64 && cont_in(c, lo + t as usize, k, Ghost(sv)) { 1 } else { 0 };
    let r = rk | (x << t);
    proof {
        assert(!bit(rk, t));
        assert forall|u: u64| u < 64 implies #[trigger] bit(r, u) == (u < t + 1 && bit(mk, u) && cont_ok(k as int, p_cont(sv, lo + u))) by {
            lemma_bit_set(rk, x, t, u);
        }
    }
    r
}

// ------------------------------------------------------------------------------------------------ one task

/// Some key among the first `n` of `keys` is `x`.
pub open spec fn listed(keys: Seq<i64>, n: int, x: i64) -> bool {
    exists|i: int| 0 <= i < n && #[trigger] keys[i] == x
}

/// A listed key stays listed when the list grows and keeps its first `n0` keys.
pub proof fn lemma_listed_grow(k0: Seq<i64>, n0: int, k1: Seq<i64>, n1: int, x: i64)
    requires listed(k0, n0, x), n0 <= n1, forall|i: int| 0 <= i < n0 ==> #[trigger] k1[i] == k0[i],
    ensures listed(k1, n1, x),
{
    let i = choose|i: int| 0 <= i < n0 && #[trigger] k0[i] == x;
    assert(k1[i] == x);
}

/// The first `n` keys and codes of a part task: each key with its (nonzero) branch code, and every part row of
/// `lo .. hi` satisfying some branch has its key listed (opaque: revealed where a list is written or read).
#[verifier::opaque]
pub open spec fn plist_ok(keys: Seq<i64>, codes: Seq<u8>, n: int, sv: StoresView, ps: Seq<Literal>, lo: int, hi: int) -> bool {
    &&& 0 <= n <= keys.len() && codes.len() == keys.len()
    &&& forall|i: int| 0 <= i < n ==> #[trigger] codes[i] == code(sv, ps, keys[i]) && codes[i] != 0u8
    &&& forall|a: int| lo <= a < hi && #[trigger] (anyp(sv, ps))(a) ==> listed(keys, n, p_key(sv)[a])
}

/// An empty list covers an empty range of rows.
pub proof fn lemma_plist_empty(keys: Seq<i64>, codes: Seq<u8>, sv: StoresView, ps: Seq<Literal>, lo: int)
    requires codes.len() == keys.len(),
    ensures plist_ok(keys, codes, 0, sv, ps, lo, lo),
{
    reveal(plist_ok);
}

/// A list covering `lo .. hi` covers `lo .. hi2` when no row of `hi .. hi2` satisfies a branch.
pub proof fn lemma_plist_extend(keys: Seq<i64>, codes: Seq<u8>, n: int, sv: StoresView, ps: Seq<Literal>, lo: int,
    hi: int, hi2: int)
    requires
        plist_ok(keys, codes, n, sv, ps, lo, hi), hi <= hi2,
        forall|a: int| hi <= a < hi2 ==> !#[trigger] (anyp(sv, ps))(a),
    ensures plist_ok(keys, codes, n, sv, ps, lo, hi2),
{
    reveal(plist_ok);
}

/// Writes the key and branch code of part row `r` (which satisfies some branch) at `keys[k]`, `codes[k]`: the list
/// then covers the rows up to `r` when it covered those before `from` and none of `from .. r` satisfies a branch.
fn put_key(c: &PartCols, keys: &mut Vec<i64>, codes: &mut Vec<u8>, k: usize, r: usize, b0: bool, b1: bool, b2: bool,
    Ghost(lo): Ghost<int>, Ghost(from): Ghost<int>, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    requires
        part_cols_ok(*c, sv), model_ok(sv), r < c.np, k < old(keys)@.len(), lo <= from <= r,
        b0 == pcond(sv, ps, 0, r as int), b1 == pcond(sv, ps, 1, r as int), b2 == pcond(sv, ps, 2, r as int),
        b0 || b1 || b2,
        plist_ok(old(keys)@, old(codes)@, k as int, sv, ps, lo, from),
        forall|a: int| from <= a < r ==> !#[trigger] (anyp(sv, ps))(a),
    ensures
        final(keys)@.len() == old(keys)@.len(),
        plist_ok(final(keys)@, final(codes)@, k + 1, sv, ps, lo, r + 1),
    no_unwind
{
    reveal(plist_ok);
    let ghost p = anyp(sv, ps);
    let cd: u8 = (if b0 { 1u8 } else { 0u8 }) | (if b1 { 2u8 } else { 0u8 }) | (if b2 { 4u8 } else { 0u8 });
    let key = c.key[r];
    let ghost (k0, c0) = (keys@, codes@);
    keys[k] = key;
    codes[k] = cd;
    proof {
        lemma_kbit_row(sv, ps, 0, r as int);
        lemma_kbit_row(sv, ps, 1, r as int);
        lemma_kbit_row(sv, ps, 2, r as int);
        lemma_code3(b0, b1, b2);
        assert(cd == code(sv, ps, key));
        assert forall|i: int| 0 <= i < k + 1 implies #[trigger] codes@[i] == code(sv, ps, keys@[i]) && codes@[i] != 0u8 by {
            if i < k { assert(codes@[i] == c0[i] && keys@[i] == k0[i]); }
        }
        assert forall|a: int| lo <= a < r + 1 && #[trigger] p(a) implies listed(keys@, k + 1, p_key(sv)[a]) by {
            if a < from {
                lemma_listed_grow(k0, k as int, keys@, k + 1, p_key(sv)[a]);
            } else {
                assert(a == r);
                assert(keys@[k as int] == p_key(sv)[a]);
            }
        }
    }
}

/// Lists the key and branch code of every row of word `w` with a branch bit (`r0`, `r1`, `r2`: the word's branch
/// words) at `keys[n..]`, `codes[n..]`; returns the new count.
fn word_keys(c: &PartCols, table: &[u8; 64], w: usize, r0: u64, r1: u64, r2: u64, keys: &mut Vec<i64>,
    codes: &mut Vec<u8>, n: usize, Ghost(lo): Ghost<int>, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (n2: usize)
    requires
        part_cols_ok(*c, sv), model_ok(sv), table@.len() == 64, 64 * w < c.np, lo <= 64 * w,
        forall|u: u64| u < 64 ==> #[trigger] bit(r0, u) == (64 * w + u < n_p(sv) && pcond(sv, ps, 0, 64 * w + u)),
        forall|u: u64| u < 64 ==> #[trigger] bit(r1, u) == (64 * w + u < n_p(sv) && pcond(sv, ps, 1, 64 * w + u)),
        forall|u: u64| u < 64 ==> #[trigger] bit(r2, u) == (64 * w + u < n_p(sv) && pcond(sv, ps, 2, 64 * w + u)),
        n + 64 <= old(keys)@.len(),
        plist_ok(old(keys)@, old(codes)@, n as int, sv, ps, lo, 64 * w),
    ensures
        final(keys)@.len() == old(keys)@.len(),
        n <= n2 <= n + 64,
        plist_ok(final(keys)@, final(codes)@, n2 as int, sv, ps, lo, 64 * w + 64),
    no_unwind
{
    let ghost p = anyp(sv, ps);
    // the buffer's length is a `usize`
    let cap = keys.len();
    let mut m = r0 | r1 | r2;
    let mut k = n;
    proof {
        assert forall|u: u64| u < 64 implies #[trigger] bit(m, u) == p(64 * w + u) by {
            lemma_bit_or3(r0, r1, r2, u);
        }
    }
    let ghost mut q: int = 0;
    while m != 0
        invariant
            part_cols_ok(*c, sv), model_ok(sv), table@.len() == 64, 64 * w < c.np, lo <= 64 * w, p == anyp(sv, ps),
            forall|u: u64| u < 64 ==> #[trigger] bit(r0, u) == (64 * w + u < n_p(sv) && pcond(sv, ps, 0, 64 * w + u)),
            forall|u: u64| u < 64 ==> #[trigger] bit(r1, u) == (64 * w + u < n_p(sv) && pcond(sv, ps, 1, 64 * w + u)),
            forall|u: u64| u < 64 ==> #[trigger] bit(r2, u) == (64 * w + u < n_p(sv) && pcond(sv, ps, 2, 64 * w + u)),
            0 <= q <= 64, n <= k <= n + q, n + 64 <= keys@.len(), keys@.len() == old(keys)@.len(), n + 64 <= usize::MAX,
            forall|u: u64| u < 64 ==> #[trigger] bit(m, u) == (q <= u && p(64 * w + u)),
            plist_ok(keys@, codes@, k as int, sv, ps, lo, 64 * w + q),
        decreases 64 - q,
    {
        proof { lemma_first_bit(m); }
        let t = tz64(m, table) as u64;
        let ghost m1 = m;
        m = m & (m - 1);
        proof {
            assert(bit(m1, t));
            assert(m1 - 1 == sub(m1, 1));
            assert forall|u: u64| u < 64 implies #[trigger] bit(m, u) == (t + 1 <= u && p(64 * w + u)) by {
                lemma_clear_lowest(m1, t, u);
            }
            assert(q <= t && t < 64);
            assert forall|a: int| 64 * w + q <= a < 64 * w + t implies !#[trigger] p(a) by {
                let u = (a - 64 * w) as u64;
                assert(!bit(m1, u));
            }
        }
        let r = 64 * w + t as usize;
        let b0 = (r0 >> t) & 1u64 == 1u64;
        let b1 = (r1 >> t) & 1u64 == 1u64;
        let b2 = (r2 >> t) & 1u64 == 1u64;
        proof {
            assert(b0 == bit(r0, t) && b1 == bit(r1, t) && b2 == bit(r2, t));
            assert(r as int == 64 * w + t);
            assert(p(r as int));
        }
        assert(k < n + 64);
        put_key(c, keys, codes, k, r, b0, b1, b2, Ghost(lo), Ghost(64 * w + q), Ghost(sv), Ghost(ps));
        k = k + 1;
        proof { q = t + 1; }
    }
    proof {
        assert forall|a: int| 64 * w + q <= a < 64 * w + 64 implies !#[trigger] p(a) by {
            let u = (a - 64 * w) as u64;
            lemma_bit_zero(u);
            assert(!bit(m, u));
        }
        lemma_plist_extend(keys@, codes@, k as int, sv, ps, lo, 64 * w + q, 64 * w + 64);
    }
    k
}

/// A part task's output: the keys and branch codes of its rows with a branch bit, the first `n` of the buffers;
/// `full`: the buffers filled up before the task's last word (the list is then incomplete).
pub struct PartOut {
    pub keys: Vec<i64>,
    pub codes: Vec<u8>,
    pub n: usize,
    pub full: bool,
}

/// One task: the words `w_lo..w_hi` and its key and code buffers of `cap` entries (allocated by the caller: a worker
/// does not allocate); `fast`: every brand parameter has 8 bytes.
pub struct PartTask {
    pub cols: PartCols,
    pub bind: Bind,
    pub w_lo: usize,
    pub w_hi: usize,
    pub fast: bool,
    pub keys: Vec<i64>,
    pub codes: Vec<u8>,
    pub cap: usize,
    pub sv: Ghost<StoresView>,
    pub ps: Ghost<Seq<Literal>>,
}

/// The output of a task covering the words `w_lo .. w_hi` (complete unless `full`).
pub open spec fn pout_ok(o: PartOut, sv: StoresView, ps: Seq<Literal>, w_lo: int, w_hi: int) -> bool {
    !o.full ==> plist_ok(o.keys@, o.codes@, o.n as int, sv, ps, 64 * w_lo, 64 * w_hi)
}

impl WorkerTask for PartTask {
    type Output = PartOut;

    open spec fn pre(&self) -> bool {
        &&& part_cols_ok(self.cols, self.sv@)
        &&& model_ok(self.sv@)
        &&& bind_ok(self.bind, self.ps@)
        &&& self.w_lo <= self.w_hi
        &&& 64 * self.w_hi <= self.cols.np + 63
        &&& self.keys@.len() == self.cap && self.codes@.len() == self.cap
        &&& self.fast ==> self.bind.e0 && self.bind.e1 && self.bind.e2
    }

    open spec fn post(&self, out: PartOut) -> bool {
        pout_ok(out, self.sv@, self.ps@, self.w_lo as int, self.w_hi as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.w_lo as u64, self.w_hi as u64)
    }

    fn run(self) -> (out: PartOut) {
        let c = self.cols;
        let x = self.bind;
        let fast = self.fast;
        let cap = self.cap;
        let ghost sv = self.sv@;
        let ghost ps = self.ps@;
        let w_lo = self.w_lo;
        let w_hi = self.w_hi;
        let mut keys = self.keys;
        let mut codes = self.codes;
        let ghost lo = 64 * w_lo as int;
        let table = tz_table_array();
        let mut n: usize = 0;
        let mut w = w_lo;
        proof { lemma_plist_empty(keys@, codes@, sv, ps, lo); }
        while w < w_hi
            invariant
                part_cols_ok(c, sv), model_ok(sv), bind_ok(x, ps), w_lo <= w <= w_hi, 64 * w_hi <= c.np + 63,
                table@.len() == 64, lo == 64 * w_lo, fast ==> x.e0 && x.e1 && x.e2,
                keys@.len() == cap, codes@.len() == cap, n <= 64 * (w - w_lo),
                plist_ok(keys@, codes@, n as int, sv, ps, lo, 64 * w),
            decreases w_hi - w,
        {
            proof { reveal(plist_ok); }
            if cap - n < 64 {
                // the buffers may not hold the next word's keys
                return PartOut { keys, codes, n, full: true };
            }
            proof { assert(64 * w < c.np); }
            let (r0, r1, r2) = part_word(&c, &x, &table, w, fast, Ghost(sv), Ghost(ps));
            n = word_keys(&c, &table, w, r0, r1, r2, &mut keys, &mut codes, n, Ghost(lo), Ghost(sv), Ghost(ps));
            w = w + 1;
        }
        PartOut { keys, codes, n, full: false }
    }
}

// ------------------------------------------------------------------------------------------------ the pass

/// Start of part `k` when `n` items are split into `w` parts: `k * (n / w) + min(k, n % w)`.
pub open spec fn split_at(n: int, w: int, k: int) -> int {
    k * (n / w) + if k < n % w { k } else { n % w }
}

/// The part boundaries are non-decreasing and end at `n`.
pub proof fn lemma_split(n: int, w: int, k: int)
    requires 0 <= n, 1 <= w, 0 <= k < w,
    ensures
        split_at(n, w, k + 1) == split_at(n, w, k) + n / w + if k < n % w { 1int } else { 0int },
        0 <= split_at(n, w, k) <= split_at(n, w, k + 1) <= n,
        split_at(n, w, 0) == 0,
        split_at(n, w, w) == n,
{
    let (q, r) = (n / w, n % w);
    assert(n == w * q + r && 0 <= r < w && 0 <= q) by (nonlinear_arith) requires q == n / w, r == n % w, 0 <= n, 1 <= w;
    assert((k + 1) * q == k * q + q) by (nonlinear_arith);
    assert(w * q == q * w) by (nonlinear_arith);
    assert(0 <= k * q) by (nonlinear_arith) requires 0 <= k, 0 <= q;
    assert((k + 1) * q <= w * q) by (nonlinear_arith) requires k + 1 <= w, 0 <= q;
    assert(0 * q == 0);
}

/// The outputs of the part pass: one key list per task, task `t` covering the words
/// `split_at(nw, nt, t) .. split_at(nw, nt, t + 1)` of the `nw = nwords(np)` words (complete unless `full`).
pub open spec fn ptasks_ok(outs: Seq<PartOut>, nt: int, sv: StoresView, ps: Seq<Literal>) -> bool {
    let nw = nwords(n_p(sv) as int);
    &&& 1 <= nt
    &&& outs.len() == nt
    &&& forall|t: int| 0 <= t < nt ==> pout_ok(#[trigger] outs[t], sv, ps, split_at(nw, nt, t), split_at(nw, nt, t + 1))
}

/// No task's list is incomplete.
pub open spec fn none_full(outs: Seq<PartOut>) -> bool {
    forall|t: int| 0 <= t < outs.len() ==> !(#[trigger] outs[t]).full
}

/// Some task's buffers filled up.
pub fn any_full(outs: &Vec<PartOut>) -> (b: bool)
    ensures b == !none_full(outs@),
{
    let mut t: usize = 0;
    while t < outs.len()
        invariant t <= outs@.len(), forall|u: int| 0 <= u < t ==> !(#[trigger] outs@[u]).full,
        decreases outs@.len() - t,
    {
        if outs[t].full {
            return true;
        }
        t = t + 1;
    }
    false
}

/// The part pass: the keys and branch codes of the part rows satisfying some branch, one list per task (`nt`
/// tasks). A task's buffers hold one key per 64 rows (plus 64): far more than TPC-H's ~0.24% of qualifying rows, and
/// small enough that their zeroing costs little; a task whose buffers fill up reports `full` (the caller then lists
/// the keys on its own thread, `serial_keys`).
pub fn part_pass(pc: PartCols, x: Bind, workers: usize, dispatch: &mut Dispatch, Ghost(sv): Ghost<StoresView>,
    Ghost(ps): Ghost<Seq<Literal>>) -> (r: Result<(Vec<PartOut>, usize), WorkerFailure>)
    requires part_cols_ok(pc, sv), model_ok(sv), bind_ok(x, ps), 1 <= workers <= MAX_WORKERS,
    ensures r matches Ok((outs, nt)) ==> ptasks_ok(outs@, nt as int, sv, ps),
{
    let nw = pc.np / 64 + if pc.np % 64 != 0 { 1 } else { 0 };
    let fast = x.e0 && x.e1 && x.e2;
    let q = nw / workers;
    let rm = nw % workers;
    let mut tasks: Vec<PartTask> = Vec::new();
    let mut w_lo: usize = 0;
    let mut k: usize = 0;
    while k < workers
        invariant
            part_cols_ok(pc, sv), model_ok(sv), bind_ok(x, ps), 1 <= workers <= MAX_WORKERS, k <= workers,
            nw == nwords(pc.np as int), q == nw / workers, rm == nw % workers,
            fast ==> x.e0 && x.e1 && x.e2,
            tasks@.len() == k,
            w_lo == split_at(nw as int, workers as int, k as int),
            forall|t: int| 0 <= t < k ==> (#[trigger] tasks@[t]).pre()
                && tasks@[t].sv@ == sv && tasks@[t].ps@ == ps
                && tasks@[t].w_lo == split_at(nw as int, workers as int, t)
                && tasks@[t].w_hi == split_at(nw as int, workers as int, t + 1),
        decreases workers - k,
    {
        proof { lemma_split(nw as int, workers as int, k as int); }
        let w_hi = w_lo + q + if k < rm { 1 } else { 0 };
        assert(64 * w_hi <= pc.np + 63);
        let cap = (w_hi - w_lo) + 64;
        let task = PartTask { cols: pc, bind: x, w_lo, w_hi, fast, keys: vec![0i64; cap], codes: vec![0u8; cap], cap,
            sv: Ghost(sv), ps: Ghost(ps) };
        tasks.push(task);
        w_lo = w_hi;
        k = k + 1;
    }
    let ghost tasks0 = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => { return Err(e); },
    };
    proof {
        assert forall|u: int| 0 <= u < workers implies pout_ok(#[trigger] outs@[u], sv, ps,
            split_at(nw as int, workers as int, u), split_at(nw as int, workers as int, u + 1)) by {
            assert(tasks0[u].post(outs@[u]));
        }
    }
    Ok((outs, workers))
}

/// The keys and branch codes of the part rows satisfying some branch, word by word on the calling thread (the
/// fallback when some task's buffers filled up).
pub fn serial_keys(pc: &PartCols, x: &Bind, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: (Vec<i64>, Vec<u8>))
    requires part_cols_ok(*pc, sv), model_ok(sv), bind_ok(*x, ps),
    ensures keys_ok(r.0@, r.1@, sv, ps),
{
    let ghost p = anyp(sv, ps);
    let nw = pc.np / 64 + if pc.np % 64 != 0 { 1 } else { 0 };
    let fast = x.e0 && x.e1 && x.e2;
    let table = tz_table_array();
    let mut keys: Vec<i64> = Vec::new();
    let mut codes: Vec<u8> = Vec::new();
    let mut kb: Vec<i64> = vec![0i64; 64];
    let mut cb: Vec<u8> = vec![0u8; 64];
    let mut w: usize = 0;
    while w < nw
        invariant
            part_cols_ok(*pc, sv), model_ok(sv), bind_ok(*x, ps), nw == nwords(pc.np as int), w <= nw,
            fast ==> x.e0 && x.e1 && x.e2, table@.len() == 64, p == anyp(sv, ps),
            kb@.len() == 64, cb@.len() == 64, keys@.len() == codes@.len(),
            forall|i: int| 0 <= i < keys@.len() ==> #[trigger] codes@[i] == code(sv, ps, keys@[i]) && codes@[i] != 0u8,
            forall|a: int| 0 <= a < 64 * w && #[trigger] p(a) ==> listed(keys@, keys@.len() as int, p_key(sv)[a]),
        decreases nw - w,
    {
        proof { assert(64 * w < pc.np); }
        let (r0, r1, r2) = part_word(pc, x, &table, w, fast, Ghost(sv), Ghost(ps));
        proof { lemma_plist_empty(kb@, cb@, sv, ps, 64 * w as int); }
        let n = word_keys(pc, &table, w, r0, r1, r2, &mut kb, &mut cb, 0, Ghost(64 * w as int), Ghost(sv), Ghost(ps));
        proof { reveal(plist_ok); }
        let base = keys.len();
        let ghost k0 = keys@;
        let mut i: usize = 0;
        while i < n
            invariant
                plist_ok(kb@, cb@, n as int, sv, ps, 64 * w as int, 64 * w + 64), i <= n,
                n <= kb@.len(), cb@.len() == kb@.len(),
                forall|j: int| 0 <= j < n ==> #[trigger] cb@[j] == code(sv, ps, kb@[j]) && cb@[j] != 0u8,
                keys@.len() == base + i, codes@.len() == base + i, base == k0.len(),
                forall|j: int| 0 <= j < base ==> #[trigger] keys@[j] == k0[j],
                forall|j: int| 0 <= j < i ==> #[trigger] keys@[base + j] == kb@[j],
                forall|j: int| 0 <= j < keys@.len() ==> #[trigger] codes@[j] == code(sv, ps, keys@[j]) && codes@[j] != 0u8,
            decreases n - i,
        {
            let ghost (k1, c1) = (keys@, codes@);
            keys.push(kb[i]);
            codes.push(cb[i]);
            proof {
                assert forall|j: int| 0 <= j < keys@.len() implies #[trigger] codes@[j] == code(sv, ps, keys@[j]) && codes@[j] != 0u8 by {
                    if j < k1.len() { assert(codes@[j] == c1[j] && keys@[j] == k1[j]); }
                }
                assert forall|j: int| 0 <= j < i + 1 implies #[trigger] keys@[base + j] == kb@[j] by {
                    if j < i { assert(keys@[base + j] == k1[base + j]); }
                }
                assert forall|j: int| 0 <= j < base implies #[trigger] keys@[j] == k0[j] by {
                    assert(keys@[j] == k1[j]);
                }
            }
            i = i + 1;
        }
        proof {
            reveal(plist_ok);
            assert forall|a: int| 0 <= a < 64 * (w + 1) && #[trigger] p(a) implies listed(keys@, keys@.len() as int, p_key(sv)[a]) by {
                if a < 64 * w {
                    lemma_listed_grow(k0, k0.len() as int, keys@, keys@.len() as int, p_key(sv)[a]);
                } else {
                    let j = choose|j: int| 0 <= j < n && #[trigger] kb@[j] == p_key(sv)[a];
                    assert(keys@[base + j] == p_key(sv)[a]);
                }
            }
        }
        w = w + 1;
    }
    proof { lemma_keys_complete(keys@, codes@, sv, ps, 64 * nw); }
    (keys, codes)
}

} // verus!
