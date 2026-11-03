//! Q8 scan kernel over the column model (`super::model`). A scan task covers stored lineitem rows `[l0, l1)` block by
//! block (at most `BLK` rows inside one lineitem group, so one base per column):
//! 1. coarse part filter: the rows whose l_partkey lies in the part bitmap's range and whose coarse bit (one per 8
//!    keys) is set, collected branch-free into `cand1` (offsets in the block);
//! 2. fine part filter: of those, the rows whose exact bit is set (`pm`), collected into `cand2`;
//! 3. per remaining row: its order (`rpos`, by a forward cursor when the lineitem rows follow the orders, else by the
//!    orders key index), the order date window, the customer and its nation's region, the supplier and its nation,
//!    then the per-year accumulators (`Acc`).
//! Without a part bitmap (`use_bits` false) every row is a candidate and the exact filter looks the part up by key.
//! Accumulation is exact: each year's absolute volume mass is checked against `i128::MAX` (it bounds every sum); a
//! task whose mass would pass it stops and reports `ovf`, which proves the range's mass exceeds `i128::MAX`.
use vstd::prelude::*;
use crate::gendb_entry::parallel::WorkerTask;
use super::model::*;
use super::join::LHit;
use super::sql::{lemma_years, year_of, d95, d96, d96e};
use std::sync::Arc;

verus! {

/// Lineitem rows per scan block.
pub const BLK: usize = 4096;

/// Nation keys with a direct status entry.
pub const NK: usize = 256;

// ------------------------------------------------------------------------------------------------ bit helpers

/// A signed offset is in `[0, n)` exactly when its unsigned reinterpretation is below `n <= 2^32`.
pub proof fn lemma_unsigned_range(x: i64, n: u64)
    requires n <= 0x100_0000_0000,
    ensures ((x as u64) < n) == (0 <= x && x < n as int), 0 <= x ==> (x as u64) as int == x as int,
{
    assert(((x as u64) < n) == (0 <= x && (x as u64) < n)) by (bit_vector) requires n <= 0x100_0000_0000;
}

/// Bit `i` of a word array.
pub open spec fn bit_at(ws: Seq<u64>, i: int) -> bool {
    ((ws[i / 64] >> ((i % 64) as u64)) & 1u64) == 1u64
}

pub proof fn lemma_shr3(x: u64)
    ensures x >> 3 == x / 8,
{
    assert(x >> 3 == x / 8) by (bit_vector);
}

pub proof fn lemma_shr6(x: u64)
    ensures x >> 6 == x / 64,
{
    assert(x >> 6 == x / 64) by (bit_vector);
}

pub proof fn lemma_and63(x: u64)
    ensures x & 63 == x % 64,
{
    assert(x & 63 == x % 64) by (bit_vector);
}

pub proof fn lemma_bit01(w: u64, s: u64)
    ensures (w >> s) & 1 == 0 || (w >> s) & 1 == 1,
{
    assert((w >> s) & 1 == 0 || (w >> s) & 1 == 1) by (bit_vector);
}

/// Bit `x` of `ws` (`x / 64` inside `ws`).
#[inline(always)]
pub fn test_bit(ws: &Vec<u64>, x: u64) -> (b: bool)
    requires (x / 64) < ws@.len(),
    ensures b == bit_at(ws@, x as int),
    no_unwind
{
    let nw = ws.len();
    proof {
        lemma_shr6(x);
        lemma_and63(x);
        assert((x & 63) == ((x as int % 64) as u64));
        assert((x >> 6) as int == x as int / 64);
        assert((x >> 6) as int <= usize::MAX);
        assert(((x >> 6) as usize) as int == x as int / 64);
    }
    let w = ws[(x >> 6) as usize];
    let s = x & 63;
    proof {
        assert(w == ws@[x as int / 64]);
    }
    ((w >> s) & 1) == 1
}

// ------------------------------------------------------------------------------------------------ the part filter

/// The part filter: bitmaps over the part keys `[pk_lo, pk_lo + nbits)` (fine: one bit per key; coarse: one bit per 8
/// keys), or (without bitmaps) a lookup of the part by key; `t` is the dictionary index of the type `$3` (`has_t`
/// false when no dictionary entry is `$3`).
pub struct PFilter {
    pub use_bits: bool,
    pub bits: Vec<u64>,
    pub coarse: Vec<u64>,
    pub nbits: u64,
    /// Key offsets at or above `clamp` (>= `nbits`) are tested at coarse bit `clamp / 8`, which is always clear.
    pub clamp: u64,
    pub pk_lo: i64,
    pub n_p: usize,
    pub bs_p: usize,
    pub pk_c: &'static [u32],
    pub pk_b: &'static [i64],
    pub pt_c: &'static [u8],
    pub pt_b: &'static [u64],
    pub p_kind: u64,
    pub t: u64,
    pub has_t: bool,
    pub e32: &'static [u32],
    pub e64: &'static [u64],
}

pub open spec fn pkey(f: PFilter, i: int) -> int { f.pk_b@[i / f.bs_p as int] + f.pk_c@[i] }
pub open spec fn ptype(f: PFilter, i: int) -> int { f.pt_b@[i / f.bs_p as int] + f.pt_c@[i] }

/// Some part row has key `v` and type `$3`.
pub open spec fn pmatch(f: PFilter, v: int) -> bool {
    f.has_t && exists|i: int| 0 <= i < f.n_p && #[trigger] pkey(f, i) == v && ptype(f, i) == f.t
}

/// The filter as a predicate.
pub open spec fn pm_of(f: PFilter) -> spec_fn(int) -> bool {
    |v: int| pmatch(f, v)
}

/// Bitmap bound: 2^32 keys.
pub open spec fn bits_cap() -> int { 0x1_0000_0000 }

pub open spec fn pf_ok(f: PFilter) -> bool {
    &&& f.bs_p >= 1
    &&& f.pk_c@.len() == f.n_p && f.pt_c@.len() == f.n_p && f.pt_b@.len() == f.pk_b@.len()
    &&& f.pk_b@.len() * f.bs_p >= f.n_p
    &&& f.e32@ == Seq::<u32>::empty() && f.e64@ == Seq::<u64>::empty()
    &&& crate::stores::custpart::interface::common::keyidx::keyidx_ok(f.pk_c@, f.pk_b@, Seq::<u32>::empty(),
            Seq::<u64>::empty(), f.bs_p as int, f.p_kind, f.n_p as int)
    &&& forall|i: int| 0 <= i < f.n_p ==> in_i64(#[trigger] pkey(f, i))
    &&& forall|a: int, b: int| 0 <= a < f.n_p && 0 <= b < f.n_p && a != b ==> #[trigger] pkey(f, a) != #[trigger] pkey(f, b)
    &&& f.use_bits ==> {
        &&& 1 <= f.nbits <= bits_cap()
        &&& f.bits@.len() * 64 >= f.nbits && f.coarse@.len() * 512 >= f.nbits
        &&& f.coarse@.len() >= 1
        &&& forall|i: int| 0 <= i < f.nbits ==> #[trigger] bit_at(f.bits@, i) == pmatch(f, f.pk_lo + i)
        &&& forall|i: int| 0 <= i < f.nbits && #[trigger] bit_at(f.bits@, i) ==> bit_at(f.coarse@, i / 8)
        &&& forall|v: int| #[trigger] pmatch(f, v) ==> f.pk_lo <= v < f.pk_lo + f.nbits
    }
}

/// The coarse padding bit: key offsets clamped to `clamp` land on coarse bit `clamp / 8`, which is clear, so the
/// coarse stage needs no separate range test.
pub open spec fn pad_ok(f: PFilter) -> bool {
    f.use_bits ==> {
        &&& f.nbits <= f.clamp <= 0x2_0000_0000
        &&& (f.clamp as int / 8) / 64 < f.coarse@.len()
        &&& !bit_at(f.coarse@, f.clamp as int / 8)
    }
}

/// The part key `v` lies below the clamp of the bitmap range.
pub open spec fn in_clamp(f: PFilter, v: int) -> bool {
    f.pk_lo <= v < f.pk_lo + f.clamp
}

/// The exact filter by key lookup.
pub fn pmatch_lookup(f: &PFilter, v: i64) -> (b: bool)
    requires pf_ok(*f),
    ensures b == pmatch(*f, v as int),
    no_unwind
{
    if !f.has_t {
        return false;
    }
    match crate::stores::custpart::interface::common::keyidx::key_find(f.pk_c, f.pk_b, f.e32, f.e64, f.bs_p, f.p_kind, f.n_p, v as i128) {
        Some(i) => {
            proof {
                crate::stores::custpart::interface::common::read::lemma_div_lt(i as int, f.bs_p as int, f.pk_b@.len() as int);
                assert(pkey(*f, i as int) == v);
                if pmatch(*f, v as int) {
                    let i2 = choose|i2: int| 0 <= i2 < f.n_p && #[trigger] pkey(*f, i2) == v && ptype(*f, i2) == f.t;
                    assert(i2 == i);
                }
            }
            f.pt_b[i / f.bs_p] as u128 + f.pt_c[i] as u128 == f.t as u128
        },
        None => {
            proof {
                if pmatch(*f, v as int) {
                    let i2 = choose|i2: int| 0 <= i2 < f.n_p && #[trigger] pkey(*f, i2) == v && ptype(*f, i2) == f.t;
                    assert(crate::stores::custpart::interface::common::keyidx::fkey(f.pk_c@, f.pk_b@, f.bs_p as int, i2) != v);
                }
            }
            false
        },
    }
}

// ------------------------------------------------------------------------------------------------ nation statuses

/// Nation statuses: by key for keys `[0, NK)` (`ex`, `reg`, `name`), and per nation row for the other keys.
pub struct NTab {
    pub ex: Vec<bool>,
    pub reg: Vec<bool>,
    pub name: Vec<bool>,
    pub keys: Vec<i64>,
    pub rreg: Vec<bool>,
    pub rname: Vec<bool>,
    pub cbits: Vec<u64>,
}

pub open spec fn nt_view(t: NTab) -> NStat {
    NStat { keys: t.keys@, reg: t.rreg@, name: t.rname@ }
}

/// Name `$1` of the nation row with key `k`.
pub open spec fn nname(ns: NStat, k: int) -> bool {
    match nfind(ns, k) {
        Some(i) => ns.name[i],
        None => false,
    }
}

pub open spec fn ntab_ok(t: NTab) -> bool {
    &&& t.ex@.len() == NK && t.reg@.len() == NK && t.name@.len() == NK
    &&& nstat_wf(nt_view(t))
    &&& forall|k: int| 0 <= k < NK ==> #[trigger] t.ex@[k] == nfind(nt_view(t), k) is Some
    &&& forall|k: int| 0 <= k < NK ==> #[trigger] t.reg@[k] == nreg(nt_view(t), k)
    &&& forall|k: int| 0 <= k < NK ==> #[trigger] t.name@[k] == nname(nt_view(t), k)
}

/// The nation of key `k`: whether it exists, whether its region is `$2`, whether its name is `$1`.
pub fn nat_lookup(t: &NTab, k: i64) -> (r: (bool, bool, bool))
    requires ntab_ok(*t),
    ensures
        r.0 == nfind(nt_view(*t), k as int) is Some,
        r.1 == nreg(nt_view(*t), k as int),
        r.2 == nname(nt_view(*t), k as int),
    no_unwind
{
    if 0 <= k && k < NK as i64 {
        return (t.ex[k as usize], t.reg[k as usize], t.name[k as usize]);
    }
    let n = t.keys.len();
    let mut i: usize = 0;
    while i < n
        invariant
            ntab_ok(*t),
            n == t.keys@.len(),
            i <= n,
            forall|q: int| 0 <= q < i ==> t.keys@[q] != k,
        decreases n - i,
    {
        if t.keys[i] == k {
            proof {
                let ns = nt_view(*t);
                assert(ns.keys[i as int] == k);
                let c = choose|c: int| 0 <= c < ns.keys.len() && #[trigger] ns.keys[c] == k as int;
                assert(c == i);
            }
            return (true, t.rreg[i], t.rname[i]);
        }
        i = i + 1;
    }
    (false, false, false)
}

// ------------------------------------------------------------------------------------------------ one row

/// `lc` after the part filter.
pub open spec fn lc2(m: Cols, ns: NStat, j: int) -> Option<LHit> {
    lc(m, |v: int| true, ns, j)
}

/// The contribution as the executable triple `(1996?, volume, nation $1?)`.
pub open spec fn hit_of(o: Option<(bool, i128, bool)>) -> Option<LHit> {
    match o {
        Some((b, v, h)) => Some(LHit { year: if b { 1996 } else { 1995 }, vol: v as int, hit: h }),
        None => None,
    }
}

pub proof fn lemma_div_below(j: int, bs: int, len: int)
    requires bs >= 1, 0 <= j < len * bs,
    ensures 0 <= j / bs < len,
{
    crate::stores::factsdir::interface::common::read::lemma_div_lt(j, bs, len);
}

/// The contribution of stored lineitem row `r` (group `g`) whose order is stored orders row `p` (group `gp`).
pub fn contrib(c: &Cols, nt: &NTab, r: usize, g: usize, p: usize, gp: usize) -> (out: Option<(bool, i128, bool)>)
    requires
        cols_ok(*c),
        ntab_ok(*nt),
        r < c.n_l,
        g == r / c.bs_l,
        p == rpos(*c, lk(*c, r as int)),
        p < c.n_o ==> gp == p / c.bs_o,
    ensures
        hit_of(out) == lc2(*c, nt_view(*nt), r as int),
        out matches Some((b, v, h)) ==> -0x1_0000_0000_0000_0000_0000_0000_0000 < v < 0x1_0000_0000_0000_0000_0000_0000_0000,
    no_unwind
{
    let ghost ns = nt_view(*nt);
    proof {
        lemma_rpos(*c, lk(*c, r as int));
    }
    if p >= c.n_o {
        return None;
    }
    proof {
        lemma_div_below(p as int, c.bs_o as int, c.ok_b@.len() as int);
        lemma_div_below(r as int, c.bs_l as int, c.lk_b@.len() as int);
        assert(in_i64(od(*c, p as int)) && in_i64(oc(*c, p as int)));
    }
    let d = c.od_b[gp] + c.od_c[p] as i64;
    if !(c.lo <= d && d <= c.hi) {
        return None;
    }
    let ckey = c.oc_b[gp] + c.oc_c[p] as i64;
    let gc = ckey as i128 - c.c_first as i128;
    let guess: usize = if 0 <= gc && gc < c.n_c as i128 { gc as usize } else { c.n_c };
    let ci = match crate::stores::custpart::interface::common::keyidx::key_find_guess(c.ck_c, c.ck_b, c.e32, c.e64, c.bs_c,
        c.c_kind, c.n_c, ckey as i128, guess) {
        Some(ci) => ci,
        None => {
            proof {
                assert forall|i: int| 0 <= i < c.n_c implies #[trigger] ck(*c, i) != ckey by {
                    assert(crate::stores::custpart::interface::common::keyidx::fkey(c.ck_c@, c.ck_b@, c.bs_c as int, i) != ckey);
                }
                assert(cfind(*c, ckey as int) is None);
            }
            return None;
        },
    };
    proof {
        assert(ck(*c, ci as int) == ckey);
        let c2 = choose|i: int| 0 <= i < c.n_c && #[trigger] ck(*c, i) == ckey as int;
        assert(c2 == ci);
        assert(cfind(*c, ckey as int) == Some(ci as int));
        lemma_div_below(ci as int, c.bs_c as int, c.ck_b@.len() as int);
        assert(in_i64(cn(*c, ci as int)));
    }
    let cnat = c.cn_b[ci / c.bs_c] + c.cn_c[ci] as i64;
    let (_, reg1, _) = nat_lookup(nt, cnat);
    if !reg1 {
        return None;
    }
    proof {
        assert(in_i64(ls(*c, r as int)));
    }
    let skey = c.ls_b[g] + c.ls_c[r] as i64;
    let gs = skey as i128 - c.s_first as i128;
    let sguess: usize = if 0 <= gs && gs < c.n_s as i128 { gs as usize } else { c.n_s };
    let si = match crate::stores::suppliers::interface::common::keyidx::key_find_guess(c.sk_c, c.sk_b, c.e32, c.e64, c.bs_s,
        c.s_kind, c.n_s, skey as i128, sguess) {
        Some(si) => si,
        None => {
            proof {
                assert forall|i: int| 0 <= i < c.n_s implies #[trigger] sk(*c, i) != skey by {
                    assert(crate::stores::suppliers::interface::common::keyidx::fkey(c.sk_c@, c.sk_b@, c.bs_s as int, i) != skey);
                }
                assert(sfind(*c, skey as int) is None);
            }
            return None;
        },
    };
    proof {
        assert(sk(*c, si as int) == skey);
        let s2 = choose|i: int| 0 <= i < c.n_s && #[trigger] sk(*c, i) == skey as int;
        assert(s2 == si);
        assert(sfind(*c, skey as int) == Some(si as int));
        lemma_div_below(si as int, c.bs_s as int, c.sk_b@.len() as int);
        assert(in_i64(sn(*c, si as int)));
    }
    let snat = c.sn_b[si / c.bs_s] + c.sn_c[si] as i64;
    let (ex2, _, name2) = nat_lookup(nt, snat);
    if !ex2 {
        return None;
    }
    proof {
        assert(coeff15(le(*c, r as int)) && coeff15(ld(*c, r as int)));
    }
    let ep = c.le_b[g] + c.le_c[r] as i64;
    let dc = c.ld_b[g] + c.ld_c[r] as i64;
    let f2 = 100 - dc as i128;
    proof {
        assert(-0x1_0000_0000_0000_0000_0000_0000_0000 < ep * f2 < 0x1_0000_0000_0000_0000_0000_0000_0000) by (nonlinear_arith)
            requires -1_000_000_000_000_000 < ep < 1_000_000_000_000_000, -1_000_000_000_000_000 + 100 < f2 < 1_000_000_000_000_000 + 100;
        lemma_years(d as int);
        assert(year_of(d as int) == if d < c.d96 { 1995int } else { 1996int });
    }
    let vol = ep as i128 * f2;
    proof {
        let ni = nfind(ns, snat as int)->Some_0;
        assert(nname(ns, snat as int) == ns.name[ni]);
    }
    Some((d >= c.d96, vol, name2))
}

// ------------------------------------------------------------------------------------------------ candidate lists

/// A candidate list of a block: strictly increasing offsets below `nb`.
pub open spec fn list_ok(l: Seq<int>, nb: int) -> bool {
    &&& forall|i: int| 0 <= i < l.len() ==> 0 <= #[trigger] l[i] < nb
    &&& forall|i: int, k: int| 0 <= i < k < l.len() ==> #[trigger] l[i] < #[trigger] l[k]
}

/// The executable list mirrors the ghost list.
pub open spec fn list_mirror(v: Seq<u16>, l: Seq<int>) -> bool {
    l.len() <= v.len() && forall|i: int| 0 <= i < l.len() ==> #[trigger] v[i] as int == l[i]
}

/// The part key of row `j + t` lies in the bitmap range.
pub open spec fn in_rng(f: PFilter, v: int) -> bool {
    f.pk_lo <= v < f.pk_lo + f.nbits
}

/// Coarse stage: every row of the block whose part may match, in order (bitmap mode: its key offset is below the
/// clamp and its coarse bit is set; lookup mode: every row). The offset is clamped to `clamp`, whose coarse bit is
/// clear (`pad_ok`), so one coarse test covers the range test too.
fn stage1(c: &Cols, f: &PFilter, cand: &mut Vec<u16>, j: usize, nb: usize, g: usize, off0: i64) -> (r: (usize, Ghost<Seq<int>>))
    requires
        cols_ok(*c),
        pf_ok(*f),
        pad_ok(*f),
        old(cand)@.len() == BLK,
        nb <= BLK,
        j + nb <= c.n_l,
        g * c.bs_l <= j, j + nb <= g * c.bs_l + c.bs_l,
        f.use_bits ==> off0 == c.lp_b@[g as int] - f.pk_lo,
        f.use_bits ==> -0x2_0000_0000 <= off0 <= 0x2_0000_0000,
        g < c.lp_b@.len(),
    ensures
        final(cand)@.len() == BLK,
        r.1@.len() == r.0,
        list_mirror(final(cand)@, r.1@),
        list_ok(r.1@, nb as int),
        f.use_bits ==> forall|i: int| 0 <= i < r.0 ==> in_clamp(*f, lp(*c, j + #[trigger] r.1@[i])),
        forall|t: int| 0 <= t < nb && pmatch(*f, lp(*c, j + t)) ==> #[trigger] r.1@.contains(t),
    no_unwind
{
    let ghost mut l: Seq<int> = Seq::empty();
    let mut n: usize = 0;
    let mut t: usize = 0;
    let use_bits = f.use_bits;
    let clamp = f.clamp;
    // The block's part keys as one slice (one bounds check per block, not per row).
    let (_, tail) = c.lp_c.split_at(j);
    let (lps, _) = tail.split_at(nb);
    proof {
        assert(lps@ =~= c.lp_c@.subrange(j as int, (j + nb) as int));
    }
    while t < nb
        invariant
            cols_ok(*c),
            pf_ok(*f),
            pad_ok(*f),
            lps@ == c.lp_c@.subrange(j as int, (j + nb) as int),
            use_bits == f.use_bits,
            clamp == f.clamp,
            cand@.len() == BLK,
            nb <= BLK,
            j + nb <= c.n_l,
            g * c.bs_l <= j, j + nb <= g * c.bs_l + c.bs_l,
            f.use_bits ==> off0 == c.lp_b@[g as int] - f.pk_lo,
            f.use_bits ==> -0x2_0000_0000 <= off0 <= 0x2_0000_0000,
            g < c.lp_b@.len(),
            n <= t <= nb,
            l.len() == n,
            list_mirror(cand@, l),
            list_ok(l, t as int),
            f.use_bits ==> forall|i: int| 0 <= i < n ==> in_clamp(*f, lp(*c, j + #[trigger] l[i])),
            forall|t2: int| 0 <= t2 < t && pmatch(*f, lp(*c, j + t2)) ==> #[trigger] l.contains(t2),
        decreases nb - t,
    {
        let r = j + t;
        let bit: usize = if use_bits {
            let offi: i64 = off0 + lps[t] as i64;
            // A negative offset wraps far above `clamp <= 2^33` and is clamped like a too large one.
            let offu: u64 = offi as u64;
            let cl: u64 = if offu < clamp { offu } else { clamp };
            let cb: u64 = cl >> 3;
            proof {
                assert(lps@[t as int] == c.lp_c@[r as int]);
                lemma_unsigned_range(offi, clamp);
                lemma_shr3(cl);
                lemma_div_group(r as int, c.bs_l as int, g as int);
                assert(lp(*c, r as int) == c.lp_b@[g as int] + c.lp_c@[r as int]);
                vstd::arithmetic::div_mod::lemma_div_is_ordered(cl as int, clamp as int, 8);
                vstd::arithmetic::div_mod::lemma_div_is_ordered(cb as int, clamp as int / 8, 64);
            }
            if test_bit(&f.coarse, cb) { 1 } else { 0 }
        } else {
            1
        };
        proof {
            let v = lp(*c, r as int);
            lemma_div_group(r as int, c.bs_l as int, g as int);
            if use_bits {
                let offi = off0 + c.lp_c@[r as int];
                assert(v - f.pk_lo == offi);
                // A clamped offset tests the clear padding bit.
                if bit == 1 && !(0 <= offi && offi < clamp) {
                    assert(false);
                }
                if pmatch(*f, v) {
                    let i = v - f.pk_lo;
                    assert(in_rng(*f, v));
                    assert(bit_at(f.bits@, i));
                    assert(bit_at(f.coarse@, i / 8));
                }
            }
        }
        cand[n] = t as u16;
        proof {
            let ghost l_old = l;
            if bit == 1 {
                l = l.push(t as int);
                assert forall|t2: int| 0 <= t2 < t + 1 && pmatch(*f, lp(*c, j + t2)) implies #[trigger] l.contains(t2) by {
                    if t2 < t {
                        assert(l_old.contains(t2));
                        let i = choose|i: int| 0 <= i < l_old.len() && l_old[i] == t2;
                        assert(l[i] == t2);
                    } else {
                        assert(l[l.len() - 1] == t2);
                    }
                }
            } else {
                assert forall|t2: int| 0 <= t2 < t + 1 && pmatch(*f, lp(*c, j + t2)) implies #[trigger] l.contains(t2) by {
                    if t2 == t {
                        assert(false);
                    }
                }
            }
        }
        n = n + bit;
        t = t + 1;
    }
    (n, Ghost(l))
}

/// Fine stage: of the coarse candidates, the rows whose part matches (`pmatch`), in order.
fn stage2(c: &Cols, f: &PFilter, cand1: &Vec<u16>, n1: usize, l1: Ghost<Seq<int>>, cand2: &mut Vec<u16>, j: usize, nb: usize,
    g: usize, off0: i64) -> (r: (usize, Ghost<Seq<int>>))
    requires
        cols_ok(*c),
        pf_ok(*f),
        old(cand2)@.len() == BLK,
        cand1@.len() == BLK,
        nb <= BLK,
        j + nb <= c.n_l,
        g * c.bs_l <= j, j + nb <= g * c.bs_l + c.bs_l,
        f.use_bits ==> off0 == c.lp_b@[g as int] - f.pk_lo,
        f.use_bits ==> -0x2_0000_0000 <= off0 <= 0x2_0000_0000,
        g < c.lp_b@.len(),
        l1@.len() == n1,
        list_mirror(cand1@, l1@),
        list_ok(l1@, nb as int),
        pad_ok(*f),
        f.use_bits ==> forall|i: int| 0 <= i < n1 ==> in_clamp(*f, lp(*c, j + #[trigger] l1@[i])),
        forall|t: int| 0 <= t < nb && pmatch(*f, lp(*c, j + t)) ==> #[trigger] l1@.contains(t),
    ensures
        final(cand2)@.len() == BLK,
        r.1@.len() == r.0,
        list_mirror(final(cand2)@, r.1@),
        list_ok(r.1@, nb as int),
        forall|i: int| 0 <= i < r.0 ==> pmatch(*f, lp(*c, j + #[trigger] r.1@[i])),
        forall|t: int| 0 <= t < nb && pmatch(*f, lp(*c, j + t)) ==> #[trigger] r.1@.contains(t),
    no_unwind
{
    let ghost la = l1@;
    let ghost mut l: Seq<int> = Seq::empty();
    let mut n: usize = 0;
    let mut i: usize = 0;
    let use_bits = f.use_bits;
    let nbits = f.nbits;
    while i < n1
        invariant
            cols_ok(*c),
            pf_ok(*f),
            use_bits == f.use_bits,
            cand2@.len() == BLK,
            cand1@.len() == BLK,
            nb <= BLK,
            j + nb <= c.n_l,
            g * c.bs_l <= j, j + nb <= g * c.bs_l + c.bs_l,
            f.use_bits ==> off0 == c.lp_b@[g as int] - f.pk_lo,
            f.use_bits ==> -0x2_0000_0000 <= off0 <= 0x2_0000_0000,
            g < c.lp_b@.len(),
            la.len() == n1,
            list_mirror(cand1@, la),
            list_ok(la, nb as int),
            pad_ok(*f),
            nbits == f.nbits,
            f.use_bits ==> forall|i2: int| 0 <= i2 < n1 ==> in_clamp(*f, lp(*c, j + #[trigger] la[i2])),
            n <= i <= n1,
            l.len() == n,
            list_mirror(cand2@, l),
            list_ok(l, nb as int),
            forall|k: int| 0 <= k < n ==> #[trigger] l[k] < if i < n1 { la[i as int] } else { nb as int },
            forall|k: int| 0 <= k < n ==> pmatch(*f, lp(*c, j + #[trigger] l[k])),
            forall|i2: int| 0 <= i2 < i && pmatch(*f, lp(*c, j + la[i2])) ==> #[trigger] l.contains(la[i2]),
        decreases n1 - i,
    {
        let t = cand1[i];
        let r = j + t as usize;
        proof {
            assert(t as int == la[i as int]);
            lemma_div_group(r as int, c.bs_l as int, g as int);
        }
        let bit: usize = if use_bits {
            proof {
                assert(in_clamp(*f, lp(*c, r as int)));
            }
            let off = (off0 + c.lp_c[r] as i64) as u64;
            proof {
                assert(off as int == lp(*c, r as int) - f.pk_lo);
                if off < nbits {
                    vstd::arithmetic::div_mod::lemma_div_is_ordered(off as int, f.bits@.len() * 64 - 1, 64);
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(f.bits@.len() * 64 - 1, 64,
                        f.bits@.len() - 1, 63);
                    assert(off as int / 64 < f.bits@.len());
                } else if pmatch(*f, lp(*c, r as int)) {
                    assert(in_rng(*f, lp(*c, r as int)));
                }
            }
            // Offsets in [nbits, clamp) belong to no key of the bitmap range.
            if off < nbits && test_bit(&f.bits, off) { 1 } else { 0 }
        } else {
            proof {
                assert(in_i64(lk(*c, r as int)));
            }
            let v = c.lp_b[g] + c.lp_c[r] as i64;
            if pmatch_lookup(f, v) { 1 } else { 0 }
        };
        proof {
            assert((bit == 1) == pmatch(*f, lp(*c, r as int)));
        }
        cand2[n] = t;
        proof {
            let l_old = l;
            if bit == 1 {
                l = l.push(t as int);
            }
            assert forall|k: int| 0 <= k < l.len() implies #[trigger] l[k] < if i + 1 < n1 { la[i + 1] } else { nb as int } by {
                if k < l_old.len() {
                    assert(l[k] == l_old[k]);
                }
                if i + 1 < n1 {
                    assert(la[i as int] < la[i + 1]);
                }
            }
            assert forall|i2: int| 0 <= i2 < i + 1 && pmatch(*f, lp(*c, j + la[i2])) implies #[trigger] l.contains(la[i2]) by {
                if i2 < i {
                    assert(l_old.contains(la[i2]));
                    let k = choose|k: int| 0 <= k < l_old.len() && l_old[k] == la[i2];
                    assert(l[k] == la[i2]);
                } else {
                    assert(l[l.len() - 1] == la[i2]);
                }
            }
        }
        n = n + bit;
        i = i + 1;
    }
    proof {
        assert forall|t: int| 0 <= t < nb && pmatch(*f, lp(*c, j + t)) implies #[trigger] l.contains(t) by {
            assert(la.contains(t));
            let i2 = choose|i2: int| 0 <= i2 < la.len() && la[i2] == t;
            assert(pmatch(*f, lp(*c, j + la[i2])));
        }
    }
    (n, Ghost(l))
}

// ------------------------------------------------------------------------------------------------ list sums

/// The accumulator of the rows `base + l[i]`, `i < n`.
pub open spec fn acc_list(m: Cols, pm: spec_fn(int) -> bool, ns: NStat, base: int, l: Seq<int>, n: int) -> AccS
    decreases n,
{
    if n <= 0 { acc_zero() } else { acc_add(acc_list(m, pm, ns, base, l, n - 1), acc_of(lc(m, pm, ns, base + l[n - 1]))) }
}

/// A strictly increasing list holding every contributing row below `t` sums like the range `[base, base + t)`.
pub proof fn lemma_list_range(m: Cols, pm: spec_fn(int) -> bool, ns: NStat, base: int, l: Seq<int>, n: int, t: int)
    requires
        0 <= n <= l.len(),
        t >= 0,
        forall|i: int| 0 <= i < n ==> 0 <= #[trigger] l[i] < t,
        forall|i: int, k: int| 0 <= i < k < n ==> #[trigger] l[i] < #[trigger] l[k],
        forall|u: int| 0 <= u < t && #[trigger] lc(m, pm, ns, base + u) is Some ==> l.take(n).contains(u),
    ensures acc_list(m, pm, ns, base, l, n) == acc_range(m, pm, ns, base, base + t),
    decreases t,
{
    if t > 0 {
        if n > 0 && l[n - 1] == t - 1 {
            assert forall|u: int| 0 <= u < t - 1 && #[trigger] lc(m, pm, ns, base + u) is Some implies l.take(n - 1).contains(u) by {
                assert(l.take(n).contains(u));
                let i = choose|i: int| 0 <= i < n && l.take(n)[i] == u;
                if i == n - 1 {
                    assert(false);
                }
                assert(l.take(n - 1)[i] == u);
            }
            assert forall|i: int| 0 <= i < n - 1 implies 0 <= #[trigger] l[i] < t - 1 by {
                assert(l[i] < l[n - 1]);
            }
            lemma_list_range(m, pm, ns, base, l, n - 1, t - 1);
        } else {
            let u = t - 1;
            if lc(m, pm, ns, base + u) is Some {
                assert(l.take(n).contains(u));
                let i = choose|i: int| 0 <= i < n && l.take(n)[i] == t - 1;
                if i < n - 1 {
                    assert(l[i] < l[n - 1]);
                }
                assert(false);
            }
            assert forall|i: int| 0 <= i < n implies 0 <= #[trigger] l[i] < t - 1 by {
                if l[i] == t - 1 {
                    if i < n - 1 {
                        assert(l[i] < l[n - 1]);
                    }
                }
            }
            assert forall|u: int| 0 <= u < t - 1 && #[trigger] lc(m, pm, ns, base + u) is Some implies l.take(n).contains(u) by {}
            lemma_list_range(m, pm, ns, base, l, n, t - 1);
        }
    } else {
        if n > 0 {
            assert(l[0] < 0);
        }
    }
}

// ------------------------------------------------------------------------------------------------ accumulators

/// The executable per-year accumulators (exact: masses bound the sums, counts are row counts).
pub struct Acc {
    pub c0: usize,
    pub v0: i128,
    pub hc0: usize,
    pub hv0: i128,
    pub m0: i128,
    pub c1: usize,
    pub v1: i128,
    pub hc1: usize,
    pub hv1: i128,
    pub m1: i128,
    pub ovf: bool,
}

pub open spec fn acc_view(a: Acc) -> AccS {
    AccS {
        c0: a.c0 as int, v0: a.v0 as int, hc0: a.hc0 as int, hv0: a.hv0 as int, m0: a.m0 as int,
        c1: a.c1 as int, v1: a.v1 as int, hc1: a.hc1 as int, hv1: a.hv1 as int, m1: a.m1 as int,
    }
}

pub fn acc_new() -> (a: Acc)
    ensures acc_view(a) == acc_zero(), !a.ovf,
    no_unwind
{
    Acc { c0: 0, v0: 0, hc0: 0, hv0: 0, m0: 0, c1: 0, v1: 0, hc1: 0, hv1: 0, m1: 0, ovf: false }
}

/// The volume bound of one row's contribution.
pub open spec fn vol_ok(o: Option<(bool, i128, bool)>) -> bool {
    o matches Some((b, v, h)) ==> -0x1_0000_0000_0000_0000_0000_0000_0000 < v < 0x1_0000_0000_0000_0000_0000_0000_0000
}

/// Adds one row's contribution; `false` (nothing added) when a year's mass would pass `i128::MAX`.
pub fn acc_push(a: &mut Acc, o: Option<(bool, i128, bool)>, Ghost(n): Ghost<int>) -> (ok: bool)
    requires
        acc_sane(acc_view(*old(a)), n),
        n < usize::MAX,
        vol_ok(o),
    ensures
        final(a).ovf == old(a).ovf,
        ok ==> acc_view(*final(a)) == acc_add(acc_view(*old(a)), acc_of(hit_of(o)))
            && acc_sane(acc_view(*final(a)), n + 1),
        !ok ==> acc_add(acc_view(*old(a)), acc_of(hit_of(o))).m0 > i128::MAX
            || acc_add(acc_view(*old(a)), acc_of(hit_of(o))).m1 > i128::MAX,
    no_unwind
{
    match o {
        None => true,
        Some((b, v, h)) => {
            let m: i128 = if v >= 0 { v } else { -v };
            if !b {
                if a.m0 > i128::MAX - m {
                    return false;
                }
                a.c0 = a.c0 + 1;
                a.v0 = a.v0 + v;
                a.m0 = a.m0 + m;
                if h {
                    a.hc0 = a.hc0 + 1;
                    a.hv0 = a.hv0 + v;
                }
            } else {
                if a.m1 > i128::MAX - m {
                    return false;
                }
                a.c1 = a.c1 + 1;
                a.v1 = a.v1 + v;
                a.m1 = a.m1 + m;
                if h {
                    a.hc1 = a.hc1 + 1;
                    a.hv1 = a.hv1 + v;
                }
            }
            true
        },
    }
}

// ------------------------------------------------------------------------------------------------ orders lookup

/// The stored orders row of key `k` (`rpos`), by the orders key index.
pub fn order_pos(c: &Cols, k: i64) -> (p: usize)
    requires cols_ok(*c),
    ensures p == rpos(*c, k as int),
    no_unwind
{
    match crate::stores::factsdir::interface::common::keyidx::key_find(c.ok_c, c.ok_b, c.oi_c, c.oi_b, c.bs_o, c.oi_kind,
        c.n_o, k as i128) {
        Some(p) => {
            proof {
                assert(okey(*c, p as int) == k);
                assert forall|q: int| 0 <= q < p implies #[trigger] okey(*c, q) != k by {
                    if okey(*c, q) == k {
                        assert(okey(*c, q) == okey(*c, p as int));
                    }
                }
                lemma_rpos_at(*c, k as int, p as int);
            }
            p
        },
        None => {
            proof {
                assert forall|q: int| 0 <= q < c.n_o implies #[trigger] okey(*c, q) != k by {
                    assert(crate::stores::factsdir::interface::common::keyidx::fkey(c.ok_c@, c.ok_b@, c.bs_o as int, q) != k);
                }
                lemma_rpos_at(*c, k as int, c.n_o as int);
            }
            c.n_o
        },
    }
}

// ------------------------------------------------------------------------------------------------ the scan

/// The facts a scan task needs.
pub open spec fn scan_pre(c: Cols, f: PFilter, nt: NTab, l0: int, l1: int, clustered: bool) -> bool {
    &&& cols_ok(c)
    &&& pf_ok(f)
    &&& pad_ok(f)
    &&& ntab_ok(nt)
    &&& 0 <= l0 <= l1 <= c.n_l
    &&& clustered ==> lines_clustered(c)
}

/// What a scan of `[l0, l1)` returns.
pub open spec fn scan_post(c: Cols, f: PFilter, nt: NTab, l0: int, l1: int, out: Acc) -> bool {
    let s = acc_range(c, pm_of(f), nt_view(nt), l0, l1);
    &&& !out.ovf ==> acc_view(out) == s
    &&& out.ovf ==> s.m0 > i128::MAX || s.m1 > i128::MAX
}

/// The rows after the listed ones contribute nothing (strictly increasing list holding every matching row).
proof fn lemma_gap_none(c: Cols, f: PFilter, ns: NStat, j: int, l: Seq<int>, n: int, lo: int, hi: int)
    requires
        n == l.len(),
        list_ok(l, hi - j + 1),
        forall|t: int| 0 <= t < hi - j && pmatch(f, lp(c, j + t)) ==> #[trigger] l.contains(t),
        forall|k: int| 0 <= k < n ==> #[trigger] l[k] < lo - j || l[k] >= hi - j,
        j <= lo <= hi,
    ensures forall|r: int| lo <= r < hi ==> #[trigger] lc(c, pm_of(f), ns, r) is None,
{
    assert forall|r: int| lo <= r < hi implies #[trigger] lc(c, pm_of(f), ns, r) is None by {
        if pmatch(f, lp(c, r)) {
            let t = r - j;
            assert(r == j + t);
            assert(l.contains(t));
        }
    }
}

/// The order cursor: stored orders row `p`, its group `gp`, and the rows `rem` of that group from `p` on.
pub struct Cursor {
    pub p: usize,
    pub gp: usize,
    pub rem: usize,
}

pub open spec fn cur_ok(c: Cols, cu: Cursor) -> bool {
    &&& cu.p <= c.n_o
    &&& cu.gp * c.bs_o <= cu.p
    &&& cu.p + cu.rem == cu.gp * c.bs_o + c.bs_o
    &&& 1 <= cu.rem <= c.bs_o
}

/// A cursor at stored orders row `p`.
fn cursor_at(c: &Cols, p: usize) -> (cu: Cursor)
    requires cols_ok(*c), p <= c.n_o,
    ensures cur_ok(*c, cu), cu.p == p,
    no_unwind
{
    let gp = p / c.bs_o;
    proof {
        lemma_group_of_row(p as int, c.bs_o as int);
    }
    Cursor { p, gp, rem: c.bs_o - (p - gp * c.bs_o) }
}

/// The cursor's row is in its group.
proof fn lemma_cur_group(c: Cols, cu: Cursor)
    requires cols_ok(c), cur_ok(c, cu), cu.p < c.n_o,
    ensures cu.gp == cu.p / c.bs_o, cu.gp < c.ok_b@.len(),
{
    lemma_div_group(cu.p as int, c.bs_o as int, cu.gp as int);
    lemma_div_below(cu.p as int, c.bs_o as int, c.ok_b@.len() as int);
}

/// Advances the cursor to `rpos(k)`, from a row at most `rpos(k)`.
fn cursor_to(c: &Cols, cu: &mut Cursor, k: i64)
    requires cols_ok(*c), cur_ok(*c, *old(cu)), old(cu).p <= rpos(*c, k as int),
    ensures cur_ok(*c, *final(cu)), final(cu).p == rpos(*c, k as int),
    no_unwind
{
    proof {
        lemma_rpos(*c, k as int);
    }
    let n_o = c.n_o;
    let bs_o = c.bs_o;
    while cu.p < n_o
        invariant
            cols_ok(*c),
            n_o == c.n_o,
            bs_o == c.bs_o,
            cur_ok(*c, *cu),
            cu.p <= rpos(*c, k as int),
            0 <= rpos(*c, k as int) <= c.n_o,
            rpos(*c, k as int) < c.n_o ==> okey(*c, rpos(*c, k as int)) == k,
            forall|q: int| 0 <= q < rpos(*c, k as int) ==> #[trigger] okey(*c, q) != k,
        decreases n_o - cu.p,
    {
        proof {
            lemma_cur_group(*c, *cu);
            assert(in_i64(okey(*c, cu.p as int)));
        }
        if c.ok_b[cu.gp] + c.ok_c[cu.p] as i64 == k {
            return;
        }
        proof {
            assert(okey(*c, cu.p as int) != k);
            assert(cu.p < rpos(*c, k as int));
        }
        cu.p = cu.p + 1;
        cu.rem = cu.rem - 1;
        if cu.rem == 0 {
            proof {
                assert((cu.gp + 1) * bs_o == cu.gp * bs_o + bs_o) by (nonlinear_arith);
            }
            cu.gp = cu.gp + 1;
            cu.rem = bs_o;
        }
    }
}

/// The candidate rows of one block (`cand2`, mirrored by `l2`): order, lookups, accumulation. `false`: a year's mass
/// passed `i128::MAX` within the block.
fn stage3(c: &Cols, f: &PFilter, nt: &NTab, cand2: &Vec<u16>, n2: usize, l2: Ghost<Seq<int>>, j: usize, nb: usize,
    g: usize, l0: usize, clustered: bool, acc: &mut Acc, cu: &mut Cursor, last: Ghost<int>) -> (r: (bool, Ghost<int>))
    requires
        cols_ok(*c),
        pf_ok(*f),
        ntab_ok(*nt),
        clustered ==> lines_clustered(*c),
        l0 <= j,
        j + nb <= c.n_l,
        g * c.bs_l <= j, j + nb <= g * c.bs_l + c.bs_l,
        g < c.lk_b@.len(),
        cand2@.len() == BLK,
        l2@.len() == n2,
        list_mirror(cand2@, l2@),
        list_ok(l2@, nb as int),
        forall|k: int| 0 <= k < n2 ==> pmatch(*f, lp(*c, j + #[trigger] l2@[k])),
        forall|t: int| 0 <= t < nb && pmatch(*f, lp(*c, j + t)) ==> #[trigger] l2@.contains(t),
        !old(acc).ovf,
        acc_view(*old(acc)) == acc_range(*c, pm_of(*f), nt_view(*nt), l0 as int, j as int),
        clustered ==> cur_ok(*c, *old(cu)) && l0 <= last@ <= j && last@ < c.n_l && old(cu).p <= rpos(*c, lk(*c, last@)),
    ensures
        !final(acc).ovf,
        r.0 ==> acc_view(*final(acc)) == acc_range(*c, pm_of(*f), nt_view(*nt), l0 as int, j + nb),
        r.0 && clustered ==> cur_ok(*c, *final(cu)) && l0 <= r.1@ <= j + nb && r.1@ < c.n_l
            && final(cu).p <= rpos(*c, lk(*c, r.1@)),
        !r.0 ==> acc_range(*c, pm_of(*f), nt_view(*nt), l0 as int, j + nb).m0 > i128::MAX
            || acc_range(*c, pm_of(*f), nt_view(*nt), l0 as int, j + nb).m1 > i128::MAX,
    no_unwind
{
    let ghost pm = pm_of(*f);
    let ghost ns = nt_view(*nt);
    let ghost l2 = l2@;
    let ghost mut lst = last@;
    let mut i: usize = 0;
    while i < n2
        invariant
            cols_ok(*c),
            pf_ok(*f),
            ntab_ok(*nt),
            pm == pm_of(*f),
            ns == nt_view(*nt),
            clustered ==> lines_clustered(*c),
            l0 <= j,
            j + nb <= c.n_l,
            g * c.bs_l <= j, j + nb <= g * c.bs_l + c.bs_l,
            g < c.lk_b@.len(),
            cand2@.len() == BLK,
            l2.len() == n2,
            list_mirror(cand2@, l2),
            list_ok(l2, nb as int),
            forall|k: int| 0 <= k < n2 ==> pmatch(*f, lp(*c, j + #[trigger] l2[k])),
            forall|t: int| 0 <= t < nb && pmatch(*f, lp(*c, j + t)) ==> #[trigger] l2.contains(t),
            i <= n2,
            !acc.ovf,
            acc_view(*acc) == acc_range(*c, pm, ns, l0 as int, j + if i == 0 { 0int } else { l2[i - 1] + 1 }),
            clustered ==> cur_ok(*c, *cu) && l0 <= lst <= j + if i == 0 { 0int } else { l2[i - 1] } && lst < c.n_l
                && cu.p <= rpos(*c, lk(*c, lst)),
        decreases n2 - i,
    {
        let t = cand2[i];
        let r = j + t as usize;
        let ghost prev_end: int = j + if i == 0 { 0int } else { l2[i - 1] + 1 };
        proof {
            assert(t as int == l2[i as int]);
            if i > 0 {
                assert(l2[i - 1] < l2[i as int]);
            }
            lemma_div_group(r as int, c.bs_l as int, g as int);
            assert(in_i64(lk(*c, r as int)));
            // The rows between the previous candidate and this one contribute nothing.
            assert forall|u: int| prev_end <= u < r implies #[trigger] lc(*c, pm, ns, u) is None by {
                if pmatch(*f, lp(*c, u)) {
                    let tt = u - j;
                    assert(u == j + tt);
                    assert(l2.contains(tt));
                    let k = choose|k: int| 0 <= k < l2.len() && l2[k] == tt;
                    if k < i {
                        if k < i - 1 {
                            assert(l2[k] < l2[i - 1]);
                        }
                    } else if k > i {
                        assert(l2[i as int] < l2[k]);
                    }
                }
            }
            lemma_acc_none(*c, pm, ns, prev_end, r as int);
            lemma_acc_split(*c, pm, ns, l0 as int, prev_end, r as int);
            lemma_acc_add_zero(acc_range(*c, pm, ns, l0 as int, prev_end));
        }
        let k = c.lk_b[g] + c.lk_c[r] as i64;
        if clustered {
            proof {
                lemma_lines_le(*c, lst, r as int);
            }
            cursor_to(c, cu, k);
            proof {
                lst = r as int;
            }
        } else {
            let p = order_pos(c, k);
            proof {
                lemma_rpos(*c, k as int);
            }
            *cu = cursor_at(c, p);
        }
        proof {
            if cu.p < c.n_o {
                lemma_cur_group(*c, *cu);
            }
        }
        let o = contrib(c, nt, r, g, cu.p, cu.gp);
        proof {
            assert(pmatch(*f, lp(*c, r as int)));
            assert(lc(*c, pm, ns, r as int) == lc2(*c, ns, r as int));
            lemma_acc_range_sane(*c, pm, ns, l0 as int, r as int);
            assert(acc_view(*acc) == acc_range(*c, pm, ns, l0 as int, r as int));
        }
        if !acc_push(acc, o, Ghost(r - l0)) {
            proof {
                lemma_acc_mass_mono(*c, pm, ns, l0 as int, r + 1, j + nb);
            }
            return (false, Ghost(lst));
        }
        i = i + 1;
    }
    proof {
        let end_l = j + if n2 == 0 { 0int } else { l2[n2 - 1] + 1 };
        assert forall|u: int| end_l <= u < j + nb implies #[trigger] lc(*c, pm, ns, u) is None by {
            if pmatch(*f, lp(*c, u)) {
                let tt = u - j;
                assert(u == j + tt);
                assert(l2.contains(tt));
                let k = choose|k: int| 0 <= k < l2.len() && l2[k] == tt;
                if k < n2 - 1 {
                    assert(l2[k] < l2[n2 - 1]);
                }
            }
        }
        lemma_acc_none(*c, pm, ns, end_l, j + nb);
        lemma_acc_split(*c, pm, ns, l0 as int, end_l, j + nb);
        lemma_acc_add_zero(acc_range(*c, pm, ns, l0 as int, end_l));
    }
    (true, Ghost(lst))
}

/// Stored lineitem rows `[l0, l1)`: the per-year accumulators.
fn scan_range(c: &Cols, f: &PFilter, nt: &NTab, l0: usize, l1: usize, clustered: bool, cand1: Vec<u16>, cand2: Vec<u16>)
    -> (out: Acc)
    requires
        scan_pre(*c, *f, *nt, l0 as int, l1 as int, clustered),
        cand1@.len() == BLK,
        cand2@.len() == BLK,
    ensures scan_post(*c, *f, *nt, l0 as int, l1 as int, out),
    no_unwind
{
    let ghost pm = pm_of(*f);
    let ghost ns = nt_view(*nt);
    let mut cand1 = cand1;
    let mut cand2 = cand2;
    let mut acc = acc_new();
    if l0 >= l1 {
        return acc;
    }
    let bs_l = c.bs_l;
    let use_bits = f.use_bits;
    let nbits = f.nbits;
    proof {
        lemma_div_below(l0 as int, bs_l as int, c.lk_b@.len() as int);
        assert(in_i64(lk(*c, l0 as int)));
        lemma_rpos(*c, lk(*c, l0 as int));
    }
    let p0: usize = if clustered { order_pos(c, c.lk_b[l0 / bs_l] + c.lk_c[l0] as i64) } else { 0 };
    let mut cu = cursor_at(c, p0);
    let ghost mut last: int = l0 as int;
    let mut j = l0;
    while j < l1
        invariant
            scan_pre(*c, *f, *nt, l0 as int, l1 as int, clustered),
            pm == pm_of(*f),
            ns == nt_view(*nt),
            bs_l == c.bs_l,
            use_bits == f.use_bits,
            nbits == f.nbits,
            cand1@.len() == BLK,
            cand2@.len() == BLK,
            l0 <= j <= l1,
            l0 < l1,
            !acc.ovf,
            acc_view(acc) == acc_range(*c, pm, ns, l0 as int, j as int),
            clustered ==> cur_ok(*c, cu) && l0 <= last <= j && last < c.n_l && cu.p <= rpos(*c, lk(*c, last)),
        decreases l1 - j,
    {
        let g = j / bs_l;
        proof {
            lemma_group_of_row(j as int, bs_l as int);
            lemma_div_below(j as int, bs_l as int, c.lk_b@.len() as int);
        }
        let in_grp = bs_l - (j - g * bs_l);
        let e1 = if in_grp < l1 - j { j + in_grp } else { l1 };
        let e = if e1 - j > BLK { j + BLK } else { e1 };
        let nb = e - j;
        let lo_i: i128 = c.lp_b[g] as i128 - f.pk_lo as i128;
        if use_bits && (lo_i + 0x1_0000_0000 <= 0 || lo_i >= nbits as i128) {
            // No row of the block has its part key in the bitmap range.
            proof {
                assert forall|r: int| j <= r < e implies #[trigger] lc(*c, pm, ns, r) is None by {
                    lemma_div_group(r, bs_l as int, g as int);
                    assert(lp(*c, r) == c.lp_b@[g as int] + c.lp_c@[r]);
                    if pmatch(*f, lp(*c, r)) {
                        assert(in_rng(*f, lp(*c, r)));
                    }
                }
                lemma_acc_none(*c, pm, ns, j as int, e as int);
                lemma_acc_split(*c, pm, ns, l0 as int, j as int, e as int);
                lemma_acc_add_zero(acc_range(*c, pm, ns, l0 as int, j as int));
            }
            j = e;
            continue;
        }
        let off0: i64 = if use_bits { lo_i as i64 } else { 0 };
        let (n1, l1s) = stage1(c, f, &mut cand1, j, nb, g, off0);
        let (n2, l2s) = stage2(c, f, &cand1, n1, l1s, &mut cand2, j, nb, g, off0);
        let (ok, lst) = stage3(c, f, nt, &cand2, n2, l2s, j, nb, g, l0, clustered, &mut acc, &mut cu, Ghost(last));
        if !ok {
            proof {
                lemma_acc_mass_mono(*c, pm, ns, l0 as int, e as int, l1 as int);
            }
            acc.ovf = true;
            return acc;
        }
        proof {
            last = lst@;
        }
        j = e;
    }
    acc
}

impl WorkerTask for ScanTask {
    type Output = Acc;

    open spec fn pre(&self) -> bool {
        &&& scan_pre(self.c, *self.f, *self.nt, self.l0 as int, self.l1 as int, self.clustered)
        &&& self.cand1@.len() == BLK
        &&& self.cand2@.len() == BLK
    }

    open spec fn post(&self, out: Acc) -> bool {
        scan_post(self.c, *self.f, *self.nt, self.l0 as int, self.l1 as int, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.l0 as u64, self.l1 as u64)
    }

    fn run(self) -> (out: Acc) {
        let f: &PFilter = &*self.f;
        let nt: &NTab = &*self.nt;
        scan_range(&self.c, f, nt, self.l0, self.l1, self.clustered, self.cand1, self.cand2)
    }
}

/// One scan task: stored lineitem rows `[l0, l1)`, with its candidate buffers.
pub struct ScanTask {
    pub c: Cols,
    pub f: Arc<PFilter>,
    pub nt: Arc<NTab>,
    pub l0: usize,
    pub l1: usize,
    pub clustered: bool,
    pub cand1: Vec<u16>,
    pub cand2: Vec<u16>,
}

} // verus!
