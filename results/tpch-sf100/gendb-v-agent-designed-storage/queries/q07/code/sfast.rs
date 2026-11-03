//! Supplier-first fast path of the Q7 scan over one batch of lines `[jb, je)` of lineitem group `g` (model:
//! `super::model`), for stored lines co-clustered with the stored orders (`clus_ok`) with the l_orderkey run starts
//! of storage `li_okruns` (`runs_ok`):
//! 1. `lc[t]` is the class of line `jb + t` (`l_scw`: its supplier's nation class when it ships in the window), from
//!    a fixed-size supplier class map (no bounds checks, so the word loads vectorize). When the zone map puts the
//!    whole group in the window the shipdate is not read (`line_classes_in`), else its code range is tested
//!    (`line_classes_edge`);
//! 2. `hm` holds one bit per line with a class (`hit_mask`); every line without its bit is in no group;
//! 3. the lines with a bit (about 8%) are the candidates (`pick_hits`): a cursor over the run starts steps to the
//!    run holding each one (`incseq::step_le`), and the run's index is taken as its orders row, whose customer row
//!    becomes the candidate's (`cq_ok`);
//! 4. one check per batch makes this exact: when the batch's first and last runs start with the keys of the orders
//!    rows of their indexes, every run between does (`runs::lemma_aligned_range`), so each candidate's row is its
//!    order's (`cr_ok`). A failed check leaves the batch to the caller's line-first passes;
//! 5. the candidates' customer classes, group codes and sums are `kernel`'s passes C and D.
use vstd::prelude::*;
use super::common::incseq::*;
use super::model::*;
use super::lookup::*;
use super::dates::*;
use super::cmap::*;
use super::kernel::*;
use super::runs::*;

verus! {

/// Words of the fixed-size supplier class map (16 suppliers per word: up to 2^20 suppliers).
pub const SMW: usize = 65536;
/// Words of a batch's hit mask (64 lines per word).
pub const HW: usize = 64;

// ------------------------------------------------------------------------------------------------ the class map

/// The supplier class map as a fixed-size array: `sm` padded with zero words.
pub fn smap_array(sm: &Vec<u32>) -> (r: Box<[u32; SMW]>)
    requires sm@.len() <= SMW,
    ensures forall|i: int| 0 <= i < SMW ==> #[trigger] r@[i] == if i < sm@.len() { sm@[i] } else { 0u32 },
{
    let mut m: Box<[u32; SMW]> = Box::new([0u32; SMW]);
    let n = sm.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == sm@.len(), n <= SMW, i <= n,
            forall|k: int| 0 <= k < SMW ==> #[trigger] m@[k] == if k < i { sm@[k] } else { 0u32 },
        decreases n - i,
    {
        m.set(i, sm[i]);
        i = i + 1;
    }
    m
}

/// A zero-padded copy of a class map is a class map.
pub proof fn lemma_smap_array(c: Cols, x: Ctx, sk0: i64, sm: Seq<u32>, ma: Seq<u32>)
    requires
        smap2_ok(c, x, sk0, sm),
        ma.len() == SMW, sm.len() <= SMW,
        forall|i: int| 0 <= i < SMW ==> #[trigger] ma[i] == if i < sm.len() { sm[i] } else { 0u32 },
    ensures smap2_ok(c, x, sk0, ma),
{
    let (nb, nc, bs, n) = (c.sn_bases@, c.sn_codes@, c.bs_s as int, c.n_s as int);
    assert forall|i: int| 0 <= i < ma.len() implies #[trigger] word_ok(x, nb, nc, bs, n, i, ma[i]) by {
        if i < sm.len() {
            assert(word_ok(x, nb, nc, bs, n, i, sm[i]));
        } else {
            assert forall|t: int| 0 <= t < 16 && 16 * i + t < n implies #[trigger] get2(ma[i], t) == nat_cls(x, nat_of(nb, nc, bs, 16 * i + t)) by {
                assert(16 * sm.len() >= n);
            }
        }
    }
}

/// `out[t] = cls_of(m, ns, sk[t] + off)` for `t < n0`, in 32-bit lanes over the fixed-size map: codes in
/// `[lo, hi]` are the ones whose row `sk[t] + off` lies in `[0, ns)`, and `offu` is `off` modulo 2^32.
#[inline(never)]
fn sclass_kernel(sk: &[u32], off: i64, lo: u32, hi: u32, offu: u32, ns: u32, m: &[u32; SMW], out: &mut [u8], n0: usize)
    requires
        n0 <= sk@.len(), n0 <= old(out)@.len(),
        ns <= 16 * SMW,
        offu as int == if off >= 0 { off as int } else { off + 0x1_0000_0000 },
        -0x1_0000_0000 < off < 0x1_0000_0000,
        forall|k: u32| lo <= k <= hi ==> 0 <= #[trigger] (k + off) < ns,
        forall|k: u32| !(lo <= k <= hi) ==> !(0 <= #[trigger] (k + off) < ns),
    ensures
        final(out)@.len() == old(out)@.len(),
        forall|t: int| 0 <= t < n0 ==> #[trigger] final(out)@[t] as int == cls_of(m@, ns as int, sk@[t] + off),
        forall|t: int| 0 <= t < n0 ==> #[trigger] final(out)@[t] < 4,
    no_unwind
{
    let (sk, _) = sk.split_at(n0);
    let (o, _rest) = out.split_at_mut(n0);
    let mut t: usize = 0;
    while t < n0
        invariant
            n0 == sk@.len(), n0 == o@.len(),
            ns <= 16 * SMW,
            offu as int == if off >= 0 { off as int } else { off + 0x1_0000_0000 },
            -0x1_0000_0000 < off < 0x1_0000_0000,
            forall|k: u32| lo <= k <= hi ==> 0 <= #[trigger] (k + off) < ns,
            forall|k: u32| !(lo <= k <= hi) ==> !(0 <= #[trigger] (k + off) < ns),
            t <= n0,
            forall|s: int| 0 <= s < t ==> #[trigger] o@[s] as int == cls_of(m@, ns as int, sk@[s] + off),
            forall|s: int| 0 <= s < t ==> #[trigger] o@[s] < 4,
        decreases n0 - t,
    {
        let k = sk[t];
        let inr = lo <= k && k <= hi;
        let mk: u32 = if inr { 3 } else { 0 };
        let r = k.wrapping_add(offu);
        let wi = ((r >> 4) & 0xffff) as usize;
        proof {
            assert((r >> 4) & 0xffff < 0x10000) by (bit_vector);
            assert((r & 15) <= 15) by (bit_vector);
        }
        let w = m[wi];
        let v = (w >> ((r & 15) * 2)) & mk;
        proof {
            assert(((w >> ((r & 15) * 2)) & 0u32) == 0u32 && ((w >> ((r & 15) * 2)) & 3u32) < 4u32) by (bit_vector);
            if inr {
                let ri = k + off;
                assert(0 <= ri < ns);
                assert(r as int == ri);
                assert(r < 0x10_0000);
                assert(r < 0x10_0000 ==> (r >> 4u32) & 0xffffu32 == r / 16 && (r & 15u32) == r % 16) by (bit_vector);
                assert(wi == ri / 16 && ((r & 15) * 2) as u32 == (2 * (ri % 16)) as u32);
                assert(v as int == get2(m@[ri / 16], ri % 16));
            } else {
                assert(!(0 <= k + off < ns));
            }
            assert(v as int == cls_of(m@, ns as int, sk@[t as int] + off));
        }
        let ghost o0 = o@;
        o[t] = v as u8;
        proof {
            assert forall|s: int| 0 <= s < t + 1 implies #[trigger] o@[s] as int == cls_of(m@, ns as int, sk@[s] + off) && o@[s] < 4 by {
                if s < t {
                    assert(o@[s] == o0[s]);
                }
            }
        }
        t = t + 1;
    }
    proof {
        assert forall|s: int| 0 <= s < n0 implies #[trigger] out@[s] == o@[s] by {}
    }
}

/// `out[t] = cls_of(m, ns, sk[t] + off)` when the shipdate code `sd[t]` lies in `[dlo, dhi]`, else 0, for `t < n0`
/// (the edge groups' version of `sclass_kernel`, in 32-bit lanes over the fixed-size map).
#[inline(never)]
fn sclass_kernel_w(sk: &[u32], sd: &[u16], dlo: u16, dhi: u16, off: i64, lo: u32, hi: u32, offu: u32, ns: u32,
    m: &[u32; SMW], out: &mut [u8], n0: usize)
    requires
        n0 <= sk@.len(), n0 <= sd@.len(), n0 <= old(out)@.len(),
        ns <= 16 * SMW,
        offu as int == if off >= 0 { off as int } else { off + 0x1_0000_0000 },
        -0x1_0000_0000 < off < 0x1_0000_0000,
        forall|k: u32| lo <= k <= hi ==> 0 <= #[trigger] (k + off) < ns,
        forall|k: u32| !(lo <= k <= hi) ==> !(0 <= #[trigger] (k + off) < ns),
    ensures
        final(out)@.len() == old(out)@.len(),
        forall|t: int| 0 <= t < n0 ==> #[trigger] final(out)@[t] as int
            == if dlo <= sd@[t] <= dhi { cls_of(m@, ns as int, sk@[t] + off) } else { 0 },
    no_unwind
{
    let (sk, _) = sk.split_at(n0);
    let (sd, _) = sd.split_at(n0);
    let (o, _rest) = out.split_at_mut(n0);
    let mut t: usize = 0;
    while t < n0
        invariant
            n0 == sk@.len(), n0 == sd@.len(), n0 == o@.len(),
            ns <= 16 * SMW,
            offu as int == if off >= 0 { off as int } else { off + 0x1_0000_0000 },
            -0x1_0000_0000 < off < 0x1_0000_0000,
            forall|k: u32| lo <= k <= hi ==> 0 <= #[trigger] (k + off) < ns,
            forall|k: u32| !(lo <= k <= hi) ==> !(0 <= #[trigger] (k + off) < ns),
            t <= n0,
            forall|s: int| 0 <= s < t ==> #[trigger] o@[s] as int
                == if dlo <= sd@[s] <= dhi { cls_of(m@, ns as int, sk@[s] + off) } else { 0 },
        decreases n0 - t,
    {
        let k = sk[t];
        let d = sd[t];
        let inr = lo <= k && k <= hi;
        let inw = dlo <= d && d <= dhi;
        let mk: u32 = if inr && inw { 3 } else { 0 };
        let r = k.wrapping_add(offu);
        let wi = ((r >> 4) & 0xffff) as usize;
        proof {
            assert((r >> 4) & 0xffff < 0x10000) by (bit_vector);
            assert((r & 15) <= 15) by (bit_vector);
        }
        let w = m[wi];
        let v = (w >> ((r & 15) * 2)) & mk;
        proof {
            assert(((w >> ((r & 15) * 2)) & 0u32) == 0u32 && ((w >> ((r & 15) * 2)) & 3u32) < 4u32) by (bit_vector);
            assert(v < 4u32);
            if inr && inw {
                let ri = k + off;
                assert(0 <= ri < ns);
                assert(r as int == ri);
                assert(r < 0x10_0000);
                assert(r < 0x10_0000 ==> (r >> 4u32) & 0xffffu32 == r / 16 && (r & 15u32) == r % 16) by (bit_vector);
                assert(wi == ri / 16 && ((r & 15) * 2) as u32 == (2 * (ri % 16)) as u32);
                assert(v as int == get2(m@[ri / 16], ri % 16));
            } else if inw {
                assert(!(0 <= k + off < ns));
                assert(mk == 0u32 && v == 0u32);
            } else {
                assert(mk == 0u32 && v == 0u32);
            }
            assert(v as int == if dlo <= sd@[t as int] <= dhi { cls_of(m@, ns as int, sk@[t as int] + off) } else { 0 });
        }
        let ghost o0 = o@;
        o[t] = v as u8;
        proof {
            assert forall|s: int| 0 <= s < t + 1 implies #[trigger] o@[s] as int
                == if dlo <= sd@[s] <= dhi { cls_of(m@, ns as int, sk@[s] + off) } else { 0 } by {
                if s < t {
                    assert(o@[s] == o0[s]);
                }
            }
        }
        t = t + 1;
    }
    proof {
        assert forall|s: int| 0 <= s < n0 implies #[trigger] out@[s] == o@[s] by {}
    }
}

/// Pass A1 over the lines `[jb, je)` of any group: `lc[t]` is the class of line `jb + t` (`l_scw`) from the
/// fixed-size supplier class map, the window tested on the shipdate codes. False when the group's supplier key base
/// is too far from `sk0` for 32-bit lanes (nothing is written then).
fn line_classes_edge(c: &Cols, sk0: i64, sma: &[u32; SMW], g: usize, jb: usize, je: usize, lc: &mut [u8; BATCH],
    Ghost(x): Ghost<Ctx>) -> (ok: bool)
    requires
        cols_ok(*c), keys_ok(*c),
        smap2_ok(*c, x, sk0, sma@),
        c.n_s <= 16 * SMW,
        g < c.ls_bases@.len(),
        jb < je <= c.n_l,
        je - jb <= BATCH,
        forall|j: int| jb <= j < je ==> #[trigger] (j / c.bs_l as int) == g,
    ensures
        ok ==> forall|t: int| 0 <= t < je - jb ==> #[trigger] final(lc)@[t] as int == l_scw(*c, x, jb + t),
    no_unwind
{
    let off128: i128 = c.lsk_bases[g] as i128 - sk0 as i128;
    if off128 <= -0x1_0000_0000i128 || off128 >= 0x1_0000_0000i128 {
        return false;
    }
    let off = off128 as i64;
    let ns64 = c.n_s as i64;
    let ns = c.n_s as u32;
    // the codes whose rows lie in [0, n_s): [lo, hi]
    let lo64: i64 = if off >= 0 { 0 } else { -off };
    let hi64: i64 = if ns64 - 1 - off > 0xffff_ffff { 0xffff_ffff } else { ns64 - 1 - off };
    let (lo, hi): (u32, u32) = if lo64 <= hi64 { (lo64 as u32, hi64 as u32) } else { (1, 0) };
    let offu: u32 = if off >= 0 { off as u32 } else { (off + 0x1_0000_0000) as u32 };
    // the shipdate codes whose days lie in the window: [dlo, dhi]
    let sbase = c.ls_bases[g];
    let dlo128: i128 = -1826i128 - sbase as i128;
    let dhi128: i128 = -1096i128 - sbase as i128;
    let dlo2: i128 = if dlo128 < 0 { 0 } else { dlo128 };
    let dhi2: i128 = if dhi128 > 0xffff { 0xffff } else { dhi128 };
    let (dlo, dhi): (u16, u16) = if dlo2 <= dhi2 { (dlo2 as u16, dhi2 as u16) } else { (1, 0) };
    proof {
        assert forall|k: u32| lo <= k <= hi implies 0 <= #[trigger] (k + off) < ns by {}
        assert forall|k: u32| !(lo <= k <= hi) implies !(0 <= #[trigger] (k + off) < ns) by {}
        assert forall|d: u16| (dlo <= d <= dhi) == (win_lo() <= #[trigger] (sbase + d) <= win_hi()) by {}
    }
    let sk = sub_u32(c.lsk_codes, jb, je);
    let sd = sub_u16(c.ls_codes, jb, je);
    sclass_kernel_w(sk, sd, dlo, dhi, off, lo, hi, offu, ns, sma, lc, je - jb);
    proof {
        assert forall|t: int| 0 <= t < je - jb implies #[trigger] lc@[t] as int == l_scw(*c, x, jb + t) by {
            let j = jb + t;
            assert(j / c.bs_l as int == g as int);
            assert(sk@[t] == c.lsk_codes@[j]);
            assert(sd@[t] == c.ls_codes@[j]);
            assert((dlo <= sd@[t] <= dhi) == (win_lo() <= sbase + sd@[t] <= win_hi()));
            assert(lc@[t] as int == lcw(sma@, c.n_s as int, off as int, sbase as int, c.lsk_codes@[j], c.ls_codes@[j]));
            lemma_lcw(*c, x, sk0, sma@, g as int, j);
        }
    }
    true
}

/// Pass A1 over the lines `[jb, je)` of a group the zone map puts in the window: `lc[t]` is the class of line
/// `jb + t` (`l_scw`) from the fixed-size supplier class map. False when the group's supplier key base is too far
/// from `sk0` for 32-bit lanes (nothing is written then).
fn line_classes_in(c: &Cols, sk0: i64, sma: &[u32; SMW], g: usize, jb: usize, je: usize, lc: &mut [u8; BATCH],
    Ghost(x): Ghost<Ctx>) -> (ok: bool)
    requires
        cols_ok(*c), keys_ok(*c),
        smap2_ok(*c, x, sk0, sma@),
        c.n_s <= 16 * SMW,
        g < c.ls_bases@.len(),
        c.ls_bases@[g as int] >= win_lo() && c.ls_zmax@[g as int] <= win_hi(),
        jb < je <= c.n_l,
        je - jb <= BATCH,
        forall|j: int| jb <= j < je ==> #[trigger] (j / c.bs_l as int) == g,
    ensures
        ok ==> forall|t: int| 0 <= t < je - jb ==> #[trigger] final(lc)@[t] as int == l_scw(*c, x, jb + t),
    no_unwind
{
    let off128: i128 = c.lsk_bases[g] as i128 - sk0 as i128;
    if off128 <= -0x1_0000_0000i128 || off128 >= 0x1_0000_0000i128 {
        return false;
    }
    let off = off128 as i64;
    let ns64 = c.n_s as i64;
    let ns = c.n_s as u32;
    // the codes whose rows lie in [0, n_s): [lo, hi]
    let lo64: i64 = if off >= 0 { 0 } else { -off };
    let hi64: i64 = if ns64 - 1 - off > 0xffff_ffff { 0xffff_ffff } else { ns64 - 1 - off };
    let (lo, hi): (u32, u32) = if lo64 <= hi64 { (lo64 as u32, hi64 as u32) } else { (1, 0) };
    let offu: u32 = if off >= 0 { off as u32 } else { (off + 0x1_0000_0000) as u32 };
    proof {
        assert forall|k: u32| lo <= k <= hi implies 0 <= #[trigger] (k + off) < ns by {}
        assert forall|k: u32| !(lo <= k <= hi) implies !(0 <= #[trigger] (k + off) < ns) by {}
    }
    let sk = sub_u32(c.lsk_codes, jb, je);
    sclass_kernel(sk, off, lo, hi, offu, ns, sma, lc, je - jb);
    proof {
        let sbase = c.ls_bases@[g as int];
        assert forall|t: int| 0 <= t < je - jb implies #[trigger] lc@[t] as int == l_scw(*c, x, jb + t) by {
            let j = jb + t;
            assert(j / c.bs_l as int == g as int);
            assert(sk@[t] == c.lsk_codes@[j]);
            // the whole group ships in the window
            assert(lship(*c, j) == sbase + c.ls_codes@[j] as int);
            assert(lship(*c, j) <= c.ls_zmax@[j / c.bs_l as int]);
            assert(lcw(sma@, c.n_s as int, off as int, sbase as int, c.lsk_codes@[j], c.ls_codes@[j])
                == cls_of(sma@, c.n_s as int, c.lsk_codes@[j] as int + off));
            lemma_lcw(*c, x, sk0, sma@, g as int, j);
        }
    }
    true
}

// ------------------------------------------------------------------------------------------------ hit mask

/// Bit `i` of word `w`.
pub open spec fn bit(w: u64, i: u64) -> bool {
    (w >> i) & 1u64 == 1u64
}

proof fn lemma_or_bits(m: u64, b: u64, i: u64, k: u64)
    requires b <= 1, i < 64, k < 64,
    ensures
        bit(m, k) ==> bit(m | (b << i), k),
        b == 1 && k == i ==> bit(m | (b << i), k),
        b == 0 ==> (m | (b << i)) == m,
{
    assert(b <= 1 && i < 64 && k < 64 ==> ((m >> k) & 1u64 == 1u64 ==> ((m | (b << i)) >> k) & 1u64 == 1u64)) by (bit_vector);
    assert(b == 1 && i < 64 && k == i ==> ((m | (b << i)) >> k) & 1u64 == 1u64) by (bit_vector);
    assert(b == 0 ==> (m | (b << i)) == m) by (bit_vector);
}

/// The hit bits of one full 64-line window: bit `i` set when `wd[i]` is nonzero (a fixed trip count of one
/// compare per byte, so it vectorizes).
fn window64(wd: &[u8]) -> (m: u64)
    requires wd@.len() == 64,
    ensures forall|k: u64| k < 64 && !bit(m, k) ==> #[trigger] wd@[k as int] == 0,
    no_unwind
{
    let mut m: u64 = 0;
    let mut i: usize = 0;
    while i < 64
        invariant
            wd@.len() == 64, i <= 64,
            forall|k: u64| k < i && !bit(m, k) ==> #[trigger] wd@[k as int] == 0,
        decreases 64 - i,
    {
        let b: u64 = if wd[i] != 0 { 1 } else { 0 };
        let ghost m0 = m;
        m = m | (b << (i as u64));
        proof {
            assert forall|k: u64| k < i + 1 && !bit(m, k) implies #[trigger] wd@[k as int] == 0 by {
                lemma_or_bits(m0, b, i as u64, k);
            }
        }
        i = i + 1;
    }
    m
}

/// The hit bits of the first `n` lines of a window (the batch's last, partial window).
fn window_bits(wd: &[u8], n: usize) -> (m: u64)
    requires n == wd@.len(), n <= 64,
    ensures forall|k: u64| k < n && !bit(m, k) ==> #[trigger] wd@[k as int] == 0,
    no_unwind
{
    let mut m: u64 = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            n == wd@.len(), n <= 64, i <= n,
            forall|k: u64| k < i && !bit(m, k) ==> #[trigger] wd@[k as int] == 0,
        decreases n - i,
    {
        let b: u64 = if wd[i] != 0 { 1 } else { 0 };
        let ghost m0 = m;
        m = m | (b << (i as u64));
        proof {
            assert forall|k: u64| k < i + 1 && !bit(m, k) implies #[trigger] wd@[k as int] == 0 by {
                lemma_or_bits(m0, b, i as u64, k);
            }
        }
        i = i + 1;
    }
    m
}

/// `hm[w]`, bit `i`: line `64 w + i` of the batch (below `n`) has a class; a clear bit means `lc` is 0 there.
pub open spec fn hits_ok(lc: Seq<u8>, hm: Seq<u64>, n: int) -> bool {
    forall|t: int| 0 <= t < n && !bit(hm[t / 64], (t % 64) as u64) ==> #[trigger] lc[t] == 0
}

/// The hit mask of the first `n` classes of `lc`.
#[inline(never)]
fn hit_mask(lc: &mut [u8], n: usize, hm: &mut [u64; HW])
    requires old(lc)@.len() == BATCH, n <= BATCH,
    ensures final(lc)@ == old(lc)@, hits_ok(old(lc)@, final(hm)@, n as int),
    no_unwind
{
    let (all, _) = lc.split_at(n);
    let mut rest = all;
    let mut w: usize = 0;
    proof {
        assert(all@ =~= lc@.subrange(0, n as int));
    }
    while w * 64 < n
        invariant
            lc@.len() == BATCH, n <= BATCH, BATCH == 64 * HW,
            w * 64 <= n + 63,
            w * 64 < n ==> rest@ == lc@.subrange(64 * w, n as int),
            forall|t: int| 0 <= t < n && t < 64 * w && !bit(hm@[t / 64], (t % 64) as u64) ==> #[trigger] lc@[t] == 0,
        decreases n + 64 - w * 64,
    {
        let left = n - w * 64;
        let take = if left < 64 { left } else { 64 };
        let (wd, r2) = rest.split_at(take);
        let m = if take == 64 { window64(wd) } else { window_bits(wd, take) };
        proof {
            assert(w < HW) by (nonlinear_arith) requires w * 64 < n, n <= 4096;
            assert forall|k: int| 0 <= k < take implies #[trigger] wd@[k] == lc@[64 * w + k] by {}
            if (w + 1) * 64 < n {
                assert(r2@ =~= lc@.subrange(64 * (w + 1), n as int));
            }
        }
        let ghost hm0 = hm@;
        hm[w] = m;
        proof {
            assert forall|t: int| 0 <= t < n && t < 64 * (w + 1) && !bit(hm@[t / 64], (t % 64) as u64) implies #[trigger] lc@[t] == 0 by {
                if t < 64 * w {
                    assert(t / 64 < w as int) by (nonlinear_arith) requires 0 <= t < 64 * w;
                    assert(hm@[t / 64] == hm0[t / 64]);
                } else {
                    let k = t - 64 * w;
                    assert(t / 64 == w as int && t % 64 == k) by {
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(t, 64, w as int, k);
                    }
                    assert(k < take);
                    assert(!bit(m, k as u64));
                    assert(wd@[k] == lc@[t]);
                }
            }
        }
        rest = r2;
        w = w + 1;
    }
}

// ------------------------------------------------------------------------------------------------ lowest bit

/// Position of the lowest set bit of `m` (any position below 64 when `m` is 0): a de Bruijn table guess.
#[inline(always)]
fn low_pos(m: u64) -> (r: u64)
    ensures r < 64,
    no_unwind
{
    let db: [u8; 64] = [
        0, 1, 48, 2, 57, 49, 28, 3, 61, 58, 50, 42, 38, 29, 17, 4, 62, 55, 59, 36, 53, 51, 43, 22, 45, 39, 33, 30,
        24, 18, 12, 5, 63, 47, 56, 27, 60, 41, 37, 16, 54, 35, 52, 21, 44, 32, 23, 11, 46, 26, 40, 15, 34, 20, 31, 10,
        25, 14, 19, 9, 13, 8, 7, 6,
    ];
    let low = m & (0u64.wrapping_sub(m));
    let h = low.wrapping_mul(0x03f7_9d71_b4cb_0a89u64);
    let i = (h >> 58u64) as usize;
    proof {
        assert(h >> 58u64 < 64u64) by (bit_vector);
    }
    let p = db[i] as u64;
    if p < 64 { p } else { 0 }
}

/// The lowest set bit of `m`, checked (`ok`): bit `b` is set, every bit below it is clear, and `next` is `m`
/// without bit `b`.
#[inline(always)]
fn lowest(m: u64) -> (r: (u64, bool, u64))
    ensures
        r.0 < 64,
        r.1 ==> bit(m, r.0),
        r.1 ==> forall|k: u64| k < r.0 ==> !#[trigger] bit(m, k),
        r.1 ==> !bit(r.2, r.0),
        r.1 ==> forall|k: u64| k < 64 && k != r.0 ==> #[trigger] bit(r.2, k) == bit(m, k),
    no_unwind
{
    if m == 0 {
        return (0, false, 0);
    }
    let b = low_pos(m);
    let low = m & !(m - 1);
    let next = m & (m - 1);
    let ok = low == (1u64 << b);
    proof {
        if ok {
            assert(m != 0 && b < 64 && m & !sub(m, 1u64) == (1u64 << b) ==> (m >> b) & 1u64 == 1u64) by (bit_vector);
            assert forall|k: u64| k < b implies !#[trigger] bit(m, k) by {
                assert(m != 0 && b < 64 && k < b && m & !sub(m, 1u64) == (1u64 << b) ==> (m >> k) & 1u64 == 0u64) by (bit_vector);
            }
            assert(m != 0 && b < 64 && m & !sub(m, 1u64) == (1u64 << b) ==> ((m & sub(m, 1u64)) >> b) & 1u64 == 0u64) by (bit_vector);
            assert forall|k: u64| k < 64 && k != b implies #[trigger] bit(next, k) == bit(m, k) by {
                assert(m != 0 && b < 64 && k < 64 && k != b && m & !sub(m, 1u64) == (1u64 << b)
                    ==> ((m & sub(m, 1u64)) >> k) & 1u64 == (m >> k) & 1u64) by (bit_vector);
            }
        }
    }
    (b, ok, next)
}

// ------------------------------------------------------------------------------------------------ candidates

/// Orders row `q` with customer row `r`: `r < n_c` is the row of the order's customer key, else the order's
/// customer key has no row.
pub open spec fn cq_ok(c: Cols, x: Ctx, q: int, r: int) -> bool {
    &&& 0 <= q < c.n_o
    &&& r < c.n_c ==> q_cls(c, x, q) == nat_cls(x, cnat(c, r)) && in_i64(cnat(c, r))
    &&& r >= c.n_c ==> q_cls(c, x, q) == 0
}

/// A line without a class is in no group.
proof fn lemma_no_class(c: Cols, x: Ctx, j: int)
    requires l_scw(c, x, j) == 0,
    ensures l_grp(c, x, j) == -1,
{
}

/// Lines `[m, b)` in no group extend a candidate list's range.
proof fn lemma_lr_gap(c: Cols, x: Ctx, js: Seq<usize>, n: int, a: int, m: int, b: int)
    requires
        a <= m <= b,
        lr_eq(c, x, js, n, a, m),
        forall|j: int| m <= j < b ==> #[trigger] l_grp(c, x, j) == -1,
    ensures lr_eq(c, x, js, n, a, b),
{
    assert forall|gi: int| 0 <= gi < 4 implies {
        &&& #[trigger] lcnt(c, x, gi, js, n) == rcnt(c, x, gi, a, b)
        &&& lsum(c, x, gi, js, n) == rsum(c, x, gi, a, b)
        &&& lmass(c, x, gi, js, n) == rmass(c, x, gi, a, b)
    } by {
        assert(lcnt(c, x, gi, js, n) == rcnt(c, x, gi, a, m));
        assert(lsum(c, x, gi, js, n) == rsum(c, x, gi, a, m));
        assert(lmass(c, x, gi, js, n) == rmass(c, x, gi, a, m));
        lemma_r_split(c, x, gi, a, m, b);
        lemma_r_none(c, x, gi, m, b);
    }
}

/// Appending line `j` (the range's next line) to the list extends its range by one.
proof fn lemma_lr_take(c: Cols, x: Ctx, js0: Seq<usize>, js: Seq<usize>, n: int, a: int, j: usize)
    requires
        a <= j,
        0 <= n < js.len(), js0.len() == js.len(),
        forall|i: int| 0 <= i < n ==> js[i] == js0[i],
        js[n] == j,
        lr_eq(c, x, js0, n, a, j as int),
    ensures lr_eq(c, x, js, n + 1, a, j + 1),
{
    assert forall|gi: int| 0 <= gi < 4 implies {
        &&& #[trigger] lcnt(c, x, gi, js, n + 1) == rcnt(c, x, gi, a, j + 1)
        &&& lsum(c, x, gi, js, n + 1) == rsum(c, x, gi, a, j + 1)
        &&& lmass(c, x, gi, js, n + 1) == rmass(c, x, gi, a, j + 1)
    } by {
        lemma_l_ext(c, x, gi, js, js0, n);
        assert(lcnt(c, x, gi, js0, n) == rcnt(c, x, gi, a, j as int));
        assert(lsum(c, x, gi, js0, n) == rsum(c, x, gi, a, j as int));
        assert(lmass(c, x, gi, js0, n) == rmass(c, x, gi, a, j as int));
        lemma_r_step(c, x, gi, a, j as int);
    }
}

/// The customer row of stored orders row `q` (dense customer keys `[ck0, ck_hi]`; `n_c` when the key has none).
#[inline(always)]
fn cust_row(c: &Cols, s: Shifts, ck0: i64, ck_hi: i64, q: usize, Ghost(x): Ghost<Ctx>) -> (r: usize)
    requires
        cols_ok(*c), shifts_ok(*c, s),
        0 < c.n_c < usize::MAX / 32, ck_hi == ck0 + c.n_c - 1, c_dense_ok(*c, true, ck0),
        q < c.n_o,
    ensures cq_ok(*c, x, q as int, r as int),
    no_unwind
{
    proof {
        lemma_div_below(q as int, c.bs_o as int, c.oc_bases@.len() as int, c.n_o as int);
        assert(in_i64(ocust(*c, q as int)));
    }
    let og = div_bs(q, c.bs_o, s.sh_o, s.pow_o);
    let ck = c.oc_bases[og] + c.oc_codes[q] as i64;
    if ck0 <= ck && ck <= ck_hi {
        let r = (ck - ck0) as usize;
        proof {
            assert(ck == ocust(*c, q as int));
            assert(in_i64(cnat(*c, r as int)));
            assert(ckey(*c, r as int) == ck);
            assert(has_c(*c, ck as int));
            let w = crow(*c, ck as int);
            assert(0 <= w < c.n_c && ckey(*c, w) == ck);
            assert(w == r);
        }
        r
    } else {
        proof {
            assert(ck == ocust(*c, q as int));
            assert forall|t: int| 0 <= t < c.n_c implies #[trigger] ckey(*c, t) != ck by {
                assert(ckey(*c, t) == ck0 + t);
            }
            assert(!has_c(*c, ck as int));
        }
        c.n_c
    }
}

/// What `pick_hits` returns: the candidate count, the run cursor after the batch, and whether it holds.
pub type PickOut = (usize, usize, bool);

/// The facts of the candidates `[0, nc)` of the lines `[jb, pos)`: their sums are the range's; each is a line of
/// run `qs[i]` (between the cursors `r0` and `r`), whose index as an orders row has customer row `cp[i]`.
#[verifier::opaque]
pub open spec fn picks_ok(c: Cols, x: Ctx, cj: Seq<usize>, cp: Seq<usize>, qs: Seq<int>, nc: int, jb: int, pos: int,
    r0: int, r: int) -> bool
{
    &&& 0 <= nc <= pos - jb
    &&& cj.len() == BATCH && cp.len() == BATCH
    &&& qs.len() == nc
    &&& lr_eq(c, x, cj, nc, jb, pos)
    &&& forall|i: int| 0 <= i < nc ==> jb <= #[trigger] cj[i] < pos
    &&& forall|i: int| 0 <= i < nc ==> r0 <= #[trigger] qs[i] <= r
    &&& forall|i: int| 0 <= i < nc ==> #[trigger] qs[i] + 1 < c.l_st@.len()
    &&& forall|i: int| 0 <= i < nc ==> c.l_st@[#[trigger] qs[i]] <= cj[i] < c.l_st@[qs[i] + 1]
    &&& forall|i: int| 0 <= i < nc ==> #[trigger] cq_ok(c, x, qs[i], cp[i] as int)
}

/// No candidate yet.
proof fn lemma_picks_empty(c: Cols, x: Ctx, cj: Seq<usize>, cp: Seq<usize>, jb: int, r0: int)
    requires cj.len() == BATCH, cp.len() == BATCH,
    ensures picks_ok(c, x, cj, cp, Seq::<int>::empty(), 0, jb, jb, r0, r0),
{
    reveal(picks_ok);
    assert forall|gi: int| 0 <= gi < 4 implies {
        &&& #[trigger] lcnt(c, x, gi, cj, 0) == rcnt(c, x, gi, jb, jb)
        &&& lsum(c, x, gi, cj, 0) == rsum(c, x, gi, jb, jb)
        &&& lmass(c, x, gi, cj, 0) == rmass(c, x, gi, jb, jb)
    } by {}
}

/// Lines `[pos, pos2)` in no group extend the candidates' range.
proof fn lemma_picks_gap(c: Cols, x: Ctx, cj: Seq<usize>, cp: Seq<usize>, qs: Seq<int>, nc: int, jb: int, pos: int,
    pos2: int, r0: int, r: int)
    requires
        picks_ok(c, x, cj, cp, qs, nc, jb, pos, r0, r),
        pos <= pos2,
        forall|j: int| pos <= j < pos2 ==> #[trigger] l_grp(c, x, j) == -1,
    ensures picks_ok(c, x, cj, cp, qs, nc, jb, pos2, r0, r),
{
    reveal(picks_ok);
    lemma_lr_gap(c, x, cj, nc, jb, pos, pos2);
}

/// A later cursor keeps the candidates' facts.
proof fn lemma_picks_cursor(c: Cols, x: Ctx, cj: Seq<usize>, cp: Seq<usize>, qs: Seq<int>, nc: int, jb: int, pos: int,
    r0: int, r: int, r2: int)
    requires picks_ok(c, x, cj, cp, qs, nc, jb, pos, r0, r), r <= r2,
    ensures picks_ok(c, x, cj, cp, qs, nc, jb, pos, r0, r2),
{
    reveal(picks_ok);
}

/// Lines `[p, q)` of the batch whose hit bits are clear are in no group.
proof fn lemma_clear_gap(c: Cols, x: Ctx, lc: Seq<u8>, hm: Seq<u64>, n: int, jb: int, w: int, rest: u64, p: int, q: int)
    requires
        hits_ok(lc, hm, n),
        forall|t: int| 0 <= t < n ==> #[trigger] lc[t] as int == l_scw(c, x, jb + t),
        0 <= w < hm.len(), 0 <= p <= q <= 64, 64 * w + q <= n,
        forall|k: u64| p <= k < 64 ==> (#[trigger] bit(rest, k) == bit(hm[w], k)),
        forall|k: u64| p <= k < q ==> !#[trigger] bit(rest, k),
    ensures forall|j: int| jb + 64 * w + p <= j < jb + 64 * w + q ==> #[trigger] l_grp(c, x, j) == -1,
{
    assert forall|j: int| jb + 64 * w + p <= j < jb + 64 * w + q implies #[trigger] l_grp(c, x, j) == -1 by {
        let t = j - jb;
        let k = t - 64 * w;
        assert(t / 64 == w && t % 64 == k) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(t, 64, w, k);
        }
        assert(!bit(rest, k as u64));
        assert(bit(rest, k as u64) == bit(hm[w], k as u64));
        assert(!bit(hm[t / 64], (t % 64) as u64));
        assert(lc[t] == 0);
        lemma_no_class(c, x, j);
    }
}

/// Candidate line `j` (the candidates' next line): the cursor steps to its run, whose index (an orders row) gives
/// the customer row. `None` when the line has no run or the index is past the orders.
#[inline(always)]
fn take_line(c: &Cols, s: Shifts, ck0: i64, ck_hi: i64, jb: usize, j: usize, r0: usize, r: usize, nc: usize,
    cand_j: &mut Vec<usize>, cand_p: &mut Vec<usize>, Ghost(qs): Ghost<Seq<int>>, Ghost(x): Ghost<Ctx>)
    -> (out: (Option<usize>, Ghost<Seq<int>>))
    requires
        cols_ok(*c), shifts_ok(*c, s), runs_ok(*c), inc(c.l_st@),
        0 < c.n_c < usize::MAX / 32, ck_hi == ck0 + c.n_c - 1, c_dense_ok(*c, true, ck0),
        picks_ok(*c, x, old(cand_j)@, old(cand_p)@, qs, nc as int, jb as int, j as int, r0 as int, r as int),
        r0 <= r < c.l_st@.len(), c.l_st@[r as int] <= j, j <= 0xffff_ffff, jb <= j < jb + BATCH,
    ensures
        final(cand_j)@.len() == BATCH, final(cand_p)@.len() == BATCH,
        out.0 matches Some(r2) ==> nc < BATCH && r <= r2 && c.l_st@[r2 as int] <= j && r2 + 1 < c.l_st@.len()
            && picks_ok(*c, x, final(cand_j)@, final(cand_p)@, out.1@, nc + 1, jb as int, j + 1, r0 as int, r2 as int),
    no_unwind
{
    proof {
        reveal(picks_ok);
    }
    let r2 = step_le(c.l_st, c.n_st, r, j as u32);
    if r2 + 1 >= c.n_st || r2 >= c.n_o {
        return (None, Ghost(qs));
    }
    let cr = cust_row(c, s, ck0, ck_hi, r2, Ghost(x));
    let ghost cj0 = cand_j@;
    let ghost cp0 = cand_p@;
    proof {
        assert(nc < BATCH);
    }
    crate::gendb_entry::work::put(cand_j, nc, j);
    crate::gendb_entry::work::put(cand_p, nc, cr);
    let ghost qs2 = qs.push(r2 as int);
    proof {
        lemma_lr_take(*c, x, cj0, cand_j@, nc as int, jb as int, j);
        assert forall|i: int| 0 <= i < nc + 1 implies {
            &&& jb <= #[trigger] cand_j@[i] < j + 1
            &&& r0 <= qs2[i] <= r2
            &&& qs2[i] + 1 < c.l_st@.len()
            &&& c.l_st@[qs2[i]] <= cand_j@[i] < c.l_st@[qs2[i] + 1]
            &&& cq_ok(*c, x, qs2[i], cand_p@[i] as int)
        } by {
            if i < nc {
                assert(cand_j@[i] == cj0[i] && cand_p@[i] == cp0[i] && qs2[i] == qs[i]);
            }
        }
        assert forall|i: int| 0 <= i < nc + 1 implies #[trigger] qs2[i] + 1 < c.l_st@.len() by {
            assert(jb <= cand_j@[i] < j + 1);
        }
        assert forall|i: int| 0 <= i < nc + 1 implies r0 <= #[trigger] qs2[i] <= r2 by {
            assert(jb <= cand_j@[i] < j + 1);
        }
        assert forall|i: int| 0 <= i < nc + 1 implies c.l_st@[#[trigger] qs2[i]] <= cand_j@[i] < c.l_st@[qs2[i] + 1] by {
            assert(jb <= cand_j@[i] < j + 1);
        }
        assert forall|i: int| 0 <= i < nc + 1 implies #[trigger] cq_ok(*c, x, qs2[i], cand_p@[i] as int) by {
            assert(jb <= cand_j@[i] < j + 1);
        }
        assert forall|i: int| 0 <= i < nc + 1 implies jb <= #[trigger] cand_j@[i] < j + 1 by {
            assert(jb <= cand_j@[i] < j + 1);
        }
    }
    (Some(r2), Ghost(qs2))
}

/// The bits of `rest` from `p` on are `m`'s, and the bits below `p` are clear.
pub open spec fn rest_ok(rest: u64, m: u64, p: int) -> bool {
    &&& forall|k: u64| p <= k < 64 ==> (#[trigger] bit(rest, k) == bit(m, k))
    &&& forall|k: u64| k < p ==> !#[trigger] bit(rest, k)
}

/// Pass A2 over the lines `[jb, je)`: the lines with a hit bit are the candidates (`cand_j`), each with the customer
/// row of the orders row of its run's index (`cand_p`), the run cursor stepping from `r0`. Holds unless a line has
/// no run or a run index is past the orders.
#[inline(never)]
fn pick_hits(c: &Cols, s: Shifts, ck0: i64, ck_hi: i64, jb: usize, je: usize, lc: &[u8; BATCH], hm: &[u64; HW],
    r0: usize, cand_j: &mut Vec<usize>, cand_p: &mut Vec<usize>, Ghost(x): Ghost<Ctx>) -> (r: (PickOut, Ghost<Seq<int>>))
    requires
        cols_ok(*c), shifts_ok(*c, s), runs_ok(*c),
        0 < c.n_c < usize::MAX / 32, ck_hi == ck0 + c.n_c - 1, c_dense_ok(*c, true, ck0),
        jb < je <= c.n_l, je - jb <= BATCH, je <= 0xffff_ffff,
        forall|t: int| 0 <= t < je - jb ==> #[trigger] lc@[t] as int == l_scw(*c, x, jb + t),
        hits_ok(lc@, hm@, je - jb),
        r0 < c.l_st@.len(), c.l_st@[r0 as int] <= jb,
        old(cand_j)@.len() == BATCH, old(cand_p)@.len() == BATCH,
    ensures
        final(cand_j)@.len() == BATCH, final(cand_p)@.len() == BATCH,
        r.0.2 ==> picks_ok(*c, x, final(cand_j)@, final(cand_p)@, r.1@, r.0.0 as int, jb as int, je as int, r0 as int, r.0.1 as int),
        r.0.2 ==> r0 <= r.0.1 && r.0.1 + 1 < c.l_st@.len() && c.l_st@[r.0.1 as int] <= je - 1 < c.l_st@[r.0.1 + 1],
    no_unwind
{
    let n = je - jb;
    proof {
        lemma_runs_inc(*c);
        lemma_picks_empty(*c, x, cand_j@, cand_p@, jb as int, r0 as int);
    }
    let mut nc: usize = 0;
    let mut r = r0;
    let ghost mut qs: Seq<int> = Seq::empty();
    let mut w: usize = 0;
    while w * 64 < n
        invariant
            cols_ok(*c), shifts_ok(*c, s), runs_ok(*c), inc(c.l_st@),
            0 < c.n_c < usize::MAX / 32, ck_hi == ck0 + c.n_c - 1, c_dense_ok(*c, true, ck0),
            jb < je <= c.n_l, n == je - jb, n <= BATCH, je <= 0xffff_ffff,
            forall|t: int| 0 <= t < je - jb ==> #[trigger] lc@[t] as int == l_scw(*c, x, jb + t),
            hits_ok(lc@, hm@, n as int),
            r0 <= r < c.l_st@.len(), c.l_st@[r as int] < je,
            c.l_st@[r as int] <= jb + w * 64,
            cand_j@.len() == BATCH, cand_p@.len() == BATCH,
            w * 64 <= n + 63,
            picks_ok(*c, x, cand_j@, cand_p@, qs, nc as int, jb as int, if w * 64 < n { jb + w * 64 } else { je as int }, r0 as int, r as int),
        decreases n + 64 - w * 64,
    {
        let base = w * 64;
        proof {
            assert(w < HW) by (nonlinear_arith) requires w * 64 < n, n <= 4096;
        }
        let m = hm[w];
        let mut rest = m;
        let mut p: usize = 0;
        let lim: usize = if n - base < 64 { n - base } else { 64 };
        let mut done = false;
        // the lines [jb + base, jb + base + p) are taken
        while !done
            invariant
                cols_ok(*c), shifts_ok(*c, s), runs_ok(*c), inc(c.l_st@),
                0 < c.n_c < usize::MAX / 32, ck_hi == ck0 + c.n_c - 1, c_dense_ok(*c, true, ck0),
                jb < je <= c.n_l, n == je - jb, n <= BATCH, je <= 0xffff_ffff,
                forall|t: int| 0 <= t < je - jb ==> #[trigger] lc@[t] as int == l_scw(*c, x, jb + t),
                hits_ok(lc@, hm@, n as int),
                w < HW, base == w * 64, base < n, lim == if n - base < 64 { n - base } else { 64 },
                m == hm@[w as int],
                p <= lim,
                done ==> p == lim,
                rest_ok(rest, m, p as int),
                r0 <= r < c.l_st@.len(), c.l_st@[r as int] < je,
                c.l_st@[r as int] <= jb + base + p,
                cand_j@.len() == BATCH, cand_p@.len() == BATCH,
                picks_ok(*c, x, cand_j@, cand_p@, qs, nc as int, jb as int, jb + base + p, r0 as int, r as int),
            decreases 64 - p + (if done { 0int } else { 1int }),
        {
            let (b, okb, next) = lowest(rest);
            let bu = b as usize;
            if !okb || bu >= lim {
                // no more set bits below lim (rest is 0 or its lowest bit is past the batch's lines here)
                if okb || rest == 0 {
                    proof {
                        assert forall|k: u64| p <= k < lim implies !#[trigger] bit(rest, k) by {
                            if rest == 0 {
                                assert(rest == 0u64 ==> (rest >> k) & 1u64 == 0u64) by (bit_vector);
                            }
                        }
                        lemma_clear_gap(*c, x, lc@, hm@, n as int, jb as int, w as int, rest, p as int, lim as int);
                        lemma_picks_gap(*c, x, cand_j@, cand_p@, qs, nc as int, jb as int, jb + base + p, jb + base + lim, r0 as int, r as int);
                    }
                    p = lim;
                    done = true;
                } else {
                    return ((0, r0, false), Ghost(Seq::<int>::empty()));
                }
            } else {
                if bu < p {
                    // impossible: the bits below p are clear
                    return ((0, r0, false), Ghost(Seq::<int>::empty()));
                }
                // the lines [p, b) have clear bits
                proof {
                    lemma_clear_gap(*c, x, lc@, hm@, n as int, jb as int, w as int, rest, p as int, bu as int);
                    lemma_picks_gap(*c, x, cand_j@, cand_p@, qs, nc as int, jb as int, jb + base + p, jb + base + bu, r0 as int, r as int);
                }
                let j = jb + base + bu;
                let (r2o, qs2) = take_line(c, s, ck0, ck_hi, jb, j, r0, r, nc, cand_j, cand_p, Ghost(qs), Ghost(x));
                match r2o {
                    Some(r2) => {
                        proof {
                            qs = qs2@;
                            assert forall|k: u64| bu + 1 <= k < 64 implies (#[trigger] bit(next, k) == bit(m, k)) by {
                                assert(bit(next, k) == bit(rest, k));
                            }
                            assert forall|k: u64| k < bu + 1 implies !#[trigger] bit(next, k) by {
                                if k < b {
                                    assert(!bit(rest, k));
                                    assert(bit(next, k) == bit(rest, k));
                                }
                            }
                        }
                        nc = nc + 1;
                        r = r2;
                        rest = next;
                        p = bu + 1;
                    },
                    None => {
                        return ((0, r0, false), Ghost(Seq::<int>::empty()));
                    },
                }
            }
        }
        proof {
            if lim < 64 {
                assert(base + lim == n);
            }
        }
        w = w + 1;
    }
    // the cursor at the batch's last line
    let re = step_le(c.l_st, c.n_st, r, (je - 1) as u32);
    if re + 1 >= c.n_st {
        return ((0, r0, false), Ghost(Seq::<int>::empty()));
    }
    proof {
        lemma_picks_cursor(*c, x, cand_j@, cand_p@, qs, nc as int, jb as int, je as int, r0 as int, r as int, re as int);
    }
    ((nc, re, true), Ghost(qs))
}

} // verus!

verus! {

// ------------------------------------------------------------------------------------------------ the batch

/// The scan facts the supplier-first path needs: co-clustered lines with their run starts, dense customer and
/// supplier keys with their class maps (`sma` the fixed-size copy of `sm2`).
pub open spec fn sfast_ok(c: Cols, s: Shifts, sk0: i64, ck0: i64, cm: Seq<u32>, sm2: Seq<u32>, sma: Seq<u32>, x: Ctx) -> bool {
    &&& cols_ok(c)
    &&& keys_ok(c)
    &&& shifts_ok(c, s)
    &&& clus_ok(c)
    &&& runs_ok(c)
    &&& cmap_ok(c, x, ck0, cm)
    &&& smap2_ok(c, x, sk0, sm2)
    &&& smap2_ok(c, x, sk0, sma)
    &&& 0 < c.n_c < usize::MAX / 32
    &&& ck0 + c.n_c - 1 <= i64::MAX
    &&& 0 < c.n_s <= 16 * SMW
}

/// The order key of stored line `p`.
fn lkey_at(c: &Cols, p: usize) -> (k: i64)
    requires cols_ok(*c), p < c.n_l,
    ensures k == lkey(*c, p as int),
    no_unwind
{
    proof {
        lemma_div_below(p as int, c.bs_l as int, c.lok_bases@.len() as int, c.n_l as int);
        assert(in_i64(lkey(*c, p as int)));
    }
    let g = p / c.bs_l;
    c.lok_bases[g] + c.lok_codes[p] as i64
}

/// The order key of stored orders row `q`.
fn okey_at(c: &Cols, s: Shifts, q: usize) -> (k: i64)
    requires cols_ok(*c), shifts_ok(*c, s), q < c.n_o,
    ensures k == okey(*c, q as int),
    no_unwind
{
    proof {
        lemma_div_below(q as int, c.bs_o as int, c.ok_bases@.len() as int, c.n_o as int);
        assert(in_i64(okey(*c, q as int)));
    }
    let g = div_bs(q, c.bs_o, s.sh_o, s.pow_o);
    c.ok_bases[g] + c.ok_codes[q] as i64
}

/// The year slot of every line of group `g` when the zone map fixes it (0: all in 1995 or before, 1: all in 1996
/// or after), else 2.
pub open spec fn yfix_ok(c: Cols, g: int, yf: u8) -> bool {
    &&& yf <= 2
    &&& yf == 0 ==> c.ls_zmax@[g] < day_1996()
    &&& yf == 1 ==> c.ls_bases@[g] >= day_1996()
}

/// Passes C and D in one: each candidate's pair from its supplier class (`lc`) and its order's customer class
/// (`cc`); only a line of a pair reads its shipdate (unless the zone map fixes the year), price and discount, and
/// is added to its group.
#[inline(never)]
fn add_hits(c: &Cols, same: bool, g: usize, jb: usize, nc: usize, cand_j: &Vec<usize>, lc: &[u8; BATCH],
    cc: &[u8; BATCH], yf: u8, sums: Vec<i128>, mass: Vec<i128>, cnts: Vec<usize>, over: bool,
    Ghost(x): Ghost<Ctx>, Ghost(a): Ghost<int>, Ghost(je): Ghost<int>) -> (r: ScanOut)
    requires
        cols_ok(*c),
        x.same == same,
        g < c.ls_bases@.len(),
        yfix_ok(*c, g as int, yf),
        0 <= a <= jb <= je <= c.n_l,
        nc <= BATCH, nc <= je - jb, je - jb <= BATCH,
        forall|j: int| jb <= j < je ==> #[trigger] (j / c.bs_l as int) == g,
        cand_j@.len() == BATCH,
        forall|t: int| 0 <= t < nc ==> jb <= #[trigger] cand_j@[t] < je,
        forall|t: int| 0 <= t < je - jb ==> #[trigger] lc@[t] as int == l_scw(*c, x, jb + t),
        forall|t: int| 0 <= t < nc ==> #[trigger] cc@[t] as int == o_cls(*c, x, lkey(*c, cand_j@[t] as int)),
        forall|t: int| 0 <= t < nc ==> #[trigger] cc@[t] < 4,
        acc_ok(*c, x, sums@, mass@, cnts@, over, a, jb as int, cand_j@, 0),
    ensures
        acc_ok(*c, x, r.0@, r.1@, r.2@, r.3, a, jb as int, cand_j@, nc as int),
    no_unwind
{
    let sbase = c.ls_bases[g];
    let pbase = c.lp_bases[g];
    let dbase = c.ld_bases[g];
    let mut sums = sums;
    let mut mass = mass;
    let mut cnts = cnts;
    let mut over = over;
    let mut i: usize = 0;
    while i < nc
        invariant
            cols_ok(*c),
            x.same == same,
            g < c.ls_bases@.len(),
            yfix_ok(*c, g as int, yf),
            0 <= a <= jb <= je <= c.n_l,
            i <= nc, nc <= BATCH, nc <= je - jb, je - jb <= BATCH,
            forall|j: int| jb <= j < je ==> #[trigger] (j / c.bs_l as int) == g,
            sbase == c.ls_bases@[g as int], pbase == c.lp_bases@[g as int], dbase == c.ld_bases@[g as int],
            cand_j@.len() == BATCH,
            forall|t: int| 0 <= t < nc ==> jb <= #[trigger] cand_j@[t] < je,
            forall|t: int| 0 <= t < je - jb ==> #[trigger] lc@[t] as int == l_scw(*c, x, jb + t),
            forall|t: int| 0 <= t < nc ==> #[trigger] cc@[t] as int == o_cls(*c, x, lkey(*c, cand_j@[t] as int)),
            forall|t: int| 0 <= t < nc ==> #[trigger] cc@[t] < 4,
            acc_ok(*c, x, sums@, mass@, cnts@, over, a, jb as int, cand_j@, i as int),
        decreases nc - i,
    {
        let jj = cand_j[i];
        let ccv = cc[i];
        proof {
            assert(jb <= jj < je);
            assert(lc@[jj - jb] as int == l_scw(*c, x, jb + (jj - jb)));
            assert(jj as int / c.bs_l as int == g as int);
            assert(in_i64(lship(*c, jj as int)));
        }
        let sc = lc[jj - jb];
        let p0 = sc % 2 == 1 && ccv >= 2;
        let p1 = !same && sc >= 2 && ccv % 2 == 1;
        if p0 || p1 {
            // a class means the line ships in the window
            proof {
                assert(sc != 0);
                assert(win_lo() <= lship(*c, jj as int) <= win_hi());
                assert(sc as int == s_cls(*c, x, lsupp(*c, jj as int)));
                assert(lship(*c, jj as int) == sbase + c.ls_codes@[jj as int] as int);
                assert(lship(*c, jj as int) <= c.ls_zmax@[g as int]);
            }
            let yi: usize = if yf < 2 { yf as usize } else if sbase + c.ls_codes[jj] as i64 >= -1461 { 1 } else { 0 };
            let gi: usize = if p0 { yi } else { 2 + yi };
            proof {
                assert(yi as int == yslot(lship(*c, jj as int)));
                assert(l_grp(*c, x, jj as int) == gi as int);
                assert(small15(lprice(*c, jj as int)) && small15(ldisc(*c, jj as int)));
            }
            let price = pbase + c.lp_codes[jj] as i64;
            let disc = dbase + c.ld_codes[jj] as i64;
            proof {
                assert(price == lprice(*c, jj as int) && disc == ldisc(*c, jj as int));
                lemma_vol_bound(price as int, disc as int);
            }
            let vol: i128 = price as i128 * (100 - disc as i128);
            let (s2, m2, c2, o2) = add_line(sums, mass, cnts, over, gi, vol,
                Ghost(*c), Ghost(x), Ghost(a), Ghost(jb as int), Ghost(cand_j@), Ghost(i as int));
            sums = s2;
            mass = m2;
            cnts = c2;
            over = o2;
        } else {
            proof {
                assert(l_grp(*c, x, cand_j@[i as int] as int) == -1);
                lemma_acc_skip(*c, x, sums@, mass@, cnts@, over, a, jb as int, cand_j@, i as int);
            }
        }
        i = i + 1;
    }
    (sums, mass, cnts, over)
}

/// What `sfast_batch` returns: the accumulators, whether the batch was taken, and the run cursor.
pub type SfastOut = (ScanOut, bool, usize);

/// The supplier-first path over the lines `[jb, je)` of group `g` (see the module header), from run cursor `rp`.
/// When it does not hold (`r.1` false) the accumulators come back unchanged for the caller's line-first passes.
pub fn sfast_batch(c: &Cols, s: Shifts, sk0: i64, ck0: i64, cm: &Vec<u32>, sm2: &Vec<u32>, sma: &[u32; SMW],
    same: bool, g: usize, jb: usize, je: usize, inside: bool, rp: usize,
    sums: Vec<i128>, mass: Vec<i128>, cnts: Vec<usize>, over: bool,
    lc: &mut [u8; BATCH], hm: &mut [u64; HW], cc: &mut [u8; BATCH],
    cand_j: &mut Vec<usize>, cand_p: &mut Vec<usize>, cand_x: &mut Vec<u8>,
    Ghost(x): Ghost<Ctx>, Ghost(a): Ghost<int>) -> (r: SfastOut)
    requires
        sfast_ok(*c, s, sk0, ck0, cm@, sm2@, sma@, x),
        x.same == same,
        g < c.ls_bases@.len(),
        jb < je <= c.n_l, je - jb <= BATCH,
        forall|j: int| jb <= j < je ==> #[trigger] (j / c.bs_l as int) == g,
        inside ==> c.ls_bases@[g as int] >= win_lo() && c.ls_zmax@[g as int] <= win_hi(),
        rp < c.l_st@.len(), c.l_st@[rp as int] <= jb,
        0 <= a <= jb,
        acc_ok(*c, x, sums@, mass@, cnts@, over, a, jb as int, Seq::<usize>::empty(), 0),
        old(cand_j)@.len() == BATCH, old(cand_p)@.len() == BATCH, old(cand_x)@.len() == BATCH,
    ensures
        final(cand_j)@.len() == BATCH, final(cand_p)@.len() == BATCH, final(cand_x)@.len() == BATCH,
        r.1 ==> acc_ok(*c, x, r.0.0@, r.0.1@, r.0.2@, r.0.3, a, je as int, Seq::<usize>::empty(), 0),
        !r.1 ==> r.0.0@ == sums@ && r.0.1@ == mass@ && r.0.2@ == cnts@ && r.0.3 == over,
        r.2 < c.l_st@.len(), c.l_st@[r.2 as int] <= je,
    no_unwind
{
    let ck_hi = ck0 + (c.n_c as i64 - 1);
    // pass A1: the lines' classes
    if inside {
        if !line_classes_in(c, sk0, sma, g, jb, je, lc, Ghost(x)) {
            return ((sums, mass, cnts, over), false, rp);
        }
    } else {
        if !line_classes_edge(c, sk0, sma, g, jb, je, lc, Ghost(x)) {
            return ((sums, mass, cnts, over), false, rp);
        }
    }
    // pass A2: the hit lines and their runs' customer rows
    if je > 0xffff_ffff {
        return ((sums, mass, cnts, over), false, rp);
    }
    hit_mask(lc, je - jb, hm);
    let ((nc, re, ok), qs) = pick_hits(c, s, ck0, ck_hi, jb, je, lc, hm, rp, cand_j, cand_p, Ghost(x));
    if !ok || re >= c.n_o {
        return ((sums, mass, cnts, over), false, rp);
    }
    // the check: the first and the last run start with their orders rows' keys
    proof {
        reveal(picks_ok);
        lemma_runs_inc(*c);
        lemma_inc(c.l_st@, rp as int, re as int);
        assert(run_ok(*c, rp as int));
        assert(run_ok(*c, re as int));
    }
    let k0 = lkey_at(c, c.l_st[rp] as usize);
    let k1 = lkey_at(c, c.l_st[re] as usize);
    if k0 != okey_at(c, s, rp) || k1 != okey_at(c, s, re) {
        return ((sums, mass, cnts, over), false, rp);
    }
    proof {
        reveal(picks_ok);
        lemma_aligned_range(*c, rp as int, re as int);
        assert forall|i: int| 0 <= i < nc implies #[trigger] cr_ok(*c, x, lkey(*c, cand_j@[i] as int), cand_p@[i] as int) by {
            let q = qs@[i];
            assert(rp <= q <= re);
            assert(aligned(*c, q));
            assert(cq_ok(*c, x, q, cand_p@[i] as int));
            lemma_line_run(*c, x, q, cand_j@[i] as int);
        }
    }
    // passes B to D: customer classes, group codes, sums
    proof {
        assert(16 * cm@.len() >= c.n_c);
    }
    cust_kernel(cand_p, c.n_c, cm, cc, nc);
    proof {
        // each candidate's customer class is its order's
        assert forall|t: int| 0 <= t < nc implies #[trigger] cc@[t] as int == o_cls(*c, x, lkey(*c, cand_j@[t] as int)) && cc@[t] < 4 by {
            let cr = cand_p@[t] as int;
            assert(cr_ok(*c, x, lkey(*c, cand_j@[t] as int), cr));
            if cr < c.n_c {
                lemma_map_row(x, c.cn_bases@, c.cn_codes@, c.bs_c as int, c.n_c as int, cm@, cr);
                assert(cnat(*c, cr) == nat_of(c.cn_bases@, c.cn_codes@, c.bs_c as int, cr));
                assert(get2(cm@[cr / 16], cr % 16) < 4) by {
                    let w = cm@[cr / 16];
                    let sh = (2 * (cr % 16)) as u32;
                    assert((w >> sh) & 3u32 < 4u32) by (bit_vector);
                }
            }
        }
        lemma_acc_list0(*c, x, sums@, mass@, cnts@, over, a, jb as int, cand_j@);
    }
    // the year of every line when the zone map fixes it
    let yf: u8 = if c.ls_zmax[g] < -1461 { 0 } else if c.ls_bases[g] >= -1461 { 1 } else { 2 };
    let (s2, m2, c2, o2) = add_hits(c, same, g, jb, nc, cand_j, lc, cc, yf, sums, mass, cnts, over,
        Ghost(x), Ghost(a), Ghost(je as int));
    proof {
        lemma_acc_batch(*c, x, s2@, m2@, c2@, o2, a, jb as int, je as int, cand_j@, nc as int);
    }
    ((s2, m2, c2, o2), true, re)
}

} // verus!
