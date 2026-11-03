//! Scan of a row group of facts' lineitem rows through the bitmap indexes of storage `li_bits`.
//!
//! A group whose rows fill whole 64-row words is described by a plan `Gw`: the words of the discount bitmaps of
//! the keys `dlo`, `dlo + 1`, `dlo + 2` (`a`, `b`, `c`; `dhi = dlo + 2`), of the quantity bitmap of the key `qhi`
//! (`q`) and, in a group the zone map does not place inside the date range, of the shipdate bitmaps of the keys
//! `lo` / `hi` (`l`, `h`). Per word they give the qualifying rows `any = (a | b | c) & q & s` and their discount
//! `dlo + [b] + 2 [c]`; only the price codes of qualifying rows are read (`word_sum` visits the set bits of
//! `any`: lowest set bit, `x & (x - 1)`). `gw_pair` scans two groups word by word together: two independent
//! memory streams keep more cache-line fetches in flight on one thread.
//!
//! Per row `j` of a group, the plan states what each bitmap bit means about `xs[j]` (`gw_bit_ok`); every
//! function returns the accumulators of `link::query` over its rows (`gsum` = `gabs`: every product is
//! non-negative, and `gcount`).
use vstd::prelude::*;
use vstd::std_specs::bits::u64_trailing_zeros;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::link::query::*;
use crate::link::expr::ival;
use crate::gendb_entry::layout::PartView;
use crate::stores::facts::interface::common::colfmt::group_of;
use super::common::bitwords::*;
use super::norm::*;
use super::scan::{Bnd, qs, lemma_hit, lemma_no_hits};

verus! {

/// The bitmaps of li_bits selected for the binding: the bitmap parts and the word offsets of the selected
/// bitmaps (`oa`, `ob`, `oc`: discount keys `dlo`, `dlo + 1`, `dlo + 2`; `oq`: quantity key `qhi`).
#[derive(Clone, Copy)]
pub struct Bits {
    pub dbits: &'static [u64],
    pub qbits: &'static [u64],
    pub sbits: &'static [u64],
    pub skeys: &'static [i64],
    /// Words per bitmap.
    pub nw: usize,
    /// Shipdate keys per row group.
    pub ns: usize,
    /// The bitmaps serve this binding.
    pub on: bool,
    pub oa: usize,
    pub ob: usize,
    pub oc: usize,
    pub oq: usize,
    /// `dlo` (at most 509).
    pub dlo: u32,
}

/// Bit of row `j` in the bitmap at word offset `off`.
pub open spec fn wbit(words: Seq<u64>, off: int, j: int) -> bool {
    bit64(words[off + j / 64], j % 64)
}

/// What the selected discount and quantity bitmaps state about row `j` (`xs[j]`), and its price code.
pub open spec fn row_bits_ok(bt: Bits, b: Bnd, xs: Seq<Row>, price: Seq<u32>, bp: int, j: int) -> bool {
    &&& wbit(bt.dbits@, bt.oa as int, j) == (ival(xs[j][2]) == b.dlo)
    &&& wbit(bt.dbits@, bt.ob as int, j) == (ival(xs[j][2]) == b.dlo + 1)
    &&& wbit(bt.dbits@, bt.oc as int, j) == (ival(xs[j][2]) == b.dlo + 2)
    &&& wbit(bt.qbits@, bt.oq as int, j) == (ival(xs[j][0]) < b.qhi)
    &&& ival(xs[j][1]) == bp + price[j]
}

/// The shipdate condition of row `j` from the shipdate bitmaps (offsets `ol`, `oh`) or the zone map.
pub open spec fn row_ship_ok(bt: Bits, b: Bnd, xs: Seq<Row>, need_lo: bool, ol: int, need_hi: bool, oh: int, j: int) -> bool {
    &&& if need_lo { wbit(bt.sbits@, ol, j) == (ival(xs[j][3]) < b.lo) } else { b.lo <= ival(xs[j][3]) }
    &&& if need_hi { wbit(bt.sbits@, oh, j) == (ival(xs[j][3]) < b.hi) } else { ival(xs[j][3]) < b.hi }
}

/// The binding's discount range is the three keys `dlo .. dlo + 2` of the lane kernel.
pub open spec fn bnd_bits_ok(bt: Bits, b: Bnd) -> bool {
    0 <= b.dlo && b.dlo <= 509 && b.dhi == b.dlo + 2 && bt.dlo == b.dlo
}

/// What the selected bitmaps state about the stored rows of facts' parts `parts`, for the binding `b` (when on).
pub open spec fn bits_rows_ok(bt: Bits, b: Bnd, parts: Seq<PartView>) -> bool {
    &&& bt.dbits@.len() <= usize::MAX && bt.qbits@.len() <= usize::MAX
    &&& bt.sbits@.len() <= usize::MAX && bt.skeys@.len() <= usize::MAX
    &&& bt.on ==> {
        let n = n_rows(parts);
        let nw = bt.nw as int;
        let ns = bt.ns as int;
        let gs = gsv(parts);
        &&& bnd_bits_ok(bt, b)
        &&& n <= nw * 64
        &&& bt.oa + nw <= bt.dbits@.len() && bt.ob + nw <= bt.dbits@.len() && bt.oc + nw <= bt.dbits@.len()
        &&& bt.oq + nw <= bt.qbits@.len()
        &&& bt.skeys@.len() == (gs.len() - 1) * ns
        &&& bt.sbits@.len() == ns * nw
        &&& forall|j: int| 0 <= j < n ==> {
            &&& #[trigger] wbit(bt.dbits@, bt.oa as int, j) == (disc_at(parts, j) == b.dlo)
            &&& wbit(bt.dbits@, bt.ob as int, j) == (disc_at(parts, j) == b.dlo + 1)
            &&& wbit(bt.dbits@, bt.oc as int, j) == (disc_at(parts, j) == b.dlo + 2)
            &&& wbit(bt.qbits@, bt.oq as int, j) == (qty_at(parts, j) < b.qhi)
        }
        &&& forall|t: int, j: int| 0 <= t < ns && 0 <= j < n ==> #[trigger] wbit(bt.sbits@, t * nw, j)
            == (ship_at(parts, j) < bt.skeys@[group_of(gs, j) * ns + t])
    }
}

/// One word's facts for `word_sum`: bit `i` of `any` is the hit of row `j0 + i`, whose product is
/// `(bp + p[i]) * (dlo + [mb] + 2 [mc])`.
pub open spec fn word_facts(g: QuerySpec, xs: Seq<Row>, j0: int, any: u64, mb: u64, mc: u64, dlo: int, bp: int, p: Seq<u32>) -> bool {
    forall|i: int| 0 <= i < 64 ==> {
        &&& hit(g, xs[j0 + i], ek()) == #[trigger] bit64(any, i)
        &&& bit64(any, i) ==> (g.arg)(0, xs[j0 + i]) == (bp + p[i]) * (dlo + b01(mb, i) + 2 * b01(mc, i))
    }
}

/// A product of a price below `2^33` and a discount factor below `2^9`.
proof fn lemma_term(bp: int, cp: int, e: int)
    requires 0 <= bp <= 0x1_0000_0000, 0 <= cp < 0x1_0000_0000, 0 <= e <= 512,
    ensures
        0 <= cp * e <= 0x1ff_ffff_fe00,
        (bp + cp) * e == cp * e + bp * e,
        0 <= (bp + cp) * e,
{
    assert(0 <= cp * e <= 0x1ff_ffff_fe00) by (nonlinear_arith) requires 0 <= cp <= 0xffff_ffff, 0 <= e <= 512;
    assert((bp + cp) * e == cp * e + bp * e) by (nonlinear_arith);
    assert(0 <= (bp + cp) * e) by (nonlinear_arith) requires 0 <= bp + cp, 0 <= e;
}

/// `bp * (se + e) == bp * se + bp * e`, and the bound of `bp * se`.
proof fn lemma_bp_terms(bp: int, se: int, e: int)
    requires 0 <= bp <= 0x1_0000_0000, 0 <= se <= 64 * 512,
    ensures bp * (se + e) == bp * se + bp * e, 0 <= bp * se <= 0x1_0000_0000 * (64 * 512),
{
    assert(bp * (se + e) == bp * se + bp * e) by (nonlinear_arith);
    assert(0 <= bp * se <= 0x1_0000_0000 * (64 * 512)) by (nonlinear_arith) requires 0 <= bp <= 0x1_0000_0000, 0 <= se <= 64 * 512;
}

/// The sums of one word's qualifying rows (`word_facts`), visiting the set bits of `any` only. Returns
/// `(sum, count)`. `fast` selects `trailing_zeros` for the bit index (may unwind: calling thread only).
#[inline(always)]
pub fn word_sum(tab: &[u8; 64], p: &[u32], any: u64, mb: u64, mc: u64, dlo: u32, bp: u64, fast: bool,
    Ghost(g): Ghost<QuerySpec>, Ghost(xs): Ghost<Seq<Row>>, Ghost(j0): Ghost<int>) -> (r: (u64, u64))
    requires
        tab@ == db_table(),
        p@.len() == 64,
        dlo <= 509,
        bp <= 0x1_0000_0000,
        0 <= j0, j0 + 64 <= xs.len(),
        word_facts(g, xs, j0, any, mb, mc, dlo as int, bp as int, p@),
    ensures
        r.0 == gsum(g, xs.subrange(j0, j0 + 64), ek(), 0),
        r.0 == gabs(g, xs.subrange(j0, j0 + 64), ek(), 0),
        r.1 == gcount(g, xs.subrange(j0, j0 + 64), ek()),
        r.0 <= 0x1_0000_0000_0000,
        r.1 <= 64,
    no_unwind when !fast
{
    let mut x = any;
    let mut s: u64 = 0;
    let mut se: u64 = 0;
    let mut cnt: u64 = 0;
    let d = dlo as u64;
    let ghost mut lo: int = 0;
    proof {
        lemma_empty(g, xs, j0, ek(), 0);
    }
    while x != 0
        invariant
            tab@ == db_table(),
            p@.len() == 64,
            dlo <= 509,
            d == dlo,
            bp <= 0x1_0000_0000,
            0 <= j0, j0 + 64 <= xs.len(),
            word_facts(g, xs, j0, any, mb, mc, dlo as int, bp as int, p@),
            0 <= lo <= 64,
            forall|i: int| 0 <= i < 64 ==> #[trigger] bit64(x, i) == (bit64(any, i) && i >= lo),
            s + bp * se == gsum(g, xs.subrange(j0, j0 + lo), ek(), 0),
            s + bp * se == gabs(g, xs.subrange(j0, j0 + lo), ek(), 0),
            cnt == gcount(g, xs.subrange(j0, j0 + lo), ek()),
            s <= lo * 0x1ff_ffff_fe00,
            se <= lo * 512,
            cnt <= lo,
        decreases 64 - lo,
    {
        let t = lowest_bit_sel(tab, x, fast);
        proof {
            lemma_lowest_bit(x);
            let ti = t as int;
            assert(bit64(x, ti));
            assert(ti >= lo);
            // rows lo .. t have no hit, row t has one
            assert forall|j: int| j0 + lo <= j < j0 + ti implies !#[trigger] hit(g, xs[j], ek()) by {
                let i = j - j0;
                assert(!bit64(x, i));
                assert(hit(g, xs[j0 + i], ek()) == bit64(any, i));
            }
            lemma_no_hits(g, xs, j0 + lo, j0 + ti);
            lemma_split(g, xs, j0, j0 + lo, j0 + ti, ek(), 0);
            lemma_range_step(g, xs, j0, j0 + ti, ek(), 0);
            assert(xs.subrange(j0, j0 + ti + 1) == xs.subrange(j0, j0 + (ti + 1)));
            assert(hit(g, xs[j0 + ti], ek()) == bit64(any, ti));
            lemma_bit_value(mb, t);
            lemma_bit_value(mc, t);
        }
        let cp = p[t as usize] as u64;
        let e = d + ((mb >> t) & 1) + 2 * ((mc >> t) & 1);
        proof {
            let ti = t as int;
            assert(e == dlo + b01(mb, ti) + 2 * b01(mc, ti));
            assert((g.arg)(0, xs[j0 + ti]) == (bp + p@[ti]) * e);
            lemma_term(bp as int, cp as int, e as int);
            lemma_bp_terms(bp as int, se as int, e as int);
        }
        s = s + cp * e;
        se = se + e;
        cnt = cnt + 1;
        x = x & (x - 1);
        proof {
            lo = t as int + 1;
        }
    }
    proof {
        lemma_const_words();
        assert forall|j: int| j0 + lo <= j < j0 + 64 implies !#[trigger] hit(g, xs[j], ek()) by {
            let i = j - j0;
            assert(!bit64(0u64, i));
            assert(hit(g, xs[j0 + i], ek()) == bit64(any, i));
        }
        lemma_no_hits(g, xs, j0 + lo, j0 + 64);
        lemma_split(g, xs, j0, j0 + lo, j0 + 64, ek(), 0);
        lemma_bp_terms(bp as int, se as int, 0);
    }
    (s + bp * se, cnt)
}

/// The facts of one word from the bitmap words `a, b, c` (discount `dlo`, `dlo + 1`, `dlo + 2`), `q` (quantity) and
/// `s` (shipdate), for the rows `64 w .. 64 w + 64` of a group.
proof fn lemma_word(bnd: Bnd, xs: Seq<Row>, price: Seq<u32>, bp: int, w: int, p: Seq<u32>,
    a: u64, b: u64, c: u64, q: u64, s: u64)
    requires
        bnd3(bnd),
        0 <= bp <= 0x1_0000_0000,
        0 <= w,
        64 * w + 64 <= xs.len(),
        64 * w + 64 <= price.len(),
        p == price.subrange(64 * w, 64 * w + 64),
        forall|i: int| 0 <= i < 64 ==> {
            let j = 64 * w + i;
            &&& #[trigger] bit64(a, i) == (ival(xs[j][2]) == bnd.dlo)
            &&& bit64(b, i) == (ival(xs[j][2]) == bnd.dlo + 1)
            &&& bit64(c, i) == (ival(xs[j][2]) == bnd.dlo + 2)
            &&& bit64(q, i) == (ival(xs[j][0]) < bnd.qhi)
            &&& bit64(s, i) == (bnd.lo <= ival(xs[j][3]) && ival(xs[j][3]) < bnd.hi)
            &&& ival(xs[j][1]) == bp + price[j]
        },
    ensures ({
        let m = q & s;
        word_facts(qs(bnd), xs, 64 * w, (a & m) | (b & m) | (c & m), b & m, c & m, bnd.dlo as int, bp, p)
    }),
{
    let m = q & s;
    let any = (a & m) | (b & m) | (c & m);
    assert forall|i: int| 0 <= i < 64 implies {
        &&& hit(qs(bnd), xs[64 * w + i], ek()) == #[trigger] bit64(any, i)
        &&& bit64(any, i) ==> (qs(bnd).arg)(0, xs[64 * w + i]) == (bp + p[i]) * (bnd.dlo + b01(b & m, i) + 2 * b01(c & m, i))
    } by {
        let j = 64 * w + i;
        lemma_bit_ops(q, s, i);
        lemma_bit_ops(a, m, i);
        lemma_bit_ops(b, m, i);
        lemma_bit_ops(c, m, i);
        lemma_bit_ops(a & m, b & m, i);
        lemma_bit_ops((a & m) | (b & m), c & m, i);
        lemma_hit(bnd, xs[j]);
        assert(bit64(a, i) == (ival(xs[j][2]) == bnd.dlo));
        assert(p[i] == price[j]);
    }
}

/// One row group scanned through the bitmaps: the selected bitmap words of its 64-row words `w0 .. w0 + nwg`
/// (`a`, `b`, `c`: discount keys `dlo`, `dlo + 1`, `dlo + 2`; `q`: quantity key `qhi`; `l`, `h`: the shipdate
/// keys `lo` / `hi` when `need_lo` / `need_hi`, otherwise any words of the right length, masked out by `ml` / `xh`)
/// and the group's price base `bp`.
#[derive(Clone, Copy)]
pub struct Gw {
    pub a: &'static [u64],
    pub b: &'static [u64],
    pub c: &'static [u64],
    pub q: &'static [u64],
    pub l: &'static [u64],
    pub h: &'static [u64],
    pub w0: usize,
    pub nwg: usize,
    pub bp: u64,
    /// `!0` when `need_lo`, else 0.
    pub ml: u64,
    /// 0 when `need_hi`, else `!0`.
    pub xh: u64,
    pub need_lo: bool,
    pub need_hi: bool,
}

/// The binding's discount range is the three keys `dlo .. dlo + 2` (`dlo` at most 509).
pub open spec fn bnd3(b: Bnd) -> bool {
    0 <= b.dlo && b.dlo <= 509 && b.dhi == b.dlo + 2
}

/// What bit `i` of word `k` of the group states about row `j = 64 (w0 + k) + i`, and the row's price code.
pub open spec fn gw_bit_ok(gw: Gw, bnd: Bnd, xs: Seq<Row>, price: Seq<u32>, k: int, i: int) -> bool {
    let j = 64 * (gw.w0 + k) + i;
    &&& bit64(gw.a@[k], i) == (ival(xs[j][2]) == bnd.dlo)
    &&& bit64(gw.b@[k], i) == (ival(xs[j][2]) == bnd.dlo + 1)
    &&& bit64(gw.c@[k], i) == (ival(xs[j][2]) == bnd.dlo + 2)
    &&& bit64(gw.q@[k], i) == (ival(xs[j][0]) < bnd.qhi)
    &&& if gw.need_lo { bit64(gw.l@[k], i) == (ival(xs[j][3]) < bnd.lo) } else { bnd.lo <= ival(xs[j][3]) }
    &&& if gw.need_hi { bit64(gw.h@[k], i) == (ival(xs[j][3]) < bnd.hi) } else { ival(xs[j][3]) < bnd.hi }
    &&& ival(xs[j][1]) == gw.bp + price[j]
}

/// A well-formed group plan over the rows `xs` with price codes `price`.
pub open spec fn gw_ok(gw: Gw, dlo: u32, bnd: Bnd, xs: Seq<Row>, price: Seq<u32>) -> bool {
    &&& bnd3(bnd) && dlo == bnd.dlo
    &&& gw.bp <= 0x1_0000_0000
    &&& gw.nwg <= 1024
    &&& 64 * (gw.w0 + gw.nwg) <= usize::MAX
    &&& 64 * (gw.w0 + gw.nwg) <= price.len()
    &&& 64 * (gw.w0 + gw.nwg) <= xs.len()
    &&& gw.a@.len() == gw.nwg && gw.b@.len() == gw.nwg && gw.c@.len() == gw.nwg && gw.q@.len() == gw.nwg
    &&& gw.l@.len() == gw.nwg && gw.h@.len() == gw.nwg
    &&& gw.ml == if gw.need_lo { !0u64 } else { 0u64 }
    &&& gw.xh == if gw.need_hi { 0u64 } else { !0u64 }
    &&& forall|k: int, i: int| 0 <= k < gw.nwg && 0 <= i < 64 ==> #[trigger] gw_bit_ok(gw, bnd, xs, price, k, i)
}

/// The rows of words `k0 .. k1` of the group.
pub open spec fn gw_rows(gw: Gw, xs: Seq<Row>, k0: int, k1: int) -> Seq<Row> {
    xs.subrange(64 * (gw.w0 + k0), 64 * (gw.w0 + k1))
}

/// Word `k` of a group: `(sum, count)` of its 64 rows (the sum is also the absolute mass).
#[inline(always)]
pub fn gw_word(tab: &[u8; 64], gw: Gw, price: &[u32], dlo: u32, k: usize, wa: u64, wb: u64, wc: u64, wq: u64,
    wl: u64, wh: u64, fast: bool, Ghost(xs): Ghost<Seq<Row>>, Ghost(bnd): Ghost<Bnd>) -> (r: (u64, u64))
    requires
        tab@ == db_table(),
        gw_ok(gw, dlo, bnd, xs, price@),
        k < gw.nwg,
        wa == gw.a@[k as int] && wb == gw.b@[k as int] && wc == gw.c@[k as int] && wq == gw.q@[k as int],
        wl == gw.l@[k as int] && wh == gw.h@[k as int],
    ensures
        r.0 == gsum(qs(bnd), gw_rows(gw, xs, k as int, k + 1), ek(), 0),
        r.0 == gabs(qs(bnd), gw_rows(gw, xs, k as int, k + 1), ek(), 0),
        r.1 == gcount(qs(bnd), gw_rows(gw, xs, k as int, k + 1), ek()),
        r.0 <= 0x1_0000_0000_0000,
        r.1 <= 64,
    no_unwind when !fast
{
    let ghost w = (gw.w0 + k) as int;
    let l = wl;
    let h = wh;
    let s = !(l & gw.ml) & (h | gw.xh);
    let m = wq & s;
    let ma = wa & m;
    let mb = wb & m;
    let mc = wc & m;
    let any = ma | mb | mc;
    let j0 = 64 * (gw.w0 + k);
    let (_, p1) = price.split_at(j0);
    let (pw, _) = p1.split_at(64);
    proof {
        lemma_const_words();
        assert(pw@ =~= price@.subrange(64 * w, 64 * w + 64));
        assert forall|i: int| 0 <= i < 64 implies {
            let j = 64 * w + i;
            &&& #[trigger] bit64(gw.a@[k as int], i) == (ival(xs[j][2]) == bnd.dlo)
            &&& bit64(gw.b@[k as int], i) == (ival(xs[j][2]) == bnd.dlo + 1)
            &&& bit64(gw.c@[k as int], i) == (ival(xs[j][2]) == bnd.dlo + 2)
            &&& bit64(gw.q@[k as int], i) == (ival(xs[j][0]) < bnd.qhi)
            &&& bit64(s, i) == (bnd.lo <= ival(xs[j][3]) && ival(xs[j][3]) < bnd.hi)
            &&& ival(xs[j][1]) == gw.bp + price@[j]
        } by {
            assert(gw_bit_ok(gw, bnd, xs, price@, k as int, i));
            lemma_bit_ops(l, gw.ml, i);
            lemma_bit_ops(l & gw.ml, 0u64, i);
            lemma_bit_ops(h, gw.xh, i);
            lemma_bit_ops(!(l & gw.ml), h | gw.xh, i);
        }
        lemma_word(bnd, xs, price@, gw.bp as int, w, pw@, gw.a@[k as int], gw.b@[k as int], gw.c@[k as int],
            gw.q@[k as int], s);
        assert(64 * (gw.w0 + k) + 64 == 64 * (gw.w0 + (k + 1)));
    }
    word_sum(tab, pw, any, mb, mc, dlo, gw.bp, fast, Ghost(qs(bnd)), Ghost(xs), Ghost(64 * w))
}

/// Words `k0 .. k1` of a group: `(sum, count)`; the sum is also the absolute mass.
pub fn gw_run(gw: Gw, price: &[u32], dlo: u32, k0: usize, k1: usize, fast: bool, Ghost(xs): Ghost<Seq<Row>>,
    Ghost(bnd): Ghost<Bnd>) -> (r: (u64, u64))
    requires
        gw_ok(gw, dlo, bnd, xs, price@),
        k0 <= k1 <= gw.nwg,
    ensures
        r.0 == gsum(qs(bnd), gw_rows(gw, xs, k0 as int, k1 as int), ek(), 0),
        r.0 == gabs(qs(bnd), gw_rows(gw, xs, k0 as int, k1 as int), ek(), 0),
        r.1 == gcount(qs(bnd), gw_rows(gw, xs, k0 as int, k1 as int), ek()),
        r.0 <= (k1 - k0) * 0x1_0000_0000_0000,
        r.1 <= 64 * (k1 - k0),
    no_unwind when !fast
{
    let ghost g = qs(bnd);
    let ghost r0 = 64 * (gw.w0 + k0);
    proof {
        lemma_empty(g, xs, r0, ek(), 0);
    }
    let tab = db_tab();
    // words 0 .. k1 of each bitmap, as slices of length k1 (no bounds check per word)
    let (a, _) = gw.a.split_at(k1);
    let (b, _) = gw.b.split_at(k1);
    let (c, _) = gw.c.split_at(k1);
    let (q, _) = gw.q.split_at(k1);
    let (l, _) = gw.l.split_at(k1);
    let (h, _) = gw.h.split_at(k1);
    proof {
        assert(a@ =~= gw.a@.subrange(0, k1 as int));
        assert(b@ =~= gw.b@.subrange(0, k1 as int));
        assert(c@ =~= gw.c@.subrange(0, k1 as int));
        assert(q@ =~= gw.q@.subrange(0, k1 as int));
        assert(l@ =~= gw.l@.subrange(0, k1 as int));
        assert(h@ =~= gw.h@.subrange(0, k1 as int));
    }
    let mut acc: u64 = 0;
    let mut cnt: u64 = 0;
    let mut k: usize = k0;
    while k < k1
        invariant
            tab@ == db_table(),
            gw_ok(gw, dlo, bnd, xs, price@),
            k0 <= k <= k1 <= gw.nwg,
            a@ == gw.a@.subrange(0, k1 as int), b@ == gw.b@.subrange(0, k1 as int),
            c@ == gw.c@.subrange(0, k1 as int), q@ == gw.q@.subrange(0, k1 as int),
            l@ == gw.l@.subrange(0, k1 as int), h@ == gw.h@.subrange(0, k1 as int),
            g == qs(bnd),
            r0 == 64 * (gw.w0 + k0),
            acc == gsum(g, xs.subrange(r0, 64 * (gw.w0 + k)), ek(), 0),
            acc == gabs(g, xs.subrange(r0, 64 * (gw.w0 + k)), ek(), 0),
            cnt == gcount(g, xs.subrange(r0, 64 * (gw.w0 + k)), ek()),
            acc <= (k - k0) * 0x1_0000_0000_0000,
            cnt <= 64 * (k - k0),
        decreases k1 - k,
    {
        let (v, n) = gw_word(&tab, gw, price, dlo, k, a[k], b[k], c[k], q[k], l[k], h[k], fast, Ghost(xs), Ghost(bnd));
        proof {
            assert(64 * (gw.w0 + k) + 64 == 64 * (gw.w0 + (k + 1)));
            lemma_split(g, xs, r0, 64 * (gw.w0 + k), 64 * (gw.w0 + (k + 1)), ek(), 0);
        }
        acc = acc + v;
        cnt = cnt + n;
        k = k + 1;
    }
    (acc, cnt)
}

/// Two groups scanned together, word `k` of the first then word `k` of the second (two independent memory
/// streams keep more cache-line fetches in flight on one thread), then the rest of the longer one. Returns
/// `(sum, count)` of each group; each sum is also its absolute mass.
#[inline(always)]
pub fn gw_pair(g1: Gw, g2: Gw, price: &[u32], dlo: u32, fast: bool, Ghost(xs): Ghost<Seq<Row>>, Ghost(bnd): Ghost<Bnd>)
    -> (r: (u64, u64, u64, u64))
    requires
        gw_ok(g1, dlo, bnd, xs, price@),
        gw_ok(g2, dlo, bnd, xs, price@),
    ensures
        r.0 == gsum(qs(bnd), gw_rows(g1, xs, 0, g1.nwg as int), ek(), 0),
        r.0 == gabs(qs(bnd), gw_rows(g1, xs, 0, g1.nwg as int), ek(), 0),
        r.1 == gcount(qs(bnd), gw_rows(g1, xs, 0, g1.nwg as int), ek()),
        r.2 == gsum(qs(bnd), gw_rows(g2, xs, 0, g2.nwg as int), ek(), 0),
        r.2 == gabs(qs(bnd), gw_rows(g2, xs, 0, g2.nwg as int), ek(), 0),
        r.3 == gcount(qs(bnd), gw_rows(g2, xs, 0, g2.nwg as int), ek()),
        r.0 <= 0x400_0000_0000_0000,
        r.2 <= 0x400_0000_0000_0000,
        r.1 <= 64 * g1.nwg,
        r.3 <= 64 * g2.nwg,
    no_unwind when !fast
{
    let ghost g = qs(bnd);
    let ghost r1 = 64 * g1.w0;
    let ghost r2 = 64 * g2.w0;
    proof {
        lemma_empty(g, xs, r1, ek(), 0);
        lemma_empty(g, xs, r2, ek(), 0);
    }
    let tab = db_tab();
    let m = if g1.nwg < g2.nwg { g1.nwg } else { g2.nwg };
    // words 0 .. m of each bitmap of both groups, as slices of length m (no bounds check per word)
    let (a1, _) = g1.a.split_at(m);
    let (b1, _) = g1.b.split_at(m);
    let (c1, _) = g1.c.split_at(m);
    let (q1, _) = g1.q.split_at(m);
    let (l1, _) = g1.l.split_at(m);
    let (h1, _) = g1.h.split_at(m);
    let (a2, _) = g2.a.split_at(m);
    let (b2, _) = g2.b.split_at(m);
    let (c2, _) = g2.c.split_at(m);
    let (q2, _) = g2.q.split_at(m);
    let (l2, _) = g2.l.split_at(m);
    let (h2, _) = g2.h.split_at(m);
    proof {
        assert(a1@ =~= g1.a@.subrange(0, m as int));
        assert(b1@ =~= g1.b@.subrange(0, m as int));
        assert(c1@ =~= g1.c@.subrange(0, m as int));
        assert(q1@ =~= g1.q@.subrange(0, m as int));
        assert(l1@ =~= g1.l@.subrange(0, m as int));
        assert(h1@ =~= g1.h@.subrange(0, m as int));
        assert(a2@ =~= g2.a@.subrange(0, m as int));
        assert(b2@ =~= g2.b@.subrange(0, m as int));
        assert(c2@ =~= g2.c@.subrange(0, m as int));
        assert(q2@ =~= g2.q@.subrange(0, m as int));
        assert(l2@ =~= g2.l@.subrange(0, m as int));
        assert(h2@ =~= g2.h@.subrange(0, m as int));
    }
    let mut acc1: u64 = 0;
    let mut cnt1: u64 = 0;
    let mut acc2: u64 = 0;
    let mut cnt2: u64 = 0;
    let mut k: usize = 0;
    while k < m
        invariant
            tab@ == db_table(),
            gw_ok(g1, dlo, bnd, xs, price@),
            gw_ok(g2, dlo, bnd, xs, price@),
            m <= g1.nwg && m <= g2.nwg,
            k <= m,
            a1@ == g1.a@.subrange(0, m as int), b1@ == g1.b@.subrange(0, m as int),
            c1@ == g1.c@.subrange(0, m as int), q1@ == g1.q@.subrange(0, m as int),
            l1@ == g1.l@.subrange(0, m as int), h1@ == g1.h@.subrange(0, m as int),
            a2@ == g2.a@.subrange(0, m as int), b2@ == g2.b@.subrange(0, m as int),
            c2@ == g2.c@.subrange(0, m as int), q2@ == g2.q@.subrange(0, m as int),
            l2@ == g2.l@.subrange(0, m as int), h2@ == g2.h@.subrange(0, m as int),
            g == qs(bnd),
            r1 == 64 * g1.w0,
            r2 == 64 * g2.w0,
            acc1 == gsum(g, xs.subrange(r1, 64 * (g1.w0 + k)), ek(), 0),
            acc1 == gabs(g, xs.subrange(r1, 64 * (g1.w0 + k)), ek(), 0),
            cnt1 == gcount(g, xs.subrange(r1, 64 * (g1.w0 + k)), ek()),
            acc2 == gsum(g, xs.subrange(r2, 64 * (g2.w0 + k)), ek(), 0),
            acc2 == gabs(g, xs.subrange(r2, 64 * (g2.w0 + k)), ek(), 0),
            cnt2 == gcount(g, xs.subrange(r2, 64 * (g2.w0 + k)), ek()),
            acc1 <= k * 0x1_0000_0000_0000,
            acc2 <= k * 0x1_0000_0000_0000,
            cnt1 <= 64 * k,
            cnt2 <= 64 * k,
        decreases m - k,
    {
        let (v1, n1) = gw_word(&tab, g1, price, dlo, k, a1[k], b1[k], c1[k], q1[k], l1[k], h1[k], fast, Ghost(xs), Ghost(bnd));
        let (v2, n2) = gw_word(&tab, g2, price, dlo, k, a2[k], b2[k], c2[k], q2[k], l2[k], h2[k], fast, Ghost(xs), Ghost(bnd));
        proof {
            assert(64 * (g1.w0 + k) + 64 == 64 * (g1.w0 + (k + 1)));
            assert(64 * (g2.w0 + k) + 64 == 64 * (g2.w0 + (k + 1)));
            lemma_split(g, xs, r1, 64 * (g1.w0 + k), 64 * (g1.w0 + (k + 1)), ek(), 0);
            lemma_split(g, xs, r2, 64 * (g2.w0 + k), 64 * (g2.w0 + (k + 1)), ek(), 0);
        }
        acc1 = acc1 + v1;
        cnt1 = cnt1 + n1;
        acc2 = acc2 + v2;
        cnt2 = cnt2 + n2;
        k = k + 1;
    }
    let (t1, d1) = gw_run(g1, price, dlo, m, g1.nwg, fast, Ghost(xs), Ghost(bnd));
    let (t2, d2) = gw_run(g2, price, dlo, m, g2.nwg, fast, Ghost(xs), Ghost(bnd));
    proof {
        lemma_split(g, xs, r1, 64 * (g1.w0 + m), 64 * (g1.w0 + g1.nwg), ek(), 0);
        lemma_split(g, xs, r2, 64 * (g2.w0 + m), 64 * (g2.w0 + g2.nwg), ek(), 0);
        assert(64 * (g1.w0 + 0) == r1);
        assert(64 * (g2.w0 + 0) == r2);
    }
    (acc1 + t1, cnt1 + d1, acc2 + t2, cnt2 + d2)
}

/// The index `t < ns` of the shipdate key `x` of group `gi`, if any.
pub fn find_ship_key(bt: Bits, gi: usize, x: i64) -> (r: Option<usize>)
    requires (gi + 1) * bt.ns <= bt.skeys@.len(), bt.skeys@.len() <= usize::MAX,
    ensures r matches Some(t) ==> t < bt.ns && bt.skeys@[gi * bt.ns + t] == x,
    no_unwind
{
    let mut t: usize = 0;
    while t < bt.ns
        invariant t <= bt.ns, (gi + 1) * bt.ns <= bt.skeys@.len(), bt.skeys@.len() <= usize::MAX,
        decreases bt.ns - t,
    {
        proof {
            assert(gi * bt.ns + t < (gi + 1) * bt.ns) by (nonlinear_arith) requires t < bt.ns;
            assert(0 <= gi * bt.ns) by (nonlinear_arith) requires 0 <= gi, 0 <= bt.ns;
        }
        if bt.skeys[gi * bt.ns + t] == x {
            return Some(t);
        }
        t = t + 1;
    }
    None
}

} // verus!
