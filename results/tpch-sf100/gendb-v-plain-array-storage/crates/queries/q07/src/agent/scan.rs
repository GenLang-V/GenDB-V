//! The lineitem scan of one task (`ScanTask`): rows `lo..hi`, accumulating per group (`lines::lsum`) the count, the
//! volume and the absolute volume.
//!
//! Fast-path facts (`scan_cols_ok`): the supplier and customer keys are positional (`s_suppkey[r] == sbase + r`,
//! `c_custkey[r] == cbase + r`), so a key finds its row by subtraction; `swords` and `cwords` hold every supplier's
//! and every customer's nation tag in 2 bits (`tags::tags_ok`).
//!
//! The task runs in rounds; each round takes rows `b..e` (`collect`: 64-row words until the candidate buffers, `CAP`
//! entries, might overflow) through four branch-light loops over small buffers, so that the loads of different rows
//! overlap:
//! 1. candidates (`collect`): per 64-row word a mask of the rows shipped in the window (`mask64`, branch-free and
//!    vectorized over a 64-day slice), then for its set bits the supplier's tag; the candidates (`cand`: in the
//!    window, a supplier with a non-zero tag) are listed in row order with their supplier tags (`cands_ok`). Every
//!    other row contributes nothing (`lemma_not_cand`).
//! 2. keys (`cand_keys`): each candidate's `l_orderkey`;
//! 3. customers (`cand_custs`): each candidate's customer row through its order (`scan::order_row`: the dbgen
//!    position of the key, checked against `o_orderkey`; a linear search when the check fails) (`custs_ok`);
//! 4. qualifying rows (`cand_quals`): the customer's tag, the tag match and the group; the qualifying rows are listed
//!    in row order with their groups (`quals_ok`);
//! 5. sums (`qual_sums`): the listed rows' volumes added to the accumulators. An absolute sum beyond `i128::MAX` stops
//!    the task (`over`), which makes the query answer `Capacity`.
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::numeric::abs;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::WorkerTask;
use crate::gendb_entry::work::filled;
use crate::link::expr::i128_max;
use crate::agent::tables::*;
use crate::agent::normal_form::*;
use crate::agent::lines::*;
use crate::agent::common::bits::*;
use crate::agent::common::tz::{tz64, tz_table_array};
use crate::agent::tags::tags_ok;

verus! {

/// Entries of each candidate buffer of a task; a round stops collecting before a 64-row word could overflow them.
pub const CAP: usize = 512;

/// Key column `keys` is `base + r` at row `r`.
pub open spec fn positional(keys: Seq<i64>, base: int) -> bool {
    forall|r: int| 0 <= r < keys.len() ==> #[trigger] keys[r] as int == base + r
}

/// On a positional key column a key resolves exactly in `base .. base + len`, at row `key - base`.
pub proof fn lemma_positional(keys: Seq<i64>, base: int, k: i64)
    requires positional(keys, base),
    ensures
        has_key(keys, k) == (base <= k < base + keys.len()),
        has_key(keys, k) ==> key_row(keys, k) == k - base,
{
    if base <= k < base + keys.len() {
        let r = k - base;
        assert(keys[r] as int == base + r);
        assert(has_key(keys, k));
    }
    if has_key(keys, k) {
        lemma_key_row(keys, k);
        let j = key_row(keys, k);
        assert(keys[j] as int == base + j);
    }
}

/// The stored columns a scan reads (whole columns) and the positional bases.
#[derive(Clone, Copy)]
pub struct ScanCols {
    pub lship: &'static [i32],
    pub lsupp: &'static [i64],
    pub lokey: &'static [i64],
    pub lprice: &'static [i128],
    pub ldisc: &'static [i128],
    pub okey: &'static [i64],
    pub ocust: &'static [i64],
    pub nl: usize,
    pub no: usize,
    pub ns: usize,
    pub nc: usize,
    pub sbase: i64,
    pub send: i64,
    pub cbase: i64,
    pub cend: i64,
}

/// The slices are the stored lineitem and orders columns of `sv` (with the numeric bounds and the primary key of
/// orders).
pub open spec fn line_cols_ok(c: ScanCols, sv: StoresView) -> bool {
    &&& c.lship@ == lsd(sv) && c.lsupp@ == lsk(sv) && c.lokey@ == lok(sv) && c.lprice@ == lpr(sv) && c.ldisc@ == ldc(sv)
    &&& c.okey@ == ok(sv) && c.ocust@ == oc(sv)
    &&& c.nl as int == n_l(sv) && c.no as int == n_o(sv) && c.ns as int == n_s(sv) && c.nc as int == n_c(sv)
    &&& lsk(sv).len() == n_l(sv) && lpr(sv).len() == n_l(sv) && ldc(sv).len() == n_l(sv) && lsd(sv).len() == n_l(sv)
    &&& oc(sv).len() == n_o(sv) && sn(sv).len() == n_s(sv) && cn(sv).len() == n_c(sv)
    &&& keys_unique(ok(sv))
    &&& forall|l: int| 0 <= l < n_l(sv) ==> num15(#[trigger] lpr(sv)[l]) && num15(ldc(sv)[l])
}

/// The fast-path facts: the columns, and positional supplier and customer keys with representable ends.
pub open spec fn scan_cols_ok(c: ScanCols, sv: StoresView) -> bool {
    &&& line_cols_ok(c, sv)
    &&& c.ns <= i64::MAX && c.nc <= i64::MAX
    &&& positional(sk(sv), c.sbase as int) && c.send as int == c.sbase + c.ns
    &&& positional(ck(sv), c.cbase as int) && c.cend as int == c.cbase + c.nc
}

/// Everything a scan task reads: the columns and the supplier and customer tags.
pub open spec fn scan_inputs_ok(c: ScanCols, swords: Seq<u64>, cwords: Seq<u64>, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& scan_cols_ok(c, sv)
    &&& tags_ok(swords, sn(sv), sv, ps, c.ns as int)
    &&& tags_ok(cwords, cn(sv), sv, ps, c.nc as int)
}

/// Row `l` is a candidate: shipped in the window, with a supplier whose nation tag is not 0.
pub open spec fn cand(c: ScanCols, sv: StoresView, ps: Seq<Literal>, l: int) -> bool {
    &&& ship_in(lsd(sv)[l] as int)
    &&& c.sbase <= lsk(sv)[l] < c.send
    &&& supp_tag(sv, ps, lsk(sv)[l] - c.sbase) != 0
}

/// A row that is not a candidate does not qualify.
pub proof fn lemma_not_cand(c: ScanCols, sv: StoresView, ps: Seq<Literal>, l: int)
    requires scan_cols_ok(c, sv), 0 <= l < n_l(sv), !cand(c, sv, ps, l),
    ensures !line_qual(sv, ps, l),
{
    lemma_positional(sk(sv), c.sbase as int, lsk(sv)[l]);
    if ship_in(lsd(sv)[l] as int) && c.sbase <= lsk(sv)[l] < c.send {
        let s = lsk(sv)[l] - c.sbase;
        assert(l_supp(sv, l) == s);
    }
}

/// Rows `x..y` none of which qualifies contribute nothing.
pub proof fn lemma_no_qual(sv: StoresView, ps: Seq<Literal>, g: int, w: int, x: int, y: int)
    requires x <= y, forall|l: int| x <= l < y ==> !#[trigger] line_qual(sv, ps, l),
    ensures lsum(sv, ps, g, w, x, y) == 0,
    decreases y - x,
{
    if y > x {
        lemma_no_qual(sv, ps, g, w, x, y - 1);
        assert(!line_qual(sv, ps, y - 1));
    }
}

// ------------------------------------------------------------------------------------------------ 1: candidates

/// `buf[0..n]` lists, in increasing order, exactly the candidates among the rows `b..e`; `tb[t]` is the nation tag of
/// the supplier of row `buf[t]`.
pub open spec fn cands_ok(buf: Seq<usize>, tb: Seq<u8>, n: int, c: ScanCols, sv: StoresView, ps: Seq<Literal>, b: int, e: int) -> bool {
    &&& 0 <= n <= buf.len() && n <= tb.len()
    &&& forall|t: int| 0 <= t < n ==> b <= #[trigger] buf[t] < e && cand(c, sv, ps, buf[t] as int)
        && tb[t] as int == supp_tag(sv, ps, lsk(sv)[buf[t] as int] - c.sbase)
    &&& forall|t: int, u: int| 0 <= t < u < n ==> #[trigger] buf[t] < #[trigger] buf[u]
    &&& forall|l: int| b <= l < e && #[trigger] cand(c, sv, ps, l) ==> exists|t: int| 0 <= t < n && buf[t] == l
}

/// The window test of 64 consecutive stored days as a mask: bit `u` is day `ch[u]` (branch-free; the compiler
/// vectorizes it since the slice length is known).
fn mask64(ch: &[i32]) -> (m: u64)
    requires ch@.len() == 64,
    ensures forall|u: u64| u < 64 ==> #[trigger] bit(m, u) == ship_in(ch@[u as int] as int),
    no_unwind
{
    let mut m: u64 = 0;
    let mut u: usize = 0;
    proof {
        assert forall|v: u64| v < 64 implies !#[trigger] bit(0u64, v) by { lemma_bit_zero(v); }
    }
    while u < 64
        invariant
            ch@.len() == 64, u <= 64,
            forall|v: u64| v < 64 ==> #[trigger] bit(m, v) == (v < u && ship_in(ch@[v as int] as int)),
        decreases 64 - u,
    {
        let d = ch[u];
        let lo_ok = (d >= 9131) as u64;
        let hi_ok = (d <= 9861) as u64;
        let x = lo_ok & hi_ok;
        proof {
            assert(x <= 1 && (x == 1) == (lo_ok == 1 && hi_ok == 1)) by (bit_vector)
                requires lo_ok <= 1, hi_ok <= 1, x == lo_ok & hi_ok;
        }
        let ghost m0 = m;
        m = m | (x << (u as u64));
        proof {
            assert forall|v: u64| v < 64 implies #[trigger] bit(m, v) == (v < u + 1 && ship_in(ch@[v as int] as int)) by {
                lemma_bit_set(m0, x, u as u64, v);
            }
        }
        u = u + 1;
    }
    m
}

/// The window test of rows `w..we` (at most 64) as a mask, one row at a time: bit `u` is row `w + u`.
fn date_mask(c: &ScanCols, w: usize, we: usize, Ghost(sv): Ghost<StoresView>) -> (m: u64)
    requires scan_cols_ok(*c, sv), w < we <= c.nl, we - w <= 64,
    ensures forall|u: u64| u < 64 ==> #[trigger] bit(m, u) == (u < we - w && ship_in(lsd(sv)[w + u] as int)),
    no_unwind
{
    let mut m: u64 = 0;
    let mut j = w;
    proof {
        assert forall|u: u64| u < 64 implies !#[trigger] bit(0u64, u) by { lemma_bit_zero(u); }
    }
    while j < we
        invariant
            scan_cols_ok(*c, sv), w <= j <= we <= c.nl, we - w <= 64,
            forall|u: u64| u < 64 ==> #[trigger] bit(m, u) == (u < j - w && ship_in(lsd(sv)[w + u] as int)),
        decreases we - j,
    {
        let d = c.lship[j];
        let x = (d >= 9131 && d <= 9861) as u64;
        let t = (j - w) as u64;
        let ghost m0 = m;
        m = m | (x << t);
        proof {
            assert forall|u: u64| u < 64 implies #[trigger] bit(m, u) == (u < j + 1 - w && ship_in(lsd(sv)[w + u] as int)) by {
                lemma_bit_set(m0, x, t, u);
            }
        }
        j = j + 1;
    }
    m
}

/// The window mask of the word at row `w` (rows `w..we`): `mask64` over the 64 stored days of a full word, else
/// `date_mask`.
fn word_mask(c: &ScanCols, w: usize, we: usize, Ghost(sv): Ghost<StoresView>) -> (m: u64)
    requires scan_cols_ok(*c, sv), w < we <= c.nl, we - w <= 64,
    ensures forall|u: u64| u < 64 ==> #[trigger] bit(m, u) == (u < we - w && ship_in(lsd(sv)[w + u] as int)),
    no_unwind
{
    if we - w == 64 {
        let (_, tail) = c.lship.split_at(w);
        let (ch, _) = tail.split_at(64);
        let m = mask64(ch);
        proof {
            assert forall|u: u64| u < 64 implies #[trigger] bit(m, u) == (u < we - w && ship_in(lsd(sv)[w + u] as int)) by {
                assert(ch@[u as int] == tail@[u as int]);
                assert(tail@[u as int] == lsd(sv)[w + u]);
            }
        }
        m
    } else {
        date_mask(c, w, we, Ghost(sv))
    }
}

/// The nation tag of the supplier of lineitem row `i` (0 when its key is outside the suppliers' keys).
fn supp_tag_at(c: &ScanCols, swords: &Vec<u64>, i: usize, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: u8)
    requires scan_cols_ok(*c, sv), tags_ok(swords@, sn(sv), sv, ps, c.ns as int), i < c.nl,
    ensures
        (r != 0) == (c.sbase <= lsk(sv)[i as int] < c.send && supp_tag(sv, ps, lsk(sv)[i as int] - c.sbase) != 0),
        r != 0 ==> r as int == supp_tag(sv, ps, lsk(sv)[i as int] - c.sbase),
    no_unwind
{
    let s = c.lsupp[i];
    if s >= c.sbase && s < c.send {
        let idx = (s - c.sbase) as usize;
        let word = swords[idx / 32];
        let t = ((word >> (2 * ((idx % 32) as u64))) & 3u64) as u8;
        proof {
            assert(field2(swords@[(idx / 32) as int], (idx % 32) as u64) as int == nat_tag(sv, ps, sn(sv)[idx as int]));
            lemma_field2_max(word, (idx % 32) as u64);
        }
        t
    } else {
        0
    }
}

/// Append the candidates among the date-mask rows of the word at `w` (rows `w..we`), at most 64 of them.
fn word_cands(c: &ScanCols, swords: &Vec<u64>, table: &[u8; 64], m0: u64, w: usize, we: usize, b: usize,
    buf: &mut Vec<usize>, tb: &mut Vec<u8>, n0: usize, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (n: usize)
    requires
        scan_cols_ok(*c, sv), tags_ok(swords@, sn(sv), sv, ps, c.ns as int), table@.len() == 64,
        b <= w < we <= c.nl, we - w <= 64, old(buf)@.len() == CAP, old(tb)@.len() == CAP, n0 + 64 <= CAP,
        forall|u: u64| u < 64 ==> #[trigger] bit(m0, u) == (u < we - w && ship_in(lsd(sv)[w + u] as int)),
        cands_ok(old(buf)@, old(tb)@, n0 as int, *c, sv, ps, b as int, w as int),
    ensures
        final(buf)@.len() == CAP, final(tb)@.len() == CAP, n <= n0 + 64,
        cands_ok(final(buf)@, final(tb)@, n as int, *c, sv, ps, b as int, we as int),
    no_unwind
{
    let mut m = m0;
    let mut n = n0;
    let ghost mut p: int = 0;
    while m != 0
        invariant
            scan_cols_ok(*c, sv), tags_ok(swords@, sn(sv), sv, ps, c.ns as int), table@.len() == 64,
            b <= w < we <= c.nl, we - w <= 64, buf@.len() == CAP, tb@.len() == CAP, n0 + 64 <= CAP,
            0 <= p <= we - w, n0 <= n <= n0 + p,
            forall|u: u64| u < 64 ==> #[trigger] bit(m, u) == (p <= u < we - w && ship_in(lsd(sv)[w + u] as int)),
            cands_ok(buf@, tb@, n as int, *c, sv, ps, b as int, w + p),
        decreases we - w - p,
    {
        proof { lemma_first_bit(m); }
        let t = tz64(m, table) as u64;
        proof {
            assert(bit(m, t));
            // rows w + p .. w + t are outside the window
            assert forall|l: int| w + p <= l < w + t implies !#[trigger] cand(*c, sv, ps, l) by {
                let u = (l - w) as u64;
                assert(!bit(m, u));
            }
        }
        let ghost m1 = m;
        m = m & (m - 1);
        proof {
            assert(m1 - 1 == sub(m1, 1));
            assert forall|u: u64| u < 64 implies #[trigger] bit(m, u) == (t + 1 <= u < we - w && ship_in(lsd(sv)[w + u] as int)) by {
                lemma_clear_lowest(m1, t, u);
            }
        }
        let i = w + t as usize;
        let st = supp_tag_at(c, swords, i, Ghost(sv), Ghost(ps));
        let ghost (buf0, tb0) = (buf@, tb@);
        buf[n] = i;
        tb[n] = st;
        let x: usize = if st != 0 { 1 } else { 0 };
        proof {
            let nn = n + x;
            assert(cand(*c, sv, ps, i as int) == (x == 1));
            assert forall|tt: int| 0 <= tt < nn implies b <= #[trigger] buf@[tt] < we && cand(*c, sv, ps, buf@[tt] as int)
                && tb@[tt] as int == supp_tag(sv, ps, lsk(sv)[buf@[tt] as int] - c.sbase) by {
                if tt < n { assert(buf@[tt] == buf0[tt] && tb@[tt] == tb0[tt]); }
            }
            assert forall|tt: int, uu: int| 0 <= tt < uu < nn implies #[trigger] buf@[tt] < #[trigger] buf@[uu] by {
                if uu < n { assert(buf@[tt] == buf0[tt] && buf@[uu] == buf0[uu]); } else { assert(buf@[tt] == buf0[tt]); }
            }
            assert forall|l: int| b <= l < w + t + 1 && #[trigger] cand(*c, sv, ps, l) implies
                exists|tt: int| 0 <= tt < nn && buf@[tt] == l by {
                if l < w + p {
                    let tt = choose|tt: int| 0 <= tt < n && buf0[tt] == l;
                    assert(buf@[tt] == buf0[tt]);
                } else {
                    assert(l == i);
                    assert(buf@[n as int] == l);
                }
            }
            p = t + 1;
        }
        n = n + x;
    }
    proof {
        assert forall|l: int| w + p <= l < we implies !#[trigger] cand(*c, sv, ps, l) by {
            let u = (l - w) as u64;
            lemma_bit_zero(u);
            assert(!bit(m, u));
        }
        assert forall|l: int| b <= l < we && #[trigger] cand(*c, sv, ps, l) implies
            exists|tt: int| 0 <= tt < n && buf@[tt] == l by {
            if l >= w + p {
                assert(!cand(*c, sv, ps, l));
            }
        }
    }
    n
}

/// Stage 1 of a round: the candidates of rows `b..e`, taking 64-row words from `b` on while `CAP` entries may still
/// hold a whole word's candidates (at least one word, so `e > b`).
fn collect(c: &ScanCols, swords: &Vec<u64>, table: &[u8; 64], b: usize, hi: usize, buf: &mut Vec<usize>, tb: &mut Vec<u8>,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: (usize, usize))
    requires
        scan_cols_ok(*c, sv), tags_ok(swords@, sn(sv), sv, ps, c.ns as int), table@.len() == 64,
        b < hi <= c.nl, old(buf)@.len() == CAP, old(tb)@.len() == CAP,
    ensures
        final(buf)@.len() == CAP, final(tb)@.len() == CAP, b < r.1 <= hi, r.0 <= CAP,
        cands_ok(final(buf)@, final(tb)@, r.0 as int, *c, sv, ps, b as int, r.1 as int),
    no_unwind
{
    let mut n: usize = 0;
    let mut w = b;
    while w < hi && n + 64 <= CAP
        invariant
            scan_cols_ok(*c, sv), tags_ok(swords@, sn(sv), sv, ps, c.ns as int), table@.len() == 64,
            b <= w <= hi <= c.nl, buf@.len() == CAP, tb@.len() == CAP, n <= CAP,
            w == b ==> n == 0,
            cands_ok(buf@, tb@, n as int, *c, sv, ps, b as int, w as int),
        decreases hi - w,
    {
        let we = if hi - w > 64 { w + 64 } else { hi };
        let m = word_mask(c, w, we, Ghost(sv));
        n = word_cands(c, swords, table, m, w, we, b, buf, tb, n, Ghost(sv), Ghost(ps));
        w = we;
    }
    (n, w)
}

// ------------------------------------------------------------------------------------------------ 2, 3: keys, customers

/// Stage 2: `kb[t]` is the `l_orderkey` of candidate `buf[t]`.
fn cand_keys(c: &ScanCols, buf: &Vec<usize>, n: usize, kb: &mut Vec<i64>, Ghost(sv): Ghost<StoresView>)
    requires
        line_cols_ok(*c, sv), buf@.len() == CAP, old(kb)@.len() == CAP, n <= CAP,
        forall|t: int| 0 <= t < n ==> #[trigger] buf@[t] < c.nl,
    ensures
        final(kb)@.len() == CAP,
        forall|t: int| 0 <= t < n ==> #[trigger] final(kb)@[t] == lok(sv)[buf@[t] as int],
    no_unwind
{
    let mut t: usize = 0;
    while t < n
        invariant
            line_cols_ok(*c, sv), buf@.len() == CAP, kb@.len() == CAP, n <= CAP, t <= n,
            forall|u: int| 0 <= u < n ==> #[trigger] buf@[u] < c.nl,
            forall|u: int| 0 <= u < t ==> #[trigger] kb@[u] == lok(sv)[buf@[u] as int],
        decreases n - t,
    {
        let k = c.lokey[buf[t]];
        kb[t] = k;
        t = t + 1;
    }
}

/// The orders row of key `k` (`no` when there is none): first the row where dbgen puts key `k`
/// (`k = 32 * (i / 8) + i % 8` for the `i`-th order, counting from 1), checked against `o_orderkey`, then a linear
/// search.
pub fn order_row(c: &ScanCols, k: i64, Ghost(sv): Ghost<StoresView>) -> (j: usize)
    requires line_cols_ok(*c, sv),
    ensures
        j <= c.no,
        j < c.no ==> ok(sv)[j as int] == k,
        j == c.no ==> !has_key(ok(sv), k),
    no_unwind
{
    if k > 0 {
        let ku = k as u64;
        let low = ku % 32;
        if low < 8 {
            let i = (ku / 32) * 8 + low;
            if i >= 1 && i - 1 < (c.no as u64) {
                let g = (i - 1) as usize;
                if c.okey[g] == k {
                    return g;
                }
            }
        }
    }
    let mut j: usize = 0;
    while j < c.no
        invariant line_cols_ok(*c, sv), j <= c.no, forall|q: int| 0 <= q < j ==> ok(sv)[q] != k,
        decreases c.no - j,
    {
        if c.okey[j] == k {
            return j;
        }
        j = j + 1;
    }
    j
}

/// `cb[t]` is the customer row of the order of candidate `buf[t]`, or `nc` when its order key or the order's
/// customer key does not resolve.
pub open spec fn custs_ok(cb: Seq<usize>, buf: Seq<usize>, n: int, c: ScanCols, sv: StoresView) -> bool {
    forall|t: int| 0 <= t < n ==> {
        &&& #[trigger] cb[t] <= c.nc
        &&& (cb[t] < c.nc) == (has_key(ok(sv), lok(sv)[buf[t] as int]) && has_key(ck(sv), oc(sv)[l_ord(sv, buf[t] as int)]))
        &&& cb[t] < c.nc ==> cb[t] as int == l_cust(sv, buf[t] as int)
    }
}

/// The customer row of the order with key `k` (`nc` when there is none), for lineitem row `l` with that key.
fn cust_of_key(c: &ScanCols, k: i64, Ghost(l): Ghost<int>, Ghost(sv): Ghost<StoresView>) -> (cr: usize)
    requires scan_cols_ok(*c, sv), 0 <= l < n_l(sv), k == lok(sv)[l],
    ensures
        cr <= c.nc,
        (cr < c.nc) == (has_key(ok(sv), lok(sv)[l]) && has_key(ck(sv), oc(sv)[l_ord(sv, l)])),
        cr < c.nc ==> cr as int == l_cust(sv, l),
    no_unwind
{
    let j = order_row(c, k, Ghost(sv));
    proof { lemma_key_row(ok(sv), k); }
    if j == c.no {
        return c.nc;
    }
    proof {
        assert(has_key(ok(sv), k));
        assert(l_ord(sv, l) == j);
    }
    let ckey = c.ocust[j];
    proof { lemma_positional(ck(sv), c.cbase as int, ckey); }
    if ckey >= c.cbase && ckey < c.cend {
        (ckey - c.cbase) as usize
    } else {
        c.nc
    }
}

/// Stage 3: each candidate's customer row (`custs_ok`).
fn cand_custs(c: &ScanCols, buf: &Vec<usize>, kb: &Vec<i64>, n: usize, cb: &mut Vec<usize>, Ghost(sv): Ghost<StoresView>)
    requires
        scan_cols_ok(*c, sv), buf@.len() == CAP, kb@.len() == CAP, old(cb)@.len() == CAP, n <= CAP,
        forall|t: int| 0 <= t < n ==> #[trigger] buf@[t] < c.nl && kb@[t] == lok(sv)[buf@[t] as int],
    ensures final(cb)@.len() == CAP, custs_ok(final(cb)@, buf@, n as int, *c, sv),
    no_unwind
{
    let mut t: usize = 0;
    while t < n
        invariant
            scan_cols_ok(*c, sv), buf@.len() == CAP, kb@.len() == CAP, cb@.len() == CAP, n <= CAP, t <= n,
            forall|u: int| 0 <= u < n ==> #[trigger] buf@[u] < c.nl && kb@[u] == lok(sv)[buf@[u] as int],
            custs_ok(cb@, buf@, t as int, *c, sv),
        decreases n - t,
    {
        assert(buf@[t as int] < c.nl);
        let cr = cust_of_key(c, kb[t], Ghost(buf@[t as int] as int), Ghost(sv));
        let ghost cb0 = cb@;
        cb[t] = cr;
        proof {
            assert forall|u: int| 0 <= u < t + 1 implies {
                &&& #[trigger] cb@[u] <= c.nc
                &&& (cb@[u] < c.nc) == (has_key(ok(sv), lok(sv)[buf@[u] as int]) && has_key(ck(sv), oc(sv)[l_ord(sv, buf@[u] as int)]))
                &&& cb@[u] < c.nc ==> cb@[u] as int == l_cust(sv, buf@[u] as int)
            } by {
                if u < t { assert(cb@[u] == cb0[u]); }
            }
        }
        t = t + 1;
    }
}

// ------------------------------------------------------------------------------------------------ 4: qualifying rows

/// `qb[0..nq]` lists, in increasing order, exactly the qualifying rows among `b..e`; `gb[t]` is the group of row
/// `qb[t]`.
pub open spec fn quals_ok(qb: Seq<usize>, gb: Seq<u8>, nq: int, sv: StoresView, ps: Seq<Literal>, b: int, e: int) -> bool {
    &&& 0 <= nq <= qb.len() && nq <= gb.len()
    &&& forall|t: int| 0 <= t < nq ==> b <= #[trigger] qb[t] < e && line_qual(sv, ps, qb[t] as int)
        && gb[t] < 4 && gb[t] as int == line_grp(sv, ps, qb[t] as int)
    &&& forall|t: int, u: int| 0 <= t < u < nq ==> #[trigger] qb[t] < #[trigger] qb[u]
    &&& forall|l: int| b <= l < e && #[trigger] line_qual(sv, ps, l) ==> exists|t: int| 0 <= t < nq && qb[t] == l
}

/// Whether candidate row `i` (supplier tag `st`, customer row `cr` as in `custs_ok`) qualifies, and its group.
fn qual_of(c: &ScanCols, cwords: &Vec<u64>, i: usize, st: u8, cr: usize, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: (bool, u8))
    requires
        scan_cols_ok(*c, sv), tags_ok(cwords@, cn(sv), sv, ps, c.nc as int), i < c.nl, cand(*c, sv, ps, i as int),
        st as int == supp_tag(sv, ps, lsk(sv)[i as int] - c.sbase),
        cr <= c.nc,
        (cr < c.nc) == (has_key(ok(sv), lok(sv)[i as int]) && has_key(ck(sv), oc(sv)[l_ord(sv, i as int)])),
        cr < c.nc ==> cr as int == l_cust(sv, i as int),
    ensures
        r.0 == line_qual(sv, ps, i as int),
        r.0 ==> r.1 < 4 && r.1 as int == line_grp(sv, ps, i as int),
    no_unwind
{
    let ghost l = i as int;
    proof {
        lemma_positional(sk(sv), c.sbase as int, lsk(sv)[l]);
        assert(l_supp(sv, l) == lsk(sv)[l] - c.sbase);
    }
    let ct: u8 = if cr < c.nc {
        let word = cwords[cr / 32];
        proof {
            assert(field2(cwords@[(cr / 32) as int], (cr % 32) as u64) as int == nat_tag(sv, ps, cn(sv)[cr as int]));
            lemma_field2_max(word, (cr % 32) as u64);
        }
        ((word >> (2 * ((cr % 32) as u64))) & 3u64) as u8
    } else {
        0
    };
    proof {
        if cr < c.nc {
            assert(ct as int == cust_tag(sv, ps, l_cust(sv, l)));
        }
    }
    let q1 = st % 2 == 1 && ct >= 2;
    let q = q1 || (st >= 2 && ct % 2 == 1);
    let g: u8 = (if q1 { 0u8 } else { 2u8 }) + (if c.lship[i] >= 9496 { 1u8 } else { 0u8 });
    (q, g)
}

/// Stage 4: the qualifying candidates and their groups (`quals_ok`).
fn cand_quals(c: &ScanCols, cwords: &Vec<u64>, buf: &Vec<usize>, tb: &Vec<u8>, cb: &Vec<usize>, n: usize, qb: &mut Vec<usize>,
    gb: &mut Vec<u8>, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(b): Ghost<int>, Ghost(e): Ghost<int>) -> (nq: usize)
    requires
        scan_cols_ok(*c, sv), tags_ok(cwords@, cn(sv), sv, ps, c.nc as int), 0 <= b <= e <= c.nl,
        buf@.len() == CAP, tb@.len() == CAP, cb@.len() == CAP, old(qb)@.len() == CAP, old(gb)@.len() == CAP, n <= CAP,
        cands_ok(buf@, tb@, n as int, *c, sv, ps, b, e),
        custs_ok(cb@, buf@, n as int, *c, sv),
    ensures
        final(qb)@.len() == CAP, final(gb)@.len() == CAP,
        quals_ok(final(qb)@, final(gb)@, nq as int, sv, ps, b, e),
    no_unwind
{
    let mut nq: usize = 0;
    let mut t: usize = 0;
    while t < n
        invariant
            scan_cols_ok(*c, sv), tags_ok(cwords@, cn(sv), sv, ps, c.nc as int), 0 <= b <= e <= c.nl,
            buf@.len() == CAP, tb@.len() == CAP, cb@.len() == CAP, qb@.len() == CAP, gb@.len() == CAP, n <= CAP,
            cands_ok(buf@, tb@, n as int, *c, sv, ps, b, e),
            custs_ok(cb@, buf@, n as int, *c, sv),
            t <= n, nq <= t,
            forall|u: int| 0 <= u < nq ==> b <= #[trigger] qb@[u] < e && line_qual(sv, ps, qb@[u] as int)
                && gb@[u] < 4 && gb@[u] as int == line_grp(sv, ps, qb@[u] as int),
            forall|u: int, v: int| 0 <= u < v < nq ==> #[trigger] qb@[u] < #[trigger] qb@[v],
            t < n ==> forall|u: int| 0 <= u < nq ==> #[trigger] qb@[u] < buf@[t as int],
            forall|u: int| 0 <= u < t && #[trigger] line_qual(sv, ps, buf@[u] as int) ==> exists|v: int| 0 <= v < nq && qb@[v] == buf@[u],
        decreases n - t,
    {
        let i = buf[t];
        assert(b <= buf@[t as int] < e && cand(*c, sv, ps, i as int));
        let (q, g) = qual_of(c, cwords, i, tb[t], cb[t], Ghost(sv), Ghost(ps));
        let ghost (qb0, gb0) = (qb@, gb@);
        qb[nq] = i;
        gb[nq] = g;
        let x: usize = if q { 1 } else { 0 };
        proof {
            let nn = nq + x;
            assert forall|u: int| 0 <= u < nn implies b <= #[trigger] qb@[u] < e && line_qual(sv, ps, qb@[u] as int)
                && gb@[u] < 4 && gb@[u] as int == line_grp(sv, ps, qb@[u] as int) by {
                if u < nq { assert(qb@[u] == qb0[u] && gb@[u] == gb0[u]); }
            }
            assert forall|u: int, v: int| 0 <= u < v < nn implies #[trigger] qb@[u] < #[trigger] qb@[v] by {
                if v < nq { assert(qb@[u] == qb0[u] && qb@[v] == qb0[v]); } else { assert(qb@[u] == qb0[u]); }
            }
            if t + 1 < n {
                assert(buf@[t as int] < buf@[t + 1]);
                assert forall|u: int| 0 <= u < nn implies #[trigger] qb@[u] < buf@[t + 1] by {
                    if u < nq { assert(qb@[u] == qb0[u]); }
                }
            }
            assert forall|u: int| 0 <= u < t + 1 && #[trigger] line_qual(sv, ps, buf@[u] as int) implies
                exists|v: int| 0 <= v < nn && qb@[v] == buf@[u] by {
                if u < t {
                    let v = choose|v: int| 0 <= v < nq && qb0[v] == buf@[u];
                    assert(qb@[v] == qb0[v]);
                } else {
                    assert(qb@[nq as int] == buf@[u]);
                }
            }
        }
        nq = nq + x;
        t = t + 1;
    }
    proof {
        assert forall|l: int| b <= l < e && #[trigger] line_qual(sv, ps, l) implies exists|v: int| 0 <= v < nq && qb@[v] == l by {
            if !cand(*c, sv, ps, l) {
                lemma_not_cand(*c, sv, ps, l);
            }
            let u = choose|u: int| 0 <= u < n && buf@[u] == l;
            assert(line_qual(sv, ps, buf@[u] as int));
        }
    }
    nq
}

// ------------------------------------------------------------------------------------------------ 5: sums

/// Per-group accumulators: count, volume and absolute volume (scale 4) of groups 0..4.
pub struct Acc {
    pub cnt: Vec<usize>,
    pub sum: Vec<i128>,
    pub abs: Vec<i128>,
}

/// The accumulators are the sums over the rows `lo..hi`.
pub open spec fn acc_ok(a: Acc, sv: StoresView, ps: Seq<Literal>, lo: int, hi: int) -> bool {
    &&& a.cnt@.len() == 4 && a.sum@.len() == 4 && a.abs@.len() == 4
    &&& forall|g: int| #![trigger a.cnt@[g]] #![trigger a.sum@[g]] #![trigger a.abs@[g]] 0 <= g < 4 ==> {
        &&& a.cnt@[g] as int == lsum(sv, ps, g, 0, lo, hi)
        &&& a.sum@[g] as int == lsum(sv, ps, g, 1, lo, hi)
        &&& a.abs@[g] as int == lsum(sv, ps, g, 2, lo, hi)
    }
}

/// `|l_extendedprice * (100 - l_discount)| < 10^31` for numeric(15,2) values.
pub proof fn lemma_val_bound(p: i128, d: i128)
    requires num15(p), num15(d),
    ensures abs(p as int * (100 - d as int)) < 10_000_000_000_000_000_000_000_000_000_000,
{
    let x = abs(p as int);
    let y = abs(100 - d as int);
    assert(abs(p as int * (100 - d as int)) == x * y) by (nonlinear_arith)
        requires x == abs(p as int), y == abs(100 - d as int);
    assert(x < 1_000_000_000_000_000);
    assert(y < 10_000_000_000_000_000);
    assert(x * y < 10_000_000_000_000_000_000_000_000_000_000) by (nonlinear_arith)
        requires 0 <= x < 1_000_000_000_000_000, 0 <= y < 10_000_000_000_000_000;
}

/// Add row `i`'s contribution to the accumulators of rows `lo..i` (rows between the last row added and `i`
/// contribute nothing). `None` when an absolute sum would exceed `i128::MAX` (then `lsum(g, 2, lo, i + 1)` does).
pub fn acc_add(acc: &mut Acc, c: &ScanCols, q: bool, g: usize, i: usize, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>,
    Ghost(lo): Ghost<int>) -> (over: Option<usize>)
    requires
        line_cols_ok(*c, sv), 0 <= lo <= i < c.nl,
        acc_ok(*old(acc), sv, ps, lo, i as int),
        q == line_qual(sv, ps, i as int),
        q ==> g < 4 && g as int == line_grp(sv, ps, i as int),
    ensures
        over is None ==> acc_ok(*final(acc), sv, ps, lo, i + 1),
        over matches Some(h) ==> h < 4 && lsum(sv, ps, h as int, 2, lo, i + 1) > i128_max(),
    no_unwind
{
    let ghost a0 = *acc;
    if !q {
        proof {
            assert forall|h: int, w: int| 0 <= h < 4 implies #[trigger] lsum(sv, ps, h, w, lo, i + 1)
                == lsum(sv, ps, h, w, lo, i as int) by {
                assert(lterm(sv, ps, h, w, i as int) == 0);
            }
            assert forall|h: int| 0 <= h < 4 implies {
                &&& #[trigger] acc.cnt@[h] as int == lsum(sv, ps, h, 0, lo, i + 1)
                &&& acc.sum@[h] as int == lsum(sv, ps, h, 1, lo, i + 1)
                &&& acc.abs@[h] as int == lsum(sv, ps, h, 2, lo, i + 1)
            } by {}
        }
        return None;
    }
    let p = c.lprice[i];
    let d = c.ldisc[i];
    proof {
        lemma_val_bound(p, d);
    }
    let v: i128 = p * (100 - d);
    let av: i128 = if v < 0 { -v } else { v };
    let ghost val = line_val(sv, i as int);
    assert(v as int == val && av as int == abs(val));
    let a = acc.abs[g];
    let s = acc.sum[g];
    let n = acc.cnt[g];
    proof {
        lemma_lsum_bounds(sv, ps, g as int, lo, i as int);
        lemma_lsum_count(sv, ps, g as int, lo, i as int);
    }
    if a > i128::MAX - av {
        proof {
            assert(lsum(sv, ps, g as int, 2, lo, i + 1) == lsum(sv, ps, g as int, 2, lo, i as int) + abs(val));
        }
        return Some(g);
    }
    acc.abs[g] = a + av;
    acc.sum[g] = s + v;
    acc.cnt[g] = n + 1;
    proof {
        assert forall|h: int| 0 <= h < 4 implies {
            &&& #[trigger] acc.cnt@[h] as int == lsum(sv, ps, h, 0, lo, i + 1)
            &&& acc.sum@[h] as int == lsum(sv, ps, h, 1, lo, i + 1)
            &&& acc.abs@[h] as int == lsum(sv, ps, h, 2, lo, i + 1)
        } by {
            if h != g {
                assert(acc.cnt@[h] == a0.cnt@[h] && acc.sum@[h] == a0.sum@[h] && acc.abs@[h] == a0.abs@[h]);
            }
        }
    }
    None
}

/// Counts are bounded by the number of rows.
pub proof fn lemma_lsum_count(sv: StoresView, ps: Seq<Literal>, g: int, lo: int, hi: int)
    requires lo <= hi,
    ensures lsum(sv, ps, g, 0, lo, hi) <= hi - lo,
    decreases hi - lo,
{
    if hi > lo {
        lemma_lsum_count(sv, ps, g, lo, hi - 1);
    }
}

/// The accumulators of `lo..x` are those of `lo..y` when no row of `x..y` qualifies.
proof fn lemma_acc_skip(a: Acc, sv: StoresView, ps: Seq<Literal>, lo: int, x: int, y: int)
    requires
        lo <= x <= y, acc_ok(a, sv, ps, lo, x),
        forall|l: int| x <= l < y ==> !#[trigger] line_qual(sv, ps, l),
    ensures acc_ok(a, sv, ps, lo, y),
{
    assert forall|h: int| 0 <= h < 4 implies {
        &&& #[trigger] a.cnt@[h] as int == lsum(sv, ps, h, 0, lo, y)
        &&& a.sum@[h] as int == lsum(sv, ps, h, 1, lo, y)
        &&& a.abs@[h] as int == lsum(sv, ps, h, 2, lo, y)
    } by {
        lemma_no_qual(sv, ps, h, 0, x, y);
        lemma_no_qual(sv, ps, h, 1, x, y);
        lemma_no_qual(sv, ps, h, 2, x, y);
        lemma_lsum_split(sv, ps, h, 0, lo, x, y);
        lemma_lsum_split(sv, ps, h, 1, lo, x, y);
        lemma_lsum_split(sv, ps, h, 2, lo, x, y);
    }
}

/// Stage 5: the listed qualifying rows of `b..e` added to the accumulators of `lo..b`.
fn qual_sums(c: &ScanCols, qb: &Vec<usize>, gb: &Vec<u8>, nq: usize, b: usize, e: usize, acc: &mut Acc,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(lo): Ghost<int>) -> (over: Option<usize>)
    requires
        line_cols_ok(*c, sv), 0 <= lo <= b < e <= c.nl,
        qb@.len() == CAP, gb@.len() == CAP,
        quals_ok(qb@, gb@, nq as int, sv, ps, b as int, e as int),
        acc_ok(*old(acc), sv, ps, lo, b as int),
    ensures
        over is None ==> acc_ok(*final(acc), sv, ps, lo, e as int),
        over matches Some(h) ==> h < 4 && exists|x: int| lo <= x <= e && lsum(sv, ps, h as int, 2, lo, x) > i128_max(),
    no_unwind
{
    let mut t: usize = 0;
    let ghost mut next: int = b as int;
    while t < nq
        invariant
            line_cols_ok(*c, sv), 0 <= lo <= b < e <= c.nl,
            qb@.len() == CAP, gb@.len() == CAP, t <= nq,
            quals_ok(qb@, gb@, nq as int, sv, ps, b as int, e as int),
            b <= next <= e,
            t < nq ==> next <= qb@[t as int],
            t > 0 ==> next == qb@[t - 1] + 1,
            t == 0 ==> next == b,
            acc_ok(*acc, sv, ps, lo, next),
        decreases nq - t,
    {
        let i = qb[t];
        let g = gb[t] as usize;
        // rows next..i do not qualify
        proof {
            assert forall|l: int| next <= l < i implies !#[trigger] line_qual(sv, ps, l) by {
                if line_qual(sv, ps, l) {
                    let tt = choose|tt: int| 0 <= tt < nq && qb@[tt] == l;
                    if tt < t - 1 {
                        assert(qb@[tt] < qb@[t - 1]);
                    } else if tt > t {
                        assert(qb@[t as int] < qb@[tt]);
                    }
                }
            }
            lemma_acc_skip(*acc, sv, ps, lo, next, i as int);
        }
        match acc_add(acc, c, true, g, i, Ghost(sv), Ghost(ps), Ghost(lo)) {
            Some(h) => { return Some(h); },
            None => {},
        }
        proof { next = i + 1; }
        t = t + 1;
    }
    proof {
        assert forall|l: int| next <= l < e implies !#[trigger] line_qual(sv, ps, l) by {
            if line_qual(sv, ps, l) {
                let tt = choose|tt: int| 0 <= tt < nq && qb@[tt] == l;
                if tt < nq - 1 { assert(qb@[tt] < qb@[nq - 1]); }
            }
        }
        lemma_acc_skip(*acc, sv, ps, lo, next, e as int);
    }
    None
}

// ------------------------------------------------------------------------------------------------ the task

/// The candidate buffers of a task (`CAP` entries each).
pub struct Bufs {
    pub buf: Vec<usize>,
    pub tb: Vec<u8>,
    pub kb: Vec<i64>,
    pub cb: Vec<usize>,
    pub qb: Vec<usize>,
    pub gb: Vec<u8>,
}

pub open spec fn bufs_ok(x: Bufs) -> bool {
    &&& x.buf@.len() == CAP && x.tb@.len() == CAP && x.kb@.len() == CAP
    &&& x.cb@.len() == CAP && x.qb@.len() == CAP && x.gb@.len() == CAP
}

/// Fresh buffers (calling thread).
pub fn bufs_new() -> (x: Bufs)
    ensures bufs_ok(x),
{
    Bufs { buf: filled(CAP, 0usize), tb: filled(CAP, 0u8), kb: filled(CAP, 0i64), cb: filled(CAP, 0usize), qb: filled(CAP, 0usize),
        gb: filled(CAP, 0u8) }
}

/// One task of the scan: rows `lo..hi`, with its preallocated buffers and accumulators.
pub struct ScanTask {
    pub cols: ScanCols,
    pub swords: Arc<Vec<u64>>,
    pub cwords: Arc<Vec<u64>>,
    pub lo: usize,
    pub hi: usize,
    pub bufs: Bufs,
    pub acc: Acc,
    pub sv: Ghost<StoresView>,
    pub ps: Ghost<Seq<Literal>>,
}

/// A task's result: the accumulators of its rows, or the group whose absolute sum over some prefix of its rows
/// exceeds `i128::MAX`.
pub struct ScanOut {
    pub acc: Acc,
    pub over: Option<usize>,
}

/// The result of a task over rows `lo..hi`.
pub open spec fn scan_out_ok(o: ScanOut, sv: StoresView, ps: Seq<Literal>, lo: int, hi: int) -> bool {
    &&& o.over is None ==> acc_ok(o.acc, sv, ps, lo, hi)
    &&& o.over matches Some(h) ==> h < 4 && exists|x: int| lo <= x <= hi && lsum(sv, ps, h as int, 2, lo, x) > i128_max()
}

/// Zero accumulators (four groups).
pub open spec fn acc_zeroed(a: Acc) -> bool {
    &&& a.cnt@ == Seq::new(4, |_i: int| 0usize)
    &&& a.sum@ == Seq::new(4, |_i: int| 0i128)
    &&& a.abs@ == Seq::new(4, |_i: int| 0i128)
}

/// Fresh zero accumulators (calling thread).
pub fn acc_zero() -> (a: Acc)
    ensures acc_zeroed(a),
{
    Acc { cnt: filled(4, 0usize), sum: filled(4, 0i128), abs: filled(4, 0i128) }
}

/// Zero accumulators are the sums over an empty range.
pub proof fn lemma_acc_empty(a: Acc, sv: StoresView, ps: Seq<Literal>, lo: int)
    requires acc_zeroed(a),
    ensures acc_ok(a, sv, ps, lo, lo),
{
    assert forall|g: int| 0 <= g < 4 implies {
        &&& #[trigger] a.cnt@[g] as int == lsum(sv, ps, g, 0, lo, lo)
        &&& a.sum@[g] as int == lsum(sv, ps, g, 1, lo, lo)
        &&& a.abs@[g] as int == lsum(sv, ps, g, 2, lo, lo)
    } by {}
}

/// The scan of rows `lo..hi` (the body of a task), in rounds.
fn scan_range(c: &ScanCols, swords: &Vec<u64>, cwords: &Vec<u64>, lo: usize, hi: usize, bufs: Bufs, acc: Acc,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (out: ScanOut)
    requires
        scan_inputs_ok(*c, swords@, cwords@, sv, ps),
        lo <= hi <= c.nl,
        bufs_ok(bufs),
        acc_zeroed(acc),
    ensures scan_out_ok(out, sv, ps, lo as int, hi as int),
    no_unwind
{
    let Bufs { mut buf, mut tb, mut kb, mut cb, mut qb, mut gb } = bufs;
    let mut acc = acc;
    proof { lemma_acc_empty(acc, sv, ps, lo as int); }
    let table = tz_table_array();
    let mut b = lo;
    while b < hi
        invariant
            scan_inputs_ok(*c, swords@, cwords@, sv, ps), table@.len() == 64,
            lo <= b <= hi <= c.nl,
            buf@.len() == CAP, tb@.len() == CAP, kb@.len() == CAP, cb@.len() == CAP, qb@.len() == CAP, gb@.len() == CAP,
            acc_ok(acc, sv, ps, lo as int, b as int),
        decreases hi - b,
    {
        let (n, e) = collect(c, swords, &table, b, hi, &mut buf, &mut tb, Ghost(sv), Ghost(ps));
        cand_keys(c, &buf, n, &mut kb, Ghost(sv));
        cand_custs(c, &buf, &kb, n, &mut cb, Ghost(sv));
        let nq = cand_quals(c, cwords, &buf, &tb, &cb, n, &mut qb, &mut gb, Ghost(sv), Ghost(ps), Ghost(b as int), Ghost(e as int));
        match qual_sums(c, &qb, &gb, nq, b, e, &mut acc, Ghost(sv), Ghost(ps), Ghost(lo as int)) {
            Some(h) => {
                proof {
                    let x = choose|x: int| lo <= x <= e && lsum(sv, ps, h as int, 2, lo as int, x) > i128_max();
                    assert(lo <= x <= hi && lsum(sv, ps, h as int, 2, lo as int, x) > i128_max());
                }
                return ScanOut { acc, over: Some(h) };
            },
            None => {},
        }
        b = e;
    }
    ScanOut { acc, over: None }
}

impl WorkerTask for ScanTask {
    type Output = ScanOut;

    open spec fn pre(&self) -> bool {
        &&& scan_inputs_ok(self.cols, self.swords@, self.cwords@, self.sv@, self.ps@)
        &&& self.lo <= self.hi <= self.cols.nl
        &&& bufs_ok(self.bufs)
        &&& acc_zeroed(self.acc)
    }

    open spec fn post(&self, out: ScanOut) -> bool {
        scan_out_ok(out, self.sv@, self.ps@, self.lo as int, self.hi as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: ScanOut) {
        let swords: &Vec<u64> = &*self.swords;
        let cwords: &Vec<u64> = &*self.cwords;
        scan_range(&self.cols, swords, cwords, self.lo, self.hi, self.bufs, self.acc, Ghost(self.sv@), Ghost(self.ps@))
    }
}

} // verus!
