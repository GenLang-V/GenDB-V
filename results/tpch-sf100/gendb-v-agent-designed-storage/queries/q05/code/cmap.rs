//! The packed customer and supplier maps: 4 bits per stored row (16 rows per `u64` word), 0 when the row's nation
//! key is in no entry of the qualifying-nation list, else the last such entry's index + 1 (`qvl`, a function of the
//! key, so a customer and a supplier are in the same qualifying nation exactly when their nonzero values agree).
//! A few MB, so per-order and per-line lookups stay in cache where the nation columns do not.
//! Built in one dispatch with the dense-key checks (`build_maps`): task `t` fills customer words
//! `[t * cwc, (t + 1) * cwc)` and supplier words `[t * cws, (t + 1) * cws)` (`fill_words`: within a block of rows, a
//! 256-entry table of code -> value); a lookup reads chunk `w / cw`, word `w % cw` of word `w = row / 16`.
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS, WorkerTask, fork_join};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::gendb_entry::work::filled;
use crate::agent::common::forview::*;
use crate::agent::common::dense::{dense_on, check_dense};

verus! {

/// Nibble `b` of word `w`.
pub open spec fn nib(w: u64, b: u64) -> u64 {
    (w >> (b << 2u64)) & 15u64
}

/// Map value `v` for nation key `cnk`: 0 when no entry has the key, else entry `v - 1` has it.
pub open spec fn qual_nib(qkey: Seq<i64>, v: u64, cnk: int) -> bool {
    &&& v == 0 ==> forall|q: int| 0 <= q < qkey.len() ==> #[trigger] qkey[q] as int != cnk
    &&& v != 0 ==> v - 1 < qkey.len() && qkey[v - 1] as int == cnk
}

/// The map value of nation key `key` over the first `n` entries: the last entry with the key, plus 1, else 0.
pub open spec fn qv(qkey: Seq<i64>, key: int, n: int) -> u64
    decreases n,
{
    if n <= 0 { 0 } else if qkey[n - 1] as int == key { n as u64 } else { qv(qkey, key, n - 1) }
}

/// `qv` names an entry with the key, or none has it.
pub proof fn lemma_qv(qkey: Seq<i64>, key: int, n: int)
    requires 0 <= n <= qkey.len(), n < 16,
    ensures
        qv(qkey, key, n) <= n,
        qv(qkey, key, n) == 0 ==> forall|q: int| 0 <= q < n ==> #[trigger] qkey[q] as int != key,
        qv(qkey, key, n) != 0 ==> qkey[qv(qkey, key, n) - 1] as int == key,
    decreases n,
{
    if n > 0 {
        lemma_qv(qkey, key, n - 1);
    }
}

/// The map value of the whole list.
pub open spec fn qvl(qkey: Seq<i64>, key: int) -> u64 {
    qv(qkey, key, qkey.len() as int)
}

/// `qvl` describes the list.
pub proof fn lemma_qvl(qkey: Seq<i64>, key: int)
    requires qkey.len() < 16,
    ensures qual_nib(qkey, qvl(qkey, key), key), qvl(qkey, key) < 16,
{
    lemma_qv(qkey, key, qkey.len() as int);
}

/// Customer row `c` has its word in the chunks.
pub open spec fn cmap_has(ms: Seq<Vec<u64>>, cw: int, c: int) -> bool {
    &&& (c / 16) / cw < ms.len()
    &&& (c / 16) % cw < ms[(c / 16) / cw]@.len()
}

/// The map value of customer row `c`.
pub open spec fn cmap_val(ms: Seq<Vec<u64>>, cw: int, c: int) -> u64 {
    nib(ms[(c / 16) / cw]@[(c / 16) % cw], (c % 16) as u64)
}

/// The map covers customer rows `[0, n)` of the nation column.
pub open spec fn cmap_ok(ms: Seq<Vec<u64>>, cw: int, qkey: Seq<i64>, cn_c: Seq<u8>, cn_b: Seq<i64>, bs: int, n: int) -> bool {
    &&& cw >= 1
    &&& forall|c: int| 0 <= c < n ==> #[trigger] cmap_has(ms, cw, c)
    &&& forall|c: int| 0 <= c < n ==> #[trigger] cmap_val(ms, cw, c) == qvl(qkey, fv8(cn_c, cn_b, bs, c))
}

proof fn lemma_nib_set_same(w: u64, v: u64, b: u64)
    requires b < 16, v < 16, (w >> (b << 2u64)) & 15u64 == 0,
    ensures ((w | (v << (b << 2u64))) >> (b << 2u64)) & 15u64 == v,
{
    assert(((w | (v << (b << 2u64))) >> (b << 2u64)) & 15u64 == v) by (bit_vector)
        requires b < 16, v < 16, (w >> (b << 2u64)) & 15u64 == 0;
}

proof fn lemma_nib_set_other(w: u64, v: u64, b: u64, b2: u64)
    requires b < 16, b2 < 16, b2 != b, v < 16,
    ensures ((w | (v << (b << 2u64))) >> (b2 << 2u64)) & 15u64 == (w >> (b2 << 2u64)) & 15u64,
{
    assert(((w | (v << (b << 2u64))) >> (b2 << 2u64)) & 15u64 == (w >> (b2 << 2u64)) & 15u64) by (bit_vector)
        requires b < 16, b2 < 16, b2 != b, v < 16;
}

pub proof fn lemma_shift_ok(b: u64)
    requires b < 16,
    ensures b << 2u64 < 64,
{
    assert(b << 2u64 < 64) by (bit_vector) requires b < 16;
}

pub proof fn lemma_nib_zero(b: u64)
    ensures (0u64 >> (b << 2u64)) & 15u64 == 0,
{
    assert((0u64 >> (b << 2u64)) & 15u64 == 0) by (bit_vector);
}

/// A nibble is below 16.
pub proof fn lemma_nib_lt16(w: u64, b: u64)
    ensures nib(w, b) < 16,
{
    lemma_nib_small(w, b);
}

pub proof fn lemma_nib_small(w: u64, b: u64)
    ensures (w >> (b << 2u64)) & 15u64 < 16,
{
    assert((w >> (b << 2u64)) & 15u64 < 16) by (bit_vector);
}

/// The map value of nation key `cnk` (the last entry with the key, branch free).
fn qual_val(qkey: &Vec<i64>, cnk: i64) -> (v: u64)
    requires qkey@.len() < 16,
    ensures v < 16, v == qvl(qkey@, cnk as int),
    no_unwind
{
    let n = qkey.len();
    let mut v: u64 = 0;
    let mut q: usize = 0;
    while q < n
        invariant
            n == qkey@.len(), n < 16, q <= n,
            v <= q,
            v == qv(qkey@, cnk as int, q as int),
        decreases n - q,
    {
        if qkey[q] == cnk {
            v = q as u64 + 1;
        }
        q = q + 1;
    }
    v
}

/// The nibble words `[wa, wa + len)` hold the map values of their rows below `n`.
pub open spec fn words_ok(out: Seq<u64>, wa: int, qkey: Seq<i64>, cn_c: Seq<u8>, cn_b: Seq<i64>, bs: int, n: int) -> bool {
    forall|c: int| 16 * wa <= c < 16 * (wa + out.len()) && c < n ==>
        #[trigger] nib(out[c / 16 - wa], (c % 16) as u64) == qvl(qkey, fv8(cn_c, cn_b, bs, c))
}

/// `min(x, n)`.
pub open spec fn rmin(x: int, n: int) -> int {
    if x < n { x } else { n }
}

/// `tab[x]` is the map value of nation key `base + x`.
pub open spec fn tab_ok(tab: Seq<u8>, qkey: Seq<i64>, base: int) -> bool {
    &&& tab.len() == 256
    &&& forall|x: int| 0 <= x < 256 ==> #[trigger] tab[x] as u64 == qvl(qkey, base + x)
}

/// The map value of a (wide) nation key.
fn qual_val_wide(qkey: &Vec<i64>, key: i128) -> (v: u64)
    requires qkey@.len() < 16,
    ensures v < 16, v == qvl(qkey@, key as int),
    no_unwind
{
    let n = qkey.len();
    let mut v: u64 = 0;
    let mut q: usize = 0;
    while q < n
        invariant
            n == qkey@.len(), n < 16, q <= n,
            v <= q,
            v == qv(qkey@, key as int, q as int),
        decreases n - q,
    {
        if qkey[q] as i128 == key {
            v = q as u64 + 1;
        }
        q = q + 1;
    }
    v
}

/// The map values of the 256 codes over base `base`.
fn fill_tab(tab: &mut Vec<u8>, qkey: &Vec<i64>, base: i64)
    requires old(tab)@.len() == 256, qkey@.len() < 16,
    ensures tab_ok(final(tab)@, qkey@, base as int),
    no_unwind
{
    let mut x: usize = 0;
    while x < 256
        invariant
            tab@.len() == 256, qkey@.len() < 16, x <= 256,
            forall|y: int| 0 <= y < x ==> #[trigger] tab@[y] as u64 == qvl(qkey@, base as int + y),
        decreases 256 - x,
    {
        let v = qual_val_wide(qkey, base as i128 + x as i128);
        let ghost t0 = tab@;
        tab[x] = v as u8;
        proof {
            assert forall|y: int| 0 <= y < x + 1 implies #[trigger] tab@[y] as u64 == qvl(qkey@, base as int + y) by {
                if y < x {
                    assert(tab@[y] == t0[y]);
                }
            }
        }
        x = x + 1;
    }
}

/// One more row in a dense check.
proof fn lemma_dense_step(kc: Seq<u32>, kb: Seq<i64>, bs: int, lo: int, x: int)
    requires lo <= x,
    ensures
        dense_on(kc, kb, bs, lo, x + 1) == (dense_on(kc, kb, bs, lo, x) && fv32(kc, kb, bs, x) == x + 1),
{
    if dense_on(kc, kb, bs, lo, x + 1) {
        assert(fv32(kc, kb, bs, x) == x + 1);
    }
}

/// The nibble words `[wa, wa + out.len())` of a nation column, and whether the key column holds `row + 1` on
/// their rows. Within a block of rows (one base) a 256-entry table gives each code's map value.
fn fill_words(codes: &[u8], bases: &[i64], kc: &[u32], kb: &[i64], d: Div, n: usize, qkey: &Vec<i64>, wa: usize,
    out: Vec<u64>, tab: &mut Vec<u8>) -> (r: (Vec<u64>, bool))
    requires
        d.ok(), col8_ok(codes@, bases@, d.bs as int, n as int), col32_ok(kc@, kb@, d.bs as int, n as int),
        qkey@.len() < 16, 16 * (wa + out@.len()) <= usize::MAX, old(tab)@.len() == 256,
    ensures
        r.0@.len() == out@.len(), final(tab)@.len() == 256,
        words_ok(r.0@, wa as int, qkey@, codes@, bases@, d.bs as int, n as int),
        r.1 == dense_on(kc@, kb@, d.bs as int, 16 * wa, rmin(16 * (wa + out@.len()), n as int)),
    no_unwind
{
    let ghost bs = d.bs as int;
    let use_tab = d.bs >= 1024;
    let mut tblk: usize = usize::MAX;
    let mut dense = true;
    let len = out.len();
    let mut out = out;
    let mut i: usize = 0;
    while i < len
        invariant
            d.ok(), col8_ok(codes@, bases@, bs, n as int), col32_ok(kc@, kb@, bs, n as int), bs == d.bs as int,
            qkey@.len() < 16,
            16 * (wa + len) <= usize::MAX,
            len == out@.len(), tab@.len() == 256,
            i <= len,
            tblk != usize::MAX ==> tblk < bases@.len() && tab_ok(tab@, qkey@, bases@[tblk as int] as int),
            forall|c: int| 16 * wa <= c < 16 * (wa + i) && c < n ==>
                #[trigger] nib(out@[c / 16 - wa], (c % 16) as u64) == qvl(qkey@, fv8(codes@, bases@, bs, c)),
            dense == dense_on(kc@, kb@, bs, 16 * wa, rmin(16 * (wa + i), n as int)),
        decreases len - i,
    {
        let base = (wa + i) * 16;
        let mut wd: u64 = 0;
        let mut b: usize = 0;
        proof {
            assert forall|b2: u64| b2 < 16 implies #[trigger] nib(wd, b2) == 0 by {
                lemma_nib_zero(b2);
            }
        }
        // fast path: the word's 16 rows lie in one block of rows (one base, the table filled once per block)
        if use_tab && base + 16 <= n {
            let fblk = div_of(d, base);
            proof {
                lemma_block_index(base as int, bs, bases@.len() as int);
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(base as int, bs);
                vstd::arithmetic::div_mod::lemma_mod_pos_bound(base as int, bs);
                assert(bs * fblk == fblk * bs) by (nonlinear_arith);
            }
            if 16 <= d.bs - (base - fblk * d.bs) {
                if fblk != tblk {
                    fill_tab(tab, qkey, bases[fblk]);
                    tblk = fblk;
                }
                proof {
                    lemma_block_index(base as int, bs, kb@.len() as int);
                }
                let kbase = kb[fblk];
                while b < 16
                    invariant
                        d.ok(), col8_ok(codes@, bases@, bs, n as int), col32_ok(kc@, kb@, bs, n as int), bs == d.bs as int,
                        qkey@.len() < 16, tab@.len() == 256,
                        base as int == 16 * (wa + i), 16 * (wa + i + 1) <= usize::MAX, base + 16 <= n,
                        fblk * bs <= base, base + 16 <= fblk * bs + bs, fblk < bases@.len(), fblk < kb@.len(),
                        tblk == fblk, tab_ok(tab@, qkey@, bases@[fblk as int] as int), kbase == kb@[fblk as int],
                        b <= 16,
                        tblk != usize::MAX ==> tblk < bases@.len() && tab_ok(tab@, qkey@, bases@[tblk as int] as int),
                        forall|b2: u64| b2 < b && base + b2 < n ==>
                            #[trigger] nib(wd, b2) == qvl(qkey@, fv8(codes@, bases@, bs, base + b2)),
                        forall|b2: u64| b <= b2 < 16 ==> #[trigger] nib(wd, b2) == 0,
                        dense == dense_on(kc@, kb@, bs, 16 * wa, rmin(base + b, n as int)),
                    decreases 16 - b,
                {
                    let c = base + b;
                    proof {
                        crate::agent::kernel::lemma_in_blk(c as int, bs, fblk as int);
                        assert(fv8(codes@, bases@, bs, c as int) == bases@[fblk as int] + codes@[c as int]);
                        assert(fv32(kc@, kb@, bs, c as int) == kb@[fblk as int] + kc@[c as int]);
                    }
                    let code = codes[c];
                    let tv = tab[code as usize] as u64;
                    proof {
                        assert(tab@[code as int] as u64 == qvl(qkey@, bases@[fblk as int] as int + code as int));
                        lemma_qv(qkey@, fv8(codes@, bases@, bs, c as int), qkey@.len() as int);
                    }
                    let k = kc[c] as i64 + kbase;
                    proof {
                        lemma_dense_step(kc@, kb@, bs, 16 * wa, c as int);
                    }
                    dense = if k as i128 == c as i128 + 1 { dense } else { false };
                    let ghost w0 = wd;
                    let bb = b as u64;
                    proof {
                        lemma_shift_ok(bb);
                    }
                    wd = wd | (tv << (bb << 2u64));
                    proof {
                        assert(nib(w0, bb) == 0);
                        lemma_nib_set_same(w0, tv, bb);
                        assert forall|b2: u64| b2 < 16 && b2 != bb implies #[trigger] nib(wd, b2) == nib(w0, b2) by {
                            lemma_nib_set_other(w0, tv, bb, b2);
                        }
                        assert forall|b2: u64| b2 < b + 1 && base + b2 < n implies
                            #[trigger] nib(wd, b2) == qvl(qkey@, fv8(codes@, bases@, bs, base + b2)) by {
                            if b2 != bb {
                                assert(nib(wd, b2) == nib(w0, b2));
                            }
                        }
                    }
                    b = b + 1;
                }
            }
        }
        while b < 16
            invariant
                d.ok(), col8_ok(codes@, bases@, bs, n as int), col32_ok(kc@, kb@, bs, n as int), bs == d.bs as int,
                qkey@.len() < 16, tab@.len() == 256,
                base as int == 16 * (wa + i), 16 * (wa + i + 1) <= usize::MAX,
                b <= 16,
                tblk != usize::MAX ==> tblk < bases@.len() && tab_ok(tab@, qkey@, bases@[tblk as int] as int),
                forall|b2: u64| b2 < b && base + b2 < n ==>
                    #[trigger] nib(wd, b2) == qvl(qkey@, fv8(codes@, bases@, bs, base + b2)),
                forall|b2: u64| b <= b2 < 16 ==> #[trigger] nib(wd, b2) == 0,
                dense == dense_on(kc@, kb@, bs, 16 * wa, rmin(base + b, n as int)),
            decreases 16 - b,
        {
            let c = base + b;
            if c < n {
                let v: u64 = if use_tab {
                    let blk = div_of(d, c);
                    proof {
                        lemma_block_index(c as int, bs, bases@.len() as int);
                    }
                    if blk != tblk {
                        fill_tab(tab, qkey, bases[blk]);
                        tblk = blk;
                    }
                    let code = codes[c];
                    let tv = tab[code as usize] as u64;
                    proof {
                        assert(tab@[code as int] as u64 == qvl(qkey@, bases@[blk as int] as int + code as int));
                    }
                    tv
                } else {
                    let cnk = get8(codes, bases, d, n, c);
                    qual_val(qkey, cnk)
                };
                proof {
                    lemma_qv(qkey@, fv8(codes@, bases@, bs, c as int), qkey@.len() as int);
                }
                let k = get32(kc, kb, d, n, c);
                proof {
                    lemma_dense_step(kc@, kb@, bs, 16 * wa, c as int);
                }
                dense = dense && (k as i128 == c as i128 + 1);
                let ghost w0 = wd;
                let bb = b as u64;
                proof {
                    lemma_shift_ok(bb);
                }
                wd = wd | (v << (bb << 2u64));
                proof {
                    assert(nib(w0, bb) == 0);
                    lemma_nib_set_same(w0, v, bb);
                    assert forall|b2: u64| b2 < 16 && b2 != bb implies #[trigger] nib(wd, b2) == nib(w0, b2) by {
                        lemma_nib_set_other(w0, v, bb, b2);
                    }
                    assert forall|b2: u64| b2 < b + 1 && base + b2 < n implies
                        #[trigger] nib(wd, b2) == qvl(qkey@, fv8(codes@, bases@, bs, base + b2)) by {
                        if b2 != bb {
                            assert(nib(wd, b2) == nib(w0, b2));
                        }
                    }
                }
            } else {
                proof {
                    assert forall|b2: u64| b2 < b + 1 && base + b2 < n implies
                        #[trigger] nib(wd, b2) == qvl(qkey@, fv8(codes@, bases@, bs, base + b2)) by {
                    }
                }
            }
            b = b + 1;
        }
        let ghost o0 = out@;
        out[i] = wd;
        proof {
            assert forall|c: int| 16 * wa <= c < 16 * (wa + i + 1) && c < n implies
                #[trigger] nib(out@[c / 16 - wa], (c % 16) as u64) == qvl(qkey@, fv8(codes@, bases@, bs, c)) by {
                if c < 16 * (wa + i) {
                    assert(c / 16 - wa < i);
                    assert(out@[c / 16 - wa] == o0[c / 16 - wa]);
                } else {
                    assert(c / 16 == wa + i);
                    let b2 = (c % 16) as u64;
                    assert(c == base + b2);
                    assert(out@[c / 16 - wa] == wd);
                }
            }
        }
        i = i + 1;
    }
    (out, dense)
}

/// One prep task: the customer nibble words `[wa_c, wa_c + out_c.len())` and the supplier nibble words
/// `[wa_s, wa_s + out_s.len())`, with the dense-key checks of their rows.
pub struct PrepTask {
    pub cn_c: &'static [u8],
    pub cn_b: &'static [i64],
    pub ck_c: &'static [u32],
    pub ck_b: &'static [i64],
    pub cd: Div,
    pub n_c: usize,
    pub sn_c: &'static [u8],
    pub sn_b: &'static [i64],
    pub sk_c: &'static [u32],
    pub sk_b: &'static [i64],
    pub sd: Div,
    pub n_s: usize,
    pub qkey: Vec<i64>,
    pub wa_c: usize,
    pub out_c: Vec<u64>,
    pub wa_s: usize,
    pub out_s: Vec<u64>,
    pub tab: Vec<u8>,
}

/// A prep task's words and dense flags.
pub struct PrepOut {
    pub wc: Vec<u64>,
    pub dc: bool,
    pub ws: Vec<u64>,
    pub ds: bool,
}

impl WorkerTask for PrepTask {
    type Output = PrepOut;

    open spec fn pre(&self) -> bool {
        &&& self.cd.ok() && col8_ok(self.cn_c@, self.cn_b@, self.cd.bs as int, self.n_c as int)
        &&& col32_ok(self.ck_c@, self.ck_b@, self.cd.bs as int, self.n_c as int)
        &&& self.sd.ok() && col8_ok(self.sn_c@, self.sn_b@, self.sd.bs as int, self.n_s as int)
        &&& col32_ok(self.sk_c@, self.sk_b@, self.sd.bs as int, self.n_s as int)
        &&& self.qkey@.len() < 16
        &&& 16 * (self.wa_c + self.out_c@.len()) <= usize::MAX
        &&& 16 * (self.wa_s + self.out_s@.len()) <= usize::MAX
        &&& self.tab@.len() == 256
    }

    open spec fn post(&self, out: PrepOut) -> bool {
        &&& out.wc@.len() == self.out_c@.len()
        &&& words_ok(out.wc@, self.wa_c as int, self.qkey@, self.cn_c@, self.cn_b@, self.cd.bs as int, self.n_c as int)
        &&& out.dc == dense_on(self.ck_c@, self.ck_b@, self.cd.bs as int, 16 * self.wa_c,
                rmin(16 * (self.wa_c + self.out_c@.len()), self.n_c as int))
        &&& out.ws@.len() == self.out_s@.len()
        &&& words_ok(out.ws@, self.wa_s as int, self.qkey@, self.sn_c@, self.sn_b@, self.sd.bs as int, self.n_s as int)
        &&& out.ds == dense_on(self.sk_c@, self.sk_b@, self.sd.bs as int, 16 * self.wa_s,
                rmin(16 * (self.wa_s + self.out_s@.len()), self.n_s as int))
    }

    fn declared_rows(&self) -> (u64, u64) {
        let e = if self.out_c.len() <= usize::MAX - self.wa_c { self.wa_c + self.out_c.len() } else { usize::MAX };
        (self.wa_c as u64, e as u64)
    }

    fn run(self) -> (r: PrepOut) {
        let PrepTask { cn_c, cn_b, ck_c, ck_b, cd, n_c, sn_c, sn_b, sk_c, sk_b, sd, n_s, qkey, wa_c, out_c, wa_s, out_s, tab } = self;
        let mut tab = tab;
        let (wc, dc) = fill_words(cn_c, cn_b, ck_c, ck_b, cd, n_c, &qkey, wa_c, out_c, &mut tab);
        let (ws, ds) = fill_words(sn_c, sn_b, sk_c, sk_b, sd, n_s, &qkey, wa_s, out_s, &mut tab);
        PrepOut { wc, dc, ws, ds }
    }
}

/// The prep results: whether the customer and supplier keys are `row + 1`, and (`use_map`) both maps.
pub struct Prep {
    pub cdense: bool,
    pub sdense: bool,
    pub use_map: bool,
    pub cm: Arc<Vec<Vec<u64>>>,
    pub cmd: Div,
    pub sm: Arc<Vec<Vec<u64>>>,
    pub smd: Div,
}

/// The smallest power of two (at least 1) above `nw / workers`.
fn chunk_words(nw: usize, workers: usize) -> (cw: usize)
    requires 1 <= workers, nw < usize::MAX / 64,
    ensures 1 <= cw <= 2 * (nw / workers + 1),
{
    let per = nw / workers + 1;
    let mut cw: usize = 1;
    while cw < per
        invariant 1 <= cw <= 2 * per, per <= nw + 1, nw < usize::MAX / 64,
        decreases 2 * per - cw,
    {
        cw = cw * 2;
    }
    cw
}

/// Dense checks without the maps.
fn prep_plain(ck_c: &'static [u32], ck_b: &'static [i64], cd: Div, n_c: usize,
    sk_c: &'static [u32], sk_b: &'static [i64], sd: Div, n_s: usize, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<Prep, WorkerFailure>)
    requires
        cd.ok(), col32_ok(ck_c@, ck_b@, cd.bs as int, n_c as int),
        sd.ok(), col32_ok(sk_c@, sk_b@, sd.bs as int, n_s as int),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(pp) ==> pp.cdense == dense_on(ck_c@, ck_b@, cd.bs as int, 0, n_c as int)
            && pp.sdense == dense_on(sk_c@, sk_b@, sd.bs as int, 0, n_s as int) && !pp.use_map,
{
    let cdense = match check_dense(ck_c, ck_b, cd, n_c, workers, dispatch) {
        Ok(b) => b,
        Err(e) => return Err(e),
    };
    let sdense = match check_dense(sk_c, sk_b, sd, n_s, workers, dispatch) {
        Ok(b) => b,
        Err(e) => return Err(e),
    };
    Ok(Prep { cdense, sdense, use_map: false, cm: Arc::new(Vec::new()), cmd: div_new(1), sm: Arc::new(Vec::new()), smd: div_new(1) })
}

/// Task `t`'s rows of a table: `[min(16 t cw, n), min(16 (t + 1) cw, n))`.
proof fn lemma_task_rows(t: int, cw: int, nw: int, n: int, len: int)
    requires
        t >= 0, cw >= 1, nw == n / 16 + 1, n >= 0,
        len == if t * cw < nw { cw } else { 0 },
    ensures
        rmin(16 * (t * cw + len), n) == rmin(16 * ((t + 1) * cw), n),
        t * cw >= nw ==> rmin(16 * (t * cw), n) == n,
{
    assert((t + 1) * cw == t * cw + cw) by (nonlinear_arith);
    if t * cw >= nw {
        assert(16 * (t * cw) > n);
    }
}

/// The customer and supplier dense checks and maps, by at most `workers` threads in one dispatch.
pub fn build_maps(cn_c: &'static [u8], cn_b: &'static [i64], ck_c: &'static [u32], ck_b: &'static [i64], cd: Div, n_c: usize,
    sn_c: &'static [u8], sn_b: &'static [i64], sk_c: &'static [u32], sk_b: &'static [i64], sd: Div, n_s: usize,
    qkey: &Vec<i64>, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Prep, WorkerFailure>)
    requires
        cd.ok(), col8_ok(cn_c@, cn_b@, cd.bs as int, n_c as int), col32_ok(ck_c@, ck_b@, cd.bs as int, n_c as int),
        sd.ok(), col8_ok(sn_c@, sn_b@, sd.bs as int, n_s as int), col32_ok(sk_c@, sk_b@, sd.bs as int, n_s as int),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(pp) ==> pp.cdense == dense_on(ck_c@, ck_b@, cd.bs as int, 0, n_c as int)
            && pp.sdense == dense_on(sk_c@, sk_b@, sd.bs as int, 0, n_s as int)
            && (pp.use_map ==> qkey@.len() < 16 && pp.cmd.ok() && pp.smd.ok()
                && cmap_ok((*pp.cm)@, pp.cmd.bs as int, qkey@, cn_c@, cn_b@, cd.bs as int, n_c as int)
                && cmap_ok((*pp.sm)@, pp.smd.bs as int, qkey@, sn_c@, sn_b@, sd.bs as int, n_s as int)),
{
    if qkey.len() >= 16 || n_c >= usize::MAX / 64 || n_s >= usize::MAX / 64 {
        return prep_plain(ck_c, ck_b, cd, n_c, sk_c, sk_b, sd, n_s, workers, dispatch);
    }
    let nwc = n_c / 16 + 1;
    let nws = n_s / 16 + 1;
    let cwc = chunk_words(nwc, workers);
    let cws = chunk_words(nws, workers);
    let lim = usize::MAX / 64;
    if cwc > lim || cws > lim {
        return prep_plain(ck_c, ck_b, cd, n_c, sk_c, sk_b, sd, n_s, workers, dispatch);
    }
    let mut tasks: Vec<PrepTask> = Vec::new();
    let mut wc: usize = 0;
    let mut ws: usize = 0;
    let mut k: usize = 0;
    while (wc < nwc || ws < nws) && k < workers && wc < lim && ws < lim
        invariant
            cd.ok(), col8_ok(cn_c@, cn_b@, cd.bs as int, n_c as int), col32_ok(ck_c@, ck_b@, cd.bs as int, n_c as int),
            sd.ok(), col8_ok(sn_c@, sn_b@, sd.bs as int, n_s as int), col32_ok(sk_c@, sk_b@, sd.bs as int, n_s as int),
            qkey@.len() < 16, n_c < usize::MAX / 64, n_s < usize::MAX / 64,
            nwc == n_c / 16 + 1, nws == n_s / 16 + 1,
            lim == usize::MAX / 64, 1 <= cwc <= lim, 1 <= cws <= lim,
            1 <= workers <= MAX_WORKERS, k <= workers,
            wc == k * cwc, ws == k * cws,
            tasks@.len() == k,
            forall|i: int| 0 <= i < k ==> (#[trigger] tasks@[i]).pre()
                && tasks@[i].wa_c == i * cwc && tasks@[i].wa_s == i * cws
                && tasks@[i].cn_c == cn_c && tasks@[i].cn_b == cn_b && tasks@[i].ck_c == ck_c && tasks@[i].ck_b == ck_b
                && tasks@[i].cd == cd && tasks@[i].n_c == n_c
                && tasks@[i].sn_c == sn_c && tasks@[i].sn_b == sn_b && tasks@[i].sk_c == sk_c && tasks@[i].sk_b == sk_b
                && tasks@[i].sd == sd && tasks@[i].n_s == n_s
                && tasks@[i].qkey@ == qkey@
                && tasks@[i].out_c@.len() == (if i * cwc < nwc { cwc as int } else { 0 })
                && tasks@[i].out_s@.len() == (if i * cws < nws { cws as int } else { 0 }),
        decreases workers - k,
    {
        let lc = if wc < nwc { cwc } else { 0 };
        let ls = if ws < nws { cws } else { 0 };
        let task = PrepTask {
            cn_c, cn_b, ck_c, ck_b, cd, n_c, sn_c, sn_b, sk_c, sk_b, sd, n_s,
            qkey: copy_i64s(qkey),
            wa_c: wc, out_c: vec![0u64; lc],
            wa_s: ws, out_s: vec![0u64; ls],
            tab: filled(256, 0u8),
        };
        tasks.push(task);
        proof {
            assert((k + 1) * cwc == k * cwc + cwc) by (nonlinear_arith);
            assert((k + 1) * cws == k * cws + cws) by (nonlinear_arith);
        }
        wc = wc + cwc;
        ws = ws + cws;
        k = k + 1;
    }
    if wc < nwc || ws < nws {
        return prep_plain(ck_c, ck_b, cd, n_c, sk_c, sk_b, sd, n_s, workers, dispatch);
    }
    let ghost tk = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    // the chunks in task order, and the dense flags
    let ghost os = outs@;
    let mut outs = outs;
    let mut cms: Vec<Vec<u64>> = Vec::new();
    let mut sms: Vec<Vec<u64>> = Vec::new();
    let mut cdense = true;
    let mut sdense = true;
    while outs.len() > 0
        invariant
            os.len() == k, tk.len() == k,
            forall|x: int| 0 <= x < k ==> #[trigger] tk[x].post(os[x]),
            outs@ == os.subrange(0, outs@.len() as int),
            cms@.len() == k - outs@.len(), sms@.len() == k - outs@.len(),
            forall|x: int| 0 <= x < cms@.len() ==> #[trigger] cms@[x] == os[outs@.len() + x].wc,
            forall|x: int| 0 <= x < sms@.len() ==> #[trigger] sms@[x] == os[outs@.len() + x].ws,
            cdense == forall|x: int| outs@.len() <= x < k ==> #[trigger] os[x].dc,
            sdense == forall|x: int| outs@.len() <= x < k ==> #[trigger] os[x].ds,
        decreases outs@.len(),
    {
        let ghost m = outs@.len() as int;
        let o = outs.pop().unwrap();
        proof {
            assert(o == os[m - 1]);
        }
        let ghost c0 = cms@;
        let ghost s0 = sms@;
        cdense = cdense && o.dc;
        sdense = sdense && o.ds;
        cms.insert(0, o.wc);
        sms.insert(0, o.ws);
        proof {
            assert(outs@ =~= os.subrange(0, m - 1));
            assert forall|x: int| 0 <= x < cms@.len() implies #[trigger] cms@[x] == os[m - 1 + x].wc by {
                if x > 0 {
                    assert(cms@[x] == c0[x - 1]);
                }
            }
            assert forall|x: int| 0 <= x < sms@.len() implies #[trigger] sms@[x] == os[m - 1 + x].ws by {
                if x > 0 {
                    assert(sms@[x] == s0[x - 1]);
                }
            }
        }
    }
    let cd2 = div_new(cwc);
    let sd2 = div_new(cws);
    proof {
        assert(cms@.len() == k && sms@.len() == k);
        let fc = Seq::new(k as nat, |x: int| os[x].dc);
        let fs = Seq::new(k as nat, |x: int| os[x].ds);
        assert forall|x: int| 0 <= x < k implies (#[trigger] cms@[x])@.len() == (if x * cwc < nwc { cwc as int } else { 0 })
            && words_ok(cms@[x]@, x * cwc, qkey@, cn_c@, cn_b@, cd.bs as int, n_c as int)
            && fc[x] == dense_on(ck_c@, ck_b@, cd.bs as int, 16 * (x * cwc),
                rmin(16 * (x * cwc + (if x * cwc < nwc { cwc as int } else { 0 })), n_c as int)) by {
            assert(tk[x].post(os[x]));
        }
        assert forall|x: int| 0 <= x < k implies (#[trigger] sms@[x])@.len() == (if x * cws < nws { cws as int } else { 0 })
            && words_ok(sms@[x]@, x * cws, qkey@, sn_c@, sn_b@, sd.bs as int, n_s as int)
            && fs[x] == dense_on(sk_c@, sk_b@, sd.bs as int, 16 * (x * cws),
                rmin(16 * (x * cws + (if x * cws < nws { cws as int } else { 0 })), n_s as int)) by {
            assert(tk[x].post(os[x]));
        }
        assert forall|x: int| 0 <= x < k implies #[trigger] fc[x] == dense_on(ck_c@, ck_b@, cd.bs as int, 16 * (x * cwc),
                rmin(16 * (x * cwc + (if x * cwc < nwc { cwc as int } else { 0 })), n_c as int)) by {
            assert(cms@[x]@.len() >= 0);
        }
        assert forall|x: int| 0 <= x < k implies #[trigger] fs[x] == dense_on(sk_c@, sk_b@, sd.bs as int, 16 * (x * cws),
                rmin(16 * (x * cws + (if x * cws < nws { cws as int } else { 0 })), n_s as int)) by {
            assert(sms@[x]@.len() >= 0);
        }
        lemma_assemble(cms@, fc, cwc as int, nwc as int, qkey@, cn_c@, cn_b@, ck_c@, ck_b@, cd.bs as int, n_c as int, k as int);
        lemma_assemble(sms@, fs, cws as int, nws as int, qkey@, sn_c@, sn_b@, sk_c@, sk_b@, sd.bs as int, n_s as int, k as int);
        assert(cdense == forall|x: int| 0 <= x < k ==> #[trigger] fc[x]) by {
            if cdense {
                assert forall|x: int| 0 <= x < k implies #[trigger] fc[x] by {
                    assert(os[x].dc);
                }
            }
            if forall|x: int| 0 <= x < k ==> #[trigger] fc[x] {
                assert forall|x: int| 0 <= x < k implies #[trigger] os[x].dc by {
                    assert(fc[x]);
                }
            }
        }
        assert(sdense == forall|x: int| 0 <= x < k ==> #[trigger] fs[x]) by {
            if sdense {
                assert forall|x: int| 0 <= x < k implies #[trigger] fs[x] by {
                    assert(os[x].ds);
                }
            }
            if forall|x: int| 0 <= x < k ==> #[trigger] fs[x] {
                assert forall|x: int| 0 <= x < k implies #[trigger] os[x].ds by {
                    assert(fs[x]);
                }
            }
        }
    }
    let cm = Arc::new(cms);
    let sm = Arc::new(sms);
    proof {
        assert(*cm == cms);
        assert(*sm == sms);
    }
    Ok(Prep { cdense, sdense, use_map: true, cm, cmd: cd2, sm, smd: sd2 })
}

/// The assembled chunks of one table are its map, and the tasks' dense flags its dense check.
proof fn lemma_assemble(ms: Seq<Vec<u64>>, fl: Seq<bool>, cw: int, nw: int, qkey: Seq<i64>,
    codes: Seq<u8>, bases: Seq<i64>, kc: Seq<u32>, kb: Seq<i64>, bs: int, n: int, k: int)
    requires
        ms.len() == k, fl.len() == k, k >= 1, cw >= 1, n >= 0, nw == n / 16 + 1, k * cw >= nw,
        forall|x: int| 0 <= x < k ==> (#[trigger] ms[x])@.len() == (if x * cw < nw { cw } else { 0 }),
        forall|x: int| 0 <= x < k ==> words_ok((#[trigger] ms[x])@, x * cw, qkey, codes, bases, bs, n),
        forall|x: int| 0 <= x < k ==> #[trigger] fl[x] == dense_on(kc, kb, bs, 16 * (x * cw),
            rmin(16 * (x * cw + (if x * cw < nw { cw } else { 0 })), n)),
    ensures
        cmap_ok(ms, cw, qkey, codes, bases, bs, n),
        (forall|x: int| 0 <= x < k ==> #[trigger] fl[x]) == dense_on(kc, kb, bs, 0, n),
{
    assert forall|c: int| 0 <= c < n implies #[trigger] cmap_has(ms, cw, c)
        && cmap_val(ms, cw, c) == qvl(qkey, fv8(codes, bases, bs, c)) by {
        let w = c / 16;
        let t = w / cw;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(w, cw);
        vstd::arithmetic::div_mod::lemma_mod_bound(w, cw);
        assert(w < nw);
        assert(cw * t == t * cw) by (nonlinear_arith);
        assert(w >= t * cw);
        assert(t < k) by {
            if t >= k {
                assert(t * cw >= k * cw) by (nonlinear_arith) requires t >= k, cw >= 1;
            }
        }
        assert(t * cw < nw);
        assert(ms[t]@.len() == cw);
        assert(words_ok(ms[t]@, t * cw, qkey, codes, bases, bs, n));
        assert(w - t * cw == w % cw);
        assert(16 * (t * cw) <= c < 16 * (t * cw + cw));
    }
    assert forall|c: int| 0 <= c < n implies #[trigger] cmap_val(ms, cw, c) == qvl(qkey, fv8(codes, bases, bs, c)) by {
        assert(cmap_has(ms, cw, c));
    }
    // the dense flags
    let lo = |x: int| 16 * (x * cw);
    let hi = |x: int| rmin(16 * (x * cw + (if x * cw < nw { cw } else { 0 })), n);
    if forall|x: int| 0 <= x < k ==> #[trigger] fl[x] {
        assert forall|c: int| 0 <= c < n implies #[trigger] fv32(kc, kb, bs, c) == c + 1 by {
            let w = c / 16;
            let t = w / cw;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(w, cw);
            vstd::arithmetic::div_mod::lemma_mod_bound(w, cw);
            assert(w < nw);
            assert(cw * t == t * cw) by (nonlinear_arith);
            assert(t < k) by {
                if t >= k {
                    assert(t * cw >= k * cw) by (nonlinear_arith) requires t >= k, cw >= 1;
                }
            }
            assert(fl[t]);
            assert(16 * (t * cw) <= c < 16 * (t * cw + cw));
            assert(lo(t) <= c < hi(t));
        }
    }
    if dense_on(kc, kb, bs, 0, n) {
        assert forall|x: int| 0 <= x < k implies #[trigger] fl[x] by {
            assert forall|c: int| lo(x) <= c < hi(x) implies #[trigger] fv32(kc, kb, bs, c) == c + 1 by {
                assert(0 <= x * cw) by (nonlinear_arith) requires 0 <= x, cw >= 1;
            }
        }
    }
}

/// The map value of customer row `c`.
pub fn cmap_get(ms: &Vec<Vec<u64>>, cd: Div, c: usize) -> (v: u64)
    requires cd.ok(), cmap_has(ms@, cd.bs as int, c as int),
    ensures v == cmap_val(ms@, cd.bs as int, c as int), v < 16,
    no_unwind
{
    let w = c / 16;
    let t = div_of(cd, w);
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(w as int, cd.bs as int);
        assert(cd.bs * t == t * cd.bs) by (nonlinear_arith);
    }
    let i = w - t * cd.bs;
    let wd = ms[t][i];
    let b = (c % 16) as u64;
    proof {
        lemma_nib_small(wd, b);
        lemma_shift_ok(b);
    }
    (wd >> (b << 2u64)) & 15u64
}

/// A copy of the qualifying keys for one task.
pub fn copy_i64s(v: &Vec<i64>) -> (r: Vec<i64>)
    ensures r@ == v@,
{
    let mut r: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v@.len(), r@ == v@.subrange(0, i as int),
        decreases v@.len() - i,
    {
        r.push(v[i]);
        i = i + 1;
        proof {
            assert(r@ =~= v@.subrange(0, i as int));
        }
    }
    proof {
        assert(v@.subrange(0, v@.len() as int) =~= v@);
    }
    r
}

} // verus!
