//! The nations named `$1` (`nations_named`: their keys) and the supplier bitmap (`supplier_bits`): bit `b` is set
//! when supplier row `b` lies in such a nation (`model::supp_ok`), built by worker tasks over ranges of 64-row
//! words (`SuppTask`), which also check that the supplier keys are dense (`s_suppkey[b] == s_suppkey[0] + b`, as
//! dbgen writes them), so that a supplier key finds its row by subtraction.
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::link::query::text_at;
use crate::agent::model::*;
use crate::agent::common::bitmap::{bit_at, wbit, lemma_zero_word, lemma_aligned, lemma_set_bit};
use crate::agent::scan::bits_ok;
use crate::stores::flat_nation::interface as ni;

verus! {

// ------------------------------------------------------------------------------------------ nations

/// `x` occurs in `want`.
pub open spec fn in_want(want: Seq<i64>, x: int) -> bool {
    exists|j: int| 0 <= j < want.len() && #[trigger] want[j] as int == x
}

/// Some nation named `p` has key `x`.
pub open spec fn key_named(sv: StoresView, p: Seq<u8>, x: int) -> bool {
    exists|d: int| 0 <= d < nat_n(sv) && #[trigger] n_keys(sv)[d] as int == x && nat_ok(sv, p, d)
}

/// `want` holds exactly the keys of the nations named `p`.
pub open spec fn want_ok(sv: StoresView, p: Seq<u8>, want: Seq<i64>) -> bool {
    &&& forall|j: int| 0 <= j < want.len() ==> key_named(sv, p, #[trigger] want[j] as int)
    &&& forall|d: int| 0 <= d < nat_n(sv) && #[trigger] nat_ok(sv, p, d) ==> in_want(want, n_keys(sv)[d] as int)
}

/// A supplier lies in a nation named `p` exactly when its nation key is listed.
pub proof fn lemma_supp_ok_want(sv: StoresView, p: Seq<u8>, want: Seq<i64>, b: int)
    requires want_ok(sv, p, want),
    ensures supp_ok(sv, p, b) == in_want(want, s_nks(sv)[b] as int),
{
    if in_want(want, s_nks(sv)[b] as int) {
        let j = choose|j: int| 0 <= j < want.len() && #[trigger] want[j] as int == s_nks(sv)[b] as int;
        assert(key_named(sv, p, want[j] as int));
        let d = choose|d: int| 0 <= d < nat_n(sv) && #[trigger] n_keys(sv)[d] as int == want[j] as int && nat_ok(sv, p, d);
        assert(n_keys(sv)[d] == s_nks(sv)[b]);
    }
    if supp_ok(sv, p, b) {
        let d = choose|d: int| 0 <= d < nat_n(sv) && #[trigger] n_keys(sv)[d] == s_nks(sv)[b] && nat_ok(sv, p, d);
        assert(in_want(want, n_keys(sv)[d] as int));
    }
}

/// Whether `x` occurs in `want`.
pub fn want_has(want: &Vec<i64>, nwant: usize, x: i64) -> (r: bool)
    requires nwant == want@.len(),
    ensures r == in_want(want@, x as int),
    no_unwind
{
    let mut j: usize = 0;
    while j < nwant
        invariant nwant == want@.len(), j <= nwant, forall|i: int| 0 <= i < j ==> want@[i] != x,
        decreases nwant - j,
    {
        if want[j] == x {
            return true;
        }
        j = j + 1;
    }
    false
}

/// `mask` has bit `x` exactly for the keys `x` in `[0, 64)` listed in `want` (nation keys are small).
pub open spec fn mask_ok(mask: u64, want: Seq<i64>) -> bool {
    forall|x: int| 0 <= x < 64 ==> (#[trigger] wbit(mask, x) <==> in_want(want, x))
}

/// The bit mask of the keys in `[0, 64)` listed in `want`.
pub fn want_mask(want: &Vec<i64>, nwant: usize) -> (mask: u64)
    requires nwant == want@.len(),
    ensures mask_ok(mask, want@),
{
    let mut mask: u64 = 0;
    let mut j: usize = 0;
    proof { lemma_zero_word(); }
    while j < nwant
        invariant
            nwant == want@.len(), j <= nwant,
            forall|x: int| 0 <= x < 64 ==> (#[trigger] wbit(mask, x) <==> in_want(want@.take(j as int), x)),
        decreases nwant - j,
    {
        let k = want[j];
        let ghost m0 = mask;
        if 0 <= k && k < 64 {
            mask = mask | (1u64 << (k as u64));
            proof { lemma_set_bit(m0, k as u64); }
        }
        proof {
            let w1 = want@.take(j + 1);
            let w0 = want@.take(j as int);
            assert(w1 =~= w0.push(k));
            assert forall|x: int| 0 <= x < 64 implies (#[trigger] wbit(mask, x) <==> in_want(w1, x)) by {
                if in_want(w0, x) {
                    let i = choose|i: int| 0 <= i < w0.len() && #[trigger] w0[i] as int == x;
                    assert(w1[i] == w0[i]);
                }
                if in_want(w1, x) {
                    let i = choose|i: int| 0 <= i < w1.len() && #[trigger] w1[i] as int == x;
                    if i < w0.len() { assert(w0[i] == w1[i]); }
                }
                assert(w1[j as int] == k);
                if 0 <= k && k < 64 {
                    assert(wbit(mask, x) == (x == k as int || wbit(m0, x))) by {
                        if x != k as int {
                            assert(wbit(mask, (x as u64) as int) == wbit(m0, (x as u64) as int));
                        }
                    }
                }
            }
        }
        j = j + 1;
    }
    proof { assert(want@.take(nwant as int) =~= want@); }
    mask
}

/// Byte equality of `bytes[a..b)` with `p`.
fn bytes_eq_at(bytes: &[u8], a: usize, b: usize, p: &[u8]) -> (r: bool)
    requires a <= b <= bytes@.len(),
    ensures r == (bytes@.subrange(a as int, b as int) == p@),
{
    let n = b - a;
    if n != p.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < n
        invariant a <= b <= bytes@.len(), n == b - a, n == p@.len(), i <= n,
            forall|j: int| 0 <= j < i ==> bytes@[a + j] == p@[j],
        decreases n - i,
    {
        if bytes[a + i] != p[i] {
            proof {
                assert(bytes@.subrange(a as int, b as int)[i as int] != p@[i as int]);
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        assert(bytes@.subrange(a as int, b as int) =~= p@);
    }
    true
}

/// The keys of the nations named `p`.
pub fn nations_named(stores: &mut Stores, p: &[u8], Ghost(sv): Ghost<StoresView>) -> (want: Vec<i64>)
    requires old(stores)@ == sv, stores_wf(sv),
    ensures final(stores)@ == sv, want_ok(sv, p@, want@),
{
    let mut want: Vec<i64> = Vec::new();
    let nn = stores.flat_nation.part_len(ni::N_NATIONKEY);
    if nn == 0 {
        return want;
    }
    let nkeys = stores.flat_nation.extent_i64(ni::N_NATIONKEY, 0, nn);
    assert(nkeys@ =~= n_keys(sv));
    let (offs, bytes) = ni::text_rows(&mut stores.flat_nation, ni::N_NAME_OFFSETS, ni::N_NAME_BYTES, 0, nn, Ghost(nn as int));
    let o0 = offs[0];
    let blen = bytes.len();
    let mut d: usize = 0;
    while d < nn
        invariant
            stores@ == sv, stores_wf(sv),
            nn == nat_n(sv), nkeys@ == n_keys(sv), d <= nn,
            offs@.len() == nn + 1, o0 == offs@[0], 0 <= offs@[0],
            forall|a: int, b: int| 0 <= a <= b <= nn ==> offs@[a] <= offs@[b],
            bytes@.len() == offs@[nn as int] - offs@[0], blen == bytes@.len(),
            forall|j: int| 0 <= j < nn ==> #[trigger] bytes@.subrange(offs@[j] - offs@[0], offs@[j + 1] - offs@[0])
                == text_at(n_name_view(sv), j),
            forall|j: int| 0 <= j < want@.len() ==> key_named(sv, p@, #[trigger] want@[j] as int),
            forall|e: int| 0 <= e < d && #[trigger] nat_ok(sv, p@, e) ==> in_want(want@, n_keys(sv)[e] as int),
        decreases nn - d,
    {
        proof {
            assert(offs@[0] <= offs@[d as int] <= offs@[d + 1] <= offs@[nn as int]);
        }
        let a = (offs[d] - o0) as usize;
        let b = (offs[d + 1] - o0) as usize;
        let eq = bytes_eq_at(bytes, a, b, p);
        proof {
            assert(bytes@.subrange(offs@[d as int] - offs@[0], offs@[d + 1] - offs@[0]) == text_at(n_name_view(sv), d as int));
            assert(eq == nat_ok(sv, p@, d as int));
        }
        let ghost w0 = want@;
        if eq {
            want.push(nkeys[d]);
            proof {
                assert forall|j: int| 0 <= j < want@.len() implies key_named(sv, p@, #[trigger] want@[j] as int) by {
                    if j < w0.len() {
                        assert(want@[j] == w0[j]);
                    } else {
                        assert(n_keys(sv)[d as int] == want@[j]);
                    }
                }
                assert forall|e: int| 0 <= e < d + 1 && #[trigger] nat_ok(sv, p@, e) implies in_want(want@, n_keys(sv)[e] as int) by {
                    if e < d {
                        let j = choose|j: int| 0 <= j < w0.len() && #[trigger] w0[j] as int == n_keys(sv)[e] as int;
                        assert(want@[j] == w0[j]);
                    } else {
                        assert(want@[w0.len() as int] as int == n_keys(sv)[e] as int);
                    }
                }
            }
        }
        d = d + 1;
    }
    want
}

// ------------------------------------------------------------------------------------------ supplier words

/// Bit `t` of word `i` of a task's words is the flag of supplier row `64 * (w0 + i) + t` (rows below `ns`).
pub open spec fn words_ok(words: Seq<u64>, w0: int, ns: int, sv: StoresView, p: Seq<u8>) -> bool {
    forall|i: int, t: int| 0 <= i < words.len() && 0 <= t < 64 && 64 * (w0 + i) + t < ns
        ==> #[trigger] wbit(words[i], t) == supp_ok(sv, p, 64 * (w0 + i) + t)
}

/// Supplier rows `[r0, r1)` have the dense keys `base + b`.
pub open spec fn dense_range(sv: StoresView, base: int, r0: int, r1: int) -> bool {
    forall|b: int| r0 <= b < r1 ==> #[trigger] s_keys(sv)[b] == base + b
}

/// The word of supplier rows `[r0, r1)` (`r1 - r0 <= 64`) and whether their keys are dense.
fn supp_word(skeys: &'static [i64], snk: &'static [i64], base: i64, want: &Vec<i64>, nwant: usize, mask: u64,
    r0: usize, r1: usize, Ghost(sv): Ghost<StoresView>, Ghost(p): Ghost<Seq<u8>>) -> (r: (u64, bool))
    requires
        skeys@ == s_keys(sv), snk@ == s_nks(sv), stores_wf(sv),
        r0 <= r1 <= supp_n(sv), r1 - r0 <= 64,
        want_ok(sv, p, want@), nwant == want@.len(), mask_ok(mask, want@),
    ensures
        forall|t: int| 0 <= t < r1 - r0 ==> #[trigger] wbit(r.0, t) == supp_ok(sv, p, r0 + t),
        r.1 ==> dense_range(sv, base as int, r0 as int, r1 as int),
    no_unwind
{
    let mut w: u64 = 0;
    let mut dense = true;
    let mut r = r0;
    proof { lemma_zero_word(); }
    while r < r1
        invariant
            skeys@ == s_keys(sv), snk@ == s_nks(sv), stores_wf(sv),
            r0 <= r <= r1 <= supp_n(sv), r1 - r0 <= 64,
            want_ok(sv, p, want@), nwant == want@.len(), mask_ok(mask, want@),
            forall|t: int| 0 <= t < r - r0 ==> #[trigger] wbit(w, t) == supp_ok(sv, p, r0 + t),
            forall|t: int| r - r0 <= t < 64 ==> !#[trigger] wbit(w, t),
            dense ==> dense_range(sv, base as int, r0 as int, r as int),
        decreases r1 - r,
    {
        let nk = snk[r];
        let hit = if 0 <= nk && nk < 64 { (mask >> (nk as u64)) & 1u64 == 1u64 } else { want_has(want, nwant, nk) };
        proof {
            lemma_supp_ok_want(sv, p, want@, r as int);
            if 0 <= nk && nk < 64 {
                assert(wbit(mask, (nk as u64) as int) <==> in_want(want@, nk as int));
            }
        }
        let x: u64 = if hit { 1 } else { 0 };
        let b: u64 = (r - r0) as u64;
        let ghost w0 = w;
        w = w | (x << b);
        proof {
            assert((((w0 | (x << b)) >> b) & 1u64 == 1u64) == (x == 1u64 || (w0 >> b) & 1u64 == 1u64)) by (bit_vector)
                requires b < 64, x <= 1;
            assert forall|c: u64| c < 64 && c != b implies wbit(w, c as int) == #[trigger] wbit(w0, c as int) by {
                assert((((w0 | (x << b)) >> c) & 1u64 == 1u64) == ((w0 >> c) & 1u64 == 1u64)) by (bit_vector)
                    requires b < 64, c < 64, c != b, x <= 1;
            }
            assert forall|t: int| 0 <= t < r + 1 - r0 implies #[trigger] wbit(w, t) == supp_ok(sv, p, r0 + t) by {
                let c = t as u64;
                if t < r - r0 {
                    assert(wbit(w, c as int) == wbit(w0, c as int));
                } else {
                    assert(c == b);
                    assert(wbit(w, t) == (x == 1u64 || wbit(w0, t)));
                    assert(!wbit(w0, t));
                }
            }
            assert forall|t: int| r + 1 - r0 <= t < 64 implies !#[trigger] wbit(w, t) by {
                let c = t as u64;
                assert(wbit(w, c as int) == wbit(w0, c as int));
            }
        }
        if skeys[r] as i128 != base as i128 + r as i128 {
            dense = false;
        }
        r = r + 1;
    }
    (w, dense)
}

/// The supplier words `[w0, w1)`.
pub struct SuppTask {
    pub skeys: &'static [i64],
    pub snk: &'static [i64],
    pub ns: usize,
    pub w0: usize,
    pub w1: usize,
    pub base: i64,
    pub want: Arc<Vec<i64>>,
    pub nwant: usize,
    pub mask: u64,
    pub words: Vec<u64>,
    pub sv: Ghost<StoresView>,
    pub p: Ghost<Seq<u8>>,
}

/// The task's words and whether its suppliers have dense keys.
pub struct SuppOut {
    pub words: Vec<u64>,
    pub dense: bool,
}

/// The supplier rows of words `[w0, w1)`.
pub open spec fn rows_of(w0: int, w1: int, ns: int) -> (int, int) {
    (64 * w0, if 64 * w1 < ns { 64 * w1 } else { ns })
}

impl WorkerTask for SuppTask {
    type Output = SuppOut;

    open spec fn pre(&self) -> bool {
        let sv = self.sv@;
        &&& stores_wf(sv)
        &&& self.skeys@ == s_keys(sv) && self.snk@ == s_nks(sv) && self.ns == supp_n(sv)
        &&& self.w0 <= self.w1 && 64 * self.w1 < self.ns + 64
        &&& want_ok(sv, self.p@, (*self.want)@) && self.nwant == (*self.want)@.len() && mask_ok(self.mask, (*self.want)@)
        &&& self.words@.len() == self.w1 - self.w0
    }

    open spec fn post(&self, out: SuppOut) -> bool {
        &&& out.words@.len() == self.w1 - self.w0
        &&& words_ok(out.words@, self.w0 as int, self.ns as int, self.sv@, self.p@)
        &&& out.dense ==> dense_range(self.sv@, self.base as int, rows_of(self.w0 as int, self.w1 as int, self.ns as int).0,
            rows_of(self.w0 as int, self.w1 as int, self.ns as int).1)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.w0 as u64, self.w1 as u64)
    }

    fn run(self) -> (out: SuppOut) {
        let ghost task = self;
        let SuppTask { skeys, snk, ns, w0, w1, base, want, nwant, mask, words, sv, p } = self;
        let ghost sv = sv@;
        let ghost p = p@;
        let wv: &Vec<i64> = &*want;
        let mut words = words;
        let mut dense = true;
        let mut w = w0;
        while w < w1
            invariant
                stores_wf(sv), skeys@ == s_keys(sv), snk@ == s_nks(sv), ns == supp_n(sv),
                w0 <= w <= w1, 64 * w1 < ns + 64,
                want_ok(sv, p, wv@), nwant == wv@.len(), mask_ok(mask, wv@),
                words@.len() == w1 - w0,
                words_ok(words@.subrange(0, w - w0), w0 as int, ns as int, sv, p),
                dense ==> dense_range(sv, base as int, 64 * w0, if 64 * w < ns { 64 * w } else { ns as int }),
                task.sv@ == sv && task.p@ == p && task.w0 == w0 && task.w1 == w1 && task.ns == ns && task.base == base && task == self,
            decreases w1 - w,
        {
            let r0 = w * 64;
            let r1 = if ns - r0 > 64 { r0 + 64 } else { ns };
            let (word, d) = supp_word(skeys, snk, base, wv, nwant, mask, r0, r1, Ghost(sv), Ghost(p));
            let ghost before = words@;
            words[w - w0] = word;
            proof {
                let i = w - w0;
                assert forall|ii: int, t: int| 0 <= ii < i + 1 && 0 <= t < 64 && 64 * (w0 + ii) + t < ns
                    implies #[trigger] wbit(words@.subrange(0, i + 1)[ii], t) == supp_ok(sv, p, 64 * (w0 + ii) + t) by {
                    if ii < i {
                        assert(words@.subrange(0, i + 1)[ii] == before.subrange(0, i as int)[ii]);
                    } else {
                        assert(words@.subrange(0, i + 1)[ii] == word);
                        assert(64 * (w0 + ii) + t == r0 + t);
                    }
                }
            }
            if !d {
                dense = false;
            }
            w = w + 1;
        }
        proof {
            assert(words@.subrange(0, w1 - w0) =~= words@);
        }
        SuppOut { words, dense }
    }
}

/// The supplier bitmap and whether the supplier keys are dense, built by at most `tasks` worker tasks (on the
/// calling thread with one task).
pub fn supplier_bits(skeys: &'static [i64], snk: &'static [i64], ns: usize, base: i64, want: Vec<i64>, tasks: usize,
    dispatch: &mut Dispatch, Ghost(sv): Ghost<StoresView>, Ghost(p): Ghost<Seq<u8>>) -> (r: Result<(Vec<u64>, bool), WorkerFailure>)
    requires
        stores_wf(sv), skeys@ == s_keys(sv), snk@ == s_nks(sv), ns == supp_n(sv),
        want_ok(sv, p, want@), 1 <= tasks <= MAX_WORKERS,
    ensures
        r matches Ok((bits, dense)) ==> bits_ok(bits@, ns as int, sv, p)
            && (dense ==> dense_range(sv, base as int, 0, ns as int)),
{
    let nwant = want.len();
    let mask = want_mask(&want, nwant);
    let want = Arc::new(want);
    let nw = if ns % 64 == 0 { ns / 64 } else { ns / 64 + 1 };
    let per = nw / tasks + 1;
    let mut ts: Vec<SuppTask> = Vec::new();
    let mut w0: usize = 0;
    let mut t: usize = 0;
    let ghost mut bounds: Seq<(int, int)> = Seq::empty();
    while t < tasks
        invariant
            stores_wf(sv), skeys@ == s_keys(sv), snk@ == s_nks(sv), ns == supp_n(sv),
            want_ok(sv, p, (*want)@), nwant == (*want)@.len(), mask_ok(mask, (*want)@),
            1 <= tasks <= MAX_WORKERS, t <= tasks,
            64 * nw >= ns, 64 * nw < ns + 64,
            w0 <= nw,
            ts@.len() == t, bounds.len() == t,
            forall|i: int| 0 <= i < t ==> (#[trigger] ts@[i]).pre() && ts@[i].w0 == bounds[i].0 && ts@[i].w1 == bounds[i].1
                && ts@[i].sv@ == sv && ts@[i].p@ == p && ts@[i].ns == ns && ts@[i].base == base,
            forall|i: int| 0 < i < t ==> #[trigger] bounds[i].0 == bounds[i - 1].1,
            t == 0 ==> w0 == 0,
            t > 0 ==> bounds[0].0 == 0 && bounds[t - 1].1 == w0,
            t == tasks ==> w0 == nw,
        decreases tasks - t,
    {
        let w1 = if t + 1 == tasks { nw } else if nw - w0 > per { w0 + per } else { nw };
        let task = SuppTask { skeys, snk, ns, w0, w1, base, want: want.clone(), nwant, mask, words: vec![0u64; w1 - w0],
            sv: Ghost(sv), p: Ghost(p) };
        let ghost ts0 = ts@;
        let ghost b0 = bounds;
        ts.push(task);
        proof {
            bounds = bounds.push((w0 as int, w1 as int));
            assert forall|i: int| 0 <= i < t + 1 implies (#[trigger] ts@[i]).pre() && ts@[i].w0 == bounds[i].0 && ts@[i].w1 == bounds[i].1
                && ts@[i].sv@ == sv && ts@[i].p@ == p && ts@[i].ns == ns && ts@[i].base == base by {
                if i < t { assert(ts@[i] == ts0[i] && bounds[i] == b0[i]); }
            }
            assert forall|i: int| 0 < i < t + 1 implies #[trigger] bounds[i].0 == bounds[i - 1].1 by {
                if i < t { assert(bounds[i] == b0[i] && bounds[i - 1] == b0[i - 1]); }
            }
        }
        w0 = w1;
        t = t + 1;
    }
    let ghost tg = ts@;
    let outs = if tasks == 1 {
        let mut ts = ts;
        let only = ts.pop().unwrap();
        assert(only == tg[0]);
        let o = only.run();
        let mut v: Vec<SuppOut> = Vec::new();
        v.push(o);
        v
    } else {
        match fork_join(dispatch, ts) {
            Ok(o) => o,
            Err(e) => return Err(e),
        }
    };
    // concatenate the words in task order
    let mut bits: Vec<u64> = Vec::with_capacity(nw);
    let mut dense = true;
    let mut i: usize = 0;
    while i < tasks
        invariant
            stores_wf(sv), ns == supp_n(sv), 64 * nw >= ns, 64 * nw < ns + 64,
            outs@.len() == tasks, tg.len() == tasks, bounds.len() == tasks, i <= tasks,
            forall|j: int| 0 <= j < tasks ==> (#[trigger] tg[j]).post(outs@[j]),
            forall|j: int| 0 <= j < tasks ==> (#[trigger] tg[j]).w0 == bounds[j].0 && tg[j].w1 == bounds[j].1
                && tg[j].sv@ == sv && tg[j].p@ == p && tg[j].ns == ns && tg[j].base == base,
            forall|j: int| 0 < j < tasks ==> #[trigger] bounds[j].0 == bounds[j - 1].1,
            bounds[0].0 == 0, bounds[tasks - 1].1 == nw,
            bits@.len() == if i == 0 { 0 } else { bounds[i - 1].1 },
            forall|b: int| 0 <= b < 64 * bits@.len() && b < ns ==> #[trigger] bit_at(bits@, b) == supp_ok(sv, p, b),
            dense ==> dense_range(sv, base as int, 0, if 64 * bits@.len() < ns { 64 * bits@.len() as int } else { ns as int }),
        decreases tasks - i,
    {
        let o = &outs[i];
        let n_i = o.words.len();
        let ghost wbase: int = bits@.len() as int;
        let ghost task = tg[i as int];
        proof {
            assert(task.post(outs@[i as int]));
            if i > 0 { assert(bounds[i as int].0 == bounds[i - 1].1); }
            assert(task.w0 == wbase);
        }
        let mut j: usize = 0;
        while j < n_i
            invariant
                n_i == o.words@.len(), j <= n_i, ns == supp_n(sv),
                bits@.len() == wbase + j,
                words_ok(o.words@, wbase, ns as int, sv, p),
                forall|b: int| 0 <= b < 64 * wbase && b < ns ==> #[trigger] bit_at(bits@, b) == supp_ok(sv, p, b),
                forall|k: int| 0 <= k < j ==> #[trigger] bits@[wbase + k] == o.words@[k],
            decreases n_i - j,
        {
            let ghost b0 = bits@;
            bits.push(o.words[j]);
            proof {
                assert forall|b: int| 0 <= b < 64 * wbase && b < ns implies #[trigger] bit_at(bits@, b) == supp_ok(sv, p, b) by {
                    lemma_aligned(0, b);
                    assert(b / 64 < wbase) by { vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b, 64); }
                    assert(bits@[b / 64] == b0[b / 64]);
                    assert(bit_at(b0, b) == supp_ok(sv, p, b));
                }
                assert forall|k: int| 0 <= k < j + 1 implies #[trigger] bits@[wbase + k] == o.words@[k] by {
                    if k < j { assert(bits@[wbase + k] == b0[wbase + k]); }
                }
            }
            j = j + 1;
        }
        proof {
            let we = wbase + n_i;
            assert forall|b: int| 0 <= b < 64 * we && b < ns implies #[trigger] bit_at(bits@, b) == supp_ok(sv, p, b) by {
                if b >= 64 * wbase {
                    let ii = b / 64 - wbase;
                    let tt = b % 64;
                    lemma_aligned(0, b);
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b, 64);
                    assert(b == 64 * (b / 64) + b % 64);
                    assert(0 <= ii < n_i) by (nonlinear_arith) requires 64 * wbase <= b < 64 * (wbase + n_i), b == 64 * (b / 64) + b % 64, 0 <= b % 64 < 64, ii == b / 64 - wbase;
                    assert(bits@[wbase + ii] == o.words@[ii]);
                    assert(b / 64 == wbase + ii);
                    assert(64 * (wbase + ii) + tt == b);
                    assert(wbit(o.words@[ii], tt) == supp_ok(sv, p, 64 * (wbase + ii) + tt));
                }
            }
        }
        if !o.dense {
            dense = false;
        }
        proof {
            if dense {
                let (r0, r1) = rows_of(task.w0 as int, task.w1 as int, ns as int);
                assert(dense_range(sv, base as int, r0, r1));
            }
        }
        i = i + 1;
    }
    proof {
        assert(bits@.len() == nw);
    }
    Ok((bits, dense))
}

} // verus!
