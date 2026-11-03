//! Phase 1 (parallel): the nation slot of every customer and every supplier (`ccode[i] == nslot(c_nk[i])`,
//! `scode[d] == nslot(s_nk[d])`), and whether the customer and supplier key columns are dense (`keys[i] ==
//! keys[0] + i`, which makes a key lookup a subtraction). Each task covers one customer range and one supplier
//! range and returns its codes; the calling thread concatenates them (with a single task, its buffer of at least
//! `MIN_MAP` bytes, zeroed lazily by the kernel, becomes the column without a copy). With the customer codes comes a bitmap of
//! the customers with a code (`bits`, bit `i` set iff `ccode[i] != NONE`): customer ranges start at multiples of
//! 64, so the task bitmaps concatenate.
use vstd::prelude::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::gendb_entry::work::put;
use crate::agent::model::*;
use crate::agent::contrib::*;
use crate::agent::cols::*;
use crate::agent::common::key_lookup::find_key;
use crate::agent::common::lookup::*;
use crate::agent::common::bitmap::*;
use crate::agent::qkeys::MIN_MAP;

verus! {

/// The slot of nation key `k`.
pub fn slot_of_key(c: &Cols, slots: &Vec<u8>, k: i64, Ghost(sv): Ghost<StoresView>) -> (r: u8)
    requires cols_ok(*c, sv), keys_ok(sv), slots@.len() == nn(sv),
    ensures r == nslot(sv, slots@, k),
    no_unwind
{
    match find_key(c.nkeys, c.nn, k) {
        Some(e) => {
            proof {
                let e2 = choose|e2: int| 0 <= e2 < nn(sv) && #[trigger] n_nk(sv)[e2] == k;
                assert(n_nk(sv)[e2] == n_nk(sv)[e as int]);
            }
            slots[e]
        },
        None => NONE,
    }
}

/// Nation keys with a direct entry in the key table (`ktab`).
pub const KT: usize = 256;

/// `ktab[k]` is the slot of nation key `k` for every `k < KT`.
pub open spec fn ktab_ok(sv: StoresView, slots: Seq<u8>, ktab: Seq<u8>) -> bool {
    &&& ktab.len() == KT
    &&& forall|k: int| 0 <= k < KT ==> #[trigger] ktab[k] == nslot(sv, slots, k as i64)
}

/// The slot of nation key `k`: from the key table when `0 <= k < KT`, else by search.
fn slot_fast(c: &Cols, slots: &Vec<u8>, ktab: &Vec<u8>, k: i64, Ghost(sv): Ghost<StoresView>) -> (r: u8)
    requires cols_ok(*c, sv), keys_ok(sv), slots@.len() == nn(sv), ktab_ok(sv, slots@, ktab@),
    ensures r == nslot(sv, slots@, k),
    no_unwind
{
    if 0 <= k && k < KT as i64 {
        proof { assert(ktab@[k as usize as int] == nslot(sv, slots@, (k as usize) as i64)); }
        ktab[k as usize]
    } else {
        slot_of_key(c, slots, k, Ghost(sv))
    }
}

/// The key table of the nation slots.
fn key_table(c: &Cols, slots: &Vec<u8>, Ghost(sv): Ghost<StoresView>) -> (ktab: Vec<u8>)
    requires cols_ok(*c, sv), keys_ok(sv), slots@.len() == nn(sv),
    ensures ktab_ok(sv, slots@, ktab@),
{
    let mut ktab: Vec<u8> = Vec::new();
    let mut k: usize = 0;
    while k < KT
        invariant
            cols_ok(*c, sv), keys_ok(sv), slots@.len() == nn(sv), k <= KT, ktab@.len() == k,
            forall|q: int| 0 <= q < k ==> #[trigger] ktab@[q] == nslot(sv, slots@, q as i64),
        decreases KT - k,
    {
        let code = slot_of_key(c, slots, k as i64, Ghost(sv));
        ktab.push(code);
        k = k + 1;
    }
    ktab
}

/// One range of customers and one range of suppliers.
pub struct CodeTask {
    pub c: Cols,
    pub slots: Vec<u8>,
    pub ktab: Vec<u8>,
    pub clo: usize,
    pub chi: usize,
    pub slo: usize,
    pub shi: usize,
    pub ccode: Vec<u8>,
    pub scode: Vec<u8>,
    pub bits: Vec<u64>,
    pub sv: Ghost<StoresView>,
}

pub struct CodeOut {
    pub cdense: bool,
    pub sdense: bool,
    pub ccode: Vec<u8>,
    pub scode: Vec<u8>,
    pub bits: Vec<u64>,
}

/// The codes of the customers `[clo, chi)` and the suppliers `[slo, shi)`, and their key density.
pub open spec fn code_post(sv: StoresView, slots: Seq<u8>, clo: int, chi: int, slo: int, shi: int, out: CodeOut) -> bool {
    &&& out.ccode@.len() >= chi - clo
    &&& out.scode@.len() == shi - slo
    &&& forall|i: int| 0 <= i < chi - clo ==> #[trigger] out.ccode@[i] == nslot(sv, slots, c_nk(sv)[clo + i])
    &&& forall|i: int| 0 <= i < shi - slo ==> #[trigger] out.scode@[i] == nslot(sv, slots, s_nk(sv)[slo + i])
    &&& out.cdense ==> forall|i: int| clo <= i < chi ==> #[trigger] c_ck(sv)[i] as int == c_ck(sv)[0] as int + i
    &&& out.sdense ==> forall|i: int| slo <= i < shi ==> #[trigger] s_sk(sv)[i] as int == s_sk(sv)[0] as int + i
    &&& 64 * out.bits@.len() >= chi - clo
    &&& 64 * out.bits@.len() < chi - clo + 64
    &&& forall|i: int| 0 <= i < chi - clo ==> #[trigger] bit_at(out.bits@, i) == (out.ccode@[i] != NONE)
}

impl WorkerTask for CodeTask {
    type Output = CodeOut;

    open spec fn pre(&self) -> bool {
        &&& cols_ok(self.c, self.sv@)
        &&& keys_ok(self.sv@)
        &&& self.slots@.len() == nn(self.sv@)
        &&& ktab_ok(self.sv@, self.slots@, self.ktab@)
        &&& self.clo <= self.chi <= self.c.nc
        &&& self.slo <= self.shi <= self.c.ns
        &&& self.ccode@.len() >= self.chi - self.clo
        &&& self.scode@.len() == self.shi - self.slo
        &&& 64 * self.bits@.len() >= self.chi - self.clo
        &&& 64 * self.bits@.len() < self.chi - self.clo + 64
    }

    open spec fn post(&self, out: CodeOut) -> bool {
        code_post(self.sv@, self.slots@, self.clo as int, self.chi as int, self.slo as int, self.shi as int, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.clo as u64, self.chi as u64)
    }

    fn run(self) -> (out: CodeOut) {
        let CodeTask { c, slots, ktab, clo, chi, slo, shi, ccode, scode, bits, sv } = self;
        let mut ccode = ccode;
        let mut bits = bits;
        let mut scode = scode;
        let ghost svv = sv@;
        let mut i = clo;
        while i < chi
            invariant
                cols_ok(c, svv), keys_ok(svv), slots@.len() == nn(svv), ktab_ok(svv, slots@, ktab@), clo <= i <= chi <= c.nc,
                ccode@.len() >= chi - clo,
                forall|x: int| 0 <= x < i - clo ==> #[trigger] ccode@[x] == nslot(svv, slots@, c_nk(svv)[clo + x]),
            decreases chi - i,
        {
            let code = slot_fast(&c, &slots, &ktab, c.cnk[i], Ghost(svv));
            put(&mut ccode, i - clo, code);
            i = i + 1;
        }
        fill_bits(&ccode, chi - clo, NONE, &mut bits);
        let mut d = slo;
        while d < shi
            invariant
                cols_ok(c, svv), keys_ok(svv), slots@.len() == nn(svv), ktab_ok(svv, slots@, ktab@), slo <= d <= shi <= c.ns,
                scode@.len() == shi - slo,
                forall|x: int| 0 <= x < d - slo ==> #[trigger] scode@[x] == nslot(svv, slots@, s_nk(svv)[slo + x]),
            decreases shi - d,
        {
            let code = slot_fast(&c, &slots, &ktab, c.snk[d], Ghost(svv));
            put(&mut scode, d - slo, code);
            d = d + 1;
        }
        let cdense = if c.nc > 0 { dense_range(c.ckeys, c.ckeys[0], clo, chi) } else { true };
        let sdense = if c.ns > 0 { dense_range(c.skeys, c.skeys[0], slo, shi) } else { true };
        CodeOut { cdense, sdense, ccode, scode, bits }
    }
}

/// The codes of all customers and suppliers, and whether their key columns are dense.
pub struct Codes {
    pub ccode: Vec<u8>,
    pub scode: Vec<u8>,
    pub bits: Vec<u64>,
    pub cdense: bool,
    pub sdense: bool,
}

pub open spec fn codes_ok(sv: StoresView, slots: Seq<u8>, k: Codes) -> bool {
    &&& k.ccode@.len() == nc(sv)
    &&& k.scode@.len() == ns(sv)
    &&& forall|i: int| 0 <= i < nc(sv) ==> #[trigger] k.ccode@[i] == nslot(sv, slots, c_nk(sv)[i])
    &&& forall|d: int| 0 <= d < ns(sv) ==> #[trigger] k.scode@[d] == nslot(sv, slots, s_nk(sv)[d])
    &&& k.cdense ==> is_dense(c_ck(sv))
    &&& k.sdense ==> is_dense(s_sk(sv))
    &&& 64 * k.bits@.len() >= nc(sv)
    &&& forall|i: int| 0 <= i < nc(sv) ==> #[trigger] bit_at(k.bits@, i) == (k.ccode@[i] != NONE)
}

/// Chunk bounds of task `t` of `nt` over `n` rows (`t * (n / nt)`; the last task takes the rest).
pub open spec fn chunk_lo(t: int, n: int, nt: int) -> int { t * (n / nt) }
pub open spec fn chunk_hi(t: int, n: int, nt: int) -> int { if t + 1 == nt { n } else { (t + 1) * (n / nt) } }

pub proof fn lemma_chunk(t: int, n: int, nt: int)
    requires 0 <= t < nt, 1 <= nt, 0 <= n,
    ensures 0 <= chunk_lo(t, n, nt) <= chunk_hi(t, n, nt) <= n, t + 1 < nt ==> chunk_hi(t, n, nt) == chunk_lo(t + 1, n, nt),
{
    let ch = n / nt;
    assert(nt * ch <= n) by (nonlinear_arith) requires ch == n / nt, nt >= 1, n >= 0;
    assert(0 <= ch) by (nonlinear_arith) requires ch == n / nt, nt >= 1, n >= 0;
    assert(t * ch <= (t + 1) * ch) by (nonlinear_arith) requires ch >= 0, t >= 0;
    assert((t + 1) * ch <= nt * ch) by (nonlinear_arith) requires ch >= 0, t + 1 <= nt;
    assert(0 <= t * ch) by (nonlinear_arith) requires ch >= 0, t >= 0;
    assert(chunk_lo(t, n, nt) == t * ch);
    assert(t + 1 < nt ==> chunk_hi(t, n, nt) == (t + 1) * ch);
}

/// Chunk bounds of task `t` of `nt` with chunk size `ch` (`nt * ch <= n`; the last task takes the rest).
pub open spec fn part_lo(t: int, ch: int) -> int { t * ch }
pub open spec fn part_hi(t: int, n: int, nt: int, ch: int) -> int { if t + 1 == nt { n } else { (t + 1) * ch } }

pub proof fn lemma_part(t: int, n: int, nt: int, ch: int)
    requires 0 <= t < nt, 1 <= nt, 0 <= ch, nt * ch <= n,
    ensures 0 <= part_lo(t, ch) <= part_hi(t, n, nt, ch) <= n, t + 1 < nt ==> part_hi(t, n, nt, ch) == part_lo(t + 1, ch),
        t + 1 < nt ==> part_hi(t, n, nt, ch) - part_lo(t, ch) == ch,
{
    assert(t * ch <= (t + 1) * ch) by (nonlinear_arith) requires ch >= 0, t >= 0;
    assert((t + 1) * ch <= nt * ch) by (nonlinear_arith) requires ch >= 0, t + 1 <= nt;
    assert(0 <= t * ch) by (nonlinear_arith) requires ch >= 0, t >= 0;
    assert((t + 1) * ch == t * ch + ch) by (nonlinear_arith);
}

/// The rows covered by the first `u` parts.
pub open spec fn pcover(u: int, n: int, nt: int, ch: int) -> int { if u == 0 { 0 } else { part_hi(u - 1, n, nt, ch) } }

pub proof fn lemma_pcover(u: int, n: int, nt: int, ch: int)
    requires 0 <= u <= nt, 1 <= nt, 0 <= ch, nt * ch <= n,
    ensures u < nt ==> pcover(u, n, nt, ch) == part_lo(u, ch), u == nt ==> pcover(u, n, nt, ch) == n,
        u < nt ==> pcover(u + 1, n, nt, ch) == part_hi(u, n, nt, ch),
{
    if u > 0 {
        lemma_part(u - 1, n, nt, ch);
    }
    assert(part_lo(0, ch) == 0);
}

/// The rows covered by the first `u` chunks.
pub open spec fn cover(u: int, n: int, nt: int) -> int { if u == 0 { 0 } else { chunk_hi(u - 1, n, nt) } }

pub proof fn lemma_cover(u: int, n: int, nt: int)
    requires 0 <= u <= nt, 1 <= nt, 0 <= n,
    ensures u < nt ==> cover(u, n, nt) == chunk_lo(u, n, nt), u == nt ==> cover(u, n, nt) == n,
        u < nt ==> cover(u + 1, n, nt) == chunk_hi(u, n, nt),
{
    if u > 0 {
        lemma_chunk(u - 1, n, nt);
    }
    assert(chunk_lo(0, n, nt) == 0);
}

/// Computes the codes in parallel (`nt` tasks; the customer chunks are multiples of 64 rows).
pub fn build_codes(c: &Cols, slots: &Vec<u8>, nt: usize, dispatch: &mut Dispatch, Ghost(sv): Ghost<StoresView>)
    -> (r: Result<Codes, WorkerFailure>)
    requires cols_ok(*c, sv), keys_ok(sv), slots@.len() == nn(sv), 1 <= nt <= MAX_WORKERS,
    ensures r matches Ok(k) ==> codes_ok(sv, slots@, k),
{
    let ncu = c.nc;
    let nsu = c.ns;
    let cw = ncu / nt / 64;
    proof {
        let q = ncu as int / nt as int;
        assert(64 * (q / 64) <= q) by (nonlinear_arith) requires q >= 0;
        assert(q <= ncu) by (nonlinear_arith) requires q == ncu as int / nt as int, nt >= 1, ncu >= 0;
    }
    let cch = 64 * cw;
    let sch = nsu / nt;
    proof {
        let q = ncu as int / nt as int;
        assert(nt * q <= ncu) by (nonlinear_arith) requires q == ncu as int / nt as int, nt >= 1, ncu >= 0;
        assert(64 * (q / 64) <= q) by (nonlinear_arith) requires q >= 0;
        assert(nt * cch <= nt * q) by (nonlinear_arith) requires cch <= q, nt >= 1;
        assert(nt * sch <= nsu) by (nonlinear_arith) requires sch == nsu as int / nt as int, nt >= 1, nsu >= 0;
    }
    let ktab = key_table(c, slots, Ghost(sv));
    let mut tasks: Vec<CodeTask> = Vec::new();
    let mut t: usize = 0;
    while t < nt
        invariant
            cols_ok(*c, sv), keys_ok(sv), slots@.len() == nn(sv), 1 <= nt <= MAX_WORKERS, t <= nt,
            ktab_ok(sv, slots@, ktab@),
            ncu == c.nc, nsu == c.ns, cch == 64 * cw, nt * cch <= ncu, nt * sch <= nsu,
            tasks@.len() == t,
            forall|u: int| 0 <= u < t ==> (#[trigger] tasks@[u]).pre()
                && tasks@[u].sv@ == sv && tasks@[u].slots@ == slots@
                && tasks@[u].clo == part_lo(u, cch as int) && tasks@[u].chi == part_hi(u, ncu as int, nt as int, cch as int)
                && tasks@[u].slo == part_lo(u, sch as int) && tasks@[u].shi == part_hi(u, nsu as int, nt as int, sch as int),
        decreases nt - t,
    {
        proof {
            lemma_part(t as int, ncu as int, nt as int, cch as int);
            lemma_part(t as int, nsu as int, nt as int, sch as int);
        }
        let clo = t * cch;
        let chi = if t + 1 == nt { ncu } else { (t + 1) * cch };
        let slo = t * sch;
        let shi = if t + 1 == nt { nsu } else { (t + 1) * sch };
        let len = chi - clo;
        let nw = len / 64 + if len % 64 == 0 { 0usize } else { 1usize };
        proof { vstd::arithmetic::div_mod::lemma_fundamental_div_mod(len as int, 64); }
        let task = CodeTask {
            c: copy_cols(c), slots: slots.clone(), ktab: ktab.clone(), clo, chi, slo, shi,
            ccode: vec![0u8; if nt == 1 && len < MIN_MAP { MIN_MAP } else { len }], scode: vec![0u8; shi - slo], bits: vec![0u64; nw], sv: Ghost(sv),
        };
        tasks.push(task);
        t = t + 1;
    }
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    let mut ccode: Vec<u8> = if nt == 1 { Vec::new() } else { Vec::with_capacity(ncu) };
    let mut scode: Vec<u8> = Vec::with_capacity(nsu);
    let mut bits: Vec<u64> = Vec::with_capacity(ncu / 64 + 1);
    let mut cdense = true;
    let mut sdense = true;
    let mut outs = outs;
    let ghost all = outs@;
    let mut u: usize = 0;
    while u < nt
        invariant
            cols_ok(*c, sv), keys_ok(sv), slots@.len() == nn(sv), 1 <= nt, u <= nt,
            ncu == c.nc, nsu == c.ns, cch == 64 * cw, nt * cch <= ncu, nt * sch <= nsu,
            all.len() == nt, tv.len() == nt,
            outs@ == all.subrange(u as int, nt as int),
            forall|w: int| 0 <= w < nt ==> #[trigger] tv[w].post(all[w]),
            forall|w: int| 0 <= w < nt ==> (#[trigger] tv[w]).clo == part_lo(w, cch as int)
                && tv[w].chi == part_hi(w, ncu as int, nt as int, cch as int)
                && tv[w].slo == part_lo(w, sch as int) && tv[w].shi == part_hi(w, nsu as int, nt as int, sch as int)
                && tv[w].sv@ == sv && tv[w].slots@ == slots@,
            ccode@.len() == pcover(u as int, ncu as int, nt as int, cch as int),
            scode@.len() == pcover(u as int, nsu as int, nt as int, sch as int),
            ccode@.len() <= ncu, scode@.len() <= nsu,
            u < nt ==> 64 * bits@.len() == ccode@.len(),
            64 * bits@.len() >= ccode@.len(),
            forall|i: int| 0 <= i < ccode@.len() ==> #[trigger] ccode@[i] == nslot(sv, slots@, c_nk(sv)[i]),
            forall|d: int| 0 <= d < scode@.len() ==> #[trigger] scode@[d] == nslot(sv, slots@, s_nk(sv)[d]),
            forall|i: int| 0 <= i < ccode@.len() ==> #[trigger] bit_at(bits@, i) == (ccode@[i] != NONE),
            cdense ==> forall|i: int| 0 <= i < ccode@.len() ==> #[trigger] c_ck(sv)[i] as int == c_ck(sv)[0] as int + i,
            sdense ==> forall|i: int| 0 <= i < scode@.len() ==> #[trigger] s_sk(sv)[i] as int == s_sk(sv)[0] as int + i,
        decreases nt - u,
    {
        proof {
            lemma_part(u as int, ncu as int, nt as int, cch as int);
            lemma_part(u as int, nsu as int, nt as int, sch as int);
            lemma_pcover(u as int, ncu as int, nt as int, cch as int);
            lemma_pcover(u as int, nsu as int, nt as int, sch as int);
            assert(tv[u as int].post(all[u as int]));
            assert(outs@[0] == all[u as int]);
        }
        let ghost (clo, slo) = (part_lo(u as int, cch as int), part_lo(u as int, sch as int));
        let ghost (c0, s0, b0) = (ccode@, scode@, bits@);
        let o = outs.remove(0);
        proof { assert(o == all[u as int]); }
        let CodeOut { cdense: od, sdense: osd, ccode: oc, scode: os, bits: ob } = o;
        let mut oc = oc;
        let mut os = os;
        let mut ob = ob;
        // With one task its buffer is at least `MIN_MAP` bytes, so the kernel zeroes it lazily in the worker, and it
        // becomes the whole column without a copy.
        let oclo = u * cch;
        let ochi = if u + 1 == nt { ncu } else { (u + 1) * cch };
        oc.truncate(ochi - oclo);
        let ghost obv = ob@;
        if !od { cdense = false; }
        if !osd { sdense = false; }
        if nt == 1 {
            proof { assert(c0 =~= Seq::<u8>::empty()); }
            ccode = oc;
        } else {
            ccode.append(&mut oc);
        }
        scode.append(&mut os);
        bits.append(&mut ob);
        proof {
            assert(outs@ =~= all.subrange(u as int + 1, nt as int));
            assert forall|i: int| 0 <= i < ccode@.len() implies #[trigger] ccode@[i] == nslot(sv, slots@, c_nk(sv)[i]) by {
                if i >= c0.len() {
                    assert(ccode@[i] == all[u as int].ccode@[i - clo]);
                    assert(all[u as int].ccode@[i - clo] == nslot(sv, slots@, c_nk(sv)[clo + (i - clo)]));
                }
            }
            assert forall|d: int| 0 <= d < scode@.len() implies #[trigger] scode@[d] == nslot(sv, slots@, s_nk(sv)[d]) by {
                if d >= s0.len() {
                    assert(scode@[d] == all[u as int].scode@[d - slo]);
                    assert(all[u as int].scode@[d - slo] == nslot(sv, slots@, s_nk(sv)[slo + (d - slo)]));
                }
            }
            lemma_concat(b0, obv);
            assert(bits@ == b0 + obv);
            assert forall|i: int| 0 <= i < ccode@.len() implies #[trigger] bit_at(bits@, i) == (ccode@[i] != NONE) by {
                if i >= c0.len() {
                    assert(bit_at(bits@, i) == bit_at(obv, i - clo));
                    assert(bit_at(obv, i - clo) == (all[u as int].ccode@[i - clo] != NONE));
                    assert(ccode@[i] == all[u as int].ccode@[i - clo]);
                } else {
                    assert(bit_at(bits@, i) == bit_at(b0, i));
                    assert(ccode@[i] == c0[i]);
                }
            }
            lemma_pcover(u as int + 1, ncu as int, nt as int, cch as int);
            lemma_pcover(u as int + 1, nsu as int, nt as int, sch as int);
        }
        u = u + 1;
    }
    proof {
        lemma_pcover(nt as int, ncu as int, nt as int, cch as int);
        lemma_pcover(nt as int, nsu as int, nt as int, sch as int);
    }
    Ok(Codes { ccode, scode, bits, cdense, sdense })
}

} // verus!
