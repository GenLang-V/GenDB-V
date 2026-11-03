//! The compact partsupp table of the matching parts (`scan::ents_ok`), built per range of part rows (`BuildTask`, the
//! ranges of the part filter, starting at multiples of 64). The matching part of rank `r` (the number of matching
//! parts before it) owns the `SLOTS` entries from `SLOTS * r`, which pack `(ps_suppkey, nation tag, ps_supplycost)`
//! of every partsupp row of its key (`EMPTY` after them; the tag is the nation row of the supplier of that key,
//! `scan::ntag`, so the kernel needs no supplier lookup); `wpre[w]` is the rank of the first part row of bit word `w`.
//! A range reports `ok == false` when partsupp is not sorted by key, a matching part has more than `SLOTS` partsupp
//! rows, a value does not pack, or its table is too small; the kernel then reads partsupp directly.
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::WorkerTask;
use crate::gendb_entry::work::put;
use super::model::*;
use super::cols::*;
use super::lookups::*;
use super::scan::*;
use super::common::popcnt::{cnt_below, lemma_cnt_step};

verus! {

/// Local entries `ents[k * SLOTS ..]` list the partsupp rows of part key `pk` (the global table's `slots_cover`).
pub open spec fn local_cover(m: M, ents: Seq<u64>, k: int, pk: int) -> bool {
    &&& 0 <= k
    &&& (k + 1) * SLOTS as int <= ents.len()
    &&& slots_cover(m, ents, k, pk)
}

/// The nation tag of supplier key `sk` (dense supplier keys, nation keys in `[0, 256)`).
fn supp_tag(c: &Cols, d: &Divs, ntab: &Vec<u64>, sk: i64, Ghost(m): Ghost<M>) -> (nt: u64)
    requires look_ok(*c, *d, m), ntab_ok(ntab@, true, m), s_dense_ok(m), m.n_n < NO_TAG,
    ensures nt as int == ntag(m, sk as int),
    no_unwind
{
    let sn = c.s_n;
    if 1 <= sk && (sk as u64) <= (sn as u64) {
        let s = (sk - 1) as usize;
        proof {
            assert(skey(m, s as int) == s + 1);
            lemma_spos(m, sk as int, s as int);
        }
        let n = nation_of(c, d, ntab, true, s, Ghost(m));
        if n == NO_NATION { NO_TAG } else { n }
    } else {
        proof {
            assert forall|x: int| 0 <= x < m.s_n implies #[trigger] skey(m, x) != sk as int by {
                assert(skey(m, x) == x + 1);
            }
            lemma_spos(m, sk as int, 0);
        }
        NO_TAG
    }
}

/// Fill the `SLOTS` entries from `k * SLOTS` (all `EMPTY`) with the partsupp rows of key `pk` (sorted partsupp).
fn fill_part(c: &Cols, d: &Divs, ntab: &Vec<u64>, pk: i64, ents: &mut Vec<u64>, k: usize, Ghost(m): Ghost<M>) -> (ok: bool)
    requires
        look_ok(*c, *d, m), m.t_kind == 1,
        ntab_ok(ntab@, true, m), s_dense_ok(m), m.n_n < NO_TAG,
        (k + 1) * SLOTS <= old(ents)@.len() <= usize::MAX,
        forall|i: int| 0 <= i < SLOTS ==> #[trigger] old(ents)@[k * SLOTS as int + i] == EMPTY,
    ensures
        final(ents)@.len() == old(ents)@.len(),
        forall|x: int| 0 <= x < old(ents)@.len() && !(k * SLOTS <= x < (k + 1) * SLOTS) ==> #[trigger] final(ents)@[x] == old(ents)@[x],
        ok ==> slots_cover(m, final(ents)@, k as int, pk as int),
    no_unwind
{
    assert(SLOTS == 4);
    let base = k * SLOTS;
    match ps_start(c, d, pk, Ghost(m)) {
        None => {
            proof {
                assert forall|i: int| 0 <= i < SLOTS implies #[trigger] slot_ok(m, pk as int, ents@[k * SLOTS as int + i]) by {}
            }
            true
        },
        Some(lo) => {
            let mut t = lo;
            let mut slot: usize = 0;
            let mut end = false;
            while t < c.t_n && !end
                invariant
                    look_ok(*c, *d, m), m.t_kind == 1,
                    ntab_ok(ntab@, true, m), s_dense_ok(m), m.n_n < NO_TAG,
                    (k + 1) * SLOTS <= ents@.len() <= usize::MAX,
                    base == k * SLOTS,
                    tstart_ok(m, pk as int, lo as int),
                    lo <= t <= m.t_n,
                    slot == t - lo, slot <= SLOTS,
                    ents@.len() == old(ents)@.len(),
                    forall|x: int| 0 <= x < ents@.len() && !(k * SLOTS <= x < (k + 1) * SLOTS) ==> #[trigger] ents@[x] == old(ents)@[x],
                    forall|i: int| slot <= i < SLOTS ==> #[trigger] ents@[k * SLOTS as int + i] == EMPTY,
                    forall|i: int| 0 <= i < slot ==> #[trigger] ents@[k * SLOTS as int + i] as int == pack(m, tsk(m, lo + i), tcost(m, lo + i)),
                    forall|x: int| lo <= x < t ==> #[trigger] packable(m, x),
                    forall|x: int| lo <= x < t ==> #[trigger] tpk(m, x) == pk as int,
                    end ==> t < m.t_n && tpk(m, t as int) != pk as int,
                decreases m.t_n - t + if end { 0int } else { 1int },
            {
                let (a, skv, cost) = get_t(c, d, t, Ghost(m));
                if a != pk {
                    end = true;
                } else {
                    if slot == SLOTS {
                        return false;
                    }
                    if skv < 0 || skv >= 0xff_ffff || cost < 0 || cost > 0xffff_ffff {
                        return false;
                    }
                    let nt = supp_tag(c, d, ntab, skv, Ghost(m));
                    proof { lemma_ntag(m, skv as int); }
                    let e = ((skv as u64) << 40u64) | (nt << 32u64) | (cost as u64);
                    proof { lemma_unpack(skv as u64, nt, cost as u64); }
                    let ghost e0 = ents@;
                    put(ents, base + slot, e);
                    proof {
                        assert(ents@[k * SLOTS as int + slot as int] as int == pack(m, tsk(m, lo + slot), tcost(m, lo + slot)));
                        assert(tpk(m, t as int) == pk as int && packable(m, t as int));
                        assert forall|i: int| 0 <= i < slot implies #[trigger] ents@[k * SLOTS as int + i] == e0[k * SLOTS as int + i] by {}
                        assert forall|i: int| slot + 1 <= i < SLOTS implies #[trigger] ents@[k * SLOTS as int + i] == EMPTY by {
                            assert(ents@[k * SLOTS as int + i] == e0[k * SLOTS as int + i]);
                        }
                        assert forall|x: int| 0 <= x < ents@.len() && !(k * SLOTS <= x < (k + 1) * SLOTS) implies #[trigger] ents@[x] == old(ents)@[x] by {
                            assert(ents@[x] == e0[x]);
                        }
                    }
                    slot = slot + 1;
                    t = t + 1;
                }
            }
            proof {
                // the rows of `pk` are exactly `[lo, t)`: earlier rows have smaller keys, later ones larger
                assert forall|x: int| 0 <= x < m.t_n && #[trigger] tpk(m, x) == pk as int implies lo <= x < t by {
                    if x >= t {
                        if t < m.t_n {
                            assert(tpk(m, t as int) != pk as int);
                            lemma_t_sorted(m, lo as int, t as int);
                            lemma_t_sorted(m, t as int, x);
                        }
                    }
                }
                assert forall|i: int| 0 <= i < SLOTS implies #[trigger] slot_ok(m, pk as int, ents@[k * SLOTS as int + i]) by {
                    if i < slot {
                        let tt = lo + i;
                        assert(tpk(m, tt) == pk as int);
                        assert(packable(m, tt));
                        assert(pack(m, tsk(m, tt), tcost(m, tt)) == ents@[k * SLOTS as int + i] as int);
                    }
                }
                assert forall|x: int| 0 <= x < m.t_n && #[trigger] tpk(m, x) == pk as int implies
                    packable(m, x) && exists|i: int| 0 <= i < SLOTS && #[trigger] ents@[k * SLOTS as int + i] as int == pack(m, tsk(m, x), tcost(m, x)) by {
                    let i = x - lo;
                    assert(ents@[k * SLOTS as int + i] as int == pack(m, tsk(m, lo + i), tcost(m, lo + i)));
                }
            }
            true
        },
    }
}

/// Set the `SLOTS` entries of local rank `k` to `EMPTY`; the others are unchanged.
fn clear_slots(ents: &mut Vec<u64>, k: usize)
    requires (k + 1) * SLOTS <= old(ents)@.len() <= usize::MAX,
    ensures
        final(ents)@.len() == old(ents)@.len(),
        forall|i: int| 0 <= i < SLOTS ==> #[trigger] final(ents)@[k * SLOTS as int + i] == EMPTY,
        forall|x: int| 0 <= x < old(ents)@.len() && !(k * SLOTS <= x < (k + 1) * SLOTS) ==> #[trigger] final(ents)@[x] == old(ents)@[x],
    no_unwind
{
    assert(SLOTS == 4);
    let base = k * SLOTS;
    put(ents, base, EMPTY);
    put(ents, base + 1, EMPTY);
    put(ents, base + 2, EMPTY);
    put(ents, base + 3, EMPTY);
}

/// Entries of an earlier local rank `kx < k`, untouched by a write to rank `k`, keep covering.
proof fn lemma_cover_keep(m: M, e0: Seq<u64>, e1: Seq<u64>, kx: int, k: int, pk: int)
    requires
        0 <= kx < k, (k + 1) * SLOTS as int <= e0.len(), e1.len() == e0.len(),
        local_cover(m, e0, kx, pk),
        forall|x: int| 0 <= x < e0.len() && !(k * SLOTS <= x < (k + 1) * SLOTS) ==> #[trigger] e1[x] == e0[x],
    ensures local_cover(m, e1, kx, pk),
{
    assert forall|i: int| 0 <= i < SLOTS implies #[trigger] e1[kx * SLOTS as int + i] == e0[kx * SLOTS as int + i] by {
        assert(kx * SLOTS as int + i < k * SLOTS as int) by (nonlinear_arith) requires 0 <= i < 4, kx + 1 <= k;
        assert(0 <= kx * SLOTS as int + i) by (nonlinear_arith) requires 0 <= i, 0 <= kx;
    }
    assert forall|i: int| 0 <= i < SLOTS implies #[trigger] slot_ok(m, pk, e1[kx * SLOTS as int + i]) by {
        assert(slot_ok(m, pk, e0[kx * SLOTS as int + i]));
    }
    assert forall|t: int| 0 <= t < m.t_n && #[trigger] tpk(m, t) == pk implies
        packable(m, t) && exists|i: int| 0 <= i < SLOTS && #[trigger] e1[kx * SLOTS as int + i] as int == pack(m, tsk(m, t), tcost(m, t)) by {
        let i = choose|i: int| 0 <= i < SLOTS && #[trigger] e0[kx * SLOTS as int + i] as int == pack(m, tsk(m, t), tcost(m, t));
        assert(e1[kx * SLOTS as int + i] == e0[kx * SLOTS as int + i]);
    }
}

/// The part rows `[c_lo, c_hi)` (`c_lo` a multiple of 64) whose first matching part has rank `k0`; `cap` matching parts
/// fit its entries.
pub struct BuildTask {
    pub cols: Cols,
    pub divs: Divs,
    pub bits: Arc<Vec<u64>>,
    pub ntab: Arc<Vec<u64>>,
    pub p_dense: bool,
    pub c_lo: usize,
    pub c_hi: usize,
    pub k0: u64,
    pub cap: usize,
    pub wpre: Vec<u32>,
    pub ents: Vec<u64>,
    pub m: Ghost<M>,
}

pub struct BuildOut {
    pub wpre: Vec<u32>,
    pub ents: Vec<u64>,
    pub ok: bool,
}

pub open spec fn build_pre(t: BuildTask) -> bool {
    let m = t.m@;
    &&& look_ok(t.cols, t.divs, m)
    &&& t.p_dense ==> p_dense_ok(m)
    &&& ntab_ok((*t.ntab)@, true, m) && s_dense_ok(m) && m.n_n < NO_TAG
    &&& t.c_lo <= t.c_hi <= m.p_n
    &&& t.c_lo % 64 == 0
    &&& (*t.bits)@.len() * 64 >= m.p_n
    &&& t.wpre@.len() == (t.c_hi - t.c_lo + 63) / 64
    &&& t.ents@.len() == t.cap * SLOTS
    &&& t.cap * SLOTS <= usize::MAX
    &&& t.c_hi + 64 <= usize::MAX
}

/// The rank of part row `c` from the range's word prefixes.
pub open spec fn local_rank(bits: Seq<u64>, wpre: Seq<u32>, c_lo: int, c: int) -> int {
    wpre[(c - c_lo) / 64] as int + cnt_below(bits[c / 64], c % 64)
}

pub open spec fn build_post(t: BuildTask, out: BuildOut) -> bool {
    let m = t.m@;
    let bits = (*t.bits)@;
    &&& out.wpre@.len() == t.wpre@.len()
    &&& out.ents@.len() == t.ents@.len()
    &&& out.ok ==> forall|c: int| t.c_lo <= c < t.c_hi && #[trigger] bit_of(bits, c) ==>
            t.k0 <= local_rank(bits, out.wpre@, t.c_lo as int, c)
            && local_cover(m, out.ents@, local_rank(bits, out.wpre@, t.c_lo as int, c) - t.k0, pkey(m, c))
}

impl WorkerTask for BuildTask {
    type Output = BuildOut;

    open spec fn pre(&self) -> bool {
        build_pre(*self)
    }

    open spec fn post(&self, out: BuildOut) -> bool {
        build_post(*self, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.c_lo as u64, self.c_hi as u64)
    }

    fn run(self) -> (out: BuildOut) {
        let ghost task = self;
        let BuildTask { cols, divs, bits, ntab, p_dense, c_lo, c_hi, k0, cap, wpre, ents, m: gm } = self;
        let ghost m = gm@;
        let ghost bv = (*bits)@;
        let c = cols;
        let d = divs;
        let mut wpre = wpre;
        let mut ents = ents;
        if c.t_kind != 1 {
            return BuildOut { wpre, ents, ok: false };
        }
        let mut ok = true;
        let mut k: usize = 0;
        let mut r = c_lo;
        // one bit word per step
        while r < c_hi && ok
            invariant
                task.pre(),
                m == task.m@, c == task.cols, d == task.divs, bits == task.bits, bv == (*bits)@, ntab == task.ntab,
                p_dense == task.p_dense, c_lo == task.c_lo, c_hi == task.c_hi, k0 == task.k0, cap == task.cap,
                m.t_kind == 1,
                c_lo <= r, r % 64 == 0, r < c_hi + 64,
                k <= cap,
                wpre@.len() == task.wpre@.len(), ents@.len() == task.ents@.len(),
                ok ==> forall|x: int| c_lo <= x < r && x < c_hi && #[trigger] bit_of(bv, x) ==>
                    k0 <= local_rank(bv, wpre@, c_lo as int, x)
                    && local_rank(bv, wpre@, c_lo as int, x) - k0 < k
                    && local_cover(m, ents@, local_rank(bv, wpre@, c_lo as int, x) - k0, pkey(m, x)),
            decreases c_hi + 64 - r + if ok { 1int } else { 0int },
        {
            if k0 as u128 + k as u128 > 0xffff_ffffu128 {
                ok = false;
            } else {
                let wl = (r - c_lo) / 64;
                proof {
                    assert(wl < wpre@.len()) by { assert(r - c_lo + 63 < c_hi - c_lo + 63 + 1); }
                    assert(r / 64 < bv.len()) by { assert(r < m.p_n); }
                }
                let ghost wpre0 = wpre@;
                put(&mut wpre, wl, (k0 + k as u64) as u32);
                let word = bits[r / 64];
                let kw = k;
                proof {
                    // earlier words keep their prefix
                    assert forall|x: int| c_lo <= x < r && x < c_hi && #[trigger] bit_of(bv, x) implies
                        local_rank(bv, wpre@, c_lo as int, x) == local_rank(bv, wpre0, c_lo as int, x) by {
                        assert((x - c_lo) / 64 < wl) by { }
                    }
                }
                let mut b: usize = 0;
                while b < 64 && r + b < c_hi && ok
                    invariant
                        task.pre(),
                        m == task.m@, c == task.cols, d == task.divs, bits == task.bits, bv == (*bits)@, ntab == task.ntab,
                        p_dense == task.p_dense, c_lo == task.c_lo, c_hi == task.c_hi, k0 == task.k0, cap == task.cap,
                        m.t_kind == 1,
                        c_lo <= r, r % 64 == 0, r < c_hi,
                        wl == (r - c_lo) / 64, wl < wpre@.len(),
                        wpre@[wl as int] as int == k0 + kw,
                        word == bv[r as int / 64],
                        b <= 64,
                        k <= cap,
                        ok ==> k == kw + cnt_below(word, b as int),
                        k <= kw + b, k0 + kw <= 0xffff_ffff,
                        wpre@.len() == task.wpre@.len(), ents@.len() == task.ents@.len(),
                        ok ==> forall|x: int| c_lo <= x < r + b && x < c_hi && #[trigger] bit_of(bv, x) ==>
                            k0 <= local_rank(bv, wpre@, c_lo as int, x)
                            && local_rank(bv, wpre@, c_lo as int, x) - k0 < k
                            && local_cover(m, ents@, local_rank(bv, wpre@, c_lo as int, x) - k0, pkey(m, x)),
                    decreases 64 - b,
                {
                    let row = r + b;
                    proof {
                        lemma_cnt_step(word, b as int);
                        assert(row / 64 == r / 64) by { }
                        assert(row % 64 == b) by { }
                        assert((row - c_lo) / 64 == wl) by { }
                    }
                    if (word >> (b as u64)) & 1u64 == 1u64 {
                        if k >= cap {
                            ok = false;
                        } else {
                            let pk: i64 = get_pkey(&c, &d, row, Ghost(m));
                            let ghost e00 = ents@;
                            clear_slots(&mut ents, k);
                            proof {
                                assert forall|x: int| c_lo <= x < row && x < c_hi && #[trigger] bit_of(bv, x) implies
                                    local_cover(m, ents@, local_rank(bv, wpre@, c_lo as int, x) - k0, pkey(m, x)) by {
                                    let kx = local_rank(bv, wpre@, c_lo as int, x) - k0;
                                    lemma_cover_keep(m, e00, ents@, kx, k as int, pkey(m, x));
                                }
                            }
                            let ghost e0 = ents@;
                            if fill_part(&c, &d, &ntab, pk, &mut ents, k, Ghost(m)) {
                                proof {
                                    assert(local_rank(bv, wpre@, c_lo as int, row as int) - k0 == k);
                                    // earlier parts' entries lie below `k * SLOTS`
                                    assert forall|x: int| c_lo <= x < row && x < c_hi && #[trigger] bit_of(bv, x) implies
                                        local_cover(m, ents@, local_rank(bv, wpre@, c_lo as int, x) - k0, pkey(m, x)) by {
                                        let kx = local_rank(bv, wpre@, c_lo as int, x) - k0;
                                        assert(local_cover(m, e0, kx, pkey(m, x)));
                                        assert forall|i: int| 0 <= i < SLOTS implies #[trigger] ents@[kx * SLOTS as int + i] == e0[kx * SLOTS as int + i] by {
                                            assert(kx * SLOTS as int + i < k * SLOTS as int) by { assert(kx + 1 <= k); }
                                        }
                                        assert forall|i: int| 0 <= i < SLOTS implies #[trigger] slot_ok(m, pkey(m, x), ents@[kx * SLOTS as int + i]) by {
                                            assert(slot_ok(m, pkey(m, x), e0[kx * SLOTS as int + i]));
                                        }
                                        assert forall|t: int| 0 <= t < m.t_n && #[trigger] tpk(m, t) == pkey(m, x) implies
                                            packable(m, t) && exists|i: int| 0 <= i < SLOTS && #[trigger] ents@[kx * SLOTS as int + i] as int == pack(m, tsk(m, t), tcost(m, t)) by {
                                            let i = choose|i: int| 0 <= i < SLOTS && #[trigger] e0[kx * SLOTS as int + i] as int == pack(m, tsk(m, t), tcost(m, t));
                                            assert(ents@[kx * SLOTS as int + i] == e0[kx * SLOTS as int + i]);
                                        }
                                    }
                                }
                                k = k + 1;
                            } else {
                                ok = false;
                            }
                        }
                    }
                    b = b + 1;
                }
                r = r + 64;
            }
        }
        BuildOut { wpre, ents, ok }
    }
}

} // verus!
