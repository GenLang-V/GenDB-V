//! Class maps of one call: the nation class (0..4, `nat_cls`) of every row of a frame-of-reference coded nation-key
//! column (`nat_of`: group base + U8 code), in 2 bits per row: row `r` in bits `2 (r % 16) ..` of word `r / 16`
//! (`map_ok`). With 16 rows per 32-bit word the maps of the supplier (n_s / 4 bytes) and customer (n_c / 4 bytes)
//! rows stay cache resident for the scan's random lookups by key, and a word gather vectorizes. Built by at most
//! `workers` tasks over contiguous word ranges (`tb`), joined in order; with two or more workers both maps come from
//! one `fork_join` (`build_two_maps`).
use vstd::prelude::*;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::WorkerFailure;
use super::model::*;
use super::lookup::*;
use super::par::{tb, lemma_tb, tb_at, copy_i64s, copy_u8s};

verus! {

/// Nation key of row `r` of a coded column (`bases[r / bs] + codes[r]`).
pub open spec fn nat_of(nb: Seq<i64>, nc: Seq<u8>, bs: int, r: int) -> int {
    nb[r / bs] + nc[r] as int
}

/// A coded nation-key column of `n` rows, values in `i64`.
pub open spec fn ncol_ok(nb: Seq<i64>, nc: Seq<u8>, bs: int, n: int) -> bool {
    &&& bs >= 1
    &&& nc.len() == n
    &&& nb.len() * bs >= n
    &&& forall|r: int| 0 <= r < n ==> in_i64(#[trigger] nat_of(nb, nc, bs, r))
}

/// The 2-bit field `t` (0..16) of word `w`.
pub open spec fn get2(w: u32, t: int) -> int {
    ((w >> ((2 * t) as u32)) & 3u32) as int
}

/// Word `i` of the map holds the classes of the rows `16 i + t` below `n`.
pub open spec fn word_ok(x: Ctx, nb: Seq<i64>, nc: Seq<u8>, bs: int, n: int, i: int, w: u32) -> bool {
    forall|t: int| 0 <= t < 16 && 16 * i + t < n ==> #[trigger] get2(w, t) == nat_cls(x, nat_of(nb, nc, bs, 16 * i + t))
}

/// The map covers every row.
pub open spec fn map_ok(x: Ctx, nb: Seq<i64>, nc: Seq<u8>, bs: int, n: int, m: Seq<u32>) -> bool {
    &&& 16 * m.len() >= n
    &&& forall|i: int| 0 <= i < m.len() ==> #[trigger] word_ok(x, nb, nc, bs, n, i, m[i])
}

/// Setting field `t` of a word whose fields from `t` on are clear keeps the lower fields and sets field `t`.
proof fn lemma_set_field(w: u32, cv: u32, t: u32, s: u32)
    requires t < 16, cv < 4, s <= t, t == 0 ==> w == 0, t > 0 ==> w < (1u32 << (2 * t)),
    ensures
        ((w | (cv << (2 * t))) >> (2 * s)) & 3 == (if s == t { cv } else { (w >> (2 * s)) & 3 }),
        t < 15 ==> (w | (cv << (2 * t))) < (1u32 << (2 * (t + 1))),
{
    assert(((w | (cv << (2 * t))) >> (2 * s)) & 3 == (if s == t { cv } else { (w >> (2 * s)) & 3 })) by (bit_vector)
        requires t < 16, cv < 4, s <= t, t == 0 ==> w == 0, t > 0 ==> w < (1u32 << (2 * t));
    assert(t < 15 ==> (w | (cv << (2 * t))) < (1u32 << (2 * (t + 1)))) by (bit_vector)
        requires t < 16, cv < 4, t == 0 ==> w == 0, t > 0 ==> w < (1u32 << (2 * t));
}

/// A row's class from a covering map.
pub proof fn lemma_map_row(x: Ctx, nb: Seq<i64>, nc: Seq<u8>, bs: int, n: int, m: Seq<u32>, r: int)
    requires map_ok(x, nb, nc, bs, n, m), 0 <= r < n,
    ensures r < 16 * m.len(), get2(m[r / 16], r % 16) == nat_cls(x, nat_of(nb, nc, bs, r)),
{
    let i = r / 16;
    let t = r % 16;
    assert(16 * i + t == r);
    assert(0 <= i < m.len());
    assert(word_ok(x, nb, nc, bs, n, i, m[i]));
}

/// The class of row `r` (0 past the column).
fn row_cls(nb: &'static [i64], nc: &'static [u8], bs: usize, sh: usize, pow: bool, n: usize, nt: &Vec<u8>,
    nk: &Vec<i64>, ncl: &Vec<u8>, nn: usize, r: usize, Ghost(x): Ghost<Ctx>) -> (v: u8)
    requires
        ncol_ok(nb@, nc@, bs as int, n as int), shift_ok(bs, sh, pow),
        ntab_ok(x, nt@), ncls_ok(x, nk@, ncl@), nn == nk@.len(),
    ensures
        v < 4,
        r < n ==> v as int == nat_cls(x, nat_of(nb@, nc@, bs as int, r as int)),
    no_unwind
{
    if r < n {
        proof {
            lemma_div_below(r as int, bs as int, nb@.len() as int, n as int);
            assert(in_i64(nat_of(nb@, nc@, bs as int, r as int)));
        }
        let g = div_bs(r, bs, sh, pow);
        nat_fast(nt, nk, ncl, nn, nb[g] + nc[r] as i64, Ghost(x))
    } else {
        0
    }
}

/// The classes of the 256 codes of group `g`: `tab[k] = nat_cls(base + k)`.
fn group_tab(nb: &'static [i64], g: usize, nt: &Vec<u8>, nk: &Vec<i64>, ncl: &Vec<u8>, nn: usize, tab: &mut [u8; 256],
    Ghost(x): Ghost<Ctx>)
    requires
        g < nb@.len(), ntab_ok(x, nt@), ncls_ok(x, nk@, ncl@), nn == nk@.len(),
        nb@[g as int] <= 0x7fff_ffff_ffff_ff00,
    ensures
        forall|k: int| 0 <= k < 256 ==> #[trigger] final(tab)@[k] as int == nat_cls(x, nb@[g as int] + k),
        forall|k: int| 0 <= k < 256 ==> #[trigger] final(tab)@[k] < 4,
    no_unwind
{
    let base = nb[g];
    let mut k: usize = 0;
    while k < 256
        invariant
            g < nb@.len(), ntab_ok(x, nt@), ncls_ok(x, nk@, ncl@), nn == nk@.len(),
            base == nb@[g as int], base <= 0x7fff_ffff_ffff_ff00,
            k <= 256,
            forall|i: int| 0 <= i < k ==> #[trigger] tab@[i] as int == nat_cls(x, base + i),
            forall|i: int| 0 <= i < k ==> #[trigger] tab@[i] < 4,
        decreases 256 - k,
    {
        let v = nat_fast(nt, nk, ncl, nn, base + k as i64, Ghost(x));
        let ghost t0 = tab@;
        tab[k] = v;
        proof {
            assert forall|i: int| 0 <= i < k + 1 implies #[trigger] tab@[i] as int == nat_cls(x, base + i) && tab@[i] < 4 by {
                if i < k {
                    assert(tab@[i] == t0[i]);
                }
            }
        }
        k = k + 1;
    }
}

/// Word `wi` of the map when its 16 rows are below `n` and in group `g` (classes from the group's table).
fn map_word_tab(nb: &'static [i64], nc: &'static [u8], bs: usize, n: usize, g: usize, tab: &[u8; 256], wi: usize,
    Ghost(x): Ghost<Ctx>) -> (w: u32)
    requires
        ncol_ok(nb@, nc@, bs as int, n as int),
        g < nb@.len(),
        16 * wi + 16 <= n,
        forall|t: int| 0 <= t < 16 ==> #[trigger] ((16 * wi + t) / bs as int) == g,
        forall|k: int| 0 <= k < 256 ==> #[trigger] tab@[k] as int == nat_cls(x, nb@[g as int] + k),
        forall|k: int| 0 <= k < 256 ==> #[trigger] tab@[k] < 4,
    ensures word_ok(x, nb@, nc@, bs as int, n as int, wi as int, w),
    no_unwind
{
    let r0 = 16 * wi;
    let mut w: u32 = 0;
    let mut t: u32 = 0;
    while t < 16
        invariant
            ncol_ok(nb@, nc@, bs as int, n as int),
            g < nb@.len(),
            r0 == 16 * wi, r0 + 16 <= n,
            forall|s: int| 0 <= s < 16 ==> #[trigger] ((16 * wi + s) / bs as int) == g,
            forall|k: int| 0 <= k < 256 ==> #[trigger] tab@[k] as int == nat_cls(x, nb@[g as int] + k),
            forall|k: int| 0 <= k < 256 ==> #[trigger] tab@[k] < 4,
            t <= 16,
            t == 0 ==> w == 0,
            0 < t < 16 ==> w < (1u32 << (2 * t)),
            forall|s: int| 0 <= s < t && r0 + s < n ==> #[trigger] get2(w, s) == nat_cls(x, nat_of(nb@, nc@, bs as int, r0 + s)),
        decreases 16 - t,
    {
        let r = r0 + t as usize;
        let cv = tab[nc[r] as usize] as u32;
        proof {
            assert(r0 + (t as int) < n);
        }
        proof {
            assert(((16 * wi + t as int) / bs as int) == g);
            assert(nat_of(nb@, nc@, bs as int, r as int) == nb@[g as int] + nc@[r as int]);
            assert(cv < 4);
        }
        let w2 = w | (cv << (2 * t));
        proof {
            assert forall|s: int| 0 <= s < t + 1 && r0 + s < n implies #[trigger] get2(w2, s) == nat_cls(x, nat_of(nb@, nc@, bs as int, r0 + s)) by {
                lemma_set_field(w, cv, t, s as u32);
                assert((2 * s) as u32 == 2 * (s as u32));
                if s < t {
                    assert(get2(w, s) == nat_cls(x, nat_of(nb@, nc@, bs as int, r0 + s)));
                }
            }
            lemma_set_field(w, cv, t, t);
        }
        w = w2;
        t = t + 1;
    }
    w
}

pub struct MapTask {
    pub nb: &'static [i64],
    pub nc: &'static [u8],
    pub bs: usize,
    pub sh: usize,
    pub pow: bool,
    pub n: usize,
    pub nk: Vec<i64>,
    pub ncl: Vec<u8>,
    pub nt: Vec<u8>,
    pub w0: usize,
    pub out: Vec<u32>,
    /// Scratch: the code classes of one group.
    pub tab: [u8; 256],
    pub x: Ghost<Ctx>,
}

/// Word `wi` of the map: the classes of rows `16 wi .. 16 wi + 16`.
fn map_word(nb: &'static [i64], nc: &'static [u8], bs: usize, sh: usize, pow: bool, n: usize, nt: &Vec<u8>,
    nk: &Vec<i64>, ncl: &Vec<u8>, nn: usize, wi: usize, Ghost(x): Ghost<Ctx>) -> (w: u32)
    requires
        ncol_ok(nb@, nc@, bs as int, n as int), shift_ok(bs, sh, pow),
        ntab_ok(x, nt@), ncls_ok(x, nk@, ncl@), nn == nk@.len(),
        16 * wi + 16 <= usize::MAX,
    ensures word_ok(x, nb@, nc@, bs as int, n as int, wi as int, w),
    no_unwind
{
    let r0 = 16 * wi;
    let mut w: u32 = 0;
    let mut t: u32 = 0;
    while t < 16
        invariant
            ncol_ok(nb@, nc@, bs as int, n as int), shift_ok(bs, sh, pow),
            ntab_ok(x, nt@), ncls_ok(x, nk@, ncl@), nn == nk@.len(),
            r0 == 16 * wi, 16 * wi + 16 <= usize::MAX,
            t <= 16,
            t == 0 ==> w == 0,
            0 < t < 16 ==> w < (1u32 << (2 * t)),
            forall|s: int| 0 <= s < t && r0 + s < n ==> #[trigger] get2(w, s) == nat_cls(x, nat_of(nb@, nc@, bs as int, r0 + s)),
        decreases 16 - t,
    {
        let cv = row_cls(nb, nc, bs, sh, pow, n, nt, nk, ncl, nn, r0 + t as usize, Ghost(x)) as u32;
        let w2 = w | (cv << (2 * t));
        proof {
            assert forall|s: int| 0 <= s < t + 1 && r0 + s < n implies #[trigger] get2(w2, s) == nat_cls(x, nat_of(nb@, nc@, bs as int, r0 + s)) by {
                lemma_set_field(w, cv, t, s as u32);
                assert((2 * s) as u32 == 2 * (s as u32));
                if s < t {
                    assert(get2(w, s) == nat_cls(x, nat_of(nb@, nc@, bs as int, r0 + s)));
                }
            }
            lemma_set_field(w, cv, t, t);
        }
        w = w2;
        t = t + 1;
    }
    w
}

impl WorkerTask for MapTask {
    type Output = Vec<u32>;

    open spec fn pre(&self) -> bool {
        &&& ncol_ok(self.nb@, self.nc@, self.bs as int, self.n as int)
        &&& shift_ok(self.bs, self.sh, self.pow)
        &&& ntab_ok(self.x@, self.nt@)
        &&& ncls_ok(self.x@, self.nk@, self.ncl@)
        &&& 16 * (self.w0 + self.out@.len()) + 16 <= usize::MAX
    }

    open spec fn post(&self, out: Vec<u32>) -> bool {
        &&& out@.len() == self.out@.len()
        &&& forall|i: int| 0 <= i < out@.len() ==>
            #[trigger] word_ok(self.x@, self.nb@, self.nc@, self.bs as int, self.n as int, self.w0 + i, out@[i])
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.w0 as u64, (self.w0 as u64).wrapping_add(self.out.len() as u64))
    }

    fn run(self) -> (r: Vec<u32>) {
        let (nb, nc, bs, sh, pow, n) = (self.nb, self.nc, self.bs, self.sh, self.pow, self.n);
        let ghost x = self.x@;
        let nk = self.nk;
        let ncl = self.ncl;
        let nt = self.nt;
        let nn = nk.len();
        let w0 = self.w0;
        let mut out = self.out;
        let len = out.len();
        let mut tab: [u8; 256] = self.tab;
        let mut tg: usize = 0;
        let mut have = false;
        let mut i: usize = 0;
        while i < len
            invariant
                ncol_ok(nb@, nc@, bs as int, n as int), shift_ok(bs, sh, pow),
                ntab_ok(x, nt@), ncls_ok(x, nk@, ncl@), nn == nk@.len(),
                have ==> tg < nb@.len(),
                have ==> forall|k: int| 0 <= k < 256 ==> #[trigger] tab@[k] as int == nat_cls(x, nb@[tg as int] + k),
                have ==> forall|k: int| 0 <= k < 256 ==> #[trigger] tab@[k] < 4,
                16 * (w0 + len) + 16 <= usize::MAX,
                len == out@.len(), i <= len,
                forall|v: int| 0 <= v < i ==> #[trigger] word_ok(x, nb@, nc@, bs as int, n as int, w0 + v, out@[v]),
            decreases len - i,
        {
            // the group's code table when the word's 16 rows are in one group, else row by row
            let wi = w0 + i;
            let r0 = 16 * wi;
            let mut fast = false;
            if r0 + 16 <= n {
                let g = div_bs(r0, bs, sh, pow);
                let g2 = div_bs(r0 + 15, bs, sh, pow);
                if g == g2 {
                    proof {
                        lemma_div_below(r0 as int, bs as int, nb@.len() as int, n as int);
                    }
                    if (!have || g != tg) && nb[g] <= 0x7fff_ffff_ffff_ff00 {
                        group_tab(nb, g, &nt, &nk, &ncl, nn, &mut tab, Ghost(x));
                        tg = g;
                        have = true;
                    }
                    fast = have && g == tg;
                }
            }
            let w = if fast {
                proof {
                    assert forall|t: int| 0 <= t < 16 implies #[trigger] ((16 * wi + t) / bs as int) == tg by {
                        vstd::arithmetic::div_mod::lemma_div_is_ordered(r0 as int, 16 * wi + t, bs as int);
                        vstd::arithmetic::div_mod::lemma_div_is_ordered(16 * wi + t, r0 + 15, bs as int);
                    }
                }
                map_word_tab(nb, nc, bs, n, tg, &tab, wi, Ghost(x))
            } else {
                map_word(nb, nc, bs, sh, pow, n, &nt, &nk, &ncl, nn, wi, Ghost(x))
            };
            let ghost o0 = out@;
            crate::gendb_entry::work::put(&mut out, i, w);
            proof {
                assert forall|v: int| 0 <= v < i + 1 implies #[trigger] word_ok(x, nb@, nc@, bs as int, n as int, w0 + v, out@[v]) by {
                    if v < i {
                        assert(out@[v] == o0[v]);
                    }
                }
            }
            i = i + 1;
        }
        out
    }
}

/// Task `i` of the `ntk` tasks building the class map of a coded column of `n` rows: words `[tb(i), tb(i + 1))` of
/// the `(n + 15) / 16` words.
pub open spec fn mtask_ok(t: MapTask, nb: &'static [i64], nc: &'static [u8], bs: usize, n: usize, x: Ctx, chunk: int,
    ntk: int, i: int) -> bool
{
    &&& t.pre()
    &&& t.nb == nb && t.nc == nc && t.bs == bs && t.n == n
    &&& t.x@ == x
    &&& t.w0 == tb(0, (n + 15) / 16, chunk, ntk, i)
    &&& t.w0 + t.out@.len() == tb(0, (n + 15) / 16, chunk, ntk, i + 1)
}

/// The task count for the map of a column of `n` rows: at most `k`, each task at least 2^14 words (2^18 rows).
fn map_ntk(n: usize, k: usize) -> (ntk: usize)
    requires 1 <= k, n < usize::MAX / 32,
    ensures 1 <= ntk <= k,
{
    let nbytes = (n + 15) / 16;
    let cap = nbytes / 16384 + 1;
    if cap < k { cap } else { k }
}

/// Appends to `tasks` the `ntk` tasks building the class map of a coded nation-key column of `n` rows.
fn map_tasks(nb: &'static [i64], nc: &'static [u8], bs: usize, sh: usize, pow: bool, n: usize,
    nk: &Vec<i64>, ncl: &Vec<u8>, ntb: &Vec<u8>, ntk: usize, tasks: &mut Vec<MapTask>, Ghost(x): Ghost<Ctx>)
    -> (chunk: Ghost<int>)
    requires
        ncol_ok(nb@, nc@, bs as int, n as int), shift_ok(bs, sh, pow),
        ntab_ok(x, ntb@), ncls_ok(x, nk@, ncl@),
        n < usize::MAX / 32,
        1 <= ntk <= MAX_WORKERS,
    ensures
        final(tasks)@.len() == old(tasks)@.len() + ntk,
        forall|i: int| 0 <= i < old(tasks)@.len() ==> #[trigger] final(tasks)@[i] == old(tasks)@[i],
        chunk@ >= 0, chunk@ * ntk <= (n + 15) / 16,
        forall|k: int| old(tasks)@.len() <= k < final(tasks)@.len() ==>
            mtask_ok(#[trigger] final(tasks)@[k], nb, nc, bs, n, x, chunk@, ntk as int, k - old(tasks)@.len()),
{
    let ghost t0 = tasks@;
    let nbytes = (n + 15) / 16;
    let chunk = nbytes / ntk;
    proof {
        assert(16 * nbytes <= n + 15) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod((n + 15) as int, 16);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound((n + 15) as int, 16);
        }
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(nbytes as int, ntk as int);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(nbytes as int, ntk as int);
        assert(chunk * ntk <= nbytes) by (nonlinear_arith)
            requires ntk * chunk + nbytes as int % ntk as int == nbytes, nbytes as int % ntk as int >= 0;
    }
    let mut t: usize = 0;
    while t < ntk
        invariant
            ncol_ok(nb@, nc@, bs as int, n as int), shift_ok(bs, sh, pow),
            ntab_ok(x, ntb@), ncls_ok(x, nk@, ncl@),
            nbytes == (n + 15) / 16, n < usize::MAX / 32, 16 * nbytes <= n + 15,
            1 <= ntk <= MAX_WORKERS,
            chunk * ntk <= nbytes,
            t <= ntk,
            tasks@.len() == t0.len() + t,
            forall|i: int| 0 <= i < t0.len() ==> #[trigger] tasks@[i] == t0[i],
            forall|k: int| t0.len() <= k < tasks@.len() ==>
                mtask_ok(#[trigger] tasks@[k], nb, nc, bs, n, x, chunk as int, ntk as int, k - t0.len()),
        decreases ntk - t,
    {
        proof {
            lemma_tb(0, nbytes as int, chunk as int, ntk as int, t as int, t + 1);
        }
        let b0 = tb_at(0, nbytes, chunk, ntk, t);
        let b1 = if t + 1 == ntk { nbytes } else { tb_at(0, nbytes, chunk, ntk, t + 1) };
        proof {
            assert(b1 <= nbytes);
            assert(16 * b1 + 16 <= usize::MAX);
        }
        let task = MapTask {
            nb, nc, bs, sh, pow, n, nk: copy_i64s(nk), ncl: copy_u8s(ncl), nt: copy_u8s(ntb), w0: b0,
            out: vec![0u32; b1 - b0], tab: [0u8; 256], x: Ghost(x),
        };
        let ghost tp = tasks@;
        tasks.push(task);
        proof {
            assert(mtask_ok(tasks@[t0.len() + t], nb, nc, bs, n, x, chunk as int, ntk as int, t as int));
            assert forall|k: int| t0.len() <= k < tasks@.len() implies
                mtask_ok(#[trigger] tasks@[k], nb, nc, bs, n, x, chunk as int, ntk as int, k - t0.len()) by {
                if k < tp.len() {
                    assert(tasks@[k] == tp[k]);
                }
            }
            assert forall|i: int| 0 <= i < t0.len() implies #[trigger] tasks@[i] == t0[i] by {
                assert(tasks@[i] == tp[i]);
            }
        }
        t = t + 1;
    }
    Ghost(chunk as int)
}

/// The class map from the outputs of its `ntk` tasks `ts`, the first `ntk` entries of `outs` (removed from it).
fn map_join(outs: &mut Vec<Vec<u32>>, Ghost(ts): Ghost<Seq<MapTask>>, nb: &'static [i64], nc: &'static [u8],
    bs: usize, n: usize, ntk: usize, Ghost(chunk): Ghost<int>, Ghost(x): Ghost<Ctx>) -> (m: Vec<u32>)
    requires
        ntk <= old(outs)@.len(), ntk <= ts.len(),
        n < usize::MAX / 32,
        1 <= ntk <= MAX_WORKERS,
        chunk >= 0, chunk * ntk <= (n + 15) / 16,
        forall|i: int| 0 <= i < ntk ==> (#[trigger] ts[i]).post(old(outs)@[i])
            && mtask_ok(ts[i], nb, nc, bs, n, x, chunk, ntk as int, i),
    ensures
        final(outs)@ == old(outs)@.subrange(ntk as int, old(outs)@.len() as int),
        map_ok(x, nb@, nc@, bs as int, n as int, m@),
{
    let ghost os = outs@;
    let nbytes = (n + 15) / 16;
    proof {
        assert(16 * nbytes >= n) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod((n + 15) as int, 16);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound((n + 15) as int, 16);
        }
        lemma_tb(0, nbytes as int, chunk, ntk as int, 0, 0);
    }
    let mut m: Vec<u32> = Vec::with_capacity(nbytes);
    let mut k: usize = 0;
    while k < ntk
        invariant
            ntk <= os.len(), ntk <= ts.len(),
            nbytes == (n + 15) / 16,
            1 <= ntk <= MAX_WORKERS,
            chunk >= 0, chunk * ntk <= nbytes,
            k <= ntk,
            outs@ == os.subrange(k as int, os.len() as int),
            forall|i: int| 0 <= i < ntk ==> (#[trigger] ts[i]).post(os[i])
                && mtask_ok(ts[i], nb, nc, bs, n, x, chunk, ntk as int, i),
            m@.len() == tb(0, nbytes as int, chunk, ntk as int, k as int),
            forall|i: int| 0 <= i < m@.len() ==> #[trigger] word_ok(x, nb@, nc@, bs as int, n as int, i, m@[i]),
        decreases ntk - k,
    {
        proof {
            lemma_tb(0, nbytes as int, chunk, ntk as int, k as int, k + 1);
            assert(outs@[0] == os[k as int]);
        }
        let mut o = outs.remove(0);
        let ghost m0 = m@;
        let ghost oo = o@;
        m.append(&mut o);
        proof {
            assert(outs@ =~= os.subrange(k + 1, os.len() as int));
            assert(ts[k as int].post(os[k as int]));
            assert(mtask_ok(ts[k as int], nb, nc, bs, n, x, chunk, ntk as int, k as int));
            assert(oo == os[k as int]@);
            assert forall|i: int| 0 <= i < m@.len() implies #[trigger] word_ok(x, nb@, nc@, bs as int, n as int, i, m@[i]) by {
                if i < m0.len() {
                    assert(m@[i] == m0[i]);
                } else {
                    let w = i - m0.len();
                    assert(m@[i] == oo[w]);
                    assert(word_ok(x, nb@, nc@, bs as int, n as int, ts[k as int].w0 + w, oo[w]));
                }
            }
        }
        k = k + 1;
    }
    proof {
        lemma_tb(0, nbytes as int, chunk, ntk as int, ntk as int, ntk as int);
        assert(m@.len() == nbytes);
    }
    m
}

/// The class map of a coded nation-key column of `n` rows, built by at most `workers` tasks.
pub fn build_map(nb: &'static [i64], nc: &'static [u8], bs: usize, sh: usize, pow: bool, n: usize,
    nk: &Vec<i64>, ncl: &Vec<u8>, ntb: &Vec<u8>, workers: usize,
    dispatch: &mut Dispatch, Ghost(x): Ghost<Ctx>) -> (r: Result<Vec<u32>, WorkerFailure>)
    requires
        ncol_ok(nb@, nc@, bs as int, n as int), shift_ok(bs, sh, pow),
        ntab_ok(x, ntb@), ncls_ok(x, nk@, ncl@),
        n < usize::MAX / 32,
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(m) ==> map_ok(x, nb@, nc@, bs as int, n as int, m@),
{
    let ntk = map_ntk(n, workers);
    let mut tasks: Vec<MapTask> = Vec::new();
    let chunk = map_tasks(nb, nc, bs, sh, pow, n, nk, ncl, ntb, ntk, &mut tasks, Ghost(x));
    let ghost ts = tasks@;
    proof {
        assert forall|i: int| 0 <= i < ts.len() implies #[trigger] ts[i].pre() by {
            assert(mtask_ok(ts[i], nb, nc, bs, n, x, chunk@, ntk as int, i - 0));
        }
    }
    let mut outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(f) => return Err(f),
    };
    proof {
        assert forall|i: int| 0 <= i < ntk implies (#[trigger] ts[i]).post(outs@[i])
            && mtask_ok(ts[i], nb, nc, bs, n, x, chunk@, ntk as int, i) by {
            assert(mtask_ok(ts[i], nb, nc, bs, n, x, chunk@, ntk as int, i - 0));
        }
    }
    let m = map_join(&mut outs, Ghost(ts), nb, nc, bs, n, ntk, chunk, Ghost(x));
    Ok(m)
}

/// The customer and supplier class maps by one `fork_join` of at most `workers` tasks (`2 <= workers`): about
/// `workers / 16` tasks for the supplier column (which has 1/15 of the customer rows in TPC-H), the rest for the
/// customer column.
fn build_two_maps(c: &Cols, s: Shifts, nk: &Vec<i64>, ncl: &Vec<u8>, ntb: &Vec<u8>, workers: usize,
    dispatch: &mut Dispatch, Ghost(x): Ghost<Ctx>) -> (r: Result<(Vec<u32>, Vec<u32>), WorkerFailure>)
    requires
        ncol_ok(c.cn_bases@, c.cn_codes@, c.bs_c as int, c.n_c as int), shift_ok(c.bs_c, s.sh_c, s.pow_c),
        ncol_ok(c.sn_bases@, c.sn_codes@, c.bs_s as int, c.n_s as int), shift_ok(c.bs_s, s.sh_s, s.pow_s),
        ntab_ok(x, ntb@), ncls_ok(x, nk@, ncl@),
        c.n_c < usize::MAX / 32, c.n_s < usize::MAX / 32,
        2 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok((cm, sm)) ==> map_ok(x, c.cn_bases@, c.cn_codes@, c.bs_c as int, c.n_c as int, cm@)
            && map_ok(x, c.sn_bases@, c.sn_codes@, c.bs_s as int, c.n_s as int, sm@),
{
    let ks0 = (workers + 15) / 16;
    let ks = map_ntk(c.n_s, ks0);
    let kc = map_ntk(c.n_c, workers - ks);
    let mut tasks: Vec<MapTask> = Vec::new();
    let chc = map_tasks(c.cn_bases, c.cn_codes, c.bs_c, s.sh_c, s.pow_c, c.n_c, nk, ncl, ntb, kc, &mut tasks, Ghost(x));
    let ghost tc = tasks@;
    let chs = map_tasks(c.sn_bases, c.sn_codes, c.bs_s, s.sh_s, s.pow_s, c.n_s, nk, ncl, ntb, ks, &mut tasks, Ghost(x));
    let ghost ts = tasks@;
    proof {
        assert forall|i: int| 0 <= i < ts.len() implies #[trigger] ts[i].pre() by {
            if i < kc {
                assert(ts[i] == tc[i]);
                assert(mtask_ok(tc[i], c.cn_bases, c.cn_codes, c.bs_c, c.n_c, x, chc@, kc as int, i - 0));
            } else {
                assert(mtask_ok(ts[i], c.sn_bases, c.sn_codes, c.bs_s, c.n_s, x, chs@, ks as int, i - kc));
            }
        }
    }
    let mut outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(f) => return Err(f),
    };
    let ghost os = outs@;
    proof {
        assert forall|i: int| 0 <= i < kc implies (#[trigger] ts[i]).post(outs@[i])
            && mtask_ok(ts[i], c.cn_bases, c.cn_codes, c.bs_c, c.n_c, x, chc@, kc as int, i) by {
            assert(ts[i] == tc[i]);
            assert(mtask_ok(tc[i], c.cn_bases, c.cn_codes, c.bs_c, c.n_c, x, chc@, kc as int, i - 0));
        }
    }
    let cm = map_join(&mut outs, Ghost(ts), c.cn_bases, c.cn_codes, c.bs_c, c.n_c, kc, chc, Ghost(x));
    let ghost ts2 = ts.subrange(kc as int, ts.len() as int);
    proof {
        assert(outs@ == os.subrange(kc as int, os.len() as int));
        assert forall|i: int| 0 <= i < ks implies (#[trigger] ts2[i]).post(outs@[i])
            && mtask_ok(ts2[i], c.sn_bases, c.sn_codes, c.bs_s, c.n_s, x, chs@, ks as int, i) by {
            assert(ts2[i] == ts[kc + i]);
            assert(outs@[i] == os[kc + i]);
            assert(ts[kc + i].post(os[kc + i]));
            assert(mtask_ok(ts[kc + i], c.sn_bases, c.sn_codes, c.bs_s, c.n_s, x, chs@, ks as int, (kc + i) - kc));
        }
    }
    let sm = map_join(&mut outs, Ghost(ts2), c.sn_bases, c.sn_codes, c.bs_s, c.n_s, ks, chs, Ghost(x));
    Ok((cm, sm))
}

// ------------------------------------------------------------------------------------------------ the scan's maps

/// The customer class map (dense customer keys from `ck0`).
pub open spec fn cmap_ok(c: Cols, x: Ctx, ck0: i64, m: Seq<u32>) -> bool {
    &&& c_dense_ok(c, true, ck0)
    &&& map_ok(x, c.cn_bases@, c.cn_codes@, c.bs_c as int, c.n_c as int, m)
}

/// The supplier class map (dense supplier keys from `sk0`).
pub open spec fn smap2_ok(c: Cols, x: Ctx, sk0: i64, m: Seq<u32>) -> bool {
    &&& s_dense_ok(c, true, sk0)
    &&& map_ok(x, c.sn_bases@, c.sn_codes@, c.bs_s as int, c.n_s as int, m)
}

/// The scan's maps: the customer map when the customer keys are dense (else empty and `cmv` false), the supplier
/// map likewise.
pub fn build_maps(c: &Cols, s: Shifts, sd: bool, sk0: i64, cd: bool, ck0: i64, nk: &Vec<i64>, ncl: &Vec<u8>,
    ntb: &Vec<u8>, workers: usize, dispatch: &mut Dispatch, Ghost(x): Ghost<Ctx>)
    -> (r: Result<(bool, Vec<u32>, bool, Vec<u32>), WorkerFailure>)
    requires
        cols_ok(*c), keys_ok(*c), shifts_ok(*c, s), s_dense_ok(*c, sd, sk0), c_dense_ok(*c, cd, ck0),
        ntab_ok(x, ntb@), ncls_ok(x, nk@, ncl@),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok((cmv, cm, smv, sm)) ==> (cmv ==> cmap_ok(*c, x, ck0, cm@)) && (smv ==> smap2_ok(*c, x, sk0, sm@)),
{
    proof {
        assert forall|r: int| 0 <= r < c.n_c implies in_i64(#[trigger] nat_of(c.cn_bases@, c.cn_codes@, c.bs_c as int, r)) by {
            assert(in_i64(cnat(*c, r)));
        }
        assert forall|r: int| 0 <= r < c.n_s implies in_i64(#[trigger] nat_of(c.sn_bases@, c.sn_codes@, c.bs_s as int, r)) by {
            assert(in_i64(snat(*c, r)));
        }
        assert(c.cn_bases@.len() * c.bs_c >= c.n_c);
        assert(c.sn_bases@.len() * c.bs_s >= c.n_s);
    }
    let cmv = cd && c.n_c < usize::MAX / 32;
    let smv = sd && c.n_s < usize::MAX / 32;
    if cmv && smv && workers >= 2 {
        return match build_two_maps(c, s, nk, ncl, ntb, workers, dispatch, Ghost(x)) {
            Ok((cm, sm)) => Ok((cmv, cm, smv, sm)),
            Err(f) => Err(f),
        };
    }
    let cm: Vec<u32> = if cmv {
        match build_map(c.cn_bases, c.cn_codes, c.bs_c, s.sh_c, s.pow_c, c.n_c, nk, ncl, ntb, workers, dispatch, Ghost(x)) {
            Ok(m) => m,
            Err(f) => return Err(f),
        }
    } else {
        Vec::new()
    };
    let sm: Vec<u32> = if smv {
        match build_map(c.sn_bases, c.sn_codes, c.bs_s, s.sh_s, s.pow_s, c.n_s, nk, ncl, ntb, workers, dispatch, Ghost(x)) {
            Ok(m) => m,
            Err(f) => return Err(f),
        }
    } else {
        Vec::new()
    };
    Ok((cmv, cm, smv, sm))
}

} // verus!
