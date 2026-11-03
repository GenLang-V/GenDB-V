//! Key lookups of the Q7 scan (all `no_unwind`, so worker tasks can call them): a nation key's class from the
//! class window, the supplier and customer rows of a key (one probe when the keys are dense: stored row `r` holds
//! key `key0 + r`; else the key index), and an order's customer class from a guessed stored orders row (one probe
//! when the guess holds the key; else the orders key index). Group indexes are shifts when the block size is a
//! power of two (`div_bs`).
use vstd::prelude::*;
use vstd::arithmetic::power2::pow2;
use crate::stores::facts::interface::common::keyidx::{fkey, key_find};
use super::model::*;
use std::sync::Arc;

verus! {

/// Block-size facts: `pow ==> bs == 2^sh`.
pub open spec fn shift_ok(bs: usize, sh: usize, pow: bool) -> bool {
    &&& bs >= 1
    &&& pow ==> sh < 64 && pow2(sh as nat) == bs
}

/// `r / bs`, by a shift when `bs == 2^sh`.
pub fn div_bs(r: usize, bs: usize, sh: usize, pow: bool) -> (q: usize)
    requires shift_ok(bs, sh, pow),
    ensures q == r / bs,
    no_unwind
{
    if pow {
        let r64 = r as u64;
        let s64 = sh as u64;
        proof {
            vstd::bits::lemma_u64_shr_is_div(r64, s64);
        }
        let q = r64 >> s64;
        proof {
            vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(r as int, 1, bs as int);
            vstd::arithmetic::div_mod::lemma_div_basics(r as int);
        }
        q as usize
    } else {
        r / bs
    }
}

/// The shift facts of a scan's three looked-up tables.
pub struct Shifts {
    pub sh_o: usize,
    pub pow_o: bool,
    pub sh_s: usize,
    pub pow_s: bool,
    pub sh_c: usize,
    pub pow_c: bool,
}

impl Copy for Shifts {}

impl Clone for Shifts {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

pub open spec fn shifts_ok(c: Cols, s: Shifts) -> bool {
    &&& shift_ok(c.bs_o, s.sh_o, s.pow_o)
    &&& shift_ok(c.bs_s, s.sh_s, s.pow_s)
    &&& shift_ok(c.bs_c, s.sh_c, s.pow_c)
}

/// Dense keys: stored row `r` holds key `key0 + r`.
pub open spec fn s_dense_ok(c: Cols, dense: bool, key0: i64) -> bool {
    dense ==> forall|r: int| 0 <= r < c.n_s ==> #[trigger] skey(c, r) == key0 + r
}

pub open spec fn c_dense_ok(c: Cols, dense: bool, key0: i64) -> bool {
    dense ==> forall|r: int| 0 <= r < c.n_c ==> #[trigger] ckey(c, r) == key0 + r
}

/// The listed nation classes, as the scan holds them.
pub open spec fn ncls_ok(x: Ctx, nk: Seq<i64>, nc: Seq<u8>) -> bool {
    &&& x.nk == nk
    &&& x.nc == nc
    &&& nk.len() == nc.len()
    &&& forall|i: int| 0 <= i < nc.len() ==> #[trigger] nc[i] < 4
}

proof fn lemma_cls_in_bound(nk: Seq<i64>, nc: Seq<u8>, v: int, n: int)
    requires 0 <= n <= nc.len(), n <= nk.len(), forall|i: int| 0 <= i < nc.len() ==> #[trigger] nc[i] < 4,
    ensures 0 <= cls_in(nk, nc, v, n) < 4,
    decreases n,
{
    if n > 0 {
        lemma_cls_in_bound(nk, nc, v, n - 1);
    }
}

/// The class of nation key `v`.
pub fn nat_class(nk: &Vec<i64>, nc: &Vec<u8>, nn: usize, v: i64, Ghost(x): Ghost<Ctx>) -> (r: u8)
    requires ncls_ok(x, nk@, nc@), nn == nk@.len(),
    ensures r as int == nat_cls(x, v as int), r < 4,
    no_unwind
{
    let mut i = nn;
    while i > 0
        invariant
            ncls_ok(x, nk@, nc@), nn == nk@.len(),
            i <= nn,
            nat_cls(x, v as int) == cls_in(nk@, nc@, v as int, i as int),
        decreases i,
    {
        if nk[i - 1] == v {
            proof {
                lemma_cls_in_bound(nk@, nc@, v as int, nn as int);
            }
            return nc[i - 1];
        }
        i = i - 1;
    }
    0
}

/// Nation keys below `NT` have their class in a table (`ntab_ok`).
pub const NT: usize = 64;

pub open spec fn ntab_ok(x: Ctx, t: Seq<u8>) -> bool {
    &&& t.len() == NT
    &&& forall|v: int| 0 <= v < NT ==> #[trigger] t[v] as int == nat_cls(x, v)
    &&& forall|v: int| 0 <= v < NT ==> #[trigger] t[v] < 4
}

/// The class table of the nation keys `0 .. NT`.
pub fn build_ntab(nk: &Vec<i64>, nc: &Vec<u8>, Ghost(x): Ghost<Ctx>) -> (t: Vec<u8>)
    requires ncls_ok(x, nk@, nc@),
    ensures ntab_ok(x, t@),
{
    let nn = nk.len();
    let mut t: Vec<u8> = Vec::new();
    let mut v: usize = 0;
    while v < NT
        invariant
            ncls_ok(x, nk@, nc@), nn == nk@.len(),
            v <= NT, t@.len() == v,
            forall|w: int| 0 <= w < v ==> #[trigger] t@[w] as int == nat_cls(x, w),
            forall|w: int| 0 <= w < v ==> #[trigger] t@[w] < 4,
        decreases NT - v,
    {
        let cl = nat_class(nk, nc, nn, v as i64, Ghost(x));
        t.push(cl);
        v = v + 1;
    }
    t
}

/// The class of nation key `v`: from the table when `v < NT`.
pub fn nat_fast(nt: &Vec<u8>, nk: &Vec<i64>, nc: &Vec<u8>, nn: usize, v: i64, Ghost(x): Ghost<Ctx>) -> (r: u8)
    requires ntab_ok(x, nt@), ncls_ok(x, nk@, nc@), nn == nk@.len(),
    ensures r as int == nat_cls(x, v as int), r < 4,
    no_unwind
{
    if 0 <= v && v < NT as i64 {
        nt[v as usize]
    } else {
        nat_class(nk, nc, nn, v, Ghost(x))
    }
}

/// Dense supplier keys: the class of supplier row `r` (key `key0 + r`) at `m[r]`.
pub open spec fn smap_ok(c: Cols, x: Ctx, dense: bool, key0: i64, m: Seq<u8>) -> bool {
    dense ==> {
        &&& m.len() == c.n_s
        &&& forall|r: int| 0 <= r < c.n_s ==> #[trigger] m[r] as int == s_cls(c, x, key0 + r)
        &&& forall|r: int| 0 <= r < c.n_s ==> #[trigger] m[r] < 4
    }
}

/// The supplier class map (empty unless the supplier keys are dense).
pub fn build_smap(c: &Cols, s: Shifts, dense: bool, key0: i64, nt: &Vec<u8>, nk: &Vec<i64>, nc: &Vec<u8>,
    Ghost(x): Ghost<Ctx>) -> (m: Arc<Vec<u8>>)
    requires
        cols_ok(*c), keys_ok(*c), shifts_ok(*c, s), s_dense_ok(*c, dense, key0),
        ntab_ok(x, nt@), ncls_ok(x, nk@, nc@),
    ensures smap_ok(*c, x, dense, key0, m@),
{
    let nn = nk.len();
    let mut m: Vec<u8> = Vec::with_capacity(if dense { c.n_s } else { 0 });
    if dense {
        let n = c.n_s;
        let mut r: usize = 0;
        while r < n
            invariant
                cols_ok(*c), keys_ok(*c), shifts_ok(*c, s), s_dense_ok(*c, dense, key0), dense,
                ntab_ok(x, nt@), ncls_ok(x, nk@, nc@), nn == nk@.len(),
                n == c.n_s, r <= n, m@.len() == r,
                forall|w: int| 0 <= w < r ==> #[trigger] m@[w] as int == s_cls(*c, x, key0 + w),
                forall|w: int| 0 <= w < r ==> #[trigger] m@[w] < 4,
            decreases n - r,
        {
            proof {
                lemma_div_below(r as int, c.bs_s as int, c.sk_bases@.len() as int, c.n_s as int);
                assert(in_i64(snat(*c, r as int)));
                let k = key0 + r;
                assert(skey(*c, r as int) == k);
                assert(has_s(*c, k));
                let w = srow(*c, k);
                assert(skey(*c, w) == k && 0 <= w < c.n_s);
                assert(w == r);
            }
            let g = div_bs(r, c.bs_s, s.sh_s, s.pow_s);
            let cl = nat_fast(nt, nk, nc, nn, c.sn_bases[g] + c.sn_codes[r] as i64, Ghost(x));
            m.push(cl);
            r = r + 1;
        }
    }
    Arc::new(m)
}

/// The supplier class of supplier key `k`: from the class map when the keys are dense.
pub fn supp_fast(c: &Cols, s: Shifts, dense: bool, key0: i64, m: &Arc<Vec<u8>>, nt: &Vec<u8>, nk: &Vec<i64>,
    nc: &Vec<u8>, nn: usize, k: i64, Ghost(x): Ghost<Ctx>) -> (r: u8)
    requires
        cols_ok(*c), keys_ok(*c), shifts_ok(*c, s), s_dense_ok(*c, dense, key0), smap_ok(*c, x, dense, key0, m@),
        ntab_ok(x, nt@), ncls_ok(x, nk@, nc@), nn == nk@.len(),
    ensures r as int == s_cls(*c, x, k as int), r < 4,
    no_unwind
{
    if dense {
        match supp_row(c, dense, key0, k) {
            Some(i) => {
                proof {
                    assert(skey(*c, i as int) == key0 + i);
                }
                m[i]
            },
            None => 0,
        }
    } else {
        supp_class(c, s, dense, key0, nt, nk, nc, nn, k, Ghost(x))
    }
}

/// The supplier row of key `k`.
pub fn supp_row(c: &Cols, dense: bool, key0: i64, k: i64) -> (r: Option<usize>)
    requires cols_ok(*c), s_dense_ok(*c, dense, key0),
    ensures
        r matches Some(i) ==> i < c.n_s && skey(*c, i as int) == k,
        r is None ==> !has_s(*c, k as int),
    no_unwind
{
    if dense {
        let d = k as i128 - key0 as i128;
        if 0 <= d && d < c.n_s as i128 {
            proof {
                assert(skey(*c, d as int) == key0 + d);
            }
            Some(d as usize)
        } else {
            proof {
                assert forall|i: int| 0 <= i < c.n_s implies #[trigger] skey(*c, i) != k by {
                    assert(skey(*c, i) == key0 + i);
                }
            }
            None
        }
    } else {
        match key_find(c.sk_codes, c.sk_bases, c.no_codes, c.no_bases, c.bs_s, c.s_kind, c.n_s, k as i128) {
            Some(i) => Some(i),
            None => {
                proof {
                    assert forall|i: int| 0 <= i < c.n_s implies #[trigger] skey(*c, i) != k by {
                        assert(fkey(c.sk_codes@, c.sk_bases@, c.bs_s as int, i) != k);
                    }
                }
                None
            },
        }
    }
}

/// The customer row of key `k`.
pub fn cust_row(c: &Cols, dense: bool, key0: i64, k: i64) -> (r: Option<usize>)
    requires cols_ok(*c), c_dense_ok(*c, dense, key0),
    ensures
        r matches Some(i) ==> i < c.n_c && ckey(*c, i as int) == k,
        r is None ==> !has_c(*c, k as int),
    no_unwind
{
    if dense {
        let d = k as i128 - key0 as i128;
        if 0 <= d && d < c.n_c as i128 {
            proof {
                assert(ckey(*c, d as int) == key0 + d);
            }
            Some(d as usize)
        } else {
            proof {
                assert forall|i: int| 0 <= i < c.n_c implies #[trigger] ckey(*c, i) != k by {
                    assert(ckey(*c, i) == key0 + i);
                }
            }
            None
        }
    } else {
        match key_find(c.ck_codes, c.ck_bases, c.no_codes, c.no_bases, c.bs_c, c.c_kind, c.n_c, k as i128) {
            Some(i) => Some(i),
            None => {
                proof {
                    assert forall|i: int| 0 <= i < c.n_c implies #[trigger] ckey(*c, i) != k by {
                        assert(fkey(c.ck_codes@, c.ck_bases@, c.bs_c as int, i) != k);
                    }
                }
                None
            },
        }
    }
}

/// `r < n` and `len * bs >= n` put `r / bs` below `len`.
pub proof fn lemma_div_below(r: int, bs: int, len: int, n: int)
    requires bs >= 1, 0 <= r < n, len * bs >= n,
    ensures 0 <= r / bs < len,
{
    crate::stores::facts::interface::common::read::lemma_div_lt(r, bs, len);
}

/// The supplier class of supplier key `k`.
pub fn supp_class(c: &Cols, s: Shifts, dense: bool, key0: i64, nt: &Vec<u8>, nk: &Vec<i64>, nc: &Vec<u8>, nn: usize, k: i64,
    Ghost(x): Ghost<Ctx>) -> (r: u8)
    requires
        cols_ok(*c), keys_ok(*c), shifts_ok(*c, s), s_dense_ok(*c, dense, key0),
        ntab_ok(x, nt@), ncls_ok(x, nk@, nc@), nn == nk@.len(),
    ensures r as int == s_cls(*c, x, k as int), r < 4,
    no_unwind
{
    match supp_row(c, dense, key0, k) {
        Some(i) => {
            proof {
                assert(has_s(*c, k as int));
                let w = srow(*c, k as int);
                assert(skey(*c, w) == k && 0 <= w < c.n_s);
                assert(w == i);
                assert(in_i64(snat(*c, i as int)));
                lemma_div_below(i as int, c.bs_s as int, c.sk_bases@.len() as int, c.n_s as int);
            }
            let g = div_bs(i, c.bs_s, s.sh_s, s.pow_s);
            let nkey = c.sn_bases[g] + c.sn_codes[i] as i64;
            nat_fast(nt, nk, nc, nn, nkey, Ghost(x))
        },
        None => 0,
    }
}

/// The customer class of customer key `k`.
pub fn cust_class(c: &Cols, s: Shifts, dense: bool, key0: i64, nt: &Vec<u8>, nk: &Vec<i64>, nc: &Vec<u8>, nn: usize, k: i64,
    Ghost(x): Ghost<Ctx>) -> (r: u8)
    requires
        cols_ok(*c), keys_ok(*c), shifts_ok(*c, s), c_dense_ok(*c, dense, key0),
        ntab_ok(x, nt@), ncls_ok(x, nk@, nc@), nn == nk@.len(),
    ensures r as int == c_cls(*c, x, k as int), r < 4,
    no_unwind
{
    match cust_row(c, dense, key0, k) {
        Some(i) => {
            proof {
                assert(has_c(*c, k as int));
                let w = crow(*c, k as int);
                assert(ckey(*c, w) == k && 0 <= w < c.n_c);
                assert(w == i);
                assert(in_i64(cnat(*c, i as int)));
                lemma_div_below(i as int, c.bs_c as int, c.ck_bases@.len() as int, c.n_c as int);
            }
            let g = div_bs(i, c.bs_c, s.sh_c, s.pow_c);
            let nkey = c.cn_bases[g] + c.cn_codes[i] as i64;
            nat_fast(nt, nk, nc, nn, nkey, Ghost(x))
        },
        None => 0,
    }
}

/// The stored orders row of order key `k`: `guess` when it holds the key, else by the key index.
pub fn order_row(c: &Cols, s: Shifts, k: i64, guess: usize) -> (r: Option<usize>)
    requires cols_ok(*c), shifts_ok(*c, s),
    ensures
        r matches Some(p) ==> p < c.n_o && okey(*c, p as int) == k,
        r is None ==> !has_o(*c, k as int),
    no_unwind
{
    if guess < c.n_o {
        proof {
            lemma_div_below(guess as int, c.bs_o as int, c.ok_bases@.len() as int, c.n_o as int);
            assert(in_i64(okey(*c, guess as int)));
        }
        let g = div_bs(guess, c.bs_o, s.sh_o, s.pow_o);
        if c.ok_bases[g] + c.ok_codes[guess] as i64 == k {
            return Some(guess);
        }
    }
    match key_find(c.ok_codes, c.ok_bases, c.oi_codes, c.oi_bases, c.bs_o, c.oi_kind, c.n_o, k as i128) {
        Some(p) => Some(p),
        None => {
            proof {
                assert forall|p: int| 0 <= p < c.n_o implies #[trigger] okey(*c, p) != k by {
                    assert(fkey(c.ok_codes@, c.ok_bases@, c.bs_o as int, p) != k);
                }
            }
            None
        },
    }
}

/// The customer class of order key `k` (through its order's customer), looking the order up from `guess`.
pub fn order_class(c: &Cols, s: Shifts, dense: bool, key0: i64, nt: &Vec<u8>, nk: &Vec<i64>, nc: &Vec<u8>, nn: usize, k: i64,
    guess: usize, Ghost(x): Ghost<Ctx>) -> (r: u8)
    requires
        cols_ok(*c), keys_ok(*c), shifts_ok(*c, s), c_dense_ok(*c, dense, key0),
        ntab_ok(x, nt@), ncls_ok(x, nk@, nc@), nn == nk@.len(),
    ensures r as int == o_cls(*c, x, k as int), r < 4,
    no_unwind
{
    match order_row(c, s, k, guess) {
        Some(p) => {
            proof {
                assert(has_o(*c, k as int));
                let w = orow(*c, k as int);
                assert(okey(*c, w) == k && 0 <= w < c.n_o);
                assert(w == p);
                assert(in_i64(ocust(*c, p as int)));
                lemma_div_below(p as int, c.bs_o as int, c.oc_bases@.len() as int, c.n_o as int);
            }
            let g = div_bs(p, c.bs_o, s.sh_o, s.pow_o);
            let ck = c.oc_bases[g] + c.oc_codes[p] as i64;
            cust_class(c, s, dense, key0, nt, nk, nc, nn, ck, Ghost(x))
        },
        None => 0,
    }
}

} // verus!
