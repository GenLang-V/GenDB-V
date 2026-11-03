//! Builders of the scan's lookup structures on the calling thread.
//!
//! - `build_pfilter`: the part filter. The dictionary entry of `$3` (`dict_find`), the keys of the parts of that
//!   type (`match_keys`, group by group: a group whose base cannot reach the entry is skipped), then over their key
//!   range a bitmap with one bit per key and a coarse bitmap with one bit per 8 keys (`build_bits`); without a
//!   matching part an empty one-bit bitmap, and over a range wider than `2^32` keys the lookup mode.
//! - `build_ntab`: per nation row its key, whether its region is named `$2` and whether its name is `$1`, and the
//!   same by key for the keys below `NK`.
use vstd::prelude::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::stored::StoredParts;
use crate::gendb_entry::bound_db;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::stores::custpart::interface as ci;
use crate::stores::suppliers::interface as si;
use crate::stores::custpart::interface::common::colfmt as cc;
use crate::stores::suppliers::interface::common::colfmt as sc;
use crate::stores::custpart::declaration as cd;
use crate::stores::suppliers::declaration as sd;
use super::sql::*;
use super::model::*;
use super::kernel::*;
use super::decode::*;
use super::filters::*;
use super::setup::*;

verus! {

// ------------------------------------------------------------------------------------------------ bit vectors

/// `n` zero words.
fn zeros(n: usize) -> (v: Vec<u64>)
    ensures v@.len() == n, forall|i: int| 0 <= i < n ==> #[trigger] v@[i] == 0,
{
    let mut v: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n, v@.len() == i, forall|k: int| 0 <= k < i ==> #[trigger] v@[k] == 0,
        decreases n - i,
    {
        v.push(0);
        i = i + 1;
    }
    v
}

proof fn lemma_zero_bits(ws: Seq<u64>, x: int)
    requires 0 <= x, x / 64 < ws.len(), ws[x / 64] == 0,
    ensures !bit_at(ws, x),
{
    let t = (x % 64) as u64;
    assert((0u64 >> t) & 1u64 == 0u64) by (bit_vector);
}

/// Sets bit `x`.
fn set_bit(ws: &mut Vec<u64>, x: u64)
    requires (x / 64) < old(ws)@.len(),
    ensures
        final(ws)@.len() == old(ws)@.len(),
        forall|y: int| 0 <= y && y / 64 < old(ws)@.len() ==> #[trigger] bit_at(final(ws)@, y) == (y == x || bit_at(old(ws)@, y)),
{
    let nw = ws.len();
    proof {
        lemma_shr6(x);
        lemma_and63(x);
        assert((x >> 6) as int == x as int / 64);
        assert((x >> 6) < nw);
    }
    let w = (x >> 6) as usize;
    let s = x & 63;
    proof {
        assert(w as int == x as int / 64);
        assert(s as int == x as int % 64);
    }
    let a = ws[w];
    ws[w] = a | (1u64 << s);
    proof {
        let o = old(ws)@;
        let nw = ws@;
        assert forall|y: int| 0 <= y && y / 64 < o.len() implies #[trigger] bit_at(nw, y) == (y == x || bit_at(o, y)) by {
            let t = (y % 64) as u64;
            if y / 64 == w as int {
                assert(nw[y / 64] == a | (1u64 << s));
                assert((((a | (1u64 << s)) >> t) & 1u64 == 1u64) == (t == s || ((a >> t) & 1u64 == 1u64))) by (bit_vector)
                    requires s < 64, t < 64;
                assert((y == x) == (t == s)) by {
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(y, 64);
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, 64);
                    vstd::arithmetic::div_mod::lemma_mod_bound(y, 64);
                    assert(t as int == y % 64);
                    assert(y == 64 * (y / 64) + y % 64);
                    assert(x as int == 64 * (x as int / 64) + x as int % 64);
                }
            } else {
                assert(nw[y / 64] == o[y / 64]);
                assert(y != x as int);
            }
        }
    }
}

/// Some key is `lo + x`.
pub open spec fn key_hit(keys: Seq<i64>, m: int, lo: int, x: int) -> bool {
    exists|q: int| 0 <= q < m && #[trigger] keys[q] as int == lo + x
}

/// The bitmaps of the keys `keys` over `[lo, lo + nbits)`.
fn build_bits(keys: &Vec<i64>, lo: i64, nbits: u64) -> (r: (Vec<u64>, Vec<u64>))
    requires
        1 <= nbits <= bits_cap(),
        forall|q: int| 0 <= q < keys@.len() ==> lo <= #[trigger] keys@[q] < lo + nbits,
    ensures
        r.0@.len() * 64 >= nbits, r.1@.len() * 512 >= nbits, r.1@.len() >= 1,
        forall|x: int| 0 <= x < nbits ==> #[trigger] bit_at(r.0@, x) == key_hit(keys@, keys@.len() as int, lo as int, x),
        forall|x: int| 0 <= x < nbits && #[trigger] bit_at(r.0@, x) ==> bit_at(r.1@, x / 8),
{
    let nw = ((nbits + 63) / 64) as usize;
    let nc = ((nbits + 511) / 512) as usize;
    let mut bits = zeros(nw);
    let mut coarse = zeros(nc);
    proof {
        assert forall|x: int| 0 <= x < nbits implies #[trigger] bit_at(bits@, x) == key_hit(keys@, 0, lo as int, x) by {
            lemma_zero_bits(bits@, x);
        }
    }
    let n = keys.len();
    let mut q: usize = 0;
    while q < n
        invariant
            n == keys@.len(), q <= n,
            1 <= nbits <= bits_cap(),
            nw as int * 64 >= nbits, nc as int * 512 >= nbits, nc >= 1,
            bits@.len() == nw, coarse@.len() == nc,
            forall|k: int| 0 <= k < keys@.len() ==> lo <= #[trigger] keys@[k] < lo + nbits,
            forall|x: int| 0 <= x < nbits ==> #[trigger] bit_at(bits@, x) == key_hit(keys@, q as int, lo as int, x),
            forall|k: int| 0 <= k < q ==> #[trigger] bit_at(coarse@, (keys@[k] - lo) / 8),
        decreases n - q,
    {
        let off = (keys[q] as i128 - lo as i128) as u64;
        let ghost ob = bits@;
        let ghost oc = coarse@;
        set_bit(&mut bits, off);
        proof { lemma_shr3(off); }
        set_bit(&mut coarse, off >> 3);
        proof {
            assert forall|x: int| 0 <= x < nbits implies #[trigger] bit_at(bits@, x) == key_hit(keys@, q + 1, lo as int, x) by {
                assert(x / 64 < nw) by {
                    vstd::arithmetic::div_mod::lemma_div_is_ordered(x, nbits as int - 1, 64);
                }
                if x == off {
                    assert(keys@[q as int] as int == lo + x);
                } else if key_hit(keys@, q + 1, lo as int, x) {
                    let k = choose|k: int| 0 <= k < q + 1 && #[trigger] keys@[k] as int == lo + x;
                    assert(k != q);
                }
            }
            assert forall|k: int| 0 <= k < q + 1 implies #[trigger] bit_at(coarse@, (keys@[k] - lo) / 8) by {
                let c = (keys@[k] - lo) / 8;
                assert(c / 64 < nc) by {
                    vstd::arithmetic::div_mod::lemma_div_is_ordered(keys@[k] - lo, nbits as int - 1, 8);
                    vstd::arithmetic::div_mod::lemma_div_is_ordered(c, (nbits as int - 1) / 8, 64);
                    vstd::arithmetic::div_mod::lemma_div_denominator(nbits as int - 1, 8, 64);
                }
            }
        }
        q = q + 1;
    }
    proof {
        assert forall|x: int| 0 <= x < nbits && #[trigger] bit_at(bits@, x) implies bit_at(coarse@, x / 8) by {
            let k = choose|k: int| 0 <= k < n && #[trigger] keys@[k] as int == lo + x;
            assert(keys@[k] - lo == x);
        }
    }
    (bits, coarse)
}

// ------------------------------------------------------------------------------------------------ the part filter

/// Part row `i` has type `$3`.
pub open spec fn mrow(f: PFilter, i: int) -> bool {
    f.has_t && ptype(f, i) == f.t
}

/// The keys of the parts of type `$3` (`gi`: their rows), and bounds of the keys.
fn match_keys(f: &PFilter) -> (r: (Vec<i64>, i64, i64, Ghost<Seq<int>>))
    requires pf_shape(*f),
    ensures
        r.0@.len() == r.3@.len(),
        forall|q: int| 0 <= q < r.3@.len() ==> 0 <= #[trigger] r.3@[q] < f.n_p && mrow(*f, r.3@[q])
            && r.0@[q] as int == pkey(*f, r.3@[q]) && r.1 <= r.0@[q] <= r.2,
        forall|i: int| 0 <= i < f.n_p && #[trigger] mrow(*f, i) ==> exists|q: int| 0 <= q < r.3@.len() && r.3@[q] == i,
{
    let mut keys: Vec<i64> = Vec::new();
    let ghost mut gi: Seq<int> = Seq::empty();
    let mut lo: i64 = i64::MAX;
    let mut hi: i64 = i64::MIN;
    if !f.has_t {
        return (keys, lo, hi, Ghost(gi));
    }
    let n = f.n_p;
    let bs = f.bs_p;
    let t = f.t;
    let mut g: usize = 0;
    let mut gs: usize = 0;
    while gs < n
        invariant
            pf_shape(*f), f.has_t, n == f.n_p, bs == f.bs_p, t == f.t,
            gs <= n, gs == g * bs,
            keys@.len() == gi.len(),
            forall|q: int| 0 <= q < gi.len() ==> 0 <= #[trigger] gi[q] < gs && mrow(*f, gi[q])
                && keys@[q] as int == pkey(*f, gi[q]) && lo <= keys@[q] <= hi,
            forall|i: int| 0 <= i < gs && #[trigger] mrow(*f, i) ==> exists|q: int| 0 <= q < gi.len() && gi[q] == i,
        decreases n - gs,
    {
        let ge = if n - gs > bs { gs + bs } else { n };
        proof {
            crate::stores::custpart::interface::common::read::lemma_div_lt(gs as int, bs as int, f.pk_b@.len() as int);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(gs as int, bs as int, g as int, 0);
            assert(gs as int / bs as int == g);
        }
        let base = f.pt_b[g];
        if t >= base && t - base < 256 {
            let want = (t - base) as u8;
            let mut i = gs;
            while i < ge
                invariant
                    pf_shape(*f), f.has_t, n == f.n_p, bs == f.bs_p, t == f.t,
                    gs <= i <= ge <= n, ge <= gs + bs, gs == g * bs, g < f.pk_b@.len(),
                    base == f.pt_b@[g as int], want as int == t - base,
                    keys@.len() == gi.len(),
                    forall|q: int| 0 <= q < gi.len() ==> 0 <= #[trigger] gi[q] < i && mrow(*f, gi[q])
                        && keys@[q] as int == pkey(*f, gi[q]) && lo <= keys@[q] <= hi,
                    forall|j: int| 0 <= j < i && #[trigger] mrow(*f, j) ==> exists|q: int| 0 <= q < gi.len() && gi[q] == j,
                decreases ge - i,
            {
                proof {
                    lemma_div_group(i as int, bs as int, g as int);
                }
                if f.pt_c[i] == want {
                    proof {
                        assert(in_i64(pkey(*f, i as int)));
                    }
                    let k = f.pk_b[g] + f.pk_c[i] as i64;
                    let ghost og = gi;
                    keys.push(k);
                    if k < lo { lo = k; }
                    if k > hi { hi = k; }
                    proof {
                        gi = gi.push(i as int);
                        assert(mrow(*f, i as int));
                        assert(gi[gi.len() - 1] == i as int);
                        assert forall|j: int| 0 <= j < i + 1 && #[trigger] mrow(*f, j) implies exists|q: int| 0 <= q < gi.len() && gi[q] == j by {
                            if j < i {
                                let q = choose|q: int| 0 <= q < og.len() && og[q] == j;
                                assert(gi[q] == og[q]);
                            } else {
                                assert(gi[gi.len() - 1] == j);
                            }
                        }
                    }
                } else {
                    proof { assert(!mrow(*f, i as int)); }
                }
                i = i + 1;
            }
        } else {
            proof {
                assert forall|j: int| gs <= j < ge implies !#[trigger] mrow(*f, j) by {
                    lemma_div_group(j, bs as int, g as int);
                }
            }
        }
        g = g + 1;
        gs = ge;
        if gs < n {
            proof { assert(gs == g * bs) by (nonlinear_arith) requires gs == (g - 1) * bs + bs; }
        } else {
            proof { assert(gs == n); }
            return (keys, lo, hi, Ghost(gi));
        }
    }
    (keys, lo, hi, Ghost(gi))
}

/// The part filter's fields other than its bitmaps agree.
pub open spec fn same_base(f: PFilter, f0: PFilter) -> bool {
    &&& f.n_p == f0.n_p && f.bs_p == f0.bs_p && f.pk_c == f0.pk_c && f.pk_b == f0.pk_b && f.pt_c == f0.pt_c
    &&& f.pt_b == f0.pt_b && f.p_kind == f0.p_kind && f.t == f0.t && f.has_t == f0.has_t && f.e32 == f0.e32
    &&& f.e64 == f0.e64
}

/// The part filter of type `$3`.
pub fn build_pfilter(cp: &mut StoredParts, p2: &'static [u8], Ghost(sv): Ghost<StoresView>, Ghost(db): Ghost<Database>,
    Ghost(ps): Ghost<Seq<Literal>>) -> (f: PFilter)
    requires old(cp)@ == sv.custpart, bound_db(sv, db), ps.len() == 3, txt(ps[2]) == p2@,
    ensures final(cp)@ == old(cp)@, pf_from(sv, ps, f), pf_ok(f),
{
    let f0 = pfilter_base(cp, p2, Ghost(sv), Ghost(db), Ghost(ps));
    let f = pfilter_serial(&f0);
    proof {
        assert(pf_from(sv, ps, f));
    }
    f
}

/// The part filter's slices and the dictionary entry of `$3`, without bitmaps.
pub fn pfilter_base(cp: &mut StoredParts, p2: &'static [u8], Ghost(sv): Ghost<StoresView>, Ghost(db): Ghost<Database>,
    Ghost(ps): Ghost<Seq<Literal>>) -> (f0: PFilter)
    requires old(cp)@ == sv.custpart, bound_db(sv, db), ps.len() == 3, txt(ps[2]) == p2@,
    ensures final(cp)@ == old(cp)@, pf_from(sv, ps, f0), pf_shape(f0),
{
    proof {
        lemma_tables(sv, db);
        let rel = cd::stored_relations(db)[1];
        assert(ci::part_ok(pa_tp(sv), rel));
        assert(cc::dict_col_at(pa_tp(sv), ci::PA_GROUPS as int, ci::PA_TYPE_CODES as int, ci::PA_TYPE_BASE as int,
            ci::PA_TYPE_DICT_OFFS as int, ci::PA_TYPE_DICT_BYTES as int, rel, 4));
    }
    let pf = ci::PART_FIRST;
    let n_p = cp.part_len(pf + ci::PA_PARTKEY_CODES);
    let bs_p = block_rows(cp, pf + ci::PA_LAYOUT, n_p);
    let pk_c = whole_u32(cp, pf + ci::PA_PARTKEY_CODES);
    let pk_b = whole_i64(cp, pf + ci::PA_PARTKEY_BASE);
    let pt_c = whole_u8(cp, pf + ci::PA_TYPE_CODES);
    let pt_b = whole_u64(cp, pf + ci::PA_TYPE_BASE);
    let p_kind = first_u64(cp, pf + ci::PA_KEYIDX_KIND);
    let doffs = whole_u64(cp, pf + ci::PA_TYPE_DICT_OFFS);
    let dbytes = whole_u8(cp, pf + ci::PA_TYPE_DICT_BYTES);
    let k = doffs.len() - 1;
    let found = crate::stores::custpart::interface::common::read::dict_find(doffs, dbytes, k, p2, p2.len());
    let (has_t, t): (bool, u64) = match found {
        Some(x) => (true, x as u64),
        None => (false, 0),
    };
    let e32: &'static [u32] = pk_c.split_at(0).0;
    let e64: &'static [u64] = pt_b.split_at(0).0;
    proof {
        assert(e32@ =~= Seq::<u32>::empty());
        assert(e64@ =~= Seq::<u64>::empty());
    }
    let f0 = PFilter {
        use_bits: false, bits: Vec::new(), coarse: Vec::new(), nbits: 0, clamp: 0, pk_lo: 0,
        n_p, bs_p, pk_c, pk_b, pt_c, pt_b, p_kind, t, has_t, e32, e64,
    };
    proof {
        assert(pf_from(sv, ps, f0));
        lemma_pa(sv, db, ps, f0);
    }
    f0
}

/// Filters with the same fields other than bitmaps have the same keys, types, matches and shape facts.
pub proof fn lemma_same_base(f: PFilter, f0: PFilter)
    requires same_base(f, f0), pf_shape(f0),
    ensures
        pf_shape(f),
        forall|i: int| #[trigger] pkey(f, i) == pkey(f0, i),
        forall|i: int| #[trigger] ptype(f, i) == ptype(f0, i),
        forall|i: int| #[trigger] mrow(f, i) == mrow(f0, i),
        forall|v: int| #[trigger] pmatch(f, v) == pmatch(f0, v),
{
    assert forall|i: int| #[trigger] pkey(f, i) == pkey(f0, i) by {}
    assert forall|i: int| #[trigger] ptype(f, i) == ptype(f0, i) by {}
    assert forall|i: int| #[trigger] mrow(f, i) == mrow(f0, i) by {}
    assert forall|i: int| 0 <= i < f.n_p implies in_i64(#[trigger] pkey(f, i)) by {
        assert(pkey(f, i) == pkey(f0, i));
    }
    assert forall|a: int, b: int| 0 <= a < f.n_p && 0 <= b < f.n_p && a != b
        implies #[trigger] pkey(f, a) != #[trigger] pkey(f, b) by {
        assert(pkey(f, a) == pkey(f0, a) && pkey(f, b) == pkey(f0, b));
    }
    assert forall|v: int| #[trigger] pmatch(f, v) == pmatch(f0, v) by {
        if pmatch(f, v) {
            let i = choose|i: int| 0 <= i < f.n_p && #[trigger] pkey(f, i) == v && ptype(f, i) == f.t;
            assert(pkey(f0, i) == v && ptype(f0, i) == f0.t);
        }
        if pmatch(f0, v) {
            let i = choose|i: int| 0 <= i < f0.n_p && #[trigger] pkey(f0, i) == v && ptype(f0, i) == f0.t;
            assert(pkey(f, i) == v && ptype(f, i) == f.t);
        }
    }
}

/// The part filter with its coarse padding bit (`pad_ok`): coarse word `ceil(nbits / 512)` is cleared (or appended)
/// and `clamp` is `512` times its index, the first key offset no set fine bit reaches.
pub fn pad_filter(f: PFilter) -> (g: PFilter)
    requires pf_ok(f),
    ensures
        pf_ok(g), pad_ok(g), same_base(g, f),
        g.use_bits == f.use_bits, g.bits == f.bits, g.nbits == f.nbits, g.pk_lo == f.pk_lo,
{
    let mut g = f;
    if !g.use_bits {
        return g;
    }
    let ghost c0 = g.coarse@;
    let ghost nb = g.nbits as int;
    let len = g.coarse.len();
    let w: usize = ((g.nbits + 511) / 512) as usize;
    proof {
        // ceil(nbits / 512) words cover every key offset below nbits, and the coarse bitmap has at least that many.
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(nb + 511, 512);
        assert(w * 512 >= nb);
        vstd::arithmetic::div_mod::lemma_div_is_ordered(nb + 511, len * 512 + 511, 512);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(len * 512 + 511, 512, len as int, 511);
        assert(w <= len);
    }
    if w < len {
        g.coarse.set(w, 0u64);
    } else {
        g.coarse.push(0u64);
    }
    g.clamp = (w as u64) * 512;
    proof {
        let c1 = g.coarse@;
        assert(c1.len() > w && c1[w as int] == 0u64);
        assert forall|k: int| 0 <= k < w implies #[trigger] c1[k] == c0[k] by {}
        assert forall|i: int| 0 <= i < g.nbits && #[trigger] bit_at(g.bits@, i) implies bit_at(g.coarse@, i / 8) by {
            assert(bit_at(c0, i / 8));
            vstd::arithmetic::div_mod::lemma_div_denominator(i, 8, 64);
            vstd::arithmetic::div_mod::lemma_div_is_ordered(i, w * 512 - 1, 512);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(w * 512 - 1, 512, w - 1, 511);
            assert((i / 8) / 64 < w);
        }
        assert(g.clamp as int / 8 == w * 64);
        assert((w * 64) / 64 == w as int) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(w * 64, 64, w as int, 0);
        }
        assert((w * 64) % 64 == 0) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(w * 64, 64, w as int, 0);
        }
        assert(((0u64 >> 0u64) & 1u64) == 0u64) by (bit_vector);
        assert(!bit_at(g.coarse@, g.clamp as int / 8));
        assert(g.coarse@.len() * 512 >= g.nbits);
        assert(g.coarse@.len() >= 1);
        assert(pf_shape(f));
        lemma_same_base(g, f);
        assert forall|i: int| 0 <= i < g.nbits implies #[trigger] bit_at(g.bits@, i) == pmatch(g, g.pk_lo + i) by {
            assert(bit_at(f.bits@, i) == pmatch(f, f.pk_lo + i));
        }
        assert forall|v: int| #[trigger] pmatch(g, v) implies g.pk_lo <= v < g.pk_lo + g.nbits by {
            assert(pmatch(f, v));
        }
        assert forall|i: int| 0 <= i < g.n_p implies in_i64(#[trigger] pkey(g, i)) by {
            assert(pkey(g, i) == pkey(f, i));
        }
        assert forall|a: int, b: int| 0 <= a < g.n_p && 0 <= b < g.n_p && a != b
            implies #[trigger] pkey(g, a) != #[trigger] pkey(g, b) by {
            assert(pkey(g, a) == pkey(f, a) && pkey(g, b) == pkey(f, b));
        }
    }
    g
}

/// A copy of the part filter's fields other than its bitmaps.
pub fn base_copy(f0: &PFilter) -> (f: PFilter)
    ensures same_base(f, *f0), !f.use_bits,
{
    PFilter {
        use_bits: false, bits: Vec::new(), coarse: Vec::new(), nbits: 0, clamp: 0, pk_lo: 0,
        n_p: f0.n_p, bs_p: f0.bs_p, pk_c: f0.pk_c, pk_b: f0.pk_b, pt_c: f0.pt_c, pt_b: f0.pt_b, p_kind: f0.p_kind,
        t: f0.t, has_t: f0.has_t, e32: f0.e32, e64: f0.e64,
    }
}

/// The part filter's bitmaps from the keys of the matching parts, on the calling thread.
pub fn pfilter_serial(f0: &PFilter) -> (f: PFilter)
    requires pf_shape(*f0),
    ensures same_base(f, *f0), pf_ok(f),
{
    let ghost old_f0 = *f0;
    let f0 = base_copy(f0);
    let n_p = f0.n_p;
    proof { lemma_same_base(f0, old_f0); }
    let (keys, lo, hi, Ghost(gi)) = match_keys(&f0);
    proof {
        if keys@.len() > 0 {
            assert(0 <= gi[0] < n_p);
            assert(lo <= keys@[0] <= hi);
        }
    }
    let (use_bits, nbits, pk_lo): (bool, u64, i64) = if keys.len() == 0 {
        (true, 1, 0)
    } else if (hi as i128 - lo as i128) < 0x1_0000_0000 {
        (true, (hi as i128 - lo as i128 + 1) as u64, lo)
    } else {
        (false, 0, 0)
    };
    let (bits, coarse) = if use_bits {
        if keys.len() == 0 {
            let b = zeros(1);
            let c = zeros(1);
            (b, c)
        } else {
            proof {
                assert forall|q: int| 0 <= q < keys@.len() implies pk_lo <= #[trigger] keys@[q] < pk_lo + nbits by {
                    assert(0 <= gi[q] < n_p);
                }
            }
            build_bits(&keys, pk_lo, nbits)
        }
    } else {
        (Vec::new(), Vec::new())
    };
    let f = PFilter {
        use_bits, bits, coarse, nbits, clamp: 0, pk_lo,
        n_p: f0.n_p, bs_p: f0.bs_p, pk_c: f0.pk_c, pk_b: f0.pk_b, pt_c: f0.pt_c, pt_b: f0.pt_b, p_kind: f0.p_kind,
        t: f0.t, has_t: f0.has_t, e32: f0.e32, e64: f0.e64,
    };
    proof {
        assert forall|v: int| #[trigger] pmatch(f, v) <==> pmatch(f0, v) by {
            if pmatch(f, v) {
                let i = choose|i: int| 0 <= i < f.n_p && #[trigger] pkey(f, i) == v && ptype(f, i) == f.t;
                assert(pkey(f0, i) == v && ptype(f0, i) == f0.t);
            }
            if pmatch(f0, v) {
                let i = choose|i: int| 0 <= i < f0.n_p && #[trigger] pkey(f0, i) == v && ptype(f0, i) == f0.t;
                assert(pkey(f, i) == v && ptype(f, i) == f.t);
            }
        }
        // A matching part's key is a listed key.
        assert forall|v: int| #[trigger] pmatch(f, v) implies exists|q: int| 0 <= q < keys@.len() && keys@[q] as int == v by {
            let i = choose|i: int| 0 <= i < f0.n_p && #[trigger] pkey(f0, i) == v && ptype(f0, i) == f0.t;
            assert(mrow(f0, i));
            let q = choose|q: int| 0 <= q < gi.len() && gi[q] == i;
            assert(keys@[q] as int == v);
        }
        if use_bits {
            if keys.len() == 0 {
                lemma_zero_bits(f.bits@, 0);
                assert forall|v: int| #[trigger] pmatch(f, v) implies f.pk_lo <= v < f.pk_lo + f.nbits by {
                    let q = choose|q: int| 0 <= q < keys@.len() && keys@[q] as int == v;
                }
                assert forall|i: int| 0 <= i < f.nbits implies #[trigger] bit_at(f.bits@, i) == pmatch(f, f.pk_lo + i) by {
                    if pmatch(f, f.pk_lo + i) {
                        let q = choose|q: int| 0 <= q < keys@.len() && keys@[q] as int == f.pk_lo + i;
                    }
                }
                assert forall|i: int| 0 <= i < f.nbits && #[trigger] bit_at(f.bits@, i) implies bit_at(f.coarse@, i / 8) by {
                    lemma_zero_bits(f.bits@, i);
                }
            } else {
                assert forall|v: int| #[trigger] pmatch(f, v) implies f.pk_lo <= v < f.pk_lo + f.nbits by {
                    let q = choose|q: int| 0 <= q < keys@.len() && keys@[q] as int == v;
                    assert(lo <= keys@[q] <= hi);
                }
                assert forall|i: int| 0 <= i < f.nbits implies #[trigger] bit_at(f.bits@, i) == pmatch(f, f.pk_lo + i) by {
                    if key_hit(keys@, keys@.len() as int, lo as int, i) {
                        let q = choose|q: int| 0 <= q < keys@.len() && #[trigger] keys@[q] as int == lo + i;
                        assert(mrow(f0, gi[q]));
                        assert(pkey(f0, gi[q]) == lo + i);
                    }
                    if pmatch(f, f.pk_lo + i) {
                        let q = choose|q: int| 0 <= q < keys@.len() && keys@[q] as int == f.pk_lo + i;
                        assert(key_hit(keys@, keys@.len() as int, lo as int, i));
                    }
                }
            }
        }
        assert forall|i: int| 0 <= i < f.n_p implies in_i64(#[trigger] pkey(f, i)) by {
            assert(pkey(f, i) == pkey(f0, i));
        }
        assert forall|a: int, b: int| 0 <= a < f.n_p && 0 <= b < f.n_p && a != b
            implies #[trigger] pkey(f, a) != #[trigger] pkey(f, b) by {
            assert(pkey(f, a) == pkey(f0, a) && pkey(f, b) == pkey(f0, b));
        }
        assert(pf_shape(f));
    }
    f
}

// ------------------------------------------------------------------------------------------------ nation statuses

/// `n` false values.
fn falses(n: usize) -> (v: Vec<bool>)
    ensures v@.len() == n, forall|i: int| 0 <= i < n ==> !#[trigger] v@[i],
{
    let mut v: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n, v@.len() == i, forall|k: int| 0 <= k < i ==> !#[trigger] v@[k],
        decreases n - i,
    {
        v.push(false);
        i = i + 1;
    }
    v
}

/// Byte equality of two texts.
fn text_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures r == (a@ == b@),
{
    let c = crate::stores::suppliers::interface::common::read::bytes_cmp(a, a.len(), b, b.len());
    proof { crate::bridge::equality::lemma_lex_cmp_zero(a@, b@); }
    c == 0
}

/// Nation row `k`'s key, whether its name is `$1` and whether its region is named `$2`.
pub open spec fn nrow_ok(sv: StoresView, ps: Seq<Literal>, keys: Seq<i64>, rreg: Seq<bool>, rname: Seq<bool>, k: int) -> bool {
    &&& keys[k] as int == nkey_at(sv, k)
    &&& rname[k] == (nname_at(sv, k) == txt(ps[0]))
    &&& rreg[k] == reg_named(sv, nrkey_at(sv, k), txt(ps[1]))
}

/// The nation statuses for `$1` (nation name) and `$2` (region name).
pub fn build_ntab(sp: &mut StoredParts, p0: &'static [u8], p1: &'static [u8], Ghost(sv): Ghost<StoresView>,
    Ghost(db): Ghost<Database>, Ghost(ps): Ghost<Seq<Literal>>) -> (nt: NTab)
    requires old(sp)@ == sv.suppliers, bound_db(sv, db), ps.len() == 3, txt(ps[0]) == p0@, txt(ps[1]) == p1@,
    ensures final(sp)@ == old(sp)@, ntab_from(sv, ps, nt), ntab_ok(nt),
{
    proof {
        lemma_tables(sv, db);
        lemma_nr_rows(sv, db);
    }
    let nf = si::NATION_FIRST;
    let rf = si::REGION_FIRST;
    let n_n = sp.part_len(nf + si::NA_NATIONKEY_CODES);
    let bs_n = block_rows(sp, nf + si::NA_LAYOUT, n_n);
    let nk_c = whole_u8(sp, nf + si::NA_NATIONKEY_CODES);
    let nk_b = whole_i64(sp, nf + si::NA_NATIONKEY_BASE);
    let nr_c = whole_u8(sp, nf + si::NA_REGIONKEY_CODES);
    let nr_b = whole_i64(sp, nf + si::NA_REGIONKEY_BASE);
    let nn_o = whole_u64(sp, nf + si::NA_NAME_OFFS);
    let nn_b = whole_u8(sp, nf + si::NA_NAME_BYTES);
    let n_r = sp.part_len(rf + si::RE_REGIONKEY_CODES);
    let bs_r = block_rows(sp, rf + si::RE_LAYOUT, n_r);
    let rk_c = whole_u8(sp, rf + si::RE_REGIONKEY_CODES);
    let rk_b = whole_i64(sp, rf + si::RE_REGIONKEY_BASE);
    let rn_o = whole_u64(sp, rf + si::RE_NAME_OFFS);
    let rn_b = whole_u8(sp, rf + si::RE_NAME_BYTES);
    let ghost na = na_tp(sv);
    let ghost re = re_tp(sv);
    proof {
        lemma_sbases(na, n_n as int, bs_n as int, si::NA_NATIONKEY_BASE as int);
        lemma_sbases(na, n_n as int, bs_n as int, si::NA_REGIONKEY_BASE as int);
        lemma_sbases(re, n_r as int, bs_r as int, si::RE_REGIONKEY_BASE as int);
    }
    // Region rows named `$2`, by key.
    let mut keys: Vec<i64> = Vec::new();
    let mut rreg: Vec<bool> = Vec::new();
    let mut rname: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n_n
        invariant
            i <= n_n, n_n == n_nat(sv), n_r == n_reg(sv),
            bound_db(sv, db), ps.len() == 3, txt(ps[0]) == p0@, txt(ps[1]) == p1@,
            na == na_tp(sv), re == re_tp(sv),
            nk_c@ == sc::u8s(na[si::NA_NATIONKEY_CODES as int]), nk_b@ == sc::i64s(na[si::NA_NATIONKEY_BASE as int]),
            nr_c@ == sc::u8s(na[si::NA_REGIONKEY_CODES as int]), nr_b@ == sc::i64s(na[si::NA_REGIONKEY_BASE as int]),
            nn_o@ == sc::u64s(na[si::NA_NAME_OFFS as int]), nn_b@ == sc::u8s(na[si::NA_NAME_BYTES as int]),
            rk_c@ == sc::u8s(re[si::RE_REGIONKEY_CODES as int]), rk_b@ == sc::i64s(re[si::RE_REGIONKEY_BASE as int]),
            rn_o@ == sc::u64s(re[si::RE_NAME_OFFS as int]), rn_b@ == sc::u8s(re[si::RE_NAME_BYTES as int]),
            bs_ok(bs_n as int, sc::u64s(na[0])[1] as int, n_n as int), bs_ok(bs_r as int, sc::u64s(re[0])[1] as int, n_r as int),
            nk_b@.len() * bs_n >= n_n, nr_b@.len() * bs_n >= n_n, rk_b@.len() * bs_r >= n_r,
            keys@.len() == i, rreg@.len() == i, rname@.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] nrow_ok(sv, ps, keys@, rreg@, rname@, k),
        decreases n_n - i,
    {
        proof {
            lemma_tables(sv, db);
            lemma_nr_rows(sv, db);
            lemma_sfor(na, n_n as int, bs_n as int, si::NA_NATIONKEY_BASE as int, si::NA_NATIONKEY_CODES as int, i as int);
            lemma_sfor(na, n_n as int, bs_n as int, si::NA_REGIONKEY_BASE as int, si::NA_REGIONKEY_CODES as int, i as int);
            crate::stores::suppliers::interface::common::read::lemma_div_lt(i as int, bs_n as int, nk_b@.len() as int);
            crate::stores::suppliers::interface::common::read::lemma_div_lt(i as int, bs_n as int, nr_b@.len() as int);
            assert(sc::text_range_ok(nn_o@, nn_b@, i as int));
            let g = i as int / bs_n as int;
            assert(na[si::NA_NATIONKEY_BASE as int] is I64 && na[si::NA_NATIONKEY_CODES as int] is U8);
            assert(na[si::NA_REGIONKEY_BASE as int] is I64 && na[si::NA_REGIONKEY_CODES as int] is U8);
            assert(nkey_at(sv, i as int) == nk_b@[g] + nk_c@[i as int]);
            assert(nrkey_at(sv, i as int) == nr_b@[g] + nr_c@[i as int]);
            assert(db.tables[6][i as int][0] == Val::Int(nkey_at(sv, i as int)));
            assert(in_i64(nkey_at(sv, i as int)) && in_i64(nrkey_at(sv, i as int)));
        }
        let key = nk_b[i / bs_n] + nk_c[i] as i64;
        let rkey = nr_b[i / bs_n] + nr_c[i] as i64;
        let nm = text_eq(crate::stores::suppliers::interface::common::read::text_slice(nn_o, nn_b, i), p0);
        let mut reg = false;
        let mut r: usize = 0;
        while r < n_r
            invariant
                r <= n_r, n_n == n_nat(sv), n_r == n_reg(sv), i < n_n,
                bound_db(sv, db), ps.len() == 3, txt(ps[0]) == p0@, txt(ps[1]) == p1@,
                na == na_tp(sv), re == re_tp(sv),
                rk_c@ == sc::u8s(re[si::RE_REGIONKEY_CODES as int]), rk_b@ == sc::i64s(re[si::RE_REGIONKEY_BASE as int]),
                rn_o@ == sc::u64s(re[si::RE_NAME_OFFS as int]), rn_b@ == sc::u8s(re[si::RE_NAME_BYTES as int]),
                bs_ok(bs_r as int, sc::u64s(re[0])[1] as int, n_r as int),
                rk_b@.len() * bs_r >= n_r,
                rkey as int == nrkey_at(sv, i as int),
                key as int == nkey_at(sv, i as int),
                nm == (nname_at(sv, i as int) == txt(ps[0])),
                keys@.len() == i, rreg@.len() == i, rname@.len() == i,
                forall|k: int| 0 <= k < i ==> #[trigger] nrow_ok(sv, ps, keys@, rreg@, rname@, k),
                reg == exists|r2: int| 0 <= r2 < r && #[trigger] rkey_at(sv, r2) == rkey as int && rname_at(sv, r2) == p1@,
            decreases n_r - r,
        {
            proof {
                lemma_tables(sv, db);
                lemma_nr_rows(sv, db);
                lemma_sfor(re, n_r as int, bs_r as int, si::RE_REGIONKEY_BASE as int, si::RE_REGIONKEY_CODES as int, r as int);
                crate::stores::suppliers::interface::common::read::lemma_div_lt(r as int, bs_r as int, rk_b@.len() as int);
                assert(sc::text_range_ok(rn_o@, rn_b@, r as int));
                assert(re[si::RE_REGIONKEY_BASE as int] is I64 && re[si::RE_REGIONKEY_CODES as int] is U8);
                assert(rkey_at(sv, r as int) == rk_b@[r as int / bs_r as int] + rk_c@[r as int]);
                assert(db.tables[7][r as int][0] == Val::Int(rkey_at(sv, r as int)));
                assert(in_i64(rkey_at(sv, r as int)));
            }
            let rk = rk_b[r / bs_r] + rk_c[r] as i64;
            if rk == rkey && text_eq(crate::stores::suppliers::interface::common::read::text_slice(rn_o, rn_b, r), p1) {
                reg = true;
            }
            proof {
                if rk == rkey && rname_at(sv, r as int) == p1@ {
                    assert(rkey_at(sv, r as int) == rkey as int);
                }
                if !(rk == rkey && rname_at(sv, r as int) == p1@) {
                    assert forall|r2: int| 0 <= r2 < r + 1 && #[trigger] rkey_at(sv, r2) == rkey as int && rname_at(sv, r2) == p1@
                        implies r2 < r by {}
                }
            }
            r = r + 1;
        }
        proof {
            assert(reg == exists|r2: int| 0 <= r2 < n_reg(sv) && #[trigger] rkey_at(sv, r2) == rkey as int && rname_at(sv, r2) == p1@);
            if reg {
                let r2 = choose|r2: int| 0 <= r2 < n_reg(sv) && #[trigger] rkey_at(sv, r2) == rkey as int && rname_at(sv, r2) == p1@;
                assert(rkey_at(sv, r2) == nrkey_at(sv, i as int) && rname_at(sv, r2) == txt(ps[1]));
            }
            if reg_named(sv, nrkey_at(sv, i as int), txt(ps[1])) {
                let r2 = choose|r2: int| 0 <= r2 < n_reg(sv) && #[trigger] rkey_at(sv, r2) == nrkey_at(sv, i as int)
                    && rname_at(sv, r2) == txt(ps[1]);
                assert(rkey_at(sv, r2) == rkey as int && rname_at(sv, r2) == p1@);
            }
        }
        let ghost ok = keys@;
        let ghost orr = rreg@;
        let ghost orn = rname@;
        keys.push(key);
        rreg.push(reg);
        rname.push(nm);
        proof {
            assert(reg == reg_named(sv, nrkey_at(sv, i as int), txt(ps[1])));
            assert forall|k: int| 0 <= k < i + 1 implies #[trigger] nrow_ok(sv, ps, keys@, rreg@, rname@, k) by {
                if k == i {
                    assert(keys@[k] == key && rname@[k] == nm && rreg@[k] == reg);
                } else {
                    assert(nrow_ok(sv, ps, ok, orr, orn, k));
                    assert(keys@[k] == ok[k] && rname@[k] == orn[k] && rreg@[k] == orr[k]);
                }
            }
        }
        i = i + 1;
    }
    // Statuses by key below `NK`.
    let mut ex = falses(NK);
    let mut kreg = falses(NK);
    let mut kname = falses(NK);
    let ghost ns = NStat { keys: keys@, reg: rreg@, name: rname@ };
    proof {
        lemma_nr_rows(sv, db);
        assert forall|i: int| 0 <= i < n_nat(sv) implies {
            &&& #[trigger] keys@[i] as int == nkey_at(sv, i)
            &&& rname@[i] == (nname_at(sv, i) == txt(ps[0]))
            &&& rreg@[i] == reg_named(sv, nrkey_at(sv, i), txt(ps[1]))
        } by {
            assert(nrow_ok(sv, ps, keys@, rreg@, rname@, i));
        }
        assert forall|a: int, b: int| 0 <= a < ns.keys.len() && 0 <= b < ns.keys.len() && a != b
            implies #[trigger] ns.keys[a] != #[trigger] ns.keys[b] by {
            assert(nrow_ok(sv, ps, keys@, rreg@, rname@, a));
            assert(nrow_ok(sv, ps, keys@, rreg@, rname@, b));
            assert(nkey_at(sv, a) != nkey_at(sv, b));
        }
    }
    let mut q: usize = 0;
    while q < n_n
        invariant
            q <= n_n, keys@.len() == n_n, rreg@.len() == n_n, rname@.len() == n_n,
            n_n == n_nat(sv),
            forall|k: int| 0 <= k < n_n ==> #[trigger] nrow_ok(sv, ps, keys@, rreg@, rname@, k),
            ns == (NStat { keys: keys@, reg: rreg@, name: rname@ }),
            nstat_wf(ns),
            ex@.len() == NK && kreg@.len() == NK && kname@.len() == NK,
            forall|k: int| 0 <= k < NK ==> (#[trigger] ex@[k] == exists|x: int| 0 <= x < q && #[trigger] keys@[x] == k),
            forall|x: int| 0 <= x < q && 0 <= #[trigger] keys@[x] < NK ==> kreg@[keys@[x] as int] == rreg@[x]
                && kname@[keys@[x] as int] == rname@[x],
            forall|k: int| 0 <= k < NK && !#[trigger] ex@[k] ==> !kreg@[k] && !kname@[k],
        decreases n_n - q,
    {
        let key = keys[q];
        if 0 <= key && key < NK as i64 {
            let kk = key as usize;
            ex.set(kk, true);
            kreg.set(kk, rreg[q]);
            kname.set(kk, rname[q]);
        }
        proof {
            assert forall|k: int| 0 <= k < NK implies (#[trigger] ex@[k] == exists|x: int| 0 <= x < q + 1 && #[trigger] keys@[x] == k) by {
                if exists|x: int| 0 <= x < q + 1 && #[trigger] keys@[x] == k {
                    let x = choose|x: int| 0 <= x < q + 1 && #[trigger] keys@[x] == k;
                    if x < q {
                        assert(exists|x2: int| 0 <= x2 < q && #[trigger] keys@[x2] == k);
                    }
                }
                if exists|x: int| 0 <= x < q && #[trigger] keys@[x] == k {
                    let x = choose|x: int| 0 <= x < q && #[trigger] keys@[x] == k;
                    assert(0 <= x < q + 1 && keys@[x] == k);
                }
            }
            assert forall|x: int| 0 <= x < q + 1 && 0 <= #[trigger] keys@[x] < NK
                implies kreg@[keys@[x] as int] == rreg@[x] && kname@[keys@[x] as int] == rname@[x] by {
                if x < q && keys@[x] == key {
                    assert(keys@[x] == keys@[q as int]);
                    assert(x == q);
                }
            }
        }
        q = q + 1;
    }
    proof {
        assert forall|i: int| 0 <= i < n_nat(sv) implies {
            &&& #[trigger] keys@[i] as int == nkey_at(sv, i)
            &&& rname@[i] == (nname_at(sv, i) == txt(ps[0]))
            &&& rreg@[i] == reg_named(sv, nrkey_at(sv, i), txt(ps[1]))
        } by {
            assert(nrow_ok(sv, ps, keys@, rreg@, rname@, i));
        }
    }
    let nt = NTab { ex, reg: kreg, name: kname, keys, rreg, rname, cbits: Vec::new() };
    proof {
        assert(ntab_from(sv, ps, nt));
        assert(nt_view(nt) == ns);
        assert forall|k: int| #![trigger nt.ex@[k]] #![trigger nt.reg@[k]] #![trigger nt.name@[k]]
            0 <= k < NK implies nt.ex@[k] == nfind(ns, k) is Some
            && nt.reg@[k] == nreg(ns, k) && nt.name@[k] == nname(ns, k) by {
            if exists|i: int| 0 <= i < ns.keys.len() && #[trigger] ns.keys[i] == k {
                let i = choose|i: int| 0 <= i < ns.keys.len() && #[trigger] ns.keys[i] == k;
                assert(keys@[i] == k);
                assert(nfind(ns, k) == Some(i));
                assert(0 <= keys@[i] < NK);
                assert(ex@[k]);
                assert(kreg@[keys@[i] as int] == rreg@[i]);
                assert(nreg(ns, k) == ns.reg[i]);
                assert(nname(ns, k) == ns.name[i]);
            } else {
                assert(!(exists|x: int| 0 <= x < n_n && #[trigger] keys@[x] == k));
                assert(nfind(ns, k) is None);
                assert(!ex@[k]);
            }
        }
    }
    nt
}

} // verus!
