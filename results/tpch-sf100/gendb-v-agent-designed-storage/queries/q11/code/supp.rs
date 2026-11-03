//! Which suppliers qualify: the nation keys named `$1` (`nation_keys`), then one flag byte per supplier key value
//! in `smin .. smin + range` (`supplier_flags`): `fl[k - smin] != 0` exactly when some supplier with key `k` is
//! in a nation named `$1` (`flags_ok`). One extra zero byte at `fl[range]` lets the scan map every out-of-range
//! key to a non-qualifying slot without a branch.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::link::expr::ival;
use super::tables::*;
use super::nf::*;

verus! {

/// The nation key values `nk` are exactly those of nations named `name`.
pub open spec fn nkeys_ok(t: Tabs, name: Seq<u8>, nk: Seq<i64>) -> bool {
    forall|v: i64| #[trigger] nk.contains(v) <==> nq(t, name, Val::Int(v as int))
}

/// The flag bytes of the supplier key values `smin .. smin + range` (plus a zero sentinel).
pub open spec fn flags_ok(t: Tabs, name: Seq<u8>, fl: Seq<u8>, smin: int, range: int) -> bool {
    &&& fl.len() == range + 1
    &&& fl[range] == 0
    &&& forall|i: int| 0 <= i < range ==> (#[trigger] fl[i] != 0 <==> sq(t, name, Val::Int(smin + i)))
    &&& forall|i: int| 0 <= i <= range ==> #[trigger] fl[i] <= 1
    &&& forall|v: int| #[trigger] sq(t, name, Val::Int(v)) ==> smin <= v < smin + range
}

/// `a[lo .. hi]` equals `b`.
fn bytes_eq(a: &[u8], lo: usize, hi: usize, b: &[u8]) -> (r: bool)
    requires lo <= hi <= a@.len(),
    ensures r == (a@.subrange(lo as int, hi as int) == b@),
{
    let n = b.len();
    if hi - lo != n {
        return false;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            n == b@.len(), hi - lo == n, lo <= hi <= a@.len(), i <= n,
            forall|j: int| 0 <= j < i ==> a@[lo + j] == b@[j],
        decreases n - i,
    {
        if a[lo + i] != b[i] {
            assert(a@.subrange(lo as int, hi as int)[i as int] != b@[i as int]);
            return false;
        }
        i = i + 1;
    }
    assert(a@.subrange(lo as int, hi as int) =~= b@);
    true
}

/// The key values of the nations named `name`.
pub fn nation_keys(c: &NCols, name: &[u8], Ghost(t): Ghost<Tabs>) -> (nk: Vec<i64>)
    requires ncols_ok(*c, t.n), tabs_typed(t),
    ensures nkeys_ok(t, name@, nk@),
{
    let mut nk: Vec<i64> = Vec::new();
    let mut q: usize = 0;
    while q < c.n
        invariant
            ncols_ok(*c, t.n), tabs_typed(t), q <= c.n,
            forall|v: i64| #[trigger] nk@.contains(v) <==>
                exists|q2: int| 0 <= q2 < q && #[trigger] t.n[q2][0] == Val::Int(v as int) && t.n[q2][1] == Val::Text(name@),
        decreases c.n - q,
    {
        assert(nat_row_ok(*c, t.n[q as int], q as int));
        assert(n_typed(t.n[q as int]));
        proof { lemma_grp_bound(c.n as int, c.bs as int, c.ng as int, q as int); }
        let a = c.name_o[q];
        let b = c.name_o[q + 1];
        assert(c.name_o@[q as int] <= c.name_o@[q + 1] && c.name_o@[q + 1] <= c.name_y@.len());
        let ylen = c.name_y.len();
        assert(c.name_y@.len() <= usize::MAX);
        let a2 = a as usize;
        let b2 = b as usize;
        assert(a2 == a && b2 == b);
        let hit = bytes_eq(c.name_y, a2, b2, name);
        let ghost old_nk = nk@;
        if hit {
            let v: i64 = c.key_b[q / c.bs] + c.key_c[q] as i64;
            nk.push(v);
            proof {
                assert(t.n[q as int][0] == Val::Int(v as int));
                assert(t.n[q as int][1] == Val::Text(name@));
                assert(nk@ == old_nk.push(v));
                lemma_push_contains(old_nk, v);
                assert forall|w: i64| #[trigger] nk@.contains(w) <==>
                    exists|q2: int| 0 <= q2 < q + 1 && #[trigger] t.n[q2][0] == Val::Int(w as int) && t.n[q2][1] == Val::Text(name@) by {
                    if nk@.contains(w) {
                        let i = choose|i: int| 0 <= i < nk@.len() && nk@[i] == w;
                        if i < old_nk.len() {
                            assert(old_nk.contains(w));
                        } else {
                            assert(t.n[q as int][0] == Val::Int(w as int));
                        }
                    }
                    if exists|q2: int| 0 <= q2 < q + 1 && #[trigger] t.n[q2][0] == Val::Int(w as int) && t.n[q2][1] == Val::Text(name@) {
                        let q2 = choose|q2: int| 0 <= q2 < q + 1 && #[trigger] t.n[q2][0] == Val::Int(w as int) && t.n[q2][1] == Val::Text(name@);
                        if q2 < q {
                            assert(old_nk.contains(w));
                            let i = choose|i: int| 0 <= i < old_nk.len() && old_nk[i] == w;
                            assert(nk@[i] == w);
                        } else {
                            assert(nk@[old_nk.len() as int] == w);
                        }
                    }
                }
            }
        } else {
            proof {
                assert forall|w: i64| #[trigger] nk@.contains(w) <==>
                    exists|q2: int| 0 <= q2 < q + 1 && #[trigger] t.n[q2][0] == Val::Int(w as int) && t.n[q2][1] == Val::Text(name@) by {
                    if exists|q2: int| 0 <= q2 < q + 1 && #[trigger] t.n[q2][0] == Val::Int(w as int) && t.n[q2][1] == Val::Text(name@) {
                        let q2 = choose|q2: int| 0 <= q2 < q + 1 && #[trigger] t.n[q2][0] == Val::Int(w as int) && t.n[q2][1] == Val::Text(name@);
                        if q2 == q {
                            assert(txt(c.name_o@, c.name_y@, q as int) != name@);
                        }
                    }
                }
            }
        }
        q = q + 1;
    }
    proof {
        assert forall|v: i64| #[trigger] nk@.contains(v) <==> nq(t, name@, Val::Int(v as int)) by {
            if nq(t, name@, Val::Int(v as int)) {
                let q2 = choose|q2: int| 0 <= q2 < t.n.len() && #[trigger] t.n[q2][0] == Val::Int(v as int) && t.n[q2][1] == Val::Text(name@);
            }
        }
    }
    nk
}

/// Membership after a push.
proof fn lemma_push_contains(s: Seq<i64>, v: i64)
    ensures forall|w: i64| #[trigger] s.push(v).contains(w) <==> (s.contains(w) || w == v),
{
    assert forall|w: i64| #[trigger] s.push(v).contains(w) <==> (s.contains(w) || w == v) by {
        if s.push(v).contains(w) {
            let i = choose|i: int| 0 <= i < s.push(v).len() && s.push(v)[i] == w;
            if i < s.len() {
                assert(s[i] == w);
            }
        }
        if s.contains(w) {
            let i = choose|i: int| 0 <= i < s.len() && s[i] == w;
            assert(s.push(v)[i] == w);
        }
        if w == v {
            assert(s.push(v)[s.len() as int] == w);
        }
    }
}

/// `v` is one of the keys `nk`.
pub fn contains_key(nk: &Vec<i64>, v: i64) -> (r: bool)
    ensures r == nk@.contains(v),
{
    let n = nk.len();
    let mut i: usize = 0;
    while i < n
        invariant n == nk@.len(), i <= n, forall|j: int| 0 <= j < i ==> nk@[j] != v,
        decreases n - i,
    {
        if nk[i] == v {
            return true;
        }
        i = i + 1;
    }
    false
}

/// The end of the frame-of-reference group holding row `r` (rows `r .. end` share its bases), capped at `n`.
fn group_end(r: usize, bs: usize, n: usize) -> (e: usize)
    requires bs >= 1, r < n,
    ensures r < e <= n, (r / bs) * bs <= r, e <= (r / bs) * bs + bs,
        forall|x: int| r <= x < e ==> #[trigger] (x / bs as int) == r / bs,
{
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(r as int, bs as int);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(r as int, bs as int);
        assert((bs as int) * ((r / bs) as int) == ((r / bs) as int) * (bs as int)) by (nonlinear_arith);
    }
    let e = if n - r > bs - r % bs { r + (bs - r % bs) } else { n };
    proof {
        let g = (r / bs) as int;
        assert forall|x: int| r <= x < e implies #[trigger] (x / bs as int) == g by {
            super::tables::lemma_in_group(bs as int, g, x);
        }
    }
    e
}

/// The smallest and largest supplier key value (`(0, -1)` for no supplier).
pub fn supplier_key_range(c: &SCols, Ghost(t): Ghost<Tabs>) -> (r: (i64, i64))
    requires scols_ok(*c, t.s),
    ensures
        forall|j: int| 0 <= j < t.s.len() ==> r.0 <= #[trigger] ival(t.s[j][0]) <= r.1,
        t.s.len() == 0 ==> r.0 == 0 && r.1 == -1,
        t.s.len() > 0 ==> r.0 <= r.1,
{
    if c.n == 0 {
        return (0, -1);
    }
    let mut lo: i64 = i64::MAX;
    let mut hi: i64 = i64::MIN;
    let mut j: usize = 0;
    while j < c.n
        invariant
            scols_ok(*c, t.s), j <= c.n, c.n > 0,
            j > 0 ==> lo <= hi,
            forall|j2: int| 0 <= j2 < j ==> lo <= #[trigger] ival(t.s[j2][0]) <= hi,
        decreases c.n - j,
    {
        // One frame-of-reference group: rows j .. gend share the key base.
        let gend = group_end(j, c.bs, c.n);
        let g = j / c.bs;
        proof { lemma_grp_bound(c.n as int, c.bs as int, c.ng as int, j as int); }
        let kb = c.key_b[g];
        while j < gend
            invariant
                scols_ok(*c, t.s), j <= gend <= c.n, c.n > 0, g < c.ng, kb == c.key_b@[g as int],
                forall|x: int| j <= x < gend ==> #[trigger] (x / c.bs as int) == g,
                j > 0 ==> lo <= hi,
                forall|j2: int| 0 <= j2 < j ==> lo <= #[trigger] ival(t.s[j2][0]) <= hi,
            decreases gend - j,
        {
            assert(supp_row_ok(*c, t.s[j as int], j as int));
            assert(j as int / c.bs as int == g);
            let k: i64 = kb + c.key_c[j] as i64;
            if k < lo { lo = k; }
            if k > hi { hi = k; }
            j = j + 1;
        }
    }
    (lo, hi)
}

/// Which nation codes of one group qualify: `tbl[x]` exactly when `nb + x` is one of the keys `nk`.
fn nation_code_table(nk: &Vec<i64>, nb: i64) -> (tbl: Vec<bool>)
    ensures tbl@.len() == 256,
        forall|x: int| 0 <= x < 256 && nb + x <= i64::MAX ==> #[trigger] tbl@[x] == nk@.contains((nb + x) as i64),
{
    let mut tbl: Vec<bool> = Vec::with_capacity(256);
    let mut x: i64 = 0;
    while x < 256
        invariant 0 <= x <= 256, tbl@.len() == x,
            forall|y: int| 0 <= y < x && nb + y <= i64::MAX ==> #[trigger] tbl@[y] == nk@.contains((nb + y) as i64),
        decreases 256 - x,
    {
        let v: i128 = nb as i128 + x as i128;
        let q = if v <= i64::MAX as i128 { contains_key(nk, v as i64) } else { false };
        tbl.push(q);
        x = x + 1;
    }
    tbl
}

/// The flag bytes of the qualifying suppliers over the key values `smin .. smin + range`.
pub fn supplier_flags(c: &SCols, nk: &Vec<i64>, smin: i64, range: usize, Ghost(t): Ghost<Tabs>, Ghost(name): Ghost<Seq<u8>>)
    -> (fl: Vec<u8>)
    requires
        scols_ok(*c, t.s), tabs_typed(t), nkeys_ok(t, name, nk@),
        range < usize::MAX,
        forall|j: int| 0 <= j < t.s.len() ==> smin <= #[trigger] ival(t.s[j][0]) < smin + range,
    ensures flags_ok(t, name, fl@, smin as int, range as int),
{
    let mut fl: Vec<u8> = vec![0u8; range + 1];
    proof {
        assert forall|i: int| 0 <= i < fl@.len() implies #[trigger] fl@[i] == 0 by {}
    }
    let mut j: usize = 0;
    while j < c.n
        invariant
            scols_ok(*c, t.s), tabs_typed(t), nkeys_ok(t, name, nk@), j <= c.n,
            forall|j2: int| 0 <= j2 < t.s.len() ==> smin <= #[trigger] ival(t.s[j2][0]) < smin + range,
            fl@.len() == range + 1, fl@[range as int] == 0,
            forall|i: int| 0 <= i <= range ==> #[trigger] fl@[i] <= 1,
            forall|i: int| 0 <= i < range ==> (#[trigger] fl@[i] != 0 <==>
                exists|j2: int| 0 <= j2 < j && #[trigger] ival(t.s[j2][0]) == smin + i && nq(t, name, t.s[j2][3])),
        decreases c.n - j,
    {
        let gend = group_end(j, c.bs, c.n);
        let g = j / c.bs;
        proof { lemma_grp_bound(c.n as int, c.bs as int, c.ng as int, j as int); }
        let kb = c.key_b[g];
        let nb = c.nat_b[g];
        let tbl = nation_code_table(nk, nb);
        while j < gend
            invariant
                scols_ok(*c, t.s), tabs_typed(t), nkeys_ok(t, name, nk@), j <= gend <= c.n, g < c.ng,
                kb == c.key_b@[g as int], nb == c.nat_b@[g as int],
                tbl@.len() == 256,
                forall|x: int| 0 <= x < 256 && nb + x <= i64::MAX ==> #[trigger] tbl@[x] == nk@.contains((nb + x) as i64),
                forall|x: int| j <= x < gend ==> #[trigger] (x / c.bs as int) == g,
                forall|j2: int| 0 <= j2 < t.s.len() ==> smin <= #[trigger] ival(t.s[j2][0]) < smin + range,
                fl@.len() == range + 1, fl@[range as int] == 0,
                forall|i: int| 0 <= i <= range ==> #[trigger] fl@[i] <= 1,
                forall|i: int| 0 <= i < range ==> (#[trigger] fl@[i] != 0 <==>
                    exists|j2: int| 0 <= j2 < j && #[trigger] ival(t.s[j2][0]) == smin + i && nq(t, name, t.s[j2][3])),
            decreases gend - j,
        {
            assert(supp_row_ok(*c, t.s[j as int], j as int));
            assert(s_typed(t.s[j as int]));
            assert(j as int / c.bs as int == g);
            let code = c.nat_c[j];
            let ghost nkey: i64 = (nb + code) as i64;
            assert(t.s[j as int][3] == Val::Int(nkey as int));
            let ghost old_fl = fl@;
            if tbl[code as usize] {
                let k: i64 = kb + c.key_c[j] as i64;
                assert(ival(t.s[j as int][0]) == k as int);
                let ix: usize = (k as i128 - smin as i128) as usize;
                assert(ix as int == k - smin);
                fl[ix] = 1;
                proof {
                    assert forall|i: int| 0 <= i <= range implies #[trigger] fl@[i] <= 1 by {
                        if i != ix { assert(fl@[i] == old_fl[i]); }
                    }
                    assert(nk@.contains(nkey));
                    assert(nq(t, name, t.s[j as int][3]));
                    assert forall|i: int| 0 <= i < range implies (#[trigger] fl@[i] != 0 <==>
                        exists|j2: int| 0 <= j2 < j + 1 && #[trigger] ival(t.s[j2][0]) == smin + i && nq(t, name, t.s[j2][3])) by {
                        if i != ix {
                            assert(fl@[i] == old_fl[i]);
                            if exists|j2: int| 0 <= j2 < j + 1 && #[trigger] ival(t.s[j2][0]) == smin + i && nq(t, name, t.s[j2][3]) {
                                let j2 = choose|j2: int| 0 <= j2 < j + 1 && #[trigger] ival(t.s[j2][0]) == smin + i && nq(t, name, t.s[j2][3]);
                                assert(j2 < j);
                            }
                        } else {
                            assert(ival(t.s[j as int][0]) == smin + i);
                        }
                    }
                }
            } else {
                proof {
                    assert(!nk@.contains(nkey));
                    assert(!nq(t, name, t.s[j as int][3]));
                    assert forall|i: int| 0 <= i < range implies (#[trigger] fl@[i] != 0 <==>
                        exists|j2: int| 0 <= j2 < j + 1 && #[trigger] ival(t.s[j2][0]) == smin + i && nq(t, name, t.s[j2][3])) by {
                        if exists|j2: int| 0 <= j2 < j + 1 && #[trigger] ival(t.s[j2][0]) == smin + i && nq(t, name, t.s[j2][3]) {
                            let j2 = choose|j2: int| 0 <= j2 < j + 1 && #[trigger] ival(t.s[j2][0]) == smin + i && nq(t, name, t.s[j2][3]);
                            assert(j2 < j);
                        }
                    }
                }
            }
            j = j + 1;
        }
    }
    proof {
        assert forall|i: int| 0 <= i < range implies (#[trigger] fl@[i] != 0 <==> sq(t, name, Val::Int(smin + i))) by {
            if sq(t, name, Val::Int(smin + i)) {
                let j2 = choose|j2: int| 0 <= j2 < t.s.len() && #[trigger] t.s[j2][0] == Val::Int(smin + i) && nq(t, name, t.s[j2][3]);
                assert(s_typed(t.s[j2]));
                assert(ival(t.s[j2][0]) == smin + i);
            }
            if fl@[i] != 0 {
                let j2 = choose|j2: int| 0 <= j2 < j && #[trigger] ival(t.s[j2][0]) == smin + i && nq(t, name, t.s[j2][3]);
                assert(s_typed(t.s[j2]));
                assert(t.s[j2][0] == Val::Int(smin + i));
            }
        }
        assert forall|v: int| #[trigger] sq(t, name, Val::Int(v)) implies smin <= v < smin + range by {
            let j2 = choose|j2: int| 0 <= j2 < t.s.len() && #[trigger] t.s[j2][0] == Val::Int(v) && nq(t, name, t.s[j2][3]);
            assert(ival(t.s[j2][0]) == v);
        }
    }
    fl
}

} // verus!
