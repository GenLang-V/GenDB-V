//! The general path: one serial pass over the lineitem rows that assumes nothing about row order or key layout.
//! Every key is found by a linear search (`find_key`, `find_key2`), and the groups are kept in a list
//! (`glist_ok`). The fast path covers TPC-H data; this path makes the answer exact on every bound database. A group
//! whose absolute amount leaves `i128` is reported (`GenOut::Over`), which is the statement's `Capacity`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::link::expr::i128_max;
use crate::agent::tables::*;
use crate::agent::normal_form::*;
use crate::agent::lines::*;
use crate::agent::answer::*;
use crate::agent::columns::*;
use crate::agent::partmatch::*;
use crate::agent::nations::*;
use crate::agent::entries::*;
use crate::agent::common::bits::*;

verus! {

/// The row of key `k` in the key column `keys` (`n` rows), if any.
pub fn find_key(keys: &[i64], n: usize, k: i64) -> (r: Option<usize>)
    requires keys@.len() == n,
    ensures
        r matches Some(j) ==> j < n && keys@[j as int] == k && has_key(keys@, k),
        r is None ==> !has_key(keys@, k),
{
    let mut j: usize = 0;
    while j < n
        invariant j <= n, keys@.len() == n, forall|x: int| 0 <= x < j ==> #[trigger] keys@[x] != k,
        decreases n - j,
    {
        if keys[j] == k {
            proof { assert(has_key(keys@, k)); }
            return Some(j);
        }
        j = j + 1;
    }
    proof {
        assert(!has_key(keys@, k)) by {
            if has_key(keys@, k) {
                let x = choose|x: int| 0 <= x < keys@.len() && #[trigger] keys@[x] == k;
                assert(keys@[x] != k);
            }
        }
    }
    None
}

/// The row of key pair `(x, y)` in the key columns `s`, `t` (`n` rows), if any.
pub fn find_key2(s: &[i64], t: &[i64], n: usize, x: i64, y: i64) -> (r: Option<usize>)
    requires s@.len() == n, t@.len() == n,
    ensures
        r matches Some(j) ==> j < n && at2(s@, t@, x, y, j as int) && has_key2(s@, t@, x, y),
        r is None ==> !has_key2(s@, t@, x, y),
{
    let mut j: usize = 0;
    while j < n
        invariant j <= n, s@.len() == n, t@.len() == n, forall|q: int| 0 <= q < j ==> !#[trigger] at2(s@, t@, x, y, q),
        decreases n - j,
    {
        if s[j] == x && t[j] == y {
            proof { assert(at2(s@, t@, x, y, j as int)); }
            return Some(j);
        }
        j = j + 1;
    }
    proof {
        assert(!has_key2(s@, t@, x, y)) by {
            if has_key2(s@, t@, x, y) {
                let q = choose|q: int| 0 <= q < s@.len() && #[trigger] at2(s@, t@, x, y, q);
                assert(!at2(s@, t@, x, y, q));
            }
        }
    }
    None
}

/// One group of the general path: group `a`, year `y`, amount sum and absolute amount.
#[derive(Clone, Copy)]
pub struct GEntry {
    pub a: usize,
    pub y: i64,
    pub sum: i128,
    pub mass: u128,
}

/// The list holds exactly the non-empty groups of the rows `0..x`, with their sums and absolute amounts (within
/// `i128`).
pub open spec fn glist_ok(gl: Seq<GEntry>, sv: StoresView, ps: Seq<Literal>, x: int) -> bool {
    &&& forall|i: int| 0 <= i < gl.len() ==> 0 <= (#[trigger] gl[i]).a < n_n(sv) && nrep(sv, gl[i].a as int) == gl[i].a
        && tsum(sv, ps, gl[i].a as int, gl[i].y as int, 0, 0, x) > 0
        && gl[i].sum as int == tsum(sv, ps, gl[i].a as int, gl[i].y as int, 1, 0, x)
        && gl[i].mass as int == tsum(sv, ps, gl[i].a as int, gl[i].y as int, 2, 0, x) && gl[i].mass as int <= i128_max()
    &&& forall|i: int, j: int| 0 <= i < gl.len() && 0 <= j < gl.len() && i != j
        ==> (#[trigger] gl[i]).a != (#[trigger] gl[j]).a || gl[i].y != gl[j].y
    &&& forall|a: int, y: int| #[trigger] tsum(sv, ps, a, y, 0, 0, x) > 0
        ==> exists|i: int| 0 <= i < gl.len() && gl[i].a as int == a && gl[i].y as int == y
}

/// The general path's result: the groups, or a group whose absolute amount leaves `i128`.
pub enum GenOut {
    Entries(Vec<Entry>),
    Over(usize, i64),
}

/// The qualification, group, year and amount of lineitem row `l`, by linear searches (`None`: it does not qualify).
fn general_row(c: &Cols, bits: &Vec<u64>, reps: &Vec<usize>, l: usize, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: Option<(usize, i64, i128)>)
    requires
        cols_ok(*c, sv), bits_ok(bits@, sv, ps), l < c.nl,
        reps@.len() == c.nn, forall|a: int| 0 <= a < c.nn ==> #[trigger] reps@[a] as int == nrep(sv, a),
    ensures
        r is None ==> !line_qual(sv, ps, l as int),
        r matches Some((a, y, v)) ==> line_qual(sv, ps, l as int) && grp(sv, l as int) == a && yr(sv, l as int) == y
            && line_val(sv, l as int) == v && -0x20_0000_0000_0000_0000_0000_0000 < v < 0x20_0000_0000_0000_0000_0000_0000,
{
    let p = match find_key(c.pkey, c.np, c.lpart[l]) { Some(p) => p, None => { return None; } };
    proof {
        lemma_key_row(pk(sv), lpk(sv)[l as int]);
        assert(l_part(sv, l as int) == p);
        assert(word_bit(bits@, p as int) == match_bit(sv, ps, p as int));
    }
    let wd = bits[p / 64];
    if (wd >> ((p % 64) as u64)) & 1u64 != 1u64 {
        return None;
    }
    let s = match find_key(c.skey, c.ns, c.lsupp[l]) { Some(s) => s, None => { return None; } };
    let q = match find_key2(c.pspart, c.pssupp, c.nps, c.lpart[l], c.lsupp[l]) { Some(q) => q, None => { return None; } };
    let o = match find_key(c.okey, c.no, c.lokey[l]) { Some(o) => o, None => { return None; } };
    proof {
        lemma_key_row(sk(sv), lsk(sv)[l as int]);
        assert(l_supp(sv, l as int) == s);
    }
    let a0 = match find_key(c.nkey, c.nn, c.snat[s]) { Some(a0) => a0, None => { return None; } };
    proof {
        lemma_key_row2(pspk(sv), pssk(sv), lpk(sv)[l as int], lsk(sv)[l as int]);
        assert(l_ps(sv, l as int) == q);
        lemma_key_row(ok(sv), lok(sv)[l as int]);
        assert(l_ord(sv, l as int) == o);
        lemma_key_row(nk(sv), sn(sv)[s as int]);
        assert(l_nat(sv, l as int) == a0);
    }
    let a = reps[a0];
    let y = day_year_exec(c.odate[o]);
    let price = c.lprice[l];
    let disc = c.ldisc[l];
    let qty = c.lqty[l];
    let cost = c.pscost[q];
    proof {
        assert(num15(lpr(sv)[l as int]) && num15(ldc(sv)[l as int]) && num15(lqt(sv)[l as int]));
        assert(num15(psc(sv)[q as int]));
        assert(-1_000_000_000_000_000 * 1_000_000_000_000_100 < price * (100 - disc) < 1_000_000_000_000_000 * 1_000_000_000_000_100)
            by (nonlinear_arith) requires -1_000_000_000_000_000 < price < 1_000_000_000_000_000,
                -1_000_000_000_000_000 < disc < 1_000_000_000_000_000;
        assert(-1_000_000_000_000_000 * 1_000_000_000_000_000 < cost * qty < 1_000_000_000_000_000 * 1_000_000_000_000_000)
            by (nonlinear_arith) requires -1_000_000_000_000_000 < cost < 1_000_000_000_000_000,
                -1_000_000_000_000_000 < qty < 1_000_000_000_000_000;
    }
    let v: i128 = price * (100 - disc) - cost * qty;
    Some((a, y, v))
}

/// A non-qualifying row leaves the list as it is.
proof fn lemma_glist_skip(gl: Seq<GEntry>, sv: StoresView, ps: Seq<Literal>, l: int)
    requires glist_ok(gl, sv, ps, l), !line_qual(sv, ps, l), 0 <= l,
    ensures glist_ok(gl, sv, ps, l + 1),
{
    assert forall|i: int| 0 <= i < gl.len() implies 0 <= (#[trigger] gl[i]).a < n_n(sv) && nrep(sv, gl[i].a as int) == gl[i].a
        && tsum(sv, ps, gl[i].a as int, gl[i].y as int, 0, 0, l + 1) > 0
        && gl[i].sum as int == tsum(sv, ps, gl[i].a as int, gl[i].y as int, 1, 0, l + 1)
        && gl[i].mass as int == tsum(sv, ps, gl[i].a as int, gl[i].y as int, 2, 0, l + 1) && gl[i].mass as int <= i128_max() by {}
    assert forall|a: int, y: int| #[trigger] tsum(sv, ps, a, y, 0, 0, l + 1) > 0
        implies exists|i: int| 0 <= i < gl.len() && gl[i].a as int == a && gl[i].y as int == y by {
        assert(tsum(sv, ps, a, y, 0, 0, l + 1) == tsum(sv, ps, a, y, 0, 0, l));
    }
}

/// The list entry of group `a`, year `y`, if any.
fn find_group(gl: &Vec<GEntry>, a: usize, y: i64) -> (r: Option<usize>)
    ensures
        r matches Some(i) ==> i < gl@.len() && gl@[i as int].a == a && gl@[i as int].y == y,
        r is None ==> forall|j: int| 0 <= j < gl@.len() ==> (#[trigger] gl@[j]).a != a || gl@[j].y != y,
{
    let mut i: usize = 0;
    while i < gl.len()
        invariant i <= gl@.len(), forall|j: int| 0 <= j < i ==> (#[trigger] gl@[j]).a != a || gl@[j].y != y,
        decreases gl@.len() - i,
    {
        if gl[i].a == a && gl[i].y == y {
            return Some(i);
        }
        i = i + 1;
    }
    None
}

/// Adds qualifying row `l` (group `a`, year `y`, amount `v`) to the list; `false` when the group's absolute amount
/// leaves `i128`.
fn add_row(gl: &mut Vec<GEntry>, a: usize, y: i64, v: i128, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(l): Ghost<int>)
    -> (ok: bool)
    requires
        glist_ok(old(gl)@, sv, ps, l), 0 <= l,
        line_qual(sv, ps, l), grp(sv, l) == a, yr(sv, l) == y, line_val(sv, l) == v,
        -0x20_0000_0000_0000_0000_0000_0000 < v < 0x20_0000_0000_0000_0000_0000_0000,
    ensures
        ok ==> glist_ok(final(gl)@, sv, ps, l + 1),
        !ok ==> nrep(sv, a as int) == a && tsum(sv, ps, a as int, y as int, 2, 0, l + 1) > i128_max(),
{
    proof { lemma_line_key_grp(sv, ps, l); }
    let ghost gl0 = gl@;
    let av: u128 = if v < 0 { (0 - v) as u128 } else { v as u128 };
    match find_group(gl, a, y) {
        Some(i) => {
            let e = gl[i];
            let m2 = e.mass + av;
            if m2 > i128::MAX as u128 {
                return false;
            }
            proof {
                lemma_tsum_bounds(sv, ps, a as int, y as int, 0, l);
            }
            let e2 = GEntry { a, y, sum: e.sum + v, mass: m2 };
            gl.set(i, e2);
            proof {
                assert forall|k: int| 0 <= k < gl@.len() implies 0 <= (#[trigger] gl@[k]).a < n_n(sv) && nrep(sv, gl@[k].a as int) == gl@[k].a
                    && tsum(sv, ps, gl@[k].a as int, gl@[k].y as int, 0, 0, l + 1) > 0
                    && gl@[k].sum as int == tsum(sv, ps, gl@[k].a as int, gl@[k].y as int, 1, 0, l + 1)
                    && gl@[k].mass as int == tsum(sv, ps, gl@[k].a as int, gl@[k].y as int, 2, 0, l + 1) && gl@[k].mass as int <= i128_max() by {
                    if k != i {
                        assert(gl@[k] == gl0[k]);
                        assert(gl0[k].a != a || gl0[k].y != y);
                    }
                }
                assert forall|k1: int, k2: int| 0 <= k1 < gl@.len() && 0 <= k2 < gl@.len() && k1 != k2
                    implies (#[trigger] gl@[k1]).a != (#[trigger] gl@[k2]).a || gl@[k1].y != gl@[k2].y by {
                    assert(gl0[k1].a != gl0[k2].a || gl0[k1].y != gl0[k2].y);
                }
                assert forall|aa: int, yy: int| #[trigger] tsum(sv, ps, aa, yy, 0, 0, l + 1) > 0
                    implies exists|k: int| 0 <= k < gl@.len() && gl@[k].a as int == aa && gl@[k].y as int == yy by {
                    if aa == a && yy == y {
                        assert(gl@[i as int].a == a && gl@[i as int].y == y);
                    } else {
                        assert(tsum(sv, ps, aa, yy, 0, 0, l + 1) == tsum(sv, ps, aa, yy, 0, 0, l));
                        let k = choose|k: int| 0 <= k < gl0.len() && gl0[k].a as int == aa && gl0[k].y as int == yy;
                        assert(gl@[k] == gl0[k]);
                    }
                }
            }
            true
        },
        None => {
            proof {
                assert(tsum(sv, ps, a as int, y as int, 0, 0, l) == 0) by {
                    lemma_tsum_bounds(sv, ps, a as int, y as int, 0, l);
                    if tsum(sv, ps, a as int, y as int, 0, 0, l) > 0 {
                        let k = choose|k: int| 0 <= k < gl0.len() && gl0[k].a as int == a && gl0[k].y as int == y;
                        assert(gl0[k].a != a || gl0[k].y != y);
                    }
                }
                lemma_tsum_bounds(sv, ps, a as int, y as int, 0, l);
            }
            gl.push(GEntry { a, y, sum: v, mass: av });
            proof {
                assert forall|k: int| 0 <= k < gl@.len() implies 0 <= (#[trigger] gl@[k]).a < n_n(sv) && nrep(sv, gl@[k].a as int) == gl@[k].a
                    && tsum(sv, ps, gl@[k].a as int, gl@[k].y as int, 0, 0, l + 1) > 0
                    && gl@[k].sum as int == tsum(sv, ps, gl@[k].a as int, gl@[k].y as int, 1, 0, l + 1)
                    && gl@[k].mass as int == tsum(sv, ps, gl@[k].a as int, gl@[k].y as int, 2, 0, l + 1) && gl@[k].mass as int <= i128_max() by {
                    if k < gl0.len() {
                        assert(gl@[k] == gl0[k]);
                        assert(gl0[k].a != a || gl0[k].y != y);
                    }
                }
                assert forall|k1: int, k2: int| 0 <= k1 < gl@.len() && 0 <= k2 < gl@.len() && k1 != k2
                    implies (#[trigger] gl@[k1]).a != (#[trigger] gl@[k2]).a || gl@[k1].y != gl@[k2].y by {
                    if k1 < gl0.len() && k2 < gl0.len() {
                        assert(gl@[k1] == gl0[k1] && gl@[k2] == gl0[k2]);
                    } else if k1 < gl0.len() {
                        assert(gl@[k1] == gl0[k1]);
                        assert(gl0[k1].a != a || gl0[k1].y != y);
                    } else {
                        assert(gl@[k2] == gl0[k2]);
                        assert(gl0[k2].a != a || gl0[k2].y != y);
                    }
                }
                assert forall|aa: int, yy: int| #[trigger] tsum(sv, ps, aa, yy, 0, 0, l + 1) > 0
                    implies exists|k: int| 0 <= k < gl@.len() && gl@[k].a as int == aa && gl@[k].y as int == yy by {
                    if aa == a && yy == y {
                        assert(gl@[gl@.len() - 1].a == a && gl@[gl@.len() - 1].y == y);
                    } else {
                        assert(tsum(sv, ps, aa, yy, 0, 0, l + 1) == tsum(sv, ps, aa, yy, 0, 0, l));
                        let k = choose|k: int| 0 <= k < gl0.len() && gl0[k].a as int == aa && gl0[k].y as int == yy;
                        assert(gl@[k] == gl0[k]);
                    }
                }
            }
            true
        },
    }
}

/// The groups of all lineitem rows (serial).
pub fn general_path(c: &Cols, bits: &Vec<u64>, reps: &Vec<usize>, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: GenOut)
    requires
        cols_ok(*c, sv), bits_ok(bits@, sv, ps),
        reps@.len() == c.nn, forall|a: int| 0 <= a < c.nn ==> #[trigger] reps@[a] as int == nrep(sv, a),
    ensures
        r matches GenOut::Entries(es) ==> elist_ok(es@, sv, ps, n_l(sv)),
        r matches GenOut::Over(a, y) ==> nrep(sv, a as int) == a && tsum(sv, ps, a as int, y as int, 2, 0, n_l(sv)) > i128_max(),
{
    let nl = c.nl;
    let mut gl: Vec<GEntry> = Vec::new();
    let mut l: usize = 0;
    while l < nl
        invariant
            l <= nl, nl == c.nl, cols_ok(*c, sv), bits_ok(bits@, sv, ps),
            reps@.len() == c.nn, forall|a: int| 0 <= a < c.nn ==> #[trigger] reps@[a] as int == nrep(sv, a),
            glist_ok(gl@, sv, ps, l as int),
        decreases nl - l,
    {
        match general_row(c, bits, reps, l, Ghost(sv), Ghost(ps)) {
            None => {
                proof { lemma_glist_skip(gl@, sv, ps, l as int); }
            },
            Some((a, y, v)) => {
                if !add_row(&mut gl, a, y, v, Ghost(sv), Ghost(ps), Ghost(l as int)) {
                    proof {
                        lemma_tsum_split(sv, ps, a as int, y as int, 2, 0, l + 1, nl as int);
                        lemma_tsum_bounds(sv, ps, a as int, y as int, l + 1, nl as int);
                    }
                    return GenOut::Over(a, y);
                }
            },
        }
        l = l + 1;
    }
    // the entries
    let mut es: Vec<Entry> = Vec::new();
    let mut i: usize = 0;
    while i < gl.len()
        invariant
            i <= gl@.len(), glist_ok(gl@, sv, ps, nl as int), nl == n_l(sv), es@.len() == i,
            forall|k: int| 0 <= k < i ==> (#[trigger] es@[k]).a == gl@[k].a && es@[k].y == gl@[k].y && es@[k].sum == gl@[k].sum,
        decreases gl@.len() - i,
    {
        es.push(Entry { a: gl[i].a, y: gl[i].y, sum: gl[i].sum });
        i = i + 1;
    }
    proof {
        let n = nl as int;
        assert forall|k: int| 0 <= k < es@.len() implies 0 <= (#[trigger] es@[k]).a < n_n(sv) && nrep(sv, es@[k].a as int) == es@[k].a
            && tsum(sv, ps, es@[k].a as int, es@[k].y as int, 0, 0, n) > 0
            && es@[k].sum as int == tsum(sv, ps, es@[k].a as int, es@[k].y as int, 1, 0, n) by {
            assert(gl@[k].a == es@[k].a);
        }
        assert forall|k1: int, k2: int| 0 <= k1 < es@.len() && 0 <= k2 < es@.len() && k1 != k2 implies ekey(#[trigger] es@[k1]) != ekey(#[trigger] es@[k2]) by {
            assert(gl@[k1].a != gl@[k2].a || gl@[k1].y != gl@[k2].y);
        }
        assert forall|a: int, y: int| 0 <= a < n_n(sv) && nrep(sv, a) == a && #[trigger] tsum(sv, ps, a, y, 0, 0, n) > 0
            implies exists|k: int| 0 <= k < es@.len() && ekey(es@[k]) == (a, y) by {
            let k = choose|k: int| 0 <= k < gl@.len() && gl@[k].a as int == a && gl@[k].y as int == y;
            assert(ekey(es@[k]) == (a, y));
        }
        assert forall|a: int, y: int| #[trigger] tsum(sv, ps, a, y, 2, 0, n) <= i128_max() by {
            lemma_tsum_bounds(sv, ps, a, y, 0, n);
            if tsum(sv, ps, a, y, 0, 0, n) > 0 {
                let k = choose|k: int| 0 <= k < gl@.len() && gl@[k].a as int == a && gl@[k].y as int == y;
                assert(gl@[k].mass as int <= i128_max());
            }
        }
    }
    GenOut::Entries(es)
}

} // verus!
