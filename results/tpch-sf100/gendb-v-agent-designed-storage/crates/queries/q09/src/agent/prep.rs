//! Small tables built on the calling thread before the scan: the nation row of each nation key in `[0, 256)`
//! (`lookups::ntab_ok`), whether supplier keys are dense (`lookups::s_dense_ok`), the first nation row of each nation
//! name (`groups::nrep_ok`), and the bytes of a nation name.
use vstd::prelude::*;
use crate::gendb_entry::work::filled;
use super::model::*;
use super::cols::*;
use super::lookups::*;
use super::groups::nrep_ok;

verus! {

/// The nation table: entry `k` is the nation row of key `k` in `[0, 256)` (or `NO_NATION`), and whether every nation
/// key is in `[0, 256)`.
pub fn nation_table(c: &Cols, d: &Divs, Ghost(m): Ghost<M>) -> (r: (Vec<u64>, bool))
    requires look_ok(*c, *d, m),
    ensures ntab_ok(r.0@, r.1, m),
{
    let mut ntab: Vec<u64> = filled(256, NO_NATION);
    let mut small = true;
    let mut n: usize = 0;
    proof { assert(frame_ok(m.n_n, m.n_bs, m.n_nb)); }
    while n < c.n_n
        invariant
            look_ok(*c, *d, m),
            n <= m.n_n, m.n_n < NO_NATION,
            ntab@.len() == 256,
            forall|k: int| 0 <= k < 256 ==> (#[trigger] ntab@[k] == NO_NATION && forall|x: int| 0 <= x < n ==> nkey(m, x) != k)
                || (ntab@[k] < n && nkey(m, ntab@[k] as int) == k),
            small ==> forall|x: int| 0 <= x < n ==> 0 <= #[trigger] nkey(m, x) < 256,
        decreases m.n_n - n,
    {
        let k = get_nkey(c, d, n, Ghost(m));
        if 0 <= k && k < 256 {
            if ntab[k as usize] == NO_NATION {
                let ghost t0 = ntab@;
                ntab.set(k as usize, n as u64);
                proof {
                    assert forall|k2: int| 0 <= k2 < 256 implies (#[trigger] ntab@[k2] == NO_NATION && forall|x: int| 0 <= x < n + 1 ==> nkey(m, x) != k2)
                        || (ntab@[k2] < n + 1 && nkey(m, ntab@[k2] as int) == k2) by {
                        if k2 != k as int {
                            assert(ntab@[k2] == t0[k2]);
                        }
                    }
                }
            } else {
                proof {
                    assert forall|k2: int| 0 <= k2 < 256 implies (#[trigger] ntab@[k2] == NO_NATION && forall|x: int| 0 <= x < n + 1 ==> nkey(m, x) != k2)
                        || (ntab@[k2] < n + 1 && nkey(m, ntab@[k2] as int) == k2) by {
                        if k2 == k as int {
                            assert(ntab@[k2] != NO_NATION);
                        }
                    }
                }
            }
        } else {
            small = false;
            proof {
                assert forall|k2: int| 0 <= k2 < 256 implies (#[trigger] ntab@[k2] == NO_NATION && forall|x: int| 0 <= x < n + 1 ==> nkey(m, x) != k2)
                    || (ntab@[k2] < n + 1 && nkey(m, ntab@[k2] as int) == k2) by {
                    assert(nkey(m, n as int) != k2);
                }
            }
        }
        n = n + 1;
    }
    proof {
        assert forall|k: int| 0 <= k < 256 implies (#[trigger] ntab@[k] == NO_NATION && npos(m, k) == m.n_n
            || ntab@[k] < m.n_n && ntab@[k] as int == npos(m, k)) by {
            if ntab@[k] == NO_NATION && forall|x: int| 0 <= x < m.n_n ==> nkey(m, x) != k {
                assert forall|x: int| 0 <= x < m.n_n implies #[trigger] nkey(m, x) != k by {}
                lemma_npos(m, k, 0);
            } else {
                lemma_npos(m, k, ntab@[k] as int);
            }
        }
    }
    (ntab, small)
}

/// Supplier row `s` has key `s + 1` for every row.
pub fn supp_dense(c: &Cols, d: &Divs, Ghost(m): Ghost<M>) -> (r: bool)
    requires look_ok(*c, *d, m),
    ensures r ==> s_dense_ok(m),
{
    let mut s: usize = 0;
    while s < c.s_n
        invariant
            look_ok(*c, *d, m),
            s <= m.s_n,
            forall|x: int| 0 <= x < s ==> #[trigger] skey(m, x) == x + 1,
        decreases m.s_n - s,
    {
        if get_skey(c, d, s, Ghost(m)) as i128 != s as i128 + 1 {
            return false;
        }
        s = s + 1;
    }
    true
}

/// Nation rows `a` and `b` have the same name.
pub fn same_name(c: &Cols, a: usize, b: usize, Ghost(m): Ghost<M>) -> (r: bool)
    requires cols_ok(*c, m), shapes_ok(m), a < m.n_n, b < m.n_n,
    ensures r == (nname(m, a as int) == nname(m, b as int)),
{
    proof {
        assert(crate::stores::suppliers::interface::common::colfmt::text_range_ok(m.n_name_o, m.n_name_y, a as int));
        assert(crate::stores::suppliers::interface::common::colfmt::text_range_ok(m.n_name_o, m.n_name_y, b as int));
    }
    let a0 = c.n_name_o[a] as usize;
    let a1 = c.n_name_o[a + 1] as usize;
    let b0 = c.n_name_o[b] as usize;
    let b1 = c.n_name_o[b + 1] as usize;
    let ghost sa = nname(m, a as int);
    let ghost sb = nname(m, b as int);
    proof {
        assert(sa == c.n_name_y@.subrange(a0 as int, a1 as int));
        assert(sb == c.n_name_y@.subrange(b0 as int, b1 as int));
        assert(sa.len() == a1 - a0 && sb.len() == b1 - b0);
    }
    if a1 - a0 != b1 - b0 {
        return false;
    }
    let mut i: usize = 0;
    while i < a1 - a0
        invariant
            cols_ok(*c, m),
            a0 <= a1 <= c.n_name_y@.len(), b0 <= b1 <= c.n_name_y@.len(), a1 - a0 == b1 - b0,
            sa == c.n_name_y@.subrange(a0 as int, a1 as int), sb == c.n_name_y@.subrange(b0 as int, b1 as int),
            sa == nname(m, a as int), sb == nname(m, b as int),
            i <= a1 - a0,
            forall|x: int| 0 <= x < i ==> sa[x] == sb[x],
        decreases a1 - a0 - i,
    {
        if c.n_name_y[a0 + i] != c.n_name_y[b0 + i] {
            proof {
                assert(sa[i as int] == c.n_name_y@[a0 + i]);
                assert(sb[i as int] == c.n_name_y@[b0 + i]);
                assert(sa[i as int] != sb[i as int]);
            }
            return false;
        }
        i = i + 1;
    }
    proof { assert(sa =~= sb); }
    true
}

/// The first nation row of each nation name.
pub fn first_names(c: &Cols, Ghost(m): Ghost<M>) -> (r: Vec<u64>)
    requires cols_ok(*c, m), shapes_ok(m),
    ensures nrep_ok(m, r@),
{
    let mut nrep: Vec<u64> = Vec::new();
    let mut n: usize = 0;
    while n < c.n_n
        invariant
            cols_ok(*c, m), shapes_ok(m),
            n <= m.n_n,
            nrep@.len() == n,
            forall|x: int| 0 <= x < n ==> {
                &&& #[trigger] nrep@[x] <= x
                &&& nname(m, nrep@[x] as int) == nname(m, x)
                &&& forall|z: int| 0 <= z < nrep@[x] ==> nname(m, z) != nname(m, x)
            },
        decreases m.n_n - n,
    {
        let mut r: usize = 0;
        while r < n && !same_name(c, r, n, Ghost(m))
            invariant
                cols_ok(*c, m), shapes_ok(m),
                n < m.n_n, r <= n,
                forall|z: int| 0 <= z < r ==> nname(m, z) != nname(m, n as int),
            decreases n - r,
        {
            r = r + 1;
        }
        proof {
            if r < n {
                assert(nname(m, r as int) == nname(m, n as int));
            }
        }
        let ghost v0 = nrep@;
        nrep.push(r as u64);
        proof {
            assert forall|x: int| 0 <= x < n + 1 implies {
                &&& #[trigger] nrep@[x] <= x
                &&& nname(m, nrep@[x] as int) == nname(m, x)
                &&& forall|z: int| 0 <= z < nrep@[x] ==> nname(m, z) != nname(m, x)
            } by {
                if x < n {
                    assert(nrep@[x] == v0[x]);
                }
            }
        }
        n = n + 1;
    }
    nrep
}

/// The bytes of nation row `r`'s name.
pub fn name_bytes(c: &Cols, r: usize, Ghost(m): Ghost<M>) -> (v: Vec<u8>)
    requires cols_ok(*c, m), shapes_ok(m), r < m.n_n,
    ensures v@ == nname(m, r as int),
{
    proof {
        assert(crate::stores::suppliers::interface::common::colfmt::text_range_ok(m.n_name_o, m.n_name_y, r as int));
    }
    let a = c.n_name_o[r] as usize;
    let e = c.n_name_o[r + 1] as usize;
    let mut v: Vec<u8> = Vec::new();
    let mut i = a;
    while i < e
        invariant
            cols_ok(*c, m),
            a <= i <= e <= c.n_name_y@.len(),
            v@ == c.n_name_y@.subrange(a as int, i as int),
        decreases e - i,
    {
        v.push(c.n_name_y[i]);
        proof { assert(v@ =~= c.n_name_y@.subrange(a as int, i + 1)); }
        i = i + 1;
    }
    v
}

} // verus!
