//! The general exact Q1 scan, for any data the storage contract admits (used only when the fast path's guards
//! fail): one serial pass over all stored rows per group key (pair of dictionary indices, in dictionary order),
//! each value decoded exactly in `i128` (a product beyond `i128` is detected by `checked_mul`), with the absolute
//! mass of every sum tracked: a sum is kept while its mass fits `i128` and flagged once it does not. Quadratic in
//! the dictionary sizes, but exact for every input.
use vstd::prelude::*;
use crate::link::expr::i128_max;
use super::model::*;
use super::fast::{Cols, cols_model};
use super::finish::{Entry, entry_vals, entries_ok, eover, esum, key_lt};

verus! {

/// The sum and absolute mass of one value kind while the mass fits `i128`, else the flag.
pub struct Acc {
    pub sum: i128,
    pub mass: i128,
    pub over: bool,
}

pub open spec fn acc_ok(acc: Acc, m: Model, p: int, a: int, b: int, w: int, j: int) -> bool {
    &&& acc.over == (kabs(m, p, a, b, w, 0, j) > i128_max())
    &&& !acc.over ==> acc.sum == ksum(m, p, a, b, w, 0, j) && acc.mass == kabs(m, p, a, b, w, 0, j)
}

/// One selected row `j` with value `v` (`None`: the value is beyond `i128`).
fn acc_add(acc: &mut Acc, v: Option<i128>, Ghost(m): Ghost<Model>, Ghost(p): Ghost<int>, Ghost(a): Ghost<int>,
    Ghost(b): Ghost<int>, Ghost(w): Ghost<int>, Ghost(j): Ghost<int>)
    requires
        0 <= j, acc_ok(*old(acc), m, p, a, b, w, j), ksel(m, p, a, b, j),
        v matches Some(x) ==> x == mval(m, w, j),
        v is None ==> abs_int(mval(m, w, j)) > i128_max(),
    ensures acc_ok(*final(acc), m, p, a, b, w, j + 1),
{
    proof {
        lemma_kabs_bounds(m, p, a, b, w, 0, j);
        assert(kabs(m, p, a, b, w, 0, j + 1) == kabs(m, p, a, b, w, 0, j) + abs_int(mval(m, w, j)));
        assert(ksum(m, p, a, b, w, 0, j + 1) == ksum(m, p, a, b, w, 0, j) + mval(m, w, j));
    }
    if acc.over {
        return;
    }
    match v {
        None => {
            acc.over = true;
        },
        Some(x) => {
            if x == i128::MIN {
                acc.over = true;
            } else {
                let ax: i128 = if x < 0 { -x } else { x };
                if acc.mass > i128::MAX - ax {
                    acc.over = true;
                } else {
                    acc.mass = acc.mass + ax;
                    acc.sum = acc.sum + x;
                }
            }
        },
    }
}

/// The unselected row `j`: nothing changes.
proof fn lemma_acc_skip(acc: Acc, m: Model, p: int, a: int, b: int, w: int, j: int)
    requires 0 <= j, acc_ok(acc, m, p, a, b, w, j), !ksel(m, p, a, b, j),
    ensures acc_ok(acc, m, p, a, b, w, j + 1),
{
}

/// The exact values of row `j`: quantity, price, price * (100 - discount), that times (100 + tax) (`None`
/// beyond `i128`), discount; its shipdate and dictionary indices.
fn row_exact(cols: &Cols, j: usize, g: usize, Ghost(m): Ghost<Model>)
    -> (r: (i128, i128, i128, Option<i128>, i128, i128, u128, u128))
    requires model_wf(m), m == cols_model(*cols, m.n, m.bsize, m.nrf, m.nls), j < m.n, g as int == (j as int) / m.bsize, g < m.nb,
    ensures
        r.0 == mval(m, 0, j as int), r.1 == mval(m, 1, j as int), r.2 == mval(m, 2, j as int),
        r.3 matches Some(x) ==> x == mval(m, 3, j as int),
        r.3 is None ==> abs_int(mval(m, 3, j as int)) > i128_max(),
        r.4 == mval(m, 4, j as int),
        r.5 == shv(m, j as int), r.6 == rfi(m, j as int), r.7 == lsi(m, j as int),
{
    let q = cols.qty_b[g] as i128 + cols.qty[j] as i128;
    let pr = cols.price_b[g] as i128 + cols.price[j] as i128;
    let d = cols.disc_b[g] as i128 + cols.disc[j] as i128;
    let t = cols.tax_b[g] as i128 + cols.tax[j] as i128;
    let x = 100 - d;
    assert(-0x8000_0001_0000_0000 <= pr <= 0x8000_0001_0000_0000);
    assert(-0x8000_0000_0000_0164 <= x <= 0x8000_0000_0000_0164);
    assert(-0x4000_0001_0000_0000_0000_0000_0000_0000 <= pr * x <= 0x4000_0001_0000_0000_0000_0000_0000_0000) by (nonlinear_arith)
        requires -0x8000_0001_0000_0000 <= pr <= 0x8000_0001_0000_0000, -0x8000_0000_0000_0164 <= x <= 0x8000_0000_0000_0164;
    let dp = pr * x;
    let ch = dp.checked_mul(100 + t);
    let sh = cols.ship_b[g] as i128 + cols.ship[j] as i128;
    let rf = cols.rf_b[g] as u128 + cols.rf[j] as u128;
    let ls = cols.ls_b[g] as u128 + cols.ls[j] as u128;
    proof {
        assert(blk(m, j as int) == g);
        if ch is None {
            assert(abs_int(dp * (100 + t)) > i128_max());
        }
    }
    (q, pr, dp, ch, d, sh, rf, ls)
}

/// The exact sums of key `(a, b)` over all stored rows.
fn key_scan(cols: &Cols, n: usize, bsize: u64, p: i64, a: usize, b: usize, Ghost(m): Ghost<Model>) -> (e: Entry)
    requires model_wf(m), m == cols_model(*cols, m.n, m.bsize, m.nrf, m.nls), n == m.n, bsize == m.bsize,
    ensures e.a == a && e.b == b && entry_vals(e, m, p as int),
{
    let ghost pi = p as int;
    let ghost ai = a as int;
    let ghost bi = b as int;
    let mut cnt: u64 = 0;
    let mut acc0 = Acc { sum: 0, mass: 0, over: false };
    let mut acc1 = Acc { sum: 0, mass: 0, over: false };
    let mut acc2 = Acc { sum: 0, mass: 0, over: false };
    let mut acc3 = Acc { sum: 0, mass: 0, over: false };
    let mut acc4 = Acc { sum: 0, mass: 0, over: false };
    let mut j: usize = 0;
    while j < n
        invariant
            model_wf(m), m == cols_model(*cols, m.n, m.bsize, m.nrf, m.nls), n == m.n, bsize == m.bsize, j <= n,
            pi == p as int, ai == a as int, bi == b as int,
            cnt as int == ksum(m, pi, ai, bi, 5, 0, j as int),
            acc_ok(acc0, m, pi, ai, bi, 0, j as int), acc_ok(acc1, m, pi, ai, bi, 1, j as int),
            acc_ok(acc2, m, pi, ai, bi, 2, j as int), acc_ok(acc3, m, pi, ai, bi, 3, j as int),
            acc_ok(acc4, m, pi, ai, bi, 4, j as int),
        decreases n - j,
    {
        proof {
            lemma_blk(m, j as int);
            lemma_kabs_bounds(m, pi, ai, bi, 5, 0, j as int);
            vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(j as int, 1, bsize as int);
        }
        let g = ((j as u64) / bsize) as usize;
        let (q, pr, dp, ch, d, sh, rf, ls) = row_exact(cols, j, g, Ghost(m));
        if sh <= p as i128 && rf == a as u128 && ls == b as u128 {
            proof {
                assert(sh == shv(m, j as int));
                assert(shv(m, j as int) <= pi);
                assert(rf == rfi(m, j as int));
                assert(rfi(m, j as int) == ai);
                assert(lsi(m, j as int) == bi);
                assert(ksel(m, pi, ai, bi, j as int));
            }
            cnt = cnt + 1;
            acc_add(&mut acc0, Some(q), Ghost(m), Ghost(pi), Ghost(ai), Ghost(bi), Ghost(0), Ghost(j as int));
            acc_add(&mut acc1, Some(pr), Ghost(m), Ghost(pi), Ghost(ai), Ghost(bi), Ghost(1), Ghost(j as int));
            acc_add(&mut acc2, Some(dp), Ghost(m), Ghost(pi), Ghost(ai), Ghost(bi), Ghost(2), Ghost(j as int));
            acc_add(&mut acc3, ch, Ghost(m), Ghost(pi), Ghost(ai), Ghost(bi), Ghost(3), Ghost(j as int));
            acc_add(&mut acc4, Some(d), Ghost(m), Ghost(pi), Ghost(ai), Ghost(bi), Ghost(4), Ghost(j as int));
        } else {
            proof {
                assert(!ksel(m, pi, ai, bi, j as int));
                lemma_acc_skip(acc0, m, pi, ai, bi, 0, j as int);
                lemma_acc_skip(acc1, m, pi, ai, bi, 1, j as int);
                lemma_acc_skip(acc2, m, pi, ai, bi, 2, j as int);
                lemma_acc_skip(acc3, m, pi, ai, bi, 3, j as int);
                lemma_acc_skip(acc4, m, pi, ai, bi, 4, j as int);
            }
        }
        j = j + 1;
    }
    let e = Entry {
        a, b, cnt,
        s0: acc0.sum, s1: acc1.sum, s2: acc2.sum, s3: acc3.sum, s4: acc4.sum,
        o0: acc0.over, o1: acc1.over, o2: acc2.over, o3: acc3.over, o4: acc4.over,
    };
    proof {
        assert forall|w: int| 0 <= w < 5 implies #[trigger] eover(e, w) == (kabs(m, pi, ai, bi, w, 0, m.n) > i128_max()) by {}
        assert forall|w: int| 0 <= w < 5 && !eover(e, w) implies #[trigger] esum(e, w) == ksum(m, pi, ai, bi, w, 0, m.n) by {}
    }
    e
}

/// The entries of every non-empty key, in dictionary order, by one exact scan per key.
pub fn general_entries(cols: &Cols, n: usize, bsize: u64, nrf: usize, nls: usize, p: i64, Ghost(m): Ghost<Model>)
    -> (es: Vec<Entry>)
    requires
        model_wf(m), m == cols_model(*cols, m.n, m.bsize, m.nrf, m.nls), n == m.n, bsize == m.bsize,
        nrf == m.nrf, nls == m.nls,
    ensures entries_ok(es@, m, p as int),
{
    let ghost pi = p as int;
    let mut es: Vec<Entry> = Vec::new();
    let mut a: usize = 0;
    while a < nrf
        invariant
            model_wf(m), m == cols_model(*cols, m.n, m.bsize, m.nrf, m.nls), n == m.n, bsize == m.bsize,
            nrf == m.nrf, nls == m.nls, a <= nrf, pi == p as int,
            forall|k: int| 0 <= k < es@.len() ==> {
                &&& #[trigger] es@[k].a < a && es@[k].b < m.nls && es@[k].cnt > 0
                &&& entry_vals(es@[k], m, pi)
            },
            forall|k1: int, k2: int| 0 <= k1 < k2 < es@.len() ==> #[trigger] key_lt(es@[k1], es@[k2]),
            forall|a2: int, b2: int| 0 <= a2 < a && 0 <= b2 < m.nls && #[trigger] ksum(m, pi, a2, b2, 5, 0, m.n) > 0
                ==> exists|k: int| 0 <= k < es@.len() && es@[k].a == a2 && es@[k].b == b2,
        decreases nrf - a,
    {
        let ghost es_a = es@;
        let mut b: usize = 0;
        while b < nls
            invariant
                model_wf(m), m == cols_model(*cols, m.n, m.bsize, m.nrf, m.nls), n == m.n, bsize == m.bsize,
                nrf == m.nrf, nls == m.nls, a < nrf, b <= nls, pi == p as int,
                es_a.len() <= es@.len(), es@.subrange(0, es_a.len() as int) == es_a,
                forall|k: int| 0 <= k < es@.len() ==> {
                    &&& #[trigger] es@[k].a <= a && es@[k].b < m.nls && es@[k].cnt > 0
                    &&& entry_vals(es@[k], m, pi)
                    &&& (es@[k].a < a || es@[k].b < b)
                },
                forall|k1: int, k2: int| 0 <= k1 < k2 < es@.len() ==> #[trigger] key_lt(es@[k1], es@[k2]),
                forall|a2: int, b2: int| ((0 <= a2 < a && 0 <= b2 < m.nls) || (a2 == a && 0 <= b2 < b))
                    && #[trigger] ksum(m, pi, a2, b2, 5, 0, m.n) > 0
                    ==> exists|k: int| 0 <= k < es@.len() && es@[k].a == a2 && es@[k].b == b2,
            decreases nls - b,
        {
            let e = key_scan(cols, n, bsize, p, a, b, Ghost(m));
            if e.cnt > 0 {
                let ghost old_es = es@;
                es.push(e);
                proof {
                    assert forall|k1: int, k2: int| 0 <= k1 < k2 < es@.len() implies #[trigger] key_lt(es@[k1], es@[k2]) by {
                        if k2 == es@.len() - 1 {
                            assert(es@[k1] == old_es[k1]);
                        } else {
                            assert(es@[k1] == old_es[k1] && es@[k2] == old_es[k2]);
                        }
                    }
                    assert forall|a2: int, b2: int| ((0 <= a2 < a && 0 <= b2 < m.nls) || (a2 == a && 0 <= b2 < b + 1))
                        && #[trigger] ksum(m, pi, a2, b2, 5, 0, m.n) > 0
                        implies exists|k: int| 0 <= k < es@.len() && es@[k].a == a2 && es@[k].b == b2 by {
                        if a2 == a && b2 == b {
                            assert(es@[es@.len() - 1].a == a2 && es@[es@.len() - 1].b == b2);
                        } else {
                            let k = choose|k: int| 0 <= k < old_es.len() && old_es[k].a == a2 && old_es[k].b == b2;
                            assert(es@[k] == old_es[k]);
                        }
                    }
                    assert(es@.subrange(0, es_a.len() as int) =~= es_a) by {
                        assert(old_es.subrange(0, es_a.len() as int) == es_a);
                    }
                }
            } else {
                proof {
                    assert(ksum(m, pi, a as int, b as int, 5, 0, m.n) == 0);
                }
            }
            b = b + 1;
        }
        proof {
            assert forall|k: int| 0 <= k < es@.len() implies {
                &&& #[trigger] es@[k].a < a + 1 && es@[k].b < m.nls && es@[k].cnt > 0
                &&& entry_vals(es@[k], m, pi)
            } by {}
        }
        a = a + 1;
    }
    es
}

} // verus!
