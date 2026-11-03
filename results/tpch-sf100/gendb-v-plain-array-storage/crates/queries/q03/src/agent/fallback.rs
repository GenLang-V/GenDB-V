//! The general path: one serial pass over the lineitem rows that assumes nothing about row order or key layout.
//!
//! Each row finds its order by `find_key` (checked equality, so any order of the rows works), its customer likewise
//! (`cust_generic`), and adds its value to per-order accumulators indexed by the orders row (`acc_sum`, `acc_abs`,
//! `acc_hit`). The absolute sums are checked against `i128::MAX`: a group beyond it is outside the statement's
//! capacity domain (`Overflow`). The fast path (`agent::scan`) is used whenever its checks hold; this path is the
//! exact answer for every other input.
use vstd::prelude::*;
use crate::spec::numeric::abs;
use crate::gendb_entry::stores::StoresView;
use crate::link::expr::i128_max;
use crate::agent::tables::*;
use crate::agent::normal_form::*;
use crate::agent::runs::*;
use crate::agent::scan::*;
use crate::agent::scan_parts::find_key;
use crate::agent::customers::*;

verus! {

/// Result of the general path.
pub enum Fallback {
    /// The groups: strictly increasing orders with their sums.
    Groups(Vec<usize>, Vec<i128>),
    /// A qualifying order whose group's absolute mass exceeds `i128::MAX`.
    Overflow(usize),
}

/// The general path's view of the columns: the scan columns plus the customer columns (`seg_eq`).
pub open spec fn general_ok(c: ScanCols, cc: CustCols, sv: StoresView, seg: Seq<u8>, dl: int) -> bool {
    &&& c.lkey@ == lk(sv) && c.lship@ == ls(sv) && c.lprice@ == lp(sv) && c.ldisc@ == ld(sv)
    &&& c.okey@ == ok(sv) && c.ocust@ == oc(sv) && c.odate@ == od(sv)
    &&& c.nl as int == n_l(sv) && c.no as int == n_o(sv) && c.nc as int == n_c(sv)
    &&& c.dl as int == dl
    &&& ls(sv).len() == n_l(sv) && lp(sv).len() == n_l(sv) && ld(sv).len() == n_l(sv)
    &&& oc(sv).len() == n_o(sv) && od(sv).len() == n_o(sv)
    &&& keys_unique(ok(sv)) && keys_unique(ck(sv))
    &&& forall|i: int| 0 <= i < n_l(sv) ==> num15(#[trigger] lp(sv)[i]) && num15(ld(sv)[i])
    &&& cust_cols_ok(cc, sv, seg)
}

/// `cust_ok` by search: the customer row of `key` (unique by the primary key), then its segment.
fn cust_generic(cc: CustCols, key: i64, Ghost(sv): Ghost<StoresView>, Ghost(seg): Ghost<Seq<u8>>) -> (b: bool)
    requires cust_cols_ok(cc, sv, seg), keys_unique(ck(sv)),
    ensures b == cust_ok(sv, seg, key as int),
{
    match find_key(cc.ckey, cc.nc, key) {
        None => {
            proof {
                if cust_ok(sv, seg, key as int) {
                    let r = choose|r: int| 0 <= r < n_c(sv) && ck(sv)[r] as int == key as int && #[trigger] cseg(sv, r) == seg;
                }
            }
            false
        },
        Some(r) => {
            let b = seg_eq(cc, r, Ghost(sv), Ghost(seg));
            proof {
                if cust_ok(sv, seg, key as int) {
                    let r2 = choose|r2: int| 0 <= r2 < n_c(sv) && ck(sv)[r2] as int == key as int && #[trigger] cseg(sv, r2) == seg;
                    assert(ck(sv)[r2] == ck(sv)[r as int]);
                }
            }
            b
        },
    }
}

/// The accumulators after rows `0..q`.
pub open spec fn acc_ok(sums: Seq<i128>, abss: Seq<i128>, hits: Seq<bool>, sv: StoresView, seg: Seq<u8>, dl: int, q: int) -> bool {
    &&& sums.len() == n_o(sv) && abss.len() == n_o(sv) && hits.len() == n_o(sv)
    &&& forall|j: int| 0 <= j < n_o(sv) ==> #[trigger] sums[j] as int == order_sum(sv, seg, dl, j, 0, q)
    &&& forall|j: int| 0 <= j < n_o(sv) ==> #[trigger] abss[j] as int == order_abs(sv, seg, dl, j, 0, q)
    &&& forall|j: int| 0 <= j < n_o(sv) ==> #[trigger] hits[j] == (order_count(sv, seg, dl, j, 0, q) > 0)
}

/// The general path.
pub fn general_groups(c: ScanCols, cc: CustCols, Ghost(sv): Ghost<StoresView>, Ghost(seg): Ghost<Seq<u8>>, Ghost(dl): Ghost<int>)
    -> (r: Fallback)
    requires general_ok(c, cc, sv, seg, dl),
    ensures
        r matches Fallback::Groups(gj, gs) ==> {
            &&& gj@.len() == gs@.len()
            &&& forall|g: int, h: int| 0 <= g < h < gj@.len() ==> gj@[g] < gj@[h]
            &&& forall|g: int| 0 <= g < gj@.len() ==> (#[trigger] gj@[g] as int) < n_o(sv)
            &&& forall|g: int| 0 <= g < gj@.len() ==> #[trigger] gs@[g] as int == order_sum(sv, seg, dl, gj@[g] as int, 0, n_l(sv))
                    && order_count(sv, seg, dl, gj@[g] as int, 0, n_l(sv)) > 0
                    && order_abs(sv, seg, dl, gj@[g] as int, 0, n_l(sv)) <= i128_max()
            &&& forall|j: int| 0 <= j < n_o(sv) && #[trigger] order_count(sv, seg, dl, j, 0, n_l(sv)) > 0 ==> gj@.contains(j as usize)
        },
        r matches Fallback::Overflow(m) ==> (m as int) < n_o(sv) && order_ok(sv, seg, dl, m as int)
            && order_abs(sv, seg, dl, m as int, 0, n_l(sv)) > i128_max(),
{
    let no = c.no;
    let mut sums: Vec<i128> = vec![0i128; no];
    let mut abss: Vec<i128> = vec![0i128; no];
    let mut hits: Vec<bool> = vec![false; no];
    let mut i: usize = 0;
    while i < c.nl
        invariant
            general_ok(c, cc, sv, seg, dl), no == c.no, i <= c.nl,
            acc_ok(sums@, abss@, hits@, sv, seg, dl, i as int),
        decreases c.nl - i,
    {
        let k = c.lkey[i];
        match find_key(c.okey, no, k) {
            None => {
                proof {
                    assert forall|j: int| 0 <= j < n_o(sv) implies !line_hit(sv, seg, dl, i as int, j) by {
                        assert(ok(sv)[j] != k);
                    }
                    assert forall|j: int| 0 <= j < n_o(sv) implies #[trigger] order_sum(sv, seg, dl, j, 0, i + 1) == order_sum(sv, seg, dl, j, 0, i as int)
                        && order_abs(sv, seg, dl, j, 0, i + 1) == order_abs(sv, seg, dl, j, 0, i as int)
                        && order_count(sv, seg, dl, j, 0, i + 1) == order_count(sv, seg, dl, j, 0, i as int) by {}
                    assert(acc_ok(sums@, abss@, hits@, sv, seg, dl, i + 1)) by {
                        assert forall|j: int| 0 <= j < n_o(sv) implies #[trigger] sums@[j] as int == order_sum(sv, seg, dl, j, 0, i + 1) by {}
                        assert forall|j: int| 0 <= j < n_o(sv) implies #[trigger] abss@[j] as int == order_abs(sv, seg, dl, j, 0, i + 1) by {}
                        assert forall|j: int| 0 <= j < n_o(sv) implies #[trigger] hits@[j] == (order_count(sv, seg, dl, j, 0, i + 1) > 0) by {}
                    }
                }
            },
            Some(m) => {
                proof {
                    lemma_account_row(sv, seg, dl, 0, i as int, m as int);
                }
                let hit = c.odate[m] < c.dl && c.lship[i] > c.dl && cust_generic(cc, c.ocust[m], Ghost(sv), Ghost(seg));
                assert(hit == line_hit(sv, seg, dl, i as int, m as int));
                if hit {
                    let p = c.lprice[i];
                    let d = c.ldisc[i];
                    proof {
                        assert(num15(lp(sv)[i as int]) && num15(ld(sv)[i as int]));
                        let (pi, di) = (p as int, 100 - d as int);
                        assert(-1_000_000_000_000_100_000_000_000_000_000 < pi * di < 1_000_000_000_000_100_000_000_000_000_000) by (nonlinear_arith)
                            requires -1_000_000_000_000_000 < pi < 1_000_000_000_000_000, -1_000_000_000_000_100 < di < 1_000_000_000_000_100;
                    }
                    let v = p * (100 - d);
                    let a = if v < 0 { -v } else { v };
                    let old_abs = abss[m];
                    proof {
                        lemma_order_bounds(sv, seg, dl, m as int, 0, i as int);
                    }
                    if old_abs > i128::MAX - a {
                        proof {
                            assert(order_abs(sv, seg, dl, m as int, 0, i + 1) > i128_max());
                            lemma_order_split(sv, seg, dl, m as int, 0, i + 1, c.nl as int);
                            lemma_order_bounds(sv, seg, dl, m as int, i + 1, c.nl as int);
                        }
                        return Fallback::Overflow(m);
                    }
                    let old_sum = sums[m];
                    sums.set(m, old_sum + v);
                    abss.set(m, old_abs + a);
                    hits.set(m, true);
                } else {
                }
                proof {
                    assert(acc_ok(sums@, abss@, hits@, sv, seg, dl, i + 1)) by {
                        assert forall|j: int| 0 <= j < n_o(sv) implies #[trigger] sums@[j] as int == order_sum(sv, seg, dl, j, 0, i + 1) by {
                            if j != m as int {
                                assert(order_sum(sv, seg, dl, j, 0, i + 1) == order_sum(sv, seg, dl, j, 0, i as int));
                            }
                        }
                        assert forall|j: int| 0 <= j < n_o(sv) implies #[trigger] abss@[j] as int == order_abs(sv, seg, dl, j, 0, i + 1) by {
                            if j != m as int {
                                assert(order_abs(sv, seg, dl, j, 0, i + 1) == order_abs(sv, seg, dl, j, 0, i as int));
                            }
                        }
                        assert forall|j: int| 0 <= j < n_o(sv) implies #[trigger] hits@[j] == (order_count(sv, seg, dl, j, 0, i + 1) > 0) by {
                            if j != m as int {
                                assert(order_count(sv, seg, dl, j, 0, i + 1) == order_count(sv, seg, dl, j, 0, i as int));
                            }
                        }
                    }
                }
            },
        }
        i = i + 1;
    }
    // collect the hit orders, in order
    let mut gj: Vec<usize> = Vec::new();
    let mut gs: Vec<i128> = Vec::new();
    let mut j: usize = 0;
    while j < no
        invariant
            general_ok(c, cc, sv, seg, dl), no == c.no, j <= no,
            acc_ok(sums@, abss@, hits@, sv, seg, dl, c.nl as int),
            gj@.len() == gs@.len(),
            forall|g: int, h: int| 0 <= g < h < gj@.len() ==> gj@[g] < gj@[h],
            forall|g: int| 0 <= g < gj@.len() ==> gj@[g] < j,
            forall|g: int| 0 <= g < gj@.len() ==> #[trigger] gs@[g] as int == order_sum(sv, seg, dl, gj@[g] as int, 0, n_l(sv))
                && order_count(sv, seg, dl, gj@[g] as int, 0, n_l(sv)) > 0
                && order_abs(sv, seg, dl, gj@[g] as int, 0, n_l(sv)) <= i128_max(),
            forall|x: int| 0 <= x < j && #[trigger] order_count(sv, seg, dl, x, 0, n_l(sv)) > 0 ==> gj@.contains(x as usize),
        decreases no - j,
    {
        if hits[j] {
            let ghost gj0 = gj@;
            gj.push(j);
            gs.push(sums[j]);
            proof {
                assert(abss@[j as int] as int == order_abs(sv, seg, dl, j as int, 0, n_l(sv)));
                assert forall|x: int| 0 <= x < j + 1 && #[trigger] order_count(sv, seg, dl, x, 0, n_l(sv)) > 0 implies gj@.contains(x as usize) by {
                    if x < j {
                        let g = choose|g: int| 0 <= g < gj0.len() && gj0[g] == x as usize;
                        assert(gj@[g] == x as usize);
                    } else {
                        assert(gj@[gj0.len() as int] == x as usize);
                    }
                }
            }
        } else {
            proof {
                assert(order_count(sv, seg, dl, j as int, 0, n_l(sv)) == 0);
            }
        }
        j = j + 1;
    }
    Fallback::Groups(gj, gs)
}

} // verus!
