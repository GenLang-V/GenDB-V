//! The stored lineitem range of the order date window `[lo, hi]`.
//!
//! The orders zone map `zm` (one maximum of o_orderdate per group of `bs_o` stored orders rows; the group base is
//! a minimum, codes being unsigned) gives a prefix of orders groups whose dates are all below `lo` and a suffix of
//! groups whose dates are all above `hi`: stored orders rows `[0, qa)` and `[qb, n_o)` are outside the window.
//! When the stored lineitem rows follow the stored orders (`lines_clustered`: the order position `rpos` of the
//! lines never decreases), the lines of those orders are a prefix `[0, la)` and a suffix `[lb, n_l)` of the stored
//! lineitem rows, found by binary search on the order position. Without clustering the range is all rows.
use vstd::prelude::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::spec::value::*;
use crate::stores::factsdir::interface as fi;
use crate::stores::factsdir::interface::common::colfmt as fc;
use crate::stores::factsdir::declaration as fd;
use super::model::*;
use super::kernel::*;
use super::decode::*;
use super::run::bounds_ok;

verus! {

// ------------------------------------------------------------------------------------------------ the zone map

/// `zm[g]` bounds the order date of every stored orders row of group `g` (of `bs_o` rows) from above.
pub open spec fn zone_ok(c: Cols, zm: Seq<i64>) -> bool {
    forall|p: int| 0 <= p < c.n_o ==> #[trigger] zone_row(c, zm, p)
}

/// Stored orders row `p`'s group has a zone map entry bounding its date.
pub open spec fn zone_row(c: Cols, zm: Seq<i64>, p: int) -> bool {
    p / (c.bs_o as int) < zm.len() && od(c, p) <= zm[p / (c.bs_o as int)]
}

/// The orders date zone map part of the stored parts.
pub open spec fn zone_part(sv: StoresView) -> Seq<i64> {
    fc::i64s(or_tp(sv)[fi::OR_ORDERDATE_ZMAX as int])
}

/// The zone map part bounds the decoded order dates.
pub proof fn lemma_zone(sv: StoresView, db: Database, c: Cols)
    requires bound_db(sv, db), cols_from(sv, c),
    ensures
        zone_ok(c, zone_part(sv)),
        sv.factsdir[(fi::ORDERS_FIRST + fi::OR_ORDERDATE_ZMAX) as int] is I64,
        fi::ORDERS_FIRST + fi::OR_ORDERDATE_ZMAX < sv.factsdir.len(),
        zone_part(sv) == fc::i64s(sv.factsdir[(fi::ORDERS_FIRST + fi::OR_ORDERDATE_ZMAX) as int]),
{
    super::setup::lemma_tables(sv, db);
    lemma_or(sv, db, c);
    let tp = or_tp(sv);
    let rel = fd::stored_relations(db)[1];
    super::decode::lemma_fparts(sv, db);
    assert(fi::orders_ok(tp, rel));
    assert(fi::table_layout_ok(tp, rel.len() as int));
    let n = rel.len() as int;
    let e = c.bs_o as int;
    let bs = fc::u64s(tp[0])[1] as int;
    let (bp, cp) = (fi::OR_ORDERDATE_BASE as int, fi::OR_ORDERDATE_CODES as int);
    let zm = zone_part(sv);
    assert(fc::zone_at(tp, fi::OR_GROUPS as int, cp, bp, fi::OR_ORDERDATE_ZMAX as int));
    assert(n == c.n_o);
    assert forall|p: int| 0 <= p < c.n_o implies #[trigger] zone_row(c, zm, p) by {
        lemma_ffor(tp, n, e, bp, cp, p);
        crate::stores::factsdir::interface::common::read::lemma_for_row(tp[1], n, bs, tp[bp], tp[cp], p);
        lemma_bs_div(e, bs, n, p);
        assert(fc::in_group(fc::gs_at(tp, 1), p / bs, p));
        assert(fc::base_at(tp[bp], p / e) == c.od_b@[p / e]);
        assert(fc::code_at(tp[cp], p) == c.od_c@[p]);
    }
    assert(fi::ORDERS_FIRST + fi::OR_PARTS <= sv.factsdir.len());
    assert(tp[fi::OR_ORDERDATE_ZMAX as int] == sv.factsdir[(fi::ORDERS_FIRST + fi::OR_ORDERDATE_ZMAX) as int]);
}

// ------------------------------------------------------------------------------------------------ orders bounds

/// Row `p` of a group at or after `g` (groups of `bs` rows).
proof fn lemma_group_ge(p: int, bs: int, g: int)
    requires bs >= 1, p >= g * bs, g >= 0,
    ensures p / bs >= g,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(p, bs);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(p, bs);
    if p / bs < g {
        assert((p / bs) * bs <= (g - 1) * bs) by (nonlinear_arith) requires p / bs <= g - 1, bs >= 1;
        assert(p < g * bs) by (nonlinear_arith) requires p == bs * (p / bs) + p % bs, p % bs < bs,
            (p / bs) * bs <= (g - 1) * bs;
    }
}

/// Row `p` before group `g`'s first row (groups of `bs` rows).
proof fn lemma_group_lt(p: int, bs: int, g: int)
    requires bs >= 1, 0 <= p < g * bs,
    ensures p / bs < g,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(p, bs);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(p, bs);
    if p / bs >= g {
        assert((p / bs) * bs >= g * bs) by (nonlinear_arith) requires p / bs >= g, bs >= 1;
        assert(p >= g * bs) by (nonlinear_arith) requires p == bs * (p / bs) + p % bs, p % bs >= 0,
            (p / bs) * bs >= g * bs;
    }
}

/// The first row of group `g`, capped at `n` (`g * bs` without overflow).
fn group_start(g: usize, bs: usize, n: usize) -> (q: usize)
    requires bs >= 1,
    ensures q <= n, q == n || q == g * bs, q < n ==> q == g * bs, g * bs <= n ==> q == g * bs,
{
    if g > n / bs {
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, bs as int);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(n as int, bs as int);
            assert(g * bs > n) by (nonlinear_arith) requires g >= n / bs + 1, n == bs * (n / bs) + n % bs, n % bs < bs,
                bs >= 1;
        }
        n
    } else {
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, bs as int);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(n as int, bs as int);
            assert(g * bs <= n) by (nonlinear_arith) requires g <= n / bs, n == bs * (n / bs) + n % bs, n % bs >= 0,
                bs >= 1;
        }
        g * bs
    }
}

/// Stored orders rows `[0, qa)` have dates below `lo`, rows `[qb, n_o)` dates above `hi`.
pub open spec fn orders_cut(c: Cols, qa: int, qb: int) -> bool {
    &&& 0 <= qa <= qb <= c.n_o
    &&& forall|p: int| 0 <= p < qa ==> #[trigger] od(c, p) < c.lo
    &&& forall|p: int| qb <= p < c.n_o ==> #[trigger] od(c, p) > c.hi
}

/// The orders rows outside the window by the zone map.
fn orders_bounds(c: &Cols, zm: &[i64]) -> (r: (usize, usize))
    requires cols_ok(*c), zone_ok(*c, zm@),
    ensures orders_cut(*c, r.0 as int, r.1 as int),
{
    let ng = zm.len();
    let bs = c.bs_o;
    let n = c.n_o;
    let mut g_lo: usize = 0;
    while g_lo < ng && zm[g_lo] < c.lo
        invariant
            g_lo <= ng, ng == zm@.len(),
            forall|g: int| 0 <= g < g_lo ==> #[trigger] zm@[g] < c.lo,
        decreases ng - g_lo,
    {
        g_lo = g_lo + 1;
    }
    let mut g_hi: usize = ng;
    proof {
        assert forall|p: int| 0 <= p < n && p / (bs as int) >= g_hi implies #[trigger] od(*c, p) > c.hi by {
            assert(zone_row(*c, zm@, p));
        }
    }
    while g_hi > g_lo && g_hi - 1 < c.od_b.len() && c.od_b[g_hi - 1] > c.hi
        invariant
            cols_ok(*c), zone_ok(*c, zm@), bs == c.bs_o, n == c.n_o,
            g_lo <= g_hi <= ng, ng == zm@.len(),
            forall|g: int| 0 <= g < g_lo ==> #[trigger] zm@[g] < c.lo,
            forall|p: int| 0 <= p < n && p / (bs as int) >= g_hi ==> #[trigger] od(*c, p) > c.hi,
        decreases g_hi,
    {
        proof {
            assert forall|p: int| 0 <= p < n && p / (bs as int) >= g_hi - 1 implies #[trigger] od(*c, p) > c.hi by {
                if p / (bs as int) == g_hi - 1 {
                    assert(od(*c, p) == c.od_b@[g_hi - 1] + c.od_c@[p]);
                }
            }
        }
        g_hi = g_hi - 1;
    }
    let qa = group_start(g_lo, bs, n);
    let qb = group_start(g_hi, bs, n);
    proof {
        if g_lo * bs <= n {
            assert(g_lo * bs <= g_hi * bs) by (nonlinear_arith) requires g_lo <= g_hi, bs >= 1;
        }
        assert forall|p: int| 0 <= p < qa implies #[trigger] od(*c, p) < c.lo by {
            assert(0 <= p < c.n_o);
            assert(zone_row(*c, zm@, p));
            assert(p < g_lo * bs);
            lemma_group_lt(p, bs as int, g_lo as int);
        }
        assert forall|p: int| qb <= p < n implies #[trigger] od(*c, p) > c.hi by {
            lemma_group_ge(p, bs as int, g_hi as int);
        }
        if g_lo * bs > n {
            assert(g_hi * bs >= g_lo * bs) by (nonlinear_arith) requires g_lo <= g_hi, bs >= 1;
        }
        assert(qa <= qb);
        assert(orders_cut(*c, qa as int, qb as int));
    }
    (qa, qb)
}

// ------------------------------------------------------------------------------------------------ lineitem bounds

/// The order position of stored lineitem row `j`.
fn line_order(c: &Cols, j: usize) -> (p: usize)
    requires cols_ok(*c), j < c.n_l,
    ensures p == rpos(*c, lk(*c, j as int)), p <= c.n_o,
{
    proof {
        crate::stores::factsdir::interface::common::read::lemma_div_lt(j as int, c.bs_l as int, c.lk_b@.len() as int);
        assert(in_i64(lk(*c, j as int)));
        lemma_rpos(*c, lk(*c, j as int));
    }
    order_pos(c, c.lk_b[j / c.bs_l] + c.lk_c[j] as i64)
}

/// The first stored lineitem row whose order position is at least `q` (`n_l` when none is).
fn first_line(c: &Cols, q: usize) -> (j: usize)
    requires cols_ok(*c), lines_clustered(*c),
    ensures
        j <= c.n_l,
        forall|i: int| 0 <= i < j ==> #[trigger] rpos(*c, lk(*c, i)) < q,
        forall|i: int| j <= i < c.n_l ==> #[trigger] rpos(*c, lk(*c, i)) >= q,
{
    let mut lo: usize = 0;
    let mut hi: usize = c.n_l;
    while lo < hi
        invariant
            cols_ok(*c), lines_clustered(*c),
            lo <= hi <= c.n_l,
            forall|i: int| 0 <= i < lo ==> #[trigger] rpos(*c, lk(*c, i)) < q,
            forall|i: int| hi <= i < c.n_l ==> #[trigger] rpos(*c, lk(*c, i)) >= q,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        let p = line_order(c, mid);
        if p < q {
            proof {
                assert forall|i: int| 0 <= i < mid + 1 implies #[trigger] rpos(*c, lk(*c, i)) < q by {
                    if i < mid {
                        lemma_lines_le(*c, i, mid as int);
                    }
                }
            }
            lo = mid + 1;
        } else {
            proof {
                assert forall|i: int| mid <= i < c.n_l implies #[trigger] rpos(*c, lk(*c, i)) >= q by {
                    lemma_lines_le(*c, mid as int, i);
                }
            }
            hi = mid;
        }
    }
    lo
}

/// The stored lineitem range to scan: the lines of the orders inside the zone-map window when the lines follow the
/// orders, else all rows.
pub fn scan_bounds(c: &Cols, f: &PFilter, nt: &NTab, clustered: bool, zm: &[i64]) -> (r: (usize, usize))
    requires cols_ok(*c), clustered ==> lines_clustered(*c), zone_ok(*c, zm@),
    ensures bounds_ok(*c, *f, *nt, r.0 as int, r.1 as int),
{
    if !clustered {
        return (0, c.n_l);
    }
    let (qa, qb) = orders_bounds(c, zm);
    let la = first_line(c, qa);
    let lb = first_line(c, qb);
    proof {
        let (pm, ns) = (pm_of(*f), nt_view(*nt));
        if la > lb {
            assert(rpos(*c, lk(*c, lb as int)) >= qb);
            assert(rpos(*c, lk(*c, lb as int)) < qa);
        }
        assert forall|j: int| 0 <= j < la implies #[trigger] lc(*c, pm, ns, j) is None by {
            assert(rpos(*c, lk(*c, j)) < qa);
            lemma_rpos(*c, lk(*c, j));
        }
        assert forall|j: int| lb <= j < c.n_l implies #[trigger] lc(*c, pm, ns, j) is None by {
            assert(rpos(*c, lk(*c, j)) >= qb);
            lemma_rpos(*c, lk(*c, j));
        }
    }
    (la, lb)
}

} // verus!
