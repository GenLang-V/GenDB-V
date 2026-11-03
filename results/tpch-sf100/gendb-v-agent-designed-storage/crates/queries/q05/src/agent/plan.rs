//! The scan plan: the stored orders range `[p0, p1)` that can hold dates of the window, from the date zone maps
//! (`candidate_range`); lineitem rows whose orders lie outside it take part in no group (`lemma_outside_zero`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::datetime::*;
use crate::link::join::*;
use crate::stores::facts::interface::cluster::{order_pos, first_key_from};
use crate::agent::q5spec::*;
use crate::agent::lookup::*;
use crate::agent::chain::*;
use crate::agent::kernel::*;
use crate::agent::setup::*;
use crate::agent::common::forview::*;

verus! {

/// Rows `[0, p0)` and `[p1, n_o)` of the stored orders have dates outside `[lo_day, hi_day)`.
pub open spec fn range_ok(c: OrdCols, lo_day: i64, hi_day: i64, p0: int, p1: int) -> bool {
    &&& 0 <= p0 <= p1 <= c.n_o
    &&& forall|q: int| 0 <= q < c.n_o && (q < p0 || q >= p1) ==>
            (#[trigger] fv16(c.od_c@, c.od_b@, c.div.bs as int, q) < lo_day || fv16(c.od_c@, c.od_b@, c.div.bs as int, q) >= hi_day)
}

/// Block `g` holds no date of the window by its zone map.
pub open spec fn noncand(c: OrdCols, lo_day: i64, hi_day: i64, g: int) -> bool {
    c.od_z@[g] < lo_day || c.od_b@[g] >= hi_day
}

/// The rows of a block without window dates have no window date.
proof fn lemma_block_out(c: OrdCols, rs: Rels, lo_day: i64, hi_day: i64, q: int)
    requires ord_cols_ok(c, rs), 0 <= q < c.n_o, noncand(c, lo_day, hi_day, q / (c.div.bs as int)),
    ensures
        fv16(c.od_c@, c.od_b@, c.div.bs as int, q) < lo_day || fv16(c.od_c@, c.od_b@, c.div.bs as int, q) >= hi_day,
{
    assert(ord_zone_ok(c, q));
}

/// The smallest stored orders range holding every block whose zone map meets the window.
pub fn candidate_range(c: &OrdCols, lo_day: i64, hi_day: i64, rs: Ghost<Rels>) -> (r: (usize, usize))
    requires ord_cols_ok(*c, rs@),
    ensures range_ok(*c, lo_day, hi_day, r.0 as int, r.1 as int),
{
    let ng = c.od_b.len();
    let bs = c.div.bs;
    let mut g: usize = 0;
    let mut found = false;
    let mut g0: usize = 0;
    let mut g1: usize = 0;
    while g < ng
        invariant
            ord_cols_ok(*c, rs@),
            ng == c.od_b@.len(), ng == c.od_z@.len(), bs == c.div.bs,
            g <= ng,
            !found ==> forall|h: int| 0 <= h < g ==> #[trigger] noncand(*c, lo_day, hi_day, h),
            found ==> g0 < g1 <= g,
            found ==> forall|h: int| 0 <= h < g && (h < g0 || h >= g1) ==> #[trigger] noncand(*c, lo_day, hi_day, h),
        decreases ng - g,
    {
        if c.od_z[g] >= lo_day && c.od_b[g] < hi_day {
            if !found {
                g0 = g;
                found = true;
            }
            g1 = g + 1;
        }
        g = g + 1;
    }
    let n = c.n_o;
    if !found {
        proof {
            assert forall|q: int| 0 <= q < n implies
                (#[trigger] fv16(c.od_c@, c.od_b@, bs as int, q) < lo_day || fv16(c.od_c@, c.od_b@, bs as int, q) >= hi_day) by {
                lemma_block_index(q, bs as int, ng as int);
                lemma_block_out(*c, rs@, lo_day, hi_day, q);
            }
        }
        return (0, 0);
    }
    proof {
        let m = 0xffff_ffff_ffff_ffffint;
        assert(g0 as int <= m && g1 as int <= m && bs as int <= m);
        assert((g0 as int) * (bs as int) <= m * m) by (nonlinear_arith) requires 0 <= g0 <= m, 0 <= bs <= m;
        assert((g1 as int) * (bs as int) <= m * m) by (nonlinear_arith) requires 0 <= g1 <= m, 0 <= bs <= m;
    }
    let a = (g0 as u128) * (bs as u128);
    let b = (g1 as u128) * (bs as u128);
    let p0: usize = if a < n as u128 { a as usize } else { n };
    let p1: usize = if b < n as u128 { b as usize } else { n };
    proof {
        assert((g0 as int) * (bs as int) <= (g1 as int) * (bs as int)) by (nonlinear_arith) requires g0 < g1, bs >= 1;
        assert forall|q: int| 0 <= q < n && (q < p0 || q >= p1) implies
            (#[trigger] fv16(c.od_c@, c.od_b@, bs as int, q) < lo_day || fv16(c.od_c@, c.od_b@, bs as int, q) >= hi_day) by {
            lemma_block_index(q, bs as int, ng as int);
            let h = q / (bs as int);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(q, bs as int);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(q, bs as int);
            assert((bs as int) * h == h * (bs as int)) by (nonlinear_arith);
            if q < p0 {
                assert(h < g0) by (nonlinear_arith) requires q < g0 * bs, h * bs <= q, bs >= 1;
            } else {
                assert(q >= g1 * bs);
                assert(h >= g1) by (nonlinear_arith) requires q >= g1 * bs, q < h * bs + bs, bs >= 1;
            }
            lemma_block_out(*c, rs@, lo_day, hi_day, q);
        }
    }
    (p0, p1)
}

/// `first_key_from` skips exactly the rows without the key.
proof fn lemma_fkf_none(orows: Seq<Row>, k: Val, i: int)
    requires 0 <= i,
    ensures
        forall|q: int| i <= q < first_key_from(orows, k, i) && q < orows.len() ==> #[trigger] orows[q][0] != k,
        first_key_from(orows, k, i) < orows.len() ==> orows[first_key_from(orows, k, i)][0] == k,
        first_key_from(orows, k, i) <= orows.len(),
    decreases orows.len() - i,
{
    if i < orows.len() && orows[i][0] != k {
        lemma_fkf_none(orows, k, i + 1);
    }
}

/// A stored lineitem row whose order position lies outside `[p0, p1)` takes part in no group.
pub proof fn lemma_outside_zero(t: ScanCtx, c: OrdCols, p0: int, p1: int, j: int, k: Row)
    requires
        t.wf(),
        range_ok(c, t.lo_day, t.hi_day, p0, p1),
        c.n_o == t.n_o, c.od_c == t.od_c, c.od_b == t.od_b, c.div == t.odiv,
        0 <= j < t.n_l,
        t.op(j) < p0 || t.op(j) >= p1,
    ensures line_mult(t.rs@, t.prm@, k, t.lrows@[j]) == 0,
{
    let rs = t.rs@;
    let l = t.lrows@[j];
    let q = t.op(j);
    lemma_fkf_none(t.orows@, l[0], 0);
    crate::stores::facts::interface::cluster::lemma_order_pos_bound(t.orows@, l[0]);
    if q < t.n_o {
        assert(t.orow_ok(q));
        assert(fv16(c.od_c@, c.od_b@, c.div.bs as int, q) < t.lo_day || fv16(c.od_c@, c.od_b@, c.div.bs as int, q) >= t.hi_day);
        let oi = t.omap@[q];
        let d = fv16(t.od_c@, t.od_b@, t.odiv.bs as int, q);
        assert(rs.o[oi][4] == Val::Date(d));
        assert(d < t.lo_day || d >= t.hi_day);
        let u = usecs_per_day();
        if d >= t.hi_day {
            assert(d * u >= t.hi_day * u) by (nonlinear_arith) requires d >= t.hi_day, u > 0;
        }
        assert(!date_ok(rs.o[oi], t.prm@));
        lemma_mult_out_of_window(rs, t.prm@, k, l, oi);
    } else {
        assert forall|i: int| 0 <= i < rs.o.len() implies #[trigger] rs.o[i][0] != l[0] by {
            assert(t.o_covered(i));
            let p = choose|p: int| 0 <= p < t.n_o && #[trigger] t.omap@[p] == i;
            assert(t.orow_ok(p));
        }
        lemma_mult_no_order(rs, t.prm@, k, l);
    }
}

} // verus!
