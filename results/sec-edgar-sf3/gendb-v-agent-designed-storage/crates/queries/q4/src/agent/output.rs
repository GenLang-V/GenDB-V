//! ORDER BY total_value DESC LIMIT 500 over the emitted groups: the groups sorted by `-sum` (a permutation of their
//! rows, sorted by the ORDER BY key), the first 500 rendered as result rows.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::spec::numeric::*;
use crate::exec::value::*;
use crate::link::query::view_rows;
use crate::stores::tag_tv::interface as T;
use crate::stores::num::interface::common::text::{text_entry, text_entry_of, text_parts_wf};
use crate::agent::common::sort::*;
use crate::agent::group::num4;
use crate::agent::sem::order_keys;
use crate::agent::filing::*;
use crate::agent::agg::*;
use crate::agent::result::*;
use crate::agent::maps::Dict;
use crate::agent::inputs::{u64v, u8v};

verus! {

fn copy_bytes(s: &[u8]) -> (v: Vec<u8>)
    ensures v@ == s@,
{
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant i <= s@.len(), v@ == s@.subrange(0, i as int),
        decreases s@.len() - i,
    {
        v.push(s[i]);
        i = i + 1;
        proof { assert(v@ =~= s@.subrange(0, i as int)); }
    }
    proof { assert(s@.subrange(0, s@.len() as int) =~= s@); }
    v
}

/// The row of a sorted entry.
pub open spec fn prow(cx: Cx, gs: Seq<Grp>) -> spec_fn((i128, u64)) -> Row {
    |x: (i128, u64)| grp_row(cx, gs[x.1 as int])
}

pub open spec fn gkey(gs: Seq<Grp>) -> spec_fn(int) -> (i128, u64) {
    |i: int| ((-(gs[i].sum as int)) as i128, i as u64)
}

/// The ORDER BY key comparison of two group rows: SUM descending.
proof fn lemma_cmp_rows(cx: Cx, a: Grp, b: Grp)
    requires a.sum >= b.sum,
    ensures keys_cmp(order_keys(), grp_row(cx, a), grp_row(cx, b)) <= 0,
{
    let (ra, rb) = (grp_row(cx, a), grp_row(cx, b));
    let k = order_keys();
    assert(ra[4] == num4(a.sum as int) && rb[4] == num4(b.sum as int));
    crate::bridge::order::lemma_num_cmp_at(a.sum as int, 4, b.sum as int, 4, 4);
    assert(pow10(0) == 1) by (compute);
    assert(align(a.sum as int, 4, 4) == a.sum as int);
    assert(align(b.sum as int, 4, 4) == b.sum as int);
    assert(num_cmp(a.sum as int, 4, b.sum as int, 4) >= 0);
    assert(key_cmp(k[0], ra, rb) <= 0);
    assert(k.drop_first().len() == 0);
    assert(keys_cmp(k.drop_first(), ra, rb) == 0);
}

/// The result rows: the groups by SUM descending (`p`, a sorted permutation of their rows), the first 500 rendered.
pub fn build_output(gs: &Vec<Grp>, tl: &Dict, b1: &[u8], Ghost(cx): Ghost<Cx>, Ghost(fs): Ghost<Seq<i32>>, Ghost(fc): Ghost<Seq<i32>>,
    Ghost(cs): Ghost<Seq<crate::agent::join::Contrib>>) -> (r: (Vec<Vec<EVal>>, Ghost<Seq<Row>>))
    requires
        forall|i: int| 0 <= i < gs@.len() ==> grp_ok(fs, fc, cs, ntl(cx) + 1, #[trigger] gs@[i]),
        tl.off@ == u64v(cx.tag[T::P_TLABEL_OFF as int]), tl.bytes@ == u8v(cx.tag[T::P_TLABEL_OFF + 1]), tl.n == ntl(cx),
        text_parts_wf(tl.off@, tl.bytes@, tl.n as int),
        b1@ == cx.b1,
    ensures
        r.1@.to_multiset() == grp_rows(cx, gs@).to_multiset(),
        sorted_by(order_keys(), r.1@),
        view_rows(r.0@) == slice_rows(r.1@, 0, Some(500nat)),
{
    let m = gs.len();
    let mut v: Vec<(i128, u64)> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            i <= m, m == gs@.len(), v@.len() == i,
            forall|i: int| 0 <= i < gs@.len() ==> grp_ok(fs, fc, cs, ntl(cx) + 1, #[trigger] gs@[i]),
            forall|k: int| 0 <= k < i ==> #[trigger] v@[k] == gkey(gs@)(k),
        decreases m - i,
    {
        proof {
            assert(grp_ok(fs, fc, cs, ntl(cx) + 1, gs@[i as int]));
        }
        v.push((-gs[i].sum, i as u64));
        i = i + 1;
    }
    let w = merge_sort(&v);
    let ghost f = prow(cx, gs@);
    let ghost p = w@.map_values(f);
    proof {
        w@.to_multiset_ensures();
        v@.to_multiset_ensures();
        assert(w@.len() == v@.len());
        crate::link::query::lemma_map_multiset(w@, v@, f);
        assert(v@.map_values(f) =~= grp_rows(cx, gs@)) by {
            assert forall|k: int| 0 <= k < v@.len() implies #[trigger] v@.map_values(f)[k] == grp_rows(cx, gs@)[k] by {
                assert(v@[k] == gkey(gs@)(k));
            }
        }
        // Every sorted entry is some group's key.
        assert forall|j: int| 0 <= j < w@.len() implies (#[trigger] w@[j]).1 < m && w@[j] == gkey(gs@)(w@[j].1 as int) by {
            w@.to_multiset_ensures();
            v@.to_multiset_ensures();
            assert(w@.to_multiset().count(w@[j]) > 0);
            assert(v@.contains(w@[j]));
            let k = choose|k: int| 0 <= k < v@.len() && v@[k] == w@[j];
            assert(v@[k] == gkey(gs@)(k));
        }
        assert forall|a: int, b: int| 0 <= a < b < p.len() implies keys_cmp(order_keys(), #[trigger] p[a], #[trigger] p[b]) <= 0 by {
            assert(w@[a].0 <= w@[b].0);
            let (ga, gb) = (gs@[w@[a].1 as int], gs@[w@[b].1 as int]);
            assert(w@[a] == gkey(gs@)(w@[a].1 as int) && w@[b] == gkey(gs@)(w@[b].1 as int));
            lemma_cmp_rows(cx, ga, gb);
        }
    }
    let lim: usize = if m < 500 { m } else { 500 };
    let mut out: Vec<Vec<EVal>> = Vec::new();
    let mut j: usize = 0;
    while j < lim
        invariant
            j <= lim, lim <= m, m == gs@.len(), w@.len() == m, p == w@.map_values(f), f == prow(cx, gs@),
            forall|i: int| 0 <= i < gs@.len() ==> grp_ok(fs, fc, cs, ntl(cx) + 1, #[trigger] gs@[i]),
            forall|j: int| 0 <= j < w@.len() ==> (#[trigger] w@[j]).1 < m,
            tl.off@ == u64v(cx.tag[T::P_TLABEL_OFF as int]), tl.bytes@ == u8v(cx.tag[T::P_TLABEL_OFF + 1]), tl.n == ntl(cx),
            text_parts_wf(tl.off@, tl.bytes@, tl.n as int),
            b1@ == cx.b1,
            view_rows(out@) == p.subrange(0, j as int),
        decreases lim - j,
    {
        proof { assert(w@[j as int].1 < m); }
        let gi = w[j].1 as usize;
        let g = &gs[gi];
        proof {
            assert(grp_ok(fs, fc, cs, ntl(cx) + 1, *g));
            lemma_aciks_bound(fs, fc, cs, 0, cs.len() as int, g.sic as int, g.slot as int);
        }
        let tv = if g.slot == tl.n as u64 {
            EVal::Null
        } else {
            let (s, _) = text_entry_of(tl.off, tl.bytes, tl.n, g.slot as usize);
            EVal::Text(copy_bytes(s))
        };
        proof {
            if g.slot != tl.n as u64 {
                assert(tl_val(cx, g.slot as int) == Val::Text(text_entry(tl.off@, tl.bytes@, g.slot as int)));
            }
            assert(tv@ == tl_val(cx, g.slot as int));
        }
        let mut row: Vec<EVal> = Vec::new();
        row.push(EVal::Int(g.sic as i64));
        row.push(tv);
        row.push(EVal::Text(copy_bytes(b1)));
        row.push(EVal::Int(g.dcnt as i64));
        row.push(EVal::Num { coeff: g.sum, scale: 4 });
        row.push(clone_val(&g.avg));
        proof {
            assert(view_row(row@) =~= grp_row(cx, *g));
            assert(p[j as int] == grp_row(cx, *g));
            crate::link::outcome::lemma_view_rows_push(out@, row);
        }
        out.push(row);
        proof { assert(view_rows(out@) =~= p.subrange(0, j + 1)); }
        j = j + 1;
    }
    proof {
        assert(slice_rows(p, 0, Some(500nat)) == p.subrange(0, lim as int));
    }
    (out, Ghost(p))
}

} // verus!
