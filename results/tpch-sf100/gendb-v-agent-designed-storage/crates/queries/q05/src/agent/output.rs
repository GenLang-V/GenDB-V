//! The result rows: one row `(n_name, revenue)` per group with a qualifying row, in descending revenue order
//! (`build_rows`); they are an allowed output of the normal form (`link::query::result_ok`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::order::*;
use crate::spec::ast::*;
use crate::exec::value::*;
use crate::link::query::*;
use crate::link::expr::{lemma_align_same, lemma_compare_num};
use crate::agent::q5spec::*;
use crate::agent::chain::*;
use crate::agent::dims::names_view;
use crate::agent::common::order::*;

verus! {

/// The normal form's groups are the computed groups: their counts and sums, and no other group has a row.
pub open spec fn groups_nf(g: QuerySpec, xs: Seq<Row>, gn: Seq<Seq<u8>>, cnt: Seq<usize>, sum: Seq<i128>) -> bool {
    &&& cnt.len() == gn.len() && sum.len() == gn.len()
    &&& forall|gi: int| 0 <= gi < gn.len() ==> #[trigger] gcount(g, xs, gkey(gn, gi)) == cnt[gi]
            && gsum(g, xs, gkey(gn, gi), 0) == sum[gi]
    &&& forall|k: Row| #[trigger] gcount(g, xs, k) > 0 ==> exists|gi: int| 0 <= gi < gn.len() && k == #[trigger] gkey(gn, gi)
    &&& forall|a: int, b: int| 0 <= a < gn.len() && 0 <= b < gn.len() && a != b ==> #[trigger] gn[a] != #[trigger] gn[b]
}

/// A result row `(name, revenue)`.
pub open spec fn res_row(name: Seq<u8>, s: int) -> Row {
    seq![Val::Text(name), Val::Num { coeff: s, scale: 4 }]
}

/// Revenue `sa >= sb` puts row `a` before row `b` under `ORDER BY revenue DESC`.
proof fn lemma_desc_cmp(na: Seq<u8>, sa: int, nb: Seq<u8>, sb: int)
    requires sa >= sb,
    ensures keys_cmp(q5_order(), res_row(na, sa), res_row(nb, sb)) <= 0,
{
    lemma_compare_num(sa, 4, sb, 4);
    lemma_align_same(sa, 4);
    lemma_align_same(sb, 4);
    let ra = res_row(na, sa);
    let rb = res_row(nb, sb);
    let k0 = q5_order()[0];
    assert(ra[1] == Val::Num { coeff: sa, scale: 4 });
    assert(rb[1] == Val::Num { coeff: sb, scale: 4 });
    assert(max_nat(4, 4) == 4);
    assert(compare(ra[1], rb[1]) == Some(sign(sa - sb)));
    assert(key_cmp(k0, ra, rb) == -sign(sa - sb));
    assert(q5_order().drop_first() =~= Seq::<OrderKey>::empty());
    assert(keys_cmp(Seq::<OrderKey>::empty(), ra, rb) == 0);
    assert(keys_cmp(q5_order(), ra, rb) == if key_cmp(k0, ra, rb) != 0 { key_cmp(k0, ra, rb) }
        else { keys_cmp(q5_order().drop_first(), ra, rb) });
}

/// A group's output row under the normal form.
proof fn lemma_out_row(g: QuerySpec, xs: Seq<Row>, prm: Prm, name: Seq<u8>)
    requires g == q5_g(prm), gcount(g, xs, name_key(name)) > 0,
    ensures out_row(g, xs, name_key(name)) == res_row(name, gsum(g, xs, name_key(name), 0)),
{
    let k = name_key(name);
    let fr = full_row(g, xs, k);
    assert(agg_outs(g, xs, k) =~= seq![Val::Num { coeff: gsum(g, xs, k, 0), scale: 4 }]);
    assert(fr =~= res_row(name, gsum(g, xs, k, 0)));
    assert(select(fr, g.outs) =~= fr);
}

/// Owned copy of a byte vector.
fn copy_bytes(v: &Vec<u8>) -> (r: Vec<u8>)
    ensures r@ == v@,
{
    let mut r: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v@.len(), r@ == v@.subrange(0, i as int),
        decreases v@.len() - i,
    {
        r.push(v[i]);
        i = i + 1;
        proof {
            assert(r@ =~= v@.subrange(0, i as int));
        }
    }
    proof {
        assert(v@.subrange(0, v@.len() as int) =~= v@);
    }
    r
}

/// The groups with a qualifying row, by descending revenue.
pub fn build_rows(cnt: &Vec<usize>, sum: &Vec<i128>, gnames: &Vec<Vec<u8>>, prm: Ghost<Prm>, xs: Ghost<Seq<Row>>)
    -> (rows: Vec<Vec<EVal>>)
    requires groups_nf(q5_g(prm@), xs@, names_view(gnames@), cnt@, sum@),
    ensures result_ok(q5_g(prm@), q5_order(), 0, None, xs@, view_rows(rows@)),
{
    let ghost g = q5_g(prm@);
    let ghost gn = names_view(gnames@);
    let ng = cnt.len();
    // the groups with rows, in group order
    let mut sel: Vec<usize> = Vec::new();
    let mut keys: Vec<i128> = Vec::new();
    let mut gi: usize = 0;
    while gi < ng
        invariant
            ng == cnt@.len(), ng == sum@.len(), ng == gn.len(),
            gi <= ng,
            sel@.len() == keys@.len(),
            forall|s: int| 0 <= s < sel@.len() ==> #[trigger] sel@[s] < gi && cnt@[sel@[s] as int] > 0
                && keys@[s] == sum@[sel@[s] as int],
            forall|a: int, b: int| 0 <= a < b < sel@.len() ==> #[trigger] sel@[a] < #[trigger] sel@[b],
            forall|h: int| 0 <= h < gi && cnt@[h] > 0 ==> exists|s: int| 0 <= s < sel@.len() && #[trigger] sel@[s] == h,
        decreases ng - gi,
    {
        if cnt[gi] > 0 {
            let ghost old_sel = sel@;
            sel.push(gi);
            keys.push(sum[gi]);
            proof {
                assert forall|h: int| 0 <= h < gi + 1 && cnt@[h] > 0 implies exists|s: int| 0 <= s < sel@.len() && #[trigger] sel@[s] == h by {
                    if h < gi {
                        let s = choose|s: int| 0 <= s < old_sel.len() && old_sel[s] == h;
                        assert(sel@[s] == h);
                    } else {
                        assert(sel@[old_sel.len() as int] == h);
                    }
                }
            }
        }
        gi = gi + 1;
    }
    let ord = order_desc(&keys);
    let n = ord.len();
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let mut r: usize = 0;
    while r < n
        invariant
            n == ord@.len(), n == sel@.len(), sel@.len() == keys@.len(),
            ng == cnt@.len(), ng == sum@.len(), ng == gnames@.len(),
            is_index_perm(ord@, n as int),
            forall|s: int| 0 <= s < sel@.len() ==> #[trigger] sel@[s] < ng && keys@[s] == sum@[sel@[s] as int],
            r <= n,
            rows@.len() == r,
            forall|x: int| 0 <= x < r ==> #[trigger] view_rows(rows@)[x]
                == res_row(gnames@[sel@[ord@[x] as int] as int]@, sum@[sel@[ord@[x] as int] as int] as int),
        decreases n - r,
    {
        let s = ord[r];
        let gsel = sel[s];
        let name = copy_bytes(&gnames[gsel]);
        let mut row: Vec<EVal> = Vec::new();
        row.push(EVal::Text(name));
        row.push(EVal::Num { coeff: sum[gsel], scale: 4 });
        let ghost old_rows = rows@;
        rows.push(row);
        proof {
            assert(view_row(row@) =~= res_row(gnames@[gsel as int]@, sum@[gsel as int] as int));
            assert forall|x: int| 0 <= x < r + 1 implies #[trigger] view_rows(rows@)[x]
                == res_row(gnames@[sel@[ord@[x] as int] as int]@, sum@[sel@[ord@[x] as int] as int] as int) by {
                if x < r {
                    assert(rows@[x] == old_rows[x]);
                    assert(view_rows(old_rows)[x] == view_rows(rows@)[x]);
                }
            }
        }
        r = r + 1;
    }
    proof {
        let out = view_rows(rows@);
        let ks = Seq::new(n as nat, |x: int| gkey(gn, sel@[ord@[x] as int] as int));
        assert forall|x: int| 0 <= x < n implies #[trigger] ord@[x] < n && sel@[ord@[x] as int] < ng && cnt@[sel@[ord@[x] as int] as int] > 0 by {
            assert(ord@[x] < n);
        }
        // distinct keys
        assert forall|a: int, b: int| 0 <= a < ks.len() && 0 <= b < ks.len() && a != b implies ks[a] != ks[b] by {
            let (sa, sb) = (ord@[a] as int, ord@[b] as int);
            assert(sa != sb);
            if sel@[sa] == sel@[sb] {
                if sa < sb {
                    assert(sel@[sa] < sel@[sb]);
                } else {
                    assert(sel@[sb] < sel@[sa]);
                }
            }
            lemma_gkey_eq(gn, sel@[sa] as int, sel@[sb] as int);
        }
        assert(ks.no_duplicates());
        // the keys are exactly the groups with a row
        assert forall|k: Row| #[trigger] ks.contains(k) <==> gcount(g, xs@, k) > 0 by {
            if ks.contains(k) {
                let x = choose|x: int| 0 <= x < ks.len() && ks[x] == k;
                let gsel = sel@[ord@[x] as int] as int;
                assert(gcount(g, xs@, gkey(gn, gsel)) == cnt@[gsel]);
            }
            if gcount(g, xs@, k) > 0 {
                let h = choose|h: int| 0 <= h < gn.len() && k == #[trigger] gkey(gn, h);
                assert(gcount(g, xs@, gkey(gn, h)) == cnt@[h]);
                let s = choose|s: int| 0 <= s < sel@.len() && #[trigger] sel@[s] == h;
                assert(covers(ord@, s));
                let x = choose|x: int| 0 <= x < ord@.len() && ord@[x] == s;
                assert(ks[x] == k);
            }
        }
        // the rows are the groups' output rows
        assert forall|x: int| 0 <= x < out.len() implies #[trigger] out[x] == out_row(g, xs@, ks[x]) by {
            let gsel = sel@[ord@[x] as int] as int;
            assert(gcount(g, xs@, gkey(gn, gsel)) == cnt@[gsel]);
            lemma_out_row(g, xs@, prm@, gn[gsel]);
        }
        // in descending revenue order
        assert forall|a: int, b: int| 0 <= a < b < out.len() implies keys_cmp(q5_order(), #[trigger] out[a], #[trigger] out[b]) <= 0 by {
            let (ga, gb) = (sel@[ord@[a] as int] as int, sel@[ord@[b] as int] as int);
            assert(keys@[ord@[a] as int] >= keys@[ord@[b] as int]);
            lemma_desc_cmp(gnames@[ga]@, sum@[ga] as int, gnames@[gb]@, sum@[gb] as int);
        }
        assert(sorted_by(q5_order(), out));
        lemma_result_from_keys(g, q5_order(), 0, None, xs@, ks, out);
        lemma_slice_all(out);
    }
    rows
}

} // verus!
