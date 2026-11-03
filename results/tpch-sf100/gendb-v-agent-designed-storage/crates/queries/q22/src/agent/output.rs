//! The result rows from the per-group counts and sums: one row `[code, count, sum]` per group that is the first
//! slot of its code (`first_occ`) and has a result row, ordered by the code bytewise (the ORDER BY order) by
//! selection sort over the at most 7 groups.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::text::lex_cmp;
use crate::exec::value::*;
use crate::link::query::view_rows;
use crate::bridge::order::{lemma_lex_cmp_antisym, lemma_lex_cmp_trans};
use crate::stores::custpart::interface::common::read::bytes_cmp;
use super::model::*;
use super::scan::pats_ok;

verus! {

/// Slot `k` is the first slot holding its text (the group of that text).
pub open spec fn first_occ(ps: Seq<Literal>, k: int) -> bool {
    gid(ps, ptext(ps, k)) == k
}

/// The output row of group `k`.
pub open spec fn orow(ps: Seq<Literal>, k: int, c: int, s: int) -> Row {
    seq![Val::Text(ptext(ps, k)), Val::Int(c), Val::Num { coeff: s, scale: 2 }]
}

/// The group order `ord` lists exactly the first slots with a result row, once each, sorted by their codes.
pub open spec fn order_ok(ps: Seq<Literal>, cnts: Seq<u64>, ord: Seq<usize>) -> bool {
    &&& ord.no_duplicates()
    &&& forall|j: int| 0 <= j < ord.len() ==> #[trigger] ord[j] < 7
    &&& forall|k: int| 0 <= k < 7 ==> (ord.contains(k as usize) <==> first_occ(ps, k) && #[trigger] cnts[k] > 0)
    &&& forall|i: int, j: int| 0 <= i < j < ord.len() ==> lex_cmp(ptext(ps, #[trigger] ord[i] as int), ptext(ps, #[trigger] ord[j] as int)) <= 0
}

/// Whether slot `k` is the first slot holding its text.
fn is_first(pats: &Vec<&'static [u8]>, plens: &Vec<usize>, k: usize, Ghost(ps): Ghost<Seq<Literal>>) -> (r: bool)
    requires pats_ok(pats@, plens@, ps), k < 7,
    ensures r == first_occ(ps, k as int),
{
    let ghost t = ptext(ps, k as int);
    let mut j: usize = 0;
    while j < k
        invariant
            j <= k < 7,
            pats_ok(pats@, plens@, ps),
            t == ptext(ps, k as int),
            gid(ps, t) == gid_from(ps, j as int, t),
        decreases k - j,
    {
        let x: &'static [u8] = pats[j];
        let y: &'static [u8] = pats[k];
        if bytes_cmp(x, plens[j], y, plens[k]) == 0 {
            proof {
                crate::bridge::equality::lemma_lex_cmp_zero(x@, y@);
            }
            return false;
        }
        proof {
            crate::bridge::equality::lemma_lex_cmp_zero(x@, y@);
        }
        j = j + 1;
    }
    true
}

/// A copy of a byte slice.
pub fn copy_slice(x: &[u8], len: usize) -> (r: Vec<u8>)
    requires len == x@.len(),
    ensures r@ == x@,
{
    let mut r: Vec<u8> = Vec::with_capacity(len);
    let mut j: usize = 0;
    while j < len
        invariant
            j <= len,
            len == x@.len(),
            r@ == x@.subrange(0, j as int),
        decreases len - j,
    {
        r.push(x[j]);
        proof {
            assert(r@ =~= x@.subrange(0, j + 1));
        }
        j = j + 1;
    }
    proof {
        assert(r@ =~= x@);
    }
    r
}

/// The sorted group order.
pub fn group_order(pats: &Vec<&'static [u8]>, plens: &Vec<usize>, cnts: &Vec<u64>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (ord: Vec<usize>)
    requires pats_ok(pats@, plens@, ps), cnts@.len() == 7,
    ensures order_ok(ps, cnts@, ord@),
{
    // Candidates: first slots with a result row.
    let mut avail: Vec<bool> = Vec::new();
    let mut k: usize = 0;
    while k < 7
        invariant
            k <= 7,
            pats_ok(pats@, plens@, ps),
            cnts@.len() == 7,
            avail@.len() == k,
            forall|m: int| 0 <= m < k ==> #[trigger] avail@[m] == (first_occ(ps, m) && cnts@[m] > 0),
        decreases 7 - k,
    {
        let f = is_first(pats, plens, k, Ghost(ps));
        avail.push(f && cnts[k] > 0);
        k = k + 1;
    }
    let ghost cand = avail@;
    let mut ord: Vec<usize> = Vec::new();
    let mut round: usize = 0;
    let mut done = false;
    while round < 7 && !done
        invariant
            round <= 7,
            ord@.len() == round,
            done ==> forall|q: int| 0 <= q < 7 ==> !(#[trigger] avail@[q]),
            pats_ok(pats@, plens@, ps),
            cnts@.len() == 7,
            avail@.len() == 7,
            cand.len() == 7,
            forall|m: int| 0 <= m < 7 ==> #[trigger] cand[m] == (first_occ(ps, m) && cnts@[m] > 0),
            // `ord` holds the chosen candidates, `avail` the others.
            forall|m: int| 0 <= m < 7 ==> (#[trigger] cand[m] <==> (avail@[m] || ord@.contains(m as usize))),
            forall|m: int| 0 <= m < 7 ==> !(#[trigger] avail@[m] && ord@.contains(m as usize)),
            ord@.no_duplicates(),
            forall|j: int| 0 <= j < ord@.len() ==> #[trigger] ord@[j] < 7,
            forall|i: int, j: int| 0 <= i < j < ord@.len() ==> lex_cmp(ptext(ps, #[trigger] ord@[i] as int), ptext(ps, #[trigger] ord@[j] as int)) <= 0,
            // every chosen code is at most every remaining one
            forall|i: int, m: int| 0 <= i < ord@.len() && 0 <= m < 7 && #[trigger] avail@[m] ==> lex_cmp(ptext(ps, #[trigger] ord@[i] as int), ptext(ps, m)) <= 0,
        decreases 7 - round + if done { 0int } else { 1int },
    {
        // The least remaining code.
        let mut best: usize = 7;
        let mut m: usize = 0;
        while m < 7
            invariant
                m <= 7,
                pats_ok(pats@, plens@, ps),
                avail@.len() == 7,
                best <= 7,
                best < 7 ==> avail@[best as int],
                best == 7 ==> forall|q: int| 0 <= q < m ==> !(#[trigger] avail@[q]),
                best < 7 ==> forall|q: int| 0 <= q < m && #[trigger] avail@[q] ==> lex_cmp(ptext(ps, best as int), ptext(ps, q)) <= 0,
            decreases 7 - m,
        {
            if avail[m] {
                if best == 7 {
                    best = m;
                    proof {
                        lemma_lex_cmp_antisym(ptext(ps, m as int), ptext(ps, m as int));
                    }
                } else {
                    let x: &'static [u8] = pats[m];
                    let y: &'static [u8] = pats[best];
                    let c = bytes_cmp(x, plens[m], y, plens[best]);
                    proof {
                        lemma_lex_cmp_antisym(x@, y@);
                    }
                    if c < 0 {
                        proof {
                            assert forall|q: int| 0 <= q < m + 1 && #[trigger] avail@[q] implies lex_cmp(ptext(ps, m as int), ptext(ps, q)) <= 0 by {
                                if q < m {
                                    lemma_lex_cmp_trans(ptext(ps, m as int), ptext(ps, best as int), ptext(ps, q));
                                } else {
                                    lemma_lex_cmp_antisym(ptext(ps, m as int), ptext(ps, m as int));
                                }
                            }
                        }
                        best = m;
                    }
                }
            }
            m = m + 1;
        }
        if best == 7 {
            done = true;
            continue;
        }
        proof {
            assert(!ord@.contains(best));
            assert forall|i: int| 0 <= i < ord@.len() implies lex_cmp(ptext(ps, #[trigger] ord@[i] as int), ptext(ps, best as int)) <= 0 by {}
        }
        let ghost o0 = ord@;
        let ghost a0 = avail@;
        ord.push(best);
        avail.set(best, false);
        proof {
            assert forall|q: int| 0 <= q < 7 implies (#[trigger] cand[q] <==> (avail@[q] || ord@.contains(q as usize))) by {
                if q == best as int {
                    assert(ord@[ord@.len() - 1] == best);
                } else {
                    assert(ord@.contains(q as usize) == o0.contains(q as usize)) by {
                        if o0.contains(q as usize) {
                            let j = choose|j: int| 0 <= j < o0.len() && o0[j] == q as usize;
                            assert(ord@[j] == q as usize);
                        }
                        if ord@.contains(q as usize) {
                            let j = choose|j: int| 0 <= j < ord@.len() && ord@[j] == q as usize;
                            assert(j < o0.len());
                            assert(o0[j] == q as usize);
                        }
                    }
                }
            }
            assert forall|q: int| 0 <= q < 7 implies !(#[trigger] avail@[q] && ord@.contains(q as usize)) by {
                if avail@[q] && ord@.contains(q as usize) {
                    let j = choose|j: int| 0 <= j < ord@.len() && ord@[j] == q as usize;
                    assert(q != best as int);
                    assert(j < o0.len());
                    assert(o0.contains(q as usize));
                }
            }
            assert(ord@.no_duplicates()) by {
                assert forall|i: int, j: int| 0 <= i < j < ord@.len() implies ord@[i] != ord@[j] by {
                    if j == ord@.len() - 1 {
                        assert(o0.contains(ord@[i]));
                    }
                }
            }
            assert forall|i: int, q: int| 0 <= i < ord@.len() && 0 <= q < 7 && #[trigger] avail@[q] implies lex_cmp(ptext(ps, #[trigger] ord@[i] as int), ptext(ps, q)) <= 0 by {
                assert(a0[q]);
            }
        }
        round = round + 1;
    }
    proof {
        if !done {
            // After 7 rounds every candidate is chosen (`ord` has 7 distinct slots below 7).
            assert forall|q: int| 0 <= q < 7 implies !(#[trigger] avail@[q]) by {
                if avail@[q] {
                    lemma_seven(ord@, q as usize);
                }
            }
        }
        assert forall|q: int| 0 <= q < 7 implies (ord@.contains(q as usize) <==> first_occ(ps, q) && #[trigger] cnts@[q] > 0) by {
            assert(cand[q] == (first_occ(ps, q) && cnts@[q] > 0));
        }
    }
    ord
}

/// Seven distinct slots below 7 include every slot (pigeonhole over the set of slots).
proof fn lemma_seven(ord: Seq<usize>, q: usize)
    requires
        ord.len() == 7,
        ord.no_duplicates(),
        forall|j: int| 0 <= j < ord.len() ==> #[trigger] ord[j] < 7,
        q < 7,
    ensures ord.contains(q),
{
    let oi = ord.map_values(|x: usize| x as int);
    assert(oi.no_duplicates()) by {
        assert forall|i: int, j: int| 0 <= i < oi.len() && 0 <= j < oi.len() && i != j implies oi[i] != oi[j] by {
            assert(ord[i] != ord[j]);
        }
    }
    oi.unique_seq_to_set();
    let s = oi.to_set();
    let r = vstd::set_lib::set_int_range(0, 7);
    vstd::set_lib::lemma_int_range(0, 7);
    if !ord.contains(q) {
        let r2 = r.remove(q as int);
        assert(s.subset_of(r2)) by {
            assert forall|x: int| s.contains(x) implies r2.contains(x) by {
                let j = choose|j: int| 0 <= j < oi.len() && oi[j] == x;
                assert(ord[j] < 7);
                if x == q as int {
                    assert(ord[j] == q);
                }
            }
        }
        vstd::set_lib::lemma_len_subset(s, r2);
        vstd::set::lemma_set_remove_len(r, q as int);
        assert(r.contains(q as int));
        assert(false);
    }
}

/// The result rows `[code, count, sum]` of the groups in order.
pub fn output_rows(pats: &Vec<&'static [u8]>, plens: &Vec<usize>, cnts: &Vec<u64>, sums: &Vec<i128>, ord: &Vec<usize>,
    Ghost(ps): Ghost<Seq<Literal>>) -> (rows: Vec<Vec<EVal>>)
    requires
        pats_ok(pats@, plens@, ps),
        cnts@.len() == 7,
        sums@.len() == 7,
        forall|j: int| 0 <= j < ord@.len() ==> #[trigger] ord@[j] < 7,
        forall|k: int| 0 <= k < 7 ==> #[trigger] cnts@[k] <= i64::MAX,
    ensures
        view_rows(rows@) == ord@.map_values(|k: usize| orow(ps, k as int, cnts@[k as int] as int, sums@[k as int] as int)),
{
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let mut j: usize = 0;
    while j < ord.len()
        invariant
            j <= ord@.len(),
            pats_ok(pats@, plens@, ps),
            cnts@.len() == 7,
            sums@.len() == 7,
            forall|q: int| 0 <= q < ord@.len() ==> #[trigger] ord@[q] < 7,
            forall|k: int| 0 <= k < 7 ==> #[trigger] cnts@[k] <= i64::MAX,
            view_rows(rows@) == ord@.subrange(0, j as int).map_values(|k: usize| orow(ps, k as int, cnts@[k as int] as int, sums@[k as int] as int)),
        decreases ord@.len() - j,
    {
        let k = ord[j];
        let p: &'static [u8] = pats[k];
        let text = copy_slice(p, plens[k]);
        let mut row: Vec<EVal> = Vec::new();
        row.push(EVal::Text(text));
        row.push(EVal::Int(cnts[k] as i64));
        row.push(EVal::Num { coeff: sums[k], scale: 2 });
        proof {
            assert(view_row(row@) =~= orow(ps, k as int, cnts@[k as int] as int, sums@[k as int] as int));
        }
        let ghost r0 = rows@;
        rows.push(row);
        proof {
            assert(rows@ =~= r0.push(row));
            assert(view_rows(rows@) =~= view_rows(r0).push(view_row(row@)));
            assert(ord@.subrange(0, j + 1) =~= ord@.subrange(0, j as int).push(k));
            assert(ord@.subrange(0, j + 1).map_values(|k: usize| orow(ps, k as int, cnts@[k as int] as int, sums@[k as int] as int))
                =~= ord@.subrange(0, j as int).map_values(|k: usize| orow(ps, k as int, cnts@[k as int] as int, sums@[k as int] as int))
                    .push(orow(ps, k as int, cnts@[k as int] as int, sums@[k as int] as int)));
        }
        j = j + 1;
    }
    proof {
        assert(ord@.subrange(0, ord@.len() as int) =~= ord@);
    }
    rows
}

} // verus!
