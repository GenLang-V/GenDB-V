//! Result candidates of Q18 and their top-100 buffer. A candidate is a good order with its customer row, keys,
//! date, total price and quantity sum; its result row is `cand_row` (c_name read from the model). The buffer keeps
//! the first `K` candidates by o_totalprice DESC, o_orderdate (`topk_insert`, sorted insertion with truncation),
//! with `common::topk::topk_ok` as its specification; ties may come in any order.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::{max_nat, sign};
use crate::spec::order::{keys_cmp, key_cmp};
use crate::spec::ast::OrderKey;
use crate::link::expr::{lemma_compare_num, lemma_compare_date, lemma_align_same};
use crate::bridge::order::{keys_ok, key_ok, lemma_keys_cmp_antisym, lemma_keys_cmp_trans};
use crate::gendb_entry::work::put;
use super::common::topk::*;
use super::model::*;
use super::qspec::*;

verus! {

/// LIMIT 100.
pub const K: usize = 100;

/// A candidate: the order at stored position `q` (key `okey`, customer key `ck`, date in days, total price
/// coefficient `tp`), its customer row `cpos` and its quantity sum coefficient `sum` (both scale 2).
#[derive(Clone, Copy)]
pub struct Cand {
    pub q: usize,
    pub okey: i64,
    pub ck: i64,
    pub cpos: usize,
    pub date: i64,
    pub tp: i64,
    pub sum: i128,
}

/// The result row of a candidate: c_name, c_custkey, o_orderkey, o_orderdate, o_totalprice, SUM(l_quantity).
pub open spec fn cand_row(m: M, c: Cand) -> Row {
    seq![
        Val::Text(cname(m, c.cpos as int)),
        Val::Int(c.ck as int),
        Val::Int(c.okey as int),
        Val::Date(c.date as int),
        Val::Num { coeff: c.tp as int, scale: 2 },
        Val::Num { coeff: c.sum as int, scale: 2 },
    ]
}

/// The first `len` candidates of a buffer, as rows.
pub open spec fn cands_view(m: M, buf: Seq<Cand>, len: int) -> Seq<Row> {
    Seq::new(len as nat, |i: int| cand_row(m, buf[i]))
}

/// The ORDER BY comparison of two candidate rows: o_totalprice DESC, then o_orderdate.
pub proof fn lemma_cand_cmp(m: M, a: Cand, b: Cand)
    ensures
        keys_cmp(q18_keys(), cand_row(m, a), cand_row(m, b)) == (if a.tp != b.tp {
            if a.tp > b.tp { -1int } else { 1int }
        } else if a.date < b.date { -1int } else if a.date > b.date { 1int } else { 0int }),
        keys_ok(q18_keys(), q18_fams(), cand_row(m, a)),
{
    let (ra, rb) = (cand_row(m, a), cand_row(m, b));
    let keys = q18_keys();
    let k0 = keys[0];
    let k1 = keys.drop_first();
    assert(k0 == OrderKey { col: 4, desc: true, nulls_first: true });
    assert(k1[0] == OrderKey { col: 3, desc: false, nulls_first: false });
    assert(k1.len() == 1);
    lemma_compare_num(a.tp as int, 2, b.tp as int, 2);
    lemma_align_same(a.tp as int, 2);
    lemma_align_same(b.tp as int, 2);
    assert(max_nat(2, 2) == 2);
    lemma_compare_date(a.date as int, b.date as int);
    assert(ra[4] == (Val::Num { coeff: a.tp as int, scale: 2 }) && rb[4] == (Val::Num { coeff: b.tp as int, scale: 2 }));
    assert(ra[3] == Val::Date(a.date as int) && rb[3] == Val::Date(b.date as int));
    let c0 = key_cmp(k0, ra, rb);
    let c1 = key_cmp(k1[0], ra, rb);
    assert(c0 == -sign(a.tp as int - b.tp as int));
    assert(c1 == sign(a.date as int - b.date as int));
    assert(k1.drop_first().len() == 0);
    assert(keys_cmp(k1.drop_first(), ra, rb) == 0);
    assert(keys_cmp(k1, ra, rb) == c1);
    assert(keys_cmp(keys, ra, rb) == if c0 != 0 { c0 } else { c1 });
    assert forall|t: int| 0 <= t < keys.len() implies #[trigger] key_ok(keys[t], q18_fams()[t], ra) by {}
}

/// `a` comes strictly before `b`: larger total price, or equal total price and earlier date.
pub fn better(a: &Cand, b: &Cand, Ghost(m): Ghost<M>) -> (r: bool)
    ensures r == (keys_cmp(q18_keys(), cand_row(m, *a), cand_row(m, *b)) < 0),
    no_unwind
{
    proof { lemma_cand_cmp(m, *a, *b); }
    a.tp > b.tp || (a.tp == b.tp && a.date < b.date)
}

pub proof fn lemma_view_last(m: M, buf: Seq<Cand>, len: int)
    requires 0 < len <= buf.len(),
    ensures cands_view(m, buf, len).last() == cand_row(m, buf[len - 1]), cands_view(m, buf, len).len() == len,
{
}

/// One more candidate of a buffer, as rows.
pub proof fn lemma_view_push(m: M, buf: Seq<Cand>, i: int)
    requires 0 <= i < buf.len(),
    ensures cands_view(m, buf, i + 1) == cands_view(m, buf, i).push(cand_row(m, buf[i])),
{
    assert(cands_view(m, buf, i + 1) =~= cands_view(m, buf, i).push(cand_row(m, buf[i])));
}

/// The sorted position of a candidate in a sorted buffer: after every row not above it.
fn find_pos(buf: &Vec<Cand>, len: usize, c: Cand, Ghost(m): Ghost<M>, Ghost(all): Ghost<Seq<Row>>) -> (pos: usize)
    requires
        buf@.len() == K,
        len <= K,
        topk_ok(q18_keys(), q18_fams(), K as nat, cands_view(m, buf@, len as int), all),
        len == K ==> keys_cmp(q18_keys(), cand_row(m, c), cand_row(m, buf@[K - 1])) < 0,
    ensures
        ins_pos(q18_keys(), cands_view(m, buf@, len as int), pos as int, cand_row(m, c)),
        len < K || pos < len,
    no_unwind
{
    let ghost keys = q18_keys();
    let ghost fams = q18_fams();
    let ghost view = cands_view(m, buf@, len as int);
    let ghost rc = cand_row(m, c);
    proof { lemma_cand_cmp(m, c, c); }
    let mut pos: usize = 0;
    let mut found = false;
    while pos < len && !found
        invariant
            pos <= len <= K,
            buf@.len() == K,
            view == cands_view(m, buf@, len as int),
            rc == cand_row(m, c),
            keys == q18_keys(),
            fams == q18_fams(),
            keys_ok(keys, fams, rc),
            topk_ok(keys, fams, K as nat, view, all),
            forall|i: int| 0 <= i < pos ==> keys_cmp(keys, #[trigger] view[i], rc) <= 0,
            found ==> pos < len && keys_cmp(keys, rc, view[pos as int]) < 0,
        decreases len - pos + if found { 0int } else { 1int },
    {
        let bp = buf[pos];
        let b = better(&c, &bp, Ghost(m));
        proof {
            assert(bp == buf@[pos as int]);
            assert(view[pos as int] == cand_row(m, buf@[pos as int]));
            assert(b == (keys_cmp(keys, rc, view[pos as int]) < 0));
        }
        if b {
            found = true;
        } else {
            proof {
                assert(keys_ok(keys, fams, view[pos as int]));
                lemma_keys_cmp_antisym(keys, fams, rc, view[pos as int]);
                assert(keys_cmp(keys, view[pos as int], rc) <= 0);
                assert forall|i: int| 0 <= i < pos + 1 implies keys_cmp(keys, #[trigger] view[i], rc) <= 0 by {
                    if i < pos {
                    }
                }
            }
            pos = pos + 1;
        }
    }
    proof {
        if pos < len {
            assert(view[pos as int] == cand_row(m, buf@[pos as int]));
            assert(keys_cmp(keys, rc, view[pos as int]) < 0);
            assert(keys_ok(keys, fams, view[pos as int]));
            lemma_keys_cmp_antisym(keys, fams, rc, view[pos as int]);
            assert forall|i: int| pos <= i < len implies keys_cmp(keys, #[trigger] view[i], rc) > 0 by {
                if i > pos {
                    assert(keys_cmp(keys, view[pos as int], view[i]) <= 0);
                    assert(keys_ok(keys, fams, view[i]));
                    if keys_cmp(keys, view[i], rc) <= 0 {
                        lemma_keys_cmp_trans(keys, fams, view[pos as int], view[i], rc);
                    }
                }
            }
        }
        if len == K && pos == K {
            assert(view[K - 1] == cand_row(m, buf@[K - 1]));
            assert(keys_cmp(keys, view[K - 1], rc) <= 0);
            assert(keys_ok(keys, fams, view[K - 1]));
            lemma_keys_cmp_antisym(keys, fams, rc, view[K - 1]);
        }
    }
    pos
}

proof fn lemma_topk_ins_len(view: Seq<Row>, pos: int, r: Row)
    requires 0 <= pos <= view.len(),
    ensures ins_at(view, pos, r, K as nat).len() == min_nat(K as nat, view.len() + 1),
{
}

proof fn lemma_topk_ins_index(view: Seq<Row>, pos: int, r: Row, t: int)
    requires 0 <= pos <= view.len(), 0 <= t < ins_at(view, pos, r, K as nat).len(),
    ensures ins_at(view, pos, r, K as nat)[t] == if t < pos { view[t] } else if t == pos { r } else { view[t - 1] },
{
}

/// Shift the buffer right from `pos` (dropping the last row) and place the candidate at `pos`.
fn shift_insert(buf: &mut Vec<Cand>, len: usize, pos: usize, c: Cand, Ghost(m): Ghost<M>) -> (r: usize)
    requires
        old(buf)@.len() == K,
        pos <= len <= K,
        len < K || pos < len,
    ensures
        final(buf)@.len() == K,
        r <= K,
        cands_view(m, final(buf)@, r as int) == ins_at(cands_view(m, old(buf)@, len as int), pos as int, cand_row(m, c), K as nat),
        forall|t: int| 0 <= t < r ==> #[trigger] final(buf)@[t] == c || exists|u: int| 0 <= u < len && final(buf)@[t] == old(buf)@[u],
    no_unwind
{
    let ghost old_buf = buf@;
    let top: usize = if len < K { len } else { K - 1 };
    let mut i: usize = top;
    while i > pos
        invariant
            pos <= i <= top <= K - 1,
            buf@.len() == K,
            forall|t: int| 0 <= t <= i ==> #[trigger] buf@[t] == old_buf[t],
            forall|t: int| i < t <= top ==> #[trigger] buf@[t] == old_buf[t - 1],
        decreases i,
    {
        let prev = buf[i - 1];
        put(buf, i, prev);
        i = i - 1;
    }
    put(buf, pos, c);
    let r: usize = if len < K { len + 1 } else { len };
    proof {
        let view = cands_view(m, old_buf, len as int);
        let nb = cands_view(m, buf@, r as int);
        let ia = ins_at(view, pos as int, cand_row(m, c), K as nat);
        lemma_topk_ins_len(view, pos as int, cand_row(m, c));
        assert forall|t: int| 0 <= t < nb.len() implies #[trigger] nb[t] == ia[t] by {
            lemma_topk_ins_index(view, pos as int, cand_row(m, c), t);
        }
        assert(nb =~= ia);
        assert forall|t: int| 0 <= t < r implies #[trigger] buf@[t] == c || exists|u: int| 0 <= u < len && buf@[t] == old_buf[u] by {
            if t < pos {
                assert(buf@[t] == old_buf[t]);
            } else if t > pos {
                assert(buf@[t] == old_buf[t - 1]);
            }
        }
    }
    r
}

/// Insert a candidate into a top-100 buffer of the rows `all` (the candidate's row is new): the buffer becomes the
/// top 100 of `all` with the candidate.
pub fn topk_insert(buf: &mut Vec<Cand>, len: usize, c: Cand, Ghost(m): Ghost<M>, Ghost(all): Ghost<Seq<Row>>) -> (r: usize)
    requires
        old(buf)@.len() == K,
        len <= K,
        topk_ok(q18_keys(), q18_fams(), K as nat, cands_view(m, old(buf)@, len as int), all),
        rel_wf(q18_keys(), q18_fams(), all.push(cand_row(m, c))),
    ensures
        final(buf)@.len() == K,
        r <= K,
        topk_ok(q18_keys(), q18_fams(), K as nat, cands_view(m, final(buf)@, r as int), all.push(cand_row(m, c))),
        forall|t: int| 0 <= t < r ==> #[trigger] final(buf)@[t] == c || exists|u: int| 0 <= u < len && final(buf)@[t] == old(buf)@[u],
    no_unwind
{
    let ghost keys = q18_keys();
    let ghost fams = q18_fams();
    let ghost view = cands_view(m, buf@, len as int);
    let ghost rc = cand_row(m, c);
    if len == K {
        if !better(&c, &buf[K - 1], Ghost(m)) {
            proof {
                lemma_view_last(m, buf@, K as int);
                lemma_cand_cmp(m, c, c);
                lemma_cand_cmp(m, buf@[K - 1], buf@[K - 1]);
                lemma_keys_cmp_antisym(keys, fams, rc, cand_row(m, buf@[K - 1]));
                lemma_topk_skip(keys, fams, K as nat, view, all, rc);
            }
            return len;
        }
    }
    let pos = find_pos(buf, len, c, Ghost(m), Ghost(all));
    let r = shift_insert(buf, len, pos, c, Ghost(m));
    proof {
        lemma_topk_insert(keys, fams, K as nat, view, all, rc, pos as int);
    }
    r
}

} // verus!
