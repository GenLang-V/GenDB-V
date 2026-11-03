//! Result candidates of Q10 and their top-20 buffer. A candidate is a customer row with its revenue coefficient
//! (scale 4); its result row is `qspec::crow_rev` (the customer's columns, read from the model). The buffer keeps
//! the first `K` candidates by revenue DESC (`topk_insert`, sorted insertion with truncation), with
//! `common::topk::topk_ok` as its specification; ties may come in any order.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::{max_nat, sign};
use crate::spec::order::{keys_cmp, key_cmp};
use crate::spec::ast::OrderKey;
use crate::link::expr::{lemma_compare_num, lemma_align_same};
use crate::bridge::order::{keys_ok, key_ok, lemma_keys_cmp_antisym, lemma_keys_cmp_trans};
use crate::gendb_entry::work::put;
use super::common::topk::*;
use super::model::*;
use super::qspec::*;

verus! {

/// LIMIT 20.
pub const K: usize = 20;

/// A candidate: customer row `cpos` with revenue coefficient `rev` (scale 4).
#[derive(Clone, Copy)]
pub struct Cand {
    pub cpos: usize,
    pub rev: i128,
}

pub open spec fn cand_row(m: M, c: Cand) -> Row {
    crow_rev(m, c.cpos as int, c.rev as int)
}

/// The first `len` candidates of a buffer, as rows.
pub open spec fn cands_view(m: M, buf: Seq<Cand>, len: int) -> Seq<Row> {
    Seq::new(len as nat, |i: int| cand_row(m, buf[i]))
}

/// The ORDER BY comparison of two candidate rows: revenue DESC.
pub proof fn lemma_cand_cmp(m: M, a: Cand, b: Cand)
    ensures
        keys_cmp(q10_keys(), cand_row(m, a), cand_row(m, b)) == (if a.rev > b.rev { -1int } else if a.rev < b.rev { 1int } else { 0int }),
        keys_ok(q10_keys(), q10_fams(), cand_row(m, a)),
{
    let (ra, rb) = (cand_row(m, a), cand_row(m, b));
    let keys = q10_keys();
    let k0 = keys[0];
    let k1 = keys.drop_first();
    assert(k0 == OrderKey { col: 2, desc: true, nulls_first: true });
    assert(k1.len() == 0);
    lemma_compare_num(a.rev as int, 4, b.rev as int, 4);
    lemma_align_same(a.rev as int, 4);
    lemma_align_same(b.rev as int, 4);
    assert(max_nat(4, 4) == 4);
    assert(ra[2] == (Val::Num { coeff: a.rev as int, scale: 4 }) && rb[2] == (Val::Num { coeff: b.rev as int, scale: 4 }));
    let c0 = key_cmp(k0, ra, rb);
    assert(c0 == -sign(a.rev as int - b.rev as int));
    assert(keys_cmp(k1, ra, rb) == 0);
    assert(keys_cmp(keys, ra, rb) == if c0 != 0 { c0 } else { 0 });
    assert forall|t: int| 0 <= t < keys.len() implies #[trigger] key_ok(keys[t], q10_fams()[t], ra) by {}
}

/// `a` comes strictly before `b`: larger revenue.
pub fn better(a: &Cand, b: &Cand, Ghost(m): Ghost<M>) -> (r: bool)
    ensures r == (keys_cmp(q10_keys(), cand_row(m, *a), cand_row(m, *b)) < 0),
    no_unwind
{
    proof { lemma_cand_cmp(m, *a, *b); }
    a.rev > b.rev
}

proof fn lemma_view_last(m: M, buf: Seq<Cand>, len: int)
    requires 0 < len <= buf.len(),
    ensures cands_view(m, buf, len).last() == cand_row(m, buf[len - 1]), cands_view(m, buf, len).len() == len,
{
}

/// The sorted position of a candidate in a sorted buffer: after every row not above it.
fn find_pos(buf: &Vec<Cand>, len: usize, c: Cand, Ghost(m): Ghost<M>, Ghost(all): Ghost<Seq<Row>>) -> (pos: usize)
    requires
        buf@.len() == K,
        len <= K,
        topk_ok(q10_keys(), q10_fams(), K as nat, cands_view(m, buf@, len as int), all),
        len == K ==> keys_cmp(q10_keys(), cand_row(m, c), cand_row(m, buf@[K - 1])) < 0,
    ensures
        ins_pos(q10_keys(), cands_view(m, buf@, len as int), pos as int, cand_row(m, c)),
        len < K || pos < len,
    no_unwind
{
    let ghost keys = q10_keys();
    let ghost fams = q10_fams();
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
            keys == q10_keys(),
            fams == q10_fams(),
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
        entries_from(final(buf)@, r as int, old(buf)@, len as int, c),
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

/// The candidate cannot enter a full buffer (it is not above the last row): the buffer stays the top K.
pub fn cannot_enter(buf: &Vec<Cand>, len: usize, rev: i128) -> (r: bool)
    requires buf@.len() == K, len <= K,
    ensures r == (len == K && rev <= buf@[K - 1].rev),
    no_unwind
{
    len == K && rev <= buf[K - 1].rev
}

/// Insert a candidate into a top-K buffer of the rows `all` (the candidate's row is new): the buffer becomes the
/// top K of `all` with the candidate.
pub fn topk_insert(buf: &mut Vec<Cand>, len: usize, c: Cand, Ghost(m): Ghost<M>, Ghost(all): Ghost<Seq<Row>>) -> (r: usize)
    requires
        old(buf)@.len() == K,
        len <= K,
        topk_ok(q10_keys(), q10_fams(), K as nat, cands_view(m, old(buf)@, len as int), all),
        rel_wf(q10_keys(), q10_fams(), all.push(cand_row(m, c))),
    ensures
        final(buf)@.len() == K,
        r <= K,
        topk_ok(q10_keys(), q10_fams(), K as nat, cands_view(m, final(buf)@, r as int), all.push(cand_row(m, c))),
        entries_from(final(buf)@, r as int, old(buf)@, len as int, c),
    no_unwind
{
    let ghost keys = q10_keys();
    let ghost fams = q10_fams();
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
                assert forall|t: int| 0 <= t < len implies #[trigger] buf@[t] == c || exists|u: int| 0 <= u < len && buf@[t] == buf@[u] by {}
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

/// A row of `all` not above the last row of a full top-K buffer of `all` with that row: skipping it keeps the buffer.
pub proof fn lemma_skip_full(m: M, buf: Seq<Cand>, len: int, all: Seq<Row>, c: Cand)
    requires
        buf.len() == K,
        len == K,
        c.rev <= buf[K - 1].rev,
        topk_ok(q10_keys(), q10_fams(), K as nat, cands_view(m, buf, len), all),
        rel_wf(q10_keys(), q10_fams(), all.push(cand_row(m, c))),
    ensures
        topk_ok(q10_keys(), q10_fams(), K as nat, cands_view(m, buf, len), all.push(cand_row(m, c))),
{
    let keys = q10_keys();
    let fams = q10_fams();
    let rc = cand_row(m, c);
    lemma_view_last(m, buf, K as int);
    lemma_cand_cmp(m, c, buf[K - 1]);
    lemma_cand_cmp(m, buf[K - 1], c);
    lemma_cand_cmp(m, c, c);
    lemma_topk_skip(keys, fams, K as nat, cands_view(m, buf, len), all, rc);
}

/// Every entry `[0, r)` of `nb` is `c` or one of the entries `[0, len)` of `ob`.
pub open spec fn entries_from(nb: Seq<Cand>, r: int, ob: Seq<Cand>, len: int, c: Cand) -> bool {
    forall|t: int| 0 <= t < r ==> #[trigger] nb[t] == c || exists|u: int| 0 <= u < len && nb[t] == ob[u]
}

/// The candidates of a buffer are groups with their revenue.
pub open spec fn cands_good(m: M, p: QP, buf: Seq<Cand>, len: int) -> bool {
    forall|i: int| 0 <= i < len ==> {
        &&& (#[trigger] buf[i]).cpos < m.c_n
        &&& good(m, p, buf[i].cpos as int)
        &&& buf[i].rev as int == csum(m, p, buf[i].cpos as int)
    }
}

/// Inserting a group with its revenue keeps the buffer's candidates groups with their revenue.
pub proof fn lemma_cands_good_insert(m: M, p: QP, ob: Seq<Cand>, len: int, nb: Seq<Cand>, r: int, c: Cand)
    requires
        cands_good(m, p, ob, len),
        entries_from(nb, r, ob, len, c),
        c.cpos < m.c_n,
        good(m, p, c.cpos as int),
        c.rev as int == csum(m, p, c.cpos as int),
    ensures cands_good(m, p, nb, r),
{
    assert forall|i: int| 0 <= i < r implies {
        &&& (#[trigger] nb[i]).cpos < m.c_n
        &&& good(m, p, nb[i].cpos as int)
        &&& nb[i].rev as int == csum(m, p, nb[i].cpos as int)
    } by {
        if nb[i] != c {
            let u = choose|u: int| 0 <= u < len && nb[i] == ob[u];
            assert(ob[u] == nb[i]);
        }
    }
}

/// Merge-order bookkeeping: one more row of a buffer, as rows.
pub proof fn lemma_view_push(m: M, buf: Seq<Cand>, i: int)
    requires 0 <= i < buf.len(),
    ensures cands_view(m, buf, i + 1) == cands_view(m, buf, i).push(cand_row(m, buf[i])),
{
    assert(cands_view(m, buf, i + 1) =~= cands_view(m, buf, i).push(cand_row(m, buf[i])));
}

} // verus!
