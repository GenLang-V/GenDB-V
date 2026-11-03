//! Result candidates of Q21 and their top-100 buffer. A candidate is a name group: the slot `t` of its first
//! supplier (whose s_name is the group's name) and its count; its result row is `[s_name, numwait]` (`cand_row`).
//! The buffer keeps the first `K` candidates by numwait DESC, s_name (`topk_insert`, sorted insertion with
//! truncation), with `common::topk::topk_ok` as its specification.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::sign;
use crate::spec::order::{keys_cmp, key_cmp};
use crate::spec::ast::OrderKey;
use crate::spec::text::lex_cmp;
use crate::link::expr::lemma_compare_int;
use crate::bridge::order::{keys_ok, key_ok, lemma_keys_cmp_antisym, lemma_keys_cmp_trans};
use crate::gendb_entry::work::put;
use crate::stores::suppliers::interface::common::colfmt::text_range_ok;
use crate::stores::suppliers::interface::common::read::{text_slice, bytes_cmp};
use super::common::topk::*;
use super::side::*;

verus! {

/// LIMIT 100.
pub const K: usize = 100;

/// ORDER BY numwait DESC, s_name (positions of the result row `[s_name, numwait]`).
pub open spec fn q21_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 1, desc: true, nulls_first: true }, OrderKey { col: 0, desc: false, nulls_first: false }]
}

/// Families of the ORDER BY keys: integer (1), text (3).
pub open spec fn q21_fams() -> Seq<int> {
    seq![1int, 3int]
}

/// A candidate: the slot `t` of the group's first supplier and the group's count.
#[derive(Clone, Copy)]
pub struct Cand {
    pub t: usize,
    pub cnt: u64,
}

/// The name of slot `t`.
pub open spec fn slot_name(sc: SCols, srows: Seq<usize>, t: int) -> Seq<u8> {
    sname(sc, srows[t] as int)
}

/// The result row of a candidate: s_name, numwait.
pub open spec fn cand_row(sc: SCols, srows: Seq<usize>, c: Cand) -> Row {
    seq![Val::Text(slot_name(sc, srows, c.t as int)), Val::Int(c.cnt as int)]
}

/// The first `len` candidates of a buffer, as rows.
pub open spec fn cands_view(sc: SCols, srows: Seq<usize>, buf: Seq<Cand>, len: int) -> Seq<Row> {
    Seq::new(len as nat, |i: int| cand_row(sc, srows, buf[i]))
}

/// The ORDER BY comparison of two candidate rows: numwait DESC, then s_name.
pub proof fn lemma_cand_cmp(sc: SCols, srows: Seq<usize>, a: Cand, b: Cand)
    ensures
        keys_cmp(q21_keys(), cand_row(sc, srows, a), cand_row(sc, srows, b)) == (if a.cnt != b.cnt {
            if a.cnt > b.cnt { -1int } else { 1int }
        } else {
            lex_cmp(slot_name(sc, srows, a.t as int), slot_name(sc, srows, b.t as int))
        }),
        keys_ok(q21_keys(), q21_fams(), cand_row(sc, srows, a)),
{
    let (ra, rb) = (cand_row(sc, srows, a), cand_row(sc, srows, b));
    let keys = q21_keys();
    let k0 = keys[0];
    let k1 = keys.drop_first();
    assert(k0 == OrderKey { col: 1, desc: true, nulls_first: true });
    assert(k1[0] == OrderKey { col: 0, desc: false, nulls_first: false });
    assert(k1.len() == 1);
    lemma_compare_int(a.cnt as int, b.cnt as int);
    assert(ra[1] == Val::Int(a.cnt as int) && rb[1] == Val::Int(b.cnt as int));
    assert(ra[0] == Val::Text(slot_name(sc, srows, a.t as int)) && rb[0] == Val::Text(slot_name(sc, srows, b.t as int)));
    let c0 = key_cmp(k0, ra, rb);
    let c1 = key_cmp(k1[0], ra, rb);
    assert(c0 == -sign(a.cnt as int - b.cnt as int));
    assert(c1 == lex_cmp(slot_name(sc, srows, a.t as int), slot_name(sc, srows, b.t as int)));
    assert(k1.drop_first().len() == 0);
    assert(keys_cmp(k1.drop_first(), ra, rb) == 0);
    assert(keys_cmp(k1, ra, rb) == c1);
    assert(keys_cmp(keys, ra, rb) == if c0 != 0 { c0 } else { c1 });
    assert forall|t: int| 0 <= t < keys.len() implies #[trigger] key_ok(keys[t], q21_fams()[t], ra) by {}
}

/// `a` comes strictly before `b`: larger count, or equal count and a bytewise smaller name.
pub fn better(sc: &SCols, srows: &Vec<usize>, a: &Cand, b: &Cand) -> (r: bool)
    requires
        scols_ok(*sc),
        a.t < srows@.len(),
        b.t < srows@.len(),
        srows@[a.t as int] < sc.n_s,
        srows@[b.t as int] < sc.n_s,
    ensures r == (keys_cmp(q21_keys(), cand_row(*sc, srows@, *a), cand_row(*sc, srows@, *b)) < 0),
{
    proof { lemma_cand_cmp(*sc, srows@, *a, *b); }
    if a.cnt != b.cnt {
        return a.cnt > b.cnt;
    }
    let ra = srows[a.t];
    let rb = srows[b.t];
    assert(text_range_ok(sc.sm_offs@, sc.sm_bytes@, ra as int));
    assert(text_range_ok(sc.sm_offs@, sc.sm_bytes@, rb as int));
    let x = text_slice(sc.sm_offs, sc.sm_bytes, ra);
    let y = text_slice(sc.sm_offs, sc.sm_bytes, rb);
    proof {
        vstd::slice::axiom_spec_len(x);
        vstd::slice::axiom_spec_len(y);
    }
    bytes_cmp(x, x.len(), y, y.len()) < 0
}

pub proof fn lemma_view_last(sc: SCols, srows: Seq<usize>, buf: Seq<Cand>, len: int)
    requires 0 < len <= buf.len(),
    ensures
        cands_view(sc, srows, buf, len).last() == cand_row(sc, srows, buf[len - 1]),
        cands_view(sc, srows, buf, len).len() == len,
{
}

/// One more candidate of a buffer, as rows.
pub proof fn lemma_view_push(sc: SCols, srows: Seq<usize>, buf: Seq<Cand>, i: int)
    requires 0 <= i < buf.len(),
    ensures cands_view(sc, srows, buf, i + 1) == cands_view(sc, srows, buf, i).push(cand_row(sc, srows, buf[i])),
{
    assert(cands_view(sc, srows, buf, i + 1) =~= cands_view(sc, srows, buf, i).push(cand_row(sc, srows, buf[i])));
}

/// Every candidate of the buffer names a slot.
pub open spec fn slots_in(sc: SCols, srows: Seq<usize>, buf: Seq<Cand>, len: int) -> bool {
    forall|i: int| 0 <= i < len ==> (#[trigger] buf[i]).t < srows.len() && srows[buf[i].t as int] < sc.n_s
        && buf[i].cnt <= i64::MAX
}

/// The sorted position of a candidate in a sorted buffer: after every row not above it.
fn find_pos(sc: &SCols, srows: &Vec<usize>, buf: &Vec<Cand>, len: usize, c: Cand, Ghost(all): Ghost<Seq<Row>>) -> (pos: usize)
    requires
        scols_ok(*sc),
        buf@.len() == K,
        len <= K,
        slots_in(*sc, srows@, buf@, len as int),
        c.t < srows@.len() && srows@[c.t as int] < sc.n_s,
        topk_ok(q21_keys(), q21_fams(), K as nat, cands_view(*sc, srows@, buf@, len as int), all),
        len == K ==> keys_cmp(q21_keys(), cand_row(*sc, srows@, c), cand_row(*sc, srows@, buf@[K - 1])) < 0,
    ensures
        ins_pos(q21_keys(), cands_view(*sc, srows@, buf@, len as int), pos as int, cand_row(*sc, srows@, c)),
        len < K || pos < len,
{
    let ghost keys = q21_keys();
    let ghost fams = q21_fams();
    let ghost view = cands_view(*sc, srows@, buf@, len as int);
    let ghost rc = cand_row(*sc, srows@, c);
    proof { lemma_cand_cmp(*sc, srows@, c, c); }
    let mut pos: usize = 0;
    let mut found = false;
    while pos < len && !found
        invariant
            scols_ok(*sc),
            pos <= len <= K,
            buf@.len() == K,
            slots_in(*sc, srows@, buf@, len as int),
            c.t < srows@.len() && srows@[c.t as int] < sc.n_s,
            view == cands_view(*sc, srows@, buf@, len as int),
            rc == cand_row(*sc, srows@, c),
            keys == q21_keys(),
            fams == q21_fams(),
            keys_ok(keys, fams, rc),
            topk_ok(keys, fams, K as nat, view, all),
            forall|i: int| 0 <= i < pos ==> keys_cmp(keys, #[trigger] view[i], rc) <= 0,
            found ==> pos < len && keys_cmp(keys, rc, view[pos as int]) < 0,
        decreases len - pos + if found { 0int } else { 1int },
    {
        let bp = buf[pos];
        assert(bp == buf@[pos as int]);
        let b = better(sc, srows, &c, &bp);
        proof {
            assert(view[pos as int] == cand_row(*sc, srows@, buf@[pos as int]));
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
            assert(view[pos as int] == cand_row(*sc, srows@, buf@[pos as int]));
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
            assert(view[K - 1] == cand_row(*sc, srows@, buf@[K - 1]));
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
fn shift_insert(buf: &mut Vec<Cand>, len: usize, pos: usize, c: Cand, Ghost(sc): Ghost<SCols>, Ghost(srows): Ghost<Seq<usize>>) -> (r: usize)
    requires
        old(buf)@.len() == K,
        pos <= len <= K,
        len < K || pos < len,
    ensures
        final(buf)@.len() == K,
        r <= K,
        cands_view(sc, srows, final(buf)@, r as int)
            == ins_at(cands_view(sc, srows, old(buf)@, len as int), pos as int, cand_row(sc, srows, c), K as nat),
        forall|t: int| 0 <= t < r ==> #[trigger] final(buf)@[t] == c || exists|u: int| 0 <= u < len && final(buf)@[t] == old(buf)@[u],
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
        let view = cands_view(sc, srows, old_buf, len as int);
        let nb = cands_view(sc, srows, buf@, r as int);
        let ia = ins_at(view, pos as int, cand_row(sc, srows, c), K as nat);
        lemma_topk_ins_len(view, pos as int, cand_row(sc, srows, c));
        assert forall|t: int| 0 <= t < nb.len() implies #[trigger] nb[t] == ia[t] by {
            lemma_topk_ins_index(view, pos as int, cand_row(sc, srows, c), t);
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
pub fn topk_insert(sc: &SCols, srows: &Vec<usize>, buf: &mut Vec<Cand>, len: usize, c: Cand, Ghost(all): Ghost<Seq<Row>>) -> (r: usize)
    requires
        scols_ok(*sc),
        old(buf)@.len() == K,
        len <= K,
        slots_in(*sc, srows@, old(buf)@, len as int),
        c.t < srows@.len() && srows@[c.t as int] < sc.n_s,
        c.cnt <= i64::MAX,
        topk_ok(q21_keys(), q21_fams(), K as nat, cands_view(*sc, srows@, old(buf)@, len as int), all),
        rel_wf(q21_keys(), q21_fams(), all.push(cand_row(*sc, srows@, c))),
    ensures
        final(buf)@.len() == K,
        r <= K,
        slots_in(*sc, srows@, final(buf)@, r as int),
        topk_ok(q21_keys(), q21_fams(), K as nat, cands_view(*sc, srows@, final(buf)@, r as int), all.push(cand_row(*sc, srows@, c))),
{
    let ghost keys = q21_keys();
    let ghost fams = q21_fams();
    let ghost view = cands_view(*sc, srows@, buf@, len as int);
    let ghost rc = cand_row(*sc, srows@, c);
    if len == K {
        let last = buf[K - 1];
        if !better(sc, srows, &c, &last) {
            proof {
                lemma_view_last(*sc, srows@, buf@, K as int);
                lemma_cand_cmp(*sc, srows@, c, c);
                lemma_cand_cmp(*sc, srows@, buf@[K - 1], buf@[K - 1]);
                lemma_keys_cmp_antisym(keys, fams, rc, cand_row(*sc, srows@, buf@[K - 1]));
                lemma_topk_skip(keys, fams, K as nat, view, all, rc);
            }
            return len;
        }
    }
    let pos = find_pos(sc, srows, buf, len, c, Ghost(all));
    let ghost old_buf = buf@;
    let r = shift_insert(buf, len, pos, c, Ghost(*sc), Ghost(srows@));
    proof {
        lemma_topk_insert(keys, fams, K as nat, view, all, rc, pos as int);
        assert forall|i: int| 0 <= i < r implies (#[trigger] buf@[i]).t < srows@.len() && srows@[buf@[i].t as int] < sc.n_s
            && buf@[i].cnt <= i64::MAX by {
            if buf@[i] != c {
                let u = choose|u: int| 0 <= u < len && buf@[i] == old_buf[u];
            }
        }
    }
    r
}

} // verus!
