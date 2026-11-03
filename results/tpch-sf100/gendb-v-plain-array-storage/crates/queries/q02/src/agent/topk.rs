//! `ORDER BY s_acctbal DESC, n_name, s_name, p_partkey LIMIT k` over the candidates' output rows.
//!
//! Each candidate `q` has an output row `rows[q]` (ghost) whose key values are known from executable data: account
//! balance `acct[q]` (scale 2), supplier row `b[q]` (its name), the nation of that supplier (its name) and part key
//! `pk[q]` (`cand_keys_ok`). `cand_cmp` compares two candidates exactly as `keys_cmp` compares their rows, reading
//! names only when the balances tie. `top_k` keeps the best `k` candidates in sorted order by insertion and records
//! the others in a ghost remainder that no kept row exceeds; `lemma_topk_perm` turns that into a sorted
//! permutation of all rows whose first `k` rows are the kept ones (an allowed `ORDER BY .. LIMIT k` output).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::text::lex_cmp;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::bridge::order::{keys_ok, key_ok, all_keys_ok, lemma_keys_cmp_antisym, lemma_keys_cmp_trans, lemma_sort_rows, lemma_sorted_prefix};
use crate::bridge::typing::val_family;
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::agent::sem_ast::order_keys;
use crate::agent::scan_part::{text_row, text_col_wf, keys_unique};
use crate::agent::common::key_lookup::find_key;

verus! {

/// Comparison families of the ORDER BY keys: numeric, text, text, numeric.
pub open spec fn order_fams() -> Seq<int> {
    seq![1int, 3int, 3int, 1int]
}

/// Row `r` is an output row with these key values (positions 0, 1, 2, 3 of the 8 output columns).
pub open spec fn row_keys(r: Row, acct: int, sname: Seq<u8>, nname: Seq<u8>, pk: int) -> bool {
    &&& r.len() == 8
    &&& r[0] == (Val::Num { coeff: acct, scale: 2 })
    &&& r[1] == Val::Text(sname)
    &&& r[2] == Val::Text(nname)
    &&& r[3] == Val::Int(pk)
}

/// The order of two output rows from their key values.
pub open spec fn key_order(a1: int, s1: Seq<u8>, n1: Seq<u8>, k1: int, a2: int, s2: Seq<u8>, n2: Seq<u8>, k2: int) -> int {
    if a1 > a2 { -1 } else if a1 < a2 { 1 } else if lex_cmp(n1, n2) != 0 { lex_cmp(n1, n2) }
    else if lex_cmp(s1, s2) != 0 { lex_cmp(s1, s2) } else { sign(k1 - k2) }
}

/// `keys_cmp` of the ORDER BY on two output rows is `key_order` of their key values, and the rows' keys lie in the
/// key families.
pub proof fn lemma_keys_cmp_rows(r1: Row, r2: Row, a1: int, s1: Seq<u8>, n1: Seq<u8>, k1: int,
    a2: int, s2: Seq<u8>, n2: Seq<u8>, k2: int)
    requires row_keys(r1, a1, s1, n1, k1), row_keys(r2, a2, s2, n2, k2),
    ensures
        keys_cmp(order_keys(), r1, r2) == key_order(a1, s1, n1, k1, a2, s2, n2, k2),
        keys_ok(order_keys(), order_fams(), r1),
{
    let keys = order_keys();
    let k0 = keys[0];
    let t1 = keys.drop_first();
    let t2 = t1.drop_first();
    let t3 = t2.drop_first();
    let t4 = t3.drop_first();
    assert(t1 =~= seq![keys[1], keys[2], keys[3]]);
    assert(t2 =~= seq![keys[2], keys[3]]);
    assert(t3 =~= seq![keys[3]]);
    assert(t4 =~= Seq::<OrderKey>::empty());
    crate::link::expr::lemma_align_same(a1, 2);
    crate::link::expr::lemma_align_same(a2, 2);
    assert(max_nat(2, 2) == 2);
    assert(compare(r1[0], r2[0]) == Some(sign(a1 - a2)));
    assert(key_cmp(k0, r1, r2) == -sign(a1 - a2));
    assert(key_cmp(t1[0], r1, r2) == lex_cmp(n1, n2));
    assert(key_cmp(t2[0], r1, r2) == lex_cmp(s1, s2));
    assert(key_cmp(t3[0], r1, r2) == sign(k1 - k2));
    assert(keys_cmp(t4, r1, r2) == 0);
    assert(keys_cmp(t3, r1, r2) == sign(k1 - k2));
    assert(keys_cmp(t2, r1, r2) == if lex_cmp(s1, s2) != 0 { lex_cmp(s1, s2) } else { sign(k1 - k2) });
    assert(keys_cmp(t1, r1, r2) == if lex_cmp(n1, n2) != 0 { lex_cmp(n1, n2) } else if lex_cmp(s1, s2) != 0 { lex_cmp(s1, s2) } else { sign(k1 - k2) });
    let fams = order_fams();
    assert forall|i: int| 0 <= i < keys.len() implies #[trigger] key_ok(keys[i], fams[i], r1) by {
        if i == 0 {} else if i == 1 {} else if i == 2 {} else {}
    }
}

// ------------------------------------------------------------------------------------------ executable keys

/// Bytes `[s0, s1)` ... of text row `i` of a column (`n` rows, `blen` bytes).
pub fn text_slice(off: &'static [i64], bytes: &'static [u8], n: usize, blen: usize, i: usize) -> (r: &'static [u8])
    requires text_col_wf(off@, bytes@, n as int), blen == bytes@.len(), i < n,
    ensures r@ == text_row(off@, bytes@, i as int),
{
    let base = off[0];
    let s0 = off[i];
    let e0 = off[i + 1];
    proof {
        assert(off@[0] <= off@[i as int]);
        assert(off@[i as int] <= off@[i + 1]);
        assert(off@[i + 1] <= off@[n as int]);
    }
    assert(e0 - base <= blen);
    let start = (s0 - base) as usize;
    let end = (e0 - base) as usize;
    let (_, tail) = bytes.split_at(start);
    let (mid, _) = tail.split_at(end - start);
    proof {
        assert(mid@ =~= bytes@.subrange(start as int, end as int));
    }
    mid
}

/// Byte order of two texts (`spec::text::lex_cmp`).
pub fn lex_cmp_slices(a: &[u8], b: &[u8]) -> (r: i8)
    ensures r as int == lex_cmp(a@, b@),
{
    let mut i: usize = 0;
    let na = a.len();
    let nb = b.len();
    assert(a@.subrange(0, a@.len() as int) =~= a@);
    assert(b@.subrange(0, b@.len() as int) =~= b@);
    while i < na && i < nb
        invariant
            na == a@.len(), nb == b@.len(),
            i <= na, i <= nb,
            lex_cmp(a@.subrange(i as int, na as int), b@.subrange(i as int, nb as int)) == lex_cmp(a@, b@),
        decreases na - i,
    {
        let ghost sa = a@.subrange(i as int, na as int);
        let ghost sb = b@.subrange(i as int, nb as int);
        if a[i] < b[i] {
            return -1;
        } else if a[i] > b[i] {
            return 1;
        }
        assert(sa.drop_first() =~= a@.subrange(i + 1, na as int));
        assert(sb.drop_first() =~= b@.subrange(i + 1, nb as int));
        i = i + 1;
    }
    if i < na { 1 } else if i < nb { -1 } else { 0 }
}

/// The name columns a comparison reads: supplier names (`ns` rows) and nation names (`nn` rows), and the keys that
/// lead from a supplier to its nation.
pub struct NameCols {
    pub soff: &'static [i64],
    pub sbytes: &'static [u8],
    pub ns: usize,
    pub sblen: usize,
    pub noff: &'static [i64],
    pub nbytes: &'static [u8],
    pub nn: usize,
    pub nblen: usize,
    pub supp_nk: &'static [i64],
    pub nat_keys: &'static [i64],
}

impl NameCols {
    pub open spec fn wf(&self) -> bool {
        &&& text_col_wf(self.soff@, self.sbytes@, self.ns as int)
        &&& self.sblen == self.sbytes@.len()
        &&& text_col_wf(self.noff@, self.nbytes@, self.nn as int)
        &&& self.nblen == self.nbytes@.len()
        &&& self.supp_nk@.len() == self.ns
        &&& self.nat_keys@.len() == self.nn
        &&& keys_unique(self.nat_keys@)
    }

    /// Row `r` has the key values of a candidate with balance `acct`, supplier row `b` and part key `pk`.
    pub open spec fn keys_of(&self, r: Row, acct: int, b: int, pk: int) -> bool {
        &&& 0 <= b < self.ns
        &&& exists|d: int| 0 <= d < self.nn && #[trigger] self.nat_keys@[d] == self.supp_nk@[b]
            && row_keys(r, acct, text_row(self.soff@, self.sbytes@, b), text_row(self.noff@, self.nbytes@, d), pk)
    }

    /// The supplier's name and its nation's name.
    fn names(&self, Ghost(r): Ghost<Row>, acct: Ghost<int>, b: usize, pk: Ghost<int>) -> (out: (&'static [u8], &'static [u8]))
        requires self.wf(), self.keys_of(r, acct@, b as int, pk@),
        ensures row_keys(r, acct@, out.0@, out.1@, pk@),
    {
        let s = text_slice(self.soff, self.sbytes, self.ns, self.sblen, b);
        match find_key(self.nat_keys, self.nn, self.supp_nk[b]) {
            Some(d) => {
                let n = text_slice(self.noff, self.nbytes, self.nn, self.nblen, d);
                proof {
                    let d2 = choose|d2: int| 0 <= d2 < self.nn && #[trigger] self.nat_keys@[d2] == self.supp_nk@[b as int]
                        && row_keys(r, acct@, text_row(self.soff@, self.sbytes@, b as int), text_row(self.noff@, self.nbytes@, d2), pk@);
                    assert(d2 == d as int);
                }
                (s, n)
            },
            None => {
                proof {
                    let d2 = choose|d2: int| 0 <= d2 < self.nn && #[trigger] self.nat_keys@[d2] == self.supp_nk@[b as int]
                        && row_keys(r, acct@, text_row(self.soff@, self.sbytes@, b as int), text_row(self.noff@, self.nbytes@, d2), pk@);
                    assert(self.nat_keys@[d2] != self.supp_nk@[b as int]);
                }
                vstd::pervasive::unreached()
            },
        }
    }
}

/// The candidates' key data and their output rows agree.
pub open spec fn cand_keys_ok(nc: NameCols, acct: Seq<i128>, pk: Seq<i64>, b: Seq<usize>, rows: Seq<Row>) -> bool {
    &&& acct.len() == rows.len()
    &&& pk.len() == rows.len()
    &&& b.len() == rows.len()
    &&& forall|q: int| 0 <= q < rows.len() ==> nc.keys_of(#[trigger] rows[q], acct[q] as int, b[q] as int, pk[q] as int)
}

/// Every output row's keys lie in the key families.
pub proof fn lemma_rows_keys_ok(nc: NameCols, acct: Seq<i128>, pk: Seq<i64>, b: Seq<usize>, rows: Seq<Row>)
    requires cand_keys_ok(nc, acct, pk, b, rows),
    ensures all_keys_ok(order_keys(), order_fams(), rows),
{
    assert forall|q: int| 0 <= q < rows.len() implies keys_ok(order_keys(), order_fams(), #[trigger] rows[q]) by {
        assert(nc.keys_of(rows[q], acct[q] as int, b[q] as int, pk[q] as int));
        let d = choose|d: int| 0 <= d < nc.nn && #[trigger] nc.nat_keys@[d] == nc.supp_nk@[b[q] as int]
            && row_keys(rows[q], acct[q] as int, text_row(nc.soff@, nc.sbytes@, b[q] as int), text_row(nc.noff@, nc.nbytes@, d), pk[q] as int);
        let (s1, n1) = (text_row(nc.soff@, nc.sbytes@, b[q] as int), text_row(nc.noff@, nc.nbytes@, d));
        lemma_keys_cmp_rows(rows[q], rows[q], acct[q] as int, s1, n1, pk[q] as int, acct[q] as int, s1, n1, pk[q] as int);
    }
}

/// `keys_cmp` of the ORDER BY on the rows of candidates `q1` and `q2`.
fn cand_cmp(nc: &NameCols, acct: &Vec<i128>, pk: &Vec<i64>, b: &Vec<usize>, Ghost(rows): Ghost<Seq<Row>>, q1: usize, q2: usize) -> (r: i8)
    requires nc.wf(), cand_keys_ok(*nc, acct@, pk@, b@, rows), q1 < rows.len(), q2 < rows.len(),
    ensures r as int == keys_cmp(order_keys(), rows[q1 as int], rows[q2 as int]),
{
    let ghost (r1, r2) = (rows[q1 as int], rows[q2 as int]);
    assert(nc.keys_of(r1, acct@[q1 as int] as int, b@[q1 as int] as int, pk@[q1 as int] as int));
    assert(nc.keys_of(r2, acct@[q2 as int] as int, b@[q2 as int] as int, pk@[q2 as int] as int));
    let (a1, a2) = (acct[q1], acct[q2]);
    let ghost d1 = choose|d: int| 0 <= d < nc.nn && #[trigger] nc.nat_keys@[d] == nc.supp_nk@[b@[q1 as int] as int]
        && row_keys(r1, a1 as int, text_row(nc.soff@, nc.sbytes@, b@[q1 as int] as int), text_row(nc.noff@, nc.nbytes@, d), pk@[q1 as int] as int);
    let ghost d2 = choose|d: int| 0 <= d < nc.nn && #[trigger] nc.nat_keys@[d] == nc.supp_nk@[b@[q2 as int] as int]
        && row_keys(r2, a2 as int, text_row(nc.soff@, nc.sbytes@, b@[q2 as int] as int), text_row(nc.noff@, nc.nbytes@, d), pk@[q2 as int] as int);
    proof {
        lemma_keys_cmp_rows(r1, r2, a1 as int, text_row(nc.soff@, nc.sbytes@, b@[q1 as int] as int), text_row(nc.noff@, nc.nbytes@, d1), pk@[q1 as int] as int,
            a2 as int, text_row(nc.soff@, nc.sbytes@, b@[q2 as int] as int), text_row(nc.noff@, nc.nbytes@, d2), pk@[q2 as int] as int);
    }
    if a1 > a2 {
        return -1;
    }
    if a1 < a2 {
        return 1;
    }
    let (s1, n1) = nc.names(Ghost(r1), Ghost(a1 as int), b[q1], Ghost(pk@[q1 as int] as int));
    let (s2, n2) = nc.names(Ghost(r2), Ghost(a2 as int), b[q2], Ghost(pk@[q2 as int] as int));
    proof {
        lemma_keys_cmp_rows(r1, r2, a1 as int, s1@, n1@, pk@[q1 as int] as int, a2 as int, s2@, n2@, pk@[q2 as int] as int);
    }
    let c = lex_cmp_slices(n1, n2);
    if c != 0 {
        return c;
    }
    let c = lex_cmp_slices(s1, s2);
    if c != 0 {
        return c;
    }
    let (k1, k2) = (pk[q1], pk[q2]);
    if k1 < k2 { -1 } else if k1 > k2 { 1 } else { 0 }
}

// ------------------------------------------------------------------------------------------ top k

/// The rows of candidates `top`, in that order.
pub open spec fn rows_of(rows: Seq<Row>, top: Seq<usize>) -> Seq<Row> {
    top.map_values(|q: usize| rows[q as int])
}

/// Inserting `x` at `pos` of a sorted sequence keeps it sorted when the rows before `pos` are not above `x` and the
/// rows from `pos` on are strictly above it.
proof fn lemma_sorted_insert(s: Seq<Row>, pos: int, x: Row)
    requires
        sorted_by(order_keys(), s),
        all_keys_ok(order_keys(), order_fams(), s),
        keys_ok(order_keys(), order_fams(), x),
        0 <= pos <= s.len(),
        forall|j: int| pos <= j < s.len() ==> keys_cmp(order_keys(), x, #[trigger] s[j]) < 0,
        pos > 0 ==> keys_cmp(order_keys(), s[pos - 1], x) <= 0,
    ensures sorted_by(order_keys(), s.insert(pos, x)),
{
    hide(keys_cmp);
    let keys = order_keys();
    let fams = order_fams();
    let t = s.insert(pos, x);
    assert forall|i: int, j: int| 0 <= i < j < t.len() implies keys_cmp(keys, #[trigger] t[i], #[trigger] t[j]) <= 0 by {
        if j < pos {
            assert(t[i] == s[i] && t[j] == s[j]);
        } else if j == pos {
            assert(t[j] == x && t[i] == s[i]);
            if i < pos - 1 {
                assert(keys_cmp(keys, s[i], s[pos - 1]) <= 0);
                lemma_keys_cmp_trans(keys, fams, s[i], s[pos - 1], x);
            }
        } else if i == pos {
            assert(t[i] == x && t[j] == s[j - 1]);
        } else if i < pos {
            assert(t[i] == s[i] && t[j] == s[j - 1]);
        } else {
            assert(t[i] == s[i - 1] && t[j] == s[j - 1]);
        }
    }
}

/// The selection state after the first `q` rows: `top` (candidates, sorted, `min(q, k)` of them) and the remainder
/// `rest` (rows not above-or-equal any kept one ... i.e. no kept row exceeds them), together all of `rows[0..q)`.
pub open spec fn topk_inv(rows: Seq<Row>, top: Seq<usize>, rest: Seq<Row>, q: int, k: int) -> bool {
    &&& 0 <= q <= rows.len()
    &&& forall|x: int| 0 <= x < top.len() ==> (#[trigger] top[x]) < q
    &&& sorted_by(order_keys(), rows_of(rows, top))
    &&& (rows_of(rows, top) + rest).to_multiset() == rows.subrange(0, q).to_multiset()
    &&& forall|x: int, y: int| 0 <= x < top.len() && 0 <= y < rest.len()
        ==> keys_cmp(order_keys(), rows[#[trigger] top[x] as int], #[trigger] rest[y]) <= 0
    &&& top.len() == if q < k { q } else { k }
    &&& all_keys_ok(order_keys(), order_fams(), rest)
}

/// The rows of candidates after inserting candidate `q` at `pos`.
proof fn lemma_rows_of_insert(rows: Seq<Row>, top: Seq<usize>, pos: int, q: usize)
    requires 0 <= pos <= top.len(), q < rows.len(),
    ensures rows_of(rows, top.insert(pos, q)) == rows_of(rows, top).insert(pos, rows[q as int]),
{
    let a = rows_of(rows, top.insert(pos, q));
    let b = rows_of(rows, top).insert(pos, rows[q as int]);
    let ti = top.insert(pos, q);
    assert(a.len() == b.len());
    assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
        if i < pos {
            assert(ti[i] == top[i]);
        } else if i == pos {
            assert(ti[i] == q);
        } else {
            assert(ti[i] == top[i - 1]);
        }
    }
    assert(a =~= b);
}

/// The kept rows lie in the key families.
pub proof fn lemma_kept_keys_ok(rows: Seq<Row>, top: Seq<usize>, q: int)
    requires all_keys_ok(order_keys(), order_fams(), rows), q <= rows.len(), forall|x: int| 0 <= x < top.len() ==> (#[trigger] top[x]) < q,
    ensures all_keys_ok(order_keys(), order_fams(), rows_of(rows, top)),
{
    let t = rows_of(rows, top);
    assert forall|i: int| 0 <= i < t.len() implies keys_ok(order_keys(), order_fams(), #[trigger] t[i]) by {
        assert(t[i] == rows[top[i] as int]);
    }
}

/// Bags of the step: adding row `x` to the kept rows or to the remainder adds it to the whole.
proof fn lemma_bag_push(rows: Seq<Row>, t: Seq<Row>, rest: Seq<Row>, q: int)
    requires 0 <= q < rows.len(), (t + rest).to_multiset() == rows.subrange(0, q).to_multiset(),
    ensures
        (t + rest.push(rows[q])).to_multiset() == rows.subrange(0, q + 1).to_multiset(),
        forall|pos: int| 0 <= pos <= t.len() ==> (#[trigger] t.insert(pos, rows[q]) + rest).to_multiset() == rows.subrange(0, q + 1).to_multiset(),
{
    let x = rows[q];
    assert(rows.subrange(0, q + 1) =~= rows.subrange(0, q).push(x));
    vstd::seq_lib::to_multiset_build(rows.subrange(0, q), x);
    vstd::seq_lib::lemma_multiset_commutative(t, rest);
    vstd::seq_lib::lemma_multiset_commutative(t, rest.push(x));
    vstd::seq_lib::to_multiset_build(rest, x);
    assert forall|pos: int| 0 <= pos <= t.len() implies (#[trigger] t.insert(pos, rows[q]) + rest).to_multiset() == rows.subrange(0, q + 1).to_multiset() by {
        vstd::seq_lib::lemma_multiset_commutative(t.insert(pos, x), rest);
        vstd::seq_lib::to_multiset_insert(t, pos, x);
    }
}

/// Moving the last kept row to the remainder keeps the bag.
proof fn lemma_bag_move_last(t: Seq<Row>, rest: Seq<Row>)
    requires t.len() > 0,
    ensures (t.drop_last() + rest.push(t.last())).to_multiset() == (t + rest).to_multiset(),
{
    vstd::seq_lib::lemma_multiset_commutative(t, rest);
    vstd::seq_lib::lemma_multiset_commutative(t.drop_last(), rest.push(t.last()));
    vstd::seq_lib::to_multiset_build(rest, t.last());
    assert(t =~= t.drop_last().push(t.last()));
    vstd::seq_lib::to_multiset_build(t.drop_last(), t.last());
}

/// Step with room in the top: insert at `pos`.
proof fn lemma_step_room(rows: Seq<Row>, top: Seq<usize>, rest: Seq<Row>, q: usize, k: int, pos: int)
    requires
        topk_inv(rows, top, rest, q as int, k),
        all_keys_ok(order_keys(), order_fams(), rows),
        q < rows.len(), top.len() < k,
        0 <= pos <= top.len(),
        forall|j: int| pos <= j < top.len() ==> keys_cmp(order_keys(), rows[q as int], #[trigger] rows[top[j] as int]) < 0,
        pos > 0 ==> keys_cmp(order_keys(), rows[q as int], rows[top[pos - 1] as int]) >= 0,
    ensures topk_inv(rows, top.insert(pos, q), rest, q + 1, k),
{
    hide(keys_cmp);
    let t = rows_of(rows, top);
    let x = rows[q as int];
    lemma_kept_keys_ok(rows, top, q as int);
    assert(rest.len() == 0) by {
        vstd::seq_lib::lemma_multiset_commutative(t, rest);
        rows.subrange(0, q as int).to_multiset_ensures();
        t.to_multiset_ensures();
        rest.to_multiset_ensures();
    }
    if pos > 0 {
        assert(t[pos - 1] == rows[top[pos - 1] as int]);
        lemma_keys_cmp_antisym(order_keys(), order_fams(), x, t[pos - 1]);
    }
    assert forall|j: int| pos <= j < t.len() implies keys_cmp(order_keys(), x, #[trigger] t[j]) < 0 by {
        assert(t[j] == rows[top[j] as int]);
    }
    lemma_sorted_insert(t, pos, x);
    let top2 = top.insert(pos, q);
    lemma_rows_of_insert(rows, top, pos, q);
    lemma_bag_push(rows, t, rest, q as int);
}

/// Step with a full top and a row below the last kept one: insert at `pos`, the last kept row moves to the remainder.
proof fn lemma_step_replace(rows: Seq<Row>, top: Seq<usize>, rest: Seq<Row>, q: usize, k: int, pos: int)
    requires
        topk_inv(rows, top, rest, q as int, k),
        all_keys_ok(order_keys(), order_fams(), rows),
        q < rows.len(), top.len() == k, k >= 1,
        0 <= pos < top.len(),
        forall|j: int| pos <= j < top.len() ==> keys_cmp(order_keys(), rows[q as int], #[trigger] rows[top[j] as int]) < 0,
        pos > 0 ==> keys_cmp(order_keys(), rows[q as int], rows[top[pos - 1] as int]) >= 0,
    ensures ({
        let top2 = top.insert(pos, q);
        topk_inv(rows, top2.drop_last(), rest.push(rows[top2.last() as int]), q + 1, k)
    }),
{
    hide(keys_cmp);
    let t = rows_of(rows, top);
    let x = rows[q as int];
    lemma_kept_keys_ok(rows, top, q as int);
    if pos > 0 {
        assert(t[pos - 1] == rows[top[pos - 1] as int]);
        lemma_keys_cmp_antisym(order_keys(), order_fams(), x, t[pos - 1]);
    }
    assert forall|j: int| pos <= j < t.len() implies keys_cmp(order_keys(), x, #[trigger] t[j]) < 0 by {
        assert(t[j] == rows[top[j] as int]);
    }
    lemma_sorted_insert(t, pos, x);
    let top2 = top.insert(pos, q);
    let t2 = rows_of(rows, top2);
    lemma_rows_of_insert(rows, top, pos, q);
    assert(top2[pos] == q);
    assert(all_keys_ok(order_keys(), order_fams(), t2)) by {
        assert forall|i: int| 0 <= i < t2.len() implies keys_ok(order_keys(), order_fams(), #[trigger] t2[i]) by {
            assert(t2[i] == rows[top2[i] as int]);
        }
    }
    let z = top2.last();
    let zr = rows[z as int];
    assert(z == top[k - 1]);
    assert(t2.last() == zr);
    let top3 = top2.drop_last();
    assert(rows_of(rows, top3) =~= t2.drop_last());
    lemma_sorted_prefix(order_keys(), order_fams(), t2);
    lemma_bag_push(rows, t, rest, q as int);
    lemma_bag_move_last(t2, rest);
    let rest2 = rest.push(zr);
    assert forall|x2: int, y: int| 0 <= x2 < top3.len() && 0 <= y < rest2.len()
        implies keys_cmp(order_keys(), rows[#[trigger] top3[x2] as int], #[trigger] rest2[y]) <= 0 by {
        let tx = rows[top3[x2] as int];
        assert(tx == t2[x2]);
        if y == rest.len() {
            assert(rest2[y] == zr);
            assert(t2[t2.len() - 1] == zr);
        } else {
            let ry = rest[y];
            assert(rest2[y] == ry);
            if x2 == pos {
                assert(top3[x2] == q);
                assert(keys_cmp(order_keys(), rows[top[k - 1] as int], ry) <= 0);
                assert(keys_cmp(order_keys(), x, zr) < 0);
                assert(keys_ok(order_keys(), order_fams(), ry));
                lemma_keys_cmp_trans(order_keys(), order_fams(), x, zr, ry);
            } else {
                let ii = if x2 < pos { x2 } else { x2 - 1 };
                assert(top[ii] == top3[x2]);
                assert(keys_cmp(order_keys(), rows[top[ii] as int], ry) <= 0);
            }
        }
    }
    assert(all_keys_ok(order_keys(), order_fams(), rest2)) by {
        assert forall|i: int| 0 <= i < rest2.len() implies keys_ok(order_keys(), order_fams(), #[trigger] rest2[i]) by {
            if i < rest.len() { assert(rest2[i] == rest[i]); }
        }
    }
}

/// Step with a full top and a row not below the last kept one: the row joins the remainder.
proof fn lemma_step_reject(rows: Seq<Row>, top: Seq<usize>, rest: Seq<Row>, q: usize, k: int)
    requires
        topk_inv(rows, top, rest, q as int, k),
        all_keys_ok(order_keys(), order_fams(), rows),
        q < rows.len(), top.len() == k, k >= 1,
        keys_cmp(order_keys(), rows[q as int], rows[top[k - 1] as int]) >= 0,
    ensures topk_inv(rows, top, rest.push(rows[q as int]), q + 1, k),
{
    hide(keys_cmp);
    let t = rows_of(rows, top);
    let x = rows[q as int];
    lemma_kept_keys_ok(rows, top, q as int);
    let last = t[k - 1];
    assert(last == rows[top[k - 1] as int]);
    lemma_keys_cmp_antisym(order_keys(), order_fams(), x, last);
    lemma_bag_push(rows, t, rest, q as int);
    let rest2 = rest.push(x);
    assert forall|x2: int, y: int| 0 <= x2 < top.len() && 0 <= y < rest2.len()
        implies keys_cmp(order_keys(), rows[#[trigger] top[x2] as int], #[trigger] rest2[y]) <= 0 by {
        if y == rest.len() {
            assert(rest2[y] == x);
            assert(t[x2] == rows[top[x2] as int]);
            if x2 < k - 1 {
                assert(keys_cmp(order_keys(), t[x2], t[k - 1]) <= 0);
                lemma_keys_cmp_trans(order_keys(), order_fams(), t[x2], last, x);
            }
        } else {
            assert(rest2[y] == rest[y]);
        }
    }
    assert(all_keys_ok(order_keys(), order_fams(), rest2)) by {
        assert forall|i: int| 0 <= i < rest2.len() implies keys_ok(order_keys(), order_fams(), #[trigger] rest2[i]) by {
            if i < rest.len() { assert(rest2[i] == rest[i]); }
        }
    }
}

/// The top `k` candidates in sorted order (`top`), with a ghost remainder `rest` of the other rows that no kept row
/// exceeds.
pub fn top_k(nc: &NameCols, acct: &Vec<i128>, pk: &Vec<i64>, b: &Vec<usize>, Ghost(rows): Ghost<Seq<Row>>, k: usize)
    -> (out: (Vec<usize>, Ghost<Seq<Row>>))
    requires
        nc.wf(),
        cand_keys_ok(*nc, acct@, pk@, b@, rows),
        k >= 1,
    ensures
        topk_inv(rows, out.0@, out.1@, rows.len() as int, k as int),
{
    proof { lemma_rows_keys_ok(*nc, acct@, pk@, b@, rows); }
    let n = acct.len();
    let mut top: Vec<usize> = Vec::new();
    let ghost mut rest: Seq<Row> = Seq::empty();
    let mut q: usize = 0;
    proof {
        assert(rows.subrange(0, 0) =~= Seq::<Row>::empty());
        assert(rows_of(rows, top@) + rest =~= Seq::<Row>::empty());
    }
    while q < n
        invariant
            nc.wf(),
            cand_keys_ok(*nc, acct@, pk@, b@, rows),
            all_keys_ok(order_keys(), order_fams(), rows),
            n == rows.len(),
            k >= 1,
            q <= n,
            topk_inv(rows, top@, rest, q as int, k as int),
        decreases n - q,
    {
        let len = top.len();
        let accept = if len < k { true } else { cand_cmp(nc, acct, pk, b, Ghost(rows), q, top[len - 1]) < 0 };
        if accept {
            // Insert `q` after every kept row that is not above it.
            let mut pos = len;
            loop
                invariant
                    nc.wf(),
                    cand_keys_ok(*nc, acct@, pk@, b@, rows),
                    q < n, n == rows.len(),
                    len == top@.len(),
                    pos <= len,
                    topk_inv(rows, top@, rest, q as int, k as int),
                    forall|j: int| pos <= j < len ==> keys_cmp(order_keys(), rows[q as int], #[trigger] rows[top@[j] as int]) < 0,
                    !(len < k) ==> keys_cmp(order_keys(), rows[q as int], rows[top@[len - 1] as int]) < 0,
                ensures
                    pos <= len,
                    forall|j: int| pos <= j < len ==> keys_cmp(order_keys(), rows[q as int], #[trigger] rows[top@[j] as int]) < 0,
                    pos > 0 ==> keys_cmp(order_keys(), rows[q as int], rows[top@[pos - 1] as int]) >= 0,
                decreases pos,
            {
                if pos == 0 {
                    break;
                }
                let c = cand_cmp(nc, acct, pk, b, Ghost(rows), q, top[pos - 1]);
                if c >= 0 {
                    break;
                }
                pos = pos - 1;
            }
            let ghost top0 = top@;
            if len < k {
                proof { lemma_step_room(rows, top0, rest, q, k as int, pos as int); }
                top.insert(pos, q);
            } else {
                proof {
                    assert(pos < len);
                    lemma_step_replace(rows, top0, rest, q, k as int, pos as int);
                }
                top.insert(pos, q);
                let ghost top2 = top@;
                let z = top.pop().unwrap();
                proof {
                    assert(top2 == top0.insert(pos as int, q));
                    assert(z == top2.last());
                    assert(top@ == top2.drop_last());
                    rest = rest.push(rows[z as int]);
                }
            }
        } else {
            proof { lemma_step_reject(rows, top@, rest, q, k as int); }
            proof { rest = rest.push(rows[q as int]); }
        }
        q = q + 1;
    }
    (top, Ghost(rest))
}

/// The kept rows followed by the sorted remainder are a sorted permutation of all rows whose first `k` rows are the
/// kept ones.
pub proof fn lemma_topk_perm(rows: Seq<Row>, t: Seq<Row>, rest: Seq<Row>, k: nat)
    requires
        sorted_by(order_keys(), t),
        all_keys_ok(order_keys(), order_fams(), t),
        all_keys_ok(order_keys(), order_fams(), rest),
        (t + rest).to_multiset() == rows.to_multiset(),
        forall|x: int, y: int| 0 <= x < t.len() && 0 <= y < rest.len() ==> keys_cmp(order_keys(), #[trigger] t[x], #[trigger] rest[y]) <= 0,
        t.len() == if rows.len() < k { rows.len() } else { k },
    ensures
        ({
            let p = t + sort_rows(order_keys(), rest);
            &&& p.to_multiset() == rows.to_multiset()
            &&& sorted_by(order_keys(), p)
            &&& slice_rows(p, 0, Some(k)) == t
        }),
{
    hide(keys_cmp);
    let keys = order_keys();
    let sr = sort_rows(keys, rest);
    lemma_sort_rows(keys, order_fams(), rest);
    let p = t + sr;
    vstd::seq_lib::lemma_multiset_commutative(t, sr);
    vstd::seq_lib::lemma_multiset_commutative(t, rest);
    sr.to_multiset_ensures();
    rest.to_multiset_ensures();
    t.to_multiset_ensures();
    rows.to_multiset_ensures();
    assert forall|i: int, j: int| 0 <= i < j < p.len() implies keys_cmp(keys, #[trigger] p[i], #[trigger] p[j]) <= 0 by {
        if j < t.len() {
            assert(p[i] == t[i] && p[j] == t[j]);
        } else if i >= t.len() {
            assert(p[i] == sr[i - t.len()] && p[j] == sr[j - t.len()]);
        } else {
            assert(p[i] == t[i] && p[j] == sr[j - t.len()]);
            assert(sr.to_multiset().count(sr[j - t.len()]) > 0);
            assert(rest.contains(sr[j - t.len()]));
            let y = choose|y: int| 0 <= y < rest.len() && rest[y] == sr[j - t.len()];
            assert(keys_cmp(keys, t[i], rest[y]) <= 0);
        }
    }
    assert(p.len() == rows.len());
    assert(slice_rows(p, 0, Some(k)) =~= t);
}

} // verus!
