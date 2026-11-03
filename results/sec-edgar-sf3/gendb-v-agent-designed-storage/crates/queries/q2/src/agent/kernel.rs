//! The top-100 buffer and the facts the walk reads. Candidates `(value, name code, tag code)` are kept sorted by
//! value DESC, name, tag (dictionary codes follow byte order, so code order is the ORDER BY order); `topk_add`
//! inserts one and keeps a top-100 split (`common::topk`) of the candidates seen. `kfacts` (opaque) holds both
//! storages' layouts and sub's primary key; small lemmas expose the facts the walk needs.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::OrderKey;
use crate::spec::order::*;
use crate::spec::numeric::*;
use crate::spec::text::lex_cmp;
use crate::bridge::order::{keys_ok, key_ok, all_keys_ok, lemma_keys_cmp_antisym, lemma_lex_cmp_antisym};
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::gendb_entry::layout::PartView;
use crate::stores::num_vord::interface as numi;
use crate::stores::sub::interface as subi;
use crate::stores::num_vord::interface::common::text::{text_entry, text_parts_wf, text_strictly_sorted, u64_part, u8_part,
    text_entry_of, compare_bytes, lemma_dict_codes, lemma_lex_cmp_lt_trans};
use crate::stores::num_vord::interface::common::cols::{i32_part, i128_part};
use crate::stores::num_vord::interface::common::runs::*;
use crate::agent::stored::*;
use crate::agent::common::topk::*;

verus! {



/// Rows kept by the LIMIT.
pub const TOPK: usize = 100;

/// The statement's ORDER BY: value DESC, name, tag.
pub open spec fn qkeys() -> Seq<OrderKey> {
    seq![
        OrderKey { col: 2, desc: true, nulls_first: true },
        OrderKey { col: 0, desc: false, nulls_first: false },
        OrderKey { col: 1, desc: false, nulls_first: false },
    ]
}

/// Comparison families of the keys: numeric, text, text.
pub open spec fn qfams() -> Seq<int> {
    seq![1int, 3int, 3int]
}

/// A candidate output row: value coefficient (scale 4), name code (sub's name dictionary), tag code (num's tag
/// dictionary).
#[derive(Clone, Copy)]
pub struct Cand {
    pub value: i128,
    pub name: u64,
    pub tag: u64,
}

pub open spec fn name_count(sp: Seq<PartView>) -> int {
    crate::stores::sub::interface::common::cols::text_count(sp, subi::P_NAME_DICT_OFF as int)
}

/// The SQL row of a candidate.
pub open spec fn cview(np: Seq<PartView>, sp: Seq<PartView>, c: Cand) -> Row {
    out_of(np, sp, c.name as int, c.tag as int, c.value as int)
}

pub open spec fn cand_ok(np: Seq<PartView>, sp: Seq<PartView>, c: Cand) -> bool {
    (c.name as int) < name_count(sp) && (c.tag as int) < numi::tag_count(np)
}

/// The SQL rows of the first `len` candidates of a buffer.
pub open spec fn tview(np: Seq<PartView>, sp: Seq<PartView>, buf: Seq<Cand>, len: int) -> Seq<Row> {
    Seq::new(len as nat, |k: int| cview(np, sp, buf[k]))
}

pub open spec fn buf_ok(np: Seq<PartView>, sp: Seq<PartView>, buf: Seq<Cand>, len: int) -> bool {
    &&& buf.len() == TOPK
    &&& 0 <= len <= TOPK
    &&& forall|k: int| 0 <= k < len ==> cand_ok(np, sp, #[trigger] buf[k])
}

/// Both dictionaries the candidates code into are sorted.
pub open spec fn dicts_sorted(np: Seq<PartView>, sp: Seq<PartView>) -> bool {
    &&& numi::tag_count(np) >= 0
    &&& text_strictly_sorted(u64_part(np[numi::P_TAG_OFF as int]), u8_part(np[numi::P_TAG_BYTES as int]), numi::tag_count(np))
    &&& name_count(sp) >= 0
    &&& crate::stores::sub::interface::common::text::text_strictly_sorted(
        crate::stores::sub::interface::common::text::u64_part(sp[subi::P_NAME_DICT_OFF as int]),
        crate::stores::sub::interface::common::text::u8_part(sp[subi::P_NAME_DICT_BYTES as int]), name_count(sp))
}

// ------------------------------------------------------------------ candidate order

/// The ORDER BY comparison of two candidates, by their codes.
pub proof fn lemma_cview_cmp(np: Seq<PartView>, sp: Seq<PartView>, a: Cand, b: Cand)
    requires dicts_sorted(np, sp), cand_ok(np, sp, a), cand_ok(np, sp, b),
    ensures
        keys_cmp(qkeys(), cview(np, sp, a), cview(np, sp, b)) == (
            if a.value != b.value { if a.value > b.value { -1int } else { 1int } }
            else if a.name != b.name { if a.name < b.name { -1int } else { 1int } }
            else if a.tag != b.tag { if a.tag < b.tag { -1int } else { 1int } }
            else { 0int }),
        keys_ok(qkeys(), qfams(), cview(np, sp, a)),
{
    reveal_with_fuel(keys_cmp, 4);
    let (ra, rb) = (cview(np, sp, a), cview(np, sp, b));
    let ks = qkeys();
    assert(ks.drop_first() =~= seq![OrderKey { col: 0, desc: false, nulls_first: false }, OrderKey { col: 1, desc: false, nulls_first: false }]);
    assert(ks.drop_first().drop_first() =~= seq![OrderKey { col: 1, desc: false, nulls_first: false }]);
    assert(ks.drop_first().drop_first().drop_first() =~= Seq::<OrderKey>::empty());
    crate::link::expr::lemma_compare_num(a.value as int, 4, b.value as int, 4);
    crate::link::expr::lemma_align_same(a.value as int, 4);
    crate::link::expr::lemma_align_same(b.value as int, 4);
    assert(max_nat(4, 4) == 4);
    let (na, nb) = (name_text(sp, a.name as int), name_text(sp, b.name as int));
    crate::stores::sub::interface::common::text::lemma_dict_codes(
        crate::stores::sub::interface::common::text::u64_part(sp[subi::P_NAME_DICT_OFF as int]),
        crate::stores::sub::interface::common::text::u8_part(sp[subi::P_NAME_DICT_BYTES as int]), name_count(sp),
        a.name as int, b.name as int);
    lemma_lex_cmp_antisym(na, nb);
    let (ta, tb) = (tag_text(np, a.tag as int), tag_text(np, b.tag as int));
    lemma_dict_codes(u64_part(np[numi::P_TAG_OFF as int]), u8_part(np[numi::P_TAG_BYTES as int]), numi::tag_count(np),
        a.tag as int, b.tag as int);
    lemma_lex_cmp_antisym(ta, tb);
    assert(keys_ok(qkeys(), qfams(), ra)) by {
        assert forall|i: int| 0 <= i < ks.len() implies #[trigger] key_ok(ks[i], qfams()[i], ra) by {
            if i == 0 {} else if i == 1 {} else {}
        }
    }
}

/// `a` sorts strictly before `b`.
pub fn before(a: &Cand, b: &Cand, Ghost(np): Ghost<Seq<PartView>>, Ghost(sp): Ghost<Seq<PartView>>) -> (r: bool)
    requires dicts_sorted(np, sp), cand_ok(np, sp, *a), cand_ok(np, sp, *b),
    ensures r == (keys_cmp(qkeys(), cview(np, sp, *a), cview(np, sp, *b)) < 0),
    no_unwind
{
    proof { lemma_cview_cmp(np, sp, *a, *b); }
    if a.value != b.value {
        a.value > b.value
    } else if a.name != b.name {
        a.name < b.name
    } else {
        a.tag < b.tag
    }
}

// ------------------------------------------------------------------ the top-k buffer

/// Inserting `x` after the rows of `s` that are not after it, at position `pos`, is `insert_sorted`.
pub proof fn lemma_insert_sorted_at(keys: Seq<OrderKey>, s: Seq<Row>, x: Row, pos: int)
    requires
        0 <= pos <= s.len(),
        forall|k: int| pos <= k < s.len() ==> keys_cmp(keys, #[trigger] s[k], x) > 0,
        pos == 0 || keys_cmp(keys, s[pos - 1], x) <= 0,
    ensures insert_sorted(keys, s, x) == s.subrange(0, pos).push(x) + s.subrange(pos, s.len() as int),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s.subrange(0, pos).push(x) + s.subrange(pos, s.len() as int) =~= seq![x]);
    } else if pos == s.len() {
        assert(s.subrange(0, pos).push(x) + s.subrange(pos, s.len() as int) =~= s.push(x));
    } else {
        let d = s.drop_last();
        assert(keys_cmp(keys, s[s.len() - 1], x) > 0);
        assert forall|k: int| pos <= k < d.len() implies keys_cmp(keys, #[trigger] d[k], x) > 0 by {
            assert(d[k] == s[k]);
        }
        if pos > 0 {
            assert(d[pos - 1] == s[pos - 1]);
        }
        lemma_insert_sorted_at(keys, d, x, pos);
        assert(d.subrange(0, pos).push(x) + d.subrange(pos, d.len() as int) + seq![s.last()]
            =~= s.subrange(0, pos).push(x) + s.subrange(pos, s.len() as int));
        assert(insert_sorted(keys, d, x).push(s.last()) =~= insert_sorted(keys, d, x) + seq![s.last()]);
    }
}

/// Add candidate `c` to the sorted buffer `buf[0..len)` (at most `TOPK` candidates): the result is a top-k split of
/// the bag `all` plus `c`'s row.
pub fn topk_add(buf: &mut Vec<Cand>, len: usize, c: Cand, Ghost(np): Ghost<Seq<PartView>>, Ghost(sp): Ghost<Seq<PartView>>,
    Ghost(all): Ghost<Seq<Row>>, Ghost(rest): Ghost<Seq<Row>>) -> (r: (usize, Ghost<Seq<Row>>))
    requires
        dicts_sorted(np, sp),
        buf_ok(np, sp, old(buf)@, len as int),
        cand_ok(np, sp, c),
        topk_ok(qkeys(), qfams(), TOPK as nat, all, tview(np, sp, old(buf)@, len as int), rest),
    ensures
        buf_ok(np, sp, final(buf)@, r.0 as int),
        topk_ok(qkeys(), qfams(), TOPK as nat, all.push(cview(np, sp, c)), tview(np, sp, final(buf)@, r.0 as int), r.1@),
    no_unwind
{
    let ghost keys = qkeys();
    let ghost x = cview(np, sp, c);
    let ghost t = tview(np, sp, buf@, len as int);
    proof { lemma_cview_cmp(np, sp, c, c); }
    if len == TOPK {
        let last = buf[TOPK - 1];
        if !before(&c, &last, Ghost(np), Ghost(sp)) {
            proof {
                assert(t.last() == cview(np, sp, last));
                lemma_cview_cmp(np, sp, last, c);
                lemma_keys_cmp_antisym(keys, qfams(), x, t.last());
                lemma_topk_reject(keys, qfams(), TOPK as nat, all, t, rest, x);
            }
            return (len, Ghost(rest.push(x)));
        }
    }
    let ghost old_buf = buf@;
    // The rows the candidate is inserted among: all of them, or all but the last (evicted) one.
    let m: usize = if len == TOPK { TOPK - 1 } else { len };
    let ghost s = tview(np, sp, old_buf, m as int);
    let mut pos: usize = m;
    while pos > 0 && before(&c, &buf[pos - 1], Ghost(np), Ghost(sp))
        invariant
            dicts_sorted(np, sp),
            cand_ok(np, sp, c),
            buf_ok(np, sp, old_buf, len as int),
            m <= len, m < TOPK,
            buf@.len() == TOPK,
            pos <= m,
            forall|k: int| 0 <= k < pos ==> #[trigger] buf@[k] == old_buf[k],
            forall|k: int| pos < k <= m ==> #[trigger] buf@[k] == old_buf[k - 1],
            forall|k: int| pos <= k < m ==> keys_cmp(keys, #[trigger] s[k], x) > 0,
            s == tview(np, sp, old_buf, m as int),
            x == cview(np, sp, c),
            keys == qkeys(),
        decreases pos,
    {
        proof {
            lemma_cview_cmp(np, sp, c, old_buf[pos - 1]);
            lemma_cview_cmp(np, sp, old_buf[pos - 1], c);
            lemma_keys_cmp_antisym(keys, qfams(), x, s[pos - 1]);
        }
        let prev = buf[pos - 1];
        buf[pos] = prev;
        pos = pos - 1;
    }
    proof {
        if pos > 0 {
            assert(buf@[pos - 1] == old_buf[pos - 1]);
            lemma_cview_cmp(np, sp, c, old_buf[pos - 1]);
            lemma_cview_cmp(np, sp, old_buf[pos - 1], c);
            lemma_keys_cmp_antisym(keys, qfams(), x, s[pos - 1]);
        }
    }
    buf[pos] = c;
    let ghost nt = tview(np, sp, buf@, (m + 1) as int);
    proof {
        lemma_insert_sorted_at(keys, s, x, pos as int);
        assert(nt =~= s.subrange(0, pos as int).push(x) + s.subrange(pos as int, m as int)) by {
            assert forall|k: int| 0 <= k < m + 1 implies #[trigger] nt[k] == (s.subrange(0, pos as int).push(x) + s.subrange(pos as int, m as int))[k] by {
                if k < pos {
                } else if k == pos {
                } else {
                    assert(buf@[k] == old_buf[k - 1]);
                }
            }
        }
        assert forall|k: int| 0 <= k < m + 1 implies cand_ok(np, sp, #[trigger] buf@[k]) by {
            if k < pos {
            } else if k == pos {
            } else {
                assert(buf@[k] == old_buf[k - 1]);
            }
        }
    }
    if len == TOPK {
        proof {
            assert(s =~= t.drop_last());
            let last = old_buf[TOPK - 1];
            assert(t.last() == cview(np, sp, last));
            lemma_cview_cmp(np, sp, c, last);
            lemma_cview_cmp(np, sp, last, c);
            lemma_keys_cmp_antisym(keys, qfams(), x, t.last());
            lemma_topk_evict(keys, qfams(), TOPK as nat, all, t, rest, x);
        }
        (len, Ghost(rest.push(t.last())))
    } else {
        proof {
            assert(s =~= t);
            lemma_topk_insert_room(keys, qfams(), TOPK as nat, all, t, rest, x);
        }
        (len + 1, Ghost(rest))
    }
}

// ------------------------------------------------------------------ worker input

/// Sub rows are identified by their adsh (the declared primary key of `sub`).
pub open spec fn adsh_unique(sp: Seq<PartView>) -> bool {
    forall|j1: int, j2: int| 0 <= j1 < subi::row_count(sp) && 0 <= j2 < subi::row_count(sp)
        && #[trigger] subi::adsh_bytes(sp, j1) == #[trigger] subi::adsh_bytes(sp, j2) ==> j1 == j2
}

/// The layouts of both storages and sub's key (hidden; facts come from the lemmas below).
#[verifier::opaque]
pub open spec fn kfacts(np: Seq<PartView>, sp: Seq<PartView>) -> bool {
    numi::num_layout_ok(np) && subi::sub_layout_ok(sp) && adsh_unique(sp)
}

/// Sub's key: two rows with the same adsh are one row.
pub proof fn lemma_kf_pk(np: Seq<PartView>, sp: Seq<PartView>, j1: int, j2: int)
    requires
        kfacts(np, sp), 0 <= j1 < subi::row_count(sp), 0 <= j2 < subi::row_count(sp),
        subi::adsh_bytes(sp, j1) == subi::adsh_bytes(sp, j2),
    ensures j1 == j2,
{
    reveal(kfacts);
}

/// Every sub row has a sorted position.
pub proof fn lemma_kf_order_pos(np: Seq<PartView>, sp: Seq<PartView>, j: int)
    requires kfacts(np, sp), 0 <= j < subi::row_count(sp),
    ensures exists|q: int| 0 <= q < subi::row_count(sp) && subi::adsh_order(sp)[q] == j,
{
    reveal(kfacts);
    let n = subi::row_count(sp);
    let order = subi::adsh_order(sp);
    crate::stores::sub::interface::common::perm::lemma_permutation_facts(order, n as nat);
    let q = crate::stores::sub::interface::common::perm::position_of(order, j);
    assert(0 <= q < n && order[q] == j);
}

/// The value order of unit code `u`.
pub proof fn lemma_kf_vorder(np: Seq<PartView>, sp: Seq<PartView>, u: int)
    requires kfacts(np, sp), 0 <= u < numi::uom_count(np),
    ensures
        numi::unit_order_ok(np, u),
        numi::u64s(np, numi::P_VORDER).len() == numi::row_count(np),
        np[numi::P_VORDER as int] is U64,
{
    reveal(kfacts);
}

/// The rows of unit code `u` lie in `[0, n)`.
pub proof fn lemma_kf_unit_bounds(np: Seq<PartView>, sp: Seq<PartView>, u: int)
    requires kfacts(np, sp), 0 <= u < numi::uom_count(np),
    ensures 0 <= numi::unit_row(np, u) <= numi::unit_row(np, u + 1) <= numi::row_count(np),
{
    reveal(kfacts);
    crate::agent::vstored::lemma_unit_bounds(np, u);
}

/// The adsh code of run `r` is an entry of num's adsh dictionary: the run's filing.
pub proof fn lemma_kf_run_adsh(np: Seq<PartView>, sp: Seq<PartView>, r: int)
    requires kfacts(np, sp), 0 <= r < numi::run_count(np),
    ensures
        numi::u64s(np, numi::P_RUN_ADSH)[r] < numi::adsh_count(np),
        adsh_entry(np, numi::u64s(np, numi::P_RUN_ADSH)[r] as int) == numi::run_adsh_of(np, r),
{
    reveal(kfacts);
    assert(numi::u64s(np, numi::P_RUN_UOM)[r] < numi::uom_count(np));
}

/// Bytes of entry `k` of num's adsh dictionary.
pub open spec fn adsh_entry(np: Seq<PartView>, k: int) -> Seq<u8> {
    text_entry(u64_part(np[numi::P_ADSH_OFF as int]), u8_part(np[numi::P_ADSH_BYTES as int]), k)
}

/// Bytes of sub row `j`'s adsh.
pub open spec fn sub_key(sp: Seq<PartView>, j: int) -> Seq<u8> {
    text_entry(u64_part(sp[subi::P_ADSH_OFF as int]), u8_part(sp[subi::P_ADSH_BYTES as int]), j)
}

/// Dictionary facts: num's adsh dictionary and both output dictionaries.
pub proof fn lemma_kf_dicts(np: Seq<PartView>, sp: Seq<PartView>)
    requires kfacts(np, sp),
    ensures
        numi::adsh_count(np) >= 0,
        text_parts_wf(u64_part(np[numi::P_ADSH_OFF as int]), u8_part(np[numi::P_ADSH_BYTES as int]), numi::adsh_count(np)),
        text_strictly_sorted(u64_part(np[numi::P_ADSH_OFF as int]), u8_part(np[numi::P_ADSH_BYTES as int]), numi::adsh_count(np)),
        dicts_sorted(np, sp),
        forall|k: int| 0 <= k < numi::adsh_count(np) ==> #[trigger] adsh_entry(np, k) == numi::dict_entry(np, numi::P_ADSH_OFF, k),
{
    reveal(kfacts);
}

/// Sub facts: adsh text list, the sorted permutation, per-row parts.
pub proof fn lemma_kf_sub(np: Seq<PartView>, sp: Seq<PartView>)
    requires kfacts(np, sp),
    ensures ({
        let n = subi::row_count(sp);
        let order = subi::adsh_order(sp);
        &&& n >= 0
        &&& text_parts_wf(u64_part(sp[subi::P_ADSH_OFF as int]), u8_part(sp[subi::P_ADSH_BYTES as int]), n)
        &&& order.len() == n
        &&& (forall|p: int| 0 <= p < n ==> #[trigger] order[p] < n)
        &&& (forall|a: int, b: int| 0 <= a < b < n ==> lex_cmp(#[trigger] sub_key(sp, order[a] as int), #[trigger] sub_key(sp, order[b] as int)) <= 0)
        &&& (forall|j: int| 0 <= j < n ==> #[trigger] sub_key(sp, j) == subi::adsh_bytes(sp, j))
        &&& i32_part(sp[subi::P_FY as int]).len() == n
        &&& u8_part(sp[subi::P_FY_VALID as int]).len() == n
        &&& u64_part(sp[subi::P_NAME_CODES as int]).len() == n
        &&& (forall|j: int| 0 <= j < n ==> #[trigger] u64_part(sp[subi::P_NAME_CODES as int])[j] < name_count(sp))
    }),
{
    reveal(kfacts);
    let n = subi::row_count(sp);
    let order = subi::adsh_order(sp);
    crate::stores::sub::interface::common::perm::lemma_permutation_facts(order, n as nat);
}

/// Num facts: runs, per-row parts, tag codes.
pub proof fn lemma_kf_num(np: Seq<PartView>, sp: Seq<PartView>)
    requires kfacts(np, sp),
    ensures ({
        let n = numi::row_count(np);
        let nr = numi::run_count(np);
        &&& runs_partition_ok(n_start(np), nr, n)
        &&& (forall|r: int| #![trigger n_start(np)[r], n_start(np)[r + 1]] 0 <= r < nr ==> 0 <= n_start(np)[r] <= n_start(np)[r + 1] <= n)
        &&& numi::u64s(np, numi::P_RUN_ADSH).len() == nr
        &&& numi::u64s(np, numi::P_TV).len() == n
        &&& n_value(np).len() == n
        &&& numi::u64s(np, numi::P_PAIR_TAG).len() == numi::pair_count(np)
        &&& (forall|i: int| 0 <= i < n ==> #[trigger] numi::u64s(np, numi::P_TV)[i] < numi::pair_count(np))
        &&& (forall|q: int| 0 <= q < numi::pair_count(np) ==> #[trigger] numi::u64s(np, numi::P_PAIR_TAG)[q] < numi::tag_count(np))
    }),
{
    reveal(kfacts);
    let st = n_start(np);
    let nr = numi::run_count(np);
    assert forall|r: int| #![trigger st[r], st[r + 1]] 0 <= r < nr implies 0 <= st[r] <= st[r + 1] <= numi::row_count(np) by {
        assert(st[0] <= st[r]);
        assert(st[r + 1] <= st[nr]);
    }
}

/// Tag codes do not decrease along a run.
pub proof fn lemma_kf_tag_mono(np: Seq<PartView>, sp: Seq<PartView>, r: int, a: int, b: int)
    requires kfacts(np, sp), 0 <= r < numi::run_count(np), n_start(np)[r] <= a <= b < n_start(np)[r + 1],
    ensures tagc(np, a) <= tagc(np, b),
{
    lemma_kf_num(np, sp);
    lemma_kf_tv_mono(np, sp, r, a, b);
    let tv = numi::u64s(np, numi::P_TV);
    if tv[a] < tv[b] {
        lemma_kf_pair_tag_mono(np, sp, tv[a] as int, tv[b] as int);
    }
}

/// Pair codes do not decrease along a run.
proof fn lemma_kf_tv_mono(np: Seq<PartView>, sp: Seq<PartView>, r: int, a: int, b: int)
    requires kfacts(np, sp), 0 <= r < numi::run_count(np), n_start(np)[r] <= a <= b < n_start(np)[r + 1],
    ensures numi::u64s(np, numi::P_TV)[a] <= numi::u64s(np, numi::P_TV)[b],
{
    reveal(kfacts);
    let st = n_start(np);
    let tv = numi::u64s(np, numi::P_TV);
    if a < b {
        assert(st[r] <= a < b < st[r + 1]);
        assert(tv[a] <= tv[b]);
    }
}

/// Tag codes of pairs do not decrease with the pair code.
proof fn lemma_kf_pair_tag_mono(np: Seq<PartView>, sp: Seq<PartView>, p: int, q: int)
    requires kfacts(np, sp), 0 <= p < q < numi::pair_count(np),
    ensures numi::u64s(np, numi::P_PAIR_TAG)[p] <= numi::u64s(np, numi::P_PAIR_TAG)[q],
{
    reveal(kfacts);
    let pt = numi::u64s(np, numi::P_PAIR_TAG);
    let pv = numi::u64s(np, numi::P_PAIR_VERSION);
    assert(pair_lt(pt[p], pv[p], pt[q], pv[q]));
}

// ------------------------------------------------------------------ searches

/// First position of a sorted dictionary whose value is not below `key`: every value before it is below `key`.
pub fn lower_bound_text(off: &[u64], bytes: &[u8], count: usize, key: &[u8], key_len: usize) -> (r: usize)
    requires
        text_parts_wf(off@, bytes@, count as int),
        text_strictly_sorted(off@, bytes@, count as int),
        key_len == key@.len(),
    ensures r <= count, forall|k: int| 0 <= k < r ==> lex_cmp(#[trigger] text_entry(off@, bytes@, k), key@) < 0,
    no_unwind
{
    let mut lo: usize = 0;
    let mut hi: usize = count;
    while lo < hi
        invariant
            lo <= hi <= count,
            text_parts_wf(off@, bytes@, count as int),
            text_strictly_sorted(off@, bytes@, count as int),
            key_len == key@.len(),
            forall|k: int| 0 <= k < lo ==> lex_cmp(#[trigger] text_entry(off@, bytes@, k), key@) < 0,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        let (e, en) = text_entry_of(off, bytes, count, mid);
        if compare_bytes(e, en, key, key_len) < 0 {
            proof {
                assert forall|k: int| 0 <= k <= mid implies lex_cmp(#[trigger] text_entry(off@, bytes@, k), key@) < 0 by {
                    if k < mid {
                        lemma_lex_cmp_lt_trans(text_entry(off@, bytes@, k), text_entry(off@, bytes@, mid as int), key@);
                    }
                }
            }
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

/// A strictly smaller value stays strictly smaller against a value not below the middle one.
proof fn lemma_lt_le(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>)
    requires lex_cmp(a, b) < 0, lex_cmp(b, c) <= 0,
    ensures lex_cmp(a, c) < 0,
{
    crate::bridge::order::lemma_lex_cmp_trans(a, b, c);
    lemma_lex_cmp_zero(a, c);
    if a == c {
        lemma_lex_cmp_antisym(b, c);
    }
}

/// Part types and lengths the entry reads.
pub proof fn lemma_kf_parts(np: Seq<PartView>, sp: Seq<PartView>)
    requires kfacts(np, sp),
    ensures
        np.len() == numi::PART_COUNT,
        np[numi::P_UOM_OFF as int] is U64, np[numi::P_UOM_BYTES as int] is U8, np[numi::P_UOM_RUNS as int] is U64,
        np[numi::P_ADSH_OFF as int] is U64, np[numi::P_ADSH_BYTES as int] is U8,
        np[numi::P_TAG_OFF as int] is U64, np[numi::P_TAG_BYTES as int] is U8,
        np[numi::P_RUN_ADSH as int] is U64, np[numi::P_RUN_START as int] is U64,
        np[numi::P_TV as int] is U64, np[numi::P_PAIR_TAG as int] is U64, np[numi::P_VALUE as int] is I128,
        numi::uom_count(np) >= 0, numi::adsh_count(np) >= 0, numi::tag_count(np) >= 0,
        text_parts_wf(u64_part(np[numi::P_UOM_OFF as int]), u8_part(np[numi::P_UOM_BYTES as int]), numi::uom_count(np)),
        text_strictly_sorted(u64_part(np[numi::P_UOM_OFF as int]), u8_part(np[numi::P_UOM_BYTES as int]), numi::uom_count(np)),
        text_parts_wf(u64_part(np[numi::P_TAG_OFF as int]), u8_part(np[numi::P_TAG_BYTES as int]), numi::tag_count(np)),
        numi::u64s(np, numi::P_UOM_RUNS).len() == numi::uom_count(np) + 1,
        numi::u64s(np, numi::P_RUN_START).len() == numi::run_count(np) + 1,
        sp.len() == subi::PART_COUNT,
        sp[subi::P_CIK as int] is I32, sp[subi::P_FY as int] is I32, sp[subi::P_FY_VALID as int] is U8,
        sp[subi::P_ADSH_OFF as int] is U64, sp[subi::P_ADSH_BYTES as int] is U8,
        sp[subi::P_NAME_CODES as int] is U64, sp[subi::P_ADSH_ORDER as int] is U64,
        sp[subi::P_NAME_DICT_OFF as int] is U64, sp[subi::P_NAME_DICT_BYTES as int] is U8,
        u64_part(sp[subi::P_ADSH_OFF as int]).len() == subi::row_count(sp) + 1,
        name_count(sp) >= 0,
        text_parts_wf(u64_part(sp[subi::P_NAME_DICT_OFF as int]), u8_part(sp[subi::P_NAME_DICT_BYTES as int]), name_count(sp)),
        forall|r: int| 0 <= r < numi::run_count(np) ==> #[trigger] numi::u64s(np, numi::P_RUN_UOM)[r] < numi::uom_count(np),
{
    reveal(kfacts);
}

/// The runs of unit code `u` are `[g[u], g[u + 1])` of the unit directory `g`.
pub proof fn lemma_kf_uom(np: Seq<PartView>, sp: Seq<PartView>, u: int)
    requires kfacts(np, sp), 0 <= u < numi::uom_count(np),
    ensures ({
        let g = numi::u64s(np, numi::P_UOM_RUNS);
        &&& g[u] <= g[u + 1] <= numi::run_count(np)
        &&& forall|r: int| #![trigger numi::u64s(np, numi::P_RUN_UOM)[r]] 0 <= r < numi::run_count(np)
            ==> ((numi::u64s(np, numi::P_RUN_UOM)[r] == u) <==> g[u] <= r < g[u + 1])
    }),
{
    reveal(kfacts);
    numi::lemma_uom_runs(np, u);
}

/// A database bound to the stores gives both layouts.
pub proof fn lemma_bound_kfacts(sv: crate::gendb_entry::stores::StoresView, db: Database)
    requires crate::gendb_entry::bound_db(sv, db),
    ensures kfacts(sv.num_vord, sv.sub), subi::row_count(sv.sub) == db.tables[0].len(),
{
    let (np, sp) = (sv.num_vord, sv.sub);
    lemma_bound_parts(sv, db);
    lemma_bound_layouts(np, sp, db);
    assert forall|j1: int, j2: int| 0 <= j1 < subi::row_count(sp) && 0 <= j2 < subi::row_count(sp)
        && #[trigger] subi::adsh_bytes(sp, j1) == #[trigger] subi::adsh_bytes(sp, j2) implies j1 == j2 by {
        lemma_sub_pk(np, sp, db, j1, j2);
    }
    reveal(kfacts);
}

/// Lengths of num's per-row and per-run parts.
pub proof fn lemma_kf_lens(np: Seq<PartView>, sp: Seq<PartView>)
    requires kfacts(np, sp),
    ensures
        numi::u64s(np, numi::P_TV).len() == numi::row_count(np),
        n_value(np).len() == numi::row_count(np),
        numi::u64s(np, numi::P_RUN_ADSH).len() == numi::run_count(np),
        n_start(np).len() == numi::run_count(np) + 1,
{
    reveal(kfacts);
}

} // verus!
