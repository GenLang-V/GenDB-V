//! Column formats of stored tables and their decode specifications: row groups (`groups_wf`), frame-of-reference
//! integer codes (`for_at`: a group's base plus an unsigned code), sorted text dictionaries (`dict_sorted`), plain
//! text (`text_of`: U64 offsets + U8 bytes), stored-to-canonical row maps (`is_perm`, `stored_rows`), per-column
//! row predicates, zone maps, and the lemmas a reader or query needs (group lookup, dictionary order, the multiset
//! of a permuted relation).
//!
//! Layout vocabulary (no query constant, no table):
//! - row groups: a U64 part `gs` of `m + 1` entries, `gs[0] == 0`, strictly increasing, `gs[m] == n`; group `g`
//!   holds the stored rows `gs[g] .. gs[g + 1]`;
//! - a frame-of-reference (FOR) column: a base part (I64 or U64, one entry per group) and a code part (U8, U16, U32
//!   or U64, one entry per row); row `j` of group `g` has the integer `base[g] + code[j]`;
//! - a dictionary column: a FOR column of dictionary indices plus a dictionary in text parts (`text_of`), its
//!   entries strictly increasing in bytewise order (`lex_cmp`), so distinct;
//! - a plain text column: U64 offsets (`n + 1` entries) and U8 bytes; value `j` is `bytes[offs[j] .. offs[j + 1]]`.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::part_len;
use crate::spec::value::{Row, Val};
use crate::spec::text::lex_cmp;

verus! {

// ------------------------------------------------------------------------------------------------ part views

/// The bytes of a U8 part (empty for another kind).
pub open spec fn u8s(p: PartView) -> Seq<u8> {
    match p {
        PartView::U8(s) => s,
        _ => Seq::empty(),
    }
}

/// The values of a U32 part (empty for another kind).
pub open spec fn u32s(p: PartView) -> Seq<u32> {
    match p {
        PartView::U32(s) => s,
        _ => Seq::empty(),
    }
}

/// The values of a U64 part (empty for another kind).
pub open spec fn u64s(p: PartView) -> Seq<u64> {
    match p {
        PartView::U64(s) => s,
        _ => Seq::empty(),
    }
}

/// The values of an I64 part (empty for another kind).
pub open spec fn i64s(p: PartView) -> Seq<i64> {
    match p {
        PartView::I64(s) => s,
        _ => Seq::empty(),
    }
}

/// Code parts hold unsigned integers: U8, U16, U32 or U64.
pub open spec fn is_code_part(p: PartView) -> bool {
    p is U8 || p is U16 || p is U32 || p is U64
}

/// The unsigned integer at position `i` of a code part.
pub open spec fn code_at(p: PartView, i: int) -> int {
    match p {
        PartView::U8(s) => s[i] as int,
        PartView::U16(s) => s[i] as int,
        PartView::U32(s) => s[i] as int,
        PartView::U64(s) => s[i] as int,
        _ => 0,
    }
}

/// Codes are never negative.
pub proof fn lemma_code_nonneg(p: PartView, i: int)
    ensures code_at(p, i) >= 0,
{
}

// ------------------------------------------------------------------------------------------------ row groups

/// Row groups over `n` rows: `gs[0] == 0`, strictly increasing, last entry `n` (`gs.len() - 1` groups).
pub open spec fn groups_wf(gs: Seq<u64>, n: int) -> bool {
    &&& gs.len() >= 1
    &&& gs[0] == 0
    &&& gs[gs.len() - 1] == n
    &&& forall|g: int| 0 <= g < gs.len() - 1 ==> #[trigger] gs[g] < gs[g + 1]
}

/// Stored row `j` lies in group `g`.
pub open spec fn in_group(gs: Seq<u64>, g: int, j: int) -> bool {
    0 <= g < gs.len() - 1 && gs[g] <= j < gs[g + 1]
}

/// The group of stored row `j` (meaningful for `0 <= j < n` under `groups_wf(gs, n)`).
pub open spec fn group_of(gs: Seq<u64>, j: int) -> int {
    choose|g: int| in_group(gs, g, j)
}

/// Group starts are strictly increasing.
pub proof fn lemma_groups_mono(gs: Seq<u64>, n: int, a: int, b: int)
    requires
        groups_wf(gs, n),
        0 <= a < b < gs.len(),
    ensures
        gs[a] < gs[b],
    decreases b - a,
{
    if b > a + 1 {
        lemma_groups_mono(gs, n, a, b - 1);
    }
    assert(gs[b - 1] < gs[(b - 1) + 1]);
}

/// Every group start lies in `[0, n]`.
pub proof fn lemma_groups_bounds(gs: Seq<u64>, n: int, g: int)
    requires
        groups_wf(gs, n),
        0 <= g < gs.len(),
    ensures
        0 <= gs[g] <= n,
        g < gs.len() - 1 ==> gs[g] < n,
{
    if g < gs.len() - 1 {
        lemma_groups_mono(gs, n, g, gs.len() - 1);
    }
}

proof fn lemma_group_search(gs: Seq<u64>, n: int, j: int, g: int)
    requires
        groups_wf(gs, n),
        0 <= g < gs.len() - 1,
        gs[g] <= j < n,
    ensures
        exists|h: int| in_group(gs, h, j),
    decreases gs.len() - g,
{
    if j < gs[g + 1] {
        assert(in_group(gs, g, j));
    } else {
        if g + 1 == gs.len() - 1 {
            assert(false);
        }
        lemma_group_search(gs, n, j, g + 1);
    }
}

/// Every stored row lies in one group: `group_of` finds it.
pub proof fn lemma_group_of(gs: Seq<u64>, n: int, j: int)
    requires
        groups_wf(gs, n),
        0 <= j < n,
    ensures
        in_group(gs, group_of(gs, j), j),
{
    if gs.len() == 1 {
        assert(false);
    }
    assert(gs[0int] < gs[0int + 1]);
    lemma_group_search(gs, n, j, 0);
}

/// Groups are disjoint: the group a row lies in is `group_of`.
pub proof fn lemma_group_of_unique(gs: Seq<u64>, n: int, g: int, j: int)
    requires
        groups_wf(gs, n),
        in_group(gs, g, j),
    ensures
        group_of(gs, j) == g,
{
    lemma_groups_bounds(gs, n, g + 1);
    lemma_group_of(gs, n, j);
    let h = group_of(gs, j);
    if h < g {
        if h + 1 < g {
            lemma_groups_mono(gs, n, h + 1, g);
        }
    } else if h > g {
        if g + 1 < h {
            lemma_groups_mono(gs, n, g + 1, h);
        }
    }
}

// ------------------------------------------------------------------------------------------------ FOR columns

/// Base of group `g` of a frame-of-reference column: an I64 part (signed values) or a U64 part (indices).
pub open spec fn base_at(b: PartView, g: int) -> int {
    match b {
        PartView::I64(s) => s[g] as int,
        PartView::U64(s) => s[g] as int,
        _ => 0,
    }
}

/// The integer of stored row `j` of a frame-of-reference column: its group's base plus its code.
pub open spec fn for_at(gs: Seq<u64>, base: PartView, codes: PartView, j: int) -> int {
    base_at(base, group_of(gs, j)) + code_at(codes, j)
}

/// Shape of a frame-of-reference column over `n` rows and the groups `gs`: one base per group, one code per row.
pub open spec fn for_shape(gs: Seq<u64>, base: PartView, codes: PartView, n: int) -> bool {
    &&& (base is I64 || base is U64)
    &&& part_len(base) == gs.len() - 1
    &&& is_code_part(codes)
    &&& part_len(codes) == n
}

/// Inside a known group, `for_at` is that group's base plus the code.
pub proof fn lemma_for_at(gs: Seq<u64>, n: int, base: PartView, codes: PartView, g: int, j: int)
    requires
        groups_wf(gs, n),
        in_group(gs, g, j),
    ensures
        for_at(gs, base, codes, j) == base_at(base, g) + code_at(codes, j),
{
    lemma_group_of_unique(gs, n, g, j);
}

/// Zone map: `zmax[g]` bounds every value of group `g` from above (the base bounds it from below, codes being
/// unsigned).
pub open spec fn zone_max_ok(gs: Seq<u64>, base: PartView, codes: PartView, zmax: Seq<i64>) -> bool {
    &&& zmax.len() == gs.len() - 1
    &&& forall|g: int, j: int| #[trigger] in_group(gs, g, j) ==> base_at(base, g) + code_at(codes, j) <= zmax[g]
}

// ------------------------------------------------------------------------------------------------ text parts

/// Value `j`'s byte range `offs[j] .. offs[j + 1]` lies inside `bytes`.
pub open spec fn text_range_ok(offs: Seq<u64>, bytes: Seq<u8>, j: int) -> bool {
    offs[j] <= offs[j + 1] && offs[j + 1] <= bytes.len()
}

/// Offsets (U64, `n + 1` entries) and bytes of `n` text values: each value is a byte range inside `bytes`
/// (instantiate with `text_range_ok(offs, bytes, j)`).
pub open spec fn text_parts_wf(offs: Seq<u64>, bytes: Seq<u8>, n: int) -> bool {
    &&& n >= 0
    &&& offs.len() == n + 1
    &&& forall|j: int| 0 <= j < n ==> #[trigger] text_range_ok(offs, bytes, j)
}

/// Text value `j`: `bytes[offs[j] .. offs[j + 1]]`.
pub open spec fn text_of(offs: Seq<u64>, bytes: Seq<u8>, j: int) -> Seq<u8> {
    bytes.subrange(offs[j] as int, offs[j + 1] as int)
}

/// The `k` dictionary entries are strictly increasing in bytewise order (so distinct).
pub open spec fn dict_sorted(doffs: Seq<u64>, dbytes: Seq<u8>, k: int) -> bool {
    forall|a: int| 0 <= a < k - 1 ==> #[trigger] lex_cmp(text_of(doffs, dbytes, a), text_of(doffs, dbytes, a + 1)) < 0
}

/// A sorted dictionary is strictly increasing between any two entries.
pub proof fn lemma_dict_order(doffs: Seq<u64>, dbytes: Seq<u8>, k: int, a: int, b: int)
    requires
        dict_sorted(doffs, dbytes, k),
        0 <= a < b < k,
    ensures
        lex_cmp(text_of(doffs, dbytes, a), text_of(doffs, dbytes, b)) < 0,
    decreases b - a,
{
    let (x, y) = (text_of(doffs, dbytes, a), text_of(doffs, dbytes, b));
    assert(lex_cmp(text_of(doffs, dbytes, b - 1), text_of(doffs, dbytes, (b - 1) + 1)) < 0);
    if b > a + 1 {
        lemma_dict_order(doffs, dbytes, k, a, b - 1);
        let z = text_of(doffs, dbytes, b - 1);
        crate::bridge::order::lemma_lex_cmp_trans(x, z, y);
        if lex_cmp(x, y) == 0 {
            crate::bridge::equality::lemma_lex_cmp_zero(x, y);
            crate::bridge::order::lemma_lex_cmp_antisym(z, y);
        }
    }
}

/// Distinct entries of a sorted dictionary hold distinct texts.
pub proof fn lemma_dict_distinct(doffs: Seq<u64>, dbytes: Seq<u8>, k: int, a: int, b: int)
    requires
        dict_sorted(doffs, dbytes, k),
        0 <= a < k,
        0 <= b < k,
        a != b,
    ensures
        text_of(doffs, dbytes, a) != text_of(doffs, dbytes, b),
{
    let (x, y) = (text_of(doffs, dbytes, a), text_of(doffs, dbytes, b));
    crate::bridge::equality::lemma_lex_cmp_zero(x, y);
    if a < b {
        lemma_dict_order(doffs, dbytes, k, a, b);
    } else {
        lemma_dict_order(doffs, dbytes, k, b, a);
        crate::bridge::equality::lemma_lex_cmp_zero(y, x);
    }
}

// ------------------------------------------------------------------------------------------------ column predicates

/// Column `c` of every stored row is the bigint (or integer) its FOR codes give.
pub open spec fn int_col(rows: Seq<Row>, c: int, gs: Seq<u64>, base: PartView, codes: PartView) -> bool {
    forall|j: int| 0 <= j < rows.len() ==> #[trigger] rows[j][c] == Val::Int(for_at(gs, base, codes, j))
}

/// Column `c` of every stored row is the numeric of scale `scale` whose coefficient its FOR codes give.
pub open spec fn num_col(rows: Seq<Row>, c: int, scale: nat, gs: Seq<u64>, base: PartView, codes: PartView) -> bool {
    forall|j: int| 0 <= j < rows.len() ==> #[trigger] rows[j][c] == (Val::Num { coeff: for_at(gs, base, codes, j), scale })
}

/// Column `c` of every stored row is the date (days since 2000-01-01, `Val::Date`) its FOR codes give.
pub open spec fn date_col(rows: Seq<Row>, c: int, gs: Seq<u64>, base: PartView, codes: PartView) -> bool {
    forall|j: int| 0 <= j < rows.len() ==> #[trigger] rows[j][c] == Val::Date(for_at(gs, base, codes, j))
}

/// Column `c` of every stored row is the dictionary entry whose index its FOR codes give.
pub open spec fn dict_col(rows: Seq<Row>, c: int, gs: Seq<u64>, base: PartView, codes: PartView, doffs: Seq<u64>, dbytes: Seq<u8>) -> bool {
    forall|j: int| 0 <= j < rows.len() ==> {
        &&& 0 <= for_at(gs, base, codes, j) < doffs.len() - 1
        &&& #[trigger] rows[j][c] == Val::Text(text_of(doffs, dbytes, for_at(gs, base, codes, j)))
    }
}

/// Column `c` of every stored row is its plain text value.
pub open spec fn text_col(rows: Seq<Row>, c: int, offs: Seq<u64>, bytes: Seq<u8>) -> bool {
    forall|j: int| 0 <= j < rows.len() ==> #[trigger] rows[j][c] == Val::Text(text_of(offs, bytes, j))
}

/// Every row of `rel` has `w` columns.
pub open spec fn rows_width(rel: Seq<Row>, w: int) -> bool {
    forall|i: int| 0 <= i < rel.len() ==> #[trigger] rel[i].len() == w
}

// ------------------------------------------------------------------------------------------------ row maps

/// `i` is the canonical index of some stored row.
pub open spec fn covered(rmap: Seq<int>, i: int) -> bool {
    exists|j: int| 0 <= j < rmap.len() && rmap[j] == i
}

/// `rmap` (stored row -> canonical row) is a bijection of `[0, n)`.
pub open spec fn is_perm(rmap: Seq<int>, n: int) -> bool {
    &&& rmap.len() == n
    &&& forall|j: int| 0 <= j < n ==> 0 <= #[trigger] rmap[j] < n
    &&& forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b ==> #[trigger] rmap[a] != #[trigger] rmap[b]
    &&& forall|i: int| 0 <= i < n ==> #[trigger] covered(rmap, i)
}

/// The identity row map of `n` rows.
pub open spec fn identity_map(n: int) -> Seq<int> {
    Seq::new(n as nat, |j: int| j)
}

/// The row map whose stored row `j` is canonical row `for_at(gs, base, codes, j)`.
pub open spec fn for_map(gs: Seq<u64>, base: PartView, codes: PartView, n: int) -> Seq<int> {
    Seq::new(n as nat, |j: int| for_at(gs, base, codes, j))
}

/// The stored rows: stored row `j` is canonical row `rmap[j]` of `rel`.
pub open spec fn stored_rows(rel: Seq<Row>, rmap: Seq<int>) -> Seq<Row> {
    Seq::new(rmap.len(), |j: int| rel[rmap[j]])
}

/// The identity is a bijection.
pub proof fn lemma_identity_perm(n: int)
    requires n >= 0,
    ensures is_perm(identity_map(n), n),
{
    let m = identity_map(n);
    assert forall|i: int| 0 <= i < n implies #[trigger] covered(m, i) by {
        assert(m[i] == i);
    }
}

/// Two relations of `n` rows of width `w` whose stored rows under one bijection agree are equal.
pub proof fn lemma_stored_rows_determine(a: Seq<Row>, b: Seq<Row>, rmap: Seq<int>, n: int, w: int)
    requires
        a.len() == n,
        b.len() == n,
        is_perm(rmap, n),
        rows_width(a, w),
        rows_width(b, w),
        forall|j: int, c: int| 0 <= j < n && 0 <= c < w ==> #[trigger] stored_rows(a, rmap)[j][c] == stored_rows(b, rmap)[j][c],
    ensures
        a == b,
{
    assert forall|i: int| 0 <= i < n implies a[i] == b[i] by {
        assert(covered(rmap, i));
        let j = choose|j: int| 0 <= j < rmap.len() && rmap[j] == i;
        assert forall|c: int| 0 <= c < w implies a[i][c] == b[i][c] by {
            assert(stored_rows(a, rmap)[j][c] == stored_rows(b, rmap)[j][c]);
        }
        assert(a[i] =~= b[i]);
    }
    assert(a =~= b);
}

proof fn lemma_perm_remove(rmap: Seq<int>, n: int, j0: int)
    requires
        is_perm(rmap, n),
        0 <= j0 < n,
        rmap[j0] == n - 1,
    ensures
        is_perm(rmap.remove(j0), n - 1),
{
    let r = rmap.remove(j0);
    assert forall|j: int| 0 <= j < n - 1 implies 0 <= #[trigger] r[j] < n - 1 by {
        let k = if j < j0 { j } else { j + 1 };
        assert(r[j] == rmap[k]);
        assert(rmap[k] != rmap[j0]);
    }
    assert forall|a: int, b: int| 0 <= a < n - 1 && 0 <= b < n - 1 && a != b implies #[trigger] r[a] != #[trigger] r[b] by {
        let ka = if a < j0 { a } else { a + 1 };
        let kb = if b < j0 { b } else { b + 1 };
        assert(r[a] == rmap[ka] && r[b] == rmap[kb]);
    }
    assert forall|i: int| 0 <= i < n - 1 implies #[trigger] covered(r, i) by {
        assert(covered(rmap, i));
        let k = choose|k: int| 0 <= k < rmap.len() && rmap[k] == i;
        assert(k != j0);
        let j = if k < j0 { k } else { k - 1 };
        assert(r[j] == i);
    }
}

/// The stored rows of a bijection are a permutation of the relation: same multiset (so the same sums and counts,
/// `link::join::lemma_sum_of_perm`).
pub proof fn lemma_stored_rows_multiset(rel: Seq<Row>, rmap: Seq<int>)
    requires
        is_perm(rmap, rel.len() as int),
    ensures
        stored_rows(rel, rmap).to_multiset() == rel.to_multiset(),
    decreases rel.len(),
{
    let n = rel.len() as int;
    let s = stored_rows(rel, rmap);
    if n == 0 {
        assert(s =~= Seq::<Row>::empty());
        assert(rel =~= Seq::<Row>::empty());
    } else {
        assert(covered(rmap, n - 1));
        let j0 = choose|j: int| 0 <= j < rmap.len() && rmap[j] == n - 1;
        let r2 = rmap.remove(j0);
        lemma_perm_remove(rmap, n, j0);
        let rel2 = rel.drop_last();
        lemma_stored_rows_multiset(rel2, r2);
        let s2 = stored_rows(rel2, r2);
        assert forall|j: int| 0 <= j < n - 1 implies #[trigger] s.remove(j0)[j] == s2[j] by {
            let k = if j < j0 { j } else { j + 1 };
            assert(r2[j] == rmap[k]);
            assert(rmap[k] != rmap[j0]);
            assert(0 <= rmap[k] < n - 1);
        }
        assert(s.remove(j0) =~= s2);
        broadcast use vstd::multiset::group_multiset_axioms;
        vstd::seq_lib::to_multiset_remove(s, j0);
        assert(rel2.push(rel.last()) =~= rel);
        vstd::seq_lib::to_multiset_build(rel2, rel.last());
        assert(s[j0] == rel[n - 1]);
        vstd::seq_lib::to_multiset_contains(s, s[j0]);
        assert(s.contains(s[j0]));
        assert(s.to_multiset().count(s[j0]) > 0);
        assert(s.to_multiset() =~= s.to_multiset().remove(s[j0]).insert(s[j0]));
    }
}

// ------------------------------------------------------------------------------------------------ uniform groups

/// Number of blocks of `bsize` rows over `n` rows.
pub open spec fn nblocks_of(n: int, bsize: int) -> int {
    (n + bsize - 1) / bsize
}

/// Uniform row groups: group `g` starts at `g * bsize`; the last group ends at `n`.
pub open spec fn uniform_gs(n: int, bsize: int) -> Seq<u64> {
    Seq::new((nblocks_of(n, bsize) + 1) as nat, |g: int| if g < nblocks_of(n, bsize) { (g * bsize) as u64 } else { n as u64 })
}

/// The group part of a table: U64, uniform groups of `bsize >= 1` rows over `n` rows.
pub open spec fn groups_part_ok(p: PartView, n: int, bsize: int) -> bool {
    &&& p is U64
    &&& 1 <= bsize
    &&& 0 <= n
    &&& n + bsize <= u64::MAX
    &&& u64s(p) == uniform_gs(n, bsize)
}

pub proof fn lemma_nblocks(n: int, bsize: int)
    requires 0 <= n, 1 <= bsize,
    ensures
        nblocks_of(n, bsize) >= 0,
        nblocks_of(n, bsize) * bsize >= n,
        nblocks_of(n, bsize) > 0 ==> (nblocks_of(n, bsize) - 1) * bsize < n,
        n == 0 ==> nblocks_of(n, bsize) == 0,
{
    let m = n + bsize - 1;
    let q = m / bsize;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m, bsize);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(m, bsize);
    assert(bsize * q == q * bsize) by (nonlinear_arith);
    assert(q >= 0) by (nonlinear_arith) requires q * bsize + m % bsize == m, m >= 0, m % bsize < bsize, bsize >= 1;
    assert(q * bsize >= n) by (nonlinear_arith) requires q * bsize + m % bsize == m, m == n + bsize - 1, m % bsize < bsize;
    if q > 0 {
        assert((q - 1) * bsize < n) by (nonlinear_arith) requires q * bsize + m % bsize == m, m == n + bsize - 1, m % bsize >= 0;
    }
    if n == 0 {
        assert(q == 0) by (nonlinear_arith) requires q * bsize + m % bsize == m, m == bsize - 1, m % bsize >= 0, bsize >= 1, q >= 0;
    }
}

/// Uniform groups are well formed, and row `j` lies in group `j / bsize` (its block).
pub proof fn lemma_uniform_groups(p: PartView, n: int, bsize: int)
    requires groups_part_ok(p, n, bsize),
    ensures
        groups_wf(u64s(p), n),
        u64s(p).len() == nblocks_of(n, bsize) + 1,
        forall|g: int| 0 <= g < nblocks_of(n, bsize) ==> #[trigger] u64s(p)[g] == g * bsize,
{
    let gs = u64s(p);
    let nb = nblocks_of(n, bsize);
    lemma_nblocks(n, bsize);
    assert forall|g: int| 0 <= g < nb implies #[trigger] gs[g] == g * bsize by {
        assert(g * bsize <= (nb - 1) * bsize) by (nonlinear_arith) requires g <= nb - 1, bsize >= 1;
        assert(g * bsize >= 0) by (nonlinear_arith) requires g >= 0, bsize >= 1;
    }
    assert forall|g: int| 0 <= g < gs.len() - 1 implies #[trigger] gs[g] < gs[g + 1] by {
        if g + 1 < nb {
            assert(g * bsize < (g + 1) * bsize) by (nonlinear_arith) requires bsize >= 1;
        } else {
            assert(gs[g] == g * bsize);
        }
    }
    if nb == 0 {
        assert(gs[0] == n);
    } else {
        assert(gs[0] == 0 * bsize);
    }
}

/// Row `j` of uniform groups lies in group `g` exactly when `g * bsize <= j < min((g + 1) * bsize, n)`.
pub proof fn lemma_uniform_in_group(p: PartView, n: int, bsize: int, g: int, j: int)
    requires
        groups_part_ok(p, n, bsize),
        0 <= g,
        g * bsize <= j,
        j < (g + 1) * bsize,
        j < n,
    ensures
        in_group(u64s(p), g, j),
        group_of(u64s(p), j) == g,
{
    let gs = u64s(p);
    let nb = nblocks_of(n, bsize);
    lemma_uniform_groups(p, n, bsize);
    lemma_nblocks(n, bsize);
    assert(g < nb) by {
        if g >= nb {
            assert(g * bsize >= nb * bsize) by (nonlinear_arith) requires g >= nb, bsize >= 1;
        }
    }
    assert(gs[g] == g * bsize);
    if g + 1 < nb {
        assert(gs[g + 1] == (g + 1) * bsize);
    } else {
        assert(gs[g + 1] == n);
    }
    lemma_group_of_unique(gs, n, g, j);
}

// ------------------------------------------------------------------------------------------------ columns by part index

/// The group part's view.
pub open spec fn gs_at(parts: Seq<PartView>, gp: int) -> Seq<u64> {
    u64s(parts[gp])
}

/// Frame-of-reference column with an I64 base part `bp` and code part `cp` over the groups at `gp`.
pub open spec fn for_i64_shape(parts: Seq<PartView>, gp: int, cp: int, bp: int, n: int) -> bool {
    &&& 0 <= gp < parts.len() && 0 <= cp < parts.len() && 0 <= bp < parts.len()
    &&& parts[bp] is I64
    &&& for_shape(gs_at(parts, gp), parts[bp], parts[cp], n)
}

/// Frame-of-reference column with a U64 base part `bp` and code part `cp` over the groups at `gp`.
pub open spec fn for_u64_shape(parts: Seq<PartView>, gp: int, cp: int, bp: int, n: int) -> bool {
    &&& 0 <= gp < parts.len() && 0 <= cp < parts.len() && 0 <= bp < parts.len()
    &&& parts[bp] is U64
    &&& for_shape(gs_at(parts, gp), parts[bp], parts[cp], n)
}

/// A bigint column: FOR codes `cp`, I64 bases `bp`.
pub open spec fn int_col_at(parts: Seq<PartView>, gp: int, cp: int, bp: int, rows: Seq<Row>, c: int) -> bool {
    &&& for_i64_shape(parts, gp, cp, bp, rows.len() as int)
    &&& int_col(rows, c, gs_at(parts, gp), parts[bp], parts[cp])
}

/// A numeric column of scale `scale`: FOR codes `cp` of coefficients, I64 bases `bp`.
pub open spec fn num_col_at(parts: Seq<PartView>, gp: int, cp: int, bp: int, rows: Seq<Row>, c: int, scale: nat) -> bool {
    &&& for_i64_shape(parts, gp, cp, bp, rows.len() as int)
    &&& num_col(rows, c, scale, gs_at(parts, gp), parts[bp], parts[cp])
}

/// A date column: FOR codes `cp` of days since 2000-01-01, I64 bases `bp`.
pub open spec fn date_col_at(parts: Seq<PartView>, gp: int, cp: int, bp: int, rows: Seq<Row>, c: int) -> bool {
    &&& for_i64_shape(parts, gp, cp, bp, rows.len() as int)
    &&& date_col(rows, c, gs_at(parts, gp), parts[bp], parts[cp])
}

/// A zone map `zp` (I64, one maximum per group) over the FOR column `cp`/`bp`.
pub open spec fn zone_at(parts: Seq<PartView>, gp: int, cp: int, bp: int, zp: int) -> bool {
    &&& 0 <= zp < parts.len()
    &&& parts[zp] is I64
    &&& zone_max_ok(gs_at(parts, gp), parts[bp], parts[cp], i64s(parts[zp]))
}

/// A dictionary column: FOR codes `cp` and U64 bases `bp` of dictionary indices, dictionary offsets `op` (U64) and
/// bytes `yp` (U8), entries strictly increasing.
pub open spec fn dict_col_at(parts: Seq<PartView>, gp: int, cp: int, bp: int, op: int, yp: int, rows: Seq<Row>, c: int) -> bool {
    &&& for_u64_shape(parts, gp, cp, bp, rows.len() as int)
    &&& 0 <= op < parts.len() && 0 <= yp < parts.len()
    &&& parts[op] is U64 && parts[yp] is U8
    &&& u64s(parts[op]).len() >= 1
    &&& text_parts_wf(u64s(parts[op]), u8s(parts[yp]), u64s(parts[op]).len() - 1)
    &&& dict_sorted(u64s(parts[op]), u8s(parts[yp]), u64s(parts[op]).len() - 1)
    &&& dict_col(rows, c, gs_at(parts, gp), parts[bp], parts[cp], u64s(parts[op]), u8s(parts[yp]))
}

/// A plain text column: offsets `op` (U64, `n + 1`) and bytes `yp` (U8).
pub open spec fn text_col_at(parts: Seq<PartView>, op: int, yp: int, rows: Seq<Row>, c: int) -> bool {
    &&& 0 <= op < parts.len() && 0 <= yp < parts.len()
    &&& parts[op] is U64 && parts[yp] is U8
    &&& text_parts_wf(u64s(parts[op]), u8s(parts[yp]), rows.len() as int)
    &&& text_col(rows, c, u64s(parts[op]), u8s(parts[yp]))
}

/// Two relations of `w`-column rows that agree on every row and column are equal.
pub proof fn lemma_rows_eq(a: Seq<Row>, b: Seq<Row>, w: int)
    requires
        a.len() == b.len(),
        rows_width(a, w),
        rows_width(b, w),
        forall|j: int, c: int| 0 <= j < a.len() && 0 <= c < w ==> #[trigger] a[j][c] == b[j][c],
    ensures
        a == b,
{
    assert forall|j: int| 0 <= j < a.len() implies a[j] == b[j] by {
        assert forall|c: int| 0 <= c < w implies a[j][c] == b[j][c] by {}
        assert(a[j] =~= b[j]);
    }
    assert(a =~= b);
}

/// A stored-to-canonical row map column: FOR codes `cp` and U64 bases `bp` of canonical row indices, a bijection of
/// `[0, n)` (stored row `j` is canonical row `for_at(gs, base, codes, j)`).
pub open spec fn perm_col_at(parts: Seq<PartView>, gp: int, cp: int, bp: int, n: int) -> bool {
    &&& for_u64_shape(parts, gp, cp, bp, n)
    &&& is_perm(for_map(gs_at(parts, gp), parts[bp], parts[cp], n), n)
}

/// The stored rows of a table whose row map column is `cp`/`bp`: stored row `j` is `rel[for_at(.., j)]`.
pub open spec fn perm_rows(parts: Seq<PartView>, gp: int, cp: int, bp: int, rel: Seq<Row>) -> Seq<Row> {
    stored_rows(rel, for_map(gs_at(parts, gp), parts[bp], parts[cp], rel.len() as int))
}

} // verus!
