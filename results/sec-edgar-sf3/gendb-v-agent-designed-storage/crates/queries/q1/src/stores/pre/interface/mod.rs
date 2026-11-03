//! Storage `pre`: the `pre` table (`n` rows, one per presented line), clustered by
//! `(adsh, (stmt, rfile), tag, version)`.
//!
//! Stored order. Stored row `i` is canonical row `orig[i]` (`P_ORIG`, a permutation of `0..n`). Stored rows are
//! sorted by (adsh code, group code, pair code, canonical row), where a group is a distinct `(stmt, rfile)` pair:
//! - sub-runs: `P_SUB_START` (`S + 1` entries) cuts the stored rows into `S` nonempty sub-runs of equal
//!   `(adsh, group)`; sub-run `s` is stored rows `[sub_start[s], sub_start[s + 1])` with adsh code `sub_adsh[s]` and
//!   group code `sub_group[s]`; sub-run keys strictly increase lexicographically (each `(adsh, stmt, rfile)`
//!   combination is exactly one sub-run, so the sub-runs of one group count its distinct filings);
//! - `P_ADSH_SUBS` (`A + 1` entries): the sub-runs of adsh code `a` are `[adsh_subs[a], adsh_subs[a + 1])`
//!   (`group_starts_ok`); together they are the filing's rows;
//! - inside a sub-run the pair codes `tv` are nondecreasing (rows of one `(tag, version)` are adjacent).
//! Groups: `(group_stmt[g], group_rfile[g])`, strictly increasing; `group_stmt[g]` is 0 for a NULL stmt and
//! `1 + stmt code` otherwise; `group_rfile[g]` is an rfile code.
//! Dictionaries (sorted, distinct, code order = byte order; `common::text`): adsh, stmt, rfile, tag, version, plabel.
//! `(tag, version)` is coded per row as a pair code `tv[i]` into the pair list `(pair_tag[p], pair_version[p])`,
//! strictly increasing lexicographically (pair code order is (tag, version) byte order).
//! Per stored row: `tv`, `line` (I32), `plabel` code and validity (U8, 0 = NULL; the code then means nothing).
//! In canonical row order (row `j`): `report`, `inpth`, `negating`.
use vstd::prelude::*;
use crate::spec::value::{Row, Val};
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::StoredParts;
pub mod common;
use common::text::{text_entry, u64_part, u8_part};
use common::cols::{i32_part, text_count, u64s, list_entry, sorted_list_ok, coded_text_at, coded_col_ok};
use common::perm::{is_permutation, lemma_permutation_facts, position_of};
use common::runs::*;

verus! {

pub const P_ORIG: usize = 0;
pub const P_SUB_START: usize = 1;
pub const P_SUB_ADSH: usize = 2;
pub const P_SUB_GROUP: usize = 3;
pub const P_ADSH_SUBS: usize = 4;
pub const P_ADSH_OFF: usize = 5;
pub const P_ADSH_BYTES: usize = 6;
pub const P_GROUP_STMT: usize = 7;
pub const P_GROUP_RFILE: usize = 8;
pub const P_STMT_OFF: usize = 9;
pub const P_STMT_BYTES: usize = 10;
pub const P_RFILE_OFF: usize = 11;
pub const P_RFILE_BYTES: usize = 12;
pub const P_TV: usize = 13;
pub const P_PAIR_TAG: usize = 14;
pub const P_PAIR_VERSION: usize = 15;
pub const P_TAG_OFF: usize = 16;
pub const P_TAG_BYTES: usize = 17;
pub const P_VERSION_OFF: usize = 18;
pub const P_VERSION_BYTES: usize = 19;
pub const P_LINE: usize = 20;
pub const P_PLABEL_CODES: usize = 21;
pub const P_PLABEL_VALID: usize = 22;
pub const P_PLABEL_OFF: usize = 23;
pub const P_PLABEL_BYTES: usize = 24;
pub const P_REPORT: usize = 25;
pub const P_INPTH: usize = 26;
pub const P_NEGATING: usize = 27;
pub const PART_COUNT: usize = 28;

/// Row count `n`.
pub open spec fn row_count(parts: Seq<PartView>) -> int {
    u64s(parts, P_ORIG).len() as int
}

/// Sub-run count `S`.
pub open spec fn sub_count(parts: Seq<PartView>) -> int {
    u64s(parts, P_SUB_ADSH).len() as int
}

/// Dictionary, group and pair-list sizes.
pub open spec fn adsh_count(parts: Seq<PartView>) -> int { text_count(parts, P_ADSH_OFF as int) }
pub open spec fn stmt_count(parts: Seq<PartView>) -> int { text_count(parts, P_STMT_OFF as int) }
pub open spec fn rfile_count(parts: Seq<PartView>) -> int { text_count(parts, P_RFILE_OFF as int) }
pub open spec fn tag_count(parts: Seq<PartView>) -> int { text_count(parts, P_TAG_OFF as int) }
pub open spec fn version_count(parts: Seq<PartView>) -> int { text_count(parts, P_VERSION_OFF as int) }
pub open spec fn group_count(parts: Seq<PartView>) -> int { u64s(parts, P_GROUP_STMT).len() as int }
pub open spec fn pair_count(parts: Seq<PartView>) -> int { u64s(parts, P_PAIR_TAG).len() as int }

/// `tag` and `version` of stored row `i` (bytes).
pub open spec fn tag_of(parts: Seq<PartView>, i: int) -> Seq<u8> {
    list_entry(parts, P_TAG_OFF, u64s(parts, P_PAIR_TAG)[u64s(parts, P_TV)[i] as int] as int)
}

pub open spec fn version_of(parts: Seq<PartView>, i: int) -> Seq<u8> {
    list_entry(parts, P_VERSION_OFF, u64s(parts, P_PAIR_VERSION)[u64s(parts, P_TV)[i] as int] as int)
}

/// The stmt of group `g`: NULL for key 0, else the dictionary value at key - 1.
pub open spec fn group_stmt_of(parts: Seq<PartView>, g: int) -> Val {
    let k = u64s(parts, P_GROUP_STMT)[g];
    if k == 0 { Val::Null } else { Val::Text(list_entry(parts, P_STMT_OFF, k - 1)) }
}

/// The rfile of group `g`.
pub open spec fn group_rfile_of(parts: Seq<PartView>, g: int) -> Seq<u8> {
    list_entry(parts, P_RFILE_OFF, u64s(parts, P_GROUP_RFILE)[g] as int)
}

/// `adsh` of the rows of sub-run `s` (bytes).
pub open spec fn sub_adsh_of(parts: Seq<PartView>, s: int) -> Seq<u8> {
    list_entry(parts, P_ADSH_OFF, u64s(parts, P_SUB_ADSH)[s] as int)
}

/// Every part has its type, length and order facts.
pub open spec fn pre_layout_ok(parts: Seq<PartView>) -> bool {
    let n = row_count(parts);
    let ns = sub_count(parts);
    let start = u64s(parts, P_SUB_START);
    let sub_adsh = u64s(parts, P_SUB_ADSH);
    let sub_group = u64s(parts, P_SUB_GROUP);
    let group_stmt = u64s(parts, P_GROUP_STMT);
    let group_rfile = u64s(parts, P_GROUP_RFILE);
    let tv = u64s(parts, P_TV);
    let pair_tag = u64s(parts, P_PAIR_TAG);
    let pair_version = u64s(parts, P_PAIR_VERSION);
    &&& parts.len() == PART_COUNT
    &&& parts[P_ORIG as int] is U64 && parts[P_SUB_START as int] is U64 && parts[P_SUB_ADSH as int] is U64
    &&& parts[P_SUB_GROUP as int] is U64 && parts[P_ADSH_SUBS as int] is U64
    &&& parts[P_GROUP_STMT as int] is U64 && parts[P_GROUP_RFILE as int] is U64
    &&& parts[P_TV as int] is U64 && parts[P_PAIR_TAG as int] is U64 && parts[P_PAIR_VERSION as int] is U64
    &&& parts[P_LINE as int] is I32 && parts[P_REPORT as int] is I32 && parts[P_INPTH as int] is I32
    &&& parts[P_NEGATING as int] is I32
    &&& is_permutation(u64s(parts, P_ORIG), n as nat)
    &&& runs_partition_ok(start, ns, n)
    &&& pairs_increasing(sub_adsh, sub_group)
    &&& forall|s: int| 0 <= s < ns ==> #[trigger] sub_adsh[s] < adsh_count(parts) && sub_group[s] < group_count(parts)
    &&& group_starts_ok(u64s(parts, P_ADSH_SUBS), sub_adsh, adsh_count(parts))
    &&& sorted_list_ok(parts, P_ADSH_OFF) && sorted_list_ok(parts, P_STMT_OFF) && sorted_list_ok(parts, P_RFILE_OFF)
    &&& sorted_list_ok(parts, P_TAG_OFF) && sorted_list_ok(parts, P_VERSION_OFF)
    &&& pairs_increasing(group_stmt, group_rfile)
    &&& forall|g: int| 0 <= g < group_count(parts) ==> #[trigger] group_stmt[g] <= stmt_count(parts)
        && group_rfile[g] < rfile_count(parts)
    &&& tv.len() == n
    &&& forall|i: int| 0 <= i < n ==> #[trigger] tv[i] < pair_count(parts)
    &&& pairs_increasing(pair_tag, pair_version)
    &&& forall|p: int| 0 <= p < pair_count(parts) ==> #[trigger] pair_tag[p] < tag_count(parts) && pair_version[p] < version_count(parts)
    &&& forall|s: int, i: int, j: int| #![trigger start[s], tv[i], tv[j]] 0 <= s < ns && start[s] <= i < j < start[s + 1] ==> tv[i] <= tv[j]
    &&& i32_part(parts[P_LINE as int]).len() == n
    &&& coded_col_ok(parts, P_PLABEL_CODES, P_PLABEL_VALID as int, P_PLABEL_OFF, n)
    &&& i32_part(parts[P_REPORT as int]).len() == n
    &&& i32_part(parts[P_INPTH as int]).len() == n
    &&& i32_part(parts[P_NEGATING as int]).len() == n
}

/// The relation row stored at position `i`.
pub open spec fn stored_row(parts: Seq<PartView>, rels: Seq<Seq<Row>>, i: int) -> Row {
    rels[0][u64s(parts, P_ORIG)[i] as int]
}

/// Columns of the row stored at `i` held per stored row: line, tag, version, plabel.
pub open spec fn stored_cols_ok(parts: Seq<PartView>, row: Row, i: int) -> bool {
    &&& row.len() == 10
    &&& row[2] == Val::Int(i32_part(parts[P_LINE as int])[i] as int)
    &&& row[6] == Val::Text(tag_of(parts, i))
    &&& row[7] == Val::Text(version_of(parts, i))
    &&& row[8] == coded_text_at(parts, P_PLABEL_CODES, P_PLABEL_VALID as int, P_PLABEL_OFF, i)
}

/// Columns held per sub-run: adsh, stmt and rfile of every row of sub-run `s`.
pub open spec fn sub_cols_ok(parts: Seq<PartView>, row: Row, s: int) -> bool {
    let g = u64s(parts, P_SUB_GROUP)[s] as int;
    &&& row[0] == Val::Text(sub_adsh_of(parts, s))
    &&& row[3] == group_stmt_of(parts, g)
    &&& row[5] == Val::Text(group_rfile_of(parts, g))
}

/// Columns held in canonical row order: report, inpth, negating of canonical row `j`.
pub open spec fn canon_cols_ok(parts: Seq<PartView>, row: Row, j: int) -> bool {
    &&& row[1] == Val::Int(i32_part(parts[P_REPORT as int])[j] as int)
    &&& row[4] == Val::Int(i32_part(parts[P_INPTH as int])[j] as int)
    &&& row[9] == Val::Int(i32_part(parts[P_NEGATING as int])[j] as int)
}

/// The parts hold the `pre` relation: canonical row `orig[i]` is stored at `i`.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    let n = row_count(parts);
    let start = u64s(parts, P_SUB_START);
    &&& pre_layout_ok(parts)
    &&& rels.len() == 1
    &&& rels[0].len() == n
    &&& forall|i: int| 0 <= i < n ==> #[trigger] stored_cols_ok(parts, stored_row(parts, rels, i), i)
    &&& forall|s: int, i: int| 0 <= s < sub_count(parts) && start[s] <= i < start[s + 1]
        ==> #[trigger] sub_cols_ok(parts, stored_row(parts, rels, i), s)
    &&& forall|j: int| 0 <= j < n ==> #[trigger] canon_cols_ok(parts, rels[0][j], j)
}

/// Two rows with the same column facts at the same positions are equal.
proof fn lemma_row_determined(parts: Seq<PartView>, x: Row, y: Row, i: int, s: int, j: int)
    requires
        stored_cols_ok(parts, x, i), stored_cols_ok(parts, y, i),
        sub_cols_ok(parts, x, s), sub_cols_ok(parts, y, s),
        canon_cols_ok(parts, x, j), canon_cols_ok(parts, y, j),
    ensures x == y,
{
    assert(x =~= y);
}

/// Lossless: every value of every canonical row is a function of the parts.
#[verifier::spinoff_prover]
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    let n = row_count(parts);
    let orig = u64s(parts, P_ORIG);
    let start = u64s(parts, P_SUB_START);
    let ns = sub_count(parts);
    lemma_permutation_facts(orig, n as nat);
    assert forall|j: int| 0 <= j < n implies #[trigger] a[0][j] == b[0][j] by {
        let i = position_of(orig, j);
        lemma_run_of(start, ns, n, i);
        let s = run_of(start, ns, i);
        assert(stored_row(parts, a, i) == a[0][j] && stored_row(parts, b, i) == b[0][j]);
        assert(stored_cols_ok(parts, stored_row(parts, a, i), i));
        assert(stored_cols_ok(parts, stored_row(parts, b, i), i));
        assert(sub_cols_ok(parts, stored_row(parts, a, i), s));
        assert(sub_cols_ok(parts, stored_row(parts, b, i), s));
        assert(canon_cols_ok(parts, a[0][j], j));
        assert(canon_cols_ok(parts, b[0][j], j));
        lemma_row_determined(parts, a[0][j], b[0][j], i, s, j);
    }
    assert(a[0] =~= b[0]);
    assert(a =~= b);
}

/// The stored rows, read in stored order, have the multiset of the relation (order-independent results such as
/// sums, counts and groups over the stored order equal those over the relation).
pub proof fn lemma_stored_rows_multiset(parts: Seq<PartView>, rels: Seq<Seq<Row>>)
    requires represents(parts, rels),
    ensures
        Seq::new(row_count(parts) as nat, |i: int| stored_row(parts, rels, i)).to_multiset() == rels[0].to_multiset(),
{
    let n = row_count(parts);
    common::perm::lemma_permuted_multiset(u64s(parts, P_ORIG), rels[0]);
    assert(Seq::new(n as nat, |i: int| stored_row(parts, rels, i))
        =~= Seq::new(rels[0].len(), |i: int| rels[0][u64s(parts, P_ORIG)[i] as int]));
}

/// The sub-runs of adsh code `a` are exactly `[adsh_subs[a], adsh_subs[a + 1])`.
pub proof fn lemma_adsh_subs(parts: Seq<PartView>, a: int)
    requires pre_layout_ok(parts), 0 <= a < adsh_count(parts),
    ensures
        u64s(parts, P_ADSH_SUBS)[a] <= u64s(parts, P_ADSH_SUBS)[a + 1] <= sub_count(parts),
        forall|s: int| 0 <= s < sub_count(parts) ==> (#[trigger] u64s(parts, P_SUB_ADSH)[s] == a
            <==> u64s(parts, P_ADSH_SUBS)[a] <= s < u64s(parts, P_ADSH_SUBS)[a + 1]),
{
    let g = u64s(parts, P_ADSH_SUBS);
    let k0 = u64s(parts, P_SUB_ADSH);
    assert(g[a] <= k0.len() && g[a + 1] <= k0.len());
    if g[a] > g[a + 1] {
        let r = g[a + 1] as int;
        assert(r < g[a] <==> k0[r] < a);
        assert(r < g[a + 1] <==> k0[r] < a + 1);
    }
    assert forall|s: int| 0 <= s < sub_count(parts) implies (#[trigger] k0[s] == a <==> g[a] <= s < g[a + 1]) by {
        assert(s < g[a] <==> k0[s] < a);
        assert(s < g[a + 1] <==> k0[s] < a + 1);
    }
}

/// Number of rows.
pub fn read_row_count(st: &StoredParts) -> (n: usize)
    requires pre_layout_ok(st@),
    ensures n == row_count(st@),
{
    st.part_len(P_ORIG)
}

/// Number of sub-runs.
pub fn read_sub_count(st: &StoredParts) -> (n: usize)
    requires pre_layout_ok(st@),
    ensures n == sub_count(st@),
{
    st.part_len(P_SUB_ADSH)
}

} // verus!
