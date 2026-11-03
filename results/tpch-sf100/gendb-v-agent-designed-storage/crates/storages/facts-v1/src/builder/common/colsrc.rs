//! Value sources of frame-of-reference columns and stored-to-canonical row maps. A `ValSrc` yields the integer
//! of canonical row `i` of one delivered column: a bigint as is, a numeric coefficient, a date as days since
//! 2000-01-01 (`Val::Date`), or the dictionary index of a text value. A `RowMap` names the canonical row of each
//! stored row (identity, or a vector shared by the worker tasks). Reads are `no_unwind`.
use vstd::prelude::*;
use std::sync::Arc;
use crate::link::query::{text_at, text_wf, TextCol, TextView};
use crate::gendb_entry::work::text_bytes;
use crate::builder::common::dict::*;

verus! {

/// `text_wf` behind an opaque name: the delivered text columns' offset quantifier instantiates itself
/// (`offsets[i]` yields `offsets[i + 1]`), so large functions see it only through this name and reveal it locally.
#[verifier::opaque]
pub open spec fn twf(t: TextView, n: int) -> bool {
    text_wf(t, n)
}

/// Bound of numeric(15, 2) coefficients: `|c| < 10^15`.
pub open spec fn num15_bound() -> int {
    1_000_000_000_000_000
}

/// One delivered column as integers.
pub enum ValSrc {
    /// bigint values.
    Int(&'static [i64]),
    /// numeric(15, s) coefficients.
    Num(&'static [i128]),
    /// Date32 days since 1970-01-01, read as days since 2000-01-01.
    Date(&'static [i32]),
    /// Text values, read as their dictionary index.
    Dict(TextCol, Arc<Dict>),
    /// The canonical row index itself (a stored-to-canonical row map as a column).
    Pos,
}

/// The integer of canonical row `i`.
pub open spec fn src_val(s: ValSrc, i: int) -> int {
    match s {
        ValSrc::Int(c) => c@[i] as int,
        ValSrc::Num(c) => c@[i] as int,
        ValSrc::Date(c) => c@[i] as int - 10957,
        ValSrc::Dict(t, d) => dict_index_of(*d, text_at(t@, i)),
        ValSrc::Pos => i,
    }
}

/// The source has `n` rows (numeric coefficients inside numeric(15, s), text values in the dictionary).
pub open spec fn src_wf(s: ValSrc, n: int) -> bool {
    match s {
        ValSrc::Int(c) => c@.len() == n,
        ValSrc::Num(c) => c@.len() == n && forall|i: int| 0 <= i < n ==> -num15_bound() < #[trigger] c@[i] < num15_bound(),
        ValSrc::Date(c) => c@.len() == n,
        ValSrc::Dict(t, d) => twf(t@, n) && dict_wf(*d) && forall|i: int| 0 <= i < n ==> #[trigger] dict_has(*d, text_at(t@, i)),
        ValSrc::Pos => 0 <= n <= usize::MAX,
    }
}

/// Signed sources (bigint, numeric, date) have I64 bases; dictionary indices and row positions have U64 bases.
pub open spec fn src_signed(s: ValSrc) -> bool {
    !(s is Dict) && !(s is Pos)
}

/// Every value lies in the range of its base kind (i64 for signed sources, u64 for dictionary indices).
pub open spec fn in_base_range(s: ValSrc, v: int) -> bool {
    if src_signed(s) {
        i64::MIN <= v <= i64::MAX
    } else {
        0 <= v <= u64::MAX
    }
}

/// Source values lie in the range of their base kind.
pub proof fn lemma_src_range(s: ValSrc, n: int, i: int)
    requires
        src_wf(s, n),
        0 <= i < n,
    ensures
        in_base_range(s, src_val(s, i)),
{
    if s is Dict {
        let t = s->Dict_0;
        let d = *s->Dict_1;
        assert(dict_has(d, text_at(t@, i)));
        let x = choose|x: int| 0 <= x < dict_k(d) && dict_entry(d, x) == text_at(t@, i);
        lemma_dict_index_of(d, text_at(t@, i), x);
        assert(d.offs@.len() <= usize::MAX) by {
            assert(d.offs@.len() == d.offs.len());
        }
    }
}

/// Dictionary indices are below the dictionary size.
pub proof fn lemma_dict_src_bound(s: ValSrc, n: int, i: int)
    requires
        src_wf(s, n),
        s is Dict,
        0 <= i < n,
    ensures
        0 <= src_val(s, i) < dict_k(*(s->Dict_1)),
{
    let t = s->Dict_0;
    let d = *s->Dict_1;
    assert(dict_has(d, text_at(t@, i)));
    let x = choose|x: int| 0 <= x < dict_k(d) && dict_entry(d, x) == text_at(t@, i);
    lemma_dict_index_of(d, text_at(t@, i), x);
}

/// The integer of canonical row `i`, `no_unwind`.
pub fn src_get(s: &ValSrc, n: usize, i: usize) -> (v: i128)
    requires
        src_wf(*s, n as int),
        i < n,
    ensures
        v == src_val(*s, i as int),
    no_unwind
{
    match s {
        ValSrc::Int(c) => c[i] as i128,
        ValSrc::Num(c) => c[i],
        ValSrc::Date(c) => c[i] as i128 - 10957,
        ValSrc::Dict(t, d) => {
            proof {
                reveal(twf);
            }
            assert(0 <= t.offsets@[i as int] <= t.offsets@[i + 1] <= t.bytes@.len());
            proof {
                vstd::slice::axiom_spec_len(t.bytes);
            }
            let a = text_bytes(t, i);
            let alen = (t.offsets[i + 1] - t.offsets[i]) as usize;
            let x = dict_search(d, a, alen);
            x as i128
        },
        ValSrc::Pos => i as i128,
    }
}

/// Stored row `j` -> canonical row.
pub enum RowMap {
    Identity,
    Map(Arc<Vec<u64>>),
}

/// Canonical row of stored row `j`.
pub open spec fn rm_at(m: RowMap, j: int) -> int {
    match m {
        RowMap::Identity => j,
        RowMap::Map(v) => v@[j] as int,
    }
}

/// The map covers `n` stored rows and names canonical rows below `n`.
pub open spec fn rm_wf(m: RowMap, n: int) -> bool {
    match m {
        RowMap::Identity => true,
        RowMap::Map(v) => v@.len() == n && forall|j: int| 0 <= j < n ==> #[trigger] v@[j] < n,
    }
}

/// Canonical row of stored row `j`, `no_unwind`.
pub fn rm_get(m: &RowMap, n: usize, j: usize) -> (i: usize)
    requires
        rm_wf(*m, n as int),
        j < n,
    ensures
        i == rm_at(*m, j as int),
        i < n,
    no_unwind
{
    match m {
        RowMap::Identity => j,
        RowMap::Map(v) => {
            assert(v@[j as int] < n);
            v[j] as usize
        },
    }
}

/// A clone of a value source (shares its dictionary).
pub fn src_clone(s: &ValSrc) -> (r: ValSrc)
    ensures r == *s,
{
    match s {
        ValSrc::Int(c) => ValSrc::Int(*c),
        ValSrc::Num(c) => ValSrc::Num(*c),
        ValSrc::Date(c) => ValSrc::Date(*c),
        ValSrc::Dict(t, d) => ValSrc::Dict(TextCol { offsets: t.offsets, bytes: t.bytes }, d.clone()),
        ValSrc::Pos => ValSrc::Pos,
    }
}

/// A clone of a row map (shares its vector).
pub fn rm_clone(m: &RowMap) -> (r: RowMap)
    ensures r == *m,
{
    match m {
        RowMap::Identity => RowMap::Identity,
        RowMap::Map(v) => RowMap::Map(v.clone()),
    }
}

} // verus!
