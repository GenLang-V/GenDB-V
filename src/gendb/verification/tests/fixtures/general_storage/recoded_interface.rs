//! TEST FIXTURE (general engine line; framework test only, not an author output): the interface of storage `recoded`.
//! It holds its one declared column (a numeric column of one table, chosen by table id and column ordinal in the
//! storage's declaration) as 64-bit coefficients in source row order: a narrower encoding of the flat storage's 128-bit
//! coefficients. It names no table or column: the scale is the declaration's (`super::declaration`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::StoredParts;
use crate::spec::value::{Row, Val};

verus! {

/// The scale of the declared column.
pub open spec fn scale() -> nat {
    super::declaration::stored_columns_t0()[0].ty->Numeric_scale as nat
}

/// The coefficients part.
pub open spec fn coefficients(parts: Seq<PartView>) -> Seq<i64> {
    parts[0]->I64_0
}

/// The parts represent `rels`, the one stored relation of one column: row `i` is coefficient `i` at the declared
/// scale.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& rels.len() == 1
    &&& parts.len() == 1
    &&& parts[0] is I64
    &&& coefficients(parts).len() == rels[0].len()
    &&& forall|i: int| 0 <= i < rels[0].len() ==> #[trigger] rels[0][i] == seq![Val::Num { coeff: coefficients(parts)[i] as int, scale: scale() }]
}

/// Lossless: the parts determine the relation.
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires
        represents(parts, a),
        represents(parts, b),
    ensures
        a == b,
{
    assert forall|i: int| 0 <= i < a[0].len() implies a[0][i] == b[0][i] by {
        assert(a[0][i] == seq![Val::Num { coeff: coefficients(parts)[i] as int, scale: scale() }]);
        assert(b[0][i] == seq![Val::Num { coeff: coefficients(parts)[i] as int, scale: scale() }]);
    }
    assert(a[0] =~= b[0]);
    assert(a =~= b);
}

/// The number of stored rows.
pub fn stored_rows(s: &StoredParts, Ghost(rels): Ghost<Seq<Seq<Row>>>) -> (n: usize)
    requires
        represents(s@, rels),
    ensures
        n == rels[0].len(),
{
    s.part_len(0)
}

/// The coefficients of rows `lo..hi` (one request): row `lo + j` is `r[j]` at the declared scale.
pub fn read_coefficients(s: &mut StoredParts, lo: usize, hi: usize, Ghost(rels): Ghost<Seq<Seq<Row>>>) -> (r: &'static [i64])
    requires
        represents(old(s)@, rels),
        lo <= hi <= rels[0].len(),
    ensures
        final(s)@ == old(s)@,
        r@.len() == hi - lo,
        forall|j: int| 0 <= j < hi - lo ==> #[trigger] rels[0][lo as int + j] == seq![Val::Num { coeff: r@[j] as int, scale: scale() }],
{
    let ghost parts = s@;
    let r = s.extent_i64(0, lo, hi);
    proof {
        assert forall|j: int| 0 <= j < hi - lo implies #[trigger] rels[0][lo as int + j] == seq![Val::Num { coeff: r@[j] as int, scale: scale() }] by {
            assert(r@[j] == coefficients(parts)[lo as int + j]);
        }
    }
    r
}

} // verus!
