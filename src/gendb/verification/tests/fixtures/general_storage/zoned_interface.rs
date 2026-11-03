//! TEST FIXTURE (general engine line; framework test only, not an author output): the interface of storage `zoned`.
//! It keeps the parts of the flat storage of one table unchanged (`extends`), states them with the plain-columns
//! vocabulary (`plain`, GenDB's `gendb-plain-columns-v1` text copied unchanged) by the declared column types and a part
//! layout given as data, and adds one zone part: the smallest value of the first column (an integer key), so a reader
//! can skip the table when a bound excludes it. It names no table or column.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::StoredParts;
use crate::spec::value::Row;

pub mod plain;

verus! {

/// The parts kept from the flat storage (the declared columns: one key part, then two text columns of two parts).
pub const KEPT_PARTS: usize = 5;

/// The zone part, after the kept parts.
pub const ZONE: usize = 5;

/// The part of each declared column among the kept parts (data: the declared column types, in order).
pub open spec fn layout() -> Seq<int> {
    seq![0int, 1int, 3int]
}

/// The zone part holds the smallest key: one value when there are rows, none otherwise.
pub open spec fn zone_holds(zone: Seq<i64>, keys: Seq<i64>) -> bool {
    &&& keys.len() == 0 ==> zone.len() == 0
    &&& keys.len() > 0 ==> zone.len() == 1 && forall|i: int| 0 <= i < keys.len() ==> zone[0] <= #[trigger] keys[i]
}

/// The parts represent `rels`, the one stored relation: the kept parts hold it plainly, and the zone part bounds its
/// first column (an integer key, held in part 0).
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& rels.len() == 1
    &&& parts.len() == KEPT_PARTS + 1
    &&& plain::plain_columns(parts, rels[0], super::declaration::stored_columns_t0(), layout())
    &&& parts[0] is I64
    &&& parts[ZONE as int] is I64
    &&& zone_holds(parts[ZONE as int]->I64_0, parts[0]->I64_0)
}

/// Lossless: the kept parts determine the relation.
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires
        represents(parts, a),
        represents(parts, b),
    ensures
        a == b,
{
    plain::lemma_plain_columns_determine(parts, a[0], b[0], super::declaration::stored_columns_t0(), layout());
    assert(a =~= b);
}

/// The number of stored rows (the length of the key part).
pub fn stored_rows(s: &StoredParts, Ghost(rels): Ghost<Seq<Seq<Row>>>) -> (n: usize)
    requires
        represents(s@, rels),
    ensures
        n == rels[0].len(),
{
    proof {
        assert(plain::plain_column(s@, layout()[0], super::declaration::stored_columns_t0()[0].ty, rels[0], 0));
    }
    s.part_len(0)
}

/// The zone part (one request): the smallest key, when there are rows.
pub fn read_zone(s: &mut StoredParts, Ghost(rels): Ghost<Seq<Seq<Row>>>) -> (r: &'static [i64])
    requires
        represents(old(s)@, rels),
    ensures
        final(s)@ == old(s)@,
        zone_holds(r@, old(s)@[0]->I64_0),
{
    let ghost parts = s@;
    let count = s.part_len(ZONE);
    let r = s.extent_i64(ZONE, 0, count);
    proof {
        assert(r@ =~= parts[ZONE as int]->I64_0);
    }
    r
}

} // verus!
