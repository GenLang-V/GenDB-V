// Framework test fixture (hand-written framework test input, not an author output, not a
// TPC-H storage): the interface of storage `sensor_days`, which stores the columns id, reading and day of
// sensor(id integer, site integer, reading numeric(10,2), day date, tag varchar(8), note text) in canonical row order,
// with a zone map of `day` over blocks of BLOCK rows.
//
// Parts (all element counts in rows or blocks):
//   0 block_min_day  I32, one per block: the smallest day (Date32, days since 1970-01-01) of the block's rows;
//   1 block_max_day  I32, one per block: the largest day of the block's rows;
//   2 id             I32, one per row;
//   3 reading        I128, one per row: the numeric(10,2) coefficient at scale 2;
//   4 day            I32, one per row: Date32.
// Block b holds rows [b * BLOCK, min(n, (b + 1) * BLOCK)).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::source_check::date32_val;
use crate::gendb_entry::stored::StoredParts;

verus! {

/// Rows per block.
pub const BLOCK: usize = 2;

/// Number of blocks of `n` rows.
pub open spec fn block_count(n: int) -> int {
    (n + BLOCK - 1) / (BLOCK as int)
}

pub open spec fn shaped(parts: Seq<PartView>) -> bool {
    &&& parts.len() == 5
    &&& parts[0] is I32 && parts[1] is I32 && parts[2] is I32 && parts[3] is I128 && parts[4] is I32
}

pub open spec fn block_mins(parts: Seq<PartView>) -> Seq<i32> { parts[0]->I32_0 }
pub open spec fn block_maxs(parts: Seq<PartView>) -> Seq<i32> { parts[1]->I32_0 }
pub open spec fn ids(parts: Seq<PartView>) -> Seq<i32> { parts[2]->I32_0 }
pub open spec fn readings(parts: Seq<PartView>) -> Seq<i128> { parts[3]->I128_0 }
pub open spec fn days(parts: Seq<PartView>) -> Seq<i32> { parts[4]->I32_0 }

/// Stored row `i` as a row of the stored relation `[id, reading, day]`.
pub open spec fn stored_row(parts: Seq<PartView>, i: int) -> Row {
    seq![Val::Int(ids(parts)[i] as int), Val::Num { coeff: readings(parts)[i] as int, scale: 2 }, date32_val(days(parts)[i])]
}

/// The zone map: every row's day lies within its block's minimum and maximum.
pub open spec fn zones_hold(parts: Seq<PartView>, n: int) -> bool {
    &&& block_mins(parts).len() == block_count(n)
    &&& block_maxs(parts).len() == block_count(n)
    &&& forall|i: int| 0 <= i < n ==>
        block_mins(parts)[i / (BLOCK as int)] <= #[trigger] days(parts)[i] <= block_maxs(parts)[i / (BLOCK as int)]
}

/// The parts represent `rels`: one relation (sensor's id, reading, day), row for row, and the zone map holds.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    let n = rels[0].len() as int;
    &&& shaped(parts)
    &&& rels.len() == 1
    &&& ids(parts).len() == n && readings(parts).len() == n && days(parts).len() == n
    &&& forall|i: int| 0 <= i < n ==> #[trigger] rels[0][i] == stored_row(parts, i)
    &&& zones_hold(parts, n)
}

/// The parts determine the represented relations (the storage is lossless): both are the one relation of the parts' rows.
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires
        represents(parts, a),
        represents(parts, b),
    ensures
        a == b,
{
    assert(a[0] =~= b[0]);
    assert(a =~= b);
}

/// Blocks that may hold a row whose day (Date32) is below `bound`: every such row's block is marked. Reads only the
/// block minima (one request).
pub fn blocks_before(st: &mut StoredParts, bound: i64, Ghost(rels): Ghost<Seq<Seq<Row>>>) -> (marked: Vec<bool>)
    requires represents(old(st)@, rels),
    ensures
        final(st)@ == old(st)@,
        marked@.len() == block_count(rels[0].len() as int),
        forall|i: int| 0 <= i < rels[0].len() && (days(old(st)@)[i] as int) < bound ==> #[trigger] marked@[i / (BLOCK as int)],
{
    let blocks = st.part_len(0);
    let mins = st.extent_i32(0, 0, blocks);
    let mut marked: Vec<bool> = Vec::new();
    let mut b: usize = 0;
    while b < blocks
        invariant
            b <= blocks,
            blocks == block_mins(st@).len(),
            mins@ == block_mins(st@),
            marked@.len() == b,
            forall|k: int| 0 <= k < b ==> #[trigger] marked@[k] == ((mins@[k] as int) < bound),
        decreases blocks - b,
    {
        marked.push((mins[b] as i64) < bound);
        b = b + 1;
    }
    proof {
        let n = rels[0].len() as int;
        assert forall|i: int| 0 <= i < n && (days(st@)[i] as int) < bound implies #[trigger] marked@[i / (BLOCK as int)] by {
            assert(block_mins(st@)[i / (BLOCK as int)] <= days(st@)[i]);
            assert(0 <= i / (BLOCK as int) < block_count(n));
        }
    }
    marked
}

} // verus!
