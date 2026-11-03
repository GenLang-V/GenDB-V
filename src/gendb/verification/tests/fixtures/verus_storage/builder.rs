// Framework test fixture (hand-written framework test input, not an author output): the
// builder of storage `sensor_days` (see `stores/sensor_days/interface`). The delivered columns are
// t0_f0 = id, t0_f1 = reading, t0_f2 = day of sensor, in canonical row order; the builder copies them and computes the
// per-block minimum and maximum day.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_source::*;
use crate::gendb_entry::layout::{owned_part_view, owned_parts_view, PartView};
use crate::gendb_entry::parallel::Dispatch;
use crate::gendb_entry::runtime::QueryError;
use crate::stores::sensor_days::interface::*;

verus! {

fn copy<T: Copy>(s: &[T]) -> (v: Vec<T>)
    ensures v@ == s@,
{
    let mut v = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant i <= s.len(), v@ == s@.subrange(0, i as int),
        decreases s.len() - i,
    {
        v.push(s[i]);
        i = i + 1;
    }
    assert(v@ =~= s@);
    v
}

/// Per block of `BLOCK` rows: the smallest and the largest day.
fn zone_map(days: &[i32]) -> (r: (Vec<i32>, Vec<i32>))
    ensures
        r.0@.len() == block_count(days@.len() as int),
        r.1@.len() == block_count(days@.len() as int),
        forall|i: int| 0 <= i < days@.len() ==> r.0@[i / (BLOCK as int)] <= #[trigger] days@[i] <= r.1@[i / (BLOCK as int)],
{
    let n = days.len();
    let mut mins: Vec<i32> = Vec::new();
    let mut maxs: Vec<i32> = Vec::new();
    let mut start: usize = 0;
    while start < n
        invariant
            start <= n,
            n == days@.len(),
            start == n || start == mins@.len() * BLOCK,
            mins@.len() == block_count(start as int),
            maxs@.len() == mins@.len(),
            forall|i: int| 0 <= i < start ==> mins@[i / (BLOCK as int)] <= #[trigger] days@[i] <= maxs@[i / (BLOCK as int)],
        decreases n - start,
    {
        let end = if n - start > BLOCK { start + BLOCK } else { n };
        let mut lo = days[start];
        let mut hi = days[start];
        let mut i = start + 1;
        while i < end
            invariant
                start < i <= end,
                end <= n,
                n == days@.len(),
                forall|j: int| start <= j < i ==> lo <= #[trigger] days@[j] <= hi,
            decreases end - i,
        {
            if days[i] < lo {
                lo = days[i];
            }
            if days[i] > hi {
                hi = days[i];
            }
            i = i + 1;
        }
        let ghost block = mins@.len() as int;
        mins.push(lo);
        maxs.push(hi);
        proof {
            assert forall|j: int| start <= j < end implies #[trigger] (j / (BLOCK as int)) == block by {}
        }
        start = end;
    }
    (mins, maxs)
}

pub fn build(src: &SourceRef, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires source_wf(src@), in_domain(tables(src@)),
    ensures r matches Ok(p) && represents(owned_parts_view(p@), tables(src@)),
{
    let (mins, maxs) = zone_map(src.t0_f2);
    let parts = vec![
        OwnedPart::I32(mins),
        OwnedPart::I32(maxs),
        OwnedPart::I32(copy(src.t0_f0)),
        OwnedPart::I128(copy(src.t0_f1)),
        OwnedPart::I32(copy(src.t0_f2)),
    ];
    proof {
        let pv = owned_parts_view(parts@);
        let v = src@;
        let t = table_t0(v);
        assert(pv.len() == 5);
        assert(pv[0] == owned_part_view(parts@[0]) && pv[1] == owned_part_view(parts@[1]) && pv[2] == owned_part_view(parts@[2]));
        assert(pv[3] == owned_part_view(parts@[3]) && pv[4] == owned_part_view(parts@[4]));
        assert(ids(pv) == v.t0_f0 && readings(pv) == v.t0_f1 && days(pv) == v.t0_f2);
        assert(tables(v)[0] == t);
        assert forall|i: int| 0 <= i < t.len() implies #[trigger] t[i] == stored_row(pv, i) by {}
    }
    Ok(parts)
}

} // verus!
