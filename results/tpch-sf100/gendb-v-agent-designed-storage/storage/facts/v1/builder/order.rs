//! Stored order of storage `facts` (clustering, a locality heuristic): orders are stored stably sorted by
//! o_orderdate; lineitem rows are stored grouped by the stored position of their order (the first order row with
//! their l_orderkey; rows without one last), stably. Both maps are counting sorts accepted only when
//! `perm::check_perm` confirms a bijection (`cluster::counting_perm`); a date range or key range too wide for a
//! counting sort keeps canonical order. Nothing here is a proof obligation beyond the bijection.
use vstd::prelude::*;
use crate::gendb_source::*;
use crate::builder::iface::common::colfmt::*;
use crate::builder::common::perm::*;
use crate::builder::common::cluster::*;

verus! {

/// Widest o_orderdate range (days) sorted by counting (2^24).
pub const MAX_DATE_RANGE: i64 = 16777216;

/// Widest o_orderkey range used for the key directory of the lineitem order (2^31).
pub const MAX_KEY_RANGE: i64 = 2147483648;

/// The stored-to-canonical maps of lineitem and orders.
pub fn row_maps(src: &SourceRef) -> (r: (Vec<u64>, Vec<u64>))
    requires
        source_wf(src@),
    ensures
        r.0@.len() == table_t0(src@).len(),
        is_perm(map_view(r.0@), table_t0(src@).len() as int),
        r.1@.len() == table_t1(src@).len(),
        is_perm(map_view(r.1@), table_t1(src@).len() as int),
{
    let omap = orders_map(src.t1_f4);
    let lmap = lineitem_map(src.t0_f0, src.t1_f0, &omap);
    (lmap, omap)
}

/// Orders stably sorted by date.
fn orders_map(dates: &[i32]) -> (v: Vec<u64>)
    ensures
        v@.len() == dates@.len(),
        is_perm(map_view(v@), dates@.len() as int),
{
    let n = dates.len();
    if n == 0 {
        return identity_perm(0);
    }
    let mut dmin: i64 = dates[0] as i64;
    let mut dmax: i64 = dates[0] as i64;
    let mut i: usize = 1;
    while i < n
        invariant
            n == dates@.len(),
            1 <= i <= n,
            i32::MIN <= dmin <= dmax <= i32::MAX,
        decreases n - i,
    {
        let d = dates[i] as i64;
        if d < dmin {
            dmin = d;
        }
        if d > dmax {
            dmax = d;
        }
        i = i + 1;
    }
    if dmax - dmin >= MAX_DATE_RANGE {
        return identity_perm(n);
    }
    let nkeys = (dmax - dmin + 1) as usize;
    assert(nkeys == dmax - dmin + 1);
    let mut keys: Vec<u32> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            n == dates@.len(),
            i <= n,
            keys@.len() == i,
            0 <= dmax - dmin < MAX_DATE_RANGE,
            i32::MIN <= dmin <= dmax <= i32::MAX,
        decreases n - i,
    {
        let d = dates[i] as i64;
        let k: u32 = if dmin <= d && d <= dmax { (d - dmin) as u32 } else { 0 };
        keys.push(k);
        i = i + 1;
    }
    counting_perm(&keys, nkeys)
}

/// Lineitem rows grouped by the stored position of their order (`omap`: stored -> canonical orders row).
fn lineitem_map(lkeys: &[i64], okeys: &[i64], omap: &Vec<u64>) -> (v: Vec<u64>)
    requires
        omap@.len() == okeys@.len(),
        is_perm(map_view(omap@), okeys@.len() as int),
    ensures
        v@.len() == lkeys@.len(),
        is_perm(map_view(v@), lkeys@.len() as int),
{
    let n = lkeys.len();
    let no = okeys.len();
    if no == 0 || no >= (u32::MAX - 1) as usize {
        return identity_perm(n);
    }
    let mut kmin: i64 = okeys[0];
    let mut kmax: i64 = okeys[0];
    let mut i: usize = 1;
    while i < no
        invariant
            no == okeys@.len(),
            1 <= i <= no,
            kmin <= kmax,
        decreases no - i,
    {
        let k = okeys[i];
        if k < kmin {
            kmin = k;
        }
        if k > kmax {
            kmax = k;
        }
        i = i + 1;
    }
    if kmax as i128 - kmin as i128 >= MAX_KEY_RANGE as i128 {
        return identity_perm(n);
    }
    // Key directory: stored position of the first order row with each key, or u32::MAX.
    let range = (kmax - kmin + 1) as usize;
    assert(range == kmax - kmin + 1);
    let mut dir: Vec<u32> = vec![u32::MAX; range];
    let mut j: usize = 0;
    while j < no
        invariant
            no == okeys@.len(),
            no == omap@.len(),
            no < u32::MAX - 1,
            j <= no,
            dir@.len() == range,
            range == kmax - kmin + 1,
            kmin <= kmax,
            kmax - kmin < MAX_KEY_RANGE,
        decreases no - j,
    {
        let cu = omap[j];
        if cu < no as u64 {
            let c = cu as usize;
            let k = okeys[c];
            if kmin <= k && k <= kmax {
                let slot = (k - kmin) as usize;
                if dir[slot] == u32::MAX {
                    dir[slot] = j as u32;
                }
            }
        }
        j = j + 1;
    }
    // Sort key of each lineitem row: its order's stored position, `no` for rows without an order.
    let mut keys: Vec<u32> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            n == lkeys@.len(),
            no < u32::MAX - 1,
            i <= n,
            keys@.len() == i,
            dir@.len() == range,
            range == kmax - kmin + 1,
            kmin <= kmax,
            kmax - kmin < MAX_KEY_RANGE,
        decreases n - i,
    {
        let k = lkeys[i];
        let mut key: u32 = no as u32;
        if kmin <= k && k <= kmax {
            let p = dir[(k - kmin) as usize];
            if p != u32::MAX {
                key = p;
            }
        }
        keys.push(key);
        i = i + 1;
    }
    counting_perm(&keys, no + 1)
}

} // verus!
