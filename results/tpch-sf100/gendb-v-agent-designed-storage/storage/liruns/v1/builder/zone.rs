//! The zone map of a frame-of-reference column: the largest value of each block of `bs` rows (its base plus its
//! largest code), one I64 per block; `None` when a maximum does not fit I64.
use vstd::prelude::*;

verus! {

/// Value of stored row `j`: `qb[j / bs] + qc[j]`.
pub open spec fn fval(qc: Seq<u16>, qb: Seq<i64>, bs: int, j: int) -> int {
    qb[j / bs] as int + qc[j] as int
}

/// `z` bounds every value of its block from above.
pub open spec fn zone_built(qc: Seq<u16>, qb: Seq<i64>, bs: int, n: int, z: Seq<i64>) -> bool {
    &&& z.len() == qb.len()
    &&& forall|j: int| 0 <= j < n ==> #[trigger] fval(qc, qb, bs, j) <= z[j / bs]
}

pub fn build_zone(qc: &[u16], qb: &[i64], bs: usize, n: usize) -> (r: Option<Vec<i64>>)
    requires
        qc.len() == n,
        bs >= 1,
        qb.len() * bs >= n,
    ensures
        r matches Some(z) ==> zone_built(qc@, qb@, bs as int, n as int, z@),
{
    let nb = qb.len();
    // the largest code of each block
    let mut maxc: Vec<u16> = crate::gendb_entry::work::filled(nb, 0u16);
    let mut j: usize = 0;
    while j < n
        invariant
            qc.len() == n, bs >= 1, qb.len() * bs >= n, nb == qb.len(),
            maxc.len() == nb,
            j <= n,
            forall|t: int| 0 <= t < j ==> (#[trigger] qc@[t]) <= maxc@[t / bs as int],
        decreases n - j,
    {
        proof {
            crate::stores::liruns::interface::common::read::lemma_div_lt(j as int, bs as int, nb as int);
        }
        let g = j / bs;
        let c = qc[j];
        if c > maxc[g] {
            maxc.set(g, c);
        }
        j = j + 1;
    }
    let mut z: Vec<i64> = Vec::new();
    let mut g: usize = 0;
    while g < nb
        invariant
            nb == qb.len(), maxc.len() == nb,
            g <= nb,
            z.len() == g,
            forall|h: int| 0 <= h < g ==> (#[trigger] z@[h]) as int == qb@[h] as int + maxc@[h] as int,
        decreases nb - g,
    {
        let v: i128 = qb[g] as i128 + maxc[g] as i128;
        if v > i64::MAX as i128 {
            return None;
        }
        z.push(v as i64);
        g = g + 1;
    }
    proof {
        assert forall|t: int| 0 <= t < n implies #[trigger] fval(qc@, qb@, bs as int, t) <= z@[t / bs as int] by {
            crate::stores::liruns::interface::common::read::lemma_div_lt(t, bs as int, nb as int);
            assert(qc@[t] <= maxc@[t / bs as int]);
        }
    }
    Some(z)
}

} // verus!
