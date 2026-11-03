//! Build-time check of the co-clustering of lineitem with orders (`interface::cluster::clustered`). Over the stored
//! key sequences (`okst`: o_orderkey of each stored orders row, `lkst`: l_orderkey of each stored lineitem row) it
//! builds a directory key -> first stored orders position (`dir_ok`), then checks that the position of each
//! lineitem row's order never decreases. The flag it returns is the only thing stored.
use vstd::prelude::*;
use crate::spec::value::{Row, Val};
use crate::builder::iface::cluster::*;

verus! {

/// The first index at or after `i` holding `x`, or `ok.len()`.
pub open spec fn ipos_from(ok: Seq<int>, x: int, i: int) -> int
    decreases ok.len() - i,
{
    if i < 0 || i >= ok.len() {
        ok.len() as int
    } else if ok[i] == x {
        i
    } else {
        ipos_from(ok, x, i + 1)
    }
}

/// The first index holding `x`, or `ok.len()`.
pub open spec fn ipos(ok: Seq<int>, x: int) -> int {
    ipos_from(ok, x, 0)
}

proof fn lemma_ipos_from(ok: Seq<int>, x: int, i: int, p: int)
    requires
        0 <= i <= p <= ok.len(),
        p < ok.len() ==> ok[p] == x,
        forall|q: int| i <= q < p ==> #[trigger] ok[q] != x,
    ensures
        ipos_from(ok, x, i) == p,
    decreases p - i,
{
    if i < p {
        lemma_ipos_from(ok, x, i + 1, p);
    }
}

/// `ipos` is `p` when `p` is the first index holding `x` (or `ok.len()` with no index holding it).
pub proof fn lemma_ipos(ok: Seq<int>, x: int, p: int)
    requires
        0 <= p <= ok.len(),
        p < ok.len() ==> ok[p] == x,
        forall|q: int| 0 <= q < p ==> #[trigger] ok[q] != x,
    ensures
        ipos(ok, x) == p,
{
    lemma_ipos_from(ok, x, 0, p);
}

/// o_orderkey of each stored orders row.
pub open spec fn okst(okeys: Seq<i64>, omap: Seq<u64>) -> Seq<int> {
    Seq::new(omap.len(), |i: int| okeys[omap[i] as int] as int)
}

/// l_orderkey of each stored lineitem row.
pub open spec fn lkst(lkeys: Seq<i64>, lmap: Seq<u64>) -> Seq<int> {
    Seq::new(lmap.len(), |j: int| lkeys[lmap[j] as int] as int)
}

/// The positions of the lineitem rows' orders never decrease.
pub open spec fn mono_step(ok: Seq<int>, lk: Seq<int>, j: int) -> bool {
    ipos(ok, lk[j]) <= ipos(ok, lk[j + 1])
}

/// Directory slot `s` (key `kmin + s`) after scanning the first `i` stored orders rows: `u32::MAX` while no row has
/// the key, else the first row that has it.
pub open spec fn dir_ok(dir: Seq<u32>, ok: Seq<int>, kmin: int, s: int, i: int) -> bool {
    &&& dir[s] == u32::MAX ==> forall|q: int| 0 <= q < i ==> #[trigger] ok[q] != kmin + s
    &&& dir[s] != u32::MAX ==> {
        &&& (dir[s] as int) < i
        &&& ok[dir[s] as int] == kmin + s
        &&& forall|q: int| 0 <= q < dir[s] ==> #[trigger] ok[q] != kmin + s
    }
}

/// Widest key range for which a directory is built (2^31).
pub const MAX_RANGE: i64 = 2147483648;

/// `true` only when the stored lineitem rows (keys `lkeys` at `lmap`) are clustered by the stored orders rows (keys
/// `okeys` at `omap`).
pub fn cluster_flag(lkeys: &[i64], lmap: &Vec<u64>, okeys: &[i64], omap: &Vec<u64>) -> (b: bool)
    requires
        forall|j: int| 0 <= j < lmap@.len() ==> #[trigger] lmap@[j] < lkeys@.len(),
        forall|i: int| 0 <= i < omap@.len() ==> #[trigger] omap@[i] < okeys@.len(),
    ensures
        b ==> forall|j: int| 0 <= j < lmap@.len() - 1 ==> #[trigger] mono_step(okst(okeys@, omap@), lkst(lkeys@, lmap@), j),
{
    let ghost ok = okst(okeys@, omap@);
    let ghost lk = lkst(lkeys@, lmap@);
    let no = omap.len();
    let nl = lmap.len();
    if no == 0 || no >= (u32::MAX - 1) as usize {
        if nl == 0 {
            return true;
        }
        return false;
    }
    let mut kmin: i64 = okeys[omap[0] as usize];
    let mut kmax: i64 = kmin;
    let mut i: usize = 0;
    while i < no
        invariant
            no == omap@.len(),
            ok == okst(okeys@, omap@),
            forall|q: int| 0 <= q < omap@.len() ==> #[trigger] omap@[q] < okeys@.len(),
            i <= no,
            kmin <= kmax,
            forall|q: int| 0 <= q < i ==> kmin <= #[trigger] ok[q] <= kmax,
        decreases no - i,
    {
        let k = okeys[omap[i] as usize];
        if k < kmin {
            kmin = k;
        }
        if k > kmax {
            kmax = k;
        }
        i = i + 1;
    }
    if kmax as i128 - kmin as i128 >= MAX_RANGE as i128 {
        return false;
    }
    let range = (kmax - kmin + 1) as usize;
    assert(range == kmax - kmin + 1);
    let mut dir: Vec<u32> = vec![u32::MAX; range];
    proof {
        assert forall|s: int| 0 <= s < range implies #[trigger] dir_ok(dir@, ok, kmin as int, s, 0) by {
            assert(vstd::pervasive::cloned(u32::MAX, dir@[s]));
        }
    }
    let mut i: usize = 0;
    while i < no
        invariant
            no == omap@.len(),
            no < u32::MAX - 1,
            ok == okst(okeys@, omap@),
            forall|q: int| 0 <= q < omap@.len() ==> #[trigger] omap@[q] < okeys@.len(),
            i <= no,
            kmax - kmin < MAX_RANGE,
            range == kmax - kmin + 1,
            dir@.len() == range,
            forall|q: int| 0 <= q < no ==> kmin <= #[trigger] ok[q] <= kmax,
            forall|s: int| 0 <= s < range ==> #[trigger] dir_ok(dir@, ok, kmin as int, s, i as int),
        decreases no - i,
    {
        let k = okeys[omap[i] as usize];
        assert(k == ok[i as int]);
        let slot = (k - kmin) as usize;
        let ghost before = dir@;
        if dir[slot] == u32::MAX {
            dir[slot] = i as u32;
        }
        proof {
            assert forall|s: int| 0 <= s < range implies #[trigger] dir_ok(dir@, ok, kmin as int, s, i + 1) by {
                assert(dir_ok(before, ok, kmin as int, s, i as int));
                if s != slot {
                    assert(dir@[s] == before[s]);
                    assert(ok[i as int] != kmin + s);
                }
            }
        }
        i = i + 1;
    }
    // Scan the stored lineitem rows: the position of each row's order must not decrease.
    let mut prev: usize = 0;
    let mut j: usize = 0;
    while j < nl
        invariant
            no == omap@.len(),
            nl == lmap@.len(),
            no < u32::MAX - 1,
            ok == okst(okeys@, omap@),
            lk == lkst(lkeys@, lmap@),
            forall|q: int| 0 <= q < lmap@.len() ==> #[trigger] lmap@[q] < lkeys@.len(),
            j <= nl,
            kmax - kmin < MAX_RANGE,
            range == kmax - kmin + 1,
            dir@.len() == range,
            forall|q: int| 0 <= q < no ==> kmin <= #[trigger] ok[q] <= kmax,
            forall|s: int| 0 <= s < range ==> #[trigger] dir_ok(dir@, ok, kmin as int, s, no as int),
            j > 0 ==> prev == ipos(ok, lk[j - 1]),
            forall|q: int| 0 <= q < j - 1 ==> #[trigger] mono_step(ok, lk, q),
        decreases nl - j,
    {
        let x = lkeys[lmap[j] as usize];
        assert(x == lk[j as int]);
        let mut p: usize = no;
        if kmin <= x && x <= kmax {
            let d = dir[(x - kmin) as usize];
            if d != u32::MAX {
                p = d as usize;
            }
        }
        proof {
            if kmin <= x && x <= kmax {
                let s = x - kmin;
                assert(dir_ok(dir@, ok, kmin as int, s as int, no as int));
                lemma_ipos(ok, x as int, p as int);
            } else {
                assert forall|q: int| 0 <= q < no implies #[trigger] ok[q] != x by {}
                lemma_ipos(ok, x as int, no as int);
            }
        }
        if j > 0 && p < prev {
            return false;
        }
        prev = p;
        j = j + 1;
    }
    true
}

proof fn lemma_first_key_ipos(orows: Seq<Row>, ok: Seq<int>, x: int, i: int)
    requires
        orows.len() == ok.len(),
        forall|q: int| 0 <= q < ok.len() ==> #[trigger] orows[q][0] == Val::Int(ok[q]),
    ensures
        first_key_from(orows, Val::Int(x), i) == ipos_from(ok, x, i),
    decreases ok.len() - i,
{
    if 0 <= i < ok.len() {
        assert(orows[i][0] == Val::Int(ok[i]));
        if ok[i] != x {
            lemma_first_key_ipos(orows, ok, x, i + 1);
        }
    }
}

/// The checked monotonicity over key sequences is the clustering of the stored rows that carry those keys.
pub proof fn lemma_cluster_rows(lrows: Seq<Row>, orows: Seq<Row>, lk: Seq<int>, ok: Seq<int>)
    requires
        lrows.len() == lk.len(),
        orows.len() == ok.len(),
        forall|j: int| 0 <= j < lk.len() ==> #[trigger] lrows[j][0] == Val::Int(lk[j]),
        forall|q: int| 0 <= q < ok.len() ==> #[trigger] orows[q][0] == Val::Int(ok[q]),
        forall|j: int| 0 <= j < lk.len() - 1 ==> #[trigger] mono_step(ok, lk, j),
    ensures
        clustered(lrows, orows),
{
    assert forall|j: int| 0 <= j < lrows.len() - 1 implies #[trigger] cluster_step(lrows, orows, j) by {
        assert(mono_step(ok, lk, j));
        assert(lrows[j][0] == Val::Int(lk[j]));
        assert(lrows[j + 1][0] == Val::Int(lk[j + 1]));
        lemma_first_key_ipos(orows, ok, lk[j], 0);
        lemma_first_key_ipos(orows, ok, lk[j + 1], 0);
    }
}

} // verus!
