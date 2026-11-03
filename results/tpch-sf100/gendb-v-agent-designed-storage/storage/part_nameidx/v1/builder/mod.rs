//! Builder of storage `part_nameidx`: the 50 parts of `custpart` are inherited unchanged; this builder adds the name
//! order of the part rows.
//!
//! Plan: the rows `0 .. n` are cut into one contiguous chunk per worker; each worker task sorts its chunk by p_name
//! (`nsort::msort`, bytewise); the calling thread concatenates the sorted chunks and merges them (`merge_runs`), then
//! checks that the result is a bijection of `[0, n)` (`check_perm`). With more than `u32::MAX` rows, no rows, or a
//! failed check, the part is empty (no index).
//!
//! Proof: `src::lemma_src` restates the source facts with this storage's definitions; the sort proves the order and
//! the bounds, the check the bijection; the inherited parts are the source's parts, so every restated fact carries
//! over to the storage's parts.
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::layout::{PartView, owned_parts_view};
use crate::gendb_entry::parallel::{Dispatch, fork_join, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::gendb_entry::storage::{represents, stored_relations};
use crate::spec::value::{Database, Row};
use crate::stores::part_nameidx::interface::*;
use crate::stores::part_nameidx::declaration as D;

pub mod src;
pub mod nsort;
pub mod perm;
use src::*;
use nsort::{texts_ok, sorted, bounded, seg, runs_ok, msort, merge_runs};
use perm::{check_perm, perm_view_ok};

verus! {

/// One worker's chunk: sort `ids` by name (scratch `tmp`).
pub struct SortTask {
    pub offs: &'static [u64],
    pub bytes: &'static [u8],
    pub n: usize,
    pub lo: usize,
    pub len: usize,
    pub ids: Vec<u32>,
    pub tmp: Vec<u32>,
}

impl WorkerTask for SortTask {
    type Output = Vec<u32>;

    open spec fn pre(&self) -> bool {
        &&& texts_ok(self.offs@, self.bytes@, self.n as int)
        &&& bounded(self.ids@, self.n as int)
        &&& bounded(self.tmp@, self.n as int)
        &&& self.tmp@.len() == self.ids@.len()
        &&& self.len == self.ids@.len()
    }

    open spec fn post(&self, out: Vec<u32>) -> bool {
        &&& out@.len() == self.ids@.len()
        &&& bounded(out@, self.n as int)
        &&& sorted(self.offs@, self.bytes@, out@)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.lo as u64)
    }

    fn run(self) -> (out: Vec<u32>) {
        let len = self.len;
        let mut ids = self.ids;
        let mut tmp = self.tmp;
        msort(self.offs, self.bytes, self.n, &mut ids, &mut tmp, 0, len);
        proof {
            assert(seg(ids@, 0, len as int) =~= ids@);
        }
        ids
    }
}

/// The rows `lo .. hi` in order.
fn row_range(lo: usize, hi: usize) -> (v: Vec<u32>)
    requires lo <= hi <= u32::MAX,
    ensures v@.len() == hi - lo, forall|i: int| 0 <= i < v@.len() ==> #[trigger] v@[i] == lo + i,
{
    let mut v: Vec<u32> = Vec::with_capacity(hi - lo);
    let mut r = lo;
    while r < hi
        invariant lo <= r <= hi <= u32::MAX, v@.len() == r - lo, forall|i: int| 0 <= i < v@.len() ==> #[trigger] v@[i] == lo + i,
        decreases hi - r,
    {
        v.push(r as u32);
        r = r + 1;
    }
    v
}

/// The rows `0 .. n` sorted by name: a vector of `n` elements below `n`, sorted (a permutation is not proved here).
fn sort_rows(offs: &'static [u64], bytes: &'static [u8], n: usize, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<Vec<u32>, QueryError>)
    requires
        texts_ok(offs@, bytes@, n as int),
        1 <= n <= u32::MAX,
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(v) ==> v@.len() == n && bounded(v@, n as int) && sorted(offs@, bytes@, v@),
        r matches Err(e) ==> e is WorkerFailed,
{
    hide(sorted);
    hide(bounded);
    let nt = if n < 65536 * workers { 1 } else { workers };
    let chunk = n / nt;
    let mut tasks: Vec<SortTask> = Vec::new();
    let mut t: usize = 0;
    let mut lo: usize = 0;
    while t < nt
        invariant
            1 <= nt <= MAX_WORKERS, t <= nt, tasks@.len() == t, 1 <= n <= u32::MAX,
            texts_ok(offs@, bytes@, n as int),
            lo <= n,
            t == 0 ==> lo == 0,
            t == nt ==> lo == n,
            t > 0 ==> tasks@[0].lo == 0,
            forall|i: int| 0 <= i < t ==> (#[trigger] tasks@[i]).pre() && tasks@[i].offs@ == offs@ && tasks@[i].bytes@ == bytes@
                && tasks@[i].n == n && tasks@[i].lo + tasks@[i].len == (if i + 1 < t { tasks@[i + 1].lo as int } else { lo as int }),
        decreases nt - t,
    {
        let hi = if t + 1 == nt || chunk > n - lo { n } else { lo + chunk };
        let ids = row_range(lo, hi);
        let tmp: Vec<u32> = vec![0u32; hi - lo];
        proof {
            reveal(bounded);
            assert forall|i: int| 0 <= i < ids@.len() implies #[trigger] ids@[i] < n by {}
            assert forall|i: int| 0 <= i < tmp@.len() implies #[trigger] tmp@[i] < n by {
                assert(tmp@[i] == 0);
            }
            assert(bounded(ids@, n as int));
            assert(bounded(tmp@, n as int));
        }
        let ghost old_tasks = tasks@;
        tasks.push(SortTask { offs, bytes, n, lo, len: hi - lo, ids, tmp });
        proof {
            assert forall|i: int| 0 <= i < t + 1 implies (#[trigger] tasks@[i]).pre() && tasks@[i].offs@ == offs@ && tasks@[i].bytes@ == bytes@
                && tasks@[i].n == n && tasks@[i].lo + tasks@[i].len == (if i + 1 < t + 1 { tasks@[i + 1].lo as int } else { hi as int }) by {
                if i < t {
                    assert(tasks@[i] == old_tasks[i]);
                }
            }
        }
        lo = hi;
        t = t + 1;
    }
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    // Concatenate the sorted chunks; `runs` cuts the result into them.
    let mut v: Vec<u32> = Vec::new();
    proof {
        reveal(bounded);
        assert(bounded(v@, n as int));
    }
    let mut runs: Vec<usize> = Vec::new();
    runs.push(0);
    let mut outs = outs;
    let mut rev: Vec<Vec<u32>> = Vec::new();
    while outs.len() > 0
        invariant
            outs@.len() + rev@.len() == nt,
            forall|i: int| 0 <= i < outs@.len() ==> #[trigger] tv[i].post(outs@[i]),
            forall|i: int| 0 <= i < rev@.len() ==> #[trigger] tv[nt - 1 - i].post(rev@[i]),
        decreases outs@.len(),
    {
        let o = outs.pop().unwrap();
        rev.push(o);
    }
    let mut k: usize = 0;
    while rev.len() > 0
        invariant
            rev@.len() + k == nt,
            k <= nt,
            forall|i: int| 0 <= i < rev@.len() ==> #[trigger] tv[nt - 1 - i].post(rev@[i]),
            forall|i: int| 0 <= i < nt ==> (#[trigger] tv[i]).offs@ == offs@ && tv[i].bytes@ == bytes@ && tv[i].n == n
                && tv[i].lo + tv[i].len == (if i + 1 < nt { tv[i + 1].lo as int } else { n as int })
                && tv[i].len == tv[i].ids@.len(),
            tv[0].lo == 0,
            bounded(v@, n as int),
            runs@.len() == k + 1,
            runs@[0] == 0,
            runs@[k as int] == v@.len(),
            v@.len() == (if k < nt { tv[k as int].lo as int } else { n as int }),
            forall|i: int| 0 <= i < k ==> #[trigger] runs@[i] <= runs@[i + 1],
            forall|i: int| 0 <= i < k ==> sorted(offs@, bytes@, #[trigger] seg(v@, runs@[i] as int, runs@[i + 1] as int)),
        decreases rev@.len(),
    {
        let ghost rv = rev@;
        let mut o = rev.pop().unwrap();
        proof {
            assert(o == rv[rv.len() - 1]);
            assert(tv[nt - 1 - (rv.len() - 1)].post(rv[rv.len() - 1]));
            assert(nt - 1 - (rv.len() - 1) == k);
            assert(tv[k as int].post(o));
        }
        let ghost ov = o@;
        let ghost v0 = v@;
        let ghost r0 = runs@;
        v.append(&mut o);
        runs.push(v.len());
        proof {
            lemma_concat_step(offs@, bytes@, n as int, v0, ov, v@, r0, runs@, k as int);
        }
        k = k + 1;
    }
    proof {
        assert(runs_ok(offs@, bytes@, v@, runs@));
    }
    let r = merge_runs(offs, bytes, n, v, runs);
    Ok(r)
}

/// One more sorted chunk `ov` appended to `v0` (cut by `r0`): the cut `r1` of the result.
proof fn lemma_concat_step(o: Seq<u64>, y: Seq<u8>, n: int, v0: Seq<u32>, ov: Seq<u32>, v1: Seq<u32>,
    r0: Seq<usize>, r1: Seq<usize>, k: int)
    requires
        bounded(v0, n), bounded(ov, n), sorted(o, y, ov),
        v1 == v0 + ov,
        r0.len() == k + 1, r0[k] == v0.len(),
        v1.len() <= usize::MAX,
        r1 == r0.push(v1.len() as usize),
        forall|i: int| 0 <= i < k ==> #[trigger] r0[i] <= r0[i + 1],
        forall|i: int| 0 <= i < k ==> sorted(o, y, #[trigger] seg(v0, r0[i] as int, r0[i + 1] as int)),
    ensures
        bounded(v1, n),
        r1[k + 1] == v1.len(),
        forall|i: int| 0 <= i < k + 1 ==> #[trigger] r1[i] <= r1[i + 1],
        forall|i: int| 0 <= i < k + 1 ==> sorted(o, y, #[trigger] seg(v1, r1[i] as int, r1[i + 1] as int)),
{
    assert forall|z: int| 0 <= z < v1.len() implies #[trigger] v1[z] < n by {
        if z >= v0.len() {
            assert(v1[z] == ov[z - v0.len()]);
        } else {
            assert(v1[z] == v0[z]);
        }
    }
    assert(r1[k + 1] == v1.len());
    assert(r1[k] == r0[k]);
    assert forall|i: int| 0 <= i < k + 1 implies #[trigger] r1[i] <= r1[i + 1] by {
        if i < k {
            assert(r1[i] == r0[i] && r1[i + 1] == r0[i + 1]);
        }
    }
    assert forall|i: int| 0 <= i < k + 1 implies sorted(o, y, #[trigger] seg(v1, r1[i] as int, r1[i + 1] as int)) by {
        if i < k {
            lemma_runs_le(r0, i + 1, k);
            assert(r1[i] == r0[i] && r1[i + 1] == r0[i + 1]);
            assert(seg(v1, r1[i] as int, r1[i + 1] as int) =~= seg(v0, r0[i] as int, r0[i + 1] as int));
        } else {
            assert(seg(v1, r1[i] as int, r1[i + 1] as int) =~= ov);
        }
    }
}

/// Nondecreasing bounds up to `k`.
proof fn lemma_runs_le(r: Seq<usize>, a: int, k: int)
    requires 0 <= a <= k < r.len(), forall|i: int| 0 <= i < k ==> #[trigger] r[i] <= r[i + 1],
    ensures r[a] <= r[k],
    decreases k - a,
{
    if a < k {
        lemma_runs_le(r, a, k - 1);
    }
}

/// The storage's parts: the inherited parts, then the name order.
proof fn lemma_built(sv: StoresView, v: Seq<u32>, db: Database)
    requires
        sources_bound(sv, db),
        v.len() == 0 || (v.len() == n_rows(sv.custpart) && perm_view_ok(v, v.len() as int)
            && sorted(name_offs(sv.custpart), name_bytes(sv.custpart), v)),
    ensures
        represents(storage_parts(sv, seq![PartView::U32(v)]), stored_relations(db)),
{
    let cp = sv.custpart;
    lemma_src(sv, db);
    let rel = D::stored_relations(db)[0];
    let n = rel.len() as int;
    let parts = storage_parts(sv, seq![PartView::U32(v)]);
    assert(parts.len() == NAMEIDX_PARTS);
    assert forall|k: int| 0 <= k < CUSTPART_PARTS implies #[trigger] parts[k] == cp[k] by {}
    assert(parts[NAME_PERM as int] == PartView::U32(v));
    assert(n_rows(parts) == n_rows(cp) && bsize(parts) == bsize(cp));
    assert(name_offs(parts) == name_offs(cp) && name_bytes(parts) == name_bytes(cp));
    assert forall|r: int| 0 <= r < n implies #[trigger] name_range_ok(parts, r) by {
        assert(name_range_ok(cp, r));
    }
    assert forall|r: int| 0 <= r < rel.len() implies #[trigger] rel[r] == pa_row(pkey_at(parts, r), name_at(parts, r)) by {
        assert(rel[r] == pa_row(pkey_at(cp, r), name_at(cp, r)));
    }
    assert(perm(parts) == v);
    if v.len() == n {
        let (o, y) = (name_offs(cp), name_bytes(cp));
        assert forall|i: int| 0 <= i < n - 1 implies #[trigger] name_le_at(parts, i) by {
            assert(nsort::le(o, y, v[i], v[i + 1]));
            assert(nsort::nm(o, y, v[i]) == name_at(parts, v[i] as int));
            assert(nsort::nm(o, y, v[i + 1]) == name_at(parts, v[i + 1] as int));
        }
        assert forall|r: int| 0 <= r < n implies #[trigger] listed(parts, n, r) by {
            assert(crate::builder::perm::covered_u32(v, r));
            let i = choose|i: int| 0 <= i < v.len() && v[i] == r;
            assert(perm(parts)[i] == r);
        }
    }
}

/// Every database bound to the sources.
proof fn lemma_built_all(sv: StoresView, v: Seq<u32>)
    requires
        v.len() == 0 || (v.len() == n_rows(sv.custpart) && perm_view_ok(v, v.len() as int)
            && sorted(name_offs(sv.custpart), name_bytes(sv.custpart), v)),
    ensures
        forall|db: Database| #[trigger] sources_bound(sv, db) ==> represents(storage_parts(sv, seq![PartView::U32(v)]), stored_relations(db)),
{
    assert forall|db: Database| #[trigger] sources_bound(sv, db) implies
        represents(storage_parts(sv, seq![PartView::U32(v)]), stored_relations(db)) by {
        lemma_built(sv, v, db);
    }
}

/// The p_name offsets and bytes of the source (whole parts) and the number of part rows.
fn read_names(stores: &mut Stores, Ghost(sv): Ghost<StoresView>) -> (r: (&'static [u64], &'static [u8], usize))
    requires
        old(stores)@ == sv,
        exists|db: Database| #[trigger] sources_bound(sv, db),
    ensures
        final(stores)@ == sv,
        r.0@ == name_offs(sv.custpart),
        r.1@ == name_bytes(sv.custpart),
        r.2 == n_rows(sv.custpart),
        texts_ok(r.0@, r.1@, r.2 as int),
{
    let ghost cp = sv.custpart;
    let ghost db0 = choose|db: Database| #[trigger] sources_bound(sv, db);
    proof {
        lemma_src(sv, db0);
    }
    let n = stores.custpart.part_len(PA_PARTKEY_CODES);
    let no = stores.custpart.part_len(PA_NAME_OFFS);
    let ny = stores.custpart.part_len(PA_NAME_BYTES);
    let offs = stores.custpart.extent_u64(PA_NAME_OFFS, 0, no);
    let bytes = stores.custpart.extent_u8(PA_NAME_BYTES, 0, ny);
    proof {
        assert(offs@ =~= name_offs(cp));
        assert(bytes@ =~= name_bytes(cp));
        assert forall|r: int| 0 <= r < n implies #[trigger] offs@[r] <= offs@[r + 1] && offs@[r + 1] <= bytes@.len() by {
            assert(name_range_ok(cp, r));
        }
    }
    (offs, bytes, n)
}

pub fn build(stores: &mut Stores, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        sources_ready(old(stores)@),
        1 <= workers <= MAX_WORKERS,
    ensures
        match r {
            Ok(p) => forall|db: Database| #[trigger] sources_bound(old(stores)@, db)
                ==> represents(storage_parts(old(stores)@, owned_parts_view(p@)), stored_relations(db)),
            Err(QueryError::WorkerFailed(_)) => true,
            Err(_) => false,
        },
{
    let ghost sv = stores@;
    let (offs, bytes, n) = read_names(stores, Ghost(sv));
    let v: Vec<u32> = if n == 0 || n > 0xffff_ffff {
        Vec::new()
    } else {
        match sort_rows(offs, bytes, n, workers, dispatch) {
            Ok(s) => if check_perm(&s) { s } else { Vec::new() },
            Err(e) => return Err(e),
        }
    };
    let ghost vv = v@;
    let mut out: Vec<OwnedPart> = Vec::new();
    out.push(OwnedPart::U32(v));
    proof {
        let built = owned_parts_view(out@);
        assert(built =~= seq![PartView::U32(vv)]);
        lemma_built_all(sv, vv);
    }
    Ok(out)
}

} // verus!
