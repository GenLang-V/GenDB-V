//! The fast path's counts are the statement's counts: when the pattern is `%s1%...%sk%` (segments `ss`), every
//! comment is ASCII and the customer keys are `base, base + 1, ...`, an orders row counts for customer index `i`
//! (`kidx`) exactly when it passes `NOT LIKE` and its `o_custkey` is customer `i`'s key; so `tot` is `ccnt`, `hcnt`
//! is `hcount`, and no `LIKE` raises (`lemma_fast_facts`). The histograms of consecutive customer ranges add up
//! (`count::lemma_hcnt_add`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::gendb_entry::stores::StoresView;
use crate::link::query::text_at;
use crate::agent::common::segments::*;
use crate::agent::common::text_rows::*;
use crate::agent::tables::*;
use crate::agent::normal::*;
use crate::agent::scan::*;
use crate::agent::count::*;

verus! {

/// The fast path's run-time facts about the data.
pub open spec fn fast_ok(c: Cols, sv: StoresView, ss: Seq<Seq<u8>>, pat: Seq<u8>, base: int) -> bool {
    &&& cols_ok(c, sv)
    &&& segs_ok(ss) && seg_pattern(ss) == pat
    &&& forall|x: int| 0 <= x < c.no ==> #[trigger] ascii(val(c.offs@, c.bytes@, x))
    &&& dense_ok(c, base, 0, c.nc as int)
}

/// Orders row `j`'s `LIKE` is the byte-level match.
proof fn lemma_like_row(c: Cols, sv: StoresView, ss: Seq<Seq<u8>>, pat: Seq<u8>, base: int, j: int)
    requires fast_ok(c, sv, ss, pat, base), 0 <= j < c.no,
    ensures like_j(sv, pat, j) == Ok::<Val, SqlError>(Val::Bool(matched(c, ss, j))),
{
    assert(cmt(sv, j) == val(c.offs@, c.bytes@, j));
    lemma_like_segments(cmt(sv, j), ss);
}

/// Counting rows below `n` for customer index `i` is counting `ccnt`'s rows.
proof fn lemma_crange_ocnt(c: Cols, sv: StoresView, ss: Seq<Seq<u8>>, pat: Seq<u8>, base: int, i: int, n: int)
    requires fast_ok(c, sv, ss, pat, base), 0 <= i < c.nc, 0 <= n <= c.no,
    ensures crange(c, ss, base, i, 0, n) == ocnt(sv, pat, cck(sv)[i] as int, n),
    decreases n,
{
    if n > 0 {
        lemma_crange_ocnt(c, sv, ss, pat, base, i, n - 1);
        lemma_like_row(c, sv, ss, pat, base, n - 1);
        assert(c.cck@[i] as int == base + i);
        assert((kidx(c, ss, base, n - 1) == i) == (ock(sv)[n - 1] as int == cck(sv)[i] as int && counted(sv, pat, n - 1)));
    }
}

/// The histogram of the customer indices below `n`.
proof fn lemma_hcnt_hcount(c: Cols, sv: StoresView, ss: Seq<Seq<u8>>, pat: Seq<u8>, base: int, v: int, n: int)
    requires fast_ok(c, sv, ss, pat, base), 0 <= n <= c.nc,
    ensures hcnt(c, ss, base, v, 0, n) == hcount(sv, pat, v, n),
    decreases n,
{
    if n > 0 {
        lemma_hcnt_hcount(c, sv, ss, pat, base, v, n - 1);
        lemma_crange_ocnt(c, sv, ss, pat, base, n - 1, c.no as int);
    }
}

/// Under the fast path's facts: no `LIKE` raises, `tot` is `ccnt` and `hcnt` is `hcount`.
pub proof fn lemma_fast_facts(c: Cols, sv: StoresView, ss: Seq<Seq<u8>>, pat: Seq<u8>, base: int)
    requires fast_ok(c, sv, ss, pat, base),
    ensures
        likes_ok(sv, pat),
        forall|i: int| 0 <= i < c.nc ==> #[trigger] tot(c, ss, base, i) == ccnt(sv, pat, i),
        forall|v: int| #[trigger] hcnt(c, ss, base, v, 0, c.nc as int) == hcount(sv, pat, v, n_c(sv)),
{
    assert forall|j: int| 0 <= j < n_o(sv) implies #[trigger] like_j(sv, pat, j) is Ok by {
        lemma_like_row(c, sv, ss, pat, base, j);
    }
    assert forall|i: int| 0 <= i < c.nc implies #[trigger] tot(c, ss, base, i) == ccnt(sv, pat, i) by {
        lemma_crange_ocnt(c, sv, ss, pat, base, i, c.no as int);
    }
    assert forall|v: int| #[trigger] hcnt(c, ss, base, v, 0, c.nc as int) == hcount(sv, pat, v, n_c(sv)) by {
        lemma_hcnt_hcount(c, sv, ss, pat, base, v, c.nc as int);
    }
}

} // verus!
