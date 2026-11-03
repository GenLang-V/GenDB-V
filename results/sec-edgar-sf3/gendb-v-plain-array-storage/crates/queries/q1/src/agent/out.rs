//! The answer from the groups (`final_ok`): one output row per group (key, COUNT(*), COUNT(DISTINCT adsh),
//! AVG(line)), sorted by COUNT(*) descending, and its proof against `ordered_ok`. A group outside the domain of its
//! aggregates gives the statement's SQL error (a count beyond int8) or `Capacity` (an AVG division outside the
//! executable domain), with the proof that this is the statement's outcome.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::order::*;
use crate::spec::limits::*;
use crate::spec::fns::div::*;
use crate::exec::value::*;
use crate::exec::ast::*;
use crate::bridge::order::*;
use crate::link::query::{gkeys, avg_of, lemma_nodup_same_multiset, lemma_map_multiset, lemma_slice_all};
use crate::query::query_spec;
use crate::agent::cols::*;
use crate::agent::spec::*;
use crate::agent::kernel::gkey;
use crate::agent::merge::Groups;
use crate::agent::serial::final_ok;
use crate::agent::sql::*;

verus! {

/// The bytes `b[lo..hi]` as a text value.
fn text_val(b: &[u8], blen: usize, lo: usize, hi: usize) -> (v: EVal)
    requires lo <= hi <= blen, blen == b@.len(),
    ensures v@ == Val::Text(b@.subrange(lo as int, hi as int)),
{
    let mut out: Vec<u8> = Vec::with_capacity(hi - lo);
    let mut k = lo;
    while k < hi
        invariant lo <= k <= hi, hi <= blen, blen == b@.len(), out@ == b@.subrange(lo as int, k as int),
        decreases hi - k,
    {
        out.push(b[k]);
        k = k + 1;
        proof { assert(out@ =~= b@.subrange(lo as int, k as int)); }
    }
    EVal::Text(out)
}

/// The keys of the groups, in table order of the groups.
pub open spec fn group_keys(t: Seq<Row>, rep: Seq<usize>) -> Seq<Row> {
    Seq::new(rep.len(), |g: int| gkey(t, rep, g))
}

/// The output rows of the groups.
pub fn build_rows(c: &Cols, Ghost(t): Ghost<Seq<Row>>, gs: &Groups) -> (r: Result<Vec<Vec<EVal>>, usize>)
    requires
        cols_wf(*c), corr(*c, t), final_ok(t, c.n as int, c.n as int, *gs),
        forall|g: int| 0 <= g < gs.rep@.len() ==> #[trigger] gs.cnt@[g] <= int8_max(),
    ensures
        r matches Ok(rows) ==> rows@.len() == gs.rep@.len()
            && forall|g: int| 0 <= g < rows@.len() ==> #[trigger] view_row(rows@[g]@) == full_row(t, gkey(t, gs.rep@, g))
                && group_fits(t, gkey(t, gs.rep@, g)),
        r matches Err(g) ==> g < gs.rep@.len()
            && !num_div_fits(sum_r(t, gkey(t, gs.rep@, g as int), 0, c.n as int), 0,
                cnt_r(t, gkey(t, gs.rep@, g as int), 0, c.n as int) as int, 0),
{
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let mut g: usize = 0;
    while g < gs.rep.len()
        invariant
            cols_wf(*c), corr(*c, t), final_ok(t, c.n as int, c.n as int, *gs),
            forall|g2: int| 0 <= g2 < gs.rep@.len() ==> #[trigger] gs.cnt@[g2] <= int8_max(),
            g <= gs.rep@.len(), rows@.len() == g,
            forall|g2: int| 0 <= g2 < g ==> #[trigger] view_row(rows@[g2]@) == full_row(t, gkey(t, gs.rep@, g2))
                && group_fits(t, gkey(t, gs.rep@, g2)),
        decreases gs.rep@.len() - g,
    {
        let row = gs.rep[g];
        let ghost k = gkey(t, gs.rep@, g as int);
        proof {
            assert(row < c.n && qual(t[row as int]));
            lemma_key_eq(*c, t, row as int, row as int);
            assert(0 <= c.stmt_off@[row as int] <= c.stmt_off@[row + 1] <= c.stmt@.len());
            assert(0 <= c.rfile_off@[row as int] <= c.rfile_off@[row + 1] <= c.rfile@.len());
            assert(gs.cnt@[g as int] == cnt_r(t, k, 0, c.n as int));
            assert(gs.sum@[g as int] == sum_r(t, k, 0, c.n as int));
            assert(gs.dcnt@[g as int] == aset_r(t, k, 0, c.n as int).len());
            lemma_aset_finite(t, k, 0, c.n as int);
        }
        let avg = match crate::link::query::exec_avg_finalize(gs.sum[g], 0, gs.cnt[g]) {
            Ok(v) => v,
            Err(_) => return Err(g),
        };
        let mut out: Vec<EVal> = Vec::new();
        out.push(text_val(c.stmt, c.stmt_len, c.stmt_off[row] as usize, c.stmt_off[row + 1] as usize));
        out.push(text_val(c.rfile, c.rfile_len, c.rfile_off[row] as usize, c.rfile_off[row + 1] as usize));
        out.push(EVal::Int(gs.cnt[g] as i64));
        out.push(EVal::Int(gs.dcnt[g] as i64));
        out.push(avg);
        proof {
            assert(view_row(out@) =~= full_row(t, k));
        }
        rows.push(out);
        g = g + 1;
    }
    Ok(rows)
}

/// The ORDER BY key, COUNT(*) descending.
pub open spec fn okeys() -> Seq<OrderKey> {
    seq![OrderKey { col: 2, desc: true, nulls_first: true }]
}

/// Rows sorted (by `sort_rows`) from the full rows of the groups are an allowed output for every database whose
/// table is `t`.
pub proof fn lemma_rows_ok(c: Cols, db: Database, t: Seq<Row>, gs: Groups, rows: Seq<Row>)
    requires
        cols_wf(c), corr(c, t), 3 < db.tables.len(), db.tables[3] == t,
        final_ok(t, c.n as int, c.n as int, gs),
        rows.len() == gs.rep@.len(),
        forall|g: int| 0 <= g < rows.len() ==> #[trigger] rows[g] == full_row(t, gkey(t, gs.rep@, g))
            && group_fits(t, gkey(t, gs.rep@, g)),
    ensures
        ordered_ok(db, query_spec(), Ok::<Relation, SqlError>(sort_rows(okeys(), rows))),
{
    let n = c.n as int;
    let rep = gs.rep@;
    let mk = group_keys(t, rep);
    let ds = gkeys(gq(), t);
    lemma_keys_typed(c, t);
    lemma_groups_keys(t);
    // The groups' keys are the toolkit's group keys.
    assert(mk.no_duplicates()) by {
        assert forall|a: int, b: int| 0 <= a < b < mk.len() implies mk[a] != mk[b] by {
            assert(gkey(t, rep, a) != gkey(t, rep, b));
        }
    }
    assert forall|k: Row| mk.contains(k) <==> ds.contains(k) by {
        if mk.contains(k) {
            let g = choose|g: int| 0 <= g < mk.len() && mk[g] == k;
            assert(cnt_r(t, gkey(t, rep, g), 0, n) > 0) by {
                let r = rep[g] as int;
                assert(hit(t[r], k));
                lemma_cnt_pos(t, k, r, n);
            }
        }
        if ds.contains(k) {
            assert(cnt_r(t, k, 0, n) > 0);
            lemma_cnt_witness(t, k, 0, n);
            let j = choose|j: int| 0 <= j < n && #[trigger] hit(t[j], k);
            let g = choose|g: int| 0 <= g < rep.len() && key_of(t[j]) == gkey(t, rep, g);
            assert(mk[g] == k);
        }
    }
    // Every group of the toolkit fits (it is one of ours).
    assert forall|k: Row| #[trigger] ds.contains(k) implies group_fits(t, k) by {
        assert(mk.contains(k));
        let g = choose|g: int| 0 <= g < mk.len() && mk[g] == k;
        assert(rows[g] == full_row(t, gkey(t, rep, g)));
        assert(group_fits(t, gkey(t, rep, g)));
    }
    lemma_denote(c, db, t);
    let f = |k: Row| full_row(t, k);
    lemma_nodup_same_multiset(mk, ds);
    lemma_map_multiset(mk, ds, f);
    assert(rows =~= mk.map_values(f));
    // Sorting keeps the bag and sorts by COUNT(*) (an integer in every row).
    let fams = seq![1int];
    assert(all_keys_ok(okeys(), fams, rows)) by {
        assert forall|i: int| 0 <= i < rows.len() implies keys_ok(okeys(), fams, #[trigger] rows[i]) by {
            assert(rows[i][2] is Int);
            assert forall|q: int| 0 <= q < okeys().len() implies #[trigger] key_ok(okeys()[q], fams[q], rows[i]) by {}
        }
    }
    lemma_sort_rows(okeys(), fams, rows);
    let p = sort_rows(okeys(), rows);
    lemma_query_shape();
    lemma_slice_all(p);
    assert(sorted_by(query_spec().keys, p));
}

/// A row of group `k` makes its count positive.
proof fn lemma_cnt_pos(t: Seq<Row>, k: Row, r: int, n: int)
    requires 0 <= r < n, hit(t[r], k),
    ensures cnt_r(t, k, 0, n) > 0,
    decreases n,
{
    if r < n - 1 {
        lemma_cnt_pos(t, k, r, n - 1);
    }
}

/// The toolkit's group keys and ours are the same keys.
pub proof fn lemma_same_groups(c: Cols, t: Seq<Row>, gs: Groups)
    requires cols_wf(c), corr(c, t), final_ok(t, c.n as int, c.n as int, gs),
    ensures
        forall|k: Row| #[trigger] gkeys(gq(), t).contains(k) ==> exists|g: int| 0 <= g < gs.rep@.len() && gkey(t, gs.rep@, g) == k,
        forall|g: int| 0 <= g < gs.rep@.len() ==> gkeys(gq(), t).contains(#[trigger] gkey(t, gs.rep@, g)),
{
    let n = c.n as int;
    let rep = gs.rep@;
    lemma_keys_typed(c, t);
    lemma_groups_keys(t);
    assert forall|k: Row| #[trigger] gkeys(gq(), t).contains(k) implies exists|g: int| 0 <= g < rep.len() && gkey(t, rep, g) == k by {
        lemma_cnt_witness(t, k, 0, n);
        let j = choose|j: int| 0 <= j < n && #[trigger] hit(t[j], k);
        let g = choose|g: int| 0 <= g < rep.len() && key_of(t[j]) == gkey(t, rep, g);
    }
    assert forall|g: int| 0 <= g < rep.len() implies gkeys(gq(), t).contains(#[trigger] gkey(t, rep, g)) by {
        let r = rep[g] as int;
        lemma_cnt_pos(t, gkey(t, rep, g), r, n);
    }
}

} // verus!
