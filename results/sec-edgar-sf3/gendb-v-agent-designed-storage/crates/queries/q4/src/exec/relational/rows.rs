//! Row and row-sequence copies and concatenations with view postconditions: the building blocks of the
//! relational operators (environments `ctx ++ row`, joined rows `left ++ right`, NULL padding).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::exec::value::*;
use crate::exec::domain::*;
use crate::exec::relational::schema::*;

verus! {

// ------------------------------------------------------------------ one row

pub fn clone_row(r: &ERow) -> (out: ERow)
    ensures view_row(out@) == view_row(r@),
{
    let mut out: ERow = Vec::new();
    let mut i: usize = 0;
    while i < r.len()
        invariant
            i <= r.len(),
            view_row(out@) == view_row(r@.take(i as int)),
        decreases r.len() - i,
    {
        let ghost prev = view_row(out@);
        let v = clone_val(&r[i]);
        out.push(v);
        proof {
            assert(view_row(out@) =~= prev.push(r@[i as int]@));
            assert(view_row(r@.take(i as int + 1)) =~= view_row(r@.take(i as int)).push(r@[i as int]@));
        }
        i = i + 1;
    }
    proof {
        assert(r@.take(r.len() as int) =~= r@);
    }
    out
}

/// `a ++ b` (environments `ctx ++ row`, joined rows `left ++ right`).
pub fn concat_rows(a: &ERow, b: &ERow) -> (out: ERow)
    ensures view_row(out@) == view_row(a@) + view_row(b@),
{
    let mut out = clone_row(a);
    let mut i: usize = 0;
    while i < b.len()
        invariant
            i <= b.len(),
            view_row(out@) == view_row(a@) + view_row(b@.take(i as int)),
        decreases b.len() - i,
    {
        let ghost prev = view_row(out@);
        let v = clone_val(&b[i]);
        out.push(v);
        proof {
            assert(view_row(out@) =~= prev.push(b@[i as int]@));
            assert(view_row(b@.take(i as int + 1)) =~= view_row(b@.take(i as int)).push(b@[i as int]@));
            assert(view_row(out@) =~= view_row(a@) + view_row(b@.take(i as int + 1)));
        }
        i = i + 1;
    }
    proof {
        assert(b@.take(b.len() as int) =~= b@);
    }
    out
}

pub proof fn lemma_row_ts_ok_concat(a: Row, b: Row)
    requires row_ts_ok(a), row_ts_ok(b),
    ensures row_ts_ok(a + b),
{
    assert forall|i: int| 0 <= i < (a + b).len() implies val_ts_ok(#[trigger] (a + b)[i]) by {
        if i < a.len() { assert((a + b)[i] == a[i]); } else { assert((a + b)[i] == b[i - a.len()]); }
    }
}

/// `n` NULLs.
pub fn null_row_exec(n: usize) -> (out: ERow)
    ensures
        view_row(out@) == crate::spec::relation::null_row(n as nat),
        row_ts_ok(view_row(out@)),
{
    let mut out: ERow = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            view_row(out@) == crate::spec::relation::null_row(i as nat),
        decreases n - i,
    {
        let ghost prev = view_row(out@);
        out.push(EVal::Null);
        proof {
            assert(view_row(out@) =~= prev.push(Val::Null));
            assert(view_row(out@) =~= crate::spec::relation::null_row((i + 1) as nat));
        }
        i = i + 1;
    }
    out
}

// ------------------------------------------------------------------ row sequences

pub fn clone_rows(rows: &Vec<ERow>) -> (out: Vec<ERow>)
    ensures view_rows(out@) == view_rows(rows@),
{
    let mut out: Vec<ERow> = Vec::new();
    let mut i: usize = 0;
    while i < rows.len()
        invariant
            i <= rows.len(),
            view_rows(out@) == view_rows(rows@.take(i as int)),
        decreases rows.len() - i,
    {
        let ghost prev = view_rows(out@);
        let r = clone_row(&rows[i]);
        out.push(r);
        proof {
            assert(view_rows(out@) =~= prev.push(view_row(rows@[i as int]@)));
            assert(view_rows(rows@.take(i as int + 1)) =~= view_rows(rows@.take(i as int)).push(view_row(rows@[i as int]@)));
        }
        i = i + 1;
    }
    proof { assert(rows@.take(rows.len() as int) =~= rows@); }
    out
}

/// Moves `rows` to the end of `out`.
pub fn append_rows(out: &mut Vec<ERow>, rows: Vec<ERow>)
    ensures view_rows(final(out)@) == view_rows(old(out)@) + view_rows(rows@),
{
    let ghost a = out@;
    let ghost b = rows@;
    let mut rows = rows;
    out.append(&mut rows);
    proof { assert(view_rows(out@) =~= view_rows(a) + view_rows(b)); }
}

/// `l ++ r` for every row `r` of `rs`, in order (the rows a cross product or a join forms with one left row).
pub open spec fn pairs_with(l: Row, rs: Seq<Row>) -> Seq<Row> {
    rs.map_values(|x: Row| l + x)
}

} // verus!
