//! Executable `spec::aggs::minmax`: one pass keeping the index of the running extremum (the value is cloned once
//! at the end). The result is an argument value, so it is a valid timestamp when the arguments are
//! (`row_ts_ok`, threaded by the caller).
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::aggs::minmax::*;
use crate::exec::value::*;
use crate::exec::scalar::*;
use crate::exec::domain::*;

verus! {

/// An error of the extremum of a prefix is the extremum's error.
proof fn lemma_extremum_err_prefix(max: bool, vs: Seq<Val>, k: int)
    requires 0 <= k <= vs.len(), extremum(max, vs.take(k)) is Err,
    ensures extremum(max, vs) == extremum(max, vs.take(k)),
    decreases vs.len() - k,
{
    if k < vs.len() {
        let p = vs.take(k + 1);
        assert(p.drop_last() =~= vs.take(k));
        assert(extremum(max, p) == extremum(max, vs.take(k)));
        lemma_extremum_err_prefix(max, vs, k + 1);
    } else {
        assert(vs.take(k) =~= vs);
    }
}

/// `spec::aggs::minmax::extremum` (`max`: MAX, otherwise MIN).
fn exec_extremum(max: bool, vs: &Vec<EVal>) -> (r: Result<EVal, SqlError>)
    requires row_ts_ok(view_row(vs@)),
    ensures view_result(r) == extremum(max, view_row(vs@)), r matches Ok(v) ==> val_ts_ok(v@),
{
    let ghost g = view_row(vs@);
    let mut best: usize = 0;
    let mut found = false;
    let mut i: usize = 0;
    while i < vs.len()
        invariant
            i <= vs.len(), g == view_row(vs@), g.len() == vs.len(),
            found ==> best < i && !(g[best as int] is Null),
            extremum(max, g.take(i as int)) == Ok::<Val, SqlError>(if found { g[best as int] } else { Val::Null }),
        decreases vs.len() - i,
    {
        let ghost acc = if found { g[best as int] } else { Val::Null };
        proof {
            let p = g.take(i as int + 1);
            assert(p.drop_last() =~= g.take(i as int));
            assert(p.last() == g[i as int]);
            assert(g[i as int] == vs@[i as int]@);
            assert(extremum(max, p) == extremum_step(max, acc, g[i as int]));
        }
        match &vs[i] {
            EVal::Null => {},
            EVal::Bool(_) => {
                proof { lemma_extremum_err_prefix(max, g, i as int + 1); }
                return Err(SqlError::TypeError);
            },
            v => {
                if !found {
                    best = i;
                    found = true;
                } else {
                    proof { assert(g[best as int] == vs@[best as int]@); }
                    match compare_exec(v, &vs[best]) {
                        Some(c) => {
                            let improves = if max { c > 0 } else { c < 0 };
                            if improves {
                                best = i;
                            }
                        },
                        None => {
                            proof { lemma_extremum_err_prefix(max, g, i as int + 1); }
                            return Err(SqlError::TypeError);
                        },
                    }
                }
            },
        }
        i = i + 1;
    }
    proof { assert(g.take(vs.len() as int) =~= g); }
    if found {
        proof { assert(g[best as int] == vs@[best as int]@); }
        Ok(clone_val(&vs[best]))
    } else {
        Ok(EVal::Null)
    }
}

/// `spec::aggs::minmax::min_value`.
pub fn exec_min(vs: &Vec<EVal>) -> (r: Result<EVal, SqlError>)
    requires row_ts_ok(view_row(vs@)),
    ensures view_result(r) == min_value(view_row(vs@)), r matches Ok(v) ==> val_ts_ok(v@),
{
    exec_extremum(false, vs)
}

/// `spec::aggs::minmax::max_value`.
pub fn exec_max(vs: &Vec<EVal>) -> (r: Result<EVal, SqlError>)
    requires row_ts_ok(view_row(vs@)),
    ensures view_result(r) == max_value(view_row(vs@)), r matches Ok(v) ==> val_ts_ok(v@),
{
    exec_extremum(true, vs)
}

/// `spec::aggs::minmax::minmax_ty`: MIN/MAX of any non-boolean type, nullable.
pub fn minmax_ty_exec(t: ColTy) -> (r: Option<ColTy>)
    ensures r == minmax_ty(t),
{
    match t.ty {
        ScalarTy::Bool => None,
        _ => Some(ColTy { ty: t.ty, nullable: true }),
    }
}

} // verus!
