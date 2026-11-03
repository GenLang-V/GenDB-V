//! Facts about `spec::relation::collect`, the canonical error-strict evaluation of a sequence: it succeeds exactly
//! when every element succeeds (with the elements' values in order), and otherwise yields the first error.
//! Every list and per-row evaluation of the denotation goes through `collect`, so these lemmas are how exec,
//! link and agent proofs relate a loop over elements to the denotation.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::relation::*;

verus! {

/// `collect` only depends on the elements: sequences with equal elements have equal `collect`. Identifies the
/// denotation's per-row sequences, whose closures call the mutually recursive evaluation functions at a fuel index,
/// with sequences built by a proof or an operator (re-exported as `exec::relational::domain::lemma_collect_pointwise`
/// and `link::expr::lemma_collect_pointwise`).
pub proof fn lemma_collect_pointwise<T>()
    ensures
        forall|rs1: Seq<Result<T, SqlError>>, rs2: Seq<Result<T, SqlError>>|
            rs1.len() == rs2.len() && (forall|j: int| 0 <= j < rs1.len() ==> rs1[j] == rs2[j])
            ==> #[trigger] collect(rs1) == #[trigger] collect(rs2),
{
    assert forall|rs1: Seq<Result<T, SqlError>>, rs2: Seq<Result<T, SqlError>>|
        rs1.len() == rs2.len() && (forall|j: int| 0 <= j < rs1.len() ==> rs1[j] == rs2[j])
        implies #[trigger] collect(rs1) == #[trigger] collect(rs2) by {
        assert(rs1 =~= rs2);
    }
}

/// `collect` succeeds iff every element does, and then its values are the elements' values, in order.
pub proof fn lemma_collect_ok<T>(rs: Seq<Result<T, SqlError>>)
    ensures
        (collect(rs) is Ok) == (forall|i: int| 0 <= i < rs.len() ==> #[trigger] rs[i] is Ok),
        collect(rs) is Ok ==> collect(rs)->Ok_0.len() == rs.len() && forall|i: int| 0 <= i < rs.len()
            ==> #[trigger] rs[i] == Ok::<T, SqlError>(collect(rs)->Ok_0[i]),
    decreases rs.len(),
{
    if rs.len() > 0 {
        let init = rs.drop_last();
        lemma_collect_ok(init);
        let n = rs.len() - 1;
        assert forall|i: int| 0 <= i < n implies #[trigger] init[i] == rs[i] by {}
        match collect(init) {
            Err(_) => {
                let i = choose|i: int| 0 <= i < init.len() && !(#[trigger] init[i] is Ok);
                assert(!(rs[i] is Ok));
            },
            Ok(vs) => {
                match rs[n] {
                    Err(_) => {},
                    Ok(v) => {
                        let out = vs.push(v);
                        assert(collect(rs) == Ok::<Seq<T>, SqlError>(out));
                        assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<T, SqlError>(out[i]) by {
                            if i < n {
                                assert(init[i] == Ok::<T, SqlError>(vs[i]));
                            }
                        }
                    },
                }
            },
        }
    }
}

/// If `rs[i]` is the first error, it is the outcome.
pub proof fn lemma_collect_first_err<T>(rs: Seq<Result<T, SqlError>>, i: int)
    requires
        0 <= i < rs.len(),
        rs[i] is Err,
        forall|j: int| 0 <= j < i ==> #[trigger] rs[j] is Ok,
    ensures
        collect(rs) == Err::<Seq<T>, SqlError>(rs[i]->Err_0),
    decreases rs.len(),
{
    let init = rs.drop_last();
    if i == rs.len() - 1 {
        lemma_collect_ok(init);
        assert forall|j: int| 0 <= j < init.len() implies #[trigger] init[j] is Ok by {
            assert(init[j] == rs[j]);
        }
    } else {
        assert forall|j: int| 0 <= j < i implies #[trigger] init[j] is Ok by {
            assert(init[j] == rs[j]);
        }
        lemma_collect_first_err(init, i);
    }
}

/// Every element succeeded with the given values.
pub proof fn lemma_collect_all<T>(rs: Seq<Result<T, SqlError>>, vs: Seq<T>)
    requires
        rs.len() == vs.len(),
        forall|i: int| 0 <= i < rs.len() ==> #[trigger] rs[i] == Ok::<T, SqlError>(vs[i]),
    ensures
        collect(rs) == Ok::<Seq<T>, SqlError>(vs),
{
    lemma_collect_ok(rs);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] is Ok by {}
    let ws = collect(rs)->Ok_0;
    assert forall|i: int| 0 <= i < vs.len() implies ws[i] == vs[i] by {
        assert(rs[i] == Ok::<T, SqlError>(ws[i]));
    }
    assert(ws =~= vs);
}

} // verus!
