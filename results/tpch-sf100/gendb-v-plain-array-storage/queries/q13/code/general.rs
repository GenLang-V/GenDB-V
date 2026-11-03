//! The general path (any pattern, any data; serial): when the fast path's run-time conditions fail. Without a
//! customer the answer is empty. Otherwise every orders row's `LIKE` is evaluated by the verified matcher (a raising
//! `LIKE` is the statement's error 22025); customer keys are found through a hash map (keys are distinct, PRIMARY
//! KEY); the counts per customer give the histogram (a `c_count` or `custdist` beyond int8 is the error 22003); the
//! answer rows come from the histogram (`answer::finish_rows`).
use vstd::prelude::*;
use vstd::hash_map::HashMapWithView;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::exec::value::*;
use crate::exec::fns::like::like_value_exec;
use crate::gendb_entry::{Answer, bound_db, stores_ready};
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::work::text_bytes;
use crate::query::{query_spec_at, param_domain};
use crate::spec::order::*;
use crate::link::query::{TextCol, text_at};
use crate::link::outcome::lemma_outcome_err;
use crate::agent::common::text_rows::offs_wf;
use crate::agent::common::zeroed::*;
use crate::agent::tables::*;
use crate::agent::normal::*;
use crate::agent::answer::*;
use crate::agent::errors::*;

verus! {

broadcast use {vstd::std_specs::hash::axiom_i64_obeys_hash_table_key_model, vstd::std_specs::hash::axiom_u64_obeys_hash_table_key_model};

/// The meaning of an answer for every database bound to the parts (the claim of `query`).
pub open spec fn answer_ok(sv: StoresView, ps: Seq<Literal>, a: Answer) -> bool {
    forall|db: Database| #[trigger] bound_db(sv, db) ==> crate::gendb_entry::outcome_ok(db, query_spec_at(ps), Ok(a))
}

/// A count is at most the number of rows looked at.
proof fn lemma_ocnt_bound(sv: StoresView, pat: Seq<u8>, key: int, n: int)
    requires n >= 0,
    ensures ocnt(sv, pat, key, n) <= n,
    decreases n,
{
    if n > 0 { lemma_ocnt_bound(sv, pat, key, n - 1); }
}

/// A histogram count is at most the number of customers looked at.
proof fn lemma_hcount_bound(sv: StoresView, pat: Seq<u8>, v: int, n: int)
    requires n >= 0,
    ensures hcount(sv, pat, v, n) <= n,
    decreases n,
{
    if n > 0 { lemma_hcount_bound(sv, pat, v, n - 1); }
}

/// The comment of orders row `j` as a value.
fn comment_val(c: &Cols, j: usize, Ghost(sv): Ghost<StoresView>) -> (v: EVal)
    requires cols_ok(*c, sv), j < c.no,
    ensures v@ == Val::Text(cmt(sv, j as int)),
{
    proof { reveal(parts_shape); }
    let col = TextCol { offsets: c.offs, bytes: c.bytes };
    proof { assert(0 <= col.offsets@[j as int] <= col.offsets@[j + 1] <= col.bytes@.len()); }
    let t = text_bytes(&col, j);
    let mut out: Vec<u8> = Vec::new();
    let mut k: usize = 0;
    let n = t.len();
    while k < n
        invariant k <= n, n == t@.len(), out@ == t@.subrange(0, k as int),
        decreases n - k,
    {
        out.push(t[k]);
        k = k + 1;
        proof { assert(out@ =~= t@.subrange(0, k as int)); }
    }
    proof { assert(out@ =~= t@); }
    EVal::Text(out)
}

/// The `NOT LIKE` outcome of every orders row: `Ok(flags)` (row `j` counted iff `flags[j]`), or the index of a row
/// whose `LIKE` raises.
fn like_pass(c: &Cols, pat: &[u8], Ghost(sv): Ghost<StoresView>) -> (r: Result<Vec<bool>, usize>)
    requires cols_ok(*c, sv),
    ensures
        match r {
            Ok(flags) => likes_ok(sv, pat@) && flags@.len() == n_o(sv)
                && forall|j: int| 0 <= j < n_o(sv) ==> #[trigger] flags@[j] == counted(sv, pat@, j),
            Err(j0) => j0 < n_o(sv) && like_j(sv, pat@, j0 as int) is Err,
        },
{
    let mut pv: Vec<u8> = Vec::new();
    let mut k: usize = 0;
    while k < pat.len()
        invariant k <= pat@.len(), pv@ == pat@.subrange(0, k as int),
        decreases pat@.len() - k,
    {
        pv.push(pat[k]);
        k = k + 1;
        proof { assert(pv@ =~= pat@.subrange(0, k as int)); }
    }
    proof { assert(pv@ =~= pat@); }
    let p = EVal::Text(pv);
    let mut ev: Vec<u8> = Vec::new();
    ev.push(0x5Cu8);
    proof { assert(ev@ =~= seq![0x5Cu8]); }
    let e = EVal::Text(ev);
    let no = c.no;
    let mut flags: Vec<bool> = Vec::new();
    let mut j: usize = 0;
    while j < no
        invariant
            cols_ok(*c, sv), no == c.no, j <= no, p@ == Val::Text(pat@), e@ == Val::Text(seq![0x5Cu8]),
            flags@.len() == j,
            forall|j2: int| 0 <= j2 < j ==> #[trigger] like_j(sv, pat@, j2) is Ok && flags@[j2] == counted(sv, pat@, j2),
        decreases no - j,
    {
        let s = comment_val(c, j, Ghost(sv));
        let res = like_value_exec(&s, &p, &e);
        proof { lemma_like_kinds(cmt(sv, j as int), pat@); }
        match res {
            Ok(v) => {
                let b = match v {
                    EVal::Bool(b) => b,
                    _ => {
                        proof {
                            let bb = choose|bb: bool| like_j(sv, pat@, j as int) == Ok::<Val, SqlError>(Val::Bool(bb));
                            assert(v@ == Val::Bool(bb));
                            assert(false);
                        }
                        false
                    },
                };
                flags.push(!b);
            },
            Err(_) => {
                return Err(j);
            },
        }
        j = j + 1;
    }
    Ok(flags)
}

/// The number of counted orders of every customer row (customer keys distinct).
fn count_pass(c: &Cols, flags: &Vec<bool>, Ghost(sv): Ghost<StoresView>, Ghost(pat): Ghost<Seq<u8>>) -> (cnt: Vec<u64>)
    requires
        cols_ok(*c, sv), keys_unique(cck(sv)), flags@.len() == n_o(sv),
        forall|j: int| 0 <= j < n_o(sv) ==> #[trigger] flags@[j] == counted(sv, pat, j),
    ensures cnt@.len() == n_c(sv), forall|i: int| 0 <= i < n_c(sv) ==> #[trigger] cnt@[i] as int == ccnt(sv, pat, i),
{
    let nc = c.nc;
    let no = c.no;
    proof { reveal(parts_shape); }
    // key -> customer row
    let mut map: HashMapWithView<i64, usize> = HashMapWithView::new();
    let mut i: usize = 0;
    while i < nc
        invariant
            cols_ok(*c, sv), keys_unique(cck(sv)), nc == c.nc, i <= nc,
            forall|i2: int| 0 <= i2 < i ==> #[trigger] map@.contains_key(cck(sv)[i2]) && map@[cck(sv)[i2]] == i2,
            forall|k: i64| #[trigger] map@.contains_key(k) ==> map@[k] < i && cck(sv)[map@[k] as int] == k,
        decreases nc - i,
    {
        let key = c.cck[i];
        let ghost m0 = map@;
        map.insert(key, i);
        proof {
            assert forall|i2: int| 0 <= i2 < i + 1 implies #[trigger] map@.contains_key(cck(sv)[i2]) && map@[cck(sv)[i2]] == i2 by {
                if i2 < i {
                    assert(cck(sv)[i2] != key);
                }
            }
        }
        i = i + 1;
    }
    let mut cnt = zeros_u64(nc);
    proof {
        assert forall|i2: int| 0 <= i2 < nc implies #[trigger] cnt@[i2] as int == ocnt(sv, pat, cck(sv)[i2] as int, 0) by {}
    }
    let mut j: usize = 0;
    while j < no
        invariant
            cols_ok(*c, sv), keys_unique(cck(sv)), nc == c.nc, no == c.no, j <= no, cnt@.len() == nc, c.ock@.len() == no,
            flags@.len() == n_o(sv), forall|j2: int| 0 <= j2 < n_o(sv) ==> #[trigger] flags@[j2] == counted(sv, pat, j2),
            forall|i2: int| 0 <= i2 < nc ==> #[trigger] map@.contains_key(cck(sv)[i2]) && map@[cck(sv)[i2]] == i2,
            forall|k: i64| #[trigger] map@.contains_key(k) ==> map@[k] < nc && cck(sv)[map@[k] as int] == k,
            forall|i2: int| 0 <= i2 < nc ==> #[trigger] cnt@[i2] as int == ocnt(sv, pat, cck(sv)[i2] as int, j as int),
        decreases no - j,
    {
        let ghost c0 = cnt@;
        if flags[j] {
            let key = c.ock[j];
            match map.get(&key) {
                Some(ix) => {
                    let ix = *ix;
                    proof { lemma_ocnt_bound(sv, pat, cck(sv)[ix as int] as int, j as int); }
                    cnt[ix] = cnt[ix] + 1;
                    proof {
                        assert forall|i2: int| 0 <= i2 < nc implies #[trigger] cnt@[i2] as int == ocnt(sv, pat, cck(sv)[i2] as int, j + 1) by {
                            if i2 != ix { if cck(sv)[i2] == key { assert(map@[cck(sv)[i2]] == i2); } }
                        }
                    }
                },
                None => {
                    proof {
                        assert forall|i2: int| 0 <= i2 < nc implies #[trigger] cnt@[i2] as int == ocnt(sv, pat, cck(sv)[i2] as int, j + 1) by {
                            assert(map@.contains_key(cck(sv)[i2]));
                        }
                    }
                },
            }
        }
        j = j + 1;
    }
    cnt
}

/// A customer row below `n` with count `v` makes `hcount(v, n)` positive, and a positive count has such a row.
proof fn lemma_hcount_witness(sv: StoresView, pat: Seq<u8>, v: int, n: int)
    requires hcount(sv, pat, v, n) > 0,
    ensures exists|i: int| 0 <= i < n && #[trigger] ccnt(sv, pat, i) == v,
    decreases n,
{
    if n > 0 && ccnt(sv, pat, n - 1) != v {
        lemma_hcount_witness(sv, pat, v, n - 1);
    }
}

/// The distinct counts of the customers, first occurrence first, each with its number of customers.
fn count_pairs(cnt: &Vec<u64>, Ghost(sv): Ghost<StoresView>, Ghost(pat): Ghost<Seq<u8>>) -> (vals: Vec<(u64, u64)>)
    requires
        cnt@.len() == n_c(sv),
        forall|i: int| 0 <= i < n_c(sv) ==> #[trigger] cnt@[i] as int == ccnt(sv, pat, i) && cnt@[i] <= i64::MAX,
    ensures
        forall|a: int, b: int| 0 <= a < vals@.len() && 0 <= b < vals@.len() && a != b ==> (#[trigger] vals@[a]).0 != (#[trigger] vals@[b]).0,
        forall|k: int| 0 <= k < vals@.len() ==> (#[trigger] vals@[k]).1 as int == hcount(sv, pat, vals@[k].0 as int, n_c(sv))
            && vals@[k].1 > 0 && vals@[k].0 <= i64::MAX,
        forall|i: int| 0 <= i < n_c(sv) ==> has_count(vals@, #[trigger] ccnt(sv, pat, i) as int),
{
    let nc = cnt.len();
    let mut map: HashMapWithView<u64, usize> = HashMapWithView::new();
    let mut vals: Vec<(u64, u64)> = Vec::new();
    let mut i: usize = 0;
    while i < nc
        invariant
            i <= nc, nc == n_c(sv), cnt@.len() == nc,
            forall|i2: int| 0 <= i2 < nc ==> #[trigger] cnt@[i2] as int == ccnt(sv, pat, i2) && cnt@[i2] <= i64::MAX,
            forall|k: int| 0 <= k < vals@.len() ==> (#[trigger] vals@[k]).1 as int == hcount(sv, pat, vals@[k].0 as int, i as int)
                && vals@[k].1 > 0 && vals@[k].0 <= i64::MAX && map@.contains_key(vals@[k].0) && map@[vals@[k].0] == k,
            forall|v: u64| #[trigger] map@.contains_key(v) ==> map@[v] < vals@.len() && vals@[map@[v] as int].0 == v,
            forall|i2: int| 0 <= i2 < i ==> #[trigger] map@.contains_key(cnt@[i2]),
        decreases nc - i,
    {
        let v = cnt[i];
        let ghost (m0, v0) = (map@, vals@);
        match map.get(&v) {
            Some(k) => {
                let k = *k;
                let (w, h) = vals[k];
                proof { lemma_hcount_bound(sv, pat, w as int, i as int); }
                vals.set(k, (w, h + 1));
                proof {
                    assert forall|k2: int| 0 <= k2 < vals@.len() implies (#[trigger] vals@[k2]).1 as int == hcount(sv, pat, vals@[k2].0 as int, i + 1)
                        && vals@[k2].1 > 0 && vals@[k2].0 <= i64::MAX && map@.contains_key(vals@[k2].0) && map@[vals@[k2].0] == k2 by {
                        if k2 != k { assert(vals@[k2] == v0[k2]); assert(v0[k2].0 != v); }
                    }
                }
            },
            None => {
                let k = vals.len();
                map.insert(v, k);
                vals.push((v, 1));
                proof {
                    if hcount(sv, pat, v as int, i as int) > 0 {
                        lemma_hcount_witness(sv, pat, v as int, i as int);
                        let i2 = choose|i2: int| 0 <= i2 < i && #[trigger] ccnt(sv, pat, i2) == v as int;
                        assert(m0.contains_key(cnt@[i2]));
                    }
                    assert forall|k2: int| 0 <= k2 < vals@.len() implies (#[trigger] vals@[k2]).1 as int == hcount(sv, pat, vals@[k2].0 as int, i + 1)
                        && vals@[k2].1 > 0 && vals@[k2].0 <= i64::MAX && map@.contains_key(vals@[k2].0) && map@[vals@[k2].0] == k2 by {
                        if k2 < k { assert(vals@[k2] == v0[k2]); assert(v0[k2].0 != v); }
                    }
                }
            },
        }
        i = i + 1;
    }
    proof {
        assert forall|a: int, b: int| 0 <= a < vals@.len() && 0 <= b < vals@.len() && a != b implies (#[trigger] vals@[a]).0 != (#[trigger] vals@[b]).0 by {}
        assert forall|i2: int| 0 <= i2 < n_c(sv) implies has_count(vals@, #[trigger] ccnt(sv, pat, i2) as int) by {
            assert(map@.contains_key(cnt@[i2]));
            let k = map@[cnt@[i2]] as int;
            assert(vals@[k].0 == cnt@[i2]);
            assert(cnt@[i2] as int == ccnt(sv, pat, i2));
            assert(0 <= k < vals@.len() && vals@[k].0 as int == ccnt(sv, pat, i2));
        }
    }
    vals
}

/// `vals` (distinct counts) sorted by `custdist DESC, c_count DESC`.
fn sort_pairs(vals: &Vec<(u64, u64)>) -> (ps: Vec<(u64, u64)>)
    requires forall|a: int, b: int| 0 <= a < vals@.len() && 0 <= b < vals@.len() && a != b ==> (#[trigger] vals@[a]).0 != (#[trigger] vals@[b]).0,
    ensures
        forall|a: int, b: int| 0 <= a < b < ps@.len() ==> before(#[trigger] ps@[a], #[trigger] ps@[b]),
        forall|x: (u64, u64)| #[trigger] ps@.contains(x) <==> vals@.contains(x),
{
    let n = vals.len();
    let mut ps: Vec<(u64, u64)> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n, n == vals@.len(),
            forall|a: int, b: int| 0 <= a < vals@.len() && 0 <= b < vals@.len() && a != b ==> (#[trigger] vals@[a]).0 != (#[trigger] vals@[b]).0,
            forall|a: int, b: int| 0 <= a < b < ps@.len() ==> before(#[trigger] ps@[a], #[trigger] ps@[b]),
            forall|x: (u64, u64)| #[trigger] ps@.contains(x) <==> exists|k2: int| 0 <= k2 < k && vals@[k2] == x,
        decreases n - k,
    {
        let x = vals[k];
        let mut t: usize = 0;
        while t < ps.len() && !(x.1 > ps[t].1 || (x.1 == ps[t].1 && x.0 > ps[t].0))
            invariant t <= ps@.len(), forall|s: int| 0 <= s < t ==> !before(x, #[trigger] ps@[s]),
            decreases ps@.len() - t,
        {
            t = t + 1;
        }
        let ghost p0 = ps@;
        proof {
            assert forall|s: int| 0 <= s < p0.len() implies (#[trigger] p0[s]).0 != x.0 by {
                assert(p0.contains(p0[s]));
                let k2 = choose|k2: int| 0 <= k2 < k && vals@[k2] == p0[s];
                assert(k2 != k);
            }
            lemma_insert_sorted(p0, x, t as int);
        }
        ps.insert(t, x);
        proof {
            assert forall|y: (u64, u64)| #[trigger] ps@.contains(y) <==> exists|k2: int| 0 <= k2 < k + 1 && vals@[k2] == y by {
                if ps@.contains(y) {
                    let s = choose|s: int| 0 <= s < ps@.len() && ps@[s] == y;
                    if s < t { assert(p0[s] == y); assert(p0.contains(y)); }
                    else if s > t { assert(p0[s - 1] == y); assert(p0.contains(y)); }
                }
                if exists|k2: int| 0 <= k2 < k + 1 && vals@[k2] == y {
                    let k2 = choose|k2: int| 0 <= k2 < k + 1 && vals@[k2] == y;
                    if k2 == k {
                        assert(ps@[t as int] == y);
                    } else {
                        assert(p0.contains(y));
                        let s = choose|s: int| 0 <= s < p0.len() && p0[s] == y;
                        if s < t { assert(ps@[s] == y); } else { assert(ps@[s + 1] == y); }
                    }
                }
            }
        }
        k = k + 1;
    }
    proof {
        assert forall|x: (u64, u64)| #[trigger] ps@.contains(x) <==> vals@.contains(x) by {
            if vals@.contains(x) {
                let k2 = choose|k2: int| 0 <= k2 < vals@.len() && vals@[k2] == x;
            }
        }
    }
    ps
}

/// The general path's answer.
pub fn general(c: &Cols, pat: &[u8], Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (a: Answer)
    requires cols_ok(*c, sv), stores_ready(sv), param_domain(ps), pat@ == pat_of(ps),
    ensures answer_ok(sv, ps, a),
{
    let nc = c.nc;
    if nc == 0 {
        let pairs: Vec<(u64, u64)> = Vec::new();
        let rows = finish_pairs(&pairs, Ghost(sv), Ghost(ps));
        return Answer::Rows(rows);
    }
    let flags = match like_pass(c, pat, Ghost(sv)) {
        Ok(f) => f,
        Err(j0) => {
            proof {
                lemma_like_kinds(cmt(sv, j0 as int), pat@);
                assert forall|db: Database| #[trigger] bound_db(sv, db) implies
                    crate::gendb_entry::outcome_ok(db, query_spec_at(ps), Ok(Answer::SqlError(SqlError::InvalidEscapeSequence))) by {
                    lemma_like_error(sv, db, ps, j0 as int);
                    lemma_outcome_err(db, query_spec_at(ps), SqlError::InvalidEscapeSequence);
                }
            }
            return Answer::SqlError(SqlError::InvalidEscapeSequence);
        },
    };
    proof {
        let db = choose|db: Database| bound_db(sv, db);
        lemma_cust_keys_unique(sv, db);
    }
    let cnt = count_pass(c, &flags, Ghost(sv), Ghost(pat@));
    // a count beyond int8 is the inner GROUP BY's error
    let mut i: usize = 0;
    while i < nc
        invariant nc == n_c(sv), i <= nc, cnt@.len() == nc,
            param_domain(ps), pat@ == pat_of(ps), likes_ok(sv, pat@),
            forall|i2: int| 0 <= i2 < nc ==> #[trigger] cnt@[i2] as int == ccnt(sv, pat@, i2),
            forall|i2: int| 0 <= i2 < i ==> #[trigger] cnt@[i2] <= i64::MAX,
        decreases nc - i,
    {
        if cnt[i] > i64::MAX as u64 {
            proof {
                assert forall|db: Database| #[trigger] bound_db(sv, db) implies
                    crate::gendb_entry::outcome_ok(db, query_spec_at(ps), Ok(Answer::SqlError(SqlError::NumericValueOutOfRange))) by {
                    lemma_count_error(sv, db, ps, i as int);
                    lemma_outcome_err(db, query_spec_at(ps), SqlError::NumericValueOutOfRange);
                }
            }
            return Answer::SqlError(SqlError::NumericValueOutOfRange);
        }
        i = i + 1;
    }
    let vals = count_pairs(&cnt, Ghost(sv), Ghost(pat@));
    // a `custdist` beyond int8 is the outer GROUP BY's error
    let mut k: usize = 0;
    while k < vals.len()
        invariant
            k <= vals@.len(), nc == n_c(sv), param_domain(ps), pat@ == pat_of(ps), likes_ok(sv, pat@),
            forall|i2: int| 0 <= i2 < nc ==> #[trigger] cnt@[i2] as int == ccnt(sv, pat@, i2) && cnt@[i2] <= i64::MAX,
            forall|k2: int| 0 <= k2 < vals@.len() ==> (#[trigger] vals@[k2]).1 as int == hcount(sv, pat@, vals@[k2].0 as int, n_c(sv))
                && vals@[k2].1 > 0 && vals@[k2].0 <= i64::MAX,
            forall|k2: int| 0 <= k2 < k ==> (#[trigger] vals@[k2]).1 <= i64::MAX,
        decreases vals@.len() - k,
    {
        if vals[k].1 > i64::MAX as u64 {
            proof {
                assert forall|i2: int| 0 <= i2 < n_c(sv) implies #[trigger] ccnt(sv, pat_of(ps), i2) <= i64::MAX by {
                    assert(cnt@[i2] as int == ccnt(sv, pat@, i2) && cnt@[i2] <= i64::MAX);
                }
                assert forall|db: Database| #[trigger] bound_db(sv, db) implies
                    crate::gendb_entry::outcome_ok(db, query_spec_at(ps), Ok(Answer::SqlError(SqlError::NumericValueOutOfRange))) by {
                    lemma_custdist_error(sv, db, ps, vals@[k as int].0 as int);
                    lemma_outcome_err(db, query_spec_at(ps), SqlError::NumericValueOutOfRange);
                }
            }
            return Answer::SqlError(SqlError::NumericValueOutOfRange);
        }
        k = k + 1;
    }
    let pairs = sort_pairs(&vals);
    proof {
        assert forall|t: int| 0 <= t < pairs@.len() implies (#[trigger] pairs@[t]).1 as int == hcount(sv, pat@, pairs@[t].0 as int, n_c(sv))
            && pairs@[t].1 > 0 && pairs@[t].0 <= i64::MAX && pairs@[t].1 <= i64::MAX by {
            assert(pairs@.contains(pairs@[t]));
            let k2 = choose|k2: int| 0 <= k2 < vals@.len() && vals@[k2] == pairs@[t];
        }
        assert forall|i2: int| 0 <= i2 < n_c(sv) implies has_count(pairs@, #[trigger] ccnt(sv, pat@, i2) as int) by {
            assert(has_count(vals@, ccnt(sv, pat@, i2) as int));
            let k2 = choose|k2: int| 0 <= k2 < vals@.len() && (#[trigger] vals@[k2]).0 as int == ccnt(sv, pat@, i2);
            assert(vals@.contains(vals@[k2]));
            assert(pairs@.contains(vals@[k2]));
            let t = choose|t: int| 0 <= t < pairs@.len() && pairs@[t] == vals@[k2];
            assert(pairs@[t].0 as int == ccnt(sv, pat@, i2));
        }
    }
    let rows = finish_pairs(&pairs, Ghost(sv), Ghost(ps));
    Answer::Rows(rows)
}

} // verus!
