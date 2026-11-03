//! The query `SELECT name, cik, SUM(value) ... GROUP BY name, cik HAVING SUM(value) > (AVG of the per-cik sums)
//! ORDER BY 3 DESC LIMIT 100` over the flat storages of `sub` and `num`.
//!
//! Plan: (1) the qualifying subs (`fy = $2`) in row order, ranked; (2) a parallel scan of `num` (`run`, `scan`):
//! per rank the exact sum of the values of its num rows with `uom = $1`; (3) the groups `(name, cik)` of the ranks
//! with rows, their sums, the number of distinct ciks and the total (`groups`); (4) the AVG of the per-cik sums
//! (the total over the cik count, PostgreSQL's numeric division), the HAVING filter and the top 100 (`answer`).
//! Inputs beyond the fast path's bounds take a quadratic fallback for (2) and (3) (`slow`). The proof (`nf`)
//! states the SQL meaning in the same terms.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db, outcome_ok};
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::{QueryError, WorkerFailure};
use crate::gendb_params::Params;
use crate::query::{param_domain, query_spec_at};
use crate::link::query::text_wf;
use crate::stores::flat_sub::interface as si;
use crate::stores::flat_num::interface as ni;

pub mod common;
pub mod nf;
pub mod keys;
pub mod scan;
pub mod run;
pub mod groups;
pub mod answer;
pub mod slow;

use common::wide::*;
use keys::*;
use scan::*;
use run::*;
use groups::*;
use answer::*;
use nf::rows::*;
use nf::glue::cols_of;

verus! {

/// The facts of the stored parts every bound database has.
pub open spec fn parts_ok(sv: StoresView, n_sub: nat, n_num: nat) -> bool {
    parts_facts(sv, n_sub, n_num)
}

/// The num columns.
fn read_num(stores: &mut Stores, Ghost(sv): Ghost<StoresView>, Ghost(n0): Ghost<nat>, Ghost(m0): Ghost<nat>) -> (num: NumCols)
    requires old(stores)@ == sv, parts_facts(sv, n0, m0),
    ensures
        final(stores)@ == sv, num.n == m0, num.wf(),
        num.uom_text() == ni::text_view(sv.flat_num, ni::UOM_OFFSETS as int, ni::UOM_BYTES as int),
        num.adsh_text() == ni::text_view(sv.flat_num, ni::ADSH_OFFSETS as int, ni::ADSH_BYTES as int),
        num.value@ == ni::i128s(sv.flat_num[ni::VALUE as int]),
        num.uom_off@.len() == num.n + 1,
{
    let np = Ghost(sv.flat_num);
    proof {
        assert(text_wf(ni::text_view(sv.flat_num, ni::ADSH_OFFSETS as int, ni::ADSH_BYTES as int), m0 as int));
        assert(text_wf(ni::text_view(sv.flat_num, ni::UOM_OFFSETS as int, ni::UOM_BYTES as int), m0 as int));
    }
    let n = stores.flat_num.part_len(ni::ADSH_OFFSETS) - 1;
    let adsh_off = stores.flat_num.extent_i64(ni::ADSH_OFFSETS, 0, n + 1);
    let l = stores.flat_num.part_len(ni::ADSH_BYTES);
    let adsh_bytes = stores.flat_num.extent_u8(ni::ADSH_BYTES, 0, l);
    let uom_off = stores.flat_num.extent_i64(ni::UOM_OFFSETS, 0, n + 1);
    let l = stores.flat_num.part_len(ni::UOM_BYTES);
    let uom_bytes = stores.flat_num.extent_u8(ni::UOM_BYTES, 0, l);
    let value = stores.flat_num.extent_i128(ni::VALUE, 0, n);
    let num = NumCols { uom_off, uom_bytes, adsh_off, adsh_bytes, value, n, uom_len: uom_bytes.len(), adsh_len: adsh_bytes.len() };
    proof {
        let p = sv.flat_num;
        assert(adsh_off@ =~= ni::i64s(p[ni::ADSH_OFFSETS as int]));
        assert(adsh_bytes@ =~= ni::u8s(p[ni::ADSH_BYTES as int]));
        assert(uom_off@ =~= ni::i64s(p[ni::UOM_OFFSETS as int]));
        assert(uom_bytes@ =~= ni::u8s(p[ni::UOM_BYTES as int]));
        assert(value@ =~= ni::i128s(p[ni::VALUE as int]));
        assert forall|i: int| 0 <= i < num.n implies #[trigger] abs(num.val(i)) < pow10(28) by {
            assert(abs(num_value(p, i)) < pow10(28));
        }
    }
    num
}

/// The sub columns of the scan.
fn read_sub(stores: &mut Stores, Ghost(sv): Ghost<StoresView>, Ghost(n0): Ghost<nat>, Ghost(m0): Ghost<nat>, p1: i32) -> (sub: SubCols)
    requires old(stores)@ == sv, parts_facts(sv, n0, m0),
    ensures
        final(stores)@ == sv, sub.n == n0, sub.p1 == p1,
        slow::sub_text_ok(&sub),
        sub.text() == si::text_view(sv.flat_sub, si::ADSH_OFFSETS as int, si::ADSH_BYTES as int),
        sub.fy@ == si::i32s(sv.flat_sub[si::FY as int]),
        sub.fy_valid@ == si::u8s(sv.flat_sub[si::FY_VALIDITY as int]),
        sub.fy@.len() == sub.n, sub.fy_valid@.len() == sub.n,
        sub.adsh_off@.len() == sub.n + 1,
        forall|j1: int, j2: int| 0 <= j1 < sub.n && 0 <= j2 < sub.n && j1 != j2
            ==> #[trigger] sub.key(j1) != #[trigger] sub.key(j2),
{
    proof {
        assert(text_wf(si::text_view(sv.flat_sub, si::ADSH_OFFSETS as int, si::ADSH_BYTES as int), n0 as int));
    }
    let n = stores.flat_sub.part_len(si::ADSH_OFFSETS) - 1;
    let adsh_off = stores.flat_sub.extent_i64(si::ADSH_OFFSETS, 0, n + 1);
    let l = stores.flat_sub.part_len(si::ADSH_BYTES);
    let adsh_bytes = stores.flat_sub.extent_u8(si::ADSH_BYTES, 0, l);
    let fy = stores.flat_sub.extent_i32(si::FY, 0, n);
    let fy_valid = stores.flat_sub.extent_u8(si::FY_VALIDITY, 0, n);
    let sub = SubCols { adsh_off, adsh_bytes, fy, fy_valid, n, bytes_len: adsh_bytes.len(), p1 };
    proof {
        let p = sv.flat_sub;
        assert(adsh_off@ =~= si::i64s(p[si::ADSH_OFFSETS as int]));
        assert(adsh_bytes@ =~= si::u8s(p[si::ADSH_BYTES as int]));
        assert(fy@ =~= si::i32s(p[si::FY as int]));
        assert(fy_valid@ =~= si::u8s(p[si::FY_VALIDITY as int]));
        assert forall|j1: int, j2: int| 0 <= j1 < sub.n && 0 <= j2 < sub.n && j1 != j2
            implies #[trigger] sub.key(j1) != #[trigger] sub.key(j2) by {
            assert(sub_adsh(p, j1) != sub_adsh(p, j2));
        }
    }
    sub
}

/// The sub columns of the group key.
fn read_keys(stores: &mut Stores, Ghost(sv): Ghost<StoresView>, Ghost(n0): Ghost<nat>, Ghost(m0): Ghost<nat>) -> (kc: KeyCols)
    requires old(stores)@ == sv, parts_facts(sv, n0, m0),
    ensures
        final(stores)@ == sv, kc.n == n0, kc.wf(),
        kc.text() == si::text_view(sv.flat_sub, si::NAME_OFFSETS as int, si::NAME_BYTES as int),
        kc.cik@ == si::i32s(sv.flat_sub[si::CIK as int]),
{
    proof {
        assert(text_wf(si::text_view(sv.flat_sub, si::NAME_OFFSETS as int, si::NAME_BYTES as int), n0 as int));
    }
    let n = stores.flat_sub.part_len(si::NAME_OFFSETS) - 1;
    let cik = stores.flat_sub.extent_i32(si::CIK, 0, n);
    let name_off = stores.flat_sub.extent_i64(si::NAME_OFFSETS, 0, n + 1);
    let l = stores.flat_sub.part_len(si::NAME_BYTES);
    let name_bytes = stores.flat_sub.extent_u8(si::NAME_BYTES, 0, l);
    let kc = KeyCols { name_off, name_bytes, cik, n, bytes_len: name_bytes.len() };
    proof {
        let p = sv.flat_sub;
        assert(cik@ =~= si::i32s(p[si::CIK as int]));
        assert(name_off@ =~= si::i64s(p[si::NAME_OFFSETS as int]));
        assert(name_bytes@ =~= si::u8s(p[si::NAME_BYTES as int]));
        reveal(KeyCols::wf);
    }
    kc
}

/// The qualifying sub rows in row order.
fn qual_rows(sub: &SubCols) -> (r: Vec<usize>)
    requires sub.fy@.len() == sub.n, sub.fy_valid@.len() == sub.n,
    ensures r@.len() == sub.qlist(sub.n as int).len(),
        forall|t: int| 0 <= t < r@.len() ==> #[trigger] r@[t] as int == sub.qlist(sub.n as int)[t],
{
    let n = sub.n;
    let mut r: Vec<usize> = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant
            n == sub.n, j <= n, sub.fy@.len() == sub.n, sub.fy_valid@.len() == sub.n,
            r@.len() == sub.qlist(j as int).len(),
            forall|t: int| 0 <= t < r@.len() ==> #[trigger] r@[t] as int == sub.qlist(j as int)[t],
        decreases n - j,
    {
        let ghost r0 = r@;
        if sub.fy_valid[j] != 0 && sub.fy[j] == sub.p1 {
            r.push(j);
            proof {
                assert(sub.qlist(j + 1) == sub.qlist(j as int).push(j as int));
                assert forall|t: int| 0 <= t < r@.len() implies #[trigger] r@[t] as int == sub.qlist(j + 1)[t] by {
                    if t < r0.len() {
                        assert(r@[t] == r0[t]);
                    }
                }
            }
        } else {
            proof {
                assert(sub.qlist(j + 1) == sub.qlist(j as int));
            }
        }
        j = j + 1;
    }
    r
}

/// The smallest table size `2^bits >= 1.5 nq` (at most `2^30`).
fn table_bits(nq: usize) -> (bits: u64)
    requires nq < 0x2000_0000,
    ensures 1 <= bits <= 30, pow2i(bits as nat) <= 0x4000_0000,
{
    let want: u64 = (nq as u64) + (nq as u64) / 2;
    let mut bits: u64 = 1;
    while bits < 30 && (1u64 << bits) < want
        invariant 1 <= bits <= 30,
        decreases 30 - bits,
    {
        bits = bits + 1;
    }
    proof {
        vstd::arithmetic::power2::lemma2_to64();
        if bits < 30 {
            vstd::arithmetic::power2::lemma_pow2_strictly_increases(bits as nat, 30);
        }
    }
    bits
}

/// The scan's totals fit the grouping's input bounds.
proof fn lemma_ranks(num: &NumCols, sub: &SubCols, kc: &KeyCols, p0: Seq<u8>, qr: Seq<usize>, tot: Seq<Wide>, seen: Seq<bool>)
    requires
        num.wf(), totals_ok(num, sub, p0, tot, seen, num.n as int), kc.n == sub.n,
        qr.len() == sub.qlist(sub.n as int).len(), qr.len() <= usize::MAX,
        forall|t: int| 0 <= t < qr.len() ==> #[trigger] qr[t] as int == sub.qlist(sub.n as int)[t],
    ensures ranks_wf(kc, qr, tot, seen),
{
    lemma_qlist(sub, sub.n as int);
    assert forall|id: int| 0 <= id < qr.len() implies #[trigger] qr[id] < kc.n by {
        assert(qr[id] as int == sub.qlist(sub.n as int)[id]);
    }
    assert(pow10(28) == 10000000000000000000000000000) by (compute);
    assert forall|id: int| 0 <= id < qr.len() implies -rank_limit() <= #[trigger] wval(tot[id]) <= rank_limit() by {
        let key = rank_key(sub, id);
        assert(wval(tot[id]) == rsum(num, p0, key, 0, num.n as int));
        lemma_rsum_bound(num, p0, key, 0, num.n as int);
        let m = num.n as int;
        assert(m * (pow10(28) - 1) <= 0xffff_ffff_ffff_ffff * 9999999999999999999999999999int) by (nonlinear_arith)
            requires 0 <= m <= 0xffff_ffff_ffff_ffffint, pow10(28) == 10000000000000000000000000000int;
        assert(0xffff_ffff_ffff_ffff * 9999999999999999999999999999int <= rank_limit());
    }
}

/// The per-rank totals and the groups, by the fast path or the fallback.
fn groups_of(num: &NumCols, sub: &SubCols, kc: &KeyCols, p0: &'static [u8], p0_len: usize, qr: &Vec<usize>,
    workers: usize, dispatch: &mut Dispatch) -> (r: Result<(Vec<Wide>, Vec<bool>, Groups), WorkerFailure>)
    requires
        num.wf(), slow::sub_text_ok(sub), kc.wf(), kc.n == sub.n, p0_len == p0@.len(),
        sub.fy@.len() == sub.n, sub.fy_valid@.len() == sub.n,
        forall|j1: int, j2: int| 0 <= j1 < sub.n && 0 <= j2 < sub.n && j1 != j2
            ==> #[trigger] sub.key(j1) != #[trigger] sub.key(j2),
        qr@.len() == sub.qlist(sub.n as int).len(),
        forall|t: int| 0 <= t < qr@.len() ==> #[trigger] qr@[t] as int == sub.qlist(sub.n as int)[t],
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok((tot, seen, g)) ==> {
            &&& totals_ok(num, sub, p0@, tot@, seen@, num.n as int)
            &&& groups_ok(&g, kc, qr@, tot@, seen@, qr@.len() as int)
            &&& groups_cols(&g, kc)
            &&& g.sum@.len() == g.rep@.len()
            &&& seen@.len() == qr@.len()
        },
{
    let nq = qr.len();
    if sub.n < 0xffff_fff0 && nq < 0x2000_0000 && (num.n as u64) < 0x2_0000_0000u64 {
        let bits = table_bits(nq);
        proof {
            assert(sub.wf());
        }
        let (tot, seen) = match run_scan(num, sub, p0, p0_len, nq, bits, workers, dispatch) {
            Ok(x) => x,
            Err(e) => return Err(e),
        };
        proof {
            lemma_ranks(num, sub, kc, p0@, qr@, tot@, seen@);
        }
        let g = build_groups(kc, qr, &tot, &seen, bits);
        Ok((tot, seen, g))
    } else {
        let (tot, seen) = slow::slow_totals(num, sub, p0, p0_len, qr);
        proof {
            lemma_ranks(num, sub, kc, p0@, qr@, tot@, seen@);
        }
        let g = slow::slow_groups(kc, qr, &tot, &seen);
        Ok((tot, seen, g))
    }
}

pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures
        answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    let ghost db0 = choose|db| bound_db(sv, db);
    proof {
        lemma_bound_facts(sv, db0);
    }
    let ghost n_sub0 = db0.tables[0].len();
    let ghost n_num0 = db0.tables[1].len();
    let p0 = params.p0;
    let p0_len = p0.len();
    let p1 = params.p1 as i32;
    let num = read_num(stores, Ghost(sv), Ghost(n_sub0), Ghost(n_num0));
    let sub = read_sub(stores, Ghost(sv), Ghost(n_sub0), Ghost(n_num0), p1);
    let kc = read_keys(stores, Ghost(sv), Ghost(n_sub0), Ghost(n_num0));
    let qr = qual_rows(&sub);
    let (tot, seen, g) = match groups_of(&num, &sub, &kc, p0, p0_len, &qr, workers, dispatch) {
        Ok(x) => x,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let (ans, Ghost(cand), Ghost(pick), Ghost(ac), Ghost(asc)) = answer(&g, &kc);
    let _ng = g.rep.len();
    let ghost ps = params@;
    let ghost p1i = params.p1 as int;
    proof {
        assert(cols_of(sv, &num, &sub, &kc));
        assert(nf::fromwhere::binding(ps, p0@, p1i));
        assert(nf::endgame::views_ok(sv, &num, &sub, &kc, p0@, p1i, qr@, tot@, seen@, &g));
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies {
            &&& ans matches Outcome3::Rows(out) ==> crate::spec::order::ordered_ok(db, query_spec_at(ps),
                Ok::<Relation, SqlError>(crate::link::query::view_rows(out@)))
            &&& ans matches Outcome3::Err(e) ==> crate::spec::order::ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(e))
            &&& ans is Capacity ==> !crate::gendb_entry::capacity_domain(db, query_spec_at(ps))
        } by {
            nf::endgame::lemma_final(sv, db, ps, &num, &sub, &kc, p0@, p1i, qr@, tot@, seen@, &g, &ans, cand, pick, ac, asc);
        }
    }
    match ans {
        Outcome3::Rows(rows) => Ok(Answer::Rows(rows)),
        Outcome3::Err(e) => Ok(Answer::SqlError(e)),
        Outcome3::Capacity => Ok(Answer::Capacity),
    }
}

} // verus!
