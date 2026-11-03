//! The general path (serial, on the calling thread): used when the l_partkey directory is absent or a fast-path
//! threshold left its integer range. Every matching part row scans all stored lineitem rows for its key: the
//! quantity sum and count, the exact AVG with the framework's `num_div_exec` (outside its domain: the part row is
//! reported, `Err(j)`, so the statement's answer is `Capacity`), then the SUM of l_extendedprice over the rows with
//! `5 * quantity * 10^(r - 2) < q` (`num_cmp_exec`), which is `quantity < 0.2 * AVG` for the AVG `q` at scale `r`.
//! Spec values are over the stored-order value rows `bind::srows`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::fns::div::*;
use crate::link::join::*;
use crate::link::expr::ival;
use crate::exec::value::*;
use crate::exec::numeric::num_cmp_exec;
use crate::exec::fns::div::num_div_exec;
use crate::gendb_entry::layout::PartView;
use crate::stores::li_pkqty::interface as LI;
use crate::stores::custpart::interface as CPI;
use crate::stores::custpart::interface::common::colfmt as CF;
use crate::stores::custpart::interface::common::read::lemma_div_lt;
use crate::bridge::fns::div::lemma_div_scale_range;
use super::vals::*;
use super::bind::*;
use super::lookup::lemma_lt_threshold;
use super::sqlsub::lemma_avg_range;
use super::scan::{PaCols, pa_cols_ok, mass_max, lemma_sum_of_split};

verus! {

/// The lineitem extents of the general path (whole parts, no directory).
#[derive(Clone, Copy)]
pub struct LiBase {
    pub n: usize,
    pub bs: u64,
    pub kc: &'static [u32],
    pub kb: &'static [i64],
    pub qc: &'static [u16],
    pub qb: &'static [i64],
    pub xc: &'static [u32],
    pub xb: &'static [i64],
}

pub open spec fn li_base_ok(c: LiBase, lp: Seq<PartView>) -> bool {
    &&& li_facts(lp)
    &&& c.n == n_li(lp)
    &&& c.bs == LI::bsize(lp)
    &&& c.kc@ == LI::u32s(lp[LI::LI_PARTKEY_CODES as int])
    &&& c.kb@ == LI::i64s(lp[LI::LI_PARTKEY_BASE as int])
    &&& c.qc@ == LI::u16s(lp[LI::LI_QUANTITY_CODES as int])
    &&& c.qb@ == LI::i64s(lp[LI::LI_QUANTITY_BASE as int])
    &&& c.xc@ == LI::u32s(lp[LI::LI_EXTENDEDPRICE_CODES as int])
    &&& c.xb@ == LI::i64s(lp[LI::LI_EXTENDEDPRICE_BASE as int])
}

/// Per part value row: the kept SUM, count and mass over the stored-order lineitem value rows.
pub open spec fn gsum(lp: Seq<PartView>, b: Seq<u8>, c: Seq<u8>) -> spec_fn(Row) -> int {
    |z: Row| psum(srows(lp), b, c, z)
}

pub open spec fn gcnt(lp: Seq<PartView>, b: Seq<u8>, c: Seq<u8>) -> spec_fn(Row) -> int {
    |z: Row| pcnt(srows(lp), b, c, z)
}

pub open spec fn gmass(lp: Seq<PartView>, b: Seq<u8>, c: Seq<u8>) -> spec_fn(Row) -> int {
    |z: Row| pmass(srows(lp), b, c, z)
}

/// The stored-order value rows are typed.
pub proof fn lemma_srows_ok(lp: Seq<PartView>)
    requires li_facts(lp),
    ensures ys_ok(srows(lp)),
{
    let ys = srows(lp);
    assert forall|i: int| 0 <= i < ys.len() implies y_ok(#[trigger] ys[i]) by {
        assert(ys[i] == srow(lp, i));
    }
}

/// The key of stored row `s` (in `i128`, so no overflow).
fn key_of(c: &LiBase, s: usize, Ghost(lp): Ghost<Seq<PartView>>) -> (k: i128)
    requires li_base_ok(*c, lp), s < c.n,
    ensures k == LI::key_at(lp, s as int),
{
    proof {
        lemma_div_lt(s as int, c.bs as int, c.kb@.len() as int);
    }
    c.kb[(s as u64 / c.bs) as usize] as i128 + c.kc[s] as i128
}

fn qty_of_b(c: &LiBase, s: usize, Ghost(lp): Ghost<Seq<PartView>>) -> (q: i64)
    requires li_base_ok(*c, lp), s < c.n,
    ensures q as int == LI::qty_at(lp, s as int), -p15() < q < p15(),
{
    proof {
        lemma_div_lt(s as int, c.bs as int, c.qb@.len() as int);
        assert(y_ok(srow(lp, s as int)));
    }
    c.qb[(s as u64 / c.bs) as usize] + c.qc[s] as i64
}

fn price_of_b(c: &LiBase, s: usize, Ghost(lp): Ghost<Seq<PartView>>) -> (x: i64)
    requires li_base_ok(*c, lp), s < c.n,
    ensures x as int == LI::price_at(lp, s as int), -p15() < x < p15(),
{
    proof {
        lemma_div_lt(s as int, c.bs as int, c.xb@.len() as int);
        assert(y_ok(srow(lp, s as int)));
    }
    c.xb[(s as u64 / c.bs) as usize] + c.xc[s] as i64
}

/// The general comparison: `5 q * 10^(r - 2) < a` is `q < 0.2 * AVG` for the AVG `a` at scale `r >= 2`.
proof fn lemma_cmp_fifth(qv: int, a: int, r: nat)
    requires r >= 2,
    ensures
        (num_cmp(5 * qv, 2, a, r) < 0) == lt_true(Val::Num { coeff: qv, scale: 2 }, Val::Num { coeff: 2 * a, scale: r + 1 }),
{
    lemma_lt_threshold(qv, a, r);
    let p = pow10((r - 2) as nat);
    assert(pow10((r - 1) as nat) == 10 * p);
    assert(max_nat(2, r) == r);
    assert(pow10(0) == 1);
    assert(align(a, r, r) == a);
    assert(align(5 * qv, 2, r) == 5 * qv * p);
    assert((qv * (10 * p) < 2 * a) == (5 * qv * p < a)) by (nonlinear_arith);
}

/// No row of key `k` when their count is 0.
proof fn lemma_cnt_zero(rows: Seq<Row>, k: int)
    requires sum_of(rows, t1(k)) == 0,
    ensures forall|i: int| 0 <= i < rows.len() ==> !is_key(#[trigger] rows[i], k),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let d = rows.drop_last();
        lemma_sum_of_nonneg(d, t1(k));
        lemma_cnt_zero(d, k);
        assert forall|i: int| 0 <= i < rows.len() implies !is_key(#[trigger] rows[i], k) by {
            if i < d.len() {
                assert(rows[i] == d[i]);
            }
        }
    }
}

/// The quantity sum and count of key `k` over all stored rows.
fn scan_qsum(c: &LiBase, k: i64, Ghost(lp): Ghost<Seq<PartView>>) -> (r: (i128, usize))
    requires li_base_ok(*c, lp),
    ensures
        r.0 == qsum(srows(lp), k as int),
        r.1 == qcnt(srows(lp), k as int),
{
    let ghost ys = srows(lp);
    let mut sq: i128 = 0;
    let mut cnt: usize = 0;
    let mut s: usize = 0;
    while s < c.n
        invariant
            li_base_ok(*c, lp),
            ys == srows(lp),
            s <= c.n,
            c.n <= 0xffff_ffff_ffff_ffff,
            sq == sum_of(ys.subrange(0, s as int), tq(k as int)),
            cnt == sum_of(ys.subrange(0, s as int), t1(k as int)),
            cnt <= s,
            -s * p15() <= sq <= s * p15(),
        decreases c.n - s,
    {
        let key = key_of(c, s, Ghost(lp));
        proof {
            assert(ys[s as int] == srow(lp, s as int));
            lemma_sum_of_sub_push(ys, tq(k as int), 0, s as int);
            lemma_sum_of_sub_push(ys, t1(k as int), 0, s as int);
            assert(-(s + 1) * p15() == -s * p15() - p15()) by (nonlinear_arith);
            assert((s + 1) * p15() == s * p15() + p15()) by (nonlinear_arith);
            assert(s * p15() <= 0xffff_ffff_ffff_ffff * p15()) by (nonlinear_arith) requires s <= 0xffff_ffff_ffff_ffff;
        }
        if key == k as i128 {
            let q = qty_of_b(c, s, Ghost(lp));
            sq = sq + q as i128;
            cnt = cnt + 1;
        }
        s = s + 1;
    }
    proof {
        assert(ys.subrange(0, c.n as int) =~= ys);
    }
    (sq, cnt)
}

/// One matching part row of key `k` (value row `z`): its kept SUM and whether a row is kept, or `Err` when its AVG
/// is outside the executable division domain.
pub fn general_part(c: &LiBase, k: i64, Ghost(lp): Ghost<Seq<PartView>>, Ghost(b): Ghost<Seq<u8>>,
    Ghost(cc): Ghost<Seq<u8>>, Ghost(z): Ghost<Row>) -> (r: Result<(i128, bool), ()>)
    requires
        li_base_ok(*c, lp),
        z == seq![Val::Int(k as int), Val::Text(b), Val::Text(cc)],
    ensures
        r matches Ok((s, any)) ==> s == psum(srows(lp), b, cc, z) && any == (pcnt(srows(lp), b, cc, z) > 0),
        r is Err ==> qcnt(srows(lp), k as int) >= 1
            && !num_div_fits(qsum(srows(lp), k as int), 2, qcnt(srows(lp), k as int), 0),
{
    let ghost ys = srows(lp);
    let ghost ki = k as int;
    proof {
        lemma_srows_ok(lp);
        lemma_qsum_bound(ys, ki);
    }
    let (sq, cnt) = scan_qsum(c, k, Ghost(lp));
    if cnt == 0 {
        proof {
            lemma_cnt_zero(ys, ki);
            assert forall|i: int| 0 <= i < ys.len() implies tsum(ys, b, cc, z)(#[trigger] ys[i]) == 0
                && tcnt(ys, b, cc, z)(ys[i]) == 0 by {
                assert(!is_key(ys[i], ki));
            }
            lemma_sum_of_zero(ys, tsum(ys, b, cc, z));
            lemma_sum_of_zero(ys, tcnt(ys, b, cc, z));
        }
        return Ok((0, false));
    }
    let avg = num_div_exec(sq, 2, cnt as i128, 0);
    proof {
        lemma_avg_range(sq as int, cnt as int);
    }
    let (q, r) = match avg {
        Err(_) => return Err(()),
        Ok(Err(_)) => {
            proof {
                assert(false);
            }
            return Err(());
        },
        Ok(Ok(v)) => match v {
            EVal::Num { coeff, scale } => (coeff, scale),
            _ => {
                proof {
                    assert(false);
                }
                return Err(());
            },
        },
    };
    proof {
        lemma_div_scale_range(sq as int, 2, cnt as int, 0);
        assert(sub_val(ys, ki) == (Val::Num { coeff: 2 * q, scale: (r + 1) as nat }));
    }
    let mut acc: i128 = 0;
    let mut any = false;
    let mut s: usize = 0;
    while s < c.n
        invariant
            li_base_ok(*c, lp),
            ys == srows(lp),
            ki == k as int,
            z == seq![Val::Int(ki), Val::Text(b), Val::Text(cc)],
            sub_val(ys, ki) == (Val::Num { coeff: 2 * q, scale: (r + 1) as nat }),
            2 <= r <= 1000,
            s <= c.n,
            c.n <= 0xffff_ffff_ffff_ffff,
            acc == sum_of(ys.subrange(0, s as int), tsum(ys, b, cc, z)),
            any == (sum_of(ys.subrange(0, s as int), tcnt(ys, b, cc, z)) > 0),
            sum_of(ys.subrange(0, s as int), tcnt(ys, b, cc, z)) >= 0,
            -s * p15() <= acc <= s * p15(),
        decreases c.n - s,
    {
        let key = key_of(c, s, Ghost(lp));
        let qv = qty_of_b(c, s, Ghost(lp));
        proof {
            let y = ys[s as int];
            assert(y == srow(lp, s as int));
            assert(y[0] == Val::Int(key as int));
            assert(y[1] == (Val::Num { coeff: qv as int, scale: 2 }));
            lemma_cmp_fifth(qv as int, q as int, r as nat);
            assert(kept(ys, b, cc, y, z) == (key == ki
                && lt_true(Val::Num { coeff: qv as int, scale: 2 }, Val::Num { coeff: 2 * q, scale: (r + 1) as nat })));
            lemma_sum_of_sub_push(ys, tsum(ys, b, cc, z), 0, s as int);
            lemma_sum_of_sub_push(ys, tcnt(ys, b, cc, z), 0, s as int);
            assert(-(s + 1) * p15() == -s * p15() - p15()) by (nonlinear_arith);
            assert((s + 1) * p15() == s * p15() + p15()) by (nonlinear_arith);
            assert(s * p15() <= 0xffff_ffff_ffff_ffff * p15()) by (nonlinear_arith) requires s <= 0xffff_ffff_ffff_ffff;
        }
        let mut cond = false;
        if key == k as i128 {
            let q5: i128 = 5 * (qv as i128);
            let cmp = num_cmp_exec(q5, 2, q, r);
            proof {
                assert(q5 as int == 5 * qv);
                assert(cmp as int == num_cmp(5 * qv, 2, q as int, r as nat));
            }
            cond = cmp < 0;
            proof {
                assert(cond == (num_cmp(5 * qv, 2, q as int, r as nat) < 0));
            }
        }
        proof {
            assert(key == ki ==> (cond == (num_cmp(5 * qv, 2, q as int, r as nat) < 0)));
            assert(key != ki ==> !cond);
        }
        proof {
            let y = ys[s as int];
            assert(z[0] == Val::Int(ki) && z[1] == Val::Text(b) && z[2] == Val::Text(cc));
            assert((z[0] == y[0]) == (key == ki));
            assert(ival(z[0]) == ki);
            assert(sub_val(ys, ival(z[0])) == (Val::Num { coeff: 2 * q, scale: (r + 1) as nat }));
            assert(y[1] == (Val::Num { coeff: qv as int, scale: 2 }));
            assert(lt_true(y[1], sub_val(ys, ival(z[0]))) == lt_true(Val::Num { coeff: qv as int, scale: 2 }, Val::Num { coeff: 2 * q, scale: (r + 1) as nat }));
            assert(key == ki ==> (cond == (num_cmp(5 * qv, 2, q as int, r as nat) < 0)));
            assert(cond == kept(ys, b, cc, y, z));
            assert(tsum(ys, b, cc, z)(y) == if cond { LI::price_at(lp, s as int) } else { 0 });
            assert(tcnt(ys, b, cc, z)(y) == if cond { 1int } else { 0 });
        }
        if cond {
            let xv = price_of_b(c, s, Ghost(lp));
            acc = acc + xv as i128;
            any = true;
        }
        s = s + 1;
    }
    proof {
        assert(ys.subrange(0, c.n as int) =~= ys);
    }
    Ok((acc, any))
}

/// The general totals over every part row: the SUM and whether a row is kept, or `Err(j)` for a part row `j`
/// whose AVG is outside the executable division domain.
pub fn general_all(li: &LiBase, pa: &PaCols, tb: u64, tc: u64, Ghost(lp): Ghost<Seq<PartView>>,
    Ghost(cp): Ghost<Seq<PartView>>, Ghost(b): Ghost<Seq<u8>>, Ghost(c): Ghost<Seq<u8>>) -> (r: Result<(i128, bool), usize>)
    requires
        li_base_ok(*li, lp),
        pa_cols_ok(*pa, cp),
        0 <= tb < n_bd(cp) && CF::text_of(bd_o(cp), bd_y(cp), tb as int) == b,
        0 <= tc < n_cd(cp) && CF::text_of(cd_o(cp), cd_y(cp), tc as int) == c,
        sum_of(zrows(cp), gmass(lp, b, c)) <= mass_max(),
    ensures
        r matches Ok((s, any)) ==> s == sum_of(zrows(cp), gsum(lp, b, c)) && any == (sum_of(zrows(cp), gcnt(lp, b, c)) > 0),
        r matches Err(j) ==> j < n_pa(cp) && qcnt(srows(lp), pkey_at(cp, j as int)) >= 1
            && !num_div_fits(qsum(srows(lp), pkey_at(cp, j as int)), 2, qcnt(srows(lp), pkey_at(cp, j as int)), 0),
{
    let ghost zs = zrows(cp);
    let ghost ys = srows(lp);
    let mut acc: i128 = 0;
    let mut any = false;
    let mut j: usize = 0;
    proof {
        assert(zs.subrange(0, 0) =~= Seq::<Row>::empty());
        lemma_srows_ok(lp);
        assert forall|i: int| 0 <= i < zs.len() implies gmass(lp, b, c)(#[trigger] zs[i]) >= 0 by {
            lemma_part_sums(ys, b, c, zs[i]);
        }
    }
    while j < pa.n
        invariant
            li_base_ok(*li, lp),
            pa_cols_ok(*pa, cp),
            0 <= tb < n_bd(cp) && CF::text_of(bd_o(cp), bd_y(cp), tb as int) == b,
            0 <= tc < n_cd(cp) && CF::text_of(cd_o(cp), cd_y(cp), tc as int) == c,
            sum_of(zrows(cp), gmass(lp, b, c)) <= mass_max(),
            zs == zrows(cp),
            ys == srows(lp),
            ys_ok(ys),
            forall|i: int| 0 <= i < zs.len() ==> gmass(lp, b, c)(#[trigger] zs[i]) >= 0,
            j <= pa.n,
            acc == sum_of(zs.subrange(0, j as int), gsum(lp, b, c)),
            any == (sum_of(zs.subrange(0, j as int), gcnt(lp, b, c)) > 0),
            sum_of(zs.subrange(0, j as int), gcnt(lp, b, c)) >= 0,
            -sum_of(zs.subrange(0, j as int), gmass(lp, b, c)) <= acc <= sum_of(zs.subrange(0, j as int), gmass(lp, b, c)),
        decreases pa.n - j,
    {
        proof {
            lemma_div_lt(j as int, pa.bs as int, pa.brb@.len() as int);
            lemma_div_lt(j as int, pa.bs as int, pa.ctb@.len() as int);
            lemma_div_lt(j as int, pa.bs as int, pa.pkb@.len() as int);
            assert(zs[j as int] == zrow(cp, j as int));
            lemma_part_sums(ys, b, c, zs[j as int]);
            lemma_sum_of_sub_push(zs, gsum(lp, b, c), 0, j as int);
            lemma_sum_of_sub_push(zs, gcnt(lp, b, c), 0, j as int);
            lemma_sum_of_sub_push(zs, gmass(lp, b, c), 0, j as int);
            lemma_sum_of_sub_le(zs, gmass(lp, b, c), 0, j + 1);
        }
        let jb = (j as u64 / pa.bs) as usize;
        let bi = pa.brb[jb] as u128 + pa.br[j] as u128;
        let ci = pa.ctb[jb] as u128 + pa.ct[j] as u128;
        let ghost z = zrow(cp, j as int);
        if bi == tb as u128 && ci == tc as u128 {
            proof {
                assert(z =~= seq![Val::Int(pkey_at(cp, j as int)), Val::Text(b), Val::Text(c)]);
            }
            let k = pa.pkb[jb] + pa.pk[j] as i64;
            match general_part(li, k, Ghost(lp), Ghost(b), Ghost(c), Ghost(z)) {
                Err(_) => return Err(j),
                Ok((s, a)) => {
                    acc = acc + s;
                    any = any || a;
                },
            }
        } else {
            proof {
                if bidx_at(cp, j as int) != tb {
                    CF::lemma_dict_distinct(bd_o(cp), bd_y(cp), n_bd(cp), bidx_at(cp, j as int), tb as int);
                    assert(z[1] != Val::Text(b));
                } else {
                    CF::lemma_dict_distinct(cd_o(cp), cd_y(cp), n_cd(cp), cidx_at(cp, j as int), tc as int);
                    assert(z[2] != Val::Text(c));
                }
                assert forall|i: int| 0 <= i < ys.len() implies !kept(ys, b, c, #[trigger] ys[i], z) by {}
                lemma_sum_of_zero(ys, tsum(ys, b, c, z));
                lemma_sum_of_zero(ys, tcnt(ys, b, c, z));
            }
        }
        j = j + 1;
    }
    proof {
        assert(zs.subrange(0, pa.n as int) =~= zs);
    }
    Ok((acc, any))
}

} // verus!
