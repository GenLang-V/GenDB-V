//! The general path (serial): for every order dated in the window, its returned lineitems' sums (by its lineitem
//! run when the layout is co-clustered, else by a scan of every lineitem row), added into per-customer
//! accumulators in `i128` (revenue) and `u128` (absolute revenue, the SUM capacity condition); then the top 20 of
//! the groups. A group whose absolute revenue leaves `i128` is reported (the Capacity answer).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::link::expr::i128_max;
use crate::gendb_entry::work::{put, filled};
use super::common::isum::*;
use super::common::topk::*;
use super::model::*;
use super::qspec::*;
use super::kernel::*;
use super::recs::*;
use super::cand::*;
use super::plan::*;
use super::phase1::{lemma_labs_lsum, lemma_lcnt_zero};
use super::phase2::lemma_gseq_wf_range;

verus! {

/// A run's result: the top-20 buffer of every group, or (`ovf`) a group whose revenue mass leaves `i128`.
pub struct RunOut {
    pub buf: Vec<Cand>,
    pub len: usize,
    pub ovf: bool,
    pub ovf_c: usize,
}

pub open spec fn run_ok(m: M, p: QP, r: RunOut) -> bool {
    &&& r.buf@.len() == K
    &&& r.len <= K
    &&& r.ovf ==> 0 <= r.ovf_c < m.c_n && good(m, p, r.ovf_c as int) && cabs(m, p, r.ovf_c as int) > i128_max()
    &&& !r.ovf ==> {
        &&& topk_ok(q10_keys(), q10_fams(), K as nat, cands_view(m, r.buf@, r.len as int), gseq(m, p, 0, m.c_n))
        &&& cands_good(m, p, r.buf@, r.len as int)
        &&& caps_ok(m, p)
    }
}

/// The sums of the order at `q`: by its lineitem run (co-clustered layout, two binary searches) or by a scan.
fn order_sums(c: &Cols, q: usize, okv: i64, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: (u64, i128, u128, bool))
    requires cols_ok(*c, m, p), model_ok(m), q < m.o_n, okv == okey(m, q as int),
    ensures sums_ok(m, q as int, r.0, r.1, r.2, r.3),
{
    if c.cluster == 1 && c.idx_ok {
        let j0 = lb_search(c, q, Ghost(m), Ghost(p));
        let j1 = lb_search(c, q + 1, Ghost(m), Ghost(p));
        if j0 <= j1 {
            let lg64 = (j0 as u64) / c.l_bs;
            proof {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j0 as int, m.l_bs);
                vstd::arithmetic::div_mod::lemma_mod_pos_bound(j0 as int, m.l_bs);
                assert(m.l_bs * lg64 == lg64 * m.l_bs) by (nonlinear_arith);
                assert((lg64 + 1) * m.l_bs == lg64 * m.l_bs + m.l_bs) by (nonlinear_arith);
                assert(lg64 <= j0) by (nonlinear_arith) requires lg64 * m.l_bs <= j0, m.l_bs >= 1, lg64 >= 0;
                assert forall|t: int| j1 <= t < m.l_n implies #[trigger] lpos(m, t) > q by {}
            }
            let r = fast_sums(c, okv, j0, j1, lg64 as usize, (lg64 + 1) * c.l_bs, Ghost(m), Ghost(p), Ghost(q as int));
            return (r.0, r.1, r.2, r.3);
        }
    }
    scan_sums(c, okv, Ghost(m), Ghost(p), Ghost(q as int))
}

/// Customer `c`'s accumulators after the orders `[0, q)`.
pub open spec fn gen_at(m: M, p: QP, q: int, gsum: Seq<i128>, gab: Seq<u128>, gflag: Seq<u8>, govf: Seq<u8>, c: int) -> bool {
    &&& (gflag[c] != 0) == (isum(q, chit_f(m, p, c)) > 0)
    &&& govf[c] != 0 ==> isum(q, cabs_f(m, p, c)) > i128_max()
    &&& govf[c] == 0 ==> gab[c] as int == isum(q, cabs_f(m, p, c)) && gab[c] as int <= i128_max()
        && gsum[c] as int == isum(q, csum_f(m, p, c)) && abs(gsum[c] as int) <= gab[c] as int
}

/// The per-customer accumulators after the orders `[0, q)`.
pub open spec fn gen_inv(m: M, p: QP, q: int, gsum: Seq<i128>, gab: Seq<u128>, gflag: Seq<u8>, govf: Seq<u8>) -> bool {
    &&& gsum.len() == m.c_n && gab.len() == m.c_n && gflag.len() == m.c_n && govf.len() == m.c_n
    &&& forall|c: int| 0 <= c < m.c_n ==> #[trigger] gen_at(m, p, q, gsum, gab, gflag, govf, c)
}

/// The terms of order `q` for customer `c`.
proof fn lemma_order_terms(m: M, p: QP, c: int, q: int)
    requires model_ok(m), 0 <= q < m.o_n,
    ensures
        isum(q + 1, chit_f(m, p, c)) == isum(q, chit_f(m, p, c)) + chit_f(m, p, c)(q),
        isum(q + 1, cabs_f(m, p, c)) == isum(q, cabs_f(m, p, c)) + cabs_f(m, p, c)(q),
        isum(q + 1, csum_f(m, p, c)) == isum(q, csum_f(m, p, c)) + csum_f(m, p, c)(q),
        isum(q, chit_f(m, p, c)) >= 0,
        isum(q, cabs_f(m, p, c)) >= 0,
        cabs_f(m, p, c)(q) >= 0,
        abs(csum_f(m, p, c)(q)) <= cabs_f(m, p, c)(q),
{
    lemma_isum_step(q, chit_f(m, p, c));
    lemma_isum_step(q, cabs_f(m, p, c));
    lemma_isum_step(q, csum_f(m, p, c));
    assert forall|t: int| 0 <= t < q implies #[trigger] chit_f(m, p, c)(t) >= 0 by {}
    lemma_isum_nonneg(0, q, chit_f(m, p, c));
    assert forall|t: int| 0 <= t < q implies #[trigger] cabs_f(m, p, c)(t) >= 0 by {
        lemma_labs_lsum(m, t);
    }
    lemma_isum_nonneg(0, q, cabs_f(m, p, c));
    lemma_labs_lsum(m, q);
}

/// An order counted for no customer leaves the accumulators unchanged.
proof fn lemma_gen_skip(m: M, p: QP, q: int, gsum: Seq<i128>, gab: Seq<u128>, gflag: Seq<u8>, govf: Seq<u8>)
    requires
        model_ok(m),
        0 <= q < m.o_n,
        gen_inv(m, p, q, gsum, gab, gflag, govf),
        forall|c: int| 0 <= c < m.c_n ==> !(#[trigger] ohit(m, p, c, q)) || lcnt(m, q) <= 0,
    ensures gen_inv(m, p, q + 1, gsum, gab, gflag, govf),
{
    assert forall|c: int| 0 <= c < m.c_n implies #[trigger] gen_at(m, p, q + 1, gsum, gab, gflag, govf, c) by {
        assert(gen_at(m, p, q, gsum, gab, gflag, govf, c));
        lemma_order_terms(m, p, c, q);
        if ohit(m, p, c, q) {
            assert(lcnt(m, q) <= 0);
            lemma_lcnt_zero(m, q);
        }
        assert(chit_f(m, p, c)(q) == 0);
        assert(cabs_f(m, p, c)(q) == 0);
        assert(csum_f(m, p, c)(q) == 0);
        assert((gflag[c] != 0) == (isum(q, chit_f(m, p, c)) > 0));
    }
}

/// Add the order at `q` (customer row `cp`, sums `cnt, sum, ab, ovf`) to the accumulators.
fn gen_add(gsum: &mut Vec<i128>, gab: &mut Vec<u128>, gflag: &mut Vec<u8>, govf: &mut Vec<u8>, cp: usize,
    cnt: u64, sum: i128, ab: u128, ovf: bool, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(q): Ghost<int>)
    requires
        model_ok(m),
        0 <= q < m.o_n,
        cp < m.c_n,
        ohit(m, p, cp as int, q),
        cnt > 0,
        sums_ok(m, q, cnt, sum, ab, ovf),
        gen_inv(m, p, q, old(gsum)@, old(gab)@, old(gflag)@, old(govf)@),
    ensures gen_inv(m, p, q + 1, final(gsum)@, final(gab)@, final(gflag)@, final(govf)@),
{
    let ghost (s0, a0, f0, o0) = (gsum@, gab@, gflag@, govf@);
    proof {
        lemma_order_terms(m, p, cp as int, q);
        assert(gen_at(m, p, q, s0, a0, f0, o0, cp as int));
        assert forall|c: int| 0 <= c < m.c_n && c != cp implies !#[trigger] ohit(m, p, c, q) by {
            assert(ckey(m, c) != ckey(m, cp as int));
        }
    }
    gflag[cp] = 1;
    if govf[cp] == 0 {
        if ovf {
            govf[cp] = 1;
        } else {
            let na = gab[cp] + ab;
            if na > 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffffu128 {
                govf[cp] = 1;
            } else {
                gab[cp] = na;
                gsum[cp] = gsum[cp] + sum;
            }
        }
    }
    proof {
        let (s1, a1, f1, o1) = (gsum@, gab@, gflag@, govf@);
        assert forall|c: int| 0 <= c < m.c_n implies #[trigger] gen_at(m, p, q + 1, s1, a1, f1, o1, c)
        by {
            assert(gen_at(m, p, q, s0, a0, f0, o0, c));
            lemma_order_terms(m, p, c, q);
            if c != cp {
                assert(!ohit(m, p, c, q));
                assert(gflag@[c] == f0[c] && govf@[c] == o0[c] && gab@[c] == a0[c] && gsum@[c] == s0[c]);
            } else {
                assert(chit_f(m, p, c)(q) == 1);
                assert(cabs_f(m, p, c)(q) == labs(m, q));
                assert(csum_f(m, p, c)(q) == lsum(m, q));
                assert(gflag@[c] == 1);
                assert(isum(q + 1, chit_f(m, p, c)) > 0);
                if o0[c] != 0 {
                    assert(isum(q, cabs_f(m, p, c)) > i128_max());
                    assert(govf@[c] != 0);
                } else if ovf {
                    assert(govf@[c] != 0);
                } else {
                    assert(a0[c] as int == isum(q, cabs_f(m, p, c)));
                    if a0[c] as int + ab as int > i128_max() {
                        assert(govf@[c] != 0);
                    } else {
                        assert(gab@[c] as int == a0[c] as int + ab as int);
                        assert(gsum@[c] as int == s0[c] as int + sum as int);
                    }
                }
            }
        }
        assert(s1.len() == m.c_n && a1.len() == m.c_n && f1.len() == m.c_n && o1.len() == m.c_n);
        assert(gen_inv(m, p, q + 1, s1, a1, f1, o1));
    }
}

/// The general path.
pub fn run_general(c: &Cols, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: RunOut)
    requires cols_ok(*c, m, p), model_ok(m),
    ensures run_ok(m, p, r),
{
    let n = c.c_n;
    let mut gsum: Vec<i128> = vec![0i128; n];
    let mut gab: Vec<u128> = vec![0u128; n];
    let mut gflag: Vec<u8> = vec![0u8; n];
    let mut govf: Vec<u8> = vec![0u8; n];
    proof {
        assert forall|cc: int| 0 <= cc < m.c_n implies #[trigger] gen_at(m, p, 0, gsum@, gab@, gflag@, govf@, cc) by {
            assert(gflag@[cc] == 0 && govf@[cc] == 0 && gab@[cc] == 0 && gsum@[cc] == 0);
        }
    }
    let mut q: usize = 0;
    while q < c.o_n
        invariant
            cols_ok(*c, m, p), model_ok(m), n == m.c_n,
            q <= m.o_n,
            gen_inv(m, p, q as int, gsum@, gab@, gflag@, govf@),
        decreases m.o_n - q,
    {
        let og = ((q as u64) / c.o_bs) as usize;
        proof { lemma_block_bound(q as int, m.o_bs, m.o_n, m.o_nb); }
        let (okv, ocv, odv) = order_at(c, q, og, Ghost(m), Ghost(p));
        let mut added = false;
        if odv >= c.lo && odv <= c.hi {
            let (cnt, sum, ab, ovf) = order_sums(c, q, okv, Ghost(m), Ghost(p));
            if cnt > 0 {
                match cust_find(c, ocv, Ghost(m), Ghost(p)) {
                    Some(cp) => {
                        gen_add(&mut gsum, &mut gab, &mut gflag, &mut govf, cp, cnt, sum, ab, ovf, Ghost(m), Ghost(p), Ghost(q as int));
                        added = true;
                    },
                    None => {},
                }
            }
        }
        if !added {
            proof {
                lemma_gen_skip(m, p, q as int, gsum@, gab@, gflag@, govf@);
            }
        }
        q = q + 1;
    }
    // the top 20 of the groups, or a group outside the capacity condition
    let mut buf: Vec<Cand> = filled(K, Cand { cpos: 0, rev: 0 });
    let mut len: usize = 0;
    let mut cc: usize = 0;
    proof {
        lemma_topk_empty(q10_keys(), q10_fams(), K as nat);
        lemma_gseq_empty(m, p, 0);
        assert(cands_view(m, buf@, 0) =~= Seq::<Row>::empty());
    }
    while cc < n
        invariant
            cols_ok(*c, m, p), model_ok(m), n == m.c_n,
            cc <= n,
            gen_inv(m, p, m.o_n, gsum@, gab@, gflag@, govf@),
            buf@.len() == K,
            len <= K,
            topk_ok(q10_keys(), q10_fams(), K as nat, cands_view(m, buf@, len as int), gseq(m, p, 0, cc as int)),
            cands_good(m, p, buf@, len as int),
            forall|x: int| 0 <= x < cc && #[trigger] good(m, p, x) ==> cabs(m, p, x) <= i128_max(),
        decreases n - cc,
    {
        let ghost before = gseq(m, p, 0, cc as int);
        proof {
            lemma_gseq_step(m, p, 0, cc as int);
            lemma_gseq_wf_range(m, p, 0, cc as int + 1);
            lemma_ccnt_pos(m, p, cc as int);
            assert(gen_at(m, p, m.o_n, gsum@, gab@, gflag@, govf@, cc as int));
            assert((gflag@[cc as int] != 0) == (ccnt(m, p, cc as int) > 0));
        }
        if gflag[cc] != 0 {
            match nat_ok_at(c, cc, Ghost(m), Ghost(p)) {
                Some(_) => {
                    assert(good(m, p, cc as int));
                    if govf[cc] != 0 {
                        return RunOut { buf, len, ovf: true, ovf_c: cc };
                    }
                    let rev = gsum[cc];
                    let cand = Cand { cpos: cc, rev };
                    proof {
                        assert(cand_row(m, cand) =~= grow(m, p, cc as int));
                    }
                    if cannot_enter(&buf, len, rev) {
                        proof {
                            lemma_skip_full(m, buf@, len as int, before, cand);
                        }
                    } else {
                        let ghost b0 = buf@;
                        let ghost l0 = len;
                        len = topk_insert(&mut buf, len, cand, Ghost(m), Ghost(before));
                        proof {
                            lemma_cands_good_insert(m, p, b0, l0 as int, buf@, len as int, cand);
                        }
                    }
                },
                None => {},
            }
        }
        cc = cc + 1;
    }
    RunOut { buf, len, ovf: false, ovf_c: 0 }
}

} // verus!
