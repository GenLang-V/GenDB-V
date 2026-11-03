//! The qualifying orders of one batch of order rows `[jb, je)` (`batch_list`): the increasing list `qj[0..nq)` of
//! exactly the order rows whose code is not `NONE`, with their customer rows `qr` (`hlist_ok`; the code of order
//! `qj[p]` is `ccode[qr[p]]`). Three passes over small buffers, each a tight loop whose random reads overlap:
//! 1. per window of 64 orders, the mask of the orders dated in the year is built without branches
//!    (`common::bitscan::range_mask`, vector code) and its set bits are walked in increasing order into `idx`;
//! 2. the customer row of each listed order (`ci`);
//! 3. the bit of that customer in the customer bitmap: the order is written to the list unconditionally and the
//!    list length advanced by the bit (no data-dependent branch).
use vstd::prelude::*;
use crate::gendb_entry::work::put;
use crate::gendb_entry::stores::StoresView;
use crate::agent::model::*;
use crate::agent::sem_pred::*;
use crate::agent::contrib::*;
use crate::agent::rows::*;
use crate::agent::common::lookup::*;
use crate::agent::common::bitmap::*;
use crate::agent::common::bitscan::*;

verus! {

/// Order rows per batch (1024: the four index buffers, 32 KiB, stay in the L1 cache).
pub const BATCH: usize = 1024;

/// `qj[0..nq)` lists, increasing, exactly the order rows of `[jb, je)` with a non-`NONE` code; `qr[p]` is the
/// customer row of `qj[p]`, whose code is the order's code.
pub open spec fn hlist_ok(sh: Shared, x: Ctx, qj: Seq<usize>, qr: Seq<usize>, nq: int, jb: int, je: int) -> bool {
    &&& 0 <= nq <= qj.len()
    &&& nq <= qr.len()
    &&& forall|p: int| 0 <= p < nq ==> jb <= #[trigger] qj[p] < je && qr[p] < nc(x.sv)
        && sh.ccode@[qr[p] as int] == ord_code(x.sv, x.slots, x.pd, x.t, qj[p] as int)
        && ord_code(x.sv, x.slots, x.pd, x.t, qj[p] as int) != NONE
    &&& forall|p: int, p2: int| 0 <= p < p2 < nq ==> #[trigger] qj[p] < #[trigger] qj[p2]
    &&& forall|j: int| jb <= j < je && #[trigger] ord_code(x.sv, x.slots, x.pd, x.t, j) != NONE ==> exists|p: int| 0 <= p < nq && qj[p] == j
}

/// No customer row: the customer of an order without a customer.
pub const NO_ROW: usize = usize::MAX;

/// `c` is the customer row of order row `j` (`NO_ROW` when no customer has its key).
pub open spec fn cust_of(sv: StoresView, j: int, c: usize) -> bool {
    &&& c != NO_ROW ==> c < nc(sv) && c_ck(sv)[c as int] == o_ck(sv)[j]
    &&& c == NO_ROW ==> !exists|i: int| 0 <= i < nc(sv) && #[trigger] c_ck(sv)[i] == o_ck(sv)[j]
}

/// The code of an order in the year is the code of its customer row, whose bit is set iff that code is not `NONE`.
proof fn lemma_cust_code(sh: Shared, x: Ctx, j: int, c: usize)
    requires shared_ok(sh, x), sh.fast, 0 <= j < no(x.sv), date_in(o_date(x.sv)[j], x.pd, x.t), cust_of(x.sv, j, c),
    ensures
        c != NO_ROW ==> ord_code(x.sv, x.slots, x.pd, x.t, j) == sh.ccode@[c as int]
            && bit_at(sh.bits@, c as int) == (sh.ccode@[c as int] != NONE),
        c == NO_ROW ==> ord_code(x.sv, x.slots, x.pd, x.t, j) == NONE,
{
    let sv = x.sv;
    if c != NO_ROW {
        let i2 = choose|i2: int| 0 <= i2 < nc(sv) && #[trigger] c_ck(sv)[i2] == o_ck(sv)[j];
        assert(c_ck(sv)[i2] == c_ck(sv)[c as int]);
    }
}

/// `idx[0..n)` lists, increasing, exactly the order rows of `[jb, je)` dated in the year.
pub open spec fn dlist_ok(x: Ctx, idx: Seq<usize>, n: int, jb: int, je: int) -> bool {
    &&& 0 <= n <= idx.len()
    &&& forall|p: int| 0 <= p < n ==> jb <= #[trigger] idx[p] < je && date_in(o_date(x.sv)[idx[p] as int], x.pd, x.t)
    &&& forall|p: int, p2: int| 0 <= p < p2 < n ==> #[trigger] idx[p] < #[trigger] idx[p2]
    &&& forall|j: int| jb <= j < je && #[trigger] date_in(o_date(x.sv)[j], x.pd, x.t) ==> exists|p: int| 0 <= p < n && idx[p] == j
}

/// One window of up to 64 order rows from `base` (`wend` its end): walks the set bits of its date mask and appends
/// the rows to `idx` from position `n`; returns the new length.
fn window_dates(sh: &Shared, jb: usize, base: usize, wend: usize, idx: &mut Vec<usize>, n: usize, Ghost(x): Ghost<Ctx>) -> (n2: usize)
    requires
        shared_ok(*sh, x), jb <= base < wend <= sh.c.no, wend - base <= 64, wend - jb <= BATCH,
        old(idx)@.len() == BATCH, n <= base - jb,
        dlist_ok(x, old(idx)@, n as int, jb as int, base as int),
    ensures
        final(idx)@.len() == BATCH, n2 <= wend - jb,
        dlist_ok(x, final(idx)@, n2 as int, jb as int, wend as int),
    no_unwind
{
    let ghost sv = x.sv;
    let odate = sh.c.odate;
    assert(odate@ == o_date(sv) && odate@.len() == sh.c.no);
    let mask = if wend - base < 64 {
        range_mask_part(odate, base, wend - base, sh.dlo, sh.dhi)
    } else {
        range_mask(odate, base, sh.dlo, sh.dhi)
    };
    proof {
        // A set bit is an order of the window dated in the year.
        assert forall|p: int| 0 <= p < 64 implies #[trigger] wbit(mask, p) == (base + p < wend && date_in(o_date(sv)[base + p], x.pd, x.t)) by {
            if base + p < wend {
                assert(date_in(odate@[base + p], x.pd, x.t) == (sh.dlo <= odate@[base + p] < sh.dhi));
            }
        }
    }
    let mut m = mask;
    let mut n = n;
    let ghost mut done: int = 0;
    while m != 0
        invariant
            shared_ok(*sh, x), sv == x.sv, jb <= base < wend <= sh.c.no, wend - base <= 64, wend - jb <= BATCH,
            idx@.len() == BATCH,
            0 <= done <= wend - base,
            n <= base + done - jb,
            forall|p: int| 0 <= p < 64 ==> #[trigger] wbit(mask, p) == (base + p < wend && date_in(o_date(sv)[base + p], x.pd, x.t)),
            forall|c: u64| c < 64 ==> #[trigger] wbit(m, c as int) == (c >= done && wbit(mask, c as int)),
            dlist_ok(x, idx@, n as int, jb as int, base + done),
        decreases m,
    {
        let pb = lowest_bit(m);
        proof { lemma_clear_lowest(m, pb); }
        let p = pb as usize;
        let ghost m0 = m;
        m = m & (m - 1);
        let j = base + p;
        proof {
            assert(wbit(m0, p as int));
            assert(p >= done) by { if p < done { assert(!wbit(m0, (p as u64) as int)); } }
            assert(wbit(mask, (p as u64) as int));
            assert(j < wend);
            // The bits between the last one walked and `p` are clear in the mask.
            assert forall|c: int| done <= c < p implies !#[trigger] wbit(mask, c) by {
                assert(!wbit(m0, (c as u64) as int));
            }
        }
        let ghost i0 = idx@;
        put(idx, n, j);
        proof {
            let lim = base + done;
            assert forall|y: int| 0 <= y < n implies #[trigger] idx@[y] == i0[y] by {}
            assert forall|y: int| 0 <= y < n + 1 implies jb <= #[trigger] idx@[y] < j + 1
                && date_in(o_date(sv)[idx@[y] as int], x.pd, x.t) by {
                if y < n { assert(i0[y] < lim); }
            }
            assert forall|y: int, y2: int| 0 <= y < y2 < n + 1 implies #[trigger] idx@[y] < #[trigger] idx@[y2] by {
                if y2 < n { assert(i0[y] < i0[y2]); } else { assert(i0[y] < lim); }
            }
            assert forall|jj: int| jb <= jj < j + 1 && #[trigger] date_in(o_date(sv)[jj], x.pd, x.t)
                implies exists|y: int| 0 <= y < n + 1 && idx@[y] == jj by {
                if jj < lim {
                    let y = choose|y: int| 0 <= y < n && i0[y] == jj;
                    assert(idx@[y] == i0[y]);
                } else if jj < j {
                    // A row between the last walked bit and `p` is not dated in the year.
                    assert(!wbit(mask, jj - base));
                } else {
                    assert(idx@[n as int] == j);
                }
            }
            assert forall|c: u64| c < 64 implies #[trigger] wbit(m, c as int) == (c >= p + 1 && wbit(mask, c as int)) by {
                assert(wbit(m, c as int) == (c != p as u64 && wbit(m0, c as int)));
            }
            done = p + 1;
        }
        n = n + 1;
    }
    proof {
        assert forall|jj: int| jb <= jj < wend && #[trigger] date_in(o_date(sv)[jj], x.pd, x.t)
            implies exists|y: int| 0 <= y < n && idx@[y] == jj by {
            if jj >= base + done {
                // Every bit from `done` on is clear in `m == 0`.
                lemma_zero_bits();
                assert(!wbit(m, ((jj - base) as u64) as int));
                assert(wbit(mask, jj - base));
            }
        }
    }
    n
}

/// The customer row of order row `j` (`NO_ROW` when there is none).
fn cust_row(sh: &Shared, j: usize, Ghost(x): Ghost<Ctx>) -> (cr: usize)
    requires shared_ok(*sh, x), j < sh.c.no,
    ensures cust_of(x.sv, j as int, cr),
    no_unwind
{
    let c = &sh.c;
    let k = c.ock[j];
    let found = if sh.ck.ok { dense_pos(&sh.ck, k, Ghost(c_ck(x.sv))) } else { find_dense(c.ckeys, c.nc, sh.cdense, k) };
    let cr = match found {
        Some(i) => i,
        None => NO_ROW,
    };
    proof {
        if cr == NO_ROW {
            assert(!exists|i: int| 0 <= i < nc(x.sv) && #[trigger] c_ck(x.sv)[i] == o_ck(x.sv)[j as int]) by {
                assert forall|i: int| 0 <= i < nc(x.sv) implies #[trigger] c_ck(x.sv)[i] != o_ck(x.sv)[j as int] by {
                    assert(c.ckeys@[i] != c.ock@[j as int]);
                }
            }
        }
    }
    cr
}

/// Whether the order (dated in the year) whose customer row is `cr` has a code: the customer's bit.
fn cust_bit(sh: &Shared, cr: usize, Ghost(x): Ghost<Ctx>, Ghost(j): Ghost<int>) -> (hit: bool)
    requires shared_ok(*sh, x), sh.fast, 0 <= j < no(x.sv), date_in(o_date(x.sv)[j], x.pd, x.t), cust_of(x.sv, j, cr),
    ensures
        hit == (ord_code(x.sv, x.slots, x.pd, x.t, j) != NONE),
        hit ==> cr < nc(x.sv) && sh.ccode@[cr as int] == ord_code(x.sv, x.slots, x.pd, x.t, j),
    no_unwind
{
    let w = if cr != NO_ROW {
        proof { vstd::arithmetic::div_mod::lemma_fundamental_div_mod(cr as int, 64); }
        sh.bits[cr / 64]
    } else {
        0u64
    };
    let sh_amt = (cr % 64) as u64;
    let hit = (w >> sh_amt) & 1u64 == 1u64;
    proof {
        lemma_cust_code(*sh, x, j, cr);
        if cr == NO_ROW {
            assert((0u64 >> sh_amt) & 1u64 == 0u64) by (bit_vector);
        } else {
            assert(bit_at(sh.bits@, cr as int) == hit);
        }
    }
    hit
}

/// Builds the qualifying-order list of the batch `[jb, je)`.
pub fn batch_list(sh: &Shared, jb: usize, je: usize, idx: &mut Vec<usize>, ci: &mut Vec<usize>, qj: &mut Vec<usize>,
    qr: &mut Vec<usize>, Ghost(x): Ghost<Ctx>) -> (nq: usize)
    requires
        shared_ok(*sh, x), sh.fast, jb <= je <= sh.c.no, je - jb <= BATCH,
        old(idx)@.len() == BATCH, old(ci)@.len() == BATCH, old(qj)@.len() == BATCH, old(qr)@.len() == BATCH,
    ensures
        final(idx)@.len() == BATCH, final(ci)@.len() == BATCH, final(qj)@.len() == BATCH, final(qr)@.len() == BATCH,
        nq <= je - jb,
        hlist_ok(*sh, x, final(qj)@, final(qr)@, nq as int, jb as int, je as int),
    no_unwind
{
    let ghost sv = x.sv;
    // Pass 1: the orders dated in the year.
    let mut n: usize = 0;
    let mut base = jb;
    while base < je
        invariant
            shared_ok(*sh, x), sh.fast, jb <= base <= je <= sh.c.no, je - jb <= BATCH,
            idx@.len() == BATCH, n <= base - jb,
            dlist_ok(x, idx@, n as int, jb as int, base as int),
        decreases je - base,
    {
        let wend = if je - base < 64 { je } else { base + 64 };
        n = window_dates(sh, jb, base, wend, idx, n, Ghost(x));
        base = wend;
    }
    // Pass 2: their customer rows.
    let mut q: usize = 0;
    while q < n
        invariant
            shared_ok(*sh, x), sh.fast, sv == x.sv, jb <= je <= sh.c.no, n <= je - jb, je - jb <= BATCH,
            idx@.len() == BATCH, ci@.len() == BATCH, q <= n,
            dlist_ok(x, idx@, n as int, jb as int, je as int),
            forall|p: int| 0 <= p < q ==> cust_of(sv, idx@[p] as int, #[trigger] ci@[p]),
        decreases n - q,
    {
        assert(jb <= idx@[q as int] < je);
        let cr = cust_row(sh, idx[q], Ghost(x));
        let ghost c0 = ci@;
        put(ci, q, cr);
        proof {
            assert forall|p: int| 0 <= p < q + 1 implies cust_of(sv, idx@[p] as int, #[trigger] ci@[p]) by {
                if p < q { assert(ci@[p] == c0[p]); }
            }
        }
        q = q + 1;
    }
    // Pass 3: the orders whose customer bit is set.
    let mut m: usize = 0;
    q = 0;
    while q < n
        invariant
            shared_ok(*sh, x), sh.fast, sv == x.sv, jb <= je <= sh.c.no, n <= je - jb, je - jb <= BATCH,
            idx@.len() == BATCH, ci@.len() == BATCH, qj@.len() == BATCH, qr@.len() == BATCH, q <= n, m <= q,
            dlist_ok(x, idx@, n as int, jb as int, je as int),
            forall|p: int| 0 <= p < n ==> cust_of(sv, idx@[p] as int, #[trigger] ci@[p]),
            forall|r: int| 0 <= r < m ==> jb <= #[trigger] qj@[r] < je && qr@[r] < nc(sv)
                && sh.ccode@[qr@[r] as int] == ord_code(sv, x.slots, x.pd, x.t, qj@[r] as int)
                && ord_code(sv, x.slots, x.pd, x.t, qj@[r] as int) != NONE,
            forall|r: int, r2: int| 0 <= r < r2 < m ==> #[trigger] qj@[r] < #[trigger] qj@[r2],
            forall|r: int| 0 <= r < m ==> q > 0 && #[trigger] qj@[r] <= idx@[q - 1],
            forall|p: int| 0 <= p < q && ord_code(sv, x.slots, x.pd, x.t, #[trigger] idx@[p] as int) != NONE
                ==> exists|r: int| 0 <= r < m && qj@[r] == idx@[p],
        decreases n - q,
    {
        let j = idx[q];
        let cr = ci[q];
        proof { assert(jb <= idx@[q as int] < je && date_in(o_date(sv)[idx@[q as int] as int], x.pd, x.t)); }
        let hit = cust_bit(sh, cr, Ghost(x), Ghost(j as int));
        let ghost (qj0, qr0) = (qj@, qr@);
        put(qj, m, j);
        put(qr, m, cr);
        proof {
            assert forall|r: int| 0 <= r < m implies #[trigger] qj@[r] == qj0[r] && qr@[r] == qr0[r] by {}
            if q > 0 { assert(idx@[q - 1] < idx@[q as int]); }
            let m2 = m + if hit { 1int } else { 0int };
            assert forall|r: int, r2: int| 0 <= r < r2 < m2 implies #[trigger] qj@[r] < #[trigger] qj@[r2] by {
                if r2 < m { assert(qj0[r] < qj0[r2]); } else { assert(qj0[r] <= idx@[q - 1]); }
            }
            assert forall|r: int| 0 <= r < m2 implies q + 1 > 0 && #[trigger] qj@[r] <= idx@[q as int] by {
                if r < m { assert(qj0[r] <= idx@[q - 1]); }
            }
            assert forall|p: int| 0 <= p < q + 1 && ord_code(sv, x.slots, x.pd, x.t, #[trigger] idx@[p] as int) != NONE
                implies exists|r: int| 0 <= r < m2 && qj@[r] == idx@[p] by {
                if p < q {
                    let r = choose|r: int| 0 <= r < m && qj0[r] == idx@[p];
                    assert(qj@[r] == qj0[r]);
                } else {
                    assert(qj@[m as int] == j);
                }
            }
        }
        m = m + if hit { 1usize } else { 0usize };
        q = q + 1;
    }
    proof {
        assert forall|jj: int| jb <= jj < je && #[trigger] ord_code(sv, x.slots, x.pd, x.t, jj) != NONE
            implies exists|r: int| 0 <= r < m && qj@[r] == jj by {
            assert(date_in(o_date(sv)[jj], x.pd, x.t));
            let p = choose|p: int| 0 <= p < n && idx@[p] == jj;
            assert(ord_code(sv, x.slots, x.pd, x.t, idx@[p] as int) != NONE);
        }
    }
    m
}

} // verus!
