//! The executable output rows: `[sic, tlabel, stmt, COUNT(DISTINCT cik), SUM(value), AVG(value)]` of a group, whose
//! view is the GroupBy row `group::g_row` (`out_row`); and the selection of the output candidates at a threshold.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::fns::div::num_div_fits;
use crate::exec::value::{EVal, view_row};
use crate::link::query::{avg_of, exec_avg_finalize, text_at, text_wf, TextCol};
use crate::agent::common::text::text_val;
use crate::agent::cols::*;
use crate::agent::groups::*;
use crate::agent::fold::*;
use crate::agent::group::*;
use crate::agent::topk::*;
use crate::agent::answer::*;

verus! {

/// A copy of `n` bytes.
pub fn copy_bytes(x: &[u8], n: usize) -> (v: Vec<u8>)
    requires n == x@.len(),
    ensures v@ == x@,
{
    let mut v: Vec<u8> = Vec::with_capacity(n);
    let mut q: usize = 0;
    while q < n
        invariant q <= n, n == x@.len(), v@ == x@.subrange(0, q as int),
        decreases n - q,
    {
        v.push(x[q]);
        q = q + 1;
        proof {
            assert(v@ =~= x@.subrange(0, q as int));
        }
    }
    proof {
        assert(x@.subrange(0, n as int) =~= x@);
    }
    v
}

/// The output columns a row is read from.
pub open spec fn out_cols_ok(k: &Cols, c: Ctx) -> bool {
    &&& cols_ok(k, c)
    &&& k.s_sic@.len() == c.m && text_wf(k.t_label@, c.nt) && k.t_labelv@.len() == c.nt
}

/// The output row of group `g`.
pub fn out_row(k: &Cols, stmt: &[u8], stmt_len: usize, gr: &Groups, sum: &Vec<i128>, cnt: &Vec<usize>, dcnt: &Vec<usize>,
    g: usize, Ghost(c): Ghost<Ctx>) -> (r: Vec<EVal>)
    requires
        out_cols_ok(k, c), stmt@ == c.stmt, stmt_len == stmt@.len(),
        reps_ok(c, gr.reps@), (g as int) < gr.reps@.len(), sum@.len() == gr.reps@.len(), cnt@.len() == gr.reps@.len(),
        dcnt@.len() == gr.reps@.len(), dcnt@[g as int] <= 0x1_0000_0000,
        num_div_fits(sum@[g as int] as int, 4, cnt@[g as int] as int, 0),
    ensures view_row(r@) == g_row(c, gr.reps@, sum@, cnt@, dcnt@, g as int),
{
    let (j, kk) = gr.reps[g];
    let sic = k.s_sic[j];
    let label = if k.t_labelv[kk] == 0 {
        EVal::Null
    } else {
        let (b, bl) = text_val(&k.t_label, kk, Ghost(c.nt));
        EVal::Text(copy_bytes(b, bl))
    };
    let st = EVal::Text(copy_bytes(stmt, stmt_len));
    let d = dcnt[g];
    let s = sum[g];
    let n = cnt[g];
    let avg = match exec_avg_finalize(s, 4, n as u64) {
        Ok(v) => v,
        Err(_) => {
            proof {
                assert(false);
            }
            EVal::Null
        },
    };
    let mut row: Vec<EVal> = Vec::new();
    row.push(EVal::Int(sic as i64));
    row.push(label);
    row.push(st);
    row.push(EVal::Int(d as i64));
    row.push(EVal::Num { coeff: s, scale: 4 });
    row.push(avg);
    proof {
        assert(view_row(row@) =~= g_row(c, gr.reps@, sum@, cnt@, dcnt@, g as int));
    }
    row
}

/// The groups of `order` with at least two distinct ciks and a sum of at least `t`, in order.
pub fn select_cands(order: &Vec<usize>, sum: &Vec<i128>, dcnt: &Vec<usize>, t: i128) -> (r: Vec<usize>)
    requires
        forall|x: int| 0 <= x < order@.len() ==> (#[trigger] order@[x] as int) < sum@.len() && (order@[x] as int) < dcnt@.len(),
    ensures r@ == filt(order@, cand_at(dcnt@, sum@, t as int)),
{
    let n = order.len();
    let mut r: Vec<usize> = Vec::new();
    let mut x: usize = 0;
    let ghost f = cand_at(dcnt@, sum@, t as int);
    proof {
        assert(order@.take(0) =~= Seq::<usize>::empty());
    }
    while x < n
        invariant
            n == order@.len(), x <= n,
            forall|y: int| 0 <= y < order@.len() ==> (#[trigger] order@[y] as int) < sum@.len() && (order@[y] as int) < dcnt@.len(),
            f == cand_at(dcnt@, sum@, t as int),
            r@ == filt(order@.take(x as int), f),
        decreases n - x,
    {
        let g = order[x];
        proof {
            assert(order@.take(x + 1) =~= order@.take(x as int).push(g));
            lemma_filt_push(order@.take(x as int), g, f);
        }
        if dcnt[g] >= 2 && sum[g] >= t {
            r.push(g);
        }
        x = x + 1;
    }
    proof {
        assert(order@.take(n as int) =~= order@);
    }
    r
}

} // verus!
