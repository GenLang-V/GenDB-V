//! The result rows of a top-20 buffer: for each candidate customer, its key, name, revenue (scale 4), account
//! balance (scale 2), nation name, address, phone and comment, read from the output columns (`load::Txt`).
use vstd::prelude::*;
use vstd::slice::slice_to_vec;
use crate::spec::value::*;
use crate::exec::value::{EVal, view_row};
use crate::link::query::view_rows;
use crate::stores::custpart::interface::common::read as cr;
use crate::stores::suppliers::interface::common::read as sr;
use super::model::*;
use super::qspec::*;
use super::kernel::*;
use super::cand::*;
use super::load::*;

verus! {

/// The output row of candidate `cand` (a group of the result).
fn cand_out(c: &Cols, t: &Txt, cand: Cand, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (row: Vec<EVal>)
    requires
        cols_ok(*c, m, p), txt_ok(*t, m), model_ok(m),
        cand.cpos < m.c_n,
        good(m, p, cand.cpos as int),
    ensures view_row(row@) == cand_row(m, cand),
{
    let i = cand.cpos;
    proof {
        lemma_block_bound(i as int, m.c_bs, m.c_n, m.c_nb);
        assert(in_i64(ckey(m, i as int)));
        assert(in_i64(cnat(m, i as int)));
        assert(crate::spec::numeric::pow10(15) == 1000000000000000) by (compute);
        assert(cf_range(m, i as int));
    }
    let g = ((i as u64) / t.c_bs) as usize;
    let key = t.c_key_b[g] + t.c_key_c[i] as i64;
    let bal = t.c_bal_b[g] + t.c_bal_c[i] as i64;
    let name = slice_to_vec(cr::text_slice(t.c_name_o, t.c_name_y, i));
    let addr = slice_to_vec(cr::text_slice(t.c_addr_o, t.c_addr_y, i));
    let phone = slice_to_vec(cr::text_slice(t.c_phone_o, t.c_phone_y, i));
    let cmt = slice_to_vec(cr::text_slice(t.c_cmt_o, t.c_cmt_y, i));
    let nn: usize = match nat_ok_at(c, i, Ghost(m), Ghost(p)) {
        Some(n) => n,
        None => 0,
    };
    let nname_v = slice_to_vec(sr::text_slice(t.n_name_o, t.n_name_y, nn));
    let row = vec![EVal::Int(key), EVal::Text(name), EVal::Num { coeff: cand.rev, scale: 4 },
        EVal::Num { coeff: bal as i128, scale: 2 }, EVal::Text(nname_v), EVal::Text(addr), EVal::Text(phone), EVal::Text(cmt)];
    proof {
        assert(view_row(row@) =~= cand_row(m, cand));
    }
    row
}

/// Text ranges of customer row `i` lie inside their byte parts.
pub open spec fn cf_range(m: M, i: int) -> bool {
    &&& crate::stores::custpart::interface::common::colfmt::text_range_ok(m.c_name_o, m.c_name_y, i)
    &&& crate::stores::custpart::interface::common::colfmt::text_range_ok(m.c_addr_o, m.c_addr_y, i)
    &&& crate::stores::custpart::interface::common::colfmt::text_range_ok(m.c_phone_o, m.c_phone_y, i)
    &&& crate::stores::custpart::interface::common::colfmt::text_range_ok(m.c_cmt_o, m.c_cmt_y, i)
}

/// The result rows of a buffer of groups.
pub fn emit(c: &Cols, t: &Txt, buf: &Vec<Cand>, len: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (rows: Vec<Vec<EVal>>)
    requires
        cols_ok(*c, m, p), txt_ok(*t, m), model_ok(m),
        len <= buf@.len(),
        cands_good(m, p, buf@, len as int),
    ensures
        view_rows(rows@) == cands_view(m, buf@, len as int),
{
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            cols_ok(*c, m, p), txt_ok(*t, m), model_ok(m),
            len <= buf@.len(),
            cands_good(m, p, buf@, len as int),
            i <= len,
            view_rows(rows@) == cands_view(m, buf@, i as int),
        decreases len - i,
    {
        let cand = buf[i];
        let row = cand_out(c, t, cand, Ghost(m), Ghost(p));
        proof {
            crate::link::outcome::lemma_view_rows_push(rows@, row);
        }
        rows.push(row);
        proof {
            lemma_view_push(m, buf@, i as int);
        }
        i = i + 1;
    }
    rows
}

} // verus!
