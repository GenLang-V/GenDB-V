//! The dictionary indices of the statement's text literals and parameters (`kernel::Arms`, `kernel::LiK`).
//!
//! Each literal is looked up once in its sorted dictionary (`dict_find`, a binary search); an absent literal gets
//! `u64::MAX`, an index no entry has. Because a sorted dictionary's entries are distinct, entry `e` holds the
//! literal exactly when `e` is the found index (`find_li`, `find_pa`).
use vstd::prelude::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::layout::PartView;
use crate::stores::facts::interface::common::colfmt::{text_of, text_parts_wf, dict_sorted, lemma_dict_distinct};
use crate::stores::facts::interface::common::read::dict_find;
use crate::stores::custpart::interface::common::colfmt as cpc;
use crate::stores::custpart::interface::common::read as cpr;
use super::model::*;
use super::terms::*;
use super::kernel::*;

verus! {

/// Index of `needle` in a sorted lineitem dictionary, or `u64::MAX`: entry `e` is the needle exactly at that index.
pub fn find_li(offs: &[u64], bytes: &[u8], needle: &[u8]) -> (r: u64)
    requires
        offs@.len() >= 1,
        text_parts_wf(offs@, bytes@, offs@.len() - 1),
        dict_sorted(offs@, bytes@, offs@.len() - 1),
    ensures
        forall|e: int| 0 <= e < offs@.len() - 1 ==> ((e == r) == (#[trigger] text_of(offs@, bytes@, e) == needle@)),
{
    let k = offs.len() - 1;
    match dict_find(offs, bytes, k, needle, needle.len()) {
        Some(x) => {
            proof {
                assert forall|e: int| 0 <= e < offs@.len() - 1 implies ((e == x) == (#[trigger] text_of(offs@, bytes@, e) == needle@)) by {
                    if e != x {
                        lemma_dict_distinct(offs@, bytes@, k as int, e, x as int);
                    }
                }
            }
            x as u64
        },
        None => u64::MAX,
    }
}

/// Index of `needle` in a sorted part dictionary, or `u64::MAX`.
pub fn find_pa(offs: &[u64], bytes: &[u8], needle: &[u8]) -> (r: u64)
    requires
        offs@.len() >= 1,
        cpc::text_parts_wf(offs@, bytes@, offs@.len() - 1),
        cpc::dict_sorted(offs@, bytes@, offs@.len() - 1),
    ensures
        forall|e: int| 0 <= e < offs@.len() - 1 ==> ((e == r) == (#[trigger] cpc::text_of(offs@, bytes@, e) == needle@)),
{
    let k = offs.len() - 1;
    match cpr::dict_find(offs, bytes, k, needle, needle.len()) {
        Some(x) => {
            proof {
                assert forall|e: int| 0 <= e < offs@.len() - 1 implies ((e == x) == (#[trigger] cpc::text_of(offs@, bytes@, e) == needle@)) by {
                    if e != x {
                        cpc::lemma_dict_distinct(offs@, bytes@, k as int, e, x as int);
                    }
                }
            }
            x as u64
        },
        None => u64::MAX,
    }
}

/// The bytes of container `i` of arm `a`.
pub fn cont_bytes(a: u8, i: u8) -> (v: Vec<u8>)
    requires a < 3, i < 4,
    ensures v@ == cont_lit(a as int, i as int),
{
    let v = if a == 0 {
        if i == 0 { vec![83u8, 77u8, 32u8, 67u8, 65u8, 83u8, 69u8] }
        else if i == 1 { vec![83u8, 77u8, 32u8, 66u8, 79u8, 88u8] }
        else if i == 2 { vec![83u8, 77u8, 32u8, 80u8, 65u8, 67u8, 75u8] }
        else { vec![83u8, 77u8, 32u8, 80u8, 75u8, 71u8] }
    } else if a == 1 {
        if i == 0 { vec![77u8, 69u8, 68u8, 32u8, 66u8, 65u8, 71u8] }
        else if i == 1 { vec![77u8, 69u8, 68u8, 32u8, 66u8, 79u8, 88u8] }
        else if i == 2 { vec![77u8, 69u8, 68u8, 32u8, 80u8, 75u8, 71u8] }
        else { vec![77u8, 69u8, 68u8, 32u8, 80u8, 65u8, 67u8, 75u8] }
    } else {
        if i == 0 { vec![76u8, 71u8, 32u8, 67u8, 65u8, 83u8, 69u8] }
        else if i == 1 { vec![76u8, 71u8, 32u8, 66u8, 79u8, 88u8] }
        else if i == 2 { vec![76u8, 71u8, 32u8, 80u8, 65u8, 67u8, 75u8] }
        else { vec![76u8, 71u8, 32u8, 80u8, 75u8, 71u8] }
    };
    proof {
        assert(v@ =~= cont_lit(a as int, i as int));
    }
    v
}

/// The dictionary indices and bounds of arm `a` with brand parameter `brand` and quantity parameter `qp`.
pub fn build_arm(d: &Dicts, brand: &[u8], qp: i64, a: u8,
    Ghost(fp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>) -> (k: ArmK)
    requires
        dicts_ok(*d, fp, cp),
        pa_shape(cp),
        a < 3,
        brand@ == brand_p(ps, a as int),
        qp as int == qty_p(ps, a as int),
        -2147483648 <= qp <= 2147483647,
    ensures arm_k_ok(k, ps, a as int, cp),
{
    let b = find_pa(d.bo, d.by, brand);
    let v0 = cont_bytes(a, 0);
    let v1 = cont_bytes(a, 1);
    let v2 = cont_bytes(a, 2);
    let v3 = cont_bytes(a, 3);
    let c0 = find_pa(d.co, d.cy, v0.as_slice());
    let c1 = find_pa(d.co, d.cy, v1.as_slice());
    let c2 = find_pa(d.co, d.cy, v2.as_slice());
    let c3 = find_pa(d.co, d.cy, v3.as_slice());
    let smax: i64 = if a == 0 { 5 } else if a == 1 { 10 } else { 15 };
    let k = ArmK { b, c0, c1, c2, c3, smax, qlo: 100 * qp, qhi: 100 * (qp + 10) };
    proof {
        assert forall|e: int| 0 <= e < n_cd(cp) implies
            ((e == k.c0 || e == k.c1 || e == k.c2 || e == k.c3) == cont_in(a as int, #[trigger] cdict(cp, e))) by {
            assert((e == c0) == (cpc::text_of(d.co@, d.cy@, e) == cont_lit(a as int, 0)));
            assert((e == c1) == (cpc::text_of(d.co@, d.cy@, e) == cont_lit(a as int, 1)));
            assert((e == c2) == (cpc::text_of(d.co@, d.cy@, e) == cont_lit(a as int, 2)));
            assert((e == c3) == (cpc::text_of(d.co@, d.cy@, e) == cont_lit(a as int, 3)));
        }
        assert forall|e: int| 0 <= e < n_bd(cp) implies ((e == k.b) == (#[trigger] bdict(cp, e) == brand_p(ps, a as int))) by {
            assert((e == b) == (cpc::text_of(d.bo@, d.by@, e) == brand@));
        }
    }
    k
}

/// The dictionary indices of `'DELIVER IN PERSON'`, `'AIR'` and `'AIR REG'`.
pub fn build_lik(d: &Dicts, Ghost(fp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>) -> (k: LiK)
    requires
        dicts_ok(*d, fp, cp),
        li_shape(fp),
    ensures li_k_ok(k, fp),
{
    let vd = vec![68u8, 69u8, 76u8, 73u8, 86u8, 69u8, 82u8, 32u8, 73u8, 78u8, 32u8, 80u8, 69u8, 82u8, 83u8, 79u8, 78u8];
    let va = vec![65u8, 73u8, 82u8];
    let vr = vec![65u8, 73u8, 82u8, 32u8, 82u8, 69u8, 71u8];
    proof {
        assert(vd@ =~= dip());
        assert(va@ =~= air());
        assert(vr@ =~= air_reg());
    }
    let ns = d.so.len();
    let nm = d.mo.len();
    proof {
        assert(ns as int <= u64::MAX && nm as int <= u64::MAX);
    }
    let it = find_li(d.so, d.sy, vd.as_slice());
    let m1 = find_li(d.mo, d.my, va.as_slice());
    let m2 = find_li(d.mo, d.my, vr.as_slice());
    let k = LiK { it, m1, m2 };
    proof {
        assert forall|e: int| 0 <= e < n_sd(fp) implies ((e == k.it) == (#[trigger] sdict(fp, e) == dip())) by {
            assert((e == it) == (text_of(d.so@, d.sy@, e) == vd@));
        }
        assert forall|e: int| 0 <= e < n_md(fp) implies ((e == k.m1 || e == k.m2) == mode_in(#[trigger] mdict(fp, e))) by {
            assert((e == m1) == (text_of(d.mo@, d.my@, e) == va@));
            assert((e == m2) == (text_of(d.mo@, d.my@, e) == vr@));
        }
        assert(n_sd(fp) < u64::MAX && n_md(fp) < u64::MAX);
    }
    k
}

} // verus!
