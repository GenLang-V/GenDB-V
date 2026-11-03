//! Output construction on the calling thread: the result row of every selected group code whose aggregates are
//! values (`build_rows`, in code order), and for the failure path the smallest canonical row number of a code's
//! stored rows (`first_of`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::limits::int8_max;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::StoredParts;
use crate::gendb_entry::work::{filled, put};
use crate::exec::value::*;
use crate::link::query::{exec_avg_finalize, view_rows};
use crate::stores::pre::interface::*;
use crate::stores::pre::interface::common::cols::*;
use crate::stores::pre::interface::common::text::*;
use super::store::*;
use super::answer::*;
use super::failure::*;
use super::runs::*;

verus! {

/// The accumulators hold the per-code values of every live code.
pub open spec fn accs_ok(p: Seq<PartView>, live: Seq<bool>, cnt: Seq<u64>, nf: Seq<u64>, sum: Seq<i128>) -> bool {
    &&& cnt.len() == group_count(p) && nf.len() == group_count(p) && sum.len() == group_count(p)
    &&& live.len() == group_count(p)
    &&& forall|g: int| 0 <= g < group_count(p) ==> #[trigger] live[g] == live_of(p, g)
    &&& forall|g: int| 0 <= g < group_count(p) && #[trigger] live_of(p, g) ==> {
        &&& cnt[g] as int == rr(p, g)
        &&& nf[g] as int == rc(p, g)
        &&& sum[g] as int == rv(p, g)
    }
}

/// The rows built so far: `codes` increasing, selected and `code_ok`, their rows in order; `fail` marks the
/// selected codes that are not `code_ok`.
pub open spec fn built_ok(p: Seq<PartView>, upto: int, rows: Seq<Vec<EVal>>, codes: Seq<int>, fail: Seq<bool>, any: bool) -> bool {
    &&& fail.len() == group_count(p)
    &&& forall|i: int| 0 <= i < codes.len() ==> #[trigger] selected(p, codes[i]) && code_ok(p, codes[i]) && codes[i] < upto
    &&& forall|i: int, j: int| 0 <= i < j < codes.len() ==> #[trigger] codes[i] < #[trigger] codes[j]
    &&& view_rows(rows) == codes.map_values(|g: int| prow(p, g))
    &&& forall|g: int| 0 <= g < group_count(p) && #[trigger] fail[g] ==> g < upto && selected(p, g) && !code_ok(p, g)
    &&& forall|g: int| 0 <= g < upto && #[trigger] selected(p, g) ==> fail[g] || codes.contains(g)
    &&& any == exists|g: int| 0 <= g < group_count(p) && #[trigger] fail[g]
}

/// The text of a dictionary entry as an owned value.
fn entry_text(st: &mut StoredParts, p_off: usize, p_bytes: usize, count: usize, k: usize) -> (v: EVal)
    requires
        p_off < old(st)@.len(), p_bytes < old(st)@.len(),
        old(st)@[p_off as int] is U64, old(st)@[p_bytes as int] is U8,
        text_parts_wf(u64_part(old(st)@[p_off as int]), u8_part(old(st)@[p_bytes as int]), count as int),
        k < count < usize::MAX,
    ensures
        final(st)@ == old(st)@,
        v@ == Val::Text(text_entry(u64_part(old(st)@[p_off as int]), u8_part(old(st)@[p_bytes as int]), k as int)),
{
    let b = read_text_entry(st, p_off, p_bytes, count, k);
    EVal::Text(vstd::slice::slice_to_vec(b))
}

/// The output row of selected code `g` (its aggregates are values; `avg` is its AVG).
fn code_row(st: &mut StoredParts, group_stmt: &'static [u64], group_rfile: &'static [u64], g: usize,
    cnt: u64, nf: u64, avg: EVal) -> (row: Vec<EVal>)
    requires
        pre_layout_ok(old(st)@),
        group_stmt@ == u64s(old(st)@, P_GROUP_STMT), group_rfile@ == u64s(old(st)@, P_GROUP_RFILE),
        selected(old(st)@, g as int),
        cnt as int == rr(old(st)@, g as int), nf as int == rc(old(st)@, g as int),
        cnt <= i64::MAX, nf <= i64::MAX,
        avg@ == avg_of_code(old(st)@, g as int),
    ensures final(st)@ == old(st)@, view_row(row@) == prow(old(st)@, g as int),
{
    let ghost p = st@;
    proof { lemma_layout_facts(p); }
    let nstmt = st.part_len(P_STMT_OFF) - 1;
    let nrfile = st.part_len(P_RFILE_OFF) - 1;
    let k = group_stmt[g];
    let stmt = entry_text(st, P_STMT_OFF, P_STMT_BYTES, nstmt, (k - 1) as usize);
    let rfile = entry_text(st, P_RFILE_OFF, P_RFILE_BYTES, nrfile, group_rfile[g] as usize);
    let mut row: Vec<EVal> = Vec::new();
    row.push(stmt);
    row.push(rfile);
    row.push(EVal::Int(cnt as i64));
    row.push(EVal::Int(nf as i64));
    row.push(avg);
    proof {
        assert(view_row(row@) =~= prow(p, g as int));
    }
    row
}

/// AVG(line) of code `g`.
pub open spec fn avg_of_code(p: Seq<PartView>, g: int) -> Val {
    crate::link::query::avg_of(rv(p, g), 0, rr(p, g) as nat)
}

/// The rows of the selected codes whose aggregates are values, in code order; the others are marked failed.
pub fn build_rows(st: &mut StoredParts, group_stmt: &'static [u64], group_rfile: &'static [u64], live: &Vec<bool>,
    cnt: &Vec<u64>, nf: &Vec<u64>, sum: &Vec<i128>, ng: usize)
    -> (r: (Vec<Vec<EVal>>, Vec<bool>, bool, Ghost<Seq<int>>))
    requires
        pre_layout_ok(old(st)@),
        ng == group_count(old(st)@),
        group_stmt@ == u64s(old(st)@, P_GROUP_STMT), group_rfile@ == u64s(old(st)@, P_GROUP_RFILE),
        accs_ok(old(st)@, live@, cnt@, nf@, sum@),
    ensures
        final(st)@ == old(st)@,
        built_ok(old(st)@, ng as int, r.0@, r.3@, r.1@, r.2),
{
    let ghost p = st@;
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let mut fail: Vec<bool> = filled(ng, false);
    let mut any = false;
    let ghost mut codes: Seq<int> = Seq::empty();
    let mut g: usize = 0;
    proof {
        assert(codes.map_values(|h: int| prow(p, h)) =~= Seq::<Row>::empty());
        assert(view_rows(rows@) =~= Seq::<Row>::empty());
    }
    while g < ng
        invariant
            st@ == p, pre_layout_ok(p), ng == group_count(p), g <= ng,
            group_stmt@ == u64s(p, P_GROUP_STMT), group_rfile@ == u64s(p, P_GROUP_RFILE),
            accs_ok(p, live@, cnt@, nf@, sum@),
            built_ok(p, g as int, rows@, codes, fail@, any),
        decreases ng - g,
    {
        let ghost gi = g as int;
        if live[g] && cnt[g] > 0 {
            assert(selected(p, gi));
            let fits_counts = cnt[g] <= 0x7fff_ffff_ffff_ffff && nf[g] <= 0x7fff_ffff_ffff_ffff;
            let avg = if fits_counts { exec_avg_finalize(sum[g], 0, cnt[g]) } else { Err(Capacity) };
            match avg {
                Ok(v) => {
                    assert(code_ok(p, gi));
                    let row = code_row(st, group_stmt, group_rfile, g, cnt[g], nf[g], v);
                    let ghost before = rows@;
                    rows.push(row);
                    proof {
                        let old_codes = codes;
                        codes = codes.push(gi);
                        assert(view_rows(rows@) =~= view_rows(before).push(view_row(row@)));
                        assert(codes.map_values(|h: int| prow(p, h)) =~= old_codes.map_values(|h: int| prow(p, h)).push(prow(p, gi)));
                        assert forall|i: int, j: int| 0 <= i < j < codes.len() implies #[trigger] codes[i] < #[trigger] codes[j] by {
                            if j < old_codes.len() { assert(codes[i] == old_codes[i] && codes[j] == old_codes[j]); }
                            else { assert(codes[i] == old_codes[i]); assert(selected(p, old_codes[i])); assert(old_codes[i] < gi); }
                        }
                        assert forall|i: int| 0 <= i < codes.len() implies #[trigger] selected(p, codes[i]) && code_ok(p, codes[i]) && codes[i] < gi + 1 by {
                            if i < old_codes.len() { assert(codes[i] == old_codes[i]); }
                        }
                        assert forall|h: int| 0 <= h <= gi && #[trigger] selected(p, h) implies fail@[h] || codes.contains(h) by {
                            if h < gi && !fail@[h] {
                                let i = choose|i: int| 0 <= i < old_codes.len() && old_codes[i] == h;
                                assert(codes[i] == h);
                            } else if h == gi {
                                assert(codes[codes.len() - 1] == h);
                            }
                        }
                    }
                },
                Err(_) => {
                    assert(!code_ok(p, gi));
                    let ghost old_fail = fail@;
                    put(&mut fail, g, true);
                    any = true;
                    proof {
                        assert(forall|i: int| 0 <= i < codes.len() ==> #[trigger] selected(p, codes[i]) && code_ok(p, codes[i]) && codes[i] < gi + 1);
                        assert(fail@[gi]);
                        assert(exists|h: int| 0 <= h < group_count(p) && #[trigger] fail@[h]);
                        assert forall|h: int| 0 <= h < group_count(p) && #[trigger] fail@[h] implies h < gi + 1 && selected(p, h) && !code_ok(p, h) by {
                            if h != gi { assert(old_fail[h]); }
                        }
                        assert forall|h: int| 0 <= h < gi + 1 && #[trigger] selected(p, h) implies fail@[h] || codes.contains(h) by {
                            if h != gi { assert(fail@[h] == old_fail[h]); }
                        }
                    }
                },
            }
        } else {
            proof {
                assert(forall|i: int| 0 <= i < codes.len() ==> #[trigger] selected(p, codes[i]) && code_ok(p, codes[i]) && codes[i] < gi + 1);
                assert(!selected(p, gi));
                assert forall|h: int| 0 <= h < gi + 1 && #[trigger] selected(p, h) implies fail@[h] || codes.contains(h) by {
                    if h != gi {}
                }
            }
        }
        proof {
            assert(fail@.len() == group_count(p));
            assert(forall|i: int| 0 <= i < codes.len() ==> #[trigger] selected(p, codes[i]) && code_ok(p, codes[i]) && codes[i] < gi + 1);
            assert(forall|i: int, j: int| 0 <= i < j < codes.len() ==> #[trigger] codes[i] < #[trigger] codes[j]);
            assert(view_rows(rows@) == codes.map_values(|h: int| prow(p, h)));
            assert(forall|h: int| 0 <= h < group_count(p) && #[trigger] fail@[h] ==> h < gi + 1 && selected(p, h) && !code_ok(p, h));
            assert(forall|h: int| 0 <= h < gi + 1 && #[trigger] selected(p, h) ==> fail@[h] || codes.contains(h));
            assert(any == exists|h: int| 0 <= h < group_count(p) && #[trigger] fail@[h]);
        }
        g = g + 1;
    }
    (rows, fail, any, Ghost(codes))
}

/// The smallest canonical row number of the stored rows of code `g` (which has a sub-run).
pub fn first_of(orig: &'static [u64], start: &'static [u64], sub_group: &'static [u64], ns: usize, n: usize, g: usize,
    Ghost(p): Ghost<Seq<PartView>>) -> (f: u64)
    requires
        pre_layout_ok(p),
        ns == sub_count(p), n == row_count(p),
        orig@ == u64s(p, P_ORIG), start@ == st_of(p), sub_group@ == sg_of(p),
        exists|s: int| 0 <= s < ns && sub_group@[s] == g,
    ensures first_at(p, g as int, f as int),
{
    proof { lemma_layout_facts(p); }
    let ghost gi = g as int;
    let mut m: u64 = u64::MAX;
    let mut found = false;
    let mut s: usize = 0;
    while s < ns
        invariant
            pre_layout_ok(p), ns == sub_count(p), s <= ns, gi == g,
            orig@ == u64s(p, P_ORIG), start@ == st_of(p), sub_group@ == sg_of(p),
            starts_ok(st_of(p), ns as int), st_of(p)[ns as int] == row_count(p), orig@.len() == row_count(p), n == row_count(p),
            forall|t: int, i: int| #[trigger] in_code(p, gi, t, i) && t < s ==> m <= orig@[i],
            found ==> exists|t: int, i: int| #[trigger] in_code(p, gi, t, i) && t < s && orig@[i] == m,
            !found ==> forall|t: int| 0 <= t < s ==> #[trigger] sub_group@[t] != g,
        decreases ns - s,
    {
        if sub_group[s] == g as u64 {
            proof {
                assert(st_of(p)[s as int] < st_of(p)[s + 1]);
                assert(st_of(p)[s + 1] <= st_of(p)[ns as int]) by { if s + 1 < ns { assert(st_of(p)[s + 1] < st_of(p)[ns as int]); } }
            }
            let a = start[s] as usize;
            let b = start[s + 1] as usize;
            let mut i = a;
            while i < b
                invariant
                    a <= i <= b, a == st_of(p)[s as int], b == st_of(p)[s + 1], b <= orig@.len(), s < ns, gi == g,
                    pre_layout_ok(p), ns == sub_count(p),
                    sg_of(p)[s as int] == g,
                    orig@ == u64s(p, P_ORIG), start@ == st_of(p), sub_group@ == sg_of(p),
                    forall|t: int, j: int| #[trigger] in_code(p, gi, t, j) && t < s ==> m <= orig@[j],
                    forall|j: int| a <= j < i ==> m <= #[trigger] orig@[j],
                    found ==> (exists|t: int, j: int| #[trigger] in_code(p, gi, t, j) && t <= s && orig@[j] == m),
                    !found ==> forall|t: int| 0 <= t < s ==> #[trigger] sub_group@[t] != g,
                    i > a ==> found,
                decreases b - i,
            {
                if orig[i] < m || !found {
                    proof {
                        assert(in_code(p, gi, s as int, i as int));
                    }
                    m = orig[i];
                    found = true;
                    proof {
                        assert forall|t: int, j: int| #[trigger] in_code(p, gi, t, j) && t < s implies m <= orig@[j] by {}
                    }
                }
                i = i + 1;
            }
            proof {
                assert forall|t: int, j: int| #[trigger] in_code(p, gi, t, j) && t < s + 1 implies m <= orig@[j] by {
                    if t == s {} else {}
                }
            }
        }
        s = s + 1;
    }
    proof {
        let t = choose|t: int| 0 <= t < ns && sub_group@[t] == g;
        assert(found);
        let (t2, j2) = choose|t: int, j: int| #[trigger] in_code(p, gi, t, j) && t < ns && orig@[j] == m;
        assert(in_code(p, gi, t2, j2) && u64s(p, P_ORIG)[j2] == m);
    }
    m
}

} // verus!
