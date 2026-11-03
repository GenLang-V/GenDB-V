//! The stages of the query: the binding's codes, the pre-pair maps, the filings, the lookups and the join inputs,
//! each with the facts the context (`filing::cx_ok`) needs.
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::stores::num::interface as N;
use crate::stores::pre::interface as P;
use crate::stores::sub_sic::interface as S;
use crate::stores::tag_tv::interface as T;
use crate::stores::num::interface::common::text::{text_entry, find_text};
use crate::agent::common::dictmap::NONE;
use crate::agent::maps::*;
use crate::agent::mapfacts::*;
use crate::agent::pairs::*;
use crate::agent::levels::*;
use crate::agent::filings::*;
use crate::agent::inputs::*;
use crate::agent::common::sort::sorted_k;
use crate::agent::filing::*;
use crate::agent::join::*;
use crate::agent::cbuf::{CBuf, cflat};

verus! {

// ------------------------------------------------------------------------------------------------ codes

pub open spec fn sc_ok(pre: Seq<PartView>, b1: Seq<u8>, sc: int) -> bool {
    &&& sc >= 0 ==> sc < P::stmt_count(pre) && pstmt_entry(pre, sc) == b1
    &&& sc < 0 ==> forall|k: int| 0 <= k < P::stmt_count(pre) ==> #[trigger] pstmt_entry(pre, k) != b1
}

pub open spec fn gq_ok(pre: Seq<PartView>, sc: int, gqv: Seq<bool>) -> bool {
    gqv.len() == P::group_count(pre) && forall|g: int| 0 <= g < P::group_count(pre) ==> #[trigger] gqv[g] == gq(pre, sc, g)
}

/// The uom code of `$1`, its run range, the stmt code of `$2` and the groups with that stmt.
pub fn stage_keys(nin: &NumIn, pin: &PreIn, p0: &[u8], p1: &[u8], Ghost(num): Ghost<Seq<PartView>>, Ghost(pre): Ghost<Seq<PartView>>)
    -> (r: (u64, u64, usize, usize, Vec<bool>))
    requires num_in_ok(num, *nin), pre_in_ok(pre, *pin),
    ensures
        uom_ok(num, p0@, tvi(r.0), r.2 as int, r.3 as int),
        sc_ok(pre, p1@, tvi(r.1)),
        gq_ok(pre, tvi(r.1), r.4@),
{
    let u: u64 = match find_text(nin.uom.off, nin.uom.bytes, nin.uom.n, p0, p0.len()) {
        Some(k) => k as u64,
        None => NONE,
    };
    let mut r0: usize = 0;
    let mut r1: usize = 0;
    let nrun = nin.run_adsh.len();
    if u != NONE {
        proof {
            N::lemma_uom_runs(num, u as int);
            assert(nin.uom_runs@[u + 1] <= nrun);
        }
        r0 = nin.uom_runs[u as usize] as usize;
        r1 = nin.uom_runs[u as usize + 1] as usize;
    }
    proof {
        if u == NONE {
            assert forall|k: int| 0 <= k < N::uom_count(num) implies #[trigger] uom_entry(num, k) != p0@ by {
                assert(uom_entry(num, k) == text_entry(nin.uom.off@, nin.uom.bytes@, k));
            }
        } else {
            assert(uom_entry(num, u as int) == text_entry(nin.uom.off@, nin.uom.bytes@, u as int));
        }
    }
    let sc: u64 = match find_text(pin.stmt.off, pin.stmt.bytes, pin.stmt.n, p1, p1.len()) {
        Some(k) => k as u64,
        None => NONE,
    };
    proof {
        if sc == NONE {
            assert forall|k: int| 0 <= k < P::stmt_count(pre) implies #[trigger] pstmt_entry(pre, k) != p1@ by {
                assert(pstmt_entry(pre, k) == text_entry(pin.stmt.off@, pin.stmt.bytes@, k));
            }
        } else {
            assert(pstmt_entry(pre, sc as int) == text_entry(pin.stmt.off@, pin.stmt.bytes@, sc as int));
        }
    }
    let ng = pin.gstmt.len();
    let mut gqv: Vec<bool> = Vec::new();
    let mut g: usize = 0;
    while g < ng
        invariant
            g <= ng, ng == P::group_count(pre), pin.gstmt@ == pre_u64s(pre, P::P_GROUP_STMT),
            sc == NONE || sc < pin.stmt.n, pin.stmt.n == P::stmt_count(pre),
            gqv@.len() == g,
            forall|k: int| 0 <= k < g ==> #[trigger] gqv@[k] == gq(pre, tvi(sc), k),
        decreases ng - g,
    {
        let b = sc != NONE && pin.gstmt[g] == sc + 1;
        gqv.push(b);
        g = g + 1;
    }
    (u, sc, r0, r1, gqv)
}

// ------------------------------------------------------------------------------------------------ pair lookups

/// The lookup inputs over the three storages.
pub fn lk_inputs(nin: &NumIn, pin: &PreIn, tin: &TagIn, Ghost(num): Ghost<Seq<PartView>>, Ghost(pre): Ghost<Seq<PartView>>,
    Ghost(tag): Ghost<Seq<PartView>>) -> (x: LkIn)
    requires num_in_ok(num, *nin), pre_in_ok(pre, *pin), tag_in_ok(tag, *tin),
    ensures lk_in_ok(num, pre, tag, x), x.ntl == tin.tl.n as u64, x.ntl < NONE, x.ppt@.len() == P::pair_count(pre),
{
    let l = tin.tl.off.len();
    proof { assert(tin.tl.n == l - 1); }
    let x = LkIn {
        ptag: pin.tag, pver: pin.ver, ppt: pin.pt, ppv: pin.pv, ppn: pin.pt.len(), ntag: nin.tag, nver: nin.ver, npt: nin.pt, npv: nin.pv, npn: nin.pt.len(),
        ttag: tin.tag, tver: tin.ver, tfirst: tin.tfirst, tvver: tin.tvver, tord: tin.ord, tabs: tin.abs, tlv: tin.tlv,
        tlc: tin.tlc, tn: tin.n, ntl: tin.tl.n as u64,
    };
    x
}

// ------------------------------------------------------------------------------------------------ filings

/// The qualifying sub rows sorted by (sic, cik), with their sic and cik.
pub open spec fn fil_ok(sin: SubIn, lo: int, hi: int, fil: Seq<u64>, fs: Seq<i32>, fc: Seq<i32>) -> bool {
    &&& fs.len() == fil.len() && fc.len() == fil.len()
    &&& fil.no_duplicates()
    &&& forall|f: int| 0 <= f < fil.len() ==> (#[trigger] fil[f]) < sin.n && squal(sin.sic@, sin.sicv@, lo, hi, fil[f] as int)
            && fs[f] == sin.sic@[fil[f] as int] && fc[f] == sin.cik@[fil[f] as int]
    &&& forall|i: u64| i < sin.n && squal(sin.sic@, sin.sicv@, lo, hi, i as int) ==> #[trigger] fil.contains(i)
    &&& forall|f1: int, f2: int| 0 <= f1 <= f2 < fil.len() ==>
            (#[trigger] fs[f1]) < (#[trigger] fs[f2]) || (fs[f1] == fs[f2] && fc[f1] <= fc[f2])
}

/// The sort word of sub row `r` in `sic_order`: 0 for a NULL sic, else `sic + 2^31 + 1` (so at least 1).
pub open spec fn sword(sin: SubIn, r: int) -> int {
    if sin.sicv@[r] == 0 { 0 } else { sin.sic@[r] as int + 0x8000_0001 }
}

/// The words along `sic_order` are nondecreasing, and within one word the ciks are (the key `(word, cik, 0, row)`).
proof fn lemma_sic_order(sub: Seq<PartView>, sin: SubIn, q1: int, q2: int)
    requires sub_in_ok(sub, sin), 0 <= q1 <= q2 < sin.n,
    ensures
        sin.ord@.len() == sin.n, sin.ord@[q1] < sin.n, sin.ord@[q2] < sin.n,
        sword(sin, sin.ord@[q1] as int) <= sword(sin, sin.ord@[q2] as int),
        sword(sin, sin.ord@[q1] as int) == sword(sin, sin.ord@[q2] as int)
            ==> sin.cik@[sin.ord@[q1] as int] <= sin.cik@[sin.ord@[q2] as int],
{
    let ord = sin.ord@;
    S::common::perm::lemma_permutation_facts(S::sic_order(sub), sin.n as nat);
    assert(ord == S::sic_order(sub));
    let (r1, r2) = (ord[q1] as int, ord[q2] as int);
    assert(S::sic_word(sub, r1) as int == sword(sin, r1));
    assert(S::sic_word(sub, r2) as int == sword(sin, r2));
    if q1 < q2 {
        assert(S::key_le(S::sic_key(sub, ord[q1] as int), S::sic_key(sub, ord[q2] as int)));
    }
}

/// The word of the row at `sic_order` position `q`.
fn word_at(sin: &SubIn, q: usize, Ghost(sub): Ghost<Seq<PartView>>) -> (w: u64)
    requires sub_in_ok(sub, *sin), q < sin.n,
    ensures w as int == sword(*sin, sin.ord@[q as int] as int), sin.ord@[q as int] < sin.n,
{
    proof { lemma_sic_order(sub, *sin, q as int, q as int); }
    let r = sin.ord[q] as usize;
    if sin.sicv[r] == 0 { 0 } else { (sin.sic[r] as i64 + 0x8000_0001) as u64 }
}

/// The first `sic_order` position whose word is at least `t` (`n` when none).
fn lower_word(sin: &SubIn, t: u64, Ghost(sub): Ghost<Seq<PartView>>) -> (a: usize)
    requires sub_in_ok(sub, *sin),
    ensures
        a <= sin.n,
        forall|q: int| 0 <= q < a ==> sword(*sin, #[trigger] sin.ord@[q] as int) < t,
        forall|q: int| a <= q < sin.n ==> sword(*sin, #[trigger] sin.ord@[q] as int) >= t,
{
    let mut lo: usize = 0;
    let mut hi: usize = sin.n;
    while lo < hi
        invariant
            sub_in_ok(sub, *sin), 0 <= lo <= hi <= sin.n,
            forall|q: int| 0 <= q < lo ==> sword(*sin, #[trigger] sin.ord@[q] as int) < t,
            forall|q: int| hi <= q < sin.n ==> sword(*sin, #[trigger] sin.ord@[q] as int) >= t,
        decreases hi - lo,
    {
        let m = lo + (hi - lo) / 2;
        let w = word_at(sin, m, Ghost(sub));
        if w < t {
            proof {
                assert forall|q: int| 0 <= q < m + 1 implies sword(*sin, #[trigger] sin.ord@[q] as int) < t by {
                    if q < m { lemma_sic_order(sub, *sin, q, m as int); }
                }
            }
            lo = m + 1;
        } else {
            proof {
                assert forall|q: int| m <= q < sin.n implies sword(*sin, #[trigger] sin.ord@[q] as int) >= t by {
                    if q > m { lemma_sic_order(sub, *sin, m as int, q); }
                }
            }
            hi = m;
        }
    }
    lo
}

/// The qualifying sub rows sorted by (sic, cik): the `sic_order` positions whose word lies in the binding's sic
/// range, one contiguous range found by two binary searches.
pub fn stage_filings(sin: &SubIn, lo: i64, hi: i64, Ghost(sub): Ghost<Seq<PartView>>) -> (r: (Vec<u64>, Vec<i32>, Vec<i32>))
    requires sub_in_ok(sub, *sin),
    ensures fil_ok(*sin, lo as int, hi as int, r.0@, r.1@, r.2@),
{
    // Word bounds of the sic range [lo, hi], clipped to the words of non-NULL sics, [1, 2^32].
    let lw0: i128 = lo as i128 + 0x8000_0001;
    let hw0: i128 = hi as i128 + 0x8000_0001;
    let lw: i128 = if lw0 < 1 { 1 } else { lw0 };
    let hw: i128 = if hw0 > 0x1_0000_0000 { 0x1_0000_0000 } else { hw0 };
    let (a, b) = if lw > hw || lw > 0x1_0000_0000 || hw < 1 {
        (0usize, 0usize)
    } else {
        let a = lower_word(sin, lw as u64, Ghost(sub));
        let b = lower_word(sin, (hw + 1) as u64, Ghost(sub));
        (a, b)
    };
    // A row qualifies exactly when its word is inside [lw, hw].
    proof {
        assert forall|r: int| 0 <= r < sin.n implies
            (squal(sin.sic@, sin.sicv@, lo as int, hi as int, r) <==> (lw <= #[trigger] sword(*sin, r) <= hw)) by {}
    }
    let ghost ordv = sin.ord@;
    proof {
        if a > b {
            // b positions all have words above hw, a positions below lw: impossible when lw <= hw.
            if lw <= hw && lw <= 0x1_0000_0000 && hw >= 1 {
                assert(sword(*sin, ordv[b as int] as int) >= hw + 1);
                assert(sword(*sin, ordv[b as int] as int) < lw);
            }
        }
    }
    let e = if a <= b { b } else { a };
    let mut filv: Vec<u64> = Vec::new();
    let mut fsv: Vec<i32> = Vec::new();
    let mut fcv: Vec<i32> = Vec::new();
    let mut q: usize = a;
    while q < e
        invariant
            sub_in_ok(sub, *sin), a <= q <= e <= sin.n, ordv == sin.ord@,
            filv@.len() == q - a && fsv@.len() == q - a && fcv@.len() == q - a,
            forall|j: int| 0 <= j < q - a ==> #[trigger] filv@[j] == ordv[a + j] && ordv[a + j] < sin.n
                && fsv@[j] == sin.sic@[ordv[a + j] as int] && fcv@[j] == sin.cik@[ordv[a + j] as int],
        decreases e - q,
    {
        proof { lemma_sic_order(sub, *sin, q as int, q as int); }
        let r = sin.ord[q];
        filv.push(r);
        fsv.push(sin.sic[r as usize]);
        fcv.push(sin.cik[r as usize]);
        q = q + 1;
    }
    proof {
        let fil = filv@;
        let nf = fil.len() as int;
        S::common::perm::lemma_permutation_facts(S::sic_order(sub), sin.n as nat);
        assert(ordv == S::sic_order(sub));
        // In range: positions [a, e) have words inside [lw, hw] (empty when the searches were skipped).
        assert forall|j: int| 0 <= j < nf implies lw <= #[trigger] sword(*sin, fil[j] as int) <= hw by {
            assert(fil[j] == ordv[a + j]);
        }
        assert forall|f: int| 0 <= f < nf implies (#[trigger] fil[f]) < sin.n
            && squal(sin.sic@, sin.sicv@, lo as int, hi as int, fil[f] as int)
            && fsv@[f] == sin.sic@[fil[f] as int] && fcv@[f] == sin.cik@[fil[f] as int] by {
            assert(lw <= sword(*sin, fil[f] as int) <= hw);
        }
        // No duplicates: distinct positions of a permutation.
        assert forall|i: int, j: int| 0 <= i < nf && 0 <= j < nf && i != j implies fil[i] != fil[j] by {
            assert(fil[i] == ordv[a + i] && fil[j] == ordv[a + j]);
        }
        assert(fil.no_duplicates());
        // Complete: a qualifying row sits at some position, which lies in [a, e).
        assert forall|i: u64| i < sin.n && squal(sin.sic@, sin.sicv@, lo as int, hi as int, i as int) implies #[trigger] fil.contains(i) by {
            let p = S::common::perm::position_of(ordv, i as int);
            assert(0 <= p < sin.n && ordv[p] == i);
            assert(lw <= sword(*sin, i as int) <= hw);
            assert(lw <= hw && lw <= 0x1_0000_0000 && hw >= 1);
            if p < a { assert(sword(*sin, ordv[p] as int) < lw); }
            if p >= b { assert(sword(*sin, ordv[p] as int) >= hw + 1); }
            assert(a <= p < e);
            assert(fil[p - a] == i);
        }
        // Sorted by (sic, cik): the key order of sic_order, every word inside one non-NULL range.
        assert forall|f1: int, f2: int| 0 <= f1 <= f2 < nf implies
            (#[trigger] fsv@[f1]) < (#[trigger] fsv@[f2]) || (fsv@[f1] == fsv@[f2] && fcv@[f1] <= fcv@[f2]) by {
            lemma_sic_order(sub, *sin, a + f1, a + f2);
            assert(fil[f1] == ordv[a + f1] && fil[f2] == ordv[a + f2]);
            assert(sword(*sin, fil[f1] as int) >= 1 && sword(*sin, fil[f2] as int) >= 1);
        }
    }
    (filv, fsv, fcv)
}

// ------------------------------------------------------------------------------------------------ lookups

pub fn stage_look(dispatch: &mut Dispatch, workers: usize, nin: &NumIn, pin: &PreIn, sin: &SubIn, fil: Arc<Vec<u64>>,
    u: u64, sc: u64, r0: usize, r1: usize, gqv: Arc<Vec<bool>>,
    Ghost(num): Ghost<Seq<PartView>>, Ghost(pre): Ghost<Seq<PartView>>, Ghost(sub): Ghost<Seq<PartView>>, Ghost(b0): Ghost<Seq<u8>>)
    -> (r: Result<Vec<(u64, u64, u64)>, WorkerFailure>)
    requires
        num_in_ok(num, *nin), pre_in_ok(pre, *pin), sub_in_ok(sub, *sin), 1 <= workers <= MAX_WORKERS,
        N::num_layout_ok(num), P::pre_layout_ok(pre), S::sub_layout_ok(sub),
        forall|f: int| 0 <= f < fil@.len() ==> #[trigger] fil@[f] < sin.n,
        uom_ok(num, b0, tvi(u), r0 as int, r1 as int),
        gq_ok(pre, tvi(sc), gqv@),
    ensures
        r matches Ok(v) ==> v@.len() == fil@.len() && forall|f: int| 0 <= f < fil@.len() ==>
            lk_ok(num, pre, b0, tvi(u), tvi(sc), text_entry(sin.adsh_off@, sin.adsh_bytes@, fil@[f] as int), #[trigger] v@[f]),
{
    hide(N::num_layout_ok);
    hide(P::pre_layout_ok);
    hide(S::sub_layout_ok);
    let li = LookIn {
        fil, sadsh_off: sin.adsh_off, sadsh_bytes: sin.adsh_bytes, srank: sin.rank, sn: sin.n, nadsh: nin.adsh, run_adsh: nin.run_adsh,
        r0, r1, padsh: pin.adsh, adsh_subs: pin.adsh_subs, sub_group: pin.sub_group, sub_start: pin.sub_start, ns: pin.nsub,
        gqv, num: Ghost(num), pre: Ghost(pre), b0: Ghost(b0), u: Ghost(tvi(u)), sc: Ghost(tvi(sc)),
    };
    proof {
        reveal(look_in_ok);
        assert(look_in_ok(li));
    }
    lookups(dispatch, workers, li)
}

// ------------------------------------------------------------------------------------------------ the context

pub open spec fn mk_cx(b0: Seq<u8>, b1: Seq<u8>, lo: int, hi: int, num: Seq<PartView>, sub: Seq<PartView>, tag: Seq<PartView>,
    pre: Seq<PartView>, u: int, sc: int, fil: Seq<u64>, look: Seq<(u64, u64, u64)>) -> Cx
{
    Cx {
        b0, b1, lo, hi, num, sub, tag, pre, u, sc,
        t3: Seq::new(P::pair_count(pre) as nat, |q: int| t3c(num, pq_tag(pre, q), pq_ver(pre, q))),
        t6: Seq::new(P::pair_count(pre) as nat, |q: int| t6c(tag, pq_tag(pre, q), pq_ver(pre, q))),
        fil: Seq::new(fil.len(), |f: int| fil[f] as int),
        runs: Seq::new(look.len(), |f: int| tvi(look[f].0)),
        pcs: Seq::new(look.len(), |f: int| tvi(look[f].1)),
    }
}

/// The join over the context's filings (parallel worker tasks over filing ranges).
pub fn stage_join(dispatch: &mut Dispatch, workers: usize, Ghost(cx): Ghost<Cx>, look: Arc<Vec<(u64, u64, u64)>>, nin: &NumIn,
    pin: &PreIn, tin: &TagIn, gqv: Arc<Vec<bool>>, pi: PairInfo, lk: LkIn, Ghost(fil): Ghost<Seq<u64>>)
    -> (r: Result<Vec<CBuf>, WorkerFailure>)
    requires
        1 <= workers <= MAX_WORKERS,
        cx == mk_cx(cx.b0, cx.b1, cx.lo, cx.hi, cx.num, cx.sub, cx.tag, cx.pre, cx.u, cx.sc, fil, look@),
        fil.len() == look@.len(),
        num_in_ok(cx.num, *nin), pre_in_ok(cx.pre, *pin), tag_in_ok(cx.tag, *tin),
        N::num_layout_ok(cx.num), P::pre_layout_ok(cx.pre), T::tag_layout_ok(cx.tag),
        gq_ok(cx.pre, cx.sc, gqv@),
        lk_in_ok(cx.num, cx.pre, cx.tag, lk), lk.ntl == tin.tl.n as u64, lk.ntl < NONE,
        pair_info_ok(cx.num, cx.pre, cx.tag, lk.ntl as int, pi),
        forall|f: int| 0 <= f < look@.len() ==> tvi((#[trigger] look@[f]).0) < N::run_count(cx.num) && tvi(look@[f].1) < P::adsh_count(cx.pre)
            && (look@[f].0 == NONE ==> look@[f].1 == NONE)
            && look@[f].2 as int == (if look@[f].0 != NONE && look@[f].1 != NONE { qn_spec(cx.pre, cx.sc, look@[f].1 as int) } else { 0 })
            && look@[f].2 <= P::row_count(cx.pre),
    ensures
        r matches Ok(out) ==> join_out_ok(cx, tin.tl.n as u64, cflat(out@)) && tin.tl.n == ntl(cx) && cflat(out@).len() <= usize::MAX,
{
    hide(N::num_layout_ok);
    hide(P::pre_layout_ok);
    hide(T::tag_layout_ok);
    let ji = JoinIn {
        look, run_start: nin.run_start, nrun1: nin.run_start.len(), ntv: nin.tv, nval: nin.val, nrows: nin.tv.len(),
        adsh_subs: pin.adsh_subs, sub_group: pin.sub_group, sub_start: pin.sub_start, ns: pin.nsub, gqv,
        ptv: pin.tv, prows: pin.nrows, info: Arc::new(pi.info), bits: Arc::new(pi.bits), pref: Arc::new(pi.pref), lk,
        ntl: tin.tl.n as u64,
    };
    proof {
        assert(nin.tv@.len() == N::row_count(cx.num)) by { reveal(N::num_layout_ok); }
        reveal(join_in_ok);
        assert(ji.ntl as int == ntl(cx));
        assert forall|f: int| 0 <= f < cx.fil.len() implies #[trigger] cx.runs[f] == tvi(ji.look@[f].0) && cx.pcs[f] == tvi(ji.look@[f].1)
            && cx.runs[f] < N::run_count(cx.num) && cx.pcs[f] < P::adsh_count(cx.pre)
            && ji.look@[f].2 as int == (if cx.runs[f] >= 0 && cx.pcs[f] >= 0 { qn_spec(cx.pre, cx.sc, cx.pcs[f]) } else { 0 })
            && ji.look@[f].2 <= ji.prows by {
            assert(tvi(look@[f].0) < N::run_count(cx.num));
        }
        assert(join_in_ok(cx, ji));
    }
    join_par(dispatch, workers, Ghost(cx), ji)
}

} // verus!
