//! The staged gather of a block's candidates (`gather_staged`): instead of following one candidate through all its
//! tests, each stage runs one test over the whole candidate list and keeps the survivors, so the random reads of a
//! stage (one per candidate, independent of each other) overlap in the memory system:
//! 1. `stage_codes`: the branch code of the candidate's part key from the key map (0: no qualifying part), kept when
//!    nonzero (`qk`);
//! 2. `stage_qty`: `l_quantity` inside the window of a branch of the code (`qq`);
//! 3. `stage_ship`: the ship instruction and mode (`qs`);
//! 4. the volume of every survivor, which qualifies, is added to the accumulator.
//! A dropped candidate does not qualify, so the survivors' totals are the candidates' (`lemma_tlist_filter`). The
//! lists live in two `u32` offset buffers used alternately (`sel_matches`) and a code buffer.
use vstd::prelude::*;
use crate::spec::ast::Literal;
use crate::spec::numeric::abs;
use crate::gendb_entry::stores::StoresView;
use crate::agent::tables::*;
use crate::agent::line::*;
use crate::agent::cols::*;
use crate::agent::bind::*;
use crate::agent::keymap::*;
use crate::agent::scan::*;
use crate::agent::common::selection::*;

verus! {

/// The candidate's part key has a qualifying part.
pub open spec fn qk(sv: StoresView, ps: Seq<Literal>) -> spec_fn(int) -> bool { |l: int| qkey(sv, ps, l_pkey(sv)[l]) }

/// Some branch holds on the candidate's part and its quantity.
pub open spec fn qq(sv: StoresView, ps: Seq<Literal>) -> spec_fn(int) -> bool {
    |l: int| (lb(sv, ps, 0, l) && qcond(sv, ps, 0, l)) || (lb(sv, ps, 1, l) && qcond(sv, ps, 1, l))
        || (lb(sv, ps, 2, l) && qcond(sv, ps, 2, l))
}

/// The candidate's ship instruction and mode.
pub open spec fn qs(sv: StoresView) -> spec_fn(int) -> bool { |l: int| ship_ok(sv, l) }

/// The rows of a list are rows of the table.
pub open spec fn rows_in(s: Seq<int>, n: int) -> bool { forall|i: int| 0 <= i < s.len() ==> 0 <= #[trigger] s[i] < n }

/// A filtered list keeps rows of the table that satisfy the filter.
pub proof fn lemma_filter_in(s: Seq<int>, q: spec_fn(int) -> bool, n: int)
    requires rows_in(s, n),
    ensures rows_in(seq_filter(s, q), n), forall|i: int| 0 <= i < seq_filter(s, q).len() ==> q(#[trigger] seq_filter(s, q)[i]),
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies 0 <= #[trigger] d[i] < n by { assert(d[i] == s[i]); }
        lemma_filter_in(d, q, n);
        let f = seq_filter(d, q);
        if q(s.last()) {
            assert forall|i: int| 0 <= i < f.push(s.last()).len() implies 0 <= #[trigger] f.push(s.last())[i] < n && q(f.push(s.last())[i]) by {
                if i < f.len() { assert(f.push(s.last())[i] == f[i]); }
            }
        }
    }
}

/// Dropping rows that do not qualify keeps the totals of a list.
pub proof fn lemma_tlist_filter(sv: StoresView, ps: Seq<Literal>, s: Seq<int>, q: spec_fn(int) -> bool)
    requires forall|i: int| 0 <= i < s.len() && !q(#[trigger] s[i]) ==> !qual(sv, ps, s[i]),
    ensures tlist(sv, ps, seq_filter(s, q)) == tlist(sv, ps, s),
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        assert forall|i: int| 0 <= i < d.len() && !q(#[trigger] d[i]) implies !qual(sv, ps, d[i]) by { assert(d[i] == s[i]); }
        lemma_tlist_filter(sv, ps, d, q);
        let x = s.last();
        assert(s == d.push(x)) by { assert(s =~= d.push(x)); }
        lemma_tlist_push(sv, ps, d, x);
        if q(x) {
            lemma_seq_filter_push(d, x, q);
            lemma_tlist_push(sv, ps, seq_filter(d, q), x);
        } else {
            lemma_seq_filter_push(d, x, q);
            assert(!qual(sv, ps, x));
            assert(tot1(sv, ps, x) == tot_zero());
            assert(tot_plus(tlist(sv, ps, d), tot_zero()) == tlist(sv, ps, d));
        }
    }
}

/// One more element of a prefix, filtered.
proof fn lemma_take_filter(s: Seq<int>, i: int, q: spec_fn(int) -> bool)
    requires 0 <= i < s.len(),
    ensures seq_filter(s.take(i + 1), q) == if q(s[i]) { seq_filter(s.take(i), q).push(s[i]) } else { seq_filter(s.take(i), q) },
{
    lemma_take_step(s, i);
    lemma_seq_filter_push(s.take(i), s[i], q);
}

/// The codes of the listed rows' part keys.
pub open spec fn codes_of(sv: StoresView, ps: Seq<Literal>, tags: Seq<u8>, s: Seq<int>) -> bool {
    &&& s.len() <= tags.len()
    &&& forall|t: int| 0 <= t < s.len() ==> #[trigger] tags[t] == code(sv, ps, l_pkey(sv)[s[t]])
}

// ------------------------------------------------------------------------------------------------ stages

/// Stage 1: the candidates whose part key has a qualifying part, with its branch code.
fn stage_codes(c: &ScanCols, km: &KeyMap, b: usize, k: usize, src: &Vec<u32>, dst: &mut Vec<u32>, tags: &mut Vec<u8>,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(s): Ghost<Seq<int>>) -> (k2: usize)
    requires
        line_cols_ok(c.line, sv), keymap_ok(*km, sv, ps), model_ok(sv),
        sel_matches(src@, k as int, b as int, s), rows_in(s, c.line.nl as int), k <= src@.len(),
        old(dst)@.len() == src@.len(), old(tags)@.len() == src@.len(),
    ensures
        final(dst)@.len() == src@.len(), final(tags)@.len() == src@.len(),
        sel_matches(final(dst)@, k2 as int, b as int, seq_filter(s, qk(sv, ps))),
        codes_of(sv, ps, final(tags)@, seq_filter(s, qk(sv, ps))),
    no_unwind
{
    let ghost q = qk(sv, ps);
    let mut k2: usize = 0;
    let mut i: usize = 0;
    proof { assert(s.take(0) =~= Seq::<int>::empty()); }
    while i < k
        invariant
            line_cols_ok(c.line, sv), keymap_ok(*km, sv, ps), model_ok(sv), q == qk(sv, ps),
            sel_matches(src@, k as int, b as int, s), rows_in(s, c.line.nl as int), k <= src@.len(),
            dst@.len() == src@.len(), tags@.len() == src@.len(), i <= k, k2 <= i,
            sel_matches(dst@, k2 as int, b as int, seq_filter(s.take(i as int), q)),
            codes_of(sv, ps, tags@, seq_filter(s.take(i as int), q)),
        decreases k - i,
    {
        let off = src[i];
        let l = b + off as usize;
        proof { assert(l as int == s[i as int]); }
        let key = c.line.pkey[l];
        let tag = key_code(km, key, Ghost(sv), Ghost(ps));
        let keep = tag != 0u8;
        proof {
            lemma_code3(kbit(sv, ps, 0, key as int), kbit(sv, ps, 1, key as int), kbit(sv, ps, 2, key as int));
            assert(keep == q(l as int));
            lemma_take_filter(s, i as int, q);
            lemma_sel_write(dst@, k2 as int, b as int, seq_filter(s.take(i as int), q), off, keep);
        }
        let ghost f0 = seq_filter(s.take(i as int), q);
        let ghost t0 = tags@;
        dst[k2] = off;
        tags[k2] = tag;
        proof {
            let f1 = seq_filter(s.take(i + 1), q);
            assert forall|t: int| 0 <= t < f1.len() implies #[trigger] tags@[t] == code(sv, ps, l_pkey(sv)[f1[t]]) by {
                if t < f0.len() {
                    assert(f1[t] == f0[t] && tags@[t] == t0[t]);
                }
            }
        }
        if keep {
            k2 = k2 + 1;
        }
        i = i + 1;
    }
    proof { assert(s.take(k as int) =~= s); }
    k2
}

/// Stage 2: the candidates whose quantity lies in the window of a branch their part satisfies.
fn stage_qty(c: &ScanCols, x: &Bind, km: &KeyMap, b: usize, k: usize, src: &Vec<u32>, tags: &Vec<u8>, dst: &mut Vec<u32>,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(s): Ghost<Seq<int>>) -> (k3: usize)
    requires
        line_cols_ok(c.line, sv), keymap_ok(*km, sv, ps), model_ok(sv), bind_ok(*x, ps),
        sel_matches(src@, k as int, b as int, s), rows_in(s, c.line.nl as int), k <= src@.len(),
        codes_of(sv, ps, tags@, s), old(dst)@.len() == src@.len(),
    ensures
        final(dst)@.len() == src@.len(),
        sel_matches(final(dst)@, k3 as int, b as int, seq_filter(s, qq(sv, ps))),
    no_unwind
{
    let ghost q = qq(sv, ps);
    let mut k3: usize = 0;
    let mut i: usize = 0;
    proof { assert(s.take(0) =~= Seq::<int>::empty()); }
    while i < k
        invariant
            line_cols_ok(c.line, sv), keymap_ok(*km, sv, ps), model_ok(sv), bind_ok(*x, ps), q == qq(sv, ps),
            sel_matches(src@, k as int, b as int, s), rows_in(s, c.line.nl as int), k <= src@.len(),
            codes_of(sv, ps, tags@, s), dst@.len() == src@.len(), i <= k, k3 <= i,
            sel_matches(dst@, k3 as int, b as int, seq_filter(s.take(i as int), q)),
        decreases k - i,
    {
        let off = src[i];
        let l = b + off as usize;
        let tag = tags[i];
        let qv = c.line.qty[l];
        let keep = (tag & 1u8 != 0u8 && x.lo0 <= qv && qv <= x.hi0) || (tag & 2u8 != 0u8 && x.lo1 <= qv && qv <= x.hi1)
            || (tag & 4u8 != 0u8 && x.lo2 <= qv && qv <= x.hi2);
        proof {
            let li = l as int;
            assert(li == s[i as int]);
            let key = l_pkey(sv)[li];
            assert(tag == code(sv, ps, key));
            lemma_code3(kbit(sv, ps, 0, key as int), kbit(sv, ps, 1, key as int), kbit(sv, ps, 2, key as int));
            lemma_probe(sv, ps, *km, li);
            assert(kbit(sv, ps, 0, key as int) == lb(sv, ps, 0, li));
            assert(kbit(sv, ps, 1, key as int) == lb(sv, ps, 1, li));
            assert(kbit(sv, ps, 2, key as int) == lb(sv, ps, 2, li));
            assert(keep == q(li));
            lemma_take_filter(s, i as int, q);
            lemma_sel_write(dst@, k3 as int, b as int, seq_filter(s.take(i as int), q), off, keep);
        }
        dst[k3] = off;
        if keep {
            k3 = k3 + 1;
        }
        i = i + 1;
    }
    proof { assert(s.take(k as int) =~= s); }
    k3
}

/// Stage 3: the candidates shipped by air and delivered in person.
fn stage_ship(c: &ScanCols, b: usize, k: usize, src: &Vec<u32>, dst: &mut Vec<u32>,
    Ghost(sv): Ghost<StoresView>, Ghost(s): Ghost<Seq<int>>) -> (k4: usize)
    requires
        line_cols_ok(c.line, sv),
        sel_matches(src@, k as int, b as int, s), rows_in(s, c.line.nl as int), k <= src@.len(), old(dst)@.len() == src@.len(),
    ensures
        final(dst)@.len() == src@.len(),
        sel_matches(final(dst)@, k4 as int, b as int, seq_filter(s, qs(sv))),
    no_unwind
{
    let ghost q = qs(sv);
    let mut k4: usize = 0;
    let mut i: usize = 0;
    proof { assert(s.take(0) =~= Seq::<int>::empty()); }
    while i < k
        invariant
            line_cols_ok(c.line, sv), q == qs(sv),
            sel_matches(src@, k as int, b as int, s), rows_in(s, c.line.nl as int), k <= src@.len(),
            dst@.len() == src@.len(), i <= k, k4 <= i,
            sel_matches(dst@, k4 as int, b as int, seq_filter(s.take(i as int), q)),
        decreases k - i,
    {
        let off = src[i];
        let l = b + off as usize;
        proof { assert(l as int == s[i as int]); }
        let keep = ship_at(&c.line, l, Ghost(sv));
        proof {
            lemma_take_filter(s, i as int, q);
            lemma_sel_write(dst@, k4 as int, b as int, seq_filter(s.take(i as int), q), off, keep);
        }
        dst[k4] = off;
        if keep {
            k4 = k4 + 1;
        }
        i = i + 1;
    }
    proof { assert(s.take(k as int) =~= s); }
    k4
}

/// Stage 4: adds the volumes of the listed rows, which qualify.
fn stage_sum(c: &ScanCols, b: usize, k: usize, src: &Vec<u32>, acc: &mut Acc,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(s): Ghost<Seq<int>>, Ghost(t0): Ghost<Tot>)
    requires
        line_cols_ok(c.line, sv), model_ok(sv),
        sel_matches(src@, k as int, b as int, s), rows_in(s, c.line.nl as int),
        forall|i: int| 0 <= i < s.len() ==> qual(sv, ps, #[trigger] s[i]),
        acc_ok(*old(acc), t0), t0.cnt + k <= 0xffff_ffff_ffff_ffff,
    ensures acc_ok(*final(acc), tot_plus(t0, tlist(sv, ps, s))),
    no_unwind
{
    let mut i: usize = 0;
    proof { assert(s.take(0) =~= Seq::<int>::empty()); }
    while i < k
        invariant
            line_cols_ok(c.line, sv), model_ok(sv),
            sel_matches(src@, k as int, b as int, s), rows_in(s, c.line.nl as int),
            forall|i: int| 0 <= i < s.len() ==> qual(sv, ps, #[trigger] s[i]),
            i <= k, t0.cnt + k <= 0xffff_ffff_ffff_ffff,
            acc_ok(*acc, tot_plus(t0, tlist(sv, ps, s.take(i as int)))),
            tot_plus(t0, tlist(sv, ps, s.take(i as int))).cnt == t0.cnt + i,
        decreases k - i,
    {
        let off = src[i];
        let l = b + off as usize;
        let ghost li = l as int;
        proof {
            assert(li == s[i as int]);
            lemma_take_step(s, i as int);
            lemma_tlist_push(sv, ps, s.take(i as int), li);
            assert(qual(sv, ps, li));
            assert(num15(l_price(sv)[li]) && num15(l_disc(sv)[li]));
        }
        let pr = c.line.price[l];
        let dc = c.line.disc[l];
        proof {
            assert(-10_000_000_000_000_000_000_000_000_000_000 < (pr as int) * (100 - dc as int)
                < 10_000_000_000_000_000_000_000_000_000_000) by (nonlinear_arith)
                requires -1_000_000_000_000_000 < (pr as int) < 1_000_000_000_000_000,
                    -1_000_000_000_000_000 < (dc as int) < 1_000_000_000_000_000;
        }
        let v = pr * (100 - dc);
        let ghost tt = tot_plus(t0, tlist(sv, ps, s.take(i as int)));
        proof {
            assert(v as int == vol(sv, li));
            assert(tot1(sv, ps, li) == (Tot { cnt: 1, s_all: v as int, a_all: abs(v as int) }));
        }
        acc_add(acc, v, Ghost(tt));
        i = i + 1;
    }
    proof { assert(s.take(k as int) =~= s); }
}

/// The candidates of a block (`sel`, offsets from `b`), staged; `sel2` and `tags` are scratch buffers.
pub fn gather_staged(c: &ScanCols, x: &Bind, km: &KeyMap, b: usize, k: usize, sel: &mut Vec<u32>, sel2: &mut Vec<u32>,
    tags: &mut Vec<u8>, acc: &mut Acc,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(s): Ghost<Seq<int>>, Ghost(t0): Ghost<Tot>)
    requires
        line_cols_ok(c.line, sv), model_ok(sv), bind_ok(*x, ps), keymap_ok(*km, sv, ps),
        sel_matches(old(sel)@, k as int, b as int, s), rows_in(s, c.line.nl as int), k <= old(sel)@.len(),
        old(sel2)@.len() == old(sel)@.len(), old(tags)@.len() == old(sel)@.len(),
        acc_ok(*old(acc), t0), t0.cnt + k <= 0xffff_ffff_ffff_ffff,
    ensures
        final(sel)@.len() == old(sel)@.len(), final(sel2)@.len() == old(sel)@.len(), final(tags)@.len() == old(sel)@.len(),
        acc_ok(*final(acc), tot_plus(t0, tlist(sv, ps, s))),
    no_unwind
{
    hide(keymap_ok);
    hide(model_ok);
    hide(line_cols_ok);
    hide(bind_ok);
    hide(tlist);
    hide(seq_filter);
    hide(qual);
    let ghost q1 = qk(sv, ps);
    let ghost q2 = qq(sv, ps);
    let ghost q3 = qs(sv);
    proof { reveal(line_cols_ok); }
    let k2 = stage_codes(c, km, b, k, sel, sel2, tags, Ghost(sv), Ghost(ps), Ghost(s));
    let ghost s2 = seq_filter(s, q1);
    proof { lemma_filter_in(s, q1, c.line.nl as int); lemma_rf_len_filter(s, q1); }
    let k3 = stage_qty(c, x, km, b, k2, sel2, tags, sel, Ghost(sv), Ghost(ps), Ghost(s2));
    let ghost s3 = seq_filter(s2, q2);
    proof { lemma_filter_in(s2, q2, c.line.nl as int); lemma_rf_len_filter(s2, q2); }
    let k4 = stage_ship(c, b, k3, sel, sel2, Ghost(sv), Ghost(s3));
    let ghost s4 = seq_filter(s3, q3);
    proof {
        lemma_filter_in(s3, q3, c.line.nl as int);
        lemma_rf_len_filter(s3, q3);
        lemma_drop_codes(sv, ps, *km, s, c.line.nl as int);
        lemma_drop_qty(sv, ps, s2);
        lemma_drop_ship(sv, ps, s3);
        lemma_survivors(sv, ps, s2);
        assert(s4 == seq_filter(seq_filter(s2, qq(sv, ps)), qs(sv)));
        assert forall|i: int| 0 <= i < s4.len() implies qual(sv, ps, #[trigger] s4[i]) by {}
    }
    stage_sum(c, b, k4, sel2, acc, Ghost(sv), Ghost(ps), Ghost(s4), Ghost(t0));
}

/// Stage 1 drops no qualifying candidate.
proof fn lemma_drop_codes(sv: StoresView, ps: Seq<Literal>, km: KeyMap, s: Seq<int>, n: int)
    requires keymap_ok(km, sv, ps), model_ok(sv), rows_in(s, n), n == n_l(sv),
    ensures tlist(sv, ps, seq_filter(s, qk(sv, ps))) == tlist(sv, ps, s),
{
    let q = qk(sv, ps);
    assert forall|i: int| 0 <= i < s.len() && !q(#[trigger] s[i]) implies !qual(sv, ps, s[i]) by {
        lemma_probe(sv, ps, km, s[i]);
        lemma_qual_lb(sv, ps, s[i]);
    }
    lemma_tlist_filter(sv, ps, s, q);
}

/// Stage 2 drops no qualifying candidate.
proof fn lemma_drop_qty(sv: StoresView, ps: Seq<Literal>, s: Seq<int>)
    ensures tlist(sv, ps, seq_filter(s, qq(sv, ps))) == tlist(sv, ps, s),
{
    let q = qq(sv, ps);
    assert forall|i: int| 0 <= i < s.len() && !q(#[trigger] s[i]) implies !qual(sv, ps, s[i]) by {
        lemma_qual_lb(sv, ps, s[i]);
    }
    lemma_tlist_filter(sv, ps, s, q);
}

/// Stage 3 drops no qualifying candidate.
proof fn lemma_drop_ship(sv: StoresView, ps: Seq<Literal>, s: Seq<int>)
    ensures tlist(sv, ps, seq_filter(s, qs(sv))) == tlist(sv, ps, s),
{
    let q = qs(sv);
    assert forall|i: int| 0 <= i < s.len() && !q(#[trigger] s[i]) implies !qual(sv, ps, s[i]) by {
        lemma_qual_lb(sv, ps, s[i]);
    }
    lemma_tlist_filter(sv, ps, s, q);
}

/// Every survivor of stages 2 and 3 qualifies.
proof fn lemma_survivors(sv: StoresView, ps: Seq<Literal>, s2: Seq<int>)
    ensures ({
        let s3 = seq_filter(s2, qq(sv, ps));
        let s4 = seq_filter(s3, qs(sv));
        forall|i: int| 0 <= i < s4.len() ==> qual(sv, ps, #[trigger] s4[i])
    }),
{
    let s3 = seq_filter(s2, qq(sv, ps));
    let s4 = seq_filter(s3, qs(sv));
    lemma_filter_holds(s2, qq(sv, ps));
    lemma_filter_holds(s3, qs(sv));
    assert forall|i: int| 0 <= i < s4.len() implies qual(sv, ps, #[trigger] s4[i]) by {
        lemma_filter_sub(s3, qs(sv), i);
        let j = choose|j: int| 0 <= j < s3.len() && #[trigger] s3[j] == s4[i];
        assert((qq(sv, ps))(s3[j]));
        assert((qs(sv))(s4[i]));
        lemma_qual_lb(sv, ps, s4[i]);
    }
}

/// The elements of a filtered list satisfy the filter.
proof fn lemma_filter_holds(s: Seq<int>, q: spec_fn(int) -> bool)
    ensures forall|i: int| 0 <= i < seq_filter(s, q).len() ==> q(#[trigger] seq_filter(s, q)[i]),
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        lemma_filter_holds(d, q);
        let f = seq_filter(d, q);
        if q(s.last()) {
            assert forall|i: int| 0 <= i < f.push(s.last()).len() implies q(#[trigger] f.push(s.last())[i]) by {
                if i < f.len() { assert(f.push(s.last())[i] == f[i]); }
            }
        }
    }
}

/// A filtered list is no longer than the list.
proof fn lemma_rf_len_filter(s: Seq<int>, q: spec_fn(int) -> bool)
    ensures seq_filter(s, q).len() <= s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_rf_len_filter(s.drop_last(), q);
    }
}

/// An element of a filtered list is an element of the list.
proof fn lemma_filter_sub(s: Seq<int>, q: spec_fn(int) -> bool, i: int)
    requires 0 <= i < seq_filter(s, q).len(),
    ensures exists|j: int| 0 <= j < s.len() && #[trigger] s[j] == seq_filter(s, q)[i],
    decreases s.len(),
{
    let d = s.drop_last();
    let f = seq_filter(d, q);
    if i < f.len() {
        lemma_filter_sub(d, q, i);
        let j = choose|j: int| 0 <= j < d.len() && #[trigger] d[j] == f[i];
        assert(s[j] == d[j]);
        if q(s.last()) {
            assert(seq_filter(s, q)[i] == f[i]);
        }
    } else {
        assert(q(s.last()));
        assert(seq_filter(s, q)[i] == s.last());
        assert(s[s.len() - 1] == s.last());
    }
}

} // verus!
