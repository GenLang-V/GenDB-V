//! The keys of the selected part rows (`joined::sel`), in part-row order, as a `common::keyset::KeySet` (slot `s`
//! is the `s`-th selected part row `srows[s]`), built from the part pass's bits on the calling thread, with its prefix directory (`keyset_index`).
//!
//! The part key column is duplicate-free, so the listed keys are distinct, and a lineitem row's part key is
//! listed exactly when the row joins a selected part (`lemma_inrow_insel`).
use vstd::prelude::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::agent::tables::*;
use crate::agent::joined::*;
use crate::agent::parts::pbits_ok;
use crate::agent::common::bits::*;
use crate::agent::common::selection::*;
use crate::agent::common::keyset::*;

verus! {

/// Row `r` is a selected part row.
pub open spec fn selr(sv: StoresView, ps: Seq<Literal>) -> spec_fn(int) -> bool {
    |r: int| 0 <= r < n_p(sv) && sel(sv, ps, r)
}

/// `keys` lists the keys of the selected part rows `srows` (all of them, ascending).
pub open spec fn keys_ok(keys: Seq<i64>, srows: Seq<int>, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& srows == range_filter(0, n_p(sv) as int, selr(sv, ps))
    &&& keys.len() == srows.len()
    &&& forall|s: int| 0 <= s < keys.len() ==> #[trigger] keys[s] == p_key(sv)[srows[s]]
}

/// Lineitem row `l`'s part key is listed.
pub open spec fn inrow(keys: Seq<i64>, sv: StoresView) -> spec_fn(int) -> bool {
    |l: int| contains_key(keys, l_pkey(sv)[l])
}

/// The listed keys are distinct.
pub proof fn lemma_keys_distinct(keys: Seq<i64>, srows: Seq<int>, sv: StoresView, ps: Seq<Literal>)
    requires keys_ok(keys, srows, sv, ps), keys_unique(p_key(sv)),
    ensures forall|s: int, t: int| 0 <= s < keys.len() && 0 <= t < keys.len() && #[trigger] keys[s] == #[trigger] keys[t] ==> s == t,
{
    lemma_range_filter_members(0, n_p(sv) as int, selr(sv, ps));
    assert forall|s: int, t: int| 0 <= s < keys.len() && 0 <= t < keys.len() && #[trigger] keys[s] == #[trigger] keys[t] implies s == t by {
        if s < t {
            assert(srows[s] < srows[t]);
        } else if t < s {
            assert(srows[t] < srows[s]);
        }
    }
}

/// A lineitem row's part key is listed exactly when the row joins a selected part.
pub proof fn lemma_inrow_insel(keys: Seq<i64>, srows: Seq<int>, sv: StoresView, ps: Seq<Literal>, l: int)
    requires keys_ok(keys, srows, sv, ps), keys_unique(p_key(sv)), 0 <= l < n_l(sv),
    ensures (inrow(keys, sv))(l) == insel(sv, ps, l),
{
    let sr = selr(sv, ps);
    lemma_range_filter_members(0, n_p(sv) as int, sr);
    if contains_key(keys, l_pkey(sv)[l]) {
        let s = choose|s: int| 0 <= s < keys.len() && #[trigger] keys[s] == l_pkey(sv)[l];
        let a = srows[s];
        assert(sr(a));
        lemma_part_is(sv, l, a);
    }
    if insel(sv, ps, l) {
        lemma_part_of(sv, l);
        let a = part_of(sv, l);
        assert(sr(a));
        let s = choose|s: int| 0 <= s < srows.len() && #[trigger] srows[s] == a;
        assert(keys[s] == l_pkey(sv)[l]);
    }
}

/// The key set of the selected part rows, from the part pass's bits, with its directory. Each word's set bits
/// are visited lowest first (`trailing_zeros`, then the lowest bit cleared), so a word costs one test plus one
/// step per selected row.
pub fn build_keys(bits: &Vec<u64>, p_key_col: &'static [i64], np: usize, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: (KeySet, Ghost<Seq<int>>))
    requires pbits_ok(bits@, sv, ps), p_key_col@ == p_key(sv), np == n_p(sv), p_key(sv).len() == n_p(sv),
    ensures keyset_wf(&r.0), keys_ok(r.0.keys@, r.1@, sv, ps),
{
    let sr = Ghost(selr(sv, ps));
    let nw = bits.len();
    let mut ks = keyset_new();
    let ghost mut srows: Seq<int> = Seq::empty();
    let mut j: usize = 0;
    while j < nw
        invariant
            pbits_ok(bits@, sv, ps), p_key_col@ == p_key(sv), np == n_p(sv), p_key(sv).len() == n_p(sv),
            nw == bits@.len(), j <= nw, sr@ == selr(sv, ps),
            keyset_wf(&ks), ks.nd == 0,
            srows == range_filter(0, 64 * j, sr@),
            ks.keys@.len() == srows.len(),
            forall|s: int| 0 <= s < srows.len() ==> #[trigger] ks.keys@[s] == p_key(sv)[srows[s]],
        decreases nw - j,
    {
        let m0 = bits[j];
        let ghost row0 = 64 * j as int;
        // every row of the word: bit u is row `64 j + u`
        assert forall|u: int| 0 <= u < 64 implies #[trigger] bit(m0, u as u64) == sr@(row0 + u) by {
            let r = row0 + u;
            assert(r / 64 == j as int && r % 64 == u) by (nonlinear_arith) requires r == 64 * j + u, 0 <= u < 64;
            assert(word_bit(bits@, r) == (r < n_p(sv) && sel(sv, ps, r)));
        }
        assert(64 * j < 64 * nw) by (nonlinear_arith) requires j < nw;
        let base = 64 * j;
        let mut m = m0;
        let ghost mut cut: int = 0;
        while m != 0
            invariant
                p_key_col@ == p_key(sv), np == n_p(sv), p_key(sv).len() == n_p(sv), sr@ == selr(sv, ps),
                base == row0, row0 >= 0, 0 <= cut <= 64,
                forall|u: int| 0 <= u < 64 ==> #[trigger] bit(m0, u as u64) == sr@(row0 + u),
                forall|u: u64| u < 64 ==> #[trigger] bit(m, u) == (bit(m0, u) && u >= cut),
                keyset_wf(&ks), ks.nd == 0,
                srows == range_filter(0, row0 + cut, sr@),
                ks.keys@.len() == srows.len(),
                forall|s: int| 0 <= s < srows.len() ==> #[trigger] ks.keys@[s] == p_key(sv)[srows[s]],
            decreases m,
        {
            let tz = m.trailing_zeros();
            proof { lemma_first_bit(m); }
            let u = tz as u64;
            proof {
                // the rows between the cut and the lowest set bit are not selected
                assert(u >= cut);
                assert forall|r: int| row0 + cut <= r < row0 + u implies !#[trigger] sr@(r) by {
                    let v = (r - row0) as u64;
                    assert(!bit(m, v));
                    assert(bit(m0, v) == sr@(row0 + v));
                }
                lemma_rf_tail(row0 + cut, row0 + u, sr@);
                assert(bit(m0, u) == sr@(row0 + u));
                lemma_range_filter_members(0, row0 + u, sr@);
                assert(srows.len() <= row0 + u);
            }
            let row = base + u as usize;
            keyset_push(&mut ks, p_key_col[row]);
            proof {
                srows = srows.push(row as int);
            }
            let ghost m1 = m;
            m = m & (m - 1);
            proof {
                assert forall|v: u64| v < 64 implies #[trigger] bit(m, v) == (bit(m0, v) && v >= u + 1) by {
                    lemma_clear_lowest(m1, u, v);
                    if cut <= v && v < u {
                        assert(!bit(m1, v));
                    }
                }
                assert(m1 != 0 ==> m1 & sub(m1, 1) < m1) by (bit_vector);
                cut = u + 1;
            }
        }
        proof {
            // no selected row is left in the word
            assert forall|r: int| row0 + cut <= r < row0 + 64 implies !#[trigger] sr@(r) by {
                let v = (r - row0) as u64;
                lemma_bit_zero(v);
                assert(bit(m0, v) == sr@(row0 + v));
            }
            lemma_rf_tail(row0 + cut, row0 + 64, sr@);
        }
        j = j + 1;
    }
    proof {
        // past the last row nothing is selected
        let nb = 64 * nw as int;
        assert(nb >= n_p(sv));
        lemma_rf_tail(n_p(sv) as int, nb, sr@);
    }
    keyset_index(&mut ks);
    (ks, Ghost(srows))
}

/// Rows from `a` on that are not selected (`p` false past the table) add nothing.
proof fn lemma_rf_tail(a: int, b: int, p: spec_fn(int) -> bool)
    requires a <= b, forall|r: int| a <= r < b ==> !#[trigger] p(r),
    ensures range_filter(0, b, p) == range_filter(0, a, p),
    decreases b - a,
{
    if b > a {
        lemma_rf_tail(a, b - 1, p);
    }
}

} // verus!
