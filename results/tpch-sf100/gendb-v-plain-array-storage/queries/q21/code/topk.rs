//! The first `TOPK` groups by `numwait DESC, s_name` (the statement's ORDER BY on the group rows `grow`): insertion
//! into a sorted list of at most `TOPK` group indices (`top`).
//!
//! Invariant after groups `0..i` (`top_inv`): `sel` holds `min(i, TOPK)` distinct indices below `i`, sorted by the
//! ORDER BY comparison of their rows (`ccmp`); while fewer than `TOPK` were seen every index is selected; and every
//! selected group sorts no later than every unselected one. A new group enters after every selected group that does
//! not sort after it; when the list is full, the last one leaves. (The list logic follows an admitted query's
//! top-k; the comparison is `keys_cmp` on the rows, a total preorder by `bridge::order`.)
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::order::*;
use crate::spec::ast::OrderKey;
use crate::spec::text::lex_cmp;
use crate::spec::scalar::compare;
use crate::spec::numeric::sign;
use crate::gendb_entry::stores::StoresView;
use crate::link::query::text_at;
use crate::bridge::order::{keys_ok, key_ok, lemma_keys_cmp_antisym, lemma_keys_cmp_trans, lemma_lex_cmp_antisym};
use crate::agent::cols::*;
use crate::agent::scan::SupMap;
use crate::agent::denot::q_order_keys;
use crate::agent::groups::*;

verus! {

/// Rows the statement returns at most (`LIMIT 100`).
pub const TOPK: usize = 100;

/// The output row of group `g`: `s_name, numwait`.
pub open spec fn grow(sv: StoresView, m: SupMap, grep: Seq<usize>, gt: Seq<u64>, g: int) -> Row {
    seq![Val::Text(gname(sv, m, grep[g] as int)), Val::Int(gt[g] as int)]
}

/// The output rows of all groups.
pub open spec fn grows(sv: StoresView, m: SupMap, grep: Seq<usize>, gt: Seq<u64>) -> Seq<Row> {
    Seq::new(grep.len(), |g: int| grow(sv, m, grep, gt, g))
}

/// ORDER BY key families: `numwait` an integer (1), `s_name` a text (3).
pub open spec fn ofams() -> Seq<int> { seq![1int, 3int] }

/// A row `(text, int)` has the ORDER BY key families.
pub proof fn lemma_row_keys_ok(n: Seq<u8>, t: int)
    ensures keys_ok(q_order_keys(), ofams(), seq![Val::Text(n), Val::Int(t)]),
{
    let keys = q_order_keys();
    let r = seq![Val::Text(n), Val::Int(t)];
    assert(key_ok(keys[0], ofams()[0], r));
    assert(key_ok(keys[1], ofams()[1], r));
}

/// The ORDER BY comparison of two rows `(text, int)`: count descending, then name.
pub proof fn lemma_row_cmp(n1: Seq<u8>, t1: int, n2: Seq<u8>, t2: int)
    ensures keys_cmp(q_order_keys(), seq![Val::Text(n1), Val::Int(t1)], seq![Val::Text(n2), Val::Int(t2)])
        == if t1 > t2 { -1 } else if t1 < t2 { 1 } else { lex_cmp(n1, n2) },
{
    let keys = q_order_keys();
    let (r1, r2) = (seq![Val::Text(n1), Val::Int(t1)], seq![Val::Text(n2), Val::Int(t2)]);
    assert(compare(r1[1], r2[1]) == Some(sign(t1 - t2)));
    assert(key_cmp(keys[0], r1, r2) == -sign(t1 - t2));
    assert(key_cmp(keys[1], r1, r2) == lex_cmp(n1, n2));
    let k1 = keys.drop_first();
    assert(k1 =~= seq![keys[1]]);
    assert(k1.drop_first() =~= Seq::<OrderKey>::empty());
    assert(keys_cmp(k1.drop_first(), r1, r2) == 0);
    assert(keys_cmp(k1, r1, r2) == lex_cmp(n1, n2));
}

/// The ORDER BY comparison of rows `a` and `b` (opaque: its laws are `lemma_ccmp`).
#[verifier::opaque]
pub open spec fn ccmp(rows: Seq<Row>, a: int, b: int) -> int { keys_cmp(q_order_keys(), rows[a], rows[b]) }

/// Every row has the ORDER BY key families.
pub open spec fn rows_ok(rows: Seq<Row>) -> bool {
    forall|i: int| 0 <= i < rows.len() ==> keys_ok(q_order_keys(), ofams(), #[trigger] rows[i])
}

/// `ccmp` is antisymmetric and transitive.
pub proof fn lemma_ccmp(rows: Seq<Row>, x: int, y: int, z: int)
    requires rows_ok(rows), 0 <= x < rows.len(), 0 <= y < rows.len(), 0 <= z < rows.len(),
    ensures
        ccmp(rows, x, y) == -ccmp(rows, y, x),
        ccmp(rows, x, y) <= 0 && ccmp(rows, y, z) <= 0 ==> ccmp(rows, x, z) <= 0,
        ccmp(rows, x, y) < 0 && ccmp(rows, y, z) <= 0 ==> ccmp(rows, x, z) < 0,
        ccmp(rows, x, y) <= 0 && ccmp(rows, y, z) < 0 ==> ccmp(rows, x, z) < 0,
{
    reveal(ccmp);
    let (k, f) = (q_order_keys(), ofams());
    lemma_keys_cmp_antisym(k, f, rows[x], rows[y]);
    lemma_keys_cmp_antisym(k, f, rows[y], rows[z]);
    lemma_keys_cmp_antisym(k, f, rows[x], rows[z]);
    if ccmp(rows, x, y) <= 0 && ccmp(rows, y, z) <= 0 {
        lemma_keys_cmp_trans(k, f, rows[x], rows[y], rows[z]);
    }
    if ccmp(rows, x, y) < 0 && ccmp(rows, y, z) <= 0 && ccmp(rows, x, z) >= 0 {
        // then z <= x, and y <= z <= x contradicts x < y
        lemma_keys_cmp_trans(k, f, rows[y], rows[z], rows[x]);
    }
    if ccmp(rows, x, y) <= 0 && ccmp(rows, y, z) < 0 && ccmp(rows, x, z) >= 0 {
        // then z <= x <= y contradicts y < z
        lemma_keys_cmp_trans(k, f, rows[z], rows[x], rows[y]);
    }
}

/// The selection invariant after rows `0..i` (see the module header).
pub open spec fn top_inv(rows: Seq<Row>, i: int, sel: Seq<usize>) -> bool {
    &&& 0 <= i <= rows.len() <= usize::MAX
    &&& rows_ok(rows)
    &&& sel.len() == if i <= TOPK { i } else { TOPK as int }
    &&& sel.no_duplicates()
    &&& forall|t: int| 0 <= t < sel.len() ==> (#[trigger] sel[t] as int) < i
    &&& forall|a: int, b: int| 0 <= a < b < sel.len() ==> ccmp(rows, sel[a] as int, sel[b] as int) <= 0
    &&& i <= TOPK ==> forall|x: int| 0 <= x < i ==> #[trigger] sel.contains(x as usize)
    &&& forall|x: int, a: int| 0 <= x < i && !sel.contains(x as usize) && 0 <= a < sel.len()
            ==> #[trigger] ccmp(rows, sel[a] as int, x) <= 0
}

/// Inserting row `i` at position `p` keeps the list sorted and duplicate-free, and its entries are the old ones and
/// `i`.
proof fn lemma_insert(rows: Seq<Row>, i: int, sel: Seq<usize>, p: int)
    requires
        top_inv(rows, i, sel), i < rows.len(),
        0 <= p <= sel.len(),
        forall|a: int| p <= a < sel.len() ==> ccmp(rows, i, #[trigger] sel[a] as int) < 0,
        p > 0 ==> ccmp(rows, sel[p - 1] as int, i) <= 0,
    ensures ({
        let ins = sel.insert(p, i as usize);
        &&& forall|a: int, b: int| 0 <= a < b < ins.len() ==> ccmp(rows, ins[a] as int, ins[b] as int) <= 0
        &&& ins.no_duplicates()
        &&& forall|y: usize| #[trigger] ins.contains(y) <==> (sel.contains(y) || y == i as usize)
        &&& forall|t: int| 0 <= t < ins.len() ==> (#[trigger] ins[t] as int) < i + 1
    }),
{
    let x = i as usize;
    let ins = sel.insert(p, x);
    assert(!sel.contains(x)) by {
        if sel.contains(x) {
            let t = choose|t: int| 0 <= t < sel.len() && sel[t] == x;
            assert((sel[t] as int) < i);
        }
    }
    assert(forall|a: int| 0 <= a < p ==> ins[a] == sel[a]);
    assert(ins[p] == x);
    assert(forall|a: int| p < a < ins.len() ==> ins[a] == sel[a - 1]);
    assert forall|a: int| 0 <= a < p implies ccmp(rows, sel[a] as int, i) <= 0 by {
        if a < p - 1 {
            lemma_ccmp(rows, sel[a] as int, sel[p - 1] as int, i);
        }
    }
    assert forall|a: int, b: int| 0 <= a < b < ins.len() implies ccmp(rows, ins[a] as int, ins[b] as int) <= 0 by {
        if b < p {
        } else if b == p {
        } else if a < p {
            lemma_ccmp(rows, sel[a] as int, i, sel[b - 1] as int);
        } else if a == p {
            lemma_ccmp(rows, i, sel[b - 1] as int, i);
        } else {
        }
    }
    assert forall|a: int, b: int| 0 <= a < ins.len() && 0 <= b < ins.len() && a != b implies ins[a] != ins[b] by {
        if a == p || b == p {
            if a != p { assert(sel.contains(ins[a])); }
            if b != p { assert(sel.contains(ins[b])); }
        }
    }
    assert forall|y: usize| #[trigger] ins.contains(y) <==> (sel.contains(y) || y == x) by {
        if ins.contains(y) {
            let t = choose|t: int| 0 <= t < ins.len() && ins[t] == y;
            if t < p { assert(sel[t] == y); } else if t > p { assert(sel[t - 1] == y); }
        }
        if sel.contains(y) {
            let t = choose|t: int| 0 <= t < sel.len() && sel[t] == y;
            if t < p { assert(ins[t] == y); } else { assert(ins[t + 1] == y); }
        }
        if y == x { assert(ins[p] == y); }
    }
    assert forall|t: int| 0 <= t < ins.len() implies (#[trigger] ins[t] as int) < i + 1 by {
        if t != p {
            assert(sel.contains(ins[t]));
            let u = choose|u: int| 0 <= u < sel.len() && sel[u] == ins[t];
        }
    }
}

/// When the full list loses its last row to `i`: every kept row sorts no later than every unselected one.
proof fn lemma_full_unselected(rows: Seq<Row>, i: int, sel: Seq<usize>, ins: Seq<usize>)
    requires
        0 <= i < rows.len() <= usize::MAX, rows_ok(rows),
        sel.len() > 0, ins.len() == sel.len() + 1,
        ins[ins.len() - 1] == sel[sel.len() - 1],
        ccmp(rows, i, sel[sel.len() - 1] as int) < 0,
        forall|a: int, b: int| 0 <= a < b < ins.len() ==> ccmp(rows, ins[a] as int, ins[b] as int) <= 0,
        forall|y: usize| #[trigger] ins.contains(y) <==> (sel.contains(y) || y == i as usize),
        forall|t: int| 0 <= t < sel.len() ==> (#[trigger] sel[t] as int) < i,
        forall|x: int, a: int| 0 <= x < i && !sel.contains(x as usize) && 0 <= a < sel.len()
            ==> #[trigger] ccmp(rows, sel[a] as int, x) <= 0,
    ensures ({
        let out = ins.drop_last();
        forall|z: int, a: int| 0 <= z < i + 1 && !out.contains(z as usize) && 0 <= a < out.len()
            ==> #[trigger] ccmp(rows, out[a] as int, z) <= 0
    }),
{
    let out = ins.drop_last();
    let last = sel[sel.len() - 1];
    assert forall|z: int, a: int| 0 <= z < i + 1 && !out.contains(z as usize) && 0 <= a < out.len()
        implies #[trigger] ccmp(rows, out[a] as int, z) <= 0 by {
        let w = out[a];
        assert(w == ins[a]);
        assert(ins.contains(w));
        if z as usize == last {
            assert(ccmp(rows, ins[a] as int, ins[ins.len() - 1] as int) <= 0);
        } else {
            assert(!ins.contains(z as usize)) by {
                if ins.contains(z as usize) {
                    let t = choose|t: int| 0 <= t < ins.len() && ins[t] == z as usize;
                    if t < out.len() { assert(out[t] == z as usize); }
                }
            }
            assert(z != i);
            assert(!sel.contains(z as usize));
            assert(ccmp(rows, sel[sel.len() - 1] as int, z) <= 0);
            assert((last as int) < i);
            if w == i as usize {
                lemma_ccmp(rows, i, last as int, z);
            } else {
                assert(sel.contains(w));
                let u = choose|u: int| 0 <= u < sel.len() && sel[u] == w;
                assert(ccmp(rows, sel[u] as int, z) <= 0);
            }
        }
    }
}

/// Inserting row `i` at position `p`, then dropping the last one when the list held `TOPK`.
proof fn lemma_enter(rows: Seq<Row>, i: int, sel: Seq<usize>, p: int)
    requires
        top_inv(rows, i, sel), i < rows.len(),
        0 <= p <= sel.len(),
        sel.len() == TOPK ==> p < TOPK,
        forall|a: int| p <= a < sel.len() ==> ccmp(rows, i, #[trigger] sel[a] as int) < 0,
        p > 0 ==> ccmp(rows, sel[p - 1] as int, i) <= 0,
    ensures ({
        let ins = sel.insert(p, i as usize);
        top_inv(rows, i + 1, if sel.len() == TOPK { ins.drop_last() } else { ins })
    }),
{
    let x = i as usize;
    let ins = sel.insert(p, x);
    lemma_insert(rows, i, sel, p);
    if sel.len() < TOPK {
        assert(i < TOPK);
        assert forall|z: int| 0 <= z < i + 1 implies #[trigger] ins.contains(z as usize) by {
            if z < i {
                assert(sel.contains(z as usize));
            }
        }
    } else {
        let out = ins.drop_last();
        assert(ins[ins.len() - 1] == sel[sel.len() - 1]);
        assert(ccmp(rows, i, sel[sel.len() - 1] as int) < 0);
        lemma_full_unselected(rows, i, sel, ins);
        assert forall|t: int| 0 <= t < out.len() implies (#[trigger] out[t] as int) < i + 1 by {
            assert(out[t] == ins[t]);
        }
        assert forall|a: int, b: int| 0 <= a < b < out.len() implies ccmp(rows, out[a] as int, out[b] as int) <= 0 by {
            assert(out[a] == ins[a] && out[b] == ins[b]);
        }
        assert(out.no_duplicates()) by {
            assert forall|a: int, b: int| 0 <= a < out.len() && 0 <= b < out.len() && a != b implies out[a] != out[b] by {
                assert(out[a] == ins[a] && out[b] == ins[b]);
            }
        }
    }
}

/// Skipping row `i` when the list is full and its last one sorts no later than `i`.
proof fn lemma_skip(rows: Seq<Row>, i: int, sel: Seq<usize>)
    requires
        top_inv(rows, i, sel), i < rows.len(),
        sel.len() == TOPK,
        ccmp(rows, sel[sel.len() - 1] as int, i) <= 0,
    ensures top_inv(rows, i + 1, sel),
{
    assert forall|z: int, a: int| 0 <= z < i + 1 && !sel.contains(z as usize) && 0 <= a < sel.len()
        implies #[trigger] ccmp(rows, sel[a] as int, z) <= 0 by {
        if z == i {
            if a < sel.len() - 1 {
                assert((sel[a] as int) < i && (sel[sel.len() - 1] as int) < i);
                lemma_ccmp(rows, sel[a] as int, sel[sel.len() - 1] as int, i);
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------ comparisons

/// `lex_cmp` of the names of supplier rows `s1` and `s2`.
pub fn name_cmp(c: &Cols, s1: usize, s2: usize, Ghost(sv): Ghost<StoresView>) -> (r: i8)
    requires cols_ok(*c, sv), s1 < c.ns, s2 < c.ns,
    ensures r as int == lex_cmp(sname(sv, s1 as int), sname(sv, s2 as int)),
{
    let ghost t = sname_col(sv);
    let ghost n1 = sname(sv, s1 as int);
    let ghost n2 = sname(sv, s2 as int);
    let a1 = c.snoff[s1];
    let b1 = c.snoff[s1 + 1];
    let a2 = c.snoff[s2];
    let b2 = c.snoff[s2 + 1];
    let blen = c.snb.len();
    proof {
        assert(0 <= t.offsets[s1 as int] <= t.offsets[s1 + 1] <= t.bytes.len());
        assert(0 <= t.offsets[s2 as int] <= t.offsets[s2 + 1] <= t.bytes.len());
        assert(n1.subrange(0, n1.len() as int) =~= n1);
        assert(n2.subrange(0, n2.len() as int) =~= n2);
    }
    let l1 = (b1 - a1) as usize;
    let l2 = (b2 - a2) as usize;
    let (u1, u2) = (a1 as usize, a2 as usize);
    let mut i: usize = 0;
    while i < l1 && i < l2
        invariant
            cols_ok(*c, sv), t == sname_col(sv), n1 == sname(sv, s1 as int), n2 == sname(sv, s2 as int),
            s1 < c.ns, s2 < c.ns, blen == c.snb@.len(),
            u1 == a1, u2 == a2, a1 == t.offsets[s1 as int], b1 == t.offsets[s1 + 1], a2 == t.offsets[s2 as int],
            b2 == t.offsets[s2 + 1], 0 <= a1 <= b1 <= blen, 0 <= a2 <= b2 <= blen, l1 == b1 - a1, l2 == b2 - a2,
            n1.len() == l1, n2.len() == l2,
            i <= l1, i <= l2,
            lex_cmp(n1.subrange(i as int, l1 as int), n2.subrange(i as int, l2 as int)) == lex_cmp(n1, n2),
        decreases l1 - i,
    {
        let ghost sa = n1.subrange(i as int, l1 as int);
        let ghost sb = n2.subrange(i as int, l2 as int);
        let x = c.snb[u1 + i];
        let y = c.snb[u2 + i];
        proof {
            assert(sa[0] == n1[i as int] && n1[i as int] == x);
            assert(sb[0] == n2[i as int] && n2[i as int] == y);
        }
        if x < y {
            return -1;
        } else if x > y {
            return 1;
        }
        proof {
            assert(sa.drop_first() =~= n1.subrange(i + 1, l1 as int));
            assert(sb.drop_first() =~= n2.subrange(i + 1, l2 as int));
        }
        i = i + 1;
    }
    if i < l1 { 1 } else if i < l2 { -1 } else { 0 }
}

/// The groups' facts the selection needs.
pub open spec fn grp_rows_ok(c: Cols, m: SupMap, grep: Seq<usize>, gt: Seq<u64>, sv: StoresView) -> bool {
    &&& cols_ok(c, sv)
    &&& grep.len() == gt.len()
    &&& forall|g: int| 0 <= g < grep.len() ==> (#[trigger] grep[g]) < m.nsel
    &&& m.nsel == m.sel@.len()
    &&& forall|ci: int| 0 <= ci < m.nsel ==> (#[trigger] m.sel@[ci]) < c.ns
}

/// Group `g1` sorts strictly before group `g2`.
fn before(c: &Cols, m: &SupMap, grep: &Vec<usize>, gt: &Vec<u64>, g1: usize, g2: usize, Ghost(sv): Ghost<StoresView>) -> (b: bool)
    requires grp_rows_ok(*c, *m, grep@, gt@, sv), g1 < grep@.len(), g2 < grep@.len(),
    ensures b == (ccmp(grows(sv, *m, grep@, gt@), g1 as int, g2 as int) < 0),
{
    let ghost rows = grows(sv, *m, grep@, gt@);
    proof {
        reveal(ccmp);
        lemma_row_cmp(gname(sv, *m, grep@[g1 as int] as int), gt@[g1 as int] as int, gname(sv, *m, grep@[g2 as int] as int),
            gt@[g2 as int] as int);
        assert(rows[g1 as int] == grow(sv, *m, grep@, gt@, g1 as int));
        assert(rows[g2 as int] == grow(sv, *m, grep@, gt@, g2 as int));
    }
    if gt[g1] > gt[g2] {
        true
    } else if gt[g1] < gt[g2] {
        false
    } else {
        name_cmp(c, m.sel[grep[g1]], m.sel[grep[g2]], Ghost(sv)) < 0
    }
}

/// Every group row has the ORDER BY key families.
pub proof fn lemma_grows_ok(sv: StoresView, m: SupMap, grep: Seq<usize>, gt: Seq<u64>)
    ensures rows_ok(grows(sv, m, grep, gt)),
{
    let rows = grows(sv, m, grep, gt);
    assert forall|i: int| 0 <= i < rows.len() implies keys_ok(q_order_keys(), ofams(), #[trigger] rows[i]) by {
        lemma_row_keys_ok(gname(sv, m, grep[i] as int), gt[i] as int);
    }
}

/// The first `min(TOPK, |groups|)` groups in ORDER BY order (indices into the groups).
pub fn top(c: &Cols, m: &SupMap, grep: &Vec<usize>, gt: &Vec<u64>, Ghost(sv): Ghost<StoresView>) -> (sel: Vec<usize>)
    requires grp_rows_ok(*c, *m, grep@, gt@, sv),
    ensures top_inv(grows(sv, *m, grep@, gt@), grep@.len() as int, sel@),
{
    let ghost rows = grows(sv, *m, grep@, gt@);
    let mut sel: Vec<usize> = Vec::new();
    let n = grep.len();
    proof { lemma_grows_ok(sv, *m, grep@, gt@); }
    let mut i: usize = 0;
    while i < n
        invariant
            grp_rows_ok(*c, *m, grep@, gt@, sv), rows == grows(sv, *m, grep@, gt@), n == grep@.len(), n == rows.len(),
            i <= n, top_inv(rows, i as int, sel@),
        decreases n - i,
    {
        let k = sel.len();
        // the position after every selected group that does not sort after group i
        let mut p: usize = k;
        while p > 0 && before(c, m, grep, gt, i, sel[p - 1], Ghost(sv))
            invariant
                grp_rows_ok(*c, *m, grep@, gt@, sv), rows == grows(sv, *m, grep@, gt@), n == grep@.len(), n == rows.len(),
                p <= k, k == sel@.len(), i < n, top_inv(rows, i as int, sel@),
                forall|a: int| p <= a < k ==> ccmp(rows, i as int, #[trigger] sel@[a] as int) < 0,
            decreases p,
        {
            p = p - 1;
        }
        proof {
            if p > 0 {
                lemma_ccmp(rows, sel@[p - 1] as int, i as int, i as int);
            }
        }
        if p < TOPK {
            proof { lemma_enter(rows, i as int, sel@, p as int); }
            let full = k == TOPK;
            sel.insert(p, i);
            if full {
                let _ = sel.pop();
            }
        } else {
            proof {
                lemma_ccmp(rows, sel@[k - 1] as int, i as int, i as int);
                lemma_skip(rows, i as int, sel@);
            }
        }
        i = i + 1;
    }
    sel
}

} // verus!
