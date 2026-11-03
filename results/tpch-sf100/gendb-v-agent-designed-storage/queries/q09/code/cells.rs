//! The accumulator cells of a lineitem range: one `Cell` (count, exact sum, absolute sum) per (year slot `k`, nation
//! row `n`) at index `k * nn + n`, for the `ny` distinct years `years[0 .. ny]`. `cells_inv(.., lo, pos)` states that
//! the cells are the `qspec` sums over the rows `[lo, pos)`, that every joining row of the range has its year in the
//! list, and that unused slots are zero. The step lemmas add one row (`lemma_cells_add`), skip rows that do not join
//! (`lemma_cells_skip`, `lemma_cells_skip_range`) and open a new year slot (`lemma_cells_new_year`).
use vstd::prelude::*;
use crate::spec::numeric::abs;
use crate::link::expr::i128_max;
use super::common::isum::*;
use super::model::*;
use super::qspec::*;

verus! {

/// One accumulator cell: count, exact sum (scale 4) and absolute sum of the contributions.
#[derive(Clone, Copy)]
pub struct Cell {
    pub cnt: u64,
    pub sum: i128,
    pub ab: u128,
}

pub open spec fn zero_cell() -> Cell {
    Cell { cnt: 0, sum: 0, ab: 0 }
}

/// The cell of nation row `n` and year `y` over the rows `[lo, pos)`.
pub open spec fn cell_is(m: M, p: QP, x: Cell, n: int, y: int, lo: int, pos: int) -> bool {
    &&& x.cnt as int == dsum(cnt_f(m, p, n, y), lo, pos)
    &&& x.sum as int == dsum(sum_f(m, p, n, y), lo, pos)
    &&& x.ab as int == dsum(abs_f(m, p, n, y), lo, pos)
    &&& x.ab as int <= i128_max()
}

/// Year slot `k` holds the distinct year `years[k]`.
pub open spec fn years_ok(years: Seq<i64>, ny: int) -> bool {
    forall|a: int, b: int| 0 <= a < ny && 0 <= b < ny && a != b ==> #[trigger] years[a] != #[trigger] years[b]
}

/// The cells over the rows `[lo, pos)` (`nn` nation rows, `ny` years of capacity `cap`).
pub open spec fn cells_inv(m: M, p: QP, cells: Seq<Cell>, years: Seq<i64>, ny: int, cap: int, nn: int, lo: int, pos: int) -> bool {
    &&& 0 <= lo <= pos <= m.l_n
    &&& nn == m.n_n
    &&& 0 <= ny <= cap
    &&& years.len() == cap
    &&& cells.len() == cap * nn
    &&& years_ok(years, ny)
    &&& forall|k: int, n: int| 0 <= k < ny && 0 <= n < nn ==> #[trigger] cell_is(m, p, cells[k * nn + n], n, years[k] as int, lo, pos)
    &&& forall|k: int, n: int| ny <= k < cap && 0 <= n < nn ==> #[trigger] cells[k * nn + n] == zero_cell()
    &&& forall|j: int| lo <= j < pos && #[trigger] jok(m, p, j) ==> exists|k: int| 0 <= k < ny && years[k] as int == jyear(m, j)
}

/// Index arithmetic of the cells: distinct (slot, nation row) pairs have distinct indices inside the vector.
pub proof fn lemma_cell_index(nn: int, k: int, n: int, k2: int, n2: int)
    requires 0 <= n < nn, 0 <= n2 < nn, 0 <= k, 0 <= k2,
    ensures
        (k * nn + n == k2 * nn + n2) <==> (k == k2 && n == n2),
        0 <= k * nn + n,
{
    if k != k2 {
        if k < k2 {
            assert(k * nn + n < k2 * nn + n2) by (nonlinear_arith) requires k < k2, 0 <= n < nn, 0 <= n2;
        } else {
            assert(k2 * nn + n2 < k * nn + n) by (nonlinear_arith) requires k2 < k, 0 <= n2 < nn, 0 <= n;
        }
    }
    assert(0 <= k * nn + n) by (nonlinear_arith) requires 0 <= k, 0 <= n, 0 <= nn;
}

pub proof fn lemma_cell_bound(nn: int, cap: int, k: int, n: int)
    requires 0 <= n < nn, 0 <= k < cap,
    ensures 0 <= k * nn + n < cap * nn,
{
    assert(k * nn + n < cap * nn) by (nonlinear_arith) requires 0 <= n < nn, 0 <= k < cap;
    assert(0 <= k * nn + n) by (nonlinear_arith) requires 0 <= k, 0 <= n, 0 <= nn;
}

/// A range on which `f` is zero sums to zero.
pub proof fn lemma_dsum_zero(f: spec_fn(int) -> int, a: int, b: int)
    requires 0 <= a <= b, forall|j: int| a <= j < b ==> #[trigger] f(j) == 0,
    ensures dsum(f, a, b) == 0,
    decreases b - a,
{
    if b > a {
        lemma_dsum_zero(f, a, b - 1);
        lemma_dsum_step(f, a, b - 1);
    }
}

/// The empty range: every cell is zero.
pub proof fn lemma_cells_start(m: M, p: QP, years: Seq<i64>, cap: int, nn: int, lo: int)
    requires 0 <= lo <= m.l_n, nn == m.n_n, nn >= 0, cap >= 0, years.len() == cap,
    ensures cells_inv(m, p, Seq::new((cap * nn) as nat, |i: int| zero_cell()), years, 0, cap, nn, lo, lo),
{
    let cells = Seq::new((cap * nn) as nat, |i: int| zero_cell());
    assert(cap * nn >= 0) by (nonlinear_arith) requires cap >= 0, nn >= 0;
    assert forall|k: int, n: int| 0 <= k < cap && 0 <= n < nn implies #[trigger] cells[k * nn + n] == zero_cell() by {
        lemma_cell_bound(nn, cap, k, n);
    }
}

/// A row that does not join leaves every cell unchanged.
pub proof fn lemma_cells_skip(m: M, p: QP, cells: Seq<Cell>, years: Seq<i64>, ny: int, cap: int, nn: int, lo: int, pos: int)
    requires cells_inv(m, p, cells, years, ny, cap, nn, lo, pos), pos < m.l_n, !jok(m, p, pos),
    ensures cells_inv(m, p, cells, years, ny, cap, nn, lo, pos + 1),
{
    assert forall|k: int, n: int| 0 <= k < ny && 0 <= n < nn implies #[trigger] cell_is(m, p, cells[k * nn + n], n, years[k] as int, lo, pos + 1) by {
        let y = years[k] as int;
        assert(cell_is(m, p, cells[k * nn + n], n, y, lo, pos));
        lemma_dsum_step(cnt_f(m, p, n, y), lo, pos);
        lemma_dsum_step(sum_f(m, p, n, y), lo, pos);
        lemma_dsum_step(abs_f(m, p, n, y), lo, pos);
    }
    assert forall|j: int| lo <= j < pos + 1 && #[trigger] jok(m, p, j) implies exists|k: int| 0 <= k < ny && years[k] as int == jyear(m, j) by {
        assert(j < pos);
    }
}

/// Rows `[pos, q)` that do not join leave every cell unchanged.
pub proof fn lemma_cells_skip_range(m: M, p: QP, cells: Seq<Cell>, years: Seq<i64>, ny: int, cap: int, nn: int, lo: int, pos: int, q: int)
    requires
        cells_inv(m, p, cells, years, ny, cap, nn, lo, pos),
        pos <= q <= m.l_n,
        forall|j: int| pos <= j < q ==> !#[trigger] jok(m, p, j),
    ensures cells_inv(m, p, cells, years, ny, cap, nn, lo, q),
    decreases q - pos,
{
    if pos < q {
        lemma_cells_skip(m, p, cells, years, ny, cap, nn, lo, pos);
        lemma_cells_skip_range(m, p, cells, years, ny, cap, nn, lo, pos + 1, q);
    }
}

/// A new year `y` (not yet in the list) gets slot `ny`; its cells, zero so far, are its sums.
pub proof fn lemma_cells_new_year(m: M, p: QP, cells: Seq<Cell>, years: Seq<i64>, ny: int, cap: int, nn: int, lo: int, pos: int, y: i64)
    requires
        cells_inv(m, p, cells, years, ny, cap, nn, lo, pos),
        ny < cap,
        forall|k: int| 0 <= k < ny ==> years[k] != y,
    ensures cells_inv(m, p, cells, years.update(ny, y), ny + 1, cap, nn, lo, pos),
{
    let ys = years.update(ny, y);
    assert forall|a: int, b: int| 0 <= a < ny + 1 && 0 <= b < ny + 1 && a != b implies #[trigger] ys[a] != #[trigger] ys[b] by {
        if a < ny && b < ny {
            assert(years[a] != years[b]);
        }
    }
    assert forall|k: int, n: int| 0 <= k < ny + 1 && 0 <= n < nn implies #[trigger] cell_is(m, p, cells[k * nn + n], n, ys[k] as int, lo, pos) by {
        if k < ny {
            assert(cell_is(m, p, cells[k * nn + n], n, years[k] as int, lo, pos));
        } else {
            assert(cells[k * nn + n] == zero_cell());
            assert forall|j: int| lo <= j < pos implies #[trigger] cnt_f(m, p, n, y as int)(j) == 0 by {
                if jhit(m, p, j, n, y as int) {
                    assert(jok(m, p, j));
                    let k2 = choose|k2: int| 0 <= k2 < ny && years[k2] as int == jyear(m, j);
                }
            }
            assert forall|j: int| lo <= j < pos implies #[trigger] sum_f(m, p, n, y as int)(j) == 0 by {
                if jhit(m, p, j, n, y as int) {
                    let k2 = choose|k2: int| 0 <= k2 < ny && years[k2] as int == jyear(m, j);
                }
            }
            assert forall|j: int| lo <= j < pos implies #[trigger] abs_f(m, p, n, y as int)(j) == 0 by {
                if jhit(m, p, j, n, y as int) {
                    let k2 = choose|k2: int| 0 <= k2 < ny && years[k2] as int == jyear(m, j);
                }
            }
            lemma_dsum_zero(cnt_f(m, p, n, y as int), lo, pos);
            lemma_dsum_zero(sum_f(m, p, n, y as int), lo, pos);
            lemma_dsum_zero(abs_f(m, p, n, y as int), lo, pos);
        }
    }
    assert forall|k: int, n: int| ny + 1 <= k < cap && 0 <= n < nn implies #[trigger] cells[k * nn + n] == zero_cell() by {}
    assert forall|j: int| lo <= j < pos && #[trigger] jok(m, p, j) implies exists|k: int| 0 <= k < ny + 1 && ys[k] as int == jyear(m, j) by {
        let k2 = choose|k2: int| 0 <= k2 < ny && years[k2] as int == jyear(m, j);
        assert(ys[k2] == years[k2]);
    }
}

/// The cell after adding a joining row's contribution `a`.
pub open spec fn added(x: Cell, a: int) -> Cell {
    Cell { cnt: (x.cnt + 1) as u64, sum: (x.sum + a) as i128, ab: (x.ab + abs(a)) as u128 }
}

/// A joining row of nation row `n0` and year slot `k0`: its cell gets its contribution, the others are unchanged.
pub proof fn lemma_cells_add(m: M, p: QP, cells: Seq<Cell>, years: Seq<i64>, ny: int, cap: int, nn: int, lo: int, pos: int,
    k0: int, n0: int, x: Cell)
    requires
        cells_inv(m, p, cells, years, ny, cap, nn, lo, pos),
        pos < m.l_n,
        jok(m, p, pos),
        0 <= k0 < ny, 0 <= n0 < nn,
        jn(m, pos) == n0,
        years[k0] as int == jyear(m, pos),
        x.cnt as int == cells[k0 * nn + n0].cnt + 1,
        x.sum as int == cells[k0 * nn + n0].sum + jamt(m, pos),
        x.ab as int == cells[k0 * nn + n0].ab + abs(jamt(m, pos)),
        x.ab as int <= i128_max(),
    ensures cells_inv(m, p, cells.update(k0 * nn + n0, x), years, ny, cap, nn, lo, pos + 1),
{
    let cs = cells.update(k0 * nn + n0, x);
    lemma_cell_bound(nn, cap, k0, n0);
    assert forall|k: int, n: int| 0 <= k < ny && 0 <= n < nn implies #[trigger] cell_is(m, p, cs[k * nn + n], n, years[k] as int, lo, pos + 1) by {
        let y = years[k] as int;
        lemma_cell_index(nn, k, n, k0, n0);
        lemma_cell_bound(nn, cap, k, n);
        assert(cell_is(m, p, cells[k * nn + n], n, y, lo, pos));
        lemma_dsum_step(cnt_f(m, p, n, y), lo, pos);
        lemma_dsum_step(sum_f(m, p, n, y), lo, pos);
        lemma_dsum_step(abs_f(m, p, n, y), lo, pos);
        lemma_terms_at(m, p, n, y, pos);
        if k == k0 && n == n0 {
            assert(jhit(m, p, pos, n, y));
        } else if k != k0 {
            assert(years[k] != years[k0]);
            assert(!jhit(m, p, pos, n, y));
        } else {
            assert(!jhit(m, p, pos, n, y));
        }
    }
    assert forall|k: int, n: int| ny <= k < cap && 0 <= n < nn implies #[trigger] cs[k * nn + n] == zero_cell() by {
        lemma_cell_index(nn, k, n, k0, n0);
        lemma_cell_bound(nn, cap, k, n);
    }
    assert forall|j: int| lo <= j < pos + 1 && #[trigger] jok(m, p, j) implies exists|k: int| 0 <= k < ny && years[k] as int == jyear(m, j) by {
        if j == pos {
            assert(years[k0] as int == jyear(m, j));
        }
    }
}

/// A row whose contribution would take its cell's absolute sum above `i128::MAX`: the cell's absolute sum over the
/// range through that row exceeds it.
pub proof fn lemma_cells_overflow(m: M, p: QP, cells: Seq<Cell>, years: Seq<i64>, ny: int, cap: int, nn: int, lo: int, pos: int,
    k0: int, n0: int)
    requires
        cells_inv(m, p, cells, years, ny, cap, nn, lo, pos),
        pos < m.l_n,
        jok(m, p, pos),
        0 <= k0 < ny, 0 <= n0 < nn,
        jn(m, pos) == n0,
        years[k0] as int == jyear(m, pos),
        cells[k0 * nn + n0].ab + abs(jamt(m, pos)) > i128_max(),
    ensures dsum(abs_f(m, p, n0, years[k0] as int), lo, pos + 1) > i128_max(),
{
    let y = years[k0] as int;
    assert(cell_is(m, p, cells[k0 * nn + n0], n0, y, lo, pos));
    lemma_dsum_step(abs_f(m, p, n0, y), lo, pos);
    lemma_terms_at(m, p, n0, y, pos);
    assert(jhit(m, p, pos, n0, y));
}

} // verus!
