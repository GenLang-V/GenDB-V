//! Verified checkers of the declared integrity constraints (`spec::constraints`), in the spec's order:
//! - `check_constraints_wf_exec` decides the declaration rule `constraints_wf` (called by `check_schema`, so by
//!   `check_db` and `check_ordered`);
//! - `check_constraints_exec` decides the instance predicate `constraints_hold` on a well-formed database, and
//!   returns `Capacity` exactly outside `fits_constraints` (some CHECK evaluation leaves the executable domain,
//!   `fits_pred`). Keys and foreign keys compare with `compare_exec` / `val_not_distinct_exec`, which are exact, so
//!   they never give `Capacity`.
//! `exec::relational::entry::evaluate` calls both. Every CHECK of every row is evaluated (no early exit on a
//! violation), so `Capacity` does not depend on the order in which violations are found. The checker is quadratic
//! in the rows of a table (reference evaluator; tiny data only).
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::typing::*;
use crate::spec::equality::*;
use crate::spec::constraints::*;
use crate::exec::value::*;
use crate::exec::ast::*;
use crate::exec::domain::*;
use crate::exec::scalar::*;
use crate::exec::equality::*;
use crate::exec::relational::schema::*;
use crate::exec::relational::domain::*;
use crate::exec::relational::eval::*;
use crate::exec::relational::check::*;

verus! {

// ------------------------------------------------------------------ executable domain of the instance check

/// Every row of `rows` evaluates CHECK `p` inside the executable domain.
pub open spec fn fits_check(db: Database, rows: Relation, p: Pred) -> bool {
    forall|i: int| 0 <= i < rows.len() ==> fits_pred(db, #[trigger] rows[i], p)
}

/// Only CHECK constraints compute (keys and foreign keys compare exactly).
pub open spec fn fits_constraint(db: Database, t: int, c: Constraint) -> bool {
    match c {
        Constraint::Check(p) => fits_check(db, db.tables[t], p),
        _ => true,
    }
}

/// Checking every declared constraint stays inside the executable domain.
pub open spec fn fits_constraints(db: Database) -> bool {
    forall|t: int, k: int| 0 <= t < db.schema.len() && t < db.tables.len() && 0 <= k < db.schema[t].constraints.len()
        ==> fits_constraint(db, t, #[trigger] db.schema[t].constraints[k])
}

// ------------------------------------------------------------------ declared-schema well-formedness
//
// Each `<spec fn>_exec` below decides the recursive spec function of the same name by a loop over prefixes
// (`take(i)`), the pattern `spec::constraints` is written for.

/// `spec::constraints::constraints_wf`.
pub fn check_constraints_wf_exec(schema: &Vec<ETableSchema>) -> (b: bool)
    ensures b == constraints_wf(view_schema(schema@)),
{
    let ghost g = view_schema(schema@);
    let mut acc = true;
    let mut i: usize = 0;
    proof { assert(g.take(0) =~= Seq::<TableSchema>::empty()); }
    while i < schema.len()
        invariant i <= schema.len(), g == view_schema(schema@), acc == tables_constraints_wf(g, g.take(i as int)),
        decreases schema.len() - i,
    {
        proof {
            let u = g.take(i as int + 1);
            assert(u.drop_last() =~= g.take(i as int));
            assert(u.last() == view_table_schema(schema@[i as int]));
        }
        let ok = table_constraints_wf_exec(schema, &schema[i]) && at_most_one_primary_exec(&schema[i].constraints);
        acc = acc && ok;
        i = i + 1;
    }
    proof { assert(g.take(schema.len() as int) =~= g); }
    acc
}

/// `spec::constraints::table_constraints_wf` of every constraint declared on table `t`.
fn table_constraints_wf_exec(schema: &Vec<ETableSchema>, t: &ETableSchema) -> (b: bool)
    ensures b == table_constraints_wf(view_schema(schema@), view_table_schema(*t), view_table_schema(*t).constraints),
{
    let ghost g = view_constraints(t.constraints@);
    let mut acc = true;
    let mut i: usize = 0;
    proof { assert(g.take(0) =~= Seq::<Constraint>::empty()); }
    while i < t.constraints.len()
        invariant
            i <= t.constraints.len(), g == view_constraints(t.constraints@),
            acc == table_constraints_wf(view_schema(schema@), view_table_schema(*t), g.take(i as int)),
        decreases t.constraints.len() - i,
    {
        proof {
            let u = g.take(i as int + 1);
            assert(u.drop_last() =~= g.take(i as int));
            assert(u.last() == view_constraint(t.constraints@[i as int]));
        }
        let ok = constraint_wf_exec(schema, t, &t.constraints[i]);
        acc = acc && ok;
        i = i + 1;
    }
    proof { assert(g.take(t.constraints.len() as int) =~= g); }
    acc
}

/// `spec::constraints::constraint_wf` for constraint `c` of table `t`.
fn constraint_wf_exec(schema: &Vec<ETableSchema>, t: &ETableSchema, c: &EConstraint) -> (b: bool)
    ensures b == constraint_wf(view_schema(schema@), view_table_schema(*t), view_constraint(*c)),
{
    let ghost gs = view_schema(schema@);
    match c {
        EConstraint::Key { cols, primary, nulls_distinct } => {
            cols.len() > 0 && cols_in_range_exec(cols, t.columns.len()) && cols_distinct_exec(cols)
                && (!*primary || cols_not_null_exec(cols, &t.columns))
        },
        EConstraint::ForeignKey { cols, table, ref_cols, match_full } => {
            if *table >= schema.len() || cols.len() == 0 || cols.len() != ref_cols.len() {
                return false;
            }
            let target = &schema[*table];
            proof { assert(gs[*table as int] == view_table_schema(schema@[*table as int])); }
            cols_in_range_exec(cols, t.columns.len()) && cols_in_range_exec(ref_cols, target.columns.len())
                && cols_distinct_exec(ref_cols) && has_key_on_exec(&target.constraints, ref_cols)
                && fk_types_ok_exec(&t.columns, cols, &target.columns, ref_cols)
        },
        EConstraint::Check(p) => {
            // A CHECK is typed over the table's row with no table in scope (the empty schema).
            let empty: Vec<ETableSchema> = Vec::new();
            let env = table_tys_exec(t);
            proof { assert(view_schema(empty@) =~= Seq::<TableSchema>::empty()); }
            type_pred_exec(&empty, &env, p)
        },
    }
}

/// `primary_keys(cs) <= 1`.
fn at_most_one_primary_exec(cs: &Vec<EConstraint>) -> (b: bool)
    ensures b == (primary_keys(view_constraints(cs@)) <= 1),
{
    let ghost g = view_constraints(cs@);
    let mut n: usize = 0;
    let mut i: usize = 0;
    proof { assert(g.take(0) =~= Seq::<Constraint>::empty()); }
    while i < cs.len()
        invariant i <= cs.len(), g == view_constraints(cs@), n <= i, n as nat == primary_keys(g.take(i as int)),
        decreases cs.len() - i,
    {
        proof {
            let t = g.take(i as int + 1);
            assert(t.drop_last() =~= g.take(i as int));
            assert(t.last() == view_constraint(cs@[i as int]));
        }
        match &cs[i] {
            EConstraint::Key { primary, .. } => if *primary { n = n + 1; },
            _ => {},
        }
        i = i + 1;
    }
    proof { assert(g.take(cs.len() as int) =~= g); }
    n <= 1
}

/// `spec::constraints::has_key_on`.
fn has_key_on_exec(cs: &Vec<EConstraint>, ref_cols: &Vec<usize>) -> (b: bool)
    ensures b == has_key_on(view_constraints(cs@), view_cols(ref_cols@)),
{
    let ghost g = view_constraints(cs@);
    let mut acc = false;
    let mut i: usize = 0;
    proof { assert(g.take(0) =~= Seq::<Constraint>::empty()); }
    while i < cs.len()
        invariant i <= cs.len(), g == view_constraints(cs@), acc == has_key_on(g.take(i as int), view_cols(ref_cols@)),
        decreases cs.len() - i,
    {
        proof {
            let t = g.take(i as int + 1);
            assert(t.drop_last() =~= g.take(i as int));
            assert(t.last() == view_constraint(cs@[i as int]));
        }
        let hit = match &cs[i] {
            EConstraint::Key { cols, .. } => cols.len() == ref_cols.len() && cols_subset_exec(cols, ref_cols),
            _ => false,
        };
        acc = acc || hit;
        i = i + 1;
    }
    proof { assert(g.take(cs.len() as int) =~= g); }
    acc
}

/// `spec::constraints::fk_types_ok`.
fn fk_types_ok_exec(child: &Vec<Column>, cols: &Vec<usize>, parent: &Vec<Column>, ref_cols: &Vec<usize>) -> (b: bool)
    requires cols.len() == ref_cols.len(),
    ensures b == fk_types_ok(child@, view_cols(cols@), parent@, view_cols(ref_cols@)),
{
    let ghost g = view_cols(cols@);
    let ghost h = view_cols(ref_cols@);
    let mut acc = true;
    let mut i: usize = 0;
    proof {
        assert(g.take(0) =~= Seq::<nat>::empty());
        assert(h.take(0) =~= Seq::<nat>::empty());
    }
    while i < cols.len()
        invariant
            i <= cols.len(), cols.len() == ref_cols.len(), g == view_cols(cols@), h == view_cols(ref_cols@),
            acc == fk_types_ok(child@, g.take(i as int), parent@, h.take(i as int)),
        decreases cols.len() - i,
    {
        proof {
            let t = g.take(i as int + 1);
            let u = h.take(i as int + 1);
            assert(t.drop_last() =~= g.take(i as int));
            assert(u.drop_last() =~= h.take(i as int));
            assert(t.last() == cols@[i as int] as nat);
            assert(u.last() == ref_cols@[i as int] as nat);
        }
        let (c, r) = (cols[i], ref_cols[i]);
        acc = acc && c < child.len() && r < parent.len() && fk_col_types_ok_exec(child[c].ty, parent[r].ty);
        i = i + 1;
    }
    proof {
        assert(g.take(cols.len() as int) =~= g);
        assert(h.take(cols.len() as int) =~= h);
    }
    acc
}

/// `spec::constraints::fk_col_types_ok`.
fn fk_col_types_ok_exec(c: SqlType, p: SqlType) -> (b: bool)
    ensures b == fk_col_types_ok(c, p),
{
    match c {
        SqlType::Bool => matches!(p, SqlType::Bool),
        SqlType::Int4 | SqlType::Int8 => matches!(p, SqlType::Int4 | SqlType::Int8 | SqlType::Numeric { .. }),
        SqlType::Numeric { .. } => matches!(p, SqlType::Numeric { .. }),
        SqlType::Date | SqlType::Timestamp => matches!(p, SqlType::Date | SqlType::Timestamp),
        SqlType::Text | SqlType::Varchar { .. } => matches!(p, SqlType::Text | SqlType::Varchar { .. }),
        SqlType::Bpchar { .. } => matches!(p, SqlType::Text | SqlType::Varchar { .. } | SqlType::Bpchar { .. }),
    }
}

/// `spec::constraints::cols_in_range`.
fn cols_in_range_exec(cols: &Vec<usize>, n: usize) -> (b: bool)
    ensures b == cols_in_range(view_cols(cols@), n as nat),
{
    let ghost g = view_cols(cols@);
    let mut acc = true;
    let mut i: usize = 0;
    proof { assert(g.take(0) =~= Seq::<nat>::empty()); }
    while i < cols.len()
        invariant i <= cols.len(), g == view_cols(cols@), acc == cols_in_range(g.take(i as int), n as nat),
        decreases cols.len() - i,
    {
        proof {
            let t = g.take(i as int + 1);
            assert(t.drop_last() =~= g.take(i as int));
            assert(t.last() == cols@[i as int] as nat);
        }
        acc = acc && cols[i] < n;
        i = i + 1;
    }
    proof { assert(g.take(cols.len() as int) =~= g); }
    acc
}

/// `spec::constraints::cols_distinct`.
fn cols_distinct_exec(cols: &Vec<usize>) -> (b: bool)
    ensures b == cols_distinct(view_cols(cols@)),
{
    let ghost g = view_cols(cols@);
    let mut acc = true;
    let mut i: usize = 0;
    proof { assert(g.take(0) =~= Seq::<nat>::empty()); }
    while i < cols.len()
        invariant i <= cols.len(), g == view_cols(cols@), acc == cols_distinct(g.take(i as int)),
        decreases cols.len() - i,
    {
        let dup = nat_in_exec(cols, i, cols[i]);
        proof {
            let t = g.take(i as int + 1);
            assert(t.drop_last() =~= g.take(i as int));
            assert(t.last() == cols@[i as int] as nat);
        }
        acc = acc && !dup;
        i = i + 1;
    }
    proof { assert(g.take(cols.len() as int) =~= g); }
    acc
}

/// `spec::constraints::cols_not_null`.
fn cols_not_null_exec(cols: &Vec<usize>, columns: &Vec<Column>) -> (b: bool)
    ensures b == cols_not_null(view_cols(cols@), columns@),
{
    let ghost g = view_cols(cols@);
    let mut acc = true;
    let mut i: usize = 0;
    proof { assert(g.take(0) =~= Seq::<nat>::empty()); }
    while i < cols.len()
        invariant i <= cols.len(), g == view_cols(cols@), acc == cols_not_null(g.take(i as int), columns@),
        decreases cols.len() - i,
    {
        proof {
            let t = g.take(i as int + 1);
            assert(t.drop_last() =~= g.take(i as int));
            assert(t.last() == cols@[i as int] as nat);
        }
        let c = cols[i];
        acc = acc && c < columns.len() && !columns[c].nullable;
        i = i + 1;
    }
    proof { assert(g.take(cols.len() as int) =~= g); }
    acc
}

/// `spec::constraints::cols_subset(a, b)`.
fn cols_subset_exec(a: &Vec<usize>, b: &Vec<usize>) -> (r: bool)
    ensures r == cols_subset(view_cols(a@), view_cols(b@)),
{
    let ghost g = view_cols(a@);
    let mut acc = true;
    let mut i: usize = 0;
    proof { assert(g.take(0) =~= Seq::<nat>::empty()); }
    while i < a.len()
        invariant i <= a.len(), g == view_cols(a@), acc == cols_subset(g.take(i as int), view_cols(b@)),
        decreases a.len() - i,
    {
        let hit = nat_in_exec(b, b.len(), a[i]);
        proof {
            let t = g.take(i as int + 1);
            assert(t.drop_last() =~= g.take(i as int));
            assert(t.last() == a@[i as int] as nat);
            assert(view_cols(b@).take(b.len() as int) =~= view_cols(b@));
        }
        acc = acc && hit;
        i = i + 1;
    }
    proof { assert(g.take(a.len() as int) =~= g); }
    acc
}

/// `spec::constraints::nat_in` on the prefix `s[..n]`.
fn nat_in_exec(s: &Vec<usize>, n: usize, x: usize) -> (b: bool)
    requires n <= s.len(),
    ensures b == nat_in(view_cols(s@).take(n as int), x as nat),
{
    let ghost g = view_cols(s@);
    let mut acc = false;
    let mut i: usize = 0;
    proof { assert(g.take(0) =~= Seq::<nat>::empty()); }
    while i < n
        invariant i <= n, n <= s.len(), g == view_cols(s@), acc == nat_in(g.take(i as int), x as nat),
        decreases n - i,
    {
        proof {
            let t = g.take(i as int + 1);
            assert(t.drop_last() =~= g.take(i as int));
            assert(t.last() == s@[i as int] as nat);
        }
        acc = acc || s[i] == x;
        i = i + 1;
    }
    acc
}

// ------------------------------------------------------------------ facts of a well-formed declaration

/// A declared constraint of a well-formed schema is well-formed.
proof fn lemma_constraint_wf_at(schema: Schema, t: int, k: int)
    requires constraints_wf(schema), 0 <= t < schema.len(), 0 <= k < schema[t].constraints.len(),
    ensures constraint_wf(schema, schema[t], schema[t].constraints[k]),
{
    lemma_tables_constraints_wf_at(schema, schema, t);
    lemma_table_constraints_wf_at(schema, schema[t], schema[t].constraints, k);
}

proof fn lemma_tables_constraints_wf_at(schema: Schema, ts: Seq<TableSchema>, t: int)
    requires tables_constraints_wf(schema, ts), 0 <= t < ts.len(),
    ensures table_constraints_wf(schema, ts[t], ts[t].constraints),
    decreases ts.len(),
{
    if t < ts.len() - 1 {
        assert(ts.drop_last()[t] == ts[t]);
        lemma_tables_constraints_wf_at(schema, ts.drop_last(), t);
    }
}

proof fn lemma_table_constraints_wf_at(schema: Schema, t: TableSchema, cs: Seq<Constraint>, k: int)
    requires table_constraints_wf(schema, t, cs), 0 <= k < cs.len(),
    ensures constraint_wf(schema, t, cs[k]),
    decreases cs.len(),
{
    if k < cs.len() - 1 {
        assert(cs.drop_last()[k] == cs[k]);
        lemma_table_constraints_wf_at(schema, t, cs.drop_last(), k);
    }
}

/// Column positions in range (`cols_in_range`) index every row of width `n` (`cols_below`).
proof fn lemma_cols_below(cols: Seq<usize>, n: nat)
    requires cols_in_range(view_cols(cols), n),
    ensures cols_below(cols, n as int),
{
    lemma_cols_in_range(view_cols(cols), n);
    assert forall|c: int| 0 <= c < cols.len() implies (#[trigger] cols[c] as int) < n by {
        assert(view_cols(cols)[c] == cols[c] as nat);
    }
}

/// The quantified form of `cols_in_range`.
proof fn lemma_cols_in_range(cols: Seq<nat>, n: nat)
    requires cols_in_range(cols, n),
    ensures forall|i: int| 0 <= i < cols.len() ==> #[trigger] cols[i] < n,
    decreases cols.len(),
{
    if cols.len() > 0 {
        lemma_cols_in_range(cols.drop_last(), n);
        assert forall|i: int| 0 <= i < cols.len() implies #[trigger] cols[i] < n by {
            if i < cols.len() - 1 { assert(cols.drop_last()[i] == cols[i]); }
        }
    }
}

// ------------------------------------------------------------------ the instance predicate

/// `spec::constraints::constraints_hold` on a well-formed database; a SQL error inside a CHECK is a violation,
/// so the only refusal is `Capacity`, exactly outside `fits_constraints`.
pub fn check_constraints_exec(db: &EDatabase) -> (r: Result<bool, Capacity>)
    requires db_wf(db@),
    ensures
        match r {
            Ok(b) => fits_constraints(db@) && b == constraints_hold(db@),
            Err(_) => !fits_constraints(db@),
        },
{
    let ghost g = db@;
    let mut acc = true;
    let mut t: usize = 0;
    while t < db.schema.len()
        invariant
            t <= db.schema.len(), g == db@, db_wf(db@), db.tables.len() == db.schema.len(),
            forall|x: int, y: int| 0 <= x < t && 0 <= y < g.schema[x].constraints.len()
                ==> fits_constraint(g, x, #[trigger] g.schema[x].constraints[y]),
            acc == (forall|x: int, y: int| 0 <= x < t && 0 <= y < g.schema[x].constraints.len()
                ==> constraint_holds(g, x, #[trigger] g.schema[x].constraints[y])),
        decreases db.schema.len() - t,
    {
        proof { assert(g.schema[t as int] == view_table_schema(db.schema@[t as int])); }
        let ghost acc0 = acc;
        let mut k: usize = 0;
        while k < db.schema[t].constraints.len()
            invariant
                t < db.schema.len(), k <= db.schema@[t as int].constraints.len(), g == db@, db_wf(db@),
                db.tables.len() == db.schema.len(),
                g.schema[t as int].constraints.len() == db.schema@[t as int].constraints.len(),
                forall|x: int, y: int| 0 <= x < t && 0 <= y < g.schema[x].constraints.len()
                    ==> fits_constraint(g, x, #[trigger] g.schema[x].constraints[y]),
                forall|y: int| 0 <= y < k ==> fits_constraint(g, t as int, #[trigger] g.schema[t as int].constraints[y]),
                acc0 == (forall|x: int, y: int| 0 <= x < t && 0 <= y < g.schema[x].constraints.len()
                    ==> constraint_holds(g, x, #[trigger] g.schema[x].constraints[y])),
                acc == (acc0 && forall|y: int| 0 <= y < k
                    ==> constraint_holds(g, t as int, #[trigger] g.schema[t as int].constraints[y])),
            decreases db.schema@[t as int].constraints.len() - k,
        {
            match constraint_holds_exec(db, t, k) {
                Err(c) => {
                    proof {
                        let cc = g.schema[t as int].constraints[k as int];
                        assert(!fits_constraint(g, t as int, cc));
                    }
                    return Err(c);
                },
                Ok(ok) => {
                    proof {
                        let cc = g.schema[t as int].constraints[k as int];
                        assert((acc && ok) == (acc0 && forall|y: int| 0 <= y < k + 1
                            ==> constraint_holds(g, t as int, #[trigger] g.schema[t as int].constraints[y]))) by {
                            if acc && ok {
                                assert forall|y: int| 0 <= y < k + 1 implies
                                    constraint_holds(g, t as int, #[trigger] g.schema[t as int].constraints[y]) by {
                                    if y == k as int { assert(ok == constraint_holds(g, t as int, cc)); }
                                }
                            }
                            if !ok {
                                assert(!constraint_holds(g, t as int, cc));
                            }
                        }
                    }
                    acc = acc && ok;
                },
            }
            k = k + 1;
        }
        proof {
            assert forall|x: int, y: int| 0 <= x < t + 1 && 0 <= y < g.schema[x].constraints.len()
                implies fits_constraint(g, x, #[trigger] g.schema[x].constraints[y]) by {
                if x == t as int { assert(fits_constraint(g, t as int, g.schema[t as int].constraints[y])); }
            }
            assert(acc == (forall|x: int, y: int| 0 <= x < t + 1 && 0 <= y < g.schema[x].constraints.len()
                ==> constraint_holds(g, x, #[trigger] g.schema[x].constraints[y]))) by {
                if acc {
                    assert forall|x: int, y: int| 0 <= x < t + 1 && 0 <= y < g.schema[x].constraints.len()
                        implies constraint_holds(g, x, #[trigger] g.schema[x].constraints[y]) by {
                        if x == t as int { assert(constraint_holds(g, t as int, g.schema[t as int].constraints[y])); }
                    }
                } else if !acc0 {
                    let w = choose|x: int, y: int| !(0 <= x < t && 0 <= y < g.schema[x].constraints.len()
                        ==> constraint_holds(g, x, #[trigger] g.schema[x].constraints[y]));
                    assert(!constraint_holds(g, w.0, g.schema[w.0].constraints[w.1]));
                } else {
                    let y = choose|y: int| !(0 <= y < k
                        ==> constraint_holds(g, t as int, #[trigger] g.schema[t as int].constraints[y]));
                    assert(!constraint_holds(g, t as int, g.schema[t as int].constraints[y]));
                }
            }
        }
        t = t + 1;
    }
    proof {
        assert forall|x: int, y: int| 0 <= x < g.schema.len() && x < g.tables.len() && 0 <= y < g.schema[x].constraints.len()
            implies fits_constraint(g, x, #[trigger] g.schema[x].constraints[y]) by {}
        if acc {
            assert forall|x: int, y: int| 0 <= x < g.schema.len() && x < g.tables.len() && 0 <= y < g.schema[x].constraints.len()
                implies constraint_holds(g, x, #[trigger] g.schema[x].constraints[y]) by {}
        } else {
            let w = choose|x: int, y: int| !(0 <= x < t && 0 <= y < g.schema[x].constraints.len()
                ==> constraint_holds(g, x, #[trigger] g.schema[x].constraints[y]));
            assert(!constraint_holds(g, w.0, g.schema[w.0].constraints[w.1]));
            assert(!constraints_hold(g));
        }
    }
    Ok(acc)
}

/// `spec::constraints::constraint_holds` for constraint `k` of table `t`.
fn constraint_holds_exec(db: &EDatabase, t: usize, k: usize) -> (r: Result<bool, Capacity>)
    requires db_wf(db@), t < db.schema.len(), k < db.schema@[t as int].constraints.len(),
    ensures
        match r {
            Ok(b) => fits_constraint(db@, t as int, db@.schema[t as int].constraints[k as int])
                && b == constraint_holds(db@, t as int, db@.schema[t as int].constraints[k as int]),
            Err(_) => !fits_constraint(db@, t as int, db@.schema[t as int].constraints[k as int]),
        },
{
    let ghost gs = db@.schema;
    proof {
        lemma_wf_table_rows(db, t as int);
        lemma_constraint_wf_at(gs, t as int, k as int);
        lemma_db_wf_ts_ok(db@);
        assert(gs[t as int].constraints[k as int] == view_constraint(db.schema@[t as int].constraints@[k as int]));
    }
    let n = db.schema[t].columns.len();
    match &db.schema[t].constraints[k] {
        EConstraint::Key { cols, primary, nulls_distinct } => {
            proof { lemma_cols_below(cols@, n as nat); }
            Ok(key_holds_exec(&db.tables[t], n, cols, *primary, *nulls_distinct))
        },
        EConstraint::ForeignKey { cols, table, ref_cols, match_full } => {
            proof {
                lemma_wf_table_rows(db, *table as int);
                lemma_cols_below(cols@, n as nat);
                lemma_cols_below(ref_cols@, gs[*table as int].columns.len());
            }
            let m = db.schema[*table].columns.len();
            Ok(fk_holds_exec(&db.tables[t], n, cols, &db.tables[*table], m, ref_cols, *match_full))
        },
        EConstraint::Check(p) => check_holds_exec(db, t, p),
    }
}

/// Table `t` of a well-formed database: its spec relation is the view of the executable rows, and every row has
/// the declared width.
proof fn lemma_wf_table_rows(db: &EDatabase, t: int)
    requires db_wf(db@), 0 <= t < db.tables.len(),
    ensures
        db@.tables[t] == view_rows(db.tables@[t]@),
        db@.schema[t] == view_table_schema(db.schema@[t]),
        rows_width(db.tables@[t]@, db.schema@[t].columns.len() as int),
{
    let rows = db.tables@[t]@;
    assert(db@.tables[t] == view_rows(rows));
    assert forall|i: int| 0 <= i < rows.len() implies (#[trigger] rows[i]).len() == db.schema@[t].columns.len() by {
        lemma_view_rows_index(rows, i);
        assert(row_in_table(db@.tables[t][i], db@.schema[t]));
    }
}

/// `spec::constraints::key_holds`: PRIMARY KEY / UNIQUE on the rows of a table of width `n` (a primary key has
/// no NULL cell, then no two rows collide; quadratic).
fn key_holds_exec(rows: &Vec<ERow>, n: usize, cols: &Vec<usize>, primary: bool, nulls_distinct: bool) -> (b: bool)
    requires rows_width(rows@, n as int), cols_below(cols@, n as int),
    ensures b == key_holds(view_rows(rows@), view_cols(cols@), primary, nulls_distinct),
{
    let ghost g = view_rows(rows@);
    let ghost vc = view_cols(cols@);
    if primary {
        let mut i: usize = 0;
        while i < rows.len()
            invariant
                i <= rows.len(), g == view_rows(rows@), vc == view_cols(cols@), primary,
                rows_width(rows@, n as int), cols_below(cols@, n as int),
                forall|j: int| 0 <= j < i ==> !has_null(key_of(#[trigger] g[j], vc)),
            decreases rows.len() - i,
        {
            proof { lemma_view_rows_index(rows@, i as int); }
            if key_has_null_exec(&rows[i], cols) {
                assert(has_null(key_of(g[i as int], vc)));
                return false;
            }
            i = i + 1;
        }
    }
    let mut j: usize = 0;
    while j < rows.len()
        invariant
            j <= rows.len(), g == view_rows(rows@), vc == view_cols(cols@),
            rows_width(rows@, n as int), cols_below(cols@, n as int),
            primary ==> forall|x: int| 0 <= x < rows.len() ==> !has_null(key_of(#[trigger] g[x], vc)),
            forall|x: int, y: int| 0 <= x < y < j ==> !key_collides(#[trigger] g[x], #[trigger] g[y], vc, nulls_distinct),
        decreases rows.len() - j,
    {
        let mut i: usize = 0;
        while i < j
            invariant
                i <= j, j < rows.len(), g == view_rows(rows@), vc == view_cols(cols@),
                rows_width(rows@, n as int), cols_below(cols@, n as int),
                forall|x: int| 0 <= x < i ==> !key_collides(#[trigger] g[x], g[j as int], vc, nulls_distinct),
            decreases j - i,
        {
            proof { lemma_view_rows_index(rows@, i as int); lemma_view_rows_index(rows@, j as int); }
            let same = keys_not_distinct_exec(&rows[i], &rows[j], cols);
            let collides = same && !(nulls_distinct && key_has_null_exec(&rows[i], cols));
            if collides {
                assert(key_collides(g[i as int], g[j as int], vc, nulls_distinct));
                return false;
            }
            i = i + 1;
        }
        proof {
            assert forall|x: int, y: int| 0 <= x < y < j + 1 implies
                !key_collides(#[trigger] g[x], #[trigger] g[y], vc, nulls_distinct) by {
                if y == j { assert(!key_collides(g[x], g[j as int], vc, nulls_distinct)); }
            }
        }
        j = j + 1;
    }
    true
}

/// `spec::constraints::fk_holds`: every row of a table of width `n` references a row of `target` (width `m`).
fn fk_holds_exec(rows: &Vec<ERow>, n: usize, cols: &Vec<usize>, target: &Vec<ERow>, m: usize, ref_cols: &Vec<usize>,
    match_full: bool) -> (b: bool)
    requires
        cols.len() == ref_cols.len(), rows_width(rows@, n as int), cols_below(cols@, n as int),
        rows_width(target@, m as int), cols_below(ref_cols@, m as int),
    ensures b == fk_holds(view_rows(rows@), view_cols(cols@), view_rows(target@), view_cols(ref_cols@), match_full),
{
    let ghost g = view_rows(rows@);
    let mut i: usize = 0;
    while i < rows.len()
        invariant
            i <= rows.len(), g == view_rows(rows@), cols.len() == ref_cols.len(),
            rows_width(rows@, n as int), cols_below(cols@, n as int),
            rows_width(target@, m as int), cols_below(ref_cols@, m as int),
            forall|x: int| 0 <= x < i ==> fk_row_holds(#[trigger] g[x], view_cols(cols@), view_rows(target@),
                view_cols(ref_cols@), match_full),
        decreases rows.len() - i,
    {
        proof { lemma_view_rows_index(rows@, i as int); }
        assert(rows@[i as int].len() == n);
        if !fk_row_holds_exec(&rows[i], cols, target, m, ref_cols, match_full) {
            assert(!fk_row_holds(g[i as int], view_cols(cols@), view_rows(target@), view_cols(ref_cols@), match_full));
            return false;
        }
        i = i + 1;
    }
    true
}

/// `spec::constraints::fk_row_holds`: one referencing row (a tuple with a NULL cell is exempt under MATCH SIMPLE,
/// and under MATCH FULL only when all cells are NULL; otherwise some target row must match).
fn fk_row_holds_exec(r: &ERow, cols: &Vec<usize>, target: &Vec<ERow>, m: usize, ref_cols: &Vec<usize>,
    match_full: bool) -> (b: bool)
    requires
        cols.len() == ref_cols.len(), cols_below(cols@, r.len() as int),
        rows_width(target@, m as int), cols_below(ref_cols@, m as int),
    ensures b == fk_row_holds(view_row(r@), view_cols(cols@), view_rows(target@), view_cols(ref_cols@), match_full),
{
    let ghost k = key_of(view_row(r@), view_cols(cols@));
    let ghost g = view_rows(target@);
    let ghost vr = view_cols(ref_cols@);
    if key_has_null_exec(r, cols) {
        return !match_full || key_all_null_exec(r, cols);
    }
    let mut j: usize = 0;
    while j < target.len()
        invariant
            j <= target.len(), cols.len() == ref_cols.len(), cols_below(cols@, r.len() as int),
            rows_width(target@, m as int), cols_below(ref_cols@, m as int),
            k == key_of(view_row(r@), view_cols(cols@)), g == view_rows(target@), vr == view_cols(ref_cols@),
            forall|x: int| 0 <= x < j ==> !key_matches(k, key_of(#[trigger] g[x], vr)),
        decreases target.len() - j,
    {
        proof { lemma_view_rows_index(target@, j as int); }
        if key_matches_exec(r, cols, &target[j], ref_cols) {
            assert(key_matches(k, key_of(g[j as int], vr)));
            return true;
        }
        j = j + 1;
    }
    false
}

/// `spec::constraints::check_holds`: CHECK `p` on every row of table `t`. Every row is evaluated, so the result is
/// `Capacity` iff some row leaves the domain, whichever rows violate the CHECK.
fn check_holds_exec(db: &EDatabase, t: usize, p: &EPred) -> (r: Result<bool, Capacity>)
    requires db_ts_ok(db@), t < db.tables.len(),
    ensures
        match r {
            Ok(b) => fits_check(db@, db@.tables[t as int], view_pred(*p)) && b == check_holds(db@, db@.tables[t as int], view_pred(*p)),
            Err(_) => !fits_check(db@, db@.tables[t as int], view_pred(*p)),
        },
{
    let rows = &db.tables[t];
    let ghost g = db@.tables[t as int];
    let ghost vp = view_pred(*p);
    proof { assert(g == view_rows(rows@)); }
    let mut acc = true;
    let mut i: usize = 0;
    while i < rows.len()
        invariant
            i <= rows.len(), db_ts_ok(db@), t < db.tables.len(), rows == &db.tables[t as int],
            g == db@.tables[t as int], g == view_rows(rows@), vp == view_pred(*p),
            forall|x: int| 0 <= x < i ==> fits_pred(db@, #[trigger] g[x], vp),
            acc == (forall|x: int| 0 <= x < i ==> check_row_holds(db@, #[trigger] g[x], vp)),
        decreases rows.len() - i,
    {
        proof {
            lemma_view_rows_index(rows@, i as int);
            assert(rows_ts_ok(db@.tables[t as int]));
            assert(row_ts_ok(g[i as int]));
        }
        match exec_pred(db, &rows[i], p) {
            Err(c) => {
                assert(!fits_pred(db@, g[i as int], vp));
                return Err(c);
            },
            Ok(res) => {
                // `spec::constraints::check_row_holds`: `True` and `Unknown` accept; `False` and a SQL error reject.
                let ok = match res {
                    Ok(Truth::False) => false,
                    Ok(_) => true,
                    Err(_) => false,
                };
                proof {
                    assert(ok == check_row_holds(db@, g[i as int], vp));
                    assert((acc && ok) == (forall|x: int| 0 <= x < i + 1 ==> check_row_holds(db@, #[trigger] g[x], vp))) by {
                        if acc && ok {
                            assert forall|x: int| 0 <= x < i + 1 implies check_row_holds(db@, #[trigger] g[x], vp) by {
                                if x == i as int { assert(ok); }
                            }
                        }
                        if !ok {
                            assert(!check_row_holds(db@, g[i as int], vp));
                        }
                    }
                }
                acc = acc && ok;
            },
        }
        i = i + 1;
    }
    Ok(acc)
}

// ------------------------------------------------------------------ key tuples of executable rows

/// Column positions of `cols` index every row of width `n`.
pub open spec fn cols_below(cols: Seq<usize>, n: int) -> bool {
    forall|c: int| 0 <= c < cols.len() ==> (#[trigger] cols[c] as int) < n
}

/// Rows of width `n`, as a requirement on an executable table.
pub open spec fn rows_width(rows: Seq<ERow>, n: int) -> bool {
    forall|i: int| 0 <= i < rows.len() ==> (#[trigger] rows[i]).len() == n
}

proof fn lemma_view_rows_index(rows: Seq<ERow>, i: int)
    requires 0 <= i < rows.len(),
    ensures view_rows(rows)[i] == view_row(rows[i]@),
{
}

proof fn lemma_key_len(r: Seq<EVal>, cols: Seq<usize>)
    ensures key_of(view_row(r), view_cols(cols)).len() == cols.len(),
{
}

proof fn lemma_key_index(r: Seq<EVal>, cols: Seq<usize>, i: int)
    requires 0 <= i < cols.len(), cols_below(cols, r.len() as int),
    ensures
        key_of(view_row(r), view_cols(cols)).len() == cols.len(),
        key_of(view_row(r), view_cols(cols))[i] == r[cols[i] as int]@,
{
    assert(cols[i] as int >= 0);
    assert(view_cols(cols)[i] == cols[i] as nat);
}

/// `has_null` of the key tuple of `r` on `cols`.
fn key_has_null_exec(r: &ERow, cols: &Vec<usize>) -> (b: bool)
    requires cols_below(cols@, r.len() as int),
    ensures b == has_null(key_of(view_row(r@), view_cols(cols@))),
{
    let ghost k = key_of(view_row(r@), view_cols(cols@));
    proof { lemma_key_len(r@, cols@); }
    let mut i: usize = 0;
    while i < cols.len()
        invariant
            i <= cols.len(), cols_below(cols@, r.len() as int), k == key_of(view_row(r@), view_cols(cols@)),
            k.len() == cols.len(),
            forall|j: int| 0 <= j < i ==> !((#[trigger] k[j]) is Null),
        decreases cols.len() - i,
    {
        proof { lemma_key_index(r@, cols@, i as int); }
        if matches!(r[cols[i]], EVal::Null) {
            assert(k[i as int] is Null);
            return true;
        }
        i = i + 1;
    }
    false
}

/// `all_null` of the key tuple of `r` on `cols`.
fn key_all_null_exec(r: &ERow, cols: &Vec<usize>) -> (b: bool)
    requires cols_below(cols@, r.len() as int),
    ensures b == all_null(key_of(view_row(r@), view_cols(cols@))),
{
    let ghost k = key_of(view_row(r@), view_cols(cols@));
    proof { lemma_key_len(r@, cols@); }
    let mut i: usize = 0;
    while i < cols.len()
        invariant
            i <= cols.len(), cols_below(cols@, r.len() as int), k == key_of(view_row(r@), view_cols(cols@)),
            k.len() == cols.len(),
            forall|j: int| 0 <= j < i ==> (#[trigger] k[j]) is Null,
        decreases cols.len() - i,
    {
        proof { lemma_key_index(r@, cols@, i as int); }
        if !matches!(r[cols[i]], EVal::Null) {
            assert(!(k[i as int] is Null));
            return false;
        }
        i = i + 1;
    }
    true
}

/// `row_not_distinct` of the two key tuples.
fn keys_not_distinct_exec(r: &ERow, s: &ERow, cols: &Vec<usize>) -> (b: bool)
    requires cols_below(cols@, r.len() as int), cols_below(cols@, s.len() as int),
    ensures b == row_not_distinct(key_of(view_row(r@), view_cols(cols@)), key_of(view_row(s@), view_cols(cols@))),
{
    let ghost kr = key_of(view_row(r@), view_cols(cols@));
    let ghost ks = key_of(view_row(s@), view_cols(cols@));
    proof { lemma_key_len(r@, cols@); lemma_key_len(s@, cols@); }
    let mut i: usize = 0;
    while i < cols.len()
        invariant
            i <= cols.len(), cols_below(cols@, r.len() as int), cols_below(cols@, s.len() as int),
            kr == key_of(view_row(r@), view_cols(cols@)), ks == key_of(view_row(s@), view_cols(cols@)),
            kr.len() == cols.len(), ks.len() == cols.len(),
            forall|j: int| 0 <= j < i ==> val_not_distinct(#[trigger] kr[j], ks[j]),
        decreases cols.len() - i,
    {
        proof { lemma_key_index(r@, cols@, i as int); lemma_key_index(s@, cols@, i as int); }
        if !val_not_distinct_exec(&r[cols[i]], &s[cols[i]]) {
            assert(!val_not_distinct(kr[i as int], ks[i as int]));
            return false;
        }
        i = i + 1;
    }
    true
}

/// `key_matches` of `r`'s tuple on `cols` against `s`'s tuple on `ref_cols`.
fn key_matches_exec(r: &ERow, cols: &Vec<usize>, s: &ERow, ref_cols: &Vec<usize>) -> (b: bool)
    requires cols.len() == ref_cols.len(), cols_below(cols@, r.len() as int), cols_below(ref_cols@, s.len() as int),
    ensures b == key_matches(key_of(view_row(r@), view_cols(cols@)), key_of(view_row(s@), view_cols(ref_cols@))),
{
    let ghost kr = key_of(view_row(r@), view_cols(cols@));
    let ghost ks = key_of(view_row(s@), view_cols(ref_cols@));
    proof { lemma_key_len(r@, cols@); lemma_key_len(s@, ref_cols@); }
    let mut i: usize = 0;
    while i < cols.len()
        invariant
            i <= cols.len(), cols.len() == ref_cols.len(),
            cols_below(cols@, r.len() as int), cols_below(ref_cols@, s.len() as int),
            kr == key_of(view_row(r@), view_cols(cols@)), ks == key_of(view_row(s@), view_cols(ref_cols@)),
            kr.len() == cols.len(), ks.len() == cols.len(),
            forall|j: int| 0 <= j < i ==> compare(#[trigger] kr[j], ks[j]) == Some(0int),
        decreases cols.len() - i,
    {
        proof { lemma_key_index(r@, cols@, i as int); lemma_key_index(s@, ref_cols@, i as int); }
        let eq = match compare_exec(&r[cols[i]], &s[ref_cols[i]]) {
            Some(c) => c == 0,
            None => false,
        };
        if !eq {
            assert(compare(kr[i as int], ks[i as int]) != Some(0int));
            return false;
        }
        i = i + 1;
    }
    true
}

} // verus!
