//! L1, unique bound database (engine toolkit; nothing here names a query, a table or a column).
//!
//! A storage stores the declared columns `cols` of table `t` as `link::query::proj_all(db.tables[t], cols)`, in
//! canonical row order (the generated `stores/<name>/declaration.rs`, `stored_relations`). Write the declarations
//! of all storage uses of an engine as one list `decls` of `(table, cols)` pairs. When they cover the schema
//! (`covers_schema`: every table is declared, and every column of every table is stored somewhere) and two
//! well-formed databases of one schema have the same stored relations (`stored_rels`), the databases are equal
//! (`lemma_unique_bound_db`).
//!
//! Recipe for an engine crate: for two databases bound to the same parts, each storage's
//! `lemma_represents_determines` gives equal `stored_relations` per storage; each storage's `stored_relations(db)`
//! is `stored_rels(db, decls_s)` for its declared pairs (extensional equality, `=~=`); `lemma_stored_rels_concat`
//! joins the storages; `covers_schema(schema_spec(), decls)` is decided `by (compute)`. Then an author proves the
//! claim for one chosen database and transfers it to every bound database.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::types::*;
use crate::spec::typing::*;
use crate::spec::constraints::nat_in;
use crate::link::query::{proj, proj_all};

verus! {

/// The stored relations of `db` under the declarations `decls`: per declaration `(t, cols)`, the columns `cols`
/// of every row of `db.tables[t]`, in row order.
pub open spec fn stored_rels(db: Database, decls: Seq<(nat, Seq<nat>)>) -> Seq<Seq<Row>> {
    Seq::new(decls.len(), |s: int| proj_all(db.tables[decls[s].0 as int], decls[s].1))
}

/// The stored relations of concatenated declaration lists are the concatenated relations.
pub proof fn lemma_stored_rels_concat(db: Database, d1: Seq<(nat, Seq<nat>)>, d2: Seq<(nat, Seq<nat>)>)
    ensures stored_rels(db, d1 + d2) == stored_rels(db, d1) + stored_rels(db, d2),
{
    assert(stored_rels(db, d1 + d2) =~= stored_rels(db, d1) + stored_rels(db, d2));
}

/// Some declaration stores table `t` (with any columns, even none: its row count is then still stored).
pub open spec fn decl_has_table(decls: Seq<(nat, Seq<nat>)>, t: nat) -> bool
    decreases decls.len(),
{
    decls.len() > 0 && (decls.last().0 == t || decl_has_table(decls.drop_last(), t))
}

/// Some declaration stores column `c` of table `t`.
pub open spec fn decl_has_col(decls: Seq<(nat, Seq<nat>)>, t: nat, c: nat) -> bool
    decreases decls.len(),
{
    decls.len() > 0 && ((decls.last().0 == t && nat_in(decls.last().1, c)) || decl_has_col(decls.drop_last(), t, c))
}

/// Columns `0..k` of table `t` are stored.
pub open spec fn cols_covered(decls: Seq<(nat, Seq<nat>)>, t: nat, k: nat) -> bool
    decreases k,
{
    k == 0 || (decl_has_col(decls, t, (k - 1) as nat) && cols_covered(decls, t, (k - 1) as nat))
}

/// Tables `0..n` of the schema are declared with all their columns.
pub open spec fn tables_covered(schema: Schema, decls: Seq<(nat, Seq<nat>)>, n: nat) -> bool
    decreases n,
{
    n == 0 || {
        let t = (n - 1) as nat;
        &&& decl_has_table(decls, t)
        &&& cols_covered(decls, t, if t < schema.len() { schema[t as int].columns.len() } else { 0 })
        &&& tables_covered(schema, decls, t)
    }
}

/// Complete coverage: every table of the schema is declared, with every column (recursive, so `by (compute)`
/// decides it for a concrete schema and declaration list).
pub open spec fn covers_schema(schema: Schema, decls: Seq<(nat, Seq<nat>)>) -> bool {
    tables_covered(schema, decls, schema.len())
}

/// A position of `x` in `s`.
proof fn lemma_nat_in_witness(s: Seq<nat>, x: nat) -> (k: int)
    requires nat_in(s, x),
    ensures 0 <= k < s.len(), s[k] == x,
    decreases s.len(),
{
    if s.last() == x {
        s.len() - 1
    } else {
        lemma_nat_in_witness(s.drop_last(), x)
    }
}

/// A declaration of table `t`.
pub proof fn lemma_decl_has_table_witness(decls: Seq<(nat, Seq<nat>)>, t: nat) -> (s: int)
    requires decl_has_table(decls, t),
    ensures 0 <= s < decls.len(), decls[s].0 == t,
    decreases decls.len(),
{
    if decls.last().0 == t {
        decls.len() - 1
    } else {
        lemma_decl_has_table_witness(decls.drop_last(), t)
    }
}

/// A declaration of table `t` and the position `k` in it of column `c`.
pub proof fn lemma_decl_has_col_witness(decls: Seq<(nat, Seq<nat>)>, t: nat, c: nat) -> (sk: (int, int))
    requires decl_has_col(decls, t, c),
    ensures
        0 <= sk.0 < decls.len(),
        decls[sk.0].0 == t,
        0 <= sk.1 < decls[sk.0].1.len(),
        decls[sk.0].1[sk.1] == c,
    decreases decls.len(),
{
    if decls.last().0 == t && nat_in(decls.last().1, c) {
        let k = lemma_nat_in_witness(decls.last().1, c);
        (decls.len() - 1, k)
    } else {
        lemma_decl_has_col_witness(decls.drop_last(), t, c)
    }
}

/// Column `c < k` of a table with `cols_covered(.., k)` is stored.
proof fn lemma_cols_covered(decls: Seq<(nat, Seq<nat>)>, t: nat, k: nat, c: nat)
    requires cols_covered(decls, t, k), c < k,
    ensures decl_has_col(decls, t, c),
    decreases k,
{
    if c < k - 1 {
        lemma_cols_covered(decls, t, (k - 1) as nat, c);
    }
}

/// The quantified meaning of `covers_schema`.
pub proof fn lemma_covers_schema(schema: Schema, decls: Seq<(nat, Seq<nat>)>, t: nat)
    requires covers_schema(schema, decls), t < schema.len(),
    ensures
        decl_has_table(decls, t),
        forall|c: nat| c < schema[t as int].columns.len() ==> #[trigger] decl_has_col(decls, t, c),
{
    lemma_tables_covered(schema, decls, schema.len(), t);
    assert forall|c: nat| c < schema[t as int].columns.len() implies #[trigger] decl_has_col(decls, t, c) by {
        lemma_cols_covered(decls, t, schema[t as int].columns.len(), c);
    }
}

proof fn lemma_tables_covered(schema: Schema, decls: Seq<(nat, Seq<nat>)>, n: nat, t: nat)
    requires tables_covered(schema, decls, n), t < n, n <= schema.len(),
    ensures decl_has_table(decls, t), cols_covered(decls, t, schema[t as int].columns.len()),
    decreases n,
{
    if t < n - 1 {
        lemma_tables_covered(schema, decls, (n - 1) as nat, t);
    }
}

/// L1. Two well-formed databases of one schema with the same stored relations under covering declarations are
/// equal.
pub proof fn lemma_unique_bound_db(a: Database, b: Database, decls: Seq<(nat, Seq<nat>)>)
    requires
        a.schema == b.schema,
        db_wf(a),
        db_wf(b),
        covers_schema(a.schema, decls),
        stored_rels(a, decls) == stored_rels(b, decls),
    ensures a == b,
{
    let n = a.schema.len();
    assert forall|t: int| 0 <= t < n implies #[trigger] a.tables[t] == b.tables[t] by {
        lemma_covers_schema(a.schema, decls, t as nat);
        let s = lemma_decl_has_table_witness(decls, t as nat);
        assert(stored_rels(a, decls)[s] == stored_rels(b, decls)[s]);
        assert(proj_all(a.tables[t], decls[s].1).len() == proj_all(b.tables[t], decls[s].1).len());
        let rows_a = a.tables[t];
        let rows_b = b.tables[t];
        assert forall|i: int| 0 <= i < rows_a.len() implies #[trigger] rows_a[i] == rows_b[i] by {
            assert(row_in_table(rows_a[i], a.schema[t]));
            assert(row_in_table(rows_b[i], b.schema[t]));
            assert forall|c: int| 0 <= c < rows_a[i].len() implies #[trigger] rows_a[i][c] == rows_b[i][c] by {
                assert(decl_has_col(decls, t as nat, c as nat));
                let (s2, k) = lemma_decl_has_col_witness(decls, t as nat, c as nat);
                assert(stored_rels(a, decls)[s2] == stored_rels(b, decls)[s2]);
                let pa = proj_all(rows_a, decls[s2].1);
                let pb = proj_all(rows_b, decls[s2].1);
                assert(pa[i] == proj(rows_a[i], decls[s2].1));
                assert(pb[i] == proj(rows_b[i], decls[s2].1));
                assert(pa[i][k] == rows_a[i][c]);
                assert(pb[i][k] == rows_b[i][c]);
            }
            assert(rows_a[i] =~= rows_b[i]);
        }
        assert(rows_a =~= rows_b);
    }
    assert(a.tables =~= b.tables);
}

} // verus!
