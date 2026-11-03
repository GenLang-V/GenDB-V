//! Checked examples of declared-schema well-formedness (`spec::constraints::constraints_wf`), decided by evaluation
//! on the TPC-H schema and on small schemas that PostgreSQL rejects or whose meaning is not represented (each must
//! be ill-formed, so no schema with such a constraint passes `schema_wf`, `check_db` or a statement's
//! `lemma_query_wf`). Instance behaviour (keys with NULLs, MATCH SIMPLE / FULL, CHECK Unknown / False / error,
//! Capacity) is exercised through the verified checker on the fixtures of `sqlspec/tests/fixtures/constraints/`.
use vstd::prelude::*;
use crate::spec::int::*;
use crate::spec::scalar::*;
use crate::spec::types::*;
use crate::spec::ast::*;
use crate::spec::constraints::*;
use crate::pins::tpch_schema::*;

verus! {

pub open spec fn int_col(nullable: bool) -> Column {
    Column { ty: SqlType::Int4, nullable }
}

pub open spec fn table(columns: Seq<Column>, constraints: Seq<Constraint>) -> TableSchema {
    TableSchema { columns, constraints }
}

/// `p(k int PRIMARY KEY, u int, UNIQUE (u))`.
pub open spec fn parent() -> TableSchema {
    table(seq![int_col(false), int_col(true)], seq![pk(seq![0nat]),
        Constraint::Key { cols: seq![1nat], primary: false, nulls_distinct: true }])
}

/// `CHECK (col > 0)`.
pub open spec fn positive(col: nat) -> Constraint {
    Constraint::Check(Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(col),
        b: Expr::Lit(Literal::Int { v: 0, kind: IntKind::Int4 }) })
}

/// The schema of `benchmarks/tpc-h/schema.sql` with its 8 primary keys and 7 foreign keys (the composite
/// lineitem -> partsupp reference included) is well-formed.
pub proof fn pin_tpch_constraints_wf()
    ensures constraints_wf(tpch_schema()), schema_wf(tpch_schema()),
{
    assert(constraints_wf(tpch_schema())) by (compute);
    assert(schema_wf(tpch_schema())) by (compute);
}

/// Accepted: MATCH FULL composite FK with a permuted, repeated referencing list onto a key's column set in another
/// order; a self reference; a CHECK over the row; bigint -> integer key; char(n) -> varchar key.
pub proof fn pin_constraints_wf_accepted()
    ensures
        constraints_wf(seq![
            table(seq![int_col(false), int_col(false)], seq![pk(seq![0nat, 1nat])]),
            table(seq![int_col(false), int_col(true), Column { ty: SqlType::Int8, nullable: true }], seq![
                pk(seq![0nat]),
                Constraint::ForeignKey { cols: seq![1nat, 1nat], table: 0, ref_cols: seq![1nat, 0nat], match_full: true },
                Constraint::ForeignKey { cols: seq![2nat], table: 1, ref_cols: seq![0nat], match_full: false },
                positive(1),
            ]),
            table(seq![Column { ty: SqlType::Varchar { max_chars: 4 }, nullable: false }], seq![pk(seq![0nat])]),
            table(seq![Column { ty: SqlType::Bpchar { len: 4 }, nullable: true }],
                seq![Constraint::ForeignKey { cols: seq![0nat], table: 2, ref_cols: seq![0nat], match_full: false }]),
        ]),
{
    assert(constraints_wf(seq![
        table(seq![int_col(false), int_col(false)], seq![pk(seq![0nat, 1nat])]),
        table(seq![int_col(false), int_col(true), Column { ty: SqlType::Int8, nullable: true }], seq![
            pk(seq![0nat]),
            Constraint::ForeignKey { cols: seq![1nat, 1nat], table: 0, ref_cols: seq![1nat, 0nat], match_full: true },
            Constraint::ForeignKey { cols: seq![2nat], table: 1, ref_cols: seq![0nat], match_full: false },
            positive(1),
        ]),
        table(seq![Column { ty: SqlType::Varchar { max_chars: 4 }, nullable: false }], seq![pk(seq![0nat])]),
        table(seq![Column { ty: SqlType::Bpchar { len: 4 }, nullable: true }],
            seq![Constraint::ForeignKey { cols: seq![0nat], table: 2, ref_cols: seq![0nat], match_full: false }]),
    ])) by (compute);
}

/// A child table `c(x, ...)` next to `parent()` with one constraint `c`.
pub open spec fn with_child(columns: Seq<Column>, c: Constraint) -> Schema {
    seq![parent(), table(columns, seq![c])]
}

/// Rejected declarations (PostgreSQL error or unrepresented meaning in brackets).
pub proof fn pin_constraints_wf_rejected()
    ensures
        // FK onto a non-key column [42830].
        !constraints_wf(seq![table(seq![int_col(false), int_col(true)], seq![pk(seq![0nat])]),
            table(seq![int_col(true)], seq![fk(seq![0nat], 0, seq![1nat])])]),
        // FK arity differs from the referenced key [42830].
        !constraints_wf(with_child(seq![int_col(true), int_col(true)], fk(seq![0nat, 1nat], 0, seq![0nat]))),
        // Repeated referenced column [42830].
        !constraints_wf(with_child(seq![int_col(true), int_col(true)], fk(seq![0nat, 1nat], 0, seq![0nat, 0nat]))),
        // Referenced table does not exist [42P01].
        !constraints_wf(with_child(seq![int_col(true)], fk(seq![0nat], 7, seq![0nat]))),
        // numeric referencing integer [42804].
        !constraints_wf(with_child(seq![Column { ty: SqlType::Numeric { precision: 5, scale: 0 }, nullable: true }],
            fk(seq![0nat], 0, seq![0nat]))),
        // date referencing integer [42804].
        !constraints_wf(with_child(seq![Column { ty: SqlType::Date, nullable: true }], fk(seq![0nat], 0, seq![0nat]))),
        // varchar referencing char(n): blank-insensitive bpchar equality, not represented.
        !constraints_wf(seq![table(seq![Column { ty: SqlType::Bpchar { len: 3 }, nullable: false }], seq![pk(seq![0nat])]),
            table(seq![Column { ty: SqlType::Varchar { max_chars: 3 }, nullable: true }], seq![fk(seq![0nat], 0, seq![0nat])])]),
        // Two primary keys [42P16].
        !constraints_wf(seq![table(seq![int_col(false), int_col(false)], seq![pk(seq![0nat]), pk(seq![1nat])])]),
        // Primary key on a nullable column (PostgreSQL makes it NOT NULL; the declaration must say so).
        !constraints_wf(seq![table(seq![int_col(true)], seq![pk(seq![0nat])])]),
        // Repeated key column [42701]; empty key; key column out of range.
        !constraints_wf(seq![table(seq![int_col(false)], seq![pk(seq![0nat, 0nat])])]),
        !constraints_wf(seq![table(seq![int_col(false)], seq![pk(Seq::<nat>::empty())])]),
        !constraints_wf(seq![table(seq![int_col(false)], seq![pk(seq![1nat])])]),
        // CHECK with a subquery [0A000]: ill-typed over the empty schema.
        !constraints_wf(seq![table(seq![int_col(true)], seq![Constraint::Check(Pred::Exists(Box::new(Query::Table(0))))])]),
        // CHECK over a column the row does not have; CHECK that is not boolean.
        !constraints_wf(seq![table(seq![int_col(true)], seq![positive(1)])]),
        !constraints_wf(seq![table(seq![int_col(true)], seq![Constraint::Check(Pred::OfBool(Expr::Col(0)))])]),
{
    assert(!constraints_wf(seq![table(seq![int_col(false), int_col(true)], seq![pk(seq![0nat])]),
        table(seq![int_col(true)], seq![fk(seq![0nat], 0, seq![1nat])])])) by (compute);
    assert(!constraints_wf(with_child(seq![int_col(true), int_col(true)], fk(seq![0nat, 1nat], 0, seq![0nat])))) by (compute);
    assert(!constraints_wf(with_child(seq![int_col(true), int_col(true)], fk(seq![0nat, 1nat], 0, seq![0nat, 0nat])))) by (compute);
    assert(!constraints_wf(with_child(seq![int_col(true)], fk(seq![0nat], 7, seq![0nat])))) by (compute);
    assert(!constraints_wf(with_child(seq![Column { ty: SqlType::Numeric { precision: 5, scale: 0 }, nullable: true }],
        fk(seq![0nat], 0, seq![0nat])))) by (compute);
    assert(!constraints_wf(with_child(seq![Column { ty: SqlType::Date, nullable: true }], fk(seq![0nat], 0, seq![0nat])))) by (compute);
    assert(!constraints_wf(seq![table(seq![Column { ty: SqlType::Bpchar { len: 3 }, nullable: false }], seq![pk(seq![0nat])]),
        table(seq![Column { ty: SqlType::Varchar { max_chars: 3 }, nullable: true }], seq![fk(seq![0nat], 0, seq![0nat])])])) by (compute);
    assert(!constraints_wf(seq![table(seq![int_col(false), int_col(false)], seq![pk(seq![0nat]), pk(seq![1nat])])])) by (compute);
    assert(!constraints_wf(seq![table(seq![int_col(true)], seq![pk(seq![0nat])])])) by (compute);
    assert(!constraints_wf(seq![table(seq![int_col(false)], seq![pk(seq![0nat, 0nat])])])) by (compute);
    assert(!constraints_wf(seq![table(seq![int_col(false)], seq![pk(Seq::<nat>::empty())])])) by (compute);
    assert(!constraints_wf(seq![table(seq![int_col(false)], seq![pk(seq![1nat])])])) by (compute);
    assert(!constraints_wf(seq![table(seq![int_col(true)], seq![Constraint::Check(Pred::Exists(Box::new(Query::Table(0))))])])) by (compute);
    assert(!constraints_wf(seq![table(seq![int_col(true)], seq![positive(1)])])) by (compute);
    assert(!constraints_wf(seq![table(seq![int_col(true)], seq![Constraint::Check(Pred::OfBool(Expr::Col(0)))])])) by (compute);
}

} // verus!
