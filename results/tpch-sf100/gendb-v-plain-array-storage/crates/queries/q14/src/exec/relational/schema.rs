//! Runtime database representation shared by the evaluator, the emitted per-query schema (`query_schema`) and the
//! host ABI, with its view onto `spec::value::Database`. Table id = index into `schema` and `tables` (DDL order);
//! a row is `ERow` in column order with the value encoding of `exec::value`.
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::typing::*;
use crate::exec::value::*;
use crate::exec::domain::*;
use crate::exec::ast::*;

verus! {

/// Exec mirror of `spec::types::Constraint`.
pub enum EConstraint {
    Key { cols: Vec<usize>, primary: bool, nulls_distinct: bool },
    ForeignKey { cols: Vec<usize>, table: usize, ref_cols: Vec<usize>, match_full: bool },
    Check(EPred),
}

pub struct ETableSchema {
    pub columns: Vec<Column>,
    pub constraints: Vec<EConstraint>,
}

pub open spec fn view_cols(cols: Seq<usize>) -> Seq<nat> {
    cols.map_values(|c: usize| c as nat)
}

pub open spec fn view_constraint(c: EConstraint) -> Constraint {
    match c {
        EConstraint::Key { cols, primary, nulls_distinct } => Constraint::Key { cols: view_cols(cols@), primary, nulls_distinct },
        EConstraint::ForeignKey { cols, table, ref_cols, match_full } =>
            Constraint::ForeignKey { cols: view_cols(cols@), table: table as nat, ref_cols: view_cols(ref_cols@), match_full },
        EConstraint::Check(p) => Constraint::Check(view_pred(p)),
    }
}

pub open spec fn view_constraints(cs: Seq<EConstraint>) -> Seq<Constraint> {
    cs.map_values(|c: EConstraint| view_constraint(c))
}

pub struct EDatabase {
    pub schema: Vec<ETableSchema>,
    pub tables: Vec<Vec<ERow>>,
}

pub open spec fn view_table_schema(t: ETableSchema) -> TableSchema {
    TableSchema { columns: t.columns@, constraints: view_constraints(t.constraints@) }
}

pub open spec fn view_schema(s: Seq<ETableSchema>) -> Schema {
    s.map_values(|t: ETableSchema| view_table_schema(t))
}

pub open spec fn view_rows(rows: Seq<ERow>) -> Seq<Row> {
    rows.map_values(|r: ERow| view_row(r@))
}

pub open spec fn view_db(db: EDatabase) -> Database {
    Database {
        schema: view_schema(db.schema@),
        tables: db.tables@.map_values(|rel: Vec<ERow>| view_rows(rel@)),
    }
}

impl View for EDatabase {
    type V = Database;

    open spec fn view(&self) -> Database {
        view_db(*self)
    }
}

/// Every row satisfies the timestamp representation invariant of `exec::domain` (required by `exec_expr`).
pub open spec fn rows_ts_ok(rows: Seq<Row>) -> bool {
    forall|i: int| 0 <= i < rows.len() ==> row_ts_ok(#[trigger] rows[i])
}

pub open spec fn db_ts_ok(db: Database) -> bool {
    forall|t: int| 0 <= t < db.tables.len() ==> rows_ts_ok(#[trigger] db.tables[t])
}

/// A well-formed database meets the timestamp representation invariant: every value lies in its column's type.
pub proof fn lemma_db_wf_ts_ok(db: Database)
    requires db_wf(db),
    ensures db_ts_ok(db),
{
    assert forall|t: int| 0 <= t < db.tables.len() implies rows_ts_ok(#[trigger] db.tables[t]) by {
        assert forall|i: int| 0 <= i < db.tables[t].len() implies row_ts_ok(#[trigger] db.tables[t][i]) by {
            let r = db.tables[t][i];
            assert(row_in_table(r, db.schema[t]));
            assert forall|c: int| 0 <= c < r.len() implies val_ts_ok(#[trigger] r[c]) by {
                assert(value_in_column(r[c], db.schema[t].columns[c]));
            }
        }
    }
}

} // verus!
