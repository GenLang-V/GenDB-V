//! The request's declared integrity constraints (`integrity_constraints`): PostgreSQL table-constraint clauses that the
//! user asserts hold on the full source tables. Absent: no declared constraint, and the DDL, the AST document, every
//! statement key and every generated file are the ones computed before constraints could be declared.
//!
//! Representation (no second model). The request holds `{"trust", "declarations": [{"table", "sql"}]}`; the dataset
//! DDL appends `ALTER TABLE <table> ADD <sql>;` per declaration, in request order ([`super::dataset_ddl`]); the frontend
//! binds each clause to one constraint of the AST document (`gendb_frontend::ast::ConstraintDef`), whose meaning is
//! SQLSpec's `Constraint`. Declaration order is part of the identity: a key must precede a foreign key that references
//! it, as in PostgreSQL.
//!
//! Trust. `user_declared` is the only mode: the declarations are the user's assumptions about the data, never checked
//! against it (no scan, no hash) and never validated by PostgreSQL. GenDB checks their form only: the structural rules
//! of [`IntegrityConstraints::validate`] before translation, the frontend's PostgreSQL DDL rules, and after translation
//! one constraint per declaration and the CHECK subset ([`IntegrityConstraints::check_translation`]).
//!
//! CHECK subset. SQLSpec's CHECK meaning (`spec::constraints::check_row_holds`: the predicate is not `False` and raises
//! no error) evaluates both operands of AND/OR (`spec::eval::eval_pred`), while PostgreSQL may skip one; and SQLSpec
//! orders text by bytes (C collation), while a database may use another collation. A CHECK is therefore accepted only
//! when it is built from nodes that never raise on a well-typed row and never order text: `And`, `Or`, `Not`, `IsNull`,
//! `OfBool`, `Cmp` (any operator on boolean, integer, numeric and date/timestamp operands; only `=` and `<>` on text),
//! `Col`, `Lit` with its literal, and the widening casts `Int4ToInt8` and `IntToNumeric`. Without errors, strict and
//! short-circuit Kleene AND/OR agree, and "not False" is PostgreSQL's CHECK rule, so such a declaration means the same
//! in SQLSpec as in PostgreSQL; text equality is byte equality under every deterministic collation (nondeterministic
//! collations are outside SQLSpec's text semantics). Every other node is a named refusal: `check_may_raise` (`Arith`,
//! `Neg`, `Call`, `If`, `AddInterval`, the cast `DateToTimestamp`), `check_text_order`, and `check_subquery`.

use super::statement::dataset_ddl;
use gendb_frontend::ast::{schema as ast_schema, Annotation, ColType, ConstraintDef, FieldValue, Node, PgType, TableDef};
use gendb_storage::import::DatasetSpec;
use serde::{Deserialize, Serialize};

/// The only trust mode: the user declares the constraints; nothing checks them against the data.
pub const USER_DECLARED: &str = "user_declared";

/// The request field `integrity_constraints`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IntegrityConstraints {
    /// [`USER_DECLARED`].
    pub trust: String,
    /// In request order (part of the identity).
    pub declarations: Vec<ConstraintDeclaration>,
}

/// One declared table constraint: `sql` is the clause PostgreSQL accepts after `ALTER TABLE <table> ADD`
/// (`PRIMARY KEY (...)`, `UNIQUE [NULLS NOT DISTINCT] (...)`, `FOREIGN KEY (...) REFERENCES t (...) [MATCH FULL]`, or
/// `CONSTRAINT <name> CHECK (...)`; `CONSTRAINT <name>` is optional metadata for the others).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ConstraintDeclaration {
    /// A dataset table, by its declared name.
    pub table: String,
    pub sql: String,
}

impl IntegrityConstraints {
    /// The structural checks before any translation: the trust mode, a non-empty list, each declaration on a dataset
    /// table that the DDL keeps (`dataset_ddl` leaves out a table with a column type outside SQLSpec's fragment), and
    /// one clause per declaration (no `;`). Errors are `integrity_constraints_trust_unsupported: ...` or
    /// `integrity_constraints_invalid: ...`.
    pub fn validate(&self, dataset: &DatasetSpec) -> Result<(), String> {
        if self.trust != USER_DECLARED {
            return Err(format!(
                "integrity_constraints_trust_unsupported: trust {:?}; the only mode is {USER_DECLARED:?} (the declarations are \
                 the user's assumptions; a checked mode would need a full-data scan)",
                self.trust
            ));
        }
        let invalid = |what: String| Err(format!("integrity_constraints_invalid: {what}"));
        if self.declarations.is_empty() {
            return invalid("an empty declaration list (omit integrity_constraints to declare none)".into());
        }
        let (_, omitted) = dataset_ddl(dataset, None);
        for (i, declaration) in self.declarations.iter().enumerate() {
            if !dataset.tables.iter().any(|t| t.name == declaration.table) {
                return invalid(format!("declarations[{i}]: table {:?} is not a dataset table", declaration.table));
            }
            if omitted.iter().any(|o| o["table"] == declaration.table.as_str()) {
                return invalid(format!(
                    "declarations[{i}]: table {:?} is left out of the DDL (a column type outside SQLSpec's fragment)",
                    declaration.table
                ));
            }
            if declaration.sql.trim().is_empty() || declaration.sql.contains(';') {
                return invalid(format!("declarations[{i}]: sql must be one table-constraint clause, non-empty and without `;`"));
            }
        }
        Ok(())
    }

    /// After translation over the DDL with these declarations (whose CREATE TABLEs declare no constraint): each table
    /// of the document has exactly the constraints declared on it, one per declaration, and every CHECK is in the
    /// supported subset (module doc). Errors are `integrity_constraints_invalid: ...`, `check_may_raise: ...`,
    /// `check_text_order: ...` or `check_subquery: ...`, naming the declaration.
    pub fn check_translation(&self, tables: &[TableDef]) -> Result<(), String> {
        for table in tables {
            let declared: Vec<(usize, &ConstraintDeclaration)> =
                self.declarations.iter().enumerate().filter(|(_, d)| d.table == table.name).collect();
            if declared.len() != table.constraints.len() {
                return Err(format!(
                    "integrity_constraints_invalid: table {:?} has {} declarations but its DDL translates to {} constraints \
                     (one table constraint per declaration)",
                    table.name,
                    declared.len(),
                    table.constraints.len()
                ));
            }
            for ((i, declaration), constraint) in declared.into_iter().zip(&table.constraints) {
                if let ConstraintDef::Check { nodes, .. } = constraint
                    && let Some(refusal) = check_subset_refusal(nodes)
                {
                    return Err(format!("{refusal} in declarations[{i}] ({})", declaration.sql));
                }
            }
        }
        Ok(())
    }
}

/// Why the CHECK arena `nodes` (exactly the CHECK's predicate tree) is outside the supported subset, or `None`.
fn check_subset_refusal(nodes: &[Node]) -> Option<String> {
    for node in nodes {
        let enum_field = |name: &str| match node.field(name) {
            Some(FieldValue::Enum(value)) => value.as_str(),
            _ => "",
        };
        match node.tag.as_str() {
            "And" | "Or" | "Not" | "IsNull" | "OfBool" | "Col" | "Lit" => {}
            "Cmp" => {
                let ordering = matches!(enum_field("op"), "Lt" | "Le" | "Gt" | "Ge");
                let text = node.child("a").is_some_and(|a| is_text(&nodes[a]));
                if ordering && text {
                    let op = enum_field("op");
                    return Some(format!("check_text_order: a {op} comparison of text depends on the collation (only = and <> on text)"));
                }
            }
            "Cast" if matches!(enum_field("cast"), "Int4ToInt8" | "IntToNumeric") => {}
            "Cast" => return Some(format!("check_may_raise: Cast {}", enum_field("cast"))),
            "Exists" | "AnyCmp" | "Subquery" => return Some(format!("check_subquery: {}", node.tag)),
            tag if ast_schema().kinds[tag].sort == "literal" => {}
            tag => return Some(format!("check_may_raise: {tag}")),
        }
    }
    None
}

/// The expression node has a text-family type (text, varchar, char).
fn is_text(node: &Node) -> bool {
    matches!(
        &node.annotation,
        Some(Annotation::Type(ColType { ty: PgType::Text | PgType::Varchar { .. } | PgType::Bpchar { .. }, .. }))
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::admission::{Statement, prepare_statement};
    use gendb_artifacts::{ColType as DataType, ColumnSpec};
    use gendb_frontend::ast::{ColumnDef, ConstraintTiming};
    use gendb_frontend::parser::SqlParser;
    use gendb_storage::import::{DataFormat, TableSpec};
    use std::path::PathBuf;

    fn constraints(declarations: &[(&str, &str)]) -> IntegrityConstraints {
        IntegrityConstraints {
            trust: USER_DECLARED.into(),
            declarations: declarations.iter().map(|(table, sql)| ConstraintDeclaration { table: (*table).into(), sql: (*sql).into() }).collect(),
        }
    }

    /// `t` (one column of every supported type family), `p` (a key referenced from `t`, declared after it), and `blob`
    /// (left out of the DDL). Only the DDL is used: no data is read.
    fn dataset() -> DatasetSpec {
        let table = |name: &str, fields: Vec<(&str, DataType)>| TableSpec {
            name: name.into(),
            fields: fields.into_iter().map(|(n, ty)| ColumnSpec { name: n.into(), ty, nullable: n == "n" }).collect(),
            locations: vec![PathBuf::from(format!("{name}.parquet"))],
            format: DataFormat::Parquet,
        };
        let money = DataType::Decimal { p: 15, s: 2 };
        DatasetSpec {
            tables: vec![
                table("t", vec![("a", DataType::I32), ("b", DataType::I64), ("m", money), ("d", DataType::Date32), ("e", DataType::Date32), ("s", DataType::Utf8), ("f", DataType::Bool), ("n", DataType::I64)]),
                table("p", vec![("k", DataType::I64)]),
                table("blob", vec![("x", DataType::Binary)]),
            ],
        }
    }

    fn scratch(name: &str) -> PathBuf {
        let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
        std::env::temp_dir().join(format!("gendb-integrity-constraints-{}", std::process::id())).join(format!("{name}-{nanos}"))
    }

    fn prepare(parser: &SqlParser, declared: Option<&IntegrityConstraints>, name: &str) -> Result<Statement, String> {
        prepare_statement(parser, &dataset(), declared, "SELECT a, b FROM t", &[], &[], &[], &scratch(name)).map_err(|r| r.error.to_string())
    }

    #[test]
    fn structural_refusals_precede_translation() {
        // prepare_statement, a public entry, applies the same rules itself before any translation or evidence write.
        let parser = SqlParser::from_environment().unwrap();
        let checked = IntegrityConstraints { trust: "checked".into(), ..constraints(&[("t", "PRIMARY KEY (a)")]) };
        let name = "untrusted-mode";
        let refused = prepare(&parser, Some(&checked), name).err().expect("refused");
        assert!(refused.contains("integrity_constraints: integrity_constraints_trust_unsupported:"), "{refused}");
        assert!(prepare(&parser, Some(&constraints(&[("u", "PRIMARY KEY (a)")])), name).err().expect("refused").contains("not a dataset table"));
        let error = |c: IntegrityConstraints| c.validate(&dataset()).unwrap_err();
        assert!(constraints(&[("t", "PRIMARY KEY (a)")]).validate(&dataset()).is_ok());
        assert!(error(IntegrityConstraints { trust: "checked".into(), ..constraints(&[("t", "PRIMARY KEY (a)")]) }).starts_with("integrity_constraints_trust_unsupported:"));
        assert!(error(constraints(&[])).contains("empty declaration list"));
        assert!(error(constraints(&[("u", "PRIMARY KEY (a)")])).contains("not a dataset table"));
        assert!(error(constraints(&[("blob", "PRIMARY KEY (x)")])).contains("left out of the DDL"));
        assert!(error(constraints(&[("t", "PRIMARY KEY (a); DROP TABLE t")])).contains("without `;`"));
        assert!(error(constraints(&[("t", " ")])).starts_with("integrity_constraints_invalid:"));
    }

    /// The DDL without declarations is unchanged; with them it is the same CREATE TABLEs followed by one ALTER TABLE
    /// line per declaration, in request order.
    #[test]
    fn ddl_appends_one_alter_line_per_declaration() {
        let (plain, omitted) = dataset_ddl(&dataset(), None);
        assert!(plain.starts_with("CREATE TABLE t (\n    a integer NOT NULL,\n") && !plain.contains("ALTER") && omitted.len() == 1, "{plain}");
        let declared = constraints(&[("p", "PRIMARY KEY (k)"), ("t", "FOREIGN KEY (b) REFERENCES p (k)")]);
        let (ddl, _) = dataset_ddl(&dataset(), Some(&declared));
        assert_eq!(ddl, format!("{plain}ALTER TABLE p ADD PRIMARY KEY (k);\nALTER TABLE t ADD FOREIGN KEY (b) REFERENCES p (k);\n"));
    }

    /// The same statement unconstrained, with declarations and with another list: equal column schema and statement
    /// texts; the v4 keys differ only by the constraints module; the records name the declarations.
    #[test]
    fn declarations_reach_the_document_and_separate_the_statement_key() {
        let parser = SqlParser::from_environment().unwrap();
        let declared = constraints(&[("p", "PRIMARY KEY (k)"), ("t", "UNIQUE (a, b)"), ("t", "FOREIGN KEY (b) REFERENCES p (k)")]);
        let other = constraints(&[("p", "PRIMARY KEY (k)"), ("t", "FOREIGN KEY (b) REFERENCES p (k)")]);
        let plain = prepare(&parser, None, "plain").unwrap();
        let constrained = prepare(&parser, Some(&declared), "constrained").unwrap();
        let fewer = prepare(&parser, Some(&other), "fewer").unwrap();
        assert!(plain.template.tables.iter().all(|t| t.constraints.is_empty()) && plain.key_v4.constraints.is_none());
        assert_eq!(constrained.template.tables.iter().map(|t| t.constraints.len()).collect::<Vec<_>>(), [2, 1], "blob is left out of the DDL");
        for statement in [&constrained, &fewer] {
            assert_eq!((&statement.key_v4.schema, &statement.key_v4.statement), (&plain.key_v4.schema, &plain.key_v4.statement));
        }
        let ids = [&plain, &constrained, &fewer].map(|s| s.key_v4_id.clone());
        assert!(ids[0] != ids[1] && ids[1] != ids[2] && ids[0] != ids[2]);
        assert_ne!(plain.key_id, constrained.key_id, "the v1 key's inline schema carries the constraints too");
        assert!(constrained.schema_ddl.ends_with("ALTER TABLE t ADD FOREIGN KEY (b) REFERENCES p (k);\n"));
        let record: serde_json::Value = serde_json::from_slice(&std::fs::read(constrained.directory.join("statement.json")).unwrap()).unwrap();
        assert_eq!(record["integrity_constraints"]["constraints_digest"], constrained.key_v4.constraints_digest().unwrap().to_hex());
        assert_eq!(record["integrity_constraints"]["declarations"][2]["sql"], "FOREIGN KEY (b) REFERENCES p (k)");
        assert_eq!(plain.integrity_constraints_json(), "none");
    }

    /// Each allowed CHECK node is accepted; each refused kind has its name; a refusal names its declaration.
    #[test]
    fn check_subset_accepts_raise_free_collation_independent_checks() {
        let parser = SqlParser::from_environment().unwrap();
        let check = |sql: &str| prepare(&parser, Some(&constraints(&[("t", sql)])), "check").map(|s| s.template.tables[0].constraints.len());
        let accepted = "CONSTRAINT ok CHECK (a BETWEEN 1 AND 10 AND b <> 0 AND m >= 0.00 AND a <= m AND d <= e \
            AND s IN ('x', 'y') AND s <> 'z' AND NOT (n IS NULL) AND (f OR n > 0) AND CAST(a AS bigint) = b AND f = true)";
        let statement = prepare(&parser, Some(&constraints(&[("t", accepted)])), "accepted").unwrap();
        let ConstraintDef::Check { nodes, .. } = &statement.template.tables[0].constraints[0] else { panic!("a CHECK") };
        let tags: std::collections::BTreeSet<&str> = nodes.iter().map(|n| n.tag.as_str()).collect();
        for tag in ["And", "Or", "Not", "IsNull", "OfBool", "Cmp", "Col", "Lit", "Cast"] {
            assert!(tags.contains(tag), "{tag} not exercised: {tags:?}");
        }
        for (sql, refusal) in [
            ("CONSTRAINT k CHECK (a + 1 > 0)", "check_may_raise: Arith"),
            ("CONSTRAINT k CHECK (-a < 0)", "check_may_raise: Neg"),
            ("CONSTRAINT k CHECK (a / 2 >= 0)", "check_may_raise: Call"),
            ("CONSTRAINT k CHECK (s LIKE 'x%')", "check_may_raise: Call"),
            ("CONSTRAINT k CHECK (CASE WHEN f THEN a ELSE 0 END >= 0)", "check_may_raise: If"),
            ("CONSTRAINT k CHECK (d + INTERVAL '1 day' > e)", "check_may_raise"),
            ("CONSTRAINT k CHECK (CAST(d AS timestamp) <= CAST(e AS timestamp))", "check_may_raise: Cast DateToTimestamp"),
            ("CONSTRAINT k CHECK (s < 'm')", "check_text_order"),
            ("CONSTRAINT k CHECK (s >= 'a' OR f)", "check_text_order"),
        ] {
            let error = check(sql).unwrap_err();
            assert!(error.contains(refusal) && error.contains("declarations[0]"), "{sql}: {error}");
        }
        // Forms the frontend refuses, by its named reasons.
        assert!(check("CONSTRAINT k CHECK (a IN (SELECT 1))").unwrap_err().contains("check_subquery"));
        assert!(check("CHECK (a > 0)").unwrap_err().contains("parse_error"), "sqlglot 27 parses ADD CHECK only when named");
    }

    /// The translated document must hold exactly one constraint per declaration on each table.
    #[test]
    fn one_constraint_per_declaration() {
        let key = |primary| ConstraintDef::Key { name: None, primary, columns: vec![0], nulls_distinct: true, timing: ConstraintTiming { deferrable: false, initially_deferred: false } };
        let table = |constraints| TableDef { name: "p".into(), columns: vec![ColumnDef { name: "k".into(), ty: PgType::Int8, nullable: false }], constraints };
        let declared = constraints(&[("p", "PRIMARY KEY (k)")]);
        assert!(declared.check_translation(&[table(vec![key(true)])]).is_ok());
        for wrong in [vec![], vec![key(true), key(false)]] {
            assert!(declared.check_translation(&[table(wrong)]).unwrap_err().starts_with("integrity_constraints_invalid: table \"p\" has 1 declarations"));
        }
    }
}
