//! The statement key an admitted package is looked up by, the parameter declaration recorded in its claim, and the
//! exact conversion of request argument texts into ABI arguments. Admission and serving compute them the same way,
//! so a new binding of an admitted template finds the same package without synthesis.

use crate::abi::StatementArgument;
use gendb_artifacts::verus::{
    VerusFreeParamV1, VerusParamBindingV1, VerusParamDeclV1, VerusStatementKeyV1, VerusStatementKeyV2, statement_meaning,
};
use gendb_frontend::params::{Binding, Instance, ParamDecl, ParamDomain, ParamType, ParamValue};
use gendb_frontend::translator::{
    EmitError, EmitOptions, emit_column_schema_module, emit_constraints_module, emit_instance_module, emit_statement_module,
};
use std::fmt;

/// Why a statement key or argument list could not be formed.
#[derive(Debug)]
pub enum StatementError {
    /// The AST document does not name the frontend that produced it.
    MissingFrontendIdentity,
    /// The emitter refused the instance.
    Emit(EmitError),
    /// The AST's output names and PostgreSQL types differ in length.
    OutputShape,
    /// A date argument's month or day does not fit the ABI's `i32` (never produced by exact parsing).
    DateArgument(ParamValue),
}

impl fmt::Display for StatementError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingFrontendIdentity => f.write_str("AST document without frontend identity"),
            Self::Emit(error) => write!(f, "{error}"),
            Self::OutputShape => f.write_str("AST output names and types differ in length"),
            Self::DateArgument(value) => write!(f, "date argument {value:?} does not fit the ABI"),
        }
    }
}

impl std::error::Error for StatementError {}

/// The statement key of an instance (fixed parameters substituted by `gendb_frontend::params::instantiate`): the
/// emitted meaning (`emit_instance_module` for candidates, without its `//!` SQL header, byte-equal to the checked
/// `query.rs` minus that header), the free-parameter declaration and the output columns. A template with another
/// fixed value or another free domain is another statement.
pub fn statement_key(instance: &Instance) -> Result<VerusStatementKeyV1, StatementError> {
    let query = emit_instance_module(instance, &EmitOptions::candidate()).map_err(StatementError::Emit)?;
    Ok(VerusStatementKeyV1 {
        frontend_identity: frontend_identity(instance)?,
        meaning: statement_meaning(&query),
        free: free_parameters(instance),
        output: output_columns(instance)?,
    })
}

/// The statement key of an instance in the storage-aware layout (entry v4): the generated column schema `schema.rs` and
/// the generated `query.rs` (without its `//!` SQL header) as two fields, the free-parameter declaration, the output
/// columns and, when the schema declares integrity constraints, the generated `gendb_constraints.rs`. The texts are the
/// ones the query crate is assembled with (`emit_column_schema_module`, `emit_statement_module`,
/// `emit_constraints_module` with candidate options), so admission and serving compute the same key; a statement over
/// another schema or another declaration list is another key even when its `query.rs` text is equal. Without
/// declared constraints the key is the one computed before constraints could be declared.
pub fn statement_key_v4(instance: &Instance) -> Result<VerusStatementKeyV2, StatementError> {
    let options = EmitOptions::candidate();
    let tables = &instance.doc.tables;
    let schema = emit_column_schema_module(tables, &options).map_err(StatementError::Emit)?;
    let query = emit_statement_module(instance, &options).map_err(StatementError::Emit)?;
    Ok(VerusStatementKeyV2 {
        frontend_identity: frontend_identity(instance)?,
        schema,
        statement: statement_meaning(&query),
        free: free_parameters(instance),
        output: output_columns(instance)?,
        constraints: emit_constraints_module(tables, &options).map_err(StatementError::Emit)?,
    })
}

fn frontend_identity(instance: &Instance) -> Result<String, StatementError> {
    instance
        .doc
        .frontend
        .get("identity")
        .and_then(|identity| identity.as_str())
        .map(str::to_string)
        .ok_or(StatementError::MissingFrontendIdentity)
}

/// The output columns `(name, PostgreSQL type)` in order.
fn output_columns(instance: &Instance) -> Result<Vec<(String, String)>, StatementError> {
    let output = &instance.doc.output;
    if output.names.len() != output.pg_types.len() {
        return Err(StatementError::OutputShape);
    }
    Ok(output.names.iter().cloned().zip(output.pg_types.iter().cloned()).collect())
}

/// Canonical texts of the free parameters of `instance`, in slot order (a text parameter has no bounds).
pub fn free_parameters(instance: &Instance) -> Vec<VerusFreeParamV1> {
    instance
        .free
        .iter()
        .map(|free| {
            let (min, max) = domain_texts(free.ty, &free.domain);
            VerusFreeParamV1 { index: free.index, slot: free.slot, sql_type: free.ty.sql_name(), min, max }
        })
        .collect()
}

/// The canonical bound texts of a free domain (none for text).
fn domain_texts(ty: ParamType, domain: &ParamDomain) -> (Option<String>, Option<String>) {
    match domain {
        ParamDomain::Range { min, max } => (Some(ty.text(min)), Some(ty.text(max))),
        ParamDomain::AllText => (None, None),
    }
}

/// The request's full parameter declaration (fixed values and free domains) as canonical texts, for the claim record.
pub fn parameter_declaration(declarations: &[ParamDecl]) -> Vec<VerusParamDeclV1> {
    declarations
        .iter()
        .map(|declaration| VerusParamDeclV1 {
            index: declaration.index,
            sql_type: declaration.ty.sql_name(),
            binding: match &declaration.binding {
                Binding::Fixed(value) => VerusParamBindingV1::Fixed { value: declaration.ty.text(value) },
                Binding::Free { domain } => {
                    let (min, max) = domain_texts(declaration.ty, domain);
                    VerusParamBindingV1::Free { min, max }
                }
            },
        })
        .collect()
}

/// ABI arguments of exactly parsed parameter values (`gendb_frontend::params::parse_arguments`, slot order). No
/// domain check: the verified entry refuses values outside the declared domain (`ParamRefused`).
pub fn statement_arguments(values: &[ParamValue]) -> Result<Vec<StatementArgument>, StatementError> {
    values
        .iter()
        .map(|value| {
            Ok(match value {
                ParamValue::Int(int) => StatementArgument::Int(*int),
                ParamValue::Num(coefficient) => StatementArgument::Num(*coefficient),
                ParamValue::Date { y, m, d } => {
                    let field = |x: u32| i32::try_from(x).map_err(|_| StatementError::DateArgument(value.clone()));
                    StatementArgument::Date { y: *y, m: field(*m)?, d: field(*d)? }
                }
                ParamValue::Text(text) => StatementArgument::Text(text.clone()),
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use gendb_frontend::ast::{Translation, decode};

    /// `SELECT c FROM t` resolved against a schema of `tables` (a JSON list).
    fn instance(tables: &str) -> Instance {
        let doc = format!(
            r#"{{"format": "gendb-sql-ast-v1", "status": "ok", "frontend": {{"identity": "unit"}}, "sql": "SELECT c FROM t",
            "schema": {{"tables": {tables}}},
            "output": {{"names": ["c"], "columns": [{{"type": {{"kind": "int4"}}, "nullable": false, "dscale": null}}], "pg_types": ["int4"]}},
            "root": 1, "nodes": [
              {{"id": 0, "tag": "Table", "table": 0, "columns": [{{"type": {{"kind": "int4"}}, "nullable": false, "dscale": null}}]}},
              {{"id": 1, "tag": "OrderedQuery", "body": 0, "keys": [], "limit": null, "offset": 0}}]}}"#
        );
        let Translation::Ok(doc) = decode(&doc).unwrap() else { panic!("refused") };
        Instance::concrete(&doc).unwrap()
    }

    /// The saved S5 Q6 template and concrete Q4 (`output/verified-storage/runs/s5-q6t-q4`, admitted in the verified storage
    /// library) keep their v1 and v4 statement keys: the optional bounds serialize as before, so a new request finds
    /// their admitted packages.
    #[test]
    fn saved_statement_keys_keep_their_identity() {
        let run = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../output/verified-storage/runs/s5-q6t-q4/queries");
        for query in ["query-0000", "query-0001"] {
            let dir = run.join(query).join("verus-preflight");
            let read = |name: &str| std::fs::read_to_string(dir.join(name)).unwrap_or_else(|e| panic!("{query}/{name}: {e}"));
            let Translation::Ok(doc) = decode(&read("ast.json")).unwrap() else { panic!("{query}: refused") };
            let requests: Vec<gendb_frontend::params::ParamRequest> = serde_json::from_str(&read("parameters.json")).unwrap();
            let instance = gendb_frontend::params::instantiate(&doc, &gendb_frontend::params::declare(&doc, &requests).unwrap()).unwrap();
            let record: serde_json::Value = serde_json::from_str(&read("statement.json")).unwrap();
            assert_eq!(statement_key(&instance).unwrap().identity().unwrap().to_hex(), record["statement_key"], "{query}: key v1");
            assert_eq!(statement_key_v4(&instance).unwrap().identity().unwrap().to_hex(), record["statement_key_v4"], "{query}: key v2");
        }
    }

    /// The same statement over two schemas that differ only in a table it does not read: the split `query.rs` texts
    /// are equal, so the v4 key must take the schema from `schema.rs`; the keys differ, and equal inputs give equal keys.
    #[test]
    fn statement_key_v4_separates_schemas_with_equal_statement_text() {
        let t = r#"{"name": "t", "columns": [{"name": "c", "type": {"kind": "int4"}, "nullable": false}]}"#;
        let u = r#"{"name": "u", "columns": [{"name": "d", "type": {"kind": "int8"}, "nullable": false}]}"#;
        let (one, two) = (instance(&format!("[{t}]")), instance(&format!("[{t}, {u}]")));
        let (key_one, key_two) = (statement_key_v4(&one).unwrap(), statement_key_v4(&two).unwrap());
        assert_eq!(key_one.statement, key_two.statement, "the statement text alone cannot tell the schemas apart");
        assert_ne!(key_one.schema, key_two.schema);
        assert_ne!(key_one.identity().unwrap(), key_two.identity().unwrap());
        assert_eq!(key_one.identity().unwrap(), statement_key_v4(&instance(&format!("[{t}]"))).unwrap().identity().unwrap());
        // The saved v1 key keeps its own meaning (schema inline) and kind: never the v2 identity.
        let v1 = statement_key(&one).unwrap();
        assert!(v1.meaning.contains("pub open spec fn schema_spec()") && !key_one.statement.contains("fn schema_spec"));
        assert_ne!(v1.identity().unwrap(), key_one.identity().unwrap());
    }

    /// Declared constraints change only the key's `constraints` field: the same statement unconstrained, with one
    /// declaration and with another declaration list has three distinct keys over byte-equal `schema.rs` and
    /// `query.rs` texts; equal declarations give equal keys; the unconstrained key serializes without the field.
    #[test]
    fn declared_constraints_separate_statement_keys() {
        let key = |constraints: &str| -> VerusStatementKeyV2 {
            let t = format!(r#"{{"name": "t", "columns": [{{"name": "c", "type": {{"kind": "int4"}}, "nullable": false}}], "constraints": {constraints}}}"#);
            statement_key_v4(&instance(&format!("[{t}]"))).unwrap()
        };
        let primary = r#"{"kind": "key", "name": null, "primary": true, "columns": [0], "nulls_distinct": true, "deferrable": false, "initially_deferred": false}"#;
        let unique = r#"{"kind": "key", "name": null, "primary": false, "columns": [0], "nulls_distinct": true, "deferrable": false, "initially_deferred": false}"#;
        let (none, pk, uq) = (key("[]"), key(&format!("[{primary}]")), key(&format!("[{unique}]")));
        assert_eq!((&none.schema, &none.statement), (&pk.schema, &pk.statement));
        assert_eq!((&pk.schema, &pk.statement), (&uq.schema, &uq.statement));
        assert!(none.constraints.is_none() && none.constraints_digest().is_none());
        assert!(pk.constraints.as_deref().is_some_and(|m| m.contains("Constraint::Key { cols: seq![0nat], primary: true")));
        let ids = [&none, &pk, &uq].map(|k| k.identity().unwrap());
        assert!(ids[0] != ids[1] && ids[1] != ids[2] && ids[0] != ids[2], "{ids:?}");
        assert_eq!(key(&format!("[{primary}]")).identity().unwrap(), ids[1]);
        assert_ne!(pk.constraints_digest(), uq.constraints_digest());
        assert!(serde_json::to_value(&none).unwrap().get("constraints").is_none(), "an unconstrained key keeps its JSON");
        // The unconstrained key equals the one computed from the same document without a constraints section.
        let t = r#"{"name": "t", "columns": [{"name": "c", "type": {"kind": "int4"}, "nullable": false}]}"#;
        assert_eq!(statement_key_v4(&instance(&format!("[{t}]"))).unwrap().identity().unwrap(), ids[0]);
    }
}
