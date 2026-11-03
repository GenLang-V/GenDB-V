//! Constant subexpressions through the Python parser and the host (`gendb_frontend::constants`): a literal-only
//! subexpression whose SQLSpec evaluation raises an SQL error refuses the statement (`constant_expression_error`, with
//! the SQLSTATE), one that leaves the executable interpreter's machine domain refuses it as
//! `constant_expression_capacity`, and constants with a value, parameter expressions and column expressions translate.

use gendb_frontend::ast::{self, Translation};
use gendb_frontend::constants::{CONSTANT_EXPRESSION_CAPACITY, CONSTANT_EXPRESSION_ERROR};
use gendb_frontend::params::Placeholder;
use gendb_frontend::parser::SqlParser;
use std::sync::atomic::{AtomicUsize, Ordering};

const DDL: &str = "CREATE TABLE t (x integer NOT NULL, n numeric(10,2), s text, c char(4), d date);\nCREATE TABLE e (z integer);\n";

/// Translate `sql` over [`DDL`] with the placeholders `params` (`(index, type)`); also checks that the returned document
/// text decodes to the returned translation.
fn translate(sql: &str, params: &[(u32, &str)]) -> Translation {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!("gendb-frontend-constants-{}-{}", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)));
    std::fs::create_dir_all(&dir).unwrap();
    let (schema, query) = (dir.join("schema.sql"), dir.join("query.sql"));
    std::fs::write(&schema, DDL).unwrap();
    std::fs::write(&query, sql).unwrap();
    let placeholders: Vec<Placeholder> = params.iter().map(|(index, ty)| Placeholder { index: *index, sql_type: ty.to_string() }).collect();
    let (text, translation) = SqlParser::from_environment().unwrap().translate(&schema, &query, "postgres", &placeholders).unwrap();
    std::fs::remove_dir_all(&dir).unwrap();
    assert_eq!(ast::decode(&text).unwrap(), translation, "{sql}: the document text is the translation");
    translation
}

/// The refusal `(reason, detail, sql)` of `sql`.
fn refused(sql: &str, params: &[(u32, &str)]) -> (String, String, String) {
    match translate(sql, params) {
        Translation::Refused(r) => (r.reason, r.detail, r.sql),
        Translation::Ok(_) => panic!("{sql}: translated, expected a refusal"),
    }
}

fn assert_raises(sql: &str, params: &[(u32, &str)], sqlstate: &str) {
    let (reason, detail, _) = refused(sql, params);
    assert_eq!(reason, CONSTANT_EXPRESSION_ERROR, "{sql}: {detail}");
    assert!(detail.starts_with(&format!("SQLSTATE {sqlstate} ")), "{sql}: {detail}");
}

fn assert_translates(sql: &str, params: &[(u32, &str)]) {
    if let Translation::Refused(r) = translate(sql, params) {
        panic!("{sql}: refused {r:?}");
    }
}

/// The PostgreSQL 18 probes where planning raises but SQLSpec alone would answer with rows (empty table, CASE branch or
/// COALESCE argument no row reaches, a literal error next to a parameter, an aggregate argument), and the other
/// erroring constants of the fragment.
#[test]
fn erroring_constants_are_refused() {
    assert_raises("SELECT z FROM e WHERE z = 1/0", &[], "22012");
    assert_raises("SELECT 1/0 FROM e", &[], "22012");
    assert_raises("SELECT z FROM e WHERE z = 1/0 AND false", &[], "22012");
    assert_raises("SELECT z FROM e WHERE z = 1/0 OR true", &[], "22012");
    assert_raises("SELECT COALESCE(x, 1/0) FROM t", &[], "22012");
    assert_raises("SELECT CASE WHEN x > 0 THEN x ELSE 1/0 END FROM t", &[], "22012");
    assert_raises("SELECT z FROM e WHERE z > $1 AND z = 1/0", &[(1, "integer")], "22012");
    assert_raises("SELECT SUM(1/0) FROM e", &[], "22012");
    assert_raises("SELECT x FROM t WHERE x < (SELECT MAX(z) / 0.0 FROM e) OR x IN (SELECT 1/0 FROM e)", &[], "22012");
    assert_raises("SELECT 1.5 / 0 FROM t", &[], "22012");
    assert_raises("SELECT 2147483647 + 1 FROM t", &[], "22003");
    assert_raises("SELECT x FROM t WHERE x > -(-2147483647 - 1)", &[], "22003");
    assert_raises("SELECT SUBSTRING('abc' FROM 1 FOR -1) FROM t", &[], "22011");
    assert_raises("SELECT 'a' LIKE 'a' ESCAPE 'xy' FROM t", &[], "22025");
    assert_raises("SELECT s FROM t WHERE s LIKE 'a' ESCAPE 'xy'", &[], "22025");
    assert_raises("SELECT x FROM t WHERE 'ab' LIKE 'a\\'", &[], "22025");
    assert_raises("SELECT DATE '2000-01-01' + INTERVAL '300000' YEAR FROM t", &[], "22008");
    assert_raises("SELECT x FROM t WHERE d < DATE '0001-01-01' - INTERVAL '1721427' DAY", &[], "22008");
    // Refused although PostgreSQL stops folding at the constant FALSE (documented; SQLSpec's AND is strict).
    assert_raises("SELECT x FROM t WHERE false AND x = 1/0", &[], "22012");
    assert_raises("SELECT CASE WHEN true THEN x ELSE 1/0 END FROM t", &[], "22012");
    // The refusal names the constant, rendered from the AST, and where it is.
    let (_, detail, sql) = refused("SELECT z FROM e WHERE z = (2 + 3) / (4 - 4)", &[]);
    assert_eq!(sql, "(2 + 3) / (4 - 4)", "{detail}");
    let (_, _, sql) = refused("SELECT s FROM t WHERE s LIKE 'a' ESCAPE 'xy'", &[]);
    assert_eq!(sql, "LIKE 'a' ESCAPE 'xy'");
}

/// A constant whose evaluation leaves `i128` has its own reason; out-of-range casts of literals stay the parser's
/// refusals.
#[test]
fn capacity_and_literal_refusals() {
    let (reason, detail, sql) = refused("SELECT 99999999999999999999999999999999999999 * 10 FROM t", &[]);
    assert_eq!(reason, CONSTANT_EXPRESSION_CAPACITY, "{detail}");
    assert_eq!(sql, "99999999999999999999999999999999999999 * CAST(10 AS numeric)");
    let (reason, _, _) = refused("SELECT 0.5 / 1000000000000000000000 FROM t", &[]);
    assert_eq!(reason, CONSTANT_EXPRESSION_CAPACITY);
    assert_eq!(refused("SELECT CAST('3000000000' AS integer) FROM t", &[]).0, "invalid_literal");
    assert_eq!(refused("SELECT CAST(3000000000 AS integer) FROM t", &[]).0, "unsupported_cast");
}

/// Constants with a value (also lazily evaluated CASE / COALESCE that PostgreSQL folds without error), parameter
/// expressions (plan-dependent in PostgreSQL, left to SQLSpec's row-by-row meaning) and column expressions translate.
#[test]
fn constants_with_values_parameters_and_columns_translate() {
    assert_translates("SELECT x FROM t WHERE d <= DATE '1998-12-01' - INTERVAL '90' DAY", &[]);
    assert_translates("SELECT x FROM t WHERE d >= DATE '1994-01-01' AND d < DATE '1994-01-01' + INTERVAL '1' YEAR", &[]);
    assert_translates("SELECT x FROM t WHERE n BETWEEN 0.06 - 0.01 AND 0.06 + 0.01", &[]);
    assert_translates("SELECT 100.00 * 7 / 3, 2147483647 + 0, -(-2147483647), EXTRACT(YEAR FROM DATE '1995-03-15') FROM t", &[]);
    assert_translates("SELECT COALESCE(1, 1/0), CASE WHEN 1 > 0 THEN 1 ELSE 1/0 END, NULLIF(1, 2) FROM t", &[]);
    assert_translates("SELECT SUBSTRING('abcdef' FROM -1 FOR 3), 'ab' LIKE 'a%', 'a%' LIKE 'a\\%' FROM t", &[]);
    assert_translates("SELECT x FROM t WHERE x > 10 / $1", &[(1, "integer")]);
    assert_translates("SELECT x FROM t WHERE d < $1 + INTERVAL '1' YEAR", &[(1, "date")]);
    assert_translates("SELECT x FROM t WHERE x > 100 AND x > 10 / $1 AND n < $2 / 0", &[(1, "integer"), (2, "numeric(10,2)")]);
    assert_translates("SELECT 1 / x, x / 0, SUBSTRING(s FROM 1 FOR -1), c LIKE 'ab%' FROM t", &[]);
    assert_translates("SELECT s FROM t WHERE s LIKE 'a%' AND s NOT LIKE '%b\\%'", &[]);
}
