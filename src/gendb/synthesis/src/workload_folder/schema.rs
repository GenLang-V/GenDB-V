//! `schema.sql` of a workload folder: the tables (column names, types and NOT NULL) and the declared keys and named
//! CHECKs, read into the dataset's table shapes and the ordered `integrity_constraints` list of the request.
//!
//! Two forms give the same request:
//! - the canonical form, the DDL GenDB writes from a request (`admission::statement::dataset_ddl`): `CREATE TABLE`
//!   statements with columns only, then one `ALTER TABLE t ADD <clause>;` per key or CHECK;
//! - keys and CHECKs inside `CREATE TABLE`: column constraints (`PRIMARY KEY`, `UNIQUE`, `REFERENCES u (c)`,
//!   `CONSTRAINT n CHECK (...)`, each optionally named) and table constraints (`PRIMARY KEY (...)`, `UNIQUE (...)`,
//!   `FOREIGN KEY (...) REFERENCES u (...)`, `CONSTRAINT n CHECK (...)`), each turned into the clause that
//!   `ALTER TABLE t ADD` takes.
//!
//! The declaration list (its order is part of the request's identity) is: the keys written inside CREATE TABLE (tables
//! in file order, each in written order), then the foreign keys written there, then the CHECKs written there, then
//! the ALTER clauses in file order. So in the inline form every key precedes the foreign keys that reference it, as the
//! request requires, and the ALTER form keeps the user's order. Clause texts are kept as written, with whitespace
//! outside quoted literals collapsed to one space; a column constraint becomes `PRIMARY KEY (c)`, `UNIQUE (c)`,
//! `FOREIGN KEY (c) REFERENCES u (...)` or `CONSTRAINT n CHECK (...)`.
//!
//! Table order is table id (the proofs name tables by id). Unquoted identifiers fold to lower case, as in PostgreSQL.
//! Column types: `integer`/`int`/`int4` (I32), `bigint`/`int8` (I64), `numeric(p,s)`/`decimal(p,s)` with 1 <= p <= 38
//! and 0 <= s <= p (Decimal), `date` (Date32), `text` (Utf8), `boolean`/`bool` (Bool). Refused by name, with the fix:
//! `varchar(n)`/`char(n)` (no stored type: write `text`), `numeric` without (p,s), any other type, `DEFAULT`, an
//! unnamed CHECK, quoted identifiers, a CREATE TABLE after an ALTER TABLE, an ALTER of an undeclared table, and any
//! other statement. GenDB does not interpret the clauses themselves: the frontend translates them with every query
//! (`WorkloadFolder::check_queries`), so an unsupported clause or a CHECK outside the supported subset is refused
//! there, before any data work.

use super::FolderError;
use gendb_artifacts::{ColType, ColumnSpec};
use gendb_storage::import::{DataFormat, DatasetSpec, TableSpec};
use gendb_verification::admission::IntegrityConstraints;
use gendb_verification::admission::integrity_constraints::ConstraintDeclaration;
use std::collections::BTreeMap;
use std::path::PathBuf;

/// The `trust` of every declaration list a folder gives (the user asserts the constraints; GenDB never checks them).
const USER_DECLARED: &str = "user_declared";

/// The tables and declared constraints of a `schema.sql`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Schema {
    /// Tables in file order (the position is the table id).
    pub tables: Vec<TableShape>,
    /// The declared keys and CHECKs in the order above; `None` when the file declares none.
    pub constraints: Option<IntegrityConstraints>,
}

/// One table: its name and its columns in order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TableShape {
    pub name: String,
    pub fields: Vec<ColumnSpec>,
}

impl Schema {
    /// The request's dataset: every table with its source files (`locations[table]`, empty when absent) in Parquet.
    pub fn dataset(&self, locations: &BTreeMap<String, Vec<PathBuf>>) -> DatasetSpec {
        let tables = self
            .tables
            .iter()
            .map(|t| TableSpec { name: t.name.clone(), fields: t.fields.clone(), locations: locations.get(&t.name).cloned().unwrap_or_default(), format: DataFormat::Parquet })
            .collect();
        DatasetSpec { tables }
    }
}

/// The kind of a declared constraint, which decides its place in the inline form's order.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Key,
    ForeignKey,
    Check,
}

/// Read the text of a `schema.sql`.
pub fn parse(text: &str) -> Result<Schema, FolderError> {
    let mut tables: Vec<TableShape> = vec![];
    let mut inline: Vec<(Kind, ConstraintDeclaration)> = vec![];
    let mut altered: Vec<ConstraintDeclaration> = vec![];
    for statement in split_top(&strip_comments(text), ';').iter().map(|s| collapse(s)).filter(|s| !s.is_empty()) {
        if let Some(rest) = strip_keywords(&statement, &["CREATE", "TABLE"]) {
            if !altered.is_empty() {
                return Err(syntax(format!("CREATE TABLE {} comes after an ALTER TABLE: write every CREATE TABLE first", head(rest))));
            }
            let (name, body) = rest.split_once('(').ok_or_else(|| syntax(format!("CREATE TABLE {}: no column list", head(rest))))?;
            let name = identifier(name.trim(), "table name")?;
            let body = body.trim_end().strip_suffix(')').ok_or_else(|| syntax(format!("CREATE TABLE {name}: the column list does not end with `)`")))?;
            if tables.iter().any(|t| t.name == name) {
                return Err(syntax(format!("table {name} is declared twice")));
            }
            let (fields, constraints) = table_body(&name, body)?;
            inline.extend(constraints.into_iter().map(|(kind, sql)| (kind, ConstraintDeclaration { table: name.clone(), sql })));
            tables.push(TableShape { name, fields });
        } else if let Some(rest) = strip_keywords(&statement, &["ALTER", "TABLE"]) {
            let (table, clause) = split_keyword(rest, "ADD").ok_or_else(|| syntax(format!("ALTER TABLE {}: write ALTER TABLE <table> ADD <constraint>", head(rest))))?;
            let table = identifier(table.trim(), "table name")?;
            if !tables.iter().any(|t| t.name == table) {
                return Err(syntax(format!("ALTER TABLE {table}: no CREATE TABLE {table} before it")));
            }
            altered.push(ConstraintDeclaration { table, sql: clause.trim().to_string() });
        } else {
            return Err(syntax(format!("{}: schema.sql holds CREATE TABLE statements and ALTER TABLE <table> ADD <constraint> statements only", head(&statement))));
        }
    }
    if tables.is_empty() {
        return Err(syntax("schema.sql declares no table".into()));
    }
    let mut declarations: Vec<ConstraintDeclaration> = vec![];
    for kind in [Kind::Key, Kind::ForeignKey, Kind::Check] {
        declarations.extend(inline.iter().filter(|(k, _)| *k == kind).map(|(_, d)| d.clone()));
    }
    declarations.extend(altered);
    let constraints = (!declarations.is_empty()).then(|| IntegrityConstraints { trust: USER_DECLARED.into(), declarations });
    Ok(Schema { tables, constraints })
}

/// The columns and inline constraints of one `CREATE TABLE` body.
fn table_body(table: &str, body: &str) -> Result<(Vec<ColumnSpec>, Vec<(Kind, String)>), FolderError> {
    let (mut fields, mut constraints) = (vec![], vec![]);
    for item in split_top(body, ',').iter().map(|s| collapse(s)) {
        if item.is_empty() {
            return Err(syntax(format!("CREATE TABLE {table}: an empty column entry")));
        }
        if let Some(kind) = table_constraint_kind(&item) {
            if kind == Kind::Check && strip_keywords(&item, &["CONSTRAINT"]).is_none() {
                return Err(unnamed_check(table, &item));
            }
            constraints.push((kind, item));
            continue;
        }
        let (field, column_constraints) = column(table, &item)?;
        if fields.iter().any(|f: &ColumnSpec| f.name == field.name) {
            return Err(syntax(format!("CREATE TABLE {table}: column {} is declared twice", field.name)));
        }
        fields.push(field);
        constraints.extend(column_constraints);
    }
    if fields.is_empty() {
        return Err(syntax(format!("CREATE TABLE {table} declares no column")));
    }
    Ok((fields, constraints))
}

/// The kind of a table constraint entry (`[CONSTRAINT n] PRIMARY KEY | UNIQUE | FOREIGN KEY | CHECK ...`), or `None`
/// for a column definition.
fn table_constraint_kind(item: &str) -> Option<Kind> {
    let body = match strip_keywords(item, &["CONSTRAINT"]) {
        Some(rest) => rest.split_once(' ').map(|(_, after_name)| after_name)?,
        None => item,
    };
    if strip_keywords(body, &["PRIMARY", "KEY"]).is_some() || strip_keywords(body, &["UNIQUE"]).is_some() {
        Some(Kind::Key)
    } else if strip_keywords(body, &["FOREIGN", "KEY"]).is_some() {
        Some(Kind::ForeignKey)
    } else if strip_check(body).is_some() {
        Some(Kind::Check)
    } else {
        None
    }
}

/// One column definition `name type [NOT NULL | NULL | PRIMARY KEY | UNIQUE | REFERENCES u [(c)] | CONSTRAINT n ...
/// | CHECK (...)]...` and its column constraints as table clauses.
fn column(table: &str, item: &str) -> Result<(ColumnSpec, Vec<(Kind, String)>), FolderError> {
    let (name, rest) = item.split_once(' ').ok_or_else(|| syntax(format!("{table}: column {item:?} has no type")))?;
    let name = identifier(name, "column name")?;
    let at = format!("{table}.{name}");
    let (ty, mut rest) = column_type(&at, rest)?;
    let (mut nullable, mut constraints, mut pending_name) = (true, vec![], None::<String>);
    while !rest.is_empty() {
        let prefix = pending_name.as_ref().map(|n| format!("CONSTRAINT {n} ")).unwrap_or_default();
        if let Some(after) = strip_keywords(rest, &["NOT", "NULL"]) {
            nullable = false;
            rest = after;
        } else if let Some(after) = strip_keywords(rest, &["NULL"]) {
            rest = after;
        } else if let Some(after) = strip_keywords(rest, &["PRIMARY", "KEY"]) {
            constraints.push((Kind::Key, format!("{prefix}PRIMARY KEY ({name})")));
            (rest, pending_name) = (after, None);
        } else if let Some(after) = strip_keywords(rest, &["UNIQUE"]) {
            constraints.push((Kind::Key, format!("{prefix}UNIQUE ({name})")));
            (rest, pending_name) = (after, None);
        } else if let Some(after) = strip_keywords(rest, &["REFERENCES"]) {
            let (target, after) = after.split_at(after.find([' ', '(']).unwrap_or(after.len()));
            let target = identifier(target, "referenced table")?;
            let after = after.trim_start();
            let (columns, after) = if after.starts_with('(') { paren_group(&at, after)? } else { ("", after) };
            let columns = if columns.is_empty() { String::new() } else { format!(" {columns}") };
            constraints.push((Kind::ForeignKey, format!("{prefix}FOREIGN KEY ({name}) REFERENCES {target}{columns}")));
            (rest, pending_name) = (after, None);
        } else if let Some(after) = strip_keywords(rest, &["CONSTRAINT"]) {
            let (constraint, after) = after.split_once(' ').ok_or_else(|| syntax(format!("{at}: CONSTRAINT without a constraint")))?;
            pending_name = Some(identifier(constraint, "constraint name")?);
            rest = after;
        } else if let Some(after) = strip_check(rest) {
            let Some(constraint) = &pending_name else { return Err(unnamed_check(table, item)) };
            let (expression, after) = paren_group(&at, after)?;
            constraints.push((Kind::Check, format!("CONSTRAINT {constraint} CHECK {expression}")));
            (rest, pending_name) = (after, None);
        } else if strip_keywords(rest, &["DEFAULT"]).is_some() {
            return Err(FolderError::new("schema_unsupported", format!("{at}: DEFAULT is not supported (the data files give every value): remove it")));
        } else {
            return Err(syntax(format!("{at}: unexpected {:?} (a column takes NOT NULL, PRIMARY KEY, UNIQUE, REFERENCES and CONSTRAINT <name> CHECK (...))", head(rest))));
        }
        rest = rest.trim_start();
    }
    if pending_name.is_some() {
        return Err(syntax(format!("{at}: CONSTRAINT <name> must be followed by its constraint")));
    }
    Ok((ColumnSpec { name, ty, nullable }, constraints))
}

/// The column type at the start of `text` and the text after it.
fn column_type<'a>(at: &str, text: &'a str) -> Result<(ColType, &'a str), FolderError> {
    let word_end = text.find(|c: char| !c.is_ascii_alphanumeric() && c != '_').unwrap_or(text.len());
    let (word, after) = (text[..word_end].to_ascii_lowercase(), text[word_end..].trim_start());
    let simple = match word.as_str() {
        "integer" | "int" | "int4" => Some(ColType::I32),
        "bigint" | "int8" => Some(ColType::I64),
        "date" => Some(ColType::Date32),
        "text" => Some(ColType::Utf8),
        "boolean" | "bool" => Some(ColType::Bool),
        _ => None,
    };
    if let Some(ty) = simple {
        return Ok((ty, after));
    }
    let unsupported = |fix: &str| FolderError::new("schema_unsupported_type", format!("{at}: type {:?} {fix}", head(text)));
    match word.as_str() {
        "numeric" | "decimal" if after.starts_with('(') => {
            let (group, after) = paren_group(at, after)?;
            let inner = &group[1..group.len() - 1];
            let (p, s) = inner.split_once(',').ok_or_else(|| unsupported("needs a precision and a scale: numeric(p,s)"))?;
            let (p, s): (u8, i8) = match (p.trim().parse(), s.trim().parse()) {
                (Ok(p), Ok(s)) if (1..=38).contains(&p) && s >= 0 && s as u8 <= p => (p, s),
                _ => return Err(unsupported("needs 1 <= p <= 38 and 0 <= s <= p: numeric(p,s)")),
            };
            Ok((ColType::Decimal { p, s }, after.trim_start()))
        }
        "numeric" | "decimal" => Err(unsupported("needs a precision and a scale: numeric(p,s)")),
        "varchar" | "char" | "character" | "bpchar" => Err(unsupported("has no stored type: write text")),
        _ => Err(unsupported("is not supported: write integer, bigint, numeric(p,s), date, text or boolean")),
    }
}

/// The parenthesized group at the start of `text` (with its parentheses) and the text after it.
fn paren_group<'a>(at: &str, text: &'a str) -> Result<(&'a str, &'a str), FolderError> {
    let (mut depth, mut quoted) = (0usize, false);
    for (i, c) in text.char_indices() {
        match c {
            '\'' => quoted = !quoted,
            '(' if !quoted => depth += 1,
            ')' if !quoted => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return Ok((&text[..=i], text[i + 1..].trim_start()));
                }
            }
            _ => {}
        }
    }
    Err(syntax(format!("{at}: unbalanced parentheses in {:?}", head(text))))
}

/// An unquoted identifier, folded to lower case.
fn identifier(text: &str, what: &str) -> Result<String, FolderError> {
    let mut chars = text.chars();
    let valid = chars.next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_') && chars.all(|c| c.is_ascii_alphanumeric() || c == '_');
    if !valid {
        return Err(syntax(format!("{what} {text:?}: write an unquoted identifier (letters, digits and _)")));
    }
    Ok(text.to_ascii_lowercase())
}

/// `text` without the leading keywords `words` (case-insensitive, separated by single spaces as after [`collapse`]),
/// when it starts with them followed by a space or the end.
fn strip_keywords<'a>(text: &'a str, words: &[&str]) -> Option<&'a str> {
    let mut rest = text;
    for word in words {
        let candidate = rest.get(..word.len())?;
        if !candidate.eq_ignore_ascii_case(word) {
            return None;
        }
        rest = &rest[word.len()..];
        if !rest.is_empty() && !rest.starts_with(' ') {
            return None;
        }
        rest = rest.trim_start();
    }
    Some(rest)
}

/// The text after a leading `CHECK` keyword (followed by a space or `(`), starting at its expression.
fn strip_check(text: &str) -> Option<&str> {
    let rest = text.get(..5).filter(|word| word.eq_ignore_ascii_case("CHECK")).map(|_| &text[5..])?;
    (rest.starts_with(' ') || rest.starts_with('(')).then(|| rest.trim_start())
}

/// Split `text` at the first standalone keyword `word` (case-insensitive) outside quotes and parentheses.
fn split_keyword<'a>(text: &'a str, word: &str) -> Option<(&'a str, &'a str)> {
    let mut start = 0;
    while let Some(found) = text[start..].to_ascii_uppercase().find(&format!(" {word} ")) {
        let at = start + found;
        let before = &text[..at];
        if before.matches('\'').count() % 2 == 0 && before.matches('(').count() == before.matches(')').count() {
            return Some((before, &text[at + word.len() + 2..]));
        }
        start = at + 1;
    }
    None
}

/// The text without `--` comments (outside quoted literals).
fn strip_comments(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for line in text.lines() {
        let mut quoted = false;
        let mut end = line.len();
        let bytes = line.as_bytes();
        for (i, &b) in bytes.iter().enumerate() {
            match b {
                b'\'' => quoted = !quoted,
                b'-' if !quoted && bytes.get(i + 1) == Some(&b'-') => {
                    end = i;
                    break;
                }
                _ => {}
            }
        }
        out.push_str(&line[..end]);
        out.push('\n');
    }
    out
}

/// Split `text` at `separator` outside quoted literals and parentheses.
fn split_top(text: &str, separator: char) -> Vec<String> {
    let (mut parts, mut current, mut depth, mut quoted) = (vec![], String::new(), 0usize, false);
    for c in text.chars() {
        match c {
            '\'' => quoted = !quoted,
            '(' if !quoted => depth += 1,
            ')' if !quoted => depth = depth.saturating_sub(1),
            c if c == separator && !quoted && depth == 0 => {
                parts.push(std::mem::take(&mut current));
                continue;
            }
            _ => {}
        }
        current.push(c);
    }
    parts.push(current);
    parts
}

/// `text` with every whitespace run outside quoted literals replaced by one space, trimmed.
fn collapse(text: &str) -> String {
    let (mut out, mut quoted, mut space) = (String::with_capacity(text.len()), false, false);
    for c in text.trim().chars() {
        if c == '\'' {
            quoted = !quoted;
        }
        if !quoted && c.is_whitespace() {
            space = true;
            continue;
        }
        if space {
            out.push(' ');
            space = false;
        }
        out.push(c);
    }
    out
}

/// The first 60 characters of `text`, for messages.
fn head(text: &str) -> String {
    text.chars().take(60).collect()
}

fn syntax(detail: String) -> FolderError {
    FolderError::new("schema_syntax", detail)
}

fn unnamed_check(table: &str, item: &str) -> FolderError {
    FolderError::new("schema_unnamed_check", format!("{table}: {:?}: a CHECK must be named: write CONSTRAINT <name> CHECK (...)", head(item)))
}
