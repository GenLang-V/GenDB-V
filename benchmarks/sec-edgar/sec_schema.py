"""The canonical SEC-EDGAR SF3 schema setting: one definition read by every script that writes data,
DDL or GenDB inputs, so GenDB, DuckDB and Umbra get the same tables, columns, types, nullability and keys.

Columns: 48 of the source columns, with their source names (num.segments and 16 sub columns are dropped).
Types: integer = SQL INTEGER (Arrow Int32, GenDB `integer`); text = VARCHAR without length (Arrow Utf8, GenDB `text`;
GenDB's dataset has no length-bounded text type, and the TPC-H setting also uses VARCHAR without size);
numeric = NUMERIC(28,4) (Arrow Decimal128(28,4)) for num.value, the SEC's own definition of the field.
Nullability: the source documentation's "May be NULL" column (FSDS readme.htm, figures 2-5), with two kinds of
exception: three columns the documentation lists as never NULL but which are NULL in the SF3 source rows (sub.period
7 rows, pre.stmt 1,073, pre.plabel 1,332) are declared nullable so that no source row is lost
(NULLABLE_DESPITE_DOCUMENTATION); num.value, documented as nullable, is declared NOT NULL because the cleaning step
drops every row whose value is NULL, so the canonical data has none by construction (NOT_NULL_BY_CLEANING).
Keys: the 7 declarations that hold at SF3 (3 primary keys, 4 foreign keys).
"""

# (column, type, nullable per the source documentation)
TABLES = {
    'sub': [
        ('adsh', 'text', False), ('cik', 'integer', False), ('name', 'text', False), ('sic', 'integer', True),
        ('countryba', 'text', True), ('stprba', 'text', True), ('cityba', 'text', True),
        ('countryinc', 'text', True), ('form', 'text', False), ('period', 'integer', False),
        ('fy', 'integer', True), ('fp', 'text', True), ('filed', 'integer', False), ('accepted', 'text', False),
        ('prevrpt', 'integer', False), ('nciks', 'integer', False), ('afs', 'text', True),
        ('wksi', 'integer', False), ('fye', 'text', True), ('instance', 'text', False),
    ],
    'num': [
        ('adsh', 'text', False), ('tag', 'text', False), ('version', 'text', False), ('ddate', 'integer', False),
        ('qtrs', 'integer', False), ('uom', 'text', False), ('coreg', 'text', True), ('value', 'numeric', True),
        ('footnote', 'text', True),
    ],
    'tag': [
        ('tag', 'text', False), ('version', 'text', False), ('custom', 'integer', False),
        ('abstract', 'integer', False), ('datatype', 'text', True), ('iord', 'text', False), ('crdr', 'text', True),
        ('tlabel', 'text', True), ('doc', 'text', True),
    ],
    'pre': [
        ('adsh', 'text', False), ('report', 'integer', False), ('line', 'integer', False), ('stmt', 'text', False),
        ('inpth', 'integer', False), ('rfile', 'text', False), ('tag', 'text', False), ('version', 'text', False),
        ('plabel', 'text', False), ('negating', 'integer', False),
    ],
}

# Documented as never NULL, NULL in SF3 source rows: declared nullable (the rows are kept).
NULLABLE_DESPITE_DOCUMENTATION = {('sub', 'period'), ('pre', 'stmt'), ('pre', 'plabel')}

# Documented as nullable, never NULL in the canonical data because the cleaning step drops those rows: NOT NULL.
NOT_NULL_BY_CLEANING = {('num', 'value')}

# Load order: referenced tables first. The GenDB dataset lists the tables in schema.sql order.
ORDER = ['sub', 'tag', 'num', 'pre']
DATASET_ORDER = ['sub', 'num', 'tag', 'pre']

PRIMARY_KEYS = [('sub', ['adsh']), ('tag', ['tag', 'version']), ('pre', ['adsh', 'report', 'line'])]
FOREIGN_KEYS = [
    ('num', ['adsh'], 'sub', ['adsh']),
    ('pre', ['adsh'], 'sub', ['adsh']),
    ('num', ['tag', 'version'], 'tag', ['tag', 'version']),
    ('pre', ['tag', 'version'], 'tag', ['tag', 'version']),
]

SQL_TYPE = {'integer': 'integer', 'text': 'text', 'numeric': 'numeric(28,4)'}  # GenDB schema setting spelling
DUCKDB_TYPE = {'integer': 'INTEGER', 'text': 'VARCHAR', 'numeric': 'DECIMAL(28,4)'}
UMBRA_TYPE = {'integer': 'INTEGER', 'text': 'VARCHAR', 'numeric': 'NUMERIC(28,4)'}
GENDB_TYPE = {'integer': 'I32', 'text': 'Utf8', 'numeric': {'Decimal': {'p': 28, 's': 4}}}


def columns(table):
    """(column, type, declared nullable) of one table: the documentation's nullability with the exceptions above."""
    return [(c, ty, (nullable or (table, c) in NULLABLE_DESPITE_DOCUMENTATION) and (table, c) not in NOT_NULL_BY_CLEANING)
            for c, ty, nullable in TABLES[table]]


def arrow_schema(table):
    import pyarrow as pa
    arrow = {'integer': pa.int32(), 'text': pa.utf8(), 'numeric': pa.decimal128(28, 4)}
    return pa.schema([pa.field(c, arrow[ty], nullable=n) for c, ty, n in columns(table)])


def create_tables(types, primary_in_create, foreign_in_create, order=ORDER):
    """CREATE TABLE statements in `order`, with the primary and foreign keys inside when asked."""
    out = []
    for t in order:
        lines = [f'    {c} {types[ty]}{"" if n else " NOT NULL"}' for c, ty, n in columns(t)]
        if primary_in_create:
            lines += [f'    PRIMARY KEY ({", ".join(k)})' for pt, k in PRIMARY_KEYS if pt == t]
        if foreign_in_create:
            lines += [f'    FOREIGN KEY ({", ".join(k)}) REFERENCES {rt} ({", ".join(rk)})'
                      for ft, k, rt, rk in FOREIGN_KEYS if ft == t]
        out.append(f'CREATE TABLE {t} (\n' + ',\n'.join(lines) + '\n);')
    return '\n'.join(out) + '\n'


def primary_key_alters():
    return [f'ALTER TABLE {t} ADD PRIMARY KEY ({", ".join(k)});' for t, k in PRIMARY_KEYS]


def foreign_key_alters():
    return [f'ALTER TABLE {ft} ADD FOREIGN KEY ({", ".join(k)}) REFERENCES {rt} ({", ".join(rk)});'
            for ft, k, rt, rk in FOREIGN_KEYS]


def gendb_declarations():
    """GenDB integrity_constraints declarations (the request's `integrity_constraints.declarations`)."""
    return ([{'table': t, 'sql': f'PRIMARY KEY ({", ".join(k)})'} for t, k in PRIMARY_KEYS]
            + [{'table': ft, 'sql': f'FOREIGN KEY ({", ".join(k)}) REFERENCES {rt} ({", ".join(rk)})'}
               for ft, k, rt, rk in FOREIGN_KEYS])
