"""Write the Umbra load script of the canonical SEC-EDGAR SF3 schema (sec_schema.py).

Same tables, columns, types (INTEGER, VARCHAR without length, NUMERIC(28,4)), nullability and keys as the DuckDB
store. The 3 primary keys are in CREATE TABLE; the 4 foreign keys are added with ALTER TABLE ... ADD FOREIGN KEY
after all COPYs. Per table, in the order sub, tag, num, pre: COPY from '/data/<t>.csv' (export_for_umbra.py format)
and a row-count line; then the foreign keys; then the pg_index listing.
Usage: make_umbra_sql.py <out.sql>
"""
import os, sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', '..', 'benchmarks', 'sec-edgar'))
import sec_schema  # noqa: E402


def main():
    out = sys.argv[1]
    sql = ["ALTER ROLE postgres WITH LOGIN SUPERUSER PASSWORD 'postgres';",
           sec_schema.create_tables(sec_schema.UMBRA_TYPE, True, False).strip()]
    for t in sec_schema.ORDER:
        sql.append(f"COPY {t} FROM '/data/{t}.csv' WITH (FORMAT csv, DELIMITER '|', NULL '', QUOTE '\"');")
        sql.append(f"SELECT 'loaded' AS step, '{t}' AS tbl, COUNT(*) AS n, now() AS at FROM {t};")
    for alter in sec_schema.foreign_key_alters():
        sql.append(alter)
        sql.append(f"SELECT 'constraint' AS step, '{alter[:-1]}' AS what, now() AS at;")
    sql.append('SELECT c.relname, i.indisprimary, i.indisunique FROM pg_index i, pg_class c '
               'WHERE c.oid = i.indexrelid ORDER BY 1;')
    with open(out, 'x') as f:
        f.write('\n'.join(sql) + '\n')


if __name__ == '__main__':
    main()
