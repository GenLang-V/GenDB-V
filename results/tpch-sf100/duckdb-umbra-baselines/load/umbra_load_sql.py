"""Write the Umbra load script. mode 'pre': constrained CREATE TABLE then COPY; mode 'post': plain CREATE TABLE,
COPY, then ALTER TABLE ADD PRIMARY KEY / FOREIGN KEY (8 PK first, then 7 FK). Usage: umbra_load_sql.py <mode> <out.sql>"""
import os, re, sys
B = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
mode, out = sys.argv[1], sys.argv[2]
ORDER = ['region', 'nation', 'supplier', 'customer', 'part', 'partsupp', 'orders', 'lineitem']
schema = open(os.path.join(B, '..', '..', '..', 'benchmarks', 'tpc-h', 'schema.sql')).read()
cons = [{'table': m[1], 'sql': m[2]} for m in re.finditer(r'^ALTER TABLE (\w+) ADD (.*);$', schema, re.M)]
# 'pre': the schema with the keys beside this script; 'post': the CREATE TABLE statements of schema.sql, keys added below.
columns = '\n'.join(m[0] for m in re.finditer(r'^CREATE TABLE .*?\);$', schema, re.M | re.S))
sql = ["ALTER ROLE postgres WITH LOGIN SUPERUSER PASSWORD 'postgres';",
       open(os.path.join(B, 'load', 'constrained-schema.sql')).read() if mode == 'pre' else columns]
for t in ORDER:
    sql.append(f"COPY {t} FROM '/data/{t}.tbl' WITH (DELIMITER '|');")
    sql.append(f"SELECT 'loaded' AS step, '{t}' AS tbl, COUNT(*) AS n, now() AS at FROM {t};")
if mode == 'post':
    for d in sorted(cons, key=lambda d: 'FOREIGN' in d['sql']):
        sql.append(f"ALTER TABLE {d['table']} ADD {d['sql']};")
        sql.append(f"SELECT 'constraint' AS step, '{d['table']}: {d['sql']}' AS what, now() AS at;")
sql.append("SELECT c.relname, i.indisprimary, i.indisunique FROM pg_index i, pg_class c WHERE c.oid = i.indexrelid ORDER BY 1;")
open(out, 'w').write('\n'.join(sql) + '\n')
