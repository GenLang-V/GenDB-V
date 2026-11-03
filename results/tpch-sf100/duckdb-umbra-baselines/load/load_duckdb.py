"""Constrained DuckDB load: CREATE TABLE with 8 PK + 7 FK (FKs only accepted at CREATE in DuckDB 1.5.6),
then INSERT ... SELECT * FROM read_parquet(...) per table in FK dependency order, CHECKPOINT per table.
lineitem/orders/partsupp are inserted as <chunks> disjoint key ranges by concurrent connections (one transaction
each): the transaction-local work (FK verification, local ART) overlaps; commits serialize inside DuckDB.
Usage: load_duckdb.py <db_path> <parquet_dir> <chunks> <memory_limit> <threads> [report.json]"""
import sys, os, json, time, threading, duckdb
B = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
db, src, chunks, mem, threads = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4], int(sys.argv[5])
report = sys.argv[6] if len(sys.argv) > 6 else None
assert not os.path.exists(db), 'fresh store required'
ORDER = ['region', 'nation', 'supplier', 'customer', 'part', 'partsupp', 'orders', 'lineitem']
KEY = {'lineitem': 'l_orderkey', 'orders': 'o_orderkey', 'partsupp': 'ps_partkey'}
con = duckdb.connect(db)
con.execute(f"SET memory_limit='{mem}'"); con.execute(f'SET threads={threads}')
con.execute(f"SET temp_directory='{os.path.dirname(db)}/spill'")
con.execute('SET preserve_insertion_order=true')
t0 = time.time(); con.execute(open(os.path.join(B, 'load', 'constrained-schema.sql')).read())
rep = {'version': con.execute('select version()').fetchone()[0], 'chunks': chunks, 'memory_limit': mem,
       'threads': threads, 'source': src, 'tables': {}}
def log(*a): print(time.strftime('%H:%M:%S'), *a, flush=True)
for t in ORDER:
    f = f'{src}/{t}.parquet'; s = time.time(); parts = []
    n = chunks if t in KEY and chunks > 1 else 1
    if n == 1:
        con.execute(f"INSERT INTO {t} SELECT * FROM read_parquet('{f}')"); parts.append(time.time() - s)
    else:
        lo, hi = con.execute(f"SELECT min({KEY[t]}), max({KEY[t]}) FROM read_parquet('{f}')").fetchone()
        step = (hi - lo) // n + 1; parts = [None] * n; errors = []
        def insert_range(i):
            try:
                cur = con.cursor(); a, b = lo + i * step, lo + (i + 1) * step; c0 = time.time()
                cur.execute('BEGIN')
                cur.execute(f"INSERT INTO {t} SELECT * FROM read_parquet('{f}') WHERE {KEY[t]} >= {a} AND {KEY[t]} < {b}")
                c1 = time.time(); cur.execute('COMMIT'); parts[i] = (round(c1 - c0, 1), round(time.time() - c1, 1))
                log(t, 'range', i, parts[i]); cur.close()
            except Exception as e:
                errors.append(f'{i}: {e}')
        ths = [threading.Thread(target=insert_range, args=(i,)) for i in range(n)]
        [x.start() for x in ths]; [x.join() for x in ths]
        if errors:
            raise SystemExit(f'{t} insert failed: {errors}')
        parts = [time.time() - s]
    c = time.time(); con.execute('CHECKPOINT'); ck = time.time() - c
    rows = con.execute(f'SELECT count(*) FROM {t}').fetchone()[0]
    rep['tables'][t] = {'rows': rows, 'insert_s': round(sum(parts), 2), 
                        'checkpoint_s': round(ck, 2), 'total_s': round(time.time() - s, 2)}
    log(t, rep['tables'][t])
rep['total_s'] = round(time.time() - t0, 2)
rep['constraints'] = con.execute("SELECT table_name, constraint_type, constraint_text FROM duckdb_constraints() "
                                 "WHERE constraint_type IN ('PRIMARY KEY','FOREIGN KEY') ORDER BY 1,2,3").fetchall()
rep['index_count'] = con.execute('SELECT table_name, index_count FROM duckdb_tables() ORDER BY 1').fetchall()
rep['database_size'] = con.execute('PRAGMA database_size').fetchall()
con.close(); rep['file_bytes'] = os.path.getsize(db)
log('DONE', rep['total_s'])
if report: json.dump(rep, open(report, 'w'), indent=1, default=str)
