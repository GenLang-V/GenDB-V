"""Load the canonical SEC-EDGAR SF3 Parquet into a fresh DuckDB store under the canonical schema (sec_schema.py).

DDL: `CREATE TABLE` with every key inside (3 PRIMARY KEY, 4 FOREIGN KEY), as in the TPC-H baselines; DuckDB enforces
them during the INSERTs, so a load that finishes is a check that all 7 hold. Types: INTEGER, VARCHAR (no length),
DECIMAL(28,4); NOT NULL as declared. Each table: `INSERT INTO t SELECT * FROM read_parquet(<exact>/t.parquet)` in
the order sub, tag, num, pre (referenced tables first), insertion order preserved; then CHECKPOINT. Row counts are
checked against the Parquet MANIFEST.json.
Usage: load_duckdb_canonical.py <db_path> <exact_dir> <memory_limit> <threads> <report.json>
Effects: creates <db_path> (refuses an existing one) and <db_dir>/spill; writes <report.json> (refuses an existing one).
"""
import json, os, sys, time

import duckdb

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', '..', 'benchmarks', 'sec-edgar'))
import sec_schema  # noqa: E402


def log(*a):
    print(time.strftime('%H:%M:%S'), *a, flush=True)


def main():
    db, exact, mem, threads, report = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5]
    assert not os.path.exists(db) and not os.path.exists(report), 'fresh store and report required'
    manifest = json.load(open(f'{exact}/MANIFEST.json'))
    con = duckdb.connect(db)
    con.execute(f"SET memory_limit='{mem}'"); con.execute(f'SET threads={threads}')
    con.execute(f"SET temp_directory='{os.path.dirname(db)}/spill'"); con.execute('SET preserve_insertion_order=true')
    ddl = sec_schema.create_tables(sec_schema.DUCKDB_TYPE, True, True)
    t0 = time.time(); con.execute(ddl)
    rep = {'version': con.execute('SELECT version()').fetchone()[0], 'memory_limit': mem, 'threads': threads,
           'source': exact, 'ddl': ddl, 'start_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime(t0)), 'tables': {}}
    for t in sec_schema.ORDER:
        s = time.time()
        con.execute(f"INSERT INTO {t} SELECT * FROM read_parquet('{exact}/{t}.parquet')")
        c = time.time(); con.execute('CHECKPOINT')
        rows = con.execute(f'SELECT count(*) FROM {t}').fetchone()[0]
        rep['tables'][t] = {'rows': rows, 'manifest_rows': manifest['tables'][t]['rows'],
                            'insert_s': round(c - s, 2), 'checkpoint_s': round(time.time() - c, 2)}
        log(t, rep['tables'][t])
        if rows != manifest['tables'][t]['rows']:
            raise SystemExit(f'{t}: {rows} rows loaded, MANIFEST says {manifest["tables"][t]["rows"]}')
    rep['total_s'] = round(time.time() - t0, 2)
    rep['constraints'] = con.execute("SELECT table_name, constraint_type, constraint_text FROM duckdb_constraints() "
                                     "WHERE constraint_type IN ('PRIMARY KEY','FOREIGN KEY') ORDER BY 1,2,3").fetchall()
    rep['index_count'] = con.execute('SELECT table_name, index_count FROM duckdb_tables() ORDER BY 1').fetchall()
    rep['columns'] = con.execute("SELECT table_name, column_name, data_type, is_nullable FROM duckdb_columns() "
                                 "WHERE NOT internal AND table_name IN ('sub','num','tag','pre') "
                                 "ORDER BY table_name, column_index").fetchall()
    rep['database_size'] = con.execute('PRAGMA database_size').fetchall()
    con.close(); rep['file_bytes'] = os.path.getsize(db)
    rep['end_utc'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
    log('DONE', rep['total_s'], len(rep['constraints']), 'constraints')
    with open(report, 'x') as f:
        json.dump(rep, f, indent=1, default=str); f.write('\n')


if __name__ == '__main__':
    main()
