"""CSV export of the canonical SEC-EDGAR SF3 Parquet for the Umbra load (the same rows in the same order).

Per table: DuckDB `COPY (SELECT * FROM read_parquet(<exact>/<t>.parquet)) TO <out>/<t>.csv` with '|' delimiter, '"'
quoting (doubled inside), no header; NULL is an unquoted empty field, an empty string would be "" (the canonical
data has none: the cleaning step makes every empty field NULL). DECIMAL(28,4) values are written as exact decimal
text (e.g. -1495000.0000), so no binary floating point is involved. Umbra's COPY ... FORMAT csv, NULL '' reads
them back the same way.
Usage: export_for_umbra.py <exact_dir> <out_dir> <threads> <report.json>
Effects: writes <out_dir>/{sub,tag,num,pre}.csv (refuses existing files) and <report.json>.
"""
import json, os, sys, time

import duckdb

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', '..', 'benchmarks', 'sec-edgar'))
import sec_schema  # noqa: E402


def main():
    exact, out, threads, report = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
    os.makedirs(out, exist_ok=True)
    con = duckdb.connect()
    con.execute(f'SET threads={threads}'); con.execute('SET preserve_insertion_order=true')
    rep = {'version': con.execute('SELECT version()').fetchone()[0], 'source': exact, 'tables': {}}
    for t in sec_schema.ORDER:
        path = f'{out}/{t}.csv'
        assert not os.path.exists(path), path
        s = time.time()
        src = f"read_parquet('{exact}/{t}.parquet')"
        con.execute(f"COPY (SELECT * FROM {src}) TO '{path}' (FORMAT csv, DELIMITER '|', HEADER false, QUOTE '\"', ESCAPE '\"')")
        rep['tables'][t] = {'rows': con.execute(f'SELECT count(*) FROM {src}').fetchone()[0],
                            'bytes': os.path.getsize(path), 'export_s': round(time.time() - s, 2)}
        print(t, rep['tables'][t], flush=True)
    con.close()
    with open(report, 'x') as f:
        json.dump(rep, f, indent=1); f.write('\n')


if __name__ == '__main__':
    main()
