"""SEC-EDGAR baseline timing: run_sec_baselines.py (the TPC-H SF100 run_baselines.py with the SEC-EDGAR parameter
types), with one change to the DuckDB block: it PREPAREs the statement again before every execution, outside the timed
interval (the previous one is DEALLOCATEd), for every template. Everything else is the runner's protocol: a fresh
read-only session per block, `SET threads` read back, 1 warm + 3 hot executions, each timed as EXECUTE + fetchall,
the median of the 3 hot times. Umbra blocks are unchanged.
Usage: as run_sec_baselines.py: sec_baselines_runner.py <bindings.json> <benchmarks/sec-edgar> <out_dir> [--queries ..]
       [--threads ..] [--engines ..]
"""
import os, statistics, sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import run_sec_baselines as e2b  # noqa: E402  (installs the SEC literal types into run_baselines)

rb = e2b.run_baselines
PREPARE_PER_EXECUTION = 'PREPARE before every execution, outside the timed interval'


def duckdb_block(sql, threads):
    """run_baselines.duckdb_block with a fresh PREPARE before each of the 1 warm + 3 hot executions."""
    import duckdb
    con = duckdb.connect(os.environ['DUCKDB_STORE'], read_only=True)
    try:
        con.execute(f'SET threads = {threads}')
        if con.execute("SELECT current_setting('threads')").fetchone()[0] != threads:
            raise ValueError('DuckDB thread readback differs')
        con.execute('SET enable_progress_bar = false')
        info = {'version': con.execute('SELECT version()').fetchone()[0], 'threads_readback': threads,
                'prepare': PREPARE_PER_EXECUTION}
        prepared = [False]

        def prepare():
            if prepared[0]:
                con.execute('DEALLOCATE q')
            con.execute('PREPARE q AS ' + sql); prepared[0] = True

        run = lambda: con.execute('EXECUTE q').fetchall()
        prepare()
        warm_ns, warm_n, warm_rows = rb.timed(run)
        rows = [[rb.jsonable(v) for v in r] for r in warm_rows]; del warm_rows
        hot = []
        for _ in range(3):
            prepare()
            ns, n, r = rb.timed(run); del r; hot.append((ns, n))
        return info, {'warm_ns': warm_ns, 'warm_rows': warm_n, 'hot_ns': [h[0] for h in hot],
                      'hot_rows': [h[1] for h in hot], 'median_ns': int(statistics.median(h[0] for h in hot)),
                      'result': rows}
    finally:
        con.close()


rb.duckdb_block = duckdb_block

if __name__ == '__main__':
    if '--prepare-check' in sys.argv or '--dry-run' in sys.argv:
        raise SystemExit('use run_sec_baselines.py for --dry-run and --prepare-check')
    rb.main()
