"""Baseline timing for the TPC-H SF100 templates (DuckDB and Umbra, stores with the declared keys).

One block = one engine x query x binding x thread count, in a fresh session: set the thread count, PREPARE the
template with the binding's arguments substituted as typed literals, 1 warm EXECUTE, then 3 hot EXECUTEs; the
reported time is the median hot time. Timed interval per execution: EXECUTE + fetchall. Block order: query, then
threads 1/32/64, then binding, DuckDB then Umbra. No other timing runs during a block (TIMING_LOCKS).

Usage: run_baselines.py <bindings.json> <benchmarks/tpc-h> <out_dir> [--queries Q01,Q02] [--threads 1,32,64]
                        [--engines duckdb,umbra]
Results: <out_dir>/blocks/<engine>/<QNN>/<binding>-t<threads>.json (existing blocks are skipped); aggregate.py turns
them into times.json. Config by environment: DUCKDB_STORE, PYTHONPATH (the DuckDB Python package), UMBRA_DSN,
TIMING_LOCKS (three colon-separated absolute paths).
"""
import argparse, datetime as dt, decimal, fcntl, json, os, statistics, sys, time

DEFAULT_LOCKS = ['/path/to/locks/locks/activity.lock',
                 '/path/to/locks/build.lock',
                 '/path/to/scratch/locks/race.lock']


def literal(value, ty):
    """SQL literal for one GenDB argument string of the template parameter type."""
    ty = ty.lower()
    if ty == 'date':
        dt.date.fromisoformat(value); return f"DATE '{value}'"
    if ty in ('integer', 'bigint', 'int'):
        return str(int(value))
    if ty.startswith(('numeric', 'decimal')):
        decimal.Decimal(value); return value
    if ty in ('text', 'varchar'):
        return "'" + value.replace("'", "''") + "'"
    raise ValueError(f'unsupported parameter type {ty}')


def bind_sql(sql, params, arguments):
    """Substitute $k by the typed literal of arguments[k-1] (highest index first so $1 never matches $10)."""
    if len(params) != len(arguments):
        raise ValueError('argument count differs from template parameters')
    by_index = {p['index']: p['type'] for p in params}
    for k in sorted(by_index, reverse=True):
        sql = sql.replace(f'${k}', literal(arguments[k - 1], by_index[k]))
    if '$' in sql.replace("'$", ''):
        raise ValueError('unsubstituted parameter left in SQL')
    return sql.strip().rstrip(';')


def jsonable(v):
    if isinstance(v, decimal.Decimal):
        return {'dec': str(v)}
    if isinstance(v, float):
        return {'f64': repr(v)}
    if isinstance(v, (dt.date, dt.datetime)):
        return {'date': v.isoformat()}
    return v


class Lease:
    def __init__(self, paths):
        self.paths = paths
    def __enter__(self):
        self.files = []
        for p in self.paths:
            os.makedirs(os.path.dirname(p), exist_ok=True)
            f = open(p, 'a+'); fcntl.flock(f.fileno(), fcntl.LOCK_EX); self.files.append(f)
        return self
    def __exit__(self, *exc):
        for f in reversed(self.files):
            f.close()


def timed(run):
    started = time.perf_counter_ns()
    rows = run(); n = len(rows)
    return time.perf_counter_ns() - started, n, rows


def duckdb_block(sql, threads):
    import duckdb
    con = duckdb.connect(os.environ['DUCKDB_STORE'], read_only=True)
    try:
        con.execute(f'SET threads = {threads}')
        if con.execute("SELECT current_setting('threads')").fetchone()[0] != threads:
            raise ValueError('DuckDB thread readback differs')
        con.execute('SET enable_progress_bar = false')
        con.execute('PREPARE q AS ' + sql)
        run = lambda: con.execute('EXECUTE q').fetchall()
        info = {'version': con.execute('SELECT version()').fetchone()[0], 'threads_readback': threads}
        return info, run_protocol(run)
    finally:
        con.close()


def umbra_block(sql, threads):
    import psycopg2
    con = psycopg2.connect(os.environ['UMBRA_DSN'], connect_timeout=10); con.autocommit = True
    cur = con.cursor()
    try:
        cur.execute(f'SET debug.parallel = {threads}')
        cur.execute('SHOW debug.parallel'); par = cur.fetchone()[0]
        cur.execute('SHOW debug.compilationmode'); mode = cur.fetchone()[0]
        if str(par) != str(threads) or mode != 'o':
            raise ValueError(f'Umbra readback differs: parallel={par} mode={mode}')
        cur.execute('SELECT version()'); version = cur.fetchone()[0]
        cur.execute('PREPARE q AS ' + sql)
        def run():
            cur.execute('EXECUTE q'); return cur.fetchall()
        info = {'version': version, 'debug.parallel': par, 'debug.compilationmode': mode}
        try:
            return info, run_protocol(run)
        finally:
            cur.execute('DEALLOCATE q')
    finally:
        cur.close(); con.close()


def run_protocol(run):
    warm_ns, warm_n, warm_rows = timed(run)
    rows = [[jsonable(v) for v in r] for r in warm_rows]; del warm_rows
    hot = []
    for _ in range(3):
        ns, n, r = timed(run); del r; hot.append((ns, n))
    return {'warm_ns': warm_ns, 'warm_rows': warm_n, 'hot_ns': [h[0] for h in hot], 'hot_rows': [h[1] for h in hot],
            'median_ns': int(statistics.median(h[0] for h in hot)), 'result': rows}


def load_templates(folder):
    """The query files <folder>/queries/<Q>.sql (benchmarks/tpc-h): per query its SQL (the text after the header) and
    its typed $k parameters (the header lines `-- $k name type`)."""
    templates = {}
    for name in sorted(os.listdir(os.path.join(folder, 'queries'))):
        if not name.endswith('.sql'):
            continue
        lines = open(os.path.join(folder, 'queries', name)).read().splitlines(keepends=True)
        params = []
        while lines and lines[0].startswith('-- $'):
            index, param, ty = lines.pop(0)[4:].split()[:3]
            params.append({'index': int(index), 'name': param, 'type': ty})
        templates[name[:-4]] = {'sql': ''.join(lines), 'parameters': params}
    return templates


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('bindings'); ap.add_argument('benchmark'); ap.add_argument('out')
    ap.add_argument('--queries'); ap.add_argument('--threads', default='1,32,64'); ap.add_argument('--engines', default='duckdb,umbra')
    a = ap.parse_args()
    bindings = json.load(open(a.bindings)); templates = load_templates(a.benchmark)
    locks = os.environ['TIMING_LOCKS'].split(':') if os.environ.get('TIMING_LOCKS') else DEFAULT_LOCKS
    queries = a.queries.split(',') if a.queries else sorted(bindings['queries'])
    engines = {'duckdb': duckdb_block, 'umbra': umbra_block}
    for q in queries:
        tpl = templates[q]
        for threads in [int(t) for t in a.threads.split(',')]:
            for b in bindings['queries'][q]:
                sql = bind_sql(tpl['sql'], tpl['parameters'], b['arguments'])
                for engine in a.engines.split(','):
                    path = f"{a.out}/blocks/{engine}/{q}/{b['binding_id']}-t{threads}.json"
                    if os.path.exists(path):
                        continue
                    os.makedirs(os.path.dirname(path), exist_ok=True)
                    rec = {'engine': engine, 'query': q, 'binding_id': b['binding_id'], 'threads': threads,
                           'arguments': b['arguments'], 'sql': sql, 'bindings_file': a.bindings}
                    rec['lock_wait_start_utc'] = dt.datetime.now(dt.timezone.utc).isoformat()
                    with Lease(locks):
                        rec['start_utc'] = dt.datetime.now(dt.timezone.utc).isoformat()
                        rec['loadavg_start'] = os.getloadavg()
                        try:
                            rec['session'], rec['run'] = engines[engine](sql, threads)
                            rec['ok'] = True
                        except Exception as e:
                            rec['ok'] = False; rec['error'] = f'{type(e).__name__}: {e}'
                        rec['end_utc'] = dt.datetime.now(dt.timezone.utc).isoformat()
                        rec['loadavg_end'] = os.getloadavg()
                    with open(path + '.tmp', 'w') as f:
                        json.dump(rec, f); f.write('\n')
                    os.replace(path + '.tmp', path)
                    med = rec['run']['median_ns'] / 1e6 if rec['ok'] else rec['error']
                    print(rec['end_utc'], engine, q, b['binding_id'], threads, med, flush=True)


if __name__ == '__main__':
    main()
