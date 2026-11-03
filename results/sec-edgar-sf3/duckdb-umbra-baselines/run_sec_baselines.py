"""SEC-EDGAR baseline timing with the unchanged TPC-H SF100 runner (results/tpch-sf100/duckdb-umbra-baselines/run_baselines.py).

The protocol, block layout, locks and value encoding are those of run_baselines.py: one block = one
engine x template x binding x thread count in a fresh session (DuckDB store read_only + `SET threads`; Umbra
`SET debug.parallel`, compilation mode `o` read back); PREPARE the template with the binding's literals substituted;
1 warm EXECUTE then 3 hot EXECUTEs; reported time = median hot time; no other timing runs during a block
(TIMING_LOCKS). Order: template, then threads, then binding, DuckDB then Umbra.

One addition, for SEC-EDGAR parameter types: run_baselines.literal() accepts date, integer/bigint/int,
numeric/decimal and text/varchar. Here a type with a length or precision suffix (`varchar(20)`, `char(2)`) is
reduced to its base name first, `char` is written as text, and `double`/`double precision`/`real`/`float` as a
plain numeric literal (checked to parse as a float). The patched function is installed as run_baselines.literal,
which bind_sql calls; nothing else changes.
Usage: run_sec_baselines.py <bindings.json> <benchmarks/sec-edgar> <out_dir> [--queries Q1,Q2] [--threads 1,32,64]
                            [--engines duckdb,umbra] [--dry-run | --prepare-check <threads>]
--dry-run binds every template x binding, prints the SQL, and connects to no engine (no timing, no lease).
--prepare-check <threads>: for every template x binding and engine, the runner's session setup, PREPARE, one EXECUTE
and the row count, at the given thread count (a functional check that the timing run will not fail; not timed, no
lease, nothing written).
Config by environment, as run_baselines.py: DUCKDB_STORE, PYTHONPATH (the DuckDB Python package), UMBRA_DSN, TIMING_LOCKS.
"""
import json, os, re, sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'tpch-sf100', 'duckdb-umbra-baselines'))
import run_baselines  # noqa: E402

_base_literal = run_baselines.literal


def sec_literal(value, ty):
    """run_baselines.literal with type names normalized: length/precision suffix dropped for text types, char as
    text, double/real/float as a numeric literal. Other types go to the unchanged function."""
    base = ty.strip().lower()
    name = re.sub(r'\s*\(.*\)$', '', base)
    if name in ('varchar', 'char', 'character', 'character varying', 'text'):
        return _base_literal(value, 'text')
    if name in ('double', 'double precision', 'real', 'float', 'float8', 'float4'):
        float(value); return value
    return _base_literal(value, base)


run_baselines.literal = sec_literal


def dry_run(bindings_path, templates_path, queries):
    bindings = json.load(open(bindings_path)); templates = run_baselines.load_templates(templates_path)
    for q in (queries.split(',') if queries else sorted(bindings['queries'])):
        for b in bindings['queries'][q]:
            sql = run_baselines.bind_sql(templates[q]['sql'], templates[q]['parameters'], b['arguments'])
            print(f"-- {q} {b['binding_id']} {b['arguments']}\n{sql};\n")


def prepare_check(bindings_path, templates_path, threads, queries):
    import os
    import duckdb, psycopg2
    bindings = json.load(open(bindings_path)); templates = run_baselines.load_templates(templates_path)
    for q in (queries.split(',') if queries else sorted(bindings['queries'])):
        for b in bindings['queries'][q]:
            sql = run_baselines.bind_sql(templates[q]['sql'], templates[q]['parameters'], b['arguments'])
            con = duckdb.connect(os.environ['DUCKDB_STORE'], read_only=True)
            try:
                con.execute(f'SET threads = {threads}'); con.execute('PREPARE q AS ' + sql)
                print(q, b['binding_id'], 'duckdb', len(con.execute('EXECUTE q').fetchall()), 'rows', flush=True)
            finally:
                con.close()
            con = psycopg2.connect(os.environ['UMBRA_DSN'], connect_timeout=10); con.autocommit = True
            cur = con.cursor()
            try:
                cur.execute(f'SET debug.parallel = {threads}'); cur.execute('PREPARE q AS ' + sql)
                cur.execute('EXECUTE q'); print(q, b['binding_id'], 'umbra', len(cur.fetchall()), 'rows', flush=True)
                cur.execute('DEALLOCATE q')
            finally:
                cur.close(); con.close()


if __name__ == '__main__':
    if '--prepare-check' in sys.argv:
        args = sys.argv[1:]
        q = args[args.index('--queries') + 1] if '--queries' in args else None
        prepare_check(args[0], args[1], int(args[args.index('--prepare-check') + 1]), q)
    elif '--dry-run' in sys.argv:
        args = [a for a in sys.argv[1:] if a != '--dry-run']
        q = args[args.index('--queries') + 1] if '--queries' in args else None
        dry_run(args[0], args[1], q)
    else:
        run_baselines.main()
