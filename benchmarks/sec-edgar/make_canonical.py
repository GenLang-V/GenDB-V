"""Canonical SEC-EDGAR SF3 data: one deterministic cleaning step from the SEC's raw text files to one Parquet file per
table with the exact schema of `sec_schema.py` (the data GenDB, DuckDB and Umbra all read).

Source: `<data_dir>/{2022,2023,2024}q{1..4}/{sub,num,tag,pre}.txt` (SEC Financial Statement Data Sets; UTF-8,
tab-delimited, '\\n'-terminated lines, header line with lowercase column names). Read only.

Cleaning rules (deterministic):
1. Fields: split on tab only; no quoting or escaping; an empty field is NULL and no other text is (only '' is a NULL
   marker; 'NA' and similar stay text); text is kept byte for byte (no trimming).
2. Malformed lines are rejected: a line whose field count differs from its file's header (a tab inside a field, an
   empty line) is not loaded. Each rejected line is listed with its file, line number and field count. Every other
   line is checked to yield one row: rows + rejected lines = data lines (newline count minus the header).
3. Columns: the 48 columns of `sec_schema.py`; other source columns (num.segments, 16 sub columns) are dropped.
4. Types are parsed strictly; any value that does not parse stops the step (none is dropped silently): integer
   columns as 32-bit integers; num.value as an exact decimal: it must match -?[0-9]+(.[0-9]{1,4})? and is converted
   to Decimal128(28,4) without rounding.
5. num: rows whose value is NULL are dropped.
6. tag: one row per (tag, version), the first in source order (quarter order, then line order); every duplicate is
   checked to be identical to the kept row in all 9 columns, so the choice cannot change the data.
7. Row order: quarters in order 2022q1 .. 2024q4, each file in line order (tag: first occurrences in that order).
8. Declared NOT NULL columns must have no NULL (checked; the step stops otherwise).
Output: `<out_dir>/{sub,num,tag,pre}.parquet` (Snappy, row groups of at most 1,000,000 rows, the Arrow schema of
`sec_schema.arrow_schema`), `<out_dir>/MANIFEST.json` (schema, rows and bytes per table) and `<record>` (the
generation record: per-file counts, rejected lines, tag deduplication, per-column NULL counts and text lengths,
decimal facts). Refuses existing outputs.
Usage: make_canonical.py <data_dir> <out_dir> <record.json>
"""
import decimal, glob, json, os, platform, sys, time

import pyarrow as pa
import pyarrow.compute as pc
import pyarrow.csv as pcsv
import pyarrow.parquet as pq

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sec_schema  # noqa: E402

QUARTERS = [f'{y}q{q}' for y in (2022, 2023, 2024) for q in (1, 2, 3, 4)]
ROW_GROUP_ROWS = 1_000_000
DECIMAL_TEXT = r'^-?[0-9]+(\.[0-9]{1,4})?$'
ARROW_TYPE = {'integer': pa.int32(), 'text': pa.utf8(), 'numeric': pa.decimal128(28, 4)}


def log(*a):
    print(time.strftime('%H:%M:%S'), *a, flush=True)


def data_lines(path):
    """Newline count minus the header line (plus one when the last line has no newline)."""
    n, last = 0, b'\n'
    with open(path, 'rb') as f:
        while chunk := f.read(1 << 24):
            n += chunk.count(b'\n'); last = chunk[-1:]
    return n - 1 + (last != b'\n')


def read_file(path, table):
    """One source file as strings (rules 1-3): (table of the schema's columns, rejected lines)."""
    rejected = []

    def reject(row):
        rejected.append({'line': row.number, 'fields': row.actual_columns, 'expected': row.expected_columns,
                         'text_prefix': row.text[:200]})
        return 'skip'

    with open(path, encoding='utf-8') as f:
        header = f.readline().rstrip('\n').split('\t')
    wanted = [c for c, _, _ in sec_schema.columns(table)]
    missing = [c for c in wanted if c not in header]
    if missing:
        raise SystemExit(f'{path}: header lacks {missing}')
    strings = pcsv.read_csv(
        path,
        read_options=pcsv.ReadOptions(use_threads=False, block_size=1 << 26),
        parse_options=pcsv.ParseOptions(delimiter='\t', quote_char=False, double_quote=False, escape_char=False,
                                        newlines_in_values=False, ignore_empty_lines=False,
                                        invalid_row_handler=reject),
        convert_options=pcsv.ConvertOptions(column_types={c: pa.string() for c in header}, null_values=[''],
                                            strings_can_be_null=True, quoted_strings_can_be_null=True,
                                            check_utf8=True, include_columns=wanted))
    return strings, sorted(rejected, key=lambda r: r['line'])


def typed(strings, table, where):
    """Rule 4: the string columns parsed to the declared Arrow types (strict)."""
    arrays = []
    for c, ty, _ in sec_schema.columns(table):
        col = strings[c]
        if ty == 'numeric':
            bad = pc.sum(pc.invert(pc.fill_null(pc.match_substring_regex(col, DECIMAL_TEXT), True))).as_py() or 0
            if bad:
                raise SystemExit(f'{where}: {bad} {c} values are not plain decimals with at most 4 fraction digits')
        arrays.append(pc.cast(col, ARROW_TYPE[ty]) if ty != 'text' else col)
    return pa.Table.from_arrays([a.combine_chunks() if isinstance(a, pa.ChunkedArray) else a for a in arrays],
                                schema=sec_schema.arrow_schema(table))


def dedup_tag(tables):
    """Rule 6: first occurrence per (tag, version) in source order; duplicates must equal the kept row."""
    staged = pa.concat_tables(tables)
    staged = staged.append_column('source_order', pa.array(range(staged.num_rows), pa.int64()))
    keys = staged.group_by(['tag', 'version'], use_threads=False).aggregate([('source_order', 'min')])
    full = staged.group_by([c for c, _, _ in sec_schema.columns('tag')], use_threads=False).aggregate([])
    if full.num_rows != keys.num_rows:
        raise SystemExit(f'tag: {keys.num_rows} distinct keys but {full.num_rows} distinct rows: duplicates differ')
    keep = pc.sort_indices(keys['source_order_min'])
    kept = staged.take(pc.take(keys['source_order_min'], keep)).drop_columns(['source_order'])
    return kept, {'staged_rows': staged.num_rows, 'distinct_keys': keys.num_rows, 'distinct_rows': full.num_rows,
                  'duplicates_removed': staged.num_rows - keys.num_rows}


def column_facts(table, data):
    """Per column: NULL count; text: max length in characters and bytes; numeric: |value| >= 2^53 count."""
    facts = {}
    for c, ty, nullable in sec_schema.columns(table):
        col = data[c]
        f = {'type': ty, 'declared_nullable': nullable, 'nulls': col.null_count}
        if ty == 'text':
            f['max_chars'] = pc.max(pc.utf8_length(col)).as_py()
            f['max_bytes'] = pc.max(pc.binary_length(col)).as_py()
        if ty == 'numeric':
            big = pc.greater_equal(pc.abs(col), pa.scalar(decimal.Decimal(2 ** 53), pa.decimal128(28, 4)))
            f['abs_ge_2_pow_53'] = pc.sum(pc.cast(big, pa.int64())).as_py()
            f['min'] = str(pc.min(col).as_py()); f['max'] = str(pc.max(col).as_py())
        if not nullable and col.null_count:
            raise SystemExit(f'{table}.{c} is declared NOT NULL but has {col.null_count} NULLs')
        facts[c] = f
    return facts


def write_parquet(path, table, parts):
    """Write the parts in order as one Parquet file; returns (rows, row groups)."""
    with pq.ParquetWriter(path, sec_schema.arrow_schema(table), compression='snappy') as w:
        for part in parts:
            w.write_table(part, row_group_size=ROW_GROUP_ROWS)
    meta = pq.ParquetFile(path).metadata
    return meta.num_rows, meta.num_row_groups, meta.created_by


def main():
    data_dir, out_dir, record_path = sys.argv[1:4]
    pa.set_cpu_count(4); pa.set_io_thread_count(2)
    os.makedirs(out_dir, exist_ok=True)
    for t in sec_schema.ORDER:
        assert not os.path.exists(f'{out_dir}/{t}.parquet'), f'{out_dir}/{t}.parquet exists'
    assert not os.path.exists(record_path) and not os.path.exists(f'{out_dir}/MANIFEST.json')
    found = sorted(os.path.basename(d) for d in glob.glob(f'{data_dir}/20[0-9][0-9]q[1-4]') if os.path.isdir(d))
    assert found == QUARTERS, found
    t0 = time.time()
    record = {'argv': sys.argv, 'start_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime(t0)),
              'python': platform.python_version(), 'pyarrow': pa.__version__, 'source': data_dir,
              'rules': __doc__.split('Cleaning rules')[1].split('Output:')[0].strip(), 'files': {}, 'tables': {}}
    manifest = {'format': 'gendb.sec-edgar.canonical.v1', 'scale': 'SF3 (2022q1-2024q4)', 'tables': {}}
    for table in sec_schema.ORDER:
        s = time.time()
        parts = []
        for q in QUARTERS:
            path = f'{data_dir}/{q}/{table}.txt'
            strings, rejected = read_file(path, table)
            lines = data_lines(path)
            if strings.num_rows + len(rejected) != lines:
                raise SystemExit(f'{path}: {strings.num_rows} rows + {len(rejected)} rejected != {lines} data lines')
            data = typed(strings, table, path)
            entry = {'data_lines': lines, 'rejected_lines': len(rejected), 'rows': data.num_rows}
            if table == 'num':
                valued = data.filter(pc.is_valid(data['value']))
                entry['null_value_dropped'] = data.num_rows - valued.num_rows
                data = valued
            entry['kept'] = data.num_rows
            if rejected:
                entry['rejected'] = rejected
            record['files'][f'{q}/{table}.txt'] = entry
            parts.append(data)
            log(table, q, {k: v for k, v in entry.items() if k != 'rejected'})
        rec = {}
        if table == 'tag':
            kept, rec['dedup'] = dedup_tag(parts)
            parts = [kept]
        whole = pa.concat_tables(parts)
        rec['columns'] = column_facts(table, whole)
        del whole
        out = f'{out_dir}/{table}.parquet'
        rows, groups, created_by = write_parquet(out, table, parts)
        rec.update({'rows': rows, 'row_groups': groups, 'bytes': os.path.getsize(out), 'seconds': round(time.time() - s, 1)})
        record['tables'][table] = rec
        manifest['tables'][table] = {'file': f'{table}.parquet', 'rows': rows, 'bytes': rec['bytes'],
                                     'row_groups': groups, 'created_by': created_by,
                                     'arrow_schema': [[c, str(ARROW_TYPE[ty]), n] for c, ty, n in sec_schema.columns(table)]}
        log(table, {k: v for k, v in rec.items() if k != 'columns'})
        del parts
    record['end_utc'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()); record['seconds'] = round(time.time() - t0, 1)
    manifest['generation'] = os.path.abspath(record_path)
    manifest['schema'] = 'sec_schema.py (columns, types, nullability, keys); schema/*.sql'
    with open(f'{out_dir}/MANIFEST.json', 'x') as f:
        json.dump(manifest, f, indent=1); f.write('\n')
    with open(record_path, 'x') as f:
        json.dump(record, f, indent=1); f.write('\n')
    log('DONE', record['seconds'])


if __name__ == '__main__':
    main()
