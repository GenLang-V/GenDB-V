"""Per-cell baseline times from the timing blocks of run_baselines.py.

For every query, binding and thread count, per engine: the median of the block's 3 hot executions in ms (3 decimals),
or null when the block is missing or failed.
Usage: aggregate.py <out_dir> <bindings.json> <times.json>
"""
import glob
import json
import sys


def main():
    out, bindings_path, times_path = sys.argv[1:4]
    bindings = json.load(open(bindings_path))
    blocks = {}
    for path in glob.glob(f'{out}/blocks/*/*/*.json'):
        r = json.load(open(path)); blocks[(r['engine'], r['query'], r['binding_id'], r['threads'])] = r
    times = {}
    for q, bs in sorted(bindings['queries'].items()):
        if not any(k[1] == q for k in blocks):
            continue
        for b in bs:
            for t in (1, 32, 64):
                cell = {}
                for e in ('duckdb', 'umbra'):
                    r = blocks.get((e, q, b['binding_id'], t))
                    cell[f'{e}_ms'] = round(r['run']['median_ns'] / 1e6, 3) if r and r.get('ok') else None
                times.setdefault(q, {}).setdefault(b['binding_id'], {})[str(t)] = cell
    with open(times_path, 'w') as f:
        json.dump(times, f, indent=1); f.write('\n')
    print(len(times), 'queries')


if __name__ == '__main__':
    main()
