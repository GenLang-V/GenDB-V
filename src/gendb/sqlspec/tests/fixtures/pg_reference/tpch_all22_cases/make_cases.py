#!/usr/bin/env python3
"""Emit one small PostgreSQL reference fixture per TPC-H query (qNN.json) from ../tpch_all22.json.

The shared fixture is too large for a naive evaluator that forms the full FROM product before filtering
(Q9 alone would be ~5e8 rows). Each query instead gets its own database: the rows listed in SPEC,
closed under every foreign key of src/gendb/fixtures/tpch-spec/schema.sql plus the undeclared nation -> region
key (the closure adds parent rows the query may not need; they are counted). SQL texts stay the
unchanged corpus texts; the case entry (order keys, limit) is copied from the shared fixture and only
the note is replaced. o_totalprice keeps the shared fixture's value (only Q18 reads it, and Q18
keeps both of its orders whole).

`WORK` is a conservative static bound on naive evaluation: the product of the FROM tables, times
(1 + work of each subquery) as if every subquery were re-evaluated per product row. Derived
tables and WITH add their own product. It is a test-design bound only, never a language limit.

    python3 make_cases.py          # rewrite qNN.json and print row counts and work bounds
"""

from __future__ import annotations

import json
from math import prod
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = HERE.parent / "tpch_all22.json"

# Per query: selected keys (lineitem (orderkey, linenumber); partsupp (part, supp); others their key)
# and the note describing the new expected answer.
SPEC = {
    1: {"lineitem": [(10, 1), (10, 2), (30, 1), (30, 2), (80, 1), (71, 1)],
        "note": "All four flag groups: (A,F) 30-2, (N,F) 80-1, (N,O) 10-1 and 71-1, (R,F) 30-1. The cut-off DATE - INTERVAL is a timestamp: 10-1 shipped 1998-09-02 is in, 10-2 shipped 1998-09-03 is out. Nonzero taxes on 10-1, 30-1, 30-2; AVG of numeric."},
    2: {"partsupp": [(2, 1), (2, 3), (2, 11), (3, 2)],
        "note": "Correlated scalar MIN subquery. Part 2 (size 15, '%BRASS'): suppliers 1 (FRANCE) and 3 (UNITED KINGDOM) tie at the EUROPE minimum 100.00 and both appear; supplier 11 (PERU, AMERICA) is cheaper at 50.00 but outside EUROPE. Part 3: supplier 2 (GERMANY, 80.00). Suppliers 1 and 3 tie on s_acctbal; n_name breaks it."},
    3: {"lineitem": [(30, 1), (30, 2), (31, 1), (31, 2), (32, 1), (33, 1), (34, 1)],
        "note": "Orders 30 (two lines), 34 and 31 of BUILDING customer 1; 34 and 31 tie on revenue 2000.0000 and are ordered by date. Excluded: line 31-1 shipped exactly 1995-03-15, order 32 dated exactly 1995-03-15, order 33 of an AUTOMOBILE customer."},
    4: {"lineitem": [(40, 1), (40, 2), (41, 1), (42, 1), (42, 2), (43, 1), (44, 1), (100, 1)],
        "note": "Correlated EXISTS. 1-URGENT: orders 40 (dated on the lower bound) and 41; 3-MEDIUM: order 42 with two late lines counts once. Excluded: 43 (commit = receipt), 44 (1993-06-30), 100 (1993-10-01 = upper bound, late line)."},
    5: {"lineitem": [(50, 1), (50, 2), (51, 1), (52, 1)],
        "note": "Six-way join with c_nationkey = s_nationkey. JAPAN 4500 (order 51 dated 1994-12-31), INDIA 2700 (line 50-1). Excluded: line 50-2 (INDIA customer, JAPAN supplier), order 52 (1995-01-01)."},
    6: {"lineitem": [(60, 1), (60, 2), (60, 3), (60, 4), (61, 1), (61, 2)],
        "note": "Lines 60-1 (discount 0.06), 60-3 (discount 0.07 = upper bound, quantity 23), 61-1 (discount 0.05 = lower bound, shipped 1994-12-31): 60 + 161 + 100. Excluded: 60-2 (quantity 24), 60-4 (discount 0.08), 61-2 (shipped 1995-01-01)."},
    7: {"lineitem": [(70, 1), (71, 1), (72, 1), (72, 2), (73, 1)],
        "note": "EXTRACT(YEAR) in a derived table, both nation directions. (FRANCE, GERMANY) 1995 = 900 and 1996 = 2000 (shipped on the upper bound 1996-12-31); (GERMANY, FRANCE) 1995 = 500. Excluded: 72-2 (FRANCE to FRANCE), 73-1 (shipped 1997)."},
    8: {"lineitem": [(80, 1), (80, 2), (80, 3), (81, 1), (82, 1), (83, 1)],
        "note": "CASE in SUM divided by SUM. 1995: BRAZIL supplier 6 has 1000 of 4000 = 0.25; 1996: only a FRANCE supplier, 0 / 1800. Excluded: 80-3 (other part type), 82 (FRANCE customer, EUROPE), 83 (1997)."},
    9: {"lineitem": [(90, 1), (91, 1), (91, 2), (200, 1), (200, 2), (200, 3)],
        "note": "LIKE '%green%' (parts 5 and 6), join to partsupp on both keys, profit = revenue - supplycost * quantity. CANADA 1994 = 7050 (includes 200-3 shipped in 1995: o_year is the order year); FRANCE 1996 = 110 and 1995 = 600; GERMANY 1996 = 40. No non-green part (kept out to bound the 6-way product)."},
    10: {"lineitem": [(100, 1), (100, 2), (101, 1), (102, 1), (103, 1)],
         "note": "Customer 7 (BRAZIL) 1900 from order 102; customer 5 (FRANCE) 1400 from orders 100 (1993-10-01, lower bound) and 101 (1993-12-31). Excluded: 100-2 (return flag A), order 103 (1994-01-01)."},
    11: {"partsupp": [(2, 2), (3, 2), (3, 12), (8, 2), (2, 1)],
         "note": "HAVING against an uncorrelated scalar subquery. GERMANY suppliers 2 and 12; part 3 sums both (40000 + 9000). Total 199001.00, threshold 19.90...; part 8 (1.00) is below it. Supplier 1 (FRANCE) is filtered out."},
    12: {"lineitem": [(120, 1), (120, 2), (121, 1), (121, 2), (121, 3)],
         "note": "SUM of CASE. MAIL: one high (order 120, 1-URGENT) and one low (order 121); SHIP: zero high, one low (121-2, received 1994-12-31). Excluded: 120-2 (commit after receipt), 121-3 (shipped after commit)."},
    13: {"orders": [30, 31, 51, 52, 131, 180, 170], "customer": [10],
         "note": "LEFT OUTER JOIN with NOT LIKE in ON, COUNT of a nullable column. Customers 1 and 4 have 2 orders each; customer 8 has 1 (order 131 matches '%special%requests%'); customer 9's only order 170 is special and customer 10 has none, so both count 0. Answer (2,2), (0,2), (1,1): the custdist tie is broken by c_count DESC."},
    14: {"lineitem": [(140, 1), (140, 2), (140, 3)],
         "note": "LIKE 'PROMO%' inside CASE, 100.00 * SUM / SUM: 100 * 900 / 2900 (140-1 shipped on the lower bound, 140-2 on 1995-09-30). Excluded: 140-3 (1995-10-01)."},
    15: {"lineitem": [(150, 1), (150, 2), (150, 3), (150, 4), (150, 5)],
         "note": "WITH referenced twice, scalar MAX subquery. Suppliers 4 (one line) and 5 (two lines) tie at the maximum 900.0000 and both appear; supplier 6 has 300. Excluded: 150-5 shipped 1996-04-01, which would otherwise be the maximum."},
    16: {"partsupp": [(8, 1), (8, 2), (8, 11), (9, 1), (10, 1), (11, 3), (11, 4), (7, 5)],
         "note": "COUNT(DISTINCT), NOT LIKE, IN list, NOT IN subquery. Part 8 counts 2 (supplier 11 has the 'Customer...Complaints' comment), part 11 counts 2, part 7 counts 1. Excluded: part 9 (Brand#45), part 10 (MEDIUM POLISHED)."},
    17: {"lineitem": [(170, 1), (170, 2), (170, 3), (170, 4), (170, 5), (190, 3)],
         "note": "Correlated scalar AVG subquery and / 7.0. Part 12's quantities are 1, 10, 20, 30, 40 (average 20.2, threshold 4.04): only 170-1 qualifies, 100.00 / 7.0. Line 190-3 (part 14, Brand#34) is excluded by brand."},
    18: {"lineitem": [(180, n) for n in range(1, 8)] + [(181, n) for n in range(1, 7)],
         "note": "IN subquery with GROUP BY + HAVING. Order 180 totals quantity 301 (in); order 181 totals exactly 300 (out, strict >)."},
    19: {"lineitem": [(170, 1), (170, 2), (170, 3), (190, 1), (190, 2), (190, 3), (190, 4)],
         "note": "OR of three conjunctions with IN lists and BETWEEN. Branch 1: 190-1 (450); branch 2: 170-2, 170-3 (quantities 10 and 20 on the bounds; 950 + 2000); branch 3: 190-3 (2500). Excluded: 170-1 (quantity 1, TRUCK), 190-2 (TRUCK), 190-4 (quantity 31)."},
    20: {"lineitem": [(200, 1), (200, 2), (200, 3)],
         "note": "Nested IN subqueries, LIKE 'forest%', correlated scalar SUM. Supplier 7 (CANADA): availqty 100 > 0.5 * 20 (200-3 of 1995 is outside the window); supplier 8 (CANADA): availqty 10 is not > 0.5 * 30."},
    21: {"lineitem": [(210, 1), (210, 2), (210, 3), (211, 1), (211, 2), (212, 1), (212, 2), (213, 1), (213, 2), (214, 1)],
         "note": "EXISTS and NOT EXISTS over lineitem self-joins. Supplier 9 waits 2 (two late lines of order 210, other supplier on time); supplier 10 waits 1 (order 212). Excluded: order 211 (both suppliers late), 213 (status O), 214 (single supplier)."},
    22: {"customer": [3, 10, 11, 12, 13, 14], "orders": [50],
         "note": "SUBSTRING of char(15), IN list, uncorrelated scalar AVG, NOT EXISTS. Average positive balance over the listed codes = 27100 / 5 = 5420 (customers 3, 10, 11, 12, 13). Code 13: customers 10 and 11; code 30: customer 12. Excluded: 13 (100.00), 14 (negative), 3 (has order 50)."},
}

# Conservative naive-work bounds over table row counts n (see module docstring).
WORK = {
    1: lambda n: n["lineitem"],
    2: lambda n: prod(n[t] for t in ("part", "supplier", "partsupp", "nation", "region"))
                 * (1 + prod(n[t] for t in ("partsupp", "supplier", "nation", "region"))),
    3: lambda n: n["customer"] * n["orders"] * n["lineitem"],
    4: lambda n: n["orders"] * (1 + n["lineitem"]),
    5: lambda n: prod(n[t] for t in ("customer", "orders", "lineitem", "supplier", "nation", "region")),
    6: lambda n: n["lineitem"],
    7: lambda n: prod(n[t] for t in ("supplier", "lineitem", "orders", "customer")) * n["nation"] ** 2,
    8: lambda n: prod(n[t] for t in ("part", "supplier", "lineitem", "orders", "customer", "region")) * n["nation"] ** 2,
    9: lambda n: prod(n[t] for t in ("part", "supplier", "lineitem", "partsupp", "orders", "nation")),
    10: lambda n: prod(n[t] for t in ("customer", "orders", "lineitem", "nation")),
    11: lambda n: (p := prod(n[t] for t in ("partsupp", "supplier", "nation"))) * (1 + p),
    12: lambda n: n["orders"] * n["lineitem"],
    13: lambda n: n["customer"] * n["orders"],
    14: lambda n: n["lineitem"] * n["part"],
    15: lambda n: n["lineitem"] + n["supplier"] * n["lineitem"] * (1 + n["lineitem"]),
    16: lambda n: n["partsupp"] * n["part"] * (1 + n["supplier"]),
    17: lambda n: n["lineitem"] * n["part"] * (1 + n["lineitem"]),
    18: lambda n: n["customer"] * n["orders"] * n["lineitem"] * (1 + n["lineitem"]),
    19: lambda n: n["lineitem"] * n["part"],
    20: lambda n: n["supplier"] * n["nation"] * (1 + n["partsupp"] * (1 + n["part"] + n["lineitem"])),
    21: lambda n: prod(n[t] for t in ("supplier", "lineitem", "orders", "nation")) * (1 + 2 * n["lineitem"]),
    22: lambda n: n["customer"] * (1 + n["customer"] + n["orders"]),
}

TABLE_ORDER = ["region", "nation", "supplier", "part", "partsupp", "customer", "orders", "lineitem"]


def closure(base: dict, spec: dict) -> dict:
    """Selected rows plus every parent row their foreign keys reach."""
    rows = {t["name"]: [dict(zip(t["columns"], r)) for r in t["rows"]] for t in base["tables"]}
    by = lambda table, *cols: {tuple(r[c] for c in cols): r for r in rows[table]}
    li, ps = by("lineitem", "l_orderkey", "l_linenumber"), by("partsupp", "ps_partkey", "ps_suppkey")
    keys = {t: set() for t in TABLE_ORDER}
    keys["lineitem"] |= {tuple(k) for k in spec.get("lineitem", [])}
    keys["partsupp"] |= {tuple(k) for k in spec.get("partsupp", [])}
    for t in ("orders", "customer", "supplier", "part", "nation"):
        keys[t] |= {(k,) for k in spec.get(t, [])}
    for k in keys["lineitem"]:
        r = li[k]
        keys["orders"].add((r["l_orderkey"],))
        keys["partsupp"].add((r["l_partkey"], r["l_suppkey"]))
    for k in keys["partsupp"]:
        keys["part"].add((k[0],))
        keys["supplier"].add((k[1],))
    orders, customer, supplier, nation = (by(t, c) for t, c in (
        ("orders", "o_orderkey"), ("customer", "c_custkey"), ("supplier", "s_suppkey"), ("nation", "n_nationkey")))
    for k in keys["orders"]:
        keys["customer"].add((orders[k]["o_custkey"],))
    for k in keys["customer"]:
        keys["nation"].add((customer[k]["c_nationkey"],))
    for k in keys["supplier"]:
        keys["nation"].add((supplier[k]["s_nationkey"],))
    for k in keys["nation"]:
        keys["region"].add((nation[k]["n_regionkey"],))
    return keys


def emit(base: dict, q: int) -> tuple[dict, dict]:
    spec = SPEC[q]
    keys = closure(base, spec)
    key_cols = {"region": ["r_regionkey"], "nation": ["n_nationkey"], "supplier": ["s_suppkey"],
                "part": ["p_partkey"], "partsupp": ["ps_partkey", "ps_suppkey"], "customer": ["c_custkey"],
                "orders": ["o_orderkey"], "lineitem": ["l_orderkey", "l_linenumber"]}
    tables, counts = [], {}
    for t in base["tables"]:
        idx = [t["columns"].index(c) for c in key_cols[t["name"]]]
        sel = [r for r in t["rows"] if tuple(r[i] for i in idx) in keys[t["name"]]]
        counts[t["name"]] = len(sel)
        if sel:
            tables.append({**{k: v for k, v in t.items() if k != "rows"}, "rows": sel})
    tables.sort(key=lambda t: TABLE_ORDER.index(t["name"]))
    case = next(c for c in base["cases"] if c["name"] == f"q{q}")
    case = {**case, "note": spec["note"]}
    fixture = {
        "fixture": f"tpch_all22_q{q:02d}",
        "description": (f"TPC-H Q{q} on its own tiny database: rows of ../tpch_all22.json selected by make_cases.py "
                        f"and closed under the schema's foreign keys and nation -> region. Static naive-work bound "
                        f"(FROM product x subquery re-evaluation): {WORK[q](counts)}."),
        "ddl": base["ddl"],
        "tables": tables,
        "cases": [case],
    }
    return fixture, counts


def dump(fixture: dict) -> str:
    """Stable JSON with one table row per line."""
    out = ["{"]
    for k in ("fixture", "description", "ddl"):
        out.append(f" {json.dumps(k)}: {json.dumps(fixture[k])},")
    out.append(' "tables": [')
    for i, t in enumerate(fixture["tables"]):
        head = {k: v for k, v in t.items() if k != "rows"}
        out.append("  " + json.dumps(head)[:-1] + ', "rows": [')
        out.append(",\n".join("    " + json.dumps(r) for r in t["rows"]))
        out.append("  ]}" + ("," if i + 1 < len(fixture["tables"]) else ""))
    out.append(" ],")
    out.append(' "cases": [\n  ' + ",\n  ".join(json.dumps(c) for c in fixture["cases"]) + "\n ]")
    out.append("}")
    return "\n".join(out) + "\n"


def main() -> None:
    base = json.loads(BASE.read_text())
    print("query " + " ".join(f"{t[:8]:>8}" for t in TABLE_ORDER) + "      work")
    for q in sorted(SPEC):
        fixture, counts = emit(base, q)
        (HERE / f"q{q:02d}.json").write_text(dump(fixture))
        print(f"q{q:02d}   " + " ".join(f"{counts[t]:>8}" for t in TABLE_ORDER) + f" {WORK[q](counts):>9}")


if __name__ == "__main__":
    main()
