"""TPC-H substitution-parameter bindings for GenDB and the baselines (single source).

Implements the qgen rules of TPC-H specification clause 2.4 (2.4.1.3 .. 2.4.22.3) for all 22 queries at SF100:
every parameter is drawn uniformly from the range/list the spec defines, with Python's `random.Random(seed)`
(fixed seeds; qgen's own RNG stream is not reproduced, only its domains). Validation values are the spec's
"Query Validation" values (for Q11 FRACTION = 0.0001/SF, i.e. 0.000001 at SF100).

sf100.json: per template v0 = validation values, v1, v2 = qgen-random (seed VISIBLE_SEED).
sf1.json  : per template v0 at SF1 (the validation values; Q11's FRACTION = 0.0001/SF is 0.0001 there).

`arguments` are the query's positional parameters ($1..$n), as strings, in GenDB binding form; `params` maps the
query's parameter names (the header lines `-- $n name type` of ../queries/<Q>.sql) to the same strings. ARGUMENTS
below forms them from the spec parameters (as param_forms.json describes); the generator refuses unless every form
fills exactly its query's parameters.
Usage: python3 generate_bindings.py   (writes sf100.json and sf1.json next to this script)
"""
import datetime as dt, json, os, random

SF = 100
VISIBLE_SEED = 20261002
HERE = os.path.dirname(os.path.abspath(__file__))
QUERIES = os.path.join(HERE, '..', 'queries')

NATIONS = {'ALGERIA': 'AFRICA', 'ARGENTINA': 'AMERICA', 'BRAZIL': 'AMERICA', 'CANADA': 'AMERICA',
           'EGYPT': 'MIDDLE EAST', 'ETHIOPIA': 'AFRICA', 'FRANCE': 'EUROPE', 'GERMANY': 'EUROPE', 'INDIA': 'ASIA',
           'INDONESIA': 'ASIA', 'IRAN': 'MIDDLE EAST', 'IRAQ': 'MIDDLE EAST', 'JAPAN': 'ASIA', 'JORDAN': 'MIDDLE EAST',
           'KENYA': 'AFRICA', 'MOROCCO': 'AFRICA', 'MOZAMBIQUE': 'AFRICA', 'PERU': 'AMERICA', 'CHINA': 'ASIA',
           'ROMANIA': 'EUROPE', 'SAUDI ARABIA': 'MIDDLE EAST', 'VIETNAM': 'ASIA', 'RUSSIA': 'EUROPE',
           'UNITED KINGDOM': 'EUROPE', 'UNITED STATES': 'AMERICA'}
REGIONS = ['AFRICA', 'AMERICA', 'ASIA', 'EUROPE', 'MIDDLE EAST']
TYPE_S1 = ['STANDARD', 'SMALL', 'MEDIUM', 'LARGE', 'ECONOMY', 'PROMO']
TYPE_S2 = ['ANODIZED', 'BURNISHED', 'PLATED', 'POLISHED', 'BRUSHED']
TYPE_S3 = ['TIN', 'NICKEL', 'BRASS', 'STEEL', 'COPPER']
CONT_S1 = ['SM', 'LG', 'MED', 'JUMBO', 'WRAP']
CONT_S2 = ['CASE', 'BOX', 'BAG', 'JAR', 'PKG', 'PACK', 'CAN', 'DRUM']
SEGMENTS = ['AUTOMOBILE', 'BUILDING', 'FURNITURE', 'MACHINERY', 'HOUSEHOLD']
SHIPMODES = ['REG AIR', 'AIR', 'RAIL', 'SHIP', 'TRUCK', 'MAIL', 'FOB']
Q13_W1 = ['special', 'pending', 'unusual', 'express']
Q13_W2 = ['packages', 'requests', 'accounts', 'deposits']
COLORS = ('almond antique aquamarine azure beige bisque black blanched blue blush brown burlywood burnished '
          'chartreuse chiffon chocolate coral cornflower cornsilk cream cyan dark deep dim dodger drab firebrick '
          'floral forest frosted gainsboro ghost goldenrod green grey honeydew hot indian ivory khaki lace lavender '
          'lawn lemon light lime linen magenta maroon medium metallic midnight mint misty moccasin navajo navy olive '
          'orange orchid pale papaya peach peru pink plum powder puff purple red rose rosy royal saddle salmon sandy '
          'seashell sienna sky slate smoke snow spring steel tan thistle tomato turquoise violet wheat white '
          'yellow').split()
assert len(COLORS) == 92


def month_start(r, first, last):
    """First day of a month drawn uniformly from the inclusive (year, month) range."""
    a, b = first[0] * 12 + first[1] - 1, last[0] * 12 + last[1] - 1
    m = r.randint(a, b)
    return dt.date(m // 12, m % 12 + 1, 1).isoformat()


def jan1(r):
    return dt.date(r.randint(1993, 1997), 1, 1).isoformat()


def brand(r):
    return f'Brand#{r.randint(1, 5)}{r.randint(1, 5)}'


# Clause 2.4.N.3: random draw per query.
RANDOM = {
    1: lambda r: {'DELTA': r.randint(60, 120)},
    2: lambda r: {'SIZE': r.randint(1, 50), 'TYPE': r.choice(TYPE_S3), 'REGION': r.choice(REGIONS)},
    3: lambda r: {'SEGMENT': r.choice(SEGMENTS), 'DATE': dt.date(1995, 3, r.randint(1, 31)).isoformat()},
    4: lambda r: {'DATE': month_start(r, (1993, 1), (1997, 10))},
    5: lambda r: {'REGION': r.choice(REGIONS), 'DATE': jan1(r)},
    6: lambda r: {'DATE': jan1(r), 'DISCOUNT': f'0.0{r.randint(2, 9)}', 'QUANTITY': r.randint(24, 25)},
    7: lambda r: dict(zip(['NATION1', 'NATION2'], r.sample(sorted(NATIONS), 2))),
    8: lambda r: (lambda n: {'NATION': n, 'REGION': NATIONS[n],
                             'TYPE': f'{r.choice(TYPE_S1)} {r.choice(TYPE_S2)} {r.choice(TYPE_S3)}'})(r.choice(sorted(NATIONS))),
    9: lambda r: {'COLOR': r.choice(COLORS)},
    10: lambda r: {'DATE': month_start(r, (1993, 2), (1995, 1))},
    11: lambda r: {'NATION': r.choice(sorted(NATIONS)), 'FRACTION': '0.0001/SF'},
    12: lambda r: dict(zip(['SHIPMODE1', 'SHIPMODE2'], r.sample(SHIPMODES, 2)), DATE=jan1(r)),
    13: lambda r: {'WORD1': r.choice(Q13_W1), 'WORD2': r.choice(Q13_W2)},
    14: lambda r: {'DATE': month_start(r, (1993, 1), (1997, 12))},
    15: lambda r: {'DATE': month_start(r, (1993, 1), (1997, 10))},
    16: lambda r: {'BRAND': brand(r), 'TYPE': f'{r.choice(TYPE_S1)} {r.choice(TYPE_S2)}',
                   **{f'SIZE{i + 1}': s for i, s in enumerate(r.sample(range(1, 51), 8))}},
    17: lambda r: {'BRAND': brand(r), 'CONTAINER': f'{r.choice(CONT_S1)} {r.choice(CONT_S2)}'},
    18: lambda r: {'QUANTITY': r.randint(312, 315)},
    19: lambda r: {'QUANTITY1': r.randint(1, 10), 'QUANTITY2': r.randint(10, 20), 'QUANTITY3': r.randint(20, 30),
                   'BRAND1': brand(r), 'BRAND2': brand(r), 'BRAND3': brand(r)},
    20: lambda r: {'COLOR': r.choice(COLORS), 'DATE': jan1(r), 'NATION': r.choice(sorted(NATIONS))},
    21: lambda r: {'NATION': r.choice(sorted(NATIONS))},
    22: lambda r: {f'I{i + 1}': str(c) for i, c in enumerate(r.sample(range(10, 35), 7))},
}

# Clause 2.4.N.3 "Query Validation" values.
VALIDATION = {
    1: {'DELTA': 90}, 2: {'SIZE': 15, 'TYPE': 'BRASS', 'REGION': 'EUROPE'},
    3: {'SEGMENT': 'BUILDING', 'DATE': '1995-03-15'}, 4: {'DATE': '1993-07-01'},
    5: {'REGION': 'ASIA', 'DATE': '1994-01-01'}, 6: {'DATE': '1994-01-01', 'DISCOUNT': '0.06', 'QUANTITY': 24},
    7: {'NATION1': 'FRANCE', 'NATION2': 'GERMANY'},
    8: {'NATION': 'BRAZIL', 'REGION': 'AMERICA', 'TYPE': 'ECONOMY ANODIZED STEEL'}, 9: {'COLOR': 'green'},
    10: {'DATE': '1993-10-01'}, 11: {'NATION': 'GERMANY', 'FRACTION': '0.0001/SF'},
    12: {'SHIPMODE1': 'MAIL', 'SHIPMODE2': 'SHIP', 'DATE': '1994-01-01'}, 13: {'WORD1': 'special', 'WORD2': 'requests'},
    14: {'DATE': '1995-09-01'}, 15: {'DATE': '1996-01-01'},
    16: {'BRAND': 'Brand#45', 'TYPE': 'MEDIUM POLISHED',
         **{f'SIZE{i + 1}': s for i, s in enumerate([49, 14, 23, 45, 19, 3, 36, 9])}},
    17: {'BRAND': 'Brand#23', 'CONTAINER': 'MED BOX'}, 18: {'QUANTITY': 300},
    19: {'QUANTITY1': 1, 'QUANTITY2': 10, 'QUANTITY3': 20, 'BRAND1': 'Brand#12', 'BRAND2': 'Brand#23', 'BRAND3': 'Brand#34'},
    20: {'COLOR': 'forest', 'DATE': '1994-01-01', 'NATION': 'CANADA'}, 21: {'NATION': 'SAUDI ARABIA'},
    22: {f'I{i + 1}': c for i, c in enumerate(['13', '31', '23', '29', '30', '18', '17'])},
}


def q1_date(p):
    return (dt.date(1998, 12, 1) - dt.timedelta(days=p['DELTA'])).isoformat()


def fraction(p):
    return f'{0.0001 / SF:.10f}'


# Spec params -> the query's arguments ($1..$n), in the slot order of the query files' headers (checked by
# check_against_queries).
ARGUMENTS = {
    1: lambda p: [q1_date(p)],
    2: lambda p: [str(p['SIZE']), '%' + p['TYPE'], p['REGION']],
    3: lambda p: [p['SEGMENT'], p['DATE']],
    4: lambda p: [p['DATE']],
    5: lambda p: [p['REGION'], p['DATE']],
    6: lambda p: [p['DATE'], p['DISCOUNT'], str(p['QUANTITY'])],
    7: lambda p: [p['NATION1'], p['NATION2']],
    8: lambda p: [p['NATION'], p['REGION'], p['TYPE']],
    9: lambda p: ['%' + p['COLOR'] + '%'],
    10: lambda p: [p['DATE']],
    11: lambda p: [p['NATION'], fraction(p)],
    12: lambda p: [p['SHIPMODE1'], p['SHIPMODE2'], p['DATE']],
    13: lambda p: [f"%{p['WORD1']}%{p['WORD2']}%"],
    14: lambda p: [p['DATE']],
    15: lambda p: [p['DATE']],
    16: lambda p: [p['BRAND'], p['TYPE'] + '%'] + [str(p[f'SIZE{i}']) for i in range(1, 9)],
    17: lambda p: [p['BRAND'], p['CONTAINER']],
    18: lambda p: [str(p['QUANTITY'])],
    19: lambda p: [p['BRAND1'], str(p['QUANTITY1']), p['BRAND2'], str(p['QUANTITY2']), p['BRAND3'], str(p['QUANTITY3'])],
    20: lambda p: [p['COLOR'] + '%', p['DATE'], p['NATION']],
    21: lambda p: [p['NATION']],
    22: lambda p: [p[f'I{i}'] for i in range(1, 8)],
}


def load_queries():
    """The 22 queries' parameter names in slot order, from the header lines `-- $n name type` of ../queries/<Q>.sql."""
    names = {}
    for q in range(1, 23):
        key = f'Q{q:02d}'
        header = []
        for line in open(os.path.join(QUERIES, f'{key}.sql')):
            if not line.startswith('-- $'):
                break
            index, name = line[4:].split()[:2]
            if int(index) != len(header) + 1:
                raise SystemExit(f'{key}.sql: parameter ${index} out of order')
            header.append(name)
        names[key] = header
    return names


def check_against_queries(names):
    """Every ARGUMENTS form must fill exactly its query's parameters."""
    for q in range(1, 23):
        args = ARGUMENTS[q](VALIDATION[q])
        if len(args) != len(names[f'Q{q:02d}']):
            raise SystemExit(f'Q{q:02d}: {len(args)} arguments for the parameters {names[f"Q{q:02d}"]}')


def build():
    names = load_queries(); check_against_queries(names); args = ARGUMENTS
    rv = random.Random(VISIBLE_SEED)
    visible = {}
    for q in range(1, 23):
        key = f'Q{q:02d}'
        vis = [('validation', VALIDATION[q])]
        while len(vis) < 3:
            p = RANDOM[q](rv)
            if all(args[q](p) != args[q](o) for _, o in vis):
                vis.append(('qgen-random', p))
        visible[key] = [{'binding_id': f'v{i}', 'source': s, 'spec_params': p, 'arguments': args[q](p)}
                        for i, (s, p) in enumerate(vis)]
        for b in visible[key]:
            b['params'] = dict(zip(names[key], b['arguments']))
    sf1 = {}
    for key, bindings in visible.items():
        v0 = json.loads(json.dumps(bindings[0]))
        if key == 'Q11':
            v0['arguments'][1] = v0['params']['fraction'] = f'{0.0001 / 1:.10f}'
        sf1[key] = [v0]
    for name, scale, queries in (('sf100', SF, visible), ('sf1', 1, sf1)):
        with open(os.path.join(HERE, f'{name}.json'), 'w') as f:
            json.dump({'schema': 'gendb.tpch.bindings.v1', 'kind': 'visible', 'seed': VISIBLE_SEED, 'scale_factor': scale,
                       'generator': 'bindings/generate_bindings.py', 'templates': 'queries/', 'queries': queries}, f, indent=1)
            f.write('\n')


if __name__ == '__main__':
    build()
