// Example page data: the one example query (results/example-readings-count), from its SQL to its verified answer.
// Part 1: the SQL template with its table and data, the typed AST, the SQLSpec tree and its semantics, operator by
// operator, and the semantics worked on the data at the README's binding. Part 2: the agent's code (code/mod.rs, every
// line with its role: executable, proof, fixed target) and the proof chain from the code to the fixed target.
// Part 3: the answer.
// Every value is read from the repository and checked: the SQL, the schema and its CHECK, the rows (data/make_data.py
// and the README), the SQLSpec tree (spec.rs, node for node), the answer (computed here from the rows, equal to the
// README's), every code line (the file Verus checked, and the fixed contract against GenDB's obligation in claim.rs),
// and the contract or definition behind each formula. With --paper, the names and formulas of the paper's figures.
// Formulas use the code's names: p is the value of $1, xs the stored rows, values the stored values.
const EX = "results/example-readings-count";
const CRATE = `${EX}/crates/example-readings-count/src`;
const README = "README.md", GUIDE = "GUIDE.md", EX_README = `${EX}/README.md`;
const SQL = `${EX}/query.sql`, SCHEMA = `${EX}/schema.sql`, DATA = `${EX}/data/make_data.py`, SPEC = `${EX}/spec.rs`;
const CODE = `${EX}/code/mod.rs`, NF = `${EX}/code/normal_form.rs`;
const CLAIM = "src/gendb/verification/src/obligations/claim.rs";
const ENTRY = `${CRATE}/gendb_entry.rs`, LINK = `${CRATE}/link/query.rs`, STORE = `${CRATE}/stores/flat_readings/interface/mod.rs`;
const EVAL = `${CRATE}/spec/eval.rs`, RELATION = `${CRATE}/spec/relation.rs`;
const FIG1 = "figures/sqlspec-example.tex", FIG2 = "figures/proof-example-figure.tex";
const SEC3 = "sections/03-sqlspec.tex", SEC4 = "sections/04-obligations.tex";
const INT8_MIN = -(2n ** 63n), INT8_MAX = 2n ** 63n - 1n;

export default function build(ctx) {
  const c = ctx.claim;

  // ---------------------------------------------------------------- the query, the table, the data, the binding
  const sql = ctx.read(SQL).trim();
  const clauses = [
    { level: "agg", text: "SELECT COUNT(*) AS n" },
    { level: "table", text: "FROM readings" },
    { level: "filter", text: "WHERE value > $1;" },
  ];
  ctx.check(clauses.map((x) => x.text).join(" ") === sql, `the SQL clauses shown are ${SQL}: ${sql}`);
  ctx.quotePaper("SELECT COUNT(*) AS n FROM readings WHERE value > \\$1;", SEC3);

  const schema = ctx.read(SCHEMA);
  const table = { name: "readings", column: "value", type: "bigint NOT NULL", check: "CHECK (value >= 0)" };
  ctx.check(/CREATE TABLE readings \(\s*value bigint NOT NULL\s*\);/.test(schema), `${SCHEMA}: one table readings, one column value bigint NOT NULL`);
  ctx.quote(`ADD CONSTRAINT value_nonnegative ${table.check};`, SCHEMA);
  const checkMin = Number(/CHECK \(value >= (\d+)\)/.exec(schema)[1]);

  const rowsText = /^ROWS = \[([\d, ]+)\]/m.exec(ctx.read(DATA));
  ctx.check(rowsText, `${DATA}: ROWS`);
  const rows = rowsText ? rowsText[1].split(",").map((v) => Number(v.trim())) : [];
  ctx.quote(`4 rows, \`value\` = ${rows.join(", ")}, in this order`, EX_README);
  ctx.check(rows.length === 4 && rows.every((v) => Number.isInteger(v) && v >= checkMin), `the rows ${rows} meet ${table.check}`);
  ctx.quotePaper(`$D[0]=[[${rows.join("],[")}]]$`, FIG1);

  const run = /at `\$1 = (\d+)` the query returns `\[\[(\d+)\]\]`/.exec(ctx.read(EX_README));
  ctx.check(run, `${EX_README}: the binding and the answer`);
  const p = run ? Number(run[1]) : 0;
  const kept = rows.filter((v) => v > p), dropped = rows.filter((v) => !(v > p));
  const count = kept.length;
  ctx.check(run && Number(run[2]) === count && BigInt(count) <= INT8_MAX, `the answer computed from the rows, [[${count}]], is the README's [[${run && run[2]}]]`);
  ctx.quotePaper(`\\textbf{Example} ($k=${p}$)`, FIG1);
  ctx.quotePaper(`Output: $[[${count}]]$`, FIG1);
  ctx.quotePaper(`the filter keeps $F_${p}(D)=[[${kept.join("],\\allowbreak[")}]]$ and the required output is $[[${count}]]$`, SEC3);

  // ---------------------------------------------------------------- the parameter's type and domain (spec.rs)
  const spec = ctx.read(SPEC);
  ctx.quote("/// - slot 0: `$1` bigint in [-9223372036854775808, 9223372036854775807]", SPEC);
  ctx.check(BigInt("-9223372036854775808") === INT8_MIN && BigInt("9223372036854775807") === INT8_MAX, "the domain of $1 is [-2^63, 2^63 - 1]");
  ctx.quotePaper("$k\\in[-2^{63},2^{63}-1]$", FIG1);

  // ---------------------------------------------------------------- the SQLSpec tree (spec.rs, node for node)
  const defs = new Map([...spec.matchAll(/^\s*let (n\d+) = (.+);$/gm)].map((m) => [m[1], m[2]]));
  const expand = (name, depth = 0) => (depth > 20 ? "?" : defs.get(name).replace(/\bn\d+\b/g, (r) => expand(r, depth + 1)));
  const last = [...defs.keys()].pop();
  const tree = defs.size ? expand(last) : "";
  const TREE = "OrderedQuery { body: Query::Aggregate { aggs: seq![Agg::CountStar], input: Box::new(Query::Filter { pred: Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(0), b: Expr::Lit(ps[0]) }, input: Box::new(Query::Table(0)) }) }, keys: seq![], limit: None, offset: 0 }";
  ctx.check(tree === TREE, `${SPEC}: query_spec_at(ps) is ${TREE} (found ${tree})`);
  // ps[0] at the binding of $1 = p is the int8 literal p (normal_form.rs), shown as Lit(p)
  ctx.quote("pub open spec fn binding(p: int) -> Seq<Literal> { seq![Literal::Int { v: p, kind: IntKind::Int8 }] }", NF);
  ctx.quote("pred: Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(0), b: Expr::Lit(Literal::Int { v: p, kind: IntKind::Int8 }) },", NF);

  // ---------------------------------------------------------------- the four views, operator by operator
  const levels = [
    {
      id: "agg",
      ast: { op: "Aggregate", arg: "COUNT(*)" },
      spec: { ctor: "Query::Aggregate", arg: "aggs: [Agg::CountStar]" },
      sem: "[[|F|]]",
      rows: [count],
    },
    {
      id: "filter",
      ast: { op: "Filter", arg: "value > $1" },
      spec: { ctor: "Query::Filter", arg: "Cmp(Gt, Col(0), Lit(p))" },
      sem: "F = [r ∈ R | value(r) > p]",
      rows: kept, dropped,
    },
    {
      id: "table",
      ast: { op: "Table", arg: "readings" },
      spec: { ctor: "Query::Table(0)" },
      sem: "R = db[0]",
      rows,
    },
  ];
  for (const l of levels) {
    ctx.check(sql.includes(l.ast.arg), `the AST node ${l.ast.op}: ${l.ast.arg} is in the SQL`);
    ctx.check(TREE.includes(l.spec.ctor), `${l.spec.ctor} is in the tree`);
  }
  ctx.check(TREE.includes("aggs: seq![Agg::CountStar]") && TREE.includes("Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(0), b: Expr::Lit(ps[0]) }"), "the node arguments are the tree's");
  for (const t of ["1. SQL template", "2. Typed AST", "3. SQLSpec syntax", "4. Semantics", "Aggregate: COUNT(*)", "Filter: value $>\\$1$", "Table: readings",
    "Query::Aggregate", "aggs: [Agg::CountStar]", "Query::Filter", "pred: Col(0) $>$ Lit(k)", "Query::Table(0)",
    "$\\mathsf{count}(F_k(D))=[[|F_k(D)|]]$", "$F_k(D)=[\\,r\\in R\\mid x(r)>k\\,]$", "$R=\\mathsf{table}_0(D)=D[0]$"]) ctx.quotePaper(t, FIG1);
  // the semantics: SQLSpec's own definitions of the three nodes
  ctx.quote("Query::Table(t) => if t < db.tables.len() { Ok(db.tables[t as int]) }", EVAL);
  ctx.quote("Ok(truths) => Ok(keep_true(rows, truths)),", EVAL);
  ctx.quote("if truths.last() is True { init.push(rows.last()) } else { init }", RELATION);
  ctx.quote("Ok(row) => Ok(seq![row]),", EVAL);
  ctx.quote("Agg::CountStar => int_result(IntKind::Int8, vs.len() as int),", RELATION);

  const types = [`value: ${table.type}`, "$1: bigint"];
  ctx.check(schema.includes("value bigint NOT NULL") && spec.includes("`$1` bigint"), "the AST types are the schema's and spec.rs's");

  // ---------------------------------------------------------------- the code: code/mod.rs, the file Verus checked
  const code = ctx.read(CODE);
  ctx.check(code === ctx.read(`${CRATE}/agent/mod.rs`), `${CODE} is the verified crate's src/agent/mod.rs`);
  const lines = code.replace(/\n$/, "").split("\n");
  const N = lines.length;
  /** The one line (1-based) in [from, to] that contains `text` (or meets the test). */
  const at = (text, from = 1, to = N) => {
    const test = typeof text === "function" ? text : (l) => l.includes(text);
    const hits = [];
    for (let i = from; i <= to; i++) if (test(lines[i - 1])) hits.push(i);
    ctx.check(hits.length === 1, `one line of ${CODE} ${typeof text === "function" ? "meets the test" : `contains "${text}"`} (found ${hits.length})`);
    return hits[0] || 1;
  };
  /** The line that closes the brace block opened on line `start` (braces outside line comments). */
  const blockEnd = (start) => {
    let depth = 0, opened = false;
    for (let i = start; i <= N; i++) {
      for (const ch of lines[i - 1].replace(/\/\/.*$/, "")) {
        if (ch === "{") { depth++; opened = true; } else if (ch === "}") depth--;
      }
      if (opened && depth === 0) return i;
    }
    ctx.check(false, `${CODE}: the block of line ${start} closes`);
    return start;
  };
  const range = (a, b) => Array.from({ length: b - a + 1 }, (_, i) => a + i);

  // roles: the fixed target (the signature and contract GenDB fixes), proof (ghost values, proof blocks, the loop's
  // invariant and decreases clause), comments, and executable code
  const fnStart = at("pub fn query(");
  const bodyOpen = at((l) => l.trim() === "{", fnStart, fnStart + 12);
  const fnEnd = blockEnd(bodyOpen);
  const proofBlocks = lines.map((l, i) => i + 1).filter((n) => /\bproof \{/.test(lines[n - 1])).map((n) => [n, blockEnd(n)]);
  const blockOf = (n) => proofBlocks.find(([a, b]) => a <= n && n <= b) || [n, n];
  const inv = at((l) => l.trim() === "invariant"), dec = at("decreases n - i,");
  const kind = new Map();
  for (let n = 1; n <= N; n++) {
    const t = lines[n - 1].trim();
    if (!t) kind.set(n, "blank");
    else if (t.startsWith("//")) kind.set(n, "comment");
    else if (fnStart <= n && n < bodyOpen) kind.set(n, "fixed");
    else if (proofBlocks.some(([a, b]) => a <= n && n <= b) || t.startsWith("let ghost ") || (inv <= n && n <= dec)) kind.set(n, "proof");
    else kind.set(n, "exec");
  }

  // the fixed target is GenDB's: the signature and the clauses of the query obligation (claim.rs, entry v5, whose
  // bound_db states the declared constraints, as this crate's gendb_entry.rs)
  const claimSrc = ctx.read(CLAIM);
  const item = /const QUERY_V5: AgentItem = AgentItem \{([\s\S]*?)\n\};/.exec(claimSrc);
  ctx.check(item, `${CLAIM}: QUERY_V5`);
  const sig = item && /signature: "([^"]*)"/.exec(item[1]);
  const obl = item && /obligation: "((?:[^"\\]|\\[\s\S])*)"/.exec(item[1]);
  ctx.check(sig && obl, `${CLAIM}: the signature and obligation of QUERY_V5`);
  const signature = sig ? sig[1] : "";
  const obligation = obl ? obl[1].replace(/\\\n\s*/g, "") : "";
  ctx.check(lines[fnStart - 1].trim() === signature, `the signature of query is GenDB's (${CLAIM})`);
  ctx.quote("&&& constraints_hold(declared_db(db))", ENTRY);
  const reqAt = at((l) => l.trim() === "requires", fnStart, bodyOpen), ensAt = at((l) => l.trim() === "ensures", fnStart, bodyOpen);
  for (let n = reqAt + 1; n < bodyOpen; n++) {
    if (n === ensAt) continue;
    const clause = lines[n - 1].trim().replace(/,$/, "").replace(/^crate::query::/, "");
    ctx.check(obligation.includes(clause), `the fixed clause "${clause}" is GenDB's (${CLAIM})`);
  }
  ctx.check(lines.slice(ensAt, bodyOpen - 1).map((l) => l.trim()).join(" ") === "answer_meets(old(stores)@, params@, r),", "query ensures exactly answer_meets");
  ctx.check(obligation.includes("Its ensures must imply gendb_entry::answer_meets(old(stores)@, params@, r)"), `${CLAIM}: the ensures answer_meets is GenDB's`);

  // the tagged regions, each tied to a node of the proof chain
  const stepBlock = blockOf(at("lemma_range_step(")), bridgeBlock = blockOf(at("lemma_body("));
  const regions = [
    { id: "target", tag: "Fixed target", node: "target", lines: range(fnStart, bodyOpen - 1) },
    { id: "reader", tag: "Reader", node: "reader", lines: [at("let n = stored_rows("), at("let values = read_value(")] },
    { id: "start", node: "invariant", lines: [at("lemma_empty(")] },
    { id: "invariant", tag: "Invariant", node: "invariant", lines: range(inv, dec - 1) },
    { id: "decreases", tag: "Termination", node: "invariant", lines: [dec] },
    { id: "step", tag: "Step lemma", node: "step", lines: range(...stepBlock) },
    { id: "loop", tag: "Loop", node: "step", lines: range(at("if values[i] > p {"), at("i = i + 1;")) },
    { id: "exit", node: "invariant", lines: [at("lemma_full_range(")] },
    { id: "bridge", tag: "Bridge", node: "bridge", lines: range(...bridgeBlock) },
  ];
  for (const r of regions) {
    const roles = new Set(r.lines.map((n) => kind.get(n)).filter((k) => k !== "comment"));
    const want = ["reader", "loop"].includes(r.id) ? "exec" : r.id === "target" ? "fixed" : "proof";
    ctx.check(roles.size === 1 && roles.has(want), `the ${r.id} lines are ${want} code (found ${[...roles]})`);
  }

  // the key lines: the contract, the reader, the loop with its invariant and step lemma, the bridge; the rest elided
  const whileAt = at("while i < n");
  const forallAt = at("assert forall|db: Database|");
  const key = new Set([
    ...range(fnStart, bodyOpen),
    at("let p = params.p0;"), at("let ghost g = count_spec(p as int);"), at("let ghost xs = rels[0];"),
    ...regions.find((r) => r.id === "reader").lines,
    at("let mut count: usize = 0;"), at("let mut i: usize = 0;"), at("lemma_empty("),
    whileAt, inv, at("count == gcount(g, xs.subrange(0, i as int), Seq::<Val>::empty()),"), dec, dec + 1,
    stepBlock[0], at("lemma_range_step("), stepBlock[1],
    ...range(at("if values[i] > p {"), at("i = i + 1;")), blockEnd(dec + 1),
    at("lemma_full_range("),
    bridgeBlock[0], forallAt, forallAt + 1, at("lemma_represents_determines("), at("lemma_body("), blockEnd(forallAt + 1), bridgeBlock[1],
    at((l) => l.trim() === "r"), fnEnd,
  ]);
  ctx.check(lines[dec].trim() === "{" && blockEnd(dec + 1) < at("lemma_full_range("), "the loop body opens after decreases and closes before lemma_full_range");

  const codeLines = lines.map((text, i) => ({ n: i + 1, text, kind: kind.get(i + 1) }));
  // every line on the page is the file's line at that number
  ctx.check(codeLines.every((l) => l.text === lines[l.n - 1]) && codeLines.length === N, `the code shown is ${CODE}, line for line`);

  // ---------------------------------------------------------------- the proof chain, from the code to the fixed target
  // Each formula is the contract or definition it names, in the code's names (xs[..i]: the first i stored rows).
  const chain = [
    { id: "reader", kind: "exec", role: "Reader", name: "read_value", formula: ["xs[j][0] = values[j]"],
      grounds: [[STORE, "forall|j: int| 0 <= j < hi - lo ==> #[trigger] rels[0][lo as int + j][0] == (Val::Int(r@[j] as int)),"], [CODE, "let values = read_value(&mut stores.flat_readings, 0, n, Ghost(rels));"], [CODE, "let ghost xs = rels[0];"]],
      paper: [FIG2, "Layer 1: \\texttt{read\\_values(S)}"] },
    { id: "step", kind: "proof", role: "Step lemma", name: "lemma_range_step", formula: ["gcount(g, xs[..i]) + 𝟙[values[i] > p]", "= gcount(g, xs[..i+1])"],
      grounds: [[LINK, "gcount(g, rows.subrange(lo, i + 1), k) == gcount(g, rows.subrange(lo, i), k) + if hit(g, rows[i], k) { 1nat } else { 0nat },"], [CODE, "lemma_range_step(g, xs, 0, i as int, Seq::<Val>::empty(), 0);"], [CODE, "assert(hit(g, xs[i as int], Seq::<Val>::empty()) == (values@[i as int] > p)) by {"], [CODE, "count = count + 1;"]],
      paper: [FIG2, "[Step lemma]"] },
    { id: "invariant", kind: "proof", role: "Invariant", formula: ["count = gcount(g, xs[..i])"], extra: { kw: "decreases", formula: "n − i" },
      grounds: [[CODE, "count == gcount(g, xs.subrange(0, i as int), Seq::<Val>::empty()),"], [CODE, "decreases n - i,"], [CODE, "proof { lemma_empty(g, xs, 0, Seq::<Val>::empty(), 0); }"], [LINK, "gcount(g, rows.subrange(lo, lo), k) == 0,"]],
      paper: [FIG2, "[Termination]"], edge: "i = n" },
    { id: "bridge", kind: "proof", role: "Bridge", name: "lemma_body", formula: ["count = gcount(g, xs) = |F|", "⟹ r ∈ ⟦Q⟧(db)"],
      grounds: [[CODE, "proof { lemma_full_range(xs); }"], [LINK, "ensures rows.subrange(0, rows.len() as int) == rows,"], [NF, "&&& kept.len() == gcount(g, rels[0], Seq::<Val>::empty())"], [NF, "count <= int8_max() ==> eval_query(db, Seq::empty(), body) == Ok::<Relation, SqlError>(seq![seq![Val::Int(count)]])"], [CODE, "lemma_body(db, parts, rels, p as int);"], [CODE, "lemma_outcome_rows(db, oq, seq![seq![Val::Int(count as int)]]);"]],
      paper: [FIG2, "Layer 3: Bridge lemma"] },
    { id: "target", kind: "fixed", role: "Fixed target", name: "answer_meets", formula: ["∀db: bound_db(db) ⟹ r ∈ ⟦Q⟧(db)"],
      grounds: [[ENTRY, "forall|db: Database| #[trigger] bound_db(sv, db) ==> outcome_ok(db, query_spec_at(ps), r)"], [CODE, "answer_meets(old(stores)@, params@, r),"], [GUIDE, "rows that are an allowed answer of the statement's SQLSpec meaning ⟦Q⟧(db)"]],
      paper: [FIG2, "[Fixed target]"] },
  ];
  for (const node of chain) {
    for (const [rel, text] of node.grounds) ctx.quote(text, rel);
    ctx.quotePaper(node.paper[1], node.paper[0]);
    ctx.check(regions.some((r) => r.node === node.id), `the chain node ${node.id} has code`);
    delete node.grounds; delete node.paper;
  }
  ctx.quotePaper("executable code is on a white background, agent-written proof annotations are in green, and the fixed synthesis target is in blue", SEC4);

  // ---------------------------------------------------------------- the words
  const verified = /Verus verified the complete crate \((\d+) verified, 0 errors\)/.exec(ctx.read(EX_README));
  ctx.check(verified, `${EX_README}: the Verus result`);
  return {
    title: "Example",
    lead: c({ text: "One query, from SQL to a verified answer.", repo: [EX_README, "One small query with its whole path in GenDB-V: the SQL template, the statement it means in SQLSpec, the agent's verified code"] }),
    parts: {
      meaning: {
        title: "The meaning",
        line: c({ text: "GenDB-V translates the SQL into SQLSpec, a formal meaning of SQL.", repo: [README, "GenDB-V translates the SQL into SQLSpec, a formal meaning of SQL modeled on PostgreSQL."] }),
        heads: ["SQL template", "Typed AST", "SQLSpec", "Semantics"],
      },
      proof: {
        title: "Code and proof",
        line: c({ text: "The AI agent writes the code and the proof. GenDB-V fixes the target.", repo: [README, "An AI agent writes Rust code and its proofs."], paper: [SEC4, "the fixed synthesis target is in blue"] }),
        legend: { exec: "Code", proof: "Proof", fixed: "Fixed target" },
        chainHead: "Proof chain",
      },
      answer: { title: "The answer" },
    },
    sql: { clauses },
    table: { ...table, rows },
    param: { name: "$1", value: p },
    levels,
    foot: {
      types,
      domain: "$1 = p ∈ [−2^{63}, 2^{63} − 1]",
      result: `p = ${p}:  ⟦Q⟧(db) = {[[${count}]]}`,
    },
    code: {
      file: "code/mod.rs",
      lines: codeLines,
      key: [...key].sort((a, b) => a - b),
      regions: regions.map(({ id, tag, node, lines: ls }) => ({ id, tag, node, from: Math.min(...ls), to: Math.max(...ls) })),
    },
    chain,
    answer: {
      rows: [[count]],
      formula: `[[${count}]] ∈ ⟦Q⟧(db)`,
      binding: `$1 = ${p}`,
      verified: c({ text: "Verified by Verus", repo: [EX_README, "Verus verified the complete crate"] }),
      count: verified ? `${verified[1]} verified, 0 errors` : "",
      scope: c({ text: "for every valid {db} and every value of $1", repo: [README, "Each answer is correct for every valid database and every parameter value."] }),
    },
  };
}
