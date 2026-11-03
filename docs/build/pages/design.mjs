// Design page data: three highlights (correct, fast, coverage) and the three parts of the design (SQLSpec; agentic code and proof synthesis;
// independent verification), each sentence with its source in this repository (its README, or the claim in
// GUIDE.md) or in the paper.
// Formulas use the site's names: db for the database D, build for the storage builder B, query for the template
// executor E_T, engine for the engine E; the paper states the targets as Equations 4 and 5 (sections/03-sqlspec.tex).
const README = "README.md", GUIDE = "GUIDE.md", ABSTRACT = "sections/00-abstract.tex";
const OVERVIEW = "sections/02-overview.tex", SQLSPEC = "sections/03-sqlspec.tex", INTRO = "sections/01-introduction.tex";
const SYNTH = "sections/04-obligations.tex", VERIFY = "sections/05-synthesis.tex";

export default function build(ctx) {
  const c = ctx.claim;
  // the targets as the paper states them; the formulas below are the same targets in the site's names
  ctx.quotePaper("\\mathsf{Valid}_\\Sigma(D)\\land\\mathsf{Rep}(S,D)\\\\ &\\Longrightarrow\\mathsf{Allowed}(D,Q_T(p),E_T(S,p))", SQLSPEC);
  ctx.quotePaper("\\mathsf{Valid}_\\Sigma(D)\\land\\mathsf{Rep}(S,D)\\\\ &\\Longrightarrow\\mathsf{Allowed}(D,Q,E(S,Q))", SQLSPEC);
  ctx.quotePaper("$\\mathsf{Allowed}(D,Q,o)$ for a query tree $Q$ and execution outcome $o$ to hold if and only if $o\\in\\llbracket Q\\rrbracket(D)$", SQLSPEC);
  ctx.quotePaper("building storage from $D$ establishes $\\mathsf{Rep}(B(D),D)$", SQLSPEC);
  ctx.quote("rows that are an allowed answer of the statement's SQLSpec meaning ⟦Q⟧(db)", GUIDE);
  return {
    title: "Design",
    highlights: [
      { id: "correct", icon: "shield-check", title: "Correct", lines: [c({ text: "Mathematically sound. Formally verified.", paper: [OVERVIEW, "a formal library in Verus that mathematically defines SQL semantics"], repo: [GUIDE, "Verus proves this claim."] })] },
      { id: "fast", icon: "zap", title: "Fast", lines: [c({ text: "Specialized to your workload.", paper: [ABSTRACT, "a system that enables AI agents to synthesize database engines specialized to hardware and workloads for performance"] })] },
      { id: "coverage", icon: "layers", title: "Coverage", lines: [c({ text: "Template and engine synthesis.", paper: [ABSTRACT, "GenDB-V supports specialized implementations of SQL templates and general-purpose engines that accept any query within a supported SQL subset"], repo: [README, "**Template synthesis.** One verified package answers one hot query template, for every parameter value."] })] },
    ],
    blocks: [
      {
        id: "sqlspec",
        title: "SQLSpec",
        line: c({ text: "SQLSpec defines what SQL means, in math.", paper: [OVERVIEW, "a formal library in Verus that mathematically defines SQL semantics based on PostgreSQL documentation"], repo: [GUIDE, "SQLSpec, a formal meaning of SQL modeled on PostgreSQL"] }),
        formula: "⟦Q⟧(db)",
        formulaText: c({ text: "every allowed answer of query {Q} on database {db}", repo: [GUIDE, "an allowed answer of the statement's SQLSpec meaning ⟦Q⟧(db)"], paper: [SQLSPEC, "SQLSpec defines the set of permitted outcomes $\\llbracket Q\\rrbracket(D)$"] }),
        covers: ["NULL", "Duplicate rows", "SQL errors", "Row order and ties"].map((t) => c({ text: t, paper: [INTRO, "nulls, duplicate rows, runtime SQL errors, and the multiple valid results permitted by unspecified row order and ordering ties"] })),
      },
      {
        id: "synthesis",
        title: "Agentic code and proof synthesis",
        line: c({ text: "An AI agent writes the code and its proofs. It chooses the data layout, the algorithms and the proofs.", repo: [README, "It chooses the data layout, the algorithms and the proofs."], paper: [OVERVIEW, "agents freely explore physical implementations, intermediate contracts, and proofs together"] }),
        parts: [
          { icon: "hard-drive", title: "Storage", text: c({ text: "Layout, builder, proof", paper: [SYNTH, "an agent analyzes the schema, data, workload, and hardware to synthesize a custom storage builder $B$, reader functions, and a representation predicate"] }) },
          { icon: "code-xml", title: "Query", text: c({ text: "Code, proof", paper: [OVERVIEW, "agents co-design storage layouts and execution algorithms"] }) },
        ],
        order: [
          { icon: "zap", text: c({ text: "Fastest design first", paper: [INTRO, "agents first prototype and profile candidate designs in an unverified mode and only develop proofs for the fastest design"] }) },
          { icon: "shield-check", text: c({ text: "Then the proofs", paper: [INTRO, "only develop proofs for the fastest design"] }) },
        ],
      },
      {
        id: "verification",
        title: "Independent verification",
        line: c({ text: "Verus checks the code and the proofs against SQLSpec. GenDB-V runs only code that Verus accepts.", repo: [README, "GenDB-V runs only code that Verus accepts."], paper: [VERIFY, "runs Verus across the entire program"] }),
        targets: [
          {
            mode: c({ text: "One query template", repo: [README, "One verified package answers one hot query template"] }),
            formula: "query(build(db)) ∈ ⟦Q⟧(db)",
            scope: c({ text: "for every valid {db} and every parameter value", repo: [README, "Each answer is correct for every valid database and every parameter value."] }),
          },
          {
            mode: c({ text: "One engine", repo: [README, "One verified engine answers every supported query over a schema"] }),
            formula: "engine(build(db), Q) ∈ ⟦Q⟧(db)",
            scope: c({ text: "for every valid {db} and every supported query {Q}", repo: [README, "One verified engine answers every supported query over a schema"], paper: [INTRO, "on every valid database, across all allowed parameter bindings for a SQL template or across all supported queries for a general-purpose engine"] }),
          },
        ],
        fixed: c({ text: "The agent cannot change the claim.", repo: [README, "The agent cannot change the claim."], paper: [VERIFY, "it cannot weaken the target, add extra input assumptions, or prove an unused function"] }),
      },
    ],
  };
}
