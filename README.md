<p align="center">
  <img src="docs/assets/hero-s.svg" width="380" alt="The GenDB cockroach, in a GenDB helmet, takes a bite out of a database.">
</p>

<h1 align="center">GenDB-V</h1>

<p align="center"><strong>AI-generated, formally verified database engines</strong></p>

<p align="center">
  <a href="https://genlang-v.github.io/GenDB-V/">Website</a> ·
  <a href="https://arxiv.org/pdf/2611.02779">Paper</a> ·
  <a href="GUIDE.md">Guide</a> ·
  <a href="results/README.md">Results</a>
</p>

Databases are rebuilt again and again for new workloads and new hardware.<br>
**→ GenDB-V synthesizes a fast engine for your workload and hardware.**

Mature systems still return wrong answers, after years of engineering and testing.<br>
**→ GenDB-V formally verifies your engine for correctness and program safety.**

## Fast

| Speedup of GenDB-V | vs DuckDB | vs Umbra |
|:---|---:|---:|
| TPC-H, 22 queries | **51.6×** | **22.0×** |
| SEC-EDGAR, 6 queries | **61.3×** | **28.3×** |

Every query, time and verified crate is in [`results/`](results/README.md).

## Correct

Verus proves **correctness**, **memory safety**, **arithmetic safety**, **no data races** and **termination**. Each answer is correct for every valid database and every parameter value. Tests check some inputs; a proof covers all of them.

## How it works

- **SQLSpec fixes the claim.** GenDB-V translates the SQL into SQLSpec, a formal meaning of SQL modeled on PostgreSQL. The agent cannot change the claim.
- **An AI agent writes Rust code and its proofs.** It chooses the data layout, the algorithms and the proofs. It tries designs first and proves only the fastest one.
- **Verus checks the whole crate.** It checks the code and the proofs against SQLSpec. GenDB-V runs only code that Verus accepts.

GenDB-V has two modes:

- **Engine synthesis.** One verified engine answers every supported query over a schema.
- **Template synthesis.** One verified package answers one hot query template, for every parameter value.

## Getting started

Tested on Linux. You need Rust, Python 3.12, the pinned Verus and Z3, and Claude Code (only to synthesize). Then run a first query, end to end:

```sh
gendb run benchmarks/readings-count      # the data, the verified storage, then the agent writes and proves the query (paid)
gendb serve benchmarks/readings-count    # the answer at $1 = 4: [[3]]
```

The **[guide](GUIDE.md)** shows every step: install, this first run, your own workload (a folder with a schema, one SQL file per query, and the data), and how to run our published packages for free with `gendb import`.

## Repository

| Path | Content |
|---|---|
| [`src/gendb/`](src/gendb/README.md) | The GenDB-V system, one Cargo workspace |
| [`results/`](results/README.md) | TPC-H and SEC-EDGAR: every query, time and verified crate; one small query end to end |
| [`benchmarks/`](benchmarks/) | The workloads: TPC-H, SEC-EDGAR, a first example and the engine's check workload; each is a folder `gendb run` reads |
| [`docs/`](docs/README.md) | The website: design, SQLSpec, an example and the performance results |

## Paper

[**Stop Handcrafting Your Engine! GenDB-V: Towards AI-Generated and Formally Verified Database Systems**](https://arxiv.org/pdf/2611.02779)

```bibtex
@misc{lao2026stophandcraftingenginegendbv,
      title={Stop Handcrafting Your Engine! GenDB-V: Towards AI-Generated and Formally Verified Database Systems},
      author={Jiale Lao and Immanuel Trummer},
      year={2026},
      eprint={2611.02779},
      archivePrefix={arXiv},
      primaryClass={cs.DB},
      url={https://arxiv.org/abs/2611.02779},
}
```

## Contact and license

Contact: solidlao.jiale@gmail.com. GenDB-V uses the [PolyForm Noncommercial License 1.0.0](LICENSE). You may use it for research and education. For commercial use, contact us.
