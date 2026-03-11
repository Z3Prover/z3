# Z3 Agent Skills

Reusable, composable verification primitives for the Z3 theorem prover.
Each skill is a self-contained unit: a `SKILL.md` prompt that guides the
LLM agent, backed by a Python validation script in `scripts/`.

## Skill Catalogue

| Skill | Status | Description |
|-------|--------|-------------|
| solve | implemented | Check satisfiability of SMT-LIB2 formulas; return models or unsat cores |
| prove | implemented | Prove validity by negation and satisfiability checking |
| encode | implemented | Translate constraint problems into SMT-LIB2 or Z3 Python API code |
| simplify | implemented | Reduce formula complexity using configurable Z3 tactic chains |
| optimize | implemented | Solve constrained optimization (minimize/maximize) over numeric domains |
| explain | implemented | Parse and interpret Z3 output: models, cores, statistics, errors |
| benchmark | implemented | Measure Z3 performance and collect solver statistics |
| static-analysis | planned | Run Clang Static Analyzer on Z3 source and log structured findings |
| deeptest | planned | Deep property-based testing of Z3 internals |
| memory-safety | planned | Memory safety verification of Z3 C++ source |

## Agents

Two orchestration agents compose these skills into end-to-end workflows:

| Agent | Role |
|-------|------|
| z3-solver | Formulation and solving: encode, solve, prove, simplify, optimize, explain |
| z3-verifier | Codebase quality: benchmark, static-analysis, deeptest, memory-safety |

## Shared Infrastructure

All scripts share a common library at `shared/z3db.py` with:

* `Z3DB`: SQLite wrapper for tracking runs, formulas, findings, and interaction logs.
* `run_z3()`: Pipe SMT-LIB2 into `z3 -in` with timeout handling.
* `find_z3()`: Locate the Z3 binary across build directories and PATH.
* Parsers: `parse_model()`, `parse_stats()`, `parse_unsat_core()`.

The database schema lives in `shared/schema.sql`.

## Relationship to a3/ Workflows

The `a3/` directory at the repository root contains two existing agentic workflow
prompts that predate the skill architecture:

* `a3/a3-python.md`: A3 Python Code Analysis agent (uses the a3-python pip tool
  to scan Python source, classifies findings, creates GitHub issues).
* `a3/a3-rust.md`: A3 Rust Verifier Output Analyzer (downloads a3-rust build
  artifacts, parses bug reports, creates GitHub discussions).

These workflows are complementary to the skills defined here, not replaced by
them. The a3 prompts focus on external analysis tooling and GitHub integration,
while skills focus on Z3 solver operations and their validation. Both may be
composed by the same orchestrating agent.

## Usage

Check database status and recent runs:

```
python shared/z3db.py status
python shared/z3db.py runs --skill solve --last 5
python shared/z3db.py log --run-id 12
python shared/z3db.py query "SELECT skill, COUNT(*) FROM runs GROUP BY skill"
```

Run an individual skill script directly:

```
python solve/scripts/solve.py --file problem.smt2
python encode/scripts/encode.py --validate formula.smt2
python benchmark/scripts/benchmark.py --file problem.smt2
```
