---
name: deeptest
description: Generate stress tests and differential tests for Z3 theories. Creates random or structured SMT-LIB2 formulas, runs them through Z3, and checks for crashes, assertion failures, or result inconsistencies. Inspired by fuzzing and metamorphic testing approaches applied to SMT solvers.
---

Given a strategy and count, generate SMT-LIB2 formulas targeting Z3 internals and report anomalies. Strategies range from pure random generation to structured metamorphic and cross-theory combinations. Every formula and finding is logged to z3agent.db.

# Step 1: Choose a strategy and run

```bash
python3 scripts/deeptest.py --strategy random --count 100 --seed 42
python3 scripts/deeptest.py --strategy metamorphic --seed-file base.smt2 --count 50
python3 scripts/deeptest.py --strategy cross-theory --theories "LIA,BV" --count 80
python3 scripts/deeptest.py --strategy incremental --count 60 --debug
```

Available strategies:

- `random`: generate formulas with random declarations (Int, Bool, BitVec), random arithmetic and boolean assertions, and check-sat.
- `metamorphic`: start from a base formula (generated or loaded from file), apply equisatisfiable transformations (tautology insertion, double negation, assertion duplication), and verify the result stays consistent.
- `cross-theory`: combine multiple theories (LIA, Bool, BV) in a single formula with bridging constraints to stress theory combination.
- `incremental`: generate push/pop sequences with per-frame assertions to stress incremental solving.

# Step 2: Interpret the output

The script prints a summary after completion:

```
strategy:  random
seed:      42
formulas:  100
anomalies: 2
elapsed:   4500ms
```

A nonzero anomaly count means the run detected crashes (nonzero exit code), assertion failures in stderr, solver errors, or result disagreements between a base formula and its metamorphic variants.

# Step 3: Inspect findings

Findings are logged to `z3agent.db` with category, severity, and details:

```bash
python3 ../../shared/z3db.py query "SELECT category, severity, message FROM findings WHERE run_id IN (SELECT run_id FROM runs WHERE skill='deeptest') ORDER BY finding_id DESC LIMIT 20"
```

Each finding includes the formula index, exit code, and a stderr excerpt for triage.

# Step 4: Reproduce

Use the `--seed` parameter to reproduce a run exactly:

```bash
python3 scripts/deeptest.py --strategy random --count 100 --seed 42
```

The seed is printed in every run summary and logged in the run record.

# Parameters

| Parameter | Type | Required | Default | Description |
|-----------|------|----------|---------|-------------|
| strategy | string | no | random | test generation strategy: random, metamorphic, cross-theory, incremental |
| count | int | no | 50 | number of formulas to generate |
| seed | int | no | clock | random seed for reproducibility |
| seed-file | path | no | | base .smt2 file for metamorphic strategy |
| theories | string | no | LIA,BV | comma-separated theories for cross-theory strategy |
| timeout | int | no | 10 | per-formula Z3 timeout in seconds |
| z3 | path | no | auto | path to z3 binary |
| debug | flag | no | off | verbose tracing |
| db | path | no | .z3-agent/z3agent.db | logging database |
