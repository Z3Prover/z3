---
name: deeptest
description: Generate stress tests and differential tests for Z3 theories. Creates random or structured SMT-LIB2 formulas, runs them through Z3, and checks for crashes, assertion failures, or result inconsistencies. Inspired by fuzzing and metamorphic testing approaches applied to SMT solvers.
---

Given a strategy and count, generate SMT-LIB2 formulas targeting Z3 internals and report anomalies. Strategies range from pure random generation to structured metamorphic and cross-theory combinations. Every formula and finding is logged to z3agent.db.

# Step 1: Choose a strategy and run

Action:
    Select a generation strategy and invoke the script with the desired
    count and seed.

Expectation:
    The script generates SMT-LIB2 formulas according to the chosen
    strategy, runs each through Z3, and records results to z3agent.db.

Result:
    On completion: a summary is printed with formula count, anomaly count,
    and elapsed time. Proceed to Step 2.
    On early exit: verify the Z3 binary is accessible and review timeout
    settings.

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

Action:
    Review the summary printed after the run completes.

Expectation:
    The summary shows strategy, seed, formula count, anomaly count, and
    elapsed time.

Result:
    On zero anomalies: Z3 handled all generated formulas without issue.
    On nonzero anomalies: crashes, assertion failures, solver errors, or
    result disagreements were detected. Proceed to Step 3 for details.

Example summary:

```
strategy:  random
seed:      42
formulas:  100
anomalies: 2
elapsed:   4500ms
```

# Step 3: Inspect findings

Action:
    Query z3agent.db for detailed finding records from the run.

Expectation:
    Each finding includes category, severity, message, formula index, exit
    code, and a stderr excerpt.

Result:
    Use findings to identify reproducible failure patterns and prioritize
    fixes by severity. If a finding appears nondeterministic, proceed to
    Step 4 with the same seed to confirm.

```bash
python3 ../../shared/z3db.py query "SELECT category, severity, message FROM findings WHERE run_id IN (SELECT run_id FROM runs WHERE skill='deeptest') ORDER BY finding_id DESC LIMIT 20"
```

# Step 4: Reproduce

Action:
    Re-run the script with the same seed to reproduce the exact sequence
    of generated formulas.

Expectation:
    Identical formulas are generated, producing the same anomalies if the
    underlying bug persists.

Result:
    On same anomalies: bug confirmed and suitable for a regression test.
    On zero anomalies: the issue may be nondeterministic or already fixed;
    investigate further before closing.

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
