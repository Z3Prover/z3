---
name: benchmark
description: Measure Z3 performance on a formula or file. Collects wall-clock time, theory solver statistics, memory usage, and conflict counts. Results are logged to z3agent.db for longitudinal tracking.
---

Given an SMT-LIB2 formula or file, run Z3 with statistics enabled and report performance characteristics. This is useful for identifying performance regressions, comparing tactic strategies, and profiling theory solver workload distribution.

# Step 1: Run Z3 with statistics

```bash
python3 scripts/benchmark.py --file problem.smt2
python3 scripts/benchmark.py --file problem.smt2 --runs 5
python3 scripts/benchmark.py --formula "(declare-const x Int)..." --debug
```

The script invokes `z3 -st` and parses the `:key value` statistics block.

# Step 2: Interpret the output

The output includes:

- wall-clock time (ms)
- result (sat/unsat/unknown/timeout)
- memory usage (MB)
- conflicts, decisions, propagations
- per-theory breakdown (arithmetic, bv, array, etc.)

With `--runs N`, the script runs Z3 N times and reports min/median/max timing.

# Step 3: Compare over time

Past benchmark runs are logged to `z3agent.db`. Query them:
```bash
python3 ../../shared/z3db.py runs --skill benchmark --last 20
python3 ../../shared/z3db.py query "SELECT smtlib2, result, stats FROM formulas WHERE run_id IN (SELECT run_id FROM runs WHERE skill='benchmark') ORDER BY run_id DESC LIMIT 5"
```

# Parameters

| Parameter | Type | Required | Default | Description |
|-----------|------|----------|---------|-------------|
| formula | string | no | | SMT-LIB2 formula |
| file | path | no | | path to .smt2 file |
| runs | int | no | 1 | number of repeated runs for timing |
| timeout | int | no | 60 | seconds per run |
| z3 | path | no | auto | path to z3 binary |
| debug | flag | no | off | verbose tracing |
| db | path | no | .z3-agent/z3agent.db | logging database |
