---
name: static-analysis
description: Run Clang Static Analyzer (scan-build) on Z3 source and log structured findings to z3agent.db.
---

Run the Clang Static Analyzer over a CMake build of Z3, parse the resulting plist diagnostics, and record each finding with file, line, category, and description. This skill wraps scan-build into a reproducible, logged workflow suitable for regular analysis sweeps and regression tracking.

# Step 1: Run the analysis

```bash
python3 scripts/static_analysis.py --build-dir build
python3 scripts/static_analysis.py --build-dir build --output-dir /tmp/sa-results --debug
python3 scripts/static_analysis.py --build-dir build --timeout 1800
```

The script invokes `scan-build cmake ..` followed by `scan-build make` inside the specified build directory. Clang checker output is written to `--output-dir` (defaults to a `scan-results` subdirectory of the build directory).

# Step 2: Interpret the output

Each finding is printed with its source location, category, and description:

```
[Dead store] src/ast/ast.cpp:142: Value stored to 'result' is never read
[Null dereference] src/smt/theory_lra.cpp:87: Access to field 'next' results in a dereference of a null pointer
```

A summary table groups findings by category so that high-frequency classes are visible at a glance.

# Step 3: Review historical findings

All findings are logged to `z3agent.db`. Query them to track trends:

```bash
python3 ../../shared/z3db.py query "SELECT category, COUNT(*) as cnt FROM findings WHERE run_id IN (SELECT run_id FROM runs WHERE skill='static-analysis') GROUP BY category ORDER BY cnt DESC"
python3 ../../shared/z3db.py runs --skill static-analysis --last 10
```

# Parameters

| Parameter | Type | Required | Default | Description |
|-----------|------|----------|---------|-------------|
| build-dir | path | yes | | path to the CMake build directory |
| output-dir | path | no | BUILD/scan-results | directory for scan-build output |
| timeout | int | no | 1200 | seconds allowed for the full build |
| db | path | no | .z3-agent/z3agent.db | logging database |
| debug | flag | no | off | verbose tracing |
