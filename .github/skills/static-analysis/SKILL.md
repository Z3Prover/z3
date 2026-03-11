---
name: static-analysis
description: Run Clang Static Analyzer (scan-build) on Z3 source and log structured findings to z3agent.db.
---

Run the Clang Static Analyzer over a CMake build of Z3, parse the resulting plist diagnostics, and record each finding with file, line, category, and description. This skill wraps scan-build into a reproducible, logged workflow suitable for regular analysis sweeps and regression tracking.

# Step 1: Run the analysis

Action:
    Invoke the script pointing at the CMake build directory. The script
    runs `scan-build cmake ..` followed by `scan-build make` and writes
    checker output to the output directory.

Expectation:
    scan-build completes within the timeout, producing plist diagnostic
    files in the output directory (defaults to a `scan-results` subdirectory
    of the build directory).

Result:
    On success: diagnostics are parsed and findings are printed. Proceed to
    Step 2.
    On failure: verify that clang and scan-build are installed and that the
    build directory contains a valid CMake configuration.

```bash
python3 scripts/static_analysis.py --build-dir build
python3 scripts/static_analysis.py --build-dir build --output-dir /tmp/sa-results --debug
python3 scripts/static_analysis.py --build-dir build --timeout 1800
```

# Step 2: Interpret the output

Action:
    Review the printed findings and the summary table grouped by category.

Expectation:
    Each finding shows its source location, category, and description.
    The summary table ranks categories by frequency for quick triage.

Result:
    On zero findings: the codebase passes all enabled static checks.
    On findings: prioritize by category frequency and severity. Address
    null dereferences and use-after-free classes first.

Example output:

```
[Dead store] src/ast/ast.cpp:142: Value stored to 'result' is never read
[Null dereference] src/smt/theory_lra.cpp:87: Access to field 'next' results in a dereference of a null pointer
```

# Step 3: Review historical findings

Action:
    Query z3agent.db to compare current results against prior analysis
    runs.

Expectation:
    Queries return category counts and run history, enabling regression
    detection across commits.

Result:
    On stable or decreasing counts: no regressions introduced.
    On increased counts: cross-reference new findings with recent commits
    to identify the responsible change.

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
