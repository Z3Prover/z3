---
name: memory-safety
description: Run AddressSanitizer and UndefinedBehaviorSanitizer on the Z3 test suite to detect memory errors, undefined behavior, and leaks. Logs each finding to z3agent.db.
---

Build Z3 with compiler-based sanitizer instrumentation, execute the test suite, and parse the runtime output for memory safety violations. Supported sanitizers are AddressSanitizer (heap and stack buffer overflows, use-after-free, double-free, memory leaks) and UndefinedBehaviorSanitizer (signed integer overflow, null pointer dereference, misaligned access, shift errors). Findings are deduplicated and stored in z3agent.db for triage and longitudinal tracking.

# Step 1: Configure and build

The script invokes cmake with the appropriate `-fsanitize` flags and builds the `test-z3` target. Each sanitizer uses a separate build directory to avoid flag conflicts. If a prior instrumented build exists with matching flags, only incremental compilation runs.

```bash
python3 scripts/memory_safety.py --sanitizer asan
python3 scripts/memory_safety.py --sanitizer ubsan
python3 scripts/memory_safety.py --sanitizer both
```

To reuse an existing build:
```bash
python3 scripts/memory_safety.py --sanitizer asan --skip-build --build-dir build/sanitizer-asan
```

# Step 2: Run and collect

The test binary runs with `halt_on_error=0` so the sanitizer reports all violations rather than aborting on the first. The script parses `ERROR: AddressSanitizer`, `runtime error:`, and `ERROR: LeakSanitizer` patterns from the combined output, extracts source locations where available, and deduplicates by category, file, and line.

```bash
python3 scripts/memory_safety.py --sanitizer asan --timeout 900 --debug
```

# Step 3: Interpret results

- `clean`: no sanitizer violations detected.
- `findings`: one or more violations found. Each is printed with severity, category, message, and source location.
- `timeout`: the test suite did not complete within the deadline. Increase the timeout or investigate a possible infinite loop.
- `error`: build or execution failed before sanitizer output could be collected.

Query past runs:
```bash
python3 ../../shared/z3db.py runs --skill memory-safety --last 10
python3 ../../shared/z3db.py query "SELECT category, severity, file, line, message FROM findings WHERE run_id IN (SELECT run_id FROM runs WHERE skill='memory-safety') ORDER BY run_id DESC LIMIT 20"
```

# Parameters

| Parameter | Type | Required | Default | Description |
|-----------|------|----------|---------|-------------|
| sanitizer | choice | no | asan | which sanitizer to enable: asan, ubsan, or both |
| build-dir | path | no | build/sanitizer-{name} | path to the build directory |
| timeout | int | no | 600 | seconds before killing the test run |
| skip-build | flag | no | off | reuse an existing instrumented build |
| debug | flag | no | off | verbose cmake, make, and test output |
| db | path | no | .z3-agent/z3agent.db | path to the logging database |
