---
name: memory-safety
description: Run AddressSanitizer and UndefinedBehaviorSanitizer on the Z3 test suite to detect memory errors, undefined behavior, and leaks. Logs each finding to z3agent.db.
---

Build Z3 with compiler-based sanitizer instrumentation, execute the test suite, and parse the runtime output for memory safety violations. Supported sanitizers are AddressSanitizer (heap and stack buffer overflows, use-after-free, double-free, memory leaks) and UndefinedBehaviorSanitizer (signed integer overflow, null pointer dereference, misaligned access, shift errors). Findings are deduplicated and stored in z3agent.db for triage and longitudinal tracking.

# Step 1: Configure and build

Action:
    Invoke the script with the desired sanitizer flag. The script calls
    cmake with the appropriate `-fsanitize` flags and builds the `test-z3`
    target. Each sanitizer uses a separate build directory to avoid flag
    conflicts.

Expectation:
    cmake configures successfully and make compiles the instrumented binary.
    If a prior build exists with matching flags, only incremental compilation
    runs.

Result:
    On success: an instrumented `test-z3` binary is ready in the build
    directory. Proceed to Step 2.
    On failure: verify compiler support for the requested sanitizer flags
    and review cmake output.

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

Action:
    Execute the instrumented test binary with halt_on_error=0 so all
    violations are reported rather than aborting on the first.

Expectation:
    The script parses AddressSanitizer, UndefinedBehaviorSanitizer, and
    LeakSanitizer patterns from combined output, extracts source locations,
    and deduplicates by category/file/line.

Result:
    On `clean`: no violations detected.
    On `findings`: one or more violations found, each printed with severity,
    category, message, and source location.
    On `timeout`: test suite did not finish; increase timeout or investigate.
    On `error`: build or execution failed before sanitizer output.

```bash
python3 scripts/memory_safety.py --sanitizer asan --timeout 900 --debug
```

# Step 3: Interpret results

Action:
    Review printed findings and query z3agent.db for historical comparison.

Expectation:
    Each finding includes severity, category, message, and source location.
    The database query returns prior runs for trend analysis.

Result:
    On `clean`: no action required; proceed.
    On `findings`: triage by severity and category. Compare against prior
    runs to distinguish new regressions from known issues.
    On `timeout`: increase the deadline or investigate a possible infinite
    loop.
    On `error`: inspect build logs before re-running.

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
