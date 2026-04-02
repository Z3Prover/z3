---
description: >
  Build Z3 in debug mode from the c3 branch, compile and run the specbot tests,
  identify root causes for any crashes, and post findings as a GitHub Discussion.

on:
  workflow_dispatch:

timeout-minutes: 120

permissions: read-all

network: defaults

tools:
  cache-memory: true
  github:
    toolsets: [default, discussions]
  bash: [":*"]
  glob: {}
  view: {}
  edit: {}

safe-outputs:
  create-discussion:
    title-prefix: "[Specbot] "
    category: "Agentic Workflows"
    close-older-discussions: true
  missing-tool:
    create-issue: true
  noop:
    report-as-issue: false

steps:
  - name: Checkout c3 branch
    uses: actions/checkout@v6.0.2
    with:
      ref: c3
      persist-credentials: false

---

# Specbot Crash Analyzer

## Job Description

Your name is ${{ github.workflow }}. You are an expert C/C++ and SMT solver analyst for the Z3 theorem prover
repository `${{ github.repository }}`. Your task is to build Z3 in debug mode from the `c3` branch, compile and run
the specbot test suite, capture any crashes or assertion failures, diagnose their root causes by reading the
relevant source files, and publish a structured findings report as a GitHub Discussion.

The repository has already been checked out at the `c3` branch in the pre-step above.

## Your Task

### 1. Install Build Dependencies

Install the tools needed to build Z3 and compile the C test programs:

```bash
sudo apt-get update -y
sudo apt-get install -y cmake ninja-build python3 gcc g++ 2>&1 | tail -5
```

### 2. Build Z3 in Debug Mode

Configure and build Z3 in debug mode. Store the build output in `build/debug`:

```bash
mkdir -p build/debug
cd build/debug
cmake -G Ninja -DCMAKE_BUILD_TYPE=Debug ../.. 2>&1 | tail -10
ninja 2>&1 | tail -20
cd ../..
```

Verify the build succeeded by checking that `build/debug/libz3.so` (or `build/debug/libz3.a`) exists:

```bash
ls build/debug/libz3* 2>/dev/null || ls build/debug/*.so* 2>/dev/null || echo "Library not found"
```

If the build fails, capture the last 50 lines of ninja output and include them in the report under a
"Build Failure" section, then stop.

### 3. Compile the Specbot Tests

The `specbot/` directory at the root of the repository contains two C test programs:

- `specbot/test_specbot_seq.c` — basic specbot invariant tests for the Z3 seq/Nielsen solver
- `specbot/test_deeptest_seq.c` — deep-coverage tests targeting under-exercised code paths

Compile each test, linking against the debug build of Z3. Use the Z3 public C API header from `src/api/z3.h`:

```bash
# Compile test_specbot_seq
gcc -g -O0 \
    -I src/api \
    specbot/test_specbot_seq.c \
    -L build/debug \
    -lz3 \
    -Wl,-rpath,build/debug \
    -o /tmp/test_specbot_seq \
    2>&1
echo "test_specbot_seq compile exit: $?"

# Compile test_deeptest_seq
gcc -g -O0 \
    -I src/api \
    specbot/test_deeptest_seq.c \
    -L build/debug \
    -lz3 \
    -Wl,-rpath,build/debug \
    -o /tmp/test_deeptest_seq \
    2>&1
echo "test_deeptest_seq compile exit: $?"
```

If a test fails to compile, include the compiler error in the report and skip running that test.

### 4. Run the Tests and Capture Output

Run each compiled test binary. Capture stdout and stderr. The test harness prints lines like:

- `[TEST] Running <name>` — test started
- `[TEST] PASS <name>` — test passed
- `[TEST] CRASH <name> (exception 0x...)` — SEH exception caught (Windows only; on Linux the process aborts)
- `[TEST] ABORT <name> (caught SIGABRT)` — assertion failure caught via SIGABRT + longjmp

On Linux, wrap each run with a timeout and capture the exit code and any signal:

```bash
LD_LIBRARY_PATH=build/debug timeout 120 /tmp/test_specbot_seq > /tmp/specbot_out.txt 2>&1
echo "specbot exit: $?"
cat /tmp/specbot_out.txt

LD_LIBRARY_PATH=build/debug timeout 120 /tmp/test_deeptest_seq > /tmp/deeptest_out.txt 2>&1
echo "deeptest exit: $?"
cat /tmp/deeptest_out.txt
```

Collect every line that contains `CRASH` or `ABORT` from both output files — these are the crashes to analyze.

### 5. Diagnose Each Crash

For each crashed test function, perform the following analysis:

1. **Identify the test body**: read `specbot/test_specbot_seq.c` or `specbot/test_deeptest_seq.c`
   to understand what Z3 API calls the test makes and what invariants it exercises.

2. **Find the likely crash site**: the test exercises the Z3 Nielsen/nseq string solver. Relevant source files are:
   - `src/smt/seq_solver.h` and `src/smt/seq_solver.cpp` (or nearby files)
   - `src/smt/seq_axioms.cpp`, `src/smt/seq_eq_solver.cpp`, `src/smt/seq_regex.cpp`
   - `src/math/lp/` for length-arithmetic paths
   - `src/api/z3_api.h` for the public API entry points

   Use `grep` and `view` to locate assertion macros, `UNREACHABLE()`, `SASSERT`, or `throw` statements
   in the code paths exercised by the failing test. Example:
   ```bash
   grep -rn "SASSERT\|UNREACHABLE\|Z3_CATCH" src/smt/seq_solver.cpp 2>/dev/null | head -30
   ```

3. **Hypothesize root cause**: based on the Z3 API calls in the test and the assertion/throw sites in
   the solver source, state the most likely root cause. Common categories include:
   - Violated invariant (SASSERT/UNREACHABLE hit due to unexpected solver state)
   - Use-after-free or dangling reference during push/pop
   - Unhandled edge case in Nielsen graph construction
   - Missing theory-combination lemma between string length and integer arithmetic

4. **Suggest a fix**: propose a minimal, concrete fix — e.g., a guard condition, an additional lemma,
   a missing reference-count increment, or a missing case in a switch/match.

### 6. Generate the Report

After analyzing all crashes, produce a structured GitHub Discussion in the "Agentic Workflows" category
using `create-discussion`.

The discussion body must follow this structure (use `###` and lower for headers):

```
### Summary

- Build: Debug (CMake + Ninja, c3 branch)
- Tests compiled: N
- Tests run: N  
- Tests passed: N
- Tests crashed: N
- Tests timed out: N

### Crash Findings

For each crash, one subsection:

#### <test function name>

**Test file**: `specbot/test_specbot_seq.c` or `specbot/test_deeptest_seq.c`

**Observed failure**: ABORT/CRASH — one-line description of what was caught

**Root cause hypothesis**: explanation of which assertion or code path was hit and why

**Suggested fix**: concrete proposed change (file, function, what to add/change)

---

### Tests Passed

List of test names that passed.

<details>
<summary><b>Full Test Output</b></summary>

Raw stdout/stderr from both test binaries.

</details>

<details>
<summary><b>Build Log</b></summary>

Last 30 lines of the ninja build output.

</details>
```

If there are no crashes at all, write a "No Crashes Found" summary celebrating that all tests passed,
and include the full test output in a collapsible section.

Use `mentions: false` behavior — do not mention any GitHub usernames in the report.

Format workflow run references as: `[§${{ github.run_id }}](https://github.com/${{ github.repository }}/actions/runs/${{ github.run_id }})`.

## Usage

Trigger via **Actions → Specbot Crash Analyzer → Run workflow** on any branch; the pre-step
always checks out the `c3` branch where `specbot/test_specbot_seq.c` and
`specbot/test_deeptest_seq.c` live. The discussion is posted to the "Agentic Workflows" category.
