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

  - name: Install build dependencies
    run: |
      sudo apt-get update -y
      sudo apt-get install -y cmake ninja-build python3 gcc g++ 2>&1 | tail -5

  - name: Build Z3 in debug mode
    id: build-z3
    continue-on-error: true
    run: |
      mkdir -p build/debug specbot-results
      cd build/debug
      cmake -G Ninja -DCMAKE_BUILD_TYPE=Debug ../.. 2>&1 | tee ../../specbot-results/cmake.log
      ninja 2>&1 | tee ../../specbot-results/build.log
      BUILD_EXIT=$?
      cd ../..
      echo "build_exit=${BUILD_EXIT}" >> specbot-results/build-status.txt
      ls -la build/debug/libz3* build/debug/*.so* 2>/dev/null >> specbot-results/build-status.txt || echo "Library not found" >> specbot-results/build-status.txt
      exit $BUILD_EXIT

  - name: Compile specbot tests
    continue-on-error: true
    run: |
      mkdir -p specbot-results
      gcc -g -O0 \
          -I src/api \
          specbot/test_specbot_seq.c \
          -L build/debug \
          -lz3 \
          -Wl,-rpath,"${GITHUB_WORKSPACE}/build/debug" \
          -o specbot-results/test_specbot_seq \
          2>&1 | tee specbot-results/compile_specbot_seq.log
      echo "compile_specbot_seq_exit=$?" >> specbot-results/compile-status.txt

      gcc -g -O0 \
          -I src/api \
          specbot/test_deeptest_seq.c \
          -L build/debug \
          -lz3 \
          -Wl,-rpath,"${GITHUB_WORKSPACE}/build/debug" \
          -o specbot-results/test_deeptest_seq \
          2>&1 | tee specbot-results/compile_deeptest_seq.log
      echo "compile_deeptest_seq_exit=$?" >> specbot-results/compile-status.txt

  - name: Run specbot tests
    continue-on-error: true
    run: |
      mkdir -p specbot-results
      if [ -f specbot-results/test_specbot_seq ]; then
        LD_LIBRARY_PATH="${GITHUB_WORKSPACE}/build/debug" timeout 120 specbot-results/test_specbot_seq > specbot-results/test_specbot_seq.log 2>&1
        SPECBOT_EXIT=$?
        echo "specbot_seq_exit=${SPECBOT_EXIT}" >> specbot-results/test-status.txt
      else
        echo "Binary not compiled" > specbot-results/test_specbot_seq.log
        echo "specbot_seq_exit=127" >> specbot-results/test-status.txt
      fi

      if [ -f specbot-results/test_deeptest_seq ]; then
        LD_LIBRARY_PATH="${GITHUB_WORKSPACE}/build/debug" timeout 120 specbot-results/test_deeptest_seq > specbot-results/test_deeptest_seq.log 2>&1
        DEEPTEST_EXIT=$?
        echo "deeptest_seq_exit=${DEEPTEST_EXIT}" >> specbot-results/test-status.txt
      else
        echo "Binary not compiled" > specbot-results/test_deeptest_seq.log
        echo "deeptest_seq_exit=127" >> specbot-results/test-status.txt
      fi

---

# Specbot Crash Analyzer

## Job Description

Your name is ${{ github.workflow }}. You are an expert C/C++ and SMT solver analyst for the Z3 theorem prover
repository `${{ github.repository }}`. The pre-steps above have already built Z3 in debug mode from the `c3`
branch, compiled and run the specbot test suite, and saved all output to the `specbot-results/` directory in
the workspace (`${{ github.workspace }}/specbot-results/`). Your task is to analyze those results, diagnose
any crash root causes by reading the relevant source files, and publish a structured findings report as a
GitHub Discussion.

**Do not try to build Z3 or run tests yourself.** All build and test output is already in `specbot-results/`.

## Your Task

### 1. Read the Pre-Generated Results

All build and test outputs are in `specbot-results/` (relative to the workspace root). Read each file:

```bash
# Build status
cat specbot-results/build-status.txt 2>/dev/null || echo "No build status"

# Compile status
cat specbot-results/compile-status.txt 2>/dev/null || echo "No compile status"

# Test status
cat specbot-results/test-status.txt 2>/dev/null || echo "No test status"

# Test output from test_specbot_seq
cat specbot-results/test_specbot_seq.log 2>/dev/null || echo "No test_specbot_seq output"

# Test output from test_deeptest_seq
cat specbot-results/test_deeptest_seq.log 2>/dev/null || echo "No test_deeptest_seq output"

# Last 30 lines of the build log
tail -30 specbot-results/build.log 2>/dev/null || echo "No build log"
```

If `specbot-results/build-status.txt` shows `build_exit=0`, the build succeeded.
If it shows a non-zero exit, include the last 50 lines of `specbot-results/build.log` in the report
under a "Build Failure" section.

If `specbot-results/compile-status.txt` shows a non-zero exit for a test, include the compile error
from `specbot-results/compile_specbot_seq.log` or `specbot-results/compile_deeptest_seq.log`.

Collect every line containing `CRASH` or `ABORT` from the test log files — these are the crashes to analyze.

### 2. Diagnose Each Crash

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

### 3. Generate the Report

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

Trigger via **Actions → Specbot Crash Analyzer → Run workflow** on any branch. The pre-steps
always check out the `c3` branch where `specbot/test_specbot_seq.c` and
`specbot/test_deeptest_seq.c` live, build Z3, run the tests, and save results to `specbot-results/`.
The agent then analyzes the results and posts a discussion to the "Agentic Workflows" category.
