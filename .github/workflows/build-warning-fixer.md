---
name: Clang-Tidy Warning Fixer
description: Compiles Z3 with clang-tidy, analyzes build warnings and errors, and creates PRs with safe fixes
on:
  schedule: daily
  workflow_dispatch:
  skip-if-match: 'is:pr is:open in:title "[clang-tidy]"'
permissions:
  contents: read
  issues: read
  pull-requests: read
  copilot-requests: write
tracker-id: clang-tidy-warning-fixer
safe-outputs:
  report-failure-as-issue: false
  create-pull-request:
    title-prefix: "[clang-tidy] "
    labels: [code-quality, clang-tidy, automation]
    reviewers: [copilot]
    expires: 1d
    if-no-changes: ignore
  missing-tool:
    create-issue: true
  noop:
    report-as-issue: false
network: defaults
tools:
  github:
    toolsets: [default]
  bash: [":*"]
timeout-minutes: 90
strict: true

steps:
  - name: Checkout repository
    uses: actions/checkout@v7.0.1
    with:
      persist-credentials: false

  - name: Prebuild and collect clang diagnostics
    shell: bash
    run: |
      set -o pipefail
      mkdir -p /tmp/gh-aw/agent

      missing_tools=0
      command -v clang >/dev/null 2>&1 || missing_tools=1
      command -v clang-tidy >/dev/null 2>&1 || missing_tools=1
      command -v cmake >/dev/null 2>&1 || missing_tools=1
      command -v ninja >/dev/null 2>&1 || missing_tools=1
      command -v python3 >/dev/null 2>&1 || missing_tools=1
      if [ "$missing_tools" -eq 1 ]; then
        sudo apt-get update -y
        sudo apt-get install -y clang clang-tidy cmake ninja-build python3
      fi

      rm -rf build

      configure_status=0
      build_status=0

      CC=clang CXX=clang++ cmake -GNinja -S . -B build \
        -DCMAKE_BUILD_TYPE=Debug \
        -DCMAKE_EXPORT_COMPILE_COMMANDS=ON \
        -DCMAKE_CXX_CLANG_TIDY=clang-tidy \
        2>&1 | tee /tmp/gh-aw/agent/clang-tidy-configure.log || configure_status=$?

      if [ "$configure_status" -eq 0 ]; then
        cmake --build build --target shell test-z3 -k 0 \
          2>&1 | tee /tmp/gh-aw/agent/clang-tidy-build.log || build_status=$?
      else
        printf 'configure failed; build skipped\n' | tee /tmp/gh-aw/agent/clang-tidy-build.log
        build_status=125
      fi

      grep -nE 'warning:|error:|clang-tidy' /tmp/gh-aw/agent/clang-tidy-build.log \
        > /tmp/gh-aw/agent/clang-tidy-diagnostics.txt || true

      {
        echo "configure_status=$configure_status"
        echo "build_status=$build_status"
      } > /tmp/gh-aw/agent/prebuild-status.txt
---

# Clang-Tidy Warning Fixer

You are an AI agent that uses pre-collected clang-tidy diagnostics, reviews warnings and errors, and creates a pull request with conservative fixes when you can do so safely.

## Current Context

- **Repository**: ${{ github.repository }}
- **Workflow**: ${{ github.workflow }}
- **Workspace**: ${{ github.workspace }}
- **Prebuild status file**: `/tmp/gh-aw/agent/prebuild-status.txt`
- **Prebuild configure log**: `/tmp/gh-aw/agent/clang-tidy-configure.log`
- **Prebuild build log**: `/tmp/gh-aw/agent/clang-tidy-build.log`
- **Prebuild diagnostics list**: `/tmp/gh-aw/agent/clang-tidy-diagnostics.txt`

## Your Task

### 0. Verify repository target

This workflow is only for `Z3Prover/z3`.

If `${{ github.repository }}` is not `Z3Prover/z3`, call `noop` immediately with a short explanation.

### 1. Review prebuild results before taking action

This workflow already ran a prebuild with clang-tidy before agent mode. Start by inspecting:
- `/tmp/gh-aw/agent/prebuild-status.txt`
- `/tmp/gh-aw/agent/clang-tidy-configure.log`
- `/tmp/gh-aw/agent/clang-tidy-build.log`
- `/tmp/gh-aw/agent/clang-tidy-diagnostics.txt`

If prebuild configuration failed, inspect the configure log and call `noop` with a clear summary unless you can make an obvious, local, semantics-preserving fix.

### 2. Extract actionable diagnostics

Analyze `/tmp/gh-aw/agent/clang-tidy-diagnostics.txt` and `/tmp/gh-aw/agent/clang-tidy-build.log`, focusing on diagnostics emitted during this workflow run.

Use commands like:

```bash
grep -nE 'warning:|error:|clang-tidy' /tmp/gh-aw/agent/clang-tidy-build.log | head -200
```

Classify findings into:
- **clang-tidy warnings**
- **compiler warnings**
- **compiler or build errors**

Prioritize findings that are:
- localized to one file
- straightforward to fix safely
- unlikely to change behavior
- validated by rebuilding

Skip findings that require design changes, broad refactors, or uncertain semantic changes.

### 3. Investigate the affected code

For each high-confidence finding:

1. Locate the file and exact lines.
2. Read the surrounding code.
3. Confirm the warning is real and not already fixed.
4. Prefer the smallest possible change.

Examples of usually safe fixes:
- removing dead or unused locals
- adding `override` where the class already overrides a virtual method
- adding `[[maybe_unused]]` for intentionally unused parameters or variables
- replacing obvious null literal usage with `nullptr`
- applying other trivial clang-tidy modernizations that do not alter behavior

Do **not** change behavior, APIs, ownership, solver logic, or performance-sensitive code unless the fix is obviously semantics-preserving.

### 4. Apply fixes conservatively

When you are confident, edit the relevant files and keep the patch minimal.

Rules:
- fix only warnings you fully understand
- do not batch unrelated cleanups
- preserve formatting and local style
- if a finding is uncertain, skip it instead of guessing

### 5. Rebuild and confirm the fixes

After making changes, rerun the same configure/build sequence if needed and always rerun at least:

```bash
cmake --build build --target shell test-z3 -k 0 2>&1 | tee /tmp/gh-aw/agent/clang-tidy-build-after.log
./build/test-z3 /a
```

If the rebuilt logs still contain actionable warnings, you may fix another small set if you remain confident. Otherwise stop.

### 6. Provide git diff details for GitHub issue contexts

When this workflow is dispatched from a GitHub issue context (for example via `aw_context` with `item_type == "issue"`), always include patch details to make PR creation easy:

```bash
git status --short
git diff --stat
git diff
```

If changes were made, include the full unified diff in your final response in a fenced `diff` block and summarize changed files explicitly.

### 7. Create the pull request

If you made safe fixes, create a pull request using `create-pull-request`.

Use a title describing the warnings fixed, for example:
- `Fix clang-tidy warnings in parser code`
- `Fix clang-tidy override and unused warnings`

The PR body should include:
- that the workflow compiled Z3 with clang-tidy
- the build command that was used
- the files changed
- the warnings or errors fixed
- confirmation that you rebuilt and ran `./build/test-z3 /a`
- a brief note for any remaining warnings you intentionally skipped

If there are no safe fixes to make, call `noop` with a short summary of what you built and what you found.

## Guidelines

- Be conservative and high-confidence only.
- Prefer no PR over a risky PR.
- Keep fixes surgical and easy to review.
- Validate every change by rebuilding.
- Focus on diagnostics produced by this workflow run, not on unrelated code quality ideas.
