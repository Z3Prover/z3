---
name: Clang-Tidy Warning Fixer
description: Analyzes clang-tidy warning artifacts and files GitHub issues with proposed fixes as git diffs
on:
  workflow_run:
    workflows: ["Clang-Tidy Warning Report"]
    types: [completed]
    branches:
      - master
  workflow_dispatch:
  skip-if-match: 'is:pr is:open in:title "[clang-tidy]"'
permissions:
  actions: read
  contents: read
  issues: read
  pull-requests: read
  copilot-requests: write
tracker-id: clang-tidy-warning-fixer
safe-outputs:
  report-failure-as-issue: false
  create-issue:
    title-prefix: "[clang-tidy] "
    labels: [code-quality, clang-tidy, automation]
    max: 1
  missing-tool:
    create-issue: true
  noop:
    report-as-issue: false
network: defaults
tools:
  github:
    toolsets: [default, actions]
  bash: [":*"]
timeout-minutes: 90
strict: true

steps:
  - name: Checkout repository
    uses: actions/checkout@v7.0.1
    with:
      persist-credentials: false

---

# Clang-Tidy Warning Fixer

You are an AI agent that uses clang-tidy warning output captured in GitHub Actions logs, proposes conservative fixes, and creates a GitHub issue with ready-to-apply git diffs.

## Current Context

- **Repository**: ${{ github.repository }}
- **Workflow**: ${{ github.workflow }}
- **Workspace**: ${{ github.workspace }}
- **Trigger run ID**: `${{ github.event.workflow_run.id }}`
- **Expected source workflow**: `clang-tidy-warning-report.yml` (`Clang-Tidy Warning Report`)
- **Local log analysis path**: `/tmp/gh-aw/clang-tidy-warning-report`

## Your Task

### 0. Verify repository target

This workflow is only for `Z3Prover/z3`.

If `${{ github.repository }}` is not `Z3Prover/z3`, call `noop` immediately with a short explanation.

### 1. Retrieve logs from `clang-tidy-warning-report.yml`

Use GitHub MCP tools (not `gh`) to retrieve job logs from the triggering run. Do not use `download_workflow_run_artifact`: it may be unavailable, and this workflow must operate entirely from Actions logs.

1. Determine source run ID:
   - If `${{ github.event.workflow_run.id }}` is present, use it.
   - For manual dispatch, call `github-mcp-server-actions_list` (`list_workflow_runs`) for workflow `clang-tidy-warning-report.yml` and select the latest `completed` run.
2. List jobs for that run with `github-mcp-server-actions_list` (`list_workflow_jobs`).
3. Identify the job named `Build Z3 with clang-tidy warnings`.
4. Retrieve its logs with `github-mcp-server-get_job_logs` using `return_content: true` and a large `tail_lines` value so the appended summary block is included.
5. Save the returned log content locally for repeatable analysis:

```bash
mkdir -p /tmp/gh-aw/clang-tidy-warning-report
cat <<'EOF' > /tmp/gh-aw/clang-tidy-warning-report/build.log
$JOB_LOG_CONTENT
EOF
cp /tmp/gh-aw/clang-tidy-warning-report/build.log /tmp/gh-aw/clang-tidy-warning-report/combined.log
ls -la /tmp/gh-aw/clang-tidy-warning-report
```

The source workflow emits a marker-delimited summary near the end of the job log:

- `CLANG_TIDY_WARNING_REPORT_BEGIN`
- `CLANG_TIDY_STATUS_BEGIN` / `CLANG_TIDY_STATUS_END`
- `CLANG_TIDY_WARNINGS_BEGIN` / `CLANG_TIDY_WARNINGS_END`
- `CLANG_TIDY_WARNING_REPORT_END`

Extract the summary into local files:

```bash
sed -n '/^CLANG_TIDY_STATUS_BEGIN$/,/^CLANG_TIDY_STATUS_END$/p' \
  /tmp/gh-aw/clang-tidy-warning-report/combined.log | sed '1d;$d' \
  > /tmp/gh-aw/clang-tidy-warning-report/status.txt

sed -n '/^CLANG_TIDY_WARNINGS_BEGIN$/,/^CLANG_TIDY_WARNINGS_END$/p' \
  /tmp/gh-aw/clang-tidy-warning-report/combined.log | sed '1d;$d' \
  > /tmp/gh-aw/clang-tidy-warning-report/warnings.txt
```

If the marker block is missing, fall back to grepping the full log:

```bash
grep -nE 'warning:|error:|clang-tidy' /tmp/gh-aw/clang-tidy-warning-report/combined.log \
  > /tmp/gh-aw/clang-tidy-warning-report/warnings.txt || true
```

Expect at minimum `build.log`, `combined.log`, and `warnings.txt`. Prefer using `status.txt` when extracted successfully. If the job log is unavailable or empty, call `noop` with a concise explanation.

### 2. Extract actionable diagnostics

Analyze log-derived files from this run:
- `/tmp/gh-aw/clang-tidy-warning-report/warnings.txt`
- `/tmp/gh-aw/clang-tidy-warning-report/build.log`
- `/tmp/gh-aw/clang-tidy-warning-report/combined.log`
- `/tmp/gh-aw/clang-tidy-warning-report/status.txt` (when available)

Use commands like:

```bash
grep -nE 'warning:|error:|clang-tidy' /tmp/gh-aw/clang-tidy-warning-report/combined.log | head -300
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

### 4. Draft fixes conservatively as patch proposals

For each high-confidence warning, draft the smallest safe change as a unified diff proposal.

Rules:
- fix only warnings you fully understand
- do not batch unrelated cleanups
- preserve formatting and local style
- if a finding is uncertain, skip it instead of guessing
- prefer one focused diff hunk per warning
- do not propose broad refactors or behavioral changes

### 5. Document proposed fixes as git diffs

For each proposed fix, include:
- file path
- warning being fixed
- rationale
- a fenced unified diff block (` ```diff ... ``` `)

Also include one consolidated patch section that can be directly applied:

```bash
git apply - << 'EOF'
[all diff hunks]
EOF
```

### 6. Create a GitHub issue with fixes

Create exactly one issue using `create-issue` when there are actionable warnings.

Issue content must include:
- source workflow run link (`clang-tidy-warning-report.yml` run ID)
- summary counts by warning type
- list of skipped warnings with reasons
- proposed fixes as unified diffs (full diff text, not prose only)
- short assignment-ready checklist for Copilot (one checkbox per proposed fix)

If no actionable warnings are found, or the source job logs are missing/corrupt, call `noop` with a concise explanation.

## Guidelines

- Be conservative and high-confidence only.
- Prefer no issue over risky or speculative patch suggestions.
- Keep fixes surgical and easy to review.
- Focus only on diagnostics produced by the referenced `clang-tidy-warning-report.yml` run.
- Prefer workflow job logs over cross-run artifact downloads, even if artifact metadata is visible.
