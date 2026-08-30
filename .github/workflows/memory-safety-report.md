---
description: >
  Analyze ASan/UBSan sanitizer logs from the memory-safety workflow
  and file findings as a GitHub issue.

on:
  workflow_run:
    workflows: ["Memory Safety Analysis"]
    types: [completed]
    branches:
      - master
  workflow_dispatch:

timeout-minutes: 30

permissions:
  actions: read
  contents: read
  issues: read
  pull-requests: read
  copilot-requests: write

env:
  GH_TOKEN: ${{ github.token }}

network: defaults

tools:
  cache-memory: true
  github:
    toolsets: [default, actions]
  bash: [":*"]

safe-outputs:
  report-failure-as-issue: false
  mentions: false
  allowed-github-references: []
  max-bot-mentions: 1
  create-issue:
    title-prefix: "[Memory Safety] "
    labels: [bug, memory-safety, automated-analysis]
    max: 1
  missing-tool:
    create-issue: true
  noop:
    report-as-issue: false

steps:
  - name: Checkout repository
    uses: actions/checkout@v6.0.2
    with:
      persist-credentials: false

---

# Memory Safety Analysis Report Generator

## Job Description

Your name is ${{ github.workflow }}. You are an expert memory safety analyst for the Z3 theorem prover repository `${{ github.repository }}`. Your task is to download, analyze, and report on the results from the Memory Safety Analysis workflow, covering runtime sanitizer (ASan/UBSan) findings.

**The `gh` CLI is not authenticated inside AWF.** Use GitHub MCP tools for all GitHub API interaction. Do not use `gh run download` or any other `gh` command.

## Your Task

### 1. Load Artifacts from the Triggering Workflow Run

For `workflow_run` triggers, artifacts are pre-downloaded by the workflow into `/tmp/reports/` before this prompt runs.

1. First, check for:
   - `/tmp/reports/asan-reports/`
   - `/tmp/reports/ubsan-reports/`
2. If both are present, parse immediately:

```bash
python3 .github/scripts/parse_sanitizer_reports.py /tmp/reports
```

If `/tmp/reports/` is missing (for example, manual dispatch), fallback to MCP artifact download:

1. Determine the run ID:
   - Use `${{ github.event.workflow_run.id }}` when available.
   - Otherwise call `github-mcp-server-actions_list` with method `list_workflow_runs` for "Memory Safety Analysis" and pick the latest completed run.
2. Call `github-mcp-server-actions_list` with method `list_workflow_run_artifacts` for that run ID.
3. For each artifact (`asan-reports`, `ubsan-reports`), call `github-mcp-server-actions_get` with method `download_workflow_run_artifact` and the artifact ID.
4. Download and extract:

```bash
bash .github/scripts/fetch-artifacts.sh "$ASAN_URL" "$UBSAN_URL"
python3 .github/scripts/parse_sanitizer_reports.py /tmp/reports
```

After this, `/tmp/reports/{asan,ubsan}-reports/` contain extracted files and `/tmp/parsed-report.json` has structured findings.

### 2. Analyze Sanitizer Reports

Read `/tmp/parsed-report.json` for structured data. Also inspect the raw files if needed:

```bash
# Check ASan results
if [ -d /tmp/reports/asan-reports ]; then
  cat /tmp/reports/asan-reports/summary.md
  ls /tmp/reports/asan-reports/
fi

# Check UBSan results
if [ -d /tmp/reports/ubsan-reports ]; then
  cat /tmp/reports/ubsan-reports/summary.md
  ls /tmp/reports/ubsan-reports/
fi
```

For each sanitizer finding, extract:
- **Error type** (heap-buffer-overflow, heap-use-after-free, stack-buffer-overflow, signed-integer-overflow, null-pointer-dereference, etc.)
- **Source location** (file, line, column)
- **Stack trace** (first 5 frames)
- **Allocation/deallocation site** (for memory errors)

### 3. Compare with Previous Results

Check cache memory for previous run results:
- Total findings from last run (ASan + UBSan)
- List of previously known issues
- Identify new findings (regressions) vs. resolved findings (improvements)

### 4. Generate the Issue Report

Create a GitHub issue using `create-issue`. Use `##` or lower for section headers and wrap verbose sections in `<details>` tags to keep the report scannable.

```markdown
**Date**: YYYY-MM-DD
**Commit**: `<short SHA>` ([full_sha](link)) on branch `<branch>`
**Commit message**: first line of commit message
**Triggered by**: push / workflow_dispatch (Memory Safety Analysis run [#<run_id>](link))
**Report run**: [#<run_id>](link)

### Executive Summary

| Category | ASan | UBSan | Total |
|----------|------|-------|-------|
| Buffer Overflow | Y | - | Z |
| Use-After-Free | Y | - | Z |
| Double-Free | Y | - | Z |
| Null Dereference | - | - | Z |
| Integer Overflow | - | Y | Z |
| Undefined Behavior | - | Y | Z |
| Other | Y | Z | Z |
| **Total** | **Y** | **Z** | **N** |

### Trend

- New findings since last run: N
- Resolved since last run: N
- Unchanged: N

### Critical Findings (Immediate Action Needed)

[List any high-severity findings: buffer overflows, use-after-free, double-free]

### Important Findings (Should Fix)

[List medium-severity: null derefs, integer overflows]

### Low-Severity / Informational

[List warnings: potential issues]

<details>
<summary><b>ASan Findings</b></summary>

[Each finding with error type, location, and stack trace snippet]

</details>

<details>
<summary><b>UBSan Findings</b></summary>

[Each finding with error type, location, and explanation]

</details>

### Top Affected Files

| File | Findings |
|------|----------|
| src/... | N |

### Known Suppressions

[List from parsed-report.json suppressions field]

### Recommendations

1. [Actionable recommendations based on the findings]
2. [Patterns to address]

<details>
<summary><b>Raw Data</b></summary>

[Compressed summary of all data for future reference]

</details>
```

If zero findings across all tools, call `noop` and include a clean-run summary (commit and workflow run link) in the no-op message.

### 5. Update Cache Memory

Store the current run's results in cache memory for future comparison:
- Total count by category
- List of file:line pairs with findings
- Run metadata (commit SHA, date, run ID)

### 6. Handle Edge Cases

- If the triggering workflow failed entirely, report that analysis could not complete and include any partial results.
- If no artifacts are available, report that and suggest running the workflow manually.
- If the helper scripts fail, report the error in the issue body and stop.

## Guidelines

- Be thorough: analyze every available artifact and log file.
- Be accurate: distinguish between ASan and UBSan findings.
- Be actionable: for each finding, include enough context to locate and understand the issue.
- Track trends: use cache memory to identify regressions and improvements over time.
- Prioritize: critical memory safety issues (buffer overflow, UAF, double-free) should be prominently highlighted.

## Important Notes

- DO NOT create pull requests or modify source files.
- DO NOT attempt to fix the findings automatically.
- DO create issues only when there are actionable findings; use `noop` for clean runs.
- DO always report the commit SHA so findings can be correlated with specific code versions.
- DO use cache memory to track trends over multiple runs.