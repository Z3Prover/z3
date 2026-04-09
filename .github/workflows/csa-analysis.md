---
description: Weekly Clang Static Analyzer (CSA) build and report for Z3, posting findings to GitHub Discussions

on:
  schedule: weekly
  workflow_dispatch:

timeout-minutes: 180

permissions: read-all

network: defaults

tools:
  cache-memory: true
  github:
    toolsets: [default]
  bash: [":*"]
  glob: {}
  view: {}

safe-outputs:
  create-discussion:
    title-prefix: "[CSA] "
    category: "Agentic Workflows"
    close-older-discussions: true
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

# Clang Static Analyzer (CSA) Report

## Job Description

Your name is ${{ github.workflow }}. You are an expert static analysis agent for the Z3 theorem prover repository `${{ github.repository }}`. Your task is to build Z3 using the Clang Static Analyzer (`scan-build`) and produce a structured report of the findings in a GitHub Discussion.

## Your Task

### 1. Set Up the Build Environment

Install required dependencies:

```bash
sudo apt-get update -y
sudo apt-get install -y clang clang-tools cmake ninja-build python3
```

Verify that `scan-build` is available:

```bash
scan-build --version || clang --version
which scan-build
```

### 2. Configure Z3 with CMake

Run CMake inside a fresh `build` directory. Use `scan-build` to wrap the CMake configure step so that analysis starts from the configuration phase, then use it again during the actual build:

```bash
mkdir -p build
cd build
scan-build cmake -DCMAKE_BUILD_TYPE=Debug -DCMAKE_EXPORT_COMPILE_COMMANDS=ON -G Ninja ../
```

### 3. Build Z3 with scan-build

Run the build under `scan-build`, directing the HTML report output to a well-known path. Capture both stdout and stderr:

```bash
cd build
scan-build -o /tmp/csa-report --html-title "Z3 CSA Report" ninja 2>&1 | tee /tmp/csa-build.log
cd ..
```

If `scan-build` is not available, try the `clang --analyze` approach via CMake flags as a fallback:

```bash
cd build
cmake -DCMAKE_BUILD_TYPE=Debug \
      -DCMAKE_C_FLAGS="--analyze" \
      -DCMAKE_CXX_FLAGS="--analyze" \
      -G Ninja ../ 2>&1 | tee /tmp/csa-configure.log
ninja 2>&1 | tee /tmp/csa-build.log
cd ..
```

### 4. Collect and Parse Results

After the build, examine the scan-build HTML output directory and build log to extract findings:

```bash
# List generated report directories
ls -la /tmp/csa-report/ 2>/dev/null || echo "No report directory found"

# Find all HTML report files
find /tmp/csa-report -name "*.html" 2>/dev/null | head -50

# Count total number of bugs reported
find /tmp/csa-report -name "report-*.html" 2>/dev/null | wc -l
```

Parse the `index.html` summary if it exists:

```bash
# Extract bug summary from index.html
if [ -f /tmp/csa-report/*/index.html ]; then
    cat /tmp/csa-report/*/index.html
fi
```

Also scan the build log for warnings and errors:

```bash
grep -E "(warning|error|bug).*\[.*\]" /tmp/csa-build.log | head -100
```

### 4.5 Extract Report Content to Text

Extract the full CSA report content into a plain-text file so it can be embedded directly in the GitHub Discussion:

```bash
python3 - << 'PYEOF' > /tmp/csa-extracted.txt 2>&1
import os
import re
import glob
import sys

report_dir = '/tmp/csa-report'
if not os.path.isdir(report_dir):
    print('No CSA report directory found.')
    sys.exit(0)

subdirs = sorted([d for d in os.listdir(report_dir) if os.path.isdir(os.path.join(report_dir, d))])
if not subdirs:
    print('No scan-build output subdirectory found.')
    sys.exit(0)

subdir = os.path.join(report_dir, subdirs[-1])
index_path = os.path.join(subdir, 'index.html')

if os.path.exists(index_path):
    with open(index_path) as f:
        content = f.read()
    print('## Summary Table\n')
    rows = re.findall(r'<tr[^>]*>(.*?)</tr>', content, re.DOTALL)
    for row in rows:
        cells = re.findall(r'<td[^>]*>(.*?)</td>', row, re.DOTALL)
        if cells:
            clean = [re.sub(r'<[^>]+>', '', c).strip() for c in cells]
            line = ' | '.join(c for c in clean if c)
            if line:
                print(line)
    print()

report_files = sorted(glob.glob(os.path.join(subdir, 'report-*.html')))
if report_files:
    print(f'## Individual Findings ({len(report_files)} total)\n')
    for i, rfile in enumerate(report_files, 1):
        with open(rfile) as f:
            rcontent = f.read()
        checker = re.search(r'<td class="CHECKER">(.*?)</td>', rcontent, re.DOTALL)
        filename = re.search(r'<td class="FILENAME">(.*?)</td>', rcontent, re.DOTALL)
        lineno = re.search(r'<td class="LINE">(.*?)</td>', rcontent, re.DOTALL)
        desc = re.search(r'<td class="DESC">(.*?)</td>', rcontent, re.DOTALL)
        c = re.sub(r'<[^>]+>', '', checker.group(1)).strip() if checker else 'unknown'
        fn = re.sub(r'<[^>]+>', '', filename.group(1)).strip() if filename else 'unknown'
        ln = re.sub(r'<[^>]+>', '', lineno.group(1)).strip() if lineno else '?'
        d = re.sub(r'<[^>]+>', '', desc.group(1)).strip() if desc else ''
        print(f'{i}. [{c}] {d}')
        print(f'   File: {fn}, Line: {ln}')
        print()
else:
    print('No individual report files found.')
PYEOF
cat /tmp/csa-extracted.txt
```

### 5. Categorize Findings

Analyze the CSA findings and group them by:

- **Bug type** (e.g., null pointer dereference, use after free, memory leak, uninitialized value, logic error)
- **Severity** (categorize by CSA checker family: `core.*`, `cplusplus.*`, `deadcode.*`, `security.*`, `unix.*`)
- **Source file** (relative path within the Z3 source tree)

Build a structured summary:

1. Total number of findings
2. Breakdown by checker/bug type
3. Top affected files (files with the most findings)
4. Any high-severity issues (null dereferences, memory safety issues)
5. Any new findings compared to cached results from a previous run

### 6. Compare with Cached Results

Check cache memory for results from the previous run:
- Number of findings from the last run
- List of previously reported high-severity issues
- Any issues that have been resolved since the last run

Update cache memory with the current run's results.

### 7. Create GitHub Discussion

Create a GitHub Discussion with a structured report. The discussion title should include the current date and a brief summary (e.g., "[CSA] Weekly Report - N findings").

**Discussion Structure:**

```markdown
# Clang Static Analyzer Report

**Date**: [YYYY-MM-DD]
**Commit**: [Short SHA of HEAD]
**Build type**: Debug (CMake + Ninja)
**Analyzer**: scan-build / clang-analyzer

## Summary

| Metric | Count |
|--------|-------|
| Total findings | N |
| High severity (core.*) | X |
| Memory issues (unix.*, cplusplus.*) | Y |
| Dead code / logic errors | Z |
| Files affected | F |

## Changes Since Last Run

- Findings resolved since last run: [list or "none"]
- New findings introduced: [list or "none"]

## High-Priority Findings

[List the top findings by severity with file paths and checker names]

## Findings by Category

### Core Checkers (Null Dereference, Division by Zero, etc.)
[List findings]

### C++ Specific (Memory Management, Object Lifetime)
[List findings]

### Dead Code and Logic Errors
[List findings]

### Security Checkers
[List findings]

## Top Affected Files

[Table or list of files with the most findings]

## Full CSA Report Content

<details>
<summary>Complete findings extracted from the CSA HTML report (click to expand)</summary>

[PASTE THE ENTIRE CONTENTS OF /tmp/csa-extracted.txt HERE verbatim — do not summarize or paraphrase]

</details>

## Build Log Excerpt

<details>
<summary>Key warnings and errors from the build log (click to expand)</summary>

```
[Relevant excerpt from build log]
```

</details>

## Notes

- This report was generated automatically by the Z3 CSA Analysis workflow.
- False positives may be present; human review is recommended before acting on findings.
- To reproduce locally: `scan-build -o /tmp/csa-report cmake -DCMAKE_BUILD_TYPE=Debug -G Ninja . && scan-build ninja`
```

### 8. Handle Edge Cases

- If `scan-build` is not installed, report the issue clearly and suggest installing `clang-tools` or `clang-analyzer`.
- If the build fails entirely (not just with warnings), report the build failure and exit gracefully without creating a misleading discussion.
- If zero findings are reported, still create the discussion celebrating the clean result.
- If the discussion would be identical to the previous one (no changes), consider skipping creation unless it has been more than 2 weeks since the last run.

## Guidelines

- **Be thorough**: Parse all available output from scan-build, not just the summary.
- **Be accurate**: Clearly distinguish between true positives and likely false positives.
- **Be actionable**: For each high-priority finding, include the file, line number, and a brief description.
- **Be concise**: The discussion should be readable; use collapsible sections for verbose output.
- **Track progress**: Use cache memory to detect regressions (new findings) and improvements (resolved findings) over time.
- **Respect build time**: The build may take 15-20 minutes; use ninja with available cores.

## Important Notes

- **DO NOT** create pull requests or modify source files.
- **DO NOT** attempt to fix the findings automatically.
- **DO** close older CSA discussions automatically (this is configured via `close-older-discussions: true`).
- **DO** always report the commit SHA so findings can be correlated with specific code versions.
- **DO** use cache memory to track trends over multiple runs.
