---
description: >
  Weekly benchmark of Z3's TPTP front-end against 500 random TPTP problems.
  Downloads TPTP benchmarks from tptp.org, resolves axiom dependencies,
  skips large problems, runs each with a 5-second timeout, and posts a
  discrepancy/crash report as a GitHub discussion.

on:
  schedule:
    - cron: "0 6 * * 1"
  workflow_dispatch:

permissions: read-all

network:
  allowed:
    - defaults
    - tptp.org

tools:
  bash: true
  github:
    toolsets: [default]

safe-outputs:
  report-failure-as-issue: false
  create-discussion:
    title-prefix: "[TPTP Benchmark] "
    category: "Agentic Workflows"
    close-older-discussions: true
    expires: 14d
  missing-tool:
    create-issue: true
  noop:
    report-as-issue: false

timeout-minutes: 300

steps:
  - name: Checkout repository
    uses: actions/checkout@v6.0.2
    with:
      persist-credentials: false

  - name: Install build dependencies
    run: |
      sudo apt-get update -y -q
      sudo apt-get install -y cmake ninja-build python3 wget curl bc

  - name: Build Z3
    run: |
      mkdir -p /tmp/z3-build
      cd /tmp/z3-build
      cmake "$GITHUB_WORKSPACE" \
        -G Ninja \
        -DCMAKE_BUILD_TYPE=Release \
        -DZ3_BUILD_TEST_EXECUTABLES=OFF
      ninja -j$(nproc) z3
      ./z3 --version

---

# TPTP Front-End Benchmark

## Job Description

Your name is ${{ github.workflow }}. You are an expert testing engineer for the Z3 theorem prover. Your task is to:

1. Verify the Z3 binary built by the pre-flight step is available
2. Download the TPTP benchmark library from tptp.org
3. Select 500 random small-to-medium problems (with their axiom dependencies)
4. Run each problem through Z3's TPTP front-end with a 5-second timeout
5. Compare Z3's output against the expected SZS status declared in each problem file
6. Post a detailed report as a GitHub Discussion summarising discrepancies and crashes

**Repository**: ${{ github.repository }}
**Workspace**: ${{ github.workspace }}

## Phase 1: Verify Z3 Binary

Z3 was built by the workflow pre-flight step and is available at `/tmp/z3-build/z3`.
Confirm the binary is present and functional:

```bash
/tmp/z3-build/z3 --version
```

If the binary is missing or returns an error, call the `noop` safe-output with a message describing the problem and stop.

Once confirmed, call `noop` with `"Z3 binary verified. Downloading TPTP benchmark library — this may take a few minutes."` to keep the safe-output session alive.

## Phase 2: Download the TPTP Problem Library

Find the latest TPTP release and download the full archive.

```bash
# Find the latest TPTP distribution version by fetching the directory listing
TPTP_DIST_URL="https://tptp.org/TPTP/Distribution/"
LATEST_TGZ=$(curl -sL "$TPTP_DIST_URL" \
  | grep -oP 'TPTP-v[0-9]+\.[0-9]+\.[0-9]+\.tgz' \
  | sort -V | tail -1)

if [ -z "$LATEST_TGZ" ]; then
  echo "ERROR: Could not determine latest TPTP version from $TPTP_DIST_URL"
  # Fall back to a known stable version
  LATEST_TGZ="TPTP-v9.0.0.tgz"
fi

echo "Downloading $LATEST_TGZ ..."
mkdir -p /tmp/tptp_download
wget -q --show-progress \
  "${TPTP_DIST_URL}${LATEST_TGZ}" \
  -O /tmp/tptp_download/tptp.tgz

echo "Extracting TPTP library..."
mkdir -p /tmp/tptp
tar -xzf /tmp/tptp_download/tptp.tgz -C /tmp/tptp --strip-components=1 2>&1 | tail -5

# Verify extraction
if [ ! -d /tmp/tptp/Problems ] || [ ! -d /tmp/tptp/Axioms ]; then
  echo "ERROR: TPTP extraction failed — Problems/ or Axioms/ directory not found"
  ls /tmp/tptp/
  exit 1
fi

TPTP_ROOT=/tmp/tptp
echo "TPTP library extracted to $TPTP_ROOT"
echo "Problem domains available:"
ls "$TPTP_ROOT/Problems/" | wc -l
echo "Axiom files available:"
ls "$TPTP_ROOT/Axioms/" | wc -l
```

If the download or extraction fails, call `noop` with the error details and stop.

Call `noop` with `"TPTP library downloaded and extracted. Selecting 500 benchmark problems — filtering by size."` to keep the session alive.

## Phase 3: Select 500 Benchmark Problems

Filter out large problems and problems that depend on large axiom files, then take a random sample of 500.

Save this script to `/tmp/select_benchmarks.py` and run it:

```python
#!/usr/bin/env python3
"""
Select 500 random TPTP problems that:
  - Have a known, conclusive expected status (Theorem, Unsatisfiable,
    CounterSatisfiable, Satisfiable) OR Unknown/Open status.
  - Are not "large" (problem file <= 50 KB).
  - Do not include any axiom file larger than 100 KB.
"""
import os
import re
import random
import sys

TPTP_ROOT = "/tmp/tptp"
PROBLEMS_DIR = os.path.join(TPTP_ROOT, "Problems")
AXIOMS_DIR = os.path.join(TPTP_ROOT, "Axioms")
MAX_PROBLEM_SIZE = 50 * 1024      # 50 KB
MAX_AXIOM_SIZE   = 100 * 1024     # 100 KB
SAMPLE_SIZE = 500
OUTPUT_FILE = "/tmp/selected_benchmarks.txt"

include_re = re.compile(r"include\s*\(\s*['\"]([^'\"]+)['\"]", re.IGNORECASE)
status_re  = re.compile(r"%\s*Status\s*:\s*(\S+)", re.IGNORECASE)

def axiom_sizes_ok(problem_path):
    """Return True if all included axiom files exist and are <= MAX_AXIOM_SIZE."""
    try:
        with open(problem_path, encoding="utf-8", errors="replace") as f:
            content = f.read(4096)   # header is in first few KB
    except OSError:
        return False
    for m in include_re.finditer(content):
        axiom_rel = m.group(1)        # e.g. "Axioms/AGT001+0.ax"
        axiom_path = os.path.join(TPTP_ROOT, axiom_rel)
        if not os.path.exists(axiom_path):
            return False              # axiom missing — skip
        if os.path.getsize(axiom_path) > MAX_AXIOM_SIZE:
            return False              # axiom too large — skip
    return True

candidates = []
skipped_size = 0
skipped_axiom = 0

for domain in sorted(os.listdir(PROBLEMS_DIR)):
    domain_dir = os.path.join(PROBLEMS_DIR, domain)
    if not os.path.isdir(domain_dir):
        continue
    for fname in os.listdir(domain_dir):
        if not fname.endswith(".p"):
            continue
        fpath = os.path.join(domain_dir, fname)
        size = os.path.getsize(fpath)
        if size > MAX_PROBLEM_SIZE:
            skipped_size += 1
            continue
        if not axiom_sizes_ok(fpath):
            skipped_axiom += 1
            continue
        candidates.append(fpath)

print(f"Total candidates (after filtering): {len(candidates)}", flush=True)
print(f"  Skipped — problem too large : {skipped_size}", flush=True)
print(f"  Skipped — axiom too large   : {skipped_axiom}", flush=True)

if len(candidates) == 0:
    print("ERROR: No suitable benchmark problems found.", file=sys.stderr)
    sys.exit(1)

if len(candidates) > SAMPLE_SIZE:
    random.seed(42)
    selected = random.sample(candidates, SAMPLE_SIZE)
else:
    selected = candidates

selected.sort()
with open(OUTPUT_FILE, "w") as f:
    f.write("\n".join(selected) + "\n")

print(f"Selected {len(selected)} problems → {OUTPUT_FILE}", flush=True)
```

Run the script:

```bash
python3 /tmp/select_benchmarks.py
SELECTED=$(wc -l < /tmp/selected_benchmarks.txt)
echo "Benchmark set: $SELECTED problems"
```

If no problems are found, call `noop` with an error message and stop.

Call `noop` with `"$SELECTED problems selected. Starting benchmark run with 5-second timeout per problem — this will take approximately $(( SELECTED * 7 / 60 )) minutes."` to keep the session alive.

## Phase 4: Run Benchmarks

Save the following script to `/tmp/run_tptp_benchmarks.sh`, make it executable, and run it.

```bash
#!/usr/bin/env bash
set -euo pipefail

Z3=/tmp/z3-build/z3
TPTP_ROOT=/tmp/tptp
TIMEOUT_HARD=8        # outer OS-level guard (seconds; 3 s beyond Z3's -T:5)
Z3_TIMEOUT=5          # Z3 internal timeout: -T:N sets N-second limit (uppercase -T is seconds)

RESULTS=/tmp/tptp_results.tsv
PROBLEM_LIST=/tmp/selected_benchmarks.txt

echo -e "file\texpected\tactual\ttime_s\tnotes" > "$RESULTS"

# Helper: extract the expected SZS status from the TPTP problem header.
get_expected_status() {
    local file="$1"
    # Look for lines like: "% Status   : Theorem"
    grep -m1 -iP '%\s*Status\s*:\s*\K\S+' "$file" 2>/dev/null || echo "Unknown"
}

# Helper: run z3 on a single TPTP problem with timeout.
run_benchmark() {
    local file="$1"
    local start end elapsed output exit_code verdict

    start=$(date +%s%3N)    # milliseconds since epoch
    output=$(TPTP="$TPTP_ROOT" timeout "$TIMEOUT_HARD" \
        "$Z3" -tptp -T:"$Z3_TIMEOUT" "$file" 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}
    end=$(date +%s%3N)
    elapsed=$(echo "scale=3; ($end - $start) / 1000" | bc)

    # Extract SZS status line from output
    szs_line=$(echo "$output" | grep -m1 "% SZS status" || true)

    if [ -n "$szs_line" ]; then
        # Parse the status keyword (e.g. "Theorem", "CounterSatisfiable", "GaveUp")
        verdict=$(echo "$szs_line" | grep -oP '% SZS status \K\S+' || echo "Unknown")
    elif [ "$exit_code" -eq 124 ]; then
        verdict="Timeout"
    elif [ "$exit_code" -ne 0 ]; then
        verdict="Crash"
    else
        verdict="NoOutput"
    fi

    echo "$verdict $elapsed"
}

COUNTER=0
TOTAL=$(wc -l < "$PROBLEM_LIST")

while IFS= read -r problem_file; do
    COUNTER=$((COUNTER + 1))

    expected=$(get_expected_status "$problem_file")
    result_line=$(run_benchmark "$problem_file")
    actual=$(echo "$result_line" | cut -d' ' -f1)
    elapsed=$(echo "$result_line" | cut -d' ' -f2)
    fname=$(basename "$problem_file")

    # Classify notes
    notes=""
    # Soundness discrepancy: both answers are conclusive but conflict
    conclusive_expected=false
    conclusive_actual=false
    case "$expected" in
        Theorem|Unsatisfiable)     conclusive_expected=true ;;
        Satisfiable|CounterSatisfiable) conclusive_expected=true ;;
    esac
    case "$actual" in
        Theorem|Unsatisfiable)     conclusive_actual=true ;;
        Satisfiable|CounterSatisfiable) conclusive_actual=true ;;
    esac

    if $conclusive_expected && $conclusive_actual; then
        # Map expected to the Z3 output equivalents for comparison
        # Theorem (has-conjecture unsat) matches "Theorem"
        # Unsatisfiable (no-conjecture unsat) matches "Unsatisfiable"
        # Satisfiable (no-conjecture sat) matches "Satisfiable"
        # CounterSatisfiable (has-conjecture sat) matches "CounterSatisfiable"
        if [ "$expected" != "$actual" ]; then
            # Check for sat/unsat polarity conflict
            sat_expected=false; sat_actual=false
            case "$expected" in Satisfiable|CounterSatisfiable) sat_expected=true ;; esac
            case "$actual"   in Satisfiable|CounterSatisfiable) sat_actual=true   ;; esac
            if [ "$sat_expected" != "$sat_actual" ]; then
                notes="SOUNDNESS_ERROR"
            else
                notes="STATUS_MISMATCH"
            fi
        fi
    fi

    if [ "$actual" = "Crash" ]; then
        notes="CRASH"
    fi

    echo -e "$fname\t$expected\t$actual\t$elapsed\t$notes" >> "$RESULTS"

    if [ -n "$notes" ]; then
        echo "[$COUNTER/$TOTAL] $fname  expected=$expected  actual=$actual  time=${elapsed}s  *** $notes ***"
    elif [ $((COUNTER % 50)) -eq 0 ]; then
        echo "[$COUNTER/$TOTAL] Progress checkpoint  last=$fname  actual=$actual  time=${elapsed}s"
    fi

done < "$PROBLEM_LIST"

echo "Benchmark run complete: $COUNTER problems processed. Results → $RESULTS"
```

Run it:

```bash
chmod +x /tmp/run_tptp_benchmarks.sh
/tmp/run_tptp_benchmarks.sh
```

Do not skip any file in the list.

## Phase 5: Analyze Results

Save the following script to `/tmp/analyze_tptp.py` and run it:

```python
#!/usr/bin/env python3
"""Compute summary statistics from the TPTP benchmark TSV."""
import csv

RESULTS_FILE = "/tmp/tptp_results.tsv"

rows = []
with open(RESULTS_FILE, newline="") as f:
    reader = csv.DictReader(f, delimiter="\t")
    for row in reader:
        rows.append(row)

total = len(rows)

# Verdict counts
from collections import Counter, defaultdict
actual_counts = Counter(r["actual"] for r in rows)
expected_counts = Counter(r["expected"] for r in rows)

# Flagged rows
soundness_errors = [r for r in rows if r["notes"] == "SOUNDNESS_ERROR"]
status_mismatches = [r for r in rows if r["notes"] == "STATUS_MISMATCH"]
crashes           = [r for r in rows if r["notes"] == "CRASH"]
timeouts          = [r for r in rows if r["actual"] == "Timeout"]
gave_up           = [r for r in rows if r["actual"] == "GaveUp"]

# Solved correctly (expected matches actual for conclusive verdicts)
conclusive_expected = {"Theorem", "Unsatisfiable", "Satisfiable", "CounterSatisfiable"}
correct = [r for r in rows
           if r["expected"] in conclusive_expected
           and r["actual"] == r["expected"]]

print(f"TOTAL={total}")
print(f"CORRECT={len(correct)}")
print(f"TIMEOUTS={len(timeouts)}")
print(f"GAVE_UP={len(gave_up)}")
print(f"CRASHES={len(crashes)}")
print(f"SOUNDNESS_ERRORS={len(soundness_errors)}")
print(f"STATUS_MISMATCHES={len(status_mismatches)}")

print("\n--- Actual verdict breakdown ---")
for v, c in sorted(actual_counts.items()):
    print(f"  {v}: {c}")

print("\n--- Expected status breakdown ---")
for v, c in sorted(expected_counts.items()):
    print(f"  {v}: {c}")

if soundness_errors:
    print(f"\n--- SOUNDNESS ERRORS ({len(soundness_errors)}) ---")
    for r in soundness_errors:
        print(f"  {r['file']}  expected={r['expected']}  actual={r['actual']}")

if crashes:
    print(f"\n--- CRASHES ({len(crashes)}) ---")
    for r in crashes:
        print(f"  {r['file']}  expected={r['expected']}")

if status_mismatches:
    print(f"\n--- STATUS MISMATCHES ({len(status_mismatches)}) ---")
    for r in status_mismatches[:20]:
        print(f"  {r['file']}  expected={r['expected']}  actual={r['actual']}")
```

Run the analysis:

```bash
python3 /tmp/analyze_tptp.py
```

## Phase 6: Generate and Post the Discussion Report

Read the TSV at `/tmp/tptp_results.tsv` and the analysis output, then compose a Markdown report and call `create_discussion`.

The report should use `###` or lower for all headers (never `#` or `##`). Use collapsible `<details>` sections for large tables.

Use this structure:

```markdown
**Date**: <today's date>
**Branch**: master
**Commit**: `<short SHA>` (run `git rev-parse --short HEAD` in ${{ github.workspace }} to get the SHA)
**Workflow Run**: [${{ github.run_id }}](https://github.com/${{ github.repository }}/actions/runs/${{ github.run_id }})
**TPTP version**: <downloaded version>
**Problems benchmarked**: <N> (random sample, timeout 5 s per problem)

---

### Summary

| Metric | Count |
|--------|-------|
| Total problems run | N |
| Correct (expected = actual) | N |
| Timeouts | N |
| GaveUp (within time budget) | N |
| Crashes / errors | N |
| Soundness errors (sat↔unsat conflict) | N |
| Status mismatches (Theorem vs Unsatisfiable etc.) | N |

### Expected Status Distribution

| Expected Status | Count |
|----------------|-------|
| Theorem | N |
| Unsatisfiable | N |
| Satisfiable | N |
| CounterSatisfiable | N |
| Unknown / Open | N |

---

### ⚠️ Critical: Soundness Errors

[List ALL files where Z3 returned a conclusive answer that contradicts the expected answer
(e.g., expected Theorem but got CounterSatisfiable). If none, write "None detected."]

### 💥 Crashes

[List ALL files where Z3 crashed (non-zero exit, no SZS output, not a timeout).
Include filename and expected status. If none, write "None detected."]

### Status Mismatches

[Files where both answers are conclusive but differ in Theorem vs Unsatisfiable polarity
(e.g., expected Theorem but actual Unsatisfiable). These may indicate conjecture-handling
differences rather than soundness bugs. If none, write "None detected."]

---

<details>
<summary>View all Timeouts (problems where Z3 exceeded the 5-second limit)</summary>

| # | File | Expected Status |
|---|------|----------------|
[First 100 timeout rows]

</details>

<details>
<summary>View full per-problem results table</summary>

| # | File | Expected | Actual | Time (s) | Notes |
|---|------|----------|--------|----------|-------|
[All rows, or first 500 if over limit]

</details>

---

### Recommendations

[Based on the findings, list actionable items. E.g.: investigate soundness errors,
file crash bugs, note domains where Z3 consistently times out.]
```

Post the discussion using the `create_discussion` safe output. The title should be
`[TPTP Benchmark] master — <date>`.

## Safe Output Guarantee

You **MUST** call either `create_discussion` or `noop` before the workflow ends:

- **Full success**: Call `create_discussion` with the complete report.
- **Partial results** (some problems ran): Call `create_discussion` with whatever results are available and a note about incomplete execution.
- **Download failure**: Call `noop` with the download error details.
- **No problems selected**: Call `noop` explaining why no problems were found.
- **Binary missing**: If `/tmp/z3-build/z3` is unexpectedly absent, call `noop` with that detail and stop.

## Important Notes

- **Build failure handling**: Z3 was built before the agent loaded. If the binary is missing or non-functional, call `noop` with the error and stop.
- **TPTP environment variable**: Set `TPTP=/tmp/tptp` when invoking `z3 -tptp` so that `include()` directives in problem files resolve correctly against the downloaded Axioms directory.
- **Timeout detection**: Use `timeout 8` as the outer OS-level guard (3 seconds beyond Z3's `-T:5`) to allow Z3 to exit cleanly before the shell kills it. If the exit code from `timeout` is 124, record the verdict as `Timeout`.
- **Crash detection**: A crash is a non-zero exit code with no `% SZS status` line in the output and no timeout. Record it separately from `GaveUp`.
- **SZS status semantics**: Z3 outputs `Theorem` (not `Unsatisfiable`) when it proves a conjecture; `CounterSatisfiable` (not `Satisfiable`) when it finds a counterexample to a conjecture. A status mismatch between `Theorem` and `Unsatisfiable` for the same problem may be innocuous and depends on whether the problem file uses a conjecture formula.
- **Report soundness bugs prominently**: Any case where the polarity of the answer conflicts (expected Theorem/Unsatisfiable but got CounterSatisfiable/Satisfiable, or vice versa) is a potential soundness bug and must be highlighted as critical.
- **Keep progress log**: Print a line for every flagged result and every 50th problem so the workflow log shows progress.
- **Close older discussions**: Configured via `close-older-discussions: true`. Only the latest weekly report remains open.
