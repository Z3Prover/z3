---
description: Benchmark Z3 seq vs nseq string solvers on QF_S test suite from the c3 branch and post results as a GitHub discussion

on:
  schedule:
    - cron: "0 0,12 * * *"
  workflow_dispatch:

permissions: read-all

network: defaults

tools:
  bash: true
  github:
    toolsets: [default]

safe-outputs:
  create-discussion:
    title-prefix: "[QF_S Benchmark] "
    category: "Agentic Workflows"
    close-older-discussions: true
  missing-tool:
    create-issue: true
  noop:
    report-as-issue: false

timeout-minutes: 120

steps:
  - name: Checkout c3 branch
    uses: actions/checkout@v6.0.2
    with:
      ref: c3
      fetch-depth: 1
      persist-credentials: false

---

# QF_S String Solver Benchmark

## Job Description

Your name is ${{ github.workflow }}. You are an expert performance analyst for the Z3 theorem prover, specializing in the string/sequence theory. Your task is to benchmark the `seq` solver (classical string theory) against the `nseq` solver (ZIPT-based string theory) on the QF_S test suite from the `c3` branch, and post a structured report as a GitHub Discussion.

The workspace already contains the `c3` branch (checked out by the preceding workflow step).

## Phase 1: Set Up the Build Environment

Install required build tools:

```bash
sudo apt-get update -y
sudo apt-get install -y cmake ninja-build python3 python3-pip time
```

Verify tools:

```bash
cmake --version
ninja --version
python3 --version
```

## Phase 2: Build Z3 in Release Mode

Build Z3 in Release mode for accurate benchmark performance numbers and lower memory usage. Running `ninja` in the background with `&` is not allowed — concurrent C++ compilation and LLM inference can exhaust available RAM and kill the agent process.

```bash
mkdir -p /tmp/z3-build
cd /tmp/z3-build
cmake "$GITHUB_WORKSPACE" \
  -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DZ3_BUILD_TEST_EXECUTABLES=OFF \
  2>&1 | tee /tmp/z3-cmake.log
ninja -j2 z3 2>&1 | tee /tmp/z3-build.log
```

Verify the binary was built:

```bash
/tmp/z3-build/z3 --version
```

If the build fails, report it immediately and stop.

Once the binary is confirmed working, call the `noop` safe-output tool with the message `"Z3 built successfully from the c3 branch. Benchmark starting — results will be posted as a GitHub Discussion once complete."` This keepalive call refreshes the safe-output MCP session before the long benchmark run begins, preventing a session timeout.

## Phase 3: Discover QF_S Benchmark Files

Find all `.smt2` benchmark files in the workspace that belong to the QF_S logic:

```bash
# Search for explicit QF_S logic declarations
grep -rl 'QF_S' "$GITHUB_WORKSPACE" --include='*.smt2' 2>/dev/null > /tmp/qf_s_files.txt

# Also look in dedicated benchmark directories
find "$GITHUB_WORKSPACE" \
  \( -path "*/QF_S/*" -o -path "*/qf_s/*" -o -path "*/benchmarks/*" \) \
  -name '*.smt2' 2>/dev/null >> /tmp/qf_s_files.txt

# Deduplicate
sort -u /tmp/qf_s_files.txt -o /tmp/qf_s_files.txt

TOTAL=$(wc -l < /tmp/qf_s_files.txt)
echo "Found $TOTAL QF_S benchmark files"
head -20 /tmp/qf_s_files.txt
```

If fewer than 5 files are found, also scan the entire workspace for any `.smt2` file that exercises string constraints:

```bash
if [ "$TOTAL" -lt 5 ]; then
  grep -rl 'declare.*String\|str\.\|seq\.' "$GITHUB_WORKSPACE" \
    --include='*.smt2' 2>/dev/null >> /tmp/qf_s_files.txt
  sort -u /tmp/qf_s_files.txt -o /tmp/qf_s_files.txt
  TOTAL=$(wc -l < /tmp/qf_s_files.txt)
  echo "After extended search: $TOTAL files"
fi
```

Cap the benchmark set to keep total runtime under 60 minutes:

```bash
# Use at most 300 files; take a random sample if more are available
if [ "$TOTAL" -gt 300 ]; then
  shuf -n 300 /tmp/qf_s_files.txt > /tmp/qf_s_sample.txt
else
  cp /tmp/qf_s_files.txt /tmp/qf_s_sample.txt
fi
SAMPLE=$(wc -l < /tmp/qf_s_sample.txt)
echo "Running benchmarks on $SAMPLE files"
```

## Phase 4: Run Benchmarks — seq vs nseq

Run each benchmark with both solvers. Use a per-file timeout of 5 seconds. Set Z3's internal timeout to 4 seconds so it exits cleanly before the shell timeout fires.

```bash
Z3=/tmp/z3-build/z3
TIMEOUT_SEC=5
Z3_TIMEOUT_SEC=4
RESULTS=/tmp/benchmark-results.csv

echo "file,seq_result,seq_time_ms,nseq_result,nseq_time_ms" > "$RESULTS"

total=0
done_count=0
while IFS= read -r smt_file; do
  total=$((total + 1))

  # Run with seq solver; capture both stdout (z3 output) and stderr (time output)
  SEQ_OUT=$({ time timeout "$TIMEOUT_SEC" "$Z3" \
    smt.string_solver=seq \
    -T:"$Z3_TIMEOUT_SEC" \
    "$smt_file" 2>/dev/null; } 2>&1)
  SEQ_RESULT=$(echo "$SEQ_OUT" | grep -E '^(sat|unsat|unknown)' | head -1)
  SEQ_MS=$(echo "$SEQ_OUT" | grep real | awk '{split($2,a,"m"); split(a[2],b,"s"); printf "%d", (a[1]*60+b[1])*1000}')
  [ -z "$SEQ_RESULT" ] && SEQ_RESULT="timeout"
  [ -z "$SEQ_MS" ] && SEQ_MS=$((TIMEOUT_SEC * 1000))

  # Run with nseq solver; same structure
  NSEQ_OUT=$({ time timeout "$TIMEOUT_SEC" "$Z3" \
    smt.string_solver=nseq \
    -T:"$Z3_TIMEOUT_SEC" \
    "$smt_file" 2>/dev/null; } 2>&1)
  NSEQ_RESULT=$(echo "$NSEQ_OUT" | grep -E '^(sat|unsat|unknown)' | head -1)
  NSEQ_MS=$(echo "$NSEQ_OUT" | grep real | awk '{split($2,a,"m"); split(a[2],b,"s"); printf "%d", (a[1]*60+b[1])*1000}')
  [ -z "$NSEQ_RESULT" ] && NSEQ_RESULT="timeout"
  [ -z "$NSEQ_MS" ] && NSEQ_MS=$((TIMEOUT_SEC * 1000))

  SHORT=$(basename "$smt_file")
  echo "$SHORT,$SEQ_RESULT,$SEQ_MS,$NSEQ_RESULT,$NSEQ_MS" >> "$RESULTS"

  done_count=$((done_count + 1))
  if [ $((done_count % 50)) -eq 0 ]; then
    echo "Progress: $done_count / $SAMPLE files completed"
  fi
done < /tmp/qf_s_sample.txt

echo "Benchmark run complete: $done_count files"
```

## Phase 5: Collect Seq Traces for Interesting Cases

For benchmarks where `seq` solves in under 2 s but `nseq` times out (seq-fast/nseq-slow cases), collect a brief `seq` trace to understand what algorithm is used:

```bash
Z3=/tmp/z3-build/z3
mkdir -p /tmp/traces

# Find seq-fast / nseq-slow files: seq solved (sat/unsat) in <2000ms AND nseq timed out
awk -F, 'NR>1 && ($2=="sat"||$2=="unsat") && $3<2000 && $4=="timeout" {print $1}' \
  /tmp/benchmark-results.csv > /tmp/seq_fast_nseq_slow.txt
echo "seq-fast / nseq-slow files: $(wc -l < /tmp/seq_fast_nseq_slow.txt)"

# Collect traces for at most 5 such cases
head -5 /tmp/seq_fast_nseq_slow.txt | while IFS= read -r short; do
  # Find the full path
  full=$(grep "/$short$" /tmp/qf_s_sample.txt | head -1)
  [ -z "$full" ] && continue
  timeout 5 "$Z3" \
    smt.string_solver=seq \
    -tr:seq \
    -T:5 \
    "$full" > "/tmp/traces/${short%.smt2}.seq.trace" 2>&1 || true
done
```

## Phase 6: Analyze Results

Compute summary statistics from the CSV. Save the analysis script to a file and run it:

```bash
cat > /tmp/analyze_benchmark.py << 'PYEOF'
import csv, sys

results = []
with open('/tmp/benchmark-results.csv') as f:
    reader = csv.DictReader(f)
    for row in reader:
        results.append(row)

total = len(results)
if total == 0:
    print("No results found.")
    sys.exit(0)

def is_correct(r, solver):
    prefix = 'seq' if solver == 'seq' else 'nseq'
    return r[f'{prefix}_result'] in ('sat', 'unsat')

def timed_out(r, solver):
    prefix = 'seq' if solver == 'seq' else 'nseq'
    return r[f'{prefix}_result'] == 'timeout'

seq_solved  = sum(1 for r in results if is_correct(r, 'seq'))
nseq_solved = sum(1 for r in results if is_correct(r, 'nseq'))
seq_to      = sum(1 for r in results if timed_out(r, 'seq'))
nseq_to     = sum(1 for r in results if timed_out(r, 'nseq'))

seq_times  = [int(r['seq_time_ms'])  for r in results if is_correct(r, 'seq')]
nseq_times = [int(r['nseq_time_ms']) for r in results if is_correct(r, 'nseq')]

def median(lst):
    s = sorted(lst)
    n = len(s)
    return s[n//2] if n else 0

def mean(lst):
    return sum(lst)//len(lst) if lst else 0

# Disagreements (sat vs unsat or vice-versa)
disagreements = [
    r for r in results
    if r['seq_result'] in ('sat','unsat')
    and r['nseq_result'] in ('sat','unsat')
    and r['seq_result'] != r['nseq_result']
]

# seq-fast / nseq-slow: seq solved in <2s, nseq timed out
seq_fast_nseq_slow = [
    r for r in results
    if is_correct(r, 'seq') and int(r['seq_time_ms']) < 2000 and timed_out(r, 'nseq')
]
# nseq-fast / seq-slow: nseq solved in <2s, seq timed out
nseq_fast_seq_slow = [
    r for r in results
    if is_correct(r, 'nseq') and int(r['nseq_time_ms']) < 2000 and timed_out(r, 'seq')
]

print(f"TOTAL={total}")
print(f"SEQ_SOLVED={seq_solved}")
print(f"NSEQ_SOLVED={nseq_solved}")
print(f"SEQ_TIMEOUTS={seq_to}")
print(f"NSEQ_TIMEOUTS={nseq_to}")
print(f"SEQ_MEDIAN_MS={median(seq_times)}")
print(f"NSEQ_MEDIAN_MS={median(nseq_times)}")
print(f"SEQ_MEAN_MS={mean(seq_times)}")
print(f"NSEQ_MEAN_MS={mean(nseq_times)}")
print(f"DISAGREEMENTS={len(disagreements)}")
print(f"SEQ_FAST_NSEQ_SLOW={len(seq_fast_nseq_slow)}")
print(f"NSEQ_FAST_SEQ_SLOW={len(nseq_fast_seq_slow)}")

# Print top-10 slowest for nseq that seq handles fast
print("\nTOP_SEQ_FAST_NSEQ_SLOW:")
for r in sorted(seq_fast_nseq_slow, key=lambda x: -int(x['nseq_time_ms']))[:10]:
    print(f"  {r['file']}  seq={r['seq_time_ms']}ms  nseq={r['nseq_time_ms']}ms  seq_result={r['seq_result']}  nseq_result={r['nseq_result']}")

print("\nTOP_NSEQ_FAST_SEQ_SLOW:")
for r in sorted(nseq_fast_seq_slow, key=lambda x: -int(x['seq_time_ms']))[:10]:
    print(f"  {r['file']}  seq={r['seq_time_ms']}ms  nseq={r['nseq_time_ms']}ms  seq_result={r['seq_result']}  nseq_result={r['nseq_result']}")

if disagreements:
    print(f"\nDISAGREEMENTS ({len(disagreements)}):")
    for r in disagreements[:10]:
        print(f"  {r['file']}  seq={r['seq_result']}  nseq={r['nseq_result']}")
PYEOF

python3 /tmp/analyze_benchmark.py
```

## Phase 7: Create GitHub Discussion

Use the `create_discussion` safe-output tool to post a structured benchmark report.

The discussion body should be formatted as follows (fill in real numbers from Phase 6):

```markdown
# QF_S Benchmark: seq vs nseq

**Date**: YYYY-MM-DD
**Branch**: c3
**Commit**: `<short SHA>`
**Workflow Run**: [#<run_id>](https://github.com/${{ github.repository }}/actions/runs/${{ github.run_id }})
**Files benchmarked**: N (capped at 300, timeout 5 s per file)

---

## Summary

| Metric | seq | nseq |
|--------|-----|------|
| Files solved (sat/unsat) | SEQ_SOLVED | NSEQ_SOLVED |
| Timeouts | SEQ_TO | NSEQ_TO |
| Median solve time (solved files) | X ms | Y ms |
| Mean solve time (solved files) | X ms | Y ms |
| **Disagreements (sat≠unsat)** | — | N |

---

## Performance Comparison

### seq-fast / nseq-slow (seq < 2 s, nseq timed out)

These are benchmarks where the classical `seq` solver is significantly faster. These represent regression risk for `nseq`.

| File | seq (ms) | nseq (ms) | seq result | nseq result |
|------|----------|-----------|------------|-------------|
[TOP 10 ENTRIES]

### nseq-fast / seq-slow (nseq < 2 s, seq timed out)

These are benchmarks where `nseq` shows a performance advantage.

| File | seq (ms) | nseq (ms) | seq result | nseq result |
|------|----------|-----------|------------|-------------|
[TOP 10 ENTRIES]

---

## Correctness

**Disagreements** (files where seq says `sat` but nseq says `unsat` or vice versa): N

[If disagreements exist, list all of them here with file paths and both results]

---

## seq Trace Analysis (seq-fast / nseq-slow cases)

<details>
<summary>Click to expand trace snippets for top seq-fast/nseq-slow cases</summary>

[Insert trace snippet for each traced file, or "No traces collected" if section was skipped]

</details>

---

## Raw Data

<details>
<summary>Full results CSV (click to expand)</summary>

```csv
[PASTE FIRST 200 LINES OF /tmp/benchmark-results.csv]
```

</details>

---

*Generated by the QF_S Benchmark workflow. To reproduce: build Z3 from the `c3` branch and run `z3 smt.string_solver=seq|nseq -T:10 <file.smt2>`.*
```

## Edge Cases

- If the build fails, call `missing_data` explaining the build error and stop.
- If no benchmark files are found at all, call `missing_data` explaining that no QF_S `.smt2` files were found in the `c3` branch.
- If Z3 crashes (segfault) on a file with either solver, record the result as `crash` and continue.
- If the total benchmark set is very small (< 5 files), note this prominently in the discussion and suggest adding more QF_S benchmarks to the `c3` branch.
- If zero disagreements and both solvers time out on the same files, note that the solvers are in agreement.
- If `create_discussion` fails (e.g., MCP session error), call `report_incomplete` with the reason and include the top-line statistics (files solved, timeouts, disagreement count) in the `details` field.

## Important Notes

- **DO NOT** modify any source files or create pull requests.
- **DO NOT** run `ninja` or any build command in the background with `&` — concurrent C++ compilation and LLM inference can exhaust available RAM and kill the agent process. Always wait for build commands to complete before proceeding.
- **DO NOT** run benchmarks for longer than 100 minutes total (leave buffer for posting).
- **DO** always report the commit SHA so results can be correlated with specific code versions.
- **DO** close older QF_S Benchmark discussions automatically (configured via `close-older-discussions: true`).
- **DO** highlight disagreements prominently — these are potential correctness bugs.
