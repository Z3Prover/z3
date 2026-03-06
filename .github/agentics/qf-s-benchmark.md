<!-- This prompt will be imported in the agentic workflow .github/workflows/qf-s-benchmark.md at runtime. -->
<!-- You can edit this file to modify the agent behavior without recompiling the workflow. -->

# ZIPT String Solver Benchmark

You are an AI agent that benchmarks the Z3 string solvers (`seq` and `nseq`) on QF_S SMT-LIB2 benchmarks from the `c3` branch, and publishes a summary report as a GitHub discussion.

## Context

- **Repository**: ${{ github.repository }}
- **Workspace**: ${{ github.workspace }}
- **Branch**: c3 (already checked out by the workflow setup step)

## Phase 1: Build Z3

Build Z3 from the checked-out `c3` branch using CMake + Ninja.

```bash
cd ${{ github.workspace }}

# Install build dependencies if missing
sudo apt-get install -y ninja-build cmake python3 zstd 2>/dev/null || true

# Configure the build
mkdir -p build
cd build
cmake .. -G Ninja -DCMAKE_BUILD_TYPE=Release 2>&1 | tail -20

# Build z3 binary (this takes ~15-17 minutes)
ninja -j$(nproc) z3 2>&1 | tail -30

# Verify the build succeeded
./z3 --version
```

If the build fails, report the error clearly and exit without proceeding.

## Phase 2: Extract and Select Benchmark Files

Extract the QF_S benchmark archive and randomly select 50 files.

```bash
cd ${{ github.workspace }}

# Extract the archive
mkdir -p /tmp/qfs_benchmarks
tar --zstd -xf tests/QF_S.tar.zst -C /tmp/qfs_benchmarks

# List all .smt2 files
find /tmp/qfs_benchmarks -name "*.smt2" -type f > /tmp/all_qfs_files.txt
TOTAL_FILES=$(wc -l < /tmp/all_qfs_files.txt)
echo "Total QF_S files: $TOTAL_FILES"

# Randomly select 50 files
shuf -n 50 /tmp/all_qfs_files.txt > /tmp/selected_files.txt
echo "Selected 50 files for benchmarking"
cat /tmp/selected_files.txt
```

## Phase 3: Run Benchmarks

Run each of the 50 selected files with both string solvers. Use a 10-second timeout (`-T:10`). Also wrap each run with `time` to capture wall-clock duration.

For each file, run:
1. `z3 smt.string_solver=seq -T:10 <file>`
2. `z3 smt.string_solver=nseq -T:10 <file>`

Capture:
- **Verdict**: `sat`, `unsat`, `unknown`, `timeout` (if exit code indicates timeout), or `bug` (if z3 crashes / produces a non-standard result, or if seq and nseq disagree on sat vs unsat)
- **Time** (seconds): wall-clock time for the run

Use a bash script to automate this:

```bash
#!/usr/bin/env bash
set -euo pipefail

Z3=${{ github.workspace }}/build/z3
RESULTS=/tmp/benchmark_results.tsv
echo -e "file\tseq_verdict\tseq_time\tnseq_verdict\tnseq_time\tnotes" > "$RESULTS"

run_z3() {
    local solver="$1"
    local file="$2"
    local start end elapsed verdict output exit_code

    start=$(date +%s%3N)
    output=$(timeout 12 "$Z3" "smt.string_solver=$solver" -T:10 "$file" 2>&1)
    exit_code=$?
    end=$(date +%s%3N)
    elapsed=$(echo "scale=3; ($end - $start) / 1000" | bc)

    # Parse verdict
    if echo "$output" | grep -q "^unsat"; then
        verdict="unsat"
    elif echo "$output" | grep -q "^sat"; then
        verdict="sat"
    elif echo "$output" | grep -q "^unknown"; then
        verdict="unknown"
    elif [ "$exit_code" -eq 124 ]; then
        verdict="timeout"
    elif echo "$output" | grep -qi "error\|assertion\|segfault\|SIGABRT\|exception"; then
        verdict="bug"
    else
        verdict="unknown"
    fi

    echo "$verdict $elapsed"
}

while IFS= read -r file; do
    fname=$(basename "$file")
    seq_result=$(run_z3 seq "$file")
    nseq_result=$(run_z3 nseq "$file")

    seq_verdict=$(echo "$seq_result" | cut -d' ' -f1)
    seq_time=$(echo "$seq_result" | cut -d' ' -f2)
    nseq_verdict=$(echo "$nseq_result" | cut -d' ' -f1)
    nseq_time=$(echo "$nseq_result" | cut -d' ' -f2)

    # Flag as bug if the two solvers disagree on sat vs unsat
    notes=""
    if { [ "$seq_verdict" = "sat" ] && [ "$nseq_verdict" = "unsat" ]; } || \
       { [ "$seq_verdict" = "unsat" ] && [ "$nseq_verdict" = "sat" ]; }; then
        notes="SOUNDNESS_DISAGREEMENT"
    fi

    echo -e "$fname\t$seq_verdict\t$seq_time\t$nseq_verdict\t$nseq_time\t$notes" >> "$RESULTS"
    echo "[$fname] seq=$seq_verdict(${seq_time}s) nseq=$nseq_verdict(${nseq_time}s) $notes"
done < /tmp/selected_files.txt

echo "Benchmark run complete. Results saved to $RESULTS"
```

Save this script to `/tmp/run_benchmarks.sh`, make it executable, and run it.

## Phase 4: Generate Summary Report

Read `/tmp/benchmark_results.tsv` and compute statistics. Then generate a Markdown report.

Compute:
- **Total benchmarks**: 50
- **Per solver (seq and nseq)**: count of sat / unsat / unknown / timeout / bug verdicts
- **Total time used**: sum of all times for each solver
- **Average time per benchmark**: total_time / 50
- **Soundness disagreements**: files where seq says sat but nseq says unsat or vice versa (these are the most critical bugs)
- **Bugs / crashes**: files with error/crash verdicts

Format the report as a GitHub Discussion post (GitHub-flavored Markdown):

```markdown
### ZIPT Benchmark Report — Z3 c3 branch

**Date**: <today's date>
**Branch**: c3
**Benchmark set**: QF_S (50 randomly selected files from tests/QF_S.tar.zst)
**Timeout**: 10 seconds per benchmark (`-T:10`)

---

### Summary

| Metric | seq solver | nseq solver |
|--------|-----------|-------------|
| sat | X | X |
| unsat | X | X |
| unknown | X | X |
| timeout | X | X |
| bug/crash | X | X |
| **Total time (s)** | X.XXX | X.XXX |
| **Avg time/benchmark (s)** | X.XXX | X.XXX |

**Soundness disagreements** (seq says sat, nseq says unsat or vice versa): N

---

### Per-File Results

| # | File | seq verdict | seq time (s) | nseq verdict | nseq time (s) | Notes |
|---|------|-------------|-------------|--------------|--------------|-------|
| 1 | benchmark_0001.smt2 | sat | 0.123 | sat | 0.456 | |
| ... | ... | ... | ... | ... | ... | ... |

---

### Notable Issues

#### Soundness Disagreements (Critical)
<list files where seq and nseq disagree on sat/unsat>

#### Crashes / Bugs
<list files where either solver crashed or produced an error>

#### Slow Benchmarks (> 8s)
<list files that took more than 8 seconds>

---

*Generated automatically by the ZIPT Benchmark workflow on the c3 branch.*
```

## Phase 5: Post to GitHub Discussion

Post the Markdown report as a new GitHub Discussion using the `create-discussion` safe output.

- **Category**: "Agentic Workflows"
- **Title**: `[ZIPT Benchmark] Z3 c3 branch — <date>`
- Close older discussions with the same title prefix to avoid clutter.

## Guidelines

- **Always build from c3 branch**: The workspace is already checked out on c3; don't change branches.
- **Handle build failures gracefully**: If Z3 fails to build, report the error and create a brief discussion noting the build failure.
- **Handle missing zstd**: If `tar --zstd` fails, try `zstd -d tests/QF_S.tar.zst --stdout | tar -x -C /tmp/qfs_benchmarks`.
- **Be precise with timing**: Use millisecond-precision timestamps and report times in seconds with 3 decimal places.
- **Distinguish timeout from unknown**: A timeout (process killed after 12s) is different from `(unknown)` returned by z3.
- **Report soundness bugs prominently**: If any benchmark shows seq=sat but nseq=unsat (or vice versa), highlight it as a critical finding.
- **Don't skip any file**: Run all 50 files even if some fail.
- **Large report**: If the per-file table is very long, put it in a `<details>` collapsible section.
