---
description: Run Z3 string solver benchmarks (seq vs nseq) and ZIPT on all Ostrich benchmarks from tests/ostrich.zip on the c3 branch and post results as a GitHub discussion

on:
  schedule:
    - cron: "0 6 * * *"
  workflow_dispatch:

permissions: read-all

network:
  allowed:
    - defaults
    - api.nuget.org

tools:
  bash: true
  github:
    toolsets: [default]

safe-outputs:
  create-discussion:
    title-prefix: "[Ostrich Benchmark] "
    category: "Agentic Workflows"
    close-older-discussions: true
  missing-tool:
    create-issue: true
  noop:
    report-as-issue: false

timeout-minutes: 180

steps:
  - name: Checkout c3 branch
    uses: actions/checkout@v6.0.2
    with:
      ref: c3
      fetch-depth: 1
      persist-credentials: false

---


# Ostrich Benchmark: Z3 c3 branch vs ZIPT

You are an AI agent that benchmarks Z3 string solvers (`seq` and `nseq`) and the standalone ZIPT solver on all SMT-LIB2 benchmarks from the `tests/ostrich.zip` archive on the `c3` branch, and publishes a summary report as a GitHub discussion.

## Context

- **Repository**: ${{ github.repository }}
- **Workspace**: ${{ github.workspace }}
- **Branch**: c3 (already checked out by the workflow setup step)

## Phase 1: Build Z3

Build Z3 from the checked-out `c3` branch using CMake + Ninja, including the .NET bindings required by ZIPT.

```bash
cd ${{ github.workspace }}

# Install build dependencies if missing
sudo apt-get install -y ninja-build cmake python3 zstd dotnet-sdk-8.0 unzip 2>/dev/null || true

# Configure the build in Release mode for better performance and lower memory usage
# (Release mode is sufficient for benchmarking; the workflow does not use -tr: trace flags)
mkdir -p build
cd build
cmake .. -G Ninja -DCMAKE_BUILD_TYPE=Release -DZ3_BUILD_DOTNET_BINDINGS=ON 2>&1 | tail -20

# Build z3 binary and .NET bindings SYNCHRONOUSLY (do NOT add & to background these commands).
# Running ninja in the background while the LLM agent is also active causes OOM and kills the
# agent process. Wait for each build command to finish before continuing.
# -j1 limits parallelism to reduce peak memory usage alongside the LLM agent process.
ninja z3 2>&1 | tail -30
ninja build_z3_dotnet_bindings 2>&1 | tail -20

# Verify the build succeeded
./z3 --version

# Locate the Microsoft.Z3.dll produced by the build
Z3_DOTNET_DLL=$(find . -name "Microsoft.Z3.dll" -not -path "*/obj/*" | head -1)
if [ -z "$Z3_DOTNET_DLL" ]; then
    echo "ERROR: Microsoft.Z3.dll not found after build"
    exit 1
fi
echo "Found Microsoft.Z3.dll at: $Z3_DOTNET_DLL"
```

If the build fails, report the error clearly and exit without proceeding.

Once the binary is confirmed working, call the `noop` safe-output tool with the message `"Z3 built successfully from the c3 branch. Starting ZIPT build and benchmark — results will be posted as a GitHub Discussion once complete."` This keepalive call refreshes the safe-output MCP session before the long build and benchmark phases begin, preventing a session timeout.

## Phase 2a: Clone and Build ZIPT

Clone the ZIPT solver from the `parikh` branch and compile it against the Z3 .NET bindings built in Phase 1.

```bash
cd ${{ github.workspace }}

# Re-locate the Microsoft.Z3.dll if needed
Z3_DOTNET_DLL=$(find build -name "Microsoft.Z3.dll" -not -path "*/obj/*" | head -1)
Z3_LIB_DIR=${{ github.workspace }}/build

# Clone ZIPT (parikh branch)
git clone --depth=1 --branch parikh https://github.com/CEisenhofer/ZIPT.git /tmp/zipt

# Patch ZIPT.csproj to point at the freshly built Microsoft.Z3.dll
# (the repo has a Windows-relative hardcoded path that won't exist here)
sed -i "s|<HintPath>.*</HintPath>|<HintPath>$Z3_DOTNET_DLL</HintPath>|" /tmp/zipt/ZIPT/ZIPT.csproj

# Build ZIPT in Release mode
cd /tmp/zipt/ZIPT
dotnet build --configuration Release 2>&1 | tail -20

# Locate the built ZIPT.dll
ZIPT_DLL=$(find /tmp/zipt/ZIPT/bin/Release -name "ZIPT.dll" | head -1)
if [ -z "$ZIPT_DLL" ]; then
    echo "ERROR: ZIPT.dll not found after build"
    exit 1
fi
echo "ZIPT binary: $ZIPT_DLL"

# Make libz3.so visible to the .NET runtime at ZIPT startup
ZIPT_OUT_DIR=$(dirname "$ZIPT_DLL")
if cp "$Z3_LIB_DIR/libz3.so" "$ZIPT_OUT_DIR/" 2>/dev/null; then
    echo "Copied libz3.so to $ZIPT_OUT_DIR"
else
    echo "WARNING: could not copy libz3.so to $ZIPT_OUT_DIR — setting LD_LIBRARY_PATH fallback"
fi
export LD_LIBRARY_PATH="$Z3_LIB_DIR${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
echo "ZIPT build complete."
```

If the ZIPT build fails, note the error in the report but continue with the Z3-only benchmark columns.

## Phase 2b: Extract Benchmark Files

Extract all SMT-LIB2 files from the `tests/ostrich.zip` archive.

```bash
cd ${{ github.workspace }}

# Extract the zip archive
mkdir -p /tmp/ostrich_benchmarks
unzip -q tests/ostrich.zip -d /tmp/ostrich_benchmarks

# List all .smt2 files
find /tmp/ostrich_benchmarks -name "*.smt2" -type f | sort > /tmp/all_ostrich_files.txt
TOTAL_FILES=$(wc -l < /tmp/all_ostrich_files.txt)
echo "Total Ostrich .smt2 files: $TOTAL_FILES"

if [ "$TOTAL_FILES" -eq 0 ]; then
    echo "ERROR: No .smt2 files found in tests/ostrich.zip"
    exit 1
fi
```

Once the benchmark files are confirmed, call the `noop` safe-output tool with the message `"Benchmark files ready: <TOTAL_FILES> Ostrich .smt2 files extracted. Starting benchmark run — this may take over an hour."` This second keepalive refreshes the safe-output MCP session immediately before the long per-file benchmark loop begins.

## Phase 3: Run Benchmarks

Run every file from `/tmp/all_ostrich_files.txt` with both Z3 string solvers and ZIPT. Use a **5-second timeout** per run.

For each file, run:
1. `z3 smt.string_solver=seq -T:5 <file>` — seq solver
2. `z3 smt.string_solver=nseq -T:5 <file>` — nseq (ZIPT) solver
3. `dotnet <ZIPT.dll> -t:5000 <file>` — standalone ZIPT solver (milliseconds)

Capture:
- **Verdict**: `sat`, `unsat`, `unknown`, `timeout` (if exit code indicates timeout or process is killed), or `bug` (if a solver crashes / produces a non-standard result)
- **Time** (seconds): wall-clock time for the run
- A row is flagged `SOUNDNESS_DISAGREEMENT` when any two solvers that both produced a definitive answer (sat/unsat) disagree

Use a bash script to automate this:

```bash
#!/usr/bin/env bash
set -euo pipefail

Z3=${{ github.workspace }}/build/z3
ZIPT_DLL=$(find /tmp/zipt/ZIPT/bin/Release -name "ZIPT.dll" 2>/dev/null | head -1)
ZIPT_AVAILABLE=false
[ -n "$ZIPT_DLL" ] && ZIPT_AVAILABLE=true

# Ensure libz3.so is on the dynamic-linker path for the .NET runtime
export LD_LIBRARY_PATH=${{ github.workspace }}/build${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}

RESULTS=/tmp/benchmark_results.tsv
mkdir -p /tmp/ostrich_run

echo -e "file\tseq_verdict\tseq_time\tnseq_verdict\tnseq_time\tzipt_verdict\tzipt_time\tnotes" > "$RESULTS"

run_z3_seq() {
    local file="$1"
    local start end elapsed verdict output exit_code

    start=$(date +%s%3N)
    output=$(timeout 7 "$Z3" "smt.string_solver=seq" -T:5 "$file" 2>&1)
    exit_code=$?
    end=$(date +%s%3N)
    elapsed=$(echo "scale=3; ($end - $start) / 1000" | bc)

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

run_z3_nseq() {
    local file="$1"
    local start end elapsed verdict output exit_code

    start=$(date +%s%3N)
    output=$(timeout 7 "$Z3" "smt.string_solver=nseq" -T:5 "$file" 2>&1)
    exit_code=$?
    end=$(date +%s%3N)
    elapsed=$(echo "scale=3; ($end - $start) / 1000" | bc)

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

run_zipt() {
    local file="$1"
    local start end elapsed verdict output exit_code

    if [ "$ZIPT_AVAILABLE" != "true" ]; then
        echo "n/a 0.000"
        return
    fi

    start=$(date +%s%3N)
    # ZIPT prints the filename on the first line, then SAT/UNSAT/UNKNOWN on subsequent lines
    output=$(timeout 7 dotnet "$ZIPT_DLL" -t:5000 "$file" 2>&1)
    exit_code=$?
    end=$(date +%s%3N)
    elapsed=$(echo "scale=3; ($end - $start) / 1000" | bc)

    if echo "$output" | grep -qi "^UNSAT$"; then
        verdict="unsat"
    elif echo "$output" | grep -qi "^SAT$"; then
        verdict="sat"
    elif echo "$output" | grep -qi "^UNKNOWN$"; then
        verdict="unknown"
    elif [ "$exit_code" -eq 124 ]; then
        verdict="timeout"
    elif echo "$output" | grep -qi "error\|crash\|exception\|Unsupported"; then
        verdict="bug"
    else
        verdict="unknown"
    fi

    echo "$verdict $elapsed"
}

COUNTER=0
while IFS= read -r file; do
    COUNTER=$((COUNTER + 1))
    fname=$(basename "$file")

    seq_result=$(run_z3_seq "$file")
    nseq_result=$(run_z3_nseq "$file")
    zipt_result=$(run_zipt "$file")

    seq_verdict=$(echo "$seq_result" | cut -d' ' -f1)
    seq_time=$(echo "$seq_result" | cut -d' ' -f2)
    nseq_verdict=$(echo "$nseq_result" | cut -d' ' -f1)
    nseq_time=$(echo "$nseq_result" | cut -d' ' -f2)
    zipt_verdict=$(echo "$zipt_result" | cut -d' ' -f1)
    zipt_time=$(echo "$zipt_result" | cut -d' ' -f2)

    # Flag soundness disagreement when any two definitive verdicts disagree
    notes=""
    declare -A definitive_map
    [ "$seq_verdict"  = "sat" ] || [ "$seq_verdict"  = "unsat" ] && definitive_map[seq]="$seq_verdict"
    [ "$nseq_verdict" = "sat" ] || [ "$nseq_verdict" = "unsat" ] && definitive_map[nseq]="$nseq_verdict"
    [ "$zipt_verdict" = "sat" ] || [ "$zipt_verdict" = "unsat" ] && definitive_map[zipt]="$zipt_verdict"
    has_sat=false; has_unsat=false
    for v in "${definitive_map[@]}"; do
        [ "$v" = "sat"   ] && has_sat=true
        [ "$v" = "unsat" ] && has_unsat=true
    done
    if $has_sat && $has_unsat; then
        notes="SOUNDNESS_DISAGREEMENT"
    fi

    echo -e "$fname\t$seq_verdict\t$seq_time\t$nseq_verdict\t$nseq_time\t$zipt_verdict\t$zipt_time\t$notes" >> "$RESULTS"
    echo "[$COUNTER] [$fname] seq=$seq_verdict(${seq_time}s) nseq=$nseq_verdict(${nseq_time}s) zipt=$zipt_verdict(${zipt_time}s) $notes"
done < /tmp/all_ostrich_files.txt

echo "Benchmark run complete. Results saved to $RESULTS"
```

Save this script to `/tmp/run_ostrich_benchmarks.sh`, make it executable, and run it. Do not skip any file.

## Phase 4: Generate Summary Report

Read `/tmp/benchmark_results.tsv` and compute statistics. Then generate a Markdown report.

Compute:
- **Total benchmarks**: total number of files run
- **Per solver (seq, nseq, and ZIPT)**: count of sat / unsat / unknown / timeout / bug verdicts
- **Total time used**: sum of all times for each solver
- **Average time per benchmark**: total_time / total_files
- **Soundness disagreements**: files where any two solvers that both returned a definitive answer disagree
- **Bugs / crashes**: files with error/crash verdicts

Format the report as a GitHub Discussion post (GitHub-flavored Markdown):

```markdown
### Ostrich Benchmark Report — Z3 c3 branch

**Date**: <today's date>
**Branch**: c3
**Benchmark set**: Ostrich (all files from tests/ostrich.zip)
**Timeout**: 5 seconds per benchmark (`-T:5` for Z3; `-t:5000` for ZIPT)

---

### Summary

| Metric | seq solver | nseq solver | ZIPT solver |
|--------|-----------|-------------|-------------|
| sat | X | X | X |
| unsat | X | X | X |
| unknown | X | X | X |
| timeout | X | X | X |
| bug/crash | X | X | X |
| **Total time (s)** | X.XXX | X.XXX | X.XXX |
| **Avg time/benchmark (s)** | X.XXX | X.XXX | X.XXX |

**Soundness disagreements** (any two solvers return conflicting sat/unsat): N

---

### Per-File Results

<details>
<summary>Click to expand full per-file table</summary>

| # | File | seq verdict | seq time (s) | nseq verdict | nseq time (s) | ZIPT verdict | ZIPT time (s) | Notes |
|---|------|-------------|-------------|--------------|--------------|--------------|--------------|-------|
| 1 | benchmark_0001.smt2 | sat | 0.123 | sat | 0.456 | sat | 0.789 | |
| ... | ... | ... | ... | ... | ... | ... | ... | ... |

</details>

---

### Notable Issues

#### Soundness Disagreements (Critical)
<list files where any two solvers disagree on sat/unsat, naming which solvers disagree>

#### Crashes / Bugs
<list files where any solver crashed or produced an error>

#### Slow Benchmarks (> 4s)
<list files that took more than 4 seconds for any solver>

---

*Generated automatically by the Ostrich Benchmark workflow on the c3 branch.*
```

## Phase 5: Post to GitHub Discussion

Post the Markdown report as a new GitHub Discussion using the `create-discussion` safe output.

- **Category**: "Agentic Workflows"
- **Title**: `[Ostrich Benchmark] Z3 c3 branch — <date>`
- Close older discussions with the same title prefix to avoid clutter.

## Guidelines

- **Always build from c3 branch**: The workspace is already checked out on c3; don't change branches.
- **Synchronous builds only**: Never run `ninja` (or any other build command) in the background using `&`. Running the build concurrently with LLM inference causes the agent process to be killed by the OOM killer (exit 137) because C++ compilation and the LLM together exceed available RAM. Always wait for each build command to finish before proceeding.
- **Release build**: The build uses `CMAKE_BUILD_TYPE=Release` for lower memory footprint and faster compilation on the GitHub Actions runner. The benchmark only needs verdict and timing output; no `-tr:` trace flags are used.
- **Run all benchmarks**: Unlike the QF_S workflow, run every file in the archive — do not randomly sample.
- **5-second timeout**: Pass `-T:5` to Z3 (both seq and nseq) and `-t:5000` to ZIPT (milliseconds). Use `timeout 7` as the outer OS-level guard to allow the solver to exit cleanly before being killed.
- **Be precise with timing**: Use millisecond-precision timestamps and report times in seconds with 3 decimal places.
- **Distinguish timeout from unknown**: A timeout is different from `(unknown)` returned by a solver within its time budget.
- **ZIPT output format**: ZIPT prints the input filename on the first line, then `SAT`, `UNSAT`, or `UNKNOWN` on subsequent lines. Parse accordingly.
- **Report soundness bugs prominently**: If any benchmark shows a conflict between any two solvers that both returned a definitive sat/unsat answer, highlight it as a critical finding and name which pair disagrees.
- **Handle build failures gracefully**: If Z3 fails to build, report the error and create a brief discussion noting the build failure. If ZIPT fails to build, continue with only the seq/nseq columns and note `n/a` for ZIPT results.
- **Large report**: Always put the per-file table in a `<details>` collapsible section since there may be many files.
- **Progress logging**: Print a line per file as you run it (e.g., `[N] [filename] seq=...`) so the workflow log shows progress even for large benchmark sets.

## Safe Output Guarantee

You **MUST** call either `create_discussion` or `noop` before the workflow ends, regardless of what happened during execution:

- **Build succeeded, benchmarks ran**: Call `create_discussion` with the full report.
- **Build succeeded, benchmarks partially ran**: Call `create_discussion` with whatever results were collected and a note about what could not be completed.
- **Z3 build failed**: Call `noop` with a brief message describing the build error.
- **No benchmarks could be run**: Call `noop` with a summary of what failed and why.

Failing to produce any safe output triggers an automatic workflow-failure issue that clutters the repository.
