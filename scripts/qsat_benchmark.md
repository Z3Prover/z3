# QSAT / Lagrangian-duality evaluation

The reference is Bocevska et al., *Lagrangian-Based Duality for Quantified SMT
Algorithms*, CAV 2026, DOI `10.1007/978-3-032-32526-6_4`. The extended version
is available as [HAL-05623727](https://hal.science/hal-05623727v1).
The linked implementation is [CoAR/MuCyc](https://github.com/hiroshi-unno/coar).
Use the **pinned Zenodo artifact**, not the moving CoAR main branch.

`qsat_benchmark_artifact.json` pins the source, prebuilt image, benchmark archive,
configurations, archive checksums, and published experimental protocol/results.
External sources, binaries, and benchmarks are not vendored into Z3.

## Setup

Run these commands inside Linux, WSL, or the artifact's Linux container.
Python 3.11 or newer and `zstd` are needed for the evaluation/download steps.

```sh
mkdir qsat-data
cd qsat-data
curl -fL https://zenodo.org/records/16740866/files/LRA.tar.zst -o LRA.tar.zst
echo '89f73c32150ccc1fdbda3dcb459e4c687a75bea2a96cb53a6d5f7f9c55c67bae  LRA.tar.zst' | sha256sum -c -
tar --zstd -xf LRA.tar.zst
curl -fL https://zenodo.org/records/19860162/files/mucyc_cav26ae_src.zip -o mucyc_cav26ae_src.zip
echo '39797c0b536c7148cbfcec96732ca2e153c07343c44f2d47c5a77782f57f57d8  mucyc_cav26ae_src.zip' | sha256sum -c -
unzip mucyc_cav26ae_src.zip
```

Follow `mucyc_cav26ae_src/cav26ae/README.md` to build CoAR manually or load the
published Docker image. The source build produces `_build/default/main.exe`.
The runner accepts either that layout or a runtime directory with `main.exe`,
`config/`, and optional matching shared libraries in `lib/`. Keep MuCyc's original
Z3 library separate from the Z3 binaries under comparison.

Preserve an unmodified baseline before changing solver sources. For example,
from a Z3 checkout at the desired baseline revision:

```sh
cmake -S . -B build-qsat-baseline -DCMAKE_BUILD_TYPE=Release
cmake --build build-qsat-baseline --target shell --parallel 4
cp build-qsat-baseline/z3 /absolute/path/to/baseline-z3
```

Build the candidate separately with the same compiler, build type, and settings.
The actual CMake executable target is `shell`, whose output name is `z3`.
Use matching libraries for shared builds. Verify `--version`; do not accidentally
time an older executable left in a reused build directory.

## Runs

Pilot: select at most 25 inputs per family using a deterministic hash ordering.
The paper archive gives **118** inputs, since two families contain fewer than 25.

```sh
python3 scripts/qsat_benchmark.py \
  --corpus /absolute/path/to/non-incremental/LRA \
  --baseline /absolute/path/to/baseline-z3 \
  --candidate /absolute/path/to/candidate-z3 \
  --recursive-backjump \
  --mucyc /absolute/path/to/mucyc_cav26ae_src \
  --per-family 25 --timeout 5 --output /absolute/path/to/new-pilot-directory
```

For the full paper protocol, omit `--per-family` and use `--timeout 300`.
This runs all **2,439** instances sequentially and can take many hours.
Run on an otherwise idle machine. The runner enforces a wall-clock timeout,
but **does not impose the paper's 32 GB memory limit** or reproduce its hardware.
Impose any required memory limit with the execution environment and report it.
The Z3 comparisons invoke `check-sat-using qsat` explicitly. Add
`--include-default` to also run each Z3 binary's default solver.
`paper-z3` is the original 4.15.2 library through CoAR's frontend, not the current
baseline binary; this preserves the paper's original comparison while keeping
the frontend-overhead distinction explicit.

Each new output directory contains:

- `manifest.json`: selected paths, original input hashes and expected statuses,
  executable/configuration hashes, tactic settings, timeout, runner hash, platform.
- `inputs/`: exact QSAT command transformations; original benchmarks are untouched.
- `raw/`: stdout and stderr for every invocation, including timeouts.
- `results.jsonl`: immediately flushed per-case results, commands, elapsed time,
  return codes, and available Z3 statistics.
- `summary.json`: result counts, disagreements, and rescued/lost cases vs baseline.

Errors/crashes are not counted as successful answers. A conflict with an input's
known status, or a sat/unsat disagreement between solvers, fails the run. Unknowns
and timeouts remain distinct. Existing output directories are never overwritten.
Do not compare totals across different timeouts or cohorts as if they were the
same experiment. Short-budget screening is not a reproduction of the paper's
300-second results.

## Integrated strategies

`qsat_recursive_backjump=true` enables recursive projection of skipped opponent
blocks before learning a clause. The projection cutoff strictly decreases, and
the existing both-polarities scope check remains the final backtracking guard.
The baseline already has that scope guard: this change adds recursive projection,
not the paper's original unsafe-scope repair. Cached intermediate projections are
kept alive until the level cache is reset.

The strategy is opt-in because short-budget screening shows tradeoffs, rather
than a uniform improvement. No global termination or new theory-support claim is
made. The paper's separate model-reuse proposal is not implemented.

Enable it directly in SMT-LIB with:

```smt2
(check-sat-using (using-params qsat :qsat_recursive_backjump true))
```

`qsat_use_qel=false` selects classical MBP instead of egraph-based QEL; add
`--classic-mbp` to evaluate this setting in the candidate only. QSAT now forwards
these tactic-local MBP parameters correctly. Its previous `use_qel=false`
assignment did not match the parameter actually read by MBP. The default stays
`true`, preserving the previous effective behavior.

Run the harness tests with:

```sh
python3 -m unittest discover -s scripts -p test_qsat_benchmark.py
```

The `test-z3 qsat` group performs 3,072 oracle-checked solver runs: 128 generated
matrices, both quantifier-prefix polarities, both projection engines, and both
backtracking strategies, over Booleans, real signs, and integer signs. Each
numeric sign independently realizes either Boolean value, so exhaustive Boolean
truth evaluation supplies the oracle in all three theories. The group also
checks cached-expression ownership and quantified real/integer examples.

## Local evaluation

The baseline is unmodified revision
`481b63e4904cac4979e077dac8be93a4ca962c92`. Both native binaries use the same
GCC Release build configuration under WSL. MuCyc uses the pinned artifact's
published executable and matching libraries, including its original Z3 4.15.2.
Output directory names below identify the retained manifests and raw logs;
large external inputs, binaries, and raw logs are not checked into this repository.

The deterministic **118-case, five-second pilot** produced these solved counts:

| Configuration | Solved |
|---|---:|
| Baseline QSAT | 94 |
| Recursive QSAT, QEL | 94 |
| Recursive QSAT, classical MBP | 91 |
| MuCyc Progress | 93 |
| MuCyc Non-Progress | 91 |
| Paper Z3 through CoAR | 89 |

These exploratory runs are retained in `qsat-paper-pilot-baseline`,
`qsat-paper-pilot-candidate`, and `qsat-paper-pilot-classic`. They predate the
final level-cache ownership fix, and their manifests pin the exact executable
snapshots. The first two pilots also used a coarser timing implementation:
use their solved counts, not their short-case timings. Classical MBP rescued
no cases and lost three relative to baseline, so QEL remains the default.

The **final candidate's full 2,439-case, one-second screen** gives:

| Configuration | Sat | Unsat | Solved | Timeout |
|---|---:|---:|---:|---:|
| Baseline QSAT | 599 | 1,105 | 1,704 | 735 |
| Recursive QSAT, QEL | 602 | 1,111 | 1,713 | 726 |

The baseline records are reused from `qsat-paper-full-screen`; the final
candidate was run separately in `qsat-paper-final-full-screen-rerun`. Input
hashes and platform descriptions match. There are nine rescues and no losses
in this comparison. Among the 147 mutually solved inputs where recursion fired,
QSAT rounds decrease from **5,167 to 3,888**.

These are single trials at a sensitive cutoff, not a statistically robust
speedup estimate. The earlier feature-only prototype solved 1,709, with eight
rescues and three losses; all three losses disappear in the final rerun.
Do not attribute differences between those runs solely to the code changes.
An external WSL update interrupted a first attempt at the final screen;
its incomplete `qsat-paper-final-full-screen` output is excluded.

A **15-second follow-up on 12 selected cutoff differences** checks the original
eight rescues, original three losses, and the additional final-screen rescue.
Baseline solves 10, the final candidate 12, each MuCyc configuration 9, and
paper Z3 10. Both Z3 configurations solve all four additional cases beyond
the original eight. The two remaining baseline timeouts are:

| Input under `2010-Monniaux-QE/` | Baseline QSAT | Recursive QSAT | MuCyc Progress | Paper Z3 |
|---|---:|---:|---:|---:|
| `mjollnir2/formula_063.smt2` | Timeout, 15 s | Unsat, 0.568 s | Unsat, 0.447 s | Unsat, 2.384 s |
| `mjollnir2/formula_166.smt2` | Timeout, 15 s | Unsat, 0.443 s | Unsat, 1.020 s | Timeout, 15 s |

Three repeated final-candidate runs of `formula_063` give **539 / 540 / 540 ms**
minimum/median/maximum, all unsat; these are also logged in
`qsat-benchmarks.db`. The selected follow-up is intentionally biased toward
changed cases, not a representative sample. No answer disagreements, errors,
or crashes were observed in the completed comparisons.

The final executable's SHA256 is
`c8c1ce79c49a9662aca3daab37c98d386487a480b50bb989e18ab36fdbc07860`.
Final raw follow-up runs are `qsat-paper-final-rescues-verified` and
`qsat-paper-final-additional-deltas`; the consolidated machine-readable report
is `qsat-paper-final-evaluation-summary.json`. These artifacts, the pilot/screen
directories, and native validation logs are retained under
`%USERPROFILE%\.copilot\session-state\c44a3851-b0bb-4c80-9256-0900155fe736\files`.

**The full 300-second paper protocol has not been rerun.** The local evaluation
does not impose the paper's 32 GB limit or reproduce its hardware. The recursive
strategy therefore remains opt-in despite the confirmed targeted wins.
