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
  MuCyc configurations also hash `lib/libz3.so` when it is present in the runtime.
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

## Deeper analysis and controlled ablations

The follow-up first selects the six original pilot inputs solved by MuCyc
Progress but not baseline QSAT at five seconds, then adds the two confirmed
recursive-projection wins and the three original one-second regression controls.
This deliberately difficult **11-case cohort** is not a representative sample.
All configurations below have a **ten-second per-input limit**.

| Configuration | Solved / 11 |
|---|---:|
| Baseline QSAT | 4 |
| Recursive QSAT, QEL | 6 |
| `simplify` then recursive QSAT | 5 |
| `simplify`, `qe-light`, then recursive QSAT | 6 |
| Recursive QSAT, classical MBP | 5 |
| Recursive QSAT, `smt.core.minimize=true` | 5 |
| Current default solver | 5 |
| MuCyc Progress, original artifact backend | 11 |
| Reversed projection variable order | 6 |
| Disable small real Fourier-Motzkin expansion | 6 |
| Disable expansion, classical MBP | 5 |
| Disable expansion, reversed variable order | 6 |
| Recursive QSAT, `smt.arith.solver=2` | 6 |
| Recursive QSAT, greatest-error pivot enabled | 6 |
| Recursive QSAT, simplex strategy 1 | 6 |
| Recursive QSAT, simplex strategy 2 | 6 |
| Recursive QSAT, theory relevancy enabled | 6 |
| Arithmetic-normalizing `simplify` then recursive QSAT | 7 |

The last preprocessing variant is exactly:

```smt2
(check-sat-using
  (then (using-params simplify :arith_lhs true :som true)
        (using-params qsat :qsat_recursive_backjump true)))
```

It solves `mjollnir6/formula_089.smt2` in 5.526 seconds, whereas ordinary
recursive QSAT exceeds ten seconds. This is a use of existing preprocessing,
not a new QSAT algorithm. It is not uniformly beneficial: the same normalization
changes `mjollnir5/formula_252.smt2` from 1.005 to 8.590 seconds and
`mjollnir4/formula_220.smt2` from 0.995 to 3.293 seconds in that matrix.

The other additional knobs do not close any of the five remaining Monniaux gaps.
In particular, disabling the small real Fourier-Motzkin path changes
`mjollnir2/formula_166.smt2` from 0.448 seconds / 33 rounds to
6.863 seconds / 205 rounds. Variable reversal does not reproduce MuCyc's
complete arithmetic pivot policy, and disabling this expansion is not equivalent
to always selecting MuCyc's greatest-lower-bound pivot. These negative results
therefore reject the tested changes, not every possible projection heuristic.
The experimental projection/relevancy parameters have been **removed**, rather
than exposed as unsupported production tuning options. Their patches, binaries,
and raw results are retained for inspection.

The five concrete Monniaux gaps, relative to ordinary recursive QSAT at ten
seconds, are:

| Input under `2010-Monniaux-QE/` | Answer | MuCyc Progress |
|---|---|---:|
| `mjollnir5/formula_096.smt2` | Sat | 0.117 s |
| `mjollnir6/formula_034.smt2` | Unsat | 0.261 s |
| `mjollnir6/formula_089.smt2` | Unsat | 0.273 s |
| `mjollnir6/formula_253.smt2` | Sat | 0.977 s |
| `mjollnir6/formula_257.smt2` | Sat | 3.509 s |

The pinned Non-Progress implementation also solves all five in the original
pilot. Thus recursive nonchronological projection alone does not explain these
remaining differences.

### Production frontend versus isolated QSAT

The default LRA tactic already performs substantial preprocessing and
`qe-light` before selecting QSAT/SMT
(`src/tactic/smtlogics/quant_tactics.cpp`). An explicit
`check-sat-using qsat` deliberately bypasses that frontend. On
`scholl-smt08/RND/RND_6_21.smt2`, ordinary recursive QSAT takes
9.101 seconds / 86 rounds, while `simplify`, `qe-light`, recursive QSAT takes
0.052 seconds / 2 rounds and the current default takes 0.044 seconds / 2 rounds.
This is already an existing default-pipeline benefit. The default still exceeds
ten seconds on all five Monniaux gaps above; it is not a universal solution.

### What the code and native profiles establish

The pinned `lib/MuCyc/qsat.ml` erases the current model after refinement with
`loop Map.Poly.empty ...`, just as current Z3 does. This differs from the
model-preservation discussion around Algorithm 7 in the extended paper.
Model reuse is not an already-working artifact fix that can simply be copied.
It needs prefix-specific saved models and reconstruction of newly introduced
predicate definitions: completing an old model with arbitrary Boolean values
for fresh abstraction predicates would not preserve the required invariant.

MuCyc uses per-level frames and fresh ground solver/context instances through
`lib/Z3Smt/z3interface.ml`. Z3 QSAT instead has two persistent SMT kernels,
global predicate abstraction, and level-filtered assumptions. MuCyc's actual
SMT frontend in `lib/MuCyc/solver.ml` performs type inference, alpha conversion,
let/ite elimination, normalization, prenex conversion, and redundant-quantifier
elimination. Its generic PCSP `simplify`/`reduce`/`slice` settings are not an
equivalent description of this path.

Three native stack samples each were collected for ordinary recursive QSAT on
`mjollnir5/formula_096.smt2` and `mjollnir6/formula_034.smt2`, with debuginfod
disabled. **All six samples are in exact-rational LRA tableau simplex work**,
including rational multiplication/GCD and row pivots under
`lp::lp_primal_core_solver`. The verbose traces show 034 still in its first
QSAT round and 096 in its second. This is not a statistical profile of the
whole corpus, but it directly locates these sampled stalls in ground solving,
not MBP or recursive backtracking. Merely making kernels fresh cannot explain
a stall already present in the first query.

Accordingly the stronger next target is the shape and normalization of the
initial ground queries, including abstraction definitions and their effect on
linear arithmetic, while holding the ground backend constant. Frame/core
granularity and MuCyc's precise bound-selection policy remain separate
opportunities. Neither naive model reuse nor globally disabling real
Fourier-Motzkin expansion is justified by the evidence.

The 11-case matrices are retained in `qsat-deep-gaps-10s`,
`qsat-deep-projection-10s`, `qsat-deep-arithmetic-10s`, and
`qsat-deep-ground-10s`, each with `run-00/manifest.json`, exact transformed
inputs, JSONL records, and raw stdout/stderr. The six native stacks and verbose
logs are in `qsat-deep-profiles`. `qsat_deep_evaluate.py` records the cohort
selection and configuration list in each `experiment.json`; its source is
retained beside those directories. The benchmark API accepts
`evaluate(args, configurations)` for such controlled tactic/command ablations,
without changing the CLI's default configurations.

### Fresh 118-case pilot and current-backend control

A new **118-case, five-second pilot** uses the exact original pilot paths, the
published recursive executable, and a newly built shared library from the same
current ground-solver sources and GCC Release settings:

| Configuration | Solved | Timeout |
|---|---:|---:|
| Baseline QSAT | 94 | 24 |
| Recursive QSAT | 94 | 24 |
| Arithmetic-normalized recursive QSAT | 91 | 27 |
| Current default solver | 92 | 26 |
| MuCyc Progress, original Z3 4.15.2 | 93 | 25 |
| MuCyc Progress, current Z3 5.3.1 | 91 | 27 |

There are no answer disagreements, errors, or crashes in this completed run.
Normalization rescues no cases at this cutoff and loses
`20230331-polyv/cp6hv-miss1v.smt2`,
`scholl-smt08/RNDPRE/RNDPRE_4_41.smt2`, and
`scholl-smt08/RNDPRE/RNDPRE_4_56.smt2` relative to recursive QSAT.
It is therefore **not enabled globally**. The current default rescues
`RND_6_21` but loses three other cases. Aggregate solved counts do not imply
that the configurations solve the same inputs.

The direct library replacement initially failed because the old OCaml binding
references the removed `Z3_mk_set_has_size` symbol at load time, even on LRA
inputs. Its eleven error records in the first `qsat-deep-ground-10s` attempt
are excluded from every MuCyc solved count. The corrected experiment eagerly
binds symbols and preloads a tiny **LRA-only compatibility sentinel**: it supplies
that missing entry point but prints an error and aborts if it is ever called.
It does not implement finite sets or return a fabricated value. No invocation
triggered the sentinel in the completed comparisons.

This is an experimental backend control, not a supported upgrade procedure for
the artifact. All other runtime libraries/configuration files stay unchanged;
the dynamic loader was checked to resolve `libz3.so` to the new library.
The manifest records `LD_LIBRARY_PATH`, `LD_PRELOAD`, eager binding, and hashes
of the selected library and sentinel, including the sentinel source hash.
The sentinel source, build logs, and runtime are retained outside the repository.

A **30-second follow-up on the six original MuCyc-only pilot inputs** gives:

| Input | Recursive QSAT | Normalized recursive QSAT | MuCyc, current Z3 |
|---|---:|---:|---:|
| `mjollnir5/formula_096` | Timeout | Timeout | Sat, 0.296 s |
| `mjollnir6/formula_034` | Timeout | Timeout | Unsat, 0.369 s |
| `mjollnir6/formula_089` | Unsat, 28.506 s | Unsat, 5.541 s | Unsat, 0.291 s |
| `mjollnir6/formula_253` | Timeout | Timeout | Sat, 1.236 s |
| `mjollnir6/formula_257` | Timeout | Timeout | Sat, 6.754 s |
| `RND/RND_6_21` | Sat, 9.110 s | Sat, 9.975 s | Sat, 8.344 s |

The first five paths are under `2010-Monniaux-QE/`; the last is under
`scholl-smt08/`. Both Z3 QSAT configurations solve two of six, while MuCyc with
the current ground engine solves all six. Four differences persist beyond
30 seconds, so they cannot be explained solely by using the older Z3 backend.
The backend still matters: MuCyc with current Z3 exceeds five seconds on
`formula_257` and `RND_6_21`, unlike the pinned original backend.

Three additional runs of `formula_089`, using the published executable and the
benchmark skill with a 40-second limit, give:

| Pipeline | Min | Median | Max |
|---|---:|---:|---:|
| Recursive QSAT | 28.579 s | 28.662 s | 28.819 s |
| Normalized recursive QSAT | 5.487 s | 5.503 s | 5.569 s |

All six answers are unsat. This is approximately **5.2x** lower median time
for this selected input, not a corpus-wide speedup. Both pipelines use six
QSAT rounds in the 30-second comparison, reinforcing the distinction between
ground-query cost and the number of refinement rounds. Timings and statistics
are logged in `qsat-benchmarks.db`.

The fresh pilot is `qsat-deep-pilot-5s`; the longer follow-up is
`qsat-deep-gaps-30s`. Both have complete manifests and raw outputs.
Repeated-timing logs are `qsat-deep-repeat-089-plain.log` and
`qsat-deep-repeat-089-normalized.log`. All are retained under the same session
artifact directory listed above. None of these shorter-budget experiments
replaces the still-unrun full 300-second / 32 GB paper protocol.

## Frobenius integer-arithmetic evaluation

The separate **October 20, 2026** evaluation uses all **120** inputs in
`non-incremental/LIA/20250213-Frobenius` from the same pinned SMT-LIB 2025
release: 60 two-coin and 60 three-coin problems. These are additional local
experiments, not the paper's published LRA evaluation. Archive URL/checksums
are pinned in `qsat_benchmark_artifact.json` under `frobenius_benchmarks`.
Only this family was extracted; the original benchmark files are unchanged
and are not vendored.

Each input asks for a nonnegative greatest integer `P` that cannot be expressed
as a nonnegative combination of the given coin denominations. All 120 inputs
are marked sat. Independent shortest-path calculations over residues and
dynamic-programming reachability checks produce Frobenius numbers for all 120;
the two-coin results also agree with `a*b - a - b`. These are numerical
cross-checks, not checks of solver-produced models: timed inputs request only
`check-sat`.

The unmodified baseline and published recursive binary are the same immutable
snapshots as above. MuCyc uses its original executable/configurations and
Z3 4.15.2 library, **without** the current-backend compatibility sentinel.
`paper-z3` remains the older default solver through CoAR's frontend, not a
native current-Z3/QSAT comparison. The initial screen, selected follow-up, and
45-second repeated timings are sequential. The later full 20-second run uses
32 pinned workers, as detailed below. Wall-clock times include startup/frontend
overhead.

### Complete one-second screen

| Configuration | Two coins / 60 | Three coins / 60 | Solved / 120 | Timeout |
|---|---:|---:|---:|---:|
| Baseline QSAT | 4 | 4 | 8 | 112 |
| Recursive QSAT, QEL | 4 | 4 | 8 | 112 |
| Recursive QSAT, classical MBP | 5 | 4 | 9 | 111 |
| Current default solver | 4 | 5 | 9 | 111 |
| MuCyc Progress | 2 | 1 | 3 | 117 |
| MuCyc Non-Progress | 2 | 1 | 3 | 117 |
| Paper Z3 through CoAR | 4 | 5 | 9 | 111 |

Every successful answer is sat; there are no errors, crashes, unknown answers,
or status disagreements. Baseline and recursive QSAT solve exactly the same
eight cases. Classical MBP additionally solves `fcp_11_13.smt2`; the current
default and paper Z3 additionally solve `fcp_11_13_17.smt2`.
This is a short-budget screen, not a full-timeout performance result.

### Selected 30-second follow-up

The follow-up selects those two cutoff differences plus larger two-/three-coin
controls. Times are seconds; **T** means the 30-second wall limit was exceeded.
These are single trials on a deliberately selected four-input subset.

| Input | Baseline / recursive QSAT | Classical MBP | Current default | MuCyc Progress | MuCyc Non-Progress | Paper Z3 |
|---|---:|---:|---:|---:|---:|---:|
| `fcp_11_13` | 29.590 / 29.583 | 0.936 | 2.545 | 17.228 | 16.915 | 1.254 |
| `fcp_11_13_17` | 3.537 / 3.540 | 19.301 | 0.685 | 16.857 | 26.064 | 0.871 |
| `fcp_17_19` | 10.755 / 10.740 | 27.654 | 12.143 | T | T | T |
| `fcp_17_19_23` | T / T | T | 29.457 | T | T | 3.575 |

Baseline, recursive QSAT, and classical MBP each solve 3/4; the current default
solves 4/4, each MuCyc mode 2/4, and paper Z3 3/4. All completed answers agree.
In particular, the default solver's 29.457-second answer is near the cutoff
and is not a robust speedup estimate.

The completed baseline and recursive answers have identical QSAT round counts:
266, 338, and 353 for the first three inputs. No extra recursive projections
are recorded in the completed candidate QSAT answers, either in this follow-up
or in the full screen. Timeouts do not provide final statistics, so this does
not assert anything about their unreported projection counts.

Three repeated runs of `fcp_11_13`, with a 45-second limit, give:

| Configuration | Min | Median | Max |
|---|---:|---:|---:|
| Baseline QSAT | 29.431 s | 29.484 s | 29.532 s |
| Recursive QSAT, QEL | 29.409 s | 29.530 s | 29.540 s |
| Recursive QSAT, classical MBP | 0.916 s | 0.924 s | 0.930 s |

All nine answers are sat and logged in `qsat-benchmarks.db` (runs 13-21).
Classical MBP is approximately **32x faster** on this input. Its 30-second
comparison also reports 248 versus 266 QSAT rounds and peak Z3 memory of
21.78 versus 31.76 MB. However, classical MBP slows `fcp_11_13_17` from
3.540 to 19.301 seconds and `fcp_17_19` from 10.740 to 27.654 seconds.
It is therefore not enabled globally. The reproducible targeted setting is:

```smt2
(check-sat-using
  (using-params qsat :qsat_recursive_backjump true :qsat_use_qel false))
```

### Complete 20-second parallel evaluation

The requested reevaluation runs all **840** input/configuration combinations
with a **20-second wall-clock limit per invocation**, using **32 workers** on
the 32 available logical CPUs. Each worker has its own CPU, enforced with
`taskset`; this does not claim 32 physical cores. Queue waiting is excluded from
the limit. Job order is shuffled with seed `20261020`. The driver verifies
input, executable, configuration, and MuCyc library hashes before running the
same seven configurations and original inputs as the one-second screen.

| Configuration | Two coins / 60 | Three coins / 60 | Solved / 120 | Timeout |
|---|---:|---:|---:|---:|
| Baseline QSAT | 7 | 6 | 13 | 107 |
| Recursive QSAT, QEL | 5 | 6 | 11 | 109 |
| Recursive QSAT, classical MBP | 5 | 4 | 9 | 111 |
| Current default solver | 6 | 6 | 12 | 108 |
| MuCyc Progress | 5 | 4 | 9 | 111 |
| MuCyc Non-Progress | 5 | 4 | 9 | 111 |
| Paper Z3 through CoAR | 6 | 7 | 13 | 107 |

Elapsed matrix time is **501.520 seconds (8m22s)**, with an observed peak of
32 simultaneous jobs. All 840 unique input/configuration pairs are present;
every configuration has 120 records. Per-CPU execution intervals do not
overlap. There are no errors, crashes, unknowns, wrong answers, or solver
disagreements. The maximum observed invocation duration is 20.290 seconds,
including timeout scheduling and process cleanup; every successful answer is
below 20 seconds. No paper-equivalent memory cap is imposed.

The eight small inputs solved by native QSAT in the one-second screen remain
solved by all seven configurations. Other completed answers are:

| Input | Baseline | Recursive QEL | Classical MBP | Current default | MuCyc Progress | MuCyc Non-Progress | Paper Z3 |
|---|---:|---:|---:|---:|---:|---:|---:|
| `fcp_11_13` | T | T | 2.552 | 4.713 | T | T | 2.429 |
| `fcp_11_13_17` | 7.871 | 6.618 | T | 1.353 | T | T | 1.616 |
| `fcp_13_17` | 6.017 | 5.446 | T | 7.401 | 9.557 | 9.408 | 7.690 |
| `fcp_13_17_19` | 14.056 | 13.834 | T | 17.860 | T | T | 5.673 |
| `fcp_17_19` | 19.679 | T | T | T | T | T | T |
| `fcp_17_19_23` | T | T | T | T | T | T | 6.714 |
| `fcp_19_23` | 19.603 | T | T | T | T | T | T |

Times are seconds; **T** means the nominal 20-second timeout. These are loaded,
parallel measurements and must not be mixed with the earlier sequential
timings. In particular, baseline's two apparent wins over recursive QSAT are
close to the cutoff. A separate **four-worker**, 20-second check repeats each
of those two inputs twice with each binary:

| Input | Baseline min/max | Recursive QEL min/max |
|---|---:|---:|
| `fcp_17_19` | 11.711 / 15.777 s | 11.458 / 11.767 s |
| `fcp_19_23` | 10.647 / 13.969 s | 10.487 / 11.534 s |

All eight lower-load answers are sat, logged as benchmark runs 22-29.
Thus these two losses are not robust across execution loads; the single
32-worker matrix is not evidence of a stable algorithmic regression.
The lower-load checks do not replace or increase its reported solved counts.
Completed recursive QSAT answers in the full matrix report no extra recursive
projections. No Frobenius improvement from recursive backprojection is
established.

**Conclusion:** recursive backprojection shows no measured Frobenius benefit
in these completed runs. Integer projection-engine selection and the default
frontend have much larger, non-uniform effects; MuCyc is not a general
performance improvement on this family.

The retained session artifacts are:

- `qsat-frobenius-smoke-5s`: four smoke inputs, seven configurations.
- `qsat-frobenius-full-1s`: all 120 inputs, seven configurations.
- `qsat-frobenius-frontier-30s`: four selected inputs, seven configurations.
- `qsat-frobenius-parallel-smoke`: one input, seven configurations, four workers.
- `qsat-frobenius-full-20s-32workers`: all 120 inputs, seven configurations,
  32 pinned workers, including per-invocation commands/CPU assignments/timing.
- `qsat-frobenius-cutoff-check.json` and
  `qsat-frobenius-cutoff-fcp_{17_19,19_23}-{baseline-qsat,candidate-qsat}.log`:
  the separate four-worker cutoff checks.
- `qsat-frobenius-repeat-{baseline-qsat,candidate-qsat,candidate-classic}.log`:
  repeated-timing output, with per-run statistics in the SQLite database.
- `qsat-frobenius-evaluation-summary.json`: consolidated results, per-coin-family
  counts, numerical oracles, and manifest/result hashes.
- `evaluate_frobenius.py`, `parallel_frobenius.py`,
  `check_frobenius_cutoffs.py`, `summarize_frobenius.py`, and
  `frobenius-followup-paths.json`: exact drivers, cross-checks, and follow-up list.

Each harness directory includes `run/` with its manifest, transformed inputs,
raw stdout/stderr, JSONL results, and summary. Sequential driver directories
also include `provenance.json`; parallel manifests include affinity, concurrency,
job-order, environment, and driver hashes. The consolidated summary preserves
each run's concurrency so sequential and parallel timings remain distinct.
Together they retain 1,743 harness invocations, in addition to 17 repeated
benchmark runs. They use the session artifact location listed above. No full 120-input
30-/300-second run or paper-equivalent memory limit is claimed.
