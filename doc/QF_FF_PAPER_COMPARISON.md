# Full finite-field paper-artifact comparison

The complete comparison covers **4,212 distinct inputs and 12,636 primary
runs** from the CAV 2023, CAV 2024 and FMCAD 2026 public artifacts at the
requested 10-second budget. It compares the current `codex/qf-ff` branch with
the official ARM64 CoCoA-enabled cvc5 1.3.4 release, using both GB and split.

The [two-page PDF](../output/pdf/finite-field-comparison/comparison.pdf)
contains vector cactus, performance-profile and scatter plots. The
[editable LaTeX bundle](../output/pdf/finite-field-comparison/finite-field-comparison-latex.zip)
and [complete data package](../output/pdf/finite-field-comparison/finite-field-comparison-data.zip)
accompany the [per-input results](../tests/finite_field/results/paper-artifacts/cases.csv).
The analysis below records the protocol, follow-ups and limitations.

A subsequent [real-project circuit comparison](QF_FF_REAL_CIRCUITS.md) adds
eight queries from Dark Forest, Hermez, MACI, and Succinct's Plonky2 verifier.
Those new runs are separate from the paper-corpus counts reported here.

## Results at 10 seconds

The full pass contains **12,636 runs on 4,212 byte-distinct inputs**. Z3 and cvc5 split have nearly identical total coverage, with large differences by family. Z3 solves 400 more inputs than cvc5 GB. The cvc5 split wrong answer described below is excluded from solved counts.

| Solver | Solved | SAT | UNSAT | Multi-query | Timeout | Memory limit | Error | Wrong | PAR-2 (s) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Z3 FF branch | 2432 | 1255 | 1177 | 0 | 1370 | 404 | 6 | 0 | 8.570 |
| cvc5 GB | 2032 | 1037 | 994 | 1 | 2118 | 62 | 0 | 0 | 10.522 |
| cvc5 split | 2434 | 1018 | 1415 | 1 | 1716 | 61 | 0 | 1 | 8.662 |

PAR-2 penalizes every failed run with 20 seconds. All runs use identical wall-time and sampled memory limits. There are no unclassified or missing runs.

### Breakdown by benchmark family

| Family | Distinct inputs | Z3 | cvc5 GB | cvc5 split |
| --- | ---: | ---: | ---: | ---: |
| ASHR | 32 | 0 | 0 | 32 |
| CirC-D | 609 | 186 | 147 | 545 |
| CirC-S | 640 | 100 | 170 | 89 |
| Examples | 10 | 3 | 10 | 9 |
| QED2 | 100 | 44 | 37 | 59 |
| Seq | 100 | 25 | 11 | 100 |
| Small | 325 | 218 | 160 | 179 |
| TV | 1553 | 1404 | 1259 | 1188 |
| TV-pureFF | 843 | 452 | 238 | 233 |

Z3 is stronger on compiler translation validation (TV), its pure-field encoding (TV-pureFF), and the small-field systems. Split is substantially stronger on operator determinism (CirC-D), bit-sum sequences (Seq), arithmetic shifts (ASHR), and the complete circomlib QED2 suite. In mixed BV/field soundness (CirC-S), cvc5 GB leads both other configurations.

The memory gap is material: Z3 reaches the 4-GiB sampled limit on 404 inputs versus 62 for GB and 61 for split. Z3 memory failures comprise 198 TV-pureFF, 77 CirC-S, 69 Seq, and 60 CirC-D inputs. The sampled cap permits overshoots; peak measured RSS reaches 4,722.6 MiB for Z3.

### Field sizes

| Largest field in input | Inputs | Z3 | cvc5 GB | cvc5 split |
| --- | ---: | ---: | ---: | ---: |
| small (<=16 bits) | 533 | 424 | 368 | 387 |
| medium (17-127 bits) | 167 | 162 | 167 | 154 |
| large (>=128 bits) | 3512 | 1846 | 1497 | 1893 |

### Paper selections

| Selection | Distinct inputs | Z3 | cvc5 GB | cvc5 split |
| --- | ---: | ---: | ---: | ---: |
| CAV23 | 2403 | 1856 | 1504 | 1427 |
| CAV23-main | 2053 | 1531 | 1167 | 1119 |
| CAV24 | 2654 | 1290 | 1092 | 1540 |
| CAV24-main | 1108 | 422 | 401 | 909 |
| FMCAD26 | 1210 | 1079 | 929 | 886 |
| FMCAD26-UNSAT | 390 | 357 | 362 | 326 |

These rows overlap. The main paper selections materially change the relative picture: Z3 leads on CAV23-main, while split leads strongly on CAV24-main. The full pooled total should not substitute for either paper-specific view.

### Pairwise overlap and conditional timings

| Reference | Both solve | Z3 only | Reference only | Neither | Geometric mean reference/Z3 time |
| --- | ---: | ---: | ---: | ---: | ---: |
| cvc5 | 1861 | 571 | 171 | 1609 | 0.985 |
| cvc5_split | 1778 | 654 | 656 | 1124 | 1.405 |

Timing ratios above condition on mutually solved inputs in the eight-worker pass. Values above one favor Z3. They are not whole-corpus speedups. Z3 and split solve 3,088 distinct inputs between them, illustrating complementary coverage; this is an oracle union, not a measured portfolio implementation.

## Longer-budget investigation

The separate follow-up uses 24 selected inputs, 60 seconds per run, four concurrent workers, and the same 4-GiB sampled RSS cap. Four slots are reserved for the named SMTHash Poseidon/MiMC circuits; the remaining twenty follow recorded family/outcome strata and ascending input hashes. It is a diagnostic sample, not full 60-second coverage.

| Solver | Solved at 10 s on this sample | Solved at 60 s | Newly solved | Lost solves |
| --- | ---: | ---: | ---: | ---: |
| Z3 | 12 | 12 | 0 | 0 |
| cvc5 GB | 6 | 7 | 1 | 0 |
| cvc5 split | 10 | 11 | 1 | 0 |

The additions are GB on `i_13_8_4_system13.smt2` (SAT, 27.677 s) and split on `compilation-sound-none-12v-008t-ff-circ-255b-0s.smt2` (UNSAT, 14.506 s). No definite answer changes. All eight single-query SAT replays pass independent model validation.

### Real Poseidon/MiMC determinism queries

| circomlib case | Z3 at 10 s | Z3 in 60-s replay | GB, both budgets | Split, both budgets |
| --- | ---: | ---: | --- | --- |
| `SMTHash1@smthash_mimc@circomlib.smt2` | UNSAT 0.156 s | UNSAT 0.150 s | timeout | timeout |
| `SMTHash1@smthash_poseidon@circomlib.smt2` | UNSAT 0.224 s | UNSAT 0.203 s | timeout | timeout |
| `SMTHash2@smthash_mimc@circomlib.smt2` | UNSAT 0.163 s | UNSAT 0.150 s | timeout | timeout |
| `SMTHash2@smthash_poseidon@circomlib.smt2` | UNSAT 0.179 s | UNSAT 0.165 s | timeout | timeout |

These are circuit determinism verification queries, not measurements of hash evaluation or proof generation. The other `Sigma@poseidon` query is easy for all three solvers (Z3 0.029 s, GB 0.043 s, split 0.042 s in the primary pass). The complete QED2 family still favors split, as the family table shows.

## Isolated timing stability

The 64-input family/runtime-stratified sample contains only inputs solved by
all three configurations in the primary pass. Each solver is run three times
per input with one worker and the original 10-second/4-GiB limits. All **576**
runs finish successfully with consistent answers.

Using each input's median of three repetitions, the geometric mean of
reference runtime divided by Z3 runtime is **1.548 for GB** and **1.879 for
split**. Z3 has the lower median on 33/64 inputs against GB and 35/64 against
split. These conditional results describe this stratified sample, not an
estimated whole-corpus speedup.

| Solver | Median max/min across repetitions | 90th percentile | Maximum |
| --- | ---: | ---: | ---: |
| Z3 | 1.024 | 1.079 | 1.152 |
| cvc5 GB | 1.020 | 1.064 | 1.146 |
| cvc5 split | 1.016 | 1.067 | 1.154 |

Selection manifests retain the exact cases and strata. The hard sample covers
8 families (no TV-pureFF case); the isolated sample covers 8 families (ASHR has
no mutually solved input). These diagnostic selections never replace full
primary coverage.

## Correctness and compatibility

All **3,310** primary single-query SAT results pass independent evaluation of
every original assertion: 1,255 Z3 models, 1,037 GB models and 1,018 split models.
There are zero retrieval failures and zero invalid models. All eight SAT
models from the hard follow-up also validate. Multi-query intermediate models
are not checked; the full answer sequence is compared instead. UNSAT answers
are not proof-certified in this v1 comparison.

The full pass has no unresolved cross-solver answer disagreements, no conflicts
with supplied SAT/UNSAT annotations, and no SAT answer on the FMCAD FF-UNSAT
selection after the following independent adjudication.

**cvc5 1.3.4 split returns a false UNSAT on one archived small-field input.**
The original `r_3_32_32_system13.smt2` contains 32 assertions. Complete models
from Z3 and cvc5 GB independently satisfy every assertion. Reduction gives:

\[
ab+a+2b+2=0,\qquad b+2=0\quad\text{over }\mathbb F_3.
\]

Its unique solution is `a = b = 1`: the two left-hand sides are 6 and 3,
respectively, both zero modulo 3. All nine assignments were enumerated.
The split result reproduces in three fresh runs; GB and Z3 return SAT. The
failure also persists when disabling each of bit-sum preprocessing, field
polynomials, Gröbner-basis tracing, and global simplification separately.
These diagnostics do not establish the internal cause. The case is outside
the CAV24 main published selection. The raw measured answer is preserved;
`adjudications.json` marks it wrong for scores and figures.

The [minimal reproducer and full evidence](../tests/finite_field/results/paper-artifacts/disagreements/7664b9fa2577c47a8008e4ded3a004f0fecbb82f589cae6a39871c3fa6b555d3/README.md)
are included. No upstream issue has been submitted.

**Version recheck (2026-09-22): this bug also persists in cvc5 1.4.0**, official
CoCoA-enabled ARM64 build `b432cd7`. Split returns false UNSAT on the original,
reduced, and minimal inputs in three fresh runs each; default and explicit GB
return SAT. New GB models independently satisfy all 32 original and two minimal
assertions. The [1.4.0 evidence](../tests/finite_field/results/paper-artifacts/disagreements/7664b9fa2577c47a8008e4ded3a004f0fecbb82f589cae6a39871c3fa6b555d3/cvc5-1.4.0/README.md)
is recorded separately and does not change the historical 1.3.4 benchmark scores.

Seven illustrative inputs use the cvc5-specific `:incremental true` option.
Their Z3 primary outcomes are six errors and one timeout. A separate 21-run
compatibility diagnostic removes only this redundant option, enables cvc5
incrementality through its command line, and preserves all assertions. Z3
then solves six of the seven; the last still times out. GB solves all seven,
and split solves six. All returned complete answer sequences agree, including
the two-query `sat, unsat` example. These diagnostic successes do not replace
the original primary scores.

## Implications for the next implementation round

1. **Extend the existing bit-sum propagation across derived equalities and
   layers.** Split solves all 100 Seq inputs and all 32 ASHR inputs; Z3 solves
   25 and zero. The current `decompose_bitsums()` pass already recognizes
   Boolean quadratics, constant pins and no-wrap binary sums, but runs before
   algebra and has no equivalent propagation in the full SMT theory path.
   A worklist that revisits affected sums after deriving equalities is a
   concrete next experiment. Preserve the Booleanity, injectivity/no-wrap and
   dependency premises for eventual v2 proof reconstruction.
2. **Reduce expansion and memory use, especially in mixed-theory solving.**
   The 404 Z3 memory-limit failures span pure-field encodings, bit-sum sequences,
   determinism, and mixed soundness. On CirC-S, GB solves 170 against Z3's 100.
   Profile the selected failures to distinguish preprocessing/encoding growth
   from algebraic basis growth before choosing a larger elimination engine.
3. **Keep real cryptographic circuits as regression targets.** All four named
   SMTHash Poseidon/MiMC cases favor Z3 at 10 seconds, but the full QED2 family
   still favors split, 59 versus 44 solves. Preserve the wins while addressing
   the broader family rather than extrapolating from four circuits.

The supporting bit-sum diagnostics are separate from benchmark scores. On the
public `bitsum_6_layers_1` input, a 200-ms diagnostic yields six bit facts and
UNSAT. Depth two produces the same six facts before exhausting the algebra
budget; depth three reports twelve cumulative facts across two algebra calls.
A synthetic wire-alias test confirms the ordinary preprocessing already
removes simple aliases. These observations support investigating propagation
between layers; they do not prove a complete internal root cause or establish
an improvement without a measured implementation.

## Validation of the benchmark machinery

The independent evaluator passed 6,460 exhaustive small-bit-vector comparisons
against Z3 plus simultaneous-let scope checks. The runner's SAT, timeout,
memory-limit, multi-query and error classifications were checked. A delayed
reader regression verifies delivery of a 1-MiB input across repeated sampling
timeouts. Solver sources were held fixed throughout; all 47 measured changed
source hashes were verified before archival.

The first hard-case launch accidentally used Apple's Python 3.9.6. Its repeated
`communicate(input=None)` calls stopped feeding some large inputs after an
interrupted write, leaving solvers waiting with almost no CPU usage. Those
follow-up logs are explicitly **discarded**, retained under
`discarded-python39-followup`, and excluded from all scores and figures. All
hard/isolated runs and the compatibility diagnostic were repeated under the
primary pass's Python 3.14.2 runtime. The harness now rejects older runtimes.
Every primary timeout used at least 8.50 seconds of CPU (median 9.84 seconds),
with no corresponding stalled-input pattern. The earlier model validation is
retained because all 3,310 attempts completed and independently satisfied every
original assertion; no failed or partial model retrieval is being hidden.

## Corpus and scope

| Artifact | Native-field SMT files | Byte-distinct inputs |
| --- | ---: | ---: |
| [CAV 2023: Satisfiability Modulo Finite Fields](https://zenodo.org/records/7865471) | 2,473 | 2,403 |
| [CAV 2024: Split Groebner Bases](https://zenodo.org/records/10917330) | 2,708 | 2,654 |
| [FMCAD 2026: Finite-field proof production](https://zenodo.org/records/20133205) | 1,242 | 1,210 |
| Union | 6,423 | 4,212 |

Artifact rows overlap. The 408-file FMCAD FF-UNSAT selection contains 390
distinct inputs. All FMCAD inputs already occur in the CAV archives. The packed
CAV 2024 benchmark archive was checked: its 2,702 SMT files are identical to
unpacked members, with no additional inputs. Byte-level deduplication does not
claim to remove all semantically equivalent formulas.

Paper-specific views also preserve the CAV 2023 `full_runs.csv` input selection
(2,106 native-field files / 2,053 distinct inputs) and the CAV 2024 union of
`benchmark_set_general` and `benchmark_set_circ_deterministic` (1,140 files /
1,108 distinct inputs). These views distinguish original experimental workloads
from the larger complete archives; original ablation options are not replayed.

The inventory includes illustrative SMT examples, all available field sizes,
and all 640 mixed bit-vector/field soundness inputs. It also records 2,304
alternate BV/NIA encodings from CAV 2023, which do not exercise a finite-field
solver and are excluded from this comparison. The 640 CirC intermediate-format
completeness inputs and 1,242 Lean translations are not SMT solver inputs.
Vendored solver implementation tests are outside the experimental corpus.

The FMCAD archive's SHA256 was verified against the published checksum. Its
Docker image was inspected as nested archive data, without running or installing
the image. Only benchmark inputs and top-level experimental metadata were
extracted. CAV archives use HTTP byte ranges to skip their Docker images;
extracted ZIP members pass their CRC checks, and every input has a recorded
SHA256. The full CAV archive hashes are not claimed as verified.

## Protocol

- Apple M2 Max, 12 cores (8 performance, 4 efficiency), 64 GiB RAM,
  macOS 26.6.2, native ARM64 binaries.
- Current Z3 branch: Release, Apple clang++, `Z3_USE_LIB_GMP=OFF`.
  Base revision `cb83665b3039c165869a30da2955dd4655502e2a`, with uncommitted
  finite-field changes. Binary hashes and changed source hashes identify the
  measured state; the version string alone does not identify these changes.
- cvc5 1.3.4, build `f3b21c4`, official static GPL/CoCoA-enabled binary.
  `gb` is its confirmed default; the other configuration adds `--ff-solver=split`.
- Every distinct input/configuration receives one fresh-process run at a
  **10-second hard wall deadline and 4-GiB sampled RSS limit**. Eight benchmark
  workers run concurrently. RSS is sampled every 50 ms, so overshoots
  are possible. The external watchdog kills and reaps limited processes.
- A seeded input order and rotating solver order reduce systematic order bias.
  There is no CPU affinity. Timings include solver startup, parsing and shutdown.
  CPU time and per-process peak RSS are recorded separately.
- The artifact-specific `QF_BVFF` logic declaration is changed to `ALL` for
  **both** solvers on mixed-theory inputs. Assertions are unchanged; original
  and executed input hashes are recorded. Other commands remain in place.
- Timeouts, memory limits, unknown results, parser errors and crashes are
  retained. A process emitting a verdict and then failing is not counted solved.
  The one multi-query example is successful only with the complete answer sequence.
- Single-query SAT results receive a separate model-producing run and independent Python
  evaluation of every original assertion, including modular arithmetic and
  bit-vector semantics. Model retrieval/check failures remain visible. The one
  multi-query example is checked by its complete answer sequence, not by model
  validation at intermediate push/pop states.
- All definite answers are checked for cross-solver disagreements and for
  conflicts with supplied status annotations/the proof paper's UNSAT subset.
  Agreement is not a checked UNSAT proof; proof reconstruction remains v2.
  Confirmed wrong answers are retained in the raw log but excluded from solved
  counts and treated as failures in scores/plots. SAT witnesses, not majority
  votes, adjudicate disagreements. The run exposed a cvc5
  split false-UNSAT over F3; complete checked witnesses and a two-equation
  reproducer are retained with the final results.
- PAR-2 assigns twice the time limit to every unsuccessful run. Conditional
  timing ratios only compare mutually solved inputs. Cactus and scatter plots
  retain failures visibly or identify their exclusion explicitly.
- An isolated 64-input stratified sample gets three repetitions per solver.
  A separate 24-input follow-up gets 60 seconds with four concurrent workers
  and the same memory limit:
  the four named circomlib Poseidon/MiMC `SMTHash` circuits, plus 20
  family/outcome-stratified hard cases. These follow-ups never overwrite the 10-second
  full-corpus measurements and do not constitute full longer-budget coverage.

The original CAV experiments allowed 300 seconds; the proof artifact's full
reproduction uses 1,200 seconds and proof-checking pipelines. This study covers
their input sets under the user-selected budget, not their original protocols,
historical solver binaries, ablations, or proof-production performance.

## Reproduction

Run from this repository with Python 3.14 or later. The sampled subprocess
harness deliberately rejects older runtimes: the system Python 3.9 can stop
feeding large inputs after an interrupted write. Corpus download needs network
access; the FMCAD archive is approximately 4.6 GB. Downloading and extraction do
not execute artifact code.

The accompanying `corpus.zip` already contains all 4,212 original inputs and
their manifest. Extracting it supplies `/path/to/corpus` below and avoids the
download step. The exact 47 changed Z3 source files are preserved in
`z3-source-overlay.zip`; apply them over the recorded base commit before building.

```sh
python3 tests/finite_field/download_paper_artifacts.py \
  --cache /path/to/archive-cache --out /path/to/corpus
python3 tests/finite_field/benchmark_artifacts.py \
  --corpus /path/to/corpus --out /path/to/results \
  --z3 build-ff-cmake/z3 --cvc5 /path/to/cvc5 \
  --timeout 10 --jobs 8 --memory-mib 4096
python3 tests/finite_field/validate_artifact_models.py \
  --corpus /path/to/corpus --results /path/to/results
python3 tests/finite_field/adjudicate_artifacts.py \
  --corpus /path/to/corpus --results /path/to/results
python3 tests/finite_field/compatibility_artifacts.py \
  --corpus /path/to/corpus --results /path/to/results
python3 tests/finite_field/followup_artifacts.py \
  --corpus /path/to/corpus --results /path/to/results --mode hard
python3 tests/finite_field/validate_artifact_models.py \
  --corpus /path/to/corpus --results /path/to/results \
  --run-log hard.jsonl --timeout 90
python3 tests/finite_field/followup_artifacts.py \
  --corpus /path/to/corpus --results /path/to/results --mode isolated
python3 tests/finite_field/artifact_analysis.py /path/to/results
python3 tests/finite_field/analyze_artifact_followups.py /path/to/results
```

Use a fresh result directory for a different budget, worker count or binary.
Interrupted primary runs can resume with the same parameters. All stdout/stderr
diagnostics are preserved up to 64 KiB; SAT model retrieval is not truncated.
The report generator uses Matplotlib for vector graphs, and LaTeX for the PDF.
Its final mode requires complete primary results and reviewed findings text;
`--draft` exists only for layout inspection.
