# SMT-LIB proof-checker cross-cut: 2026-10-15

This is the **pre-arithmetic-integration snapshot**. The subsequent
[arithmetic certificate report](ARITHMETIC_CERTIFICATE_REPORT.md) records
the new verified bridge, fresh cross-cut, and proof-producer gaps without
overwriting these baseline measurements.

## Result

A fresh, stratified run of **900 UNSAT-annotated inputs across nine logics**
produced **192 obligation-free `ACCEPT` refutations (21.3% of selected inputs)**,
322 `PARTIAL` derivations, 127 rejected exports, and 252 phase timeouts.
Seven additional exports failed through Python expression-recursion limits.
There were no native checker errors.

The checker validated 514 complete derivations containing **2,324,118 DAG
nodes**, with **89,657 explicit obligations**. A partial derivation is not
a certified UNSAT result. The strongest full-proof coverage remains QF_UF
and QF_AX; arithmetic theory lemmas and arithmetic rewrites remain the
largest certification gap. Quantified input handling has improved, but
general quantified proof checking is still not supported.

Timed proof generation, export, and native checking took **344.18 seconds
elapsed**, with 32 workers. Export is the main pipeline bottleneck.
This evaluation changes no checker rules or trust policy.

## Corpus and measurement policy

The sample reuses the existing seed-42 manifests rather than selecting
easier inputs after seeing outcomes:

```text
C:\smtlib-benchmarks\proof_check_20261014_1034\manifest.json
C:\smtlib-benchmarks\proof_check_seven_20261014\manifest.json
```

For each logic, the original selection was
`random.Random(42).sample(sorted(UNSAT_annotated_paths), 100)`.
The archives are the official SMT-LIB 2025 non-incremental collection from
[Zenodo record 16740866](https://zenodo.org/records/16740866). The earlier
download manifests retain archive-checksum provenance; this run verified
the SHA-256 of every selected input before execution.

| Logic | Locally available UNSAT-annotated inputs | Selected |
|---|---:|---:|
| QF_UF | 4,361 | 100 |
| QF_AX | 279 | 100 |
| QF_LIA | 4,609 | 100 |
| QF_LRA | 683 | 100 |
| QF_IDL | 917 | 100 |
| QF_UFLIA | 183 | 100 |
| QF_AUFLIA | 760 | 100 |
| AUFLIA | 2,505 | 100 |
| UFLIA | 7,733 | 100 |
| **Total** | **22,030** | **900** |

This is an equally weighted logic cross-cut, **not** a population-weighted
SMT-LIB coverage estimate. Benchmark families can be highly correlated.
SAT/model certification, incremental sessions, bit-vectors, floating point,
strings, sequences, datatypes, and other undownloaded logics are outside
this measurement.

Proofs were freshly generated with the installed **Python Z3 5.1.0.0 API**
and Python 3.14.7 on Windows 11. The repository's separate `build\z3.exe`
is version 5.3.0 and was **not** used for the 900 proof-generation jobs.
Native checking used WSL and the frozen, already verified OCaml checker
with the n-ary `distinct` extension.

Each phase used up to 32 independent processes:

- **Proving:** 10-second external wall-clock limit, including interpreter
  startup and input parsing; also a 10-second solver timeout.
- **Export:** a separate 60-second external wall-clock watchdog after the
  atomic proof-generation completion marker.
- **Checking:** 10 seconds per native checker process, inside WSL.

All 147 proof-generation timeouts hit the external watchdog. Their solver
outcome/statistics were not recovered; they are censored observations,
not evidence that the input cannot be solved or checked. Watchdog polling
and process termination can make recorded times slightly exceed limits.
No timed-out or failed export was sent to the checker.

## End-to-end coverage

Every row has **100 selected inputs**. `Export T/F` means export timeout /
exception. `Not checked` is the sum of proof timeouts, export timeouts, and
export exceptions; it is not a separate additional failure category.

| Logic | Proved UNSAT | Proof timeout | Exported | Export T/F | ACCEPT | PARTIAL | REJECT | Check timeout | Not checked |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| QF_UF | 93 | 7 | 56 | 37 / 0 | 54 | 0 | 0 | 2 | 44 |
| QF_AX | 100 | 0 | 98 | 2 / 0 | 79 | 3 | 0 | 16 | 2 |
| QF_LIA | 79 | 21 | 69 | 7 / 3 | 12 | 51 | 0 | 6 | 31 |
| QF_LRA | 59 | 41 | 55 | 4 / 0 | 3 | 52 | 0 | 0 | 45 |
| QF_IDL | 48 | 52 | 25 | 19 / 4 | 2 | 20 | 0 | 3 | 75 |
| QF_UFLIA | 97 | 3 | 95 | 2 / 0 | 3 | 92 | 0 | 0 | 5 |
| QF_AUFLIA | 100 | 0 | 100 | 0 / 0 | 31 | 62 | 0 | 7 | 0 |
| AUFLIA | 91 | 9 | 91 | 0 / 0 | 3 | 13 | 75 | 0 | 9 |
| UFLIA | 86 | 14 | 86 | 0 / 0 | 5 | 29 | 52 | 0 | 14 |
| **Total** | **753** | **147** | **675** | **71 / 7** | **192** | **322** | **127** | **34** | **225** |

Thus 83.7% of selected inputs produced proofs, 75.0% exported, and 57.1%
reached `ACCEPT` or `PARTIAL`. Certification is **192/900**, not 514/900;
192/675 = 28.4% is the conditional rate among exported documents.

All seven export exceptions are recursion-depth failures in expression
conversion: `QF_LIA_038`, `QF_LIA_052`, `QF_LIA_090`,
`QF_IDL_015`, `QF_IDL_021`, `QF_IDL_030`, and `QF_IDL_084`.
They are exporter failures, not native rejections.

## What is actually checked

The native protocol is authoritative: `ACCEPT`/exit 0, `PARTIAL n`/exit 3,
`REJECT`/exit 1. Python's predicted obligation count never determines
acceptance. A supplemental native audit calls the same extracted decoding
and node-checking functions to categorize pending leaves. Its totals
agree with the original native result for **all 514 validated documents**.
Audit time is excluded from the performance tables.

| Logic | Validated DAGs | DAG nodes | Pending `th-lemma` | Pending `rewrite` | Pending `sk` | Total obligations |
|---|---:|---:|---:|---:|---:|---:|
| QF_UF | 54 | 1,192,257 | 0 | 0 | 0 | 0 |
| QF_AX | 82 | 221,215 | 0 | 3 | 0 | 3 |
| QF_LIA | 63 | 60,037 | 1,305 | 12,128 | 0 | 13,433 |
| QF_LRA | 55 | 109,639 | 11,507 | 7,135 | 0 | 18,642 |
| QF_IDL | 22 | 256,826 | 20,804 | 3,921 | 0 | 24,725 |
| QF_UFLIA | 95 | 275,727 | 25,213 | 1,548 | 0 | 26,761 |
| QF_AUFLIA | 93 | 207,132 | 27 | 5,891 | 0 | 5,918 |
| AUFLIA | 16 | 291 | 5 | 51 | 1 | 57 |
| UFLIA | 34 | 994 | 42 | 76 | 0 | 118 |
| **Total** | **514** | **2,324,118** | **58,903** | **30,753** | **1** | **89,657** |

The remaining **2,234,461 nodes (96.1% of nodes in validated documents)**
have no local obligation. That node percentage is not a full-refutation
coverage rate: one pending leaf can invalidate an otherwise large claim
of certification. Rejected and timed-out DAGs are excluded from this census.

The exercised verified fragment includes unit resolution and discharged
hypotheses, equality/congruence/path transitivity, Boolean reasoning and
supported rewrite schemas, array lemmas/rewrites, checked definition
introductions/applications, and n-ary `distinct` expansion. In these
validated DAGs:

- All **17,399 `def-axiom` nodes** are discharged without obligations.
  No `def-axiom` is trusted merely because of its tag.
- All **151 `intro-def` and two `apply-def` nodes** pass their checked
  expansion/freshness rules.
- **13,509 array `th-lemma` instances** are checked. The other 58,903
  `th-lemma` nodes remain obligations; their rule name is not a proof.

The three QF_AX partial proofs are still `QF_AX_022`, `QF_AX_041`, and
`QF_AX_085`, each with one unsupported rewrite. The earlier detailed
analysis identifies missing checked naming witnesses in the first two
and stronger guarded-ITE reasoning in the third; this run does not remove
those obligations.

The exporter predicts 89,723 obligations, **66 too many across 13
documents**, because native rewriting discharges more than its diagnostic
allowlist predicts. The native audit resolves that discrepancy: 30,753
pending rewrites, not the predicted 30,819. No proof is rejected for a
diagnostic-count mismatch.

### Quantified boundary

The 127 native rejections all occur in AUFLIA/UFLIA. The supplemental
audit locates the first failure at:

| Failure stage | AUFLIA | UFLIA | Total |
|---|---:|---:|---:|
| Well-formed-expression check | 74 | 45 | 119 |
| `proof-bind` node checking | 0 | 7 | 7 |
| First `asserted` node checking | 1 | 0 | 1 |

These are rejected certificate shapes, not new UNSAT certifications or
solver correctness failures. Pending histograms are not taken from
partially traversed rejected DAGs.

The eight accepted quantified-logic inputs are `AUFLIA_031`,
`AUFLIA_049`, `AUFLIA_053`, `UFLIA_034`, `UFLIA_076`,
`UFLIA_086`, `UFLIA_088`, and `UFLIA_094`. They contain quantified
expressions, but their refutations use the supported propositional and
equational structure, **not general quantifier instantiation or
Skolemization rules**. The one encountered `sk` leaf in a validated
derivation remains pending. These results must not be advertised as
general AUFLIA/UFLIA proof support.

## Performance

### Completed-phase latency

Seconds below are **median / nearest-rank p95**, with the completed
population in parentheses. Proving includes parsing, solver execution,
and proof retrieval, timed inside the worker before importing Z3; its
external cap additionally includes interpreter startup. Export includes
conversion and writing the proof JSON. Native checking includes process
startup, file reading, parsing, and checking, but no per-proof WSL launch,
F* invocation, or SMT-solver call.

`Check` here includes only `ACCEPT`/`PARTIAL`, **not fast rejections**.
All columns are conditional on completion and must be read together with
the timeout table above.

| Logic | Prove seconds (n) | Export seconds (n) | Native check seconds (n) |
|---|---:|---:|---:|
| QF_UF | 0.589 / 4.569 (93) | 5.053 / 52.234 (56) | 0.382 / 5.889 (54) |
| QF_AX | 0.188 / 0.439 (100) | 1.420 / 12.146 (98) | 0.357 / 6.940 (82) |
| QF_LIA | 0.275 / 4.973 (79) | 0.399 / 9.539 (69) | 0.068 / 1.299 (63) |
| QF_LRA | 0.164 / 5.218 (59) | 0.036 / 22.477 (55) | 0.050 / 2.853 (55) |
| QF_IDL | 0.785 / 2.720 (48) | 8.019 / 52.627 (25) | 0.835 / 3.512 (22) |
| QF_UFLIA | 0.158 / 0.409 (97) | 0.374 / 8.250 (95) | 0.072 / 1.096 (95) |
| QF_AUFLIA | 0.155 / 0.311 (100) | 0.534 / 13.740 (100) | 0.086 / 5.976 (93) |
| AUFLIA | 0.163 / 0.486 (91) | 0.099 / 0.366 (91) | 0.049 / 0.068 (16) |
| UFLIA | 0.204 / 0.995 (86) | 0.572 / 4.341 (86) | 0.064 / 0.331 (34) |
| **All** | **0.184 / 2.412 (753)** | **0.527 / 19.631 (675)** | **0.125 / 4.098 (514)** |

### Censored and total cost

| Phase | Attempted | Timeouts | Other unsuccessful outcomes | All-attempt median / p95 seconds | Sum of per-process wall seconds |
|---|---:|---:|---|---:|---:|
| Prove | 900 | 147 | 0 | 0.212 / 10.047 | 1,876.07 |
| Export | 753 | 71 | 7 recursion failures | 0.825 / 60.534 | 6,784.74 |
| Native check | 675 | 34 | 127 rejects, 0 errors | 0.088 / 10.017 | 716.58 |

The proving/export batch took **305.20 seconds** and the subsequent native
batch **38.79 seconds**. Their timed pipeline, including intermediate
bookkeeping, took **344.18 seconds**. Initial input hashing/tool snapshots,
subsequent database logging, the nine-input pilots, and supplemental
auditing are not included. Summed process wall times overlap under
parallel execution and are **not CPU time**.

Successful exports alone consumed 2,478.13 summed wall seconds, compared
with 366.06 for validated native checks. Export also lost 71 jobs to its
60-second limit, notably 37 QF_UF and 19 QF_IDL jobs. Optimizing recursive
expression conversion and export throughput is therefore at least as
important for end-to-end coverage as optimizing native checking.
Native timeouts, especially the 16 QF_AX cases, remain a distinct
bottleneck. These are one-run, contended-machine measurements, not
single-core microbenchmarks or a demonstrated speedup over another checker.

### Proof-search workload statistics

These are Z3-reported statistics from **successfully generated proofs**,
not native-checker memory or host peak RSS. Missing statistics are omitted,
not treated as zero. Conflict counts give their own reporting denominator.
Full per-theory statistics are retained in every successful `prove.json`
and in `z3agent.db`.

| Logic | Reported max-memory MB: median / max | Conflicts: median / max (n reporting) |
|---|---:|---:|
| QF_UF | 40.22 / 496.85 | 1,370 / 26,256 (91) |
| QF_AX | 18.61 / 149.16 | 49 / 29,576 (98) |
| QF_LIA | 19.85 / 272.52 | 1 / 17,321 (50) |
| QF_LRA | 18.04 / 348.44 | 1 / 7,579 (54) |
| QF_IDL | 26.89 / 527.14 | 24 / 7,356 (47) |
| QF_UFLIA | 18.56 / 144.71 | 103 / 23,341 (65) |
| QF_AUFLIA | 18.70 / 43.93 | 48 / 5,774 (87) |
| AUFLIA | 18.64 / 147.12 | 1 / 270 (83) |
| UFLIA | 19.98 / 188.06 | 1 / 412 (67) |

Array workloads report `array ax1`, `array ax2`, and `array ext ax`;
arithmetic workloads report the corresponding simplex/bound-propagation,
conflict, and integer-cut counters when those engines are exercised.
No aggregate native-checker memory or timed-out-solver memory was measured.

## Comparison with previous reports

This is a **fresh proof-generation/export run**, not a paired checker
experiment over byte-identical DAGs. Historical results below match input
IDs, not necessarily the generated proof documents or machine load.

| Logic | Historical ACCEPT | Fresh ACCEPT | Historical reference |
|---|---:|---:|---|
| QF_UF | 56 | 54 | Latest post-`distinct` archived recheck |
| QF_AX | 79 | 79 | Latest post-`distinct` archived recheck |
| QF_LIA | 12 | 12 | Seven-logic post-array-extension recheck |
| QF_LRA | 3 | 3 | Seven-logic post-array-extension recheck |
| QF_IDL | 2 | 2 | Seven-logic post-array-extension recheck |
| QF_UFLIA | 3 | 3 | Seven-logic post-array-extension recheck |
| QF_AUFLIA | 28 | 31 | Seven-logic post-array-extension recheck |
| AUFLIA | 0 | 3 | Seven-logic post-array-extension recheck |
| UFLIA | 0 | 5 | Seven-logic post-array-extension recheck |

`QF_UF_015` now hits the 10-second native limit, and `QF_UF_095` hits
the 60-second export limit. These explain the two lower UF accept counts;
neither became a native `REJECT` or `PARTIAL`. No formerly accepted
reference input became rejected or partial in this run.

`QF_AUFLIA_019`, `QF_AUFLIA_034`, and `QF_AUFLIA_047` move from
historical `PARTIAL` to obligation-free acceptance. The 50 newly
structurally validated quantified-logic exports comprise eight accepted
and 42 partial derivations; 127 still reject. Historical seven-logic
results predate the current checked-definition and quantified-expression
handling, so neither aggregate obligation differences nor these accept
counts isolate a single rule's effect. No performance-regression or
speedup claim is made from the differing validated sets.

## Trust boundary and scope of certification

`ACCEPT` means the document supplies a closed false root, every DAG entry
passes the kernel, and no pending leaf remains. Asserted leaves require
exact membership in the supplied original assertion list. Definitions
are expanded capture-avoidantly, with final freshness checked against
**all** original assertions, including unused assertions and binder bodies.
`def-axiom`, `intro-def`, and `apply-def` are checked, not trusted tags.
The exporter emits the legacy `check_original_assertions: false` field;
in this checker version, exact asserted-input membership is mandatory
regardless of that field.

The soundness claim is under the formal interpretation contracts for the
supported operators, the extraction/compiler/runtime assumptions, and
correct association of the exported assertion list with the SMT-LIB input.
The native checker consumes JSON, **not SMT-LIB**: parsing inputs through
the Z3 API and serializing their assertions is outside its verified kernel.
Input hashes establish provenance, not a verified SMT-LIB parser.

The OCaml shim still represents F* integers as native 63-bit integers.
There is no general arbitrary-precision/extraction-overflow guarantee;
these results must not be extrapolated to unbounded numeric inputs or
wide bit-vector arithmetic. Native acceptance is not a claim that all
SMT-LIB theories, quantifier rules, or preprocessing transformations have
been formalized.

## Artifacts and reproduction

The complete main run is retained at:

```text
C:\smtlib-benchmarks\proof_check_crosscut_20261015_1327\full
```

It contains `manifest.json` with all 900 paths/input hashes,
`run_metadata.json`, `results.json`, incremental `results.jsonl`,
`outcomes.csv`, `summary.json`, `checks.json`, per-input proof-generation
statistics/logs/exported certificates, and **900 benchmark entries in
`z3agent.db`**. `native_audit.json` records exact obligation categories
and first rejection stages; `historical_comparison.json` records
input-ID transitions. `supplemental_provenance.json` hashes supplemental
tools/results and exported certificates without modifying the original
run's metadata.

The frozen `tools` directory contains the checker, original runner,
exporter, source manifests, F* sources, and OCaml runtime sources.
The run is based on Git commit
`11306ced808398e9b03686f096c63771dee8ba82` **plus the archived uncommitted
working-tree patch and source snapshots**, not that commit alone.

| Component | SHA-256 |
|---|---|
| Native checker | `b4b430fe820940b03523f2e8ed017ac8c8a952542f5c08e30f6df141e874b593` |
| Exporter | `7f6e5a191f98037529c60666e1ea63256fea2fcbfa2d8c8cb9653572894fac1f` |
| Original main-run driver | `29709934ec4a0f3f0f576e683292cb8ffa1d4fc98bb5ac0e69bdbb2ffb21fd75` |
| UF/AX source manifest | `597b18136a861ee9155352f6f24b068cf478443ab0507560a5f4ba1c3f0a2565` |
| Seven-logic source manifest | `604d8df74b2928e6326a5f042dfc922331c487d428e137576b0864d8c6bc8001` |

The separately retained `run_crosscut_replay.py` adds a snapshot option,
so reproducing the evaluation does not silently pick up later exporter or
checker changes. Its nine-logic replay pilot reproduced the original
pilot's status, node, and obligation totals. On this machine, with the
same Python Z3 5.1.0.0 installation and benchmark input paths:

```powershell
$run = 'C:\smtlib-benchmarks\proof_check_crosscut_20261015_1327\full'
python "$run\tools\run_crosscut_replay.py" `
  --out C:\smtlib-benchmarks\proof_check_crosscut_reproduction `
  --tool-snapshot "$run\tools"
```

The destination must not already exist. Add `--pilot` for one input per
logic. Timeouts and exact proof-search timing can vary between runs.
The frozen checker can also recheck each saved `proof.json` directly in
WSL; no F* re-verification is performed per certificate.

The historical reference records are:

```text
C:\smtlib-benchmarks\proof_check_array_rewrites_20261015_0815\distinct-extension\after.json
C:\smtlib-benchmarks\proof_check_seven_20261014\array_extension_final\after.json
```

The separate three-repeat CLI sanity measurement used Z3 **5.3.0 without
proof generation**, on `QF_UF_000`: 343 / 346 / 350 ms
minimum / median / maximum, logged in the parent directory's
`cli_sanity.db`. It confirms the local command-line path only and is not
mixed into any proof-checker performance result above.
