# SMT-LIB proof-checker cross-cut: current proof producer, 2026-10-16

## Current PR #11208 result

This measurement is frozen at the producer revisions identified below.
It predates the subsequent `0af294e26` branch update and the installed-Z3
build/test harness; their toolchain validation is not a new cohort replay.

With the latest arithmetic-proof PR and the integration fix described
below, the unchanged **900-input cohort still yields 334 obligation-free
`ACCEPT` refutations (37.1%)**. **All 334 preceding accepts are retained;
there are no new accepts.** The additional internal arithmetic evidence
does not yet increase end-to-end native checker coverage.

| Outcome | Preceding coverage extensions | Initial PR build | Corrected PR build |
|---|---:|---:|---:|
| `ACCEPT` | 334 | 333 | **334** |
| `PARTIAL` | 254 | 229 | 242 |
| `REJECT` | 143 | 141 | 142 |
| Solver `UNKNOWN` | 119 | 150 | 134 |
| Whole-process timeout | 48 | 45 | 46 |
| Allocation abort | 2 | 2 | 2 |

The remaining 15 changed outcomes relative to the preceding run are all
solver timeouts: twelve former partials, one former rejection, and two
former whole-process timeouts. These are resource regressions or
resource-classification changes, **not discharged proof obligations**.
The 134 solver unknowns comprise 132 timeouts and two out-of-memory
results. Both allocation aborts recur on the same inputs.

### Producer integration and regression repair

The checked-out branch is `arithmetic-proof-evidence`, from
[PR #11208](https://github.com/Z3Prover/z3/pull/11208), with PR head
`28aab4c094978abd29743fb26385038a66b80ad5`. Local merge
`5e707a253982b3d3cf2b3010e0769d188d1712ee` incorporates the two newer
master fixes through `90c3d1839`. The measured corrected producer also
includes the uncommitted `theory_lra.cpp` fix and its `lp_evidence.cpp`
regression; the merge hash alone does not identify that binary.

The initial PR build returned `UNKNOWN invalid rational value passed as
an integer` on **19 inputs**, including the formerly accepted
`QF_LIA_024`. Its new source-expression Farkas validation passed rational
weights directly to a helper that constructs coefficients in each
premise's arithmetic sort. The legacy proof checker already clears all
denominators before calling that helper.

The correction applies the same **positive common denominator scale**
to all weights used during validation. Exported coefficients, evidence
checks, and unsupported-evidence guards are unchanged. A reduced
four-inequality integer regression returns `UNKNOWN` with the frozen
initial PR executable and `SAT` with the corrected producer. In the full
fixed replay, all 19 rational-construction errors disappear: thirteen
inputs become partial, one accepts, one rejects, three reach solver
timeouts, and one reaches the external watchdog. `QF_LIA_024` is restored.

Windows Z3, its Python bindings, and the statically linked WSL producer
were rebuilt from this checkout. All 116 native tests, eleven native
bridge regressions, and eight checker CLI tests pass. The full native
F* dependency pipeline and proof regressions verify using the freshly
built Windows Z3 5.3.1, with a fresh cache and its actual version passed
through F*'s documented `--z3version` check. Explicit arithmetic proof
steps were needed for the new SMT automation; the **35 OCaml runtime
modules remain byte-identical** to the preceding coverage executable.
No acceptance-policy change is being attributed to the new producer.

### Paired coverage and limits

The **576 inputs valid in both runs** retain exactly the same proof-node
counts and pending-obligation counts: **21,470,839 proof nodes and
105,820 pending obligations**. One partial, `QF_LIA_073`, marshals one
additional expression (3,597 instead of 3,596), but retains 3,247 proof
nodes and 165 obligations. The smaller aggregate pending count versus
the preceding run reflects the twelve partials lost to solving timeouts,
not improved discharge.

Every per-logic acceptance count is unchanged: QF_UF 89, QF_AX 90,
QF_LIA 31, QF_LRA 7, QF_IDL 11, QF_UFLIA 8, QF_AUFLIA 59,
AUFLIA 14, and UFLIA 25. The corrected batch takes **765.81 seconds**.
On the paired 576 valid inputs, median end-to-end latency changes from
169.3 to 184.0 ms and median checking time from 49.0 to 49.1 ms.
This is not a speedup claim; the resource losses remain visible.

The PR introduces internally checked arithmetic evidence, but **native
integer evidence export and the polynomial certificate's native AST
correspondence bridge remain pending**. The native F* document pipeline
does not accept an arithmetic tag merely because an internal C++ checker
accepted a certificate. Missing evidence, quantified binders, and the
existing model-contract inhabitance gap described below remain limitations.
`PARTIAL` still does not certify UNSAT.

### Reproduction and frozen evidence

All 900 manifest records and hashes match the preceding run. The
measurements retain eight workers, a 10-second solver timeout, a
60-second process watchdog, and a 4 GiB address-space limit per child.
The preceding 334-accept run remains at
`C:\smtlib-benchmarks\proof_coverage_20261016\final`. Both new producer
runs, raw outputs, comparison CSV/JSON, source snapshots, exact working-tree
patch, build logs, binary hashes, and provenance are preserved at:

```text
C:\smtlib-benchmarks\proof_pr11208_20261016\full
C:\smtlib-benchmarks\proof_pr11208_20261016\fixed
corrected checker SHA256:
ed0b8c8f5743e657199e98182294ffc6fc5d70502b972450cc951a068aa4870f
```

The corrected source is reproduced by applying `working-tree.patch` to
`producer-source-base.tar`; see `toolchain_provenance.json` for the exact
native-library and executable hashes. The existing
[native build instructions](OCAML_CHECKER_REPORT.md#build-status-and-trust-boundary)
select the source-built Windows verifier and the PR checker output directory.

## Archived coverage extension result

The same **900-input, nine-logic cohort** now produces **334 obligation-free
`ACCEPT` refutations (37.1%)**, up from 231 (25.7%). **All 231 preceding
accepts are retained.** There are 103 new complete refutations: 96 former
partials and seven former rejections. `PARTIAL` still does not certify UNSAT.

| Outcome | Native baseline | Coverage extensions |
|---|---:|---:|
| `ACCEPT` | 231 | **334** |
| `PARTIAL` | 318 | **254** |
| `REJECT` | 192 | **143** |
| Solver `UNKNOWN` | 121 | 119 |
| Whole-process timeout | 36 | 48 |
| Allocation abort | 2 | 2 |

The rejection reduction is not 49 new complete proofs. Of the 192 former
rejections, **seven now accept, 30 become partial, 12 reach the external
watchdog, and 143 still reject**. The twelve new watchdog outcomes expose
work formerly avoided by early rejection; they must not be counted as
successful derivations.

### Features selected and implemented

The optional native `--diagnostics` pass reports typed unmet obligations,
their first proof-node indices, and bounded sort-aware expression
fingerprints. Fingerprints retain operator structure and small exact
rationals and alpha-alias opaque declarations; they are coarse diagnostic
keys, not evidence of equivalence. Profiling all **318 baseline partials**
reproduced every ordinary checker pending count exactly. Ranking by
**proofs blocked by a sole fingerprint family**, rather than leaf counts,
put integer reflexive comparisons first (six proofs), followed by
`0 <= x` / `x >= 0` duality over integers (four) and reals (three), and
strict-comparison negation (two).

`Z3ArithmeticRewrite.fst` now checks those comparison families, equivalent
affine differences, constant comparisons, and integer term normalization
using exact polynomial linearization and cancellation. Strict and
non-strict comparisons remain distinct. Integer subtraction, addition
permutations, and arithmetic constants are covered without introducing
trusted rewrite names. This completes **96 former partial proofs**; all
have the same proof-node counts as the baseline. It does not add producer
evidence for bare arithmetic theory tags.

Typed observational equality now preserves matching non-Boolean operand
sorts and a distinct `Observational` judgment. The checked same-model
fragment uses truth agreement for Boolean terms and value agreement as a
sufficient witness for other sorts. Equality evidence can establish this
observation; observational evidence is **not converted into ordinary
equality**. `iff~` remains Boolean-only. General naming/model-extension
transformations are not admitted without their corresponding witnesses.

An integration blocker remained after adding the typed relation: existing
checked fresh-definition expansion made a congruence conclusion
syntactically reflexive, but redundant observational premises caused the
ordinary congruence rule to reject. The checker now proves that identity
independently of the redundant premises. It still checks every premise
and DAG entry, propagates hypotheses and obligations, and rejects
non-reflexive ordinary congruence based on observational premises alone.
This completes seven formerly rejected array proofs:
`QF_AX_022`, `QF_AX_041`, `QF_AX_087`, `QF_AX_091`, `QF_AX_095`,
`QF_AUFLIA_045`, and `QF_AUFLIA_046`. The last five restore all previously
identified accepted array inputs lost at the non-Boolean relation boundary.

All **45 old non-Boolean observational-declaration rejections** move past
that boundary: seven accept, 27 become partial, and eleven hit the
watchdog. The four old `monotonicity` rejections become three partials and
one watchdog outcome. The remaining 143 rejections are the unchanged
125 expression-well-formedness failures, 17 `proof-bind` failures, and
one asserted-input-membership failure.

### Per-logic coverage

Every row still contains the same 100 selected inputs. Resource outcomes
are excluded from the three displayed result columns, not silently
classified as rejections.

| Logic | Baseline accept / partial / reject | Extended accept / partial / reject |
|---|---:|---:|
| QF_UF | 89 / 3 / 0 | 89 / 3 / 0 |
| QF_AX | 85 / 0 / 5 | **90 / 0 / 0** |
| QF_LIA | 12 / 55 / 2 | **31 / 37 / 0** |
| QF_LRA | 2 / 44 / 19 | **7 / 57 / 0** |
| QF_IDL | 1 / 34 / 15 | **11 / 30 / 0** |
| QF_UFLIA | 4 / 93 / 1 | **8 / 91 / 0** |
| QF_AUFLIA | 30 / 57 / 6 | **59 / 34 / 0** |
| AUFLIA | 3 / 12 / 77 | **14 / 1 / 77** |
| UFLIA | 5 / 20 / 67 | **25 / 1 / 66** |

The 588 completed valid derivations contain **23,564,835 proof nodes** and
183,865 pending obligations. Comparing that total directly with the
baseline's 184,899 obscures newly reachable partial derivations. On the
**548 inputs valid in both runs**, proof-node counts are identical and
pending obligations fall from **180,352 to 150,771**, a reduction of
29,581 (16.4%). No common valid input acquires additional obligations.
One former partial (`QF_LRA_034`) instead times out in solving, and three
former solver unknowns now become partial. These resource variations do
not demonstrate a change in kernel-rule coverage.

### Measurement, artifacts, and semantic limits

The final run retains the baseline producer **Z3 5.3.1**, all 900 input
hashes, eight workers, a 10-second internal solver timeout, a 60-second
whole-process watchdog, and a 4 GiB address-space limit per child. The
baseline and final manifest records are identical. The C++ producer is
unchanged at `5a645fcc6de7e1483048cad08998567cc86411fe`; the extended kernel
is an uncommitted source change, not a new revision of that producer.

The final batch took **777.20 seconds**, versus 672.70 seconds for the
baseline. It checks more previously rejected work and is **not a speedup
claim**. For the paired 548 valid inputs, median end-to-end time changes
from 149.9 to 156.8 ms and median checking time from 34.6 to 36.0 ms.
The 119 solver unknowns comprise 118 timeouts and one out-of-memory result.
Both allocation aborts recur on the same inputs.

The baseline remains archived at
`C:\smtlib-benchmarks\proof_check_native_20261016\full`. Typed fingerprint
profiles, rankings, and the profiling executable/script are archived at
`C:\smtlib-benchmarks\proof_obligations_20261016`. The final executable,
raw outputs, manifest, metadata, comparison CSV/JSON, and a 111-file
source snapshot with per-file hashes are at:

```text
C:\smtlib-benchmarks\proof_coverage_20261016\final
checker SHA256:
b61e9bcb739fdc94f53f79aeb0571e301fca21a413a0e0365a37270fc641c23b
```

The affected F* modules and focused proof regressions verify; eleven native
bridge tests and eight CLI tests pass. The new arithmetic semantic lemmas
use standard `numeric_operators` laws and local value-typing premises for
the actual operands, rather than relying on the old all-environments
typing premise. **The existing end-to-end model-contract inhabitance gap
is not repaired**: the global Boolean/integer typing assumptions still
quantify over untyped environments. There is no unconditional SMT-LIB
soundness theorem or proved native-API semantic correspondence.

Real-valued term equality is deliberately not inferred from equality of
the numeric projection. Missing rewrite families, unsupported arithmetic
explanations, and quantified proof binders remain genuine obligations or
rejections. Input membership, freshness, scoping, exact evidence checks,
and the closed false root are not bypassed to obtain these gains.

## Archived native-only baseline

The remainder records the preceding native-only run, before the coverage
extensions above. Its counts and rule census are baseline measurements.

### Baseline result

The fixed **900-input, nine-logic UNSAT sample** now produces **231
obligation-free `ACCEPT` refutations (25.7%)**, 318 `PARTIAL` derivations,
192 rejections, 121 solver `UNKNOWN` results, 36 whole-process timeouts,
and two allocation aborts. **`PARTIAL` is not certified UNSAT.**
Of the 121 unknowns, 118 report timeout and three report out of memory.

The direct executable parses SMT-LIB, generates proofs using statically
linked **Z3 5.3.1**, marshals native ASTs into F* algebraic datatypes with
identity caches, and runs the extracted checker. There is no Python proof
exporter, proof JSON, external solver process, or runtime F* invocation.
The Python benchmark driver only schedules executables and records results.

The 549 accepted/partial DAGs contain **22,277,998 proof nodes**. The
checker discharges **85,974 supplied Farkas steps** and 13,962 array theory
lemmas, but leaves **184,899 explicit obligations**. These include 570
supplied Farkas steps that do not pass the supported arithmetic check;
their labels do not make them trusted facts.

The native batch took **672.70 seconds with eight workers**. Among completed
valid derivations, median end-to-end latency was **153.4 ms** and median
checking time **34.8 ms**. Across all 900 attempts, including resource-limited
runs, end-to-end median/p95 was **206.3 ms / 32.95 s**. Checking dominates
completed valid work in aggregate; large-proof tails and memory exhaustion
remain important despite eliminating serialization.

The preceding Python/JSON run accepted 193 inputs. The new run gains 52
accepted inputs and loses 14, for a **net increase of 38**, not a uniform
improvement. The producer, proof shapes, concurrency, and resource budgets
differ; this is **not a controlled measurement of JSON-removal speedup or
new kernel-rule coverage**. No checker rules or trust policy were changed
for this reevaluation.

## Corpus, provenance, and measurement policy

The cohort is unchanged: 100 inputs per logic selected originally by
`random.Random(42).sample(sorted(UNSAT_annotated_paths), 100)`.
All 900 input hashes were checked against the original manifests and
matched the preceding cross-cut's manifest exactly:

```text
C:\smtlib-benchmarks\proof_check_20261014_1034\manifest.json
C:\smtlib-benchmarks\proof_check_seven_20261014\manifest.json
```

The inputs come from the official SMT-LIB 2025 non-incremental archives,
[Zenodo record 16740866](https://zenodo.org/records/16740866). The locally
available UNSAT-annotated populations remain QF_UF 4,361; QF_AX 279;
QF_LIA 4,609; QF_LRA 683; QF_IDL 917; QF_UFLIA 183; QF_AUFLIA 760;
AUFLIA 2,505; UFLIA 7,733: **22,030 total**.

This equally weighted sample is not a population-weighted SMT-LIB coverage
estimate. SAT/model certification, incremental sessions, BV, FP, strings,
sequences, datatypes, and other unsampled logics are outside the experiment.

Both native checker and standalone solver were rebuilt from source commit
`5a645fcc6de7e1483048cad08998567cc86411fe`. The checker uses OCaml 5.3.0,
Zarith exact integers, the official Z3 OCaml/C bindings, and static
`libz3`, compiled in Release mode. WSL2 exposed 32 logical CPUs and about
62.8 GiB RAM; this was a shared machine, not an isolated benchmark host.

The primary native run used **eight workers**, a **10,000 ms internal
solver timeout**, a **60-second external end-to-end watchdog**, and a
**4 GiB virtual-address-space limit per child**. The watchdog covers
startup, file reading, parsing, solving, proof retrieval, marshaling,
checking, and process teardown. Limits can be exceeded slightly by
scheduling/polling; a solver timeout is not a bound on the whole process.
The run began at `2026-10-16T17:11:55Z`.

The CLI's `--stats` emits phase times only after document checking returns.
Consequently phase statistics cover the 741 completed `ACCEPT`, `PARTIAL`,
and `REJECT` runs, not the 159 remaining outcomes. Whole-process timeouts
cannot reliably be assigned to solving, marshaling, or checking.

The separate proof-disabled standalone solver batch ran **after**, not
concurrently with, the native batch. It used the same inputs, source
revision, eight workers, 4 GiB address-space limit, and external watchdog,
with `-smt2 -st -T:10`. Sharing a version does not make the shell's
logic-sensitive frontend/configuration identical to the checker's
`parse_smtlib2_string` plus default solver API. The difference between
these batches is therefore not a pure proof-production overhead estimate.

## End-to-end coverage

Each logic has 100 inputs. `UNKNOWN` is split by the solver's actual reason;
allocation aborts are separate process failures, not certificate rejections.

| Logic | ACCEPT | PARTIAL | REJECT | Solver timeout | Solver OOM | Wall timeout | Allocation abort |
|---|---:|---:|---:|---:|---:|---:|---:|
| QF_UF | 89 | 3 | 0 | 5 | 0 | 3 | 0 |
| QF_AX | 85 | 0 | 5 | 0 | 0 | 10 | 0 |
| QF_LIA | 12 | 55 | 2 | 17 | 3 | 10 | 1 |
| QF_LRA | 2 | 44 | 19 | 35 | 0 | 0 | 0 |
| QF_IDL | 1 | 34 | 15 | 43 | 0 | 7 | 0 |
| QF_UFLIA | 4 | 93 | 1 | 2 | 0 | 0 | 0 |
| QF_AUFLIA | 30 | 57 | 6 | 0 | 0 | 6 | 1 |
| AUFLIA | 3 | 12 | 77 | 8 | 0 | 0 | 0 |
| UFLIA | 5 | 20 | 67 | 8 | 0 | 0 | 0 |
| **Total** | **231** | **318** | **192** | **118** | **3** | **36** | **2** |

Thus 741/900 reached a completed document-check result and 549/900 (61.0%)
produced valid derivations with or without obligations. Full certification
is **231/900**, not 549/900.

The three solver OOM results are `QF_LIA_026`, `QF_LIA_080`, and
`QF_LIA_087`. `QF_LIA_070` and `QF_AUFLIA_004` abort with
`Fatal error: allocation failure during minor GC`. Both still abort in a
separate **8 GiB** address-space-limit rerun. That supplement does not
replace their primary outcomes. These failures need memory/scalability
work; they must not be counted as successful or invalid proofs.

## What is covered, and what remains

A separate, untimed native audit calls the **actual extracted**
`Z3ProofDocument.check_document`, `check_entry`, and arithmetic functions.
It matches the primary disposition, pending count, and node count for
all **741 completed documents**. One audit solve (`QF_IDL_093`) initially
timed out at the 10-second boundary; an isolated retry with the same
timeout reproduced its 657,851 nodes and 12,634 obligations. Initial and
retry records are retained. Auditing does not change primary timings.

Only complete valid DAGs contribute to the following census; prefixes of
rejected or timed-out proofs are excluded.

| Logic | Valid DAGs | Proof nodes | Checked Farkas | Pending arithmetic | Pending rewrites |
|---|---:|---:|---:|---:|---:|
| QF_UF | 92 | 17,643,706 | 0 | 0 | 188 |
| QF_AX | 85 | 275,363 | 0 | 0 | 0 |
| QF_LIA | 67 | 530,844 | 8,825 | 27,930 | 14,215 |
| QF_LRA | 46 | 185,997 | 4,746 | 9,789 | 26,862 |
| QF_IDL | 35 | 2,403,317 | 35,210 | 43,623 | 15,565 |
| QF_UFLIA | 97 | 1,089,878 | 37,158 | 37,494 | 3,181 |
| QF_AUFLIA | 87 | 147,727 | 27 | 0 | 5,939 |
| AUFLIA | 15 | 283 | 5 | 0 | 58 |
| UFLIA | 25 | 883 | 3 | 0 | 55 |
| **Total** | **549** | **22,277,998** | **85,974** | **118,836** | **66,063** |

The other **22,093,099 nodes (99.17%)** have no local obligation. This
is not a full-proof success rate: one pending step blocks certification.
The largest valid DAG is `QF_UF_085`, with **1,095,360 nodes**.

The exercised checked fragment includes asserted-input membership,
congruence, equality/path transitivity, symmetry, modus ponens, unit
resolution, hypotheses and lemma discharge, supported Boolean and array
rewrites, commutativity, and checked definition axioms. The valid DAGs
include **60,219 checked `def-axiom` nodes**, **13,962 checked array theory
lemmas**, 6,236,135 congruence nodes, and 7,382,041 unit-resolution nodes.
No `intro-def` or `apply-def` nodes occur in this valid-DAG census; their
implementation is not benchmark evidence of exercise.

### Arithmetic evidence

The native bridge preserves the producer's original parameters, rather
than reconstructing evidence or re-solving obligations:

| Source arithmetic evidence in valid DAGs | Checked | Pending |
|---|---:|---:|
| `arith/farkas` | 85,974 | 570 |
| `arith/bound` | 0 | 65,668 |
| `arith/assign-bounds` | 0 | 43,623 |
| `arith/implied-eq` | 0 | 4,947 |
| `arith/triangle-eq` | 0 | 4,023 |
| Bare `arith` | 0 | 5 |
| **Total** | **85,974** | **118,836** |

Of 86,544 supplied Farkas steps, 99.34% pass the supported check. The
85,974 checked steps occur in **184 derivations, all still `PARTIAL`**.
The 570 pending supplied steps occur in eight QF_LIA inputs. A focused
native diagnostic confirms that **all 570 prepare successfully**, but
their resulting combinations do not satisfy the current refutation
test: this is neither a coefficient-decoding/count failure nor evidence
that the underlying Z3 inference is unsound. Their semantic explanation
and any additional integer-strengthening rule require further analysis.
They remain obligations, never accepted solely because of a Farkas tag.

Among 318 partial derivations, 231 need only rewrites, 83 need rewrites
and arithmetic/theory steps, and four need only theory steps. Missing
bound/equality-propagation evidence and unsupported arithmetic rewrites
remain the principal arithmetic gaps. General integer cuts require
separately checkable evidence, not just a rule-name allowlist.

### Rejection boundaries

| First failing stage | Inputs | Interpretation |
|---|---:|---|
| Expression well-formedness | 125 | Quantified proof-valued/binder expressions outside the ordinary expression fragment |
| Logical declaration validation | 45 | Non-Boolean observational equality: 11 array, 15 integer, 19 real cases |
| `proof-bind` node | 17 | Unsupported proof-binder judgment shape |
| `monotonicity` node | 4 | Congruence step not established by the current kernel |
| `asserted` node | 1 | Asserted conclusion not established as an original input |
| **Total** | **192** | |

The 45 observational-equality cases preserve the actual `~` operand sorts.
The kernel's observation relation is Boolean-only; native marshaling does
not relabel these as equality or manufacture a Boolean proxy.

The eight accepted quantified-logic inputs are still `AUFLIA_031`,
`AUFLIA_049`, `AUFLIA_053`, `UFLIA_034`, `UFLIA_076`, `UFLIA_086`,
`UFLIA_088`, and `UFLIA_094`. They do not demonstrate general
quantifier-instantiation, proof-binder, or Skolemization support.

## Performance

### Native latency

Values are **median / nearest-rank p95 milliseconds**, with population
size in parentheses. End-to-end includes all attempts and censored runs.
Solve/marshal include all 741 completed documents, including rejections;
check includes only `ACCEPT`/`PARTIAL`, avoiding fast-rejection bias.
These are completion-conditioned phase distributions, not estimates of
unobserved work in resource-limited cases.

| Logic | End-to-end, all attempts | Solve, completed | Marshal, completed | Check, valid DAGs |
|---|---:|---:|---:|---:|
| QF_UF | 2965.6 / 33356.5 (100) | 205.9 / 2761.0 (92) | 633.1 / 8428.4 (92) | 1006.2 / 19387.7 (92) |
| QF_AX | 533.2 / 60010.2 (100) | 21.5 / 42.6 (90) | 23.0 / 106.6 (90) | 387.0 / 10617.5 (85) |
| QF_LIA | 683.6 / 60019.3 (100) | 33.7 / 2582.8 (69) | 12.6 / 382.6 (69) | 6.2 / 1722.5 (67) |
| QF_LRA | 366.6 / 11876.6 (100) | 18.1 / 8228.8 (65) | 4.7 / 1146.2 (65) | 0.2 / 1726.7 (46) |
| QF_IDL | 10253.2 / 60022.7 (100) | 333.3 / 7759.4 (50) | 397.9 / 8613.2 (50) | 1182.3 / 39863.2 (35) |
| QF_UFLIA | 74.4 / 1944.8 (100) | 20.0 / 177.6 (98) | 9.4 / 205.0 (98) | 4.0 / 742.4 (97) |
| QF_AUFLIA | 101.3 / 60009.9 (100) | 20.4 / 58.9 (93) | 8.0 / 75.2 (93) | 16.8 / 6773.5 (87) |
| AUFLIA | 69.1 / 10837.8 (100) | 23.1 / 206.2 (92) | 2.8 / 10.5 (92) | 0.1 / 0.2 (15) |
| UFLIA | 107.2 / 10331.5 (100) | 38.4 / 376.4 (92) | 14.6 / 65.5 (92) | 0.3 / 0.7 (25) |
| **All** | **206.3 / 32948.7 (900)** | **28.3 / 1832.5 (741)** | **15.7 / 3038.2 (741)** | **34.8 / 11846.2 (549)** |

Solve time starts after reading the input and includes parsing, asserting,
solving, and proof retrieval. Marshal time covers direct AST/proof
conversion. Check time covers typed document validation and inference
checking. Process startup, file reading, reporting, teardown, and the
driver's polling overhead are only in end-to-end time.

| Population/cost | Seconds |
|---|---:|
| Native batch elapsed, eight workers | 672.70 |
| All-attempt summed process wall time | 5,329.78 |
| All-attempt summed child CPU time | 5,299.17 |
| Valid-DAG summed solve time | 220.00 |
| Valid-DAG summed marshal time | 266.62 |
| Valid-DAG summed check time | 1,094.74 |

Summed process times overlap; they are not batch elapsed time. Hashing,
source snapshots, subsequent database logging, probes, and diagnostics are
excluded from the timed batch. Among completed valid phases, checking
accounts for about 69.2% of summed phase time. Identity caches prevent
duplicate marshaled allocations, but do not make structural equality,
definition expansion, or inference checking constant-time.

### Separate standalone solver

The matching-version proof-disabled CLI solves **796/900** within its
10-second solver limit; 104 time out, with no SAT, other unknown, or error
outcomes. The batch takes **171.28 seconds** with eight workers.

| Logic | UNSAT / timeout | Completed median / p95 ms |
|---|---:|---:|
| QF_UF | 100 / 0 | 106.4 / 782.6 |
| QF_AX | 100 / 0 | 55.6 / 97.0 |
| QF_LIA | 87 / 13 | 146.0 / 4502.4 |
| QF_LRA | 64 / 36 | 50.0 / 5204.4 |
| QF_IDL | 63 / 37 | 137.1 / 5733.5 |
| QF_UFLIA | 99 / 1 | 50.3 / 539.1 |
| QF_AUFLIA | 100 / 0 | 48.4 / 74.8 |
| AUFLIA | 91 / 9 | 50.1 / 166.4 |
| UFLIA | 92 / 8 | 64.1 / 413.5 |
| **All** | **796 / 104** | **56.3 / 1569.6** |

For completed CLI runs, Z3-reported `max-memory` has median/max
**18.42 / 539.60 MB**, not host RSS. `conflicts` has median/max
**32 / 164,700** over the 599 runs reporting that counter.
Separate `sat-conflicts` are not merged into it. Other reporting subsets
include 127 runs with `quant-instantiations` (median 58, maximum 100,266),
five with `arith-gomory-cuts` (8 / 160), and 34 with `arith-pivots`
(624 / 285,182). These counters describe solver work, not proof-checker
coverage of the corresponding inference.

The benchmark skill also ran the fixed index-0 input of each logic three
times sequentially after the timed batches: **27 additional UNSAT runs**
with statistics logged separately. Their median CLI times were QF_UF
336 ms, QF_AX 20, QF_LIA 26, QF_LRA 4,368, QF_IDL 58, QF_UFLIA 517,
QF_AUFLIA 20, AUFLIA 31, and UFLIA 70. These nine repeated cases do not
provide confidence intervals for the 900-input distributions.

Per-child `wait4` CPU/high-water records are retained. Native high-water
RSS comparisons are not reported as precise heap measurements: launch
records can include an inherited-memory floor, and address-space limits
are not RSS limits. Timed-out runs have no recovered completed phase
statistics.

## Comparison with the preceding Python/JSON run

The reference is the refreshed 2026-10-15 run archived at
`C:\smtlib-benchmarks\proof_check_crosscut_20261015_2123\full`.
Its full report is retained in the new run's `preceding_report.md`.

| Metric | Previous Python/JSON | Native-only |
|---|---:|---:|
| ACCEPT / PARTIAL / REJECT | 193 / 322 / 127 | 231 / 318 / 192 |
| Completed valid DAGs / nodes | 515 / 2,327,425 | 549 / 22,277,998 |
| Checked Farkas steps | 9,968 | 85,974 |
| Pending obligations | 79,689 | 184,899 |
| Workers | 32 | 8 |
| Timed pipeline elapsed seconds | 348.37 | 672.70 |

The much larger census is conditioned on different completed proofs; it
does not establish a new checked rule or a per-node performance regression.
In particular, the 192 native rejections include 65 inputs not previously
rejected, while all 127 previous rejections remain rejected.

Of the previous 193 accepts, **179 remain accepted**, five become partial,
five reject on **non-Boolean array observational equality**, and four hit
the whole-process watchdog. The five new partials are `QF_UF_001`,
`QF_UF_021`, `QF_IDL_044`, and `QF_LRA_037` (rewrites), plus
`QF_UFLIA_052` (theory steps). The five newly rejected former accepts are
`QF_AX_087`, `QF_AX_091`, `QF_AX_095`, `QF_AUFLIA_045`, and
`QF_AUFLIA_046`.

The **52 newly accepted inputs** comprise 36 former export timeouts,
11 former checking timeouts, and five former partials. All seven former
exporter expression-recursion failures now reach `PARTIAL`; none becomes
fully certified. This is concrete evidence that the direct worklist path
can traverse those inputs, not that their remaining inference gaps are fixed.

For the 179 inputs accepted by both runs, median summed old phase time was
2.450 s versus native end-to-end 0.222 s. This is a descriptive matched-input
comparison only: the old producer was Python Z3 **5.1**, its export/check
watchdogs were separate, its checker limit was 10 seconds, it had 32
workers, and it did not use the new address-space cap. Producer version,
proof shape, platform/load, and censoring all confound a causal speedup
claim. Removing JSON demonstrably removes that transport stage, but does
not eliminate marshaling or large-proof checking costs.

## Trust boundary and scope

`ACCEPT` means that the executable checker reaches a closed false root,
checks every DAG entry, and finds no pending leaves. Assertions must match
the original inputs obtained from the linked parser. Definition freshness
is checked against unused as well as used inputs. Unsupported relations,
binders, or evidence are not silently converted into checked facts.

Foreign AST views, native ownership, Z3 parsing, OCaml/C bindings, F*
extraction, the compiler, and the handwritten runtime remain trust
boundaries. There is no theorem proving that the foreign API implements
the checker AST's semantics.

The existing formal-foundation limitation also remains: the global Boolean
and arithmetic semantic contracts quantify over untyped environments and
are not inhabitable as literally stated. Well-sorted valuations and an
inhabited interpretation bridge are still needed for an unconditional
end-to-end SMT-LIB soundness theorem. These measurements establish
**executable certificate coverage**, not that missing theorem. See
[the arithmetic report](ARITHMETIC_CERTIFICATE_REPORT.md) and
[the native executable report](OCAML_CHECKER_REPORT.md).

## Artifacts and reproduction

All artifacts are retained outside the repository at:

```text
C:\smtlib-benchmarks\proof_check_native_20261016
```

`full` contains the frozen native executable, driver, 900-input CSV
manifest, 900 raw stdout/stderr pairs, outcomes, metadata, the preceding
report, and **900 records in `z3agent.db`**. `full\audit` contains the
untimed diagnostic binary/source, all 741 audits, and the recorded retry.
`full\farkas_diagnostics` contains the focused 570-step diagnostic.
`solver` independently contains the matching CLI, driver, all 900 outcomes
and statistics, and another **900 database records**. `probes` contains
the 27 repeated skill invocations and their database. `memory_supplement`
records the two larger-cap reruns without modifying the primary data.

`fstar_sources.tar`, `extracted_native.tar`, and build logs freeze the
committed F* development and generated native closure. `comparison.csv`
records all 900 old/new outcome pairs; `summary_evidence.txt` records
validated aggregates. No proof JSON was generated or consumed by this run.

| Artifact | SHA-256 |
|---|---|
| Native executable | `1ebb734e4204f11ae957bd813156fe9d3d4787c124fa5278544f8390441d4a5e` |
| Matching standalone solver | `30dc45ad0a5ab3f60dc4fe4b4d712ae53297bcc9d260c5d8c89f8b759d59b053` |
| Timed driver | `fb72f048330527265bae3f34e50d3ae4dc1d58dc0acfc8594e9493a71718ddb9` |
| `full\manifest.csv` | `8c5b7ae8f82ede1313079965b260b4cf26ed159951349e0aee31730023aa66a5` |
| `full\outcomes.csv` | `607810b1b99c31234117a11e413a637196e18aab8ac4973c885a865e467466b6` |
| `solver\outcomes.csv` | `f48c6e0b4293fddb0c69e48f96e8246b4bbd6e98a055359ee984098e99c2afbc` |
| Reconciled audit outcomes | `1cdff68cb5d76ff56913b01e34f52bee84dcf0313fdfd49773a09badbcb9ae9f` |

With WSL Python 3, the same original corpus/manifests, and the frozen
executable, the primary run can be reproduced using its archived driver:

```powershell
wsl -e python3 `
  /mnt/c/smtlib-benchmarks/proof_check_native_20261016/full/run_crosscut.py `
  --manifest /mnt/c/smtlib-benchmarks/proof_check_20261014_1034/manifest.json `
  --manifest /mnt/c/smtlib-benchmarks/proof_check_seven_20261014/manifest.json `
  --executable /mnt/c/smtlib-benchmarks/proof_check_native_20261016/full/checker `
  --output /mnt/c/smtlib-benchmarks/proof_check_native_reproduction
```

The output destination must not already exist. The archived driver imports
the repository's benchmark database helper/schema after timing, so the
checkout is also required for database logging. Use the archived solver
driver with `--mode solver` and its frozen `z3` for the standalone batch;
run batches sequentially. Source archives and script hashes establish
provenance, not deterministic timing or an uncensored coverage estimate.
