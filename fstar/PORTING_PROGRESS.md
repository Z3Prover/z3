# Proof-checker pending dashboard

Updated: **2026-11-24T17:07:30-08:00** (America/Los_Angeles).

`PENDING` is the weighted total of unresolved obligations from diagnostic-bearing
proofs. Missing diagnostics, timeout tails, and unobserved evidence are `N/M`,
not zero. Dataset-wide PENDING totals cover only the proofs with completed
diagnostics.

## Native sorted-core candidate (not comparable to Definition mode)

Verified candidate built from source HEAD `08b118df3e51440ec8394cceaf98c31f2c462f7f`
plus F* source diff SHA-256
`1f44d355add220803ae0d9d455a3fd84edabe094286a13e8a79ff867efb8149c`;
checker SHA-256
`417f0605883481a49d08edae18f364afb654e72ccea9b37072fe7f550dc6f843`,
mode `--sorted-core`, F* 2026.10.25, OCaml 5.3.0, Z3 5.4.2 (build hash
`08b118df3e51440ec8394cceaf98c31f2c462f7f`). The strict production build
verified all 185 modules and linked the native checker; focused
`Z3SortedProofTests.fst` verification passed. Cohorts ran serially with
10,000-ms solver queries, 60-s per-case caps, 4,096-MiB per case, and
3,600-s per-cohort budgets. Artifacts, including the checker, are retained
under `files\current-definition-axiom-search-02`.

| Dataset | Outcomes (all statuses) | Diagnostic replays | Diagnostic errors / replay mismatches | Weighted PENDING | Aggregate case time / median per case |
| --- | --- | ---: | ---: | ---: | ---: |
| smtlib-sample | 101 ACCEPT, 86 PARTIAL, 0 REJECT, 0 SAT, 21 solver UNKNOWN, 17 TIMEOUT, 0 ERROR, 0 CRASH, 0 PROTOCOL_ERROR, 0 NOT_RUN (225) | 86 / 225 | 0 / 0 | 3,979 | 1,969.7s / 0.579s |
| smtlib-extended | 73 ACCEPT, 130 PARTIAL, 0 REJECT, 0 SAT, 74 solver UNKNOWN, 8 TIMEOUT, 0 ERROR, 0 CRASH, 0 PROTOCOL_ERROR, 0 NOT_RUN (285) | 130 / 285 | 0 / 0 | 28,427 | 1,681.8s / 0.580s |

Every PARTIAL case has a completed diagnostic replay (86/86 and 130/130),
with zero diagnostic errors or replay mismatches. UNKNOWN and TIMEOUT cases
have no proof diagnostics and are not counted as zero-PENDING. Input manifest
SHA-256 values are sample
`72cba03d2816fa47b8bb65d2dc03105b0781cb1243813846bbed1a789666cc44` and
extended `6f6ad04db40a0f49733329ce056e5d599328a4468133f987a56c2172ac08cb34`.
These native `--sorted-core` results are not comparable to the retained
`--definition-replay` captures below; they do not establish matched-proof
burn-down or Legacy parity. An initial invocation with unsupported
`--definition-replay` was preserved separately under
`files\current-definition-axiom-search-01` and is excluded from these counts.

## Retained Definition-mode SMT-LIB capture

Candidate built from source HEAD `1f910bbc6a19f185ec401394f33ff3eb684ace06`
plus F* source diff SHA-256
`a1af51d1468940d9287ae75c7a49b222cacb39a9a4488baeb76160297c928661`;
checker SHA-256
`b082bd428205357e7830445b624dee744679be80345f77fc26f0feaf74092c78`,
mode `--definition-replay`, OCaml 5.3.0, Z3 5.4.2, and static linkage
(`libz3ml.a` SHA-256
`62ac403890a049d879e11422efbff9452cd7b849f6dc48a666e22405a354458c`,
`libz3.a` SHA-256
`2d63d27f2fa75759813154430b3eeba6441abcaa003ce6d92307201eba2cc0d7`).
This source includes bounded Boolean search and recognizes the validated,
premise-free ITE branch axiom when represented by `DefinitionIntroduction`.
Both pinned cohorts ran serially with 10,000-ms solver queries, a 60-s
per-case cap, a 4,096-MiB limit, and a 3,600-s cohort budget. The retained
checker was rerun on 2026-11-22 at 17:15 Pacific with the same binary and
pinned manifests. Outcomes, diagnostic counts, weighted PENDING, and per-rule
totals reproduced exactly; all PARTIAL cases had diagnostics with zero errors
or replay mismatches. Latest aggregate case wall time / median per case was
2,075.3s / 0.686s for sample and 1,776.5s / 0.636s for extended, versus
2,013.1s / 0.580s and 1,739.6s / 0.580s in the preceding repeat. This is
repeatability data, not an improvement or matched-proof burn-down:
proof-document hashes were not retained. The latest repeat artifacts are under
`files\current-retained-definition-cycle-03`; cycle 02 remains preserved.

| Dataset | Outcomes (all statuses) | Diagnostic replays | Diagnostic errors / replay mismatches | Weighted PENDING | Aggregate case time / median per case |
| --- | --- | ---: | ---: | ---: | ---: |
| smtlib-sample | 110 ACCEPT, 77 PARTIAL, 0 REJECT, 0 SAT, 21 solver UNKNOWN, 17 TIMEOUT, 0 ERROR, 0 CRASH, 0 PROTOCOL_ERROR, 0 NOT_RUN (225) | 77 / 225 | 0 / 0 | 3,836 | 2,075.3s / 0.686s |
| smtlib-extended | 78 ACCEPT, 126 PARTIAL, 0 REJECT, 0 SAT, 74 solver UNKNOWN, 7 TIMEOUT, 0 ERROR, 0 CRASH, 0 PROTOCOL_ERROR, 0 NOT_RUN (285) | 126 / 285 | 0 / 0 | 30,907 | 1,776.5s / 0.636s |
| fstar-build | **No current-source capture**; last measured checker `2671dc150931` | 7,190 / 7,190 completed diagnostics | 0 / N/M | 430 (last known) | N/M |

Every PARTIAL case has a completed proof diagnostic (77/77 and 126/126);
diagnostic error/mismatch counts apply only to those replays. ACCEPT,
solver-UNKNOWN, and TIMEOUT cases have no proof diagnostic; their outcome
counts above are explicit and are not treated as zero-PENDING evidence.

| Rule | fstar-build, last known | smtlib-sample, Definition | smtlib-extended, Definition | smtlib-sample, Definition+Array | smtlib-sample, sorted-core candidate | smtlib-extended, sorted-core candidate |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `arith/bound` | N/M | 0 | 11 | 0 | 0 | 11 |
| `arith/farkas` | 3 | 0 | 0 | 0 | 0 | 0 |
| `arith/lp-integer-lattice` | N/M | 0 | 0 | 0 | 0 | 0 |
| `arith/lp-gomory` | N/M | 0 | 0 | 0 | 0 | 0 |
| `arith/lp-monomial-interval` | 1 | 0 | 26 | 0 | 0 | 26 |
| `arith/lp-monomial-substitute` | N/M | 0 | 0 | 0 | 0 | 0 |
| `assumed:nlsat` | 139 | 0 | 102 | 0 | 0 | 102 |
| `apply-def` | 0 | 0 | 0 | 0 | 0 | 0 |
| `def-axiom` | 0 | 3 | 89 | 1 | 4 | 89 |
| `der` | 0 | 6 | 0 | 6 | 6 | 0 |
| `intro-def` | 0 | 162 | 103 | 113 | 307 | 126 |
| `nnf-neg` | 10 | 0 | 0 | 0 | 0 | 0 |
| `nnf-pos` | 0 | 0 | 0 | 0 | 0 | 0 |
| `quant-intro` | 23 | 42 | 81 | 26 | 52 | 81 |
| `rewrite` | 8 | 124 | 24,342 | 58 | 111 | 21,839 |
| `sk` | 10 | 0 | 0 | 0 | 0 | 0 |
| `th-lemma` | 236 | 3,499 | 6,153 | 140 | 3,499 | 6,153 |

Correction recorded 2026-11-21 22:19 Pacific: the extended diagnostics aggregate
to 11 `arith/bound` and 0 `arith/farkas`; the earlier table duplicated the
bound count under Farkas. The weighted PENDING total remains 30,907. This is an
attribution correction only, not a measured improvement or burn-down.

The fstar-build column is a historical baseline, not a current-source result;
its original run observed 407/583 cases, completed 384, timed out on 23, and
left 176 `NOT_RUN`. The current SMT-LIB input-manifest SHA-256 values are
sample `72cba03d2816fa47b8bb65d2dc03105b0781cb1243813846bbed1a789666cc44`
and extended
`6f6ad04db40a0f49733329ce056e5d599328a4468133f987a56c2172ac08cb34`. The
original checker, manifest, per-case results, and diagnostics are under
`files\current-ite-intro-cohorts-01`; the repeated run's checker, reports,
per-case results, and diagnostics are under
`files\current-retained-definition-cycle-02`.

<!-- BEGIN PERIODIC SMTLIB -->
### Six-hour SMT-LIB measurements (Definition)

Updated `2026-11-24T17:07:30-08:00`; cycle `periodic-smtlib-20261124T235942Z` **completed**; checker SHA-256 `6eb16f0b187e27a5d4a5298f7c848869899edf7feb15895ab525325cb5099fbb`, OCaml 5.3.0, static Z3 linkage. Schedule **#5**, every six hours.
Fixed hashed inputs; serial native cases; 10,000-ms queries / 60-s cases / 4,096-MiB / 3,600-s budget per cohort. A 30-s quiet pause precedes each cohort. Finite fields are excluded; QF_BV is excluded from extended as in the workflow.

| Cohort | State | ACCEPT | PARTIAL | Solver UNKNOWN | TIMEOUT | SAT | REJECT | Crash/error | NOT_RUN |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| smtlib-sample | COMPLETED | 83 | 103 | 20 | 19 | 0 | 0 | 0 | 0 |
| smtlib-extended | COMPLETED | 74 | 135 | 69 | 7 | 0 | 0 | 0 | 0 |

NOT_RUN counts cases with no observed outcome; solver UNKNOWN is not checker success. Both cohorts have NOT_RUN=0. Historical nine-case guards remain separate.
Case wall time / median: sample 2,070.827s / 0.498s; extended 1,751.094s / 0.547s. Pins, per-case timestamps/logs, per-logic CSV/JSON and collector: session `files\periodic-smtlib-20261124T235942Z`.

| Cohort | Diagnostic replays | Weighted PENDING | Missing diagnostics | TIMEOUT | NOT_RUN |
| --- | ---: | ---: | ---: | ---: | ---: |
| smtlib-sample | 186 / 225 | 5,907 | 39 / 225 | 19 / 225 | 0 / 225 |
| smtlib-extended | 209 / 285 | 31,516 | 76 / 285 | 7 / 285 | 0 / 285 |

| Rule | smtlib-sample | smtlib-extended |
| --- | ---: | ---: |
| `quant-intro` | 42 | 83 |
| `rewrite` | 1,866 | 24,704 |
| `der` | 7 | 0 |
| `def-axiom` | 3 | 89 |
| `th-lemma` | 3,514 | 6,267 |
| `intro-def` | 272 | 147 |
| `apply-def` | 203 | 0 |
| `arith/farkas` | 0 | 33 |
| `arith/lp-monomial-interval` | 0 | 46 |
| `assumed:nlsat` | 0 | 146 |
| `arith/lp-monomial-substitute` | 0 | 1 |
| **Total** | **5,907** | **31,516** |

PENDING covers completed diagnostic-bearing proofs only; 0 means no PENDING in the 186 / 209 checked replays. Missing diagnostics equal solver UNKNOWN plus TIMEOUT here (sample 20+19; extended 69+7); these cases are N/M, not zero-PENDING. This cycle reproduced the preceding capture's outcome and per-rule PENDING counts, but retained no proof-document hashes or paired Legacy control; it is repeatability data, not matched-proof burn-down or parity evidence.

<details><summary>Per-logic outcomes and input pins</summary>

| Cohort / logic | ACCEPT | PARTIAL | UNKNOWN | TIMEOUT | SAT | REJECT | Crash/error | NOT_RUN |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| smtlib-sample / AUFLIA | 13 | 11 | 1 | 0 | 0 | 0 | 0 | 0 |
| smtlib-sample / QF_AUFLIA | 8 | 14 | 0 | 3 | 0 | 0 | 0 | 0 |
| smtlib-sample / QF_AX | 1 | 22 | 0 | 2 | 0 | 0 | 0 | 0 |
| smtlib-sample / QF_IDL | 11 | 5 | 2 | 7 | 0 | 0 | 0 | 0 |
| smtlib-sample / QF_LIA | 12 | 6 | 5 | 2 | 0 | 0 | 0 | 0 |
| smtlib-sample / QF_LRA | 5 | 11 | 8 | 1 | 0 | 0 | 0 | 0 |
| smtlib-sample / QF_UF | 22 | 3 | 0 | 0 | 0 | 0 | 0 | 0 |
| smtlib-sample / QF_UFLIA | 2 | 22 | 1 | 0 | 0 | 0 | 0 | 0 |
| smtlib-sample / UFLIA | 9 | 9 | 3 | 4 | 0 | 0 | 0 | 0 |
| smtlib-extended / QF_ABV | 0 | 21 | 3 | 1 | 0 | 0 | 0 | 0 |
| smtlib-extended / QF_AUFBV | 0 | 13 | 10 | 2 | 0 | 0 | 0 | 0 |
| smtlib-extended / QF_DT | 11 | 0 | 13 | 1 | 0 | 0 | 0 | 0 |
| smtlib-extended / QF_NIA | 0 | 17 | 8 | 0 | 0 | 0 | 0 | 0 |
| smtlib-extended / QF_NRA | 9 | 13 | 2 | 1 | 0 | 0 | 0 | 0 |
| smtlib-extended / QF_UFBV | 0 | 22 | 2 | 1 | 0 | 0 | 0 | 0 |
| smtlib-extended / QF_UFDT | 0 | 0 | 25 | 0 | 0 | 0 | 0 | 0 |
| smtlib-extended / QF_UFLRA | 8 | 16 | 0 | 1 | 0 | 0 | 0 | 0 |
| smtlib-extended / UF | 14 | 9 | 2 | 0 | 0 | 0 | 0 | 0 |
| smtlib-extended / UFDT | 11 | 10 | 4 | 0 | 0 | 0 | 0 | 0 |
| smtlib-extended / UFDTLIA | 11 | 14 | 0 | 0 | 0 | 0 | 0 | 0 |
| smtlib-extended / UFLRA | 10 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

smtlib-sample: seed `independent-checker-b09a2011`; manifest SHA-256 `72cba03d2816fa47b8bb65d2dc03105b0781cb1243813846bbed1a789666cc44`.

smtlib-extended: seed `42`; manifest SHA-256 `6f6ad04db40a0f49733329ce056e5d599328a4468133f987a56c2172ac08cb34`.

</details>
<!-- END PERIODIC SMTLIB -->

## QF_LIA rewrite and Farkas diagnosis (focused sample measured)

In the retained Definition cycle, QF_LIA has 12 ACCEPT and 6 PARTIAL. Five
PARTIAL inputs have only 26 pending `rewrite` obligations, all of the form
integer equality rewritten as a conjunction of matching `<=` and `>=`
comparisons. A narrowly guarded, premise-free checker rule for this identity
was added to `Z3SortedProof`, with positive and negative regression controls.
`Z3SortedProof.fst` was checked as a root with stale-cache diagnostics 241/247
silenced, refreshing its checked artifact. `Z3SortedProofTests.fst` then passed
with strict `--warn_error '@1..999'` and installed Z3 5.4.2; all VCs were
discharged. This is focused strict module verification, not a full production
closure.

The current checker build (SHA-256
`38b225fc74b67928260aa6dd9645003e7af9f10c257b55cfa712f95b598ab5da`) was
measured on the same 25 pinned QF_LIA inputs in default Legacy and
`--sorted-core` modes. All input hashes matched; manifest SHA-256 is
`4ad6a2e5efd3d1893cf50325045685102e0aa2d2508f55465cf675176ebb1fc6`
(source-manifest SHA-256
`72cba03d2816fa47b8bb65d2dc03105b0781cb1243813846bbed1a789666cc44`).

| Mode | ACCEPT | PARTIAL | Solver UNKNOWN | TIMEOUT | Other |
| --- | ---: | ---: | ---: | ---: | ---: |
| Legacy | 19 | 0 | 5 | 1 | 0 |
| SortedProof | 17 | 2 | 5 | 1 | 0 |

Both runs had no REJECT, SAT, checker error, crash, protocol error, or
NOT_RUN. The two SortedProof PARTIAL proofs are
`ring_2exp4_3vars_1ite_unsat.smt2` (4 PENDING) and
`ring_2exp6_9vars_3ite_unsat.smt2` (30 PENDING); all 34 obligations are
`intro-def`, with zero diagnostic errors or replay mismatches. Thus this
input-matched sample still trails Legacy by two ACCEPTs; it provides no
evidence that the equality-to-bounds rewrite closes these cases. Proof
documents were not retained, so this is not a proof-hash-matched comparison.
The 25-input sample is separate from the 225-case cohort, whose totals and
PENDING are unchanged. Artifacts are under
`files\qflia-current-legacy-20261124` and
`files\qflia-current-sorted-core-20261124`.

The retained sample has zero `arith/farkas` PENDING. The separately captured
current-source QF_LIA ring proof has 251 Farkas entries and zero Farkas
PENDING; its four PENDING obligations are all `intro-def`. The 20 extended
`arith/farkas` PENDING entries are in three QF_NIA inputs and one QF_NRA input,
with fingerprints containing multiplication. In `theory_lra.cpp`,
`set_proof_params` attempts to reconstruct and check the LP derivation, then
linearizes and locally validates Farkas coefficients; it emits an
`unsupported` payload when that path cannot be checked, and bound propagation
can export a replayable LP derivation. This source evidence and the QF_LIA
controls do not demonstrate flaky QF_LIA Farkas generation. The extended
nonlinear cases still need their exact proof documents before attributing
their PENDING to producer output versus checker coverage.

The consumer path is also certificate-based: `Z3Native_view_proof` extracts
Farkas parameters from `th-lemma` nodes, `Z3NativeProof.native_rule` maps
those supplied weights to `ArithmeticFarkas`, and
`Z3LinearArithmeticAst.check` replays them against the premises and negated
conclusion literals, including integer strict-bound rounding. It does not
search for weights. If the producer marks a node `unsupported`, the decoder
leaves it as `Unverified "th-lemma"`; generic checked fragments may then
accept it, otherwise it remains PENDING. The separate LP-certificate route
encodes replayable linear, integer-tightening, lattice, Gomory, and monomial
steps. Without the four extended proof documents, the observed PENDING cannot
distinguish absent/unsupported producer evidence from a mismatch in the exact
certificate or nonlinear evidence outside the fragment. No QF_LIA producer
defect is demonstrated.

## Current PR-head sample: Definition+Array route

The same retained checker executable SHA-256
`b082bd428205357e7830445b624dee744679be80345f77fc26f0feaf74092c78`
was rerun with `--definition-array-replay` over the same 225 input paths and
manifest SHA-256
`72cba03d2816fa47b8bb65d2dc03105b0781cb1243813846bbed1a789666cc44`.
The run verified all input hashes. It produced 142 ACCEPT, 42 PARTIAL, 21
solver UNKNOWN, and 20 TIMEOUT, with no REJECT, SAT, ERROR, CRASH,
PROTOCOL_ERROR, or NOT_RUN cases. All 42 PARTIAL cases had matching
diagnostics with zero errors and replay mismatches; their weighted PENDING
total is 344: 140 `th-lemma`, 113 `intro-def`, 58 `rewrite`, 26
`quant-intro`, 6 `der`, and 1 `def-axiom`. Other outcomes have no proof
diagnostic and are not counted as zero-PENDING.

Path-matched outcomes versus Definition-only were 110 ACCEPT→ACCEPT, 42
PARTIAL→PARTIAL, 32 PARTIAL→ACCEPT, 3 PARTIAL→TIMEOUT, 21
UNKNOWN→UNKNOWN, and 17 TIMEOUT→TIMEOUT. Thus no prior ACCEPT regressed, but
three PARTIAL cases timed out. Aggregate case wall time / median was
2,250.4s / 0.779s, versus 2,016.1s / 0.579s for Definition-only; the combined
route was slower. This is an input-matched route comparison, **not**
matched-proof burn-down (proof-document hashes were not retained) or Legacy
parity. The matched 11-proof Legacy control above remains 3/11 ACCEPT versus
Legacy 11/11. Results and diagnostics are retained under
`files\current-ite-array-prhead-01`.

The retained pre-patch Definition capture recorded 83/225 sample ACCEPT and
74/285 extended ACCEPT, with 5,907 sample PENDING. Its extended PENDING is
31,501 in the saved run state/per-rule totals, while an older dashboard says
31,516; that discrepancy remains unresolved. The current source records 27
more sample ACCEPT and 4 more extended ACCEPT than that capture; its PENDING
totals are 3,836 sample and 30,907 extended. These are cohort observations,
**not matched-proof burn-down** or a Legacy-parity result. Against the previous
Boolean-search run, sample outcomes and PENDING are unchanged. Extended has
one `QF_UFBV` case transition from TIMEOUT to PARTIAL, adding 2,503 observed
PENDING; that run used eight workers while this run was serial, so no causal
improvement is inferred. Proof-document hashes were not retained. The earlier
Definition+Array capture is a different checker mode and is not a direct
comparison. A prior fixed-proof control accepted 1/11 with the sort-indexed
checker versus Legacy's 11/11; the completed current-source control below uses
new frozen proof documents, so it is not a burn-down comparison.

## Matched current-source sample control (separate from cohort totals)

Eleven pinned sample inputs selected for conditional-definition/apply-def
controls were hash-verified against the current sample manifest. Each was
captured once, then replayed by the independent `check_definition_diagnosed`
route and Legacy on the same frozen document. All 11 schema records had zero
datatype cases, so Legacy used `Z3ProofDocument`. The independent checker
accepted 3/11 and returned PARTIAL on 8/11 (811 total PENDING); Legacy accepted
11/11. Current PENDING was 681 `th-lemma`, 93 `intro-def`, 27 `rewrite`, 9
`quantifier-intro`, and 1 `def-axiom`; `apply-def` PENDING was 0. Thus
apply-def was not the unresolved-rule blocker in this control set. Single-pass
paired replay medians were 6.038s current versus 0.573s Legacy; one timing per
proof is indicative only, not a stable performance estimate. These 11 controls
are not cohort totals and do not establish parity or burn-down. Hashes, logs,
and build provenance are retained under
`files\conditional-current-source-control-04e`.

The retained fixed-control logs localize its 681 `th-lemma` PENDING to proofs
10, 20, 37, and 40, but do not retain per-obligation fingerprints. Legacy's
`Z3UnifiedProof.checked_theory_lemma` tries `array_lemma`, `TN.consequence`,
LP bound/equality checks, and inferred split rules; the sorted route uses its
own schema-indexed fragments. `TN.lemma_consequence` requires the broader
`TN.normalization_model`, so this is not a sound drop-in port. The 681
obligations are a target for further per-entry tracing, not yet attributed to
a specific Legacy rule.

### Sorted array-kernel control (not a native CLI or cohort result)

The same 11 hash-verified frozen documents were checked directly with
`Z3SortedProof.check_document_array`. Source HEAD is `0484078c4`;
`Z3SortedProof.fst` SHA-256 is
`663e1b1c832c20771fc62309fb62c286e03b81e0d4a24581d960807baa02ef9c`;
the rebuilt checker SHA-256 is
`1ef727da50c13150257ff7a7116d38d3c3de9d0b143fd08055670d19fe10c383`.
The array route accepted 4/11 (proofs 10, 20, 37, 49) and returned PARTIAL
on 7/11, with 151 aggregate PENDING; the matched ordinary sorted-core
control accepted 1/11 and had 832 PENDING. Legacy accepted 11/11. This is a
fixed-proof kernel experiment, not a native CLI/corpus measurement; the
array route has no per-rule diagnostics, so its per-rule PENDING is N/M.
The same standard diagnostics show no pending `arith/farkas` obligations in
these controls, including the selected QF_LIA cases; they do not evidence a
Farkas-producer defect.

The production sorted path uses `check_document_epsilon`. On the same frozen
documents it accepted 1/11 and returned PARTIAL on 10/11 (831 PENDING:
681 `th-lemma`, 113 `intro-def`, 27 `rewrite`, 10 other; `apply-def`=0).
The direct `check_document` baseline above has 832 PENDING; the one-obligation
difference is from epsilon elaboration. The epsilon-only replay took 94.14s
versus Legacy's 21.787s, slower on 9/11 (4.32x aggregate). Its helper binary
SHA-256 is
`ecbf59ddd07325a0c067d71c1e4103dc7cd7900f0d9174027c88d900244ed401`.
Per-proof outputs, timings, and verified proof hashes are under
`files\conditional-current-sorted-epsilon-control-01`.

Single-pass array-route time was 93.40s total versus 21.787s for Legacy on
these same documents; the array route was slower on 8/11. The guarded fast
path for supported array lemmas preserved all outcomes and changed the
one-pass total from 94.47s to 93.40s (1.1%, not a conclusive performance
gain). Per-proof verdicts, timings, and hashes are retained under
`files\conditional-current-sorted-replay-02`; no parity or performance claim
is made.

### Current-source Definition+Array matched replay (not promoted)

The Real-gated conditional rewrite path was verified and replayed through the
independent `check_definition_array_diagnosed` route on the same 11 frozen
documents from `files\conditional-current-source-control-04e`. All proof
hashes were reverified (ordered proof-set SHA-256
`176f8a87df57df9b3ba18914101ad3d5b9085cc350d4419c15c91117b297e22b`).
Source HEAD is `e6d993a219092ed820a9a984250be7bb81a72294`; the current F*
source diff SHA-256 is
`e971d15c787725702bd8326ccd76e4bffd20540ab71eef2a38ed52f202ef0a4e`.
F* 2026.10.25 strictly verified the 218-module independent-checker
dependency closure; the checker extracted and linked with OCaml 5.3.0 and
Z3 5.4.2. Strict `Z3SortedProofTests.fst` verification passed, including
positive actual-route and invalid-branch controls. Checker SHA-256 is
`73c07133d25e5949bd07428fa64e106b5cc993461f72b1e0a63f3971959e7487`.
The broader `build_independent_checker.py` test sequence stopped later in its
test-only finite-field polynomial extraction because that module's `.checked`
cache was stale; see
`files\real-conditional-independent-build-02.log`.

The candidate accepted 7/11 and returned PARTIAL on 4/11 (108 PENDING: 93
`intro-def`, 5 `rewrite`, 1 `def-axiom`, 9 `quantifier-intro`; `apply-def`
and `arith/farkas` were 0). Against the prior PR-head control, acceptance is
unchanged at 7/11 while rewrite PENDING fell 20→5, reducing total PENDING
123→108. On proof 63, PENDING fell 79→64 (60 `intro-def`, 19→4 `rewrite`).
Legacy accepts 11/11. Candidate aggregate time / median was 181.047s /
11.053s versus 181.016s / 11.101s in the prior single pass—no meaningful
performance change. The retained paired Legacy total is 32.213s, so the
candidate remains about 5.62x slower. This is fixed-proof evidence, not cohort
burn-down or parity; no sample/extended cohort or new Legacy timing was run.
Detailed output is under
`files\real-conditional-independent-matched-11.log`; no Farkas-producer
evidence is added. Cohort outcome counts, diagnostic errors, timeout tails,
and new fstar-build counts remain N/M.

A follow-on candidate hoists the input-expression budget check out of the
per-definition collection loop and reuses collected items while rewriting
entries. Strict `Z3IndependentDefinitionPair.fst` verification passed;
focused document and NNF regression checks discharged their VCs but emitted
stale-cache warnings 241/247 for `Z3SortedProof` and
`Z3IndependentDefinitionPair.fsti`. Full strict closure, extraction, pinned
replay, and timing remain incomplete. The 7/11 and 5.62x results above remain
the last verified matched result; this change is not promoted.

Proof-90 triage attributes 9 of its 14 PENDING obligations to `quant-intro`,
reported as `eq:binder->binder`. Legacy uses `binder_quantifier_step` with
bounded `QR.equivalent`; `Z3BinderKernel` has a narrower exact-body-edge
fragment over asserted/core entries, but its soundness theorem has not been
connected to the sorted model here. The retained diagnostics lack the full
binder-entry graph, so coverage by that fragment is unestablished. No
acceptance or performance change is claimed.

### Current-source binary-distinct replay on frozen proof 69

The current source at HEAD `b9d75b48a` plus F* source diff SHA-256
`348c04b19c72f033b9a16f0b248b4b5ecf256943bed89c4682980d4b8a21b50c`
was strictly verified across the 167-module checker-only closure and linked
with F* 2026.10.25, OCaml 5.3.0, and Z3 5.4.2 (build hash
`b9d75b48a79669c2fe0c98244d8a3dd52a5aa51f`). The production checker SHA-256
is `8cdf3a91a32002bf7f1c9cb27b45fb9796469437e0ff02826b0c0273bea2b978`.
The 18,135-node frozen proof for
`QF_UFLIA/mathsat/EufLaArithmetic/hard/hard18.smt2` was replayed unchanged
(input SHA-256
`d56cb93eb85e7e50aaa3a3831ee4d399c2f944e500a8b32a6913504c61fc59fb`,
proof SHA-256
`903e90305ea4afa3660b4d27fe3f5d0a39ce9d018f6604ad92dae3d337466289`).
The prior candidate was PARTIAL with one pending `rewrite`; binary-only
`distinct(a,b) = not (= a b)` replay now ACCEPTs with zero PENDING, matching
Legacy's ACCEPT on that exact document. Across seven paired runs, median
sorted-checker time was 6,010.433 ms versus 567.671 ms for Legacy (10.59x
slower): this is a one-obligation coverage gain, not a performance gain or
parity claim. Cohort tables above are unchanged and remain historical; no
new fstar-build or SMT-LIB cohort measurement was run. Replay artifacts are
under `files\conditional-current-source-control-04e`; the current replay
harness SHA-256 is
`7169e20add7053fd80e6548ed21256a80bac46bc167996b1f4e5c565502dfa6c`.

## Matched current-source SortedProof/Legacy replay on fixed 11

The same 11 frozen sample proof documents were hash-verified against
`files\conditional-current-sorted-replay-02\proof-hashes.tsv` (ordered
proof-set SHA-256
`176f8a87df57df9b3ba18914101ad3d5b9085cc350d4419c15c91117b297e22b`).
The current checker build (SHA-256
`38b225fc74b67928260aa6dd9645003e7af9f10c257b55cfa712f95b598ab5da`) and
Legacy's indexed `Z3ProofDocument` route were replayed in seven alternating
paired runs per document. All 11 proof hashes matched. SortedProof ACCEPTed
2/11 (proofs 49 and 69), with 9 PARTIAL and 802 PENDING: 681 `th-lemma`,
113 `intro-def`, 7 `rewrite`, and 1 `def-axiom`. Legacy ACCEPTed 11/11.
Summed per-document medians are 92.883s SortedProof versus 21.425s Legacy
(4.34x slower). The candidate remains materially behind Legacy.

The prior direct sorted-core control on this fixed set was 1/11 ACCEPT and
832 PENDING. The current build is +1 ACCEPT and -30 PENDING on the fixed set,
but the source snapshots differ, so this is not causal attribution to a
single change. It is not cohort burn-down or a Farkas-producer finding.
Detailed output is retained at
`files\current-frozen-11-paired7-indexed.log`; the proof set is not cohort
data.

## Exploratory sort-indexed array-kernel route (not root-gated)

Using current source HEAD `823915c2c`, the direct
`Z3SortedProof.check_document_array` route was replayed on the same 11
hash-pinned documents. It returned 5/11 ACCEPT and 6 PARTIAL with 126 total
PENDING (proofs 40: 7, 45: 29, 51: 4, 59: 16, 63: 64, 90: 6), versus that
run's then-current `check_document` baseline of 2/11 ACCEPT and 807 PENDING. The
array-route diagnostic helper reports no per-rule attribution (`N/M`). Its
one-pass summed time was 93.500s; this is not comparable to the default and
Legacy seven-run medians above.

This is exploratory checker-function evidence, not a root-certified CLI
result: `lemma_check_document_array` requires an explicit `array_kernel`, and
this replay did not execute the root-level wrapper that constructs that
kernel. Legacy still accepts 11/11; no parity, cohort burn-down, or
performance claim follows. The default route and dashboard counts remain
unchanged. Proof hashes, helper source, replay output, and candidate binary
hash are retained under
`files\sample-sorted-array-route-current-20261123` (`12ef0ed921770c7d4ef849af6e592455681fbd2c3bda0e95dbcbe6a1912c8a96`).

## Current-source root-gated array-document replay (fixed proof set)

The same 11 hash-pinned documents from
`files\conditional-current-source-control-04e` were replayed through
`Z3IndependentArrayDocument.check`, including the root wrapper, rather than
calling `Z3SortedProof.check_document_array` directly. All 11 proof hashes
were reverified. The current-source 115-module array-document closure passed
strict F* verification; focused `Z3TypedRootTests` and `Z3SortedRootTests`
passed. The replay helper and executable are retained under
`files\array-root-certified-replay-20261124`; their SHA-256 values are
`a8cec893bb68560164698e2bd0974532a5f748d786b7fb84dcda10504ae9329a` and
`da3c299085d6f2fabde68e57a79036aec0c2142006c18c10ff928d7045c71ef7`,
respectively.

The root-gated route ACCEPTed 6/11 (proofs 10, 20, 37, 40, 49, 69) and
returned PARTIAL on 5/11 (proof 45: 29, 51: 4, 59: 16, 63: 64, 90: 5), for
118 total PENDING. It has no per-rule diagnostic breakdown (`N/M`). On these
identical documents the current SortedProof control ACCEPTed 2/11 with 802
PENDING, and Legacy ACCEPTed 11/11; the root-gated route therefore adds four
ACCEPTs and removes 684 PENDING, but remains short of Legacy parity.

Three isolated current runs per proof have 151.973s summed per-proof medians,
versus 35.109s for the existing seven-run alternating Legacy medians on the
same hashes (4.33x slower). This is a fixed-proof coverage improvement, not a
performance gain, production CLI result, cohort burn-down, or Farkas finding.
The cohort tables remain unchanged.

## Current-source guarded definition-array fast path (fixed proof set)

The explicit `--definition-array-replay` route now uses a guarded fast path:
when the document has array declarations and candidates but no definition
entries, it tries the selected array replay directly; otherwise it preserves
the existing definition-array checker. The default route is unchanged.
Strict F* verification passed for the 218-module dependency closure, the
independent checker was extracted and linked, and the focused array-document
and definition-array CLI regressions passed.

On the same hash-pinned documents, proofs 10, 20, 37, and 40 all had array
declarations, no definition entries, and ACCEPTed through both routes. Three
isolated native runs per route produced these per-proof medians:

| Proof | Existing definition-array | Guarded fast path |
| --- | ---: | ---: |
| 10 | 3.455s | 1.269s |
| 20 | 5.974s | 2.765s |
| 37 | 32.283s | 16.095s |
| 40 | 16.384s | 10.303s |

Summed per-proof medians fell from 58.096s to 30.432s (47.6%). Proof 45 had
no array declarations and definition entries; its one-run fallback timings
were 9.810s and 9.742s. A six-proof invocation hit its 600-second wrapper
timeout during proof 90, so no timing is reported for that proof. These are
fixed-proof route measurements, not cohort burn-down, a matched Legacy
comparison, or a change to default checking. Cohort tables remain unchanged.

## Last 10 updates (measurements and corrections)

Times are Pacific. A cohort comparison without identical proof-document hashes
is a coverage observation, not causal attribution or burn-down.

| Time | Change / measurement | Measured effect |
| --- | --- | --- |
| Nov 24 17:07:30 | Complete pinned Schedule #5 Definition cohorts with checker SHA-256 `6eb16f0b187e` and OCaml 5.3.0 | Sample: 83 ACCEPT / 103 PARTIAL, 5,907 weighted PENDING, 2,070.827s / 0.498s median. Extended: 74 ACCEPT / 135 PARTIAL, 31,516 weighted PENDING, 1,751.094s / 0.547s median. Same outcomes and PENDING as the preceding capture; without proof-document hashes or paired Legacy controls, no matched-proof burn-down or parity claim. |
| Nov 24 11:55:36 | Complete pinned Schedule #5 Definition cohorts with checker SHA-256 `6eb16f0b187e` | Sample: 83 ACCEPT / 103 PARTIAL, 5,907 weighted PENDING, 2,072.97s aggregate / 0.498s median. Extended: 74 ACCEPT / 135 PARTIAL, 31,516 weighted PENDING, 1,747.76s / 0.548s. All inputs observed; missing diagnostics are UNKNOWN/TIMEOUT only. No proof hashes or paired Legacy control, so no matched-proof burn-down or parity claim. |
| Nov 24 09:19 | Replay the current SortedProof and indexed Legacy checkers on the fixed 11 proofs, compare both modes on the pinned 25-input QF_LIA sample, refresh the root-gated delta, and clarify its historical comparator | Fixed 11: SortedProof 2/11 ACCEPT, 802 PENDING, 4.34x slower; Legacy 11/11. QF_LIA sample: SortedProof 17 ACCEPT / 2 PARTIAL versus Legacy 19 ACCEPT; all 34 PENDING are `intro-def`. The root-gated array delta is +4 ACCEPT and −684 PENDING against the latest control; the 807-PENDING control in the exploratory array section is historical. No parity or 225-case cohort burn-down. |
| Nov 24 08:20 | Refresh the checked `Z3SortedProof` root and rerun sorted proof regression tests with strict warnings | Root and `Z3SortedProofTests` VCs all discharge; only the root pass silences stale-cache diagnostics 241/247, and the test module passes `--warn_error '@1..999'`. No extraction, pinned replay, or cohort run; no acceptance/PENDING delta. |
| Nov 24 08:06 | Recheck the guarded Int equality-to-bounds rewrite and conditional ApplyDefinition positive/negative controls in `Z3SortedProofTests` | F* verified the focused module with all VCs discharged using installed Z3 5.4.2; only stale-cache diagnostics 241/247 were silenced. No extraction, pinned replay, or cohort run; no acceptance/PENDING delta. |
| Nov 24 07:53 | Diagnose the current-source strict-closure failure from its retained log | Closure stops at 74/219 on a finite-field solver timeout even with `z3rlimit=100000`; no code, coverage, or timing change. Finite-field work remains paused. |
| Nov 24 07:46 | Compare Legacy and sorted `th-lemma` dispatch on the pinned 11-proof sample control | The 681 `th-lemma` PENDING are concentrated in proofs 10/20/37/40; logs lack per-entry fingerprints. Legacy's generic route has stronger model assumptions, so no direct port or causal attribution yet. No coverage/timing delta. |
| Nov 24 07:41 | Trace Farkas producer parameters through native decoding and exact certificate replay | Confirms the arithmetic checker consumes supplied weights without search; unsupported evidence falls back to generic `th-lemma` fragments. No coverage/timing delta; extended nonlinear attribution remains open. |
| Nov 24 07:34 | Trace proof-90’s remaining `quant-intro` obligations against Legacy and the existing binder kernel | Identifies 9/14 PENDING as `eq:binder->binder`; exact certificate fit and sorted-model soundness are unestablished. No checker change or coverage/timing delta. |
| Nov 24 07:26 | Hoist the definition-input budget scan and reuse collected definition items during entry rewriting | Strict `Z3IndependentDefinitionPair.fst` verification passes; focused document and NNF controls discharge VCs with stale-cache warnings 241/247. No extraction, pinned replay, cohort run, or checker timing. |
## Validation and cadence

The prior candidate passed strict F* verification for its 185 registered
production modules. After splitting the proof obligations in
`Z3BvExtract.lemma_concat_across` and
`Z3SortedRealOrder.lemma_real_negated_operand`, the current production build
verified all 167 checker modules, extracted the OCaml checker, and compiled
and linked it with Ubuntu WSL. The resulting checker SHA-256 is
`817a7ece2ae60ba2b495cdde3e80f511ae2aed64bbc43546390bf014cddb20f3`;
the build log is
`files\definition-context-checker-build-ubuntu.log`. These proof fixes were
committed as `96c98cacb` and pushed to the PR branch. The built production CLI
does not advertise `--definition-replay`, so the scheduled cohort data above
still use the retained Definition-mode binary and do not measure these source
changes.

The guarded definition-array fast path passed strict F* verification for its
218-module dependency closure, native extraction/linking, the
`test_independent_array_document.ml` regression, and the focused
`test_definition_array_replay_cli` test. The full standalone test suite was not
run for this update; a prior full run failed in the unrelated
`Z3IndependentFiniteFieldPolynomial` test at line 638, so finite-field work
remains paused. Current-source paired Legacy controls are measured on the
11-input fixed control above, where the independent checker still trails
Legacy; broader cohort parity remains unestablished. Do not treat these cohort
observations as matched-proof burn-down or Legacy parity.
The array-kernel fast path passed strict F* verification, the focused
`Z3SortedProofTests.fst` regressions, and the isolated native build. An optional
profile-instrumented build stopped with `Missing extracted rule datatype`, so
no profiler conclusions are available.
The 2026-11-22 diagnostic-wrapper change also passed strict verification for
the 220-module checker/test closure, the corrected conditional
`ApplyDefinition` controls, and the focused native array-document regression.

The six-hour smtlib-sample/smtlib-extended measurement schedule remains active.
The separate parity/performance schedule has been updated to prioritize
smtlib-sample and legacy-method parity. Preserve `N/M` for unobserved evidence,
serialize native runs with `files\current-corpus.lock`, and claim burn-down only
for identical fixed proof documents.

The latest strict production-closure attempt verified 74/219 modules, then
timed out in `Z3SortedFiniteField.lemma_pprod` at the VC
`peval v q % p == x % p` (F* reported solver timeout at `z3rlimit=100000`).
The earlier fresh-cache attempt timed out in `Z3TheoryNormalize.fst`. These
are build blockers, not checker results; no finite-field source was changed,
and current-source extraction and pinned replay remain incomplete. Logs are
under `files\proof63-budget-production-closure-verify-20261124-r2.log` and
`files\proof63-budget-strict-verify-20261124-r1.log`.

## QF_LIA ring: producer and checker evidence

The pinned ring input SHA-256 is
`bd330dab1469304d3d149dc6062aa1ba00be734aee5bad0feaa27a10267dc8c5`. On the
current source HEAD `823915c2c` (Z3 build hash
`823915c2c1595019ed0ec943d43d8de660e6b341`), the captured proof SHA-256 is
`70fbf6f5c3934ca6ac0e4373bfc5297502f75997b07ad2afc89fb819ba45c912`, matching
fixed sample proof 51. The current checker returns PARTIAL 4 solely from
`intro-def`; Legacy accepts. All 251 `arith/farkas`, one `arith/bound`, and 18
`arith/lp-integer-lattice` entries have zero PENDING. Seven alternating paired
replays measured medians of 38.915 ms for SortedProof and 18.944 ms for Legacy
(2.05x slower). Separately, five solver runs on the input were UNSAT with
28/44/92 ms min/median/max; this formula timing is not proof-checker timing.
This current-source evidence does not show a QF_LIA Farkas-certificate or
producer defect. Artifacts are under
`files\qflia-ring-current-20261123T1820PST`.

The four pending `intro-def` entries are recognized as scalar ITE definitions
on the exact proof above. Their collected order was compatible but not
`Context.ordered`, so Definition eligibility was false even though an
ungated augmented-root probe returned ACCEPT. Stable dependency ordering now
makes the context ordered and eligible; the root-gated Definition and NNF
probes both ACCEPT. The default SortedProof result remains PARTIAL 4, and the
Definition route's final result already ACCEPTed before this change, so this
is not new final acceptance or cohort burn-down. Preparation now reuses one
elaborated document; its native runtime impact has not been measured. Strict
verification of the affected Definition pipeline and focused tests passed;
the full registered test harness stopped later at the unrelated
`Z3IndependentFiniteFieldPolynomial.lemma_canon_bound_split`.

On the older
trace-06 capture (`c8fabf7675231bc5a27e9bd999c1507ce62d07a1b589157addf1f1ddbf181dcb`),
the instrumented native producer recorded 33 Farkas hints, one bound hint, and
zero pending `th-lemma` hints. The same run's checker diagnostic was PARTIAL 46:
18 `arith/lp-integer-lattice`, 4 `intro-def`, 4 `apply-def`, and 20 `rewrite`.
No producer fallback trace events were recorded.

Legacy replayed that exact capture as PARTIAL 18: all 252 serialized
`arith/farkas` entries were accepted, while the same 18 integer-lattice
obligations remained pending. Thus the 28-obligation matched gap on this proof
is in definitions and rewrites, not Farkas checking. The trace-06 checker
executable SHA-256 is `d3c61e8abd8458e171a26bcaa30805fb7fc8386760e3e2f49df34a8684bc6388`;
its instrumented C++ source SHA-256 is
`4da9870f0c3e28ed6d462fab0f54492620f06df8f5fd24d289cd4e746c731c02`.
This is a matched replay for the trace-06 build, not a result for the latest
PR-head checker.

An earlier capture of the same input (`1e9b4745f1c67b6eb8480d652208f946b5564581ac9676b92f25ef8ae80256f7`)
is a different proof document. It contains 15 `arith unsupported` lemmas and
was PARTIAL 43 under its capture checker, while Legacy accepts that document.
This confirms that the older proof supplied no Farkas certificate for those
lemmas and that Legacy's acceptance is not evidence that such a certificate
was checked: `proof_checker.cpp` returns true for bare `arith` and non-`farkas`
hints (lines 1448-1468). Because the capture hashes differ, this is not a
producer-version delta. No producer change is justified by the trace-06 proof;
the evidence points instead to integer-lattice support and the independent
checker's definition/rewrite gap.

The trace and exact Legacy replay are retained as
`files\ring-producer-trace-06.json` and
`files\ring-producer06-legacy-replay.json`. The separate cohort table above is
unchanged; these ring observations are not cohort totals.
