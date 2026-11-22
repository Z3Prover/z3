# Proof-checker pending dashboard

Updated: **2026-11-22T09:39:04-08:00**.

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
checker was rerun on 2026-11-22 at 06:34 Pacific with the same binary and
pinned manifests. Latest aggregate case wall time / median per case was
2,013.1s / 0.580s for sample and 1,739.6s / 0.580s for extended. Outcomes,
diagnostic counts, weighted PENDING, and per-rule totals reproduced exactly;
all PARTIAL cases had diagnostics with zero errors or replay mismatches. This
confirms repeatability, not matched-proof burn-down: proof-document hashes
were not retained. The repeat artifacts are under
`files\current-retained-definition-cycle-02`.

| Dataset | Outcomes (all statuses) | Diagnostic replays | Diagnostic errors / replay mismatches | Weighted PENDING | Aggregate case time / median per case |
| --- | --- | ---: | ---: | ---: | ---: |
| smtlib-sample | 110 ACCEPT, 77 PARTIAL, 0 REJECT, 0 SAT, 21 solver UNKNOWN, 17 TIMEOUT, 0 ERROR, 0 CRASH, 0 PROTOCOL_ERROR, 0 NOT_RUN (225) | 77 / 225 | 0 / 0 | 3,836 | 2,013.1s / 0.580s |
| smtlib-extended | 78 ACCEPT, 126 PARTIAL, 0 REJECT, 0 SAT, 74 solver UNKNOWN, 7 TIMEOUT, 0 ERROR, 0 CRASH, 0 PROTOCOL_ERROR, 0 NOT_RUN (285) | 126 / 285 | 0 / 0 | 30,907 | 1,739.6s / 0.580s |
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

The proved `Z3IndependentChecker.check_definition_array_diagnosed` route was
replayed on the same 11 frozen documents from
`files\conditional-current-source-control-04e`; all proof hashes were
reverified. Source HEAD is `5e066be358246dd889c86b0f41d8ba7fad32f9f9` plus
F* source diff SHA-256
`5e6b199a448799eaa39cd3d1de9760250f0a0bdb73f7728145bb20a111ce5780`;
toolchain: F* 2026.10.25, OCaml 5.3.0, and Z3 5.4.2 (build hash
`0484078c420054c34598f245bf1d92c3ba2136fe`). Strict F* verification passed
for the 220-module checker/test dependency closure, including the corrected
conditional `ApplyDefinition` controls. The focused
`test_independent_array_document.ml` regression now passes. Re-extracted
`Z3IndependentChecker.ml` SHA-256 is
`c24727b5ff2dcdaf3b137a65d3b573d7df075d4ff51009cd18db05b2d232f6cd`; the
matched-replay helper SHA-256 is
`e6ed29be5f1de048bab4d8423433a380b685d3a32feaff1b5594c494ee48917d`.

The route again accepted 7/11 and returned PARTIAL on 4/11 (123 PENDING:
93 `intro-def`, 20 `rewrite`, 1 `def-axiom`, 9 `quantifier-intro`;
`apply-def` and `arith/farkas` were 0). Legacy accepted 11/11. The new
single-pass replay took 272.614s versus the retained same-document Legacy
total of 21.787s (about 12.51x, slower on all 11); the earlier single pass
was 213.781s, so these timings do not establish a stable performance delta.
The diagnostic fix changes reporting, not acceptance or PENDING burn-down;
the route remains behind Legacy and is not promoted. This is a fixed-proof
route experiment, not a native CLI/cohort result or burn-down, and gives no
evidence of a Farkas-producer defect. Updated per-proof results are retained
under `files\definition-array-lazy-diagnostics-20261122.tsv`; the prior
diagnostic breakdown remains in the matched capture above.

## Last 10 updates (measurements and corrections)

Times are Pacific. A cohort comparison without identical proof-document hashes
is a coverage observation, not causal attribution or burn-down.

| Time | Change / measurement | Measured effect |
| --- | --- | --- |
| Nov 22 09:39 | Fix certified array diagnostics, add valid/wrong-branch `ApplyDefinition` controls, and replay the matched 11 | Strict 220-module F* closure and focused native array test pass. Same 7/11 ACCEPT and 123 PENDING; Legacy 11/11. 272.614s vs 21.787s Legacy (12.51x, slower on all 11); one-pass timing only. Diagnostic fix, no burn-down or Farkas gap. |
| Nov 22 08:36 | Pair current-source Definition+Array route against Legacy on the same 11 frozen proofs | Independent route 7/11 ACCEPT, 123 PENDING; Legacy 11/11. 213.781s vs retained Legacy 21.787s, slower on all 11. Focused array diagnostic test failed; route not promoted. No Farkas gap or cohort burn-down inferred. |
| Nov 22 07:48 | Replay the actual sorted epsilon path and the sorted array kernel on the same 11 frozen proofs | Epsilon: 1/11 ACCEPT, 831 PENDING, 94.14s vs Legacy 11/11 and 21.787s (9/11 slower). Array kernel: 4/11 ACCEPT, 151 PENDING, but 93.40s and not a native CLI route. No parity or Farkas-producer defect established. |
| Nov 22 07:37 | Replay the same 11 frozen proofs through the sorted array-kernel route; measure the array-lemma fast path | Array kernel 4/11 ACCEPT, 151 PENDING vs ordinary sorted core 1/11, 832 PENDING; Legacy 11/11. One-pass total 93.40s vs Legacy 21.787s, slower on 8/11. Fast-path delta is 1.1%, not conclusive; kernel route is not native CLI or cohort evidence. |
| Nov 22 06:34 | Repeat the retained Definition-mode checker on both pinned cohorts; diagnose every PARTIAL | Same outcomes and per-rule PENDING as the prior capture: sample 110/225 ACCEPT and 3,836 PENDING; extended 78/285 ACCEPT and 30,907 PENDING. Diagnostics: 77/77 and 126/126, zero errors/mismatches. Latest aggregate case times 2,013.1s / 1,739.6s; no matched-proof burn-down inferred. |
| Nov 22 02:56 | Rerun the retained PR-head checker on pinned sample inputs with `--definition-array-replay`; diagnose all PARTIALs | 142/225 ACCEPT, 42 PARTIAL, 21 UNKNOWN, 20 TIMEOUT; versus Definition-only, 32 PARTIAL→ACCEPT and 3 PARTIAL→TIMEOUT with no ACCEPT regressions. 344 observed PENDING; combined mode is slower (0.779s vs 0.579s median). Input-matched only, not frozen-proof burn-down or Legacy parity. |
| Nov 21 23:04 | Complete current-source matched 11-input sample control | Independent checker 3/11 ACCEPT, 8/11 PARTIAL (811 PENDING); Legacy 11/11 ACCEPT. `apply-def` PENDING=0; single-pass medians 6.038s vs 0.573s. Fixed control only, no cohort burn-down; parity not met. |
| Nov 21 22:19 | Correct extended arithmetic-rule attribution (dashboard correction; no new run) | `arith/bound` remains 11; `arith/farkas` corrected 11→0; total PENDING remains 30,907. Classification only, not improvement or burn-down. |
| Nov 21 21:56 | Rebuild current-source ITE `DefinitionIntroduction` path; rerun pinned cohorts serially | Sample unchanged at 110/225 ACCEPT and 3,836 PENDING; extended 78/285 ACCEPT, with one TIMEOUT→PARTIAL and 30,907 PENDING. No matched-proof burn-down or causal claim: the prior run used eight workers. |
| Nov 21 18:59 | Pair trace-06 QF_LIA ring proof with Legacy | On identical capture, trace checker PENDING 46 vs Legacy 18; both leave 18 lattice obligations, while the trace checker has 28 additional definition/rewrite obligations. Legacy accepts all 252 serialized Farkas entries; producer records 33 Farkas hints, 1 bound, and 0 pending `th-lemma`. The earlier 15-unsupported capture differs, so no producer-version delta is inferred; trace build is not latest PR HEAD. |

## Validation and cadence

Strict F* verification passed for all 185 registered production modules and
the focused ITE-definition regressions. The independent checker linked and
completed both cohorts with zero diagnostic errors or replay mismatches.
`build_independent_checker.py` then stopped in its standalone test-only
`Z3IndependentFiniteFieldPolynomial` extraction because that module's cached
`.checked` file was stale; the full standalone suite remains unverified and
finite-field work remains paused. Current-source paired Legacy controls are
now measured on the 11-input fixed control above, where the independent checker
still trails Legacy; broader cohort parity remains unestablished. Do not treat
these cohort observations as matched-proof burn-down or Legacy parity.
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

## QF_LIA ring: producer and checker evidence

The pinned ring input SHA-256 is
`bd330dab1469304d3d149dc6062aa1ba00be734aee5bad0feaa27a10267dc8c5`. On the
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
