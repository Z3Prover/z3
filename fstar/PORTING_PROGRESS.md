# Proof-checker pending dashboard

Updated: **2026-11-21T21:56:06-08:00**.

`PENDING` is the weighted total of unresolved obligations from diagnostic-bearing
proofs. Missing diagnostics, timeout tails, and unobserved evidence are `N/M`,
not zero. Dataset-wide PENDING totals cover only the proofs with completed
diagnostics.

## Current SMT-LIB capture

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
per-case cap, a 4,096-MiB limit, and a 3,600-s cohort budget. Aggregate case
wall time / median per case was 2,016.1s / 0.579s for sample and
1,746.4s / 0.580s for extended. Diagnostic replays covered all PARTIAL cases,
with zero diagnostic errors or replay mismatches.

| Dataset | Outcomes (all statuses) | Diagnostic replays | Diagnostic errors / replay mismatches | Weighted PENDING | Aggregate case time / median per case |
| --- | --- | ---: | ---: | ---: | ---: |
| smtlib-sample | 110 ACCEPT, 77 PARTIAL, 0 REJECT, 0 SAT, 21 solver UNKNOWN, 17 TIMEOUT, 0 ERROR, 0 CRASH, 0 PROTOCOL_ERROR, 0 NOT_RUN (225) | 77 / 225 | 0 / 0 | 3,836 | 2,016.1s / 0.579s |
| smtlib-extended | 78 ACCEPT, 126 PARTIAL, 0 REJECT, 0 SAT, 74 solver UNKNOWN, 7 TIMEOUT, 0 ERROR, 0 CRASH, 0 PROTOCOL_ERROR, 0 NOT_RUN (285) | 126 / 285 | 0 / 0 | 30,907 | 1,746.4s / 0.580s |
| fstar-build | **No current-source capture**; last measured checker `2671dc150931` | 7,190 / 7,190 completed diagnostics | 0 / N/M | 430 (last known) | N/M |

Every PARTIAL case has a completed proof diagnostic (77/77 and 126/126);
diagnostic error/mismatch counts apply only to those replays. ACCEPT,
solver-UNKNOWN, and TIMEOUT cases have no proof diagnostic; their outcome
counts above are explicit and are not treated as zero-PENDING evidence.

| Rule | fstar-build, last known | smtlib-sample, current | smtlib-extended, current |
| --- | ---: | ---: | ---: |
| `arith/bound` | N/M | 0 | 11 |
| `arith/farkas` | 3 | 0 | 11 |
| `arith/lp-integer-lattice` | N/M | 0 | 0 |
| `arith/lp-gomory` | N/M | 0 | 0 |
| `arith/lp-monomial-interval` | 1 | 0 | 26 |
| `arith/lp-monomial-substitute` | N/M | 0 | 0 |
| `assumed:nlsat` | 139 | 0 | 102 |
| `apply-def` | 0 | 0 | 0 |
| `def-axiom` | 0 | 3 | 89 |
| `der` | 0 | 6 | 0 |
| `intro-def` | 0 | 162 | 103 |
| `nnf-neg` | 10 | 0 | 0 |
| `nnf-pos` | 0 | 0 | 0 |
| `quant-intro` | 23 | 42 | 81 |
| `rewrite` | 8 | 124 | 24,342 |
| `sk` | 10 | 0 | 0 |
| `th-lemma` | 236 | 3,499 | 6,153 |

The fstar-build column is a historical baseline, not a current-source result;
its original run observed 407/583 cases, completed 384, timed out on 23, and
left 176 `NOT_RUN`. The current SMT-LIB input-manifest SHA-256 values are
sample `72cba03d2816fa47b8bb65d2dc03105b0781cb1243813846bbed1a789666cc44`
and extended
`6f6ad04db40a0f49733329ce056e5d599328a4468133f987a56c2172ac08cb34`.
Current checker, manifest, per-case results, and diagnostic logs are retained
under `files\current-ite-intro-cohorts-01`.

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
checker versus Legacy's 11/11; current-source matched Legacy controls remain
necessary to show the new checker meets or beats Legacy.

## Last 10 measured updates

Times are Pacific. A cohort comparison without identical proof-document hashes
is a coverage observation, not causal attribution or burn-down.

| Time | Change / measurement | Measured effect |
| --- | --- | --- |
| Nov 21 21:56 | Rebuild current-source ITE `DefinitionIntroduction` path; rerun pinned cohorts serially | Sample unchanged at 110/225 ACCEPT and 3,836 PENDING; extended 78/285 ACCEPT, with one TIMEOUT→PARTIAL and 30,907 PENDING. No matched-proof burn-down or causal claim: the prior run used eight workers. |
| Nov 21 18:59 | Pair trace-06 QF_LIA ring proof with Legacy | On identical capture, trace checker PENDING 46 vs Legacy 18; both leave 18 lattice obligations, while the trace checker has 28 additional definition/rewrite obligations. Legacy accepts all 252 serialized Farkas entries; producer records 33 Farkas hints, 1 bound, and 0 pending `th-lemma`. The earlier 15-unsupported capture differs, so no producer-version delta is inferred; trace build is not latest PR HEAD. |
| Nov 21 18:21 | Add bounded Boolean search to sorted rewrite; measure pinned cohorts | Sample 110/225 ACCEPT and 3,836 PENDING; extended 78/285 ACCEPT and 28,404 PENDING. Relative to the retained Definition capture, +27/+4 ACCEPT and -2,071/-3,097 PENDING by saved totals; extended PENDING differs by 15 from the older dashboard. Proof hashes are absent, so not matched-proof burn-down. |
| Nov 21 13:31 | Run current Definition+Array checker on both pinned SMT-LIB cohorts | Sample 139/225 ACCEPT and 471 PENDING; extended 77/285 ACCEPT and 29,457 PENDING. Relative to the prior Definition capture: sample +56 ACCEPT, extended +3; proofs are not hash-matched, so no burn-down or Legacy-parity claim. |
| Nov 21 08:26 | Pair current-source SMT-LIB sample timing controls | Sorted accepted 1/11 vs Legacy 11/11; summed medians 89.838s vs 18.253s (4.92x slower), sorted slower on 10/11. |
| Nov 21 07:49 | Replay fixed QF_LIA ring proofs on current source | Proof 52 fell 48→30 PENDING, clearing 18 `rewrite` obligations; both proofs remained PARTIAL. Sorted accepted 0/2 vs Legacy 2/2. |
| Nov 21 05:17 | Complete retained Definition-mode SMT-LIB capture | Sample 83/225 ACCEPT, 5,907 PENDING; extended 74/285 ACCEPT; saved PENDING 31,501 vs older dashboard 31,516 (unresolved). Proof hashes absent; not matched-proof burn-down. |
| Nov 21 03:34 | Rebuild paired control at PR HEAD | Legacy accepted 2/2 vs sorted 1/2; sorted was 6.32x and 8.25x slower on the two proofs. |
| Nov 21 03:11 | Defer `integer_product` behind cheaper consequence checks | Fixed proof 51 fell 2,258.694→367.665 ms (6.14x within-checker speedup); still PARTIAL and slower than Legacy. |
| Nov 20 23:32 | Complete cohort, timing, and strict array-checker controls | Sample 4,020 PENDING; extended 31,262 (proof hashes absent). Earlier fixed-control timing was 88.699s sorted vs 26.251s Legacy (3.38x); strict F* array closure passed. |

## Validation and cadence

Strict F* verification passed for all 185 registered production modules and
the focused ITE-definition regressions. The independent checker linked and
completed both cohorts with zero diagnostic errors or replay mismatches.
`build_independent_checker.py` then stopped in its standalone test-only
`Z3IndependentFiniteFieldPolynomial` extraction because that module's cached
`.checked` file was stale; the full standalone suite remains unverified and
finite-field work remains paused. Current-source paired Legacy controls are
still pending. Do not treat these cohort observations as matched-proof
burn-down or Legacy parity.

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
