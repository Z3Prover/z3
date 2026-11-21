# Proof-checker pending dashboard

Updated: **2026-11-21T16:33:12-05:00**.

`PENDING` is the weighted total of unresolved obligations from diagnostic-bearing
proofs. Missing diagnostics, timeout tails, and unobserved evidence are `N/M`,
not zero. Dataset-wide PENDING totals cover only the proofs with completed
diagnostics.

## Current SMT-LIB capture

Current PR source `493f76c9d`, checker SHA-256
`66d13043b895ea096fc44eda5a8744c88ebe6ebfcd60497542e82f0a1c1fcc00`,
mode `--definition-array-replay`, OCaml 5.3.0, statically linked Z3
(`libz3ml.a` SHA-256 `05430e0c6aefd777dac9857dfb58667f236f5e20e29fb49c5fe57c69b994c882`,
`libz3.a` SHA-256 `8bae2a59f87fc79ddb88b77917ac555eb03c5f2e3382765fb3084e507df6d978`).
The checker used the pinned 225-case sample and 285-case extended manifests,
10,000-ms solver queries, 60-s per-case cap, 4,096-MiB limit, and 3,600-s
per-cohort budget. Diagnostic replays matched their original verdicts with no
diagnostic errors.

| Dataset | Outcomes | Diagnostics | Errors / mismatches | Weighted PENDING | Wall / median per case |
| --- | --- | ---: | ---: | ---: | ---: |
| smtlib-sample | 139 ACCEPT, 45 PARTIAL, 21 UNKNOWN, 20 TIMEOUT (225) | 45 / 225 | 0 / 0 | 471 | 2,250.3s / 0.781s |
| smtlib-extended | 77 ACCEPT, 126 PARTIAL, 74 UNKNOWN, 8 TIMEOUT (285) | 126 / 285 | 0 / 0 | 29,457 | 2,108.2s / 0.781s |
| fstar-build | **No current-source capture**; last measured checker `2671dc150931` | 7,190 / 7,190 completed diagnostics | 0 | 430 (last known) | N/M |

| Rule | fstar-build, last known | smtlib-sample, current | smtlib-extended, current |
| --- | ---: | ---: | ---: |
| `arith/farkas` | 3 | 0 | 11 |
| `arith/lp-integer-lattice` | N/M | 0 | 0 |
| `arith/lp-gomory` | N/M | 0 | 0 |
| `arith/lp-monomial-interval` | 1 | 0 | 26 |
| `arith/lp-monomial-substitute` | N/M | 0 | 0 |
| `assumed:nlsat` | 139 | 0 | 102 |
| `apply-def` | 0 | 0 | 0 |
| `def-axiom` | 0 | 1 | 8 |
| `der` | 0 | 6 | 0 |
| `intro-def` | 0 | 221 | 106 |
| `nnf-neg` | 10 | 0 | 0 |
| `nnf-pos` | 0 | 0 | 0 |
| `quant-intro` | 23 | 26 | 81 |
| `rewrite` | 8 | 77 | 23,789 |
| `sk` | 10 | 0 | 0 |
| `th-lemma` | 236 | 140 | 5,334 |

The fstar-build column is a historical baseline, not a current-source result;
its original run observed 407/583 cases, completed 384, timed out on 23, and
left 176 `NOT_RUN`. The current SMT-LIB input-manifest SHA-256 values are
sample `72cba03d2816fa47b8bb65d2dc03105b0781cb1243813846bbed1a789666cc44`
and extended
`6f6ad04db40a0f49733329ce056e5d599328a4468133f987a56c2172ac08cb34`.
Checker/library pins and per-case logs are retained under
`files\current-source-array-candidate-01`.

The earlier retained Definition capture on these manifests recorded 83/225
sample ACCEPT and 74/285 extended ACCEPT, with 5,907 and 31,516 PENDING.
The current Definition+Array results have higher ACCEPT totals, but
the proof-document hashes were not retained and the checker modes differ.
Therefore these deltas are **not matched-proof burn-down** and do not establish
Legacy parity. A prior fixed-proof control at an earlier source accepted 1/11
with the sort-indexed checker versus Legacy's 11/11; current-source matched
Legacy controls remain necessary to show the new checker meets or beats Legacy.

## Last 10 measured updates

Times are Pacific. A cohort comparison without identical proof-document hashes
is a coverage observation, not causal attribution or burn-down.

| Time | Change / measurement | Measured effect |
| --- | --- | --- |
| Nov 21 13:31 | Run current Definition+Array checker on both pinned SMT-LIB cohorts | Sample 139/225 ACCEPT and 471 PENDING; extended 77/285 ACCEPT and 29,457 PENDING. Relative to the prior Definition capture: sample +56 ACCEPT, extended +3; proofs are not hash-matched, so no burn-down or Legacy-parity claim. |
| Nov 21 08:26 | Pair current-source SMT-LIB sample timing controls | Sorted accepted 1/11 vs Legacy 11/11; summed medians 89.838s vs 18.253s (4.92x slower), sorted slower on 10/11. |
| Nov 21 07:49 | Replay fixed QF_LIA ring proofs on current source | Proof 52 fell 48→30 PENDING, clearing 18 `rewrite` obligations; both proofs remained PARTIAL. Sorted accepted 0/2 vs Legacy 2/2. |
| Nov 21 05:17 | Complete retained Definition-mode SMT-LIB capture | Sample 83/225 ACCEPT, 5,907 PENDING; extended 74/285 ACCEPT, 31,516 PENDING. Proof hashes absent; not matched-proof burn-down. |
| Nov 21 03:34 | Rebuild paired control at PR HEAD | Legacy accepted 2/2 vs sorted 1/2; sorted was 6.32x and 8.25x slower on the two proofs. |
| Nov 21 03:11 | Defer `integer_product` behind cheaper consequence checks | Fixed proof 51 fell 2,258.694→367.665 ms (6.14x within-checker speedup); still PARTIAL and slower than Legacy. |
| Nov 20 23:32 | Complete cohort, timing, and strict array-checker controls | Sample 4,020 PENDING; extended 31,262 (proof hashes absent). Earlier fixed-control timing was 88.699s sorted vs 26.251s Legacy (3.38x); strict F* array closure passed. |
| Nov 20 22:25 | Correct SMT-LIB mode attribution | No metric change: checker `b5e8cb065f06` used `--sorted-core`, so the capture was Core, not Definition. |
| Nov 20 21:17 | Replay sorted Core on identical QF_LIA sample proofs | Sorted accepted 1/2 vs Legacy 2/2; PENDING fell 44→4 against a different-mode control, so not source-only burn-down. |
| Nov 20 19:37 | Pair conditional `apply-def` controls | On 11 fixed proofs, sorted accepted 1/11 vs Legacy 11/11 with 840 PENDING and zero `apply-def` PENDING; sorted was 2.68x slower on the measured subset. |

## Validation and cadence

Strict F* verification passed for the 219-module independent-checker dependency
closure, including `Z3IndependentArrayDocument`. All 23 standalone CLI
regressions passed against the built independent checker. The broader
`build_independent_checker.py` run built the checker and passed its preceding
tests, then stopped at the unrelated
`Z3IndependentFiniteFieldPolynomial.fst` verification VC (line 638); do not
count the optional full test scope as passed.

The six-hour smtlib-sample/smtlib-extended measurement schedule remains active.
The separate parity/performance schedule has been updated to prioritize
smtlib-sample and legacy-method parity. Preserve `N/M` for unobserved evidence,
serialize native runs with `files\current-corpus.lock`, and claim burn-down only
for identical fixed proof documents.
