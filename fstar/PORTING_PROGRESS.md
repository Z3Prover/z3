# Proof-checker pending dashboard

Updated: **2026-11-21T18:34:53-08:00**.

`PENDING` is the weighted total of unresolved obligations from diagnostic-bearing
proofs. Missing diagnostics, timeout tails, and unobserved evidence are `N/M`,
not zero. Dataset-wide PENDING totals cover only the proofs with completed
diagnostics.

## Current SMT-LIB capture

Candidate built atop source HEAD `aef2b8dac0c23fd435ab24fbb05c3b4574893174`, checker
SHA-256 `a61618bf4602124779f2ddd3ce309a671ac9e6fdbf18cfb4a7887f4f8fdacade`,
mode `--definition-replay`, OCaml 5.3.0, and statically linked Z3 build
`aef2b8dac0c23fd435ab24fbb05c3b4574893174` (`libz3ml.a` SHA-256
`05430e0c6aefd777dac9857dfb58667f236f5e20e29fb49c5fe57c69b994c882`,
`libz3.a` SHA-256
`655d31c28d475f13eb802fc88771938362a3a3f4cef1bc0d0b7701b20eefcd39`).
This candidate adds bounded Boolean search to sorted rewrite checking. The
cohorts used the pinned 225-case sample and 285-case extended manifests,
10,000-ms solver queries, 60-s per-case cap, 4,096-MiB limit, and eight
parallel workers. Elapsed cohort wall time was 274.1s / 245.8s. Inline
diagnostics were collected for 187 sample and 203 extended cases with zero
diagnostic errors.

| Dataset | Outcomes | Diagnostics | Diagnostic errors / replay mismatches | Weighted PENDING | Aggregate case time / median per case |
| --- | --- | ---: | ---: | ---: | ---: |
| smtlib-sample | 110 ACCEPT, 77 PARTIAL, 21 UNKNOWN, 17 TIMEOUT (225) | 187 / 225 | 0 / N/A | 3,836 | 2,069.7s / 0.630s |
| smtlib-extended | 78 ACCEPT, 125 PARTIAL, 74 UNKNOWN, 8 TIMEOUT (285) | 203 / 285 | 0 / N/A | 28,404 | 1,789.5s / 0.582s |
| fstar-build | **No current-source capture**; last measured checker `2671dc150931` | 7,190 / 7,190 completed diagnostics | 0 / N/M | 430 (last known) | N/M |

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
| `rewrite` | 8 | 124 | 21,839 |
| `sk` | 10 | 0 | 0 |
| `th-lemma` | 236 | 3,499 | 6,153 |

The fstar-build column is a historical baseline, not a current-source result;
its original run observed 407/583 cases, completed 384, timed out on 23, and
left 176 `NOT_RUN`. The current SMT-LIB input-manifest SHA-256 values are
sample `72cba03d2816fa47b8bb65d2dc03105b0781cb1243813846bbed1a789666cc44`
and extended
`6f6ad04db40a0f49733329ce056e5d599328a4468133f987a56c2172ac08cb34`.
Checker, manifest, and per-case logs are retained under
`files\boolean-search-cohorts-20261121-212122`.

The retained pre-patch Definition capture recorded 83/225 sample ACCEPT and
74/285 extended ACCEPT, with 5,907 sample PENDING. Its extended PENDING is
31,501 in the saved run state/per-rule totals, while an older dashboard says
31,516; that discrepancy remains unresolved. This candidate records 27 more
sample ACCEPT and 2,071 fewer sample PENDING, plus 4 more extended ACCEPT and
3,097 fewer extended PENDING against the saved run state (3,112 fewer against
the older dashboard total). Proof-document hashes were not retained, so these
are cohort coverage observations, **not matched-proof burn-down** or a
Legacy-parity result. The earlier Definition+Array capture is a different
checker mode and is not a direct comparison. A prior fixed-proof control
accepted 1/11 with the sort-indexed checker versus Legacy's 11/11; current-source
matched Legacy controls remain necessary to show the new checker meets or beats
Legacy.

## Last 10 measured updates

Times are Pacific. A cohort comparison without identical proof-document hashes
is a coverage observation, not causal attribution or burn-down.

| Time | Change / measurement | Measured effect |
| --- | --- | --- |
| Nov 21 18:21 | Add bounded Boolean search to sorted rewrite; measure pinned cohorts | Sample 110/225 ACCEPT and 3,836 PENDING; extended 78/285 ACCEPT and 28,404 PENDING. Relative to the retained Definition capture, +27/+4 ACCEPT and -2,071/-3,097 PENDING by saved totals; extended PENDING differs by 15 from the older dashboard. Proof hashes are absent, so not matched-proof burn-down. |
| Nov 21 13:31 | Run current Definition+Array checker on both pinned SMT-LIB cohorts | Sample 139/225 ACCEPT and 471 PENDING; extended 77/285 ACCEPT and 29,457 PENDING. Relative to the prior Definition capture: sample +56 ACCEPT, extended +3; proofs are not hash-matched, so no burn-down or Legacy-parity claim. |
| Nov 21 08:26 | Pair current-source SMT-LIB sample timing controls | Sorted accepted 1/11 vs Legacy 11/11; summed medians 89.838s vs 18.253s (4.92x slower), sorted slower on 10/11. |
| Nov 21 07:49 | Replay fixed QF_LIA ring proofs on current source | Proof 52 fell 48→30 PENDING, clearing 18 `rewrite` obligations; both proofs remained PARTIAL. Sorted accepted 0/2 vs Legacy 2/2. |
| Nov 21 05:17 | Complete retained Definition-mode SMT-LIB capture | Sample 83/225 ACCEPT, 5,907 PENDING; extended 74/285 ACCEPT; saved PENDING 31,501 vs older dashboard 31,516 (unresolved). Proof hashes absent; not matched-proof burn-down. |
| Nov 21 03:34 | Rebuild paired control at PR HEAD | Legacy accepted 2/2 vs sorted 1/2; sorted was 6.32x and 8.25x slower on the two proofs. |
| Nov 21 03:11 | Defer `integer_product` behind cheaper consequence checks | Fixed proof 51 fell 2,258.694→367.665 ms (6.14x within-checker speedup); still PARTIAL and slower than Legacy. |
| Nov 20 23:32 | Complete cohort, timing, and strict array-checker controls | Sample 4,020 PENDING; extended 31,262 (proof hashes absent). Earlier fixed-control timing was 88.699s sorted vs 26.251s Legacy (3.38x); strict F* array closure passed. |
| Nov 20 22:25 | Correct SMT-LIB mode attribution | No metric change: checker `b5e8cb065f06` used `--sorted-core`, so the capture was Core, not Definition. |
| Nov 20 21:17 | Replay sorted Core on identical QF_LIA sample proofs | Sorted accepted 1/2 vs Legacy 2/2; PENDING fell 44→4 against a different-mode control, so not source-only burn-down. |

## Validation and cadence

Strict F* verification passed for the changed `Z3SortedProof.fst` and
`Z3SortedProofTests.fst`; the generic sorted-core native build and all 84 CLI
tests passed. The candidate independent executable was manually relinked from
current production extraction and retained independent-only modules after the
clean Linux F* build hit unrelated cache/solver timeouts. Its cohort runs
completed with no diagnostic errors, but the canonical independent build and
its full standalone test suite remain unverified. Do not treat the cohort
comparison as matched-proof burn-down or Legacy parity.

The six-hour smtlib-sample/smtlib-extended measurement schedule remains active.
The separate parity/performance schedule has been updated to prioritize
smtlib-sample and legacy-method parity. Preserve `N/M` for unobserved evidence,
serialize native runs with `files\current-corpus.lock`, and claim burn-down only
for identical fixed proof documents.
