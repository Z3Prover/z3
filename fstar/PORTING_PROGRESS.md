# Proof-checker pending dashboard

Updated: **2026-11-20T14:06:08-08:00**. The cohort figures below are the last
completed diagnostics, not measurements of the current LP-bound candidate.
The current source branch includes master through `bf981cb1b`; the candidate
checker hash and fresh cohort results are N/M.

**Old historical** means archived measurements from earlier Legacy-checker
captures, not a current checker binary. **Core** is the sort-indexed checker
without definition, NNF, or Skolem replay. **Definition** adds those replays to
Core; its interpretation maps each sort AST to a value type (`sort -> Type`)
and does not use `Z3ValueTheory.fst`.

PENDING is the weighted count of unresolved proof-rule obligations in completed
diagnostics. Missing diagnostics, timeout tails, and unobserved evidence are
N/M, never zero.

## Latest completed cohort captures

| Dataset | Checker pin and mode | Observed / selected | Case status / observed verdicts | Diagnostics / observed | Diagnostic errors | Weighted PENDING |
| --- | --- | ---: | --- | ---: | ---: | ---: |
| smtlib-sample | Definition `b5e8cb065f06`, `--sorted-core` | 225 / 225 | 100 ACCEPT, 88 PARTIAL, 20 UNKNOWN, 17 TIMEOUT; 0 SAT/REJECT/crash/error/NOT_RUN | 188 / 225 | 0 | 4,020 |
| smtlib-extended | Definition `b5e8cb065f06`, `--sorted-core` | 285 / 285 | 73 ACCEPT, 135 PARTIAL, 70 UNKNOWN, 7 TIMEOUT; 0 SAT/REJECT/crash/error/NOT_RUN | 208 / 285 | 0 | 31,254 |
| fstar-build | Definition `2671dc150931` | 407 / 583 observed; 384 completed, 23 TIMEOUT, 176 NOT_RUN | 8,411 ACCEPT, 209 PARTIAL verdicts; 0 UNKNOWN/REJECT among observed verdicts; 256 solver-UNKNOWN queries | 7,190 / 7,190 completed diagnostics | 0 | 430 |

The SMT-LIB checker SHA-256 is
`b5e8cb065f06b49a42bc9dab56669dd3cea9804e9650326d0a7ef3ffd17258de`.
Its `libz3ml.a` and `libz3.a` pins are
`62ac403890a049d879e11422efbff9452cd7b849f6dc48a666e22405a354458c` and
`9568710d43d750bc7439094d9ce9eaa2754c36a6dda4f28a81da3d2309f921a4`.
The fstar-build manifest is
`151fb3147a773d622252d6db5786802e11b62b19a61a2af83ed0ff6c89826187`.
SMT-LIB manifests: sample
`72cba03d2816fa47b8bb65d2dc03105b0781cb1243813846bbed1a789666cc44`,
extended `6f6ad04db40a0f49733329ce056d5e599328a4468133f987a56c2172ac08cb34`.

| Rule | smtlib-sample PENDING | smtlib-extended PENDING | fstar-build PENDING |
| --- | ---: | ---: | ---: |
| `arith/farkas` | 0 | 17 | 3 |
| `arith/lp-integer-lattice` | N/M | N/M | N/M |
| `arith/lp-gomory` | N/M | N/M | N/M |
| `arith/lp-monomial-interval` | 0 | 40 | 1 |
| `assumed:nlsat` | 0 | 128 | 139 |
| `def-axiom` | 4 | 89 | 0 |
| `der` | 6 | 0 | 0 |
| `intro-def` | 307 | 139 | 0 |
| `nnf-neg` | 0 | 0 | 10 |
| `quant-intro` | 52 | 83 | 23 |
| `rewrite` | 152 | 24,641 | 8 |
| `sk` | 0 | 0 | 10 |
| `th-lemma` | 3,499 | 6,117 | 236 |

The sample QF_LIA slice contains 25 inputs: 17 ACCEPT, 2 PARTIAL, 1 TIMEOUT,
and 5 UNKNOWN. Its two PARTIAL proofs have 52 PENDING (34 `intro-def`, 18
`rewrite`) and no `arith/farkas` PENDING. The extended selection has no QF_LIA
inputs. The fstar-build timeout tails have N/M rule diagnostics.

## QF_LIA/Farkas status and candidate

The frozen QF_LIA ring document (`68279bde5cd0...`, checker
`421406127c03`) has 18 typed `ArithmeticLattice` entries; replay checks all
18, leaving 4 `intro-def` PENDING. Erasing only those entries from that same
document restores 18 `arith/lp-integer-lattice` PENDING (22 total). This is a
same-document evidence control, not a whole-cohort or Legacy parity claim.

The producer reconstructs an LP derivation for a propagated bound only when
direct coefficient replay fails, then attaches it only if the native proof
validates and its conclusion exactly matches that bound. The per-consequent
follow-up ensures distinct propagated bounds cannot reuse a proof with another
conclusion. An earlier AProVE capture, before this follow-up, emitted 12
`lp-context` nodes and reported PARTIAL 22 (`assumed:nlsat` 3, `rewrite` 14,
`th-lemma` 5), versus a prior non-identical document at PARTIAL 24
(`arith/farkas` 3, `assumed:nlsat` 6, `rewrite` 13, `th-lemma` 2). The proof
hashes differ; neither this capture nor the follow-up is matched-proof
burn-down or a performance result. The earlier document SHA-256 is
`a4010d3132426167c23a5eb31e85077af9efcbfd1b0f46b9424453aa1a1c627d`;
the prior capture is `a223a1c83bccc50ec3a93a34dea312f2862f6091dece34995bdcac35607317bf`.

Current captured cohort Farkas failures are nonlinear QF_NIA/QF_NRA residuals,
not controlled QF_LIA failures. The typed certificate decoder checks LP
structure, while the native proof mapper currently gives typed replay to
integer-lattice and Gomory steps; generic LP steps still need rule-specific
checker replay. No producer defect is established by the current cohort data.

## Burn-down on fixed evidence

| Dataset / fixed proof set | Comparison | Rule | Before | Checked | Remaining |
| --- | --- | --- | ---: | ---: | ---: |
| QF_LIA frozen ring, one document | Same checker `421406127c03`, lattice evidence erased → typed | `arith/lp-integer-lattice` | 18 | 18 | 0 |
| Same QF_LIA document | Typed-evidence result | `intro-def` | 4 | 0 | 4 |
| smtlib-sample, 11 fixed proofs | `a0ca7df92173` → `79de3a41dcdb` | `apply-def` | 80 | 80 | 0 |
| smtlib-sample, 11 fixed proofs | `79de3a41dcdb` → `2671dc150931` | `rewrite` | 43 | 7 | 36 |

These are fixed proof-set measurements; they do not imply whole-cohort parity.

## Last 10 measured improvements and corrections

Times are PST. Corrections and incomparable captures are not checker gains;
overlapping candidate effects must not be added.

| Time (PST) | Change / scope | Measured effect | Evidence |
| --- | --- | --- | --- |
| Nov 20 14:06 | Generate/attach bound proof evidence per consequent | Native `proof_checker`, `lp_evidence`, and `smt_context` tests pass; authentic-bound bridge case passes. No post-fix cohort or AProVE capture yet | `src/smt/theory_lra.cpp`, `src/smt/smt_justification.cpp`; native test commands in Validation |
| Nov 20 13:58 | LP derivation attachment for bound propagation; native validation | Focused `test-z3` targets pass. AProVE candidate has 12 `lp-context` nodes and PARTIAL 22, but its proof differs from the prior PARTIAL 24 capture; no burn-down or performance claim | `src/smt/theory_lra.cpp`, `src/smt/smt_justification.cpp`; `current-lp-bound-aprove-trace03.*` |
| Nov 20 12:33 | Same-pin QF_LIA and extended Farkas trace | Both sample QF_LIA PARTIAL documents have no failed Farkas node; their 52 PENDING remain `intro-def`/`rewrite`. Three extended nonlinear cases reproduce 12 weighted Farkas PENDING; no matched-proof claim | `current-farkas-trace-summary-20261120.json`, `current-farkas-trace-20261120.json`, `current-qflia-farkas-trace-20261120.json` |
| Nov 20 12:04 | Mixed-sort strict-bound rounding guard; serial SMT-LIB rerun | Forged mixed-sort contradiction rejected; integer-valued control accepted. Sample QF_LIA has 0 Farkas PENDING; sample total remains 4,020; extended total rises by 9. No matched-proof gain | `current-farkas-rounding-validation`, `periodic-smtlib-20261120T185721Z` |
| Nov 19 20:41 | Same-run QF_LIA producer/checker trace | Pinned 1,196-node proof: 33 `farkas` hints and one six-premise `bound` hint. Same-capture diagnostic PARTIAL 46; differs from typed replay proof, so no burn-down credit | `ring-producer-trace-06.json`, `ring-producer-trace-06.stderr` |
| Nov 19 20:15–20:27 | QF_LIA lattice replay and provenance audit | Same-proof lattice evidence reduces PENDING 22 → 4; five paired runs median 1.253197s → 0.038934s (32.2×). Producer trace is not byte-identical to typed document | `current-qflia-lattice-replay-03.json`, `current-qflia-lattice-rule-count-03.json`, `ring-native-hints-2671-01.json` |
| Nov 19 14:00 | QF_LIA producer-to-checker trace | Historical 1,196-node document had 18 unrecognized lattice steps and PARTIAL 22; later typed replay supersedes this coverage result | `ring-producer-evidence-20261119T1626ET` |
| Nov 19 13:22 | Cached-root experiment; matched-proof correction | Candidate had 43 PENDING versus baseline 4 on the same 927-node proof; paired median check-time ratio 1.0061. Not promoted | `ring-matched-proof-capture-20261119T1550ET-order2`, `ring-inprocess-route-isolation-20261119T1612ET-order2` |
| Nov 19 12:28 | fstar-build Farkas provenance triage | Three observed PENDING are in `Algebra.CommMonoid` and `Math.Exp`; native payloads and proof hashes N/M | `fstar-build-incremental-20261119T193000Z` |
| Nov 19 12:24 | Same-pin fstar-build refresh | 384 completed, 23 TIMEOUT, 176 NOT_RUN; 430 weighted PENDING across completed diagnostics. Not comparable to prior 253-input capture | `fstar-build-incremental-20261119T193000Z` |

## Validation and active cadence

After merging master commit `bf981cb1b`, `cmake --build build --target
test-z3 --parallel 32`, `test-z3 smt_context`, `test-z3 proof_checker`, and
`test-z3 lp_evidence` pass. The updated Linux `libz3_ocaml` target and install
pass; the all-target build hits a stale `examples/ml/z3.cmi` compiled with an
older OCaml version. The native bridge's `authentic-bound-parameters` test
passes; the full bridge suite still fails in unchanged synthetic Real-product
coverage (`th-lemma`: expected PENDING 1, actual 0; baseline has not been
rerun). Two full `build_ocaml_checker.ps1 -RunTests` attempts timed out at
`Z3SortedBv.fst:456`; the native bridge stage was not reached. A checker-only
strict build had passed before this full-scope attempt.

The six-hour smtlib-sample/smtlib-extended measurement schedule remains active.
The new candidate has not been run across the cohorts; keep its weighted
PENDING as N/M until the scheduled, pinned capture completes. Preserve timeout
and missing-diagnostic counts, serialize native runs using
`files\current-corpus.lock`, and claim burn-down only on identical fixed proofs.
