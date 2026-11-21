# Proof-checker pending dashboard

Updated: **2026-11-20T17:29:58-08:00**. The cohort figures below are the latest
completed diagnostics, not measurements of the current LP-bound candidate.
The Nov 20 rerun kept the sample figures unchanged and the extended verdict
counts unchanged, but extended weighted PENDING moved from 31,254 to 31,271.
The input manifest, checker, and native-library pins match; proof-document
hashes were not retained for the cohort, so this is not matched-proof burn-down.
The PR branch includes master through `a2fd7e6b1`.

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
| smtlib-extended | Definition `b5e8cb065f06`, `--sorted-core` | 285 / 285 | 73 ACCEPT, 135 PARTIAL, 70 UNKNOWN, 7 TIMEOUT; 0 SAT/REJECT/crash/error/NOT_RUN | 208 / 285 | 0 | 31,271 |
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
| `arith/farkas` | 0 | 15 | 3 |
| `arith/lp-integer-lattice` | N/M | N/M | N/M |
| `arith/lp-gomory` | N/M | N/M | N/M |
| `arith/lp-monomial-interval` | 0 | 40 | 1 |
| `assumed:nlsat` | 0 | 129 | 139 |
| `def-axiom` | 4 | 89 | 0 |
| `der` | 6 | 0 | 0 |
| `intro-def` | 307 | 143 | 0 |
| `nnf-neg` | 0 | 0 | 10 |
| `quant-intro` | 52 | 83 | 23 |
| `rewrite` | 152 | 24,650 | 8 |
| `sk` | 0 | 0 | 10 |
| `th-lemma` | 3,499 | 6,122 | 236 |

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

The latest extended cohort has 15 weighted `arith/farkas` PENDING. Pinned
traces cover 12 at the cohort-reported indices (AProVE QF_NIA: 3; LassoRanker
QF_NIA: 7; meti-tarski QF_NRA: 2). The AProVE document hash
`a223a1c83bccc50ec3a93a34dea312f2862f6091dece34995bdcac35607317bf` matches
a previously saved proof document for that input, but the latest cohort did
not retain document hashes, so identity to that cohort's document is
unverified. Original cohort document hashes are also unavailable for
LassoRanker and meti-tarski, so matching indices do not establish exact proof
identity there. At the traced PENDING nodes, AProVE and LassoRanker leave
bilinear or higher-degree products in the residual; meti-tarski leaves cubic
terms. The supplied weights therefore do not cancel the original nonlinear
formulas. These are QF_NIA/QF_NRA cases, not evidence that the checker rejects
a well-formed pure-linear QF_LIA certificate. To check such nonlinear steps
without search, the proof object must expose the sound product
linearization/bounds or another separately checkable nonlinear lemma that
accounts for the residual; the current Farkas weights alone do not. VeryMax
QF_NIA accounts for the remaining 3 PENDING; its same-input recapture timed
out without a proof document, so its producer/checker evidence remains N/M.
The two sample QF_LIA PARTIAL documents have no Farkas PENDING, and the
extended selection has no QF_LIA inputs. The 40 `arith/lp-monomial-interval`
PENDING are a separate rule family. Current data does not implicate integer
rounding, cuts, or bound propagation in a pure QF_LIA Farkas failure, and does
not justify a producer change without a pinned QF_LIA counterexample.

A current interactive `--sorted-core` diagnostic covered the three
CommMonoid and eleven Math.Exp proof queries, using checker `b5e8cb065f06` and
the pinned native libraries above. Its official per-query diagnostics total
16 PENDING, all in other families (`assumed:nlsat` or `th-lemma`); none are
`arith/farkas`. This is a targeted diagnostic, not a replacement for the
fstar-build cohort row, which remains the prior completed `2671dc150931`
capture. The trace helper's `BASE_FAILED_FARKAS` list tests only
`SP.arithmetic_farkas`; it does not run the full document checker, including
the typed `real_farkas` path and other fallbacks. For example, it listed 45
Math.Exp query-7 nodes while the official diagnostics reported only
`assumed:nlsat` and `th-lemma` PENDING. Those helper results are not official
Farkas failures or producer evidence.

A post-follow-up producer/checker run on the AProVE input is now pinned. The
input SHA-256 is `8e9c33d59fec315a4853913768f76e15f98aea47938c6bb69ac484ece919219a`;
the checker SHA-256 is `53f2b433d0a37ba5470ab3ebda9ce27d6316c188ceb6c4f73ae5002982df73aa`,
with `libz3.a` SHA-256
`65e3753c4688ed3f1fa2bd7f3b3855c2e7dde9b3f038c9057d3695dc8f738d91` and
`libz3ml.a` SHA-256
`f6d38ea8870fc0e2b69451e243735a5f4e13198dd8b2aa358eafd0c14ac775ba`.
The separate native proof print is 276,000 bytes (`SHA-256
86ff0c6c029f716e8ba41ff45ea74eb711478036e4f85fb2b07a2afd000ca7e3`) and
contains 12 `lp-context`, 15 `lp-linear`, 13 `lp-monomial-interval`, and 14
`lp-monomial-substitute` nodes. A checker relinked against the current native
libraries reports PARTIAL 22 with 3 `assumed:nlsat`, 14 `rewrite`, and 5
`th-lemma` PENDING; there is no arithmetic/Farkas PENDING in this run. This is
a fresh single-input diagnostic, not a matched-proof comparison to the earlier
document; the checker does not export its internal proof hash, so no burn-down
or performance claim follows.

## Burn-down on fixed evidence

| Dataset / fixed proof set | Comparison | Rule | Before | Checked | Remaining |
| --- | --- | --- | ---: | ---: | ---: |
| QF_LIA frozen ring, one document | Same checker `421406127c03`, lattice evidence erased → typed | `arith/lp-integer-lattice` | 18 | 18 | 0 |
| Same QF_LIA document | Typed-evidence result | `intro-def` | 4 | 0 | 4 |
| smtlib-sample, 11 fixed proofs | `a0ca7df92173` → `79de3a41dcdb` | `apply-def` | 80 | 80 | 0 |
| smtlib-sample, 11 fixed proofs | `79de3a41dcdb` → `2671dc150931` | `rewrite` | 43 | 7 | 36 |

These are fixed proof-set measurements; they do not imply whole-cohort parity.
The conditional apply-def row is a weighted rule diagnostic on 11 frozen
captures, not root parity: the candidate may certify an augmented proof. Its
separate CLI comparison has 1 ACCEPT and 10 PARTIAL for both candidate and
retained checkers, while Legacy accepts all 11. Paired timings on seven
captures (five repetitions per arm) give a median candidate/retained ratio of
1.0141, so there is no measured speedup; that timing applies only to candidate
`79de3a41dcdb`.

The current PR source was also strictly verified over its 167-module F*
checker-only closure, including explicit `Z3IndependentConditionalDefinition.fsti`,
and its focused native conditional-definition test passed. Source hashes match
the current checkout; the source-derived checker pin is `421406127c03`. The
same 11 frozen documents were replayed through its production
`Z3SortedProof.check_document_epsilon_diagnosed` path: 1 ACCEPT, 10 PARTIAL,
840 weighted PENDING, and zero `apply-def` PENDING in every document. Candidate
`79de` has 847 weighted PENDING on those captures; the retained checker has
927, including 80 `apply-def`. This confirms the rule-level result on the exact
PR source, but root outcomes still trail Legacy's 11/11 ACCEPT. The current
source replay is not a paired timing measurement, and the 1.0141 ratio cannot
be transferred to it; do not claim root parity or a current-source speedup.

## Last 10 measured improvements and corrections

Times are PST. Corrections and incomparable captures are not checker gains;
overlapping candidate effects must not be added.

| Time (PST) | Change / scope | Measured effect | Evidence |
| --- | --- | --- | --- |
| Nov 20 17:26 | Complete exact-PR-source conditional apply-def control | On the same 11 frozen proofs: 1 ACCEPT / 10 PARTIAL, 840 weighted PENDING, zero `apply-def` PENDING; Legacy accepts 11/11, so root parity is not met. Strict 167-module F* verification and the focused native control passed; no exact-source paired timing | `conditional-current-pr-sample-20261120T2020Z.json`, `conditional-current-source-control-02.json`, `conditional-sample-01.json`, `conditional-sample-timing-01.json` |
| Nov 20 17:05 | Complete six-hour SMT-LIB rerun and targeted interactive F* capture | Sample unchanged at 4,020; extended outcomes unchanged and PENDING 31,254 → 31,271, not matched-proof burn-down. Extended Farkas PENDING is 15: 12 traced NIA/NRA residuals and 3 VeryMax without a reproduced document. Fourteen targeted F* queries have 16 non-Farkas PENDING and zero official `arith/farkas` PENDING | `periodic-smtlib-20261120T235732Z`, `current-farkas-trace-20261120T170526Z-run02.json`, `current-fstar-build-farkas-interactive-20261120T1705Z.json`; `fstar/Z3SortedProof.fst:2030-2047,3230-3237` |
| Nov 20 17:02 | Sync PR branch with latest master | Merged fetched master through `a2fd7e6b1`; no new checker/cohort metric measured. The active cohort continues on its pinned binaries | merge `743908848`; active cohort state |
| Nov 20 16:58 | Diagnose fstar-build Farkas recapture mode | The attempted recapture used unsupported `--definition-replay` on the cohort's `Z3NativeMain` CLI; return code 2 and no proof document. No new proof or producer conclusion; retry in matching mode after the active stage | `current-fstar-build-farkas-trace-20261120.json`; `fstar/ocaml_runtime/Z3NativeMain.ml:799-830` |
| Nov 20 14:59 | Merge master unbounded-objective fix | At merged HEAD `23a61f9c0`, the focused build and `opt_bounds`, `opt_pareto`, `proof_checker`, `lp_evidence`, and `smt_context` pass (5/5); cohort figures unchanged | master `a4b03329f`; `cmake --build build --target test-z3 --parallel 32` |
| Nov 20 14:55 | Conditional apply-def checkout and matched-proof audit | Weighted rule diagnostic: 80 apply-def PENDING → 0 across 11 frozen captures, with 0 per-rule regressions; candidate/retained CLI outcomes 1 ACCEPT, 10 PARTIAL (Legacy 11 ACCEPT); paired timing ratio 1.0141. Candidate source differs from current PR checkout; no parity/promotion claim | `conditional-weighted-01.json`, `conditional-sample-01.json`, `conditional-sample-timing-01.json`, `conditional-checkout-controls-01.json`, `conditional-current-source-control-02.json` |
| Nov 20 14:45 | Merge latest master optimization fix into the PR candidate | At merged HEAD `c502703ad`, `opt_bounds`, `opt_pareto`, `proof_checker`, `lp_evidence`, and `smt_context` pass (5/5); cohort figures unchanged | master `8d5366f8c`; `cmake --build build --target test-z3 --parallel 32` |
| Nov 20 14:41 | Post-follow-up AProVE producer/checker trace | Native proof print has 12 `lp-context`, 15 `lp-linear`, 13 `lp-monomial-interval`, 14 `lp-monomial-substitute`; same-input checker PARTIAL 22 with 3 `assumed:nlsat`, 14 `rewrite`, 5 `th-lemma`, and no arithmetic/Farkas PENDING. Not comparable to earlier proof; no burn-down/performance claim | `current-lp-bound-postfix-aprove-20261120T223212Z`, `current-lp-bound-postfix-checker-20261120T224129Z` |
| Nov 20 14:12 | Correct Farkas replay-path status | `lp-linear` is already checked as candidate `ArithmeticFarkas` weights against actual formulas; no cohort metrics changed and no new burn-down/performance claim | `fstar/ocaml_runtime/Z3Native.ml`, `fstar/Z3NativeProof.fst:309-317`, `fstar/Z3UnifiedProof.fst:276`, `fstar/Z3LinearArithmeticAst.fst:216-219` |
| Nov 20 14:06 | Generate/attach bound proof evidence per consequent | Native `proof_checker`, `lp_evidence`, and `smt_context` tests pass; authentic-bound bridge case passes. No post-fix cohort or matched-proof comparison yet | `src/smt/theory_lra.cpp`, `src/smt/smt_justification.cpp`; native test commands in Validation |

## Validation and active cadence

At merged HEAD `23a61f9c0`, `cmake --build build --target test-z3 --parallel
32` and the `opt_bounds`, `opt_pareto`, `proof_checker`, `lp_evidence`, and
`smt_context` test modules pass (5/5). At candidate HEAD `817035eb8`, the
Linux `shell` and `libz3_ocaml` were built and installed; the one-case checker
was relinked against pinned `libz3.a` and `libz3ml.a` and returned PARTIAL 22
on the AProVE input.
F* checker sources are unchanged since the prior checker-only strict pass, but
a strict refresh timed out in `Z3SortedRealOrder.real_negated_operand` at the
default Z3 resource limit. An initial cached-module relink failed because
`main.cmx` and `Z3NativeMain.cmx` had inconsistent assumptions; rebuilding
`main.ml` resolved the relink. The full bridge suite's unchanged synthetic
Real-product mismatch remains unrerun. Two full
`build_ocaml_checker.ps1 -RunTests` attempts previously timed out at
`Z3SortedBv.fst:456`; no cohort candidate run is complete. The separate
interactive `--sorted-core` capture of CommMonoid and Math.Exp completed with
16 non-Farkas PENDING across 14 proof queries; it is not comparable to the
`2671dc150931` fstar-build cohort capture. The current PR source's conditional
apply-def replay on the 11 fixed sample proofs completed with 1 ACCEPT, 10
PARTIAL and zero `apply-def` PENDING; its 840 total PENDING and lack of
11/11 Legacy parity mean it is not a promotion result. No paired timing was
collected for this exact source pin.

The six-hour smtlib-sample/smtlib-extended measurement schedule remains active.
The new candidate has not been run across the cohorts; keep its weighted
PENDING as N/M until the scheduled, pinned capture completes. Preserve timeout
and missing-diagnostic counts, serialize native runs using
`files\current-corpus.lock`, and claim burn-down only on identical fixed proofs.
