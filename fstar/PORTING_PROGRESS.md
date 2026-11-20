# Proof-checker pending dashboard

Updated: **2026-11-19T20:40:59-08:00**. The cohort tables below are the latest
complete captures pinned to checker `2671dc150931`; the single-proof result
uses the current-worktree checker and does not refresh those cohort totals.

**Old historical** means archived measurements from earlier Legacy-checker
captures, not a current checker binary. **Legacy** uses `Z3ValueTheory.fst`.
**Core** is the sort-indexed checker without definition, NNF, or Skolem replay.
**Definition** adds those replays to Core; its interpretation maps each sort AST
to a value type (`sort -> Type`) and does not use `Z3ValueTheory.fst`.

PENDING counts are weighted unresolved proof-rule obligations, not PARTIAL
proof counts. Rule totals cover only completed diagnostics. Missing diagnostics,
timeout tails, and unobserved obligations are **N/M**, never zero.

## Current SMT-LIB diagnostic collection

Updated `2026-11-19T11:10:50-08:00`; latest case
`2026-11-19T11:07:40-08:00`; Definition checker
`2671dc1509317d8d991f5b7a3f3f3ff41d5b19a043db95d7ca3ec27ffdafe0b9`.
Only successful diagnostic results contribute to the rule table.

| Cohort | Latest case | Observed / selected | Diagnostics / observed | Diagnostic errors | ACCEPT | PARTIAL | UNKNOWN | TIMEOUT | SAT | REJECT | Crash / error | NOT_RUN |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| smtlib-sample | `2026-11-19T10:38:14-08:00` | 225 / 225 | 186 / 225 | 0 | 100 | 86 | 20 | 19 | 0 | 0 | 0 | 0 |
| smtlib-extended | `2026-11-19T11:07:40-08:00` | 285 / 285 | 208 / 285 | 0 | 74 | 134 | 70 | 7 | 0 | 0 | 0 | 0 |

| Rule | Sample observed PENDING | Extended observed PENDING |
| --- | ---: | ---: |
| `arith/farkas` | 0 | 14 |
| `arith/lp-monomial-interval` | 0 | 40 |
| `assumed:nlsat` | 0 | 148 |
| `def-axiom` | 3 | 89 |
| `der` | 6 | 0 |
| `intro-def` | 272 | 127 |
| `quant-intro` | 42 | 83 |
| `rewrite` | 133 | 24654 |
| `th-lemma` | 3499 | 6197 |

The sample QF_LIA slice has 25 inputs: 17 ACCEPT, 1 PARTIAL, 2 TIMEOUT, and
5 UNKNOWN; its PARTIAL has four `intro-def` PENDING. The extended selection
contains no QF_LIA inputs. Manifests: sample
`72cba03d2816fa47b8bb65d2dc03105b0781cb1243813846bbed1a789666cc44`,
extended `6f6ad04db40a0f49733329ce056d5e599328a4468133f987a56c2172ac08cb34`.
Per-case evidence is in `files\periodic-smtlib-20261119T173100Z`.

## Current fstar-build diagnostic collection

Updated `2026-11-19T12:28:50-08:00`; Definition checker
`2671dc1509317d8d991f5b7a3f3f3ff41d5b19a043db95d7ca3ec27ffdafe0b9`;
corpus manifest
`151fb3147a773d622252d6db5786802e11b62b19a61a2af83ed0ff6c89826187`.

| Observed / selected | Completed | TIMEOUT | Error / crash | NOT_RUN | Rule-diagnosed / completed | Diagnostic errors |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 407 / 583 | 384 | 23 | 0 | 176 | 7,190 / 7,190 | 0 |

Observed verdicts: 8,411 ACCEPT / 209 PARTIAL / 0 UNKNOWN / 0 REJECT;
solver UNKNOWN queries: 256. Timeout prefixes contain 1,430 verdicts
(1,405 ACCEPT / 25 PARTIAL), but their rule diagnostics and tails are N/M.

| Rule | Completed-diagnostic PENDING |
| --- | ---: |
| `arith/farkas` | 3 |
| `arith/lp-monomial-interval` | 1 |
| `assumed:nlsat` | 139 |
| `def-axiom` | 0 |
| `der` | 0 |
| `intro-def` | 0 |
| `nnf-neg` | 10 |
| `quant-intro` | 23 |
| `rewrite` | 8 |
| `sk` | 10 |
| `th-lemma` | 236 |

Rule totals sum to 430. The three observed `arith/farkas` PENDING occur in two
queries with product/division-shaped context and `assumed:nlsat`; exact native
certificate provenance is N/M. The 14 SMT-LIB `arith/farkas` PENDING are in
QF_NIA/QF_NRA cases with nonlinear residuals, not controlled QF_LIA failures.
Neither capture establishes a producer defect. Evidence and input hashes:
`files\fstar-build-incremental-20261119T193000Z`.

## Last 10 incremental improvements and measurement corrections

Times are PST. Retain only the 10 latest measured improvements/corrections;
corrections are not checker gains, and overlapping candidate gains must not be
added.

| Time (PST) | Improvement and scope | Measured effect | Evidence in session `files\` |
| --- | --- | --- | --- |
| Nov 19 20:41 | Same-run QF_LIA producer/checker trace; 1,196-node proof | The pinned `c8fabf...` proof emitted 33 `farkas` hints (weights 1,1) and one six-premise `bound` hint at index 755 (weights 1/2, 2, 16, 8, 1/2, 1/2, 1). The same-capture diagnostic has no `arith/farkas` PENDING, but remains PARTIAL 46 (18 lattice, 4 `intro-def`, 4 `apply-def`, 20 `rewrite`). It differs from typed replay proof `68279b...`; no burn-down credit | `ring-producer-trace-06.json`, `ring-producer-trace-06.stderr`, `current-qflia-lattice-replay-03.json` |
| Nov 19 20:15; source audit 20:20; provenance 20:27 | QF_LIA lattice replay and Farkas producer/checker audit; one frozen 1,196-node proof | Same current checker and proof: the control with 18 typed lattice rules erased is PARTIAL 22 (18 `arith/lp-integer-lattice`, 4 `intro-def`); full evidence is PARTIAL 4 (`intro-def`). Five alternating pairs: median 1.253197s → 0.038934s (32.2x). Provenance review distinguishes the exact 2671 ring trace from current producer document `c8fabf...`; the latter is not a byte-identical replay of typed document `68279b...` | `current-qflia-lattice-replay-03.json`, `current-qflia-lattice-rule-count-03.json`, `ring-native-hints-2671-01.json`, `ring-producer-evidence-20261119T1626ET\summary-current.json` |
| Nov 19 14:00 | QF_LIA producer-to-checker trace; historical baseline proof | The 1,196-node document SHA-256 `c8fabf7675231bc5a27e9bd999c1507ce62d07a1b589157addf1f1ddbf181dcb` had 18 unrecognized lattice steps and PARTIAL 22; exact per-rule attribution was then N/M. The later typed-evidence result above supersedes this coverage finding | `ring-producer-evidence-20261119T1626ET` |
| Nov 19 13:22 | Cached-root experiment; matched-proof correction | Baseline `2671dc150931` had 4 PENDING; candidate `4a4d6e2ac0b9` had 43 on the same 927-node proof. Five pairs gave median candidate/baseline `check_ms` ratio 1.0061. Not promoted; no burn-down credit | `ring-matched-proof-capture-20261119T1550ET-order2`, `ring-inprocess-route-isolation-20261119T1612ET-order2` |
| Nov 19 12:28 | fstar-build Farkas provenance triage | Three observed PENDING are in `Algebra.CommMonoid` and `Math.Exp`; native payloads and proof hashes are N/M. No controlled QF_LIA failure or producer defect established | `fstar-build-incremental-20261119T193000Z` |
| Nov 19 12:24 | Same-pin fstar-build coverage refresh | 384 completed, 23 TIMEOUT, 176 NOT_RUN; 430 weighted PENDING across completed diagnostics. Not comparable to the prior 253-input capture | `fstar-build-incremental-20261119T193000Z` |
| Nov 19 11:07 | Same-pin SMT-LIB rerun | Sample 100 ACCEPT / 86 PARTIAL / 20 UNKNOWN / 19 TIMEOUT; extended 74 / 134 / 70 / 7. Extended Farkas PENDING are nonlinear QF_NIA/QF_NRA; no matched-proof burn-down | `periodic-smtlib-20261119T173100Z`, prior `periodic-smtlib-20261119T121101Z` |
| Nov 19 05:16 | Same-pin SMT-LIB rerun | Sample 100 ACCEPT / 85 PARTIAL / 20 UNKNOWN / 20 TIMEOUT; extended 74 / 133 / 72 / 6. No matched-proof burn-down | `periodic-smtlib-20261119T121101Z`, prior `periodic-smtlib-20261119T060109Z` |
| Nov 19 02:42 | Expanded-definition candidate; 25 sample QF_LIA inputs | Baseline 17 ACCEPT / 1 PARTIAL / 2 TIMEOUT / 5 UNKNOWN; candidate 18 / 0 / 2 / 5. Median candidate/baseline `check_ms` ratio 1.0045; ring 2.174x slower. Proof hashes N/M | `qflia-sample-candidate-240329-02` |
| Nov 19 02:07 | Expanded paired-ITE definition replay; frozen ring | Baseline PARTIAL 4; candidate ACCEPT. Five pairs measured 2.240s → 5.086s (2.271x slower); no proof hash, no burn-down credit | `ring-expanded-def-20261119-paired.txt`, `ring-expanded-def-20261119-more-pairs.txt` |

## Burn-down: identical frozen proofs or evidence controls

| Dataset / proof set | Comparison | Rule | Before | Newly checked | Remaining |
| --- | --- | --- | ---: | ---: | ---: |
| fstar-build, Math.Exp query 7 | `245dd5c801e3` → `35ef16e3adce` | `arith/lp-monomial-interval` | 4 | 4 | 0 |
| fstar-build, Math.Exp query 7 | `35ef16e3adce` → `38203471c053` | `th-lemma` | 4 | 1 | 3 |
| fstar-build, CancellableInvariant query 2 | `35ef16e3adce` → `38203471c053` | `th-lemma` | 2 | 1 | 1 |
| smtlib-extended, 1 proof | `38203471c053` → `98ecf978a307` | `arith/farkas` | 5 | 2 | 3 |
| smtlib-extended, 1 proof | `38203471c053` → `98ecf978a307` | `th-lemma` | 7 | 2 | 5 |
| fstar-build, UInt128, 1 proof | `98ecf978a307` → `a0ca7df92173` | `th-lemma` | 199 | 63 | 136 |
| smtlib-sample, 11 proofs | `a0ca7df92173` → `79de3a41dcdb` | `apply-def` | 80 | 80 | 0 |
| smtlib-sample, 11 proofs | `79de3a41dcdb` → `2671dc150931` | `rewrite` | 43 | 7 | 36 |
| smtlib-sample, 11 proofs; array draft | `98ecf978a307` → `bac3ba06e1c1` | `th-lemma` | 681 | 681 | 0 |
| smtlib-sample, 11 proofs; array draft | `98ecf978a307` → `bac3ba06e1c1` | `rewrite` | 43 | 7 | 36 |
| QF_LIA frozen ring, 1 proof | Same checker `421406127c03`; lattice evidence erased → typed | `arith/lp-integer-lattice` | 18 | 18 | 0 |

The latest ring row is a same-document, same-checker control: only the 18
`ArithmeticLattice` payloads are erased in the control arm. It is not a
cross-version or full-cohort parity claim. Earlier rows are fixed subsets, not
whole-cohort burn-downs. Supporting evidence:
`files\real-product-checkout-math-exp-01.json`,
`files\real-division-checkout-math-exp-01.json`,
`files\real-division-checkout-cancellable-01.json`,
`files\multiple-zero-extended-02.json`, `files\int-quotient-uint128-01.json`,
`files\array-prefilter-weighted-01.json`, `files\conditional-weighted-01.json`,
`files\ite-add-weighted-02.json`.

## Current QF_LIA certificate result

Input SHA-256 `bd330dab1469304d3d149dc6062aa1ba00be734aee5bad0feaa27a10267dc8c5`;
frozen candidate proof-document SHA-256
`68279bde5cd0e7b0be1736c8cd8067fe850a2425509a4ffb071bb9a9438a5287`;
current checker SHA-256
`421406127c03c73e70ee0fab220a1761a19794fde134b35415878e8e10af87f8`.
The 1,196-node document contains 18 typed `ArithmeticLattice` entries. The
current checker resolves all 18; the remaining four PENDING are `intro-def`.
Erasing only those typed rules from the same document restores 18
`arith/lp-integer-lattice` PENDING, for 22 total. This establishes current
checker consumption of the frozen evidence, not a Legacy comparison, a
whole-cohort result, or a formal linear-time bound.

## Farkas certificate source findings

The native bridge retains the `farkas` and `bound` hint names but exposes both
coefficient lists through `proof_view.farkas`; `Z3NativeProof.native_rule`
maps either to `ArithmeticFarkas`. In `theory_lra.cpp`, bound propagation calls
`set_proof_params(m_bound, true)`, while the producer-side
`check_farkas_conflict` validation runs only for `m_farkas`. Evidence collection
also omits hard definition constraints and permanent LP facts without SAT-core
sources. These are possible evidence/replay gaps, not proof that the observed
nonlinear cases are malformed.

At checker pin `2671dc150931`, an exact frozen ring capture (document SHA-256
`23fedbd874befdb1d88fe310aeedec84d49c6c23bd05cb2088318f3fe665a474`, capture
binary SHA-256 `bede92c57096ead8fb1eee22eb3ccec56e3cf733cacd39cae575795977625079`)
has one native `bound` node (index 655) and four `farkas` nodes (460, 912, 846,
929); all five pass arithmetic replay. The producer summary for input SHA-256
`bd330dab1469304d3d149dc6062aa1ba00be734aee5bad0feaa27a10267dc8c5` and
document SHA-256
`c8fabf7675231bc5a27e9bd999c1507ce62d07a1b589157addf1f1ddbf181dcb` reports
18 integer-lattice and 19 linear LP entries. A later isolated instrumented
capture successfully traced that document: 33 `farkas` hints, each with
weights `1,1` and one premise, plus one `bound` hint (index 755) with six
premises and weights `1/2, 2, 16, 8, 1/2, 1/2, 1`; its conclusion is
`(not (<= v1 8))`.
The trace's same-capture diagnostic has no `arith/farkas` PENDING and reports
PARTIAL 46 from 18 `arith/lp-integer-lattice`, 4 `intro-def`, 4 `apply-def`,
and 20 `rewrite` obligations. This establishes that these observed arithmetic
hints are checked, not that all integer rounding/cut cases are covered. The
bound payload includes fractional multipliers, but this one successful
certificate is not evidence about other producer paths. The trace build used
`libz3.a` SHA-256
`32fcfb61c2797843bcede15be26622fc651433e287e1a432efb7b5ec1f636d4d`,
instrumented `theory_lra.cpp` SHA-256
`4da9870f0c3e28ed6d462fab0f54492620f06df8f5fd24d289cd4e746c731c02`,
and capture executable SHA-256
`d3c61e8abd8458e171a26bcaa30805fb7fc8386760e3e2f49df34a8684bc6388`.
The typed replay document (`68279b...`) has a different hash; these results
are not an identical-proof comparison. The 14 extended-cohort Farkas PENDING
have nonlinear QF_NIA/QF_NRA residuals; the three fstar-build cases lack
native payloads and proof hashes. Neither set is a controlled QF_LIA Farkas
failure. Evidence: `ring-native-hints-2671-01.json`,
`ring-producer-evidence-20261119T1626ET\summary-current.json`,
`ring-producer-trace-06.json`, `ring-producer-trace-06.stderr`,
`count-farkas-trace-2671-01.json`, `count-farkas-trace-2671-01.txt`,
`Z3Native.ml`, `Z3NativeProof.fst`, `src\smt\theory_lra.cpp`.

## Validation and remaining work

The current-checkout production checker was strictly verified, extracted, and
built; the focused `test_conditional_apply_def` control passed. Native
`test-z3 lp_evidence` passed, including integer-input binding and lattice
tightening controls. Evidence: `files\conditional-current-source-control-02.json`,
`files\lp-evidence-native-test-01.json`. The broader strict test closure remains
incomplete: its prior run timed out at
`Z3SortedRootDocumentTests.i3_certified`; no cause is established.

No full cohort has been rerun with checker `421406127c03`; the cohort tables
remain pinned to `2671dc150931`. Therefore no whole-cohort parity claim is
made. Continue with matched SMT-LIB sample/extended captures and QF_LIA
certificate provenance; retain N/M for timeouts and unobserved proof tails.
Six-hour SMT-LIB measurements remain scheduled; finite-field work remains
paused.
