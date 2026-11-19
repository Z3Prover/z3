# Proof-checker pending dashboard

Updated: **2026-11-19T14:00:49-08:00**. Goal: eliminate pending proof obligations
and meet or beat the legacy checker on `fstar-build` and SMT-LIB.

**Definition** is the independent checker with definition, NNF and Skolem
replay. **Core** is the same sort-indexed checker without those extensions;
both use a value family indexed by sort, not `Z3ValueTheory.fst`.
**Legacy** uses `Z3ValueTheory.fst`. Counts are for Definition unless stated.

PENDING counts are weighted unresolved proof-rule obligations, not PARTIAL
proofs. Current observed counts appear below; **N/M** means not measured.
Per-rule counts for undiagnosed cases and unobserved timeout tails are N/M,
not zero.

<!-- BEGIN CURRENT PENDING -->
## Current SMT-LIB diagnostic collection

Updated `2026-11-19T11:10:50-08:00`; latest case `2026-11-19T11:07:40-08:00`; checker `2671dc150931` (`2671dc1509317d8d991f5b7a3f3f3ff41d5b19a043db95d7ca3ec27ffdafe0b9`). Counts below cover only successful diagnostic results; UNKNOWN, timeouts, errors and unrun cases may hide additional pending obligations.

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

State: **stages complete**. All 394 ACCEPT/PARTIAL cases have diagnostics; there were no diagnostic errors. Rule totals exclude UNKNOWN/TIMEOUT cases and their unobserved proof tails (N/M). Input manifests: sample `72cba03d2816fa47b8bb65d2dc03105b0781cb1243813846bbed1a789666cc44`, extended `6f6ad04db40a0f49733329ce056d5e599328a4468133f987a56c2172ac08cb34`. Per-case logs and input hashes: session `files\periodic-smtlib-20261119T173100Z`.
<!-- END CURRENT PENDING -->

<!-- BEGIN CURRENT FSTAR PENDING -->
## Current fstar-build diagnostic collection

Updated `2026-11-19T12:28:50-08:00`; completed capture checker `2671dc150931` (`2671dc1509317d8d991f5b7a3f3f3ff41d5b19a043db95d7ca3ec27ffdafe0b9`); corpus manifest `151fb3147a773d622252d6db5786802e11b62b19a61a2af83ed0ff6c89826187`.

| Observed / selected | Completed | TIMEOUT | Error / crash | NOT_RUN | Rule-diagnosed proof verdicts | Diagnostic errors |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 407 / 583 | 384 | 23 | 0 | 176 | 7,190 / 7,190 completed | 0 |

Observed proof verdicts: **8,411 ACCEPT / 209 PARTIAL / 0 UNKNOWN / 0 REJECT**; solver UNKNOWN queries: **256**. The 23 TIMEOUT sessions yielded 1,430 prefix verdicts (1,405 ACCEPT / 25 PARTIAL), but their rule diagnostics and proof tails are N/M. All 583 selected path/hash pairs match the pinned manifest.

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

Rule totals sum to 430 across completed diagnostics. The 1,430 timeout-prefix verdicts have no corresponding complete rule-diagnostic stream; their PENDING and unobserved tails are N/M. This is a coverage refresh, not a comparable burn-down from the earlier 253-input capture; proof hashes are N/M. Evidence, per-input hashes and logs: `files\fstar-build-incremental-20261119T193000Z`.

The three observed `arith/farkas` PENDING are two in `queries-FStar.Algebra.CommMonoid.smt2` and one in `queries-FStar.Math.Exp.smt2`; both input hashes match the manifest. Their obligations include product/division-shaped terms, and the same proof sessions contain `assumed:nlsat` PENDING. This excludes them as controlled QF_LIA cases, but does not show that the Farkas steps themselves are nonlinear or malformed: `Z3LinearArithmeticAst.linearize` can treat non-linear applications as opaque variables. The capture lacks those nodes' native hint/coefficient arrays and proof hashes, so exact certificate provenance is N/M and no producer defect is inferred. See `Z3NativeProof.fst`, `Z3Native.ml`, `theory_lra.cpp`, and `Z3LinearArithmeticAst.fst`.

<!-- END CURRENT FSTAR PENDING -->

## Last 10 incremental improvements and measurement corrections

Refresh this rolling timeline on every dashboard update; retain existing rows
when no new improvement has been measured. Label measurement corrections
explicitly and do not credit them as checker gains. Times are evidence-file
completion or last-modified times in PST. Counts are for the specified frozen
proofs, not whole cohorts; overlapping candidate gains must not be added.

| Time (PST) | Improvement and scope | Measured effect | Evidence in session `files\` |
| --- | --- | --- | --- |
| Nov 19 14:00 | QF_LIA LP producer-to-checker handoff audit; no checker gain | The pinned ring proof (input SHA-256 `bd330dab1469304d3d149dc6062aa1ba00be734aee5bad0feaa27a10267dc8c5`, document SHA-256 `c8fabf7675231bc5a27e9bd999c1507ce62d07a1b589157addf1f1ddbf181dcb`) has 1,196 nodes and 18 `lp-integer-lattice` producer nodes, each with `farkas=none`, one LP step-index parameter, and 4 or 6 formula premises. Both routes remain PARTIAL 22; no exact per-rule vector was captured, so the 18 nodes are not asserted to account for exactly 18 PENDING. `Z3Native.ml` preserves the name as `arith/lp-integer-lattice`; `Z3UnifiedProofSyntax.basic_rule_of_name` does not recognize it and `Z3NativeProof.native_rule` falls through to `Unverified` because there is no Farkas vector. The native checker therefore does not consume these explicit steps. No producer defect or matched-proof burn-down is established | `ring-producer-evidence-20261119T1626ET`, `Z3Native.ml`, `Z3NativeProof.fst`, `Z3UnifiedProofSyntax.fst` |
| Nov 19 13:22 | Cached-root experiment; matched-proof measurement correction, not a gain | Baseline modules `2671dc150931` and candidate `4a4d6e2ac0b9` checked the same 927-node QF_LIA ring proof document (SHA-256 `bb2a48d9f712c4278644ff531c088d17d53a6ae7fb45db64b359e65efe3fb1cc` in the paired timing run). Baseline has 4 `intro-def` PENDING; candidate has 43 (4 `apply-def`, 4 `intro-def`, 20 `rewrite`, 15 `th-lemma`). Five alternating pairs gave median candidate/baseline `check_ms` ratio 1.0061. A separate in-process capture gave both arms the same document hash (`1e9b4745f1c67b6eb8480d652208f946b5564581ac9676b92f25ef8ae80256f7`, 927 nodes); both `check` and `check_definition` returned PARTIAL 4 on baseline and PARTIAL 43 on candidate, so the regression is not confined to the definition entrypoint. No timing claim from this single route capture. Not promoted; no burn-down credit | `ring-matched-proof-capture-20261119T1550ET-order2`, `ring-inprocess-route-isolation-20261119T1612ET-order2` |
| Nov 19 12:28 | Farkas provenance triage on the completed `fstar-build` capture; no checker or producer change | Three observed PENDING: two in `Algebra.CommMonoid`, one in `Math.Exp`; pinned input hashes match. Their contexts contain product/division terms and `assumed:nlsat`, but the F* arithmetic linearizer may treat compound terms as opaque variables. Native hint/coefficient payloads and proof hashes are N/M; these are not QF_LIA certificate failures and do not establish a producer defect | `fstar-build-incremental-20261119T193000Z`, `Z3NativeProof.fst`, `Z3Native.ml`, `theory_lra.cpp`, `Z3LinearArithmeticAst.fst` |
| Nov 19 12:24 | Same-pin interactive `fstar-build` capture; coverage refresh, no checker change | All 583 path/input-hash pairs match the pinned selection. 384 sessions completed, 23 timed out and 176 were not run; completed diagnostics cover 7,190/7,190 proof verdicts with 430 weighted PENDING (139 `assumed:nlsat`, 236 `th-lemma`, 23 `quant-intro`, 10 `nnf-neg`, 10 `sk`, 8 `rewrite`, 3 `arith/farkas`, 1 `arith/lp-monomial-interval`). Observed verdicts include 8,411 ACCEPT / 209 PARTIAL; timeout-prefix rule diagnostics, tails and proof hashes are N/M. Not comparable to the prior capture; no burn-down credit | `fstar-build-incremental-20261119T193000Z` |
| Nov 19 11:07 | Scheduled same-pin, same-input SMT-LIB rerun; measurement correction, no checker change | All 510 path/input-hash pairs match the prior capture. Sample: 100 ACCEPT / 86 PARTIAL / 20 UNKNOWN / 19 TIMEOUT; extended: 74 ACCEPT / 134 PARTIAL / 70 UNKNOWN / 7 TIMEOUT. Sample QF_LIA remains 17 ACCEPT / 1 PARTIAL / 2 TIMEOUT / 5 UNKNOWN; its PARTIAL has four `intro-def` PENDING and no Farkas PENDING. The 14 extended Farkas PENDING are in four QF_NIA/QF_NRA cases whose residual formulas contain nonlinear products. Status and rule-vector drift with proof hashes N/M is not a matched-proof burn-down or evidence of a producer defect | `periodic-smtlib-20261119T173100Z`, prior `periodic-smtlib-20261119T121101Z` |
| Nov 19 05:16 | Scheduled same-pin, same-input SMT-LIB rerun; measurement correction, no checker change | All 510 input hashes matched. Sample: 100 ACCEPT / 85 PARTIAL / 20 UNKNOWN / 20 TIMEOUT; extended: 74 ACCEPT / 133 PARTIAL / 72 UNKNOWN / 6 TIMEOUT. Sample QF_LIA subset remains 17 ACCEPT / 1 PARTIAL / 2 TIMEOUT / 5 UNKNOWN (four `intro-def` PENDING); extended has no selected QF_LIA inputs. Current 14 Farkas PENDING are in QF_NIA/QF_NRA cases with nonlinear products. Diagnostic rule vectors changed, but proof hashes are N/M; no matched-proof burn-down or producer defect is established | `periodic-smtlib-20261119T121101Z`, prior `periodic-smtlib-20261119T060109Z` |
| Nov 19 02:42 | Expanded-definition candidate; alternating input-paired control on the 25 selected `smtlib-sample` QF_LIA inputs | Baseline `2671dc150931`: 17 ACCEPT / 1 PARTIAL / 2 TIMEOUT / 5 UNKNOWN, with 4 `intro-def` PENDING; candidate `240329979fbe`: 18 ACCEPT / 0 PARTIAL / 2 TIMEOUT / 5 UNKNOWN. Median candidate/baseline `check_ms` ratio 1.0045 across 18 timed pairs, but the ring was 2.174x slower (4.849s vs 2.231s). All input hashes and checker binaries were pinned; proof hash N/M, so no matched-proof burn-down or full-cohort claim | `files\qflia-sample-candidate-240329-02` |
| Nov 19 02:07 | Expanded paired-ITE `DefAxiom` replay; one frozen QF_LIA ring | Retained baseline `2671dc150931`: PARTIAL 4 (`intro-def`); candidate `240329979fbe`: ACCEPT 0. Both runs reported 933 proof nodes on the same input (SHA-256 `bd330dab1469304d3d149dc6062aa1ba00be734aee5bad0feaa27a10267dc8c5`). Five paired runs: median `check_ms` 2.240s → 5.086s (2.271x slower). Proof hash not captured; no matched-proof or cohort burn-down claim | `ring-expanded-def-20261119-paired.txt`, `ring-expanded-def-20261119-more-pairs.txt`, `ground-def-replay-verify-01`, `ground-def-replay-native-05` |
| Nov 18 23:10 | Scheduled same-pin, same-input SMT-LIB rerun; measurement correction, no checker change | All 510 input hashes matched; ACCEPT/PARTIAL counts unchanged, with one sample UNKNOWN → TIMEOUT. Two extended QF_NIA PARTIAL vectors and three proof-node counts changed; Farkas shift is QF_NIA, not QF_LIA. No matched-proof burn-down | `periodic-smtlib-20261119T060109Z`, prior `periodic-smtlib-20261118T235842Z` |
| Nov 18 17:44 | fstar-build aggregation correction, current pin; no checker change | 359 raw rows → 253 distinct inputs; excluded 106 repeated paths. Duplicate hashes/verdicts match, but proof counts differ in 103 rows and rule vectors in 5; no burn-down credit | `current-fstar-pending-2671-01`, `current-fstar-pending-2671-05`, `current-fstar-pending-2671-06` |
Root certification may discharge obligations without independently
certifying each original entry. Evidence files contain checker and proof pins.

## Burn-down: identical frozen proofs

| Dataset | Checker SHA-256 prefixes | Rule | Before | Newly checked | Remaining |
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

These are subset results, not full-cohort burn-downs. Evidence: session
`files\real-product-checkout-math-exp-01.json`,
`files\real-division-checkout-math-exp-01.json`,
`files\real-division-checkout-cancellable-01.json`,
`files\multiple-zero-extended-02.json`, `files\int-quotient-uint128-01.json`,
`files\array-prefilter-weighted-01.json`, `files\conditional-weighted-01.json`,
`files\ite-add-weighted-02.json`.

## Matched acceptance and timing

| Dataset | Checker | Proofs | ACCEPT | PARTIAL |
| --- | --- | ---: | ---: | ---: |
| fstar-build | retained `38203471c053` | 147 | 146 | 1 |
| fstar-build | multi-zero `98ecf978a307` | 147 | 146 | 1 |
| smtlib-sample | legacy | 11 | 11 | 0 |
| smtlib-sample | retained `38203471c053` | 11 | 1 | 10 |
| smtlib-sample | multi-zero `98ecf978a307` | 11 | 1 | 10 |
| smtlib-sample | array draft `bac3ba06e1c1` | 11 | 5 | 6 |
| smtlib-sample | ITE/add `2671dc150931` | 11 | 1 | 10 |

Five alternating pairs gave multi-zero/retained median time ratios of **1.030**
on the extended proof and **1.004** over five sample proofs. These subsets do
not establish whole-cohort parity or speedup. Evidence: session
`files\multiple-zero-fstar-02.json`, `files\multiple-zero-sample-02.json`,
`files\multiple-zero-extended-timing-01.json`,
`files\multiple-zero-sample-timing-01.json`.

The quotient replay preserved verdicts and rule counts on 11 sample
proofs. Five alternating pairs on five of those proofs gave a median per-proof
candidate/retained time ratio of **1.006**; five paired UInt128 runs gave
**1.007**. Evidence: `files\int-quotient-sample-01.json`,
`files\int-quotient-sample-timing-02.json`,
`files\int-quotient-uint128-timing-01.json`.

The filtered array draft's overall median paired ratio was **1.009** over five
sample proofs, but two promoted proofs slowed by **1.66x** and **1.94x**.
It is not retained. Evidence: `files\array-prefilter-sample-timing-01.json`.

Conditional definition replay preserved verdicts on 11 sample proofs and
eliminated their 80 weighted `apply-def` obligations. Five alternating pairs
on seven frozen sample proofs gave a median per-proof candidate/retained time
ratio of **1.014**; this does not establish cohort performance. Evidence:
`files\conditional-weighted-01.json`, `files\conditional-sample-timing-01.json`.

Int ITE/add factoring eliminated seven weighted `rewrite` obligations on the
frozen QF_LIA ring proof at retained pin `2671dc150931`, which remains PARTIAL
with four `intro-def` obligations there. The expanded-definition candidate
now accepts that input, but this is a separate single-proof result and is
slower; it does not change the pinned cohort totals. Five alternating pairs on
seven frozen sample proofs gave a median candidate/retained time ratio of
**0.982** (ring **0.951**). Evidence:
`files\ite-add-sample-02.json`, `files\ite-add-weighted-02.json`,
`files\ite-add-sample-timing-02.json`.

## Current work

The multi-zero replay proves zero factors and resulting product bounds before
checking a linear contradiction; strict downstream F* verification, checkout
native tests and SMT/Python/help smoke checks passed. Scope tests passed with
seven Windows skips. Evidence: session `files\multiple-zero-downstream-01.json`,
`files\multiple-zero-checkout-build-01.json`, `files\multiple-zero-checkout-smoke-01.json`.

An additional bounded-integers `fstar-build` diagnostic covered 10 queries:
the replay reports 9 ACCEPT / 1 PARTIAL and preserves three `th-lemma`
PENDING fingerprints. Proof-node counts differ on queries 7-10 and the proof
document hash is N/M, so this does not establish a matched-proof burn-down or
change the aggregate 158/583 cohort counts. Evidence:
`files\fstar-build-bounded-integers-2671-03.json`.

The expanded ground-definition candidate adds dependency-aware expansion of
ground `DefinitionIntroduction` entries before sorted proof replay, including
the paired ITE branch clauses in the frozen ring. Strict F* verification
passed for the changed modules and dependent root/regression modules with F*
2026.10.25 and Z3 5.4.1; the native checker build and focused ground-definition
regressions also passed. On the frozen ring input, baseline `2671dc150931`
reports PARTIAL 4 (`intro-def`), while candidate
`240329979fbea18523b0f0ce9ba57e46ad2d047f294014e36d96e1702c41011d` accepts
with 933 proof nodes. Five paired runs measured median `check_ms` of 2,239.596
for baseline and 5,086.373 for candidate (2.271x slower). The proof hash was
not captured by the CLI, so this is not a matched-proof burn-down or a
cohort-wide result; the cohort tables remain pinned to `2671dc150931`. An
alternating input-paired control over the 25 selected sample QF_LIA cases
returned baseline 17 ACCEPT / 1 PARTIAL / 2 TIMEOUT / 5 UNKNOWN and candidate
18 ACCEPT / 0 PARTIAL / 2 TIMEOUT / 5 UNKNOWN. Median candidate/baseline
`check_ms` ratio was 1.0045 across 18 timed pairs, while the ring was 2.174x
slower in that pair; input and checker hashes are recorded, but proof hashes
are N/M. This is not a matched-proof burn-down or a full-cohort comparison.
The separate `Z3UnifiedProof.fst` array-lemma experiment remains unverified after
an 1800-second timeout and is not included in this candidate. Evidence:
`files\ground-def-replay-verify-01`, `files\ground-def-replay-native-05`,
`files\current-unified-fstar-verification-05.json`,
`files\ring-expanded-def-20261119-paired.txt`,
`files\ring-expanded-def-20261119-more-pairs.txt`,
`files\qflia-sample-candidate-240329-02`.

The separate cached-root candidate was tested on a captured ring proof
document, not merely the same SMT input: the paired run had SHA-256
`bb2a48d9f712c4278644ff531c088d17d53a6ae7fb45db64b359e65efe3fb1cc`, 927
proof nodes. Retained modules `2671dc150931` report four `intro-def` PENDING;
candidate modules `4a4d6e2ac0b9` report 43 (4 `apply-def`, 4 `intro-def`, 20
`rewrite`, 15 `th-lemma`). Five alternating pairs yielded a median
candidate/baseline checker-time ratio of 1.0061. A second in-process
route-isolation capture had matching baseline/candidate proof-document hashes
(`1e9b4745f1c67b6eb8480d652208f946b5564581ac9676b92f25ef8ae80256f7`, 927
nodes) and showed both `check` and `check_definition` return PARTIAL 4 on the
baseline and PARTIAL 43 on the candidate. The regression is therefore present
on both routes; the single route-isolation run is not timing evidence. The
candidate is not promoted, does not alter the cohort pin, and receives no
burn-down credit. Evidence: sessions
`files\ring-matched-proof-capture-20261119T1550ET-order2` and
`files\ring-inprocess-route-isolation-20261119T1612ET-order2`.

The pre-existing, unstaged `src/ast/proofs/lp_proof.cpp` change was built into
Z3 hash `2a744d6369f337becd8a9a0dc45dc4b099b7664b`; focused
`test-z3 lp_evidence` passed. On the pinned QF_LIA ring input, a new in-process
proof capture had 1,196 nodes and explicit `lp-linear` (19),
`lp-integer-lattice` (18), `lp-input` (199) and `lp-context` (19) nodes.
The output hash differs from the prior native proof, so this is not a
matched-proof burn-down or timing comparison. Both routes return PARTIAL 22;
the trace reports zero pending `th-lemma`, while `Z3NativeProof.fst` only
decodes `arith/lp-gomory` and `Z3UnifiedProofSyntax.fst` has no integer-lattice
rule. The new explicit integer-rounding nodes therefore remain unconsumed;
their complete per-rule diagnostic vector is N/M. Do not attribute this
checker gap to malformed producer evidence. The unstaged producer and test
changes were left untouched. Evidence:
`files\ring-producer-evidence-20261119T1626ET`, `src/ast/proofs/lp_proof.cpp`,
`src/test/lp_evidence.cpp`.

The producer-to-checker trace confirms that all 18 emitted
`lp-integer-lattice` steps have no Farkas coefficient list: each carries a
single step index and four or six actual formula premises. `Z3Native.ml`
preserves the hint as `arith/lp-integer-lattice`, but
`Z3UnifiedProofSyntax.basic_rule_of_name` does not recognize it and
`Z3NativeProof.native_rule` returns `Unverified` when no Farkas vector is
present. The proof
has 22 total PARTIAL obligations, but without checker diagnostics the exact
per-rule contribution remains N/M. This is a verified checker-coverage gap,
not evidence of malformed producer data. Capture log:
`files\ring-producer-evidence-20261119T1626ET\capture-current.stderr`.

On the pinned `2671dc150931` extended cohort, the 15 weighted `arith/farkas`
PENDING occur in five QF_NIA/QF_NRA inputs (13 and 2 respectively); the
sample cohort has zero. Same-timeout traces recaptured four inputs: 13 weighted
PENDING across 10 nodes, all with native `arith bound` hints. The 10-second
Count capture timed out, but a 60-second same-input control completed with a
different 5,142-entry proof: `PARTIAL 172` with Farkas PENDING at 4159 and
4160, versus the 10-second baseline's `PARTIAL 74` and index 2409. This is not
a matched-proof comparison. Both new nodes carry 32 rational weights for 31
visible premises plus the negated conclusion. F* preparation succeeds, but
the weighted sums leave 10 and 9 residual monomials, including nonlinear
products; they are not plain-linear certificates over the visible premises.
Evidence: `count-farkas-trace-2671-01.json` and
`count-farkas-trace-2671-01.txt`.

The native bridge recognizes `farkas` and `bound` as different parameter-1
hints in `fstar/ocaml_runtime/Z3Native.ml`, but exposes both coefficient lists
as `proof_view.farkas`; `Z3NativeProof.native_rule` maps either to
`ArithmeticFarkas`. The hint distinction is lost before checker dispatch, so
no bound-specific integer-rounding or cut check can be selected there. In
`src/smt/theory_lra.cpp`, LP bound propagation calls
`set_proof_params(m_bound, true)`, which emits explanation weights and a unit
consequent coefficient. The producer's `check_farkas_conflict` validation is
gated to `m_farkas`, not `m_bound`; moreover, `set_evidence` omits hard
definition constraints and constraints with no SAT-core source. These facts
make a bound-evidence/replay gap plausible, but do not show that skipped
constraints occur in the Count nodes. Their nonlinear residuals mean the
visible payload is not a complete plain-linear certificate. On the exact
frozen QF_LIA ring proof `23fedbd874be`, a same-process trace matches the
frozen proof hash and finds five arithmetic nodes: native `arith bound` at
655 and native `arith farkas` at 460, 912, 846 and 929. All five pass the
current checker after both hint kinds are mapped to `ArithmeticFarkas`; the
bound node is a valid linear certificate in this proof, not an
integer-rounding failure. Recover full provenance for the separate nonlinear
Count nodes before changing the Farkas checker or producer.
Evidence: `ring-native-hints-2671-01.json`,
`ring-native-hints-2671-01.stderr` and
`ring-definitions-trace-2671-03.json`.

On the frozen QF_LIA ring proof `23fedbd874be`, all five arithmetic steps are
accepted by Legacy and both independent-checker arms at retained pin
`2671dc150931`; its four remaining `intro-def` PENDING define nullary integer
`z3name!` symbols through paired ITE branch clauses. Two definitions have
cross-entry dependencies, including `z3name!3` referring to `z3name!2` before
the latter's definition entry. The expanded candidate collects and validates
the dependent ground definitions, expands the entries, and checks the
premise-free paired-ITE `DefAxiom` under sorted semantics. It accepts this
single input; the five paired measurements show a 2.271x checker-time
regression, and the proof hash was not captured, so this does not establish a
matched-proof or cohort-wide gain. This is a checker-coverage result, not
evidence of faulty Farkas generation. Evidence: session
`files\periodic-smtlib-20261118T170450Z`,
`files\ite-add-sample-02.json`, `files\extended-farkas-capture-2671-05.json`,
`files\extended-farkas-capture-2671-06.json`,
`files\ring-definitions-trace-2671-03.json`,
`files\ring-expanded-def-20261119-paired.txt`,
`files\ring-expanded-def-20261119-more-pairs.txt`.

The QF_LIA slice of the retained-pin SMT-LIB sample capture contains 25
selected inputs:
17 ACCEPT, one PARTIAL, two TIMEOUT and five UNKNOWN. The only PARTIAL is the
ring proof above, with four `intro-def` PENDING; its five arithmetic nodes
(one native bound and four native Farkas) are accepted. The extended capture
contains no selected QF_LIA inputs, so it provides no QF_LIA comparison. Two
definitions have cross-entry dependencies,
including `z3name!3` referring to `z3name!2` before the latter's definition
entry. A sound replay therefore needs freshness checks and dependency-aware
interpretation of all four constants; recognizing one paired-ITE formula in
isolation would not close the proof. Evidence: session
`files\periodic-smtlib-20261118T170450Z`,
`files\ring-definitions-trace-2671-03.json`.

An experimental integer-input binding bridge passed LP unit tests, but on the
same QF_LIA ring input it changed the generated proof and increased root
PENDING from 15 to 33, adding 18 `arith/lp-integer-lattice` obligations.
An isolated lattice replay draft verified 173 F* modules and passed positive and
negative controls for all 18 nodes. On its pinned experimental proof, the
same checker reported 18 → 0 lattice PENDING when only the lattice payloads
were restored; four `intro-def` obligations remain. Eleven frozen sample
proofs had no verdict regressions and identical weighted counts; seven-proof paired timing
had median candidate/retained ratio 0.998. The retained producer's original
ring proof also has four pending obligations, so this is not yet a measured
end-to-end improvement. The bridge and replay remain unretained; linear-time
checking has not been established. Evidence:
`files\lp-binding-ring-compare-01.json`,
`files\lattice-integration-verification-01.json`,
`files\lattice-integration-controls-03.json`,
`files\lattice-same-producer-01.json`,
`files\lattice-sample-weighted-02.json`,
`files\lattice-sample-timing-01.json`.

Six-hour SMT-LIB measurements remain scheduled; finite-field work is paused.
Timeout tails, missing diagnostics and unmeasured candidate cohorts remain N/M.
The quotient replay passed strict downstream verification, checkout native
controls, SMT/Python/help smoke checks and scope tests (seven Windows skips).
Evidence: `files\int-quotient-downstream-02.json`,
`files\int-quotient-checkout-controls-01.json`,
`files\int-quotient-checkout-smoke-01.json`,
`files\int-quotient-scope-tests-02.json`. The diagnostic tables specify their
checker pins; matched acceptance and timings cover only frozen subsets.
Conditional replay also passed strict downstream verification, checkout native
controls, SMT/Python/help smoke checks and scope tests (seven skipped).
Evidence: `files\conditional-downstream-02.json`,
`files\conditional-checkout-controls-01.json`,
`files\conditional-checkout-smoke-01.json`,
`files\conditional-scope-tests-01.json`.
A matched-proof comparison of pre-conditional baseline `a0ca7df92173` against
current checker `2671dc150931` passed on 11 identical sample proofs:
`apply-def` PENDING 80 → 0 and `rewrite` 43 → 36, with zero verdict
regressions or unobserved proofs. These are combined confirmations of the
conditional and ITE/add changes, not an additional cohort gain. Evidence:
session `files\conditional-current-baseline-2671-01.json`.
