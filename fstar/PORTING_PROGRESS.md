# Proof-checker pending dashboard

Updated: **2026-11-21T08:26:11-08:00**. The latest completed full SMT-LIB
capture below used a retained Definition-mode checker, not a fresh current-PR
build. Its binary, runtime, and input manifests are pinned, but proof-document
hashes were not retained; these counts are not matched-proof burn-down or a
Legacy comparison. The PR branch includes master through `a2fd7e6b1`.

**Old historical** means archived measurements from earlier Legacy-checker
captures, not a current checker binary. **Core** is the sort-indexed checker
without definition, NNF, or Skolem replay. **Definition** adds those replays to
Core; its interpretation maps each sort AST to a value type (`sort -> Type`)
and does not use `Z3ValueTheory.fst`.

PENDING is the weighted count of unresolved proof-rule obligations in completed
diagnostics. Missing diagnostics, timeout tails, and unobserved evidence are
N/M, never zero.

## Latest completed retained Definition capture

The checker was invoked with `--definition-replay`, SHA-256
`6eb16f0b187e27a5d4a5298f7c848869899edf7feb15895ab525325cb5099fbb`;
OCaml is pinned at 5.3.0 and Z3 is statically linked. The retained
`verified-sources.json` shows a passing verification run on Nov 15, but its
source/build provenance is not tied to this capture. The capture does not
record a source commit, build, or self-test result. Input hashes were verified
before each cohort; proof-document hashes are N/M.

| Dataset | Input manifest SHA-256 | Outcomes (selected) | Diagnostics | Diagnostic errors | Weighted PENDING |
| --- | --- | --- | ---: | ---: | ---: |
| smtlib-sample | `72cba03d2816fa47b8bb65d2dc03105b0781cb1243813846bbed1a789666cc44` | 83 ACCEPT, 103 PARTIAL, 20 UNKNOWN, 19 TIMEOUT (225) | 186 / 225 | 0 | 5,907 |
| smtlib-extended | `6f6ad04db40a0f49733329ce056e5d599328a4468133f987a56c2172ac08cb34` | 74 ACCEPT, 135 PARTIAL, 69 UNKNOWN, 7 TIMEOUT (285) | 209 / 285 | 0 | 31,516 |

| Rule | smtlib-sample PENDING | smtlib-extended PENDING |
| --- | ---: | ---: |
| `arith/farkas` | 0 | 33 |
| `arith/lp-monomial-interval` | 0 | 46 |
| `arith/lp-monomial-substitute` | 0 | 1 |
| `assumed:nlsat` | 0 | 146 |
| `apply-def` | 203 | 0 |
| `def-axiom` | 3 | 89 |
| `der` | 7 | 0 |
| `intro-def` | 272 | 147 |
| `quant-intro` | 42 | 83 |
| `rewrite` | 1,866 | 24,704 |
| `th-lemma` | 3,514 | 6,267 |

The rule totals cover only diagnostic-bearing cases; the remaining 39 sample
and 76 extended cases have N/M rule diagnostics. In sample, QF_LIA has 12
ACCEPT, 6 PARTIAL, 5 UNKNOWN, and 2 TIMEOUT; no `arith/farkas` PENDING appears
in the observed sample diagnostics. Extended has no QF_LIA inputs. Its 33
`arith/farkas` PENDING are in four QF_NIA and one QF_NRA inputs; their
diagnostic fingerprints contain nonlinear products, while raw proof documents
and weights are N/M. This is not evidence of a pure-linear producer defect.

## Prior completed Core cohort baseline

| Dataset | Checker pin and mode | Observed / selected | Case status / observed verdicts | Diagnostics / observed | Diagnostic errors | Weighted PENDING |
| --- | --- | ---: | --- | ---: | ---: | ---: |
| smtlib-sample | Core `b5e8cb065f06`, `--sorted-core` | 225 / 225 | 100 ACCEPT, 88 PARTIAL, 20 UNKNOWN, 17 TIMEOUT; 0 SAT/REJECT/crash/error/NOT_RUN | 188 / 225 | 0 | 4,020 |
| smtlib-extended | Core `b5e8cb065f06`, `--sorted-core` | 285 / 285 | 73 ACCEPT, 135 PARTIAL, 70 UNKNOWN, 7 TIMEOUT; 0 SAT/REJECT/crash/error/NOT_RUN | 208 / 285 | 0 | 31,262 |
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
| `arith/farkas` | 0 | 19 | 3 |
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
| `th-lemma` | 3,499 | 6,123 | 236 |

In this Core baseline, the sample QF_LIA slice contains 25 inputs: 17 ACCEPT,
2 PARTIAL, 1 TIMEOUT, and 5 UNKNOWN. Its two PARTIAL proofs have 52 PENDING
(34 `intro-def`, 18 `rewrite`) and no `arith/farkas` PENDING. The extended
selection has no QF_LIA inputs. The fstar-build timeout tails have N/M rule
diagnostics.

A separate pinned two-ring recapture used the sample inputs and the same
Definition checker/runtime pins. Its proof documents hash to
`000797dfef565ba1...` and `0ff8d8b000f3c6e4...`; the official full-document
diagnostics are PARTIAL 4 and PARTIAL 48, respectively, with 34 `intro-def`,
18 `rewrite`, and zero `arith/farkas` PENDING. These are not proven identical
to the cohort proofs because cohort proof hashes were not retained, so this is
not cohort burn-down. The helper's `BASE_FAILED_FARKAS` line is not native
producer evidence or the full-document result; the exact producer evidence
for these two documents is N/M. No controlled pure-QF_LIA Farkas failure is
established.

On those exact two documents, five alternating-order paired replays passed
each identical unmarshaled `(schema, document)` to the `Z3ProofDocument`
Legacy path and the sort-indexed path. Legacy ACCEPTed both documents 5/5;
sort-indexed remained PARTIAL 4 (`intro-def` 4) and PARTIAL 48 (`intro-def`
30, `rewrite` 18). Median check times were 0.028s vs 0.047s on the smaller
ring and 4.569s vs 0.775s on the larger ring, respectively; the sort-indexed
path was 5.9x slower on the latter. This comparison is pinned to checker
`b5e8cb065f06` / source commit `ce57c4095b54`, not the current PR-source
checker, and the recaptures are not proven identical to the cohort documents.
It is a fixed-proof Legacy control, not cohort burn-down or a current-PR
performance claim. These proofs prioritize `intro-def` and `rewrite` parity
work over a QF_LIA Farkas producer change.

A current-source dispatch-order control moved the expensive `integer_product`
fallback after the cheaper consequence checks. At PR HEAD `d52b5df5e`, checker
SHA-256 `1c7b0f432f8a27966e7b5e38eaa6c5a5d4631ee5b608ff7c797cccf606e1a6c8`,
`libz3.a` SHA-256
`6e4e68e11f8ef2a26c4e2f7e027b62655431dc60ba1e0802ebe1368564f355ea`, and
`libz3ml.a` SHA-256
`62ac403890a049d879e11422efbff9452cd7b849f6dc48a666e22405a354458c`, seven
alternating paired replays kept verdicts unchanged: Legacy accepted both;
sort-indexed remained PARTIAL 4 on proof 51 and ACCEPT on proof 52. Medians
were 361.337 ms vs. 57.157 ms and 28.988 ms vs. 3.514 ms, respectively; the
current checker is 6.32x and 8.25x slower than Legacy. The same-pin pre-commit
control (`e6f6e04e` → `1db30488`) isolates the dispatch change: proof 51 fell
from 2,258.694 ms to 367.665 ms (6.14x faster within the sort-indexed
checker), while proof 52 was unchanged at 28.873 ms vs. 29.093 ms. The proof
hashes are unchanged, but neither document is proven identical to a cohort
proof, so this is not cohort burn-down or parity.

An exact-node attribution pass over those same frozen documents retained
PARTIAL 4 and PARTIAL 48 (0.0296s and 4.6018s in this single diagnostic run).
For the four `intro-def` obligations in case 00 and 30 in case 01,
`DR.tautology`, `TN.tautology`, and `Z3UnifiedProof.logical_step` all returned
false on the sort-indexed diagnostic obligations. All 18 `rewrite` obligations
in case 01 passed `Z3UnifiedProof.relational_step`; the conditional-rewrite
predicate matched all 18, and one also matched arithmetic and
theory-normalization. `Z3SortedProof.check_node_cached` uses narrower typed
predicates rather than that general relational dispatch, making these
obligation-level results useful parity leads but not a proof of soundness in
the sort-indexed interpretation. In particular, the local `intro-def` results
do not explain the separate whole-document Legacy ACCEPT results, so they
cannot be read as Legacy rejecting those documents. This is pinned to the
same older checker/source as the recapture, not current PR source; it changes
no cohort count or burn-down. Exact output: session artifact
`qflia-legacy-rule-attribution-20261121T0217Z.json`.

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

The preceding extended cohort had 15 weighted `arith/farkas` PENDING. Pinned
traces covered 12 at that cohort's reported indices (AProVE QF_NIA: 3;
LassoRanker QF_NIA: 7; meti-tarski QF_NRA: 2). The AProVE document hash
`a223a1c83bccc50ec3a93a34dea312f2862f6091dece34995bdcac35607317bf` matches
a previously saved proof document for that input, but the latest cohort did
not retain document hashes, so identity to that cohort's document is
unverified. Original cohort document hashes are also unavailable for
LassoRanker and meti-tarski, so matching indices do not establish exact proof
identity there. The Nov 21 recapture also omitted proof hashes, so its 19
`arith/farkas` PENDING are not connected to these older traces and their
producer evidence is N/M. At the earlier traced PENDING nodes, AProVE and
LassoRanker leave bilinear or higher-degree products in the residual;
meti-tarski leaves cubic terms. The supplied weights therefore do not cancel
the original nonlinear formulas. These are QF_NIA/QF_NRA cases, not evidence
that the checker rejects a well-formed pure-linear QF_LIA certificate. To
check such nonlinear steps without search, the proof object must expose the
sound product
linearization/bounds or another separately checkable nonlinear lemma that
accounts for the residual; the current Farkas weights alone do not. In that
preceding cohort, VeryMax QF_NIA accounted for the other 3 PENDING; its
same-input recapture timed out without a proof document, so its
producer/checker evidence remains N/M.
The two sample QF_LIA PARTIAL documents have no Farkas PENDING, and the
extended selection has no QF_LIA inputs. The 40 `arith/lp-monomial-interval`
PENDING are a separate rule family. Current data does not implicate integer
rounding, cuts, or bound propagation in a pure QF_LIA Farkas failure, and does
not justify a producer change without a pinned QF_LIA counterexample.

A current-source paired replay of the same two frozen documents used PR HEAD
`a76daae251fa66ed61816e58333098b3e563358d`. The checker-only build strictly
verified 167 modules; the replay used `Z3SortedProof.cmx`
`bc87a39b7f3edc6f4d0b4e595a10d2e53a5c6b9eeda3341348c6c211193092de`,
`Z3ProofDocument.cmx`
`e749dc33be9f20305b2ff5055f15b58e8a74893c842ead460f55704c2082bf97`,
and helper `Qflia_sorted_rewrite_replay.ml`
`a1528c55da5e616819405227ff91fd30f64295dd82b364db5d8f2f694a3a3b29`;
OCaml is 5.3.0. Five alternating pairs gave proof 51 `PARTIAL 4`
(`intro-def` 4), median 0.036309s sorted vs. 0.017596s Legacy (2.06x
slower), and proof 52 `PARTIAL 30` (`intro-def` 30, no `rewrite` PENDING),
median 0.464344s vs. 0.830512s (1.79x faster). Legacy ACCEPTed both 5/5;
sort-indexed remains PARTIAL on both, so acceptance parity is not met. On
the identical proof-52 hash, weighted PENDING fell from 48 on checker
`818cab5a190f` to 30; the 18 cleared obligations were all `rewrite`. This is
fixed-proof evidence, not cohort burn-down or a source-only causal claim.

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

The current source already has explicit proof rules for integer tightening
and cuts; the earlier producer-gap table in
`ARITHMETIC_CERTIFICATE_REPORT.md` describes its separately pinned historical
snapshot. During LP bound propagation, `lar_solver::update_column_type_and_bound`
adds an `integer_tighten` derivation when integer rounding changes the bound.
`evidence.cpp` checks the exact floor/ceiling step and integer variables,
`lp_proof.cpp` serializes it with its premise, and the F* path accepts
`arith/lp-integer-tighten` only through `LP.check_tightening`. The Gomory and
integer-lattice producers likewise carry explicit evidence consumed by the
typed `ArithmeticGomory` and `ArithmeticLattice` checks. Focused native bridge
tests cover integer-tightening mutations and authentic Gomory cuts. This
confirms those producer/checker paths exist; it does not establish that the
two recaptured ring proofs used those steps, and does not justify a producer
change without a matched failing QF_LIA proof.

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
| QF_LIA frozen proof 52, fixed document | `818cab5a190f` → current-source `a76daae251fa` | all rules, weighted PENDING | 48 | 18 | 30 |
| smtlib-sample, 11 fixed proofs | `a0ca7df92173` → `79de3a41dcdb` | `apply-def` | 80 | 80 | 0 |
| smtlib-sample, 11 fixed proofs | `79de3a41dcdb` → `2671dc150931` | `rewrite` | 43 | 7 | 36 |
| smtlib-sample, two frozen QF_LIA ring proofs | Prior Definition control → current sorted Core | all rules, weighted PENDING | 44 | 40 | 4 |

These are fixed proof-set measurements; they do not imply whole-cohort parity.
The conditional apply-def row is a weighted rule diagnostic on 11 frozen
captures, not root parity: the candidate may certify an augmented proof. Its
separate CLI comparison has 1 ACCEPT and 10 PARTIAL for both candidate and
retained checkers, while Legacy accepts all 11. Paired timings on seven
captures (five repetitions per arm) give a median candidate/retained ratio of
1.0141, so there is no measured speedup; that timing applies only to candidate
`79de3a41dcdb`.

The two frozen QF_LIA proof documents (`51.proofs`,
`23fedbd874befdb1d88fe310aeedec84d49c6c23bd05cb2088318f3fe665a474`; and
`52.proofs`, `2680073a4cd2a7ab2317da9cef7e19f98660cb428611c2918b060525e3942896`)
were replayed five times per arm through Legacy, the earlier Definition
control, and the current sorted Core checker. Legacy ACCEPTed both 5/5. The
current Core ACCEPTed proof 52 and remained PARTIAL 4 on proof 51; the earlier
Definition control was PARTIAL 1 and 43, respectively. Proof 51's pending
count fell from 43 (`apply-def` 4, `intro-def` 4, `rewrite` 20, `th-lemma`
15) to four `intro-def`; proof 52's single `rewrite` PENDING was cleared.
This is a fixed-document comparison across different checker modes, not an
isolated source delta or cohort burn-down. The remaining proof-51 definitions
are conditional fresh-integer definitions, not Farkas or NNF obligations.

The earlier fixed-document checker pin is `2d086fe27e764778b335f6a3706228769ac81e35e7ab715c1cbc6a432601d875`;
the earlier Definition and Legacy pins are
`b8f6e0763cbc86b2474cf2ce6b39aa4fe538c5d0cf534422605c78a41ac8ada1` and
`9d590c3d12a50c49798a07a52a61d477971048d28a542845704e3f4a00d1b949`.
Five alternating paired median times were 2.421s sorted Core / 0.108s Legacy
and 0.0505s / 0.0225s, respectively. The current Core was also 1–4% slower
than the earlier Definition control. This records acceptance progress, not a
performance gain or Legacy parity. Exact outputs and all pins are in
`sample-sorted-core-matched-20261120.json`.

The current PR source was also strictly verified over its 167-module F*
checker-only closure, including explicit `Z3IndependentConditionalDefinition.fsti`,
and its focused native conditional-definition test passed. Source hashes match
the current checkout; the source-derived checker pin is `421406127c03`. The
same 11 frozen documents were replayed through its production
`Z3SortedProof.check_document_epsilon_diagnosed` path: 1 ACCEPT, 10 PARTIAL,
840 weighted PENDING, and zero `apply-def` PENDING in every document. Candidate
`79de` has 847 weighted PENDING on those captures; the retained checker has
927, including 80 `apply-def`. This confirms the rule-level result on the exact
PR source, but root outcomes still trail Legacy's 11/11 ACCEPT. The 1.0141
ratio belongs to the earlier candidate and cannot be transferred to this source.

A separate five-pair timing-only control used the current checker modules
(`Z3SortedProof.cmx` SHA-256 `bc87a39b7f3e`,
`Z3ProofDocument.cmx` SHA-256 `e749dc33be9f`) on 11 pinned proof files. Sorted
accepted 1/11 versus Legacy 11/11 and had 839 total PENDING; per-rule
diagnostics for this timing-only run are N/M. Summed per-capture medians were
89.838s sorted and 18.253s Legacy (4.92x), with sorted slower on 10/11.
All five pairs per proof completed below the 120s per-run cap.
Proof 63's hash differs from the earlier diagnostic capture, so the 839 total
is not a burn-down from its 840 PENDING and its rule counts must not be
transferred. No root parity or promotion claim follows. Full pins and timings
are in `current-source-sample-paired-20261121.json`.

Five alternating-order paired timing repetitions were run on checker
`818cab5a190f` for all 11 frozen captures. The sum of per-capture medians is
88.699s sorted vs. 26.251s Legacy (3.38x); sorted is slower on 10/11 captures.
Per-capture sorted / Legacy medians are 10: 2.118 / 1.512s, 20: 3.186 /
4.842s, 37: 15.625 / 0.283s, 40: 5.932 / 0.101s, 45: 10.162 / 1.934s,
49: 0.013 / 0.005s, 51: 2.230 / 0.059s, 59: 1.786 / 0.791s, 63: 23.841 /
16.023s, 69: 5.964 / 0.569s, and 90: 17.843 / 0.133s. These timings do not
alter the 11-capture verdicts or establish cohort performance. The control
uses the `818cab` checker, not current HEAD `1ef5585c7`; do not transfer the
result to current source. Proof hashes and the first seven medians are in
`conditional-current-source-control-03.json`; the remaining four captures'
five-pair results are in
`conditional-current-source-control-03-remaining-timing-20261121T0208Z.log`.

## Last 10 measured improvements and corrections

Times are PST. Corrections and incomparable captures are not checker gains;
overlapping candidate effects must not be added.

| Time (PST) | Change / scope | Measured effect | Evidence |
| --- | --- | --- | --- |
| Nov 21 08:26 | Pair current-source SMT-LIB sample timing controls | Five pairs per proof, all below the 120s cap. Sorted accepts 1/11 vs Legacy 11/11; summed medians are 89.838s vs 18.253s (4.92x), sorted slower on 10/11. Timing-only total is 839 PENDING with per-rule diagnostics N/M; proof 63 differs from the earlier diagnostic hash, so no burn-down or promotion | Source `a76daae251fa`, HEAD `38469af2f`; modules `bc87a39b7f3e`, `e749dc33be9f`; `current-source-sample-paired-20261121.json` |
| Nov 21 07:49 | Re-run paired QF_LIA ring controls on current PR source | On identical proof hashes, proof 52 falls 48 → 30 weighted PENDING, clearing all 18 `rewrite` obligations; both proofs still PARTIAL from `intro-def`. Five-pair medians: proof 51 sorted/Legacy 0.036309/0.017596s; proof 52 0.464344/0.830512s. Current sorted accepts 0/2 vs. Legacy 2/2; no parity or cohort claim | Proofs `000797dfef56`, `0ff8d8b000f3`; source `a76daae251fa`; `Z3SortedProof.cmx` `bc87a39b7f3e`; helper `a1528c55da5e` |
| Nov 21 05:17 | Complete retained Definition-mode SMT-LIB capture | Sample: 83/225 ACCEPT, 5,907 PENDING across 186 diagnostics; extended: 74/285 ACCEPT, 31,516 PENDING across 209 diagnostics. Not comparable to the prior Core run; no proof hashes, matched-proof burn-down, current-source, or Legacy-parity claim | `periodic-smtlib-20261121T120903Z/smtlib-sample/report.md`, `periodic-smtlib-20261121T120903Z/smtlib-extended/report.md`; checker `6eb16f0b187e`; manifests `72cba03d2816`, `6f6ad04db40a` |
| Nov 21 03:34 | Rebuild paired control at PR HEAD | Checker `d52b5df5e` retained Legacy ACCEPT 2/2 and sort-indexed ACCEPT 1/2; current medians are 6.32x and 8.25x slower than Legacy. Confirms the same-pin dispatch-order speedup; no cohort burn-down or parity | `pr-head-control-replay.log`; checker `1c7b0f43`; `libz3.a` `6e4e68e1`; fixed proof hashes unchanged |
| Nov 21 03:11 | Defer integer-product fallback behind cheaper consequence checks | On identical frozen proof 51, sort-indexed median fell 2,258.694 → 367.665 ms (6.14x within-checker speedup), but remained 6.39x slower than Legacy and PARTIAL 4. Proof 52 remained ACCEPT and unchanged against the preceding checker (29.093 ms; 8.24x slower than Legacy); no cohort burn-down or parity | `integer-product-frozen-replay.log` → `integer-product-reorder-frozen-replay.log`; checker `e6f6e04e` → `1db30488`; same proof hashes and native-library pins |
| Nov 20 23:32 | Complete cohort, timing, and strict array-checker controls | Sample remains 4,020 PENDING; extended falls 31,271 → 31,262 without retained proof hashes, not matched-proof burn-down. The 19 extended Farkas PENDING are untraced. Fixed-control medians total 88.699s sorted vs. 26.251s Legacy (3.38x), sorted slower on 10/11; this is not current-source performance. Strict F* verification passed for the 113-module array-document closure, including interfaces. Full `-RunTests` stopped at an unrelated finite-field VC before extraction/OCaml tests | `periodic-smtlib-20261121T060114Z`; `conditional-current-source-control-03.json`; remaining-timing log; F* output `1795246163690-copilot-tool-output-57984-e771cb18-86b4-4b05-8557-931ad6ef986c.txt` |
| Nov 20 22:25 | Correct SMT-LIB cohort mode attribution | No metric change: checker `b5e8cb065f06` was invoked with `--sorted-core`, so these captures are Core, not Definition. The active cycle uses the same Core mode; no burn-down or parity claim | `periodic-smtlib-20261121T060114Z/smtlib-sample/selection.json`; `periodic-smtlib-launcher.py` |
| Nov 20 21:17 | Replay current sorted Core on identical QF_LIA sample proofs | Current Core ACCEPTed 1/2 vs Legacy 2/2; against the prior Definition control, weighted PENDING fell 44 → 4 (proof 51: 43 → 4 `intro-def`; proof 52: 1 → 0 `rewrite`). Five paired medians: 2.421s vs. 0.108s and 0.0505s vs. 0.0225s (Core slower than Legacy); modes differ, so this is fixed-proof evidence, not cohort burn-down or a source-only delta | `sample-sorted-core-matched-20261120.json`; checker SHA-256 `2d086fe27e764778b335f6a3706228769ac81e35e7ab715c1cbc6a432601d875` |
| Nov 20 19:37 | Pair exact-current-source conditional apply-def controls | On seven of the 11 frozen captures, five alternating pairs: sum of per-capture medians 51.576s sorted vs. 19.240s Legacy (2.68x); sorted slower on all seven. Full 11-capture control remains 1 ACCEPT / 10 PARTIAL and 840 weighted PENDING vs. Legacy 11/11 ACCEPT; apply-def itself has zero PENDING. No cohort burn-down or promotion | `conditional-current-source-control-03.json`; checker SHA-256 `818cab5a190fe340fa7c75ade37b78ecfa7681878d6fdad0715656dab24aea13` |
| Nov 20 18:17 | Attribute exact QF_LIA ring obligations | PARTIAL 4 / 48 persisted at 0.0296s / 4.6018s in one diagnostic run. All 18 `rewrite` nodes pass Legacy local dispatch (`conditional` on all; one also arithmetic and theory-normalize); the 4 / 30 `intro-def` nodes fail the local DR/TN checks. This is obligation-level evidence only, not a Legacy document verdict, soundness proof, cohort burn-down, or current-PR result | `qflia-legacy-rule-attribution-20261121T0217Z.json`; `fstar/Z3UnifiedProof.fst:73-114`; `fstar/Z3SortedProof.fst:3209-3248` |

## Validation and active cadence

At merged HEAD `23a61f9c0`, `cmake --build build --target test-z3 --parallel
32` and the `opt_bounds`, `opt_pareto`, `proof_checker`, `lp_evidence`, and
`smt_context` test modules pass (5/5). At candidate HEAD `817035eb8`, the
Linux `shell` and `libz3_ocaml` were built and installed; the one-case checker
was relinked against pinned `libz3.a` and `libz3ml.a` and returned PARTIAL 22
on the AProVE input.
The current `Z3IndependentArrayDocument.fst` and its dependency closure were
strictly verified with warning errors `@1..999`: all 113 registered modules,
including the explicit `.fsti` interfaces, passed against installed Z3
5.4.2. The changed Python test passes `py_compile`. A full
`build_ocaml_checker.ps1 -RunTests` attempt rebuilt/installed Z3 and verified
185 production modules, then stopped at the unrelated
`Z3IndependentFiniteFieldPolynomial.fst` VC (assertion at line 638); extraction,
OCaml compilation, and native/CLI tests were not reached. Do not treat this as
a failure in the array changes, but retain the native test status as
unvalidated. No cohort candidate run is complete. The separate
interactive `--sorted-core` capture of CommMonoid and Math.Exp completed with
16 non-Farkas PENDING across 14 proof queries; it is not comparable to the
`2671dc150931` fstar-build cohort capture. The current-source apply-def
diagnostic replay remains 1 ACCEPT / 10 PARTIAL, 840 PENDING, with zero
`apply-def` PENDING; it is not a promotion result. The
separate paired timing control above uses current modules but a different proof
63 hash, so its 839 aggregate is not comparable burn-down and per-rule
diagnostics remain N/M. The older `818cab` paired timing control remains
historical only; see its timeline entry and
`conditional-current-source-control-03.json`.

The six-hour smtlib-sample/smtlib-extended measurement schedule remains active.
The current sorted Core has fixed-proof results above but has not been run
across the cohorts; keep its per-rule cohort PENDING as N/M until the
scheduled, pinned capture completes. Preserve timeout and missing-diagnostic
counts, serialize native runs using `files\current-corpus.lock`, and claim
burn-down only on identical fixed proofs.
