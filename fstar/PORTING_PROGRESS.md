# Proof-checker pending dashboard

Updated: **2026-11-23T08:31:02-08:00**.

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

## Latest scheduled retained-Definition cohort (fallback, not current-source coverage)

The 2026-11-23 05:17 PST run used retained checker SHA-256
`6eb16f0b187e27a5d4a5298f7c848869899edf7feb15895ab525325cb5099fbb`
with `--definition-replay`, OCaml 5.3.0, and static Z3 linkage. Both complete
non-field input manifests and all 510 input hashes were reverified:
sample `72cba03d2816fa47b8bb65d2dc03105b0781cb1243813846bbed1a789666cc44`,
extended `6f6ad04db40a0f49733329ce056e5d599328a4468133f987a56c2172ac08cb34`.
Artifacts are retained under `files\periodic-smtlib-20261123T120843Z`.

| Dataset | Outcomes | Diagnostic replays | Errors / mismatches | Weighted PENDING | Aggregate time / median |
| --- | --- | ---: | ---: | ---: | ---: |
| smtlib-sample | 83 ACCEPT, 103 PARTIAL, 0 REJECT, 0 SAT, 20 solver UNKNOWN, 19 TIMEOUT, 0 ERROR, 0 CRASH, 0 PROTOCOL_ERROR, 0 NOT_RUN (225) | 186 / 225 | 0 / 0 | 5,907 | 2,073.4s / 0.543s |
| smtlib-extended | 74 ACCEPT, 135 PARTIAL, 0 REJECT, 0 SAT, 69 solver UNKNOWN, 7 TIMEOUT, 0 ERROR, 0 CRASH, 0 PROTOCOL_ERROR, 0 NOT_RUN (285) | 209 / 285 | 0 / 0 | 31,500 | 1,756.4s / 0.546s |

Per-rule PENDING is limited to completed diagnostic replays; UNKNOWN and
TIMEOUT cases have no proof diagnostics and are not zero-PENDING:

| Rule | smtlib-sample | smtlib-extended |
| --- | ---: | ---: |
| `arith/farkas` | 0 | 36 |
| `arith/lp-monomial-interval` | 0 | 46 |
| `arith/lp-monomial-substitute` | 0 | 1 |
| `apply-def` | 203 | 0 |
| `assumed:nlsat` | 0 | 146 |
| `def-axiom` | 3 | 89 |
| `der` | 7 | 0 |
| `intro-def` | 272 | 138 |
| `quant-intro` | 42 | 83 |
| `rewrite` | 1,866 | 24,681 |
| `th-lemma` | 3,514 | 6,280 |

Against the prior scheduled run with the same checker and input hashes, sample
outcomes and per-rule PENDING reproduce exactly. Extended has one outcome
change: `QF_NIA/20170427-VeryMax/ITS/From_AProVE_2014__Count.jar-obl-10-2__terminationS_9_0.smt2`
returns PARTIAL instead of UNKNOWN, with 111 newly observed obligations
(16 `arith/farkas`, 59 `th-lemma`, 24 `rewrite`, 11 `intro-def`, 1
`assumed:nlsat`). Extended PENDING therefore changes from 31,389 to 31,500;
without matched proof-document hashes this is restored evidence, not
burn-down. All 186 and 209 diagnostic replays have zero errors or mismatches.
This retained binary predates current-source changes; no Legacy parity is
established.

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

## Last 10 updates (measurements and corrections)

Times are Pacific. A cohort comparison without identical proof-document hashes
is a coverage observation, not causal attribution or burn-down.

| Time | Change / measurement | Measured effect |
| --- | --- | --- |
| Nov 23 08:31 | Admit closed `asserted`/`mp` binder entries only as exact document equalities; replay a structurally reversed single-premise `symm` | On the same 11 frozen current-source Definition+Array proofs, acceptance stays 7/11 and PENDING drops 108→99, entirely removing proof 90's 9 `quant-intro` obligations (5 remain: 4 `intro-def`, 1 `def-axiom`). Aggregate/median are 181.549s / 11.138s versus 211.323s / 11.218s in the immediately prior run and 181.047s / 11.053s in the earlier matched run; one-pass timings are variable, so no performance claim. Legacy remains 11/11. Strict 219-module independent closure and isolated positive/negative replay tests pass; the full test suite is still blocked by unrelated finite-field/root-document test failures. No cohort run or parity. |
| Nov 23 05:17 | Rerun both pinned cohorts with the retained Definition checker (`6eb16f0b`) | Same checker and all input hashes. Sample reproduces 83/225 ACCEPT and 5,907 PENDING. Extended returns 74/285 ACCEPT and 31,500 PENDING; one prior UNKNOWN returns PARTIAL with 111 observed obligations, so the 31,389→31,500 change is not burn-down. Zero diagnostic errors/mismatches; current-source production build now verifies, but this run remains fallback evidence. |
| Nov 22 22:04 | Repeat both pinned cohorts with the retained fallback checker (`6eb16f0b`) | Sample reproduces exactly: 83/225 ACCEPT and 5,907 PENDING. Extended has 74/285 ACCEPT and 31,389 observed PENDING; one prior PARTIAL became UNKNOWN, leaving 112 obligations undiagnosed, so the 112-count difference is not burn-down. Zero diagnostic errors/mismatches. Current-source build failed before producing a checker; no coverage claim for the scalar-context changes. |
| Nov 22 20:05 | Add Real-gated conditional rewrite certificates and replay the 11 hash-pinned documents | Acceptance stays 7/11; PENDING 123→108, entirely from rewrite 20→5. Aggregate time 181.016s→181.047s and median 11.101s→11.053s: effectively flat, one pass. Strict 218-module checker closure and positive/negative controls pass; the broader native suite stops later at stale finite-field cache. Still 5.62x slower than Legacy; no cohort run or parity. |
| Nov 22 18:09 | Reuse definition diagnostics before the array fallback; replay all 11 hash-pinned proofs | 7/11 ACCEPT versus Legacy 11/11; 123 PENDING unchanged. Strict 219-module closure, `Z3SortedProofTests.fst` including conditional `ApplyDefinition` controls, and focused native regression pass. Aggregate time 272.614s→181.016s (-33.6%), median 15.872s→11.101s (-30.1%), faster 6/11; still 5.62x slower than paired Legacy. Single-pass evidence only; no cohort burn-down, parity, or Farkas finding. |
| Nov 22 17:15 | Repeat the retained Definition-mode checker on both pinned cohorts and diagnose every PARTIAL | Outcomes and per-rule PENDING reproduce: sample 110/225 ACCEPT, 3,836; extended 78/285 ACCEPT, 30,907. Diagnostics 77/77 and 126/126, zero errors/mismatches. QF_LIA sample: 19 ACCEPT, 5 UNKNOWN, 1 TIMEOUT, no PARTIAL. Timings 2,075.3s / 0.686s and 1,776.5s / 0.636s, slower than the prior repeat; repeatability only, no improvement, Farkas evidence, or matched-proof burn-down. |
| Nov 22 09:39 | Fix certified array diagnostics, add valid/wrong-branch `ApplyDefinition` controls, and replay the matched 11 | Strict 220-module F* closure and focused native array test pass. Same 7/11 ACCEPT and 123 PENDING; Legacy 11/11. 272.614s vs 21.787s Legacy (12.51x, slower on all 11); one-pass timing only. Diagnostic fix, no burn-down or Farkas gap. |
| Nov 22 08:36 | Pair current-source Definition+Array route against Legacy on the same 11 frozen proofs | Independent route 7/11 ACCEPT, 123 PENDING; Legacy 11/11. 213.781s vs retained Legacy 21.787s, slower on all 11. Focused array diagnostic test failed; route not promoted. No Farkas gap or cohort burn-down inferred. |
| Nov 22 07:48 | Replay the actual sorted epsilon path and the sorted array kernel on the same 11 frozen proofs | Epsilon: 1/11 ACCEPT, 831 PENDING, 94.14s vs Legacy 11/11 and 21.787s (9/11 slower). Array kernel: 4/11 ACCEPT, 151 PENDING, but 93.40s and not a native CLI route. No parity or Farkas-producer defect established. |
| Nov 22 07:37 | Replay the same 11 frozen proofs through the sorted array-kernel route; measure the array-lemma fast path | Array kernel 4/11 ACCEPT, 151 PENDING vs ordinary sorted core 1/11, 832 PENDING; Legacy 11/11. One-pass total 93.40s vs Legacy 21.787s, slower on 8/11. Fast-path delta is 1.1%, not conclusive; kernel route is not native CLI or cohort evidence. |

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

`build_independent_checker.py` also previously stopped in its standalone
test-only `Z3IndependentFiniteFieldPolynomial` extraction because that
module's cached `.checked` file was stale; the full standalone suite remains
unverified and finite-field work remains paused. Current-source paired Legacy
controls are measured on the 11-input fixed control above, where the
independent checker still trails Legacy; broader cohort parity remains
unestablished. Do not treat these cohort observations as matched-proof
burn-down or Legacy parity.
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
