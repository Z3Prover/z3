# Proof-checker pending dashboard

Updated: **2026-11-15 19:00 PST**. Goal: eliminate pending proof obligations
and meet or beat the legacy checker on `fstar-build` and SMT-LIB.

**Definition** is the independent sort-indexed checker with definition,
NNF and Skolem replay; **Core** is the same checker without those extensions.
**Legacy** uses `Z3ValueTheory.fst`. Counts below are for Definition unless
stated otherwise.

## Latest per-rule PENDING

PENDING counts are weighted unresolved proof-rule obligations, not PARTIAL
proofs. Columns have different scopes and checker versions; do **not** add or
directly compare them. `N/M` means not measured, not zero.

| Rule | fstar-build: 583 inputs, full-run checker | sample: 103 PARTIAL inputs, older checker | sample: 11 frozen proofs, candidate | extended: full cohort |
| --- | ---: | ---: | ---: | ---: |
| `apply-def` | 0 | 203 | 80 | N/M |
| `arith/farkas` | 8 | 0 | 0 | N/M |
| `arith/lp-monomial-interval` | 5 | 0 | 0 | N/M |
| `assumed:nlsat` | 437 | 0 | 0 | N/M |
| `def-axiom` | 0 | 3 | 1 | N/M |
| `der` | 0 | 7 | 0 | N/M |
| `intro-def` | 0 | 272 | 113 | N/M |
| `nnf-neg` | 19 | 0 | 0 | N/M |
| `quant-intro` | 39 | 42 | 9 | N/M |
| `rewrite` | 14 | 1,866 | 43 | N/M |
| `sk` | 14 | 0 | 0 | N/M |
| `th-lemma` | 1,073 | 3,514 | 681 | N/M |
| **Total attributed** | **1,609** | **5,907** | **927** | **N/M** |

- **fstar-build:** last ABI-corrected full run, 08:57 PST, checker
  `d87b731ba6aa`; all 583 ledger entries and diagnostic logs matched. Counts
  include emitted prefixes from 45 timed-out sessions; remaining work in
  their unobserved tails is unknown. This is an older checker, not the current
  candidate. [Instance ledger](PORTING_INSTANCES.csv); evidence:
  session `files\fstar-pending-ledger-01.json`.
- **smtlib-sample:** current candidate, 11 identical frozen proofs, not all
  225 inputs. Its full-cohort per-rule totals have not been collected.
  The separate 103-input column is a source diagnostic rerun at 11:40 PST
  for the PARTIAL inputs from an earlier cycle, using checker `1147416d9a4c`;
  it is not directly comparable to the later full cycle or 11 frozen proofs.
  Evidence: session `files\large-real-sample-01.json`,
  `files\sample-partial-controls-01\results.jsonl`.
- **smtlib-extended:** the latest 285-input cycle recorded outcomes but did
  not collect per-rule diagnostics. Rule counts remain unmeasured.

## Burn-down: matched proofs

Compare only identical frozen proofs and checker versions within each row.
Positive gains mean fewer pending obligations; unmeasured cohorts are not
assumed unchanged.

| Date | Cohort | Rule | Before | After | Newly checked | Remaining |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| Nov 15 | fstar-build, 147 proofs | `rewrite` | 2 | 0 | 2 | 0 |
| Nov 15 | smtlib-sample, 1 ring proof | `th-lemma` | 15 | 0 | 15 | 0 |
| Nov 15 | smtlib-sample, 11 proofs | `rewrite` | 1,039 | 43 | 996 | 43 |
| Nov 15 | smtlib-sample, 11 proofs | all pending | 1,923 | 927 | 996 | 927 |
| Nov 15 | smtlib-sample, 11 proofs | all pending | 927 | 927 | 0 | 927 |

The fstar-build row compares the retained bounds checker with the large Real
equation candidate; two PARTIAL proofs became ACCEPT. The sample `rewrite`
row compares the preceding integer-cut checker with the bounds checker; the
later large-equation candidate left the sample's rule counts unchanged.
The ring `th-lemma` row compares the retained checker with integer-cut replay.
These are subset results, not full-cohort burn-downs. Evidence: session
`files\large-real-compare-02.json`, `files\bounds-sample-01.json`,
`files\large-real-sample-01.json`, `files\integer-cut-sample-03.json`.

## Latest benchmark outcomes

| Dataset / checker | Coverage | ACCEPT | PARTIAL | Solver UNKNOWN | TIMEOUT | REJECT / crash / error | NOT_RUN |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| fstar-build, full-run Definition | 583 inputs | 10,774 proofs | 382 proofs | 443 | 45 sessions | 0 | 0 inputs |
| fstar-build, frozen retained | 147 proofs | 144 | 3 | 0 | 0 | 0 | 0 |
| fstar-build, frozen candidate | 147 proofs | 146 | 1 | 0 | 0 | 0 | 0 |
| smtlib-sample, full-run Definition | 225 inputs | 84 | 102 | 20 | 19 | 0 | 0 |
| smtlib-extended, full-run Definition | 285 inputs | 74 | 135 | 69 | 7 | 0 | 0 |
| smtlib-sample, frozen legacy | 11 proofs | 11 | 0 | 0 | 0 | 0 | 0 |
| smtlib-sample, frozen candidate | 11 proofs | 1 | 10 | 0 | 0 | 0 | 0 |

Full fstar-build proof counts include timed-out session prefixes; its solver
UNKNOWN count is query-level. Full SMT-LIB runs finished Nov 15 at 17:05 PST
with checker `9c022c1f9f84`, before the current candidate. Legacy parity and
whole-corpus performance remain unestablished. Evidence: session
`files\periodic-smtlib-state.json`, `files\large-real-fstar-01.json`.

## Active / next

- **Collect current per-rule totals** for all three datasets using pinned
  inputs and checker, recording diagnostic coverage, timeouts and unobserved
  tails. Add comparable snapshots here; do not treat missing data as zero.
- **Burn down `th-lemma` and `rewrite`**, alternating fstar-build and sample;
  investigate unsupported Farkas, integer-cut and interval evidence at its
  producer before changing replay.
- **Candidate validation:** strict F* kernel and downstream verification,
  focused tests and SMT/Python/help smoke tests passed. Two known finite-field
  tests and one known uncovered-binder fixture were excluded from the checker
  build. Native `shell` / `test-z3` build and `/a` unit tests passed.
  Evidence: session `files\large-real-build-02.json`,
  `files\large-real-native-check-01.json`.
- **Six-hour SMT-LIB measurement** remains scheduled; finite-field work is
  paused. All native work uses the shared lock and a 30-second quiet pause.

## Touched files

| File | Change |
| --- | --- |
| `Z3IndependentRealBounds.fst`, `.fsti` | Verify Real equations |
| `Z3SortedProof.fst` | Replay large equations |
| `tools\test_independent_bounds.ml` | Test rewrite guards |
| `PORTING_INSTANCES.csv` | Full-run instance ledger |
| `PORTING_PROGRESS.md` | Pending burn-down dashboard |
