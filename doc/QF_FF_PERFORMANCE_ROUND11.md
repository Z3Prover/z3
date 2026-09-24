# QF_FF performance round 11: sparse symbolic reducer selection

This round tests whether preferring shorter basis polynomials during symbolic
matrix construction reduces growth enough to add solves. The targeted Small
cohort shows no coverage improvement. The heuristic remains an opt-in experiment;
existing defaults and resource allowances are unchanged. The full cvc5 comparison
remains paused.

## Algorithm and justification

`ff.sparse_matrix_reducers` orders nonempty basis rows by number of terms, with
original basis index breaking ties. For each pending monomial it chooses the
first row in that order whose leading monomial divides the pending monomial.
The order is constructed once per batch. The heuristic uses no benchmark names,
input-family classification or special field values.

Multiplication by a fixed monomial is injective and preserves the number of
terms, so a shorter row supplies fewer candidate tail terms in that one step.
It need not minimize the eventual symbolic closure or elimination fill. Any
chosen row is still an exact monomial multiple of a retained basis row. Adding
it and using row operations preserves the ideal generated with the old basis
and input rows. The selected row carries its own premises and sugar metadata;
these must not be copied from the row that the original policy would have used.
The code comments state both the heuristic motivation and this justification.

Sorting, construction of the order and candidate checks consume the existing
local/shared work allowance. Comparator cancellation safely unwinds the local
index vector without changing the retained basis. The index allocation is
charged to symbolic storage when bounded matrix admission is active. Existing
column, row, polynomial, basis and cancellation limits remain in force.

The historical selection path retains its original work charges, including its
coarse accounting for divisibility scans. The new option explicitly charges
candidate tests as well as sorting. Work-counter comparisons therefore include
this conservative accounting change; wall-clock measurements remain separate.

The option works with expanded and referenced symbolic rows, tree and packed
coefficient layouts, and the support-mask filter. Probe engines inherit it.
Local spelling is `ff.sparse_matrix_reducers`; global SMT-LIB spelling is
`:smt.ff.sparse_matrix_reducers`. It defaults to false. This changes the existing
word-prime matrix backend; the arbitrary-precision scalar path is unaffected.
Conflict explanations remain distinct from v2 proof certificates. No CoCoA code
or dependency is introduced.

## Targeted algebra experiment

The archived 34-case Small selection is restored with source hashes checked.
Each configuration runs `ff-simplify` followed directly by `ff-solve`, with local
parameters, a ten-second external deadline, a 9.8-second internal timeout, four
workers and a 4 GiB cap. These are algebra diagnostics, not default-portfolio
scores. All 170 runs finish without infrastructure errors.

| Configuration | Solved / 34 | Work limits | Remaining stopping guards |
| --- | ---: | ---: | --- |
| Original selection, 2M work | 0 | 18 | 15 reducer-count; one polynomial-size |
| Sparse selection, 2M work | 0 | 19 | 14 reducer-count; one polynomial-size |
| Original + referenced/adaptive matrix, 8M | 1 | 25 | Four polynomial-size; two column; one row-growth; one symbolic-storage |
| Sparse + referenced/adaptive matrix, 8M | 1 | 25 | Four polynomial-size; two column; one row-growth; one symbolic-storage |
| Sparse + referenced/adaptive matrix, 32M | 1 | 6 | 14 active-basis; five pivot-storage; four polynomial-size; two column; one row-growth; one symbolic-storage |

The only solve is the same SAT case, `r_211_16_8_system16.smt2`. At eight million
work units, the sparse policy increases its charged work from 3,236,034 to
4,876,301. Its reported column statistic rises from 4,523 to 4,655. This complete
solve illustrates why locally shorter reducers do not guarantee a smaller
resulting matrix computation.

Across the 34 attempts at eight million units, symbolic-stage work rises from
13.75M to 30.88M, while numeric matrix work falls from 83.31M to 80.89M. These are
charges on attempted prefixes with potentially different stopping points, not
completed-work or CPU-time comparisons. The added selection cost does not yield
additional coverage. At 32M, active-basis and pivot-storage guards remain major
blockers.

## Correctness

All 19 regression commands pass. The new C++ fixture has a dense valid reducer,
a shorter valid reducer, and a tied alternative. It verifies deterministic ties,
chosen premises, sugar metadata and a reduction from four symbolic columns to
two in all four storage combinations. A separate scalar basis computation checks
ideal preservation in both directions and sufficiency of the reported premises.
The randomized basis suite now performs 1,024 configuration checks, including
all new matrix combinations, validating ideal membership, S-pair completeness
and provenance.

The Python suite checks local on/off options through ff-solve, ff-sat, QF_FF and
native SMT, observes use of the selection policy, and checks incremental model
recovery. For each coefficient layout it independently enumerates 225 small-field
systems and validates conflict cores, then runs 54 guarded mixed-theory cases
and 96 boundary-prime scalar/matrix checks.

The initial C++ fixture expected the unnormalized negative remainder; matrix
outputs are monic, so its expected value was corrected. That failed fixture
record is preserved separately. No algorithm change was needed for that failure.
The previous temporary cvc5 executable is no longer available: this round's
`test_qfff.py` runs Z3 against exhaustive enumeration without the optional cvc5
cross-check. No fresh cvc5 result is claimed.

## Default-portfolio screen and decision

The frozen round-10 default, final build with defaults, sparse policy alone,
and sparse policy with referenced/adaptive matrices run the same 113-input
screen at ten seconds per input, eight workers and a 4 GiB cap. Builds, tests
and targeted diagnostics finish before the screen starts. All 452 runs finish
without infrastructure failures. Every variant solves **53/113**: 40 UNSAT,
12 single-query SAT and one multi-query Example. All ten Examples solve; there
are no gains, losses or contradictory answer sequences.

| Configuration | Solved | Summed common-solve time | Change vs baseline |
| --- | ---: | ---: | ---: |
| Frozen round-10 default | 53 | 9.619 s | — |
| Final build, default settings | 53 | 9.638 s | +0.21% |
| Sparse selection | 53 | 9.702 s | +0.86% |
| Sparse + referenced/adaptive matrix | 53 | 9.598 s | −0.21% |

These differences indicate comparable screening performance, not a speedup.
All **48 screen SAT model replays** and **three direct-algebra SAT replays** pass
independent evaluation of original assertions. Multi-query Examples are checked
by their full answer sequences, rather than counted as single-query models.

**Decision:** keep the tested heuristic available for experiments but disabled
by default. Do not change work or storage allowances. No coverage gain warrants
a larger default-acceptance campaign. The evidence argues against assuming that
locally shorter reducers solve the remaining growth problem. A subsequent
structural experiment should address active-basis admission/compaction and its
storage cost, rather than relying only on this local term-count proxy. That
proposal has not been implemented or benchmarked in this round.

## Reproduction and evidence

Raw data is retained under `tests/finite_field/results/performance-round11`:
`diagnostic/` contains 170 direct-algebra runs; `screen/` contains 452 portfolio
runs and model validations; `regressions.json` and `diagnostic-models.json`
contain correctness records. Frozen binaries, restored input files, their
identities, configurations, source overlays and helper scripts are preserved.
The restored corpus matches the round-10 archive by SHA256. The final binaries
are retained in the evidence directory as well as temporary execution paths.

For a new direct-algebra run, from the repository root:

```sh
python3 tests/finite_field/diagnose_ff_limits.py \
  --manifest tests/finite_field/results/performance-round11/portable-small-selection.json \
  --binary tests/finite_field/results/performance-round11/binaries/candidate \
  --configs tests/finite_field/results/performance-round11/diagnostic-configs.json \
  --out /tmp/ff-sparse-reducers-new --timeout 10 --jobs 4
```

For the portfolio, use `benchmark_ff_optimizations.py` with the preserved
`portable-screen-selection.json` and `portable-screen-configs.json`, ten seconds
and eight workers. Portable manifests point at the retained local inputs; original
execution journals/configurations remain unchanged for provenance.

Binary SHA256 identities:

- Baseline: `571b96ff0a7dac9f40a5fa63c6fe1c3a0bd6215363f1a7abfa157412efd497d7`.
- Candidate/test build: `bd0ee41654e7e9f58c16eca364f0a0084e2eed63cdfeeafe7f1eb2c87c74caf8`.

The existing CAV draft remains tied to its frozen round-8 evidence. This round
neither changes an accepted default nor refreshes the cvc5 comparison.
