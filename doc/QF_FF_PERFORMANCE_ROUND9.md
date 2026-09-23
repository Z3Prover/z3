# QF_FF performance round 9: matrix storage and exact resource attribution

This round keeps the round-8 default policy. A new opt-in representation greatly
reduces symbolic-storage failures on the 34 historical Small gaps, but adds no
solves. Raising the work allowance exposes further basis and elimination limits;
it does not establish a default improvement. The full cvc5 comparison remains
paused. These experiments compare Z3 configurations, not current cvc5 releases.

## What actually stops the algebra

The new statistics distinguish local work from shared cancellation, polynomial
term count from monomial degree, active basis size from historical basis slots,
and five matrix guards: reducer count, symbolic storage, column count, row growth,
and pivot storage. Existing aggregate counters remain available. The diagnostic
change preserves the guards, their thresholds, and work/cancellation semantics.

Matrix peaks separately report columns, reducers, row terms, estimated symbolic
bytes, coefficient bytes, and premise bytes. They are per-engine estimates, not
process RSS. Wrappers may sum peaks across independent attempts, so an aggregated
peak is not necessarily the maximum simultaneously live storage. Tree entries use
the existing 48-byte estimate; packed coefficients use 16 bytes per capacity
entry. Symbolic accounting conservatively includes monomial copies and headers.

The initial algebra-only diagnostic covers all 51 historical cvc5-union-only
cases, including two now solved by the round-8 default. The 34 Small cases all
stop before root completion. With the ordinary two-million work allowance,
18 hit local work, 15 hit the 1,024-reducer guard, and one hits polynomial size.
None of those initial matrix failures is a pivot/provenance-storage failure.
With adaptive matrix admission and eight million work units, 21 hit the 16 MiB
symbolic-storage allowance, 11 hit work, one hits polynomial size, and one is SAT.

## Referenced symbolic reducers

`ff.lazy_matrix` is a new **false-by-default** experiment. A symbolic reducer is
stored as a basis index and a monomial multiplier. The immutable basis remains
alive throughout the batch. Multiplication by a fixed monomial is injective and
preserves monomial order, so the descriptor denotes exactly the expanded row;
no terms combine or cancel. Coefficients, premise sets, sugar metadata, reducer
selection, and row order are preserved when the row reaches elimination.

This avoids keeping expanded polynomial trees and copied premise sets for every
reducer. Both existing tree and packed coefficient layouts can consume the
references. Descriptor capacity, owned factors, transient shifted monomials,
and discovery/index storage are charged to the symbolic allowance. Recomputing
shifted column indices consumes additional work. Column, degree, polynomial,
row-growth, pivot-storage and cancellation guards remain active. The 1,024
reducer cap remains unless `ff.adaptive_matrix` is also enabled.

The option is available locally on the solver/tactics and globally as
`:smt.ff.lazy_matrix`. It changes representation in the existing word-prime
matrix backend, not the arbitrary-precision scalar path. It introduces no CoCoA
dependency. Premise tracking remains conflict explanation; proof reconstruction
and polynomial-combination certificates remain v2.

## Targeted measurements

All entries below use `ff-simplify` followed directly by `ff-solve`, with local
parameters. They do not include the default SAT/BV fallback. Each run has a
4 GiB memory cap. The three-second diagnostic uses a 2.8-second internal timeout;
the ten-second follow-up uses 9.8 seconds internally. Four workers run in parallel.

| Representation and admission | Work allowance | Deadline | Small solved / 34 |
| --- | ---: | ---: | ---: |
| Original, fixed reducer count | 2M | 3 s | 0 |
| Expanded reducers, adaptive storage | 8M | 3 s | 1 |
| Referenced reducers, adaptive storage | 2M | 3 s | 0 |
| Referenced reducers, adaptive storage | 8M | 3 s | 1 |
| Expanded reducers, packed rows, adaptive storage | 8M | 10 s | 0 |
| Referenced reducers, packed rows, adaptive storage | 8M | 10 s | 0 |
| Referenced reducers, adaptive storage | 32M | 10 s | 1 |
| Referenced reducers, packed rows, adaptive storage | 32M | 10 s | 1 |

The only solved case is `r_211_16_8_system16.smt2`, already recovered by increasing
the work allowance in round 8. At eight million work units, referenced reducers
reduce symbolic-storage blockers from **21 to one**, but local-work blockers rise
from 11 to 25. The remaining failures are four polynomial-size limits, two column
limits, and one row-growth limit. Removing retained expanded rows therefore
addresses a real storage cost without yet improving coverage.

At 32 million work units, the tree layout reaches the active-basis cap on 13
cases and pivot storage on four; seven still hit work. The packed layout instead
hits work on 24 cases and the active-basis cap on two. Merely increasing budgets
moves failures between stages. The next candidate should reduce basis growth,
redundant reduction work, or elimination fill, with separate accounting for each
phase. The present data do not establish which algorithmic change will succeed.

Development and builds overlapped some targeted diagnostics. Their results and
resource classifications support the analysis above, but their wall times do
not support a performance-equivalence claim. The broader screen below was run
separately after builds and regression commands completed.

## Correctness

The final build passes the existing 16 regression commands and a new matrix
suite. The latter independently enumerates 225 small-field systems and validates
returned conflict cores for each of the two coefficient layouts; it also checks
54 guarded mixed-theory cases and 96 scalar/batched boundary-prime cases per
layout. Local options are checked through `ff-solve`, `ff-sat`, QF_FF, and native
SMT, with observed referenced-reducer use and successful push/pop model recovery.

C++ tests compare eager/reference output polynomials, sugar values and premises,
check scalar ideal membership, and require lower estimated symbolic storage.
They exercise admission past 1,024 reducers in both layouts and representations,
and subsequent batch reuse. The randomized basis suite performs 640 configuration
checks across four primes, including reference layouts, checking ideal equality,
S-pair reduction, and conflict premises. Focused diagnostics test each unchanged
resource guard, shared cancellation, and provenance storage.

The first version of the new interface test incorrectly expected algebra-only
`ff-solve` to prove a finite-field-root contradiction. It was replaced with an
invertibly mixed polynomial contradiction. The failed test attempt is preserved
in the local evidence; all reported final tests use the corrected fixture.

## Default-portfolio screen and decision

The frozen round-8 baseline and final candidate run the same preselected
113-input screen at ten seconds per run, eight workers, and a 4 GiB cap.
All 452 runs complete without infrastructure failures. Every variant solves
**53/113**: 40 UNSAT, 12 single-query SAT, and one multi-query Example. All ten
Examples solve. There are no gains, losses, or contradictory answer sequences.

| Configuration | Solved | Common-solve summed time | Change versus baseline |
| --- | ---: | ---: | ---: |
| Frozen round-8 default | 53 | 9.942 s | — |
| Final build, default flags | 53 | 9.781 s | −1.62% |
| Referenced reducers + adaptive admission | 53 | 9.888 s | −0.54% |
| Referenced reducers + adaptive admission + packed rows | 53 | 9.838 s | −1.04% |

The near-equal timings are screening evidence, not a speedup claim. All 48
single-query SAT model replays validate by independently evaluating original
assertions. Seven SAT replays from the targeted algebra diagnostics also
validate, including the one Small case at higher work allowances. Multi-query
Examples are compared by their full answer sequences rather than counted as
single-query models.

**Decision:** retain precise diagnostics and the tested opt-in representation;
keep `ff.lazy_matrix`, `ff.adaptive_matrix`, and `ff.compact_matrix` false by
default. Keep the ordinary work allowance. No observed coverage gain warrants a
new 1,256-input default-acceptance run. Next, attribute work to symbolic discovery,
S-pair processing, and numeric elimination before choosing a general algorithm
that reduces basis growth or redundant work. Large-field expansion, Linux/CI
hardening and real Blaster acceptance remain subsequent plan items.

The diagnostic runner also passes a focused supervision check: a missing input
is journaled as an infrastructure failure, the following valid input still
runs, and reusing the output directory is rejected without changing the journal.

## Reproduction and evidence

Local raw evidence is in `tests/finite_field/results/performance-round9`:
`diagnostics.jsonl` contains the original 51-case attribution;
`lazy-diagnostics/` and `followup/` contain the 34-case representation experiments;
`screen/` contains the default-portfolio screen. Configurations, source/input
hashes for the reusable runner, frozen binary hashes, and full solver output
are retained. The original one-off diagnostic predates input hashing; its
queried source files and script are archived separately.

The reusable diagnostic runner preserves assertions, accepts explicit local
`ff-solve` options, journals infrastructure failures, and refuses to overwrite
an existing journal. For example, from the repository root:

```sh
python3 tests/finite_field/diagnose_ff_limits.py \
  --manifest tests/finite_field/results/performance-round9/lazy-diagnostics/selection.json \
  --binary build-ff-cmake/z3 \
  --configs tests/finite_field/results/performance-round9/lazy-diagnostic-configs.json \
  --out /tmp/ff-matrix-diagnostic-new --timeout 3 --jobs 4
```

This is an algebra diagnostic, not a competitive solver score. To reproduce the
portfolio screen, use `benchmark_ff_optimizations.py` with the archived screen
selection/configuration and `--timeout 10 --jobs 8`, substituting the matching
frozen binaries. The baseline is the retained round-8 default, not round 7.

Frozen binary SHA256 identities:

- Round-8 baseline: `4c63ed60034006639969127ed7f81deadf46b12c21955c106a61b09370efca8a`.
- Diagnostics-only build: `af33cf0db9328037a9abd5091ae31e96e6dbe85218e5fcc0b03acbe6d7151aaf`.
- Targeted experiment build: `807837466d083f175cccaf5fe26c27fcba0efbcc4b579ac46f34db22f3c33b67`.
- Final screen/test build: `abbca83d74685143a3b488383a1c58a377d995f6783a9619a62a9c03e6381f01`.

The final build adds a referenced-reducer use counter to the targeted experiment
build. The source overlay, regression records, input archive, helper scripts and
logs are kept with the local evidence. The historical CAV figures are unchanged;
this round does not introduce a newly accepted default or a fresh cvc5 score.
