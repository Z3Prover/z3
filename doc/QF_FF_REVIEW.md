# Reviewing the QF_FF branch

Start with [the feature contract](QF_FF.md), then review the six implementation
commits in order. The branch starts from `cb83665b3`; it adds a coherent feature,
not a replay of every development experiment. The commit organization preserves
the validated solver sources byte for byte. No public history was rewritten.

## Commit order

| Step | Commit subject | Main review focus |
| --- | --- | --- |
| 1 | `feat(ff): add prime-field terms, rewriting, and SMT-LIB support` | Sort separation, numeral semantics, guarded rewrite conditions, models |
| 2 | `feat(api): expose prime fields in C, C++, and Python` | Public API dispatch and round trips |
| 3 | `feat(ff): implement bounded modular algebra with explained conflicts` | Polynomial identities, premise tracking, roots, bounded resources; C++ tests included |
| 4 | `feat(tactic): add field preprocessing, algebra, SAT, and exact BV tactics` | Wire/model reconstruction, Boolean abstraction, widened BV arithmetic, defaults |
| 5 | `feat(smt): combine prime fields with UF, arrays, and datatypes` | Shared model arrangements, finite cardinality, exact bridge, incremental lifecycle |
| 6 | `feat(solver): route finite-field goals through the native portfolio` | Default, repeated-check, and assumption routing |
| 7 | `test(ff): cover semantics, model reconstruction, and theory combination` | Independent enumeration, models, cores, lifecycle, large-field queries |
| 8 | `test(bench): add reproducible field benchmarks and independent validation` | Measurement integrity, cleanup, input identity, independent SAT evaluation |
| 9 | `docs(ff): explain the semantic contract and guide the review` | Supported scope, proof obligations, measured default decisions |
| 10 | `docs(paper): update the CAV draft with the measured root-completion gains` | Reproducible figures, exact populations, historical/current distinction |

The largest implementation file is `src/math/polynomial/ff_polynomial.cpp`.
Review its public data/provenance contract in the header first, then arithmetic,
basis construction, root reasoning, and `solve_core`. The optional experimental
branches are explicitly disabled unless stated in the parameter table. They
are implemented and tested, not claimed as performance wins.

For theory combination, read `doc/QF_FF_COMBINATION.md` before
`src/smt/theory_ff.cpp`. Candidate-model equalities guide decisions; they are
not unconditional theorems. The bridge must preserve finite cardinality and
native foreign signatures, and conflict premises must match the SAT atoms.

## Validation and scope

The final retained source passed 16 regression commands, including independent
small-field enumeration, 512 C++ algebra/provenance checks, mixed-theory and
incremental tests, and resource/cancellation recovery. All 559 primary SAT
model replays in the latest paired study validate against original assertions.
The compact paper evidence includes the exact regression records. These checks
apply to the complete feature tree; intermediate commits have not each been
independently rebuilt. Build instructions are in [QF_FF.md](QF_FF.md).

The latest default enables `ff.model_search`: 886 to 888 solves on 1,256 paired
inputs, no losses, and +0.45% summed time on common solves. Two short-case
slowdowns are documented. `ff.quotient_field` and `ff.adaptive_matrix` remain
off. See [round 8](QF_FF_PERFORMANCE_ROUND8.md) for the acceptance evidence.

Certificates remain v2; dependency sets are not checkable proofs. Large-modulus
primality is screened rather than certified. General quantified solving and
extension fields are outside the implemented feature scope. Neither the latest
Z3 default nor current cvc5 main has a completed fresh full-corpus comparison.

## Source and data boundaries

Source commits include tests, benchmark tools, small fixtures, and manifests.
Downloaded corpora, raw solver journals, generated figures/PDFs, and render
scratch files remain on disk but are ignored. Nothing was deleted to achieve
this separation. Historical performance documents describe their own frozen
configurations and should not be read as current-default results.

The final paper commit includes editable LaTeX and a compact, frozen evidence
archive sufficient to regenerate its figures without solver runs. See
[paper reproduction](papers/qf_ff/README.md). Full local raw evidence remains
under `tests/finite_field/results`; the archive is a focused report input,
not a substitute for a future public benchmark/source release.
