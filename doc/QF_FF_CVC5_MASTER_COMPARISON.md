# Current cvc5 comparison and follow-up plan

## Comparison paused at user request

Pinned cvc5 upstream `main` revision: `72f647eb75c0241d82bc24ecf1f4092ff0f683f7`
(1.4.1.dev, fetched 2026-09-23). Unrestricted optimized static build with
CoCoALib 0.99850; no cvc5 source modifications. Build details and configuration
are in `tests/finite_field/results/cvc5-master-20260923`.

The full campaign was stopped after 1,018 of 12,636 solver runs so Z3 improvement work can proceed. Partial results and frozen binaries are preserved; they are not a complete comparison. Do not resume without a new request.

The planned campaign reruns all three configurations (Z3+FF, cvc5 GB, cvc5 split)
on 4,212 distinct paper inputs, interleaving their order, using eight workers,
10 seconds and 4 GiB sampled RSS per run. The eight real-project queries will
be measured separately. The Z3 binary remains the frozen round-7 retained
binary throughout the comparison. No implementation changes during measurement.

All seven `:incremental true` inputs are normalized for Z3 only. All assertions,
incremental commands and check-sat commands are preserved. The corrected
historical report remains available until this campaign is complete.

Current-master smoke tests reproduce the known split false-UNSAT on the original
32-constraint F3 example and its minimal reduction. A fresh GB model independently
satisfies every original assertion. Raw results remain intact; the adjudication
layer excludes the incorrect split answer from solved counts.

## Completed follow-up: bounded root completion

Round 8 enabled `ff.model_search` after a clean 1,256-input study: 886 to 888
solves, zero losses, +0.45% common-solve time. The cyclic Example and
Montgomery2Edwards query are the two gains. Root-only completion is available;
quotient-field and adaptive-matrix candidates remain off. The full current-cvc5
comparison remains paused. See [the round-8 report](QF_FF_PERFORMANCE_ROUND8.md).

## Historical investigation plan

The user brought this work forward and paused the comparison. Investigate and implement
general improvements to multivariate-to-univariate elimination and exhaustive
finite-field root reasoning. Start by classifying missed inputs; do not infer
that all timeouts have this cause. Use a broad regression set and retain a new
default only if coverage improves without material performance regression.

Concrete lead: `examples/sec4_triangular.smt2`, the cyclic five-variable system
over F394357. Frozen Z3's algebra-only tactic returns unknown in about 0.02 s
with reason `ff-solve requires complete BV fallback`, without algebra-budget
exhaustion. Default routing then enters BV fallback and times out at 10 s.
Pinned cvc5 master GB proves UNSAT in about 0.03 s; split times out. The diagnostic
logs are in `results/cav-overview/examples-normalized/triangular-*.json`.
This is a strategy/completion gap, not evidence that polynomial arithmetic
alone consumed the timeout. No special case for the benchmark is authorized.

### Candidate mechanisms to evaluate after the baseline is frozen

* Separate complete finite-field refutation from SAT witness heuristics. The
  existing optional `ff.model_search` derives quotient minimal polynomials but
  is off by default after earlier screens; first determine why it failed to
  provide broad gains and whether the new gap population differs.
* For a certified zero-dimensional leading ideal, derive bounded univariate
  consequences using normal-form linear dependence, then exhaust all roots in
  Fp. Choose unset coordinates rather than repeatedly probing assigned ones.
* A complementary general method is to reduce the field axioms `x^p - x = 0`
  in the quotient using repeated modular squaring. Adding the resulting small
  remainders can exclude extension-field-only solutions without expanding an
  exponent-p polynomial. It must preserve dependency explanations, cancellation,
  work accounting, and bounded term growth.
* Measure these separately; avoid enabling expensive witness sampling merely
  to enable a useful refutation step. Check small-characteristic cases,
  extension-only roots, genuine SAT counterparts, variable permutations,
  mixed-theory cores, and incremental lifecycle. Use original-assertion model
  validation and exhaustive small-field oracles, not agreement alone.
