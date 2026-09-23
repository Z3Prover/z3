# QF_FF performance round 10: work attribution and fused scalar reduction

This round measures where the algebra consumes its bounded work allowance, then
tests direct accumulation of scalar reducer multiples. The experiment preserves
reducer selection and the resulting polynomials, while avoiding intermediate
polynomial construction. It does not add solves on the 34 hard Small cases.
The full cvc5 comparison remains paused; these are Z3-versus-Z3 experiments.

## Exclusive work attribution

Six counters partition `ff algebra steps`: other work, scalar reduction, basis
insertion, pair processing, matrix symbolic construction, and matrix elimination.
Nested scopes account exclusively; a scalar reduction called by basis insertion
is charged to scalar reduction. On scope exit, including an exception, accounting
returns to the caller. Collecting statistics includes the current unfinished
scope. No extra ticks are charged and existing cancellation/limit semantics are
unchanged. These are work-unit counts, **not CPU profiles**: some searches and
bookkeeping do not have proportional work charges.

The 34-case diagnostic uses the direct `ff-simplify`/`ff-solve` route, ten-second
external and 9.8-second internal deadlines, four workers and a 4 GiB cap.
Every recorded run's phase sum agrees with its total reported work.

| Configuration | Scalar reduction | Matrix elimination | Symbolic matrix | Insertion | Pairs | Other |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Existing default limits | 51.27% | 32.13% | 11.25% | 1.99% | 2.88% | 0.48% |
| Referenced/adaptive matrix, 8M work | 51.43% | 39.26% | 6.48% | 0.94% | 1.59% | 0.30% |
| Referenced/adaptive matrix, 32M work | 54.26% | 40.09% | 4.19% | 0.57% | 0.80% | 0.10% |

These percentages describe work performed before each attempt stops, not the
cost of a completed basis. Changing a representation or budget can move the
stopping point, so a phase-share change alone is not evidence of a speedup.
Scalar reduction is nevertheless the largest consumer of the existing work
allowance, which motivates the following controlled implementation experiment.

## Direct accumulation of reducer multiples

The optional `ff.fused_reduction` replaces `f = f + (scalar * monomial) * b`
through a temporary polynomial with direct updates to `f`. Multiplication by a
fixed monomial is injective and order-preserving, so these updates occur in the
same order with identical coefficients. The same first applicable reducer is
selected. Each used reducer contributes its original premises and the same
sugar-degree bound. Coefficient arithmetic remains exact for arbitrary-size
moduli, and every accumulator update retains cancellation and size guards.

The saved work corresponds to operations removed: constructing the temporary
polynomial and traversing it again. The allowance itself is unchanged. The
existing geobucket alternative retains its own accumulation algorithm; this
option changes the ordinary scalar reducer only. Probe engines inherit the
setting. Local solver/tactic spelling is `ff.fused_reduction`; global SMT-LIB
spelling is `:smt.ff.fused_reduction`. The experimental default is false.

This is an independently implemented arithmetic change with no CoCoA dependency.
It preserves conflict explanations but does not implement proof certificates;
recording polynomial-combination witnesses remains v2.

## Targeted resource results

| Configuration | Solved / 34 | Work-limit cases | Other principal limits |
| --- | ---: | ---: | --- |
| Original, 2M | 0 | 18 | 15 reducer-count, one polynomial-size |
| Fused, 2M | 0 | 16 | 17 reducer-count, one polynomial-size |
| Fused + referenced/adaptive matrix, 8M | 1 | 25 | Four polynomial-size; two column; one row-growth; one symbolic-storage |
| Fused + referenced/adaptive matrix, 32M | 1 | 2 | 16 active-basis; six pivot-storage; four polynomial-size; three column; one row-growth; one symbolic-storage |

The only solved case remains `r_211_16_8_system16.smt2`. At eight million work
units its scalar-reduction charge falls from 117,204 to 80,681, but total work
falls only from 3,236,034 to 3,199,511: most of that particular solve is elsewhere.

At 32 million work units, the previous representation without fusion hit seven
work limits, 13 active-basis limits and four pivot-storage limits. Fusion reaches
more of those later guards: two, 16 and six respectively. This is further
progress within unsuccessful attempts, not increased solving coverage. Basis
growth and matrix fill remain the next algorithmic targets; the results do not
justify simply raising the default work allowance.

## Correctness and regression checks

All 18 regression commands pass. C++ tests compare exact ordinary/fused
remainders, premises and sugar values on 60 reductions across three prime sizes
and both coefficient modes, and require strictly fewer work units. The basis
suite now exercises 768 configuration checks, including fusion, with ideal
membership, complete S-pair reduction and premise validation.

The new Python suite exercises local on/off settings through ff-solve, ff-sat,
QF_FF and native SMT, observes actual fused reductions, and checks incremental
model recovery. For each matrix layout it independently enumerates 225 random
small-field systems and validates conflict cores, checks 54 guarded mixed-theory
cases, and runs 96 scalar/batched boundary-prime cases including a cryptographic
prime. The accounting test exercises nested scopes, exception unwinding,
subsequent reuse and exact partition totals.

## Portfolio screen and decision

The same preselected 113 inputs are run with four configurations, ten seconds
per input, eight workers and a 4 GiB cap. Builds, regression commands and targeted
algebra diagnostics finish before the screen begins. All 452 runs complete
without infrastructure failures. Every configuration solves **53/113**: 40 UNSAT,
12 single-query SAT and one multi-query Example. All ten Examples solve. There
are no gains, losses or contradictory answer sequences.

| Configuration | Solved | Summed common-solve time | Change vs frozen baseline |
| --- | ---: | ---: | ---: |
| Frozen round-9 build, default settings | 53 | 10.470 s | — |
| Final build, default settings | 53 | 10.264 s | −1.97% |
| Fused scalar reduction | 53 | 10.149 s | −3.07% |
| Fused scalar + referenced/adaptive matrix | 53 | 10.203 s | −2.55% |

These small differences do not establish a speedup: the geometric fused/baseline
ratio on common cases taking at least 50 ms in either configuration is 1.009.
The screen shows comparable performance, not a uniform improvement. All **48
screen SAT model replays** and **four diagnostic SAT replays** pass independent
evaluation of their original assertions. Multi-query Examples are compared by
full answer sequences, rather than counted as single-query models.

**Decision:** retain the work diagnostics and tested opt-in scalar implementation;
keep `ff.fused_reduction` false and preserve all existing default policies and
budgets. There is no observed coverage gain to justify a larger default-acceptance
campaign. The next candidate should address basis growth or matrix fill. A
possible general experiment is choosing sparser valid symbolic reducers, which
may discover fewer columns and generate less elimination fill. It must be
measured independently; this round supplies no evidence that it will add solves.

## Reproduction and evidence

Local evidence is under `tests/finite_field/results/performance-round10`:

- `profile/` and `profile-summary.json`: 102 instrumented algebra runs and exact
  work partitions on the 34-case cohort.
- `candidate/` and `candidate-summary.json`: 136 algebra runs comparing original
  and fused reduction with explicit local options.
- `screen/`: 452 portfolio runs, selection, configurations, source/input hashes,
  timing summaries and independent SAT validations.
- `regressions.json`, `diagnostic-models.json`: full regression records and
  independent algebra-route model checks.

For the direct algebra experiment, from the repository root:

```sh
python3 tests/finite_field/diagnose_ff_limits.py \
  --manifest tests/finite_field/results/performance-round10/candidate/selection.json \
  --binary build-ff-cmake/z3 \
  --configs tests/finite_field/results/performance-round10/candidate-configs.json \
  --out /tmp/ff-fused-diagnostic-new --timeout 10 --jobs 4
```

Use `benchmark_ff_optimizations.py` for the portfolio, with the archived screen
selection and configurations, matching frozen binaries, and `--timeout 10
--jobs 8`. Direct tactic diagnostics must use local numeric parameters; they
are not a replacement for a default-portfolio score.

Frozen binary SHA256 identities:

- Baseline: `abbca83d74685143a3b488383a1c58a377d995f6783a9619a62a9c03e6381f01`.
- Profiling build: `a343b3a51348842077596c55683c6f0faa8d268b0411b1600136ae8f259fbc93`.
- Candidate/screen/test build: `571b96ff0a7dac9f40a5fa63c6fe1c3a0bd6215363f1a7abfa157412efd497d7`.

The input archive, source overlay, helper scripts and build/test logs accompany
the local evidence. The CAV draft remains tied to its frozen round-8 data;
this round neither changes an accepted default nor refreshes the cvc5 comparison.
