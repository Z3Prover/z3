# Review of the attached fixed-width F4 backend

**Recommendation: integrate the backend after compiler-portability and resource-guard
cleanup. The performance criterion is met on this screen: broader coverage with
essentially unchanged time on the previously solved cases.** The six patches are
built and tested in an isolated checkout; no backend change has been merged into
our working branch by this review. Proof production still needs its own F4 integration.

## Measured results

Fresh native arm64 comparison, ten-second external deadline, four workers:

| Family | Distinct inputs | Current fork | F4 candidate | Candidate, F4 off |
|---|---:|---:|---:|---:|
| Public compiler circuits | 1,553 | 1,453 | **1,454** | 1,453 |
| FFSAT small-field systems | 325 | 243 | **272** | 243 |
| Generated dense systems | 28 | 12 | **27** | 12 |
| Generated underdetermined systems | 6 | 2 | **6** | 2 |
| Fresh exhaustive-oracle cases | 200 | 200 | 200 | 200 |
| Fresh large-field differential cases | 100 | 100 | 100 | 100 |
| **Total** | **2,212** | **2,010** | **2,059** | **2,010** |

There are **49 gains, zero losses, zero SAT/UNSAT disagreements, no process
errors, and no known-oracle mismatches**. The new solutions comprise 31 UNSAT
and 18 SAT answers. Across the same 2,010 shared successes, cumulative elapsed
time is **281.825 s current, 279.106 s candidate, and 282.338 s F4-off**. Median
paired candidate/current time ratio is 0.9995. This supports comparable speed,
not a claim of a meaningful 1% speedup. There is no common success with both a
2x slowdown and an absolute slowdown over 0.2 s; raw timings remain available.

Every current/F4-off status agrees input by input. All primary input files use
`QF_FF`, so the extra `QF_FFA` alias is not responsible for these gains. When
weighted by the 1,927 public member paths, current versus candidate coverage is
**1,745 versus 1,775**, reproducing the supplied public-corpus coverage counts
on our machine, even with our shorter time budget. The 19 additional gains are
on the generated dense/underdetermined suites.

This is an ordinary-solving benchmark: **none of these counts is a count of
checked certificates**. It uses different inputs and a lighter timing harness
than the earlier 390-input FMCAD proof comparison.

![F4 review cactus](../tests/finite_field/results/claude-f4-review-20260928/measurement/cactus.png)

### Held-out and integration checks

A separate, size-stratified selection of **32 QED², sequence, arithmetic-shift
and example inputs** from the CAV24 artifact gives **28/32 for all three
configurations**, with identical statuses. Shared-success cumulative times are
2.065, 2.143 and 2.127 seconds respectively; those short concurrent measurements
do not establish a significant timing difference.

Additional checks passed:

* 15 mixed-theory/incremental cases over five fields, including UF and arrays;
* `QF_FF` / `QF_FFA` alias equivalence;
* 32 fresh exhaustive-oracle systems around the dispatch boundaries, over
  p=61, 67, 251 and 257, checked by both executables (64 successful checks);
* a direct F4 test with 65 variables, colliding support masks and a conflict
  core crossing the 64-bit premise-word boundary, over F3 and BN254;
* the original finite-field unit suite;
* the literal external proof suite: 29 accepted bundles and 25 rejected cases;
* the Boolean proof suite: 30 accepted bundles, 22 rejected cases, 575 Boolean
  search checks, a 12,000-level let input and a 400-node sharing chain. Its
  exhaustive mixed sample retains two unavailable proofs; this is not a claim
  of complete certification.

### Serial timing and memory diagnostics

These follow-ups are separate from the primary campaign. RSS is sampled every
10 ms for the solver process; it is an observed peak, not a hard memory cap.

| Input | Current fork | F4 candidate | Current / candidate peak RSS |
|---|---:|---:|---:|
| BN254, 8-variable planted dense | timeout (10 s) | **SAT, 2.16 s** | 2,492 / **51 MiB** |
| BN254, 9-variable planted dense | timeout (10 s) | timeout (10 s) | 2,496 / **79 MiB** |
| FFSAT `i_211_8_16.022` | timeout (10 s) | **UNSAT, 1.91 s** | 158 / **100 MiB** |

These selected examples show useful memory improvements, not a corpus-wide
memory result. The main campaign did not sample RSS for every run. Successful
primary measurements all finish below ten seconds; timeout elapsed values
include polling/termination overhead and are not clipped.


## Scope and provenance

The supplied ZIP contains six patches, although its README still says three.
The accompanying PR text describes the earlier defaults (`f4_budget=100`);
the final source uses 40, a short circuit budget, and disables F4 by default in
lazy SAT branch queries. The review evaluates all six patches together.

The patches were applied to our current `6400f1a42` in an isolated clone.
Three-way application required two additive conflict resolutions:
retain both `ff_certificate.cpp` and `ff_f4.cpp` in CMake, and retain both
certificate and F4 unit tests. No solver algorithm or dispatch threshold was
changed for the measured candidate. The main branch was not changed.

Release build: Apple Clang, native arm64, explicit Xcode macOS SDK, CMake/Ninja.
The SDK override repairs a local CommandLineTools/Xcode mismatch; it is not a
patch-specific source change. Baseline is our existing Release executable;
the F4-off ablation uses the same executable as the candidate.

## Correctness and integration review

Positive features:

* fixed-width field arithmetic is confined to a separate implementation;
* matrix reductions retain premise sets;
* randomized minimal-polynomial discovery is followed by an exact membership
  check before using the result for root splitting;
* root enumeration/splitting is exhaustive when returning UNSAT, and failures
  or exhausted budgets yield unknown;
* SAT models are re-evaluated on original constraints;
* unsupported field widths retain the legacy path;
* all existing certificate code and tests can coexist with the new backend.

Remaining integration work:

1. **Compiler portability.** `ff_field.h` uses `unsigned __int128` and
   `__int128` unconditionally; `deps::for_each` uses `__builtin_ctzll` without
   the compiler guard/fallback found in `util/approx_set.h`. The file is always
   compiled. Native MSVC needs a fallback or a capability-gated backend.
   A runtime `ff.f4=false` cannot repair a compile-time incompatibility.
2. **Certificate derivations.** Premise bitsets are not PAC certificates. The
   backend does not record polynomial multipliers, matrix row derivations,
   checked minimal-polynomial witnesses or exhaustive-root derivations. The
   existing `ff-certify` builder uses its own search, so solver gains cannot be
   counted as certificate gains. Keeping that independent pipeline is sound;
   integrating the F4 speedups into it requires additional work.
3. **Resource accounting.** The variable cap counts original variables before
   Rabinowitsch auxiliaries are added. The monomial cap is checked during matrix
   row materialization, not at every monomial-interning site. Pair installation
   and some basis/model loops also have coarse cancellation accounting. These
   should receive guard/recovery tests before enabling this backend broadly.
4. **Basis handoff.** F4 exports a grevlex basis into the legacy polynomial
   container's ordering and skips the legacy basis computation. The ideal is
   preserved, but the exported set need not be a Gröbner basis in the receiving
   order. I audited the receiving consumers: reductions preserve ideal
   congruence, the finite-dimension test remains a sufficient bound, root
   splits use explicit consequence polynomials, and SAT models are rechecked.
   I found no unsound inference from this handoff. Document it as an equivalent
   generating set, rather than a basis in the receiving order; the differing
   order can still change heuristic effectiveness.

The native finite-field suite passed, including 900 F4 systems checked against
exhaustive enumeration with conflict-core checks, arithmetic tests, and our
existing certificate/basis/model regressions. The external proof-pipeline
suite accepted 29 valid bundles and rejected 25 invalid cases. These are tests,
not a formal proof of the implementation's soundness.

## Audit of supplied performance claims

The supplied JSONL logs contain 1,927 cases, with 30 gained solutions and zero
lost solutions for the candidate: 29 FFSAT cases and one circuit case. No paired
SAT/UNSAT disagreement appears in those logs. The claim that no case is more
than twice as slow is incorrect: 20 paired successes exceed 2x. Most are very
short runs, so those ratios alone do not establish important regressions.

Their runner accepts the first answer even when a process exits unsuccessfully,
clips recorded time to the limit, and grants extra outer timeout slack. Our
rerun uses a strict ten-second external deadline, preserves elapsed times and
requires a successful exit with exactly one answer and no SMT error.

## Our protocol

The 1,927 named public cases map to 1,878 distinct inputs in our verified paper
corpus. The 325 FFSAT names are mapped from `testdata_*.NNN.smt2` to the artifact's
`*_systemNN.smt2` naming. We have no source bytes in Claude's ZIP to verify
byte-for-byte identity with its Linux runs; this is a comparison on our locally
verified corresponding corpus. The same bytes go to all three configurations.

Additional inputs: 28 dense and six underdetermined systems from the supplied
generator with seed 2026, plus 200 exhaustive-oracle small-field and 100
large-field differential systems with a new seed, 20260928. Total: 2,212 inputs
and 6,636 runs, four workers, deterministically shuffled configuration/input
pairs. Generated overdetermined systems have no assumed UNSAT oracle; planted
systems have a known SAT witness. Randomized small-field cases have exhaustive
oracles. The large-field differential cases do not establish correctness when
all implementations share an error.

Configurations: current fork, six-patch candidate, same candidate with
`smt.ff.f4=false`. Separate serial follow-ups investigate coverage losses and
material timing regressions; they never replace primary measurements.

## Comments on the proposed future work

**Uniqueness propagation:** a promising next step, but the starting point is
stronger than the supplied description suggests. Our fork already eliminates
acyclic wire definitions, normalizes shared expressions, eliminates variables
with constant nonzero linear coefficients, and propagates injective binary
encodings. Extend these facilities to proof-producing relational uniqueness
rather than treating all two-copy circuits as arbitrary polynomial systems.
Local linear uniqueness needs equal inputs and a provably nonzero coefficient.
Binary uniqueness needs a non-wrapping range (`2^n <= p` for unrestricted n-bit
encodings), or an appropriate canonical-range proof. Stalling gives an unresolved
obligation, not an underconstraint witness: e.g. y^2=1 and y^3=1 uniquely fix y=1,
but a simple linear/bit propagation engine can stall. A counterexample or a
complete decision procedure is needed to declare underconstraint.

[Picus](https://github.com/Veridise/Picus) already combines uniqueness propagation
with solver reasoning. The novelty of a particular certified in-SMT version
needs a focused literature comparison; do not claim a first from this proposal.

**MCSat:** the direction is credible for positive-dimensional systems, but
adapting nlsat is a research-sized change, not simply changing coefficient types.
Its assignments, root atoms, evaluators and interval machinery are specialized
to real arithmetic. Hader et al.'s [Yices2 implementation](https://arxiv.org/html/2402.17927v2)
uses finite-field zero decomposition and GCD-based explanations. A finite-field
plugin needs sound conflict explanations, handling of vanishing leading
coefficients, backtracking and learned clauses. Partial assignment makes a
constraint univariate only after all but one of its variables are assigned.
Field size alone does not determine when Gröbner methods work.

**Certificates:** PAC combinations, Fermat, Bézout and uniqueness lemmas are
appropriate ingredients, but the end-to-end obligations include normalization,
input binding, root completeness, branch discharge and Boolean reasoning.
The [FMCAD 2026 paper](https://hanielbarbosa.com/papers/2026fmcad-ffproofs.pdf)
already implements CVC5 finite-field proof production and Lean reconstruction.
It is incorrect to describe all CVC5 finite-field reasoning as trusted or to
claim that Lean-checked finite-field SMT certificates would be a first. Our
credible differentiators would be Z3 integration, broader certified coverage,
and efficient certificate production/checking. The current branch's evaluated
external path is Carcara/FFPacheck plus independent replay, not a demonstrated
Lean kernel check of every solver UNSAT answer.

## Suggested certificate integration order

First add an optional derivation DAG for F4 linear combinations, using the
certificate builder's original polynomial inputs. Calling the ordinary solver's
F4 stage after unrecorded variable elimination/bit propagation is not enough:
premise sets do not reconstruct those preprocessing derivations. Keep Boolean
and original-input binding checks unchanged. Next record the minimal-polynomial
membership witness and complete root partitions; then extend proof-producing
normalization/uniqueness propagation. Measure generated size and checking time
as well as solver time, because faster elimination can still produce expensive
proofs. This is independent of the native solver's useful performance gains.

## Evidence and reproduction

The local archive is
`tests/finite_field/results/claude-f4-review-20260928/`. Bulky results are ignored
by Git; this report is versioned. The archive contains original inputs, all
stdout/stderr receipts, input/binary hashes, the supplied ZIP, the exact integrated
patch, build/test logs, native binaries, comparison scripts, and separate
follow-up receipts.

* [Primary summary](../tests/finite_field/results/claude-f4-review-20260928/measurement/summary.json)
* [Per-input CSV](../tests/finite_field/results/claude-f4-review-20260928/measurement/per-input.csv)
* [Held-out CSV](../tests/finite_field/results/claude-f4-review-20260928/holdout/per-input.csv)
* [Tested integration patch](../tests/finite_field/results/claude-f4-review-20260928/provenance/integrated-candidate.patch)
* [Supplemental wide-variable regression](../tests/finite_field/results/claude-f4-review-20260928/provenance/additional-review-tests.patch)

The candidate source checkout remains at
`/private/tmp/claude-ff-review-20260928/z3-candidate`. Its measured executable is
`build-review/z3`. The integrated patch applies to `6400f1a42`; the supplemental
wide-variable test is a separate patch and changes no solver code. All measured
source hashes were rechecked after the tests. To repeat elsewhere, apply that
patch to the base, build Release `z3` and `test-z3`, then adjust the archive paths
and executable paths in the archived comparison scripts. Their metadata records
the seeds, selected hashes, commands and deadline.
