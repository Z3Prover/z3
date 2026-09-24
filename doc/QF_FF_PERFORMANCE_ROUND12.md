# QF_FF performance round 12: basis admission and pair storage

This round replaces the optional basis row-count policy with estimated storage
accounting and removes retired pair records. The implementation can pass the old
256-row limit, but the measured hard cases still do not gain solves. A larger
storage/work follow-up removes the basis bottleneck and exposes matrix-pivot
storage and deadline limits. Existing defaults remain unchanged; the full cvc5
comparison is still paused.

## Policy and invariants

`ff.adaptive_basis` is false by default. When enabled, the algebra admits up to
1,024 active rows within separate budgets for retained basis data and pair
records. The default allowance is 16 MiB for each. The historical 4,096-slot
ceiling remains, as do polynomial-size, degree, work, matrix and shared
cancellation guards. When disabled, the existing 256-active-row policy remains.

`ff.basis_max_bytes` adjusts the retained-basis allowance, defaults to 16,777,216,
and is capped at 1 GiB even if the caller requests the largest unsigned value.
The pair-record allowance remains 16 MiB. Local and global settings are supported;
the global names are `:smt.ff.adaptive_basis` and `:smt.ff.basis_max_bytes`.
Probe engines inherit both the policy and the effective basis allowance.

Basis accounting includes polynomial/vector headers, term nodes, canonical
coefficient limb estimates, allocated monomial capacities and premise sets.
Per-row sizes are calculated at insertion and subtracted at retirement, avoiding
repeated scans of the full basis. The scan itself consumes work. Pair accounting
includes heap/FIFO capacity even after removals, completed-pair nodes, GM map
records and their allocated LCM monomials. Vector allowances include reallocation
and compaction headroom. These are estimates for retained structures, not a
bound on total process RSS; input formulas, temporary rows, caches and matrices
have their own costs and guards.

After at least 64 further retirements, the ordinary batched path rebuilds its
pair heap at a batch boundary and removes completed-pair records involving empty
rows. The original loop already skipped pending pairs involving those rows,
and chain criteria already excluded empty intermediate rows. Cleanup therefore
preserves every live pair and its rank/order. No basis or premise index is
renumbered. It happens after batch outputs are installed, so pending derivations
never become premature chain witnesses. GM keeps basis rows stable and does not
use this retirement cleanup.

These changes alter resource admission and scheduling storage, not polynomial
identities. Conflict explanations keep their original premise indices. Proof
certificates remain v2; no CoCoA code or dependency is introduced.

## Initial algebra experiment

The same 34 historical Small gaps run through `ff-simplify` and direct `ff-solve`.
Each run has a ten-second external deadline, a 9.8-second internal deadline,
a 4 GiB cap and four workers. Options are explicit local tactic parameters.
These are diagnostic algebra runs, not the complete default portfolio.

| Configuration | Solved / 34 | Work limits | Principal remaining limits |
| --- | ---: | ---: | --- |
| Adaptive basis alone, 2M work | 0 | 18 | 15 reducer-count; one polynomial-size |
| Referenced/adaptive matrix, old basis policy, 32M | 1 | 7 | 13 active-basis; nine matrix; four polynomial-size |
| Same matrix, adaptive basis, 16 MiB, 32M | 1 | 12 | Eight basis-storage; nine matrix; four polynomial-size |
| Plus fused scalar reduction | 1 | 3 | 16 basis-storage; ten matrix; four polynomial-size |
| Packed matrix rows, adaptive basis, 16 MiB, 32M | 1 | 24 | Two basis-storage; six matrix; one polynomial-size |

The baseline row-count blocker is real: the adaptive tree configuration performs
13 pair compactions and discards 114,542 stale pair records across the cohort.
It reaches an active-basis statistic of 298, versus the old stopping value 257.
With fused scalar reduction, the corresponding statistic reaches 331. Yet all
these configurations solve only the previously recovered SAT case,
`r_211_16_8_system16.smt2`. Removing the row-count guard alone is insufficient.

## Larger bounded follow-up

A second build exposes the configurable basis allowance; its default policy
matches the initial build. The follow-up retains the same deadline and input
cohort, increases the explicit work allowance to 128M, and tests 64 MiB of basis
storage. The pair and matrix allowances are unchanged.

| Configuration at 128M work | Solved / 34 | Main stopping observations |
| --- | ---: | --- |
| Old basis policy, referenced/adaptive matrix | 1 | 16 active-basis; seven pivot-storage; one shared cancellation |
| Adaptive basis, 64 MiB | 1 | 15 pivot-storage; nine shared cancellations; no basis-storage failures |
| Same, with fused scalar reduction | 1 | 17 pivot-storage; seven shared cancellations; no basis-storage failures |
| Same, with packed matrix rows | 1 | 11 local-work; 12 shared cancellations; eight other matrix guards; one outer timeout |

The table highlights dominant guards rather than listing every polynomial/column
failure. Shared-limit cancellation in these runs accompanies the internal time
limit. One packed-row run reaches the outer deadline without a diagnostic
answer; it remains recorded as a timeout. All 136 runs complete without an
infrastructure failure, and the only solve is still the same SAT case.

The adaptive tree and fused variants reach active-basis statistics of 356 and
390, respectively. Their peak reported basis estimates exceed the old 16 MiB
allowance, confirming that the requested 64 MiB setting takes effect. Neither
hits the new basis-storage limit. The tree variant performs 18 compactions and
discards 223,386 stale pair records; the fused variant performs 20 and discards
270,981. Such cleanup does not imply a speedup: scanning and rebuilding live
records costs work too.

This follow-up distinguishes the old basis restriction from the remaining
problem. More basis capacity is now available, but matrix-pivot storage and
elimination cost prevent completion within the deadline. No larger resource
allowance is adopted as a default.

## Correctness

All 20 regression commands pass. A C++ fixture builds 300 independent monic
variables over both a small prime and a cryptographic prime: the original policy
fails at its active-row limit, while the adaptive
policy completes the exact known basis with both ordinary and GM pair selection.
Separate injected storage limits force basis-data and pair-record exhaustion,
leave the caller's input unchanged, and permit a successful subsequent call.
A retirement fixture checks exact output and premise equality with the original
algorithm while actually removing stale pair records.

The randomized basis suite now performs 1,152 configuration checks, including
adaptive admission with and without GM, with ideal membership, S-pair completion
and provenance validation. The Python suite checks options through ff-solve,
ff-sat, QF_FF and native SMT, observes storage accounting and tests incremental
model recovery. For each coefficient layout it independently enumerates 225
small-field systems and validates cores, plus 54 mixed-theory cases and 96
boundary-prime checks. An additional final replay forces exhaustion through a
global byte limit and verifies a successful local override on the next check.

As in round 11, the optional cvc5 executable is unavailable; `test_qfff.py` uses
Z3 and exhaustive enumeration without a fresh cvc5 cross-check. No new cvc5 score
is claimed.

## Normal-configuration screen and decision

The same 113-input screen compares the frozen round-11 default, the final build
with default options, and the final build with `ff.adaptive_basis=true`. All
resource values remain at their defaults in this screen. Each run gets ten
seconds, a 4 GiB cap and eight workers. Builds, regression runs and targeted
algebra diagnostics finish before the timing screen starts. The later
cryptographic-prime fixture replay and model validations occur after it ends.

All **339 runs** complete without infrastructure errors. Every configuration
solves **53/113**: 40 UNSAT, 12 single-query SAT and one multi-query Example.
All ten Examples solve. There are no gains, losses or contradictory answer
sequences. All **36 screen SAT model replays** and **eight direct-algebra SAT
replays** pass independent evaluation of original assertions. Multi-query
Examples are compared by full answer sequences, not counted as single-query
model replays.

| Configuration | Solved | Summed common-solve time | Change vs baseline |
| --- | ---: | ---: | ---: |
| Frozen round-11 default | 53 | 10.220 s | — |
| Final build, default options | 53 | 9.647 s | −5.60% |
| Adaptive basis, default allowances | 53 | 9.768 s | −4.42% |

The control build improves as well, so these screening timings cannot establish
a speedup attributable to the new policy. Adaptive admission is about 1.25%
slower than its same-build control by summed time. No larger-budget default
portfolio is proposed: the direct-algebra follow-up already supplies no coverage
gain despite using more time and memory.

**Decision:** retain the tested storage-aware admission and stale-pair cleanup as
an opt-in capability, keep `ff.adaptive_basis=false`, and preserve default work,
row and storage allowances. No larger default-acceptance campaign is justified
by this result. The basis-specific restriction is now bypassable with explicit
bounds, but solving the remaining gaps needs attention to matrix-pivot storage
and elimination cost. Increasing basis capacity alone is not a coverage win.

## Reproduction and evidence

Local evidence is in `tests/finite_field/results/performance-round12`:
`diagnostic/` has 170 initial algebra runs; `followup/` has 136 larger-budget
algebra runs; `screen/` has 339 default-portfolio runs. The archive also retains
regression records, independent model validations, frozen binaries, source
snapshots, helper scripts, restored benchmark inputs and portable configurations.
The CAV draft remains tied to its frozen round-8 evidence; there is no new cvc5
comparison or newly accepted default in this round.

For a fresh larger-budget diagnostic, from the repository root:

```sh
python3 tests/finite_field/diagnose_ff_limits.py \
  --manifest tests/finite_field/results/performance-round12/portable-small-selection.json \
  --binary tests/finite_field/results/performance-round12/binaries/expanded \
  --configs tests/finite_field/results/performance-round12/followup-configs.json \
  --out /tmp/ff-basis-storage-new --timeout 10 --jobs 4
```

Use `benchmark_ff_optimizations.py` with the retained
`portable-screen-selection.json` and `portable-screen-configs.json`, ten seconds
and eight workers for the portfolio screen. Original execution journals and
configurations retain their actual temporary paths; portable copies point at
preserved local inputs and executables.

Binary SHA256 identities:

- Baseline: `bd0ee41654e7e9f58c16eca364f0a0084e2eed63cdfeeafe7f1eb2c87c74caf8`.
- Initial 16 MiB experiment: `d532dc249a73c14ce73317cfb2d9c34dd8c5c15208b0e053a5dc7358345f1888`.
- Configurable-storage/final screen build: `8617c9d3ce535f366521381c9ec1f1f4135fd2eb4427b6558570552137bd18c9`.

The final changes after freezing the screen binary extend only C++ test coverage
to the cryptographic prime; the solver implementation is unchanged.
