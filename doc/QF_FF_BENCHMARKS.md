# QF_FF validation and performance snapshot

Recorded 2026-09-22 on macOS 26.6.2, ARM64. Z3 is the release build of this
branch (version banner 5.1.0), built with Apple Clang 21. The reference is the
official cvc5 1.3.4 macOS ARM64 static GPL release, git f3b21c4, with CoCoA.
Both cvc5's default field solver and `--ff-solver=split` were tested.

These are local elapsed-time measurements, not production performance
guarantees. Each successful measurement is the median of three fresh processes,
including startup, parsing, primality screening, solving, and shutdown. Startup
and modulus validation matter at these short runtimes. No warm-process timings
or peak-memory measurements are included. A timeout ends the repetitions for
that case; it is not an exact solve time.

## Correctness checks

- 1,000 generated formulas over fields of size 2, 3, 5, 7, and 17 were checked
  against exhaustive enumeration and cvc5. The default pipeline and forced
  bit-vector fallback were checked, with returned models independently evaluated
  against the original formulas. Bounded native tactics were also checked when
  they returned a definite answer. Cases include nonlinear arithmetic, Boolean
  combinations, field-valued ITEs, and bit sums.
- A clean CMake debug build passed native finite-field, AST, polynomial, and
  rational unit tests, plus 200 generated formula comparisons without assertions.
- The new polynomial engine and native field unit tests passed AddressSanitizer
  and UndefinedBehaviorSanitizer. This was not an instrumented whole-solver run.
- API tests cover models, incremental checks, assumptions, cores, context
  translation, resource-limit recovery, invalid moduli, large moduli, SMT-LIB
  round trips, and explicit rejection of proof requests. A compiled C++ smoke
  test exercises BN254 arithmetic and models.
- Native conflict subsets were checked for inconsistency by exhaustive
  enumeration on small fields. Input provenance is not a proof certificate.

## cvc5 regression suite

The harness reads the official cvc5 1.3.4 `test/regress/cli/regress0/ff` directory.
It selects explicit QF_FF cases with expected SAT/UNSAT answers, excluding
timing-specific unknown cases and other logics. It removes only cvc5-specific
`:incremental` and `:check-models` options; formulas and expected answers stay
unchanged. The per-process timeout is 10 seconds.

Z3 and default cvc5 both match **all 31 selected cases**. The median per-case
Z3/cvc5 time ratio is **1.001**, and its geometric mean is **0.917**. These ratios
describe this small regression set, not arbitrary QF_FF problems.

| Regression | Z3 (ms) | cvc5 (ms) | cvc5 split (ms) |
| --- | ---: | ---: | ---: |
| randcompile-sound-3i-5t-circ | 26.70 | 145.61 | 163.37 |
| randcompile-sound-3i-5t-zokcirc | 25.74 | 109.91 | 113.42 |
| randcompile-sound-3i-5t-zokref | 26.07 | 91.46 | 98.29 |
| bigff_is_zero_sound | 47.55 | 20.19 | 20.26 |
| bigff_is_zero_unsound | 46.62 | 18.75 | 24.37 |

The split reference passes 30 cases and crashes with a CoCoA `ErrorInfo` on
`issue11107.smt2`. The harness records this reference failure and exits nonzero;
it is not a Z3 mismatch. Details and all timings are in
[cvc5-regressions.json](../tests/finite_field/results/cvc5-regressions.json).

## Cryptographic-field synthetic gadgets

The generated suite contains **58 cases**, across BN254 and BLS12-381 scalar
fields. It includes affine chains up to 1,024 steps, fifth-power chains up to
512 steps, width-three S-box/MDS networks up to 32 rounds, polynomial identities,
inverse constraints, quadratic root exclusion, and 8/32/128-bit decomposition
checks. Timeouts are five seconds per process.

| Solver | Correct answers | Timeouts | Incorrect answers |
| --- | ---: | ---: | ---: |
| Z3 branch | 58 | 0 | 0 |
| cvc5 default | 48 | 10 | 0 |
| cvc5 split | 56 | 2 | 0 |

Representative BN254 results:

| Case | Result | Z3 (ms) | cvc5 (ms) | cvc5 split (ms) |
| --- | --- | ---: | ---: | ---: |
| Affine chain, 1,024 steps | SAT | 43.22 | 37.06 | 37.30 |
| Fifth-power chain, 512 steps | SAT | 55.57 | 29.80 | 29.17 |
| S-box/MDS, 32 rounds | SAT | 38.96 | 18.11 | 18.59 |
| Bit-sum injectivity, 128 bits | UNSAT | 25.66 | timeout | 281.85 |
| Bit-sum equals constant, 128 bits | SAT | 29.86 | timeout | timeout |
| Both square roots excluded | UNSAT | 31.63 | 13.53 | 12.68 |

Arithmetic-chain and S-box/MDS inputs are fixed, so these cases mostly measure
propagation and evaluation; their UNSAT variants change the claimed output.
The S-box/MDS network uses synthetic constants and the matrix I+J. It is **not**
a production Poseidon instance. The injectivity checks leave the bits symbolic
and supply explicit Booleanity constraints. Specialized, guarded bit-sum rules
explain the strong results on these cases.

All measurements are in [results.json](../tests/finite_field/results/results.json),
with banners in [versions.json](../tests/finite_field/results/versions.json).
Generated SMT-LIB inputs are reproducible using the harness and are not checked
in. Run from the repository root:

```sh
python3 tests/finite_field/benchmark_qfff.py \
  --z3 build-ff/z3 --cvc5 /path/to/cvc5 --repeat 3 --timeout 5
python3 tests/finite_field/cvc5_regressions.py \
  --suite /path/to/cvc5/test/regress/cli/regress0/ff \
  --z3 build-ff/z3 --cvc5 /path/to/cvc5 --repeat 3 --timeout 10
```

## Acceptance work still needed

The current results justify further development; they do not establish the
requested cvc5 performance on large production ZK circuits. Real R1CS and
Poseidon workloads with actual parameters, elliptic-curve constraints, partially
specified witnesses, and symbolic soundness/equivalence queries are still needed.
Measure scaling and memory as well as wall time. Several measured large-field
cases are already around two times slower than cvc5, and the exact BV fallback
can be impractical at cryptographic widths.

The next implementation decisions should follow those measurements: sparse F4
elimination, improved basis scheduling, polynomial sharing, and incremental
basis reuse are candidates. Checkable certificates remain a separate v2
milestone described in [QF_FF.md](QF_FF.md).
