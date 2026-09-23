# QF_FF: circuit scaling, simplification, and public benchmarks

This is the historical second-round report. The subsequent circuit-aware
preprocessing and symbolic improvements are measured in
[QF_FF_SYMBOLIC_BENCHMARKS.md](QF_FF_SYMBOLIC_BENCHMARKS.md).

Second-round measurements, 2026-09-22, macOS 26.6.2 ARM64. The branch was
fast-forwarded by 18 commits to `origin/master` at `cb83665b3`, and migrated to
the upstream CMake build and static tactic registration. All second-round
before/after binaries use this same upstream base.

## Measurement protocol

The CLI harnesses run solvers sequentially in fresh processes. Successful runs
use the median of three repetitions; an unresolved result stops repetitions for
that case. The solver limit is three seconds, with a five-second external process
guard because solvers may not respond promptly to cancellation. `unknown`,
process timeout, and runtime error are kept distinct in the JSON. Startup,
parsing, modulus screening, solving, and shutdown are included in wall time.
Peak RSS comes from a fresh worker's child-process resource usage and is reported
in MiB; it is not the cumulative peak of the benchmark suite. These are local
measurements without machine-wide performance isolation.

Every SAT result is rerun with model production, outside timed repetitions, and
checked independently against the original constraints. The generated suite uses
integer modular evaluation of every R1CS equation, pin, and disequality. Public
SMT inputs use a separate Python evaluator for Boolean structure, field arithmetic,
ITEs, and nested lets. No proof certificates are claimed for UNSAT results.
Binary and input hashes are recorded in the raw results.

## Reference-parameter circuit suite

There are 50 cases across BN254 and BLS12-381 scalar fields:

- Width-three Poseidon permutations with 8 full rounds, 56 partial rounds and
  exponent 5, chained 1/4/16 times; the largest has 6,912 R1CS-shaped equations.
  Parameters and independent known-answer vectors come from the pinned
  [HorizenLabs reference](https://github.com/HorizenLabs/poseidon2/tree/055bde3f4782731ba5f5ce5888a440a94327eaf3/plain_implementations/src/poseidon).
  These are that reference's original Poseidon instances, not Poseidon2 or a
  claim of circomlib-compatible parameter choices.
- Ordinary R1CS range encodings at 8/32/128/253 bits, testing witness completion
  and injectivity. They deliberately do not use `ff.bitsum`.
- Baby Jubjub and Jubjub affine addition chains of 1/8/64 additions, with fixed
  inputs, partial witnesses, and an on-curve preservation query. These use the
  [Baby Jubjub parameters](https://github.com/iden3/circomlibjs/blob/main/src/babyjub.js)
  and [Jubjub parameters](https://github.com/zkcrypto/jubjub/blob/main/src/lib.rs).
  They are curve-equation gadgets, not subgroup checks or signature verification.

The circuits are generated locally from authentic parameters; they are not
compiler-exported production applications. Fixed-input, free-input, partial-input
and symbolic-equivalence cases are labeled separately. The partial Poseidon case
leaves a two-bit input unknown while fixing an output. Equivalence compares two
multiplication schedules for the same full permutation.

## Measured optimization: ordinary R1CS bit decompositions

Profiling showed polynomial expansion and Gröbner computation on range checks
that missed the old syntax-specific `ff.bitsum` rules. The new recognizer works
on linear polynomials and directly pinned outputs. It requires Booleanity for
every bit, unique power-of-two coefficients, and an explicit no-wrap bound.
The original equations remain in the problem and derived facts carry conservative
input dependencies.

| Configuration | Solved / 50 | Unresolved | Incorrect answers detected |
| --- | ---: | ---: | ---: |
| Z3 before optimization | 28 | 22 | 0 |
| Z3 after optimization | 44 | 6 | 0 |
| cvc5 1.3.4 default | 30 | 20 | 0 |
| cvc5 1.3.4 split | 40 | 10 | 0 |

All 16 range cases move from unresolved to solved. For BN254 128-bit injectivity,
Z3 changes from `unknown` at the limit, with roughly 2,497 MiB peak RSS, to UNSAT
in 36.43 ms and 33.1 MiB. cvc5 split takes 290.82 ms on that case. The 253-bit
range witness case takes Z3 68.59 ms; both cvc5 configurations reach their limits.

These aggregate counts must not hide the remaining gap: the free-input Poseidon
case takes cvc5 about 81 ms and the equivalence case about 143 ms, while Z3 reaches
the limit on both. Across the two fields, free, partial, and equivalence Poseidon
account for all six unresolved Z3 cases. Fixed-input scaling is much better:
16 chained BN254 permutations take Z3 395.60 ms versus cvc5 383.22 ms, although
Z3 uses more memory (73.0 versus 48.7 MiB).

Raw results: [zk-before-after.json](../tests/finite_field/results/zk-before-after.json).

## Simplification measured separately

The next step adds standalone field rewriting: zero/one identities, constant
folding, double negation, combining like terms, additive equality cancellation,
and nonzero constant-coefficient elimination. Associative field declarations are
also normalized to flat applications. Products of symbolic sums are not expanded,
and unknown multiplicative factors are never cancelled.

`ff-simplify` additionally runs constant propagation between assertions. We
compare the saved pre-rewrite binary, the new binary's default strategy, and an
explicit `ff-simplify` preprocessing pass in the new binary. All three solve the
same 44 of 50 cases. The explicit preprocessing pass has a median wall-time ratio
of **1.020** versus the new default, over their solved cases: no general speedup.

| BN254 case | Before rewrites (ms) | New default (ms) | Explicit preprocessing (ms) |
| --- | ---: | ---: | ---: |
| 16 Poseidon permutations, fixed SAT | 396.59 | 381.45 | 392.41 |
| 16 Poseidon permutations, wrong output | 333.05 | 315.31 | 326.61 |
| 253-bit range witness | 67.21 | 55.92 | 60.69 |
| 64 Edwards additions, fixed SAT | 48.20 | 50.05 | 54.17 |
| One Edwards addition, partial witness | 31.39 | 32.21 | 25.66 |

Preprocessing increases peak RSS on the 16-permutation SAT case from 71.1 to
96.3 MiB. It therefore remains **opt-in**, rather than being inserted into every
QF_FF check. This does not disable standalone simplification or simplification
already used internally for model evaluation.

Raw results: [zk-simplification.json](../tests/finite_field/results/zk-simplification.json).

## Public ZK compiler benchmarks

The publicly available [CAV 2023 artifact](https://zenodo.org/records/7864537)
contains translation-validation queries for CirC, ZoK-CirC, and ZoKrates. We
selected a predetermined Cartesian product of 54 inputs: soundness/determinism,
three compilers, intact/last-constraint-removed/random-constraints-removed,
eight Boolean source variables, 4/16/64 source terms, a 255-bit field, and seed 0.
Selection was made before timing. This is a sample of the artifact, not the full
corpus and not a benchmark of SNARK proof generation.

The SMT formulas are unchanged. Only solver time limits, optional preprocessing,
and statistics/model commands are added. Inputs do not supply trusted status
annotations: we compare definite solver answers and independently evaluate every
returned SAT model against the original Boolean and field formula.

| Solver | Solved / 54 | Unknown | External timeout | Runtime error |
| --- | ---: | ---: | ---: | ---: |
| Z3 default | 32 | 22 | 0 | 0 |
| Z3 with ff-simplify | 32 | 22 | 0 | 0 |
| cvc5 default | 33 | 3 | 18 | 0 |
| cvc5 split | 32 | 2 | 17 | 3 |

| Query family | Z3 | Z3 + preprocessing | cvc5 default | cvc5 split |
| --- | ---: | ---: | ---: | ---: |
| Soundness (27) | 23 | 23 | 19 | 17 |
| Determinism (27) | 9 | 9 | 14 | 15 |

There are no SAT/UNSAT disagreements when both solvers return a definite answer.
Every returned SAT model passed the independent evaluator. Z3 solves six inputs
that default cvc5 does not solve within this budget, while default cvc5 solves
seven that Z3 does not. On their 26 commonly solved inputs, the geometric mean
Z3/cvc5 wall-time ratio is 1.207. Near-equal total counts therefore do not establish
performance parity: determinism is a material weakness in this Z3 implementation.

The three cvc5 split failures terminate with `CoCoA::ErrorInfo`, on
`sound-none / zokref / 16 terms`, `sound-random / zokcirc / 16 terms`, and
`sound-random / zokref / 16 terms`. The harness exits nonzero to retain these
reference failures. There are no Z3 runtime errors or missing SAT validations.

Raw results: [public-cav23.json](../tests/finite_field/results/public-cav23.json).
The [selection manifest](../tests/finite_field/fixtures/cav23-manifest.json)
contains each original filename and SHA-256. The downloader retrieves the ZIP
index and approximately 40 MB benchmark region instead of the Docker image;
extraction verifies ZIP CRCs. This does not verify the whole 997 MB archive hash,
which is separately recorded as published by the artifact authors.

```sh
python3 tests/finite_field/download_public_ff.py
python3 tests/finite_field/benchmark_public_ff.py \
  --z3 build-ff-cmake/z3 --cvc5 /path/to/cvc5 --repeat 3 --timeout 3
```

## Profiling and reproduction

Statistics include algebra calls and steps, eliminated variables, substitutions
and visited terms, basis calls and pairs, root calls, derived bit facts, budget
exhaustion, Boolean branches/conflicts, and BV fallback invocations. Timers cover
field encoding, algebra solving, final validation, and optional preprocessing.
Failed tactic attempts retain their counters. CLI statistics round small times;
the Python profiling harness separates parsing from checking and repeats parsing
with a previously validated modulus in the same context.

The [phase measurements](../tests/finite_field/results/zk-phases.json) show why
lower algebra work alone is not sufficient. On the 64-addition BLS12-381 Edwards
case with the modulus cached, preprocessing reduces algebra steps from 34,900 to
4,637, but its 19 ms cost raises total checking time from 18.64 to 22.56 ms.
On free-input BN254 Poseidon, both configurations exhaust the two-million-step
algebra budget and enter the BV fallback before returning `unknown`. These
single-run phase diagnostics explain the repeated CLI measurements; they are
not separate statistically repeated timing claims.

```sh
python3 tests/finite_field/zk_circuits.py
python3 tests/finite_field/benchmark_zk.py --large --repeat 3 --timeout 3 \
  --z3 build-ff-cmake/z3 --baseline /path/to/saved/baseline \
  --cvc5 /path/to/cvc5 --out /path/to/comparison.json
python3 tests/finite_field/benchmark_zk.py --large --simplify \
  --only z3,z3_simplify --repeat 3 --timeout 3 --cvc5 /path/to/cvc5
PYTHONPATH=build-ff-cmake/python Z3_LIBRARY_PATH=build-ff-cmake \
  python3 tests/finite_field/profile_zk.py
```

The fixture importer verifies the downloaded reference source hashes before
extracting parameter data; the MIT attribution is retained beside the fixture.
The fixture self-test checks all three published output coordinates and every
generated SAT witness. Additional tests cover 175 signed, wrapping, guarded and
unguarded decompositions including exhaustive core checks, and 22,560 exhaustive
rewrite evaluations, model reconstruction and proof-request rejection.

Fresh Release and Debug builds on the synced upstream base pass the native
finite-field, AST, and rational unit suites. Differential testing checks 1,000
random formulas with the Release CLI and 200 with the Debug CLI against exhaustive
enumeration and cvc5, including forced BV lowering and independent model checks.
The Python API regressions use the Release bindings. These checks supplement
the circuit and public-input model validation above.

## Next performance priority

Preserve circuit dependencies during symbolic solving and witness construction,
rather than expanding intermediate wires into large polynomials prematurely.
The public cases above also test Boolean/algebra interaction. Those profiles
should determine the next change; the current results do not justify claiming
production-circuit parity or proceeding directly to certificates. V2 obligations
are recorded in [QF_FF_CERTIFICATES.md](QF_FF_CERTIFICATES.md).
