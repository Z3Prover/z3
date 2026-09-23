# QF_FF: symbolic determinism and circuit-aware preprocessing

Third-round measurements, 2026-09-22, on the same macOS ARM64 machine and
upstream base `cb83665b3` as the [previous round](QF_FF_ZK_BENCHMARKS.md).
Certificates and Lean proof reconstruction remain v2 work.

## What changed

- Affine equality rewriting exposes wire definitions even in forms such as
  `t = c - a*x`. It prefers existing acyclic definitions and unit coefficients
  instead of hiding a usable output behind a cyclic input definition. Monomial
  ordering uses retained factors instead of recyclable temporary AST ids.
- Constants propagate before symbolic elimination. This matters for long
  Edwards chains: expanding before discovering the known denominator values
  had caused a regression, which the full circuit suite caught.
- Acyclic wires are normalized bottom-up with a shared cache. Definitions are
  removed with a model reconstruction map; cycles remain constraints. Pure
  acyclic circuits need no symbolic expansion at all. All rules are structural;
  no circuit names, expected answers, or benchmark filenames enter the solver.
- From `x*z=0` and `z=1+c*x*u`, infer `z=ite(x=0,1,0)`. The nonzero indicator
  has the complementary rule. Both premises remain and the derived equality
  carries their dependencies; different inverse witnesses no longer hide
  identical zero tests.
- Explicit Boolean field domains are protected from elimination through wide
  sums, preserving the existing no-wrap range recognizer. A residual circuit
  with at most eight bit inputs can be checked by exhaustive DAG evaluation;
  an UNSAT answer requires explicit domains for every variable (or F2).
- Preprocessing is adaptive: goals with free Boolean inputs retain their
  compact atoms for lazy Boolean/algebra search. Expanding across those choices
  regressed public soundness queries during development. General field
  simplification remains available independently through `simplify`.

The resulting `ff-simplify` pass is enabled by default. Python callers can
disable it with `solver.set(**{'ff.preprocess': False})`. The measured raw tactic
is `or-else(ff-solve, ff-sat, then(ff2bv, qfbv))`, so the on/off comparison uses
the same binary, field rewriter, algebra engine, budgets, and fallback.

## Protocol

Successful timings are medians of three fresh processes. The internal solver
limit is 3 seconds and the external guard is 5 seconds; unknown, external timeout,
and runtime error are recorded separately. These are local measurements without
machine-wide performance isolation. Wall time includes startup, parsing and
modulus screening. Peak RSS is measured separately per process. cvc5 is the
official 1.3.4 ARM64 GPL binary with CoCoA, tested in default and split modes.

Every SAT result is rerun outside timing and its complete assignment checked
against the original input. Circuit checks use independent integer modular
evaluation; public inputs use an independent Boolean/field evaluator. UNSAT
answers are compared between solvers; no UNSAT certificates are claimed. Raw
files record input hashes, binary hashes, commands, individual runs and counters.

The public corpus remains the predetermined 54-case sample of the
[CAV 2023 artifact](https://zenodo.org/records/7864537): three compilers,
soundness/determinism, three constraint-removal settings, 4/16/64 source terms,
eight source variables, a 255-bit field, and seed 0. It measures circuit/compiler
queries, not SNARK proof-generation throughput.

## Circuit results

| Configuration | Solved / 50 | Unknown | External timeout |
| --- | ---: | ---: | ---: |
| Z3 default, adaptive preprocessing | **50** | 0 | 0 |
| Same Z3 binary, raw field strategy | 44 | 6 | 0 |
| cvc5 default | 30 | 14 | 6 |
| cvc5 split | 40 | 4 | 6 |

All six formerly unresolved symbolic Poseidon cases are now solved. Each row
below is a fresh-process median, including startup and parsing. The free-input
case asks for any valid circuit witness; the partial case leaves only a two-bit
input unknown while pinning an output. Neither is a claim of solving general
Poseidon preimages. Equivalence compares two multiplication schedules for the
same reference permutation.

| Field / Poseidon query | Z3 (ms) | cvc5 default (ms) | cvc5 split (ms) |
| --- | ---: | ---: | ---: |
| BN254 free inputs | **41.85** | 76.88 | 77.03 |
| BLS12-381 scalar free inputs | **42.87** | 76.76 | 76.89 |
| BN254 symbolic equivalence | **110.51** | 137.22 | 138.80 |
| BLS12-381 scalar symbolic equivalence | **111.21** | 139.75 | 138.11 |
| BN254 partial inputs | **99.96** | external timeout | external timeout |
| BLS12-381 scalar partial inputs | **105.56** | external timeout | external timeout |

Free-input Poseidon is about 1.8 times faster than cvc5 and equivalence about
1.25 times faster on these instances. The raw strategy returns `unknown` on all
six at the 3-second limit. Sixteen fixed-input BN254 permutations take 336.44 ms
versus 367.95 ms for default cvc5; the BLS12-381 version takes 338.60 versus
386.61 ms. These wins do not extend to every size: cvc5 remains faster on several
small fixed-input and Edwards cases.

Preprocessing adds **1.6% median wall time** over the 44 cases both Z3 variants
solve (geometric-mean ratio 1.027). It therefore pays for itself in new coverage
and the symbolic workloads, not as a uniform speedup. The BN254 253-bit range
witness increases from 54.31 to 64.49 ms. Peak RSS for 16 fixed-input BN254
permutations rises from 71.5 to 89.4 MiB, versus cvc5's 48.0 MiB. The long Edwards
regression was removed: the 64-addition BN254 SAT case takes 46.31 ms with
preprocessing versus 48.59 ms raw.

Raw results: [zk-round3.json](../tests/finite_field/results/zk-round3.json).

## Public compiler results

| Configuration | Solved / 54 | Soundness / 27 | Determinism / 27 | Runtime errors |
| --- | ---: | ---: | ---: | ---: |
| Z3 default | **43** | **23** | **20** | 0 |
| Same Z3 binary, raw strategy | 32 | 23 | 9 | 0 |
| cvc5 default | 33 | 19 | 14 | 0 |
| cvc5 split | 32 | 17 | 15 | 3 |

Preprocessing adds eleven solved determinism queries and preserves every raw
soundness result. On 29 inputs solved by both Z3 and default cvc5, the geometric
mean Z3/cvc5 wall-time ratio is 1.037; on 28 shared with split cvc5 it is 0.524.
The coverage win is stronger than the timing claim: default cvc5 still wins
several small shared cases. Compared with raw Z3 on their 32 shared solved
inputs, the geometric-mean ratio is 0.954.

There are no definite-answer disagreements and every returned SAT model passes
independent evaluation of the original input. The harness exits nonzero solely
for the same three `CoCoA::ErrorInfo` failures in cvc5 split recorded in the
previous round. Z3 returns `unknown` on eleven cases; default cvc5 has three
unknowns and eighteen external timeouts, and split has two unknowns and
seventeen external timeouts in addition to its three errors.

An earlier exploratory preprocessing variant solved 21 determinism cases but
regressed other circuit queries. The final adaptive configuration solves 20,
while retaining the original soundness coverage and all 50 circuit cases.
The unresolved determinism cases comprise six weakened-circuit queries and
the intact 16-term ZoKrates query. Residual expansion on that intact query and
witness construction for the weakened circuits remain performance work.

Raw results: [public-cav23-round3.json](../tests/finite_field/results/public-cav23-round3.json).

## Larger symbolic Poseidon check

After tuning on the one-permutation cases, the fixed implementation was tested
on twelve additional cases: two and four chained permutations, free/partial
inputs/equivalence, in both fields. Z3 solves **12/12**; each cvc5 configuration
solves **8/12**, with the four partial-input cases reaching the external guard.
Every SAT model passes the same independent R1CS evaluator. All definite
answers agree.

| Four-permutation query | Z3 (ms) | cvc5 default (ms) | cvc5 split (ms) |
| --- | ---: | ---: | ---: |
| BN254 free | **98.42** | 882.19 | 879.58 |
| BLS12-381 scalar free | **100.53** | 879.51 | 882.81 |
| BN254 equivalence | **376.65** | 1,685.38 | 1,696.94 |
| BLS12-381 scalar equivalence | **378.70** | 1,697.82 | 1,703.73 |
| BN254 partial | **338.51** | external timeout | external timeout |
| BLS12-381 scalar partial | **338.89** | external timeout | external timeout |

The four-permutation cases show about 8.8–9.0 times faster free-witness solving
and 4.5 times faster equivalence checking. This is a scaling check of the same
reference gadgets, not an independent production-circuit corpus. No solver
changes were made after running these additional cases.

Raw results: [symbolic-scaling.json](../tests/finite_field/results/symbolic-scaling.json).

## Reproduction

```sh
python3 tests/finite_field/benchmark_zk.py --large --raw \
  --only z3,z3_raw,cvc5,cvc5_split --repeat 3 --timeout 3 \
  --cvc5 /path/to/cvc5 --out tests/finite_field/results/zk-round3.json
python3 tests/finite_field/benchmark_public_ff.py \
  --only z3,z3_raw,cvc5,cvc5_split --repeat 3 --timeout 3 \
  --cvc5 /path/to/cvc5 --out tests/finite_field/results/public-cav23-round3.json
python3 tests/finite_field/benchmark_zk.py --symbolic-scaling \
  --only z3,cvc5,cvc5_split --repeat 3 --timeout 3 \
  --cvc5 /path/to/cvc5 --out tests/finite_field/results/symbolic-scaling.json
```

## Correctness checks

Release differential testing covers 1,000 random formulas against exhaustive
enumeration and cvc5, including native tactics, forced BV lowering, models and
API behavior. The Debug CLI passes another 200 formulas and the native field,
AST and rational unit suites. Rewriting has 22,560 exhaustive evaluations and
idempotence checks. The existing 175 guarded decomposition tests include
exhaustive returned-core checks. The final Debug binary also solves and validates
all ten single-permutation Poseidon cases (fixed, partial, free and equivalence,
in both fields) with assertions enabled. All three recorded performance suites
were verified to use the same final Release binary hash.

New tests exercise zero and nonzero indicators in five characteristics, scaled
and composite inputs, removal of either premise, exhaustive small-field core
checking, both Booleanity encodings, acyclic model reconstruction, cyclic
definitions, and complete small-bit UNSAT coverage. Proof requests still reject
unsupported field certificates. V2 obligations are documented in
[QF_FF_CERTIFICATES.md](QF_FF_CERTIFICATES.md).
