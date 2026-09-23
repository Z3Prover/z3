# QF_FF: implementation, validation, and next milestones

This branch adds native prime-field syntax, models, C/C++/Python interfaces,
and an algebraic solver to Z3. Large-prime performance is part of the v1 target;
bit-vector lowering is the complete fallback and a correctness reference.
Certificates are explicitly deferred to v2.

## Current interface

Supported: arbitrary-precision prime moduli, canonical field numerals, n-ary
`ff.add`, `ff.mul`, `ff.bitsum`, unary `ff.neg`, equality, disequality, `distinct`,
Boolean combinations, field-valued ITEs, and multiple prime fields. Mixed moduli
are rejected. `ff.bitsum` means `x0 + 2*x1 + 4*x2 + ...`; it does **not** assert
that its arguments are bits.

Both `(as ff-1 F)` and `#f12m13` are accepted, and printing preserves the field
modulus. SMT-LIB sort parameters are arbitrary-precision, including in parser,
model, and Python `to_smt2()` round trips.

```smt2
(set-logic QF_FF)
(set-option :produce-models true)
(define-sort F () (_ FiniteField 13))
(declare-const x F)
(declare-const y F)
(assert (= (ff.add x y) (as ff1 F)))
(assert (= (ff.mul x y) (as ff1 F)))
(check-sat)
(get-model)
```

```python
from z3 import *
F = FiniteFieldSort(21888242871839275222246405745257275088548364400416034343698204186575808495617)
x, y = FiniteFieldElems("x y", F)
s = SolverFor("QF_FF")
s.add(7*x == 3, y == x*x)
assert s.check() == sat
assert s.model().eval(7*x).as_long() == 3
```

Use `SolverFor("QF_FF")` for explicit selection. The general `Solver()` also
routes field assertions through the field pipeline, including incremental and
assumption checks. Push/pop, repeated checks, unsat cores, model evaluation,
and context translation are covered by regression tests. The algebraic path
rebuilds its state at each check; incremental algebraic basis reuse is future work.
Ground combinations with uninterpreted functions, integers/reals, bit-vectors,
arrays and datatypes now have an SMT integration path. Use `Solver()` or logic
`ALL` for mixed queries; `SimpleSolver()` uses the SMT integration directly.
See [QF_FF_COMBINATION.md](QF_FF_COMBINATION.md) for its scope and performance limits.

The C API provides `Z3_mk_finite_field_sort`, `Z3_get_finite_field_sort_size`,
`Z3_mk_ff_add`, `Z3_mk_ff_mul`, `Z3_mk_ff_neg`, and `Z3_mk_ff_bitsum`.
Existing numeral constructors/readers work for fields. C++ adds
`context::finite_field_sort` and field arithmetic operators. Python adds
`FiniteFieldSort`, `FiniteFieldVal`, `FiniteFieldElem(s)`, and
`FiniteFieldBitsum`, with `+`, `-`, `*`, and nonnegative integer powers.

## Solving pipeline

The default strategy first runs `ff-simplify`: field rewriting, guarded zero-test
recovery, and acyclic wire elimination with model reconstruction. Constraints
defining Boolean field elements are preserved so wide range encodings remain
recognizable. Goals with free Boolean inputs retain the compact original atoms
for lazy Boolean/algebra search instead of expanding across choices. Set
`ff.preprocess=false` to measure the algebraic strategy without this pass.

1. `ff-solve`: sparse modular variable elimination, polynomial normalization,
   Buchberger Gröbner bases, univariate prime-field root extraction, and guarded
   bit-decomposition reasoning. Sparse occurrence indices update affected
   constraints instead of repeatedly traversing the whole circuit. For primes
   below 2^32, bounded F4-style batches reduce critical pairs with sparse modular
   row elimination. Arbitrary-precision Buchberger remains the larger-field
   backend. Both use the product and completed-pair chain criteria.
   Underdetermined systems also receive bounded sparse witness probes; each
   accepted assignment is checked against the full original problem.
2. `ff-sat`: Boolean SAT abstraction with lazy algebraic consistency checks.
   Field ITEs are eliminated with model reconstruction. Algebraic input
   provenance supplies learned conflict clauses. Disequalities are also encoded
   with inverse witnesses (`f != 0` iff there exists `t` with `f*t = 1`) for
   algebraic inconsistency checks.
3. SMT theory combination: for residual formulas, the SMT field plugin keeps
   the original field sorts and runs native
   modular algebra with acyclic wire DAG substitution. Candidate-model equality
   decisions connect functions, arrays and datatype selectors to the shared SMT
   search; explained algebraic conflicts reject inconsistent assignments. Exact
   bounded BV representations remain a fallback when native algebra is inconclusive.
   See [QF_FF_COMBINATION.md](QF_FF_COMBINATION.md) for the algorithm and measurements.

The standalone `ff2bv` tactic remains available as an exact reference encoding:
values occupy `ceil(log2(p))` bits with range restrictions, addition uses one
extra bit, and multiplication uses double width before reduction modulo p.
The default strategy now gives native SMT reasoning a chance before committing
to BV encoding; see [the measured comparison](QF_FF_PERFORMANCE_ROUND4.md).

SAT results from the algebraic backend are checked against the input
polynomials and original field AST. Failure to construct a verified witness
means fallback, never an UNSAT conclusion. Root extraction uses
`gcd(f, X^p-X)` to ensure roots belong to the requested prime field, rather than
an algebraic closure. The algebraic backend is bounded; the exact BV fallback
provides completeness in principle but can be expensive on cryptographic fields.

Bit-decomposition rules require explicit Booleanity for **every** participating
bit and `2^n <= p`. This excludes modular wraparound. Missing Booleanity and
wraparound have dedicated SAT regression tests.
Propagation repeats after elimination, so equalities exposed in later circuit
layers are recognized. Matching non-bit polynomial tails may be cancelled to
expose equal bit sums; all Boolean-domain and no-wrap premises remain required.

Parameters: `ff.max_steps` (default 2,000,000), `ff.max_terms` (4,096),
`ff.max_branches` (128), `ff.enum_bits` (8, capped at 12), `ff.bit_propagation`
(true, repeated propagation), `ff.batch` (true, sparse word-arithmetic batches),
`ff.sparse_witness` (true, bounded witness probes), and `ff.preprocess` (true).
These strategies can be disabled independently on a solver/tactic.
Their global SMT-LIB spellings are `:smt.ff.batch` and `:smt.ff.sparse_witness`. The SMT integration additionally supports `ff.root_split` (true) for
bounded product/square case splits, and `ff.boolean_split` (false) for optional
`x*x=x` domain clauses. The latter is off by default because held-out mixed
problems exposed SAT-search regressions. Enable it on an SMT solver with
`solver.set(**{"ff.boolean_split": True})`, or globally with SMT-LIB
`(set-option :smt.ff.boolean_split true)`. See
[QF_FF_ROOT_BENCHMARKS.md](QF_FF_ROOT_BENCHMARKS.md), and `ff.basis_cache` (true)
for bounded, exact basis reuse across native checks. The cache checks the modulus,
input polynomials and premise dependencies, and reports hit/miss counters.
Round 6 also enables `ff.disjunctive_bits` (preprocessing) and `ff.bit_bounds`
(algebraic bit propagation). The first rewrites candidate Boolean-domain
alternatives after constant propagation, using `(u=0 or v=0) iff u*v=0` in a
field. The second tests signed Boolean-sum intervals for possible integer
multiples of the modulus, retaining all used domain and equality premises.
Both have global `:smt.ff.*` spellings and can be disabled independently.
Experimental `ff.linear_split`, `ff.basis_bits`, and `ff.compact_matrix` are
false by default. These bounded prototypes did not meet the default acceptance
criterion in the development screen. See
[QF_FF_PERFORMANCE_ROUND6.md](QF_FF_PERFORMANCE_ROUND6.md) for algorithms,
measurements, and limits. A separate narrow BV carry backend is not implemented.

Round 7 enables `ff.compact_retry` for the `ff-solve` tactic (including its use
inside `ff-sat`). If the original polynomial encoding exceeds its size limit,
the tactic retries once with exact fresh-variable definitions. The retry receives
at most one sixteenth of `ff.max_steps`, also capped by the work remaining after
the original encoding. Cancellation and statistics include both attempts. This
does not add a retry to the native SMT theory. Disable it locally with
`ff.compact_retry=false` or globally with `:smt.ff.compact_retry false`.

Direct compact encoding and the other round-7 experiments remain opt-in:
`ff.compact_encoding`, `ff.sugar_pairs`, `ff.gm_pairs`, `ff.div_masks`,
`ff.geobucket`, `ff.small_coefficients`, `ff.adaptive_reduction`, and
`ff.bounded_elimination` all default to false. Their independent implementations
add no CoCoA dependency. See [QF_FF_PERFORMANCE_ROUND7.md](QF_FF_PERFORMANCE_ROUND7.md)
for the paired comparison, rejected variants, correctness checks, and limits.

Round 8 enables `ff.model_search`: bounded quotient minimal-polynomial
completion plus diversified, verified SAT witness probes. A clean 1,256-input
paired run gains two solves with no losses and comparable aggregate timing;
some short inputs incur additional probing time. Disable it with
`ff.model_search=false` locally or `:smt.ff.model_search false` globally.
Disabling `ff.sparse_witness` alone does not suppress slices while model search
is enabled. To retain only minimal-polynomial completion, disable model search
and set `ff.root_completion=true`.

Round 8 also adds independently controlled root-completion and matrix experiments:
`ff.root_completion` exposes bounded quotient minimal-polynomial deductions
without diversified witness search; `ff.quotient_field` reduces Frobenius field
axioms inside a certified small finite-dimensional quotient; and
`ff.adaptive_matrix` replaces the fixed symbolic-reducer count with conservative
storage accounting. These three switches remain false by default; model search
already includes the minimal-polynomial operation. Their deductions retain
input dependencies, work accounting, and shared cancellation. See
[QF_FF_PERFORMANCE_ROUND8.md](QF_FF_PERFORMANCE_ROUND8.md).

Round 9 adds `ff.lazy_matrix` (false), which stores symbolic matrix reducers as
basis references with monomial multipliers instead of expanded polynomial trees.
It supports both coefficient layouts and preserves conflict premises. Enable
`ff.adaptive_matrix` as well to admit more than 1,024 reducers. This removes most
symbolic-storage blockers in the targeted Small cohort without adding solves,
so it remains opt-in. New resource sub-counters identify the exact stopping
guard; matrix storage peaks are estimates per engine, and wrappers may sum them
across attempts. See [QF_FF_PERFORMANCE_ROUND9.md](QF_FF_PERFORMANCE_ROUND9.md).

A residual formula whose only free variables are explicitly Boolean
field elements can be evaluated exhaustively without polynomial expansion.
Characteristic-two variables need no additional Booleanity premise.
Resource cancellation is checked throughout algebra,
DAG conversion, and Boolean search. Setting a low algebra budget exercises the
complete fallback.

## Standalone simplification

`simplify` now supports field constant folding, zero/one identities, double
negation, associative/commutative normalization, combining like terms, additive
cancellation in equalities, and solving an equality with a single nonzero
constant coefficient. For example, over F13, `3*x + 2 = 5` becomes `x = 1`.
It never cancels an unknown multiplicative factor. Bit-sum positions are retained.
Addition and multiplication use flat associative ASTs with a shared binary
declaration, matching Z3's other associative arithmetic operators.

For pure field inputs, `ff-simplify` exposes affine wire definitions, propagates constants
and symbolic definitions through a shared expression DAG, and recovers zero-test
indicators from their two defining constraints. For example, `x*z=0` together
with `z=1-x*u` implies `z=ite(x=0,1,0)` regardless of the inverse witness `u`.
Both premises are required and retained. The complementary nonzero indicator
is handled too. Acyclic definitions can be removed without expanding a pure
circuit into polynomials; a model converter evaluates the original definitions
in dependency order. Remaining cyclic equations go to general equation
elimination or the algebraic backend. Boolean domain constraints, including
`b*b=b` and `b*(b-1)=0`, are protected from elimination through a wide sum.

It explicitly rejects proof-producing goals. An explicit invocation is:

```smt2
(check-sat-using
  (then ff-simplify (or-else ff-solve ff-sat smt)))
```

Unlike the previous constant-only pass, this pass is now included in the default
strategy. The on/off comparison and remaining regressions are recorded in
[QF_FF_SYMBOLIC_BENCHMARKS.md](QF_FF_SYMBOLIC_BENCHMARKS.md).
Rewrites are available independently through Python/C++/C simplification APIs.
They currently have no Lean reconstruction or field certificate support.

R1CS-style weighted sums of Boolean field variables are recognized directly
from their linear polynomials, including a directly pinned output variable.
The same explicit Booleanity and no-wrap conditions used for `ff.bitsum` apply.
This handles ordinary circuit exports without requiring a special bit-sum AST.

## Validation and performance

See [QF_FF_BENCHMARKS.md](QF_FF_BENCHMARKS.md) for recorded comparisons and their
limits. The checked-in harnesses generate small-field exhaustive comparisons,
validate returned models, exercise all three tactics, and compare with cvc5.
The second-round circuit, simplification and public benchmark measurements are
recorded in [QF_FF_ZK_BENCHMARKS.md](QF_FF_ZK_BENCHMARKS.md).

```sh
CXXFLAGS='' cmake -S . -B build-ff-cmake -G Ninja \
  -DCMAKE_BUILD_TYPE=Release -DZ3_BUILD_PYTHON_BINDINGS=ON \
  -DZ3_BUILD_TEST_EXECUTABLES=ON
cmake --build build-ff-cmake -j8
cmake --build build-ff-cmake --target test-z3 -j8
PYTHONPATH=build-ff-cmake/python Z3_LIBRARY_PATH=build-ff-cmake \
  python3 tests/finite_field/test_qfff.py --z3 build-ff-cmake/z3 \
  --cases 200 --cvc5 /path/to/cvc5
python3 tests/finite_field/benchmark_qfff.py --z3 build-ff-cmake/z3 --cvc5 /path/to/cvc5
python3 tests/finite_field/cvc5_regressions.py \
  --suite /path/to/cvc5/test/regress/cli/regress0/ff \
  --z3 build-ff-cmake/z3 --cvc5 /path/to/cvc5
```

cvc5 must be built with CoCoA. This checkout's initially installed cvc5 was not;
comparisons use the official cvc5 1.3.4 macOS ARM64 static GPL release as an
external executable. No cvc5 or CoCoA code is linked into Z3.

The `finite_field` C++ unit test is registered in `test-z3`. It checks modular
systems and, by exhaustive enumeration, that reported conflict subsets are
actually inconsistent. The algebra implementation has also been exercised under
AddressSanitizer and UndefinedBehaviorSanitizer. `api_smoke.cpp` checks the C++
interface on BN254.

## V1 closeout work remaining

Ground theory combination now integrates native algebra, explained conflicts,
shared equality arrangements and model reconstruction, with tested large-field
UF/array and Poseidon workloads. See [QF_FF_COMBINATION.md](QF_FF_COMBINATION.md).
Release readiness still needs:

- CI coverage for the finite-field Python regression harnesses, Linux builds,
  and sanitizer runs covering the latest contextual preprocessing. The C++
  `finite_field` test is registered in `test-z3`; the additional Python suites
  are currently run manually. Recorded Release/Debug measurements use macOS ARM64.
- End-to-end Blaster integration and acceptance runs on the actual exported
  circuits we intend to solve, including symbolic SAT and UNSAT queries, model
  reconstruction, incremental calls, assumptions, and resource limits.
- An explicit v1 contract for large moduli: callers must supply primes; the
  current probable-prime screen above 2^64 is not a proof of primality. The
  checked-primality/certificate work remains part of v2.

The latest runs already cover public CAV'23 circuit queries, parameterized
Poseidon permutations, range checks, and Edwards-curve gadgets. They establish
wins on selected workloads, not performance parity on complete production
circuits. See [QF_FF_SYMBOLIC_BENCHMARKS.md](QF_FF_SYMBOLIC_BENCHMARKS.md): the
current configuration solves 43/54 public queries, leaving 11 unknown at the
recorded limits. Broader compiler exports and harder symbolic witness searches
remain performance acceptance work; fixed-witness evaluation alone is insufficient.

Both the word-arithmetic batched reducer and arbitrary-precision Buchberger
backend are intentionally bounded. Larger systems may need scalable matrix
storage, arbitrary-precision batching, better pair selection, shared polynomial
DAGs, and incremental extension of bases. Exact bounded basis reuse is already
implemented. These are potential responses to measured bottlenecks,
not individually required algorithms for v1. Ground theory combination is
required; extension fields and general quantified solving remain outside v1.
Universally stated properties can still be verified when their counterexample
queries are quantifier-free.

General algebra and conflict-explanation experiments are recorded in
[QF_FF_PERFORMANCE_ROUND5.md](QF_FF_PERFORMANCE_ROUND5.md). The next round
compares bit-domain, interval, basis, matrix and model-search strategies with a
fresh confirmation sample; see [QF_FF_PERFORMANCE_ROUND6.md](QF_FF_PERFORMANCE_ROUND6.md).
The subsequent algebra and representation experiments are recorded in
[QF_FF_PERFORMANCE_ROUND7.md](QF_FF_PERFORMANCE_ROUND7.md).

## V2: checkable certificates

See [QF_FF_CERTIFICATES.md](QF_FF_CERTIFICATES.md) for the proposed recording and
checking contract, including the boundary with Blaster.

Proof-producing calls reject field solving with an explicit unsupported message.
Input dependency sets support cores and Boolean conflict clauses; they are
**not** algebraic certificates. Preserve this distinction.

The native AST and polynomial engine are independent of the BV encoder. Future
proof recording should retain polynomial multipliers for elimination and basis
reduction, inverse-witness introduction, prime-field root arguments, and the
Boolean resolution chain. Guarded bit-decomposition steps need explicit
Booleanity and no-wrap premises. The BV tactic's proof obligation is
range-constrained equivalence of translated terms plus model reconstruction.
A standalone checker should verify these obligations without trusting search.

Sort construction uses deterministic Miller–Rabin bases below 2^64, and strong
probable-prime screening for larger moduli. Large moduli are required to be prime;
screening is not a primality certificate. V2 must accept checked primality
witnesses or treat primality as an explicit theorem assumption.
