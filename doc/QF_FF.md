# QF_FF: implementation, validation, and next milestones

This branch adds native prime-field syntax, models, C/C++/Python interfaces,
and an algebraic solver to Z3. Large-prime performance is part of the v1 target;
bit-vector lowering is the complete fallback and a correctness reference.
V2 has begun with standalone polynomial certificates; complete solver proofs
remain under development.

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
rebuilds each query, with bounded exact basis reuse across compatible checks.
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

The default strategy starts with a bounded `ff-unique` attempt. It propagates
functional dependencies, non-wrapping Boolean digits and zero-test gadgets
between circuit copies. The iterative encoder handles deep expression DAGs;
a shared local work allowance covers encoding, propagation and Boolean splits.
An unproductive pass yields to the existing solver without changing the goal.
`ff.unique_work` defaults to 1,000,000 work units; propagation gives up after
one tenth of that allowance without a new equality or value. There is also a
50,000-node limit and a default split depth of 16 (hard-capped at 64).
Disable the pass with `:smt.ff.unique false`; local exhaustion does not cancel
the subsequent solver. The optional `ff.unique_equalities` mode only exports
root-level consequences and is off by default.

Next, `ff-simplify` performs field rewriting, guarded zero-test
recovery, and acyclic wire elimination with model reconstruction. Constraints
defining Boolean field elements are preserved so wide range encodings remain
recognizable. Goals with free Boolean inputs retain the compact original atoms
for lazy Boolean/algebra search instead of expanding across choices. Set
`ff.preprocess=false` to measure the algebraic strategy without this pass.

1. `ff-solve`: sparse modular variable elimination, polynomial normalization,
   Buchberger Gröbner bases, univariate prime-field root extraction, and guarded
   bit-decomposition reasoning. Sparse occurrence indices update affected
   constraints instead of repeatedly traversing the whole circuit. After
   elimination, fields smaller than 64 receive bounded finite-domain search
   with forward checking and an explicit choice stack. On compilers with a
   128-bit integer type, odd primes below 2^256 can use fixed-width Montgomery
   arithmetic, F4 elimination and bounded quotient/root model construction.
   Failed random slices are inconclusive; only verified SAT assignments escape
   a slice. Remaining cases retain the arbitrary-precision Buchberger path,
   including its small-field sparse batches. Compilers without that integer
   type use the existing engine and tiny-field search; they report F4 as
   unsupported rather than failing compilation.
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
to BV encoding; see [the measured comparison](https://github.com/RSoulatIOHK/z3/blob/0a5210c9009ba5595521c39cefa7ef0a7b1d46aa/doc/QF_FF_PERFORMANCE_ROUND4.md).

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

## Configuration and limits

Use `z3 smt.ff.max_steps=1000 input.smt2` or
`(set-option :smt.ff.max_steps 1000)` for global options. Local solver/tactic
`ff.*` overrides take precedence. `ff.max_steps` defaults to 2,000,000 and
`ff.max_terms` to 4,096. `ff.f4`, `ff.tiny`, `ff.bit_propagation`,
`ff.root_split` and `ff.basis_cache` can be disabled independently. Use `z3 -pm:smt`
for the complete option list. `ff.enum_bits` is a tactic-local enumeration option.

Field/BV theory registration is demand-driven. In SMT combination, an
inconclusive field falls back independently; other fields still receive native
checks. A bridge remains active while its decoder terms survive. Popping the
last bridge permits native solving again. The normalization cache is bounded
and cleared on pop. Disabling BV internally yields unknown if fallback is needed.

The supported scope is quantifier-free prime fields. Extension fields and
complete quantified reasoning are outside this implementation. Above 64 bits,
moduli receive probable-prime screening, not primality certification.

## Proofs

Standalone reconstruction and independent checking are described in
[QF_FF_CERTIFICATES.md](QF_FF_CERTIFICATES.md) and the
[Alethe/PAC pipeline](QF_FF_PROOF_PIPELINE.md). They do not imply native Z3
`get-proof` support for the entire field solver. Mixed-theory proofs, root/field
closure, uniqueness and small-field-search traces remain incomplete. Conflict
premise sets alone are not certificates.

## Validation and research artifacts

The external harness and fixtures live in a pinned `z3test` checkout.
The `finite-field.yml` CI job runs both solver and certificate suites. Native
C++ unit tests remain in `src/test`. See [the regression test guide](https://github.com/RSoulatIOHK/z3test/blob/df7d7c5f66f603fc07991ece60c9a3e70eb91828/regressions/finite_field/README.md) for build and
check commands. Tests cover exact small-field oracles, models, resource recovery,
scopes, theory combination, simplification, APIs and proof rejection/mutation.

Research measurements, paper sources and plotting/corpus scripts have been
removed from the solver tree and preserved in a separate artifact repository.
Until that repository is published, the
[immutable published snapshot](https://github.com/RSoulatIOHK/z3/tree/0a5210c9009ba5595521c39cefa7ef0a7b1d46aa/doc)
keeps the existing PR figures and reports available. Those measurements identify
their original revisions; they are not automatically results for later fixes.
Experiments relying on previously ignored global budgets/toggles require reruns
before drawing option-specific conclusions.
