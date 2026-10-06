# Ground finite-field theory combination

Ground theory combination, including native large-field algebra, is implemented
for v1. The SMT plugin retains native field sorts in UF signatures, array
indices/ranges and datatype fields. Integer, real, bit-vector and Boolean
constraints use Z3's existing theories. Each prime field is solved separately.

## Native shared-theory search

At each field final check, the plugin collects relevant equality classes and
assigned field equality/disequality atoms. Foreign field-valued applications
are atomic algebraic variables; their arguments and interpretation remain with
the owning theories. There is no eager bit-vector encoding on this path.

The SMT plugin and `ff-solve` tactic both use `ff::field_problem` in `ast/ff`.
It applies standard rewriting and `solve-eqs` to a private dependent-expression
state before encoding residual equations for the bounded modular algebra engine.
Candidate digit variables are preserved during substitution to retain explicit
bit-domain constraints. This is a cost heuristic, not an assumption of Booleanity.
The standard model reconstruction trail restores eliminated variables; every
original field constraint is checked before exposing candidate values.

A problem represents one conjunction of signed field equalities. Only pinned,
pure term encodings may be cached across checks. Foreign field-valued terms are
purified to opaque constants; the SMT frontend supplies their interface facts
and validates model arrangements. The standalone tactic accepts only field
operators and free field constants, exports models for all original variables,
and maps conflict indices back to goal dependencies. It retains the small-bit
shortcut, compact-encoding retry and proof-mode rejection.

Each algebraic input has an explicit equality or disequality premise. Conflict
provenance produces a conditional theory lemma, with all substituted definitions
included conservatively. Conflict clauses preserve the exact SAT atoms: rewriting
them into different, algebraically equivalent atoms can prevent the current
assignment from being rejected. Dependency sets are not proof certificates.

When two shared field roots have the same candidate value, the plugin asks SAT
to decide their equality. This is a candidate-model arrangement, not an asserted
algebraic consequence. A false decision becomes an algebraic disequality on the
next check; a true decision lets UF congruence, arrays and datatypes propagate.
Only roots observed by other theories require arrangements. Private circuit
wires retain their algebraic values without unnecessary SAT equality decisions.
Values are always actual elements of F_p, so this approach does not assume
stable infiniteness. Small-field cardinality and array extensionality are tested.

Before polynomial solving, a bounded root pass recognizes products equal to zero
and equalities between syntactic squares. It emits clauses guarded by the exact
original equality: A²=B² implies A=B or A=-B, including characteristic two.
Repeated factors support quartic and other even-power reductions without general
factorization. Only integer-square residue representatives are recognized as
constant squares; failure is not evidence of a modular nonresidue. Product arity
is capped at 16, and branch choices are deduplicated. Clause emission caches are
cleared after backtracking and at the next search. Set `ff.root_split=false` to
disable this SMT pass; `ff root clauses` counts its emitted clauses.

The polynomial engine also recognizes a*X²+c=0 when -c/a has an integer-square
representative, directly enumerating the complete ±r root set. Other quadratics
continue through the existing field-membership gcd and root factorization.
See [QF_FF_ROOT_BENCHMARKS.md](https://github.com/RSoulatIOHK/z3/blob/0a5210c9009ba5595521c39cefa7ef0a7b1d46aa/doc/QF_FF_ROOT_BENCHMARKS.md) for the measurements.

Current equality facts and models are rebuilt after backtracking. A bounded exact basis cache can reuse compatible problems across assignments
and checks. Model factories
never invent extra elements when a field's finite domain is full.

## Exact fallback and lifecycle

If native algebra is inconclusive or reaches its local bound, the plugin enables
an exact BV bridge. For each field F_p, fresh private functions encode:F_p->BV_w
and decode:BV_w->F_p, with w=ceil(log2(p)), enforce:

- encode(t)<p, except in F_2 where every bit already lies in range;
- decode(encode(t))=t;
- exact modular encodings of field numerals and operations, widened before
  reduction so machine-width overflow cannot change the result.

Congruence gives both directions of equality preservation, including finite
cardinality across theory boundaries. Fallback is selected independently for each field, after checking the other
fields for native conflicts. A bridge stays enabled while its decoder enodes
survive; helpers must not later become unconstrained native variables. Popping
the last such enode permits native solving for that field again. Definition caches are invalidated on pop and at a new search, so
popped or interrupted axioms are re-emitted. Resource cancellation returns
unknown; it is not a reason to start a fresh expensive fallback. Private helpers
are hidden from returned models.

Field arithmetic operators do not also use EUF congruence-table entries: their
interpreted semantics enforces congruence. Foreign applications keep ordinary
congruence closure. This avoids the congruence-generation backtracking failure
encountered in the initial implementation.

The default solver tries the existing pure-field strategies before this mixed
SMT path. `SimpleSolver()` and the `smt` tactic exercise it directly. Use logic
`ALL` for mixed SMT-LIB formulas. Native algebra honors `ff.max_steps` (2,000,000)
and `ff.max_terms` (4,096), also exposed on direct SMT solvers. Setting the former
to zero forces fallback when residual polynomial work is required. Native checks,
conflicts, arrangements and BV fallback counts are reported in solver statistics.

Native wire normalization and bit propagation now track the actual premises
used by each derived constraint, rather than attaching every unrelated wire
definition to a conflict. The optional `ff.boolean_split` setting enables the guarded clause `x*x=x => x=0 or x=1`, exposing
Boolean field domains to the shared SAT search, including compound and foreign
field terms. It defaults to false because these clauses hurt some mixed SAT
searches. Both changes preserve conditional explanations; neither propagates
values merely sampled for a candidate model. See the
[generalization experiment](https://github.com/RSoulatIOHK/z3/blob/0a5210c9009ba5595521c39cefa7ef0a7b1d46aa/doc/QF_FF_PERFORMANCE_ROUND5.md).

The default `ff.bit_bounds` rule also propagates algebraic consequences of proved
Boolean domains using signed integer intervals and exact modulus-multiple tests.
It retains the domain/pin dependencies needed by a shared-theory conflict. This
adds no eager Boolean-domain split clauses. Disjunctive-domain rewriting is part
of QF_FF preprocessing (`ff.disjunctive_bits`), not an unconditional native SMT
rewrite of arbitrary Boolean structure. See [round 6](https://github.com/RSoulatIOHK/z3/blob/0a5210c9009ba5595521c39cefa7ef0a7b1d46aa/doc/QF_FF_PERFORMANCE_ROUND6.md).

Quantified solving is not an acceptance claim. Proof production remains
explicitly unsupported; see [QF_FF_CERTIFICATES.md](QF_FF_CERTIFICATES.md).

## Regression coverage

Release and Debug pass both combination suites. Coverage includes:

- field-valued functions and field arguments to integer/real/BV/Boolean functions;
- nested functions, arrays, stores, datatype selectors and multiple fields;
- finite-domain pigeonholes, exhaustive-index array extensionality and finite
  arrays with no original field-valued ground term;
- checking every original SAT assertion, helper hiding and tracked cores;
- push/pop, assumptions, translation, reset, late field introduction, different
  relevancy settings, cancellation and same-context recovery;
- 105 small-field queries independently enumerating both field values and entire
  unary-function tables, through default, SMT-tactic and persistent SMT solvers;
- the same mixed-theory examples, finite domains, incremental checks and 105
  exhaustive queries with native residual algebra forced to fall back;
- BN254 and BLS12-381 scalar-field nonlinear UFs, arrays, symbolic determinism,
  cores and repeated assumptions, with zero BV fallbacks;
- full-round Poseidon circuits using different multiplication schedules, with
  outputs compared through an opaque UF, for both SAT and UNSAT. Native model
  assertions and zero BV fallbacks are checked explicitly.

The current pure-field regression run also passes 500 random formulas against
independent enumeration and cvc5, 665 successful standalone native tactic checks,
API/model/resource tests, 20 guarded preprocessing families and five C++ tests
covering finite fields, SMT context, model evaluation and parametric datatypes.

```sh
PYTHONPATH=build-ff-cmake/python Z3_LIBRARY_PATH=build-ff-cmake \
  python3 tests/finite_field/test_ff_combination.py
PYTHONPATH=build-ff-cmake/python Z3_LIBRARY_PATH=build-ff-cmake \
  python3 tests/finite_field/test_ff_large_combination.py
```

## Measured large-field workloads

The table below records the native-combination baseline before the root-clause
optimization. The subsequent before/after results are recorded in
[QF_FF_ROOT_BENCHMARKS.md](https://github.com/RSoulatIOHK/z3/blob/0a5210c9009ba5595521c39cefa7ef0a7b1d46aa/doc/QF_FF_ROOT_BENCHMARKS.md).

`benchmark_ff_combination.py` generates nonlinear mixed UF/array queries and
one/four chained Poseidon permutations, over both cryptographic fields. It
compares direct SMT, the default pipeline, both cvc5 1.3.4 field backends with
CoCoA, and the previous
BV-only plugin on the non-Poseidon cases. SAT models are checked separately,
against every original assertion. Fresh-process wall times include parsing and
modulus validation; they are not solver-only times. Results retain binary and
input hashes, repeated timings, native counters and peak process memory.

See [large-combination.json](../tests/finite_field/results/large-combination.json).
The harness uses a three-second solver limit and a five-second external deadline
because a solver may not promptly interrupt an external algebra operation.
These are generated combination workloads, not exported production ZK programs.

Both Z3 paths solve all 16 cases in all three repetitions. Each cvc5 backend
solves eight and reaches the external deadline on the eight Poseidon cases.
Direct SMT uses zero
BV fallbacks, and all six SAT cases have their models checked. The previous
BV-only plugin returns unknown on all eight non-Poseidon cases at the solver
limit. Selected medians (seconds, fresh-process wall time):

| BN254 workload | Native SMT | Default pipeline | cvc5 default | cvc5 split |
| --- | ---: | ---: | ---: | ---: |
| Nonlinear UF contradiction | 0.042 | 0.042 | 0.032 | 0.025 |
| Array index contradiction | 0.044 | 0.044 | 0.052 | 0.082 |
| Symbolic quartic/UF contradiction | 0.086 | 0.085 | 0.043 | 0.028 |
| Poseidon, one permutation per circuit, SAT | 0.353 | 0.191 | >5 (external timeout) | >5 (external timeout) |
| Poseidon, four permutations per circuit, SAT | 1.364 | 0.699 | >5 (external timeout) | >5 (external timeout) |
| Poseidon, four permutations per circuit, equivalence | 1.234 | 0.682 | >5 (external timeout) | >5 (external timeout) |

Poseidon compares two circuits with independently ordered x^5 multiplication
schedules; the condition relates their outputs through a UF. cvc5 is faster on
some small root problems. These results support the specific large-field
combination acceptance cases, not a blanket performance claim.

## Remaining performance work

The core large-field combination mechanism is complete for the ground v1 scope.
The bounded algebra engine can still select the expensive exact BV fallback on
hard multivariate systems. Incremental basis reuse, tighter dependency sets and
additional algebra algorithms are potential responses to measured bottlenecks.
Production Blaster circuit acceptance, Linux/CI coverage and v2 certificates are
separate remaining milestones; selected benchmark wins do not imply universal
performance superiority over cvc5.
