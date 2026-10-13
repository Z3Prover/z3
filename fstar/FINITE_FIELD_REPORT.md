# Finite-Field Formal Audit

## Scope

This audit covers the finite-field implementation introduced on the `ff`
branch:

- `src/ast/ff_decl_plugin.{h,cpp}`
- `src/ast/rewriter/ff_rewriter.h`
- `src/ast/rewriter/ff_bv_operations.h`
- `src/ast/ff/ff_solver.cpp`
- `src/ast/simplifiers/ff_{simplify,domain_analysis}.{h,cpp}`
- `src/math/ff/ff_{polynomial,certificate,f4,field,tiny,params}.{h,cpp}`
- `src/smt/theory_ff.cpp`
- `src/tactic/ff/ff_{solve,sat,unique,simplify,2bv}_tactic.cpp`

`Z3FiniteFieldTheory.fst` models the semantic kernel shared by these modules
and mechanically verifies the field rewrites, sparse-polynomial operations,
ideal-preserving reduction, S-polynomials, ideal-membership certificates,
Rabinowitsch completion, finite-field equations, root splitting, exhaustive
finite-domain reasoning, candidate validation, theory arrangements, and the
canonical encoding equality used by the bit-vector bridge.

## Result

The audited decision paths are sound under the declared prime-field
contract. Polynomial reductions and F4 rows are explicit ideal combinations;
UNSAT is returned only from a contradiction, exhaustive finite-domain
closure, or a unit-ideal derivation. Candidate SAT models are re-evaluated
against the original polynomial and AST constraints. Resource limits,
incomplete projections, slicing, bounded elimination, and failed heuristics
return `unknown` or fall back to an exact encoding.

The audit found one trust boundary:

| Severity | Module | Finding |
|---|---|---|
| High | `ff_decl_plugin.cpp` | For `p < 2^64`, the seven Miller-Rabin bases form a deterministic primality test. For larger moduli, bases 2 through 65 are only a probable-prime screen. Every downstream inverse, no-zero-divisor, factor-split, root-split, Groebner, F4, and BV-bridge argument requires that `p` actually be prime. A composite strong pseudoprime accepted by the screen would violate the advertised `FiniteField` semantics and could make SAT/UNSAT conclusions unsound. |

Large cryptographic moduli are an intended use case, so this audit does not
replace them with a `uint64` restriction. Instead, the F* model makes
primality an explicit constructor obligation. Closing the boundary requires
either a deterministic arbitrary-precision primality certificate/checker or
an API contract that accepts a trusted primality certificate with the
modulus. Adding more fixed Miller-Rabin bases would reduce risk but would not
establish the formal contract.

## Module audit

### Declarations and rewriting

- Numerals are canonical residues modulo `p`; pointer identity is therefore
  sufficient for distinct canonical numerals.
- Addition and multiplication are correctly marked associative and
  commutative. `ff.bitsum` remains positional.
- `ff_rewriter` flattens AC terms, combines only equal monomials, and solves
  affine equations only through a nonzero coefficient.
- `square_root` is deliberately incomplete: it recognizes integer-square
  coefficients and even syntactic factor multiplicities, never treating
  failure as proof that no field square root exists.
- `bitsum(a0,...,an)` denotes `sum(2^i*ai) mod p`; neither Booleanity nor
  no-wrap is assumed by constant folding.

F* coverage: `lemma_add_flatten`, `lemma_mul_flatten`,
`lemma_combine_coefficients`, `lemma_affine_solve`,
`lemma_disjunction_as_product`, `lemma_boolean_split`,
`lemma_zero_indicator`, `lemma_nonzero_indicator`, and the `bitsum`
definition.

### Polynomial representation and completion

- Sparse monomials are sorted variable multisets; polynomial evaluation is
  independent of the map/storage representation.
- Addition, scaling, multiplication, monomial multiplication, scalar
  reduction, and S-polynomial construction preserve their expected
  evaluation and ideal-membership semantics.
- Buchberger product/chain criteria affect scheduling only. Reduction uses a
  nonzero leading coefficient, and derived rows retain premise dependencies.
- Disequalities are completed with `g*t-1=0`; this is equivalent to `g != 0`
  exactly because nonzero field elements are invertible.
- Adding `x^p-x` preserves all and only base-field values.
- Root/value splitting is complete only when the retained roots enumerate all
  field roots. Positive-dimensional slicing is used only to find SAT
  candidates and cannot justify UNSAT.

F* coverage: `lemma_eval_monomial_append`, `lemma_eval_append`,
`lemma_eval_scale`, `lemma_eval_mul_monomial`, `lemma_eval_mul`,
`lemma_reduction_preserves_zero`, `lemma_s_polynomial_vanishes`,
`lemma_rabinowitsch`, `lemma_field_equation`,
`lemma_root_split_complete`, and `lemma_complete_enumeration`.

### Certificates and UNSAT

- `ff_certificate` records only input, monomial/scalar multiplication, and
  addition nodes. Replaying the DAG therefore reconstructs an explicit ideal
  combination of original equations.
- Normalizing a derived nonzero constant to one produces a unit-ideal
  certificate. Search order, pair criteria, and resource bounds are not
  trusted by the checker.
- V1 proof mode is explicitly rejected; the certificate machinery is not
  silently presented as a complete Z3 proof object.

F* coverage: `certificate`, `lemma_certificate_sound`, and
`lemma_unit_ideal_unsat`.

### Native, F4, fixed-width, and tiny solvers

- Native affine elimination restores definitions in reverse order and checks
  final assignments against original constraints.
- Bit propagation requires actual equations equivalent to `x^2=x`; the
  domain-analysis pass is only a syntax-preservation heuristic.
- `ff_tiny` exhaustively enumerates fields below its supported bound.
- F4 row operations are field-linear ideal operations. Minimal-polynomial
  candidates are checked for ideal membership before use, root isolation is
  intersected with `X^p-X`, and final models are independently validated.
- `field64` and `field256` are Montgomery representations of the same
  abstract field operations. Unsupported native-width configurations fall
  back instead of manufacturing an answer.

### SMT theory and tactics

- `theory_ff` keeps shared terms in the equality engine, requests
  arrangements when candidate values collide, and falls back per field to an
  exact bounded-BV encoding when native algebra is inconclusive.
- The BV bridge widens before arithmetic, constrains canonical values to
  `[0,p-1]`, and decodes model values before auxiliary declarations are
  removed.
- Factor and root clauses use only field no-zero-divisor laws.
- `ff-solve`, `ff-sat`, and `ff-unique` report UNSAT only after all required
  algebra/Boolean branches close and retain dependency support.
- Standalone tactics reject unsupported foreign consumers rather than
  pretending to combine theories.
- `ff-simplify` transformations preserve dependencies and model
  reconstruction; possible Boolean-domain matches are preserved, not assumed.

F* coverage: `lemma_validated_candidate_is_model`,
`lemma_arrangement_preserves_model`, and
`lemma_canonical_encoding_equality`, together with the rewrite and polynomial
lemmas above.

## Mechanical verification

The audit file contains no `admit`, `assume`, or declared axiom. It was
verified locally with F* `v2026.08.16` and the pinned Z3 `4.13.3` backend:

```text
Verified module: Z3FiniteFieldTheory
All verification conditions discharged successfully
```

Implementation refinements not modeled directly are monomial ordering,
hash/cache layout, sparse/dense matrix storage, Montgomery limb arithmetic,
pair scheduling, and resource accounting. Their audit obligation is that they
implement or select among the proved semantic operations; they are not used
as independent logical assumptions.
