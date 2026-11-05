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

`Z3FiniteFieldTheory.fst` models the algebraic kernel shared by these modules
and mechanically verifies the field rewrites, sparse-polynomial operations,
ideal-preserving reduction, S-polynomials, ideal-membership certificates,
Rabinowitsch completion, finite-field equations, root splitting, candidate
validation, theory arrangements, and the canonical encoding equality used by
the bit-vector bridge.

`Z3FiniteFieldSearch.fst` is a second-stage audit of the preprocessing and
search code around that kernel. It adds executable models and 35 verified
lemmas for polynomial substitution, equality and disequality preservation,
affine elimination/model restoration, binary no-wrap reasoning, exhaustive
assignment construction over `F_p^n`, forward domain filtering, branch
closure, dependency-core lifting, learned blocking clauses, and checked
SAT/UNSAT/unknown results.

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

Second-stage F* coverage:

- `substitute_monomial` and `substitute_poly` implement the same
  `c*m*v^d -> c*m*value^d` transformation as
  `ff::engine::substitute`.
- `lemma_eval_substitute_monomial` and `lemma_eval_substitute_poly` prove
  that syntactic substitution equals evaluation in an environment updated
  with the definition's value.
- `lemma_substituted_system_model` and
  `lemma_substituted_disequalities_model` cover both `=0` and `!=0`
  constraints.
- `lemma_elimination_model_extension` and
  `lemma_elimination_problem_extension` prove the saved definition extends a
  residual model to a model of the pre-elimination problem.
- `verified_preprocess`, `elimination_preprocess`, and
  `compose_preprocess` package each stage with its reconstruction theorem and
  mechanically prove that a sequence of stages rebuilds models in reverse
  transformation order, matching the C++ restoration loop.
- `lemma_binary_bound`, `lemma_binary_injective`,
  `lemma_no_wrap_mod_injective`, and
  `lemma_no_wrap_binary_injective` justify digit equality only when every
  digit is Boolean and both integer packs lie below the modulus.
- `assignments`, `lemma_assignments_complete`, and
  `lemma_exhaustive_search_unsat` construct and prove completeness of the
  Cartesian product searched by `ff_tiny`.
- `lemma_filter_retains_solution` proves forward filtering cannot remove a
  satisfying value from the remaining variable's domain.

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

Second-stage F* coverage:

- Premises and Boolean branches are represented by numeric IDs interpreted
  through a predicate table, matching the dependency indices and signed atoms
  carried by the C++ frontends.
- `lemma_dependency_core_unsat` proves that inconsistency of a reported
  subset is sufficient to refute the full input conjunction.
- `lemma_unsat_core_blocking_clause` proves the learned `ff-sat` clause is
  exactly the negation of an inconsistent branch conjunction and therefore
  cannot block a combined model.
- `lemma_all_branches_closed` proves root/value/Boolean splitting may report
  UNSAT only after every covering branch is UNSAT. Any incomplete or
  exhausted branch prevents this conclusion.
- `lemma_validated_sat_result`, `lemma_checked_unsat_result`, and
  `lemma_unknown_is_safe` package the public three-way result contract:
  SAT carries a checked witness, UNSAT carries a checked dependency core, and
  stopping early yields only `unknown`.
- The bounded factor-split accounting added after the first audit controls
  whether an already-valid field clause is attempted; exhausting that local
  allowance emits no clause and has no semantic effect.

## Native checker: finite-field rewrite steps

`Z3FiniteFieldLemma.fst` lets the native F* checker decide the `rewrite`
steps that Z3's `ff_rewriter` records in QF_FF proofs. The native bridge
(`Z3Native.ml`, `cherry_runtime/native.cpp`) marshals `FiniteField p` sorts
as `FF<p>` and `ff` numerals, `ff.add`, `ff.mul`, `ff.neg`, and `ff.bitsum`
as interpreted declarations (`decl_kind` 300-304) whose `int_params` hold the
modulus (and, for numerals, the canonical residue). Before this change they
were opaque, so every FF rewrite was reported as an unmet obligation.

Both sides of a rewrite are translated to sparse polynomials over Z/pZ whose
variables are the maximal non-field subterms (variables, `ite` terms, array
reads, and so on). A step is accepted when

* the two terms have the same polynomial (constant folding of numerals,
  `ff.neg y = (p-1)*y`, `x + x = 2*x`, AC reordering and flattening,
  distribution, neutral and absorbing numerals);
* an equality `(= s t)` has a nonzero constant difference `s - t` (so it is
  `false`) or a difference that is `0` (so it is `true`); or
* two equalities have difference polynomials that are multiples of each other
  by factors `k`, `w`, checked as polynomial identities modulo `p`
  (isolating a variable or dividing by a leading coefficient); or
* a conditional term is compared with a numeral: `(= (ite c t u) k)` becomes
  `(and x (not c))` when `(= t k)` has a nonzero constant difference (so the
  then branch cannot be `k`) and `x` is the equality `(= u k)`, or any
  equality or constant already accepted as equivalent to it; symmetrically
  `(and x c)` when `(= u k)` has a nonzero constant difference and `x` is
  `(= t k)`. This is the shape of the rewrites in QF_FF field-3/case-02
  (`x` is `(= (ff.bitsum y y) 1)`) and field-7/case-01 (both branches differ
  from `k`, so `x` is `false`). The condition `c` must be the same term, the
  conjunction must have exactly two arguments, and `t`, `u`, `k` must be
  closed terms over the same `FF<p>`; a branch equal to `k`, a symbolic
  branch, or a numeral or branch of another modulus is not dropped.

The checker uses only the commutative-ring laws, so it never assumes that
`p` is prime. The factors `k`, `w` come from an untrusted modular-inverse
search and are re-checked, so over a composite modulus `2*x = 0` is not
rewritten to `x = 0`. The field equation `x^p = x` is not derived: `x*x = x`
in `F_2` stays unmet. Numerals outside `[0, p)`, a modulus below 2, operands
or declarations naming different moduli, and operations with the wrong arity
are left opaque.

Trust statement. `ff_model i project` is a hypothesis on the interpretation
`i`, conjoined into `Z3TheoryNormalize.normalization_model` exactly like
`bv_model`. It says: closed terms of sort `FF<p>` have a residue
`project p v` in `[0, p)` and equal values have equal residues; a numeral with
parameters `[p; n]` denotes `n`; and `ff.add`, `ff.mul`, `ff.neg`, `ff.bitsum`
over `FF<p>` denote the matching operation modulo `p` (`bitsum(a0, ..., an)
= sum 2^i * ai`). It is satisfied by the standard model in which `FF<p>`
values are residues. There is no `assume`, axiom, or admit, and the legacy
unified kernel is the only consumer; the sorted-semantics kernel does not use
`TN.equivalent`.

Dropping a branch in the conditional-term rule needs no inverse, only the
nonzero-constant test above, and the surviving equality is matched by itself
or by the checked rescaling above, so the rule is also valid over a composite
modulus. It never assumes the condition: the result must contain `c` or
`(not c)` as its second conjunct. The rule additionally uses
`Z3ArrayRewrite.term_ite_sound`, which is already part of
`Z3TheoryNormalize.normalization_model` through `A.rewrite_model`; the trust
statement is otherwise unchanged and no `assume`, axiom or admit is added.

## Native checker: finite-field theory lemmas

Z3's finite-field solver records its conflicts as `th-lemma` steps,
`((_ th-lemma ff pac (ff-pac ...)) C)`, whose conclusion `C` is a clause
over equalities of `FF<p>` terms. `Z3FiniteFieldLemma.exhaustive_clause`
decides such a step from `C` alone by evaluating it under every assignment
of residues in `[0, p)` to its leaves. The rule name and the producer's
`ff-pac` certificate are not read, so neither is trusted.

* Fragment. `eval_ff` and `eval_bool` interpret canonical numerals of
  modulus `p`; `ff.add`, `ff.mul`, `ff.neg` and `ff.bitsum` over `FF<p>`;
  `ite` over `FF<p>` with a Boolean condition (the then branch exactly when
  the condition holds); `=` between two `FF<p>` terms (equal residues) or two
  Boolean terms; `not`, n-ary `and` and `or`; `true` and `false`.
* Leaves. Every other closed `FF<p>` subterm is a leaf: constants,
  uninterpreted applications, numerals outside `[0, p)`, and numerals or
  operations whose parameters name another modulus or that have an unknown
  kind or a wrong arity. A leaf is opaque, so a clause that needs its value
  is not accepted. Leaves are identified by structural equality and the
  table records each once (`lemma_leaves_unique`).
* Not decided. A clause is left unmet when it is open (a bound variable),
  not Boolean, or contains a literal outside the fragment: an equality over
  another field or sort (so mixed moduli are rejected), `=>`, `xor`, a
  predicate, a quantifier. The modulus is that of the first numeral or field
  operation; a clause with neither is not decided.
* Bound. The number of assignments `p^n` (n leaves) must be at most
  `max_assignments = 4096`. `within_budget` checks this before anything is
  enumerated, multiplying one factor at a time and stopping as soon as the
  product exceeds the bound, so `p^n` is never formed for a large modulus;
  `lemma_within_budget` proves the bound. Exactly 4096 assignments are
  evaluated; one more factor leaves the step unmet.
* Premises. The rule applies only to a step without premises (the `es = []`
  branch of `Z3UnifiedProof.checked_theory_lemma`); it never assumes them.

Soundness is `lemma_exhaustive_clause_sound`: under `ff_model` (as an
existential, taken from `Z3TheoryNormalize.normalization_model`),
`boolean_rewrite_model` and `Z3ArrayRewrite.term_ite_sound`, all already
part of `Z3UnifiedProof.model_sound`, an accepted clause holds. The proof
shows that the evaluation of a closed term equals the residue (or truth
value) of its denotation when each leaf is given its own residue
(`lemma_eval_ff`, `lemma_eval_bool`); that the residues of the leaves in
any model lie in `[0, p)` (`lemma_projections_range`, from the range clause
of `ff_model`); and that `for_all_vectors` evaluates every vector of `n`
residues in `[0, p)` (`lemma_for_all_vectors`). Only evaluation in the ring
Z/pZ is used, so the rule never assumes that `p` is prime: the zero-product
clause of field-2/case-03 is accepted because it holds for all four
assignments over F_2, not by a field law, and the same clause modulo 4 is
rejected. No hypothesis, `assume`, axiom or admit is added and the trust
statement above is unchanged.

Tests: `Z3FiniteFieldLemmaTests` (normalized F* assertions: corpus clauses,
the kernel entry point, connectives, ite polarity, a composite modulus, a
mutated numeral, a dropped literal, the wrong field and mixed moduli,
out-of-range numerals, unknown operators, unsupported connectives and
predicates, open and non-Boolean terms, and the bound at 4096 and one factor
over); the native bridge group `checked-finite-field-theory-lemmas`
(`checked_theory_lemma` and `check_node` on parsed clauses, including 2^12
assignments at the bound, 2^13 and F_4099 over it, and steps with premises);
and the CLI cases for the twelve corpus certificates and a refutation over a
31-bit prime, which is out of the bound (its `th-lemma` is now checked by the
certificate replay below).

On the 25 hashed Pulse QF_FF certificates (pulse-run-40244844124-1, manifest
sha256 `d2c1b338...f9380`) every one of the 21 finite-field `th-lemma`
obligations is a premise-free clause over F_2, F_3, F_5, F_7 or F_17 with
one or two leaves (at most 17^2 = 289 assignments), and all 21 are decided:
the OCaml and Cherry checkers go from 13 ACCEPT / 12 PARTIAL / 0 REJECT to
25 ACCEPT / 0 PARTIAL / 0 REJECT with no pending obligation.

Fields and clauses beyond the bound are handled by the certificate replay
below when the producer's certificate uses only positive premises.

## Native checker: finite-field ideal certificates

Each finite-field `th-lemma` carries the solver's refutation certificate
`(ff-pac (ff-premises L0 ... Ln) ROOT (ff-support i ...))`: a DAG of
`(ff-input k)`, `(ff-add A B)` and `(ff-mul A c v1 ... vm)` nodes that
combines the equations of the producer's input table (`ff_evidence.cpp`,
`encoding::bind`) into the constant 1. `Z3FiniteFieldPac.check` replays it
for any modulus `p >= 2`; the kernel tries it after the exhaustive check, as
a new rule constructor `FiniteFieldPac` of `Z3UnifiedProof` for steps
without premises.

* Native view. `Z3Native.view_proof` (OCaml and Cherry) recognises only a
  `th-lemma` whose parameters are exactly `ff`, `pac` and an `ff-pac`
  application, and flattens the DAG iteratively, memoised by AST id: nodes
  are listed children first and refer to earlier positions. It expands at
  most 100000 nodes, accepts only Int numerals in [0, 2^32) as indices,
  field-sorted coefficients and Boolean premises, and otherwise yields no
  certificate, so the step stays pending. Nothing in the view is trusted.
* Input table. The checker re-derives the table from the premise ASTs in
  the producer's order: for each premise `(= a b)` or `(not (= a b))` over
  one `FF<p>`, the subterms of `a` and then of `b` are visited (arguments
  right to left, each term once); a canonical numeral is a constant, an
  `ff.add`/`ff.mul`/`ff.bitsum`/`ff.neg` term gets a fresh variable `v` and
  the definition `v - op(args)`, and any other term (constant, `ite`,
  uninterpreted application) is a variable. A positive premise contributes
  `a - b`. A negated premise allocates the producer's inverse witness, but its
  equation `w*(a - b) - 1` is never usable. The Fermat equations `x^p - x`,
  added by the producer for `p <= 31`, are not generated. The producer's
  bounds of 4096 variables and 8192 equations apply.
* Replay. Every node must refer to strictly earlier nodes, which rules out
  cycles and future, self and missing references. An `ff-mul` coefficient
  must be a canonical numeral of the same `FF<p>`, and its factor a sorted
  list of table variables. Polynomials are normalised: merge sort,
  coefficients reduced modulo p, zero terms dropped. The size of each
  operation (at most 16384 monomial cells) and the cumulative work (4000000)
  are checked before the operation. At most 100000 nodes are replayed.
* Acceptance. The root must normalise to the constant 1. Each used input
  must be a definition or a positive premise listed in the support, whose
  negation is a literal of the conclusion. The support must be strictly
  increasing, in range and exactly the set of used premises.

Soundness is `lemma_check_sound`. Give every table variable the residue of
its term. Under `ff_model`, every definition evaluates to 0 modulo p, and a
positive premise does when it holds. If the conclusion were false, every used
premise would hold. Each node is a sum or a monomial multiple of earlier nodes,
so it would also evaluate to 0. The root evaluates to 1, and `p >= 2`. The
lemma's hypotheses are `exists project. ff_model i project` (from
`Z3TheoryNormalize.normalization_model`) and `boolean_model`, `not_sound`,
`or_sound` and `eq_sound`. All are existing conjuncts of
`Z3UnifiedProof.model_sound`; no model contract changed. Only ring laws of
Z/pZ are used, so primality is neither assumed nor needed. The producer's
rule name and claimed result are not trusted. There is no `assume`, axiom or
admit, and no constructed witness: `ff_model` remains a hypothesis exactly
as `bv_model`.

Not checked (the step stays pending):

* certificates that use the inverse witness of a disequality. Replaying
  `w*(a - b) - 1` needs a prime modulus: `x*x = 0` and `x != 0` is
  satisfiable modulo 4. Discharging these would need a checked primality
  certificate.
* certificates that use the Fermat equations (fields up to 31, usually
  covered by the exhaustive check).
* malformed or over-budget certificates, steps with premises, and premises
  over different fields or outside equalities of field terms.

Tests: `Z3FiniteFieldPacTests` (normalised F* assertions: the unit-ideal
certificate over 2^31-1, 2^127-1 and Z/4Z; mutated coefficient and modulus;
false conclusions; missing, reordered, extra and negated premises; support
mutations; input indices out of the table; future, self and negative
references; a wrong root; and the inverse-witness certificate over 2^31-1
and Z/4Z). The native bridge group `checked-finite-field-certificates`
covers real producer certificates over 2^31-1, 2^61-1 and 2^127-1 and their
mutations. It also checks that each bound accepts up to the limit and
rejects beyond it, that steps with premises are not replayed, and that
inverse-witness and mixed refutations keep their obligations. For native
flattening it covers a 60-level shared DAG (61 nodes), a 200000-deep chain
and malformed indices, coefficients, node kinds and premises. The Cherry
`checker-tests` repeat the native flattening cases, and the CLI tests
accept `unit_ideal` over 2^31-1, 2^61-1 and 2^127-1 in batch and
interactive mode while the inverse-witness cases stay `PARTIAL 1`.

On twelve hashed QF_FF probes over fields beyond the exhaustive bound, both
checkers behave the same in batch and interactive mode. The following
refutations go from `PARTIAL 1` to `ACCEPT`: the unit ideal above over 4099,
2^31-1, 2^61-1 and 2^127-1, inverse uniqueness over 2^127-1, a product chain
over 2^61-1, and a three-bit range check (538 certificate nodes) and an XOR
gadget over the 254-bit BN254 scalar field. A refutation with one
positive-premise certificate and one inverse-witness certificate goes from
`PARTIAL 2` to `PARTIAL 1`. `x*x = 0, x != 0` stays `PARTIAL 1`, and two
controls refuted by rewriting stay `ACCEPT`. The 25 hashed Pulse QF_FF
certificates stay 25 `ACCEPT` on both checkers.

## Mechanical verification

The audit files contain no `admit`, `assume`, or declared axiom. They were
verified locally with F* `v2026.08.16` and the pinned Z3 `4.13.3` backend:

```text
Verified module: Z3FiniteFieldTheory
All verification conditions discharged successfully
Verified module: Z3FiniteFieldSearch
All verification conditions discharged successfully
```

Implementation refinements not modeled directly are monomial ordering,
hash/cache layout, sparse/dense matrix storage, Montgomery limb arithmetic,
pair scheduling, and resource accounting. The second-stage audit also leaves
the low-level correctness of the SAT CNF encoder, `ff_unique`'s union-find
storage, `ff_tiny`'s bitmask/trail implementation, and the C++ loops'
refinement to the pure recursive models as source-review obligations. Their
logical contracts are now proved: retained domains preserve every solution,
complete enumeration justifies UNSAT, all split branches must close, cores
must be subsets of original premises, and SAT models must pass original-input
validation. None of these implementation details is used as an independent
algebraic assumption.
