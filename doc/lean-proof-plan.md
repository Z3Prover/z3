# Z3 native certificates and Lean verification

## Goal and boundary

Preserve Z3's native proof-producing architecture and add an independent Lean
verification backend. Missing native proof evidence and checker correctness are
separate obligations. Ordinary Z3 behavior stays unchanged while the integration
is developed.

## Milestones

1. **Native Boolean proof exporter (implemented).** Use the existing proof API
   with proof generation enabled before solving. Export one propositional
   refutation together with its original source, assertion roots, typed native
   declarations, shared proof/term DAG, and rule inventory. Reject unsupported
   script semantics, nonpropositional assertions, missing proofs, and unsupported
   native shapes. Never present the artifact as independently verified.
2. **Kernel-checked Boolean vertical slice (basic, structural, and scoped rules implemented).**
   Extend the initial reconstructor with more Boolean proof rules and formalize
   the frontend encoding boundary. Account for preprocessing, fresh definitions,
   hypothesis scope, and the
   connection to the original assertions. Produce a theorem that the assertions
   imply False, with no sorry or solver-oracle axioms. Reject malformed/tampered
   certificates and unsupported inference rules.
3. **Equality and linear arithmetic.** Add uninterpreted functions and equality
   reasoning, then real/integer linear arithmetic with checked side conditions
   and certificates. Extend native evidence only where replay needs it. Complete
   each fragment end-to-end before adding another.
4. **Broader theories and integration.** Treat bit-vectors, arrays, quantifiers,
   strings, and nonlinear arithmetic as distinct extensions. Introduce a
   proof-required frontend that publishes certified unsat only after successful
   checking, preserves exact incremental/assumption contexts, and explicitly
   rejects unsupported configurations. Keep the C++ checker for diagnostics.

## First milestone deliverables

- `examples/python/proof_certificate.py`: opt-in CLI and Python exporter using
  existing APIs; no solver algorithm or public API changes.
- Versioned, topologically ordered JSON encoding of native ASTs, preserving
  declaration identity and complete arguments.
- Documentation in `examples/python/README` and CMake example integration.
- `examples/python/test_proof_certificate.py`: focused coverage of exact native
  DAG preservation, source/assertion binding,
  sharing, Boolean operators, named assertions, lexer/query restrictions, CLI
  behavior, and error paths. Run this in the existing Python-wheel CI job,
  separately from the dependency-free build-script tests.

## Acceptance boundary

For a supported unsat snapshot, produce a complete native proof bundle with
explicit unverified status. For sat, unknown, unsupported inputs, or missing
proof evidence, fail explicitly without a success-shaped certificate.
The exporter itself still makes no independent verification claim. The new
reconstruction slice publishes a Lean artifact only after checking succeeds,
and rejects unsupported proof rules rather than treating them as axioms.

## Lean environment

The `lean/` workspace pins Lean 4.34.0 and contains a small example proof library.
Run `./scripts/check_lean.sh` to build/check it, or
`./scripts/check_lean.sh /tmp/l.txt` to check a Lean source file. Both `.lean` and
`.txt` inputs are accepted, and files may import `Z3Proofs`.

The helper rechecks imported modules and enables warnings as errors. It checks
Lean source, not JSON. The separate `examples/python/proof_to_lean.py` consumer
validates JSON and invokes the helper before publishing generated Lean source.
Installation and usage are documented in `lean/README.md`.

## Current reconstruction slice

- Require the original SMT-LIB input separately from the certificate. Match
  source text and the exact parsed assertion structures; validate declaration
  signatures, topological node references, sorts, and proof conclusions.
- Reconstruct `asserted`, `unit-resolution`, `mp`, and Boolean `rewrite`,
  including derived clauses, both complement orientations, factoring, shared
  intermediate proofs, and ordered implication/equivalence elimination.
- Reconstruct Boolean equivalence `refl`, `symm`, and `trans`, as well as
  `monotonicity` for the supported Boolean connectives. Match application heads,
  arities, and oriented argument equivalences, including omitted reflexive
  premises and shared evidence. Use direct Lean proof terms, not truth tables.
- Reconstruct `and-elim` and `not-or-elim` for immediate operands, including
  singleton/n-ary connectives and native double-negation cancellation.
- Reconstruct `hypothesis` and `lemma` with explicit open-hypothesis tracking.
  Represent open proof DAG nodes as functions of their structural hypothesis
  sets, preserving sharing without closing a shared node globally. A lemma must
  consume a proof of false and discharge every open hypothesis into a
  complementary conclusion literal. Support nested lemmas, both complement
  orientations, compound literals, clause reordering, duplicates, and weakening.
  Reject a root with any undischarged hypotheses.
- Check each rewrite independently of the assertions by exhaustive cases over
  its own atoms and kernel reduction using `of_decide_eq_true rfl`. Rewrites and
  double-negation cancellation, as well as classical lemma steps, use temporary
  decidability witnesses, which are
  eliminated constructively from the refutation:
  `k (isFalse (fun hp => k (isTrue hp))) : False` for
  `k : Decidable p -> False`. The final theorem keeps arbitrary `Nat -> Prop`
  valuations, the original hypotheses, and no axiom dependencies.
- Generate shared Lean proposition definitions and explicit proof terms using
  Lean core logical rules. Do not introduce axioms, sorry, or solver calls to
  justify missing reasoning.
- Check with the pinned Lean toolchain before atomically publishing a `.lean`
  artifact. Fail explicitly for malformed certificates, changed assumptions,
  unsupported rules, and Lean errors.
- Exercise complete examples using `lean/examples/unit_resolution.smt2`,
  `lean/examples/boolean_rewrite.smt2`, and
  `lean/examples/boolean_structural.smt2`, plus scoped learning in
  `lean/examples/boolean_branching.smt2`. Cover Boolean truth tables, chained
  and shared proof steps, all Boolean congruence operators, both elimination
  orientations, large congruences without truth tables, forged structural
  premises/conclusions, false or unused rewrites, nested and shared hypothesis
  scopes, malformed lemmas, leaked hypotheses, and large learned clauses without
  truth tables.

Z3's SMT-LIB parser and the Python statement encoder remain part of the trusted
frontend. The source digest identifies the generated namespace; it is not the
input-binding check or a formal proof of parsing/encoding correctness.

Rewrite truth tables are exponential in the number of atoms in an individual
rewrite; large valid rewrites may exceed Lean's normal resource limits. A
checking failure never publishes an artifact.

Condensed transitivity (`trans*`), definition introduction, and other native
rules remain unsupported. These and a formalized encoding
connection must be addressed before claiming general Boolean proof support.
Arithmetic and other theories remain later milestones.

## Completed first-milestone evidence

- CMake/Ninja Release build with local Python bindings; full native build
  completed in 101.70 seconds. No legacy Python/make artifacts were present.
- 22 exporter tests passed against the local build, including exact DAG
  preservation, deep terms, escaped symbols, and command/fragment rejection.
- All 18 existing build-script tests passed with Python site packages disabled.
- Solver, Python bindings, help, and copied CMake examples were exercised.
- `boolean-unsat.proof.json` in this session's files directory contains an
  exported three-assertion refutation: 16 nodes, 12 declarations, and native
  asserted/mp/rewrite/unit-resolution steps. Its status is explicitly unverified.
