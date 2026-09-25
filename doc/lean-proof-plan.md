# Z3 native certificates and Lean verification

## Goal and boundary

Preserve Z3's native proof-producing architecture and add an independent Lean
verification backend. Missing native proof evidence and checker correctness are
separate obligations. Ordinary Z3 behavior stays unchanged while the integration
is developed.

## Regression methodology

Proof checking in Z3 is currently disjointed, and the remaining work is larger
than a handful of PRs. Before extending Lean coverage further, establish one
regression methodology and suite that covers every proof-producing path:

- The `sat.smt=true` core has a modular self-checker (`euf_proof_checker` with
  theory plugins for arithmetic `farkas`/`bound`/`implied-eq`/`cut`,
  bit-vectors, quantifiers, Tseitin, and `distinct`). It falls back to calling
  the SMT solver for lemmas it does not handle; such a fallback is not a check.
- The legacy core (`sat.smt=false`) produces proof objects with
  `produce-proofs` and clause proofs with `smt.clause_proof` /
  `solver.proof.log`, checked by `solver.proof.check` and
  `solver.proof.check_rup`, optionally saved via `solver.proof.save` or
  `solver.proof.trim`. The clause-proof logging is not yet rock solid.
- `theory_lra` has ad hoc self-validation behind `smt.arith.validate`, and the
  SMT context validates cores behind `smt.core.validate`.

The suite is a matrix of benchmarks x parameters x checking method.

**Benchmarks.** QF_UF, QF_LIA, QF_LRA, QF_NIA, QF_AUFLIA from the SMT-LIB
release archives, plus the z3test regressions and the generated propositional
families from the scaling survey. Curate per logic a small canary set (seconds,
mixed sat/unsat) for PR CI and a larger set for nightly runs. Record the
expected result of every instance from a proof-free run.

**Parameters.**
1. `sat.smt=true` with clause-proof checking enabled (`solver.proof.check`,
   `solver.proof.check_rup`) and `solver.proof.log` written for external replay.
2. `sat.smt=false` with `produce-proofs=true` (legacy proof objects).
3. `sat.smt=false` with `smt.clause_proof=true` (legacy clause proofs).
4. Self-validation oracles: `smt.arith.validate=true`, `smt.core.validate=true`.
   These use the solver to check itself and only count as diagnostics.

**Checking method.** Self checker (the built-in checkers above) and external
checker (the C++ `proof_checker` for proof objects, DRAT tools for pure clause
trails, and Lean reconstruction for the fragments it supports).

**Recorded per cell.** Result agreement with the proof-free run, time, proof
size, checker verdict, number of self-checker fallbacks, and a failure class:
`verified`, `unverified-fallback`, `checker-rejected`, `no-proof`, `crash`,
`timeout`. A cell that passes only through fallback is never reported as
verified. Every `checker-rejected` and `crash` instance is minimized and added
as a regression test with its parameter cell.

**Coverage tracking.** For each logic and parameter cell, tabulate the proof
rules and theory-lemma kinds that occur and which checkers accept each kind.
This replaces guessing which rule to support next; the Boolean survey below is
the first instance of this method.

**First deliverable.** A runner in `examples/python/` that takes a benchmark
list and emits one JSON record per cell, following `proof_preprocessing.py`,
together with a canary list per logic and a summary table. The runner must
exit nonzero on `checker-rejected` and `crash`, and must report fallbacks
separately from verified results.

## Milestones

1. **Native Boolean proof exporter (implemented).** Use the existing proof API
   with proof generation enabled before solving. Export one propositional
   refutation together with its original source, assertion roots, typed native
   declarations, shared proof/term DAG, and rule inventory. Reject unsupported
   script semantics, nonpropositional assertions, missing proofs, and unsupported
   native shapes. Never present the artifact as independently verified.
2. **Kernel-checked Boolean vertical slice (basic, structural, scoped, and gate-clause rules implemented).**
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
5. **External consumers as gradual milestones.** Each is one end-to-end test in
   the regression matrix: the Rutgers project consuming Z3 certificates
   end-to-end; a Z3-native path in Lean-smt, which currently only supports
   CVC5; and a certifying mode for F*, whose infrastructure is not yet set up
   here. Start with the consumer whose fragment the checkers already cover.

The regression methodology above is the current top priority and gates the
order in which milestones 3 to 5 proceed.

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
- Reconstruct condensed Boolean transitivity (`trans*`) by finding a path
  through the supplied equivalences, reversing edges as needed. Support
  reordered, repeated, cyclic, and redundant evidence, and reflexive empty
  paths. Validate every premise, preserve the hypotheses of all supplied
  premises, and reject disconnected endpoints. Balance the generated
  `Iff.trans` terms so long paths do not require deeply nested compositions.
- Reconstruct `and-elim` and `not-or-elim` for immediate operands, including
  singleton/n-ary connectives and native double-negation cancellation.
- Reconstruct `iff-true` and `iff-false` from their exact Boolean premises and
  ordered endpoints, using axiom-free logical terms and preserving scope.
- Reconstruct `hypothesis` and `lemma` with explicit open-hypothesis tracking.
  Represent open proof DAG nodes as functions of their structural hypothesis
  sets, preserving sharing without closing a shared node globally. A lemma must
  consume a proof of false and discharge every open hypothesis into a
  complementary conclusion literal. Support nested lemmas, both complement
  orientations, compound literals, clause reordering, duplicates, and weakening.
  Reject a root with any undischarged hypotheses.
- Reconstruct Boolean `def-axiom` clauses as independent Lean theorems, never
  as trusted axioms. Support the gate schemas for not, n-ary and/or, implication,
  Boolean equivalence, xor, and Boolean ite, plus complementary literals and
  constant tautologies. Handle negated/compound operands and reordered,
  duplicated, or weakened clauses using direct proof terms over one gate's
  immediate operands, not truth tables over nested atoms. Reject invalid or
  unsupported clauses, including unused ones. Fresh definitions remain separate.
- Check each rewrite independently of the assertions by exhaustive cases over
  its own atoms and kernel reduction using `of_decide_eq_true rfl`. Rewrites and
  double-negation cancellation, gate clauses, and classical lemma steps use
  temporary decidability witnesses, which are eliminated constructively from
  the refutation:
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
  `lean/examples/boolean_branching.smt2` and gate clauses in
  `lean/examples/boolean_def_axiom.smt2`. Cover Boolean truth tables, chained
  and shared proof steps, all Boolean congruence operators, both elimination
  orientations, large congruences without truth tables, forged structural
  premises/conclusions, false or unused rewrites, nested and shared hypothesis
  scopes, malformed lemmas, leaked hypotheses, forged/unused gate clauses, and
  large gate and learned clauses without truth tables. Cover condensed
  transitivity with reversed/cyclic paths, structural sharing, scoped premises,
  disconnected endpoints, and long equivalence chains.

Z3's SMT-LIB parser and the Python statement encoder remain part of the trusted
frontend. The source digest identifies the generated namespace; it is not the
input-binding check or a formal proof of parsing/encoding correctness.

Rewrite truth tables are exponential in the number of atoms in an individual
rewrite; large valid rewrites may exceed Lean's normal resource limits. A
checking failure never publishes an artifact.

Definition introduction and other native rules remain unsupported. These and
a formalized encoding connection must be addressed before claiming general
Boolean proof support. Arithmetic and other theories remain later milestones.

### Scaling survey (2026-09-25)

A survey of export, reconstruction, and Lean checking over generated
propositional families (pigeonhole, xor cycles, implication chains, wide de
Morgan, nested equivalences, random 3-SAT) shows that rule coverage is no longer
the bottleneck: every rule the default pipeline emits on propositional inputs is
supported. Two resource cliffs remain, both on the Lean side:

- The main theorem is one nested `let` chain. Lean's elaborator hits its
  recursion limit at roughly 500 bindings (about 1000 proof nodes). Raising
  `maxRecDepth` inside the theorem recovers chains and random 3-SAT, but the
  chain is superlinear to elaborate; pigeonhole with five holes emits 5391
  steps for 1939 nodes because shared lemma nodes are re-instantiated per
  hypothesis scope. Emit steps as top-level lemmas parameterized by the
  assertion hypotheses, or as a tactic `have` chain, and share instantiations.
- Rewrites are checked by truth tables, exponential in the atom count: eight
  atoms take seconds, twelve exceed the heartbeat limit. The large rewrites seen
  are structural: identity, and/or flattening, de Morgan, and reordering.
  Prove these schemas directly and keep truth tables only for small rewrites.
  Z3 should also stop emitting identity rewrites from the simplify pass.

The z3test corpus has almost no single-query propositional files, so generated
families are the benchmark for this fragment.

## Preprocessing evidence audit

Before expanding the checker further, exercise native simplifiers explicitly.
`examples/python/proof_preprocessing.py` compares the simplifier API
(`solve-eqs` wrapping `SimpleSolver`) with the `solve-eqs`/`smt` tactic chain,
each with proof generation off and on. It records elimination and search
statistics separately from proof validity and checks every available native
refutation against the original input using the existing Lean consumer.

`lean/examples/boolean_solve_eqs.smt2` requires its equality for unsatisfiability:
elimination leaves four clauses and search still makes decisions and conflicts.
Use `--require-search` for this case. The existing unit-resolution example
covers contradictions closed by preprocessing alone; a search step is not
required in that case.

Both examples now run `solve-eqs` and reconstruct their refutations successfully
through both interfaces with proof generation enabled. The native producer
changes were merged upstream in Z3Prover/z3#10915. The native producer
carries equality evidence through extraction and substitution normalization,
composes substitution congruences with subsequent rewrites, and preserves proofs
when flattening conjunctions or replaying eliminated definitions. Tracked
assertions keep their original labels instead of introducing unbound proxy
assumptions in the final proof.

Proof support currently covers direct variable equalities and Boolean units.
Theory-specific isolation, conditional and nested-equation extraction, and
guarded array definitions remain disabled in proof mode until their own
certificates are implemented. The actual goal's proof setting is respected;
proof-disabled goals keep the existing extraction behavior.

Native checks validate proof conclusions, original assertion leaves, and rewrite
side conditions. Lean coverage checks complete Boolean refutations, axiom
dependencies, incremental additions, push/pop, query assumptions, context
translation, and tracked assertions against explicit original-input snapshots.
The exporter retains its single-snapshot input restriction.

Preprocessing-only proofs and preprocessing followed by search must both
preserve the original assertion boundary; checking a SAT proof of an unrelated
or unverified CNF is insufficient. The audit continues to report failure when
required execution evidence or checked proofs are absent.

## Arithmetic proof infrastructure

The arithmetic proof infrastructure is slightly broken and must be repaired
before milestone 3 can claim checked arithmetic. Known defects:

- `theory_lra` attaches Farkas coefficients to `th-lemma arith farkas`, but the
  coefficients can be wrong in two situations: when a lemma is reused for unit
  propagation rather than the conflict it was derived for, and when the LP
  solver derives bounds internally that do not correspond to literals and
  those bounds enter an LP explanation. The `sat.smt=true` arithmetic checker
  already re-derives `farkas` and `bound` justifications, so the first step is
  to run the matrix with that checker and with `smt.arith.validate` on the
  linear logics and measure how often each defect occurs. The fix is to explain
  only in terms of literal bounds, or to emit explicit derived-bound steps
  that the checker can replay, and to regenerate coefficients for the
  propagated orientation.
- `nla` lemmas are built at more than fifty sites across the basics, order,
  monotonicity, tangent, power, and Groebner modules, and the self-checker
  falls back to the SMT solver for them. Proposal: inventory the lemma schemas,
  certify each schema statically at build time as a parameterized theorem,
  name the schema in the `lemma_builder` output, and emit each lemma with a
  hint recording the schema and its instantiation (monomial, factors, sign, and
  bounds). The proof checker then instantiates the certified schema from the
  hint instead of calling a solver. Lemmas without a certified schema stay in
  the `unverified-fallback` class of the matrix until they are covered.

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
