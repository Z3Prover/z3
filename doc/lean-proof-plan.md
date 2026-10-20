# Z3 native certificates and Lean verification

## Goal and boundary

The goal is unsat results from Z3 that an independent Lean checker accepts
without trusting the solver. Z3's proof format is a means to that end, not
something to preserve. The current low-level proof terms and clause logs are
prone to regressions, because every simplifier and solver path has to thread
proof evidence through by hand. The regression matrix below and the Lean checks
exist to expose those regressions, and the format is free to change wherever a
change makes the evidence more complete or easier to check. The exporter is a
thin adapter over whatever evidence Z3 emits, so a format change is a change to
the adapter, not to the Lean rules, which are tied to the meaning of each
inference rather than to its encoding. Missing native proof evidence and
checker correctness are separate obligations. Proof certification is opt-in,
so users who do not request proofs see no change while the integration is
developed.

## Current integration status (2026-10-02)

`examples/python/proof_certificate.py` saves a native Z3 proof as JSON.
`examples/python/proof_to_lean.py` translates that proof into Lean source and
checks it. `examples/python/proof_preprocessing.py` checks that simplification
steps preserve proof evidence connecting the result to the original assertions.
`scripts/check_lean.sh` invokes the Lean version specified in
`lean/lean-toolchain`. These tools currently support selected proofs over
Boolean variables and operators, not arbitrary SMT inputs.

The Python script `scripts/proofs/proof_matrix.py` in
[Z3Prover/z3test](https://github.com/Z3Prover/z3test/tree/master/scripts/proofs)
runs input files through Z3 with different proof-generation and checking
settings, then reports the results. Its automated tests and sample input files
also live in that repository. With `--lean`, the script uses
`examples/python/proof_certificate.py` to save a native Z3 proof and
`examples/python/proof_to_lean.py` to check it with Lean.

The `releaseClang` job in `.github/workflows/ci.yml` requires Lean to accept the
proof for every Boolean example, reported as `lean-verified`. It saves the
native JSON proof certificates and the checked Lean source files.
These Lean checks and the other tests share the `z3test/` checkout from its
default branch.
`proof_certificate.py` and `proof_to_lean.py` can also be used directly,
without `proof_matrix.py`.

### Input files checked now

The automated Lean checks use these six files in `z3test/regressions/proofs/lean/`:

- `unit_resolution.smt2`
- `boolean_branching.smt2`
- `boolean_def_axiom.smt2`
- `boolean_rewrite.smt2`
- `boolean_structural.smt2`
- `boolean_solve_eqs.smt2`

### Additional input files: future plan

**Planned only; these files are not included in the current automated Lean
checks.** Add the seven `.smt2` examples from
[jreeves3/SMT-Skeleton-Check/formulas](https://github.com/jreeves3/SMT-Skeleton-Check/tree/main/formulas):

| Logic | Input file |
| --- | --- |
| QF_UF | `simple-cong.smt2` |
| QF_UF | `QG-classification-qg5-gensys_icl634.smt2` |
| QF_LIA | `cut_lemmas-20-vars-cut_lemma_01_003.smt2` |
| QF_LRA | `LassoRanker-CooperatingT2-efegp.t2.c_Iteration1_Lasso_3-pieceTemplate.smt2` |
| QF_UFLIA | `wisas-xs_10_20.smt2` |
| UF | `20170428-Barrett-cdt-cade2015-nada-afp-abstract_completeness-x2015_09_10_16_59_39_090_1045351.smt_in.smt2` |
| UFLIA | `boogie-AdditiveMethods_AdditiveMethods..ctor.smt2` |

The LassoRanker QF_LRA example is now available as the optional, manual
certification benchmark described below; the other six examples remain
planned extensions. It is not run by PR CI or scheduled/nightly builds.

These examples require support beyond Boolean variables: equality and
uninterpreted functions, linear real or integer arithmetic, and, for UF and
UFLIA, quantifiers. Before enabling each file, check that Z3 can read it,
review cvc5-specific options such as `:simplification` without changing the
assertions, and add the proof translation needed for Lean to check it.
Keep these additional external test inputs in `Z3Prover/z3test`.

### Larger collections of input files: future plan

**Planned only; these collections are not included in the current automated
Lean checks.** Obtain additional `.smt2` inputs using the benchmark names in
the following CSV files in
[jreeves3/SMT-Skeleton-Check/data/ijcar26](https://github.com/jreeves3/SMT-Skeleton-Check/tree/main/data/ijcar26):

| Logic | CSV file containing benchmark names | Distinct names | Recorded as `unsat` |
| --- | --- | ---: | ---: |
| QF_UF | `QF_UF_cvc5-no-proof-rt.csv` | 7,503 | 4,356 |
| QF_LIA | `QF_LIA_cvc5-no-proof-rt.csv` | 13,306 | 3,545 |
| QF_LRA | `QF_LRA_cvc5-no-proof-rt.csv` | 1,753 | 696 |
| QF_UFLIA | `QF_UFLIA_cvc5-no-proof-rt.csv` | 190 | 190 |
| UF | `UF_cvc5-no-proof-rt.csv` | 2,857 | 702 |
| UFLIA | `UFLIA_cvc5-no-proof-rt.csv` | 2,849 | 1,518 |

The counts above describe the published CSV files inspected on 2026-10-02.
Their `Name` columns identify benchmarks, not ready-to-use file paths. The
repository provides only the seven example `.smt2` files listed above, not
the complete collections. Obtain the remaining inputs separately.
The recorded `unsat` results come from cvc5 runs; they are not Lean-checked
results.

Start with the entries recorded as `unsat`. Locate the original inputs,
record their source and expected result, and store the selected test inputs
and file lists in `Z3Prover/z3test`. Add them to automated Lean checking
gradually as `proof_certificate.py` and `proof_to_lean.py` support their
formulas and proof steps. Missing proof support must remain an explicit
failure, not an accepted proof.

The dated findings below describe earlier runs and retain their historical
file paths. The Boolean-negation and arithmetic-coefficient fixes have since
merged as Z3Prover/z3#10952, Z3Prover/z3#10954, and Z3Prover/z3#10955.

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

**Implemented infrastructure.** The runner is now
`Z3Prover/z3test/scripts/proofs/proof_matrix.py`. It takes a benchmark
list and emits one JSON record per cell, together with a summary table;
canary lists live in `Z3Prover/z3test/regressions/proofs/canaries/`. The runner must
exit nonzero on `checker-rejected` and `crash`, and must report fallbacks
separately from verified results.

### First matrix run (2026-09-25)

`examples/python/proof_matrix.py` implements the runner. A canary of 86
single-query benchmarks (z3test regressions plus small local SMT-LIB samples in
QF_UF, QF_LIA, QF_LRA/QF_RDL, QF_NIA, QF_AUFLIA/QF_ALIA) produced these
findings:

- **Crash (fixed in PR).** `sat.smt=true` with `solver.proof.log` segfaulted on
  13 array-logic instances that solve fine without logging (for example z3test
  `t168.smt2`). The array solver justified its unconditional axiom merges with
  a bare `sat::constraint_base` index, which `log_justifications` reinterpreted
  as a `th_explain`. The fix (branch `array-proof-log`) uses a `th_explain`
  with an `array` hint carrying the derived equality. A four-line reproducer
  is in the PR description and should become the first canary regression.
- **Checker rejection exposed by the fix.** With logging working on arrays,
  z3test `t8.smt2` (array `default`, `map`, and `array-ext`) replays with
  `tseitin` and `euf` steps whose derived units are not RUP-derivable
  (`unit (not (default s1)) is not rup`). This is a logging or checker defect
  in the array/euf interplay, not a solver result error.
- **Preprocessing is outside the clause log.** Every QF_UF unsat instance and
  some QF_LIA ones are closed by `solve-eqs` or value propagation before the
  core runs, so the clause log is empty and the run is classed `no-proof`. The
  `smt-clause-log-nopp` cell disables those simplifiers to measure the core
  alone. Preprocessing proofs exist only in the legacy proof objects.
- **Self-checker fallbacks in linear arithmetic.** On the QF_LIA canary the
  checker fell back to the SMT solver for 262 `smt` hints, 41 failed `rup`
  checks, and all 16 `bound` hints in one bignum instance; one `farkas` hint in
  QF_RDL was also rejected and recovered by fallback. `bound` and `farkas`
  misses are the coefficient defects described below; `smt` hints carry no
  checkable justification at all; `rup` misses mean the logged clause is not
  reverse-unit-propagation derivable from the logged state.
- **Nonlinear lemmas always fall back.** `nla` and `cut` hints were never
  accepted by the checker.
- **Legacy proof objects have no external checker.** Every unsat legacy proof
  is classed `no-checker` outside the propositional fragment. Their theory
  lemma kinds on this canary are `arith`, `arith farkas`,
  `arith assign-bounds`, and `arith triangle-eq`, which is the inventory for
  milestone 3. The built-in `context::check_proof` runs `proof_checker` but
  discards the verdict and is not exposed as an option.
- **Legacy clause proofs** (`smt.clause_proof`) record only assumptions and the
  final `proof-trail`, so there is nothing to check.

### Canary lists and known failures (2026-09-25)

The array proof-logging fix merged as Z3Prover/z3#10922 without a test, and the
canary set of the first run existed only as session files. Both are now in the
repository under `examples/python/proof_canaries/`:

- `array_axiom_log.smt2` is the four-line reproducer from the PR. The
  end-to-end test in `test_proof_matrix.py` asserts that both clause-log cells
  classify it as `unverified-fallback` with `array` hints, so a return of the
  crash fails the test, and so does a silent change to `verified` once an array
  checker plugin exists. CI runs the matrix tests against the built binary in
  the Lean-enabled job.
- One list per logic (`QF_UF`, `QF_LIA`, `QF_LRA` with `QF_RDL`, `QF_NIA`,
  `QF_AUFLIA` with `QF_ALIA` and the z3test array regressions, plus the
  propositional Lean examples). Entries resolve next to the list first and then
  against `--benchmark-root`, so the z3test checkout and the SMT-LIB samples
  are expected under one root outside the repository. The two z3test array
  files whose proof-free run itself reports an error are excluded.
- List entries may carry `cell=status` annotations for known failures in the
  `checker-rejected`, `disagree`, and `crash` classes. A known failure that
  reproduces is reported but does not fail the run; one that stops reproducing
  is reported as stale so the annotation is removed deliberately. `t8.smt2`
  carries the first annotation, for both clause-log cells, until the
  array/euf replay defect is fixed. This is how every future minimized
  `checker-rejected` or `crash` instance is recorded: the instance goes into
  the canary directory or its list, its expected class is annotated, and the
  fix removes the annotation.

**t8 diagnosed (2026-09-28).** The rejection is two checker defects, not a
logging gap. The array `default` axiom for `(_ map not)` over a Bool array
introduces the term `(not (default s))` as its own literal. The clause log
prints the negation of that literal as `(not (not x))`, while the `tseitin`
and `euf` hints, built through `literal2expr`, collapse it to `x`;
`theory_checker::check` compared the two syntactically, saw a spurious extra
hint literal, and demanded a unit that is not RUP-derivable. Separately, the
`euf` plugin treated `(not x)` inside an equality as uninterpreted and found no
conflict in `x = true, (not x) = y, y = true`. The fix (branch
`proof-log-double-negation`) compares literals modulo double negation and makes
the `euf` plugin reject a class where `x` and `(not x)` coincide or share a
truth value. On t8 the replay goes from four rejected `tseitin` and two
rejected `euf` steps to all accepted, leaving only the `array` fallbacks. The
one-assertion reproducer `array_default_not.smt2` is in the canary directory
with a known-failure annotation; the annotations for it and t8 go stale, and
are removed, when the fix merges.

Rerunning the 115-entry canary set on the merged fix exits zero: the 13 former
crash cells now log and replay (`unverified-fallback` or `not-applicable`), the
`t8.smt2` annotation reproduces, and the six propositional examples are
Lean-verified through `legacy-proof-object`. New observation: proof logging
slows the larger `QF_ALIA_SAT` instances (`qlock-bug-10`, `qlock-bug2-10`,
`qlock.induction.10`) past the 30-second budget although they solve within it
without logging, so the array log volume on sat instances is itself a cost to
measure.

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
- Exercise complete examples using `z3test/regressions/proofs/lean/unit_resolution.smt2`,
  `z3test/regressions/proofs/lean/boolean_rewrite.smt2`, and
  `z3test/regressions/proofs/lean/boolean_structural.smt2`, plus scoped learning in
  `z3test/regressions/proofs/lean/boolean_branching.smt2` and gate clauses in
  `z3test/regressions/proofs/lean/boolean_def_axiom.smt2`. Cover Boolean truth tables, chained
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
  (Done 2026-10-16: see "Propositional rewrites as direct proof terms" below.)

The z3test corpus has almost no single-query propositional files, so generated
families are the benchmark for this fragment.

## Preprocessing evidence audit

Before expanding the checker further, exercise native simplifiers explicitly.
`examples/python/proof_preprocessing.py` compares the simplifier API
(`solve-eqs` wrapping `SimpleSolver`) with the `solve-eqs`/`smt` tactic chain,
each with proof generation off and on. It records elimination and search
statistics separately from proof validity and checks every available native
refutation against the original input using the existing Lean consumer.

`z3test/regressions/proofs/lean/boolean_solve_eqs.smt2` requires its equality for unsatisfiability:
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
The exporter certifies one query of a script at a time: the certificate names
the query and the reconstructor rebuilds that query's snapshot (scoped
declarations and assertions plus the query's assumptions) from the original
script (see the 2026-10-16 note on incremental scripts below).

Preprocessing-only proofs and preprocessing followed by search must both
preserve the original assertion boundary; checking a SAT proof of an unrelated
or unverified CNF is insufficient. The audit continues to report failure when
required execution evidence or checked proofs are absent.

## QF_LRA slice through the clause log (2026-10-06)

Milestone 3 now has a working linear real arithmetic slice. It deliberately
uses the `sat.smt` clause log rather than the smt core's proof objects, because
`theory_lra` records its arithmetic conflicts there as `(_ th-lemma arith)`
with no Farkas coefficients: `set_conflict_or_lemma` passes a parameter vector
that is only ever reset. The clause log carries them, for example
`(farkas 1 $11 2 $17 1 $21)`, and its hints are already validated by the C++
checker in the matrix. `proof_clause_log.py` rebuilds the log into the
existing certificate format, so the Boolean reconstruction is reused
unchanged: theory hints become `th-lemma` nodes, Tseitin hints become
`def-axiom` nodes, and reverse-unit-propagation steps become explicit
hypothesis/unit-resolution/lemma chains. Lean proves each theory lemma and each
arithmetic rewrite with `grind` over a `Rat` encoding of the Real variables,
after the reconstructor has re-derived the recorded Farkas combination with
exact rationals.

Findings from building and running it:

- **`bound_simplifier` defeats the no-preprocessing cell.** With `solve_eqs`,
  `propagate_values`, and `elim_unconstrained` disabled, `bound_simplifier`
  (on by default) still runs `solve_eqs` and `propagate_values` internally,
  so assumed clauses can combine several assertions. The exporter disables it
  too; the companion matrix update disables it in `smt-clause-log-nopp` as well.
- **Equality coefficients in `farkas` hints are placeholders.** A hint
  listing an equality with coefficient 1 may need multiplier 15 to cancel;
  Z3's checker solves for equality multipliers rather than reading them, and
  the exporter and reconstructor now do the same by Gaussian elimination.
- **Hint conventions differ.** `farkas`, `bound`, `implied-eq`, and `euf` list
  jointly contradictory literals; `tseitin` lists the gate clause itself;
  `smt` carries no literals. A clause-log consumer must know which is which.
  An `implied-eq` ends in a disequality: Python checks the shape and Lean
  proves the implied equality, rather than summing the disequality as a
  Farkas constraint. `alldiff` clauses must be tied to the original `distinct`
  assertion, never trusted as unconditional theory lemmas.
- **Z3's RUP check is Tseitin-aware.** `rup` steps may rely on the definitions
  of compound Boolean atoms that are never logged as clauses; the replayer
  adds those gate clauses as `def-axiom` nodes.
- **Preprocessing splits assertions.** An `xor` or Boolean equality becomes
  several clauses, and a contradiction found while asserting produces an
  empty or truncated log. Such clauses are tied to the assertions by a `cnf`
  theory lemma that Lean proves, which keeps the theorem's hypotheses equal to
  the original assertions.
- **`grind` and fractional equalities.** Lean 4.34's `grind` proves the lemmas
  once denominators are cleared but not always with fractional constants in
  equalities; stating each fractional atom's scaled form as a helper
  implication restores completeness on every instance tried.
- **Real as Rat.** Lean core has no `Real`; the encoding is sound for linear
  constraints with rational coefficients and is stated at the trust boundary.
  Lean core's own `Rat` lemmas depend on the three standard axioms, so the
  arithmetic slice cannot be axiom-free regardless of the tactic used.
- **Scaling.** Random QF_LRA instances up to 24 variables and 140 constraints
  (about 2,400 DAG nodes, 525 proof steps) export in under a second and check
  in about three seconds once `maxRecDepth` is raised; the earlier ~500-step
  elaboration cliff was the default recursion limit, not the kernel.

The companion matrix update is
[Z3Prover/z3test#77](https://github.com/Z3Prover/z3test/pull/77): it adds the
clause-log `--lean` cell and eight QF_LRA inputs, including implied equality,
n-ary `distinct`, and fractional unary-negation regressions.

Still open for this slice: real SMT-LIB QF_LRA benchmarks (the canary list has
two unsat instances, both trivial), `smt` hints have not been observed on the
inputs tried, and QF_LIA needs `cut` hints that the C++ checker never accepts
(QF_LIA certified since 2026-10-15 with Lean proving the cuts; see below).

**Real `ite` terms and congruence claims (2026-10-11).** The exporter rejected
every QF_LRA input with a Real-valued `ite`, although the clause log handles
them cleanly: `theory_lra` treats the `ite` as an opaque variable and the
`euf` core records `(not c) ∨ (ite c a b) = a` and `c ∨ (ite c a b) = b` as
`tseitin` inferences. The replay now does the same, adds those gate clauses
as `def-axiom` nodes, and Lean proves them from a decidability witness for
`c` with `ite_eq_left`/`ite_eq_right`; the term is Lean's `ite` over `Rat`
with the classical instance, so the term definitions containing one are
`noncomputable`. Z3 normalizes `abs`/`max`-shaped `ite` terms by swapping
branches, so the assumption is bridged by a `rewrite` that `grind` proves by
splitting on the condition. The same inputs exposed `euf` hints that carry
congruence claims `(cc (= a b))` and `(comm (= a b))` as `Proof`-sorted
arguments; Z3's checker uses them as guidance and builds the clause from the
Boolean arguments only, and the replay now drops them after a shape check.
Review of this slice found that a comparison applied directly to an `ite`
with a fractional branch, such as `(>= (ite p x (/ 1.0 2.0)) 1.0)`, exported
a certificate that `grind` could not close: Z3's rewriter pushes the
comparison through the `ite`, so no gate clause is recorded, and `grind`
splits on the `ite` but, as with fractional atoms, does not combine the
resulting equality `ite = 1/2` with its linear facts. Each `grind` lemma now
states the two branch equalities of every reachable `ite` first, scaled to
integer coefficients when a branch has fractions, proved by `ite_eq_left` and
`ite_eq_right`. Random instances with `ite` terms verify end to end; integer
`ite` and `ite` with nonlinear branches stay rejected.

**QF_UF through the clause log (2026-10-11).** Inputs over one uninterpreted
sort with constants, functions, and predicates are now certified end to end.
The clause log needs nothing new: the sort and the functions it uses are
declared in the log (and must be the input's own, with the input's arities),
equality conflicts arrive as `euf` hints with `cc` claims, `distinct` as
`alldiff` clauses, and the Boolean structure as `tseitin` and `rup` steps.
In Lean the sort is a type variable `_U` and the symbols are indexed families
`_elems : Nat -> _U`, `_funs : Nat -> List _U -> _U`, and
`_preds : Nat -> List _U -> Prop`, so one theorem signature serves every
arity; the theorem quantifies over all such interpretations, which include
every model of the input, so it is sound for unsatisfiability. `grind`'s
congruence closure proves every `euf` lemma and every rewrite over the sort
tried, including through `List.cons` applications, in well under a second
each, and reports the three standard axioms. Python checks only shapes for
`euf` hints, so a false `euf` lemma is rejected by Lean alone (covered by a
tampering test). Still rejected: a second uninterpreted sort, mixing the sort
with arithmetic (QF_UFLRA), functions with Bool or Real arguments or results,
and `ite` over the sort (a second sort, `ite`, and Bool accepted since
2026-10-12, QF_UFLRA and Real since 2026-10-15, see below).

**Long refutations in every fragment (2026-10-12).** The lemma outlining
added for LassoRanker applied only to arithmetic certificates with more than
2,000 steps, and only at shared subproofs. A 7-level QF_UF equality diamond
(1,606 steps) and the propositional pigeonhole principle for five holes
(1,644 steps) both failed in `theorem unsat` with `maximum number of
heartbeats (200000)`: one nested term of `let`-bound steps elaborates
superlinearly, and the `maxHeartbeats` raise covers only the `grind` lemmas.
Outlining now applies to every fragment above 500 steps, cuts a chain at
every 500 nested steps even without sharing, and ignores steps the root never
uses. The arithmetic and uninterpreted slices keep their classical witnesses
inside the lemmas; propositional lemmas take their decidability witnesses as
parameters, introduced constructively by the main theorem, so the
propositional slice reports no axioms at any size. The 7-level diamond now
checks in 3 s (the 8-level one, 3,827 nodes, in 5 s; previously a failure),
the 6-level one drops from 15 s to 2 s, and pigeonhole-5 checks in 3 s;
pigeonhole-6 (8,693 steps, 3,071 lemmas) checks in about 90 s. Covered by
`test_proof_to_lean_uf.py` and `test_proof_to_lean_integration.py`.

**`ite` over the uninterpreted sort (2026-10-12).** The QF_UF slice rejected
every input with an `ite` whose branches have the uninterpreted sort, although
the clause log treats it exactly like a Real `ite`: the `euf` core keeps the
term opaque and records `(not c) ∨ (ite c a b) = a` and `c ∨ (ite c a b) = b`
as `tseitin` inferences. The exporter now classifies such inputs as `qf_uf`,
the replay adds the gate clauses as `def-axiom` nodes for `ite` terms found
inside equalities, `distinct`, and predicate applications, and the
reconstructor renders the term as Lean's `ite` over `_U` with the classical
instance and proves the gates with `ite_eq_left`/`ite_eq_right` as before.
`grind` splits on the `ite` inside `euf` lemmas and rewrites without help.
Random instances with nested `ite` terms exposed two older gaps that the new
inputs hit often: Z3 also records the two condition-free Boolean `ite` gate
clauses (`(or (not (ite p q r)) q r)` and `(or (ite p q r) (not q) (not r))`),
which the def-axiom checker rejected; and when `q` is asserted, Z3
internalizes a later `distinct` with `(ite (not q) b a)` already replaced by
`a`, so its `alldiff` clauses follow only from the `distinct` together with
`q`. The replay's last-resort `cnf` lemma now negates an unsat core of the
assertions instead of all of them, and keeps a clause literal that is already
the negation of a source as a literal (resolving it away produced a
unit-resolution the reconstructor rejected). 20 of 400 random stress
instances failed before these fixes, none after. Still rejected: a second
sort (accepted since 2026-10-12, see below), QF_UFLRA, and Bool or Real
arguments or results of uninterpreted functions (Bool accepted since
2026-10-12, QF_UFLRA and Real since 2026-10-15, see below).

**Several uninterpreted sorts (2026-10-12).** Inputs over more than one
uninterpreted sort were rejected at the exporter, although Z3's clause log
declares every sort and treats functions between sorts like any other. The
exporter now classifies any number of sorts as `qf_uf` and the certificate
keeps every sort name, so the reconstructor checks the proof graph is
well-sorted (functions and predicates take uninterpreted-sort arguments
only, equality and `distinct` compare one sort, every application matches
its declaration) and `_bind_input` checks the sort set against the input.
Lean renders all sorts as the one type `_U`: a many-sorted model is an
instance of the theorem over the disjoint union of its carriers, every
ground term keeps its value, and well-sorted inputs only compare terms of
one sort, so the collapsed theorem implies unsatisfiability of the
many-sorted input. The two documented two-sort inputs and 19 random
three-sort instances with `ite` terms (unsat cores of 3 to 5 assertions)
verify end to end under the standard axioms; three are pinned in
`test_proof_to_lean_uf.py`. Review of this change found that the binder
matched symbols by name alone while Z3 accepts one name declared with several
signatures (`(declare-fun c () A) (declare-fun c () B)`, applied as
`(as c A)`): the honest refutation of a one-sort input could be rebound to a
satisfiable two-sort input whose assertions print identically, once an
unused declaration padded the certificate's sort set. Overloaded names are
now rejected by `classify_fragment` (so by the exporter and, since the
reconstructor parses the input itself, by the binder), the binder requires
every bound declaration to carry the input's full signature and interns
terms with their sort, and a declaration over an uninterpreted sort that no
node uses is rejected. Still rejected: QF_UFLRA and Bool or Real arguments
or results of uninterpreted functions (Bool accepted since 2026-10-12,
QF_UFLRA and Real since 2026-10-15, see below).

**Bool arguments of uninterpreted functions (2026-10-12).** Functions and
predicates with Bool arguments (`(declare-fun f (Bool) U)`, `(declare-fun r
(Bool U) Bool)`, `(declare-fun p (Bool) Bool)`) were rejected at the
exporter; they are common in hardware-derived QF_UF benchmarks. The clause
log treats a Boolean argument like any other enode: once the SAT solver
assigns it, the egraph merges it with `true` or `false`, and the `euf` hint
lists the Boolean literal among its premises, so `(f q) = (f r)` follows from
`q`, `r`, and congruence. Lean renders a Boolean argument `p` as `_bool p`
for one more quantified map `_bool : Prop -> _U`: Bool is one more sort in
the disjoint-union instance, and `grind` proves the lemmas through the
congruence `p <-> q -> _bool p = _bool q` (via `propext`); nothing states
that `_bool True` and `_bool False` differ, and no inference needs it. The
egraph does know that every Boolean argument is `true` or `false` once the
SAT solver assigns it, and `cnf` lemmas combining preprocessed assertions
rest on that without naming the literal, so each `grind` lemma first states
excluded middle for every Boolean argument it reaches (5 of 40 random
instances failed in `grind` before this, none after). Two
findings about Z3's sat.smt core shaped the slice: (1) a unit asserted at
level 0 is substituted into the arguments before internalization (`(f q)`
is logged as `(f true)`), which the replay's existing `cnf` fallback ties to
the unit and the assertion; and (2) a Boolean unit makes goal2sat log its
internal `true` variable, which has no expression, as a fresh constant
`k!0` assumed as a unit clause. The second affected plain QF_UF inputs with
a negated unit assertion as well (`(assert (not s))` with `s` elsewhere),
which the exporter rejected as a fresh symbol; empirically the phantom
appears for inputs without a `set-logic` line and not for the same
assertions under `(set-logic QF_UF)`, so the inputs that test it carry no
`set-logic` line and the live tests check the raw log for `k!0` before
checking that the certificate has none. The replay now drops assumed
or deleted clauses over such phantom constants (sound: dropping a clause
only removes support for later propagation) and still rejects any inference
or definition mentioning one. Functions whose arguments are all Bool are
accepted only together with an uninterpreted sort: without one the sat.smt
core Ackermannizes them with fresh symbols the log cannot be tied to the
input, so the exporter rejects that case explicitly. Two documented inputs
and five pinned random instances verify end to end under the standard
axioms. Still rejected: QF_UFLRA and Real arguments or results (accepted
since 2026-10-15, see below).

**Legacy core proof objects (2026-10-13).** The theory slices above all read
the `sat.smt=true` clause log. The legacy smt core (`sat.smt=false`) is the
default and the one most users run, and with `produce-proofs` it emits a
complete proof object for every logic, so it has to be a supported proof
producer for theories too, not only for propositional input as today
(`--core legacy` rejects anything else). What the legacy proof object has
that the log does not: complete equality proofs (`congruence`,
`transitivity`, `symmetry`, `monotonicity` built by conflict resolution) and
the preprocessing steps (`rewrite`, `solve-eqs`), which the log starts
after. What it lacks: `theory_lra` reports an arithmetic conflict as a bare
`th-lemma arith` because `set_conflict_or_lemma` resets its parameter vector
and never fills it, so there are no Farkas coefficients to check; the older
`theory_arith` (`smt.arith.solver=2`) does record them. Decision: both cores
are in scope, and the regression matrix keeps a `legacy-proof-object` cell
per fragment next to the clause-log cell. Two backlog items follow: a QF_UF
slice over legacy proof objects (Python and Lean only: lift the
propositional restriction, extend `trans`/`symm`/`monotonicity` from Boolean
equivalences to sort-valued equalities), and a C++ change so `theory_lra`
fills the `th-lemma` parameters with Farkas coefficients from the LP
explanation, after which the exporter's existing `th-lemma` node and
`_check_th_lemma` verify them unchanged. The "inventory for milestone 3"
noted in the first matrix run (`arith`, `arith farkas`, `arith
assign-bounds`, `arith triangle-eq`) is the list of legacy lemma kinds that
second item must map or reject explicitly.

**QF_UF over legacy proof objects (2026-10-14).** The first of the two items
is done, in Python and Lean only. `export_certificate` (`--core legacy`)
accepts QF_UF input and keeps the input's sort names in the certificate;
`--core auto` still picks the clause log for anything but propositional
input, so the matrix compares both cores on the same inputs. Scanning the
legacy proofs of 348 unsat QF_UF instances (the documented inputs, equality
diamonds, and the four random generators) gave the rule inventory the
reconstructor had to learn: `trans`, `symm`, `trans*`, and `monotonicity`
over sort-valued equalities (860 monotonicity steps, with heads `not`, `=`,
`ite` over a sort, `distinct`, `or`, `and`, `=>`, functions, and predicates),
`commutativity` (new rule), rewrites between terms (`(ite true a b)` to `a`,
branch swaps under a negated condition), 234 identity rewrites, and
`def-axiom` clauses pairing `distinct` with its conjunction of disequalities.
Every premise of every monotonicity step was forward-oriented, so the
Boolean rule's orientation requirement is kept. The equality rules are
explicit Lean terms (`Eq.trans`, `Eq.symm`, `congrArg` over argument lists,
`propext` for `_bool` arguments, a per-file `ite_congr_classical` lemma for
`ite` terms); only the non-identity rewrites go to `grind`, and refutations
without one depend on `propext` alone. One elaboration pitfall: `congr`
against a `formula_N` application unifies its metavariable head with the
definition's last argument instead of unfolding, so equality congruence is
composed from `Eq.trans` like the Boolean `Iff` congruence. All ten
documented QF_UF inputs, 109 random instances with unsat cores of at least
three assertions, and the 5- and 7-level diamonds (the latter outlined,
1,230 steps) verify under the standard axioms. Not done: the C++ Farkas item
for `theory_lra`, and a `uf_*.smt2` set in z3test for a legacy QF_UF matrix
cell.

**QF_LRA over legacy proof objects (2026-10-14).** The second item is done.
`theory_lra` now fills the `th-lemma` parameters it used to reset: an LP
conflict carries `farkas` with the explanation's multipliers, one per
premise in the order the justification lists them (literals, then
equalities); a bound propagation from the LP carries `bound` with the same
multipliers and 1 for the consequent, mirroring the sat.smt `bound` hint
(the fresh bound literals of `smt.arith.propagation_mode=2` included); an
equality propagation is labelled `implied-eq`. Scanning the proofs showed
two more producers on the same inputs: `arith_eq_adapter`'s `triangle-eq`
axioms, and the older `theory_arith`, which the smt core still selects for
difference-logic-shaped input and whose `assign-bounds` steps weight the
antecedents only with signed coefficients. The exporter accepts `qf_lra` on
the legacy path, maps these conventions to the certificate's `farkas`,
`bound`, `implied-eq`, and `triangle-eq` hints (premises first, then clause
literals, magnitudes only), and rejects a bare `(_ th-lemma arith)` or an
integer rule. The reconstructor re-derives each combination with the
premises as held constraints, states a `th-lemma` with premises as the
implication from them, proved by `grind`, and proves congruence through
arithmetic operators and comparisons (new in legacy proofs, since the smt
core rewrites atoms inside assertions) by `grind` over the argument
equalities. All eight documented QF_LRA inputs, 188 random instances (up to
571 steps, 4.4 s), ten difference-logic inputs, and the three rewritten-ite
inputs verify under the standard axioms from the legacy proof object. Still
rejected on this path: Real `ite` terms, which the smt core names by
`intro-def` (a fresh definition; the first candidate for the next legacy
item), so `--core auto` keeps the clause log for arithmetic and the matrix
compares both cores. No input tried produced a legacy `implied-eq` step, so
that shape is covered by the exporter's mapping and the reconstructor's
shape check only.

**Uninterpreted predicates over Bool without a sort (2026-10-14).** The
Bool-argument note of 2026-10-12 left `(declare-fun r (Bool) Bool)` with no
uninterpreted sort in the assertions rejected on every path, because the
sat.smt core Ackermannizes such predicates: its log declares fresh symbols
(`r!1`, `k!2`) for the applications, or is empty when the input is decided
before search. The legacy proof object has no such gap: `(= (r p) (r q))`
is a `monotonicity` step from `(= p q)`, with `iff-true`/`iff-false` under a
`hypothesis` when it splits on an argument, all rules the reconstructor
already checks. The exporter now classifies these inputs as `qf_uf` (an
input mixing them with arithmetic stays rejected), `--core auto` selects the
legacy proof object for them (`requires_legacy_core`), and `--core
clause-log` rejects them explicitly instead of failing on the fresh symbols.
The reconstructor keys the qf_uf encoding on "uses a sort or an
uninterpreted predicate" rather than on the sort set: the theorem takes the
same `_U`, `_elems`, `_funs`, `_preds`, `_bool` binders with no sort name in
the certificate, `_U` carries nothing but the injected Boolean arguments,
and the header says so. Five documented inputs (congruence, a binary
predicate, a split on `true`/`false`, nested applications with `xor`, a
Boolean `ite` argument) and 247 random instances of a new generator (129
small, 118 with five variables, twenty constraints, and depth-3 arguments)
verify under `propext` alone with no failure; three seeds with 33
to 41 monotonicity steps are pinned in `test_proof_to_lean_uf.py`, and
`test_proof_certificate.py` checks the classification, the routing, and the
clause-log rejection. Still rejected: Bool-only predicates together with
arithmetic (the qf_lra encoding has no predicate family; accepted since
2026-10-15, see below).

**QF_UFLRA: uninterpreted functions mixed with arithmetic (2026-10-15).**
Every slice so far rejected an input combining an uninterpreted sort or
function with linear real arithmetic, although the clause log treats the
combination like its parts: an application with a Real result is an opaque
variable of the `farkas`, `bound`, and `implied-eq` hints (as a Real `ite`
already was), `euf` hints carry the congruences between applications, and
`implied-eq` hints supply the equalities between Real terms they rest on;
the legacy proof object proves the same congruences by `monotonicity`
through Real arguments. The exporter now classifies such inputs as a fourth
fragment `qf_uflra` (functions and predicates may take and return Real), both
cores export it, and the reconstructor's Lean theorem takes the Rat
valuation and the carrier binders together plus `_real : Rat -> _U`, which
injects Real arguments into the disjoint-union carrier as `_bool` injects
Boolean ones, and `_rfuns : Nat -> List _U -> Rat` for functions with a Real
result. One `grind` gap appeared on random instances: congruence closure
compares function arguments as terms, so `(f (- x y))` and `(f (+ x (* -1
y)))`, one term to Z3's rewriter, stayed apart (3 of 130 random instances
failed); each `grind` lemma now states the equality of every pair of
reachable Real arguments with the same linear form, proved by `grind` as an
atom first, and none fails. Also fixed on the way: the replay's canonical
formula keys identified all numerals in function arguments, and the
atom-normalizing rewrite shape indexed linear forms by variable, which an
`ite` or application atom does not have (it now falls back to the plain
`grind` lemma). Nine documented inputs and 131 random instances (65 with an
uninterpreted sort next to the Real functions) verify through both cores
under the standard axioms; `test_proof_to_lean_uflra.py` pins seven seeds.
The mixed inputs also produced the legacy `implied-eq` step that the
2026-10-14 note had mapped without observing it: `theory_lra` propagates
`x = y` from `x <= y` and `x >= y` when the egraph needs the equality for a
congruence `(h x) = (h y)`, as a `th-lemma` with the two bound premises, no
coefficients, and the equality as conclusion; the reconstructor's existing
shape check and `grind` lemma accept it, and `test_proof_certificate.py`
pins the shape. Two limits, both rejected explicitly: predicates over Bool alone applied to
Real atoms are Ackermannized by the sat.smt core like in QF_UF (`--core
auto` routes them to the legacy proof object, which certifies them), and a
Real variable occurring in a single function argument is eliminated by the
sat.smt path's unconstrained-variable simplifier regardless of
`smt.elim_unconstrained=false`, so the log declares a fresh `k!N` constant
(the legacy core names the term by `intro-def`); plumbing that option
through `simplifier_solver` is a C++ follow-up.

**The frontend's tactic preamble is bypassed (2026-10-15).** Both limits of
the previous note had the same cause, and it was not `smt.elim_unconstrained`:
for a non-incremental `check-sat` Z3's combined solver first runs the tactic
of the input's logic (`mk_tactic_for_logic`; for QF_UFLRA and for input
without `set-logic` that is `mk_default_tactic`, whose `mk_preamble_tactic`
chains `simplify`, `propagate-values`, `ctx-simplify`, `solve-eqs`,
`lia2card`, and `elim-uncnstr`) and only then the sat.smt core wrapped in
`simplifier_solver`, which is where the `smt.*` options are read. The
tactic's `elim-uncnstr` is what replaced `(- x y)` by `k!0` (and, with
proofs, named it by `intro-def` in the legacy proof object), and the same
preamble Ackermannized predicates over Bool alone (`r!1`, `k!2`) or decided
the input before the core logged a clause. Both exporters now set
`combined_solver.ignore_solver1=true` (the clause-log run through
`_NO_PREPROCESSING`, the legacy run on its `z3.Solver`), so the assertions
reach the core directly. Consequences: inputs with a variable in a single
function argument certify through both cores (`uflra_single_occurrence`),
predicates over Bool alone certify through the clause log as well as the
legacy proof object (the `requires_legacy_core` routing and the explicit
`--core clause-log` rejection of 2026-10-14 are gone; `--core auto` is now
"legacy for propositional, clause log otherwise"), and inputs the preamble
used to decide outright have a proof. Every existing documented input, the
pinned seeds, both matrix cells, 24 random Bool-only predicate instances,
and random QF_UF and QF_UFLRA instances verify unchanged or newly through
both cores; `test_proof_certificate.py` pins the mechanism by running the
log once without the option (fresh symbol or no inference) and once with
it. The clause log's assumptions now stay closer to the input: the core's
own `rewriter_simplifier` and `flatten_clauses` still run, but the level-0
substitution into Boolean arguments and the phantom `k!0` of the 2026-10-12
note were the preamble's doing and are gone (the replay keeps its phantom
handling). One new bridge appeared: the core logs a Real `ite` argument in
the rewriter's normal form (`(ite (<= x 0) (* -1 x) x)` for `(ite (> x 0) x
(- x))`), which `grind` cannot identify under a function application, so the
Real-argument helpers of each `grind` lemma key `ite` atoms up to that
normalization (`_real_argument_key`) and state the equality, which `grind`
proves on its own (an `ite` whose condition is no linear atom stays an
opaque atom, `uflra_opaque_ite_conditions`). On the legacy side the proofs changed more: the smt core
reached directly keeps Real `ite` terms (no `intro-def`), so all seven
`ite` inputs of `test_proof_to_lean_arith.py` now verify through the legacy
core too; difference-logic inputs are proved by `theory_lra`'s bound
propagations rather than `theory_arith`'s `assign-bounds` (the mapping stays,
exercised on constructed declarations only); and the documented QF_UF
proofs lost the `trans` and `ite`-congruence steps the preamble's
simplifier used to cause, so a legacy-only input (`uf_rewritten_ite`) keeps
those shapes covered.

**QF_LIA through the clause log (2026-10-15).** Linear integer arithmetic
was rejected at the exporter ("unsupported sort: Int") although Z3's
clause log for it differs from the Real case in three conventions only,
all taken from Z3's own clause-log checker (`arith_theory_checker.h`): the
numerals are printed without a sort, a strict bound over Int is tightened to
its non-strict form (`(< t 5)` and `(not (<= 5 t))` both mean `(<= t 4)`),
and a `bound` combination may be rounded to the integer lattice before the
propagated literal cancels it. What the C++ checker never accepts, the
`cut` hints of Gomory cuts and gcd conflicts, needs no certificate in Lean:
`omega` decides linear integer arithmetic. The exporter now classifies
Int-only input as a fifth fragment `qf_lia` (Int mixed with Real, with
uninterpreted sorts or functions, and `div`/`mod`/`abs`/`to_real` stay
rejected explicitly; the legacy proof object rejects integer input before
producing a proof, and `parse_assertions` accepts the fragment only when
the consumer opts in, since z3test's harness expects integer input to stay
"unsupported" until it adds `lia_*.smt2` inputs), the replay values
numerals in Int, tightens integer
constraints in the Farkas checks and in the canonical assumption keys, and
re-derives `bound` hints with the rounding; the reconstructor values
`_vars` in `Int`, renders Int numerals and `ite`, and proves every integer
lemma and rewrite by `first | omega | grind`: grind's `lia` module ran out
of steps (`liaSteps := 10000`) on Farkas lemmas with several equalities and
on `ite` splits that `omega` closes in under a second. One policy decision:
Z3's LP explanations over Int can rest on cuts it made along the way, so a
`farkas` or `bound` whose coefficients do not refute the tightened literals
(2 of 1,382 lemmas in a 400-seed sample; Z3's checker fails on them too,
"maybe follows from a cut") is kept without coefficients, which marks it in
the certificate as proved by Lean alone like a `cut`; over Real such a hint
is still rejected, and coefficients that are present must re-derive the
lemma on both paths. Nine documented inputs (gcd conflict, rounded bounds,
tightened strict bounds, branch-and-bound shape, a four-literal Gomory cut,
Boolean structure, Int `ite`, `distinct`, equality elimination), three
pinned seeds, and 520 random instances (4 to 6 variables, 10 to 16
constraints, with and without `ite`) verify under the standard axioms; the
first pass had 2 export rejections and 5 Lean failures, all of the two
kinds above and none after. Review of the iteration found the
normalized-rewrite path (more than 16 linear atoms in one rewrite) broken
over Int, because a tightened strict atom and the bound it contradicts got
two unrelated names; the atoms are now keyed up to complement as in the
replay's `_Normalizer`, with a nine-variable, 18-literal input in the test
module. Not done: QF_LIRA and QF_UFLIA (no mixed encoding), the legacy
core's integer steps, the `bound` rounding path is exercised by unit tests
and a pinned log only (no random instance needed it), and an Int `ite`
nested inside another `ite`'s condition can push `omega` and `grind` past
the heartbeat budget (one such instance in the reviewer's stress run; the
certificate is rejected, not misproved).

**QF_UFLIA through the clause log (2026-10-15).** Int next to uninterpreted
sorts or functions was the one combination of certified fragments still
rejected at the exporter ("integer arithmetic with uninterpreted sorts or
functions is not supported"; z3test's `regressions/smt2` has Int-only files
that fail for exactly this reason). The clause log needs nothing new: an
application with an Int result is an opaque integer atom of the `farkas`,
`bound`, `implied-eq`, and `cut` hints (a strict bound on it is tightened, a
gcd conflict runs through it), `euf` carries the congruences, and a 150-seed
probe in three shapes showed no other hint kind. The exporter classifies
the input as a sixth fragment `qf_uflia` (opt-in and clause-log-only like
`qf_lia`; a signature mixing Int and Real, such as `(Int) Real`, is rejected
as QF_LIRA), the replay already valued numerals in Int and keyed
applications by identity, and the reconstructor renders the QF_UFLRA
encoding over Int: `(_vars : Nat -> Int)`, `(_int : Int -> _U)`,
`(_ifuns : Nat -> List _U -> Int)`, with `first | omega | grind` for every
lemma, rewrite, and argument-equality helper (`omega` reads applications as
atoms; a Lean probe of six shapes, Farkas over applications, congruence
through `_int`, rounding, tightening, normalized arguments, and `ite`
arguments, passed before any code changed). The stress runs found one
reconstructor gap that is not integer-specific: an `ite` whose branches are
one term, `(ite c a a)`, which Z3 keeps inside a product or an application
and for which it logs both gate clauses and the bare equality
`(ite c a a) = a` as a tseitin step; the gate lemma tried only the
then-branch orientation (so the else gate `c or (ite c a a) = a` was
rejected) and had no case for the unit clause. Both are now proved by a
case split on `c` with `ite_eq_left` and `ite_eq_right`; the lemma is
fragment-independent, though Z3 was observed to log these clauses only for
Int input (over Real and the uninterpreted sorts it simplified the `ite`
away in every input tried; a hand-added sort-valued unit gate on a QF_UF
certificate is accepted and Lean-verified). 6 of 38 random `ite` instances
failed before, none after; the shape is pinned by a documented input and a
random seed. Twelve documented inputs
(the Int twins of the QF_UFLRA set, a gcd conflict and tightened and
rounded bounds through an application, the same-branch `ite`, a Bool-only
predicate over Int atoms, and one input showing all five hint kinds), eight
pinned seeds, and 124 random instances (plain, with a sort, with `ite`,
both) verify under the standard axioms; the QF_LRA and Boolean matrix
cells and every earlier module verify unchanged. Not done: QF_LIRA, the
legacy core's integer steps (`--core legacy` rejects both integer
fragments), and a z3test `uflia_*.smt2` matrix cell.

**Integer `div`, `mod`, and `abs` (2026-10-15).** Both integer fragments
rejected `div`, `mod`, and `abs` at the exporter ("unsupported arithmetic
operator"), although QF_LIA benchmarks use `div` and `mod` by numerals
routinely. A clause-log probe showed what the sat.smt arithmetic solver
emits for them: nothing new in the Farkas machinery, since `(div t k)` and
`(mod t k)` are opaque atoms of the `farkas`, `bound`, `cut`, and
`implied-eq` hints, plus the solver's own defining clauses `k (div t k) +
(mod t k) = t`, `(mod t k) >= 0`, `(mod t k) <= |k| - 1` under a hint
`arith` whose arguments are the negated clause literals (the `name()` of
the theory solver, which `th_euf_solver::add_clause` records for every
axiom it adds without a hint of its own; the three clauses appear even when
the input mentions `div` alone, and for negative `k` too). `abs` never
reaches the log: the rewriter replaces it by `(ite (>= t 0) t (- t))`, and
an assertion the rewriter folds outright (`(>= (mod x 5) 5)` becomes
`false`) is assumed as the empty clause. A Lean probe confirmed that Lean's
Int `/` and `%` follow SMT-LIB's Euclidean convention, negative divisors
included, and that `first | omega | grind` proves the axioms and the folded
facts (`omega` alone reads `/` and `%` by a positive numeral and leaves a
negative divisor's `t % -3` as an atom, where `grind` closes the goal). Now:
the exporter accepts `div` and `mod` by a nonzero numeral constant and
`abs` as atoms of the linear forms (`integer_divisor`; a zero or term
divisor and `rem` stay rejected), the replay builds the log's `div`, `mod`,
and `abs` terms, keeps the atoms opaque, and shape-checks `arith` hints
like `cut` (`check_arith_hint`), and the reconstructor declares `div`,
`mod`, and `abs` in Int certificates only, renders them as `/`, `%`, and
the classical `ite` of SMT-LIB's definition, treats them as atoms in the
Farkas re-derivation, accepts an `arith` th-lemma without premises or
coefficients whose literals are linear arithmetic atoms (Real certificates
too, where `grind` proves it), and rejects every `div` or `mod` node whose
divisor is not a nonzero constant wherever it occurs, because Lean's `x /
0 = 0` would prove unsatisfiability under one interpretation of SMT-LIB's
uninterpreted division by zero only. Six documented QF_LIA inputs (`div`
in a bound conflict, a gcd conflict through `mod`, the folded assertion, a
negative divisor, `abs`, division of a sum), one QF_UFLIA input, five
pinned seeds of a new `random_division_instance` generator, and 151 random
instances (89 QF_LIA, 62 QF_UFLIA, every hint kind observed) verify under
the standard axioms; the tampering tests cover coefficients on an `arith`
lemma, a Boolean literal, the empty clause, a zero or variable divisor, a
Real `div` declaration, a swapped operator in the input, and a false
`arith` unit lemma that Lean rejects without publishing a proof. Not done:
`div` and `mod` by a term (nonlinear; Z3 axiomatizes them with `abs` of
the divisor), `rem`, `to_real`/`to_int`, and the legacy core's integer
steps.

**Harmless front matter is ignored instead of rejected (2026-10-15).** The
exporter accepted `(set-option :produce-proofs true)` and nothing else, and
only `check-sat`, `get-proof`, and `exit` as queries, so z3test regressions
such as `core.smt2` (`:auto-config`, `:produce-unsat-cores`, a named
assertion, `get-unsat-core`), `3220.smt2` (`:sat.local_search`,
`:model_validate`), `z3.4`/`z3.5.smt2` (`:produce-models`), and
`strategy-par-or-2.smt2` (`check-sat-using (par-or smt ...)`) were rejected
at the frontend although Z3 solves them and their assertions are in the
certified fragments; a scan of the 951 `regressions/smt2` inputs (828 of
them rejected at the frontend) found 36 that pass it once such front matter
is ignored, 28 of them satisfiable, and 7 unsat ones that export. The
certificate is a statement about the parsed assertions that
Lean checks, so an option that only configures Z3's output, model
production, resource limits, or search cannot change what is certified.
The exporter now ignores an allowlist of such options (`_IGNORED_OPTIONS`,
by Z3's parameter name with `-` and `_` identified, plus the `pp.*` and
`model.*` families), accepts `check-sat-using` with any tactic as the one
query, the output queries `get-model`, `get-unsat-core`, `get-assignment`
after it, and `get-info`, `get-option`, `echo` anywhere; none of them reach
the solver run or the certificate, whose `source_smt2` stays verbatim. It
still rejects, with messages naming the reason, options that change how
the input is read (`numeral-as-real`, `int-real-coercions`,
`smtlib2_compliant`, under which Z3's scanner reads `-1.0` as a symbol and
Int/Real coercions are off, so a file declaring `|-1.0|` is `sat` for Z3
and `unsat` for the exporter's reading; and `rewriter.*`), the proof-production
and preprocessing options the exporter sets itself (`sat.smt`,
`solver.proof.*`, `smt.clause_proof`, `smt.solve_eqs`,
`combined_solver.*`; z3test's harness pins the `sat.smt` rejection), and
every option not on the allowlist. The five regressions above now verify
through the clause log and the propositional ones through the legacy core
too (kept verbatim as `CONFIGURED_INPUTS` in the test modules); `3282.smt2`
stays rejected for `rewriter.flat`, `3626.smt2` for
`combined_solver.ignore_solver1`, and `3732.smt2` for its second query.

**Integer input through the legacy proof object (2026-10-16).** `--core
legacy` rejected `qf_lia` and `qf_uflia` ("certified through the clause log
only") because theory_lra's integer steps were not inventoried. A probe over
the documented inputs and 200 random instances found no integer rule names:
the legacy core emits the Real hints (`farkas`, `bound`, `implied-eq`,
`triangle-eq`) over Int, plus three shapes of its own. A bare `(_ th-lemma
arith)` with premises is a cut (`lia_move::cut` assigns the derived bound
literal with an empty parameter vector), a bare one without premises is a
div or mod axiom stated as `(or false l)` and resolved with the unit `true`
(the `true-axiom` rule), and a lattice conflict (`lia_move::conflict`, for
example `x + y = 1`, `2x - y = 1`) is labelled `farkas` with coefficients
that do not refute its premises rationally. The exporter now accepts the
integer fragments on this path (opt-in as for the clause log,
`parse_legacy_assertions(..., integer=True)`), keeps the bare steps as the
`arith` hint, strips the coefficients of a `farkas` or `bound` step over Int
that do not re-derive (`_integer_coefficients_certify`, the decision the
clause-log replay makes), and declares Int sorts; the reconstructor accepts
`arith` lemmas with premises and coefficient-free Int `farkas`/`bound`
steps with premises (shape-checked, Lean proves them), renders `true-axiom`
as `True.intro` and lets the unit `true` resolve `false` literals, proves
congruence through `div`, `mod`, and `abs` as a grind lemma, and checks the
nonzero-constant-divisor rule on the nodes the theorem states (the
assertions and their subterms) rather than on every node: Z3's rewriter
cancels the common factor of `(div (* 2 x) (- 2))` through `(ite (= 0 (-
2)) (div (* 2 x) 0) (div (* x 1) (- 1)))`, whose dead branch divides by
zero without reaching the statement (the ite gate helper skips a branch
without a linear form). All 15 documented QF_LIA and 12 QF_UFLIA inputs
verify through the legacy core under the standard axioms, as do the random
instances of every integer generator (see the iteration summary for
counts). Tests: `test_proof_certificate.py` (legacy integer export,
coefficient stripping, parameter validation), `test_proof_to_lean_lia.py`
(`TestLegacyIntegerLeanIntegration`, the `true-axiom` and dead-branch
validation), `test_proof_to_lean_uflia.py`
(`TestLegacyIntegerMixedLeanIntegration`). Still open: the matrix runner's
legacy cell remains propositional-only (z3test change), and no integer
rule name other than the bare `arith` was observed, so `gomory-cut` and
`gcd-test` labels stay rejected until an input emits them.

**Incremental scripts, one query at a time (2026-10-16).** The frontend
accepted exactly one `check-sat` and rejected `push`, `pop`, `reset`,
`reset-assertions`, `check-sat-assuming`, a second query, and any assertion
after the query; 175 of z3test's 951 `regressions/smt2` files are
incremental. Now `proof_certificate.query_snapshot(source, query)` replays
the script with Z3's default scoped declarations (a declaration inside a
popped scope is gone with its assertions; `reset-assertions` is modelled as
Z3's `cmd_context::reset_assertions` does it, removing every assertion but
keeping the declarations and the open scopes, not as SMT-LIB's "pop every
scope") and returns the
declarations, definitions, and assertions in scope at the selected query,
with the query's assumptions (`check-sat-assuming`'s list, or Z3's
`check-sat` with literal arguments) appended as assertions. A script with
one query needs no index; several need `--query N` (or `query=` in the
Python API), and a script without any query is query 0 over its final
state. Both exporters solve the snapshot non-incrementally and record the
index as the certificate field `query` (bundle format version 2); the
reconstructor validates the field, rebuilds the same snapshot from the
original script, binds the certificate's assertions to it as before, and
writes the query into the Lean file's header, so the theorem is a
statement about that query of the script and a certificate pointed at a
different query is rejected. Verbatim z3test inputs now certified:
`incsat` (query 2, propositional, BitVec constants in a later scope),
`t143` (query 1, assumptions through `define-fun`), `3632` (a query inside
`push 1`), `3732` (both queries, QF_UF), `unsatcore` (both queries,
QF_UFLIA, an assumption literal). Tests: `test_proof_certificate.py`
(`_INCREMENTAL`, snapshots, scoping, rejections, CLI), `test_proof_to_lean.py`
(`INCREMENTAL_INPUTS`, the tampered query index), and the Lean integration
tests of `test_proof_to_lean_integration.py`, `test_proof_to_lean_uf.py`,
`test_proof_to_lean_uflia.py`. Still open: `define-sort` (61 of the
incremental corpus files are rejected for it first) and the
`global-declarations` option (rejected).

**Propositional rewrites as direct proof terms (2026-10-16).** A Boolean
`rewrite` step was proved by a truth table (a `cases` on every atom's
decidability witness and `decide` per assignment), exponential in the number
of atoms: the legacy core's proof of z3test `3632.smt2` flattens conjunctions
over 13 to 14 atoms and failed on `maxHeartbeats`, so the input was certified
through the clause log only, and the scaling survey above had listed this
cliff since 2026-09-25. `proof_to_lean._PropositionalProver` now proves the
equivalence directly: both sides are read as gates over the atoms (xor, Boolean
`ite`, and `distinct` expanded exactly as the Lean rendering does), each
direction assumes one side, propagates truth values through the gates (one
typed `have` per step, each justified by the immediate operands as the
def-axiom gate proofs are), and where propagation does not settle the other
side it splits on an atom with `Decidable.em` until each branch proves the
side or reaches a contradiction. Double negations are cancelled by
`Decidable.byContradiction` on atoms only (instance synthesis for a compound
proposition of 24 atoms fails), so the lemma takes as parameters exactly the
atoms whose decidability the term uses, the proof stays axiom-free, and the
refutation keeps eliminating the witnesses constructively. The truth table is
the fallback for an equivalence the prover cannot settle (a false one, more
than `_STRUCTURAL_REWRITE_STEPS` steps, or more than
`_STRUCTURAL_REWRITE_CHARS` rendered characters: each `have` states its full
proposition, and a parity rewrite over seven atoms renders 2.8 MB that Lean
rejects on heartbeats only after 25 s, whereas its truth table fails in 4 s),
and Lean rejects it as before.
3632 through the legacy core now checks in under a second, axiom-free, as do
flattening, duplicate removal, de Morgan, implication chains, and
distributivity over 24 atoms, a Boolean `distinct` over 8, and xor and ite
nests (`test_wide_boolean_rewrites_are_proved_structurally`). Tests:
`test_proof_to_lean.py` (needed witnesses, the fallback, the structure
expansion) and `test_proof_to_lean_integration.py`.

**Two rejections found by a scaled random stress (2026-10-16).** Random
instances larger than the pinned seeds (six to seven variables or constants,
18 to 24 constraints, nesting depth 3, 40 seeds per generator, both cores,
Lean-checked) found two rejections of inputs Z3 solves; QF_LRA, QF_LIA,
QF_UFLIA, and QF_UF without `ite` had none. (1) The sat.smt arithmetic
solver logs its axiom for a Real division by a numeral, `q = 0 or q * (p / q)
= p`, with its first literal as the constant `true` (the negation of the
false disequality `(= q 0)`, elided from the clause) when a numeral quotient
such as `(/ 1.0 2.0)` inside a ground atom is internalized as a term next to
a conflict at level zero; the replay rejected the hint ("hint literal is not
an arithmetic atom") on 10 of 23 unsat QF_UFLRA instances through the clause
log (the legacy core certified them). `infer` now drops `true` literals from
theory hints before the shape checks (a hint of nothing else stays rejected,
and `false` is still not an arithmetic atom), and Lean proves the unit
equality `2 * (1 / 2) = 1` as any `arith` lemma. (2) The gates of an `ite`
over the uninterpreted sort whose condition is a negation, `(ite (not q) a
b)`, reach the log with the double negation collapsed, `q or (ite (not q) a
b) = a`, which `_ite_gate_lemma` did not recognize ("unsupported or invalid
def-axiom clause") on 5 of 24 unsat QF_UF instances with `ite` terms. The
gate lemma now splits on the condition's innermost negand and proves the
condition and its negation by lifting through the negations (`fun _n0 => _n0
_hc`), so it stays axiom-free and the equally collapsed guards of deeper
negations are covered too. Tests: `test_proof_certificate.py`
(`_LRA_DIV_LOG`, the `true` literal of a coefficient hint),
`test_proof_to_lean_arith.py` (`REAL_DIVISION_AXIOM`, both cores),
`test_proof_to_lean_uflra.py` (`uflra_division_axiom`),
`test_proof_to_lean_uf.py` (`UF_NEGATED_ITE_CONDITION`, both cores,
nested negations, and rejection of a gate with its guard reversed).

## Arithmetic proof infrastructure

### Constant rows in native implied-equality checking (2026-10-19)

The native `implied-eq` checker now handles constant inequalities before
selecting a variable for Fourier-Motzkin elimination. A slack premise such
as `0 <= 1`, or a row reduced to one by equality substitution or elimination,
previously dereferenced an empty coefficient map and could crash or fall
back to the SMT solver.

Slack constant rows are skipped, zero rows retain their tightness
dependencies, and contradictory constant rows discharge the hint. Tight-row
state is cleared between hints, including after an early contradiction.
Native `proof_replay` regressions cover Real and Int rows, zero-weight
strict premises, checker reuse, and replay without SMT fallback. Tautologies
alone still cannot prove an unrelated equality; solver search and Lean's
independent verification are unchanged.

### Native implied-equality conclusions (2026-10-19)

The native arithmetic checker requires an `implied-eq` hint to end in a
disequality with a nonzero numeral coefficient. Previously,
`(implied-eq 0 (not (= x y)))` erased its target row and verified even
though `x != y` is satisfiable. `(implied-eq 1 (<= x 0.0))` also verified:
without a concluding disequality, the consequent row was still the initial
zero row. Neither is evidence for an implied equality.

Only a successfully parsed concluding disequality can now reach the
implied-equality check, and its coefficient cannot erase the conclusion.
Empty and incomplete hints are rejected too. Native `proof_replay`
regressions cover these malformed hints over Real and Int, and preserve
valid equality propagation with positive or negative nonzero conclusion
coefficients. This changes native checker acceptance, not solver search
or Lean's independent verification of the implied equality.

### Native arithmetic row strictness (2026-10-16)

The native arithmetic checker now keeps strictness on each linear row, not
in one flag shared by the premises and the consequent. Previously,
`(farkas 0 (< x 0.0))` was accepted even though its only literal is
satisfiable: multiplying the strict inequality by zero erased its terms
but left a strict `0 < 0`. A second counterexample,
`(bound 1 (< x 0.0) 1 (<= (- x x) 0.0))`, was accepted because the strict
premise incorrectly made the separate consequent row strict. Both
literals hold at `x = -1`.

Strictness now follows only nonzero weighted contributions to the row
being checked and is preserved when rows are combined or equalities
eliminated. A bound hint still verifies when either row independently
reduces to a contradiction. Native `proof_replay` regressions cover both
strict comparison orientations, negated non-strict comparisons, zero weights on premises and
consequents, and valid strict contradictions. This repairs native checker
acceptance without adding proof rules or changing Lean's independent
verification boundary.

### Real QF_LRA hardening (2026-10-07)

The planned LassoRanker example contains 1,463 Real variables and 105 original
assertions. Its source is pinned in z3test under
`regressions/proofs/lean/real/`, unchanged and with its upstream license.
A proof-free run reports unsat in about one second, while the no-preprocessing
clause log contains about 600,000 inferences and 39 MB of text. Replaying the
whole log in Python exceeds the small-canary budget.

The exporter now reduces large logs using native dependency annotations,
validates the dependency graph, and reconstructs the selected refutation.
Every retained step is still checked, and all original assertions remain in
the certificate. Cached normalization and literal keys avoid repeated AST
traversals. EUF cc/comm annotations are recognized without turning their
conclusions into assumptions.

This exercise exposed a native proof-trimmer defect: when adding a clause
with one unassigned literal, it failed to check whether another literal was
already true. It could therefore propagate from a satisfied clause and
produce an invalid dependency core. The minimized case is `p`, `not q`,
`p or q or r`, `not r`, `not p`; only the final `not p` contradicts the
preceding assertions. The trimmer must not propagate `r` from the satisfied
third clause. Native and external replay regressions cover this case.

The reconstructed certificate has about 67,000 nodes and 41,000 proof steps,
so a single deeply nested Lean term is unsuitable. Arithmetic proof DAGs are
outlined at shared subproofs into independently checked lemmas with explicit
input and hypothesis scopes (since 2026-10-12 every fragment above 500 steps
is outlined, and chains are also cut every 500 nested steps; see "Long
refutations in every fragment" above). Large arithmetic rewrites normalize each atom
separately, then reconstruct and/or rearrangements over abstract propositions.
This avoids sending large Boolean equivalences back through arithmetic search.

The complete reconstructed LassoRanker refutation was accepted by the pinned
Lean kernel with `--trust=0` and warnings treated as errors. The final matrix
run reports `lean-verified`, with 109 seconds for certificate production and
830 seconds for reconstruction and Lean checking. All 105 original assertions
and the input, raw log, reduced log, certificate, and checked proof hashes were
retained and verified. The generated source is approximately 89 MB, so
this is a correctness milestone, not yet an efficient large-benchmark checker.
Because this cost is unsuitable for routine CI, LassoRanker is manual-only:
neither PR CI nor scheduled/nightly builds run it. An explicit invocation of
the matrix runner selects the file and its production/checking budgets.
Automatic CI retains the small examples and minimized regressions, with their
existing budgets and strict rejection policy unchanged.

The arithmetic proof infrastructure is slightly broken and must be repaired
before milestone 3 can claim checked arithmetic. Known defects:

- **Fixed (2026-09-28), two checker-side defects and one producer defect found
  by the matrix.** The two `farkas` misses on QF_RDL `bignum_rdl2` were the
  arithmetic checker not parsing printed numerals: a replayed log carries
  non-integers as `(/ n d)`, and the checker accepted only plain numerals and
  `(- n)`, so any hint with a fractional constant was rejected (branch
  `proof-checker-numerals`). The 16 `bound` misses on QF_LIA `bignum_lia1`
  were the producer: `lar_solver::explain_implied_bound` handed every premise
  to the consumer with coefficient 1 behind a TODO, because the dependency
  flattening had lost the row coefficients. A bound on column `j` from row
  `sum_k a_k x_k = 0` uses each other column's bound with Farkas coefficient
  `|a_k / a_j|`; the bound analyzer now supplies those weights through
  `implied_bound` (branch `lp-bound-explanation-coefficients`). This is the
  second of Nikolaj's two coefficient situations, bounds derived from a
  tableau row over slack columns. After both fixes every `farkas` and `bound`
  hint in the canary set is accepted.
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
