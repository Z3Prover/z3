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

The reconstruction tests (`examples/python/test_proof_to_lean*.py`) check
Lean through `examples/python/lean_test_support.py`. Most of their
certificates check in a tenth of a second, while each run of the helper
spends about half a second starting Lean, so the tests check each
certificate once, with its `#print axioms` report in the same run; build
the project once per process (`Z3_LEAN_SKIP_BUILD=1` makes the helper skip
`lake build`); and check the documented inputs of a test in a few
concatenated files (`prefetch`). Five stress tests, whose inputs exercise
the size and memory limits of the reconstruction (QF_LIA
cut_lemma_02_002, QF_UF NEQ004_size4, the 13,000-node BubbleSort circuit,
and two wide random division instances), run only with
`Z3_LEAN_SLOW_TESTS=1`. On a 16-core Darwin arm64 machine these
changes took the suite from 30 minutes to under 10.

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
- Wide n-ary connectives (2026-10-20). A conjunction or disjunction of a few
  hundred operands (z3test's QF_UF `NEQ004_size4` asserts one of 338
  literals) renders as a right-nested `And`/`Or` chain whose `def` exceeded
  the default `maxRecDepth` (512); only the main theorem raised it. The
  generated file now raises it once for its whole namespace, so definitions,
  lemmas, and steps are no longer cut off by the limit (not a trust setting).
  and-elim projects by field notation (`_step_N.2.2.1`), which elaborates
  inside out from the known type, and unit resolution cuts eliminated
  literals with `(h.resolve_left n)` instead of one `Or.elim` case split per
  literal; the old forms created metavariables per level and took 36 s
  (200-operand clause-log and-elim) and 9 s (260-literal resolution), now
  about 7 s and under a second. `examples/python/test_proof_to_lean_wide.py`
  covers 200-260 operands through both cores. Still open: at 600 operands the
  outlined proof steps (more than 500 proof nodes) exceed the heartbeat limit
  on a step with a hundred quadratic `_inputs` projections, and
  `NEQ004_size4` itself fails at export (the clause-log trimming step rejects
  `declare-sort`; fixed 2026-10-27, see "Trimmed QF_UF logs" below).

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
  Farkas constraint. An `alldiff` clause of gate shape (a `distinct` below
  the root against the disjunction of its pairwise equalities) is a
  `def-axiom` that Lean proves from the pairs; any other `alldiff` clause
  must be tied to the original `distinct` assertion, never trusted as an
  unconditional theory lemma.
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

**Commands that only print, define-const, and exit (2026-11-07).** A rescan
of the 959 `regressions/smt2` inputs (the export classification of every
query, with the reason for each rejection) found 35 unsat queries in the
certified fragments, all of which export and verify in Lean, and frontend
rejections for commands that do not touch the assertion stack: `simplify`
(43 files), `apply` (25), `get-value` (16), `eval` (11), `display` (6),
`get-assertions`, commands after `exit` (14), `define-const`, the debug
option `:trace` (12), and `:global-decls false` (Z3's default). The
exporter now drops the printing commands (`_OUTPUT_COMMANDS`) unless one
contains a `:named` label: Z3 keeps the label even when the command fails,
and a later `define-fun` of the same name is then an error in Z3 but the
definition in the snapshot, so dropping it could certify a script that Z3
answers sat. It reads `define-const` as a definition, ends the
script at `exit` without reading further (Z3's parser throws
`stop_parser_exception` there, so text after it need not even parse),
ignores `trace`/`trace_file_name`, and accepts `:global-decls` and
`:global-declarations` with `false` only. Four more unsat queries verify
through the clause log: `abs.smt2`, `t119.smt2` (no check-sat, so the
certified statement is that its final state, after two resets and with
`apply` between assertions, is unsat), `3570.smt2` (a
unary `+` and a chained `<`), and `z3.29.smt2` query 1
(`OUTPUT_COMMAND_INPUTS`). Still rejected: `minimize`, `maximize`,
`assert-soft` and `:opt.*` options (they change what check-sat answers),
`get-consequences` (a query of its own), `include`, `:error-behavior`, and
`:global-decls true`; the other newly parsed files are satisfiable or
leave the fragments (quantifiers, nonlinear arithmetic, strings). (Since
2026-11-07 the optimization commands are accepted; see the next note.)

**Optimization commands; distincts of Booleans (2026-11-07).** With a soft
assertion or an objective in scope, Z3's `check-sat` runs the optimization
context with the assertions and assumptions as hard constraints
(`cmd_context::check_sat`), and its first check of them is the unsat
answer (`opt::context::optimize`). The exporter now drops `assert-soft`,
`minimize`, `maximize`, and `get-objectives` like the output commands
(`:named` inside one is rejected) and ignores the `opt.*` options, so the
certificate states that the hard assertions are contradictory. A later
unsat that only reports an exhausted Pareto front or box (hard constraints
satisfiable) gets no certificate: the exporter's own solver answers sat
(tested). Of the 90 z3test files with optimization commands, the frontend
rejects 9 now (input-reading or unknown options), and the two unsat
queries in the fragments, `3402.smt2` and `3524.smt2` (QF_LIA with
`assert-soft`), verify (`OPTIMIZATION_INPUTS`). `3524` also needed a Lean
change: its rewrite folds distincts of 8 and 13 Booleans, false by
pigeonhole, and `omega`, tried before `grind` over Int, ran out of
heartbeats on their unfolded pairs (a heartbeat timeout escapes `first`).
Each distinct of three or more Booleans a grind lemma reaches is now
stated false from its first three arguments' pairs (`_bool_distinct3`,
`_boolean_distinct_facts`) and rewritten away by a pre-order `simp only`
before the tactic, also in the attempt that first generalizes div, mod,
and abs atoms (the facts then name them); the minimized QF_LIA input took
80 s and failed, its variant over mod atoms 66 s, both now 1 s
(`test_distincts_of_three_or_more_booleans_are_false`).

**One-argument `+`, `*`, and `distinct` in the clause log (2026-11-07).**
Z3's parser keeps `(+ t)`, `(* t)`, and `(distinct t)` as applications of
one argument. Once an assertion folds to false, sat.smt logs an empty
`(assume)` and then the later assertions unsimplified, so these terms reach
the clause-log replay, which rejected them ("unsupported operator in the
clause log": 8 of 89 unsat inputs of a random QF_LIA generator with Boolean
structure, and LRA, LIRA, UFLIA, array, and UF variants). The replay now
rebuilds them through the API with one argument (`_ONE_ARGUMENT_HEADS`),
which yields the input's own terms; the certificate and Lean already
handled them, since the assertions come from the input. A zero-argument sum
or a sum of a Boolean is still rejected. Division by a zero numeral in such
a tail stays rejected by the fragment check. Tests:
`test_one_argument_sums_products_and_distincts_after_a_false_assertion` in
`test_proof_certificate.py` and its Lean counterpart in
`test_proof_to_lean_arith.py` (`ONE_ARGUMENT_INPUTS`).

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
incremental corpus files are rejected for it first; accepted since
2026-10-19, see below) and the `global-declarations` option (rejected).

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
`_STRUCTURAL_REWRITE_CHARS` rendered characters, or up to twice those when a
normalized rewrite's links use their allowance, see "Link allowance of
normalized rewrites": each `have` states its full
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

**define-sort aliases (2026-10-19).** `proof_certificate.query_snapshot`
accepts `(define-sort name (parameters) sort)` and keeps it in the scope it
is made in, like a declaration. Z3's parser expands every use of the alias
(substituting the parameters) both when the exporter parses the snapshot and
when the z3 executable writes the clause log, so the certificate, the
reconstructor's rebuilt snapshot, and the Lean statement mention only the
expanded sorts, which pass the usual sort checks; no Lean change was needed.
The exporter rejects a malformed definition (no parameter list, a body of
other than one sort, a non-symbol name or parameter) and a repeated
parameter; Z3 rejects an unknown body sort and a name already declared or
defined. Tests: `test_proof_certificate.py`
(`test_define_sort_aliases_are_expanded_and_malformed_ones_rejected`) and
`test_proof_to_lean_uf.py` (`TestDefineSort`: a plain and a parametric
alias checked in Lean, an alias in a popped scope).

**Int theory lemmas over generalized atoms (2026-10-21).** The iter-027
stress input `div` seed 67 (QF_LIA, 547 theory lemmas over `div`, `mod`,
and `abs` by the numerals -3, -2, 2, 3, 4) was the one clause-log
certificate still failing in Lean: a `farkas` step and four `cut` steps
whose literals sum a dozen such atoms hit `maxHeartbeats` in `first |
omega | grind (splits := 64)`. The cause is not the lemma size: `omega`
reads `t / -3` but leaves `t % -3` as an unbounded atom, so every lemma
over a negative divisor fell to `grind`, which splits each `abs` ite and
took 105 s on one cut when given no limit. The atoms are opaque to the
step anyway: a `farkas` or `bound` with coefficients is a combination the
reconstructor re-derived over them (`_check_th_lemma`), and a cut lists
the bounds and the div and mod rows it rests on as literals. So `_grind_lemma`
now proves an Int th-lemma under those hints in two attempts: first the
definitions outside the atoms are unfolded, every `mod` atom gets its
bounds `0 <= m < |k|` (`Int.emod_nonneg`, `Int.emod_lt_of_pos`, through
`Int.emod_neg` for a negative divisor; the solver fixes these at base level
and omits them from the lemmas it explains, which left one cut unprovable
without them) stated and reverted, the atoms are `generalize`d to fresh
integers, and `omega` (farkas, bound: it closes the linear goal at once)
or `grind (splits := 64)` (cut and the coefficient-free Int farkas or
bound: cutsat proved a twenty-atom cut in a second where omega took two
and a half minutes) decides the linear goal; if that fails, the atoms are
unfolded and the previous proof (gate helpers, `first | omega | grind`)
runs unchanged. `arith` axioms, `euf`, `implied-eq`, and every Real lemma
keep the old proof. Nothing is trusted: `generalize` and the reverted
library facts are ordinary tactics, and a false cut over a `mod` atom
fails both attempts (tested). Seed 67 now verifies in 11 s of Lean; the
other division seeds and the documented inputs are unchanged in time.
Tests: `test_proof_to_lean_lia.py`
(`test_integer_theory_lemmas_generalize_their_opaque_atoms`: the two-branch
text per hint and per atom kind on four documented inputs and seed 67, Real
untouched; `test_wide_division_instance_verifies_over_generalized_atoms`;
the `cut` case of
`test_false_integer_lemmas_without_coefficients_never_publish_a_proof`;
`test_generalized_attempt_falls_through_to_the_unfolded_proof`: the unit
`x >= 3 * (div x 3)` under the `cut` hint, false over the generalized atom
and proved by the fallback, Lean accepting; the `mod` axioms would not do,
the stated bounds prove them generalized).
Not done: a rewrite whose assertion sums a dozen `abs` terms still splits
every ite (`(assert (<= (+ (abs x0) ... (abs x11)) 11))` times out in the
rewrite lemma, not in the theory lemma; done 2026-10-22, next note), and
the fallback itself would still benefit from the `mod` facts (`omega`
would then replace `grind` on negative divisors).

**Lattice lemmas: two million heartbeats (2026-10-23).** The upstream
pull request carrying iterations 26 to 33 (Z3Prover/z3#11276) failed its
Lean step on `test_wide_division_instance_verifies_over_generalized_atoms`:
GitHub tests the branch merged with upstream `master`, and the simplex
changes merged there since the fork's base (pivot-cost and redundant-bound
handling, #11253 and #11256) make the solver search seed 67 differently.
The clause-log proof has 1,032 theory lemmas instead of 547, and one `cut`
of 47 literals (25 distinct) over thirteen `div`, `mod`, and `abs` atoms
with six `mod` bounds exhausted the million heartbeats under
`grind (splits := 64)` in its generalized attempt; the same text verifies
at 1.5 million, and `omega` proves that generalized goal in under a second.
Neither procedure dominates on lattice goals (the note above has the
opposite case, a twenty-atom cut where `omega` took minutes), and trying
one before the other is not an option: a heartbeat timeout is a runtime
exception that Lean's `first` does not catch, so an attempt
`first | (set_option maxHeartbeats 400000 in omega) | grind` failed six
lemmas of this file that `grind` alone proves (observed; the timeout fails
the whole lemma). So `_grind_lemma` now gives a cut or a coefficient-free
Int farkas or bound over generalized atoms (`_lattice_step`) two million
heartbeats (`_LATTICE_LEMMA_HEARTBEATS`); lemmas with coefficients
(`omega`), the unfolded fallback, and every other lemma keep the million.
Nothing is trusted: a heartbeat budget bounds work, and a false
generalized goal still fails and falls through to the unfolded proof
(tested). Checked against a local merge of the fork with upstream
`ac62f5a6a`: seed 67 verifies, and the division seeds, the documented
QF_LIA inputs, and the QF_UFLIA seed-75 file keep their proofs. Tests:
`test_proof_to_lean_lia.py` (the lemma-shape test expects the budget per
hint; the wide seed-67 test asserts it), `test_proof_to_lean_uflia.py`.
Still open: a tactic that races `omega` and `grind` by budget would need an
elaborator catching runtime exceptions (`Lean.Core.tryCatchRuntimeEx`),
hence `import Lean` in every generated file; and the loop's local gate
tests fork `master` alone, so a solver change upstream shows only in
upstream CI.

**Theory rewrites over bridged atoms (2026-10-22).** Z3's rewriter logs
`(abs x)` as `(ite (<= 0 x) x (* -1 x))`, so the `rewrite` step relating
an assertion over twelve `abs` terms to its normal form is a tautology
over 24 ite atoms (the SMT-LIB renderings of `abs`, `ite (x >= 0) x (-x)`,
against the rewriter's form); `omega` splits ite terms, as `grind` does,
so the lemma `first | omega | grind (splits := 64)` hit `maxHeartbeats`
after 30 s while the Farkas lemma over the same atoms verified
generalized (previous note). Theory rewrites now take the same two
attempts as the Int theory lemmas (`_grind_lemma` with
`_opaque_rewrite_tactic`: `omega` over Int, `grind` over Rat), with one
addition: `abs` is keyed as its defining ite (`_real_atom_key`), and
every two atoms of one key among those to be generalized are first
bridged by an equality `have _eA_B : term_A = term_B := by unfold ...;
first | omega | grind` (a two-way split), reverted into the goal so that it
survives as an equation between the fresh variables
(`_atom_bridge_facts`, also applied to the theory lemmas' attempt). A
rewrite that uses an atom's definition (`(ite c t t)` to `t`, a `mod`
folded by its bounds) fails the attempt fast on the small linear goal and
is proved unfolded as before. The 12-`abs` input verifies in 1.3 s of Lean
through the clause log and in 0.9 s through the legacy core (which
rewrites each `abs` to its ite on its own, bridged the same way); the
variant writing `(ite (>= x 0) x (- x))` out verifies too. The condition
of an ite is keyed canonically (`_condition_key`): the atom with its
leading coefficient positive, over Int primitive with the constant
rounded (as the rewriter divides `0 <= 2x` to `0 <= x`), choosing the
complement (over Int `-t + 1 <= 0` for `t <= 0`, over Real the strict
`-t < 0`) with the branches swapped when the leading coefficient is
negative. Before, the strict `(ite (> x 0) x (- x))` was keyed apart from
the rewriter's `(ite (<= x 0) (* -1 x) x)` over Int, because
`_polarity_constraint` tightens `x > 0` to `x - 1 >= 0` before the key
saw a strict relation to flip (review of this change), and `(abs (* 2 x))`
from its ite with the divided condition; both 12-wide variants hit
`maxHeartbeats`, both verify in about a second now, and the Int ite under
an application (`uflia_ite_argument`) gets its argument helper as over
Real. `(ite (<= x 0) -x x)` and `abs x` still have different keys: equal
in value (the branches agree at zero), different atoms. Nothing is
trusted: a forged rewrite `|x| >= 3 <-> 2 <= ite` fails both attempts
(tested), and a wrong key could only cost a bridge the theory tactic
cannot prove. An ite with a branch outside the linear forms (the dead
`div` by zero of seed 77) is opaque to the key, as it was. Tests:
`test_proof_to_lean_lia.py`
(`test_rewrites_bridge_atoms_with_one_key_before_generalizing`: keys and
lemma text on `wide_abs_instance` with and without the ite spelled out,
the strict and the `(* 2 x)` variants bridged, the Int complement keyed
with a swap; `test_wide_abs_sum_verifies_over_bridged_atoms`, both cores
and the strict and scaled variants;
`test_false_bridged_rewrites_are_rejected_by_lean`),
`test_proof_to_lean_uflia.py` (the ite argument helper over Int). All
QF_LRA, QF_UFLRA, QF_UF, QF_UFLIA and Boolean suites and both CI matrix
cells are unchanged in outcome.

**Wide Farkas lemmas over `mod` atoms without the redundant bounds
(2026-10-22).** A random stress run at twice the usual size (seeds 70 to
89 of every generator, both cores) found no rejection but one slow
certificate: `random_division_instance(75, variables=12, constraints=36,
functions=True)` (QF_UFLIA, 2,815 steps) took 48 s of Lean on an idle
machine (140 s under the load of the stress run), of which one `farkas`
lemma of 33 literals (15 of them the div/mod definitional equalities Z3
lists as literals) over 26 `div`, `mod`, `abs`, and application atoms took
27 s (40 to 134 s under load) in its generalized attempt. The cause
was not the width: `omega` proved the same generalized goal in under two
seconds once the 28 `mod` bounds (`_mod_bound_facts`, 0 <= m < |k| for
each of the 14 `mod` atoms) were left out of its context, and `grind`
proved it in two seconds with them. `omega` eliminates a bounded variable
by case analysis over its range, so bounded, redundant facts multiply its
work. The bounds exist for cuts and coefficient-free Int lemmas, which
are shape-checked only and may rest on the base-level bounds Z3 omits;
a `farkas` or `bound` step with coefficients is re-derived over the atoms
alone by `_check_th_lemma` (rounding included), so its generalized goal
holds without them. `_grind_lemma` now states no `mod` bounds for such a
step (`_combination_certified`); cuts, coefficient-free lemmas, and
theory rewrites keep them. The seed-75 certificate verifies in 22 s on an
idle machine (its longest `omega` call 3 s); the lemma text of every other input is
unchanged except for the dropped `have _m`/`revert` lines on coefficient
steps, and the wide seed-67 input and the documented QF_LIA inputs still
verify. Nothing is trusted: the facts were ordinary `have`s and their
absence can only make a proof fail, never succeed wrongly. Tests:
`test_proof_to_lean_uflia.py`
(`test_wide_farkas_lemmas_over_mod_atoms_omit_the_redundant_bounds`:
seed 75 through z3, certificate, Lean kernel; every generalized lemma's
text checked by hint), `test_proof_to_lean_lia.py` (the lemma-shape test
now expects no bounds on coefficient steps). Still open: a direct
Farkas-combination proof term from the coefficients the reconstructor
already holds would make these lemmas independent of `omega`'s
elimination order altogether; the remaining 22 s of the seed-75 file are
spread over its 587 theory lemmas, none above 3 s.

**`cnf` bridges by propagation over opaque atoms (2026-10-23).** The
iter-032 scan left `mathsat/Wisa/xs-05-12-1-4-2-1.smt2` (QF_UFLIA, 720
steps) timing out in Lean with nine theory lemmas failing. All of them
were the exporter's `cnf` bridges: the input is one 3,500-character
assertion (a conjunction of equalities, a 40-way disjunction, and ten
Boolean `ite` terms over Int applications) whose root `ite` terms Z3
clausifies without the `ite` literal, so the 30 assumed gate clauses
(`(not c) or t`, and `c`'s conjuncts distributed over `e`) match no
conjunct and are tied to the assertion by `cnf` lemmas, which
`_grind_lemma` proved by unfolding everything and calling `omega` then
`grind`, both of which split every `ite` and disjunction. Such a clause
follows from its sources propositionally with the theory atoms opaque,
up to Z3's normalization of the atoms themselves (an equality's sides
reordered, a sum's operands reordered, a strict comparison written as
the negation of its complement). `_cnf_lemma` now proves it first by
`Classical.byContradiction` and the gate propagation of
`_PropositionalProver` (iter-018) in a classical mode over the Boolean
structure with every theory atom a leaf rendered by its definition name
(`_boolean_structure(..., leaves=...)`), after stating, as `have`
equivalences the theory tactic proves on its own, a chain of bridges
through the leaves of one constraint key and one bridge between two
complementary keys (`_leaf_bridges`, `_leaf_key`: coprime integer
coefficients, Int bounds rounded, equality sides unordered); the unfolded
`grind` proof stays as the second alternative of `first` and alone when
the prover finds no refutation (the `alldiff` clauses of `uf_ite_alldiff`
need the `ite`'s value). The fallback unfolds what the attempt did not,
and again a formula shared between the clause and the inside of a leaf (a
predicate's Boolean argument), which occurs folded once more when the
leaf is unfolded. Nothing is trusted: the term, the bridges, and
the fallback are checked by Lean. The Wisa file verifies in 13 s of Lean
(was a timeout after 900 s); its text grows from 0.75 MB to 2.7 MB (each
propagation step restates its proposition over the leaf names). Tests:
`test_proof_to_lean.py` (classical prover: bridges, `Classical.em`
splits, no instances), `test_proof_to_lean_lia.py` (`_leaf_key` up to
orientation, scaling, and complement), `test_proof_to_lean_uflia.py`
(documented input `uflia_root_ite_gates`: lemma shape, Lean, and the
fallback forced by a rejected structural term), `test_proof_to_lean_uf.py`
(the `alldiff` bridges stay with `grind`). Through the legacy core the same
input produced the first live `(_ th-lemma smt)` steps: `theory_lra`
restating a held bound in its own normal form (`(>= (+ (* -1 (cnt 1))
(* 1 (cnt 0))) -1)` from `(>= (+ (cnt 0) (* -1 (cnt 1))) -1)`), one
premise each, which the existing path proves as the implication by
`omega`; the legacy test now expects the hint.

**Balanced `Inputs` and normalized rewrites over opaque terms
(2026-10-22).** An end-to-end pass over z3test's `smtlib-sample`
QF_LIA and QF_UFLIA files found two reconstructor limits on inputs Z3
solves in seconds. (1) The outlined proof hands every chunk lemma the
assertions as one conjunction, `Inputs`, and projects assertion k by
field notation; right-nested, assertion k sat under k projections, and
on `20220307-SMPT/BART-PT-002/RF-00.smt2` (1,211 assertions) and
`BART-PT-005/RC-11.smt2` elaborating the chain exhausted `maxHeartbeats`
(a 601-assertion disjunction reproduces it). `Inputs` and its
`And.intro` term are now balanced trees (`_balanced`,
`_balanced_select`), so no assertion is more than log2(count)
projections deep; RF-00 verifies in 7 s of Lean, RC-11 in 33 s. (2) A
theory rewrite over more than 16 arithmetic atoms is proved atom by atom
and then propositionally over the atoms' names (`_normalized_rewrite`)
only when its linear forms range over variables; `mathsat/Wisa/
xs-05-11-2-5-3-2.smt2` rewrites an `Iff` between two disjunctions of 20
Int equalities over applications of uninterpreted functions, differing in
flattening, order, and orientation, and `grind` on the whole equivalence
split exponentially. The linear forms may now also range over opaque
terms without a formula inside (applications, `div`, `mod`), keyed by
node, provided every atom whose canonical key occurs on one side of the
rewrite only ranges over variables alone (`_normalizable_rewrite`,
`_normalized_atom`). An atom over an opaque term that disappears from
one side means Z3's rewriter reasoned about the term, which the
propositional lemma over abstract atoms cannot: it decides
`(< (mod x 10) 0)` from the bounds of `mod`, and it simplifies inside a
function's arguments, so that the atoms differ by more than their linear
form; such a rewrite goes to `grind` as before. The Boolean structure
above the atoms must consist of connectives and Boolean variables alone,
which the propositional lemma can bind; an `ite` term (the logged form
of `abs`) stays excluded and keeps the iter-030 bridging. The Wisa file
verifies in 5 s. Nothing is trusted: every atom equivalence is a
`grind`-proved `have`, and the propositional lemma is checked by Lean.
Tests: `test_proof_to_lean.py` (`_balanced_select` follows `_balanced`
within its height for every count up to 69), `test_proof_to_lean_wide.py`
(the 601-assertion disjunction outlined, every assertion at most ten
projections deep), `test_proof_to_lean_lia.py` and
`test_proof_to_lean_uflia.py` (wide rewrites over `mod` and over
applications through the normalized path; a wide rewrite deciding a
`mod`-bound atom and a rewrite inside an application's argument stay
with `grind`, all through Lean).

**Normalized rewrites proved by propagation; let-named structures
(2026-10-27).** z3test's `smtlib-sample` QF_LRA
`clock_synchro/clocksynchro_3clocks.main_invar.base.smt2` (the last QF_LRA
Lean failure of the iter-032 scan) failed on one lemma: the propositional
part of a normalized rewrite relating a 74-way left-nested disjunction over
85 atoms (three symmetric groups of conjunctions sharing atoms, 15 copies of
one literal, three conjuncts false by a constant atom, a re-nested
conjunction) to Z3's flattened 48-way form. The projection-only search
(`_propositional_implication`) found no term, since it knew nothing of the
constant atoms, and `grind (splits := 64)` failed on the whole equivalence.
`_normalized_rewrite` now builds the two sides as `_boolean_structure`
structures (a leaf per normalized atom name, a constant for a constant atom)
and proves the lemma with `_PropositionalProver` in classical mode, `grind`
staying as the `first` fallback; `_propositional_implication` is gone. Two
changes to the prover made that term fit: (1) it names every and, or, implies
and iff structure by a `let` inside the term (`_bind`, children first) and
states propositions over the names, with the steps through conjunctions and
disjunctions written so that Lean infers their types (projections,
`And.intro`, `mt` over `And.left`/`And.right`/`Or.inl`/`Or.inr` with the
other operand named, `not_or.mpr`, `Or.elim` over the disjunction's proof),
where a `have` stating its proposition at every level was quadratic in a
nested gate and exhausted the character budget after a thousand steps; (2)
before splitting on an atom it does case analysis on a true disjunction with
two or more undetermined disjuncts (`_case_split`, `Or.elim`), where
splitting on the atoms the 74 disjuncts share branched on every atom before
a case closed and exhausted the step budget. The same term shape serves the
propositional rewrites and the cnf bridges: the parity rewrite over eight
atoms is a 380 KB direct term Lean checks in 3 s (it rendered ten megabytes
and fell back to the truth table), and the clocksynchro cnf lemmas shrink
from 4.8 MB to 2.2 MB. Nothing is trusted: the term is checked by Lean, and
the fallbacks (grind, the truth table) are unchanged. The clocksynchro file
verifies in 23 s of Lean (was `grind` failed after 97 s); a generated input
with its exact Boolean skeleton over fresh bounds fails under the previous
reconstructor and verifies in 9 s now. Tests: `test_proof_to_lean_arith.py`
(`flattening_rewrite_instance`: the direct term with `(Not True)` and the
forced grind fallback, both through Lean; `clock_shaped_rewrite_instance`
through Lean), `test_proof_to_lean.py` (let-named classical prover,
disjunction cases without excluded middle, atom splits where no disjunction
is assumed, parity thresholds), `test_proof_to_lean_uflia.py` (cnf lemma
shape).

**Propagation proofs as tactic scripts over named gates (2026-10-27).**
The iter-032 scan's one QF_IDL Lean failure, z3test's `smtlib-sample`
`Averest/buble_sort/BubbleSort_safe_bgmc007.smt2` (one assertion, a
13,000-node bounded model checking circuit of and, or, not and iff over
Boolean variables with a few difference bounds; 890 steps, one `cnf` lemma),
exhausted its heartbeats three times over. The lemma's head unfolded the
13,000 definitions outside the leaves (`unfold` rewrites the whole goal once
per name: quadratic, the "timeout at `transform`"); without the unfold, the
1.6 MB propagation term of 9,500 `have` steps under 11,000 `let` names timed
out at `whnf` after 400 s, because Lean elaborates a term of nested binders
in time quadratic in their number (every binder abstracts the rest of the
term: a synthetic chain of 1,000 type-free `have`s took nine minutes as one
term and five seconds as tactic lines); and the export itself spent 134 s in
`_Normalizer._compute_key`, sorting nested keys by `repr`. Three changes,
none touching the trust boundary: (1) `_PropositionalProver` emits a tactic
script (`have` lines, `refine` over `Or.elim`/`Iff.intro` with one hole per
case and a bullet each, `exact`; `equivalence`, `implication` and
`refutation` return lines), (2) the cnf lemmas and the propositional rewrites
name the gates by the nodes' own definitions (`names=_structure_names`), so
the proof binds no `let` and the lemma unfolds nothing before the attempt
(Lean unfolds a definition when a step unifies with it, one level per step),
and the steps through conjunctions and disjunctions leave their operands to
unification (`mt (@And.left _ _)`, `Or.inr`, ...) under a `have` typed by
the gate's name, where writing the operands out was O(n) characters per step
through an n-ary gate; the normalized rewrites keep tactic `let`s for their
structures over the abstracted atoms, (3) the replay's assumption keys are
interned forms over child keys (`_Normalizer.ids`/`forms`), linear in the
DAG. The BubbleSort file now exports in 10 s and verifies in about a minute
of Lean (standard axioms); the lemma is a 1.1 MB script of 9,841 steps.
Tests: `test_proof_to_lean_lia.py`
(`test_bounded_model_checking_circuit_verifies_through_one_cnf_lemma`, the
file itself under `examples/python/data`, through Lean),
`test_proof_certificate.py` (interned keys), and the shape tests of
`test_proof_to_lean.py`, `test_proof_to_lean_uf.py`,
`test_proof_to_lean_uflia.py`, `test_proof_to_lean_arith.py` updated to the
script form. Still open: a tactic `let` per structure is itself about 3 ms
in a chain of thousands (8,000 lets and 8,000 steps: 25 s against 9.5 s
without the lets), so a normalized rewrite over thousands of gates would
want definitions too; and the `unfold` of the grind fallback is still one
pass per name (`delta` is one pass for all, tested on the same file).

**Legacy `(_ th-lemma arith unsupported)` over Int (2026-10-21).**
`theory_lra::set_proof_params` labels an LP conflict `unsupported` instead
of `farkas` with coefficients when its own `check_farkas_conflict` fails or
the explanation does not linearize, which is what a lattice conflict (no
integer point on a rationally feasible region) looks like from inside the
solver; the iter-027 stress run found five Int instances rejected for it
("th-lemma without a replayable theory hint: arith unsupported"), and about
one in seventy small random QF_LIA instances carries the label. The step
lists the held literals and concludes `false`, the shape of the
coefficient-free Int `farkas` the exporter already produces when it strips
coefficients that do not re-derive, so `_th_lemma_parameters` now maps the
label to that step over Int (it must list at least one premise and conclude
`false`; otherwise rejected). Nothing is trusted: the reconstructor's shape
check and Lean's `first | omega | grind` prove the refutation as before, and
a tampered variant with unit coefficients is rejected before Lean ("do not
refute"). Over Real the label stays rejected (a Real Farkas step Z3 could
not check is suspect), as does `unsupported nla`. All five stress inputs now
verify through the legacy core, including the `div`/`mod` one whose
clause-log certificate still hits `maxHeartbeats` (BACKLOG). Tests:
`test_proof_certificate.py`
(`test_legacy_unsupported_conflicts_are_left_to_lean_over_int`: parameter
mapping and rejections, the live label on `_LIA_LATTICE`),
`test_proof_to_lean_lia.py` (documented inputs `lia_lattice_conflict` and
`lia_lattice_bounds` through both cores,
`test_legacy_unsupported_label_is_a_coefficient_free_farkas`).

## Boolean and EUF proof infrastructure

### Assumption search skips conjuncts a model refutes (2026-11-11)

`assume` ties an assumed clause no key matches to the first candidate
conjunct (sharing a symbol with it) that implies it, one bounded solver
check per candidate, and falls back to an unsat core of the assertions
when none does. On QF_IDL `qlock-4-10-8` (one assertion of a thousand
nested ands, 196 assumed clauses) a clause took up to 680 checks, ten
clauses needed the fallback after all of them, and the replay took 259 s
(the iter-096 scan stopped it at 120 s). A model of a conjunct and
the clause's negation now refutes that conjunct and every conjunct below
it (`_refute_conjuncts`), so those are skipped; the model comes from a
failed implication check, or from a failed equivalence check whose model
makes the clause false. The order of the checks, so the source chosen, is
unchanged: the certificates of the large data inputs and of qlock-4-10-8
are identical, and qlock-4-10-8 exports in 141 s with 8,251 checks. Lean
still fails on it (38 MB; a theory lemma's `first | omega | grind` times
out at `whnf`, then the 8 GB cap). Trying the equivalence candidates first
for the implication too took the export to 28 s, but it picks deeper
conjuncts as sources, and on tta_startup 11 nodes the propositional search
then fails over the smaller cnf lemma (Lean would fall back to grind,
which fails); not done. Test:
`test_implication_search_skips_conjuncts_a_model_refutes`
(`test_proof_certificate.py`), which also pins that a model of a failed
equivalence check refutes and an undecided check refutes nothing.

### Theory clauses over uninterpreted functions and sorts (2026-11-11)

The oracle of `_theory_clauses` (see "Theory clauses for cnf lemmas over
rewritten ites") read only arithmetic and Boolean nodes, so a leaf that is
an application or a term of an uninterpreted sort was free in it. A cnf
lemma whose clause Z3 logged over the rewriter's form of applications
(`(ite c (f 0) (f 0))` as `(f 0)`, `(+ 0 (f z))` as `(f z)`) or that rests
on congruence (`(= (f a) e)` makes `(ite (= (f a) e) (f e) ...)` equal
`(f e)`) ended in a model of the leaves and kept the unfolded fallback
alone. `_theory_expression` now declares each uninterpreted function,
predicate, and constant of an uninterpreted sort in the oracle's context
(`_theory_function`; terms over an array sort and datatype constructors
stay free), and the clauses it finds are proved like the others by the
theory tactic over the unfolded definitions, under `first` with the
fallback. Nothing new is trusted. The alldiff clauses Z3 simplifies under
a unit (`uf_ite_alldiff`, the value of an ite of the sort under the
distinct) and the cnf lemmas of the predicate cast chains
(`cast_chains_instance(8, "predicate")`) now have structural proofs that
check with the fallback removed. In the z3test smtlib-sample QF_UFLIA
`wisas` files `xs_5_5`, `xs_6_11`, and `xs_8_18`, one cnf lemma each
took the fallback alone before and now has a structural proof through one
such clause (`xs_8_18` checks with that lemma's fallback removed); the
fallback proved them too, so no file changes status. Tests:
`test_cnf_lemmas_over_applications_are_refuted_with_theory_clauses`
(QF_UF, QF_UFLRA, QF_UFLIA inputs, checked with the fallback removed; with
`_theory_function` disabled the lemmas are the fallback alone) and
`test_theory_expressions_declare_uninterpreted_symbols`
(`test_proof_to_lean_uflra.py`).

### Link allowance of normalized rewrites (2026-11-11)

QF_LRA `tta_startup/simple_startup_15nodes` (z3test smtlib-sample) failed
in `normalized_rewrite_15304`, the propositional lemma relating the
assertion's left-nested binary conjunctions and disjunctions over 480
normalized atoms to the rewriter's flattened form; `grind (splits := 64)`
fails on it. The prover links the two sides' structures equal up to
flattening before searching (`_equivalent_structures`), and its 481 links
took 22,000 steps and 960,000 characters (46 and 2,000 each, mostly
projections and re-associations), more than the whole budget
(`_STRUCTURAL_REWRITE_STEPS`, `_STRUCTURAL_REWRITE_CHARS`): the search over
the sides gave up at once. Each link now has an allowance of its own
(`_LINK_STEPS`, `_LINK_CHARS`, 100 and 5,000) on top of the budget, which
the search does not inherit, so the budget grows linearly with the
structures the rewrite relates and the search keeps all of it. The
allowance is capped at the budget itself, so a rewrite's proof is at most
twice the old limits: uncapped, the same shape at 30 nodes (931 links)
became a 1.8 MB structural lemma Lean checked in 116 s instead of grind's
25 s, and at 40 nodes Lean ran out of memory where grind alone verifies;
capped, both are grind alone again, byte for byte the earlier certificates.
tta15's links take 22,000 steps and 960,000 characters, within the capped
allowance of 20,000 and 1,000,000 but for 2,000 steps the search can
spare. The rewrite
is proved in 1,000 search steps after the links, and the whole 5.2 MB file
verifies in 42 s at a 2.9 GB peak. Nothing new is trusted: links and
search are `have` steps Lean checks, with grind still the `first`
fallback. Test: `test_links_do_not_use_up_the_search_budget`
(`test_proof_to_lean_arith.py`, `startup_shaped_rewrite_instance`: 6 nodes,
43 links, the step limit scaled down to 1,000, checked with the fallback
removed; without the allowance the lemma is grind alone) and
`test_link_allowance_is_capped_at_the_budget` (30 nodes, grind alone).

### Theory clauses for cnf lemmas over rewritten ites (2026-11-11)

QF_LRA `tta_startup/simple_startup_11nodes` (z3test smtlib-sample) failed
in every scan since 2026-10-29 in its one cnf lemma: Z3 logs a clause over
the rewriter's form of the assertion's Real ites (an 11-way conjunction
condition flattened, `(+ 0 x)` as `x`, `(ite c 0 0)` as `0`) and of modular
counters (`(= 10 x)` makes `(ite (= x 11) 1 (+ x 1))` equal 11), so the
clause does not follow from the Boolean structure with every theory atom a
leaf and the one-constraint bridges (`_leaf_bridges`); the propositional
search ended in a model, and the unfolded grind fallback (227 ites) ran out
of heartbeats. When both searches of `_cnf_lemma` fail now,
`_theory_clauses` finds the missing theory facts as a lazy SMT solver
does: z3 (an untrusted oracle, as for `_relevant_structures`) takes a model
of the abstraction, checks the leaves' and atoms' values in it against
what the leaves denote (`_theory_expression`, arithmetic and Boolean nodes
only; uninterpreted ones since the same day, see "Theory clauses over
uninterpreted functions and sorts"), and a shrunk unsat core of those
literals is a clause excluding the model, until the abstraction is
unsatisfiable (at most 256 clauses). A clause over every leaf of the lemma would restate it as one theory fact,
without the fallback's helpers (scaled ite gates), so then the search
stops and the fallback stays alone, as before. Each
clause is a `have` the theory tactic proves over the leaves' unfolded
definitions and a fact for one more search, with ten times the prover's
limits (`_THEORY_CLAUSE_BUDGET`; the fallback stays under `first`), while
the proof kept stays within `_STRUCTURAL_REWRITE_CHARS` as before. Lean
checks every clause and step, so a wrong clause is a rejection. A clause
that does not hold is an elaboration error, which `first` catches; a
theory tactic that runs out of heartbeats is not caught and fails the
whole lemma, so the size bound and the every-leaf rule are heuristics
against that, not a guarantee (no input of the z3test smtlib-sample sweep
hit it). The 11-node
input takes 45 clauses (1.4 s), the search 36,000 steps and keeps a
0.45 MB proof, and the whole file verifies in 24 s at a 2.6 GB peak. The
15-node input's cnf lemma now checks too; the file then failed in a
propositional normalized rewrite that grind cannot prove (verified since
the same day, see "Link allowance of normalized rewrites"). Tests:
`test_cnf_lemmas_over_rewritten_ites_are_refuted_with_theory_clauses`
(two small inputs, checked with the fallback removed),
`test_theory_clause_search_stops_at_a_model_the_leaves_allow`, and the slow
`test_time_triggered_startup_verifies_through_theory_clauses`
(`test_proof_to_lean_arith.py`, data
`QF_LRA_tta_startup_simple_startup_11nodes.smt2`).

### Resolution types inferred; re-applications applied in place (2026-11-10)

Two parts of the outlined lemmas' text restated what Lean already knows. In
the 26.1 MB of Lean of QF_IDL `DTP_k2_n35_c245_s9` (which verified at
7.86 GB of the 8 GB cap), 46,002 of the 49,550 steps bound inside other steps
were unit resolutions keeping one literal, the clause's proof cut down by
`Or.resolve_*` and `Or.neg_resolve_*`, whose type those lemmas infer from the
clause's; their lets stated it again (`let _step_N : (formula_M _atoms
_vars) :=`). Such a let now states no type (`_INFERRED_TYPE`); every other
term (an injection into a wider conclusion, a case split, a proof by
contradiction) keeps it. 49,236 lets bound a step's or an imported lemma's
application to its hypotheses (`let _step_N := proof_step_N _inputs
_hyp...`) for one use in the term on the next line; that use is now the
application (`_reapplications_in_place`). Lean checks every term as before,
so a wrongly inferred type is a rejection, not a gap. DTP goes from 26.1 to
23.2 MB and verifies in 114 s at a 7.45 GB peak; plan-21 from 21.4 to
20.4 MB (78 s, 6.47 GB; 6.60 GB before), NEQ004 from 11.1 to 10.1 MB,
`swap_t2_np_sf_ai_00009_002` from 16.0 to 15.2 MB (104 s, 7.27 GB; 7.39 GB
before). Tests:
`test_resolution_types_are_inferred_and_reapplications_applied_in_place`,
`test_reapplications_used_once_are_applied_in_place`
(`test_proof_to_lean_lia.py`). A rescan of the earlier QF_AX/QF_AUFLIA
memory failures: `storecomm_t2_np_nf_ai_00050_007` (14.3 MB) verifies in
129 s at 7.64 GB, as it already did before this change;
`swap_t1_pp_sf_ai_00010_008` (35.7 MB) still fails at the cap, after 1,928
of its 12,176 declarations, in its theory lemmas rather than its proof
steps.

### Single imports, negated eliminations, and classical contradictions in place (2026-11-10)

Three parts of the outlined lemmas' text bound or wrapped what one
application states. In DTP's 32.2 MB of Lean, 70,817 eliminations of a
literal `(not p)` by a proof of p were `.resolve_left (fun _literal =>
_literal _step_N)` (2.6 MB); they are now `Or.neg_resolve_left` and
`Or.neg_resolve_right` on the proof itself (Lean core, no axioms). 92,491 of
its 100,549 imported lemmas were used once in the lemma importing them;
such a lemma is now applied at that use, by name or in the line that
re-applies it to its hypotheses (`_merge_single_imports`). 15,068 proofs by
contradiction named their formula and a witness `let _dfN :=
Classical.propDecidable ...` (1.9 MB); classical lemmas now use one helper,
`classical_by_contradiction`, which is `Decidable.byContradiction` at
`Classical.propDecidable` (the same axiom as before;
`Classical.byContradiction` would add `propext` and `Quot.sound`) and takes the
formula from the expected type. QF_IDL `DTP_k2_n35_c245_s9` goes from 32.2
to 26.1 MB and verifies for the first time, in 117 s at a 7.86 GB peak;
`swap_t2_np_sf_ai_00009_002` (QF_AX) from 20.6 to 16.0 MB and verifies
(105 s, 7.39 GB); plan-21 from 23.4 to 21.4 MB (79 s, 6.60 GB; 87 s and
7.0 GB before); NEQ004 from 13.9 to 11.1 MB. Tests:
`test_single_imports_and_negated_eliminations_are_applied_in_place`, slow
`test_disjunctive_temporal_refutation_verifies_under_the_memory_cap`
(`test_proof_to_lean_lia.py`). Still open: DTP is close to the cap; its
largest remaining parts are the nested step headers (`let _step_N :
(formula_M _atoms _vars) :=`, 2.6 MB) and the lemma statements'
hypothesis chains.

### Hypotheses named by their binders; resolutions closed on the right (2026-11-10)

A `hypothesis` step was bound like any other step: a function of its own
binder `_hypN`, re-applied by each user, and, used by several steps, an
outlined lemma `fun _hypN => _hypN` imported by every lemma using it. In
DTP's 36.9 MB of Lean that was 3.3 MB. Its users now name the binder
itself, which is in scope wherever the step's hypotheses are
(`_direct_hypotheses`); only the premise of a `lemma`, which discharges the
binder, keeps its step. A unit resolution whose literals after the last
kept one are all eliminated is closed by `Or.resolve_right` on that tail
instead of an `Or.elim` case split; in DTP most resolutions keep one literal
of a two-literal clause. DTP goes from 36.9 to 32.2 MB and still fails at
the 8 GB cap, after 13,579 of its 16,557 outlined lemmas (11,991 of 17,084
before); plan-21 from 25.5 to 23.4 MB, NEQ004 from 16.5 to 13.9 MB,
`swap_t2_np_sf_ai_00009_002` from 22.7 to 20.6 MB. plan-21 verifies in 87 s
at a 7.0 GB peak (7.5 GB before); the swap file still fails at the cap.
Still open: imports of shared steps under hypotheses, each followed by its
re-application (about 1 MB of DTP), and the lemma statements' hypothesis
chains.

### Steps under hypotheses bound inside the step using them (2026-11-10)

A proof step under hypotheses (the clause log's lemmas and the legacy
core's `hypothesis` steps) was a let-bound function of them: its binders
restated every hypothesis formula, and each step using it re-applied it to
them. Outlined lemmas restated their own statement the same way and passed
the interpretation to every lemma they imported. In the 58 MB of Lean of
QF_IDL `DTP_k2_n35_c245_s9` this was 28 MB of the 54 MB of proof steps.
Lean's memory grows with the elaborated text, about 160 bytes per
character there (4,000 trivial theorems of the same signature cost only
0.2 GB), so plan-21 and DTP ran out of the 8 GB cap. Now (`_step_blocks`,
`_outline_steps`):

- a step under hypotheses that one other step uses is bound inside it,
  where its hypotheses are in scope, at most 32 such steps deep;
- an outlined lemma's own step is its statement: its hypotheses are the
  binders of a `fun`;
- the interpretation is implicit in outlined lemmas, determined by the type
  of `_inputs`, and the classical witnesses' types are inferred.

plan-21 goes from 33.2 to 25.5 MB and verifies in 92 s at a 7.5 GB peak
(it failed at 95 s before). DTP goes from 58.4 to 36.9 MB and still fails,
after 11,991 of its 17,084 outlined lemmas (7,921 before); NEQ004 goes from
21.6 to 16.5 MB, the QF_AX swap file `swap_t2_np_sf_ai_00009_002` from 27.1
to 22.7 MB (still failing). Still open: the shared steps (each its own
lemma, imported and re-applied by every user) and the `Or.elim` resolution
terms are most of what remains in DTP.

### euf lemmas without ite gates and array axiom instances (2026-11-10)

Every theory lemma proved by `_grind_lemma` got the gates of every
arithmetic ite it reaches and, with arrays, the instances of the array
axioms for every read it reaches. `euf` lemmas need neither. Z3's egraph
internalizes an ite term as a leaf without arguments
(`euf::solver::internalize`), and the ite's gates are tseitin clauses of
their own. The egraph applies no array axiom either: those are `array`
lemmas, and a theory's equality enters an `euf` hint as a literal. The C++
checker (`eq_theory_checker`) accepts an `euf` hint by union-find and
congruence alone. So an `euf` lemma now states only the bodies of the
folded array terms (`_t`), the map identities (`_map_identities`, with
`_mc` among them), and the commutativity of extensionality witnesses
(`_xc`), which its `comm` claims may use. Its tactic is
grind alone: omega, tried first over Int, ran out of heartbeats on several
dlx-regfile `euf` lemmas, and `first` does not catch that. A lemma that
reaches ites is first tried with them folded, unfolding only the
definitions outside them. The unfolded proof stays as the fallback, for
facts written out after the unfold that inline an ite. The other theory
lemmas are unchanged. Dropping hypotheses cannot make Lean accept more,
and a lemma that needed one fails.

| Input | Before | Now |
| --- | --- | --- |
| `register_file_instance(8)` (QF_AUFLIA shape, `qf_uflia`) | 6.0 MB, 136 s, 3.9 GB | 5.1 MB, 20 s, 1.8 GB |
| dlx-regfile, file without the proof steps | about 30 MB, not checked; without gates and read facts but unfolded with omega: 7.7 MB, 1,372 s, 10 GB, 101 error lines (heartbeats) | 8.0 MB, 255 s, 5.2 GB, one `cnf` lemma out of heartbeats |
| QF_UFLIA `EufLaArithmetic/hard16` | 12 MB, 76 s, 4.5 GB (2026-11-08) | 11.4 MB, 55 s, 3.9 GB |

Still open: dlx-regfile still does not verify. Its one `cnf` lemma
reaches 227 ites; the propositional prover gives up and the unfolded
grind fallback runs out of heartbeats. Its outlined proof steps are 14 MB
of the 22 MB file.

Tests: `test_congruence_lemmas_state_no_ite_gates_or_array_axioms` (fails
before: 346 of the 348 `euf` lemmas of `register_file_instance(8)` carried
facts) and `test_congruence_lemmas_over_ite_chains_verify`
(`test_proof_to_lean_array.py`).

Update (2026-11-10, later): the unfolded fallback under `first` is dropped
for `euf` lemmas, so the folded proof is their only one. (The attempt
normalized by the rewriter's store identities stays as before, over the
full unfold, since its simp cannot rewrite inside a folded ite; no `euf`
lemma of the documented inputs gets it.) With the
fallback removed, the whole Lean test suite still passed, so no `euf`
lemma in it needed the fallback. The fallback doubled the lemmas' text.
`maxHeartbeats` is per declaration, so a folded attempt that used up the
budget before failing would also have left the fallback none.

| Input | With the fallback | Folded proof only |
| --- | --- | --- |
| `register_file_instance(8)`, file | 5.12 MB, 20 s, 1.83 GB | 4.28 MB, 7 s, 2.52 GB |
| `register_file_instance(8)`, `euf` lemmas | 1.55 MB | 0.71 MB |
| dlx-regfile, file / `euf` lemmas | 22.3 MB / 5.56 MB | 18.6 MB / 1.80 MB |
| dlx-regfile, theory lemmas without the `cnf` one | 206 s, 5.0 GB | 206 s, 4.9 GB |

The dlx-regfile time does not change: Lean parses a fallback that is
never taken but does not elaborate it. The `cnf` lemma `th_lemma_1612`
still fails. Its clause relates the input's disequality (115 ites) to the
form sat.smt's preprocessing rewriter gave it (114 ites). The rewriter
merges nested ite conditions into disjunctions and pushes the `select`
into the ites, so no level-by-level correspondence pairs the two terms.

Update (2026-11-10, iteration 109): `array` th-lemmas keep their ites
folded too. Lean's profiler on dlx-regfile's theory lemmas (without the
`cnf` one) put about 150 of the 208 s in its 50 `array` lemmas: each
carried about 128 ite gates and 37 read facts, unfolded about 60 ites, and
went to `first | omega | grind`. An array lemma is one axiom instance over
the terms of its literals: `array::solver::assert_select_store_axiom`
builds it over the store it is given, and the array solver internalizes
no ite (an ite of arrays meets a store only through the egraph, by the
ite's tseitin gates). So an `array` lemma now gets no ite gates (nor the
Real scaling facts of `_folded_ite_gates`), unfolds only the definitions
outside its ites, and states the array facts of the nodes outside them,
without the rewriter's reads through ites of arrays (`_si`). The one ite
it unfolds is the select-map axiom's own over a map of ite, which equates
the read with the ite of the reads (`_map_read_values`); folded, grind
failed on `map_ite_symbolic`. The tactic is unchanged.

| Input | Before | Now |
| --- | --- | --- |
| dlx-regfile, theory lemmas without the `cnf` one | 208 s, 4.9 GB | 25 s, 2.2 GB |
| dlx-regfile, `array` lemmas / file | 0.90 MB / 18.6 MB | 0.03 MB / 17.7 MB |
| `register_file_instance(8)`, its 8 `array` lemmas | 64 gates, 40 read facts, 23,551 characters | 8 read facts, 3,951 characters |

dlx-regfile still fails on its `cnf` lemma `th_lemma_1612`. Tests:
`test_array_lemmas_keep_their_ites_folded` and
`test_array_lemmas_over_ite_chains_verify` (`test_proof_to_lean_array.py`).

Update (2026-11-10, iteration 110): `euf` lemmas that reach ites state
only the facts of the nodes outside them, as `array` lemmas do: the `_t`
body of a store, the excluded middle of a Boolean argument, a cast or
distinct fact about a term that only a folded ite reaches cannot meet the
goal. Their tactic and unfold are unchanged.

| Input | Before | Now |
| --- | --- | --- |
| dlx-regfile, `euf` lemmas (`_t` facts) / file | 1.75 MB (8,139) / 17.7 MB | 0.72 MB (1,122) / 16.7 MB |
| dlx-regfile, theory lemmas without the `cnf` one | 27 s, 2.23 GB | 19 s, 1.58 GB |
| `register_file_instance(8)`, `euf` lemmas (`_t` facts) | 0.69 MB (3,592) | 0.45 MB (1,817) |

Test: `test_congruence_lemmas_state_no_ite_gates_or_array_axioms` (fails
before: `_t` facts of stores only ites reach).

### Array facts stated over folded definitions (2026-11-10)

A rescan of z3test's `smtlib-sample` QF_AUFLIA files found that
`cvc/dlx-regfile` (z3 answers unsat in 0.04 s, export 7 s) never finished
reconstructing: after five minutes the reconstructor was still rendering
the facts of nine theory lemmas. The register file is read through shared
nested ites, and the array facts of `_array_helpers` (`_t` store bodies,
`_s` reads of stores, `_x`, `_d`, map facts) and, with arrays, the ite
gates were written out, with every definition expanded down to the
leaves. Text for a shared ite DAG grows exponentially with its depth.

Now the array facts name the definitions of the nodes they mention
(`_store_apply ((term_a ..)) (term_i ..) (term_v ..) (_vars 3)`), and the
ite gates and scaling facts of `_folded_ite_gates` are stated folded with
arrays too. `_grind_lemma` reverts them before its fallback's `unfold` and
introduces them after it, as it already did without arrays. Array terms,
constants, variables, and numerals are written as before. A node's facts
that mention nothing else are stated after the unfold as before, not
reverted. Reverting them anyway (the many facts of storecomm's stores
over variables) took Lean from 118 s and 5.6 GB to 155 s and 7.9 GB on
`storecomm_t3_pp_sf_ai_00060_005`. The unfold does not enter array terms
(`_definition_names`), and an index or a stored value may occur in the
goal only inside a folded store, so the nodes the facts mention are also
roots of that unfold. Without those roots, grind fails on the lemmas.

| Input | Before | Now |
| --- | --- | --- |
| `array_chain_instance(6)` (QF_ALIA) | 6.7 MB, 78 s, 3.9 GB | 0.36 MB, 3 s, 0.8 GB |
| `array_chain_instance(8)` | 57 MB, not checked | 0.74 MB, 17 s, 1.4 GB |
| `array_chain_instance(8, "index")` | 55 MB, not checked | 0.84 MB, 6 s, 1.7 GB |
| `array_chain_instance(8, "real")` (QF_AUFLIRA) | 57 MB, not checked | 0.81 MB, 4 s, 0.9 GB |
| dlx-regfile | no output after 5 min | 6.5 s, 44 MB of Lean (Lean: see below) |

The storecomm, storeinv, and swap files have shallow terms. Their text is
byte-identical or up to 3% smaller. Every array-free certificate of the
documented test inputs is byte-identical, and so are 124 of the 198 with
arrays. `_scaling_helpers` and `_ite_gate_helpers`, the
written-out forms, are no longer reachable and are removed.

Still open: dlx-regfile does not verify yet. Its 44 MB file reached 12 GB
in Lean and was stopped after 20 minutes. Of its 854 theory lemmas, 803
are `euf` lemmas, each reaching about 66 ites, and every reachable ite
gets two gates. Gates alone are about 80% of a lemma's text, and the
outlined proof steps add another 14 MB. The swap files of 66 to 250 MB
belong to the many-lemma memory class.

Tests: `test_array_facts_are_stated_over_folded_definitions` (fails before
on size and without the unfold roots on the unfold line) and
`test_nested_ite_chains_through_arrays_verify` (`test_proof_to_lean_array.py`).
The tests that drop facts to show they are needed now also drop the
dropped facts' names from the revert and intro lines (`_without_facts`).

### cnf lemmas searched again over an unsat core (2026-11-07)

QF_IDL `planning/plan-21` is one assertion with a disjunction of cases per
time step. One of its 33 cnf lemmas ties a clause Z3 derived from one step
to the assertion. `_PropositionalProver` split the true disjunction with
the fewest open disjuncts, earliest first, so it went through the cases of
about fifty earlier steps (about 150 propagation steps each) and ran out of
its budget (also at 20 times the budget). The unfolded fallback then failed
in Lean (`grind`: `simp` step limit).

When the search of a cnf lemma gives up, `_cnf_lemma` now asks z3 for an
unsat core of the propositional abstraction: every gate's definition under
a guard of its own (`_relevant_structures`). z3 is an untrusted oracle
here, and Lean checks the proof as before. The search is then repeated over
the gates in the core. Only those propagate and are split, and the gates
outside the core that feed them are split like atoms. On plan-21 the core
has 360 of 5,649 gates (0.24 s of z3, 0.4 million rlimit; minimizing the
core gave the same 360 at a hundred times the cost), and the lemma is proved
with two case splits and 18 KB of proof.

plan-21 as a whole still fails: its 33 MB Lean file peaks at 8.6 GB and
hits kernel memory errors in outlined proof steps (verifies since
2026-11-10, see "Steps under hypotheses bound inside the step using
them"). RTCL `tf_20`/`tf_30`
are unchanged: their cores have about 3,000 gates, and the search over
them still runs out of budget. That retry is not free: on `tf_20` the core
(3,123 of 12,943 gates, 0.6 s) and the second search raise reconstruction
from 0.7 s to 5.4 s for identical output. The cores that help are smaller
(plan-21 6%, the FISCHER6-4 lemmas under a 25,000-character budget 7%,
against 24% for `tf_20`), but three inputs are too few to pick a core-size
cutoff, so bounding the second search is left open.

### Propositional proofs keep the steps they use and drop unused splits (2026-11-07)

A first Lean status of z3test's `smtlib-sample` QF_IDL files (the files of
at most 160 KB) found 6 of 17 verified and 5 failing in Lean on
heartbeats or memory (`DTP_k2_n35`, `plan-21`, and three RTCL circuits).
The other 6 exceed Z3's 20 s limit (4) or the replay's 120 s limit (2,
`qlock`). The three RTCL
`ckt_PROP*_tf_*` circuits failed the same way. A cnf lemma ties a clause
Z3 derived from an ite chain (9, 19, or 30 cases) to the one assertion. The
search of `_PropositionalProver` gave up on it, and the unfolded fallback
ran out of heartbeats. The search split atoms in order of how many gates
read them, and on `tf_10` it went 31 atoms deep. It exhausted its
character budget on splits whose two branches both closed by facts found
before the split. `_prove` now tracks which `have` names each proof uses
(`_needed_lines`). A branch whose proof does not use its hypothesis proves
the goal before the split, so the split and its other branches are dropped
(backjumping). Every proof also keeps only the steps it uses.

Results:

- `tf_10` (now `examples/python/data/QF_IDL_ckt_PROP1_tf_10.smt2`) verifies
  in 3 s at 1 GB.
- BubbleSort's cnf proof shrinks from about ten thousand steps to 853, and
  the file checks in 9 s at 1.8 GB (about a minute at 4.5 GB before).

Still open: `tf_20` and `tf_30` keep the fallback. Their search explodes
even with 100 times the budget. Restricting the search to the gates of a
z3 unsat core (about 2,600 of 13,000) did not help, nor did other split
orders. The search seems to need clause learning or proof guidance from
a SAT solver's refutation.

### Distincts over the same terms in other orders (2026-11-07)

`(distinct c0 ... c11)` with `(not (distinct c11 ... c0))` over Int exported
but failed Lean: Z3's rewriter sorts a distinct's arguments, so the two
assertions simplify to false before the log, and the exporter's cnf lemma
tying them had the two distincts as unrelated opaque leaves (the second has
no pair node of its order), so it went to omega over the unfolded pairs and
ran out of heartbeats from twelve arguments (33 arguments, iter-090's
repro, likewise). A distinct now becomes its pairs also when a pair is
logged the other way round or another distinct ranges over the same terms
(`_distinct_pair_leaves`, `distinct_term_sets`), and a synthetic pair leaf
`(a = b)` is bridged by `eq_comm` to the node `(= b a)` or the synthetic
leaf `(b, a)` of the other distinct (`_leaf_bridges`), so the propagation
proof covers it. Twelve and 33 Int terms, and 33 over U, check in 2 to 4 s
with the fallback dropped (`test_reordered_distincts_verify_by_propagation`
in `test_proof_to_lean_lia.py`,
`test_reordered_distincts_verify_by_propagation_alone` in
`test_proof_to_lean_uf.py`).
The cost grows faster than the bridges: 60 reversed Int terms (1770
bridges) took about 32 s with or without the fallback, so a reordered
distinct of about a hundred terms may reach the heartbeat limit; no size
cap guards it. The criterion is global to the certificate (a distinct
expands in every cnf lemma once another distinct over its terms exists
anywhere), as the pair-node criterion is; a per-clause criterion would
spare the prover the unbridged pairs.

### Negated distincts whose every pair is refuted (2026-11-07)

A negated distinct of 30 or 40 Int terms pinned to distinct values (435 or
780 pairs, each refuted by the proof) exported but failed Lean on three
counts. The rewrite of `(not (distinct ...))` into the disjunction of its
pairs went to grind over the unfolded sides and ran out of heartbeats; it
is now proved by one De Morgan step per pair
(`_negated_distinct_rewrite`: `Classical.not_and_iff_not_or_not`,
`Classical.not_not`, `eq_comm` for a pair written the other way round),
any other shape still goes to grind. The `lemma` steps discharging the
pairs' hypotheses projected each literal from the negated clause with its
own `Or.inr` chain, quadratic in the clause width (a 2.7 MB line); over a
clause wider than 32 literals they now start from tails of the negated
clause let-bound every 32 literals. And a step with hundreds of premises or
clause literals elaborated about ten times slower inside a 500-step outlined
chunk than alone, so outlining counts a step wider than 64 by its width
(`_outline_weight`). The 40-term input now checks in about 8 s
(`test_negated_wide_distincts_verify`, `test_proof_to_lean_lia.py`). Z3's
rewriter writes every pair `(= ai aj)`, so the `eq_comm` congruence is
checked on a certificate with reversed pairs
(`test_negated_distinct_rewrites_of_reversed_pairs_verify`); a
33-term strict order chain checks in 90 s, and 34 terms over U with distinct
f-images in 150 s (12.8 MB of Lean, mostly many small lemmas), neither in
CI.

### Distincts of more than 32 terms (2026-11-07)

Every input with a root `distinct` of more than 32 arguments, in any
fragment, failed to export through the clause log: the sat.smt core
encoded it over a fresh sort and function (`distinct-elems`, `dist-f`, and
an at-least-2 constraint for a negated one), which the replay rejects ("the
clause log declares a sort absent from the input"). With proofs
(`use_drat()`) `add_distinct_axiom` and `add_not_distinct_axiom` in
`src/sat/smt/euf_internalize.cpp` now log the pairwise clauses at any width,
as they did up to 32 arguments; without proofs nothing changes. Second, the
certificate keeps only the pair equalities the proof uses, and a distinct
with any pair missing was one opaque leaf in the cnf lemmas tying a logged
`(not (= a b))` to it, so those lemmas fell back to omega and grind over the
unfolded distinct, which ran out of heartbeats over Int from 30 arguments
(435 pairs). A missing pair is now a synthetic leaf rendered as the
distinct's conjunct (`_distinct_pair_leaves`), and the propagation proof
projects the logged pairs. Wide distincts over U and Int verify in about a
second. Tests: `test_wide_distincts_are_clausified_pairwise_under_proofs`
(`test_proof_certificate.py`), `test_cnf_lemmas_project_the_logged_pairs_of_a_wide_distinct`
and `test_wide_distincts_verify_through_their_logged_pairs`
(`test_proof_to_lean_lia.py`), `test_distincts_of_more_than_32_terms_verify`
(`test_proof_to_lean_uf.py`). Still open then (done since, see "Negated
distincts whose every pair is refuted"): a negated wide distinct whose
every pair the proof refutes exports, but its Lean text is quadratic (528
pairs under a strict order give 25 MB; the 528-literal clause is projected
by `Or.inr` chains, and over Int the rewrite of the negated distinct into
the disjunction goes to grind). Also open, and older than this change: a
wide distinct with an ite argument whose clauses Z3 simplified under a unit
(34 `f` applications, `(+ x 1)`, and `(ite (> x 0) (f 3) (f 4))` with
`x = 2`) still sends the cnf lemmas over the ite's value to grind over the
unfolded distinct, which runs out of heartbeats from about 30 arguments; the
base reconstructor emits the same text at 30 arguments. Clausifying pairwise
under proofs is quadratic in the width (1000 arguments: about 8 s and 34 MB
of clause log, against 0.02 s without a log); the encoding is not capped,
as the fresh-symbol encoding above the cap could not be certified anyway.

### Arrays of enumerations (2026-11-06)

Every array sort with an enumeration component was rejected ("unsupported
sort"). Arrays whose element sort is an enumeration, `(Array I Color)` over
Int, Real, Bool, uninterpreted, or array index sorts, are now certified
through the clause log: array constants, functions into and over them,
store, ite, select, equality, and extensionality. The datatype solver splits
on reads of such arrays, so Lean must know that every read is a constructor:
the interpretation gains a field per array constant (`enum_acases_i`, over
every index of the Lean index type) and per function into such arrays
(`enum_afcases_j`, over every argument list and index), sound because a
model's arrays embed with a constructor as their value outside the index
sort. A read of a store or of an ite over arrays is a constructor by the
cases of what it may evaluate to; each lemma reaching a read gets that fact
as a proof term built along the read's array (`_cases_store`,
`_cases_ite`, theorems of the prelude, down to the fields), so grind gets
the read's disjunction ready-made. Still rejected, explicitly: arrays
indexed by an enumeration (extensionality would have to range over its
finitely many values, which the Lean function type over `_m.U` does not
have), arrays of an enumeration nested in other arrays, constant arrays,
default values, and maps over them. Random sweeps
(`random_enum_array_instance`, seeds 1-150 over Int and over uninterpreted
indices, 1-100 of `variables=3, constraints=16, depth=3`): 200
unsatisfiable seeds, all verify. They are not complete: in the review's
sweep of `index="U", constraints=14, depth=3`, 4 of 37 unsatisfiable seeds
(200-259: 219, 223, 224, 251) fail Lean with grind errors. The cause
predates this section and affects `(Array Int Int)` alike: `_array_helpers`
states `_store_apply` only for a read whose array is itself a store, so a
read through an ite over a store, `(select (ite p (store a1 k c) a0) k)`,
which Z3's rewriter evaluates to `(ite p c (select a0 k))`, gets no value
(done 2026-11-06: the `_si` facts walk the ite branches, see "Constant
arrays of enumerations, and the rewriter's constant-array evaluations";
seeds 219 and 251 are pinned). The read cases are built on an explicit stack, so a
read through 1,100 nested stores is reconstructed without RecursionError
(`test_proof_to_lean_deep.py`, reconstruction only: its 1,100 enumeration
constants are 1,100 fields, a structure that alone runs out of heartbeats;
the same chain 200 levels deep passes Lean). Tests: `test_proof_to_lean_enum.py` (eight
documented inputs `ENUM_ARRAY_INPUTS`, four pinned seeds, the fields, the
rejections, the replay's constructors of element sorts, and the read cases
failing Lean when dropped).

### Store chains over two constant arrays compared (2026-11-06)

A random QF_ALIA sweep with constant arrays, default values, stores, and ite
of arrays over Int elements (`random_constant_array_instance` in
`test_proof_to_lean_array.py`) found two more of the rewriter's evaluations
Lean could not follow. `array_rewriter::mk_eq_core` decides `(= S T)`, for
store chains S and T over constant arrays `(const v)` and `(const w)` with an
infinite index sort, as the conjunction of `(= (select S i) (select T i))`
over the stored indices i and `(= v w)`, after dropping an ite of an array
with itself. The direction from S = T was already stated (`_e` facts of
`_constant_array_comparisons`); the converse is extensionality, which grind
does not do, and `_const_eq_store` covered only one store over one constant
array. `_constant_chain_extensionality` now states and proves the converse
per such equality (`_x` facts: funext, a case split on the stored indices,
and the new prelude theorem `_store_off` down to the constants). Second,
`(store (const c) i (ite p c c))` folds into `(const c)`: the array rewrite
alternative's simp set has `ite_self`, so simp drops the ite before
`_const_store_self` folds the store (rewrite steps with a store always get
that alternative; on the 528 seeds no other step needed it). Seeds 131, 139, and 246 failed Lean
before and are pinned (`CONSTANT_ARRAY_SEEDS`); 528 unsatisfiable seeds of
four sweep configurations verify, none rejected. Five documented inputs (one
over Real indices) fail Lean with grind errors only without the new facts
(`test_constant_chain_facts_are_needed`).

Long chains (2026-11-06, later). The read facts of
`_constant_array_comparisons` are every store and constant array of the sort
read at every index stored into it, quadratic; above `_COMPARISON_READS` (64)
they were all dropped, so the `_x` facts lost the evaluations of their
premises and two chains of five numeral stores already failed Lean. Above the
cap the facts are now the reads the rewriter evaluates in each comparison of
store chains over constant arrays (`_chain_comparison_reads`): each side read
at the indices stored into either side, down to the outermost store at that
index or to the constant. A random sweep of such comparisons
(`random_chain_comparison_instance`, three chains of 3 to 10 stores over Int
or Real indices) went from 20 of 45 unsat seeds verified to 145 of 145 (seeds
1-300, 91 above the cap, at most 122 targeted reads). Seeds 13 and 14 are
pinned, and the documented input `long_store_chains_over_two_constants` fails
Lean without its read facts. The targeted reads are still quadratic, about
n(n+2) for two n-store chains, and each is repeated in every case of the
rewrite's proof, so they have a cap of their own, `_CHAIN_COMPARISON_READS`
(640), above which no read facts are stated, as before. Two 24-store chains
(624 reads) check in 2.8 s and 1.5 GB; uncapped, 32 stores took 3.5 GB, 40
stores 7.6 GB, and two 64-store chains over `(const 0)` and `(const 1)`, which
checked in 1.2 s without read facts, exceeded the 12 GB watchdog
(`test_chain_comparison_reads_are_bounded`).

Real sorts (2026-11-06, iteration 86). `random_constant_array_instance` now
takes the index and element sorts (Real numerals are integers or halves in
lowest terms). Two gaps showed, neither specific to Real. First, a clause
the exporter ties to the assertions through an unsat core may get a cnf lemma
that reads an array equated to a constant array, with no read of the
constant array: for `(= a (const 1))` and `(distinct 3 (select a k) (select a
0))` the split clause `(not (= 3 (select a k)))` is implied by the equality
alone, so the lemma is `(not (= a (const 1))) \/ (not (= 3 (select a k)))`,
which grind cannot prove from the stored-index reads. Each store and constant
array a side of an array equality reaches now also gets its value at every
index read from the sort (`_compared_side_reads`, within
`_COMPARISON_READS`). Second, Z3's congruence closure takes `(_ array-ext 0)`
as commutative (a `comm` claim of an euf hint merges the witnesses of
`(= a b)` and `(= b a)`); `_array_diff` is an epsilon over a predicate that is
propositionally symmetric, so the new prelude theorem `_array_diff_comm`
proves it and each witness gets it as a fact. Over Real/Real, seeds 1-300
went from 188 to 190 of 190 unsat seeds verified; Int/Real and Real/Int seeds
1-150 verify, except one Real/Int seed rejected ("arithmetic step over both
Int and Real atoms"); Int/Int seeds 1-200 still verify (133 of 133). The
documented inputs `read_of_an_array_equated_to_a_constant` (Int and Real)
and `commuted_extensionality_witnesses` fail Lean without the new facts.
Still open: an index written as an unnormalized numeral expression, `(/ 2 2)`
next to `1.0`, which the rewriter evaluates before applying a store identity
while grind keeps `2 * 2⁻¹` and `1` apart as array indices.
Update (2026-11-07): closed. `_store_identity_instance` compares indices and
values as numeral expressions (`+ - * /` and `to_real` over numerals, no
division by zero), and the store-identity simp alternative first rewrites
each outermost numeral expression to its value with a grind-proved fact
(`_numeral_facts`, pre-order `↓`, so an expression shared with an enclosing
one cannot block it). With `random_constant_array_instance(unnormalized=0.8)`,
671 of 673 unsat seeds verified before and 672 after; six documented inputs
(`NUMERAL_EXPRESSION_INPUTS`) failed before. The remaining seed
compares an ite of store chains with a store chain over constant arrays,
which still fails Lean with plain numerals too.
Update (2026-11-07, iteration 89): closed. The sat.smt core logs an asserted
`(= (ite p S S') T)`, for store chains over constant arrays, as the outcome of
comparing each branch with T (`x0 = x1` for `(= (ite p (store (const x0) k
x1) (const x0)) (store (const x1) 1 x0))`), and the replay ties the two by a
rewrite step. grind splits the ite but `_x` facts existed only for sides that
are chains, so the branch comparisons had no converse. Each pair of a leaf of
one side's ite tree with a different leaf of the other now gets one
(`_ite_chain_extensionality`, over the leaves' terms, at most 16 pairs), and
the reads above the cap walk every leaf (`_chain_comparison_reads`). Seed 102
(Real/Int) now verifies and is pinned; three documented Int inputs (an ite on
one side, on both, nested) failed Lean before and fail with grind errors
without the new facts. The leaf walk visits each ite once (a shared ite DAG
took exponential time otherwise), and an equality above the 16-pair cap gets
no chain-comparison reads, so it cannot push the others over
`_CHAIN_COMPARISON_READS`.

### Constant arrays of enumerations, and the rewriter's constant-array evaluations (2026-11-06)

Constant arrays of an enumeration, `((as const (Array Int Color)) c)` over
Int or Real indices, are certified through the clause log, and so are default
values of arrays built from constant arrays by store and ite. A read of a
constant array is its value (`_cases_const`), the default value of one is
too (`_cases_default_const`), and the default value of a store is that of
the array below (`_cases_default_store`), so `_read_cases` walks on through
them. The default value of an array constant or application is rejected
explicitly by the exporter: `_default` of an array that is not constant
almost everywhere is an arbitrary value of `_m.U`, not provably a
constructor. Random sweeps of `random_enum_array_instance(constant=True)`
(seeds 1-300, 178 unsatisfiable) exposed four gaps that are not specific to
enumerations and fail `(Array Int Int)` inputs alike; each is closed:
the exporter's cnf th-lemmas now get the default and read facts of
constant-array comparisons that rewrites get (the old backlog item
"constant-array comparisons outside rewrites"); the array rewrite
alternative's simp set evaluates reads of constant arrays (`_select_const`),
folds `(store (const c) i c)` into `(const c)` (`_const_store_self`, moved
from the map prelude into the constant-array prelude), and decides `(= (const
c) (store (const c) i v))` as `(= c v)` either way round (`_const_eq_store`,
`_store_eq_const`); and a read of an ite over arrays gets the facts of a read
of each store or constant-array branch (`_si` facts), which also closes the
iter-082 review's failures of seeds 219, 223, 224, and 251 (all 37
unsatisfiable seeds of that sweep verify). All 178 unsatisfiable constant
seeds verify. Tests: `test_proof_to_lean_enum.py` (`ENUM_CONSTANT_INPUTS`,
`ENUM_CONSTANT_SEEDS`, seeds 219 and 251) and `test_proof_to_lean_array.py`
(five QF_ALIA inputs, one per gap).

### Nested arrays (2026-11-05)

Arrays of arrays, and arrays indexed by arrays, were rejected ("unsupported
array operator: select", "only arrays over uninterpreted sorts"); z3test
`3006`, `segfault2`, `3141`, `3529`, `3728` declare them (all sat, so none
certifies). The exporter, the clause-log replay (sort names `(Array Int
(Array Int Int))`, nested in constant arrays too), and the reconstructor
now admit an index or element sort that is itself a supported array sort,
at any depth. Lean renders it as a function type (`Int -> (Int -> Int)`,
family `arrs_iaii`); the extensionality witness over array indices is
chosen with a constant function. Reads, witnesses, and default values
whose values are arrays are unfolded in lemmas (`_folded_array`; the array
solver introduces the default row of a constant array of rows itself,
`const_rows_default`); only stores, ites, constants, maps, and
applications stay folded. Maps and set operators over sets indexed by
arrays are rejected: the embedding of a model's outer arrays is fixed off
the embedded indices, and a connective does not commute with it there.
The rewriter evaluates a
read through a stored row, `(select (select (store a i (store r j v)) i)
j)` to `v`, with no read term of the stored row, so each row stored along
the outer chain (recursively, three levels deep too) gets the read facts of
its own levels at the read's index (`_n` facts, `_stored_rows`; shown
necessary in Lean). A gap present before for
plain Int arrays showed up in a random sweep: a read that is both an opaque
Int atom of a lemma and the value of a folded store was never unfolded in
the generalization fallback, so grind failed (`stored_read_atom`, 7 lines
of QF_ALIA); `_definition_names` now takes the atoms as roots. Constant
arrays over array indices and array-valued default values stay rejected.
28 documented inputs (`NESTED_ARRAY_INPUTS`) verify in Lean, as do the 104
unsat seeds among 350 random two-dimensional Int array instances (stores,
reads, and ites of matrices and rows).

### Arrays over Bool indices (2026-11-05)

`(Array Bool E)` was rejected by the exporter ("only arrays over
uninterpreted sorts, Int, and Real") and the reconstructor ("unsupported
array sort"), which blocked z3test `5798.smt2`. Both now admit Bool as the
index sort over every element sort (uninterpreted, Int, Real, Bool), with
store, ite, extensionality, functions into and over such arrays, and maps
over sets of them; the clause-log replay needed no change. Lean's index type
is `Prop` (`_m.arrs_bi : Nat -> Prop -> Int`): an index is a formula, two
indices are equal as propositions, and the extensionality witness is a
formula chosen with `True`. A model's array over Bool embeds as `fun p => a
(decide p)` (injective, and commuting with select and store by propext), so
the generic array facts apply. Two gaps showed up: the rewriter skips a
store at `false` in a read at `true` as it skips stores at other numerals,
so `_distinct_values` now compares `true`/`false` too
(`bool_index_read_through_value_stores`, shown necessary in Lean); and the
gate clause `(or (not (= (not p) p)) (not (not p)) p)` of the index equality
of stores at `p` and `(not p)` is resolved by the SAT solver to `p` (the
double negation is one literal there), which the reconstructor rejected
("incorrect unit-resolution conclusion"). `_resolution` now concludes a kept
`(not (not x))` as `x` when `x` is kept or concluded, by
`Decidable.byContradiction` with `x`'s decidability witness
(`bool_index_negated_stores`). Constant arrays and default values over Bool
indices stay rejected (a finite index sort), as do arrays of arrays. z3test
`5798.smt2` and eleven synthetic inputs (`BOOL_INDEX_INPUTS` in
`test_proof_to_lean_array.py`) verify in Lean.

### Arrays with Bool elements (2026-11-04)

Sets, `(Array I Bool)`, were the commonest remaining array rejection
("unsupported propositional operator: select"). The exporter and the
reconstructor now admit Bool as an array's element sort over every
supported index sort (uninterpreted, Int, Real), with constant arrays,
default values, functions into and over such arrays, and ite; the clause-log
replay needed no change. Lean's element type is `Prop` (`Prop : Type`, so the
array definitions apply unchanged): an array is a predicate (`_m.arrs_ib :
Nat -> Int -> Prop`), a read `(_select a i)` is a formula, a stored or
constant value is a formula, and a Bool default value is `_default ... :
Prop`. The array solver's store axiom over a Boolean value, `(= v (select
(store a i v) i))`, is a Bool equality (Iff); an `array` lemma may compare
Bool terms only when some array has Bool elements. Bool indices and arrays
of arrays were still rejected then (Bool indices are admitted since
2026-11-05, above); `map` over sets is supported since 2026-11-05 (below).
Along the way a gap for every element sort was closed: Z3's rewriter
evaluates a read of a store over a constant array, `(select (store (const
v) y w) x)`, without any read of the constant array at `x` in the
certificate, so grind failed on the rewrite; a read of a store chain ending
at a constant array now gets `_store_apply` at every level and
`_select_const` at the bottom (`test_reads_down_to_constant_arrays_are_needed`).
On 2026-11-05 the same was found over plain arrays: the rewriter skips the
stores at numerals other than the read's, `(select (store (store a 1 5) 2 7)
3)` is `(select a 3)`, so those levels get their `_store_apply` facts too
(`read_through_numeral_stores`), and so does the store where the skip stops,
whose read at the read's own numeral the rewriter evaluates in the same step
(`(select (store (store a 3 5) 2 7) 3)` is `5`,
`read_through_numeral_stores_to_own_index`). Numerals are compared by value,
negative ones `(- n)` and Real fractions `(/ n d)` included
(`read_through_negative_numeral_stores`). Reads through stores at symbolic
indices keep one fact, so z3test's swap files are unaffected.
No z3test input is newly certified (its Bool-array files also need `map`,
nested arrays, quantifiers, or unsupported commands); sixteen synthetic
inputs (`BOOL_ELEMENT_INPUTS` in `test_proof_to_lean_array.py`) and the
Int-element `read_of_store_over_constant` verify in Lean.

### Default values read at a generic index: the default-map axiom (2026-11-11)

The array solver's default-map axiom, `(= (default (map f a b)) (f (default
a) (default b)))`, was the last rejection of the random set sweep: 64 of
the 368 unsatisfiable `random_set_instance` seeds of 1-1000 (and 40 of the
262 of 1001-1600) name no member, so Z3 refutes them by default values,
e.g. `(= ((_ map =>) a b) full)` with `a` full and `b` empty. Lean's
`_default` is the value an array takes at all but finitely many indices
(any store-invariant value when there is none), and the axiom is not a
theorem of it: the arguments of a map need not be constant almost
everywhere.

None of these inputs names a default value. The default values are then
terms of the array solver alone, and the refutation uses three properties
of them: that of a constant array is its value, that of a store is the
array's, that of a map is the function of the arrays'. One function has all
three over the terms of a certificate, whatever the element sort: the read
at one index that no store of the certificate writes. So when

- an `array` th-lemma of the certificate states the default value of a map
  (`_default_map_axiom`),
- no assertion mentions a default value, and
- no index stored at mentions one,

the reconstructor reads every default value at such an index
(`_generic_defaults`, `_Graph.generic`):

- `_generic_i` (`_generic_r` over Real indices) is a definition over the
  interpretation, `Classical.choose (_int_unbounded [i1, ..., ik])` at the
  list of the index terms of the certificate's stores over that index
  sort; `_generic_i_fresh` is its specification and `_generic_i_ne_K :
  Not (_generic_i ... = term_K ...)` the fact for one stored index
  (`_generic_index_definitions`). The index terms are definitions written
  before it, the definitions that mention a default value after it.
- `_default g a` is `a g` (`_GENERIC_DEFAULT_DEFINITIONS`), with the
  generic index where the unboundedness proof stood; `_default_const` is
  `rfl`, `_default_store` takes the proof that the index is not the stored
  one (`_default_store_fact`), and the axiom itself is a fact by `rfl`, like
  a read of the map (`_default_map_fact`; over a map of `ite` the lemma
  unfolds the ite of the default values, `_map_read_values`). Rewrites and
  cnf lemmas that compare arrays get the facts of the maps they reach too:
  the replay may tie a logged equality to an assertion that is false of
  the default values alone (seed 67, a set equal to a store into its
  complement).

The theorem is unchanged: its hypotheses are the assertions, which do not
mention the index (they are defined before it), and nothing is assumed of
it (it is chosen, and Lean checks that it is off the stored indices:
`test_the_generic_index_is_proved_off_the_stored_indices` chooses it off the
empty list instead and expects the rejection). An input that names a
default value keeps Lean's `_default`, and a refutation of it through the
axiom is rejected as before, by the exporter (`_Replay._require_certified`,
which now asks whether an assertion names one) and by the reconstructor
(`_check_th_lemma`). A certificate that does not use the axiom is rendered
as before. Default values of arrays of an enumeration get no case facts at
a generic index (`_read_cases`).

After: all 368 unsatisfiable seeds of 1-1000 verify in Lean (304 before);
of the 262 of 1001-1600, 258 verify (218 before) and none is rejected. The
other four fail in Lean as they did before (`grind` in a rewrite or cnf
lemma, not through default values: 1083, 1088, 1398, 1486). Still
rejected: the axiom next to a default value the input names. Tests
(`test_proof_to_lean_array.py`): fifteen documented inputs
(`GENERIC_DEFAULT_INPUTS`: Int and Real indices, both at once, a
Real-indexed array that takes no default value next to sets over Int,
stores under and over the map, maps of `+`, `<=`, `ite`, and an
uninterpreted function, a row of nested arrays, a trimmed log, enumeration
arrays next to the sets; Lean), the pinned seeds `GENERIC_DEFAULT_SEEDS`
(Lean),
`test_default_values_are_read_at_a_generic_index`,
`test_default_values_of_maps_are_rejected` (now inputs that name a default
value), and `test_the_generic_index_is_proved_off_the_stored_indices`.

### Sets compared member by member (2026-11-11)

Z3's rewriter simplifies a map of connectives over sets as it simplifies
the connective over their members (`array_rewriter::mk_map_core`), and
decides an equality between the results when they are constant arrays:
`(setminus s s)` is the empty set, `(intersection (complement s) (setminus
s t))` too, nested maps of `and` are flattened, sorted, and stripped of a
repeated set, a difference of stores at one index is the store of the
difference, `(= ((_ map and) s (complement s)) full)` is false. The
certificate holds the sets before and after; they are equal as functions
of their members, but by no identity of a single map node
(`_map_identities`), so `grind` failed in the rewrite, or in a cnf lemma
over such sets: 17 of the 114 exported seeds of `random_set_instance`
1-400, and 26 of the 190 of 401-1000.

`_pointwise_map_facts` (`proof_to_lean.py`) reads each set term over
Booleans a rewrite or cnf lemma reaches as a Boolean function of its
leaves: the sets its maps, set operators, and stores are over, the Boolean
values stored or held by constant arrays (other than true and false), and,
per stored index, whether the member's index is that one. It computes the
truth table (at most `_POINTWISE_LEAVES` = 8 leaves and `_POINTWISE_SIZE`
= 48 maps and stores per term, counted as its member formula writes them;
a larger term is a leaf itself) and states

- two terms of one function equal: `have _pwN : A = B := funext (fun _i =>
  propext (rewrite_K_pwJ (_select a _i) ...))`, or `funext (fun _i => rfl)`
  when the two have one member formula (a union and the map of `or` over
  the same sets);
- the sides of an equality whose functions differ in every row different:
  `A = B -> False`, at an inhabitant of the index sort (0 over Int and
  Real; over an uninterpreted sort only when the interpretation already
  states `nonempty`, next to an extensionality witness);
- in a cnf lemma, the members of an equality's sides at each index the
  lemma reads from a set of that sort, `A = B -> (Iff (member of A at i)
  (member of B at i))`, by `congrFun` (three seeds of 401-1000: an
  assertion logged as written, tied to a clause about one member).

The auxiliary theorems `rewrite_K_pwJ` are over the members as
propositions and are proved by `grind` with nothing else in its context;
the member formulas are what the sets' definitions unfold to at an index,
so the instances type-check by unfolding. The tables only choose which
facts to state: a wrong table gives a theorem `grind` cannot prove or a
fact that does not type-check. Steps without a map or set operator get
nothing (stores alone stay with the store identities).

What the facts cost is bounded in two ways, both found on `(select X i)`,
`(not (select a i))`, `(= c (setminus a a))` with `X` sixteen nested maps
`((_ map xor) ... b)` over `a`, which verified in 0.6 s before any
pointwise fact (every second level of the nest has the function of `a` or
of `(xor a b)`, and no step needs to know):

- A map of `xor` writes the member formula of each argument twice and a
  map of `ite` that of its condition, so the formula of a nest doubles per
  level. `_POINTWISE_SIZE` counts a map's argument once per occurrence in
  what `_map_application` writes (`_pointwise_occurrences`): five nested
  maps of `xor` count 31, the sixth is a leaf. Counted as a tree of maps,
  the sixteen levels were under the limit: 10.8 MB of text, and an
  auxiliary theorem out of heartbeats (172 MB at twenty levels).
- A step is first tried without its pointwise facts and then again with
  them (`_grind_lemma`; each attempt is an alternative of `first`). With
  small auxiliary theorems and the facts in the only attempt, the cnf
  lemma of that input, given the eleven equalities between the levels of
  the nest, ran out of its 1,000,000 heartbeats (`whnf`, inside `grind`,
  after 15 s); stating the facts and clearing them took 0.6 s, so the cost
  is `grind` closing the classes of the equated sets under the maps and
  reads of its context. `first` does not catch a heartbeat timeout, so
  the attempt without the facts has to come first: a step that needs none
  is proved as before, and a step that needs them fails the first attempt
  with `grind` failed, as it did before the facts existed.

An auxiliary theorem is stated once per certificate
(`_Graph.pointwise_theorems`, by its text): a later step that compares the
same two member formulas uses the earlier step's theorem. Over the 304
exported seeds of 1-1000 that is 221 auxiliary theorems instead of 477
(207 of those had one formula on both sides, now `rfl`), 7.19 MB of text
against 6.80 MB (the repeated attempts), and the same Lean time (131 s).

After: all 304 exported seeds of 1-1000 verify in Lean (261 before; the
other 64 unsatisfiable ones rest on the default-map axiom and stayed
rejected until "Default values read at a generic index" above). Still
open: an equality of sets decided false over an uninterpreted index sort
when the interpretation has no `nonempty` field (`(= (union a (complement
a)) (setminus b b))` over `(Array Index Bool)`); and a step that needs
some of its pointwise facts while `grind` cannot afford all of them (none
is known).
Tests (`test_proof_to_lean_array.py`): ten documented inputs in
`SET_COMBINATOR_INPUTS` and the pinned seeds `POINTWISE_SET_SEEDS` (Lean;
each failed before), the sixteen nested maps of `xor` and of `ite`
(`set_read_of_nested_xor_maps`, `set_read_of_nested_ite_maps`; Lean),
`test_sets_are_compared_member_by_member`, and
`test_map_facts_are_needed`. The last drops each kind of fact alone; for
the six rewriter identities of a single map of connectives, which the
pointwise facts prove as well, it reconstructs the input without pointwise
facts (over `_POINTWISE_SETS`), checks that Lean accepts it by the
identities alone, and that Lean rejects it without them. Four inputs need
the pointwise facts themselves.

### Set logs: operators as written, unused default-map axioms (2026-11-11)

A sweep of random constraints over four sets of integers
(`random_set_instance`: equalities and disequalities between unions,
intersections, differences, complements, maps of `=>`, `xor`, `and`,
inserts and removals, the empty and the full set, and members read)
showed the replay rejecting 61 of the 142 unsatisfiable seeds of 1-400, for
two reasons that are not about the refutation:

- Once an assertion simplifies to false, Z3 logs the remaining assertions
  as they are written, set operators included: `(complement s2)`,
  `(intersection s1 s1)`, `(setminus a b)`, and union with its sort,
  `((as union (Array Int Bool)) a b)`. Elsewhere the log holds the maps the
  rewriter makes of them, so the replay built `(_ map f)` heads only
  ("unsupported operator in the clause log: complement", "unsupported
  application head"; 28 seeds). `_Terms.build` now builds the four operators
  (`_SET_HEADS`), under `map_parameters` like the input's own, and checks the
  sort an `as` head names. Z3 qualifies only its own functions, so
  `(as union S)` is the operator even when the input declares a function
  named `union` (over other sorts; Z3 rejects one with the operator's own),
  which takes the bare name as for every head. The other three operators
  are printed bare, so beside a function of their name the log is ambiguous
  and the input is rejected ("ill-sorted application of intersection in the
  clause log", an `AttributeError` of z3py before).
- The array solver states the default-map axiom, `(= (default (map f a b))
  (f (default a) (default b)))`, for every map it meets, whether or not a
  conflict comes to rest on it, and the replay rejected it on sight. A log
  of 4 KB or more is trimmed, which drops an unused axiom; a shorter one is
  not, so `(= (setminus a b) empty)` with a member of `a` outside `b` (what
  the rewriter makes of `subset`), or the same as a full `=>` map, was
  rejected although its refutation is two reads (5 seeds). The replay now
  records the axiom's node (`_Replay.uncertified`), rejects with the same
  message only when the refutation reaches it (`_require_certified`), and
  otherwise leaves it out (a compact certificate). The default value of a
  store over a map, `(= (default (store m i v)) (default m))`, was taken for
  the axiom too; it is `_default_store`'s and is kept (`_default_map_axiom`).
  The reconstructor rejects the axiom on its own (`_check_th_lemma`), where
  Lean would have failed before.

After: 114 of the 142 export and 97 verify in Lean (81 and 67 before; 30
of the 33 new ones verify). Still open: the other 28 rest on the
default-map axiom (no member is named, e.g. `(= ((_ map =>) a b) full)`
with `a` full and `b` empty) and stay rejected (certified since "Default
values read at a generic index" above); and 17 fail Lean in a
rewrite where Z3's rewriter decides an equality of sets by map identities
(`(setminus s1 s1)` is empty, `(not (not s))` is `s`, flattened and sorted
`and`s), which had no theorem (14 of them exported before as well; they
verify since "Sets compared member by member" above).
`subset` itself is still rejected as an operator. Tests
(`test_proof_to_lean_array.py`): six documented inputs in
`SET_COMBINATOR_INPUTS` and the pinned seeds `SET_SEEDS` (Lean),
`test_the_replay_reads_set_operators`,
`test_unused_default_values_of_maps_are_left_out`, and
`test_default_values_of_maps_are_rejected` (now an input whose refutation
needs the axiom, short and behind enough clauses for the log to be trimmed,
and the reconstructor's own rejection of both).

### Replay keys of maps and constant arrays (2026-11-06)

The replay ties a clause the log assumes to an input conjunct by its
structural key, which named uninterpreted symbols, numerals, and
constructors but not the parameters of built-in heads: `((_ map and) a b)`
and `((_ map or) a b)`, maps of two declared functions, or of `+` and `-`
over the same arrays shared one key. When preprocessing split a conjunction,
a conjunct with one map was derived from the input's conjunct with the
other, and Lean rejected the step (`grind` failed). The key of a map now
names its function by signature (`(declare-fun f (Int) Int)`, built-ins
alike), and that of a constant array its sort. A random sweep of maps of
several functions over the same arrays inside guarded conjunctions (200
seeds, not kept in the repository) had 5 of 41 unsat seeds fail in Lean
before and 41 of 41 verify after. Other parameterized heads (datatype
accessors, bit-vector `extract`, `as-array`) still key without their
parameters; the export rejects them today, so they must be keyed when
they become supported. Tests:
`test_replay_keys_tell_maps_and_constant_arrays_apart` and the documented
inputs `conjuncts_map_and_or`, `conjuncts_map_f_g`,
`conjuncts_map_plus_minus` (`test_proof_to_lean_array.py`).

### Trimmed map logs (2026-11-06)

The trimmer could not read back any clause log with a map: Z3 printed
`((_ map f) a)` without ever declaring `f` (the declaration collector did not
follow a map's function parameter, as it does for `as-array`) and a built-in
as `(_ map <=)`, without the signature the SMT-LIB parser requires
("unknown function f", "must provide signature for builtin symbol <="). Every
map log of 4 KB or more was replayed untrimmed, and inputs whose search
derived the default-value axiom of a map were rejected even when the
refutation does not use it. `decl_collector` now collects a map's function,
so every printer that uses it (clause logs, but also `to_smt2` and
`Solver.sexpr()`) declares a mapped uninterpreted function. The clause-log
printer (`mk_ismt2_func`, used only by `ast_pp_util::define_expr`) prints the
built-in function of a map with its signature,
`((_ map (<= (Int Int) Bool)) a b)`; other indexed heads such as `(_ is C)`
and `(_ update-field a)` keep their standard form, and Z3's general printer
still prints `(_ map <=)`. The replay accepts both map forms and rejects a logged signature that
is not the rebuilt application's. All 92 unsat seeds of the iter-078 random
map sweep now export with trimming (the 2 previously rejected by the
default-map axiom included) and the 305 documented array inputs trim
without fallback at threshold 0. Tests: `test_native_trimming_reads_map_logs`
and `test_clause_logs_print_datatype_heads_without_signatures`
(`test_proof_certificate.py`), signature heads in
`test_the_replay_reads_maps`.

### Maps of other functions (2026-11-05)

Maps of anything but `not`, `and`, `or`, `=>` were rejected ("maps are
supported over the connectives not, and, or, => only"), although Z3 solves
such inputs. Maps of `xor`, `=` and `distinct`, Int and Real `+`, `-`
(binary and unary), and comparisons, `ite`, and uninterpreted functions and
predicates of up to three arguments, over elements of an uninterpreted sort,
Int, Real, or Bool, are now certified through the clause log. The
certificate names a built-in by its SMT-LIB name and an uninterpreted
function as `("declared", f)`; the replay rebuilds `(_ map +)` (logged
without a signature) from the arrays' element sorts; the reconstructor binds
a mapped function to the input's symbol and signature even when it is never
applied, and checks each built-in's element signature. Lean's
`_map1`/`_map2`/`_map3` are polymorphic in the element types and take a
lambda whose body is the application as the term and formula renderers
write it, so the select-map read facts (beta-reduced by rfl) match the
lemmas' terms; maps of stores and constants reuse the set theorems, and
maps of commutative functions get `_map2_comm` with the pointwise swap
proved by `grind`. A random sweep found one more gap, which set operators
already had: Z3's rewriter skips a store at another numeral index and
evaluates the read of a map below it (`(select (store ((_ map not) s) 1
false) 0)` is `(not (select s 0))`) with no read term of the map, so such
a read now gets the map's read facts too (`_skipped_to_map`), and a read
of a map goes on through the stores below it the same way.
Multiplication, conversions, uninterpreted functions of four or more
arguments, connectives of three or more arguments, and maps over arrays of
arrays stay rejected. Tests: `MAP_FUNCTION_INPUTS` (29 inputs, Lean), `test_map_function_encoding`,
`test_tampered_map_functions_are_rejected`, `test_the_replay_reads_maps`,
and seven more cases in `test_map_facts_are_needed`; of 200 random map
inputs from a one-off sweep (not part of the repository), all 90 unsat ones
that export verify in Lean, and 2 more are rejected explicitly (they need the
default-map axiom). z3test's maps of
arithmetic (`t155.smt2`, `t154.smt2`) are sat or use `eval`/options, so no
z3test file newly certifies.

### Maps and set operators over sets (2026-11-05)

`((_ map f) a b)` was rejected ("unsupported array operator: map"), which
blocked z3test `t8.smt2` and `issue-1665.smt2`. Maps of `not`, `and`, `or`,
`=>` over sets of one sort and Z3's set operators (`union`, `intersection`,
`setminus`, `complement`) are now certified through the clause log: the
certificate's map declaration carries the connective as its parameter, the
replay reads `(_ map f)` heads, and Lean's `_map1`/`_map2` apply a function
over `Prop` pointwise. The select-map axiom (an `array` hint stating the
propagated equality, as for the store axiom) is rfl per read, stated through
nested maps and into the stores and constant arrays below them, which Z3's
rewriter evaluates in one step. The identities euf and the rewriter apply
(commutativity and idempotence of `and`/`or` maps, double complement, maps of
stores at one index, maps of constant arrays) are funext theorems
instantiated per map node, and a `setminus` node is stated equal, by rfl, to
the map of `and` over the complement that the rewriter turns it into
(`setminus_named`; the other set operators share their Lean function with
the map they become); each is shown necessary by
`test_map_facts_are_needed`. The default-map axiom is not valid for
`_default` (a map's arguments need not be constant almost everywhere) and is
rejected explicitly ("the default value of a map is not certified"; since
2026-11-11 only when the refutation uses it, see "Set logs: operators as
written, unused default-map axioms", and only when the input names a
default value, see "Default values read at a generic index"); input
`default` terms are admitted over Int and Real indices. z3test `t8.smt2` and
`issue-1665.smt2` queries 1 and 2 verify in Lean (query 0 takes default
values over an uninterpreted index and stays rejected). Maps of other
functions (uninterpreted, arithmetic) stayed rejected until the entry above.

### Functions into arrays (2026-11-04)

Uninterpreted functions returning an array, `(declare-fun h (I) (Array I
E))`, were rejected by the exporter ("uninterpreted functions over
Array(I, E)") and the reconstructor ("unsupported array declaration"),
although functions over arrays were certified. Both now accept them on the
clause log, for every array sort already supported (index and element sorts
uninterpreted, Int, or Real); the result may be the array sort of an
argument too. Lean renders each as one more family per Lean array type
(`_m.arrs_funs`, `_m.arrs_ii_funs : Nat -> List U -> Int -> Int`, ...),
taking the injected argument list like `_m.funs`, so a model's function
into arrays is an instance through the embedding of its array values that
the array constants use. Applications stay folded in the array lemmas like
stores and are each stated equal to their body (a `_t` fact), so grind's
congruence closure compares them by arguments; without those facts grind
fails (`test_application_facts_are_needed`). Arrays over Bool or arrays stay
rejected as results as well as arguments. No z3test input is newly
certified (the fuzzsmt `t168`/`t170` regressions with such functions are
satisfiable); eleven synthetic inputs (`ARRAY_FUNCTION_INPUTS` in
`test_proof_to_lean_array.py`: store, extensionality, ite, constant arrays,
predicates over applications, Int/Real/mixed sorts, arrays to arrays, two
functions sharing one family) verify in Lean.

### Constant arrays over Int and Real indices (2026-11-03, 2026-11-04)

Constant arrays `((as const (Array I E)) v)` were rejected ("unsupported
array operator: const"), so z3test `regressions/smt2/2549.smt2` and the six
queries of `array.smt2` could not be certified. With constant arrays in the
input, the sat.smt array solver relates arrays through their default values,
logging `array` hints over `(default a)` terms: `(default (const v)) = v` and
`(default (store a i v)) = (default a)` (index sorts it considers large).
Both hold only over an infinite index sort, so uninterpreted index sorts
(possibly finite) stay rejected by the exporter and the reconstructor. Real
indices are infinite but not implemented yet (they need an unboundedness
lemma over Rat like `_int_unbounded`), so constant arrays are now accepted
over Int indices only, on the clause log only. Lean
renders a constant array as `_const_array Int v` and a default value as
`_default _int_unbounded a`, where `_default` is defined on every function
(the value taken outside some finite list of indices, else a store-invariant
choice) and `_default_const`, `_default_store` are theorems from
`_int_unbounded` (no finite list exhausts Int). The replay reads `as const`
and `default` terms (defaults are linear atoms), and the single-equality
`array` hints of these axioms are the propagated equality, like the store
axiom. Z3's rewriter decides an equality between stores over constant arrays
by default values or values at the stored indices; rewrite steps reaching a
constant array get those facts (`_constant_array_comparisons`). Result:
`2549.smt2` and all six `array.smt2` queries export and verify in Lean.
Tests: `CONSTANT_ARRAY_INPUTS` in
`test_proof_to_lean_array.py`.

Real indices (2026-11-04): constant arrays and default values over
Real indices are accepted too. Lean proves `_rat_unbounded` (no finite list
exhausts Rat, bounded by `max (a + 1) b` per element, grind over Rat) and
instantiates the same `_default_const`, `_default_store`, and
`_select_const` at `Rat`; the reconstructor maps each admitted index sort to
its unboundedness theorem (`_UNBOUNDED`), proves only the theorems of the
index sorts of the file's array sorts (Int-indexed output is unchanged), and
still rejects uninterpreted index sorts. No z3test file uses Real-indexed constant arrays; the five
`REAL_INDEX_CONSTANT_ARRAY_INPUTS` (2549 and array.smt2's third query over
Real indices, a Farkas read, stores at Real terms, uninterpreted elements)
verify in Lean, and grind fails on the Real 2549 and comparison inputs once
the default or read facts are removed.

### Arrays over Int and Real, and functions over arrays (2026-11-03)

Arrays were certified only between uninterpreted sorts, so all 13 of
z3test's 25 smtlib-sample QF_AUFLIA files that use arrays (`(Array Int
Int)`) were rejected ("only arrays from one uninterpreted sort to
another"), and 10 of them also by their Skolem function `sk : (Array Int Int) (Array Int Int)
-> Int` ("uninterpreted functions over Array(Int, Int)"). Index and element
sorts may now be Int or Real as well, on the clause log only: Lean renders
them as Int and Rat (`(Array Int Int)` is `Int -> Int`, one family of
constants per Lean array type, `_m.arrs_ii`), and the array definitions
and theorems are generic in both types. A read of an Int or Real array is
an atom of the linear forms on both sides (exporter `_linear`,
reconstructor `_LINEAR_ATOM_KINDS` and the generalized opaque atoms, never
inside a folded array term), the qf_lira sort of a step does not look into
array terms, and an extensionality witness over Int or Rat chooses with
`Nonempty.intro 0`. An `array` lemma may compare Int or Real terms only if
some array of the certificate has that sort. Functions and predicates may
take arrays: an array argument is injected into the carrier by one field per
Lean array type (`_m.arrs_ii_inj`), as Int and Real arguments are. No map
from `U -> U` or `U -> Int` into `U` is injective, so a model is an instance
because only finitely many array values are denoted: `U` gets one fresh
point per denoted array, which the injection picks and the functions read
back. Any theory step reaching a store, not only a rewrite, is offered the
store identities as a last alternative: a `th-lemma cnf` over a predicate
of `(store c n (select c n))` needs `_store_select`. The
unused-simp-argument lint is off for the one store-identity `simp` (it is an
error under `warningAsError` when simp needs only one identity). Result: of
the 13 QF_AUFLIA files with arrays, 8 verify (the largest, a 9.2 MB file,
in 2 minutes); the 4 swap files with `sk` reconstruct to 66 to 243 MB of
Lean, too large to check, and `cvc/dlx-regfile` exhausts the exporter's
memory. Tests: `ARITHMETIC_ARRAY_INPUTS` in `test_proof_to_lean_array.py`.

### Arrays over uninterpreted sorts through the clause log (2026-11-03)

Any array sort was rejected ("unsupported sort"), so none of z3test's 25
smtlib-sample QF_AX benchmarks (storecomm, storeinv, swap) could be
certified. Arrays from one uninterpreted sort to another (array constants,
`select`, `store`, `ite`, equality) now join the UF fragments on the clause
log; the legacy core rejects them explicitly. The replay reads array sorts
in definitions, `select`, `store`, and the extensionality witness
`(_ array-ext 0)` (z3py `Ext`). An `array` lemma is the complement of its
hint, like `euf`, except for the store axiom: that hint lists the
equality it propagates (`propagate_axiom`), so the lemma is that equality.
Lean renders an array as a function `_m.U -> _m.U` (constants `_m.arrs`),
`select` as `_select`, `store` as the classical update `_store`, and the
witness as `_array_diff`, an epsilon choice that needs `_m.nonempty`. A
model's arrays embed injectively, commuting with `select` and `store`, so
every model is an instance. grind proves the array lemmas with two kinds of
per-lemma fact, `_store_apply` for each read of a store and `_array_ext`
for each witness. Array terms stay folded in those lemmas (`term_N`, tied to
its body by `rfl`): inlined, the shared store chains grow exponentially and
exhausted the kernel. Rewrites over stores may also use `_store_store` and
`_store_select`, the identities Z3's rewriter applies. All array facts are
theorems in the file. Result: 23 of the 25 QF_AX files verify (the slowest
in 88 s). `storecomm_t2_np_nf_ai_00050_007` and `swap_t2_np_sf_ai_00009_002`
(17 and 29 MB of Lean) still hit "(kernel) excessive memory consumption".
That happens in outlined proof steps, not in array lemmas. Tests:
`test_proof_to_lean_array.py`.

### Pseudo-Boolean constraints through the legacy core (2026-11-02)

Propositional input may now use `at-most`, `at-least`, `pble`, `pbge`, and
`pbeq` over Boolean variables and their negations (integer parameters; any
other argument, or such a constraint next to arithmetic or uninterpreted
functions, is rejected). The certificate keeps each constraint's bound and
coefficients as declaration parameters, and the reconstructor binds them to
the input like the arguments. Lean states a constraint as an Int comparison
of the weighted sum of its literals' values, the classical `if l then 1 else
0`. theory_pb's `(_ th-lemma pb)` steps and the rewrites over constraints
(Z3 normalizes `at-most k` to `at-least` of the negations, weights by their
gcd, decides trivial bounds) are proved after unfolding: a negation's value
becomes one minus its variable's (`_pb_not`), each variable's value is
generalized to an Int between 0 and 1 (`_pb_bit`; bounds rather than the
disjunction `= 0 or = 1`, which omega splits: 83 s against nothing for a
16-variable at-most), the variable itself becomes `_x = 1`, and omega
decides the rest. Only the legacy core: the sat.smt core compiles the
constraints away before its clause log starts and logs bare `smt` clauses
that cite none of them, so the clause-log exporter rejects them.

Lean rejected two kinds of theory_pb step that do not hold on their own,
both fixed in `theory_pb.cpp` when proofs are enabled. Internalizing a
weighted constraint folded the values of arguments already assigned at
the base level into the bound and then stated, say, `(not (pbge 7 ...))` as
an axiom without them (the input's `(pble 0 ...)` had fixed those
arguments false). With proofs enabled no argument is folded (constants
still are); the arguments are read off the assignment once the constraint's
literal is assigned, so only an early propagation is lost. Cardinality
conflict resolution derived a cutting-plane resolvent and propagated its
asserting literal citing the antecedent literals only, not the constraints
resolved: `(not p3), (not p12), (pbge 28 ...) |- (not p0)` with p0 in no
cited constraint. With proofs enabled the conflict clause is learned
instead, a valid th-lemma. Before the fixes 16 of 31 unsat random 5-variable
instances failed Lean; after them, z3 confirms every th-lemma pb of 486
random and 10 pigeonhole refutations on its own, and all 113, 77, 50, and
37 unsat instances of four random sweeps (5 to 24 variables) and
pigeonhole up to 6 pigeons in 5 holes (1,572 steps, 8 s) verify in Lean;
so do the two unsatisfiable queries of z3test `regressions/smt2/pb.smt2`.
Tests: `test_proof_to_lean_pb.py`.

### cnf lemmas over a distinct's pairs; conjuncts projected from tails (2026-10-30)

NEQ004's twelve cnf lemmas (`(not A) or (not (= c2 c3))` and the like, A
the 814-definition assertion holding `(distinct c0 c1 c2 c3)`) all went to
the unfolded grind fallback, about 3 s each: the propagation prover read
the distinct as one opaque leaf, so the clause's literal named nothing in
A. A distinct over terms whose every argument pair (a, b) has its own node
`(= a b)` (the alldiff literals Z3 logs) is now read as the conjunction of
those equalities negated, which is how `_formula_body` renders it, so the
pairs are shared leaves (and bridged to `(= b a)` like any other equality
leaves). A pair logged only with its sides swapped keeps the distinct a
single leaf. With the lemmas in reach, half of them made the 400-operand
assertion true and projected every conjunct from its proof
(`And.left (And.right ...)`, 80,000 levels): 30 s in Lean, ten times
grind. The prover now projects by field notation from a tail bound once
every `_AND_ELIM_STRIDE` operands, as and-elim does: those lemmas check in
under a second, and NEQ004 as a whole in 79 s at a 5.54 GB peak (was
116 s, 7.06 GB, measured on the same machine), more headroom under the
8 GB cap. Tests: `test_cnf_lemmas_read_a_distinct_over_terms_as_its_pairs`
and `test_cnf_lemmas_over_a_distinct_verify_by_propagation_alone` (the
fallbacks dropped, so Lean checks the propagation proofs themselves) in
`test_proof_to_lean_uf.py`, and the NEQ004 test now requires a
propagation attempt for each of its cnf lemmas.

### One interpretation argument; serial elaboration of large files (2026-10-30)

z3test's QF_UF `NEQ/NEQ004_size4` (16 KB of SMT-LIB) exported in 3 s but
failed in Lean with "(kernel) excessive memory consumption" since the
2026-10-27 `--memory=8192` cap: 20,634 proof steps become 13,700
declarations and 21 MB of text, and Lean's memory grew past 11 GB within
30 s. Two changes bring it to 7.06 GB (103 s). The carrier and maps of the
UF fragments (`_U _elems _funs _preds _bool`, plus `_real _rfuns` or
`_int _ifuns`) are now the fields of one structure `Interpretation`
declared in each file, and every declaration takes the one argument
`(_m : Interpretation)` next to `_atoms` (and `_vars`), so every reference
`formula_k _atoms _m` is two arguments instead of six to eight; quantifying
over the structure is quantifying over its fields, so the theorem states
the same thing. A file of more than 8 MB of Lean text also sets
`Elab.async false`: parallel elaboration keeps far more memory alive. Measured on
NEQ004 (11 GB cap, to see the peaks): six parameters in parallel above 11 GB, one
structure in parallel 10.1 GB, six parameters serially 9.6 GB, one structure
(with `_atoms` folded in too) serially 6.5 GB; four threads instead of all
cores did not help (10.0 GB). Serial elaboration costs about three times the
wall time, so smaller files keep the parallel default (no other test file
exceeds 3.9 MB). Tests: `test_interpretation_is_one_structure_argument`,
`test_large_files_are_elaborated_serially`, and
`test_large_certificates_verify_under_the_memory_cap` (NEQ004, about 110 s)
in `test_proof_to_lean_uf.py`.

### Limits on the legacy solve and the clause-log replay (2026-10-30)

The two in-process stages the note below left unbounded now take the same
limits. The legacy core (`export_certificate(..., timeout, memory)`, and
`proof_certificate.py --timeout/--memory`, which `--core auto` uses for
propositional input) sets the time limit as its solver's `timeout` and the
memory limit as z3's `memory_high_watermark_mb`, a global parameter the smt
core polls during the search, set for the check and restored after it
(`memory_max_size` would throw from the allocator and leave z3 marked out of
memory for the rest of the process). The smt core reports them as unknown
with "canceled" and "memout", now raised as "the legacy solver run exceeded
the time limit of N s" (only when the check lasted the limit; an earlier
"canceled" is an interrupt and stays "unknown: canceled") and "z3's memory in
this process exceeded the limit of N MB during the legacy solver run" (the
watermark compares all of z3's allocations in the process, not the solve's
own). The clause-log replay
(`build_certificate(..., timeout)`) has a wall-clock deadline of the time
limit, checked before every log command and every bounded solver call of
the assumption search: QF_IDL `qlock-4-10-8` exported in 622 s under a 60 s
z3 timeout and is now rejected with "the clause-log replay exceeded the time
limit of 60 s". Nothing about what Lean certifies changes. Tests:
`test_legacy_solve_stops_at_the_limits` and
`test_replay_stops_at_its_time_limit` in `test_proof_certificate.py`.

### Time and memory limits on the exporter's z3 runs (2026-10-30)

The clause-log export starts the z3 executable twice, to solve and to trim,
and before this change bounded neither by memory and the solver only when
the caller passed a timeout. A sweep that exported without one left eleven
z3 processes running after its own deadlines killed the Python workers
(220 GB in total). Both runs now always carry `-T` and `-memory` (600 s and
8192 MB unless the caller passes `timeout`/`memory`, CLI `--timeout` and
`--memory`), so an orphaned run stops by itself, plus a wall-clock deadline
30 s past the time limit. Limits above 10^6 s or 2^22 MB are rejected:
larger ones overflowed `subprocess.run` and z3's `-T`/`-memory` parameters
(4294967295 MB makes z3 report out of memory at once). Hitting a limit is an error naming it ("the
clause-log solver run exceeded the time limit of 1 s", "native proof
trimming exceeded the memory limit of 20 MB"). Before, a trimmer stopped at
either limit (`timeout` on stdout with status 0, `(error "out of memory")`
with status 101) read as an unusable log and the export silently went on
with the untrimmed replay. `trim_clause_log` itself still raises
`subprocess.TimeoutExpired` at the time limit, as z3test's `proof_lean.py`
expects. Not bounded: the legacy core and the replay's own solver calls run
in process (the latter under `_RLIMIT`). Tests: three in
`test_proof_certificate.py`, the live one on pigeonhole inputs.

### Equivalence search only over the clause's symbols (2026-10-29)

`assume` ties an assumed clause the canonical keys do not match by a
bounded solver check for an equivalent conjunct (a rewrite), then for an
implying one (a cnf lemma). On a right-nested conjunction every suffix
shares the clause's symbols: FISCHER6-4-ninc checked seven clauses for
equivalence against all 1,743 such conjuncts, 12,207 solver calls each
asserting a suffix of the conjunction (459 s of export), before the whole
assertion, the first candidate, implied each. Only conjuncts over exactly
the clause's symbols (a hash of each source's symbol set is kept with the
symbol index), and leaf conjuncts (not ands) over at least them, are
checked for equivalence now. The leaves matter: Z3 may simplify a symbol
away (`(f (* 0 y))` to `(f 0)`), and without them such a clause was tied
by the implication pass through a cnf lemma over the whole assertion,
which Lean failed to prove within its heartbeats on a thousand-wide QF_UFLIA
conjunction (review of this change). Each leaf is checked at most once per
clause, so the cost stays linear in the assertions. FISCHER exports in
about 3 s (55 equivalence checks on leaves, 7 implications) and verifies
in Lean; it is test data now (`test_proof_to_lean_lia.py`), with unit
tests in `test_proof_certificate.py` and the QF_UFLIA case in
`test_proof_to_lean_uflia.py`.

### and-elim from shared conjunction tails (2026-10-29)

and-elim projected operand k of a right-nested conjunction by field
notation with k `.2`s, so a refutation that eliminates every operand of a
wide conjunction held a quadratic number of projections. Legacy refutations
that eliminate most operands of a conjunction of 600 or more failed in Lean:
in the 600-operand implication chain one outlined lemma eliminated 250
operands through 94,000 projections and exhausted its heartbeats, and
iter-045's 1,200-operand Real/Boolean chain (`mixed1200`, legacy core)
failed the same way. The reconstructor now binds the rest of such a
conjunction once every 32 operands (`let _tail_P_K := ...`, each tail
projected from the one before with an inferred type) in every lemma and
theorem that eliminates from it, and each and-elim projects at most 32
levels from the nearest tail. Premises that take hypotheses still project
from the start. The 600-operand implication chain checks in 6 s and
`mixed1200` in 28 s. Tests: `test_proof_to_lean_wide.py`, outlined (600
operands), inline (150), and outlined with the conjunction's proof local to
the eliminating lemma (80).

### Ite value tables evaluate comparisons of numeral-valued ites (2026-10-31)

`sal/carpark/Carpark2-ausgabe-6`, the last of the four rewrite failures
below, verifies (15 s; it failed after 117 s with five heartbeat timeouts).
Its rate is `(ite (= s 4) 20 (ite (= s 3) 10 ...))` over a selector `s`, an
ite chain over four flags with numeral branches, and Z3's rewriter decides
the comparisons, leaving an ite over disjunctions of the flags'
conjunctions. `_ite_table` now evaluates an atom whose linear form ranges
over such numeral-valued ites (`_numeral_ite`) instead of keeping it as an
independent leaf: its leaves are the selector's condition leaves, so the
two rate ites share a table. An atom over an ite with a non-numeral branch
stays a leaf, as before. The atom lemma relating the two rate ites (grind
and `repeat' split` both fail there) gets a third alternative: `by_cases`
on each Boolean variable of the ites' conditions (at most eight), `simp
only` with connective and `ite_true`/`ite_false` rewrites and `decide` to
evaluate the conditions and comparisons, then grind. The matching remains a
heuristic that only chooses which term is rendered; a wrong match fails in
Lean. Tests: `test_rewrite_over_numeral_comparisons_of_selector_ites_verifies`
(clause-log core: grind over the whole rewrite timed out after 60 s before)
and `test_ite_value_tables_evaluate_comparisons_of_numeral_ites` in
`test_proof_to_lean_arith.py`.

### Normalized rewrites over ite terms and wide flattenings (2026-10-30)

Four QF_LRA smtlib-sample benchmarks failed Lean in a whole-assertion
rewrite. In `spider_benchmarks/mode_cntrl` and `current_frame` the
rewriter reshapes Real `ite` terms (`(ite (not b) (ite c (+ x 1) x) x)`
becomes `(ite (or b (not c)) x (+ 1 x))`), so the ites of the two sides
differ, the generalized attempt failed, and grind over the unfolded rewrite
ran out of heartbeats; ites kept these rewrites off the normalized path. An
ite is now one opaque term keyed by its value table (its linear-form value
under every assignment of at most eight condition leaves, Boolean variables
and normalized atoms), and the atom lemma over the other side's ite proves
the two equal by grind, or, when grind fails (an iff or xor condition), by
`repeat' split` and grind on each case. In `clocksynchro_8clocks.main_invar` the
propositional lemma of a 250-way disjunction (left-nested on one side,
flattened on the other) exhausted the prover's character budget, and grind
failed. The prover of a normalized rewrite now first links the structures
of the two sides that are equal up to and/or flattening, order, duplicates,
constants, and double negation, children first (iff by `iff_congr`, the
rest by its search), proves each direction by contradiction, and refutes
the disjuncts of a false disjunction from tails bound every 32 operands
(the mirror of the conjunction tails). mode_cntrl verifies in 6 s,
current_frame in 8 s, clocksynchro_8clocks in 60 s. Still open then (done
2026-10-31, above): `sal/carpark/Carpark2-ausgabe-6`, whose rewriter
evaluates `(= (ite ...) 4)` conditions inside other ites, which a table over
independent leaves does not see. Tests:
`test_rewrite_reshaping_ite_terms_verifies` (both cores),
`test_rewrite_reshaping_ites_with_iff_and_xor_conditions_verifies`,
`test_ite_value_tables_key_reshaped_ites_alike`, and
`test_wide_clock_shaped_flattening_rewrite_verifies` (16 clocks; grind
failed on it before) in `test_proof_to_lean_arith.py`.

### Normalized rewrites: one lemma per atom normalization (2026-10-29)

`_normalized_rewrite` proved each atom's normalization to its canonical
linear form by `grind` in a `have` of the rewrite theorem, so every call saw
the atoms and normalizations before it and all shared the theorem's
1,000,000 heartbeats; the legacy rewrite of a nested conjunction of 1,100
bounds ran out of heartbeats about 200 atoms in. Each normalization is now a
private lemma `normalized_atom_N_A` with its own 1,000,000 heartbeats,
applied by the rewrite's `have`s. That certificate now verifies in 16 s of
Lean, and a 200-atom one drops from 38 s to 15 s. Test: the legacy case of
`test_proof_to_lean_deep.py`, now checked by Lean (it was reconstructed
only).

### Deep nesting: formula walks and the prover on explicit stacks (2026-10-29)

Inputs nested deeper than Python's recursion limit (1000) failed with
RecursionError instead of being certified or rejected. z3test's QF_IDL
`FISCHER6-4-ninc` (a CVC Lite translation) asserts `(and a (and b ...))`
nested a thousand levels, and the clause-log export crashed in the
assumption sources (`_conjuncts`) and then in the canonical keys
(`_Normalizer._key`); the QF_LRA `tta_startup/simple_startup_11nodes` and
`_15nodes` certificates failed in `reconstruct`, where the propositional
prover's search for a cnf lemma went through a thousand nested case splits.
These walks, and `_boolean_structure`, the prover's structure index, the
normalized rewrite's structure and `_render_structure`, now keep their own
stacks; outputs are byte-identical on 322 generated certificates of both
cores. Lean checks a thousand nested case splits (bullets) in a second, so
the prover's search is not capped. The prover also no longer rebuilds the
projections of a true conjunction's operands that are already true (cubic
in the width: two minutes for a legacy rewrite over 1,200 operands, one
second now). The three inputs now export and reconstruct; the tta inputs
do not verify yet: their cnf lemma is not propositional and its grind
fallback times out. FISCHER's export then took 459 s for 12,207
solver equivalence checks of `assume`; it verifies since the equivalence
search note above. Tests: `test_proof_to_lean_deep.py` (1,100 levels; the
clause-log certificates of a Boolean and an LRA conjunction checked by
Lean, a 1,100-split proof checked by Lean, the legacy normalized rewrite
reconstructed; checked by Lean since the per-atom lemmas above).

### Native euf and tseitin checks over Boolean constants and arguments (2026-10-28)

Z3's own replay (`z3 -smt2 log`, the `smt-clause-log` matrix cells) sent
two kinds of steps to its SMT fallback (`verified-smt`). The euf checker
(`eq_theory_checker`) merges the atom of a literal `(not q)` with false but
gives the term `(not q)` no class, so congruence `(pb (not q)) = (pb true)`
was "not congruent"; congruence now also equates Boolean arguments whose
truth values are known, reading `not` through. The tseitin checker matched
gate clauses literal by literal, so a gate over a constant (Z3 writes
`(not (= true b))`, b, false, with false standing for `(not true)`), an
`or` gate with a `true` disjunct, `(= (ite c a a) a)`, and clauses with
complementary literals or a constantly true literal were missed; the checker
now gives the constants their fixed values and accepts those tautologies.
Over 692 unsat logs of the UF-family random generators (seeds 1..300 of
eight generators of the Lean suites) the native replay went from 28 euf and
700 tseitin fallbacks (165 logs) to none; the remaining fallbacks there are
arithmetic (`cut`, `arith`). The Python replay and Lean checked these steps
already, so certificates are unchanged. Tests: `tst_checker_tseitin_constants`,
`tst_checker_euf_negated_arguments`, `tst_replay_boolean_constants_and_arguments`
in `src/test/proof_replay.cpp`, and
`test_native_checker_verifies_boolean_arguments_and_constant_gates` in
`test_proof_certificate.py` (real Z3 logs, all fail on the previous build).

### Trimmer: negated Boolean arguments (2026-10-28)

A Boolean term under an uninterpreted function, x = `(not q)` in
`(pb (not q))`, is a solver variable of its own, and the clause log prints
its literals as `(not q)` and `(not (not q))`, the same text as q negated
and q. The native trimmer (`proof_trim::add_literal` in `proof_cmds.cpp`)
stripped one negation per literal, so `(not (not q))` became a variable
unrelated to q: a conflict through it was missed, and the trimmer rejected
the log ("the empty clause is not derivable", or "the inferred clause ...
is not derivable" for a `rup` step through it), so the export replayed the
untrimmed log. Over seeds 1..2500 of `random_bool_argument_instance` and
1..300 of `random_boolean_predicate_instance` (615 unsat logs), 9 fell back,
three of them in the Lean suite; now none does. The trimmer strips every
negation, as the Python replay (`_strip`) always did; it only selects steps,
and the replay checks every retained one. Tests: `tst_trim_double_negation`
in `src/test/proof_replay.cpp`, `test_native_trimming_strips_every_negation`
in `test_proof_certificate.py` (both fail on the previous build), and in
`test_proof_to_lean_uf.py` the Boolean-argument and Boolean-predicate Lean
tests run with warnings as errors, so they check trimmed certificates, plus
an export-only test over the other six seeds. A clause can now repeat a
literal, `(not (not q)) q a` is q q a; `sat::proof_trim` stored it without
the repeat but looked up its deletion with it, so the deletion was ignored.
Deletions are normalized like additions now
(`tst_trim_deletes_clauses_with_repeated_literals`).

### Clause logs trimmed from 4 KB; Lean memory capped (2026-10-27)

Clause logs were trimmed natively only from 1 MB up, so most real inputs
replayed their whole search. Measured on z3test's `smtlib-sample`, trimming
shrinks every log tried, whatever its size: `QF_UF_cambridge.3.prop1_ab_reg_max`
(695 KB log) goes from 20,656 reachable proof steps, a 17 MB Lean file, and
68 s of export plus Lean to 458 steps, 1.9 MB, and 6.4 s;
`QF_UF_train-gate.6.prop1_ab_reg_max` (32 KB) from 711 KB of Lean to 120 KB;
the QF_LIA `ring_2exp4_5vars_0ite_unsat` (13 KB) from a 4.7 s export to
0.2 s; QF_LRA `Carpark2-t1-2` and `current_frame.base` export two to four
times faster. `_TRIM_THRESHOLD` is now 4,096 characters, below which a log holds a
few dozen commands. The trust boundary is unchanged: the trimmer only selects
steps, the replay checks each retained one, and a failed or unusable trim
still falls back to the untrimmed log with a warning. Every `lean` process of
`scripts/check_lean.sh` and of the library build now runs with
`--memory=8192`, so a runaway proof fails with "excessive memory consumption
detected" instead of exhausting the machine. Tests: `test_proof_certificate.py`
(`test_logs_of_a_few_kilobytes_are_trimmed`), `test_proof_to_lean_uf.py`
(`test_moderate_logs_are_trimmed_by_default`, on the train-gate benchmark in
`examples/python/data`), `scripts/tests/test_check_lean.py`.

More logs now reach the trimmer, and with them three open trimmer bugs, each
handled by the untrimmed fallback (a `RuntimeWarning`, one wasted run):
(1) it crashes (SIGSEGV or SIGBUS, never any output) on any `arith`-hinted
inference over `div`/`mod` by a constant; the minimal input is the first ten
lines of the log of `test_proof_to_lean_lia.random_division_instance(24)`,
ending in `(infer $137 $139)` with `$137 = (= (+ (* (- 3) (div x2 (- 3)))
(mod x2 (- 3))) x2)`, and 58 of the seeds 1 to 59 crash; (2) for
`random_instance(1, 10, 30, ite=True)` it prints only the empty clause, as
`(deps 172 172)`, likely `add_core(null, NONE)` in `proof_trim::trim`
finding the empty clause's own entry; (3) the log of one input of the Lean suite is rejected
("the inferred clause 47 -59 is not derivable by unit propagation"). All three need C++ fixes in
`src/sat/sat_proof_trim.cpp`, each with a `src/test` regression. (1) and (2)
are fixed, see "Trimmer: watches over false literals, empty assumptions,
hints without a checker (2026-10-27)"; (3) is still open.

### Trimmed QF_UF logs; assumption search by shared symbols (2026-10-27)

A first end-to-end pass over z3test's `smtlib-sample` QF_UF files found two
export costs on inputs that verify. (1) The native trimmer prints the input's
`(declare-sort U 0)` ahead of the declarations, and the dependency core
(`_dependency_core`) accepted only `declare-fun`, so every trimmed QF_UF log
was "unusable" and the replay fell back to the untrimmed log (the open
`NEQ004_size4` item of the scaling survey). The core now keeps sort
declarations: `NEQ004_size4` exports in 3.6 s instead of 19.7 s (16,643
resolution steps instead of 47,038) and checks in 40 s of Lean instead of
81 s. (2) An assumed clause that matches no assertion by canonical key was
compared with every conjunct of every assertion, one solver per check, for
equivalence and then for implication; `QF_UF_cambridge.3.prop1_ab_reg_max`
with its log trimmed (1,876 assertions, 90 assumed clauses each implied by
one of them) ran 274,092 checks and spent 90 s building a 460-step
certificate. The search now checks only the conjuncts that share an
uninterpreted symbol with the clause, plus the symbol-free ones
(`_candidate_sources`); a satisfiable conjunct and a non-valid clause without
a shared symbol cannot be related, and anything the search misses still
reaches the unsat-core fallback. Inputs with at most 64 conjuncts
(`_SEARCH_ALL_SOURCES`) are still searched whole, since indexing traverses
every assertion (a second on the BubbleSort circuit, whose 27 conjuncts all
share symbols with its one clause). The index keeps one symbol set per
conjunct, computed by one DAG traversal, not one per subterm: per-subterm
sets are quadratic on a deep ite chain over distinct atoms (5.5 GB at depth
16,000, now 194 MB). The cambridge build takes 1 s (941 checks) with the
same certificate. Nothing is trusted either way: the replay checks each step
and Lean each lemma. Tests: `test_proof_certificate.py`
(`test_dependency_core_keeps_sort_declarations`,
`test_assumption_search_checks_only_conjuncts_sharing_a_symbol`,
`test_assumption_search_index_is_linear_on_deep_terms`),
`test_proof_to_lean_uf.py` (`test_trimmed_logs_over_a_declared_sort_verify`:
a trimmed diamond through Lean with warnings as errors).

### SMT fallback proves the logged clause (2026-10-20)

When a native checker rejected a hint, `smt_proof_checker::infer` built the
fallback verification condition from the logged clause together with the
hint's clause (the default `theory_checker_plugin::vc` appended the hint's
clause to a vector already holding the logged one) and asked the solver to
refute the negation of both. Whenever the hint's clause is a theory
tautology its negation alone is unsatisfiable, so any logged clause passed
as `verified-smt`: a log with `(assume (not d))`, `(infer d (alldiff d
some_eq))` for `d = (distinct a b c)` accepted a refutation of the
satisfiable `(not (distinct a b c))`. Every plugin without its own `vc`
(all but quantifier instantiation) was affected, and the hole predates
the `alldiff` checker.

The fallback now refutes the negation of the logged clause alone under the
assumptions. A plugin's simplified condition (quantifier instantiation:
`phi(t) => psi` instead of the quantified premise, or no solver call when
`psi` is the instantiation itself) speaks for the hint's clause, so it is
used only when the logged clause follows from the hint's clause the way the
native path demands: every logged literal occurs there and the dropped
literals are false by RUP. `infer` returns whether the step verified and no
longer exits the process itself; the replay command and the in-solver check
still exit on a failed step, so the executable's behaviour is unchanged.
The `unit ... is not rup` diagnostic is buffered and printed only when the
step is rejected, since z3test's `proof_matrix.py` classifies any replay
whose output contains it as `checker-rejected`; before, a natively checked
hint whose dropped literal was not RUP printed it and then verified through
the fallback. The `proof_replay` unit test drives the checker directly: the
probe above is rejected with a countermodel, the same step with `some_eq`
assumed false verifies natively, a valid hint the plugin cannot check still
verifies through the fallback with a dropped RUP literal (and without any
`is not rup` line when the dropped literal is not RUP but the logged clause
holds on its own), and a logged clause outside the hint's clause is proved
on its own.

### One-argument `xor` (2026-10-21)

Z3's parser accepts `(xor p)` and its rewriter reads it as `p`
(`bool_rewriter`, `OP_XOR` with one argument; the legacy core records the
rewrite `(= (xor p) p)`), while n-ary `xor` is binarized, so one and two
are the only arities a certificate can carry. The reconstructor rejected
the unary node ("wrong number of arguments"), which kept z3test
`3434.smt2` (`(assert (xor false))`) out of both paths. `_validate_graph`
now admits the one-argument application, `_formula_body`,
`_boolean_connective`, and `_congruence_term` render it as its argument,
and `_gate_contradiction` proves its two gate clauses `(or (xor p) (not
p))` and `(or (not (xor p)) p)`; zero or three arguments stay rejected.
The clause-log exporter builds the application when a log mentions it
(`_unary_xor`; z3py's `Xor` is binary) and `ensure_gates` adds those two
clauses. Z3's simplifier removes the unary `xor` before logging, so live
logs assume the simplified clauses and the exporter ties them to the
assertions by `cnf` lemmas as before; the legacy path is axiom-free.
Tests: `test_proof_to_lean.py` (`UNARY_XOR`, the arity rejections,
`DEF_AXIOM_CLAUSES`, the gate polarity sweep, the structure expansion,
`CONFIGURED_INPUTS["3434"]` verbatim), `test_proof_certificate.py`
(`UNARY_XOR_GATES_LOG`, a constructed log keeping the literal, whose final
`rup` step needs the gates), `test_proof_to_lean_integration.py` (both
cores, the constructed log's def-axioms checked without axioms).

### `distinct` gate clauses as def-axioms, one-argument `distinct` (2026-10-21)

The clause-log exporter routed every `alldiff` clause through its `assume`
path. For the two gate clauses of a `distinct` below the root that path
found no matching assertion and fell back to an unsat core of the
assertions plus a `cnf` theory lemma, a bounded solver call at export time
and a `grind` lemma in Lean, for a clause that holds on its own. The
exporter now checks the gate shape (`proof_clause_log._distinct_gate`: two
literals of one polarity, a `distinct` over terms of at least two
arguments against a disjunction, or a single equality, whose disjuncts
each equate two of its arguments in either orientation, all pairs covered
for the positive clause) and makes such clauses def-axiom nodes; any other
`alldiff` clause still goes through the assertions. The reconstructor
proves the def-axiom from the pairs (`_distinct_gate_contradiction`): with
`d` and `some_eq` held, `Or.elim` over the disjuncts refutes each by the
pair's conjunct of `d` (through `Eq.symm` for a flipped disjunct); with
both denied, the conjuncts of `d` are built by injecting each pair's
equality into `some_eq`. A missing pair, a disjunct that is no pair, or
two polarities leave the clause unproved and rejected. Documented input
`uf_distinct_gates` (both cores), constructed-log and tampered-certificate
tests in `test_proof_certificate.py` and `test_proof_to_lean_uf.py`.

Found alongside: `(assert (not (distinct a)))` over an uninterpreted or
Real constant failed in Lean on both paths with `unfold failed to unfold
term_0`: a one-argument `distinct` renders as `True`, so its argument
occurs nowhere, but the lemma's unfold list and the theory flag were
computed from the graph. `_reachable` no longer descends into such a node
and `_boolean_structure` reads it as `("true",)`; the inputs
`UF_ONE_ARGUMENT_DISTINCT` verify through both cores.

### Native `alldiff` clauses (2026-10-20)

The native `alldiff` checker plugin accepted every hint ("first version
just trusts that distinct is internalized correctly"), so a clause log
could infer any clause natively under that label. Z3 emitted `alldiff`
for two different things: the clausification of a `distinct` asserted at
the root (the clause of all pairwise equalities for a negated root
`distinct`, unit disequalities for a positive one, and the fresh-symbol
encodings above 32 arguments), which follows from the asserted `distinct`
and not from the hint, and the two gate clauses of a `distinct` below the
root, `(or (not d) (not some_eq))` and `(or d some_eq)` with `some_eq`
the disjunction of the pairwise equalities, which are tautologies.

The root clauses are now logged as input clauses, like every other root
clausification (an `(assert (and a b))` logs `(assume a)` and
`(assume b)`), so the log no longer claims a theory inference for them;
the exporter already tied `alldiff` clauses to the original assertions
through its `assume` path, and that path is unchanged. The checker
verifies the gate pair: the two literals have one polarity, every pair of
arguments that can be equal has its equality among the disjuncts for the
positive clause, and every disjunct is an equality of two arguments for
the negated one. Anything else is rejected and falls to the SMT check,
which refutes the old root shape with a countermodel. The `proof_replay`
unit test covers the accepted and rejected shapes and replays a log with
both gate clauses natively.

### Native xor gate clauses (2026-10-19)

The native `tseitin` checker accepted invalid xor gate clauses. For a
positive gate literal it counted marked and complemented arguments with
one sign each and accepted an even total, so `(or (xor a b) a b)` and
`(or (xor a b) (not a) (not b))` verified. The former is false at
`a = b = false`, and the latter at `a = b = true`. Arguments the clause
left free were not counted at all. For a
negated gate it iterated the arguments of the `not` node instead of the
xor, so any clause whose deepest literal was `(not (xor ...))` verified,
for example `(or (not (xor a b)) (not a))`.

The checker now evaluates the xor under the assignment that falsifies the
other clause literals: every argument has to be fixed by a clause literal
or be a constant, and the xor must be true for a positive gate literal and
false for a negated one. Z3's own four clauses per gate still verify
natively, and a replayed xor log reports `+tseitin 4` without SMT
fallback. Z3's rewriter turns `xor` into a negated Boolean equality before
clausification, so the sat.smt log rarely carries these hints; the repair
is to the checker's acceptance, not to proof production or to Lean's
independent def-axiom checking. The `proof_replay` unit test also fails
now when the replay frontend exits inside a log instead of ending the
binary successfully with the remaining checks unrun.

## Arithmetic proof infrastructure

### is_int of nested Real chains related to its normal form (2026-11-09)

The rewriter's normal form of `(is_int t)` is `(= (to_real (to_int t'))
t')`, with `t'` the normal form of `t`: another node when `t` is a nested
Real ite chain. Only numeric arguments of uninterpreted applications got
`_r` equalities, so nothing related `t` and `t'`, and the grind lemma
relating the two formulas split both chains. `is_int` of two chains of
six nested Real ites failed on the clause log, compared directly (QF_LIRA,
grind failed after 47 s) or under a predicate `p` (QF_UFLIRA, 55 s). Now
`_real_argument_pairs` also groups the terms each reachable formula floors
(`_floored_terms`: an `is_int`'s argument, the arguments of the `to_int`
atoms of a comparison's sides), and `_real_argument_helpers` runs for any
arithmetic certificate with a `to_int` or `is_int`, not only for those
with uninterpreted symbols. The chains' equality is proved level by
level, and grind relates the formulas by congruence: 10 s and 7 s at
depth 6, 15 s at depth 8. The legacy core already passed and is mostly
unchanged. Tests: `test_is_int_of_nested_real_chains_is_related_to_its_normal_form`
(without Lean) and `test_is_int_of_nested_real_chains_verifies` (both
cores, Lean). `div`/`mod` by a numeral of nested Int chains (under `f` or
compared directly) already pass at depth 6 on both cores.

### Floors keyed by their argument's normal form (2026-11-09)

`to_int` atoms were keyed by node in `_real_atom_key`, so the floor of a
nested Real ite chain and the floor of the rewriter's normal form of that
chain (a different node) had different keys. No `_r` argument equality
related `(f (to_int a8))` and its rewritten form. The rewrite's grind
fallback ran out of heartbeats in `isDefEq` over the unfolded chains
(QF_UFLIRA, depth 8; depth 6 took 47 s and 3.7 GB). A `to_int` is now
keyed by its argument's key. Its level in `_argument_equality_levels` is
its argument's linear form, and two floors of one key get their own
equality, proved with only the two floors unfolded, by congruence from
the equality of the floored chains (which is stated first, level by
level). `_atom_bridge_facts` now also bridges such floors.
`cast_chains_instance(depth, "floor")`, clause log: depth 6 now takes 6 s
and 0.9 GB, depth 8 14 s and 1.3 GB, depth 10 40 s and 1.7 GB. The legacy
core relates the floors by `congrArg` and is unchanged (depth 8: 15 s).
Tests: `test_floors_of_nested_real_chains_are_related_level_by_level`
(without Lean) and the `floor` case of
`test_nested_ite_chains_verify_through_folded_facts` (both cores, Lean).

Keying a floor recurses into its argument, so keying a floor of a nested
chain took about 3^depth calls (as keying an ite argument already did),
and the keys themselves, nested tuples, grew as fast, with every
comparison, hash, and `repr` order paying for it. `_real_argument_key` and
`_real_atom_key` are now cached per graph, and the key of an ite, `abs`, or
`to_int` is interned (`_InternedKey`, compared by identity, ordered by a
short index), so keying is linear in the depth. `reconstruct` of
`cast_chains_instance(16, "floor")` went from over 120 s to 0.3 s, and of
`(= n (to_int a16))` against `(> n (+ (to_int a16) 1))` from over 300 s
to under 0.1 s. Outputs are byte-identical on 282 test inputs with an
ite, `abs`, or `to_int` (both cores). Test:
`test_keys_of_nested_chains_are_linear_in_depth` (without Lean).

### Cast, integrality, and Boolean-argument facts stated over folded definitions (2026-11-09)

The cast facts of a lemma reaching `to_real` or `to_int` (`_c`: an Int atom
transported into Rat; `_f`/`_u`: the floor bounds; `_r`/`_q`: a Real atom
over Int terms tied to an Int atom) and the excluded middles of Boolean
arguments of uninterpreted functions (`_b`) were still written out after the
lemma's unfold. Over nested ites every such fact repeats each inner ite in
full, as the ite gates did before 2026-11-08. They are now stated over the
term and formula definitions, folded, and reverted with the ite gates
before the lemma's one unfold, which rewrites them into the goal's terms
(the integrality fact is proved with its atom unfolded down to the Int terms
of its form). Certificates with arrays keep the written-out form, whose
terms the unfold leaves folded.

`cast_chains_instance(8, ...)` in `test_proof_to_lean_lira.py` compares two
chains of eight nested Int ites with one value (clause log):

| Compare | Fragment | Before | Now |
| --- | --- | --- | --- |
| casts against a Real `y` | QF_LIRA | 15.6 MB, fails (kernel memory, 218 s, 11.2 GB) | 0.92 MB, 20 s, 3.1 GB |
| Real `f` of the casts | QF_UFLIRA | 16.0 MB (not checked) | 0.89 MB, 9 s, 1.8 GB |
| Bool `p` of a bound on each | QF_UFLIA | 8.2 MB, fails (heartbeats, 168 s) | 0.94 MB, 10 s, 1.5 GB |

On the legacy core the QF_LIRA text goes from 23.9 MB to 1.6 MB (9 s).
Tests: `test_facts_over_nested_ites_are_stated_folded` (shapes, without
Lean) and `test_nested_ite_chains_verify_through_folded_facts` (both cores,
Lean). Still open: `to_int` of a Real chain under `f` (QF_UFLIRA, depth 8)
fails in a rewrite's grind fallback (heartbeats in `isDefEq`); the
rewriter's normal form of the floored chain needs an equality grind does not
find.

### Argument equalities proved level by level (2026-11-09)

The 2026-11-08 argument equalities (`_r` facts) were proved with both
arguments unfolded entirely. For two modular chains compared through `f`,
the theory tactic then splits every nested ite on both sides at once, and
at depth 8 (`real_modular_chains_instance(8, function=True)`, QF_UFLRA)
grind ran out of heartbeats in `isDefEq`, so the file failed.

The rewriter's normal form keeps the ites one by one, so two arguments
with one key (`_real_argument_key`) have corresponding nested ites with one
key each. `_argument_equality_levels` relates them bottom up: each pair of
corresponding ites gets its own `have _rA_B : term_A = term_B`, proved
with only its own level unfolded (its condition's sides and its branches
down to their linear atoms). The ites below stay folded, related by the
facts already proved. Every other atom of a level is the same node on both
sides and stays folded too; an `abs` keyed with an ite, and ites of one
key but different sorts (an Int ite under `to_real` against a Real ite),
are unfolded with the level, as before. The outer facts are then unfolded
in place as before, and the inner ones are cleared. (The mixed-sort case
still fails in Lean, before and after: grind does not push the cast
through the ite.)

| Input | Before | Now |
| --- | --- | --- |
| `real_modular_chains_instance(6, function=True)` | 30 s, 2.7 GB | 5 s, 0.85 GB |
| `real_modular_chains_instance(8, function=True)` | fails (heartbeats) | 11 s, 1.3 GB |
| `real_modular_chains_instance(10, function=True)` | fails (heartbeats) | 29 s, 2.0 GB |
| `modular_chains_instance(8, function=True)` (QF_UFLIA) | 19 s, 3.2 GB | 4 s, 1.3 GB |
| `modular_chains_instance(10, function=True)` | fails (heartbeats) | 13 s, 4.1 GB |

Tests: `test_argument_equalities_are_proved_level_by_level` (the shapes,
without Lean) and `test_nested_ite_arguments_verify_level_by_level` (the
Lean check) in `test_proof_to_lean_arith.py`, with
`test_argument_equalities_unfold_their_own_terms` and
`test_argument_equalities_unfold_ites_of_mixed_sorts`. Certificates with arrays
still state the equalities written out.

### Scaling facts and scaled gates stated over folded definitions (2026-11-09)

The Real counterpart of the modular chains,
`real_modular_chains_instance` (each step `(ite (< s 17/2) s (- s 17/2))`
over `s = previous + 5/2`), has fractional constants in its atoms and ite
branches. So its theory lemmas state the `_s` scaling facts
(`_scaling_helpers`) and the scaled `_g` gates (`_ite_gate_helpers`), which
the 2026-11-08 change below had left written out. They were 5.6 MB of the
5.9 MB of Lean text at depth 6 and almost all of the 44 MB at depth 8.

Without arrays, `_folded_ite_gates` now states them over the definitions as
well, and they are reverted, unfolded, and introduced with the integral
gates:

- a scaled gate is `formula_c -> (k * term_ite) = <scaled form over term_N
  atoms>`, proved by rewriting `term_ite` to its branch (`ite_eq_left` or
  `ite_eq_right`), unfolding the definitions from the branch down to the
  atoms of its linear form (`_linear_unfold`), and `grind`;
- a scaling fact is `formula_a -> <scaled form> R 0`, proved the same way
  from the atom.

The atoms, nested ites included, stay folded in these proofs, so grind
does not split them. An atom whose ite cancels (`5 + t = -7/2 + t`) keeps
`t` folded too.

| Input | Before | Now |
| --- | --- | --- |
| `real_modular_chains_instance(6)` | 5.9 MB, 69 s, 4.0 GB | 0.44 MB, 8 s, 1.3 GB |
| same, `function=True` (QF_UFLRA) | 4.6 MB, 43 s, 6.6 GB | 0.48 MB, 31 s, 2.8 GB |
| `real_modular_chains_instance(8)` | 44 MB, killed above 12 GB after 240 s | 0.93 MB, 17 s, 2.6 GB |

Tests in `test_proof_to_lean_arith.py`:
`test_scaled_gates_and_scaling_facts_are_stated_over_folded_definitions`
(the shapes, without Lean) and
`test_real_modular_chains_verify_through_folded_scaled_facts` (the Lean
check); for QF_LIRA, where a folded Int atom is cast to Rat,
`test_folded_scaled_facts_cast_int_atoms_to_rat` and
`test_folded_scaled_facts_over_int_casts_verify`. At depth 8 with
`function=True` the `_r` argument equality of the 2026-11-08 change below
ran out of heartbeats in grind, which was given the nested ites unfolded;
closed by the level-by-level proof above.

### Argument equalities stated over folded definitions (2026-11-08)

The ite gates were not the only written-out helper. Comparing the two
modular chains through a function, `(not (= (f a6) (f b3)))`, Z3's
rewriter replaces both arguments with their normal forms, and the rewrite
step's lemma states each argument equal to its normal form
(`_real_argument_helpers`, `have _rA_B : sA = sB`). Written out, the `a6`
equality was 106 KB of text, and its theory tactic ran out of heartbeats in
`isDefEq`, so the file failed.

Without arrays the equality is now stated over the two terms' definitions,
`(term_A ...) = (term_B ...)`. It is proved by unfolding the definitions
both terms reach and then running the theory tactic, with the same
hypotheses in context as before. The same `unfold ... at _rA_B` then
rewrites the fact into the goal's terms. Certificates with arrays keep the
written-out form, since their array terms stay folded.

`modular_chains_instance(6, function=True)` (QF_UFLIA) is 0.37 MB of Lean
instead of 0.48 MB, and it verifies in 5 s at 1.2 GB; before, it failed.
Tests in `test_proof_to_lean_uflia.py`:

- `test_argument_equalities_are_stated_over_folded_definitions`: the
  shape of the facts, without Lean.
- `test_nested_ite_arguments_verify_through_folded_equalities`: the Lean
  check.

### Ite gates stated over folded definitions (2026-11-08)

A rescan of z3test's `smtlib-sample` QF_UFLIA files of at most 160 KB
found three that no longer verify:
`mathsat/EufLaArithmetic/hard/hard16`, `hard17`, and `hard20`. The 2026-10-28
reconstruction fails the same way, so this is not a regression of the
generator. Earlier checks of these files ran without Lean's `--memory=8192`
limit; with the limit, all three stop with "(kernel) excessive memory
consumption".

The memory goes to info trees. The command-line frontend keeps every
command's info tree until the end of the file (`Language/Lean.lean` in Lean
4.34). Without the proof steps, hard16's definitions take 0.9 GB and its
leaf lemmas 6.8 GB. The leaf lemmas' proof terms account for only about 2.5
million expression objects; turning info trees off (a measurement only)
removed most of the lemmas' cost.

In 644 theory lemmas the largest elaborated text is the ite gates of
`_ite_gate_helpers`: `have`s stating `c -> ite c a b = a` with every term
written out. These files reduce modulo 17 through nested ites, and each
step holds the previous one three times, so the gates took 11 KB per lemma
and 7 MB in all.

`_folded_ite_gates` now states the integral gates over the definitions
(`formula_c -> term_ite = term_branch`, proved by `ite_eq_left`). It
reverts them before the fallback's `unfold`, so that one unfold rewrites
them into the goal's terms, and introduces them again. Scaled Real gates and
certificates with arrays keep the written-out form.

| Input | Before | Now |
| --- | --- | --- |
| hard16 | 20.1 MB, fails at 8 GB | 11.9 MB, 76 s, 4.5 GB |
| hard17 | 21.7 MB, fails at 8 GB | 12.9 MB, 86 s, 4.8 GB |
| hard20 | 27.4 MB, fails at 8 GB | 15.7 MB, 118 s, 6.0 GB |

The other 21 QF_UFLIA files verify, and `wisas/xs_17_37` is beyond the
120 s clause-log solver limit.

Tests in `test_proof_to_lean_lia.py`, on `modular_chains_instance(6)`
(two chains of modular additions compared): 0.3 MB of Lean and 4 s at
1.2 GB, against 4.9 MB, 13 s, and 2.8 GB before.

- `test_ite_gates_are_stated_over_folded_definitions`: the shape of the
  gates.
- `test_nested_ite_chains_verify_through_folded_gates`: the Lean check.

- `test_folded_ite_gates_are_reverted_unfolded_and_introduced` in
  `test_proof_to_lean.py`: on the depth-2 chains, without Lean, each lemma
  reverts its gates, unfolds every definition they name, and introduces
  them again. It also runs in the Python wheel job.

`scripts/ci_lean_proofs.sh` runs all `test_proof_to_lean*.py` modules with
Lean installed, so the Lean check above runs in CI.

### Farkas identities by linear normalization over balanced sums (2026-11-08)

A rescan of z3test's `smtlib-sample` QF_LIA files of at most 160 KB found
two regressions. `bofill-scheduling/SMT_random_LIA/ex11200_2600_100` and
`SMT_real_LIA/ex2360_2400_100` had verified in an earlier recheck but now
failed in Lean. Each has one Farkas lemma of about 200 bounds over more than
400 atoms, each bound spanning up to 20 atoms. Such a lemma now gets the
direct combination (see "Int Farkas lemmas proved by their combination"
below). Its identity, a right-nested sum proved by `omega`, took about five
million heartbeats, five times the lemma's budget. An exhausted budget is
not an error `first` catches, so the unfolded fallback never ran.

Two changes:

- `_combination_sum` nests the sum as a balanced tree.
- `_sum_identity` proves it by `first | (simp +arith only []; done) |
  omega`.

On the bofill lemma, `simp +arith` takes about 2 s. The cost of both
tactics is in the kernel check of their reflective proofs: on a synthetic
202-bound combination with a 300-atom row, 14 s for simp and 17 s for
omega. Results:

| Input | Before | Now |
| --- | --- | --- |
| ex11200 | heartbeat failure | 37 s, 3.5 GB |
| ex2360 | heartbeat failure | 42 s, 4.1 GB |
| `cut_lemma_02_002` (188 split identities) | 150 s | 69 s, 3.8 GB |

The rest of the scan is unchanged: every other file verifies or is out of
reach for z3 or the replay, except QF_LRA `tta_startup` 11 nodes (a known
failure, verified since 2026-11-11, see "Theory clauses for cnf lemmas over
rewritten ites").

Tests in `test_proof_to_lean_lia.py`:

- `test_farkas_combinations_of_many_wide_bounds_verify`: a 140-bound
  conflict over two partitions of 700 variables (`two_partitions_instance`)
  checks in about 9 s with the identity left to simp alone. Before, it ran
  out of heartbeats.
- `test_combinations_are_balanced_sums_proved_by_linear_normalization`: the
  sum's shape and the identity's tactic.

### Int and Real side by side: qf_lira (2026-11-02)

Input with both Int and Real variables was rejected ("mixing integer and
real arithmetic is not supported"), even when no term converts between the
sorts. Such input is now the `qf_lira` fragment (opt-in with the integer
ones, both cores): conversions stay rejected (`to_real` of anything but
numerals, `to_int`, `is_int`), and so do both sorts next to uninterpreted
functions. Every atom is over one sort and Z3 relates no atoms of the two
sorts in one arithmetic lemma. The statement takes two valuations,
`(_vars : Nat -> Rat) (_ivars : Nat -> Int)`; numerals, ite, abs, the
scaling and ite-branch helpers, and the normalized rewrites read the type
off their node, the atom keys round over Int atoms only, and each th-lemma
takes the Int or Real path by the sort of its atoms (`_lemma_numeric`, which
rejects a lemma over both). The clause-log reader values a numeral by its
spelling in such input (`2.0` Real, `2` Int). Found on the way, for every
fragment: once an assertion folds to false, Z3 logs the empty assumption and
then the remaining assertions unprocessed, Int numerals and `to_real`
coercions included, which made the reader fail on a QF_LRA input under
logic ALL ("definition $17 has sort Real, declared Int"); the reader now
gives a numeral the sort of its definition (an Int one under `to_real`,
`div`, `mod`, `rem`) and reads `to_real` of a numeral term as that term over
Real, as the input snapshot does (`_real_counterpart`). (Stopping the replay
at the empty assumption instead was tried and dropped: six reconstructor
tests rely on what Z3 logs after it, gate clauses and solver axioms.)
Tests: `test_proof_to_lean_lira.py` (four documented inputs with farkas, cut,
and arith hints and four `random_mixed_instance` seeds on both cores, the
encoding, label and sort tampering, a lemma over both sorts, the numeral
spelling), classification cases and the raw-tail replay in
`test_proof_certificate.py`. A sweep of the 15 unsatisfiable seeds in 1-60
(30 runs on both cores) verified in Lean. Not done: conversions
(`to_real` of Int terms, `to_int`, `is_int`), which need cast lemmas in Lean.

### to_real of Int terms in qf_lira (2026-11-02)

`to_real` of an Int term (a variable, a sum, an Int `ite`, `div`, `mod`,
`abs`) is now accepted in `qf_lira` on both cores; `to_int`, `is_int`, and
both sorts next to uninterpreted functions stay rejected. This also covers
the iter-055 case of an Int `ite` of numerals in a Real position under
logic ALL, `(to_real (ite p 1 2))`. Lean renders `to_real` as `Int.cast`
into `Rat`. A theory lemma reaching `to_real` mixes the sorts (for example
`x = n`, `(not (<= n 0))`, `x < 1`, which refutes only after the Int literal
is tightened to `n >= 1`). The exporter and the reconstructor check it as a
rational combination in which `(to_real t)` has `t`'s linear form and each
Int atom is tightened on its own. A cut may round only Int atoms and Real
atoms over Int terms alone, such as `(= (to_real n) (/ 9 4))`. Lean core
has `push_cast` and `Rat.intCast_le_intCast`/`_lt_`/`_inj`, but `grind`
does not reason through the cast. The fallback proof of such a lemma
therefore first states two kinds of facts, then runs `push_cast at *` and
`grind`:

- every Int atom is equivalent, in both polarities, to the tightened bound
  between the casts of its sides, through three private lemmas emitted once
  per file (`_int_cast_le`, `_int_cast_lt`, `_int_cast_eq`);
- every Real atom over Int terms alone is equivalent to the Int atom of its
  integer-scaled form.

Removing either kind of fact makes `grind` fail on a lemma that needs it.
The legacy core's congruence through `to_real` is `congrArg Int.cast`. The
legacy core's coefficient-free farkas lemmas over both sorts take the
lattice path, proved by Lean alone. A Real atom over Int terms alone is
tightened (scaled to integer coefficients, rounded to the lattice) before
it is keyed for normalized rewrites and ite tables, so it shares its key
with the equivalent Int atom. Tests: `test_proof_to_lean_lira.py`
(four documented `to_real` inputs with farkas, cut, bound, and arith hints,
four `random_cast_instance` seeds on both cores, the encoding, the cast and
integrality facts, invalid `to_real` declarations, and a cut over a Real
variable rejected by both checkers); classification and raw-tail cases in
`test_proof_certificate.py`. All 99 unsatisfiable `random_cast_instance`
seeds in 1-200 verify in Lean on both cores (198 runs, each at most about
1 s). Not done: `to_int` and `is_int`, and `to_real` next to uninterpreted
functions.

### to_int and is_int in qf_lira (2026-11-02)

`to_int` and `is_int` of linear Real terms are now accepted in `qf_lira` on
both cores. Lean renders `to_int t` as `Rat.floor t` (an opaque Int atom of
the linear forms, like `div`) and `is_int t` as
`((Rat.floor t : Int) : Rat) = t`, SMT-LIB's definition. A step reaching
either is a conversion step like one reaching `to_real`, and its fallback
proof also states, per floored term `a`, the core lemmas
`Rat.floor_le a` and `Rat.lt_floor_add_one a` (the two `arith` axioms Z3
adds for `to_int`), `floor a = D` through `Rat.floor_intCast` when `a` is
itself an integer `D` over Int terms (`(is_int (to_real n))`), and
`floor a = floor b + D` through `Rat.floor_add_intCast` for floored terms
differing by an integer `D` (Z3 rewrites `(is_int (+ x 1.0))` to
`(is_int x)`; these pairs only up to 12 floors per step). The clause log's
`arith` hints may carry `is_int` atoms (its definition axioms). A Real atom
over Int terms alone is now also cast back into Rat after its integrality
fact, so `(not (<= 3.0 (to_real (to_int x))))` bounds `x` by 2. The legacy
core's congruence through `to_int` and `is_int` is `congrArg`. Still
rejected: a cut rounding a Real atom over a Real variable (`x` and `x/2`
both integral gives `(= (* 0.5 x) (to_real (to_int (* 0.5 x))))`), by the
exporter ("cut hint over Real atoms") or the reconstructor; the legacy core
emits such lemmas as farkas steps that Lean then fails to prove. Tests:
`test_proof_to_lean_lira.py` (nine documented floor inputs, one of them
z3test `issue-1608.smt2`, and four
`random_floor_instance` seeds on both cores, the encoding, the floor and
shift facts, the `is_int` axioms, invalid declarations, and the rejected
cut). Of the 81 unsatisfiable `random_floor_instance` seeds in 1-200, 151
of 162 runs verify in Lean (each about 1 s); the other 11 are such
integrality cuts (eight clause-log rejections, three legacy Lean failures).

Update (2026-11-02, later): such integrality cuts through floors are now
certified on both cores. The exporter and the reconstructor accept a cut
when some literal reaches an Int atom (a floor counts; a cut over Real atoms
alone stays rejected), and a cut or coefficient-free farkas or bound of a
conversion step gets its projection onto the Int atoms
(`_projection_facts`): its constraints and floor bounds with every Real
atom eliminated exactly in Python (an equality by substitution, the rest by
Fourier-Motzkin), each projected constraint stated over Int through the
`_int_cast_*` lemmas (`x = 5` and `x/2` integral leave
`2 floor(x/2) - 5 = 0`; `x - 5/4` and `3x/2` integral leave
`8b - 12a - 15 = 0`), which grind's Int module refutes. All 162 runs of the
81 unsatisfiable seeds verify; without the facts six of the eight runs of
the new test inputs fail.

### Uninterpreted functions next to both sorts: qf_uflira (2026-11-03)

Input with uninterpreted sorts or functions next to both Int and Real
(a function `Int -> Real`, a predicate over both sorts, or `qf_uflia` and
`qf_uflra` symbols side by side) was rejected ("mixing integer and real
arithmetic with uninterpreted functions"). It is now the `qf_uflira`
fragment (opt-in with the integer ones, both cores), conversions included.
The statement takes both valuations of `qf_lira` next to `_m`, and the
`Interpretation` structure has both numeric pairs: `_m.int`/`_m.ifuns` and
`_m.real`/`_m.rfuns`, each argument injected and each result valued by the
fields of its own sort (`_Graph.injection(node)`,
`_Graph.numeric_functions(node)`). The one reconstructor change beyond the
encoding: `_lemma_numeric` no longer walks into the arguments of an
application (an atom of the linear forms), so a farkas lemma over `(f n)`
with `f : Int -> Real` is a Real lemma, and `_farkas_combination` checks
the hint before asking for the sort, so an `euf` congruence relating
`(= 3 n)` to `(= (f n) (f 3))` is not mistaken for an arithmetic step over
both sorts; a coefficient step over atoms of both sorts without a
conversion is still rejected. The argument-equality helpers
(`_real_argument_helpers`) group function arguments by sort as well as by
linear form: review found that an Int `(ite c 1 0)` and a Real
`(ite c 1.0 0.0)` got an ill-sorted `Int = Rat` helper that failed Lean.
Tests: `test_proof_to_lean_uflira.py` (five
documented inputs and five `random_uflira_instance` seeds, one with ite
arguments of both sorts, with farkas,
implied-eq, cut, bound, and euf hints on both cores, the encoding, label
tampering, the per-lemma sort, no helper across sorts), classification cases in
`test_proof_certificate.py`. Sweeps of `random_uflira_instance` (with and
without `to_real`, 2-3 variables of each sort, depth 2-3): all 392 runs on
both cores of 196 unsatisfiable seeds verified in Lean, plus hand probes
with `to_int` under a function argument, `is_int` next to a predicate, and
the floor of an application. With ite arguments (`ites=True`, seeds 1-300,
2/10/3) all 168 runs of 84 unsatisfiable seeds verify; 42 of them have Int
and Real arguments with one linear form, and three of those (105, 128, 279)
failed Lean before the per-sort grouping. Known gap, shared with
`qf_lira`: an Int ite whose condition compares Reals (or the reverse),
outside a function argument, makes its theory step "over both Int and Real
atoms", which is rejected.

Update (2026-11-06): that gap is closed. An arithmetic ite is an atom of the
linear forms, tied to its branches by gate clauses, so `_lemma_numeric` no
longer counts the atoms of its condition among the step's (the step takes
the ite's sort; a lemma whose own literals are over both sorts is still
rejected). The case also arises without an ite in the input: Z3's rewriter
turns a read of a store into `(Array Real Int)` into an Int ite over a Real
index equality. Tests: `lira_int_ite_over_real_condition` and
`lira_real_ite_over_int_condition` on both cores,
`int_read_of_a_store_at_real_indices`, `random_constant_array_instance`
seed 103 over Real indices and Int elements (seeds 1-300: 192 of 192
unsatisfiable seeds verify in Lean), and `random_mixed_instance` with
`ites=0.3` (ites over conditions of the other sort; seeds 1-150: 13 of 35
unsatisfiable seeds were rejected, now 70 of 70 runs on both cores verify;
three are pinned).

### Enumeration cases of applications stated over folded definitions (2026-11-10)

The `enum_fcases_j` instance a theory step states for each application of
an enumeration sort it reaches wrote the argument list out in full, so an
application over a nested ite chain repeated the chain. In an `euf` lemma,
whose ites stay folded in the goal, the written-out fact did not even meet
the goal's term. Without arrays the fact is now the field applied to the
argument list as the application's definition writes it, over the
arguments' definitions; it is stated before the lemma's unfold and
reverted with the ite gates, so the unfold rewrites it as it rewrites the
goal (`_folded_enumeration_cases`). Two eight-level chains of Color ites
through `f` and `g` (`enumeration_chain_instance(8)`): 27.2 MB of Lean
(26.7 MB of `euf` lemmas), which the 12 GB watchdog stopped after 288 s,
now 0.57 MB, checked in about a second; twelve levels 4.4 MB, 5 s, 2 GB.
Smaller inputs grow by up to 5% (the revert and intro lines). With arrays
the facts stay written out, like the other facts (`fold` in
`_grind_lemma`). Tests: `test_enumeration_cases_of_applications_are_stated_folded`,
`test_enumeration_ite_chains_verify` (`test_proof_to_lean_enum.py`).

### Enumeration datatypes through the clause log (2026-11-06)

Every `declare-datatype(s)` was rejected by the frontend. Enumerations
(all constructors nullary, not parametric) are now accepted as sorts of the
UF fragments, through the clause log only (the legacy core rejects them
explicitly; its datatype steps are not encoded); any other datatype, and an
array over an enumeration, is rejected. In Lean an enumeration joins the
carrier `_m.U`, its constructors are `_m.ctors k`, a recognizer
`((_ is c) t)` is `t = _m.ctors k`, and the `Interpretation` gains fields
read from the input's declarations: `enum_distinct` (constructors of one
enumeration differ) and, per constant or function of an enumeration sort,
`enum_cases_i` / `enum_fcases_j` (its value is one of the sort's
constructors, all of them, for every argument list). The clause log's
`datatype` hints become th-lemmas over enumeration equalities and
recognizers, proved by grind with those fields instantiated; the
reconstructor checks every constructor and recognizer against the input's
enumeration and interns constructors by name. This redoes fork PR #67
(iteration 67, never merged) on top of the array work. Three defects found
there and kept fixed: a root `distinct` with more arguments than the sort
has values had no certifiable proof (the `add_distinct_axiom` shortcut
logged an empty clause with an empty `tseitin` hint, which the exporter
rejects as not derivable by unit propagation, and on iteration 67's build
z3 crashed, exit 139, writing it; with proofs the pairwise clauses are now
added and the datatype solver refutes them); the replay's structural keys ignored
constructor names, so `(= x red)` and `(= x blue)` shared a key; and a
datatype hint may state an equality the other way around from its logged
clause, so the lemma is the logged clause. z3test
`regressions/smt2/t198.smt2` (recognizers) and the second query of
`z3.14.smt2` (the pigeonhole; the first is sat) now certify;
SMT-LIB 2.5's `is-c` recognizers (`OP_DT_RECOGNISER`) are written as
`(_ is c)` (`OP_DT_IS`). The pigeonhole search grows exponentially in the
constructors (with 32 arguments, 7 constructors log 8 MB in 0.7 s and 8
constructors 96 MB in 8 s), and the Lean check costs more than the search:
6 constructors and 7 arguments give 6.5 MB of Lean (18 s, 2 GB), 7 and 8
give 59 MB, which exhausts the kernel's 8 GB. Every clause over the
`distinct` unfolds all its pairwise disequalities, so the arguments count
too: with 5 constructors, 16 arguments check in 7 s (1.5 GB) and 32 exhaust
the kernel's memory; 4 constructors and 32 arguments take 76 s (4.3 GB).
So the exporter rejects a pigeonhole `distinct` (more arguments than
constructors) over more than five constructors or with more than sixteen
arguments; parametric datatypes
are rejected in both the 2.6 (`par`) and 2.5 (`(declare-datatypes (T) ...)`)
syntax. Follow-up: a counting lemma for the `distinct` shortcut. Tests:
`test_proof_to_lean_enum.py` (twelve documented inputs, z3.14, seven
`random_enum_instance` seeds, the encoding, constructor and recognizer
tampering, the pigeonhole and its bounds (a slow-tier check of the largest
accepted one), the keys, a dropped enumeration fact failing Lean).

### Native checks of the rem axioms (2026-10-31)

Z3's own replay of a clause log checked only the `rem` axiom whose guard
`(>= k 0)` is decided in its favour (the guard literal is valid); the other
one, `(= (rem t k) (mod t k))` for `k > 0` or `(= (rem t k) (- (mod t k)))`
for `k < 0`, went to the SMT fallback: 280 steps in the 37 unsatisfiable
logs of `random_remainder_instance` seeds 1 to 40. The `arith` checker's
`expand_definitions` now also replaces `(rem u k)` for a nonzero numeral `k`
by `s * (u - k * (div u k))`, `s` the sign of `k`, so both axioms verify
natively and those logs fall back on `cut` steps only (by design); the other
generators of the Lean suites are unchanged (cut only). `rem` bounds, zero or
term divisors are still rejected. Python and Lean already checked these
steps; certificates are unchanged. A fuzz of 1,500 near-miss `rem` clauses
accepted none that z3py found falsifiable. Tests: the rem cases of
`tst_checker_arith_axioms` and `tst_replay_arith_axioms` in
`src/test/proof_replay.cpp`, and the `lia_rem` input of
`test_native_checker_verifies_arithmetic_axioms`.

### Int rem by a numeral (2026-10-31)

`rem` is a Z3 extension, `(ite (>= k 0) (mod t k) (- (mod t k)))`, and every
input using it was rejected ("unsupported arithmetic operator: rem"). Z3's
rewriter turns `(rem t k)` by a numeral into `mod` or `-mod`, so most such
inputs never show `rem` in the proof, but a sum or product dividend keeps
it, and the arithmetic solver then adds two axioms per term (both cores):
`(or (not (>= k 0)) (= (rem t k) (mod t k)))` and
`(or (>= k 0) (= (rem t k) (- (mod t k))))`. Now the exporter accepts `rem`
by a nonzero numeral (`integer_divisor`, as for `div` and `mod`), the replay
rebuilds `(rem a b)` and keeps it an opaque atom of the linear forms, and the
axioms take the existing `arith` path (shape check in Python, proof in Lean).
The reconstructor declares `rem` in Int certificates only, rejects a zero or
term divisor on every stated node, and states `rem` at its numeral divisor:
`t % k` for `k > 0`, `-(t % k)` for `k < 0`; Lean proves the rewrite to
`mod` and both axioms. Tests: `lia_rem` among the documented QF_LIA inputs
(both cores, and the combination-only Farkas test),
`test_rem_is_stated_at_its_numeral_divisor` (rendering, the four axioms, and
tampering: renamed, wrong arity, term divisor, rem relabelled as mod, rem
in a Real certificate), `test_pinned_remainder_instances_verify_on_both_cores`
(three seeds of the new `random_remainder_instance`, with cuts and an
implied equality), and classification and rejection cases in
`test_proof_certificate.py`. A sweep of 93 unsatisfiable generator seeds
(186 runs on both cores) verified in Lean.

### abs over Real (2026-10-31)

SMT-LIB defines `abs` on Int only, but Z3 accepts it over Real with the
same definition, `(ite (>= t 0) t (- t))`, and its rewriter replaces it by
that ite before solving. Hand-written Real inputs use it for distances and
error bounds, and every one was rejected ("unsupported arithmetic operator:
abs over Real"), on both cores. The exporter now accepts it, and the
reconstructor accepts an `abs` declaration over Real (of the integer
operators, only `abs`; `div` and `mod` stay Int only) and states it as
`(@ite Rat (t >= 0) (Classical.propDecidable _) t (-t))`, the same ite it
already used for Int `abs`. The Rat encoding stays sound: like an ite, `abs`
is linear under each fixed sign of its argument. The rewrite bridges key
`(abs t)` as its ite (`_real_atom_key`), which already handled Real
conditions. Without a logic, `(abs 3)` in a Real position is
`(to_real (abs 3))`; the snapshot now reads it as the Real `abs` of `3.0`,
as QF_LRA does. `(to_real (abs n))` of an Int variable is still rejected. No
trimmed certificate in 450 random seeds kept an `arith` hint over `abs`
(the arithmetic solver's two case axioms, seen in untrimmed logs); such a
lemma is proved by grind as for Int. The replay rebuilds a logged `(abs t)`
as the `abs` application itself, the input's term; it used z3py's `Abs`,
which is `(ite (> t 0) t (- t))`, a different term.
`test_untrimmed_real_abs_axioms_verify` replays seed 59 under QF_LRA
untrimmed, keeping that lemma, through Lean. Tests:
`test_real_abs_verifies` and `..._through_the_legacy_core` (five
hand-written inputs, including the triangle inequality and a QF_UFLRA one,
plus four random seeds, with Lean and `#print axioms`; all 18 runs were
rejected before), `test_real_abs_is_stated_as_its_ite_over_rat`, and the
classification tests in `test_proof_certificate.py`.

### Integer numerals in Real terms (2026-10-30)

Without a `set-logic`, or under `ALL`, Z3 reads an integer numeral where a
Real is expected as an Int term under `to_real`, around the largest Int
subterm: `(* 2 x)` over a Real `x` is `(* (to_real 2) x)`, `(/ 1 3)` is
`(/ (to_real 1) (to_real 3))`, and `(- 5 1)` is `(to_real (- 5 1))`. The
exporter rejected every such input ("unsupported arithmetic operator:
to_real"), even `(assert (> x 1))`, although QF_LRA reads the same text
with Real numerals. The assertion snapshot (`_parse_snapshot`, shared by the
exporter's two cores and the reconstructor's binding to the input) now
replaces `(to_real t)` of a term built from numerals, sums, differences,
products, and negations by the same term over Real numerals, which is what
QF_LRA reads (SMT-LIB defines `to_real` as the injection of the integers
into the reals); the z3 executable folds the same coercions before logging.
An explicit `(to_real (+ 2 1))` is read the same way under any logic.
`to_real` of a variable, an application, `div`/`mod`/`abs`, or an Int `ite`
(`(ite p 1 2)` in a Real position is `(to_real (ite p 1 2))`, which the
clause log keeps over an Int `ite`) is still rejected. Tests:
`test_integer_numerals_coerced_to_real_read_as_under_qf_lra` (the snapshot
equals Z3's QF_LRA/QF_UFLRA reading), `test_coerced_numerals_are_bound_to_the_input_by_value`,
and three inputs through Lean on both cores
(`test_integer_numerals_in_real_terms_verify`,
`..._through_the_legacy_core`).

### Int cut lemmas proved by one split (2026-10-30)

A `cut`, and an Int `farkas` or `bound` without coefficients, names the
bounds it rests on but not the cut's derivation, so `omega` and `grind`
redid the search: QF_LIA `cut_lemmas/20-vars/cut_lemma_02_002` (188 such
lemmas over twenty variables) exhausted Lean's memory, single lemmas taking
over a minute or six gigabytes. Every Gomory cut is a split cut, so
`_split_combination` now proves such a lemma by one case split: z3, as an
untrusted oracle (`_split_certificate`), solves for an integer form `s`, an
integer `k`, and two sets of Farkas multipliers such that each side of
`k < s` or `s <= k` refutes the lemma's bounds rationally (a mixed integer
problem, the coefficients of `s` within [-1, 1] first, within
`_SPLIT_BOUNDED_RLIMIT`, then unbounded, within `_SPLIT_RLIMIT`); Python checks the combinations exactly, and Lean
checks `Int.lt_or_le` and each side as in `_farkas_combination` below. The
attempt comes first under `first`; a lemma without a certificate keeps the
generalized and unfolded proofs. All 188 lattice lemmas of
`cut_lemma_02_002` get a split within [-1, 1] (4 s of z3 in all). Its 25
Farkas lemmas of 20 and 21 bounds with coefficients below 10000 were as
costly through `omega`; a Farkas lemma of at least 16 bounds now gets its
combination when a bound spans 8 atoms or more (`_FARKAS_COMBINATION_ATOMS`;
the wide division seed's bounds span at most four). With serial elaboration
from 5 MB (`_SERIAL_ELABORATION_CHARS`, was 8 MB), the input verifies in
about 3 minutes at a 6.7 GB peak (`test_cut_lemmas_over_twenty_variables_verify`).
The splits also replace `grind`'s cutsat search on 126 of the 129 lattice
lemmas of the wide division seed, whose peak drops from 7.7 GB to 3.7 GB.
`test_lattice_lemmas_are_proved_by_their_split_alone` checks the splits of
the documented inputs (both cores) and pinned instances with no fallback.
Still open: the cut of `lia_gomory` has no split over its listed bounds (a
side needs the gcd rounding of a bound), so it keeps `grind`; each split
costs Lean about 26 MB, mostly the two `omega` identities over dense forms.

### Int Farkas lemmas proved by their combination (2026-10-30)

An Int `farkas` or `bound` th-lemma with coefficients was proved by `omega`
(or `grind`) with every bound in scope, so `omega` searched for the
combination the reconstructor had already re-derived. On QF_LIA
`cut_lemmas/20-vars/cut_lemma_03_012` (z3test smtlib-sample, 2.8 KB) two
21-literal lemmas over twenty variables with coefficients of seven and eight
digits ran for ten minutes each without an answer, so the 80 KB certificate
never checked. `_farkas_combination` now writes the proof directly: each
premise and each negated clause literal becomes `0 <= upper - lower` by a
core `Int` lemma (strict bounds tightened by one, equalities oriented by the
sign of their multiplier), the facts are scaled by integer multipliers (the
hint's coefficients for inequalities, solved for equalities) and summed by
`Int.add_nonneg`/`Int.mul_nonneg`, and `omega` checks only that the sum is a
negative constant, before any hypothesis is in scope. The attempt comes
first under `first`, ahead of the generalized and unfolded proofs, for
lemmas of at least 16 bounds (`_FARKAS_COMBINATION_BOUNDS`) with a
coefficient of magnitude at least 10000 (`_FARKAS_COMBINATION_COEFFICIENT`):
on the others omega is quick and its proof cheaper (the combination cost
Lean about 3 MB per lemma against 1 MB; the 800 mostly two-literal Farkas
lemmas of the wide division seed would have pushed it past the 8 GB cap,
and even its 59 lemmas of 16 to 26 bounds, coefficients at most 780,
raised its peak by 0.2 GB to within 0.3 GB of the cap). A combination that
needs a bound step's rounding gets no attempt. The input now verifies in
1.4 s. Every such lemma of the documented QF_LIA and
QF_UFLIA inputs through both cores is proved by the combination alone
(`test_farkas_lemmas_are_proved_by_their_combination_alone`,
`test_wide_farkas_conflicts_with_large_coefficients_verify` in
`test_proof_to_lean_lia.py`). Still open: Real Farkas lemmas keep `grind`,
and `cut_lemma_02_002` of the same family still exhausts Lean's memory on its
186 coefficient-free `cut` lemmas (verified since, see above).

### Native checks of the arithmetic solver's axioms (2026-10-29)

Clauses the sat.smt arithmetic solver adds without a hint of their own
(`arith_axioms.cpp`) reach the log with a bare `arith` hint listing the
negated clause literals, and Z3's own replay had no checker for that name:
every one went to the SMT fallback (5,213 steps in 164 of 452 unsat logs of
the LRA/LIA/UFLRA random generators, all from `random_division_instance`
and its variant with functions, plus 18 in the UFLRA logs of the iter-043
scan). The arithmetic checker now registers `arith` and accepts a clause when
one literal is valid by linear arithmetic once `(mod u k)` is replaced by
`u - k * (div u k)` and `(/ u k)` by `u / k` for nonzero numerals k, or by
the bounds `0 <= (mod u k) <= |k| - 1`, or when the clause is one of the two
`abs` cases, `(abs u) = u` or `(abs u) = -u` with the case condition implied
by the negation of the other literal. A leading `true` stands for the false
`q = 0` literal of `q * (p / q) = p` that the logged clause omits; the
checker's `clause` drops it, so the trimmer keeps the logged clause. Anything
else under `arith` (to_int, powers, nonlinear divisors) still falls back
(`rem`: see 2026-10-31).
After the change the same logs have no `arith` fallback (only the `cut`
steps, by design), and a soundness fuzz of 3,000 random near-miss clauses
found no accepted invalid one. The Python replay and Lean checked these
steps already, so certificates are unchanged. Tests:
`tst_checker_arith_axioms`, `tst_replay_arith_axioms` in
`src/test/proof_replay.cpp`, and
`test_native_checker_verifies_arithmetic_axioms` in
`test_proof_certificate.py` (all three inputs fail on the previous build).

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

### Trimmer: watches over false literals, empty assumptions, hints without a checker (2026-10-27)

Since trimming starts at 4 KB, three trimmer bugs sent many logs back to the
untrimmed replay. Over 40 seeds of each random generator of the Lean suites
(clause log of each instance, then `trim_clause_log`), 43 of 133 logs
above 4 KB fell back; after the fixes none does.
(1) At base level the SAT solver watches a clause's first two literals as
given, and `proof_trim::assume` passed them in sorted order. A clause whose
first two literals were already false never propagated, so the trimmer missed
the conflict. The empty clause then went in as a fresh conflict, with no
clause behind it, and its core was the empty clause depending on itself
(`(deps 172 172)`, rejected as "cyclic clause dependencies"; 12 QF_LRA and
QF_LIA logs). The trimmer now watches the clause's non-false literals.
(2) An assertion that preprocessing reduces to false is logged as an empty
assumption, `(assume)`. The trimmer kept "no conflict yet" as an empty
conflict clause, so it took this conflict for none, went on adding clauses to
an inconsistent solver, and again wrote a self-dependent empty clause (12
QF_UF and QF_UFLIA logs with `ite`, and 8 QF_LIA division logs once (3) was
fixed). The conflict is a flag now, and an assumed empty clause sets it; the
inferred empty clause depends on the assumed one. An inferred empty clause
that arrives without a conflict is checked by propagating the whole trail
again; if that finds none either, `trim()` rejects the log ("the empty
clause is not derivable by unit propagation") instead of writing a cycle.
An empty clause inferred under a theory hint is assumed like any theory
axiom; when it is the first conflict, the trimmer cannot know its premises,
and `trim()` rejects the log ("the empty clause is a theory axiom whose
premises are unknown") rather than make it depend on itself. An assumed
empty clause after the conflict is left out of the core.
(3) Z3 logs div/mod axioms under a bare `arith` hint, for which
`euf::theory_checker` has no plugin. The trimmer (`proof_cmds.cpp`) looked up
the hint's clause anyway, read through a missing map entry, and crashed with
SIGBUS or SIGSEGV and no output (19 of 19 division logs). A hint without a
plugin (`theory_checker::has_rule`) is now treated as a theory axiom over its
logged clause, like any other.
The trust boundary is unchanged: the replay checks every retained step.
Tests: `src/test/proof_replay.cpp` (`tst_trim_watches_literals_that_are_not_false`:
the missed conflict, the rejected underivable empty clause, the assumed empty
clause; `tst_trim_assumed_empty_clauses`: the rejected theory-axiom empty
clause, the assumed empty clause after a conflict) and `test_proof_certificate.py` (one test per bug through the z3
executable's trimmer with warnings as errors, then the core replayed; all
three fail on the previous build). Four Lean-suite tests had been checking
untrimmed certificates through these fallbacks: the wide division seeds of
`test_proof_to_lean_lia.py` and `test_proof_to_lean_uflia.py` (their trimmed
cores leave out the Farkas lemmas the tests are about) and the wide
conjunction of `test_proof_to_lean_wide.py` (trimmed, its core is the
assumed empty clause). They now export the untrimmed log explicitly; the
conjunction test checks the trimmed default in Lean as well. Three
fallbacks remain in the Lean suite, now as explicit errors: the "inferred
clause ... not derivable" of a Boolean-predicate input, and two
`random_bool_argument_instance` seeds whose final empty clause is not
derivable over the clauses the trimmer assumes. All three are fixed: see
"Trimmer: negated Boolean arguments (2026-10-28)".

### Trimmer: deletions of clauses it never added (2026-10-23)

The clause-log export of z3test's QF_LRA `LassoRanker/SV-COMP/
HarrisLalNoriRajamani-2010SAS-Fig1_true-termination.c_Iteration1_Lasso_4-
pieceTemplate.smt2` (141,681 log lines, 114,408 clause additions) failed
native trimming with "the clause ... used by the proof was never added" and,
since 2026-10-22, fell back to replaying the untrimmed log: 240 s of export
and 29 MB of Lean text that does not check in time. The trimmer's own unit
propagation finds the conflict as soon as the clause set is inconsistent,
here about 3,000 additions before the solver logs its empty clause; it
ignores the clauses added in between but recorded their deletions, and the
backward pass "revived" each such clause by adding it to the solver, where it
took part in the probes. A core that chased a literal such a clause implied
referred to a clause registered nowhere, hence the error. A deletion logged
before the conflict for a clause the trimmer never added (a theory lemma Z3
deletes under its logged literals while the trimmer assumed the checker's
clause, `proof_cmds.cpp`) revived one the same way.

Now `proof_trim::del` ignores every deletion after the conflict (nothing
after it changes the state the conflict was derived in) and records a
deletion only when the solver held a copy of the clause (`detach`: a
registered clause object, an attached binary watch; a unit's assignment is
never withdrawn, so its deletion is a no-op). The LassoRanker log trims to
62,659 retained steps and exports again. Tests: `src/test/proof_replay.cpp`
(`tst_trim_ignores_deletions_of_clauses_never_added`, both placements, which
the previous trimmer fails with the exact error) and `test_proof_certificate.py`
(the same log through the z3 executable's trimmer with warnings as errors,
the ignored resolvent absent from the core, the core replayed).

### Trimmer: implied literals of duplicate clauses, explicit failure (2026-10-22)

The clause-log exports of z3test's QF_UFLIA
`mathsat/EufLaArithmetic/hard/hard16.smt2` and `hard20.smt2` were rejected
with "inferred clause is not derivable by unit propagation" although the
untrimmed logs replay. The native proof trimmer (`src/sat/sat_proof_trim.cpp`,
see "Real QF_LRA hardening" below for its earlier defect) walks the log
backwards and, before removing a clause, unassigns the literal it implied and
that literal's cone of influence; it took any true literal of the clause as
implied by it. Z3 logs the same binary theory lemma several times (five
copies of one clause in hard16), and the copies share one justification, so
removing the last copy unassigned the literal although earlier copies
remained, and with it every fact derived from it. Facts whose own clause the
log had deleted in the meantime (and units asserted after a clause already
implied them) have no watch to re-derive them, so the probe of a later `rup`
step found no conflict; the trimmer then read the stale conflict state and
reported arbitrary, incomplete dependencies, which the exporter rejected.

Now `prune_trail` unassigns only the literal whose justification is the
clause itself (by clause object, or for a binary clause only when it is the
last attached copy, or for a unit when the literal has no other reason); a
probe that finds no conflict raises an error instead of emitting a core (the
trimmer's output is untrusted, but a core the replay cannot use is a
rejection of an input Z3 solved); a probe on a clause a level-0 fact already
satisfies depends on that fact's justification alone (the solver's conflict
carries no clause there, which used to read a non-existent unit clause); and
a clause the core refers to but was never added is an internal error rather
than undefined behaviour. The copies of a binary clause are told apart only
by counting attached watches, so a log that deletes a binary clause
(`big::reduce_tr` logs such deletions during in-processing) and later adds
it again can still lose a fact; that case ends in the explicit error and the
untrimmed replay, not in a wrong core.

On the Python side `trim_clause_log` treats a failed or unusable trimming as
what it is, an optimization that did not apply: it warns and returns the
untrimmed log, which the replay checks step by step. hard16 (10,689 steps
before, 3,292 in the core) verifies in 40 s of Lean and hard20 (4,624 in the
core) in 57 s, both axiom-free apart from the standard three. Tests:
`src/test/proof_replay.cpp` (`tst_trim_duplicate_binary_keeps_implied_
literal`, which the previous trimmer fails, and
`tst_trim_rejects_underivable_inference`), `test_proof_certificate.py`
(the same log through the z3 executable's trimmer with warnings as errors,
and the fallback for a failing trimmer, a rejected inference, and a cyclic
core).

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
