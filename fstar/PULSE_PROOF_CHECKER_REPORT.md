# Pulse-verified proof checker

## Goal

Everything in this directory up to this point formalizes proof-term
and proof-rule soundness as **pure, non-executable (or at best
"accidentally" executable) F\* propositions/lemmas**: `fact`/`facts_of`
in [`Z3ProofTheory.fst`](Z3ProofTheory.fst) are ordinary recursive F\*
functions, and the rule families in
[`Z3ProofJustifications.fst`](Z3ProofJustifications.fst) /
[`Z3PreprocessingProofTheory.fst`](Z3PreprocessingProofTheory.fst) are
libraries of `Lemma`s about structural recognizers, not a checker one
could actually run as a trusted imperative component (e.g. as a
drop-in, independently-verified replacement for part of
`src/ast/proofs/proof_checker.cpp`, which does maintain explicit
mutable state — a worklist/cache of already-checked sub-proofs).

This follow-up asks: can the *same* specifications be re-proven correct
against a genuinely **imperative, stateful** implementation, written in
[Pulse](https://github.com/FStarLang/pulse) (F\*'s separation-logic
verified-imperative-programming DSL, bundled with the F\* toolchain
used throughout this project)? This is a strictly stronger claim than
"the pure recursive function has the right type" — Pulse's program
logic must independently verify every heap read/write and every loop
of control flow against the same pre/postconditions, giving an
actual, checkable (in principle, extractable-to-OCaml/C) decision
procedure, not just a specification.

## Architecture

Two new Pulse modules, each following the same pattern: **a pure
specification (already proven in a prior audit) is decided by a
genuinely imperative Pulse `fn`, proven to compute exactly that
specification while legitimately mutating a heap-allocated step
counter.** The counter has no bearing on soundness — it exists
specifically to force every Pulse function in this file to be a true
stateful program (not a disguised pure function), and its exact final
value is itself part of what's proven, as an extra sanity check that
the imperative implementation visits precisely the nodes the
recursion scheme says it should.

### `Z3PulseProofChecker.fst` — the rewriter-calculus checker (centerpiece)

Ports `Z3ProofTheory.fst`'s `fact : proof -> option (expr & expr)` /
`facts_of : list proof -> list (option (expr & expr))` — the checker
for the `Refl`/`Sym`/`Trans`/`Congr`/`Rewrite`/`QuantIntro` proof-term
calculus modeling `rewriter_def.h`'s `PR_REFLEXIVITY`/`PR_SYMMETRY`/
`PR_TRANSITIVITY`/`PR_MONOTONICITY`/`PR_REWRITE`/(`PR_BIND`+
`PR_QUANT_INTRO`) shapes.

* **`proof_or_list`**: a sum type (`PNode : proof -> proof_or_list |
  PList : list proof -> proof_or_list`) merging `fact`'s and
  `facts_of`'s recursion into one. Pulse's `fn rec` does not support
  F\*-style `and`-chained mutual recursion (confirmed empirically — see
  "Pulse lessons" below); this is the standard encoding trick to
  reduce mutual recursion to ordinary self-recursion.
* **`combined_size`**: the single `decreases` measure over
  `proof_or_list`, reusing `Z3ProofTheory.fst`'s pre-existing
  `proof_size`/`proof_list_size` unchanged (they already follow the
  "+1 per node, including +1 per list-cons cell" convention a
  single merged measure needs).
* **`check_either (x:proof_or_list) (ctr:ref int)`**: the core `fn
  rec`, one match arm per `proof` constructor plus the `PList`
  cons/nil cases, each incrementing `ctr` by exactly 1 and recursing
  on strictly smaller sub-structure. Its Pulse postcondition states
  both `pts_to ctr ('n + combined_size x)` (the counter advanced by
  exactly the size) and `result_matches x r` (the returned tagged
  result corresponds, constructor-by-constructor, to `fact`/`facts_of`
  applied to the unwrapped input) — i.e., Pulse's own program logic,
  not merely F\*'s type system, proves every heap mutation and control
  branch is exactly right.
* **`check_proof`, `check_proof_list`**: thin wrappers specializing
  back to the natural `proof`/`list proof` interface (hiding the
  sum-type encoding from callers).
* **`checker_accepts (p:proof) : bool`**: a self-contained convenience
  entry point that allocates and frees its own counter internally.
* **`lemma_checker_sound`**: the end-to-end corollary — composes the
  Pulse-proved `o == fact p` equivalence with `Z3ProofTheory.fst`'s
  pre-existing `lemma_proof_sound`, i.e. *if* the Pulse checker's
  result is `Some (a, b)` and every `Rewrite` leaf in `p` is
  semantically sound (`all_leaves_sound`) and quantifiers denote
  extensionally (`quant_extensional`), *then* `a` and `b` evaluate
  identically under every environment, for real, by running the
  actual Pulse program, not merely by trusting a same-shaped pure
  function.

### `Z3PulseJustificationChecker.fst` — modus ponens / unit resolution

Decides the rule families formalized in `Z3ProofJustifications.fst`:

* **`decide_mp`/`check_modus_ponens`**: pure shape-dispatch (reusing
  `is_implies`/`is_eq_e`/`is_oeq_e`) wrapped in a Pulse shell; the
  corollary `lemma_decide_mp_sound` composes the three pre-existing
  `lemma_mp_implies_sound`/`lemma_mp_eq_sound`/`lemma_mp_oeq_sound`
  lemmas, covering all three antecedent shapes `PR_MODUS_PONENS`
  accepts.
* **`check_has_complement`**: genuine Pulse recursion over a literal
  list (no sum-type trick needed — no call cycle here), deliberately
  non-short-circuiting so its step count has the closed form
  `List.length negs`.
* **`resolve_residual_cost`/`check_resolve_residual`**: a Pulse port of
  `resolve_residual` (the residual-clause computation underlying
  `PR_UNIT_RESOLUTION`), with a custom cost measure for its own
  step-counter postcondition.
* **`lemma_check_resolve_residual_sound`/`lemma_check_singleton_sound`**:
  corollaries reusing `Z3ProofJustifications.fst`'s existing
  `lemma_resolve_residual_sound`/`lemma_unit_resolution_singleton_sound`
  lemmas unchanged.

### `Z3PulseProofCheckerTests.fst` — cross-theory exercise

Since `rewriter_def.h`'s proof-production machinery (and hence `fact`/
`facts_of`/`check_proof`) is shared verbatim by *every* theory
rewriter plugin, "test it on all theories" means: build sample proof
derivations whose `Rewrite` leaves are rewrite facts independently
established by this directory's own per-theory audits, and confirm
`check_proof`/`checker_accepts` accept the resulting proof trees (and
correctly reject ill-formed ones). Each leaf is treated the same way
`all_leaves_sound`'s own docstring treats them — as a trusted
input whose own semantic correctness is exactly what that theory's
separate `*_REWRITER_REPORT.md` establishes; this file is testing the
*calculus* layer (`Trans`/`Sym`/`Congr`/`QuantIntro` composition), not
re-deriving per-theory rewrite soundness.

Coverage, all proved both via the pure `fact p == expected` equality
and by literally running `check_proof`/`checker_accepts` and checking
their returned value and final counter reading:

| # | Theory | Leaf under test | Proof shape exercised |
|---|---|---|---|
| 1 | `bool_rewriter` | `not(not x) = x` | `Rewrite` leaf, then `Sym` |
| 2 | `arith_rewriter` | `(+ x 0) = x` | `Rewrite` leaf lifted through a unary application via `Congr` |
| 3 | `bv_rewriter` | `(bvand y y) = y` | bare `Rewrite` leaf |
| 4 | `seq_rewriter` + `bool_rewriter` + `arith_rewriter` (combined) | associativity of `++`, chained into unrelated bool/arith leaves | two-step `Trans` chaining leaves from three different theories in one derivation |
| 5 | non-linear arithmetic (`Z3NlArith.fst`) | an opaque NLA leaf (trusted the same way every other leaf is) | bare `Rewrite` leaf |
| 6 | `PR_BIND`+`PR_QUANT_INTRO` | the test-2 leaf, wrapped under `forall` | `QuantIntro` over a `Rewrite`-derived body |

Rejection tests (`fact` must return `None`, `checker_accepts` must
return `false`, proven of both): a `Trans` whose two middle terms
disagree; a `Congr` with mismatched argument-list lengths; a `Congr`
with matching lengths but a changed argument no supplied premise
justifies.

## What was verified, precisely

1. **Functional correspondence** (Pulse ⟺ pure spec): `check_either`'s
   Pulse postcondition `result_matches x r` is proven — by Pulse's
   program logic composing its separation-logic VCs with the
   underlying SMT discharge, not merely stated — to hold after every
   execution path through `check_either`, for `fact`/`facts_of` exactly
   as previously defined and already relied upon by every other report
   in this directory. No change was made to `Z3ProofTheory.fst`'s or
   `Z3ProofJustifications.fst`'s specifications to make this possible.
2. **Resource/step accounting**: the step counter's final value is
   proven equal to `proof_size p` / `proof_list_size ps` /
   `resolve_residual_cost lits negs` / `List.length negs` as
   applicable — i.e. the imperative implementation's control flow
   provably visits exactly the nodes the structural recursion scheme
   dictates, neither more nor fewer.
3. **End-to-end soundness, executed**: `lemma_checker_sound`,
   `lemma_decide_mp_sound`, `lemma_check_resolve_residual_sound`, and
   `lemma_check_singleton_sound` each show that an *actual Pulse
   program's* accept/reject verdict, when positive together with the
   same soundness side-conditions every prior report already requires
   (`all_leaves_sound`, `quant_extensional`, or the propositional
   antecedent-shape preconditions), implies the real semantic
   equality/implication the original rule asserts. This closes the gap
   between "the specification is sound" (already known) and "a
   concrete, heap-mutating decision procedure for that specification
   is sound" (new).
4. **Cross-theory exercise**: `Z3PulseProofCheckerTests.fst` runs the
   checker, for real, on sample derivations combining leaves from
   `bool_rewriter`, `arith_rewriter`, `bv_rewriter`, `seq_rewriter`,
   non-linear arithmetic, and quantifier introduction, plus three
   deliberately ill-formed proofs, confirming both acceptance and
   rejection match the pure specification in every case.

## Pulse lessons (for future Pulse work in this project)

* Pulse `fn rec` requires an explicit `decreases <expr>` clause (not
  inferred); it does not support F\*-style mutual recursion via
  `fn rec f ... and g ...` — merge mutually-recursive domains into one
  sum type and self-recurse on that, as done here for
  `proof_or_list`/`combined_size`.
* Pulse's `match` does not support nested/"deep" patterns (not even
  `Some (a, b)`); destructure one constructor level at a time, using
  `fst`/`snd` for tuples bound as a single variable.
* `if`/`else` needs brace syntax, and the condition should be
  parenthesized when immediately followed by `{` (otherwise it can be
  misparsed as record-update syntax).
* `Pulse.Lib.Core.unreachable()` discharges impossible branches when a
  `pure False` fact is derivable from context (e.g. a mismatched
  sum-type tag combination).
* `Pulse.Lib.Reference.alloc`/`free` are flagged `@@deprecated`
  ("unsound, only use for model implementations" — a warning, not an
  error); the "proper" alternative is the scoped, closure-based
  `with_local`. This project's self-contained convenience wrappers
  (`checker_accepts`, the test file's `run_one`) are exactly the kind
  of standalone/model usage that deprecation notice has in mind, and
  were left using `alloc`/`free` with a justifying comment rather than
  adopting the more complex `with_local` API.
* A plain top-level F\* `Lemma` can be invoked as an ordinary statement
  inside a Pulse `fn` body (confirmed via a disposable probe); its
  postcondition then becomes an ambient fact available to later
  `assert (pure ...)` goals in the same body, via the normal SMT
  discharge — this is how the test file supplies `fact p == expected`
  facts (established once, by F\*-level `Lemma`s, at the top level)
  into Pulse's separation-logic proof obligations.

## Scope and limitations

* **Not covered by a Pulse checker**: the rule families in
  `Z3PreprocessingProofTheory.fst` (`PR_COMMUTATIVITY`,
  `PR_QUANT_INTRO` over non-rewriter-calculus shapes, `PR_PUSH_QUANT`,
  `PR_IFF_TRUE`/`FALSE`/`OEQ`, `PR_AND_ELIM`, `PR_NOT_OR_ELIM`,
  `PR_MODUS_PONENS(_OEQ)` as formalized independently there). These
  remain pure-specification-only, as they were before this follow-up;
  the same "pure decision function + thin Pulse shell + corollary
  lemma" pattern used for `Z3PulseJustificationChecker.fst` would
  apply directly if extended in a future pass.
* **`PR_TH_LEMMA`, `PR_HYPER_RESOLVE`, `PR_QUANT_INST`, `PR_SKOLEMIZE`,
  `PR_DEF_AXIOM`, `PR_NNF_POS`/`NEG`** remain out of scope here exactly
  as they are in `PROOF_REWRITER_REPORT.md`/
  `PROOF_JUSTIFICATIONS_REPORT.md` — this follow-up adds an imperative
  implementation layer under the *existing* scope, it does not expand
  which proof rules have been formalized at all.
* **`alloc`/`free` deprecation**: accepted as a documented tradeoff for
  the self-contained convenience wrappers (see "Pulse lessons" above);
  not a soundness gap in the proved specifications themselves, since
  Pulse's separation-logic VCs for `pts_to`/ownership are still fully
  discharged around every `alloc`/`free` pair used.
* **No OCaml/C extraction was attempted** — this is a verified-model
  exercise within F\*/Pulse's own type checker, not a build-integration
  change to Z3's actual `proof_checker.cpp`; nothing in
  `src/ast/proofs/proof_checker.cpp` was modified.

## Files

| File | Role |
|---|---|
| [`Z3PulseProofChecker.fst`](Z3PulseProofChecker.fst) | Pulse port of `fact`/`facts_of` (the rewriter-calculus checker) |
| [`Z3PulseJustificationChecker.fst`](Z3PulseJustificationChecker.fst) | Pulse decision procedures for modus ponens / unit resolution |
| [`Z3PulseProofCheckerTests.fst`](Z3PulseProofCheckerTests.fst) | Cross-theory sample derivations, run through both checkers above, including rejection tests |

All three files type-check cleanly with the standard toolchain
invocation (`fstar.exe --smt <z3 4.13.3 binary> <File>.fst`), with zero
errors; remaining diagnostics are pre-existing unrelated warnings from
`Z3AstTheory.fst` plus the expected `alloc`/`free` deprecation
warnings discussed above.
