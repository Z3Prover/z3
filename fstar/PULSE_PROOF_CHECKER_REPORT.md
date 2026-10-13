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
  error). **Update**: this project no longer uses them. Pulse's
  surface sugar `let mut x = <init-expr>;` (confirmed against F\*'s own
  test suite, `pulse/test/bug-reports/Bug431.fst`) desugars to
  `with_local` (the non-deprecated, scoped-allocation primitive
  `alloc`/`free` are themselves implemented in terms of) and
  automatically reclaims the binding at the end of its enclosing
  scope — strictly simpler than calling `with_local` directly with an
  explicit closure, and with no deprecation warning. Every
  `checker_accepts`/`run_one`/`run_parsed`-style self-contained
  convenience wrapper in this project (`Z3PulseProofChecker.fst`,
  `Z3PulseProofCheckerTests.fst`, `Z3PulseLraCheckerTests.fst`,
  `Z3PulseLraCheckerParsed.fst`, and the `tools/extract_z3_proof.py`
  generator template) was converted from `let ctr =
  Pulse.Lib.Reference.alloc 0; ... Pulse.Lib.Reference.free ctr;` to
  `let mut ctr = 0;` with no corresponding `free` (the compiler inserts
  it), and all re-verify cleanly with zero `alloc`/`free` deprecation
  warnings.
* A plain top-level F\* `Lemma` can be invoked as an ordinary statement
  inside a Pulse `fn` body (confirmed via a disposable probe); its
  postcondition then becomes an ambient fact available to later
  `assert (pure ...)` goals in the same body, via the normal SMT
  discharge — this is how the test file supplies `fact p == expected`
  facts (established once, by F\*-level `Lemma`s, at the top level)
  into Pulse's separation-logic proof obligations.

## Follow-up: trusted leaves made concrete, and `Z3InterpretedProofChecker.fst`

Everything above treats every `Rewrite s t` node as a **trusted leaf**:
`all_leaves_sound`/`lemma_proof_sound`/`lemma_checker_sound` all require
semantic soundness of every leaf as an explicit caller-side
precondition, never discharged inside the checker — this mirrors Z3's
own `proof_checker.cpp::check1_basic`'s `PR_REWRITE` case exactly
(shape-only check, equation pushed to an unverified `side_conditions`
list that ordinary solving, `smt_context.cpp::check_proof`, discards
without checking; only `src/test/simplifier.cpp`/`src/test/proof_checker.cpp`
independently verify it, via a second SMT call).

Two follow-ups make this concrete instead of abstract:

1. **`Z3PulseProofCheckerTests.fst`** gained a new array-theory
   derivation (`select(store(a,i,v),i) = v`, matching the earlier
   `array:select` tag from the now-reverted tagging mechanism) and a
   generic `collect_rewrite_leaves`/`collect_rewrite_leaves_list`
   traversal that returns every trusted `Rewrite` leaf's `(s, t)` pair
   reachable in a proof tree — demonstrated on both the new array leaf
   (one leaf) and the pre-existing `mixed_chain` derivation (three
   leaves, spanning seq/bool/arith). This answers "what, exactly, is
   this proof trusting?" mechanically, rather than by manual
   inspection.
2. **`Z3InterpretedProofChecker.fst`** goes one step further: for four
   concrete example leaves, it actually **discharges**
   `all_leaves_sound`, rather than leaving it as an assumed
   precondition, by constructing one real semantic `interpretation
   value` and invoking the matching already-proved per-theory lemma:

   | Leaf | Equation | Theory lemma invoked |
   |---|---|---|
   | `array_leaf` | `select(store(a,i,v),i) = v` | [`Z3ArrayTheory.lemma_select_store_same`](Z3ArrayTheory.fst) |
   | `seq_leaf` | `(a++b)++c = a++(b++c)` | [`Z3SeqRewrites.lemma_concat_assoc`](Z3SeqRewrites.fst) |
   | `bool_leaf` | `not(not x) = x` | [`Z3BoolRewriter.not_not`](Z3BoolRewriter.fst) |
   | `bv_leaf` | `bvand y y = y` | [`Z3BvRewriter.lemma_bvand_self`](Z3BvRewriter.fst) |

   The semantic domain `value` is deliberately first-order
   (`VInt`/`VBool`/`VArr (Z3ArrayTheory.arr int int)`/
   `VSeq (Z3SeqTheory.seq int)`/`VBV (Z3BvTheory.bv 32)`) rather than
   recursively embedding `value` itself as the array/sequence element
   type: `Z3SeqTheory.seq` requires its element type to be an
   `eqtype`, and a function-typed constructor (`VArr`, needed for
   `Z3ArrayTheory`'s extensional-array representation) can never be an
   `eqtype` (no decidable equality on functions) — so the two
   requirements are jointly unsatisfiable for a single recursive
   `value`, and restricting array/sequence elements to plain `int`
   (matching the concrete sorts `ArrayIntInt`/`SeqInt` the example
   leaves actually use) sidesteps the conflict entirely.
   `interp_app`'s operator dispatch is written as nested `if`/`match`
   rather than guard-bearing `match ... | p when c ->` arms, because
   F*'s `--verify` mode rejects `when` clauses (confirmed by a
   type-checking error — "When clauses are not yet supported in
   --verify mode").

   For each leaf, both `lemma_<leaf>_sound : Lemma (all_leaves_sound
   the_interpretation <leaf>)` (invokes the theory lemma directly) and
   an end-to-end `lemma_<leaf>_true` (composes it with
   `Z3ProofTheory.lemma_proof_sound` to get an actual `eval`-level
   equality, for every environment `rho`) are proved. Arithmetic's
   `(+ x 0) = x` leaf (used elsewhere in the test suite) was
   deliberately **not** wired this way: `Z3ArithRewriter.fst` has no
   standalone additive-identity lemma matching that exact shape (the
   relevant logic lives in `poly_rewriter`'s `cancel_monomials`, out of
   scope per `PROOF_OMISSION_AUDIT.md`), so forcing a match would have
   meant proving a new lemma outside this follow-up's stated scope
   rather than reusing one that already exists.

   This demonstrates, for a representative leaf from each of four
   theories, that "trust this leaf" is not merely assumed but can be
   *replaced* by "this leaf is exactly an instance of an
   already-mechanically-verified per-theory lemma" — closing, for
   these four cases, the one gap in the Pulse checker's soundness
   story that remains open in general (and in general must remain
   open: for the checker to stay theory-agnostic, it cannot itself
   re-derive every theory's semantics).

## Follow-up: `Z3PatternMatchedProofChecker.fst` — rewrite rules as patterns, not examples

`Z3InterpretedProofChecker.fst`'s four leaves above are each a single,
literal, hand-picked instance of a theory lemma (named constants `a`,
`i`, `v`, ...) — proving each one sound is a one-line call into the
matching lemma only because the sub-expressions' shapes are "obviously"
right by construction. `Z3PatternMatchedProofChecker.fst` generalizes
this into a genuine **pattern-matching compiler**: a decidable
recognizer library, one recognizer per already-proven rewrite-rule
lemma, each accepting its schema for *arbitrary* sub-expressions — not
just literal named constants — and automatically discharging
`all_leaves_sound` for any `Rewrite` leaf (however deeply its pieces
are nested) by invoking the matching theory lemma under the hood.

**Six patterns are covered**, spanning four theories, chosen because
each is expressible using only the six operators
(`op_not`/`op_plus`/`op_select`/`op_store`/`op_bvand`/`op_concat`)
`the_interpretation` already gives semantics to, and none needs a
semantic side condition requiring two named constants to be
*provably distinct* (see the standing limitation below):

| Pattern | Lemma |
|---|---|
| `select(store(a,i,x),i) = x` | `Z3ArrayTheory.lemma_select_store_same` |
| `store(store(a,i,x),i,y) = store(a,i,y)` | `Z3ArrayTheory.lemma_store_same_twice` |
| `store(a,i,select(a,i)) = a` | `Z3ArrayTheory.lemma_store_redundant` |
| `(a++b)++c = a++(b++c)` | `Z3SeqRewrites.lemma_concat_assoc` |
| `not(not(x)) = x` | `Z3BoolRewriter.not_not` |
| `bvand(y,y) = y` | `Z3BvRewriter.lemma_bvand_self` |

`try_match_leaf` (§5) is the boolean OR of the six individual matchers,
with its own soundness lemma (`lemma_try_match_leaf_sound`) composing
whichever one of the six fired; `all_matched`/`lemma_matched_proof_true`
(§6) lift this, unchanged in shape from the original single-pattern
design, to whole proof trees.

**No Meta-F*/tactics are needed.** `expr`/`func_decl`/`sort` have no
function-typed fields anywhere (`func_decl.interp : option decl_kind`
is a plain integer tag, not a semantic function), so `expr` has
decidable structural equality and admits genuinely general, decidable
pattern matching in plain F*. The design:

- **`decl_shape_ok`/`decls_ok`** — `Z3AstTheory.wf` only checks that an
  `App`'s args match its *own* declared domain; it says nothing about
  whether a given `f.interp = Some k` tag is consistent with the
  specific domain/range `Z3InterpretedProofChecker.interp_app` actually
  expects for that `k` (that binding is this project's own choice, not
  anything `Z3AstTheory.fst` enforces). `decl_shape_ok` closes this
  gap with a finite case-split over the six interpreted ops
  (`op_not`/`op_plus`/`op_select`/`op_store`/`op_bvand`/`op_concat`);
  `decls_ok` extends it recursively over a whole expression.
- **`shape_ok`/`lemma_eval_shape`** — the central structural "type
  soundness" lemma: a well-formed, `decls_ok`, closed, quantifier-free
  expression's value (under `the_interpretation`) always has the
  constructor shape (`VInt`/`VBool`/`VArr`/`VSeq`/`VBV`) its declared
  sort promises, proved once by induction over `expr`. This is the
  piece that makes matching *arbitrary* sub-expressions sound:
  `interp_app`'s dispatch (e.g. `op_select`'s
  `match args with | [VArr a; VInt i] -> ... | _ -> VInt 0`) silently
  falls back to a dummy value for ill-shaped arguments, so recognizing
  `select(store(a,i,x),i)` generically is only sound once `a`/`i`/`x`
  are *guaranteed* — not merely assumed — to evaluate to the right
  shapes.
- **`match_select_store_same`/`select_store_same_leaf_ok`** — a purely
  structural matcher (decidable `expr` equality, checking `f.interp`
  tags and that the two index sub-expressions are syntactically
  identical) plus the side conditions (`wf`/`closed`/`decls_ok`/sort
  checks on the matched pieces) needed for `lemma_eval_shape` to apply.
- **`all_matched`/`lemma_all_matched_sound`** — a decidable, whole-
  proof-tree checker mirroring `all_leaves_sound`'s own recursion
  structure, calling the matcher at every `Rewrite` leaf, with a
  soundness proof composing `lemma_select_store_same_leaf_sound` at
  each one.
- **`lemma_matched_proof_true`** — the end-to-end theorem: any proof
  tree the structural checker accepts (`Some? (fact p)`) whose
  `Rewrite` leaves all fit the select-store-same schema (`all_matched
  p`) denotes a *true* equation under `the_interpretation`, composing
  `lemma_all_matched_sound` with `Z3ProofTheory.lemma_proof_sound` —
  with no hand-wired, per-example trust needed for this pattern,
  however deeply nested.

**Demonstrated on a new, non-trivial example**, distinct from
`Z3InterpretedProofChecker.array_leaf`'s literal named constants:
`select(store(f(x), i+i, g(y)), i+i) = g(y)`, where `f`/`g` are
uninterpreted functions and `i+i` is a *compound* index expression
(not a named constant). `lemma_nested_leaf_true` proves this leaf's
equation holds under `the_interpretation`, via `all_matched
nested_leaf` alone — no new per-leaf lemma call was written for this
specific example, unlike every leaf in `Z3InterpretedProofChecker.fst`.

**Partial mode: leftover proof obligations for unmatched leaves.**
`all_matched` is all-or-nothing: a single `Rewrite` leaf not fitting
any of the six schemas (e.g. anything built from `select_const`,
`ite`, `map`, set operations, or extensionality — none of which
`the_interpretation` gives semantics to) makes `all_matched` reject the
*whole* proof tree, even if every other leaf, however deeply nested,
matches cleanly. §7 adds a middle ground between "trust everything"
(`all_leaves_sound`) and "match everything or reject" (`all_matched`):

- **`collect_unmatched`/`collect_unmatched_list`** walk a proof tree
  with exactly `all_leaves_sound`'s own recursion structure and return
  the list of `(s,t)` pairs for every `Rewrite` leaf none of the six
  matchers recognizes — the already-matched leaves, however many,
  contribute nothing to this list.
- **`leftover_sound`** is the prop that every `(s,t)` pair in such a
  list genuinely denotes a true equation under `the_interpretation`
  (for every environment).
- **`lemma_collect_unmatched_sound`** is the key theorem:
  `leftover_sound (collect_unmatched p) ==> all_leaves_sound p` — i.e.
  supplying semantic soundness for just the leftover list suffices to
  establish soundness for the *entire* tree, matched leaves included.
  Splitting this fact correctly across `Trans`/`Cong`'s two recursive
  sub-proofs needed explicit list-membership helper lemmas
  (`lemma_mem_app_left`/`lemma_mem_app_right`/
  `lemma_leftover_sound_append_split`) over the `@`-concatenated
  leftover lists.
- **`lemma_partial_proof_true`** composes this with
  `Z3ProofTheory.lemma_proof_sound`: given only `leftover_sound
  (collect_unmatched p)`, the whole derivation's top-level equation is
  true.

**Demonstrated with a mixed example** (`mixed_leaf`, §9): a `Trans` of
two leaves sharing an intermediate expression `mid = select(const(c),i)`
— the first, `select(store(f(x),i,mid),i) = mid`, is a genuine (if
unusually shaped) instance of the already-matched select-store-same
pattern; the second, `mid = c` (`Z3ArrayTheory.lemma_select_const`), is
deliberately unmatched since `const` has no assigned semantics.
`lemma_mixed_leftover_is_exactly_select_const` confirms
`collect_unmatched` isolates *exactly* that one unmatched pair, and
`lemma_mixed_proof_true` proves the composed equation true given only
that single leftover fact as a hypothesis — the matched leaf requires
no further trust.

**Update -- `select_store_diff` is now solved, `store_commute` remains
open**: `Z3InterpretedProofChecker.uninterp_app` now injects distinct
`decl_name` strings to distinct `VInt`s (an injective `string -> nat`
encoding, `string_key`, proved injective by structural induction over
`FStar.String.list_of_string`), so two distinctly-*named* 0-ary
uninterpreted Int constants are provably unequal. This is strong enough
to add `select_store_diff` as a tenth -- see below, "ninth" after
`eq_symm` -- matcher: `select(store(a,i,x),j) = select(a,j)` is matched
whenever `i`/`j` are themselves such constants. `store_commute`
(`store(store(a,i,x),j,y) = store(store(a,j,y),i,x)` for `i <> j`)
remains unmatched: it needs the same semantic side condition but a
larger rewrite shape this task did not add a matcher for.

## Follow-up: running the checker on a real Z3-produced proof

Everything above (and every proof derivation `Z3PulseProofCheckerTests
.fst` exercises) is **hand-transcribed**: an engineer picks a theory
lemma and writes the corresponding `proof` literal directly in F*. A
natural next question: can the checker be run on a proof Z3 *itself*
actually produced, rather than one written by hand to match?

`tools/extract_z3_proof.py` answers this directly, using Z3's own
Python front-end (`z3` / z3py):

1. Builds a tiny example with proof production enabled
   (`z3.set_param("proof", True)`) and refutes the negation of
   `not(not(x)) == x`:
   ```python
   s.add(z3.Xor(z3.Not(z3.Not(x)), x)); s.check()   # unsat
   pf = s.proof()                                    # a real ExprRef proof DAG
   ```
2. Walks down from the real proof's root (here, a top-level `mp` node
   wrapping an `asserted` premise and an equational premise) to find
   the first descendant whose own Z3 proof-rule kind is in the
   equational fragment `Z3ProofTheory.fst` models
   (`Z3_OP_PR_REFLEXIVITY`/`SYMMETRY`/`TRANSITIVITY`/`MONOTONICITY`/
   `REWRITE`(`_STAR`)/`QUANT_INTRO`). For this example, real Z3
   internal preprocessing happens to produce **exactly**:
   ```
   trans(
     monotonicity( rewrite( not(not(x)) = x ),            (* a real not_not rewrite *)
                   xor(not(not(x)), x) = xor(x, x) ),
     rewrite( xor(x, x) = false ) )                        (* a real xor-self rewrite *)
   ```
   -- a `Trans(Congr(xor, ...), Rewrite(...))` shape that maps onto
   `Z3ProofTheory.fst`'s calculus **exactly**, not approximately: every
   `rewrite` leaf transcribed really is a `PR_REWRITE` leaf Z3's own
   kernel accepted, every `monotonicity`/`transitivity` node really is
   what `Congr`/`Trans` model.
3. Pretty-prints that subtree, node-by-node (memoized by Z3's own
   internal AST id, so hash-consed sharing is preserved), into literal
   `sort`/`func_decl`/`expr`/`proof` F* definitions, producing a
   complete, self-contained, auto-generated module
   (`Z3ExtractedProof.fst`, committed as a snapshot of this run --
   regenerate it by rerunning the script) ending in a Pulse `fn
   check_extracted ()` that calls `check_proof`/`checker_accepts` on
   the result.
4. Shells out to `fstar.exe` (`--check` flag) to actually run the
   Pulse-verified checker on the generated file and reports the
   verdict back to the Python caller -- there is no other way to "run"
   a Pulse program; F* type-checking a `#lang-pulse` `fn` body *is*
   executing its verification.

Any proof node *within* the extracted subtree that is not in the
equational fragment (did not occur for this example, since the
`trans`/`monotonicity`/`rewrite` nodes above have no further premises
beyond other equational nodes/leaves) falls back to a documented,
clearly-non-semantic representational bridge: `Rewrite a b` if the
node's own conclusion already is an equation/`iff`, else `Rewrite F
true_marker` for a bare formula `F` (`true_marker` is just an
uninterpreted Bool constant -- this does not assert `F` is true in any
interpretation, it only lets the structural checker treat "some other
kind of derivation step occurred here" uniformly as one more trusted
leaf, exactly as every `PR_REWRITE` leaf already is).

**Result, actually run**: `python extract_z3_proof.py --check` ->
`fstar.exe` reports `Verified module: Z3ExtractedProof / All
verification conditions discharged successfully` -- the Pulse checker
genuinely accepts this real, Z3-produced (not hand-authored) proof
object, and (via `lemma_checker_sound`, transitively) its conclusion
`xor(not(not(x)), x) = false` is sound given `all_leaves_sound`
(discharged here the same way as any other leaf -- `not_not` and
`xor`-self-elimination are exactly the kind of leaf
`BOOL_ARITH_REWRITER_REPORT.md` already independently audits).

**Scope of this follow-up, precisely**: a full `(get-proof)` output for
a realistic `check-sat` is dominated by inferential rules (`asserted`,
`hypothesis`, `mp`, `unit-resolution`, `th-lemma`, `hyper-resolve`, ...)
this checker's calculus does not model at all (see
`PROOF_JUSTIFICATIONS_REPORT.md`/`PREPROCESSING_PROOFS_REPORT.md` for
the separate files that model some of those). This script does not
attempt to convert those; it deliberately picks out the purely
equational *subtree*, which is exactly this checker's stated scope.
It is a genuine demonstration that real Z3-produced equational proof
fragments fit this model exactly, not a general-purpose proof importer
for arbitrary Z3 refutations.

### Extending to arbitrary `.smt2` files

`tools/extract_z3_proof.py` now also accepts an optional positional
argument: a path to an `.smt2` file whose assertions are jointly
unsatisfiable. Usage:

```
python extract_z3_proof.py [smt2-file] [--check] [--out FILE.fst]
```

With a path given, the script parses the file with
`z3.parse_smt2_file`, loads the assertions into a fresh `z3.Solver()`
(with proof production enabled first, as before), calls `check()`, and
-- if the result is anything other than `unsat` -- reports clearly
that no refutation proof exists to extract (rather than crashing on a
missing `.proof()`). On `unsat`, the rest of the pipeline
(`find_equational_root` / `Converter` / `generate`) runs unchanged. The
built-in `not(not(x)) == x` example remains the default when no path
is given.

Two real `.smt2` files were used to exercise this path end-to-end,
both committed under `tools/` together with their generated/checked
snapshots:

* `tools/test_not_not.smt2` (`(assert (xor (not (not x)) x))`) --
  produces the same 4-node equational subtree as the built-in example,
  now driven entirely by parsing a file instead of building the
  formula in Python. Snapshot: `Z3ExtractedProof_FromFile.fst`.
* `tools/test_bvand_self.smt2` (`(assert (not (= (bvand y y) y)))`) --
  a larger, independently-interesting case: Z3's real proof for this
  one is a 12-proof-node / 11-expr-node equational subtree (rewriting
  `bvand y y` down through `bvnot (bvor (bvnot y) (bvnot y))` to `y`,
  via De Morgan's law on bitvectors), still landing entirely inside the
  equational fragment. Snapshot: `Z3ExtractedProof_Bv.fst`.

Both snapshots pass `--check` (`fstar.exe` reports `All verification
conditions discharged successfully`), but the larger one surfaced a
real issue worth recording: F*'s default `--fuel 2 --ifuel 2` /
`--z3rlimit` budget was not enough for the SMT solver to unfold
`fact`/`congr_matched`/`find_matching_fact`'s recursion all the way
through a 12-node proof when the `Some? (fact extracted_proof)` goal
was asked for directly inside the Pulse function's generated
verification condition. The fix applied to the generator's template
(affecting every generated file, not just the larger example):
1. wrap the generated `lemma_extracted_proof_wellformed`/
   `check_extracted` pair in `#push-options "--z3rlimit 60 --fuel 4
   --ifuel 4" ... #pop-options`, and
2. prove `lemma_extracted_proof_wellformed` by `assert_norm` (full
   normalization, not SMT-driven unfolding) rather than bare `()`, and
   **explicitly call it as the first statement of `check_extracted`**
   so the Pulse function's own VC gets `Some? (fact extracted_proof)`
   as an already-proven hypothesis instead of having to re-derive it
   from scratch under the Pulse encoding's own fuel budget.

This is a verification-engineering fix (how the already-correct fact
gets communicated to the SMT solver), not a change to the checker's
soundness argument -- `check_proof`'s own internal logic is untouched.

## Wiring the rewrite-rule matcher into the extraction pipeline

`Z3PatternMatchedProofChecker.fst`'s `collect_unmatched` (see above) is
proven sound, but until this follow-up it only ever ran over
hand-constructed F\* `proof`/`expr` terms inside that file's own
demonstrations -- it had never been pointed at a real Z3-extracted
proof. `tools/extract_z3_proof.py` now closes that gap:

* **Python-side mirror.** `classify_rewrite(s, t)` re-implements the
  same six pattern tests (`select_store_same`, `store_same_twice`,
  `store_redundant`, `concat_assoc`, `not_not`, `bvand_self`) directly
  over z3's own `ExprRef` ASTs (via `decl().kind()` checks), at every
  site a `Rewrite` leaf is produced during conversion. This mirror is
  *not* trusted on its own -- it only drives a human-readable log.
* **Cross-check, not re-trust.** The generated `.fst` file
  additionally does `open Z3PatternMatchedProofChecker` and emits
  `assert_norm (FStar.List.Tot.length (collect_unmatched
  extracted_proof) == N)`, where `N` is the Python mirror's own
  unmatched count. If the Python classification ever disagrees with
  the real, proven F\* matcher, this assertion fails to type-check --
  so the log's "matched" vs. "unmatched" split is mechanically tied to
  `Z3PatternMatchedProofChecker.fst`'s soundness proof, not merely
  asserted by the extraction script.
* **`interp` tagging.** The six theory-specific matchers require
  `func_decl.interp = Some op_X` (not just the right `decl_name`/arity); `Converter.func_decl`
  now tags declarations matching one of the six known interpreted ops
  (`not`, `select`, `store`, `bvand`, `seq.++`) at their expected arity,
  leaving everything else `interp = None` (safely covered by
  `decl_shape_ok`'s `None -> true` case) exactly as before.
* **Sort naming fixes.** `Converter.sort` special-cases `BitVecSort`
  (`"BV%d" % s.size()`, since `.name()` loses the width) and
  `Seq(Int)` (`"SeqInt"`, since `.name()` loses the element sort) to
  match the literal sort names `Z3InterpretedProofChecker.fst` expects;
  it also fixes a pre-existing bug where the array-sort branch called
  a nonexistent `ArraySortRef.arity()` (replaced with the raw C API
  `Z3_get_array_arity`), which had silently blocked every array-sort
  extraction until now.
* **Log output.** `--log <file>` (default `<out>.unmatched.log`) lists
  every `Rewrite` leaf seen, either tagged with the matched pattern
  name or marked unverified with its `.sexpr()` text, plus a
  matched/unmatched summary count.

New end-to-end examples exercising all six matchers via real Z3
proofs: `not(not(x))==x` (`not_not`, pre-existing), `(select (store a
i v) i)==v` (`select_store_same`), `(store (store a i x) i y) ==
(store a i y)` (`store_same_twice`), `(store a i (select a i)) == a`
(`store_redundant`), `(seq.++ (seq.++ a b) c) == (seq.++ a (seq.++ b
c))` (`concat_assoc`), and `bvand y y == y` (which Z3 proves via De
Morgan expansion rather than the literal `bvand_self` schema -- a
genuine example of the "accumulate unmatched, don't reject" path).

A further example, `(select (store a i x) j) == (select a j)` under
hypothesis `i <> j` (`select_store_diff`), demonstrates an array
rewrite that is **deliberately not wired in**: this schema needs an
`i <> j` side condition that `the_interpretation`'s model can't
discharge generically (documented as a known limitation in
`Z3PatternMatchedProofChecker.fst` section 4a), so no
`match_select_store_diff` exists. Inspecting the raw Z3 proof confirms
this isn't merely an unmatched shape -- Z3 proves it via `PR_TH_LEMMA`
(a theory lemma over `(or (= i j) (select (store a i x) j) = (select a
j))` discharged by `unit-resolution`), not a `PR_REWRITE` node at all,
so the fact never even reaches the rewrite-matcher machinery; the one
`Rewrite` leaf that *is* logged for this example is an unrelated
trivial self-rewrite of the asserted hypothesis.

## A seventh, general-purpose matcher: reflexivity

`Rewrite s t` leaves where `s` and `t` are the *same* `expr` (e.g. the
`select_store_diff` example above actually surfaces one: its sole
`Rewrite` leaf is `(not (= i j)) == (not (= i j))`, Z3's own self-
rewrite of the asserted hypothesis) are sound for *any* theory and
*any* interpretation, by plain reflexivity of `==`: `eval i s rho` and
`eval i t rho` apply the same `eval` function to the same argument
`s` (since `s` and `t` are the same term), so they are trivially equal
-- no theory lemma, sort check, or side condition is needed at all.
This is now the seventh matcher, `reflexivity_leaf_ok`/
`lemma_reflexivity_leaf_sound` (checked first, since it's the cheapest
and most general), wired into `try_match_leaf`/`all_matched`/
`collect_unmatched` exactly like the six theory-specific matchers, and
mirrored in `classify_rewrite`'s Python side. Re-running the
`select_store_diff` example confirms it: the previously-unmatched
reflexive leaf is now reported `[reflexivity] (not (= i j)) == (not (=
i j))`, with 0 leftover unmatched leaves, and the cross-check
`assert_norm` still passes -- i.e. F\*'s real, proven
`collect_unmatched` independently agrees.

## An eighth and ninth matcher: `eq_symm` and `select_store_diff`

Two more matchers were added afterwards, bringing the library to nine:

* **`eq_symm`**: `(= a b) = (= b a)`, for any two same-sorted
  sub-expressions. This needed a new interpreted operator, `op_eq`
  (polymorphic -- `decl_shape_ok` now accepts `domain = [d;d]` for
  *any* sort `d`, `range = Bool`), given semantics `value_eq_sym :
  value -> value -> bool` (total; `VArr`'s function type has no
  decidable equality, so two array-valued arguments are soundly
  reported unequal, an under-approximation never exercised by any
  `op_eq` leaf this checker actually sees). Soundness needs no theory
  lemma, just `lemma_value_eq_sym_symmetric`. This directly addresses
  a shape observed at scale in the QF_AX benchmark corpus (see
  `QF_AX_QF_UF_BENCHMARK_REPORT.md`'s "= ... -> = ..." outer-shape
  bucket): orientation-swapped equality leaves from `array-ext`-derived
  goals.
* **`select_store_diff`**: `select(store(a,i,x),j) = select(a,j)` for
  `i <> j` -- the pattern flagged as a known limitation above. Solved
  via a model fix: `Z3InterpretedProofChecker.uninterp_app` now
  special-cases 0-ary, Int-sorted uninterpreted constants, injecting
  their `decl_name` through an injective `string -> nat` encoding
  (`string_key`: a base-`0x110001` positional encoding over
  `FStar.String.list_of_string`, `0x110001` chosen because it exceeds
  every Unicode scalar value `FStar.Char.int_of_char` can return;
  injectivity proved by one straightforward structural induction, no
  extra hints needed) instead of the old fixed `default_value` for
  every constant of a sort. Two distinctly-named constants are now
  *provably* distinct `VInt`s (`lemma_string_key_distinct`), which is
  exactly what `Z3ArrayTheory.lemma_select_store_diff`'s `i <> j`
  hypothesis needs whenever `i`/`j` are themselves such constants
  (compound index expressions, e.g. `i+1` vs `j`, remain unmatched).
  Changing `uninterp_app` required a matching update to
  `lemma_eval_shape`'s uninterpreted-application case (a new
  `lemma_uninterp_app_shape_ok`, case-splitting the same way
  `uninterp_app` itself does) to keep the central type-soundness
  induction correct; both files still typecheck cleanly, and all
  pre-existing `Z3ExtractedProof*.fst` snapshots still verify with no
  regressions. Two new in-source demonstrations (`ssd_leaf`/
  `eqsym_leaf` in `Z3PatternMatchedProofChecker.fst` section 10) show
  each matcher firing on constructed, non-literal examples, and
  re-running the full QF_AX corpus confirms `select_store_diff` fires
  for real at least once outside any hand-built example (see
  `QF_AX_QF_UF_BENCHMARK_REPORT.md`'s "Update" section for the full
  before/after numbers, including an honest cost: the extra
  nine-matcher reasoning needs roughly 3x the per-file F* budget the
  baseline experiment used before most files reliably `pass`).

## A tenth matcher: `store_commute`, and a negative result

A tenth matcher, `store_commute`, was added afterwards:
`store(store(a,i,x),j,y) = store(store(a,j,y),i,x)` for `i <> j`
(`Z3ArrayTheory.lemma_store_commute`) -- the index-swap twin of
`select_store_diff`, discharging the same `i <> j` side condition the
same way (`i`/`j` must be two distinctly-named 0-ary uninterpreted Int
constants). It typechecks cleanly, fires on a hand-built,
single-level in-source demonstration (`sc_leaf`,
`Z3PatternMatchedProofChecker.fst` section 11, built from
`tools/test_store_commute.smt2`), and all 9 pre-existing
`Z3ExtractedProof*.fst` snapshots still verify with no regressions.

Re-running the full QF_AX corpus, however, is a **negative result**:
`store_commute` matches **zero** additional leaves. The corpus's
dominant unmatched family, `storecomm_*`, proves an entire
multi-level (4+ nested `store`s) index permutation in a single leap --
from a bare atom straight to a giant `(_ array-ext 0)` witness term --
inside Z3's array theory solver itself, not as a chain of adjacent
one-step swaps. No literal `Rewrite` leaf in those proofs has the flat
two-level shape any single-equation matcher (this one included) can
recognize. This is reported plainly rather than glossed over: see
`QF_AX_QF_UF_BENCHMARK_REPORT.md`'s "Update 2" section for the
concrete unmatched leaf that demonstrates it, and for why closing this
gap would need a structurally different kind of matcher (one that
recurses into the `array-ext` witness itself), not another one-step
lemma.

## An eleventh matcher: `store_perm`, a general multi-level theorem

Rather than add another fixed-shape equation, `Z3ArrayTheory.fst` was
extended with a genuinely *general* theorem: for an arbitrary-length
chain of `n` nested `store`s on pairwise-distinct (named, uninterpreted)
indices, the final array depends only on the *set* of (index, value)
updates, not the order they were applied in
(`lemma_apply_updates_set_eq`, built over `apply_updates`/`last_match`
association-list semantics). `store_commute`'s fixed two-level swap is
exactly this theorem's `n = 2` special case.

The new matcher, `store_perm`, flattens both sides of a `Rewrite s t`
leaf into `(base, [(index, value), ...])` pairs (`flatten_store`),
checks the two chains share a base, have equal length `>= 2`, carry
pairwise-distinct named-constant indices on each side, and the same
*set* of (index, value) pairs -- then discharges the leaf through
`lemma_apply_updates_set_eq` via a chain of append/evaluation
bookkeeping lemmas (`lemma_eval_pairs_append`, `lemma_eval_store_chain`,
`lemma_flatten_store_wf`). It is now the eleventh matcher in
`try_match_leaf`. It typechecks cleanly, fires on a hand-built 3-level
store chain under two different cyclic rotations
(`Z3PatternMatchedProofChecker.fst` section 12, "Demonstration 5" --
`sp3_leaf_1`/`sp3_leaf_2`, neither matchable by `store_commute` alone),
and all 9 pre-existing `Z3ExtractedProof*.fst` snapshots still verify
with no regressions. The Python mirror in `extract_z3_proof.py`
(`_match_store_perm`, `_flatten_store`, `_pairwise_distinct_keys`,
`_same_update_set`) was updated to match and is cross-checked against the
real F* matcher on every generated benchmark file via `assert_norm`.

Unlike `store_commute`, re-running the full QF_AX corpus with this
eleventh matcher is a small but **positive** result: it finds one
genuine match, `cvc/read5.smt2`'s leaf
`(store (store (store S aaa vvv) a v) aa vv) = (store (store (store S a
v) aa vv) aaa vvv)` -- a literal 3-level store-chain reordering with no
intervening `select`/congruence steps. This confirms the generalization
pays off on real proof output in at least one case, even though the
corpus's dominant `storecomm_*` family remains out of reach for the
reason explained above (its permutation reasoning is buried inside an
opaque `array-ext` witness-skolemization step, not a literal `store`
chain). See `QF_AX_QF_UF_BENCHMARK_REPORT.md`'s "Update 3" section for
the full before/after numbers.

## Scope and limitations

* **`provably_distinct` now covers literal constants, not just named
  ones.** `Z3InterpretedProofChecker.fst` gained four new interpreted
  ops -- `op_true`/`op_false` (`OP_TRUE`/`OP_FALSE`) and two
  `OP_NUM`-family numeral ops, `op_num_int`/`op_num_bv` (a numeral's
  decoded value is carried in `func_decl.int_params`, mirroring how
  `re.loop`'s bounds are already represented) -- each with its own
  small, independently-verified interpretation function
  (`interp_true`/`interp_false`/`interp_num_int`/`interp_num_bv`).
  `Z3PatternMatchedProofChecker.fst`'s `provably_distinct (a b:expr) :
  bool` generalizes the pre-existing injective-naming trick
  (`is_uninterp_const`/`const_name`/`string_key`, sound only because
  `Int` is an *infinite* sort) with four more disjuncts: `true`
  vs. `false`, two Int numerals with different raw values, and two BV
  numerals with different values *after* `bv32_value`'s mod-2^32
  reduction (two different raw `int_params` can denote the same
  bit-vector). Literal distinctness is sound for *any* sort, finite or
  not, because a literal's denotation is a fixed function of its own
  payload, never a free/symbolic choice -- unlike named constants,
  where the naming trick is deliberately restricted to `Int`.
  `lemma_provably_distinct_sound` is the one soundness lemma every
  matcher needing a semantic index-disequality side condition
  (`select_store_diff`, `store_commute`, `store_perm`'s
  `all_const_distinct_from`) now calls, replacing the previous
  ad-hoc inline `lemma_string_key_distinct` invocation duplicated at
  each call site. A new demonstration (§13, `lit_ssd_leaf`) matches
  `select(store(a,3,x),5) = select(a,5)` -- literal Int numerals, not
  named constants -- via `select_store_diff`, and `lit_bv_leaf` does
  the analogous thing for two BV numerals via `eq_symm`.
* **Performance lesson (verification-engineering, not soundness):**
  adding the BV-numeral reduction (`bv32_value`, now
  `Z3BvTheory.bv_of_int`) as one more branch *inline inside*
  `Z3InterpretedProofChecker.fst`'s single, monolithic `interp_app`
  if/elif dispatcher caused a severe (multi-hour) verification hang --
  confirmed, via `--z3rlimit`/`--z3cliopt timeout=...`, to be in F*'s
  own SMT-query-*construction* phase (building one giant combined VC
  mixing array/seq/bv/bool facts), not in Z3's search. The fix was
  decomposing `interp_app` into eleven small, independently-checked
  top-level helper functions (`interp_not`, `interp_plus`, ...,
  `interp_num_bv`), each only ever typechecking its own op's VC, with
  `interp_app` reduced to a trivial dispatcher. This restored the
  file's verification time to its original ~15s baseline (in fact
  slightly faster). The general lesson: when one function's body
  touches many different theories' lemmas/types at once, prefer many
  small single-theory helper functions over one large combined
  `if`/`match` chain, even when the combined chain is logically
  simpler to read.
* **`interp_app` is now dispatched per-theory, not as one monolithic
  function.** `value` (the `VInt`/`VBool`/`VArr`/`VSeq`/`VBV` semantic
  domain) and every `op_*` decl_kind constant moved out of
  `Z3InterpretedProofChecker.fst` into a new, dependency-free leaf
  module, `Z3ValueTheory.fst`. Each existing base theory file
  (`Z3ArrayTheory.fst`/`Z3SeqTheory.fst`/`Z3BvTheory.fst`) itself stays
  untouched -- still pure `arr`/`seq`/`bv`-plus-lemmas, with no notion
  of `value` at all, since `value` is defined *over* those theories'
  types and a module defining `arr`/`seq`/`bv` cannot also depend on
  `value` without a circular module dependency. Instead, three new
  thin companion modules -- `Z3ArrayInterp.fst`, `Z3SeqInterp.fst`,
  `Z3BvInterp.fst` -- each depend on both `Z3ValueTheory.fst` and
  their own base theory file, and each expose one
  `interp_app (k:decl_kind) (int_params:list int) (args:list value) :
  option value`: `Some v` for any `decl_kind` that theory owns
  (array: `op_select`/`op_store`; seq: `op_concat`; bv:
  `op_bvand`/`op_num_bv`, the latter needing `bv32_value` -- also
  moved here, next to its one use site), `None` otherwise.
  `Z3InterpretedProofChecker.fst`'s top-level `interp_app` is now a
  short composition: try `Z3ArrayInterp.interp_app`, then
  `Z3SeqInterp.interp_app`, then `Z3BvInterp.interp_app`, then a local
  `core_interp_app` for the remaining bool/arith/`eq`/literal ops
  (`op_not`/`op_plus`/`op_eq`/`op_true`/`op_false`/`op_num_int`, which
  have no dedicated theory file of their own), then a total fallback.
  This mirrors the same "small, independently-checked pieces, trivial
  composition" shape as the earlier eleven-helper-function
  decomposition (previous bullet): each theory's interpretation is now
  owned, re-verified, and extensible independently of every other
  theory's, and none of this changed any lemma's *statement* -- only
  which module proves/hosts it. Downstream consumers
  (`Z3PatternMatchedProofChecker.fst` and all nine
  `Z3ExtractedProof*.fst` files, plus the `tools/extract_z3_proof.py`
  generator template) needed one mechanical addition, `open
  Z3ValueTheory`, since F* does not transitively re-export `open`ed
  names. Re-verified end to end with no new hangs: `Z3ValueTheory.fst`
  (~2s), each of `Z3ArrayInterp.fst`/`Z3SeqInterp.fst`/`Z3BvInterp.fst`
  (~1.6s each), `Z3InterpretedProofChecker.fst` (~8s, unchanged from
  before this refactor), `Z3PatternMatchedProofChecker.fst` (~3.5
  minutes, in line with its pre-refactor time; one lemma,
  `lemma_concat_assoc_leaf_sound`, needed its `--z3rlimit` raised to
  50 to absorb the extra `Some`/`None` unfolding the new composed
  dispatcher requires), and all nine `Z3ExtractedProof*.fst` files
  (~9s each).
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
* **`alloc`/`free` deprecation**: **resolved** (see "Pulse lessons"
  above) -- every `alloc`/`free` pair in this project's Pulse files was
  replaced with Pulse's `let mut` scoped-local sugar (built on the
  non-deprecated `with_local`), and all files re-verify with zero
  `alloc`/`free` deprecation warnings. This was always a verification-
  engineering concern, not a soundness gap: Pulse's separation-logic
  VCs for `pts_to`/ownership were already fully discharged around
  every `alloc`/`free` pair even before this change.
* **No OCaml/C extraction was attempted** — this is a verified-model
  exercise within F\*/Pulse's own type checker, not a build-integration
  change to Z3's actual `proof_checker.cpp`; nothing in
  `src/ast/proofs/proof_checker.cpp` was modified.

## A twelfth generalization: `is_unique_value`, a general distinctness predicate

The literal-distinctness disjuncts of `provably_distinct` described
above (`true`/`false`, Int numerals, BV numerals) were four separate
ad-hoc cases. `Z3PatternMatchedProofChecker.fst` now has a single
recursive predicate, `is_unique_value : expr -> bool`, generalizing
all four into one definition and extending it one level deeper to
sequence literals: an expression is a "unique value" if it is a
`true`/`false` constant, an Int or BV numeral, or a `seq.unit`/`++`
(`op_concat`) tree built entirely from unique-value elements — this
project's concrete stand-in for "an algebraic datatype constructor
applied to unique-value arguments" (a sequence is exactly the free
list datatype, `nil`/`cons` relabelled `empty`/`unit`+`concat`).

The soundness property proved is exactly the one requested: for any
`s`, `t` satisfying `is_unique_value`, `is_unique_value s /\
is_unique_value t /\ not (unique_value_eq s t) ==> eval s rho =!=
eval t rho` (`lemma_unique_value_distinct`) — i.e. two *syntactically
different* unique values are always *semantically distinct*, no
matter which sort they inhabit. `provably_distinct` now dispatches to
this lemma (alongside the pre-existing, separately-sound, injective
*named*-uninterpreted-constant disjunct restricted to `Int`), so every
matcher with a semantic index-disequality side condition
(`select_store_diff`, `store_commute`, `store_perm`) transparently
gains sequence-literal disequality for free, with no changes to the
matchers themselves.

**Design note — why comparing value expressions by raw tree shape is
unsound.** A first attempt compared two sequence-literal expressions
by their `App`-tree shape (same op at each node, pointwise-equal
children). This is **unsound**: `concat` is associative, so
`concat(unit 1, concat(unit 2, unit 3))` and `concat(concat(unit 1,
unit 2), unit 3)` are different expression trees denoting the *same*
list `[1;2;3]` — tree-shape comparison would (wrongly) report them as
distinct, which would make the "distinct" conclusion of a congruence
lemma built on top of it unsound. The fix: never compare literal
*expressions* structurally when the underlying operator has a
non-trivial equational law (associativity here); instead, decode every
unique-value expression down to a flat, literal *semantic* payload
first. `unique_value_key : expr -> lit_value` does this (`lit_value =
LInt int | LBV (bv 32) | LBool bool | LSeq (list int)`, with `LSeq`
built via `Z3SeqTheory.concat`, the *same* function `interp_concat`
itself calls — not a different, extensionally-equal-but-not-
definitionally-equal list operation like `List.Tot.append`, which
would otherwise force an extra bridging lemma). `unique_value_eq s t`
is then plain decidable equality of two `lit_value`s, and the central
bridge lemma `lemma_eval_unique_value_key` shows `eval e rho ==
lit_to_value (unique_value_key e)` whenever `is_unique_value e` holds
— proved by structural induction, using `lemma_eval_shape` (the
file's existing sort/shape-soundness lemma) at each recursive step to
rule out the sub-expression's `unique_value_key` landing in the
"wrong" `lit_value` case (e.g. a `seq.unit`'s argument must have sort
`Int`, so `lemma_eval_shape` forces its decoded key to be `LInt`, not
`LBV`/`LBool`/`LSeq`) before the final distinctness corollary.

## Rewrite steps as *synthesis*, not just verification: the `Z3<Theory>Embed.fst` family

Every matcher described above (§4) answers a *verification* question:
"given both sides `s`/`t` of a candidate `Rewrite` leaf, is this an
instance of lemma `x`?" Five new files — `Z3ArrayEmbed.fst`,
`Z3SeqEmbed.fst`, `Z3BoolEmbed.fst`, `Z3BvEmbed.fst`,
`Z3CoreEmbed.fst` — answer the complementary *synthesis* question:
"given only one side `t`, what does lemma `x` say it equals?" Each
exports, per covered lemma `lemma_x : a = b` (with side condition
`cond(a,b)`):

```
apply_lemma_x : expr -> option expr
```

such that `Some s = apply_lemma_x t` implies `cond(eval t, eval s)`
holds and `eval t == eval s` — proved (`lemma_apply_lemma_x_sound`)
by re-using exactly the same shape/sort/side-condition checks and
`lemma_eval_shape`/theory-lemma dispatch already in each `match_x`
pattern, just with the equality-with-`t`'s-other-side check removed
and the matched right-hand sub-expression returned directly instead.
Each file also exports:

* `apply_lemmas : expr -> list expr` — every successful single-step
  rewrite of `t` by one of that file's lemmas.
* `is_rewrite : expr -> expr -> bool` — `is_rewrite t s` holds iff
  some `apply_lemma_x` in that file maps `t` to `s`, with its own
  soundness corollary `lemma_is_rewrite_sound` (case-split over which
  disjunct fired, dispatching to that lemma's own soundness proof).

**Coverage**: ten of the eleven §4 patterns get an `apply_lemma_x`
(`Z3ArrayEmbed.fst`: `select_store_same`, `store_same_twice`,
`store_redundant`, `select_store_diff`, `store_commute`;
`Z3SeqEmbed.fst`: `concat_assoc`; `Z3BoolEmbed.fst`: `not_not`;
`Z3BvEmbed.fst`: `bvand_self`; `Z3CoreEmbed.fst`: `reflexivity`,
`eq_symm`). **The eleventh, `store_perm`, is deliberately excluded**:
it is not a function of its input in the first place.
`Z3ArrayTheory.lemma_apply_updates_set_eq` proves an `n`-level nested
`store` chain with pairwise-distinct indices equal to *any* of the
`n!` reorderings of the same updates, not one canonical target, so no
single `s` can be returned from an `expr -> option expr` signature.
(`store_commute` is `store_perm`'s `n = 2` special case, where there
*is* a unique "other" order to swap to — hence it alone, among the
distinctness-side-conditioned patterns, gets an `apply_lemma_x`.)

**A genuine, non-mechanical proof bug surfaced along the way**: an
initial draft of the aggregate `lemma_apply_lemmas_sound` (one
"everything in `apply_lemmas t` is sound" lemma per file, stated as a
`forall s. mem s (apply_lemmas t) ==> ...`) failed to verify —
"incomplete quantifiers"/timeouts, because discharging a `forall`
over `mem`-in-a-list-built-by-`@`/`match` needs genuine list-structure
reasoning the individual per-lemma soundness facts don't supply by
themselves. The fix was to define `is_rewrite` directly as an
explicit five-way (or two-way, etc.) *disjunction* of
`apply_lemma_x t = Some s` facts instead of `mem s (apply_lemmas t)`:
logically equivalent, but its own soundness lemma is then a plain
`if`/`else if` case split, each branch an immediate call to that
lemma's own already-proven `lemma_apply_lemma_x_sound` — no `mem`/list
reasoning required at all. `apply_lemmas` itself is kept only as the
convenient "list of what fired" enumeration the task asked for; its
soundness is witnessed per-element by `is_rewrite`'s corollary, not by
a separate blanket lemma over the list.

All five files verify with zero errors ("All verification conditions
discharged successfully" for each).

## Files

| File | Role |
|---|---|
| [`Z3PulseProofChecker.fst`](Z3PulseProofChecker.fst) | Pulse port of `fact`/`facts_of` (the rewriter-calculus checker) |
| [`Z3PulseJustificationChecker.fst`](Z3PulseJustificationChecker.fst) | Pulse decision procedures for modus ponens / unit resolution |
| [`Z3PulseProofCheckerTests.fst`](Z3PulseProofCheckerTests.fst) | Cross-theory sample derivations, run through both checkers above, including rejection tests, plus an array-theory derivation and a generic trusted-`Rewrite`-leaf collector (`collect_rewrite_leaves`) |
| [`Z3InterpretedProofChecker.fst`](Z3InterpretedProofChecker.fst) | Discharges (rather than assumes) `all_leaves_sound` for 4 example leaves (array/seq/bool/bv), by constructing a real semantic `interpretation value` and invoking the matching per-theory lemma directly; its top-level `interp_app` composes each theory's own `interp_app` (below) plus a local `core_interp_app` for bool/arith/`eq`/literal ops |
| [`Z3ValueTheory.fst`](Z3ValueTheory.fst) | The shared `value` semantic domain (`VInt`/`VBool`/`VArr`/`VSeq`/`VBV`) and every `op_*` decl_kind constant, factored out so each theory's own `interp_app` module (below) can depend on it without a circular module dependency on its base theory file |
| [`Z3ArrayInterp.fst`](Z3ArrayInterp.fst), [`Z3SeqInterp.fst`](Z3SeqInterp.fst), [`Z3BvInterp.fst`](Z3BvInterp.fst) | Thin, `value`-level companions to `Z3ArrayTheory.fst`/`Z3SeqTheory.fst`/`Z3BvTheory.fst`, each exposing one theory-scoped `interp_app (k:decl_kind) (int_params:list int) (args:list value) : option value` (`Some` iff that theory owns `k`) that `Z3InterpretedProofChecker.fst`'s top-level dispatcher tries in turn |
| [`Z3PatternMatchedProofChecker.fst`](Z3PatternMatchedProofChecker.fst) | Decidable pattern-matching compiler recognizing six rewrite-rule schemas across array/seq/bool/bv theories for *arbitrary* nested sub-expressions (not just named constants), auto-discharging `all_leaves_sound` via a structural "type soundness" lemma plus the matching theory lemma; also provides a "partial" mode (`collect_unmatched`/`lemma_partial_proof_true`) that reduces an unrecognized leaf's proof obligation to an explicit, minimal leftover-fact list instead of rejecting the whole proof |
| [`tools/extract_z3_proof.py`](tools/extract_z3_proof.py) | Uses Z3's Python front-end to produce a real proof object (from a built-in example or an arbitrary `.smt2` file path), extracts its equational subtree, pretty-prints it into `proof`/`expr` F* literals, and shells out to `fstar.exe` to run the Pulse checker on it |
| [`Z3ExtractedProof.fst`](Z3ExtractedProof.fst) | Auto-generated (regenerate via `python tools/extract_z3_proof.py --out Z3ExtractedProof.fst`) -- the literal transcription of a real Z3 proof object produced for `not(not(x)) == x`, committed as a snapshot of the pipeline's output |
| [`tools/test_not_not.smt2`](tools/test_not_not.smt2), [`Z3ExtractedProof_FromFile.fst`](Z3ExtractedProof_FromFile.fst) | Same `not(not(x)) == x` example, but driven from an `.smt2` file path instead of a built-in Python formula |
| [`tools/test_bvand_self.smt2`](tools/test_bvand_self.smt2), [`Z3ExtractedProof_Bv.fst`](Z3ExtractedProof_Bv.fst) | A larger `.smt2`-driven example (`bvand y y == y`), 12 proof nodes / 11 expr nodes, that surfaced and validated the fuel/`assert_norm` fix described above; also an example where the matcher log reports *unmatched* leaves, since Z3 proves this via De Morgan expansion rather than the literal `bvand_self` schema |
| [`tools/test_select_store.smt2`](tools/test_select_store.smt2), [`Z3ExtractedProof_ArrayExample.fst`](Z3ExtractedProof_ArrayExample.fst) | `(select (store a i v) i) == v`, exercising the `select_store_same` matcher and multi-argument-array sort extraction |
| [`tools/test_concat_assoc.smt2`](tools/test_concat_assoc.smt2), [`Z3ExtractedProof_Seq.fst`](Z3ExtractedProof_Seq.fst) | `(seq.++ (seq.++ a b) c) == (seq.++ a (seq.++ b c))`, exercising the `concat_assoc` matcher and `Seq(Int)` sort naming |
| [`tools/test_store_same_twice.smt2`](tools/test_store_same_twice.smt2), [`Z3ExtractedProof_StoreSameTwice.fst`](Z3ExtractedProof_StoreSameTwice.fst) | `(store (store a i x) i y) == (store a i y)`, exercising the `store_same_twice` matcher |
| [`tools/test_store_redundant.smt2`](tools/test_store_redundant.smt2), [`Z3ExtractedProof_StoreRedundant.fst`](Z3ExtractedProof_StoreRedundant.fst) | `(store a i (select a i)) == a`, exercising the `store_redundant` matcher |
| [`tools/test_select_store_diff.smt2`](tools/test_select_store_diff.smt2), [`Z3ExtractedProof_SelectStoreDiff.fst`](Z3ExtractedProof_SelectStoreDiff.fst) | `(select (store a i x) j) == (select a j)` under `i <> j` -- a rewrite that is *not* wired into any matcher (no `i <> j` side-condition support); Z3 in fact proves it via `PR_TH_LEMMA`, not `PR_REWRITE`, so it never reaches the matcher at all |
| [`Z3ArrayEmbed.fst`](Z3ArrayEmbed.fst) | `apply_lemma_x : expr -> option expr` rewrite-*synthesis* functions for `select_store_same`/`store_same_twice`/`store_redundant`/`select_store_diff`/`store_commute`, plus `apply_lemmas`/`is_rewrite` |
| [`Z3SeqEmbed.fst`](Z3SeqEmbed.fst) | Same, for `concat_assoc` |
| [`Z3BoolEmbed.fst`](Z3BoolEmbed.fst) | Same, for `not_not` |
| [`Z3BvEmbed.fst`](Z3BvEmbed.fst) | Same, for `bvand_self` |
| [`Z3CoreEmbed.fst`](Z3CoreEmbed.fst) | Same, for the two theory-agnostic matchers, `reflexivity` and `eq_symm` |

All three files type-check cleanly with the standard toolchain
invocation (`fstar.exe --smt <z3 4.13.3 binary> <File>.fst`), with zero
errors; remaining diagnostics are pre-existing unrelated warnings from
`Z3AstTheory.fst` (the `alloc`/`free` deprecation warnings previously
noted here no longer occur -- see "Pulse lessons" above).
