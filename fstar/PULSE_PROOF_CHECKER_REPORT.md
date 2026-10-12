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

## Follow-up: `Z3PatternMatchedProofChecker.fst` — select-store as a pattern, not an example

`Z3InterpretedProofChecker.fst`'s four leaves above are each a single,
literal, hand-picked instance of a theory lemma (named constants `a`,
`i`, `v`, ...) — proving each one sound is a one-line call into the
matching lemma only because the sub-expressions' shapes are "obviously"
right by construction. `Z3PatternMatchedProofChecker.fst` generalizes
one of those four patterns, `select(store(a,i,x),i) = x`
(`Z3ArrayTheory.lemma_select_store_same`), into a genuine **pattern-
matching compiler**: a decidable recognizer that accepts this schema
for *arbitrary* array/index/value sub-expressions `a`/`idx`/`x` — not
just literal named constants — and automatically discharges
`all_leaves_sound` for any `Rewrite` leaf (however deeply `a`/`idx`/`x`
are nested) by invoking `Z3ArrayTheory.lemma_select_store_same` under
the hood.

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

**Known limitation, flagged rather than solved**: the companion
pattern `select(store(a,i,x),j) = select(a,j)` for `i <> j`
(`Z3ArrayTheory.lemma_select_store_diff`) is *not* generalized here.
`Z3InterpretedProofChecker.uninterp_app`/`default_value` maps *every*
uninterpreted 0-ary constant of a given sort to the *same* value
regardless of name, so two syntactically distinct named Int constants
currently always denote the identical `VInt`, making the semantic side
condition `i <> j` unsatisfiable for any two currently-expressible
named constants under this interpretation. Supporting this pattern
generically would require `uninterp_app` to inject distinct constant
names to distinct values (e.g. hashing `decl_name`), which is left as
future work rather than attempted here.

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

## Files

| File | Role |
|---|---|
| [`Z3PulseProofChecker.fst`](Z3PulseProofChecker.fst) | Pulse port of `fact`/`facts_of` (the rewriter-calculus checker) |
| [`Z3PulseJustificationChecker.fst`](Z3PulseJustificationChecker.fst) | Pulse decision procedures for modus ponens / unit resolution |
| [`Z3PulseProofCheckerTests.fst`](Z3PulseProofCheckerTests.fst) | Cross-theory sample derivations, run through both checkers above, including rejection tests, plus an array-theory derivation and a generic trusted-`Rewrite`-leaf collector (`collect_rewrite_leaves`) |
| [`Z3InterpretedProofChecker.fst`](Z3InterpretedProofChecker.fst) | Discharges (rather than assumes) `all_leaves_sound` for 4 example leaves (array/seq/bool/bv), by constructing a real semantic `interpretation value` and invoking the matching per-theory lemma directly |
| [`Z3PatternMatchedProofChecker.fst`](Z3PatternMatchedProofChecker.fst) | Generalizes the array leaf above into a decidable pattern-matching compiler: recognizes `select(store(a,i,x),i) = x` for *arbitrary* nested `a`/`i`/`x` sub-expressions (not just named constants) and auto-discharges `all_leaves_sound` via a structural "type soundness" lemma plus `Z3ArrayTheory.lemma_select_store_same` |
| [`tools/extract_z3_proof.py`](tools/extract_z3_proof.py) | Uses Z3's Python front-end to produce a real proof object (from a built-in example or an arbitrary `.smt2` file path), extracts its equational subtree, pretty-prints it into `proof`/`expr` F* literals, and shells out to `fstar.exe` to run the Pulse checker on it |
| [`Z3ExtractedProof.fst`](Z3ExtractedProof.fst) | Auto-generated (regenerate via `python tools/extract_z3_proof.py --out Z3ExtractedProof.fst`) -- the literal transcription of a real Z3 proof object produced for `not(not(x)) == x`, committed as a snapshot of the pipeline's output |
| [`tools/test_not_not.smt2`](tools/test_not_not.smt2), [`Z3ExtractedProof_FromFile.fst`](Z3ExtractedProof_FromFile.fst) | Same `not(not(x)) == x` example, but driven from an `.smt2` file path instead of a built-in Python formula |
| [`tools/test_bvand_self.smt2`](tools/test_bvand_self.smt2), [`Z3ExtractedProof_Bv.fst`](Z3ExtractedProof_Bv.fst) | A larger `.smt2`-driven example (`bvand y y == y`), 12 proof nodes / 11 expr nodes, that surfaced and validated the fuel/`assert_norm` fix described above |

All three files type-check cleanly with the standard toolchain
invocation (`fstar.exe --smt <z3 4.13.3 binary> <File>.fst`), with zero
errors; remaining diagnostics are pre-existing unrelated warnings from
`Z3AstTheory.fst` (the `alloc`/`free` deprecation warnings previously
noted here no longer occur -- see "Pulse lessons" above).
