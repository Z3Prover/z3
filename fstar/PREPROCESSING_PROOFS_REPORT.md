# Preprocessing Proof-Production Formalization Report

Formalization file: [`fstar/Z3PreprocessingProofTheory.fst`](Z3PreprocessingProofTheory.fst)
(built on the pre-existing generic AST model
[`fstar/Z3AstTheory.fst`](Z3AstTheory.fst) and reusing
[`fstar/Z3SimplifierTheory.fst`](Z3SimplifierTheory.fst)'s quantifier
distributivity lemmas).

## Relationship to `PROOF_REWRITER_REPORT.md`/`PROOF_JUSTIFICATIONS_REPORT.md`

Two sibling reports in this directory, [`PROOF_REWRITER_REPORT.md`](PROOF_REWRITER_REPORT.md)
(`Z3ProofTheory.fst`) and [`PROOF_JUSTIFICATIONS_REPORT.md`](PROOF_JUSTIFICATIONS_REPORT.md)
(`Z3ProofJustifications.fst`), independently formalize much of the same
kernel inference-rule layer this report covers — `Z3ProofTheory.fst`
via an explicit proof-term datatype and well-formedness/soundness
theorem for `PR_REFLEXIVITY`/`PR_SYMMETRY`/`PR_TRANSITIVITY`/
`PR_MONOTONICITY`/`PR_REWRITE`, anchored to `rewriter_def.h`'s call
sites; `Z3ProofJustifications.fst` via a standalone propositional
sub-language, anchored to `smt_justification.cpp`'s call sites, for
`PR_MODUS_PONENS`/`PR_MODUS_PONENS_OEQ`/`PR_UNIT_RESOLUTION`/
`PR_AND_ELIM`/`PR_NOT_OR_ELIM`. This report takes a different
anchor point — `ast/simplifiers`' `supports_proofs()` survey and
`dependent_expr_simplifier::mp` — and a different, flatter
representation (implication lemmas stated directly over
`Z3AstTheory.eval`, with no dedicated proof-term datatype), so the two
bodies of work are not literally the same F* code; where they overlap
in *content* (reflexivity/symmetry/transitivity/monotonicity/
and_elim/not_or_elim/modus_ponens), that overlap is intentional
cross-validation via an independently-structured model, not
duplication to be reconciled — both independently conclude the same
rules are sound. The genuinely new material here, not covered by
either sibling report, is: the `ast/simplifiers`-wide
`supports_proofs()` survey and the `dominator_simplifier.cpp` gating
observation; `PR_COMMUTATIVITY`; `PR_QUANT_INTRO`; `PR_PUSH_QUANT`
(via direct reuse of `Z3SimplifierTheory.fst`); `PR_IFF_TRUE`/
`PR_IFF_FALSE`/`PR_IFF_OEQ`; and the pipeline-composition capstone
tied specifically to `dependent_expr_simplifier::mp` across a whole
preprocessing run.

## Scope: what question does this audit answer?

Every other audit in this directory (bool/arith/bv/seq/array/datatype/
fpa/pb/recfun/finite-set rewriters, the two `ast/simplifiers` passes)
answers *"is this concrete rewrite `s -> t` semantics-preserving?"*.
This audit answers a different, complementary question: *when Z3
justifies such a rewrite with a `proof*` object (so that the rewrite
can participate in a certified proof of `unsat`, or be checked by
`proof_checker.cpp`/an external proof checker), is the **inference
rule** used to build that justification itself sound, and does
chaining many such justifications across a whole preprocessing
pipeline preserve soundness end-to-end?* This is the kernel-level
("logical framework") layer underneath the theory-level rewrites;
the two questions are independent and both are needed for the overall
claim "Z3's preprocessing is sound, including when it emits a proof
object."

### Where does preprocessing produce proofs, and where doesn't it?

`src/ast/simplifiers/dependent_expr_simplifier::supports_proofs()`
(declared in `dependent_expr_state.h`, default `false`) gates this: a
simplifier that does not override it to `true` is skipped entirely by
`dependent_expr_state_tactic` whenever `proofs_enabled()`
(`dependent_expr_state_tactic.h:130-134`), rather than running without
a proof. Surveying every file in the directory:

| `supports_proofs()` | Files |
|---|---|
| **`true`** (overridden) | `bit2int.h`, `bv_divrem_bounds.h`, `der_simplifier.h`, `distribute_forall.h`, `elim_term_ite.h`, `euf_completion.h`, `pull_nested_quantifiers.h`, `rewriter_simplifier.h`, `solve_eqs.h`, `extract_eqs.cpp` |
| **`false`** (explicitly overridden) | `bound_simplifier.h`, `randomizer.h` |
| **`false`** (default, not overridden) | `bit_blaster.h`, `blast_term_ite_simplifier.h`, `bv1_blaster.h`, `bv_elim.h`, `bv_slice.h`, `card2bv.h`, `cnf_nnf.h`, `demodulator_simplifier.h`, `dominator_simplifier.h`, `elim_bounds.h`, `elim_unconstrained.h`, `eliminate_predicates.h`, `factor_simplifier.h`, `flatten_clauses.h`, `fold_unfold.h`, `injectivity_simplifier.h`, `lambda_simplifier.h`, `leibniz_simplifier.h`, `max_bv_sharing.cpp`, `propagate_values.h`, `push_ite.h`, `recfun_finder.h`, `reduce_args_simplifier.cpp`, `refine_inj_axiom.h`, `then_simplifier.h` |

`dominator_simplifier.cpp` is the one file in the third group that
*does* nonetheless construct `m.mk_rewrite`/`m.mk_modus_ponens` proof
terms internally (its `reduce()` builds a proof whether or not
`supports_proofs()` is overridden) — but since the base class still
reports `supports_proofs() == false`, the tactic driver may skip it
rather than run it under `proofs_enabled()`, so this file's own proof
construction is currently *dead code* reachable only if some other
caller invokes it directly outside the `dependent_expr_state_tactic`
gate. This file formalizes the inference rules it would need *if* it
were reachable (`PR_REWRITE` + `PR_MODUS_PONENS`, both covered below),
but does not attempt to fix the apparent gating inconsistency — this
is a C++ architecture question, not a soundness question, and is
called out here only because it surfaced during the survey.

### How do proof-enabled simplifiers build their proofs?

Reading every `true`-row file's `reduce()`:

- **Nine of the ten** (`bit2int`, `bv_divrem_bounds`, `der_simplifier`,
  `elim_term_ite`, `euf_completion`, `pull_nested_quantifiers`,
  `rewriter_simplifier`, `solve_eqs`, `extract_eqs`) delegate the
  per-rewrite-step proof construction to the generic `rewriter_tpl`
  engine (`ast/rewriter/rewriter_def.h`, out of scope of this audit —
  it is shared infrastructure, not specific to preprocessing), which
  internally builds one `m.mk_rewrite(s,t)`/`m.mk_oeq_rewrite(s,t)`
  trusted-axiom leaf per atomic theory-rewriter simplification, then
  composes these upward via `m.mk_congruence`/`m.mk_monotonicity`
  (`PR_MONOTONICITY`, one changed argument position at a time) and
  `m.mk_transitivity` (`PR_TRANSITIVITY`, chained steps). `solve_eqs`/
  `extract_eqs` additionally thread the substitution step's own proof
  through this same machinery. `euf_completion.cpp` is the most
  involved of these: its congruence-closure replay builds explicit
  transitivity chains and `prove_eq`/`prove_conflict` helpers, but the
  *rules* it ultimately invokes are the same `PR_TRANSITIVITY`/
  `PR_MONOTONICITY`/`PR_MODUS_PONENS` family covered here.
- **`distribute_forall.cpp`** is the one exception: its
  `reduce_quantifier` callback directly calls `m.mk_push_quant`
  (`PR_PUSH_QUANT`) rather than going through the generic rewriter.
- Every one of the ten then combines its own step's proof with the
  dependent_expr's *existing* justification via the shared
  `dependent_expr_simplifier::mp(a,b) = m.mk_modus_ponens(a,b)`
  (`dependent_expr_state.h`) — i.e. `PR_MODUS_PONENS` is the one rule
  that is architecturally guaranteed to be used by *every* proof-
  producing simplifier, regardless of which rule justified its own
  step.

### What `src/ast/proofs/proof_checker.cpp` actually checks

`proof_checker::check1_basic` is a **structural, rule-shape** checker:
for each proof DAG node it pattern-matches the node's premises' facts
against the exact shape its `decl_kind` (`PR_REFLEXIVITY`,
`PR_SYMMETRY`, `PR_TRANSITIVITY`, `PR_MODUS_PONENS`, `PR_MONOTONICITY`,
`PR_QUANT_INTRO`, `PR_PUSH_QUANT`, `PR_AND_ELIM`, `PR_NOT_OR_ELIM`,
`PR_COMMUTATIVITY`, `PR_IFF_TRUE`/`PR_IFF_FALSE`, `PR_IFF_OEQ`,
`PR_MODUS_PONENS_OEQ`, ...) requires, and rejects malformed shapes —
but it does **not** re-derive semantic truth. In particular
`PR_REWRITE`/`PR_OEQ_REWRITE` (and `PR_DEF_AXIOM`) are **trusted
leaves**: the checker confirms the conclusion has the shape of an
equivalence (or, for `PR_DEF_AXIOM`, is simply accepted), then defers
the actual rewrite's correctness to an external `side_conditions` list
for separate verification — the kernel has no theory-specific
knowledge with which to check a concrete rewrite itself. This is
exactly the gap this project's other audits close, rewrite rule by
rewrite rule; see `lemma_pr_rewrite_delegates` below for the precise
hand-off statement.

`PR_HYPOTHESIS`/`PR_LEMMA`/`PR_UNIT_RESOLUTION` are SAT-proof-logging
rules (open hypotheses/resolution over learned clauses) that never
arise in the simplifier-produced proofs covered here (preprocessing
only ever starts from closed top-level assertions) and are out of
scope.

## What was formalized and proved

`Z3PreprocessingProofTheory.fst` formalizes every `PR_*` rule actually
used by the recipe above, as an F* lemma whose premises/conclusion
match `proof_checker.cpp`'s structural shape for that rule and whose
proof shows the shape is also *semantically* sound (i.e. a model
satisfying the premises necessarily satisfies the conclusion, under
`Z3AstTheory.fst`'s generic `eval`):

| Rule | Lemma | Shown |
|---|---|---|
| `PR_REFLEXIVITY` | `lemma_pr_reflexivity` | `e ~ e` always |
| `PR_SYMMETRY` | `lemma_pr_symmetry` | `t1~t2 ==> t2~t1` |
| `PR_TRANSITIVITY`/`PR_TRANSITIVITY_STAR` | `lemma_pr_transitivity` | `t1~t2 /\ t2~t3 ==> t1~t3` |
| `PR_COMMUTATIVITY` | `lemma_pr_commutativity` | `f` symmetric in its 2 args `==> f(a,b)~f(b,a)` |
| `PR_MONOTONICITY` | `lemma_pr_monotonicity` (+ `eval_args_eq`/`lemma_eval_args_eq_sound`) | pairwise-equivalent argument lists `==>` equivalent applications |
| `PR_QUANT_INTRO`/`PR_OEQ_QUANT_INTRO` | `lemma_pr_quant_intro` | same kind/bound sorts + pointwise-equivalent bodies under every binder extension `==>` equivalent quantifiers (reuses the exact `quant_extensional`-based argument `Z3AstTheory.lemma_closed_eval_env_irrelevant` already uses for its own `Quantifier` case) |
| `PR_AND_ELIM` | `lemma_pr_and_elim` (+ `is_and_decl`, `all_eq`, `lemma_all_eq_mem`) | `(and args)` holds `/\ fact in args ==> fact` holds |
| `PR_NOT_OR_ELIM` | `lemma_pr_not_or_elim` (+ `is_or_decl`/`is_not_decl`, `any_eq`, `lemma_any_eq_mem`) | `(not (or args))` holds `/\ t in args ==> (not t)` holds |
| `PR_MODUS_PONENS` | `lemma_pr_modus_ponens` (+ `is_implies_decl`/`is_iff_decl`) | `fml0` holds `/\` (`(implies fml0 fact)` or `(iff fml0 fact)`) holds `==> fact` holds |
| `PR_MODUS_PONENS_OEQ` | `lemma_pr_modus_ponens_oeq` | same, for the `oeq`-tagged shape |
| `PR_IFF_TRUE` | `lemma_pr_iff_true` | `fml` holds `==> (iff fml true)` holds |
| `PR_IFF_FALSE` | `lemma_pr_iff_false` | `(not fml)` holds `==> (iff fml false)` holds |
| `PR_IFF_OEQ` | `lemma_pr_iff_oeq` | `(iff t1 t2)` holds `==> (~ t1 t2)` holds |
| `PR_PUSH_QUANT` | *(reused, not restated — see below)* | `distribute_forall.cpp`'s claim is a direct corollary of `Z3SimplifierTheory.lemma_forall_distributes_and_list`/`lemma_exists_distributes_or_list`, instantiated at the AST/environment level |
| `PR_REWRITE`/`PR_OEQ_REWRITE` | `lemma_pr_rewrite_delegates` | makes precise *what* side condition must be separately established (by the theory-specific audits) for the kernel's trust in this leaf to be justified |
| (pipeline composition) | `chain_sound`/`lemma_chain_sound` | iterating `mp`/`mk_modus_ponens` (`PR_TRANSITIVITY` in disguise) across a whole list of pipeline steps preserves soundness from the very first formula to the very last |

All 15 lemmas plus the 2 chain/congruence helper lemmas (`lemma_eval_args_eq_sound`,
`lemma_all_eq_mem`, `lemma_any_eq_mem`) type-check and discharge every
verification condition with **zero `admit`/`assume`**. The Boolean
connectives (`and_d`/`or_d`/`not_d`/`implies_d`/`iff_d`) are modeled as
explicit semantic hypotheses on a concrete `interpretation value`
(`is_and_decl`, etc.), in the same style `Z3SimplifierTheory.fst`'s
`quant_extensional` is a semantic hypothesis rather than something
baked into `Z3AstTheory.fst`'s deliberately theory-agnostic
`interpretation` record — this keeps `Z3AstTheory.fst` itself
unmodified and reusable by every other audit that imports it.

### Design notes

- **Why no new AST/semantics infrastructure was needed beyond one
  small Boolean-interpretation layer.** The equivalence-rule family
  (reflexivity/symmetry/transitivity/monotonicity/quant_intro/
  commutativity/iff_oeq) only ever needs `eval i a rho == eval i b
  rho`-style denotational equality, which `Z3AstTheory.fst`'s fully
  abstract `value`/`eval` already expresses with no further
  assumptions — these lemmas hold for *any* interpretation whatsoever.
  Only the truth-level rules (modus ponens, and/not-or-elim, iff_true/
  iff_false) need to talk about a formula "holding", which requires
  picking out a distinguished Boolean truth value and axiomatizing
  and/or/not/implies/iff's interpretations against it; this is the one
  genuinely new piece of infrastructure this file adds.
- **`PR_PUSH_QUANT` needed no new lemma.** `distribute_forall.cpp`'s
  own proof-production path claims exactly `forall x.(F1/\.../\Fn) <=>
  (forall x.F1)/\.../\(forall x.Fn)` (dually for `exists`/`or`), which
  is precisely `Z3SimplifierTheory.lemma_forall_distributes_and_list`/
  `lemma_exists_distributes_or_list`, already proved fully generically
  over an abstract domain `dom`. Instantiating `dom :=
  (vs:list value{length vs = length bound_sorts})` (one value per
  bound variable) and each predicate `p_k vs := eval i body_k (shift
  vs rho) == vtrue` turns that existing generic theorem directly into
  the ground fact `PR_PUSH_QUANT` needs — restating it would only
  duplicate the proof with concrete `p_k`'s plugged in, which this
  project's convention (see `SIMPLIFIERS_REPORT.md`'s own treatment of
  `distribute_forall.cpp`) already treats as unnecessary repetition
  rather than new content.
- **`PR_REWRITE`/`PR_OEQ_REWRITE` are intentionally *not* proved
  sound in general** — they cannot be: `proof_checker.cpp` itself
  treats them as trusted, and a rewrite is only as sound as the
  concrete theory-specific rule that produced it. `lemma_pr_rewrite_delegates`
  states the hand-off precisely (`eval i s rho == eval i t rho` is
  exactly the side condition that must be established) and is
  deliberately trivial to prove (`()`) — its value is documentary,
  pinning down *which* fact every per-rewriter audit in this directory
  (`Z3BoolRewriter.fst`, `Z3ArithRewriter.fst`, `Z3BvRewriter.fst`,
  `Z3SeqRewrites.fst`, `Z3ArrayTheory.fst`, `Z3DatatypeTheory.fst`,
  `Z3FpaRewrites.fst`, `Z3PbTheory.fst`, `Z3RecfunTheory.fst`,
  `Z3FiniteSetTheory.fst`, ...) is actually establishing when it proves
  a concrete rewrite rule correct, and connecting that body of work
  explicitly to the kernel's proof-checking layer for the first time
  in this project.
- **The capstone (`chain_sound`/`lemma_chain_sound`) is the
  architecturally load-bearing result.** It shows that
  `dependent_expr_simplifier::mp`'s repeated `mk_modus_ponens`
  composition across an entire preprocessing *pipeline* — not just one
  simplifier's one step — cannot silently accumulate unsoundness:
  if every individual pass in the pipeline is justified by one of the
  rules above (so `chain_sound` holds of the list of intermediate
  formulas), the first and last formulas in the pipeline are
  equivalent. The proof is a straightforward structural induction,
  but it is the fact that actually matters end-to-end: no individual
  `PR_MODUS_PONENS`/`PR_TRANSITIVITY` node being locally sound would
  matter if composing thousands of them across a real preprocessing
  pipeline could still drift.

### Kernel hardening: `proof_checker::check1_basic`'s `PR_PUSH_QUANT` case was dead-rejecting everything

Re-examining this rule's *actual* checker code (as opposed to the
semantic claim formalized above, which was always true) while auditing
`distribute_forall` on request turned up a genuine, independent bug in
`src/ast/proofs/proof_checker.cpp`, now fixed:

- The old code's success path (`match_proof`/`match_fact`/`match_iff`/
  `match_and` on both sides + a per-conjunct `for` loop checking each
  `terms2[i]` is a matching quantifier over `terms1[i]`) had **no
  `return true` anywhere** — after the loop finished without hitting
  its internal early `return false`, control simply fell out of the
  `if` block into the function's shared `UNREACHABLE(); return false;`
  tail. That means **every** `PR_PUSH_QUANT` proof, including a
  perfectly well-formed one, was unconditionally rejected (aborting
  the process via `UNREACHABLE()`, per this function's convention) —
  the structural check computed the right answer and then discarded
  it. This had gone unnoticed because nothing in this project's test
  suite previously round-tripped a real `PR_PUSH_QUANT` node through
  `proof_checker::check`.
- Separately, the old code only ever matched the `and`-shaped
  conjunction (`match_and` on both sides of the `iff`) — but
  `distribute_forall_simplifier` (`src/ast/simplifiers/
  distribute_forall.cpp:72-76`) also produces the dual `exists`/`or`
  shape (`(exists X (or F1 .. Fn)) <-> (or (exists X F1) .. (exists X
  Fn))`), which `match_and` can never match, so that shape was
  (silently, via the same dead `UNREACHABLE()` fall-through) also
  always rejected.
- The fix accepts whichever connective (`and` or `or`) the outer
  quantifier's body actually uses, requires the *same* connective on
  the right-hand side, additionally checks each `terms2[i]`'s
  quantifier *kind* matches the outer quantifier's kind (`forall` vs.
  `exists` — not checked at all previously, a latent soundness gap in
  its own right since nothing stopped a proof from claiming a
  `forall`-to-`exists` "distribution"), and `return true`s on success
  instead of falling through.
- Verified: `ninja -C build shell test-z3` rebuilds cleanly, all 112
  unit tests pass, and a new `tst_push_quant`
  (`src/test/proof_checker.cpp`) constructs genuine instances of both
  the `forall`/`and` and `exists`/`or` shapes via the real
  `ast_manager::mk_push_quant` and confirms `proof_checker::check`
  now accepts both (previously both would have aborted the process).
  A live `(check-sat-using (then distribute-forall smt))` run under
  `(set-option :produce-proofs true)` over a quantified `unsat` query
  still returns `unsat`, confirming no regression to real end-to-end
  proof production (this path doesn't itself call `proof_checker` by
  default, so it was unaffected by the bug, but remains a useful
  smoke test that the fix doesn't reject genuine Z3-produced proofs).
- This is now the second time auditing a `rewriter_def.h`-adjacent
  proof-production path against `check1_basic` as "ground truth" (see
  `PROOF_REWRITER_REPORT.md`'s `PR_QUANT_INTRO`/`PR_BIND` kernel-
  hardening note for the first) has found that the *semantic* claim
  F* independently verifies was always true, while Z3's own kernel
  checker had a structural bug preventing it from ever actually
  confirming that — i.e. the F* audit's "cross-checked against
  `proof_checker.cpp` as ground truth" methodology is doing real work
  catching bugs in the ground truth itself, not just in the rewriters
  being audited.

## Deferred / out of scope

- **`rewriter_tpl`'s own internal proof-term construction**
  (`ast/rewriter/rewriter_def.h` — exactly how a `mk_rewrite`/
  `mk_congruence`/`mk_transitivity` node gets built as the engine walks
  a term bottom-up) is shared infrastructure, not specific to
  `ast/simplifiers`, and is out of scope here; this audit covers the
  rule *shapes* it produces, not its tree-walking implementation.
- **`euf_completion.cpp`'s congruence-closure proof replay** in full
  detail (its `get_canonical`/`prove_eq`/`prove_conflict` helpers) is
  only covered here at the rule level (`PR_TRANSITIVITY`/
  `PR_MONOTONICITY`/`PR_MODUS_PONENS`, all proved); the specific
  algorithm that decides *which* chain of congruence steps to emit is
  a search/engineering concern, not an independent soundness
  obligation, matching how other audits in this directory treat
  search/scheduling logic as out of scope.
- **`PR_DEF_AXIOM`** is a trusted axiom leaf by construction (it
  asserts a fact is a pre-registered axiom of some theory, not derived
  from other proof nodes) and has no independent soundness content to
  formalize beyond "whatever theory registered this axiom must itself
  be sound" — already the implicit premise of every theory-specific
  audit in this directory.
- **The `dominator_simplifier.cpp` gating inconsistency** noted above
  (it builds proof terms despite `supports_proofs()==false`) is flagged
  for awareness but is a C++ driver-gating question, not something an
  F* soundness proof can resolve.

## Verification

```
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3PreprocessingProofTheory.fst
```

`Verified module: Z3PreprocessingProofTheory`, zero errors, zero
`admit`/`assume`.
