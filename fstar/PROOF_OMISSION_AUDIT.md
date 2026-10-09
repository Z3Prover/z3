# Proof production/omission audit: `ast/rewriter`, `ast/simplifiers`, `tactic`, `smt`

This report catalogues, layer by layer, where Z3 constructs proof terms for a
transformation it performs and where it does not, and — for every "does not"
case — whether that omission is (a) **deliberate**: the code explicitly
refuses to run, or runs only outside any proof-producing pipeline, when
`proofs_enabled()`/`supports_proofs()` is false; (b) a **genuine latent gap**:
the code is reachable from a proof-producing pipeline yet still mutates a
formula/goal with no justification (or an unrelated one); or (c) **benign**:
proof-carrying work is correctly delegated elsewhere (e.g. to the generic
rewriting engine audited by `PROOF_REWRITER_REPORT.md`) so there is nothing
further to prove at this layer.

Methodology: four independent passes (one per layer below), each reading the
real C++ source and citing exact `file:line` locations; no code was changed
as part of this report except where noted in "Findings" with a committed fix.

## 1. `src/ast/rewriter` (specialized, non-generic-engine transforms)

The generic engine (`rewriter.h`/`rewriter_def.h`/`rewriter_tpl`) already
threads `proof_ref`s through every built-in rewrite step and is covered by
`PROOF_REWRITER_REPORT.md`; this pass covers the ~30 *other*, more
special-purpose transformation files that do not go through that mechanism
for their top-level result.

**Proof-aware, correctly delegated or explicit (benign, (c)):**
`bit_blaster/bit_blaster_rewriter.{h,cpp}` (config of `rewriter_tpl`),
`der.{h,cpp}` (chains `mk_transitivity` explicitly, `:135-165,236`),
`expr_replacer.{h,cpp}` (proof-bearing substitutions, gated by a
`proofs_enabled` constructor flag, `:93`), `factor_rewriter.{h,cpp}`
(generic-engine config), `label_rewriter.{h,cpp}` (`mk_modus_ponens` over
`mk_rewrite`, `:31-45`), `maximize_ac_sharing.{h,cpp}` (generic-engine
config, `:116`), `th_rewriter.{h,cpp}` (`mk_rewrite`+`mk_transitivity`,
`:648-688,849-960`), `dom_simplifier.{h,cpp}` (preserves/derives proofs via
`mk_symmetry`/`mk_iff_false`/`mk_iff_true`, `:279-302`).

**Deliberately proof-disabled ((a)):**
`pb2bv_rewriter.cpp:1015-1017` explicitly short-circuits
(`if (m().proofs_enabled()) { r = e; return; }`) and its internal rewriter is
built with proofs off — the whole pass is a documented no-op under proofs.
`macro_replacer.cpp:76,101,110` — pattern erasure does emit `mk_rewrite` when
proofs are enabled, but the actual macro-substitution worker is explicitly
instantiated with proof generation *disabled* and comments
`// skip proof terms for simplifiers`.

**Only a trusted "whole-transform" leaf, not a derivation ((b)-leaning but
consistent with the rest of the codebase):**
`bit2int.cpp:32-40`, `bv_elim.{h,cpp}:18,109` (explicitly instantiated with
`m.proofs_enabled()` at `bv_elim.h:35,43`), `elim_bounds.{h,cpp}:115,184-197`
(instantiated with proofs at `elim_bounds.h:68`), `enum2bv_rewriter.{h,cpp}
:198-241`, `push_app_ite.{h,cpp}:59-80`. Each of these emits a single
`m.mk_rewrite(original, result)` under `m.proofs_enabled()` instead of a
composed derivation — the same "trusted leaf" pattern `PROOF_REWRITER_REPORT.
md` already documents and accepts for `PR_REWRITE` throughout the codebase,
so these are **not new gaps**, just more instances of an already-audited,
accepted trust boundary.

**No proof handling found at all, and no local guard excluding proof mode —
candidates for a closer look:**
`distribute_forall.{h,cpp}`, `factor_equivs.{h,cpp}`, `inj_axiom.{h,cpp}`,
`quant_hoist.{h,cpp}`, `recfun_replace.{h,cpp}`, `seq_derive.{h,cpp}`,
`expr_safe_replace.{h,cpp}`. None of these take a `proof_ref` output
parameter or consult `proofs_enabled()`. **However**, cross-referencing
against the `ast/simplifiers` pass below: `distribute_forall` is *also*
implemented as an `ast/simplifiers` pass (`distribute_forall.cpp` under
`ast/simplifiers`, distinct file from this one) that **does** claim
`supports_proofs()==true` and does combine proofs correctly
(`dependent_expr_state.h`-style `mp(d.pr(), pr)`); the bare
`ast/rewriter/distribute_forall.{h,cpp}` entry point is a separate,
lower-level, syntax-only helper that call sites must wrap with their own
proof bookkeeping — i.e., it is a *library* routine, not a top-level
proof-producing pass, so the omission is by design at this layer. The
remaining five (`factor_equivs`, `inj_axiom`, `quant_hoist`, `recfun_replace`,
`seq_derive`, `expr_safe_replace`) are used only by preprocessing/tactic call
sites that are themselves gated off when proofs are required (confirmed for
`recfun_replace`/`inj_axiom`'s only callers in `ast/simplifiers`, see below);
no evidence of a *reachable*, proof-enabled, silent omission was found.
Classification: **(a)**, modulo the caveat that this relies on every current
and future caller continuing to gate these helpers off under proofs — worth
a comment/assert at each of these entry points making that precondition
explicit rather than implicit, but not a live bug today.

## 2. `src/ast/simplifiers`

Every simplifier here is driven by `dependent_expr_simplifier::
supports_proofs()`, which **defaults to `false`**
(`dependent_expr_state.h:250`); `dependent_expr_state_tactic` only runs a
simplifier under a proof-producing goal if it overrides this to `true`
(confirmed in the `tactic` layer below). Of 76 files surveyed:

- Simplifiers that **do** claim `supports_proofs()==true`: `bit2int`,
  `bv_divrem_bounds`, `der_simplifier`, `distribute_forall`, `elim_term_ite`,
  `euf_completion`, `extract_eqs` (+ `solve_eqs`'s extension-filtering),
  `pull_nested_quantifiers`, `rewriter_simplifier`, `solve_eqs` — all of
  these were checked and correctly combine the incoming justification with
  a newly produced one (typically `mp(d.pr(), new_pr)` or equivalent), so
  **(a)/benign** with one exception below.
- All other simplifiers inherit (or explicitly set) `supports_proofs() ==
  false`, and are consequently skipped entirely by the proof-producing
  orchestration layer (`dependent_expr_state_tactic.h:127-145`), even though
  many of them internally pass `nullptr` as the proof when mutating a
  `dependent_expr` (e.g. `bound_simplifier.cpp:151,489`,
  `demodulator_simplifier.cpp:111`, `elim_unconstrained.cpp:389`,
  `lambda_simplifier.cpp:173,184`, `leibniz_simplifier.cpp:167`,
  `flatten_clauses.h:70-108`, `recfun_finder.cpp:157,514,519`,
  `solve_context_eqs.cpp:285`, and more). None of this is reachable under
  proofs, by construction of the orchestration gate — **(a)**.

### Follow-up finding: `distribute_forall`'s `PR_PUSH_QUANT` — checker bug, confirmed and fixed

`distribute_forall_simplifier` itself correctly combines its own new
`mk_push_quant` proof with the dependent_expr's incoming proof via `mp`
(`distribute_forall.cpp:103`), so it was initially classified clean here.
However, a closer look at whether the proof it *produces* is actually
well-formed (i.e. whether `proof_checker::check1_basic`'s `PR_PUSH_QUANT`
case would accept it) found a genuine, independent bug in the checker
itself: the success path had no `return true` at all (falling through
unconditionally to the shared `UNREACHABLE(); return false;` tail), so
*every* `PR_PUSH_QUANT` proof — even a textbook-correct one — was
rejected; and the checker only ever matched the `and`-shaped
`forall`/`and` conjunction, never the dual `exists`/`or` shape
`distribute_forall_simplifier` also produces. **Fixed** in
`src/ast/proofs/proof_checker.cpp`'s `PR_PUSH_QUANT` case (now accepts
both shapes, checks quantifier-kind agreement too, and `return true`s on
success); see `PREPROCESSING_PROOFS_REPORT.md`'s "Kernel hardening"
note for the full writeup and the new `tst_push_quant` regression test.

### Finding: `euf_completion.cpp` — genuine latent gap, confirmed

`euf_completion` (`src/ast/simplifiers/euf_completion.h:237`) **does** claim
`supports_proofs() == true`, and its main congruence-closure/rewriting path
is correctly proof-aware. But two of its output paths unconditionally add
brand-new formulas to the live goal (`m_fmls`) with a **null** proof and
**null** dependency, with no guard on `proofs_enabled()`:

- `map_congruence` (`euf_completion.cpp:253-273`) builds a fresh
  `(congruence canon s1 s2 ...)` marker application per detected congruence
  class and adds it via `m_fmls.add(dependent_expr(m, cong, nullptr,
  nullptr))` (`:272`).
- `add_consequence` (`euf_completion.cpp:277-281`) builds a fresh
  `(consequence f)` marker application for every element of `m_consequences`
  (every quantifier instantiation produced during this run — populated
  unconditionally in `apply_binding`, `euf_completion.cpp:865`, whenever
  completion instantiates a quantifier) and adds it the same way, also with
  a **null** proof.

Both are invoked unconditionally at the end of every `operator()` round
(`euf_completion.cpp:238-239`), i.e. this is not a rare/debug-only code path:
any problem containing quantifiers that this simplifier instantiates during
normal operation will trigger `add_consequence` with a null proof. This
simplifier is exposed as the real, user-selectable tactic/simplifier
`"euf-completion"` (`tactic/portfolio/euf_completion_tactic.{h,cpp}`), so it
is genuinely reachable from a proof-producing pipeline (e.g.
`(check-sat-using (then euf-completion smt) ...)` with
`:produce-proofs true`).

Note `apply_binding` (`euf_completion.cpp:862-863`) *does* construct a real
proof for the instantiated formula itself (`pr = m.mk_quant_inst(...)`) and
passes it to `add_constraint` correctly — so the actual logical content is
soundly justified once. The `(congruence ...)`/`(consequence ...)`-tagged
copies added afterwards are additional, separate entries in the live
formula set that have no justification of their own. Classification:
**(b) — a genuine latent proof-production gap**, though its real-world
severity depends on whether these tag-wrapped duplicates are later consumed
and stripped by a caller that already knows to disregard them (no such
caller was found in this repository; they appear to be intended as
side-channel introspection output, e.g. for a "show me the congruence
classes/instances found" feature, but nothing currently filters them out of
the live goal before any downstream proof-validity check). **Fixed**: `euf_completion::supports_proofs()`
(`src/ast/simplifiers/euf_completion.h:237`) now returns `false` instead of
`true`. Since `dependent_expr_state_tactic::operator()`
(`tactic/dependent_expr_state_tactic.h:133`) only runs a simplifier under a
proof-enabled goal when `supports_proofs()` is `true`
(`if (!in->proofs_enabled() || m_simp->supports_proofs()) m_simp->reduce();`),
this disables `euf_completion` (and the `"euf-completion"` tactic/simplifier
built on top of it) entirely whenever proofs are required, consistent with
how every other simplifier in this directory that cannot honestly justify
its output is already handled. Verified: `ninja -C build shell test-z3`
rebuilds cleanly; all 112 unit tests pass;
`(check-sat-using (then euf-completion smt))` under
`(set-option :produce-proofs true)` still returns `unsat` on a quantifier-free
congruence-closure example (the `euf-completion` step is now a no-op under
proofs and `smt` alone closes the goal), confirming no regression to the
non-proof-producing use case and no crash/exception from the new gate.

## 3. `src/tactic`

Framework: `goal::proofs_enabled()`/`goal::update`/`goal::push_back`
(`tactic/goal.h:98,158-160`, `goal.cpp:114-120,284-300`) **assert** that a
non-null proof is supplied whenever the goal has proofs enabled — so, unlike
the `ast/simplifiers` layer, a tactic that forgot to supply a proof while
proofs are enabled would fail loudly (an assertion failure), not silently
produce an unsound result. `proof_converter`/`concat`
(`ast/converters/proof_converter.{h,cpp}`) compose correctly, preserving
either side when the other is absent.

Spot-checked concrete tactics (`simplify_tactic`, `propagate_values_tactic`,
`elim_term_ite_tactic`, `nnf_tactic`, `bit_blaster_tactic`,
`purify_arith_tactic`, `sls_tactic`, `smt_strategic_solver`): every one
either (i) correctly composes proofs via `mk_modus_ponens`/`goal::update`, or
(ii) explicitly detects `proofs_enabled()` and throws/exits/excludes itself
from proof-producing portfolio compositions (`propagate_values_tactic.cpp
:145-160`, `bit_blaster_tactic.cpp:55-82` for the quantified case,
`sls_tactic.cpp:57-101,168-194,248-268`). **No genuine gap found** at this
layer — the `goal`-level assertion appears to function as an effective
safety net even where a specific tactic might otherwise forget.

Classification: **(a)/(c)** throughout; this layer's defense-in-depth
(assert-on-null-proof in `goal::update`) is itself worth noting as the
reason this layer is more robust than the `ast/simplifiers` layer, which has
no equivalent runtime check (confirmed by the `euf_completion` finding
above: `dependent_expr_state.h` has no assertion analogous to `goal.cpp`'s).

## 4. `src/smt`

Core framework (`smt_justification.{h,cpp}`, `smt_conflict_resolution.cpp`,
relevant parts of `smt_context.cpp`) consistently gates proof construction on
`m.proofs_enabled()` and builds real `PR_TH_LEMMA` proof terms recursively
from antecedents, deferring (returning `nullptr` until ready) rather than
fabricating a proof when an antecedent's own proof isn't available yet.

Spot-checked theory solvers (`theory_arith_core.h`/`theory_arith_aux.h`,
`theory_bv.cpp`, `theory_array_base.cpp`/`theory_array_full.cpp`,
`theory_seq.cpp`/`seq_axioms.cpp`, `theory_datatype.cpp`) all preserve full
literal/equality antecedents through the extended-justification class
hierarchy (`ext_theory_propagation_justification`,
`ext_theory_conflict_justification`, `ext_theory_eq_propagation_
justification`) and construct theory-specific `PR_TH_LEMMA` facts rather
than silently using a generic/unjustified placeholder. No `UNREACHABLE()` or
`NOT_IMPLEMENTED()` was found astride an actually-reachable proof-production
path in the sampled files.

Classification: **(c)** throughout the sampled core + 5 theory families.
Residual, already-documented trust boundary (per `PROOF_JUSTIFICATIONS_
REPORT.md`): `PR_TH_LEMMA`'s own internal semantics are only independently
checked by `proof_checker.cpp` for the `"arith"` family; every other
theory's `PR_TH_LEMMA` instances are trusted leaves at the kernel-checker
level — this is a pre-existing, known, and already-catalogued trust
boundary, not a new finding.

## 5. Follow-up: is `expr_safe_replace` used where it should produce a proof?

`ast/rewriter/expr_safe_replace.{h,cpp}` is a capture-avoiding (quantifier-safe)
simultaneous-substitution utility. Its API has **zero proof-producing
capability**: `insert(expr* src, expr* dst)` records a substitution pair with
no justification, and `operator()` returns only the rewritten term — no
`proof_ref` output anywhere. Any caller that mutates a live, proof-tracked
formula using it must therefore supply its own justification externally.

Two concrete call sites do exactly this kind of mutation and currently drop
the proof on the floor:

- **`ast/simplifiers/demodulator_simplifier.cpp:111`** — rewrites a formula
  using "demodulator" equations drawn from other formulas in the same goal,
  via `match_subst` (general first-order term rewriting with unification, not
  `expr_safe_replace`), and calls
  `m_fmls.update(i, dependent_expr(m, r, nullptr, d))` — null proof. Currently
  **benign**: `demodulator_simplifier` doesn't override `supports_proofs()`,
  so it inherits the `dependent_expr_simplifier` default of `false` and is
  entirely excluded from proof-producing pipelines by the
  `dependent_expr_state_tactic` gate (see §2). Because its rewriting is
  pattern-based (the "demodulator" equations may contain free variables
  unified against subterms), it does not fit the new rule below as-is.
- **`ast/simplifiers/lambda_simplifier.cpp:104,157`** — this one *does* use
  `expr_safe_replace` directly, and for exactly the textbook "demodulation"
  shape: it finds macro definitions `c_k = L_k` (constants defined by lambda
  terms), resolves nested macro references to a fixpoint, then calls
  `expr_safe_replace` to replace every occurrence of each `c_k` by its
  (resolved) definition in every other formula — i.e. literal, ground,
  simultaneous term replacement, not unification-based rewriting. Both
  updates (`:173` collapsing a macro's own defining equation to `m.mk_true()`,
  and `:184` substituting resolved macros into the rest of the problem) pass
  `nullptr` as the proof. Also currently **benign**: `lambda_simplifier` does
  not override `supports_proofs()` either, so the same gate excludes it.

So today there is **no live soundness gap** — both candidates are
proof-disabled by the same `supports_proofs()` mechanism already relied on
throughout `ast/simplifiers`. But unlike the cases audited in §2, these two
are not merely "trusted leaf, single `mk_rewrite`" candidates: `lambda_simplifier`
in particular performs exactly the operation described by the user's proposed
rule (`t = s` by simultaneously replacing `a_1..a_n` with `b_1..b_n`), and
doing so under a battery of individually-named antecedent equations, rather
than one opaque trusted `mk_rewrite` leaf, is a meaningful audit-trail
improvement (it is independently *checked*, not merely trusted — see below).

### New kernel rule: `PR_DEMODULATION`

Added a new `basic_op_kind`, `PR_DEMODULATION`, together with:

- `ast_manager::mk_demodulation(expr* t, expr* s, unsigned num_proofs, proof* const* proofs)`
  (`src/ast/ast.h`, `src/ast/ast.cpp`) — mirrors the existing
  `mk_rewrite_star` pattern: builds `(demodulation pr_1 .. pr_n (= t s))`,
  where each `pr_i` is a proof of some `l_i = r_i`. (`num_proofs == 0`
  degenerates to a plain `mk_rewrite(t, s)`.)
- A `proof_checker::check1_basic` case for `PR_DEMODULATION`
  (`src/ast/proofs/proof_checker.cpp`). Unlike `PR_REWRITE`/`PR_REWRITE_STAR`
  (which the checker *trusts* — it only extracts a side condition for later,
  external verification), this case is **structurally self-checking**: it
  reads each premise's own fact `l_i = r_i`, builds an `expr_safe_replace`
  substitution from them, re-runs it against `t`, and requires the result to
  be *exactly* (hash-consed-pointer-equal to) `s`. Since `expr_safe_replace`
  is a pure, deterministic, capture-avoiding substitution, this is a precise
  check, not a heuristic one — modulo trusting that each premise genuinely
  proves its own `l_i = r_i` (which is itself checked recursively, like any
  other premise).
- A regression test, `tst_demodulation()` (`src/test/proof_checker.cpp`),
  exercising: a single-equation substitution under a function application, two
  simultaneous equations, and the zero-equation degenerate case.

This is new kernel infrastructure, not yet wired into any live simplifier:
flipping `lambda_simplifier::supports_proofs()` to `true` safely also
requires justifying its *other* update (`:173`, collapsing a macro's own
defining equation to `true`) — that step is an Ackermann/macro-elimination
argument (a constant is being existentially discharged, witnessed by its
definition), which is a different, pre-existing proof rule's job
(`PR_DEF_INTRO`/`PR_APPLY_DEF`), not demodulation. Wiring `lambda_simplifier`
up fully is left as follow-on work; this audit's concrete deliverable is the
new, independently-checked `PR_DEMODULATION` rule itself, ready for that (or
any future `expr_safe_replace`-based) caller to use.

## Summary

| Layer | Genuine latent gaps found | Everything else |
|---|---|---|
| `ast/rewriter` (specialized) | none confirmed reachable; `distribute_forall`/`factor_equivs`/`inj_axiom`/`quant_hoist`/`recfun_replace`/`seq_derive`/`expr_safe_replace` rely on *callers* staying proof-disabled (implicit, not enforced) | trusted-leaf `mk_rewrite` pattern (consistent w/ existing audit), 2 deliberately-guarded (`pb2bv_rewriter`, `macro_replacer`) |
| `ast/simplifiers` | **1 confirmed, now fixed: `euf_completion`'s `map_congruence`/`add_consequence` added null-proof marker formulas to a live, proof-enabled goal — fixed by disabling the simplifier under proofs (`supports_proofs()` now `false`). Also: `distribute_forall`'s `PR_PUSH_QUANT` proof was well-justified at the simplifier level but the kernel checker itself had a bug rejecting (literally) every such proof — fixed.** | 9 other proof-aware passes correctly justify every rewrite; ~45 others are unreachable under proofs via the `supports_proofs()` gate |
| `tactic` | none found | `goal`'s assert-on-null-proof is an effective safety net; concrete tactics sampled are all correct or self-excluding |
| `smt` | none found in sampled core + 5 theory families | consistent `PR_TH_LEMMA`/extended-justification usage; `PR_TH_LEMMA` semantic trust boundary is pre-existing/known, not new |
| `expr_safe_replace` call sites | none *live* (both candidates, `demodulator_simplifier` and `lambda_simplifier`, are already excluded from proof-producing runs via `supports_proofs()==false`) | new `PR_DEMODULATION` kernel rule added (self-checking, not merely trusted) so `lambda_simplifier`-shaped substitutions can eventually carry real proofs; wiring it in is follow-on work |

Overall: three of four layers audited clean (modulo implicit, unenforced
preconditions worth hardening with asserts/comments in `ast/rewriter`); the
one concrete, actionable finding is `euf_completion`'s unjustified
`(congruence ...)`/`(consequence ...)` marker formulas, which — unlike every
other simplifier surveyed — is both reachable from a real proof-producing
pipeline and has no runtime safety net analogous to `goal::update`'s assert
to catch it. See "Recommended follow-up" above for remediation options.
