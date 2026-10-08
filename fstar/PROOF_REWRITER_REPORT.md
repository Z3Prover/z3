# F* Formalization of Z3's Proof-Term Calculus and `rewriter_def.h`'s Proof Production — Coverage Report

See [`README.md`](README.md) for the top-level index of this F*
formal-verification audit series.

Z3 can optionally produce, alongside every rewrite it performs, a
*proof term* (a `proof*`, itself an ordinary `expr*` tagged with a
`basic_op_kind` such as `PR_REWRITE`/`PR_TRANSITIVITY`/
`PR_MONOTONICITY`) justifying that rewrite. `src/ast/ast.h`/`ast.cpp`
define the proof-term constructors and the *shape* each kind must have;
`src/ast/proofs/proof_checker.cpp`'s `check1_basic` is Z3's own
internal self-checker, the authoritative executable specification of
what makes each proof-term kind *well-formed*. `src/ast/rewriter/
rewriter_def.h` is the generic bottom-up rewriting engine shared by
every Z3 theory rewriter (`bool_rewriter`, `arith_rewriter`,
`bv_rewriter`, `seq_rewriter`, `th_rewriter`, ...); when proof
generation is enabled (`ProofGen = true`), it is the single place in
Z3 responsible for *assembling* a proof term for every rewrite step
out of the smaller proof terms individual theory plugins hand it.

This report covers:

1. A proof-term calculus, `Z3ProofTheory.fst`, modeling the fragment of
   `basic_op_kind` that `rewriter_def.h` actually constructs
   (`PR_REFLEXIVITY`/`PR_SYMMETRY`/`PR_TRANSITIVITY`/`PR_MONOTONICITY`/
   `PR_REWRITE`), together with a well-formedness/conclusion-extraction
   judgment (`fact`) designed to agree with `proof_checker::
   check1_basic`.
2. Smart constructors (`mk_refl`/`mk_sym`/`mk_trans`/`mk_congr`/
   `mk_rewrite_leaf`) reproducing `ast_manager::mk_reflexivity`/
   `mk_symmetry`/`mk_transitivity`/`mk_congruence`
   (`mk_monotonicity`)/`mk_rewrite` exactly (including
   `mk_transitivity`'s double-negation "fixup" special case), proved to
   always produce well-formed output from well-formed input.
3. A soundness theorem (`lemma_proof_sound`): under *any* denotational
   interpretation of terms (`Z3AstTheory.fst`'s `interpretation`/
   `eval`), a well-formed proof tree whose `PR_REWRITE` leaves are all
   individually sound denotes a true equation.
4. A site-by-site mapping of every proof-term-constructing call in
   `rewriter_def.h` to the lemma that establishes it is well-formed.

Proof file: [`Z3ProofTheory.fst`](Z3ProofTheory.fst) (builds on
[`Z3AstTheory.fst`](Z3AstTheory.fst) for terms/semantics).

Toolchain used: [F*](https://github.com/FStarLang/FStar) `v2026.09.27`
(Windows x64) with Z3 `4.13.3` as the SMT backend:

```
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3ProofTheory.fst
```

Type-checks and discharges all verification conditions with **no
`admit`/`assume`/axioms**.

## Representation

- Terms (`expr`) and their semantics (`interpretation value`/`eval`)
  are reused unchanged from `Z3AstTheory.fst`.
- `proof` models exactly the five `basic_op_kind`s `rewriter_def.h`
  constructs: `Refl e` (`PR_REFLEXIVITY`), `Sym p` (`PR_SYMMETRY`),
  `Trans p1 p2` (`PR_TRANSITIVITY`), `Congr f args1 args2 prfs`
  (`PR_MONOTONICITY`, always instantiated at `R = eq` since
  `rewriter_def.h` only ever calls `mk_congruence`, never
  `mk_oeq_congruence`), and `Rewrite s t` (`PR_REWRITE`, the trusted
  leaf). `oeq`-flavored facts, and the `PR_BIND`/`PR_QUANT_INTRO`
  kinds used only when rewriting fires underneath a binder, are out of
  scope (see "Not yet covered").
- `fact : proof -> option (expr & expr)` returns `Some (a, b)` (the
  conclusion `a = b`) exactly when `proof_checker::check1_basic` would
  accept the corresponding real proof term, and `None` otherwise.
  `Congr`'s acceptance condition (`congr_matched`/`find_matching_fact`,
  via the precomputed `facts_of prfs : list (option (expr & expr))`)
  mirrors `check1_basic`'s `PR_MONOTONICITY` case exactly: pointwise,
  either the two argument lists already agree at a position (no
  premise needed — the semantic counterpart of `rewriter_core::
  elim_reflex_prs` dropping implicit-reflexivity child proofs before
  `mk_congruence` is ever called) or *some* supplied premise proves
  exactly that position's equation, found by content (a linear search),
  not by position.

## Coverage by proof-term kind / smart constructor

| `.cpp` site | What it builds | Lemma(s) | Status |
|---|---|---|---|
| `ast_manager::mk_reflexivity` | `PR_REFLEXIVITY` leaf, `e = e` | `lemma_mk_refl_wf` | ✅ |
| `ast_manager::mk_symmetry` | `PR_SYMMETRY` wrapping; its `is_reflexivity`/`is_symmetry` short-circuit optimizations preserve the same conclusion as the general wrap | `lemma_mk_sym_wf`, `lemma_mk_sym_refl`, `lemma_mk_sym_sym` | ✅ |
| `ast_manager::mk_transitivity` (direct case, middle terms match) | `PR_TRANSITIVITY` chaining `a=b` and `b=d` into `a=d` | `lemma_mk_trans_wf_direct` | ✅ |
| `ast_manager::mk_transitivity` (double-negation fixup, both orientations) | an extra bridging `PR_REWRITE(not(not c), c)` (or symmetric) leaf inserted before chaining | `lemma_mk_trans_wf_bridge1`, `lemma_mk_trans_wf_bridge2` | ✅ |
| `ast_manager::mk_congruence`/`mk_monotonicity` (`R = eq`) | `PR_MONOTONICITY` over `App f args1`/`App f args2`, premises matched by content not position | `lemma_mk_congr_wf` | ✅ |
| `ast_manager::mk_rewrite` | `PR_REWRITE` leaf, `s = t` | `lemma_mk_rewrite_wf` | ✅ |
| (proof-calculus semantics, not a single `.cpp` site) | overall soundness: well-formed + all leaves sound ⟹ conclusion holds under any interpretation, for any environment | `lemma_proof_sound` (+ helpers `lemma_find_matching_sound`, `lemma_congr_args_sound`) | ✅ |

## `rewriter_def.h` call-site mapping

Every proof-term-constructing statement in `rewriter_def.h` calls one
of the five smart constructors above (it never builds a raw `PR_*`
node directly), so the table above's well-formedness lemmas cover
every site. Concretely:

| `rewriter_def.h` site | Smart constructor(s) used | Covered by |
|---|---|---|
| `process_const`, `BR_FAILED` fallback (implicit reflexivity when a leaf doesn't rewrite) | *(no proof constructed; `nullptr` is pushed, read as implicit reflexivity downstream — `rewrites_from`/`rewrites_to` treat a `nullptr` proof as trivially satisfying both)* | N/A (vacuous) |
| `process_const`, `BR_DONE`/retry path, no plugin-supplied proof | `mk_rewrite(t0, m_r)` | `lemma_mk_rewrite_wf` |
| `PROCESS_CHILDREN`, rebuilding `t` from rewritten children (`elim_reflex_prs` + `mk_congruence`) | `mk_congruence(t, new_t, num_prs, ...)` (`→ mk_congr`) | `lemma_mk_congr_wf` |
| `PROCESS_CHILDREN`, after `reduce_app`'s own rewrite on the rebuilt term, chaining the congruence step with the builtin rewrite step | `mk_transitivity(m_pr, m_pr2)` (`m_pr2` defaults to `mk_rewrite(new_t, m_r)` if the plugin supplied none) | `lemma_mk_trans_wf_direct`/bridge lemmas, `lemma_mk_rewrite_wf` |
| `PROCESS_CHILDREN`, `BR_REWRITEk` recursive re-visit, chaining the first two proof steps with the recursively-obtained one | `mk_transitivity(pr1, pr2)` | `lemma_mk_trans_wf_direct`/bridge lemmas |
| `PROCESS_CHILDREN`, macro/definition expansion chaining | `mk_transitivity(m_pr, def_pr)` | `lemma_mk_trans_wf_direct`/bridge lemmas |
| `PROCESS_CHILDREN`, "preserve the congruence proof from the rewritten children" fallback (`fr.m_new_child`, no further builtin rewrite fired) | `mk_rewrite(t, m_r)` | `lemma_mk_rewrite_wf` |
| `REWRITE_BUILTIN` state, chaining the two outstanding proof-stack entries | `mk_transitivity(pr1, pr2)` | `lemma_mk_trans_wf_direct`/bridge lemmas |
| `process_quantifier`, rewriting a quantifier without pattern-driven rewriting underneath a binder (`m_pr` absent) | `mk_rewrite(q, new_q)` | `lemma_mk_rewrite_wf` |
| `process_quantifier`, chaining with `reduce_quantifier`'s own proof | `mk_transitivity(m_pr, pr2)` | `lemma_mk_trans_wf_direct`/bridge lemmas |
| `main_loop`/`resume_core`, trivial top-level reflexivity when nothing changed | `mk_reflexivity(t)`/`mk_reflexivity(m_root)` | `lemma_mk_refl_wf` |

`rewriter.cpp`'s own debug invariants `rewrites_from(t, pr)`/
`rewrites_to(t, pr)` (asserted throughout `rewriter_def.h` via
`SASSERT`) are exactly the claim `fst (fact pr) == t`/`snd (fact pr)
== t` this report's `fact` function computes — i.e. this file's `fact`
is the F* counterpart of what those two C++ debug helpers check at
runtime (only for the one proof at hand, not recursively), while
`lemma_proof_sound` additionally establishes the *semantic* content of
that claim given sound leaves.

## Soundness theorem

`lemma_proof_sound (i : interpretation value) (p : proof) (rho : env
value)`: if `fact p = Some (a, b)` (i.e. `p` is well-formed) and every
`Rewrite s t` leaf reachable inside `p` satisfies `eval i s rho == eval
i t rho` for all `rho` (`all_leaves_sound i p`), then `eval i a rho ==
eval i b rho`. This is the proof-calculus-layer half of "`rewriter_
def.h`'s proof output is a correct derivation" — the other half, that
every individual rewriter plugin's own `PR_REWRITE` leaves really are
semantically sound for the specific `(s, t)` pairs that plugin's
`reduce_app` produces, is exactly what this project's other rewriter
correctness reports (`BOOL_REWRITER_REPORT.md`,
`ARITH_REWRITER_REPORT.md`, `BV_REWRITER_REPORT.md`,
`SEQ_REWRITE_REPORT.md`, `DATATYPE_REWRITER_REPORT.md`, etc.)
separately establish. Together, they show: *if* every theory plugin's
rewrites are sound (established elsewhere) *and* `rewriter_def.h`
assembles them using only its smart constructors (true by inspection:
it never builds a raw `PR_*` node), *then* the final proof term
`rewriter_def.h` returns is both well-formed and denotes a true
equation.

The one non-trivial semantic fact this file's `mk_trans` relies on but
does not itself discharge is the double-negation bridge: whenever
`mk_transitivity`'s fixup fires, it inserts a `PR_REWRITE(not(not c),
c)` leaf, whose own soundness (`eval i (not(not c)) rho == eval i c
rho`, i.e. double-negation elimination under whatever Boolean
connective `not` is interpreted as) must hold for the `all_leaves_
sound` hypothesis to be satisfiable — this is a property of `Not`'s
interpretation (trivially true for the standard two-valued Boolean
semantics `bool_rewriter.cpp` implements, see `BOOL_REWRITER_REPORT.md`
§`mk_not`), not an independent axiom of this file.

## Not yet covered

- **`PR_BIND`/`PR_QUANT_INTRO`** (`ast_manager::mk_bind_proof`/
  `mk_quant_intro`, used only by `rewriter_tpl::process_quantifier`
  when a rewrite fires underneath a quantifier's binder): these
  additionally need to reason about `Z3AstTheory.fst`'s
  `interp_quant`/environment-shifting machinery, which this file does
  not yet connect to the proof calculus. Deferred to a follow-up pass.
- **`oeq`-flavored facts** (`mk_oeq_reflexivity`/`mk_oeq_rewrite`/
  `mk_oeq_congruence`/`PR_IFF_OEQ`/`PR_MODUS_PONENS_OEQ`): never
  constructed by `rewriter_def.h` itself (only by other call sites in
  Z3, e.g. the simplifier/preprocessing pipeline's "observational
  equivalence" tracking), so out of scope for this report; `fact`
  treats every binary relation as a plain `eq`.
  `proof_checker::check1_basic`'s other ~30 `basic_op_kind` cases
  (`PR_MODUS_PONENS`, `PR_UNIT_RESOLUTION`, `PR_DEF_AXIOM`,
  `PR_TH_LEMMA`, `PR_HYPER_RESOLVE`, hypothesis/lemma/clause
  management, quantifier instantiation, Skolemization, ...) are
  produced by the SAT/SMT core and theory solvers, not by
  `rewriter_def.h`; verifying those is the subject of a separate,
  future "other proof-producing code" follow-up (theory lemmas/
  propagations, substitution, model-based quantifier instantiation,
  etc.), per this project's broader `followup-passes` task.
- **`mk_symmetry`'s/`mk_transitivity`'s internal proof-shape sharing**
  (e.g. that `is_symmetry(p)`'s unwrap literally returns the *same*
  `proof*` object as the original parent, saving an allocation): this
  report only verifies the *fact* each optimization establishes is the
  same as the general case, not the term-sharing/allocation behavior
  itself (irrelevant to soundness, only to performance).

## Summary

This report proves 6 top-level smart-constructor well-formedness
lemmas plus the central soundness theorem (`lemma_proof_sound`, with
2 supporting helper lemmas), covering every proof-term-constructing
call site in `src/ast/rewriter/rewriter_def.h` (and the quantifier
path in `process_quantifier` up to, but not including, the binder-
crossing `PR_BIND`/`PR_QUANT_INTRO` kinds). Combined with this
project's existing per-plugin rewrite-correctness reports (which
separately establish that every `PR_REWRITE` leaf's `(s, t)` pair is
semantically valid), this gives an end-to-end soundness argument for
proof terms produced during ordinary Z3 rewriting.
