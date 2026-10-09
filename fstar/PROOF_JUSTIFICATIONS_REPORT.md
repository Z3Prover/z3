# Proof justifications audit: `smt_justification.cpp`'s `PR_MODUS_PONENS`/`PR_UNIT_RESOLUTION`, and `PR_AND_ELIM`/`PR_NOT_OR_ELIM`

## Scope

This report is a follow-up to `PROOF_REWRITER_REPORT.md` (which covers
`src/ast/rewriter/rewriter_def.h`, the generic rewriting engine's proof
production) and addresses the next most significant proof-producing
site in Z3: `src/smt/smt_justification.cpp`, the layer that turns the
SMT core's `conflict_resolution` justification graph into `proof*`
objects. It formalizes the two combinators this file uses almost
exclusively — `ast_manager::mk_modus_ponens` (`PR_MODUS_PONENS`/
`PR_MODUS_PONENS_OEQ`) and `ast_manager::mk_unit_resolution`
(`PR_UNIT_RESOLUTION`) — and proves them *semantically* sound (not
just well-formed), since both are purely propositional inference rules
whose validity does not depend on which theory the literals come from.
It additionally covers two further propositional elimination rules
used by CNF-conversion/clausification code (`PR_AND_ELIM`/
`PR_NOT_OR_ELIM`), selected because — unlike most of the remaining
proof kinds surveyed below — `check1_basic` gives them real, checked
semantic content rather than accepting any well-typed fact outright.

New file: **`Z3ProofJustifications.fst`** (builds on `Z3ProofTheory.fst`
and `Z3AstTheory.fst`). Zero `admit`/`assume`.

## Why a separate semantic model from `Z3ProofTheory.fst`

`Z3ProofTheory.fst`'s `proof` type is specialized to *equational*
conclusions (`expr & expr` pairs), because that is all
`rewriter_def.h` ever derives. `PR_MODUS_PONENS`/`PR_UNIT_RESOLUTION`
instead combine arbitrary Boolean facts (an implication's consequent,
a clause's residual literal disjunction), so they don't fit that
type. Rather than generalize `Z3ProofTheory.fst`'s representation
(a large, invasive change), this file works directly over a small,
self-contained propositional sub-language (`not`/`and`/`or`/`implies`/
`=`/`~` (`oeq`)/`true`/`false` applied to opaque `expr` atoms) with a
concrete two-valued semantics, `blit_eval`/`bclause_eval`/`band_eval`
— the same scope restriction `BOOL_ARITH_REWRITER_REPORT.md` uses for
its own closed-form `bool`/`int` lemmas. Atoms are assigned truth by an
arbitrary, uninterpreted `v : expr -> bool`, standing in for
`Z3AstTheory.fst`'s richer `eval i e rho : value`; every lemma below
is universally quantified over `v`, so nothing depends on a particular
choice of atom valuation.

## Coverage

| Site (ast.cpp / proof_checker.cpp) | Lemma(s) | Status |
|---|---|---|
| `is_complement_core`/`is_complement` (ast.h:2206-2209) | `lemma_is_complement_core_sound`, `lemma_is_complement_sound` | ✅ complementary literals always take opposite truth values |
| `mk_unit_resolution`'s main (`is_or`) loop (ast.cpp:3056-3090); `check1_basic`'s `PR_UNIT_RESOLUTION` multi-premise case (proof_checker.cpp:560-605) | `resolve_residual`, `lemma_resolve_residual_sound` | ✅ if the clause and every resolved-away literal hold, the computed residual clause holds |
| `mk_unit_resolution`'s 2-premise non-`or` shortcut (ast.cpp:3049-3055); `check1_basic`'s 2-premise `is_complement` case (proof_checker.cpp:550-557) | `lemma_unit_resolution_singleton_sound` | ✅ shown as a direct corollary (singleton clause instance) |
| `mk_modus_ponens`, `is_implies(f2)` case (ast.cpp:2756) | `lemma_mp_implies_sound` | ✅ |
| `mk_modus_ponens`, `is_eq(f2)` case | `lemma_mp_eq_sound` | ✅ (treated as iff, matching `is_iff`'s Bool-sort guard) |
| `mk_modus_ponens`, `is_oeq(f2)` case | `lemma_mp_oeq_sound` | ✅ |
| `mk_modus_ponens`'s `is_reflexivity(p2)` short-circuit (ast.cpp:2764) | `lemma_mp_reflexivity_shortcut` | ✅ shown as a direct corollary of `lemma_mp_eq_sound` at `t1 = t2` |
| `check1_basic`'s `PR_AND_ELIM` case (proof_checker.cpp:386-396): membership test on a conjunction's conjuncts | `lemma_and_elim_sound` (via `lemma_band_eval_mem_sound`) | ✅ a true conjunction makes every one of its conjuncts true |
| `check1_basic`'s `PR_NOT_OR_ELIM` case (proof_checker.cpp:397-412): `match_negated` membership test on a negated disjunction's disjuncts | `lemma_not_or_elim_sound` (via `lemma_bclause_eval_false_mem_sound`) | ✅ a false disjunction makes every one of its disjuncts false, hence every disjunct's complement true |


9/9 target properties proved.

## `smt_justification.cpp`/CNF-conversion call-site mapping

| Function | Combinators used | Covered by |
|---|---|---|
| `unit_resolution_justification::mk_proof` | `mk_unit_resolution` over `[pr(clause); pr(lit_0); ...; pr(lit_n)]` | `lemma_resolve_residual_sound` / `lemma_unit_resolution_singleton_sound` |
| `eq_conflict_justification::mk_proof` | `mk_transitivity` (equational, already covered by `Z3ProofTheory.fst`) then `mk_rewrite` + `mk_modus_ponens` to derive `false` from `lhs = rhs` | `lemma_mp_eq_sound` (the `mk_rewrite(eq(lhs,rhs), false)` leaf is a trusted `PR_REWRITE` leaf exactly as in `Z3ProofTheory.fst`; this file covers the `mk_modus_ponens` combination step) |
| `eq_root_propagation_justification::mk_proof` | `mk_rewrite` + `mk_modus_ponens` | `lemma_mp_eq_sound` |
| `mp_iff_justification::mk_proof` | `mk_symmetry`/`mk_congruence` (already covered) composed with `mk_modus_ponens` | `lemma_mp_eq_sound` / `lemma_mp_implies_sound` depending on `l.sign()` |
| `theory_axiom_justification`, `theory_propagation_justification`, `theory_conflict_justification`, `ext_*_justification`, `theory_lemma_justification` | `mk_th_lemma` only | **Not covered** — see below |
| CNF-conversion/clausification sites building `mk_and_elim`/`mk_not_or_elim` (e.g. `nnf.cpp`, `asserted_formulas.cpp`) | `ast_manager::mk_and_elim`, `ast_manager::mk_not_or_elim` | `lemma_and_elim_sound`, `lemma_not_or_elim_sound` |

## Not yet covered (deferred)

- **`PR_TH_LEMMA`** (`mk_th_lemma`, used by every `theory_*_justification`
  class above): this is the proof-term equivalent of
  `rewriter_def.h`'s `PR_REWRITE` leaves — a trusted node whose
  soundness is the responsibility of whichever theory solver produced
  it, not a generic combinator. Notably, `proof_checker.cpp`'s own
  `check1_basic` case for `PR_TH_LEMMA` (proof_checker.cpp:762-770)
  *only* self-checks the `"arith"` family (`check_arith_proof`); for
  every other theory it unconditionally `return true`s after dumping
  the proof for inspection. This file treats `PR_TH_LEMMA` as entirely
  out of scope for the same reason — there is no generic combinator
  here to verify, only theory-specific lemma content (already the
  subject of the `SEQ_EQ_SOLVER_REPORT.md`-style per-theory audits).
- **`PR_HYPER_RESOLVE`**: a strict generalization of `PR_UNIT_RESOLUTION`
  to multiple clause premises simultaneously, used only by the Datalog/
  PDR/Spacer engine (`src/muz/**`) and `ast/proofs/proof_utils.cpp`,
  not `smt_justification.cpp`. Deferred: beyond positional/substitution
  bookkeeping (quantifier instantiation at each premise), even
  `check1_basic`'s own check (proof_checker.cpp:775-830) does not fully
  self-validate it -- it builds an `iff` side condition and defers its
  truth to an external decision procedure rather than checking it
  inline, making a faithful formalization substantially larger in
  scope than the combinators covered here.
- **`PR_QUANT_INST`**, **`PR_SKOLEMIZE`**, **`PR_DEF_AXIOM`**,
  **`PR_NNF_POS`/`PR_NNF_NEG`**: per `check1_basic`
  (proof_checker.cpp:671-680, 719-726, 771-774), these are either
  entirely trusted (`PR_DEF_AXIOM`/`PR_NNF_POS`/`PR_NNF_NEG`/
  `PR_QUANT_INST` all unconditionally `return true` for any well-typed
  fact — explicitly marked `// TBD` in two of these cases in the C++
  source) or only partially checked (`PR_SKOLEMIZE`). None have
  non-trivial semantic content to formalize against today's checker.
- The `ast_mark`-based clause-literal de-duplication in the real
  `mk_unit_resolution` (an allocation optimization with no semantic
  effect, since `bclause_eval`'s `||` is idempotent on repeated
  literals) is not modeled; `resolve_residual` assumes no deduplication
  is needed for soundness (it still holds with duplicates, just
  produces a syntactically longer, not shorter, residual than the
  real code would — purely a conservativeness gap, not a soundness
  gap).
- `is_iff`'s Bool-sort guard on `is_eq` is elided: `is_eq_e`/`blit_eval`
  treat every `=`-application as an iff, which is only correct when
  both arguments are Bool-sorted — true at every call site this file
  analyzes (`eq_conflict_justification`/`eq_root_propagation_
  justification`/`mp_iff_justification` only ever build `mk_modus_ponens`
  calls over Bool-sorted equalities), but not asserted as a general
  invariant here.

## Full-directory status

All 48 `.fst` files in this directory (47 pre-existing + the new
`Z3ProofJustifications.fst`) type-check cleanly with zero
`admit`/`assume`, confirmed via a full clean recompile.
