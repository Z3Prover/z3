import Z3SeqProofs.SmartStar

/-
Correctness of the regex rewriter's *derived* smart constructors:
`seq_rewriter::mk_re_opt`, `mk_re_diff`, and `mk_re_plus`
(src/ast/rewriter/seq_rewriter.cpp). Unlike every Tier 1/Tier 2
constructor so far, none of `opt`/`diff`/`plus` has its own `RE`
constructor at all — Z3's AST has dedicated `OP_RE_OPTION`/`OP_RE_DIFF`/
`OP_RE_PLUS` nodes, but `RE` deliberately only models the core primitive
set (see `Regex.lean`'s docstring), so each of these is modeled the same
way `SmartXor.lean` modeled xor: as a *reference* notion defined directly
in terms of the general constructors (`Lopt`/`Ldiff`/`Lplus`), together
with a smart constructor that is correct against that reference.

`mk_re_power` is out of scope: it is a one-line delegate to `mk_loop`
(bounded repetition `r^k`), which has no `RE` analog (see
`SmartConcat.lean`'s docstring for why bounded loops are out of scope
throughout this development) and has no rewriting logic of its own to
model.

Each of `smartOpt`/`smartDiff` is essentially free, reusing a Tier 1
correctness theorem directly: `mk_re_opt` always rewrites to
`ε ∪ a`, i.e. `smartUnion`; `mk_re_diff`'s only `RE`-expressible case
(the `range_predicate` fast path operates on a different, not-modeled
representation) always rewrites to `a ∩ ~b`, i.e. `smartInter` composed
with `smartComplement`. `smartPlus` needs its own small case analysis,
mirroring `mk_re_plus`'s chain, plus one new general `starL` fact
(`starL_self_concat`) for the "already a star" case.
-/
namespace Z3SeqProofs

variable {α σ : Type} [EBA α σ]

/-- Reference semantics for `opt`: "zero or one `r`", matching
`mk_re_opt`'s literal construction `mk_union(mk_to_re(empty), a)`. -/
def Lopt (r : RE α) (w : List σ) : Prop := L (.union .eps r : RE α) w

/-- `r?`, modeled as `smartUnion ε r` — exactly what `mk_re_opt` always
produces. -/
def smartOpt [DecidableEq α] (r : RE α) : RE α := smartUnion .eps r

theorem smartOpt_correct [DecidableEq α] (r : RE α) (w : List σ) :
    L (smartOpt r) w ↔ Lopt r w :=
  smartUnion_correct .eps r w

/-- Reference semantics for `diff`: `a` but not `b`, matching
`mk_re_diff`'s general-case construction `mk_inter(a, mk_complement(b))`
(its `range_predicate` fast path operates on a separate representation,
not modeled by `RE`; see the file docstring). -/
def Ldiff (a b : RE α) (w : List σ) : Prop := L (.inter a (.compl b) : RE α) w

/-- `a \ b`, modeled as `smartInter a (smartComplement b)` — exactly
`mk_re_diff`'s general-case fallback. -/
def smartDiff [DecidableEq α] (a b : RE α) : RE α := smartInter a (smartComplement b)

theorem smartDiff_correct [DecidableEq α] (a b : RE α) (w : List σ) :
    L (smartDiff a b) w ↔ Ldiff a b w := by
  unfold smartDiff Ldiff
  rw [smartInter_correct]
  simp only [L, smartComplement_correct]

/-- A word accepted by `starL P` splits (trivially) into two `starL P`
pieces, and conversely two spliced `starL P` pieces are themselves a
`starL P` match. The key fact behind `(r*)+ = r*`. -/
theorem starL_self_concat {P : List σ → Prop} {w : List σ} :
    (∃ w1 w2, w = w1 ++ w2 ∧ starL P w1 ∧ starL P w2) ↔ starL P w := by
  constructor
  · rintro ⟨w1, w2, heq, h1, h2⟩
    subst heq
    exact starL_append h1 h2
  · intro h
    exact ⟨w, [], (List.append_nil w).symm, h, .nil⟩

/-- Reference semantics for `plus`: "one or more `r`", matching
`mk_re_plus`'s fallback construction `mk_re_append(a, mk_star(a))`. -/
def Lplus (r : RE α) (w : List σ) : Prop := L (.concat r (.star r) : RE α) w

/-- Models `mk_re_plus`'s case chain. `is_full_char` is not modeled
separately: in the real rewriter it deliberately declines to simplify
`Σ+` (there is no primitive `plus` node in `RE` to preserve as a
canonical form, so this check has no analog — see the file docstring),
and `is_plus` never applies since no `RE` value is ever literally a
`plus` node. -/
def smartPlus [DecidableEq α] (a : RE α) : RE α :=
  if a.isEmpty then a
  else if a.isEpsilon then a
  else if a.isStar then a
  else .concat a (.star a)

theorem smartPlus_correct [DecidableEq α] (r : RE α) (w : List σ) :
    L (smartPlus r) w ↔ Lplus r w := by
  unfold smartPlus Lplus
  split
  · rename_i h1
    rw [RE.isEmpty_true_iff] at h1
    subst h1
    simp only [L]
    constructor
    · exact False.elim
    · rintro ⟨w1, w2, heq, h, _⟩; exact h.elim
  split
  · rename_i h2
    rw [RE.isEpsilon_true_iff] at h2
    subst h2
    simp only [L]
    constructor
    · rintro rfl; exact ⟨[], [], rfl, rfl, starL.nil⟩
    · rintro ⟨w1, w2, heq, h1', h2'⟩
      have hw1 : w1 = [] := h1'
      subst hw1
      simp only [List.nil_append] at heq
      subst heq
      cases h2' with
      | nil => rfl
      | step hw hp _ => exact absurd hp hw
  split
  · rename_i h3
    obtain ⟨r1, hr⟩ := RE.isStar_true_iff.mp h3
    subst hr
    simp only [L, starL_idem]
    exact starL_self_concat.symm
  rfl

end Z3SeqProofs
