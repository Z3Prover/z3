import Z3SeqProofs.SmartComplement

/-
Correctness of the regex rewriter's xor smart constructors, modeling
`seq_rewriter::mk_re_xor`/`mk_re_xor0` (src/ast/rewriter/seq_rewriter.cpp).

Unlike union/intersection/complement, `RE` has no `xor` constructor at
all (it deliberately matches only Z3's core `OP_RE_*` set; see the
docstring on `Regex.lean`). Xor is therefore modeled here as a genuinely
*derived* notion throughout: `LXor a b w` is the reference semantics
(symmetric difference, matching how the Mathlib-based `Ere.xor` is
specified: `xs ⊫ xor l r ↔ ((xs ⊫ l) ↔ ¬(xs ⊫ r))`), and `smartXor`
produces an ordinary `RE` term — its "raw" fallback case constructs
`(a ∩ ~b) ∪ (~a ∩ b)` directly, since there is no primitive xor node to
fall back to.

Out of scope, same rationale as the other files: ITE-hoisting and the
AC (expression-ID) canonicalization step (not semantically meaningful —
a presentation/dedup concern, not a correctness one).
-/
namespace Z3SeqProofs

variable {α σ : Type} [EBA α σ]

/-- A coarse structural size, used only as a termination measure for
`smartXor`'s complement-pushing recursion. -/
def RE.size : RE α → Nat
  | .eps => 1
  | .bot => 1
  | .pred _ => 1
  | .union r s => r.size + s.size + 1
  | .inter r s => r.size + s.size + 1
  | .concat r s => r.size + s.size + 1
  | .star r => r.size + 1
  | .compl r => r.size + 1

/-- Reference semantics for xor: symmetric difference, matching the
Mathlib-based `Ere.xor`'s specification. -/
def LXor (a b : RE α) (w : List σ) : Prop := L a w ↔ ¬ L b w

/-- Returns the inner regex if `r` is syntactically a complement,
mirroring `seq_rewriter::is_complement`. `smartXor` matches on this
(rather than on `a`/`b` directly), so that the hypotheses produced by
destructuring `a.asCompl`/`b.asCompl` in the correctness proof can drive
the *same* reduction via `simp`, without ever needing to destructure
`a`/`b` themselves (which would eliminate them from the context in the
non-complement branches). -/
def RE.asCompl : RE α → Option (RE α)
  | .compl r => some r
  | _ => none

theorem RE.asCompl_eq_some_iff {r r' : RE α} : r.asCompl = some r' ↔ r = .compl r' := by
  cases r <;> simp [RE.asCompl]

theorem RE.size_asCompl_some {r r' : RE α} (h : r.asCompl = some r') : r'.size < r.size := by
  rw [RE.asCompl_eq_some_iff] at h; subst h; simp [RE.size]

/-- Models `mk_re_xor`'s case chain (minus ITE-hoisting and AC
canonicalization; see the file docstring). The two `is_complement`
cases recurse; the final fallback constructs the derived form directly,
since `RE` has no xor node. -/
def smartXor [DecidableEq α] : RE α → RE α → RE α
  | a, b =>
    if a = b then .bot
    else if a.isEmpty then b
    else if b.isEmpty then a
    else if a.isFullSeq then smartComplement b
    else if b.isFullSeq then smartComplement a
    else match _h1 : a.asCompl with
      | some ra =>
          match _h2 : b.asCompl with
          | some rb => smartXor ra rb
          | none => smartComplement (smartXor ra b)
      | none =>
          match _h2 : b.asCompl with
          | some rb => smartComplement (smartXor a rb)
          | none => .union (.inter a (.compl b)) (.inter (.compl a) b)
termination_by a b => a.size + b.size
decreasing_by
  all_goals first
    | (have := RE.size_asCompl_some _h1; have := RE.size_asCompl_some _h2; omega)
    | (have := RE.size_asCompl_some _h1; omega)
    | (have := RE.size_asCompl_some _h2; omega)

theorem RE.size_pos (r : RE α) : 1 ≤ r.size := by cases r <;> simp only [RE.size] <;> omega

set_option linter.unusedSimpArgs false in
theorem smartXor_correct_aux [DecidableEq α] :
    ∀ (n : Nat) (a b : RE α), a.size + b.size ≤ n → ∀ (w : List σ), L (smartXor a b) w ↔ LXor a b w := by
  intro n
  induction n with
  | zero =>
      intro a b hn w
      exfalso
      have := RE.size_pos a
      have := RE.size_pos b
      omega
  | succ n ih =>
      intro a b hn w
      unfold smartXor
      split
      next _h1 =>
        subst _h1
        simp only [LXor, L]
        by_cases h : L a w <;> simp_all
      split
      next _h2 =>
        rw [RE.isEmpty_true_iff] at _h2; subst _h2
        simp only [LXor, L]
        by_cases h : L b w <;> simp_all
      split
      next _h3 =>
        rw [RE.isEmpty_true_iff] at _h3; subst _h3
        simp only [LXor, L]
        by_cases h : L a w <;> simp_all
      split
      next h4 =>
        rw [RE.isFullSeq_true_iff] at h4; subst h4
        rw [smartComplement_correct]
        have hfs := L_fullSeq (α := α) w
        simp only [LXor, L] at *
        by_cases hb : L b w <;> simp_all
      split
      next h5 =>
        rw [RE.isFullSeq_true_iff] at h5; subst h5
        rw [smartComplement_correct]
        have hfs := L_fullSeq (α := α) w
        simp only [LXor, L] at *
        by_cases ha : L a w <;> simp_all
      · rcases hca : a.asCompl with _ | ra
        · rcases hcb : b.asCompl with _ | rb
          · simp only [hca, hcb, LXor, L]
            by_cases ha : L a w <;> by_cases hb : L b w <;> simp_all
          · have hsize := RE.size_asCompl_some hcb
            have hb' := RE.asCompl_eq_some_iff.mp hcb
            subst hb'
            simp only [hca, hcb]
            rw [smartComplement_correct]
            simp only [L]
            rw [ih a rb (by omega) w]
            simp only [LXor, L]
            by_cases ha : L a w <;> by_cases hb : L rb w <;> simp_all
        · have hsize := RE.size_asCompl_some hca
          have ha' := RE.asCompl_eq_some_iff.mp hca
          subst ha'
          rcases hcb : b.asCompl with _ | rb
          · simp only [hca, hcb]
            rw [smartComplement_correct]
            simp only [L]
            rw [ih ra b (by omega) w]
            simp only [LXor, L]
            by_cases ha : L ra w <;> by_cases hb : L b w <;> simp_all
          · have hsize2 := RE.size_asCompl_some hcb
            have hb' := RE.asCompl_eq_some_iff.mp hcb
            subst hb'
            simp only [hca, hcb]
            rw [ih ra rb (by omega) w]
            simp only [LXor, L]
            by_cases ha : L ra w <;> by_cases hb : L rb w <;> simp_all

theorem smartXor_correct [DecidableEq α] (a b : RE α) (w : List σ) :
    L (smartXor a b) w ↔ LXor a b w :=
  smartXor_correct_aux (a.size + b.size) a b (by omega) w

end Z3SeqProofs
