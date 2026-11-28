import Z3SeqProofs.SmartIntersection

/-
Correctness of the regex rewriter's complement smart constructor,
modeling `seq_rewriter::mk_re_complement` (src/ast/rewriter/seq_rewriter.cpp).

Out of scope for this pass, same rationale as `SmartUnion.lean`: ITE
hoisting, and the `to_re("")` special case (`~(to_re ""))= Σ+`), which
has no analog since `RE` has no string-literal constructor.

Unlike the union/intersection smart constructors, this one is genuinely
*recursive*: the De Morgan cases push the complement inward and feed the
already-proven `smartUnion`/`smartInter`, so its correctness proof is by
structural induction on the regex, using classical excluded-middle
reasoning (via `by_cases` on the undecidable `L _ w` propositions) for
the De Morgan / double-negation steps themselves.
-/
namespace Z3SeqProofs

variable {α σ : Type} [EBA α σ]

/-- Models `mk_re_complement`'s case chain (minus ITE-hoisting and the
`to_re("")` case; see the file docstring). -/
def smartComplement [DecidableEq α] : RE α → RE α
  | .inter e1 e2 => smartUnion (smartComplement e1) (smartComplement e2)
  | .union e1 e2 => smartInter (smartComplement e1) (smartComplement e2)
  | .bot => RE.fullSeq
  | .compl e1 => e1
  | r => if r.isFullSeq then .bot else .compl r

theorem smartComplement_correct [DecidableEq α] (r : RE α) (w : List σ) :
    L (smartComplement r) w ↔ L (.compl r : RE α) w := by
  induction r with
  | eps =>
      have h : ¬ (RE.eps : RE α).isFullSeq = true := by simp [RE.isFullSeq]
      simp [smartComplement, h]
  | bot =>
      simp only [smartComplement, L]
      exact ⟨fun _ => id, fun _ => L_fullSeq w⟩
  | pred p =>
      have h : ¬ (RE.pred p : RE α).isFullSeq = true := by simp [RE.isFullSeq]
      simp [smartComplement, h]
  | union e1 e2 ih1 ih2 =>
      show L (smartInter (smartComplement e1) (smartComplement e2)) w ↔
        L (.compl (RE.union e1 e2) : RE α) w
      rw [smartInter_correct]
      simp only [L, ih1, ih2]
      by_cases h1 : L e1 w <;> by_cases h2 : L e2 w <;> simp_all
  | inter e1 e2 ih1 ih2 =>
      show L (smartUnion (smartComplement e1) (smartComplement e2)) w ↔
        L (.compl (RE.inter e1 e2) : RE α) w
      rw [smartUnion_correct]
      simp only [L, ih1, ih2]
      by_cases h1 : L e1 w <;> by_cases h2 : L e2 w <;> simp_all
  | concat e1 e2 _ _ =>
      have h : ¬ (RE.concat e1 e2 : RE α).isFullSeq = true := by simp [RE.isFullSeq]
      simp [smartComplement, h]
  | star e1 _ =>
      by_cases h : (RE.star e1 : RE α).isFullSeq = true
      · have hLtrue : L (RE.star e1 : RE α) w := by
          rw [RE.isFullSeq_true_iff.mp h]; exact L_fullSeq w
        simp only [smartComplement, h, ite_true, L]
        exact ⟨fun hf => absurd hf (by simp), fun hc => absurd hLtrue hc⟩
      · simp [smartComplement, h]
  | compl e1 _ =>
      simp only [smartComplement, L]
      by_cases h : L e1 w <;> simp_all

end Z3SeqProofs
