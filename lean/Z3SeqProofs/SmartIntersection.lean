import Z3SeqProofs.SmartUnion

/-
Correctness of the regex rewriter's intersection smart constructors,
modeling `seq_rewriter::mk_re_inter0` (src/ast/rewriter/seq_rewriter.cpp).
Same structure and scope restrictions as `SmartUnion.lean`: ITE-hoisting
and `mk_regex_inter_normalize`'s n-ary normalization are out of scope for
this pass.
-/
namespace Z3SeqProofs

variable {α σ : Type} [EBA α σ]

/-- Mirrors `seq_rewriter::try_collapse_re_inter`, specialized (as for
union) to the case both operands are bare predicate atoms. -/
def RE.tryCollapseInter : RE α → RE α → Option (RE α)
  | .pred p, .pred q => some (.pred (EBA.inf p q))
  | _, _ => none

theorem RE.tryCollapseInter_eq_some_iff {a b : RE α} {r : RE α} :
    RE.tryCollapseInter a b = some r ↔ ∃ p q, a = .pred p ∧ b = .pred q ∧ r = .pred (EBA.inf p q) := by
  constructor
  · intro h
    cases a with
    | pred p =>
        cases b with
        | pred q =>
            simp only [RE.tryCollapseInter] at h
            injection h with h'
            exact ⟨p, q, rfl, rfl, h'.symm⟩
        | eps => simp [RE.tryCollapseInter] at h
        | bot => simp [RE.tryCollapseInter] at h
        | union _ _ => simp [RE.tryCollapseInter] at h
        | inter _ _ => simp [RE.tryCollapseInter] at h
        | concat _ _ => simp [RE.tryCollapseInter] at h
        | star _ => simp [RE.tryCollapseInter] at h
        | compl _ => simp [RE.tryCollapseInter] at h
    | eps => cases b <;> simp [RE.tryCollapseInter] at h
    | bot => cases b <;> simp [RE.tryCollapseInter] at h
    | union _ _ => cases b <;> simp [RE.tryCollapseInter] at h
    | inter _ _ => cases b <;> simp [RE.tryCollapseInter] at h
    | concat _ _ => cases b <;> simp [RE.tryCollapseInter] at h
    | star _ => cases b <;> simp [RE.tryCollapseInter] at h
    | compl _ => cases b <;> simp [RE.tryCollapseInter] at h
  · rintro ⟨p, q, ha, hb, hr⟩
    subst ha; subst hb; subst hr
    rfl

/-- Models `mk_re_inter0`'s case chain (minus ITE-hoisting; see the file
docstring). -/
def smartInter [DecidableEq α] (a b : RE α) : RE α :=
  if a = b then a
  else if a.isEmpty then a
  else if b.isEmpty then b
  else if a.isFullSeq then b
  else if b.isFullSeq then a
  else if RE.areComplements a b then .bot
  else match RE.tryCollapseInter a b with
    | some r => r
    | none => .inter a b

theorem smartInter_correct [DecidableEq α] (a b : RE α) (w : List σ) :
    L (smartInter a b) w ↔ L (.inter a b : RE α) w := by
  unfold smartInter
  split
  · rename_i h1
    subst h1
    simp only [L]
    exact ⟨fun h => ⟨h, h⟩, fun h => h.1⟩
  split
  · rename_i h2
    rw [RE.isEmpty_true_iff] at h2
    subst h2
    simp [L]
  split
  · rename_i h3
    rw [RE.isEmpty_true_iff] at h3
    subst h3
    simp [L]
  split
  · rename_i h4
    rw [RE.isFullSeq_true_iff] at h4
    subst h4
    simp only [L]
    exact ⟨fun h => ⟨L_fullSeq w, h⟩, fun h => h.2⟩
  split
  · rename_i h5
    rw [RE.isFullSeq_true_iff] at h5
    subst h5
    simp only [L]
    exact ⟨fun h => ⟨h, L_fullSeq w⟩, fun h => h.1⟩
  split
  · rename_i h6
    rcases RE.areComplements_true_iff.mp h6 with h6 | h6
    · subst h6
      simp only [L]
      exact ⟨fun h => h.elim, fun ⟨h1, h2⟩ => absurd h2 h1⟩
    · subst h6
      simp only [L]
      exact ⟨fun h => h.elim, fun ⟨h1, h2⟩ => absurd h1 h2⟩
  · rcases hcol : RE.tryCollapseInter a b with _ | r
    · rfl
    · obtain ⟨p, q, ha, hb, hr⟩ := RE.tryCollapseInter_eq_some_iff.mp hcol
      subst ha; subst hb; subst hr
      simp only [L]
      constructor
      · rintro ⟨c, hc, hm⟩
        rw [EBA.models_inf, Bool.and_eq_true] at hm
        exact ⟨⟨c, hc, hm.1⟩, ⟨c, hc, hm.2⟩⟩
      · rintro ⟨⟨c, hc, hm1⟩, ⟨c', hc', hm2⟩⟩
        rw [hc] at hc'
        injection hc' with hcc' _
        subst hcc'
        exact ⟨c, hc, by rw [EBA.models_inf, hm1, hm2]; rfl⟩

end Z3SeqProofs
