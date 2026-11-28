import Z3SeqProofs.Derivatives

/-
Correctness of the regex rewriter's union smart constructors, modeling
`seq_rewriter::mk_re_union0` (src/ast/rewriter/seq_rewriter.cpp). Each
syntactic special case there is reproduced here as a branch of
`smartUnion`, in the same checking order, with a single theorem
(`smartUnion_correct`) proving the simplified construction denotes the
same language as the raw `RE.union` constructor for every branch.

Two things are intentionally out of scope for this first pass, matching
the plan: ITE-hoisting (there is no `ite` node in `RE`'s syntax — the
real rewriter's ITE cases only fire when a regex argument is itself a
Boolean-ite term, which does not arise from this closed regex syntax),
and `mk_regex_union_normalize`'s n-ary ACI/dedup normalization (a
separate, list-processing concern, structurally more like the
`range_predicate` union/intersection work than a case analysis).
-/
namespace Z3SeqProofs

variable {α σ : Type} [EBA α σ]

/-- `Σ*`, the regex matching every word. -/
def RE.fullSeq : RE α := .star (.pred EBA.top)

/-- Mirrors `seq_rewriter::is_empty`. -/
def RE.isEmpty : RE α → Bool
  | .bot => true
  | _ => false

theorem RE.isEmpty_true_iff {r : RE α} : r.isEmpty = true ↔ r = .bot := by
  cases r <;> simp [RE.isEmpty]

/-- Mirrors `seq_rewriter::is_epsilon`. -/
def RE.isEpsilon : RE α → Bool
  | .eps => true
  | _ => false

theorem RE.isEpsilon_true_iff {r : RE α} : r.isEpsilon = true ↔ r = .eps := by
  cases r <;> simp [RE.isEpsilon]

/-- Mirrors `seq_rewriter::is_star`. -/
def RE.isStar : RE α → Bool
  | .star _ => true
  | _ => false

theorem RE.isStar_true_iff {r : RE α} : r.isStar = true ↔ ∃ s, r = .star s := by
  cases r <;> simp [RE.isStar]

/-- Mirrors `seq_rewriter::is_full_seq`: syntactically `(pred top)*`. -/
def RE.isFullSeq [DecidableEq α] : RE α → Bool
  | .star (.pred p) => p == EBA.top
  | _ => false

theorem RE.isFullSeq_true_iff [DecidableEq α] {r : RE α} :
    r.isFullSeq = true ↔ r = RE.fullSeq := by
  unfold RE.fullSeq
  cases r with
  | star r' =>
      cases r' with
      | pred p => simp [RE.isFullSeq]
      | eps => simp [RE.isFullSeq]
      | bot => simp [RE.isFullSeq]
      | union _ _ => simp [RE.isFullSeq]
      | inter _ _ => simp [RE.isFullSeq]
      | concat _ _ => simp [RE.isFullSeq]
      | star _ => simp [RE.isFullSeq]
      | compl _ => simp [RE.isFullSeq]
  | eps => simp [RE.isFullSeq]
  | bot => simp [RE.isFullSeq]
  | pred _ => simp [RE.isFullSeq]
  | union _ _ => simp [RE.isFullSeq]
  | inter _ _ => simp [RE.isFullSeq]
  | concat _ _ => simp [RE.isFullSeq]
  | compl _ => simp [RE.isFullSeq]

/-- Mirrors `seq_rewriter::are_complements`: one operand is syntactically
the complement of the other. -/
def RE.areComplements [DecidableEq α] (a b : RE α) : Bool :=
  a == RE.compl b || b == RE.compl a

theorem RE.areComplements_true_iff [DecidableEq α] {a b : RE α} :
    RE.areComplements a b = true ↔ a = RE.compl b ∨ b = RE.compl a := by
  simp [RE.areComplements]

/-- Mirrors `seq_rewriter::try_collapse_re_union`, specialized to the
case both operands are already bare predicate atoms (the only shape `RE`
has for a single-character class — no separate string/range/to_re forms
to normalize first, unlike the real AST). -/
def RE.tryCollapseUnion : RE α → RE α → Option (RE α)
  | .pred p, .pred q => some (.pred (EBA.sup p q))
  | _, _ => none

theorem RE.tryCollapseUnion_eq_none_iff {a b : RE α} :
    RE.tryCollapseUnion a b = none ↔ (∀ p, a ≠ .pred p) ∨ (∀ q, b ≠ .pred q) := by
  cases a <;> cases b <;> simp [RE.tryCollapseUnion]

theorem RE.tryCollapseUnion_eq_some_iff {a b : RE α} {r : RE α} :
    RE.tryCollapseUnion a b = some r ↔ ∃ p q, a = .pred p ∧ b = .pred q ∧ r = .pred (EBA.sup p q) := by
  constructor
  · intro h
    cases a with
    | pred p =>
        cases b with
        | pred q =>
            simp only [RE.tryCollapseUnion] at h
            injection h with h'
            exact ⟨p, q, rfl, rfl, h'.symm⟩
        | eps => simp [RE.tryCollapseUnion] at h
        | bot => simp [RE.tryCollapseUnion] at h
        | union _ _ => simp [RE.tryCollapseUnion] at h
        | inter _ _ => simp [RE.tryCollapseUnion] at h
        | concat _ _ => simp [RE.tryCollapseUnion] at h
        | star _ => simp [RE.tryCollapseUnion] at h
        | compl _ => simp [RE.tryCollapseUnion] at h
    | eps => cases b <;> simp [RE.tryCollapseUnion] at h
    | bot => cases b <;> simp [RE.tryCollapseUnion] at h
    | union _ _ => cases b <;> simp [RE.tryCollapseUnion] at h
    | inter _ _ => cases b <;> simp [RE.tryCollapseUnion] at h
    | concat _ _ => cases b <;> simp [RE.tryCollapseUnion] at h
    | star _ => cases b <;> simp [RE.tryCollapseUnion] at h
    | compl _ => cases b <;> simp [RE.tryCollapseUnion] at h
  · rintro ⟨p, q, ha, hb, hr⟩
    subst ha; subst hb; subst hr
    rfl

/-- Models `mk_re_union0`'s case chain (minus ITE-hoisting; see the file
docstring). -/
def smartUnion [DecidableEq α] (a b : RE α) : RE α :=
  if a = b then a
  else if a.isEmpty then b
  else if b.isEmpty then a
  else if a.isFullSeq then a
  else if b.isFullSeq then b
  else if a.isStar && b.isEpsilon then a
  else if b.isStar && a.isEpsilon then b
  else if RE.areComplements a b then RE.fullSeq
  else match RE.tryCollapseUnion a b with
    | some r => r
    | none => .union a b

/-! ## Supporting facts -/

/-- `Σ*` matches every word: the predicate `top` always holds, so every
single character is consumed by `.pred top`, and `starL` accepts any
concatenation of such singletons. -/
theorem L_fullSeq (w : List σ) : L (RE.fullSeq : RE α) w := by
  show starL (L (RE.pred EBA.top)) w
  induction w with
  | nil => exact starL.nil
  | cons a w ih =>
      have hL1 : L (RE.pred EBA.top : RE α) [a] := ⟨a, rfl, EBA.models_top a⟩
      have hstep := starL.step (P := L (RE.pred EBA.top : RE α)) (w1 := [a]) (w2 := w)
        (by simp) hL1 ih
      simpa using hstep

/-- `r★` always matches the empty word, regardless of `r`. -/
theorem L_star_nil (r : RE α) : L (RE.star r) ([] : List σ) := starL.nil

theorem smartUnion_correct [DecidableEq α] (a b : RE α) (w : List σ) :
    L (smartUnion a b) w ↔ L (.union a b : RE α) w := by
  unfold smartUnion
  split
  · rename_i h1
    subst h1
    simp only [L]
    exact ⟨Or.inl, fun h => h.elim id id⟩
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
    exact ⟨Or.inl, fun _ => L_fullSeq w⟩
  split
  · rename_i h5
    rw [RE.isFullSeq_true_iff] at h5
    subst h5
    simp only [L]
    exact ⟨Or.inr, fun _ => L_fullSeq w⟩
  split
  · rename_i h6
    obtain ⟨ha, hb⟩ := Bool.and_eq_true .. |>.mp h6
    obtain ⟨r, ha⟩ := RE.isStar_true_iff.mp ha
    have hb' := RE.isEpsilon_true_iff.mp hb
    subst ha; subst hb'
    by_cases hw : w = []
    · subst hw; exact ⟨Or.inl, fun _ => starL.nil⟩
    · simp only [L, hw, or_false]
  split
  · rename_i h7
    obtain ⟨hb, ha⟩ := Bool.and_eq_true .. |>.mp h7
    obtain ⟨r, hb⟩ := RE.isStar_true_iff.mp hb
    have ha' := RE.isEpsilon_true_iff.mp ha
    subst ha'; subst hb
    by_cases hw : w = []
    · subst hw; exact ⟨Or.inr, fun _ => starL.nil⟩
    · simp only [L, hw, false_or]
  split
  · rename_i h8
    rcases RE.areComplements_true_iff.mp h8 with h8 | h8
    · subst h8
      simp only [L]
      by_cases hb : L b w
      · exact ⟨fun _ => Or.inr hb, fun _ => L_fullSeq w⟩
      · exact ⟨fun _ => Or.inl hb, fun _ => L_fullSeq w⟩
    · subst h8
      simp only [L]
      by_cases ha : L a w
      · exact ⟨fun _ => Or.inl ha, fun _ => L_fullSeq w⟩
      · exact ⟨fun _ => Or.inr ha, fun _ => L_fullSeq w⟩
  · rcases hcol : RE.tryCollapseUnion a b with _ | r
    · rfl
    · obtain ⟨p, q, ha, hb, hr⟩ := RE.tryCollapseUnion_eq_some_iff.mp hcol
      subst ha; subst hb; subst hr
      simp only [L]
      constructor
      · rintro ⟨c, hc, hm⟩
        rw [EBA.models_sup, Bool.or_eq_true] at hm
        rcases hm with hm | hm
        · exact .inl ⟨c, hc, hm⟩
        · exact .inr ⟨c, hc, hm⟩
      · rintro (⟨c, hc, hm⟩ | ⟨c, hc, hm⟩)
        · exact ⟨c, hc, by rw [EBA.models_sup, hm, Bool.true_or]⟩
        · exact ⟨c, hc, by rw [EBA.models_sup, hm, Bool.or_true]⟩

end Z3SeqProofs
