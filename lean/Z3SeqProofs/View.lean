import Z3SeqProofs.Derivatives

/-
Views: mirrors the resplit paper's Sec. "View Based Splits" (`View{r}{s}`,
Theorem [View]). This is the formal basis for c3mv's
`seq_view_witness.cpp`/`mem_monadic_split`: splitting `x·u ⊨ r` into "`u`
drives `r` to some reachable state `s`" plus "the rest matches from `s`
onward".

Modeled semantically (via iterated derivative) rather than as a further
syntactic t-term layer, since the certification use case only needs the
soundness content, not a re-derivation of `ders{r}`'s finiteness (that is
exactly EREQ's `Finiteness/*.lean`, not re-proved here).
-/
namespace Z3SeqProofs

variable {α σ : Type} [EBA α σ]

def iterDerivative : List σ → RE α → RE α
  | [],     r => r
  | a :: w, r => iterDerivative w (derivative a r)

theorem iterDerivative_correct (r : RE α) (w v : List σ) :
    L (iterDerivative w r) v ↔ L r (w ++ v) := by
  induction w generalizing r with
  | nil => rfl
  | cons a w ih =>
      simp only [iterDerivative, List.cons_append]
      rw [ih, derivative_correct]

-- `u ⊨ View{r}{s}  :=  der[u](r) = s  ∧  s ≢ ∅`  (paper's `Lang(View r s)`).
def ViewPred (r s : RE α) (u : List σ) : Prop := iterDerivative u r = s ∧ s ≠ RE.bot

-- Theorem [View]: `uv ⊨ r  ⟺  ∃ s, u ⊨ View{r}{s} ∧ v ⊨ s`.
theorem view_theorem (r : RE α) (u v : List σ) :
    L r (u ++ v) ↔ ∃ s : RE α, ViewPred r s u ∧ L s v := by
  constructor
  · intro h
    rw [← iterDerivative_correct] at h
    refine ⟨iterDerivative u r, ⟨rfl, ?_⟩, h⟩
    intro hbot
    rw [hbot] at h
    exact h
  · rintro ⟨s, ⟨heq, _⟩, hLs⟩
    subst heq
    rwa [iterDerivative_correct] at hLs

end Z3SeqProofs
