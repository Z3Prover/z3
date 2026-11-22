import Z3SeqProofs.Regex

/-
Brzozowski derivatives: `null`/`derivative` over the closed regex type `RE`,
with full correctness (`derivative_correct`, `null_correct`) against the
reference semantics `L`, and a reusable verified decision procedure
(`acceptsBy`/`acceptsBy_correct`).

Matches c3mv's `seq_derive.cpp` concrete (`derivative_kind::brzozowski_t`)
rules — specifically the shape used by `seq_mem_facet.cpp`'s ground-witness
derivative loop, now exposed as named `OP_SEQ_PROOF` rules
`"seq-mem-derivative"` and `"seq-mem-nullable"` in
`src/ast/seq/seq_mem_facet.cpp` (landed in #11816).
-/
namespace Z3SeqProofs

variable {α σ : Type} [EBA α σ]

def null : RE α → Bool
  | .eps        => true
  | .bot        => false
  | .pred _     => false
  | .union r s  => null r || null s
  | .inter r s  => null r && null s
  | .concat r s => null r && null s
  | .star _     => true
  | .compl r    => !(null r)

def derivative (a : σ) : RE α → RE α
  | .eps        => .bot
  | .bot        => .bot
  | .pred p     => if EBA.models p a then .eps else .bot
  | .union r s  => .union (derivative a r) (derivative a s)
  | .inter r s  => .inter (derivative a r) (derivative a s)
  | .concat r s =>
      if null r then .union (.concat (derivative a r) s) (derivative a s)
      else .concat (derivative a r) s
  | .star r     => .concat (derivative a r) (.star r)
  | .compl r    => .compl (derivative a r)

theorem null_correct (r : RE α) : null r = true ↔ L r [] := by
  induction r with
  | eps => simp [null, L]
  | bot => simp [null, L]
  | pred p => simp [null, L]
  | union r s ihr ihs => simp [null, L, ihr, ihs]
  | inter r s ihr ihs => simp [null, L, ihr, ihs]
  | concat r s ihr ihs =>
      simp only [null, Bool.and_eq_true, L, ihr, ihs]
      constructor
      · intro ⟨hr, hs⟩; exact ⟨[], [], rfl, hr, hs⟩
      · rintro ⟨w1, w2, heq, hr, hs⟩
        have h12 : w1 = [] ∧ w2 = [] := by
          rcases w1 with _ | ⟨a, w1⟩
          · simp at heq; exact ⟨rfl, heq⟩
          · simp at heq
        exact ⟨h12.1 ▸ hr, h12.2 ▸ hs⟩
  | star r ih => simp [null, L]; exact starL.nil
  | compl r ih =>
      simp only [null, L]
      cases hnr : null r <;> simp_all

-- Head-decomposition lemma for `starL`, needed to invert `L (star r) (a :: w)`.
theorem starL_cons (P : List σ → Prop) (a : σ) (w : List σ) :
    starL P (a :: w) ↔ ∃ w1 w2, w = w1 ++ w2 ∧ P (a :: w1) ∧ starL P w2 := by
  constructor
  · intro h
    generalize hw' : a :: w = w' at h
    cases h with
    | nil => simp at hw'
    | step hne hp hrest =>
        rename_i w1' w2'
        rcases w1' with _ | ⟨b, w1''⟩
        · exact absurd rfl hne
        · simp only [List.cons_append, List.cons.injEq] at hw'
          obtain ⟨hab, hweq⟩ := hw'
          subst hab
          exact ⟨w1'', w2', hweq, hp, hrest⟩
  · rintro ⟨w1, w2, heq, hp, hrest⟩
    subst heq
    have heq2 : a :: (w1 ++ w2) = (a :: w1) ++ w2 := by rw [List.cons_append]
    rw [heq2]
    exact starL.step (by simp) hp hrest

theorem derivative_correct (r : RE α) (a : σ) (w : List σ) :
    L (derivative a r) w ↔ L r (a :: w) := by
  induction r generalizing w with
  | eps => simp [derivative, L]
  | bot => simp [derivative, L]
  | pred p =>
      simp only [derivative, L]
      by_cases hp : EBA.models p a
      · simp only [hp, ite_true]
        simp only [L]
        constructor
        · intro h; exact ⟨a, by rw [h], hp⟩
        · rintro ⟨c, hc, _⟩
          exact (List.cons.injEq .. |>.mp hc).2
      · simp only [hp, ite_false, Bool.false_eq_true]
        simp only [L]
        constructor
        · exact False.elim
        · rintro ⟨c, hc, hmc⟩
          have h2 := List.cons.injEq .. |>.mp hc
          rw [←h2.1] at hmc
          exact hp hmc
  | union r s ihr ihs => simp only [derivative, L, ihr, ihs]
  | inter r s ihr ihs => simp only [derivative, L, ihr, ihs]
  | concat r s ihr ihs =>
      simp only [derivative]
      by_cases hr : null r = true
      · simp only [hr, ite_true]
        simp only [L]
        constructor
        · rintro (⟨w1, w2, heq, hdr, hsw2⟩ | hds)
          · exact ⟨a :: w1, w2, by rw [heq, List.cons_append], (ihr w1).mp hdr, hsw2⟩
          · exact ⟨[], a :: w, rfl, (null_correct r).mp hr, (ihs w).mp hds⟩
        · rintro ⟨w1, w2, heq, hrw1, hsw2⟩
          rcases w1 with _ | ⟨b, w1'⟩
          · right
            simp only [List.nil_append] at heq
            subst heq
            exact (ihs w).mpr hsw2
          · left
            simp only [List.cons_append, List.cons.injEq] at heq
            obtain ⟨hab, hweq⟩ := heq
            subst hab
            exact ⟨w1', w2, hweq, (ihr w1').mpr hrw1, hsw2⟩
      · simp only [hr, ite_false, Bool.false_eq_true]
        simp only [L]
        constructor
        · rintro ⟨w1, w2, heq, hdr, hsw2⟩
          exact ⟨a :: w1, w2, by rw [heq, List.cons_append], (ihr w1).mp hdr, hsw2⟩
        · rintro ⟨w1, w2, heq, hrw1, hsw2⟩
          rcases w1 with _ | ⟨b, w1'⟩
          · exfalso
            apply hr
            simp only [List.nil_append] at heq
            subst heq
            exact (null_correct r).mpr hrw1
          · simp only [List.cons_append, List.cons.injEq] at heq
            obtain ⟨hab, hweq⟩ := heq
            subst hab
            exact ⟨w1', w2, hweq, (ihr w1').mpr hrw1, hsw2⟩
  | star r ih =>
      simp only [derivative, L]
      rw [starL_cons]
      constructor
      · rintro ⟨w1, w2, heq, hdr, hrest⟩
        exact ⟨w1, w2, heq, (ih w1).mp hdr, hrest⟩
      · rintro ⟨w1, w2, heq, hp, hrest⟩
        exact ⟨w1, w2, heq, (ih w1).mpr hp, hrest⟩
  | compl r ih => simp only [derivative, L, ih]

/-
A self-contained, VERIFIED decision procedure, not just individual
correctness lemmas to be chained by hand per instance. `acceptsBy` is a
plain executable function; `acceptsBy_correct` proves it sound and
complete ONCE, by induction on the word, so a future certificate only
needs `decide`/`rfl` to compute `acceptsBy` plus one application of this
theorem. This is exactly the role `Ere.decideEquiv` +
`decideEquiv_eq_true_iff_matches` plays for bisimulation-based regex
equivalence in the lpar26 formalization (`C:\git\ere\lpar26`) — same
pattern, simpler procedure.
-/
def acceptsBy (r : RE α) : List σ → Bool
  | []      => null r
  | a :: tl => acceptsBy (derivative a r) tl

theorem acceptsBy_correct (r : RE α) (w : List σ) : acceptsBy r w = true ↔ L r w := by
  induction w generalizing r with
  | nil => exact null_correct r
  | cons a w ih =>
      show acceptsBy (derivative a r) w = true ↔ L r (a :: w)
      rw [ih, derivative_correct]

end Z3SeqProofs
