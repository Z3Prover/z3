import Z3SeqProofs.EBA

/-
Concrete EBA instance matching `seq::range_predicate`'s actual
representation (`src/ast/rewriter/seq_range_predicate.h`): a list of
`(lo, hi)` ranges over a bounded character domain `[0, maxChar]`.

Confirms the EBA <-> `range_predicate` correspondence is formally
checkable, not just structurally suggestive.
-/
namespace Z3SeqProofs

abbrev Alphabet (maxChar : Nat) := Fin (maxChar + 1)

structure RangePred (maxChar : Nat) where
  ranges : List (Nat × Nat)

-- Nat-indexed membership test (no `Fin` construction needed), used
-- internally so `complV` can iterate `c : Nat` directly without a
-- dependent-if.
def RangePred.modelsNat (p : RangePred maxChar) (c : Nat) : Bool :=
  p.ranges.any (fun r => r.1 ≤ c && c ≤ r.2)

def RangePred.modelsB (p : RangePred maxChar) (c : Alphabet maxChar) : Bool :=
  p.modelsNat c.val

theorem modelsNat_iff (p : RangePred maxChar) (c : Nat) :
    p.modelsNat c = true ↔ ∃ r ∈ p.ranges, r.1 ≤ c ∧ c ≤ r.2 := by
  simp [RangePred.modelsNat, List.any_eq_true]

-- Prop-level characterization of `modelsB`, used to avoid fighting
-- Bool/List computation lemmas directly in the EBA law proofs below.
theorem modelsB_iff (p : RangePred maxChar) (c : Alphabet maxChar) :
    p.modelsB c = true ↔ ∃ r ∈ p.ranges, r.1 ≤ c.val ∧ c.val ≤ r.2 := modelsNat_iff p c.val

def RangePred.botV (maxChar : Nat) : RangePred maxChar := ⟨[]⟩
def RangePred.topV (maxChar : Nat) : RangePred maxChar := ⟨[(0, maxChar)]⟩
def RangePred.supV (p q : RangePred maxChar) : RangePred maxChar := ⟨p.ranges ++ q.ranges⟩
def RangePred.infV (p q : RangePred maxChar) : RangePred maxChar :=
  ⟨p.ranges.flatMap (fun r1 => q.ranges.filterMap (fun r2 =>
      let lo := max r1.1 r2.1
      let hi := min r1.2 r2.2
      if lo ≤ hi then some (lo, hi) else none))⟩
def RangePred.complV (p : RangePred maxChar) : RangePred maxChar :=
  ⟨(List.range (maxChar + 1)).filterMap (fun c =>
      if p.modelsNat c then none else some (c, c))⟩

theorem botV_correct (maxChar : Nat) (c : Alphabet maxChar) :
    (RangePred.botV maxChar).modelsB c = false := by
  simp [RangePred.modelsB, RangePred.modelsNat, RangePred.botV]

theorem topV_correct (maxChar : Nat) (c : Alphabet maxChar) :
    (RangePred.topV maxChar).modelsB c = true := by
  rw [modelsB_iff]
  exact ⟨(0, maxChar), by simp [RangePred.topV], by omega, by omega⟩

theorem supV_correct (p q : RangePred maxChar) (c : Alphabet maxChar) :
    (RangePred.supV p q).modelsB c = (p.modelsB c || q.modelsB c) := by
  simp only [RangePred.modelsB, RangePred.modelsNat, RangePred.supV, List.any_append]

-- Small Bool/Prop bridging helper (no Mathlib available in this workspace).
theorem bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

theorem infV_correct (p q : RangePred maxChar) (c : Alphabet maxChar) :
    (RangePred.infV p q).modelsB c = (p.modelsB c && q.modelsB c) := by
  apply bool_ext
  rw [Bool.and_eq_true]
  constructor
  · intro h
    rw [modelsB_iff] at h
    obtain ⟨r, hr, hlo, hhi⟩ := h
    simp only [RangePred.infV, List.mem_flatMap, List.mem_filterMap] at hr
    obtain ⟨r1, hr1, r2, hr2, heq⟩ := hr
    split at heq
    · rename_i hmm
      injection heq with heq
      subst heq
      refine ⟨modelsB_iff .. |>.mpr ⟨r1, hr1, ?_, ?_⟩, modelsB_iff .. |>.mpr ⟨r2, hr2, ?_, ?_⟩⟩ <;> omega
    · contradiction
  · rintro ⟨hp, hq⟩
    rw [modelsB_iff] at hp hq
    obtain ⟨r1, hr1, hlo1, hhi1⟩ := hp
    obtain ⟨r2, hr2, hlo2, hhi2⟩ := hq
    rw [modelsB_iff]
    refine ⟨(max r1.1 r2.1, min r1.2 r2.2), ?_, by omega, by omega⟩
    simp only [RangePred.infV, List.mem_flatMap, List.mem_filterMap]
    refine ⟨r1, hr1, r2, hr2, ?_⟩
    have : max r1.1 r2.1 ≤ min r1.2 r2.2 := by omega
    simp [this]

theorem complV_correct (p : RangePred maxChar) (c : Alphabet maxChar) :
    (RangePred.complV p).modelsB c = !(p.modelsB c) := by
  have key : (RangePred.complV p).modelsB c = true ↔ ¬ (p.modelsB c = true) := by
    rw [modelsB_iff]
    constructor
    · rintro ⟨⟨r1, r2⟩, hr, hlo, hhi⟩ hp
      simp only [RangePred.complV, List.mem_filterMap, List.mem_range] at hr
      obtain ⟨x, _, hx⟩ := hr
      split at hx
      · contradiction
      · rename_i hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hx
        obtain ⟨hx1, hx2⟩ := hx
        subst hx1; subst hx2
        have hxc : x = c.val := by omega
        rw [RangePred.modelsB, ←hxc] at hp
        exact absurd hp (by simp [hnm])
    · intro hnp
      refine ⟨(c.val, c.val), ?_, by omega, by omega⟩
      simp only [RangePred.complV, List.mem_filterMap, List.mem_range]
      refine ⟨c.val, c.isLt, ?_⟩
      have : p.modelsNat c.val = false := by
        rw [RangePred.modelsB] at hnp
        cases h : p.modelsNat c.val
        · rfl
        · exact absurd h hnp
      simp [this]
  cases h : p.modelsB c <;> simp_all

instance rangePredEBA (maxChar : Nat) : EBA (RangePred maxChar) (Alphabet maxChar) where
  models       := RangePred.modelsB
  bot          := RangePred.botV maxChar
  top          := RangePred.topV maxChar
  compl        := RangePred.complV
  inf          := RangePred.infV
  sup          := RangePred.supV
  models_bot   := botV_correct maxChar
  models_top   := topV_correct maxChar
  models_compl := complV_correct
  models_inf   := infV_correct
  models_sup   := supV_correct

end Z3SeqProofs
