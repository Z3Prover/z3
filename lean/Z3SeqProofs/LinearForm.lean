import Z3SeqProofs.Derivatives

/-
Symbolic derivatives as transition-terms (t-terms) and their linear form.

Formalizes `TRegex`/`eval`/the symbolic-derivative theorem (eq:sder) and
the Linear Form `LF`. This is the layer matching c3mv's `seq_derive.h`
ITE-tree representation and
`get_cofactors`/`derivative_cofactors`/`light_ant_derivative_cofactors`.
-/
namespace Z3SeqProofs

-- A t-term: a decision tree over predicates in `α`, whose leaves are regexes.
inductive TTerm (α : Type) (σ : Type) [EBA α σ] where
  | leaf : RE α → TTerm α σ
  | ite  : α → TTerm α σ → TTerm α σ → TTerm α σ

variable {α σ : Type} [EBA α σ]

-- `eval{f}{a}`: the regex that t-term `f` denotes for concrete character `a`.
def TTerm.eval : TTerm α σ → σ → RE α
  | .leaf r,     _ => r
  | .ite c t e,  a => if EBA.models c a then t.eval a else e.eval a

-- Pointwise combinators used to build `sder` compositionally (mirrors
-- `seq_derive.h`'s `hoist_ite` / EREQ's `lift_unary_norm`/`lift_binary_norm`).
def TTerm.liftU (f : RE α → RE α) : TTerm α σ → TTerm α σ
  | .leaf r     => .leaf (f r)
  | .ite c t e  => .ite c (t.liftU f) (e.liftU f)

def TTerm.liftB (f : RE α → RE α → RE α) : TTerm α σ → TTerm α σ → TTerm α σ
  | .leaf r1,    t2 => t2.liftU (f r1)
  | .ite c t e,  t2 => .ite c (t.liftB f t2) (e.liftB f t2)

theorem liftU_correct (f : RE α → RE α) (t : TTerm α σ) (a : σ) :
    (t.liftU f).eval a = f (t.eval a) := by
  induction t with
  | leaf r => simp [TTerm.liftU, TTerm.eval]
  | ite c t e iht ihe =>
      simp only [TTerm.liftU, TTerm.eval]
      split
      · exact iht
      · exact ihe

theorem liftB_correct (f : RE α → RE α → RE α) (t1 t2 : TTerm α σ) (a : σ) :
    (t1.liftB f t2).eval a = f (t1.eval a) (t2.eval a) := by
  induction t1 with
  | leaf r1 => simp only [TTerm.liftB, TTerm.eval]; exact liftU_correct (f r1) t2 a
  | ite c t e iht ihe =>
      simp only [TTerm.liftB, TTerm.eval]
      split
      · exact iht
      · exact ihe

-- Symbolic derivative: builds the t-term whose `eval` at any concrete `a`
-- equals `derivative a r` — mirrors `seq_derive.h`'s `derive_rec`/
-- `derive_core` and matches the symbolic-derivative theorem of
-- [SVB21, Thm 4.3].
def sder : RE α → TTerm α σ
  | .eps        => .leaf .bot
  | .bot        => .leaf .bot
  | .pred p     => .ite p (.leaf .eps) (.leaf .bot)
  | .union r s  => (sder r).liftB RE.union (sder s)
  | .inter r s  => (sder r).liftB RE.inter (sder s)
  | .concat r s =>
      let t' := (sder r).liftU (fun dr => RE.concat dr s)
      if null r then t'.liftB RE.union (sder s) else t'
  | .star r     => (sder r).liftU (fun dr => RE.concat dr (.star r))
  | .compl r    => (sder r).liftU RE.compl

theorem sder_correct (r : RE α) (a : σ) : (sder (σ := σ) r).eval a = derivative a r := by
  induction r with
  | eps => rfl
  | bot => rfl
  | pred p => simp only [sder, derivative, TTerm.eval]
  | union r s ihr ihs =>
      show ((sder r).liftB RE.union (sder s)).eval a = _
      rw [liftB_correct, ihr, ihs, derivative]
  | inter r s ihr ihs =>
      show ((sder r).liftB RE.inter (sder s)).eval a = _
      rw [liftB_correct, ihr, ihs, derivative]
  | concat r s ihr ihs =>
      show (let t' := (sder r).liftU (fun dr => RE.concat dr s)
            if null r then t'.liftB RE.union (sder s) else t').eval a = _
      rw [derivative]
      by_cases hr : null r = true
      · simp only [hr, ite_true]
        rw [liftB_correct, liftU_correct, ihr, ihs]
      · simp only [hr, ite_false, Bool.false_eq_true]
        rw [liftU_correct, ihr]
  | star r ih =>
      show ((sder r).liftU (fun dr => RE.concat dr (.star r))).eval a = _
      rw [liftU_correct, ih, derivative]
  | compl r ih =>
      show ((sder r).liftU RE.compl).eval a = _
      rw [liftU_correct, ih, derivative]

-- Linear form: the list of all branches `(β, ℓ)` reached by a t-term, with
-- `β` the accumulated path condition — the standard `LF_β(leaf ℓ)` /
-- `LF_β(ite α t e)` linear-form definition, minus the (optimization-only)
-- unsatisfiable-branch pruning.
def LFaux (β : α) : TTerm α σ → List (α × RE α)
  | .leaf r     => [(β, r)]
  | .ite c t e  => LFaux (EBA.inf β c) t ++ LFaux (EBA.inf β (EBA.compl c)) e

def LF (f : TTerm α σ) : List (α × RE α) := LFaux EBA.top f

theorem exists_mem_append {β : Type} {l1 l2 : List β} {P : β → Prop} :
    (∃ p ∈ l1 ++ l2, P p) ↔ (∃ p ∈ l1, P p) ∨ (∃ p ∈ l2, P p) := by
  simp only [List.mem_append]
  constructor
  · rintro ⟨p, (h1 | h2), hp⟩
    · exact Or.inl ⟨p, h1, hp⟩
    · exact Or.inr ⟨p, h2, hp⟩
  · rintro (⟨p, h1, hp⟩ | ⟨p, h2, hp⟩)
    · exact ⟨p, Or.inl h1, hp⟩
    · exact ⟨p, Or.inr h2, hp⟩

-- eq:LF, generalized over the accumulated path condition `β`.
theorem LFaux_correct (f : TTerm α σ) (β : α) (a : σ) (v : List σ) :
    (∃ p ∈ LFaux β f, EBA.models p.1 a = true ∧ L p.2 v) ↔
    (EBA.models β a = true ∧ L (f.eval a) v) := by
  induction f generalizing β with
  | leaf r => simp [LFaux, TTerm.eval]
  | ite c t e iht ihe =>
      simp only [LFaux, TTerm.eval]
      rw [exists_mem_append, iht, ihe, EBA.models_inf, EBA.models_inf, EBA.models_compl]
      by_cases hca : EBA.models c a = true
      · simp only [hca, Bool.and_true, Bool.not_true, Bool.and_false, ite_true]
        constructor
        · rintro (⟨hb, hl⟩ | ⟨hb, _⟩)
          · exact ⟨hb, hl⟩
          · exact absurd hb (by simp)
        · rintro ⟨hb, hl⟩
          exact Or.inl ⟨hb, hl⟩
      · simp only [hca, Bool.and_false, Bool.not_false, Bool.and_true, ite_false, Bool.false_eq_true]
        constructor
        · rintro (⟨hb, _⟩ | ⟨hb, hl⟩)
          · exact absurd hb (by simp)
          · exact ⟨hb, hl⟩
        · rintro ⟨hb, hl⟩
          exact Or.inr ⟨hb, hl⟩

-- Top-level eq:LF (`β = ⊤` specialization).
theorem LF_correct (f : TTerm α σ) (a : σ) (v : List σ) :
    (∃ p ∈ LF f, EBA.models p.1 a = true ∧ L p.2 v) ↔ L (f.eval a) v := by
  have h := LFaux_correct f EBA.top a v
  rw [EBA.models_top] at h
  simpa [LF] using h

-- End-to-end correctness of `derive::derivative_cofactors`: the cofactors
-- of `r`'s symbolic derivative decide membership of `a :: v` in `L r`
-- directly, without ever naming the concrete derivative in between.
-- Chains `LF_correct`, `sder_correct`, and (from `Derivatives.lean`)
-- `derivative_correct`.
theorem derivative_cofactors_correct (r : RE α) (a : σ) (v : List σ) :
    (∃ p ∈ LF (sder (σ := σ) r), EBA.models p.1 a = true ∧ L p.2 v) ↔ L r (a :: v) := by
  rw [LF_correct, sder_correct]
  exact derivative_correct r a v

/-
The two merge/split rewrite rules describing `light_ant_derivative_cofactors`'
behavior in `seq_derive.h`, as direct corollaries of `LFaux_correct` (both
are "replace a sub-list of branches by an equivalent sub-list" facts,
verified sound by the same ∃-characterization).
-/

-- Merge: two branches `(c,p)` and `(d,p)` with the SAME leaf `p` combine
-- into one branch `(c⊔d, p)` without changing which `(a,v)` pairs are
-- covered.
theorem LF_merge_sound (c d : α) (p : RE α) (rest : List (α × RE α)) (a : σ) (v : List σ) :
    (∃ q ∈ (c, p) :: (d, p) :: rest, EBA.models q.1 a = true ∧ L q.2 v) ↔
    (∃ q ∈ (EBA.sup c d, p) :: rest, EBA.models q.1 a = true ∧ L q.2 v) := by
  simp only [List.mem_cons]
  constructor
  · rintro ⟨q, (hq | hq | hq), hm, hl⟩
    · subst hq
      refine ⟨(EBA.sup c d, p), Or.inl rfl, ?_, hl⟩
      show EBA.models (EBA.sup c d) a = true
      rw [EBA.models_sup]; simp [hm]
    · subst hq
      refine ⟨(EBA.sup c d, p), Or.inl rfl, ?_, hl⟩
      show EBA.models (EBA.sup c d) a = true
      rw [EBA.models_sup]; simp [hm]
    · exact ⟨q, Or.inr hq, hm, hl⟩
  · rintro ⟨q, (hq | hq), hm, hl⟩
    · subst hq
      have hor : EBA.models c a = true ∨ EBA.models d a = true := by
        rw [EBA.models_sup] at hm
        simpa using hm
      rcases hor with hc | hd
      · exact ⟨(c, p), Or.inl rfl, hc, hl⟩
      · exact ⟨(d, p), Or.inr (Or.inl rfl), hd, hl⟩
    · exact ⟨q, Or.inr (Or.inr hq), hm, hl⟩

-- Split: a branch `(c, p|s)` can be seen as the two branches `(c,p)` and
-- `(c,s)` — the "light-Antimirov -> full-Antimirov" refinement.
theorem LF_split_sound (c : α) (p s : RE α) (rest : List (α × RE α)) (a : σ) (v : List σ) :
    (∃ q ∈ (c, RE.union p s) :: rest, EBA.models q.1 a = true ∧ L q.2 v) ↔
    (∃ q ∈ (c, p) :: (c, s) :: rest, EBA.models q.1 a = true ∧ L q.2 v) := by
  simp only [List.mem_cons]
  constructor
  · rintro ⟨q, (hq | hq), hm, hl⟩
    · subst hq
      rcases hl with hl | hl
      · exact ⟨(c, p), Or.inl rfl, hm, hl⟩
      · exact ⟨(c, s), Or.inr (Or.inl rfl), hm, hl⟩
    · exact ⟨q, Or.inr (Or.inr hq), hm, hl⟩
  · rintro ⟨q, (hq | hq | hq), hm, hl⟩
    · subst hq; exact ⟨(c, RE.union p s), Or.inl rfl, hm, Or.inl hl⟩
    · subst hq; exact ⟨(c, RE.union p s), Or.inl rfl, hm, Or.inr hl⟩
    · exact ⟨q, Or.inr hq, hm, hl⟩

-- Swapping a branch's target regex for one denoting the same language
-- never changes the ∃-characterization. Used below to reduce the
-- concat-of-union split to the bare-union case already handled by
-- `LF_split_sound`.
theorem LF_target_congr (c : α) (p q : RE α) (rest : List (α × RE α))
    (h : ∀ v, L p v ↔ L q v) (a : σ) (v : List σ) :
    (∃ r ∈ (c, p) :: rest, EBA.models r.1 a = true ∧ L r.2 v) ↔
    (∃ r ∈ (c, q) :: rest, EBA.models r.1 a = true ∧ L r.2 v) := by
  simp only [List.mem_cons]
  constructor
  · rintro ⟨r, (hr | hr), hm, hl⟩
    · subst hr; exact ⟨(c, q), Or.inl rfl, hm, (h v).mp hl⟩
    · exact ⟨r, Or.inr hr, hm, hl⟩
  · rintro ⟨r, (hr | hr), hm, hl⟩
    · subst hr; exact ⟨(c, p), Or.inl rfl, hm, (h v).mpr hl⟩
    · exact ⟨r, Or.inr hr, hm, hl⟩

-- Concatenation distributes over union: `(p|s)·tail = p·tail | s·tail`.
-- A basic regex identity, needed to extend `LF_split_sound` to the
-- "union under concat" shape `light_ant_derivative_cofactors` also splits.
theorem L_concat_union_distrib (p s tail : RE α) (v : List σ) :
    L (.concat (.union p s) tail : RE α) v ↔
    L (.union (.concat p tail) (.concat s tail) : RE α) v := by
  simp only [L]
  constructor
  · rintro ⟨w1, w2, heq, (h1 | h1), h2⟩
    · exact Or.inl ⟨w1, w2, heq, h1, h2⟩
    · exact Or.inr ⟨w1, w2, heq, h1, h2⟩
  · rintro (⟨w1, w2, heq, h1, h2⟩ | ⟨w1, w2, heq, h1, h2⟩)
    · exact ⟨w1, w2, heq, Or.inl h1, h2⟩
    · exact ⟨w1, w2, heq, Or.inr h1, h2⟩

-- Split under concat: a branch `(c, (p|s)·tail)` can be seen as the two
-- branches `(c, p·tail)` and `(c, s·tail)` — the extra case
-- `light_ant_derivative_cofactors` handles (its inner `heads` worklist)
-- beyond the bare-union split of `LF_split_sound`, for a target of the
-- form `(s1|...|sn)·tail` reached after a concat-head derivative step.
theorem LF_split_concat_sound (c : α) (p s tail : RE α) (rest : List (α × RE α))
    (a : σ) (v : List σ) :
    (∃ q ∈ (c, RE.concat (RE.union p s) tail) :: rest, EBA.models q.1 a = true ∧ L q.2 v) ↔
    (∃ q ∈ (c, RE.concat p tail) :: (c, RE.concat s tail) :: rest,
        EBA.models q.1 a = true ∧ L q.2 v) :=
  (LF_target_congr c _ _ rest (L_concat_union_distrib p s tail) a v).trans
    (LF_split_sound c (RE.concat p tail) (RE.concat s tail) rest a v)

-- Dropping a branch whose target is the empty language never changes the
-- ∃-characterization — justifies `get_cofactors_rec`'s `is_empty`-guarded
-- `push_back` (an unreachable leaf is simply never added to the result).
theorem LF_filter_empty_sound (c : α) (rest : List (α × RE α)) (a : σ) (v : List σ) :
    (∃ q ∈ (c, RE.bot) :: rest, EBA.models q.1 a = true ∧ L q.2 v) ↔
    (∃ q ∈ rest, EBA.models q.1 a = true ∧ L q.2 v) := by
  simp only [List.mem_cons]
  constructor
  · rintro ⟨q, (hq | hq), hm, hl⟩
    · subst hq; exact absurd hl (by simp [L])
    · exact ⟨q, hq, hm, hl⟩
  · rintro ⟨q, hq, hm, hl⟩
    exact ⟨q, Or.inr hq, hm, hl⟩

end Z3SeqProofs

