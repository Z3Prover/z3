import Z3SeqProofs.SmartConcat

/-
Correctness of the regex rewriter's star smart constructor, modeling
`seq_rewriter::mk_re_star` (src/ast/rewriter/seq_rewriter.cpp).

Out of scope, matching the plan for the other files: `is_plus` (there is
no `plus` constructor in `RE` — `r+` is only ever a *derived* notion),
ITE-hoisting (no `ite` node in `RE`), and the `Σ*·S` self-concatenation
idempotence case (`(Σ*·S)* = ε ∪ Σ*·S`) — unlike every other case here,
that one needs its own bespoke "a suffix-absorbing language is closed
under concatenation" lemma that nothing else reuses, so it is lower
priority than finishing breadth across the remaining Tier 2 operators.

What *is* modeled: star idempotence (`r** = r*`), the two degenerate
bases (`∅* = ε`, `ε* = ε`), the single-character-universe case
(`Σ* = Σ*`, read off `full_char`), the four union-absorption laws
(`(r*∪s)* = (r∪s)*` and its three siblings via epsilon/symmetry), and
the concat-of-stars law (`(r*·s*)* = (r∪s)*`). The last two groups need
general facts about `starL` that the simpler Tier 1 constructors never
needed (`starL_mono`, `starL_single`, `starL_flatten`,
`starL_insert_eps(_right)`, `starL_union_absorb_left/right`,
`starL_concat_absorb`) — each a standalone automata-theoretic fact about
Kleene star, proved once here and reused across the whole case split.
-/
namespace Z3SeqProofs

variable {α σ : Type} [EBA α σ]

/-- Mirrors `seq_rewriter::is_full_char`: syntactically the maximal
single-character predicate `top`, i.e. `Σ` (matches every character). -/
def RE.isFullChar [DecidableEq α] : RE α → Bool
  | .pred p => p == EBA.top
  | _ => false

theorem RE.isFullChar_true_iff [DecidableEq α] {r : RE α} :
    r.isFullChar = true ↔ r = .pred EBA.top := by
  cases r <;> simp [RE.isFullChar]

/-- `starL` is monotone in its predicate argument. -/
theorem starL_mono {P P' : List σ → Prop} (h : ∀ w, P w → P' w) :
    ∀ {w}, starL P w → starL P' w
  | _, .nil => .nil
  | _, .step hw hp hrest => .step hw (h _ hp) (starL_mono h hrest)

/-- Any single word satisfying `P` is (trivially) a one-block `starL P`
match: via `.nil` if already empty, or a single `.step` otherwise. Used
repeatedly below to turn a pointwise inclusion into a `starL` inclusion
via `starL_mono`. -/
theorem starL_single {P : List σ → Prop} {w : List σ} (h : P w) : starL P w := by
  by_cases hw : w = []
  · subst hw; exact .nil
  · simpa using starL.step hw h starL.nil

/-- `starL` is idempotent: repeating "zero or more `P`-blocks" zero or
more times is the same as repeating `P`-blocks directly. The key fact
behind `r** = r*`. -/
theorem starL_flatten {P : List σ → Prop} : ∀ {w}, starL (starL P) w → starL P w
  | _, .nil => .nil
  | _, .step _ hp hrest => starL_append hp (starL_flatten hrest)

theorem starL_idem {P : List σ → Prop} {w : List σ} : starL (starL P) w ↔ starL P w :=
  ⟨starL_flatten, starL_mono (fun _ => starL_single)⟩

/-- Inserting a vacuous "or empty" option into a `starL` predicate
changes nothing: no `starL.step` can ever consume it, since steps
require a nonempty block. The key fact behind `(ε∪r)* = r*`. -/
theorem starL_insert_eps {P : List σ → Prop} {w : List σ} :
    starL (fun w => w = [] ∨ P w) w ↔ starL P w := by
  constructor
  · intro h
    induction h with
    | nil => exact .nil
    | step hw hp _ ih =>
        rcases hp with heq | hp
        · exact absurd heq hw
        · exact .step hw hp ih
  · exact starL_mono (fun _ => Or.inr)

/-- Symmetric to `starL_insert_eps` (the "or" on the other side). The
key fact behind `(r∪ε)* = r*`. -/
theorem starL_insert_eps_right {P : List σ → Prop} {w : List σ} :
    starL (fun w => P w ∨ w = []) w ↔ starL P w := by
  constructor
  · intro h
    induction h with
    | nil => exact .nil
    | step hw hp _ ih =>
        rcases hp with hp | heq
        · exact .step hw hp ih
        · exact absurd heq hw
  · exact starL_mono (fun _ => Or.inl)

/-- A nested `starL P` inside a union-with-`Q` is absorbed by the outer
star: any `P★`-block decomposes into (trivially one-block each) `P ∨ Q`
pieces, so repeating "`P★` or `Q`"-blocks is the same as repeating
"`P` or `Q`"-blocks. The key fact behind `(r*∪s)* = (r∪s)*`. -/
theorem starL_union_absorb_left {P Q : List σ → Prop} {w : List σ} :
    starL (fun w => starL P w ∨ Q w) w ↔ starL (fun w => P w ∨ Q w) w := by
  constructor
  · intro h
    induction h with
    | nil => exact .nil
    | step hw hpq _ ih =>
        rcases hpq with hsp | hq
        · exact starL_append (starL_mono (fun _ => Or.inl) hsp) ih
        · exact .step hw (Or.inr hq) ih
  · exact starL_mono (fun w hpq => hpq.elim (fun hp => Or.inl (starL_single hp)) Or.inr)

/-- Symmetric to `starL_union_absorb_left`: the key fact behind
`(r∪s*)* = (r∪s)*`. -/
theorem starL_union_absorb_right {P Q : List σ → Prop} {w : List σ} :
    starL (fun w => P w ∨ starL Q w) w ↔ starL (fun w => P w ∨ Q w) w := by
  constructor
  · intro h
    induction h with
    | nil => exact .nil
    | step hw hpq _ ih =>
        rcases hpq with hp | hsq
        · exact .step hw (Or.inl hp) ih
        · exact starL_append (starL_mono (fun _ => Or.inr) hsq) ih
  · exact starL_mono (fun w hpq => hpq.elim Or.inl (fun hq => Or.inr (starL_single hq)))

/-- A `starL` of "the concatenation of a `P★`-block and a `Q★`-block" is
the same as a `starL` of plain "`P` or `Q`"-blocks: each side can
simulate the other one single-language block at a time. The key fact
behind `(r*·s*)* = (r∪s)*`. -/
theorem starL_concat_absorb {P Q : List σ → Prop} {w : List σ} :
    starL (fun w => ∃ w1 w2, w = w1 ++ w2 ∧ starL P w1 ∧ starL Q w2) w ↔
    starL (fun w => P w ∨ Q w) w := by
  constructor
  · intro h
    induction h with
    | nil => exact .nil
    | step _ hblock _ ih =>
        obtain ⟨w1, w2, heq, hp1, hq2⟩ := hblock
        have hblock' : starL (fun w => P w ∨ Q w) (w1 ++ w2) :=
          starL_append (starL_mono (fun _ => Or.inl) hp1) (starL_mono (fun _ => Or.inr) hq2)
        rw [heq]
        exact starL_append hblock' ih
  · exact starL_mono (fun w hpq => hpq.elim
      (fun hp => ⟨w, [], (List.append_nil w).symm, starL_single hp, .nil⟩)
      (fun hq => ⟨[], w, rfl, .nil, starL_single hq⟩))

/-- Models the semantically meaningful subset of `mk_re_star`'s case
chain; see the file docstring for what is out of scope and why. -/
def smartStar [DecidableEq α] : RE α → RE α
  | a =>
    if a.isStar then a
    else if a.isFullChar then RE.fullSeq
    else if a.isEmpty then .eps
    else if a.isEpsilon then .eps
    else match a with
      | .union b c =>
          match b.asStar with
          | some b1 => .star (.union b1 c)
          | none =>
              match c.asStar with
              | some c1 => .star (.union b c1)
              | none =>
                  if b.isEpsilon then .star c
                  else if c.isEpsilon then .star b
                  else .star a
      | .concat b c =>
          match b.asStar with
          | some b1 =>
              match c.asStar with
              | some c1 => .star (.union b1 c1)
              | none => .star a
          | none => .star a
      | _ => .star a

theorem smartStar_correct [DecidableEq α] (a : RE α) (w : List σ) :
    L (smartStar a) w ↔ L (.star a : RE α) w := by
  unfold smartStar
  by_cases h1 : a.isStar = true
  · simp only [h1]
    obtain ⟨r, ha⟩ := RE.isStar_true_iff.mp h1
    subst ha
    simp only [L]
    exact starL_idem.symm
  simp only [h1]
  by_cases h2 : a.isFullChar = true
  · simp only [h2]
    rw [RE.isFullChar_true_iff] at h2
    subst h2
    rfl
  simp only [h2]
  by_cases h3 : a.isEmpty = true
  · simp only [h3]
    rw [RE.isEmpty_true_iff] at h3
    subst h3
    simp only [L]
    constructor
    · rintro rfl; exact starL.nil
    · intro h
      cases h with
      | nil => rfl
      | step _ hp _ => exact hp.elim
  simp only [h3]
  by_cases h4 : a.isEpsilon = true
  · simp only [h4]
    rw [RE.isEpsilon_true_iff] at h4
    subst h4
    simp only [L]
    constructor
    · rintro rfl; exact starL.nil
    · intro h
      cases h with
      | nil => rfl
      | step hw hp _ => exact absurd hp hw
  simp only [h4]
  cases a with
  | eps => exact absurd rfl h4
  | bot => exact absurd rfl h3
  | pred p => rfl
  | union b c =>
      rcases hsb : b.asStar with _ | b1
      · rcases hsc : c.asStar with _ | c1
        · by_cases hbe : b.isEpsilon = true
          · simp only [hsb, hsc, hbe]
            rw [RE.isEpsilon_true_iff] at hbe
            subst hbe
            simp only [L]
            exact starL_insert_eps.symm
          simp only [hsb, hsc, hbe]
          by_cases hce : c.isEpsilon = true
          · simp only [hce]
            rw [RE.isEpsilon_true_iff] at hce
            subst hce
            simp only [L]
            exact starL_insert_eps_right.symm
          simp only [hce]
          rfl
        · simp only [hsb, hsc]
          have hc' := RE.asStar_eq_some_iff.mp hsc
          subst hc'
          simp only [L]
          exact starL_union_absorb_right.symm
      · simp only [hsb]
        have hb' := RE.asStar_eq_some_iff.mp hsb
        subst hb'
        simp only [L]
        exact starL_union_absorb_left.symm
  | inter r s => rfl
  | concat b c =>
      rcases hsb : b.asStar with _ | b1
      · simp only [hsb]
        rfl
      · rcases hsc : c.asStar with _ | c1
        · simp only [hsb, hsc]
          rfl
        · simp only [hsb, hsc]
          have hb' := RE.asStar_eq_some_iff.mp hsb
          have hc' := RE.asStar_eq_some_iff.mp hsc
          subst hb'; subst hc'
          simp only [L]
          exact starL_concat_absorb.symm
  | star r => exact absurd rfl h1
  | compl r => rfl

end Z3SeqProofs
