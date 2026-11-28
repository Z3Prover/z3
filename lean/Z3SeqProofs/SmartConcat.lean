import Z3SeqProofs.SmartXor

/-
Correctness of the regex rewriter's concatenation smart constructor,
modeling `seq_rewriter::mk_re_concat` (src/ast/rewriter/seq_rewriter.cpp).

`mk_re_concat` is by far the largest smart constructor in the codebase:
beyond the cases modeled here, it also handles string literals
(`to_re`), bounded loops (`{lo,hi}`), `full_char`-specific `+`
specializations, multi-level "starts/ends with Σ*" chain detection
across arbitrary concat nesting, and ITE-hoisting. None of these have an
`RE` analog (`RE` deliberately matches only Z3's core `OP_RE_*` set — no
string literals, no loop, no full_char as a distinct notion from
`pred top`) or are structurally a case-analysis concern rather than a
presentation/associativity one (the "chain detection" helpers, and
concat-flattening, are about recognizing `Σ*` through arbitrary levels
of concat-grouping — not a correctness question, since concat's
semantics is associative regardless of grouping).

What *is* modeled here are the semantically meaningful, directly
expressible cases: full-sequence absorption/identity (using nullability
rather than Z3's richer `min_length`-based `accepts_empty_word`, which
collapses to the same thing for `RE`'s simpler language), empty/epsilon
identities, and the `r* ++ r* = r*` idempotence law (needing its own
`starL_append` lemma, since concatenating two `star`-matches is not
immediate from the definitions alone).
-/
namespace Z3SeqProofs

variable {α σ : Type} [EBA α σ]

/-- Concatenating two words each accepted by `r★` is itself accepted by
`r★`: the key fact behind the `r* ++ r* = r*` identity. -/
theorem starL_append {P : List σ → Prop} :
    ∀ {w1 : List σ}, starL P w1 → ∀ {w2 : List σ}, starL P w2 → starL P (w1 ++ w2)
  | _, .nil, _, h2 => by simpa using h2
  | _, .step hne hp hrest, w2, h2 => by
      rw [List.append_assoc]
      exact starL.step hne hp (starL_append hrest h2)

/-- Returns the inner regex if `r` is syntactically a star, mirroring
`seq_rewriter::is_star`'s 2-argument overload. Matched on (rather than
`a`/`b` directly) for the same reason as `RE.asCompl` in `SmartXor.lean`. -/
def RE.asStar : RE α → Option (RE α)
  | .star r => some r
  | _ => none

theorem RE.asStar_eq_some_iff {r r' : RE α} : r.asStar = some r' ↔ r = .star r' := by
  cases r <;> simp [RE.asStar]

/-- Models the semantically meaningful subset of `mk_re_concat`'s case
chain; see the file docstring for what is out of scope and why. -/
def smartConcat [DecidableEq α] : RE α → RE α → RE α
  | a, b =>
    if a.isFullSeq && b.isFullSeq then a
    else if a.isFullSeq && null b then a
    else if b.isFullSeq && null a then b
    else if a.isEmpty then a
    else if b.isEmpty then b
    else if a.isEpsilon then b
    else if b.isEpsilon then a
    else match a.asStar with
      | some a1 =>
          match b.asStar with
          | some b1 => if a1 = b1 then a else .concat a b
          | none => .concat a b
      | none => .concat a b

set_option linter.unusedSimpArgs false in
theorem smartConcat_correct [DecidableEq α] (a b : RE α) (w : List σ) :
    L (smartConcat a b) w ↔ L (.concat a b : RE α) w := by
  unfold smartConcat
  by_cases h1 : (a.isFullSeq && b.isFullSeq) = true
  · simp only [h1]
    obtain ⟨ha, hb⟩ := Bool.and_eq_true .. |>.mp h1
    rw [RE.isFullSeq_true_iff] at ha hb
    subst ha; subst hb
    simp only [L]
    exact ⟨fun h => ⟨w, [], by simp, h, L_fullSeq []⟩, fun _ => L_fullSeq w⟩
  simp only [h1]
  by_cases h2 : (a.isFullSeq && null b) = true
  · simp only [h2]
    obtain ⟨ha, hb⟩ := Bool.and_eq_true .. |>.mp h2
    rw [RE.isFullSeq_true_iff] at ha
    have hb' := (null_correct b).mp hb
    subst ha
    simp only [L]
    exact ⟨fun h => ⟨w, [], by simp, h, hb'⟩, fun _ => L_fullSeq w⟩
  simp only [h2]
  by_cases h3 : (b.isFullSeq && null a) = true
  · simp only [h3]
    obtain ⟨hb, ha⟩ := Bool.and_eq_true .. |>.mp h3
    rw [RE.isFullSeq_true_iff] at hb
    have ha' := (null_correct a).mp ha
    subst hb
    simp only [L]
    exact ⟨fun h => ⟨[], w, by simp, ha', h⟩, fun _ => L_fullSeq w⟩
  simp only [h3]
  by_cases h4 : a.isEmpty = true
  · simp only [h4]
    rw [RE.isEmpty_true_iff] at h4; subst h4
    simp only [L]
    constructor
    · exact False.elim
    · rintro ⟨w1, w2, _, h, _⟩; exact h
  simp only [h4]
  by_cases h5 : b.isEmpty = true
  · simp only [h5]
    rw [RE.isEmpty_true_iff] at h5; subst h5
    simp only [L]
    constructor
    · exact False.elim
    · rintro ⟨w1, w2, _, _, h⟩; exact h
  simp only [h5]
  by_cases h6 : a.isEpsilon = true
  · simp only [h6]
    rw [RE.isEpsilon_true_iff] at h6; subst h6
    simp only [L]
    refine ⟨fun h => ⟨[], w, by simp, rfl, h⟩, ?_⟩
    rintro ⟨w1, w2, heq, rfl, h⟩
    simp only [List.nil_append] at heq
    subst heq
    exact h
  simp only [h6]
  by_cases h7 : b.isEpsilon = true
  · simp only [h7]
    rw [RE.isEpsilon_true_iff] at h7; subst h7
    simp only [L]
    refine ⟨fun h => ⟨w, [], by simp, h, rfl⟩, ?_⟩
    rintro ⟨w1, w2, heq, h, rfl⟩
    simp only [List.append_nil] at heq
    subst heq
    exact h
  simp only [h7]
  rcases hsa : a.asStar with _ | a1
  · simp
  · rcases hsb : b.asStar with _ | b1
    · simp
    · simp only [hsa, hsb]
      by_cases h8 : a1 = b1
      · simp only [h8]
        have ha' := RE.asStar_eq_some_iff.mp hsa
        have hb' := RE.asStar_eq_some_iff.mp hsb
        rw [h8] at ha'
        subst ha'; subst hb'
        simp only [L]
        refine ⟨fun h => ⟨w, [], by simp, h, starL.nil⟩, ?_⟩
        rintro ⟨w1, w2, heq, hh1, hh2⟩
        subst heq
        exact starL_append hh1 hh2
      · simp [h8]

end Z3SeqProofs
