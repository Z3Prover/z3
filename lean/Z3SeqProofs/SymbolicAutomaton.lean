import Z3SeqProofs.LinearForm
import Z3SeqProofs.View

/-
Symbolic automata: formalizes the construction connecting the
transition-regex/linear-form theory of `LinearForm.lean` to the
automaton-level statement `Lang(M_r) = Lang(r)`.

For `r : RE α`, the symbolic automaton `M_r = (A, Q, q0, F, ρ)` has
`Q = ders(r)` (the regexes reachable from `r` by iterated derivative),
`q0 = r`, `F = {q ∈ Q | nullable q}`, and
`ρ = {(s,α,t) | (α,t) ∈ LF(der(s))}` — i.e. exactly the transitions
already characterized by `sder_correct`/`LF_correct`
(`derivative_cofactors_correct` in `LinearForm.lean`). A word is
accepted iff it drives `r` through a chain of such transitions to a
final state.

As with `View.lean`, only the *soundness* content (`AutAccepts_correct`,
the statement `Lang(M_r) = Lang(r)`) is formalized here: reifying `Q` as
an explicit finite state set and proving `ders(r)` finite (needed to
see `M_r` as a literal finite-state object, not just an acceptance
relation) is EREQ's `Finiteness/*.lean`, not re-proved here.

The merge/split rewrites already proved sound in `LinearForm.lean`
(`LF_merge_sound`, `LF_split_sound`, `LF_split_concat_sound`) describe
exactly the "normal form" choices (Brzozowski vs. light-Antimirov `LF`)
mentioned in `seq_derive.h`'s `transition_mode`: since they preserve
`LF`'s ∃-characterization pointwise, they transparently preserve
`AutAccepts`/`Lang(M_r)` too — the same `ρ` up to a differently-shaped
but equivalent representation of its branches. No separate theorem is
needed for that.
-/
namespace Z3SeqProofs

variable {α σ : Type} [EBA α σ]

-- `AutAccepts r w`: acceptance of `w` by the symbolic automaton `M_r`,
-- walking its transition relation `ρ = {(s,α,t) | (α,t) ∈ LF(sder s)}`
-- one character at a time and finishing in a nullable (final) state.
def AutAccepts : RE α → List σ → Prop
  | r, []     => null r = true
  | r, a :: w => ∃ p ∈ LF (sder (σ := σ) r), EBA.models p.1 a = true ∧ AutAccepts p.2 w

-- Theorem [Lang(M_r) = Lang(r)]: the symbolic automaton driven by the
-- linear form of the symbolic derivative accepts exactly `L r`.
theorem AutAccepts_correct (r : RE α) (w : List σ) :
    AutAccepts r w ↔ L r w := by
  induction w generalizing r with
  | nil => exact null_correct r
  | cons a w ih =>
      show (∃ p ∈ LF (sder (σ := σ) r), EBA.models p.1 a = true ∧ AutAccepts p.2 w) ↔
        L r (a :: w)
      rw [← derivative_cofactors_correct r a w]
      constructor
      · rintro ⟨p, hp, hm, hacc⟩; exact ⟨p, hp, hm, (ih p.2).mp hacc⟩
      · rintro ⟨p, hp, hm, hl⟩; exact ⟨p, hp, hm, (ih p.2).mpr hl⟩

-- Bridges the two equivalent acceptance mechanisms now on record: the
-- transition-regex/linear-form-driven `AutAccepts` above, and the plain
-- iterated-concrete-derivative `acceptsBy` (`Derivatives.lean`). Both
-- compute the same thing, just via different (and now both verified)
-- machinery.
theorem AutAccepts_eq_acceptsBy (r : RE α) (w : List σ) :
    AutAccepts r w ↔ acceptsBy r w = true := by
  rw [AutAccepts_correct, acceptsBy_correct]

/-
`AutAccepts` only ever reports the *final* state's nullability, never
which state `M_r` actually lands in. `AutReaches` tracks the reached
state explicitly, so it can be related directly to `View.lean`'s
`iterDerivative` — the two are independent formalizations of "the state
`r` is driven to after reading `u`" (one via the automaton's `ρ`, one via
the plain iterated concrete derivative), and `AutReaches_iff_iterDerivative`
shows they agree on every reached state, not just on acceptance.
-/

-- `AutReaches r u s`: there is a path through `ρ` from `r` to `s`
-- labeled by `u`.
def AutReaches : RE α → List σ → RE α → Prop
  | r, [],     s => r = s
  | r, a :: w, s => ∃ p ∈ LF (sder (σ := σ) r), EBA.models p.1 a = true ∧ AutReaches p.2 w s

-- The state `M_r`'s transitions reach after reading `u` is exactly the
-- iterated concrete derivative `iterDerivative u r`: the automaton-level
-- notion of "reached state" (`ρ`-paths, `AutReaches`) and the
-- derivative-level notion (`View.lean`'s `iterDerivative`, underlying
-- `ViewPred`) are the same construction seen two ways.
theorem AutReaches_iff_iterDerivative (r : RE α) (u : List σ) (s : RE α) :
    AutReaches r u s ↔ iterDerivative u r = s := by
  induction u generalizing r with
  | nil => rfl
  | cons a w ih =>
      show (∃ p ∈ LF (sder (σ := σ) r), EBA.models p.1 a = true ∧ AutReaches p.2 w s) ↔
        iterDerivative (a :: w) r = s
      have hLF := LF_correct_general (sder (σ := σ) r) a (fun t => iterDerivative w t = s)
      rw [sder_correct] at hLF
      rw [show iterDerivative (a :: w) r = iterDerivative w (derivative a r) from rfl, ← hLF]
      constructor
      · rintro ⟨p, hp, hm, hreach⟩; exact ⟨p, hp, hm, (ih p.2).mp hreach⟩
      · rintro ⟨p, hp, hm, hiter⟩; exact ⟨p, hp, hm, (ih p.2).mpr hiter⟩

-- Consequently, every `View` (`ViewPred`) is exactly a reachable,
-- non-dead state of `M_r`: the automaton-level and derivative-level
-- accounts of "views" coincide.
theorem AutReaches_iff_ViewPred (r s : RE α) (u : List σ) :
    (AutReaches r u s ∧ s ≠ RE.bot) ↔ ViewPred r s u := by
  rw [AutReaches_iff_iterDerivative]
  rfl

end Z3SeqProofs
