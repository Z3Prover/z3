/-
Effective Boolean Algebra (EBA): predicates over characters with Boolean-
algebra operations consistent with their semantic membership test.

Mirrors the abstraction used in the EREQ/Lean formalization (MSO/EBA.lean,
`C:\git\EREQ\Lean`) and the resplit paper's split algebra
(`C:\git\z3papers\resplit\paper\paper.tex`), specialized to what c3mv's
regex engine actually needs (Brzozowski derivatives, linear form, views).

This library is derived locally rather than vendoring EREQ's own Lean
source, for two reasons: it can grow incrementally together with the rest
of this project (views, linear form, and eventually bisimulation-based
equivalence), and it never needs an `Existential`/quantifier constructor —
unlike EREQ's own `RE`/`RE_norm` types, which bundle that constructor
alongside the 7 ordinary ones in a single inductive type, the regex type
defined in `Regex.lean` has no such case at all, since c3mv has no
quantified regex support to formalize.
-/
namespace Z3SeqProofs

class EBA (α : Type) (σ : outParam Type) where
  models       : α → σ → Bool
  bot          : α
  top          : α
  compl        : α → α
  inf          : α → α → α
  sup          : α → α → α
  models_bot   : ∀ c, models bot c = false
  models_top   : ∀ c, models top c = true
  models_compl : ∀ a c, models (compl a) c = !(models a c)
  models_inf   : ∀ a b c, models (inf a b) c = (models a c && models b c)
  models_sup   : ∀ a b c, models (sup a b) c = (models a c || models b c)

end Z3SeqProofs
