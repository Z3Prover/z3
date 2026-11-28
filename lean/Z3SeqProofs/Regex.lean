import Z3SeqProofs.EBA

/-
Closed regex syntax over an abstract EBA, with reference (non-executable)
language semantics `L`.

No quantifier/existential constructor: matches the "n = 0" instance of
EREQ's `RE`/`RE_norm` and Z3's `OP_RE_*` core directly (UNION/INTERSECT/
CONCAT/STAR/COMPLEMENT/RANGE(=pred)/EMPTY_SET/epsilon).
-/
namespace Z3SeqProofs

inductive RE (α : Type) where
  | eps    : RE α
  | bot    : RE α
  | pred   : α → RE α
  | union  : RE α → RE α → RE α
  | inter  : RE α → RE α → RE α
  | concat : RE α → RE α → RE α
  | star   : RE α → RE α
  | compl  : RE α → RE α
  deriving DecidableEq

variable {α σ : Type} [EBA α σ]

-- Kleene-star closure of a word predicate, as a relation (avoids
-- existentials over `List (List σ)` and is the standard induction-friendly
-- formulation).
inductive starL (P : List σ → Prop) : List σ → Prop
  | nil  : starL P []
  | step : ∀ {w1 w2}, w1 ≠ [] → P w1 → starL P w2 → starL P (w1 ++ w2)

-- Reference language semantics (independent of null/derivative; the
-- ground truth `derivative_correct` in `Derivatives.lean` is checked
-- against).
def L : RE α → List σ → Prop
  | .eps,        w => w = []
  | .bot,        _ => False
  | .pred p,     w => ∃ c, w = [c] ∧ EBA.models p c = true
  | .union r s,  w => L r w ∨ L s w
  | .inter r s,  w => L r w ∧ L s w
  | .concat r s, w => ∃ w1 w2, w = w1 ++ w2 ∧ L r w1 ∧ L s w2
  | .star r,     w => starL (L r) w
  | .compl r,    w => ¬ L r w

end Z3SeqProofs
