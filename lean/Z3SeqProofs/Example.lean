import Z3SeqProofs.RangePredicate
import Z3SeqProofs.Derivatives
import Z3SeqProofs.View
import Z3SeqProofs.SymbolicAutomaton
import Z3SeqProofs.SmartConcat

/-
A concrete, end-to-end worked example over a toy 4-symbol alphabet
`[0,3]`, mirroring what a c3mv proof-certificate step needs to discharge
for `seq_mem_facet.cpp`'s ground-witness derivative loop.

Regex: `(0|1)*2` — "zero or more symbols from {0,1}, then a literal 2".
-/
namespace Z3SeqProofs

abbrev Pred3 := RangePred 3

def predZeroOne : Pred3 := ⟨[(0, 1)]⟩   -- matches symbols 0 and 1
def predTwo     : Pred3 := ⟨[(2, 2)]⟩   -- matches symbol 2 only

def exampleRE : RE Pred3 :=
  .concat (.star (.pred predZeroOne)) (.pred predTwo)

-- word [0,1,0,2] should be accepted: (0|1)* consumes 0,1,0 and 2 matches the tail.
def exampleWord : List (Alphabet 3) := [0, 1, 0, 2]

#eval acceptsBy exampleRE exampleWord   -- expect true

-- The "self-contained checker" style: one theorem application, no manual
-- per-character chaining (compare with the hand-chained version below,
-- kept only as a cross-check that both styles agree).
theorem exampleRE_accepts : L exampleRE exampleWord :=
  (acceptsBy_correct exampleRE exampleWord).mp (by decide)

-- The original "embed lemmas + per-instance proof" style, kept to confirm
-- both approaches certify the same fact (a decision-procedure soundness
-- theorem is only as trustworthy as `decide`/`native_decide`'s evaluation,
-- so cross-checking against the hand-built chain once is worthwhile
-- evidence).
theorem exampleRE_accepts_by_hand : L exampleRE exampleWord := by
  have step1 : L (derivative (0 : Alphabet 3) exampleRE) [1, 0, 2] ↔ L exampleRE [0, 1, 0, 2] :=
    derivative_correct exampleRE 0 [1, 0, 2]
  have step2 : L (derivative (1 : Alphabet 3) (derivative (0 : Alphabet 3) exampleRE)) [0, 2]
             ↔ L (derivative (0 : Alphabet 3) exampleRE) [1, 0, 2] :=
    derivative_correct (derivative 0 exampleRE) 1 [0, 2]
  have step3 : L (derivative (0 : Alphabet 3) (derivative (1 : Alphabet 3) (derivative (0 : Alphabet 3) exampleRE))) [2]
             ↔ L (derivative (1 : Alphabet 3) (derivative (0 : Alphabet 3) exampleRE)) [0, 2] :=
    derivative_correct (derivative 1 (derivative 0 exampleRE)) 0 [2]
  have step4 : L (derivative (2 : Alphabet 3) (derivative (0 : Alphabet 3) (derivative (1 : Alphabet 3) (derivative (0 : Alphabet 3) exampleRE)))) []
             ↔ L (derivative (0 : Alphabet 3) (derivative (1 : Alphabet 3) (derivative (0 : Alphabet 3) exampleRE))) [2] :=
    derivative_correct (derivative 0 (derivative 1 (derivative 0 exampleRE))) 2 []
  have final : null (derivative (2 : Alphabet 3) (derivative (0 : Alphabet 3) (derivative (1 : Alphabet 3) (derivative (0 : Alphabet 3) exampleRE)))) = true := by
    decide
  have accL : L (derivative (2 : Alphabet 3) (derivative (0 : Alphabet 3) (derivative (1 : Alphabet 3) (derivative (0 : Alphabet 3) exampleRE)))) [] :=
    (null_correct _).mp final
  exact step1.mp (step2.mp (step3.mp (step4.mp accL)))

/-
The sections below exercise the machinery added after this file was
first written (smart constructors, the symbolic-derivative/linear-form
layer, the symbolic automaton, and views) concretely on `exampleRE`,
confirming it all actually computes and type-checks on a non-toy
instance, not just abstractly.
-/

-- ===== Smart constructors, concretely =====

-- `(0|1)*·(0|1)* = (0|1)*`: `smartConcat`'s star-star idempotence law,
-- demonstrated on the concrete `(0|1)*` factor of `exampleRE` — it
-- collapses to a single `star`, not a raw (unsimplified) `concat`.
example :
    smartConcat (RE.star (.pred predZeroOne) : RE Pred3) (RE.star (.pred predZeroOne)) =
      (RE.star (.pred predZeroOne) : RE Pred3) := by
  decide

-- Correctness carries over regardless of whether the smart constructor
-- fired: both sides denote the same language as the raw concat, by
-- `smartConcat_correct`.
example (w : List (Alphabet 3)) :
    L (smartConcat (RE.star (.pred predZeroOne) : RE Pred3) (RE.star (.pred predZeroOne))) w ↔
      L (.concat (.star (.pred predZeroOne)) (.star (.pred predZeroOne)) : RE Pred3) w :=
  smartConcat_correct _ _ w

-- ===== Symbolic derivative / linear form, concretely =====

-- `LF (sder exampleRE)` is a concrete, computable list of
-- `(predicate, leaf)` branches.
#eval (LF (sder (σ := Alphabet 3) exampleRE)).length

-- The end-to-end `derivative_cofactors_correct` pipeline, instantiated on
-- `exampleRE`: the cofactors of its symbolic derivative decide
-- membership of `exampleWord` directly, agreeing with the
-- already-established `exampleRE_accepts`.
example :
    ∃ p ∈ LF (sder (σ := Alphabet 3) exampleRE), EBA.models p.1 (0 : Alphabet 3) = true ∧
      L p.2 [1, 0, 2] :=
  (derivative_cofactors_correct exampleRE 0 [1, 0, 2]).mpr exampleRE_accepts

-- ===== Symbolic automaton, concretely =====

-- `AutAccepts` (driven by `sder`/`LF`) and `acceptsBy` (driven by the raw
-- derivative) are two independently-verified routes that agree on this
-- concrete instance.
theorem exampleRE_AutAccepts : AutAccepts exampleRE exampleWord := by
  rw [AutAccepts_eq_acceptsBy]
  decide

-- ===== Views, concretely =====

-- The state reached after reading just the first character `0` is a
-- genuine (non-empty) view: `exampleRE`'s loop hasn't gone dead.
example : ViewPred exampleRE (iterDerivative ([0] : List (Alphabet 3)) exampleRE)
    ([0] : List (Alphabet 3)) :=
  ⟨rfl, by decide⟩

-- Theorem [View] splits `exampleWord = [0]·[1,0,2]` into "`[0]` drives
-- `exampleRE` to some reachable state `s`" plus "`[1,0,2]` matches from
-- `s` onward" — concretely confirming the split c3mv's
-- `seq_view_witness.cpp`/`mem_monadic_split` performs is sound here.
example :
    L exampleRE exampleWord ↔
      ∃ s, ViewPred exampleRE s ([0] : List (Alphabet 3)) ∧ L s [1, 0, 2] :=
  view_theorem exampleRE [0] [1, 0, 2]

end Z3SeqProofs
