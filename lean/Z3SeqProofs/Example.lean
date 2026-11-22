import Z3SeqProofs.RangePredicate
import Z3SeqProofs.Derivatives

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

end Z3SeqProofs
