; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/seq/proj-issue427-subtypes-value.smt2
; EXPECT: sat
; EXPECT: (((seq.unit _x0) (seq.unit 0.0)))
(set-logic ALL)
(set-option :global-declarations true)
(set-option :produce-models true)
(declare-const _x0 Real)
(assert (= _x0 0.0))
(check-sat)

