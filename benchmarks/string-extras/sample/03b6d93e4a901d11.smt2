; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress1/seq/issue8936-nth-eager-red.smt2
; REQUIRES: no-safe-mode
; COMMAND-LINE: --no-strings-lazy-pp
; EXPECT: unsat
(set-logic ALL)
(declare-fun a () (Seq Int))
(declare-fun b () (Seq Int))
(declare-fun c () Int)
(assert (= a b))
(assert (not (= (seq.nth a c) (seq.nth b c))))
(check-sat)
