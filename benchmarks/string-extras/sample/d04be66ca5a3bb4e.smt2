; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/strings/issue12756-str-inc-model.smt2
; COMMAND-LINE: -i
; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(declare-const x Int)
(declare-const c String)
(declare-const c1 (Array String Bool))
(assert (< (str.indexof "" "" x) (str.len (ite (str.<= "0" c) (str.from_int 0) ""))))
(check-sat)
(assert (distinct (store c1 "" false) (store c1 "" (str.<= "0" c))))
(check-sat)
