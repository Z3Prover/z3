; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress1/strings/issue6545-extr.smt2
; COMMAND-LINE: --ext-rew-prep --ext-rew-prep-agg
; EXPECT: sat
(set-logic ALL)
(declare-fun a () String)
(assert
 (str.contains ""
  (str.replace_all ""
   (str.substr a 1
    (str.to_int
     (str.substr
      (str.substr a 0
       (ite (= (str.len (str.substr a 2 1)) 1)
        (ite (< (str.len a) 0)
         (ite (= (str.len (str.substr (str.substr a 2 1) (str.len (str.substr a 1 1)) 2)) 1) 1 0)
         (- 1))
        0))
      0 2)))
   a)))
(check-sat)
