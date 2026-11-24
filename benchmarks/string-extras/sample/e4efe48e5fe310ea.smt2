; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress1/strings/issue8434-nterm-str-rw.smt2
; COMMAND-LINE:
; EXPECT: unsat
(set-logic ALL)
(declare-fun T_7 () String)                                                     
(declare-fun T_c () String)                                                     
(assert (= T_c (str.++ (str.at T_7 0) ";")))                                    
(assert (= 0 (ite (str.contains "" (str.substr T_c 1 (str.indexof (str.substr T_c 0 
(str.indexof T_c (str.substr T_c (+ 1 1) 1) 0)) "T" 0))) 1 0)))                 
(check-sat)
