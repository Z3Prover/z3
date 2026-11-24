; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/strings/issue5815-ndet-string-ent.smt2
(set-logic ALL)
(set-info :status sat)
(declare-fun a () String)
(assert (= (str.substr (str.substr a (+ (+ 1 0) 1)
    (- (str.len (str.substr (str.substr (str.substr a 1 (- (+ (str.len a) 1) 1)) 1 (- (+ 1 (+ 1 1)) 1)) 
    1 (- (str.len a) 1))) 1)) 0 0) a))
(check-sat)
