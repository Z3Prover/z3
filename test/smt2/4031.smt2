(set-option :smt.arith.solver 6)
(set-option :model_validate true)
(declare-fun a () String)
(declare-fun b () String)
(assert
 (or (= (str.substr (str.++ a "abc" b) 0 (- (str.len a) 1)) "a")
 (distinct (str.substr (str.++ "abc" b) 1 3) (str.++ "bc" b))))
(check-sat)