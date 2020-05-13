(set-option :model_validate true)
(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(assert (distinct (str.substr a 3 (str.len b)) ""))
(assert (distinct
         (ite (= (str.len (str.substr (str.replace a b "") 0 (- (str.len c)))) 1) 0 2)
         (ite (= (str.at (str.replace a b "") 2) "") 1 2)))
(check-sat)
