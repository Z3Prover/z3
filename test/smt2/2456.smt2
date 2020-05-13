(set-option :smt.mbqi true)

(declare-sort A)
(declare-sort B)
(declare-fun f (A) B)

(assert
 (forall ((b B) (x A) (y A))
         (or (= x y)
             (not (= (f x) b)))))
(declare-fun a1 () A)
(declare-fun a2 () A)
(declare-fun x () B)
(assert (not (= a1 a2)))
(check-sat)  
