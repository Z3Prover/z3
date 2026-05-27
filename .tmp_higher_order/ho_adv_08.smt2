; Advanced: higher-order pattern matching
; Synthesis: find F such that F applied pointwise doubles output
(set-logic HO_ALL)
(declare-fun F () (-> (-> Int Int) (-> Int Int)))
; F transforms any function by doubling its output
(assert (forall ((g (-> Int Int)) (x Int))
  (= ((F g) x) (* 2 (g x)))))
(declare-fun h () (-> Int Int))
(assert (= h (lambda ((x Int)) (+ x 1))))
(assert (not (= ((F h) 3) 8)))
(check-sat)
(exit)
