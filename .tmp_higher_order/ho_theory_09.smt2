; HO + Datatypes: map over option type
(set-logic HO_ALL)
(declare-datatype (Option 1) ((par (T) ((none) (some (val T))))))
(define-fun map_opt ((f (-> Int Int)) (o (Option Int))) (Option Int)
  (match o
    ((none (as none (Option Int)))
     ((some v) (some (f v))))))
(assert (not (= (map_opt (lambda ((x Int)) (+ x 1)) (some 5)) (some 6))))
(check-sat)
(exit)
