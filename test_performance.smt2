(set-option :timeout 5000)
(set-option :smt.arith.nl false)
(set-option :sat.random_seed 42)

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

(assert (> (+ x y z) 100))
(assert (< (* x y) z))
(assert (> (- x y) 0))

(check-sat)
(get-model)