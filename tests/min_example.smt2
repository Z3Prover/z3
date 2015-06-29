(set-option :fixedpoint.engine datalog)
(set-option :fixedpoint.datalog.transform_rules false)

(define-sort nibble_t () (_ BitVec 4))
(declare-rel triples (nibble_t nibble_t nibble_t))
(declare-rel pairs (nibble_t nibble_t))

(declare-var x nibble_t)
(declare-var y nibble_t)
(declare-var z nibble_t)

(rule (triples #x0 #x3 #x5))
(rule (triples #x0 #x1 #x4))

(rule (=> (and (triples x y z) (min y)) (pairs x y)))

(query (pairs x y) :print-answer true)

;sat
;(and (= (:var 0) #x0) (= (:var 1) #x1))
