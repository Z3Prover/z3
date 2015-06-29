(set-option :fixedpoint.engine datalog)
(set-option :fixedpoint.datalog.transform_rules false)

(define-sort nibble_t () (_ BitVec 4))

(declare-rel A (nibble_t nibble_t))
(declare-rel B (nibble_t nibble_t))
(declare-rel C (nibble_t nibble_t nibble_t))

(declare-var x nibble_t)
(declare-var y nibble_t)
(declare-var z nibble_t)

(rule (A #x1 #x2))
(rule (A #x1 #x3))
(rule (A #x1 #x1))

(rule (B #x2 #x4))
(rule (B #x2 #x5))
(rule (B #x3 #x0))
(rule (B #x1 #x4))

(rule (=>
  (and (A x y) (B y z) (min y))
  (C x z y)))

(query (C x z y) :print-answer true)

;sat
;(or (and (= (:var 0) #x1) (= (:var 1) #x5) (= (:var 2) #x2))
;    (and (= (:var 0) #x1) (= (:var 1) #x0) (= (:var 2) #x3))
;    (and (= (:var 0) #x1) (= (:var 1) #x4) (= (:var 2) #x1)))

