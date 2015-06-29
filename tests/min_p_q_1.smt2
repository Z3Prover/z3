(set-option :fixedpoint.engine datalog)
(set-option :fixedpoint.datalog.transform_rules false)

(define-sort nibble_t () (_ BitVec 4))
(declare-rel P (nibble_t))
(declare-rel MIN_P (nibble_t))
(declare-rel Q (nibble_t))
(declare-rel MIN_Q (nibble_t))

(declare-var x nibble_t)
(declare-var y nibble_t)

(rule (P #x2))
(rule (Q #x2))

(rule (=> (and (P x) (min x)) (MIN_P x)))
(rule (=> (and (Q y) (min y)) (MIN_Q y)))

(rule (=> (and (MIN_P x) (= x #x2)) (Q #x1)))
(rule (=> (and (MIN_Q y) (= y #x2)) (P #x1)))

(query (Q y) :print-answer true)

; sat
; (or (= (:var 0) #x2) (= (:var 0) #x1))

