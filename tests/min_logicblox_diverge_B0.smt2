(set-option :fixedpoint.engine datalog)
(set-option :fixedpoint.datalog.transform_rules false)

(define-sort number_t () (_ BitVec 8))

(declare-rel Q (number_t))
(declare-rel MIN_Q (number_t))

(declare-var x number_t)
(declare-var y number_t)

(rule (Q #x05))

(rule (=>
  (and (Q x) ((_ min Q 0) x))
  (MIN_Q x)))

(rule (=>
  (and (MIN_Q x) (= #x05 x))
  (Q #x04)))

(query (Q x) :print-answer true)

; sat
; (or (= (:var 0) #x05) (= (:var 0) #x04))