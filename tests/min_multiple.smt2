(set-option :fixedpoint.engine datalog)

(define-sort number_t () (_ BitVec 2))

(declare-rel a_rel (number_t number_t))
(declare-rel b_rel (number_t number_t))

(declare-var u number_t)
(declare-var v number_t)

(declare-var x number_t)
(declare-var y number_t)

(rule (a_rel #b01 #b00))
(rule (a_rel #b10 #b00))
(rule (a_rel #b10 #b11))
(rule (a_rel #b01 #b11))

(rule (=>
  (and (a_rel u v) ((_ min a_rel 0) u v) (a_rel x y) ((_ min a_rel 1) x y))
  (b_rel u x)))

(query (b_rel x y) :print-answer true)

; sat
; (or (and (= (:var 0) #b01) (= (:var 1) #b01))
;     (and (= (:var 0) #b01) (= (:var 1) #b10)))
