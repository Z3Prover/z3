(set-option :fixedpoint.engine datalog)
(set-option :fixedpoint.datalog.transform_rules false)

(define-sort router_t () (_ BitVec 1))
(define-sort cost_t () (_ BitVec 4))

(declare-rel length (router_t cost_t))
(declare-rel min_length (router_t cost_t))

(declare-var node router_t)

(declare-var cost cost_t)
(declare-var new_cost cost_t)

(rule (length #b0 #x2))
(rule (length #b0 #x3))
(rule (length #b1 #x5))

(rule (=>
  (and (length node cost) (min cost))
  (min_length node cost)))

(rule (=>
  (and (min_length node cost) (= (bvadd cost #x1) new_cost))
  (length node new_cost)))

(query (length node cost) :print-answer true)

; sat
; (or (and (= (:var 0) #b0) (= (:var 1) #x2))
;     (and (= (:var 0) #b0) (= (:var 1) #x3))
;     (and (= (:var 0) #b1) (= (:var 1) #x5))
;     (and (= (:var 0) #b1) (= (:var 1) #x6)))
