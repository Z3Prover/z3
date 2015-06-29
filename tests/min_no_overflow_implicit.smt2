(set-option :fixedpoint.engine datalog)
(set-option :fixedpoint.datalog.transform_rules false)

; identifier for a router
(define-sort router_t () (_ BitVec 1))

; large enough to avoid overflow in addition
(define-sort cost_t () (_ BitVec 3))

; direct cost between two routers
(declare-rel link (router_t router_t cost_t))

(declare-rel sh_path (router_t router_t cost_t))
(declare-rel path (router_t router_t cost_t))
(declare-rel split_path (router_t router_t cost_t))

(declare-var x router_t)
(declare-var y router_t)
(declare-var z router_t)

(declare-var c1 cost_t)
(declare-var c2 cost_t)
(declare-var c3 cost_t)
(declare-var c4 cost_t)

(rule (link #b0 #b1 #b011))
(rule (link #b1 #b0 #b011))
(rule (link #b0 #b0 #b011))
(rule (link #b1 #b1 #b011))

(rule (=> (link x y c1) (path x y c1)))

(rule (=>
  (and (sh_path x y c1) (link y z c2) (= (bvadd c1 c2) c3))
  (split_path x z c3)))

(rule (=>
  (and (split_path x y c1))
  (path x y c1)))

(rule (=>
  (and (path x y c1) (min c1))
  (sh_path x y c1)))

(query (sh_path x y c1) :print-answer true)

; sat
; (or (and (= (:var 0) #b0) (= (:var 1) #b0) (= (:var 2) #b011))
;     (and (= (:var 0) #b1) (= (:var 1) #b0) (= (:var 2) #b011))
;     (and (= (:var 0) #b0) (= (:var 1) #b1) (= (:var 2) #b011))
;     (and (= (:var 0) #b1) (= (:var 1) #b1) (= (:var 2) #b011)))
