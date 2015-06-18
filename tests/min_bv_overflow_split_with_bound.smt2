(set-option :fixedpoint.engine datalog)

; identifier for a router
(define-sort router_t () (_ BitVec 2))

; large enough to avoid overflow in addition
(define-sort cost_t () (_ BitVec 8))

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

(rule (link #b00 #b01 #b000000001))
(rule (link #b00 #b11 #b000000100))
(rule (link #b00 #b10 #b000000011))

(rule (link #b01 #b00 #b000000001))
(rule (link #b01 #b10 #b000000001))
(rule (link #b01 #b11 #b000000100))

(rule (link #b10 #b00 #b000000011))
(rule (link #b10 #b01 #b000000001))
(rule (link #b10 #b11 #b000000001))

(rule (link #b11 #b00 #b000000100))
(rule (link #b11 #b01 #b000000100))
(rule (link #b11 #b10 #b000000001))

(rule (=> (link x y c1) (path x y c1)))

(rule (path x y #b01111111))

(rule (=>
  (and (path x y c1) ((_ min path 2) x y c1) (link y z c2) (= (bvadd c1 c2) c3))
  (split_path x z c3)))

(rule (=>
  (and (split_path x y c1) (path x y c2) ((_ min path 2) x y c2)  (bvult c1 c2))
  (path x y c1)))

(rule (=>
  (and (path x y c1) ((_ min path 2) x y c1))
  (sh_path x y c1)))

(query (sh_path #b00 #b11 #x01) :print-answer true) ; expected: unsat
(query (sh_path #b01 #b11 #x01) :print-answer true) ; expected: unsat
