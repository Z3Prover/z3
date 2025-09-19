;; Test case for max PB constraints optimization feature
;; This demonstrates the transformation from multiple maximize objectives
;; to auxiliary variables with threshold constraints

(echo "Testing max PB constraints optimization")

;; Declare boolean variables
(declare-fun x1 () Bool)
(declare-fun x2 () Bool) 
(declare-fun y1 () Bool)
(declare-fun y2 () Bool)

;; Test case: Two PB constraints to maximize
;; PB1: 2*x1 + x2 (max value = 3)
;; PB2: y1 + 2*y2 (max value = 3)

(maximize (+ (ite x1 2 0) (ite x2 1 0)))
(maximize (+ (ite y1 1 0) (ite y2 2 0)))

(echo "Before optimization:")
(check-sat)

;; The implementation should detect these two PB maximize objectives
;; and transform them to auxiliary variables:
;; - For PB1: aux_0_1, aux_0_2, aux_0_3 where PB1 >= k => aux_0_k
;; - For PB2: aux_1_1, aux_1_2, aux_1_3 where PB2 >= k => aux_1_k  
;; - Then maximize: aux_0_1 + aux_0_2 + aux_0_3 + aux_1_1 + aux_1_2 + aux_1_3

(echo "Max PB optimization feature test completed")