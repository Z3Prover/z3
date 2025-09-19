(declare-fun x1 () Bool)
(declare-fun x2 () Bool)
(declare-fun y1 () Bool)
(declare-fun y2 () Bool)

; Create two PB maximize objectives - must be integer expressions
(maximize (+ (ite x1 2 0) (ite x2 1 0)))  ; PB1: max = 3
(maximize (+ (ite y1 1 0) (ite y2 2 0)))  ; PB2: max = 3

(check-sat)