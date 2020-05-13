
; Copyright (c) 2015 Microsoft Corporation
(set-option :produce-unsat-cores true)
(set-option :produce-models false)

(declare-const start25 Bool)
(declare-const bf07 Bool)
(declare-const bf19 Bool)
(declare-const lt06 Int)
(declare-const ef08 Int)
(declare-const ef110 Int)

(declare-fun whileM4 (Int) Int)

(assert start25)
(assert (=> start25 (distinct lt06 1)))
(assert (=> start25 (= lt06 (whileM4 0))))
(assert (=> (not bf07) (= ef08 0)))
(assert (=> bf07 (= ef08 (whileM4 (+ 0 1)))))
(assert (=> start25 (not (< (whileM4 0) 1))))
(assert (=> start25 (= (whileM4 0) ef08)))
(assert (=> start25 (and (=> bf07 (< 0 1)) (=> (< 0 1) bf07))))
(assert (=> (not bf19) (= ef110 (+ 0 1))))
(assert (=> bf19 (= ef110 (whileM4 (+ (+ 0 1) 1)))))
(assert (=> bf07 (not (< (whileM4 (+ 0 1)) 1))))
(assert (=> bf07 (= (whileM4 (+ 0 1)) ef110)))
(assert (=> bf07 (and (=> bf19 (< (+ 0 1) 1)) (=> (< (+ 0 1) 1) bf19))))

; (push) 
(check-sat (not bf19))
; (pop)  

(check-sat)
