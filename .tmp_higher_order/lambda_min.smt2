; Source: diffblue/cbmc - regression/smt2_solver/function-applications/lambda1.smt2
; Lambda used to define a min function over bitvectors
;(set-logic QF_ABV)

(define-const min (-> (_ BitVec 8) (_ BitVec 8) (_ BitVec 8))
  (lambda ((a (_ BitVec 8)) (b (_ BitVec 8))) 
    (ite (bvule a b) a b)))

(define-fun p1 () Bool (= (min #x01 #x02) #x01))
(define-fun p2 () Bool (= (min #xff #xfe) #xfe))

; all must be true

(assert (not (and p1 p2)))

(check-sat)
