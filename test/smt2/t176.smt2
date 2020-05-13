
; Copyright (c) 2015 Microsoft Corporation
(set-logic  QF_BV)
(set-option :auto-config true)
(set-info :status unsat)
(define-fun bvsmod_def ((s (_ BitVec 13)) (t (_ BitVec 13))) (_ BitVec 13)
      (let ((msb_s ((_ extract 12 12) s))
            (msb_t ((_ extract 12 12) t)))
        (let ((abs_s (ite (= msb_s #b0) s (bvneg s)))
              (abs_t (ite (= msb_t #b0) t (bvneg t))))
          (let ((u (bvurem abs_s abs_t)))
            (ite (= u (_ bv0 13))
                 u
            (ite (and (= msb_s #b0) (= msb_t #b0))
                 u
            (ite (and (= msb_s #b1) (= msb_t #b0))
                 (bvadd (bvneg u) t)
            (ite (and (= msb_s #b0) (= msb_t #b1))
                 (bvadd u t)
                 (bvneg u)))))))))

(simplify (bvsmod_def (_ bv30 13) (_ bv8190 13)))
(simplify (bvsmod (_ bv30 13) (_ bv8190 13)))

(simplify (bvsmod_def (_ bv30 13) (_ bv8180 13)))
(simplify (bvsmod (_ bv30 13) (_ bv8180 13)))

(simplify (bvsmod_def (_ bv8130 13) (_ bv8180 13)))
(simplify (bvsmod (_ bv8130 13) (_ bv8180 13)))

(simplify (bvsmod_def (_ bv8130 13) (_ bv30 13)))
(simplify (bvsmod (_ bv8130 13) (_ bv30 13)))

(simplify (bvsmod_def (_ bv30 13) (_ bv30 13)))
(simplify (bvsmod (_ bv30 13) (_ bv30 13)))

(simplify (bvsmod_def (_ bv30 13) (_ bv0 13)))
(simplify (bvsmod (_ bv30 13) (_ bv0 13)))

(simplify (bvsmod_def (_ bv8130 13) (_ bv0 13)))
(simplify (bvsmod (_ bv8130 13) (_ bv0 13)))

(define-fun a () (_ BitVec 13) (_ bv30 13))
(define-fun b () (_ BitVec 13) (_ bv8190 13))
 
(assert (not (= (bvsmod_def a b) (bvsmod a b))))
(check-sat)



