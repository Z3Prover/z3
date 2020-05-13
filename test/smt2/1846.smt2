(set-option :produce-unsat-cores true)


(define-fun intToStr ((i Int)) String (ite (> i 0) (int.to.str i) (str.++ "-" (int.to.str (- 0 i)))))

(declare-const t Int)
(declare-const s String)

(assert (! (= t 11) :named a))
(assert (= s (intToStr t)))

(check-sat)
(exit)
(reset)


 (declare-const t Int)
 (declare-const s String)
 (assert (>= t 53))
 (assert (= s (int.to.str t)))
 (check-sat)

