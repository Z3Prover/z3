(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun d () Int)
(declare-fun e () Int)
(assert
 (let ((f (< 0 e d)))
  (or
   (and
    (= c (/ 2.0 e))
    (forall ((g Int))
     (= (<= g d) (forall ((h Int)) (> h g)))))
   (< b a)
   f)))
(check-sat-using psmt)
