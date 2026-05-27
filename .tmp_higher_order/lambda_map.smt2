; Source: tip-org/tools-paper - example.smt2
; Higher-order lambda with parametric datatypes and map

(declare-datatypes (a) ((list (nil) (cons (head a) (tail (list a))))))
(define-fun-rec
  (par (a b)
    (map ((f (=> a b)) (xs (list a))) (list b)
      (match xs (case nil (as nil (list b)))
                (case (cons x xs) (cons (@ f x) (map f xs)))))))

(assert-not
  (par (a)
    (forall ((xs (list a)))
       (= xs (map (lambda ((x a)) x) xs)))))
(check-sat)
