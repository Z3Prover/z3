;; Copyright (c) 2016 Microsoft Corporation 

(set-info :source |Written by D. B. Staple as regression test for safe handling of even roots.|)
(set-info :status unsat)

(define-fun sqrt ((x Real)) Real (^ x 0.5))
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(assert (= x1 x2))
(assert (distinct (sqrt x1) (sqrt x2)))
(check-sat-using qfnra-nlsat)
