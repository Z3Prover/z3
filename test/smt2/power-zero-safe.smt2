;; Copyright (c) 2016 Microsoft Corporation

(set-info :source |Written by D. B. Staple for GitHub issue #707.|)
(set-info :status unsat)

(declare-fun x () Real)
(declare-fun y () Real)
(assert (> x 0.0))
(assert (= y (^ x 0.0)))
(assert (distinct y 1.0))
(check-sat)
