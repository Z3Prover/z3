;; Copyright (c) 2016 Microsoft Corporation 

(set-info :source |Written by D. B. Staple for GitHub issue #625.|)
(set-info :status unsat)

(declare-fun x () Int)
(declare-fun y () Int)
(assert (= y (abs x)))
(assert (distinct y (abs x)))
(check-sat-using (par-or
    smt smt smt smt smt
    smt smt smt smt smt
    smt smt smt smt smt
))
