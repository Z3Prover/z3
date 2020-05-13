;; Copyright (c) 2016 Microsoft Corporation 

(set-info :source |Written by D. B. Staple for GitHub issue #629.|)
(set-info :status sat)

(declare-fun a0 () Bool)
(declare-fun a1 () Bool)
(declare-fun c0 () Bool)
(declare-fun c1 () Bool)
(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(declare-fun b2 () Bool)
(assert (or
    (not (=> (and (and (not b2) (not b1)) (not b0)) (= c0 a0)))
    (not (=> (and (and (not b2) (not b1)) (not b0)) (= c1 a1)))))
(check-sat-using (and-then (par-or qfbv qfbv)))
